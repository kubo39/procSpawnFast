module procspawnfast;

version (linux):
version (X86_64):

import core.stdc.errno;
import core.sys.posix.sys.wait;
import core.sys.posix.unistd;

import std.internal.cstring;
import std.process : ProcessException;
import std.range.primitives;
import std.stdio;

private
{
    // Made available by the C runtime:
    extern(C) extern __gshared const char** environ;
    const(char**) getEnvironPtr() @trusted
    {
        return environ;
    }

    extern (C) long syscall(long nr, long n1, long n2, long n3) nothrow @nogc;
}

/**
Spawns a new process, optionally assigning it an arbitrary set of standard
input, output, and error streams. This function is optimized for Linux, by
using clone(CLONE_VM | CLONE_VFORK).
 */
Pid spawnProcessFast(scope const(char[])[] args,
                     File stdin = std.stdio.stdin,
                     File stdout = std.stdio.stdout,
                     File stderr = std.stdio.stderr,
                     const string[string] env = null,
                     Config config = Config.none)
    @trusted
{
    return spawnProcessFastImpl(args, stdin, stdout, stderr, env, config);
}

/// ditto
Pid spawnProcessFast(scope const(char[])[] args,
                     const string[string] env,
                     Config config = Config.none)
    @trusted
{
    return spawnProcessFast(args,
                            std.stdio.stdin,
                            std.stdio.stdout,
                            std.stdio.stderr,
                            env,
                            config);
}

/// ditto
Pid spawnProcessFast(scope const(char)[] program,
                     File stdin = std.stdio.stdin,
                     File stdout = std.stdio.stdout,
                     File stderr = std.stdio.stderr,
                     const string[string] env = null,
                     Config config = Config.none)
    @trusted
{
    return spawnProcessFast((&program)[0 .. 1],
                            stdin, stdout, stderr, env, config);
}

/// ditto
Pid spawnProcessFast(scope const(char)[] program,
                     const string[string] env,
                     Config config = Config.none)
    @trusted
{
    return spawnProcessFast((&program)[0 .. 1], env, config);
}

private enum InternalError : ubyte
{
    noerror,
    exec,
    sysconf,
    pthread_sigmask,
}

Pid spawnProcessFastImpl(scope const(char[])[] args,
                         File stdin,
                         File stdout,
                         File stderr,
                         scope const string[string] env,
                         Config config)
    @trusted
{
    import core.exception : RangeError;
    import std.algorithm.searching : any;
    import std.conv : text;
    import std.path : isDirSeparator;
    import std.string : toStringz;

    if (args.empty) throw new RangeError();
    const(char)[] name = args[0];
    if (any!isDirSeparator(name))
    {
        if (!isExecutable(name))
            throw new ProcessException(text("Not an executable file: ", name));
    }
    else
    {
        name = searchPathFor(name);
        if (name is null)
            throw new ProcessException(text("Executable file not found: ", args[0]));
    }

    // Convert program name and arguments to C-style strings.
    auto argz = new const(char)*[args.length+1];
    argz[0] = toStringz(name);
    foreach (i; 1 .. args.length) argz[i] = toStringz(args[i]);
    argz[$-1] = null;

    // Prepare environment.
    auto envz = createEnv(env, !(config & Config.newEnv));

    static int getFD(ref File f) { return core.stdc.stdio.fileno(f.getFP()); }

    // Get the file descriptors of the streams.
    // These could potentially be invalid, but that is OK.  If so, later calls
    // to dup2() and close() will just silently fail without causing any harm.
    auto stdinFD  = getFD(stdin);
    auto stdoutFD = getFD(stdout);
    auto stderrFD = getFD(stderr);

    // We don't have direct access to the errors that may happen in a child process.
    // So we use this pipe to deliver them.
    int[2] forkPipe;
    if (core.sys.posix.unistd.pipe(forkPipe) == 0)
        setCLOEXEC(forkPipe[1], true);
    else
        throw ProcessException.newFromErrno("Could not create pipe to check startup of child");
    scope(exit) close(forkPipe[0]);

    /*
    To create detached process, we use double fork technique
    but we don't have a direct access to the second fork pid from the caller side thus use a pipe.
    We also can't reuse forkPipe for that purpose
    because we can't predict the order in which pid and possible error will be written
    since the first and the second forks will run in parallel.
    */
    int[2] pidPipe;

    static void abortOnError(int forkPipeOut, InternalError errorType, int error) nothrow
    {
        core.sys.posix.unistd.write(forkPipeOut, &errorType, errorType.sizeof);
        core.sys.posix.unistd.write(forkPipeOut, &error, error.sizeof);
        close(forkPipeOut);
        core.sys.posix.unistd._exit(1);
        assert(0);
    }

    void closePipeWriteEnds()
    {
        close(forkPipe[1]);
    }

    import core.sys.linux.sched : clone, CLONE_VM;
    import core.sys.linux.sys.mman : mmap, munmap, MAP_PRIVATE, MAP_ANONYMOUS,
        MAP_STACK, MAP_FAILED, PROT_READ, PROT_WRITE;

    enum CLONE_VFORK = 0x4000; // TODO: Add to druntime.

    struct clone_args
    {
        const(char*)[] argz;
        const(char*)* envz;
        int stdinFD;
        int stdoutFD;
        int stderrFD;
        Config config;
        int forkPipeIn;
        int forkPipeOut;
        sigset_t oldmask;
    }

    // Add a slack area for child's stack.
    size_t argvSize = (argz.length * (void*).sizeof) + 512;
    argvSize += (32 * 1024);

    size_t stackSize = argvSize;
    immutable pageSize = sysconf(_SC_PAGESIZE);
    stackSize = (stackSize + pageSize) & ~(pageSize - 1);
    void* stack = mmap(null, stackSize, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_STACK,
                       -1, 0);
    if (stack == MAP_FAILED)
        throw ProcessException.newFromErrno("Failed to allocate child stack");

    extern (C) static int cloneChild(void* arguments) nothrow @nogc
    {
        auto argv = cast(clone_args*) arguments;
        close(argv.forkPipeIn);
        // The child process must ensure that no signal handler are
        // enabled because it shares memory with parent.
        enum _NSIG = 32;
        foreach (int signum; 1 .. _NSIG)
        {
            signal(signum, SIG_DFL);
        }

        // Redirect streams and close the old file descriptors.
        // In the case that stderr is redirected to stdout, we need
        // to backup the file descriptor since stdout may be redirected
        // as well.
        if (argv.stderrFD == STDOUT_FILENO)
            argv.stderrFD = dup(argv.stderrFD);
        dup2(argv.stdinFD,  STDIN_FILENO);
        dup2(argv.stdoutFD, STDOUT_FILENO);
        dup2(argv.stderrFD, STDERR_FILENO);

        // Ensure that the standard streams aren't closed on execute, and
        // optionally close all other file descriptors.
        setCLOEXEC(STDIN_FILENO, false);
        setCLOEXEC(STDOUT_FILENO, false);
        setCLOEXEC(STDERR_FILENO, false);

        if (!(argv.config & Config.inheritFDs))
        {
            int posIntFromAscii(const(char)* name) nothrow @nogc
            {
                int num = 0;
                while (*name >= '0' && *name <= '9')
                {
                    num = num * 10 + (*name - '0');
                    name++;
                }
                if (*name)
                    return -1;
                return num;
            }

            int closeOpenFileDescriptorsSafe(int forkPipeOut) nothrow @nogc
            {
                import core.sys.posix.fcntl : open, O_RDONLY;
                enum SYS_getdents64 = 217;
                struct linux_dirent64
                {
                    ulong d_ino;
                    long d_off;
                    ushort d_reclen;  // Length of this linux_dirent
                    char d_type;
                    char[256] d_name;  // Filename(null-terminated)
                }

                int dfd = open("/proc/self/fd\0", O_RDONLY);
                if (dfd < 0)
                    return dfd;
                char[linux_dirent64.sizeof] buffer;
                long bytes;
                while ((bytes = syscall(SYS_getdents64, dfd,
                                        cast(long)cast(linux_dirent64*)buffer,
                                        buffer.sizeof)) > 0)
                {
                    linux_dirent64* entry;
                    for (int offset; offset < bytes; offset += entry.d_reclen)
                    {
                        int fd;
                        entry = cast(linux_dirent64*)(buffer.ptr + offset);
                        if ((fd = posIntFromAscii(entry.d_name.ptr)) < 0)
                            continue; // Not a number
                        if (fd != dfd && fd > 2 && fd != forkPipeOut)
                            close(fd);
                    }
                }
                close(dfd);
                return 0;
            }

            if (closeOpenFileDescriptorsSafe(argv.forkPipeOut) < 0)
            {
                // Fall back to closing everything.
                immutable maxDescriptors = cast(int) sysconf(_SC_OPEN_MAX);
                if (maxDescriptors == -1)
                {
                    abortOnError(argv.forkPipeOut, InternalError.sysconf, .errno);
                }
                foreach (i; 3 .. maxDescriptors)
                {
                    if (i == argv.forkPipeOut) continue;
                    close(i);
                }
            }
        }
        else
        {
            // Close the old file descriptors, unless they are
            // either of the standard streams.
            if (argv.stdinFD  > STDERR_FILENO)  close(argv.stdinFD);
            if (argv.stdoutFD > STDERR_FILENO)  close(argv.stdoutFD);
            if (argv.stderrFD > STDERR_FILENO)  close(argv.stderrFD);
        }

        int rc = pthread_sigmask(SIG_SETMASK, &argv.oldmask, null);
        if (rc != 0)
            abortOnError(argv.forkPipeOut, InternalError.pthread_sigmask, rc);

        // Execute program.
        core.sys.posix.unistd.execve(argv.argz[0], argv.argz.ptr, argv.envz);
        // If execution fails, exit as quickly as possible.
        abortOnError(argv.forkPipeOut, InternalError.exec, .errno);
        assert(false);
    }

    sigset_t all = void;
    sigset_t oldmask = void;
    int rc = sigfillset(&all);
    if (rc < 0)
        throw ProcessException.newFromErrno("Failed sigfillset()");
    rc = pthread_sigmask(SIG_SETMASK, &all, &oldmask);
    if (rc != 0)
        throw new ProcessException(text("Failed pthread_sigmask(): ", rc));

    clone_args cArgs;
    cArgs.config = config;
    cArgs.argz = argz;
    cArgs.envz = envz;
    cArgs.stdinFD = stdinFD;
    cArgs.stdoutFD = stdoutFD;
    cArgs.stderrFD = stderrFD;
    cArgs.forkPipeIn = forkPipe[0];
    cArgs.forkPipeOut = forkPipe[1];
    cArgs.oldmask = oldmask;

    int id = clone(&cloneChild, stack + stackSize, CLONE_VM | CLONE_VFORK | SIGCHLD,
                   cast(void*)&cArgs);

    rc = pthread_sigmask(SIG_SETMASK, &oldmask, null);
    if (rc != 0)
        throw new ProcessException(text("Failed pthread_sigmask(): ", rc));

    rc = munmap(stack, stackSize);
    if (rc != 0)
        throw ProcessException.newFromErrno("Failed munmap()");
    assert(id != 0);

    if (id < 0)
    {
        closePipeWriteEnds();
        throw ProcessException.newFromErrno("Failed to spawn new process");
    }
    else // id > 0
    {
        closePipeWriteEnds();
        auto status = InternalError.noerror;
        auto readExecResult = core.sys.posix.unistd.read(forkPipe[0], &status, status.sizeof);
        // Save error number just in case if subsequent "waitpid" fails and overrides errno
        immutable lastError = .errno;

        if (readExecResult == -1)
            throw ProcessException.newFromErrno(lastError, "Could not read from pipe to get child status");

        bool owned = true;
        if (status != InternalError.noerror)
        {
            int error;
            readExecResult = read(forkPipe[0], &error, error.sizeof);
            string errorMsg;
            final switch (status)
            {
                case InternalError.exec:
                    errorMsg = "Failed to execute program";
                    break;
                case InternalError.sysconf:
                    errorMsg = "sysconf failed";
                    break;
                case InternalError.pthread_sigmask:
                    errorMsg = "pthread_sigmask failed";
                    break;
                case InternalError.noerror:
                    assert(false);
            }
            if (readExecResult == error.sizeof)
                throw ProcessException.newFromErrno(error, errorMsg);
            throw new ProcessException(errorMsg);
        }

        // Parent process:  Close streams and return.
        if (!(config & Config.retainStdin ) && stdinFD  > STDERR_FILENO
                                            && stdinFD  != getFD(std.stdio.stdin ))
            stdin.close();
        if (!(config & Config.retainStdout) && stdoutFD > STDERR_FILENO
                                            && stdoutFD != getFD(std.stdio.stdout))
            stdout.close();
        if (!(config & Config.retainStderr) && stderrFD > STDERR_FILENO
                                            && stderrFD != getFD(std.stdio.stderr))
            stderr.close();
        return new Pid(id, owned);
    }
}

/**
 *  Mostly copy-and-paste'ed from std.process module.
 */

private const(char*)* createEnv(const string[string] childEnv,
                                bool mergeWithParentEnv)
{
    // Determine the number of strings in the parent's environment.
    int parentEnvLength = 0;
    auto environ = getEnvironPtr;
    if (mergeWithParentEnv)
    {
        if (childEnv.length == 0) return environ;
        while (environ[parentEnvLength] != null) ++parentEnvLength;
    }

    // Convert the "new" variables to C-style strings.
    auto envz = new const(char)*[parentEnvLength + childEnv.length + 1];
    int pos = 0;
    foreach (var, val; childEnv)
        envz[pos++] = (var~'='~val~'\0').ptr;

    // Add the parent's environment.
    foreach (environStr; environ[0 .. parentEnvLength])
    {
        int eqPos = 0;
        while (environStr[eqPos] != '=' && environStr[eqPos] != '\0') ++eqPos;
        if (environStr[eqPos] != '=') continue;
        auto var = environStr[0 .. eqPos];
        if (var in childEnv) continue;
        envz[pos++] = environStr;
    }
    envz[pos] = null;
    return envz.ptr;
}

private string searchPathFor(scope const(char)[] executable)
    @trusted //TODO: @safe nothrow
{
    import std.algorithm.iteration : splitter;
    import std.conv : to;
    import std.path : buildPath;
    static import core.stdc.stdlib;
    auto pathz = core.stdc.stdlib.getenv("PATH");
    if (pathz == null)  return null;

    foreach (dir; splitter(to!string(pathz), ':'))
    {
        auto execPath = buildPath(dir, executable);
        if (isExecutable(execPath))  return execPath;
    }

    return null;
}

private bool isExecutable(scope const(char)[] path) @trusted nothrow @nogc //TODO: @safe
{
    return (access(path.tempCString(), X_OK) == 0);
}

private void setCLOEXEC(int fd, bool on) nothrow @nogc
{
    import core.sys.posix.fcntl : fcntl, F_GETFD, FD_CLOEXEC, F_SETFD;
    auto flags = fcntl(fd, F_GETFD);
    if (flags >= 0)
    {
        if (on) flags |= FD_CLOEXEC;
        else    flags &= ~(cast(typeof(flags)) FD_CLOEXEC);
        flags = fcntl(fd, F_SETFD, flags);
    }
    assert(flags != -1 || .errno == EBADF);
}

enum Config
{
    none = 0,

    /**
    By default, the child process inherits the parent's environment,
    and any environment variables passed to $(LREF spawnProcess) will
    be added to it.  If this flag is set, the only variables in the
    child process' environment will be those given to spawnProcess.
    */
    newEnv = 1,

    /**
    Unless the child process inherits the standard input/output/error
    streams of its parent, one almost always wants the streams closed
    in the parent when $(LREF spawnProcess) returns.  Therefore, by
    default, this is done.  If this is not desirable, pass any of these
    options to spawnProcess.
    */
    retainStdin  = 2,
    retainStdout = 4,                                  /// ditto
    retainStderr = 8,                                  /// ditto

    /**
    On POSIX, open $(LINK2 http://en.wikipedia.org/wiki/File_descriptor,file descriptors)
    are by default inherited by the child process.  As this may lead
    to subtle bugs when pipes or multiple threads are involved,
    $(LREF spawnProcess) ensures that all file descriptors except the
    ones that correspond to standard input/output/error are closed
    in the child process when it starts.  Use `inheritFDs` to prevent
    this.
    */
    inheritFDs = 32,
}


/// A handle that corresponds to a spawned process.
final class Pid
{
    /**
    The process ID number.

    This is a number that uniquely identifies the process on the operating
    system, for at least as long as the process is running.  Once $(LREF wait)
    has been called on the $(LREF Pid), this method will return an
    invalid (negative) process ID.
    */
    @property int processID() const @safe pure nothrow
    {
        return _processID;
    }

    /**
    An operating system handle to the process.

    This handle is used to specify the process in OS-specific APIs.
    On POSIX, this function returns a `core.sys.posix.sys.types.pid_t`
    with the same value as $(LREF Pid.processID), while on Windows it returns
    a `core.sys.windows.windows.HANDLE`.

    Once $(LREF wait) has been called on the $(LREF Pid), this method
    will return an invalid handle.
    */
    // Note: Since HANDLE is a reference, this function cannot be const.
    @property pid_t osHandle() @safe pure nothrow
    {
        return _processID;
    }

private:
    /*
    Pid.performWait() does the dirty work for wait() and nonBlockingWait().

    If block == true, this function blocks until the process terminates,
    sets _processID to terminated, and returns the exit code or terminating
    signal as described in the wait() documentation.

    If block == false, this function returns immediately, regardless
    of the status of the process.  If the process has terminated, the
    function has the exact same effect as the blocking version.  If not,
    it returns 0 and does not modify _processID.
    */
    int performWait(bool block) @trusted
    {
        import std.exception : enforce;
        enforce!ProcessException(owned, "Can't wait on a detached process");
        if (_processID == terminated) return _exitCode;
        int exitCode;
        while (true)
        {
            int status;
            auto check = waitpid(_processID, &status, block ? 0 : WNOHANG);
            if (check == -1)
            {
                if (errno == ECHILD)
                {
                    throw new ProcessException(
                        "Process does not exist or is not a child process.");
                }
                else
                {
                    // waitpid() was interrupted by a signal.  We simply
                    // restart it.
                    assert(errno == EINTR);
                    continue;
                }
            }
            if (!block && check == 0) return 0;
            if (WIFEXITED(status))
            {
                exitCode = WEXITSTATUS(status);
                break;
            }
            else if (WIFSIGNALED(status))
            {
                exitCode = -WTERMSIG(status);
                break;
            }
            // We check again whether the call should be blocking,
            // since we don't care about other status changes besides
            // "exited" and "terminated by signal".
            if (!block) return 0;

            // Process has stopped, but not terminated, so we continue waiting.
        }
        // Mark Pid as terminated, and cache and return exit code.
        _processID = terminated;
        _exitCode = exitCode;
        return exitCode;
    }

    // Special values for _processID.
    enum invalid = -1, terminated = -2;

    // OS process ID number.  Only nonnegative IDs correspond to
    // running processes.
    int _processID = invalid;

    // Exit code cached by wait().  This is only expected to hold a
    // sensible value if _processID == terminated.
    int _exitCode;

    // Whether the process can be waited for by wait() for or killed by kill().
    // False if process was started as detached. True otherwise.
    bool owned;

    // Pids are only meant to be constructed inside this module, so
    // we make the constructor private.
    this(int id, bool owned) @safe pure nothrow
    {
        _processID = id;
        this.owned = owned;
    }
}


/**
Waits for the process associated with `pid` to terminate, and returns
its exit status.

In general one should always _wait for child processes to terminate
before exiting the parent process unless the process was spawned as detached
(that was spawned with `Config.detached` flag).
Otherwise, they may become "$(HTTP en.wikipedia.org/wiki/Zombie_process,zombies)"
– processes that are defunct, yet still occupy a slot in the OS process table.
You should not and must not wait for detached processes, since you don't own them.

If the process has already terminated, this function returns directly.
The exit code is cached, so that if wait() is called multiple times on
the same $(LREF Pid) it will always return the same value.

POSIX_specific:
If the process is terminated by a signal, this function returns a
negative number whose absolute value is the signal number.
Since POSIX restricts normal exit codes to the range 0-255, a
negative return value will always indicate termination by signal.
Signal codes are defined in the `core.sys.posix.signal` module
(which corresponds to the `signal.h` POSIX header).

Throws:
$(LREF ProcessException) on failure or on attempt to wait for detached process.

Example:
See the $(LREF spawnProcess) documentation.

See_also:
$(LREF tryWait), for a non-blocking function.
*/
int wait(Pid pid) @safe
{
    assert(pid !is null, "Called wait on a null Pid.");
    return pid.performWait(true);
}


@system unittest // Pid and wait()
{
    TestScript prog = "exit $1";
    assert(wait(spawnProcessFast([prog.path, "0"])) == 0);
    assert(wait(spawnProcessFast([prog.path, "123"])) == 123);
    auto pid = spawnProcessFast([prog.path, "10"]);
    assert(pid.processID > 0);
    assert(pid.osHandle == pid.processID);
    assert(wait(pid) == 10);
    assert(wait(pid) == 10); // cached exit code
    assert(pid.processID < 0);
    assert(pid.osHandle < 0);
}


/**
A non-blocking version of $(LREF wait).

If the process associated with `pid` has already terminated,
`tryWait` has the exact same effect as `wait`.
In this case, it returns a tuple where the `terminated` field
is set to `true` and the `status` field has the same
interpretation as the return value of `wait`.

If the process has $(I not) yet terminated, this function differs
from `wait` in that does not wait for this to happen, but instead
returns immediately.  The `terminated` field of the returned
tuple will then be set to `false`, while the `status` field
will always be 0 (zero).  `wait` or `tryWait` should then be
called again on the same `Pid` at some later time; not only to
get the exit code, but also to avoid the process becoming a "zombie"
when it finally terminates.  (See $(LREF wait) for details).

Returns:
An $(D std.typecons.Tuple!(bool, "terminated", int, "status")).

Throws:
$(LREF ProcessException) on failure or on attempt to wait for detached process.

Example:
---
auto pid = spawnProcess("dmd myapp.d");
scope(exit) wait(pid);
...
auto dmd = tryWait(pid);
if (dmd.terminated)
{
    if (dmd.status == 0) writeln("Compilation succeeded!");
    else writeln("Compilation failed");
}
else writeln("Still compiling...");
...
---
Note that in this example, the first `wait` call will have no
effect if the process has already terminated by the time `tryWait`
is called.  In the opposite case, however, the `scope` statement
ensures that we always wait for the process if it hasn't terminated
by the time we reach the end of the scope.
*/
auto tryWait(Pid pid) @safe
{
    import std.typecons : Tuple;
    assert(pid !is null, "Called tryWait on a null Pid.");
    auto code = pid.performWait(false);
    return Tuple!(bool, "terminated", int, "status")(pid._processID == Pid.terminated, code);
}

@property string nativeShell() @safe @nogc pure nothrow
{
    return "/bin/sh";
}

// Unittest support code:  TestScript takes a string that contains a
// shell script for the current platform, and writes it to a temporary
// file. On Windows the file name gets a .cmd extension, while on
// POSIX its executable permission bit is set.  The file is
// automatically deleted when the object goes out of scope.
version (unittest)
private struct TestScript
{
    this(string code) @system
    {
        // @system due to chmod
        import std.ascii : newline;
        import std.file : write;

        auto ext = "";
        auto firstLine = "#!" ~ nativeShell;

        path = uniqueTempPath()~ext;
        write(path, firstLine ~ newline ~ code ~ newline);

        import core.sys.posix.sys.stat : chmod;
        import std.conv : octal;
        chmod(path.tempCString(), octal!777);
    }

    ~this()
    {
        import std.file : remove, exists;
        if (!path.empty && exists(path))
        {
            try { remove(path); }
            catch (Exception e)
            {
                debug std.stdio.stderr.writeln(e.msg);
            }
        }
    }

    string path;
}

version (unittest)
private string uniqueTempPath() @safe
{
    import std.file : tempDir;
    import std.path : buildPath;
    import std.uuid : randomUUID;
    // Path should contain spaces to test escaping whitespace
    return buildPath(tempDir(), "std.process temporary file " ~
        randomUUID().toString());
}
