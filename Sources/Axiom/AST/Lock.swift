#if canImport(Darwin)
import Darwin
#elseif canImport(Glibc)
import Glibc
#elseif canImport(Musl)
import Musl
#endif

/// A minimal cross-platform mutex, used by ``TermArena`` to guard the hash-cons table.
///
/// On Darwin we use `os_unfair_lock` (lighter than `pthread_mutex` for uncontended
/// single-threaded hot paths like fresh-term interning). Other platforms use pthread.
final class Lock: @unchecked Sendable {
    #if canImport(Darwin)
    private var unfairLock = os_unfair_lock()
    #else
    private var mutex = pthread_mutex_t()
    #endif

    init() {
        #if !canImport(Darwin)
        pthread_mutex_init(&mutex, nil)
        #endif
    }

    deinit {
        #if !canImport(Darwin)
        pthread_mutex_destroy(&mutex)
        #endif
    }

    @inline(__always)
    func lock() {
        #if canImport(Darwin)
        os_unfair_lock_lock(&unfairLock)
        #else
        pthread_mutex_lock(&mutex)
        #endif
    }

    @inline(__always)
    func unlock() {
        #if canImport(Darwin)
        os_unfair_lock_unlock(&unfairLock)
        #else
        pthread_mutex_unlock(&mutex)
        #endif
    }

    @inline(__always)
    func withLock<T>(_ body: () throws -> T) rethrows -> T {
        lock()
        defer { unlock() }
        return try body()
    }
}
