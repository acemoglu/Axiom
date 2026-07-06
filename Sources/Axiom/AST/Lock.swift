#if canImport(Darwin)
import Darwin
#elseif canImport(Glibc)
import Glibc
#elseif canImport(Musl)
import Musl
#endif

/// A minimal cross-platform mutex, used by ``TermPool`` to guard the hash-cons table.
///
/// Kept dependency-free (no Foundation) so the trusted kernel has zero external imports.
final class Lock: @unchecked Sendable {
    private var mutex = pthread_mutex_t()

    init() {
        pthread_mutex_init(&mutex, nil)
    }

    deinit {
        pthread_mutex_destroy(&mutex)
    }

    @inline(__always)
    func lock() {
        pthread_mutex_lock(&mutex)
    }

    @inline(__always)
    func unlock() {
        pthread_mutex_unlock(&mutex)
    }

    @inline(__always)
    func withLock<T>(_ body: () throws -> T) rethrows -> T {
        lock()
        defer { unlock() }
        return try body()
    }
}
