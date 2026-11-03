/// A predicative universe level: a concrete index, a level variable, or a
/// combination built with `succ` and `max`.
///
/// Declarations are still monomorphic. Level variables appear in terms and are
/// compared under an explicit ``UniverseConstraints`` set — they are not yet
/// parameters of definitions or inductives.
public indirect enum UniverseLevel: Hashable, Sendable {
    case literal(Int)
    case variable(String)
    case succ(UniverseLevel)
    case max(UniverseLevel, UniverseLevel)

    public var successor: UniverseLevel {
        UniverseLevel.succ(self).normalized()
    }

    public static func join(_ left: UniverseLevel, _ right: UniverseLevel) -> UniverseLevel {
        UniverseLevel.max(left, right).normalized()
    }

    /// Folds concrete `succ`/`max` and puts `max` arguments in a stable order.
    public func normalized() -> UniverseLevel {
        switch self {
        case .literal, .variable:
            return self

        case .succ(let inner):
            let normalizedInner = inner.normalized()
            if case .literal(let level) = normalizedInner {
                return .literal(level + 1)
            }
            return .succ(normalizedInner)

        case .max(let left, let right):
            let normalizedLeft = left.normalized()
            let normalizedRight = right.normalized()
            switch (normalizedLeft, normalizedRight) {
            case (.literal(let i), .literal(let j)):
                return .literal(Swift.max(i, j))
            case let (a, b) where a == b:
                return a
            case (.literal(0), let other), (let other, .literal(0)):
                return other
            default:
                if Self.canonicalOrder(normalizedLeft, before: normalizedRight) {
                    return .max(normalizedLeft, normalizedRight)
                }
                return .max(normalizedRight, normalizedLeft)
            }
        }
    }

    private static func canonicalOrder(_ left: UniverseLevel, before right: UniverseLevel) -> Bool {
        String(describing: left) < String(describing: right)
    }
}

/// Assumed inequalities between universe levels. Used by cumulativity when a
/// level is not a concrete integer.
public struct UniverseConstraints: Sendable {
    private var assumptions: [Assumption] = []

    public init() {}

    public mutating func assumeLessOrEqual(_ lower: UniverseLevel, _ upper: UniverseLevel) {
        let normalizedLower = lower.normalized()
        let normalizedUpper = upper.normalized()
        if normalizedLower == normalizedUpper { return }
        assumptions.append(Assumption(lower: normalizedLower, upper: normalizedUpper))
    }

    public func lessOrEqual(_ lower: UniverseLevel, _ upper: UniverseLevel) -> Bool {
        lessOrEqual(lower.normalized(), upper.normalized(), visiting: [])
    }

    private func lessOrEqual(
        _ lower: UniverseLevel,
        _ upper: UniverseLevel,
        visiting: Set<Visit>
    ) -> Bool {
        if lower == upper { return true }

        let visit = Visit(lower: lower, upper: upper)
        guard !visiting.contains(visit) else { return false }
        var visiting = visiting
        visiting.insert(visit)

        switch (lower, upper) {
        case (.literal(let i), .literal(let j)):
            return i <= j

        case (.succ(let lowerInner), .succ(let upperInner)):
            return lessOrEqual(lowerInner, upperInner, visiting: visiting)

        case (_, .succ(let upperInner)):
            if lessOrEqual(lower, upperInner, visiting: visiting) {
                return true
            }

        case (.max(let left, let right), _):
            return lessOrEqual(left, upper, visiting: visiting)
                && lessOrEqual(right, upper, visiting: visiting)

        case (_, .max(let left, let right)):
            if lessOrEqual(lower, left, visiting: visiting)
                || lessOrEqual(lower, right, visiting: visiting)
            {
                return true
            }

        default:
            break
        }

        for assumption in assumptions {
            if lessOrEqual(lower, assumption.lower, visiting: visiting)
                && lessOrEqual(assumption.upper, upper, visiting: visiting)
            {
                return true
            }
        }
        return false
    }

    private struct Assumption: Hashable, Sendable {
        var lower: UniverseLevel
        var upper: UniverseLevel
    }

    private struct Visit: Hashable {
        var lower: UniverseLevel
        var upper: UniverseLevel
    }
}
