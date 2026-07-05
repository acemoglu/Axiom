/// Fuel counter guaranteeing termination of normalization during type checking.
public struct ReductionBudget: Sendable {
    public static let defaultSteps = 100_000

    public var remaining: Int

    public init(steps: Int = Self.defaultSteps) {
        remaining = steps
    }

    public mutating func consume() throws {
        guard remaining > 0 else {
            throw ReductionError.outOfFuel
        }
        remaining -= 1
    }
}

/// Failures during bounded β/match reduction.
public enum ReductionError: Error, Equatable, Sendable {
    case outOfFuel
}
