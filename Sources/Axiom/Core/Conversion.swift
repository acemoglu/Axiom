public enum ConversionStrategy: Sendable {
    case weakHeadNormalForm
    case normalForm
}

public struct Conversion {
    public let strategy: ConversionStrategy

    public init(strategy: ConversionStrategy = .normalForm) {
        self.strategy = strategy
    }

    public func normalize(
        _ term: Term,
        budget: inout ReductionBudget,
        unfolding: [String: Term] = [:]
    ) throws -> Term {
        switch strategy {
        case .weakHeadNormalForm:
            return try weakHeadNormalize(term, budget: &budget, unfolding: unfolding)
        case .normalForm:
            return try term.reduced(budget: &budget, unfolding: unfolding)
        }
    }

    public func areDefinitionallyEqual(
        _ left: Term,
        _ right: Term,
        budget: inout ReductionBudget,
        unfolding: [String: Term] = [:]
    ) throws -> Bool {
        let normalizedLeft = try normalize(left, budget: &budget, unfolding: unfolding)
        let normalizedRight = try normalize(right, budget: &budget, unfolding: unfolding)
        return alphaEquivalent(normalizedLeft, normalizedRight)
    }

    public func normalize(_ term: Term, unfolding: [String: Term] = [:]) throws -> Term {
        var budget = ReductionBudget()
        return try normalize(term, budget: &budget, unfolding: unfolding)
    }

    public func areDefinitionallyEqual(
        _ left: Term,
        _ right: Term,
        unfolding: [String: Term] = [:]
    ) throws -> Bool {
        var budget = ReductionBudget()
        return try areDefinitionallyEqual(left, right, budget: &budget, unfolding: unfolding)
    }

    private func weakHeadNormalize(
        _ term: Term,
        budget: inout ReductionBudget,
        unfolding: [String: Term]
    ) throws -> Term {
        try budget.consume()
        if case .variable(let name) = term.kind, let value = unfolding[name] {
            return try weakHeadNormalize(value, budget: &budget, unfolding: unfolding)
        }
        switch term.kind {
        case .application(let function, let argument):
            let reducedFunction = try weakHeadNormalize(function, budget: &budget, unfolding: unfolding)
            if case .abstraction(let param, _, let body) = reducedFunction.kind {
                return try weakHeadNormalize(
                    body.substituting(name: param, with: argument),
                    budget: &budget,
                    unfolding: unfolding
                )
            }
            return .application(function: reducedFunction, argument: argument)
        case .match(let scrutinee, let motive, let cases):
            return try .match(
                scrutinee: weakHeadNormalize(scrutinee, budget: &budget, unfolding: unfolding),
                motive: motive,
                cases: cases
            ).reduced(budget: &budget, unfolding: unfolding)
        default:
            return term
        }
    }

    private func alphaEquivalent(_ t1: Term, _ t2: Term) -> Bool {
        func compare(_ lhs: Term, _ rhs: Term, mapping: inout [String: String]) -> Bool {
            // Fast path: hash-consing means structurally-identical subterms are literally
            // the same instance. If they're pointer-equal *and* none of this subterm's free
            // variables have been renamed by an enclosing binder mismatch, it is trivially
            // alpha-equivalent to itself — bypass the deep walk entirely.
            if lhs === rhs, lhs.freeVariables.allSatisfy({ (mapping[$0] ?? $0) == $0 }) {
                return true
            }
            switch (lhs.kind, rhs.kind) {
            case (.variable(let l), .variable(let r)):
                if let mapped = mapping[l] { return mapped == r }
                return l == r
            case (.hole(let l), .hole(let r)):
                return l == r
            case (.universe(let l), .universe(let r)):
                return l == r
            case (.application(let lf, let la), .application(let rf, let ra)):
                return compare(lf, rf, mapping: &mapping) && compare(la, ra, mapping: &mapping)
            case (.pi(let lp, let lt, let lb), .pi(let rp, let rt, let rb)),
                 (.abstraction(let lp, let lt, let lb), .abstraction(let rp, let rt, let rb)):
                guard compare(lt, rt, mapping: &mapping) else { return false }
                let previous = mapping[lp]
                mapping[lp] = rp
                let result = compare(lb, rb, mapping: &mapping)
                if let previous {
                    mapping[lp] = previous
                } else {
                    mapping.removeValue(forKey: lp)
                }
                return result
            case (.inductive(let ln, let lt), .inductive(let rn, let rt)):
                return ln == rn && compare(lt, rt, mapping: &mapping)
            case (.constructor(let ln, let li, let lt), .constructor(let rn, let ri, let rt)):
                return ln == rn && li == ri && compare(lt, rt, mapping: &mapping)
            case (.match(let ls, let lm, let lc), .match(let rs, let rm, let rc)):
                guard lc.keys == rc.keys,
                      compare(ls, rs, mapping: &mapping),
                      compare(lm, rm, mapping: &mapping) else { return false }
                for key in lc.keys {
                    guard let lv = lc[key], let rv = rc[key], compare(lv, rv, mapping: &mapping) else {
                        return false
                    }
                }
                return true
            default:
                return false
            }
        }

        var mapping: [String: String] = [:]
        return compare(t1, t2, mapping: &mapping)
    }
}
