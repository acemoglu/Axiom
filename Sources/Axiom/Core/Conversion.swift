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
        return areDefinitionallyEqualAssumingNormalized(normalizedLeft, normalizedRight)
    }

    /// Compares terms that are already in the checker’s normal form. Skips a second
    /// normalization pass when the caller has already normalized both sides once.
    func areDefinitionallyEqualAssumingNormalized(_ left: Term, _ right: Term) -> Bool {
        alphaEquivalent(etaShort(left), etaShort(right))
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
            if case .abstraction(_, _, let body) = reducedFunction.kind {
                return try weakHeadNormalize(
                    body.instantiated(with: argument),
                    budget: &budget,
                    unfolding: unfolding
                )
            }
            return .application(function: reducedFunction, argument: argument)
        case .localLet(_, _, let value, let body):
            let reducedValue = try weakHeadNormalize(value, budget: &budget, unfolding: unfolding)
            return try weakHeadNormalize(
                body.instantiated(with: reducedValue),
                budget: &budget,
                unfolding: unfolding
            )
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

    /// O(1), unconditionally. ``Term`` binds variables by de Bruijn index rather than by
    /// name, and ``TermPool`` interns `pi`/`abstraction` nodes by their (type, de Bruijn
    /// body) pair — deliberately ignoring each binder's display `hint`. Two alpha-equivalent
    /// terms therefore always share the same arena intern id.
    private func alphaEquivalent(_ t1: Term, _ t2: Term) -> Bool {
        t1 == t2
    }

    /// Contracts `λx. f x` to `f` wherever `x` is not free in `f`, including under binders.
    private func etaShort(_ term: Term) -> Term {
        if let reduct = term.etaReduct() {
            return etaShort(reduct)
        }
        switch term.kind {
        case .variable, .hole, .universe, .boundVariable, .prop:
            return term
        case .application(let function, let argument):
            let rebuilt = Term.application(function: etaShort(function), argument: etaShort(argument))
            if let reduct = rebuilt.etaReduct() { return etaShort(reduct) }
            return rebuilt
        case .abstraction(let hint, let type, let body):
            let rebuilt = Term.rawAbstraction(hint: hint, type: etaShort(type), body: etaShort(body))
            if let reduct = rebuilt.etaReduct() { return etaShort(reduct) }
            return rebuilt
        case .localLet(let hint, let type, let value, let body):
            return .rawLocalLet(
                hint: hint,
                type: etaShort(type),
                value: etaShort(value),
                body: etaShort(body)
            )
        case .pi(let hint, let type, let body):
            return .rawPi(hint: hint, type: etaShort(type), body: etaShort(body))
        case .inductive(let name, let type):
            return .inductive(name: name, type: etaShort(type))
        case .constructor(let name, let inductiveName, let type):
            return .constructor(name: name, inductiveName: inductiveName, type: etaShort(type))
        case .match(let scrutinee, let motive, let cases):
            return .match(
                scrutinee: etaShort(scrutinee),
                motive: etaShort(motive),
                cases: cases.mapValues { etaShort($0) }
            )
        }
    }
}
