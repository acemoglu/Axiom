public enum ConversionStrategy: Sendable {
    case weakHeadNormalForm
    case normalForm
}

public struct Conversion {
    public let strategy: ConversionStrategy

    public init(strategy: ConversionStrategy = .normalForm) {
        self.strategy = strategy
    }

    public func normalize(_ term: Term) -> Term {
        switch strategy {
        case .weakHeadNormalForm:
            return weakHeadNormalize(term)
        case .normalForm:
            return term.reduced()
        }
    }

    public func areDefinitionallyEqual(_ left: Term, _ right: Term) -> Bool {
        alphaEquivalent(normalize(left), normalize(right))
    }

    private func weakHeadNormalize(_ term: Term) -> Term {
        switch term {
        case .application(let function, let argument):
            let reducedFunction = weakHeadNormalize(function)
            if case .abstraction(let param, _, let body) = reducedFunction {
                return weakHeadNormalize(body.substituting(name: param, with: argument))
            }
            return .application(function: reducedFunction, argument: argument)
        case .match(let scrutinee, let cases):
            return .match(scrutinee: weakHeadNormalize(scrutinee), cases: cases).reduced()
        default:
            return term
        }
    }

    private func alphaEquivalent(_ t1: Term, _ t2: Term) -> Bool {
        func compare(_ lhs: Term, _ rhs: Term, mapping: inout [String: String]) -> Bool {
            switch (lhs, rhs) {
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
            case (.match(let ls, let lc), .match(let rs, let rc)):
                guard lc.keys == rc.keys, compare(ls, rs, mapping: &mapping) else { return false }
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
