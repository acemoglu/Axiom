/// Structural proximity / distance heuristics for partial proof search.
///
/// Without embeddings, we score how closely an inferred (or goal) type matches the
/// target by walking both ASTs: matching kinds, Π telescopes, application spines, and
/// universe levels earn higher scores. Holes act as wildcards (partial credit).
public enum ProximityMetric: Sendable {

    /// Returns a score in *[0, 1]* measuring structural similarity of `currentType` to
    /// `targetType`. Exact structural identity yields `1.0`.
    public static func calculateProximity(currentType: Term, targetType: Term) -> Double {
        proximity(currentType, targetType, depth: 0)
    }

    // MARK: - Recursive scoring

    private static func proximity(_ left: Term, _ right: Term, depth: Int) -> Double {
        if left == right { return 1.0 }

        // Metavariables are soft wildcards: they can stand for any remaining structure.
        switch (left.kind, right.kind) {
        case (.hole, _), (_, .hole):
            return max(0.35, 0.85 - Double(depth) * 0.05)

        case (.universe(let i), .universe(let j)):
            let distance = abs(i - j)
            return distance == 0 ? 1.0 : max(0, 1.0 - Double(distance) * 0.25)

        case (.variable(let a), .variable(let b)):
            return a == b ? 1.0 : 0.0

        case (.boundVariable(let i), .boundVariable(let j)):
            return i == j ? 1.0 : 0.0

        case (
            .pi(_, let leftDomain, let leftBody),
            .pi(_, let rightDomain, let rightBody)
        ):
            let domainScore = proximity(leftDomain, rightDomain, depth: depth + 1)
            let bodyScore = proximity(leftBody, rightBody, depth: depth + 1)
            // Π-structure match is itself a strong signal even before domains align.
            return 0.15 + 0.40 * domainScore + 0.45 * bodyScore

        case (
            .abstraction(_, let leftType, let leftBody),
            .abstraction(_, let rightType, let rightBody)
        ):
            let typeScore = proximity(leftType, rightType, depth: depth + 1)
            let bodyScore = proximity(leftBody, rightBody, depth: depth + 1)
            return 0.15 + 0.35 * typeScore + 0.50 * bodyScore

        case (
            .application(let leftFn, let leftArg),
            .application(let rightFn, let rightArg)
        ):
            let fnScore = proximity(leftFn, rightFn, depth: depth + 1)
            let argScore = proximity(leftArg, rightArg, depth: depth + 1)
            return 0.10 + 0.55 * fnScore + 0.35 * argScore

        case (
            .inductive(let leftName, let leftType),
            .inductive(let rightName, let rightType)
        ):
            let nameScore = leftName == rightName ? 1.0 : 0.0
            let typeScore = proximity(leftType, rightType, depth: depth + 1)
            return 0.55 * nameScore + 0.45 * typeScore

        case (
            .constructor(let leftName, let leftInd, let leftType),
            .constructor(let rightName, let rightInd, let rightType)
        ):
            let nameScore = leftName == rightName ? 1.0 : 0.0
            let indScore = leftInd == rightInd ? 1.0 : 0.0
            let typeScore = proximity(leftType, rightType, depth: depth + 1)
            return 0.35 * nameScore + 0.30 * indScore + 0.35 * typeScore

        case (
            .match(let leftScrutinee, let leftMotive, let leftCases),
            .match(let rightScrutinee, let rightMotive, let rightCases)
        ):
            let scrutineeScore = proximity(leftScrutinee, rightScrutinee, depth: depth + 1)
            let motiveScore = proximity(leftMotive, rightMotive, depth: depth + 1)
            let caseScore = caseProximity(leftCases, rightCases, depth: depth + 1)
            return 0.35 * scrutineeScore + 0.35 * motiveScore + 0.30 * caseScore

        default:
            // Kind mismatch — still give tiny credit when both are binders / both apps
            // so nested search can prefer "same shape family" over random noise.
            return kindFamilyBonus(left.kind, right.kind)
        }
    }

    private static func caseProximity(
        _ left: [String: Term],
        _ right: [String: Term],
        depth: Int
    ) -> Double {
        let keys = Set(left.keys).union(right.keys)
        guard !keys.isEmpty else { return 1.0 }
        var total = 0.0
        for key in keys {
            switch (left[key], right[key]) {
            case let (l?, r?):
                total += proximity(l, r, depth: depth)
            default:
                total += 0.0
            }
        }
        return total / Double(keys.count)
    }

    private static func kindFamilyBonus(_ left: Term.Kind, _ right: Term.Kind) -> Double {
        func family(_ kind: Term.Kind) -> Int {
            switch kind {
            case .pi, .abstraction: return 1
            case .application: return 2
            case .universe: return 3
            case .variable, .boundVariable: return 4
            case .hole: return 5
            case .inductive, .constructor: return 6
            case .match: return 7
            }
        }
        return family(left) == family(right) ? 0.08 : 0.0
    }
}
