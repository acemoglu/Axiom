/// Structural termination checks for recursive definitions.
public enum TerminationError: Error, Equatable, Sendable {
    case unsupportedRecursion(String)
    case recursionNotOnMatch(String)
    case recursionNotOnSmallerArgument(String, callArgument: String)
}

public struct TerminationChecker {
    public init() {}

    public func checkDefinition(name: String, value: Term) throws {
        guard containsSelfCall(value, name: name) else { return }

        let (parameters, body) = peelAbstractions(value)
        guard case .match(let scrutinee, _, let cases) = body,
              case .variable(let scrutineeName) = scrutinee else {
            throw TerminationError.recursionNotOnMatch(name)
        }
        guard parameters.contains(scrutineeName) else {
            throw TerminationError.recursionNotOnMatch(name)
        }

        for (_, branch) in cases {
            let binders = branchPatternBinders(branch)
            if containsBareSelfReference(in: branch, name: name) {
                throw TerminationError.recursionNotOnSmallerArgument(
                    name,
                    callArgument: name
                )
            }
            for arguments in selfCallArgumentTerms(in: branch, name: name) {
                try validateStructuralDescent(
                    arguments: arguments,
                    binders: binders,
                    definitionName: name
                )
            }
        }
    }

    private func validateStructuralDescent(
        arguments: [Term],
        binders: Set<String>,
        definitionName: String
    ) throws {
        guard !arguments.isEmpty else {
            throw TerminationError.recursionNotOnSmallerArgument(
                definitionName,
                callArgument: "$nonvar"
            )
        }
        guard arguments.contains(where: { isStrictStructuralDescent($0, binders: binders) }) else {
            let reported = arguments.map(describeArgument).joined(separator: ", ")
            throw TerminationError.recursionNotOnSmallerArgument(
                definitionName,
                callArgument: reported
            )
        }
    }

    private func peelAbstractions(_ term: Term) -> (parameters: [String], body: Term) {
        var parameters: [String] = []
        var current = term
        while case .abstraction(let param, _, let body) = current {
            parameters.append(param)
            current = body
        }
        return (parameters, current)
    }

    private func branchPatternBinders(_ branch: Term) -> Set<String> {
        var binders: Set<String> = []
        var current = branch
        while case .abstraction(let param, _, let body) = current {
            binders.insert(param)
            current = body
        }
        return binders
    }

    private func containsSelfCall(_ term: Term, name: String) -> Bool {
        switch term {
        case .variable(let variableName):
            return variableName == name
        case .application(let function, let argument):
            return containsSelfCall(function, name: name) || containsSelfCall(argument, name: name)
        case .abstraction(_, _, let body):
            return containsSelfCall(body, name: name)
        case .match(let scrutinee, _, let cases):
            return containsSelfCall(scrutinee, name: name)
                || cases.values.contains { containsSelfCall($0, name: name) }
        case .pi(_, let domain, let body):
            return containsSelfCall(domain, name: name) || containsSelfCall(body, name: name)
        case .inductive(_, let type), .constructor(_, _, let type):
            return containsSelfCall(type, name: name)
        case .hole, .universe:
            return false
        }
    }

    private func containsBareSelfReference(in term: Term, name: String) -> Bool {
        switch term {
        case .variable(let variableName):
            return variableName == name
        case .application(let function, let argument):
            if isSelfCallHead(function, name: name) {
                return containsBareSelfReference(in: argument, name: name)
            }
            return containsBareSelfReference(in: function, name: name)
                || containsBareSelfReference(in: argument, name: name)
        case .abstraction(_, _, let body):
            return containsBareSelfReference(in: body, name: name)
        case .match(let scrutinee, _, let cases):
            return containsBareSelfReference(in: scrutinee, name: name)
                || cases.values.contains { containsBareSelfReference(in: $0, name: name) }
        case .pi(_, let domain, let body):
            return containsBareSelfReference(in: domain, name: name)
                || containsBareSelfReference(in: body, name: name)
        case .inductive(_, let type), .constructor(_, _, let type):
            return containsBareSelfReference(in: type, name: name)
        case .hole, .universe:
            return false
        }
    }

    private func isSelfCallHead(_ function: Term, name: String) -> Bool {
        if case .variable(let variableName) = function {
            return variableName == name
        }
        var current = function
        while case .application(let head, _) = current {
            current = head
        }
        if case .variable(let variableName) = current {
            return variableName == name
        }
        return false
    }

    private func selfCallArgumentTerms(in term: Term, name: String) -> [[Term]] {
        var sites: [[Term]] = []
        collectSelfCallSites(term, name: name, into: &sites)
        return sites
    }

    private func collectSelfCallSites(_ term: Term, name: String, into sites: inout [[Term]]) {
        if let arguments = maximalSelfCallArguments(in: term, name: name) {
            sites.append(arguments)
            for argument in arguments {
                collectSelfCallSites(argument, name: name, into: &sites)
            }
            return
        }
        switch term {
        case .application(let function, let argument):
            collectSelfCallSites(function, name: name, into: &sites)
            collectSelfCallSites(argument, name: name, into: &sites)
        case .pi(_, let domain, let body):
            collectSelfCallSites(domain, name: name, into: &sites)
            collectSelfCallSites(body, name: name, into: &sites)
        case .abstraction(_, let paramType, let body):
            collectSelfCallSites(paramType, name: name, into: &sites)
            collectSelfCallSites(body, name: name, into: &sites)
        case .match(let scrutinee, let motive, let cases):
            collectSelfCallSites(scrutinee, name: name, into: &sites)
            collectSelfCallSites(motive, name: name, into: &sites)
            for branch in cases.values {
                collectSelfCallSites(branch, name: name, into: &sites)
            }
        case .hole, .universe, .variable, .inductive, .constructor:
            break
        }
    }

    private func maximalSelfCallArguments(in term: Term, name: String) -> [Term]? {
        guard case .application = term else { return nil }
        var arguments: [Term] = []
        var current = term
        while case .application(let function, let argument) = current {
            arguments.append(argument)
            current = function
        }
        guard case .variable(let functionName) = current, functionName == name else {
            return nil
        }
        return arguments.reversed()
    }

    private func isStrictStructuralDescent(_ term: Term, binders: Set<String>) -> Bool {
        guard case .variable(let binderName) = term else { return false }
        return binders.contains(binderName)
    }

    private func describeArgument(_ term: Term) -> String {
        switch term {
        case .variable(let name):
            return name
        case .application(let function, let argument):
            return "\(describeArgument(function)) \(describeArgument(argument))"
        default:
            return "$term"
        }
    }
}
