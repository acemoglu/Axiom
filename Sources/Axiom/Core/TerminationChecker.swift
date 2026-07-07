/// Structural termination checks for recursive definitions.
public enum TerminationError: Error, Equatable, Sendable {
    case unsupportedRecursion(String)
    case recursionNotOnMatch(String)
    case recursionNotOnSmallerArgument(String, callArgument: String)
}

public struct TerminationChecker {
    public init() {}

    public func checkDefinition(name: String, value: Term) throws {
        try checkDefinition(name: name, value: value, cluster: [name])
    }

    /// Verifies termination for a definition within its mutually-recursive cluster.
    public func checkDefinition(name: String, value: Term, cluster: Set<String>) throws {
        guard containsCall(to: cluster, in: value) else { return }

        let (parameters, body) = peelAbstractions(value)
        guard case .match(let scrutinee, _, let cases) = body.kind,
              case .variable(let scrutineeName) = scrutinee.kind else {
            throw TerminationError.recursionNotOnMatch(name)
        }
        guard parameters.contains(scrutineeName) else {
            throw TerminationError.recursionNotOnMatch(name)
        }

        for (_, branch) in cases {
            let binders = branchPatternBinders(branch)
            if containsBareRecursiveReference(in: branch, targets: cluster) {
                throw TerminationError.recursionNotOnSmallerArgument(
                    name,
                    callArgument: name
                )
            }
            for arguments in callArgumentTerms(in: branch, targets: cluster) {
                try validateStructuralDescent(
                    arguments: arguments,
                    binders: binders,
                    definitionName: name
                )
            }
        }
    }

    /// Validates termination for every member of the SCC containing a new definition.
    public func checkClusterTermination(
        newName: String,
        newValue: Term,
        existingDeclarations: [Declaration]
    ) throws {
        let definable = existingDeclarations.filter {
            switch $0.kind {
            case .definition, .theorem, .constant:
                return $0.value != nil
            case .axiom, .inductive, .constructor:
                return false
            }
        }
        var names = Set(definable.map(\.name))
        names.insert(newName)
        var callGraph = buildCallGraph(for: definable, among: names)
        callGraph[newName] = calleeNames(in: newValue, among: names)
        let cluster = sccContaining(newName, in: callGraph, nodes: names)
        let defsByName = Dictionary(uniqueKeysWithValues: definable.map { ($0.name, $0) })

        for member in cluster.sorted() {
            let value: Term
            if member == newName {
                value = newValue
            } else if let existing = defsByName[member]?.value {
                value = existing
            } else {
                continue
            }
            try checkDefinition(name: member, value: value, cluster: cluster)
        }
    }

    /// Checks termination for a new definition against existing declarations in the environment.
    public func checkMutualTermination(
        name: String,
        value: Term,
        existingDeclarations: [Declaration]
    ) throws {
        try checkClusterTermination(
            newName: name,
            newValue: value,
            existingDeclarations: existingDeclarations
        )
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

    private func buildCallGraph(for declarations: [Declaration], among names: Set<String>) -> [String: Set<String>] {
        var graph: [String: Set<String>] = [:]
        for declaration in declarations {
            guard let value = declaration.value else { continue }
            graph[declaration.name] = calleeNames(in: value, among: names)
        }
        return graph
    }

    private func calleeNames(in term: Term, among names: Set<String>) -> Set<String> {
        var callees: Set<String> = []
        collectCalleeNames(in: term, among: names, into: &callees)
        return callees
    }

    private func collectCalleeNames(
        in term: Term,
        among names: Set<String>,
        into callees: inout Set<String>
    ) {
        switch term.kind {
        case .application(let function, let argument):
            if let callee = headVariable(in: function), names.contains(callee) {
                callees.insert(callee)
            }
            collectCalleeNames(in: function, among: names, into: &callees)
            collectCalleeNames(in: argument, among: names, into: &callees)
        case .abstraction(_, _, let body):
            // `names` are global (mutually-recursive) declaration names, never local bound
            // parameters, so a call site is always `.variable(globalName)` regardless of
            // whether enclosing binders are opened — walking the raw de Bruijn body is safe.
            collectCalleeNames(in: body, among: names, into: &callees)
        case .match(let scrutinee, let motive, let cases):
            collectCalleeNames(in: scrutinee, among: names, into: &callees)
            collectCalleeNames(in: motive, among: names, into: &callees)
            for branch in cases.values {
                collectCalleeNames(in: branch, among: names, into: &callees)
            }
        case .pi(_, let domain, let body):
            collectCalleeNames(in: domain, among: names, into: &callees)
            collectCalleeNames(in: body, among: names, into: &callees)
        case .inductive(_, let type), .constructor(_, _, let type):
            collectCalleeNames(in: type, among: names, into: &callees)
        case .hole, .universe, .variable, .boundVariable:
            break
        }
    }

    private func headVariable(in term: Term) -> String? {
        var current = term
        while case .application(let function, _) = current.kind {
            current = function
        }
        if case .variable(let name) = current.kind {
            return name
        }
        return nil
    }

    private func sccContaining(
        _ node: String,
        in graph: [String: Set<String>],
        nodes: Set<String>
    ) -> Set<String> {
        var index = 0
        var stack: [String] = []
        var onStack: Set<String> = []
        var indices: [String: Int] = [:]
        var lowlinks: [String: Int] = [:]
        var sccs: [[String]] = []

        func strongConnect(_ vertex: String) {
            indices[vertex] = index
            lowlinks[vertex] = index
            index += 1
            stack.append(vertex)
            onStack.insert(vertex)

            for successor in graph[vertex, default: []] where nodes.contains(successor) {
                if indices[successor] == nil {
                    strongConnect(successor)
                    lowlinks[vertex] = min(lowlinks[vertex]!, lowlinks[successor]!)
                } else if onStack.contains(successor) {
                    lowlinks[vertex] = min(lowlinks[vertex]!, indices[successor]!)
                }
            }

            if lowlinks[vertex] == indices[vertex] {
                var component: [String] = []
                while true {
                    let w = stack.removeLast()
                    onStack.remove(w)
                    component.append(w)
                    if w == vertex { break }
                }
                sccs.append(component)
            }
        }

        for vertex in nodes where indices[vertex] == nil {
            strongConnect(vertex)
        }

        for component in sccs where component.contains(node) {
            return Set(component)
        }
        return [node]
    }

    /// Opens each abstraction with its own hint as we peel: downstream structural-descent
    /// checks compare `.variable(name)` occurrences inside `body` against these exact
    /// `parameters`, so the body must have those parameters free-by-name, not as raw bound
    /// indices.
    private func peelAbstractions(_ term: Term) -> (parameters: [String], body: Term) {
        var parameters: [String] = []
        var current = term
        while case .abstraction(let param, _, let rawBody) = current.kind {
            parameters.append(param)
            current = rawBody.instantiated(with: .variable(param))
        }
        return (parameters, current)
    }

    /// See ``peelAbstractions(_:)``: the collected `binders` are later matched by name
    /// against occurrences inside this same (opened) body, via ``collectCallSites``.
    private func branchPatternBinders(_ branch: Term) -> Set<String> {
        var binders: Set<String> = []
        var current = branch
        while case .abstraction(let param, _, let rawBody) = current.kind {
            binders.insert(param)
            current = rawBody.instantiated(with: .variable(param))
        }
        return binders
    }

    private func containsCall(to targets: Set<String>, in term: Term) -> Bool {
        switch term.kind {
        case .variable(let variableName):
            return targets.contains(variableName)
        case .application(let function, let argument):
            return containsCall(to: targets, in: function) || containsCall(to: targets, in: argument)
        case .abstraction(_, _, let body):
            return containsCall(to: targets, in: body)
        case .match(let scrutinee, _, let cases):
            return containsCall(to: targets, in: scrutinee)
                || cases.values.contains { containsCall(to: targets, in: $0) }
        case .pi(_, let domain, let body):
            return containsCall(to: targets, in: domain) || containsCall(to: targets, in: body)
        case .inductive(_, let type), .constructor(_, _, let type):
            return containsCall(to: targets, in: type)
        case .hole, .universe, .boundVariable:
            return false
        }
    }

    private func containsBareRecursiveReference(in term: Term, targets: Set<String>) -> Bool {
        switch term.kind {
        case .variable(let variableName):
            return targets.contains(variableName)
        case .application(let function, let argument):
            if isRecursiveCallHead(function, targets: targets) {
                return containsBareRecursiveReference(in: argument, targets: targets)
            }
            return containsBareRecursiveReference(in: function, targets: targets)
                || containsBareRecursiveReference(in: argument, targets: targets)
        case .abstraction(_, _, let body):
            return containsBareRecursiveReference(in: body, targets: targets)
        case .match(let scrutinee, _, let cases):
            return containsBareRecursiveReference(in: scrutinee, targets: targets)
                || cases.values.contains { containsBareRecursiveReference(in: $0, targets: targets) }
        case .pi(_, let domain, let body):
            return containsBareRecursiveReference(in: domain, targets: targets)
                || containsBareRecursiveReference(in: body, targets: targets)
        case .inductive(_, let type), .constructor(_, _, let type):
            return containsBareRecursiveReference(in: type, targets: targets)
        case .hole, .universe, .boundVariable:
            return false
        }
    }

    private func isRecursiveCallHead(_ function: Term, targets: Set<String>) -> Bool {
        if case .variable(let variableName) = function.kind {
            return targets.contains(variableName)
        }
        var current = function
        while case .application(let head, _) = current.kind {
            current = head
        }
        if case .variable(let variableName) = current.kind {
            return targets.contains(variableName)
        }
        return false
    }

    private func callArgumentTerms(in term: Term, targets: Set<String>) -> [[Term]] {
        var sites: [[Term]] = []
        collectCallSites(term, targets: targets, into: &sites)
        return sites
    }

    private func collectCallSites(_ term: Term, targets: Set<String>, into sites: inout [[Term]]) {
        if let arguments = maximalCallArguments(in: term, targets: targets) {
            sites.append(arguments)
            for argument in arguments {
                collectCallSites(argument, targets: targets, into: &sites)
            }
            return
        }
        switch term.kind {
        case .application(let function, let argument):
            collectCallSites(function, targets: targets, into: &sites)
            collectCallSites(argument, targets: targets, into: &sites)
        case .pi(let hint, let domain, let rawBody):
            collectCallSites(domain, targets: targets, into: &sites)
            collectCallSites(rawBody.instantiated(with: .variable(hint)), targets: targets, into: &sites)
        case .abstraction(let hint, let paramType, let rawBody):
            // Unlike `containsCall`/`containsBareRecursiveReference` (which only match
            // *global* names), the call-argument terms collected here are later tested by
            // `isStrictStructuralDescent` against *local* pattern binders — so nested
            // references to an enclosing parameter must come back as `.variable(hint)`,
            // not a raw bound index, or a legitimate structural-descent call would be
            // rejected as non-terminating.
            collectCallSites(paramType, targets: targets, into: &sites)
            collectCallSites(rawBody.instantiated(with: .variable(hint)), targets: targets, into: &sites)
        case .match(let scrutinee, let motive, let cases):
            collectCallSites(scrutinee, targets: targets, into: &sites)
            collectCallSites(motive, targets: targets, into: &sites)
            for branch in cases.values {
                collectCallSites(branch, targets: targets, into: &sites)
            }
        case .hole, .universe, .variable, .boundVariable, .inductive, .constructor:
            break
        }
    }

    private func maximalCallArguments(in term: Term, targets: Set<String>) -> [Term]? {
        guard case .application = term.kind else { return nil }
        var arguments: [Term] = []
        var current = term
        while case .application(let function, let argument) = current.kind {
            arguments.append(argument)
            current = function
        }
        guard case .variable(let functionName) = current.kind, targets.contains(functionName) else {
            return nil
        }
        return arguments.reversed()
    }

    private func isStrictStructuralDescent(_ term: Term, binders: Set<String>) -> Bool {
        guard case .variable(let binderName) = term.kind else { return false }
        return binders.contains(binderName)
    }

    private func describeArgument(_ term: Term) -> String {
        switch term.kind {
        case .variable(let name):
            return name
        case .application(let function, let argument):
            return "\(describeArgument(function)) \(describeArgument(argument))"
        default:
            return "$term"
        }
    }
}
