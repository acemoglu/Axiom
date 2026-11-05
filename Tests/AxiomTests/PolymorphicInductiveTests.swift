import XCTest
@testable import Axiom

final class PolymorphicInductiveTests: XCTestCase {

    func testListSpecializesAtTwoUniverses() throws {
        var checker = TypeChecker()
        try registerPolymorphicList(into: &checker)

        let list0 = Term.constant("List", levels: [.literal(0)])
        let list1 = Term.constant("List", levels: [.literal(1)])
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(
                list0,
                expected: Term.pi(param: "A", type: .universe(0), body: .universe(0))
            )
        )
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(
                list1,
                expected: Term.pi(param: "A", type: .universe(1), body: .universe(1))
            )
        )
        XCTAssertThrowsError(
            try checker.checkTermMatchesType(
                list0,
                expected: Term.pi(param: "A", type: .universe(1), body: .universe(1))
            )
        ) { error in
            guard case .typeMismatch = error as? TypeError else {
                return XCTFail("Expected typeMismatch, got \(error)")
            }
        }
    }

    func testNilAtZeroInhabitsListAtZero() throws {
        var env = DeclarationEnvironment()
        try env.add(Declaration(name: "Nat", kind: .inductive, type: .universe(0)))
        try env.add(Declaration(name: "zero", kind: .constructor, type: .variable("Nat")))
        try env.closeInductive("Nat")

        var checker = TypeChecker(declarations: env)
        try registerPolymorphicList(into: &checker)

        let nilNat = Term.application(
            function: .constant("nil", levels: [.literal(0)]),
            argument: .variable("Nat")
        )
        let listNat = Term.application(
            function: .constant("List", levels: [.literal(0)]),
            argument: .variable("Nat")
        )
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(nilNat, expected: listNat)
        )
    }

    func testConsBuildsListAtOne() throws {
        var checker = TypeChecker()
        try registerPolymorphicList(into: &checker)

        let elementType = Term.universe(0)
        let nilA = Term.application(
            function: .constant("nil", levels: [.literal(1)]),
            argument: elementType
        )
        let cons = Term.application(
            function: Term.application(
                function: Term.application(
                    function: .constant("cons", levels: [.literal(1)]),
                    argument: elementType
                ),
                argument: .variable("x")
            ),
            argument: nilA
        )
        let listA = Term.application(
            function: .constant("List", levels: [.literal(1)]),
            argument: elementType
        )
        XCTAssertNoThrow(
            try checker.checkTermMatchesType(
                cons,
                expected: listA,
                environment: ["x": elementType]
            )
        )
    }

    private func registerPolymorphicList(into checker: inout TypeChecker) throws {
        let u = UniverseLevel.variable("u")
        let listA = Term.application(function: .variable("List"), argument: .variable("A"))
        try checker.checkDeclaration(Declaration(
            name: "List",
            kind: .inductive,
            type: Term.pi(param: "A", type: .universe(u), body: .universe(u)),
            levelParameters: ["u"]
        ))
        try checker.checkDeclaration(Declaration(
            name: "nil",
            kind: .constructor,
            type: Term.pi(param: "A", type: .universe(u), body: listA),
            levelParameters: ["u"]
        ))
        try checker.checkDeclaration(Declaration(
            name: "cons",
            kind: .constructor,
            type: Term.pi(
                param: "A",
                type: .universe(u),
                body: Term.pi(
                    param: "h",
                    type: .variable("A"),
                    body: Term.pi(param: "t", type: listA, body: listA)
                )
            ),
            levelParameters: ["u"]
        ))
        try checker.closeInductive("List")
    }
}
