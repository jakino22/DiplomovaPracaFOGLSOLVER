#include <iostream>
#include <memory>
#include <string>
#include <vector>
#include <ctime>

#include "Theory.h"
#include "translator.h"
#include "Solver.h"

using F = std::shared_ptr<Formula>;
using T = std::shared_ptr<Term>;


static F atom(const std::string &name) {
    return std::make_shared<PredicateAtom>(
            std::make_shared<Predicate>(name, std::vector<T>{std::make_shared<Variable>("x")})
    );
}

static F atomxyz(const std::string &name) {
    return std::make_shared<PredicateAtom>(
            std::make_shared<Predicate>(name,
                                        std::vector<T>{std::make_shared<Variable>("x"), std::make_shared<Variable>("y"),
                                                       std::make_shared<Variable>("z")})
    );
}

static F yatom(const std::string &name) {
    return std::make_shared<PredicateAtom>(
            std::make_shared<Predicate>(name, std::vector<T>{std::make_shared<Variable>("y")})
    );
}

static F Fatom(const std::string &name) {
    return std::make_shared<ForAll>(
            atom(name), std::make_shared<Variable>("x")
    );
}

static F Fa(F f) {
    return std::make_shared<ForAll>(
            f, std::make_shared<Variable>("x")
    );
}

static F Fay(F f) {
    return std::make_shared<ForAll>(
            f, std::make_shared<Variable>("y")
    );
}

static F Ea(F f) {
    return std::make_shared<Exists>(
            f, std::make_shared<Variable>("x")
    );
}

static F Ez(F f) {
    return std::make_shared<Exists>(
            f, std::make_shared<Variable>("z")
    );
}

static F Eatom(const std::string &name) {
    return std::make_shared<Exists>(
            atom(name), std::make_shared<Variable>("x")
    );
}

static std::shared_ptr<Literal>
lit(std::shared_ptr<EpsylonContent> e1, std::shared_ptr<EpsylonContent> e2, std::string op) {
    return std::make_shared<Literal>(e1, e2, op);
}

static F zero() {
    return std::make_shared<ConstantAtom>(std::make_shared<Constant>("0"));
}

static F oneHalf() {
    return std::make_shared<ConstantAtom>(std::make_shared<Constant>("0.5"));
}

static F one() {
    return std::make_shared<ConstantAtom>(std::make_shared<Constant>("1"));
}

static F impl(F a, F b) {
    return std::make_shared<Implication>(a, b);
}

static F conj(F a, F b) {
    return std::make_shared<Conjunction>(a, b);
}

static F disj(F a, F b) {
    return std::make_shared<Disjunction>(a, b);
}

static F neg(F a) {
    return impl(a, zero());
}

static SolverResult solveFormulaLessThanOne(F phi) {
    auto theory = std::make_shared<Theory>(std::vector<F>{phi});

    Translator translator;
    auto cnf = std::make_shared<CNF>(translator.translate(theory));
    cnf->clauses.front()->literals.front()->operation = "<";
    GodelSATSolver solver(cnf, Inferencer(cnf));
    return solver.solve(1); ///witness depth
}

static const char *toString(SolverResult r) {
    return r == SolverResult::UNSAT ? "UNSAT" : "SAT";
}

struct TestCase {
    std::string name;
    F formula;
    SolverResult expected;
};

static bool runOne(const TestCase &tc) {
    std::clock_t start = std::clock();
    SolverResult got = solveFormulaLessThanOne(tc.formula);
    std::clock_t end = std::clock();
    double cpu_time = double(end - start) / CLOCKS_PER_SEC;
    bool ok = (got == tc.expected);

    std::cout << (ok ? "[PASS] " : "[FAIL] ")
              << tc.name
              << "  expected=" << toString(tc.expected)
              << " got=" << toString(got)
              << "cpu time= " << std::to_string(cpu_time)
              << "\n";

    return ok;
}

static F lt(F a, F b) {
    return std::make_shared<StrictOrder>(a, b);
}

static F eq(F a, F b) {
    return std::make_shared<EkvEquivalence>(a, b);
}


int main() {

    auto p = atom("P");
    auto q = atom("Q");
    auto r = atom("R");
    auto s = atom("S");
    auto c13 = std::make_shared<ConstantAtom>(std::make_shared<Constant>("0.3"));


    std::vector<TestCase> tests = {
            {"I1",  impl(impl(p, q), impl(impl(q, r), impl(p, r))),          SolverResult::UNSAT},
            {"I2",  impl(p, disj(p, r)),                                     SolverResult::UNSAT},
            {"I3",  impl(r, disj(p, r)),                                     SolverResult::UNSAT},
            {"I4",  impl(impl(p, r), impl(impl(q, r), impl(disj(p, q), r))), SolverResult::UNSAT},
            {"I5",  impl(conj(p, q), p),                                     SolverResult::UNSAT},
            {"I6",  impl(conj(p, q), q),                                     SolverResult::UNSAT},
            {"I7",  impl(impl(r, p), impl(impl(r, q), impl(r, conj(p, q)))), SolverResult::UNSAT},
            {"I8",  impl(impl(p, impl(q, r)), impl(conj(p, q), r)),          SolverResult::UNSAT},
            {"I9",  impl(impl(conj(p, q), r), impl(p, impl(q, r))),          SolverResult::UNSAT},
            {"I10", impl(conj(p, neg(p)), q),                                SolverResult::UNSAT},
//            {"example 1",
//             impl(
//                     Fa(lt(atom("Q"), c13)),
//                     disj(
//                             Ea(lt(atom("Q"), c13)),
//                             eq(Eatom("Q"), c13)
//                     )
//             ),
//             SolverResult::UNSAT
//            },
//            {"example 2",
//                    impl(
//                            lt(Eatom("P"), Fatom("Q")),
//                            Fa(Fay(lt(atom("P"), yatom("Q"))))
//                    ),
//                    SolverResult::UNSAT
//            },
//            {"example 3",
//             impl(
//                     Ea(Fay(Ez(atomxyz("P")))),
//                     Fay(Ez(Ea(atomxyz("P"))))
//             ),
//             SolverResult::UNSAT
//            },
            {"V1", impl(Fatom("P"), p),SolverResult::UNSAT},
            {"E1", impl(p, Eatom("P")),SolverResult::UNSAT},
//            {"V2", impl(Fa(impl(oneHalf(),q)), impl(oneHalf(), Fatom("Q"))),SolverResult::UNSAT},
            {"E2", impl(Fa(impl(q,oneHalf())), impl(Eatom("Q"),oneHalf())),SolverResult::UNSAT},
    };

    int passed = 0;
    int failed = 0;

    for (const auto &tc: tests) {
        if (runOne(tc)) {
            passed++;
        } else {
            failed++;
        }
    }

    std::cout << "\nPassed: " << passed << "\n";
    std::cout << "Failed: " << failed << "\n";

    if (failed != 0) {
        return 1;
    }
    return 0;
}