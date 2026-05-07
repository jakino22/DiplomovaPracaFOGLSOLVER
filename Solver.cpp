#include <vector>
#include <memory>
#include <iostream>
#include "Solver.h"

bool GodelSATSolver::literalsEqualAfterRenaming(std::shared_ptr<Literal> left,
                                                std::shared_ptr<Literal> right,
                                                Substitution sigma) {
    auto leftClone = left->clone();
    auto rightClone = right->clone();

    leftClone->applySubstitution(&sigma);
    rightClone->applySubstitution(&sigma);

    if (leftClone->operation == "=" && rightClone->operation == "=") {
        if (leftClone->returnStr() == rightClone->returnStr()) {
            return true;
        }

        auto swapped = rightClone->clone();
        std::swap(swapped->e1, swapped->e2);
        return leftClone->returnStr() == swapped->returnStr();
    }

    return leftClone->returnStr() == rightClone->returnStr();
}

bool GodelSATSolver::subSumesByVariableRenaming(std::shared_ptr<Clause> who,
                                                std::shared_ptr<Clause> what) {
    Substitution sigmaOut;
    return subSumesByVariableRenaming(who, what, sigmaOut);
}

bool GodelSATSolver::subSumesByVariableRenaming(const std::shared_ptr<Clause> &who,
                                                const std::shared_ptr<Clause> &what,
                                                Substitution &sigmaOut) {

    if (who->literals.size() > what->literals.size()) {
        return false;
    }

    auto whoClone = std::make_shared<Clause>(who->clone());
    auto whatClone = std::make_shared<Clause>(what->clone());

    std::vector<bool> used(whatClone->literals.size(), false);
    Substitution sigma;

    return subSumesByVariableRenamingRec(whoClone->literals, whatClone->literals, 0, used, sigma, sigmaOut);
}

bool GodelSATSolver::subSumesByVariableRenamingRec(const std::vector<std::shared_ptr<Literal>> &whoLits,
                                                   const std::vector<std::shared_ptr<Literal>> &whatLits, int whoIndex,
                                                   std::vector<bool> &used, Substitution sigma,
                                                   Substitution &sigmaOut
) {

    if (whoIndex == whoLits.size()) {
        sigmaOut = sigma;
        return true;
    }

    auto whoLit = whoLits[whoIndex];

    for (int j = 0; j < whatLits.size(); j++) {
        if (used[j]) {
            continue;
        }

        auto whatLit = whatLits[j];

        if (whoLit->operation != whatLit->operation) {
            continue;
        }

        Substitution nSigma = sigma;
        bool unif = unifier.variable_renaming_substitution_with_operation(
                whoLit, whatLit, nSigma
        );

        if (unif) {
            auto whoInst = whoLit->clone();
            auto whatInst = whatLit->clone();
            whoInst->applySubstitution(&nSigma);
            whatInst->applySubstitution(&nSigma);

            if (literalsEqualAfterRenaming(whoLit, whatLit, nSigma)) {
                used[j] = true;

                int nwhoIndex = whoIndex + 1;
                if (subSumesByVariableRenamingRec(whoLits, whatLits, nwhoIndex, used, nSigma, sigmaOut)) {
                    return true;
                }

                used[j] = false;
            }
        }

        if (whatLit->operation == "=") {
            auto swappedWhat = whatLit->clone();
            std::swap(swappedWhat->e1, swappedWhat->e2);
            Substitution nSigma2 = sigma;
            bool unif = unifier.variable_renaming_substitution_with_operation(whoLit, swappedWhat, nSigma2);

            if (unif) {
                auto whoInst = whoLit->clone();
                auto whatInst = swappedWhat->clone();
                whoInst->applySubstitution(&nSigma2);
                whatInst->applySubstitution(&nSigma2);

                if (literalsEqualAfterRenaming(whoLit, swappedWhat, nSigma2)) {
                    used[j] = true;

                    int nwhoIndex = whoIndex + 1;
                    if (subSumesByVariableRenamingRec(whoLits, whatLits, nwhoIndex, used, nSigma2, sigmaOut)) {
                        return true;
                    }

                    used[j] = false;
                }
            }
        }
    }

    return false;
}

void GodelSATSolver::removeSubsumed(std::shared_ptr<Clause> cl) {
    std::vector<std::shared_ptr<Clause>> new_clauses;
    for (auto clause: S->clauses) {
        if (!subSumesByVariableRenaming(cl, clause)) {
            new_clauses.push_back(clause);
        }
    }
    S->clauses = std::move(new_clauses);
}

SolverResult GodelSATSolver::solve(int witnessDepthLimit) {
    for (std::shared_ptr<Clause> clause: S->clauses) {
        removeDuplicateLiterals(clause);
    }
    inferencer = Inferencer(S);

    ///no mock
    auto new_clauses = inferencer.applyRules(witnessDepthLimit);


    ///mock for example 1
//    std::vector<std::shared_ptr<Clause>> new_clauses;
//    auto Vxp3x = std::make_shared<ForAllPredicateValue>(
//            "p3",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x")},
//            std::make_shared<Variable>("x")
//    );
//    auto Exqx = std::make_shared<ExistsPredicateValue>(
//            "Q",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x")},
//            std::make_shared<Variable>("x")
//    );
//    auto Exp6x = std::make_shared<ExistsPredicateValue>(
//            "p6",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x")},
//            std::make_shared<Variable>("x")
//    );
//    auto c03 = std::make_shared<EpsylonConstant>("1/3");
//
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderVQuantificationRule(std::dynamic_pointer_cast<ForAllPredicateValue>(Vxp3x->clone()))));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderEWitnessingRule(std::dynamic_pointer_cast<ExistsPredicateValue>(Exqx->clone()),
//                                            std::dynamic_pointer_cast<EpsylonConstant>(c03->clone()))));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderEWitnessingRule(std::dynamic_pointer_cast<ExistsPredicateValue>(Exqx->clone()),
//                                            std::dynamic_pointer_cast<ExistsPredicateValue>(Exp6x->clone()))));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderEQuantificationRule(std::dynamic_pointer_cast<ExistsPredicateValue>(Exp6x->clone()))));

    ///mock for example 2
//    std::vector<std::shared_ptr<Clause>> new_clauses;
//
//    auto Expx = std::make_shared<ExistsPredicateValue>(
//            "P",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x")},
//            std::make_shared<Variable>("x")
//    );
//    auto Vxqx = std::make_shared<ForAllPredicateValue>(
//            "Q",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x")},
//            std::make_shared<Variable>("x")
//    );
//    auto Vxp5xy = std::make_shared<ForAllPredicateValue>(
//            "p5",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x"), std::make_shared<Variable>("y")},
//            std::make_shared<Variable>("x")
//    );
//    auto Vyp6xy = std::make_shared<ForAllPredicateValue>(
//            "p6",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x"), std::make_shared<Variable>("y")},
//            std::make_shared<Variable>("y")
//    );
//    auto c1 = std::make_shared<EpsylonConstant>("1");
//
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderEQuantificationRule(std::dynamic_pointer_cast<ExistsPredicateValue>(Expx->clone()))));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderVQuantificationRule(std::dynamic_pointer_cast<ForAllPredicateValue>(Vxqx->clone()))));
//
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderVWitnessingRule(std::dynamic_pointer_cast<ForAllPredicateValue>(Vyp6xy->clone()),
//                                            c1->clone())));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderVWitnessingRule(std::dynamic_pointer_cast<ForAllPredicateValue>(Vxp5xy->clone()),
//                                            c1->clone())));

    ///mock for example 3
//    std::vector<std::shared_ptr<Clause>> new_clauses;
//    auto Exp3xyz = std::make_shared<ExistsPredicateValue>(
//            "p3",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x"), std::make_shared<Variable>("y"),
//                                               std::make_shared<Variable>("z")},
//            std::make_shared<Variable>("x")
//    );
//    auto ExPxyz = std::make_shared<ExistsPredicateValue>(
//            "P",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x"), std::make_shared<Variable>("y"),
//                                               std::make_shared<Variable>("z")},
//            std::make_shared<Variable>("x")
//    );
//    auto Ezp6xyz = std::make_shared<ExistsPredicateValue>(
//            "p6",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x"), std::make_shared<Variable>("y"),
//                                               std::make_shared<Variable>("z")},
//            std::make_shared<Variable>("z")
//    );
//    auto EzPxyz = std::make_shared<ExistsPredicateValue>(
//            "P",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x"), std::make_shared<Variable>("y"),
//                                               std::make_shared<Variable>("z")},
//            std::make_shared<Variable>("z")
//    );
//    auto Vyp4xyz = std::make_shared<ForAllPredicateValue>(
//            "p4",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x"), std::make_shared<Variable>("y"),
//                                               std::make_shared<Variable>("z")},
//            std::make_shared<Variable>("y")
//    );
//    auto Vyp5xyz = std::make_shared<ForAllPredicateValue>(
//            "p5",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<Variable>("x"), std::make_shared<Variable>("y"),
//                                               std::make_shared<Variable>("z")},
//            std::make_shared<Variable>("y")
//    );
//    auto p3gama0yz = std::make_shared<PredicateValue>(
//            "p3",
//            std::vector<std::shared_ptr<Term>>{std::make_shared<FunctionSymbol>("gama0",
//                                                                                std::vector<std::shared_ptr<Term>>{
//                                                                                        std::make_shared<Variable>("y"),
//                                                                                        std::make_shared<Variable>("z"),
//                                                                                        std::make_shared<Variable>(
//                                                                                                "x"),
//                                                                                        std::make_shared<Variable>(
//                                                                                                "z")}),
//                                               std::make_shared<Variable>("y"),
//                                               std::make_shared<Variable>("z")}
//    );
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderEWitnessingRule(std::dynamic_pointer_cast<ExistsPredicateValue>(Exp3xyz->clone()),
//                                            Vyp5xyz->clone())));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderVWitnessingRule(std::dynamic_pointer_cast<ForAllPredicateValue>(Vyp5xyz->clone()),
//                                            p3gama0yz->clone())));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderVQuantificationRule(std::dynamic_pointer_cast<ForAllPredicateValue>(Vyp4xyz->clone()))));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderEWitnessingRule(std::dynamic_pointer_cast<ExistsPredicateValue>(EzPxyz->clone()),
//                                            Ezp6xyz->clone())));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderEQuantificationRule(std::dynamic_pointer_cast<ExistsPredicateValue>(Ezp6xyz->clone()))));
//    new_clauses.push_back(std::make_shared<Clause>(
//            inferencer.orderEQuantificationRule(std::dynamic_pointer_cast<ExistsPredicateValue>(ExPxyz->clone()))));

    for (auto cl: new_clauses) {
        S->clauses.push_back(cl);
    }

    S->renameVariables();
    removeImpossible();
    if (containsEmptyClause()) {
        return SolverResult::UNSAT;
    }
    foundEmpty = false;


    S->renameVariables();
    accResS = 1;
    while (true) {
        if (accResS > 10) {
            break;
        }
        if (containsEmptyClause()) {
            return SolverResult::UNSAT;
        }
        ///uzitocny pomocny vypis
//        std::cout << "acc:";
//        std::cout << accResS;
//        std::cout << "s:";
//        std::cout << S->clauses.size();
//        std::cout << std::endl;
        auto resolvents = hyperresolve();
        int countOfActuallyAdded = 0;
        for (std::shared_ptr<Clause> cl: resolvents) {
            bool isSubsumedByExistingClause = false;
            for (auto cla: S->clauses) {
                if (subSumesByVariableRenaming(cla, cl)) {
                    isSubsumedByExistingClause = true;
                }
            }
            if (isSubsumedByExistingClause) {
                continue;
            }
            removeSubsumed(cl);
            countOfActuallyAdded++;
            S->clauses.push_back(cl);
            ///inference application for new resolvents
//            auto newInf = inferencer.applyRulesOnNewResolvent(cl,witnessDepthLimit);
//            for (auto infCl: newInf) {
//                isSubsumedByExistingClause = false;
//                for (auto cla: S->clauses) {
//                    if (subSumesByVariableRenaming(cla, infCl)) {
//                        isSubsumedByExistingClause = true;
//                    }
//                }
//                if (isSubsumedByExistingClause) {
//                    continue;
//                }
//                removeSubsumed(infCl);
//                countOfActuallyAdded++;
//                S->clauses.push_back(infCl);
//            }
        }

        if (countOfActuallyAdded == 0) {
            accResS++;
        } else {
            accResS--;
            if (accResS < 1) {
                accResS = 1;
            }
        }

        S->renameVariables();
        removeImpossible();
    }

    if (containsEmptyClause()) {
        return SolverResult::UNSAT;
    }
    return SolverResult::SAT;
}


std::shared_ptr<Clause> GodelSATSolver::buildResolvent(Substitution sigma,
                                                       std::vector<std::shared_ptr<Literal>> chain,
                                                       std::map<std::shared_ptr<Literal>, std::shared_ptr<Clause>> litToClause) {
    std::shared_ptr<Clause> resolvent = std::make_shared<Clause>();
    for (int i = 0; i < chain.size(); i++) {
        auto clause = litToClause[chain[i]]->clone();
        clause.literals.erase(
                std::remove_if(clause.literals.begin(), clause.literals.end(),
                               [&](const std::shared_ptr<Literal> &x) {
                                   return x->equals(chain[i]);
                               }),
                clause.literals.end()
        );
        clause.applySubstitution(sigma);
        for (auto lit: clause.literals) {
            resolvent->literals.push_back(lit->clone());
        }
    }
    removeDuplicateLiterals(resolvent);
    if (resolvent->literals.empty()) {
        foundEmpty = true;
    }

    return resolvent;
}


std::vector<std::shared_ptr<Clause>> GodelSATSolver::hyperresolve() {
    std::vector<std::shared_ptr<Clause>> resolvents;
    std::vector<bool> usedClause;
    for (int i = 0; i < S->clauses.size(); i++) {
        usedClause.push_back(false);
    }
    std::vector<std::shared_ptr<Literal>> chain;
    std::vector<std::string> endPoints;
    Substitution sigma;
    std::map<std::shared_ptr<Literal>, std::shared_ptr<Clause>> litToClause;
    for (std::shared_ptr<Clause> cptr: S->clauses) {
        for (std::shared_ptr<Literal> lit: cptr->literals) {
            litToClause[lit] = cptr;
        }
    }
    for (int i = 0; i < S->clauses.size(); i++) {
        if (S->clauses[i]->literals.size() > accResS) {
            continue;
        }
        usedClause[i] = true;
        for (auto &lit: S->clauses[i]->literals) {
            chain.clear();
            endPoints.clear();
            Substitution sigma;
            int acc = S->clauses[i]->literals.size() - 1;
            findChain(lit, usedClause, chain, endPoints, sigma, litToClause, resolvents,
                      acc);
            if (lit->operation == "=") {
                std::swap(lit->e1, lit->e2);
                chain.clear();
                endPoints.clear();
                Substitution sigma;
                int acc = S->clauses[i]->literals.size() - 1;
                findChain(lit, usedClause, chain, endPoints, sigma, litToClause, resolvents,
                          acc);
            }
        }
        usedClause[i] = false;
    }
    return resolvents;
}

void GodelSATSolver::removeImpossible() {
    for (auto clause: S->clauses) {
        std::vector<std::shared_ptr<Literal>> newLits;
        for (auto lit: clause->literals) {
            if (lit->e2->returnStr() == "0" && lit->operation == "<") {
                continue;
            }
            if (lit->e1->returnStr() == "1" && lit->operation == "<") {
                continue;
            }
            newLits.push_back(lit);
        }
        clause->literals = std::move(newLits);
    }
}

void GodelSATSolver::removeDuplicateLiterals(
        std::shared_ptr<Clause> clause) {
    std::vector<std::shared_ptr<Literal>> literals;
    bool isDouble;
    for (std::shared_ptr<Literal> lit: clause->literals) {
        isDouble = false;
        for (std::shared_ptr<Literal> lit2: literals) {
            if (lit->equals(lit2)) {
                isDouble = true;
                break;
            }
        }
        if (isDouble) {
            continue;
        }
        literals.push_back(lit);
    }
    clause->literals = std::move(literals);
}

bool GodelSATSolver::isAnIncreasingChain(std::vector<std::shared_ptr<Literal>> &chain) {
    for (auto a: chain) {
        if (a->operation == "<") {
            return true;
        }
    }
    return false;
}

std::vector<std::shared_ptr<Literal>>
GodelSATSolver::existsZeroInChainExceptFirstPlace(std::vector<std::shared_ptr<Literal>> &chain) {
    bool wasZero = false;
    std::vector<std::shared_ptr<Literal>> res;
    for (int i = chain.size() - 1; i > -1; i--) {
        if (chain[i]->e2->returnStr() == "0") {
            wasZero = true;
            res.clear();
        }
        if (wasZero) {
            res.push_back(chain[i]);
        }
        if (chain[i]->operation == "<" && wasZero) {
            return res;
        }
    }
    return {};
}

std::vector<std::shared_ptr<Literal>>
GodelSATSolver::existsOneInChainExceptLastPlace(std::vector<std::shared_ptr<Literal>> &chain) {
    bool wasOnne = false;
    std::vector<std::shared_ptr<Literal>> res;
    for (int i = 0; i < chain.size(); i++) {
        if (chain[i]->e1->returnStr() == "1") {
            wasOnne = true;
            res.clear();
        }
        if (wasOnne) {
            res.push_back(chain[i]);
        }
        if (chain[i]->operation == "<" && wasOnne) {
            return res;
        }
    }
    return {};
}


void GodelSATSolver::findChain(std::shared_ptr<Literal> current,
                               std::vector<bool> &usedClause,
                               std::vector<std::shared_ptr<Literal>> &chain,
                               std::vector<std::string> &endPoints,
                               Substitution &sigma,
                               std::map<std::shared_ptr<Literal>, std::shared_ptr<Clause>> &litToClause,
                               std::vector<std::shared_ptr<Clause>> &foundClauses,
                               int accumulatedResolventSize) {
    if (foundEmpty) {
        return;
    }
    if (accumulatedResolventSize > accResS) {
        return;
    }

    auto instCur = current->clone();
    instCur->applySubstitution(&sigma);
    endPoints.push_back(instCur->e2->returnStr());
    chain.push_back(current);

    if (isAnIncreasingChain(chain)) {
        Substitution sub = sigma;
        auto backClone = chain.back()->clone();
        backClone->applySubstitution(&sigma);
        auto frontClone = chain.front()->clone();
        frontClone->applySubstitution(&sigma);
        if (unifier.unifyEpsilons(backClone->e2->clone(), frontClone->e1->clone(),
                                  sub)) {
            auto res = buildResolvent(sub, chain, litToClause);

            std::vector<std::shared_ptr<Clause>> newFound;
            for (auto a: foundClauses) {
                if (subSumesByVariableRenaming(a, res)) {
                    endPoints.pop_back();
                    chain.pop_back();
                    return;
                }
            }
            for (auto a: foundClauses) {
                if (!subSumesByVariableRenaming(res, a)) {
                    newFound.push_back(a);
                }
            }
            foundClauses = std::move(newFound);
            foundClauses.push_back(res);
            endPoints.pop_back();
            chain.pop_back();

            return;
        }

        auto zero = existsZeroInChainExceptFirstPlace(chain);
        if (!zero.empty()) {
            auto res = buildResolvent(sigma, zero, litToClause);

            std::vector<std::shared_ptr<Clause>> newFound;
            for (auto a: foundClauses) {
                if (subSumesByVariableRenaming(a, res)) {
                    endPoints.pop_back();
                    chain.pop_back();
                    return;
                }
            }
            for (auto a: foundClauses) {
                if (!subSumesByVariableRenaming(res, a)) {
                    newFound.push_back(a);
                }
            }
            foundClauses = std::move(newFound);
            foundClauses.push_back(res);
            endPoints.pop_back();
            chain.pop_back();
            return;
        }

        auto one = existsOneInChainExceptLastPlace(chain);
        if (!one.empty()) {
            auto res = buildResolvent(sigma, one, litToClause);

            std::vector<std::shared_ptr<Clause>> newFound;
            for (auto a: foundClauses) {
                if (subSumesByVariableRenaming(a, res)) {
                    endPoints.pop_back();
                    chain.pop_back();
                    return;
                }
            }
            for (auto a: foundClauses) {
                if (!subSumesByVariableRenaming(res, a)) {
                    newFound.push_back(a);
                }
            }
            foundClauses = std::move(newFound);
            foundClauses.push_back(res);
            endPoints.pop_back();
            chain.pop_back();
            return;
        }
    }


    for (int i = 0; i < S->clauses.size(); i++) {
        if (usedClause[i]) {
            continue;
        }
        usedClause[i] = true;
        for (const auto &lit: S->clauses[i]->literals) {

            Substitution newSigma = sigma;
            auto currClone = current->clone();
            currClone->applySubstitution(&sigma);
            if (unifier.chainable(currClone, lit, newSigma)) {
                auto instl = lit->clone();
                instl->applySubstitution(&newSigma);
                auto ccecheck = std::dynamic_pointer_cast<EpsylonConstant>(instl->e2);
                if (!ccecheck &&
                    std::find(endPoints.begin(), endPoints.end(), instl->e2->returnStr()) != endPoints.end()) {
                    continue;
                }
                int newAcc = accumulatedResolventSize + (S->clauses[i]->literals.size() - 1);
                findChain(lit, usedClause, chain, endPoints, newSigma, litToClause, foundClauses,
                          newAcc);
            }
        }
        usedClause[i] = false;
    }
    endPoints.pop_back();
    chain.pop_back();
}

bool GodelSATSolver::containsEmptyClause() {
    for (const auto &clause: S->clauses) {
        if (clause->literals.empty()) {
            return true;
        }
    }
    return false;
}