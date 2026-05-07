#pragma once

#include "CNF.h"
#include "Unifier.h"
#include "Inferencer.h"
#include <vector>
#include <string>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <memory>
#include <utility>
#include <iostream>

enum class SolverResult {
    SAT, UNSAT
};

class GodelSATSolver {
public:
    std::shared_ptr<CNF> S;
    Unifier unifier;
    Inferencer inferencer;
    int accResS = 100;
    bool foundEmpty;

    GodelSATSolver(std::shared_ptr<CNF> initialTheory, Inferencer inferencer) : inferencer(inferencer) {
        S = initialTheory;
    }

    SolverResult solve(int witnessDepthLimit);

    std::vector<std::shared_ptr<Clause>> hyperresolve();

    bool containsEmptyClause();

    void removeDuplicateLiterals(std::shared_ptr<Clause> clause);


    std::shared_ptr<Clause> buildResolvent(Substitution sigma, std::vector<std::shared_ptr<Literal>> chain,
                                           std::map<std::shared_ptr<Literal>, std::shared_ptr<Clause>> litToClause);


    bool isAnIncreasingChain(std::vector<std::shared_ptr<Literal>> &chain);

    std::vector<std::shared_ptr<Literal>>
    existsZeroInChainExceptFirstPlace(std::vector<std::shared_ptr<Literal>> &chain);

    std::vector<std::shared_ptr<Literal>> existsOneInChainExceptLastPlace(std::vector<std::shared_ptr<Literal>> &chain);

    void
    findChain(std::shared_ptr<Literal> current, std::vector<bool> &usedClause,
              std::vector<std::shared_ptr<Literal>> &chain,
              std::vector<std::string> &endPoints, Substitution &sigma,
              std::map<std::shared_ptr<Literal>, std::shared_ptr<Clause>> &litToClause,
              std::vector<std::shared_ptr<Clause>> &foundClauses, int accumulatedResolventSize);


    void removeSubsumed(std::shared_ptr<Clause> cl);

    void removeImpossible();

    bool literalsEqualAfterRenaming(std::shared_ptr<Literal> left, std::shared_ptr<Literal> right, Substitution sigma);

    bool subSumesByVariableRenaming(std::shared_ptr<Clause> who, std::shared_ptr<Clause> what);

    bool subSumesByVariableRenaming(const std::shared_ptr<Clause>& who, const std::shared_ptr<Clause>& what, Substitution &sigmaOut);

    bool subSumesByVariableRenamingRec(const std::vector<std::shared_ptr<Literal>> &whoLits,
                                       const std::vector<std::shared_ptr<Literal>> &whatLits, int whoIndex,
                                       std::vector<bool> &usedWhat, Substitution sigma, Substitution &sigmaOut);

    void removeTautologies();
};
