#include "Inferencer.h"

Clause
Inferencer::forceBoundary(const std::shared_ptr<PredicateValue> &a) {
    Clause clause;
    for (const auto &b: tcons) {
        clause.addLiteral(std::make_shared<Literal>(a, b, "="));
    }
    return clause.clone();
}

Clause Inferencer::orderTrichotomyRule(std::shared_ptr<PredicateValue> a, std::shared_ptr<EpsylonContent> b) {
    a = std::dynamic_pointer_cast<PredicateValue>(a->clone());
    Substitution sub;
    a->renameVariables(sub);

    b = b->clone();
    Substitution sub2;
    sub2.currentHighestIndex = sub.currentHighestIndex;
    b->renameVariables(sub2);


    auto l1 = std::make_shared<Literal>(a, b, "<");
    auto l2 = std::make_shared<Literal>(a, b, "=");
    auto l3 = std::make_shared<Literal>(b, a, "<");
    Clause clause;
    clause.addLiteral(l1);
    clause.addLiteral(l2);
    clause.addLiteral(l3);
    return clause.clone();
}

Clause Inferencer::orderEQuantificationRule(const std::shared_ptr<ExistsPredicateValue> &e) {
    auto l1 = std::make_shared<Literal>(std::make_shared<PredicateValue>(e->predicate, e->terms), e, "<");
    auto l2 = std::make_shared<Literal>(std::make_shared<PredicateValue>(e->predicate, e->terms), e, "=");
    if (existingSet.find(std::make_shared<PredicateValue>(e->predicate, e->terms)->returnStructuralKey()) ==
        existingSet.end()) {
        atoms.push_back(std::make_shared<PredicateValue>(e->predicate, e->terms));
        existingSet.insert(std::make_shared<PredicateValue>(e->predicate, e->terms)->returnStructuralKey());
    }
    Clause clause;
    clause.addLiteral(l1);
    clause.addLiteral(l2);
    return clause.clone();
}

Clause Inferencer::orderVQuantificationRule(const std::shared_ptr<ForAllPredicateValue> &fa) {
    auto l1 = std::make_shared<Literal>(fa, std::make_shared<PredicateValue>(fa->predicate, fa->terms), "<");
    auto l2 = std::make_shared<Literal>(fa, std::make_shared<PredicateValue>(fa->predicate, fa->terms), "=");
    if (existingSet.find(std::make_shared<PredicateValue>(fa->predicate, fa->terms)->returnStructuralKey()) ==
        existingSet.end()) {
        atoms.push_back(std::make_shared<PredicateValue>(fa->predicate, fa->terms));
        existingSet.insert(std::make_shared<PredicateValue>(fa->predicate, fa->terms)->returnStructuralKey());
    }
    Clause clause;
    clause.addLiteral(l1);
    clause.addLiteral(l2);
    return clause.clone();
}


Clause
Inferencer::orderVWitnessingRule(std::shared_ptr<ForAllPredicateValue> fa, std::shared_ptr<EpsylonContent> b) {
    Substitution s1;

    fa = std::dynamic_pointer_cast<ForAllPredicateValue>(fa->clone());
    fa->renameVariables(s1);
    Substitution s2;
    s2.currentHighestIndex = s1.currentHighestIndex;
    b = b->clone();
    b->renameVariables(s2);

    Substitution substitution;
    std::vector<std::shared_ptr<Term>> newTerms = fa->returnFreeVariables();
    std::vector<std::shared_ptr<Term>> newTerms2 = b->returnFreeVariables();
    newTerms.insert(newTerms.end(), newTerms2.begin(), newTerms2.end());

    auto w = std::make_shared<FunctionSymbol>(getNewWitnessFunction(), newTerms);
    auto a = std::make_shared<PredicateValue>(fa->predicate, fa->terms);
    Substitution subst;
    subst.bind(fa->boundVar->name, w);
    a->applySubstitution(&subst);
    newWitnesses.push_back(std::dynamic_pointer_cast<PredicateValue>(a->clone()));


    auto l1 = std::make_shared<Literal>(a, b, "<");
    auto l2 = std::make_shared<Literal>(b, fa, "=");
    auto l3 = std::make_shared<Literal>(b, fa, "<");
    Clause clause;
    clause.addLiteral(l1);
    clause.addLiteral(l2);
    clause.addLiteral(l3);
    return clause.clone();
}

Clause
Inferencer::orderEWitnessingRule(std::shared_ptr<ExistsPredicateValue> e, std::shared_ptr<EpsylonContent> b) {
    Substitution s1;
    e = std::dynamic_pointer_cast<ExistsPredicateValue>(e->clone());
    e->renameVariables(s1);
    Substitution s2;
    s2.currentHighestIndex = s1.currentHighestIndex;
    b = b->clone();
    b->renameVariables(s2);

    Substitution substitution;
    std::vector<std::shared_ptr<Term>> newTerms = e->returnFreeVariables();
    std::vector<std::shared_ptr<Term>> newTerms2 = b->returnFreeVariables();
    newTerms.insert(newTerms.end(), newTerms2.begin(), newTerms2.end());

    auto w = std::make_shared<FunctionSymbol>(getNewWitnessFunction(), newTerms);
    auto a = std::make_shared<PredicateValue>(e->predicate, e->terms);
    Substitution subst;
    subst.bind(e->boundVar->name, w);
    a->applySubstitution(&subst);
    newWitnesses.push_back(std::dynamic_pointer_cast<PredicateValue>(a->clone()));

    auto l1 = std::make_shared<Literal>(b, a, "<");
    auto l2 = std::make_shared<Literal>(b, e, "=");
    auto l3 = std::make_shared<Literal>(e, b, "<");
    Clause clause;
    clause.addLiteral(l1);
    clause.addLiteral(l2);
    clause.addLiteral(l3);
    return clause.clone();
}

std::vector<std::shared_ptr<PredicateValue>> Inferencer::getAtoms(const std::shared_ptr<CNF> &Theory) {
    std::vector<std::shared_ptr<PredicateValue>> atoms;
    std::vector<std::string> atomsVisited;
    for (auto &clause: Theory->clauses) {
        for (auto &literal: clause->literals) {
            if (auto atomA = std::dynamic_pointer_cast<PredicateValue>(literal->e1)) {
                if (std::find(atomsVisited.begin(), atomsVisited.end(), atomA->returnStructuralKey()) ==
                    atomsVisited.end()) {
                    atoms.push_back(atomA);
                    atomsVisited.push_back(atomA->returnStructuralKey());
                }
            }
            if (auto atomB = std::dynamic_pointer_cast<PredicateValue>(literal->e2)) {
                if (std::find(atomsVisited.begin(), atomsVisited.end(), atomB->returnStructuralKey()) ==
                    atomsVisited.end()) {
                    atoms.push_back(atomB);
                    atomsVisited.push_back(atomB->returnStructuralKey());
                }
            }
        }
    }
    for (auto atom: atoms) {
        existingSet.insert(atom->returnStructuralKey());
    }
    return atoms;
}

std::vector<std::shared_ptr<ExistsPredicateValue>> Inferencer::getExistsQAtoms(const std::shared_ptr<CNF> &Theory) {
    std::vector<std::shared_ptr<ExistsPredicateValue>> eQAtoms;
    std::vector<std::string> eatomsVisited;
    for (auto &clause: Theory->clauses) {
        for (auto &literal: clause->literals) {
            if (auto eQAtomA = std::dynamic_pointer_cast<ExistsPredicateValue>(literal->e1)) {
                if (std::find(eatomsVisited.begin(), eatomsVisited.end(), eQAtomA->returnStructuralKey()) ==
                    eatomsVisited.end()) {
                    eQAtoms.push_back(eQAtomA);
                    eatomsVisited.push_back(eQAtomA->returnStructuralKey());
                }
            }
            if (auto eQAtomB = std::dynamic_pointer_cast<ExistsPredicateValue>(literal->e2)) {
                if (std::find(eatomsVisited.begin(), eatomsVisited.end(), eQAtomB->returnStructuralKey()) ==
                    eatomsVisited.end()) {
                    eQAtoms.push_back(eQAtomB);
                    eatomsVisited.push_back(eQAtomB->returnStructuralKey());
                }

            }
        }
    }
    for (auto eQatom: eQAtoms) {
        existingSet.insert(eQatom->returnStructuralKey());
    }
    return eQAtoms;
}

std::vector<std::shared_ptr<ForAllPredicateValue>> Inferencer::getForAllQAtoms(const std::shared_ptr<CNF> &Theory) {
    std::vector<std::shared_ptr<ForAllPredicateValue>> faQAtoms;
    std::vector<std::string> fatomsVisited;
    for (auto &clause: Theory->clauses) {
        for (auto &literal: clause->literals) {
            if (auto faQAtomA = std::dynamic_pointer_cast<ForAllPredicateValue>(literal->e1)) {
                if (std::find(fatomsVisited.begin(), fatomsVisited.end(), faQAtomA->returnStructuralKey()) ==
                    fatomsVisited.end()) {
                    faQAtoms.push_back(faQAtomA);
                    fatomsVisited.push_back(faQAtomA->returnStructuralKey());
                }
            }
            if (auto faQAtomB = std::dynamic_pointer_cast<ForAllPredicateValue>(literal->e2)) {
                if (std::find(fatomsVisited.begin(), fatomsVisited.end(), faQAtomB->returnStructuralKey()) ==
                    fatomsVisited.end()) {
                    faQAtoms.push_back(faQAtomB);
                    fatomsVisited.push_back(faQAtomB->returnStructuralKey());
                }
            }
        }
    }
    for (auto faQAtom: faQAtoms) {
        existingSet.insert(faQAtom->returnStructuralKey());
    }
    return faQAtoms;
}

std::vector<std::shared_ptr<EpsylonConstant>> Inferencer::getTcons(const std::shared_ptr<CNF> &Theory) {
    std::vector<std::shared_ptr<EpsylonConstant>> tCons;
    std::vector<std::string> tconsVisited;
    for (auto &clause: Theory->clauses) {
        for (auto &literal: clause->literals) {
            if (auto tConA = std::dynamic_pointer_cast<EpsylonConstant>(literal->e1)) {
                if (std::find(tconsVisited.begin(), tconsVisited.end(), tConA->returnStructuralKey()) ==
                    tconsVisited.end()) {
                    tCons.push_back(tConA);
                    tconsVisited.push_back(tConA->returnStructuralKey());
                }
            }
            if (auto tConB = std::dynamic_pointer_cast<EpsylonConstant>(literal->e2)) {
                if (std::find(tconsVisited.begin(), tconsVisited.end(), tConB->returnStructuralKey()) ==
                    tconsVisited.end()) {
                    tCons.push_back(tConB);
                    tconsVisited.push_back(tConB->returnStructuralKey());
                }
            }
        }
    }
    for (auto tcon: tcons) {
        existingSet.insert(tcon->returnStructuralKey());
    }
    return tCons;
}

std::vector<std::shared_ptr<Clause>>
Inferencer::applyWitnessRulesOnNewWitnesses(const std::vector<std::shared_ptr<PredicateValue>> &witnesses,
                                            int witnessDepthLimit) {
    std::vector<std::shared_ptr<Clause>> results;
    for (auto a: faQAtoms) {
        if (a->returnWitnessFunctionDepth() >= witnessDepthLimit) {
            continue;
        }
        for (auto b: witnesses) {
            if (b->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                continue;
            }
            results.push_back(std::make_shared<Clause>(orderVWitnessingRule(a, b)));
        }
    }

    for (auto a: eQAtoms) {
        if (a->returnWitnessFunctionDepth() >= witnessDepthLimit) {
            continue;
        }
        for (auto b: witnesses) {
            if (b->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                continue;
            }
            results.push_back(std::make_shared<Clause>(orderEWitnessingRule(a, b)));
        }
    }

    return results;
}

std::vector<std::shared_ptr<Clause>>
Inferencer::forceBoundaryOnNewWitnesses(const std::vector<std::shared_ptr<PredicateValue>> &witnesses) {
    std::vector<std::shared_ptr<Clause>> results;
    for (auto atom: witnesses) {
        results.push_back(std::make_shared<Clause>(forceBoundary(atom)));
    }
    return results;
}

std::vector<std::shared_ptr<Clause>>
Inferencer::applyRulesOnNewResolvent(std::shared_ptr<Clause> clause, int witnessDepthLimit) {
    std::vector<std::shared_ptr<Clause>> output;
    std::set<std::shared_ptr<EpsylonContent>> newEps;
    for (auto literal: clause->literals) {
        if (existingSet.find(literal->e1->returnStructuralKey()) == existingSet.end()) {
            existingSet.insert(literal->e1->returnStructuralKey());
            newEps.insert(literal->e1->clone());
        }
        if (existingSet.find(literal->e2->returnStructuralKey()) == existingSet.end()) {
            existingSet.insert(literal->e2->returnStructuralKey());
            newEps.insert(literal->e2->clone());
        }
    }

    if (newEps.empty()) {
        return output;
    }

    ///insert new atoms/qatoms
    ///no need to deal with a case for ep being a constant since hyperresolution currently does not resolve new constants
    for (auto ep: newEps) {
        if (auto qatom = std::dynamic_pointer_cast<ForAllPredicateValue>(ep->clone())) {
            faQAtoms.push_back(qatom);
        }
        if (auto qatom = std::dynamic_pointer_cast<ExistsPredicateValue>(ep->clone())) {
            eQAtoms.push_back(qatom);
        }
        if (auto atom = std::dynamic_pointer_cast<PredicateValue>(ep->clone())) {
            atoms.push_back(atom);
        }
    }

    ///order quant rules
    for (auto ep: newEps) {
        if (auto qatom = std::dynamic_pointer_cast<ForAllPredicateValue>(ep)) {
            output.push_back(std::make_shared<Clause>(orderVQuantificationRule(qatom)));
        }
        if (auto qatom = std::dynamic_pointer_cast<ExistsPredicateValue>(ep)) {
            output.push_back(std::make_shared<Clause>(orderEQuantificationRule(qatom)));
        }
    }

    ///witnessing rules on new atoms
    for (auto ep: newEps) {
        if (auto qatom = std::dynamic_pointer_cast<ForAllPredicateValue>(ep->clone())) {
            if (qatom->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                continue;
            }
            for (auto a: faQAtoms) {
                if (a->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderVWitnessingRule(a, qatom)));
            }
            for (auto a: eQAtoms) {
                if (a->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderEWitnessingRule(a, qatom)));
            }
        }
        if (auto qatom = std::dynamic_pointer_cast<ExistsPredicateValue>(ep->clone())) {
            if (qatom->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                continue;
            }
            for (auto a: faQAtoms) {
                if (a->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderVWitnessingRule(a, qatom)));
            }
            for (auto a: eQAtoms) {
                if (a->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderEWitnessingRule(a, qatom)));
            }
        }
        if (auto atom = std::dynamic_pointer_cast<PredicateValue>(ep->clone())) {
            if (atom->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                continue;
            }
            for (auto a: faQAtoms) {
                if (a->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderVWitnessingRule(a, atom)));
            }
            for (auto a: eQAtoms) {
                if (a->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderEWitnessingRule(a, atom)));
            }
        }
    }

    ///witnessing rules for new atoms
    for (auto ep: newEps) {
        if (auto qatom = std::dynamic_pointer_cast<ForAllPredicateValue>(ep)) {
            if (qatom->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                continue;
            }
            for (auto b: atoms) {
                if (b->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                if (std::make_shared<PredicateValue>(qatom->predicate, qatom->terms)->returnStructuralKey() ==
                    b->returnStructuralKey()) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderVWitnessingRule(qatom, b)));
            }
            for (auto b: tcons) {
                output.push_back(std::make_shared<Clause>(orderVWitnessingRule(qatom, b)));
            }
            for (auto b: faQAtoms) {
                if (b->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                if (qatom->returnStructuralKey() == b->returnStructuralKey()) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderVWitnessingRule(qatom, b)));
            }
            for (auto b: eQAtoms) {
                if (b->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderVWitnessingRule(qatom, b)));
            }
        }
        if (auto qatom = std::dynamic_pointer_cast<ExistsPredicateValue>(ep)) {
            if (qatom->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                continue;
            }
            for (auto b: atoms) {
                if (b->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                if (std::make_shared<PredicateValue>(qatom->predicate, qatom->terms)->returnStructuralKey() ==
                    b->returnStructuralKey()) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderEWitnessingRule(qatom, b)));
            }
            for (auto b: tcons) {
                output.push_back(std::make_shared<Clause>(orderEWitnessingRule(qatom, b)));
            }
            for (auto b: faQAtoms) {
                if (b->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderEWitnessingRule(qatom, b)));
            }
            for (auto b: eQAtoms) {
                if (b->returnWitnessFunctionDepth() >= witnessDepthLimit) {
                    continue;
                }
                if (qatom->returnStructuralKey() == b->returnStructuralKey()) {
                    continue;
                }
                output.push_back(std::make_shared<Clause>(orderEWitnessingRule(qatom, b)));
            }
        }
    }

    ///trich rules and force boundary
//    for (auto ep: newEps) {
//        if (auto atom = std::dynamic_pointer_cast<PredicateValue>(ep)) {
//            for (auto con: tcons) {
//                if (con->constant == "1" || con->constant == "0") {
//                    continue;
//                }
//                output.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom, con)));
//            }
//            for (auto atom2: atoms) {
//                if (atom->returnStructuralKey() == atom2->returnStructuralKey()) {
//                    continue;
//                }
//                output.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom, atom2)));
//            }
//            for (auto faQatom: faQAtoms) {
//                output.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom, faQatom)));
//            }
//            for (auto eQatom: eQAtoms) {
//                output.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom, eQatom)));
//            }
    ///boundary
//            output.push_back(std::make_shared<Clause>(forceBoundary(atom)));
//        }
//    }

    int i = 0;
    while (true) {
        auto wit = std::move(newWitnesses);
        newWitnesses.clear();

        i++;
        if (i < witnessDepthLimit) {
            atoms.insert(atoms.end(), wit.begin(), wit.end());
            ///witness
            auto res = applyWitnessRulesOnNewWitnesses(wit, witnessDepthLimit);
            output.insert(output.end(), res.begin(), res.end());
            ///trichotomy
            auto res2 = applyTrichRulesOnNewWitnesses(wit);
            output.insert(output.end(), res2.begin(), res2.end());
            ///boundary
            auto res3 = forceBoundaryOnNewWitnesses(wit);
            output.insert(output.end(), res3.begin(), res3.end());
            continue;
        }
        break;
    }

    return output;
}


std::vector<std::shared_ptr<Clause>>
Inferencer::applyTrichRulesOnNewWitnesses(const std::vector<std::shared_ptr<PredicateValue>> &witnesses) {
    std::vector<std::shared_ptr<Clause>> results;

    for (auto atom: witnesses) {
        for (auto con: tcons) {
            if (con->constant == "1" || con->constant == "0") {
                continue;
            }
            results.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom, con)));
        }
        for (auto atom2: atoms) {
            if (atom->returnStructuralKey() == atom2->returnStructuralKey()) {
                continue;
            }
            results.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom, atom2)));
        }
        for (auto faQatom: faQAtoms) {
            results.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom, faQatom)));
        }
        for (auto eQatom: eQAtoms) {
            results.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom, eQatom)));
        }
    }
    return results;
}

std::vector<std::shared_ptr<Clause>> Inferencer::applyRules(int witnessDepthLimit) {
    std::vector<std::shared_ptr<Clause>> results;

    /// order quantification rules
    for (auto a: faQAtoms) {
        results.push_back(std::make_shared<Clause>(orderVQuantificationRule(a)));
    }

    for (auto a: eQAtoms) {
        results.push_back(std::make_shared<Clause>(orderEQuantificationRule(a)));
    }

    /// order witnessing rules
    for (auto a: faQAtoms) {
        for (auto b: atoms) {
            if (std::make_shared<PredicateValue>(a->predicate, a->terms)->returnStructuralKey() ==
                b->returnStructuralKey()) {
                continue;
            }
            results.push_back(std::make_shared<Clause>(orderVWitnessingRule(a, b)));
        }
        for (auto b: tcons) {
            results.push_back(std::make_shared<Clause>(orderVWitnessingRule(a, b)));
        }
        for (auto b: faQAtoms) {
            if (a->returnStructuralKey() == b->returnStructuralKey()) {
                continue;
            }
            results.push_back(std::make_shared<Clause>(orderVWitnessingRule(a, b)));
        }
        for (auto b: eQAtoms) {
            results.push_back(std::make_shared<Clause>(orderVWitnessingRule(a, b)));
        }
    }

    for (auto a: eQAtoms) {
        for (auto b: atoms) {
            if (std::make_shared<PredicateValue>(a->predicate, a->terms)->returnStructuralKey() ==
                b->returnStructuralKey()) {
                continue;
            }
            results.push_back(std::make_shared<Clause>(orderEWitnessingRule(a, b)));
        }
        for (auto b: tcons) {
            results.push_back(std::make_shared<Clause>(orderEWitnessingRule(a, b)));
        }
        for (auto b: faQAtoms) {
            results.push_back(std::make_shared<Clause>(orderEWitnessingRule(a, b)));
        }
        for (auto b: eQAtoms) {
            if (a->returnStructuralKey() == b->returnStructuralKey()) {
                continue;
            }
            results.push_back(std::make_shared<Clause>(orderEWitnessingRule(a, b)));
        }
    }

    /// order trichotomy rules
//    for(auto atom:atoms){
//        for(auto con: tcons){
//            if(con->constant == "1" || con->constant == "0"){
//                continue;
//            }
//            results.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom,con)));
//        }
//        for(auto atom2: atoms){
//            if(atom->returnStructuralKey() == atom2->returnStructuralKey()){
//                continue;
//            }
//            results.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom,atom2)));
//        }
//        for(auto faQatom: faQAtoms){
//            results.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom,faQatom)));
//        }
//        for(auto eQatom: eQAtoms){
//            results.push_back(std::make_shared<Clause>(orderTrichotomyRule(atom,eQatom)));
//        }
//    }

    /// by forcing a boundary we can effectively reduce fogl tu an n-valued logic (by forcing that every predicate takes one of the truth values existing in clausal theory
    ///force boundary
//    for (auto atom: atoms) {
//        results.push_back(std::make_shared<Clause>(forceBoundary(atom)));
//    }

    int i = 0;
    while (true) {
        auto wit = std::move(newWitnesses);
        newWitnesses.clear();
        ///boundary
//        auto res3 = forceBoundaryOnNewWitnesses(wit);
//        results.insert(results.end(), res3.begin(), res3.end());
        i++;
        if (i < witnessDepthLimit) {
            for (const auto& literal: wit) {
                atoms.push_back(literal);
                existingSet.insert(literal->returnStructuralKey());
            }
            ///witness
            auto res = applyWitnessRulesOnNewWitnesses(wit, witnessDepthLimit);
            results.insert(results.end(), res.begin(), res.end());
            ///trichotomy
            auto res2 = applyTrichRulesOnNewWitnesses(wit);
            results.insert(results.end(), res2.begin(), res2.end());
            continue;
        }
        break;
    }

    return results;
}