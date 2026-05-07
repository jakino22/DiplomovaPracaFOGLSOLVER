#include "translator.h"

CNF Translator::translate(const std::shared_ptr<Theory> &theory) {
    index = 0;
    CNF output;
    for (const std::shared_ptr<Formula> &formula: theory->formulae) {
        std::vector<std::shared_ptr<Term>> variableVector = formula->returnAllVariables();
        std::set<std::string> seen;
        variableVector.erase(std::remove_if(variableVector.begin(), variableVector.end(),
                                            [&](const auto &t) {
                                                return !seen.insert(
                                                        std::dynamic_pointer_cast<Variable>(t)->name).second;
                                            }),
                             variableVector.end());

        std::shared_ptr<PredicateValue> predicateValue = std::make_shared<PredicateValue>("p" + std::to_string(index),
                                                                                          variableVector);
        index++;
        auto oneVal = std::make_shared<EpsylonConstant>("1");
        auto rootClause = std::make_shared<Clause>();
        rootClause->addLiteral(std::make_shared<Literal>(predicateValue->clone(), oneVal, "="));
        output.clauses.push_back(rootClause);

        auto oneVala = std::make_shared<EpsylonConstant>("1");
        auto zeroVal = std::make_shared<EpsylonConstant>("0");
        auto orderClause = std::make_shared<Clause>();
        orderClause->addLiteral(std::make_shared<Literal>(zeroVal, oneVala, "<"));

/// Uncomment based on used truth constants. For each constant there needs to be an ordering with respect to other truth constants.
///  If you choose to add other truth constants please add new corresponding clauses


        auto oneValaa = std::make_shared<EpsylonConstant>("1");
        auto onehalf = std::make_shared<EpsylonConstant>("0.5");
        auto orderClause1 = std::make_shared<Clause>();
        orderClause1->addLiteral(std::make_shared<Literal>(onehalf, oneVala, "<"));

//        auto oneValaaa = std::make_shared<EpsylonConstant>("1");
//        auto onethird = std::make_shared<EpsylonConstant>("0.3");
//        auto orderClause2 = std::make_shared<Clause>();
//        orderClause2->addLiteral(std::make_shared<Literal>(onethird, oneVala, "<"));
//
//        auto onethirdd = std::make_shared<EpsylonConstant>("0.3");
//        auto onehalf1 = std::make_shared<EpsylonConstant>("0.5");
//        auto orderClause3 = std::make_shared<Clause>();
//        orderClause3->addLiteral(std::make_shared<Literal>(onethirdd, onehalf1, "<"));
//
        auto zeroo = std::make_shared<EpsylonConstant>("0");
        auto onehalf2 = std::make_shared<EpsylonConstant>("0.5");
        auto orderClause4 = std::make_shared<Clause>();
        orderClause4->addLiteral(std::make_shared<Literal>(zeroo, onehalf2, "<"));

//        auto onethirddd = std::make_shared<EpsylonConstant>("0.3");
//        auto zerou = std::make_shared<EpsylonConstant>("0");
//        auto orderClause5 = std::make_shared<Clause>();
//        orderClause5->addLiteral(std::make_shared<Literal>(zerou, onethirddd, "<"));


/// Do not forget to add them to output theory

        output.clauses.push_back(orderClause);
        output.clauses.push_back(orderClause1);
//        output.clauses.push_back(orderClause2);
//        output.clauses.push_back(orderClause3);
        output.clauses.push_back(orderClause4);
//        output.clauses.push_back(orderClause5);

        auto recursion = ApplyRule(predicateValue, formula, variableVector);
        output.clauses.insert(output.clauses.end(), recursion.clauses.begin(), recursion.clauses.end());

        index++;
    }
    return output;
}

CNF Translator::ConjunctionRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<Conjunction> &c,
                                const std::vector<std::shared_ptr<Term>> &variableVector) {

    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula2)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }
    std::shared_ptr<EpsylonContent> newPredicate2;
    bool atomSf2 = false;
    if (isAtom(c->subformula2)) {
        atomSf2 = true;
        if (isPredicateAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->terms);
        } else if (isConstantAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula2)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate2 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "<"));
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "="));
    nliterals1.push_back(std::make_shared<Literal>(p, newPredicate2, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    nliterals2.push_back(std::make_shared<Literal>(newPredicate2, newPredicate1, "<"));
    nliterals2.push_back(std::make_shared<Literal>(p, newPredicate1, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    if (!atomSf2) {
        CNF secondRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate2), c->subformula2,
                                        variableVector);
        output.clauses.insert(output.clauses.end(), secondRecursion.clauses.begin(), secondRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

CNF Translator::DisjunctionRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<Disjunction> &c,
                                const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }
    std::shared_ptr<EpsylonContent> newPredicate2;
    bool atomSf2 = false;
    if (isAtom(c->subformula2)) {
        atomSf2 = true;
        if (isPredicateAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->terms);
        } else if (isConstantAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula2)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate2 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "<"));
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "="));
    nliterals1.push_back(std::make_shared<Literal>(p, newPredicate1, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    nliterals2.push_back(std::make_shared<Literal>(newPredicate2, newPredicate1, "<"));
    nliterals2.push_back(std::make_shared<Literal>(p, newPredicate2, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    if (!atomSf2) {
        CNF secondRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate2), c->subformula2,
                                        variableVector);
        output.clauses.insert(output.clauses.end(), secondRecursion.clauses.begin(), secondRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

CNF Translator::ImplicationRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<Implication> &c,
                                const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }
    std::shared_ptr<EpsylonContent> newPredicate2;
    bool atomSf2 = false;
    if (isAtom(c->subformula2)) {
        atomSf2 = true;
        if (isPredicateAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->terms);
        } else if (isConstantAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula2)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate2 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "<"));
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "="));
    nliterals1.push_back(std::make_shared<Literal>(p, newPredicate2, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    auto e = std::make_shared<EpsylonConstant>("1");
    nliterals2.push_back(std::make_shared<Literal>(newPredicate2, newPredicate1, "<"));
    nliterals2.push_back(std::make_shared<Literal>(p, e, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    if (!atomSf2) {
        CNF secondRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate2), c->subformula2,
                                        variableVector);
        output.clauses.insert(output.clauses.end(), secondRecursion.clauses.begin(), secondRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

CNF Translator::EquivalenceRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<Equivalence> &c,
                                const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }
    std::shared_ptr<EpsylonContent> newPredicate2;
    bool atomSf2 = false;
    if (isAtom(c->subformula2)) {
        atomSf2 = true;
        if (isPredicateAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->terms);
        } else if (isConstantAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula2)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate2 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "<"));
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "="));
    nliterals1.push_back(std::make_shared<Literal>(p, newPredicate2, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    nliterals2.push_back(std::make_shared<Literal>(newPredicate2, newPredicate1, "<"));
    nliterals2.push_back(std::make_shared<Literal>(newPredicate2, newPredicate1, "="));
    nliterals2.push_back(std::make_shared<Literal>(p, newPredicate1, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    std::vector<std::shared_ptr<Literal>> nliterals3;
    auto e = std::make_shared<EpsylonConstant>("1");
    nliterals3.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "<"));
    nliterals3.push_back(std::make_shared<Literal>(newPredicate2, newPredicate1, "<"));
    nliterals3.push_back(std::make_shared<Literal>(p, e, "="));
    auto outputClause3 = std::make_shared<Clause>(nliterals3);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    if (!atomSf2) {
        CNF secondRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate2), c->subformula2,
                                        variableVector);
        output.clauses.insert(output.clauses.end(), secondRecursion.clauses.begin(), secondRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause3->clone()));

    return output;
}

CNF Translator::EkvEquivalenceRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<EkvEquivalence> &c,
                                   const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }
    std::shared_ptr<EpsylonContent> newPredicate2;
    bool atomSf2 = false;
    if (isAtom(c->subformula2)) {
        atomSf2 = true;
        if (isPredicateAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->terms);
        } else if (isConstantAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula2)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate2 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    auto e = std::make_shared<EpsylonConstant>("0");
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "="));
    nliterals1.push_back(std::make_shared<Literal>(p, e, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    auto e2 = std::make_shared<EpsylonConstant>("1");
    nliterals2.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "<"));
    nliterals2.push_back(std::make_shared<Literal>(newPredicate2, newPredicate1, "<"));
    nliterals2.push_back(std::make_shared<Literal>(p, e2, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    if (!atomSf2) {
        CNF secondRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate2), c->subformula2,
                                        variableVector);
        output.clauses.insert(output.clauses.end(), secondRecursion.clauses.begin(), secondRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

CNF Translator::StrictOrderRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<StrictOrder> &c,
                                const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }
    std::shared_ptr<EpsylonContent> newPredicate2;
    bool atomSf2 = false;
    if (isAtom(c->subformula2)) {
        atomSf2 = true;
        if (isPredicateAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->terms);
        } else if (isConstantAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula2)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate2 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    auto e = std::make_shared<EpsylonConstant>("0");
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, newPredicate2, "<"));
    nliterals1.push_back(std::make_shared<Literal>(p, e, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    auto e2 = std::make_shared<EpsylonConstant>("1");
    nliterals2.push_back(std::make_shared<Literal>(newPredicate2, newPredicate1, "<"));
    nliterals2.push_back(std::make_shared<Literal>(newPredicate2, newPredicate1, "="));
    nliterals2.push_back(std::make_shared<Literal>(p, e2, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    if (!atomSf2) {
        CNF secondRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate2), c->subformula2,
                                        variableVector);
        output.clauses.insert(output.clauses.end(), secondRecursion.clauses.begin(), secondRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

CNF Translator::ForAllRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<ForAll> &c,
                           const std::vector<std::shared_ptr<Term>> &variableVector) {

    std::shared_ptr<EpsylonContent> newPredicateNotQuantified;
    std::shared_ptr<EpsylonContent> newPredicate;
    bool atomSf1 = false;
    if (isPredicateAtom(c->subformula)) {
        atomSf1 = true;
        newPredicateNotQuantified = std::make_shared<PredicateValue>(
                std::dynamic_pointer_cast<PredicateAtom>(c->subformula)->predicate->symbol,
                std::dynamic_pointer_cast<PredicateAtom>(c->subformula)->predicate->terms);
        newPredicate = std::make_shared<ForAllPredicateValue>(
                std::dynamic_pointer_cast<PredicateAtom>(c->subformula)->predicate->symbol,
                std::dynamic_pointer_cast<PredicateAtom>(c->subformula)->predicate->terms,
                std::dynamic_pointer_cast<ForAll>(c)->boundVariable);
    } else {
        newPredicate = std::make_shared<ForAllPredicateValue>("p" + std::to_string(index), variableVector,
                                                              c->boundVariable);
        newPredicateNotQuantified = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals;
    nliterals.push_back(std::make_shared<Literal>(p, newPredicate, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicateNotQuantified),
                                       c->subformula,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }
    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));

    return output;
}

CNF Translator::ExistsRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<Exists> &c,
                           const std::vector<std::shared_ptr<Term>> &variableVector) {

    std::shared_ptr<EpsylonContent> newPredicateNotQuantified;
    std::shared_ptr<EpsylonContent> newPredicate;
    bool atomSf1 = false;
    if (isPredicateAtom(c->subformula)) {
        atomSf1 = true;
        newPredicateNotQuantified = std::make_shared<PredicateValue>(
                std::dynamic_pointer_cast<PredicateAtom>(c->subformula)->predicate->symbol,
                std::dynamic_pointer_cast<PredicateAtom>(c->subformula)->predicate->terms);
        newPredicate = std::make_shared<ExistsPredicateValue>(
                std::dynamic_pointer_cast<PredicateAtom>(c->subformula)->predicate->symbol,
                std::dynamic_pointer_cast<PredicateAtom>(c->subformula)->predicate->terms,
                std::dynamic_pointer_cast<Exists>(c)->boundVariable);
    } else {
        newPredicate = std::make_shared<ExistsPredicateValue>("p" + std::to_string(index), variableVector,
                                                              c->boundVariable);
        newPredicateNotQuantified = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }


    std::vector<std::shared_ptr<Literal>> nliterals;
    nliterals.push_back(std::make_shared<Literal>(p, newPredicate, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicateNotQuantified),
                                       c->subformula,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }
    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));

    return output;
}

CNF Translator::ImplicationZeroRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<Implication> &c,
                                    const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    auto e = std::make_shared<EpsylonConstant>("0");
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, e, "="));
    nliterals1.push_back(std::make_shared<Literal>(p, e, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    auto e2 = std::make_shared<EpsylonConstant>("1");
    nliterals2.push_back(std::make_shared<Literal>(e, newPredicate1, "<"));
    nliterals2.push_back(std::make_shared<Literal>(p, e2, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

CNF
Translator::EkvEquivalenceZeroRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<EkvEquivalence> &c,
                                   const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    auto e = std::make_shared<EpsylonConstant>("0");
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, e, "="));
    nliterals1.push_back(std::make_shared<Literal>(p, e, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    auto e2 = std::make_shared<EpsylonConstant>("1");
    nliterals2.push_back(std::make_shared<Literal>(e, newPredicate1, "<"));
    nliterals2.push_back(std::make_shared<Literal>(p, e2, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

CNF
Translator::EkvEquivalenceOneRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<EkvEquivalence> &c,
                                  const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    auto e = std::make_shared<EpsylonConstant>("0");
    auto e2 = std::make_shared<EpsylonConstant>("1");
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, e2, "="));
    nliterals1.push_back(std::make_shared<Literal>(p, e, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    nliterals2.push_back(std::make_shared<Literal>(newPredicate1, e2, "<"));
    nliterals2.push_back(std::make_shared<Literal>(p, e2, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

CNF Translator::StrictOrderZeroRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<StrictOrder> &c,
                                    const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate2;
    bool atomSf2 = false;
    if (isAtom(c->subformula2)) {
        atomSf2 = true;
        if (isPredicateAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula2)->predicate->terms);
        } else if (isConstantAtom(c->subformula2)) {
            newPredicate2 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula2)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate2 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    auto e = std::make_shared<EpsylonConstant>("0");
    auto e2 = std::make_shared<EpsylonConstant>("1");
    nliterals1.push_back(std::make_shared<Literal>(e, newPredicate2, "<"));
    nliterals1.push_back(std::make_shared<Literal>(p, e, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    nliterals2.push_back(std::make_shared<Literal>(newPredicate2, e, "="));
    nliterals2.push_back(std::make_shared<Literal>(p, e2, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf2) {
        CNF secondRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate2), c->subformula2,
                                        variableVector);
        output.clauses.insert(output.clauses.end(), secondRecursion.clauses.begin(), secondRecursion.clauses.end());
    }
    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

CNF Translator::StrictOrderOneRule(const std::shared_ptr<PredicateValue> &p, const std::shared_ptr<StrictOrder> &c,
                                   const std::vector<std::shared_ptr<Term>> &variableVector) {
    std::shared_ptr<EpsylonContent> newPredicate1;
    bool atomSf1 = false;
    if (isAtom(c->subformula1)) {
        atomSf1 = true;
        if (isPredicateAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<PredicateValue>(
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->symbol,
                    std::dynamic_pointer_cast<PredicateAtom>(c->subformula1)->predicate->terms);
        } else if (isConstantAtom(c->subformula1)) {
            newPredicate1 = std::make_shared<EpsylonConstant>(
                    std::dynamic_pointer_cast<ConstantAtom>(c->subformula1)->constant->value);
        } else {
            throw std::runtime_error("Unknown Atom type");
        }
    } else {
        newPredicate1 = std::make_shared<PredicateValue>("p" + std::to_string(index), variableVector);
        index++;
    }

    std::vector<std::shared_ptr<Literal>> nliterals1;
    auto e = std::make_shared<EpsylonConstant>("0");
    auto e2 = std::make_shared<EpsylonConstant>("1");
    nliterals1.push_back(std::make_shared<Literal>(newPredicate1, e2, "<"));
    nliterals1.push_back(std::make_shared<Literal>(p, e, "="));
    auto outputClause1 = std::make_shared<Clause>(nliterals1);

    std::vector<std::shared_ptr<Literal>> nliterals2;
    nliterals2.push_back(std::make_shared<Literal>(newPredicate1, e2, "="));
    nliterals2.push_back(std::make_shared<Literal>(p, e2, "="));
    auto outputClause2 = std::make_shared<Clause>(nliterals2);

    CNF output;
    if (!atomSf1) {
        CNF firstRecursion = ApplyRule(std::dynamic_pointer_cast<PredicateValue>(newPredicate1), c->subformula1,
                                       variableVector);
        output.clauses.insert(output.clauses.end(), firstRecursion.clauses.begin(), firstRecursion.clauses.end());
    }

    output.clauses.push_back(std::make_shared<Clause>(outputClause1->clone()));
    output.clauses.push_back(std::make_shared<Clause>(outputClause2->clone()));

    return output;
}

bool Translator::isAtom(std::shared_ptr<Formula> &f) {
    if (auto atom = std::dynamic_pointer_cast<PredicateAtom>(f)) {
        return true;
    }
    if (auto atom = std::dynamic_pointer_cast<ConstantAtom>(f)) {
        return true;
    }
    return false;
}

bool Translator::isPredicateAtom(std::shared_ptr<Formula> &f) {
    if (auto atom = std::dynamic_pointer_cast<PredicateAtom>(f)) {
        return true;

    }
    return false;
}

bool Translator::isConstantAtom(std::shared_ptr<Formula> &f) {
    if (auto atom = std::dynamic_pointer_cast<ConstantAtom>(f)) {
        return true;
    }
    return false;
}

CNF Translator::ApplyRule(const std::shared_ptr<PredicateValue> &np, const std::shared_ptr<Formula> &f,
                          const std::vector<std::shared_ptr<Term>> &variableVector) {
    CNF output;
    if (auto atom = std::dynamic_pointer_cast<PredicateAtom>(f)) {

        std::vector<std::shared_ptr<Literal>> nliterals;

        auto newPredicate1 = std::make_shared<PredicateValue>(atom->predicate->symbol, atom->predicate->terms);
        nliterals.push_back(std::make_shared<Literal>(np, newPredicate1, "="));

        auto outputClause = std::make_shared<Clause>(nliterals);
        output.clauses.push_back(outputClause);

    } else if (auto atom = std::dynamic_pointer_cast<ConstantAtom>(f)) {

        std::vector<std::shared_ptr<Literal>> nliterals;

        auto newPredicate1 = std::make_shared<EpsylonConstant>(atom->constant->value);
        nliterals.push_back(std::make_shared<Literal>(np, newPredicate1, "="));

        auto outputClause = std::make_shared<Clause>(nliterals);
        output.clauses.push_back(outputClause);

    } else if (auto fa = std::dynamic_pointer_cast<ForAll>(f)) {
        return ForAllRule(np, fa, variableVector);

    } else if (auto ex = std::dynamic_pointer_cast<Exists>(f)) {
        return ExistsRule(np, ex, variableVector);

    } else if (auto conj = std::dynamic_pointer_cast<Conjunction>(f)) {
        return ConjunctionRule(np, conj, variableVector);

    } else if (auto disj = std::dynamic_pointer_cast<Disjunction>(f)) {
        return DisjunctionRule(np, disj, variableVector);

    } else if (auto impl = std::dynamic_pointer_cast<Implication>(f)) {
        if (auto constant = std::dynamic_pointer_cast<ConstantAtom>(impl->subformula2)) {
            if (constant->constant->value == "0") {
                return ImplicationZeroRule(np, impl, variableVector);
            }
        }
        return ImplicationRule(np, impl, variableVector);

    } else if (auto equiv = std::dynamic_pointer_cast<Equivalence>(f)) {
        return EquivalenceRule(np, equiv, variableVector);

    } else if (auto ekv = std::dynamic_pointer_cast<EkvEquivalence>(f)) {
        if (auto constant = std::dynamic_pointer_cast<ConstantAtom>(ekv->subformula2)) {
            if (constant->constant->value == "0") {
                return EkvEquivalenceZeroRule(np, ekv, variableVector);
            } else if (constant->constant->value == "1") {
                return EkvEquivalenceOneRule(np, ekv, variableVector);
            }
        }
        return EkvEquivalenceRule(np, ekv, variableVector);

    } else if (auto stri = std::dynamic_pointer_cast<StrictOrder>(f)) {
        if (auto constant = std::dynamic_pointer_cast<ConstantAtom>(stri->subformula1)) {
            if (constant->constant->value == "0") {
                return StrictOrderZeroRule(np, stri, variableVector);
            }
        }
        if (auto constant = std::dynamic_pointer_cast<ConstantAtom>(stri->subformula2)) {
            if (constant->constant->value == "1") {
                return StrictOrderOneRule(np, stri, variableVector);
            }
        }
        return StrictOrderRule(np, stri, variableVector);

    } else {
        throw std::runtime_error("Unknown Formula type");
    }

    return output;
}
