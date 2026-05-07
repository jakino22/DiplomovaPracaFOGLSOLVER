#include "Unifier.h"

bool
Unifier::attempt_unification(const std::shared_ptr<Literal>& unit, const std::shared_ptr<Literal>& other, Substitution &sigma) {
    if (!unifyEpsilons(unit->e1, other->e1, sigma)) {
        return false;
    }
    if (!unifyEpsilons(unit->e2, other->e2, sigma)) {
        return false;
    }

    return true;
}

bool
Unifier::attempt_unification_with_operation(const std::shared_ptr<Literal>& unit, const std::shared_ptr<Literal>& other,
                                            Substitution &sigma) {
    if (unit->operation != other->operation) {
        return false;
    }
    if (!unifyEpsilons(unit->e1, other->e1, sigma)) {
        return false;
    }
    if (!unifyEpsilons(unit->e2, other->e2, sigma)) {
        return false;
    }

    return true;
}

std::shared_ptr<Term> Unifier::applyEverything(std::shared_ptr<Term> term, Substitution &sigma) {
    while (auto var = std::dynamic_pointer_cast<Variable>(term)) {
        if (!sigma.contains(var->name)) break;
        term = sigma.lookup(var->name);
    }
    return term;
}

bool Unifier::unifyTerms(std::shared_ptr<Term> tterm1, std::shared_ptr<Term> tterm2, Substitution &sigma) {
    auto term1 = applyEverything(tterm1, sigma);
    auto term2 = applyEverything(tterm2, sigma);

    if (term1->returnStr() == term2->returnStr()) {
        return true;
    }

    if (auto var1 = std::dynamic_pointer_cast<Variable>(term1)) {
        if (term2->variableExistsInTerm(var1->name, sigma)) {
            return false;
        }
        sigma.bind(var1->name, term2);
        return true;
    }
    if (auto var2 = std::dynamic_pointer_cast<Variable>(term2)) {
        if (term1->variableExistsInTerm(var2->name, sigma)) {
            return false;
        }
        sigma.bind(var2->name, term1);
        return true;
    }

    if (std::dynamic_pointer_cast<Constant>(term1) && std::dynamic_pointer_cast<Constant>(term2)) {
        return false;
    }

    if (auto func1 = std::dynamic_pointer_cast<FunctionSymbol>(term1)) {
        if (auto func2 = std::dynamic_pointer_cast<FunctionSymbol>(term2)) {
            if (func1->symbol != func2->symbol || func1->terms.size() != func2->terms.size()) {
                return false;
            }
            for (int i = 0; i < func1->terms.size(); i++) {
                if (!unifyTerms(func1->terms[i], func2->terms[i], sigma)) {
                    return false;
                }
            }
            return true;
        }
    }

    return false;
}

bool Unifier::isBoundPosition(const std::shared_ptr<Term>& term, const std::string& varName) {
    auto var = std::dynamic_pointer_cast<Variable>(term);
    return var && var->name == varName;
}

bool Unifier::unifyEpsilons(const std::shared_ptr<EpsylonContent> &e1, const std::shared_ptr<EpsylonContent> &e2,
                            Substitution &sigma) {

    if (auto t1 = std::dynamic_pointer_cast<EpsylonConstant>(e1)) {
        if (auto t2 = std::dynamic_pointer_cast<EpsylonConstant>(e2)) {
            return t1->constant == t2->returnStr();
        }
        return false;
    }

    if (auto t2 = std::dynamic_pointer_cast<EpsylonConstant>(e2)) {
        return false;
    }

    if (auto p1 = std::dynamic_pointer_cast<PredicateValue>(e1)) {
        if (auto p2 = std::dynamic_pointer_cast<PredicateValue>(e2)) {
            if (p1->predicate != p2->predicate || p1->terms.size() != p2->terms.size()) {
                return false;
            }
            for (int i = 0; i < p1->terms.size(); i++) {
                if (!unifyTerms(p1->terms[i], p2->terms[i], sigma)) {
                    return false;
                }
            }
            return true;
        }
    }

    if (auto qa1 = std::dynamic_pointer_cast<ForAllPredicateValue>(e1)) {
        if (auto qa2 = std::dynamic_pointer_cast<ForAllPredicateValue>(e2)) {
            if (qa1->boundVar->name != qa2->boundVar->name || qa1->predicate != qa2->predicate || qa1->terms.size() != qa2->terms.size()) {
                return false;
            }

            for (int i = 0; i < qa1->terms.size(); i++) {
                bool bound1 = isBoundPosition(qa1->terms[i], qa1->boundVar->name);
                bool bound2 = isBoundPosition(qa2->terms[i], qa2->boundVar->name);

                if (bound1 != bound2) {
                    return false;
                }

                if(bound1 && bound2){
                    continue;
                }

                if (!unifyTerms(qa1->terms[i], qa2->terms[i], sigma)) {
                    return false;
                }

            }
            return true;
        }
    }

    if (auto qe1 = std::dynamic_pointer_cast<ExistsPredicateValue>(e1)) {
        if (auto qe2 = std::dynamic_pointer_cast<ExistsPredicateValue>(e2)) {
            if (qe1->boundVar->name != qe2->boundVar->name || qe1->predicate != qe2->predicate || qe1->terms.size() != qe2->terms.size()) {
                return false;
            }

            for (int i = 0; i < qe1->terms.size(); i++) {
                bool bound1 = isBoundPosition(qe1->terms[i], qe1->boundVar->name);
                bool bound2 = isBoundPosition(qe2->terms[i], qe2->boundVar->name);

                if (bound1 != bound2) {
                    return false;
                }

                if(bound1 && bound2){
                    continue;
                }

                if (!unifyTerms(qe1->terms[i], qe2->terms[i], sigma)) {
                    return false;
                }

            }
            return true;
        }
    }
    return false;
}

bool Unifier::chainable(const std::shared_ptr<Literal>& a, const std::shared_ptr<Literal>& b, Substitution &sigma) {
    Substitution s1 = sigma;
    if (unifyEpsilons(a->e2->clone(), b->e1->clone(), s1)) {
        sigma = std::move(s1);
        return true;
    }

    Substitution s2 = sigma;
    if (b->operation == "=") {
        if (unifyEpsilons(a->e2->clone(), b->e2->clone(), s2)) {
            std::swap(b->e1, b->e2);
            sigma = std::move(s2);
            return true;
        }
    }

    return false;
}

bool Unifier::variable_renaming_substitution(const std::shared_ptr<Literal>& unit,
                                             const std::shared_ptr<Literal>& other,
                                             Substitution &sigma) {
    if (!variable_renaming_substitution_epsilons(unit->e1, other->e1, sigma)) {
        return false;
    }
    if (!variable_renaming_substitution_epsilons(unit->e2, other->e2, sigma)) {
        return false;
    }

    return true;
}

bool Unifier::variable_renaming_substitution_with_operation(const std::shared_ptr<Literal>& unit,
                                                            const std::shared_ptr<Literal>& other,
                                                            Substitution &sigma) {
    if (unit->operation != other->operation) {
        return false;
    }
    if (!variable_renaming_substitution_epsilons(unit->e1, other->e1, sigma)) {
        return false;
    }
    if (!variable_renaming_substitution_epsilons(unit->e2, other->e2, sigma)) {
        return false;
    }

    return true;
}

bool Unifier::variable_renaming_substitution_terms(std::shared_ptr<Term> tterm1,
                                                   std::shared_ptr<Term> tterm2,
                                                   Substitution &sigma) {
    auto term1 = applyEverything(tterm1, sigma);
    auto term2 = applyEverything(tterm2, sigma);

    if (term1->returnStr() == term2->returnStr()) {
        return true;
    }

    if (auto var1 = std::dynamic_pointer_cast<Variable>(term1)) {
        if (auto var2 = std::dynamic_pointer_cast<Variable>(term2)) {
            sigma.bind(var1->name, var2);
            return true;
        }
        return false;
    }

    if (std::dynamic_pointer_cast<Variable>(term2)) {
        return false;
    }

    if (auto const1 = std::dynamic_pointer_cast<Constant>(term1)) {
        if (auto const2 = std::dynamic_pointer_cast<Constant>(term2)) {
            return const1->value == const2->value;
        }
        return false;
    }

    if (std::dynamic_pointer_cast<Constant>(term2)) {
        return false;
    }

    if (auto func1 = std::dynamic_pointer_cast<FunctionSymbol>(term1)) {
        if (auto func2 = std::dynamic_pointer_cast<FunctionSymbol>(term2)) {
            if (func1->symbol != func2->symbol || func1->terms.size() != func2->terms.size()) {
                return false;
            }

            for (int i = 0; i < static_cast<int>(func1->terms.size()); i++) {
                if (!variable_renaming_substitution_terms(func1->terms[i], func2->terms[i], sigma)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    return false;
}

bool Unifier::variable_renaming_substitution_epsilons(const std::shared_ptr<EpsylonContent> &e1,
                                                      const std::shared_ptr<EpsylonContent> &e2,
                                                      Substitution &sigma) {
    if (auto t1 = std::dynamic_pointer_cast<EpsylonConstant>(e1)) {
        if (auto t2 = std::dynamic_pointer_cast<EpsylonConstant>(e2)) {
            return t1->constant == t2->constant;
        }
        return false;
    }

    if (std::dynamic_pointer_cast<EpsylonConstant>(e2)) {
        return false;
    }

    if (auto p1 = std::dynamic_pointer_cast<PredicateValue>(e1)) {
        if (auto p2 = std::dynamic_pointer_cast<PredicateValue>(e2)) {
            if (p1->predicate != p2->predicate || p1->terms.size() != p2->terms.size()) {
                return false;
            }

            for (int i = 0; i < p1->terms.size(); i++) {
                if (!variable_renaming_substitution_terms(p1->terms[i], p2->terms[i], sigma)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    if (auto qa1 = std::dynamic_pointer_cast<ForAllPredicateValue>(e1)) {
        if (auto qa2 = std::dynamic_pointer_cast<ForAllPredicateValue>(e2)) {
            if (qa1->boundVar->name != qa2->boundVar->name || qa1->predicate != qa2->predicate || qa1->terms.size() != qa2->terms.size()) {
                return false;
            }

            for (int i = 0; i < static_cast<int>(qa1->terms.size()); i++) {
                bool bound1 = isBoundPosition(qa1->terms[i], qa1->boundVar->name);
                bool bound2 = isBoundPosition(qa2->terms[i], qa2->boundVar->name);

                if (bound1 != bound2) {
                    return false;
                }

                if(bound1 && bound2){
                    continue;
                }

                if (!variable_renaming_substitution_terms(qa1->terms[i], qa2->terms[i], sigma)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    if (auto qe1 = std::dynamic_pointer_cast<ExistsPredicateValue>(e1)) {
        if (auto qe2 = std::dynamic_pointer_cast<ExistsPredicateValue>(e2)) {
            if (qe1->boundVar->name != qe2->boundVar->name || qe1->predicate != qe2->predicate || qe1->terms.size() != qe2->terms.size()) {
                return false;
            }

            for (int i = 0; i < static_cast<int>(qe1->terms.size()); i++) {
                bool bound1 = isBoundPosition(qe1->terms[i], qe1->boundVar->name);
                bool bound2 = isBoundPosition(qe2->terms[i], qe2->boundVar->name);

                if (bound1 != bound2) {
                    return false;
                }

                if(bound1 && bound2){
                    continue;
                }

                if (!variable_renaming_substitution_terms(qe1->terms[i], qe2->terms[i], sigma)) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    return false;
}
