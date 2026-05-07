#pragma once

#include <sstream>
#include <utility>
#include <vector>
#include <set>
#include <unordered_set>
#include "Theory.h"
#include <iostream>
#include <memory>
#include <vector>
#include <set>
#include <string>
#include "Theory.h"

class EpsylonContent {
public:

    virtual ~EpsylonContent() = default;

    virtual std::string returnStr() { return {}; };

    virtual int renameVariables(Substitution &substitution) { return 0; };

    virtual void applySubstitution(Substitution *substitution) {}

    virtual std::shared_ptr<EpsylonContent> clone() { return {}; };

    virtual std::vector<std::shared_ptr<Term>> returnFreeVariables() { return {}; }

    virtual bool equalsRenamed(std::shared_ptr<EpsylonContent> eps) { return false; }

    virtual std::string returnStructuralKey() { return ""; }

    virtual int returnWitnessFunctionDepth() { return 0; }
};

class EpsylonConstant : public EpsylonContent {
public:
    EpsylonConstant(std::string nconstant) : constant(std::move(nconstant)) {}

    std::string constant;

    int returnWitnessFunctionDepth() override {
        return 0;
    }

    std::string returnStr() override { return constant; };

    std::string returnStructuralKey() override { return constant; };

    int renameVariables(Substitution &substitution) override { return 0; };

    void applySubstitution(Substitution *substitution) override {}

    std::shared_ptr<EpsylonContent> clone() override {
        auto ret = std::make_shared<EpsylonConstant>(
                constant
        );
        return ret;
    }

    bool equalsRenamed(std::shared_ptr<EpsylonContent> eps) override {
        if (auto ec = std::dynamic_pointer_cast<EpsylonConstant>(eps)) {
            return ec->constant == constant;
        }
        return false;
    }

    std::vector<std::shared_ptr<Term>> returnFreeVariables() override { return {}; }
};


class PredicateValue : public EpsylonContent {
public:
    PredicateValue() = default;

    PredicateValue(std::string npredicate, std::vector<std::shared_ptr<Term>> nterms)
            : predicate(std::move(npredicate)), terms(std::move(nterms)) {}

    std::string predicate;
    std::vector<std::shared_ptr<Term>> terms;

    int returnWitnessFunctionDepth() override {
        auto ret = 0;
        auto topDepth = 0;
        for (auto term: terms) {
            if(topDepth< term->returnWitnessFunctionDepth()){
                topDepth = term->returnWitnessFunctionDepth();
            }
        }
        return topDepth;
    }

    std::vector<std::shared_ptr<Term>> returnFreeVariables() override {
        auto output = std::vector<std::shared_ptr<Term>>();
        for (const auto &itr: terms) {
            auto temp = itr->returnVariables();
            for (const auto &term: temp) {
                output.push_back(term);
            }
        }
        return output;
    }

    bool equalsRenamed(std::shared_ptr<EpsylonContent> eps) override {
        if (auto ep = std::dynamic_pointer_cast<PredicateValue>(eps->clone())) {
            bool eq = true;
            Substitution s1;
            Substitution s2;
            auto thisClone = std::dynamic_pointer_cast<PredicateValue>(this->clone());
            ep->renameVariables(s1);
            thisClone->renameVariables(s2);
            if (ep->predicate != thisClone->predicate) {
                return false;
            }
            if (ep->terms.size() != thisClone->terms.size()) {
                return false;
            }
            for (int i = 0; i < thisClone->terms.size(); i++) {
                eq = eq && thisClone->terms[i]->equals(ep->terms[i]);
            }
            return eq;
        }
        return false;
    }

    std::shared_ptr<EpsylonContent> clone() override {
        std::vector<std::shared_ptr<Term>> copied;
        copied.reserve(terms.size());
        for (const auto &t: terms) copied.push_back(t->clone());
        auto ret = std::make_shared<PredicateValue>(predicate, std::move(copied));
        return ret;
    }

    std::string returnStr() override {
        std::string output;
        output += predicate;
        output += "(";
        if (terms.empty()) {
            output += ")";
            return output;
        }
        for (const auto &term: terms) {
            output += term->returnStr();
            output += ",";
        }
        output[output.length() - 1] = ')';
        return output;
    }

    std::string returnStructuralKey() override {
        auto selfClone = clone();
        Substitution sub;
        selfClone->renameVariables(sub);
        return selfClone->returnStr();
    }

    int renameVariables(Substitution &substitution) override {
        std::vector<std::shared_ptr<Term>> new_terms;
        for (auto &term: terms) {
            if (auto func = std::dynamic_pointer_cast<FunctionSymbol>(term)) {
                term->renameVariables(substitution);
                new_terms.push_back(term);
            } else if (auto var = std::dynamic_pointer_cast<Variable>(term)) {
                if (substitution.contains(var->name)) {
                    new_terms.push_back(substitution.lookup(var->name)->clone());
                } else {
                    auto new_var = substitution.returnVariable();
                    auto new_var_ptr = std::make_shared<Variable>(new_var);
                    substitution.bind(var->name, new_var_ptr);
                    new_terms.push_back(std::make_shared<Variable>(new_var));
                }
            } else {
                new_terms.push_back(term);
            }
        }
        this->terms = std::move(new_terms);
        return substitution.currentHighestIndex;
    }

    void applySubstitution(Substitution *substitution) override {
        std::vector<std::shared_ptr<Term>> new_terms;
        for (auto &term: terms) {
            if (auto func = std::dynamic_pointer_cast<FunctionSymbol>(term)) {
                term->applySubstitution(substitution);
                new_terms.push_back(term);
            } else if (auto var = std::dynamic_pointer_cast<Variable>(term)) {
                if (substitution->contains(var->name)) {
                    while (substitution->contains(var->name)) {
                        if (auto c = std::dynamic_pointer_cast<Constant>(substitution->lookup(var->name)->clone())) {
                            new_terms.push_back(c);
                            var = nullptr;
                            break;
                        }
                        if (auto x = std::dynamic_pointer_cast<Variable>(substitution->lookup(var->name)->clone())) {
                            var = std::dynamic_pointer_cast<Variable>(substitution->lookup(var->name)->clone());
                        } else {
                            auto f = std::dynamic_pointer_cast<FunctionSymbol>(
                                    substitution->lookup(var->name)->clone());
                            f->applySubstitution(substitution);
                            new_terms.push_back(f);
                            var = nullptr;
                            break;
                        }
                    }
                    if (var) {
                        new_terms.push_back(var);
                    }
                } else {
                    new_terms.push_back(var);
                }
            } else {
                new_terms.push_back(term);
            }
        }
        this->terms = std::move(new_terms);
    }

};

class ForAllPredicateValue : public EpsylonContent {
public:
    ForAllPredicateValue() = default;

    ForAllPredicateValue(std::string npredicate, std::vector<std::shared_ptr<Term>> nterms,
                         std::shared_ptr<Variable> nboundVar)
            : predicate(std::move(npredicate)), terms(std::move(nterms)), boundVar(std::move(nboundVar)) {}

    std::string predicate;
    std::vector<std::shared_ptr<Term>> terms;
    std::shared_ptr<Variable> boundVar;

    std::vector<std::shared_ptr<Term>> returnFreeVariables() override {
        auto output = std::vector<std::shared_ptr<Term>>();
        for (const auto &itr: terms) {
            auto temp = itr->returnVariables();
            for (const auto &term: temp) {
                if (term->equals(boundVar)) {
                    continue;
                }
                output.push_back(term);
            }
        }
        return output;
    }

    int returnWitnessFunctionDepth() override {
        auto ret = 0;
        auto topDepth = 0;
        for (auto term: terms) {
            if(topDepth< term->returnWitnessFunctionDepth()){
                topDepth = term->returnWitnessFunctionDepth();
            }
        }
        return topDepth;
    }

    std::string returnStructuralKey() override {
        auto selfClone = clone();
        Substitution sub;
        selfClone->renameVariables(sub);
        return selfClone->returnStr();
    }

    bool equalsRenamed(std::shared_ptr<EpsylonContent> eps) override {
        if (auto ep = std::dynamic_pointer_cast<ForAllPredicateValue>(eps->clone())) {
            bool eq = true;
            Substitution s1;
            Substitution s2;
            auto thisClone = std::dynamic_pointer_cast<ForAllPredicateValue>(this->clone());
            ep->renameVariables(s1);
            thisClone->renameVariables(s2);
            if (!boundVar->equals(ep->boundVar)) {
                return false;
            }
            if (ep->predicate != thisClone->predicate) {
                return false;
            }
            if (ep->terms.size() != thisClone->terms.size()) {
                return false;
            }
            for (int i = 0; i < thisClone->terms.size(); i++) {
                eq = eq && thisClone->terms[i]->equals(ep->terms[i]);
            }
            return eq;
        }
        return false;
    }

    std::shared_ptr<EpsylonContent> clone() override {
        std::vector<std::shared_ptr<Term>> copied;
        copied.reserve(terms.size());
        for (const auto &t: terms) copied.push_back(t->clone());
        auto ret = std::make_shared<ForAllPredicateValue>(
                predicate,
                std::move(copied),
                std::dynamic_pointer_cast<Variable>(boundVar->clone())
        );
        return ret;
    }

    std::string returnStr() override {
        std::string output = "V";
        output += boundVar->returnStr();
        output += " ";
        output += predicate;
        output += "(";
        if (terms.empty()) {
            output += ")";
            return output;
        }
        for (const auto &term: terms) {
            output += term->returnStr();
            output += ",";
        }
        output[output.length() - 1] = ')';
        return output;
    }

    int renameVariables(Substitution &substitution) override {
        std::vector<std::shared_ptr<Term>> new_terms;
        for (auto &term: terms) {
            if(term->equals(boundVar)){
                new_terms.push_back(term);
                continue;
            }
            if (auto func = std::dynamic_pointer_cast<FunctionSymbol>(term)) {
                term->renameVariables(substitution);
                new_terms.push_back(term);
            } else if (auto var = std::dynamic_pointer_cast<Variable>(term)) {
                if (substitution.contains(var->name)) {
                    new_terms.push_back(substitution.lookup(var->name)->clone());
                } else {
                    auto new_var = substitution.returnVariable();
                    auto new_var_ptr = std::make_shared<Variable>(new_var);
                    substitution.bind(var->name, new_var_ptr);
                    new_terms.push_back(std::make_shared<Variable>(new_var));
                }
            } else {
                new_terms.push_back(term);
            }
        }
        this->terms = std::move(new_terms);

        return substitution.currentHighestIndex;
    }

    void applySubstitution(Substitution *substitution) override {
        std::vector<std::shared_ptr<Term>> new_terms;
        for (auto &term: terms) {
            if (auto func = std::dynamic_pointer_cast<FunctionSymbol>(term)) {
                term->applySubstitution(substitution);
                new_terms.push_back(term);
            } else if (auto var = std::dynamic_pointer_cast<Variable>(term)) {
                if (var->name == boundVar->name) {
                    new_terms.push_back(var);
                    continue;
                }
                if (substitution->contains(var->name)) {
                    while (substitution->contains(var->name)) {
                        if (auto x = std::dynamic_pointer_cast<Variable>(substitution->lookup(var->name)->clone())) {
                            var = std::dynamic_pointer_cast<Variable>(substitution->lookup(var->name)->clone());
                        } else {
                            auto f = std::dynamic_pointer_cast<FunctionSymbol>(
                                    substitution->lookup(var->name)->clone());
                            f->applySubstitution(substitution);
                            new_terms.push_back(f);
                            var = nullptr;
                            break;
                        }
                    }
                    if (var) {
                        new_terms.push_back(var);
                    }
                } else {
                    new_terms.push_back(var);
                }
            } else {
                new_terms.push_back(term);
            }
        }
        this->terms = std::move(new_terms);
    }
};

class ExistsPredicateValue : public EpsylonContent {
public:
    ExistsPredicateValue() = default;

    ExistsPredicateValue(std::string npredicate, std::vector<std::shared_ptr<Term>> nterms,
                         std::shared_ptr<Variable> nboundVar)
            : predicate(std::move(npredicate)), terms(std::move(nterms)), boundVar(std::move(nboundVar)) {}

    std::string predicate;
    std::vector<std::shared_ptr<Term>> terms;
    std::shared_ptr<Variable> boundVar;

    int returnWitnessFunctionDepth() override {
        auto ret = 0;
        auto topDepth = 0;
        for (auto term: terms) {
            if(topDepth< term->returnWitnessFunctionDepth()){
                topDepth = term->returnWitnessFunctionDepth();
            }
        }
        return topDepth;
    }

    bool equalsRenamed(std::shared_ptr<EpsylonContent> eps) override {
        if (auto ep = std::dynamic_pointer_cast<ExistsPredicateValue>(eps->clone())) {
            bool eq = true;
            Substitution s1;
            Substitution s2;
            auto thisClone = std::dynamic_pointer_cast<ExistsPredicateValue>(this->clone());
            ep->renameVariables(s1);
            thisClone->renameVariables(s2);
            if (!boundVar->equals(ep->boundVar)) {
                return false;
            }
            if (ep->predicate != thisClone->predicate) {
                return false;
            }
            if (ep->terms.size() != thisClone->terms.size()) {
                return false;
            }
            for (int i = 0; i < thisClone->terms.size(); i++) {
                eq = eq && thisClone->terms[i]->equals(ep->terms[i]);
            }
            return eq;
        }
        return false;
    }

    std::string returnStructuralKey() override {
        auto selfClone = clone();
        Substitution sub;
        selfClone->renameVariables(sub);
        return selfClone->returnStr();
    }

    std::vector<std::shared_ptr<Term>> returnFreeVariables() override {
        auto output = std::vector<std::shared_ptr<Term>>();
        for (const auto &itr: terms) {
            auto temp = itr->returnVariables();
            for (const auto &term: temp) {
                if (term->equals(boundVar)) {
                    continue;
                }
                output.push_back(term);
            }
        }
        return output;
    }

    std::shared_ptr<EpsylonContent> clone() override {
        std::vector<std::shared_ptr<Term>> copied;
        copied.reserve(terms.size());
        for (const auto &t: terms) copied.push_back(t->clone());
        auto ret = std::make_shared<ExistsPredicateValue>(
                predicate,
                std::move(copied),
                std::dynamic_pointer_cast<Variable>(boundVar->clone())
        );
        return ret;
    }

    std::string returnStr() override {
        std::string output = "E";
        output += boundVar->returnStr();
        output += " ";
        output += predicate;
        output += "(";
        if (terms.empty()) {
            output += ")";
            return output;
        }
        for (const auto &term: terms) {
            output += term->returnStr();
            output += ",";
        }
        output[output.length() - 1] = ')';
        return output;
    }


    int renameVariables(Substitution &substitution) override {
        std::vector<std::shared_ptr<Term>> new_terms;
        for (auto &term: terms) {
            if(term->equals(boundVar)){
                new_terms.push_back(term);
                continue;
            }
            if (auto func = std::dynamic_pointer_cast<FunctionSymbol>(term)) {
                term->renameVariables(substitution);
                new_terms.push_back(term);
            } else if (auto var = std::dynamic_pointer_cast<Variable>(term)) {
                if (substitution.contains(var->name)) {
                    new_terms.push_back(substitution.lookup(var->name)->clone());
                } else {
                    auto new_var = substitution.returnVariable();
                    auto new_var_ptr = std::make_shared<Variable>(new_var);
                    substitution.bind(var->name, new_var_ptr);
                    new_terms.push_back(std::make_shared<Variable>(new_var));
                }
            } else {
                new_terms.push_back(term);
            }
        }
        this->terms = std::move(new_terms);

        return substitution.currentHighestIndex;
    }

    void applySubstitution(Substitution *substitution) override {
        std::vector<std::shared_ptr<Term>> new_terms;
        for (auto &term: terms) {
            if (auto func = std::dynamic_pointer_cast<FunctionSymbol>(term)) {
                term->applySubstitution(substitution);
                new_terms.push_back(term);
            } else if (auto var = std::dynamic_pointer_cast<Variable>(term)) {
                if (substitution->contains(var->name)) {
                    if (var->name == boundVar->name) {
                        new_terms.push_back(var);
                        continue;
                    }
                    while (substitution->contains(var->name)) {
                        if (auto x = std::dynamic_pointer_cast<Variable>(substitution->lookup(var->name)->clone())) {
                            var = std::dynamic_pointer_cast<Variable>(substitution->lookup(var->name)->clone());
                        } else {
                            auto f = std::dynamic_pointer_cast<FunctionSymbol>(
                                    substitution->lookup(var->name)->clone());
                            f->applySubstitution(substitution);
                            new_terms.push_back(f);
                            var = nullptr;
                            break;
                        }
                    }
                    if (var) {
                        new_terms.push_back(var);
                    }
                } else {
                    new_terms.push_back(var);
                }
            } else {
                new_terms.push_back(term);
            }
        }
        this->terms = std::move(new_terms);
    }

};

class Literal {
public:
    Literal(std::shared_ptr<EpsylonContent> ne1,
            std::shared_ptr<EpsylonContent> ne2,
            std::string noperation)
            : e1(std::move(ne1)), e2(std::move(ne2)), operation(std::move(noperation)) {
        str = returnStr();
    }

    std::shared_ptr<EpsylonContent> e1;
    std::shared_ptr<EpsylonContent> e2;
    std::string operation;
    std::string str;

    std::string returnStructuralKey() {
        auto selfClone = clone();
        Substitution sub;
        selfClone->renameVariables(sub);
        return selfClone->returnStr();
    }

    std::string returnStr() {
        return "(" + e1->returnStr() + operation + e2->returnStr() + ")";
    }

    bool equals(const std::shared_ptr<Literal> &literal2) {
        auto selfClone = this->clone();
        Substitution sub;
        selfClone->renameVariables(sub);
        auto otherClone = literal2->clone();
        Substitution sub2;
        otherClone->renameVariables(sub2);

        if (selfClone->operation == "=" && otherClone->operation == "=") {
            if (selfClone->e1->returnStr() == otherClone->e1->returnStr() &&
                selfClone->e2->returnStr() == otherClone->e2->returnStr()) {
                return true;
            }
            if (selfClone->e2->returnStr() == otherClone->e1->returnStr() &&
                selfClone->e1->returnStr() == otherClone->e2->returnStr()) {
                return true;
            }
        }

        if (selfClone->returnStr() != otherClone->returnStr()) {
            return false;
        }
        return true;
    }

    int renameVariables(Substitution &substitution) {
        auto a1 = e1->renameVariables(substitution);
        a1 += e2->renameVariables(substitution);
        this->str = returnStr();
        return a1;
    }

    void applySubstitution(Substitution *substitution) {
        e1->applySubstitution(substitution);
        e2->applySubstitution(substitution);
        this->str = returnStr();
    }

    std::shared_ptr<Literal> clone() {
        return std::make_shared<Literal>(e1->clone(), e2->clone(), operation);
    }

};

class Clause {
public:
    Clause() = default;

    explicit Clause(std::vector<std::shared_ptr<Literal>> nliterals)
            : literals(std::move(nliterals)) {}

    std::vector<std::shared_ptr<Literal>> literals;

    void addLiteral(const std::shared_ptr<Literal> &literal) {
        literals.push_back(literal);
    }

    std::string returnStr() {
        std::string output = "|";
        for (auto i = literals.begin(); i != literals.end(); i++) {
            output += i.base()->get()->returnStr();
            output += ",";
        }
        output[output.length() - 1] = '|';
        return output;
    }

    int renameVariables(Substitution &sub) {
        int increment = 0;
        for (auto &literal: literals) {
            increment += literal->renameVariables(sub);
        }
        return increment;
    }

    void applySubstitution(Substitution &substitution) {
        for (auto &literal: literals) {
            literal->applySubstitution(&substitution);
        }
    }

    Clause clone() {
        std::vector<std::shared_ptr<Literal>> copied;
        copied.reserve(literals.size());
        for (auto &lit: literals) {
            copied.push_back(lit->clone());
        }
        return Clause(std::move(copied));
    }

};

class CNF {
public:
    CNF() = default;;

    explicit CNF(std::vector<std::shared_ptr<Clause>> nclauses) { clauses = std::move(nclauses); }

    std::vector<std::shared_ptr<Clause>> clauses;

    std::string returnStr() {
        std::string output = ":";
        for (auto &clause: clauses) {
            output += clause->returnStr();
            output += ",\n";
        }
        output[output.length() - 1] = ':';
        return output;
    }

    void renameVariables() {
        int index = 0;
        for (auto &clause: clauses) {
            Substitution sub;
            sub.currentHighestIndex = index;
            clause->renameVariables(sub);
            index = sub.currentHighestIndex + 1;
        }
    }
};