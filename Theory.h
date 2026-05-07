#pragma once

#include <sstream>
#include <utility>
#include <vector>
#include <set>
#include <unordered_set>
#include <memory>
#include <bits/stdc++.h>
#include <map>

class Term;

struct Substitution {
    int currentHighestIndex = 0;
    std::string zeta = "zeta";
    std::map<std::string, std::shared_ptr<Term>> map;

    bool contains(const std::string &var) {
        return map.find(var) != map.end();
    }

    std::shared_ptr<Term> lookup(const std::string &var) {
        auto it = map.find(var);
        return (it == map.end()) ? nullptr : it->second;
    }

    void bind(const std::string &var, std::shared_ptr<Term> term) {
        map[var] = std::move(term);
    }

    void unbind(const std::string &var) {
        map.erase(var);
    }

    std::string returnVariable() {
        currentHighestIndex++;
        return zeta + std::to_string(currentHighestIndex);
    }
};

class Term {
public:
    virtual ~Term() = default;

    virtual std::vector<std::shared_ptr<Term>> returnVariables() { return {}; };

    virtual std::string returnStr() { return ""; };

    virtual bool equals(const std::shared_ptr<Term> &other) const { return false; }

    virtual int renameVariables(Substitution &sub) { return 0; }

    virtual int returnWitnessFunctionDepth() { return 0; }

    virtual void applySubstitution(Substitution *substitution) {}

    virtual bool variableExistsInTerm(const std::string &name, Substitution &sigma) {
        return false;
    }

    virtual std::shared_ptr<Term> clone() { return {}; };
};

class Variable : public Term {
public:
    explicit Variable(std::string nname) : name(std::move(nname)) {}

    std::string name;

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        return {std::make_shared<Variable>(name)};
    };

    std::string returnStr() override {
        return name;
    }

    bool variableExistsInTerm(const std::string &name, Substitution &sigma) override {
        if (this->name == name) return true;
        if (sigma.contains(this->name)) {
            return sigma.lookup(this->name)->variableExistsInTerm(name, sigma);
        }
        return false;
    }

    bool equals(const std::shared_ptr<Term> &other) const override {
        if (auto v = std::dynamic_pointer_cast<Variable>(other)) {
            return v->name == name;
        }
        return false;
    }

    int renameVariables(Substitution &substitution) override {
        return 0;
    }

    void applySubstitution(Substitution *substitution) override {
    }

    std::shared_ptr<Term> clone() override {
        return std::make_shared<Variable>(name);
    }

    int returnWitnessFunctionDepth() override {
        return 0;
    }
};

class Constant : public Term {
public:
    explicit Constant(std::string nvalue) : value(std::move(nvalue)) {}

    std::string value;

    int returnWitnessFunctionDepth() override {
        return 0;
    }

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        return {};
    };

    std::string returnStr() override {
        return value;
    }

    bool variableExistsInTerm(const std::string &name, Substitution &sigma) override {
        return false;
    }

    bool equals(const std::shared_ptr<Term> &other) const override {
        if (auto c = std::dynamic_pointer_cast<Constant>(other)) {
            return c->value == value;
        }
        return false;
    }

    int renameVariables(Substitution &substitution) override {
        return 0;
    }

    void applySubstitution(Substitution *substitution) override {
    }

    std::shared_ptr<Term> clone() override {
        return std::make_shared<Constant>(value);
    }
};

class Predicate;

class FunctionSymbol : public Term {
public:
    FunctionSymbol(std::string nsymbol, std::vector<std::shared_ptr<Term>> nterms)
            : symbol(std::move(nsymbol)), terms(std::move(nterms)) {}

    std::string symbol;
    std::vector<std::shared_ptr<Term>> terms;
    int depthLevel = 0;

    int returnWitnessFunctionDepth() override {
        int ret = 0;
        if (symbol.find("gama") != std::string::npos) {
            ret++;
        }
        auto topDepth = 0;
        for (auto term: terms) {
            if(topDepth< term->returnWitnessFunctionDepth()){
                topDepth = term->returnWitnessFunctionDepth();
            }
        }
        return ret+topDepth;
    }


    std::vector<std::shared_ptr<Term>> returnVariables() override {
        auto output = std::vector<std::shared_ptr<Term>>();
        for (const auto &itr: terms) {
            auto temp = itr->returnVariables();
            for (const auto &term: temp) {
                output.push_back(term);
            }
        }
        return output;
    };

    bool equals(const std::shared_ptr<Term> &other) const override {
        if (auto f = std::dynamic_pointer_cast<FunctionSymbol>(other)) {
            if (f->symbol != symbol) {
                return false;
            }
            if (f->terms.size() != terms.size()) {
                return false;
            }
            for (int i = 0; i < terms.size(); i++) {
                if (!f->terms[i]->equals(terms[i])) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    bool variableExistsInTerm(const std::string &name, Substitution &sigma) override {
        for (auto &term: terms) {
            if (term->variableExistsInTerm(name, sigma)) return true;
        }
        return false;
    }

    std::string returnStr() {
        std::string output = symbol + "(";
        for (const auto &term: terms) {
            output += term->returnStr();
            output += ",";
        }
        output += ")";
        return output;
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

    std::shared_ptr<Term> clone() override {
        std::vector<std::shared_ptr<Term>> copied;
        copied.reserve(terms.size());
        for (const auto &t: terms) copied.push_back(t->clone());
        auto ret = std::make_shared<FunctionSymbol>(symbol, std::move(copied));
        ret->depthLevel = depthLevel;
        return ret;
    }
};

class Predicate {
public:
    Predicate(std::string nname, std::vector<std::shared_ptr<Term>> nterms)
            : symbol(std::move(nname)), terms(std::move(nterms)) {}

    std::string symbol;
    std::vector<std::shared_ptr<Term>> terms;


    std::vector<std::shared_ptr<Term>> returnVariables() {
        auto output = std::vector<std::shared_ptr<Term>>();
        for (const auto &itr: terms) {
            auto temp = itr->returnVariables();
            for (const auto &term: temp) {
                output.push_back(term);
            }
        }
        return output;
    };

    bool equals(const std::shared_ptr<Term> &other) const {
        if (auto f = std::dynamic_pointer_cast<Predicate>(other)) {
            if (f->symbol != symbol) {
                return false;
            }
            if (f->terms.size() != terms.size()) {
                return false;
            }
            for (int i = 0; i < terms.size(); i++) {
                if (!f->terms[i]->equals(terms[i])) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    std::string returnStr() {
        std::string output = symbol + "(";
        for (const auto &term: terms) {
            output += term->returnStr();
        }
        output += ")";
        return output;
    }

    void renameVariables(Substitution &substitution) {
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
    }

    void applySubstitution(Substitution *substitution) {
        std::vector<std::shared_ptr<Term>> new_terms;
        for (auto &term: terms) {
            if (auto func = std::dynamic_pointer_cast<FunctionSymbol>(term)) {
                term->applySubstitution(substitution);
                new_terms.push_back(term);
            } else if (auto var = std::dynamic_pointer_cast<Variable>(term)) {
                if (substitution->contains(var->name)) {
                    new_terms.push_back(substitution->lookup(var->name)->clone());
                } else {
                    new_terms.push_back(term);
                }

            } else {
                new_terms.push_back(term);
            }
        }
        this->terms = std::move(new_terms);
    }

    std::shared_ptr<Predicate> clone() {
        std::vector<std::shared_ptr<Term>> copied;
        copied.reserve(terms.size());
        for (const auto &t: terms) copied.push_back(t->clone());
        return std::make_shared<Predicate>(symbol, std::move(copied));
    }
};

class Formula {
public:
    virtual ~Formula() = default;

    virtual std::vector<std::shared_ptr<Term>> returnVariables() { return {}; };

    virtual std::vector<std::shared_ptr<Term>> returnAllVariables() { return {}; };
};

class PredicateAtom : public Formula {
public:
    explicit PredicateAtom(std::shared_ptr<Predicate> npredicate) : predicate(std::move(npredicate)) {}

    std::shared_ptr<Predicate> predicate;

    std::vector<std::shared_ptr<Term>> returnVariables() override { return predicate->returnVariables(); };

    std::vector<std::shared_ptr<Term>> returnAllVariables() override { return predicate->returnVariables(); };
};

class ConstantAtom : public Formula {
public:
    explicit ConstantAtom(std::shared_ptr<Constant> nconstant) : constant(std::move(nconstant)) {}

    std::shared_ptr<Constant> constant;

    std::vector<std::shared_ptr<Term>> returnVariables() override { return constant->returnVariables(); };

    std::vector<std::shared_ptr<Term>> returnAllVariables() override { return constant->returnVariables(); };
};


class ForAll : public Formula {
public:
    explicit ForAll(std::shared_ptr<Formula> nsubformula, std::shared_ptr<Variable> nboundVariable)
            : subformula(std::move(nsubformula)), boundVariable(std::move(nboundVariable)) {}

    std::shared_ptr<Formula> subformula;
    std::shared_ptr<Variable> boundVariable;

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        auto vars = subformula->returnVariables();
        vars.erase(std::remove_if(vars.begin(), vars.end(), [&](const std::shared_ptr<Term> &t) {
            return
                    boundVariable->equals(t);
        }), vars.end());
        return vars;
    }

    std::vector<std::shared_ptr<Term>> returnAllVariables() override {
        return subformula->returnAllVariables();
    }
};

class Exists : public Formula {
public:
    explicit Exists(std::shared_ptr<Formula> nsubformula, std::shared_ptr<Variable> nboundVariable)
            : subformula(std::move(nsubformula)), boundVariable(std::move(nboundVariable)) {}

    std::shared_ptr<Formula> subformula;
    std::shared_ptr<Variable> boundVariable;

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        auto vars = subformula->returnVariables();
        vars.erase(std::remove_if(vars.begin(), vars.end(), [&](const std::shared_ptr<Term> &t) {
            return
                    boundVariable->equals(t);
        }), vars.end());
        return vars;
    }

    std::vector<std::shared_ptr<Term>> returnAllVariables() override {
        return subformula->returnAllVariables();
    }
};

class Conjunction : public Formula {
public:
    Conjunction(std::shared_ptr<Formula> left, std::shared_ptr<Formula> right)
            : subformula1(std::move(left)), subformula2(std::move(right)) {}

    std::shared_ptr<Formula> subformula1;
    std::shared_ptr<Formula> subformula2;

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnVariables();
        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }

    std::vector<std::shared_ptr<Term>> returnAllVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnAllVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnAllVariables();
        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }
};

class Disjunction : public Formula {
public:
    Disjunction(std::shared_ptr<Formula> left, std::shared_ptr<Formula> right)
            : subformula1(std::move(left)), subformula2(std::move(right)) {}

    std::shared_ptr<Formula> subformula1;
    std::shared_ptr<Formula> subformula2;

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnVariables();

        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }

    std::vector<std::shared_ptr<Term>> returnAllVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnAllVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnAllVariables();
        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }
};

class Implication : public Formula {
public:
    Implication(std::shared_ptr<Formula> left, std::shared_ptr<Formula> right)
            : subformula1(std::move(left)), subformula2(std::move(right)) {}

    std::shared_ptr<Formula> subformula1;
    std::shared_ptr<Formula> subformula2;

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnVariables();
        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }

    std::vector<std::shared_ptr<Term>> returnAllVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnAllVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnAllVariables();
        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }
};


class Equivalence : public Formula {
public:
    Equivalence(std::shared_ptr<Formula> n1, std::shared_ptr<Formula> n2)
            : subformula1(std::move(n1)), subformula2(std::move(n2)) {}

    std::shared_ptr<Formula> subformula1;
    std::shared_ptr<Formula> subformula2;

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnVariables();

        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }

    std::vector<std::shared_ptr<Term>> returnAllVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnAllVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnAllVariables();
        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }
};

class EkvEquivalence : public Formula {
public:
    EkvEquivalence(std::shared_ptr<Formula> n1, std::shared_ptr<Formula> n2)
            : subformula1(std::move(n1)), subformula2(std::move(n2)) {}

    std::shared_ptr<Formula> subformula1;
    std::shared_ptr<Formula> subformula2;

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnVariables();

        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }

    std::vector<std::shared_ptr<Term>> returnAllVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnAllVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnAllVariables();
        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }
};

class StrictOrder : public Formula {
public:
    StrictOrder(std::shared_ptr<Formula> n1, std::shared_ptr<Formula> n2)
            : subformula1(std::move(n1)), subformula2(std::move(n2)) {}

    std::shared_ptr<Formula> subformula1;
    std::shared_ptr<Formula> subformula2;

    std::vector<std::shared_ptr<Term>> returnVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnVariables();

        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }

    std::vector<std::shared_ptr<Term>> returnAllVariables() override {
        std::vector<std::shared_ptr<Term>> s1 = subformula1->returnAllVariables();
        std::vector<std::shared_ptr<Term>> s2 = subformula2->returnAllVariables();
        for (const auto &temp: s2) {
            s1.push_back(temp);
        }
        return s1;
    }
};

class Theory {
public:
    Theory() = default;

    explicit Theory(std::vector<std::shared_ptr<Formula>> nformulae)
            : formulae(std::move(nformulae)) {}

    std::vector<std::shared_ptr<Formula>> formulae;
};
