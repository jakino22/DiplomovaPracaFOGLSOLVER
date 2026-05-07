#include "CNF.h"
#include "Theory.h"

class Translator {
public:
    int index = 0;
    Translator() = default;

    CNF translate(const std::shared_ptr<Theory>& theory);

    CNF ConjunctionRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<Conjunction>& c,
                        const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF DisjunctionRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<Disjunction>& c,
                        const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF ImplicationRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<Implication>& c,
                        const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF EquivalenceRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<Equivalence>& c,
                        const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF EkvEquivalenceRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<EkvEquivalence>& c,
                           const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF StrictOrderRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<StrictOrder>& c,
                        const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF ImplicationZeroRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<Implication>& c,
                            const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF EkvEquivalenceZeroRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<EkvEquivalence>& c,
                               const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF EkvEquivalenceOneRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<EkvEquivalence>& c,
                              const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF StrictOrderZeroRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<StrictOrder>& c,
                            const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF StrictOrderOneRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<StrictOrder>& c,
                           const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF ForAllRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<ForAll>& c,
                   const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF ExistsRule(const std::shared_ptr<PredicateValue>& p, const std::shared_ptr<Exists>& c,
                   const std::vector<std::shared_ptr<Term>>& variableVector);

    CNF ApplyRule(const std::shared_ptr<PredicateValue>& np, const std::shared_ptr<Formula>& f,
                  const std::vector<std::shared_ptr<Term>>& variableVector);

    bool isAtom(std::shared_ptr<Formula> &f);

    bool isPredicateAtom(std::shared_ptr<Formula> &f);

    bool isConstantAtom(std::shared_ptr<Formula> &f);
};