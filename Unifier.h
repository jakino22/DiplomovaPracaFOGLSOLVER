#include "Theory.h"
#include "CNF.h"
#include "map"


class Unifier {
public:
    Unifier() = default;

    bool attempt_unification(const std::shared_ptr<Literal>& unit, const std::shared_ptr<Literal>& other, Substitution &substitution);

    bool unifyEpsilons(const std::shared_ptr<EpsylonContent> &e1, const std::shared_ptr<EpsylonContent> &e2,
                       Substitution &sigma);

    bool unifyTerms(std::shared_ptr<Term> term1, std::shared_ptr<Term> term2, Substitution &sigma);

    bool isBoundPosition(const std::shared_ptr<Term>& term, const std::string& varName);

    bool chainable(const std::shared_ptr<Literal>& a, const std::shared_ptr<Literal>& b, Substitution &sigma);

    bool
    attempt_unification_with_operation(const std::shared_ptr<Literal>& unit, const std::shared_ptr<Literal>& other,
                                       Substitution &sigma);

    bool
    variable_renaming_substitution(const std::shared_ptr<Literal>& unit, const std::shared_ptr<Literal>& other, Substitution &sigma);

    bool variable_renaming_substitution_with_operation(const std::shared_ptr<Literal>& unit, const std::shared_ptr<Literal>& other,
                                                       Substitution &sigma);

    bool variable_renaming_substitution_epsilons(const std::shared_ptr<EpsylonContent> &e1,
                                                 const std::shared_ptr<EpsylonContent> &e2, Substitution &sigma);

    bool
    variable_renaming_substitution_terms(std::shared_ptr<Term> tterm1, std::shared_ptr<Term> tterm2,
                                         Substitution &sigma);

    std::shared_ptr<Term> applyEverything(std::shared_ptr<Term> term, Substitution &sigma);
};
