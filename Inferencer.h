#include "CNF.h"

class Inferencer {
public:
    Inferencer(std::shared_ptr<CNF> Theory) {
        wIndex = 0;
        atoms = getAtoms(Theory);
        tcons = getTcons(Theory);
        faQAtoms = getForAllQAtoms(Theory);
        eQAtoms = getExistsQAtoms(Theory);
    };

    std::vector<std::shared_ptr<PredicateValue>> atoms;
    std::vector<std::shared_ptr<EpsylonConstant>> tcons;
    std::vector<std::shared_ptr<ForAllPredicateValue>> faQAtoms;
    std::vector<std::shared_ptr<ExistsPredicateValue>> eQAtoms;
    std::vector<std::shared_ptr<PredicateValue>> newWitnesses;
    std::set<std::string> existingSet;

    int wIndex;
    std::string omega = "gama";

    std::string getNewWitnessFunction() {
        return omega + std::to_string(wIndex++);
    }

    std::vector<std::shared_ptr<PredicateValue>> getAtoms(const std::shared_ptr<CNF>& Theory);

    std::vector<std::shared_ptr<EpsylonConstant>> getTcons(const std::shared_ptr<CNF>& Theory);

    std::vector<std::shared_ptr<ForAllPredicateValue>> getForAllQAtoms(const std::shared_ptr<CNF>& Theory);

    std::vector<std::shared_ptr<ExistsPredicateValue>> getExistsQAtoms(const std::shared_ptr<CNF>& Theory);


    Clause orderTrichotomyRule(std::shared_ptr<PredicateValue> a, std::shared_ptr<EpsylonContent> b);

    Clause orderVQuantificationRule(const std::shared_ptr<ForAllPredicateValue>& fa);

    Clause orderEQuantificationRule(const std::shared_ptr<ExistsPredicateValue>& e);

    Clause orderVWitnessingRule(std::shared_ptr<ForAllPredicateValue> fa, std::shared_ptr<EpsylonContent> b);

    Clause orderEWitnessingRule(std::shared_ptr<ExistsPredicateValue> e, std::shared_ptr<EpsylonContent> b);

    std::vector<std::shared_ptr<Clause>> applyRules(int witnessDepthLimit);

    std::vector<std::shared_ptr<Clause>>
    applyTrichRulesOnNewWitnesses(const std::vector<std::shared_ptr<PredicateValue>>& witnesses);

    std::vector<std::shared_ptr<Clause>>
    applyWitnessRulesOnNewWitnesses(const std::vector<std::shared_ptr<PredicateValue>>& witnesses, int witnessDepthLimit);

    Clause forceBoundary(const std::shared_ptr<PredicateValue>& a);

    std::vector<std::shared_ptr<Clause>>
    forceBoundaryOnNewWitnesses(const std::vector<std::shared_ptr<PredicateValue>>& witnesses);

    std::vector<std::shared_ptr<Clause>>
    applyRulesOnNewResolvent(std::shared_ptr<Clause> clause, int witnessDepthLimit);
};