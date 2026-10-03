import RelationalFoundations.FiniteRuleScope
import RelationalFoundations.FiniteRuleInstances
set_option genInjectivity false

namespace RelationalFoundations.RuleScopeTests
open FiniteRuleConstruction

theorem fragment_identity_required : ExactTransport (Unit ⊕ Unit) Unit → False := fun transport =>
  have left : Sum.inl () = transport.backward () := (transport.forwardBackward (.inl ())).symm
  have right : transport.backward () = Sum.inr () := transport.forwardBackward (.inr ())
  nomatch left.trans right

def falseObservation : History HeterogeneousFeedback.Step (.ready 0) (.observed 0 false) :=
  .extend .root (.observe 0 false)

theorem false_observation_unrealizable :
    ¬ Nonempty ((FiniteRuleInstances.heterogeneous 0).Complete falseObservation) :=
  fun actual => Bool.noConfusion
    (((FiniteRuleInstances.heterogeneous 0).coverage_iff falseObservation).mpr actual).2

theorem homogeneous_unique {Token : Type} (choose : List Token → Token) {one two : List Token}
    (left : History (HistoricalFeedback.Step Token) [] one)
    (right : History (HistoricalFeedback.Step Token) [] two)
    (leftAllowed : FeedbackCoverage.Admissible choose left) (rightAllowed : FeedbackCoverage.Admissible choose right)
    (same : left.length = right.length) :
    (⟨one, left⟩ : (target : List Token) × History (HistoricalFeedback.Step Token) [] target) = ⟨two, right⟩ :=
  FiniteRuleScope.admissible_unique (FiniteRuleInstances.homogeneous Token choose) left right
    ((FiniteRuleInstances.homogeneousAdmission Token choose left).mpr leftAllowed)
    ((FiniteRuleInstances.homogeneousAdmission Token choose right).mpr rightAllowed) same

end RelationalFoundations.RuleScopeTests

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.RuleScopeTests.fragment_identity_required
#print axioms RelationalFoundations.RuleScopeTests.false_observation_unrealizable
#print axioms RelationalFoundations.RuleScopeTests.homogeneous_unique
/- AXIOM_AUDIT_END -/
