import RelationalFoundations.FiniteRuleCoordinates
import Tests.FiniteRuleConstruction
import Tests.CyclicSupport
set_option genInjectivity false
set_option linter.defProp false

namespace RelationalFoundations.FiniteRuleCoordinatesTests
open FiniteRuleConstruction FiniteRuleInstances FiniteRuleCoordinates
universe u

def homogeneous_all (Token : Type u) (choose : List Token → Token) {target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] target) (admitted : FeedbackCoverage.Admissible choose history)
    (request : (homogeneous Token choose).Requests history ()) :=
  homogeneous_native_coordinates Token choose history admitted request

def heterogeneous_all {seed : Nat} {target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) target) (admitted : HeterogeneousFeedback.Admissible history)
    (kind : TypedResources.Kind) (request : (heterogeneous seed).Requests history kind) :=
  heterogeneous_native_coordinates history admitted kind request

def higher_universe (choose : List (ULift.{1} Bool) → ULift.{1} Bool)
    {target : List (ULift.{1} Bool)}
    (history : History (HistoricalFeedback.Step (ULift.{1} Bool)) [] target)
    (admitted : FeedbackCoverage.Admissible choose history)
    (request : (homogeneous (ULift.{1} Bool) choose).Requests history ()) :=
  homogeneous_all _ choose history admitted request

def thirteen_coordinates (request : (homogeneous Bool FeedbackCoverageTests.alternating).Requests FeedbackCoverageTests.whole ()) :=
  homogeneous_all Bool FeedbackCoverageTests.alternating FeedbackCoverageTests.whole FeedbackCoverageTests.whole_admitted request

def seven_coordinates (kind : TypedResources.Kind) (request : (heterogeneous 0).Requests HeterogeneousFeedbackTests.h6 kind) :=
  heterogeneous_all HeterogeneousFeedbackTests.h6 HeterogeneousFeedbackTests.a6 kind request

def thirteen_ordered_dependencies
    (request : (homogeneous Bool FeedbackCoverageTests.alternating).Requests FeedbackCoverageTests.whole ()) :=
  homogeneous_dependencies Bool FeedbackCoverageTests.alternating FeedbackCoverageTests.whole FeedbackCoverageTests.whole_admitted request

def seven_ordered_dependencies (kind : TypedResources.Kind)
    (request : (heterogeneous 0).Requests HeterogeneousFeedbackTests.h6 kind) :=
  heterogeneous_dependencies HeterogeneousFeedbackTests.h6 HeterogeneousFeedbackTests.a6 kind request

def all_resumed_coordinates {rules : Rules.{u}} {middle target : rules.State}
    (history : History rules.Step rules.origin middle) (admitted : rules.Admissible history)
    (prior : rules.Realization history) (following : History rules.Step middle target)
    (allowed : rules.Admissible following) (kind : rules.Kind) (request : rules.Requests history kind) :=
  resumed_coordinates history admitted prior following allowed kind request

def all_composed_coordinates {rules : Rules.{u}} {middle next target : rules.State}
    (history : History rules.Step rules.origin middle) (admitted : rules.Admissible history)
    (prior : rules.Realization history) (one : History rules.Step middle next) (allowedOne : rules.Admissible one)
    (two : History rules.Step next target) (allowedTwo : rules.Admissible two)
    (kind : rules.Kind) (request : rules.Requests history kind) :=
  resumed_composed_coordinates history admitted prior one allowedOne two allowedTwo kind request

def real_resumed_coordinates (kind : TypedResources.Kind)
    (request : (heterogeneous 0).Requests HeterogeneousFeedbackTests.h2 kind) :=
  resumed_coordinates HeterogeneousFeedbackTests.h2
    ((heterogeneousAdmission 0 _).mpr HeterogeneousFeedbackTests.a2)
    FiniteRuleConstructionTests.hetTwo.realization HeterogeneousFeedbackTests.suffix
    ((heterogeneousAdmission 0 _).mpr HeterogeneousFeedbackTests.suffix_admitted) kind request

def native_homogeneous_reprise (Token : Type u) (choose : List Token → Token) {middle target : List Token}
    (history : History (HistoricalFeedback.Step Token) [] middle) (admitted : FeedbackCoverage.Admissible choose history)
    (prior : (homogeneous Token choose).Realization history)
    (following : History (HistoricalFeedback.Step Token) middle target) (allowed : FeedbackCoverage.Admissible choose following)
    (request : (homogeneous Token choose).Requests history ()) :=
  homogeneous_resumed_coordinates Token choose history admitted prior following allowed request

def native_heterogeneous_reprise {seed : Nat} {middle target : HeterogeneousFeedback.State}
    (history : History HeterogeneousFeedback.Step (.ready seed) middle) (admitted : HeterogeneousFeedback.Admissible history)
    (prior : (heterogeneous seed).Realization history) (following : History HeterogeneousFeedback.Step middle target)
    (allowed : HeterogeneousFeedback.Admissible following) (kind : TypedResources.Kind)
    (request : (heterogeneous seed).Requests history kind) :=
  heterogeneous_resumed_coordinates history admitted prior following allowed kind request

def swap : ExactTransport (Unit ⊕ Unit) (Unit ⊕ Unit) where
  forward := fun value => match value with | .inl atom => .inr atom | .inr atom => .inl atom
  backward := fun value => match value with | .inl atom => .inr atom | .inr atom => .inl atom
  forwardBackward := fun value => by cases value <;> rfl
  backwardForward := fun value => by cases value <;> rfl

def permuted : (CyclicSupportTests.cyclic 0).Coverage CyclicSupportTests.oneStep (1 : Nat) where
  coordinates := fun _ => swap
  values := fun _ request => by cases request <;> rfl

theorem permuted_changes_identity :
    (permuted.coordinates ()).forward (.inl ()) ≠
      (((CyclicSupportTests.cyclic 0).complete CyclicSupportTests.oneStep
        (CyclicSupportTests.admitted 0 _)).coverage.coordinates ()).forward (.inl ()) := by
  intro same
  change (Sum.inr () : Unit ⊕ Unit) = Sum.inl () at same
  cases same

theorem values_still_agree (request : (CyclicSupportTests.cyclic 0).Requests CyclicSupportTests.oneStep ()) :
    (CyclicSupportTests.cyclic 0).read (1 : Nat) () ((permuted.coordinates ()).forward request) =
      (CyclicSupportTests.cyclic 0).expected CyclicSupportTests.oneStep () request := permuted.values () request

end RelationalFoundations.FiniteRuleCoordinatesTests

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.homogeneous_all
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.heterogeneous_all
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.higher_universe
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.thirteen_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.seven_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.thirteen_ordered_dependencies
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.seven_ordered_dependencies
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.all_resumed_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.all_composed_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.real_resumed_coordinates
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.native_homogeneous_reprise
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.native_heterogeneous_reprise
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.swap
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.permuted
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.permuted_changes_identity
#print axioms RelationalFoundations.FiniteRuleCoordinatesTests.values_still_agree
/- AXIOM_AUDIT_END -/
