/-!
# Constructive non-factorization through information-forgetting projections

The closure program needs a precise notion of information loss.

A property factors through a projection when it can be recovered solely from
the projected value. A value-valued observation factors through a projection
when one function of the projected value reproduces that observation exactly.
A total action factors through a projection when one projected action recovers
its result on every argument.

The generic separator theorems below are constructive:
* equal projections with opposite predicate truth values refute predicate
  factorization;
* equal projections with distinct observed values refute value factorization;
* equal projections with total actions that differ at one argument refute
  action factorization.

The last statement isolates the information-loss principle needed by the
operational-stability layer. The equality of projections is an explicit
hypothesis and is consumed by the proof; it need not be definitional.
-/

namespace ConstitutiveSearch

universe uA uB uC uX uY

/-- A predicate is recoverable from a projection alone. -/
def PredicateFactorsThrough
    {A B : Type}
    (project : A → B)
    (predicate : A → Prop) : Prop :=
  ∃ projectedPredicate : B → Prop,
    ∀ value : A,
      predicate value ↔
        projectedPredicate
          (project value)

/-- A value-valued observation is recoverable from a projection alone. -/
def ValueFactorsThrough
    {A B C : Type}
    (project : A → B)
    (observe : A → C) : Prop :=
  ∃ projectedObservation : B → C,
    ∀ value : A,
      projectedObservation
          (project value) =
        observe value

/-- A total action is recoverable from a projection alone. -/
def ActionFactorsThrough
    {A : Type uA}
    {B : Type uB}
    {X : Type uX}
    {Y : Type uY}
    (project : A → B)
    (action : A → X → Y) : Prop :=
  ∃ projectedAction : B → X → Y,
    ∀ value argument,
      projectedAction (project value) argument =
        action value argument

/--
A collision in a projection whose two preimages still induce different total
actions at one admissible argument.
-/
structure ActionProjectionCollision
    {A : Type uA}
    {B : Type uB}
    {X : Type uX}
    {Y : Type uY}
    (project : A → B)
    (action : A → X → Y) where
  first : A
  second : A
  sameProjection : project first = project second
  argument : X
  differentAction : action first argument ≠ action second argument

/-- A projection collision anchored at a specified first preimage.  The anchor
is an index of the witness type rather than a freely replaceable field. -/
structure AnchoredActionProjectionCollision
    {A : Type uA}
    {B : Type uB}
    {X : Type uX}
    {Y : Type uY}
    (project : A → B)
    (action : A → X → Y)
    (first : A) where
  second : A
  sameProjection : project first = project second
  argument : X
  differentAction : action first argument ≠ action second argument

/-- Forget only the fixed-anchor index after it has served to type the
collision witness. -/
def AnchoredActionProjectionCollision.toCollision
    {A : Type uA}
    {B : Type uB}
    {X : Type uX}
    {Y : Type uY}
    {project : A → B}
    {action : A → X → Y}
    {first : A}
    (collision : AnchoredActionProjectionCollision project action first) :
    ActionProjectionCollision project action :=
  { first := first
    second := collision.second
    sameProjection := collision.sameProjection
    argument := collision.argument
    differentAction := collision.differentAction }

/--
Two states with the same projection but different predicate truth values
constructively refute predicate factorization.
-/
theorem predicate_not_factors_of_same_projection
    {A B : Type}
    (project : A → B)
    (predicate : A → Prop)
    (first second : A)
    (sameProjection :
      project first =
        project second)
    (firstFalse :
      ¬ predicate first)
    (secondTrue :
      predicate second) :
    ¬
      PredicateFactorsThrough
        project
        predicate := by
  intro factors
  rcases factors with
    ⟨projectedPredicate, exactFactor⟩
  have secondProjected :
      projectedPredicate
        (project second) :=
    (exactFactor second).1
      secondTrue
  have firstProjected :
      projectedPredicate
        (project first) := by
    rw [sameProjection]
    exact secondProjected
  exact
    firstFalse
      ((exactFactor first).2
        firstProjected)

/--
Two states with the same projection but unequal observations constructively
refute value factorization.
-/
theorem value_not_factors_of_same_projection
    {A B C : Type}
    (project : A → B)
    (observe : A → C)
    (first second : A)
    (sameProjection :
      project first =
        project second)
    (different :
      observe first ≠
        observe second) :
    ¬
      ValueFactorsThrough
        project
        observe := by
  intro factors
  rcases factors with
    ⟨projectedObservation, exactFactor⟩
  apply different
  calc
    observe first
        =
      projectedObservation
        (project first) :=
          (exactFactor first).symm
    _ =
      projectedObservation
        (project second) := by
          rw [sameProjection]
    _ =
      observe second :=
        exactFactor second

/--
A projection collision with different total actions constructively refutes
factorization of that action through the projection.

The middle equality necessarily consumes `collision.sameProjection`; therefore
the theorem applies equally when the projected values are only propositionally
equal and not definitionally identical.
-/
theorem action_not_factors_of_projection_collision
    {A : Type uA}
    {B : Type uB}
    {X : Type uX}
    {Y : Type uY}
    {project : A → B}
    {action : A → X → Y}
    (collision : ActionProjectionCollision project action) :
    ¬ ActionFactorsThrough project action := by
  intro factors
  rcases factors with
    ⟨projectedAction, exactFactor⟩
  apply collision.differentAction
  calc
    action collision.first collision.argument =
        projectedAction (project collision.first) collision.argument :=
      (exactFactor collision.first collision.argument).symm
    _ =
        projectedAction (project collision.second) collision.argument := by
      rw [collision.sameProjection]
    _ = action collision.second collision.argument :=
      exactFactor collision.second collision.argument

/-- An anchored collision refutes factorization while retaining the designated
first preimage in the witness type consumed by the proof. -/
theorem action_not_factors_of_anchored_projection_collision
    {A : Type uA}
    {B : Type uB}
    {X : Type uX}
    {Y : Type uY}
    {project : A → B}
    {action : A → X → Y}
    {first : A}
    (collision : AnchoredActionProjectionCollision project action first) :
    ¬ ActionFactorsThrough project action :=
  action_not_factors_of_projection_collision collision.toCollision

end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.PredicateFactorsThrough
#print axioms ConstitutiveSearch.ValueFactorsThrough
#print axioms ConstitutiveSearch.ActionFactorsThrough
#print axioms ConstitutiveSearch.ActionProjectionCollision
#print axioms ConstitutiveSearch.AnchoredActionProjectionCollision
#print axioms ConstitutiveSearch.AnchoredActionProjectionCollision.toCollision
#print axioms ConstitutiveSearch.predicate_not_factors_of_same_projection
#print axioms ConstitutiveSearch.value_not_factors_of_same_projection
#print axioms ConstitutiveSearch.action_not_factors_of_projection_collision
#print axioms ConstitutiveSearch.action_not_factors_of_anchored_projection_collision
/- AXIOM_AUDIT_END -/
