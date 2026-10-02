import ExactTypeTransport
import RelationalPerimeter.Computation.ConstitutiveSearch.ConstructivePrelude

/-!
# General extensive families constituted by dependent relational roles

This module defines the general class used by the complexity theorem.  A stage
is indexed by the state it receives and the state it produces.  Its role and
occurrences are connected by primitive source, formation, target, and
provenance relations with positive witnesses.  The global extensive carrier is
then derived from a dependent history of such stages; no global frontier,
arity list, or width formula is supplied by the family.
-/

namespace ConstitutiveSearch
namespace RelationalExtensive


/--
One relational opening.  Positions and occurrences remain distinct.  The
stage realizes every structural position by an occurrence, proves the exact
formation and provenance agreements, and supplies the two inverse laws before
any frontier or width is derived.
-/
structure RelationalOpeningStage
    (State : Type) (source next : State) where
  Role : Type
  Position : Type
  Occurrence : Type
  Provenance : Type
  SourceRelation : State → Role → Type
  FormationRelation : Role → Occurrence → Type
  TargetRelation : Role → State → Type
  ProvenanceRelation : Provenance → Role → Occurrence → Type
  role : Role
  provenance : Provenance
  sourceWitness : SourceRelation source role
  targetWitness : TargetRelation role next
  positionDecEq : DecidableEq Position
  positionFrontier : List Position
  positionComplete : (position : Position) → position ∈ positionFrontier
  positionNodup : positionFrontier.Nodup
  realize : Position → Occurrence
  classify : Occurrence → Position
  realize_classify : (occurrence : Occurrence) →
    realize (classify occurrence) = occurrence
  classify_realize : (position : Position) →
    classify (realize position) = position
  formationAgreement : (position : Position) →
    FormationRelation role (realize position)
  provenanceAgreement : (position : Position) →
    ProvenanceRelation provenance role (realize position)

/--
The exact transport belonging to a relational opening.  It is formed before
the occurrence frontier: positions and occurrences are independently typed,
and the two inverse laws record their exact realized agreement.
-/
def RelationalOpeningStage.positionOccurrenceTransport
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    RelationalFoundations.ExactTransport stage.Position stage.Occurrence :=
  { forward := stage.realize
    backward := stage.classify
    forwardBackward := stage.classify_realize
    backwardForward := stage.realize_classify }

/-- Dependent history: the tail starts at the exact state produced by its head. -/
inductive DependentRelationalRoleHistory
    (State : Type) : State → Nat → Type 1 where
  | nil (state : State) : DependentRelationalRoleHistory State state 0
  | step {source next : State} {count : Nat}
      (head : RelationalOpeningStage State source next)
      (tail : DependentRelationalRoleHistory State next count) :
      DependentRelationalRoleHistory State source (count + 1)


/-- Recover a formation witness for an arbitrary realized occurrence. -/
def RelationalOpeningStage.formationAt
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (occurrence : stage.Occurrence) :
    stage.FormationRelation stage.role occurrence := by
  have witness := stage.formationAgreement (stage.classify occurrence)
  rw [stage.realize_classify occurrence] at witness
  exact witness

/-- Recover provenance through the exact realization, not a position copy. -/
def RelationalOpeningStage.provenanceAt
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (occurrence : stage.Occurrence) :
    stage.ProvenanceRelation stage.provenance stage.role occurrence := by
  have witness := stage.provenanceAgreement (stage.classify occurrence)
  rw [stage.realize_classify occurrence] at witness
  exact witness

/--
A constituted identity carries its actual realization and all four positive
witnesses. Exactness pins those Type-valued witnesses to the canonical witnesses
of this stage; their possible multiplicity therefore does not change width.
No position is substituted for the realized occurrence.
-/
structure RelationallyConstitutedOccurrence
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) : Type where
  private mk ::
  realized : stage.Occurrence
  sourceWitness : stage.SourceRelation source stage.role
  sourceWitnessExact : sourceWitness = stage.sourceWitness
  formationWitness : stage.FormationRelation stage.role realized
  formationWitnessExact : formationWitness = stage.formationAt realized
  targetWitness : stage.TargetRelation stage.role next
  targetWitnessExact : targetWitness = stage.targetWitness
  provenanceWitness :
    stage.ProvenanceRelation stage.provenance stage.role realized
  provenanceWitnessExact : provenanceWitness = stage.provenanceAt realized

/-- Constitute an already realized occurrence with its canonical witnesses. -/
def constituteRealizedOccurrence
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (occurrence : stage.Occurrence) : RelationallyConstitutedOccurrence stage :=
  { realized := occurrence
    sourceWitness := stage.sourceWitness
    sourceWitnessExact := rfl
    formationWitness := stage.formationAt occurrence
    formationWitnessExact := rfl
    targetWitness := stage.targetWitness
    targetWitnessExact := rfl
    provenanceWitness := stage.provenanceAt occurrence
    provenanceWitnessExact := rfl }

/-- Classify the actual realization to recover its historical position. -/
def RelationallyConstitutedOccurrence.position
    {State : Type} {source next : State}
    {stage : RelationalOpeningStage State source next}
    (identity : RelationallyConstitutedOccurrence stage) : stage.Position :=
  stage.classify identity.realized

/-- Realization precedes the construction of the witnessed identity. -/
def relationallyConstitutedOccurrence
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (position : stage.Position) : RelationallyConstitutedOccurrence stage :=
  constituteRealizedOccurrence stage (stage.realize position)

/-- Canonical witnesses make reconstitution exact without an extra quotient. -/
theorem RelationallyConstitutedOccurrence.reconstitute
    {State : Type} {source next : State}
    {stage : RelationalOpeningStage State source next}
    (identity : RelationallyConstitutedOccurrence stage) :
    constituteRealizedOccurrence stage identity.realized = identity := by
  rcases identity with
    ⟨value, sw, swExact, fw, fwExact, tw, twExact, pw, pwExact⟩
  cases swExact
  cases fwExact
  cases twExact
  cases pwExact
  rfl

/-- This return law uses the classification-realization law of the stage. -/
theorem relationallyConstitutedOccurrence_position
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (position : stage.Position) :
    (relationallyConstitutedOccurrence stage position).position = position :=
  stage.classify_realize position

/-- This return law uses actual realization and canonical witness exactness. -/
theorem relationallyConstitutedOccurrence_roundTrip
    {State : Type} {source next : State}
    {stage : RelationalOpeningStage State source next}
    (identity : RelationallyConstitutedOccurrence stage) :
    relationallyConstitutedOccurrence stage identity.position = identity := by
  change constituteRealizedOccurrence stage
    (stage.realize (stage.classify identity.realized)) = identity
  rw [stage.realize_classify identity.realized]
  exact identity.reconstitute

/-- Exact incorporation of actual occurrences into witnessed identities. -/
def RelationalOpeningStage.constitutedOccurrenceTransport
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    RelationalFoundations.ExactTransport stage.Occurrence (RelationallyConstitutedOccurrence stage) :=
  { forward := constituteRealizedOccurrence stage
    backward := RelationallyConstitutedOccurrence.realized
    forwardBackward := fun _ => rfl
    backwardForward := RelationallyConstitutedOccurrence.reconstitute }

/-- Recover the formation witness carried by this particular identity. -/
def RelationalOpeningStage.formationWitness
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (identity : RelationallyConstitutedOccurrence stage) :
    stage.FormationRelation stage.role identity.realized :=
  identity.formationWitness

/-- Recover the provenance witness carried by the same identity. -/
def RelationalOpeningStage.provenanceWitness
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (identity : RelationallyConstitutedOccurrence stage) :
    stage.ProvenanceRelation stage.provenance stage.role identity.realized :=
  identity.provenanceWitness

/-- Equality is inherited through the exact realized occurrence transport. -/
def relationallyConstitutedOccurrenceDecEq
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    DecidableEq (RelationallyConstitutedOccurrence stage) :=
  fun left right =>
    match stage.positionDecEq left.position right.position with
    | isTrue same => isTrue (by
        calc
          left = relationallyConstitutedOccurrence stage left.position :=
            (relationallyConstitutedOccurrence_roundTrip left).symm
          _ = relationallyConstitutedOccurrence stage right.position :=
            congrArg (relationallyConstitutedOccurrence stage) same
          _ = right := relationallyConstitutedOccurrence_roundTrip right)
    | isFalse different =>
        isFalse (fun same => different
          (congrArg RelationallyConstitutedOccurrence.position same))

/-- A profile of identities constituted at every relational role. -/
def RelationalOccurrenceProfile :
    {State : Type} → {source : State} → {count : Nat} →
      DependentRelationalRoleHistory State source count → Type
  | _, _, _, .nil _ => Unit
  | _, _, _, .step head tail =>
      RelationallyConstitutedOccurrence head × RelationalOccurrenceProfile tail

/-- Position profile kept distinct from its realized occurrence profile. -/
def RelationalPositionProfile :
    {State : Type} → {source : State} → {count : Nat} →
      DependentRelationalRoleHistory State source count → Type
  | _, _, _, .nil _ => Unit
  | _, _, _, .step head tail =>
      head.Position × RelationalPositionProfile tail

/-- Pointwise realization of a complete relational position profile. -/
def relationalPositionToOccurrenceProfile :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      RelationalPositionProfile history → RelationalOccurrenceProfile history
  | _, _, _, .nil _, profile => by cases profile; exact ()
  | _, _, _, .step head tail, profile =>
      (relationallyConstitutedOccurrence head profile.1,
        relationalPositionToOccurrenceProfile tail profile.2)

/-- Pointwise classification of a complete relational occurrence profile. -/
def relationalOccurrenceToPositionProfile :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      RelationalOccurrenceProfile history → RelationalPositionProfile history
  | _, _, _, .nil _, profile => by cases profile; exact ()
  | _, _, _, .step head tail, profile =>
      (profile.1.position,
        relationalOccurrenceToPositionProfile tail profile.2)

theorem relationalPositionProfile_roundTrip :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      (profile : RelationalPositionProfile history) →
      relationalOccurrenceToPositionProfile history
          (relationalPositionToOccurrenceProfile history profile) = profile
  | _, _, _, .nil _, profile => by cases profile; rfl
  | _, _, _, .step head tail, profile => by
      exact Prod.ext (head.classify_realize profile.1)
        (relationalPositionProfile_roundTrip tail profile.2)

theorem relationalOccurrenceProfile_roundTrip :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      (profile : RelationalOccurrenceProfile history) →
      relationalPositionToOccurrenceProfile history
          (relationalOccurrenceToPositionProfile history profile) = profile
  | _, _, _, .nil _, profile => by cases profile; rfl
  | _, _, _, .step head tail, profile => by
      exact Prod.ext (relationallyConstitutedOccurrence_roundTrip profile.1)
        (relationalOccurrenceProfile_roundTrip tail profile.2)

/-- Exact history-level transport, constructed before any numeric readout. -/
def relationalProfileTransport
    {State : Type} {source : State} {count : Nat}
    (history : DependentRelationalRoleHistory State source count) :
    RelationalFoundations.ExactTransport
      (RelationalPositionProfile history)
      (RelationalOccurrenceProfile history) :=
  { forward := relationalPositionToOccurrenceProfile history
    backward := relationalOccurrenceToPositionProfile history
    forwardBackward := relationalPositionProfile_roundTrip history
    backwardForward := relationalOccurrenceProfile_roundTrip history }

/-- Mapping preserves list membership. -/
theorem relational_mem_map {α β : Type} (map : α → β) {value : α} :
    ∀ {values : List α}, value ∈ values → map value ∈ values.map map
  | _ :: _, .head _ => .head _
  | _ :: _, .tail _ prior => .tail _ (relational_mem_map map prior)

/-- Membership in a mapped list has a constructive preimage. -/
theorem relational_mem_map_preimage {α β : Type} (map : α → β) {target : β} :
    ∀ {values : List α}, target ∈ values.map map →
      ∃ source, source ∈ values ∧ map source = target
  | _ :: _, .head _ => ⟨_, .head _, rfl⟩
  | _ :: _, .tail _ prior =>
      let ⟨source, sourceMember, sourceExact⟩ :=
        relational_mem_map_preimage map prior
      ⟨source, .tail _ sourceMember, sourceExact⟩

/-- An injective map preserves duplicate-freeness. -/
theorem relational_nodup_map
    {α β : Type} (map : α → β)
    (injective : Function.Injective map) :
    ∀ {values : List α}, values.Nodup → (values.map map).Nodup
  | [], .nil => .nil
  | _ :: _, .cons headFresh tailNodup =>
      .cons
        (fun _mapped mappedMember same =>
          let ⟨source, sourceMember, sourceExact⟩ :=
            relational_mem_map_preimage map mappedMember
          headFresh source sourceMember
            (injective (Eq.trans same sourceExact.symm)))
        (relational_nodup_map map injective tailNodup)

/-- Cartesian frontier, defined without replacing occurrences by indices. -/
def productFrontier {Head Tail : Type} :
    List Head → List Tail → List (Head × Tail)
  | [], _ => []
  | head :: rest, tail =>
      tail.map (fun suffix => (head, suffix)) ++ productFrontier rest tail

theorem relational_mem_append_cases {α : Type} {value : α} :
    ∀ {left right : List α}, value ∈ left ++ right →
      value ∈ left ∨ value ∈ right
  | [], _, prior => Or.inr prior
  | _ :: _, _, .head _ => Or.inl (.head _)
  | _ :: tail, _, .tail _ prior =>
      match relational_mem_append_cases (left := tail) prior with
      | .inl inTail => .inl (.tail _ inTail)
      | .inr inRight => .inr inRight

theorem relational_nodup_append {α : Type} :
    ∀ {left right : List α},
      left.Nodup → right.Nodup →
      (∀ leftValue, leftValue ∈ left →
        ∀ rightValue, rightValue ∈ right → leftValue ≠ rightValue) →
      (left ++ right).Nodup
  | [], _, .nil, rightNodup, _ => rightNodup
  | head :: _, _, .cons headFresh tailNodup, rightNodup, disjoint =>
      .cons
        (fun value valueMember same =>
          match relational_mem_append_cases valueMember with
          | .inl inTail => headFresh value inTail same
          | .inr inRight => disjoint head (.head _) value inRight same)
        (relational_nodup_append tailNodup rightNodup
          (fun leftValue inTail rightValue inRight =>
            disjoint leftValue (.tail _ inTail) rightValue inRight))

theorem relational_length_map {α β : Type} (map : α → β) :
    ∀ values : List α, (values.map map).length = values.length
  | [] => rfl
  | _ :: tail => congrArg Nat.succ (relational_length_map map tail)

theorem relational_zero_add : ∀ value : Nat, 0 + value = value
  | 0 => rfl
  | value + 1 => congrArg Nat.succ (relational_zero_add value)

theorem relational_succ_add (left : Nat) :
    ∀ right : Nat, Nat.succ left + right = Nat.succ (left + right)
  | 0 => rfl
  | right + 1 => congrArg Nat.succ (relational_succ_add left right)

theorem relational_length_append {α : Type} :
    ∀ left right : List α,
      (left ++ right).length = left.length + right.length
  | [], right => (relational_zero_add right.length).symm
  | _ :: tail, right => Eq.trans
      (congrArg Nat.succ (relational_length_append tail right))
      (relational_succ_add tail.length right.length).symm

theorem productFrontier_complete
    {Head Tail : Type} {head : Head} {tail : Tail} :
    ∀ {heads : List Head} {tails : List Tail},
      head ∈ heads → tail ∈ tails →
      (head, tail) ∈ productFrontier heads tails
  | _ :: _, _, .head _, tailMember => by
      apply List.mem_append_left
      exact relational_mem_map (fun suffix => (head, suffix)) tailMember
  | _ :: rest, tails, .tail _ prior, tailMember => by
      apply List.mem_append_right
      exact productFrontier_complete prior tailMember

theorem productFrontier_length {Head Tail : Type} :
    ∀ (heads : List Head) (tails : List Tail),
      (productFrontier heads tails).length = heads.length * tails.length
  | [], tails => (Nat.zero_mul tails.length).symm
  | _ :: rest, tails => by
      rw [productFrontier, relational_length_append, relational_length_map,
        productFrontier_length rest tails, List.length_cons, Nat.succ_mul]
      exact Nat.add_comm _ _

theorem fst_mem_of_mem_productFrontier
    {Head Tail : Type} {value : Head × Tail} :
    ∀ {heads : List Head} {tails : List Tail},
      value ∈ productFrontier heads tails → value.1 ∈ heads
  | [], _, member => by cases member
  | head :: rest, tails, member => by
      rcases relational_mem_append_cases member with inFirst | inLater
      · rcases relational_mem_map_preimage
            (fun suffix => (head, suffix)) inFirst with
          ⟨_, _, exactPair⟩
        exact exactPair ▸ .head _
      · exact .tail _ (fst_mem_of_mem_productFrontier inLater)

theorem productFrontier_nodup
    {Head Tail : Type}
    [DecidableEq Head] [DecidableEq Tail] :
    ∀ {heads : List Head} {tails : List Tail},
      heads.Nodup → tails.Nodup →
      (productFrontier heads tails).Nodup
  | [], _, .nil, tailNodup => by
      exact .nil
  | head :: rest, tails, .cons headFresh restNodup, tailNodup => by
      have mappedNodup :
          (tails.map (fun suffix => (head, suffix))).Nodup :=
        relational_nodup_map
          (fun suffix => (head, suffix))
          (fun {_left _right} same => congrArg Prod.snd same)
          tailNodup
      have restProductNodup : (productFrontier rest tails).Nodup :=
        productFrontier_nodup restNodup tailNodup
      exact relational_nodup_append mappedNodup restProductNodup
        (fun leftValue inMapped rightValue inRest same => by
          rcases relational_mem_map_preimage
              (fun suffix => (head, suffix)) inMapped with
            ⟨leftTail, _leftMember, leftExact⟩
          have restHeadMember : rightValue.1 ∈ rest :=
            fst_mem_of_mem_productFrontier inRest
          have headSame : head = rightValue.1 := by
            exact congrArg Prod.fst (Eq.trans leftExact same)
          exact headFresh rightValue.1 restHeadMember headSame)

/-- The local frontier after formation and provenance have constituted it. -/
def relationallyConstitutedOccurrenceFrontier
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    List (RelationallyConstitutedOccurrence stage) :=
  stage.positionFrontier.map (relationallyConstitutedOccurrence stage)

theorem relationallyConstitutedOccurrenceFrontier_complete
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next)
    (identity : RelationallyConstitutedOccurrence stage) :
    identity ∈ relationallyConstitutedOccurrenceFrontier stage := by
  have realizedMember := relational_mem_map
    (relationallyConstitutedOccurrence stage)
    (stage.positionComplete identity.position)
  exact (relationallyConstitutedOccurrence_roundTrip identity) ▸ realizedMember

theorem relationallyConstitutedOccurrenceFrontier_nodup
    {State : Type} {source next : State}
    (stage : RelationalOpeningStage State source next) :
    (relationallyConstitutedOccurrenceFrontier stage).Nodup :=
  relational_nodup_map (relationallyConstitutedOccurrence stage)
    (fun {left right} same => by
      have classified := congrArg RelationallyConstitutedOccurrence.position same
      exact Eq.trans (stage.classify_realize left).symm
        (Eq.trans classified (stage.classify_realize right)))
    stage.positionNodup

/-- The unique global frontier of relationally constituted identities. -/
def relationalProfileFrontier :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      List (RelationalOccurrenceProfile history)
  | _, _, _, .nil _ => [()]
  | _, _, _, .step head tail =>
      productFrontier (relationallyConstitutedOccurrenceFrontier head)
        (relationalProfileFrontier tail)

theorem relationalProfileFrontier_complete :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      (profile : RelationalOccurrenceProfile history) →
      profile ∈ relationalProfileFrontier history
  | _, _, _, .nil _, profile => by cases profile; exact .head _
  | _, _, _, .step head tail, profile =>
      productFrontier_complete
        (relationallyConstitutedOccurrenceFrontier_complete head profile.1)
        (relationalProfileFrontier_complete tail profile.2)

/-- Constructive equality decision on constituted relational profiles. -/
def relationalOccurrenceProfileDecEq :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      DecidableEq (RelationalOccurrenceProfile history)
  | _, _, _, .nil _ => fun left right =>
      match left, right with
      | (), () => isTrue rfl
  | _, _, _, .step head tail => fun left right =>
      match relationallyConstitutedOccurrenceDecEq head left.1 right.1 with
      | isFalse headDifferent =>
          isFalse (fun same => headDifferent (congrArg Prod.fst same))
      | isTrue headSame =>
          match relationalOccurrenceProfileDecEq tail left.2 right.2 with
          | isFalse tailDifferent =>
              isFalse (fun same => tailDifferent (congrArg Prod.snd same))
          | isTrue tailSame => isTrue (Prod.ext headSame tailSame)

theorem relationalProfileFrontier_nodup :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      (relationalProfileFrontier history).Nodup
  | _, _, _, .nil _ =>
      .cons (fun _ impossible _ => nomatch impossible) .nil
  | _, _, _, .step head tail => by
      letI : DecidableEq (RelationallyConstitutedOccurrence head) :=
        relationallyConstitutedOccurrenceDecEq head
      letI : DecidableEq (RelationalOccurrenceProfile tail) :=
        relationalOccurrenceProfileDecEq tail
      exact productFrontier_nodup
        (relationallyConstitutedOccurrenceFrontier_nodup head)
        (relationalProfileFrontier_nodup tail)

/-- Arity list read from the already realized local occurrence frontiers. -/
def relationalHistoryArities :
    {State : Type} → {source : State} → {count : Nat} →
      DependentRelationalRoleHistory State source count → List Nat
  | _, _, _, .nil _ => []
  | _, _, _, .step head tail =>
      (relationallyConstitutedOccurrenceFrontier head).length ::
        relationalHistoryArities tail

/-- Width is a readout of the derived global profile frontier. -/
def relationalProfileWidth
    {State : Type} {source : State} {count : Nat}
    (history : DependentRelationalRoleHistory State source count) : Nat :=
  (relationalProfileFrontier history).length

theorem relationalProfileWidth_eq_arityProduct :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      relationalProfileWidth history = (relationalHistoryArities history).prod
  | _, _, _, .nil _ => rfl
  | _, _, _, .step head tail => by
      change
        (productFrontier (relationallyConstitutedOccurrenceFrontier head)
          (relationalProfileFrontier tail)).length =
        (relationallyConstitutedOccurrenceFrontier head).length *
          (relationalHistoryArities tail).prod
      calc
        (productFrontier (relationallyConstitutedOccurrenceFrontier head)
            (relationalProfileFrontier tail)).length =
            (relationallyConstitutedOccurrenceFrontier head).length *
              (relationalProfileFrontier tail).length :=
          productFrontier_length _ _
        _ = (relationallyConstitutedOccurrenceFrontier head).length *
              (relationalHistoryArities tail).prod :=
          congrArg
            (fun width =>
              (relationallyConstitutedOccurrenceFrontier head).length * width)
            (relationalProfileWidth_eq_arityProduct tail)

/-- Every realized local opening has one fixed arity. -/
def UniformLocalArity :
    {State : Type} → {source : State} → {count : Nat} →
      DependentRelationalRoleHistory State source count → Nat → Prop
  | _, _, _, .nil _, _ => True
  | _, _, _, .step head tail, arity =>
      (relationallyConstitutedOccurrenceFrontier head).length = arity ∧
        UniformLocalArity tail arity

/-- Every realized local opening has at least two occurrences. -/
def AtLeastBinaryLocalArity :
    {State : Type} → {source : State} → {count : Nat} →
      DependentRelationalRoleHistory State source count → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .step head tail =>
      2 ≤ (relationallyConstitutedOccurrenceFrontier head).length ∧
        AtLeastBinaryLocalArity tail

theorem uniformLocalArity_width :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      (arity : Nat) → UniformLocalArity history arity →
      relationalProfileWidth history = arity ^ count
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .step head tail, arity, uniform => by
      change
        (productFrontier (relationallyConstitutedOccurrenceFrontier head)
          (relationalProfileFrontier tail)).length = arity ^ (_ + 1)
      calc
        (productFrontier (relationallyConstitutedOccurrenceFrontier head)
            (relationalProfileFrontier tail)).length =
            (relationallyConstitutedOccurrenceFrontier head).length *
              relationalProfileWidth tail := productFrontier_length _ _
        _ = arity * (arity ^ _) := by
          rw [uniform.1, uniformLocalArity_width tail arity uniform.2]
        _ = arity ^ (_ + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm]

theorem atLeastBinaryLocalArity_width_lowerBound :
    {State : Type} → {source : State} → {count : Nat} →
      (history : DependentRelationalRoleHistory State source count) →
      AtLeastBinaryLocalArity history →
      2 ^ count ≤ relationalProfileWidth history
  | _, _, _, .nil _, _ => Nat.le_refl 1
  | _, _, _, .step head tail, binary => by
      have tailBound := atLeastBinaryLocalArity_width_lowerBound tail binary.2
      change
        2 ^ (_ + 1) ≤
          (productFrontier (relationallyConstitutedOccurrenceFrontier head)
            (relationalProfileFrontier tail)).length
      rw [productFrontier_length, Nat.pow_succ]
      calc
        2 ^ _ * 2 = 2 * 2 ^ _ := Nat.mul_comm _ _
        _ ≤ (relationallyConstitutedOccurrenceFrontier head).length *
              relationalProfileWidth tail := by
          rw [relationallyConstitutedOccurrenceFrontier]
          exact Nat.mul_le_mul binary.1 tailBound

end RelationalExtensive
end ConstitutiveSearch

/- AXIOM_AUDIT_BEGIN -/
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage.formationAt
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage.provenanceAt
#print axioms ConstitutiveSearch.RelationalExtensive.constituteRealizedOccurrence
#print axioms ConstitutiveSearch.RelationalExtensive.RelationallyConstitutedOccurrence.reconstitute
#print axioms ConstitutiveSearch.RelationalExtensive.relationallyConstitutedOccurrence_position
#print axioms ConstitutiveSearch.RelationalExtensive.relationallyConstitutedOccurrence_roundTrip
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage.constitutedOccurrenceTransport
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage.positionOccurrenceTransport
#print axioms ConstitutiveSearch.RelationalExtensive.DependentRelationalRoleHistory
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOccurrenceProfile
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalPositionProfile
#print axioms ConstitutiveSearch.RelationalExtensive.relationalPositionToOccurrenceProfile
#print axioms ConstitutiveSearch.RelationalExtensive.relationalOccurrenceToPositionProfile
#print axioms ConstitutiveSearch.RelationalExtensive.relationalPositionProfile_roundTrip
#print axioms ConstitutiveSearch.RelationalExtensive.relationalOccurrenceProfile_roundTrip
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileTransport
#print axioms ConstitutiveSearch.RelationalExtensive.RelationallyConstitutedOccurrence
#print axioms ConstitutiveSearch.RelationalExtensive.RelationallyConstitutedOccurrence.position
#print axioms ConstitutiveSearch.RelationalExtensive.RelationallyConstitutedOccurrence.realized
#print axioms ConstitutiveSearch.RelationalExtensive.relationallyConstitutedOccurrence
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage.formationWitness
#print axioms ConstitutiveSearch.RelationalExtensive.RelationalOpeningStage.provenanceWitness
#print axioms ConstitutiveSearch.RelationalExtensive.relationallyConstitutedOccurrenceDecEq
#print axioms ConstitutiveSearch.RelationalExtensive.relationallyConstitutedOccurrenceFrontier
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFrontier
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFrontier_complete
#print axioms ConstitutiveSearch.RelationalExtensive.relationalOccurrenceProfileDecEq
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileFrontier_nodup
#print axioms ConstitutiveSearch.RelationalExtensive.relationalProfileWidth_eq_arityProduct
#print axioms ConstitutiveSearch.RelationalExtensive.UniformLocalArity
#print axioms ConstitutiveSearch.RelationalExtensive.AtLeastBinaryLocalArity
#print axioms ConstitutiveSearch.RelationalExtensive.uniformLocalArity_width
#print axioms ConstitutiveSearch.RelationalExtensive.atLeastBinaryLocalArity_width_lowerBound
/- AXIOM_AUDIT_END -/
