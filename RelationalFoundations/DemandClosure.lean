import RelationalFoundations.ExactTransport
set_option genInjectivity false

/-!
# Constructive closure of declared demands

`Tree` retains every declared prerequisite and its position, including repeated
prerequisites. `RankedSystem.build` constructs that tree from a locally checked
decrease. The rank is a termination measure, not a prescribed support size.

The theorem is relative to the declared prerequisites. A concrete semantic
application must identify all of its actual demands and construct its local
producer. Those obligations are not consequences of the generic theorem.
-/

namespace RelationalFoundations.DemandClosure
universe u v w

namespace FiniteList

/-- Positive membership transport, proved without extensionality axioms. -/
theorem mappedMember {A : Type u} {B : Type v} (f : A → B) {value : A} :
    {items : List A} → value ∈ items → f value ∈ items.map f
  | _, .head _ => .head _
  | _, .tail _ member => .tail _ (mappedMember f member)

theorem mapLength {A : Type u} {B : Type v} (f : A → B) (items : List A) :
    (items.map f).length = items.length := by
  induction items with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem appendLength {A : Type u} (first second : List A) :
    (first ++ second).length = first.length + second.length := by
  induction first with
  | nil => exact (Nat.zero_add _).symm
  | cons _ _ ih => exact (congrArg Nat.succ ih).trans (Nat.succ_add _ _).symm

theorem mapCompose {A : Type u} {B : Type v} {C : Type w} (first : A → B) (second : B → C) (items : List A) :
    (items.map first).map second = items.map (fun value => second (first value)) := by
  induction items with
  | nil => rfl
  | cons value rest ih => exact congrArg (List.cons (second (first value))) ih

theorem mapAgree {A : Type u} {B : Type v} (first second : A → B) (same : ∀ value, first value = second value)
    (items : List A) : items.map first = items.map second := by
  induction items with
  | nil => rfl
  | cons value rest ih =>
      exact (congrArg (fun head => head :: rest.map first) (same value)).trans
        (congrArg (List.cons (second value)) ih)

end FiniteList

mutual
  inductive Tree {Request : Type u} (requires : Request → List Request) : Request → Type u
    | node (request : Request) (children : Forest requires (requires request)) : Tree requires request

  inductive Forest {Request : Type u} (requires : Request → List Request) : List Request → Type u
    | nil : Forest requires []
    | cons {request : Request} {rest : List Request}
        (head : Tree requires request) (tail : Forest requires rest) : Forest requires (request :: rest)
end

namespace Forest
variable {Request : Type u} {requires : Request → List Request}

def fromProducer : (requests : List Request) →
    ((request : Request) → request ∈ requests → Tree requires request) → Forest requires requests
  | [], _ => .nil
  | request :: rest, produce =>
      .cons (produce request (.head _))
        (fromProducer rest (fun child member => produce child (.tail _ member)))

def get : {requests : List Request} → Forest requires requests →
    (index : Fin requests.length) → Tree requires (requests.get index)
  | _ :: _, .cons head _, ⟨0, _⟩ => head
  | _ :: _, .cons _ tail, ⟨n + 1, bound⟩ => get tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩
end Forest

/-- Finite branching and strict decrease are explicit sufficient conditions. -/
structure RankedSystem where
  Request : Type u
  requires : Request → List Request
  rank : Request → Nat
  decreases : ∀ request child, child ∈ requires request → rank child < rank request

namespace RankedSystem

def buildWithin (system : RankedSystem.{u}) :
    (bound : Nat) → (request : system.Request) → system.rank request < bound →
      Tree system.requires request
  | 0, _, impossible => False.elim (Nat.not_lt_zero _ impossible)
  | bound + 1, request, within =>
      .node request (Forest.fromProducer (system.requires request) (fun child member =>
        buildWithin system bound child
          (Nat.lt_of_lt_of_le (system.decreases request child member) (Nat.le_of_lt_succ within))))

/-- No external fuel or prescribed support cardinality is an argument. -/
def build (system : RankedSystem.{u}) (request : system.Request) : Tree system.requires request :=
  system.buildWithin (system.rank request + 1) request (Nat.lt_succ_self _)

def buildMany (system : RankedSystem.{u}) (requests : List system.Request) :
    Forest system.requires requests := Forest.fromProducer requests (fun request _ => system.build request)
end RankedSystem

mutual
  def Tree.size {Request : Type u} {requires : Request → List Request} :
      {request : Request} → Tree requires request → Nat
    | _, .node _ children => children.size + 1

  def Forest.size {Request : Type u} {requires : Request → List Request} :
      {requests : List Request} → Forest requires requests → Nat
    | _, .nil => 0
    | _, .cons head tail => head.size + tail.size
end

namespace Tree
variable {Request : Type u} {requires : Request → List Request}

theorem size_positive {request : Request} (tree : Tree requires request) : 0 < tree.size := by
  cases tree with
  | node _ children => exact Nat.zero_lt_succ _

/- Structural addresses individuate resources before numerical cardinalization. -/
mutual
  inductive Address : {request : Request} → Tree requires request → Type u
    | root {request : Request} {children : Forest requires (requires request)} : Address (.node request children)
    | child {request : Request} {children : Forest requires (requires request)} :
        ForestAddress children → Address (.node request children)

  inductive ForestAddress : {requests : List Request} → Forest requires requests → Type u
    | head {request : Request} {rest : List Request}
        {first : Tree requires request} {tail : Forest requires rest} :
        Address first → ForestAddress (.cons first tail)
    | tail {request : Request} {rest : List Request}
        {first : Tree requires request} {tail : Forest requires rest} :
        ForestAddress tail → ForestAddress (.cons first tail)
end

mutual
  def requestsAt : {request : Request} → (tree : Tree requires request) → Address tree → Request
    | _, .node request _, .root => request
    | _, .node _ children, .child address => forestRequestsAt children address

  def forestRequestsAt : {requests : List Request} → (forest : Forest requires requests) →
      ForestAddress forest → Request
    | _, .cons first _, .head address => requestsAt first address
    | _, .cons _ tail, .tail address => forestRequestsAt tail address
end

mutual
  def subtree : {request : Request} → (tree : Tree requires request) → Address tree →
      (request : Request) × Tree requires request
    | _, tree@(.node _ _), .root => ⟨_, tree⟩
    | _, .node _ children, .child address => forestSubtree children address

  def forestSubtree : {requests : List Request} → (forest : Forest requires requests) →
      ForestAddress forest → (request : Request) × Tree requires request
    | _, .cons first _, .head address => subtree first address
    | _, .cons _ tail, .tail address => forestSubtree tail address
end

mutual
  def addresses : {request : Request} → (tree : Tree requires request) → List (Address tree)
    | _, .node _ children => .root :: (forestAddresses children).map Address.child

  def forestAddresses : {requests : List Request} → (forest : Forest requires requests) → List (ForestAddress forest)
    | _, .nil => []
    | _, .cons first tail => (addresses first).map ForestAddress.head ++
        (forestAddresses tail).map ForestAddress.tail
end

mutual
  theorem addresses_complete : {request : Request} → (tree : Tree requires request) →
      (address : Address tree) → address ∈ addresses tree
    | _, .node _ _, .root => .head _
    | _, .node _ children, .child address =>
        List.mem_cons_of_mem _ (FiniteList.mappedMember Address.child (forestAddresses_complete children address))

  theorem forestAddresses_complete : {requests : List Request} → (forest : Forest requires requests) →
      (address : ForestAddress forest) → address ∈ forestAddresses forest
    | _, .cons first _, .head address =>
        List.mem_append_left _ (FiniteList.mappedMember ForestAddress.head (addresses_complete first address))
    | _, .cons _ tail, .tail address =>
        List.mem_append_right _ (FiniteList.mappedMember ForestAddress.tail (forestAddresses_complete tail address))
end

mutual
  theorem addresses_length : {request : Request} → (tree : Tree requires request) →
      (addresses tree).length = tree.size
    | _, .node _ children => by
        simp only [addresses, List.length_cons, FiniteList.mapLength, Tree.size]
        rw [forestAddresses_length children]

  theorem forestAddresses_length : {requests : List Request} → (forest : Forest requires requests) →
      (forestAddresses forest).length = forest.size
    | _, .nil => rfl
    | _, .cons first tail => by
        simp only [forestAddresses, FiniteList.appendLength, FiniteList.mapLength, Forest.size]
        rw [addresses_length first, forestAddresses_length tail]
end
end Tree

/-- A tuple retains each prerequisite position, even if request labels coincide. -/
inductive Values {Request : Type u} (Value : Request → Type v) : List Request → Type (max u v)
  | nil : Values Value []
  | cons {request : Request} {rest : List Request}
      (head : Value request) (tail : Values Value rest) : Values Value (request :: rest)

namespace Values
variable {Request : Type u} {Value : Request → Type v}

def All (Valid : (request : Request) → Value request → Prop) :
    {requests : List Request} → Values Value requests → Prop
  | _, .nil => True
  | _, .cons head tail => Valid _ head ∧ All Valid tail

def toList : {requests : List Request} → Values Value requests → List ((request : Request) × Value request)
  | _, .nil => []
  | _, .cons head tail => ⟨_, head⟩ :: toList tail
end Values

/-- This is a local rule producer, not a precomputed family of semantic witnesses. -/
structure LocalProducer {Request : Type u} (requires : Request → List Request) where
  Value : Request → Type (max u v)
  produce : (request : Request) → Values Value (requires request) → Value request

namespace LocalProducer
variable {Request : Type u} {requires : Request → List Request}

mutual
  def realize (producer : LocalProducer.{u,v} requires) :
      {request : Request} → Tree requires request → producer.Value request
    | _, .node request children => producer.produce request (realizeMany producer children)

  def realizeMany (producer : LocalProducer.{u,v} requires) :
      {requests : List Request} → Forest requires requests → Values producer.Value requests
    | _, .nil => .nil
    | _, .cons head tail => .cons (realize producer head) (realizeMany producer tail)
end

/-- The semantic predicate is declared independently of the construction. -/
structure Soundness (producer : LocalProducer.{u,v} requires) where
  Valid : (request : Request) → producer.Value request → Prop
  preserves : ∀ request inputs, Values.All Valid inputs → Valid request (producer.produce request inputs)

mutual
  theorem realize_valid (producer : LocalProducer.{u,v} requires) (sound : producer.Soundness) :
      {request : Request} → (tree : Tree requires request) → sound.Valid _ (producer.realize tree)
    | _, .node request children => sound.preserves request _ (realizeMany_valid producer sound children)

  theorem realizeMany_valid (producer : LocalProducer.{u,v} requires) (sound : producer.Soundness) :
      {requests : List Request} → (forest : Forest requires requests) →
        Values.All sound.Valid (producer.realizeMany forest)
    | _, .nil => True.intro
    | _, .cons head tail => ⟨realize_valid producer sound head, realizeMany_valid producer sound tail⟩
end
end LocalProducer

/-- A finite input can have a declared prerequisite loop with no closed tree. -/
def cyclicRequires (_ : Unit) : List Unit := [()]

theorem cyclic_tree_impossible : {request : Unit} → (tree : Tree cyclicRequires request) → False
  | _, .node _ (.cons first .nil) => cyclic_tree_impossible first
termination_by _ tree => tree.size
decreasing_by exact Nat.lt_succ_self _

end RelationalFoundations.DemandClosure
