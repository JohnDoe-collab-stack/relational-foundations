import RelationalFoundations.ResourceGraph
set_option genInjectivity false

/-!
# Constructed heterogeneous resources and kind-preserving historical references

This extends the resource graph to two genuine value types. References are
indexed by the kind they read. Every producer is implemented, and its inputs
belong to the support already constructed. The historical and enumeration
proofs reuse the constructive list tools of the existing resource graph.
-/

namespace RelationalFoundations.TypedResources
open DemandClosure ResourceGraph

inductive Kind where
  | number
  | truth

def Value : Kind → Type
  | .number => Nat
  | .truth => Bool

inductive Ref : List Kind → Kind → Type where
  | head {kind : Kind} {rest : List Kind} : Ref (kind :: rest) kind
  | old {kind added : Kind} {rest : List Kind} : Ref rest kind → Ref (added :: rest) kind

inductive AnyRef (context : List Kind) where
  | number (ref : Ref context .number)
  | truth (ref : Ref context .truth)

namespace AnyRef
def pack {context : List Kind} : (kind : Kind) → Ref context kind → AnyRef context
  | .number, ref => .number ref
  | .truth, ref => .truth ref

def map {first second : List Kind} (embed : ∀ kind, Ref first kind → Ref second kind) :
    AnyRef first → AnyRef second
  | .number ref => .number (embed .number ref)
  | .truth ref => .truth (embed .truth ref)

def old {added : Kind} {context : List Kind} : AnyRef context → AnyRef (added :: context) :=
  map (fun _ => Ref.old)

theorem map_comp {a b c : List Kind} (one : ∀ kind, Ref a kind → Ref b kind)
    (two : ∀ kind, Ref b kind → Ref c kind) (ref : AnyRef a) :
    map two (map one ref) = map (fun kind ref => two kind (one kind ref)) ref := by
  cases ref <;> rfl

theorem pack_map {a b : List Kind} (embed : ∀ kind, Ref a kind → Ref b kind)
    (kind : Kind) (ref : Ref a kind) : map embed (pack kind ref) = pack kind (embed kind ref) := by
  cases kind <;> rfl

theorem map_list_id {context : List Kind} (refs : List (AnyRef context)) :
    refs.map (map (fun _ ref => ref)) = refs := by
  induction refs with
  | nil => rfl
  | cons ref rest ih => cases ref <;> exact congrArg (List.cons _) ih
end AnyRef

def test (number : Nat) : Bool := number == 0
def adjust (flag : Bool) (number : Nat) : Nat := if flag then number + 1 else number.pred

/-- Producers with typed arguments and genuinely different result types. -/
inductive Operation (context : List Kind) : Kind → Type where
  | literal (number : Nat) : Operation context .number
  | test (number : Ref context .number) : Operation context .truth
  | adjust (flag : Ref context .truth) (number : Ref context .number) : Operation context .number
  | reuse {kind : Kind} (ref : Ref context kind) : Operation context kind

namespace Operation
def eval {context : List Kind} (read : ∀ kind, Ref context kind → Value kind) :
    {kind : Kind} → Operation context kind → Value kind
  | _, .literal number => number
  | _, .test number => TypedResources.test (read .number number)
  | _, .adjust flag number => TypedResources.adjust (read .truth flag) (read .number number)
  | kind, .reuse ref => read kind ref

def map {a b : List Kind} (embed : ∀ kind, Ref a kind → Ref b kind) :
    {kind : Kind} → Operation a kind → Operation b kind
  | _, .literal number => .literal number
  | _, .test number => .test (embed .number number)
  | _, .adjust flag number => .adjust (embed .truth flag) (embed .number number)
  | kind, .reuse ref => .reuse (embed kind ref)

def inputs {context : List Kind} : {kind : Kind} → Operation context kind → List (AnyRef context)
  | _, .literal _ => []
  | _, .test number => [.number number]
  | _, .adjust flag number => [.truth flag, .number number]
  | kind, .reuse ref => [AnyRef.pack kind ref]

theorem map_comp {a b c : List Kind} (one : ∀ kind, Ref a kind → Ref b kind)
    (two : ∀ kind, Ref b kind → Ref c kind) {kind : Kind} (node : Operation a kind) :
    (node.map one).map two = node.map (fun kind ref => two kind (one kind ref)) := by
  cases node <;> rfl

theorem map_id {context : List Kind} {kind : Kind} (node : Operation context kind) :
    node.map (fun _ ref => ref) = node := by
  cases node <;> rfl

theorem inputs_map {a b : List Kind} (embed : ∀ kind, Ref a kind → Ref b kind)
    {kind : Kind} (node : Operation a kind) :
    (node.map embed).inputs = node.inputs.map (AnyRef.map embed) := by
  cases node with
  | literal _ => rfl
  | test _ => rfl
  | adjust _ _ => rfl
  | reuse ref => exact congrArg (fun ref => [ref]) (AnyRef.pack_map embed _ ref).symm

theorem eval_map {a b : List Kind} (embed : ∀ kind, Ref a kind → Ref b kind)
    (read : ∀ kind, Ref b kind → Value kind) {kind : Kind} (node : Operation a kind) :
    (node.map embed).eval read = node.eval (fun kind ref => read kind (embed kind ref)) := by
  cases node <;> rfl
end Operation

inductive Support : List Kind → Type where
  | empty : Support []
  | push {context : List Kind} {kind : Kind} : Support context → Operation context kind → Support (kind :: context)

namespace Support
def read : {context : List Kind} → Support context → (kind : Kind) → Ref context kind → Value kind
  | _, .push previous operation, _, .head => operation.eval (read previous)
  | _, .push previous _, kind, .old ref => read previous kind ref

def nodeAt : {context : List Kind} → Support context → (kind : Kind) → Ref context kind → Operation context kind
  | _, .push _ operation, _, .head => operation.map (fun _ => Ref.old)
  | _, .push previous _, kind, .old ref => (nodeAt previous kind ref).map (fun _ => Ref.old)

def dependencies {context : List Kind} (support : Support context) : AnyRef context → List (AnyRef context)
  | .number ref => (support.nodeAt .number ref).inputs
  | .truth ref => (support.nodeAt .truth ref).inputs

def Depends {context : List Kind} (support : Support context) (parent child : AnyRef context) : Prop :=
  child ∈ support.dependencies parent

theorem read_correct : {context : List Kind} → (support : Support context) →
    (kind : Kind) → (ref : Ref context kind) →
    support.read kind ref = (support.nodeAt kind ref).eval support.read
  | _, .push previous operation, _, .head =>
      (Operation.eval_map (fun _ => Ref.old) (read (.push previous operation)) operation).symm
  | _, .push previous operation, kind, .old ref =>
      (read_correct previous kind ref).trans
        (Operation.eval_map (fun _ => Ref.old) (read (.push previous operation)) (previous.nodeAt kind ref)).symm
end Support

namespace Ref
theorem old_injective {context : List Kind} {kind added : Kind} :
    Function.Injective (@Ref.old kind added context) := by
  intro one two equality
  cases equality
  rfl

theorem head_ne_old {context : List Kind} {kind : Kind} (ref : Ref context kind) :
    (Ref.head : Ref (kind :: context) kind) ≠ .old ref := by
  intro equality
  cases equality
end Ref

namespace AnyRef
theorem number_injective {context : List Kind} {one two : Ref context .number}
    (same : AnyRef.number one = AnyRef.number two) : one = two := by
  cases same
  rfl

theorem truth_injective {context : List Kind} {one two : Ref context .truth}
    (same : AnyRef.truth one = AnyRef.truth two) : one = two := by
  cases same
  rfl

theorem map_injective {a b : List Kind} (embed : ∀ kind, Ref a kind → Ref b kind)
    (injective : ∀ kind, Function.Injective (embed kind)) : Function.Injective (map embed) := by
  intro one two equality
  cases one with
  | number one =>
      cases two with
      | number two =>
          have same := number_injective equality
          exact congrArg AnyRef.number (injective .number same)
      | truth _ => cases equality
  | truth one =>
      cases two with
      | number _ => cases equality
      | truth two =>
          have same := truth_injective equality
          exact congrArg AnyRef.truth (injective .truth same)

theorem head_ne_old {added : Kind} {context : List Kind} (ref : AnyRef context) :
    pack added (Ref.head : Ref (added :: context) added) ≠ old ref := by
  cases added <;> cases ref <;> intro equality <;> cases equality
end AnyRef

def references : (context : List Kind) → List (AnyRef context)
  | [] => []
  | kind :: rest => AnyRef.pack kind Ref.head :: (references rest).map AnyRef.old

theorem references_complete : (context : List Kind) → (kind : Kind) → (ref : Ref context kind) →
    AnyRef.pack kind ref ∈ references context
  | _, _kind, .head => .head _
  | _, kind, .old ref => List.mem_cons_of_mem _
      ((AnyRef.pack_map (fun _ => Ref.old) kind ref) ▸
        FiniteList.mappedMember AnyRef.old (references_complete _ kind ref))

theorem references_all (context : List Kind) (ref : AnyRef context) : ref ∈ references context := by
  cases ref with
  | number ref => exact references_complete context .number ref
  | truth ref => exact references_complete context .truth ref

theorem references_length (context : List Kind) : (references context).length = context.length := by
  induction context with
  | nil => rfl
  | cons kind rest ih => exact congrArg Nat.succ ((FiniteList.mapLength _ _).trans ih)

theorem references_unique (context : List Kind) : (references context).Nodup := by
  induction context with
  | nil => exact .nil
  | cons kind rest ih =>
      apply List.Pairwise.cons _ (Enumeration.nodup_map AnyRef.old
        (AnyRef.map_injective (fun _ => Ref.old) (fun _ => Ref.old_injective)) ih)
      intro value member
      obtain ⟨old, _, equality⟩ := Enumeration.map_origin AnyRef.old _ member
      exact fun same => AnyRef.head_ne_old old (same.trans equality.symm)

/-- A finite extension retains the actual new operations and their typed references. -/
inductive Extension {context : List Kind} (first : Support context) :
    {lastContext : List Kind} → Support lastContext → Type where
  | refl : Extension first first
  | push {middle : List Kind} {support : Support middle} {kind : Kind} :
      Extension first support → (operation : Operation middle kind) → Extension first (.push support operation)

namespace Extension
variable {a b c : List Kind} {first : Support a} {second : Support b} {third : Support c}

def embed : {b : List Kind} → {second : Support b} → Extension first second →
    (kind : Kind) → Ref a kind → Ref b kind
  | _, _, .refl, _, ref => ref
  | _, _, .push previous _, kind, ref => .old (embed previous kind ref)

def compose (one : Extension first second) : {c : List Kind} → {third : Support c} →
    Extension second third → Extension first third
  | _, _, .refl => one
  | _, _, .push previous operation => .push (compose one previous) operation

theorem embed_injective (extension : Extension first second) (kind : Kind) :
    Function.Injective (extension.embed kind) := by
  induction extension with
  | refl => exact fun _ _ equality => equality
  | push previous _ ih => exact fun _ _ equality => ih (Ref.old_injective equality)

theorem read_preserved (extension : Extension first second) (kind : Kind) (ref : Ref a kind) :
    second.read kind (extension.embed kind ref) = first.read kind ref := by
  induction extension with
  | refl => rfl
  | push previous _ ih => exact ih

theorem node_preserved (extension : Extension first second) (kind : Kind) (ref : Ref a kind) :
    second.nodeAt kind (extension.embed kind ref) = (first.nodeAt kind ref).map extension.embed := by
  induction extension with
  | refl => exact (Operation.map_id _).symm
  | push previous _ ih =>
      exact (congrArg (Operation.map (fun _ => Ref.old)) ih).trans (Operation.map_comp _ _ _)

theorem dependencies_preserved (extension : Extension first second) (ref : AnyRef a) :
    second.dependencies (AnyRef.map extension.embed ref) =
      (first.dependencies ref).map (AnyRef.map extension.embed) := by
  cases ref with
  | number ref =>
      exact (congrArg Operation.inputs (extension.node_preserved .number ref)).trans (Operation.inputs_map _ _)
  | truth ref =>
      exact (congrArg Operation.inputs (extension.node_preserved .truth ref)).trans (Operation.inputs_map _ _)

theorem relation_preserved (extension : Extension first second) {parent child : AnyRef a}
    (related : first.Depends parent child) :
    second.Depends (AnyRef.map extension.embed parent) (AnyRef.map extension.embed child) := by
  change AnyRef.map extension.embed child ∈ second.dependencies (AnyRef.map extension.embed parent)
  rw [extension.dependencies_preserved]
  exact FiniteList.mappedMember _ related

theorem relation_reflected (extension : Extension first second) {parent child : AnyRef a}
    (related : second.Depends (AnyRef.map extension.embed parent) (AnyRef.map extension.embed child)) :
    first.Depends parent child := by
  change AnyRef.map extension.embed child ∈ second.dependencies (AnyRef.map extension.embed parent) at related
  rw [extension.dependencies_preserved] at related
  exact ResourceGraph.Extension.mapped_member_reflects _
    (AnyRef.map_injective extension.embed extension.embed_injective) _ related

theorem embed_compose (one : Extension first second) (two : Extension second third)
    (kind : Kind) (ref : Ref a kind) :
    (one.compose two).embed kind ref = two.embed kind (one.embed kind ref) := by
  induction two with
  | refl => rfl
  | push previous _ ih => exact congrArg Ref.old ih

theorem compose_associative {d : List Kind} {fourth : Support d}
    (one : Extension first second) (two : Extension second third) (three : Extension third fourth) :
    (one.compose two).compose three = one.compose (two.compose three) := by
  induction three with
  | refl => rfl
  | push previous operation ih => exact congrArg (fun ext => Extension.push ext operation) ih
end Extension

end RelationalFoundations.TypedResources
