import RelationalFoundations.FiniteRuleConstruction
set_option genInjectivity false

/-! Finite dependency paths retain their ordered occurrences, including repeated
references. Cycles are compatible with coverage. Evaluation from a reading and
construction of that reading remain separate obligations. -/

namespace RelationalFoundations.DependencyPaths

inductive Walk {A : Type} (relation : A → A → Prop) : A → A → Type where
  | stop (point : A) : Walk relation point point
  | next {first middle last : A} : relation first middle → Walk relation middle last → Walk relation first last

namespace Walk
variable {A B : Type} {R : A → A → Prop} {S : B → B → Prop}

def length {a b : A} : Walk R a b → Nat
  | .stop _ => 0
  | .next _ tail => tail.length + 1

def nodes {a b : A} : Walk R a b → List A
  | .stop point => [point]
  | .next (first := first) _ tail => first :: tail.nodes

def map (f : A → B) (preserves : ∀ {a b}, R a b → S (f a) (f b)) :
    {a b : A} → Walk R a b → Walk S (f a) (f b)
  | _, _, .stop point => .stop (f point)
  | _, _, .next edge tail => .next (preserves edge) (map f preserves tail)

theorem map_length (f : A → B) (preserves : ∀ {a b}, R a b → S (f a) (f b))
    {a b : A} (path : Walk R a b) : (path.map f preserves).length = path.length := by
  induction path with
  | stop _ => rfl
  | next _ _ ih => exact congrArg Nat.succ ih

theorem map_nodes (f : A → B) (preserves : ∀ {a b}, R a b → S (f a) (f b))
    {a b : A} (path : Walk R a b) : (path.map f preserves).nodes = path.nodes.map f := by
  induction path with
  | stop _ => rfl
  | next _ _ ih => exact congrArg (List.cons _) ih
end Walk

open FiniteRuleConstruction DemandClosure
universe u
variable {rules : Rules.{u}}

abbrev Path (frame : rules.Frame) := Walk (rules.Depends frame)

def transport {a b : rules.Frame} (execution : rules.Execution a b)
    {first last : Packed (rules.Ref a)} (path : Path a first last) :
    Path b (rename execution.embed first) (rename execution.embed last) :=
  path.map (rename execution.embed) (rules.relation_preserved execution)

theorem transport_nodes {a b : rules.Frame} (execution : rules.Execution a b)
    {first last : Packed (rules.Ref a)} (path : Path a first last) :
    (transport execution path).nodes = path.nodes.map (rename execution.embed) :=
  path.map_nodes _ _

theorem transport_length {a b : rules.Frame} (execution : rules.Execution a b)
    {first last : Packed (rules.Ref a)} (path : Path a first last) :
    (transport execution path).length = path.length := path.map_length _ _

private theorem reflectAux {a b : rules.Frame} (execution : rules.Execution a b)
    {first last : Packed (rules.Ref b)} (path : Path b first last) :
    ∀ oldFirst : Packed (rules.Ref a), rename execution.embed oldFirst = first →
      ∃ oldLast, ∃ oldPath : Path a oldFirst oldLast,
        rename execution.embed oldLast = last ∧ oldPath.length = path.length ∧
          oldPath.nodes.map (rename execution.embed) = path.nodes := by
  induction path with
  | stop point =>
      intro oldFirst same
      exact ⟨oldFirst, .stop oldFirst, same, rfl, congrArg (fun point => [point]) same⟩
  | @next first middle last edge tail ih =>
      intro oldFirst same
      have member : middle ∈ (rules.dependencies a oldFirst).map (rename execution.embed) := by
        change middle ∈ rules.dependencies b _ at edge
        rw [← same, rules.dependencies_preserved execution oldFirst] at edge
        exact edge
      obtain ⟨oldMiddle, oldEdge, middleSame⟩ := ResourceGraph.Enumeration.map_origin _ _ member
      obtain ⟨oldLast, oldTail, lastSame, lengthSame, nodesSame⟩ := ih oldMiddle middleSame
      exact ⟨oldLast, .next oldEdge oldTail, lastSame, congrArg Nat.succ lengthSame,
        (congrArg (fun point => point :: oldTail.nodes.map (rename execution.embed)) same).trans
          (congrArg (List.cons first) nodesSame)⟩

/-- Every path starting at an old resource stays in the transported old
dependencies. Reflection is a proposition; no executable inverse is assumed. -/
theorem reflected {a b : rules.Frame} (execution : rules.Execution a b)
    (first : Packed (rules.Ref a)) {last : Packed (rules.Ref b)}
    (path : Path b (rename execution.embed first) last) :
    ∃ oldLast, ∃ oldPath : Path a first oldLast,
      rename execution.embed oldLast = last ∧ oldPath.length = path.length ∧
        oldPath.nodes.map (rename execution.embed) = path.nodes :=
  reflectAux execution path first rfl

theorem cycle_preserved {a b : rules.Frame} (execution : rules.Execution a b)
    {point : Packed (rules.Ref a)} (cycle : Path a point point) (positive : 0 < cycle.length) :
    0 < (transport execution cycle).length := (transport_length execution cycle).symm ▸ positive

theorem cycle_reflected {a b : rules.Frame} (execution : rules.Execution a b)
    (point : Packed (rules.Ref a)) (cycle : Path b (rename execution.embed point) (rename execution.embed point))
    (positive : 0 < cycle.length) : ∃ oldCycle : Path a point point, 0 < oldCycle.length := by
  obtain ⟨last, path, lastSame, lengthSame, _⟩ := reflected execution point cycle
  have same : last = point := rename_injective _ execution.embed_injective lastSame
  cases same
  exact ⟨path, lengthSame.symm ▸ positive⟩

theorem transport_composition_nodes {a b c : rules.Frame}
    (one : rules.Execution a b) (two : rules.Execution b c)
    {first last : Packed (rules.Ref a)} (path : Path a first last) :
    (transport two (transport one path)).nodes = (transport (one.compose two) path).nodes := by
  rw [transport_nodes, transport_nodes, transport_nodes]
  exact (FiniteList.mapCompose _ _ path.nodes).trans
    (FiniteList.mapAgree _ _ (fun ⟨kind, ref⟩ =>
      congrArg (Sigma.mk kind) (one.embed_compose two kind ref).symm) path.nodes)

namespace Coverage
variable {target : rules.State} {history : History rules.Step rules.origin target}
variable (actual : rules.Complete history)

def coordinates : ExactTransport (Packed (rules.Requests history)) (Packed (rules.Ref actual.realization.frame)) where
  forward := rename (fun kind => (actual.coverage.coordinates kind).forward)
  backward := rename (fun kind => (actual.coverage.coordinates kind).backward)
  forwardBackward := fun ⟨kind, request⟩ => congrArg (Sigma.mk kind) ((actual.coverage.coordinates kind).forwardBackward request)
  backwardForward := fun ⟨kind, ref⟩ => congrArg (Sigma.mk kind) ((actual.coverage.coordinates kind).backwardForward ref)

def RequestDepends (first last : Packed (rules.Requests history)) : Prop :=
  rules.Depends actual.realization.frame ((coordinates actual).forward first) ((coordinates actual).forward last)

theorem request_edge {one two : Packed (rules.Ref actual.realization.frame)}
    (edge : rules.Depends actual.realization.frame one two) :
    RequestDepends actual ((coordinates actual).backward one) ((coordinates actual).backward two) := by
    change rules.Depends _ ((coordinates actual).forward ((coordinates actual).backward one))
      ((coordinates actual).forward ((coordinates actual).backward two))
    rw [(coordinates actual).backwardForward one, (coordinates actual).backwardForward two]
    exact edge

def requests {first last : Packed (rules.Ref actual.realization.frame)}
    (path : Path actual.realization.frame first last) :
    Walk (RequestDepends actual) ((coordinates actual).backward first) ((coordinates actual).backward last) :=
  path.map (coordinates actual).backward (request_edge actual)

theorem roundtrip {A B : Type} (e : ExactTransport A B) (items : List B) :
    (items.map e.backward).map e.forward = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      exact (congrArg (fun x => x :: (tail.map e.backward).map e.forward) (e.backwardForward head)).trans
        (congrArg (List.cons head) ih)

/-- Demand paths are constructed from the actual resource path. Their return
preserves every visited reference, in order, with all repeated visits. -/
theorem ordered_roundtrip {first last : Packed (rules.Ref actual.realization.frame)}
    (path : Path actual.realization.frame first last) :
    (requests actual path).nodes.map (coordinates actual).forward = path.nodes := by
  exact (congrArg (List.map (coordinates actual).forward)
    (path.map_nodes (coordinates actual).backward (request_edge actual))).trans (roundtrip _ _)

theorem enumerated {first last : Packed (rules.Ref actual.realization.frame)}
    (path : Path actual.realization.frame first last) (ref : Packed (rules.Ref actual.realization.frame))
    (_visited : ref ∈ path.nodes) : ref ∈ actual.resources.items := actual.resources.exhaustive ref

theorem values (kind : rules.Kind) (ref : rules.Ref actual.realization.frame kind) :
    rules.read actual.realization.frame kind ref =
      rules.expected history kind ((actual.coverage.coordinates kind).backward ref) := by
  have known := actual.coverage.values kind ((actual.coverage.coordinates kind).backward ref)
  exact (congrArg (rules.read actual.realization.frame kind)
    ((actual.coverage.coordinates kind).backwardForward ref)).symm.trans known
end Coverage
end RelationalFoundations.DependencyPaths

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.DependencyPaths.Walk.map
#print axioms RelationalFoundations.DependencyPaths.transport
#print axioms RelationalFoundations.DependencyPaths.reflected
#print axioms RelationalFoundations.DependencyPaths.cycle_preserved
#print axioms RelationalFoundations.DependencyPaths.cycle_reflected
#print axioms RelationalFoundations.DependencyPaths.transport_composition_nodes
#print axioms RelationalFoundations.DependencyPaths.Coverage.requests
#print axioms RelationalFoundations.DependencyPaths.Coverage.ordered_roundtrip
#print axioms RelationalFoundations.DependencyPaths.Coverage.enumerated
#print axioms RelationalFoundations.DependencyPaths.Coverage.values
/- AXIOM_AUDIT_END -/
