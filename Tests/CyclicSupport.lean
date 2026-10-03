import RelationalFoundations.FiniteRuleInstances
import RelationalFoundations.DependencyPaths
set_option genInjectivity false

/-! A closed cyclic rule system with certified supplied readings and retained resource identities. -/

namespace RelationalFoundations.CyclicSupportTests
open RelationalFoundations RelationalFoundations.FiniteRuleConstruction

def Step (a b : Nat) : Type := { _u : Unit // b = a + 1 }

def hist : (n : Nat) → History Step 0 n
  | 0 => .root
  | n + 1 => .extend (hist n) ⟨(), rfl⟩

def Slot : Nat → Type
  | 0 => Unit
  | n + 1 => Slot n ⊕ Unit

def readS (v : Nat) : (n : Nat) → Slot n → Nat
  | 0, _ => 0
  | n + 1, .inl s => readS v n s
  | _ + 1, .inr _ => v

def cyclic (v : Nat) : Rules.{0} where
  State := Nat
  Step := Step
  origin := 0
  allowed := fun _ => True
  Kind := Unit
  Value := fun _ => Nat
  Initial := fun _ => Unit
  New := fun _ _ => Unit
  initialExpected := fun _ _ => 0
  newExpected := fun _ _ _ => v
  initialFinite := FiniteRuleInstances.unitFinite
  newFinite := fun _ => FiniteRuleInstances.unitFinite
  Frame := Nat
  recorded := fun n => ⟨n, hist n⟩
  Ref := fun n _ => Slot n
  Node := fun n _ => Slot n
  read := fun n _ => readS v n
  node := fun _ _ r => r
  inputs := fun {_} {kind} nd => [⟨kind, nd⟩]
  eval := fun {_} read {kind} nd => read kind nd
  map := fun {_ _} f {kind} nd => f kind nd
  map_id := fun {_} {_} _ => rfl
  map_comp := fun {_ _ _} _ _ {_} _ => rfl
  inputs_map := fun {_ _} _ {_} _ => rfl
  eval_map := fun {_ _} _ _ {_} _ => rfl
  eval_congr := fun {_} _ _ same {kind} nd => same kind nd
  initial := 0
  initial_recorded := rfl
  initialCoordinates := fun _ => ExactTransport.reflexive Unit
  initial_values := fun _ _ => rfl
  initial_rules := fun _ _ => rfl
  valid := fun _ => True
  initial_valid := True.intro
  advance := fun n => n + 1
  Result := fun _ => Unit
  produce := fun _ => ()
  react := fun n _ => ⟨n + 1, ⟨(), rfl⟩⟩
  advance_recorded := fun _ => rfl
  advance_valid := fun _ _ => True.intro
  reaction_allowed := fun _ _ => True.intro
  reaction_exact := fun _ _ {_} step _ => by
    obtain ⟨u, h⟩ := step
    cases u
    cases h
    rfl
  split := fun n _ => ExactTransport.reflexive (Slot n ⊕ Unit)
  old_values := fun _ _ _ => rfl
  old_nodes := fun _ _ _ => rfl
  new_values := fun _ _ _ _ => rfl
  new_rules := fun _ _ _ => rfl
  visible := fun n => n
  visible_valid := fun _ _ => rfl

theorem admitted (v : Nat) {t : Nat} : (h : History (cyclic v).Step (cyclic v).origin t) → (cyclic v).Admissible h
  | .root => True.intro
  | .extend previous _ => ⟨admitted v previous, True.intro⟩

theorem cyclic_self_dependency (v : Nat) {t : Nat} (h : History (cyclic v).Step (cyclic v).origin t)
    (ref : Packed ((cyclic v).Ref ((cyclic v).complete h (admitted v h)).realization.frame)) :
    (cyclic v).Depends ((cyclic v).complete h (admitted v h)).realization.frame ref ref := by
  cases ref with
  | mk kind r => exact List.Mem.head _

def oneStep : History Step 0 1 := hist 1

def frameOne (v : Nat) : (cyclic v).Frame := (1 : Nat)

def freshRef (v : Nat) : (cyclic v).Ref (frameOne v) () := (Sum.inr () : Slot 0 ⊕ Unit)

theorem certification_does_not_determine_values :
    ((cyclic 7).complete oneStep (admitted 7 oneStep)).realization.frame = frameOne 7 ∧
    ((cyclic 8).complete oneStep (admitted 8 oneStep)).realization.frame = frameOne 8 ∧
    ((cyclic 7).node (frameOne 7) () (freshRef 7) : Slot 1) = ((cyclic 8).node (frameOne 8) () (freshRef 8) : Slot 1) ∧
    (cyclic 7).Certified (frameOne 7) ∧ (cyclic 8).Certified (frameOne 8) ∧
    (cyclic 7).read (frameOne 7) () (freshRef 7) = (7 : Nat) ∧
    (cyclic 8).read (frameOne 8) () (freshRef 8) = (8 : Nat) :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

def cyclicComplete : (cyclic 7).Complete oneStep := (cyclic 7).complete oneStep (admitted 7 oneStep)

def loop (frame : (cyclic 7).Frame) (ref : Packed ((cyclic 7).Ref frame)) :
    DependencyPaths.Path (rules := cyclic 7) frame ref ref :=
  .next (by cases ref; exact .head _) (.stop ref)

theorem loop_positive (frame : (cyclic 7).Frame) (ref : Packed ((cyclic 7).Ref frame)) :
    0 < (loop frame ref).length := Nat.zero_lt_succ 0

theorem repeated_visits_covered (ref : Packed ((cyclic 7).Ref cyclicComplete.realization.frame)) :
    (DependencyPaths.Coverage.requests cyclicComplete (loop _ ref)).nodes.map
      (DependencyPaths.Coverage.coordinates cyclicComplete).forward = [ref, ref] :=
  DependencyPaths.Coverage.ordered_roundtrip cyclicComplete (loop _ ref)

theorem cycle_continues (depth : Nat) (ref : Packed ((cyclic 7).Ref cyclicComplete.realization.frame)) :
    0 < (DependencyPaths.transport ((cyclic 7).run cyclicComplete.realization.frame depth).2 (loop _ ref)).length :=
  DependencyPaths.cycle_preserved _ (loop _ ref) (loop_positive _ ref)

end RelationalFoundations.CyclicSupportTests

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CyclicSupportTests.Step
#print axioms RelationalFoundations.CyclicSupportTests.hist
#print axioms RelationalFoundations.CyclicSupportTests.Slot
#print axioms RelationalFoundations.CyclicSupportTests.readS
#print axioms RelationalFoundations.CyclicSupportTests.cyclic
#print axioms RelationalFoundations.CyclicSupportTests.admitted
#print axioms RelationalFoundations.CyclicSupportTests.cyclic_self_dependency
#print axioms RelationalFoundations.CyclicSupportTests.oneStep
#print axioms RelationalFoundations.CyclicSupportTests.frameOne
#print axioms RelationalFoundations.CyclicSupportTests.freshRef
#print axioms RelationalFoundations.CyclicSupportTests.certification_does_not_determine_values
#print axioms RelationalFoundations.CyclicSupportTests.cyclicComplete
#print axioms RelationalFoundations.CyclicSupportTests.loop
#print axioms RelationalFoundations.CyclicSupportTests.repeated_visits_covered
#print axioms RelationalFoundations.CyclicSupportTests.cycle_continues
/- AXIOM_AUDIT_END -/
