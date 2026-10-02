import RelationalFoundations.WordSupport
import RelationalFoundations.Perimetral
set_option genInjectivity false

namespace RelationalFoundations.HistoricalSupportTests
open DemandClosure HistoricalSupport

/-- Two equal prerequisite labels still occupy different constitutive positions. -/
def repeated : WordSupport.Request Bool := .join (.emit true) (.emit true)

def repeatedTree := (WordSupport.system Bool).build repeated

def repeatedFirst : Tree.Address repeatedTree := .child (.head .root)
def repeatedSecond : Tree.Address repeatedTree := .child (.tail (.head .root))

theorem repeated_labels_equal : Tree.requestsAt repeatedTree repeatedFirst =
    Tree.requestsAt repeatedTree repeatedSecond := rfl

theorem repeated_resources_distinct : repeatedFirst ≠ repeatedSecond := by
  intro equality
  cases equality

/-- A reuse has the same semantic output as its child and a distinct resource. -/
def reuseTree := (WordSupport.system Bool).build (.reuse (.emit false))

theorem reuse_root_child_distinct :
    (Tree.Address.root : Tree.Address reuseTree) ≠ .child (.head .root) := by
  intro equality
  cases equality

theorem reuse_preserves_output : (WordSupport.producer Bool).realize reuseTree = [false] :=
  WordSupport.build_realizes_meaning _

/- Dependency growth is an output of construction, not a supplied capacity. -/
#guard repeatedTree.size == 3
#guard reuseTree.size == 2
#guard (Tree.addresses repeatedTree).length == 3

def license {source target : Perimetral.Node} : Perimetral.Next source target → Bool
  | .licensed value => value

def actualPolicy := WordSupport.policy (Step := Perimetral.Next) license

def first : History Perimetral.Next Perimetral.Node.first Perimetral.Node.second :=
  .extend .root (.licensed true)

def second : History Perimetral.Next Perimetral.Node.first Perimetral.Node.third :=
  .extend first (.licensed false)

def tail : History Perimetral.Next Perimetral.Node.second Perimetral.Node.third :=
  .extend .root (.licensed false)

theorem every_actual_history_has_exact_output {source target : Perimetral.Node}
    (history : History Perimetral.Next source target) :
    WordSupport.previousOutput history ((actualPolicy.build history).context (WordSupport.producer Bool)) =
      WordSupport.trace license history := WordSupport.output_eq_trace license history

/-- The second request is formed using the actual first produced output. -/
theorem second_uses_previous_output : ((actualPolicy.build second).entry .last).1 =
    [WordSupport.Request.join (.emit false)
      (.reuse (.join (.emit true) .empty))] := rfl

theorem old_demand_and_witness_preserved :
    (actualPolicy.build second).entry (.earlier .last) = (actualPolicy.build first).entry .last :=
  actualPolicy.build_old_entry first (.licensed false) .last

theorem continuing_agrees_with_rebuilding : actualPolicy.advance (actualPolicy.build first) tail =
    actualPolicy.build second := actualPolicy.advance_build first tail

theorem all_resources_certified (address : (actualPolicy.build second).Address) :
    let resource := (actualPolicy.build second).resourceAt address
    (WordSupport.producer Bool).realize resource.2 = WordSupport.meaning resource.1 :=
  actualPolicy.build_resource_valid (WordSupport.soundness Bool) second address

/-- The actual generated family admits no common finite support bound. -/
theorem actual_supports_unbounded (bound : Nat) :
    ∃ depth : Nat, bound < (actualPolicy.build (Perimetral.iterate depth).history).size := by
  refine ⟨bound, ?_⟩
  have lower := WordSupport.support_size_lower_bound license (Perimetral.iterate bound).history
  rw [Perimetral.iterate_length] at lower
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_left bound 3)) lower

#guard (WordSupport.previousOutput second
  ((actualPolicy.build second).context (WordSupport.producer Bool))) == [false, true]
#guard (actualPolicy.build first).size == 5
#guard (actualPolicy.build second).size == 11

/-- A single operational occurrence does not imply closure of its demands. -/
def finite_occurrence_with_cyclic_demands :
    History.ExactlyOne first × PLift (¬ Nonempty (Tree cyclicRequires ())) :=
  ⟨History.ExactlyOne.single (Step := Perimetral.Next)
      (Perimetral.Compatible.licensed true : Perimetral.Next .first .second),
    ⟨fun ⟨tree⟩ => cyclic_tree_impossible tree⟩⟩

end RelationalFoundations.HistoricalSupportTests
