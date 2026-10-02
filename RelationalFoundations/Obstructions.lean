import RelationalFoundations.Generation
import RelationalFoundations.Regime
set_option genInjectivity false

namespace RelationalFoundations
universe u v w

/-- Obstruction is actual root data, retained by the free constructors. -/
inductive ObstructedFormation {Node : Type u} (Next : Node → Node → Type v)
    (Obstruction : Type w) (root : Node) : Node → Type (max u v w)
  | initial (obstruction : Obstruction) : ObstructedFormation Next Obstruction root root
  | formed {source target : Node} :
      ObstructedFormation Next Obstruction root source → Next source target →
        ObstructedFormation Next Obstruction root target

namespace ObstructedFormation
variable {Node : Type u} {Next : Node → Node → Type v} {Obstruction : Type w} {root : Node}

def inherited {target : Node} : ObstructedFormation Next Obstruction root target → Obstruction
  | .initial obstruction => obstruction
  | .formed previous _ => previous.inherited

def forget {target : Node} : ObstructedFormation Next Obstruction root target → Formation Next root target
  | .initial _ => .initial
  | .formed previous witness => .formed previous.forget witness

def attach (obstruction : Obstruction) {target : Node} : Formation Next root target →
    ObstructedFormation Next Obstruction root target
  | .initial => .initial obstruction
  | .formed previous witness => .formed (attach obstruction previous) witness

theorem inherited_attach (obstruction : Obstruction) {target : Node} (f : Formation Next root target) :
    (attach obstruction f).inherited = obstruction := by
  induction f with
  | initial => rfl
  | formed previous witness ih => exact ih

theorem forget_attach (obstruction : Obstruction) {target : Node} (f : Formation Next root target) :
    (attach obstruction f).forget = f := by
  induction f with
  | initial => rfl
  | formed previous witness ih => exact congrArg (fun k => Formation.formed k witness) ih

theorem inherited_formed {source target : Node}
    (f : ObstructedFormation Next Obstruction root source) (witness : Next source target) :
    (ObstructedFormation.formed f witness).inherited = f.inherited := rfl

end ObstructedFormation
end RelationalFoundations
