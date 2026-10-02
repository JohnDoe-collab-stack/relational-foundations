import RelationalFoundations.Generation
set_option genInjectivity false

namespace RelationalFoundations.History
universe u v
variable {State : Type u} {Step : State → State → Type v}

def Occurrence.prefix {source target : State} {h : History Step source target} :
    Occurrence h → Σ endpoint : State, Positive Step source endpoint
  | .last (history := prior) (step := step) => ⟨_, ⟨_, prior, step⟩⟩
  | .earlier old => old.prefix

def Occurrence.formation {source target : State} {h : History Step source target}
    (o : Occurrence h) : Formation Step source o.prefix.1 :=
  .formed (Formation.fromHistory o.prefix.2.priorHistory) o.prefix.2.lastStep

def Occurrence.currentRecord {source target : State} {h : History Step source target}
    (o : Occurrence h) : Formation.Record o.formation := .current

theorem Occurrence.record_exact {source target : State} {h : History Step source target}
    (o : Occurrence h) : o.currentRecord.located = o.locatedStep := by
  induction o with
  | last => rfl
  | earlier old ih => exact ih

end RelationalFoundations.History
