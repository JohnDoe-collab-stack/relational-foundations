import RelationalFoundations.Spine
set_option genInjectivity false

namespace RelationalFoundations
universe u v w

/-- Free formation retains the complete prior constitution and the exact new witness. -/
inductive Formation {Node : Type u} (Next : Node → Node → Type v) (root : Node) :
    Node → Type (max u v)
  | initial : Formation Next root root
  | formed {source target : Node} :
      Formation Next root source → Next source target → Formation Next root target

namespace Formation
variable {Node : Type u} {Next : Node → Node → Type v} {root : Node}

def toHistory {target : Node} : Formation Next root target → History Next root target
  | .initial => .root
  | .formed previous witness => .extend previous.toHistory witness

def fromHistory {target : Node} : History Next root target → Formation Next root target
  | .root => .initial
  | .extend previous witness => .formed (fromHistory previous) witness

theorem toHistory_fromHistory (h : History Next root target) :
    (fromHistory h).toHistory = h := by
  induction h with
  | root => rfl
  | extend h witness ih => exact congrArg (fun k => History.extend k witness) ih

theorem fromHistory_toHistory (f : Formation Next root target) :
    fromHistory f.toHistory = f := by
  induction f with
  | initial => rfl
  | formed f witness ih => exact congrArg (fun k => Formation.formed k witness) ih

inductive Record : {target : Node} → Formation Next root target → Type (max u v)
  | current {source target : Node} {previous : Formation Next root source} {witness : Next source target} :
      Record (.formed previous witness)
  | preserved {source target : Node} {previous : Formation Next root source} {witness : Next source target} :
      Record previous → Record (.formed previous witness)

def Record.located {f : Formation Next root target} : Record f → History.LocatedStep Next
  | .current (witness := witness) => ⟨_, _, witness⟩
  | .preserved old => old.located

theorem current_ne_preserved (f : Formation Next root source) (k : Next source target)
    (old : Record f) : (Record.current : Record (.formed f k)) ≠ .preserved old := by
  intro eq
  cases eq

def recordOccurrence {f : Formation Next root target} : Record f → History.Occurrence f.toHistory
  | .current => .last
  | .preserved old => .earlier (recordOccurrence old)

def occurrenceRecord (f : Formation Next root target) : History.Occurrence f.toHistory → Record f :=
  match f with
  | .initial => fun impossible => nomatch impossible
  | .formed previous _ => fun o =>
    match o with
    | .last => .current
    | .earlier old => .preserved (occurrenceRecord previous old)

theorem record_roundTrip {f : Formation Next root target} (r : Record f) :
    occurrenceRecord f (recordOccurrence r) = r := by
  induction r with
  | current => rfl
  | preserved r ih => exact congrArg Record.preserved ih

theorem occurrence_roundTrip (f : Formation Next root target)
    (o : History.Occurrence f.toHistory) : recordOccurrence (occurrenceRecord f o) = o := by
  induction f with
  | initial => cases o
  | formed previous witness ih =>
    cases o with
    | last => rfl
    | earlier old => exact congrArg History.Occurrence.earlier (ih old)

def recordTransport (f : Formation Next root target) :
    ExactTransport (Record f) (History.Occurrence f.toHistory) :=
  ⟨recordOccurrence, occurrenceRecord f, record_roundTrip, occurrence_roundTrip f⟩

theorem record_witness_exact {f : Formation Next root target} (r : Record f) :
    (recordOccurrence r).locatedStep = r.located := by
  induction r with
  | current => rfl
  | preserved r ih => exact ih

theorem preserves_origin {f : Formation Next root source} {k : Next source target}
    (r : Record f) : (Record.preserved (witness := k) r).located = r.located := rfl

structure Algebra (Next : Node → Node → Type v) (root : Node) where
  Carrier : Node → Type w
  initial : Carrier root
  form : {source target : Node} → Carrier source → Next source target → Carrier target

def fold (algebra : Algebra Next root) {target : Node} : Formation Next root target → algebra.Carrier target
  | .initial => algebra.initial
  | .formed previous witness => algebra.form (fold algebra previous) witness

theorem fold_formed (algebra : Algebra Next root) (f : Formation Next root source)
    (k : Next source target) : fold algebra (.formed f k) = algebra.form (fold algebra f) k := rfl

/-- The recursive interpretation is uniquely determined by preservation of the constructors. -/
theorem fold_unique (algebra : Algebra Next root)
    (interpret : {target : Node} → Formation Next root target → algebra.Carrier target)
    (initialExact : interpret .initial = algebra.initial)
    (formedExact : ∀ {source target} (f : Formation Next root source) (k : Next source target),
      interpret (.formed f k) = algebra.form (interpret f) k)
    (f : Formation Next root target) : interpret f = fold algebra f := by
  induction f with
  | initial => exact initialExact
  | formed previous witness ih =>
    exact (formedExact previous witness).trans (congrArg (fun value => algebra.form value witness) ih)

def deployed {node : Node} (spine : Spine Next node) : Formation Next node spine.finalNode :=
  fromHistory spine.toHistory

theorem deployed_exact {node : Node} (spine : Spine Next node) :
    (deployed spine).toHistory = spine.toHistory := toHistory_fromHistory _

end Formation
end RelationalFoundations
