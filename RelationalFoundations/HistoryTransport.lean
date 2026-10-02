import RelationalFoundations.History
set_option genInjectivity false

namespace RelationalFoundations.History
universe u v
variable {State : Type u} {Step : State → State → Type v}
variable {a b c : State}

def joinOccurrence (h : History Step a b) (k : History Step b c) :
    Occurrence h ⊕ Occurrence k → Occurrence (append h k)
  | .inl old => embedLeftOccurrence old k
  | .inr new => embedRightOccurrence h new

theorem split_left (h : History Step a b) (k : History Step b c)
    (o : Occurrence h) :
    splitAppendOccurrence (embedLeftOccurrence o k) = Sum.inl o := by
  induction k with
  | root => rfl
  | extend k step ih =>
    change (match splitAppendOccurrence (embedLeftOccurrence o k) with
      | .inl old => Sum.inl old
      | .inr new => Sum.inr (Occurrence.earlier new)) = Sum.inl o
    rw [ih]

theorem split_right (h : History Step a b) (k : History Step b c)
    (o : Occurrence k) :
    splitAppendOccurrence (embedRightOccurrence h o) = Sum.inr o := by
  induction o with
  | last => rfl
  | earlier o ih =>
    change (match splitAppendOccurrence (embedRightOccurrence h o) with
      | .inl old => Sum.inl old
      | .inr new => Sum.inr (Occurrence.earlier new)) = Sum.inr (Occurrence.earlier o)
    rw [ih]

theorem join_split (h : History Step a b) (k : History Step b c)
    (o : Occurrence (append h k)) :
    joinOccurrence h k (splitAppendOccurrence o) = o := by
  induction k with
  | root => rfl
  | extend k step ih =>
    cases o with
    | last => rfl
    | earlier o =>
      have eq := ih o
      cases splitEq : splitAppendOccurrence (firstHistory := h)
          (continuation := k) o with
      | inl old =>
        change joinOccurrence h (.extend k step)
          (match splitAppendOccurrence o with
           | .inl old => Sum.inl old
           | .inr new => Sum.inr (Occurrence.earlier new)) = .earlier o
        rw [splitEq]
        change Occurrence.earlier (embedLeftOccurrence old k) = .earlier o
        rw [splitEq] at eq
        exact congrArg Occurrence.earlier eq
      | inr new =>
        change joinOccurrence h (.extend k step)
          (match splitAppendOccurrence o with
           | .inl old => Sum.inl old
           | .inr new => Sum.inr (Occurrence.earlier new)) = .earlier o
        rw [splitEq]
        change Occurrence.earlier (embedRightOccurrence h new) = .earlier o
        rw [splitEq] at eq
        exact congrArg Occurrence.earlier eq

def appendTransport (h : History Step a b) (k : History Step b c) :
    ExactTransport (Occurrence (append h k)) (Occurrence h ⊕ Occurrence k) where
  forward := splitAppendOccurrence
  backward := joinOccurrence h k
  forwardBackward := join_split h k
  backwardForward := by
    intro o
    cases o with
    | inl old => exact split_left h k old
    | inr new => exact split_right h k new

theorem positive_vertices_distinct (p : Positive Step a b) :
    initialVertex p.toHistory ≠ finalVertex p.toHistory := by
  cases p
  intro eq
  cases eq

def exactlyOneOfPositiveAndUnique (positive : Positive Step a b)
    (unique : ∀ first second : Occurrence positive.toHistory, first = second) :
    ExactlyOne positive.toHistory := by
  cases positive with
  | mk predecessor prior step =>
    cases prior with
    | root => exact .single step
    | extend previous penultimate =>
      have impossible := unique .last (.earlier .last)
      cases impossible

theorem ExactlyOne.history_exact {h : History Step a b} (one : ExactlyOne h) :
    h = .extend .root one.step := by
  cases one
  rfl

end RelationalFoundations.History
