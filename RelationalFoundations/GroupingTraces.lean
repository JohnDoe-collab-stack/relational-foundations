set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping
universe u v w z

inductive Trace {S : Type u} (Step : S → S → Type v) : S → S → Type (max u v) where
  | nil (x : S) : Trace Step x x
  | cons {x y z : S} (step : Step x y) (tail : Trace Step y z) : Trace Step x z

namespace Trace
variable {S : Type u} {Step : S → S → Type v}

def one {x y : S} (step : Step x y) : Trace Step x y := .cons step (.nil y)

def append {x y z : S} : Trace Step x y → Trace Step y z → Trace Step x z
  | .nil _, right => right
  | .cons step tail, right => .cons step (append tail right)

def length {x y : S} : Trace Step x y → Nat
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

theorem append_nil {x y : S} (path : Trace Step x y) : path.append (.nil y) = path := by
  induction path with
  | nil => rfl
  | cons step tail ih => exact congrArg (Trace.cons step) ih

theorem append_assoc {a b c d : S} (one : Trace Step a b) (two : Trace Step b c)
    (three : Trace Step c d) : (one.append two).append three = one.append (two.append three) := by
  induction one with
  | nil => rfl
  | cons step tail ih => exact congrArg (Trace.cons step) (ih two)

def map {T : Type w} {Next : T → T → Type z} (f : S → T)
    (stepMap : ∀ {x y}, Step x y → Trace Next (f x) (f y))
    {x y : S} : Trace Step x y → Trace Next (f x) (f y)
  | .nil _ => .nil _
  | .cons step tail => (stepMap step).append (map f stepMap tail)

theorem invariant {T : Type w} (read : S → T)
    (stepMap : ∀ {x y}, Step x y → read x = read y)
    {x y : S} : Trace Step x y → read x = read y
  | .nil _ => rfl
  | .cons step tail => (stepMap step).trans (invariant read stepMap tail)

def act {D : S → Type w} (stepMap : ∀ {x y}, Step x y → D x → D y)
    {x y : S} : Trace Step x y → D x → D y
  | .nil _, value => value
  | .cons step tail, value => act stepMap tail (stepMap step value)

theorem act_append {D : S → Type w} (stepMap : ∀ {x y}, Step x y → D x → D y)
    {a b c : S} (one : Trace Step a b) (two : Trace Step b c) (value : D a) :
    act (Step := Step) (D := D) stepMap (one.append two) value = act (Step := Step) (D := D) stepMap two (act (Step := Step) (D := D) stepMap one value) := by
  induction one with
  | nil => rfl
  | cons step tail ih => exact ih two (stepMap step value)

theorem act_preserves {D : S → Type w} (stepMap : ∀ {x y}, Step x y → D x → D y)
    (accept : (x : S) → D x → Prop)
    (preserves : ∀ {x y} (step : Step x y) (value : D x), accept x value → accept y (stepMap step value))
    {x y : S} (path : Trace Step x y) (value : D x) (allowed : accept x value) :
    accept y (act (Step := Step) (D := D) stepMap path value) := by
  induction path with
  | nil => exact allowed
  | cons step tail ih => exact ih (stepMap step value) (preserves step value allowed)
end Trace

structure Join {S : Type u} (Step : S → S → Type v) (x y : S) where
  target : S
  left : Trace Step x target
  right : Trace Step y target

inductive Chain {S : Type u} (Step : S → S → Type v) : S → S → Type (max u v) where
  | nil (x : S) : Chain Step x x
  | forward {x y z : S} (step : Step x y) (tail : Chain Step y z) : Chain Step x z
  | backward {x y z : S} (step : Step y x) (tail : Chain Step y z) : Chain Step x z

namespace Chain
variable {S : Type u} {Step : S → S → Type v}

def append {x y z : S} : Chain Step x y → Chain Step y z → Chain Step x z
  | .nil _, right => right
  | .forward step tail, right => .forward step (append tail right)
  | .backward step tail, right => .backward step (append tail right)

def reverse {x y : S} : Chain Step x y → Chain Step y x
  | .nil _ => .nil _
  | .forward step tail => (reverse tail).append (.backward step (.nil _))
  | .backward step tail => (reverse tail).append (.forward step (.nil _))

def ofTrace {x y : S} : Trace Step x y → Chain Step x y
  | .nil _ => .nil _
  | .cons step tail => .forward step (ofTrace tail)

theorem invariant {T : Type w} (read : S → T)
    (stepMap : ∀ {x y}, Step x y → read x = read y)
    {x y : S} : Chain Step x y → read x = read y
  | .nil _ => rfl
  | .forward step tail => (stepMap step).trans (invariant read stepMap tail)
  | .backward step tail => (stepMap step).symm.trans (invariant read stepMap tail)

theorem minimal (R : S → S → Prop) (refl : ∀ x, R x x)
    (trans : ∀ x y z, R x y → R y z → R x z)
    (includes : ∀ {x y}, Step x y → R x y)
    (reverse : ∀ x y, R x y → R y x)
    {x y : S} : Chain Step x y → R x y
  | .nil x => refl x
  | .forward step tail => trans _ _ _ (includes step) (minimal R refl trans includes reverse tail)
  | .backward step tail => trans _ _ _ (reverse _ _ (includes step)) (minimal R refl trans includes reverse tail)
end Chain
end RelationalFoundations.CertifiedGrouping

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.Trace.append
#print axioms RelationalFoundations.CertifiedGrouping.Trace.append_assoc
#print axioms RelationalFoundations.CertifiedGrouping.Trace.map
#print axioms RelationalFoundations.CertifiedGrouping.Trace.act
#print axioms RelationalFoundations.CertifiedGrouping.Trace.act_append
#print axioms RelationalFoundations.CertifiedGrouping.Trace.act_preserves
#print axioms RelationalFoundations.CertifiedGrouping.Chain.reverse
#print axioms RelationalFoundations.CertifiedGrouping.Chain.minimal
/- AXIOM_AUDIT_END -/
