import RelationalFoundations.GroupingNormalization
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping.ProjectionFamily
universe u v w t

inductive Path {S : Type u} {I : Type v} {Q : I → Type w}
    (P : (i : I) → S → Q i) : S → S → Type (max u v w) where
  | nil (x : S) : Path P x x
  | link {x y z : S} (i : I) (same : P i x = P i y) (tail : Path P y z) : Path P x z

namespace Path
variable {S : Type u} {I : Type v} {Q : I → Type w} {P : (i : I) → S → Q i}

def append {x y z : S} : Path P x y → Path P y z → Path P x z
  | .nil _, right => right
  | .link i same tail, right => .link i same (append tail right)

def reverse {x y : S} : Path P x y → Path P y x
  | .nil _ => .nil _
  | .link i same tail => (reverse tail).append (.link i same.symm (.nil _))

theorem invariant {T : Type t} (read : S → T)
    (respects : ∀ i x y, P i x = P i y → read x = read y)
    {x y : S} : Path P x y → read x = read y
  | .nil _ => rfl
  | .link i same tail => (respects i _ _ same).trans (invariant read respects tail)

theorem minimal (R : S → S → Prop) (refl : ∀ x, R x x)
    (trans : ∀ x y z, R x y → R y z → R x z)
    (includes : ∀ i x y, P i x = P i y → R x y)
    {x y : S} : Path P x y → R x y
  | .nil x => refl x
  | .link i same tail => trans _ _ _ (includes i _ _ same) (minimal R refl trans includes tail)

def ofTrace {Step : S → S → Type t}
    (identifies : ∀ {x y}, Step x y → {i : I // P i x = P i y})
    {x y : S} : Trace Step x y → Path P x y
  | .nil _ => .nil _
  | .cons step tail =>
      let produced := identifies step
      .link produced.1 produced.2 (ofTrace identifies tail)
end Path

def JointAgreement {S : Type u} {I : Type v} {Q : I → Type w}
    (P : (i : I) → S → Q i) (x y : S) : Prop := ∀ i, P i x = P i y

def Connected {S : Type u} {I : Type v} {Q : I → Type w}
    (P : (i : I) → S → Q i) := ∀ x y, Path P x y

theorem boundary_constant {S : Type u} {I : Type v} {Q : I → Type w}
    (P : (i : I) → S → Q i) (connected : Connected P) (boundary : S → Bool)
    (respects : ∀ i x y, P i x = P i y → boundary x = boundary y) (x y : S) :
    boundary x = boundary y := Path.invariant boundary respects (connected x y)

/-- Every kernel identification carries an actual licensed common target.
This is a local projection interface, separate from the normalization rules. -/
structure Authorized (rules : Rules.{u}) (I : Type v) (Q : I → Type w) where
  project : (i : I) → rules.State → Q i
  realize : ∀ i x y, project i x = project i y → Join rules.Step x y

namespace Authorized
variable {rules : Rules.{u}} {I : Type v} {Q : I → Type w}

theorem normal_eq (family : Authorized rules I Q) {x y}
    (path : Path family.project x y) : rules.normal x = rules.normal y :=
  Path.invariant rules.normal (fun i x y same => rules.normal_join (family.realize i x y same)) path

def realizePath (family : Authorized rules I Q) {x y}
    (path : Path family.project x y) : Join rules.Step x y :=
  rules.joinOfNormalEq (family.normal_eq path)

theorem exact_fibres (family : Authorized rules I Q)
    (identifies : ∀ {x y}, rules.Step x y → {i : I // family.project i x = family.project i y})
    (x y : rules.State) : rules.normal x = rules.normal y ↔ Nonempty (Path family.project x y) := by
  constructor
  · intro same
    let joined := rules.joinOfNormalEq same
    exact ⟨(Path.ofTrace (P := family.project) (Step := rules.Step) identifies joined.left).append
      (Path.ofTrace (P := family.project) (Step := rules.Step) identifies joined.right).reverse⟩
  · intro ⟨path⟩
    exact family.normal_eq path
end Authorized
end RelationalFoundations.CertifiedGrouping.ProjectionFamily
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.ProjectionFamily.Path.append
#print axioms RelationalFoundations.CertifiedGrouping.ProjectionFamily.Path.reverse
#print axioms RelationalFoundations.CertifiedGrouping.ProjectionFamily.Path.minimal
#print axioms RelationalFoundations.CertifiedGrouping.ProjectionFamily.Path.ofTrace
#print axioms RelationalFoundations.CertifiedGrouping.ProjectionFamily.boundary_constant
#print axioms RelationalFoundations.CertifiedGrouping.ProjectionFamily.Authorized.realizePath
#print axioms RelationalFoundations.CertifiedGrouping.ProjectionFamily.Authorized.exact_fibres
/- AXIOM_AUDIT_END -/
