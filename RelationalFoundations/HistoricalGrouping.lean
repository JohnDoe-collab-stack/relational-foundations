import RelationalFoundations.GroupingNormalization
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping
universe u v w
/-- A historical inclusion transports each old admitted operation to an actual
finite trace in the new context. New operations may additionally be authorized. -/
structure Extension (old : Rules.{u}) (new : Rules.{v}) where
  embedding : old.State → new.State
  lift : ∀ {x y}, old.Step x y → Trace new.Step (embedding x) (embedding y)

namespace Extension
variable {old : Rules.{u}} {middle : Rules.{v}} {new : Rules.{w}}
def trace (extension : Extension old middle) {x y}
    (path : Trace old.Step x y) : Trace middle.Step (extension.embedding x) (extension.embedding y) :=
  Trace.map extension.embedding extension.lift path

theorem renormalized (extension : Extension old middle) (x : old.State) :
    middle.normal (extension.embedding (old.normal x)) = middle.normal (extension.embedding x) :=
  (middle.normal_trace (extension.trace (old.normalize x).trace)).symm

def identity (rules : Rules.{u}) : Extension rules rules :=
  ⟨id, fun step => Trace.one step⟩

def compose (first : Extension old middle) (second : Extension middle new) : Extension old new :=
  ⟨fun x => second.embedding (first.embedding x), fun step => second.trace (first.lift step)⟩

def Obligation (rules : Rules.{u}) := {x : rules.State // rules.normal x = x}

def obligation (extension : Extension old middle) (source : Obligation old) : Obligation middle :=
  ⟨middle.normal (extension.embedding source.1), middle.normal_idempotent _⟩

theorem obligation_composes (first : Extension old middle) (second : Extension middle new)
    (source : Obligation old) :
    second.obligation (first.obligation source) = (first.compose second).obligation source :=
  Subtype.ext (second.renormalized (first.embedding source.1))

theorem obligation_identity (rules : Rules.{u}) (source : Obligation rules) :
    (identity rules).obligation source = source := Subtype.ext source.2

theorem include_composes (first : Extension old middle) (second : Extension middle new)
    (x : old.State) : (first.compose second).embedding x = second.embedding (first.embedding x) := rfl
end Extension
end RelationalFoundations.CertifiedGrouping
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.Extension.trace
#print axioms RelationalFoundations.CertifiedGrouping.Extension.renormalized
#print axioms RelationalFoundations.CertifiedGrouping.Extension.compose
#print axioms RelationalFoundations.CertifiedGrouping.Extension.obligation
#print axioms RelationalFoundations.CertifiedGrouping.Extension.obligation_composes
/- AXIOM_AUDIT_END -/

