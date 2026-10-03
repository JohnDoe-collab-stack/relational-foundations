import RelationalFoundations.GroupingProjections
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping.Binary

inductive Shape where
  | empty
  | more : Shape → Shape

def shape : Nat → Shape
  | 0 => .empty
  | n + 1 => .more (shape n)

def Profile : Shape → Type
  | .empty => Unit
  | Shape.more n => Bool × Profile n

inductive Move : {n : Shape} → (mask : Profile n) → Profile n → Profile n → Type where
  | head {n} {mask : Profile n} {p : Profile n} : Move (n := Shape.more n) (true, mask) (false, p) (true, p)
  | tail {n} {flag bit : Bool} {mask : Profile n} {p q : Profile n}
      (step : Move mask p q) : Move (n := Shape.more n) (flag, mask) (bit, p) (bit, q)

def extra (flag bit : Bool) : Nat :=
  match flag, bit with
  | false, _ => 0
  | true, false => 1
  | true, true => 0

def rank : {n : Shape} → Profile n → Profile n → Nat
  | .empty, _, _ => 0
  | .more _, mask, p => rank mask.2 p.2 + extra mask.1 p.1

def liftEntry {n} (flag bit : Bool) (mask p : Profile n)
    (entry : (q : Profile n) × Move mask p q) :
    (q : Profile (Shape.more n)) × Move (n := Shape.more n) (flag, mask) (bit, p) q :=
  ⟨(bit, entry.1), .tail entry.2⟩

def choices : {n : Shape} → (mask p : Profile n) → List ((q : Profile n) × Move mask p q)
  | .empty, _, _ => []
  | .more _, (true, mask), (false, p) =>
      ⟨(true, p), .head⟩ :: (choices mask p).map (liftEntry true false mask p)
  | .more _, (false, mask), (bit, p) => (choices mask p).map (liftEntry false bit mask p)
  | .more _, (true, mask), (true, p) => (choices mask p).map (liftEntry true true mask p)

theorem mappedMember {A B : Type} (f : A → B) {a : A} {items : List A}
    (member : a ∈ items) : f a ∈ items.map f := by
  induction member with
  | head => exact List.Mem.head _
  | tail head member ih => exact List.Mem.tail _ ih

def locate {n : Shape} {mask p q : Profile n} (step : Move mask p q) :
    {entry : (z : Profile n) × Move mask p z // entry ∈ choices mask p ∧
      HEq entry (⟨q, step⟩ : (z : Profile n) × Move mask p z)} :=
  match n with
  | .empty => nomatch step
  | .more _ =>
      match step with
      | .head => ⟨_, List.Mem.head _, HEq.rfl⟩
      | .tail (flag := flag) (bit := bit) (mask := mask) (p := p) (q := q) child => by
          obtain ⟨entry, member, same⟩ := locate child
          have equal : entry = ⟨q, child⟩ := eq_of_heq same
          cases equal
          let produced := liftEntry flag bit mask p ⟨q, child⟩
          have mapped := mappedMember (f := liftEntry flag bit mask p) member
          refine ⟨produced, ?_, HEq.rfl⟩
          cases flag <;> cases bit
          · exact mapped
          · exact mapped
          · exact List.Mem.tail _ mapped
          · exact mapped
termination_by structural step

theorem decreases {n : Shape} {mask p q : Profile n} (step : Move mask p q) :
    rank mask q < rank mask p := by
  induction step with
  | head => exact Nat.lt_succ_self _
  | tail step ih => exact Nat.add_lt_add_right ih _

def liftTrace {n} (flag bit : Bool) {mask p q : Profile n}
    (path : Trace (Move mask) p q) : Trace (Move (n := Shape.more n) (flag, mask)) (bit, p) (bit, q) :=
  Trace.map (fun x => (bit, x)) (fun step => Trace.one (.tail step)) path

def diamond {n : Shape} {mask p q r : Profile n}
    (first : Move mask p q) (second : Move mask p r) : Join (Move mask) q r :=
  match n with
  | .empty => nomatch first
  | .more _ =>
      match first with
      | .head =>
          match second with
          | .head => ⟨_, .nil _, .nil _⟩
          | .tail other => ⟨_, Trace.one (.tail other), Trace.one .head⟩
      | .tail (flag := flag) (bit := bit) child =>
          match second with
          | .head => ⟨_, Trace.one .head, Trace.one (.tail child)⟩
          | .tail other =>
              let joined := diamond child other
              ⟨(bit, joined.target), liftTrace flag bit joined.left, liftTrace flag bit joined.right⟩
termination_by structural first

def rules {n} (mask : Profile n) : Rules :=
  { State := Profile n, Step := Move mask, rank := rank mask, choices := choices mask
    locate := locate, decreases := decreases, diamond := diamond }

def selected : {n : Shape} → Profile n → Profile n → Profile n
  | .empty, _, _ => ()
  | .more _, (true, mask), (_, p) => (true, selected mask p)
  | .more _, (false, mask), (bit, p) => (bit, selected mask p)

def selectTrace : {n : Shape} → (mask p : Profile n) → Trace (Move mask) p (selected mask p)
  | .empty, _, _ => .nil _
  | .more _, (true, mask), (false, p) =>
      (Trace.one Move.head).append (liftTrace true true (selectTrace mask p))
  | .more _, (true, mask), (true, p) => liftTrace true true (selectTrace mask p)
  | .more _, (false, mask), (bit, p) => liftTrace false bit (selectTrace mask p)

theorem selected_rank_zero : {n : Shape} → (mask p : Profile n) → rank mask (selected mask p) = 0
  | .empty, _, _ => rfl
  | .more _, (true, mask), (_, p) => selected_rank_zero mask p
  | .more _, (false, mask), (_, p) => selected_rank_zero mask p

theorem normal_selected {n} (mask p : Profile n) : (rules mask).normal p = selected mask p :=
  (rules mask).normal_trace (selectTrace mask p) |>.trans
    ((rules mask).normal_terminal _ ((rules mask).zero_terminal _ (selected_rank_zero mask p)))

inductive Slot : Shape → Type where
  | here {n} : Slot (Shape.more n)
  | there {n} : Slot n → Slot (Shape.more n)

def projection {n : Shape} (mask : Profile n) (slot : Slot n) (p : Profile n) : Profile n :=
  match slot with
  | .here => (if mask.1 then true else p.1, p.2)
  | .there child => (p.1, projection mask.2 child p.2)
termination_by structural slot

def projectionTrace : {n : Shape} → (mask : Profile n) → (slot : Slot n) →
    (p : Profile n) → Trace (Move mask) p (projection mask slot p)
  | .more _, (false, _), .here, _ => .nil _
  | .more _, (true, _), .here, (false, _) => Trace.one .head
  | .more _, (true, _), .here, (true, _) => .nil _
  | .more _, (flag, mask), .there slot, (bit, p) => liftTrace flag bit (projectionTrace mask slot p)

def joinOfProjectionEq {n} (mask : Profile n) (slot : Slot n) (p q : Profile n)
    (same : projection mask slot p = projection mask slot q) : Join (Move mask) p q :=
  ⟨_, projectionTrace mask slot p, same.symm ▸ projectionTrace mask slot q⟩

theorem joint_injective {n} (mask p q : Profile (Shape.more (Shape.more n)))
    (agrees : ∀ slot, projection mask slot p = projection mask slot q) : p = q := by
  have headSame := congrArg (fun value : Profile (Shape.more (Shape.more n)) => value.1) (agrees (.there .here))
  have tailSame := congrArg (fun value : Profile (Shape.more (Shape.more n)) => value.2) (agrees .here)
  exact Prod.ext headSame tailSame

theorem joint_injective_of_shape {s n : Shape} (size : s = .more (.more n))
    (mask p q : Profile s) (agrees : ∀ slot, projection mask slot p = projection mask slot q) : p = q := by
  cases size
  exact joint_injective mask p q agrees

def enabled : (n : Shape) → Profile n
  | .empty => ()
  | Shape.more n => (true, enabled n)

theorem selected_enabled : {n : Shape} → (p : Profile n) → selected (enabled n) p = enabled n
  | .empty, _ => rfl
  | .more _, (_, p) => congrArg (fun tail => (true, tail)) (selected_enabled p)

def fullyConnected {n} (p q : Profile n) : Join (Move (enabled n)) p q :=
  (rules (enabled n)).joinOfNormalEq
    (((normal_selected _ p).trans (selected_enabled p)).trans
      ((normal_selected _ q).trans (selected_enabled q)).symm)

def stepIdentification {n : Shape} {mask p q : Profile n} (step : Move mask p q) :
    {slot : Slot n // projection mask slot p = projection mask slot q} :=
  match n with
  | .empty => nomatch step
  | .more _ =>
      match step with
      | .head => ⟨.here, rfl⟩
      | .tail (bit := bit) child =>
          let identified := stepIdentification child
          ⟨.there identified.1, congrArg (fun value => (bit, value)) identified.2⟩
termination_by structural step

def family {n} (mask : Profile n) :
    ProjectionFamily.Authorized (rules mask) (Slot n) (fun _ => Profile n) :=
  { project := projection mask
    realize := fun slot p q same => joinOfProjectionEq mask slot p q same }

def familyConnected {n} : ProjectionFamily.Connected (projection (enabled n)) :=
  fun p q =>
    let joined := fullyConnected p q
    (ProjectionFamily.Path.ofTrace (P := projection (enabled n)) stepIdentification joined.left).append
      (ProjectionFamily.Path.ofTrace (P := projection (enabled n)) stepIdentification joined.right).reverse

theorem boundary_constant {n} (boundary : Profile n → Bool)
    (respects : ∀ slot p q, projection (enabled n) slot p = projection (enabled n) slot q →
      boundary p = boundary q) (p q : Profile n) : boundary p = boundary q :=
  ProjectionFamily.boundary_constant _ familyConnected boundary respects p q

theorem composed_fibres {n} (mask : Profile n) (p q : Profile n) :
    selected mask p = selected mask q ↔ Nonempty (ProjectionFamily.Path (projection mask) p q) := by
  have fibres := (family mask).exact_fibres stepIdentification p q
  rw [normal_selected, normal_selected] at fibres
  exact fibres


def equality : (n : Shape) → DecidableEq (Profile n)
  | .empty => fun x y => match x, y with | (), () => isTrue rfl
  | .more n => fun x y =>
      match Bool.decEq x.1 y.1 with
      | isFalse different => isFalse (fun same => different (congrArg Prod.fst same))
      | isTrue head =>
          match equality n x.2 y.2 with
          | isFalse different => isFalse (fun same => different (congrArg Prod.snd same))
          | isTrue tail => isTrue (Prod.ext head tail)

def enumerate : (n : Shape) → List (Profile n)
  | .empty => [()]
  | .more n => (enumerate n).map (fun p => (false, p)) ++ (enumerate n).map (fun p => (true, p))

end RelationalFoundations.CertifiedGrouping.Binary
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.Binary.rules
#print axioms RelationalFoundations.CertifiedGrouping.Binary.diamond
#print axioms RelationalFoundations.CertifiedGrouping.Binary.normal_selected
#print axioms RelationalFoundations.CertifiedGrouping.Binary.projectionTrace
#print axioms RelationalFoundations.CertifiedGrouping.Binary.joint_injective
#print axioms RelationalFoundations.CertifiedGrouping.Binary.fullyConnected
#print axioms RelationalFoundations.CertifiedGrouping.Binary.stepIdentification
#print axioms RelationalFoundations.CertifiedGrouping.Binary.family
#print axioms RelationalFoundations.CertifiedGrouping.Binary.familyConnected
#print axioms RelationalFoundations.CertifiedGrouping.Binary.boundary_constant
#print axioms RelationalFoundations.CertifiedGrouping.Binary.composed_fibres
#print axioms RelationalFoundations.CertifiedGrouping.Binary.equality
#print axioms RelationalFoundations.CertifiedGrouping.Binary.enumerate
/- AXIOM_AUDIT_END -/
