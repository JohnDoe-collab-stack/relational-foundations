import RelationalFoundations.CertifiedGrouping
set_option genInjectivity false
namespace RelationalFoundations.CertifiedGrouping.Rules
universe u
variable (rules : Rules.{u})

/-- Structural fuel recursion. Completeness of local choices certifies its stop. -/
def normalizeWithin : (fuel : Nat) → (x : rules.State) → rules.rank x ≤ fuel → rules.Normalized x
  | 0, x, bound =>
    { target := x, trace := .nil x
      terminal := rules.zero_terminal x (Nat.eq_zero_of_le_zero bound) }
  | fuel + 1, x, bound =>
    match same : rules.choices x with
    | [] => { target := x, trace := .nil x, terminal := rules.terminal_of_empty x same }
    | entry :: _ =>
      let smaller : rules.rank entry.1 ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (rules.decreases entry.2) bound)
      let next := normalizeWithin fuel entry.1 smaller
      { target := next.target, trace := .cons entry.2 next.trace, terminal := next.terminal }

def normalize (x : rules.State) : rules.Normalized x :=
  rules.normalizeWithin (rules.rank x) x (Nat.le_refl _)

def normal (x : rules.State) : rules.State := (rules.normalize x).target

theorem terminal_unique : (fuel : Nat) → (x : rules.State) → rules.rank x ≤ fuel →
    {y z : rules.State} → Trace rules.Step x y → Trace rules.Step x z →
    rules.Terminal y → rules.Terminal z → y = z
  | 0, x, bound, _, _, left, right, terminalLeft, terminalRight => by
      cases left with
      | nil =>
        cases right with
        | nil => rfl
        | cons first tail => exact False.elim (terminalLeft first)
      | cons first tail =>
        exact False.elim (rules.zero_terminal x (Nat.eq_zero_of_le_zero bound) first)
  | fuel + 1, x, bound, _, _, left, right, terminalLeft, terminalRight => by
      cases left with
      | nil =>
        cases right with
        | nil => rfl
        | cons first tail => exact False.elim (terminalLeft first)
      | cons first tail =>
        cases right with
        | nil => exact False.elim (terminalRight first)
        | cons second rest =>
          let raccord := rules.diamond first second
          let last := rules.normalize raccord.target
          have leftBound := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (rules.decreases first) bound)
          have rightBound := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (rules.decreases second) bound)
          have leftSame := terminal_unique fuel _ leftBound tail
            (raccord.left.append last.trace) terminalLeft last.terminal
          have rightSame := terminal_unique fuel _ rightBound rest
            (raccord.right.append last.trace) terminalRight last.terminal
          exact leftSame.trans rightSame.symm

theorem normal_trace {x y : rules.State} (path : Trace rules.Step x y) :
    rules.normal x = rules.normal y :=
  rules.terminal_unique (rules.rank x) x (Nat.le_refl _)
    (rules.normalize x).trace (path.append (rules.normalize y).trace)
    (rules.normalize x).terminal (rules.normalize y).terminal

theorem normal_step {x y : rules.State} (step : rules.Step x y) :
    rules.normal x = rules.normal y := rules.normal_trace (Trace.one step)

theorem normal_terminal (x : rules.State) (terminal : rules.Terminal x) :
    rules.normal x = x :=
  rules.terminal_unique (rules.rank x) x (Nat.le_refl _)
    (rules.normalize x).trace (.nil x) (rules.normalize x).terminal terminal

theorem normal_idempotent (x : rules.State) :
    rules.normal (rules.normal x) = rules.normal x :=
  rules.normal_terminal _ (rules.normalize x).terminal

def joinOfNormalEq {x y : rules.State} (same : rules.normal x = rules.normal y) :
    Join rules.Step x y :=
  { target := rules.normal x, left := (rules.normalize x).trace
    right := same.symm ▸ (rules.normalize y).trace }

theorem normal_join {x y : rules.State} (joined : Join rules.Step x y) :
    rules.normal x = rules.normal y :=
  (rules.normal_trace joined.left).trans (rules.normal_trace joined.right).symm

theorem normal_chain {x y : rules.State} (chain : Chain rules.Step x y) :
    rules.normal x = rules.normal y :=
  Chain.invariant rules.normal (fun step => rules.normal_step step) chain

def joinOfChain {x y : rules.State} (chain : Chain rules.Step x y) :
    Join rules.Step x y := rules.joinOfNormalEq (rules.normal_chain chain)

def confluence {x y z : rules.State} (left : Trace rules.Step x y)
    (right : Trace rules.Step x z) : Join rules.Step y z :=
  rules.joinOfNormalEq ((rules.normal_trace left).symm.trans (rules.normal_trace right))

theorem normal_eq_iff_join (x y : rules.State) :
    rules.normal x = rules.normal y ↔ Nonempty (Join rules.Step x y) :=
  ⟨fun same => ⟨rules.joinOfNormalEq same⟩, fun ⟨joined⟩ => rules.normal_join joined⟩

theorem normal_eq_iff_chain (x y : rules.State) :
    rules.normal x = rules.normal y ↔ Nonempty (Chain rules.Step x y) := by
  constructor
  · intro same
    let joined := rules.joinOfNormalEq same
    exact ⟨(Chain.ofTrace joined.left).append (Chain.ofTrace joined.right).reverse⟩
  · intro ⟨chain⟩
    exact rules.normal_chain chain

theorem trace_length_le {x y : rules.State} (path : Trace rules.Step x y) :
    path.length ≤ rules.rank x := by
  induction path with
  | nil => exact Nat.zero_le _
  | cons first tail ih =>
    exact Nat.le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt (rules.decreases first))

theorem normalize_length_le (x : rules.State) :
    (rules.normalize x).trace.length ≤ rules.rank x :=
  rules.trace_length_le _

end RelationalFoundations.CertifiedGrouping.Rules
/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.CertifiedGrouping.Rules.normalizeWithin
#print axioms RelationalFoundations.CertifiedGrouping.Rules.normalize
#print axioms RelationalFoundations.CertifiedGrouping.Rules.terminal_unique
#print axioms RelationalFoundations.CertifiedGrouping.Rules.normal_idempotent
#print axioms RelationalFoundations.CertifiedGrouping.Rules.joinOfNormalEq
#print axioms RelationalFoundations.CertifiedGrouping.Rules.joinOfChain
#print axioms RelationalFoundations.CertifiedGrouping.Rules.confluence
#print axioms RelationalFoundations.CertifiedGrouping.Rules.normal_eq_iff_chain
#print axioms RelationalFoundations.CertifiedGrouping.Rules.normalize_length_le
/- AXIOM_AUDIT_END -/
