import RelationalFoundations.NativeForgettingBridgeV1
set_option genInjectivity false

/-! Every input in a typed stack precedes its consumer; this is a property of the concrete support datatype. -/

namespace RelationalFoundations.TypedResourceOrder
open RelationalFoundations RelationalFoundations.TypedResources
open RelationalFoundations.NativeForgettingV1 (address address_bound)

def anyAddress {context : List Kind} : AnyRef context → Nat
  | .number ref => address ref
  | .truth ref => address ref

theorem old_address {context : List Kind} {added : Kind} (x : AnyRef context) :
    anyAddress (AnyRef.map (fun _ => Ref.old (added := added)) x) = anyAddress x := by
  cases x <;> rfl

theorem pack_address {context : List Kind} : (kind : Kind) → (ref : Ref context kind) →
    anyAddress (AnyRef.pack kind ref) = address ref
  | .number, _ => rfl
  | .truth, _ => rfl

theorem operation_inputs_bounded {context : List Kind} {kind : Kind} (op : Operation context kind)
    (x : AnyRef context) (member : x ∈ op.inputs) : anyAddress x < context.length := by
  cases op with
  | literal _ => cases member
  | test n =>
      cases member with
      | head => exact address_bound n
      | tail _ rest => cases rest
  | adjust f n =>
      cases member with
      | head => exact address_bound f
      | tail _ rest =>
          cases rest with
          | head => exact address_bound n
          | tail _ rest => cases rest
  | reuse ref =>
      cases member with
      | head => exact (pack_address _ ref).symm ▸ address_bound ref
      | tail _ rest => cases rest

theorem inputs_precede : {context : List Kind} → (support : Support context) → (kind : Kind) →
    (ref : Ref context kind) → (x : AnyRef context) → x ∈ (support.nodeAt kind ref).inputs →
    anyAddress x < address ref
  | _, .push previous op, _, .head, x, member => by
      have mem : x ∈ op.inputs.map (AnyRef.map (fun _ => Ref.old)) :=
        (Operation.inputs_map (fun _ => Ref.old) op) ▸ member
      obtain ⟨y, yMem, yEq⟩ := ResourceGraph.Enumeration.map_origin _ _ mem
      rw [← yEq, old_address]
      exact operation_inputs_bounded op y yMem
  | _, .push previous _, kind, .old ref, x, member => by
      have mem : x ∈ (previous.nodeAt kind ref).inputs.map (AnyRef.map (fun _ => Ref.old)) :=
        (Operation.inputs_map (fun _ => Ref.old) (previous.nodeAt kind ref)) ▸ member
      obtain ⟨y, yMem, yEq⟩ := ResourceGraph.Enumeration.map_origin _ _ mem
      rw [← yEq, old_address]
      exact inputs_precede previous kind ref y yMem

end RelationalFoundations.TypedResourceOrder

/- AXIOM_AUDIT_BEGIN -/
#print axioms RelationalFoundations.TypedResourceOrder.anyAddress
#print axioms RelationalFoundations.TypedResourceOrder.old_address
#print axioms RelationalFoundations.TypedResourceOrder.pack_address
#print axioms RelationalFoundations.TypedResourceOrder.operation_inputs_bounded
#print axioms RelationalFoundations.TypedResourceOrder.inputs_precede
/- AXIOM_AUDIT_END -/
