import RelationalFoundations.ExactTransport
set_option linter.defProp false
universe u v
abbrev ExactTypeTransport (A : Type u) (B : Type v) := RelationalFoundations.ExactTransport A B
set_option linter.checkUnivs false
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («backward»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («backward_eq_of_forward_eq»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («compose»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («ofEquality»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («backwardForward»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («ctorIdx»)
end ExactTypeTransport
namespace ExactTypeTransport.mk
export RelationalFoundations.ExactTransport.mk («sizeOf_spec»)
end ExactTypeTransport.mk
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («mk»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («sumUnit»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («forward»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («reverse»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («reflexive»)
end ExactTypeTransport
namespace ExactTypeTransport
export RelationalFoundations.ExactTransport («forwardBackward»)
end ExactTypeTransport
