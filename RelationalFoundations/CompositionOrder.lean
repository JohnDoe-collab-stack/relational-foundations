import RelationalFoundations.Spine
set_option genInjectivity false

namespace RelationalFoundations
universe u v
namespace History
variable {State : Type u} {Step : State → State → Type v}

theorem left_precedes_right {a b c : State} {h : History Step a b} {k : History Step b c}
    (old : Occurrence h) (new : Occurrence k) :
    OccurrencePrecedes (embedLeftOccurrence old k) (embedRightOccurrence h new) := by
  induction new with
  | last => exact .earlier_last _
  | earlier new ih => exact .earlier_earlier ih

theorem precedes_embedRight {a b c : State} (h : History Step a b) {k : History Step b c}
    {first second : Occurrence k} (relation : OccurrencePrecedes first second) :
    OccurrencePrecedes (embedRightOccurrence h first) (embedRightOccurrence h second) := by
  induction relation with
  | earlier_last old => exact .earlier_last _
  | earlier_earlier _ ih => exact .earlier_earlier ih

theorem next_embedRight {a b c : State} (h : History Step a b) {k : History Step b c}
    {first second : Occurrence k} (relation : OccurrenceNext first second) :
    OccurrenceNext (embedRightOccurrence h first) (embedRightOccurrence h second) := by
  induction relation with
  | previous_last => exact .previous_last
  | earlier_earlier _ ih => exact .earlier_earlier ih

theorem next_first_two {a b c d : State} (first : Step a b) (second : Step b c)
    (rest : History Step c d) :
    OccurrenceNext
      (embedLeftOccurrence (.last : Occurrence (.extend .root first))
        (append (.extend .root second) rest))
      (embedRightOccurrence (.extend .root first)
        (embedLeftOccurrence (.last : Occurrence (.extend .root second)) rest)) := by
  induction rest with
  | root => exact .previous_last
  | extend rest step ih => exact .earlier_earlier ih

end History

namespace Spine
variable {Node : Type u} {Next : Node → Node → Type v}

theorem precedes_realize {node : Node} {s : Spine Next node} {first second : Position s}
    (relation : Precedes first second) : History.OccurrencePrecedes (realize first) (realize second) := by
  induction relation with
  | here_later position => exact History.left_precedes_right _ _
  | later_later _ ih => exact History.precedes_embedRight _ ih

theorem adjacent_realize {node : Node} {s : Spine Next node} {first second : Position s}
    (relation : Adjacent first second) : History.OccurrenceNext (realize first) (realize second) := by
  induction relation with
  | here_next => exact History.next_first_two _ _ _
  | later_next _ ih => exact History.next_embedRight _ ih

end Spine
end RelationalFoundations
