import RelationalFoundations.Perimetral
import RelationalFoundations.FormationAtOccurrence
import RelationalFoundations.MarkedQuantity
set_option genInjectivity false

namespace RelationalFoundations.Perimetral

inductive SortName
  | role | occurrence | node | explicit | implicit | compatibility
  | formation | provenance | history | fullRole | finalRole

inductive Symbol
  | realization | source | target | compatibility | actualWitness | formation | provenance
  | precedes | adjacent | composition | closing | internalBranch | finalBranch

inductive Port
  | left | middle | right

def sortAt : Symbol → Port → SortName
  | .realization => fun port => match port with
    | .left => .role
    | .middle | .right => .occurrence
  | .source | .target => fun port => match port with
    | .left => .occurrence
    | .middle | .right => .node
  | .actualWitness => fun port => match port with
    | .left => .occurrence
    | .middle | .right => .compatibility
  | .formation => fun port => match port with
    | .left => .occurrence
    | .middle | .right => .formation
  | .provenance => fun port => match port with
    | .left => .occurrence
    | .middle | .right => .provenance
  | .compatibility | .closing => fun port => match port with
    | .left => .implicit
    | .middle => .explicit
    | .right => .compatibility
  | .precedes | .adjacent => fun _ => .occurrence
  | .composition => fun _ => .history
  | .internalBranch => fun port => match port with
    | .left => .fullRole
    | .middle | .right => .role
  | .finalBranch => fun port => match port with
    | .left => .fullRole
    | .middle | .right => .finalRole

def signature : ConstitutiveSignature := ⟨SortName, Symbol, fun _ => Port, sortAt⟩

def Carrier : SortName → Type
  | .role => presentation.InternalRole
  | .occurrence => presentation.InteriorOccurrence
  | .node => Node
  | .explicit => ExplicitToken
  | .implicit => ImplicitToken
  | .compatibility => Σ i : ImplicitToken, Σ e : ExplicitToken, Compatible i e
  | .formation => Σ target : Node, Formation Next Node.first target
  | .provenance => Σ target : Node, Σ f : Formation Next Node.first target, Formation.Record f
  | .history => Σ source : Node, Σ target : Node, History Next source target
  | .fullRole => presentation.FullRole
  | .finalRole => presentation.FinalRole

structure ComposablePair where
  source : Node
  middle : Node
  target : Node
  first : History Next source middle
  second : History Next middle target

def Witness : Symbol → Type
  | .realization => interiorQuantity.Witness
  | .source | .target | .actualWitness | .formation | .provenance => presentation.InteriorOccurrence
  | .compatibility => Carrier .compatibility
  | .precedes => Σ first : presentation.InteriorOccurrence, Σ second : presentation.InteriorOccurrence,
      PLift (History.OccurrencePrecedes first second)
  | .adjacent => Σ first : presentation.InteriorOccurrence, Σ second : presentation.InteriorOccurrence,
      PLift (History.OccurrenceNext first second)
  | .composition => ComposablePair
  | .closing => Compatible presentation.boundary.terminal presentation.boundary.initial
  | .internalBranch => presentation.InternalRole
  | .finalBranch => presentation.FinalRole

def incidence (symbol : Symbol) : Witness symbol → (port : Port) → Carrier (sortAt symbol port) :=
  match symbol with
  | .realization => fun witness port => match port with
    | .left => witness.1
    | .middle | .right => witness.2.1
  | .source => fun occurrence port => match port with
    | .left => occurrence
    | .middle | .right => occurrence.locatedStep.source
  | .target => fun occurrence port => match port with
    | .left => occurrence
    | .middle | .right => occurrence.locatedStep.target
  | .compatibility => fun witness port => match port with
    | .left => witness.1
    | .middle => witness.2.1
    | .right => witness
  | .actualWitness => fun occurrence port => match port with
    | .left => occurrence
    | .middle | .right =>
      ⟨implicit occurrence.locatedStep.source, explicit occurrence.locatedStep.target, occurrence.locatedStep.step⟩
  | .formation => fun occurrence port => match port with
    | .left => occurrence
    | .middle | .right => ⟨occurrence.prefix.1, occurrence.formation⟩
  | .provenance => fun occurrence port => match port with
    | .left => occurrence
    | .middle | .right => ⟨occurrence.prefix.1, occurrence.formation, occurrence.currentRecord⟩
  | .precedes => fun witness port => match port with
    | .left => witness.1
    | .middle | .right => witness.2.1
  | .adjacent => fun witness port => match port with
    | .left => witness.1
    | .middle | .right => witness.2.1
  | .composition => fun pair port => match port with
    | .left => ⟨pair.source, pair.middle, pair.first⟩
    | .middle => ⟨pair.middle, pair.target, pair.second⟩
    | .right => ⟨pair.source, pair.target, History.append pair.first pair.second⟩
  | .closing => fun witness port => match port with
    | .left => presentation.boundary.terminal
    | .middle => presentation.boundary.initial
    | .right => ⟨presentation.boundary.terminal, presentation.boundary.initial, witness⟩
  | .internalBranch => fun role port => match port with
    | .left => .inl role
    | .middle | .right => role
  | .finalBranch => fun role port => match port with
    | .left => .inr role
    | .middle | .right => role

def signatureInterpretation : SignatureInterpretation signature := ⟨Carrier, Witness, incidence⟩

def equippedQuantity : EquippedQuantity signature Symbol.realization Port.left Port.middle where
  interpretation := signatureInterpretation
  Realizes := presentation.InteriorRealizes
  exact := presentation.interiorRealization
  graph := id
  graphRole := fun _ => rfl
  graphOccurrence := fun _ => rfl

inductive Mark
  | junction | finalRole

def distinguishedSignature : DistinguishedSignature signature :=
  ⟨Mark, fun mark => match mark with | .junction => .closing | .finalRole => .finalBranch⟩

def circularQuantity : MarkedQuantity Symbol.realization Port.left Port.middle distinguishedSignature where
  equipped := equippedQuantity
  distinguished := fun mark => match mark with
    | .junction => presentation.junction
    | .finalRole => BoundaryFinalRole.final

def circularIdentity : MarkedQuantityEquiv circularQuantity circularQuantity := .identity _

theorem composition_graph_actual (pair : ComposablePair) :
    incidence .composition pair .right =
      ⟨pair.source, pair.target, History.append pair.first pair.second⟩ := rfl

theorem provenance_graph_actual (o : presentation.InteriorOccurrence) :
    incidence .provenance o .middle = ⟨o.prefix.1, o.formation, o.currentRecord⟩ := rfl

theorem signature_preserves_source
    (f : SignatureTransport signatureInterpretation signatureInterpretation)
    (o : presentation.InteriorOccurrence) :
    (f.sorts SortName.node).forward o.locatedStep.source =
      ((f.sorts SortName.occurrence).forward o).locatedStep.source := by
  have occurrenceExact := f.incidenceExact Symbol.source o Port.left
  have sourceExact := f.incidenceExact Symbol.source o Port.middle
  change (f.sorts SortName.occurrence).forward o = (f.witnesses Symbol.source).forward o at occurrenceExact
  change (f.sorts SortName.node).forward o.locatedStep.source =
    ((f.witnesses Symbol.source).forward o).locatedStep.source at sourceExact
  exact sourceExact.trans (congrArg (fun occurrence => occurrence.locatedStep.source) occurrenceExact.symm)

theorem signature_preserves_actual_compatibility
    (f : SignatureTransport signatureInterpretation signatureInterpretation)
    (o : presentation.InteriorOccurrence) :
    (f.sorts SortName.compatibility).forward
      ⟨implicit o.locatedStep.source, explicit o.locatedStep.target, o.locatedStep.step⟩ =
    incidence Symbol.actualWitness ((f.sorts SortName.occurrence).forward o) Port.middle := by
  have occurrenceExact := f.incidenceExact Symbol.actualWitness o Port.left
  have compatibilityExact := f.incidenceExact Symbol.actualWitness o Port.middle
  change (f.sorts SortName.occurrence).forward o = (f.witnesses Symbol.actualWitness).forward o at occurrenceExact
  exact compatibilityExact.trans
    (congrArg (fun occurrence => incidence Symbol.actualWitness occurrence Port.middle) occurrenceExact.symm)

theorem signature_preserves_composition_graph
    (f : SignatureTransport signatureInterpretation signatureInterpretation) (pair : ComposablePair) :
    (f.sorts SortName.history).forward ⟨pair.source, pair.target, History.append pair.first pair.second⟩ =
      incidence Symbol.composition ((f.witnesses Symbol.composition).forward pair) Port.right :=
  f.incidenceExact Symbol.composition pair Port.right

end RelationalFoundations.Perimetral
