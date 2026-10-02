import RelationalFoundations.InteriorDelimitation
import RelationalFoundations.FormationAtOccurrence
import RelationalFoundations.MarkedQuantity
set_option genInjectivity false

namespace RelationalFoundations.CircularSignature
universe u v t i c
variable (presentation : CircularPresentation.{u,v,t,i,c})

inductive SortName
  | role | occurrence | node | explicit | implicit | compatibility
  | formation | provenance | history | fullRole | finalRole | stepWitness

inductive Symbol
  | realization | source | target | compatibility | actualWitness | formation | provenance
  | precedes | adjacent | composition | closing | internalBranch | finalBranch
  | formationInitial | formationAdvance | formationTarget
  | recordFormation | recordStep | recordCurrent | recordPreserved
  | stepSource | stepTarget | terminalInterface | initialInterface

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
    | .middle | .right => .stepWitness
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
  | .formationInitial | .formationTarget => fun port => match port with
    | .left => .formation
    | .middle | .right => .node
  | .formationAdvance => fun port => match port with
    | .left => .formation
    | .middle => .stepWitness
    | .right => .formation
  | .recordFormation | .recordCurrent => fun port => match port with
    | .left => .provenance
    | .middle | .right => .formation
  | .recordStep => fun port => match port with
    | .left => .provenance
    | .middle | .right => .stepWitness
  | .recordPreserved => fun port => match port with
    | .left => .provenance
    | .middle => .stepWitness
    | .right => .provenance
  | .stepSource | .stepTarget => fun port => match port with
    | .left => .stepWitness
    | .middle | .right => .node
  | .terminalInterface => fun port => match port with
    | .left => .node
    | .middle | .right => .implicit
  | .initialInterface => fun port => match port with
    | .left => .node
    | .middle | .right => .explicit

def signature : ConstitutiveSignature := ⟨SortName, Symbol, fun _ => Port, sortAt⟩

def Carrier : SortName → Type (max u v t i c)
  | .stepWitness => ULift.{max u v t i c} (History.LocatedStep presentation.Next)
  | .role => ULift.{max u v t i c} (presentation.InternalRole)
  | .occurrence => ULift.{max u v t i c} (presentation.InteriorOccurrence)
  | .node => ULift.{max u v t i c} (presentation.Node)
  | .explicit => ULift.{max u v t i c} (presentation.Initial)
  | .implicit => ULift.{max u v t i c} (presentation.Terminal)
  | .compatibility => ULift.{max u v t i c} (Σ i : presentation.Terminal, Σ e : presentation.Initial, presentation.Close i e)
  | .formation => ULift.{max u v t i c} (Σ target : presentation.Node, Formation presentation.Next presentation.start target)
  | .provenance => ULift.{max u v t i c} (Σ target : presentation.Node, Σ f : Formation presentation.Next presentation.start target, Formation.Record f)
  | .history => ULift.{max u v t i c} (Σ source : presentation.Node, Σ target : presentation.Node, History presentation.Next source target)
  | .fullRole => ULift.{max u v t i c} (presentation.FullRole)
  | .finalRole => ULift.{max u v t i c} (presentation.FinalRole)

structure ComposablePair (presentation : CircularPresentation.{u,v,t,i,c}) where
  source : presentation.Node
  middle : presentation.Node
  target : presentation.Node
  first : History presentation.Next source middle
  second : History presentation.Next middle target

structure FormationAdvance (presentation : CircularPresentation.{u,v,t,i,c}) where
  source : presentation.Node
  target : presentation.Node
  previous : Formation presentation.Next presentation.start source
  step : presentation.Next source target

structure PreservedRecord (presentation : CircularPresentation.{u,v,t,i,c}) extends FormationAdvance presentation where
  record : Formation.Record previous

def Witness : Symbol → Type (max u v t i c)
  | .realization => ULift.{max u v t i c} ((Σ role : presentation.InternalRole, Σ occurrence : presentation.InteriorOccurrence, presentation.InteriorRealizes role occurrence))
  | .source | .target | .actualWitness | .formation | .provenance => ULift.{max u v t i c} (presentation.InteriorOccurrence)
  | .compatibility => ULift.{max u v t i c} (Σ i : presentation.Terminal, Σ e : presentation.Initial, presentation.Close i e)
  | .precedes => ULift.{max u v t i c} (Σ first : presentation.InteriorOccurrence, Σ second : presentation.InteriorOccurrence,
      PLift (History.OccurrencePrecedes first second))
  | .adjacent => ULift.{max u v t i c} (Σ first : presentation.InteriorOccurrence, Σ second : presentation.InteriorOccurrence,
      PLift (History.OccurrenceNext first second))
  | .composition => ULift.{max u v t i c} ((ComposablePair presentation))
  | .closing => ULift.{max u v t i c} (presentation.Close presentation.boundary.terminal presentation.boundary.initial)
  | .internalBranch => ULift.{max u v t i c} (presentation.InternalRole)
  | .finalBranch => ULift.{max u v t i c} (presentation.FinalRole)
  | .formationInitial => ULift.{max u v t i c} Unit
  | .formationAdvance | .recordCurrent => ULift.{max u v t i c} (FormationAdvance presentation)
  | .formationTarget => Carrier presentation .formation
  | .recordFormation | .recordStep => Carrier presentation .provenance
  | .recordPreserved => ULift.{max u v t i c} (PreservedRecord presentation)
  | .stepSource | .stepTarget => Carrier presentation .stepWitness
  | .terminalInterface | .initialInterface => ULift.{max u v t i c} presentation.Node

def incidence (symbol : Symbol) : (Witness presentation) symbol → (port : Port) → (Carrier presentation) (sortAt symbol port) :=
  match symbol with
  | .realization => fun witness port => match port with
    | .left => ⟨witness.down.1⟩
    | .middle | .right => ⟨witness.down.2.1⟩
  | .source => fun occurrence port => match port with
    | .left => ⟨occurrence.down⟩
    | .middle | .right => ⟨occurrence.down.locatedStep.source⟩
  | .target => fun occurrence port => match port with
    | .left => ⟨occurrence.down⟩
    | .middle | .right => ⟨occurrence.down.locatedStep.target⟩
  | .compatibility => fun witness port => match port with
    | .left => ⟨witness.down.1⟩
    | .middle => ⟨witness.down.2.1⟩
    | .right => ⟨witness.down⟩
  | .actualWitness => fun occurrence port => match port with
    | .left => ⟨occurrence.down⟩
    | .middle | .right => ⟨occurrence.down.locatedStep⟩
  | .formation => fun occurrence port => match port with
    | .left => ⟨occurrence.down⟩
    | .middle | .right => ⟨⟨occurrence.down.prefix.1, occurrence.down.formation⟩⟩
  | .provenance => fun occurrence port => match port with
    | .left => ⟨occurrence.down⟩
    | .middle | .right => ⟨⟨occurrence.down.prefix.1, occurrence.down.formation, occurrence.down.currentRecord⟩⟩
  | .precedes => fun witness port => match port with
    | .left => ⟨witness.down.1⟩
    | .middle | .right => ⟨witness.down.2.1⟩
  | .adjacent => fun witness port => match port with
    | .left => ⟨witness.down.1⟩
    | .middle | .right => ⟨witness.down.2.1⟩
  | .composition => fun pair port => match port with
    | .left => ⟨⟨pair.down.source, pair.down.middle, pair.down.first⟩⟩
    | .middle => ⟨⟨pair.down.middle, pair.down.target, pair.down.second⟩⟩
    | .right => ⟨⟨pair.down.source, pair.down.target, History.append pair.down.first pair.down.second⟩⟩
  | .closing => fun witness port => match port with
    | .left => ⟨presentation.boundary.terminal⟩
    | .middle => ⟨presentation.boundary.initial⟩
    | .right => ⟨⟨presentation.boundary.terminal, presentation.boundary.initial, witness.down⟩⟩
  | .internalBranch => fun role port => match port with
    | .left => ⟨.inl role.down⟩
    | .middle | .right => ⟨role.down⟩
  | .finalBranch => fun role port => match port with
    | .left => ⟨.inr role.down⟩
    | .middle | .right => ⟨role.down⟩
  | .formationInitial => fun _ port => match port with
    | .left => ⟨presentation.start, Formation.initial⟩
    | .middle | .right => ⟨presentation.start⟩
  | .formationAdvance => fun advance port => match port with
    | .left => ⟨advance.down.source, advance.down.previous⟩
    | .middle => ⟨advance.down.source, advance.down.target, advance.down.step⟩
    | .right => ⟨advance.down.target, .formed advance.down.previous advance.down.step⟩
  | .formationTarget => fun formation port => match port with
    | .left => formation
    | .middle | .right => ⟨formation.down.1⟩
  | .recordFormation => fun record port => match port with
    | .left => record
    | .middle | .right => ⟨record.down.1, record.down.2.1⟩
  | .recordStep => fun record port => match port with
    | .left => record
    | .middle | .right => ⟨record.down.2.2.located⟩
  | .recordCurrent => fun advance port => match port with
    | .left => ⟨advance.down.target, .formed advance.down.previous advance.down.step, .current⟩
    | .middle | .right => ⟨advance.down.target, .formed advance.down.previous advance.down.step⟩
  | .recordPreserved => fun record port => match port with
    | .left => ⟨record.down.source, record.down.previous, record.down.record⟩
    | .middle => ⟨record.down.source, record.down.target, record.down.step⟩
    | .right => ⟨record.down.target, .formed record.down.previous record.down.step, .preserved record.down.record⟩
  | .stepSource => fun step port => match port with
    | .left => step
    | .middle | .right => ⟨step.down.source⟩
  | .stepTarget => fun step port => match port with
    | .left => step
    | .middle | .right => ⟨step.down.target⟩
  | .terminalInterface => fun node port => match port with
    | .left => node
    | .middle | .right => ⟨presentation.terminalInterface node.down⟩
  | .initialInterface => fun node port => match port with
    | .left => node
    | .middle | .right => ⟨presentation.initialInterface node.down⟩

def signatureInterpretation : SignatureInterpretation signature := ⟨(Carrier presentation), (Witness presentation), (incidence presentation)⟩

def equippedQuantity : EquippedQuantity signature Symbol.realization Port.left Port.middle where
  interpretation := (signatureInterpretation presentation)
  Realizes := fun role occurrence => ULift.{max u v t i c} (presentation.InteriorRealizes role.down occurrence.down)
  exact :=
    { transport :=
        { forward := fun role => ⟨Spine.realize role.down⟩
          backward := fun occurrence => ⟨Spine.decode presentation.spine occurrence.down⟩
          forwardBackward := fun role => congrArg ULift.up (Spine.decode_realize role.down)
          backwardForward := fun occurrence => congrArg ULift.up (Spine.realize_decode presentation.spine occurrence.down) }
      agreement := fun role => ⟨presentation.interiorRealization.agreement role.down⟩ }
  graph := fun witness => ⟨witness.1.down, witness.2.1.down, witness.2.2.down⟩
  graphRole := fun _ => rfl
  graphOccurrence := fun _ => rfl
inductive Mark
  | junction | finalRole

def distinguishedSignature : DistinguishedSignature signature :=
  ⟨Mark, fun mark => match mark with | .junction => .closing | .finalRole => .finalBranch⟩

def circularQuantity : MarkedQuantity Symbol.realization Port.left Port.middle distinguishedSignature where
  equipped := (equippedQuantity presentation)
  distinguished := fun mark => match mark with
    | .junction => ⟨presentation.junction⟩
    | .finalRole => ⟨BoundaryFinalRole.final⟩

def circularIdentity : MarkedQuantityEquiv (circularQuantity presentation) (circularQuantity presentation) := .identity _

variable {presentation} {other : CircularPresentation.{u,v,t,i,c}}

theorem preserves_formation_constructor
    (transport : SignatureTransport (signatureInterpretation presentation) (signatureInterpretation other))
    (advance : FormationAdvance presentation) :
    (transport.sorts .formation).forward ⟨advance.target, .formed advance.previous advance.step⟩ =
      incidence other .formationAdvance ((transport.witnesses .formationAdvance).forward ⟨advance⟩) .right :=
  transport.incidenceExact .formationAdvance ⟨advance⟩ .right

theorem preserves_historical_record
    (transport : SignatureTransport (signatureInterpretation presentation) (signatureInterpretation other))
    (record : PreservedRecord presentation) :
    (transport.sorts .provenance).forward
      ⟨record.target, .formed record.previous record.step, .preserved record.record⟩ =
      incidence other .recordPreserved ((transport.witnesses .recordPreserved).forward ⟨record⟩) .right :=
  transport.incidenceExact .recordPreserved ⟨record⟩ .right

theorem preserves_terminal_boundary
    (transport : MarkedQuantityEquiv (circularQuantity presentation) (circularQuantity other)) :
    (transport.equipped.signature.sorts .implicit).forward ⟨presentation.boundary.terminal⟩ =
      ⟨other.boundary.terminal⟩ := transport.equipped.signature.incidenceExact .closing ⟨presentation.junction⟩ .left

theorem preserves_initial_boundary
    (transport : MarkedQuantityEquiv (circularQuantity presentation) (circularQuantity other)) :
    (transport.equipped.signature.sorts .explicit).forward ⟨presentation.boundary.initial⟩ =
      ⟨other.boundary.initial⟩ := transport.equipped.signature.incidenceExact .closing ⟨presentation.junction⟩ .middle

theorem preserves_junction
    (transport : MarkedQuantityEquiv (circularQuantity presentation) (circularQuantity other)) :
    (transport.equipped.signature.witnesses .closing).forward ⟨presentation.junction⟩ = ⟨other.junction⟩ :=
  transport.preserves .junction

end RelationalFoundations.CircularSignature
