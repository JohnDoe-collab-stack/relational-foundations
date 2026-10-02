## Foreword

*Mathematicians now have, with Lean, a proof tool precise enough to compare not
only the results proved, but the meanings that proofs acquire according to the
formal ontologies in which they are situated.*

*`Relational Perimeter` puts this possibility to the test by treating relations
as primitives of formal constitution. From this choice, it re-examines the
meanings of familiar notions such as role, perimeter, circularity, closure,
whole, residual, transport, and turning. It follows their constitution in the
types: which relations are primitive, which witnesses are given, which
occurrences are generated, which relations are preserved by transports, and
which data are actually consumed by proofs.*

*In this sense, the framework is endogenous relative to the primitive
presentation it receives. It does not generate its own primitives; within a
single typed architecture, it constructs or establishes the identities, roles,
histories, exact quantity of the perimeter, and changes of status that proceed
from them.*

*The carrier, understood as the formal support equipped with its structure, is
not neutral. In the four-node example, separating models show that local data
alone determine neither order nor participation in the whole. For every
presentation, returning to a rooted, composable history then makes it possible
to reconstruct order, adjacency, and factorization from the global constitution
of the object.*

*The scope of this formalization goes beyond a mere terminological refinement.
By stratifying construction, realization, admission, and satisfaction of a
specification, it shifts the very criteria of identity and completeness. An
occurrence receives its identity from the relational history that constitutes
it, not from its value alone. A whole is complete when its relations positively
determine its interior domain, not when it exhausts every possible continuation.
What might appear as incompleteness then becomes the non-exhaustion of
generation. The affirmative perimetral turning designates the exact point at
which, beyond an already constituted and complete whole, generation produces a
continuation outside the regime in which that whole is maximal.*

*The perimeter thus determines an exact quantity whose exactness does not
depend on numerical evaluation. This quantity is carried by the reversible
correspondence between the successive positions and the occurrences of the
deployment; their order and adjacency are established by distinct structural
relations. The closing place completes the circular system of requirements
without entering this interior quantity, since it is not generated as an
occurrence. `History.length` provides only a subsequent, derived numerical
reading of it.*

*The methodological distinction between theorem and chain extends this
stratification without opposing them as two unrelated terms. The theorem
expresses a terminal propositional result; the chain retains the relations,
witnesses, provenances, and typed dependencies within which its proof acquires
its meaning. The same theorem may be situated in different constitutive chains;
conversely, a chain may carry more structure than the theorem's minimal logical
proof actually consumes. Comparison therefore holds together what proofs
establish and the relational constitution within which they establish it.*

*This approach makes comparable what terminal theorems alone leave invisible.
Two systems may establish similar propositional results while giving objects
and proofs different relational constitutions, and therefore different
meanings. The relational constitution of the perimeter, circularity, and the
affirmative perimetral turning provide the formal setting in which this method
is deployed.*

<br>

# Primitive Relations and the Constitution of the Perimeter

### Circularity, residual role, and affirmative perimetral turning

The four files studied here form a continuous construction:

- `SegmentedResidualRole.lean` determines the residual role abstractly;
- `AbstractSegmentedTurning.lean` articulates boundary, continuation, and
  regime change;
- `ExactTypeTransport.lean` defines exact transport between types;
- `StrongPerimetralTurning.lean` realizes the whole construction in a
  constructive circular presentation.

Their common feature is that they treat relations as constitutive parts of
formal objects. An occurrence is individuated in the history in which it is
formed, and its role depends on its provenance and participation in the chain;
a perimeter is constituted by an effectively witnessed chain of relations; a
transport is exact through the correspondences it constructs; an affirmative
perimetral turning is located by the relation between a completed boundary and
its continuation.

The general architecture can be summarized as follows:

```text
one typed relational family
→ internal articulations and inter-node junctions
→ n − 1 given successive witnesses + 1 given closing witness
→ rooted deployment of n − 1 occurrences realizing the successive witnesses
→ perimeter constituted as an interior whole
→ positive continuation
→ forced occupation of the residual closing place
→ totalization required by the regime
→ rejection by the initial obstruction
→ affirmative perimetral turning and regime change
```

## Positioning and scope

This construction is a relational architecture formalized in Lean, not a
competing logical foundation. Its proof relevance, the separation of its
interfaces, and the exact limits of its affinities with transition systems,
trace semantics, free paths, and type theories are stated in the canonical
[Positioning and scope](positioning-and-scope.en.md) section.

![Relational Perimeter foundations and formal architecture](figures/relational-perimeter-formal-architecture.svg)

## 1. Relations, roles, and occurrences

The central local relation is a type family:

```lean
Compatible : Implicit → Explicit → Type uK
```

A witness of `Compatible i e` is positive data. It can be retained,
transported, and used as an index for other constructions. `LocalNode` thus
collects an explicit term, an implicit term, a difference, the provenance of
that difference, and an internal compatibility from the implicit component to
the explicit one. A node is already a relational configuration.

A **constitutive relational role** is the determination of an occurrence by
the structural relations in which it participates within a constitution. It is
not merely a label: the role may depend on the occurrence's formation, source,
target, provenance, succession, and insertion into a composable chain.

This determination presupposes that the occurrence exists before it is read. A
`History` is built from a root and composable extensions, and
`History.Occurrence` individuates a step within that precise history. A readout
function may then assign a value to the occurrence; the history remains the
principle of its identity and relations.

The exact realization of a role preserves accessible witnesses. In
`ExactInternalRealization`, two functions relate internal roles and old
occurrences, with both round-trip laws. In the perimetral instance,
`ExactNonClosingRealization` assigns to every non-closing position an
occurrence with the exact structural address. This agreement reconstructs the
complete local step and forces the realization to be injective.

Covering the internal roles nevertheless leaves room for a continuation.
Realizing every requirement exactly means that each has its faithful
occurrence; it does not automatically classify every occurrence in the history
as internal. This opening makes the positive appearance of a new role possible.

The status of properties depends on the structure of the carrier. In the
four-node example, a permuted `SemanticTrace` preserves the local steps and
their injectivity while changing their order. An interleaved trace preserves
order while failing to constitute a composable bridge between two adjacent
positions. These two separators establish the intended independence for this
presentation. When the carrier is again a `RootedGeneratedHistory`, the typed
composition of its steps and its rootedness reconstruct precedence, adjacency,
and factorization through the canonical perimeter for every presentation.

Formation relations are therefore primitive, while some of their consequences
become derivable on a carrier containing the required structure. The method
locates this boundary by weakening the carrier, producing separating models,
and then reintroducing actual composition. The files establish this positive
reconstruction; they do not state a general converse characterizing every trace
from order and contiguity.

The framework calls **relative endogeneity** the fact that a determination is
constructed or proved from primitive data explicitly carried by a typed
architecture, without a post-constitutive readout serving as its principle.
This endogeneity does not mean self-generation: relations and their witnesses
may be given. It indicates that their role, their consequences, and the statuses
that proceed from them are established within the same architecture. It thus
cuts across the distinction between given and generated, and does not coincide
with interiority.

## 2. The constituted perimeter and circularity

`PerimeterSpine` presents a chain of nodal positions without requiring the node
values to be distinct. Its advance constructor requires a witness:

```lean
Compatible node.implicit nextNode.explicit
```

Each advance relates the implicit output of one node to the explicit input of
the next. The witness of this relation is primitive data of the chain:
generation does not create it. `NonClosingPosition` designates these n − 1
successive places; `NonClosingPrecedes` expresses their precedence, and
`NonClosingNext` their immediate succession. The internal witnesses of the
nodes belong to the same `Compatible` family, but they play another role: they
are parts of the nodes, not of the type of circular requirements.

Within a rooted, composable history, `perimeterDeployment` recursively
generates the occurrences that realize the given successive witnesses. Its
non-closing positions and occurrences are related by two maps with their
round-trip laws. Every occurrence therefore has the source, target,
compatibility, and provenance imposed by its position. The final junction
plays no part in any step of this deployment.

The framework calls a structural unity a **constituted whole** when its
constitutive relations suffice to determine canonically their own domain of
interiority. Its completeness consists in this positive determination of what
is internal.

The perimeter reconstructed in this way constitutes such a whole.

Its interior domain consists of the n − 1 occurrences that realize the
successive places. The closing place completes the requirement system, but it
is not an interior occurrence of the deployment.

In the Lean types, this whole is the generated, rooted, composable history that
realizes exactly the successive junctions. Local exactness reconstructs
injectivity, order, adjacency, and factorization through the canonical
deployment. The absence of an admissible strict extension establishes its
maximality relative to the regime.

The perimeter therefore determines an exact quantity whose exactness does not
depend on numerical evaluation. This quantity is not primarily a cardinal: it
is the structured type of non-closing positions, exactly realized by the type
of occurrences in the canonical deployment. `requirementToOccurrence` and
`occurrenceToRequirement`, together with their two round-trip laws, establish
that no position is omitted and no perimeter occurrence remains outside this
realization. Order and adjacency do not follow from this correspondence alone:
they are preserved separately by
`ExactNonClosingRealization.preservesPrecedence` and
`ExactNonClosingRealization.preservesNext`, by virtue of the history being
rooted and composable. The closing place belongs to the circular system of
requirements, but not to the interior domain measured in this way, since it is
not realized by a perimeter occurrence. `History.length` then provides a
derived numerical reading of the history: it counts its extensions while
forgetting the relational structure that individuates and relates their
occurrences.
This quantitative determination is endogenous to the relational constitution
of the perimeter: `History.length` provides a numerical reading of it without
being its principle.

Circularity completes the system of inter-node requirements with a closing
place:

```lean
CircularRequirement P =
  NonClosingPosition P.perimeter ⊕ FinalRequirement P
```

The first n − 1 requirements are the successive junctions carried by the
chain. The last is a one-point place, `FinalRequirement P`, which carries no
witness; the corresponding closing pair is witnessed separately by a
primitive field of the presentation:

```lean
finalJunction :
  Compatible perimeter.finalNode.implicit initialNode.explicit
```

`finalJunction` is thus a new instance of the same inter-node family, oriented
from the terminal implicit component to the initial explicit component. Its
position in the presentation distinguishes it even when its value coincides
with another compatibility. It is given, not derived, and remains outside the
generated occurrences: the perimeter realizes the successive junctions with
occurrences without realizing the closing junction. The formal structures
retain it as distinguished data; no closure theorem consumes it to produce an
occurrence, a loop, or an identification.

The closing character of the final place designates this typed completeness of
the requirement system, not a return produced by the history: the generator
never traverses `finalJunction`, and every positive generated history advances
to a new cursor.

The presentation also contains `leftEndpoint` and `rightEndpoint`. These
endpoints are the two poles of the initial difference; they are neither the
first and last nodes nor the initial and terminal states of the history (the
canonical realization only reads them at its initial and terminal vertices).
The initial obstruction refutes their contraction. The positivity of the
history, on the other hand, distinguishes its initial and terminal vertices.
These two separations therefore have different formal sources.

`RawJunctionWithSeparatedEndpoints` brings together a closing compatibility,
canonically `finalJunction`, and the separation of the two poles. The structure
makes their coexistence explicit without deriving either from the other or
quotienting the poles. It remains compatible with the possible equality of the
initial and terminal nodes, because node identity does not define circularity.

Four interfaces express the complementary functions of this architecture:

- `CircularPresentation` provides the chain, the closing junction, the
  difference, and its obstruction;
- `perimeterDeployment` generates the history that realizes the successive
  junctions;
- `CircularRefinement` governs admission and stipulates the treatment of every
  positive continuation in the closing place;
- `CircularSpecificationSatisfaction` associates local exactness with a
  trajectory clause equivalent to the absence of every strict constitutive
  extension of the perimeter.

`noIntermediateRefinement` establishes that every history admitted by this
regime equals the canonical deployment. The perimeter is therefore complete as
a constituted whole and maximal relative to the regime, while generation
retains its capacity to produce beyond it.

## 3. From the residual role to the affirmative perimetral turning

`SegmentedResidualRole.lean` isolates residual determination from any circular
geometry. Its input consists of:

- an exact realization of internal roles by old occurrences;
- disjoint embeddings of old and new occurrences into the extension;
- a faithful labelling by `internal role ⊕ residual role` that preserves the
  internal labels of old occurrences;
- a contractible residual-role type;
- the positive existence of a new occurrence.

If a new occurrence reused the label of an internal role, label preservation
and injectivity would identify it with the old occurrence realizing that role;
disjointness excludes this identification. It therefore receives the residual
role. Because this role is contractible and the labelling is injective, all new
occurrences coincide. The positive new part has a unique residual occurrence.

The file factors this proof down to the kernel it actually consumes:

```text
FaithfulExtension
→ ResidualUniquenessKernel
→ ResidualDeterminationCore
→ CoreUniqueResidualOccurrence
```

Faithful segmentation is therefore sufficient to determine residual
uniqueness. In the circular instance, its internal roles are the n − 1 already
realized successive places, and its residual role is `FinalRequirement`, the
unique closing place still available. This role remains distinct from
`finalJunction`: the first is a one-point role that classifies an occurrence,
whereas the second is the primitive relational witness of the closing pair. No
type identifies them; `FinalClosureInterpretation` subsequently places them
side by side at the terminal boundary.

Once the perimeter has been deployed, `oneStepAfterPerimeter` effectively
constructs one additional step. In every injective labelling that preserves the
old places, this new occurrence is forced into the closing place: reusing a
successive place would identify it with an old occurrence. The contractibility
of `FinalRequirement` then forces the new part to be unique. The residual is
thus determined, not chosen.

`FinalClosureInterpretation` then retains two relations issuing from the
terminal implicit term:

```text
actual free step : terminal implicit → newly formed explicit
final junction   : terminal implicit → initial explicit
```

The structure retains them side by side, without identification, composition,
or application of one to the other. It is entirely determined by the boundary
occurrence. It also records the formation of the actual step, the provenance
of its source, and the obstruction inherited from the initial difference.

`ResidualFinalClosureInterpretation` identifies the same residual occurrence
with the boundary occurrence of this interpretation. The chain

```text
labelled extension
→ unique residual occurrence
→ boundary interpretation
→ totalization attempt
```

is therefore a dependently typed production. It does not, however, constitute
a logical dependency of the refutation: an attempt can be reindexed over
another interpretation, and the final rejection consumes no data from the
residual occurrence.

`CircularRefinement.realizesFinal` stipulates that every positive continuation
admitted in the same regime must provide a bilateral closure attempt. This
obligation is not derived from `finalJunction`. Explicit and implicit
totalizations require a single component to represent both poles of the
initial difference; each therefore reconstructs their contraction.

The obstruction is inscribed at the root and inherited unchanged through
successive formations. The constitutive rejection proof consumes this
obstruction at the terminal boundary, whereas the minimal logical proof of the
impossibility of totalization can already be carried out from the initial
fields of the presentation. The step remains constructed and exactly located;
what is refused is its admission into the same regime.

`AbstractSegmentedTurning.lean` extracts the general form of this mechanism. A
`BoundaryGenerator` supplies a canonical boundary, a strict continuation, and
the extension relation. A segmented boundary supplies the unique residual
occurrence. An `ObstructedRegime` classifies every admitted candidate between
equality with the boundary and a totalization attempt, and then rejects the
second branch.

`TurningConclusion` then assembles the witnesses of the construction and their
exact consequences:

- the unique residual occurrence;
- the effectively generated continuation;
- its constructive distinction from the boundary;
- the exact classification of the regime;
- the continuation's position outside that regime;
- the impossibility of a strict extension within the same regime;
- the rejection of totalization.

The perimetral turning is affirmative because it proceeds from the effective
constitution of a continuation. The structures `PositiveContinuation`,
`PositiveNewPart`, and `PositiveResidualBoundary` carry its positive witnesses
in the types: a new step and a residual occurrence are effectively given.
Their positivity means here that they are constructed, not that they are
favourable or optimal. Inadequacy for the previous regime is established
afterwards. The regime change thus results from a constituted addition, not
from a lack: **generation continues, and this continuation opens the turning**.

The turning thus establishes that the endogenous does not coincide with the
interior: the continuation is produced by the framework's own generation while
lying beyond the perimeter and outside the regime in which that perimeter is
maximal.

In the perimetral instance, this turning is the first step generated beyond the
perimeter. Its occurrence is still faithfully labelable in the circular
system, whose unique residual place it occupies, and the step remains exactly
interpretable in every `ConcreteContinuationAlgebra`. Two steps beyond the
perimeter remain constituted and locally exact but can no longer receive such
a faithful labelling. The turning therefore marks the exact boundary between
the continuation that can still be classified by the circular role system and
the further course of generation.

The same architecture finally distinguishes admission from satisfaction.
`CircularSpecificationSatisfaction` associates local exactness with a
trajectory requirement formulated independently of `CircularRefinement`.
Because `TotalLoop` is refuted in every presentation, this requirement has
exactly the logical content “no strict constitutive extension of the
perimeter.” Its soundness and completeness with respect to
`CircularRefinement` establish that regime and specification classify the same
histories by distinct witnesses. `oneStepAfterPerimeter` preserves local
exactness and the possibility of further extension while leaving both the
regime and the specification. Constitution, local exactness, faithful
labelling, and admission therefore remain four distinct statuses.

## 4. Exact transport and comparative method

`ExactTypeTransport.lean` defines a constructive correspondence by two
functions and their two round-trip laws:

```lean
forward  : Source → Target
backward : Target → Source

backward (forward source) = source
forward (backward target) = target
```

The transport is reversible and composable. `sumUnit` extends it with an
unchanged one-point component placed on the right of a sum. This structure is
independent of a constitution, regime, specification, or particular readout.

Transport exactness concerns the related types first. Preserving relations
requires additional agreements on sources, targets, steps, compatibilities,
and provenances. This separation exposes what is actually preserved: a
correspondence between carriers and a correspondence between relational
architectures are two distinct obligations.

The same precision applies to concrete realizations. An interpretation may
establish an exact correspondence between free and concrete occurrences while
merging their states or some of their read values. In particular,
`ConcreteContinuationAlgebra` does not require `interpretExplicit` to
distinguish the target of the closing junction from that of the free
continuation; a one-state algebra identifying them still satisfies
`exactlyInterpretHistory` (a construction verified outside the four files).
The distinction between the two targets is therefore guaranteed at the level
of the free constitution; preserving it concretely requires an additional
agreement.

The comparative method arising from the four files follows a short
progression:

```text
individuate
→ relate
→ test
→ reconstruct
→ transport
→ diagnose
```

**Individuating** means constructing occurrences before their readouts.
**Relating** means determining their roles through structural agreements.
**Testing** means weakening the carrier to test dependencies.
**Reconstructing** means deriving, on the full carrier, the order, adjacency,
and participation made possible by its composition. **Transporting** means
providing exact correspondences and the required relational agreements.
**Diagnosing** means retaining, on the same continuation, both what remains
constituted and the exact proof of the regime change.

Comparing two architectures then amounts to examining:

1. the relation families taken as primitive;
2. how their witnesses constitute objects, positions, and chains;
3. the carrier on which each property is primitive or reconstructed;
4. the exact correspondences between roles and occurrences;
5. the relations preserved by transports;
6. the distribution between generated and given relations;
7. the constitutive role of each datum and the proofs that actually consume it;
8. the rule governing occupation of a residual place and admission of
   continuations.

Two systems may reach similar propositional theorems while differing in their
constitution. Comparison therefore concerns the dependencies producing those
theorems: relations, witnesses, chains, transports, closures, and regime
changes.

## Extension to computation

The repository extends this method with a construction in which the operational
decomposition of a search is itself produced during execution. Opening
generates two structurally distinct alternatives. An effective search then
reconstructs a directed transport between them; this transport acts on
arbitrary continuations, while acceptance preservation is established by a
separate theorem. Absorbing one obligation is therefore relative to the
viability criterion: it neither identifies the alternatives nor proves the
absorbed one impossible.

The executed result also produces the retained state, seed, decisions, and
provenance consumed by the next stage. Structural multiplicity and operational
independence are therefore not conflated: the operational status is constituted
during the computation from relations and data that the computation has itself
reconstructed or produced. The detailed presentation and exact scope of this
result are given in
[Endogenous Operational Decomposition](endogenous-operational-decomposition.en.md).

## Conclusion

The four files give constructive form to a framework of **relative
endogeneity**: a formal architecture receives a primitive relational
presentation, then constructs the occurrences, roles, and histories that
proceed from it, while distinguishing their realizations, admissions, and
regime changes within its own types.

In the circular instance, one relational family appears in three distinct
places: internal node witnesses, successive junctions, and the closing
junction. Circularity lies in the complete system of inter-node requirements:
n − 1 successive witnesses are given with the chain and realized by the same
number of generated occurrences; one final witness is given from the terminal
implicit component to the initial explicit component.

The constituted perimeter is the rooted, composable history that realizes the
successive junctions exactly. It forms a whole because its relations positively
determine its occurrences, their order, their adjacency, and their interior
domain. The one-point closing role completes the requirement system;
`finalJunction` witnesses the closing relational pair without becoming an
occurrence of this history. They are brought together at the terminal boundary
by `FinalClosureInterpretation`, not by an identification in the types.

Every faithfully labelled positive continuation must then occupy the closing
place left available, and its occurrence there is unique. The circular regime
stipulates that this occupation must provide, at the terminal boundary, an
attempt to totalize the two poles of the initial difference. The obstruction
carried from the root rejects this contraction. The affirmative perimetral
turning is thereby located exactly: generation proceeds through an effectively
constituted continuation, while incorporating that continuation into the same
regime is impossible.

The resulting method compares architectures through what they constitute and
preserve. For each relation, it distinguishes its place in the constitution,
its possible realization as an occurrence, its preservation under transport,
and its actual use in proofs. It thus follows relations from their local
witnesses to the generated whole, and then from that whole to the place where
the status of its continuation changes.
