# Independent adversarial audit prompt: stagewise causal regime repair

Perform an independent, adversarial audit of the causal operational-regime
repair in `relational-perimeter`. Do not trust declaration names, comments,
documentation, the implementation plan, prior audit reports, or the summary in
this prompt. Reconstruct the scientific dependency chain from the Lean types,
definitions, proofs, executable reductions, and public API. The target must not
be weakened or replaced by a cardinality-only result.

## 1. Repository coordinates

- Repository: `https://github.com/JohnDoe-collab-stack/relational-perimeter.git`
- Branch: `codex/stagewise-causal-regime-repair`
- Exact target commit:
  `25a114d9643d936d97dceb9375f9864b7ab03a8d`
- Comparison base and expected merge-base:
  `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`
- Expected `origin/main` at audit start:
  `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`
- Public Lean root: `RelationalPerimeter.lean`
- Toolchain: the version pinned by `lean-toolchain`
- Temporary implementation plan:
  `CAUSAL_EXECUTED_REGIME_REPAIR_PLAN.md`
- Primary French conclusion:
  `docs/conclusion-largeur-exponentielle-conservation-identites.fr.md`
- Main public explanatory documents:
  - `docs/decomposition-operationnelle-endogene.fr.md`
  - `docs/endogenous-operational-decomposition.en.md`

Clone the repository yourself into a fresh directory. Fetch all remote refs.
Stop immediately and report the mismatch if the remote branch does not resolve
to the exact target commit, if `origin/main` does not resolve to the expected
base, or if the merge-base differs from the expected base. Check out the exact
target commit in detached-HEAD state for the audit.

Do not modify any production or documentation file in the audited checkout.
Run mutations only in disposable copies. Record SHA-256 hashes of every tracked
file before and after the audit and prove that the target checkout was not
changed.

## 2. Exact scientific target — no substitution permitted

Audit the following four claims as one connected result:

> **Dans ce cadre, la constitution relationnelle des dépendances est primitive.
> Le calcul produit lui-même, pendant son exécution et à partir de ce qu’il a
> déjà produit, sa décomposition opérationnelle et détermine ainsi quelles
> alternatives doivent continuer à être traitées comme des obligations
> indépendantes.**
>
> **Cette exécution ne produit pas d’explosion exponentielle de la largeur
> opérationnelle : bien que la lecture extensive de la frontière complète des
> profils constitués ait une largeur 2^n, le régime exécuté les regroupe en une
> seule obligation sans identifier les profils eux-mêmes.**
>
> **Dans la classe binaire formalisée, une largeur opérationnelle exponentielle
> apparaît si et seulement si le régime impose de conserver séparément toute la
> multiplicité lue sur cette frontière, c’est-à-dire si son application `carry`
> est injective.**
>
> **L’explosion exponentielle de la largeur opérationnelle est donc démontrée
> ici comme l’effet exact de cette exigence extensive de conservation
> indépendante, et non comme une conséquence nécessaire de la structure
> relationnelle du problème elle-même.**

The following do **not** count as establishing the target:

- proving only that a finite surjection has full width iff it is injective;
- defining a singleton obligation frontier independently of the executed
  reduction;
- reconstructing an operational decomposition only from a completed run when
  the local decision is not available from the current causal stage;
- defining `carry` as a constant and proving afterwards that it equals a value
  associated with a reduction;
- switching to a propositionally equivalent carrier;
- allowing a foreign relation to enter the authoritative public certificate;
- proving only a documentation statement, a theorem name, an `rfl` coincidence,
  or a regression test that restates the production theorem.

## 3. Framework stratification that must be preserved

Check that the implemented dependency order is literally:

```text
primitive relations and positive witnesses
  -> constituted role occurrences
  -> dependent relational role history
  -> constituted occurrence profiles
  -> complete source frontier
  -> computation and stagewise operational decisions
  -> obligation regime
  -> derived width readout
```

The source identities must remain exactly `RoleOccurrenceProfile roles`, with
`roleProfileFiniteCarrier roles` as their finite carrier. A program carrier,
`StructuralObligation`, a plain list, a transported equivalent carrier, or an
address space must not replace them in the main theorem or the public contrast.

Use the project’s vocabulary precisely:

- constitution belongs to the primitive relational layer;
- extensivity is the quantitative readout of an already derived complete
  frontier and neither creates nor individuates identities;
- an extensional view is a separate downstream projection and is not a synonym
  for the extensive readout;
- structural distinction of profiles is not operational independence;
- equality of obligations is not equality of source profiles;
- an honest generic conditional interface is allowed, but it must not be
  confused with the closed public instance that claims executed reconstruction.

Report any violation of this stratification as a material failure even if all
files compile.

## 4. Build, integrity, constructivity, and reachability

Run and report the exact exit status, job count, warnings, and relevant logs for:

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
lake update
```

If PowerShell is unavailable, say so explicitly; do not claim that command
passed. Verify that `lake update` leaves `lake-manifest.json` byte-identical.

Independently verify:

1. every tracked `.lean` production and test source is built;
2. every production module is reachable from `RelationalPerimeter`;
3. the stratification inventory covers every production module and has no
   orphan or unenforced entry;
4. every Lean file contains exactly one final axiom-audit block;
5. there is no `axiom`, `sorry`, `admit`, `noncomputable`, `Classical`,
   `propext`, `Quot.sound`, `native_decide`, `unsafe`, or hidden equivalent in
   handwritten source;
6. every handwritten declaration is axiom-free; distinguish compiler-generated
   declarations if Lean emits any;
7. the four foundational files are byte-identical to the comparison base:
   - `SegmentedResidualRole.lean`
   - `AbstractSegmentedTurning.lean`
   - `ExactTypeTransport.lean`
   - `StrongPerimetralTurning.lean`
8. no declaration present at the base or at the parent target
   `b65e8241eb23dad859bf552330ac8c4e11ca77a0` was silently deleted or weakened;
9. local Markdown links resolve and the edited SVG is valid and legible.

## 5. Stagewise causal production — former blocking defect 1

Audit, at minimum:

- `ExecutedStageDecomposition`;
- `executedStageDecomposition`;
- `StagewiseExecutedDecompositionHistory`;
- `buildStagewiseExecutedDecompositionHistory`;
- `StagewiseExecutedDecompositionHistory.roles`;
- `StagewiseExecutedDecompositionHistory.reduction`;
- the exactness theorems for the canonical roles and reduction;
- the corresponding fields of
  `ConstitutiveExtensiveSeparationCertificate`.

Determine whether the decomposition at one stage genuinely depends only on
that executed stage, with no future tail argument, and whether the dependent
tail starts at the exact state produced by the head stage. Distinguish this
formal prefix-local availability from an unverifiable wall-clock statement.

Construct a positive probe showing that a local decomposition can be built
from one stage before supplying any tail. Construct a two-tail or equivalent
probe showing that two histories sharing the same executed head cannot change
the head decomposition through their different suffixes.

Attempt the following adversarial mutations in disposable copies:

1. replace the stagewise decomposition in the final certificate by a
   post-hoc role-history reconstruction;
2. make the head reduction license depend on data from the future tail;
3. attach a tail whose source is not the state produced by the head;
4. delete the stagewise fields from the final certificate and adapt superficial
   tests if possible.

For each mutation, report whether it compiles, whether the full verification
suite passes, and—most importantly—whether the original public scientific
statement remains derivable. A failure caused only by deleting a referenced
name is not substantive evidence.

Answer explicitly:

> If two executions share exactly the same causal prefix through stage `k`, is
> the decomposition through `k` determined independently of either future
> suffix?

## 6. Constructive reduction-to-`carry` dependency — former defect 2

Audit, at minimum:

- `ExecutedRoleOccurrenceDecision`;
- `ExecutedRoleProfileReduction`;
- `normalizeExecutedRoleProfile`;
- `ExecutedCarryDerivation`;
- `reduceExecutedRoleProfile`;
- `carryByExecutedReduction`;
- `ExecutedRoleObligationRegime`;
- `ExecutedRoleObligationRegime.regime`;
- `ExecutedRoleObligationRegime.carryFromReduction`;
- `ExecutedRoleObligationRegime.carryDerivation`;
- the public carry theorem and regression checks.

Verify from the definitions—not merely from equations—that:

1. every source profile receives a computed, source-indexed reduction trace;
2. the transformed decision consumes the authoritative action, exact output,
   separate preservation map, non-identity, and occurrence distinction;
3. the retained decision cannot inhabit the transformed occurrence index;
4. `reduceExecutedRoleProfile` returns an obligation together with a derivation
   indexed by that exact obligation;
5. `ExecutedRoleObligationRegime` has no independently supplied `carry` field;
6. the regime’s `carry` is definitionally the first projection of the dependent
   reducer;
7. the package constructor is inaccessible outside its defining module;
8. width one is a downstream readout and not the premise that creates the
   reduction.

Attempt a substantive constant-`carry` ablation. Do not stop after changing one
line if a theorem name becomes unresolved: remove or adapt downstream cosmetic
references and determine whether the public certificate and its claimed
reduction-derived `carry` can still be reconstructed without the dependent
reducer. Also attempt to erase the reduction payload while preserving the
public result. If either succeeds, classify the causal claim as not established.

Compile the shipped expected-failure fixtures and independently reproduce their
intended failures. Confirm that each fails for the intended type error or
privacy boundary rather than for an unrelated import, syntax, or missing-name
error.

## 7. Authoritative relation provenance — former blocking defect 3

The generic `CausalConstitutiveStageExecution` interface may remain publicly
instantiable as an honest conditional interface. This is not by itself a
failure. The question is whether such a foreign value can enter the **closed
public scientific certificate**.

Audit the complete chain:

```text
executeConstitutiveResolution input
  -> publicInstrumentedExecutionRealization input
  -> exact public causal run
  -> canonical stagewise decomposition
  -> authoritative roles and compiled atoms
  -> stagewise reduction licenses
  -> dependent profile reduction
  -> executed obligation regime
  -> width readout and class-level iff
```

Verify that `ConstitutiveExtensiveSeparationCertificate` has a private
constructor and that its canonical builder fixes:

- the exact public instrumented realization;
- the canonical stagewise decomposition of that realization;
- the exact roles read from it;
- the executed regime built from that same stagewise decomposition.

Attempt to construct the final certificate with:

1. an externally supplied stage relation;
2. a different causal run;
3. a noncanonical stagewise decomposition;
4. an independently supplied regime or `carry`;
5. the generic post-hoc role builder substituted for the stagewise chain.

The authoritative public result must reject these substitutions. Report
separately whether generic conditional lemmas still accept generic values; do
not confuse that intended abstraction with the closed public instance.

## 8. Same carrier and exact exponential `iff`

Verify that both the identity regime and the executed regime have literally the
same source type:

```text
roleProfileFiniteCarrier certificate.roles
```

No equality cast, type equivalence, transport, or timeout-prone definitional
comparison may be hidden in the main contrast.

Audit both directions of the class theorem for every problem of every binary
family and every surjective `ObligationRegime`:

```text
regime.frontier.length = 2 ^ stageCount
  iff
Injective regime.carry
```

and its stronger formulation with distinct identities and separate addressing
factorized through the regime. Verify that:

- surjectivity is an explicit constitutive field of the regime;
- neither side of the `iff` is stored as a premise for the other;
- the binary relational class supplies the exact `2^n` source readout;
- the finite cardinal argument remains general and constructive;
- the public identity regime positively realizes the exponential side;
- the public executed regime has width one on the same source carrier;
- two source profiles are constructed as distinct while carrying to the same
  obligation;
- no source-profile equality is derived from obligation equality.

State the exact scope: this is an exact characterization of operational width
inside the formalized class of surjective obligation regimes, not a universal
time or memory lower bound and not a theorem about every possible adaptive
search tree.

## 9. Stratification and vocabulary audit

Trace every public object in the result to its layer. Produce a table with at
least these columns:

```text
declaration | constituted from | layer | consumed by | derived readout?
```

The table must include roles, occurrences, profiles, source frontier, program,
stagewise decomposition, reduction licenses, profile reductions, obligation
regime, extensive source readout, operational-width readout, and extensional
projection.

Verify that the documentation does not use “relational extensivity” as a
constitutive layer. In this project, extensivity is a derived quantitative
readout of a complete frontier. Verify separately that the extensional
state-and-quantity projection remains a downstream, information-forgetting
view. Report any sentence that reverses or merges those meanings.

## 10. Documentation truthfulness

Audit the exact French target paragraph, its English explanations, the README,
the implementation plan, and `docs/figures/relational-extensive-iff.svg` against
the code.

For every substantive clause, give:

```text
clause | VERIFIED / QUALIFIED / FALSE | exact declaration(s) | reason
```

In particular, determine whether “pendant son exécution” is justified by the
stage-local dependency structure. Do not interpret it as a wall-clock or
runtime-tracing theorem unless the code actually proves such a statement.

Check the SVG for valid XML, clipping, overlap, unreadable text, misleading
arrows, and incorrect layer names. Render it and include the rendering in the
evidence.

## 11. Regression and ablation standard

Do not count a mutation as rejected merely because it deletes a name used by a
test. For every critical ablation:

1. make the smallest coherent semantic mutation;
2. adapt superficial declaration names or restatement tests where necessary;
3. rerun the clean build and both verification gates;
4. add an independent counterprobe that imports only `RelationalPerimeter`
   whenever the public API should expose the property;
5. identify the first substantive type or theorem that becomes impossible;
6. report if the mutation survives.

At minimum, test:

- post-hoc rather than stagewise decomposition;
- future-tail-dependent head decision;
- unrelated tail state;
- constant `carry` independent of the reducer;
- erased dependent derivation;
- retained constructor used at the transformed occurrence;
- foreign relation injected into the final certificate;
- unrelated run or regime inserted into the final certificate;
- source carrier replaced by an equivalent but different carrier;
- source profiles identified after grouping;
- preservation proof removed from the transformed decision.

## 12. Required audit deliverables

Place all audit material under `audit/` in the audit project, not in the target
checkout:

1. `audit/STAGEWISE_CAUSAL_REGIME_AUDIT.md`
2. `audit/README.md`
3. `audit/reproduce.sh`
4. `audit/reproduce.ps1`
5. `audit/counterprobes/`
6. `audit/expected-failures/`
7. `audit/ablations/`
8. `audit/tools/`
9. `audit/evidence/`

Both reproduction scripts must:

- clone the repository into a fresh directory;
- verify the remote branch, target SHA, `origin/main`, and merge-base;
- record pre-audit hashes;
- run the complete clean build and verification sequence;
- compile every positive and expected-failure probe;
- run every recorded ablation and compare its actual result with the expected
  result;
- validate Markdown links and render the SVG;
- record post-audit hashes and prove the target checkout unchanged;
- stop on every unexpected outcome.

Run both scripts end to end. If an environment cannot run one of them, report
that limitation instead of claiming success.

All audit Lean probes must obey the repository’s constructive restrictions.
They must import the narrowest public surface possible, preferably only
`RelationalPerimeter`, redefine no production object as a substitute for the
audited one, and end with exactly one axiom-audit block.

## 13. Mandatory final questions

Answer every question with `YES`, `NO`, or `QUALIFIED`, followed by exact file,
declaration, probe, and evidence references.

1. Is the target commit exactly the remote branch head?
2. Is the expected base exactly `origin/main` and the merge-base?
3. Do all required clean builds and verification commands pass without Lean
   warnings?
4. Is the manifest unchanged by `lake update`?
5. Are all production modules reachable and stratification-enforced?
6. Are all handwritten declarations constructive and axiom-free?
7. Are the four foundational files unchanged from the base?
8. Were all tracked target files unchanged by the audit?
9. Are source identities constituted before every program, regime, and width
   readout?
10. Is extensivity only a derived readout of the complete constituted frontier?
11. Is the extensional projection kept distinct from that extensive readout?
12. Is one stage decomposition constructible from the current executed stage
    without any future tail?
13. Does the dependent tail begin at the exact state produced by the head?
14. Is the head decomposition invariant under different future suffixes sharing
    the same causal prefix?
15. Does every stage license use the relation reconstructed by that stage?
16. Does the transformed decision consume the action, exact output, preservation,
    non-identity, and occurrence distinction?
17. Does every source profile receive an executable dependent reduction trace?
18. Is each resulting obligation indexed by the derivation that produces it?
19. Does the executed package contain no independently supplied `carry` field?
20. Is the regime’s `carry` definitionally the first projection of the dependent
    reducer?
21. Does a coherent constant-`carry` ablation fail substantively?
22. Does erasing the dependent reducer destroy the claimed public causal chain?
23. Can a retained decision inhabit the transformed occurrence index?
24. Is the generic conditional interface clearly separated from the canonical
    public execution?
25. Is the final scientific certificate constructor private?
26. Is the final certificate fixed to the exact public realization?
27. Is its stagewise decomposition fixed to the canonical decomposition of that
    realization?
28. Is its executed regime built from that exact stagewise decomposition?
29. Can a foreign relation, unrelated run, arbitrary regime, or arbitrary
    `carry` enter the final public certificate?
30. Do the identity and executed regimes have literally the same source carrier?
31. Is the class-level exponential theorem a genuine two-way `iff`?
32. Is it quantified over every binary family problem and every surjective
    obligation regime in scope?
33. Is the conservation/addressing side independent of the width premise?
34. Does separate addressing factor through the regime itself?
35. Does the identity regime positively realize exact width `2^n`?
36. Does the executed regime positively realize exact width one?
37. Are two source profiles proved distinct while mapped to the same obligation?
38. Are those source profiles left un-identified after grouping?
39. Is the width-one result downstream of the executed reduction rather than a
    substitute for it?
40. Does the integrated public chain consume the authoritative relation before
    the width readout?
41. Does the main result avoid every carrier substitution or hidden transport?
42. Do the regression tests protect semantic dependencies rather than merely
    declaration names?
43. Do all shipped expected-failure fixtures fail for their intended reason?
44. Do the French and English documents state the same formal scope?
45. Is the edited SVG both visually correct and conceptually stratified?
46. Is any sentence stronger than the Lean result?
47. Does any critical ablation preserve the public causal conclusion?
48. Is the exact four-sentence scientific target established without
    substitution?

## 14. Verdict scale

Use exactly one final verdict:

- `TARGET ESTABLISHED — STAGEWISE CAUSAL REGIME DERIVATION VERIFIED`
- `TARGET ESTABLISHED WITH DOCUMENTATION CORRECTIONS`
- `REQUIRES CORRECTIONS`
- `TARGET NOT ESTABLISHED`
- `AUDIT BLOCKED`

`TARGET ESTABLISHED` is permitted only if the stagewise causal dependency, the
constructive reducer-to-`carry` dependency, the authoritative-relation closure,
the same-carrier contrast, and the bidirectional class theorem all survive the
adversarial probes and coherent ablations. Build success alone is insufficient.

End the report with:

1. the exact revisions audited;
2. the exact commands run;
3. a list of every mutation and its observed outcome;
4. every remaining qualification or limitation;
5. a direct answer as to whether the scientific target is established exactly,
   weakened, or not established;
6. confirmation that no target file was modified;
7. the names of all audit deliverables and successfully executed reproduction
   commands.
