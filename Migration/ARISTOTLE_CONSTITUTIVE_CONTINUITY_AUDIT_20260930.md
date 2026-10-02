# Independent scientific audit of the immutable causal exponential-width target

Audit the exact target below against the published Lean implementation. Be
independent and adversarial. Report failures plainly. Do not repair production
code, change the target, or certify a nearby statement instead.

## 1. Retrieve the repository yourself and pin the revisions

- Repository: `https://github.com/JohnDoe-collab-stack/relational-perimeter.git`
- Published target branch: `codex/constitutive-continuity-audit-20260930`
- Exact target commit: `4e0febf032821882069e7cfefd7e631fc8461d95`
- Exact immediate parent: `dd226b05056cd1f944df3368c7d3233a49d97bd4`
- Expected `origin/main` and merge-base: `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`
- Toolchain: use the target repository's `lean-toolchain`, without changing it.

Start from a fresh clone, not a repository reconstructed from attachments:

```bash
git clone --no-checkout https://github.com/JohnDoe-collab-stack/relational-perimeter.git relational-perimeter-target
cd relational-perimeter-target
git fetch origin main codex/constitutive-continuity-audit-20260930
git rev-parse origin/codex/constitutive-continuity-audit-20260930
git rev-parse origin/main
git checkout --detach 4e0febf032821882069e7cfefd7e631fc8461d95
git rev-parse HEAD
git rev-parse HEAD^
git merge-base HEAD origin/main
git status --porcelain
```

Compare every result with the exact values above. Stop and report a revision
mismatch if any differs. Record SHA-256 hashes of every tracked file before
and after the audit. Keep this checkout unchanged. Place reports and probes
outside it; run source mutations only in separate disposable copies.

## 2. Immutable scientific target

The following four paragraphs are the exact target. Quote them unchanged in
the report. Do not replace them with a finite cardinality lemma, a statement
about compression, a weaker causal claim, or an assessment of alignment.

> **Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes.**
>
> **Cette exécution ne produit pas d'explosion exponentielle de la largeur opérationnelle : bien que le déploiement extensif des profils constitués ait une largeur 2^n, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes.**
>
> **Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c'est-à-dire si son application `carry` est injective.**
>
> **L'explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l'effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même.**

The already-declared mathematical scope is exact full finite width
`2^stageCount` for surjective obligation regimes over binary role histories.
For the public executed instance, `stageCount = input + 1`. The general class
and the particular executed instance have distinct quantifications: inspect
both. The target does not assert a universal time or memory lower bound, a
polynomial SAT algorithm, or a result about every adaptive search tree.

Extensivity is a quantitative readout of prior constitution, not an additional
constitutive layer. Interpret the target's wording according to that explicit
stratification; flag any code or documentation that contradicts it.

## 3. Constitutive method and mandatory scientific checks

Read the four foundational files and the relevant production closure, not just
the final theorem or the regression tests:

```text
SegmentedResidualRole.lean
AbstractSegmentedTurning.lean
ExactTypeTransport.lean
StrongPerimetralTurning.lean
```

Follow the actual typed dependency order:

```text
primitive relations and positive formation witnesses
-> dependent role history and constituted occurrences
-> source profiles and their derived finite carrier
-> executed action and prefix-local operational production
-> produced outputs, dependent traces and proved convergence
-> exact realization and separate semantic admission
-> operational obligation regime
-> width readouts and the class-level iff
```

Check all of the following, citing production declarations and compiling
client probes importing only `RelationalPerimeter` wherever possible.

### A. Constitution, source identity, and scope of the class

Verify that public source profiles are derived from the authoritative dependent
role history, with positive formation, source, target and provenance material.
Distinguish formation from the equality used to realize its fibre. Trace the
material actually consumed by the interpreter, the normalization and admission.

At class level, inspect the definitions and quantifiers rather than treating
the word "relational" as evidence. Test generic families with trivial relation
families separately from trivializing relations in the actual public execution.
State exactly what each probe demonstrates. Acceptance of a different abstract
family does not by itself show that the public executed determination has been
erased; conversely, a label or an unused witness must not be accepted as a
constitutive dependency merely because the public example is rich.

Separate constitutive participation from minimal proof-theoretic consumption.
If a claimed dependency is missing, mark it plainly, even when the final width
is mathematically correct.

### B. One source carrier, including the general theorem's application

Verify by `rfl` the equality of the complete finite-carrier objects, not only
their widths or isomorphic identity types:

```text
publicBinaryRelationalRoleExtensiveFamily.sourceCarrier (index := input) ()
= publicRoleProfileFiniteCarrier input
```

Apply the general binary-family theorem directly to
`publicCertificateExecutedRegime input`, with explicit `index := input` if
needed for inference. No cast, adapter, heterogeneous equality or alternative
carrier may be used to close this probe.

### C. Prefix-local production during the execution

Inspect `OperationalProductionProgram.evaluate`, the head producer, the fused
recursive executor and its exact interpreter equation. Check that each head is
formed from its stage and constituted past, before its dependent continuation,
and that the next state consumes actual output, seed and provenance.

Test two valid histories with the same head and different tails, and two
different remaining horizons. The head production and decision must coincide.
Check that the closed scientific certificate includes the exact interpreter
equation, primitive order and origin of the stored output images.

Attempt a coherent mutation that adds a future-data field to the head production
and fills it from the completed tail, explicitly opening the private constructor
in the disposable copy so privacy cannot be the only reason for rejection.
Check the production-level interpreter equality and head exactness, not merely
a test referring to a declaration name. Also test executing a subsequent stage
before the first decomposition while retaining the same terminal value.

These are properties at the declared primitive-operation boundaries. Do not
mistake them for wall-clock timing, or claim that pure Lean terms prohibit every
observationally irrelevant evaluation of an unused argument.

### D. Executed action, preservation, viability and persistent distinctions

Verify that transformed outputs are computed by the relation returned by the
actual discovery, rather than a prescribed retained value. The action must be
defined on arbitrary continuation payloads. Preservation must be proved
separately and consumed by the generic semantic consumer and the admitted
obligations. Inspect the concrete consumer, not just stored certificate fields.

Verify positive viability and distinction of both siblings, non-identity of the
action, and the feedback into the next discovery. A dispensable sibling must
not be classified as equal to the retained sibling or impossible.

### E. Full produced image before convergence and exact width-one condition

Inspect `ProducedOutputImage.Value`, `imageRegime`, `targetEquality`, `regime`
and `image_width_one_iff_converges`.

The image carrier must contain actual produced values with membership evidence,
without an anchor-equality or convergence clause in its definition.
`imageRegime` must be constructible with explicit decidable equality of image
values before any convergence premise is supplied.

For a nonempty source, verify both directions of the general theorem:

```text
imageRegime.frontier.length = 1
  iff all produced source outputs are equal
```

Verify that the executed width proof uses this result and that the instance
constructively supplies image equality from its executed convergence when the
full continuation codomain does not have decidable equality.

On the same two constituted role occurrences, inspect the shipped separating
Boolean readout. Its actual image regime must have width two, not merely two
unequal terms of an unused subtype. This is a comparative readout, not another
SAT execution or a replacement for the public instance.

### F. Normalization and exact realization across layers

Verify that `ExecutedCausalNormalization.result` is derived by eliminating its
exact constitutive chain at the supplied source, not a freely installed result
field. Each result must yield its actual target and its source/target-indexed
trace. Convergence must follow from executed decisions and action agreements,
not the ambient target carrier's shape.

Inspect the output images stored at heads, their dependent composition,
`ExecutedOutput.value`, `reify` and both return laws. The inverse must copy
actual target components, not choose a fixed source from a propositional
existence or use singleton width to manufacture an inverse.

Check `policyObligationTransport`, both return laws, the source-wise `carry`
agreement, target agreement and arbitrary-payload action agreement. An exact
carrier equivalence alone is not enough. This transport relates two realizations
of produced obligations, not source profiles bijectively to their grouped image.

### G. Admission and the regime actually produced

Keep image membership, exact realization, admission and criterion satisfaction
separate. Verify that semantic admission is closed from the same executed chain
and that a carried obligation exposes and consumes its guarantees.

Prove both directions of:

```text
carry p = carry q iff producedTarget p = producedTarget q
carry p = carry q iff the executed traces positively codetermine p and q
```

The image realization must neither merge genuinely different produced targets
nor split equal produced targets. Width one must be a downstream readout of
the recorded output images, their convergence and exact realization, not a
presence-only status marker or an independent `Unit` regime.

### H. Binary iff and the actual non-exponential witness

Verify the genuine two-direction theorem for every binary family, every problem
and every surjective regime in the class:

```text
regime.frontier.length = 2 ^ stageCount
  iff Function.Injective regime.carry
```

Identify where surjectivity is required. Separate the general finite-surjection
fact from the prior constitution and binary readout that supply its meaning
here. Neither direction may be assumed in a certificate field without a proof.

Verify that separate addressing is constructed through the regime from
injectivity. Locate the identity regime of full width and the actual semantically
admitted executed regime of width one on the same source carrier. Locate the
two explicit distinct profiles, their executed traces and their common carried
obligation, without source-identity collapse.

Judge paragraph 4 within this exact class and notion of width. Do not certify it
merely because any finite carrier admits an arbitrary constant map; inspect
the actual executed, semantically admitted witness and its causal chain.

## 4. Required causal substitutions in disposable copies

Freeze each patch before its run. Record patch hash, full command, exit code,
first substantive diagnostic and any immediate coherent adaptations. Do not
count missing imports, syntax errors, unused-variable warnings, missing names,
timeouts or privacy alone as semantic rejection.

At minimum attempt:

1. An independent `Unit` public regime retaining width one.
2. A genuinely independent prescribed target with a recovered trace.
3. Future-derived head production, including the opened-constructor variant.
4. A reordering that delays decomposition until after a subsequent stage.
5. A source-ignoring replacement of the canonical normalization result.
6. Removal of action-output exactness while retaining the closed target.
7. Removal of universal preservation from the semantic consumer/admission.
8. Removal of source distinction or identification of sibling occurrences.
9. A downstream merger of different produced values or split of equal values.
10. A source-carrier adapter in the direct class-to-public-regime application.
11. Replacement of recorded output images by a fixed singleton/status marker.

Evaluate the complete target, not only whether an isolated numeric equality
survives. Rebuilding a guarantee from the same executed relation and witnesses
does not erase that guarantee. Similarly, transporting an actual executed trace
along an equality proved from that same chain is not an independently prescribed
target. If a mutation survives, show which dependencies it genuinely removed
and which it still reconstructs; do not assume either failure or success.

Opening a constructor should expose an attempted forgery for substantive checking;
it is not itself a false target clause. Conversely, private names alone are not
evidence that the scientific dependency is enforced.

## 5. Repository integrity, constructivity and reproducibility

Run from the pinned fresh checkout:

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
lake update
```

Report commands, exit codes, warnings, job/file counts and tool versions. If a
tool is unavailable, report that limitation; do not claim its check passed.
Verify matching Lean-file selection, production reachability and enforcement
of every stratification row. Check unchanged manifest, four foundational files
and existing diagrams; compare with the base and immediate parent as appropriate.
Inspect the diff for removed or weakened scientific results, distinguishing
declarations moved to a lower layer from declarations lost.

Every Lean source must have exactly one final axiom-audit block. Scan for
`axiom`, `sorry`, `admit`, `noncomputable`, `Classical`, `propext`, `Quot.sound`,
`unsafe`, `native_decide` and `implemented_by`, including prefixed declarations.
Sweep all production constants for axioms, distinguishing handwritten from
compiler/deriving-generated declarations. Check executable `Type` data and
positive construction of concrete witnesses. Honest abstract conditional
interfaces are not closed concrete realizations.

Compare the French, English and README claims to production code. Verify local
links. Do not spend the audit on unrelated philosophical novelty claims, a new
alignment theory, or redesigning unchanged figures.

## 6. Deliverables and decision

Provide, outside the unchanged target checkout:

- `audit/CONSTITUTIVE_CONTINUITY_EXACT_TARGET_AUDIT.md`;
- a clause table for all four unchanged target paragraphs and every mandatory
  dependency above, with `VERIFIED`, `QUALIFIED` or `FALSE` and exact evidence;
- a typed dependency table from primitive constitution to regime width;
- constructive positive client probes, with final axiom-audit blocks;
- expected-failure probes with their intended diagnostics;
- frozen mutation patches, hashes, outcomes and logs;
- a reproducible script and README documenting commands actually run;
- final tracked-file hashes and final clean-checkout status.

Answer explicitly:

1. Does the actual public construction follow the constitutive method end to end?
2. Is production prefix-local inside the executed primitive program, rather than
   only a compatible reconstruction from a completed history?
3. Are actual outputs and their traces the origin of grouping and admission?
4. Is width one derived from proved output convergence, with a genuine width-two
   separating image on the same constituted local sources?
5. Are realization, admission and semantic preservation demonstrably separate?
6. Do the exact transports preserve the same produced values and action, with
   both return laws and no constant inverse?
7. Does the class iff apply directly to the public executed regime on literally
   the same carrier, and keep its announced quantifiers?
8. Are distinct profiles carried together without equating their source identities?
9. Do surviving substitutions expose a genuine target dependency failure or
   merely reconstruct the same executed determination?
10. Are all four target paragraphs established together, with no indispensable
    link existing only in prose or in audit-only probes?

Use exactly one final verdict:

```text
EXACT TARGET ESTABLISHED
EXACT TARGET REQUIRES CORRECTIONS
EXACT TARGET NOT ESTABLISHED
```

`EXACT TARGET ESTABLISHED` requires every target clause and indispensable typed
dependency to be `VERIFIED`. A false target clause entails
`EXACT TARGET NOT ESTABLISHED`; a qualified target clause permits at most
`EXACT TARGET REQUIRES CORRECTIONS`. Do not turn an observed failure into an
editorial success, nor turn an observationally equivalent reconstruction from
the same determination into an independent forgery.

Report exactly what is proved, what is not, and what would need correction.
Do not modify the audited production repository.
