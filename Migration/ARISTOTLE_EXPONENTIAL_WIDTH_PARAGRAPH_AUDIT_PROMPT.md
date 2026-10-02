# Independent audit prompt: endogenous decomposition and exponential operational width

Perform an independent, adversarial audit of one published French conclusion
against the Lean development that is claimed to establish it. Do not trust the
documentation, declaration names, comments, earlier audit reports, or this
prompt's interpretation of the code. Reconstruct the dependency chain from the
types, definitions, theorem statements, and proofs.

## Repository coordinates

- Repository: `https://github.com/JohnDoe-collab-stack/relational-perimeter.git`
- Branch: `codex/constitutive-succinctness-implementation`
- Exact target commit: `b65e8241eb23dad859bf552330ac8c4e11ca77a0`
- Comparison base and expected merge-base: `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`
- Document under audit:
  `docs/conclusion-largeur-exponentielle-conservation-identites.fr.md`
- Public Lean root: `RelationalPerimeter.lean`

Clone the repository yourself into a fresh directory. Fetch the remote refs and
stop immediately if the remote branch does not resolve to the exact target
commit above. Check out the target commit in detached-HEAD state. Confirm that
the comparison base is the merge-base with `origin/main`; report any divergence
instead of silently choosing another base.

## Exact paragraph to audit

> **Dans ce cadre, la constitution relationnelle des dépendances est primitive.
> Le calcul produit lui-même, pendant son exécution et à partir de ce qu’il a
> déjà produit, sa décomposition opérationnelle et détermine ainsi quelles
> alternatives doivent continuer à être traitées comme des obligations
> indépendantes.**
>
> **Cette exécution ne produit pas d’explosion exponentielle de la largeur
> opérationnelle : bien que le déploiement extensif des profils constitués ait
> une largeur 2ⁿ, le régime exécuté les regroupe en une seule obligation sans
> identifier les profils eux-mêmes.**
>
> **Dans la classe binaire formalisée, une largeur opérationnelle exponentielle
> apparaît si et seulement si le régime impose de conserver séparément toute la
> multiplicité extensive, c’est-à-dire si son application `carry` est
> injective.**
>
> **L’explosion exponentielle de la largeur opérationnelle est donc démontrée
> ici comme l’effet exact de cette exigence extensive de conservation
> indépendante, et non comme une conséquence nécessaire de la structure
> relationnelle du problème elle-même.**

The purpose of the audit is to determine whether every part of this paragraph
is supported exactly as written, without weakening it into a cardinality-only
statement and without strengthening it into an unproved universal complexity
claim.

## Mandatory integrity and build checks

Record the Lean version, Lake version, operating system, target SHA, base SHA,
merge-base, and SHA-256 hashes of every tracked file before doing any analysis.
Then run, from a clean checkout, at least:

```text
lake clean
lake build +RelationalPerimeter
lake build
pwsh -File scripts/verify.ps1
bash scripts/verify.sh
git diff --check
```

Also run `lake update` and verify that it leaves `lake-manifest.json` unchanged.
At the end, recompute all tracked-file hashes and prove that the target checkout
was not modified. Report job counts, warnings, failures, the number of Lean
files checked by each verifier, and whether both verifiers cover the same set.

Check independently that:

- every Lean file has exactly one final axiom-audit block;
- no production source contains `axiom`, `sorry`, `admit`, `noncomputable`,
  `Classical`, `propext`, `Quot.sound`, `native_decide`, `implemented_by`, or
  another escape from the repository's constructive discipline;
- no handwritten declaration used by the audited chain depends on an axiom;
- every production module relevant to the claim is reachable from the public
  root;
- the four foundational files remain unchanged relative to the base.

Do not modify any production or documentation file. Counter-probes and tools
must live only under your audit deliverable.

## Sentence-by-sentence mathematical audit

Give a separate `YES`, `NO`, or `QUALIFIED` verdict for every claim below. For
each answer, cite exact files, fully qualified declarations, and line numbers,
and distinguish what is present in a type from what is merely stated in a
comment.

### 1. Primitive relational constitution

Determine whether the formal dependency order genuinely begins with primitive
relational witnesses and uses them to constitute the role occurrences and the
dependent role history from which the profile carrier is derived.

Verify especially that:

- the profile identities are downstream of the relationally constituted role
  history;
- the extensive width is a readout of a complete duplicate-free profile
  frontier, not a constituent of the role history;
- the obligation regime is downstream of the already constituted source
  carrier;
- no hidden import reverses this dependency order.

Do not accept the first sentence merely because identifiers contain words such
as `Relational`, `Constitutive`, or `Role`.

### 2. Operational decomposition produced by execution

Reconstruct the complete causal chain behind the claim that the computation
produces its own operational decomposition from previously produced material.
At minimum, establish or refute all of the following:

1. structural opening exists without an operational transport field;
2. the relevant transport is returned by an executed search rather than stored
   in the opening or supplied as an external hypothesis;
3. unsuccessful candidates perform real executable work and fail before the
   successful relation is obtained;
4. the returned transformation acts on arbitrary continuations before an
   acceptance witness is inspected;
5. criterion preservation is a separate theorem and is actually consumed by
   the reduction;
6. the reduction changes which alternatives are retained as independent
   operational obligations;
7. the alternatives remain distinct and viable; neither equality nor
   impossibility is used to justify the reduction;
8. the executed output, seed, and provenance materially constrain the next
   discovery.

Test whether the claimed causal links are enforced by types and proofs or only
recorded as fields, definitional equalities, comments, or regression-test names.
Attempt targeted ablations in disposable copies. In particular, try to replace
the discovered transformation by preconstructed data, disconnect the next
state from the executed output, erase the preservation proof, and construct the
published executed regime without the authoritative reduction history. Record
the first meaningful failure for every rejected mutation. If a mutation
survives, classify the corresponding sentence as `NO` or `QUALIFIED`.

### 3. Same constituted profiles, non-exponential executed width

Verify on the public executed instance that:

- the profile frontier has exact width `2 ^ n` with the document's precise
  indexing convention;
- the executed obligation frontier has exact width one for the same source
  profile carrier;
- at least two source profiles are positively constructed and proved distinct;
- those distinct profiles are carried to the same executed obligation;
- no equality between the distinct source profiles is derived;
- the singleton obligation regime is tied to the executed reduction rather
  than being an unrelated singleton introduced only for the width comparison.

State explicitly whether “this execution does not produce exponential
operational width” is a theorem about all inputs in the public family or only a
finite evaluated sample.

### 4. The class-level binary `if and only if`

Check the exact quantifiers of the strongest public theorem. The required
statement is not merely an example and not merely one direction. It must range
over every `BinaryRelationalRoleExtensiveFamily`, every problem in the family,
and every relevant `ObligationRegime`, and prove:

```text
regime.frontier.length = 2 ^ family.stageCount problem
  ↔ Function.Injective regime.carry
```

Verify that:

- binary profile width is independently proved to be exactly the power of two;
- `ObligationRegime` requires `carry` to be surjective but does not store
  injectivity or full width;
- both directions of the equivalence are proved;
- the reverse direction is not circular and does not recover injectivity from
  an assumption definitionally equivalent to injectivity;
- separate addressing factors through the regime and is constructed from
  injectivity rather than assumed independently;
- “all alternatives” is justified by completeness and duplicate-freeness of
  the source frontier;
- a non-binary member exists so that the surrounding general class is not
  merely a renamed copy of the binary example.

Build independent public-root counter-probes for the theorem's exact type and
for both directions. Also show positively that the identity regime realizes
the exponential side and that the executed regime realizes the non-injective,
width-one side on the same constituted source carrier.

### 5. Meaning and scope of the conclusion

Determine whether the final sentence follows from the formal contrast on the
same constituted source carrier:

- one regime preserves all profile identities separately and has exponential
  operational width;
- the executed regime groups distinct profile identities and has width one;
- the relational constitution of the source profiles is unchanged between
  those two regime readings.

Decide whether this is sufficient to say, within the formalized binary class,
that exponential operational width is the exact effect of requiring separate
conservation rather than a necessary consequence of the relational problem
structure itself.

At the same time, check that the paragraph does **not** claim a universal lower
bound for all algorithms, all notions of time or memory complexity, all search
trees, or all mathematical formalisms. If any French wording exceeds the exact
Lean scope, provide the smallest exact French replacement.

## Required counter-probes

Create constructive Lean probes against the unmodified target. Prefer imports
of only `RelationalPerimeter`. Every probe file must end in one axiom-audit
block and must use none of the forbidden constructs listed above.

The probes must establish, or fail to establish with a recorded reason:

1. the exact class-level `iff` type;
2. exact source width `2 ^ stageCount`;
3. identity-regime exponential width;
4. executed-regime width one;
5. two distinct constituted profiles carried to the same executed obligation;
6. failure of injectivity for the executed `carry`;
7. separation of source-profile equality from equality of obligations;
8. the causal dependence of the executed obligation regime on the reduction
   history;
9. next-stage dependence on produced output, seed, and provenance;
10. impossibility of deriving exponential operational width from source
    multiplicity alone without separate preservation.

Do not count a probe as successful merely because it restates an existing
theorem. Where feasible, construct the witnesses and reductions independently
from the public interfaces.

## Required report structure

Produce `audit/EXPONENTIAL_WIDTH_PARAGRAPH_AUDIT.md` with these sections:

1. Verdict
2. Revisions and environment
3. Integrity and hashes
4. Clean builds and verification scripts
5. Constructivity and axiom sweep
6. Public dependency and import graph
7. Primitive relational constitution
8. Execution-produced operational decomposition
9. Exact source and executed widths
10. Distinct profiles grouped without identification
11. Class-level binary `iff`
12. Role of surjectivity and injectivity
13. Separate addressing through the regime
14. Same-carrier regime contrast
15. Adversarial ablations
16. Counter-probes
17. Sentence-by-sentence verdict on the French paragraph
18. Exact scope and prohibited extrapolations
19. Required corrections, if any
20. Final answers

The first line of the report must be exactly one of:

- `VERIFIED — THE PARAGRAPH IS FULLY SUPPORTED AS WRITTEN`
- `REQUIRES CORRECTIONS`

Do not use `VERIFIED` if any sentence depends only on a comment, a declaration
name, an unconsumed certificate field, a fixed fixture that makes the causal
claim vacuous, or an audit-only construction absent from the target.

## Final questions

Answer each with `YES`, `NO`, or `QUALIFIED`, followed by exact evidence.

1. Does the remote branch resolve to the required target commit?
2. Is the expected base the actual merge-base with `origin/main`?
3. Do both clean Lake builds succeed without warnings?
4. Do both verification scripts succeed and inspect the same Lean files?
5. Is the target checkout byte-identical before and after the audit?
6. Is the audited chain constructive and free of handwritten axioms?
7. Are all relevant production modules reachable from the public root?
8. Is relational constitution genuinely upstream of profile formation?
9. Is extensivity only a readout of the derived profile frontier?
10. Is the obligation regime downstream of the constituted source carrier?
11. Is the operational decomposition produced from executed discovery data?
12. Do failed candidates represent actual failed executable attempts?
13. Does the discovered transformation act on arbitrary continuations?
14. Is preservation separate from the transformation and consumed by the
    reduction?
15. Do the alternatives remain distinct and viable after the reduction?
16. Does produced material constrain the next discovery?
17. Does the public source profile frontier have exact power-of-two width for
    every input?
18. Does the executed regime have width one for every input?
19. Are distinct source profiles positively shown to share that one obligation?
20. Is their source identity preserved despite obligation grouping?
21. Is the executed singleton regime causally indexed by the actual reduction
    history in a way that cannot be erased without loss?
22. Is the class-level result a genuine `iff` quantified over every binary
    family, problem, and obligation regime?
23. Is `carry` surjective by regime definition but not injective by definition?
24. Is exponential width equivalent to injectivity of `carry`?
25. Is factorized separate addressing constructed rather than assumed?
26. Does the identity regime positively inhabit the exponential side?
27. Does the executed regime positively inhabit the non-exponential side on
    the same constituted source carrier?
28. Does the proof establish that source multiplicity alone is insufficient to
    force exponential operational width?
29. Is the paragraph careful to concern operational width rather than every
    possible notion of computational complexity?
30. Is every sentence of the French paragraph exactly supported as written?

Conclude with a compact table mapping every clause of the French paragraph to
the precise declarations and counter-probes that support or refute it. If the
verdict is `REQUIRES CORRECTIONS`, provide exact minimal French replacements
and distinguish formal defects from editorial imprecision.
