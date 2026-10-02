# Independent audit of the exact causal and exponential-width target

## Repository and immutable revisions

Fetch the project yourself from GitHub. Do not use a repository supplied by the
author and do not trust any local build cache.

- Repository: `https://github.com/JohnDoe-collab-stack/relational-perimeter.git`
- Target branch: `codex/causal-normalization-integration`
- Expected target commit: `0a65c21edecef03709081c24a8d224dae1537378`
- Expected base commit: `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`

Stop immediately if the remote branch does not resolve to the expected target
commit, if the merge-base with `origin/main` is not the expected base commit, or
if the checkout is not clean before the audit.

Do not modify any production file. Any probe, mutation, report, script or log
created for the audit must live under `audit/`. Run mutations only in disposable
copies. Record hashes before and after the audit and prove that the audited tree
was not changed.

## Immutable target

The target below is the only scientific target of this audit. Do not replace it
with a weaker cardinality statement, a compression result, an independently
postulated singleton regime, an existence theorem for some unrelated regime, or
an interpretation based only on documentation.

> Dans ce cadre, la constitution relationnelle des dépendances est primitive.
> Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a
> déjà produit, sa décomposition opérationnelle et détermine ainsi quelles
> alternatives doivent continuer à être traitées comme des obligations
> indépendantes.
>
> Cette exécution ne produit pas d'explosion exponentielle de la largeur
> opérationnelle : bien que le readout extensif des profils constitués ait une
> largeur `2^n`, le régime exécuté les regroupe en une seule obligation sans
> identifier les profils eux-mêmes.
>
> Dans la classe binaire formalisée, une largeur opérationnelle exponentielle
> apparaît si et seulement si le régime impose de conserver séparément toute la
> multiplicité extensive, c'est-à-dire si son application `carry` est injective.
>
> L'explosion exponentielle de la largeur opérationnelle est donc démontrée ici
> comme l'effet exact de cette exigence extensive de conservation indépendante,
> et non comme une conséquence nécessaire de la structure relationnelle du
> problème elle-même.

The intended formal equivalence is:

```text
regime.frontier.length = 2 ^ stageCount
  iff
Function.Injective regime.carry
```

where the source profiles have already been constituted from the dependent
history of relational constitutive roles, and where separate addressing must
factor through the obligations carried by the regime.

## Required interpretation of the stratification

Audit the following order exactly. A downstream layer must not replace or
retroactively constitute an upstream one.

```text
primitive typed relations and witnesses
  -> executed stages
  -> relational constitutive roles
  -> constituted occurrence profiles
  -> stagewise executed reduction
  -> targets produced by that reduction
  -> operational obligations computed as the exact image of those targets
  -> finite width readout
```

Extensivity is only a downstream readout of already constituted profiles. It
must not be credited with constituting, individuating or identifying them.

## Questions that must be decided

For every item, answer `VERIFIED`, `FALSE` or `QUALIFIED`, cite the exact Lean
declarations and lines, and provide a compiling probe or a reproducible failing
probe whenever the answer is not immediate from the declaration.

1. Are the source profiles produced from the dependent history of relational
   constitutive roles, rather than from a free-standing `Fin`, Boolean cube or
   independently chosen extensive carrier?
2. Is the public stage decomposition prefix-local? In particular, can the head
   decomposition and head decision be constructed from the head stage and the
   already-produced prefix without reading a future tail?
3. Does each per-stage reduction consume the executed role's discovered action,
   the separate preservation proof for arbitrary continuations, and the
   distinction between the two occurrences?
4. Does the public normalization return, for every source profile, both a
   produced target and an occurrence-indexed reduction trace from that exact
   source profile to that exact target?
5. Is the public operational regime computed directly as the finite image of
   the produced target function on the same constituted source carrier?
6. Is obligation equality exact, in both directions?

   ```text
   carry p = carry q  iff  producedTarget p = producedTarget q
   ```

   The downstream regime must neither merge distinct produced targets nor split
   equal produced targets.
7. Is regime width proved equal to the cardinality of the computed target image,
   before the width-one conclusion is derived?
8. Is the singleton target image proved from the executed reduction traces,
   rather than prescribed by choosing `Unit`, a literal singleton obligation
   type, a constant `carry`, or a one-element frontier independently of the
   computation?
9. Does the public executed regime have width one on exactly the same source
   profile carrier whose extensive readout has width `2^n`?
10. Are at least two source profiles proved distinct while being carried to the
    same produced operational obligation, without any equality or quotient of
    the source profiles?
11. For every binary relational-role extensive family, every problem and every
    surjective obligation regime on its constituted profile carrier, is the
    following genuine two-way theorem proved?

    ```text
    width = 2 ^ stageCount  iff  carry is injective
    ```
12. Is separately factorized addressing constructed from injectivity through
    the regime itself, rather than added as an independent assumption or applied
    directly to the source carrier?
13. Does the identity/separate regime positively inhabit the exponential side,
    while the computed executed regime positively inhabits the width-one,
    non-injective side on the same carrier?
14. Does any public conclusion silently rely on `Classical`, `propext`,
    `Quot.sound`, `noncomputable`, `axiom`, `sorry`, `admit`, `native_decide`,
    `implemented_by` or an open external hypothesis that should have been closed
    by a repository construction?
15. Do the French and English documentation state exactly the proved scope,
    without presenting extensivity as a constitutive layer and without replacing
    the computed target-image regime with an independently postulated singleton?

## Mandatory causal checks

These checks must preserve the public target statements and types. A mutation
that merely deletes or renames the theorem being checked is not evidence.

### A. Independent singleton substitution

Attempt to replace the public computed-image regime with a `Unit` obligation,
a literal one-element frontier or a constant `carry` independent of the
normalization target. The exact-regime theorem and the fibre equivalence must
reject this substitution. If all public target conclusions survive unchanged,
mark the target `FALSE`.

### B. Trace erasure

Attempt to erase the source-indexed reduction trace or to construct the public
normalization target without the executed reduction. The canonical
normalization, target exactness and certificate chain must cease to be
inhabitable. A width-one theorem that survives solely because a singleton was
prescribed does not establish the target.

### C. Post-hoc reconstruction

Construct two valid completed histories sharing the same head but having
different tails. Verify that their head decomposition and head operational
decision are identical for structural reasons. Then attempt a coherent mutation
that reconstructs the head decomposition from the completed future history. If
the same canonical public certificate can still be inhabited, mark the phrase
"pendant son exécution et à partir de ce qu'il a déjà produit" `FALSE`.

### D. Inexact downstream grouping

Attempt both of the following while preserving all public target statements:

- merge two source profiles whose produced targets are distinct;
- split two source profiles whose produced targets are equal.

Both must be rejected by the two directions of the public fibre equivalence.

### E. Loss of material execution

Attempt to replace the discovered per-stage action, remove arbitrary-
continuation preservation, or identify the sibling occurrences while preserving
the canonical normalization and certificate. The relevant construction must
fail for substantive type/proof reasons.

## Build, integrity and constructivity checks

From a fresh clone at the exact target commit, run at least:

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
lake update
```

Confirm that `lake update` leaves `lake-manifest.json` byte-identical. Confirm
that both verification scripts inspect the same set of Lean files. Check that
every production module is reachable from `RelationalPerimeter`, that every Lean
file contains exactly one final axiom-audit block, and that no hand-written
declaration depends on an axiom.

## Required deliverables

Place all audit material under `audit/`:

- `audit/EXACT_CAUSAL_EXPONENTIAL_TARGET_AUDIT.md`;
- `audit/README.md`;
- fresh-clone reproduction scripts for Bash and PowerShell;
- positive probes and expected-failure probes;
- exact mutation patches and logs for checks A-E;
- build, verification, hash, reachability and axiom-scan evidence.

The report must contain:

1. the exact revisions and integrity results;
2. the complete build and constructivity results;
3. a clause-by-clause table for the immutable target;
4. a declaration-level reconstruction of the stratification;
5. the results of causal checks A-E;
6. an explicit statement of anything proved only by a probe rather than by a
   production declaration;
7. a list of any documentation sentence stronger than the Lean result;
8. answers to all fifteen questions above;
9. one strict final verdict.

## Strict verdict rule

Use exactly one of these verdicts:

- `EXACT TARGET ESTABLISHED`
- `EXACT TARGET REQUIRES CORRECTIONS`
- `EXACT TARGET NOT ESTABLISHED`

`EXACT TARGET ESTABLISHED` is permitted only if every target clause is
`VERIFIED`, the same-carrier and exact-image conditions hold, and all mandatory
causal checks reject the illicit substitutions for substantive reasons. Any
`FALSE` target clause entails `EXACT TARGET NOT ESTABLISHED`. Any `QUALIFIED`
target clause entails at most `EXACT TARGET REQUIRES CORRECTIONS`.

Do not assess novelty, philosophical importance or publication value. Decide
only whether the exact immutable target is established by the Lean code at the
specified commit.
