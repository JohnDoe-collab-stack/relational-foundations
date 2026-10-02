# Audit only the exact target

Audit only whether the Lean code at the revision below proves the exact target
quoted here. Do not audit another objective. Do not reformulate, weaken,
strengthen, reinterpret, or replace the target.

## Repository

- Repository: `https://github.com/JohnDoe-collab-stack/relational-perimeter.git`
- Branch: `codex/causal-normalization-integration`
- Exact commit: `7e857a28989995edc71f781c19ca9e6a0f59ca60`
- Public root: `RelationalPerimeter.lean`

Clone the repository yourself, verify that the branch resolves to this exact
commit, and inspect the Lean code at that revision.

## Exact and immutable target

> **Dans ce cadre, la constitution relationnelle des dépendances est primitive.
> Le calcul produit lui-même, pendant son exécution et à partir de ce qu’il a
> déjà produit, sa décomposition opérationnelle et détermine ainsi quelles
> alternatives doivent continuer à être traitées comme des obligations
> indépendantes.**
>
> **Cette exécution ne produit pas d’explosion exponentielle de la largeur
> opérationnelle : bien que la lecture extensive de la frontière complète des
> profils constitués ait une largeur 2ⁿ, le régime exécuté les regroupe en une
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

Do not replace “régime exécuté” with another expression. If the code uses an
internal structure called a causally admitted regime, determine only whether it
is genuinely the regime produced by the execution and therefore proves the
exact words “le régime exécuté”.

## Verification required

For each sentence and each substantive clause, answer `VERIFIED`, `QUALIFIED`,
or `FALSE`, with the exact Lean declarations and proof dependencies.

Verify only these points, because they are the content of the target:

1. Relational constitution is upstream and primitive in the framework.
2. The computation produces its operational decomposition during execution and
   from material already produced by that execution.

   For the words “pendant son exécution et à partir de ce qu’il a déjà produit”,
   test prefix locality explicitly. The decomposition and decision of a stage
   must be constructible from that stage and its already-produced prefix,
   without reading any future tail. Build a probe with two execution histories
   sharing the same head but different valid tails; the head decomposition and
   head operational decision must be identical. Also test a coherent mutation
   that reconstructs the head decomposition from the completed history after
   the fact. If the public causal conclusion survives such a post-hoc
   reconstruction unchanged, mark clause 2 `FALSE`.

3. This produced decomposition determines which alternatives continue as
   independent obligations.
4. The executed regime is produced from this chain, not independently supplied
   afterwards.

   Verify exactness of the produced operational decomposition: for source
   profiles `p` and `q`, equality of their executed obligations must hold if and
   only if the normalization produced the same operational target for `p` and
   `q`. The downstream realization must neither merge distinct produced targets
   nor split equal produced targets.

5. The extensive reading of the complete constituted-profile frontier has width
   `2^n` in the formalized binary class.
6. The executed regime groups those same profiles into one obligation.
7. The grouping does not identify the source profiles.
8. Exponential operational width holds if and only if `carry` is injective in
   the stated binary class.
9. The width-one result is genuinely derived from executed production. It must
   not follow merely from an independently stipulated singleton type, singleton
   frontier, or constant `carry`.
10. The final sentence follows exactly from these formal results within the
    stated class.

Test the decisive causal point adversarially: in a disposable copy, erase or
neutralize the executed decisions, their source-indexed traces, and the exact
image of produced targets while preserving public statements as far as
possible. If the same executed-regime width-one conclusion can still be proved
from an independent singleton or constant `carry`, the target is not
established. A failure caused only by deleting a referenced name does not count.

Also verify that two distinct constituted profiles are carried to the same
executed obligation without being proved equal, and that the exponential regime
and executed regime use literally the same source carrier.

Run the repository build and any Lean probes necessary to decide this target.
Do not expand the audit into unrelated repository questions.

## Deliverable

Write `audit/EXACT_TARGET_AUDIT.md` containing:

- one clause-by-clause table;
- the exact Lean dependency chain supporting or refuting each clause;
- the causal ablation result;
- one final verdict.

Use exactly one verdict:

- `EXACT TARGET ESTABLISHED`
- `EXACT TARGET REQUIRES CORRECTIONS`
- `EXACT TARGET NOT ESTABLISHED`

`EXACT TARGET ESTABLISHED` is permitted only if all ten target clauses are
`VERIFIED` and the causal ablation succeeds for substantive reasons. Any
`FALSE` target clause entails `EXACT TARGET NOT ESTABLISHED`. A `QUALIFIED`
clause may at most yield `EXACT TARGET REQUIRES CORRECTIONS`; it cannot support
`EXACT TARGET ESTABLISHED`.

A nearby theorem, a cardinality-only theorem, or a differently formulated
target does not count as validation.
