# Independent scientific audit — exact relational and causal completion

Audit the target repository independently and adversarially. Report every
failure plainly. Do not repair the target repository during the audit. Run
mutations and probes only in disposable copies.

## Revisions to audit

- Repository: `https://github.com/JohnDoe-collab-stack/relational-perimeter.git`
- Branch containing the target: `codex/exact-relational-causal-completion`
- Exact scientific target commit: `2c31d97616d631c1641ab6ee89e1173db3ee44f4`
- Immediate parent: `4a21728b81d3e8eb5fdeb085dd7fc25e60df1229`
- Public `main` reference: `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`
- Required toolchain: the repository's own `lean-toolchain`

Clone the repository yourself, fetch the branch, and check out the exact target
commit. Stop and report a revision mismatch if any expected revision is absent
or resolves differently. Record hashes before and after the audit and leave the
target checkout unchanged.

## Immutable scientific target

The following French statement is the target. Do not weaken it, replace it by a
cardinality lemma, or validate a nearby statement.

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

Judge every sentence and every causal dependency separately. The only positive
verdict allowed is `EXACT TARGET ESTABLISHED`, and it is allowed only if every
clause and every mandatory dependency below is verified by the Lean code for
substantive type-theoretic reasons.

## Central method to verify

The project method is constitutive and relational. The audit must check that the
implementation follows this order end to end:

1. primitive typed formation, provenance, source, and target relations;
2. positive witnesses of those relations;
3. constituted role occurrences carrying those witnesses;
4. dependent histories of those constituted occurrences;
5. extensive profiles as a readout of that prior constitution;
6. an executed stagewise transformation acting on those profiles;
7. operational codetermination produced by elimination of the executed chain;
8. an obligation regime that is the exact image of that codetermination;
9. the width result and the exponential `iff` only after those dependencies.

Merely storing a witness beside relation-free data is not enough. A required
witness must be consumed by the next constitutive eliminator, and removing or
trivializing it must break the relevant downstream construction or theorem.

## Mandatory checks

### A. Relational constitution is genuinely primitive

Verify that the scientific carrier is made of constituted occurrences, not raw
occurrences accompanied by unused evidence. Check that the interpreter consumes
formation, provenance, source, and target witnesses in their constitutive order.

Attempt coherent mutations that:

- replace all four primitive relation families by `Unit`;
- erase one relation witness at a time;
- keep the witness as an unused stored field;
- replace constituted occurrences by the former raw occurrence carrier.

The target fails if the same public scientific conclusions survive such a
mutation without an explicit, honestly weaker theorem and scope.

### B. One authoritative carrier, without an adapter

Verify definitionally, not merely propositionally or heterogeneously, that:

- the carrier produced from the public executed role history;
- the carrier used by the executed regime; and
- the carrier to which the public binary-class `iff` is applied

are the same carrier. A transport equality, cast, adapter carrier, or separately
reconstructed copy is a failure of this requirement.

### C. Production is prefix-local and occurs during execution

Verify that the head operational production has no completed future tail in its
type or inputs. The tail must be indexed by the state and constituted context
produced by the head. Two valid histories sharing the same head but having
different tails must receive the same head production and decision for
substantive dependency reasons.

Attempt a coherent mutation that computes or stores the head production from
the completed future tail. It must be rejected by the production types, not
merely forced equal afterward because the result type happens to be a singleton.

### D. The normalized target is produced, not prescribed

Verify that local normalization eliminates the executed decision constructors
and computes the target from the executed action or retained occurrence. There
must be no independently supplied target plus equality proof, and no prescribed
target whose trace is recovered afterward by a cast.

Attempt both mutations. They must fail for substantive typing reasons while the
canonical construction still compiles.

### E. Preservation and occurrence separation are constitutively consumed

Verify that arbitrary-continuation preservation and the distinctness of the two
constituted occurrences are both required by the chain that authorizes grouping
and by the exact operational regime. Delete each witness independently. The
public certificate, grouping authorization, exact regime, and target conclusion
must no longer be constructible; deleting a regression test that merely names a
witness must not make the mutation pass.

Also verify that no proof identifies the two alternatives or proves the removed
alternative impossible.

### F. Grouping authorization is indispensable

Verify that the one-obligation regime cannot be constructed merely because all
targets inhabit a singleton-like type. Its obligation must be indexed by the
executed target together with the exact relational constitution, preservation,
and separation evidence authorizing that grouping.

Attempt to remove the grouping authorization, use an independent `Unit` regime,
or install a constant `carry` unrelated to executed normalization. The exact
public regime and target certificate must fail.

### G. Exact image and fibre equivalence

For source profiles `p` and `q`, verify both directions of:

`carry p = carry q` if and only if the executed normalization produces the same
operational target for `p` and `q`.

The downstream regime must neither merge distinct produced targets nor split
equal produced targets. Width one must be derived only after this exact-image
result and executed convergence, not built into an unrelated obligation type.

### H. Exponential equivalence and scope

Verify a genuine theorem, in both directions, for every member of the stated
binary relational-role extensive class and every surjective obligation regime:

`regimeWidth = 2 ^ stageCount` if and only if `Function.Injective carry`.

Verify that separate addressing is constructed through the regime from
injectivity, rather than assumed independently or applied directly to the source
carrier. Confirm that the identity regime inhabits the exponential side.

State the exact generality: the binary equality, the variable-arity product
result, and any limitations. Do not present the finite-cardinality lemma alone
as the scientific target.

### I. Same profiles, different operational status

Verify on the same constituted source carrier that:

- two profiles are positively proved distinct;
- executed normalization codetermines them;
- the exact executed regime carries them together without identifying them;
- the separate regime keeps all profiles independently addressable and has
  width `2 ^ stageCount`.

### J. Constructivity and public closure

From a fresh checkout run at least:

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -File scripts/verify.ps1
git diff --check
```

Check that every production module is reachable from `import RelationalPerimeter`.
Check every Lean file for exactly one final `AXIOM_AUDIT` block. Scan all source
and generated declarations for axiom dependencies and distinguish handwritten
from compiler-generated declarations. Confirm the complete absence in source of
`axiom`, `sorry`, `admit`, `noncomputable`, `Classical`, `propext`, `Quot.sound`,
`native_decide`, `unsafe`, and `implemented_by`.

## Required adversarial result table

For every mutation above, record:

- the exact patch;
- whether the clean build and both verification scripts pass;
- the first substantive error when rejected;
- whether rejection comes from a constitutive type dependency, a theorem body,
  a linter, a name-level test, or documentation only.

Do not count an unused-variable warning, a missing theorem name, a removed test,
or a timeout as substantive rejection. Where a mutation initially fails only
for such a superficial reason, repair that superficial issue in the disposable
copy and continue the mutation test.

## Required report

Create a self-contained report under `audit/` containing:

1. revisions, hashes, environment, and reproduction commands;
2. build, constructivity, reachability, and integrity results;
3. a clause-by-clause verdict on the four immutable target paragraphs;
4. a declaration-level map of the nine constitutive layers;
5. a result for every mandatory check A–J;
6. the complete mutation table with reproducible patches and logs;
7. a list of every documentation statement stronger than Lean;
8. the exact scope and limitations of the final theorem;
9. final answers labelled `VERIFIED`, `QUALIFIED`, or `FALSE`;
10. one final verdict chosen only from:
   - `EXACT TARGET ESTABLISHED`
   - `EXACT TARGET REQUIRES CORRECTIONS`
   - `EXACT TARGET NOT ESTABLISHED`

`EXACT TARGET ESTABLISHED` is permitted only if all four target paragraphs and
all mandatory causal and relational dependencies are `VERIFIED`, and the
adversarial mutations are rejected for substantive reasons. Any `FALSE` target
clause entails `EXACT TARGET NOT ESTABLISHED`. Any `QUALIFIED` clause entails at
most `EXACT TARGET REQUIRES CORRECTIONS`.

Do not infer success from documentation, theorem names, private constructors, or
the existence of a certificate. Establish that every claimed dependency is
present in the types and actually consumed by the proof-producing construction.
