# Audit scope and resource identity — V4

This revision closes three obligations: state exactly what the scanners check, bind the complete bundle to its hashes, and prove coordinate agreement for both instances on every admissible history. The existing mathematical constructions keep their interfaces. V1–V3 scripts and receipts remain historical references.

## 1. Semantic forgetting and syntactic checks

`scripts/AuditForgettingV4.lean` checks exactly two `Nat` fields, `position` and `active`. It visits reachable types and definition bodies and rejects the names on its declared list. Its result concerns that shape and that list. The scanner uses Lean Meta tools; the mathematical declarations receive a separate axiom audit.

`Tests/HiddenEncoding.lean` demonstrates a recoverable origin encoded in scalar data. `Tests/ForgettingAuditScope.lean` adds structural local replay from an encoded origin using the local `next` transition. For every origin and finite depth, `replay_tracks` proves that its projection equals native execution, while `origin_recoverable` constructs an origin decoder. `replay_separates` distinguishes encoded memories with equal native projections. The V4 scanner accepts this implementation, recorded as `REPLAY_V4_SYNTAX_ACCEPTED`. Executable controls check origins `0..12` and depths `0..24`; the proof quantifies over all naturals.

The native memory's forgetting property follows from its own collision theorems: `origin_irrecoverable_from_prefixes` and `first_decision_irrecoverable` rule out a decoder correct on their declared prefix families. `colliding_prefixes_continue` proves equal native executions and observations at every depth from the equal erased memories. Continuation guarantees cover every finite independently admitted native suffix and the readings specified by that interface.

The forbidden-dependency fixture must fail with the forbidden-name diagnostic. The additional-field fixture must fail with the memory-shape diagnostic. These validate the scanner's specified checks. The accepted local replay witnesses its semantic limitation.

## 2. Exhaustive portable file catalogue

`scripts/ValidationManifestV4.ps1` traverses the entire root with `-Force`. It includes hidden files, dotfiles, extra root sources, auxiliary files, ordinary logs, documents, configuration and historical evidence. Exact exclusions are `.git`, `.lake`, `Migration/.lake` and `Comparison/.lake`. New run logs are written in those caches or in a fresh external output directory.

Inputs form I4; current evidence under `docs/validation-v4` forms E4. Each relative path is normalized with `/`, ordered ordinally and bound to its role, byte size and SHA-256. Links in the scientific domain and case collisions are rejected. Actual traversal must match the frozen catalogue exactly. The E4 index binds I4, both platform receipts and every evidence file. Each receipt binds commands, parameters, gate sources, exit codes, diagnostics and output hashes. Each platform file must also be one of that receipt's declared outputs. Inputs are checked before and after execution.

Catalogue tests check hidden and auxiliary entries, logs, same-size edits, missing files, invalid paths, case collisions, roles, sizes, digests and links. `test-validation-bundle-v4-r2.ps1` copies the complete real bundle and attacks sources, scripts, historical evidence, receipts, outputs, bindings and catalogue additions in that separate copy. The original bundle is checked again. Windows prevents creation of directory names differing only by case; both platforms test rejection of such names in the manifest.

Historical archives and comparison tools present in the root are also hashed as referenced material. Current compilation explicitly omits `Comparison` and access to the original project directory. V1/V2 receipts are checked against a dedicated extraction of Git snapshot `99f0801`. V3 evidence is itself hashed as historical input; its delivered bytes stay unchanged. Replaying V3 requires its own snapshot, while V4 binds the revised sources. Hash checks establish byte identity; the corresponding builds, proofs and tests establish their results.

## 3. General coordinate agreement

`RelationalFoundations/FiniteRuleCoordinates.lean` derives laws of the existing constructors. `Rules` retains its local procedures and laws. It receives no new field containing the desired global agreement.

| Declaration | Scope and conclusion |
|---|---|
| `homogeneous_native_coordinates` | Every `Token : Type u`, total selector, admitted history from the origin and common request: its common coordinate equals the native coordinate of the corresponding request, in the same constructed frame. |
| `heterogeneous_native_coordinates` | Every natural origin, admitted history, sort and typed request: agreement on the actual reference. |
| `homogeneous_coordinates`, `heterogeneous_coordinates` | Agreement with the original `complete` constructors through explicit transport between equal frames. |
| `homogeneous_inverse`, `heterogeneous_inverse` | Agreement of inverse request maps for every reference. |
| `homogeneous_operators`, `heterogeneous_operators` | Agreement of operators at these identified references. |
| `homogeneous_dependencies`, `heterogeneous_dependencies` | Agreement of declared dependency lists, preserving order, argument positions and repetitions. |
| `resumed_coordinates` | Every prior realization executed from the origin and every admitted suffix: include then coordinate equals coordinate then transport the old reference. |
| `homogeneous_resumed_coordinates`, `heterogeneous_resumed_coordinates` | Agreement with native transports for every prior realization, admitted continuation and old reference of both instances. |
| `resumed_composed_coordinates` | The same diagram for two actual successive resumptions, retaining intermediate executions and references. |
| `liftRequests_append`, `composed_coordinates` | Request inclusion respects suffix append through its associativity equality; the coordinate diagram holds for composed canonical extensions. |
| `resumed_operators`, `resumed_dependencies` | Preservation of operators and ordered inputs at the coordinates constructed by resumption. |

`realization_eq` normalizes actual realizations executed from the origin for the same history, including execution and frame. Coordinate results concern the constructors `complete`, `certify` and `resumeCompleteFrom`; native coordinate definitions remain those of the original constructions. Tests consume the general statements, a higher-universe token type, all thirteen homogeneous and seven heterogeneous example requests and an actual resumed execution.

The test `permuted` provides a certified abstract coverage at constant reading that exchanges two resource identities. `values_still_agree` proves equal readings; `permuted_changes_identity` proves different references. Agreement therefore follows the actual constructor; arbitrary `Coverage` witnesses can choose these different coordinates.

Lake compiles the new data producers. Exhaustive axiom audits inspect the mathematical declarations, with terminal audit blocks naming the principal results. Resource closure concerns finite admissible histories. Unbounded executor termination is a separate property.

## Reproduction

Use Lean `leanprover/lean4:v4.33.1` and PowerShell 7 in a full Git checkout containing `99f0801`:

```powershell
pwsh -NoProfile -File scripts/check-validation-v4.ps1
pwsh -NoProfile -File scripts/test-validation-bundle-v4-coverage.ps1
pwsh -NoProfile -File scripts/verify-validation-v4.ps1 -FrozenManifest docs/validation-v4/inputs.json
```

Each run creates a new `.lake/validation-v4/<id>` directory, or a supplied fresh `-OutputDirectory`. The [Windows](validation-v4/Windows/receipt.json) and [Linux](validation-v4/Linux/receipt.json) receipts record actual versions, commands and counts, bound by the [index](validation-v4/index.json) to the [common manifest](validation-v4/inputs.json). Bundle tests accept `-OutputPath` to preserve their separate receipt. GitHub Actions is configured for Windows and Ubuntu; local Windows and WSL Linux receipts remain distinct from a GitHub Actions run. An Aristotle submission is a separate action.

The versioned V4.1 coverage supplement, scripts/test-validation-bundle-v4-coverage.ps1, includes the complete V4 bundle test and adds allowed caches, hidden scripts, visible sources, nested additions, renaming, manifest roles and paths on the actual bundle. It also rejects a V3 receipt substituted for V4 and an indexed output lacking a receipt binding. Outer digests are rebound within the test copy to reach the internal checks. Original V4 scripts retain their version; final confirmation binds the manifest including this supplement.
