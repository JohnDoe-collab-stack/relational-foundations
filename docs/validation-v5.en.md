# Certified grouping reproduction — V5

The V5 protocol checks the new state described in [Certified grouping, projections and continuation](regroupements-certifies.en.md). V1–V4 scripts, manifests and execution evidence retain their bytes and respective scientific states. [Français](validation-v5.fr.md).

## Reproduction

Use Lean `leanprover/lean4:v4.33.1`, PowerShell 7 and a full Git checkout containing historical snapshots `99f0801` and `1887515`.

```powershell
pwsh -NoProfile -File scripts/check-validation-v5.ps1
pwsh -NoProfile -File scripts/test-validation-bundle-v5.ps1
pwsh -NoProfile -File scripts/verify-validation-v5.ps1 -FrozenManifest docs/validation-v5/inputs.json
```

The controller creates a fresh `.lake/validation-v5/<identifier>` directory. `-OutputDirectory` accepts a new external directory; an existing output directory is rejected. Without `-FrozenManifest`, it freezes the current inputs for that new run. Use the delivered manifest to reproduce the delivered results.

## Checks

The 19 gates check terminal audit blocks, the input catalogue, historical receipts, compilation and audits of foundations and migration, forgetting producers, coordinates, executable controls, eight native/grouping type rejections and two scanner rejections. Historical foundation and migration rejections also run under their dedicated catalogues. Rejection totals and source/declaration counts are derived from actual outputs.

`check-grouping-v5.ps1` adds a matrix of 5,461 mask/profile pairs for dimensions `0..6`. Each case checks the normalizer's target and trace bound. Parametric proofs cover every dimension. The gate compiles general migration consumers, audits imported mathematical declarations, scans actual dependencies of the three native reduced producers and records hashes of the 13 generated C modules. Metaprogrammed audits retain their specified scope; mathematical proofs and semantic separators are checked separately.

The migration audit separately inventories legacy generated auxiliaries `.injEq`, `.congr_simp`, `.eq_def` and `instRepr` display instances with axiom dependencies. Their complete names and dependencies are recorded in its log. This exception applies only to legacy computation modules. All declarations in new modules, authored historical declarations and tests retain the full transitive check: a proof using one of these auxiliaries is rejected. Success concerns this explicit mathematical scope; inventoried auxiliaries retain their separate status.

V5 stratification scripts assign explicit levels to the new adapters. Historical V3 inventories and rules remain preserved. The 806 legacy public targets and four import boundaries are checked.

## Result bindings

`ValidationManifestV5.ps1` exhaustively catalogues the directory, including hidden and auxiliary files. Exclusions are `.git`, `.lake`, `Migration/.lake` and `Comparison/.lake`. Historical evidence is an input; `docs/validation-v5` holds current evidence. Normalized relative paths, sizes, roles and SHA-256 values are checked before and after each run. The manifest identifies complete contents, including sources changed since the base commit.

The [common manifest](validation-v5/inputs.json) binds [Windows](validation-v5/Windows/receipt.json) and [Linux](validation-v5/Linux/receipt.json) receipts through the [index](validation-v5/index.json). Each receipt binds complete commands, parameters, versions, exit codes, diagnostics and output hashes. Generated temporary audit sources are included among bound outputs. Both confirmations use identical input bytes in separate environments. Linux runs natively in Ubuntu under WSL, with its own filesystem and caches.

`test-validation-bundle-v5.ps1` copies the complete bundle and attacks sources, scripts, receipts, outputs, historical evidence, paths and bindings. It also checks same-size changes and indexed outputs lacking receipt bindings. Tests run in an independent copy and recheck the original bundle. Confirmation diagnostics and totals are recorded in [Windows tests](validation-v5/Windows-bundle-tests.json) and [Linux tests](validation-v5/Linux-bundle-tests.json), indexed with other evidence. Development runs and their failures remain outside the delivered bundle.

GitHub Actions configuration replays this protocol on Windows and Ubuntu. Delivered confirmations are local executions. Git integration and external auditing are separate actions.
