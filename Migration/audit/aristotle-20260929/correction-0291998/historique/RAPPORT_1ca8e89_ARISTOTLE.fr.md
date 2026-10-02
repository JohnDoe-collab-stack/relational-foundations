# Rapport d'audit scientifique adversarial indépendant

**Dépôt :** `https://github.com/JohnDoe-collab-stack/relational-perimeter.git`
**Cible scientifique :** `1ca8e89ed02eacc71eb70efa1ccab84985fb8ace` (arbre `9379b85f008b7618ca3336a4a2c8e7730edd3681`)
**Auditeur :** Aristotle (Harmonic)
**Date :** 2026-09-29

> Toutes les pièces citées (journaux, patches, sondes, résultats structurés) se trouvent dans ce même dossier `audit/1ca8e89ed02eacc71eb70efa1ccab84985fb8ace/`. Aucune modification n'a été faite au checkout cible ; aucune poussée, aucune fusion.

**Verdict global (détaillé au §10) : `EXACT TARGET REQUIRES CORRECTIONS`.**

---

## 1. Identité des révisions, environnement, commandes et intégrité

### 1.1 Révisions

| Élément | Valeur attendue | Valeur observée | Statut |
|---|---|---|---|
| `HEAD` après `checkout --detach` | `1ca8e89e…` | `1ca8e89ed02eacc71eb70efa1ccab84985fb8ace` | OK |
| `HEAD^` | `ded0e8ef…` | `ded0e8ef4d343c091b66c80010c5a6827a589319` | OK |
| `HEAD^{tree}` | `9379b85f…` | `9379b85f008b7618ca3336a4a2c8e7730edd3681` | OK |
| `PARENT^` | `ea3f26c2…` | `ea3f26c20267cba42059e2f0d47bfe7e9244ee96` | OK |
| `merge-base TARGET MAIN_REF` | `8a5e494e…` | `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685` | OK |
| cible ancêtre du HEAD de livraison | oui | oui (`merge-base --is-ancestor` code 0) | OK |
| HEAD de livraison (branche) | mobile | `13eed60eac867cacfc4d4a0fddca33334ea882ed` | relevé |
| `main` distant (début et fin d'audit) | `8a5e494e…` | `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685` (inchangé) | OK |
| `git status --porcelain` avant / après | vide | vide / vide | OK |

Toutes les commandes initiales du protocole ont été exécutées dans un répertoire temporaire neuf et ont réussi (aucun blocage d'identité).

**Provenance du matériel de préparation.** Le commit `13eed60` (« audit: prepare immutable Aristotle adversarial review… ») est postérieur à la cible et ne touche que 20 fichiers, tous sous `audit/aristotle-20260929/`. Son fichier `evidence/verified-source-sha256.json` a été comparé à mon propre inventaire : **208/208 empreintes identiques** à l'arbre cible (0 divergence, 0 manquant). Ce matériel a été traité comme témoignage à revérifier : toutes les commandes et mutations historiques ont été ré-exécutées (§6). Son `preparation.json` déclare lui-même : « No new independent Aristotle audit has been run. Prior mutation results are historical, not target certification. »

### 1.2 Environnement effectivement disponible

| Capacité | Disponible | Détail |
|---|---|---|
| Checkout complet, shell, Git, réseau | oui | clone HTTPS complet |
| Lean | oui | `Lean (version 4.33.1, x86_64-unknown-linux-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)` = toolchain épinglée `leanprover/lean4:v4.33.1` |
| Lake | oui | `Lake version 5.0.0-src+819816b` |
| PowerShell (`pwsh`) | **non** | `pwsh: command not found`, code 127 → **`verify.ps1` = NOT RUN** partout |
| Mathlib | non utilisée | le dépôt ne dépend pas de Mathlib ; rien n'a été ajouté |

Aucun `.olean` d'une autre révision n'a été copié : chaque compilation (cible et variantes) part de `lake clean`.

### 1.3 Commandes J sur la cible (journaux `J/`)

| # | Commande | Code | Durée | Observations |
|---|---|---|---|---|
| 01 | `lean --version` | 0 | 0 s | voir ci-dessus |
| 02 | `lake --version` | 0 | 0 s | |
| 03 | `lake clean` | 0 | 1 s | |
| 04 | `lake build +RelationalPerimeter` | 0 | 578 s | 0 avertissement, aucun « depends on axioms » |
| 05 | `lake build` | 0 | 84 s | idem |
| 06 | `bash scripts/verify.sh` | 0 | 892 s | « Verified 140 Lean files: build, constructivity, audit blocks, import boundaries, and migration boundaries are clean. » |
| 07 | `pwsh -NoProfile -File scripts/verify.ps1` | 127 | 0 s | **NOT RUN** (pwsh absent) |
| 08 | `git diff --check` | 0 | 1 s | vide |
| 09 | `git status --porcelain` | 0 | 0 s | vide |
| 10 | `git rev-parse HEAD` | 0 | 1 s | `1ca8e89ed02eacc71eb70efa1ccab84985fb8ace` |

stdout/stderr séparés : `J/NN_*.stdout`, `J/NN_*.stderr` ; synthèse `J/summary.txt`.

### 1.4 Intégrité avant/après

- Inventaire initial : `inventory-before.txt` (208 fichiers suivis, dont 140 `.lean`, avec leurs imports), `sha256-before.txt`.
- Inventaire final : `sha256-after.txt`. `diff sha256-before.txt sha256-after.txt` → **identique**. `git status --porcelain` final vide ; `HEAD` et arbre inchangés.

### 1.5 Relevé de lecture (fichiers et plages)

| Fichier (au SHA cible) | Plages lues |
|---|---|
| `docs/conclusion-largeur-exponentielle-conservation-identites.fr.md` | intégral (l.1–230) |
| `docs/positionnement-et-portee.fr.md` | intégral (l.1–163) |
| `docs/decomposition-operationnelle-endogene.fr.md` | intégral (l.1–394) |
| `README.md` | l.242–330 (construction computationnelle, build, début du résumé français) ; plan complet par titres ; le reste n'est pas déclaré lu intégralement |
| `docs/relations-primitives-constitution-perimetre.fr.md` | l.117–183, l.522–578 ; plan complet par titres ; §2–§4 (périmètre circulaire, l.183–521) non relus intégralement (partie circulaire, hors du raccord computationnel audité) |
| versions anglaises (`docs/*.en.md`) | **non comparées intégralement** ; aucune divergence anglais/français n'est donc affirmée ni exclue |
| `ED/ConstitutiveExtensiveSeparation.lean` | l.160–300, l.330–420, l.630–740 (certificat, charges portées, raccord) |
| `ED/ExecutedFeedbackBridge.lean` | intégral (l.1–175) |
| `ED/ExecutedCausalNormalization.lean` | l.21–110, l.170–260, l.330–520, l.566, l.652 (structures, autorisation, image, régime, fibres, largeur) |
| `ED/RelationalConstitutiveRoles.lean` | l.1–215 |
| `ED/RoleIndexedProfiles.lean`, `ED/RoleIndexedProgram.lean`, `ED/RoleProfileSemantics.lean`, `ED/ExecutedRoleIndexedReduction.lean`, `ED/CausalOperationalExecution.lean`, `ED/PrefixLocalOperationalProduction.lean` | déclarations touchées par le raccord et par les mutations (définitions, preuves consommées) |
| `RelationalRoleExtensiveFamily.lean`, `FiniteExtensiveAddressing.lean`, `RelationalProfileConstitution.lean`, `SemanticImage.lean`, `ED/PublicRelationalExtensiveFamily.lean`, `ED/RolewiseObligationRegime.lean` | déclarations de l'`iff`, des porteurs et de `certify`/`use`/`viable_iff` |
| `RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean`, `RelationalPerimeter.lean` | façade (déclarations publiques), racine (imports) |
| `Tests/EndogenousWidthBridgeRegression.lean`, `Tests/RelationalExtensiveIffRegression.lean`, `Tests/ConstitutiveObjectiveRegression.lean`, `Tests/SemanticImageRegression.lean`, fixtures d'échec | parties touchées par les mutations ; câblage dans les vérificateurs |
| `scripts/verify.sh`, `scripts/verify.ps1`, `scripts/*.tsv`, `lakefile.toml`, `lake-manifest.json` | intégral pour les différences avec `ded0e8e` et `ea3f26c` |

La lecture n'est pas déclarée exhaustive au-delà de ce relevé.

---

## 2. Les quatre paragraphes, avec hypothèses et quantificateurs exacts

Texte cible (inchangé) et lecture précise, sans réduction :

**§P1.** « Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes. »
- P1.a : *primitivité* — les relations typées (formation, provenance, source, cible) sont premières et ce qui suit (témoins, occurrences, histoires, profils) en dépend.
- P1.b : *production endogène locale au préfixe* — pour chaque étape de l'exécution de référence, la tête est produite depuis l'état courant, la suite dépend de l'état et du contexte produits.
- P1.c : *détermination des obligations indépendantes* — le regroupement final (quelles alternatives restent séparées) est un résultat de cette exécution.
- Portée : l'exécution particulière instanciée sur la famille SAT engendrée du dépôt (`publicCausalOperationalExecution input`, pour tout `input : Nat`).

**§P2.** « Cette exécution ne produit pas d'explosion exponentielle de la largeur opérationnelle : bien que le déploiement extensif des profils constitués ait une largeur 2^n, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes. »
- Quantificateur : pour tout `input`, avec `n = input + 1`.
- P2.a largeur extensive `= 2^(input+1)` ; P2.b largeur du régime exécuté `= 1` ; P2.c « sans identifier » : des profils distincts restent distincts et sont portés ensemble.

**§P3.** « Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c'est-à-dire si son application `carry` est injective. »
- Quantificateurs : pour toute famille `BinaryRelationalRoleExtensiveFamily`, tout indice, tout problème, tout `ObligationRegime` (surjectif par construction) sur `family.sourceCarrier problem` : `regime.frontier.length = 2 ^ family.stageCount problem ↔ Function.Injective regime.carry`. « Exponentielle » signifie ici **exactement `2^n`** (pleine largeur), `n = stageCount`.

**§P4.** « L'explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l'effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même. »
- P4.a « effet exact » = conséquence de P3 ; P4.b « non nécessaire » = il existe, sur le même porteur, un régime de largeur `≠ 2^n` — et, selon le texte, c'est le régime *exécuté* qui en témoigne, la structure relationnelle étant celle du problème.

Paramétrage vérifié : pour l'instance publique, `stageCount = resolutionLength = input + 1` (égalité définitionnelle, `rfl`, `PublicRelationalExtensiveFamily.lean`) ; pour la classe, `n = family.stageCount problem`. Aucun remplacement du quantificateur général par des exemples : le théorème de classe est prouvé une fois pour toutes les familles (§5, H).

---

## 3. Carte des neuf niveaux constitutifs

Chemins relatifs à `RelationalPerimeter/Computation/ConstitutiveSearch/` ; `ED/` = `EndogenousDecomposition/`.

| Niveau | Fichier / déclaration | Producteur | Consommateur | Garantie | Rôle réel constaté |
|---|---|---|---|---|---|
| 1. Relations typées primitives (source, cible, provenance, formation) | `ED/RelationalConstitutiveRoles.lean` l.19–29 `RoleSourceAgreement`, `RoleTargetAgreement`, `RoleProvenanceAgreement` (= `PLift (observed = expected)`) ; `ED/RoleIndexedProfiles.lean` l.39 `RoleFormationAgreement` ; version abstraite `RelationalProfileConstitution.lean` (`RelationalOpeningStage` : familles `SourceRelation`, `FormationRelation`, `TargetRelation`, `ProvenanceRelation`) | `relationalConstitutiveRoleStage run` (l.91) : tous les témoins valent `⟨rfl⟩` | `searchStateExact`, `nextStateExact`, `provenanceExact` (`.down`), `formedAt` | égalité entre une copie stockée et la donnée exécutée | Dans l'instance exécutée, ces « relations » sont des **égalités** entre champs recopiés du `run` et le `run` lui-même ; elles sont *dérivées* de l'exécution (constructeur `private mk`, construction canonique) et non premières. Dans la classe abstraite, les familles sont arbitraires (peuvent être `Unit`, sonde `unitRelationFamily`). |
| 2. Témoins positifs | champs `sourceWitness`, `targetWitness`, `provenanceWitness` ; `RoleConstitutionEvidence` (`ED/RoleIndexedProfiles.lean` l.390) | `relationalConstitutiveRoleStage`, `roleConstitutionEvidence` (l.403) | élimination `.down`, `transportFormation` (l.424), `interpretRoleStageAtom` (argument d'évidence) | idem | Transportent une égalité récupérable ailleurs (M01/M02/H01/H02 survivent, §6). |
| 3. Occurrences de rôle constituées | `RoleOpeningOccurrence` (l.51), `RoleConstitutedOccurrence` (l.343), `roleConstitutedOccurrenceAt` (l.350), `realizeRoleConstitutedOccurrence` (l.368) | construction depuis le rôle | profils, action (`interpretRoleStageAtom`) | réalisation ↔ position (`openingPositionOccurrenceTransport`) | Transport interne de réalisation entre positions `left/right` et occurrences ; pas un second porteur. |
| 4. Histoires dépendantes | `RelationalConstitutiveRoleHistory` (l.149), `buildRelationalConstitutiveRoleHistory` (l.164), `RelationalRoleHistoryConstitutionExact` (l.174) | l'exécution `CausalOperationalExecutionHistory` via `stagewiseDecomposition.roles` | profils, programme, réduction | `rolesConstitutionExact` | Réelle dépendance typée de l'histoire à l'état produit (M05/M06 rejetées). |
| 5. Profils et frontière source | `RoleOccurrenceProfile` (l.490), `roleProfileFrontier` (l.547), `roleProfileFiniteCarrier` (`ED/RolewiseObligationRegime.lean` l.26), `roleProfileFiniteCarrier_width` (l.32) | produit fini des occurrences par rôle | régimes, normalisation, théorème de classe | complétude, `Nodup`, longueur `2^(input+1)` | Porteur unique (§4, B). La frontière extensive est une vraie liste énumérée (8 éléments pour `input = 2`). |
| 6. Transformation exécutée sur ces profils | `ED/RoleIndexedProgram.lean` (`compileRoleStageAtom`, `interpretRoleStageAtom`, `interpretCompiledRoleStage_left` l.115), `ED/ExecutedRoleIndexedReduction.lean` (`ActionProducedOperationalTarget.value` l.~270, `ExecutedRoleReductionHistory`), `ED/RoleProfileSemantics.lean` (`actProfile`, `localPreserves`, `canonicalAction_exact`) | élimination de la décision exécutée : `interpretRoleStageAtom` sur l'entrée exécutée | normalisation, `transformPayload` | action = carte découverte sur **toute** continuation (`interpretCompiledRoleStage_left`, `producedRoleAction_is_discovered`) | L'action totale est réellement la carte découverte (M07 rejetée). En revanche, la *cible* d'un profil est égale, par construction, à la cible retenue unique, indépendante de la source (sonde `target_independent_of_source`). |
| 7. Codétermination par élimination | `ED/ExecutedCausalNormalization.lean` : `ExecutedCausalNormalization` (l.21), `target` (l.173), `trace`, `target_exact` (l.198), `targets_converge` (l.212), `OperationallyCoDetermined` (l.518) | `executedCausalNormalization reduction` | régime, fibres | `target_exact` : toute cible = `retainedExecutedOperationalTargetProfile reduction` | La convergence est vraie **par construction** : la cible ne dépend pas du profil source. `OperationallyCoDetermined p q` est habité pour tout `p q`. |
| 8. Régime représentant son image, avec admission | `ExecutedOperationalGroupingAuthorization` (l.82, `private mk`, champ `causalExact`), `imageSpecification` (l.~250), `AuthorizedProducedTargetObligation` (l.330, paramètre `_authorization` fantôme), `transformPayload` (l.344), `authorizedOperationalRegime` (l.426), `carry_eq_iff_target_eq` (l.495), `carry_eq_iff_coDetermined` (l.566), `width_exact` (l.652) | `authorizedOperationalRegime` : frontière `[anchorObligation]`, `carry p = .admitted (target p) …` | pont public, tests | `Specification` via `SemanticImage.certify` ; `carry p = carry q ↔ target p = target q` | Image exacte : formellement vraie (§5, G), mais l'image a un seul point pour une raison de construction. Autorisation : garanties reconstructibles depuis la réduction (M09a/M09b/M11 survivent). |
| 9. Largeurs et équivalence exponentielle | `RelationalRoleExtensiveFamily.lean` (`BinaryRelationalRoleExtensiveFamily` l.41, `exponentialWidth_iff_preservesConstitutedIdentities` l.114, `abstractBinaryRelationalFamily` l.344), `FiniteExtensiveAddressing.lean`, `ED/PublicRelationalExtensiveFamily.lean` l.121, `ED/ConstitutiveExtensiveSeparation.lean` l.708 `binaryClass_fullWidthExactlyInjective` | combinatoire finie | pont, façade | `iff` général | Théorème authentique pour toute famille/problème/régime ; il n'utilise pas le contenu des relations (valable pour une famille où les quatre familles sont `Unit`, sonde `unitFamily_iff`). |

Ordre constitutif : l'ordre typé 1→9 est respecté dans les dépendances de modules et de types. Mais au niveau 1, l'ordre *de production* est inverse dans l'instance exécutée : le `run` (exécution) est premier, les relations sont des égalités lues depuis lui (`relationalConstitutiveRoleStage run`, tous témoins `⟨rfl⟩`).

---

## 4. Analyse du nouveau raccord et des preuves endogènes consommées

### 4.1 Point d'entrée

`RelationalPerimeter.Computation.EndogenousOperationalDecomposition.endogenous_production_and_width_separation` (façade `RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean`) réexporte `ConstitutiveSearch.EndogenousDecomposition.endogenousDecompositionAndWidth` (`ED/ConstitutiveExtensiveSeparation.lean` l.687), de type `EndogenousDecompositionAndWidth input` (structure `Prop`, l.638–685). `#print axioms` : « does not depend on any axioms » (`probes/J_key_axioms.out`).

### 4.2 Dépliage champ par champ

| Champ | Énoncé (déplié) | Preuve fournie | Données raccordées ? | Observation adversariale |
|---|---|---|---|---|
| `feedbackAtEveryStep` | `ExecutedFeedback.Along (publicCausalOperationalExecution input)` : à chaque tête `.step stage run production tail` : `StepFacts run` (découverte depuis la source, action = carte découverte sur l'entrée, sortie → état suivant, décisions/provenance/graine suivantes, domaine de candidats suivant filtré par la provenance produite, graine produite effectivement utilisée, états frères distincts, frère absorbé viable, préservation de viabilité, préservation sur toutes continuations) ∧ constitution exacte du rôle ∧ action compilée = carte découverte **pour toute continuation** ∧ `Along tail` | `public_along` = `along` par récursion structurelle (`ED/ExecutedFeedbackBridge.lean` l.111–160) | **oui** : même histoire que celle qui définit `publicRelationalConstitutiveRoles` (sonde B, `rfl`) | Propriétés extensionnelles de chaque étape exécutée ; elles ne fixent pas l'ordre d'évaluation (M04 survit). |
| `constitutedRoles` | `RelationalRoleHistoryConstitutionExact (publicRelationalConstitutiveRoles input)` | `rolesConstitutionExact` | oui | Exprime que chaque rôle est la lecture canonique de son étape. |
| `sourceAgreements` | `∀ p, RoleSemantics.ProfileConstitution p` | `(publicCarriedProfile_constitution input p).2 p` | oui | Aussi prouvable par `RoleSemantics.profileConstitution` seul, **sans aucune évidence** (sonde `constitution_without_evidence`) : égalités triviales entre champs de rôle. |
| `allProfilesRemainViable` | `∀ p, ∃ payload, ProfileAccept p payload` | charge canonique + `canonicalPayload_accepted` | oui | Viabilité point par point des continuations locales, pas une affectation globale commune. |
| `interpretedAction` | `(publicCarriedProfilePayload input p payload).1 = actProfile reduction p payload` pour **toute** charge | projection du sous-type de `transformPayload` | oui (via l'obligation portée) | L'égalité est portée par `SemanticImage.use` ; l'action est définie sans preuve d'acceptation (correct). |
| `preservation` | `ProfileAccept p payload → TargetAccept reduction (…).1` | idem | oui | Reconstructible depuis les licences de la réduction (M09a survit). |
| `sourceIndexedTrace` | `∀ p, Nonempty (ExecutedRoleProfileReduction reduction p (carry p).value)` | `publicCertificateCarryTrace` | oui | `carry p).value` ≡ `target p` définitionnellement dans la cible. |
| `exactCodetermination` | `carry p = carry q ↔ Nonempty (OperationallyCoDetermined normalization p q)` | `carry_eq_iff_coDetermined` | oui | Les deux membres sont vrais pour tout `p q` ; l'`iff` vaut aussi pour un régime `Unit` étranger (sonde `unitRegime_fibres`). |
| `distinctProfiles` | profil transformé ≠ profil retenu | `headProfilesDistinct` | oui | Distinction réelle des sources. |
| `groupedProfiles` | leurs `carry` sont égaux | `carry_eq_iff_coDetermined` + `targets_converge` | oui | |
| `extensiveWidth` | `(publicRoleProfileFiniteCarrier input).frontier.length = 2^(input+1)` | `roleProfileFiniteCarrier_width` | oui | Largeur de l'énumération extensive (objet de spécification, pas étape d'exécution). |
| `executedWidth` | `(publicCertificateExecutedRegime input).frontier.length = 1` | `width_exact` | oui | Frontière `[anchorObligation]` ; complétude prouvée par `all_eq`. |
| `transientWidth` | `WidthTraceAtMost 2 (widthTrace history)` | `public_widthTrace_le_two` via `widthTrace_existing` | oui | Lecture numérique des frontières locales ; pour `input = 2` : `[1,2,1,1,2,1,1,2,1]`. |
| `fullWidthExactlyIndependent` | `∀ regime, length = 2^(input+1) ↔ Injective regime.carry` | théorème de classe instancié | oui | Même porteur, sans cast (sonde B). |
| `separateRegimeWidth`, `separateRegimeConservation` | régime identitaire de largeur `2^(input+1)` conservant distinctement et séparément | `identityObligationRegime` | oui | Régime conservatif distinct construit sur le même porteur. |

**Assemblage.** Tous les champs portent sur la même histoire `publicCausalOperationalExecution input` et le même porteur `publicRoleProfileFiniteCarrier input` ; il ne s'agit pas de certificats indépendants juxtaposés sur des objets différents. En revanche, la structure ne relie pas logiquement les champs entre eux : chaque champ est une propriété séparée des mêmes objets. En particulier, rien dans le type n'exprime que le regroupement (`executedWidth`, `groupedProfiles`) *résulte* de `feedbackAtEveryStep` ; le regroupement découle de `target_exact` (cible indépendante de la source).

### 4.3 Preuves endogènes antérieures consommées

- **Tête et suite** (`ED/CausalOperationalExecution.lean` l.64 `executeCausalOperationalHead`, l.86 `executeCausalOperationalExecutionHistory`). La tête appelle `runThreadedNextDiscovery state`, construit l'étape via `buildThreadedConstitutiveStage`, puis `prefixLocalOperationalProducer context (causalStageOfThreadedStage run)`. La suite est typée par `run.nextRun.next` et le contexte étendu : **dépendance typée réelle** (M05, M06 rejetées au typage, l.97).
- **Production locale.** `executedStageDecomposition stage` : fonction de l'étape seule ; le contexte est stocké mais non utilisé pour calculer la décomposition.
- **Consommation de la provenance/graine produites.** `nextDiscoveryConsumesProducedProvenance`, `nextDiscoveryConsumesRetainedSearchSeed` : utilisés dans `StepFacts` (`nextCandidateDomain`, `nextSeedIsUsed`). Ce sont des égalités sur les états **émis par l'exécution de référence**, distinctes des états comparateurs contrefactuels des modules de non-factorisation.
- **Exclusion après échec.** La tête élimine le cas `none` par `runThreadedNextDiscovery_found` (hypothèse `fresh`) : aucune étape n'est construite après un échec de découverte.
- **Équations de tête / indépendance d'horizon.** Égalités de résultats ; elles restent vraies dans M04 où la tête est lue sur une histoire déjà achevée (preuves `rfl` inchangées). Elles ne constituent donc pas une preuve d'ordre d'évaluation.

---

## 5. Verdicts phrase par phrase et champ par champ

### 5.1 Validité des théorèmes Lean (i)

Tous les théorèmes audités compilent à la cible, sans `sorry`, sans axiome (y compris `propext`, `Quot.sound`, `Classical.choice`) : 660 déclarations non auxiliaires des six modules centraux, 0 avec axiome (`probes/J_key_axioms.out`). **VERIFIED.**

### 5.2 Adéquation au texte français (ii)

| Phrase / partie | Verdict | Énoncé réellement démontré et justification |
|---|---|---|
| P1.a « la constitution relationnelle des dépendances est primitive » | **QUALIFIED** | Les types des rôles, occurrences, profils sont indexés par les relations (ordre typé respecté). Mais dans l'instance exécutée, les relations sont `PLift (copie = donnée exécutée)` produites par `⟨rfl⟩` depuis le `run` ; les remplacer par `Unit` en aval (M01, H01) ou les ignorer (M02, H02) laisse **tous** les contrats publics et leurs clients intacts ; seule l'effacement de l'origine (M03a–e) casse, parce qu'on supprime alors l'égalité copie=donnée. Les familles relationnelles de la classe abstraite peuvent être `Unit` sans rien changer à l'`iff` (sonde `unitFamily_iff`). |
| P1.b « le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a déjà produit, sa décomposition » | **QUALIFIED** | Vrai au sens de la dépendance typée de la suite sur l'état/contexte produits (M05/M06 rejetées) et des faits `StepFacts` à chaque tête. Non établi au sens fort : une tête calculée à partir d'une histoire d'exécution déjà achevée (M04) passe tous les contrôles ; la décomposition est une fonction de l'étape seule (le contexte produit n'entre pas dans le calcul). |
| P1.c « et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes » | **QUALIFIED** | Le régime public a une seule obligation ; mais cette unicité découle de `target_exact` (toutes les cibles égalent la cible retenue unique, indépendamment de la source) ; une cible prescrite (M08) et une autorisation ignorée (M11) passent. Le « ainsi » (causalité de la détermination par la production) n'est pas exprimé par un énoncé. |
| P2.a largeur extensive `2^n`, `n = input+1` | **VERIFIED** | `extensiveWidth`, `roleProfileFiniteCarrier_width`. |
| P2.b « le régime exécuté les regroupe en une seule obligation » | **VERIFIED** (au sens formel) / **QUALIFIED** (au sens de « exécuté ») | `executedWidth = 1`, `groupedProfiles`. Le régime est construit depuis la normalisation exécutée ; mais le singleton est obtenu par convergence triviale et un `carry` constant vers l'ancrage passe aussi (voir G, M12). |
| P2.c « sans identifier les profils eux-mêmes » | **VERIFIED** | `distinctProfiles` sur le même porteur, `carry` non injectif, régime identitaire distinct. La garantie de distinction de l'autorisation est une copie reconstructible depuis la réduction (M09b), sans affecter l'énoncé. |
| P2 « ne produit pas d'explosion exponentielle de la largeur opérationnelle » | **QUALIFIED** | Démontré pour la largeur du régime final (1) et la trace transitoire (≤ 2). Aucune borne de temps ou de mémoire ; la frontière extensive de `2^n` profils est bien énumérée en tant qu'objet de spécification (`roleProfileFrontier`) et n'est pas présentée comme opération de largeur constante. |
| P3 équivalence dans la classe binaire | **VERIFIED** | `binaryClass_fullWidthExactlyInjective` : `∀ family problem (regime : ObligationRegime (family.sourceCarrier problem)), regime.frontier.length = 2 ^ family.stageCount problem ↔ Function.Injective regime.carry`. Surjectivité incluse dans `ObligationRegime`. Pleine largeur exacte, pas croissance asymptotique. |
| P4.a « effet exact de cette exigence » | **VERIFIED** | Conséquence directe de P3. |
| P4.b « et non comme une conséquence nécessaire de la structure relationnelle du problème » | **QUALIFIED** | `extensiveMultiplicity_doesNotForceFullOperationalWidth` est vrai et sa preuve utilise le régime exécuté ; mais son énoncé est prouvable par un régime `Unit` arbitraire (sonde `notForced_withoutExecution`) et le théorème de classe ne dépend pas du contenu des relations. La non-nécessité est donc établie *pour ce porteur* par un argument de cardinalité ; le lien avec « la structure relationnelle du problème » n'est pas porté par un énoncé qui échouerait sans elle. |

**Verdict par paragraphe** : P1 **QUALIFIED** ; P2 **QUALIFIED** ; P3 **VERIFIED** ; P4 **QUALIFIED**. Aucun paragraphe **FALSE**.

---

## 6. Contrôles A–J et table complète des mutations

### 6.1 Dispositif

- Une copie jetable par variante (`git worktree`/clone local depuis le SHA de base), SHA de départ dans `mutations/<id>/base_sha.txt`, patch complet `final.patch`, fichiers `files.txt`.
- Pour chaque variante finale : `lake clean`, `lake build +RelationalPerimeter`, `lake build`, `bash scripts/verify.sh`, (`pwsh` NOT RUN), `git diff --check` ; stdout/stderr séparés ; synthèse `summary.txt`.
- Témoin non modifié dans le même dispositif : la cible elle-même (`J/`), et le parent `ded0e8e` pour H01/H02.
- Variantes de développement (itérations de réparation par compilation ciblée) : `dev/<id>.patch` + `dev/<id>.out`.
- Si la compilation racine échoue, les étapes aval échouent par causalité (non comptées comme rejets indépendants).

### 6.2 Table des mutations

Légende des colonnes : **Codes** = clean / build root / build all / verify.sh / verify.ps1 / diff-check.

| Id | Clause | Base | Fichiers modifiés | Contrat inchangé | Codes | Premier défaut substantiel | Origine du rejet | Données encore récupérables | Classification | Effet sur la phrase |
|---|---|---|---|---|---|---|---|---|---|---|
| H01 | A (hist.) quatre familles publiques → `Unit` | `ded0e8e` | patch historique A6 (`historical/A6-*.applied.patch`) | tous contrats et tests du parent | 0/0/0/0/NR/0 | aucun | — | accords récupérés depuis rôles/occurrences riches | **SURVIVES** | P1.a |
| H02 | A (hist.) stocker mais ignorer l'évidence | `ded0e8e` | patch historique A5 | idem | 0/0/0/0/NR/0 | aucun | — | idem | **SURVIVES** | P1.a |
| M01 | A : quatre familles → `Unit`, rebasée sur la cible, y compris nouveaux clients du raccord | `1ca8e89` | voir `mutations/M01-*/files.txt` | tous, dont `EndogenousDecompositionAndWidth` et `Tests/EndogenousWidthBridgeRegression.lean` | 0/0/0/0/NR/0 | aucun | — | idem | **SURVIVES** | P1.a |
| M02 | A : témoins conservés mais ignorés, rebasée | `1ca8e89` | idem | tous | 0/0/0/0/NR/0 | aucun | — | idem | **SURVIVES** | P1.a |
| M03a | A : effacement de l'origine de l'accord source (`RoleSourceAgreement` → `Unit`) | `1ca8e89` | `ED/RelationalConstitutiveRoles.lean` | tous | 0/1/1/1/NR/0 | `searchStateExact` : `.down` sur `PUnit` (l.73) | substantiel : l'égalité `searchState = source` n'est plus dérivable | aucune (la copie `searchState` n'est plus reliée à `source`) | **SUBSTANTIVE REJECTION** | P1.a (voir note) |
| M03b | A : origine de l'accord cible | `1ca8e89` | idem | tous | 0/1/1/1/NR/0 | `nextStateExact` (l.80) | substantiel | aucune | **SUBSTANTIVE REJECTION** | P1.a |
| M03c | A : origine de l'accord de provenance | `1ca8e89` | idem | tous | 0/1/1/1/NR/0 | `provenanceExact` (l.87) | substantiel | aucune | **SUBSTANTIVE REJECTION** | P1.a |
| M03d | A : origine de l'accord de formation | `1ca8e89` | `ED/RoleIndexedProfiles.lean` | tous | 0/1/1/1/NR/0 | `formedAt` (l.67) | substantiel | aucune | **SUBSTANTIVE REJECTION** | P1.a |
| M03e | A : les quatre origines effacées | `1ca8e89` | les deux | tous | 0/1/1/1/NR/0 | premier : l.73 | substantiel | aucune | **SUBSTANTIVE REJECTION** | P1.a |
| A-occ | A : occurrences constituées → porteur brut | — | — | — | — | — | — | — | **NOT RUN** | P1.a |
| M04 | C : tête lue sur une histoire d'exécution déjà achevée (`completedFirstStage? (executeConstitutiveExecutionHistory 1 state fresh)`), théorèmes d'horizon inchangés, preuve `instrumented_exact` réparée | `1ca8e89` | `ED/CausalOperationalExecution.lean` (`M04.patch`) | tous | 0/0/0/0/NR/0 | aucun | — | — | **SURVIVES** | P1.b (sens fort) |
| M05 | C : suite repartant de l'état racine | `1ca8e89` | `ED/CausalOperationalExecution.lean` | tous | 0/1/1/1/NR/0 | incompatibilité d'index typé l.97 | substantiel : la suite est indexée par l'état produit | — | **SUBSTANTIVE REJECTION** | P1.b |
| M06 | C : suite avec contexte `.root` indépendant | `1ca8e89` | idem | tous | 0/1/1/1/NR/0 | idem l.97 | substantiel : index de contexte | — | **SUBSTANTIVE REJECTION** | P1.b |
| M07 | D : action gauche → sortie canonique constante `role.completedOutput` | `1ca8e89` | `ED/RoleIndexedProgram.lean` | tous | 0/1/1/1/NR/0 | `interpretCompiledRoleStage_left` (l.115) : `rfl` contre la carte découverte sur continuation arbitraire | substantiel : l'action totale n'est plus la carte découverte | égalités sur l'échantillon canonique réparables (`dev/D1b`) | **SUBSTANTIVE REJECTION** | P1.b / action |
| D1b | D : M07 + réparations canoniques | `1ca8e89` | `RoleIndexedProgram`, `RoleProfileSemantics`, `PrefixLocalOperationalProduction`, test | bibliothèque ; **mais** suppression de `interpretCompiledRoleStage_left`, `compiledRoleStage_action_changes_executed_source` et des tests `compiledActionIsMaterial`, `transformedOccurrenceUsesDiscoveredAction` | dev : bibliothèque compilée ; échec sur le bloc `AXIOM_AUDIT` du test (référence supprimée) | — | — | — | non-survie (clients substantiels supprimés) ; confirme M07 | Observation : les champs du raccord seuls ne détectent pas l'action constante. |
| M08 | D : cible prescrite `value := role.completedOutput` + égalité `valueExact` prouvée après coup, tests réparés propositionnellement | `1ca8e89` | `ED/ExecutedRoleIndexedReduction.lean`, `Tests/RelationalExtensiveIffRegression.lean` (2 preuves `rfl` → lemme/`rw`, énoncés inchangés) | tous | 0/0/0/0/NR/0 | aucun | — | la cible prescrite est propositionnellement égale à l'action | **SURVIVES** | P1.b/P1.c (production de la cible) |
| M09a | E : préservation de l'autorisation remplacée par sa reconstruction depuis les licences de la réduction | `1ca8e89` | `ExecutedCausalNormalization`, `RoleProfileSemantics` (+`profilePreservesFromReduction`) | tous | 0/0/0/0/NR/0 | aucun | — | `license.preservesCriterion` → `localPreserves` | **SURVIVES** (copie dispensable) | P1.c/P2 |
| M09b | E : séparation de l'autorisation remplacée par reconstruction depuis la réduction | `1ca8e89` | idem (+`sourcesRemainDistinctFromReduction`) | tous | 0/0/0/0/NR/0 | aucun | — | `license.occurrencesRemainDistinct` | **SURVIVES** (copie dispensable) | P2.c |
| E-deep | E : retrait de la garantie jusqu'à sa source (`role.preservation`, `executedSiblingReduction_preservesAccept`) | — | — | — | — | — | — | — | **NOT RUN** | P2 |
| M10 | F : régime public `Unit` indépendant | `1ca8e89` | `ED/ConstitutiveExtensiveSeparation.lean` | tous | 0/1/1/1/NR/0 | `transformPayload` sur `PUnit` (l.307) | substantiel : le contrat est typé sur les valeurs d'obligation portant une spécification | — | **SUBSTANTIVE REJECTION** | P2.b |
| M11 | F : autorisation ignorée (`_authorization`), constitution/préservation/séparation reconstruites depuis la réduction | `1ca8e89` | `ExecutedCausalNormalization`, `RoleProfileSemantics` | tous | 0/0/0/0/NR/0 | aucun | — | toutes les garanties depuis la réduction riche | **SURVIVES** | P1.c/F |
| F-True | F : garantie portée remplacée par `True` | — | — | — | — | — | — | — | **NOT RUN** | F |
| M12 | F/G : `carry` constant vers l'ancrage ; `carry_eq_iff_target_eq` réparée par `targets_converge` ; `viable_iff` réparée ; clients réparés propositionnellement (`rfl` → `targets_converge`, transport de la trace) | `1ca8e89` | `ExecutedCausalNormalization`, `ConstitutiveExtensiveSeparation` (`mutations/M12-*/final.patch` ; itérations `dev/F4.*`) ; tests **inchangés** | tous (énoncés publics identiques, dont `carry_eq_iff_target_eq`, `publicCertificate_carry_value_eq_produced_target`, `EndogenousDecompositionAndWidth`) | 0/0/0/0/NR/0 | aucun (premières erreurs de la 1re itération : `rfl` et délai `whnf` sur l'égalité `carry p).value = target p`, **superficielles**, réparées par `targets_converge`) | — | convergence triviale des cibles | **SURVIVES** | P2.b, G |
| S-unitFamily (sonde) | H/A : membre binaire dont les quatre familles sont `Unit` | `1ca8e89` | sonde externe `probes/H_I_probes.lean` | — | `lake env lean` 0 | — | — | — | l'`iff` et `2^n` valent (sans axiome) | P3/P4.b |
| S-notForced (sonde) | I : énoncé de `extensiveMultiplicity_doesNotForceFullOperationalWidth` prouvé par un régime `Unit` arbitraire | `1ca8e89` | idem | — | 0 | — | — | — | énoncé indépendant de l'exécution | P4.b |
| S-unitFibres (sonde) | G : `carry p = carry q ↔ OperationallyCoDetermined` vaut pour le régime `Unit` | `1ca8e89` | idem | — | 0 | — | — | — | fibres non discriminantes | G |

Note sur M03 : il faut distinguer (1) effacer une copie aval en récupérant l'accord depuis un rôle riche — M01/M02/H01/H02, **survit** — et (2) effacer aussi l'origine constitutive — M03, **rejet**. Le rejet (2) montre qu'une égalité copie=donnée est consommée ; il ne montre pas qu'une relation primitive précède l'exécution : l'origine elle-même est `⟨rfl⟩` sur des champs recopiés du `run`.

### 6.3 Résultats A–J

| Contrôle | Résultat | Justification |
|---|---|---|
| **A** Primitivité | **QUALIFIED** (mutations obligatoires survivantes) | M01/M02/H01/H02 survivent ; M03a–e rejetées pour une raison substantielle mais triviale (égalité de copie) ; A-occ NOT RUN. Producteur de chaque accord : `relationalConstitutiveRoleStage` / `roleConstitutionEvidence` (`⟨rfl⟩`) ; consommateurs : `searchStateExact`, `nextStateExact`, `provenanceExact`, `formedAt`, `transportFormation` ; voie de récupération : champs riches du rôle. |
| **B** Porteur unique | **VERIFIED** | Sonde `probes/B_carriers.lean` : égalités par `rfl` (définitionnelles) entre le porteur des rôles de l'histoire exécutée, celui du régime, `family.sourceCarrier` de l'instance publique, `imageDescription.Source` et le domaine de l'action ; le théorème de classe s'applique au régime public sans cast. Transports internes (`openingPositionOccurrenceTransport`, `roleProfileTransport`) = réalisation positions↔occurrences, pas un second porteur. |
| **C** Production endogène locale | **QUALIFIED** | M05/M06 rejetées (dépendance typée) ; M04 survit (tête lue sur histoire achevée ; rejet non produit par la dépendance de production) ; décomposition = fonction de l'étape seule. Invalide la prétention forte « l'ordre d'évaluation est garanti par les types » ; ne réfute pas l'existence de l'exécution de référence. Observation J : la fixture d'échec `FutureCannotProduceOwnHead` n'est câblée dans aucun vérificateur et, à l'essai, n'est rejetée que par non-terminaison d'une récursion mutuelle. |
| **D** Cibles produites, action non prescrite | **QUALIFIED** | Action : M07 rejetée substantiellement (action totale = carte découverte, VERIFIED). Cible : M08 survit (cible prescrite + égalité). `canonicalPayload_accepted` et convergence canonique distincts de la préservation sur toute continuation (champs séparés `interpretedAction`/`preservation`) ; aucune déduction que toutes les charges donnent la même valeur. |
| **E** Préservation et distinction dans l'admission | **QUALIFIED** | Les garanties sont effectivement consommées par `imageSpecification` → `certify` → `use` → `transformPayload` ; mais les copies de l'autorisation sont dispensables (M09a/M09b) ; retrait profond NOT RUN. Critère : acceptation point par point des continuations locales (`ProfileAccept`/`TargetAccept`), non une solution globale. L'action reste définie sans acceptation (VERIFIED). Viabilité positive de chaque profil : `allProfilesRemainViable` (VERIFIED). |
| **F** Autorisation et obligation utilisable | **QUALIFIED** | Régime `Unit` indépendant rejeté (M10, substantiel) ; autorisation ignorée survit (M11) ; paramètre `_authorization` de `AuthorizedProducedTargetObligation` fantôme ; `Specification` vraie pour toute valeur (via `certify`) ; F-True NOT RUN ; `carry` constant : **SURVIVES** (M12). Appartenance à l'image (`produced`) et admission (`semantics`) sont des champs distincts ; l'admission ne dépend pas effectivement de l'autorisation. |
| **G** Image exacte et fibres | **QUALIFIED** | Les deux directions de `carry p = carry q ↔ target p = target q` sont prouvées (`carry_eq_iff_target_eq`, l.495) ; complétude/`Nodup` de la frontière, surjectivité, trace de chaque source, cible produite : VERIFIED. Mais l'image est un point par construction (`target_exact`), l'`iff` n'est pas discriminant (sonde `unitRegime_fibres`) et un `carry` constant vers l'ancrage survit (M12). Le porteur ambiant des continuations n'a pas été rendu singleton (VERIFIED). |
| **H** Équivalence exponentielle | **VERIFIED** | `iff` général prouvé (combinatoire finie, `FiniteExtensiveAddressing.lean`) ; adressage séparé construit depuis l'injectivité ; régime identitaire ; membre indépendant `abstractBinaryRelationalFamily` ; non-borne `unboundedStages` ; formule à arités variables = produit des arités (`productFrontier_length`, famille à arités croissantes). Le lemme fini seul ne prouve pas la cible complète. |
| **I** Mêmes profils, statuts différents | **QUALIFIED** | Sur le même porteur : profils distincts, continuations canoniques acceptées, traces vers la cible commune, portage commun sans égalité des sources, régime conservatif de pleine largeur : VERIFIED. `extensiveMultiplicity_doesNotForceFullOperationalWidth` utilise bien le régime exécuté, mais son énoncé ne l'exige pas (sonde). Largeurs séparées : extensive `2^n` (spécification), frontière en attente/transitoire ≤ 2 (`widthTrace`, lecture numérique des frontières locales ; `widthTrace_existing` = trace existante de l'effacement de la même histoire), régime final 1. Aucune borne de temps/mémoire. |
| **J** Compilation, constructivité, fermeture | **QUALIFIED** | Toutes commandes exécutables : code 0. `verify.ps1` **NOT RUN** (pwsh absent). Modules atteignables depuis `import RelationalPerimeter` : oui (vérifié par `verify.sh`, règle d'import) ; stratification A5→A6→A7→A8→A9 contrôlée dans les deux scripts via `stratification.tsv` (seul ajout vs parents : une ligne `ExecutedFeedbackBridge` en A6 — pas un assouplissement). Vérificateurs, `lakefile`, manifeste inchangés vs `ded0e8e` et `ea3f26c` hormis cet ajout. **Faiblesse** : 5 fixtures d'échec attendu non câblées dans les vérificateurs (`CanonicalSampleCannotPrescribeAction`, `FutureCannotProduceOwnHead`, `MissingImageConstitution`, `MissingImagePreservation`, `RootCannotReplaceProducedTail`, ajoutées en `ded0e8e`) ; `IndependentUnitRegime` ne teste que la non-égalité définitionnelle. Axiomes : §7. |

---

## 7. Inventaire des axiomes

### 7.1 Sources

Recherche lexicale (`verify.sh`, contrôle « constructivity », code 0) des termes `axiom`, `sorry`, `admit`, `noncomputable`, `Classical`, `propext`, `Quot.sound`, `native_decide`, `unsafe`, `implemented_by` dans le code effectif : aucune occurrence dans le code ; les occurrences restantes sont dans des commentaires, chaînes des scripts et fixtures d'échec. Chaque fichier Lean pertinent contient exactement un bloc final `AXIOM_AUDIT_BEGIN … AXIOM_AUDIT_END` (contrôle « audit blocks » de `verify.sh`) ; toutes les lignes `#print axioms` des blocs affichent « does not depend on any axioms » (0 occurrence de « depends on axioms » dans `J/04_build_root.stdout` et `J/05_build_all.stdout`).

### 7.2 Dépendances transitives

Sonde `probes/J_axiom_inventory.lean` (`Lean.collectAxioms` sur les 14 454 constantes du projet) : 349 constantes ont des axiomes, **toutes générées automatiquement** :

| Catégorie | Nombre | Axiome | Origine |
|---|---|---|---|
| `*.mk.injEq` (théorèmes d'injectivité de constructeurs) | 344 | `propext` | générés pour chaque structure |
| `inspectCandidateHistory.eq_def`, `inspectCandidateProvenance.eq_def` (`ED/ConstitutiveFeedback.lean`) | 2 | `Quot.sound` | équations de définition générées |
| `Extensive.firstIndexOf.congr_simp` (`FiniteExtensiveAddressing.lean`) | 1 | `Quot.sound` | lemme de congruence généré |
| `SAT.instReprCandidateExtractionRun` et `.repr` (`SAT/SecondAuditCausalBenchmark.lean`, `deriving Repr`) | 2 | `propext` | instance dérivée |

Sonde `probes/J_key_axioms.lean` : sur les 660 déclarations non auxiliaires des modules `EndogenousOperationalDecomposition` (façade), `ConstitutiveExtensiveSeparation`, `ExecutedFeedbackBridge`, `ExecutedCausalNormalization`, `RelationalRoleExtensiveFamily`, `FiniteExtensiveAddressing`, **0** dépend d'un axiome ; `endogenous_production_and_width_separation` : « does not depend on any axioms ». Comme `collectAxioms` est transitif, aucun des 349 auxiliaires ci-dessus n'est atteignable depuis les résultats audités.

### 7.3 Variantes

Aucune variante finale ne contient `sorryAx` (0 occurrence dans les journaux `03_build_all.stdout` des survivantes). Une première version de M04 avec `match` dépendant introduisait `propext` et aurait été rejetée par la seule barrière d'axiomes ; la version finale n'en a pas. Les `sorryAx` apparaissant après erreurs dans `dev/F4.out` (première itération) proviennent d'erreurs d'élaboration et n'ont été utilisés comme preuve d'aucun résultat.

---

## 8. Divergences documentation / Lean

| # | Assertion documentaire | Énoncé réellement démontré |
|---|---|---|
| 1 | « relations typées primitives » (README, `docs/relations-primitives-constitution-perimetre.fr.md`, commentaires `Primitive agreement…`) | Dans l'instance exécutée : `PLift (copie = donnée exécutée)` créées `⟨rfl⟩` depuis le `run` ; remplaçables par `Unit` en aval sans perte (M01). Dans la classe : familles arbitraires, non utilisées par l'`iff`. |
| 2 | « le calcul produit sa décomposition pendant son exécution » (`docs/decomposition-operationnelle-endogene.fr.md`) | Dépendance typée de la suite sur l'état/contexte produits ; propriétés extensionnelles `StepFacts` à chaque tête ; pas de garantie d'ordre d'évaluation de la tête (M04). |
| 3 | « la codétermination est produite par élimination de la chaîne exécutée » ; commentaire `targets_converge` : « The executed traces, not the ambient target carrier, prove convergence » | `target_exact` : toute cible = `retainedExecutedOperationalTargetProfile reduction`, sans dépendance à la source ; la convergence est une égalité de constante. |
| 4 | « régime représentant exactement son image, avec admission justifiée » ; « The public regime is formed only through its exact grouping authorization » | `AuthorizedProducedTargetObligation` a un paramètre d'autorisation fantôme ; `Specification` obtenue par `certify` pour toute valeur ; autorisation dispensable (M11). |
| 5 | « the actual executed witness refutes necessity of full extensive width » | Vrai, mais l'énoncé est prouvable par tout régime `Unit` (sonde). |
| 6 | `docs/conclusion-largeur-exponentielle-conservation-identites.fr.md` : équivalence exponentielle | Conforme : pleine largeur `2^n` exacte, pour toute famille binaire, `n = stageCount`. |
| 7 | `docs/positionnement-et-portee.fr.md` : pas de `P = NP`/`P ≠ NP`, pas de borne de temps/mémoire | Conforme ; aucun énoncé de ce type dans le code. |
| 8 | README l.~287 : « Both gates traverse the declared import boundaries and compile the expected-failure fixtures. » | 5 fixtures d'échec (`CanonicalSampleCannotPrescribeAction`, `FutureCannotProduceOwnHead`, `MissingImageConstitution`, `MissingImagePreservation`, `RootCannotReplaceProducedTail`) ne sont exécutées par aucun des deux vérificateurs (§6.3 J). |
| 9 | `docs/conclusion-…` : « le `carry` conserve littéralement la cible produite pour chaque source » ; « un singleton indépendant ne possède pas ce type » | Vrai de la définition cible (`publicCertificate_carry_value_eq_produced_target` par `rfl`) ; un singleton de type `Unit` est rejeté (M10) ; mais un `carry` constant vers l'ancrage, dans le même type d'obligation, voir M12 : **SURVIVES** (M12). Aucun client public n'exige la propriété « littérale ». |
| 10 | `docs/decomposition-…` : « cette autorisation n'est ni remplacée ni inférée depuis le seul résultat numérique » | Elle n'est pas inférée du résultat numérique, mais elle est dispensable : toutes ses garanties se reconstruisent depuis la réduction (M11). |
| 11 | `docs/decomposition-…` / `conclusion-…` : « Ce type local ne possède aucun paramètre de futur » | Exact pour le type de `ExecutedStageOperationalProduction` ; mais la tête de l'exécution peut être extraite d'une histoire exécutée achevée sans changer aucun contrat (M04). |
| 12 | `docs/decomposition-…` l.33–40 : témoins de formation/provenance « récupérés dans `Type` » depuis l'étape relationnelle | Récupérables, mais remplaçables par `Unit` en aval (M01) : ils ne sont pas indispensables aux conclusions. |
| 13 | `docs/relations-primitives-…` l.170–177 : « endogénéité relative … les relations et leurs témoins peuvent être donnés » | Le cadre de l'auteur admet explicitement des relations données ; la cible du protocole exige cependant la *primitivité* des relations dans la constitution des dépendances ; dans l'instance exécutée, elles sont lues depuis l'exécution et non données en amont. |
| 14 | Libellé de P2 : le prompt dit « le déploiement extensif des profils constitués », le document `conclusion-…` dit « la lecture extensive du carrier des profils constitués » | Différence de formulation ; l'énoncé Lean (`extensiveWidth`) correspond à la longueur de la frontière du porteur. |

---

## 9. Périmètre exact

- **Instance exécutée** : famille SAT engendrée du dépôt, `publicCausalOperationalExecution input` pour tout `input : Nat`, `n = input + 1`. Profils : `RoleOccurrenceProfile (publicRelationalConstitutiveRoles input)`, `2^(input+1)` profils binaires. Régime exécuté : une obligation. Trace transitoire ≤ 2.
- **Classe générale** : toute `BinaryRelationalRoleExtensiveFamily`, tout problème, tout régime (surjectif par définition), `n = stageCount problem` ; équivalence pleine largeur `2^n` ↔ `carry` injectif. Aucun résultat d'exécution endogène n'est attribué aux membres abstraits.
- **Critère** : acceptation point par point des continuations locales ; pas d'affectation globale commune, pas d'arbre adaptatif.
- **Largeurs** : extensive (spécification, liste énumérée de `2^n`), transitoire (lecture des frontières locales), finale (régime) — distinctes.
- **Hors périmètre** : `P = NP`, `P ≠ NP`, toute borne universelle de temps/mémoire, toute propriété de tout arbre adaptatif, toute croissance « asymptotiquement exponentielle » autre que `2^n` exact.

---

## 10. Conclusion

### 10.1 Sur l'objectif scientifique

- **Démontré (Lean, sans axiome, compilé ici)** : l'équivalence de classe `length = 2^stageCount ↔ Injective carry` pour toute famille binaire formalisée (P3) ; sur l'instance publique, la largeur extensive `2^(input+1)`, un régime construit depuis la normalisation exécutée de largeur 1 portant ensemble deux profils distincts, l'action totale égale à la carte découverte sur toute continuation, la préservation point par point, la dépendance typée de la suite sur l'état et le contexte produits, un porteur public unique définitionnellement partagé, la trace transitoire ≤ 2.
- **Non démontré au sens fort exigé** : (a) la *primitivité* des relations (elles sont des égalités lues depuis l'exécution et remplaçables en aval) ; (b) une production de la tête garantie par la dépendance de production plutôt que par une égalité de résultat ; (c) que le regroupement en une obligation soit *déterminé* par l'exécution plutôt que par la construction de la cible (`target_exact`, cible indépendante de la source) ; (d) une autorisation effectivement indispensable ; (e) une non-nécessité (P4.b) portée par un énoncé qui dépende de la structure relationnelle ou de l'exécution.
- **Dépendance exacte restant en cause** : `ExecutedCausalNormalization.target_exact` (toutes les cibles égalent `retainedExecutedOperationalTargetProfile`) combiné à `SemanticImage.certify` et au paramètre fantôme `_authorization` : c'est là que la convergence, l'image exacte et l'admission deviennent vraies indépendamment de la production ; et `relationalConstitutiveRoleStage` (`⟨rfl⟩`) pour la primitivité.
- **Preuves / contre-exemples** : mutations survivantes M01, M02, H01, H02 (A), M04 (C), M08 (D), M09a, M09b (E), M11 (F), M12 (F/G, `carry` constant vers l'ancrage) ; sondes `unitFamily_iff`, `notForced_withoutExecution`, `unitRegime_fibres`, `constitution_without_evidence`, `target_independent_of_source`.

### 10.2 Verdict global du protocole

Paragraphes : P1 QUALIFIED, P2 QUALIFIED, P3 VERIFIED, P4 QUALIFIED ; aucun FALSE. Contrôles : B et H VERIFIED ; A, C, D, E, F, G, I, J QUALIFIED ; mutations obligatoires survivantes ; cas NOT RUN (A-occ, E-deep, F-True, `verify.ps1`) ; lecture documentaire non intégrale pour `README.md`, `docs/relations-primitives-…` et les versions anglaises (§1.5).

```text
EXACT TARGET REQUIRES CORRECTIONS
```

Ce verdict ne nie pas les théorèmes présents : ils sont valides. Il constate que la cible exacte, prise dans son sens fort (primitivité, production déterminante, admission indispensable), n'est pas portée par des énoncés qui échoueraient sans ces ingrédients.
