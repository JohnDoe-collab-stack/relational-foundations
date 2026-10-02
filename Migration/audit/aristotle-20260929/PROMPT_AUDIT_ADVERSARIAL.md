# Aristotle — réaudit adversarial de la correction `0291998`

## 1. Mission et révision immuable

Audite indépendamment le projet, la cible scientifique intégrale ci-dessous et les corrections intervenues depuis l'audit de `1ca8e89…`. Détermine ce que chaque correction établit réellement, ce qu'elle ne fait que déplacer et ce qui reste ouvert. Ne cherche ni un verdict positif par complaisance ni une réfutation obtenue en changeant le cadre. Aucun résultat de l'auteur n'est une certification indépendante.

**Un seul prompt fait autorité pour cette soumission : ce document, au chemin `audit/aristotle-20260929/PROMPT_AUDIT_ADVERSARIAL.md` sur la branche de correction.** Il remplace à ce même chemin l'ancienne version de préparation. Les versions conservées dans l'historique Git concernent d'autres cibles ; ne les exécute pas comme des prompts concurrents.

**Ne modifie pas le checkout cible.** Utilise une copie propre au SHA scientifique, des copies jetables pour les mutations et un dossier de résultats extérieur. Aucun commit, push ou merge n'est demandé à l'auditeur. Les noms, commentaires, certificats et rapports ne remplacent pas l'examen des termes.

```text
repository: https://github.com/JohnDoe-collab-stack/relational-perimeter.git
branch: chatgpt/aristotle-correction-20260929
scientific_target_commit: 02919988b97d959253b9104ec20372f39ca2f69d
scientific_target_tree: 55cadef8a0bf1c2a42606d83076ea844a62745c3
immediate_parent: 13eed60eac867cacfc4d4a0fddca33334ea882ed
parent_of_immediate_parent: 1ca8e89ed02eacc71eb70efa1ccab84985fb8ace
previous_independent_audit_target: 1ca8e89ed02eacc71eb70efa1ccab84985fb8ace
previous_independent_audit_parent: ded0e8ef4d343c091b66c80010c5a6827a589319
original_protocol_target_for_comparison_only: 5617ab4b09e5c0c044645737acd62973457b9a59
main_observed_at_preparation: 8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685
merge_base_target_with_that_main: 8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685
required_toolchain: leanprover/lean4:v4.33.1
observed_lean_commit: 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
observed_lake_version: 5.0.0-src+819816b
```

La branche contient un commit de préparation postérieur à la cible scientifique. **Audite `0291998…`, pas le HEAD mobile.** Le SHA cible contient encore l'ancienne copie historique du prompt : ne la substitue pas au présent document. Extrais les pièces du commit de livraison avant de te placer sur la cible, et conserve séparément les deux identités.

Clone toi-même le dépôt. Une divergence de cible, de parent ou d'arbre bloque l'identification : ne choisis pas une autre version. Si `main` a avancé, relève sa valeur nouvelle sans déplacer la cible. Enregistre aussi le SHA du commit de livraison dont tu extrais ce prompt et les pièces.

```bash
set -euo pipefail
TARGET=02919988b97d959253b9104ec20372f39ca2f69d
TREE=55cadef8a0bf1c2a42606d83076ea844a62745c3
PARENT=13eed60eac867cacfc4d4a0fddca33334ea882ed
PREVIOUS=1ca8e89ed02eacc71eb70efa1ccab84985fb8ace
MAIN_REF=8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685
BRANCH=chatgpt/aristotle-correction-20260929
WORKSPACE="$(mktemp -d)"
git clone https://github.com/JohnDoe-collab-stack/relational-perimeter.git "$WORKSPACE/target"
cd "$WORKSPACE/target"
git fetch origin "$BRANCH"
DELIVERY_HEAD="$(git rev-parse FETCH_HEAD)"
git merge-base --is-ancestor "$TARGET" "$DELIVERY_HEAD"
mkdir -p "$WORKSPACE/preparation" "$WORKSPACE/audit/$TARGET"
git archive "$DELIVERY_HEAD" audit/aristotle-20260929 |
  tar -x -C "$WORKSPACE/preparation"
printf '%s\n' "$DELIVERY_HEAD" > "$WORKSPACE/audit/$TARGET/delivery-head.txt"
git checkout --detach "$TARGET"
test "$(git rev-parse HEAD)" = "$TARGET"
test "$(git rev-parse HEAD^)" = "$PARENT"
test "$(git rev-parse HEAD^{tree})" = "$TREE"
test "$(git rev-parse "$PARENT^")" = "$PREVIOUS"
test "$(git merge-base "$TARGET" "$MAIN_REF")" = "$MAIN_REF"
test -z "$(git status --porcelain)"
git ls-remote origin refs/heads/main "refs/heads/$BRANCH"
git diff --stat "$PREVIOUS" "$TARGET"
```

Vérifie les empreintes annoncées dans `preparation.json` sur les pièces extraites. Décompresse `correction-0291998/Correction_Aristotle_0291998.zip` uniquement dans un dossier extérieur au checkout. Son compte rendu décrit l'état **antérieur à la publication** ; les mentions « aucun push » et `published: false` qui s'y trouvent sont historiques. Ne modifie pas ces pièces pour leur faire dire autre chose.

Inventorie les fichiers suivis, leurs SHA-256, les imports et le statut Git avant/après. Ne réemploie aucun `.olean` provenant d'une autre révision. La copie de référence et chaque mutation scientifique finale doivent repartir de `lake clean` ; vérifie les artefacts réellement supprimés.

**Environnement.** Indique les capacités réelles : checkout complet, shell, Git, Lean, Lake et PowerShell. Si un outil ou le compilateur épinglé n'est pas disponible, classe les commandes concernées `NOT RUN` ; ne remplace ni Lean ni les définitions et n'ajoute pas Mathlib. Une interface de preuve seule ne vaut pas audit du dépôt. Les contrôles de l'auteur ne remplacent jamais tes propres commandes.

## 2. Cible scientifique inchangée

La cible est le texte suivant, intégralement. N'en change ni les objets, ni les quantificateurs, ni la direction des dépendances pour faciliter l'audit.

> **Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes.**
>
> **Cette exécution ne produit pas d'explosion exponentielle de la largeur opérationnelle : bien que le déploiement extensif des profils constitués ait une largeur 2^n, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes.**
>
> **Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c'est-à-dire si son application `carry` est injective.**
>
> **L'explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l'effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même.**

La portée fixée dans les documents est la **pleine largeur exactement `2^n`**, pas l'ensemble des fonctions asymptotiquement exponentielles. Pour l'instance publique positive, `n = input + 1` ; pour la classe générale, `n = stageCount`. Vérifie cette différence de paramétrage et ne remplace pas un quantificateur général par quelques exemples.

Le théorème d'équivalence doit valoir pour chaque membre de la classe binaire et chaque régime surjectif concerné. L'exécution endogène particulière de largeur un est instanciée sur la famille SAT engendrée du dépôt ; n'attribue pas cette exécution à tous les membres abstraits de la classe. Aucun résultat `P = NP`, `P ≠ NP`, aucune borne universelle de temps/mémoire ou propriété de tout arbre adaptatif ne doit être inféré.

Sépare dans ton analyse : (i) la validité des théorèmes Lean, (ii) leur adéquation à chaque phrase française, (iii) les exigences adversariales fortes A–J. Une mutation survivante peut révéler une redondance ou un défaut du contrat sans réfuter un théorème mathématique existant. Inversement, les bons nombres ne suffisent pas à établir la production constitutive revendiquée. Cette séparation analytique ne dispense d'aucun contrôle obligatoire et ne permet pas un verdict global positif si un contrôle reste non vérifié.

## 3. Lecture préalable et méthode à respecter

Lis intégralement les documents avant de conclure, puis les modules concernés et leurs dépendances nécessaires. Respecte l'ordre interne, les distinctions, les hypothèses et les limites de chaque fichier. Tiens un relevé des fichiers et plages lus ; ne déclare pas une lecture exhaustive à partir d'extraits.

Entrées documentaires au commit cible :

1. `README.md` et `docs/relations-primitives-constitution-perimetre.fr.md` ;
2. `docs/decomposition-operationnelle-endogene.fr.md` ;
3. `docs/conclusion-largeur-exponentielle-conservation-identites.fr.md` ;
4. `docs/positionnement-et-portee.fr.md` ;
5. les trois versions anglaises correspondantes, intégralement : `primitive-relations-and-perimeter-constitution.en.md`, `endogenous-operational-decomposition.en.md`, `positioning-and-scope.en.md` ; puis les figures si elles portent une assertion nécessaire ;
6. le rapport indépendant antérieur et le compte rendu de correction joints, intégralement, après ces documents de cadre. Le premier audit avait signalé une lecture documentaire partielle : ne reconduis pas cette limite en annonçant une lecture complète.

L'ordre constitutif à vérifier est :

```text
relations typées primitives de formation, provenance, source et cible
→ témoins positifs
→ occurrences de rôle constituées
→ histoires dépendantes de ces occurrences
→ profils et frontière source dérivés de cette constitution
→ transformation exécutée sur ces mêmes profils
→ codétermination produite par élimination de la chaîne exécutée
→ régime représentant exactement son image, avec admission justifiée
→ lectures de largeur et équivalence exponentielle
```

La lecture extensive ne constitue pas ses propres objets. Une sélection de positions n'est pas une occurrence réalisée par simple changement de nom. L'action totale n'est pas sa preuve de préservation ; un transport dirigé n'est pas une équivalence ; absorption n'est ni identification ni impossibilité ; image exacte et admission ne sont pas identiques ; provenance causale et nouveauté informationnelle ne sont pas synonymes.

### Entrées de code : réutilisation à vérifier, non conclusion imposée

La production endogène possède déjà des constructions dans le dépôt. Ne la présume pas absente parce que le nouveau pont n'en redémontre pas tout le contenu. Examine leurs termes et leur réutilisation effective, sans prendre leur existence déclarée comme un verdict.

Sous `RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/` :

- `ConstitutiveInterface.lean`, `ConstitutiveFullStep.lean`, `ConstitutiveFeedback.lean` : génération, découverte exécutée, transformation, échec, état transmis et feedback ;
- `ExecutedOperationalReduction.lean` et `ExecutedOperationalReductionHistory.lean` : ouverture, statut, absorption autorisée, préservation et lectures transitoires ;
- `InstrumentedExecutionRealization.lean`, `CausalOperationalExecution.lean`, `PrefixLocalOperationalProduction.lean` : source faisant autorité, production locale et suites dépendantes ;
- `RelationalConstitutiveRoles.lean`, `RoleIndexedProfiles.lean`, `RoleIndexedProgram.lean`, `ExecutedRoleIndexedReduction.lean` : constitution, réalisation, action et traces ;
- `RoleProfileSemantics.lean` et `ExecutedCausalNormalization.lean` : action sur données arbitraires, critères, autorisation et image ;
- **`ExecutedFeedbackBridge.lean`** : `StepFacts`, `stepFacts`, `producedRoleAction_is_discovered`, `Along`, `along`, `widthTrace_existing`, `widthTrace_le_two`, `public_along` ;
- **`ConstitutiveExtensiveSeparation.lean`** : `EndogenousDecompositionAndWidth`, `endogenousDecompositionAndWidth`, `binaryClass_fullWidthExactlyInjective`, `extensiveMultiplicity_doesNotForceFullOperationalWidth`.

Autres points indispensables : `SemanticImage.lean`, `RelationalProfileConstitution.lean`, `RelationalRoleExtensiveFamily.lean`, `FiniteExtensiveAddressing.lean`, la façade `RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean`, la racine `RelationalPerimeter.lean` et les tests clients.

Le point d'entrée annoncé du nouveau raccord est :

```lean
RelationalPerimeter.Computation.EndogenousOperationalDecomposition.endogenous_production_and_width_separation
```

Déplie intégralement son type `EndogenousDecompositionAndWidth`, chaque champ et chaque prédicat référencé. Vérifie que sa preuve assemble des résultats réellement raccordés aux mêmes données, pas des certificats indépendants simplement juxtaposés. Vérifie notamment que `Along` porte sur les têtes de l'exécution qui définit le porteur public, et que l'action du rôle est l'action découverte sur toute continuation.

Les tests à examiner incluent `Tests/EndogenousWidthBridgeRegression.lean`, `Tests/ConstitutiveObjectiveRegression.lean`, `Tests/RelationalExtensiveIffRegression.lean`, `Tests/SemanticImageRegression.lean` et les régressions de stabilité opérationnelle. Leur succès ne remplace pas l'audit des définitions.

### Réaudit spécifique du correctif — compléments aux contrôles A–J

Ces vérifications s'ajoutent aux contrôles de la section 4 ; elles n'en retirent aucune exigence. Compare le code à `1ca8e89…` et à son parent immédiat `13eed60…`. Pour chaque réserve antérieure, rends un état explicite : corrigée avec preuve, déplacée, toujours ouverte, ou non testée.

**Origine, A/B.** Lis `SAT/GeneratedStructuralContext.lean`, `GeneratedChildFormation`, `RoleFormationAgreement` et les projections de `RelationalConstitutiveRoleStage`. Examine le rapport entre la relation de formation, le constructeur `child`, ses témoins de génération et les égalités de réalisation. Détermine si la nouvelle formation apporte le contenu constitutif revendiqué ou une présentation équivalente d'un accord déjà dérivable. Vérifie ce qui est effectivement disponible avant la découverte, et ce qui reste indexé par un run déjà complet. Ne considère ni un constructeur inductif ni le mot « primitive » comme une preuve d'indispensabilité. N'efface pas les distinctions fondatrices entre relations données, générations, réalisations et lectures.

**Statuts et image, D/G/I.** Lis intégralement `RolewiseOperationalStatus.lean` : `Status`, `target`, `act`, `act_preserves`, `History.policy`, `History.selected`, `History.transform`, `History.fibres`, `History.width`, `returnedTransport`, `executed` et `executed_action_exact`. Vérifie la formule `2^pendingCount`, les cas mixtes 4/2/1, l'action sur toute continuation et leur raccord matériel au régime public. `none` signifie qu'aucun transport n'est fourni à ce statut, pas qu'aucun transport ne peut exister. Les politiques mixtes comparent des statuts sur une même histoire ; ce ne sont pas de nouvelles exécutions SAT revendiquées.

Examine les corps de `producedTargetFrontier`, `authorizedOperationalRegime`, `regimeWidth_eq_statusWidth` et `width_exact`. Vérifie si la composition des statuts détermine réellement cette frontière ou ne fait que fournir un décompte compatible. Distingue les occurrences sélectionnées des cibles-continuations : la réalisation de l'une vers l'autre doit être exacte et préserver le critère, pas seulement la cardinalité. Ne requiers pas silencieusement `DecidableEq` sur les continuations fonctionnelles. Teste un regroupement constant à la fois dans le cas convergent et dans un cas en attente à cibles distinctes.

**Admission, E/F.** Déplie `SemanticImage.Admission`, `AdmittedImageValue` et leur consommateur, puis **séparément** le type concret `AuthorizedProducedTargetObligation`, ses champs et les consommateurs publics. Vérifie la disparition du paramètre d'autorisation fantôme sans inférer que toute redondance a disparu. Un contre-modèle abstrait n'interdit pas une reconstruction dans l'instance riche ; une survie concrète ne réfute pas automatiquement le contre-modèle abstrait. Éprouve chacun dans son domaine exact. Vérifie que l'admission énonce encore invariant, accord canonique, préservation sur toute charge et réflexion, sans être remplacée par une preuve de largeur.

**Ordre exécuté, C/D.** Lis intégralement `OperationalProductionProgram`, `evaluate`, `withCausalOperationalHead`, les producteurs spécialisés, `executeWithTrace_program_exact`, `operationalProductionTimeline_exact` et leur utilisation publique. La trace doit provenir de l'interprétation des opérations observées, non d'un journal indépendant accepté sans preuve. Examine aussi `done`, `mapResult`, les continuations et les arguments : du calcul peut-il s'y effectuer sans événement correspondant ? L'équation d'un évaluateur spécialisé avec l'interprète suffit-elle exactement à la prétention déclarée ? N'étends pas une propriété des frontières de trois primitives à tout l'ordre d'évaluation Lean ou au temps machine.

Rejoue distinctement l'ancienne M04 de longueur un et une anticipation réelle comportant une étape ultérieure, comme `ProductionTimelineRegression.delayedTwo`. Vérifie l'égalité de valeur et la différence de trace. Une impossibilité de terminaison n'est pas cette différence. L'ordre des trois primitives ne garantit pas, à lui seul, que la sortie canonique interne de M08 a été calculée autrement que par prescription ; vérifie cette limite au lieu de déclarer D fermé par C.

**Énoncé terminal, H/I.** Déplie les nouveaux champs `primitiveOperationOrder`, `admittedImage`, `widthFromProducedStatuses` et `statusActionIsCarriedAction` de `EndogenousDecompositionAndWidth`. Vérifie la provenance commune de leurs objets et les éventuels changements de dépendances dus à la factorisation des types de certificats. Examine `executedAdmittedRegime_notFullWidth` : nommer le régime et ajouter une conjonction ne suffit pas si le lien de production/admission revendiqué n'est pas porté par la construction. Le lemme cardinal faible et le théorème binaire général restent distincts du phénomène exécuté.

**Nouvelles régressions, J.** Lis `Tests/AristotleCorrectionRegression.lean`, `Tests/DeepPreservationRegression.lean` et `Tests/ProductionTimelineRegression.lean`, en plus des anciens clients. Confronte les contre-modèles à l'instance, aux hypothèses retirées et aux mutations du même nom ; ne confonds pas régression compilée, erreur d'un corps particulier et impossibilité de satisfaire un contrat inchangé.

Exécute aussi, après la compilation propre :

```bash
python3 scripts/test-expected-failure-gates.py --output "$WORKSPACE/audit/$TARGET/gate-self-tests"
```

Vérifie que les deux contrôleurs utilisent l'inventaire commun `scripts/expected-failures.tsv`, appellent chacune des 19 fixtures exactement une fois et détectent absences, doublons, omissions, diagnostic incorrect, fixture devenue compilable et interruption. Compare les quatorze attentes historiques et les cinq ajouts. Les autotests des contrôleurs partagent explicitement les bibliothèques compilées ; ils ne se substituent pas aux compilations propres des mutations scientifiques. Ne prends pas un fichier `.olean` manquant ou un échec d'import pour le rejet sémantique attendu d'une fixture.

## 4. Contrôles obligatoires A–J

### A. Primitivité de la constitution relationnelle

Vérifie la constitution effective du porteur et la fonction de chacun des quatre accords dans les constructions qui l'utilisent. Stocker un témoin à côté de données déjà suffisantes ne suffit pas. Localise le producteur, le consommateur, l'index dépendant et les voies de récupération de chaque accord.

Mutations obligatoires : remplacer les quatre familles par `Unit` ; retirer les témoins un par un ; conserver les témoins mais les ignorer ; remplacer les occurrences constituées par le porteur brut. Poursuis les essais jusque dans leurs conséquences publiques, sans changer silencieusement le sens des conclusions.

Distingue deux opérations : effacer une copie aval en récupérant le même accord depuis un rôle riche, et effacer aussi l'origine constitutive de cet accord. Consigne les deux. La survie de la première n'est pas une preuve d'absence de toute relation ; elle reste un problème pour l'exigence forte d'indispensabilité de cette interface. Ne transforme pas cette distinction en exemption de test. Si les mêmes conclusions survivent à la mutation obligatoire, ne marque pas A `VERIFIED` sans expliquer exactement ce qui a été supprimé et ce qui reste.

### B. Un porteur public faisant autorité

Vérifie définitionnellement que le porteur de l'histoire exécutée, celui du régime et celui de l'application publique du théorème binaire sont le même. Ajoute le domaine de `imageDescription` et celui de l'action sémantique à cette vérification.

Une égalité propositionnelle, `HEq`, un cast, un adaptateur ou une copie reconstruite ne remplit pas ce contrôle. Cela n'interdit pas les transports internes de réalisation prévus par la méthode : vérifie leur rôle sans les confondre avec un second porteur scientifique.

### C. Production endogène, locale au préfixe

Lis le corps de `executeCausalOperationalHead`, celui de l'exécuteur récursif et le raccord à la découverte existante. Vérifie que la tête est produite depuis la source, que la suite dépend de son état et de son contexte produits, et que la provenance/graine utilisées ensuite viennent effectivement de cette production.

Contrôle les preuves existantes `nextDiscoveryConsumesProducedProvenance`, `nextDiscoveryConsumesRetainedSearchSeed`, l'exclusion des étapes après échec et la non-factorisation sur le domaine comparateur défini. Ne confonds pas états comparateurs contrefactuels et états émis par l'exécution de référence.

Vérifie le rôle exact des équations de tête, du théorème d'indépendance de l'horizon et de `ExecutedFeedback.Along`. Une égalité de résultat ne prouve pas à elle seule un ordre d'évaluation ; distingue inspection de la définition, dépendance typée, propriété extensionnelle et propriété du calcul exécuté.

Tente une mutation cohérente calculant/stockant la tête à partir d'une histoire future achevée, puis une suite repartant d'un état racine ou d'un contexte indépendant. Le rejet demandé pour la première doit provenir de la dépendance de production, pas seulement de la confidentialité d'un constructeur ou de l'unicité du résultat. Si une variante extensionnellement équivalente passe, indique exactement quelle prétention forte elle invalide ; ne prétends pas qu'elle réfute l'existence de l'exécution de référence.

### D. Cibles produites et action non prescrite

Vérifie que les cibles sont calculées par élimination des décisions exécutées et application de l'action ou conservation de la continuation. Une cible fournie avec une égalité, ou une cible prescrite dont la trace est reconstruite après coup, ne remplit pas la condition forte.

Tente les deux mutations. Tente aussi de remplacer l'action par une sortie canonique constante. Répare ses égalités sur l'échantillon canonique si elles sont réparables, puis conserve le contrat sur les données arbitraires. Un succès seulement sur les données canoniques n'établit pas l'action totale annoncée.

Distingue l'accord `canonicalPayload_accepted` et la convergence des sorties canoniques de la préservation sur toute continuation. Ne déduis pas que toutes les données arbitraires produisent la même valeur.

### E. Préservation et distinction dans l'admission

Vérifie que la préservation du critère pour les continuations arbitraires et la persistance des occurrences distinctes sont effectivement utilisées par la justification du regroupement. Retire chaque garantie séparément ; poursuis au-delà d'un champ ou d'un test nommé.

Inspecte `RoleSemantics.profilePreserves`, `sourcesRemainDistinct`, `profileConstitutionFromChain`, `SemanticImage.certify`, `Specification`, `use`, `viable_iff`, puis leurs instanciations. Vérifie l'acceptation exacte considérée : le critère des profils est point par point sur les continuations locales. Ne l'assimile pas sans preuve à une solution globale d'un arbre adaptatif ou à une affectation commune réalisant toutes les histoires.

L'action doit rester définie sans preuve préalable d'acceptation. La distinction doit justifier « sans identification » ; ne transforme pas artificiellement cette distinction en précondition de toute action brute. Vérifie aussi la viabilité positive de l'alternative absorbée et de chaque profil selon le critère annoncé.

Si la preuve retirée est reconstructible depuis la relation conservée, fournis cette reconstruction et trace sa dépendance. Une copie dispensable et une garantie dispensable ne sont pas la même conclusion. La mutation n'est néanmoins pas rejetée : son statut doit rester visible dans la table forte A–J.

### F. Autorisation et obligation sémantiquement utilisable

Examine le passage de la chaîne causale à `ExecutedOperationalGroupingAuthorization.imageSpecification`, puis à `AuthorizedProducedTargetObligation`, à `transformPayload` et aux consommateurs publics. Détermine ce qui relève de l'appartenance à l'image, de son admission et du portage d'une garantie réellement consommée.

Tente : retrait de l'autorisation ; remplacement de la garantie portée par `True` ; reconstruction de cette garantie depuis une réduction riche restée accessible ; régime `Unit` indépendant ; `carry` constant vers un ancrage. Répare les premières erreurs de champs/projections/noms, puis conserve les obligations sémantiques et d'exactitude publiques.

Ce n'est pas l'impossibilité de définir un singleton abstrait qu'il faut prouver. Il faut éprouver sa capacité à remplacer le régime exécuté exact et autorisé pour ces profils. Ne donne pas un faux rejet en gardant un appel syntaxique à un champ supprimé. Ne donne pas un faux succès en redéfinissant la spécification pour qu'elle n'affirme plus la même chose.

### G. Image exacte et fibres

Vérifie les deux directions de :

```text
carry p = carry q ↔ normalization.target p = normalization.target q
```

et leur raccord aux deux traces de `OperationallyCoDetermined`. Le régime ne doit ni fusionner des cibles produites distinctes, ni séparer des cibles produites égales. Vérifie la complétude et l'absence de doublons de sa frontière, la surjectivité de `carry`, la conservation de la source de chaque trace et de la cible effectivement produite.

La largeur un doit se lire après la convergence et l'exactitude de l'image. Une énumération singleton est admissible si sa complétude sur l'image réelle est démontrée ; elle ne constitue pas à elle seule une preuve de convergence. Le porteur ambiant des continuations ne doit pas avoir été rendu singleton pour obtenir le résultat.

### H. Équivalence exponentielle et généralité

Vérifie le véritable `iff` pour toute famille binaire formalisée, tout problème et tout régime surjectif concerné :

```text
regime.frontier.length = 2 ^ family.stageCount problem
  ↔ Function.Injective regime.carry
```

L'adressage séparé doit être construit à travers les obligations depuis l'injectivité, non ajouté indépendamment. Vérifie le régime identitaire, l'existence du membre binaire indépendant de l'exemple SAT, le caractère non borné prévu par la classe et, séparément, la formule à arités variables comme produit des arités réalisées.

N'élargis pas « exactement `2^n` » à « toute croissance exponentielle ». Inversement, ne déclare pas erronée la conclusion fixée parce qu'elle ne prétend pas cette généralisation. Le lemme fini abstrait est un composant ; il ne prouve pas à lui seul la cible complète.

### I. Mêmes profils, statuts opérationnels différents

Sur le même porteur, vérifie : profils distincts explicites ; continuations canoniques acceptées ; traces exécutées vers une cible commune ; portage commun sans égalité des sources ; régime conservatif distinct de pleine largeur.

Relie les résultats du nouveau théorème commun à l'exécution et à la normalisation qui font autorité. Vérifie que `extensiveMultiplicity_doesNotForceFullOperationalWidth` utilise ce régime exécuté, pas un singleton fabriqué indépendamment.

Sépare la largeur extensive, la frontière en attente, la largeur du régime final et les lectures locales transitoires. Inspecte `widthTrace`, `widthTrace_existing`, la borne deux et les objets dont les nombres sont lus. Vérifie qu'aucune énumération exhaustive des `2^n` profils n'est implicitement présentée comme une opération de largeur constante. Ne convertis pas les bornes de ces lectures en bornes globales de temps ou de mémoire.

### J. Compilation, constructivité et fermeture publique

Depuis le checkout propre au SHA cible, exécute réellement :

```bash
lean --version
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
git status --porcelain
git rev-parse HEAD
```

Enregistre stdout, stderr et code de sortie séparément pour chaque commande. Un contrôle impossible dans ton environnement est `NOT RUN`, pas `PASS`. Les résultats annoncés par l'auteur ne remplacent pas tes propres exécutions.

Vérifie que tous les modules de production sont atteignables depuis `import RelationalPerimeter` et que la stratification terminale A5 → A6 → A7 → A8 → A9 est contrôlée dans les scripts Bash et PowerShell. Compare les vérificateurs, tests d'échec, configuration Lake et manifeste aux révisions parentes : une règle affaiblie doit être identifiée. Un ajout d'entrée au manifeste n'est pas en lui-même un assouplissement.

Vérifie exactement un bloc final `AXIOM_AUDIT` dans chaque fichier Lean pertinent. Recherche dans les sources effectives `axiom`, `sorry`, `admit`, `noncomputable`, `Classical`, `propext`, `Quot.sound`, `native_decide`, `unsafe`, `implemented_by` ; distingue code, commentaires, chaînes et fixtures d'échec. Contrôle les dépendances transitives des théorèmes, pas seulement l'absence lexicale des noms.

Inventorie aussi les auxiliaires générés : récursors, éliminateurs, théorèmes d'injectivité, équations et déclarations dérivées. **Ne confonds pas leurs dépendances avec une invocation dans les sources ou une dépendance d'un théorème central.** Pour `propext` et `Quot.sound`, indique chaque origine et si elle est atteignable transitivement depuis les résultats audités. Leur présence dans un auxiliaire généré inutilisé n'établit pas à elle seule que la démonstration source les utilise. Ne transforme pas l'exigence de distinguer les origines en interdiction supplémentaire de tout auxiliaire du compilateur.

Les `sorryAx` éventuellement émis après une erreur d'élaboration dans une copie mutée ne constituent jamais une preuve acceptée. Identifie le premier défaut, corrige la sonde lorsque c'est légitime et recompile ; n'utilise aucun résultat dépendant d'un trou.

## 5. Pièces, résultats antérieurs et mutations à reprendre

### 5.1 Pièces de la livraison — sources à vérifier, pas verdict imposé

Tous les chemins de cette section sont relatifs au dossier extrait `audit/aristotle-20260929/` du commit de livraison, pas au checkout scientifique.

- `correction-0291998/Correction_Aristotle_0291998.zip` : compte rendu de correction unique, `results.json`, patch du correctif, bundle Git incrémental, `frozen-evidence/`, `gate-selftests-complete/`, `mutations-final/<cas>/final.patch` et journaux, `final-probes/`, `probe-logs/`, script de reproduction. Les copies complètes et caches ne sont pas nécessaires : chaque variante est reconstruite depuis le SHA et son patch.
- `correction-0291998/results.json` et `manifest.json` : copies exactes des résultats structurés et du manifeste antérieurs à la publication. Vérifie leurs empreintes et leur accord avec l'archive.
- `correction-0291998/historique/RAPPORT_1ca8e89_ARISTOTLE.fr.md` et `results-1ca8e89.json` : rapport indépendant précédent et ses résultats structurés, sans modification. Son verdict était `EXACT TARGET REQUIRES CORRECTIONS`, pas une réfutation des théorèmes Lean. PowerShell n'y avait pas été exécuté et certaines lectures et mutations étaient incomplètes.
- Les dossiers préexistants `evidence/` et `historical-mutations-ded0e8e/` concernent respectivement l'ancienne cible `1ca8e89…` et le parent `ded0e8e…`. Ils ne sont pas des résultats sur `0291998…`.

L'auteur annonce sur la nouvelle cible : compilation propre de la racine et de l'ensemble, Bash et PowerShell réussis, 144 fichiers Lean, 19 fixtures, 16 autotests des contrôleurs, intégrité de 234 fichiers. La sonde des modules sélectionnés annonce 1 231 déclarations non auxiliaires selon son filtre, sans axiome ; ce filtre n'est pas une classification exhaustive de toutes les déclarations sources. L'inventaire plus large annonce 356 auxiliaires dépendants de `propext` et trois de `Quot.sound`. **Reproduis et contrôle ces nombres et leurs définitions ; ne les adopte pas comme conclusions.**

### 5.2 Campagne ciblée de l'auteur sur `0291998…`

Le compte rendu annonce **16 variantes, 9 survies, 7 échecs dans l'essai**. Les sept échecs ne sont pas par défaut sept impossibilités scientifiques. Vérifie les premiers diagnostics, répare les obstacles superficiels et rattache les contre-modèles aux contrats testés. Les erreurs en cascade et `sorryAx` après élaboration échouée ne sont jamais des preuves.

| Identifiant exact dans les pièces | Observation annoncée | Ce qu'il faut distinguer ou retester |
|---|---|---|
| `M01-four-derived-families-Unit` | SURVIVES | Quatre familles aval remplacées par `Unit` ; formation et étape riches conservées. |
| `M02-ignore-derived-evidence` | SURVIVES | Témoins ignorés ; formation reconstruite depuis l'occurrence. |
| `A-raw-realized-carrier` | SURVIVES | `stage.Occurrence` remplace l'enveloppe ; accords récupérés depuis l'étape. Ce n'est pas l'effacement de toute formation. |
| `M05-root-tail` | Échec observé | Suite à la racine au lieu de l'état produit ; vérifier les indices et réparations possibles. |
| `M06-root-context` | Échec observé | Contexte racine au lieu du contexte transmis. |
| `C-real-future-reordering` | Échec observé | Étape suivante avant la première décomposition ; vérifier une contradiction de trace, pas seulement un `change` échoué. |
| `M07-action-constant` | Échec observé | Action totale remplacée par une sortie canonique ; réparer les accords canoniques et éprouver les charges arbitraires. |
| `M08-prescribed-canonical-target` | SURVIVES | Sortie prescrite, égalité démontrée ; action totale inchangée. |
| `M09a-reconstruct-preservation` | SURVIVES | Garantie reconstruite depuis les licences, pas supprimée à son origine. |
| `M09b-reconstruct-separation` | SURVIVES | Distinction reconstruite depuis les mêmes licences. |
| `E-deep-formula-agreement` | Échec observé | Accord de formule remplacé par `True`, carte structurelle conservée ; vérifier le contre-modèle SAT et le périmètre de la suppression. |
| `M11-reconstruct-authorization` | SURVIVES | Autorisation ignorée, garanties reconstruites depuis la réduction. |
| `F-True-generic-guarantee` | Échec observé | Spécification abstraite remplacée par `True`, sans run riche pour la reconstruire. |
| `F-True-public-reconstructed` | SURVIVES | Garantie concrète remplacée par `True`, puis reconstruite depuis la normalisation. |
| `G-pending-constant-carry` | Échec observé | Fusion même sans transport ; confronter aux fibres et à la largeur en attente. |
| `M12-constant-executed-carry` | SURVIVES | Ancrage constant dans l'instance convergente ; traces transportées avec la convergence prouvée. |

Rejoue les variantes cohérentes sur la cible, avec tous les nouveaux clients. Ne requalifie pas une survie en rejet parce que l'auteur explique sa redondance. N'appelle pas non plus « garantie absente » une reconstruction dont les prémisses conservent précisément cette garantie. Le statut expérimental et sa portée scientifique doivent apparaître dans deux colonnes distinctes.

### 5.3 Couverture complète, au-delà de ces seize variantes

La campagne ciblée ne couvrait pas chaque demande A–J. Il faut notamment reprendre la M04 historique exacte de longueur un, les suppressions de témoins une par une et à leur origine, ainsi que le remplacement intégral par un régime `Unit` étranger. Pour H01/H02, reproduis les patches joints sur `ded0e8e…` puis leur adaptation sur la nouvelle cible ; indique les deux SHA. Lorsqu'un patch historique exact n'est pas livré, reconstruis une expérience sémantiquement équivalente et nomme-la comme telle : ne prétends pas avoir rejoué octet pour octet un fichier absent.

Les trois manques du précédent audit — porteur brut, retrait profond de la préservation, garantie remplacée par `True` — ont maintenant des essais fournis, mais leur **profondeur réelle** reste à contrôler. Une enveloppe retirée avec toutes ses dépendances reconstructibles n'est pas toute la chaîne retirée. Les modèles génériques sans garantie ne doivent pas remplacer l'examen des consommateurs publics concrets.

Recompile les sondes historiques `H_I_probes.lean` : famille aux relations `Unit`, non-nécessité faible prouvée sans exécution, fibres d'un régime étranger, accords reconstructibles et cibles canoniques indépendantes du profil. Confronte-les ensuite à l'énoncé public renforcé ; conserve exactement leurs domaines et leurs quantificateurs.

Tout essai obligatoire absent reçoit `NOT RUN`, avec sa raison. Ni une lecture partielle ni un outil indisponible ne permettent de produire un bilan exhaustif positif. Le but est de départager ce que la correction résout réellement, ce qui n'était qu'une redondance de représentation et ce qui reste insuffisamment formalisé.

## 6. Discipline des mutations

Une copie jetable par variante. Enregistre le SHA de départ et le patch complet. Vérifie un témoin non modifié dans le même dispositif. Conserve l'historique des réparations de la sonde et distingue la première erreur superficielle de la première erreur substantielle.

Pour chaque variante finale, lance une compilation propre de la racine, la compilation complète et les deux vérificateurs, puis le contrôle de diff. Si un échec amont empêche un test aval, indique cette causalité ; ne le compte pas comme un second rejet indépendant. Si un processus expire, classe `INCONCLUSIVE`, pas `REJECTED`.

Classification obligatoire des observations :

- `SURVIVES` : les mêmes contrats publics et leurs clients passent ; préciser la garantie conservée ou reconstruite ;
- `SUBSTANTIVE REJECTION` : une obligation constitutive, sémantique ou d'exactitude inchangée ne peut plus être typée/prouvée dans la variante testée ; donner l'erreur et sa raison ;
- `SUPERFICIAL FAILURE` : syntaxe, nom, champ, confidentialité, test non adapté, linter ; réparer et continuer ;
- `INCONCLUSIVE` ou `NOT RUN` : limites d'exécution, environnement ou analyse encore insuffisante.

Un échec d'un corps de preuve particulier ne démontre pas l'impossibilité de toute preuve équivalente. Cherche la réparation cohérente pertinente avant de conclure à la nécessité d'une donnée. Inversement, un succès obtenu en affaiblissant l'énoncé, en supprimant un client substantiel ou en introduisant des hypothèses n'est pas une survie de la cible.

Le protocole n'exige pas d'interdire toute réécriture extensionnellement équivalente par un artifice d'opacité. Lorsque l'exigence forte de rejet dépasse les propriétés effectivement formalisées, explique précisément cet écart au lieu de modifier l'objectif ou de masquer le succès de la mutation.

## 7. Rapport unique attendu

Produis un document autonome `audit/<TARGET>/RAPPORT_ADVERSARIAL_ARISTOTLE.fr.md` et les pièces techniques nécessaires : manifestes, sources des sondes, patches, journaux et résultats structurés. Le rapport doit contenir, dans cet ordre :

1. identité des révisions, environnement, commandes et intégrité avant/après ;
2. lecture des quatre paragraphes sans reformulation réductrice, avec leurs hypothèses et quantificateurs exacts ;
3. carte des neuf niveaux constitutifs : fichier, déclaration, producteur, consommateur, garantie et rôle réel ;
4. analyse détaillée du nouveau raccord et des preuves endogènes antérieures qu'il consomme ;
5. verdict phrase par phrase et champ par champ : `VERIFIED`, `QUALIFIED` ou `FALSE`, avec lignes et preuves ;
6. résultats A–J et table complète des mutations, y compris celles qui survivent ;
7. inventaire des axiomes, séparant sources, dépendances transitives et auxiliaires générés ;
8. divergences entre documentation et Lean, chacune accompagnée de l'énoncé réellement démontré ;
9. périmètre exact : instance exécutée, classe générale, profils, critère local, largeurs et limites ;
10. conclusion directe sur l'objectif scientifique puis verdict global du protocole.

Table minimale pour chaque mutation : identifiant, clause, SHA de base, fichiers modifiés, patch, contrat inchangé, commandes/codes de sortie, premier défaut substantiel, origine du rejet, données encore récupérables, effet précis sur la phrase visée. N'invente aucune preuve de nécessité à partir du seul nom d'une déclaration.

Le verdict global final est exactement l'un de :

```text
EXACT TARGET ESTABLISHED
EXACT TARGET REQUIRES CORRECTIONS
EXACT TARGET NOT ESTABLISHED
```

`EXACT TARGET ESTABLISHED` requiert les quatre paragraphes et toutes les dépendances obligatoires `VERIFIED`, avec les mutations fortes rejetées pour des raisons substantielles. Un paragraphe `FALSE` impose `EXACT TARGET NOT ESTABLISHED`. Un paragraphe ou contrôle `QUALIFIED`, un cas obligatoire non testé ou une mutation obligatoire survivante interdit le verdict positif et permet au mieux `EXACT TARGET REQUIRES CORRECTIONS`.

**N'assimile pas le verdict global de ce protocole fort à la négation de tous les théorèmes présents.** Termine par une réponse lisible : ce qui est démontré, ce qui ne l'est pas, la dépendance exacte restant en cause, et les preuves ou contre-exemples qui justifient ces distinctions. N'exécute aucune réparation du dépôt cible pendant cet audit.
