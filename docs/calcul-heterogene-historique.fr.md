# Calcul hétérogène et réemploi historique typé

La méthode est réalisée sur une seconde famille : un nombre produit un booléen, ce booléen détermine l'opération numérique suivante et son témoin, puis le résultat est réemployé par sa référence historique typée. La construction couvre toutes les histoires finies admissibles depuis tout nombre initial. Elle produit leurs ressources, leurs certifications et leur résultat terminal, et conserve ces déterminations sous continuation et composition.

Les réalisations acquises dans `FeedbackCoverage` sont conservées. Le nouveau développement étend la lecture des ressources à des valeurs dépendant de leur sorte : `Nat` pour `number`, `Bool` pour `truth`.

## Règles et périmètre

[TypedResources.lean](../RelationalFoundations/TypedResources.lean) définit une référence `Ref context kind` qui désigne une ressource de cette sorte dans le contexte constitué. La lecture retourne `Value kind`. Les dépendances peuvent ainsi relier des ressources de sortes différentes, tout en conservant le type de chaque entrée.

| Producteur | Entrées typées | Résultat |
|---|---|---|
| `literal` | Un nombre primitif | Ce nombre, de sorte numérique |
| `test` | Référence numérique | Booléen indiquant si le nombre est zéro |
| `adjust` | Référence booléenne, puis référence numérique | Successeur du nombre si le booléen est vrai ; prédécesseur sinon |
| `reuse` | Référence d'une sorte donnée | Valeur de cette ressource, de la même sorte |

Ces producteurs sont implémentés dans `Operation.eval`. Le support commence vide, puis reçoit la ressource numérique initiale. Chaque ajout conserve son opérateur et ses références vers le support précédent. Cette dépendance structurelle vers des ressources déjà constituées justifie la fermeture et la terminaison de leur lecture.

[HeterogeneousFeedback.lean](../RelationalFoundations/HeterogeneousFeedback.lean) définit trois états : nombre prêt, nombre observé avec son booléen, nombre mis à jour. Les occurrences sont les témoins `Step.observe`, `Step.act` et `Step.reuse`. `LocalAdmission` impose respectivement le résultat du test, l'accord du choix avec le booléen et le résultat numérique attendu, puis l'accord du réemploi. `Admissible` applique ces conditions à toute l'histoire. Elles utilisent les données opérationnelles, avant l'existence d'une réalisation ou de ses certifications.

Les primitives sont le nombre initial, les types `Nat` et `Bool`, les quatre producteurs et ces règles. La famille est déterministe, avec les deux branches d'augmentation et de diminution. Le nombre zéro donne successivement un test vrai, une augmentation vers un, un réemploi de un, un test faux, une diminution vers zéro et son réemploi.

## Construction et preuves

`declaredContext` extrait les sortes des obligations depuis l'histoire. `expected` lit leurs valeurs attendues depuis ses témoins. `diagram` extrait les opérateurs et leur câblage historique ; `declaredDependencies` déclare séparément leurs entrées ordonnées. Cette description est disponible pour une histoire fournie, avant sa preuve d'admission.

L'exécuteur `advance` lit les références disponibles et construit ses nouveaux résultats et témoins. Au pas `act`, le choix inscrit dans le témoin provient de la lecture effective de la ressource booléenne. `build` répète cette production par récurrence sur l'histoire admissible. Sa preuve d'exactitude identifie la configuration entière au diagramme déclaré, y compris les témoins, les opérateurs et les références.

| Obligation fermée | Construction ou preuve |
|---|---|
| Origine produite et valide | `initial`, `initial_valid` |
| Sorties effectivement utilisées dans les pas | `advance`, `reaction`, `advance_history`, `advance_specified` |
| Couverture dans les deux sens | `coverage_iff`, `complete_coverage_iff` |
| Valeur attendue de toute référence typée | `diagram_certified`, `coordinate_certified` |
| Correspondance exacte des références, sorte par sorte | `coordinates`, avec les deux identités de retour de `ExactTransport` |
| Toutes les dépendances et leur ordre | `diagram_dependencies`, `coordinate_dependencies` |
| Certification locale de tous les opérateurs | `TypedResources.Support.read_correct` |
| Énumération exhaustive et sans répétition | `references_all`, `references_unique`, `references_length` |
| Garantie terminale indépendante | `complete.terminal`, `run_trajectory`, `admitted_target` |

`complete` produit ensemble l'exécution, les correspondances, les certifications, les dépendances et l'énumération finie. Les preuves de certification sont construites depuis les producteurs et les conditions locales ; leurs obligations sont traitées sur toutes les références. La taille est ensuite lue : `complete_size` donne une ressource initiale plus une ressource par occurrence. `admitted_supports_unbounded` démontre l'absence de borne finie commune à cette famille.

`resumeFrom` reçoit une réalisation existante et poursuit directement depuis son support. La reconstruction du préfixe intervient uniquement dans la preuve d'égalité, effacée à l'exécution. `resumeCompleteFrom` fournit toutes les certifications du résultat prolongé. `resumeResourcesFrom` fournit son extension effective : son transport préserve la sorte, est injectif et conserve valeurs, opérateurs, références et dépendances. Il conserve et reflète les relations entre anciennes ressources. `resumeFrom_certified_old` conserve leurs certifications. `resume_compose` et `Execution.embed_compose` établissent la composition des configurations et des transports ; leur associativité est également prouvée.

Les histoires `History`, leurs compositions, les transports `ExactTransport` et les outils constructifs d'énumération de `DemandClosure` et `ResourceGraph` sont réutilisés. La couche spécialisée de références et de producteurs est nécessaire pour porter les valeurs dépendantes et le partage historique typé.

## Vérification et portée

[Tests/HeterogeneousFeedback.lean](../Tests/HeterogeneousFeedback.lean) fournit des histoires indépendantes de l'exécuteur. Les preuves vérifient le passage numérique vers booléen, les deux décisions issues des résultats, le réemploi par identité, la couverture des ressources et les transports. Les contrôles exécutables traitent l'origine, les deux branches, une continuation et quatre rejets : test incorrect, choix incorrect, résultat incorrect et réemploi incorrect. Le contrôleur `check` retourne la réalisation complète ou une preuve de rejet.

[TypedNumericInput.lean.fail](../Tests/ExpectedFailures/TypedNumericInput.lean.fail) vérifie séparément que le compilateur rejette une référence booléenne fournie à l'entrée numérique du test. Les contrôles exécutables complètent les preuves Lean quantifiées sur tout nombre initial et toute histoire admissible.

La lecture récursive recalcule les valeurs depuis les opérateurs conservés, sans cache partagé ; `TypedResourceOrder.inputs_precede` prouve que chaque entrée de ce support typé précède son consommateur. Les résultats portent sur la réalisation, la fermeture, la couverture et la conservation. Une politique de cache, une minimalité ou une borne de temps demandent leurs propres preuves. L'extension à d'autres sortes ou règles demande de fermer leurs producteurs et leurs obligations. La classe maximale et les stratégies d'oubli constituent des chantiers distincts.

La commande complète est `pwsh -NoProfile -File scripts/verify-v4.ps1 -SkipComparison -SkipReference`. Les reçus effectifs sont conservés dans [verification-result.json](verification-result.json) et [le rapport de migration](../Migration/verification-result.json). Les comparaisons avec le dépôt historique et ses empreintes sont explicitement omises pour respecter la vérification autonome du dossier isolé.

La vérification du 2 octobre 2026 a réussi : 53 fichiers de fondations et de tests, 4 569 déclarations auditées sans dépendance à des axiomes, 174 sources migrées et 806 symboles publics contrôlés. Les 25 rejets attendus, la stratification des 154 modules de production et les quatre frontières d'import passent.

La vérification actuelle et les preuves complémentaires sont décrites dans la [validation V4](audit-corrections-v4.fr.md) et le [bilan des corrections](audit-corrections-v3.fr.md). Les reçus datés ci-dessus restent des références historiques conservées.
