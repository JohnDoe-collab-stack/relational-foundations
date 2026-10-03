# Portée vérifiée et preuves complémentaires

La construction commune, ses deux instances fermées et l’oubli relatif aux continuations natives sont conservés. Cette révision précise leurs quantificateurs, ajoute les preuves de parcours finis et ferme un invariant effectif sur toute la chaîne calculée. La [validation V3](validation-v3.fr.md) identifie les sources et les sorties des contrôles sur Windows et Linux.

## Trois obligations distinctes de fermeture

1. **Couverture des références.** Le support fini possède une énumération exhaustive et une correspondance exacte avec les demandes déclarées. Chaque entrée ordonnée d’un opérateur désigne une ressource de ce support.
2. **Certification des lectures.** `Certified` établit que l’évaluation de chaque opérateur avec la lecture fournie redonne cette lecture. Le constructeur reconstruit cette certification depuis les lois initiales, locales et de transport.
3. **Production des valeurs.** Les procédures de chaque instance construisent effectivement les lectures. Dans les deux familles existantes, `Support.read` procède structurellement depuis les opérateurs conservés. Leur égalité avec les cadres génériques est démontrée sur les cadres entiers, références et dépendances comprises.

Ces obligations gardent leurs contenus propres. [CyclicSupport.lean](../Tests/CyclicSupport.lean) construit un système de règles qui ferme tous les champs du contrat, avec une auto-dépendance pour chaque ressource. Deux lectures fraîches différentes satisfont chacune leur certification pour le même opérateur. Cela précise ce que fournit l’équation de certification seule.

## Tous les parcours finis, cycles compris

[DependencyPaths.lean](../RelationalFoundations/DependencyPaths.lean) définit un parcours comme une donnée dans `Type`, avec ses arêtes, sa longueur et sa liste ordonnée de références visitées. Sa construction et ses transports sont exécutables.

| Obligation | Déclaration | Quantificateur et contenu |
|---|---|---|
| Couverture de tout parcours | `Coverage.requests`, `ordered_roundtrip`, `enumerated` | Tout résultat `Complete`, tout parcours fini : les demandes correspondantes sont construites ; leur retour donne toutes les références dans leur ordre, avec toutes les visites répétées |
| Lectures couvertes | `Coverage.values` | Toute sorte, toute référence du résultat : sa lecture égale la valeur attendue de sa demande exacte |
| Conservation | `transport`, `transport_nodes`, `transport_length` | Toute exécution et tout ancien parcours : longueur et liste ordonnée sont conservées par le transport des identités |
| Réflexion | `reflected` | Tout parcours du support prolongé qui commence à une ancienne ressource possède un parcours antérieur de même longueur, même liste transportée et même extrémité transportée |
| Cycles | `cycle_preserved`, `cycle_reflected` | Tout cycle de longueur positive sur les anciennes ressources se conserve et se reflète |
| Composition | `transport_composition_nodes` | Deux prolongements successifs et leur composition donnent la même liste de références transportées |

La réflexion est une proposition d’existence ; l’API exécutable comprend la construction du parcours couvert et son transport. Aucun inverse calculable du transport général n’est demandé par cette preuve.

Le support reste fini même quand un parcours revisite ses références arbitrairement souvent. La preuve porte sur chaque parcours fini ; elle conserve les cycles et les distingue d’un arrêt de l’exécuteur. Les tests `repeated_visits_covered` et `cycle_continues` appliquent les résultats génériques au système cyclique construit.

L’ordre strict des entrées du support hétérogène est une propriété supplémentaire de son datatype : [TypedResourceOrder.inputs_precede](../RelationalFoundations/TypedResourceOrder.lean) montre que toute entrée d’une opération précède son consommateur selon l’adresse chronologique. L’instance homogène construit aussi ses valeurs structurellement par son arbre d’expressions et ses références historiques ; ses trois positions par occurrence restent distinctes, avec des dépendances internes au fragment. Le contrat commun accueille ces différences.

## Classe d’histoires exacte

L’admission est définie sur les témoins opérationnels avant leur réalisation. Le champ local `reaction_exact` oblige toute étape admise à une source valide à coïncider avec la réaction produite, cible et témoin compris.

[FiniteRuleScope.admissible_unique](../RelationalFoundations/FiniteRuleScope.lean) démontre, pour tout `Rules`, que deux histoires admises de même longueur depuis l’origine sont égales comme couples dépendants cible/histoire. `every_horizon_admitted` fournit positivement l’histoire de chaque horizon. Les paramètres des systèmes de règles peuvent varier ; à paramètres fixés, la classe est déterministe. Les quantificateurs « toutes les histoires admises » et « tous les suffixes admis » couvrent chaque horizon de cette classe.

`realization_at_horizon` raccorde la réalisation commune à l’exécution depuis l’origine pendant la longueur de l’histoire. Cette longueur fournit un horizon fini ; la terminaison générale d’un exécuteur sans horizon est une autre obligation.

## Invariant effectif fermé

[HeterogeneousInvariants.lean](../RelationalFoundations/HeterogeneousInvariants.lean) définit indépendamment l’invariant suivant, pour une valeur initiale `seed` :

```text
dans un état observed, flag = test(number)
et, dans tout état, number ≤ seed + 1
```

`initial` ferme son cas initial. `adjust_bounded` traite les deux décisions : zéro produit un ; un successeur positif produit son prédécesseur. `step_preserves` ferme chaque règle admise observe/act/reuse. `admitted_preserves` couvre toute histoire admise depuis un état satisfaisant l’invariant.

`extracted` emploie exactement `Rules.extract_guarantee` avec ces preuves locales fermées. `constructed_then_forgotten` traite le cadre effectivement construit, son oubli et tout nombre de pas ultérieurs. `forgotten_suffix` traite toute histoire admise depuis la vue active. Le nombre initial reste un paramètre de preuve ; la mémoire exécutée après l’oubli conserve seulement position et actif.

`terminal_predicate_iff` et le commentaire corrigé de `ReducedContinuation.extract` précisent l’extraction : une égalité terminale transfère un prédicat dont la preuve est établie séparément. L’invariant ci-dessus fournit cette preuve pour une propriété des valeurs calculées.

## Oubli démontré et contrôle syntaxique

Les deux préfixes effectifs d’origines zéro et deux aboutissent à la même mémoire `⟨2, 1⟩`. `origin_irrecoverable_from_prefixes` établit qu’une fonction de cette mémoire ne peut rendre l’origine correcte pour toutes les origines et tous les horizons.

[NativeForgettingContract.first_decision_irrecoverable](../RelationalFoundations/NativeForgettingContract.lean) ajoute une perte historique effectivement produite : les premières décisions booléennes sont respectivement vraie et fausse. Une fonction de la mémoire oubliée ne peut restituer correctement cette décision pour toutes les origines au deuxième pas. Les preuves existantes conservent tous les événements, observations prévues et nouvelles certifications des suffixes natifs admis.

[HiddenEncoding.lean](../Tests/HiddenEncoding.lean) constitue un contrôle adversarial : son champ `active` encode origine et valeur active dans `2^origin × (2 × active + 1)`. Les procédures de codage/décodage sont totales et exécutables. `hidden_tracks_v1` prouve l’accord avec chaque exécution scalaire ; `hidden_origin_recoverable` reconstruit pourtant l’origine pour toute origine et tout horizon. Le même contrôle de champs et de noms accepte cet exemple.

[AuditForgettingV3.lean](../scripts/AuditForgettingV3.lean) distingue explicitement le contrôle syntaxique et les témoins sémantiques audités. Le test `HiddenReplay.lean.fail` utilise ce même contrôleur et exige le rejet d’une dépendance effective au rejeu historique. Les métaprogrammes de validation emploient les API de Lean pour inspecter son environnement ; les objets mathématiques inspectés restent soumis à l’audit exhaustif sans axiomes.

Le compteur constant `historicalNodes` et son identité `no_persistent_history` sont retirés. Les garanties substantielles reposent sur les séparateurs, les dépendances effectives et les preuves de conservation.

## Ce que consomme la position

`phase_memory_runs`, `phase_memory_events` et `phase_memory_view` construisent une continuation avec phase et nombre actif, et prouvent son accord pour tout horizon. Les événements comprennent source, cible et témoin opérationnel.

`same_phase_active_different_observation` donne deux mémoires avec même phase et actif, mêmes événements à tout horizon, mais des adresses absolues différentes. Le contrat V1 comprend ces adresses : il conserve donc la position absolue. La nécessité du champ s’évalue relativement à ce contrat précis.

## Coûts et références historiques

Les comparaisons matérielles existantes concernent leurs modèles déclarés de cellules et chiffres. Les compteurs de pas concernent les appels comptés. Les lectures récursives réévaluent des opérateurs et `phaseAt` recalcule la phase depuis la position ; leurs coûts nécessitent une analyse temporelle distincte. Les observations exploratoires de l’audit ne constituent pas des bornes Lean de performance.

Les reçus antérieurs ont été produits dans une révision de travail `0edc6135`, puis livrés dans le dépôt public. Leur liaison porte sur les empreintes des fichiers de l’instantané `99f0801`. V3 conserve ces reçus, vérifie cet instantané séparément et produit ses propres empreintes pour les sources corrigées.
