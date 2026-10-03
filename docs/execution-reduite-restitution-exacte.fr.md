# Exécution réduite et restitution historique exacte

## Résultat

L’instance déterministe `Nat`/`Bool` dispose maintenant d’un exécuteur qui poursuit le calcul avec trois nombres : origine, position et valeur numérique active. Le booléen est reconstruit localement depuis le nombre qui l’a produit ; la phase est déterminée par la position. L’exécuteur calcule les résultats numériques et booléens, produit leurs témoins de réaction et assure le réemploi numérique.

Une seconde réduction retire la valeur active persistante. Son noyau conserve origine et position. Chaque appel `Kernel.tick` régénère temporairement l’état scalaire, calcule la réaction et émet son témoin effectivement produit. Le témoin est une sortie de l’appel, distincte du noyau persistant. Cette variante échange le cache numérique contre de la recomputation scalaire.

Les deux représentations permettent la restitution exacte de la configuration historique complète et de toutes ses certifications. Les fonctions de production et de continuation scalaire construisent leurs résultats indépendamment du support historique. La restitution complète constitue une opération séparée, explicitement demandée.

Le constructeur commun de référence reste celui du commit `0edc613`. `common_constructor_round_trip` couvre les configurations qu’il produit. Les deux instances et leurs tests antérieurs sont conservés.

## 1. Ce que consulte le calcul, ce que restitue le calcul

| Phase native | Consultations effectives | Résultat et réaction | Entrées historiques ordonnées |
|---|---|---|---|
| `ready n` | référence numérique active | `test n`, puis `observe n booléen` | `[référence numérique]` |
| `observed n b` | référence booléenne, puis référence numérique | `adjust b n`, puis `act n b b résultat` | `[référence booléenne, référence numérique]` |
| `updated n` | référence numérique produite | lecture typée, puis `reuse n n` | `[référence numérique]` |

Dans toute histoire atteignable, le booléen de `observed n b` vérifie `b = test n`. Cette propriété est démontrée par `trajectory_local`. La suppression de son stockage est donc justifiée par une reconstruction locale précise. À la phase suivante, `output` recalcule ce booléen, l’utilise pour choisir l’augmentation ou la diminution et calcule le résultat. À la phase de réemploi, il reprend la valeur numérique produite.

`evaluation_local` établit directement, pour les quatre constructeurs d’`Operation`, que l’évaluation est déterminée par les lectures des références figurant dans ses entrées. `producer_consultations` raccorde le résultat typé réduit au résultat du producteur natif. L’argument utilise les opérations concrètes de cette instance ; les listes d’entrées du contrat générique conservent leur portée précédente.

Les déterminations restituées comprennent l’histoire avec ses témoins de pas, les occurrences, le contexte des sortes, les valeurs de chaque ressource, les opérateurs, leurs références d’entrée ordonnées, le focus et les certifications. `certificate` construit l’interface native `CompleteRealization` pour l’histoire restituée : chaque référence dispose d’une demande indépendante, d’une valeur attendue, de ses entrées et de sa certification de règle. La couverture concerne toutes les ressources historiques.

## 2. Données persistantes et propositions

Les deux structures exécutables sont exactement :

```text
Memory = origine : Nat, position : Nat, actif : Nat
Kernel = origine : Nat, position : Nat
```

`Coherent memory` est une proposition séparée : la vue active coïncide avec la trajectoire issue de l’origine à la position atteinte. `initial_coherent`, `step_coherent` et `run_coherent` ferment cette proposition pour les configurations construites. Les structures persistantes contiennent exclusivement leurs champs numériques.

Les références actives sont restituées avec le focus de la configuration complète. Les occurrences sont coordonnées avec `Fin position` par `occurrenceCoordinates`, avec un transport exact et sa preuve d’injectivité. Les coordonnées historiques conservent les identités des ressources et leur sorte. Leur reconstruction s’appuie sur les producteurs et l’ordre des pas déterministes, plutôt que sur une identification de valeurs.

`scripts/AuditReduced.lean` vérifie les types des champs persistants et parcourt les dépendances des treize fonctions exécutables de production, d’itération et de réduction du cache. Il rejette les dépendances à `History`, `Support`, aux références, aux opérations historiques, aux configurations complètes, à leur exécuteur et à `reconstruct`. Lean partage un petit éliminateur de `Nat` nommé dans le module natif ; l’audit parcourt aussi son corps, constitué de `Nat.casesOn`.

## 3. Successeur et réaction effectivement calculés

```text
Memory
→ phase depuis la position, nombre actif
→ output : calcul du booléen, de l’ajustement ou du réemploi
→ nextState et event : résultat, cible et témoin de réaction
→ step : nouvelle position et nombre effectivement produit
```

`event` utilise le résultat d’`output` pour construire le témoin `observe`, `act` ou `reuse`. `event_target` prouve l’accord de sa cible avec `nextState`. `event_admitted` établit son admission locale. Le successeur numérique est extrait de cet état effectivement calculé.

Pour la variante avec cache retiré :

```text
Kernel
→ inflate : régénération scalaire de l’actif
→ Kernel.tick : réaction calculée et émise, noyau suivant
```

`tick_active` et `tick_next_view` établissent que l’actif régénéré depuis le noyau suivant est précisément celui que la réaction calculée a produit. `tick_exact` établit l’accord du témoin complet avec le producteur historique. Cette variante calcule une sortie à chaque appel ; son coût de régénération scalaire est déclaré séparément.

## 4. Restitution exacte

`reconstruct` est la restitution demandée à partir de l’origine et de la position. Elle exécute les règles natives pour construire la configuration complète. Les preuves obtenues sont :

| Déclaration | Garantie |
|---|---|
| `reconstruct_reduce` | toute configuration atteignable est restituée exactement après réduction |
| `reduce_reconstruct` | toute mémoire cohérente est retrouvée après restitution puis réduction |
| `reconstruct_step` | restitution du successeur réduit égale au successeur complet |
| `reduce_step` | réduction du successeur complet égale au successeur réduit |
| `event_exact` | égalité du témoin complet de réaction, avec sa source et sa cible |
| `reduce_run`, `reconstruct_run` | accord des itérations depuis une mémoire déjà constituée |
| `certificate` | toutes les certifications natives de la restitution |
| `common_constructor_round_trip` | même restitution exacte pour le constructeur commun acquis |

Ces égalités portent sur les configurations complètes. Elles comprennent donc les données de l’histoire, le support, les opérateurs, les entrées ordonnées et le focus. `Coherent` est nécessaire pour comparer les valeurs actives et les réactions effectivement calculées. Certaines égalités de restitution seules sont plus fortes : elles dépendent de l’origine et de la position même lorsqu’un cache scalaire a été corrompu. Les tests distinguent ces deux portées.

## 5. Toute continuation finie indépendamment admissible

`continueFrom` reçoit une histoire finie commençant à `view memory`. Son corps exécutable utilise la mémoire réduite et la longueur de cette histoire. Pour ces règles déterministes, toute histoire localement admissible fournit les mêmes réactions que l’exécution effective. Son admission reste déclarée par les règles locales natives.

Pour toute mémoire cohérente et toute continuation ainsi admissible, `active_continuation` prouve l’égalité de la restitution finale avec la spécification de l’histoire antérieure prolongée par cette continuation. `active_terminal` donne le résultat terminal indépendant. `all_finite_continuations` et `continuationCertificate` exposent aussi l’interface native complète.

Les transports restitués sont construits par `restorationExecution` et `transport`. Les résultats `old_identity`, `old_value`, `old_operator`, `old_ordered_inputs`, `old_relation` et `old_certificate` préservent les identifiants, sortes, valeurs, opérateurs, entrées ordonnées, relations et certifications. La relation historique est préservée et réfléchie. `transports_compose`, `histories_compose` et `reconstruction_compose` ferment la composition des prolongements. `extract` transporte la garantie terminale déclarée indépendamment vers la vue réduite.

La réduction supplémentaire du cache conserve ces résultats via `inflate_erase`, `every_tick` et `kernel_continuation`. Les tests comprennent une continuation fournie indépendamment depuis une mémoire déjà constituée à la position 2, jusqu’à la position 6.

## 6. Weakening et résidus effectivement séparés

| Donnée candidate | Consommation ou observation | Reconstruction démontrée | Décision |
|---|---|---|---|
| support et histoire développés | consultations historiques et certificats à restituer | `reconstruct_reduce`, `certificate` | retirés de la mémoire persistante |
| références et identités | lectures du producteur et déterminations historiques | focus restitué, coordonnées exactes, `occurrenceCoordinates` | retirées du stockage persistant |
| booléen actif | sélection de l’ajustement | `b = test n` sur les états atteignables | retiré ; recalcul local |
| phase | choix de l’opération suivante | `trajectory_phase`, puis `phaseAt position` | retirée comme champ autonome |
| nombre actif | entrée numérique du prochain producteur | `inflate_erase` par régénération scalaire | retiré dans `Kernel`, conservé comme cache dans `Memory` |
| origine | restitution du producteur initial et de sa valeur | séparateur positif | conservée |
| position | restitution du nombre et de l’identité des occurrences | séparateur positif | conservée |

Le premier résidu isolé est l’origine. À la position 2, les origines 0 et 2 produisent toutes deux l’actif `updated 1`. La position et l’actif coïncident, tandis que les valeurs initiales restituées valent respectivement 0 et 2. `origin_not_reconstructible` prouve qu’aucune fonction de ces seules données ne reconstruit l’origine sur toutes les mémoires cohérentes.

Le résidu de position est examiné ensuite : pour l’origine 0, les positions 0 et 6 ont le même actif `ready 0`. Les histoires comportent respectivement 0 et 6 occurrences. `position_not_reconstructible` exclut la récupération de la position depuis les seuls origine et actif.

À la position 6, la ressource initiale et la dernière ressource numérique ont toutes deux la valeur 0. `repeated_zero_equal` et `repeated_zero_distinct` démontrent ensemble l’égalité des valeurs et la distinction des références. Ces séparateurs portent sur les projections précisées ci-dessus. Ils laissent ouverte la comparaison avec d’autres codages conjoints ; aucune minimalité absolue de mémoire n’est conclue.

## 7. Réduction matérielle et coûts séparés

Le coût déclaré attribue une unité à une cellule et une unité à chaque chiffre binaire d’un naturel. La charge numérique est donc prise en compte : `digits n = log₂ n + 1`, avec un chiffre pour zéro. Ce modèle de représentation fournit des inégalités formelles ; sa conversion vers les octets d’un allocateur constitue une autre question.

Pour le noyau à la position `n`, le coût persistant est :

```text
3 + digits(origine) + digits(n)
```

Le support complet comporte exactement `n + 1` nœuds de ressources, démontré à partir de ses constructeurs par `support_nodes` et `reconstruction_resources`. Son histoire comporte `n` extensions et une racine. En comptant seulement ces nœuds et les chiffres de l’origine, on obtient déjà la borne inférieure :

```text
2 × (n + 1) + digits(origine)
```

Cette borne laisse de côté les références, la syntaxe des opérateurs et les autres charges numériques des témoins. `strict_reduction` prouve que le coût du noyau est strictement inférieur à cette borne dès `n ≥ 3`, pour toute origine. Le résultat compare donc une charge numérique explicitement variable à des données historiques effectivement matérialisées.

Le cache ajoute une cellule et les chiffres du nombre actif. `cached_reduction` fournit une condition suffisante constructive : `4 + digits(actif) ≤ n`. Elle est satisfaite dans le test à la position 6. La comparaison à la borne inférieure peut rester conservatrice pour de grandes valeurs initiales.

| Coût | Résultat établi | Ce que la mesure couvre |
|---|---|---|
| mémoire persistante | `kernelCost`, `cacheCost`, `strict_reduction`, `cached_reduction` | cellules et chiffres du modèle déclaré |
| travail temporaire de restitution | `working_support_bound` | au plus `n + 1` nœuds dans chacun des supports intermédiaires jusqu’à la position demandée |
| taille restituée | `output_size`, `reconstruction_history_length` | exactement `n + 1` ressources et `n` occurrences, avec leurs références et certificats |
| régénération scalaire du cache | `regeneration_exact`, `scalar_step_count` | exactement `n` appels de la transition scalaire |
| restitution historique | `replay_step_count` | exactement `n` pas complets reconstruits |

Les compteurs de transitions distinguent les appels des coûts d’arithmétique, des lectures récursives et de l’allocation. Les longueurs des chemins de référence, les piles récursives, les traces d’exécution construites à la demande et les listes de certifications contribuent à la taille réelle des restitutions et au travail temporaire. La borne sur les nœuds du support porte sur cette composante précise ; elle fournit une information différente d’une borne sur tout le tas temporaire en octets. La phase est actuellement recomputée par une petite récurrence sur la position. Le noyau ajoute la régénération scalaire à chaque tick. Ces choix n’emportent aucune conclusion de gain de temps.

## 8. Périmètre et vérification

La classe traitée est l’instance déterministe actuelle, depuis les configurations atteignables et pour chaque horizon fini. Les preuves d’admission, de reconstruction locale, de réaction et de certification sont fermées par les producteurs existants. Aucune entrée externe ni règle non déterministe n’est ajoutée.

L’oubli véritable, la mémoire minimale, une borne physique en octets et la terminaison d’un exécuteur sans horizon constituent des chantiers distincts. Le résultat acquis ici est une compression constructive : les déterminations historiques restent exactement restituables.

Commandes reproductibles :

```powershell
pwsh -NoProfile -File scripts/verify-v4.ps1 -SkipComparison -SkipReference
```

Le script construit les modules publics et les tests, audite exhaustivement leurs dépendances axiomatiques, contrôle les dépendances du producteur réduit et le type de ses champs persistants, exige les neuf rejets attendus du socle, puis vérifie le projet migré et ses dix-neuf rejets attendus. Les comparaisons et empreintes du dossier historique sont explicitement écartées de cette commande autonome. Les résultats datés sont dans `verification-result.json` et `../Migration/verification-result.json`.

La vérification du 2 octobre 2026 est réussie : 60 fichiers sources du socle et des tests, 5 341 déclarations sans dépendance axiomatique, 13 fonctions exécutables et 138 dépendances contrôlées pour l’exécution réduite. La migration passe également : 174 sources, 3 095 déclarations constitutives et 1 191 déclarations computationnelles récentes sans dépendance axiomatique, 806 symboles publics, 3 400 audits publics et quatre frontières d’import. Les 28 rejets attendus sont confirmés.

Les nouveaux modules sont `ReducedHeterogeneous.lean`, `ReducedContinuation.lean` et `ReducedWeakening.lean`. Les tests sont dans `Tests/ReducedHeterogeneous.lean`. Le rejet `UnreachableReducedMemory.lean.fail` contrôle qu’une mémoire dont l’actif contredit l’origine et la position exige sa propre preuve de cohérence.

La vérification actuelle et les preuves complémentaires sont décrites dans la [validation V4](audit-corrections-v4.fr.md) et le [bilan des corrections](audit-corrections-v3.fr.md). Les reçus datés ci-dessus restent des références historiques conservées.
