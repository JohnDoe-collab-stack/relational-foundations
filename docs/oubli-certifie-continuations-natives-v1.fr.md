# Oubli historique certifié pour les continuations natives — V1

Le résultat V1 est conservé, avec les précisions de portée de cette révision. Son protocole original et ses reçus sont historiques. La vérification courante emploie la [V3 portable](validation-v3.fr.md) ; le [bilan des corrections](audit-corrections-v3.fr.md) présente les preuves complémentaires.

## 1. Résultat et deux contrats

Dans l'instance déterministe Nat/Bool de `HeterogeneousFeedback`, la position atteinte et le nombre actif suffisent pour produire chaque prochain pas natif, ses références typées, son opérateur, ses entrées ordonnées et sa certification locale. Cette représentation permet toutes les continuations finies admises par les règles natives déterministes, avec une histoire par horizon. Elle perd effectivement certaines différences historiques.

Les deux contrats sont conservés et distingués :

| Contrat | Données promises | Construction |
|---|---|---|
| Restitution historique acquise | Origine, préfixe entier, occurrences, valeurs, opérateurs, entrées ordonnées et certifications historiques | `ReducedHeterogeneous`, `ReducedContinuation`, `ReducedWeakening` ; origine conservée |
| Continuation native V1 | État actif, résultats et réactions, identités des ressources encore consultées, nouvelles ressources et opérateurs, entrées ordonnées, nouvelles évaluations certifiées | `NativeForgettingV1` et ses trois raccords ; position et actif conservés |

Le contrat historique et ses preuves restent disponibles. V1 ajoute un autre résultat : la même représentation suffit à continuer deux préfixes dont elle a perdu la différence initiale.

La classe admissible reste exactement `HeterogeneousFeedback.LocalAdmission` et `HeterogeneousFeedback.Admissible`. Les suffixes fournis dans les théorèmes sont quantifiés avant leur exécution. La garantie terminale est leur état cible, porté par leur type natif : pour tout suffixe admis `h : History Step (view m) target`, `view (run m h.length) = target`.

Les observations couvertes comprennent la sorte et la valeur produites, l'opérateur réel, la liste ordonnée de ses références et l'adresse de sa nouvelle occurrence dans l'exécution considérée. La consultation arbitraire d'une ressource ancienne définit un autre contrat, matérialisé par le séparateur de la section 6.

## 2. Exigences des trois consommateurs réels

Les branches de `HeterogeneousFeedback.advance` consultent leur `Focus`, construisent un `Operation`, l'évaluent sur le support, puis étendent ce support et l'histoire. À la position `p`, le support atteint contient `p + 1` ressources : la ressource initiale à l'adresse 0, puis une nouvelle ressource par pas. Ces adresses concernent les ressources ; l'histoire opérationnelle du préfixe a longueur `p`.

| Branche et phase | Consultation réelle et occurrence | Entrées dans leur ordre natif | Production et prochain focus | Justification requise |
|---|---|---|---|---|
| `observe`, `ready n` | Numérique actif, adresse `p` | `[number(p)]` | `.test` produit un booléen à `p + 1` ; le nombre garde l'adresse `p` | `Valid` raccorde la référence numérique à `n` ; le nouvel opérateur certifie `test n` |
| `act`, `observed n b` | Booléen à `p`, numérique à `p - 1` | `[truth(p), number(p - 1)]` | `.adjust` produit le nombre à `p + 1` ; la réaction contient le booléen effectivement lu | `Valid` raccorde les deux lectures ; l'atteignabilité établit `b = test n` |
| `reuse`, `updated n` | Numérique produit au pas précédent, adresse `p` | `[number(p)]` | `.reuse` produit une nouvelle occurrence numérique à `p + 1` | Référence source typée, valeur correctement raccordée, nouvelle évaluation certifiée |

Le nombre actif, sa référence et sa provenance entière ont ainsi trois fonctions distinctes. Pour `reuse`, la valeur source et la valeur produite coïncident, tandis que les occurrences restent distinctes : la source est transportée par `.old` et la nouvelle ressource est `.head`.

`ReducedHeterogeneous.evaluation_local` établit la localité des valeurs évaluées. La conservation des références repose sur des preuves supplémentaires : adresses natives, injectivité, transport et égalité de l'opérateur complet avec ses références effectives.

## 3. Exécution depuis deux naturels

Le module [NativeForgettingV1](../RelationalFoundations/NativeForgettingV1.lean) définit :

```text
Memory = { position : Nat, active : Nat }
initial n = { position := 0, active := n }
view m = state (phaseAt m.position) m.active
```

`Context` représente la frontière typée utile : `[number]` en phase `ready` ou `updated`, `[truth, number]` en phase `observed`. `read` fournit le nombre actif et, en phase `observed`, recalcule `test active`. `operation` choisit le véritable opérateur typé ; `produce` l'évalue sur cette frontière.

`target` construit l'état suivant à partir de la valeur ainsi produite. `event` construit le témoin natif, y compris la sélection effectivement lue dans `act`. `step` conserve le nouveau nombre actif et incrémente la position. `tick` retourne la mémoire suivante, le témoin, l'observation relationnelle et une `Production` certifiée.

La `Production` contient le nouvel opérateur, sa valeur et deux preuves dans `Prop` : l'exactitude de l'opérateur choisi et l'équation de son évaluation locale. Ses indices sont les deux champs de mémoire et la frontière finie. Elle est construite positivement par `certify`. `new_evaluation_certified` la raccorde au contexte où la nouvelle ressource vient d'être ajoutée.

Les producteurs reçoivent uniquement cette mémoire. `forget` et `erase` sont des conversions d'entrée ; ils sont distincts des producteurs. Les comparaisons avec les supports natifs figurent dans les théorèmes de raccord. Les listes `observations` et `events` sont des sorties optionnelles ; le pas suivant utilise les deux naturels de `Memory`.

## 4. Références, identités et nouveaux certificats

Le module [NativeForgettingBridgeV1](../RelationalFoundations/NativeForgettingBridgeV1.lean) définit `address` directement sur les constructeurs de `TypedResources.Ref`. L'adresse d'une référence `.head` est la longueur du contexte antérieur ; `.old` conserve cette adresse.

- `address_bound` borne l'adresse par la taille du contexte.
- `address_identity` prouve l'injectivité pour une sorte et un contexte donnés.
- `transported_address` prouve sa conservation par une extension native.
- `execution_sized` et `execution_focused` raccordent les adresses de la frontière à la position et aux références réelles du focus, pour chaque configuration atteignable.

`Matches` est une relation de preuve dans `Prop`. Elle rassemble l'accord de l'état, de la position, des lectures valides, de la taille et du focus. `forget_matches` construit toutes ses lois depuis une exécution native atteignable. Cette relation sert aux comparaisons ; la mémoire et le producteur V1 ont les types décrits à la section 3.

`frontierFor` relie chaque port local à une référence du support natif considéré. `frontierFor_value`, `frontierFor_address` et `frontierFor_injective` préservent respectivement les lectures, les coordonnées et les distinctions typées. `retained_native_identity` démontre que tout port encore vivant au pas suivant désigne exactement le transport de son ancienne référence.

Le raccord d'une nouvelle production comprend :

| Détermination | Déclaration principale |
|---|---|
| Identité de la nouvelle occurrence | `new_occurrence_memory` : l'adresse native vaut `position + 1` |
| Sorte et valeur effectivement produites | `new_value_memory` : égalité des paires dépendantes sorte/valeur |
| Opérateur réel avec ses références natives | `new_operator_memory` : égalité de la syntaxe complète après transport des ports |
| Entrées ordonnées | `new_inputs_memory` : égalité de la liste effective des références typées |
| Réaction et sélection effectives | `event_native` : égalité du témoin natif complet |
| Évaluation certifiée sur la frontière | `certified_frontier_evaluation` |
| Évaluation du nouveau nœud dans le support prolongé | `certified_new_evaluation` |
| Ensemble des observations couvertes | `observation_native` |

Les certificats V1 sont produits localement. Le raccord au support natif utilise les lois déjà prouvées de lecture et de transport ; il quantifie sur ce support dans la preuve.

Une identité est préservée à l'intérieur de son exécution. Entre deux préfixes, `Corresponding` relie explicitement les références via leur port local commun. L'adresse numérique seule exprime une coordonnée relative ; la comparaison entre exécutions conserve son support de référence.

## 5. Toutes les continuations finies admises

Le module [NativeForgettingContinuationV1](../RelationalFoundations/NativeForgettingContinuationV1.lean) ferme le passage du raccord local à tout suffixe fini.

1. `forget_step` démontre l'égalité entre l'effacement du successeur natif et le successeur V1.
2. `locally_exact` utilise les équations de l'admission native pour déterminer le témoin complet d'un pas admis. `admissible_history` étend cet accord à toute histoire native admise fournie indépendamment.
3. `run_view`, `all_admissible_terminal` et `all_admissible_events` accordent l'itération V1 à l'état cible et à chacun des témoins du suffixe.
4. `matches_run` ferme le raccord à chaque préfixe. `every_observation`, `every_reaction`, `every_certificate` et `every_new_evaluation` couvrent chaque prochain pas. Les égalités d'opérateurs et d'entrées s'appliquent avec ce même raccord.
5. `all_native_continuations` retrouve le suffixe fourni comme continuation de l'exécution native effective, avec son témoin complet. `observation_log` accorde toute la liste des productions V1 aux productions natives.
6. `run_add`, `transports_compose` et `observation_composition` accordent les prolongements successifs. Les transports natifs préservent les références anciennes injectivement et conservent leurs adresses.

`forgetting_all_admissible` est une entrée fermée : elle reçoit une exécution native atteignable et un suffixe indépendamment admis. Elle fournit ensemble la garantie terminale, l'accord des témoins et l'accord des observations relationnelles. `forgetting_all_new_evaluations` ferme les nouvelles certifications pour tout indice de pas.

Le périmètre porte sur chaque horizon fini. Le contrat déclaré suffit à toutes les opérations des trois règles natives déterministes. Un exécuteur sans horizon et des règles supplémentaires restent des objets distincts.

## 6. Perte historique effective et réemploi non vide

Le module [NativeForgettingSeparationV1](../RelationalFoundations/NativeForgettingSeparationV1.lean) construit les deux préfixes depuis les producteurs natifs :

```text
origine 0 → observe true  → act 1 → updated 1
origine 2 → observe false → act 1 → updated 1

position atteinte : 2
mémoire V1 commune : { position := 2, active := 1 }
```

`same_erased` prouve l'égalité des mémoires. `same_all_admitted_suffixes` réalise sur chaque préfixe tout suffixe natif admis fourni. `same_all_future_observations` prouve l'accord de toutes leurs productions observées, pour chaque horizon. `zero_new_certificates` et `two_new_certificates` raccordent les certificats localement produits à chacun des deux supports.

Le suffixe `reuseSuffix` est effectivement admis et contient un pas. Le calcul produit :

```text
source : updated 1
opérateur : reuse
entrée typée : number à l'adresse 2
nouvelle occurrence : number à l'adresse 3
résultat : 1
état suivant : ready 1
```

`typed_reuse_wiring`, `fresh_reuse_identity` et `reuse_certified` établissent ensemble ce réemploi, la distinction de sa source et de sa nouvelle occurrence, et son évaluation locale.

La lecture native de la ressource initiale, par `.old (.old .head)`, donne 0 dans le premier préfixe et 2 dans le second. `initial_observation_separates` prouve cette différence. `origin_irrecoverable` et `origin_irrecoverable_from_prefixes` excluent une fonction de reconstruction de l'origine depuis la seule mémoire V1, respectivement sur les mémoires cohérentes acquises et sur tous les préfixes natifs atteints.

Ainsi la différence initiale est effectivement perdue par la représentation V1, et la continuation admise reste effectivement constructible avec ses références et certificats. La restitution historique complète demeure assurée par le contrat acquis qui conserve l'origine.

## 7. Weakening relatif au contrat déclaré

| Donnée examinée | Consommation précise | Reconstruction ou séparateur | Décision V1 |
|---|---|---|---|
| Origine | Restitution initiale ; aucune lecture du prochain producteur natif | Préfixes 0/2 à la position 2 ; accord de tous les suffixes et séparation initiale | Supprimée |
| Nombre actif | `test`, `adjust`, `reuse` | Même position initiale pour 0/1 ; résultats booléens différents ; `active_not_reconstructible` et `active_consumption_separates` | Conservé |
| Position | Adresses absolues des ressources encore lues ou créées | Actif 0 aux positions 0/6 ; nouvelles adresses 1/7 ; `position_not_reconstructible` | Conservée pour ce contrat d’adresses ; `NativeForgettingContract.phase_memory_events` prouve que phase et actif suffisent pour les événements |
| Phase autonome | Choix de l'opération et de la frontière | `phaseAt position`, raccordé par `phaseMatch` | Recalculée |
| Booléen autonome | Sélection dans `act` | `test active`, raccordé par la validité locale et `frontierFor_value` | Recalculé |
| Références complètes du focus | Identités des entrées ordonnées | Ports typés, coordonnées et `frontierFor` ; preuve d'identité conservée | Frontière locale construite à la demande |
| Support et préfixe complets | Provenance et restitution historiques | Localité de l'évaluation, raccords fermés des opérateurs et de leurs nouvelles certifications | Retirés de la mémoire de continuation |
| Nouveaux opérateurs et certificats | Productions couvertes par le contrat V1 | `operation`, `certify`, `new_operator_memory`, `certified_new_evaluation` | Produits à chaque pas comme sorties |

Les séparateurs portent sur les projections et observations énoncées. Le résultat justifie ces deux champs dans cette représentation et ce contrat. La recherche d'un codage absolument minimal reste ouverte.

## 8. Coût persistant déclaré

Le modèle de coût reprend les cellules et chiffres binaires de `ReducedWeakening`. Pour un ancien cache `old` à trois naturels :

```text
cacheCost old = 4 + digits(origin) + digits(position) + digits(active)
cost (erase old) = 3 + digits(position) + digits(active)

cacheCost old = cost (erase old) + 1 + digits(origin)
```

`cost_removed_origin` prouve cette égalité pour toute mémoire ancienne. La réduction porte exactement sur la cellule et les chiffres de l'origine.

L'ancien `Kernel` conserve deux naturels, origine et position, puis régénère le cache actif. Son coût est `3 + digits(origin) + digits(position)`. V1 conserve position et actif et assure une autre garantie. À l'origine 0, position 60, le test montre une égalité des coûts persistants V1 et `Kernel`. La comparaison formelle démontrée ici concerne le cache à trois naturels.

La production locale recalcule la phase et, quand nécessaire, le booléen. Les logs de sorties et les allocations temporaires se distinguent de la mémoire persistante. Le modèle déclaré mesure des cellules et chiffres, indépendamment d'une mesure de temps ou d'octets d'allocateur.

## 9. Vérification V1 et références préservées

Commande reproductible dans ce dossier isolé :

```powershell
pwsh -NoProfile -File scripts/verify-forgetting-v1.ps1
```

Le protocole V1 reprend la construction complète du socle et de la migration, les contrôles des sources, les audits axiomatiques exhaustifs, l'audit de l'exécution réduite acquise, les rejets attendus existants et les frontières d'import. Il ajoute l'audit [AuditForgettingV1](../scripts/AuditForgettingV1.lean), qui traverse les types et les corps des producteurs et des structures de sortie : deux champs `Nat` et contrôle des noms de dépendances historiques. Ce contrôle est syntaxique. Les pertes d’information sont établies par les séparateurs et théorèmes d’irréconstructibilité. Les [compléments V3](audit-corrections-v3.fr.md) prouvent aussi la perte de la première décision, précisent la consommation de la position et donnent un encodage caché accepté par ce contrôle de forme.

Les tests [NativeForgettingV1](../Tests/NativeForgettingV1.lean) contrôlent les propriétés universelles et les calculs effectifs. Trois rejets supplémentaires vérifient les sortes incompatibles, l'inversion des entrées ordonnées et l'utilisation d'un raccord de preuve appartenant à l'autre préfixe. Ils sont séparés dans `Tests/ExpectedFailures/NativeForgettingV1`.

Les reçus V1 sont [verification-forgetting-v1.json](verification-forgetting-v1.json) et [le reçu de migration V1](../Migration/verification-forgetting-v1.json). Le protocole enregistre les empreintes des deux reçus de référence et vérifie leur conservation exacte. Les contrôles du dossier original et de la comparaison historique sont explicitement écartés de cette vérification autonome ; les autres agents peuvent poursuivre dans leurs dossiers.

Vérification réussie le 2 octobre 2026 : 65 sources du socle et des tests, 5 659 déclarations sans dépendance axiomatique, 22 entrées de données et producteurs et 199 dépendances de types/corps contrôlées pour V1. L'exécution réduite acquise conserve son audit de 13 producteurs et 138 dépendances. La migration passe sur ses 174 sources, 806 symboles publics, 3 095 déclarations constitutives et 1 191 déclarations computationnelles récentes sans axiome, ainsi que quatre frontières d'import. Les 31 rejets attendus sont confirmés : 9 acquis dans le socle, 3 nouveaux pour V1 et 19 dans la migration. Les deux empreintes des reçus de référence sont conservées.

Ce chantier est livré dans son espace isolé, avec les sources et protocoles vérifiables. Aucun commit, push ou merge n'a été effectué pour V1.
