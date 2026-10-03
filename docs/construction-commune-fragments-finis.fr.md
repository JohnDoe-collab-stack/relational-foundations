# Construction commune des calculs à fragments finis

Un même constructeur réalise désormais les histoires finies des deux familles acquises au commit `e60bea1`. Son résultat porte sur une classe explicite de règles à producteurs locaux de fragments finis, références portant leur sorte et réaction issue du résultat produit. Les deux instances ferment toutes ses hypothèses locales. Les constructions précédentes restent disponibles avec leurs résultats et leurs tests.

Le code général est dans [FiniteRuleConstruction.lean](../RelationalFoundations/FiniteRuleConstruction.lean). Les producteurs, preuves locales et raccords des deux instances sont dans [FiniteRuleInstances.lean](../RelationalFoundations/FiniteRuleInstances.lean). Les tests sont dans [Tests/FiniteRuleConstruction.lean](../Tests/FiniteRuleConstruction.lean).

## Correspondance entre les deux constructions

| Composante | FeedbackCoverage | HeterogeneousFeedback | Construction commune et différence conservée |
|---|---|---|---|
| Occurrences et résultats | Une émission choisie depuis la lecture précédente et un réemploi produisent une liste ; cette liste fournit le témoin `record`. | Une lecture numérique produit un booléen ; la lecture de ce booléen détermine l'action numérique et son témoin ; le résultat est ensuite réemployé. | Commun : `produce`, puis `react` sur cette sortie effective, puis ajout du témoin à l'histoire. Les types de sorties et les règles de réaction restent propres à chaque instance. |
| Sortes et valeurs | Une sorte, de valeurs `List Token`. | Deux sortes, de valeurs `Nat` et `Bool`. | Spécifique et raccordable : `Kind` et `Value kind`. La sorte homogène est `Unit` ; les deux sortes hétérogènes gardent leurs types distincts. |
| Références | `Address layout` distingue l'origine, les positions fraîches et les positions historiques. | `Ref context kind` désigne une ressource de sa sorte et distingue la tête des références précédentes. | Spécifique et raccordable : `Ref frame kind`, avec une correspondance exacte entre anciennes références et nouvelles positions d'un fragment. |
| Ressources par occurrence | Trois positions : résultat, émission, réemploi. Le résultat dépend de deux positions du même fragment. | Une position de la sorte produite. Ses entrées désignent des ressources précédentes. | Différence conservée : `New step kind` décrit un fragment fini quelconque. Ses opérateurs peuvent lire des positions du même fragment. Le contrat conserve leur liste ordonnée d'entrées. |
| Demandes indépendantes | Origine, occurrence et rôle constituent `Demand history`. | Le contexte déclaré de l'histoire constitue les références typées attendues. | Commun : `Requests` se construit depuis les positions initiales et les fragments déclarés par les témoins opérationnels. `homogeneousRequests` et `heterogeneousRequests` raccordent ces demandes par deux transports exacts. |
| Producteurs et fermeture | `empty`, `emit`, `reuse`, `join` produisent et certifient les positions de l'expression. | `literal`, `test`, `adjust`, `reuse` produisent et certifient les ressources typées. | Commun : construire le fragment, certifier ses positions, puis reconstruire la certification des anciennes positions par transport des opérateurs et des lectures. Les syntaxes restent différentes. |
| Admission et couverture | Le token du témoin doit égaler le choix déclaré sur l'état source. | Les valeurs et la décision du témoin doivent satisfaire le test, l'action ou le réemploi déclarés. | Spécifique et raccordable : admission locale indépendante ; une réaction produite est admise et toute étape admise à cette source concorde avec elle. La couverture globale est ensuite démontrée. |
| Continuation et composition | Extension des supports et transport des adresses. | Extension des contextes et transport des références de chaque sorte. | Commun : avancer depuis la configuration existante, conserver les lectures, opérateurs et relations, puis composer les exécutions et leurs transports. |
| Extraction terminale | La liste effectivement lue égale l'état cible, puis la trajectoire déclarée. | L'état assemblé depuis les lectures typées égale l'état cible, puis la trajectoire déclarée. | Commun : extraire la vue depuis les ressources et utiliser sa concordance locale avec l'état. `extract_guarantee` traite les invariants opérationnels déclarés séparément. |

Les différences de syntaxe, de sortes, de nombre de positions et de dépendances internes sont fermées par leurs producteurs propres. Le chantier annoncé possède ainsi deux instances effectivement raccordées ; chaque extension à d'autres producteurs devra construire ses propres lois locales.

Les constructions déjà partagées dans le code sont `History`, `ExactTransport` et les outils constructifs d'énumération. Les deux boucles et leurs preuves étaient homologues et distinctes ; le constructeur général en extrait le mécanisme. Les lois de composition et d'accord des applications de listes sont désormais dans `DemandClosure.FiniteList`, avec leurs anciens noms conservés dans `FeedbackCoverage.ListMaps`. Le noyau général importe les primitives communes, puis le module des instances importe les deux familles.

## Classe de règles et hypothèses locales

`Rules` fixe les états, les témoins de pas, une origine et une condition `allowed step`. `Admissible` demande uniquement que chaque témoin de l'histoire satisfasse cette condition. Sa définition reçoit les états et témoins opérationnels ; la réalisation sera une sortie du constructeur.

La classe possède une origine finie et un producteur de successeur total sur ses configurations. Depuis une configuration valide, la réaction produite satisfait l'admission locale. Toute autre étape admise à cette même source concorde exactement avec cette réaction, cible et témoin compris. Cette exhaustivité locale fixe le périmètre déterministe couvert depuis l'origine. Les histoires commencent à l'origine et leur horizon est fini.

Les positions `Initial kind` et `New step kind` sont déclarées avant l'exécution. Elles disposent d'une énumération finie exhaustive sans répétition, toutes sortes réunies. `initialExpected` et `newExpected` attribuent leurs significations depuis les données de l'origine et du témoin opérationnel. La définition des demandes est récursive : l'origine fournit ses positions ; chaque occurrence ajoute celles de son fragment tout en distinguant les demandes précédentes.

Le support concret reste le support du producteur. Les procédures `read`, `node`, `inputs`, `eval` et `map` exposent ses lectures, ses opérateurs, leurs entrées ordonnées, leur évaluation et leur transport. Les lois de cette syntaxe portent sur une opération et une application de références. Elles conservent les différences entre les deux syntaxes du dépôt.

| Données ou lois du contrat | Portée exacte | Fermeture dans les deux instances |
|---|---|---|
| `initial`, `initialCoordinates`, `initial_values`, `initial_rules`, `initial_valid` | Construction et certification du fragment initial. | Support `empty` homogène ; support `literal seed` hétérogène ; preuves structurelles de leurs lectures. |
| `advance`, `Result`, `produce`, `react`, `advance_recorded` | Producteur d'un pas et témoin constitué depuis sa sortie effective. | `HistoricalFeedback.rule` ; `HeterogeneousFeedback.advance` avec `heteroProduce` et `heteroReact`. |
| `split` | Bijection, sorte par sorte, entre les références précédentes plus les nouvelles positions et toutes les références du support prolongé. | `homogeneousSplit` sépare `Address.old` et `Address.fresh` ; `heteroSplit` sépare `Ref.old` et `Ref.head`. |
| `new_values`, `new_rules` | Significations attendues et certification des seules positions fraîchement produites. | Calcul de l'expression homogène ; évaluation de l'opération typée ; `Support.read_correct` appliqué aux positions fraîches. |
| `old_values`, `old_nodes` | Conservation d'une ancienne lecture et de son opérateur, avec transport de ses références. | Lois structurelles des deux extensions de support. |
| `map_id`, `map_comp`, `inputs_map`, `eval_map`, `eval_congr` | Transport d'un opérateur et de sa liste d'entrées ; concordance de son évaluation. | Preuves par les constructeurs de `Node` et `Operation`. |
| `advance_valid`, `reaction_allowed`, `reaction_exact`, `visible_valid` | Concordances d'un pas avec l'admission et avec la vue effectivement lue. | Preuves locales sur la liste et sur les trois formes du focus hétérogène. |

Toutes ces clauses sont fermées dans les définitions `homogeneous` et `heterogeneous`. Elles prennent les paramètres primitifs annoncés : le type des tokens et sa procédure `choose`, ou le nombre initial. Leurs définitions utilisent les producteurs d'origine et d'un pas. Les preuves globales des anciennes réalisations interviennent ensuite dans les raccords de comparaison.

## Constructeur général et résultat démontré

Pour toute règle `R : Rules`, toute cible et toute histoire finie `h` issue de son origine, `R.complete h admitted` construit un seul témoin commun contenant : la configuration produite, son exécution, l'égalité de toute l'histoire fournie, les correspondances de toutes les demandes, leurs valeurs certifiées, la certification de tous les opérateurs, une énumération exhaustive sans répétition et la concordance terminale avec la cible.

L'ordre des quantificateurs reste explicite : la règle puis l'histoire puis sa preuve d'admission déterminent cette réalisation ; toutes les demandes et références sont ensuite quantifiées sur son même support. Chaque sorte conserve son propre domaine de références et son type de valeur.

| Obligation globale | Déclarations qui la construisent ou la démontrent |
|---|---|
| Construire le support initial et le successeur | `initialCoverage`, `growCoverage`, `recordedCoverage`, `build` |
| Certifier toutes les ressources | `advance_certified`, `Execution.certified`, `Coverage.values` |
| Couvrir toutes les demandes et ressources | `Coverage.coordinates` et ses deux identités de retour ; `requestFinite`, `certify` |
| Couvrir les entrées déclarées | `dependencies_covered` : toute entrée retrouve sa demande unique et revient à sa référence exacte, dans le même ordre et avec les mêmes répétitions |
| Réaliser toute histoire admise et caractériser les réalisations | `build`, `complete`, `coverage_iff` |
| Établir l'admission des histoires produites | `Execution.admissible` |
| Conserver identités, sortes, valeurs et opérateurs | `old_injective`, `old_new_distinct`, `Execution.embed_injective`, `values_preserved`, `nodes_preserved` |
| Conserver et refléter les relations | `dependencies_preserved`, `relation_preserved`, `relation_reflected` |
| Conserver les occurrences opérationnelles | `Execution.history_exact`, avec les témoins de `continuation` |
| Poursuivre depuis une réalisation existante | `resumeFrom`, `resumeExecutionFrom`, `resumeCompleteFrom`, `resume_expected` |
| Composer configurations, histoires et transports | `run_add`, `resume_compose`, `Execution.continuation_compose`, `embed_compose`, `compose_associative` |
| Transférer un invariant prouvé séparément | `Complete.terminal`, `extract_guarantee` reçoivent sa preuve initiale et sa préservation locale ; `HeterogeneousInvariants.extracted` ferme ces preuves pour la cohérence du test et la borne numérique |

La couverture à un pas porte sur les entrées déclarées par les opérateurs locaux du producteur. `DependencyPaths.Coverage.requests`, `ordered_roundtrip` et `enumerated` étendent cette couverture à tout parcours fini, avec ses visites répétées et ses cycles. Le raccord aux listes de dépendances indépendantes déjà définies dans les deux familles est aussi fermé : le champ `coveredDependencies` des résultats `homogeneousNativeComplete` et `heterogeneousNativeComplete` reprend exactement ces listes sur les supports produits par le constructeur commun.

`fragmentSize` additionne les positions de l'origine et celles des fragments de chaque occurrence. `request_count` et `resource_count` démontrent que l'énumération construite possède cette taille. Les instances donnent respectivement `1 + 3 * n` positions et `1 + n` positions après `n` occurrences. Le nombre est lu sur ces positions constituées ; la construction accepte la taille variable déclarée par chaque fragment.

## Raccord des deux réalisations

`homogeneousComplete` et `heterogeneousComplete` invoquent effectivement `Rules.complete`. Les équivalences `homogeneousAdmission` et `heterogeneousAdmission` conservent leurs admissions indépendantes. Les transports `homogeneousRequests` et `heterogeneousRequests` sont bijectifs ; `homogeneousMeanings` et `heterogeneousMeanings` prouvent leurs accords sémantiques.

`homogeneousFrame` et `heterogeneousFrame` établissent l'égalité des configurations complètes avec les réalisations acquises. Cette égalité porte sur les histoires et témoins, les supports, les références, les opérateurs et le focus. `frame_values`, `frame_nodes`, `frame_dependencies`, `homogeneousOperators` et `heterogeneousOperators` en donnent les conséquences sur les lectures et le transport des opérateurs et dépendances.

`homogeneousExecution` et `heterogeneousExecution` raccordent chaque exécution générale à l'exécution native sur ses mêmes configurations. `homogeneousTransport`, `heterogeneousTransport`, `homogeneousContinuation` et `heterogeneousContinuation` conservent leurs applications de références et leurs témoins de continuation. `heterogeneousResume` vérifie aussi la reprise native depuis la réalisation existante. Les deux fonctions `NativeComplete` restituent toutes les certifications dans les interfaces originales, avec la configuration et l'exécution du constructeur commun.

## Reconstruction locale et données persistantes

La configuration conserve les opérateurs constitués, leurs références historiques et le focus requis par la prochaine réaction. Les valeurs peuvent être relues récursivement depuis ce support ; les lectures réévaluent les opérateurs sans cache partagé et leur coût temporel requiert une étude distincte. Le booléen de décision hétérogène est ainsi produit par lecture de la référence identifiée, puis remis à la réaction.

La validité du focus et les certifications globales sont des propositions. La preuve `advance_valid` reconstruit la première localement ; `advance_certified` reconstruit les secondes depuis les certifications antérieures, les opérations conservées et le nouveau fragment. Le producteur de successeur prend la configuration brute. Les certifications complètes, l'énumération et la correspondance globale des demandes sont des sorties du résultat général.

Le test `numerical_reading_is_not_injective` fournit un séparateur concret pour identifier les références par leur seule valeur : le résultat numérique final et la ressource numérique initiale valent tous deux zéro, avec deux références distinctes. Il établit cette différence de force entre lecture numérique et identité historique dans la réalisation concernée. Une nécessité universelle de mémoire supplémentaire ou une minimalité du support demanderait un périmètre et des séparateurs supplémentaires.

## Vérification et portée

Les tests exécutent le constructeur général sur les histoires indépendantes des tests précédents. Ils vérifient les trois positions homogènes et leurs dépendances internes, les deux sortes et les deux décisions hétérogènes, les certificats dans les interfaces originales, la reprise du support existant, les anciennes lectures, les opérateurs, les relations, les témoins historiques, les transports et leur composition. Les contrôles exécutables lisent les sorties et les énumérations produites.

`CollapsedFragment.lean.fail` impose la distinction entre les positions par les identités de retour du transport exact. `GenericFalseAdmission.lean.fail` vérifie qu'une histoire localement contraire au test numérique fournit une obligation d'admission que le compilateur rejette. Les rejets attendus précédents et tous les tests existants sont conservés.

La commande complète est `pwsh -NoProfile -File scripts/verify-v4.ps1 -SkipComparison -SkipReference`. Elle vérifie compilation, audit de toutes les déclarations, catalogue des rejets attendus et projet migré. Les reçus datés sont [verification-result.json](verification-result.json) et [Migration/verification-result.json](../Migration/verification-result.json). Les comparaisons et empreintes du dépôt historique sont omises explicitement dans le dossier isolé.

La vérification du 2 octobre 2026 a réussi : 56 fichiers de fondations et de tests, 5 078 déclarations auditées sans dépendance à des axiomes, 174 sources migrées et 806 symboles publics contrôlés. Les 27 rejets attendus, la stratification des 154 modules de production migrés et les quatre frontières d'import passent.

Le théorème couvre les histoires finies du périmètre déclaré, avec des procédures locales totales et une réaction localement exhaustive depuis les configurations valides. Pour chaque système de règles fixé, `FiniteRuleScope.admissible_unique` établit une histoire admise par longueur. Son support fini couvre chaque référence et chaque parcours fini, cycles compris. La certification établit une équation sur la lecture fournie ; chaque instance ferme séparément sa production de valeurs. L'arrêt d'une exécution sans horizon, une classe maximale, les stratégies d'oubli, le cache et les performances demandent leurs propres constructions.

La vérification actuelle et les preuves complémentaires sont décrites dans la [validation V4](audit-corrections-v4.fr.md) et le [bilan des corrections](audit-corrections-v3.fr.md). Les reçus datés ci-dessus restent des références historiques conservées.

La [révision V4](audit-corrections-v4.fr.md#3-accord-général-des-coordonnées) démontre pour toutes les histoires admises que les coordonnées communes et natives désignent la même référence effectivement construite. Elle ferme leurs inverses, opérateurs et dépendances ordonnées ainsi que l'accord pendant les reprises et leur composition. Le séparateur de permutation précise la portée de cet accord aux constructeurs déterminés.
