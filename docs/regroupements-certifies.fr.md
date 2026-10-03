# Regroupements certifiés, projections et continuation

Le constructeur part des opérations locales admises dans un contexte constitué. Il produit une cible terminale, la trace qui y conduit et sa certification. La cible commune des regroupements compatibles est démontrée à partir de leurs raccords locaux et de leur décroissance. Dans l'instance relationnelle, ce constructeur retrouve la sélection existante et sa largeur exacte, sur toute histoire finie de rôles.

Version anglaise : [Certified grouping, projections and continuation](regroupements-certifies.en.md). La [reproduction V5](validation-v5.fr.md) fixe le périmètre technique et les preuves d'exécution.

## 1. Classe de règles et résultat générique

Les déclarations de cette partie appartiennent à `RelationalFoundations.CertifiedGrouping`.

`Rules` reçoit uniquement ces données locales :

| Champ | Donnée ou loi locale |
|---|---|
| `State` | Configurations du contexte examiné. |
| `Step x y` | Témoin dans `Type` d'une opération effective admise de `x` vers `y`. Le témoin conserve son identité opérationnelle. |
| `rank` | Mesure naturelle de la configuration. |
| `choices x` | Liste finie des couples cible/témoin disponibles depuis `x`. Leur admission est portée par `Step`. |
| `locate` | Pour chaque opération admise, une entrée effectivement présente dans cette liste avec son accord hétérogène sur le couple complet. |
| `decreases` | Chaque opération effective diminue strictement la mesure. |
| `diamond` | Pour deux opérations issues de la même source, construction d'une cible et de deux traces dirigées vers cette cible. |

L'admission est définie par `Step` avant la normalisation. Les listes de choix sont exactes sur cette admission. La cible terminale, la frontière globale et une solution complète sont produites ensuite.

`Trace` conserve les témoins successifs et leurs extrémités. Sa trace vide réalise l'action neutre. `Trace.append`, `append_assoc`, `act_append` et `act_preserves` construisent et certifient la composition. `Join` contient une cible commune et deux traces orientées. `Chain` décrit des liens parcourus dans les deux sens ; sa réalisation opérationnelle utilise les traces orientées de `joinOfChain`.

`Rules.normalizeWithin` utilise une récursion structurelle sur un compteur suffisant pour la mesure. `normalize` initialise ce compteur avec `rank x` et produit `Normalized` : cible, trace et terminalité. `terminal_of_empty` utilise `locate` pour établir la terminalité d'une liste vide. `terminal_unique` dérive l'unicité terminale de `diamond` et de `decreases`.

En écrivant `N = Rules.normal`, les conclusions sont :

\[
N(N(x))=N(x),\qquad
N(x)=N(y)\iff \mathrm{Nonempty}(\mathrm{Join}(x,y))
\iff \mathrm{Nonempty}(\mathrm{Chain}(x,y)).
\]

`joinOfNormalEq` et `joinOfChain` construisent les témoins de jonction dans `Type`. `confluence` traite deux traces arbitraires issues d'une même source. `trace_length_le` borne toute trace effective par la mesure initiale. Cette terminaison concerne un regroupement sous les règles du contexte examiné ; une continuation peut constituer un autre contexte et d'autres opérations.

## 2. Lectures réunies et identifications composées

Pour une famille de projections `P i`, `ProjectionFamily.JointAgreement P x y` signifie que **toutes** les lectures sont égales. `ProjectionFamily.Path P x y` conserve une chaîne où chaque maillon choisit **une** projection et son égalité. Ces deux relations gardent leurs quantificateurs respectifs.

`Path.minimal` prouve la propriété de clôture engendrée par ces liens. `Path.invariant` propage toute lecture respectant chaque identification locale. Lorsque la famille est connectée, `boundary_constant` démontre qu'une frontière booléenne respectant tous ces liens est constante, sur toutes les paires de sources.

`ProjectionFamily.Authorized` reçoit, pour chaque égalité locale, une jonction admise construite. `realizePath` produit la jonction pour toute chaîne. Avec `stepIdentification`, qui associe positivement une projection identifiante à chaque opération, `exact_fibres` caractérise exactement les fibres de `N` par ces chaînes.

`BinaryGrouping` ferme ce contrat sur des profils de positions binaires. La projection locale sélectionne sa position autorisée et conserve les autres. Avec au moins deux positions, `joint_injective` prouve que les lectures réunies distinguent les sources. Lorsque toutes les positions sont autorisées, `fullyConnected` prouve que les identifications composées relient toutes les sources. `projections_each_separate` et `nevertheless_connected`, dans `Tests/CertifiedGrouping.lean`, donnent le cas à quatre profils : deux sources ont des lectures différentes sous chaque projection et appartiennent à la même composante engendrée.

## 3. Obligations et frontières exactes

`FiniteImage.Target` est le type des cibles certifiées stables sous `N`. `carry` produit `N(x)` avec sa preuve de stabilité. `carry_surjective` utilise une cible stable comme source positive. `carry_fibres` conserve l'équivalence exacte avec les chaînes admises.

`FiniteImage.Source` ajoute explicitement une égalité décidée, une énumération finie complète et son absence de doublons. `frontier` normalise cette énumération puis retire les répétitions. `frontier_exact` prouve que ses membres sont exactement les cibles stables. Les données transportées restent arbitraires ; cette décision d'égalité compare les identités des configurations du périmètre.

`FiniteImage.Composed` déclare une frontière produite avec ses preuves locales d'exactitude et d'absence de doublons. L'interface générique reçoit cette construction ; l'adaptateur relationnel la ferme par les producteurs de fragments existants. `exhaustive_composed` prouve l'accord d'appartenance des deux frontières et `composed_width` leur même largeur. `singleton_of_connected` demande une source distinguée et la connexité ; `empty_image` traite le domaine vide.

La longueur de trace mesure les opérations de regroupement. La largeur mesure les obligations produites. L'image exhaustive énumère le domaine source ; la construction relationnelle par fragments utilise `rolewiseObligationFrontier`. Les égalités de largeur conservent cette différence entre producteurs. Les résultats donnent une borne sur les pas effectifs, avec les coûts propres aux procédures de choix et de composition laissés visibles dans leurs programmes.

## 4. Instance sur les histoires relationnelles

Les adaptateurs se trouvent dans `Migration/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/`. Leur espace de noms est `ConstitutiveSearch.EndogenousDecomposition.CertifiedRoleGrouping`.

`roleShape`, `encode`, `decode` et `code` établissent une correspondance réversible avec les profils natifs. La reconstruction conserve le rôle effectivement exécuté et son occurrence constituée. `GroupingReindex` transporte les règles binaires vers ce domaine, avec accords exacts sur les couples cible/témoin. Le reindexeur fourni part de règles dont les porteurs sont dans `Type 0` ; son domaine réindexé peut vivre dans un univers supérieur.

Pour chaque `RoleStatus.History` :

- un statut en attente conserve ses deux occurrences ;
- un transport présent autorise l'action orientée gauche vers droite ;
- les choix locaux et leurs raccords sont construits depuis la structure de l'histoire ;
- la mesure compte les positions autorisées encore à transformer dans le profil source.

`normal_selected` démontre que le normaliseur construit retrouve `History.selected`. La sélection existante intervient comme conclusion d'accord. `targetTransport` établit la correspondance réversible entre les anciennes obligations et les cibles stables génériques. `carry_fibres`, `projection_fibres` et `targetTransport_carry` conservent les portages et leurs identités. `composed_width` et `exhaustive_width` donnent :

\[
\mathrm{largeur}=2^{\mathrm{History.pendingCount}}.
\]

`pendingCount` compte les positions conservant deux obligations ; la mesure de normalisation compte les actions restantes d'un profil. Tous les statuts mixtes sont couverts avec leurs transports fournis.

La fermeture concrète utilise `RoleStatus.executed reduction`, dont les transports proviennent de `returnedTransport`. `stagewise_normal` réutilise `ofStagewise_eq_executed` pour identifier les licences produites. `executed_normal`, `executed_join`, `executed_path` et `executed_boundary` relient les profils au profil retenu de la réalisation. La frontière exécutée a une obligation. La caractérisation antérieure de la pleine largeur par la conservation séparée injective reste accessible dans `ConstitutiveExtensiveSeparation` et l'entrée publique migrée.

## 5. Données, transports et continuation

`Normative` fournit une famille de données indexées, un critère d'acceptation et l'action certifiée de chaque opération. `transport_preserves` conserve l'acceptation sur toute trace, pour toute donnée acceptée ; `transport_composes` donne l'accord point par point sur la composition.

Dans l'instance relationnelle, `codedAction` et `act` utilisent les transports attachés aux licences. `all_trace_acceptance` traite toute histoire, toute trace et toute donnée acceptée. `completed_trace`, dans `RoleGroupingSemantics.lean`, établit une conservation supplémentaire de la transformation complète. Il en découle :

| Déclaration | Quantificateurs et accord |
|---|---|
| `every_normalizing_trace` | Toute histoire, tout profil, toute trace vers sa sélection et toute donnée : transport = `History.transform`. |
| `normalization_coherent` | Deux traces vers cette sélection : égalité des transports sur chaque donnée. |
| `executed_trace_output` | Toute trace de normalisation dans une réalisation exécutée : les données canoniques donnent la cible opérationnelle effectivement retenue. |

Ces accords sont dérivés dans l'instance. Le contrat générique de normalisation porte sur les configurations ; `Normative.Coherent` exprime séparément une éventuelle cohérence de transport sur tous les couples d'extrémités. Le séparateur `equal_target_different_transport` conserve l'importance de cette loi supplémentaire.

`Continuation.Exact` reçoit deux pas totaux, leurs lectures, événements et admissions en `Type`. Il demande l'accord local des pas et les deux transports d'admission. `run_exact`, `events_exact`, `observations_exact`, `admitted` et `admittedSource` propagent ces accords sur toute liste finie d'entrées. Les observations de cette interface sont prises avant chaque pas. `stable` prouve la stabilité du prochain état projeté ; `run_append` et `events_append` ferment la composition des suffixes.

`Native.bridge`, dans `GroupingInstances.lean`, ferme ce contrat avec `forget`, `step`, `forget_step` et `forget_matches`. Sa source conserve l'exécution historique comme témoin de correspondance. Les producteurs réduits séparés `reducedNext`, `reducedEvent` et `reducedRead` utilisent uniquement la mémoire native, composée de `position` et `active`, avec l'entrée unité du pas déterministe. `all_finite` porte sur toutes les listes de telles entrées. `all_native_admissible` porte sur tous les suffixes du prédicat natif indépendant `HeterogeneousFeedback.Admissible`, depuis tout témoin `Execution` admis comme source. Cette admission détermine actuellement son suffixe depuis la source et sa longueur.

`all_new_certifications` ferme les évaluations nouvelles dans le support effectivement prolongé ; `references_compose` conserve les références typées à travers deux continuations. Les théorèmes existants de `FiniteRuleCoordinates` conservent les coordonnées, les opérateurs et les dépendances ordonnées pour les deux réalisations homogène et hétérogène, y compris lors des reprises. `forgotten_decision` réutilise le séparateur positif de mémoires égales et de décisions distinctes qui exclut un décodeur uniforme.

## 6. Prolongements historiques

`Extension` reçoit une inclusion et le transport de chaque ancienne opération vers une trace admise du contexte suivant. Les nouvelles autorisations peuvent ouvrir d'autres regroupements. `renormalized` prouve :

\[
N_{h'}(\iota(N_h(x)))=N_{h'}(\iota(x)).
\]

`obligation` normalise la cible transportée dans ce nouveau contexte. `obligation_composes` et `obligation_identity` prouvent les accords de composition et d'unité sur les obligations.

`Historical`, dans `HistoricalRoleGrouping.lean`, conserve les anciens rôles exécutés identiques. Son cas `suffix` reçoit un profil des occurrences nouvelles ; `same` conserve une autorisation ; `license` ajoute un transport à une ancienne position en attente ; `composed` conserve les deux prolongements construits. `embedding_injective` conserve les identités sources, `liftMove` transporte les opérations et `extension` ferme le contrat générique. `renormalized`, `embedding_composes` et `obligation_composes` donnent les accords natifs. `executedSuffix` fournit le profil nouveau depuis la réalisation retenue ; `returnedGrowth` ferme la nouvelle autorisation par la licence effectivement retournée.

## 7. Séparateurs et périmètre

Les fermetures des interfaces sont identifiables dans les constructions suivantes :

| Obligation | Données locales | Producteur | Conclusion dérivée | Fermeture concrète |
|---|---|---|---|---|
| Choix admis et terminalité | Positions, masque, profil | `Binary.choices`, `locate`, `Rules.reindex` | `normal_selected` | Histoire native, avec licences `returnedTransport` dans l'instance exécutée. |
| Raccords compatibles | Deux témoins `Binary.Move` | `Binary.diamond` | `confluence`, `executed_join` | Cas même position, deux positions et récursion sur l'histoire. |
| Image exacte | Porteur fini ; fragments d'obligations | `finiteSource`, `composed` | `exhaustive_width`, `targetTransport_carry` | `roleProfileFiniteCarrier`, `rolewiseObligationFrontier` et leurs preuves locales. |
| Conservation normative | Action de chaque licence | `codedAction`, `act`, `normative` | `all_trace_acceptance` | Transports du statut ; producteurs retournés dans le cas exécuté. |
| Accord des données | Actions locales sur les occurrences | `completed`, `liftCompleted` | `every_normalizing_trace`, `executed_trace_output` | `History.transform`, `canonicalAction_exact`. |
| Continuation exacte | Mémoire native, entrée unité, exécution source | `Native.bridge` | `all_native_admissible`, `all_new_certifications` | `forget_step`, `forget_matches` et l'admission native indépendante. |
| Prolongement des obligations | Profil nouveau et autorisations conservées ou ajoutées | `Historical.embedding`, `liftMove`, `extension` | `renormalized`, `obligation_composes` | `executedSuffix`, `returnedGrowth`. |
| Ressources historiques | Histoires admises et références typées | Constructeurs `FiniteRuleCoordinates` existants | Coordonnées, opérateurs et dépendances lors des reprises | Réalisations homogène et hétérogène, contrôlées par les tests de coordonnées V5. |

| Obligation examinée | Témoin ou test |
|---|---|
| Plusieurs choix compatibles simultanés | `real_peak`, raccord binaire à deux positions autorisées. |
| Lectures réunies et liens composés | `joint_injective`, `projections_each_separate`, `nevertheless_connected`. |
| Lecture actuelle et prochaine lecture | `current_equal_future_distinct`. |
| Raccord local nécessaire | `fork_no_join`, deux terminaux distincts d'une bifurcation. |
| Décroissance effective et actions neutres | `cycle_forbids_strict_rank`, `neutral_forbids_strict_rank`. |
| Cible commune et données transportées | `equal_target_different_transport`, deux actions étiquetées. |
| Admissions | `admissions_mismatch`. |
| Nouvelle licence historique | `new_license_requires_renormalization`. |
| Domaine vide et singleton habité | `empty_width`, `inhabited_width`. |
| Valeurs égales et références différentes | `RelationalFoundations.FiniteRuleCoordinatesTests.permuted_changes_identity`, rejet `ForgottenGlobalIdentityV1`. |
| Dépendances ordonnées et sortes | Rejets `ForgottenReorderedInputsV1`, `ForgottenWrongSortV1`. |
| Origine encodée ou rejouée | `Tests.HiddenEncoding`, `Tests.ForgettingAuditScope`, et séparateurs sémantiques de l'oubli natif. |
| Statuts comparés et réalisation | Contrat `RoleStatus.History` ; fermeture `returnedTransport` et `ofStagewise_eq_executed`. |

Les cinq nouveaux rejets attendus se trouvent dans `Tests/ExpectedFailures/CertifiedGrouping`. Ils ciblent l'égalité des sources, l'unicité des transports sans loi, la détermination du prochain état par la seule lecture actuelle, une action neutre considérée comme réduction stricte et l'absence de renormalisation historique.

La preuve générale porte sur toute instance de la classe locale explicitée. La famille relationnelle ferme les regroupements pluriels et les données normatives. L'adaptateur natif ferme la continuation exacte sur son interface déclarée. Les règles et admissions spécifiques gardent leur origine dans ces constructions. Les preuves portent sur des histoires et regroupements finis ; les confirmations exécutées exercent un domaine fini de test, décrit séparément dans les reçus V5.
