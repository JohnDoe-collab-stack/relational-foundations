# Achèvement du chantier indépendant

Ce bilan remplace les statuts provisoires de la revérification du 30 septembre. Le résultat livré comprend les fondations et une copie complète migrée du projet, dans `Migration`. Le basculement physique du dépôt original est exclu par la contrainte de conservation : ses sources, son HEAD et sa branche sont contrôlés, sans écriture.

## Points incomplets désormais traités

| Point du précédent rapport | Réalisation |
| --- | --- |
| Quantité circulaire équipée seulement concrète | `CircularSignature.circularQuantity` reçoit une présentation générique, avec univers distincts pour nœuds, pas et fermeture |
| Formation et provenance limitées aux préfixes intérieurs | Graphes de formation initiale, d’avancée arbitraire, de cible, de registre actuel et de registre préservé ; accords des transports sur ces graphes |
| Lois de transport insuffisamment exposées | Lois pointwise, existence réflexive/symétrique/transitive des transports équipés et marqués ; identité et composition des transports des fibres de réalisation |
| Invariance cardinale manquante | Preuve constructive de `Fin n ↔ Fin m → n = m`, puis invariance des quantités et histoires finitement cardinalisées |
| Spécification générique seulement abstraite | Spécification de clôture indépendante de l’admission, modèle canonique, classification, correction, complétude et rejet des extensions strictes |
| Spécification historique non reprise | Définitions et preuves riches migrées dans `Constitution.Specification`, `Regime` et `CoupledTurning` |
| Diagnostics uniformes non raccordés | Diagnostics abstraits migrés dans `RelationalFoundations.Diagnostics` et raccords dans `TurningDiagnostics` ; candidat fixé avant variation des implémentations |
| Migration des cinq entrées non effectuée | Façades et modules spécialisés dans la copie complète ; inventaire des 806 symboles publics déclarés et vérification de leurs noms et types exposés |
| Computation non rebranchée | Transports canoniques, histoires enracinées et itération utilisent le socle ; compilation des consommateurs et résultats publics conservés |

## Correspondance avec les phases de réalisation

| Phases du plan | Code ou contrôle principal |
| --- | --- |
| 5 — Référence et préservation | Empreintes, archive récupérable, différences Git et contrôle du dépôt initial |
| 6 — Contrat fondationnel | Architecture explicite, hypothèses séparées et modèles séparateurs |
| 7 — Outils et histoires | `ExactTransport`, `History`, `HistoryTransport`, `Residual` |
| 8 — Épine et places | `Spine`, `CompositionOrder` |
| 9 — Formation | `Generation`, `FormationAtOccurrence`, unicité pointwise du pli |
| 10 — Réalisation et rigidité | `ExactRealization`, `InteriorDelimitation`, contre-modèle de réalisation non rigide |
| 11 — Frontière et rôles | `Presentation`, singleton indexé, somme des branches et exclusions |
| 12 — Délimitation | Certificat intérieur produit par les preuves |
| 13 — Local et global | Conservation de précédence et adjacence ; modèles injectifs permuté et intercalé ; reconstruction spécialisée canonique migrée |
| 14 — Continuation et résidu | `Continuation`, `FaithfulContinuation`, extraction structurelle du pas depuis positivité et unicité |
| 15 — Frontière et obstruction | `BoundaryInterpretation`, `Obstructions`, couches périmétrales spécialisées |
| 16 — Régime et tournant constitutif affirmatif | `Regime`, `Turning`, `FaithfulTurning`, `CircularSpecification`, diagnostics et spécification historique migrée |
| 17 — Quantités et signature | `Quantity`, `FiberTransport`, `Signature`, `EquippedQuantity`, `MarkedQuantity`, `CircularSignature`, `TransportLaws` |
| 18 — Lectures | `Cardinalization`, `FiniteInvariance`, bornes et readouts spécialisés migrés |
| 19 — Instance périmétrale | Instance autonome, témoins multiples, modèle riche migré et vue générique de ses porteurs |
| 20 — Interprétations | `Interpretation`, oubli non fidèle, interprétations concrètes et diagnostics uniformes spécialisés migrés |
| 21 — Comparaison et migration | Pont historique, sources spécialisées réparties, façades, inventaire public et stratification |
| 22 — Raccord computationnel | Générateur commun, histoires causales constituées, contrôles ancien/frais et compilation complète des profils, obligations et largeurs |
| 23–24 — Preuves et contrôles | Audits exhaustifs, modèles positifs/négatifs, quatre frontières d’import, tests de rejet et inventaire public |

Les phases d’analyse, de méthode, de risques et de traçabilité restent conservées dans le plan. Elles n’ajoutent pas d’objets mathématiques à fabriquer. Leur fonction est de fixer les critères appliqués ci-dessus.

## Une seule chaîne scientifique dans la copie migrée

`ExactTypeTransport` est une adaptation du transport générique. Les consommateurs computationnels utilisent le nom canonique du type pour éviter les ambiguïtés de notation de champs liées aux aliases.

`SegmentedResidualRole` et `AbstractSegmentedTurning` exportent les définitions du socle. Ils ne réintroduisent pas de seconde définition du résidu ou des diagnostics.

`StrongPerimetralTurning` importe les modules spécialisés. Le namespace public historique est conservé pour les consommateurs ; ses définitions riches ont été réparties selon leurs responsabilités. L’histoire générique n’y est plus redéfinie. `RootedGeneratedHistory` est une spécialisation du type générique `RootedConstruction`, avec adaptations transparentes des projections.

`RelationalPerimeter` est la façade globale : elle expose le socle, les vues spécialisées et la computation. L’histoire de `CausalConstitutiveState` demeure un objet constitué entier, distinct de l’état opérationnel et de ses lectures.

Les preuves valides du modèle spécialisé ont été conservées. La migration apporte une nouvelle organisation et une autorité commune pour les outils génériques ; elle ne remplace pas les données riches de formation, différence, provenance, obstruction ou interprétation par un résumé numérique.

## Tournant constitutif affirmatif

L’expression retenue dans les documents est **tournant constitutif affirmatif**. Elle désigne la continuation effectivement engendrée, la conservation des données constitutives antérieures et la réalisation interprétée du rôle de frontière par la nouvelle occurrence. Le tournant avec sortie ajoute l’exclusion démontrée du régime antérieur. La [définition dans l’architecture](architecture-et-portee.fr.md#tournant-constitutif-affirmatif) distingue les données de génération, leur détermination résiduelle et les preuves de régime. Les noms publics Lean restent ceux du code vérifié.

## Hypothèses et limites intrinsèques des énoncés

La rigidité intérieure générique est démontrée pour la relation choisie, qui contient l’identité de l’occurrence distinguée. Le modèle périmétral riche conserve ses résultats plus forts de reconstruction canonique depuis les accords locaux. Ces deux portées sont distinctes.

La spécification générique reçoit une constitution locale sous forme d’un préfixe effectif. La spécification périmétrale spécialisée reçoit l’exactitude locale riche et reconstruit ce préfixe par ses théorèmes de canonicité. Elle ne suppose pas directement le résultat qu’elle doit produire.

La signature est commune aux présentations comparées. Ses transports conservent les graphes déclarés, les incidences et les marques. Les relevés d’univers sont réversibles ; ils n’oublient pas les témoins. Des relations qui ne font pas partie de la signature ne sont pas automatiquement préservées. Le changement arbitraire de signature et une métathéorie de toutes les opérations dépendantes restent hors de la première version prévue par le plan.

Les lois de transport sont pointwise. Aucune égalité globale de fonctions ni structure catégorique supplémentaire n’est nécessaire au résultat annoncé. L’unicité résiduelle est structurelle ; les bornes numériques et certains certificats de différence utilisent ensuite la lecture dérivée.

## Ce que vérifie l’inventaire public

`migration-symbols.csv` recense les types et résultats publics déclarés dans les quatre sources historiques, avec leur origine et leur cible. Le contrôle Lean vérifie que les anciens noms publics et les cibles sont typables dans le projet migré. Les constructeurs et projections sont aussi éprouvés par la recompilation des consommateurs.

Ce contrôle de disponibilité ne remplace pas une preuve de transport : les transports historiques de places, histoires et occurrences, leurs retours et les accords de réalisation sont démontrés séparément. Les données spécialisées conservées sont vérifiées dans leurs sources migrées ; l’inventaire ne prétend pas établir une équivalence non déclarée entre signatures différentes.

## Reproduction et résultats effectifs

Le contrôle global est `pwsh -NoProfile -File scripts/verify.ps1`. Il rassemble les résultats du socle, de la comparaison historique et de la copie migrée. Les comptes datés sont dans `docs/verification-result.json` et `Migration/verification-result.json`.

La vérification complète du 30 septembre 2026 a réussi : 40 sources du socle, 166 sources migrées, 806 symboles publics contrôlés, 11 résultats de comparaison et 24 rejets attendus. Les audits exhaustifs portent sur 2 712 déclarations du socle et 3 095 déclarations de la constitution spécialisée, sans dépendance axiomatique. Les 3 152 audits publics migrés, les quatre frontières d’import et la stratification des 150 modules de production passent également. Les 253 fichiers d’origine et leur archive de récupération sont vérifiés inchangés.

L’audit du socle parcourt toutes ses déclarations et celles des tests, y compris les auxiliaires et déclarations privées. L’audit spécialisé parcourt toutes les déclarations des modules `Constitution`, avec la même exigence d’absence de dépendance axiomatique. Les résultats computationnels conservent leurs audits publics et leurs tests de rejet historiques.

Une compilation réussie ne garantit pas à elle seule l’adéquation philosophique de toute théorie possible. Ici, les constructions, leur périmètre, les hypothèses, les contre-modèles et les raccords sont explicités pour permettre l’examen du travail livré.

## Intégration des exécutions récentes — 1er octobre 2026

La copie `Migration` intègre désormais `VariableRelationalExecution`, `VariableOutputComposition`, `AdaptiveRelationalExecution` et `UnboundedMixedExecution`, ainsi que leurs quatre suites de régression et les deux documents associés. L’entrée publique expose les résultats mixtes, adaptatifs et de longueur arbitraire. Le certificat de production conserve aussi le caractère local de la première opération pour toute longueur restante.

Les transports des nouveaux modules utilisent directement `RelationalFoundations.ExactTransport`. La génération automatique des lemmes d’injectivité est désactivée dans les modules concernés. La sélection des candidats utilise `List.foldr` avec des continuations différées ; les preuves de sélection sont rebranchées sur l’équation du pli. Les quatre suites de régression conservent leurs énoncés d’origine.

Le vérificateur migré audite exhaustivement les déclarations des quatre nouveaux modules et des deux modules computationnels mis à jour, y compris les auxiliaires et déclarations privées. Son reçu `recentComputationAudit` complète l’audit de la constitution spécialisée dans `Migration/verification-result.json`.

La vérification du 1er octobre a réussi : 174 sources migrées, 154 modules de production inventoriés, 806 symboles historiques disponibles et 3 400 reçus publics. L’audit des six modules computationnels concernés couvre 1 191 déclarations sans dépendance axiomatique. Le socle conserve ses 2 712 déclarations auditées et la constitution spécialisée ses 3 095. Les onze résultats de comparaison, les quatre frontières d’import et les 24 rejets attendus passent. Une compilation finale confirme que les sources présentes correspondent aux modules vérifiés.

La commande d’intégration est `pwsh -NoProfile -File scripts/verify.ps1 -SkipReference`. L’option concerne le contrôle d’identité du dépôt source avec le relevé historique du 30 septembre : ce dépôt a depuis reçu les ajouts à intégrer. Le socle, la comparaison historique, la compilation migrée, les inventaires publics, les frontières d’import et les tests de rejet restent contrôlés. L’archive et son relevé historiques sont conservés.
