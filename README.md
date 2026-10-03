# Fondations relationnelles et projet migré

Le chantier est réalisé dans ce dossier indépendant. Il contient le socle générique et une copie complète du projet dont les cinq entrées fondamentales et les consommateurs computationnels sont migrés. Le dépôt `relational-perimeter` d’origine reste inchangé.

La chaîne formalisée relie les places inductives, les occurrences, la réalisation exacte, la frontière, le résidu, la continuation effective, la formation et la sortie de régime. Les quantités équipées conservent les fibres de réalisation, leurs témoins distingués et les graphes déclarés constitutifs. La cardinalisation vient ensuite.

Le **tournant constitutif affirmatif** est une continuation effectivement engendrée, qui conserve les données constitutives antérieures et dont la nouvelle occurrence réalise le rôle de frontière avec ses accords d’interprétation. Sa version avec sortie établit aussi que la construction prolongée quitte le régime antérieur. La [définition et ses raccords au code](docs/architecture-et-portee.fr.md#tournant-constitutif-affirmatif) précisent ces deux niveaux.

## Vérifier

Lean est fixé à `leanprover/lean4:v4.33.1`. La vérification utilise PowerShell 7 (`pwsh`). Aucun paquet Mathlib ni service externe n’est requis.

```powershell
pwsh -NoProfile -File scripts/verify-validation-v5.ps1
```

Cette commande crée son dossier de validation sur une copie fraîche. Elle fige les empreintes des entrées, construit et audite le socle et la copie migrée, contrôle les 806 symboles publics, la stratification et les quatre frontières d’import, puis vérifie les rejets du catalogue explicite. Elle contrôle séparément la syntaxe des producteurs, les preuves de perte d’information, les regroupements certifiés et les exécutions de test. Elle relit les reçus historiques sur les instantanés `99f0801` et `1887515`, disponibles dans un checkout Git complet. Chaque exécution produit de nouveaux reçus et sorties dans `.lake/validation-v5`.

Pour contrôler les sources et les preuves du socle et de la migration :

```powershell
pwsh -NoProfile -File scripts/verify-v5.ps1 -SkipComparison -SkipReference
```

Pour construire ou vérifier uniquement la bibliothèque générique :

```powershell
lake build
pwsh -NoProfile -File scripts/verify-v5.ps1 -SkipComparison -SkipReference -SkipMigration
```

La compilation du projet computationnel complet peut prendre plusieurs minutes. Ses sources sont dans `Migration`; son unique dépendance est ce socle, par chemin local `..`. La [validation V5](docs/validation-v5.fr.md) décrit les regroupements certifiés, le catalogue exhaustif et les contrôles Windows/Linux : `pwsh -NoProfile -File scripts/check-validation-v5.ps1`. Les scripts et reçus V1 à V4 restent des références historiques ; les comparaisons avec le dossier original relèvent de l’ancien protocole `scripts/verify.ps1`.

## Résultats et traçabilité

- [Regroupements certifiés, projections et continuation](docs/regroupements-certifies.fr.md) ([English](docs/regroupements-certifies.en.md)) : normaliseur local exécutable, convergence, distinction entre lectures réunies et identifications composées, instances relationnelle et native fermées, conservation des données et composition historique. [Validation V5](docs/validation-v5.fr.md).
- [Construction et fermeture des supports historiques](docs/fermeture-support-historique.fr.md) : fermeture générale sous conditions explicites, demandes issues des résultats précédents, conservation lors des prolongements et famille complète de producteurs locaux.
- [Calcul, sortie et réemploi historique](docs/calcul-sortie-reemploi-historique.fr.md) : couverture exacte des histoires admissibles indépendamment définies, réalisation de toutes leurs obligations, réemploi par adresse, conservation et composition du support, garantie terminale extraite.
- [Calcul hétérogène et réemploi historique typé](docs/calcul-heterogene-historique.fr.md) : ressources numériques et booléennes, décisions issues des résultats, références portant leur sorte, réalisation complète et continuation depuis le support existant.
- [Construction commune des calculs à fragments finis](docs/construction-commune-fragments-finis.fr.md) : classe de règles à lois locales, constructeur général, conservation et composition, avec les deux réalisations comme instances effectivement fermées.
- [Exécution réduite et restitution historique exacte](docs/execution-reduite-restitution-exacte.fr.md) : calcul effectif depuis les valeurs actives, weakening du cache, restitution complète, continuations certifiées et réduction matérielle démontrée dans un coût explicite.
- [Oubli historique certifié pour les continuations natives — V1](docs/oubli-certifie-continuations-natives-v1.fr.md) : mémoire position/actif, références typées et nouvelles évaluations certifiées pour tous les suffixes natifs admis, avec un séparateur historique effectif. Protocole dédié : `scripts/verify-forgetting-v1.ps1` ; [reçu V1](docs/verification-forgetting-v1.json) et [migration V1](Migration/verification-forgetting-v1.json), séparés des reçus de référence.
- [Validation avec manifeste — V2 historique](docs/validation-oubli-natif-v2.fr.md) : empreintes et reçus de l’instantané public `99f0801`, conservés tels quels. Le protocole V3 vérifie leur liaison dans une extraction dédiée de cet instantané.
- [Corrections et preuves complémentaires — V3](docs/audit-corrections-v3.fr.md) : couverture des parcours finis avec cycles, portée déterministe, invariant effectif, perte de la première décision et test d’encodage caché.
- [Validation portable — V3](docs/validation-v3.fr.md) : manifeste commun, reçus Windows/Linux, commandes et sorties vérifiables, avec conservation des références historiques.
- [Portée des audits et identité des ressources — V4](docs/audit-corrections-v4.fr.md) ([English](docs/audit-corrections-v4.en.md)) : reconstruction locale acceptée par le scanner, catalogue exhaustif des octets et accord général des coordonnées avec reprises et dépendances ordonnées.
- [Bilan du chantier](docs/achevement.fr.md) : réalisations, raccords, périmètre et correspondance avec le plan.
- [Rapport global](docs/verification-result.json) et [rapport de migration](Migration/verification-result.json) : résultats effectifs datés.
- [Inventaire des symboles](docs/migration-symbols.csv) : les 806 symboles publics déclarés dans les quatre anciennes sources, leurs cibles et le type de raccord.
- [Architecture](docs/architecture-et-portee.fr.md) : hypothèses et sens des énoncés.
- [Texte conceptuel](docs/conceptual-source.fr.md) et [plan](docs/reconstruction-plan.fr.md) : références conservées.

## Entrées de code

`RelationalFoundations.lean` expose les fondations génériques. `CircularSignature.lean` construit une quantité circulaire équipée pour une présentation quelconque, avec des sortes relevées réversiblement pour respecter les univers. Ses graphes couvrent aussi les constructeurs de formations arbitraires et les registres actuels ou préservés.

`CircularSpecification.lean` définit une obligation de clôture indépendante de l’admission. `TransportLaws.lean` démontre notamment l’identité et la composition des transports de fibres. `FiniteInvariance.lean` prouve constructivement l’invariance des cardinalisations finies. `TurningDiagnostics.lean` conserve le candidat dans les diagnostics uniformes sur les implémentations.

`Migration/RelationalPerimeter.lean` expose le projet complet migré. Les quatre anciennes entrées mathématiques servent de façades. Les définitions spécialisées sont réparties dans `Migration/Constitution`; les outils neutres, histoires, résidus et diagnostics abstraits ont une seule autorité dans le socle générique. Le générateur computationnel utilise son itération et son transport ancien/frais. L’état causal conserve l’histoire constituée entière.

`Migration/Constitution/GenericCircularView.lean` raccorde les porteurs primitifs riches à la quantité générique et les formations effectives à leurs histoires et registres. Les contrôles de ce raccord sont dans `Migration/Tests/FoundationMigration.lean`.

## Portée mathématique

Les résultats conservent leurs hypothèses : une réalisation distinguée n’implique pas la rigidité, une frontière ne produit pas son témoin, et une jonction positive ne fournit pas une admission de régime. L’interface intérieure choisit une relation identifiant l’occurrence distinguée. Le modèle historique spécialisé conserve, en plus, ses preuves de reconstruction depuis l’exactitude locale et son générateur canonique.

Une équivalence constitutive est relative à la signature commune déclarée. Les graphes retenus et leurs témoins sont préservés; aucun changement arbitraire de signature ni aucune égalité globale de fonctions ne sont annoncés. La lecture numérique seule oublie la constitution.

Les constructions et preuves spécialisées valides ont été conservées et migrées. L’archive `reference/source.zip`, les empreintes et les différences Git enregistrées préservent aussi les modifications préexistantes. Le chantier n’a pas remplacé le dossier original : la version migrée, compilable et vérifiable, est livrée séparément conformément à la contrainte de conservation.
