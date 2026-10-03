# Validation portable V3

Le protocole `foundations-audit-validation-v3` valide les sources corrigées et conserve les références V1/V2. Il s’exécute avec Lean `4.33.1` et PowerShell 7 sur Windows et Linux, dans un checkout Git complet comprenant l’instantané public `99f0801e0f91b6821944f8a4a09dedf7810fdf14`.

## Exécuter et relire

Depuis la racine du checkout :

```powershell
pwsh -NoProfile -File scripts/verify-validation-v3.ps1
```

Le script crée un dossier neuf `.lake/validation-v3/<identifiant>`, même sur une copie sans `.lake`. Il refuse de remplacer un dossier de résultats existant. La comparaison avec le dossier historique original est explicitement omise ; les sources de la copie migrée sont entièrement compilées et contrôlées.

Pour relire le paquet livré :

```powershell
pwsh -NoProfile -File scripts/check-validation-v3.ps1
```

Pour reproduire exactement ses empreintes plutôt que créer un nouveau manifeste :

```powershell
pwsh -NoProfile -File scripts/verify-validation-v3.ps1 -FrozenManifest docs/validation-v3/inputs.json
```

## Manifestes et preuves d’exécution

Le [manifeste commun](validation-v3/inputs.json) recense les sources mathématiques, les tests positifs et fichiers de rejet, les scripts et auxiliaires des validations actuelle et historiques, les configurations Lake, les catalogues de migration, les documents et la configuration CI. Chaque entrée porte rôle, chemin relatif normalisé, taille en octets et SHA-256. Les reçus et sorties V3 sont exclus de leur propre manifeste pour éviter une dépendance circulaire d’empreintes. Les caches `.lake`, les logs intermédiaires, l’archive brute `reference` et les outils `Comparison` du dossier historique original sont hors de ce catalogue.

Les [reçus Windows](validation-v3/Windows/receipt.json) et [Linux](validation-v3/Linux/receipt.json) désignent les mêmes octets du manifeste. Ils donnent versions effectivement exécutées, paramètres, commandes complètes, codes de sortie et empreintes des sorties. Le paquet contient les sorties des contrôles ainsi que les logs complets de compilation, les inventaires publics et les rapports du socle et de la migration. Le contrôleur relit leurs empreintes et leurs diagnostics attendus.

L’[index livré](validation-v3/index.json) lie l’empreinte du manifeste aux empreintes des deux reçus. `test-validation-bundle-v3.ps1` accepte le paquet complet puis rejette quatre corruptions : reçu, manifeste, sortie du contrôle syntaxique/sémantique et log interne de compilation. Ces liaisons assurent la cohérence des octets livrés ; l’exécution reproductible du protocole établit les résultats.

Le commit de départ et la branche identifient le contexte Git de préparation. Les sources modifiées, y compris les fichiers nouveaux, sont identifiées par leurs empreintes ; le commit de départ désigne l’instantané initial, distinct du contenu corrigé. La livraison de ce chantier est préparée dans un worktree isolé.

Les scripts sont figés avant les exécutions de confirmation. Les mêmes empreintes sont vérifiées avant et après chaque exécution. Les versions antérieures des scripts et les sept fichiers de manifeste/reçus historiques restent inchangés. Le protocole extrait l’instantané Git `99f0801` dans son dossier neuf, puis y vérifie les 306 entrées du manifeste V2 et les liaisons de ses reçus. Les annotations documentaires corrigées sont propres au contenu V3 ; leurs versions originales restent dans cet instantané.

## Catalogue des contrôles

| Contrôle | Résultat exigé |
|---|---|
| Sources corrigées | Un bloc d’audit terminal par fichier créé/modifié ; scan des marqueurs interdits |
| Intégrité du manifeste | Association valide et neuf corruptions ou changements rejetés, notamment à longueur égale |
| Références historiques | 306 empreintes V2 raccordées à `99f0801`, sept manifestes/reçus conservés octet pour octet |
| Socle et migration | Compilation, audit exhaustif sans axiomes, 806 symboles publics, stratification et quatre frontières d’import |
| Exécution scalaire | Forme des champs et dépendances de 22 racines ; résultat explicitement syntaxique |
| Encodage caché | Le même contrôleur accepte 11 racines de l’exemple qui conserve l’origine ; sa récupération est prouvée |
| Témoins sémantiques | Sept déclarations vérifiées sans axiomes, couvrant collisions, pertes historiques, continuation et invariant |
| Contrôles exécutés | 325 cas de borne numérique, 21 cas d’encodage, visites cycliques et décisions historiques |
| Rejets Lean | Neuf du socle, dix-neuf de la migration, trois V1, un rejeu historique : 32 au total |

Les trois rejets V1 gardent leur nom historique. `ForgottenGlobalIdentityV1` contrôle l’indexation d’une preuve `Matches` par son préfixe ; `both_prefixes_match` établit positivement que chacun des deux préfixes possède sa propre correspondance. Les preuves de perte d’information sont `origin_irrecoverable_from_prefixes` et `first_decision_irrecoverable`.

Les paramètres des tests sont des listes finies explicites, enregistrées dans les reçus. Les théorèmes couvrent tous les nombres initiaux et toutes les histoires finies admises de leur classe ; les tests finis vérifient également l’exécution des procédures. Aucune graine aléatoire ni service distant n’intervient dans cette validation.

## Portabilité et CI

Les scripts de migration V3 normalisent les séparateurs avant les exclusions de `.lake`, `scripts` et `Tests`. Les scripts V1/V2 conservent leurs octets historiques et leurs contraintes de plateforme. La configuration CI comporte Windows et Ubuntu, avec cache désactivé et checkout complet ; elle relit le paquet livré puis produit des résultats neufs pour chaque plateforme.

La confirmation Linux locale utilise Ubuntu sous WSL avec le runtime Linux de Lean, des sources copiées dans un checkout Linux neuf et des artefacts reconstruits sur place. Les versions effectivement utilisées figurent dans les reçus. Ces vérifications locales et la configuration de CI ont des statuts distincts : l’exécution GitHub sera observée après publication.
