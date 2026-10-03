# Portée des audits et identité des ressources — V4

Cette révision ferme trois obligations : décrire exactement ce que contrôlent les scanners, couvrir le paquet entier par ses empreintes, et démontrer l'accord des coordonnées des deux instances sur toutes leurs histoires admissibles. Les sources mathématiques et les preuves antérieures restent raccordées aux mêmes interfaces. Les versions V1 à V3 des scripts et leurs reçus constituent des références historiques conservées.

## 1. Ce qui établit l'oubli

`scripts/AuditForgettingV4.lean` contrôle les deux champs `position` et `active`, tous deux de type `Nat`. Il parcourt les types accessibles et les corps des définitions accessibles, puis vérifie l'absence des noms de sa liste de refus. Son résultat porte sur cette forme et cette liste. Le scanner emploie les outils Meta de Lean ; les théorèmes mathématiques qu'il inspecte subissent séparément l'audit des axiomes.

Deux champs naturels peuvent contenir davantage que leurs valeurs actives apparentes. `Tests/HiddenEncoding.lean` donne un encodage dont l'origine est récupérable. `Tests/ForgettingAuditScope.lean` ajoute un calcul qui reconstruit localement chaque état depuis une origine encodée, en utilisant une récursion structurelle et la transition locale `next`. Pour toute origine et toute profondeur finie :

- `replay_tracks` établit l'égalité de la projection avec l'exécution native ;
- `origin_recoverable` construit un décodeur correct de l'origine conservée ;
- `replay_separates` distingue deux mémoires dont les projections natives coïncident.

Ce calcul est accepté par le scanner V4. Son marqueur `REPLAY_V4_SYNTAX_ACCEPTED` consigne ce résultat de forme. Il constitue un séparateur général entre l'accord d'une projection et la perte effective des données dans sa mémoire source. Les contrôles exécutables parcourent les origines `0..12` et les profondeurs `0..24` ; la preuve quantifie sur tous les naturels.

L'oubli du constructeur natif repose sur ses propres théorèmes : `origin_irrecoverable_from_prefixes` et `first_decision_irrecoverable` excluent un décodeur correct sur les familles de préfixes déclarées. Les préfixes distincts donnent la même mémoire effacée. `colliding_prefixes_continue` démontre alors, pour toute profondeur, l'égalité de leurs exécutions et de leurs observations natives. Les garanties de continuation portent sur tous les suffixes finis admis dans l'interface native. Leur quantificateur reste relatif à cette interface et à ses lectures.

Le cas interdit `ForbiddenDependency.lean.fail` doit produire le diagnostic d'un nom refusé. `WrongShape.lean.fail` doit produire celui des champs supplémentaires. Ces rejets contrôlent le fonctionnement du scanner. Ils sont distincts du séparateur de reconstruction locale, accepté par ce même scanner.

## 2. Même domaine de fichiers sous Windows et Linux

`scripts/ValidationManifestV4.ps1` parcourt la racine entière avec `-Force`. Tous les fichiers ordinaires sont recensés : fichiers cachés, fichiers commençant par un point, sources supplémentaires à la racine, auxiliaires, logs ordinaires, documents, configurations et reçus historiques. Les exclusions exactes sont `.git`, `.lake`, `Migration/.lake` et `Comparison/.lake`. Les logs d'une nouvelle validation sont écrits dans ces caches ou dans son dossier externe de résultats.

Les sources et auxiliaires constituent les entrées `I4`. Les preuves courantes sous `docs/validation-v4` constituent le domaine séparé `E4`. Les chemins sont relatifs, normalisés avec `/`, triés ordinalement et associés à leur rôle, taille et SHA-256. Les liens du domaine scientifique et les collisions de casse sont rejetés. Le contrôleur compare le catalogue effectivement parcouru avec le catalogue figé ; un ajout, une suppression ou un changement de contenu provoque un désaccord.

L'index E4 lie le manifeste I4, les deux reçus et chaque fichier de preuve. Chaque reçu lie ses commandes, paramètres, sources de contrôles, codes de retour, diagnostics et sorties à I4. Tous les fichiers sous les deux dossiers de plateforme doivent aussi appartenir aux sorties déclarées par leur reçu. Les sources sont relues avant et après l'exécution. Le contrôle d'empreintes atteste l'identité des octets ; les compilations, preuves et essais attestent les résultats correspondants.

Les tests du catalogue contrôlent notamment les fichiers cachés, les logs, les auxiliaires, les tailles, les changements de même taille, les chemins invalides, les collisions et les liens. `test-validation-bundle-v4-r2.ps1` copie ensuite le véritable paquet complet et y attaque séparément sources, scripts, preuves historiques, reçus, sorties, liaisons et catalogue. Chaque modification a lieu dans la copie de test et le paquet initial est revérifié. Sous Windows, la création de deux noms ne différant que par la casse est empêchée par le système de fichiers ; le test de manifeste vérifie dans les deux environnements le rejet de ces noms concurrents.

Le domaine couvre aussi les archives et outils historiques présents dans la racine, en tant que matériaux référencés. Leur inclusion dans le manifeste ne les transforme pas en dépendances scientifiques : la validation actuelle omet explicitement `Comparison` et les accès au dossier original. La conservation des reçus V1/V2 est contrôlée dans une extraction dédiée de l'instantané Git `99f0801`. Les fichiers de preuve V3 sont eux-mêmes des entrées historiques de I4 ; leurs empreintes livrées restent conservées. Rejouer V3 demande son instantané V3, tandis que V4 décrit les nouvelles sources.

## 3. Accord général des coordonnées

`RelationalFoundations/FiniteRuleCoordinates.lean` dérive les lois des constructeurs déjà définis. Le contrat `Rules` reçoit toujours ses données et lois locales ; aucun champ contenant l'accord global des coordonnées n'est ajouté.

| Déclaration | Quantificateurs et conclusion |
|---|---|
| `homogeneous_native_coordinates` | Tout `Token : Type u`, tout sélecteur total, toute histoire admise depuis l'origine et toute demande : la coordonnée commune égale la coordonnée native de la demande correspondante, dans le même cadre construit. |
| `heterogeneous_native_coordinates` | Toute origine naturelle, toute histoire admise, toute sorte et toute demande typée : même accord sur la référence effective. |
| `homogeneous_coordinates`, `heterogeneous_coordinates` | Accord avec les constructeurs `complete` initiaux après le transport explicite entre leurs cadres égaux. |
| `homogeneous_inverse`, `heterogeneous_inverse` | Les applications inverses retrouvent les demandes communes correspondantes pour toute référence. |
| `homogeneous_operators`, `heterogeneous_operators` | Les opérateurs aux références ainsi identifiées sont ceux de l'instance native. |
| `homogeneous_dependencies`, `heterogeneous_dependencies` | Accord des listes de dépendances déclarées : ordre, places d'arguments et répétitions conservés. |
| `resumed_coordinates` | Toute réalisation antérieure issue de l'origine, tout suffixe admis : inclure une ancienne demande puis la coordonner égale coordonner puis transporter sa référence. |
| `homogeneous_resumed_coordinates`, `heterogeneous_resumed_coordinates` | Raccord de ce diagramme aux transports natifs pour toute réalisation antérieure, toute continuation admise et chaque référence ancienne des deux instances. |
| `resumed_composed_coordinates` | Même diagramme pour deux reprises effectives successives, avec les exécutions et les références intermédiaires conservées. |
| `liftRequests_append`, `composed_coordinates` | Inclusion compatible avec l'append des suffixes, après son égalité d'associativité ; diagramme pour les prolongements canoniques composés. |
| `resumed_operators`, `resumed_dependencies` | Conservation des opérateurs et de toutes leurs entrées ordonnées sur les références effectivement coordonnées pendant la reprise. |

La normalisation `realization_eq` compare les réalisations effectivement exécutées depuis l'origine pour une même histoire. Elle conserve l'exécution et son cadre, avec les casts dépendants nécessaires. Les accords portent sur les coordonnées de `complete`, `certify` et `resumeCompleteFrom`. Les coordonnées natives restent définies par les constructions initiales.

`Tests/FiniteRuleCoordinates.lean` consomme les énoncés généraux, un type de jeton dans un univers supérieur, les treize demandes de l'exemple homogène, les sept demandes typées de l'exemple hétérogène et une reprise effective. Il construit également `permuted`, une couverture cyclique à lecture constante qui permute deux ressources. `values_still_agree` conserve l'accord des valeurs ; `permuted_changes_identity` établit la différence des références. L'accord général démontré suit donc le constructeur déterminé ; les champs abstraits de `Coverage` seuls autorisent cette permutation.

Toutes les nouvelles constructions de données sont compilées par Lake. Les preuves mathématiques subissent l'audit exhaustif des axiomes, en plus des blocs terminaux nommant leurs déclarations principales. La fermeture reste celle d'histoires finies admises ; la terminaison d'un exécuteur sans horizon est une autre propriété.

## Reproduction

Lean est fixé à `leanprover/lean4:v4.33.1` et le protocole utilise PowerShell 7. Depuis un checkout Git complet contenant `99f0801` :

```powershell
pwsh -NoProfile -File scripts/check-validation-v4.ps1
pwsh -NoProfile -File scripts/test-validation-bundle-v4-coverage.ps1
pwsh -NoProfile -File scripts/verify-validation-v4.ps1 -FrozenManifest docs/validation-v4/inputs.json
```

Le protocole écrit dans un dossier neuf `.lake/validation-v4/<identifiant>` ou dans le `-OutputDirectory` neuf fourni. Les versions, commandes et nombres effectivement vérifiés figurent dans les reçus [Windows](validation-v4/Windows/receipt.json) et [Linux](validation-v4/Linux/receipt.json), reliés par l'[index](validation-v4/index.json) au [manifeste commun](validation-v4/inputs.json). Les totaux de sources et de déclarations sont dérivés de ce run. Les contrôles complets du paquet peuvent être rejoués avec `-OutputPath` pour conserver leur reçu propre.

La configuration GitHub Actions reproduit le protocole sur Windows et Ubuntu. Les reçus livrés distinguent les exécutions locales Windows et Linux sous WSL d'une exécution GitHub Actions. Une soumission à Aristotle est une action séparée.

Le complément versionné V4.1, scripts/test-validation-bundle-v4-coverage.ps1, reprend le test complet V4 et ajoute les caches autorisés, les scripts cachés, les sources visibles, les ajouts imbriqués, les renommages, les rôles et chemins du manifeste réel. Il vérifie aussi le rejet d'un reçu V3 substitué à V4 et celui d'une sortie indexée sans liaison au reçu. Les empreintes extérieures sont recalculées dans la copie pour atteindre ces contrôles internes. Les scripts V4 initiaux conservent leur version ; la confirmation finale désigne le manifeste qui inclut ce complément.
