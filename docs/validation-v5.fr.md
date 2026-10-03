# Reproduction des regroupements certifiés — V5

Le protocole V5 vérifie le nouvel état décrit dans [Regroupements certifiés, projections et continuation](regroupements-certifies.fr.md). Les scripts, manifestes et preuves d'exécution V1 à V4 gardent leurs octets et leurs états scientifiques respectifs. [English](validation-v5.en.md).

## Reproduction

Utiliser Lean `leanprover/lean4:v4.33.1`, PowerShell 7 et un checkout Git complet contenant les instantanés historiques `99f0801` et `1887515`.

```powershell
pwsh -NoProfile -File scripts/check-validation-v5.ps1
pwsh -NoProfile -File scripts/test-validation-bundle-v5.ps1
pwsh -NoProfile -File scripts/verify-validation-v5.ps1 -FrozenManifest docs/validation-v5/inputs.json
```

Le contrôleur crée un dossier neuf `.lake/validation-v5/<identifiant>`. `-OutputDirectory` accepte un nouveau dossier extérieur. Il rejette un dossier de sortie existant. Sans `-FrozenManifest`, il fige les entrées actuelles de cette nouvelle exécution. Pour reproduire les résultats livrés, utiliser le manifeste livré.

## Contrôles

Les 19 gates vérifient les blocs d'audit terminaux, le catalogue d'entrées, les reçus historiques, la compilation et les audits du socle et de la migration, les producteurs de l'oubli, les coordonnées, les contrôles exécutables, les huit rejets de types natifs et de regroupement, ainsi que les deux rejets du scanner. Les rejets historiques du socle et de la migration sont aussi exécutés dans leurs catalogues dédiés. Le total de rejets, les nombres de sources et de déclarations sont dérivés des sorties effectives.

`check-grouping-v5.ps1` ajoute une matrice de 5 461 couples masque/profil pour les dimensions `0..6`. Chaque cas vérifie la cible et la borne sur les pas du normaliseur. Les preuves paramétrées couvrent toutes les dimensions. La gate compile les consommateurs généraux de la migration, audite ses déclarations mathématiques importées, scanne les dépendances réelles des trois producteurs réduits natifs et enregistre les empreintes des 13 modules C générés. Les audits métaprogrammés ont leur propre portée ; les preuves mathématiques et les séparateurs sémantiques restent vérifiés séparément.

L'audit migré inventorie séparément les anciens auxiliaires automatiques `.injEq`, `.congr_simp`, `.eq_def` et les instances d'affichage `instRepr` portant une dépendance axiomatique. Leurs noms et dépendances figurent intégralement dans son journal. Cette exception concerne uniquement les anciens modules computationnels. Toutes les déclarations des modules nouveaux, les déclarations écrites du domaine historique et les tests gardent le contrôle transitif complet : une preuve utilisant l'un de ces auxiliaires est rejetée. Le succès concerne ce périmètre mathématique explicite ; les auxiliaires inventoriés conservent leur statut distinct.

Les scripts de stratification V5 classent les adaptateurs nouveaux dans leurs niveaux explicites. Les inventaires et règles V3 historiques restent conservés. Les 806 anciennes cibles publiques et les quatre frontières d'import sont contrôlées.

## Liaison des résultats

`ValidationManifestV5.ps1` catalogue exhaustivement le dossier, y compris les fichiers cachés et auxiliaires. Les exclusions sont `.git`, `.lake`, `Migration/.lake` et `Comparison/.lake`. Les preuves historiques sont des entrées ; `docs/validation-v5` porte les preuves actuelles. Les chemins relatifs normalisés, tailles, rôles et SHA-256 sont vérifiés avant et après chaque exécution. Le manifeste décrit les contenus complets, y compris les sources modifiées depuis le commit de base.

Le [manifeste commun](validation-v5/inputs.json) lie les reçus [Windows](validation-v5/Windows/receipt.json) et [Linux](validation-v5/Linux/receipt.json) par l'[index](validation-v5/index.json). Chaque reçu lie les commandes complètes, paramètres, versions, codes de sortie, diagnostics et empreintes de ses sorties. Les sources temporaires d'audit générées sont incluses parmi ces sorties liées. Les deux confirmations utilisent les mêmes octets d'entrée dans des environnements séparés. Linux est exécuté nativement dans Ubuntu sous WSL, avec son propre système de fichiers et ses caches.

`test-validation-bundle-v5.ps1` copie le paquet complet puis attaque ses sources, scripts, reçus, sorties, historiques, chemins et liaisons. Il vérifie aussi les modifications de même taille et les sorties indexées sans liaison au reçu. Les tests s'exécutent dans une copie indépendante ; le paquet original est revérifié. Les diagnostics et totaux des confirmations figurent dans les [tests Windows](validation-v5/Windows-bundle-tests.json) et [tests Linux](validation-v5/Linux-bundle-tests.json), indexés avec les autres preuves. Les runs de développement et leurs échecs sont conservés hors du paquet livré.

La configuration GitHub Actions rejoue ce protocole sur Windows et Ubuntu. Les confirmations livrées sont des exécutions locales. L'intégration Git et un audit externe constituent des actions distinctes.
