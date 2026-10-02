# Relational Foundations : dépôt autonome de publication

Ce dépôt rassemble le socle relationnel constructif, le projet computationnel migré, le constructeur commun de fragments finis, l'exécution réduite avec restitution historique et l'oubli certifié relativement aux continuations natives. Les sources, tests, documentations, archives et reçus acquis sont livrés ensemble.

Le dépôt est accessible à [JohnDoe-collab-stack/relational-foundations](https://github.com/JohnDoe-collab-stack/relational-foundations). Le développement d'origine demeure dans [relational-perimeter](https://github.com/JohnDoe-collab-stack/relational-perimeter).

## Récupérer et vérifier

Les outils requis sont Git, Lean via Elan et PowerShell 7. Le fichier `lean-toolchain` fixe Lean à `leanprover/lean4:v4.33.1`.

```powershell
git clone https://github.com/JohnDoe-collab-stack/relational-foundations.git
cd relational-foundations
pwsh -NoProfile -File scripts/check-forgetting-v2.ps1
New-Item -ItemType Directory -Path .lake -Force | Out-Null
pwsh -NoProfile -File scripts/verify-forgetting-v2.ps1
```

La première vérification contrôle les empreintes des 306 fichiers associés aux reçus livrés. La seconde compile le projet, audite les déclarations et les producteurs, exécute les rejets attendus et produit une nouvelle validation dans la copie locale.

La création de `.lake` prépare le dossier des journaux avant la première exécution du protocole V2.

## Lire les résultats

- [Présentation et entrées du projet](../README.md)
- [Constructeur commun et deux instances fermées](construction-commune-fragments-finis.fr.md)
- [Exécution réduite et restitution historique exacte](execution-reduite-restitution-exacte.fr.md)
- [Oubli certifié et son séparateur](oubli-certifie-continuations-natives-v1.fr.md)
- [Traçabilité V2 des preuves, sources et scripts](validation-oubli-natif-v2.fr.md)

Les [sources génériques](../RelationalFoundations) et les [sources migrées](../Migration) sont compilables ensemble. Le périmètre et les quantificateurs des résultats sont précisés dans leurs rapports respectifs.

## Validation automatique

Le workflow [Certified Lean validation](../.github/workflows/validate.yml) s'exécute sur les envois vers `main`, les pull requests et les déclenchements manuels. Il vérifie d'abord le manifeste livré, installe le toolchain déclaré, puis exécute la validation complète. Les nouveaux reçus et diagnostics sont conservés comme artefacts GitHub Actions.

Les actions utilisées sont fixées par leur commit. Les attributs Git de cette publication préservent les octets couverts par les empreintes, notamment les fins de ligne des sources et des anciens reçus.

## Origine de cette livraison

Les quatre reçus acquis et le manifeste V2 proviennent du dossier de travail isolé au commit de départ `0edc6135ce7cb3a8f0402328a19c6425b8621508`. Le manifeste identifie aussi les fichiers qui étaient alors nouveaux ou modifiés. La publication conserve leurs contenus exacts ; son historique Git débute par un instantané de livraison.

La [licence Apache 2.0](../LICENSE) et la [déclaration d'origine des idées et de production par les modèles](../AI_AUTHORSHIP.md) sont conservées.
