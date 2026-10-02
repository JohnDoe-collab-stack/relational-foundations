# Validation V2 : liaison des preuves aux sources et aux scripts

## Résultat concerné

Cette livraison complète la traçabilité de l'[oubli historique certifié V1](oubli-certifie-continuations-natives-v1.fr.md). Les quatre modules mathématiques V1, l'admission native, les deux contrats et leurs preuves sont conservés. V2 désigne le protocole de validation avec manifeste ; le résultat mathématique reste celui de `NativeForgettingV1`.

Les reçus V1 conservent leur contenu et leur date. La validation V2 exécute à nouveau les contrôles dans le dossier isolé et crée ses propres fichiers de livraison.

## Ce qui est lié

Le [manifeste V2](manifest-forgetting-v2.json) associe à chaque fichier son chemin relatif, son rôle, sa longueur en octets et son empreinte SHA-256. Il couvre :

- toutes les sources Lean du socle, de ses tests et de la migration ;
- tous les fichiers de rejet attendus de ces développements ;
- les scripts exécutés pour la compilation, les audits, les catalogues et les frontières d'import, ainsi que leurs fonctions auxiliaires ;
- les configurations Lake, les toolchains déclarées et les manifestes de dépendances ;
- les catalogues de stratification, de frontières d'import, de rejets et de symboles publics ;
- les quatre reçus acquis, le protocole V1 et les documents de livraison concernés.

Les fichiers modifiés et nouveaux sont inclus par leur contenu effectif. Le manifeste enregistre aussi la branche et le commit de départ ; les empreintes identifient les contenus au-delà de cet état Git.

Le [reçu principal V2](verification-forgetting-v2.json) contient l'empreinte du manifeste, les résultats des contrôles et le relevé des étapes exécutées : fichier, arguments, code de sortie et empreinte de la sortie capturée. Il contient également l'empreinte du [reçu de migration V2](../Migration/verification-forgetting-v2.json). Ce dernier désigne le même manifeste.

L'association durable suit donc la chaîne :

```text
contenus des sources, scripts et configurations
→ empreintes du manifeste
→ empreinte du manifeste dans les deux reçus V2
→ empreinte du reçu de migration dans le reçu principal
```

## Contrôles avant et après l'exécution

[verify-forgetting-v2.ps1](../scripts/verify-forgetting-v2.ps1) établit le manifeste avant les vérifications, contrôle son catalogue et ses empreintes, puis exécute le socle, la migration, l'audit des producteurs V1 et les trois rejets propres à l'oubli.

Avant de publier un statut `PASSED`, il contrôle de nouveau les contenus et l'ensemble des chemins. Un fichier modifié, ajouté ou manquant invalide la validation. Les quatre anciens reçus sont compris dans ce contrôle. Les sorties sont écrites dans des emplacements V2 distincts.

Le [contrôle du paquet sauvegardé](../scripts/check-forgetting-v2.ps1) relit les fichiers livrés. Il exige l'accord entre le contenu actuel, le manifeste et les deux reçus ; il vérifie aussi la conservation des quatre reçus acquis et l'association des comptes de sources aux fichiers recensés. Cette commande permet d'examiner ultérieurement la livraison sans lancer une nouvelle compilation.

## Tests de l'intégrité

[test-validation-manifest-v2.ps1](../scripts/test-validation-manifest-v2.ps1) vérifie une association valide, puis neuf rejets : changement d'une source à longueur égale, changement d'un script à longueur égale, fichier manquant, catalogue augmenté, catalogue réduit, chemin dupliqué, chemin sortant du dossier, rôle changé et manifeste dont l'empreinte diffère du reçu.

Ces essais utilisent un dossier temporaire dédié. Ils éprouvent la liaison documentaire ; les 31 rejets Lean continuent de contrôler les obligations mathématiques et leurs frontières.

## Commandes reproductibles

Pour exécuter la validation complète et produire les nouveaux reçus :

```powershell
pwsh -NoProfile -File scripts/verify-forgetting-v2.ps1
```

Pour contrôler les contenus et l'association des fichiers déjà livrés :

```powershell
pwsh -NoProfile -File scripts/check-forgetting-v2.ps1
```

Les reçus précisent les dates et les résultats effectivement obtenus. Le périmètre mathématique reste les continuations finies indépendamment admises par les trois règles natives déterministes. La vérification autonome écarte explicitement la comparaison et le contrôle du dossier original ; elle conserve la vérification complète de la copie migrée.

V2 apporte une liaison vérifiable entre une exécution de validation et son ensemble exact de fichiers. Une nouvelle modification de ces fichiers appelle une nouvelle validation. Le manifeste et les reçus conservent la trace du contenu auquel leurs résultats se rapportent.

Ce chantier demeure dans son dossier isolé, sans commit, push ou merge.
