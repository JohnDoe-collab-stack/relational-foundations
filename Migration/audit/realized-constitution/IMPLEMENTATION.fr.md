# Correction des occurrences réalisées et de leur interprétation

## 1. Livraison et révisions

Cette livraison implémente une correction ciblée de la constitution des occurrences et de l'interprétation de leurs continuations. Elle contient du code de production compilé, des régressions et des sondes de dépendance exécutées. Elle ne constitue pas l'achèvement de toutes les corrections possibles ni une certification intégrale du protocole scientifique A–J.

| Référence | Valeur |
| --- | --- |
| Dépôt | `JohnDoe-collab-stack/relational-perimeter` |
| Base immuable | `5617ab4b09e5c0c044645737acd62973457b9a59` |
| Parent vérifié de cette base | `ea5a0e6aa91dab1c763c870e6e825a8581721f78` |
| Commit contenant les trois modules corrigés et la régression | `ef9e87bc8989b6bd45c782a94aa7e90d6dab60ab` |
| Branche de travail isolée | `chatgpt/realized-constitution-implementation-20260929` |
| Pull request | `#1`, en brouillon, non fusionnée |
| Compilation et vérifications | GitHub Actions, exécution `36555088170` |
| Sondes de dépendance | GitHub Actions, exécution `36557776322` |
| Révision examinée par les sondes | `b74e63feae546da906de74a19752e0c37cff1827` |
| Compilateur | Lean `4.33.1`, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |

Les actions ont utilisé des clones avec l'historique Git, contrôlé l'ascendance et installé la distribution officielle correspondant à `lean-toolchain`. Le condensat SHA-256 de l'archive a été vérifié contre celui publié pour la distribution. Le fichier `toolchain.txt` conserve ce condensat.

La seconde exécution a vérifié, avant et après les sondes, l'absence de différence dans les sources de production et les tests par rapport à `ef9e87b`. Les commits ultérieurs de cette livraison ajoutent l'infrastructure de vérification, ses résultats et ce document ; ils ne remplacent pas silencieusement le code compilé.

`main` n'a pas été modifiée par cette livraison. Sa référence a été relue à `8a5e494e9ac2ee725ff9fdb03dfe08c8b1b30685`.

## 2. Correction du porteur : réaliser avant de compter

Fichier : `RelationalPerimeter/Computation/ConstitutiveSearch/RelationalProfileConstitution.lean`.

L'ancien constructeur d'identité recevait une position et permettait une correspondance entre profils de positions et profils d'identités dont les lois de retour n'utilisaient pas directement les lois de réalisation de l'étape.

Le nouveau `RelationallyConstitutedOccurrence stage` contient l'occurrence effectivement réalisée dans `stage.Occurrence`. Il porte aussi les témoins de source, formation, cible et provenance de cette occurrence. Chaque témoin est relié par une égalité au témoin canonique de l'étape.

Cette précision est nécessaire : les familles relationnelles de l'interface sont à valeurs dans `Type`. Ajouter leurs témoins librement au porteur aurait pu introduire une multiplicité nouvelle. La correction n'assume pas leur unicité générale ; elle conserve explicitement les témoins canoniques de l'étape dans l'identité qu'elle construit.

La construction suit désormais :

```text
position
  → stage.realize position
  → occurrence réalisée accompagnée de ses témoins canoniques
```

La classification récupère la position par `stage.classify identity.realized`. Les lois `relationallyConstitutedOccurrence_position` et `relationallyConstitutedOccurrence_roundTrip` utilisent respectivement `classify_realize` et `realize_classify`. La reconstitution utilise les accords canoniques des témoins.

`constitutedOccurrenceTransport` relie exactement le porteur des réalisations internes au porteur constitué. Ce transport local n'est pas un adaptateur interposé entre plusieurs porteurs publics : les profils de l'histoire, le régime public et la spécialisation publique du théorème binaire continuent à employer le même porteur constitué.

Les preuves de retour des profils, de complétude de la frontière, d'absence de doublons et d'égalité décidable ont été adaptées. La lecture de largeur demeure en aval de ces constructions.

## 3. Correction de l'élimination : transporter entre deux fibres

Fichiers : `EndogenousDecomposition/RoleIndexedProfiles.lean` et `EndogenousDecomposition/RoleIndexedProgram.lean`, sous le même répertoire `ConstitutiveSearch`.

L'éliminateur antérieur recevait déjà un terme `constituted : Result`, déstructurait les témoins puis retournait ce terme. Il a été supprimé, et non conservé sous une signature équivalente.

Son remplacement, `RoleConstitutionEvidence.transportFormation`, reçoit une valeur dans une fibre indexée par l'état effectivement réalisé :

```lean
value : Motive identity.realized.state
```

Il produit une valeur dans la fibre de la position historique :

```lean
Motive (identity.position.state role)
```

Le passage utilise l'égalité portée par le témoin de formation. Renvoyer directement `value` ne suffit plus à typer cette fonction pour une occurrence arbitraire.

`RoleOpeningPayload occurrence` est maintenant le type des continuations de `occurrence.realized.state`. L'interpréteur transporte cette continuation vers sa position historique, puis applique l'action reconstruite dans le cas transformé ou conserve la continuation dans le cas retenu. L'action totale reste distincte du théorème de préservation de l'acceptation.

L'éliminateur dépendant `eliminateRoleConstitutedOccurrence` utilise le retour exact de l'occurrence réalisée. La construction des données canoniques des profils et la preuve d'interprétation ont été réécrites en conséquence.

Cette correction établit une utilisation typée de l'accord de formation. Elle n'établit pas que chacune des copies de cet accord est indispensable indépendamment des autres copies disponibles dans l'architecture. Elle ne prétend pas non plus que les quatre témoins modifient chacun la valeur calculée par l'action locale.

## 4. Résultats existants préservés et tests ajoutés

Le test `Tests/RealizedConstitutionRegression.lean` utilise une réalisation booléenne non identitaire : une position `false` réalise une occurrence `true`, et la classification retrouve `false`. Cela permet de distinguer concrètement position et valeur réalisée.

Il vérifie aussi les accords des quatre témoins, les égalités définitionnelles du porteur public, la largeur un du régime exécuté et la spécialisation publique de l'équivalence entre largeur exactement `2 ^ (input + 1)` et injectivité de `carry`.

Les régressions déjà présentes ont été conservées. Les fichiers de production définissant l'exécution causale, les décisions, la normalisation et le régime n'ont pas été remaniés dans ce lot. Leurs résultats publics sont préservés par la compilation et les régressions, sans que cela constitue une nouvelle vérification exhaustive de toutes leurs dépendances causales.

## 5. Vérification réellement exécutée

Source du relevé : `verification.json`. Tous les contrôles ci-dessous ont terminé avec un code de sortie nul.

| Commande | Résultat |
| --- | --- |
| `lean --version` | Version épinglée confirmée |
| `lake clean` | Réussi |
| `lake build +RelationalPerimeter` | Réussi, 127 tâches |
| `lake build` | Réussi, 136 tâches |
| `bash scripts/verify.sh` | Réussi, 134 fichiers Lean vérifiés |
| `pwsh -NoProfile -File scripts/verify.ps1` | Réussi |
| `git diff --check` | Réussi |

Les scripts du dépôt n'ont pas été affaiblis pour obtenir ces résultats. Leurs contrôles d'importation, de stratification, des exemples devant échouer, des blocs finaux `AXIOM_AUDIT`, des constructions interdites et des sorties de compilation ont été exécutés.

Le tableau JSON contient aussi certaines lignes informatives dont les noms de théorèmes comportent le mot anglais `failed`. Ce filtre lexical ne transforme pas ces lignes en erreurs : les codes de sortie et les diagnostics explicites font autorité.

Ces contrôles ne doivent pas être assimilés à une nouvelle inspection indépendante de toutes les déclarations produites par le compilateur. Les sorties d'audit présentes dans les modules et les contrôles des scripts ont été vérifiées ; l'extension exhaustive demandée au point J du protocole n'a pas été réalisée séparément.

## 6. Sondes de dépendance effectivement exécutées

Source du relevé : `dependency-probes.json`. Les modifications exactes sont conservées dans `patches/`. Les journaux complets sont joints à l'artefact de l'exécution `36557776322`.

| Sonde | Résultat observé | Portée |
| --- | --- | --- |
| `CoreControl` | Compilation réussie | Contrôle positif du module générique inchangé dans le même dispositif |
| `RoleControl` | Compilation réussie | Contrôle positif du module des rôles inchangé |
| `FormationTransportIgnored` | Rejet, `Type mismatch` | L'entrée indexée par l'état réalisé ne peut pas être renvoyée directement dans la fibre de la position |
| `RealizationReturnLawIgnored` | Rejet de `rfl` | La loi de retour n'est plus une simple réflexivité de la copie d'une position |
| `RawFormationErased` | Rejet de la preuve de retour | La suppression du champ intrinsèque de formation et de son argument de construction perd l'exactitude entre état réalisé et position |
| `FormationRecoveredFromRealization` | Compilation réussie | Le même accord peut être récupéré depuis `identity.realized.formedAt` ; cette récupération conserve la relation au lieu de l'effacer |

Les trois rejets sont des erreurs de typage ou de preuve. Ils ne reposent pas sur un constructeur privé introuvable, un nom de test supprimé, un avertissement de variable inutilisée ou un dépassement de temps.

Les éventuelles mentions de `sorryAx` dans les journaux des copies rejetées suivent les erreurs d'élaboration de ces copies. Elles ne correspondent pas à un ajout dans la source livrée ni à une compilation acceptée de ces mutations.

Ces sondes compilent des copies temporaires de modules avec leurs dépendances vérifiées. Elles ne constituent pas les mutations cohérentes de tout le dépôt, avec nettoyage et exécution des deux scripts pour chaque mutation, exigées par le protocole A–J.

## 7. Limites restant ouvertes dans cette livraison

La correction de la réalisation, du porteur et du transport de formation est implémentée et compilée. Les exigences plus larges ne sont pas déclarées acquises par simple conséquence.

En particulier, l'effacement cohérent de chacune des quatre familles relationnelles sur toute la chaîne publique reste à examiner. Le code livre désormais des témoins canoniques portés par les identités et une utilisation substantielle de la formation dans l'interpréteur ; il ne démontre pas encore l'indispensabilité autonome de chaque famille pour chaque conclusion publique.

La production préfixe-locale, le contexte transmis à la suite, l'impossibilité d'une prescription a posteriori des cibles et l'indispensabilité de l'autorisation de regroupement n'ont pas été intégralement réimplémentés et attaqués dans ce lot. Les tests existants passent, mais ils ne remplacent pas ces examens.

L'équivalence binaire préservée porte sur la largeur exactement égale à `2^n`, dans la classe et les régimes surjectifs définis. Elle ne constitue pas une borne universelle de temps ou de mémoire, et le résultat cardinal isolé n'est pas substitué à la cible scientifique complète.

Aucun verdict `EXACT TARGET ESTABLISHED` n'est attribué à cette livraison. La pull request reste un correctif ciblé en brouillon, pas une certification complète ni une fusion dans `main`.

## 8. Reproduction

Pour reproduire les vérifications du commit de sources :

```bash
git clone https://github.com/JohnDoe-collab-stack/relational-perimeter.git
cd relational-perimeter
git checkout --detach ef9e87bc8989b6bd45c782a94aa7e90d6dab60ab
# Utiliser le compilateur indiqué par lean-toolchain.
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
```

Pour reproduire les sondes dans une autre copie du dépôt, sans modifier le premier checkout :

```bash
git checkout --detach b74e63feae546da906de74a19752e0c37cff1827
lake build +RelationalPerimeter.Computation.ConstitutiveSearch.RelationalProfileConstitution
lake build +RelationalPerimeter.Computation.ConstitutiveSearch.EndogenousDecomposition.RoleIndexedProfiles
python3 scripts/run-focused-constitution-probes.py
```

Le script des sondes conserve les sources de production et effectue les mutations dans des fichiers temporaires. Les modifications du correctif se reproduisent aussi directement par le diff Git entre la base immuable et `ef9e87b` ; le générateur n'est pas nécessaire pour utiliser le code livré.
