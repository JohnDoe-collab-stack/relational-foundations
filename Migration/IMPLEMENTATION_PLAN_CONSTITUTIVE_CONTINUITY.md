# Plan de fermeture de la continuité constitutive

## État de départ et statut du document

Branche : `chatgpt/aristotle-correction-20260929`.
HEAD de départ : `dd226b05056cd1f944df3368c7d3233a49d97bd4`.
Code scientifique de départ : `02919988b97d959253b9104ec20372f39ca2f69d`.

Ce document est un plan de chantier, non une déclaration de résultat acquis.
Il devra être retiré de l'arbre destiné à `main`. Aucun commit, push ou merge
n'est autorisé par la demande d'implémentation présente.

## 1. Cible intégrale, inchangée

**Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes.**

**Cette exécution ne produit pas d'explosion exponentielle de la largeur opérationnelle : bien que le déploiement extensif des profils constitués ait une largeur 2^n, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes.**

**Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c'est-à-dire si son application `carry` est injective.**

**L'explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l'effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même.**

Le résultat quantitatif précis est la pleine largeur `2^n`, dans la classe et
les régimes surjectifs déjà formalisés. Il ne s'agit pas d'une borne universelle
de temps, de mémoire ou de complexité de SAT. La production exécutée concerne
l'instance publique ; le `iff` conserve sa quantification sur toute la classe.
Ces portées ne seront ni élargies ni remplacées pendant le travail.

## 2. Méthode et invariants

L'unité suivie est une détermination constitutive persistante à travers des
couches distinctes. Il faut démontrer les raccords entre ses réalisations, pas
seulement réunir des conclusions de même valeur dans un certificat.

- Les quatre fichiers fondateurs restent inchangés.
- Le carrier source public demeure exactement le carrier des profils de
  l'histoire de rôles produite par l'exécution fusionnée.
- Une occurrence formée et ses accords de réalisation ne sont pas confondus.
- Le readout extensif ne constitue ni les occurrences ni leurs obligations.
- L'action est définie sur les continuations arbitraires ; sa préservation
  reste un résultat séparé effectivement utilisé pour l'admission.
- L'identité d'un profil source n'est pas l'indépendance de son obligation.
- Le transport exact concerne les réalisations des obligations produites,
  jamais une bijection fictive entre les profils sources et leur image regroupée.
- Les deux lois de retour doivent être accompagnées des accords de portage,
  de cible et d'action ; une équivalence de types seule ne suffit pas.
- Les productions locales utilisent leur étape et leur passé constitué, pas
  une suite achevée. La réalisation globale les projette, sans seconde découverte.
- Une garantie reconstruite depuis la même chaîne n'est pas une garantie
  supprimée. La confidentialité d'un constructeur ne remplace aucune preuve.
- Aucune hypothèse concrète nouvelle ne restera ouverte. Aucune seconde
  instance, aucun carrier concurrent et aucune enveloppe de compatibilité
  scientifique ne seront introduits pour contourner le raccord.

## 3. Acquis à conserver

`GeneratedChildFormation`, `RoleOccurrenceProfile`, le transport des fibres de
formation, le programme indexé par les rôles, la normalisation par élimination
de la chaîne, la préservation universelle, les deux profils explicitement
distincts et leur portage commun, et le `iff` général restent des acquis.

`RoleStatus.History.fibres` et `History.width` traitent déjà les politiques
mixtes. Celles-ci sont des comparaisons sur une histoire, pas d'autres
exécutions SAT. Elles ne remplacent pas la production publique.

## 4. Correction à la racine

La première application A–F reliait exactement une politique de statuts à
l’image admise, mais le statut `some` assignait déjà la réunion des occurrences.
Elle ne suffisait donc pas à établir que cette réunion venait des sorties
réelles. Cette insuffisance n’est pas corrigée par un témoin supplémentaire :
la politique utilisée par le régime public doit changer de dépendance.

La cible de la section 1 demeure intégralement inchangée. Les politiques de
statuts en attente et mixtes restent des comparaisons démontrées ; elles ne
sont plus la construction qui détermine les obligations publiques.

## 5. Construction, dans l’ordre des dépendances

### A. Exécuter la carte locale sur les occurrences constituées

`canonicalRoleOpeningPayload` lit l’entrée canonique de chaque occurrence de
rôle. `producedRoleOutput` exécute l’instruction sur cette entrée. Il ne remplace
pas l’exécution par une occurrence sélectionnée.

`producedRoleOutput_exact` consomme l’accord de sortie de la licence exécutée,
puis `producedRoleOutputs_converge` en déduit l’égalité des sorties. La
préservation sur toute continuation reste séparée de cet accord.

### B. Former l’image entière, puis sa frontière locale

`ProducedOutputImage.Value` contient une valeur du codomaine et une preuve
qu’une source la produit. Sa définition ne contient ni convergence, ni égalité
avec une valeur distinguée, ni restriction à un singleton.

L’égalité du codomaine des continuations n’est pas supposée décidable en
général. Pour les sorties effectivement convergentes, la preuve de convergence
fournit une égalité décidable sur leur image. `regime` utilise cette égalité
pour retirer les doublons de la liste des sorties locales calculées.

L’interface est conditionnelle à cet endroit précis ; l’instance ferme la
condition avec l’accord de sortie exécuté. Les deux occurrences locales sont
les seules sources énumérées pour former cette image. Le carrier source global
n’est pas remplacé par un produit de Bool ni parcouru exhaustivement.

### C. Enregistrer la production avant la suite

`ExecutedStageDecomposition.outputRegime` enregistre l’image produite à la
tête et son accord exact avec la licence. Le constructeur local n’a ni queue
future ni histoire terminée comme paramètre. La récursion fusionnée conserve
cette production avant de poursuivre depuis l’état qu’elle a produit.

`ExecutedOutput.ofStagewise` compose ces images enregistrées.
`ofStagewise_exact` raccorde cette composition à la réduction de la même
histoire. Cette lecture n’exécute pas une seconde découverte.

### D. Transporter les valeurs, sans inverse constant

`ExecutedOutput.value` lit les composantes des obligations locales.
`IsProduced` exprime leur appartenance aux images réelles sans clause de
convergence. `reify` recopie ces composantes et leurs preuves d’appartenance :
il ne choisit aucun profil source depuis une existence propositionnelle.

`value_reify` et `reify_value` établissent les retours sans utiliser la
largeur un. `carry_action` raccorde cette réalisation à l’action sur les
entrées canoniques de chaque profil.

`policyObligationTransport` relie cette composition de sorties aux valeurs
admises de la normalisation. Sa carte directe conserve la valeur réelle ; sa
carte inverse utilise `reify`, non une source retenue constante. La
commutation avec `carry` et l’accord de cible sont prouvés pour chaque source.

### E. Admettre, puis lire la largeur

L’autorisation de regroupement ferme la spécification à partir de la chaîne :
constitution des sources, distinction persistante et préservation arbitraire.
L’appartenance à l’image et l’admission restent deux données distinctes.

La frontière admise est la frontière des images locales composée puis
transportée. Sa complétude et son absence de doublons utilisent les retours.
`ExecutedOutput.width` démontre la largeur depuis la convergence de chaque
image locale et leur composition. `width_exact` utilise ce résultat, non la
largeur des statuts.

`publicRegimeWidth_eq_producedOutputs` expose le raccord public.
L’égalité avec la largeur des statuts reste une comparaison ultérieure,
jamais la cause du résultat exécuté.

### F. Conserver le résultat de classe et ses portées

Le carrier source, le `iff` de classe, le régime identitaire et les profils
sources explicitement distincts sont conservés. Le transport exact relie les
obligations produites à leurs réalisations admises ; il ne prétend pas être
une bijection entre les profils sources et leur image regroupée.

La pleine largeur `2^n` demeure la portée du théorème binaire sur les régimes
surjectifs. Aucune conclusion de temps polynomial, de complexité universelle
ou de nouveauté informationnelle n’est ajoutée.

## 6. Vérification de l’implémentation

Le contrôle accompagne les constructions, sans se substituer à elles :

- compiler les modules producteurs de données et vérifier leurs audits ;
- vérifier les deux retours, l’accord de `carry`, la cible et l’action ;
- montrer que l’image ne force pas l’égalité pour une carte qui distingue les
  deux mêmes occurrences constituées ; il s’agit d’un readout comparatif,
  non d’une nouvelle exécution SAT ;
- vérifier l’usage du régime local enregistré dans la projection publique ;
- conserver les cas comparatifs mixtes 4/2/1 et les preuves de préservation ;
- exécuter les deux builds et les deux vérificateurs, sans avertissement Lean ;
- contrôler tous les blocs axiomatiques finaux et l’absence des constructions
  interdites ; les données dans `Type` doivent rester exécutables ;
- contrôler la stratification sans assouplir ses règles, les liens français et
  anglais, le diff, le manifeste et les quatre fichiers fondateurs.

`ProducedOutputImage` appartient à la strate générique d’image `K`.
`ExecutedOutputObligations` appartient à la strate dépendante `D`.
Les figures et les fichiers utilisateur étrangers à ce chantier restent
inchangés. Aucun commit, push ou merge n’est demandé ici.

## 7. État de validation

L’image locale, sa composition, le transport et le raccord public sont
implémentés. Les vérifications suivantes ont été exécutées avec succès :

- `lake build +RelationalPerimeter` : 134 tâches, sans avertissement Lean.
- `lake build` : 150 tâches, sans avertissement Lean.
- Compilation des contrôles de continuité : succès, sans axiome dans les audits.
- `scripts/verify.ps1` et `scripts/verify.sh` : les mêmes 148 fichiers Lean ;
  133 modules de production contrôlés, tous contrôlés et sans orphelin ;
  19 fixtures de rejet attendu dans chacun des deux scripts.
- Contrôles de constructivité, d’imports et des blocs axiomatiques : succès.
- `git diff --check` : succès ; liens Markdown locaux des documents modifiés :
  valides.
- `lake update` : manifeste inchangé.
- Quatre fichiers fondateurs et figures SVG : inchangés depuis le HEAD de départ.

Ces contrôles ne valent ni nouvel audit indépendant ni déclaration que tout protocole
adversarial antérieur rejettera toute transformation syntaxique équivalente.
Une reconstruction équivalente depuis la même détermination ne constitue pas
en soi un effacement de cette détermination.
