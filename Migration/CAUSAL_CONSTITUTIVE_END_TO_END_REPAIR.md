# Réparation constitutive causale de bout en bout

## 1. Cible immuable

La réparation conserve intégralement la cible scientifique déjà fixée. Elle ne
la remplace ni par un résultat de cardinalité, ni par l'existence d'un régime de
largeur un, ni par une propriété documentaire.

La chaîne à établir est strictement orientée :

```text
relations primitives et témoins exécutés
-> rôle constitutif local
-> action relationnelle et préservation
-> décision opérationnelle locale
-> trace dépendante d'un profil source vers sa cible produite
-> normalisation de tous les profils constitués
-> codétermination prouvée des cibles produites
-> régime exact engendré par ces cibles
-> largeur opérationnelle
```

Chaque objet produit à une étape doit indexer ou construire l'objet de l'étape
suivante. Une donnée seulement stockée, répétée dans un certificat, récupérée
après coup ou vérifiée uniquement par un test ne compte pas comme une
dépendance constitutive.

## 2. Diagnostic exact

### 2.1 Cible transformée contournable

Le code actuel calcule bien
`transformedExecutedRoleOperationalTarget` par l'action exécutée. Cependant,
le constructeur `ExecutedRoleOccurrenceDecision.transformed` peut être modifié
pour viser directement la cible retenue, voire cesser de consommer
`CriterionPreservingAbsorption`, sans rendre inhabitable le certificat final.

Cause : la provenance par l'action est démontrée autour de la valeur cible,
mais elle ne fait pas encore partie de l'identité du résultat produit que la
normalisation est obligée de consommer.

### 2.2 Préservation présente mais non nécessaire jusqu'au terme

La préservation des continuations arbitraires est disponible dans
`RoleStageAtom`, recopiée dans la licence puis dans l'absorption. La largeur et
la convergence peuvent néanmoins survivre à la suppression d'une de ces
copies.

Cause : plusieurs témoins redondants rendent possible une reconstruction
latérale. La chaîne doit avoir une source autoritative unique et le résultat
produit doit transporter ce témoin jusqu'à la codétermination opérationnelle.

### 2.3 Localité préfixe insuffisamment fermée par l'interface publique

La récursion canonique construit actuellement la production locale avant la
queue. Mais une mutation peut enrichir la production de tête avec une donnée
future et adapter l'implémentation sans invalider la façade scientifique.

Cause : la localité est vraie de l'implémentation actuelle, mais elle n'est pas
une interface exacte consommée par le certificat terminal.

### 2.4 Régime exact encore remplaçable dans une façade

Le régime canonique est bien une image des cibles produites, mais certaines
façades publiques peuvent encore être remplacées par un singleton indépendant
sans casser toute la suite de vérification.

Cause : l'objet final expose des égalités et des largeurs, mais ne consomme pas
partout l'objet preuve-pertinent qui relie chaque obligation à sa source, à sa
cible et à sa trace exécutée.

### 2.5 Portée relationnelle de la classe générale

Le théorème général de largeur accepte des relations triviales. Ce n'est pas en
soi contradictoire : une relation primitive peut être triviale. Mais ce théorème
est essentiellement le readout fini d'une histoire relationnelle déjà fournie ;
il ne suffit pas à établir seul la causalité de l'instance exécutée.

La réparation doit donc conserver deux niveaux sans les confondre :

1. le théorème général de readout sur les familles binaires ;
2. le théorème causal sur les histoires effectivement produites par la chaîne
   relationnelle exécutée.

## 3. Architecture réparée

### 3.1 Une seule source autoritative par strate

Supprimer les duplications de témoins qui permettent une reconstruction
latérale. Les données autoritatives sont :

1. le rôle exécuté fournit l'entrée, l'action et la sortie accomplie ;
2. `RoleStageAtom` fournit l'action relationnelle et sa préservation générale ;
3. la licence relie exactement ce rôle et cet atome aux deux occurrences ;
4. l'absorption est construite à partir de cette licence et produit une cible
   accompagnée de sa provenance par l'action et de la préservation consommée ;
5. la décision transformée ne peut être construite qu'à partir de ce résultat ;
6. la trace globale est l'itération dépendante de ces décisions ;
7. la normalisation est exclusivement l'exécution de cette trace ;
8. le régime est exclusivement l'image exacte de cette normalisation ;
9. la largeur est exclusivement le readout du régime ainsi construit.

### 3.2 Remplacer la cible nue par une production preuve-pertinente

Introduire un objet local dont la forme publique est conceptuellement :

```lean
structure ActionProducedOperationalTarget
    (license : ExecutedRoleReductionLicense role atom) where
  absorption : CriterionPreservingAbsorption license
  value : ExecutedRoleOperationalTarget license
  valueExact : value = interpretRoleStageAtom atom
    license.transformedOccurrence
    (license.transformedOccurrenceExact ▸ role.executedInput)
```

Le constructeur doit être privé. La construction canonique remplit `value`
par l'application effective de l'action. La décision transformée doit être
indexée par cet objet produit, pas seulement par une continuation nue égale à
la sortie retenue.

La projection vers la continuation brute intervient seulement après la
production. La convergence compare les projections de deux productions ; elle
ne fabrique jamais leur provenance.

Conséquence exigée : remplacer la production transformée par la cible retenue
oblige à fournir un `ActionProducedOperationalTarget` authentique. Une égalité
postérieure avec la cible retenue ne peut pas remplacer cette production.

### 3.3 Faire consommer la préservation par la codétermination

La décision transformée doit transporter l'absorption complète. La trace
globale doit conserver les décisions, et la relation de codétermination doit
être construite à partir des deux traces complètes.

La codétermination opérationnelle devra donc exposer :

- la cible commune projetée ;
- la trace du profil gauche ;
- la trace du profil droit ;
- pour chaque pas transformé, le témoin d'action et le témoin de préservation
  contenus dans la décision correspondante.

La construction du régime exact consommera cette normalisation certifiée. Une
simple fonction constante vers une cible ne pourra pas fournir les traces
certifiées nécessaires.

Il ne faut pas dupliquer la préservation dans plusieurs structures. La trace
doit référencer le témoin autoritatif déjà produit, afin que sa suppression à la
source rende réellement la construction suivante inhabitable.

### 3.4 Fermer la localité préfixe par un type sans futur

Isoler dans un module antérieur à toute histoire complète l'interface :

```lean
abbrev PrefixLocalOperationalProducer :=
  {source : CausalConstitutiveState} ->
  (stage : CausalConstitutiveStageExecution source) ->
  ExecutedStageOperationalProduction stage
```

Le producteur canonique est une valeur de ce type exact. La récursion fusionnée
reçoit ou fixe ce producteur et stocke uniquement `producer stage` dans la
tête, avant l'appel récursif.

`ExecutedStageOperationalProduction` reste indexé uniquement par `stage`. Son
module ne doit importer aucun type d'histoire future. Le module de l'histoire
consomme ensuite cette production locale.

Le certificat final transporte le producteur exact et établit que chaque tête
est exactement son application au stage courant. Deux histoires partageant la
même tête ont donc la même production locale, indépendamment de leurs queues.

Une donnée future supplémentaire est acceptable seulement si elle est hors de
la production opérationnelle et n'en affecte aucune projection. Toute mutation
qui la place dans la production, dans son index ou dans son calcul doit changer
le type public exact et être rejetée.

### 3.5 Construire la normalisation uniquement par élimination des décisions

La normalisation canonique doit rester :

```text
profil source
-> décisions locales indexées par les occurrences de ce profil
-> productions locales indexées par leurs actions
-> profil cible produit avec trace complète
```

La cible retenue ne doit jamais être un argument de la normalisation. Elle est
obtenue ensuite par un théorème de convergence qui élimine la trace :

- cas transformé : utiliser la production par l'action puis son absorption ;
- cas retenu : utiliser la sortie positivement acceptée ;
- cas récursif : combiner exactement avec la trace de queue.

Le théorème de convergence doit échouer si la production par l'action, la
préservation nécessaire à l'absorption ou la décision source-indexée est
retirée.

### 3.6 Faire du régime l'image exacte de la normalisation certifiée

Définir l'obligation non comme `Unit`, mais comme une cible effectivement
produite accompagnée de sa preuve d'appartenance à la fibre convergente. La
source et sa trace exacte restent dans l'occurrence positive source-indexée de
cette cible, portée par `ExactExecutedOperationalRegime`. Elles ne doivent pas
entrer dans l'identité de l'obligation elle-même : les y introduire séparerait à
nouveau deux sources dont l'exécution a produit la même cible et détruirait le
regroupement que le régime doit exprimer.

Le `carry` d'un profil doit conserver directement la valeur cible de
`normalization.result profile`, tandis que la réalisation exacte conserve sa
source et sa trace. Les deux équivalences doivent être prouvées :

```text
carry p = carry q <-> target p = target q
carry p = carry q <-> codétermination exécutée positive de p et q
```

L'objet `ExactExecutedOperationalRegime` doit contenir ce régime et sa
construction source-indexée, pas seulement une égalité vers une façade. Son
constructeur reste privé.

### 3.7 Séparer le readout général et le résultat causal sans les désaligner

Conserver `BinaryRelationalRoleExtensiveFamily` comme classe générale des
histoires relationnelles binaires et son `iff` de largeur. Ne pas présenter ce
théorème cardinal comme la preuve de la causalité exécutée.

Ajouter une interface de réalisation causale dont les problèmes fournissent :

- une exécution autoritative ;
- son histoire de rôles exactement constituée ;
- son producteur préfixe-local ;
- sa réduction exécutée ;
- sa normalisation certifiée ;
- son régime exact.

L'instance publique doit habiter cette interface. Le théorème final combine :

1. le readout exponentiel du carrier des profils constitués ;
2. le régime exécuté de largeur un issu de la normalisation ;
3. le `iff` pour tout régime sur exactement ce même carrier.

Ainsi, une famille aux relations triviales reste un membre légitime du niveau
général, mais elle ne constitue pas artificiellement la preuve causale de
l'instance publique.

## 4. Certificat terminal

`ExactCausalExponentialTarget` doit être reconstruit avec les champs suivants,
dans cet ordre de dépendance :

1. exécution autoritative exacte ;
2. producteur local de type sans futur ;
3. histoire causale construite par la récursion fusionnée ;
4. histoire de rôles constituée depuis cette exécution ;
5. programme et réduction indexés par ces rôles ;
6. production par action et préservation pour chaque décision transformée ;
7. normalisation source-indexée et traces complètes ;
8. convergence obtenue par élimination de ces traces ;
9. régime exact construit depuis l'image convergente ;
10. deux profils sources explicitement distincts et codéterminés ;
11. largeur exécutée égale à un sans égalité des profils ;
12. readout extensif égal à `2 ^ (input + 1)` sur le même carrier ;
13. `iff` entre largeur exponentielle et injectivité de `carry` pour tout régime
    sur ce carrier.

Un champ ne sera pas accepté s'il répète seulement un théorème déjà disponible.
Il doit soit indexer le champ suivant, soit être la conclusion terminale dont la
cible exige explicitement l'exposition.

## 5. Ordre d'implémentation obligatoire

1. Geler l'état de référence et les signatures de la cible.
2. Introduire le producteur préfixe-local dans un module ne connaissant aucun
   futur.
3. Refactorer la récursion causale pour consommer ce producteur avant la queue.
4. Introduire la production locale preuve-pertinente issue de l'action.
5. Refactorer les décisions pour consommer cette production et la préservation.
6. Refactorer les traces globales pour conserver ces décisions exactes.
7. Refaire la normalisation uniquement par récursion sur ces traces.
8. Refaire la convergence uniquement par élimination de ces traces.
9. Refaire le régime comme image exacte des résultats source-indexés.
10. Ajouter l'interface de réalisation causale au-dessus de la classe générale.
11. Reconstruire le certificat terminal dans l'ordre des dépendances.
12. Ajouter les régressions structurelles et les mutations négatives.
13. Exécuter tous les contrôles Lean et axiomatiques.
14. Corriger la documentation seulement après validation du code.

Il est interdit de passer à une étape tant que la précédente peut être retirée
sans rendre la suivante inhabitable.

## 6. Gates obligatoires

Les contrôles suivants doivent faire partie de la vérification livrée, et non
rester dans un audit extérieur :

1. la décision transformée projette définitionnellement la sortie de l'action ;
2. cette décision contient la production authentifiée et la préservation ;
3. le producteur de tête a exactement le type sans futur ;
4. deux queues valides derrière une même tête donnent la même production et la
   même décision de tête ;
5. une normalisation constante ignorant sa source est non typable ;
6. une cible prescrite avec trace récupérée après coup est non typable ;
7. un régime `Unit` indépendant ne satisfait pas l'objet exact ;
8. fusionner deux cibles produites différentes est impossible ;
9. séparer deux cibles produites égales est impossible ;
10. remplacer le carrier de rôles par un carrier isomorphe indépendant est
    impossible sans transport explicite ;
11. retirer l'action, la préservation, la distinction des occurrences ou une
    trace empêche la construction du certificat terminal ;
12. le certificat final reste privé et ne peut être assemblé depuis des valeurs
    numériques.

Chaque échec attendu doit être vérifié pour la raison type-théorique annoncée,
et non pour un nom absent, un linter, un timeout ou une erreur syntaxique.

## 7. Vérification finale

Avant toute demande d'audit indépendant :

```text
lake clean
lake build +RelationalPerimeter
lake build
bash scripts/verify.sh
pwsh -NoProfile -File scripts/verify.ps1
git diff --check
lake update
```

Vérifier en plus :

- exactement un bloc final `AXIOM_AUDIT` par fichier Lean ;
- aucun `axiom`, `sorry`, `admit`, `noncomputable`, `Classical`, `propext`,
  `Quot.sound`, `native_decide`, `unsafe` ou `implemented_by` ;
- aucun axiome dans une déclaration manuscrite ;
- tous les modules de production accessibles depuis `RelationalPerimeter` ;
- aucune régression des quatre fichiers fondateurs ;
- même carrier constitué à tous les niveaux annoncés ;
- rejet substantiel de toutes les mutations obligatoires ;
- suppression du présent document temporaire avant toute fusion dans `main`.

## 8. Critère d'arrêt

La réparation n'est terminée que si la cible immuable est démontrée par une
chaîne où chaque production est consommée par la suivante, et si la suppression
de n'importe quel transport constitutif rend le certificat final inhabitable.

Si une de ces conditions ne peut pas être obtenue constructivement, il faut le
déclarer explicitement. Il est interdit de la remplacer par une conclusion plus
faible.
