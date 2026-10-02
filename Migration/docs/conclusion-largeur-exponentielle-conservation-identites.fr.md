# Conclusion de la branche : largeur exponentielle et conservation séparée des identités

**Dans ce cadre, la constitution relationnelle des dépendances est primitive. Le calcul produit lui-même, pendant son exécution et à partir de ce qu’il a déjà produit, sa décomposition opérationnelle et détermine ainsi quelles alternatives doivent continuer à être traitées comme des obligations indépendantes.**

**Cette exécution ne produit pas d’explosion exponentielle de la largeur opérationnelle : bien que la lecture extensive du carrier des profils constitués ait une largeur 2ⁿ, le régime exécuté les regroupe en une seule obligation sans identifier les profils eux-mêmes.**

**Dans la classe binaire formalisée, une largeur opérationnelle exponentielle apparaît si et seulement si le régime impose de conserver séparément toute la multiplicité extensive, c’est-à-dire si son application `carry` est injective.**

**L’explosion exponentielle de la largeur opérationnelle est donc démontrée ici comme l’effet exact de cette exigence extensive de conservation indépendante, et non comme une conséquence nécessaire de la structure relationnelle du problème elle-même.**

## Résultat démontré

Pour toute `BinaryRelationalRoleExtensiveFamily`, tout problème de cette
famille et tout `ObligationRegime` sur le carrier source correspondant, Lean
démontre le véritable `iff` suivant :

```text
R.frontier.length = 2 ^ F.stageCount(p)
  ↔ Function.Injective R.carry
```

Autrement dit, dans la classe binaire formalisée :

> **La largeur de la frontière des obligations vaut exactement 2ⁿ si et
> seulement si le régime conserve injectivement chaque identité du carrier
> source comme obligation distincte.**

L'adressage séparé n'est pas une hypothèse supplémentaire. Il est construit à
partir de l'injectivité de `carry` et doit factoriser par les obligations du
régime :

```text
identité du carrier source
  ─carry→ obligation du régime
  ─address→ slot
```

La surjectivité de `carry` est un champ essentiel de `ObligationRegime`. Ni la
pleine largeur ni l'injectivité ne sont placées dans la définition du régime ;
les deux directions de l'équivalence sont démontrées.

Avant la spécialisation binaire, le théorème général est :

```text
longueur de la frontière des obligations
  = longueur de la frontière du carrier source
  ↔ Function.Injective R.carry
```

Le terme 2ⁿ provient du théorème séparé qui calcule la largeur de la
frontière source d'une histoire uniformément binaire.

## Conséquence mathématique

Le même carrier source admet deux régimes formellement construits.

Le régime identitaire conserve chaque profil source comme obligation
distincte :

```text
régime identitaire
  ⇒ Function.Injective carry
  ⇒ largeur des obligations = largeur source = 2ⁿ
```

Le régime exécuté est construit sur exactement le même carrier.
`CausalOperationalExecutionHistory` est produit par la récursion qui exécute
les étapes. À chaque pas, elle forme un `ExecutedStageOperationalProduction`
depuis l’étape courante avant de poursuivre depuis l’état que cette étape a
produit. Le type de cette production locale ne possède aucun paramètre de
futur, et son constructeur privé fixe sa décomposition comme fonction
canonique de la seule étape courante. Son effacement redonne exactement
l’exécution publique antérieure. Pour chaque profil source,
`executedCausalNormalization` consomme ensuite une
`ExecutedReductionConstitutiveChain` exactement indexée par ce profil. Dans le
cas transformé, la décision locale élimine un
`ActionProducedOperationalTarget`, à construction privée, lui-même indexé par
un `CriterionPreservingAbsorption`. Ce témoin consomme l’application exacte de
l’action relationnelle effectivement reconstruite, la preuve séparée de sa
préservation pour toute continuation, sa non-identité, l’acceptation positive
et la distinction persistante des occurrences ; le cas retenu consomme sa
viabilité positive. Chaque maillon de la chaîne porte ainsi la décision locale
et sa cible effectivement produite avant que le maillon dépendant suivant soit
construit. `ExecutedReductionCausalExact` expose encore, à chaque rôle,
l’action, la préservation, l’acceptation et la distinction consommées par cette
construction. La normalisation ne stocke aucune paire résultat : son résultat
est défini par l’élimination de cette chaîne exacte sur le profil source, ce
qui produit un profil d’occurrences cible et une trace
`ExecutedRoleProfileReduction` indexée exactement par cette source et cette
cible.

`producedTargetOccurrences` rassemble ensuite les cibles de tous les profils
sources sans perdre les traces qui les produisent. Le carrier ambiant de ces
cibles reste le produit dépendant complet des espaces de continuation : il
n'est pas réduit d'avance à un singleton. Les traces démontrent leur
convergence. La préservation et la séparation persistante des occurrences sont
projetées depuis toute la même chaîne dans
`ExecutedOperationalGroupingAuthorization`. Les traces réalisent séparément
l’image exacte des cibles produites. Chaque production locale enregistre
l’image complète de ses sorties. L’accord de sortie exécuté permet d’en retirer
les doublons ; l’histoire compose ces images. Le transport exact réalise leurs
valeurs dans l’image admise. Sa carte inverse recopie les valeurs de la cible
sans choisir une occurrence source fixe. Ses retours garantissent la complétude
et l’absence de doublons sans utiliser la largeur un. La commutation avec `carry` et l’accord avec
l’action sur toute continuation sont prouvés séparément.
`ExactExecutedOperationalRegime`, à constructeur privé, joint
ensuite l’autorisation causale à cette réalisation exacte, sans identifier
réalisation et admission. Deux profils reçoivent
la même obligation si et seulement si leurs cibles produites sont égales, et si
et seulement si `OperationallyCoDetermined` est habité par leurs deux traces
vers une cible commune. La frontière réalise exactement la composition des
images locales enregistrées. L’accord de sortie exécuté prouve leur convergence ;
celle-ci donne une largeur un, conservée par le transport. L’accord avec la
normalisation est prouvé pour chaque source :

```text
régime exécuté
  ⇒ largeur des obligations = 1
```

L’unicité de cette obligation n’est donc pas utilisée comme substitut à la
réduction. Les cibles et leurs traces sont construites avant le régime, et le
`carry` conserve littéralement la cible produite pour chaque source. Le régime
public est une projection de leur réalisation exécutée exacte ; un singleton
indépendant ne possède pas ce type.

La course causale de la récursion fusionnée est prouvée exactement égale à celle
de la réalisation publique faisant autorité, puis son histoire de rôles est
reliée par égalité dépendante aux rôles publics. La classe générale et
l’instance exécutée utilisent définitionnellement le même carrier de profils
d’occurrences ; le théorème public de classe est donc énoncé directement sur
ce carrier, sans adaptation ni réindexation.

Dans l'instance publique positive, deux profils sources explicites sont
construits, leur distinction est prouvée, leurs deux traces vers une même cible
sont produites, puis leur même obligation exécutée est démontrée. Leur égalité
d'obligation n'établit aucune égalité dans le carrier source.

```text
distinction des identités du carrier source
  ≠ conservation comme obligations opérationnelles distinctes
```

La quantité exponentielle des profils sources ne suffit donc pas à imposer une
largeur opérationnelle exponentielle. Cette largeur apparaît exactement lorsque
le régime porte séparément toutes les identités sources.

Le régime exécuté ne compresse pas 2ⁿ obligations préexistantes. Avant son
introduction, il existe un carrier source de 2ⁿ profils distincts, dont
l’extensivité fournit la lecture quantitative ; leur statut d’obligations
opérationnelles n’est pas encore déterminé. La normalisation exécutée construit
ce statut pour chaque profil, la réalisation exacte en constitue l’image, puis
le régime en expose la frontière et la largeur. Le théorème public littéral
`constituted_exponential_width_iff_carry_injective` est énoncé directement sur
ce carrier de profils de rôles ; aucun transport vers un autre carrier
n’intervient dans cet énoncé scientifique.

Le résultat central peut ainsi être formulé sans le réduire à un problème de
compression :

> **Dans la classe formalisée, l'explosion exponentielle de la largeur des
> obligations apparaît exactement lorsque le régime impose que toutes les
> identités structurelles soient conservées comme obligations distinctes et
> séparément adressables.**

## Stratification qui donne son sens au résultat

La constitution appartient exclusivement à la couche relationnelle. Des
relations primitives de source, de formation, de cible et de provenance,
accompagnées de leurs témoins, constituent les occurrences de rôle et leur
histoire dépendante.

```text
relations primitives + témoins
  → occurrences de rôle constituées
  → histoire relationnelle dépendante
  → profils complets d'occurrences
  → carrier source
```

Les profils sont des sélections dépendantes d'occurrences déjà constituées à
chaque rôle. Leur frontière complète et sans doublon est dérivée de l'histoire.

L'extensivité n'est pas une couche constitutive. Elle est seulement le readout
quantitatif de cette frontière déjà dérivée :

```text
carrier source
  → frontière complète des profils
  → readout extensif : longueur de la frontière
```

Depuis le même carrier source, un régime d'obligations peut être formé sans
dépendre du calcul de cette largeur. Sa propre largeur est un second readout.

```text
constitution relationnelle
  → carrier de profils
      ├→ readout extensif source
      └→ carry → régime d'obligations
                  → readout de la largeur des obligations
```

Le `iff` relie ces deux readouts ; il ne transforme pas le readout extensif en
principe de constitution.

Le nom Lean `RelationalRoleExtensiveFamily` doit être lu selon cette
stratification : `RelationalRole` qualifie la constitution de l'histoire et de
ses occurrences ; la largeur extensive est un readout dérivé. Ce nom ne
désigne pas une « extensivité relationnelle » qui constituerait ses propres
termes.

## Différence avec une lecture extensionnelle

Une lecture extensionnelle prend ses termes comme donnés et les rassemble dans
une collection. Elle ne contient pas leur constitution. Le cadre relationnel
expose en amont les relations et les témoins qui constituent les occurrences,
puis maintient la distinction entre le carrier ainsi obtenu, sa lecture
quantitative et son portage opérationnel.

La différence ne s'énonce donc pas comme une opposition entre une
« extensivité classique » et une « extensivité relationnelle ». Elle réside
dans l'accès formel à une couche constitutive que la lecture extensionnelle ne
contient pas, puis dans la séparation entre identité structurelle et statut
d'obligation opérationnelle.

## Raccord après l’audit adversarial

La formation d’une occurrence est désormais portée par `GeneratedChildFormation`,
qui indexe l’enfant engendré par sa source, sa décision et sa fraîcheur, avant
qu’un transport opérationnel soit requis. Son égalité de réalisation est dérivée.
Les lectures de source, cible et provenance du rôle ne sont plus des copies
librement stockées : elles sont projetées depuis l’étape indexée. Ces accords
de réalisation sont distingués des relations de génération d’origine.

`RoleStatus.History` conserve les comparaisons de statuts sur le même porteur
de profils : les politiques en attente et mixtes ont une largeur
`2^pendingCount`, avec les cas 4, 2 et 1 à deux rôles. Ce ne sont pas trois
nouvelles exécutions SAT. Ces statuts ne déterminent pas la frontière publique.

Cette frontière vient des sorties réelles. `producedRoleOutput` applique
l’instruction à l’entrée canonique de chaque occurrence formée.
`ProducedOutputImage.Value` en porte l’image complète sans lui imposer une
valeur distinguée. L’accord exécuté prouve la convergence et permet de retirer
les doublons locaux. `ExecutedStageDecomposition.outputRegime` enregistre
cette image avant la queue future ; `ExecutedOutput.ofStagewise` compose les
images enregistrées. La largeur un est ensuite démontrée par cette convergence
et cette composition, pas par la présence d’un marqueur de statut.

L’admission est séparée de l’appartenance à l’image par `SemanticImage.Admission`
et `AdmittedImageValue`. Le consommateur abstrait n’a aucun accès à une réduction
SAT riche. Le paramètre d’autorisation fantôme a été retiré ; l’instance fournit
la garantie depuis sa chaîne. Une preuve équivalente reconstruite depuis cette
même chaîne n’est pas considérée comme une disparition de son contenu.

L’ordre est également observé dans un programme de primitives de découverte,
d’application et de décomposition. L’interprète produit une valeur et une trace ;
le calcul public est relié à cet interprète par une égalité démontrée. Une
réorganisation qui applique réellement l’étape suivante avant la première
décomposition conserve la valeur mais viole la trace attendue. Cette propriété
porte sur ces frontières de primitives, non sur le temps machine ni sur tout
calcul Lean susceptible d’être caché dans un argument.

Le théorème de convergence et le théorème binaire ne sont pas affaiblis.
`executedAdmittedRegime_notFullWidth` désigne expressément le régime public admis ;
le lemme cardinal de non-nécessité reste une conséquence plus faible. Le rapport
Aristotle original et ses mutations survivantes ne sont pas réécrits en succès.

## Portée exacte

Le théorème porte sur l'égalité de deux largeurs finies et sur la conservation
injective des identités de profil par un régime surjectif d'obligations. Dans
la sous-classe binaire, la largeur source vaut exactement 2ⁿ. Dans la classe à
arités variables, elle vaut le produit des arités locales réalisées.

Il ne s'agit pas d'une borne universelle de temps ou de mémoire, ni d'une
formalisation de tout arbre adaptatif possible. Il s'agit d'une
caractérisation exacte du moment où la largeur de la frontière des obligations
reprend intégralement la quantité lue sur le carrier source.
