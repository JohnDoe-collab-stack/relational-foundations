# Décomposition opérationnelle endogène

## Résultat

La construction exhibe une recherche dont la **décomposition opérationnelle
est un produit du calcul, et non une donnée de sa structure de branchement**.

L’ouverture produit une multiplicité structurelle. Le calcul dote cette
multiplicité d’un statut opérationnel à partir d’une transformation qui :

1. n’existe pas comme donnée avant que l’exécution ne la reconstruise ;
2. est trouvée par un travail effectivement exécuté, qui échoue sur la plupart
   des relations candidates ;
3. agit sur des continuations arbitraires, avant que l’on sache quelle
   alternative est acceptée ;
4. possède une preuve de préservation distincte, qui autorise l’abandon d’une
   alternative pour le critère considéré, sans identifier les alternatives et
   sans prouver l’impossibilité de celle qui est abandonnée.

Le résultat de la transformation fournit ensuite l’état retenu, la graine,
l’histoire des décisions et la provenance utilisés par l’étape suivante. La
reconstruction suivante a donc lieu sous des conditions produites par la
précédente.

En bref, **la multiplicité structurelle et l’indépendance opérationnelle sont
séparées, et leur statut opérationnel est constitué pendant le calcul à partir
de matériaux produits par le calcul**.

![Architecture exécutée de la décomposition opérationnelle endogène](figures/endogenous-operational-decomposition.svg)

## Obligations opérationnelles et lecture extensive

L’ordre de constitution est explicite dans les types. Des relations primitives
de source, de formation, de cible et de provenance témoignent positivement
chaque ouverture. Une histoire dépendante de ces ouvertures constitue ensuite
les identités locales d’occurrence. Le carrier de la classe utilise
`RelationalOccurrenceProfile` : chaque occurrence sélectionnée y est
indexée par l’étape relationnelle qui la constitue, depuis laquelle ses témoins
exacts de formation et de provenance sont récupérés dans `Type`. Sa frontière
complète et sans doublon, sa liste d’arités et sa largeur sont toutes dérivées
de cette histoire avant l’introduction de tout programme ou régime opérationnel.

Pour toute histoire relationnelle, Lean prouve

```text
largeur des profils = produit des arités locales réalisées.
```

Une arité uniforme `k` sur `n` rôles donne donc `k^n` ; des arités locales au
moins binaires donnent une borne inférieure `2^n`. Le dépôt contient une
famille non bornée à arités variables et, séparément, une famille binaire non
bornée indépendante de l’exécution SAT publique. Le théorème est ainsi énoncé
sur une classe générale et non inféré d’un seul exemple.

Un `ObligationRegime` vient en aval de ce carrier. Son application surjective
`carry` peut conserver chaque identité de profil constituée comme obligation
opérationnelle distincte, ou regrouper plusieurs identités. L’adressage séparé
doit se factoriser par ces obligations. Pour tout problème de toute
`BinaryRelationalRoleExtensiveFamily`, le théorème public établit le véritable
équivalent :

```text
largeur du régime = 2^stageCount
  ↔ les identités constituées restent distinctes et séparément adressables
     à travers ce régime.
```

La même condition équivaut à la capacité minimale exacte d’un adressage
factorisé. Aucun côté de l’équivalence n’est stocké dans l’autre : la largeur
exponentielle est une cardinalité lue sur la frontière du régime, tandis que la
conservation est l’injectivité de `carry` accompagnée d’un adressage des
obligations. La preuve finie générale est constructive ; l’équation binaire
provient des frontières locales constituées relationnellement.

Les deux comportements sont positivement réalisés sur le même carrier public. Le
certificat construit le régime identitaire de pleine largeur et son témoin
complet de conservation factorisée. Sur ces mêmes identités constituées, le
régime exécuté a une largeur un et ne les conserve pas comme obligations
séparées.

Sur l’exécution publique, `CausalOperationalExecutionHistory` est construit par
la récursion qui exécute les étapes. À chaque pas, elle forme un
`ExecutedStageOperationalProduction` depuis l’étape courante avant de poursuivre
depuis l’état produit par cette étape. Ce type local ne possède aucun paramètre
de futur, et son constructeur privé fixe la décomposition comme fonction
canonique de la seule étape courante. Son effacement redonne exactement
l’exécution antérieure faisant autorité. Les rôles et les licences de réduction
sont lus depuis cette même histoire. Le programme est en aval : il ne constitue
pas les alternatives du profil. Chaque `RoleStageAtom` est attaché à la relation
reconstruite par son rôle et agit sur l’occurrence effectivement sélectionnée
par un profil. L’occurrence gauche applique cette action totale, l’occurrence
droite conserve sa continuation, et l’action compilée est positivement prouvée
modifier la source exécutée.

Pour chaque profil source, `executedCausalNormalization` construit une paire
dépendante contenant un profil d’occurrences cible et une trace
`ExecutedRoleProfileReduction` exactement indexée par cette source et cette
cible. La décision locale transformée élimine un
`ActionProducedOperationalTarget` dont la construction privée est indexée par
`CriterionPreservingAbsorption`. Ce témoin consomme l’application exacte de
l’action découverte, sa preuve séparée de préservation pour toute continuation,
la non-identité de l’action, l’acceptation positive et la distinction
persistante des occurrences ; chaque décision retenue consomme sa viabilité
positive. `executedCausalNormalization` effectue sa récursion sur
`ExecutedReductionConstitutiveChain` : chaque maillon est donc consommé avant
le maillon dépendant suivant, et `ExecutedReductionCausalExact` expose l’action,
la préservation, l’acceptation et la distinction encore présentes à chaque rôle.
La paire résultat n’est pas un champ stocké dans la normalisation : elle est
définie par l’élimination de cette chaîne exacte sur le profil source fourni.

La préservation pour toute continuation et la séparation persistante des
occurrences sont aussi projetées depuis la chaîne entière sous les types
`ExecutedReductionPreservationExact` et
`ExecutedReductionOccurrenceSeparationExact`.
`ExecutedOperationalGroupingAuthorization` conserve la chaîne causale complète
dont ces deux témoins sont extraits ; cette autorisation n’est ni remplacée ni
inférée depuis le seul résultat numérique.

`producedTargetOccurrences` énumère ensuite toutes les cibles produites en
conservant, pour chacune, sa source et sa trace. Leur carrier ambiant demeure le
produit dépendant complet des espaces de continuation. Les traces démontrent la
convergence des valeurs effectivement produites. Chaque production de tête
enregistre l’image complète de sa carte de sortie locale, dans le codomaine
des continuations. L’appartenance à cette image ne contient aucune condition
de convergence. La frontière retire les doublons locaux avec l’égalité
justifiée par l’accord de sortie exécuté, puis l’histoire compose ces images.
Un transport exact réalise leurs valeurs dans l’image admise ; son inverse
recopie les composantes de la cible sans choisir un profil source depuis une
existence propositionnelle. Ses retours établissent la complétude et l’absence
de doublons avant toute lecture de largeur. Séparément,
`ExactExecutedOperationalRegime`, à constructeur
privé, joint l’autorisation de regroupement à cette réalisation exacte. La
réalisation et l’admission restent distinctes. L’égalité de deux
obligations équivaut à l’égalité des cibles produites et à l’habitation de
`OperationallyCoDetermined` par leurs deux traces vers une cible commune. La
largeur un découle de la convergence des sorties locales, de leur composition
et de ce transport exact. L’accord avec la normalisation est prouvé source par
source. Le régime public est une projection de
cette réalisation exacte, non un singleton fourni indépendamment.

Le dépôt construit deux profils sources explicites, prouve leur distinction,
construit leurs traces de codétermination, puis démontre que le régime exact les
porte ensemble sans les identifier. Sur ce même carrier de profils de rôles, le
théorème public littéral est
`regime.frontier.length = 2^n ↔ Function.Injective regime.carry`. Ses lectures
locales `2 → 1` sont calculées récursivement depuis l’histoire de réduction
effective. Les identités sources persistent donc alors que leur indépendance
opérationnelle change.

La récursion fusionnée est reliée dans le code de production à la réalisation
publique par l’égalité exacte de sa course causale, puis par l’égalité dépendante
de son histoire de rôles. La classe générale et l’instance exécutée utilisent
définitionnellement le même carrier de profils d’occurrences : le théorème
public de classe est donc énoncé directement sur le carrier exécuté faisant
autorité, sans adaptateur ni réindexation.

La recherche exécutée reste essentielle à cette instance publique. Son préfixe
de candidats en échec est extrait de l’exécution, sa relation sélectionnée est
prouvée réussie, son application agit sur des continuations arbitraires et sa
loi de préservation est distincte. La sortie, la graine, l’histoire des
décisions et la provenance constituent ensuite les conditions consommées par
la découverte suivante.

![Lecture extensive et obligations opérationnelles](figures/relational-extensive-iff.svg)

Il s’agit d’un théorème exact sur la largeur d’un carrier et l’adressage
opérationnel factorisé dans la classe formelle ci-dessus, non d’une borne
universelle de complexité en temps ou en mémoire. Le coût instrumenté et la
projection par état et quantité restent des résultats aval distincts.

![Stabilité opérationnelle endogène](figures/endogenous-operational-stability.svg)

### Limite exacte d’une projection par état et quantité

Le dépôt construit également une vue extensionnelle de stabilité qui conserve
les états source et retenu, une entrée acceptée observée et sa sortie, une
lecture numérique de largeur fournie explicitement et sa borne. La couche
générique définit `ActionFactorsThrough` : une action totale se factorise par
une projection lorsqu’une seule action sur les valeurs projetées la reconstruit
sur tout argument. Elle définit aussi `ActionProjectionCollision` : deux
antécédents possèdent des projections égales mais leurs actions totales
diffèrent sur un argument. Sa forme indexée,
`AnchoredActionProjectionCollision project action first`, fixe le premier
antécédent dans le type même du témoin. Le théorème générique
`action_not_factors_of_anchored_projection_collision` consomme cette collision
ancrée et réfute constructivement la factorisation.

Sur le système engendré d’une étape effectivement exécutée, le transport total
porté par l’instruction faisant autorité et un transport de comparaison
possédant la même source et la même cible exécutées constituent une telle
collision. L’instruction faisant autorité agit point par point comme la
relation découverte sur toute continuation. Les deux transports sont projetés
séparément ; leurs vues projetées sont égales pour la continuation exécutée
observée, tandis que leurs actions totales diffèrent sur une autre continuation
admissible. La non-factorisation exécutée est donc une instance du théorème
générique ancré. Son énoncé public,
`authoritative_instruction_projection_collision`, exhibe explicitement une
collision dont le premier antécédent est l’instruction faisant autorité ; cet
antécédent n’est pas un champ librement assignable du témoin.

Cela identifie la limite relative exacte de la projection par état et quantité
définie ici. Cette projection conserve des états, un segment de trajectoire
observé et une quantité bornée, mais oublie une partie du processus opérationnel
constitué : elle enregistre la lecture de stabilité sans déterminer la
transformation dont la reconstruction exécutée l’a produite. Il s’agit d’un
résultat formel de non-factorisation pour cette projection déterminée, et non
de la prétention d’avoir formalisé toute version de la théorie classique de la
stabilité.

## Chaîne exécutée

Pour chaque entrée, une récursion faisant autorité construit la chaîne suivante :

```text
état constitué
  → racine opérationnelle engendrée
  → extraction endogène des candidats
  → filtrage par la provenance produite
  → ouverture structurelle en deux enfants distincts
  → recherche exécutée d’une relation entre eux
  → compilation et validation du transport découvert
  → application à une continuation arbitraire
  → preuve séparée de préservation de l’acceptation et de la viabilité
  → cible retenue et détermination booléenne exécutée
  → transmission de la graine, de l’histoire des décisions et de la provenance
  → racine, domaine de candidats et recherche de relation suivants
```

Le calcul public est
`ConstitutiveSearch.EndogenousDecomposition.executeConstitutiveResolution`.
Son résultat est projeté depuis `executeConstitutiveExecutionHistory` ; aucune
seconde exécution ne fournit parallèlement l’histoire publique, l’état terminal,
la décision ou la comptabilité.

La frontière d’entrée suit la même discipline causale. Le premier état transmis
est construit depuis le point terminal enregistré par l’initialisation mesurée
effectivement exécutée. Sa génération est ensuite prouvée égale à la génération
canonique ; aucune source reconstruite indépendamment ne remplace celle qui a
été produite.

## Ce que les types séparent

Les types maintiennent visibles les distinctions suivantes :

- la génération de deux alternatives n’est pas leur indépendance
  opérationnelle ;
- une application totale sur les continuations n’est pas son théorème de
  préservation de l’acceptation ;
- la préservation relative à un critère n’est pas l’égalité des alternatives ;
- l’absorption d’une obligation n’est pas une preuve que l’alternative absorbée
  est impossible ;
- l’égalité d’une lecture n’est pas l’égalité de la recherche constituée ;
- la formation causale d’une graine par un état produit demeure distincte de
  l’invariant qui détermine sa valeur canonique ;
- un transport exact réversible n’est pas le transport dirigé utilisé pour
  l’absorption.

Cette dernière distinction raccorde directement la computation aux quatre
modules fondamentaux. `ExactTypeTransport` enregistre un transport réversible
entre carriers. `AcceptingContinuationTransport`, au contraire, contient une
application dirigée et une loi de préservation séparée. Le résultat
computationnel dépend de ce second transport sans le renforcer silencieusement
en équivalence.

## Évidence exposée par le dépôt

Le module public de formulation est
[`EndogenousOperationalDecomposition.lean`](../RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean).
Il expose des déclarations sans axiome pour :

- la classe générale non bornée de familles relationnelles dont la frontière
  complète admet une lecture extensive, et sa sous-classe binaire, avec un
  membre binaire indépendant et
  un membre à arités variables de la classe plus large ;
- l’équivalence, au niveau de la classe, entre largeur exponentielle exacte du
  régime et conservation des identités constituées comme distinctes et
  séparément adressables à travers ce régime ;
- la forme équivalente en capacité minimale exacte d’adressage factorisé ;
- un certificat public unique rattachant la même chaîne exécutée, les rôles
  faisant autorité, les profils d’occurrences, le programme aval, l’interprète
  exact et la réduction causale ;
- le régime exécuté de largeur un qui regroupe les identités sources sans les
  identifier, avec ses largeurs locales lues récursivement sur l’histoire de
  réduction ;
- la distinction structurelle des alternatives ouvertes ;
- la transformation totale de continuations arbitraires ;
- la preuve séparée de préservation de l’acceptation ;
- le transport de la viabilité et la préservation exacte de la viabilité de la
  frontière ;
- l’indépendance du pas complet à l’égard d’une preuve d’acceptation ;
- l’absence de toute étape construite et de toute histoire descendante faisant
  autorité de longueur positive après l’échec de la découverte ;
- l’échec de chaque relation candidate leurre engendrée et le nombre exact de
  tentatives précédant la réussite de la découverte ;
- la loi exacte des tentatives filtrées par la provenance et la croissance
  stricte du compteur total de recherche de relation émis par la récursion
  faisant autorité, en plus de la croissance de la recherche locale de
  référence ;
- la construction du premier état transmis depuis le point terminal de
  l’initialisation mesurée ;
- la formation, au niveau des constructeurs, de la graine et du faisceau
  d’extraction suivants à partir de l’état exécuté, distincte des preuves
  ultérieures de leur égalité canonique ;
- la consommation de la graine et de la provenance produites par la découverte
  suivante ;
- des lectures projetées égales dont les traces candidates constituées
  diffèrent ;
- des comparaisons contrefactuelles construites depuis une même origine
  exécutée : la comparaison de l’état retenu avec l’état à histoire effacée
  sépare les traces candidates constituées, tandis que la comparaison avec
  l’état bloqué sépare les histoires décisionnelles et les résultats de la
  découverte malgré l’accord de toute donnée projetable autorisée ; les
  comparateurs effacé et bloqué ne sont pas eux-mêmes émis par la récursion
  faisant autorité ;
- la non-factorisation du résultat suivant par la projection autorisée sur ce
  domaine séparateur à deux points : la projection lit l’affectation, la
  génération et la graine de recherche, dont les valeurs sont délibérément
  égales pour les deux comparateurs ;
- une comptabilité mesurée canonique, à propriétaire unique, et les bornes
  polynomiales portant sur le travail explicitement instrumenté de la famille
  construite ;
- des carriers structurels complets et sans doublon de largeur exacte `2^n`,
  des carriers en attente de largeur exacte `2^n` et des carriers opérationnels
  retenus de largeur exacte `1` ;
- la comparaison locale indexée par le type sur une ouverture exécutée :
  largeur `2` en l’absence de transport opérationnel et largeur `1` avec le
  transport retourné par la découverte exécutée ;
- des charges locales acceptées pour chaque rôle structurel, avec la lecture
  numérique transitoire dérivée `1 → 2 → 1` et sa borne uniforme `2` ;
- l’extraction du préfixe des candidats effectivement en échec et l’équation
  exacte entre sa longueur et le nombre mesuré de tentatives ;
- la preuve qu’un mauvais singleton peut posséder la bonne largeur numérique
  tout en différant de la cible sémantique exactement retenue ;
- la non-factorisation générique d’une action totale à partir d’une collision
  de projection possédant des valeurs projetées égales et des actions
  différentes sur un argument, instanciée à la fois par un séparateur fini et
  par le système engendré d’une étape effectivement exécutée.

L’implémentation complète demeure sous
`RelationalPerimeter/Computation/ConstitutiveSearch/`. En particulier,
`RelationalRoleExtensiveFamily.lean` définit les classes relationnelles
générales et l’`iff` au niveau de la classe ; `RoleIndexedProfiles.lean` et
`RoleProfileArityTransport.lean` dérivent le carrier concret et ses arités ;
`RoleIndexedProgram.lean` fournit l’interprète aval ;
`RolewiseObligationPolicy.lean` prouve l’équivalence locale/globale de la
conservation ; `PrefixLocalOperationalProduction.lean` fixe l’interface de
production à la seule étape déjà exécutée ; `ExecutedRoleIndexedReduction.lean` construit les décisions et
les traces de sorties typées ; `ExecutedCausalNormalization.lean` construit la
normalisation, prouve la convergence des cibles et en dérive le régime exact ;
`CausalOperationalExecution.lean` fusionne l’exécution des étapes avec leur
production opérationnelle locale ; `ConstitutiveExtensiveSeparation.lean`
réunit ces composants sur l’exécution publique.

Le compte rendu opérationnel antérieur reste disponible :
`OperationalFrontierStatus.lean` définit la frontière générique entre attente
et réduction, tandis que `ExecutedOperationalReduction.lean`,
`ExecutedOperationalReductionHistory.lean`,
`ExtensionalOperationalStability.lean` et
`EndogenousOperationalStability.lean` établissent la chaîne causale exécutée,
ses carriers, ses largeurs exactes et la frontière de projection. Le module de
formulation est un point d’entrée vers cette implémentation, non son
remplacement. Les suites de régression comprennent
`EndogenousOperationalStabilityRegression.lean`, qui vérifie les largeurs
publiques, le changement local de largeur indexé par le statut, chaque champ de
la réduction exécutée exacte, le préfixe mesuré d’échecs, l’application
découverte, les histoires causales et le normaliseur exacts, la distinction du
mauvais singleton, l’énoncé public de factorisation d’action et une collision de
projection générique dont l’égalité de projection est propositionnelle plutôt
que définitionnelle. `RelationalExtensiveIffRegression.lean` protège
séparément l’équivalence au niveau de la classe, sa forme en capacité exacte,
les témoins indépendants des classes générales, l’action matérielle du
programme, le champ de préservation distinct et les largeurs dérivées
récursivement de la réduction.

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

Le raccord est démontré par des cartes, pas seulement par une égalité de
largeurs. `policyObligationTransport` relie les obligations des images locales
composées aux valeurs admises avec deux retours. Sa carte inverse recopie les
valeurs produites. `publicProducedObligationTransport_carry` prouve la
commutation avec le portage ; `publicCertificate_carry_value_eq_produced_target`
fixe la cible et `publicCarriedProfilePayload_action` fixe l’action sur toute
continuation. `publicRegimeWidth_eq_producedOutputs` relie la largeur du régime
aux images enregistrées. Séparément, les retours de
`RoleStatus.History.producedOccurrenceTransport` restent valables pour les
politiques comparatives en attente et mixtes. Aucun de ces transports n’est une
bijection entre les profils sources et leur image regroupée.

Le raccord à la cible complète de continuation utilise les accords de sortie
des licences exécutées. Un transport arbitraire qui préserve le critère ne
suffit pas, à lui seul, à garantir cette égalité de sorties canoniques.

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

Les résultats sont constructifs, exécutables, uniformément indexés et sans
axiome. L’`iff` extensif porte sur la classe générale des familles relationnelles
binaires ; le phénomène computationnel complet est instancié sur une famille
SAT explicite engendrée, fondée sur une symétrie par inversion de polarité. La découverte accomplit un travail
décidable réel, rejette des candidats leurres, et le compteur de tentatives émis
par la récursion faisant autorité, filtrée par la provenance, obéit à une loi
générale exacte et croît strictement avec les entrées successives. L’échec de la
découverte ne produit ni étape ni histoire descendante faisant autorité de
longueur positive.

La recherche suivante dépend du résultat précédent en deux sens différents :

- matériellement, la comparaison contrefactuelle de l’état produit avec des
  états effacé et bloqué construits depuis la même origine exécutée montre
  que l’histoire des décisions et la provenance peuvent changer le domaine de
  candidats et le résultat de la découverte suivante ; les états comparateurs
  sont des constructions d’analyse, non des états supplémentaires émis par la
  récursion faisant autorité ;
- causalement, la racine suivante est formée depuis une graine lue sur l’état
  produit, bien que l’invariant de cet état force cette graine à être égale à sa
  valeur canonique.

Le dépôt n’établit ni `P = NP`, ni `P ≠ NP`, ni un solveur polynomial pour des
instances SAT arbitraires, ni un théorème portant sur tout espace de recherche.
Ses bornes polynomiales concernent des compteurs explicitement produits et le
paramètre unaire de la famille construite. Ces limites ne réduisent pas le
phénomène exhibé ; elles délimitent exactement le lieu où il est démontré.
