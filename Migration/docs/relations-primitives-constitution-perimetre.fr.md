## Avant-propos

*Les mathématiciens disposent désormais, avec Lean, d'un outil de preuve
suffisamment précis pour comparer non seulement les résultats démontrés, mais
les acceptions que prennent les preuves en fonction des ontologies formelles
dans lesquelles elles s'inscrivent.*

*`Relational Perimeter` met cette possibilité à l'épreuve en prenant les
relations comme primitives de la constitution formelle. À partir de ce choix,
il réexamine les acceptions de notions usuelles telles que le rôle, le
périmètre, la circularité, la fermeture, le tout, le résidu, le transport et le
tournant. Il suit leur constitution dans les types : quelles relations sont
primitives, quels témoins sont donnés, quelles occurrences sont engendrées,
quelles relations sont conservées par les transports et quelles données sont
effectivement consommées par les preuves.*

*Le cadre est en ce sens endogène relativement à la présentation primitive
qu'il reçoit. Il n'engendre pas ses propres primitives ; il construit ou
établit dans une même architecture typée les identités, les rôles, les
histoires, la quantité du périmètre et les changements de statut qui en
procèdent.*

*Le carrier, entendu comme le support formel muni de sa structure, n'est pas
neutre. Dans l'exemple à quatre nœuds, des modèles séparateurs montrent que les
seules données locales ne fixent ni l'ordre ni la participation au tout. Pour
toute présentation, le retour à une histoire enracinée et composable permet
ensuite de reconstruire l'ordre, l'adjacence et la factorisation à partir de la
constitution globale de l'objet.*

*La portée de cette formalisation dépasse un simple raffinement terminologique.
En stratifiant construction, réalisation, admission et satisfaction d'une
spécification, elle déplace les critères mêmes de l'identité et de la
complétude. Une occurrence reçoit son identité de l'histoire relationnelle qui
la constitue, et non de sa seule valeur. Un tout est complet lorsque ses
relations déterminent positivement son domaine intérieur, non lorsqu'il épuise
toute continuation possible. Ce qui pourrait apparaître comme une incomplétude
devient alors la non-exhaustion de la génération. Le tournant périmétral
affirmatif désigne le point exact où, au-delà d'un tout déjà constitué et
complet, la génération produit une continuation hors du régime dans lequel ce
tout est maximal.*

*Le périmètre détermine ainsi une quantité exacte sans que cette exactitude
dépende d'une évaluation numérique. Cette quantité est portée par la
correspondance réversible entre les positions successives et les occurrences du
déploiement ; leur ordre et leur adjacence sont établis par des relations
structurelles distinctes. La place fermante complète le système circulaire des
exigences sans entrer dans cette quantité intérieure, puisqu'elle n'est pas
engendrée comme occurrence. `History.length` n'en fournit qu'ensuite une lecture
numérique dérivée.*

*La distinction méthodologique du théorème et de la chaîne prolonge cette
stratification sans les opposer comme deux termes étrangers. Le théorème
exprime un résultat propositionnel terminal ; la chaîne conserve les relations,
les témoins, les provenances et les dépendances typées au sein desquels sa
preuve prend son acception. Un même théorème peut s'inscrire dans des chaînes
constitutives différentes ; inversement, une chaîne peut porter davantage de
structure que n'en consomme la preuve logique minimale du théorème. La
comparaison tient donc ensemble ce que les preuves établissent et la
constitution relationnelle dans laquelle elles l'établissent.*

*Cette démarche rend comparable ce que les seuls théorèmes terminaux laissent
invisible. Deux systèmes peuvent établir des résultats propositionnels
semblables tout en donnant aux objets et aux preuves des constitutions
relationnelles, et donc des acceptions, différentes. La constitution
relationnelle du périmètre, la circularité et le tournant périmétral affirmatif
constituent ici le terrain formel sur lequel cette méthode est déployée.*

<br>

# Relations primitives et constitution du périmètre

### Circularité, rôle résiduel et tournant périmétral affirmatif

Les quatre fichiers étudiés forment une construction continue :

- `SegmentedResidualRole.lean` détermine abstraitement le rôle résiduel ;
- `AbstractSegmentedTurning.lean` articule frontière, continuation et changement
  de régime ;
- `ExactTypeTransport.lean` définit le transport exact entre types ;
- `StrongPerimetralTurning.lean` réalise l'ensemble dans une présentation
  circulaire constructive.

Leur point commun est de traiter les relations comme une partie constitutive
des objets formels. Une occurrence est individuée dans l'histoire où elle est
formée, et son rôle dépend de sa provenance et de sa participation à la chaîne ;
un périmètre est constitué par l'enchaînement de relations effectivement
témoigné ; un transport est exact par les correspondances qu'il construit ; un
tournant périmétral affirmatif est localisé par la relation entre une frontière
accomplie et sa continuation.

L'architecture générale peut être résumée ainsi :

```text
une même famille relationnelle typée
→ articulations internes et jonctions inter-nœuds
→ n − 1 témoins successifs donnés + 1 témoin fermant donné
→ déploiement enraciné de n − 1 occurrences réalisant les témoins successifs
→ périmètre constitué comme tout intérieur
→ continuation positive
→ occupation forcée de la place fermante résiduelle
→ totalisation exigée par le régime
→ rejet par l'obstruction initiale
→ tournant périmétral affirmatif et changement de régime
```

## Positionnement et portée

Cette construction est une architecture relationnelle formalisée dans Lean,
non une fondation logique concurrente. Sa proof-relevance, la séparation de ses
interfaces et les limites exactes de ses rapprochements avec les systèmes de
transition, les sémantiques de traces, les chemins libres et les théories de
types sont exposées dans la section canonique
[Positionnement et portée](positionnement-et-portee.fr.md).

![Fondations et architecture formelle de Relational Perimeter](figures/relational-perimeter-formal-architecture.svg)

## 1. Relations, rôles et occurrences

La relation locale centrale est une famille de types :

```lean
Compatible : Implicit → Explicit → Type uK
```

Un témoin de `Compatible i e` est une donnée positive. Il peut être conservé,
transporté et utilisé comme indice d'autres constructions. `LocalNode`
rassemble ainsi un terme explicite, un terme implicite, une différence, la
provenance de cette différence et une compatibilité interne de l'implicite vers
l'explicite. Le nœud est déjà une configuration relationnelle.

Un **rôle constitutif relationnel** est la détermination d'une occurrence par
les relations structurelles auxquelles elle participe dans une constitution.
Il ne s'agit pas d'une simple étiquette : le rôle peut dépendre de la formation
de l'occurrence, de sa source, de sa cible, de sa provenance, de sa succession
et de son inscription dans une chaîne composable.

Cette détermination suppose que l'occurrence existe avant sa lecture. Une
`History` est construite par une racine et des extensions composables, et
`History.Occurrence` individue un pas dans cette histoire précise. Une fonction
de lecture peut ensuite attribuer une valeur à l'occurrence ; l'histoire reste
le principe de son identité et de ses relations.

La réalisation exacte d'un rôle conserve des témoins accessibles. Dans
`ExactInternalRealization`, deux fonctions relient rôles internes et anciennes
occurrences, avec leurs deux lois de retour. Dans l'instance périmétrale,
`ExactNonClosingRealization` associe à chaque position non fermante une
occurrence dont l'adresse structurelle est exacte. Cet accord permet de
reconstruire le pas local complet et impose l'injectivité de la réalisation.

La couverture des rôles internes laisse cependant ouverte la présence d'une
continuation. Réaliser exactement chaque exigence signifie que chacune possède
son occurrence fidèle ; cela ne classe pas automatiquement toute occurrence de
l'histoire comme interne. Cette ouverture rend possible l'apparition positive
d'un nouveau rôle.

Le statut des propriétés dépend de la structure du carrier. Dans l'exemple à
quatre nœuds, une `SemanticTrace` permutée conserve les pas locaux et leur
injectivité tout en modifiant l'ordre. Une trace intercalée conserve l'ordre
tout en échouant à constituer un pont composable entre deux positions
adjacentes. Ces deux séparateurs établissent l'indépendance recherchée pour
cette présentation. Lorsque le carrier redevient une
`RootedGeneratedHistory`, la composition typée des pas et son enracinement
permettent, pour toute présentation, de reconstruire la précédence,
l'adjacence et la factorisation par le périmètre canonique.

Les relations de formation sont donc primitives, tandis que certaines de
leurs conséquences deviennent dérivables sur le carrier qui contient la
structure nécessaire. La méthode détermine cette frontière en affaiblissant le
carrier, en produisant des modèles séparateurs, puis en réintroduisant la
composition réelle. Les fichiers établissent cette reconstruction positive ;
ils ne formulent pas de converse général caractérisant toute trace à partir de
l'ordre et de la contiguïté.

Le cadre appelle **endogénéité relative** le fait qu'une détermination soit
construite ou démontrée à partir des données primitives explicitement portées
par une architecture typée, sans qu'une lecture post-constitutive intervienne
comme son principe. Cette endogénéité ne signifie pas auto-engendrement : les
relations et leurs témoins peuvent être donnés. Elle indique que leur rôle,
leurs conséquences et les statuts qui en procèdent sont établis dans la même
architecture. Elle traverse ainsi la distinction entre donné et engendré, et
ne se confond pas avec l'intériorité.

## 2. Le périmètre constitué et la circularité

`PerimeterSpine` présente une chaîne de positions nodales, sans imposer que les
valeurs des nœuds soient distinctes. Son constructeur d'avancée demande un
témoin :

```lean
Compatible node.implicit nextNode.explicit
```

Chaque avancée relie la sortie implicite d'un nœud à l'entrée explicite du
suivant. Le témoin de cette relation est une donnée primitive de la chaîne :
la génération ne le crée pas. `NonClosingPosition` désigne ces n − 1 places
successives ; `NonClosingPrecedes` en exprime la précédence et
`NonClosingNext` la succession immédiate. Les témoins internes des nœuds
appartiennent à la même famille `Compatible`, mais ils remplissent un autre
rôle : ils font partie des nœuds et non du type des exigences circulaires.

`perimeterDeployment` engendre récursivement, dans une histoire enracinée et
composable, les occurrences qui réalisent les témoins successifs donnés. Ses
positions non fermantes et ses occurrences sont reliées par deux applications
avec leurs lois de retour. Chaque occurrence possède ainsi la source, la cible,
la compatibilité et la provenance imposées par sa position. La jonction finale
n'intervient dans aucune étape de ce déploiement.

Le cadre appelle **tout constitutif** une unité structurelle dont les relations
constitutives suffisent à déterminer canoniquement leur propre domaine
d'intériorité. Sa complétude consiste dans cette détermination positive de
l'interne.

Le périmètre ainsi reconstruit constitue un tel tout.

Son domaine intérieur est constitué par les n − 1 occurrences qui réalisent
les places successives. La place fermante complète le système des exigences,
mais elle n'est pas une occurrence intérieure du déploiement.

Dans les types Lean, ce tout est l'histoire générée, enracinée et composable
qui réalise exactement les jonctions successives. L'exactitude locale y
reconstruit l'injectivité, l'ordre, l'adjacence et la factorisation par le
déploiement canonique. L'absence d'extension stricte admissible en établit la
maximalité relative au régime.

Le périmètre détermine donc une quantité exacte sans que cette exactitude
dépende d'une évaluation numérique. Cette quantité n'est pas d'abord un
cardinal : elle est le type structuré des positions non fermantes, exactement
réalisé par le type des occurrences du déploiement canonique.
`requirementToOccurrence` et `occurrenceToRequirement`, avec leurs deux lois de
retour, établissent qu'aucune position n'est omise et qu'aucune occurrence du
périmètre ne demeure hors de cette réalisation. L'ordre et l'adjacence ne
résultent pas de cette seule correspondance : ils sont conservés séparément par
`ExactNonClosingRealization.preservesPrecedence` et
`ExactNonClosingRealization.preservesNext`, grâce à l'enracinement et à la
composabilité de l'histoire. La place fermante appartient au système circulaire
des exigences, mais non au domaine intérieur ainsi mesuré, puisqu'elle n'est
pas réalisée par une occurrence du périmètre. `History.length` fournit ensuite
une lecture numérique dérivée de l'histoire : elle compte ses extensions en
oubliant la structure relationnelle qui individue et relie leurs occurrences.
Cette détermination quantitative est endogène à la constitution relationnelle
du périmètre : `History.length` en fournit une lecture numérique sans en être le
principe.

La circularité complète le système des exigences inter-nœuds par une place
fermante :

```lean
CircularRequirement P =
  NonClosingPosition P.perimeter ⊕ FinalRequirement P
```

Les n − 1 premières exigences sont les jonctions successives portées par la
chaîne. La dernière est une place ponctuelle, `FinalRequirement P`, qui ne porte
aucun témoin ; la paire fermante correspondante est témoignée séparément par un
champ primitif de la présentation :

```lean
finalJunction :
  Compatible perimeter.finalNode.implicit initialNode.explicit
```

`finalJunction` est donc une nouvelle instance de la même famille inter-nœuds,
orientée de l'implicite terminal vers l'explicite initial. Sa position dans la
présentation la distingue, même lorsque sa valeur coïncide avec une autre
compatibilité. Elle est donnée, non dérivée, et demeure extérieure aux
occurrences engendrées : le périmètre réalise les jonctions successives par des
occurrences, sans réaliser la jonction fermante. Les structures formelles la
conservent comme donnée distinguée ; aucun théorème de fermeture ne la consomme
pour produire une occurrence, une boucle ou une identification.

Le caractère fermant de la dernière place désigne ici cette complétude typée du
système des exigences, non un retour produit par l'histoire : le générateur ne
parcourt jamais `finalJunction` et toute histoire générée positive avance vers
un nouveau curseur.

La présentation contient aussi `leftEndpoint` et `rightEndpoint`. Ces
extrémités sont les deux pôles de la différence initiale ; elles ne sont ni le
premier et le dernier nœud, ni les états initial et terminal de l'histoire (la
réalisation canonique les lit seulement sur ses sommets initial et terminal).
L'obstruction initiale réfute leur contraction. La positivité de l'histoire, de
son côté, distingue ses sommets initial et terminal. Ces deux séparations ont
donc des sources formelles différentes.

`RawJunctionWithSeparatedEndpoints` réunit une compatibilité fermante,
canoniquement `finalJunction`, et la séparation des deux pôles. La structure
rend leur coexistence explicite sans dériver l'une de l'autre ni quotienter les
pôles. Elle reste compatible avec l'égalité éventuelle des nœuds initial et
terminal, car l'identité des nœuds ne définit pas la circularité.

Quatre interfaces expriment les fonctions complémentaires de cette
architecture :

- `CircularPresentation` donne la chaîne, la jonction fermante, la différence et
  son obstruction ;
- `perimeterDeployment` engendre l'histoire qui réalise les jonctions
  successives ;
- `CircularRefinement` règle l'admission et stipule le traitement de toute
  continuation positive dans la place fermante ;
- `CircularSpecificationSatisfaction` associe l'exactitude locale à une clause
  trajectorielle qui équivaut à l'absence de toute extension constitutive
  stricte du périmètre.

`noIntermediateRefinement` établit que toute histoire admise dans ce régime
est égale au déploiement canonique. Le périmètre est ainsi complet comme tout
constitutif et maximal relativement au régime, tandis que la génération
conserve sa capacité de produire au-delà de lui.

## 3. Du rôle résiduel au tournant périmétral affirmatif

`SegmentedResidualRole.lean` isole la détermination résiduelle de toute
géométrie circulaire. Son entrée comprend :

- une réalisation exacte des rôles internes par les anciennes occurrences ;
- des inclusions disjointes des anciennes et des nouvelles occurrences dans
  l'extension ;
- un étiquetage fidèle par `rôle interne ⊕ rôle résiduel`, qui préserve les
  étiquettes internes des anciennes occurrences ;
- un type de rôle résiduel contractile ;
- l'existence positive d'une nouvelle occurrence.

Si une nouvelle occurrence reprenait l'étiquette d'un rôle interne, la
préservation des étiquettes et l'injectivité l'identifieraient à l'ancienne
occurrence qui réalise ce rôle ; la disjonction exclut cette identification.
Elle reçoit donc le rôle résiduel. Comme ce rôle est contractile et que
l'étiquetage est injectif, toutes les nouvelles occurrences coïncident. La
partie nouvelle positive possède une occurrence résiduelle unique.

Le fichier factorise cette preuve jusqu'à son noyau effectivement consommé :

```text
FaithfulExtension
→ ResidualUniquenessKernel
→ ResidualDeterminationCore
→ CoreUniqueResidualOccurrence
```

La segmentation fidèle suffit ainsi à déterminer l'unicité résiduelle. Dans
l'instance circulaire, ses rôles internes sont les n − 1 places successives
déjà réalisées, et son rôle résiduel est `FinalRequirement`, l'unique place
fermante encore disponible. Ce rôle reste distinct de `finalJunction` : le
premier est un rôle ponctuel qui classe une occurrence, tandis que le second
est le témoin relationnel primitif de la paire fermante. Aucun type ne les
identifie ; `FinalClosureInterpretation` les place ensuite côte à côte au bord
terminal.

Une fois le périmètre déployé, `oneStepAfterPerimeter` construit effectivement
un pas supplémentaire. Dans tout étiquetage injectif qui préserve les anciennes
places, cette nouvelle occurrence est forcée dans la place fermante : réutiliser
une place successive l'identifierait à une ancienne occurrence. La
contractilité de `FinalRequirement` impose alors l'unicité de la partie
nouvelle. Le résiduel est ainsi déterminé, et non choisi.

`FinalClosureInterpretation` conserve alors deux relations issues du terme
implicite terminal :

```text
pas libre effectif : implicite terminal → nouvel explicite formé
jonction finale    : implicite terminal → explicite initial
```

La structure les conserve côte à côte, sans identification, composition ni
application de l'une vers l'autre. Elle est entièrement déterminée par
l'occurrence de frontière. Elle enregistre aussi la formation du pas effectif,
la provenance de sa source et l'obstruction héritée depuis la différence
initiale.

`ResidualFinalClosureInterpretation` identifie la même occurrence résiduelle à
l'occurrence de frontière de cette interprétation. La chaîne

```text
extension étiquetée
→ occurrence résiduelle unique
→ interprétation de frontière
→ tentative de totalisation
```

est donc une production dépendamment typée. Elle ne constitue cependant pas
une dépendance logique de la réfutation : une tentative peut être réindexée
sur une autre interprétation, et le rejet final ne consomme aucune donnée de
l'occurrence résiduelle.

`CircularRefinement.realizesFinal` stipule que toute continuation positive
admise dans le même régime doit fournir une tentative de fermeture bilatérale.
Cette obligation n'est pas dérivée de `finalJunction`. Les totalisations
explicite et implicite demandent qu'une même composante représente les deux
pôles de la différence initiale ; chacune reconstruit donc leur contraction.

L'obstruction est inscrite à la racine et héritée inchangée par les formations
successives. La preuve constitutive de rejet consomme cette obstruction au
bord terminal, tandis que la preuve logique minimale de l'impossibilité d'une
totalisation peut déjà être menée à partir des champs initiaux de la
présentation. Le pas reste construit et exactement localisé ; c'est son
admission dans le même régime qui est refusée.

`AbstractSegmentedTurning.lean` dégage la forme générale de ce mécanisme. Un
`BoundaryGenerator` fournit une frontière canonique, une continuation stricte
et la relation d'extension. Une frontière segmentée fournit l'occurrence
résiduelle unique. Un `ObstructedRegime` classe tout candidat admis entre
l'égalité avec la frontière et une tentative de totalisation, puis rejette
cette seconde branche.

`TurningConclusion` réunit alors les témoins de la construction et leurs
conséquences exactes :

- l'occurrence résiduelle unique ;
- la continuation effectivement engendrée ;
- sa distinction constructive d'avec la frontière ;
- la classification exacte du régime ;
- la situation de la continuation hors de ce régime ;
- l'impossibilité d'une extension stricte dans le même régime ;
- le rejet de la totalisation.

Le tournant périmétral est affirmatif parce qu'il procède de la constitution
effective d'une continuation. Les structures `PositiveContinuation`,
`PositiveNewPart` et `PositiveResidualBoundary` en portent les témoins positifs
dans les types : un nouveau pas et une occurrence résiduelle sont effectivement
donnés. Leur positivité signifie ici qu'ils sont construits, non qu'ils seraient
favorables ou optimaux. L'inadéquation au régime antérieur est établie ensuite.
Le changement de régime résulte ainsi d'un supplément constitué, non d'un
manque : **la génération continue, et cette continuation ouvre le tournant**.

Le tournant établit ainsi que l'endogène ne coïncide pas avec l'intérieur : la
continuation est produite par la génération propre au cadre, tout en se situant
au-delà du périmètre et hors du régime dans lequel celui-ci est maximal.

Dans l'instance périmétrale, ce tournant est le premier pas engendré au-delà du
périmètre. Son occurrence est encore fidèlement étiquetable dans le système
circulaire, dont elle occupe l'unique place résiduelle, et le pas reste
exactement interprétable dans toute `ConcreteContinuationAlgebra`. Deux pas
au-delà du périmètre restent constitués et localement exacts, mais ne peuvent
plus recevoir un tel étiquetage fidèle. Le tournant marque ainsi la limite
exacte entre la continuation encore classable par le système circulaire des
rôles et la poursuite de la génération.

La même architecture distingue enfin admission et satisfaction.
`CircularSpecificationSatisfaction` associe l'exactitude locale à une exigence
trajectorielle formulée indépendamment de `CircularRefinement`. Comme
`TotalLoop` est réfuté dans toute présentation, cette exigence possède
exactement le contenu logique « aucune extension constitutive stricte du
périmètre ». Sa soundness et sa complétude par rapport à `CircularRefinement`
établissent que régime et spécification classent les mêmes histoires par des
témoins distincts.
`oneStepAfterPerimeter` conserve l'exactitude locale et la possibilité d'être
encore étendu, tout en quittant le régime et la spécification.
Constitution, exactitude locale, étiquetage fidèle et admission demeurent donc
quatre statuts distincts.

## 4. Transport exact et méthode comparative

`ExactTypeTransport.lean` définit une correspondance constructive par deux
fonctions et leurs deux lois de retour :

```lean
forward  : Source → Target
backward : Target → Source

backward (forward source) = source
forward (backward target) = target
```

Le transport est réversible et composable. `sumUnit` l'étend par une composante
ponctuelle inchangée, placée à droite d'une somme. Cette structure est
indépendante d'une constitution, d'un régime, d'une spécification ou d'une
lecture particulière.

L'exactitude du transport porte d'abord sur les types reliés. La conservation
des relations demande des accords supplémentaires sur les sources, les
cibles, les pas, les compatibilités et les provenances. Cette séparation rend
visible le contenu réellement préservé : une correspondance entre porteurs et
une correspondance entre architectures relationnelles sont deux obligations
distinctes.

La même précision s'impose pour les réalisations concrètes. Une interprétation
peut établir une correspondance exacte entre les occurrences libres et
concrètes tout en fusionnant leurs états ou certaines valeurs lues. En
particulier, `ConcreteContinuationAlgebra` n'exige pas que `interpretExplicit`
distingue la cible de la jonction fermante et celle de la continuation libre ;
une algèbre à un seul état qui les identifie satisfait encore
`exactlyInterpretHistory` (construction vérifiée hors des quatre fichiers). La
distinction des deux cibles est donc garantie au niveau de la constitution
libre ; sa conservation concrète exige un accord supplémentaire.

La méthode comparative issue des quatre fichiers suit une progression courte :

```text
individuer
→ relier
→ éprouver
→ reconstruire
→ transporter
→ diagnostiquer
```

**Individuer** consiste à construire les occurrences avant leurs lectures.
**Relier** consiste à déterminer leurs rôles par des accords structurels.
**Éprouver** consiste à affaiblir le carrier pour tester les dépendances.
**Reconstruire** consiste à dériver sur le carrier complet l'ordre,
l'adjacence et la participation rendus possibles par sa composition.
**Transporter** consiste à fournir des correspondances exactes et les accords
relationnels requis. **Diagnostiquer** consiste à conserver sur la même
continuation ce qui reste constitué et la preuve exacte du changement de
régime.

Comparer deux architectures revient alors à examiner :

1. les familles de relations prises comme primitives ;
2. la manière dont leurs témoins constituent les objets, positions et chaînes ;
3. le carrier sur lequel chaque propriété est primitive ou reconstruite ;
4. les correspondances exactes entre rôles et occurrences ;
5. les relations préservées par les transports ;
6. la répartition entre les relations générées et les relations données ;
7. le rôle constitutif de chaque donnée et les preuves qui la consomment
   effectivement ;
8. la règle qui gouverne l'occupation d'une place résiduelle et l'admission des
   continuations.

Deux systèmes peuvent aboutir à des théorèmes propositionnels semblables tout
en différant dans leur constitution. La comparaison porte donc sur les
dépendances qui produisent ces théorèmes : relations, témoins, chaînes,
transports, fermetures et changements de régime.

## Extension à la computation

Le dépôt prolonge cette méthode par une construction où la décomposition
opérationnelle d’une recherche est elle-même produite pendant l’exécution.
L’ouverture engendre deux alternatives structurellement distinctes. Une
recherche effective reconstruit ensuite entre elles un transport dirigé ; ce
transport agit sur des continuations arbitraires, tandis que la préservation de
l’acceptation est établie par un théorème séparé. L’absorption d’une obligation
est ainsi relative au critère de viabilité : elle n’identifie pas les
alternatives et ne prouve pas l’impossibilité de celle qui est abandonnée.

Le résultat exécuté produit en outre l’état retenu, la graine, les décisions et
la provenance consommés par l’étape suivante. La multiplicité structurelle et
l’indépendance opérationnelle ne sont donc pas confondues : le statut
opérationnel est constitué pendant le calcul à partir de relations et de données
que le calcul a lui-même reconstruites ou produites. La présentation détaillée et la portée
exacte de ce résultat figurent dans
[Décomposition opérationnelle endogène](decomposition-operationnelle-endogene.fr.md).

## Conclusion

Les quatre fichiers donnent une forme constructive à un cadre
d'**endogénéité relative** : une architecture formelle reçoit une présentation
primitive relationnelle, puis construit les occurrences, les rôles et les
histoires qui en procèdent, tout en distinguant leurs réalisations, leurs
admissions et leurs changements de régime dans ses propres types.

Dans l'instance circulaire, une même famille relationnelle apparaît en trois
places distinctes : témoins internes des nœuds, jonctions successives et
jonction fermante. La circularité réside dans le système complet des exigences
inter-nœuds : n − 1 témoins successifs sont donnés avec la chaîne et réalisés
par autant d'occurrences engendrées ; un dernier témoin est donné de
l'implicite terminal vers l'explicite initial.

Le périmètre constitué est l'histoire enracinée et composable qui réalise
exactement les jonctions successives. Il forme un tout parce que ses relations
déterminent positivement ses occurrences, leur ordre, leur adjacence et leur
domaine intérieur. Le rôle fermant ponctuel complète le système des exigences ;
`finalJunction` témoigne la paire relationnelle fermante sans devenir une
occurrence de cette histoire. Leur rapprochement est effectué au bord terminal
par `FinalClosureInterpretation`, non par une identification dans les types.

Toute continuation positive fidèlement étiquetée occupe alors nécessairement
la place fermante restée libre, et son occurrence y est unique. Le régime
circulaire stipule que cette occupation doit fournir, au bord terminal, une
tentative de totalisation des deux pôles de la différence initiale.
L'obstruction portée depuis la racine rejette cette contraction. Le tournant
périmétral affirmatif est ainsi exactement localisé : la génération se poursuit
par une continuation effectivement constituée, tandis que l'incorporation de
celle-ci dans le même régime est impossible.

La méthode qui en résulte compare les architectures à partir de ce qu'elles
constituent et préservent. Elle distingue, pour chaque relation, sa place dans
la constitution, sa réalisation éventuelle comme occurrence, sa conservation
sous transport et son usage effectif dans les preuves. Elle suit ainsi les
relations depuis leurs témoins locaux jusqu'au tout généré, puis depuis ce tout
jusqu'à la place où sa continuation change de statut.
