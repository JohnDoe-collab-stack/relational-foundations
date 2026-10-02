# Faisabilité de la cible causale et exponentielle exacte

## 1. Cible immuable

La cible ne peut être ni remplacée par un théorème cardinal, ni réduite à une
compression, ni obtenue par l'installation indépendante d'un singleton.

> Dans ce cadre, la constitution relationnelle des dépendances est primitive.
> Le calcul produit lui-même, pendant son exécution et à partir de ce qu'il a
> déjà produit, sa décomposition opérationnelle et détermine ainsi quelles
> alternatives doivent continuer à être traitées comme des obligations
> indépendantes.
>
> Cette exécution ne produit pas d'explosion exponentielle de la largeur
> opérationnelle : bien que le readout extensif des profils constitués ait une
> largeur `2^n`, le régime exécuté les regroupe en une seule obligation sans
> identifier les profils eux-mêmes.
>
> Dans la classe binaire formalisée, une largeur opérationnelle exponentielle
> apparaît si et seulement si le régime impose de conserver séparément toute la
> multiplicité extensive, c'est-à-dire si son application `carry` est injective.
>
> L'explosion exponentielle de la largeur opérationnelle est donc l'effet exact
> de cette exigence extensive de conservation indépendante, et non une
> conséquence nécessaire de la structure relationnelle du problème elle-même.

## 2. Verdict de faisabilité

La cible est formalisable constructivement dans Lean, sans changer la méthode,
à une condition impérative : la causalité doit être une causalité **typée et
stagewise**, exprimée par une syntaxe ou un inductif d'exécution dont chaque
constructeur ne reçoit que le préfixe disponible. Elle ne peut pas être définie
comme une affirmation métaphysique sur l'ordre physique d'évaluation du noyau
Lean.

Cette précision ne modifie pas la cible. Elle donne un sens formel exact à :

```text
pendant son exécution et à partir de ce qu'il a déjà produit
```

La propriété requise est une factorisation constitutive par le préfixe : les
données du stade suivant sont formées par un constructeur dont les indices et
les arguments appartiennent au stade courant. Une fonction extérieure peut
toujours lire une donnée inutile puis retourner le même résultat ; ce fait
observationnel ne réfute pas la factorisation. En revanche, une donnée future ne
doit jamais pouvoir apparaître dans le type, les indices ou les constructeurs de
la décomposition locale canonique.

## 3. Comparaison avec l'audit final

L'audit du commit `0a65c21edecef03709081c24a8d224dae1537378`
confirme le diagnostic causal central, mais révèle aussi des lacunes que la
première version du présent document ne traitait pas encore explicitement.

| Point audité | Résultat | Conséquence pour la réparation |
| --- | --- | --- |
| iff largeur pleine / injectivité | vérifié | conserver le théorème combinatoire en aval |
| image exacte avant largeur | vérifié | conserver cette strate et la rendre constitutive de la façade |
| fusion et séparation de cibles | correctement rejetées | préserver l'exactitude bidirectionnelle actuelle |
| A : singleton indépendant | survit à la façade | remplacer la façade nue par une réalisation exécutée exacte |
| B : cible prescrite, trace reconstruite | survit | faire de la cible une projection de la décision et de la trace produites |
| C : futur stocké dans la tête | survit | construire exécution et décomposition dans un même inductif stagewise |
| E : préservation supprimée | survit | faire consommer le témoin préservant par la formation de la décision |
| ancrage relationnel de la classe générale | insuffisant | séparer le lemme cardinal générique du théorème scientifique relationnel |
| deux profils distincts regroupés | probe d'audit seulement | construire le couple et son regroupement dans le code de production |
| identité littérale du carrier | non établie par l'adaptateur générique | énoncer la cible directement sur le carrier des rôles constitués |
| documentation causale | trop forte | ne la corriger qu'après fermeture des types et des théorèmes |

Le diagnostic précédent avait donc correctement isolé les quatre ruptures
causales A, B, C et E. Il n'était pas encore suffisant pour guider
l'implémentation finale, car il ne protégeait pas complètement la juridiction
du résultat relationnel ni son exposition publique.

## 4. Diagnostic de l'implémentation actuelle

L'implémentation actuelle contient plusieurs strates utiles, mais huit raccords
doivent être rendus exacts.

### 4.1 Cible détachable de la trace

`ExecutedCausalNormalization` contient bien un résultat dépendant :

```text
source -> Sigma target, ExecutedRoleProfileReduction source target
```

mais le certificat ne protège pas cette forme comme l'unique interface publique
de normalisation. Une mutation peut remplacer la cible par le profil droit lu
directement sur les rôles, puis reconstruire une trace après coup.

Défaut méthodologique : la lecture `target` peut redevenir primitive et la trace
un accord ajouté ensuite.

Réparation requise : le résultat dépendant complet devient l'unique donnée
publique. La cible et toute obligation sont exclusivement des projections de ce
résultat. Aucun champ `targetMap`, aucune cible autonome et aucune égalité
`targetMapExact` ne doivent pouvoir remplacer ce résultat.

### 4.2 Localité de préfixe non certifiée par l'objet public

`ExecutedStageDecomposition stage` est local, mais le certificat public stocke
une histoire complète et son égalité avec un builder. Il ne porte pas encore une
interface de factorisation stagewise indépendante du futur.

Défaut méthodologique : la localité est vérifiée par une régression, mais n'est
pas une propriété constitutive exposée par le certificat final.

Réparation requise : la chaîne publique doit être construite par un inductif
stagewise dont le constructeur de tête reçoit exclusivement :

```text
état courant
stade exécuté courant
rôle constitué courant
décision opérationnelle courante
état suivant produit
```

Le tail ne peut apparaître qu'après l'état suivant, dans le constructeur
récursif. Le certificat doit exposer la factorisation de la tête par ce
constructeur local, et non seulement l'égalité de deux histoires complètes.

Il ne suffit pas de construire d'abord une exécution complète, puis de la
parcourir pour produire une décomposition dite stagewise. L'objet canonique
doit produire, dans une même récursion structurale, le stade courant, sa
décision et l'état suivant, avant de construire la suite indexée par cet état.
L'ancienne exécution peut être récupérée ensuite par effacement de cette
structure plus riche ; l'inverse ne doit pas constituer le certificat canonique.

### 4.3 Préservation disponible mais non constitutive de la réduction

La préservation est présente dans la relation et dupliquée dans la licence.
Supprimer certains champs de la licence ne détruit rien, car la preuve peut être
redérivée depuis `GeneratedStructuralFlipAtRelation.mapContinuation_accept`.

Cette redérivabilité n'est pas un défaut : la méthode demande de minimiser les
primitives. Le défaut réel est que la formation de la cible ne dépend pas d'une
décision d'absorption dont la construction exige la préservation.

Réparation requise : introduire un témoin en `Type`, par exemple une décision de
réduction préservante, dont le constructeur transformé exige simultanément :

```text
action relationnelle exacte
sortie exécutée exacte
préservation pour toute continuation acceptée
viabilité de la branche conservée
distinction des occurrences
```

La cible locale doit être une projection de cette décision. Il ne faut pas
conserver séparément des champs redondants si leur contenu est dérivable de la
relation primitive ; il faut rendre indispensable le témoin construit qui les
réunit.

### 4.4 Obligation publique détachable de sa réalisation exécutée

Le régime interne est l'image exacte des cibles, mais la façade publique
n'expose qu'un `ObligationRegime`. Un singleton `Unit` peut reproduire sa largeur
et ses fibres parce que, dans l'instance publique, toutes les cibles convergent.

Défaut méthodologique : la réalisation exacte qui rattache les obligations aux
cibles exécutées n'est pas le type public principal ; les mêmes readouts peuvent
être redémontrés sur une représentation sans provenance.

Réparation requise : définir une structure publique à constructeur privé :

```text
ExactExecutedOperationalRegime
```

qui contient, dans cet ordre :

```text
normalisation dépendante canonique
image finie calculée de ses cibles
régime dont le carrier d'obligations est cette image
accord exact entre carry et cible produite
couverture de chaque obligation par une occurrence produite
égalité de largeur avec l'image
```

La projection vers `ObligationRegime` reste disponible comme readout. Elle ne
doit plus être l'objet constitutif principal.

### 4.5 Classe combinatoire trop générale pour porter seule la cible

Le théorème générique de largeur accepte un type d'occurrences arbitraire et
des relations triviales. Ce n'est pas une erreur du lemme cardinal : son
contenu est précisément indépendant de la provenance relationnelle du carrier.
Mais ce lemme ne peut pas, à lui seul, établir la première phrase de la cible.

Défaut méthodologique : un résultat combinatoire vrai sur tout carrier est
présenté trop près du résultat scientifique qui concerne des profils déjà
constitués par une histoire dépendante de rôles relationnels.

Réparation requise : conserver deux niveaux explicitement distincts :

```text
théorème combinatoire générique :
  largeur pleine iff carry injectif sur un carrier fini surjectivement porté

théorème scientifique constitutif :
  même iff, largeur exécutée et regroupement exact,
  directement sur roleProfileFiniteCarrier roles,
  où roles provient de l'exécution relationnelle canonique
```

Le second théorème doit consommer une réalisation exacte de l'histoire des
rôles et de la normalisation. Il ne doit pas être obtenu en décorant après coup
un carrier abstrait de relations inutilisées. Inversement, il serait artificiel
de forcer le lemme cardinal générique à consommer des relations dont sa preuve
n'a mathématiquement pas besoin.

### 4.6 Carrier de la cible seulement propositionnellement raccordé

L'adaptateur générique fournit une égalité ou un transport exact entre les
profils publics et les profils génériques, mais le théorème générique ne
s'applique pas littéralement au régime exécuté sans ce raccord. La
documentation ne peut donc pas dire qu'il s'agit directement du même carrier.

Réparation requise : le théorème final de la cible doit être énoncé directement
sur `roleProfileFiniteCarrier roles`. Le transport vers la famille générique
peut rester un théorème comparatif séparé ; il ne doit pas servir à masquer un
changement de carrier dans l'énoncé principal.

### 4.7 Regroupement de profils distincts non construit en production

La non-injectivité de `carry` découle actuellement du comptage, mais le code de
production ne fournit pas le couple positif de profils distincts porté par une
même obligation. L'audit ne l'obtient que dans un probe externe.

Réparation requise : pour toute histoire publique non vide, construire deux
profils qui diffèrent à un stade déterminé, prouver leur distinction sans
axiome, construire leurs deux traces exécutées vers la même cible, puis en
déduire l'égalité de leurs obligations. Cette construction doit rester en amont
du readout cardinal ; elle ne doit pas être extraite d'un argument de taille.

### 4.8 Façade documentaire plus forte que son objet public

Plusieurs formulations attribuent déjà à la façade des propriétés que seuls le
normaliseur interne ou des probes établissent : régime jamais fourni
indépendamment, application directe du iff sur le même carrier, couple distinct
construit et décomposition produite pendant l'exécution.

Réparation requise : aucune reformulation rhétorique ne doit précéder la
réparation des types. Après celle-ci, chaque proposition documentaire devra
pointer vers un théorème de production précis et non vers une simple égalité de
readout.

## 5. Relation constitutive centrale manquante

La réparation ne doit pas ajouter une nouvelle étiquette. Elle doit formaliser
la relation qui constitue l'indépendance opérationnelle :

```text
OperationallyCoDetermined p q
```

Cette relation signifie qu'il existe une cible opérationnelle produite et deux
traces exécutées, l'une depuis `p`, l'autre depuis `q`, qui atteignent exactement
cette cible.

Elle doit être définie en `Type`, avec ses témoins positifs :

```text
target
traceFromP
traceFromQ
```

L'exactitude du régime devient alors :

```text
carry p = carry q
  iff
OperationallyCoDetermined p q est habité
```

Cette équivalence de fibres est nécessaire mais elle n'est pas suffisante. Dans
l'instance où toutes les cibles convergent, un `carry` constant indépendant la
satisfait lui aussi. Le type public exact doit donc conserver en plus la
réalisation elle-même : chaque obligation est un élément de l'image produite,
avec sa cible et une trace exécutée qui l'atteint. L'équivalence de fibres est
alors un théorème de cette réalisation, jamais son substitut.

La direction droite ne doit jamais être prouvée depuis la seule constance de
`carry`. Elle doit construire l'accord à partir des traces exécutées. La
direction gauche doit récupérer l'égalité exacte des cibles portées par
l'obligation.

Cette relation réalise directement la séparation recherchée :

```text
profils constitués distincts
!=
obligations opérationnelles indépendantes
```

## 6. Architecture nécessaire

La chaîne finale doit être la suivante :

```text
relations typées primitives
  -> stade exécuté avec sortie produite
  -> rôle constitutif relationnel du stade
  -> décision préservante formée au stade
  -> histoire stagewise de décisions
  -> profils d'occurrences constitués
  -> résultat dépendant source-(cible, trace)
  -> codétermination opérationnelle par traces
  -> réalisation exacte des obligations
  -> readout fini de largeur
```

L'extensivité intervient seulement après la constitution des profils :

```text
profils constitués -> énumération extensive -> largeur 2^n
```

Elle ne crée ni les profils, ni leurs identités, ni la décision de les maintenir
indépendants.

## 7. Obligations formelles de chaque strate

### Strate P — relations primitives

- la relation est une donnée en `Type` ;
- son action totale est calculable ;
- la préservation est un théorème séparé ;
- aucune largeur, adresse ou obligation n'est disponible.

### Strate E — exécution

- le stade contient la relation effectivement trouvée ;
- la sortie est l'application exacte de cette relation ;
- l'état suivant dépend de cette sortie ;
- le tail de l'histoire est indexé par cet état suivant.

### Strate R — rôle constitutif

- le rôle est lu depuis le stade exécuté ;
- relation, entrée, sortie, préservation et provenance sont raccordées ;
- aucune lecture extensive n'intervient.

### Strate D — décision opérationnelle

- la décision transformée exige le témoin préservant complet ;
- la décision retenue exige la viabilité positive ;
- les occurrences restent distinctes ;
- la cible locale est produite par la décision.

### Strate H — histoire stagewise

- le constructeur de tête ne mentionne aucun futur ;
- le tail commence à l'état produit ;
- les rôles et décisions sont lus depuis la même histoire ;
- une reconstruction postérieure ne peut pas inhabiter le certificat canonique
  sans fournir cette même histoire stagewise.

### Strate N — normalisation

- l'unique résultat est un sigma dépendant cible-trace ;
- la cible n'existe pas comme donnée autonome ;
- le calcul est une récursion structurelle exécutable ;
- les traces conservent les décisions locales.

### Strate O — obligations

- les obligations sont réalisées par l'image des résultats dépendants ;
- chaque obligation porte ou récupère une occurrence produite et sa trace ;
- l'égalité des obligations est exactement la codétermination exécutée ;
- la façade ne peut pas être remplacée par `Unit` sans perdre le type exact de
  réalisation.

Cette dernière exigence ne signifie pas qu'un type singleton serait impossible
ou qu'il ne pourrait pas être isomorphe au carrier d'obligations produit. Elle
signifie qu'un singleton indépendant, dépourvu des traces et de l'accord exact
avec les cibles exécutées, ne peut pas inhabiter le type de réalisation exact.

### Strate X — extensivité

- le carrier source est le même carrier de profils déjà constitué ;
- `2^n` est un readout cardinal ;
- pour tout régime sur ce carrier, largeur pleine iff `carry` injectif ;
- l'adressage séparé factorise par `carry`.

## 8. Théorèmes indispensables

Les déclarations finales doivent établir au minimum :

```text
canonicalHeadFactorsThroughCurrentStage
canonicalNormalizationResultIsDependentTrace
decisionTargetIsProducedByPreservingDecision
carryEqualityIffOperationalCoDetermination
operationalRegimeIsExactExecutedRealization
operationalWidthEqualsProducedImageWidth
publicExecutedImageIsSingleton
publicExecutedWidthIsOne
distinctProfilesRemainDistinct
distinctProfilesAreOperationallyCoDetermined
explicitDistinctProfilesCarryTogether
scientificIffOnRoleProfileCarrier
genericCountingIffIsDownstreamReadout
fullWidthIffCarryInjective
separateAddressingFactorsThroughCarry
```

Ces noms sont indicatifs ; les types et les dépendances, non les noms, sont
normatifs.

## 9. Mutations devant être reproduites localement

Aucun nouvel audit externe ne doit être lancé avant que le dépôt contienne une
suite locale qui traite chacune des mutations suivantes.

1. remplacer la réalisation exacte des obligations par `Unit` sans accord
   exécuté ;
2. remplacer `carry` par une constante indépendante ;
3. fournir une cible autonome puis reconstruire la trace après coup ;
4. indexer la décomposition de tête par une donnée future ;
5. supprimer le témoin préservant nécessaire à la décision transformée ;
6. remplacer l'action découverte par une action constante ;
7. identifier les deux occurrences ;
8. fusionner deux cibles produites distinctes ;
9. séparer deux cibles produites égales ;
10. remplacer la façade publique exacte tout en gardant seulement ses readouts.
11. remplacer l'histoire de rôles par un carrier arbitraire muni de relations
    triviales tout en prétendant conserver le théorème scientifique ;
12. supprimer le couple positif de profils distincts et ne garder qu'une preuve
    de non-injectivité par cardinalité ;
13. appliquer le théorème générique au régime exécuté en dissimulant un
    transport de carrier.

La mutation 3 doit être évaluée sur le type public du résultat dépendant : une
implémentation extensionnellement équivalente peut calculer une valeur fermée,
mais elle ne satisfait la cible que si elle produit encore le témoin dépendant
exigé. L'ordre textuel dans lequel un programmeur écrit la valeur et sa preuve
n'est pas une propriété mathématique.

La mutation 4 doit être évaluée par factorisation : consulter une donnée future
sans que cette donnée puisse influencer le résultat est observationnellement
équivalent à la fonction locale. Ce qui doit être impossible est qu'une donnée
future apparaisse dans le type de la décision, modifie sa valeur ou devienne une
hypothèse de sa formation.

La mutation C2 de l'audit est la référence négative précise : si le futur peut
être stocké dans la décomposition de tête et si le certificat canonique reste
habitable, la cible n'est pas atteinte. Une fonction externe qui reçoit un futur
mais retourne, preuve à l'appui, exactement la construction locale factorisée
ne constitue pas une nouvelle décomposition canonique et ne réfute pas la
propriété.

## 10. Critères d'arrêt avant implémentation

L'implémentation ne doit pas commencer si l'un des points suivants reste sans
solution :

- la cible doit être reformulée pour rendre le plan possible ;
- une largeur est installée avant la réalisation exacte ;
- la normalisation peut être remplacée par une cible sans trace dans le même
  type public ;
- la préservation n'intervient dans aucune formation en `Type` ;
- la façade publique ne distingue pas la réalisation exécutée d'un singleton
  nu ;
- l'extensivité intervient dans l'individuation des profils ;
- le théorème scientifique final est énoncé sur un carrier générique seulement
  relié par transport au carrier des rôles ;
- le regroupement de profils distincts n'a pas de témoin positif dans le code de
  production ;
- une mutation connue n'a pas de résultat local reproductible.

## 11. Verdict révisé de faisabilité

La cible reste réalisable sans modifier son contenu mathématique, mais le commit
audité ne l'établit pas. La réparation nécessite une reconstruction du noyau
opérationnel et de sa façade scientifique, et non l'ajout de champs ou de
théorèmes autour de l'architecture actuelle.

La construction correcte doit rendre primitifs les témoins relationnels de la
réduction, constituer la codétermination opérationnelle à partir des traces,
réaliser exactement les obligations depuis cette relation, puis seulement lire
leur largeur. L'équivalence exponentielle existante peut alors rester en aval,
sur le même carrier de profils, sans devenir la cause de la constitution.

Le point décisif est désormais entièrement explicite : le théorème cardinal
générique est déjà correct, mais il ne peut pas remplacer le théorème causal et
relationnel. Celui-ci doit être fermé sur l'histoire réelle des rôles, produire
la décomposition dans la même construction stagewise que l'exécution, faire de
la cible une sortie de la décision préservante, puis réaliser le régime exact à
partir de l'image obtenue. C'est seulement cette chaîne qui autorise la
conclusion scientifique de la cible immuable.

Le prochain travail admissible est donc :

```text
rapport final d'audit
  -> matrice exhaustive des défauts
  -> prototype isolé du noyau stagewise et de la réalisation exacte
  -> reproduction locale de toutes les mutations
  -> intégration sans suppression des résultats établis
  -> vérification complète
  -> audit externe unique
```
