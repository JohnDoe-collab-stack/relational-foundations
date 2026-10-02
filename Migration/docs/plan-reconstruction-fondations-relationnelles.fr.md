# Plan détaillé de reconstruction des fondations relationnelles

Ce plan organise la reconstruction mathématique et Lean des fondations de Relational Perimeter. Il vise une théorie dans laquelle les relations et leurs témoins constituent des places, des occurrences, un domaine exactement réalisé et une quantité structurelle, puis permettent de définir la circularité, les interprétations de frontière et les changements de régime. La clarté recherchée porte sur les primitives et les dépendances des preuves autant que sur les modules.

Le chantier proposé construit une théorie générale et une instance périmétrale complète. Les preuves actuelles servent de référence et de modèles de contrôle. Leur conservation ne doit pas imposer des définitions qui contrediraient les nouvelles fondations. Toute différence de portée devra être expliquée et démontrée.

Le présent document est un plan de travail, pas une déclaration de résultats déjà acquis. La demande actuelle autorise sa préparation. Aucun fichier Lean n’a été réécrit pour le produire.

**Référence technique établie lors de l’analyse initiale du 30 septembre 2026.** La branche était `chatgpt/aristotle-correction-20260929`, à `dd226b05056cd1f944df3368c7d3233a49d97bd4`. Le répertoire de travail comportait des modifications et des fichiers non suivis, principalement dans la partie computationnelle. La construction de `RelationalPerimeter` avait réussi et exécuté 3 135 déclarations d’audit sans dépendance axiomatique signalée. Cette référence ne vaut pas nouvelle exécution des contrôles après chaque changement du répertoire ; elle ne certifie pas les nouvelles interfaces proposées ici.

## 1 Objet mathématique et périmètre du chantier

La cible est de construire la chaîne suivante avec des raccords démontrés entre ses étapes :

```text
types et familles relationnelles primitifs
→ témoins distingués et architecture de présentation
→ places relationnelles et rôles
→ formation et occurrences engendrées
→ réalisation exacte accompagnée de ses accords
→ domaine intérieur et système complet des rôles
→ quantité structurelle
→ continuation positive et détermination résiduelle
→ interprétation de frontière
→ admission ou sortie d’un régime
→ éventuelle cardinalisation
```

La frontière fermante possède une branche propre. Elle ne doit pas être artificiellement placée après la réalisation intérieure dans les dépendances : la présentation peut déjà déterminer la frontière, son rôle final et son témoin avant qu’une occurrence nouvelle existe.

Le résultat visé distingue donc un ordre de dépendance mathématique d’un ordre d’exposition. On ne prouvera pas une chronologie philosophique en s’appuyant seulement sur l’ordre des déclarations dans un fichier.

Le périmètre initial comprend les quatre modules mathématiques fondamentaux et leur point d’entrée public. La migration computationnelle intervient après la construction d’une instance périmétrale complète. Le chantier ne prétend pas refonder les règles générales de Lean ni établir une théorie des cohérences homotopiques supérieures.

### Résultats attendus

- Une présentation des primitives et de la notion de constitution relative.
- Une théorie successive des places et des occurrences.
- Une théorie de la réalisation distinguée et de ses éventuelles propriétés de rigidité.
- Une frontière fermante autonome et un rôle final équipé de son origine relationnelle.
- Un théorème de délimitation formulé sans confondre classement et réalisation.
- Une quantité structurelle avec un critère explicite de comparaison.
- Une théorie générale du résidu et une interprétation finale dans l’instance circulaire.
- Une théorie des régimes séparée de la génération et de la circularité.
- Une construction affirmative du tournant, couplée à sa propre continuation.
- Des transports constitutifs avec cohérences de témoins et lois de composition.
- Une lecture cardinale dérivée et des modèles séparant les couches.
- Une migration vérifiée des consommateurs existants.

## 2 Principes de méthode

### Définition des responsabilités

Chaque définition doit dire ce qu’elle reçoit et ce qu’elle constitue. Chaque théorème doit distinguer ses hypothèses déclarées, les champs effectivement consommés et les données supplémentaires qui situent sa signification.

Pour chaque notion centrale, produire une fiche comportant :

1. Les entrées primitives et leurs univers.
2. Le type de sortie et ses indices.
3. Le constructeur ou l’éliminateur qui produit la donnée.
4. Les témoins conservés et leur autorité.
5. Les accords dérivés.
6. Les projections qui oublient une partie de la constitution.
7. Les transports autorisés.
8. Un modèle positif et, lorsque pertinent, un modèle séparateur.

### Exactitude des annonces

Les expressions « dérivé », « constitué », « exact », « complet », « fidèle », « libre », « circulaire » et « indépendant » doivent recevoir un sens local défini. On ne leur attribuera pas une portée plus large que les signatures démontrées.

La présence d’un argument dans le type d’une fonction ne démontre pas que son implémentation l’utilise. Une preuve de conservation ou de reconstruction doit accompagner les raccords essentiels. Une structure contenant plusieurs résultats ne démontre pas que ces résultats proviennent de la même chaîne.

La dépendance d’un rôle à une frontière ne doit pas être justifiée uniquement par le choix d’un inductif à un constructeur. Une équivalence uniforme avec une famille constante peut conserver l’index. La différence constitutive doit être portée par les données équipées et les morphismes qui les préservent.

### Construction et validation

Les nouveaux modules restent constructifs et soumis aux contrôles existants : pas de `sorry`, `admit`, principe de choix, déclaration axiomatique, code `unsafe`, ni recours aux constructions interdites par `scripts/verify.ps1`.

Les égalités de fonctions ne seront pas ajoutées par commodité si elles imposent des dépendances axiomatiques. Les lois de transport et d’inversion seront d’abord formulées point par point. Une égalité de structures plus forte ne sera exigée que si elle est utile et démontrable dans les contraintes du projet.

On ne multipliera pas les certificats de valeurs déjà déterminées par un index. Quand une donnée est réellement stockée, sa projection doit lire cette donnée. Quand elle est dérivée, sa provenance doit être explicite. Les deux cas ne sont pas interchangeables.

## 3 Décisions mathématiques à fixer

Les choix recommandés dans cette section sont des propositions de conception. Ils devront être éprouvés par les premiers modèles Lean avant d’être considérés comme stables.

| Question | Choix recommandé | Obligation associée |
|---|---|---|
| Portée de la fondation | Constitution relative à une présentation primitive | Décrire les données reçues et celles construites |
| Généralité de la succession | Histoire générique de pas et instance canonique séparée | Ne pas exporter la détermination par curseur comme propriété générale |
| Réalisation | Décomposition distinguée avec rigidité optionnelle | Séparer correspondance choisie et unicité de toute réalisation |
| Frontière | Objet autonome déterminé par l’architecture | Relier ses interfaces au départ et au terme de l’épine |
| Témoin fermant | Habitant distingué de la fibre portée par la frontière | Conserver le témoin sous transport sans le confondre avec le rôle |
| Rôle final | Fibre contractile équipée de sa frontière | Démontrer ce que les projections et transports conservent |
| Circularité | Structure positive préalable aux obstructions | Fournir une instance circulaire sans présupposer un rejet de totalisation |
| Obstruction | Couche supplémentaire | Démontrer ses conséquences depuis ses hypothèses exactes |
| Clôture des rôles | Exhaustivité relative à une grammaire déterminée | Ne pas annoncer une impossibilité universelle de tout autre rôle |
| Quantité structurelle | Domaine exactement réalisé avec signature et accords | Définir ses morphismes et son critère d’équivalence |
| Régime | Famille d’admission indépendante | Les obligations de fermeture doivent apparaître dans sa définition |
| Tournant | Construction couplée à une continuation déterminée | Identifier l’occurrence interprétée à celle produite par cette continuation |
| Cardinalisation | Lecture dérivée | Construire le transport vers `Fin` après l’exactitude |
| Compatibilité avec l’existant | Adaptation explicite et temporaire | Ne pas présenter une égalité d’habitation comme une équivalence riche |

### Questions qui restent ouvertes

Trois choix ne doivent pas être décidés implicitement pendant l’implémentation.

**La rigidité de la réalisation.** Veut-on que toute preuve `Realizes r o` impose `r = classify o`, ou seulement distinguer une réalisation exacte particulière parmi plusieurs ? La recommandation est de permettre les deux notions et de réserver les théorèmes d’unicité forte à la couche rigide.

**La signature générale.** Une signature entièrement arbitraire avec plusieurs sortes et opérations dépendantes peut devenir un second projet de métathéorie. Commencer par une signature explicite suffisante pour l’instance périmétrale, puis généraliser les schémas dont les lois de composition auront été démontrées.

**Les générations multiples.** La couche générique doit pouvoir représenter plusieurs témoins ou plusieurs successeurs. L’instance périmétrale conservera initialement son générateur canonique. Une généralisation du tournant à des générations ramifiées sera formulée sous des hypothèses propres, sans être promise comme conséquence automatique.

## 4 Architecture proposée

Les noms ci-dessous sont proposés. Leur rôle mathématique est prioritaire sur leur orthographe finale. Le nombre de modules sera ajusté à la lisibilité des preuves ; il ne faut pas reproduire artificiellement les cinq fichiers actuels.

Les modules neutres peuvent être classés dans la strate `U`. Les modules constitutifs sont dans `F`. Ils ne doivent importer aucune exécution, aucun SAT, aucun régime computationnel ni aucune mesure de coût. La façade globale conserve une strate d’agrégation adaptée aux règles existantes.

| Groupe | Modules proposés | Responsabilité |
|---|---|---|
| Outils | `ExactTypeTransport` | Deux applications et leurs retours |
| Histoire générique | `RelationalPerimeter.Constitution.History` | Pas, occurrences, sommets, composition et portions positives |
| Architecture successive | `RelationalPerimeter.Constitution.RelationalSpine` | Épine à témoins et positions issues de ses avancées |
| Présentation | `RelationalPerimeter.Constitution.Presentation` | Primitives, architecture et autorité des témoins |
| Formation | `RelationalPerimeter.Constitution.GeneratedConstruction` | Construction canonique, registres et provenance |
| Réalisation | `RelationalPerimeter.Constitution.ExactRealization` | Réalisation distinguée, retours et accord inverse |
| Rigidité | `RelationalPerimeter.Constitution.RealizationRigidity` | Unicité des rôles ou occurrences lorsqu’elle est exigée |
| Frontière | `RelationalPerimeter.Constitution.ClosingBoundary` | Interfaces, fibre fermante et rattachement à l’architecture |
| Rôles | `RelationalPerimeter.Constitution.CircularRoles` | Rôles intérieurs et finaux, somme et séparation |
| Délimitation | `RelationalPerimeter.Constitution.InteriorDelimitation` | Domaine intérieur, classification et exclusion finale |
| Résidu | `RelationalPerimeter.Constitution.ResidualDetermination` | Exclusion de l’intérieur et unicité conditionnelle du résidu |
| Reconstruction | `RelationalPerimeter.Constitution.InternalReconstruction` | Reconstruction de l’inverse intérieur depuis l’étiquetage |
| Interprétation | `RelationalPerimeter.Constitution.BoundaryInterpretation` | Occurrence nouvelle, formation, frontière et jonction |
| Régimes | `RelationalPerimeter.Constitution.Regime` | Admission, tentatives, classification et diagnostics |
| Tournant | `RelationalPerimeter.Constitution.AffirmativeTurning` | Chaîne complète et sortie éventuelle du régime |
| Quantité | `RelationalPerimeter.Constitution.StructuralQuantity` | Objet exact équipé de sa signature |
| Signature | `RelationalPerimeter.Constitution.ConstitutiveSignature` | Relations, opérations et témoins à préserver |
| Transport | `RelationalPerimeter.Constitution.ConstitutiveTransport` | Transports de porteurs et de fibres avec accords |
| Lois | `RelationalPerimeter.Constitution.ConstitutiveTransportLaws` | Réflexivité, inversion, composition et cohérences |
| Cardinalisation | `RelationalPerimeter.Constitution.Cardinalization` | Longueur dérivée et réalisation dans `Fin` |
| Instance | `RelationalPerimeter.Perimetral.Presentation` | Présentation hétérogène explicite et implicite |
| Instance | `RelationalPerimeter.Perimetral.Construction` | Générateur canonique et déploiement |
| Instance | `RelationalPerimeter.Perimetral.Realization` | Accords locaux et couverture exacte |
| Instance | `RelationalPerimeter.Perimetral.Closure` | Obstruction, totalisations et interprétation finale |
| Instance | `RelationalPerimeter.Perimetral.Turning` | Régime périmétral et certificat composé |
| Modèles | `RelationalPerimeter.Perimetral.Examples` | Exemple autonome et modèles séparateurs |
| Façade fondamentale | `RelationalPerimeter.Constitution` | Point d’entrée sans computation |
| Façade publique | `RelationalPerimeter` | Fondations et applications publiques |

### Sens des dépendances

L’histoire générique et les transports de types ne connaissent ni la circularité ni les obstructions. L’épine produit les places. La construction produit les occurrences. La réalisation relie ces deux couches. La frontière constitue une branche de rôles distincte. Le régime reçoit les constructions et leurs interprétations ; il ne constitue pas rétroactivement les occurrences.

La signature et les lois générales de transport peuvent être développées après le premier théorème complet de délimitation. Leur insertion ne doit pas modifier l’autorité des témoins déjà constitués. La cardinalisation importe les objets structuraux ; ceux-ci ne l’importent pas.

Avant toute création des fichiers, établir la liste précise de leurs imports. La réalisation exacte abstraite ne dépend ni de la présentation périmétrale ni de sa formation canonique. La présentation successive minimale ne dépend pas des rôles finaux. La présentation circulaire positive étend cette base avec une frontière et un témoin fermant ; les obstructions et le régime sont des enrichissements ultérieurs. La formation abstraite reçoit une algèbre de génération, tandis que les lois de détermination par curseur appartiennent à l’instance canonique. Ces interfaces seront réparties dans les modules proposés seulement après vérification de l’absence de cycle.

La façade `RelationalPerimeter.Constitution` exportera les interfaces générales. La façade globale exportera aussi l’instance périmétrale, par une façade dédiée ou des imports explicites. Les nouvelles familles `RelationalPerimeter.Constitution.+` et `RelationalPerimeter.Perimetral.+` devront être prises en compte dans `lakefile.toml` ainsi que dans les contrôles de portée des racines publiques. Un simple ajout au manifeste des strates ne suffit pas à intégrer leur construction et leurs audits.

## 5 Phase initiale de référence et de préservation

### But

Établir une référence récupérable du code courant, de ses résultats et de ses consommateurs avant toute modification de source.

### Travail

1. Enregistrer la branche, le HEAD et l’état suivi et non suivi du répertoire de travail.
2. Préserver les sources modifiées et non suivies : un simple `git diff` ne constitue pas une sauvegarde de ces dernières.
3. Distinguer les modifications du chantier des modifications déjà présentes. Aucun nettoyage global ou retour global à HEAD ne doit intervenir.
4. Conserver le texte conceptuel fourni comme source de référence durable dans la documentation du chantier, avec son origine et son statut.
5. Inventorier tous les exports fondamentaux utilisés par les applications et les tests.
6. Relever les blocs d’audit, règles de strates, contrôles d’imports et cas d’échec attendus.
7. Construire les cibles actuelles et archiver un compte rendu compact des contrôles.
8. Constituer une table par export : signature actuelle, consommateurs, sens conceptuel, destination envisagée et accord de migration nécessaire.
9. Choisir un espace d’implémentation isolé adapté à l’état réel du travail. Un worktree neuf ne contient pas automatiquement les modifications locales.

### Points d’attention

Le plan computationnel `IMPLEMENTATION_PLAN_CONSTITUTIVE_CONTINUITY.md` figeait les fondations pour son chantier propre. La présente reconstruction a une autre portée : elle devra coexister avec ce travail pendant la transition, puis documenter quelles anciennes contraintes sont remplacées. Cela n’autorise pas à modifier sans examen les conclusions computationnelles ou les interfaces de provenance.

### Livrables

- État de référence récupérable.
- Inventaire des consommateurs.
- Table des exports et de leur portée.
- Compte rendu de construction et d’audit.

### Critère de sortie

Il est possible de retrouver l’état de départ et de distinguer toute modification nouvelle. L’inventaire contient notamment `ConstitutiveGeneration`, `CausalFoundationBridge`, les utilisateurs directs de `ExactTypeTransport` et les usages des namespaces historiques.

## 6 Phase du contrat fondationnel

### But

Stabiliser le sens des notions avant de choisir les structures Lean définitives.

### Travail

1. Écrire une définition conceptuelle de présentation relative, place, rôle, occurrence, réalisation, domaine intérieur, frontière, circularité, quantité, régime et tournant.
2. Séparer le statut d’une donnée primitive de celui d’une conséquence inductive.
3. Définir les différentes exactitudes : accord local, injectivité, couverture globale et correspondance réversible.
4. Définir les deux lectures de l’unicité de réalisation.
5. Définir la distinction entre témoin fermant, place finale, occurrence finale et totalisation.
6. Définir les variantes de complétude : clôture des rôles, couverture du domaine, satisfaction d’une spécification et maximalité dans un régime.
7. Établir la convention d’identité entre occurrences de constructions différentes : comparaison par transport ou interprétation, sans égalité globale présupposée.
8. Définir les données de la quantité structurelle et les données de son environnement circulaire.
9. Préciser le traitement de `Type`, `Prop`, égalité, pertinence des témoins et univers.
10. Corriger les formulations conceptuelles dépassant les données : équivalence avec `Unit`, unicité de toute réalisation et absence absolue d’une troisième classe.

Le texte fourni raisonne au niveau des ensembles ou 0-types. Sa traduction Lean devra expliquer l’usage de l’égalité propositionnelle et de l’irrélevance des preuves d’égalité, tout en conservant les témoins relationnels comme données dans `Type`. On ne rajoutera pas une hypothèse de troncation homotopique sans préciser son sens dans Lean. Les relations de précédence pourront elles-mêmes être des propositions ; toutes les données de la signature ne sont pas obligatoirement des fibres proof-relevant.

### Modèles de contrôle

- `Realizes = Unit` avec deux rôles distincts et une décomposition distinguée exacte.
- Une famille finale contractile sur deux frontières distinctes avec un transport uniforme entre les fibres.
- Une équivalence de fibres qui échange deux témoins distingués.

Ces modèles doivent être conservés comme contre-exemples aux inférences trop fortes, pas utilisés pour appauvrir les objets visés.

### Critère de sortie

Chaque usage d’« exact », « complet » ou « unique » correspond à une signature précise. Les questions ouvertes sont isolées ; aucune n’est dissimulée dans un constructeur choisi par commodité.

## 7 Phase des outils neutres et de l’histoire générique

### But

Extraire les opérations indépendantes de la circularité, sans importer la présentation périmétrale.

### Interfaces

```text
History Step source target
Occurrence history
LocatedStep Step
Vertex history
PositiveHistory Step source target
ExactlyOne history
append first continuation
OccurrencePrecedes first second
OccurrenceNext first second
```

La structure générique d’histoire ne doit pas recevoir un champ de canonicité du successeur. Elle conserve les témoins de pas fournis.

### Théorèmes et constructions

1. Racine et extension des histoires.
2. Composition et lois unité et associativité.
3. Occurrences `last` et `earlier`, sans occurrence à la racine.
4. Sommets initial et final comme positions dans l’histoire ; séparation de ces positions pour une histoire positive. Cette séparation ne concerne pas automatiquement leurs états lus : une histoire générique positive peut revenir au même état.
5. Décomposition constructive entre racine et histoire positive.
6. Plongements ancien et nouveau dans une histoire composée.
7. Injectivité de chacun des plongements.
8. Séparation ancien et nouveau.
9. Classification constructive de toute occurrence composée, avec preuve de reconstruction.
10. Transport exact `Occ(append H K)` vers `Occ H ⊕ Occ K`, avec les deux retours.
11. Conservation du pas situé sous plongement.
12. Précédence, adjacence, irréflexivité et trichotomie structurelle des occurrences.
13. Caractérisation d’une histoire exactement à un pas.
14. Déduction « positivité et unicité des occurrences impliquent exactement un pas ».
15. Lectures d’occurrences et transport de lectures par applications réversibles.

### Conservation de l’existant

Le module `ExactTypeTransport` est candidat à une conservation presque intégrale. La propriété `sumUnit` reste un outil de porteur, sans interprétation de frontière implicite. Une extension générale par somme de deux transports pourra être ajoutée si elle sert réellement aux raccords.

### Critère de sortie

Tous ces résultats se construisent sans présentation circulaire, jonction, obstruction, régime ou longueur numérique. Les anciens et nouveaux plongements ont des accords pointwise vérifiés.

## 8 Phase de l’architecture successive et des places

### But

Construire les places depuis une épine dont les avancées conservent des témoins relationnels.

### Interfaces

```text
Node : Type
NextRel : Node → Node → Type
RelationalSpine NextRel start
SuccessivePosition spine
PositionPrecedes spine first second
PositionNext spine first second
```

Dans l’instance périmétrale, `NextRel` sera obtenu par la compatibilité entre la composante implicite de la source et la composante explicite de la cible. Cela préservera les deux sortes d’interfaces.

### Travail

1. Définir l’épine dépendante avec ses témoins d’avancée.
2. Définir les positions inductivement, et non primitivement par `Fin` ou par une somme avec `Unit`.
3. Construire les éliminateurs de position retrouvant les données de l’avancée.
4. Retrouver source, cible et témoin particulier dans des fibres correctement indexées.
5. Construire la précédence et l’adjacence.
6. Démontrer l’irréflexivité de la précédence et le passage de l’adjacence à la précédence.
7. Construire l’équivalence dérivée entre positions d’une avancée et `Unit ⊕` positions de la suite.
8. Construire les transports induits par une transformation d’épine conservant les témoins.
9. Distinguer une transformation qui conserve seulement la forme d’une épine d’un transport constitutif de ses relations.
10. Documenter la différence entre la structure finie successive et sa lecture ultérieure dans `Nat`.

### Critère de sortie

Une position n’est pas seulement un indice numérique : son élimination retrouve une avancée relationnelle précise. Les transports qui oublient les témoins ne sont pas présentés comme constitutifs.

## 9 Phase de la présentation et de la formation

### But

Construire les occurrences à partir d’une présentation relationnelle en séparant la formation générique et le générateur canonique de l’instance.

### Travail

1. Définir une présentation successive minimale, sans obstruction à la contraction.
2. Définir les données locales de l’instance hétérogène : explicite, implicite, compatibilité, différence et provenance.
3. Définir les lectures retournées sans les confondre avec la constitution complète.
4. Définir le terme de formation avec le témoin relationnel choisi.
5. Définir la constitution initiale et la constitution formée.
6. Définir une autorité unique pour la différence actuelle et sa provenance.
7. Définir les registres de formation actuelle et de formation préservée.
8. Définir les registres historiques indexés par leur origine complète.
9. Démontrer leur conservation au cours d’un pas et d’une histoire.
10. Démontrer que le registre actuel ne peut être confondu avec un registre ancien préservé.
11. Construire les éliminateurs de formation et leurs lois exactes.
12. Définir séparément le successeur canonique et les lois de canonicité de l’instance.
13. Extraire l’obstruction persistante du noyau initial : elle pourra être un enrichissement de la constitution, avec ses propres lois de conservation.
14. Vérifier que l’enrichissement obstrué ne modifie pas artificiellement les places ou occurrences successives.

### Questions à éprouver

La représentation actuelle utilise `BoundaryDifferenceCode` pour rendre l’induction dépendante acceptable par Lean. Une nouvelle représentation peut conserver cette technique. Le plan n’exige pas une autre représentation uniquement pour obtenir des noms plus abstraits.

Le mot « libre » devra être justifié par les éliminateurs et leurs lois, avec la portée exacte de l’algèbre de formation. Il ne devra pas annoncer une propriété universelle plus forte que celle effectivement démontrée.

### Critère de sortie

La présentation successive équipée de son algèbre de génération produit une construction positive sans recevoir une jonction ou une réfutation de boucle. Les registres lisent les données constituées, et les accords de conservation sont démontrés.

Cette production exige une algèbre de génération positive : les familles relationnelles seules ne fournissent pas, pour toute présentation arbitraire, un successeur ni un terme de formation. L’interface doit donner les constructeurs qui consomment les témoins primitifs, leurs sources et cibles, et les accords de formation et de provenance. Le déploiement de l’épine sera démontré pour les présentations équipées de cette algèbre. L’instance canonique en construira une concrètement.

La distinction entre registre actuel et registre ancien concerne leur origine et leur position dans la constitution. Elle ne permet pas d’affirmer que leurs valeurs lues ou leurs témoins projetés sont nécessairement différents. Une séparation de registres sera formulée sur leurs types équipés ou sur les constructeurs qui les distinguent.

## 10 Phase de la réalisation exacte et de la rigidité

### But

Définir une décomposition exacte accompagnée d’accords et traiter séparément l’unicité de la relation de réalisation.

### Interface schématique

```text
Role : Type
Occurrence : Type
Realizes : Role → Occurrence → Type
realize : Role → Occurrence
classify : Occurrence → Role
roleRoundTrip : classify (realize role) = role
occurrenceRoundTrip : realize (classify occurrence) = occurrence
agreement : Realizes role (realize role)
```

Cette signature est schématique. Les univers et les paramètres de construction devront être explicites. Elle ne constitue pas encore du code Lean compilé.

### Théorèmes

1. Injectivité de `realize` et de `classify`.
2. Couverture constructive de toutes les occurrences du domaine.
3. Accord inverse dérivé par transport le long du retour des occurrences.
4. Unicité pointwise de l’inverse pour une réalisation fixée.
5. Restriction d’une réalisation à son domaine exactement couvert.
6. Distinction formelle entre couverture des rôles et couverture de l’histoire entière.
7. Transport d’une décomposition distinguée avec ses accords.

### Couche de rigidité

Définir séparément les propriétés possibles :

```text
Realizes role occurrence → role = classify occurrence
Realizes role occurrence → occurrence = realize role
```

Selon les retours exacts, certaines propriétés pourront être déduites des autres. Distinguer aussi l’unicité d’un rôle ou d’une occurrence de l’unicité des témoins de réalisation. Plusieurs témoins d’un même accord peuvent demeurer distincts dans `Type`.

### Instance canonique

Reconstruire `RequirementOccurrenceAgreement` comme réalisation spécialisée. Démontrer que, dans les histoires enracinées canoniques, l’accord de curseur détermine les données complètes. Exporter ce résultat dans l’instance, sans l’imposer à toute présentation relationnelle.

### Critère de sortie

Le contre-exemple `Realizes = Unit` habite la décomposition distinguée, mais ne peut pas fournir indûment les théorèmes de rigidité. Toute affirmation d’unicité précise la couche utilisée.

## 11 Phase de la frontière et du système circulaire des rôles

### But

Construire une frontière autonome portant ses interfaces et sa relation fermante, puis situer le rôle final dans cette structure.

### Travail sur la frontière

1. Définir les types des interfaces initiale et terminale.
2. Définir leur rattachement au départ et au terme de l’architecture successive.
3. Définir la famille fermante et la fibre correspondant à ces interfaces.
4. Construire la frontière dérivée depuis la présentation, en privilégiant des vues des données autoritatives.
5. Ajouter le témoin fermant distingué comme donnée positive séparée.
6. Définir un transport de frontière et ses accords sur les interfaces et les fibres.
7. Définir la conservation du témoin fermant, distincte de l’équivalence de la fibre.

Il ne faut pas demander une égalité entre une interface implicite et une interface explicite de types différents. Les identifications à étudier porteront sur des lectures dans un type commun de pôles, ou sur un transport explicitement donné.

### Travail sur les rôles

1. Définir `BoundaryFinalRole boundary` par un inductif à constructeur unique.
2. Démontrer sa contractilité.
3. Démontrer le transport exact de sa fibre vers `Unit`.
4. Distinguer la fibre seule, la famille indexée et le rôle total équipé de sa frontière.
5. Sur le rôle total, démontrer que l’égalité projette un accord des frontières.
6. Définir les rôles intérieurs comme positions de l’épine.
7. Définir les rôles complets par somme.
8. Démontrer classification exhaustive et séparation.
9. Définir les transformations préservant les branches intérieure et finale.
10. Exposer les projections qui oublient la frontière ou les témoins et établir leur portée.

### Modèles

- Frontière avec une fibre fermante inhabitée avant l’ajout d’un témoin.
- Même architecture successive avec deux témoins fermants distincts.
- Deux frontières distinctes dont les fibres finales sont transportables.
- Présentation circulaire positive indépendante de toute obstruction.

### Critère de sortie

L’origine commune de la place et du témoin fermant apparaît dans les indices et les accords. Le document ne prétend pas que le seul porteur singleton empêche une simplification équivalente de la représentation.

## 12 Phase du déploiement intérieur et de la délimitation

### But

Obtenir le premier résultat complet reliant places, occurrences, accords et frontière.

### Construction

1. Déployer récursivement chaque avancée successive en un pas engendré.
2. Ne pas parcourir la jonction primitive dans ce déploiement intérieur.
3. Construire la réalisation position vers occurrence.
4. Construire le décodage occurrence vers position avec son certificat de reconstruction.
5. Démontrer les deux retours.
6. Démontrer les accords de source, cible, formation, compatibilité et provenance.
7. Construire la classification intérieure dans le système complet.
8. Démontrer l’exclusion de l’étiquette finale.
9. Définir la réalisation des rôles complets de sorte que l’exclusion relationnelle finale soit justifiée, et pas simplement affirmée depuis l’étiquette.
10. Démontrer les variantes distinguée et rigide du théorème de délimitation.
11. Démontrer que la clôture des rôles n’exige pas l’existence d’une occurrence finale.
12. Démontrer séparément la continuation possible lorsque le générateur est disponible.

### Résultat composé

Le certificat doit réunir des données qui partagent la même présentation, la même épine, le même déploiement et les mêmes témoins. Des égalités de valeurs numériques ne peuvent pas servir de raccord.

### Critère de sortie

Une présentation circulaire positive équipée de son algèbre de génération et de ses accords de déploiement produit un domaine intérieur exactement réalisé, délimité dans son système complet de rôles. Le résultat ne reçoit aucune classification de régime ni mesure numérique. C’est le premier jalon scientifique complet du chantier.

La portée est celle d’une présentation équipée de la génération et des accords de déploiement précédents. Pour l’exclusion finale, il faudra choisir et justifier une famille `RealizesFull` qui prolonge la réalisation intérieure. Deux voies sont admissibles : une réalisation complète liée à une classification rigide, ou des constructeurs relationnels dont la branche finale exige effectivement une occurrence de continuation. Dans la seconde voie, il faut démontrer l’absence d’un tel constructeur dans le déploiement intérieur. Définir l’exclusion finale comme un champ hypothétique ne constituerait pas la démonstration recherchée.

## 13 Phase de l’exactitude locale et de la composition globale

### But

Retrouver et situer les résultats forts de l’instance actuelle sur l’ordre, l’adjacence et la factorisation.

### Travail

1. Définir l’exactitude locale indépendamment de la couverture globale.
2. Démontrer l’irréflexivité de l’avancée canonique par des relations structurales.
3. Démontrer l’absence de pas dans une histoire canonique aux extrémités identifiées.
4. Démontrer les résultats de détermination par curseur avec leurs hypothèses exactes.
5. Démontrer l’injectivité d’une réalisation locale canonique.
6. Démontrer la conservation de la précédence.
7. Démontrer la conservation de l’adjacence par exclusion d’un intervalle positif.
8. Reconstruire le premier pas de l’histoire depuis une occurrence locale exacte.
9. Reconstruire récursivement le déploiement comme facteur initial.
10. Déduire une extension constitutive du périmètre depuis l’exactitude locale.
11. Conserver les réalisations partielles et leur complétion.

### Modèles séparateurs

Reconstruire les traces permutées et intercalées. Le premier modèle conserve l’exactitude locale mais échoue sur l’ordre. Le second conserve l’ordre mais échoue sur la participation effective à une composition entre exigences adjacentes.

Ajouter un modèle de génération non canonique montrant que la reconstruction complète depuis le seul curseur n’est pas un théorème général.

### Critère de sortie

Chaque résultat global indique pourquoi son porteur et son générateur suffisent. Les modèles empêchent d’étendre ces conclusions à une trace ou à une génération arbitraire.

Les contre-modèles de trace ne doivent pas habiter frauduleusement la même interface forte que les histoires générées canoniques. Nommer leurs interfaces locales distinctes, puis donner les projections ou affaiblissements qui rendent la comparaison possible. Une permutation réfutant la conservation de l’ordre sur une trace ne réfute pas le théorème qui la dérive depuis une véritable composition canonique.

## 14 Phase de la continuation et du résidu

### But

Formaliser la détermination résiduelle générale et la rattacher à une continuation réellement construite.

### Théorie générale

1. Définir l’extension positive avec une continuation et une recomposition.
2. Démontrer la stricte différence dans l’instance où la progression est irréflexive.
3. Définir ancien, nouveau et porteur étendu.
4. Démontrer ou recevoir explicitement la séparation et les injectivités nécessaires.
5. Définir l’étiquetage complet fidèle et la conservation des anciens rôles.
6. Démontrer qu’une nouvelle occurrence ne peut reprendre un rôle intérieur.
7. Démontrer son étiquette résiduelle.
8. Démontrer le caractère sous-singleton de la partie nouvelle sous ces conditions.
9. Ajouter la positivité pour obtenir un centre distingué et la contractilité de la partie nouvelle.
10. Formaliser séparément le noyau minimal sans anciens porteurs.
11. Démontrer les adaptations conservant étiquette et occurrence.
12. Reconstruire l’inverse intérieur depuis les conditions de reconstruction.
13. Démontrer son accord avec l’inverse canonique lorsqu’il existe déjà.

### Deux chemins de preuve

Conserver distinctement le chemin général depuis une extension complète fidèle et le chemin canonique direct où la continuation est déjà à un pas. Les comparer par des accords d’occurrence, sans leur attribuer une même source explicative de l’unicité.

### Critère de sortie

Le théorème général ne mentionne pas la jonction fermante. L’instance fournit positivement sa continuation et identifie ses nouvelles occurrences à celles utilisées par le théorème. Une deuxième occurrence nouvelle distincte est incompatible avec la classification fidèle dans le même résidu contractile, sans être incompatible avec la génération elle-même.

L’énoncé obtenu depuis l’étiquetage seul est une détermination de l’étiquette, et non encore un habitant de `RealizesFull final occurrence`. Cette réalisation relationnelle exige un accord supplémentaire construit depuis le pas et sa formation. Le théorème enrichi indiquera explicitement ce pont ; l’existence de `j★` ne le remplace pas.

Les comparaisons d’histoires doivent être bien typées. Si la cible varie, utiliser un type total d’histoires enracinées tel que `Σ target, History Step root target`. Une extension fournit alors une continuation entre les cibles et une égalité de recomposition dans une fibre commune. L’inégalité stricte et la classification du régime concernent les constructions totales. On ne comparera pas directement par `=` deux termes dans des fibres `History` de cibles différentes. Le code actuel suit cette discipline avec `RootedGeneratedHistory` et `StrictConstitutivePrefix` ; la nouvelle interface devra la conserver.

## 15 Phase de l’interprétation de frontière et des obstructions

### But

Relier l’occurrence finale à la frontière primitive et séparer cette interprétation des obligations de totalisation.

### Interprétation positive

1. Construire l’occurrence finale depuis la continuation positive et le résultat résiduel.
2. Identifier cette occurrence au pas situé de la continuation.
3. Retrouver sa source et sa cible.
4. Conserver son terme de formation et sa provenance exacte.
5. Attacher la frontière structurale autoritative.
6. Attacher le témoin fermant distingué avec son accord exact.
7. Démontrer la compatibilité effective du pas engendré.
8. Démontrer la différence entre son contenu et celui de la jonction primitive lorsque les types retournés la rendent observable.
9. Dans l’instance canonique, retrouver le départ terminal et la première cible libre.

La structure positive contient aussi le témoin de réalisation finale construit à partir du pas, avec son accord à l’étiquette résiduelle. Un simple enregistrement réunissant une occurrence quelconque, une frontière et `j★` serait insuffisant. Le constructeur de l’interprétation prend le résultat résiduel et les données exactes de cette même continuation ; ses projections démontrent leurs accords.

### Couche obstruée

1. Définir le type commun des pôles et leurs lectures.
2. Définir l’obstruction à la contraction comme enrichissement explicite.
3. Définir l’obligation qui ferait d’une identification une boucle totale.
4. Définir l’obligation qui ferait d’une boucle une contraction.
5. Démontrer le rejet des boucles dans cette classe obstruée.
6. Reconstruire les noyaux explicite et implicite de contraction.
7. Reconstruire les totalisations riches et leurs projections vers les noyaux.
8. Démontrer le rejet de chaque côté séparément.
9. Définir l’attachement constitutif reliant la tentative à sa propre interprétation.
10. Démontrer la conservation de l’obstruction dans la chaîne de formation obstruée.

### Critère de sortie

La présence d’une jonction positive est compatible avec la séparation des pôles. Le rejet des totalisations annonce sa classe d’obstructions et les champs qu’il consomme. L’interprétation de frontière existe avant toute admission par un régime.

## 16 Phase des régimes et du tournant affirmatif

### But

Construire un tournant complet où le résidu, l’interprétation et la sortie de régime concernent une même continuation.

### Régime général

1. Définir `Regime construction : Type` séparément de la génération.
2. Définir les interprétations et les tentatives propres au régime.
3. Définir l’analyse constructive « canonique ou tentative ».
4. Définir son rejet et construire la classification exacte.
5. Démontrer la sortie de toute extension stricte concernée.
6. Conserver les diagnostics `RegimeExit` et leur variation des familles positives et négatives.
7. Conserver le quantificateur uniforme sur les implémentations, en fixant le candidat avant ce quantificateur.

### Chaîne couplée

1. Définir un contexte contenant une continuation et la famille de ses nouvelles occurrences.
2. Relier la frontière résiduelle au contexte par les champs de recomposition et les accords d’occurrence.
3. Construire l’interprétation depuis l’occurrence résiduelle produite.
4. Exposer une projection prouvant que l’occurrence interprétée est celle du producteur.
5. Construire la tentative du régime sur cette interprétation exacte.
6. Construire le certificat de tournant avec intérieur exact, rôles complets, continuation, résidu, interprétation et diagnostic.
7. Distinguer un tournant positif général d’un tournant accompagné d’une sortie de régime.
8. Démontrer la version périmétrale obstruée.

Les noyaux minimaux pourront rester disponibles. Leur résultat ne sera pas présenté comme une chaîne complète s’ils n’ont pas les raccords nécessaires.

### Spécification et adéquation

Reconstruire la spécification circulaire indépendante du régime dans ses définitions, démontrer correction et complétude, puis préciser que la trajectoire canonique est satisfaite par absence d’extension stricte. Une équivalence d’habitation par classification du porteur ne sera pas appelée reconstruction directe des témoins riches.

La première adéquation normative peut demeurer globale et constante le long des occurrences. Une adéquation locale dépendant réellement des occurrences devra être identifiée comme résultat supplémentaire, avec des témoins spécifiques.

### Critère de sortie

Le certificat permet de suivre sans rupture une occurrence engendrée jusqu’à l’interprétation et au rejet de l’admission. La sortie ne se déduit ni du seul rôle final ni du seul témoin fermant.

## 17 Phase de la quantité et des transports constitutifs

### But

Définir les objets de comparaison avant leur cardinalisation.

### Quantité structurelle

1. Définir le domaine exactement réalisé et sa décomposition distinguée.
2. Définir la signature des relations à conserver.
3. Définir les accords constitutifs portés par le domaine.
4. Distinguer la quantité intérieure de son environnement circulaire complet.
5. Définir les projections vers les rôles seuls, occurrences seules, lectures et porteurs.
6. Démontrer quelles informations sont conservées par ces projections.
7. Construire une quantité circulaire intérieure avec frontière, rôle final non intérieurement réalisé et témoin fermant.

### Signature

Commencer par les composantes exigées par l’instance : source, cible, formation, provenance, compatibilité, précédence, adjacence et composition. Pour chacune, écrire ses sortes, ses paramètres et les opérations à préserver.

Un transport de fibres ne suffit pas à préserver une opération de composition. L’interface doit inclure les accords correspondants. Les témoins distingués de réalisation et de fermeture possèdent chacun une loi propre lorsque ces témoins appartiennent à l’objet comparé.

La signature doit préciser les porteurs de nœuds, d’états, de différences et de provenances utilisés par ses relations. Lorsque deux présentations ont des porteurs différents, les applications ou transports sur ces sortes et les accords de source et de cible sont nécessaires. Des transports limités aux rôles et occurrences ne suffisent pas à typer une équivalence de compatibilité ou de formation sur des états hétérogènes. Pour la première version, fixer une signature de sortes et d’opérations commune, avec des interprétations éventuellement différentes ; les changements de signature sont hors de ce premier résultat.

### Transport

Construire :

```text
FRole
FOccurrence
accord de la réalisation directe
transport réversible des fibres Realizes
cohérence du témoin de réalisation distingué
transports des relations retenues
accords sur leurs opérations
```

Ces données définissent le transport de quantité intérieure relative à une signature. Un transport de quantité circulaire équipée ajoute la conservation des branches intérieure et finale, le transport de frontière et la conservation du témoin fermant. Ces lois supplémentaires ne sont pas imposées aux quantités sans environnement circulaire. Le module ou l’interface devra distinguer les deux niveaux, même si certaines constructions sont partagées.

### Lois à démontrer

1. Accord inverse de classification dérivé des retours et de l’accord direct.
2. Réflexivité par les identités.
3. Inversion des porteurs et des fibres.
4. Reconstruction de l’accord de réalisation inverse.
5. Reconstruction de la cohérence des témoins inverse.
6. Composition des applications sur les rôles et occurrences.
7. Composition des transports de fibres avec tous les changements d’indices.
8. Calcul explicite des transports successifs des témoins distingués.
9. Conservation des opérations relationnelles sous composition.
10. Lois unité, associativité et inversion au niveau pointwise requis.
11. Réflexivité, symétrie et transitivité de l’existence de transports constitutifs.
12. Distinction entre les données de transport en `Type` et leur simple habitation dans `Prop`.

Les lois seront d’abord démontrées pour la signature concrète suffisante et pour ses enrichissements effectivement implémentés. Le mot « général » ne promet pas une preuve uniforme pour toute signature dépendante arbitraire. Pour chaque enrichissement, refaire le calcul d’inversion et de composition des nouveaux accords. Une égalité globale entre structures de transport contenant des fonctions ne sera pas exigée : les lois pointwise et les accords de fibres suffisent au résultat annoncé.

### Modèles

- Équivalence des porteurs qui ne conserve pas l’ordre.
- Équivalence des fibres qui ne conserve pas le témoin distingué.
- Transport qui échange les branches lorsqu’aucune loi ne l’interdit.
- Transformation de même lecture numérique mais de constitution différente.
- Signature vide et réalisation triviale comme cas appauvri, avec sa portée exacte.

### Critère de sortie

L’équivalence constitutive générale possède des inverses et compositions avec leurs accords. Sa transitivité ne repose pas seulement sur `ExactTypeTransport.compose`. Les contre-exemples habitent les interfaces faibles et échouent précisément sur les lois fortes qu’ils ne satisfont pas.

## 18 Phase de la cardinalisation et des lectures

### But

Donner une lecture numérique au domaine déjà constitué sans modifier son identité.

### Travail

1. Définir la longueur d’une histoire comme élimination de son inductif.
2. Démontrer les lois de longueur de la racine, de l’extension et de la composition.
3. Construire explicitement le transport `Occ history` vers `Fin history.length`.
4. Démontrer les deux retours.
5. Composer ce transport avec la réalisation intérieure pour cardinaliser ses rôles.
6. Démontrer les inégalités de longueur associées aux préfixes et préfixes stricts.
7. Retrouver les bornes numériques du régime après sa classification structurelle.
8. Démontrer l’invariance de la lecture cardinale sous les transports retenus, avec les hypothèses finies appropriées.
9. Conserver les lectures arbitraires et leurs transports réversibles d’indexation.
10. Distinguer ces résultats de toute affirmation sur le coût d’une exécution ou d’un algorithme.

### Critère de sortie

Aucun module constitutif inférieur ne dépend du module de cardinalisation. Le nombre est relié au domaine par un transport démontré, et non par une annotation externe.

Le transport `Occ history ↔ Fin history.length` est réversible sur les porteurs lorsqu’on conserve la construction et ses accords. La projection qui ne conserve que le naturel n’est pas réversible sur les quantités équipées : elle oublie leurs relations et témoins. L’invariance cardinale ne fournit donc pas une réciproque « même nombre implique équivalence constitutive ».

## 19 Phase de l’instance périmétrale complète

### But

Construire une instance autonome qui éprouve toutes les nouvelles interfaces.

### Travail

1. Reprendre les quatre nœuds et les témoins de compatibilité interne et successive.
2. Construire la frontière quatrième vers premier.
3. Construire le témoin fermant distingué.
4. Construire les trois places intérieures et le rôle final.
5. Construire le déploiement intérieur et sa décomposition exacte.
6. Construire la première continuation libre.
7. Construire son étiquetage complet fidèle.
8. Démontrer sa détermination résiduelle.
9. Construire son interprétation avec formation et provenance.
10. Démontrer la séparation entre la jonction primitive et le pas effectif.
11. Construire l’obstruction sur les pôles booléens distincts.
12. Construire le régime obstrué et sa classification.
13. Construire le tournant complet.
14. Retrouver la quantité intérieure de trois par cardinalisation.
15. Retrouver les modèles de permutation et d’intercalation.
16. Construire une instance à témoins relationnels multiples pour vérifier que la cohérence des témoins a un contenu effectif.
17. Construire une présentation circulaire positive où l’obstruction n’est pas une donnée requise par l’interface.

### Critère de sortie

La théorie abstraite possède des habitants construits. Les résultats forts sont accompagnés de modèles séparant les notions plus faibles. La nouvelle instance ne se contente pas de réemballer un certificat terminal de l’ancienne.

## 20 Phase des interprétations concrètes

### But

Préserver l’interprétation positive dans plusieurs porteurs tout en distinguant morphisme et équivalence.

### Travail

1. Définir une algèbre d’interprétation des générateurs et des témoins.
2. Construire l’histoire interprétée par récursion sur l’histoire constituée.
3. Construire les deux applications sur ses occurrences et leurs retours.
4. Démontrer les accords de source, cible et pas interprété.
5. Distinguer les transformations unidirectionnelles des fibres de leurs transports réversibles.
6. Définir les conditions supplémentaires faisant d’une interprétation une équivalence constitutive.
7. Reconstruire les chemins partiels depuis une dérivation concrète, sans prétendre reconstruire depuis toute histoire concrète arbitraire.
8. Retrouver les diagnostics uniformes de sortie de régime.
9. Fournir un modèle d’interprétation qui conserve les occurrences mais appauvrit certaines lectures ou relations.

### Critère de sortie

Une correspondance exacte d’occurrences ne se transforme pas implicitement en équivalence de toute la constitution. Les quantificateurs sur les implémentations et la dépendance au candidat restent inchangés.

## 21 Phase de comparaison et de migration des cinq fichiers

### Règle de comparaison

Pour chaque ancien résultat, déterminer si la nouvelle version est identique, plus générale, plus faible ou de portée différente. La table de migration devra donner le raccord exact : égalité définitionnelle, égalité pointwise, transport d’indices, morphisme, équivalence de données ou équivalence de simple habitation.

### Traitement des fichiers

| Fichier actuel | Traitement proposé | Preuve de continuité exigée |
|---|---|---|
| `ExactTypeTransport.lean` | Conserver l’outil neutre, compléter seulement si nécessaire | Accords pointwise des applications et retours |
| `SegmentedResidualRole.lean` | Répartir détermination et reconstruction ; façade temporaire | Même étiquette résiduelle, même occurrence positive et inverse reconstruit compatible |
| `AbstractSegmentedTurning.lean` | Séparer diagnostics, noyaux minimaux et chaîne couplée | Même candidat, mêmes familles et même quantification ; portée des adaptations documentée |
| `StrongPerimetralTurning.lean` | Répartir présentation, construction, réalisation, clôture, tournant et modèles | Correspondances de places et occurrences ; accords de formation, provenance et témoins |
| `RelationalPerimeter.lean` | Distinguer façade fondamentale et façade globale | Exports publics et audits cohérents avec les nouvelles dépendances |

### Travail

1. Construire les nouvelles fondations à côté des anciennes.
2. Ajouter chaque module de production au manifeste des strates dès son introduction.
3. Maintenir un chemin d’import depuis une racine publique contrôlée. Le vérificateur actuel rejette les modules de production orphelins.
4. Mettre à jour les racines de Lake ou les imports de façade de manière cohérente avec ce contrôle.
5. Écrire les adaptations de comparaison comme telles, sans introduire une seconde autorité scientifique.
6. Migrer un groupe cohérent de consommateurs à la fois.
7. Retirer une adaptation lorsqu’aucun consommateur ne dépend plus de l’ancienne signature.
8. Supprimer une ancienne définition uniquement après la comparaison de sa portée et la migration de tous ses usages.
9. Réécrire les commentaires et audits autour des objets réellement autoritatifs.

Les racines contrôlées sont actuellement énumérées aussi dans `scripts/check-stratification.ps1`, et `lakefile.toml` déclare les familles de modules construites. Introduire un module et son chemin public dans le même lot cohérent. Pendant la transition, une façade ne doit pas créer un cycle entre le namespace historique et ses nouveaux remplaçants. Le code de comparaison dépend des deux versions ; le noyau nouveau ne dépend pas de la version ancienne.

### Critère de sortie

Les anciennes couches n’existent plus comme autorités concurrentes. Les façades éventuelles sont de simples exports. Chaque résultat public a une seule chaîne scientifique identifiable.

## 22 Phase de raccord avec la computation

### Périmètre

Les points de raccord observés comprennent `RelationalPerimeter.Computation.ConstitutiveGeneration`, `CausalFoundationBridge` et les utilisateurs directs de `ExactTypeTransport`. La liste complète des usages de noms et de projections doit être établie avant migration ; un inventaire d’imports directs ne suffit pas.

### Travail

1. Rebrancher `ConstitutiveGeneration` sur la nouvelle constitution canonique.
2. Préserver l’itération de l’histoire depuis le périmètre effectivement constitué.
3. Préserver la séparation ancien et nouveau à chaque successeur.
4. Préserver le transport exact d’occurrences ajouté par un pas.
5. Vérifier les accords « ancien » et « frais » au niveau des applications réelles.
6. Rebrancher le champ d’histoire constituée de `CausalConstitutiveState` sans le remplacer par sa profondeur ou sa longueur.
7. Préserver la distinction entre histoire constituée et état opérationnel.
8. Préserver l’autorité des formations et provenances utilisées par les rôles computationnels.
9. Examiner les chaînes d’indices dépendant directement de `examplePresentation`.
10. Préserver les résultats publics de profils, images opérationnelles, obligations et largeurs avec leurs portées actuelles.
11. Vérifier qu’un raccord ne reconstruit pas une nouvelle exécution à partir d’un résultat terminal.
12. Mettre à jour la stratification et les frontières d’import au moment où les interfaces changent.

### Limites

Le plan ne promet pas une généralisation des conclusions computationnelles à toutes les nouvelles présentations. Il exige d’abord une continuité de leur instance actuelle. Une extension de leur classe de problèmes sera un résultat distinct.

### Critère de sortie

Les applications consomment les nouvelles fondations sans identité de façade trompeuse ni remplacement de la constitution par un readout. Les résultats et leurs quantificateurs sont vérifiés sur les nouvelles sources.

## 23 Catalogue des preuves et modèles exigés

| Famille | Résultats minimaux |
|---|---|
| Histoire | Composition, plongements, séparation, couverture composée et retours |
| Places | Élimination relationnelle, précédence, adjacence et transports |
| Formation | Témoins exacts, conservation historique et distinction des registres |
| Réalisation | Deux retours, accord inverse et rigidité séparée |
| Frontière | Interfaces exactes, fibre fermante et conservation du témoin |
| Rôles complets | Exhaustivité relative, séparation et conservation des branches |
| Intérieur | Déploiement, décodage, couverture et exclusion finale justifiée |
| Composition globale | Détermination canonique, ordre, adjacence et factorisation |
| Résidu | Exclusion intérieure, unicité conditionnelle et existence positive |
| Reconstruction | Conditions exactes, inverse reconstruit et unicité pointwise |
| Interprétation finale | Occurrence produite, formation, provenance et jonction distinguée |
| Obstruction | Conservation, contraction et rejets séparés |
| Régime | Classification, continuation hors régime et diagnostic |
| Tournant | Raccords entre la continuation, le résidu, l’interprétation et l’admission |
| Quantité | Définition équipée, projections et critère de comparaison |
| Transport constitutif | Fibres, témoins, opérations, branches et lois de composition |
| Cardinalisation | Transport vers `Fin`, retours et mesures de préfixes |
| Interprétation concrète | Occurrences exactes et distinction morphisme équivalence |
| Migration | Accords des exports et des consommateurs |

### Modèles obligatoires

1. Réalisation triviale sans rigidité.
2. Fibre finale uniforme sur frontières distinctes.
3. Transport de fibres ne conservant pas un témoin distingué.
4. Rôles complets permutables sans conservation des branches.
5. Lecture constante sur occurrences distinctes.
6. Trace localement exacte mais permutée.
7. Trace ordonnée mais intercalée sans pont constitutif effectif.
8. Génération non canonique avec données de lecture insuffisantes.
9. Frontière structurelle sans témoin fermant fourni.
10. Circularité positive sans obstruction imposée par l’interface.
11. Présentation obstruée autonome avec première continuation.
12. Continuation à deux occurrences distinctes incompatible avec le même étiquetage résiduel fidèle.
13. Interprétation préservant les occurrences tout en oubliant du contenu.
14. Chaîne de formation conservant la provenance historique et produisant un registre actuel distinct.

Chaque modèle doit viser une inférence précise. Les tests qui reproduisent seulement une définition ne remplacent pas ces modèles.

## 24 Contrôles techniques et contrôle du sens

### Contrôles techniques

- Construction des modules touchés et de leurs consommateurs directs.
- Blocs d’audit présents, terminaux et sans dépendances interdites.
- Absence des termes et architectures interdits par le vérificateur.
- Manifeste de strates complet, sans modules orphelins ni dépendances inversées.
- Contrôles des frontières d’import et de leurs autotests lorsque modifiés.
- Cas d’échec attendus pour les interfaces dont les hypothèses ont changé.
- Construction complète et `scripts/verify.ps1` aux jalons globaux et à la fin de la migration.
- Vérification de la différence Git sans altérer le travail préexistant.

### Contrôle du sens

Pour chaque certificat composé, vérifier :

1. Que les données concernent la même présentation et construction.
2. Que l’occurrence consommée est celle produite par la continuation.
3. Que le témoin relationnel conservé est le témoin autoritatif.
4. Que les accords exacts ne sont pas remplacés par égalité de lecture.
5. Que le rôle final, la jonction et le pas engendré restent distincts.
6. Que le régime ajoute explicitement ses propres obligations.
7. Que la portée des théorèmes reste relative aux hypothèses utilisées.
8. Que les résultats minimalement logiques sont situés sans être confondus avec leur chaîne riche.
9. Que la cardinalisation intervient comme projection démontrée.
10. Que les adaptations ne sont pas appelées équivalences sans leurs inverses et cohérences.

### Portée des vérifications

Une recherche d’identifiants, un contrôle d’import ou un compteur d’arguments ne démontre pas la nécessité logique d’un champ. Les analyses de dépendance sont appuyées par les preuves et les modèles séparateurs. La nécessité déclarée reste relative à la signature et au raisonnement examinés.

## 25 Jalons et ordre de réalisation

| Jalon | Contenu | Condition de validation |
|---|---|---|
| Référence protégée | État de départ et consommateurs | Travail préexistant récupérable |
| Contrat stabilisé | Notions et portées | Les contre-exemples ne réfutent aucun énoncé annoncé |
| Succession autonome | Histoire, épine et formation | Aucun import de circularité ou de computation |
| Intérieur délimité | Réalisation, frontière et rôles complets | Théorème composé et modèle positif |
| Composition comprise | Exactitude locale et factorisation | Modèles de permutation et d’intercalation |
| Tournant construit | Continuation, résidu, interprétation et régime | Une seule chaîne avec accords de provenance |
| Quantités comparables | Signature et transports constitutifs | Inversion et composition cohérentes |
| Quantité cardinalisée | Transport explicite vers `Fin` | Retours et ordre des imports vérifiés |
| Instance complète | Exemple périmétral et modèles | Toutes les couches possèdent des habitants |
| Applications migrées | Consommateurs computationnels | Même portée scientifique vérifiée |
| Fondations publiques | Façades et documentation | Aucune ancienne autorité concurrente |

L’ordre n’est pas strictement linéaire. Les outils neutres et l’inventaire documentaire peuvent avancer indépendamment des choix de frontière. Les lois générales de transport peuvent être développées après le premier jalon d’intérieur délimité. En revanche, on ne migre pas la computation avant une instance périmétrale complète et comparée.

Ce plan ne fixe pas de durée calendaire : la composition des transports dépendants, les choix de rigidité et les raccords computationnels doivent d’abord être éprouvés. L’avancement sera mesuré par les résultats et critères de sortie, plutôt que par un pourcentage de fichiers réécrits.

## 26 Risques mathématiques et réponses prévues

| Risque | Signal | Réponse |
|---|---|---|
| Réalisation trop forte | Unicité annoncée depuis les seuls retours | Ajouter une couche de rigidité ou restreindre l’énoncé |
| Frontière nominale | Paramètre ignoré et aucune loi de transport | Équiper les rôles et démontrer leurs raccords |
| Généralité excessive | Signature universelle sans première instance | Construire le cas suffisant puis généraliser les schémas établis |
| Obstruction primitive cachée | Circularité contient déjà le rejet désiré | Séparer la présentation positive et son enrichissement obstrué |
| Résidu utilisé comme décoration | Interprétation ignore l’occurrence produite | Exporter les accords de consommation de l’occurrence |
| Canonicité exportée sans condition | Curseur supposé déterminer tout pas générique | Localiser les théorèmes dans l’instance canonique |
| Équivalence appauvrie | Retours de porteurs sans cohérence de témoins | Exiger les transports de fibres et les accords distingués |
| Façades persistantes | Deux définitions autoritatives concurrentes | Migrer les consommateurs et retirer l’ancienne autorité |
| Migration par valeur | Profondeur ou largeur utilisée à la place d’une histoire | Conserver la constitution et prouver ses projections |
| Réécriture sans gain | Noms changés mais mêmes ambiguïtés | Relier chaque modification à une décision et un modèle |
| Tests trop faibles | Compilation seule ou tests miroir | Utiliser les modèles séparateurs et comparer les signatures |
| Portée élargie abusivement | Exemple transformé en théorème universel | Conserver les quantificateurs et distinguer les extensions de théorie |

## 27 Définition de l’achèvement

Le chantier sera achevé lorsque les conditions suivantes seront réunies :

1. Les primitives et toutes les notions fondamentales possèdent des interfaces explicites.
2. Les places et occurrences sont construites dans des couches distinctes et exactement reliées.
3. La réalisation distinguée et la rigidité sont correctement séparées.
4. La frontière et le témoin fermant ont une origine relationnelle commune vérifiable.
5. La clôture des rôles et la délimitation intérieure ont la portée annoncée.
6. La circularité positive ne reçoit pas implicitement toutes les obstructions ultérieures.
7. Le résidu général et son interprétation périmétrale sont raccordés à la même continuation.
8. La sortie de régime dépend d’obligations explicitement choisies.
9. La quantité structurelle possède un critère de comparaison constitutif démontré.
10. La cardinalisation possède un transport réversible du porteur fini déjà constitué vers `Fin`, et la lecture du seul naturel est explicitement reconnue comme une projection qui oublie de la structure.
11. Les modèles positifs et séparateurs éprouvent les inférences essentielles.
12. Les applications existantes consomment une seule fondation autoritative.
13. Les contrôles Lean et les vérificateurs du projet passent.
14. La documentation distingue les résultats acquis des généralisations encore ouvertes.

Le critère décisif est la possibilité d’expliquer et de suivre, dans les types et les preuves, pourquoi chaque donnée appartient à la constitution de l’objet étudié et ce que les comparaisons conservent de cette constitution.

## 28 Premier lot concret

Le premier lot d’implémentation recommandé comprend seulement :

1. La référence protégée et l’inventaire des consommateurs.
2. Le contrat fondationnel avec les trois premiers contre-exemples.
3. L’histoire générique avec composition et séparation des occurrences.
4. L’épine relationnelle et les éliminateurs de positions.
5. Une présentation successive minimale et une algèbre de génération positive avec ses accords.
6. La décomposition distinguée abstraite et l’accord inverse dérivé.
7. La frontière autonome et le rôle final équipé.
8. Un premier modèle habité, son déploiement intérieur autonome et les accords de réalisation complète.
9. Le théorème de délimitation distinguée, puis sa variante rigide sous ses hypothèses explicites.

Ce lot se termine sur un résultat mathématique complet. Il ne doit pas se disperser dans la migration computationnelle ou dans une signature universelle avant que cette première articulation ait été éprouvée.

## 29 Sources et références du chantier

- [Texte conceptuel fourni par l’utilisateur](<C:/Users/frederick/.codex/attachments/263ad19d-ee81-4cd1-94b4-af8544d25f63/Pasted text.txt>) : Décomposition en rôles relationnels constitutifs circularité et quantification structurelle, notamment §§ 1 à 68.
- [Transport exact](C:/Users/frederick/Documents/relational-perimeter/ExactTypeTransport.lean:12).
- [Détermination résiduelle](C:/Users/frederick/Documents/relational-perimeter/SegmentedResidualRole.lean:106) et [reconstruction intérieure](C:/Users/frederick/Documents/relational-perimeter/SegmentedResidualRole.lean:436).
- [Interfaces de tournant](C:/Users/frederick/Documents/relational-perimeter/AbstractSegmentedTurning.lean:268) et [régime couplé](C:/Users/frederick/Documents/relational-perimeter/AbstractSegmentedTurning.lean:644).
- [Présentation périmétrale](C:/Users/frederick/Documents/relational-perimeter/StrongPerimetralTurning.lean:209), [rôle final](C:/Users/frederick/Documents/relational-perimeter/StrongPerimetralTurning.lean:267), [réalisation](C:/Users/frederick/Documents/relational-perimeter/StrongPerimetralTurning.lean:4515) et [interprétation finale](C:/Users/frederick/Documents/relational-perimeter/StrongPerimetralTurning.lean:5700).
- [Génération pour la computation](C:/Users/frederick/Documents/relational-perimeter/RelationalPerimeter/Computation/ConstitutiveGeneration.lean:1).
- [Pont causal](C:/Users/frederick/Documents/relational-perimeter/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/CausalFoundationBridge.lean:1).
- [Vérification du projet](C:/Users/frederick/Documents/relational-perimeter/scripts/verify.ps1:1) et [manifeste des strates](C:/Users/frederick/Documents/relational-perimeter/scripts/stratification.tsv:1).

Les chemins proposés, interfaces schématiques et noms de nouveaux résultats sont des éléments de planification. Ils ne doivent pas être cités comme des déclarations déjà présentes dans le dépôt.

## 30 Traçabilité du texte conceptuel et critères de révision

### Correspondance des sections

Cette table couvre les sections 1 à 68 du texte fourni. Elle distingue la reprise de son intention des corrections nécessaires pour obtenir des énoncés démontrables. Le texte source reste une référence indépendante ; le plan ne doit pas réécrire silencieusement ses affirmations.

| Sections du texte | Destination dans le plan | Condition de reprise |
|---|---|---|
| 1 à 3 | 1, 6, 9 | Constitution relative, univers et témoins primitifs explicités |
| 4 et 5 | 17 | Signature suffisante, cas vide et réalisation triviale admis |
| 6 et 7 | 8 | Places construites avant les occurrences réalisatrices |
| 8 et 9 | 7, 9 | Occurrences indexées par une construction, indépendantes de leur lecture |
| 10 à 14 | 10 | Décomposition distinguée et accord inverse ; rigidité séparée |
| 15 à 18 | 8, 9, 11 | Succession et circularité séparées ; positions inductives |
| 19 et 20 | 11 | Frontière structurelle distincte de son témoin positif |
| 21 à 24 | 6, 11 | Inductif final contractile ; ne pas attribuer à son index une invariance que les morphismes ne démontrent pas |
| 25 à 27 | 11 | Clôture relative à la somme des rôles construite |
| 28 et 29 | 12 | Déploiement exact et classification intérieure |
| 30 à 32 | 10, 12 | Inégalité d’étiquette distincte de non-réalisation ; pont relationnel et rigidité explicités |
| 33 et 34 | 17 | Quantité intérieure distincte de son environnement circulaire |
| 35 à 39 | 17 | Transports des porteurs et fibres, avec cohérence des témoins et opérations retenues |
| 40 | 17 | Accord inverse dérivé, non redondant comme donnée primitive |
| 41 à 44 | 17 | Inversion et composition démontrées pour la signature implémentée |
| 45 et 46 | 7, 14 | Continuation positive et recomposition bien typées ; injections d’occurrences séparées |
| 47 à 50 | 14, 15 | Détermination d’étiquette et sous-singleton ; réalisation finale ajoutée par un pont explicite |
| 51 à 53 | 15 | Interprétation raccordée au pas réel ; `j★` reste distinct du rôle et du pas |
| 54 à 56 | 16 | Admission séparée ; classification et sortie conditionnelles au régime |
| 57 et 58 | 16, 17 | Chaîne couplée et quantité circulaire équipée |
| 59 | 18 | Transport vers `Fin` dérivé ; nombre seul insuffisant pour reconstruire la constitution |
| 60 | 12, 14, 15, 16, 17 | Théorème composé avec les hypothèses de génération, de réalisation finale et de régime nécessaires |
| 61 à 65 | 1, 6, 11, 17 | Synthèse relative au domaine constitué, sans refondation implicite de Lean |
| 66 | 19, 21 | Correspondances de l’instance démontrées, non déduites de ressemblances de noms |
| 67 et 68 | 3, 25, 28 | Statut conceptuel distingué du statut formel ; première instance avant généralisation complète |

### Conditions de révision du chantier

Avant de passer à l’étape suivante, examiner le modèle positif et les contre-modèles de l’étape terminée. Si la preuve demande un champ absent de l’interface, corriger l’énoncé ou ajouter explicitement l’hypothèse ; ne pas l’introduire dans un constructeur sous un nom anodin. Si un modèle séparateur ne peut pas être formulé parce que l’interface faible contient déjà le résultat fort, revoir la séparation des couches.

Les décisions de rigidité, de signature et de génération non canonique restent ouvertes au sens indiqué en section 3. Le premier lot peut avancer avec la décomposition distinguée, une signature concrète et un générateur canonique démontré, à condition de ne pas exporter leurs propriétés comme universelles.

Le plan révisé donne un ordre de travail et des obligations précises. Il ne démontre pas encore la faisabilité de toutes les abstractions Lean proposées. La validation formelle des nouveaux énoncés sera acquise par leurs preuves et leurs modèles, au fil des jalons.
