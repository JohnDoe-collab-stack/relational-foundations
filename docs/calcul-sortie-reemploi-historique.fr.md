# Calcul, sortie et réemploi historique

Le calcul construit désormais sa succession opérationnelle à partir des sorties qu'il produit. Chaque demande peut réemployer une ressource antérieure par son adresse exacte. Les prolongements conservent les ressources, leurs valeurs, leurs distinctions et leurs dépendances ; leurs compositions conservent aussi l'histoire effectivement produite.

Ce développement ferme les trois raccords demandés pour la méthode : sortie vers pas opérationnel, réemploi vers ressource identifiée, puis conservation et composition sur la chaîne complète. Il établit aussi la couverture exacte des histoires admissibles définies indépendamment de l'exécuteur. Pour chacune, un constructeur produit l'exécution, le support fini, la correspondance exhaustive entre obligations et ressources, les certifications et la garantie terminale.

## Comment un pas est constitué

[OutputDriven.lean](../RelationalFoundations/OutputDriven.lean) conserve dans chaque `Frame` l'état atteint, l'histoire produite, le support constitué et l'adresse du résultat courant. Deux procédures locales définissent une `Rule` : `plan` construit une demande depuis ce contexte ; `react` construit un état suivant et un témoin effectif de relation depuis le résultat réalisé.

`Rule.advance` effectue cette chaîne dans cet ordre :

1. `plan` constitue une expression finie dont les références désignent des ressources déjà présentes.
2. Le producteur réalise cette expression en lisant les ressources désignées.
3. `react` reçoit exactement la sortie produite et construit le témoin du pas opérationnel.
4. L'histoire est prolongée par ce témoin, le support par cette expression, et le résultat courant reçoit une nouvelle adresse.

`advance_output` et `advance_history` identifient respectivement le résultat réalisé et le témoin ajouté à l'histoire. `Rule.run` répète la procédure depuis une configuration initiale. Son entrée `depth` donne le nombre de réactions demandées. La fermeture de chaque expression suit sa construction structurelle ; la taille de ses ressources est lue après leur constitution.

La règle est une donnée primitive effective. La dépendance au résultat est explicitement réalisée par l'exécuteur ; une propriété particulière du choix ou de la réaction appartient aux preuves de la règle considérée. Dans la famille réalisée ci-dessous, le résultat précédent détermine le token suivant, et le résultat nouvellement produit détermine le témoin du pas suivant.

## Les ressources et leurs références

[ResourceGraph.lean](../RelationalFoundations/ResourceGraph.lean) définit les quatre règles de production et traite tous leurs constructeurs.

| Règle | Dépendances constituées | Production |
|---|---|---|
| Sortie vide | Aucune | Liste vide |
| Émission | Aucune | Liste contenant le token donné |
| Composition | Les deux positions internes, dans leur ordre | Concaténation de leurs valeurs |
| Réemploi | Adresse exacte d'une ressource antérieure | Lecture de cette ressource |

Une expression conserve ses positions internes. Le support conserve les expressions et leurs liens vers les ressources antérieures. Les types imposent que chaque référence soit une adresse du support disponible au moment où l'expression est constituée. La fermeture couvre ainsi les quatre règles, leurs positions internes et leurs références historiques.

`Support.nodeAt` donne le constructeur et les références directes d'une ressource. `dependencies` en extrait une liste ordonnée : deux positions peuvent désigner une même ressource. `read_correct` démontre, pour toute ressource de tout support construit, que sa valeur respecte la règle locale et ses références.

`Shape.positions_complete`, `positions_nodup`, `Layout.addresses_complete` et `addresses_nodup` donnent une énumération exhaustive sans répétition des adresses. `addresses_length` relie sa longueur à la taille lue sur le support. Les positions et leurs relations sont donc constituées avant cette lecture numérique.

Le réemploi conserve le lien vers l'ancien nœud. La lecture récursive peut recalculer sa valeur depuis l'expression conservée. Les preuves portent sur l'identité de la ressource et de ses dépendances ; une politique de cache et sa complexité constituent un sujet supplémentaire.

## Ce qui reste identique pendant la continuation

Une `Extension` conserve les expressions effectivement ajoutées. Ses preuves valent pour toute extension finie de la grammaire, quelles que soient les valeurs des tokens et les références réemployées.

| Résultat | Théorème | Portée |
|---|---|---|
| Les anciennes adresses restent distinctes | `embed_injective` | Toute extension finie |
| La valeur d'une ancienne ressource est conservée | `read_preserved` | Chaque adresse antérieure |
| Son constructeur et ses références sont conservés | `node_preserved` | Le nœud complet, avec les adresses prolongées |
| Ses dépendances gardent leur ordre et leurs positions répétées | `dependencies_preserved` | Liste exacte des dépendances |
| Les relations entre anciennes ressources se conservent dans les deux sens | `relation_preserved`, `relation_reflected` | Toute paire d'adresses antérieures |
| Deux prolongements composent leurs adresses | `embed_compose` | Toute paire d'extensions composables |
| Trois prolongements s'associent | `compose_associative` | Toute triple d'extensions composables |

`Execution` raccorde ces extensions à la succession opérationnelle produite par une `Rule`. `history_exact` prouve que la continuation contient exactement les témoins qui prolongent l'histoire initiale. `resources_compose`, `continuation_compose` et `embed_compose` conservent ensemble le support, l'histoire et les références.

`run_add` établit une égalité du `Frame` entier : exécuter `a + b` réactions ou exécuter `a`, puis `b` depuis le résultat atteint donne exactement la même configuration. Cette égalité comprend l'état, l'histoire, le support et l'adresse courante.

## Une famille dont la chaîne est entièrement démontrée

[HistoricalFeedback.lean](../RelationalFoundations/HistoricalFeedback.lean) traite tout type de tokens et toute procédure totale `choose : List Token → Token`.

À chaque réaction :

1. `choose` reçoit la sortie courante effectivement lue dans le support.
2. La nouvelle demande compose l'émission du token choisi et le réemploi de l'adresse courante.
3. Cette demande produit `token choisi :: sortie précédente`.
4. Le producteur du pas reçoit ce résultat et construit un témoin `Step.record` portant le token produit.

`reuse_reference` et `reuse_link` identifient l'ancienne ressource à laquelle le réemploi est relié. `reuse_is_fresh` distingue la nouvelle occurrence du réemploi et la ressource qu'elle désigne. `advance_history` identifie le token effectivement inscrit dans le nouveau témoin opérationnel.

La spécification `trajectory` est définie séparément par récurrence sur les listes. `run_output` prouve que le résultat construit lui est égal pour toute longueur finie. `state_eq_output` et `trace_eq_output` prouvent, pour toute exécution issue de la configuration initiale, l'accord entre l'état atteint, la trace des témoins produits et la sortie réalisée. La garantie terminale est ainsi dérivée des règles mises en œuvre.

`run_size` établit une taille de `1 + depth * 3` ressources. Chaque réaction ajoute les trois positions de la composition, de l'émission et du réemploi. Les expressions antérieures restent partagées par adresse. `supports_unbounded` démontre que cette famille dépasse toute borne finie commune, tout en conservant une énumération finie pour chaque exécution.

[Tests/OutputDriven.lean](../Tests/OutputDriven.lean) contrôle les distinctions essentielles : valeurs identiques avec références différentes, deux positions de réemploi vers une même ressource, conservation d'un lien de réemploi après continuation et égalité du calcul fractionné. Une procédure binaire qui alterne depuis la tête de la sortie produite fournit aussi un contrôle exécuté des témoins opérationnels.

## Les histoires admissibles définies indépendamment

[FeedbackCoverage.lean](../RelationalFoundations/FeedbackCoverage.lean) fixe le périmètre avant de construire une réalisation. Les données primitives sont un type quelconque `Token` et une procédure totale `choose : List Token → Token`. La relation opérationnelle possède le constructeur `Step.record source token`, qui relie `source` à `token :: source`.

`LocalAdmission choose step` exige que le token porté par ce témoin soit `choose source`. `Admissible choose history` exige cette condition à chaque occurrence de l'histoire ; l'origine est admise. Cette définition consulte les états opérationnels et les témoins. Le support, les ressources, l'exécution et la conclusion terminale interviennent ensuite dans la construction et ses preuves.

Pour un `choose` fixé, le périmètre comprend exactement les histoires finies depuis la liste vide qui respectent cette condition locale. Il est déterministe. Les théorèmes sont quantifiés sur tout type de tokens, toute procédure totale de choix et toute histoire de ce périmètre. Le type `Step.record` permet aussi des témoins portant d'autres tokens ; les tests démontrent explicitement leur exclusion lorsque la condition locale échoue.

`build choose history admitted` procède par récurrence structurelle sur l'histoire fournie. À l'origine, il construit le support vide initial. À chaque prolongement, il poursuit depuis le support du préfixe par le producteur existant. La sortie réalisée détermine le nouveau témoin. La preuve locale d'admission sert à établir l'accord de ce témoin produit avec celui de l'histoire fournie.

La donnée retournée contient une véritable `Execution`, ainsi que l'égalité du couple dépendant « état atteint, histoire avec ses témoins » avec le couple fourni. Cette égalité porte sur toute l'histoire ; elle préserve davantage que sa longueur ou la valeur terminale.

`coverage_iff` établit les deux sens : une histoire est admissible exactement lorsqu'elle possède une réalisation par cette règle. `generated_iff_admissible` donne la même caractérisation pour `Rule.run`. `admitted_history_exact` identifie l'histoire fournie à l'histoire produite à sa propre longueur. Ces théorèmes raccordent les conditions indépendantes à l'exécution existante.

## Toutes les obligations et leurs certifications

`Demand history` décrit les obligations depuis l'histoire opérationnelle, avant la construction du support : une obligation initiale et, pour chaque occurrence, trois rôles distincts. Leurs valeurs attendues et leurs prérequis se définissent depuis les états et le token du témoin.

| Obligation | Valeur attendue indépendante | Prérequis ordonnés |
|---|---|---|
| Origine | Liste vide | Aucun |
| Émission d'une occurrence | Liste contenant le token de son témoin | Aucun |
| Réemploi d'une occurrence | État source de son témoin | Résultat de l'occurrence précédente, ou origine au premier pas |
| Résultat d'une occurrence | État cible de son témoin | Émission, puis réemploi de cette occurrence |

`locate` construit l'adresse de chaque obligation dans le support réalisé. `classify` retrouve l'obligation de chaque adresse. `classify_locate` et `locate_classify` prouvent leurs deux identités de retour. `demandTransport` réunit cette correspondance exacte. Deux obligations distinctes conservent ainsi des ressources distinctes, même lorsque leurs valeurs sont égales.

`fulfills` démontre la valeur attendue pour chaque obligation. `every_resource_certified` étend cette certification à chaque adresse du support grâce à la correspondance inverse. `dependencies_covered` prouve l'égalité de la liste effective des références directes avec la liste déclarée des prérequis, transportée par `locate`. L'ordre et les positions répétées sont conservés par cette égalité de listes.

Les certifications sont elles-mêmes produites : la preuve sémantique suit la structure de l'histoire et la preuve locale de chaque nœud suit les quatre producteurs de `ResourceGraph`. Pour cette instance, leur production utilise les ressources construites et leurs références, avec les définitions des règles et les preuves locales d'admission. Le constructeur fournit ces preuves pour tous les nœuds ; aucune demande de certification extérieure au support de cette instance n'est laissée à réaliser.

## La construction complète et sa continuation

`complete` produit un `CompleteRealization`. Ses entrées sont le type des tokens, `choose`, l'histoire et sa preuve d'admission locale. Les champs produits réunissent :

1. L'exécution effective et la reconstruction exacte de l'histoire fournie.
2. La correspondance dans les deux sens entre toutes les obligations et toutes les adresses.
3. Les valeurs certifiées de toutes les obligations et la certification locale de tous les nœuds.
4. La couverture exacte de leurs dépendances ordonnées.
5. Une énumération exhaustive des ressources, sans répétition, et la preuve de sa longueur.
6. L'égalité du résultat produit avec l'état terminal de l'histoire.

`complete_coverage_iff` caractérise exactement les histoires qui possèdent cette réalisation complète. `complete_size` lit ensuite la taille du support : `1 + history.length * 3`. La construction par `build` reçoit l'histoire elle-même et suit ses constructeurs ; cette taille est un résultat. `admitted_supports_unbounded` transporte la preuve acquise d'absence de borne commune vers ce périmètre indépendamment déclaré.

`resume` poursuit le support effectivement construit pour le préfixe. Lorsque le suffixe satisfait ses propres conditions locales, `resume_equals_build` établit l'égalité de la configuration entière avec la construction de l'histoire composée. `resume_history_exact` identifie tous ses témoins à ceux du préfixe suivi du suffixe. `admissible_append` établit que l'admission de cette composition équivaut à l'admission de ses deux histoires.

`resume_preserves` conserve le nœud complet de chaque ancienne ressource, avec ses références prolongées. `resume_certified_old` conserve sa certification relativement à son obligation historique. `resume_dependencies_preserved` conserve la liste de ses dépendances ; `resume_relation_iff` conserve et reflète les relations entre anciennes adresses. L'injectivité du transport est celle de l'exécution effective. `resume_transport_compose` compose les adresses de deux continuations ; `resume_compose` compose leurs configurations complètes. Ces preuves réutilisent les conservations déjà établies dans `OutputDriven` et `ResourceGraph`.

La garantie terminale est obtenue par `complete.terminal` depuis les producteurs et la reconstruction. `admitted_target` la raccorde aussi à la spécification indépendante `trajectory`. Les conditions d'admission n'exigent aucune de ces conclusions terminales.

`admissionDecision` contrôle effectivement les conditions locales lorsque l'égalité des tokens est décidable. `check` retourne alors soit la réalisation complète, soit une preuve que l'histoire échoue à ces conditions. `check_complete` et `check_rejects` prouvent ces deux comportements. L'égalité décidable est nécessaire à ce contrôle automatique ; les constructeurs `build` et `complete` fonctionnent pour un type quelconque de tokens.

[Tests/FeedbackCoverage.lean](../Tests/FeedbackCoverage.lean) construit ses histoires d'entrée directement avec `Step.record`, indépendamment de l'exécuteur. Il contrôle la reconstruction entière, les certifications, les liens de réemploi par identité historique, la continuation depuis le préfixe et la composition des transports. Les contrôles exécutés traitent l'origine, une histoire admise de quatre pas, un rejet dès le premier pas et un rejet après un préfixe admis.

## Portée du résultat

La fermeture structurelle est entièrement construite pour les quatre règles déclarées. L'exécuteur traite toute paire de procédures locales `plan` et `react` de son interface. La famille `HistoricalFeedback` ajoute une garantie sémantique indépendante pour toute procédure totale de choix et toute longueur finie. `FeedbackCoverage` ferme la couverture des histoires admissibles de cette famille, avec leurs obligations, leurs certifications et leur conservation historique.

Les primitives sont le type des tokens, les règles de production et les procédures locales. Les supports et les témoins opérationnels sont construits pendant l'exécution. Les preuves générales et celles de la famille réalisée rendent explicite cette distinction.

Une application à d'autres jugements sémantiques doit déclarer ses propres constructeurs, leurs obligations et leurs producteurs, puis établir leur adéquation. La fermeture des univers d'un vérificateur évoquée dans le document méthodologique reste une application distincte. Le résultat achevé ici est la chaîne complète, sur le périmètre explicite : admissibilité indépendante, couverture des obligations, réalisation positive, support fini conservé et composé, puis garantie extraite.

[Calcul hétérogène et réemploi historique typé](calcul-heterogene-historique.fr.md) réalise cette chaîne dans une seconde famille, avec des valeurs numériques et booléennes et des références portant leur sorte. Ce développement étend le périmètre réalisé tout en conservant les résultats de la présente famille.

La vérification est consignée dans [verification-result.json](verification-result.json) et [le rapport de migration](../Migration/verification-result.json). Elle couvre compilation, audit exhaustif des axiomes, rejets attendus et cohérence du projet migré dans notre dossier isolé.

La vérification du 2 octobre 2026 a réussi : 50 fichiers de fondations et de tests, 3 951 déclarations auditées sans axiomes, 174 sources migrées et 806 symboles publics contrôlés. Les 24 rejets attendus, la stratification des 154 modules de production migrés et les quatre frontières d'import passent. Commande utilisée : `pwsh -NoProfile -File scripts/verify.ps1 -SkipComparison -SkipReference`. Les comparaisons et empreintes du dépôt historique sont explicitement omises dans cette vérification du dossier isolé.
