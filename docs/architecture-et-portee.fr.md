# Architecture mathématique et portée des fondations indépendantes

Ce document précise les objets construits, les raccords démontrés et la portée des comparaisons. Le bilan `achevement.fr.md` décrit aussi la copie complète migrée. La bibliothèque est une formalisation relative : elle reçoit des types et familles relationnelles primitifs, puis construit les places, occurrences et quantités du domaine étudié. Elle ne remplace pas les règles de Lean.

## Primitives et autorité des données

`Spine Next node` reçoit un nœud et une famille `Next : Node → Node → Type`. Chaque avancée stocke son témoin particulier. `Spine.Position` est inductif, avec `here` et `later`, et ne possède aucun constructeur sur une frontière vide. Une position retrouve une source, une cible et le témoin précis de son avancée.

`History Step source target` reçoit les pas eux-mêmes. Ses occurrences sont les positions des pas dans cette histoire. Les sommets d’une histoire positive sont distincts comme positions, même lorsqu’une histoire revient au même état. Le modèle de boucle sur `Unit` vérifie cette distinction. Une lecture constante ne peut pas identifier les occurrences.

La première algèbre de génération est libre : ses constructeurs initial et formé produisent `Formation`, en conservant le terme précédent et le nouveau témoin. Les éliminateurs, la correspondance avec l’histoire et les registres de formation sont démontrés. Cette construction est disponible pour toutes les familles de pas ; aucun successeur choisi dans une fibre arbitraire n’est obtenu sans donnée positive. La continuation reçoit donc son témoin explicitement.

`Formation.Record` distingue un registre actuel des registres anciens préservés. Son type contient l’origine complète de la formation. La séparation concerne ces registres équipés ; leurs valeurs lues pourraient coïncider. `ObstructedFormation` ajoute une obstruction à la racine et la conserve réellement dans les constructeurs. Son éliminateur lit la donnée stockée, et les preuves de conservation sont constructives.

## Réalisation et délimitation

`ExactRealization` stocke un transport à deux retours et un accord de réalisation. L’accord inverse est dérivé en transportant seulement la variable d’occurrence. Le rôle doit rester fixé pendant ce transport dépendant.

La rigidité des rôles et celle des occurrences sont des propriétés supplémentaires, équivalentes sous les deux retours. Elles ne signifient pas unicité des témoins. Le modèle de réalisation triviale sur `Bool` possède une décomposition exacte distinguée et réfute la rigidité.

Pour le déploiement intérieur, `InteriorRealizes` conserve l’identité de l’occurrence distinguée et l’égalité du pas situé. Cette identité est une décision d’interface explicite, à partir de laquelle la rigidité est démontrée. Une simple égalité de pas situé pourrait être trop faible si la même donnée de pas apparaît plusieurs fois dans une histoire.

La réalisation complète intérieure ne possède que la branche intérieure. Son élimination démontre l’absence de réalisation finale. Il s’agit d’une grammaire relationnelle choisie et démontrée pour ce déploiement, pas d’une impossibilité portant sur toutes les relations de réalisation concevables.

La frontière fermante contient ses interfaces hétérogènes. `BoundaryFinalRole` en est une fibre inductive à un constructeur. Le système complet des rôles est une somme. Son exhaustivité et sa séparation sont relatives à cette grammaire. Une présentation positive n’inclut aucune obstruction de boucle ou admission de régime.

## Composition et ordre

La composition d’histoires fournit des plongements ancien et nouveau, leur séparation et une décomposition exacte du porteur composé. Les pas situés sont conservés par les plongements. L’ordre et l’adjacence du déploiement de l’épine sont préservés par sa réalisation naturelle.

Les modèles permuté et intercalé sont des traces avec accords locaux de pas situés. Leurs réalisations sont injectives. Le premier conserve les accords locaux mais inverse l’ordre ; le second conserve tout l’ordre et échoue sur l’adjacence. Leur portée est de séparer les interfaces faibles des compositions effectivement construites.

Les théorèmes historiques plus forts qui reconstruisent toute une constitution canonique depuis un curseur dépendent de son générateur spécialisé. Ils ne deviennent pas des théorèmes sur une famille `Next` arbitraire. Le pont de comparaison conserve la réalisation canonique historique et ses accords dans une instance de `ExactRealization` ; il ne supprime pas ces hypothèses de canonicité.

## Résidu et interprétation finale

La théorie résiduelle générale est indépendante de la circularité. Elle reçoit une conservation des anciens rôles, une séparation ancien et nouveau, un étiquetage injectif et un rôle résiduel contractile. Elle déduit une étiquette finale et le caractère sous-singleton du nouveau porteur. Elle conserve aussi la reconstruction constructive de l’inverse intérieur sous ses conditions exactes.

`FaithfulContinuation` fixe les plongements aux occurrences d’une véritable composition d’histoires. Une continuation positive fournit une occurrence. L’unicité résiduelle démontre structurellement qu’elle comporte exactement un pas, sans mesurer sa longueur. Ce pas est extrait de la continuation, et la recomposition vers `OneStepContinuation` est démontrée.

La classification finale seule ne produit pas un témoin de réalisation. `FinalRealizes` ajoute l’identité de l’occurrence générée et son pas exact. `BoundaryInterpretation` réunit cette occurrence, cette réalisation, le pas, la formation et la jonction primitive, avec leurs accords. La jonction n’est pas utilisée pour déterminer l’étiquette résiduelle.

## Tournant constitutif affirmatif

Le **tournant constitutif affirmatif** est une continuation effectivement engendrée, qui conserve les données constitutives antérieures et dont la nouvelle occurrence réalise le rôle de frontière avec ses accords d’interprétation. Le système des rôles reste fixé ; le changement concerne sa réalisation dans la construction prolongée. Dans la suite des documents, « tournant » est le nom court de cette notion.

Le générateur fournit le témoin positif de continuation. Sous les conditions de conservation, de séparation et de fidélité, le théorème résiduel détermine le rôle de la nouvelle occurrence et son unicité. L’interprétation raccorde cette même occurrence à son pas, à sa formation et à la jonction fermante. La génération, la détermination résiduelle et l’interprétation sont donc des opérations distinctes, liées par leurs accords.

`AffirmativeTurning` rassemble le contenu positif et l’interprétation. `TurningWithExit` ajoute une sortie démontrée du régime antérieur : la construction prolongée existe, mais n’y est pas admise. Cette sortie ne définit pas à elle seule un nouveau régime. Le qualificatif « affirmatif » porte sur le contenu effectivement construit ; les preuves de rejet restent des réfutations. Le rejet d’une totalisation ne fournit pas, à lui seul, un témoin de continuation.

Le tournant constitutif affirmatif couplé conserve les accords d’histoire, de formation et de nouvelle occurrence avec la continuation d’origine. La version directement à un pas et la version dérivée depuis le résidu sont comparées par leur témoin effectivement engendré.

## Régime et obstruction

`ExactRegime` reçoit une admission canonique et une classification de toute admission. Sa complétude est dérivée, sans stocker un champ redondant. Une construction différente est rejetée par cette classification. `ObstructedRegime` sépare l’analyse canonique ou tentative du rejet des tentatives.

L’obstruction sur les pôles est une donnée supplémentaire. La présence d’un témoin fermant ne fournit pas une égalité de pôles. L’exemple contient une jonction positive et une obstruction indépendante sur deux pôles booléens distincts.

Le régime de l’instance est défini par une admission canonique ou une tentative attachée à une continuation, son interprétation et une totalisation bilatérale. Cette obligation fait partie du choix de régime ; elle n’est pas une conséquence universelle de la circularité. Son analyse et le rejet donnent la classification exacte.

La spécification reste une famille d’entrée distincte dans `NormativeAdequacy`. Les deux implications peuvent être globales et constantes le long des occurrences. `CircularSpecification` construit désormais une spécification indépendante avec une hypothèse explicite de préfixe constitué, sa classification et son adéquation. La spécification historique riche, qui reconstruit le préfixe depuis son exactitude locale, est reprise dans les modules spécialisés de `Migration/Constitution`. Une normativité locale dépendant réellement des occurrences n’est pas postulée par cette adéquation globale.

## Quantités et signature

`StructuralQuantity` conserve les rôles, occurrences, fibres de réalisation, transport exact et accords distingués. `ConstitutiveEquiv` transporte les deux porteurs et le porteur total des témoins. Ses projections sur les rôles et occurrences commutent avec les transports. L’accord inverse de classification est dérivé.

Cette présentation par porteur total ne remplace pas une équivalence de fibres par un résultat plus faible. `FiberTransport` construit explicitement les équivalences des fibres `Realizes r o`, avec les deux retours. Il démontre aussi la cohérence des témoins distingués après le transport le long de l’accord direct. L’identité, l’inverse et la composition des transports totaux produisent les transports constitutifs ; leur existence est réflexive, symétrique et transitive.

Une signature d’incidence possède des sortes, des symboles, des ports et la sorte de chaque port. Son interprétation contient des porteurs, des types de témoins et des projections d’incidence. Un transport conserve les sortes et les témoins réversiblement, avec leurs accords pointwise. L’inversion et la composition sont démontrées sans égalité globale de fonctions.

Dans l’instance, les graphes de formation et provenance sont construits depuis les préfixes effectifs des occurrences. Le graphe de composition contient les deux histoires composables et leur composition effective. Les résultats de conservation des sources, des compatibilités effectives et de ce graphe sont des théorèmes, pas de simples intitulés de champs.

`EquippedQuantity` raccorde la réalisation au symbole de réalisation et à ses deux ports. `EquippedEquiv` impose l’accord entre les applications de porteurs du transport constitutif et celles de la signature, ainsi que l’accord du graphe des témoins. `MarkedQuantity` ajoute la conservation de témoins distingués supplémentaires. La jonction et la place finale sont les marques de l’instance circulaire.

Cette théorie ne promet pas une équivalence automatique entre signatures différentes, ni une métathéorie de toutes les opérations dépendantes arbitraires. Les opérations retenues sont représentées par des graphes typés, et leurs témoins sont préservés. Le modèle de signature vide reste disponible comme cas limite.

La portée de chaque graphe est celle de son domaine déclaré. La petite signature périmétrale reste un modèle concret. `CircularSignature` construit maintenant une quantité circulaire équipée pour une présentation générique, avec des relevés réversibles d’univers. Elle contient les graphes des formations arbitraires, de leurs cibles, des registres actuels et préservés et de leurs projections. Les accords de transport couvrent ces graphes.

`TransportLaws` expose les lois pointwise et démontre l’identité et la composition des transports des fibres de réalisation. Les transports équipés et marqués ont aussi leurs résultats d’existence réflexive, symétrique et transitive.

## Cardinalisation et interprétation concrète

La longueur est une lecture de l’inductif d’histoire. Le transport vers `Fin length` est construit avec ses deux retours. L’indexation adoptée est du plus récent vers le plus ancien ; elle fournit une cardinalisation et ne remplace pas la relation de précédence.

La stricte différence des constructions utilisée par certains certificats fermés de tournant est démontrée au moyen de cette lecture dérivée. La détermination résiduelle et la preuve qu’une continuation est exactement à un pas demeurent structurelles. `FiniteInvariance` démontre constructivement que deux porteurs `Fin` exactement transportés ont le même cardinal, puis applique ce résultat aux quantités et histoires cardinalisées.

Une interprétation concrète transforme les états et les pas dans un sens. Les occurrences de l’histoire interprétée gardent une correspondance réversible, avec conservation des pas interprétés. Cela ne rend pas réversible la transformation des témoins : l’exemple qui oublie une licence booléenne conserve les occurrences mais n’est pas fidèle sur ces témoins.

## Comparaison et intégration

La bibliothèque principale ne connaît pas les anciens namespaces. Le fichier de comparaison importe les deux projets dans un processus de vérification séparé. Il démontre les transports de places, de rôles finaux, d’histoires et d’occurrences, la conservation des pas et une réalisation exacte transportant les accords canoniques historiques.

La vue positive d’une ancienne présentation conserve les nœuds riches et leurs familles relationnelles primitives. Elle oublie délibérément les champs d’obstruction et de régime, dont la nouvelle couche positive n’a pas besoin. Cet oubli n’est pas annoncé comme une équivalence de toutes les données de présentation.

La nouvelle instance à quatre nœuds est autonome. Elle possède trois places intérieures, une frontière quatrième vers premier, une continuation vers un nœud libre, une quantité équipée, un régime obstrué et une génération itérable sans borne. Elle n’est pas une identité définitionnelle de tout le modèle historique des types retournés.

Les exports computationnels, les types retournés spécialisés et leurs résultats de factorisation ou de spécification sont migrés et vérifiés dans la copie `Migration`. Les entrées historiques y sont des façades et les couches spécialisées sont réparties. Les consommateurs utilisent les nouveaux transports, les histoires constituées et l’itération générique. Le dépôt initial reste conservé intégralement.

## Vérification constructive

L’audit central examine toutes les déclarations importées depuis les modules du projet et des tests, y compris les auxiliaires générés et les déclarations privées. Toute dépendance axiomatique entraîne un échec.

La génération automatique des lemmes `injEq` est désactivée, car Lean peut y introduire `propext` pour des égalités entre propositions. Les injectivités nécessaires sont démontrées directement. Certains éliminateurs et simplifications standard ont également été remplacés par des preuves explicites. Ce choix ne modifie pas les objets mathématiques ; il rend la contrainte constructive vérifiable sur toute la bibliothèque produite.

Le contrôle du dépôt initial compare le contenu et la liste des fichiers à la référence enregistrée. La source est conservée dans une archive locale récupérable. Les comptes rendus de construction et de comparaison se trouvent dans `.lake`, et le résumé reproductible dans `docs/verification-result.json`.
