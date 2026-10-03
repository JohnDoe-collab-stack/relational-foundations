# Construction et fermeture des supports historiques

Ce développement construit un support de demandes pendant une histoire effective. Il fournit un théorème général de fermeture sous des conditions explicites, conserve les ressources antérieures lors des prolongements et réalise une famille complète de règles dont les demandes dépendent des résultats précédemment produits.

Le résultat général concerne des arbres de dépendances à branchement fini et à mesure strictement décroissante. La famille réalisée ici comprend sortie vide, émission, composition et réemploi. La fermeture sémantique du vérificateur et de ses univers évoqués dans le document méthodologique demeure une application distincte à construire : ses règles concrètes et leurs producteurs ne sont pas identifiés dans les sources examinées.

Le développement suivant, [Calcul, sortie et réemploi historique](calcul-sortie-reemploi-historique.fr.md), achève les trois raccords de la méthode : production du prochain pas depuis la sortie réalisée, réemploi par référence à une ressource historique identifiée, conservation et composition sur la chaîne complète. Il ajoute un support de références dont la fermeture structurelle est démontrée pour tous les constructeurs déclarés. `FeedbackCoverage` établit ensuite la couverture exacte d'histoires définies par des conditions d'admission indépendantes, avec la réalisation de toutes leurs obligations et certifications dans ce support.

## Le résultat général

[DemandClosure.lean](../RelationalFoundations/DemandClosure.lean) distingue trois données.

1. Une demande et la liste ordonnée de ses prérequis. Deux positions distinctes peuvent porter une même demande.
2. Une mesure de terminaison et une preuve de sa stricte décroissance vers chaque prérequis.
3. Un producteur local qui reçoit les réalisations de tous les prérequis et construit la réalisation de la demande.

`RankedSystem.build` développe effectivement l'arbre fermé d'une demande. `buildMany` construit les arbres d'une liste de demandes. Leur résultat contient les dépendances constituées ; le constructeur de chaque arbre impose exactement la liste des prérequis déclarés. La mesure sert à justifier la terminaison. La taille du support est calculée après la construction ; aucune capacité ni aucun fuel extérieur n'est fourni à `build`.

`Tree.Address` et `ForestAddress` individuent chaque ressource par sa place dans cette construction. Une liste explicite énumère toutes ces adresses ; les preuves `addresses_complete` et `addresses_length` établissent la couverture et la longueur de cette énumération. Plusieurs adresses distinctes peuvent porter la même étiquette de demande.

`LocalProducer.realize` construit les réalisations de bas en haut. Une propriété sémantique est fixée séparément dans `Soundness.Valid`. La loi locale `Soundness.preserves` suffit alors à démontrer cette propriété pour tous les nœuds construits. Pour appliquer ce théorème, il faut implémenter le producteur de chaque règle et prouver sa loi locale.

La portée est relative aux prérequis déclarés. Leur correspondance avec toutes les obligations réelles d'une application reste une preuve de cette application. Le théorème général fournit une condition suffisante de fermeture ; il ne caractérise pas toutes les architectures possibles de supports finis.

## Les histoires et les résultats réemployés

[HistoricalSupport.lean](../RelationalFoundations/HistoricalSupport.lean) raccorde la fermeture au type `History` existant. Ce type possède deux constructeurs : origine et prolongement par un témoin effectif de relation.

| Règle historique | Demandes produites | Construction réalisée | Conservation |
|---|---|---|---|
| Origine | La politique déclare les demandes initiales depuis l'état initial | Construction de leurs arbres fermés et de leurs réalisations | Les ressources initiales ont des adresses propres |
| Prolongement | La politique reçoit l'histoire précédente, le témoin du pas et le support constitué avec ses valeurs dérivées | Construction des nouveaux arbres, puis prolongement du support précédent | Les anciennes ressources et occurrences restent accessibles avec leurs mêmes arbres |

`Context` porte le support constitué. Ses valeurs sont dérivées par le producteur depuis ce support. La politique peut donc consulter les différences structurelles et les résultats produits ; elle reçoit les données effectivement construites à l'étape précédente.

Les demandes futures sont calculées au moment du prolongement. Une liste de toutes les demandes de toute l'histoire ne figure pas parmi les entrées de la procédure.

`Policy.build` construit le support par récurrence sur l'histoire. `build_next_demands` identifie les nouvelles demandes à celles calculées depuis le contexte effectivement produit. `build_old_entry` conserve les demandes et arbres associés à chaque occurrence antérieure.

`Policy.advance` poursuit depuis le support existant. Deux résultats couvrent les prolongements de toute longueur finie :

- `advance_build` prouve que poursuivre depuis le support construit du préfixe donne le même support que construire l'histoire prolongée.
- `advance_preserves_resource` prouve que chaque adresse antérieure se prolonge en une adresse donnant exactement le même arbre de dépendances.

`embed_injective` démontre que deux adresses antérieures distinctes restent distinctes après toute continuation finie.

Le support associe également une origine historique aux ressources. Les anciennes et nouvelles adresses sont distinctes. Les preuves `build_entry_valid`, `build_initial_valid` et `build_resource_valid` certifient les demandes initiales, les demandes de chaque occurrence et les ressources internes de leurs arbres.

## Une famille dont toutes les règles sont construites

[WordSupport.lean](../RelationalFoundations/WordSupport.lean) donne une application uniforme pour un type quelconque de tokens. Son interprétation produit des listes de tokens.

| Règle | Prérequis | Production sémantique | Fermeture |
|---|---|---|---|
| Sortie vide | Aucun | Liste vide | Production immédiate |
| Émission | Aucun | Liste contenant le token donné | Production immédiate |
| Composition | Les deux demandes composées, dans leur ordre | Concaténation de leurs résultats | La mesure décroît vers chaque composante |
| Réemploi | La demande réemployée | Conservation de son résultat | La mesure décroît vers cette demande |

Les quatre producteurs et leurs preuves sémantiques sont définis. La décroissance est démontrée depuis leurs constructeurs ; elle est ainsi disponible pour toute demande de cette famille.

À chaque nouveau pas historique, la politique forme une demande qui compose le token du pas avec le résultat précédemment produit. Elle construit sa demande de réemploi à partir de cette valeur effective. Les anciennes ressources restent dans le support historique.

`output_eq_trace` prouve, pour toute histoire typée finie et toute lecture de ses témoins en tokens, que le résultat produit est la trace complète des tokens dans l'ordre du plus récent au plus ancien. Cette garantie terminale est démontrée depuis les quatre règles et le prolongement ; elle ne figure pas comme hypothèse terminale de la construction.

`support_size_lower_bound` démontre que la taille du support est au moins la longueur de l'histoire augmentée d'une unité. Son instance `actual_supports_unbounded` exhibe, pour toute borne proposée, une profondeur de la famille existante `Perimetral.iterate` dont le support dépasse cette borne. La finitude de chaque support et l'absence de borne commune sont ainsi établies séparément.

Cette famille établit une fermeture constructive effective avec réemploi. Sa sémantique est celle des tokens et de leur composition. Elle fournit une instance du théorème général, sans constituer un modèle des univers d'un vérificateur.

## Les séparateurs et les vérifications

[Tests/HistoricalSupport.lean](../Tests/HistoricalSupport.lean) vérifie plusieurs distinctions matérielles.

- Deux prérequis portant la même étiquette conservent des adresses distinctes.
- Un réemploi et son prérequis conservent des adresses distinctes tout en produisant une même valeur.
- Les demandes du second pas dépendent du résultat effectivement produit au premier.
- La construction s'instancie sur les témoins `Perimetral.Next` existants et conserve les demandes de leurs anciennes occurrences.
- Poursuivre le support du préfixe donne le même support que reconstruire l'histoire prolongée.
- Toutes les ressources internes du support produit satisfont la propriété sémantique fixée.

Un séparateur supplémentaire est démontré dans `DemandClosure` : pour la déclaration de prérequis `() → [()]`, aucun arbre fermé fini ne peut être construit. Le test l'associe à une histoire possédant exactement une occurrence opérationnelle. Ce résultat sépare la finitude opérationnelle de la fermeture par arbres des demandes déclarées. Il porte sur ce modèle d'arbres ; il n'exclut pas toutes les autres formes de support ou de certification.

La bibliothèque, les tests et toutes leurs déclarations sont contrôlés par la procédure de vérification existante. Les résultats effectifs de la compilation, de l'audit des axiomes, des rejets attendus et du projet migré sont enregistrés dans [verification-result.json](verification-result.json) et [le rapport de migration](../Migration/verification-result.json).

La vérification du 2 octobre 2026, incluant la chaîne complète et la couverture des histoires admissibles, a réussi : 50 fichiers de fondations et de tests, 3 951 déclarations auditées sans axiomes, puis 174 sources migrées, 806 symboles publics contrôlés et les 24 rejets attendus. Les contrôles de stratification et les quatre frontières d'import passent. Les comparaisons avec le dépôt historique et ses empreintes ont été explicitement omises pour cette vérification autonome du dossier isolé.

## Une application distincte : la fermeture du vérificateur

Le document méthodologique demande de conserver les mêmes déterminations sémantiques dans le support particulier de chaque histoire. Pour le vérificateur évoqué, il reste à identifier puis à traiter exhaustivement :

1. Ses constructeurs de jugements et ses règles de transition, avec leurs paramètres et quantificateurs.
2. Les demandes sémantiques réelles de chaque règle, y compris celles de leurs certifications et des constantes prédéfinies.
3. Les producteurs locaux des ressources d'univers et les données primitives qu'ils utilisent.
4. La fermeture de ces demandes dans l'architecture de support choisie.
5. La conservation des déterminations sémantiques lors du prolongement.
6. L'extraction de sa garantie terminale indépendante.

Le développement présent fournit des constructions et des preuves réutilisables pour ce travail. Son application au vérificateur devra justifier la déclaration des demandes et leurs producteurs. L'absence d'une règle de ce vérificateur dans le périmètre examiné ne constitue pas une preuve d'impossibilité de sa fermeture.

La taille produite est une lecture du support construit. Une borne optimale, une minimalité du support et une complexité particulière demanderaient des résultats supplémentaires.

La vérification actuelle et les preuves complémentaires sont décrites dans la [validation V4](audit-corrections-v4.fr.md) et le [bilan des corrections](audit-corrections-v3.fr.md). Les reçus datés ci-dessus restent des références historiques conservées.
