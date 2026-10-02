> État historique de la première revérification. Les points laissés ouverts ici sont traités dans [le bilan d’achèvement](achevement.fr.md). Les rapports JSON donnent les résultats actuels.

# Revérification du 30 septembre 2026

La terminologie actuelle est **tournant constitutif affirmatif** ; « tournant » en est la forme courte. La [définition et la distinction de sa version avec sortie](architecture-et-portee.fr.md#tournant-constitutif-affirmatif) sont précisées dans l’architecture. Ce choix de terme ne modifie pas les résultats historiques rapportés ici.

La vérification technique passe. Ce résultat porte sur les énoncés formalisés et leurs dépendances ; il ne certifie pas, à lui seul, que toute l’ambition conceptuelle ou tout le plan de migration est achevé.

## Corrections effectuées

- Ajout de `Formation.fold_unique` : toute interprétation qui conserve les deux constructeurs coïncide point par point avec le pli récursif. La propriété de liberté dispose ainsi d’un énoncé d’unicité explicite.
- Le test négatif de positivité demande maintenant un témoin dans la fibre de la frontière vide effective et tente de le produire depuis cette frontière. Il contrôle la confusion frontière/témoin.
- Le vérificateur contrôle les noms des cinq tests négatifs, plutôt que leur seul nombre.
- Le nombre de résultats historiques audités est calculé et confronté aux reçus de Lean.
- Les quatre sources mathématiques historiques sont recompilées dans `.lake/reference-verification`, avant la comparaison. Le dépôt original reçoit aucune écriture de cette procédure.
- Le rapport porte un état `RUNNING`, `FAILED` ou `PASSED` et une date UTC. Un échec ne laisse plus le dernier succès affiché comme résultat de la nouvelle exécution.

## Contrôle mathématique des articulations

La réalisation exacte distingue le transport réversible de la rigidité. L’accord inverse fixe le rôle pendant le transport dépendant. Le transport du porteur total des témoins restitue de véritables transports des fibres de réalisation, et leur cohérence avec les témoins distingués est démontrée.

La continuation fidèle utilise les plongements de la composition effective. Le résidu fournit l’unicité de ses occurrences ; la positivité permet ensuite d’extraire son unique pas. Cette extraction est structurelle. L’interprétation de frontière conserve le pas extrait, l’occurrence, la formation et la jonction avec des accords explicites. Elle ne convertit pas la jonction en pas engendré.

La sortie de régime utilise une classification d’admission reçue séparément. La circularité positive ne fournit ni cette classification ni une obstruction de pôles. La différence stricte du certificat final utilise actuellement la longueur dérivée ; la détermination résiduelle demeure indépendante de cette lecture.

## Couverture et limites par rapport au texte et au plan

| Domaine | État constaté |
| --- | --- |
| Places inductives, frontière indexée, système complet des rôles | Construits pour la grammaire retenue |
| Réalisation exacte, accord inverse, rigidité séparée | Formalisés avec modèles séparateurs |
| Délimitation intérieure | Démontrée pour une relation qui impose l’identité de l’occurrence distinguée |
| Composition, résidu, continuation fidèle, frontière et tournant constitutif affirmatif | Chaîne couplée formalisée |
| Quantité, fibres de témoins, signature et marques | Interfaces génériques ; instance circulaire équipée concrète |
| Cardinalisation et interprétation concrète | Formalisées ; la lecture des témoins peut être non fidèle |
| Correspondance avec le modèle historique | Ponts de transports et accords canoniques ; pas d’équivalence de toutes ses données riches |
| Spécification normative historique | Interface générique disponible ; reprise intégrale non réalisée |
| Migration des cinq fichiers et raccord computationnel | Non effectués dans le dépôt original |

La signature conserve exactement ses graphes déclarés. Les graphes de formation et provenance couvrent les préfixes des occurrences intérieures. La conservation des constructeurs de toutes les formations arbitraires demanderait des graphes supplémentaires. La construction d’une quantité circulaire équipée pour toute présentation circulaire n’est pas encore fournie.

L’existence d’identités, inverses et compositions est formalisée pour les transports équipés et marqués. La bibliothèque ne pose pas d’égalité globale entre fonctions ni de structure catégorique complète sur ces objets.

Le plan reste un programme plus large que cette bibliothèque indépendante. Il ne doit pas être présenté comme intégralement achevé.

## Résultats reproductibles

`scripts/verify.ps1` construit les 32 sources de bibliothèque et tests, audite toutes leurs déclarations importées, exige le rejet des cinq fichiers négatifs et vérifie les onze résultats explicitement audités du pont historique. Le résumé final, avec les comptes effectifs, se trouve dans `verification-result.json`.

Une exécution avec `-SkipComparison -SkipReference` vérifie l’autonomie de la bibliothèque. Une exécution complète vérifie aussi les 253 fichiers du dépôt original, son HEAD, sa branche et les empreintes de l’archive récupérable.

Les tests négatifs exigent un rejet par incompatibilité de types. Ils ne constituent pas un analyseur sémantique général des diagnostics. Le contrôle textuel des imports et constructions interdites est un contrôle complémentaire ; le contrôle des dépendances axiomatiques repose sur l’environnement de Lean.
