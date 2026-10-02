# Décomposition exécutée variable

Ce prolongement conserve l'instance publique convergente et son équivalence
entre pleine largeur binaire et conservation injective. Il ajoute des
exécutions où certaines sorties se regroupent et d'autres restent distinctes.

## Production locale

`VariableRelationalExecution` forme les deux occurrences depuis le même état
constitué. L'action recherche le transport existant sur la variable sélectionnée.
Si la recherche réussit, elle applique la relation découverte ; sinon, elle
conserve la continuation d'entrée. Les traces indexent les entrées et les
sorties effectives. La préservation de l'acceptation sur les continuations
arbitraires est démontrée séparément et consommée par l'admission.

La première étape de `MixedExample` produit une image de largeur un, la
seconde une image de largeur deux. Les quatre profils sources restent
distincts ; l'image composée porte deux obligations. Une recherche infructueuse
ne signifie pas qu'aucun autre transport serait possible : les deux obligations
correspondent ici à des sorties effectivement démontrées distinctes.

## Composition et suites

`VariableOutputComposition` réalise exactement les tuples de sorties stockées,
avec les deux lois de retour. Deux profils ont la même obligation exactement
lorsqu'ils produisent le même tuple. Sur ces histoires factorisées, la largeur
est le produit des largeurs locales, donc `2^k`, où `k` compte les images locales
de largeur deux. Ce nombre est lu après leur production, pas fourni en entrée.

Une suite commune exige un accord avec les affectations réellement produites.
`AdaptiveRelationalExecution` traite séparément le cas où les suites diffèrent :
chaque suite est indexée par l'état formé depuis la sortie de son occurrence.
Son exemple mixte possède six profils et trois sorties distinctes. La formule
de produit précédente n'est pas appliquée aux arbres adaptatifs.

`UnboundedMixedExecution` construit, pour tout `count`, une histoire de
`count + 1` étapes à partir des états successivement produits. La sélection est
raccordée à l'extraction des candidats du résidu reçu. La recherche réussit sur
les préfixes regroupants et échoue à l'étape terminale séparante. Le carrier
source a `2^(count + 1)` profils ; l'image des tuples de sorties a largeur deux.
L'acceptation de ces tuples est établie à partir des actions préservantes.

## Certificat et portée

`PublicExecutionConstitutionCertificate.wholeHeadIsPrefixLocal` intègre la
preuve existante d'exactitude de la production initiale entière, quel que soit
l'horizon restant. Le producteur audité n'est pas remplacé.

Toutes ces constructions sont accessibles depuis `import RelationalPerimeter`.
Les régressions correspondantes figurent dans `Tests/`. Les quatre fichiers
fondateurs sont inchangés. Aucun résultat de coût total n'est ajouté : largeur,
taille descriptive et temps de calcul restent des quantités différentes.

Ce prolongement ne remplace ni ne généralise silencieusement la cible auditée.
Il n'établit pas que les obligations conservées sont irréductibles par toute
autre transformation préservante. Il décrit exactement les images des actions
exécutées et les suites que leurs sorties permettent de constituer.
