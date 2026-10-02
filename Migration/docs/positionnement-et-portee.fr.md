# Positionnement et portée

`Relational Perimeter` n'est pas une fondation logique concurrente de ZF, de
la théorie des types de Martin-Löf, du calcul des constructions inductives ou
de la théorie homotopique des types. C'est une architecture relationnelle
constructive formalisée en théorie dépendante dans Lean. Son positionnement
naturel se situe à l'intersection des systèmes de transition typés, des
histoires dépendantes proof-relevant, de la sémantique des traces et des
interfaces de spécification et d'admission.

Cette situation doit être comprise comme un positionnement comparatif, non
comme une équivalence déjà établie avec l'un de ces cadres. Le dépôt formalise
l'architecture dans Lean. Son transport vers d'autres fondations et sa
caractérisation par des constructions mathématiques externes restent des
questions de recherche.

![Fondations et architecture formelle de Relational Perimeter](figures/relational-perimeter-formal-architecture.svg)

## Fondation et architecture

Lean fournit ici le langage dépendamment typé et le vérificateur de preuves.
L'architecture étudiée organise, à l'intérieur de ce langage, des relations
primitives, des témoins, des rôles, des histoires, des occurrences, des
réalisations, des interprétations, des régimes et des spécifications.

Il convient notamment de distinguer Lean du calcul des constructions
inductives qui constitue le langage noyau de Coq/Rocq. Lean repose sur une
théorie dépendante apparentée, décrite comme une version du calcul des
constructions munie de types inductifs et d'une hiérarchie d'univers. Cette
proximité ne justifie pas leur identification.

La proof-relevance du projet vient notamment du fait que les **relations
primitives constitutives**, les étapes, les histoires, les occurrences et les
témoins pertinents sont portés par `Type`. Certaines relations dérivées, telles
que la précédence, vivent en revanche dans `Prop`. Cette organisation est
compatible avec plusieurs théories dépendantes ; elle ne confère pas, en elle-même,
un caractère homotopique au projet.

## Classification relationnelle

Le système circulaire d'exigences est défini par :

```lean
def CircularRequirement (P : CircularPresentation) : Type _ :=
  NonClosingPosition P.perimeter ⊕ FinalRequirement P
```

Trois objets formellement distincts, que la construction n'identifie pas,
doivent rester séparés :

- `FinalRequirement P` est le type de la place classificatoire fermante ;
- l'occurrence résiduelle est une donnée effectivement engendrée dans la
  continuation au-delà du périmètre ;
- `P.finalJunction` est le témoin primitif de compatibilité entre l'implicite
  du dernier nœud et l'explicite du nœud initial.

La réalisation exacte du périmètre intérieur met en correspondance les
positions non fermantes et les occurrences du déploiement canonique :

```text
NonClosingPosition P.perimeter
  ≃
History.Occurrence (perimeterDeployment P).history
```

La place fermante n'appartient pas à cette correspondance. Elle classifie
fidèlement l'unique occurrence nouvelle de la première continuation ; elle
n'est ni cette occurrence ni la jonction finale primitive.

## Génération et statut de la continuation

La partie dynamique utilise une famille de transitions proof-relevant :

```lean
Step : State → State → Type
```

À partir de cette famille sont construites des histoires dépendantes et leurs
occurrences. `perimeterDeployment P` est le déploiement canonique du périmètre
constitué. La génération appliquée à son point terminal produit
`oneStepAfterPerimeter P`, puis une occurrence résiduelle qui reçoit
fidèlement l'étiquette `FinalRequirement P`.

L'articulation centrale du projet réside dans le fait qu'une continuation peut
être **positivement engendrée, munie d'une réalisation concrète exacte,
fidèlement classifiée par l'unique place résiduelle et structuralement
interprétée**, sans pour autant être admise dans le régime circulaire ni
satisfaire la spécification circulaire.

La continuation n'est donc pas éliminée par son changement de statut. Elle
reste une construction disponible et exactement interprétable. Trois résultats
négatifs doivent demeurer distincts : le rejet d'une tentative de totalisation
bilatérale, la non-admission de la continuation dans le régime circulaire et sa
non-satisfaction de la spécification circulaire.

## Séparation des interfaces

Le squelette conceptuel peut être résumé par la séparation suivante :

```text
classification | génération | réalisation | interprétation | admission | satisfaction
```

Les barres expriment une séparation métathéorique d'interfaces, de rôles et de
statuts dans l'architecture. Elles ne représentent pas une suite d'inégalités
typées formalisées dans Lean.

- La **classification** fournit les positions et les rôles disponibles.
- La **génération** produit des états, des étapes, des histoires et des
  occurrences.
- La **réalisation** construit une correspondance exacte ou une réalisation
  concrète entre des porteurs déterminés.
- L'**interprétation** rattache une occurrence et les données de frontière à
  une structure sémantique supplémentaire.
- L'**admission** incorpore une histoire dans un régime avec ses propres
  témoins.
- La **satisfaction** répond à une spécification indépendante avec ses propres
  témoins.

Dans l'instance circulaire étudiée, admission et satisfaction reconnaissent le
même carrier d'histoires, mais par des interfaces et des témoins distincts.
Leur adéquation est démontrée ; elle ne les identifie pas comme structures.

## Proximités externes et spécificité du cadre

L'architecture entretient des proximités précises avec plusieurs familles de
constructions. Ces rapprochements la situent sans l'identifier à celles-ci :

- `Step`, `History` et les occurrences rapprochent la construction des
  systèmes de transition typés et de la sémantique opérationnelle ;
- la séparation entre histoires produites, histoires admises et histoires
  satisfaisant une spécification rappelle les sémantiques de traces ;
- la concaténation d'histoires évoque les constructions de chemins libres,
  sans qu'une propriété universelle de catégorie libre soit établie ;
- le placement des témoins constitutifs dans `Type` rappelle la
  proof-relevance de plusieurs théories intensionales, sans introduire pour
  autant univalence, types d'identité supérieurs ou contenu homotopique.

Les graphes, automates et systèmes de transition enrichis fournissent ainsi des
points de comparaison partiels. La contribution formalisée ici réside dans
l'organisation explicite de ces données en couches dont les dépendances et les
changements de statut sont contrôlés dans les types.

## Programme de positionnement externe

Le code Lean établit les séparations internes décrites ci-dessus. Leur
positionnement dans la littérature constitue un travail distinct de comparaison
déclaration par déclaration et hypothèse par hypothèse : il précise quelles
parties sont équivalentes à des constructions connues, lesquelles s'y
réduisent, lesquelles leur sont apparentées et quels écarts formels leur
organisation conjointe fait apparaître. Ce positionnement externe complète le
résultat formel ; il n'en conditionne ni la validité ni la portée.

## Références primaires pour le positionnement

- Per Martin-Löf, [*Intuitionistic Type Theory*](https://archive-pml.github.io/martin-lof/pdfs/Bibliopolis-Book-retypeset-1984.pdf), 1984.
- Peter Aczel et Nicola Gambino, [*Collection Principles in Dependent Type Theory*](https://doi.org/10.1007/3-540-45842-5_1), 2002.
- Lean, [*Dependent Type Theory*](https://lean-lang.org/theorem_proving_in_lean4/Dependent-Type-Theory/) et [*Propositions and Proofs*](https://docs.lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/).
- Coq/Rocq, [*Core language: Calculus of Inductive Constructions*](https://docs.rocq-prover.org/V8.12.0/refman/language/core/index.html).
- Gordon D. Plotkin, [*A Structural Approach to Operational Semantics*](https://doi.org/10.1016/j.jlap.2004.05.001), version révisée des notes d'Aarhus de 1981.
- C. A. R. Hoare, [*Communicating Sequential Processes*](https://www.cs.ox.ac.uk/ucs/hoarebook.pdf), 1985.
- The Univalent Foundations Program, [*Homotopy Type Theory: Univalent Foundations of Mathematics*](https://homotopytypetheory.org/book/), 2013.
- Tom Leinster, [*Basic Category Theory*](https://arxiv.org/abs/1612.09375), version libre de l'ouvrage de 2014.
