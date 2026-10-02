# Décomposition en rôles relationnels constitutifs, circularité et quantification structurelle

> Note terminologique : les documents actuels emploient **tournant constitutif affirmatif** pour la notion appelée « tournant structurel affirmatif » dans le texte de référence ci-dessous. Sa [définition actuelle](architecture-et-portee.fr.md#tournant-constitutif-affirmatif) précise aussi la version avec sortie de régime. Le corps du texte fourni est conservé.

## 1. Objet

On cherche à définir mathématiquement trois notions articulées :

1. la **décomposition en rôles relationnels constitutifs** ;
2. la **circularité comme constitution d’un système clos de rôles** ;
3. la **quantification structurelle** du domaine exactement réalisé.

L’idée directrice est de ne pas présupposer que les unités pertinentes d’une construction sont déjà données comme objets individués.

On part d’une présentation relationnelle. Celle-ci fournit des relations primitives et leurs témoins. Ces relations construisent des places différenciées ; des occurrences sont ensuite engendrées pour réaliser ces places ; leur réalisation exacte détermine un domaine intérieur ; enfin, dans le cas circulaire, une frontière fermante complète le système des rôles sans mettre fin à la génération.

La progression générale est :

```text
relations et témoins primitifs
↓
architecture relationnelle
↓
construction des places
↓
rôles relationnels constitutifs
↓
occurrences engendrées
↓
réalisation exacte
↓
système circulaire complet des rôles
↓
délimitation du domaine intérieur
↓
quantité structurelle
↓
continuation éventuelle
↓
changement de statut
↓
cardinalisation éventuelle
```

Le déplacement conceptuel est :

> **Les unités, leur domaine et leur quantité ne sont pas nécessairement présupposés. Ils peuvent être constitués progressivement à partir des relations primitives et de leur composition.**

---

# I. Cadre typé

## 2. Niveau de généralité

La théorie est formulée dans une théorie des types dépendants.

Les types de rôles, les types d’occurrences et les fibres relationnelles considérées sont supposés être des **ensembles au sens de la théorie des types**, c’est-à-dire des 0-types.

Une fibre :

`R(a,b) : Type`

peut contenir plusieurs témoins distincts.

L’hypothèse de 0-troncation signifie seulement que les identités entre ces témoins ne portent pas de structure homotopique supérieure pertinente pour la présente théorie.

On conserve donc :

```text
types dépendants
témoins relationnels proof-relevant
transports
quasi-inverses
équivalences
```

sans introduire ici une théorie des cohérences supérieures.

---

# II. Présentation relationnelle

## 3. Relations primitives

On considère une présentation :

`Π : Presentation`.

Elle comporte des types et des familles relationnelles dépendantes.

Une famille relationnelle peut avoir la forme :

`R : A → B → Type`.

Pour :

`a : A`

et :

`b : B`,

un terme :

`r : R(a,b)`

est un témoin positif de la relation entre `a` et `b`.

On distingue donc :

```text
R
famille relationnelle

r : R(a,b)
témoin particulier
```

Les témoins peuvent participer directement à la formation de nouvelles données.

Ils peuvent notamment être :

```text
conservés
transportés
inscrits dans une construction
utilisés comme indices
consommés par des constructions ultérieures
```

---

# III. Signature constitutive

## 4. Relations déclarées constitutives

Toutes les relations disponibles ne sont pas nécessairement pertinentes pour toute comparaison.

On fixe donc une **signature constitutive** :

`Σc`.

Elle indique les familles relationnelles que la notion étudiée doit conserver.

Elle peut contenir :

```text
formation
source
cible
provenance
ordre
adjacence
compatibilité
composition
```

Une équivalence structurelle sera toujours relative à cette signature.

---

## 5. Cas limite

Si :

`Σc = ∅`

et :

`Realizes(r,o) ≔ Unit`,

alors la couche relationnelle devient triviale.

La théorie se réduit essentiellement à des équivalences de rôles et de porteurs compatibles avec leur réalisation.

La simple équivalence de types apparaît donc comme le cas limite appauvri de la théorie.

---

# IV. Places relationnelles

## 6. Place avant occurrence

Une **place relationnelle** est une position produite par la structure d’une présentation avant qu’une occurrence particulière ne la réalise.

On distingue :

```text
relation primitive
≠
témoin relationnel
≠
place relationnelle
≠
occurrence réalisatrice
```

Une place n’est donc pas une occurrence encore dépourvue d’étiquette.

Elle appartient à la structure qui détermine les fonctions relationnelles disponibles.

---

## 7. Rôle relationnel constitutif

Un **rôle relationnel constitutif** est une place relationnelle considérée selon la fonction qu’elle remplit dans la constitution.

La direction est :

```text
relations
→ architecture
→ places
→ rôles
```

et non :

```text
objets déjà individués
→ classification
→ rôles
```

---

# V. Construction et occurrences

## 8. Construction

Soit :

`H : Construction(Π)`.

On lui associe :

`Occ(H) : Type`.

Une occurrence :

`o : Occ(H)`

est individuée relativement à `H`.

Sa construction précède donc toute lecture de sa valeur.

---

## 9. Individuation avant lecture

Une lecture :

`read : Occ(H) → V`

peut associer une valeur à une occurrence.

Mais :

`read(o₁) = read(o₂)`

ne fournit pas généralement :

`o₁ = o₂`.

Le principe est :

> **L’occurrence est individuée dans la construction ; sa lecture est ultérieure.**

---

# VI. Réalisation constitutive

## 10. Famille de réalisation

On introduit :

`RealizesΠ : Role(Π) → Occ(H) → Type`.

Un terme :

`a : RealizesΠ(r,o)`

atteste que `o` réalise effectivement le rôle `r`.

Lorsque la signature `Σc` est non triviale, `RealizesΠ` doit être construit ou justifié à partir de ses relations.

Il peut notamment porter des accords sur :

```text
formation
source
cible
provenance
position
succession
composition
```

---

## 11. Réalisation

Une réalisation constitutive comprend :

`ρ : Role(Π) → Occ(H)`

et :

`α : ∀ r, RealizesΠ(r,ρ(r))`.

À chaque rôle correspond donc :

```text
une occurrence
+
la justification relationnelle de cette réalisation
```

---

# VII. Décomposition exacte

## 12. Réalisation et couverture

La réalisation de tous les rôles ne signifie pas nécessairement que toutes les occurrences d’une construction appartiennent au domaine réalisé.

On distingue :

```text
réalisation de tous les rôles
≠
couverture de toutes les occurrences
```

Cette distinction permet à une construction d’être exactement réalisée sur son domaine intérieur tout en étant prolongeable.

---

## 13. Décomposition exacte

Pour un type de rôles `A` et un domaine d’occurrences `O`, une décomposition exacte comprend :

`ρ : A → O`

`κ : O → A`

avec :

`η : ∀ a, κ(ρ(a)) = a`

`ε : ∀ o, ρ(κ(o)) = o`.

On obtient :

`A ≃ O`.

Cette équivalence est accompagnée des accords constitutifs :

`α : ∀ a, Realizes(a,ρ(a))`.

---

## 14. Accord inverse dérivé

Pour :

`o : O`,

on dispose de :

`α(κ(o)) : Realizes(κ(o),ρ(κ(o)))`.

Le chemin :

`ε(o) : ρ(κ(o)) = o`

permet d’obtenir par transport :

`β(o) : Realizes(κ(o),o)`.

Ainsi chaque rôle possède une occurrence justifiée et chaque occurrence possède un rôle justifié.

---

# VIII. Présentation circulaire

## 15. Primitive circulaire

On considère maintenant :

`Π : CircularPresentation`.

La présentation possède deux structures relationnelles qu’il faut distinguer :

```text
une structure successive
une frontière fermante
```

La première engendre les places intérieures.

La seconde engendre la place fermante et porte la relation primitive de fermeture.

---

# IX. Structure successive

## 16. Épine relationnelle

On considère :

`Node : Type`

et une famille relationnelle :

`NextRel : Node → Node → Type`.

L’épine relationnelle est un type inductif dépendant :

```text
Spine : Node → Type
```

avec schématiquement deux constructeurs :

```text
boundary :
  Spine(n)

advance :
  (k : NextRel(n,m))
  →
  Spine(m)
  →
  Spine(n)
```

Une avancée de l’épine ne peut donc être construite sans un témoin relationnel :

`k : NextRel(n,m)`.

La structure successive n’est pas une simple liste de nœuds.

Ses étapes sont constituées avec leurs témoins relationnels.

---

## 17. Positions successives : définition inductive

Les positions successives sont définies directement comme un type inductif indexé par une épine.

Schématiquement :

```text
SuccessivePosition :
  Spine(n) → Type
```

avec deux constructeurs.

Pour une épine :

`advance(k,tail)`,

on possède :

```text
here :
  SuccessivePosition(advance(k,tail))
```

qui désigne la place créée par l’avancée relationnelle courante.

Et :

```text
later :
  SuccessivePosition(tail)
  →
  SuccessivePosition(advance(k,tail))
```

qui transporte dans l’épine étendue une place déjà constituée dans `tail`.

Il n’existe aucun constructeur pour :

`SuccessivePosition(boundary(n))`.

Ainsi, les positions sont générées exactement par les avancées relationnelles.

On peut montrer ensuite :

`SuccessivePosition(advance(k,tail)) ≃ Unit ⊎ SuccessivePosition(tail)`,

mais cette équivalence est **dérivée**.

Elle n’est pas la définition primitive de `SuccessivePosition`.

---

## 18. Rôles intérieurs

La présentation circulaire fournit une épine :

`spineΠ : Spine(startΠ)`.

On définit :

`InternalRole(Π) ≔ SuccessivePosition(spineΠ)`.

Le type des rôles intérieurs n’est donc pas postulé.

Il est engendré par :

```text
témoins relationnels successifs
↓
Spine
↓
constructeurs here / later
↓
SuccessivePosition
↓
InternalRole(Π)
```

L’inversion des primitives est ici effective :

> **les relations successives participent directement à la construction du type des rôles intérieurs.**

---

# X. Frontière fermante

## 19. Frontière structurale

La présentation circulaire détermine également :

`∂Π : ClosingBoundary(Π)`.

Cette frontière contient ou détermine au minimum :

```text
interface terminale t₀
interface initiale i₀
famille relationnelle fermante
CloseΠ(t₀,i₀)
```

Schématiquement :

`∂Π ≔ (t₀,i₀,CloseΠ)`.

La frontière structurale doit être distinguée de l’existence d’un témoin particulier de fermeture.

---

## 20. Témoin fermant

La présentation fournit :

`j★ : CloseΠ(t₀,i₀)`.

Ainsi :

```text
∂Π
=
frontière structurelle

j★
=
témoin positif de sa relation fermante
```

La frontière détermine quelle relation doit être considérée.

`j★` atteste que cette relation est effectivement habitée.

---

# XI. Construction de la place fermante

## 21. Inductif indexé par la frontière

La place finale ne doit pas être définie comme un alias de `Unit`.

On introduit un véritable type inductif paramétré par une frontière :

```text
BoundaryFinalRole :
  ClosingBoundary(Π) → Type
```

avec un unique constructeur :

```text
final :
  BoundaryFinalRole(∂)
```

pour chaque :

`∂ : ClosingBoundary(Π)`.

On définit alors :

`FinalRole(Π) ≔ BoundaryFinalRole(∂Π)`.

Et :

`r★ ≔ final : FinalRole(Π)`.

La frontière `∂Π` apparaît donc réellement comme **indice du type**.

---

## 22. Pourquoi ce n’est pas simplement `Unit`

Pour une frontière fixée `∂Π`, on peut naturellement démontrer :

`BoundaryFinalRole(∂Π) ≃ Unit`.

Cette équivalence concerne seulement le cardinal ou la forme du porteur une fois l’index fixé.

Elle n’autorise pas à remplacer la famille dépendante :

`BoundaryFinalRole : ClosingBoundary(Π) → Type`

par un `Unit` indépendant de la frontière.

L’information constitutive est portée par l’index :

```text
BoundaryFinalRole(∂₁)
```

et :

```text
BoundaryFinalRole(∂₂)
```

sont des fibres de la même famille à des frontières éventuellement différentes.

Le gain recherché n’est donc pas cardinal.

Il est **typal et dépendant**.

---

## 23. Contractilité dérivée

Pour une frontière :

`∂ : ClosingBoundary(Π)`,

tout :

`r : BoundaryFinalRole(∂)`

est construit par l’unique constructeur `final`.

On démontre donc par élimination :

`finalContract :
  ∀ r : BoundaryFinalRole(∂),
  r = final`.

En particulier :

`finalContractΠ :
  ∀ r : FinalRole(Π),
  r = r★`.

La contractilité est ainsi dérivée de l’inductif indexé.

Elle n’est pas ajoutée comme hypothèse extérieure.

---

## 24. Origine commune de `r★` et `j★`

La même frontière produit deux branches distinctes :

```text
∂Π
├──→ BoundaryFinalRole(∂Π)
│      ↓
│      r★
│
└──→ CloseΠ(t₀,i₀)
       ↓
       j★
```

Ainsi :

`r★`

et :

`j★`

possèdent une origine structurelle commune.

Mais ils demeurent mathématiquement distincts :

```text
r★
=
place fermante

j★
=
témoin relationnel fermant
```

Le rôle n’est pas le témoin.

Le témoin n’est pas le rôle.

---

# XII. Système complet des rôles

## 25. Construction

On définit :

`FullRole(Π) ≔ InternalRole(Π) ⊎ FinalRole(Π)`.

Le système complet est donc produit par deux structures issues de la présentation :

```text
structure successive
↓
InternalRole(Π)

frontière fermante ∂Π
↓
FinalRole(Π)
```

puis :

```text
InternalRole(Π)
⊎
FinalRole(Π)
↓
FullRole(Π)
```

---

## 26. Clôture structurelle

Pour :

`r : FullRole(Π)`,

l’élimination de la somme donne deux cas.

### Cas intérieur

`r = inl(a)`

pour :

`a : InternalRole(Π)`.

### Cas final

`r = inr(f)`

pour :

`f : FinalRole(Π)`.

Par contractilité :

`f = r★`.

Donc tout rôle complet est :

```text
soit intérieur
soit égal à la place fermante
```

Il n’existe aucune troisième forme de rôle dans le système construit par `Π`.

C’est la **clôture structurelle du système des rôles**.

---

## 27. Séparation

Pour tout :

`a : InternalRole(Π)`,

on a :

`inl(a) ≠ inr(r★)`.

La somme assure donc :

```text
exhaustivité
+
séparation
```

des deux formes de rôle.

---

# XIII. Domaine intérieur

## 28. Construction intérieure

La présentation engendre une construction intérieure :

`H₀ : Construction(Π)`.

On note :

`O₀ ≔ Occ(H₀)`.

Les rôles intérieurs sont exactement réalisés par les occurrences de `H₀`.

On dispose de :

`ρ₀ : InternalRole(Π) → O₀`

`κ₀ : O₀ → InternalRole(Π)`

avec :

`η₀ : ∀ a, κ₀(ρ₀(a)) = a`

`ε₀ : ∀ o, ρ₀(κ₀(o)) = o`.

Et :

`α₀ : ∀ a, Realizes₀(a,ρ₀(a))`.

Ainsi :

`InternalRole(Π) ≃ O₀`.

---

## 29. Classification dans le système complet

On définit :

`λ₀ : O₀ → FullRole(Π)`

par :

`λ₀(o) ≔ inl(κ₀(o))`.

Toute occurrence intérieure réalise donc une place appartenant à la branche intérieure du système complet.

---

## 30. Non-réalisation de la place fermante

Pour tout :

`o : O₀`,

on a :

`λ₀(o) ≠ inr(r★)`.

Ainsi :

```text
InternalRole(Π)
↔
occurrences intérieures

tandis que

r★
∈
FullRole(Π)

mais

r★
n’est pas réalisé dans H₀
```

La place fermante existe donc structuralement avant son éventuelle réalisation par une continuation.

---

# XIV. Délimitation circulaire

## 31. Théorème

> **Théorème — Délimitation circulaire du domaine intérieur.**
>
> Pour une présentation circulaire `Π` :
>
> - ses témoins successifs construisent une épine relationnelle ;
> - les constructeurs `here` et `later` engendrent `InternalRole(Π)` à partir de cette épine ;
> - sa frontière `∂Π` indexe `FinalRole(Π)` ;
> - la contractilité de `FinalRole(Π)` est dérivée de son inductif à constructeur unique ;
> - `FullRole(Π) ≔ InternalRole(Π) ⊎ FinalRole(Π)` ;
> - `H₀` réalise exactement les rôles intérieurs.
>
> Alors :
>
> 1. chaque occurrence de `H₀` réalise exactement un rôle intérieur ;
> 2. chaque rôle intérieur possède exactement son occurrence ;
> 3. aucune occurrence intérieure ne réalise la place fermante ;
> 4. tout rôle complet est intérieur ou fermant ;
> 5. aucune troisième classe de rôle n’existe relativement à cette présentation ;
> 6. le domaine intérieur est exactement délimité dans le système complet construit depuis `Π`.

---

## 32. Portée du théorème

Ce théorème ne dit pas :

```text
que la génération est épuisée
que r★ possède déjà une occurrence
que j★ est parcouru par H₀
que t₀ = i₀
que toute continuation future est impossible
```

La clôture porte sur le système des rôles.

Elle ne signifie pas l’arrêt de la génération.

---

# XV. Quantification structurelle

## 33. Quantité intérieure

La décomposition exacte :

`InternalRole(Π) ≃ O₀`

avec les accords constitutifs détermine :

`Qint(Π)`.

Cette quantité structurelle répond à :

```text
quelles sont les unités ?
quelles places réalisent-elles ?
pourquoi réalisent-elles ces places ?
quel domaine couvrent-elles exactement ?
```

---

## 34. Contribution propre de la circularité

La décomposition exacte produit la quantité structurelle intérieure.

La circularité produit son système complet de référence :

`FullRole(Π)`.

Elle détermine :

```text
la composante intérieure exactement réalisée
+
la place finale qui clôt le système
sans être encore réalisée intérieurement
```

Ainsi :

```text
décomposition exacte
→ quantité structurelle

circularité
→ clôture structurelle des rôles

ensemble
→ quantité structurelle intérieure
  exactement délimitée
```

---

# XVI. Équivalence constitutive

## 35. Données fondamentales

Pour deux quantités `Q₁` et `Q₂` relatives à une même signature `Σc`, une équivalence constitutive comprend :

`FRole : Role₁ ≃ Role₂`

`FOcc : Occ₁ ≃ Occ₂`

et :

`χρ :
  ∀ r,
  FOcc(ρ₁(r))
  =
  ρ₂(FRole(r))`.

---

## 36. Transport de `Realizes`

Pour :

`r : Role₁`

et :

`o : Occ₁`,

on demande :

`FRealizes(r,o) :
  Realizes₁(r,o)
  ≃
  Realizes₂(FRole(r),FOcc(o))`.

La relation de réalisation est ainsi transportée réversiblement.

---

## 37. Cohérence des témoins distingués

Le témoin :

`α₁(r)`

transporté par `FRealizes` puis le long de `χρ(r)` doit être égal à :

`α₂(FRole(r))`.

On demande donc explicitement :

`cohα(r)`.

Cette condition n’est pas automatique, puisque les fibres `Realizes` ne sont pas supposées propositionnelles.

---

## 38. Relations de `Σc`

Pour chaque relation appartenant à `Σc`, on demande une équivalence fibre à fibre appropriée.

Par exemple :

`S₁(o₁,o₂)
 ≃
 S₂(FOcc(o₁),FOcc(o₂))`.

---

## 39. Définition

On note :

`Q₁ ≃c Q₂`

l’existence d’une telle structure de transport constitutif.

Elle conserve :

```text
rôles
occurrences
réalisations
témoins distingués
relations de Σc
```

---

# XVII. Compatibilité inverse dérivée

## 40. Dérivation de `χκ`

Pour :

`o : Occ₁`,

on construit :

`χκ(o) :
  FRole(κ₁(o))
  =
  κ₂(FOcc(o))`.

Premièrement :

`FRole(κ₁(o))
 =
 κ₂(ρ₂(FRole(κ₁(o))))`

par :

`η₂(FRole(κ₁(o)))⁻¹`.

Puis :

`κ₂(ρ₂(FRole(κ₁(o))))
 =
 κ₂(FOcc(ρ₁(κ₁(o))))`

par application de `κ₂` à :

`χρ(κ₁(o))⁻¹`.

Enfin :

`κ₂(FOcc(ρ₁(κ₁(o))))
 =
 κ₂(FOcc(o))`

par application de :

`κ₂ ∘ FOcc`

à :

`ε₁(o)`.

`χκ` est donc dérivé des données primitives.

---

# XVIII. Réflexivité, symétrie et transitivité

## 41. Réflexivité

Toute quantité est constitutivement équivalente à elle-même par les identités.

---

## 42. Symétrie

Une équivalence constitutive s’inverse en inversant :

```text
FRole
FOcc
FRealizes
relations de Σc
```

et en reconstruisant le chemin de réalisation et `cohα` dans le sens inverse.

---

## 43. Transitivité

Deux équivalences constitutives se composent par composition :

```text
des rôles
des occurrences
des fibres Realizes
des relations de Σc
```

Le nouveau `χρ` est obtenu par concaténation des chemins correspondants.

Le nouveau `cohα` demande le calcul explicite des transports successifs.

---

## 44. Proposition

> **Relativement à une signature constitutive fixée `Σc`, `≃c` est réflexive, symétrique et transitive au niveau des ensembles.**

La preuve formelle générale, en particulier le calcul de transitivité de `cohα`, reste à construire.

---

# XIX. Continuation positive

## 45. Stricte extension

Une stricte extension :

`StrictExtension(H₀,H₁)`

est une donnée positive.

Elle contient au minimum :

```text
continuation :
  PositiveContinuation(H₀,H₁)

recompose :
  append(H₀,continuation) = H₁

ne :
  H₁ ≠ H₀
```

L’extension n’est donc pas réduite à la négation d’une égalité.

---

## 46. Anciennes et nouvelles occurrences

Soient :

`N : Type`

les nouvelles occurrences,

et :

`X : Type`

le porteur étendu.

On dispose de :

`old : O₀ → X`

`new : N → X`.

On suppose :

`separate :
  ∀ o n,
  old(o) ≠ new(n)`.

Et :

`newInjective :
  ∀ n₁ n₂,
  new(n₁) = new(n₂)
  →
  n₁ = n₂`.

---

# XX. Classification fidèle

## 47. Étiquetage complet

On suppose :

`ℓ : X → FullRole(Π)`.

Il est fidèle :

`faithful :
  ∀ x y,
  ℓ(x) = ℓ(y)
  →
  x = y`.

Il conserve les anciens rôles :

`preserve :
  ∀ a,
  ℓ(old(ρ₀(a)))
  =
  inl(a)`.

---

## 48. Détermination du nouveau rôle

Prenons :

`n : N`.

L’étiquette :

`ℓ(new(n))`

appartient à :

`InternalRole(Π) ⊎ FinalRole(Π)`.

### Branche intérieure

Supposons :

`ℓ(new(n)) = inl(a)`.

Par conservation :

`ℓ(old(ρ₀(a))) = inl(a)`.

Donc :

`ℓ(old(ρ₀(a))) = ℓ(new(n))`.

Par fidélité :

`old(ρ₀(a)) = new(n)`.

Cela contredit `separate`.

### Branche finale

Il reste :

`ℓ(new(n)) = inr(f)`.

Par :

`finalContractΠ(f)`,

on a :

`f = r★`.

Donc :

`ℓ(new(n)) = inr(r★)`.

---

## 49. Théorème résiduel

> **Toute nouvelle occurrence fidèlement classable dans `FullRole(Π)` réalise nécessairement la place fermante.**

La preuve utilise :

```text
construction du système complet
conservation des rôles intérieurs
séparation ancien/nouveau
fidélité
contractilité dérivée de FinalRole(Π)
```

Elle n’utilise pas `j★`.

Cette absence est intentionnelle.

---

## 50. Unicité de la partie nouvelle

Si :

`n₁ n₂ : N`,

alors :

`ℓ(new(n₁)) = inr(r★)`

et :

`ℓ(new(n₂)) = inr(r★)`.

La fidélité donne :

`new(n₁) = new(n₂)`.

Puis `newInjective` donne :

`n₁ = n₂`.

Ainsi `N` est un sous-singleton.

Ce résultat est général pour un résidu contractile fidèlement classé.

Il n’est pas produit spécifiquement par la circularité.

---

# XXI. Interprétation de frontière

## 51. Fonction de `j★`

Le témoin :

`j★ : CloseΠ(t₀,i₀)`

ne sert pas à déterminer que la nouvelle occurrence est finale.

Cette détermination provient déjà de la clôture des rôles et de la fidélité.

`j★` intervient ensuite pour donner à cette frontière son contenu relationnel fermant.

---

## 52. Interprétation de frontière

Pour :

`n : N`

avec :

`ℓ(new(n)) = inr(r★)`,

on introduit :

`BoundaryInterpretationΠ(n) : Type`.

Cette structure contient au minimum :

```text
la nouvelle occurrence
son pas effectivement engendré
sa formation
sa provenance
sa réalisation de r★
la frontière ∂Π
le témoin fermant j★
```

Elle ne contient pas automatiquement :

```text
une égalité entre le pas engendré et j★

une égalité de leurs cibles

une identification de la nouvelle cible
avec l’interface initiale
```

---

## 53. Pont complet

On obtient :

```text
témoins successifs
↓
Spine
↓
SuccessivePosition
↓
InternalRole(Π)
              \
               \
                → FullRole(Π)
               /
∂Π ─→ FinalRole(Π)
 │
 └──→ CloseΠ(t₀,i₀)
          ↓
          j★

nouvelle occurrence
↓
r★
↓
BoundaryInterpretationΠ
↑
∂Π et j★
```

Les rôles intérieurs et la place finale sont donc engendrés par des structures relationnelles.

La place finale et le témoin fermant partagent la même frontière structurale sans être identifiés.

---

# XXII. Régime

## 54. Admission

On introduit séparément :

`G : Construction(Π) → Type`.

Un régime peut imposer à une interprétation de frontière des obligations supplémentaires.

Ces obligations ne découlent pas :

```text
de r★ seul
ni
de j★ seul
```

mais de la structure d’admission choisie.

---

## 55. Classification exacte du régime

Supposons :

`canonical : G(H₀)`.

Supposons :

`classifyG :
  ∀ H,
  G(H) → H = H₀`.

Et :

`completeG :
  ∀ H,
  H = H₀ → G(H)`.

Le régime est exactement classifié par `H₀`.

---

## 56. Sortie de régime

Soit :

`s : StrictExtension(H₀,H₁)`.

Si :

`g₁ : G(H₁)`,

alors :

`classifyG(H₁,g₁) : H₁ = H₀`.

Mais :

`s.ne : H₁ ≠ H₀`.

Donc :

`G(H₁) → Empty`.

La continuation reste néanmoins positivement construite par :

`s.continuation`.

---

# XXIII. Tournant

## 57. Tournant structurel affirmatif

Un tournant structurel affirmatif réunit :

```text
un domaine intérieur exactement constitué

un système de rôles structurellement clos

une continuation positivement engendrée

une nouvelle occurrence occupant la place finale

une interprétation de cette frontière
avec le témoin fermant primitif

une sortie éventuelle du régime antérieur
```

Le tournant est affirmatif parce que la continuation existe positivement.

Il ne signifie pas un arrêt de génération.

---

# XXIV. Quantité structurelle circulaire

## 58. Définition

Une quantité structurelle circulaire intérieure comprend :

```text
Π : CircularPresentation

spineΠ : Spine(startΠ)

InternalRole(Π)
≔ SuccessivePosition(spineΠ)

∂Π : ClosingBoundary(Π)

BoundaryFinalRole :
  ClosingBoundary(Π) → Type

FinalRole(Π)
≔ BoundaryFinalRole(∂Π)

FullRole(Π)
≔ InternalRole(Π) ⊎ FinalRole(Π)

H₀ : Construction(Π)

O₀ ≔ Occ(H₀)

InternalRole(Π) ≃ O₀

accords constitutifs

non-réalisation intérieure de r★

j★ : CloseΠ(t₀,i₀)
```

Cette quantité est donc située dans un système dont les deux classes de rôles sont elles-mêmes produites par la présentation relationnelle.

---

# XXV. Cardinalisation

## 59. Passage au nombre

Si :

`InternalRole(Π) ≃ Fin(n)`,

alors :

`O₀ ≃ Fin(n)`.

Le naturel `n` représente numériquement un domaine déjà constitué.

L’ordre est :

```text
relations primitives
↓
construction des places
↓
rôles
↓
occurrences
↓
réalisation exacte
↓
clôture
↓
quantité structurelle
↓
cardinalisation
```

---

# XXVI. Théorème composé

## 60. Circularité constitutive, quantité et continuation

> **Théorème — Circularité constitutive, quantité intérieure et continuation.**
>
> Soit une présentation circulaire `Π` telle que :
>
> 1. ses témoins successifs construisent une épine relationnelle ;
> 2. `SuccessivePosition` soit inductivement engendré par les constructeurs `here` et `later` sur cette épine ;
> 3. `InternalRole(Π)` soit la fibre correspondante de `SuccessivePosition` ;
> 4. `Π` détermine une frontière `∂Π` ;
> 5. `FinalRole(Π)` soit la fibre `BoundaryFinalRole(∂Π)` d’un inductif indexé par cette frontière ;
> 6. sa contractilité soit dérivée de son unique constructeur ;
> 7. `FullRole(Π) ≔ InternalRole(Π) ⊎ FinalRole(Π)` ;
> 8. `j★` témoigne la relation fermante portée par `∂Π` ;
> 9. une construction `H₀` réalise exactement les rôles intérieurs ;
> 10. une continuation positive `H₁` soit engendrée ;
> 11. cette extension soit fidèlement classable dans `FullRole(Π)`.
>
> Alors :
>
> - `H₀` détermine une quantité structurelle intérieure exacte ;
> - son domaine est exactement délimité dans le système complet des rôles ;
> - la place fermante appartient au système complet sans être intérieurement réalisée ;
> - toute nouvelle occurrence fidèlement classable réalise nécessairement cette place ;
> - cette occurrence n’est pas identifiée au témoin `j★` ;
> - une interprétation de frontière peut réunir l’occurrence nouvelle, `∂Π` et `j★` sans les confondre ;
> - la génération d’une continuation est compatible avec la complétude structurelle du domaine intérieur.
>
> Si un régime `G` est exactement classifié par `H₀`, toute stricte extension est hors de ce régime.

---

# XXVII. Les deux piliers

## 61. Décomposition constitutive

```text
témoins relationnels
↓
Spine
↓
SuccessivePosition
↓
InternalRole
↓
occurrences
↓
réalisation exacte
↓
quantité structurelle
```

---

## 62. Circularité

```text
frontière structurale ∂Π
├──→ BoundaryFinalRole(∂Π)
│      ↓
│      r★
│
└──→ CloseΠ(t₀,i₀)
       ↓
       j★

InternalRole(Π)
+
FinalRole(Π)
↓
FullRole(Π)
↓
clôture structurelle
```

---

## 63. Articulation

```text
décomposition relationnelle
+
clôture circulaire
↓
domaine intérieur exactement déterminé
↓
quantité structurelle close
↓
continuation positive
↓
occupation du rôle final
↓
interprétation de frontière
↓
changement éventuel de régime
```

---

# XXVIII. Thèse synthétique

## 64. Formulation

> **La décomposition en rôles relationnels constitutifs détermine les unités à partir des relations qui engendrent leurs places.**
>
> **Les rôles intérieurs sont inductivement engendrés par les avancées relationnelles de l’épine de la présentation.**
>
> **La place fermante est une fibre d’un type inductif indexé par la frontière relationnelle structurale de la présentation.**
>
> **Sa contractilité est dérivée de son constructeur unique ; elle n’est pas postulée.**
>
> **Cette fibre est équivalente à `Unit` une fois la frontière fixée, mais cette équivalence oublie précisément l’index relationnel qui donne à la place sa provenance constitutive.**
>
> **Le témoin fermant `j★` habite la relation portée par cette même frontière, sans être identifié à la place finale.**
>
> **Le système complet des rôles est donc produit à partir de la présentation relationnelle elle-même.**
>
> **La réalisation exacte des rôles intérieurs détermine la quantité structurelle du domaine intérieur.**
>
> **La circularité délimite cette quantité dans un système complet comportant une place finale non encore réalisée intérieurement.**
>
> **La cardinalisation intervient seulement après cette constitution.**

---

# XXIX. Inversion des primitives

## 65. Forme finale

L’ordre :

```text
objets déjà donnés
↓
ensemble
↓
nombre
↓
relations
```

est remplacé, relativement au domaine considéré, par :

```text
relations primitives
↓
témoins relationnels
↓
structures inductives
↓
places
↓
rôles
↓
occurrences
↓
domaine exactement réalisé
↓
clôture structurelle
↓
quantité structurelle
↓
nombre éventuel
```

La relation ne constitue donc plus seulement une structure ajoutée à des objets préexistants.

Elle participe à déterminer :

```text
ce qui constitue une place
ce qui constitue un rôle
ce qui constitue une occurrence
ce qui constitue l’intérieur
ce qui constitue la frontière
ce qui constitue la quantité
```

avant toute lecture cardinale.

---

# XXX. Correspondance avec l’instance périmétrale

## 66. Instance existante

Dans l’instance périmétrale :

```text
Spine
↔
PerimeterSpine

SuccessivePosition
↔
NonClosingPosition

InternalRole
↔
NonClosingPosition

BoundaryFinalRole
↔
forme abstraite de FinalRequirement

FinalRole(Π)
↔
FinalRequirement(P)

contractilité
↔
finalRequirementContractible

FullRole
↔
CircularRequirement

j★
↔
finalJunction
```

Le mécanisme concret déjà formalisé montre que les positions non fermantes sont produites par la chaîne relationnelle, tandis que la place fermante et la jonction fermante restent distinctes.

---

# XXXI. Statut du travail

## 67. Partie conceptuelle stabilisée

La théorie abstraite distingue maintenant explicitement :

```text
genèse relationnelle des rôles intérieurs

genèse relationnelle de la place fermante

indexation de la place par sa frontière

contractilité dérivée

réalisation exacte de l’intérieur

clôture du système des rôles

continuation positive

détermination résiduelle

interprétation de frontière

changement de régime

cardinalisation ultérieure
```

Les deux objections principales contre une simple théorie de classification de porteurs sont ainsi traitées :

1. `InternalRole(Π)` n’est pas un type arbitraire : il est inductivement engendré par `Spine`;
2. `FinalRole(Π)` n’est pas un `Unit` indépendant : il est une fibre d’un inductif indexé par `∂Π`.

---

## 68. Prochaine étape formelle

Il reste désormais à construire cette abstraction comme théorie Lean indépendante.

Les premières structures à formaliser sont :

```text
Spine

SuccessivePosition

ClosingBoundary

BoundaryFinalRole

InternalRole

FinalRole

FullRole
```

puis à démontrer :

```text
contractilité de FinalRole

clôture de FullRole

décomposition exacte

théorème de délimitation

théorème résiduel

BoundaryInterpretation

ConstitutiveEquiv

réflexivité / symétrie / transitivité de ≃c
```

Enfin, il faudra montrer que l’architecture périmétrale existante instancie ces interfaces.

---

# XXXII. Conclusion

L’inversion recherchée prend maintenant une forme constructive :

```text
relations
↓
inductifs relationnellement indexés
↓
places
↓
rôles
↓
occurrences
↓
domaine exact
↓
clôture
↓
quantité structurelle
↓
cardinal éventuel
```

La quantité n’est plus primitivement la taille d’un ensemble d’unités supposées connues.

Elle devient la lecture d’un domaine dont les unités, les rôles et la frontière ont d’abord été constitués relationnellement.
