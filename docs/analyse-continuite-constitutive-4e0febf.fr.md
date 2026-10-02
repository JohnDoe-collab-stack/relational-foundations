# Analyse de la continuité constitutive et de la largeur opérationnelle

Analyse du 30 septembre 2026. Référence : branche `codex/constitutive-continuity-audit-20260930`, commit `4e0febf032821882069e7cfefd7e631fc8461d95`. Les sources ont été extraites par clonage local dans un dossier d’analyse distinct, puis recompilées. Les modifications locales ultérieures du dépôt de travail sont exclues de cette analyse.

La branche fournit une chaîne effective entre constitution relationnelle, découverte exécutée, décomposition locale, normalisation et régime d’obligations. Elle démontre que des profils constitués distincts peuvent recevoir une obligation opérationnelle commune avec des garanties sémantiques. Elle caractérise exactement la conservation de toute la largeur extensive par l’injectivité de `carry`. Elle ne caractérise pas par cette injectivité toute croissance exponentielle possible.

## Constitution relationnelle et profils

Le point de départ pertinent n’est pas une liste de profils booléens auxquels on ajouterait des noms relationnels. Un `CausalConstitutiveStageExecution` contient une ouverture, une relation particulière, son action sur une continuation et l’état suivant. Un `RelationalConstitutiveRoleStage` est indexé par cette étape et conserve les accords avec sa relation, son entrée et sa sortie effectivement exécutées.

L’histoire des rôles est dépendante : sa queue est indexée par l’histoire causale qui commence à l’état produit par la tête. Une occurrence d’ouverture comporte une position, un état structurel et un témoin de formation. Les profils sont ensuite des sélections d’occurrences sur cette histoire. Leur frontière finie et sa largeur sont dérivées.

Les équations de source et de provenance parfois prouvées par `rfl` expriment que ces vues ont la même autorité. Leur simplicité ne suffit pas à établir, seule, la causalité de l’exécution ; celle-ci vient aussi des fonctions de production et de leurs index dépendants.

La primitivité est relative aux objets étudiés et aux opérations formalisées. Le développement reçoit les règles de formation et les procédures de recherche ; il constitue les occurrences et les profils pertinents à partir de ces règles. Il ne reconstruit pas la théorie des types de Lean.

Sources : [étape causale](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/CausalConstitutiveExecution.lean:27), [rôles](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RelationalConstitutiveRoles.lean:31), [occurrences](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleIndexedProfiles.lean:68).

## Décomposition produite pendant l’exécution

`OperationalProductionProgram` distingue les primitives de découverte, d’application et de décomposition. Son interprète exécute chaque primitive et produit l’événement correspondant. Le programme de tête les compose dans cet ordre. L’exécuteur récursif poursuit ensuite à partir du nouvel état et du contexte opérationnel produit par cette tête.

L’accord `executeWithTrace_program_exact` relie l’exécuteur spécialisé à cet interprète. La chronologie des événements est démontrée séparément. Elle décrit l’ordre des primitives du modèle, pas un minutage des instructions d’une machine.

Le producteur local reçoit le préfixe constitué et l’étape exécutée ; sa signature ne reçoit pas la queue future. Il construit la licence de réduction puis le régime local comme image des sorties produites. Le regroupement n’est donc pas installé au moyen d’une largeur globale fournie comme hypothèse.

La découverte suivante lit la génération, la graine de recherche et la provenance conservées dans l’état. `runThreadedNextDiscovery` filtre effectivement les candidats à partir de cette provenance, puis exécute leur exploration. Des résultats de séparation montrent que des états ayant les mêmes données projetées peuvent différer par leur constitution et leurs résultats de découverte. La dépendance n’est donc pas réduite à la présence d’un champ historique inutilisé.

Pour autant, cette exécution suit des règles programmées dans une famille précise. « Produire sa décomposition » signifie construire ses données opérationnelles à partir de l’exécution ; cela ne signifie pas inventer ses propres règles de calcul. Dans la famille publique, une découverte réussie est canonique à profondeur fixée, tandis que sa disponibilité et sa trace dépendent du matériau transmis.

Sources : [programme et interprète](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/CausalOperationalExecution.lean:110), [récursion](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/CausalOperationalExecution.lean:188), [production locale](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/PrefixLocalOperationalProduction.lean:154), [découverte transmise](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ConstitutiveFeedback.lean:980), [séparateurs](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean:995).

## Identité conservée et obligation commune

La réduction possède une action sur les données et une preuve distincte de préservation du critère. La licence locale conserve aussi la distinction des occurrences transformée et retenue, et leur acceptation. Le regroupement ne repose donc pas sur l’égalité des sources ni sur la déclaration d’une branche impossible.

Deux portées doivent rester séparées. L’action et la préservation sémantique sont formulées pour des continuations arbitraires des types considérés. La convergence vers les sorties retenues concerne les continuations canoniques effectivement utilisées dans l’exécution. Le code ne démontre pas que toutes les données possibles sont identiques après transformation.

Les obligations globales contiennent une cible produite, une garantie de production et une spécification sémantique. Le régime est construit par transport exact depuis la politique issue des images locales. Ses lois de retour précèdent la preuve de largeur singleton : elles ne sont pas obtenues en supposant d’abord que tout le porteur vaut `Unit`.

Le théorème `carry_eq_iff_target_eq` établit que l’égalité des obligations correspond exactement à l’égalité des cibles produites. Les témoins publics exposent deux profils distincts ayant la même obligation. Une égalité dans le codomaine de `carry` n’est pas une égalité dans son domaine.

Sources : [licence locale](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/PrefixLocalOperationalProduction.lean:20), [sémantique](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/RoleProfileSemantics.lean:35), [obligation autorisée](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedCausalNormalization.lean:346), [transport exact](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/EndogenousDecomposition/ExecutedCausalNormalization.lean:492).

## Théorème exact de largeur

`ObligationRegime` comporte une frontière complète, sans doublon, et une application `carry` surjective depuis les identités sources. L’injectivité et l’égalité des largeurs ne sont pas des champs du régime.

Le noyau mathématique est un résultat fini général :

```text
largeur des obligations = largeur source
  si et seulement si carry est injective
```

La surjectivité donne la première borne de cardinalité. L’injectivité donne l’autre borne. Réciproquement, en présence d’une collision entre deux identités sources, retirer l’une d’elles conserve la couverture des obligations et produit une contradiction avec l’égalité des largeurs.

Dans la classe binaire, un théorème distinct calcule la largeur source `2 ^ stageCount`. La spécialisation donne donc :

```text
largeur des obligations = 2 ^ stageCount
  si et seulement si carry est injective
```

Ce noyau fini n’est pas, pris isolément, un nouveau principe de complexité. L’apport du développement est aussi de le raccorder à un régime effectivement produit, sémantiquement autorisé, sur le même porteur constitué.

Dans l’instance publique, `stageCount = input + 1`. Le régime identitaire conserve la largeur `2 ^ (input + 1)`. Le régime exécuté a une largeur exactement égale à un. La trace de largeur opérationnelle publique est bornée par deux.

Sources : [définition du régime](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/FiniteExtensiveAddressing.lean:156), [preuve des deux directions](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/FiniteExtensiveAddressing.lean:221), [classe binaire](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/ConstitutiveSearch/RelationalRoleExtensiveFamily.lean:114), [largeurs publiques](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/RelationalPerimeter/Computation/EndogenousOperationalDecomposition.lean:575).

## Correction nécessaire du paragraphe

L’expression « largeur opérationnelle exponentielle si et seulement si `carry` est injective » est trop large si « exponentielle » désigne une classe de croissance. Un régime non injectif peut encore avoir une largeur exponentielle inférieure à toute la largeur source.

Cette possibilité est déjà visible dans `RoleStatus.History.width` : une politique mixte a exactement `2 ^ pendingCount` obligations. Les rôles absorbés réduisent ce nombre sans obliger tous les rôles à être absorbés.

Une preuve d’analyse séparée a été construite sans modifier les sources de la révision. Sur une histoire de `count + 1` rôles munie de sa réduction exécutée, elle absorbe seulement la tête et conserve tous les rôles suivants comme obligations distinctes. Elle démontre :

```text
largeur source = 2 ^ (count + 1)
largeur du régime partiel = 2 ^ count
carry du régime partiel n’est pas injective
la transformation de ce régime préserve le critère
```

Ces politiques mixtes sont des comparaisons sur une histoire donnée ; elles ne sont pas annoncées comme d’autres exécutions publiques du programme. Elles suffisent à distinguer le théorème quantifié sur les régimes d’une affirmation sur toute croissance exponentielle.

La preuve [WidthProbe.lean](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/audit/WidthProbe.lean) compile et ses résultats audités sont sans dépendance axiomatique. Elle ne réfute aucun théorème de la branche. Elle réfute l’interprétation trop large de son commentaire.

Formulation exacte proposée :

> Dans la classe binaire formalisée, la largeur opérationnelle reprend intégralement la largeur extensive `2 ^ n` si et seulement si le régime conserve injectivement chaque profil comme obligation distincte. L’exécution publique produit, pour le même domaine de profils constitués, un régime autorisé de largeur un, sans identifier ces profils.

## Portée fondationnelle et rapport au tournant

Le résultat établit une différence entre individuation constitutive et statut opérationnel. Une fois les profils constitués, leur multiplicité ne prescrit pas leur conservation comme autant d’obligations indépendantes. Des relations produites et leurs garanties permettent de déterminer un autre portage.

Cela éclaire la discussion du tout et de ses parties : la multiplicité des unités constituées et la multiplicité des traitements requis sont deux lectures distinctes. Le nombre des profils ne détermine pas, à lui seul, le nombre des obligations du régime exécuté. Ce résultat ne constitue pas une théorie générale de toute relation partie–tout.

Le rapport au tournant constitutif affirmatif est conceptuel et architectural. Dans les deux cas, on conserve des données constituées tout en produisant une nouvelle situation et en examinant son statut relativement à un régime. La notion de régime n’a cependant pas le même type dans les deux théories : l’admission circulaire classifie des constructions, tandis que `ObligationRegime` porte des profils vers des obligations.

Il faut en particulier distinguer la fidélité de l’étiquetage résiduel et l’injectivité de `carry`. La première sert à déterminer l’occurrence nouvelle ; la seconde impose la conservation séparée de toutes les obligations. Aucun raccord démontré ici n’identifie `TotalLoop`, sortie du régime circulaire et injectivité de `carry`. Le seul mot « régime » ne fournit pas ce raccord.

Le caractère affirmatif computationnel est néanmoins effectif : le regroupement possède des cibles produites, des traces et des preuves de préservation. Il ne se réduit pas à un rejet de la multiplicité extensive.

## Limites du résultat de largeur

Le nombre d’obligations est la largeur de la frontière opérationnelle définie dans le modèle. Une obligation peut elle-même contenir plusieurs données. Sa largeur singleton n’implique pas que son contenu ni l’histoire conservée aient une taille constante.

La branche comporte aussi des comptes instrumentés et des bornes polynomiales pour leur modèle de coût. Ces résultats sont distincts de l’équivalence de largeur. La présente analyse n’a pas réaudité exhaustivement la propriété de couvrir tous les coûts d’une implémentation machine. Les définitions qui énumèrent la frontière source ou toutes les occurrences cibles parcourent une multiplicité extensive ; elles ne doivent pas être confondues avec le producteur local et la frontière opérationnelle exécutée.

La convergence et la préservation concernent les familles et critères formalisés. Les profils sont constitués sur une histoire de rôles déterminée par l’exécution ; le développement n’autorise pas une conclusion universelle sur tous les problèmes relationnels ou tous les arbres adaptatifs.

## Contrôles exécutés

Dans `C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930`, le contrôle `pwsh -NoProfile -File scripts/verify.ps1` a réussi sur le commit fixé :

| Contrôle | Résultat |
| --- | --- |
| Construction complète | 150 travaux réussis |
| Sources Lean du dépôt | 148 vérifiées |
| Reçus d’audit publiés pendant la construction | 3 143 sans dépendance axiomatique signalée |
| Avertissements et échecs d’audit | Aucun |
| Tests de rejet | 19, tous vérifiés |
| Stratification | 133 modules de production, aucun orphelin |
| Frontières d’import | Les quatre manifestes passent |
| Différences des fichiers suivis après analyse | Aucune |

Les reçus d’audit sont ceux des déclarations explicitement auditées par cette révision. Ils ne doivent pas être présentés comme un audit exhaustif de tous les auxiliaires privés ou générés. Les fichiers d’analyse sont extérieurs aux sources suivies du commit.

Le contrôle complémentaire `lake env lean audit/WidthProbe.lean` réussit. Ses résultats et les dépendances directement vérifiées produisent dix reçus sans dépendance axiomatique. Le [journal principal](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/audit-verification.log) et le [journal du contrôle complémentaire](C:/Users/frederick/Documents/relational-perimeter-audit-4e0febf-20260930/audit/width-probe.log) sont conservés. Le dépôt original n’a reçu aucune écriture de cette analyse.
