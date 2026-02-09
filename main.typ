#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/ctheorems:1.1.3": *
#import "@preview/zebraw:0.5.5" : *
#import "@preview/codelst:2.0.2": sourcecode
#import "@preview/plotsy-3d:0.2.1" : *
#import "@preview/diagraph:0.3.6" : *

#import "lib.typ": *

#show: university-assignment.with(
  title: "Projet MIDL 1",
  subtitle: "Implémentation de la procédure de décision dans la théorie des Ordres Denses sans Bornes",
  authors: ("DAVID--MULLER Robin", "MARCHAND Nicolas", "VASSEUR-LAURENS Odin"),
  details: (
    course: "Projet MIDL 1",
    due-date: "09/02/2026",
    software: "OCaml"
  )
)

#set enum(numbering: "a) i)")
#set text(lang: "fr")

#let cdot = $dot.c$

#show link: underline

#show: shorthands.with(
  ($<===$, $arrow.l.double.long$),
  ($<==$, $arrow.l.double$),
  ($emptyset$, $diameter$),
  ($<=$, $lt.eq.slant$),
  ($>=$, $gt.eq.slant$),
)

= Lot 1

Ce projet s'inscrit dans le cadre de la vérification de formules logiques pour la théorie des ordres denses sans bornes. 

Le problème central est de déterminer la vérité d'une formule mathématique contenant, dans un premier temps, des comparaisons et des quantificateurs. La difficulté dans la vérification de ces formules réside dans le fait que ces quantificateurs portent sur des domaines "infinis", ne permettant pas de vérifier naïvement chaque solution par un algorithme dit de "bruteforce". Nous résolvons donc ce problème par la manipulation algébrique des formules, permettant une élimination systématique des quantificateurs.

Suite à l'approbation de nos professeurs, nous avons choisi de développer notre projet dans le langage OCaml, contrairement aux recommandations initiales d'utiliser Python. Il y a deux raisons à cela : 
- La représentation algébrique d'une formule se fait beaucoup plus naturellement sur OCaml, grâce au principe mathématique de "types inductifs", naturellement introduits par OCaml. Ceux-ci, combinés au très puissant "pattern matching", nous permettent d'obtenir un code bien plus lisible et court qu'en Python.
- Le troisième semestre de MIDL nous a introduit à l'UE ILU1. Nous y avons appris les bases d'OCaml, et ce projet nous a permis de nous familiariser avec ce langage dans un cadre approprié ainsi que d'en apprendre certaines fonctionnalités telles que les types inductifs et le pipelining.

Nous avons donc commencé par traduire le script python fourni par nos professeurs dans notre langage de choix. 

Ensuite, nous avons assez facilement implémenté le prétraitement. Notre choix a été de séparer chaque clause de notre forme normale disjonctive dans une liste après avoir poussé les quantificateurs existentiels dans celle-ci. 

Nous nous retrouvons finalement en train de traiter un ensemble de disjonctions.
Nous avons donc choisi de classifier dans un dictionnaire toutes les contraintes sur chaque variable quantifiée : égalités, majorantions, minorations, formules indépendantes ($chi$). Maintenant que cela est fait, nous avons appliqué toutes les règles de suppression de quantification universelle, à l'exception de la seconde ("si $psi$ contient $x < x : (exists x.psi)<-> bot$") que nous avons supprimé lors de notre implémentation du Lot 2 ; cela sera donc détaillé plus tard.

#pagebreak()

= Lot 2
Maintenant que nous pouvons appliquer notre procédure à toute proposition de la théorie des ordres denses, nous pouvons nous pencher sur l'arithmétique des nombres rationnels. On remarque que peu de choses changent, il n'y a pas de collision entre le prétraitement et la complexification des (in)égalités "générales" qui se résumaient à des comparaisons entre deux variables.

Ce qui change le plus, c'est que l'on ne peut pas simplement avoir de majoration/minoration sur une variable $x$ en regardant le terme de gauche ou le terme de droite. Dans le cas d'une égalité, c'est facile ! Nous avons appris la méthode du pivot de Gauss qui convient parfaitement à cette situation, il nous suffira de l'appliquer à notre égalité pour isoler $x$. Dans le cas d'une inégalité, nous appliquons la même chose, la seule différence est qu'il faut faire attention aux changements de signe (c'est ce que l'on appelle l'"Élimination de Fourier-Motzkin"). Ainsi, nous obtenons des majorations/minorations de $x$ par rapport aux autres variables.

Supposons l'inégalité : $A < B$. Dans ce cas, celle-ci est équivalente à $A - B < 0$.
Nous pouvons effectuer une extraction du coefficient $x$ dans $A - B$ (cela pourrait s'apparenter à une sorte de division euclidienne d'un polynôme de degré 1 par $x$). Ainsi, nous aurons un coefficient scalaire $q$ et un reste $R$ ne dépendant pas de $x$. Cela nous donnera : $q x + R < 0 <==> q x < -R$.
- Dans le cas où $q = 0$, nous avons une proposition indépendante de $x$ : $R < 0$. 
- Dans le cas où $q > 0$, nous avons $x < -R/q$
- Dans le cas où $q < 0$, nous avons $x > -R/q$
Le cas de l'égalité s'effectue de la même manière.

C'est cette étape de normalisation qui rend l'étape 3.2 mentionnée précedemment (suppression triviale de $x < x$) obsolète : notre algorithme transforme naturellement $x < x$ en $0 < 0$, qui est identifié comme une formule indépendante (fausse) et traitée lors de l'étape 3.6.

Nous avons d'abord introduit une fonction `simplify_term` qui simplifiera au maximum les formules algébriques, notamment à l'aide de la règle d'associativité, pour simplifier les calculs. Ensuite, nous avons créé la fonction d'extraction de coefficients `get_coeff` pour finalement l'appliquer à la fonction de normalisation `isolate`. 

Il a aussi fallu changer les fonctions implémentées précédemment : après avoir supprimé l'étape 3.2, nous avons rajouté les comparaisons arithmétiques à la fonction `simplify`. Nous pensions avoir fini lorsque l'exemple de proposition "$exists x . x + 5 > x + 2$" ne fonctionnait pas. Le dysfonctionnement venait de la fonction `check_var` car elle ne devait plus seulement regarder à droite et à gauche de l'inégalité, mais bien parcourir récursivement l'arbre syntaxique créé par les expressions arithmétiques à gauche et à droite. Ainsi, après avoir fait ce changement, notre procédure s'est mise à fonctionner sur tous nos tests.   

En dernière retouche, nous avons finalement remplacé nos flottants par un type `Rational` afin de représenter nos nombres par des fractions, ce qui nous permet de ne pas avoir d'approximations lors des calculs. Par exemple : $exists x. x + 0.3 < x + 0.1 + 0.2$ qui est faux, mais renvoyait vrai car $0.1 + 0.2$ est stocké comme "$0.300000000000000044$" au lieu de $0,3$ :
#sourcecode(numbering:none)[
```
utop # 0.1 +. 0.2;;
- : float = 0.300000000000000044
```
]
#pagebreak()

== Ouvertures
- Bien que notre implémentation de l'élimination des quantificateurs soit maintenant fonctionnelle pour l'Arithmétique Linéaire Rationnelle, elle repose sur une version standard de l'algorithme de Fourier-Motzkin. Cette méthode est "naïve" car elle peut créer des inégalités redondantes, et en crée beaucoup. #link("https://fr.wikipedia.org/wiki/%C3%89limination_de_Fourier-Motzkin#Extension_:_acc%C3%A9l%C3%A9ration_de_Imbert")[La page Wikipedia] nous introduit alors à une accélération de l'algorithme créée par Jean-Louis Imbert en 1990 qui permet d'éliminer certaines contraintes selon la manière dont elles ont été construites, réduisant considérablement les formules intermédiaires de la procédure. L'intégration de cet algorithme aurait cependant nécessité une refonte profonde des structures de données que l'on utilise car elle nécessite une traçabilité des inégalités prises en compte. 

- Nous aurions pu généraliser notre algorithme à la #link("https://fr.wikipedia.org/wiki/Corps_r%C3%A9el_clos#Th%C3%A9orie_des_corps_r%C3%A9els_clos")[Théorie des corps réels clos], qui aurait nécessité l'implémentation de l'algorithme de #link("https://jfla.inria.fr/static/slides/jfla2025-Vermande.pdf")[Décomposition Algébrique Cylindrique] de Collins.
- Un cadre d'étude intéressant est aussi l'#link("https://fr.wikipedia.org/wiki/Arithm%C3%A9tique_de_Presburger")[Arithmétique Linéaire Entière, dite de "Presburger"], beaucoup plus proche de l'Arithmétique Linéaire Rationnelle, à l'exception de 

#pagebreak()

= Lot 3

== Élaboration de la méthode

Il nous est demandé de faire un jeu consistant pour le joueur $J$ de trouver un exemple validant une formule satisfiable ou invalidant un résultat non satisfiable. L'ordinateur $O$ doit alors trouver une stratégie pour bloquer les choix du joueur. Dans un premier temps, l'ordinateur doit vérifier la véracité de la formule en appliquant totalement la suppression des quantificateurs. Après avoir enregistré l'ordre des quantificateurs dans la formule de base (sous forme prénexe), il faut que $O$ ait une bonne vue d'ensemble des contraintes imposées à chaque variable. Notre implémentation des clauses après le prétraitement est déjà parfaite, elle représente tout ce dont on a besoin. Raisonnons par l'exemple :

Soit la formule $exists x. forall y. exists z. forall t.$$P(x,y,z,t)$ avec le prédicat $P(x,y,z,t) equiv psi_1(x,y) or psi_2(x,y,z) or psi_3(x,y,z,t)$ où les $psi_i$ sont des prédicats représentants un ensemble de disjonction. Représentons l'arbre $({x, y, z, t} union {(psi_i)}, {(a,psi) | psi "dépend de "a})$ :
#raw-render(
  ```dot
  digraph {
    x -> psi_1
    x -> psi_2
    x -> psi_3
    y -> psi_1
    y -> psi_2
    y -> psi_3
    z -> psi_2
    z -> psi_3
    t -> psi_3
  }
  ```
)
Au premier tour, $J$ choisit une valeur valide pour tous les $psi$. $O$ va donc devoir choisir une valeur qui va influencer $psi_2, psi_3$. Son intérêt est d'invalider tous les $psi_i$. Il est obligé d'agir en priorité sur les variables pour lesquelles $y$ est la seule variable dans son camps à avoir un rôle sur l'invalidité, c'est-à-dire $psi_1$ et $psi_2$. Il peut éventuellement choisir des valeurs qui servent à invalider $psi_3$, mais ce n'est pas la priorité. 
- Sur $psi_1$, tout ne sera que sous une forme équivalente à une égalité/inégalité linéaire sur $y$. Notons $E_1 = { y in QQ | psi_1(x,y) }$ l'ensemble des valeurs vérifiant.
- De même pour $psi_2(x, y, z)$, qui dépend encore de $z$ (choisi par $J$ au prochain tour). Pour bloquer le joueur, $O$ doit choisir $y$ tel qu'il devienne impossible pour $J$ de trouver un $z$ satisfaisant $psi_2$ plus tard. Notons $E_2= { y in QQ | exists z in QQ : psi_2(x,y,z) }$ l'ensemble des valeurs.
Ainsi, si $E_1 union E_2 != QQ$, alors on peut prendre $y in QQ without (E_1 union E_2)$, sinon $J$ a gagné. On peut facilement vérifier si $E_1 union E_2 = emptyset$ en éliminant les quantificateurs de la formule. Si $E_1 union E_2 != QQ$, on peut donc trouver des valeurs qui vont falsifier $psi_1$ et $psi_2$. Cela ressemble à de l'algèbre linéaire : en supposant qu'il n'y a que des égalités, on tombe sur un sous-espace affine (ici, de dimension 1), alors rajouter des inégalités va créer une forme géométrique. On peut parler de #link("https://lalgebrisant.fr/images/pdfArticles/LePolyedreVide.pdf")["polyèdre convexe"]. Trouver un point extérieur est intuitif : le polyèdre étant défini par des "facettes", il suffirait de choisir une valeur de $y$ qui permet d franchir l'une de ces bornes. L'ordinateur peut en réalité prendre directement l'union des polyèdres/sous-espaces affines générés par $psi_1, psi_2, psi_3$ afin de les invalider par la théorie des ordres denses sans bornes; l'élimination des quantificateurs va projeter l'union de formes géométriques et la projeter sur l'axe de $y$. Ainsi, $O$ gagne forcément, car la subsitution d'une variable quantifiée par une constante n'est qu'une projection de cet ensemble de formes sur une dimension plus faible. Il peut ainsi jouer une valeur quelconque jusqu'à la fin. Cette approche géométrique (intersections de polyèdres/sous-espaces affines et projections) correspond exactement à ce que calcule l'algorithme d'élimination des quantificateurs avec Fourier-Motzkin et Gauss-Jordan implémentés dans le Lot 2.
L'ensemble $I$ récupéré en sortie de l'élimination de $exists z. forall t. psi_1(x,y) or psi_2(x,y,z) or psi_3(x,y,z,t)$ est la représentation de l'union des polyèdres et/ou espaces affines représentés par les clauses ($E_1 union E_2 union E_3$) projetée sur l'axe $(O y)$. Il suffit de prendre $y in QQ without I$ pour gagner.

Pour terminer, supposons que $O$ soit dans le rôle inverse (il doit prouver une existence). Alors il suffit de faire la même chose, mais en prenant une valeur dans $I$, et perdra si la projection sur l'axe $(O y)$ est l'ensemble vide. Cependant, dans ce cas, il pourrait être mené à choisir une valeur d'existence lors du choix de la valeur de $t$.

#set enum(numbering: "1) a)")
== Méthode
Ainsi, la méthode est finalement assez simple :

Si l'on note l'ensemble des variables $(x_i)_(1 <= i <= n)$ et $(psi_i)_(1 <= i <= m)$ l'ensemble des clauses de la DNF de $P$. Si l'ordinateur est au tour $k$, les variables $x_i$ sont fixées pour tout $i < k$. Ainsi, on élimine les quantificateurs des variables $x_(k+1), dots, x_n$ de la proposition de départ en  substituant les $k-1$ premières variables par les valeurs choisies. Supposons que nous sommes au tour de $O$. 
+ Si $O$ doit réfuter la formule :
  + Si le résultat de l'élimination donne $top$, $O$ a perdu, il joue une valeur par défaut. Si le résultat donne $bot$, il a gagné, il joue aussi une valeur par défaut. Sinon, Notons $I$ l'intervalle représentée par le résultat ; qui est soit une union d'intervalles, soit un singleton.
  + $O$ choisit $x in QQ without I$, $J$ n'a plus la possibilité de gagner ($O$ a "neutralisé" $J$ en falsifiant chaque clause, comme dans l'exemple).
+ Si $O$ doit valider la formule :
  + Si le résultat de l'élimination donne $bot$, $O$ a perdu, il joue une valeur par défaut et le fera jusqu'à la fin de la partie. S'il donne $top$, il joue aussi une valeur par défaut. Sinon $O$ choisit $x in I$.

#pagebreak()

= Manuel

Pour lancer le code dans un REPL, vous pouvez exécuter la commande : `./run_repl.sh`. Sinon, vous pouvez lancer le REPL manuellement en exécutant `utop -init syntax.ml`

== Construction d'une formule
Nous avons créé des fonctions macro permettant une construction assez simple des propositions. Voici un tableau les regroupant :
#table(
  columns: (1fr, 1fr),
  table.header([Constructeur logique],[Équivalent]),
  [$top$], [`top`],
  [$bot$], [`bottom`],
  [$x < y$], [`lt (var "x") (var "y")`],
  [$x = y$], [`equal (var "x") (var "y")`],
  [$P or Q$], [`disj P Q`],
  [$P and Q$], [`conj P Q`],
  [$not P$], [`notf P`],
  [$P -> Q$], [`implies P Q`],
  [$exists x. P$],[`exists "x" P`],
  [$forall x. P$], [`forall "x" P`],
  [$x$ (variable)], [`var x`],
  [$n in ZZ$], [`val_ n`],
  [$p/q$ avec $(p,q) in ZZ^2$], [`frac p q`],
  [$x + y$], [`add x y`],
  [$x - y$], [`sub x y`],
  [$a cdot x$ avec $a in ZZ$], [`mul a x`],
  [$p/q cdot x$], [`mul_frac p q x`]
)

L'exécution de la procédure se fera via la fonction `final_test` avec le nom de la formule (voir exemples). 

#pagebreak()

== Exemples

- $forall x.forall y.(x<y->exists z.(x<z and z<y))$ s'écrira : 
  #sourcecode[
  ```ml
  let density = forall "x" (
    forall "y" (
      implies (
          lt (var "x") (var "y")
        ) 
        (
          exists "z" (
            conj (
                lt (var "x") (var "z")
              ) 
              (
                lt (var "z") (var "y")
              )
            )
          )
        )
      )
  ```
]

- $forall x. exists y. (x < y)$ s'écrira :
  #sourcecode[
  ```ml
  let no_sup_extremum = forall "x" (exists "y" (lt (var "x") (var "y")))
  ```
]

Exemples d'exécution de la procédure :

#sourcecode[
  ```ml
  final_test density "Densité"
  ```
]

Qui renverra :
#sourcecode(numbering:none)[
```
Nom de la formule : "Densité"
Input initial : (∀x.(∀y.(¬(x < y) ∨ (∃z.((x < z) ∧ (z < y))))))
Output final : Τ
```
]