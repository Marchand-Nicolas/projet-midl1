#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/ctheorems:1.1.3": *
#import "@preview/zebraw:0.5.5" : *

#let fontsize = 14pt;

#show : zebraw

#set heading(numbering: "I 1 a i  ")
#set text(font: "New Computer Modern", size: fontsize, lang: "fr")
#set linebreak(justify: true)
#set par(leading: 0.8em, spacing: 1.2em, justify: true, linebreaks: "optimized")
#show raw: set text(font: "New Computer Modern")
#show math.cases: it => {
  show math.frac: frc => { math.display(frc) }
  it
}
#set enum(numbering: "a) i)")
#let hd = [
  #table(columns: (auto, auto, auto), stroke: none, [
    _noms_
  ],
  "Projet MIDL 1", 
  "Implantation de la procédure de décision"
  )
]
#set page(
  paper: "a4",
  header: hd,
  numbering: "I",
  margin: (top: fontsize + 2em, bottom: 2em, left: 5em, right: 5em),
)
#set grid(
  row-gutter: 1.5em,
  column-gutter: 2em,
)
#show: shorthands.with(
  ($+-$, $plus.minus$),
  ($<===$, $arrow.l.double.long$),
  ($<==$, $arrow.l.double$),
  ($emptyset$, $diameter$),
  ($<=$, $lt.eq.slant$),
  ($>=$, $gt.eq.slant$),
  ($(->$, $arrow.r.hook$),
  ($-+$, $minus.plus$),
)

= Lot 1
== Tâches T1, T2

// Fonctions implémentées :

// - dual : formula $->$ formula
  
//   Renvoie la forme duale de la formule.
// - univ_to_exist : formula $->$ formula
  
//   Transforme les quantificateurs universels $forall$ en quantificateur d'existence $exists$ à l'aide de l'équivalence :
//   $ forall x, P(x) equiv not(exists x, not P(x)) $
// - is_prenex : formula $->$ bool

//   Vérifie si une formule est sous forme prénexe, c'est-à-dire que les quantificateurs sont au début.
// - neg_inside : formula $->$ formula
  
//   Repousse les négations d'une formule vers l'intérieur.
// - neg_elim : formula $->$ formula

//   Élimine les négations d'une formule en utilisant les équivalences :
//   $
//   not (F = G) equiv (F > G) or (G > F)  \
//   not(F > G) equiv (F = G) or (G > F) \
//   $

// Tous ces algorithmes n'étant que des parcours de graphes, ils ne sont que de complexité $O(|X| + |U|)$ avec $X$ l'ensemble des noeuds de l'arbre et $U$ l'ensemble des arêtes de l'arbre.
// Notons qu'ici, $X$ est l'ensemble (avec répétitions) des symboles utilisés.

// Ainsi les arêtes sont les liens engendrés par les quantificateurs et relations binaires.
// En notant que l'arité d'une relation binaire est $2$ et celle d'un quantificateur est $1$. Ainsi $|U| = O(2 |X|) = O(|X|)$.

// Finalement, ces algorithmes sont tous de complexité $O(|X|)$, ce qui est très correct.

// Notre procédure de décision est alors, pour l'instant, de complexité $O(|X|)$.

// Cependant, nous allons maintenant passer à la suppression de variables. En réalité, c'est là le coeur de l'algorithme.

