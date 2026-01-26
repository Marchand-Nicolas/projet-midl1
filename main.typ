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
