#import "@preview/quick-maths:0.2.1": shorthands
#import "@preview/ctheorems:1.1.3": *
#import "@preview/zebraw:0.5.5" : *

#import "lib.typ": *

#show: university-assignment.with(
  title: "Projet MIDL 1",
  subtitle: "Implémentation de la procédure de décision dans la théorie des Ordres Denses",
  authors: ("DAVID--MULLER Robin", "MARCHAND Nicolas", "VASSEUR-LAURENS Odin"),
  details: (
    course: "Projet MIDL 1",
    due-date: "09/02/2026",
    software: "OCaml"
  )
)

#set enum(numbering: "a) i)")

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
