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
  ($<===$, $arrow.l.double.long$),
  ($<==$, $arrow.l.double$),
  ($emptyset$, $diameter$),
  ($<=$, $lt.eq.slant$),
  ($>=$, $gt.eq.slant$),
)

= Lot 1

Ce projet s'inscrit dans le cadre de la vérification de formules logiques pour la théorie des ordres denses sans bornes. 

Le problème central est de déterminer la vérité d'une formule mathématique contenant des comparaisons et des quantificateurs. La difficulté dans la vérification de ces formules réside dans le fait que ces quantificateurs portent sur des domaines "infinis", ne permettant pas de vérifier naïvement chaque solution par un algorithme dit de "bruteforce". Nous résolvons donc ce problème par la manipulation algébrique des formules, permettant une élimination systématique des quantificateurs.

Suite à l'approbation de nos professeurs, nous avons choisi de développer notre projet dans le langage OCaml, contrairement aux recommandations initiales d'utiliser Python. Il y a deux raisons à cela : 
- La représentation algébrique d'une formule se fait beaucoup plus naturellement sur OCaml, grâce au principe mathématique de "types inductifs", naturellement introduits par OCaml. Ceux-ci, combinés au très puissant "pattern matching", nous permettent d'obtenir un code bien plus lisible et court qu'en Python.
- Le troisième semestre de MIDL nous a introduit à l'UE ILU1. Nous y avons appris les bases d'OCaml, et ce projet nous a permis de nous familiariser avec ce langage dans un cadre approprié ainsi que d'en apprendre certaines fonctionnalités telles que les types inductifs et le pipelining.