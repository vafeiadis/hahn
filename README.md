# Hahn : A Coq library for lists and relations

Hahn is a Coq library that contains a useful collection of lemmas and tactics
about lists and binary relations.

- HahnBase.v : basic tactics used throughout the development
- HahnFun.v : functional update
- HahnList.v : lemmas about lists
- HahnSets.v : lemmas about sets (i.e., unary relations)
- HahnRelationsBasic.v : binary relations
- HahnRewrite.v : support for rewriting equivalent relations
- HahnDom.v : (co)domain of a relation
- HahnMaxElt.v : maximal elements of a relation
- HahnMinPath.v : minimal paths/cycles over relations
- HahnPath.v : paths over relations
- HahnTotalExt.v : extension of a partial order to a total order.
- HahnTotalList.v : building finite relations for program order.
- HahnExtraNotation.v : notation for decidable equality.

## Build

- Install [Coq](http://coq.inria.fr) 8.6 [or 8.5]
- make

## Use

- In a Coq file, write "Require Import Hahn".
- Optionally, also "Require Import HahnExtraNotation".

