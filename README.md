# Hahn : A Coq library for lists and relations

Hahn is a Coq library that contains a useful collection of lemmas and tactics
about lists and binary relations.

- Hahn.v : exports all other files except HahnExtraNotation.v
- HahnBase.v : basic tactics used throughout the development
- HahnDom.v : (co)domain of a relation
- HahnEquational.v : relational equivalences
- HahnExtraNotation.v : notation for decidable equality.
- HahnFun.v : functional update
- HahnFuneq.v : functional preservation properties of relations
- HahnList.v : lemmas about lists
- HahnMaxElt.v : maximal elements of a relation
- HahnMinElt.v : minimum elements of a relation
- HahnWf.v : well-founded and finitely supported relations
- HahnMinPath.v : minimal paths/cycles over relations
- HahnPath.v : paths over relations
- HahnRelationsBasic.v : binary relations
- HahnRewrite.v : support for rewriting equivalent relations
- HahnSets.v : lemmas about sets (i.e., unary relations)
- HahnSegment.v : lemmas about segments of total orders
- HahnSorted.v : lemmas about sortedness of lists 
- HahnTotalExt.v : extension of a partial order to a total order.
- HahnTotalList.v : building finite relations for program order.

## Build

- Install [Coq](http://coq.inria.fr) 8.6 or 8.7 
- make

## Use

- In a Coq file, write "Require Import Hahn".
- Optionally, also "Require Import HahnExtraNotation".

