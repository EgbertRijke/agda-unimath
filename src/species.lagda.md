# Species

The theory of combinatorial species is a branch of mathematics that studies the
enumeration and classification of structures. It provides a framework for
analyzing and understanding various combinatorial objects and their
relationships. The concept of a species was introduced by the Canadian
mathematician André Joyal in the 1980s as a way to formalize the notion of
combinatorial structures.

In combinatorics, a structure refers to any collection of objects or elements
that have certain properties or satisfy certain constraints. For example,
permutations, graphs, trees, and partitions are all examples of combinatorial
structures. The idea behind combinatorial species is to define a functor that
assigns a set of structures to each set. Such functors preserve isomorphisms,
and hence preserve "sameness" or "equivalence" in combinatorial structures.

Formally, a (finite) combinatorial species is a functor from the category of
finite sets with bijections to itself. In simple terms, this means that for
every finite set `A`, the species assigns a set `S(A)` of structures to `A`.
Additionally, for every bijection `f : A ≅ B`, the species provides a
structure-preserving isomorphism `S(f): S(A) ≅ S(B)`. This bijection ensures
that structures that are essentially the same in A are mapped to structures that
are essentially the same in B.

In univalent mathematics, the formal definition of combinatirial species
simplifies significantly. The category of finite sets with bijections is simply
the type of all finite sets, since the univalence axiom implies that
identifications of finite sets are equivalently described by bijections of
finite sets. The definition of [finite species](species.finite-species.md) in
the agda-unimath library is therefore simply a function `S : 𝔽 → 𝔽`.

The concept of species allows us to define operations on structures in a
coherent and systematic way. For instance, we can define the coproduct of two
species, which corresponds to taking the disjoint union of structures. We can
also define the product of two species, which represents combining structures in
a pairwise manner. These operations help us study and analyze the combinatorial
structures more effectively.

Furthermore, we can associate to each species a polynomial endofunctor, which is
called the generating series of a species. The polynomial endofunctor
`X ↦ P_S(X)` of a species `S` is given by

```text
  P_S(X) := ∑_{A : 𝔽} S(A) × Xᴬ.
```

The theory of polynomial endofunctors allows us to study and manipulate species
using algebraic tools. For example, we can compose polynomial endofunctors,
multiply them, and perform other algebraic operations.

Combinatorial species provide a powerful language for studying combinatorial
structures and counting them. They enable us to derive elegant and general
results by manipulating and combining species using functorial operations. This
theory has applications in various areas of mathematics and computer science,
such as algebraic combinatorics, theoretical computer science, and theoretical
physics.

## Files in the species folder

```agda
module species where

open import species.cartesian-exponents-species-of-types public
open import species.cartesian-products-species-of-types public
open import species.cauchy-composition-species-of-types public
open import species.cauchy-composition-species-of-types-in-subuniverses public
open import species.cauchy-exponentials-species-of-types public
open import species.cauchy-exponentials-species-of-types-in-subuniverses public
open import species.cauchy-products-species-of-types public
open import species.cauchy-products-species-of-types-in-subuniverses public
open import species.cauchy-series-species-of-types public
open import species.cauchy-series-species-of-types-in-subuniverses public
open import species.composition-cauchy-series-species-of-types public
open import species.composition-cauchy-series-species-of-types-in-subuniverses public
open import species.coproducts-species-of-types public
open import species.coproducts-species-of-types-in-subuniverses public
open import species.cycle-index-series-species-of-types public
open import species.derivatives-species-of-types public
open import species.dirichlet-exponentials-species-of-types public
open import species.dirichlet-exponentials-species-of-types-in-subuniverses public
open import species.dirichlet-products-species-of-types public
open import species.dirichlet-products-species-of-types-in-subuniverses public
open import species.dirichlet-series-species-of-finite-inhabited-types public
open import species.dirichlet-series-species-of-types-in-subuniverses public
open import species.equivalences-species-of-types public
open import species.equivalences-species-of-types-in-subuniverses public
open import species.exponentials-cauchy-series-of-types public
open import species.exponentials-cauchy-series-of-types-in-subuniverses public
open import species.hasse-weil-species public
open import species.morphisms-finite-species public
open import species.morphisms-species-of-types public
open import species.pointing-species-of-types public
open import species.precategory-of-finite-species public
open import species.products-cauchy-series-species-of-types public
open import species.products-cauchy-series-species-of-types-in-subuniverses public
open import species.products-dirichlet-series-species-of-finite-inhabited-types public
open import species.products-dirichlet-series-species-of-types-in-subuniverses public
open import species.small-cauchy-composition-species-of-finite-inhabited-types public
open import species.small-cauchy-composition-species-of-types-in-subuniverses public
open import species.species-of-finite-inhabited-types public
open import species.species-of-finite-types public
open import species.species-of-inhabited-types public
open import species.species-of-types public
open import species.species-of-types-in-subuniverses public
open import species.unit-cauchy-composition-species-of-types public
open import species.unit-cauchy-composition-species-of-types-in-subuniverses public
open import species.unlabeled-structures-species public
```
