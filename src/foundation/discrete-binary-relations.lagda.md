# Discrete binary relations

```agda
module foundation.discrete-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.empty-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A [binary relation](foundation.binary-relations.md) `R` on `A` is said to be
{{#concept "discrete" Disambiguation="binary relation" Agda=is-discrete-Relation}}
if it does not relate any elements, i.e., if the type `R x y` is empty for all
`x y : A`. In other words, a binary relation is discrete if and only if it is
the initial binary relation. This definition ensures that the inclusion of
[discrete directed graphs](graph-theory.discrete-directed-graphs.md) is a left
adjoint to the forgetful functor `(V , E) ↦ (V , ∅)`.

The condition of discreteness of binary relations compares to the condition of
[discreteness](foundation.discrete-reflexive-relations.md) of
[reflexive relations](foundation.reflexive-relations.md) in the sense that both
conditions imply initiality. Nevertheless, the condition of discreteness on
reflexive relations asserts that the type family `R x` is
[torsorial](foundation-core.torsorial-type-families.md) for every `x : A`, which
looks quite differently.

The condition of torsoriality is not adequate as a condition for discreteness
for arbitrary binary relations. For example, the binary relation on
[natural numbers](elementary-number-theory.natural-numbers.md) given by
`R m n := (m + 1 ＝ n)`, relating natural numbers as follows

```text
  0 ---> 1 ---> 2 ---> ⋯,
```

satisfies the condition that the type family `R m` is torsorial for every
`m : ℕ`, simply because the relation `R` is a
[functional correspondence](foundation.functional-correspondences.md). Since
this relation relates distinct elements, it is typically not considered to be
discrete.

## Definitions

### The predicate on relations of being discrete

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-discrete-prop-Relation : Prop (l1 ⊔ l2)
  is-discrete-prop-Relation =
    Π-Prop A (λ x → Π-Prop A (λ y → is-empty-Prop (R x y)))

  is-discrete-Relation : UU (l1 ⊔ l2)
  is-discrete-Relation = type-Prop is-discrete-prop-Relation

  is-prop-is-discrete-Relation : is-prop is-discrete-Relation
  is-prop-is-discrete-Relation = is-prop-type-Prop is-discrete-prop-Relation
```

## See also

- [Discrete reflexive relations](foundation.discrete-reflexive-relations.md)
- [Discrete directed graphs](graph-theory.discrete-directed-graphs.md)
- [Discrete-reflexive graphs](graph-theory.discrete-reflexive-graphs.md)