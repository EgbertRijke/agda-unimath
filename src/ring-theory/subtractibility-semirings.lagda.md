# Subtractibility in semirings

```agda
module ring-theory.subtractibility-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.divisibility-commutative-monoids

open import ring-theory.semirings
```

</details>

## Idea

Consider a [semiring](group-theory.semirings.md) `M`. The {{#concept "subtractibility relation" Disambiguation="Semiring" Agda=subtractible-Monoid}} is defined by saying that an element `y` of `M` divides an element `x` of `M` if it comes equipped with an element of type

```text
  subtractible-Semiring M y x := Σ (z : M), (z + y ＝ x)
```

## Definitions

### Subtractibility in a semiring

```agda
module _
  {l : Level} (R : Semiring l) (y x : type-Semiring R)
  where
  
  subtractible-Semiring : UU l
  subtractible-Semiring =
    div-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( y)
      ( x)

module _
  {l : Level} (R : Semiring l) {y x : type-Semiring R}
  (H : subtractible-Semiring R y x)
  where

  diff-subtractible-Semiring : type-Semiring R
  diff-subtractible-Semiring =
    quotient-div-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( H)

  is-left-difference-subtractible-Semiring :
    add-Semiring R diff-subtractible-Semiring y ＝ x
  is-left-difference-subtractible-Semiring =
    is-left-quotient-div-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( H)

  is-right-difference-subtractible-Semiring :
    add-Semiring R y diff-subtractible-Semiring ＝ x
  is-right-difference-subtractible-Semiring =
    is-right-quotient-div-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( H)
```

## Properties
