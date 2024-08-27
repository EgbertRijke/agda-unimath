# Divisibility in commutative monoids

```agda
module group-theory.divisibility-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation-core.identity-types
open import foundation.universe-levels

open import group-theory.divisibility-monoids
open import group-theory.commutative-monoids
```

</details>

## Idea

Consider a [commutative-monoid](group-theory.commutative-monoids.md) `M`. The {{#concept "divisibility relation" Disambiguation="Commutative Monoid" Agda=div-Monoid}} is defined by saying that an element `y` of `M` divides an element `x` of `M` if it comes equipped with an element of type

```text
  div-Commutative-Monoid M y x := Σ (z : M), (z + y ＝ x)
```

## Definitions

### Divisibility in a commutative monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l) (y x : type-Commutative-Monoid M)
  where
  
  div-Commutative-Monoid : UU l
  div-Commutative-Monoid =
    left-div-Monoid (monoid-Commutative-Monoid M) y x

module _
  {l : Level} (M : Commutative-Monoid l) {y x : type-Commutative-Monoid M}
  (H : div-Commutative-Monoid M y x)
  where

  quotient-div-Commutative-Monoid : type-Commutative-Monoid M
  quotient-div-Commutative-Monoid = pr1 H

  is-left-quotient-div-Commutative-Monoid :
    mul-Commutative-Monoid M quotient-div-Commutative-Monoid y ＝ x
  is-left-quotient-div-Commutative-Monoid = pr2 H

  is-right-quotient-div-Commutative-Monoid :
    mul-Commutative-Monoid M y quotient-div-Commutative-Monoid ＝ x
  is-right-quotient-div-Commutative-Monoid =
    commutative-mul-Commutative-Monoid M _ _ ∙
    is-left-quotient-div-Commutative-Monoid
```
