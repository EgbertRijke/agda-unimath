# Divisibility in monoids

```agda
module group-theory.divisibility-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.divisibility-semigroups
open import group-theory.monoids
```

</details>

## Idea

Consider a [monoid](group-theory.monoids.md) `M`. The {{#concept "divisibility relation" Disambiguation="Monoid" Agda=div-Monoid}} is defined by saying that an element `y` of `M` divides an element `x` of `M` if it comes equipped with an element of type

```text
  div-Monoid M y x := Σ (z : M), (zy ＝ x) × (yz ＝ x)
```

Note that we require both [identifications](foundation-core.identity-types.md) `zy ＝ x` and `yz ＝ x`, since the multiplicative operation on a monoid is not necessarily commutative. If only one of the identifications holds, we say that `y` left-divides `x` or that `y` right-divides `x`, respectively.

## Definitions

### Left divisibility in a monoid

```agda
module _
  {l : Level} (M : Monoid l) (y x : type-Monoid M)
  where
  
  left-div-Monoid : UU l
  left-div-Monoid = left-div-Semigroup (semigroup-Monoid M) y x
```

### Right divisibility in a monoid

```agda
module _
  {l : Level} (M : Monoid l) (y x : type-Monoid M)
  where

  right-div-Monoid : UU l
  right-div-Monoid = right-div-Semigroup (semigroup-Monoid M) y x
```

### Divisibility in a monoid

```agda
module _
  {l : Level} (M : Monoid l) (y x : type-Monoid M)
  where

  div-Monoid : UU l
  div-Monoid = div-Semigroup (semigroup-Monoid M) y x

module _
  {l : Level} (M : Monoid l) {y x : type-Monoid M}
  (H : div-Monoid M y x)
  where

  quotient-div-Monoid : type-Monoid M
  quotient-div-Monoid = pr1 H

  is-left-quotient-quotient-div-Monoid :
    mul-Monoid M quotient-div-Monoid y ＝ x
  is-left-quotient-quotient-div-Monoid = pr1 (pr2 H)

  is-right-quotient-quotient-div-Monoid :
    mul-Monoid M y quotient-div-Monoid ＝ x
  is-right-quotient-quotient-div-Monoid = pr2 (pr2 H)
```

## Properties

### The divisibility relation on a monoid is reflexive

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  quotient-refl-div-Monoid : type-Monoid M
  quotient-refl-div-Monoid = unit-Monoid M

  is-left-quotient-quotient-refl-div-Monoid :
    mul-Monoid M quotient-refl-div-Monoid x ＝ x
  is-left-quotient-quotient-refl-div-Monoid =
    left-unit-law-mul-Monoid M x

  is-right-quotient-quotient-refl-div-Monoid :
    mul-Monoid M x quotient-refl-div-Monoid ＝ x
  is-right-quotient-quotient-refl-div-Monoid =
    right-unit-law-mul-Monoid M x

  refl-div-Monoid : div-Monoid M x x
  pr1 refl-div-Monoid = quotient-refl-div-Monoid
  pr1 (pr2 refl-div-Monoid) = is-left-quotient-quotient-refl-div-Monoid
  pr2 (pr2 refl-div-Monoid) = is-right-quotient-quotient-refl-div-Monoid
```

### The divisibility relation on a monoid is transitive

```agda
module _
  {l : Level} (M : Monoid l) {x y z : type-Monoid M}
  (H : div-Monoid M x y) (K : div-Monoid M y z)
  where

  quotient-transitive-div-Monoid : type-Monoid M
  quotient-transitive-div-Monoid =
    mul-Monoid M (quotient-div-Monoid M K) (quotient-div-Monoid M H)

  is-left-quotient-quotient-transitive-div-Monoid :
    mul-Monoid M quotient-transitive-div-Monoid x ＝ z
  is-left-quotient-quotient-transitive-div-Monoid =
    ( associative-mul-Monoid M _ _ _) ∙
    ( ap (mul-Monoid M _) (is-left-quotient-quotient-div-Monoid M H) ∙
    ( is-left-quotient-quotient-div-Monoid M K))

  is-right-quotient-quotient-transitive-div-Monoid :
    mul-Monoid M x quotient-transitive-div-Monoid ＝ z
  is-right-quotient-quotient-transitive-div-Monoid =
    inv (associative-mul-Monoid M _ _ _) ∙
    {!ap (mul-Monoid' M _) (is-right-quotient-quotient-div-Monoid M K) ∙ ?!}
```
