# Divisibility in semigroups

```agda
module group-theory.divisibility-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

Consider a [semigroup](group-theory.semigroups.md) `M`. The {{#concept "divisibility relation" Disambiguation="Semigroup" Agda=div-Semigroup}} is defined by saying that an element `y` of `M` divides an element `x` of `M` if it comes equipped with an element of type

```text
  div-Semigroup M y x := Σ (z : M), (zy ＝ x) × (yz ＝ x)
```

Note that we require both [identifications](foundation-core.identity-types.md) `zy ＝ x` and `yz ＝ x`, since the multiplicative operation on a semigroup is not necessarily commutative. If only one of the identifications holds, we say that `y` left-divides `x` or that `y` right-divides `x`, respectively.

## Definitions

### Left divisibility in a semigroup

```agda
module _
  {l : Level} (S : Semigroup l) (y x : type-Semigroup S)
  where
  
  left-div-Semigroup : UU l
  left-div-Semigroup = Σ (type-Semigroup S) (λ z → mul-Semigroup S z y ＝ x)
```

### Right divisibility in a semigroup

```agda
module _
  {l : Level} (S : Semigroup l) (y x : type-Semigroup S)
  where

  right-div-Semigroup : UU l
  right-div-Semigroup = Σ (type-Semigroup S) (λ z → mul-Semigroup S y z ＝ x)
```

### Divisibility in a semigroup

```agda
module _
  {l : Level} (S : Semigroup l) (y x : type-Semigroup S)
  where

  div-Semigroup : UU l
  div-Semigroup =
    Σ ( type-Semigroup S)
      ( λ z → (mul-Semigroup S z y ＝ x) × ( mul-Semigroup S y z ＝ x))
```
