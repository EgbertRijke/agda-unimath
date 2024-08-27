# Partial inverse elements in semigroups

```agda
module group-theory.partial-inverse-elements-semigroups where
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

Consider an element `x` in a [semigroup](group-theory.semigroups.md) `G`. An {{#concept "partial inverse element" Disambiguation="Semigroup"}} of `x` is an element `y` such that the identifications

```text
  xyx = x
  yxy = y
```

hold. These laws are called the {{#concept "inner partial inverse law" Disambiguation="Semigroup" Agda=inner-partial-inverse-law-Semigroup}} and the {{#concept "outer partial inverse law" Disambiguation="Semigroup" Agda=outer-partial-inverse-law-Semigroup}}, respectively. If `y` is an inverse of `x` in the above sense, then the elements `xy` and `yx` are idempotent, i.e., we have that

```text
  xyxy = xy
  yxyx = yx.
```

Since the elements `xy` and `yx` are only idempotent, we say that `y` is only a partial inverse to `x`.

Partial nverses need not necessarily be unique. Semigroups in which every element has a unique partial inverse in the above sense are called [inverse semigroups](group-theory.inverse-semigroups.md), and they are used to study partial bijections.

## Definitions

### The inner partial inverse law in a semigroup

```agda
module _
  {l : Level} (G : Semigroup l) (x y : type-Semigroup G)
  where

  inner-partial-inverse-law-Semigroup : UU l
  inner-partial-inverse-law-Semigroup =
    mul-Semigroup G (mul-Semigroup G x y) x ＝ x
```

### The outer partial inverse law in a semigroup

```agda
module _
  {l : Level} (G : Semigroup l) (x y : type-Semigroup G)
  where

  outer-partial-inverse-law-Semigroup : UU l
  outer-partial-inverse-law-Semigroup =
    mul-Semigroup G (mul-Semigroup G y x) y ＝ y
```

### Partial inverse elements

```agda
module _
  {l : Level} (G : Semigroup l) (x : type-Semigroup G)
  where
  
  partial-inverse-element-Semigroup : UU l
  partial-inverse-element-Semigroup =
    Σ ( type-Semigroup G)
      ( λ y →
        inner-partial-inverse-law-Semigroup G x y ×
        outer-partial-inverse-law-Semigroup G x y)

module _
  {l : Level} (G : Semigroup l) {x : type-Semigroup G}
  (y : partial-inverse-element-Semigroup G x)
  where

  element-partial-inverse-element-Semigroup : type-Semigroup G
  element-partial-inverse-element-Semigroup = pr1 y

  is-inner-partial-inverse-partial-inverse-element-Semigroup :
    inner-partial-inverse-law-Semigroup G x
      element-partial-inverse-element-Semigroup
  is-inner-partial-inverse-partial-inverse-element-Semigroup = pr1 (pr2 y)

  is-outer-partial-inverse-partial-inverse-element-Semigroup :
    outer-partial-inverse-law-Semigroup G x
      element-partial-inverse-element-Semigroup
  is-outer-partial-inverse-partial-inverse-element-Semigroup = pr2 (pr2 y)
```
