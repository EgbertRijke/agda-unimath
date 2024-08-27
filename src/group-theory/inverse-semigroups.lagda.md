# Inverse semigroups

```agda
module group-theory.inverse-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.partial-inverse-elements-semigroups
open import group-theory.semigroups
```

</details>

## Idea

An {{#concept "inverse semigroup" Agda=Inverse-Semigroup}} is an algebraic
structure that models partial bijections.
Inverse semigroups are [semigroups](group-theory.semigroups.md) in which
elements have unique [inverses](group-theory.inverse-elements-semigroups.md) in the sense that for
each `x` there is a unique `y` such that `xyx = x` and `yxy = y`.

## Definitions

### Inverse semigroups

```agda
is-inverse-Semigroup :
  {l : Level} (S : Semigroup l) → UU l
is-inverse-Semigroup S =
  (x : type-Semigroup S) → is-contr (partial-inverse-element-Semigroup S x)

Inverse-Semigroup : (l : Level) → UU (lsuc l)
Inverse-Semigroup l = Σ (Semigroup l) is-inverse-Semigroup

module _
  {l : Level} (S : Inverse-Semigroup l)
  where

  semigroup-Inverse-Semigroup : Semigroup l
  semigroup-Inverse-Semigroup = pr1 S

  set-Inverse-Semigroup : Set l
  set-Inverse-Semigroup = set-Semigroup semigroup-Inverse-Semigroup

  type-Inverse-Semigroup : UU l
  type-Inverse-Semigroup = type-Semigroup semigroup-Inverse-Semigroup

  is-set-type-Inverse-Semigroup : is-set type-Inverse-Semigroup
  is-set-type-Inverse-Semigroup =
    is-set-type-Semigroup semigroup-Inverse-Semigroup

  mul-Inverse-Semigroup :
    (x y : type-Inverse-Semigroup) → type-Inverse-Semigroup
  mul-Inverse-Semigroup = mul-Semigroup semigroup-Inverse-Semigroup

  mul-Inverse-Semigroup' :
    (x y : type-Inverse-Semigroup) → type-Inverse-Semigroup
  mul-Inverse-Semigroup' = mul-Semigroup' semigroup-Inverse-Semigroup

  associative-mul-Inverse-Semigroup :
    (x y z : type-Inverse-Semigroup) →
    mul-Inverse-Semigroup (mul-Inverse-Semigroup x y) z ＝
    mul-Inverse-Semigroup x (mul-Inverse-Semigroup y z)
  associative-mul-Inverse-Semigroup =
    associative-mul-Semigroup semigroup-Inverse-Semigroup

  is-inverse-semigroup-Inverse-Semigroup :
    is-inverse-Semigroup semigroup-Inverse-Semigroup
  is-inverse-semigroup-Inverse-Semigroup = pr2 S

  partial-inverse-element-Inverse-Semigroup :
    (x : type-Inverse-Semigroup) →
    partial-inverse-element-Semigroup semigroup-Inverse-Semigroup x
  partial-inverse-element-Inverse-Semigroup x =
    center (is-inverse-semigroup-Inverse-Semigroup x)

  inv-Inverse-Semigroup : type-Inverse-Semigroup → type-Inverse-Semigroup
  inv-Inverse-Semigroup x =
    element-partial-inverse-element-Semigroup
      ( semigroup-Inverse-Semigroup)
      ( partial-inverse-element-Inverse-Semigroup x)

  inner-partial-inverse-law-mul-Inverse-Semigroup :
    (x : type-Inverse-Semigroup) →
    inner-partial-inverse-law-Semigroup
      ( semigroup-Inverse-Semigroup)
      ( x)
      ( inv-Inverse-Semigroup x)
  inner-partial-inverse-law-mul-Inverse-Semigroup x =
    is-inner-partial-inverse-partial-inverse-element-Semigroup
      ( semigroup-Inverse-Semigroup)
      ( partial-inverse-element-Inverse-Semigroup x)

  outer-inverse-law-mul-Inverse-Semigroup :
    (x : type-Inverse-Semigroup) →
    outer-partial-inverse-law-Semigroup
      ( semigroup-Inverse-Semigroup)
      ( x)
      ( inv-Inverse-Semigroup x)
  outer-inverse-law-mul-Inverse-Semigroup x =
    is-outer-partial-inverse-partial-inverse-element-Semigroup
      ( semigroup-Inverse-Semigroup)
      ( partial-inverse-element-Inverse-Semigroup x)
```
