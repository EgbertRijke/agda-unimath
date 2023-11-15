# The downwards closure of large subposets

```agda
module order-theory.downwards-closure-large-subposets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.existential-quantification
open import foundation.logical-equivalences
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.large-subposets
open import order-theory.large-subpreorders
open import order-theory.lower-sets-large-posets
```

</details>

## Idea

The **downwards closure** of a [large subposet](order-theory.large-subposets.md) `S` of a [large poset](order-theory.large-posets.md) `P` is the large subposet `↓S` consisting of all elements of `P` that are less than some element in `S` of the same universe level as `x`. In other words, the downwards closure `↓S` of `S` consists of all elements `x : type-Large-Poset l P` satisfying the property

```text
  ∃ (y : type-Large-Poset l P), (y ∈ S) ∧ (x ≤ y)
```

The requirement that `x` must be less than an element `y ∈ S` of the same universe level as `x` is included because there is no [existential quantification](foundation.existential-quantification.md) over the sort `Level` of [universe levels](foundation.universe-levels.md). In other words, downwards closures of large subposets are defined as _levelwise_ downwards closures.

Alternatively, the downwards closure of `S` can be characterized as the least [lower set](order-theory.lower-sets-large-posets.md) that contains `S`.

## Definitions

### The predicate of being the downwards closure of a large subposet

```agda
module _
  {α γ δ : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β) (S : Large-Subposet γ P)
  (T : lower-set-Large-Poset δ P)
  where

  is-downwards-closure-lower-set-Large-Poset : {!!}
  is-downwards-closure-lower-set-Large-Poset =
    (U : lower-set-Large-Poset δ P)
    {l : Level} →
    {!!} ↔
    ( (x : type-Large-Poset P l) →
      is-in-Large-Subposet P S x → is-in-lower-set-Large-Poset P U x)
```

### The downwards closure of a large subposet

```agda
module _
  {α γ : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β) (S : Large-Subposet γ P)
  where

  large-subpreorder-downwards-closure-Large-Subposet :
    Large-Subpreorder (λ z → α z ⊔ γ z ⊔ β z z) (large-preorder-Large-Poset P)
  large-subpreorder-downwards-closure-Large-Subposet {l} x =
    ∃-Prop
      ( type-Large-Poset P l)
      ( λ y → is-in-Large-Subposet P S y × leq-Large-Poset P x y)

  is-closed-under-sim-downwards-closure-Large-Subposet :
    is-closed-under-sim-Large-Subpreorder P
      large-subpreorder-downwards-closure-Large-Subposet
  is-closed-under-sim-downwards-closure-Large-Subposet {l1} {l2} x y s t p =
    {!!}

  large-subposet-downwards-closure-Large-Subposet :
    Large-Subposet (λ z → α z ⊔ γ z ⊔ β z z) P
  large-subpreorder-Large-Subposet
    large-subposet-downwards-closure-Large-Subposet =
    large-subpreorder-downwards-closure-Large-Subposet
  is-closed-under-sim-Large-Subposet
    large-subposet-downwards-closure-Large-Subposet = {!!}

  downwards-closure-Large-Subposet :
    lower-set-Large-Poset (λ z → α z ⊔ γ z ⊔ β z z) P
  large-subposet-lower-set-Large-Poset downwards-closure-Large-Subposet = {!!}
  is-lower-set-lower-set-Large-Poset downwards-closure-Large-Subposet = {!!}
```
