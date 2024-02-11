# Infinitely coherent equivalences

```agda
{-# OPTIONS --guardedness --lossy-unification #-}

module foundation.infinitely-coherent-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "infinitely coherent equivalence"}} `e : A ≃ᶜ B` from `A` to `B`
consists of maps

```text
  f : A → B
  g : B → A
```

and for each `x : A` and `y : B` a infinitely coherent equivalence

```text
  transpose-eq : (f x ＝ y) ≃ᶜ (g y ＝ x).
```

Since this definition is infinite, it follows that for any `x : A` and `y : B`
we have maps

```text
  f' : (f x ＝ y) → (g y ＝ x)
  g' : (g y ＝ x) → (f x ＝ y)
```

and for each `p : f x ＝ y` and `q : g y ＝ x` a infinitely coherent equivalence

```text
  transpose-eq : (f' p ＝ q) ≃ᶜ (g' q ＝ p).
```

In particular, we have identifications

```text
  f' x (f x) refl : g (f x) ＝ x
  g' y (g y) refl : f (g y) ＝ y,
```

which are the usual homotopies witnessing that `g` is a retraction and a section
of `f`. By infinitely imposing the structure of a coherent equivalence, we have
stated an infinite hierarchy of coherence conditions. In other words, the
infinite condition on infinitely coherent equivalences is a way of stating
infinite coherence for equivalences.

## Definitions

### The predicate of being a infinitely coherent equivalence

```agda
record is-∞-equiv
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    map-inv-is-∞-equiv : B → A
    map-transpose-is-∞-equiv :
      (x : A) (y : B) →
      (f x ＝ y) → (x ＝ map-inv-is-∞-equiv y)
    is-∞-equiv-map-transpose-is-∞-equiv :
      (x : A) (y : B) →
      is-∞-equiv
        ( map-transpose-is-∞-equiv x y)

open is-∞-equiv public
```

### Infinitely coherent equivalences

```agda
record
  ∞-equiv
    {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    map-∞-equiv : A → B
    map-inv-∞-equiv : B → A
    ∞-equiv-transpose-∞-equiv :
      (x : A) (y : B) → ∞-equiv (map-∞-equiv x ＝ y) (map-inv-∞-equiv y ＝ x)

open ∞-equiv public

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  infix 6 _≃ᶜᵒʰ_

  _≃ᶜᵒʰ_ : UU (l1 ⊔ l2)
  _≃ᶜᵒʰ_ = ∞-equiv A B
```

### Composition of infinitely coherent equivalences

```agda
is-∞-equiv-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  (G : is-∞-equiv g)
  (F : is-∞-equiv f) →
  is-∞-equiv (g ∘ f)
map-inv-is-∞-equiv (is-∞-equiv-comp G F) =
  map-inv-is-∞-equiv F ∘ map-inv-is-∞-equiv G
map-transpose-is-∞-equiv (is-∞-equiv-comp G F) x z p =
  map-transpose-is-∞-equiv F x _ (map-transpose-is-∞-equiv G _ z p)
is-∞-equiv-map-transpose-is-∞-equiv (is-∞-equiv-comp G F) x z =
  is-∞-equiv-comp
    ( is-∞-equiv-map-transpose-is-∞-equiv F x _)
    ( is-∞-equiv-map-transpose-is-∞-equiv G _ z)
```

### Infinitely coherent equivalences obtained from equivalences

```agda
is-∞-equiv-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-∞-equiv f
map-inv-is-∞-equiv (is-∞-equiv-is-equiv H) =
  map-inv-is-equiv H
map-transpose-is-∞-equiv (is-∞-equiv-is-equiv H) x y =
  map-eq-transpose-equiv (_ , H)
is-∞-equiv-map-transpose-is-∞-equiv (is-∞-equiv-is-equiv H) x y =
  is-∞-equiv-is-equiv (is-equiv-map-equiv (eq-transpose-equiv (_ , H) x y))
```

### Being a infinitely coherent equivalence implies being an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-is-∞-equiv : is-∞-equiv f → is-equiv f
  is-equiv-is-∞-equiv H =
    is-equiv-is-invertible
      ( map-inv-is-∞-equiv H)
      ( λ y →
        map-inv-is-∞-equiv (is-∞-equiv-map-transpose-is-∞-equiv H _ y) refl)
      ( λ x → inv (map-transpose-is-∞-equiv H x (f x) refl))
```

### Any map-∞-equiv homotopic to an infinitely coherent equivalence is an infinitely coherent equivalence

```agda
is-∞-equiv-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  f ~ g →
  is-∞-equiv f → is-∞-equiv g
map-inv-is-∞-equiv (is-∞-equiv-htpy H K) =
  map-inv-is-∞-equiv K
map-transpose-is-∞-equiv (is-∞-equiv-htpy H K) x y =
  map-transpose-is-∞-equiv K x y ∘ concat (H x) _
is-∞-equiv-map-transpose-is-∞-equiv (is-∞-equiv-htpy H K) x y =
  is-∞-equiv-comp
    ( is-∞-equiv-map-transpose-is-∞-equiv K x y)
    ( is-∞-equiv-is-equiv (is-equiv-concat (H x) _))
```

### Homotopies of elements of type `is-∞-equiv f`

Consider a map-∞-equiv `f : A → B` and consider two elements

```text
  H K : is-∞-equiv f.
```

A {{#concept "homotopy of elments of type `is-∞-equiv`" Agda=htpy-is-∞-equiv}}
from `H := (h , s , H')` to `K := (k , t , K')` consists of a homotopy

```text
  α₀ : h ~ k,
```

for each `x : A` and `y : B` a homotopy `α₁` witnessing that the triangle

```text
               (f x = y)
              /         \
       s x y /           \ t x y
            /             \
           ∨               ∨
  (x = h y) --------------> (x = k y)
             p ↦ p ∙ α₀ y
```

commutes, and finally a homotopy of elements of type

```text
  is-infintitely-coherent-equivalence
    ( is-∞-equiv-htpy α₁
      ( is-∞-equiv-comp
        ( is-∞-equiv-is-equiv
          ( is-equiv-concat' _ (α₀ y)))
        ( H' x y))
    ( K' x y).
```

In other words, there are by the previous data two witnesses of the fact that
`t x y` is an infinintely coherent equivalence. The second (easiest) element is
the given element `K' x y`. The first element is from the homotopy witnessing
that the above triangle commutes. On the left we compose two infinitely coherent
equivalences, which results in an infinitely coherent equivalence, and the
element witnessing that the composite is an infinitely coherent equivalence
transports along the homotopy to a new element witnessing that `t x y` is an
infinitely coherent equivalence.

```agda
record
  htpy-is-∞-equiv
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (H K : is-∞-equiv f) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    htpy-map-inv-htpy-is-∞-equiv :
      map-inv-is-∞-equiv H ~ map-inv-is-∞-equiv K
    htpy-map-transpose-htpy-is-∞-equiv :
      (x : A) (y : B) →
      coherence-triangle-maps
        ( map-transpose-is-∞-equiv K x y)
        ( concat' _ (htpy-map-inv-htpy-is-∞-equiv y))
        ( map-transpose-is-∞-equiv H x y)
    infinitely-htpy-htpy-is-∞-equiv :
      (x : A) (y : B) →
      htpy-is-∞-equiv
        ( map-transpose-is-∞-equiv K x y)
        ( is-∞-equiv-htpy
          ( inv-htpy (htpy-map-transpose-htpy-is-∞-equiv x y))
          ( is-∞-equiv-comp
            ( is-∞-equiv-is-equiv (is-equiv-concat' _ _))
            ( is-∞-equiv-map-transpose-is-∞-equiv H x y)))
        ( is-∞-equiv-map-transpose-is-∞-equiv K x y)
```

## Operations

```agda
inv-∞-equiv :
  {l1 : Level} {A B : UU l1} → A ≃ᶜᵒʰ B → B ≃ᶜᵒʰ A
map-∞-equiv (inv-∞-equiv e) =
  map-inv-∞-equiv e
map-inv-∞-equiv (inv-∞-equiv e) =
  map-∞-equiv e
∞-equiv-transpose-∞-equiv (inv-∞-equiv e) y x =
  inv-∞-equiv (∞-equiv-transpose-∞-equiv e x y)
```

## Properties

### Computing the type `is-∞-equiv f`

```agda
type-compute-is-∞-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) → UU (l1 ⊔ l2)
type-compute-is-∞-equiv {A = A} {B} f =
  Σ (B → A) (λ g → (x : A) (y : B) → Σ ((f x ＝ y) → (x ＝ g y)) is-∞-equiv)

map-compute-is-∞-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  type-compute-is-∞-equiv f → is-∞-equiv f
map-inv-is-∞-equiv (map-compute-is-∞-equiv f H) =
  pr1 H
map-transpose-is-∞-equiv (map-compute-is-∞-equiv f H) x y =
  pr1 (pr2 H x y)
is-∞-equiv-map-transpose-is-∞-equiv (map-compute-is-∞-equiv f H) x y =
  pr2 (pr2 H x y)

map-inv-compute-is-∞-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-∞-equiv f → type-compute-is-∞-equiv f
pr1 (map-inv-compute-is-∞-equiv f H) =
  map-inv-is-∞-equiv H
pr1 (pr2 (map-inv-compute-is-∞-equiv f H) x y) =
  map-transpose-is-∞-equiv H x y
pr2 (pr2 (map-inv-compute-is-∞-equiv f H) x y) =
  is-∞-equiv-map-transpose-is-∞-equiv H x y
```

### Being a infinitely coherent equivalence is a property

```text
is-prop-is-∞-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-∞-equiv f)
is-prop-is-∞-equiv = {!!}
```