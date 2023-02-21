# The involutive type of divisors of a natural number

```agda
module elementary-number-theory.involutive-type-of-divisors where

open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.weak-function-extensionality

open import structured-types.involutive-types

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

## Idea

There is a natural `ℤ/2`-action on the set of divisors of a natural number `n`, which takes a divisor `d` to its opposite `n/d`.

## Definition

```agda
div-Involutive-Type : (n : ℕ) → Involutive-Type (lsuc lzero)
div-Involutive-Type n X =
  Σ ( type-2-Element-Type X → 𝔽 lzero)
    ( λ Y → Fin n ≃ ((x : type-2-Element-Type X) → type-𝔽 (Y x)))

orbit-div-Involutive-Type : (n : ℕ) → UU (lsuc lzero)
orbit-div-Involutive-Type n = orbit-Involutive-Type (div-Involutive-Type n)
```

## Properties

### Characterization of equility of the involutive type of divisors

```agda
module _
  (n : ℕ) (X : 2-Element-Type lzero)
  where
  
  equiv-div-Involutive-Type :
    (d d' : div-Involutive-Type n X) → UU lzero
  equiv-div-Involutive-Type d d' =
    Σ ( (x : type-2-Element-Type X) → equiv-𝔽 (pr1 d x) (pr1 d' x))
      ( λ e → htpy-equiv (equiv-map-Π e ∘e pr2 d) (pr2 d'))

  id-equiv-div-Involutive-Type :
    (d : div-Involutive-Type n X) → equiv-div-Involutive-Type d d
  pr1 (id-equiv-div-Involutive-Type d) x = id-equiv
  pr2 (id-equiv-div-Involutive-Type d) = refl-htpy

  equiv-eq-div-Involutive-Type :
    (d d' : div-Involutive-Type n X) →
    d ＝ d' → equiv-div-Involutive-Type d d'
  equiv-eq-div-Involutive-Type d .d refl = id-equiv-div-Involutive-Type d

  is-contr-total-equiv-div-Involutive-Type :
    (d : div-Involutive-Type n X) →
    is-contr (Σ (div-Involutive-Type n X) (equiv-div-Involutive-Type d))
  is-contr-total-equiv-div-Involutive-Type (Y , α) =
    is-contr-total-Eq-structure
      ( λ Y' α' e → htpy-equiv (equiv-map-Π e ∘e α) α')
      ( is-contr-total-Eq-Π
        ( λ x Y' → equiv-𝔽 (Y x) Y')
        ( λ x → is-contr-total-equiv-𝔽 (Y x)))
      ( Y , (λ x → id-equiv))
      ( is-contr-total-htpy-equiv α)

  is-equiv-equiv-eq-div-Involutive-Type :
    (d d' : div-Involutive-Type n X) →
    is-equiv (equiv-eq-div-Involutive-Type d d')
  is-equiv-equiv-eq-div-Involutive-Type d =
    fundamental-theorem-id
      ( is-contr-total-equiv-div-Involutive-Type d)
      ( equiv-eq-div-Involutive-Type d)

  extensionality-div-Involutive-Type :
    (d d' : div-Involutive-Type n X) →
    (d ＝ d') ≃ equiv-div-Involutive-Type d d'
  pr1 (extensionality-div-Involutive-Type d d') =
    equiv-eq-div-Involutive-Type d d'
  pr2 (extensionality-div-Involutive-Type d d') =
    is-equiv-equiv-eq-div-Involutive-Type d d'

  eq-equiv-div-Involutive-Type :
    (d d' : div-Involutive-Type n X) →
    equiv-div-Involutive-Type d d' → d ＝ d'
  eq-equiv-div-Involutive-Type d d' =
    map-inv-equiv (extensionality-div-Involutive-Type d d')
```

### The involutive type of divisors of `1` is contractible

```agda
center-div-one-Involutive-Type :
  (X : 2-Element-Type lzero) → div-Involutive-Type 1 X
pr1 (center-div-one-Involutive-Type X) x = Fin-𝔽 1
pr2 (center-div-one-Involutive-Type X) =
  equiv-is-contr
    ( is-contr-Fin-one-ℕ)
    ( is-contr-Π (λ x → is-contr-Fin-one-ℕ))

equiv-contraction-div-one-Involutive-Type :
  (X : 2-Element-Type lzero) (d : div-Involutive-Type 1 X) →
  equiv-div-Involutive-Type 1 X (center-div-one-Involutive-Type X) d
pr1 (equiv-contraction-div-one-Involutive-Type X d) x =
  equiv-is-contr
    ( is-contr-Fin-one-ℕ)
    ( converse-weak-funext
      ( has-decidable-equality-type-2-Element-Type X)
      ( is-contr-equiv'
        ( Fin 1)
        ( pr2 d)
        ( is-contr-Fin-one-ℕ))
      ( x))
pr2 (equiv-contraction-div-one-Involutive-Type X d) x =
  eq-is-contr (is-contr-equiv' (Fin 1) (pr2 d) (is-contr-Fin-one-ℕ))

is-contr-div-one-Involutive-Type :
  (X : 2-Element-Type lzero) → is-contr (div-Involutive-Type 1 X)
pr1 (is-contr-div-one-Involutive-Type X) = center-div-one-Involutive-Type X
pr2 (is-contr-div-one-Involutive-Type X) d =
  eq-equiv-div-Involutive-Type 1 X
    ( center-div-one-Involutive-Type X)
    ( d)
    ( equiv-contraction-div-one-Involutive-Type X d)
```
