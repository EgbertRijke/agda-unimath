---
title: The greatest common divisor of integers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.greatest-common-divisor-integers where

open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.greatest-common-divisor-natural-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.universe-levels
```

## Idea

The greatest common divisor of two integers `x` and `y` is a nonnegative integer `d` such that

```md
  (z : ℤ) → is-common-divisor-ℤ x y z ↔ div-ℤ d z
```

## Definition

### The predicate `is-gcd-ℤ`

```agda
is-common-divisor-ℤ : ℤ → ℤ → ℤ → UU lzero
is-common-divisor-ℤ x y d = (div-ℤ d x) × (div-ℤ d y)

is-gcd-ℤ : ℤ → ℤ → ℤ → UU lzero
is-gcd-ℤ x y d =
  is-nonnegative-ℤ d × ((k : ℤ) → is-common-divisor-ℤ x y k ↔ div-ℤ k d)
```

### The greatest common divisor of two integers

```agda
nat-gcd-ℤ : ℤ → ℤ → ℕ
nat-gcd-ℤ x y = gcd-ℕ (abs-ℤ x) (abs-ℤ y)

gcd-ℤ : ℤ → ℤ → ℤ
gcd-ℤ x y = int-ℕ (nat-gcd-ℤ x y)
```

## Properties

### A natural number `d` is a common divisor of two natural numbers `x` and `y` if and only if `int-ℕ d` is a common divisor of `int-ℕ x` and `ind-ℕ y`

```agda
is-common-divisor-int-is-common-divisor-ℕ :
  {x y d : ℕ} →
  is-common-divisor-ℕ x y d → is-common-divisor-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d)
is-common-divisor-int-is-common-divisor-ℕ =
  map-prod div-int-div-ℕ div-int-div-ℕ

is-common-divisor-is-common-divisor-int-ℕ :
  {x y d : ℕ} →
  is-common-divisor-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d) → is-common-divisor-ℕ x y d
is-common-divisor-is-common-divisor-int-ℕ {x} {y} {d} =
  map-prod div-div-int-ℕ div-div-int-ℕ
```

### If `ux ＝ x'` and `vy ＝ y'` for two units `u` and `v`, then `d` is a common divisor of `x` and `y` if and only if `d` is a common divisor of `x'` and `y'`

```agda
is-common-divisor-sim-unit-ℤ :
  {x x' y y' d d' : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' → sim-unit-ℤ d d' →
  is-common-divisor-ℤ x y d → is-common-divisor-ℤ x' y' d'
is-common-divisor-sim-unit-ℤ H K L =
  map-prod (div-sim-unit-ℤ L H) (div-sim-unit-ℤ L K)
```

### If `ux ＝ x'` and `vy ＝ y'` for two units `u` and `v`, then `d` is a greatest common divisor of `x` and `y` if and only if `c` is a greatest common divisor of `x'` and `y'`

```agda
is-gcd-sim-unit-ℤ :
  {x x' y y' d : ℤ} → sim-unit-ℤ x x' → sim-unit-ℤ y y' →
  is-gcd-ℤ x y d → is-gcd-ℤ x' y' d
pr1 (is-gcd-sim-unit-ℤ H K (pair x _)) = x
pr1 (pr2 (is-gcd-sim-unit-ℤ H K (pair _ G)) k) =
  ( pr1 (G k)) ∘
  ( is-common-divisor-sim-unit-ℤ
    ( symm-sim-unit-ℤ H)
    ( symm-sim-unit-ℤ K)
    ( refl-sim-unit-ℤ k))
pr2 (pr2 (is-gcd-sim-unit-ℤ H K (pair _ G)) k) =
  ( is-common-divisor-sim-unit-ℤ H K (refl-sim-unit-ℤ k)) ∘
  ( pr2 (G k))
```

### An integer `d` is a common divisor of `x` and `y` if and only if `|d|` is a common divisor of `x` and `y`

```agda
is-common-divisor-int-abs-is-common-divisor-ℤ :
  {x y d : ℤ} →
  is-common-divisor-ℤ x y d → is-common-divisor-ℤ x y (int-abs-ℤ d)
is-common-divisor-int-abs-is-common-divisor-ℤ =
  map-prod div-int-abs-div-ℤ div-int-abs-div-ℤ

is-common-divisor-is-common-divisor-int-abs-ℤ :
  {x y d : ℤ} →
  is-common-divisor-ℤ x y (int-abs-ℤ d) → is-common-divisor-ℤ x y d
is-common-divisor-is-common-divisor-int-abs-ℤ =
  map-prod div-div-int-abs-ℤ div-div-int-abs-ℤ
```

### A natural number `d` is a greatest common divisor of two natural numbers `x` and `y` if and only if `int-ℕ d` is a greatest common divisor of `int-ℕ x` and `int-ℕ y`

```agda
is-gcd-int-is-gcd-ℕ :
  {x y d : ℕ} → is-gcd-ℕ x y d → is-gcd-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d)
pr1 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) = is-nonnegative-int-ℕ d
pr1 (pr2 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) k) =
  ( ( ( ( div-div-int-abs-ℤ) ∘
        ( div-int-div-ℕ)) ∘
      ( pr1 (H (abs-ℤ k)))) ∘
    ( is-common-divisor-is-common-divisor-int-ℕ)) ∘
  ( is-common-divisor-int-abs-is-common-divisor-ℤ)
pr2 (pr2 (is-gcd-int-is-gcd-ℕ {x} {y} {d} H) k) =
  ( ( ( ( is-common-divisor-is-common-divisor-int-abs-ℤ) ∘
        ( is-common-divisor-int-is-common-divisor-ℕ)) ∘
      ( pr2 (H (abs-ℤ k)))) ∘
    ( div-div-int-ℕ)) ∘
  ( div-int-abs-div-ℤ)

is-gcd-is-gcd-int-ℕ :
  {x y d : ℕ} → is-gcd-ℤ (int-ℕ x) (int-ℕ y) (int-ℕ d) → is-gcd-ℕ x y d
pr1 (is-gcd-is-gcd-int-ℕ {x} {y} {d} H k) =
  ( ( div-div-int-ℕ) ∘
    ( pr1 (pr2 H (int-ℕ k)))) ∘
  ( is-common-divisor-int-is-common-divisor-ℕ)
pr2 (is-gcd-is-gcd-int-ℕ {x} {y} {d} H k) =
  ( ( is-common-divisor-is-common-divisor-int-ℕ) ∘
    ( pr2 (pr2 H (int-ℕ k)))) ∘
  ( div-int-div-ℕ)
```

### `gcd-ℤ x y` is a greatest common divisor of `x` and `y`

```agda
is-nonnegative-gcd-ℤ : (x y : ℤ) → is-nonnegative-ℤ (gcd-ℤ x y)
is-nonnegative-gcd-ℤ x y = is-nonnegative-int-ℕ (nat-gcd-ℤ x y)

gcd-nonnegative-ℤ : ℤ → ℤ → nonnegative-ℤ
pr1 (gcd-nonnegative-ℤ x y) = gcd-ℤ x y
pr2 (gcd-nonnegative-ℤ x y) = is-nonnegative-gcd-ℤ x y

is-gcd-gcd-ℤ : (x y : ℤ) → is-gcd-ℤ x y (gcd-ℤ x y)
pr1 (is-gcd-gcd-ℤ x y) = is-nonnegative-gcd-ℤ x y
pr1 (pr2 (is-gcd-gcd-ℤ x y) k) =
  ( ( ( ( ( div-sim-unit-ℤ
            ( sim-unit-abs-ℤ k)
            ( refl-sim-unit-ℤ (gcd-ℤ x y))) ∘
          ( div-int-div-ℕ)) ∘
        ( pr1 (is-gcd-gcd-ℕ (abs-ℤ x) (abs-ℤ y) (abs-ℤ k)))) ∘
      ( is-common-divisor-is-common-divisor-int-ℕ)) ∘
    ( is-common-divisor-int-abs-is-common-divisor-ℤ)) ∘
  ( is-common-divisor-sim-unit-ℤ
    ( symm-sim-unit-ℤ (sim-unit-abs-ℤ x))
    ( symm-sim-unit-ℤ (sim-unit-abs-ℤ y))
    ( refl-sim-unit-ℤ k))
pr2 (pr2 (is-gcd-gcd-ℤ x y) k) =
  ( ( ( ( ( is-common-divisor-sim-unit-ℤ
            ( sim-unit-abs-ℤ x)
            ( sim-unit-abs-ℤ y)
            ( refl-sim-unit-ℤ k)) ∘
          ( is-common-divisor-is-common-divisor-int-abs-ℤ)) ∘
        ( is-common-divisor-int-is-common-divisor-ℕ)) ∘
      ( pr2 (is-gcd-gcd-ℕ (abs-ℤ x) (abs-ℤ y) (abs-ℤ k)))) ∘
    ( div-div-int-ℕ)) ∘
  ( div-sim-unit-ℤ
    ( symm-sim-unit-ℤ (sim-unit-abs-ℤ k))
    ( refl-sim-unit-ℤ (gcd-ℤ x y)))
```

### The gcd of `x` and `y` divides both `x` and `y`

```agda
is-common-divisor-gcd-ℤ :
  (x y : ℤ) → is-common-divisor-ℤ x y (gcd-ℤ x y)
is-common-divisor-gcd-ℤ x y =
  pr2 (pr2 (is-gcd-gcd-ℤ x y) (gcd-ℤ x y)) (refl-div-ℤ (gcd-ℤ x y))

div-left-gcd-ℤ : (x y : ℤ) → div-ℤ (gcd-ℤ x y) x
div-left-gcd-ℤ x y = pr1 (is-common-divisor-gcd-ℤ x y)

div-right-gcd-ℤ : (x y : ℤ) → div-ℤ (gcd-ℤ x y) y
div-right-gcd-ℤ x y = pr2 (is-common-divisor-gcd-ℤ x y)
```

### Any common divisor of `x` and `y` divides the greatest common divisor

```agda
div-gcd-is-common-divisor-ℤ :
  (x y k : ℤ) → is-common-divisor-ℤ x y k → div-ℤ k (gcd-ℤ x y)
div-gcd-is-common-divisor-ℤ x y k H =
  pr1 (pr2 (is-gcd-gcd-ℤ x y) k) H
```

### If either `x` or `y` is a positive integer, then `gcd-ℤ x y` is positive

```agda
is-positive-gcd-is-positive-left-ℤ :
  (x y : ℤ) → is-positive-ℤ x → is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-is-positive-left-ℤ x y H =
  is-positive-int-ℕ
    ( gcd-ℕ (abs-ℤ x) (abs-ℤ y))
    ( is-nonzero-gcd-ℕ
      ( abs-ℤ x)
      ( abs-ℤ y)
      ( λ p → is-nonzero-abs-ℤ x H (f p)))
  where
  f : is-zero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y)) → is-zero-ℕ (abs-ℤ x)
  f = is-zero-left-is-zero-add-ℕ (abs-ℤ x) (abs-ℤ y)

is-positive-gcd-is-positive-right-ℤ :
  (x y : ℤ) → is-positive-ℤ y → is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-is-positive-right-ℤ x y H =
  is-positive-int-ℕ
    ( gcd-ℕ (abs-ℤ x) (abs-ℤ y))
    ( is-nonzero-gcd-ℕ
      ( abs-ℤ x)
      ( abs-ℤ y)
      ( λ p → is-nonzero-abs-ℤ y H (f p)))
  where
  f : is-zero-ℕ (add-ℕ (abs-ℤ x) (abs-ℤ y)) → is-zero-ℕ (abs-ℤ y)
  f = is-zero-right-is-zero-add-ℕ (abs-ℤ x) (abs-ℤ y)

is-positive-gcd-ℤ :
  (x y : ℤ) → (is-positive-ℤ x) + (is-positive-ℤ y) →
  is-positive-ℤ (gcd-ℤ x y)
is-positive-gcd-ℤ x y (inl H) = is-positive-gcd-is-positive-left-ℤ x y H
is-positive-gcd-ℤ x y (inr H) = is-positive-gcd-is-positive-right-ℤ x y H
```

### `gcd-ℤ a b` is zero if and only if both `a` and `b` are zero

```agda
is-zero-gcd-ℤ :
  (a b : ℤ) → is-zero-ℤ a → is-zero-ℤ b → is-zero-ℤ (gcd-ℤ a b)
is-zero-gcd-ℤ zero-ℤ zero-ℤ refl refl =
  ap int-ℕ is-zero-gcd-zero-zero-ℕ

is-zero-left-is-zero-gcd-ℤ :
  (a b : ℤ) → is-zero-ℤ (gcd-ℤ a b) → is-zero-ℤ a
is-zero-left-is-zero-gcd-ℤ a b =
  is-zero-is-zero-div-ℤ a (gcd-ℤ a b) (div-left-gcd-ℤ a b)

is-zero-right-is-zero-gcd-ℤ :
  (a b : ℤ) → is-zero-ℤ (gcd-ℤ a b) → is-zero-ℤ b
is-zero-right-is-zero-gcd-ℤ a b =
  is-zero-is-zero-div-ℤ b (gcd-ℤ a b) (div-right-gcd-ℤ a b)
```

### If either `a` or `b` is nonzero, then `gcd-ℤ a b` is nonzero

```agda
is-nonzero-gcd-ℤ :
  (a b : ℤ) → (is-nonzero-ℤ a + is-nonzero-ℤ b) → is-nonzero-ℤ (gcd-ℤ a b)
is-nonzero-gcd-ℤ a b (inl H) p = H (is-zero-left-is-zero-gcd-ℤ a b p)
is-nonzero-gcd-ℤ a b (inr H) p = H (is-zero-right-is-zero-gcd-ℤ a b p)
```

### `gcd-ℤ` is commutative

```agda
is-commutative-gcd-ℤ : (x y : ℤ) → gcd-ℤ x y ＝ gcd-ℤ y x
is-commutative-gcd-ℤ x y =
  ap int-ℕ (is-commutative-gcd-ℕ (abs-ℤ x) (abs-ℤ y))
```
