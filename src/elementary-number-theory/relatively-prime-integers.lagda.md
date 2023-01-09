---
title: Relatively prime integers
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module elementary-number-theory.relatively-prime-integers where

open import elementary-number-theory.absolute-value-integers
open import elementary-number-theory.divisibility-integers
open import elementary-number-theory.greatest-common-divisor-integers
open import elementary-number-theory.integers
open import elementary-number-theory.relatively-prime-natural-numbers

open import foundation.coproduct-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels
```

## Idea

Two integers are said to be relatively prime if their greatest common divisor is 1.

## Definition

```agda
relative-prime-ℤ : ℤ → ℤ → UU lzero
relative-prime-ℤ x y = is-one-ℤ (gcd-ℤ x y)
```

## Properties

### Two integers are relatively prime if and only if their absolute values are relatively prime natural numbers

```agda
relatively-prime-abs-relatively-prime-ℤ :
  {a b : ℤ} → relative-prime-ℤ a b → relatively-prime-ℕ (abs-ℤ a) (abs-ℤ b)
relatively-prime-abs-relatively-prime-ℤ {a} {b} H = is-injective-int-ℕ H

relatively-prime-relatively-prime-abs-ℤ :
  {a b : ℤ} → relatively-prime-ℕ (abs-ℤ a) (abs-ℤ b) → relative-prime-ℤ a b
relatively-prime-relatively-prime-abs-ℤ {a} {b} H = ap int-ℕ H
```

### For any two integers `a` and `b` that are not both `0`, the integers `a/gcd(a,b)` and `b/gcd(a,b)` are relatively prime

```agda
relatively-prime-quotient-div-ℤ :
  {a b : ℤ} → (is-nonzero-ℤ a + is-nonzero-ℤ b) →
  relative-prime-ℤ
    ( quotient-div-ℤ (gcd-ℤ a b) a (div-left-gcd-ℤ a b))
    ( quotient-div-ℤ (gcd-ℤ a b) b (div-right-gcd-ℤ a b))
relatively-prime-quotient-div-ℤ H =
  relatively-prime-relatively-prime-abs-ℤ
    {!!}
```

```agda
is-prop-is-relative-prime-ℤ : (x y : ℤ) → is-prop (relative-prime-ℤ x y)
is-prop-is-relative-prime-ℤ x y = is-set-ℤ (gcd-ℤ x y) one-ℤ
```
