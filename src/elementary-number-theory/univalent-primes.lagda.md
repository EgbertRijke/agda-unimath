# Univalent primes

```agda
module elementary-number-theory.univalent-primes where

open import elementary-number-theory.involutive-type-of-divisors
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.prime-numbers

open import foundation.contractible-types
open import foundation.universe-levels
```

## Idea

We say that a natural number is a **univalent prime** if the type of orbits of its involutive type of divisors is contractible. The univalence axiom implies that this condition is equivalent to being prime in the usual sense.

## Definition

```agda
is-univalent-prime-ℕ : ℕ → UU (lsuc lzero)
is-univalent-prime-ℕ n = is-contr (orbit-div-Involutive-Type n)
```

## Theorem

### If `n` is a univalent prime, then it is a prime

```agda
is-prime-is-univalent-prime : (n : ℕ) → is-univalent-prime-ℕ n → is-prime-ℕ n
is-prime-is-univalent-prime n H = {!!}
```

### If `n` is a prime, then it is a univalent prime
