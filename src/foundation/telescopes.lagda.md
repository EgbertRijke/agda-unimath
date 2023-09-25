# Telescopes

```agda
{-# OPTIONS --guardedness #-}

module foundation.telescopes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
```

</details>

## Idea

A **telescope**, or **iterated type family**, is a list of type families
`(A₀, A₁, A₂, ..., A_n)` consisting of

- a type `A₀`,
- a type family `A₁ : A₀ → 𝒰`,
- a type family `A₂ : (x₀ : A₀) → A₁ x₀ → 𝒰`,
- ...
- a type family `A_n : (x₀ : A₀) ... (x_(n-1) : A_(n-1) x₀ ... x_(n-2)) → 𝒰`.

We say that a telescope `(A₀,...,A_n)` has **length** `n+1`. In other words, the
length of the telescope `(A₀,...,A_n)` is the length of the (dependent) list
`(A₀,...,A_n)`.

We encode the type of telescopes as a family of inductive types

```text
  telescope : (l : Level) → ℕ → UUω
```

The type of telescopes is a [directed tree](trees.directed-trees.md)

```text
  ... → T₃ → T₂ → T₁ → T₀,
```

where `T_n` is the type of all telescopes of length `n`, and the map from
`T_(n+1)` to `T_n` maps `(A₀,...,A_n)` to `(A₀,...,A_(n-1))`. The type of such
directed trees can be defined as a coinductive record type, and we will define
the tree `T` of telescopes as a particular element of this tree.

## Definitions

### Telescopes

```agda
data
  telescope : (l : Level) → ℕ → UUω
  where
  base-telescope :
    {l1 : Level} → UU l1 → telescope l1 0
  cons-telescope :
    {l1 l2 : Level} {n : ℕ} {X : UU l1} →
    (X → telescope l2 n) → telescope (l1 ⊔ l2) (succ-ℕ n)

open telescope public
```

### Inferring telescopes

```agda
instance
  infer-cons-telescope⁰ : {l : Level} {X : UU l} → telescope l 0
  infer-cons-telescope⁰ {X = X} = base-telescope X

  infer-cons-telescope¹ :
    {l1 lX : Level} {A : UU l1} {X : A → UU lX} → telescope (l1 ⊔ lX) 1
  infer-cons-telescope¹ {X = X} =
    cons-telescope (λ a → infer-cons-telescope⁰ {X = X a})

  infer-cons-telescope² :
    {l1 l2 lX : Level} {A : UU l1} {B : A → UU l2}
    {X : (a : A) → B a → UU lX} → telescope (l1 ⊔ l2 ⊔ lX) 2
  infer-cons-telescope² {X = X} =
    cons-telescope (λ a → infer-cons-telescope¹ {X = X a})

  infer-cons-telescope³ :
    {l1 l2 l3 lX : Level} {A : UU l1} {B : A → UU l2} {C : (a : A) → B a → UU l3}
    {X : (a : A) → (b : B a) → C a b → UU lX} → telescope (l1 ⊔ l2 ⊔ l3 ⊔ lX) 3
  infer-cons-telescope³ {X = X} =
    cons-telescope (λ a → infer-cons-telescope² {X = X a})

infer-cons-telescope : {l : Level} {n : ℕ} → {{telescope l n}} → telescope l n
infer-cons-telescope {{x}} = x
```
