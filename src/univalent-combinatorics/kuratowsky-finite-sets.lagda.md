# Kuratowsky finite sets

```agda
module univalent-combinatorics.kuratowsky-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A Kuratowsky finite type is a set `X` for which there exists a surjection into
`X` from a standard finite type. In other words, the Kuratowsky finite types are
the set-quotient of a standard finite type.

## Definition

```agda
is-kuratowsky-finite-set-Prop : {l : Level} → Set l → Prop l
is-kuratowsky-finite-set-Prop X =
  exists-structure-Prop ℕ (λ n → Fin n ↠ type-Set X)

is-kuratowsky-finite-set : {l : Level} → Set l → UU l
is-kuratowsky-finite-set X = type-Prop (is-kuratowsky-finite-set-Prop X)

𝔽-Kuratowsky : (l : Level) → UU (lsuc l)
𝔽-Kuratowsky l = Σ (Set l) is-kuratowsky-finite-set

module _
  {l : Level} (X : 𝔽-Kuratowsky l)
  where

  set-𝔽-Kuratowsky : Set l
  set-𝔽-Kuratowsky = pr1 X

  type-𝔽-Kuratowsky : UU l
  type-𝔽-Kuratowsky = type-Set set-𝔽-Kuratowsky

  is-set-type-𝔽-Kuratowsky : is-set type-𝔽-Kuratowsky
  is-set-type-𝔽-Kuratowsky = is-set-type-Set set-𝔽-Kuratowsky

  is-kuratowsky-finite-set-𝔽-Kuratowsky :
    is-kuratowsky-finite-set set-𝔽-Kuratowsky
  is-kuratowsky-finite-set-𝔽-Kuratowsky = pr2 X
```

## Properties

### A Kuratowsky finite set is finite if and only if it has decidable equality

```agda
is-finite-has-decidable-equality-type-𝔽-Kuratowsky :
  {l : Level} (X : 𝔽-Kuratowsky l) →
  has-decidable-equality (type-𝔽-Kuratowsky X) →
  is-finite (type-𝔽-Kuratowsky X)
is-finite-has-decidable-equality-type-𝔽-Kuratowsky X H =
  apply-universal-property-trunc-Prop
    ( is-kuratowsky-finite-set-𝔽-Kuratowsky X)
    ( is-finite-Prop (type-𝔽-Kuratowsky X))
    ( λ (n , f , s) → is-finite-codomain (is-finite-Fin n) s H)

has-decidable-equality-is-finite-type-𝔽-Kuratowsky :
  {l : Level} (X : 𝔽-Kuratowsky l) →
  is-finite (type-𝔽-Kuratowsky X) →
  has-decidable-equality (type-𝔽-Kuratowsky X)
has-decidable-equality-is-finite-type-𝔽-Kuratowsky X H =
  has-decidable-equality-is-finite H
```

### TODO: change title

```agda
is-kuratowsky-finite-set-surjection :
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) →
  type-Set X ↠ type-Set Y →
  is-kuratowsky-finite-set X →
  is-kuratowsky-finite-set Y
is-kuratowsky-finite-set-surjection X Y f =
  map-universal-property-trunc-Prop
    ( is-kuratowsky-finite-set-Prop Y)
    ( λ (n , g) → (intro-∃ n (surjection-comp f g)))

is-kuratowsky-finite-set-is-finite :
  {l : Level} (X : Set l) →
  is-finite (type-Set X) →
  is-kuratowsky-finite-set X
is-kuratowsky-finite-set-is-finite X =
  map-universal-property-trunc-Prop
    ( is-kuratowsky-finite-set-Prop X)
    ( λ (n , e) → intro-∃ n (map-equiv e , is-surjective-map-equiv e))
```

### Classical facts

```agda
is-finite-is-kuratowsky-finite-set :
  {l : Level} (X : Set l) →
  LEM l →
  is-kuratowsky-finite-set X → is-finite (type-Set X)
is-finite-is-kuratowsky-finite-set X lem is-fin =
  is-finite-has-decidable-equality-type-𝔽-Kuratowsky
    ( X , is-fin)
    ( λ x y → lem (Id-Prop X x y))
```
