# Symmetric binary relations

```agda
module foundation.symmetric-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-type-families
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.symmetric-operations
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.unordered-pairs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A **symmetric binary relation** on a type `A` is a type family `R` over the type
of [unordered pairs](foundation.unordered-pairs.md) of elements of `A`. Given a
symmetric binary relation `R` on `A` and an equivalence of unordered pairs
`p ＝ q`, we have `R p ≃ R q`. In particular, we have

```text
  R ({x,y}) ≃ R ({y,x})
```

for any two elements `x y : A`, where `{x,y}` is the _standard unordered pair_
consisting of `x` and `y`.

Note that a symmetric binary relation R on a type is just a
[symmetric operation](foundation.symmetric-operations.md) from `A` into a
universe `𝒰`.

## Definitions

### Symmetric binary relations

```agda
symmetric-binary-relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
symmetric-binary-relation l2 A = symmetric-operation A (UU l2)
```

### Action on symmetries of symmetric binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : symmetric-binary-relation l2 A)
  where

  abstract
    equiv-tr-symmetric-binary-relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R p ≃ R q
    equiv-tr-symmetric-binary-relation p =
      ind-Eq-unordered-pair p (λ q e → R p ≃ R q) id-equiv

    compute-refl-equiv-tr-symmetric-binary-relation :
      (p : unordered-pair A) →
      equiv-tr-symmetric-binary-relation p p (refl-Eq-unordered-pair p) ＝
      id-equiv
    compute-refl-equiv-tr-symmetric-binary-relation p =
      compute-refl-ind-Eq-unordered-pair p (λ q e → R p ≃ R q) id-equiv

    htpy-compute-refl-equiv-tr-symmetric-binary-relation :
      (p : unordered-pair A) →
      htpy-equiv
        ( equiv-tr-symmetric-binary-relation p p (refl-Eq-unordered-pair p))
        ( id-equiv)
    htpy-compute-refl-equiv-tr-symmetric-binary-relation p =
      htpy-eq-equiv (compute-refl-equiv-tr-symmetric-binary-relation p)

  abstract
    tr-symmetric-binary-relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R p → R q
    tr-symmetric-binary-relation p q e =
      map-equiv (equiv-tr-symmetric-binary-relation p q e)

    tr-inv-symmetric-binary-relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R q → R p
    tr-inv-symmetric-binary-relation p q e =
      map-inv-equiv (equiv-tr-symmetric-binary-relation p q e)

    is-section-tr-inv-symmetric-binary-relation :
      (p q : unordered-pair A) (e : Eq-unordered-pair p q) →
      tr-symmetric-binary-relation p q e ∘
      tr-inv-symmetric-binary-relation p q e ~
      id
    is-section-tr-inv-symmetric-binary-relation p q e =
      is-section-map-inv-equiv (equiv-tr-symmetric-binary-relation p q e)

    is-retraction-tr-inv-symmetric-binary-relation :
      (p q : unordered-pair A) (e : Eq-unordered-pair p q) →
      tr-inv-symmetric-binary-relation p q e ∘
      tr-symmetric-binary-relation p q e ~
      id
    is-retraction-tr-inv-symmetric-binary-relation p q e =
      is-retraction-map-inv-equiv (equiv-tr-symmetric-binary-relation p q e)

    compute-refl-tr-symmetric-binary-relation :
      (p : unordered-pair A) →
      tr-symmetric-binary-relation p p (refl-Eq-unordered-pair p) ＝ id
    compute-refl-tr-symmetric-binary-relation p =
      ap map-equiv (compute-refl-equiv-tr-symmetric-binary-relation p)

    htpy-compute-refl-tr-symmetric-binary-relation :
      (p : unordered-pair A) →
      tr-symmetric-binary-relation p p (refl-Eq-unordered-pair p) ~ id
    htpy-compute-refl-tr-symmetric-binary-relation p =
      htpy-eq (compute-refl-tr-symmetric-binary-relation p)
```

### The underlying binary relation of a symmetric binary relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : symmetric-binary-relation l2 A)
  where

  relation-symmetric-binary-relation : Relation l2 A
  relation-symmetric-binary-relation x y = R (standard-unordered-pair x y)

  equiv-symmetric-relation-symmetric-binary-relation :
    {x y : A} →
    relation-symmetric-binary-relation x y ≃
    relation-symmetric-binary-relation y x
  equiv-symmetric-relation-symmetric-binary-relation {x} {y} =
    equiv-tr-symmetric-binary-relation R
      ( standard-unordered-pair x y)
      ( standard-unordered-pair y x)
      ( swap-standard-unordered-pair x y)

  symmetric-relation-symmetric-binary-relation :
    {x y : A} →
    relation-symmetric-binary-relation x y →
    relation-symmetric-binary-relation y x
  symmetric-relation-symmetric-binary-relation =
    map-equiv equiv-symmetric-relation-symmetric-binary-relation
```

### The forgetful functor from binary relations to symmetric binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  symmetric-binary-relation-Relation : symmetric-binary-relation l2 A
  symmetric-binary-relation-Relation p =
    Σ ( type-unordered-pair p)
      ( λ i →
        R (element-unordered-pair p i) (other-element-unordered-pair p i))

  unit-symmetric-binary-relation-Relation :
    (x y : A) → R x y →
    relation-symmetric-binary-relation symmetric-binary-relation-Relation x y
  pr1 (unit-symmetric-binary-relation-Relation x y r) = zero-Fin 1
  pr2 (unit-symmetric-binary-relation-Relation x y r) =
    tr
      ( R x)
      ( inv (compute-other-element-standard-unordered-pair x y (zero-Fin 1)))
      ( r)
```

### Morphisms of symmetric binary relations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  hom-symmetric-binary-relation :
    symmetric-binary-relation l2 A → symmetric-binary-relation l3 A →
    UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3)
  hom-symmetric-binary-relation R S =
    (p : unordered-pair A) → R p → S p

  hom-relation-hom-symmetric-binary-relation :
    (R : symmetric-binary-relation l2 A) (S : symmetric-binary-relation l3 A) →
    hom-symmetric-binary-relation R S →
    hom-Relation
      ( relation-symmetric-binary-relation R)
      ( relation-symmetric-binary-relation S)
  hom-relation-hom-symmetric-binary-relation R S f x y =
    f (standard-unordered-pair x y)
```