# Pointed 2-homotopies

```agda
module structured-types.pointed-2-homotopies where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import structured-types.pointed-dependent-functions
open import structured-types.pointed-families-of-types
open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
open import structured-types.uniform-pointed-homotopies
```

</details>

## Idea

Consider two [pointed homotopies](structured-types.pointed-homotopies.md)
`H := (H₀ , H₁)` and `K := (K₀ , K₁)` between two
[pointed dependent functions](structured-types.pointed-dependent-functions.md)
`f := (f₀ , f₁)` and `g := (g₀ , g₁)` with base point coherences

```text
        H₀ *                        H₀ *
  f₀ * ------> g₀ *           f₀ * ------> g₀ *
      \       /                   \       ∧
    f₁ \  H₁ / g₁      and      f₁ \  H̃₁ / inv g₁
        \   /                       \   /
         ∨ ∨                         ∨ /
          *                           *
```

and

```text
        K₀ *                        K₀ *
  f₀ * ------> g₀ *           f₀ * ------> g₀ *
      \       /                   \       ∧
    f₁ \  K₁ / g₁      and      f₁ \  K̃₁ / inv g₁
        \   /                       \   /
         ∨ ∨                         ∨ /
          *                           *,
```

where

```text
  H̃₁ := coherence-triangle-inv-right f₁ g₁ (H₀ *) H₁
  K̃₁ := coherence-triangle-inv-right f₁ g₁ (K₀ *) K₁
```

A {{#concept "pointed 2-homotopy" Agda=_~²∗_}} `H ~²∗ K` then consists of an
unpointed [homotopy](foundation-core.homotopies.md) `α₀ : H₀ ~ K₀` and an
[identification](foundation-core.identity-types.md) witnessing that the triangle

```text
        H₁
  f₁ ------> (H₀ *) ∙ g₁
    \       /
  K₁ \     / right-whisker-concat (α₀ *) g₁
      \   /
       ∨ ∨
   (K₀ *) ∙ g₁
```

[commutes](foundation.commuting-triangles-of-identifications.md). Equivalently,
following the [equivalence](foundation-core.equivalences.md) of pointed
homotopies and
[uniform pointed homotopies](structured-types.uniform-pointed-homotopies.md), a
uniform pointed 2-homotopy consists of an unpointed homotopy `α₀ : H₀ ~ K₀` and
an identification witnessing that `α₀` preserves the base point, i.e.,
witnessing that the triangle

```text
        α₀ *
  H₀ * ------> K₀ *
      \       ∧
    H̃₁ \     / inv K̃₁
        \   /
         ∨ /
       f₁ ∙ inv g₁
```

commutes. Note that such identifications are often much harder to construct. Our
preferred definition of pointed 2-homotopies is therefore the non-uniform
definition described first.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H K : pointed-htpy f g)
  where

  unpointed-htpy-pointed-htpy : UU (l1 ⊔ l2)
  unpointed-htpy-pointed-htpy =
    htpy-pointed-htpy H ~ htpy-pointed-htpy K

  coherence-point-unpointed-htpy-pointed-htpy :
    unpointed-htpy-pointed-htpy → UU l2
  coherence-point-unpointed-htpy-pointed-htpy α =
    coherence-triangle-identifications
      ( coherence-point-pointed-htpy K)
      ( right-whisker-concat
        ( α (point-Pointed-Type A))
        ( preserves-point-function-pointed-Π g))
      ( coherence-point-pointed-htpy H)

  pointed-2-htpy : UU (l1 ⊔ l2)
  pointed-2-htpy =
    Σ unpointed-htpy-pointed-htpy coherence-point-unpointed-htpy-pointed-htpy

  infix 6 _~²∗_

  _~²∗_ : UU (l1 ⊔ l2)
  _~²∗_ = pointed-2-htpy

  module _
    (α : pointed-2-htpy)
    where

    htpy-pointed-2-htpy : unpointed-htpy-pointed-htpy
    htpy-pointed-2-htpy = pr1 α

    coherence-point-pointed-2-htpy :
      coherence-point-unpointed-htpy-pointed-htpy htpy-pointed-2-htpy
    coherence-point-pointed-2-htpy = pr2 α

    preserves-point-pointed-2-htpy :
      preserves-point-unpointed-htpy-pointed-Π
        ( make-uniform-pointed-htpy
          ( htpy-pointed-htpy H)
          ( coherence-point-pointed-htpy H))
        ( make-uniform-pointed-htpy
          ( htpy-pointed-htpy K)
          ( coherence-point-pointed-htpy K))
        ( htpy-pointed-2-htpy)
    preserves-point-pointed-2-htpy =
      transpose-right-coherence-triangle-identifications
        ( htpy-pointed-2-htpy (point-Pointed-Type A))
        ( preserves-point-pointed-htpy K)
        ( preserves-point-pointed-htpy H)
        ( refl)
        ( higher-transpose-right-coherence-triangle-identifications
          ( htpy-pointed-htpy H (point-Pointed-Type A))
          ( preserves-point-function-pointed-Π g)
          ( preserves-point-function-pointed-Π f)
          ( htpy-pointed-2-htpy (point-Pointed-Type A))
          ( refl)
          ( coherence-point-pointed-htpy H)
          ( coherence-point-pointed-htpy K)
          ( coherence-point-pointed-2-htpy))

    uniform-pointed-htpy-pointed-2-htpy :
      uniform-pointed-htpy
        ( uniform-pointed-htpy-pointed-htpy H)
        ( uniform-pointed-htpy-pointed-htpy K)
    pr1 uniform-pointed-htpy-pointed-2-htpy =
      htpy-pointed-2-htpy
    pr2 uniform-pointed-htpy-pointed-2-htpy =
      preserves-point-pointed-2-htpy
```

### The reflexive pointed 2-homotopy

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H : f ~∗ g)
  where

  htpy-refl-pointed-2-htpy : unpointed-htpy-pointed-htpy H H
  htpy-refl-pointed-2-htpy = refl-htpy

  coherence-point-refl-pointed-2-htpy :
    coherence-point-unpointed-htpy-pointed-htpy H H
      ( htpy-refl-pointed-2-htpy)
  coherence-point-refl-pointed-2-htpy = inv right-unit

  refl-pointed-2-htpy : H ~²∗ H
  pr1 refl-pointed-2-htpy = htpy-refl-pointed-2-htpy
  pr2 refl-pointed-2-htpy = coherence-point-refl-pointed-2-htpy
```

### Concatenation of pointed 2-homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} {H K L : f ~∗ g} (α : H ~²∗ K) (β : K ~²∗ L)
  where

  htpy-concat-pointed-2-htpy :
    unpointed-htpy-pointed-htpy H L
  htpy-concat-pointed-2-htpy =
    htpy-pointed-2-htpy H K α ∙h htpy-pointed-2-htpy K L β

  coherence-point-concat-pointed-2-htpy :
    coherence-point-unpointed-htpy-pointed-htpy H L htpy-concat-pointed-2-htpy
  coherence-point-concat-pointed-2-htpy =
    ( coherence-point-pointed-2-htpy K L β) ∙
    ( ( right-whisker-concat
        ( coherence-point-pointed-2-htpy H K α)
        ( right-whisker-concat
          ( htpy-pointed-2-htpy K L β (point-Pointed-Type A))
          ( preserves-point-function-pointed-Π g))) ∙
      ( ( assoc
          ( coherence-point-pointed-htpy H)
          ( _)
          ( _)) ∙
        ( inv
          ( left-whisker-concat
            ( coherence-point-pointed-htpy H)
            ( ap-concat
              ( _∙ pr2 g)
              ( htpy-pointed-2-htpy H K α _)
              ( htpy-pointed-2-htpy K L β _))))))

  concat-pointed-2-htpy : H ~²∗ L
  pr1 concat-pointed-2-htpy = htpy-concat-pointed-2-htpy
  pr2 concat-pointed-2-htpy = coherence-point-concat-pointed-2-htpy
```

### Inverses of pointed 2-homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} {H K : f ~∗ g} (α : H ~²∗ K)
  where

  htpy-inv-pointed-2-htpy :
    unpointed-htpy-pointed-htpy K H
  htpy-inv-pointed-2-htpy = inv-htpy (htpy-pointed-2-htpy _ _ α)

  coherence-point-inv-pointed-2-htpy :
    coherence-point-unpointed-htpy-pointed-htpy K H htpy-inv-pointed-2-htpy
  coherence-point-inv-pointed-2-htpy =
    transpose-right-coherence-triangle-identifications
      ( coherence-point-pointed-htpy H)
      ( right-whisker-concat (htpy-pointed-2-htpy H K α _) _)
      ( coherence-point-pointed-htpy K)
      ( inv (ap-inv _ (htpy-pointed-2-htpy H K α _)))
      ( coherence-point-pointed-2-htpy H K α)

  inv-pointed-2-htpy : K ~²∗ H
  pr1 inv-pointed-2-htpy = htpy-inv-pointed-2-htpy
  pr2 inv-pointed-2-htpy = coherence-point-inv-pointed-2-htpy
```

## Properties

### Extensionality of pointed homotopies

Pointed 2-homotopies characterize identifications of pointed homotopies.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H : f ~∗ g)
  where

  is-torsorial-pointed-2-htpy :
    is-torsorial (pointed-2-htpy H)
  is-torsorial-pointed-2-htpy =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy _)
      ( htpy-pointed-htpy H , refl-htpy)
      ( is-torsorial-Id' _)

  pointed-2-htpy-eq : (K : f ~∗ g) → H ＝ K → H ~²∗ K
  pointed-2-htpy-eq .H refl = refl-pointed-2-htpy H

  is-equiv-pointed-2-htpy-eq :
    (K : f ~∗ g) → is-equiv (pointed-2-htpy-eq K)
  is-equiv-pointed-2-htpy-eq =
    fundamental-theorem-id
      ( is-torsorial-pointed-2-htpy)
      ( pointed-2-htpy-eq)

  extensionality-pointed-htpy :
    (K : f ~∗ g) → (H ＝ K) ≃ (H ~²∗ K)
  pr1 (extensionality-pointed-htpy K) = pointed-2-htpy-eq K
  pr2 (extensionality-pointed-htpy K) = is-equiv-pointed-2-htpy-eq K

  eq-pointed-2-htpy :
    (K : f ~∗ g) → H ~²∗ K → H ＝ K
  eq-pointed-2-htpy K = map-inv-equiv (extensionality-pointed-htpy K)
```

### Associativity of concatenation of pointed homotopies

Associativity of concatenation of three pointed homotopies `G`, `H`, and `K` is
a pointed 2-homotopy

```text
  (G ∙h H) ∙h K ~²∗ G ∙h (H ∙h K).
```

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g h k : pointed-Π A B} (G : f ~∗ g) (H : g ~∗ h) (K : h ~∗ k)
  where

  htpy-associative-concat-pointed-htpy :
    htpy-pointed-htpy
      ( concat-pointed-htpy (concat-pointed-htpy G H) K) ~
    htpy-pointed-htpy
      ( concat-pointed-htpy G (concat-pointed-htpy H K))
  htpy-associative-concat-pointed-htpy =
    assoc-htpy
      ( htpy-pointed-htpy G)
      ( htpy-pointed-htpy H)
      ( htpy-pointed-htpy K)

  coherence-associative-concat-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy (concat-pointed-htpy G H) K)
      ( concat-pointed-htpy G (concat-pointed-htpy H K))
      ( htpy-associative-concat-pointed-htpy)
  coherence-associative-concat-pointed-htpy =
    associative-horizontal-pasting-coherence-triangle-identifications
      ( preserves-point-function-pointed-Π f)
      ( preserves-point-function-pointed-Π g)
      ( preserves-point-function-pointed-Π h)
      ( preserves-point-function-pointed-Π k)
      ( htpy-pointed-htpy G _)
      ( htpy-pointed-htpy H _)
      ( htpy-pointed-htpy K _)
      ( coherence-point-pointed-htpy G)
      ( coherence-point-pointed-htpy H)
      ( coherence-point-pointed-htpy K)

  associative-concat-pointed-htpy :
    concat-pointed-htpy (concat-pointed-htpy G H) K ~²∗
    concat-pointed-htpy G (concat-pointed-htpy H K)
  pr1 associative-concat-pointed-htpy =
    htpy-associative-concat-pointed-htpy
  pr2 associative-concat-pointed-htpy =
    coherence-associative-concat-pointed-htpy
```

### The left unit law of concatenation of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H : f ~∗ g)
  where

  htpy-left-unit-law-concat-pointed-htpy :
    unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy (refl-pointed-htpy f) H)
      ( H)
  htpy-left-unit-law-concat-pointed-htpy = refl-htpy

  coherence-point-left-unit-law-concat-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy (refl-pointed-htpy f) H)
      ( H)
      ( htpy-left-unit-law-concat-pointed-htpy)
  coherence-point-left-unit-law-concat-pointed-htpy =
    inv (right-unit ∙ right-unit ∙ ap-id (coherence-point-pointed-htpy H))

  left-unit-law-concat-pointed-htpy :
    concat-pointed-htpy (refl-pointed-htpy f) H ~²∗ H
  pr1 left-unit-law-concat-pointed-htpy =
    htpy-left-unit-law-concat-pointed-htpy
  pr2 left-unit-law-concat-pointed-htpy =
    coherence-point-left-unit-law-concat-pointed-htpy
```

### The right unit law of concatenation of pointed homotopies

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Fam l2 A}
  {f g : pointed-Π A B} (H : f ~∗ g)
  where

  htpy-right-unit-law-concat-pointed-htpy :
    unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy H (refl-pointed-htpy g))
      ( H)
  htpy-right-unit-law-concat-pointed-htpy = right-unit-htpy

  coherence-point-right-unit-law-concat-pointed-htpy :
    coherence-point-unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy H (refl-pointed-htpy g))
      ( H)
      ( htpy-right-unit-law-concat-pointed-htpy)
  coherence-point-right-unit-law-concat-pointed-htpy =
    ( inv right-unit) ∙
    ( ( left-whisker-concat
        ( coherence-point-pointed-htpy H)
        ( left-transpose-eq-concat
          ( assoc (htpy-pointed-htpy H _) refl _)
          ( refl)
          ( right-whisker-concat
            ( right-unit)
            ( preserves-point-function-pointed-Π g))
          ( ( right-unit) ∙
            ( middle-unit-law-assoc _ _)))) ∙
      ( inv
        ( assoc
          ( coherence-point-pointed-htpy H)
          ( inv (assoc (htpy-pointed-htpy H _) refl _))
          ( right-whisker-concat
            ( right-unit)
            ( preserves-point-function-pointed-Π g)))))

  right-unit-law-concat-pointed-htpy :
    concat-pointed-htpy H (refl-pointed-htpy g) ~²∗ H
  pr1 right-unit-law-concat-pointed-htpy =
    htpy-right-unit-law-concat-pointed-htpy
  pr2 right-unit-law-concat-pointed-htpy =
    coherence-point-right-unit-law-concat-pointed-htpy
```