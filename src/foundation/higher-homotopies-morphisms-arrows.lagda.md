# Higher homotopies of morphisms of arrows

```agda
module foundation.higher-homotopies-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-identifications
open import foundation.dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies-morphisms-arrows
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition
open import foundation.whiskering-homotopies-concatenation
open import foundation.whiskering-identifications-concatenation

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Consider two [morphisms of arrows](foundation.morphisms-arrows.md)
`α := (i , j , H)` and `α' := (i' , j' , H')` and two
[homotopies of morphisms of arrows](foundation.homotopies-morphisms-arrows.md)
`β := (I , J , K)` and `β' : (I' , J' , K')` between them. A
{{#concept "2-homotopy of morphisms of arrows" Agda=htpy-htpy-hom-arrow}} is a
triple `(γ₀, γ₁ , γ₂)` consisting of [homotopies](foundation-core.homotopies.md)

```text
  γ₀ : I ~ I'
  γ₁ : J ~ J'
```

and a homotopy witnessing that the square of homotopies

```text
                 left-whisker-concat-htpy H (g · γ₀)
  H ∙ (g ·l I) ---------------------------------------> H ∙ (g · I')
       |                                                     |
     K |                                                     | K'
       ∨                                                     ∨
  (J · f) ∙ H' ---------------------------------------> (J' · f) ∙ H'
                right-whisker-concat-htpy (γ₁ · f) H'
```

[commutes](foundation.commuting-squares-of-homotopies.md).

## Definitions

### Homotopies of homotopies of arrows

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α α' : hom-arrow f g)
  (β β' : htpy-hom-arrow f g α α')
  where

  coherence-htpy-htpy-hom-arrow :
    htpy-domain-htpy-hom-arrow f g α α' β ~
    htpy-domain-htpy-hom-arrow f g α α' β' →
    htpy-codomain-htpy-hom-arrow f g α α' β ~
    htpy-codomain-htpy-hom-arrow f g α α' β' → UU (l1 ⊔ l4)
  coherence-htpy-htpy-hom-arrow γ₀ γ₁ =
    coherence-square-homotopies
      ( left-whisker-concat-htpy
        ( coh-hom-arrow f g α)
        ( left-whisker-comp² g γ₀))
      ( coh-htpy-hom-arrow f g α α' β)
      ( coh-htpy-hom-arrow f g α α' β')
      ( right-whisker-concat-htpy
        ( right-whisker-comp² γ₁ f)
        ( coh-hom-arrow f g α'))

  htpy-htpy-hom-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-htpy-hom-arrow =
    Σ ( htpy-domain-htpy-hom-arrow f g α α' β ~
        htpy-domain-htpy-hom-arrow f g α α' β')
      ( λ γ₀ →
        Σ ( htpy-codomain-htpy-hom-arrow f g α α' β ~
            htpy-codomain-htpy-hom-arrow f g α α' β')
          ( coherence-htpy-htpy-hom-arrow γ₀))

  module _
    (γ : htpy-htpy-hom-arrow)
    where

    htpy-domain-htpy-htpy-hom-arrow :
      htpy-domain-htpy-hom-arrow f g α α' β ~
      htpy-domain-htpy-hom-arrow f g α α' β'
    htpy-domain-htpy-htpy-hom-arrow = pr1 γ

    htpy-codomain-htpy-htpy-hom-arrow :
      htpy-codomain-htpy-hom-arrow f g α α' β ~
      htpy-codomain-htpy-hom-arrow f g α α' β'
    htpy-codomain-htpy-htpy-hom-arrow = pr1 (pr2 γ)

    coh-htpy-htpy-hom-arrow :
      coherence-htpy-htpy-hom-arrow
        ( htpy-domain-htpy-htpy-hom-arrow)
        ( htpy-codomain-htpy-htpy-hom-arrow)
    coh-htpy-htpy-hom-arrow = pr2 (pr2 γ)
```

### The reflexivity homotopy of homotopies of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α α' : hom-arrow f g)
  (β : htpy-hom-arrow f g α α')
  where

  htpy-domain-refl-htpy-htpy-hom-arrow :
    htpy-domain-htpy-hom-arrow f g α α' β ~
    htpy-domain-htpy-hom-arrow f g α α' β
  htpy-domain-refl-htpy-htpy-hom-arrow = refl-htpy

  htpy-codomain-refl-htpy-htpy-hom-arrow :
    htpy-codomain-htpy-hom-arrow f g α α' β ~
    htpy-codomain-htpy-hom-arrow f g α α' β
  htpy-codomain-refl-htpy-htpy-hom-arrow = refl-htpy

  coh-refl-htpy-htpy-hom-arrow :
    coherence-htpy-htpy-hom-arrow f g α α' β β
      ( htpy-domain-refl-htpy-htpy-hom-arrow)
      ( htpy-codomain-refl-htpy-htpy-hom-arrow)
  coh-refl-htpy-htpy-hom-arrow = right-unit-htpy

  refl-htpy-htpy-hom-arrow : htpy-htpy-hom-arrow f g α α' β β
  pr1 refl-htpy-htpy-hom-arrow = htpy-domain-refl-htpy-htpy-hom-arrow
  pr1 (pr2 refl-htpy-htpy-hom-arrow) = htpy-codomain-refl-htpy-htpy-hom-arrow
  pr2 (pr2 refl-htpy-htpy-hom-arrow) = coh-refl-htpy-htpy-hom-arrow
```

## Properties

### Homotopies of homotopies of morphisms of arrows characterize equality of homotopies of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α α' : hom-arrow f g)
  (β : htpy-hom-arrow f g α α')
  where

  htpy-eq-htpy-hom-arrow :
    (β' : htpy-hom-arrow f g α α') → β ＝ β' → htpy-htpy-hom-arrow f g α α' β β'
  htpy-eq-htpy-hom-arrow .β refl = refl-htpy-htpy-hom-arrow f g α α' β

  is-torsorial-htpy-htpy-hom-arrow :
    is-torsorial (htpy-htpy-hom-arrow f g α α' β)
  is-torsorial-htpy-htpy-hom-arrow =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy _)
      ( htpy-domain-htpy-hom-arrow f g α α' β , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy _)
        ( htpy-codomain-htpy-hom-arrow f g α α' β , refl-htpy)
        ( is-torsorial-htpy _))

  is-equiv-htpy-eq-htpy-hom-arrow :
    (β' : htpy-hom-arrow f g α α') → is-equiv (htpy-eq-htpy-hom-arrow β')
  is-equiv-htpy-eq-htpy-hom-arrow =
    fundamental-theorem-id
      ( is-torsorial-htpy-htpy-hom-arrow)
      ( htpy-eq-htpy-hom-arrow)

  extensionality-htpy-hom-arrow :
    (β' : htpy-hom-arrow f g α α') →
    (β ＝ β') ≃ htpy-htpy-hom-arrow f g α α' β β'
  pr1 (extensionality-htpy-hom-arrow β') = htpy-eq-htpy-hom-arrow β'
  pr2 (extensionality-htpy-hom-arrow β') = is-equiv-htpy-eq-htpy-hom-arrow β'

  eq-htpy-htpy-hom-arrow :
    (β' : htpy-hom-arrow f g α α') →
    htpy-htpy-hom-arrow f g α α' β β' → β ＝ β'
  eq-htpy-htpy-hom-arrow β' = map-inv-equiv (extensionality-htpy-hom-arrow β')
```

### The left unit law for concatenation of homotopies of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α α' : hom-arrow f g)
  (β : htpy-hom-arrow f g α α')
  where

  htpy-domain-left-unit-law-concat-htpy-hom-arrow :
    htpy-domain-concat-htpy-hom-arrow f g α α α' (refl-htpy-hom-arrow f g α) β ~
    htpy-domain-htpy-hom-arrow f g α α' β
  htpy-domain-left-unit-law-concat-htpy-hom-arrow = refl-htpy

  htpy-codomain-left-unit-law-concat-htpy-hom-arrow :
    htpy-codomain-concat-htpy-hom-arrow f g α α α'
      ( refl-htpy-hom-arrow f g α)
      ( β) ~
    htpy-codomain-htpy-hom-arrow f g α α' β
  htpy-codomain-left-unit-law-concat-htpy-hom-arrow = refl-htpy

  coh-left-unit-law-concat-htpy-hom-arrow :
    coherence-htpy-htpy-hom-arrow f g α α'
      ( concat-htpy-hom-arrow f g α α α' (refl-htpy-hom-arrow f g α) β)
      ( β)
      ( htpy-domain-left-unit-law-concat-htpy-hom-arrow)
      ( htpy-codomain-left-unit-law-concat-htpy-hom-arrow)
  coh-left-unit-law-concat-htpy-hom-arrow a =
    ( right-unit) ∙
    ( right-whisker-concat
      ( right-whisker-concat-horizontal-refl-coherence-square-identifications
        ( coh-hom-arrow f g α a)
        ( ap g (htpy-domain-htpy-hom-arrow f g α α' β a)))
      ( coh-htpy-hom-arrow f g α α' β a))

  left-unit-law-concat-htpy-hom-arrow :
    htpy-htpy-hom-arrow f g α α'
      ( concat-htpy-hom-arrow f g α α α' (refl-htpy-hom-arrow f g α) β)
      ( β)
  pr1 left-unit-law-concat-htpy-hom-arrow =
    htpy-domain-left-unit-law-concat-htpy-hom-arrow
  pr1 (pr2 left-unit-law-concat-htpy-hom-arrow) =
    htpy-codomain-left-unit-law-concat-htpy-hom-arrow
  pr2 (pr2 left-unit-law-concat-htpy-hom-arrow) =
    coh-left-unit-law-concat-htpy-hom-arrow
```

### The right unit law for concatenation of morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (α α' : hom-arrow f g)
  (β : htpy-hom-arrow f g α α')
  where

  htpy-domain-right-unit-law-concat-htpy-hom-arrow :
    htpy-domain-concat-htpy-hom-arrow f g α α' α' β
      ( refl-htpy-hom-arrow f g α') ~
    htpy-domain-htpy-hom-arrow f g α α' β
  htpy-domain-right-unit-law-concat-htpy-hom-arrow = right-unit-htpy

  htpy-codomain-right-unit-law-concat-htpy-hom-arrow :
    htpy-codomain-concat-htpy-hom-arrow f g α α' α' β
      ( refl-htpy-hom-arrow f g α') ~
    htpy-codomain-htpy-hom-arrow f g α α' β
  htpy-codomain-right-unit-law-concat-htpy-hom-arrow = right-unit-htpy

  coh-right-unit-law-concat-htpy-hom-arrow :
    coherence-htpy-htpy-hom-arrow f g α α'
      ( concat-htpy-hom-arrow f g α α' α' β (refl-htpy-hom-arrow f g α'))
      ( β)
      ( htpy-domain-right-unit-law-concat-htpy-hom-arrow)
      ( htpy-codomain-right-unit-law-concat-htpy-hom-arrow)
  coh-right-unit-law-concat-htpy-hom-arrow a = {!!}

{-
Id
( ( left-whisker-concat (α₂ a) (ap-concat g (β₀ a) refl)) ∙
  ( ( ( ( inv (left-whisker-concat (α₂ a) (inv right-unit))) ∙
        ( ( β₂ a) ∙
          ( left-whisker-concat (β₁ (f a)) (inv right-unit)))) ∙
      ( ( inv (assoc (β₁ (f a)) (α'₂ a) refl)) ∙
        ( left-whisker-concat-coherence-square-identifications
          ( β₁ (f a))
          ( refl) -- top
          ( α'₂ a) -- left
          ( α'₂ a) -- right
          ( refl) -- bottom
          ( right-unit))))) ∙
    ( right-whisker-concat (α'₂ a) right-unit))

( ( left-whisker-concat (α₂ a) (ap (ap g) right-unit)) ∙
  ( β₂ a))
-}

{-
    coherence-square-homotopies
      ( left-whisker-concat-htpy
        ( coh-hom-arrow f g α)
        ( left-whisker-comp² g right-unit-htpy))
      ( coh-concat-htpy-hom-arrow f g α α' α' β (refl-htpy-hom-arrow f g α'))
      ( coh-htpy-hom-arrow f g α α' β)
      ( right-whisker-concat-htpy
        ( right-whisker-comp² right-unit-htpy f)
        ( coh-hom-arrow f g α'))
-}

  right-unit-law-concat-htpy-hom-arrow :
    htpy-htpy-hom-arrow f g α α'
      ( concat-htpy-hom-arrow f g α α' α' β (refl-htpy-hom-arrow f g α'))
      ( β)
  pr1 right-unit-law-concat-htpy-hom-arrow =
    htpy-domain-right-unit-law-concat-htpy-hom-arrow
  pr1 (pr2 right-unit-law-concat-htpy-hom-arrow) =
    htpy-codomain-right-unit-law-concat-htpy-hom-arrow
  pr2 (pr2 right-unit-law-concat-htpy-hom-arrow) =
    coh-right-unit-law-concat-htpy-hom-arrow
```