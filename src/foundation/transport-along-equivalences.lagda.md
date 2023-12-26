# Transport along equivalences

```agda
module foundation.transport-along-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-functions
open import foundation.action-on-equivalences-type-families
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalence-induction
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

Applying
[transport along identifications](foundation-core.transport-along-identifications.md)
to [identifications](foundation-core.identity-types.md) arising from the
[univalence axiom](foundation.univalence.md) gives us
{{#concept "transport along equivalences"}}.

Since transport defines [equivalences](foundation-core.equivalences.md) of
[fibers](foundation-core.fibers-of-maps.md), this gives us an _action on
equivalences_. Alternatively, we could apply the
[action on identifications](foundation.action-on-identifications-functions.md)
to get another
[action on equivalences](foundation.action-on-equivalences-functions.md), but
luckily, these two notions coincide.

## Definitions

### Transporting along equivalences

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  where
  
  map-tr-equiv : X ≃ Y → f X → f Y
  map-tr-equiv e = tr f (eq-equiv X Y e)

  is-equiv-map-tr-equiv : (e : X ≃ Y) → is-equiv (map-tr-equiv e)
  is-equiv-map-tr-equiv e = is-equiv-tr f (eq-equiv X Y e)

  tr-equiv : X ≃ Y → f X ≃ f Y
  pr1 (tr-equiv e) = map-tr-equiv e
  pr2 (tr-equiv e) = is-equiv-map-tr-equiv e

  eq-tr-equiv : X ≃ Y → f X ＝ f Y
  eq-tr-equiv = eq-equiv (f X) (f Y) ∘ tr-equiv
```

## Properties

### Transporting along `id-equiv` is the identity equivalence

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2) {X : UU l1}
  where

  compute-map-tr-equiv-id-equiv : map-tr-equiv f id-equiv ＝ id
  compute-map-tr-equiv-id-equiv = ap (tr f) (compute-eq-equiv-id-equiv X)

  compute-tr-equiv-id-equiv : tr-equiv f id-equiv ＝ id-equiv
  compute-tr-equiv-id-equiv =
    ap (equiv-tr f) (compute-eq-equiv-id-equiv X) ∙ equiv-tr-refl f
```

### Transport along equivalences preserves composition of equivalences

For any operation `f : 𝒰₁ → 𝒰₂` and any two composable equivalences `e : X ≃ Y` and `e' : Y ≃ Z` in `𝒰₁` we obtain a commuting triangle

```text
                     tr-equiv f e
                 f X ----------> f Y
                     \         /
  tr-equiv f (e' ∘ e) \       / tr-equiv f e'
                       \     /
                        ∨   ∨ 
                         f Z

```

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y Z : UU l1} (e : X ≃ Y) (e' : Y ≃ Z)
  where
  
  distributive-map-tr-equiv-equiv-comp :
    coherence-triangle-maps
      ( map-tr-equiv f (e' ∘e e))
      ( map-tr-equiv f e')
      ( map-tr-equiv f e)
  distributive-map-tr-equiv-equiv-comp x =
    ( ap (λ p → tr f p x) (inv (compute-eq-equiv-comp-equiv X Y Z e e'))) ∙
    ( tr-concat (eq-equiv X Y e) (eq-equiv Y Z e') x)

  distributive-tr-equiv-equiv-comp :
    tr-equiv f (e' ∘e e) ＝ tr-equiv f e' ∘e tr-equiv f e
  distributive-tr-equiv-equiv-comp =
    eq-htpy-equiv distributive-map-tr-equiv-equiv-comp
```

### Transporting along an equivalence and its inverse is just the identity

```agda
module _
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y)
  where
  
  is-section-map-tr-equiv :
    is-section (map-tr-equiv f (inv-equiv e)) (map-tr-equiv f e)
  is-section-map-tr-equiv x =
    ( ap
      ( λ p → tr f p (map-tr-equiv f e x))
      ( inv (commutativity-inv-eq-equiv X Y e))) ∙
    ( is-retraction-inv-tr f (eq-equiv X Y e) x)

  is-retraction-map-tr-equiv :
    is-retraction (map-tr-equiv f (inv-equiv e)) (map-tr-equiv f e)
  is-retraction-map-tr-equiv x =
    ( ap
      ( map-tr-equiv f e ∘ (λ p → tr f p x))
      ( inv (commutativity-inv-eq-equiv X Y e))) ∙
    ( is-section-inv-tr f (eq-equiv X Y e) x)
```

### Transposing transport along the inverse of an equivalence

```agda
eq-transpose-map-tr-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) {u : f X} {v : f Y} →
  v ＝ map-tr-equiv f e u → map-tr-equiv f (inv-equiv e) v ＝ u
eq-transpose-map-tr-equiv f e {u} p =
  (ap (map-tr-equiv f (inv-equiv e)) p) ∙ (is-section-map-tr-equiv f e u)

eq-transpose-map-tr-equiv' :
  {l1 l2 : Level} (f : UU l1 → UU l2)
  {X Y : UU l1} (e : X ≃ Y) {u : f X} {v : f Y} →
  map-tr-equiv f e u ＝ v → u ＝ map-tr-equiv f (inv-equiv e) v
eq-transpose-map-tr-equiv' f e {u} p =
  (inv (is-section-map-tr-equiv f e u)) ∙ (ap (map-tr-equiv f (inv-equiv e)) p)
```

### Substitution law for transport along equivalences

```agda
substitution-map-tr-equiv :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) →
  map-tr-equiv g (action-equiv-family f e) ~ map-tr-equiv (g ∘ f) e
substitution-map-tr-equiv g f {X} {Y} e X' =
  ( ap (λ p → tr g p X') (is-retraction-eq-equiv (action-equiv-function f e))) ∙
  ( substitution-law-tr g f (eq-equiv X Y e))

substitution-law-tr-equiv :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → tr-equiv g (action-equiv-family f e) ＝ tr-equiv (g ∘ f) e
substitution-law-tr-equiv g f e =
  eq-htpy-equiv (substitution-map-tr-equiv g f e)
```

### Transporting along the action on equivalences of a function

```agda
compute-map-tr-equiv-action-equiv-family :
  {l1 l2 l3 l4 : Level} {B : UU l1 → UU l2} {D : UU l3 → UU l4}
  (f : UU l1 → UU l3) (g : (X : UU l1) → B X → D (f X))
  {X Y : UU l1} (e : X ≃ Y) (X' : B X) →
  map-tr-equiv D (action-equiv-family f e) (g X X') ＝ g Y (map-tr-equiv B e X')
compute-map-tr-equiv-action-equiv-family {D = D} f g {X} {Y} e X' =
  ( ap
    ( λ p → tr D p (g X X'))
    ( is-retraction-eq-equiv (action-equiv-function f e))) ∙
  ( tr-ap f g (eq-equiv X Y e) X')
```

### Transport along equivalences and the action on equivalences in the universe coincide

```agda
eq-tr-equiv-action-equiv-family :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  (e : X ≃ Y) → tr-equiv f e ＝ action-equiv-family f e
eq-tr-equiv-action-equiv-family f {X} =
  ind-equiv
    ( λ Y e → tr-equiv f e ＝ action-equiv-family f e)
    ( compute-tr-equiv-id-equiv f ∙
      inv (compute-action-equiv-family-id-equiv f))

eq-map-tr-equiv-map-action-equiv-family :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  (e : X ≃ Y) → map-tr-equiv f e ＝ map-action-equiv-family f e
eq-map-tr-equiv-map-action-equiv-family f e =
  ap map-equiv (eq-tr-equiv-action-equiv-family f e)
```
