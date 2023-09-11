# Action on equivalences of type families

```agda
module foundation.action-on-equivalences-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.equivalence-induction
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.subuniverses
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Ideas

Given a [subuniverse](foundation.subuniverses.md) `P`, any family of types `B`
indexed by types of `P` has an **action on equivalences**

```text
  (A ≃ B) → P A ≃ P B
```

obtained by [equivalence induction](foundation.equivalence-induction.md). The
acion on equivalences of a type family `B` on a subuniverse `P` of `𝒰` is such
that `B id-equiv ＝ id-equiv`, and fits in a
[commuting square](foundation.commuting-squares-of-maps.md)

```text
                   ap B
        (X ＝ Y) --------> (B X ＝ B Y)
           |                    |
  equiv-eq |                    | equiv-eq
           V                    V
        (X ≃ Y) ---------> (B X ≃ B Y).
                     B
```

## Definitions

### The action on equivalences of a family of types over a universe

```agda
module _
  {l1 l2 : Level} (B : UU l1 → UU l2)
  where

  unique-action-on-equivalences-family-of-types-universe :
    {X : UU l1} →
    is-contr (fiber (ev-id-equiv (λ Y e → B X ≃ B Y)) id-equiv)
  unique-action-on-equivalences-family-of-types-universe =
    is-contr-map-ev-id-equiv (λ Y e → B _ ≃ B Y) id-equiv

  action-on-equivalences-family-of-types-universe :
    {X Y : UU l1} → (X ≃ Y) → B X ≃ B Y
  action-on-equivalences-family-of-types-universe {X} {Y} =
    pr1 (center (unique-action-on-equivalences-family-of-types-universe {X})) Y

  compute-id-equiv-action-on-equivalences-family-of-types-universe :
    {X : UU l1} →
    action-on-equivalences-family-of-types-universe {X} {X} id-equiv ＝ id-equiv
  compute-id-equiv-action-on-equivalences-family-of-types-universe {X} =
    pr2 (center (unique-action-on-equivalences-family-of-types-universe {X}))

action-equiv-family :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X ≃ f Y
action-equiv-family f = equiv-eq ∘ action-equiv-function f

map-action-equiv-family :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X → f Y
map-action-equiv-family f = map-equiv ∘ action-equiv-family f
```

## Properties

### The action on equivalences of a family of types over a universe fits in a commuting square with `equiv-eq`

We claim that the square

```text
                   ap B
        (X ＝ Y) --------> (B X ＝ B Y)
           |                    |
  equiv-eq |                    | equiv-eq
           V                    V
        (X ≃ Y) ---------> (B X ≃ B Y).
                     B
```

commutes for any two types `X Y : 𝒰` and any type family `B` over `𝒰`.

```agda
coherence-square-action-on-equivalences-family-of-types-universe :
  {l1 l2 : Level} (B : UU l1 → UU l2) (X Y : UU l1) →
  coherence-square-maps
    ( ap B {X} {Y})
    ( equiv-eq)
    ( equiv-eq)
    ( action-on-equivalences-family-of-types-universe B)
coherence-square-action-on-equivalences-family-of-types-universe B X .X refl =
  compute-id-equiv-action-on-equivalences-family-of-types-universe B
```

### The identity function acts trivially on equivalences

```agda
compute-action-equiv-family-id :
  {l : Level} {X Y : UU l} (e : X ≃ Y) → (action-equiv-family id e) ＝ e
compute-action-equiv-family-id {l} {X} {Y} e =
  (ap equiv-eq (ap-id (eq-equiv X Y e))) ∙ (is-section-eq-equiv e)
```

### The action on equivalences of a composite function is the composite of the actions

```agda
distributive-action-equiv-function-comp :
  {l1 l2 l3 : Level} {C : UU l3} (g : UU l2 → C) (f : UU l1 → UU l2)
  {X Y : UU l1} →
  action-equiv-function (g ∘ f) ~
  action-equiv-function g ∘ action-equiv-family f
distributive-action-equiv-function-comp g f {X} {Y} e =
  ( ap-comp g f (eq-equiv X Y e)) ∙
  ( ap (ap g) (inv (is-retraction-eq-equiv (action-equiv-function f e))))

distributive-action-equiv-family-comp :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2)
  {X Y : UU l1} →
  action-equiv-family (g ∘ f) ~
  action-equiv-family g ∘ action-equiv-family f
distributive-action-equiv-family-comp g f {X} {Y} e =
  ap equiv-eq (distributive-action-equiv-function-comp g f {X} {Y} e)
```

### The action on equivalences of any map preserves `id-equiv`

```agda
compute-action-equiv-family-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) (A : UU l1) →
  (action-equiv-family f id-equiv) ＝ id-equiv
compute-action-equiv-family-id-equiv f A =
  ap equiv-eq (compute-action-equiv-function-id-equiv f A)
```

### The action on equivalences of a constant map is constant

```agda
compute-action-equiv-family-const :
  {l1 l2 : Level} (B : UU l2) {X Y : UU l1}
  (e : X ≃ Y) → (action-equiv-family (const (UU l1) (UU l2) B) e) ＝ id-equiv
compute-action-equiv-family-const B {X} {Y} e =
  ap equiv-eq (compute-action-equiv-function-const B e)
```

### The action on equivalences of any map preserves composition of equivalences

```agda
distributive-action-equiv-family-comp-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y Z : UU l1} →
  (e : X ≃ Y) (e' : Y ≃ Z) →
  action-equiv-family f (e' ∘e e) ＝
  action-equiv-family f e' ∘e action-equiv-family f e
distributive-action-equiv-family-comp-equiv f e e' =
  ( ap equiv-eq (distributive-action-equiv-function-comp-equiv f e e')) ∙
  ( inv
    ( compute-equiv-eq-concat
      ( action-equiv-function f e)
      ( action-equiv-function f e')))
```

### The action on equivalences of any map preserves inverses

```agda
compute-action-equiv-family-inv-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) →
  action-equiv-family f (inv-equiv e) ＝ inv-equiv (action-equiv-family f e)
compute-action-equiv-family-inv-equiv f {X} {Y} e =
  ( ap equiv-eq (compute-action-equiv-function-inv-equiv f e)) ∙
  ( inv (commutativity-inv-equiv-eq (f X) (f Y) (action-equiv-function f e)))
```