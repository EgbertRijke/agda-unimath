# Operations on cocones under span diagrams

```agda
module synthetic-homotopy-theory.operations-cocones-under-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.equivalences-span-diagrams
open import foundation.extensions-span-diagrams
open import foundation.function-extensionality
open import foundation.morphisms-arrows
open import foundation.morphisms-span-diagrams
open import foundation.span-diagrams
open import foundation.transposition-span-diagrams
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.commuting-squares-of-maps
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types

open import synthetic-homotopy-theory.cocones-under-span-diagrams
```

</details>

## Idea

There are several ways of producing
[cocones under span diagrams](synthetic-homotopy-theory.cocones-under-span-diagrams.md)
by combining cocones with other cocones,
[morphisms of arrows](foundation.morphisms-arrows.md),
[equivalences of arrows](foundation.equivalences-arrows.md),
[morphisms of span diagrams](foundation.morphisms-span-diagrams.md),
[equivalences of span diagrams](foundation.equivalences-span-diagrams.md), and
so on.

## Definitions

### Transposing cocones under span diagrams

Any cocone

```text
        g
    S -----> B
    |        |
  f |        | j
    V        V
    A -----> X
        i
```

induces a cocone

```text
        f
    S -----> A
    |        |
  g |        | i
    V        V
    B -----> X.
        j
```

This {{#concept "transposition" Disambiguation="cocones under span diagrams"}}
on cocones is an [involution](foundation.involutions.md).

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4}
  where

  transposition-cocone-span-diagram :
    cocone-span-diagram 𝒮 X →
    cocone-span-diagram (transposition-span-diagram 𝒮) X
  pr1 (transposition-cocone-span-diagram c) =
    right-map-cocone-span-diagram 𝒮 c
  pr1 (pr2 (transposition-cocone-span-diagram c)) =
    left-map-cocone-span-diagram 𝒮 c
  pr2 (pr2 (transposition-cocone-span-diagram c)) =
    inv-htpy (coherence-square-cocone-span-diagram 𝒮 c)

module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) (X : UU l4)
  where

  is-involution-transposition-cocone-span-diagram :
    transposition-cocone-span-diagram (transposition-span-diagram 𝒮) {X} ∘
    transposition-cocone-span-diagram 𝒮 {X} ~
    id
  is-involution-transposition-cocone-span-diagram c =
    eq-htpy-cocone-span-diagram 𝒮
      ( transposition-cocone-span-diagram
        ( transposition-span-diagram 𝒮)
        ( transposition-cocone-span-diagram 𝒮 c))
      ( c)
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ t →
          concat
            ( right-unit)
            ( coherence-square-cocone-span-diagram 𝒮 c t)
            ( inv-inv (coherence-square-cocone-span-diagram 𝒮 c t))))

module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) (X : UU l4)
  where

  is-equiv-transposition-cocone-span-diagram :
    is-equiv (transposition-cocone-span-diagram 𝒮 {X})
  is-equiv-transposition-cocone-span-diagram =
    is-equiv-is-invertible
      ( transposition-cocone-span-diagram (transposition-span-diagram 𝒮))
      ( is-involution-transposition-cocone-span-diagram
        ( transposition-span-diagram 𝒮)
        ( X))
      ( is-involution-transposition-cocone-span-diagram 𝒮 X)

  equiv-transposition-cocone-span-diagram :
    cocone-span-diagram 𝒮 X ≃
    cocone-span-diagram (transposition-span-diagram 𝒮) X
  pr1 equiv-transposition-cocone-span-diagram =
    transposition-cocone-span-diagram 𝒮
  pr2 equiv-transposition-cocone-span-diagram =
    is-equiv-transposition-cocone-span-diagram
```

### Postcomposing cocones under span diagrams with maps

Consider a span diagram `A <-f- S -g-> B`. equipped with a cocone
`c := (i , j , H)` as indicated in the diagram

```text
        g
    S -----> B
    |        |
  f |   H    | j
    V        V
    A -----> X.
        i
```

Then any map `h : X → Y` induces a cocone

```text
         g
    S -------> B
    |          |
  f |  h · H   | h ∘ j
    V          V
    A -------> Y.
       h ∘ i
```

This way of extending cocones by maps is used to express the
[universal property of pushouts](synthetic-homotopy-theory.universal-property-pushouts.md).

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4} {Y : UU l5}
  where

  cocone-map-span-diagram :
    cocone-span-diagram 𝒮 X → (X → Y) → cocone-span-diagram 𝒮 Y
  pr1 (cocone-map-span-diagram c h) =
    h ∘ left-map-cocone-span-diagram 𝒮 c
  pr1 (pr2 (cocone-map-span-diagram c h)) =
    h ∘ right-map-cocone-span-diagram 𝒮 c
  pr2 (pr2 (cocone-map-span-diagram c h)) =
    h ·l coherence-square-cocone-span-diagram 𝒮 c

module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4}
  where

  compute-id-cocone-map-span-diagram :
    (c : cocone-span-diagram 𝒮 X) → cocone-map-span-diagram 𝒮 c id ＝ c
  compute-id-cocone-map-span-diagram c =
    eq-pair-Σ refl
      ( eq-pair-Σ refl
        ( eq-htpy (ap-id ∘ coherence-square-cocone-span-diagram 𝒮 c)))

module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  where

  compute-comp-cocone-map-span-diagram :
    (c : cocone-span-diagram 𝒮 X) (h : X → Y) (k : Y → Z) →
    cocone-map-span-diagram 𝒮 c (k ∘ h) ＝
    cocone-map-span-diagram 𝒮 (cocone-map-span-diagram 𝒮 c h) k
  compute-comp-cocone-map-span-diagram (i , j , H) h k =
    eq-pair-Σ refl (eq-pair-Σ refl (eq-htpy (ap-comp k h ∘ H)))
```

### Horizontal composition of cocones under span diagrams

Consider a span diagram `s := A <-f- S -g-> B` and a moprhism `h : B → C`. Then
we can **compose** any cocone `c := (i , j , H)` with codomain `X` under the
span diagram `𝒮` **on the left** with a cocone `d` under the span diagram
`X <-j- B -h-> C` as indicated in the diagram

```text
        g       h
    S ----> B ----> C
    |       |       |
  f |       |       |
    v       v       v
    A ----> X ----> Y
```

to obtain a cocone under the span diagram `A <-f- S -h∘g-> C`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6} (h : codomain-span-diagram 𝒮 → C)
  (c : cocone-span-diagram 𝒮 X)
  (d :
    cocone-span-diagram
      ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
      ( Y))
  where

  left-map-horizontal-comp-cocone-span-diagram :
    domain-span-diagram 𝒮 → Y
  left-map-horizontal-comp-cocone-span-diagram =
    left-map-cocone-span-diagram
      ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
      ( d) ∘
    left-map-cocone-span-diagram 𝒮 c

  right-map-horizontal-comp-cocone-span-diagram : C → Y
  right-map-horizontal-comp-cocone-span-diagram =
    right-map-cocone-span-diagram
      ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
      ( d)

  coherence-square-horizontal-comp-cocone-span-diagram :
    coherence-square-maps
      ( h ∘ right-map-span-diagram 𝒮)
      ( left-map-span-diagram 𝒮)
      ( right-map-horizontal-comp-cocone-span-diagram)
      ( left-map-horizontal-comp-cocone-span-diagram)
  coherence-square-horizontal-comp-cocone-span-diagram =
    pasting-horizontal-coherence-square-maps
      ( right-map-span-diagram 𝒮)
      ( h)
      ( left-map-span-diagram 𝒮)
      ( right-map-cocone-span-diagram 𝒮 c)
      ( right-map-cocone-span-diagram
        ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
        ( d))
      ( left-map-cocone-span-diagram 𝒮 c)
      ( left-map-cocone-span-diagram
        ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
        ( d))
      ( coherence-square-cocone-span-diagram 𝒮 c)
      ( coherence-square-cocone-span-diagram
        ( make-span-diagram (right-map-cocone-span-diagram 𝒮 c) h)
        ( d))

  horizontal-comp-cocone-span-diagram :
    cocone-span-diagram (right-extend-span-diagram 𝒮 h) Y
  pr1 horizontal-comp-cocone-span-diagram =
    left-map-horizontal-comp-cocone-span-diagram
  pr1 (pr2 horizontal-comp-cocone-span-diagram) =
    right-map-horizontal-comp-cocone-span-diagram
  pr2 (pr2 horizontal-comp-cocone-span-diagram) =
    coherence-square-horizontal-comp-cocone-span-diagram
```

### Cocones under span diagrams extended on the left by morphisms and equivalences of arrows

Consider a span diagram `s := A <-f- S -g-> B`, a cocone on `𝒮`, and a
[moprhism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f` for
some map `f : S' → A'`, as indicated in the diagram

```text
          h₀       g
     S' -----> S -----> B
     |         |        |
  f' |    h    | f      | j
     v         v        v
     A' -----> A -----> X
          h₁       i
```

Then we obtain a new cocone on the outer span diagram `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A') {X : UU l6}
  where

  cocone-left-extend-hom-arrow-span-diagram :
    (h : hom-arrow f' (left-map-span-diagram 𝒮)) → cocone-span-diagram 𝒮 X →
    cocone-span-diagram (left-extend-hom-arrow-span-diagram 𝒮 f' h) X
  cocone-left-extend-hom-arrow-span-diagram h c =
    horizontal-comp-cocone-span-diagram
      ( span-diagram-hom-arrow f' (left-map-span-diagram 𝒮) h)
      ( right-map-span-diagram 𝒮)
      ( cocone-hom-arrow f' (left-map-span-diagram 𝒮) h)
      ( c)

  cocone-left-extend-equiv-arrow-span-diagram :
    (e : equiv-arrow f' (left-map-span-diagram 𝒮)) → cocone-span-diagram 𝒮 X →
    cocone-span-diagram (left-extend-equiv-arrow-span-diagram 𝒮 f' e) X
  cocone-left-extend-equiv-arrow-span-diagram e =
    cocone-left-extend-hom-arrow-span-diagram
      ( hom-equiv-arrow f' (left-map-span-diagram 𝒮) e)
```

Consider a span diagram `s := A <-f- S -g-> B`, a cocone `(i , j , H)` on `𝒮`,
and a moprhism of arrows `h : hom-arrow j j'` for some map `j' : B' → X'`, as
indicated in the diagram

```text
        g        h₀
    S -----> B -----> B'
    |        |        |
  f |      j |   h    | j'
    v        v        ∨
    A -----> X -----> X'
        i        h₁
```

Then we obtain a new cocone on the outer span diagram `A <- S -> B'`.

### Vertical composition of cocones under span diagrams

Consider a span diagram `s := A <-f- S -g-> B` and a map `h : A → C`. Then we
can **compose** a cocone `c := (i , j , H)` under `𝒮` **on the right** with a
cocone `d` under the span diagram `C <-h- A -i-> X` as indicated in the diagram

```text
        g
    S -----> B
    |        |
  f |        |
    v        v
    A -----> X
    |        |
  h |        |
    v        v
    C -----> Y
```

to obtain a cocone under the span diagram `C <-h∘f- S -g-> B`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {C : UU l4} (h : domain-span-diagram 𝒮 → C) {X : UU l5} {Y : UU l6}
  (c : cocone-span-diagram 𝒮 X)
  (d :
    cocone-span-diagram
      ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
      ( Y))
  where

  left-map-vertical-comp-cocone-span-diagram : C → Y
  left-map-vertical-comp-cocone-span-diagram =
    left-map-cocone-span-diagram
      ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
      ( d)

  right-map-vertical-comp-cocone-span-diagram : codomain-span-diagram 𝒮 → Y
  right-map-vertical-comp-cocone-span-diagram =
    right-map-cocone-span-diagram
      ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
      ( d) ∘
    right-map-cocone-span-diagram 𝒮 c

  coherence-square-vertical-comp-cocone-span-diagram :
    coherence-square-maps
      ( right-map-span-diagram 𝒮)
      ( h ∘ left-map-span-diagram 𝒮)
      ( right-map-vertical-comp-cocone-span-diagram)
      ( left-map-vertical-comp-cocone-span-diagram)
  coherence-square-vertical-comp-cocone-span-diagram =
    pasting-vertical-coherence-square-maps
      ( right-map-span-diagram 𝒮)
      ( left-map-span-diagram 𝒮)
      ( right-map-cocone-span-diagram 𝒮 c)
      ( left-map-cocone-span-diagram 𝒮 c)
      ( h)
      ( right-map-cocone-span-diagram
        ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
        ( d))
      ( left-map-cocone-span-diagram
        ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
        ( d))
      ( coherence-square-cocone-span-diagram 𝒮 c)
      ( coherence-square-cocone-span-diagram
        ( make-span-diagram h (left-map-cocone-span-diagram 𝒮 c))
        ( d))

  vertical-comp-cocone-span-diagram :
    cocone-span-diagram (left-extend-span-diagram 𝒮 h) Y
  pr1 vertical-comp-cocone-span-diagram =
    left-map-vertical-comp-cocone-span-diagram
  pr1 (pr2 vertical-comp-cocone-span-diagram) =
    right-map-vertical-comp-cocone-span-diagram
  pr2 (pr2 vertical-comp-cocone-span-diagram) =
    coherence-square-vertical-comp-cocone-span-diagram
```

### Composing cocones with morphisms of arrows on the right

Consider a span diagram `s := A <-f- S -g-> B` and a map `g' : S' → B'`. Then we
can **compose** a morphism of arrows `h : hom-arrow g' g` with a cocone
`c := (i , j , H)` under `𝒮`, as indicated in the diagram

```text
         g'
     S' ----> B'
     |        |
  h₀ |        | h₁
     v   g    v
     S -----> B
     |        |
   f |        |
     v        v
     A -----> X
```

to obtain a cocone under the span diagram `A <- S' -> B'`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (𝒮 : span-diagram l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B') {X : UU l6}
  where

  cocone-right-extend-hom-arrow-span-diagram :
    (h : hom-arrow g' (right-map-span-diagram 𝒮)) → cocone-span-diagram 𝒮 X →
    cocone-span-diagram (right-extend-hom-arrow-span-diagram 𝒮 g' h) X
  cocone-right-extend-hom-arrow-span-diagram h c =
    vertical-comp-cocone-span-diagram
      ( span-diagram-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span-diagram 𝒮) h)
        ( map-codomain-hom-arrow g' (right-map-span-diagram 𝒮) h)
        ( transpose-hom-arrow g' (right-map-span-diagram 𝒮) h))
      ( left-map-span-diagram 𝒮)
      ( cocone-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span-diagram 𝒮) h)
        ( map-codomain-hom-arrow g' (right-map-span-diagram 𝒮) h)
        ( transpose-hom-arrow g' (right-map-span-diagram 𝒮) h))
      ( c)

  cocone-right-extend-equiv-arrow-span-diagram :
    (e : equiv-arrow g' (right-map-span-diagram 𝒮)) → cocone-span-diagram 𝒮 X →
    cocone-span-diagram (right-extend-equiv-arrow-span-diagram 𝒮 g' e) X
  cocone-right-extend-equiv-arrow-span-diagram e =
    cocone-right-extend-hom-arrow-span-diagram
      ( hom-equiv-arrow g' (right-map-span-diagram 𝒮) e)
```

### Composition of cocones and morphisms of span diagrams

Given a commutative diagram of the form

```text
          g'
     S' ------> B'
     | \         \
     |  \ k       \ j
     v   v     g   v
     A'   S ------> B
      \   |         |
     i \  | f       |
        v v         v
          A ------> X
```

we can compose both vertically and horizontally to get the following cocone:

```text
   S' ---> B'
   |       |
   |       |
   v       v
   A' ---> X
```

Notice that the triple `(i,j,k)` is really a morphism of span diagrams. So the
resulting cocone arises as a composition of the original cocone with this
morphism of span diagrams.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (𝒮' : span-diagram l1 l2 l3) (𝒮 : span-diagram l4 l5 l6)
  (h : hom-span-diagram 𝒮' 𝒮)
  {X : UU l7} (c : cocone-span-diagram 𝒮 X)
  where

  comp-cocone-hom-span-diagram : cocone-span-diagram 𝒮' X
  comp-cocone-hom-span-diagram =
    cocone-right-extend-hom-arrow-span-diagram
      ( left-extend-hom-arrow-span-diagram 𝒮
        ( left-map-span-diagram 𝒮')
        ( left-hom-arrow-hom-span-diagram 𝒮' 𝒮 h))
      ( right-map-span-diagram 𝒮')
      ( ( id) ,
        ( map-codomain-hom-span-diagram 𝒮' 𝒮 h) ,
        ( right-square-hom-span-diagram 𝒮' 𝒮 h))
      ( cocone-left-extend-hom-arrow-span-diagram
        ( 𝒮)
        ( left-map-span-diagram 𝒮')
        ( left-hom-arrow-hom-span-diagram 𝒮' 𝒮 h)
        ( c))

module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (𝒮' : span-diagram l1 l2 l3) (𝒮 : span-diagram l4 l5 l6)
  (e : equiv-span-diagram 𝒮' 𝒮)
  {X : UU l7} (c : cocone-span-diagram 𝒮 X)
  where

  comp-cocone-equiv-span-diagram : cocone-span-diagram 𝒮' X
  comp-cocone-equiv-span-diagram =
    comp-cocone-hom-span-diagram 𝒮' 𝒮 (hom-equiv-span-diagram 𝒮' 𝒮 e) c
```
