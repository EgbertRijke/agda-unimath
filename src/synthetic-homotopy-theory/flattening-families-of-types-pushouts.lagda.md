# Flattening families of types over pushouts

```agda
module synthetic-homotopy-theory.flattening-families-of-types-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.descent-property-families-of-types-pushouts
open import synthetic-homotopy-theory.equivalences-families-of-types-pushouts
open import synthetic-homotopy-theory.families-of-types-pushouts
```

</details>

## Idea

Consider the [structure of a type family](synthetic-homotopy-theory.families-of-types-pushouts.md) `(P , Q , e)` over a [span diagram](foundation.span-diagrams.md) `s`. The {{#concept "flattening" Disambiguation="families over span diagrams"}} of `(P , Q , e)` is the span diagram

```text
  Σ (a : A), P a <-- Σ (s : S), P (f s) --> Σ (s : S), Q (g s) --> Σ (b : B), Q b
```

where the map in the middle is the [map on total spaces](foundation.functoriality-dependent-pair-types.md) of the [family of equivalences](foundation.families-of-equivalences.md) `e`.

In the case where the structure of a family over a span diagram is obtained from a type family `P` over the codomain of a [cocone](synthetic-homotopy-theory.cocones-under-span-diagrams.md), we obtain a cocone on the flattening of that structure. This will be called the {{#concept "flattening" Disambiguation="families over cocones under span diagrams"}}.

The flattening span diagrams and cocones introduced in this file will be used to state and prove the [flattening lemma](synthetic-homotopy-theory.flattening-lemma.md).

## Definitions

### Flattening of the structure of a type family over a span diagram

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 s)
  where

  spanning-type-flattening-structure-type-family-pushout : UU (l3 ⊔ l4)
  spanning-type-flattening-structure-type-family-pushout =
    Σ ( spanning-type-span-diagram s)
      ( ( left-type-family-structure-type-family-pushout s P) ∘
        ( left-map-span-diagram s))

  domain-flattening-structure-type-family-pushout : UU (l1 ⊔ l4)
  domain-flattening-structure-type-family-pushout =
    Σ ( domain-span-diagram s)
      ( left-type-family-structure-type-family-pushout s P)

  codomain-flattening-structure-type-family-pushout : UU (l2 ⊔ l4)
  codomain-flattening-structure-type-family-pushout =
    Σ ( codomain-span-diagram s)
      ( right-type-family-structure-type-family-pushout s P)

  left-map-flattening-structure-type-family-pushout :
    spanning-type-flattening-structure-type-family-pushout →
    domain-flattening-structure-type-family-pushout
  left-map-flattening-structure-type-family-pushout =
    map-Σ-map-base
      ( left-map-span-diagram s)
      ( left-type-family-structure-type-family-pushout s P)

  right-map-flattening-structure-type-family-pushout :
    spanning-type-flattening-structure-type-family-pushout →
    codomain-flattening-structure-type-family-pushout
  right-map-flattening-structure-type-family-pushout =
    map-Σ
      ( right-type-family-structure-type-family-pushout s P)
      ( right-map-span-diagram s)
      ( map-matching-equiv-structure-type-family-pushout s P)

  span-flattening-structure-type-family-pushout :
    span
      ( l3 ⊔ l4)
      ( domain-flattening-structure-type-family-pushout)
      ( codomain-flattening-structure-type-family-pushout)
  pr1 span-flattening-structure-type-family-pushout =
    spanning-type-flattening-structure-type-family-pushout
  pr1 (pr2 span-flattening-structure-type-family-pushout) =
    left-map-flattening-structure-type-family-pushout
  pr2 (pr2 span-flattening-structure-type-family-pushout) =
    right-map-flattening-structure-type-family-pushout

  span-diagram-flattening-structure-type-family-pushout :
    span-diagram (l1 ⊔ l4) (l2 ⊔ l4) (l3 ⊔ l4)
  span-diagram-flattening-structure-type-family-pushout =
    make-span-diagram
      left-map-flattening-structure-type-family-pushout
      right-map-flattening-structure-type-family-pushout
```

### Flattening families over cocones equipped with structure of families over span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  (P : structure-type-family-pushout l5 s)
  (Q : X → UU l5)
  (e :
    equiv-structure-type-family-pushout s P
      ( descent-data-type-family-pushout s c Q))
  where

  left-map-cocone-flattening-structure-type-family-pushout :
    domain-flattening-structure-type-family-pushout s P → Σ X Q
  left-map-cocone-flattening-structure-type-family-pushout =
    map-Σ Q
      ( left-map-cocone-span-diagram s c)
      ( map-left-equiv-equiv-structure-type-family-pushout s P
        ( descent-data-type-family-pushout s c Q)
        ( e))

  right-map-cocone-flattening-structure-type-family-pushout :
    codomain-flattening-structure-type-family-pushout s P → Σ X Q
  right-map-cocone-flattening-structure-type-family-pushout =
    map-Σ Q
      ( right-map-cocone-span-diagram s c)
      ( map-right-equiv-equiv-structure-type-family-pushout s P
        ( descent-data-type-family-pushout s c Q)
        ( e))

  coherence-square-cocone-flattening-structure-type-family-pushout :
    coherence-square-maps
      ( right-map-flattening-structure-type-family-pushout s P)
      ( left-map-flattening-structure-type-family-pushout s P)
      ( right-map-cocone-flattening-structure-type-family-pushout)
      ( left-map-cocone-flattening-structure-type-family-pushout)
  coherence-square-cocone-flattening-structure-type-family-pushout =
    htpy-map-Σ Q
      ( coherence-square-cocone-span-diagram s c)
      ( λ x →
        map-left-equiv-equiv-structure-type-family-pushout s P
          ( descent-data-type-family-pushout s c Q)
          ( e)
          ( left-map-span-diagram s x))
      ( λ x →
        inv-htpy
          ( coherence-equiv-structure-type-family-pushout s P
            ( descent-data-type-family-pushout s c Q)
            ( e)
            ( x)))

  cocone-flattening-structure-type-family-pushout :
    cocone-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout s P)
      ( Σ X Q)
  pr1 cocone-flattening-structure-type-family-pushout =
    left-map-cocone-flattening-structure-type-family-pushout
  pr1 (pr2 cocone-flattening-structure-type-family-pushout) =
    right-map-cocone-flattening-structure-type-family-pushout
  pr2 (pr2 cocone-flattening-structure-type-family-pushout) =
    coherence-square-cocone-flattening-structure-type-family-pushout
```

### Flattening families of types over pushouts

Consider a type family `P` over the codomain `X` of a cocone `c` under  a span diagram `A <- S -> B`. The descent data of `P` then yields the [structure of a type family](synthetic-homotopy-theory.structure-type-family-pushout.md) over a pushout. The flattening of `P` consists of the span diagram and the cocone as displayed in the following commuting square:

```text
  Σ (s : S), P(if(s)) ---> Σ (s : S), P(jg(s)) ---> Σ (b : B), P(j(b))
           |                                                 |
           |                                                 |
           V                                               ⌜ V
  Σ (a : A), P(i(a)) -----------------------------> Σ (x : X), P(x).
```

Note that this is defined as a special case of the flattening of the structure of a type family over a pushout, by first taking the descent data of `P` and then flattening.

```agda
module _
  { l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  { X : UU l4} (c : cocone-span-diagram s X) (P : X → UU l5)
  where

  spanning-type-flattening-type-family-pushout : UU (l3 ⊔ l5)
  spanning-type-flattening-type-family-pushout =
    spanning-type-flattening-structure-type-family-pushout s
      ( descent-data-type-family-pushout s c P)

  domain-flattening-type-family-pushout : UU (l1 ⊔ l5)
  domain-flattening-type-family-pushout =
    domain-flattening-structure-type-family-pushout s
      ( descent-data-type-family-pushout s c P)

  codomain-flattening-type-family-pushout : UU (l2 ⊔ l5)
  codomain-flattening-type-family-pushout =
    codomain-flattening-structure-type-family-pushout s
      ( descent-data-type-family-pushout s c P)

  left-map-flattening-type-family-pushout :
    spanning-type-flattening-type-family-pushout →
    domain-flattening-type-family-pushout
  left-map-flattening-type-family-pushout =
    left-map-flattening-structure-type-family-pushout s
      ( descent-data-type-family-pushout s c P)

  right-map-flattening-type-family-pushout :
    spanning-type-flattening-type-family-pushout →
    codomain-flattening-type-family-pushout
  right-map-flattening-type-family-pushout =
    right-map-flattening-structure-type-family-pushout s
      ( descent-data-type-family-pushout s c P)

  span-flattening-type-family-pushout :
    span
      ( l3 ⊔ l5)
      ( domain-flattening-type-family-pushout)
      ( codomain-flattening-type-family-pushout)
  span-flattening-type-family-pushout =
    span-flattening-structure-type-family-pushout s
      ( descent-data-type-family-pushout s c P)

  span-diagram-flattening-type-family-pushout :
    span-diagram (l1 ⊔ l5) (l2 ⊔ l5) (l3 ⊔ l5)
  span-diagram-flattening-type-family-pushout =
    span-diagram-flattening-structure-type-family-pushout s
      ( descent-data-type-family-pushout s c P)

  left-map-cocone-flattening-type-family-pushout :
    domain-flattening-type-family-pushout → Σ X P
  left-map-cocone-flattening-type-family-pushout =
    left-map-cocone-flattening-structure-type-family-pushout s c
      ( descent-data-type-family-pushout s c P)
      ( P)
      ( id-equiv-structure-type-family-pushout s
        ( descent-data-type-family-pushout s c P))

  right-map-cocone-flattening-type-family-pushout :
    codomain-flattening-type-family-pushout → Σ X P
  right-map-cocone-flattening-type-family-pushout =
    right-map-cocone-flattening-structure-type-family-pushout s c
      ( descent-data-type-family-pushout s c P)
      ( P)
      ( id-equiv-structure-type-family-pushout s
        ( descent-data-type-family-pushout s c P))

  coherence-square-cocone-flattening-type-family-pushout :
    coherence-square-maps
      ( right-map-flattening-type-family-pushout)
      ( left-map-flattening-type-family-pushout)
      ( right-map-cocone-flattening-type-family-pushout)
      ( left-map-cocone-flattening-type-family-pushout)
  coherence-square-cocone-flattening-type-family-pushout =
    coherence-square-cocone-flattening-structure-type-family-pushout s c
      ( descent-data-type-family-pushout s c P)
      ( P)
      ( id-equiv-structure-type-family-pushout s
        ( descent-data-type-family-pushout s c P))

  cocone-flattening-type-family-pushout :
    cocone-span-diagram span-diagram-flattening-type-family-pushout (Σ X P)
  cocone-flattening-type-family-pushout =
    cocone-flattening-structure-type-family-pushout s c
      ( descent-data-type-family-pushout s c P)
      ( P)
      ( id-equiv-structure-type-family-pushout s
        ( descent-data-type-family-pushout s c P))
```

## Properties

### Computation of cocones under the flattening span diagram of the structure of a type family of a pushout

Consider the structure of a type family `(P , Q , e)` over a span diagram `A <- S -> B`, with flattening span diagram `𝒯`

```text
  Σ (a : A), P a <-- Σ (s : S), P (f s) --> Σ (s : S), Q (g s) --> Σ (b : B), Q b.
```

Furthermore, consider a type `X`, a type family `Y` over `X`, a cocone `c` on `𝒮` with codomain `X` and a dependent cocone `d` on `𝒯` over `c` with codomain `Y`. Then there is an equivalence

```text
  cocone 𝒯 Z ≃ dependent-cocone 𝒮 c (λ x → Y x → Z)
```


Then the type of cocones under `𝒯` with codomain `X` is equivalent to the type of pairs `(c , d)` consisting of a cocone `c` under `𝒮` with codomain `X` and a dependent cocone `d` over `C`

Then a cocone under `𝒯` with codomain `X` is equivalently described as a triple `(p , q , H)` consisting of

```text
  p : (a : A) → P a → X
  q : (b : B) → Q b → X
  H : (s : S) (t : P (f s)) → p (f s) t ＝ q (g s) (e s t).
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  (Y : X → UU l5)
  (Q : structure-type-family-pushout l6 s)
  (e : equiv-structure-type-family-pushout s c Y Q)
  where
```

```text
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  (P : structure-type-family-pushout l4 s) (X : UU l5)
  where

  structure-cocone-flattening-structure-type-family-pushout :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  structure-cocone-flattening-structure-type-family-pushout =
    Σ ( (a : domain-span-diagram s) →
        left-type-family-structure-type-family-pushout s P a → X)
      ( λ p →
        Σ ( (b : codomain-span-diagram s) →
            right-type-family-structure-type-family-pushout s P b → X)
          ( λ q →
            (x : spanning-type-span-diagram s) →
            (t : spanning-type-family-structure-type-family-pushout s P x) →
            p (left-map-span-diagram s x) t ＝
            q ( right-map-span-diagram s x)
              ( map-matching-equiv-structure-type-family-pushout s P x t)))

  compute-cocone-flattening-structure-type-family-pushout :
    cocone-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout s P)
      ( X) ≃
    structure-cocone-flattening-structure-type-family-pushout
  compute-cocone-flattening-structure-type-family-pushout =
    equiv-Σ _
      ( equiv-ev-pair)
      ( λ _ → equiv-Σ _ equiv-ev-pair (λ _ → equiv-ev-pair))

  map-compute-cocone-flattening-structure-type-family-pushout :
    cocone-span-diagram
      ( span-diagram-flattening-structure-type-family-pushout s P)
      ( X) →
    structure-cocone-flattening-structure-type-family-pushout
  map-compute-cocone-flattening-structure-type-family-pushout =
    map-equiv compute-cocone-flattening-structure-type-family-pushout

  triangle-compute-cocone-flattening-structure-type-family-pushout :
    coherence-triangle-maps
      {!!}
      {!!}
      {!!}
  triangle-compute-cocone-flattening-structure-type-family-pushout = {!!}

{-
  triangle-comparison-dependent-cocone-ind-Σ-cocone :
    { l : Level} (Y : UU l) →
    coherence-triangle-maps
      ( dependent-cocone-map-span-diagram s c (λ x → P x → Y))
      ( map-equiv (comparison-dependent-cocone-ind-Σ-cocone Y))
      ( map-equiv equiv-ev-pair³ ∘ cocone-map-flattening-type-family-pushout Y ∘ ind-Σ)
-}
```
