# Whiskering pointed homotopies with respect to concatenation

```agda
module structured-types.whiskering-pointed-homotopies-concatenation where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.universe-levels
open import foundation.whiskering-homotopies-concatenation
open import foundation.whiskering-identifications-concatenation

open import structured-types.pointed-homotopies
open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Idea

The [whiskering operations](foundation.whiskering-operations.md) of
[pointed homotopies](structured-types.pointed-homotopies.md) are operations that
take a pointed `2`-homotopy between two pointed homotopies `H K : f ~∗ g`
between [pointed maps](structured-types.pointed-maps.md) `f g : A →∗ B` and a
pointed homotopy `α` either into `H` or out of `K` and return a pointed
`2`-homotopy from the concatenation of `α` and `H` to the concatenation of `α`
and `K`. There are two such operations: left whiskering and right whiskering.

The
{{#concept "left whiskering" Disambiguation="pointed 2-homotopies with respect to concatenation" Agda=left-whisker-concat-pointed-2-htpy}}
is an operation that takes a pointed homotopy `H : f ~∗ g` and a pointed
2-homotopy `α : K ~∗ L` between two pointed homotopies `K L : g ~∗ h` as
indicated in the diagram

```text
               K
      H      ----->
  f -----> g -----> h,
               L
```

and returns a pointed 2-homotopy `H ∙h K ~∗ H ∙h K`.

The
{{#concept "right whiskering" Disambiguation="pointed 2-homotopies with respect to concatenation" Agda=right-whisker-concat-pointed-2-htpy}}
is an operation that takes a pointed 2-homotopy `α : H ~∗ K` between two pointed
homotopies `H K : f ~∗ g` and a pointed homotopy `L : g ~∗ h` as indicated in
the diagram

```text
      H
    ----->
  f -----> g -----> h,
      K        L
```

and returns a pointed 2-homotopy `H ∙h L ~∗ K ∙h L`.

## Definitions

### Left whiskering of pointed 2-homotopies with respect to concatenation

Consider three pointed maps `f := (f₀ , f₁)`, `g := (g₀ , g₁)`, and
`h := (h₀ , h₁)` from `A` to `B`, a pointed homotopy `H := (H₀ , H₁) : f ~∗ g`
and a pointed 2-homotopy `α := (α₀ , α₁) : K ~∗ L` between two pointed
homotopies `K := (K₀ , K₁)` and `L := (L₀ , L₁)` from `g` to `h` as indicated in
the diagram

```text
               K
      H      ----->
  f -----> g -----> h.
               L
```

The underlying homotopy of the left whiskering `H ·l α : H ∙h K ~∗ H ∙h L` is
the homotopy

```text
  H₀ ·l α₀ : H₀ ∙h K₀ ~ H₀ ∙h L₀.
```

The base point coherence of this homotopy is an identification witnessing that
the triangle

```text
           (H ∙h K)₁
        f₁ --------> ((H₀ *) ∙ (K₀ *)) ∙ h₁
           \       /
  (H ∙h L)₁ \     / right-whisker (left-whisker (H₀ *) (α₀ *)) h₁
             \   /
              ∨ ∨
    ((H₀ *) ∙ (L₀ *)) ∙ h₁
```

commutes. Here, the identifications `(H ∙h K)₁` and `(H ∙h L)₁` are the
horizontal pastings of the
[commuting triangles of identifications](foundation-core.commuting-triangles-identifications.md)

```text
       H₀ *      K₀ *                   H₀ *      L₀ *
  f₀ * ---> g₀ * ----> h₀ *        f₀ * ---> g₀ * ----> h₀ *
       \      |      /                  \      |      /
        \  H₁ |  K₁ /                    \  H₁ |  L₁ /
     f₁  \    |g₁  / h₁               f₁  \    |g₁  / h₁
          \   |   /                        \   |   /
           \  |  /                          \  |  /
            ∨ ∨ ∨                            ∨ ∨ ∨
              *                                *.
```

Then the triangle

```text
                   horizontal-pasting H₁ K₁
                       f₁ --------> (H₀ * ∙ K₀ *) ∙ h₁
                         \         /
                          \       /
  horizontal-pasting H₁ L₁ \     / right-whisker (left-whisker (H₀ *) (α₀ *)) h₁
                            \   /
                             ∨ ∨
                        (H₀ * ∙ K₀ *) ∙ h₁
```

commutes by left whiskering of horizontal pasting of commuting triangles of
identifications.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {f g h : A →∗ B} (H : f ~∗ g) (K L : g ~∗ h) (α : K ~²∗ L)
  where

  htpy-left-whisker-concat-pointed-2-htpy :
    unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy H K)
      ( concat-pointed-htpy H L)
  htpy-left-whisker-concat-pointed-2-htpy =
    left-whisker-concat-htpy (htpy-pointed-htpy H) (htpy-pointed-2-htpy K L α)

  coherence-point-left-whisker-concat-pointed-2-htpy :
    coherence-point-unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy H K)
      ( concat-pointed-htpy H L)
      ( htpy-left-whisker-concat-pointed-2-htpy)
  coherence-point-left-whisker-concat-pointed-2-htpy =
    left-whisker-horizontal-pasting-coherence-triangle-identifications
      ( preserves-point-pointed-map f)
      ( preserves-point-pointed-map g)
      ( preserves-point-pointed-map h)
      ( htpy-pointed-htpy H (point-Pointed-Type A))
      ( htpy-pointed-htpy K (point-Pointed-Type A))
      ( htpy-pointed-htpy L (point-Pointed-Type A))
      ( coherence-point-pointed-htpy H)
      ( coherence-point-pointed-htpy K)
      ( coherence-point-pointed-htpy L)
      ( htpy-pointed-2-htpy K L α (point-Pointed-Type A))
      ( coherence-point-pointed-2-htpy K L α)

  left-whisker-concat-pointed-2-htpy :
    concat-pointed-htpy H K ~²∗ concat-pointed-htpy H L
  pr1 left-whisker-concat-pointed-2-htpy =
    htpy-left-whisker-concat-pointed-2-htpy
  pr2 left-whisker-concat-pointed-2-htpy =
    coherence-point-left-whisker-concat-pointed-2-htpy
```

### Right whiskering of pointed 2-homotopies with respect to concatenation

Consider three pointed maps `f := (f₀ , f₁)`, `g := (g₀ , g₁)`, and
`h := (h₀ , h₁)` from `A` to `B`, a pointed 2-homotopy `α := (α₀ , α₁) : H ~∗ K`
between two pointed homotopies `H := (H₀ , H₁)` and `K := (K₀ , K₁)` from `f` to
`g` and a pointed homotopy `L := (L₀ , L₁) : g ~∗ h` as indicated in the diagram

```text
      H
    ----->
  f -----> g -----> h.
      K        L
```

The underlying homotopy of the right whiskering `α ·r L : H ∙h L ~∗ K ∙h L` is
the homotopy

```text
  α₀ ·r L₀ : H₀ ∙h L₀ ~ K₀ ∙h L₀.
```

The base point coherence of this homotopy is an identification witnessing that
the triangle

```text
           (H ∙h L)₁
        f₁ --------> ((H₀ *) ∙ (L₀ *)) ∙ h₁
           \       /
  (K ∙h L)₁ \     / right-whisker (right-whisker (α₀ *) (L₀ *)) h₁
             \   /
              ∨ ∨
    ((K₀ *) ∙ (L₀ *)) ∙ h₁
```

commutes. Here, the identifications `(H ∙h L)₁` and `(K ∙h L)₁` are the
horizontal pastings of the
[commuting triangles of identifications](foundation-core.commuting-triangles-identifications.md)

```text
       H₀ *      L₀ *                   K₀ *      L₀ *
  f₀ * ---> g₀ * ----> h₀ *        f₀ * ---> g₀ * ----> h₀ *
       \      |      /                  \      |      /
        \  H₁ |  L₁ /                    \  K₁ |  L₁ /
     f₁  \    |g₁  / h₁               f₁  \    |g₁  / h₁
          \   |   /                        \   |   /
           \  |  /                          \  |  /
            ∨ ∨ ∨                            ∨ ∨ ∨
              *                                *.
```

Then the triangle

```text
                   horizontal-pasting H₁ L₁
                       f₁ --------> (H₀ * ∙ L₀ *) ∙ h₁
                         \         /
                          \       /
  horizontal-pasting K₁ L₁ \     / right-whisker (right-whisker (α₀ *) (L₀ *)) h₁
                            \   /
                             ∨ ∨
                        (K₀ * ∙ L₀ *) ∙ h₁
```

commutes by right whiskering of horizontal pasting of commuting triangles of
identifications.

```agda
module _
  {l1 l2 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {f g h : A →∗ B} (H K : f ~∗ g) (α : H ~²∗ K) (L : g ~∗ h)
  where

  htpy-right-whisker-concat-pointed-2-htpy :
    unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy H L)
      ( concat-pointed-htpy K L)
  htpy-right-whisker-concat-pointed-2-htpy =
    right-whisker-concat-htpy (htpy-pointed-2-htpy H K α) (htpy-pointed-htpy L)

  coherence-point-right-whisker-concat-pointed-2-htpy :
    coherence-point-unpointed-htpy-pointed-htpy
      ( concat-pointed-htpy H L)
      ( concat-pointed-htpy K L)
      ( htpy-right-whisker-concat-pointed-2-htpy)
  coherence-point-right-whisker-concat-pointed-2-htpy =
    right-whisker-horizontal-pasting-coherence-triangle-identifications
      ( preserves-point-pointed-map f)
      ( preserves-point-pointed-map g)
      ( preserves-point-pointed-map h)
      ( htpy-pointed-htpy H (point-Pointed-Type A))
      ( htpy-pointed-htpy K (point-Pointed-Type A))
      ( htpy-pointed-htpy L (point-Pointed-Type A))
      ( coherence-point-pointed-htpy H)
      ( coherence-point-pointed-htpy K)
      ( coherence-point-pointed-htpy L)
      ( htpy-pointed-2-htpy H K α (point-Pointed-Type A))
      ( coherence-point-pointed-2-htpy H K α)

  right-whisker-concat-pointed-2-htpy :
    concat-pointed-htpy H L ~²∗ concat-pointed-htpy K L
  pr1 right-whisker-concat-pointed-2-htpy =
    htpy-right-whisker-concat-pointed-2-htpy
  pr2 right-whisker-concat-pointed-2-htpy =
    coherence-point-right-whisker-concat-pointed-2-htpy
```