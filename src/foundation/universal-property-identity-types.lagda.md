# The universal property of identity types

```agda
module foundation.universal-property-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.axiom-l
open import foundation.embeddings
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositional-maps
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.injective-maps
open import foundation-core.propositions
```

</details>

## Idea

The universal property of identity types characterizes families of maps out of
the identity type. This universal property is also known as the type theoretic
Yoneda lemma.

## Theorem

```agda
ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → a ＝ x → UU l2} →
  ((x : A) (p : a ＝ x) → B x p) → B a refl
ev-refl a f = f a refl

abstract
  is-equiv-ev-refl :
    {l1 l2 : Level} {A : UU l1} (a : A)
    {B : (x : A) → a ＝ x → UU l2} → is-equiv (ev-refl a {B = B})
  is-equiv-ev-refl a =
    is-equiv-has-inverse
      ( ind-Id a _)
      ( λ b → refl)
      ( λ f → eq-htpy
        ( λ x → eq-htpy
          ( ind-Id a
            ( λ x' p' → ind-Id a _ (f a refl) x' p' ＝ f x' p')
            ( refl) x)))

equiv-ev-refl :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → a ＝ x → UU l2} →
  ((x : A) (p : a ＝ x) → B x p) ≃ (B a refl)
pr1 (equiv-ev-refl a) = ev-refl a
pr2 (equiv-ev-refl a) = is-equiv-ev-refl a

equiv-ev-refl' :
  {l1 l2 : Level} {A : UU l1} (a : A) {B : (x : A) → x ＝ a → UU l2} →
  ((x : A) (p : x ＝ a) → B x p) ≃ B a refl
equiv-ev-refl' a {B} =
  equiv-ev-refl a ∘e equiv-map-Π (λ x → equiv-precomp-Π (equiv-inv a x) (B x))
```

### `Id : A → (A → 𝒰)` is an embedding

We first show that [axiom L](foundation.axiom-l.md) implies that the map `Id : A → (A → 𝒰)` is an [embedding](foundation.embeddings.md). Since the [univalence axiom](foundation.univalence.md) implies axiom L, it follows that `Id : A → (A → 𝒰)` is an embedding under the postulates of agda-unimath.

#### Axiom L implies that `Id : A → (A → 𝒰)` is an embedding

The proof that axiom L implies that `Id : A → (A → 𝒰)` is an embedding proceeds via the [fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md) by showing that the [fiber](foundation.fibers-of-maps.md) of `Id` at `Id x` is [contractible](foundation.contractible-types.md) for each `x : A`. 

```agda
module _
  {l : Level} (L : axiom-L l) (A : UU l)
  where

  is-emb-Id-axiom-L : is-emb (Id {A = A})
  is-emb-Id-axiom-L x =
    fundamental-theorem-id
      ( pair
        ( pair x refl)
        ( λ _ →
          is-injective-emb
            ( emb-fib x)
            ( eq-is-contr (is-contr-total-path x))))
      ( λ _ → ap Id)
    where
    emb-fib : (x : A) → fib' Id (Id x) ↪ Σ A (Id x)
    emb-fib x =
      comp-emb
        ( comp-emb
          ( emb-equiv
            ( equiv-tot
              ( λ y →
                ( equiv-ev-refl y) ∘e
                ( ( equiv-inclusion-is-full-subtype
                    ( Π-Prop A ∘ (is-equiv-Prop ∘_))
                    ( fundamental-theorem-id (is-contr-total-path x))) ∘e
                  ( distributive-Π-Σ)))))
          ( emb-Σ
            ( λ y → (z : A) → Id y z ≃ Id x z)
            ( id-emb)
            ( λ y →
              comp-emb
                ( emb-Π (λ z → emb-L L (Id y z) (Id x z)))
                ( emb-equiv equiv-funext))))
        ( emb-equiv (inv-equiv (equiv-fib Id (Id x))))
```

#### `Id : A → (A → 𝒰)` is an embedding

```agda
module _
  {l : Level} (A : UU l)
  where

  is-emb-Id : is-emb (Id {A = A})
  is-emb-Id = is-emb-Id-axiom-L (axiom-L-univalence univalence) A
```

#### For any type family `B` over `A`, the type of pairs `(a , e)` consisting of `a : A` and a family of equivalences `e : (x : A) → (a ＝ x) ≃ B x` is a proposition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-proof-irrelevant-total-family-of-equivalences-Id :
    is-proof-irrelevant (Σ A (λ a → (x : A) → (a ＝ x) ≃ B x))
  is-proof-irrelevant-total-family-of-equivalences-Id (a , e) =
    is-contr-equiv
      ( Σ A (λ b → (x : A) → (b ＝ x) ≃ (a ＝ x)))
      ( equiv-tot
        ( λ b →
          equiv-map-Π
            ( λ x → equiv-postcomp-equiv (inv-equiv (e x)) (b ＝ x))))
      ( is-contr-equiv'
        ( fib Id (Id a))
        ( equiv-tot
          ( λ b → equiv-map-Π (λ x → equiv-univalence) ∘e equiv-funext))
        ( is-proof-irrelevant-is-prop
          ( is-prop-map-is-emb (is-emb-Id A) (Id a))
          ( a , refl)))

  is-prop-total-family-of-equivalences-Id :
    is-prop (Σ A (λ a → (x : A) → (a ＝ x) ≃ B x))
  is-prop-total-family-of-equivalences-Id =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-total-family-of-equivalences-Id)
```
