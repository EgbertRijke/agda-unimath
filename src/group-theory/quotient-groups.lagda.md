---
title: Quotient groups
---

```agda
module group-theory.quotient-groups where

open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.embeddings
open import foundation.equivalences
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.powersets
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.slice
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universal-property-image
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.kernels
open import group-theory.normal-subgroups
```

## Idea

Given a normal subgroup `H` of `G`, the quotient group `G/H` is a group equipped with a group homomorphism `q : G → G/H` such that for any group `K` the map

```md
  (G/H → K) → Σ (h : G → K), H ⊆ ker h
```

is an equivalence. This equivalence expresses the universal property of the quotient group.

## Definitions

### The universal property of quotient groups

```agda
kernel-contains-Normal-Subgroup :
  {l1 l2 l3 : Level} (G : Group l1) (H : Normal-Subgroup l2 G) (K : Group l3)
  (h : type-hom-Group G K) → UU (l1 ⊔ l2 ⊔ l3)
kernel-contains-Normal-Subgroup G H K h =
  subset-Normal-Subgroup G H ⊆ subtype-kernel-hom-Group G K h

precomp-quotient-Group :
  {l1 l2 l3 l4 : Level} (G : Group l1) (H : Normal-Subgroup l2 G)
  (K : Group l3) (L : Group l4) (f : type-hom-Group G K) →
  kernel-contains-Normal-Subgroup G H K f →
  type-hom-Group K L →
  Σ (type-hom-Group G L) (kernel-contains-Normal-Subgroup G H L)
pr1 (precomp-quotient-Group G H K L f k h) =
  comp-hom-Group G K L h f
pr2 (precomp-quotient-Group G H K L f k h) x α =
  ap (map-hom-Group K L h) (k x α) ∙ preserves-unit-hom-Group K L h

is-quotient-Group :
  {l1 l2 l3 : Level} (l : Level) (G : Group l1) (H : Normal-Subgroup l2 G)
  (K : Group l3) (f : type-hom-Group G K) →
  kernel-contains-Normal-Subgroup G H K f → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l)
is-quotient-Group l G H K f k =
  (L : Group l) → is-equiv (precomp-quotient-Group G H K L f k)
```

## The construction of quotient groups

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Normal-Subgroup l2 G)
  where

  type-quotient-Group : UU (l1 ⊔ l2)
  type-quotient-Group = set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  map-hom-quotient-Group : type-Group G → type-quotient-Group
  map-hom-quotient-Group = quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  is-surjective-map-hom-quotient-Group :
    is-surjective map-hom-quotient-Group
  is-surjective-map-hom-quotient-Group =
    is-surjective-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  surjection-hom-quotient-Group : type-Group G ↠ type-quotient-Group
  surjection-hom-quotient-Group =
    surjection-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  emb-subtype-quotient-Group :
    type-quotient-Group ↪ subtype (l1 ⊔ l2) (type-Group G)
  emb-subtype-quotient-Group =
    emb-subtype-set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  subtype-quotient-Group :
    type-quotient-Group → subtype (l1 ⊔ l2) (type-Group G)
  subtype-quotient-Group =
    subtype-set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  is-inhabited-subtype-quotient-Group :
    (x : type-quotient-Group) → is-inhabited-subtype (subtype-quotient-Group x)
  is-inhabited-subtype-quotient-Group =
    is-inhabited-subtype-set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  is-in-equivalence-class-quotient-Group :
    (x : type-quotient-Group) → type-Group G → UU (l1 ⊔ l2)
  is-in-equivalence-class-quotient-Group =
    is-in-equivalence-class-set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  is-prop-is-in-equivalence-class-quotient-Group :
    (x : type-quotient-Group) (g : type-Group G) →
    is-prop (is-in-equivalence-class-quotient-Group x g)
  is-prop-is-in-equivalence-class-quotient-Group =
    is-prop-is-in-equivalence-class-set-quotient
      ( eq-rel-congruence-Normal-Subgroup G H)

  is-in-equivalence-class-quotient-Group-Prop :
    (x : type-quotient-Group) → subtype (l1 ⊔ l2) (type-Group G)
  is-in-equivalence-class-quotient-Group-Prop =
    is-in-equivalence-class-set-quotient-Prop
      ( eq-rel-congruence-Normal-Subgroup G H)

  is-set-type-quotient-Group : is-set type-quotient-Group
  is-set-type-quotient-Group =
    is-set-set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  set-quotient-Group : Set (l1 ⊔ l2)
  set-quotient-Group = quotient-Set (eq-rel-congruence-Normal-Subgroup G H)

  unit-im-quotient-Group :
    hom-slice (prop-congruence-Normal-Subgroup G H) subtype-quotient-Group
  unit-im-quotient-Group =
    unit-im-set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  is-image-quotient-Group :
    {l : Level} →
    is-image l
      ( prop-congruence-Normal-Subgroup G H)
      ( emb-subtype-quotient-Group)
      ( unit-im-quotient-Group)
  is-image-quotient-Group =
    is-image-set-quotient (eq-rel-congruence-Normal-Subgroup G H)

  is-effective-map-hom-quotient-Group :
    is-effective (eq-rel-congruence-Normal-Subgroup G H) map-hom-quotient-Group
  is-effective-map-hom-quotient-Group =
    is-effective-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  apply-effectiveness-map-hom-quotient-Group :
    {x y : type-Group G} →
    map-hom-quotient-Group x ＝ map-hom-quotient-Group y →
    sim-congruence-Normal-Subgroup G H x y
  apply-effectiveness-map-hom-quotient-Group =
    apply-effectiveness-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  apply-effectiveness-map-hom-quotient-Group' :
    {x y : type-Group G} →
    sim-congruence-Normal-Subgroup G H x y →
    map-hom-quotient-Group x ＝ map-hom-quotient-Group y
  apply-effectiveness-map-hom-quotient-Group' =
    apply-effectiveness-quotient-map' (eq-rel-congruence-Normal-Subgroup G H)

  is-surjective-and-effective-map-hom-quotient-Group :
    is-surjective-and-effective
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( map-hom-quotient-Group)
  is-surjective-and-effective-map-hom-quotient-Group =
    is-surjective-and-effective-quotient-map
      ( eq-rel-congruence-Normal-Subgroup G H)

  reflecting-map-hom-quotient-Group :
    reflecting-map-Eq-Rel
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( type-quotient-Group)
  reflecting-map-hom-quotient-Group =
    reflecting-map-quotient-map (eq-rel-congruence-Normal-Subgroup G H)

  is-set-quotient-quotient-Group :
    {l : Level} →
    is-set-quotient l
      ( eq-rel-congruence-Normal-Subgroup G H)
      ( set-quotient-Group)
      ( reflecting-map-hom-quotient-Group)
  is-set-quotient-quotient-Group =
    is-set-quotient-set-quotient (eq-rel-congruence-Normal-Subgroup G H)
    
  unit-quotient-Group : type-quotient-Group
  unit-quotient-Group = map-hom-quotient-Group (unit-Group G)

  mul-quotient-Group :
    type-quotient-Group → type-quotient-Group → type-quotient-Group
  mul-quotient-Group = {!is-set-quotient-quotient-Group ?!}
```
