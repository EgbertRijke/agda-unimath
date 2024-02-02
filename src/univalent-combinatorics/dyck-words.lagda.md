# Dyck words

```agda
module univalent-combinatorics.dyck-words where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import lists.lists

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "Dyck word"}} is a [list](lists.lists.md) `w` of elements of the [standard 2-element set](univalent-combinatorics.standard-finite-sets.md), i.e., elements `0` and `1`, satisfying 2-conditions:

1. The word `w` is {{#concept "balanced" Disambiguation="Dyck word"}}, in the sense that there is a pairing of positions in the `w` such that for each pair `(i , j)` we have `i < j`, `wᵢ = 0`, `wⱼ = 1`, and the word

```text
  wᵢʲ := (wᵢ̨₊₁ ⋯ wⱼ₋₁)
```

of characters strictly between the `i`'th and `j`'th position is again a Dyck word.

Equivalently, a Dyck word contains an equal number of `0`'s and `1`'s and when reading it from left to right we never encounter more `1`'s than `0`'s.

The number of Dyck words of length `n` is the `n`-th [Catalan number](elementary-number-theory.catalan-numbers.md).

## Definitions

### Dyck words

```agda
data is-dyck-word : list (Fin 2) → UU lzero
is-dyck-word w = {!!}
```
