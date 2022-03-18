# Univalent mathematics in Agda

Welcome to the website of the `agda-unimath` formalization project.

[![build](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml/badge.svg?branch=master)](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml)

<pre class="Agda"><a id="281" class="Symbol">{-#</a> <a id="285" class="Keyword">OPTIONS</a> <a id="293" class="Pragma">--without-K</a> <a id="305" class="Pragma">--exact-split</a> <a id="319" class="Symbol">#-}</a>
</pre>
## Category theory

<pre class="Agda"><a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="category-theory.html" class="Module">category-theory</a>
<a id="384" class="Keyword">open</a> <a id="389" class="Keyword">import</a> <a id="396" href="category-theory.adjunctions-large-precategories.html" class="Module">category-theory.adjunctions-large-precategories</a>
<a id="444" class="Keyword">open</a> <a id="449" class="Keyword">import</a> <a id="456" href="category-theory.anafunctors.html" class="Module">category-theory.anafunctors</a>
<a id="484" class="Keyword">open</a> <a id="489" class="Keyword">import</a> <a id="496" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="523" class="Keyword">open</a> <a id="528" class="Keyword">import</a> <a id="535" href="category-theory.equivalences-categories.html" class="Module">category-theory.equivalences-categories</a>
<a id="575" class="Keyword">open</a> <a id="580" class="Keyword">import</a> <a id="587" href="category-theory.equivalences-large-precategories.html" class="Module">category-theory.equivalences-large-precategories</a>
<a id="636" class="Keyword">open</a> <a id="641" class="Keyword">import</a> <a id="648" href="category-theory.equivalences-precategories.html" class="Module">category-theory.equivalences-precategories</a>
<a id="691" class="Keyword">open</a> <a id="696" class="Keyword">import</a> <a id="703" href="category-theory.functors-categories.html" class="Module">category-theory.functors-categories</a>
<a id="739" class="Keyword">open</a> <a id="744" class="Keyword">import</a> <a id="751" href="category-theory.functors-large-precategories.html" class="Module">category-theory.functors-large-precategories</a>
<a id="796" class="Keyword">open</a> <a id="801" class="Keyword">import</a> <a id="808" href="category-theory.functors-precategories.html" class="Module">category-theory.functors-precategories</a>
<a id="847" class="Keyword">open</a> <a id="852" class="Keyword">import</a> <a id="859" href="category-theory.homotopies-natural-transformations-large-precategories.html" class="Module">category-theory.homotopies-natural-transformations-large-precategories</a>
<a id="930" class="Keyword">open</a> <a id="935" class="Keyword">import</a> <a id="942" href="category-theory.isomorphisms-categories.html" class="Module">category-theory.isomorphisms-categories</a>
<a id="982" class="Keyword">open</a> <a id="987" class="Keyword">import</a> <a id="994" href="category-theory.isomorphisms-large-precategories.html" class="Module">category-theory.isomorphisms-large-precategories</a>
<a id="1043" class="Keyword">open</a> <a id="1048" class="Keyword">import</a> <a id="1055" href="category-theory.isomorphisms-precategories.html" class="Module">category-theory.isomorphisms-precategories</a>
<a id="1098" class="Keyword">open</a> <a id="1103" class="Keyword">import</a> <a id="1110" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>
<a id="1143" class="Keyword">open</a> <a id="1148" class="Keyword">import</a> <a id="1155" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="1191" class="Keyword">open</a> <a id="1196" class="Keyword">import</a> <a id="1203" href="category-theory.monomorphisms-large-precategories.html" class="Module">category-theory.monomorphisms-large-precategories</a>
<a id="1253" class="Keyword">open</a> <a id="1258" class="Keyword">import</a> <a id="1265" href="category-theory.natural-isomorphisms-categories.html" class="Module">category-theory.natural-isomorphisms-categories</a>
<a id="1313" class="Keyword">open</a> <a id="1318" class="Keyword">import</a> <a id="1325" href="category-theory.natural-isomorphisms-large-precategories.html" class="Module">category-theory.natural-isomorphisms-large-precategories</a>
<a id="1382" class="Keyword">open</a> <a id="1387" class="Keyword">import</a> <a id="1394" href="category-theory.natural-isomorphisms-precategories.html" class="Module">category-theory.natural-isomorphisms-precategories</a>
<a id="1445" class="Keyword">open</a> <a id="1450" class="Keyword">import</a> <a id="1457" href="category-theory.natural-transformations-categories.html" class="Module">category-theory.natural-transformations-categories</a>
<a id="1508" class="Keyword">open</a> <a id="1513" class="Keyword">import</a> <a id="1520" href="category-theory.natural-transformations-large-precategories.html" class="Module">category-theory.natural-transformations-large-precategories</a>
<a id="1580" class="Keyword">open</a> <a id="1585" class="Keyword">import</a> <a id="1592" href="category-theory.natural-transformations-precategories.html" class="Module">category-theory.natural-transformations-precategories</a>
<a id="1646" class="Keyword">open</a> <a id="1651" class="Keyword">import</a> <a id="1658" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>
</pre>
## Elementary number theory

<pre class="Agda"><a id="1730" class="Keyword">open</a> <a id="1735" class="Keyword">import</a> <a id="1742" href="elementary-number-theory.html" class="Module">elementary-number-theory</a>
<a id="1767" class="Keyword">open</a> <a id="1772" class="Keyword">import</a> <a id="1779" href="elementary-number-theory.absolute-value-integers.html" class="Module">elementary-number-theory.absolute-value-integers</a>
<a id="1828" class="Keyword">open</a> <a id="1833" class="Keyword">import</a> <a id="1840" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a>
<a id="1883" class="Keyword">open</a> <a id="1888" class="Keyword">import</a> <a id="1895" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="1945" class="Keyword">open</a> <a id="1950" class="Keyword">import</a> <a id="1957" href="elementary-number-theory.binomial-coefficients.html" class="Module">elementary-number-theory.binomial-coefficients</a>
<a id="2004" class="Keyword">open</a> <a id="2009" class="Keyword">import</a> <a id="2016" href="elementary-number-theory.collatz-bijection.html" class="Module">elementary-number-theory.collatz-bijection</a>
<a id="2059" class="Keyword">open</a> <a id="2064" class="Keyword">import</a> <a id="2071" href="elementary-number-theory.collatz-conjecture.html" class="Module">elementary-number-theory.collatz-conjecture</a>
<a id="2115" class="Keyword">open</a> <a id="2120" class="Keyword">import</a> <a id="2127" href="elementary-number-theory.congruence-integers.html" class="Module">elementary-number-theory.congruence-integers</a>
<a id="2172" class="Keyword">open</a> <a id="2177" class="Keyword">import</a> <a id="2184" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a>
<a id="2236" class="Keyword">open</a> <a id="2241" class="Keyword">import</a> <a id="2248" href="elementary-number-theory.decidable-types.html" class="Module">elementary-number-theory.decidable-types</a>
<a id="2289" class="Keyword">open</a> <a id="2294" class="Keyword">import</a> <a id="2301" href="elementary-number-theory.difference-integers.html" class="Module">elementary-number-theory.difference-integers</a>
<a id="2346" class="Keyword">open</a> <a id="2351" class="Keyword">import</a> <a id="2358" href="elementary-number-theory.distance-integers.html" class="Module">elementary-number-theory.distance-integers</a>
<a id="2401" class="Keyword">open</a> <a id="2406" class="Keyword">import</a> <a id="2413" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a>
<a id="2463" class="Keyword">open</a> <a id="2468" class="Keyword">import</a> <a id="2475" href="elementary-number-theory.divisibility-integers.html" class="Module">elementary-number-theory.divisibility-integers</a>
<a id="2522" class="Keyword">open</a> <a id="2527" class="Keyword">import</a> <a id="2534" href="elementary-number-theory.divisibility-modular-arithmetic.html" class="Module">elementary-number-theory.divisibility-modular-arithmetic</a>
<a id="2591" class="Keyword">open</a> <a id="2596" class="Keyword">import</a> <a id="2603" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a>
<a id="2657" class="Keyword">open</a> <a id="2662" class="Keyword">import</a> <a id="2669" href="elementary-number-theory.divisibility-standard-finite-types.html" class="Module">elementary-number-theory.divisibility-standard-finite-types</a>
<a id="2729" class="Keyword">open</a> <a id="2734" class="Keyword">import</a> <a id="2741" href="elementary-number-theory.equality-integers.html" class="Module">elementary-number-theory.equality-integers</a>
<a id="2784" class="Keyword">open</a> <a id="2789" class="Keyword">import</a> <a id="2796" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a>
<a id="2846" class="Keyword">open</a> <a id="2851" class="Keyword">import</a> <a id="2858" href="elementary-number-theory.euclidean-division-natural-numbers.html" class="Module">elementary-number-theory.euclidean-division-natural-numbers</a>
<a id="2918" class="Keyword">open</a> <a id="2923" class="Keyword">import</a> <a id="2930" href="elementary-number-theory.eulers-totient-function.html" class="Module">elementary-number-theory.eulers-totient-function</a>
<a id="2979" class="Keyword">open</a> <a id="2984" class="Keyword">import</a> <a id="2991" href="elementary-number-theory.exponentiation-natural-numbers.html" class="Module">elementary-number-theory.exponentiation-natural-numbers</a>
<a id="3047" class="Keyword">open</a> <a id="3052" class="Keyword">import</a> <a id="3059" href="elementary-number-theory.factorials.html" class="Module">elementary-number-theory.factorials</a>
<a id="3095" class="Keyword">open</a> <a id="3100" class="Keyword">import</a> <a id="3107" href="elementary-number-theory.falling-factorials.html" class="Module">elementary-number-theory.falling-factorials</a>
<a id="3151" class="Keyword">open</a> <a id="3156" class="Keyword">import</a> <a id="3163" href="elementary-number-theory.fibonacci-sequence.html" class="Module">elementary-number-theory.fibonacci-sequence</a>
<a id="3207" class="Keyword">open</a> <a id="3212" class="Keyword">import</a> <a id="3219" href="elementary-number-theory.finitary-natural-numbers.html" class="Module">elementary-number-theory.finitary-natural-numbers</a>
<a id="3269" class="Keyword">open</a> <a id="3274" class="Keyword">import</a> <a id="3281" href="elementary-number-theory.finitely-cyclic-maps.html" class="Module">elementary-number-theory.finitely-cyclic-maps</a>
<a id="3327" class="Keyword">open</a> <a id="3332" class="Keyword">import</a> <a id="3339" href="elementary-number-theory.fractions.html" class="Module">elementary-number-theory.fractions</a>
<a id="3374" class="Keyword">open</a> <a id="3379" class="Keyword">import</a> <a id="3386" href="elementary-number-theory.goldbach-conjecture.html" class="Module">elementary-number-theory.goldbach-conjecture</a>
<a id="3431" class="Keyword">open</a> <a id="3436" class="Keyword">import</a> <a id="3443" href="elementary-number-theory.greatest-common-divisor-integers.html" class="Module">elementary-number-theory.greatest-common-divisor-integers</a>
<a id="3501" class="Keyword">open</a> <a id="3506" class="Keyword">import</a> <a id="3513" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a>
<a id="3578" class="Keyword">open</a> <a id="3583" class="Keyword">import</a> <a id="3590" href="elementary-number-theory.inequality-integers.html" class="Module">elementary-number-theory.inequality-integers</a>
<a id="3635" class="Keyword">open</a> <a id="3640" class="Keyword">import</a> <a id="3647" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a>
<a id="3699" class="Keyword">open</a> <a id="3704" class="Keyword">import</a> <a id="3711" href="elementary-number-theory.inequality-standard-finite-types.html" class="Module">elementary-number-theory.inequality-standard-finite-types</a>
<a id="3769" class="Keyword">open</a> <a id="3774" class="Keyword">import</a> <a id="3781" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a>
<a id="3827" class="Keyword">open</a> <a id="3832" class="Keyword">import</a> <a id="3839" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="3873" class="Keyword">open</a> <a id="3878" class="Keyword">import</a> <a id="3885" href="elementary-number-theory.iterating-functions.html" class="Module">elementary-number-theory.iterating-functions</a>
<a id="3930" class="Keyword">open</a> <a id="3935" class="Keyword">import</a> <a id="3942" href="elementary-number-theory.lower-bounds-natural-numbers.html" class="Module">elementary-number-theory.lower-bounds-natural-numbers</a>
<a id="3996" class="Keyword">open</a> <a id="4001" class="Keyword">import</a> <a id="4008" href="elementary-number-theory.mersenne-primes.html" class="Module">elementary-number-theory.mersenne-primes</a>
<a id="4049" class="Keyword">open</a> <a id="4054" class="Keyword">import</a> <a id="4061" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a>
<a id="4127" class="Keyword">open</a> <a id="4132" class="Keyword">import</a> <a id="4139" href="elementary-number-theory.modular-arithmetic.html" class="Module">elementary-number-theory.modular-arithmetic</a>
<a id="4183" class="Keyword">open</a> <a id="4188" class="Keyword">import</a> <a id="4195" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a>
<a id="4244" class="Keyword">open</a> <a id="4249" class="Keyword">import</a> <a id="4256" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a>
<a id="4312" class="Keyword">open</a> <a id="4317" class="Keyword">import</a> <a id="4324" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="4365" class="Keyword">open</a> <a id="4370" class="Keyword">import</a> <a id="4377" href="elementary-number-theory.ordinal-induction-natural-numbers.html" class="Module">elementary-number-theory.ordinal-induction-natural-numbers</a>
<a id="4436" class="Keyword">open</a> <a id="4441" class="Keyword">import</a> <a id="4448" href="elementary-number-theory.prime-numbers.html" class="Module">elementary-number-theory.prime-numbers</a>
<a id="4487" class="Keyword">open</a> <a id="4492" class="Keyword">import</a> <a id="4499" href="elementary-number-theory.products-of-natural-numbers.html" class="Module">elementary-number-theory.products-of-natural-numbers</a>
<a id="4552" class="Keyword">open</a> <a id="4557" class="Keyword">import</a> <a id="4564" href="elementary-number-theory.proper-divisors-natural-numbers.html" class="Module">elementary-number-theory.proper-divisors-natural-numbers</a>
<a id="4621" class="Keyword">open</a> <a id="4626" class="Keyword">import</a> <a id="4633" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a>
<a id="4675" class="Keyword">open</a> <a id="4680" class="Keyword">import</a> <a id="4687" href="elementary-number-theory.relatively-prime-integers.html" class="Module">elementary-number-theory.relatively-prime-integers</a>
<a id="4738" class="Keyword">open</a> <a id="4743" class="Keyword">import</a> <a id="4750" href="elementary-number-theory.relatively-prime-natural-numbers.html" class="Module">elementary-number-theory.relatively-prime-natural-numbers</a>
<a id="4808" class="Keyword">open</a> <a id="4813" class="Keyword">import</a> <a id="4820" href="elementary-number-theory.repeating-element-standard-finite-type.html" class="Module">elementary-number-theory.repeating-element-standard-finite-type</a>
<a id="4884" class="Keyword">open</a> <a id="4889" class="Keyword">import</a> <a id="4896" href="elementary-number-theory.retracts-of-natural-numbers.html" class="Module">elementary-number-theory.retracts-of-natural-numbers</a>
<a id="4949" class="Keyword">open</a> <a id="4954" class="Keyword">import</a> <a id="4961" href="elementary-number-theory.square-free-natural-numbers.html" class="Module">elementary-number-theory.square-free-natural-numbers</a>
<a id="5014" class="Keyword">open</a> <a id="5019" class="Keyword">import</a> <a id="5026" href="elementary-number-theory.stirling-numbers-of-the-second-kind.html" class="Module">elementary-number-theory.stirling-numbers-of-the-second-kind</a>
<a id="5087" class="Keyword">open</a> <a id="5092" class="Keyword">import</a> <a id="5099" href="elementary-number-theory.strong-induction-natural-numbers.html" class="Module">elementary-number-theory.strong-induction-natural-numbers</a>
<a id="5157" class="Keyword">open</a> <a id="5162" class="Keyword">import</a> <a id="5169" href="elementary-number-theory.sums-of-natural-numbers.html" class="Module">elementary-number-theory.sums-of-natural-numbers</a>
<a id="5218" class="Keyword">open</a> <a id="5223" class="Keyword">import</a> <a id="5230" href="elementary-number-theory.triangular-numbers.html" class="Module">elementary-number-theory.triangular-numbers</a>
<a id="5274" class="Keyword">open</a> <a id="5279" class="Keyword">import</a> <a id="5286" href="elementary-number-theory.twin-prime-conjecture.html" class="Module">elementary-number-theory.twin-prime-conjecture</a>
<a id="5333" class="Keyword">open</a> <a id="5338" class="Keyword">import</a> <a id="5345" href="elementary-number-theory.universal-property-natural-numbers.html" class="Module">elementary-number-theory.universal-property-natural-numbers</a>
<a id="5405" class="Keyword">open</a> <a id="5410" class="Keyword">import</a> <a id="5417" href="elementary-number-theory.upper-bounds-natural-numbers.html" class="Module">elementary-number-theory.upper-bounds-natural-numbers</a>
<a id="5471" class="Keyword">open</a> <a id="5476" class="Keyword">import</a> <a id="5483" href="elementary-number-theory.unit-elements-standard-finite-types.html" class="Module">elementary-number-theory.unit-elements-standard-finite-types</a>
<a id="5544" class="Keyword">open</a> <a id="5549" class="Keyword">import</a> <a id="5556" href="elementary-number-theory.unit-similarity-standard-finite-types.html" class="Module">elementary-number-theory.unit-similarity-standard-finite-types</a>
<a id="5619" class="Keyword">open</a> <a id="5624" class="Keyword">import</a> <a id="5631" href="elementary-number-theory.well-ordering-principle-natural-numbers.html" class="Module">elementary-number-theory.well-ordering-principle-natural-numbers</a>
<a id="5696" class="Keyword">open</a> <a id="5701" class="Keyword">import</a> <a id="5708" href="elementary-number-theory.well-ordering-principle-standard-finite-types.html" class="Module">elementary-number-theory.well-ordering-principle-standard-finite-types</a>
</pre>
## Finite group theory

<pre class="Agda"><a id="5816" class="Keyword">open</a> <a id="5821" class="Keyword">import</a> <a id="5828" href="finite-group-theory.html" class="Module">finite-group-theory</a>
<a id="5848" class="Keyword">open</a> <a id="5853" class="Keyword">import</a> <a id="5860" href="finite-group-theory.abstract-quaternion-group.html" class="Module">finite-group-theory.abstract-quaternion-group</a>
<a id="5906" class="Keyword">open</a> <a id="5911" class="Keyword">import</a> <a id="5918" href="finite-group-theory.concrete-quaternion-group.html" class="Module">finite-group-theory.concrete-quaternion-group</a>
<a id="5964" class="Keyword">open</a> <a id="5969" class="Keyword">import</a> <a id="5976" href="finite-group-theory.finite-groups.html" class="Module">finite-group-theory.finite-groups</a>
<a id="6010" class="Keyword">open</a> <a id="6015" class="Keyword">import</a> <a id="6022" href="finite-group-theory.orbits-permutations.html" class="Module">finite-group-theory.orbits-permutations</a>
<a id="6062" class="Keyword">open</a> <a id="6067" class="Keyword">import</a> <a id="6074" href="finite-group-theory.transpositions.html" class="Module">finite-group-theory.transpositions</a>
</pre>
## Foundation

<pre class="Agda"><a id="6137" class="Keyword">open</a> <a id="6142" class="Keyword">import</a> <a id="6149" href="foundation.html" class="Module">foundation</a>
<a id="6160" class="Keyword">open</a> <a id="6165" class="Keyword">import</a> <a id="6172" href="foundation.0-maps.html" class="Module">foundation.0-maps</a>
<a id="6190" class="Keyword">open</a> <a id="6195" class="Keyword">import</a> <a id="6202" href="foundation.1-types.html" class="Module">foundation.1-types</a>
<a id="6221" class="Keyword">open</a> <a id="6226" class="Keyword">import</a> <a id="6233" href="foundation.2-types.html" class="Module">foundation.2-types</a>
<a id="6252" class="Keyword">open</a> <a id="6257" class="Keyword">import</a> <a id="6264" href="foundation.algebras-polynomial-endofunctors.html" class="Module">foundation.algebras-polynomial-endofunctors</a>
<a id="6308" class="Keyword">open</a> <a id="6313" class="Keyword">import</a> <a id="6320" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="6345" class="Keyword">open</a> <a id="6350" class="Keyword">import</a> <a id="6357" href="foundation.axiom-of-choice.html" class="Module">foundation.axiom-of-choice</a>
<a id="6384" class="Keyword">open</a> <a id="6389" class="Keyword">import</a> <a id="6396" href="foundation.binary-embeddings.html" class="Module">foundation.binary-embeddings</a>
<a id="6425" class="Keyword">open</a> <a id="6430" class="Keyword">import</a> <a id="6437" href="foundation.binary-equivalences.html" class="Module">foundation.binary-equivalences</a>
<a id="6468" class="Keyword">open</a> <a id="6473" class="Keyword">import</a> <a id="6480" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="6508" class="Keyword">open</a> <a id="6513" class="Keyword">import</a> <a id="6520" href="foundation.boolean-reflection.html" class="Module">foundation.boolean-reflection</a>
<a id="6550" class="Keyword">open</a> <a id="6555" class="Keyword">import</a> <a id="6562" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="6582" class="Keyword">open</a> <a id="6587" class="Keyword">import</a> <a id="6594" href="foundation.cantors-diagonal-argument.html" class="Module">foundation.cantors-diagonal-argument</a>
<a id="6631" class="Keyword">open</a> <a id="6636" class="Keyword">import</a> <a id="6643" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="6678" class="Keyword">open</a> <a id="6683" class="Keyword">import</a> <a id="6690" href="foundation.choice-of-representatives-equivalence-relation.html" class="Module">foundation.choice-of-representatives-equivalence-relation</a>
<a id="6748" class="Keyword">open</a> <a id="6753" class="Keyword">import</a> <a id="6760" href="foundation.coherently-invertible-maps.html" class="Module">foundation.coherently-invertible-maps</a>
<a id="6798" class="Keyword">open</a> <a id="6803" class="Keyword">import</a> <a id="6810" href="foundation.commuting-squares.html" class="Module">foundation.commuting-squares</a>
<a id="6839" class="Keyword">open</a> <a id="6844" class="Keyword">import</a> <a id="6851" href="foundation.complements.html" class="Module">foundation.complements</a>
<a id="6874" class="Keyword">open</a> <a id="6879" class="Keyword">import</a> <a id="6886" href="foundation.conjunction.html" class="Module">foundation.conjunction</a>
<a id="6909" class="Keyword">open</a> <a id="6914" class="Keyword">import</a> <a id="6921" href="foundation.connected-components-universes.html" class="Module">foundation.connected-components-universes</a>
<a id="6963" class="Keyword">open</a> <a id="6968" class="Keyword">import</a> <a id="6975" href="foundation.connected-components.html" class="Module">foundation.connected-components</a>
<a id="7007" class="Keyword">open</a> <a id="7012" class="Keyword">import</a> <a id="7019" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="7046" class="Keyword">open</a> <a id="7051" class="Keyword">import</a> <a id="7058" href="foundation.constant-maps.html" class="Module">foundation.constant-maps</a>
<a id="7083" class="Keyword">open</a> <a id="7088" class="Keyword">import</a> <a id="7095" href="foundation.contractible-maps.html" class="Module">foundation.contractible-maps</a>
<a id="7124" class="Keyword">open</a> <a id="7129" class="Keyword">import</a> <a id="7136" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="7166" class="Keyword">open</a> <a id="7171" class="Keyword">import</a> <a id="7178" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="7205" class="Keyword">open</a> <a id="7210" class="Keyword">import</a> <a id="7217" href="foundation.coslice.html" class="Module">foundation.coslice</a>
<a id="7236" class="Keyword">open</a> <a id="7241" class="Keyword">import</a> <a id="7248" href="foundation.decidable-dependent-function-types.html" class="Module">foundation.decidable-dependent-function-types</a>
<a id="7294" class="Keyword">open</a> <a id="7299" class="Keyword">import</a> <a id="7306" href="foundation.decidable-dependent-pair-types.html" class="Module">foundation.decidable-dependent-pair-types</a>
<a id="7348" class="Keyword">open</a> <a id="7353" class="Keyword">import</a> <a id="7360" href="foundation.decidable-embeddings.html" class="Module">foundation.decidable-embeddings</a>
<a id="7392" class="Keyword">open</a> <a id="7397" class="Keyword">import</a> <a id="7404" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a>
<a id="7434" class="Keyword">open</a> <a id="7439" class="Keyword">import</a> <a id="7446" href="foundation.decidable-maps.html" class="Module">foundation.decidable-maps</a>
<a id="7472" class="Keyword">open</a> <a id="7477" class="Keyword">import</a> <a id="7484" href="foundation.decidable-propositions.html" class="Module">foundation.decidable-propositions</a>
<a id="7518" class="Keyword">open</a> <a id="7523" class="Keyword">import</a> <a id="7530" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="7560" class="Keyword">open</a> <a id="7565" class="Keyword">import</a> <a id="7572" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="7599" class="Keyword">open</a> <a id="7604" class="Keyword">import</a> <a id="7611" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="7643" class="Keyword">open</a> <a id="7648" class="Keyword">import</a> <a id="7655" href="foundation.diagonal-maps-of-types.html" class="Module">foundation.diagonal-maps-of-types</a>
<a id="7689" class="Keyword">open</a> <a id="7694" class="Keyword">import</a> <a id="7701" href="foundation.disjunction.html" class="Module">foundation.disjunction</a>
<a id="7724" class="Keyword">open</a> <a id="7729" class="Keyword">import</a> <a id="7736" href="foundation.distributivity-of-dependent-functions-over-coproduct-types.html" class="Module">foundation.distributivity-of-dependent-functions-over-coproduct-types</a>
<a id="7806" class="Keyword">open</a> <a id="7811" class="Keyword">import</a> <a id="7818" href="foundation.distributivity-of-dependent-functions-over-dependent-pairs.html" class="Module">foundation.distributivity-of-dependent-functions-over-dependent-pairs</a>
<a id="7888" class="Keyword">open</a> <a id="7893" class="Keyword">import</a> <a id="7900" href="foundation.double-negation.html" class="Module">foundation.double-negation</a>
<a id="7927" class="Keyword">open</a> <a id="7932" class="Keyword">import</a> <a id="7939" href="foundation.effective-maps-equivalence-relations.html" class="Module">foundation.effective-maps-equivalence-relations</a>
<a id="7987" class="Keyword">open</a> <a id="7992" class="Keyword">import</a> <a id="7999" href="foundation.elementhood-relation-w-types.html" class="Module">foundation.elementhood-relation-w-types</a>
<a id="8039" class="Keyword">open</a> <a id="8044" class="Keyword">import</a> <a id="8051" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="8073" class="Keyword">open</a> <a id="8078" class="Keyword">import</a> <a id="8085" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="8108" class="Keyword">open</a> <a id="8113" class="Keyword">import</a> <a id="8120" href="foundation.epimorphisms-with-respect-to-sets.html" class="Module">foundation.epimorphisms-with-respect-to-sets</a>
<a id="8165" class="Keyword">open</a> <a id="8170" class="Keyword">import</a> <a id="8177" href="foundation.equality-cartesian-product-types.html" class="Module">foundation.equality-cartesian-product-types</a>
<a id="8221" class="Keyword">open</a> <a id="8226" class="Keyword">import</a> <a id="8233" href="foundation.equality-coproduct-types.html" class="Module">foundation.equality-coproduct-types</a>
<a id="8269" class="Keyword">open</a> <a id="8274" class="Keyword">import</a> <a id="8281" href="foundation.equality-dependent-function-types.html" class="Module">foundation.equality-dependent-function-types</a>
<a id="8326" class="Keyword">open</a> <a id="8331" class="Keyword">import</a> <a id="8338" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="8379" class="Keyword">open</a> <a id="8384" class="Keyword">import</a> <a id="8391" href="foundation.equality-fibers-of-maps.html" class="Module">foundation.equality-fibers-of-maps</a>
<a id="8426" class="Keyword">open</a> <a id="8431" class="Keyword">import</a> <a id="8438" href="foundation.equivalence-classes.html" class="Module">foundation.equivalence-classes</a>
<a id="8469" class="Keyword">open</a> <a id="8474" class="Keyword">import</a> <a id="8481" href="foundation.equivalence-induction.html" class="Module">foundation.equivalence-induction</a>
<a id="8514" class="Keyword">open</a> <a id="8519" class="Keyword">import</a> <a id="8526" href="foundation.equivalence-relations.html" class="Module">foundation.equivalence-relations</a>
<a id="8559" class="Keyword">open</a> <a id="8564" class="Keyword">import</a> <a id="8571" href="foundation.equivalences-maybe.html" class="Module">foundation.equivalences-maybe</a>
<a id="8601" class="Keyword">open</a> <a id="8606" class="Keyword">import</a> <a id="8613" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="8637" class="Keyword">open</a> <a id="8642" class="Keyword">import</a> <a id="8649" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="8687" class="Keyword">open</a> <a id="8692" class="Keyword">import</a> <a id="8699" href="foundation.extensional-w-types.html" class="Module">foundation.extensional-w-types</a>
<a id="8730" class="Keyword">open</a> <a id="8735" class="Keyword">import</a> <a id="8742" href="foundation.faithful-maps.html" class="Module">foundation.faithful-maps</a>
<a id="8767" class="Keyword">open</a> <a id="8772" class="Keyword">import</a> <a id="8779" href="foundation.fiber-inclusions.html" class="Module">foundation.fiber-inclusions</a>
<a id="8807" class="Keyword">open</a> <a id="8812" class="Keyword">import</a> <a id="8819" href="foundation.fibered-maps.html" class="Module">foundation.fibered-maps</a>
<a id="8843" class="Keyword">open</a> <a id="8848" class="Keyword">import</a> <a id="8855" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="8881" class="Keyword">open</a> <a id="8886" class="Keyword">import</a> <a id="8893" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="8928" class="Keyword">open</a> <a id="8933" class="Keyword">import</a> <a id="8940" href="foundation.functions.html" class="Module">foundation.functions</a>
<a id="8961" class="Keyword">open</a> <a id="8966" class="Keyword">import</a> <a id="8973" href="foundation.functoriality-cartesian-product-types.html" class="Module">foundation.functoriality-cartesian-product-types</a>
<a id="9022" class="Keyword">open</a> <a id="9027" class="Keyword">import</a> <a id="9034" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="9075" class="Keyword">open</a> <a id="9080" class="Keyword">import</a> <a id="9087" href="foundation.functoriality-dependent-function-types.html" class="Module">foundation.functoriality-dependent-function-types</a>
<a id="9137" class="Keyword">open</a> <a id="9142" class="Keyword">import</a> <a id="9149" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="9195" class="Keyword">open</a> <a id="9200" class="Keyword">import</a> <a id="9207" href="foundation.functoriality-function-types.html" class="Module">foundation.functoriality-function-types</a>
<a id="9247" class="Keyword">open</a> <a id="9252" class="Keyword">import</a> <a id="9259" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="9309" class="Keyword">open</a> <a id="9314" class="Keyword">import</a> <a id="9321" href="foundation.functoriality-set-quotients.html" class="Module">foundation.functoriality-set-quotients</a>
<a id="9360" class="Keyword">open</a> <a id="9365" class="Keyword">import</a> <a id="9372" href="foundation.functoriality-set-truncation.html" class="Module">foundation.functoriality-set-truncation</a>
<a id="9412" class="Keyword">open</a> <a id="9417" class="Keyword">import</a> <a id="9424" href="foundation.functoriality-w-types.html" class="Module">foundation.functoriality-w-types</a>
<a id="9457" class="Keyword">open</a> <a id="9462" class="Keyword">import</a> <a id="9469" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="9518" class="Keyword">open</a> <a id="9523" class="Keyword">import</a> <a id="9530" href="foundation.global-choice.html" class="Module">foundation.global-choice</a>
<a id="9555" class="Keyword">open</a> <a id="9560" class="Keyword">import</a> <a id="9567" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="9589" class="Keyword">open</a> <a id="9594" class="Keyword">import</a> <a id="9601" href="foundation.identity-systems.html" class="Module">foundation.identity-systems</a>
<a id="9629" class="Keyword">open</a> <a id="9634" class="Keyword">import</a> <a id="9641" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="9667" class="Keyword">open</a> <a id="9672" class="Keyword">import</a> <a id="9679" href="foundation.images.html" class="Module">foundation.images</a>
<a id="9697" class="Keyword">open</a> <a id="9702" class="Keyword">import</a> <a id="9709" href="foundation.impredicative-encodings.html" class="Module">foundation.impredicative-encodings</a>
<a id="9744" class="Keyword">open</a> <a id="9749" class="Keyword">import</a> <a id="9756" href="foundation.indexed-w-types.html" class="Module">foundation.indexed-w-types</a>
<a id="9783" class="Keyword">open</a> <a id="9788" class="Keyword">import</a> <a id="9795" href="foundation.induction-principle-propositional-truncation.html" class="Module">foundation.induction-principle-propositional-truncation</a>
<a id="9851" class="Keyword">open</a> <a id="9856" class="Keyword">import</a> <a id="9863" href="foundation.induction-w-types.html" class="Module">foundation.induction-w-types</a>
<a id="9892" class="Keyword">open</a> <a id="9897" class="Keyword">import</a> <a id="9904" href="foundation.inequality-w-types.html" class="Module">foundation.inequality-w-types</a>
<a id="9934" class="Keyword">open</a> <a id="9939" class="Keyword">import</a> <a id="9946" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="9972" class="Keyword">open</a> <a id="9977" class="Keyword">import</a> <a id="9984" href="foundation.interchange-law.html" class="Module">foundation.interchange-law</a>
<a id="10011" class="Keyword">open</a> <a id="10016" class="Keyword">import</a> <a id="10023" href="foundation.involutions.html" class="Module">foundation.involutions</a>
<a id="10046" class="Keyword">open</a> <a id="10051" class="Keyword">import</a> <a id="10058" href="foundation.isolated-points.html" class="Module">foundation.isolated-points</a>
<a id="10085" class="Keyword">open</a> <a id="10090" class="Keyword">import</a> <a id="10097" href="foundation.isomorphisms-of-sets.html" class="Module">foundation.isomorphisms-of-sets</a>
<a id="10129" class="Keyword">open</a> <a id="10134" class="Keyword">import</a> <a id="10141" href="foundation.law-of-excluded-middle.html" class="Module">foundation.law-of-excluded-middle</a>
<a id="10175" class="Keyword">open</a> <a id="10180" class="Keyword">import</a> <a id="10187" href="foundation.lawveres-fixed-point-theorem.html" class="Module">foundation.lawveres-fixed-point-theorem</a>
<a id="10227" class="Keyword">open</a> <a id="10232" class="Keyword">import</a> <a id="10239" href="foundation.locally-small-types.html" class="Module">foundation.locally-small-types</a>
<a id="10270" class="Keyword">open</a> <a id="10275" class="Keyword">import</a> <a id="10282" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="10314" class="Keyword">open</a> <a id="10319" class="Keyword">import</a> <a id="10326" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="10343" class="Keyword">open</a> <a id="10348" class="Keyword">import</a> <a id="10355" href="foundation.mere-equality.html" class="Module">foundation.mere-equality</a>
<a id="10380" class="Keyword">open</a> <a id="10385" class="Keyword">import</a> <a id="10392" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="10421" class="Keyword">open</a> <a id="10426" class="Keyword">import</a> <a id="10433" href="foundation.monomorphisms.html" class="Module">foundation.monomorphisms</a>
<a id="10458" class="Keyword">open</a> <a id="10463" class="Keyword">import</a> <a id="10470" href="foundation.multisets.html" class="Module">foundation.multisets</a>
<a id="10491" class="Keyword">open</a> <a id="10496" class="Keyword">import</a> <a id="10503" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="10523" class="Keyword">open</a> <a id="10528" class="Keyword">import</a> <a id="10535" href="foundation.non-contractible-types.html" class="Module">foundation.non-contractible-types</a>
<a id="10569" class="Keyword">open</a> <a id="10574" class="Keyword">import</a> <a id="10581" href="foundation.path-algebra.html" class="Module">foundation.path-algebra</a>
<a id="10605" class="Keyword">open</a> <a id="10610" class="Keyword">import</a> <a id="10617" href="foundation.path-split-maps.html" class="Module">foundation.path-split-maps</a>
<a id="10644" class="Keyword">open</a> <a id="10649" class="Keyword">import</a> <a id="10656" href="foundation.polynomial-endofunctors.html" class="Module">foundation.polynomial-endofunctors</a>
<a id="10691" class="Keyword">open</a> <a id="10696" class="Keyword">import</a> <a id="10703" href="foundation.propositional-extensionality.html" class="Module">foundation.propositional-extensionality</a>
<a id="10743" class="Keyword">open</a> <a id="10748" class="Keyword">import</a> <a id="10755" href="foundation.propositional-maps.html" class="Module">foundation.propositional-maps</a>
<a id="10785" class="Keyword">open</a> <a id="10790" class="Keyword">import</a> <a id="10797" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="10834" class="Keyword">open</a> <a id="10839" class="Keyword">import</a> <a id="10846" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="10870" class="Keyword">open</a> <a id="10875" class="Keyword">import</a> <a id="10882" href="foundation.pullbacks.html" class="Module">foundation.pullbacks</a>
<a id="10903" class="Keyword">open</a> <a id="10908" class="Keyword">import</a> <a id="10915" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="10950" class="Keyword">open</a> <a id="10955" class="Keyword">import</a> <a id="10962" href="foundation.ranks-of-elements-w-types.html" class="Module">foundation.ranks-of-elements-w-types</a>
<a id="10999" class="Keyword">open</a> <a id="11004" class="Keyword">import</a> <a id="11011" href="foundation.reflecting-maps-equivalence-relations.html" class="Module">foundation.reflecting-maps-equivalence-relations</a>
<a id="11060" class="Keyword">open</a> <a id="11065" class="Keyword">import</a> <a id="11072" href="foundation.replacement.html" class="Module">foundation.replacement</a>
<a id="11095" class="Keyword">open</a> <a id="11100" class="Keyword">import</a> <a id="11107" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="11130" class="Keyword">open</a> <a id="11135" class="Keyword">import</a> <a id="11142" href="foundation.russells-paradox.html" class="Module">foundation.russells-paradox</a>
<a id="11170" class="Keyword">open</a> <a id="11175" class="Keyword">import</a> <a id="11182" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="11202" class="Keyword">open</a> <a id="11207" class="Keyword">import</a> <a id="11214" href="foundation.set-presented-types.html" class="Module">foundation.set-presented-types</a>
<a id="11245" class="Keyword">open</a> <a id="11250" class="Keyword">import</a> <a id="11257" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="11284" class="Keyword">open</a> <a id="11289" class="Keyword">import</a> <a id="11296" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="11312" class="Keyword">open</a> <a id="11317" class="Keyword">import</a> <a id="11324" href="foundation.singleton-induction.html" class="Module">foundation.singleton-induction</a>
<a id="11355" class="Keyword">open</a> <a id="11360" class="Keyword">import</a> <a id="11367" href="foundation.slice.html" class="Module">foundation.slice</a>
<a id="11384" class="Keyword">open</a> <a id="11389" class="Keyword">import</a> <a id="11396" href="foundation.small-maps.html" class="Module">foundation.small-maps</a>
<a id="11418" class="Keyword">open</a> <a id="11423" class="Keyword">import</a> <a id="11430" href="foundation.small-multisets.html" class="Module">foundation.small-multisets</a>
<a id="11457" class="Keyword">open</a> <a id="11462" class="Keyword">import</a> <a id="11469" href="foundation.small-types.html" class="Module">foundation.small-types</a>
<a id="11492" class="Keyword">open</a> <a id="11497" class="Keyword">import</a> <a id="11504" href="foundation.small-universes.html" class="Module">foundation.small-universes</a>
<a id="11531" class="Keyword">open</a> <a id="11536" class="Keyword">import</a> <a id="11543" href="foundation.split-surjective-maps.html" class="Module">foundation.split-surjective-maps</a>
<a id="11576" class="Keyword">open</a> <a id="11581" class="Keyword">import</a> <a id="11588" href="foundation.structure-identity-principle.html" class="Module">foundation.structure-identity-principle</a>
<a id="11628" class="Keyword">open</a> <a id="11633" class="Keyword">import</a> <a id="11640" href="foundation.structure.html" class="Module">foundation.structure</a>
<a id="11661" class="Keyword">open</a> <a id="11666" class="Keyword">import</a> <a id="11673" href="foundation.subterminal-types.html" class="Module">foundation.subterminal-types</a>
<a id="11702" class="Keyword">open</a> <a id="11707" class="Keyword">import</a> <a id="11714" href="foundation.subtype-identity-principle.html" class="Module">foundation.subtype-identity-principle</a>
<a id="11752" class="Keyword">open</a> <a id="11757" class="Keyword">import</a> <a id="11764" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="11784" class="Keyword">open</a> <a id="11789" class="Keyword">import</a> <a id="11796" href="foundation.subuniverses.html" class="Module">foundation.subuniverses</a>
<a id="11820" class="Keyword">open</a> <a id="11825" class="Keyword">import</a> <a id="11832" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="11859" class="Keyword">open</a> <a id="11864" class="Keyword">import</a> <a id="11871" href="foundation.truncated-equality.html" class="Module">foundation.truncated-equality</a>
<a id="11901" class="Keyword">open</a> <a id="11906" class="Keyword">import</a> <a id="11913" href="foundation.truncated-maps.html" class="Module">foundation.truncated-maps</a>
<a id="11939" class="Keyword">open</a> <a id="11944" class="Keyword">import</a> <a id="11951" href="foundation.truncated-types.html" class="Module">foundation.truncated-types</a>
<a id="11978" class="Keyword">open</a> <a id="11983" class="Keyword">import</a> <a id="11990" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="12019" class="Keyword">open</a> <a id="12024" class="Keyword">import</a> <a id="12031" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="12054" class="Keyword">open</a> <a id="12059" class="Keyword">import</a> <a id="12066" href="foundation.type-arithmetic-cartesian-product-types.html" class="Module">foundation.type-arithmetic-cartesian-product-types</a>
<a id="12117" class="Keyword">open</a> <a id="12122" class="Keyword">import</a> <a id="12129" href="foundation.type-arithmetic-coproduct-types.html" class="Module">foundation.type-arithmetic-coproduct-types</a>
<a id="12172" class="Keyword">open</a> <a id="12177" class="Keyword">import</a> <a id="12184" href="foundation.type-arithmetic-dependent-pair-types.html" class="Module">foundation.type-arithmetic-dependent-pair-types</a>
<a id="12232" class="Keyword">open</a> <a id="12237" class="Keyword">import</a> <a id="12244" href="foundation.type-arithmetic-empty-type.html" class="Module">foundation.type-arithmetic-empty-type</a>
<a id="12282" class="Keyword">open</a> <a id="12287" class="Keyword">import</a> <a id="12294" href="foundation.type-arithmetic-unit-type.html" class="Module">foundation.type-arithmetic-unit-type</a>
<a id="12331" class="Keyword">open</a> <a id="12336" class="Keyword">import</a> <a id="12343" href="foundation.uniqueness-image.html" class="Module">foundation.uniqueness-image</a>
<a id="12371" class="Keyword">open</a> <a id="12376" class="Keyword">import</a> <a id="12383" href="foundation.uniqueness-set-quotients.html" class="Module">foundation.uniqueness-set-quotients</a>
<a id="12419" class="Keyword">open</a> <a id="12424" class="Keyword">import</a> <a id="12431" href="foundation.uniqueness-set-truncations.html" class="Module">foundation.uniqueness-set-truncations</a>
<a id="12469" class="Keyword">open</a> <a id="12474" class="Keyword">import</a> <a id="12481" href="foundation.uniqueness-truncation.html" class="Module">foundation.uniqueness-truncation</a>
<a id="12514" class="Keyword">open</a> <a id="12519" class="Keyword">import</a> <a id="12526" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="12547" class="Keyword">open</a> <a id="12552" class="Keyword">import</a> <a id="12559" href="foundation.univalence-implies-function-extensionality.html" class="Module">foundation.univalence-implies-function-extensionality</a>
<a id="12613" class="Keyword">open</a> <a id="12618" class="Keyword">import</a> <a id="12625" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="12647" class="Keyword">open</a> <a id="12652" class="Keyword">import</a> <a id="12659" href="foundation.univalent-type-families.html" class="Module">foundation.univalent-type-families</a>
<a id="12694" class="Keyword">open</a> <a id="12699" class="Keyword">import</a> <a id="12706" href="foundation.universal-multiset.html" class="Module">foundation.universal-multiset</a>
<a id="12736" class="Keyword">open</a> <a id="12741" class="Keyword">import</a> <a id="12748" href="foundation.universal-property-booleans.html" class="Module">foundation.universal-property-booleans</a>
<a id="12787" class="Keyword">open</a> <a id="12792" class="Keyword">import</a> <a id="12799" href="foundation.universal-property-cartesian-product-types.html" class="Module">foundation.universal-property-cartesian-product-types</a>
<a id="12853" class="Keyword">open</a> <a id="12858" class="Keyword">import</a> <a id="12865" href="foundation.universal-property-coproduct-types.html" class="Module">foundation.universal-property-coproduct-types</a>
<a id="12911" class="Keyword">open</a> <a id="12916" class="Keyword">import</a> <a id="12923" href="foundation.universal-property-dependent-pair-types.html" class="Module">foundation.universal-property-dependent-pair-types</a>
<a id="12974" class="Keyword">open</a> <a id="12979" class="Keyword">import</a> <a id="12986" href="foundation.universal-property-empty-type.html" class="Module">foundation.universal-property-empty-type</a>
<a id="13027" class="Keyword">open</a> <a id="13032" class="Keyword">import</a> <a id="13039" href="foundation.universal-property-fiber-products.html" class="Module">foundation.universal-property-fiber-products</a>
<a id="13084" class="Keyword">open</a> <a id="13089" class="Keyword">import</a> <a id="13096" href="foundation.universal-property-identity-types.html" class="Module">foundation.universal-property-identity-types</a>
<a id="13141" class="Keyword">open</a> <a id="13146" class="Keyword">import</a> <a id="13153" href="foundation.universal-property-image.html" class="Module">foundation.universal-property-image</a>
<a id="13189" class="Keyword">open</a> <a id="13194" class="Keyword">import</a> <a id="13201" href="foundation.universal-property-maybe.html" class="Module">foundation.universal-property-maybe</a>
<a id="13237" class="Keyword">open</a> <a id="13242" class="Keyword">import</a> <a id="13249" href="foundation.universal-property-propositional-truncation-into-sets.html" class="Module">foundation.universal-property-propositional-truncation-into-sets</a>
<a id="13314" class="Keyword">open</a> <a id="13319" class="Keyword">import</a> <a id="13326" href="foundation.universal-property-propositional-truncation.html" class="Module">foundation.universal-property-propositional-truncation</a>
<a id="13381" class="Keyword">open</a> <a id="13386" class="Keyword">import</a> <a id="13393" href="foundation.universal-property-pullbacks.html" class="Module">foundation.universal-property-pullbacks</a>
<a id="13433" class="Keyword">open</a> <a id="13438" class="Keyword">import</a> <a id="13445" href="foundation.universal-property-set-quotients.html" class="Module">foundation.universal-property-set-quotients</a>
<a id="13489" class="Keyword">open</a> <a id="13494" class="Keyword">import</a> <a id="13501" href="foundation.universal-property-set-truncation.html" class="Module">foundation.universal-property-set-truncation</a>
<a id="13546" class="Keyword">open</a> <a id="13551" class="Keyword">import</a> <a id="13558" href="foundation.universal-property-truncation.html" class="Module">foundation.universal-property-truncation</a>
<a id="13599" class="Keyword">open</a> <a id="13604" class="Keyword">import</a> <a id="13611" href="foundation.universal-property-unit-type.html" class="Module">foundation.universal-property-unit-type</a>
<a id="13651" class="Keyword">open</a> <a id="13656" class="Keyword">import</a> <a id="13663" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="13690" class="Keyword">open</a> <a id="13695" class="Keyword">import</a> <a id="13702" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>
<a id="13729" class="Keyword">open</a> <a id="13734" class="Keyword">import</a> <a id="13741" href="foundation.w-types.html" class="Module">foundation.w-types</a>
<a id="13760" class="Keyword">open</a> <a id="13765" class="Keyword">import</a> <a id="13772" href="foundation.weak-function-extensionality.html" class="Module">foundation.weak-function-extensionality</a>
<a id="13812" class="Keyword">open</a> <a id="13817" class="Keyword">import</a> <a id="13824" href="foundation.weakly-constant-maps.html" class="Module">foundation.weakly-constant-maps</a>
</pre>
## Foundation Core

<pre class="Agda"><a id="13889" class="Keyword">open</a> <a id="13894" class="Keyword">import</a> <a id="13901" href="foundation-core.0-maps.html" class="Module">foundation-core.0-maps</a>
<a id="13924" class="Keyword">open</a> <a id="13929" class="Keyword">import</a> <a id="13936" href="foundation-core.1-types.html" class="Module">foundation-core.1-types</a>
<a id="13960" class="Keyword">open</a> <a id="13965" class="Keyword">import</a> <a id="13972" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="14012" class="Keyword">open</a> <a id="14017" class="Keyword">import</a> <a id="14024" href="foundation-core.coherently-invertible-maps.html" class="Module">foundation-core.coherently-invertible-maps</a>
<a id="14067" class="Keyword">open</a> <a id="14072" class="Keyword">import</a> <a id="14079" href="foundation-core.commuting-squares.html" class="Module">foundation-core.commuting-squares</a>
<a id="14113" class="Keyword">open</a> <a id="14118" class="Keyword">import</a> <a id="14125" href="foundation-core.constant-maps.html" class="Module">foundation-core.constant-maps</a>
<a id="14155" class="Keyword">open</a> <a id="14160" class="Keyword">import</a> <a id="14167" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="14201" class="Keyword">open</a> <a id="14206" class="Keyword">import</a> <a id="14213" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="14248" class="Keyword">open</a> <a id="14253" class="Keyword">import</a> <a id="14260" href="foundation-core.dependent-pair-types.html" class="Module">foundation-core.dependent-pair-types</a>
<a id="14297" class="Keyword">open</a> <a id="14302" class="Keyword">import</a> <a id="14309" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="14336" class="Keyword">open</a> <a id="14341" class="Keyword">import</a> <a id="14348" href="foundation-core.empty-types.html" class="Module">foundation-core.empty-types</a>
<a id="14376" class="Keyword">open</a> <a id="14381" class="Keyword">import</a> <a id="14388" href="foundation-core.equality-cartesian-product-types.html" class="Module">foundation-core.equality-cartesian-product-types</a>
<a id="14437" class="Keyword">open</a> <a id="14442" class="Keyword">import</a> <a id="14449" href="foundation-core.equality-dependent-pair-types.html" class="Module">foundation-core.equality-dependent-pair-types</a>
<a id="14495" class="Keyword">open</a> <a id="14500" class="Keyword">import</a> <a id="14507" href="foundation-core.equality-fibers-of-maps.html" class="Module">foundation-core.equality-fibers-of-maps</a>
<a id="14547" class="Keyword">open</a> <a id="14552" class="Keyword">import</a> <a id="14559" href="foundation-core.equivalence-induction.html" class="Module">foundation-core.equivalence-induction</a>
<a id="14597" class="Keyword">open</a> <a id="14602" class="Keyword">import</a> <a id="14609" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="14638" class="Keyword">open</a> <a id="14643" class="Keyword">import</a> <a id="14650" href="foundation-core.faithful-maps.html" class="Module">foundation-core.faithful-maps</a>
<a id="14680" class="Keyword">open</a> <a id="14685" class="Keyword">import</a> <a id="14692" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
<a id="14723" class="Keyword">open</a> <a id="14728" class="Keyword">import</a> <a id="14735" href="foundation-core.functions.html" class="Module">foundation-core.functions</a>
<a id="14761" class="Keyword">open</a> <a id="14766" class="Keyword">import</a> <a id="14773" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
<a id="14824" class="Keyword">open</a> <a id="14829" class="Keyword">import</a> <a id="14836" href="foundation-core.fundamental-theorem-of-identity-types.html" class="Module">foundation-core.fundamental-theorem-of-identity-types</a>
<a id="14890" class="Keyword">open</a> <a id="14895" class="Keyword">import</a> <a id="14902" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="14929" class="Keyword">open</a> <a id="14934" class="Keyword">import</a> <a id="14941" href="foundation-core.identity-systems.html" class="Module">foundation-core.identity-systems</a>
<a id="14974" class="Keyword">open</a> <a id="14979" class="Keyword">import</a> <a id="14986" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="15017" class="Keyword">open</a> <a id="15022" class="Keyword">import</a> <a id="15029" href="foundation-core.logical-equivalences.html" class="Module">foundation-core.logical-equivalences</a>
<a id="15066" class="Keyword">open</a> <a id="15071" class="Keyword">import</a> <a id="15078" href="foundation-core.negation.html" class="Module">foundation-core.negation</a>
<a id="15103" class="Keyword">open</a> <a id="15108" class="Keyword">import</a> <a id="15115" href="foundation-core.path-split-maps.html" class="Module">foundation-core.path-split-maps</a>
<a id="15147" class="Keyword">open</a> <a id="15152" class="Keyword">import</a> <a id="15159" href="foundation-core.propositional-maps.html" class="Module">foundation-core.propositional-maps</a>
<a id="15194" class="Keyword">open</a> <a id="15199" class="Keyword">import</a> <a id="15206" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="15235" class="Keyword">open</a> <a id="15240" class="Keyword">import</a> <a id="15247" href="foundation-core.retractions.html" class="Module">foundation-core.retractions</a>
<a id="15275" class="Keyword">open</a> <a id="15280" class="Keyword">import</a> <a id="15287" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
<a id="15312" class="Keyword">open</a> <a id="15317" class="Keyword">import</a> <a id="15324" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>
<a id="15345" class="Keyword">open</a> <a id="15350" class="Keyword">import</a> <a id="15357" href="foundation-core.singleton-induction.html" class="Module">foundation-core.singleton-induction</a>
<a id="15393" class="Keyword">open</a> <a id="15398" class="Keyword">import</a> <a id="15405" href="foundation-core.subtype-identity-principle.html" class="Module">foundation-core.subtype-identity-principle</a>
<a id="15448" class="Keyword">open</a> <a id="15453" class="Keyword">import</a> <a id="15460" href="foundation-core.subtypes.html" class="Module">foundation-core.subtypes</a>
<a id="15485" class="Keyword">open</a> <a id="15490" class="Keyword">import</a> <a id="15497" href="foundation-core.truncated-maps.html" class="Module">foundation-core.truncated-maps</a>
<a id="15528" class="Keyword">open</a> <a id="15533" class="Keyword">import</a> <a id="15540" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="15572" class="Keyword">open</a> <a id="15577" class="Keyword">import</a> <a id="15584" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
<a id="15618" class="Keyword">open</a> <a id="15623" class="Keyword">import</a> <a id="15630" href="foundation-core.type-arithmetic-cartesian-product-types.html" class="Module">foundation-core.type-arithmetic-cartesian-product-types</a>
<a id="15686" class="Keyword">open</a> <a id="15691" class="Keyword">import</a> <a id="15698" href="foundation-core.type-arithmetic-dependent-pair-types.html" class="Module">foundation-core.type-arithmetic-dependent-pair-types</a>
<a id="15751" class="Keyword">open</a> <a id="15756" class="Keyword">import</a> <a id="15763" href="foundation-core.univalence.html" class="Module">foundation-core.univalence</a>
<a id="15790" class="Keyword">open</a> <a id="15795" class="Keyword">import</a> <a id="15802" href="foundation-core.universe-levels.html" class="Module">foundation-core.universe-levels</a>
</pre>
## Graph theory

<pre class="Agda"><a id="15864" class="Keyword">open</a> <a id="15869" class="Keyword">import</a> <a id="15876" href="graph-theory.html" class="Module">graph-theory</a>
<a id="15889" class="Keyword">open</a> <a id="15894" class="Keyword">import</a> <a id="15901" href="graph-theory.connected-undirected-graphs.html" class="Module">graph-theory.connected-undirected-graphs</a>
<a id="15942" class="Keyword">open</a> <a id="15947" class="Keyword">import</a> <a id="15954" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="15983" class="Keyword">open</a> <a id="15988" class="Keyword">import</a> <a id="15995" href="graph-theory.edge-coloured-undirected-graphs.html" class="Module">graph-theory.edge-coloured-undirected-graphs</a>
<a id="16040" class="Keyword">open</a> <a id="16045" class="Keyword">import</a> <a id="16052" href="graph-theory.equivalences-undirected-graphs.html" class="Module">graph-theory.equivalences-undirected-graphs</a>
<a id="16096" class="Keyword">open</a> <a id="16101" class="Keyword">import</a> <a id="16108" href="graph-theory.finite-graphs.html" class="Module">graph-theory.finite-graphs</a>
<a id="16135" class="Keyword">open</a> <a id="16140" class="Keyword">import</a> <a id="16147" href="graph-theory.incidence-undirected-graphs.html" class="Module">graph-theory.incidence-undirected-graphs</a>
<a id="16188" class="Keyword">open</a> <a id="16193" class="Keyword">import</a> <a id="16200" href="graph-theory.mere-equivalences-undirected-graphs.html" class="Module">graph-theory.mere-equivalences-undirected-graphs</a>
<a id="16249" class="Keyword">open</a> <a id="16254" class="Keyword">import</a> <a id="16261" href="graph-theory.morphisms-undirected-graphs.html" class="Module">graph-theory.morphisms-undirected-graphs</a>
<a id="16302" class="Keyword">open</a> <a id="16307" class="Keyword">import</a> <a id="16314" href="graph-theory.orientations-undirected-graphs.html" class="Module">graph-theory.orientations-undirected-graphs</a>
<a id="16358" class="Keyword">open</a> <a id="16363" class="Keyword">import</a> <a id="16370" href="graph-theory.paths-undirected-graphs.html" class="Module">graph-theory.paths-undirected-graphs</a>
<a id="16407" class="Keyword">open</a> <a id="16412" class="Keyword">import</a> <a id="16419" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>
<a id="16441" class="Keyword">open</a> <a id="16446" class="Keyword">import</a> <a id="16453" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
<a id="16483" class="Keyword">open</a> <a id="16488" class="Keyword">import</a> <a id="16495" href="graph-theory.simple-undirected-graphs.html" class="Module">graph-theory.simple-undirected-graphs</a>
<a id="16533" class="Keyword">open</a> <a id="16538" class="Keyword">import</a> <a id="16545" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
## Group theory

<pre class="Agda"><a id="16606" class="Keyword">open</a> <a id="16611" class="Keyword">import</a> <a id="16618" href="group-theory.html" class="Module">group-theory</a>
<a id="16631" class="Keyword">open</a> <a id="16636" class="Keyword">import</a> <a id="16643" href="group-theory.abstract-abelian-groups.html" class="Module">group-theory.abstract-abelian-groups</a>
<a id="16680" class="Keyword">open</a> <a id="16685" class="Keyword">import</a> <a id="16692" href="group-theory.abstract-abelian-subgroups.html" class="Module">group-theory.abstract-abelian-subgroups</a>
<a id="16732" class="Keyword">open</a> <a id="16737" class="Keyword">import</a> <a id="16744" href="group-theory.abstract-group-actions.html" class="Module">group-theory.abstract-group-actions</a>
<a id="16780" class="Keyword">open</a> <a id="16785" class="Keyword">import</a> <a id="16792" href="group-theory.abstract-group-torsors.html" class="Module">group-theory.abstract-group-torsors</a>
<a id="16828" class="Keyword">open</a> <a id="16833" class="Keyword">import</a> <a id="16840" href="group-theory.abstract-groups.html" class="Module">group-theory.abstract-groups</a>
<a id="16869" class="Keyword">open</a> <a id="16874" class="Keyword">import</a> <a id="16881" href="group-theory.abstract-subgroups.html" class="Module">group-theory.abstract-subgroups</a>
<a id="16913" class="Keyword">open</a> <a id="16918" class="Keyword">import</a> <a id="16925" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="16961" class="Keyword">open</a> <a id="16966" class="Keyword">import</a> <a id="16973" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="17002" class="Keyword">open</a> <a id="17007" class="Keyword">import</a> <a id="17014" href="group-theory.concrete-subgroups.html" class="Module">group-theory.concrete-subgroups</a>
<a id="17046" class="Keyword">open</a> <a id="17051" class="Keyword">import</a> <a id="17058" href="group-theory.examples-higher-groups.html" class="Module">group-theory.examples-higher-groups</a>
<a id="17094" class="Keyword">open</a> <a id="17099" class="Keyword">import</a> <a id="17106" href="group-theory.furstenberg-groups.html" class="Module">group-theory.furstenberg-groups</a>
<a id="17138" class="Keyword">open</a> <a id="17143" class="Keyword">import</a> <a id="17150" href="group-theory.higher-groups.html" class="Module">group-theory.higher-groups</a>
<a id="17177" class="Keyword">open</a> <a id="17182" class="Keyword">import</a> <a id="17189" href="group-theory.sheargroups.html" class="Module">group-theory.sheargroups</a>
</pre>
## Linear algebra

<pre class="Agda"><a id="17246" class="Keyword">open</a> <a id="17251" class="Keyword">import</a> <a id="17258" href="linear-algebra.html" class="Module">linear-algebra</a>
<a id="17273" class="Keyword">open</a> <a id="17278" class="Keyword">import</a> <a id="17285" href="linear-algebra.matrices.html" class="Module">linear-algebra.matrices</a>
<a id="17309" class="Keyword">open</a> <a id="17314" class="Keyword">import</a> <a id="17321" href="linear-algebra.vectors.html" class="Module">linear-algebra.vectors</a>
</pre>
## Order theory

<pre class="Agda"><a id="17374" class="Keyword">open</a> <a id="17379" class="Keyword">import</a> <a id="17386" href="order-theory.html" class="Module">order-theory</a>
<a id="17399" class="Keyword">open</a> <a id="17404" class="Keyword">import</a> <a id="17411" href="order-theory.chains-posets.html" class="Module">order-theory.chains-posets</a>
<a id="17438" class="Keyword">open</a> <a id="17443" class="Keyword">import</a> <a id="17450" href="order-theory.chains-preorders.html" class="Module">order-theory.chains-preorders</a>
<a id="17480" class="Keyword">open</a> <a id="17485" class="Keyword">import</a> <a id="17492" href="order-theory.decidable-subposets.html" class="Module">order-theory.decidable-subposets</a>
<a id="17525" class="Keyword">open</a> <a id="17530" class="Keyword">import</a> <a id="17537" href="order-theory.decidable-subpreorders.html" class="Module">order-theory.decidable-subpreorders</a>
<a id="17573" class="Keyword">open</a> <a id="17578" class="Keyword">import</a> <a id="17585" href="order-theory.finite-posets.html" class="Module">order-theory.finite-posets</a>
<a id="17612" class="Keyword">open</a> <a id="17617" class="Keyword">import</a> <a id="17624" href="order-theory.finite-preorders.html" class="Module">order-theory.finite-preorders</a>
<a id="17654" class="Keyword">open</a> <a id="17659" class="Keyword">import</a> <a id="17666" href="order-theory.finitely-graded-posets.html" class="Module">order-theory.finitely-graded-posets</a>
<a id="17702" class="Keyword">open</a> <a id="17707" class="Keyword">import</a> <a id="17714" href="order-theory.interval-subposets.html" class="Module">order-theory.interval-subposets</a>
<a id="17746" class="Keyword">open</a> <a id="17751" class="Keyword">import</a> <a id="17758" href="order-theory.largest-elements-posets.html" class="Module">order-theory.largest-elements-posets</a>
<a id="17795" class="Keyword">open</a> <a id="17800" class="Keyword">import</a> <a id="17807" href="order-theory.largest-elements-preorders.html" class="Module">order-theory.largest-elements-preorders</a>
<a id="17847" class="Keyword">open</a> <a id="17852" class="Keyword">import</a> <a id="17859" href="order-theory.least-elements-posets.html" class="Module">order-theory.least-elements-posets</a>
<a id="17894" class="Keyword">open</a> <a id="17899" class="Keyword">import</a> <a id="17906" href="order-theory.least-elements-preorders.html" class="Module">order-theory.least-elements-preorders</a>
<a id="17944" class="Keyword">open</a> <a id="17949" class="Keyword">import</a> <a id="17956" href="order-theory.locally-finite-posets.html" class="Module">order-theory.locally-finite-posets</a>
<a id="17991" class="Keyword">open</a> <a id="17996" class="Keyword">import</a> <a id="18003" href="order-theory.maximal-chains-posets.html" class="Module">order-theory.maximal-chains-posets</a>
<a id="18038" class="Keyword">open</a> <a id="18043" class="Keyword">import</a> <a id="18050" href="order-theory.maximal-chains-preorders.html" class="Module">order-theory.maximal-chains-preorders</a>
<a id="18088" class="Keyword">open</a> <a id="18093" class="Keyword">import</a> <a id="18100" href="order-theory.planar-binary-trees.html" class="Module">order-theory.planar-binary-trees</a>
<a id="18133" class="Keyword">open</a> <a id="18138" class="Keyword">import</a> <a id="18145" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="18165" class="Keyword">open</a> <a id="18170" class="Keyword">import</a> <a id="18177" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
<a id="18200" class="Keyword">open</a> <a id="18205" class="Keyword">import</a> <a id="18212" href="order-theory.subposets.html" class="Module">order-theory.subposets</a>
<a id="18235" class="Keyword">open</a> <a id="18240" class="Keyword">import</a> <a id="18247" href="order-theory.subpreorders.html" class="Module">order-theory.subpreorders</a>
<a id="18273" class="Keyword">open</a> <a id="18278" class="Keyword">import</a> <a id="18285" href="order-theory.total-posets.html" class="Module">order-theory.total-posets</a>
<a id="18311" class="Keyword">open</a> <a id="18316" class="Keyword">import</a> <a id="18323" href="order-theory.total-preorders.html" class="Module">order-theory.total-preorders</a>
</pre>
## Polytopes

<pre class="Agda"><a id="18379" class="Keyword">open</a> <a id="18384" class="Keyword">import</a> <a id="18391" href="polytopes.html" class="Module">polytopes</a>
<a id="18401" class="Keyword">open</a> <a id="18406" class="Keyword">import</a> <a id="18413" href="polytopes.abstract-polytopes.html" class="Module">polytopes.abstract-polytopes</a>
</pre>
## Ring theory

<pre class="Agda"><a id="18471" class="Keyword">open</a> <a id="18476" class="Keyword">import</a> <a id="18483" href="ring-theory.html" class="Module">ring-theory</a>
<a id="18495" class="Keyword">open</a> <a id="18500" class="Keyword">import</a> <a id="18507" href="ring-theory.eisenstein-integers.html" class="Module">ring-theory.eisenstein-integers</a>
<a id="18539" class="Keyword">open</a> <a id="18544" class="Keyword">import</a> <a id="18551" href="ring-theory.gaussian-integers.html" class="Module">ring-theory.gaussian-integers</a>
<a id="18581" class="Keyword">open</a> <a id="18586" class="Keyword">import</a> <a id="18593" href="ring-theory.ideals.html" class="Module">ring-theory.ideals</a>
<a id="18612" class="Keyword">open</a> <a id="18617" class="Keyword">import</a> <a id="18624" href="ring-theory.localizations-rings.html" class="Module">ring-theory.localizations-rings</a>
<a id="18656" class="Keyword">open</a> <a id="18661" class="Keyword">import</a> <a id="18668" href="ring-theory.rings-with-properties.html" class="Module">ring-theory.rings-with-properties</a>
<a id="18702" class="Keyword">open</a> <a id="18707" class="Keyword">import</a> <a id="18714" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
## Synthetic homotopy theory

<pre class="Agda"><a id="18775" class="Keyword">open</a> <a id="18780" class="Keyword">import</a> <a id="18787" href="synthetic-homotopy-theory.html" class="Module">synthetic-homotopy-theory</a>
<a id="18813" class="Keyword">open</a> <a id="18818" class="Keyword">import</a> <a id="18825" href="synthetic-homotopy-theory.23-pullbacks.html" class="Module">synthetic-homotopy-theory.23-pullbacks</a>
<a id="18864" class="Keyword">open</a> <a id="18869" class="Keyword">import</a> <a id="18876" href="synthetic-homotopy-theory.24-pushouts.html" class="Module">synthetic-homotopy-theory.24-pushouts</a>
<a id="18914" class="Keyword">open</a> <a id="18919" class="Keyword">import</a> <a id="18926" href="synthetic-homotopy-theory.25-cubical-diagrams.html" class="Module">synthetic-homotopy-theory.25-cubical-diagrams</a>
<a id="18972" class="Keyword">open</a> <a id="18977" class="Keyword">import</a> <a id="18984" href="synthetic-homotopy-theory.26-descent.html" class="Module">synthetic-homotopy-theory.26-descent</a>
<a id="19021" class="Keyword">open</a> <a id="19026" class="Keyword">import</a> <a id="19033" href="synthetic-homotopy-theory.26-id-pushout.html" class="Module">synthetic-homotopy-theory.26-id-pushout</a>
<a id="19073" class="Keyword">open</a> <a id="19078" class="Keyword">import</a> <a id="19085" href="synthetic-homotopy-theory.27-sequences.html" class="Module">synthetic-homotopy-theory.27-sequences</a>
<a id="19124" class="Keyword">open</a> <a id="19129" class="Keyword">import</a> <a id="19136" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
<a id="19169" class="Keyword">open</a> <a id="19174" class="Keyword">import</a> <a id="19181" href="synthetic-homotopy-theory.cyclic-types.html" class="Module">synthetic-homotopy-theory.cyclic-types</a>
<a id="19220" class="Keyword">open</a> <a id="19225" class="Keyword">import</a> <a id="19232" href="synthetic-homotopy-theory.double-loop-spaces.html" class="Module">synthetic-homotopy-theory.double-loop-spaces</a>
<a id="19277" class="Keyword">open</a> <a id="19282" class="Keyword">import</a> <a id="19289" href="synthetic-homotopy-theory.functoriality-loop-spaces.html" class="Module">synthetic-homotopy-theory.functoriality-loop-spaces</a>
<a id="19341" class="Keyword">open</a> <a id="19346" class="Keyword">import</a> <a id="19353" href="synthetic-homotopy-theory.infinite-cyclic-types.html" class="Module">synthetic-homotopy-theory.infinite-cyclic-types</a>
<a id="19401" class="Keyword">open</a> <a id="19406" class="Keyword">import</a> <a id="19413" href="synthetic-homotopy-theory.interval-type.html" class="Module">synthetic-homotopy-theory.interval-type</a>
<a id="19453" class="Keyword">open</a> <a id="19458" class="Keyword">import</a> <a id="19465" href="synthetic-homotopy-theory.iterated-loop-spaces.html" class="Module">synthetic-homotopy-theory.iterated-loop-spaces</a>
<a id="19512" class="Keyword">open</a> <a id="19517" class="Keyword">import</a> <a id="19524" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
<a id="19562" class="Keyword">open</a> <a id="19567" class="Keyword">import</a> <a id="19574" href="synthetic-homotopy-theory.pointed-dependent-functions.html" class="Module">synthetic-homotopy-theory.pointed-dependent-functions</a>
<a id="19628" class="Keyword">open</a> <a id="19633" class="Keyword">import</a> <a id="19640" href="synthetic-homotopy-theory.pointed-equivalences.html" class="Module">synthetic-homotopy-theory.pointed-equivalences</a>
<a id="19687" class="Keyword">open</a> <a id="19692" class="Keyword">import</a> <a id="19699" href="synthetic-homotopy-theory.pointed-families-of-types.html" class="Module">synthetic-homotopy-theory.pointed-families-of-types</a>
<a id="19751" class="Keyword">open</a> <a id="19756" class="Keyword">import</a> <a id="19763" href="synthetic-homotopy-theory.pointed-homotopies.html" class="Module">synthetic-homotopy-theory.pointed-homotopies</a>
<a id="19808" class="Keyword">open</a> <a id="19813" class="Keyword">import</a> <a id="19820" href="synthetic-homotopy-theory.pointed-maps.html" class="Module">synthetic-homotopy-theory.pointed-maps</a>
<a id="19859" class="Keyword">open</a> <a id="19864" class="Keyword">import</a> <a id="19871" href="synthetic-homotopy-theory.pointed-types.html" class="Module">synthetic-homotopy-theory.pointed-types</a>
<a id="19911" class="Keyword">open</a> <a id="19916" class="Keyword">import</a> <a id="19923" href="synthetic-homotopy-theory.spaces.html" class="Module">synthetic-homotopy-theory.spaces</a>
<a id="19956" class="Keyword">open</a> <a id="19961" class="Keyword">import</a> <a id="19968" href="synthetic-homotopy-theory.triple-loop-spaces.html" class="Module">synthetic-homotopy-theory.triple-loop-spaces</a>
<a id="20013" class="Keyword">open</a> <a id="20018" class="Keyword">import</a> <a id="20025" href="synthetic-homotopy-theory.universal-cover-circle.html" class="Module">synthetic-homotopy-theory.universal-cover-circle</a>
</pre>
## Tutorials

<pre class="Agda"><a id="20101" class="Keyword">open</a> <a id="20106" class="Keyword">import</a> <a id="20113" href="tutorials.basic-agda.html" class="Module">tutorials.basic-agda</a>
</pre>
## Univalent combinatorics

<pre class="Agda"><a id="20175" class="Keyword">open</a> <a id="20180" class="Keyword">import</a> <a id="20187" href="univalent-combinatorics.html" class="Module">univalent-combinatorics</a>
<a id="20211" class="Keyword">open</a> <a id="20216" class="Keyword">import</a> <a id="20223" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="20263" class="Keyword">open</a> <a id="20268" class="Keyword">import</a> <a id="20275" href="univalent-combinatorics.binomial-types.html" class="Module">univalent-combinatorics.binomial-types</a>
<a id="20314" class="Keyword">open</a> <a id="20319" class="Keyword">import</a> <a id="20326" href="univalent-combinatorics.cartesian-product-types.html" class="Module">univalent-combinatorics.cartesian-product-types</a>
<a id="20374" class="Keyword">open</a> <a id="20379" class="Keyword">import</a> <a id="20386" href="univalent-combinatorics.classical-finite-types.html" class="Module">univalent-combinatorics.classical-finite-types</a>
<a id="20433" class="Keyword">open</a> <a id="20438" class="Keyword">import</a> <a id="20445" href="univalent-combinatorics.coproduct-types.html" class="Module">univalent-combinatorics.coproduct-types</a>
<a id="20485" class="Keyword">open</a> <a id="20490" class="Keyword">import</a> <a id="20497" href="univalent-combinatorics.counting-decidable-subtypes.html" class="Module">univalent-combinatorics.counting-decidable-subtypes</a>
<a id="20549" class="Keyword">open</a> <a id="20554" class="Keyword">import</a> <a id="20561" href="univalent-combinatorics.counting-dependent-function-types.html" class="Module">univalent-combinatorics.counting-dependent-function-types</a>
<a id="20619" class="Keyword">open</a> <a id="20624" class="Keyword">import</a> <a id="20631" href="univalent-combinatorics.counting-dependent-pair-types.html" class="Module">univalent-combinatorics.counting-dependent-pair-types</a>
<a id="20685" class="Keyword">open</a> <a id="20690" class="Keyword">import</a> <a id="20697" href="univalent-combinatorics.counting-fibers-of-maps.html" class="Module">univalent-combinatorics.counting-fibers-of-maps</a>
<a id="20745" class="Keyword">open</a> <a id="20750" class="Keyword">import</a> <a id="20757" href="univalent-combinatorics.counting-function-types.html" class="Module">univalent-combinatorics.counting-function-types</a>
<a id="20805" class="Keyword">open</a> <a id="20810" class="Keyword">import</a> <a id="20817" href="univalent-combinatorics.counting-maybe.html" class="Module">univalent-combinatorics.counting-maybe</a>
<a id="20856" class="Keyword">open</a> <a id="20861" class="Keyword">import</a> <a id="20868" href="univalent-combinatorics.counting.html" class="Module">univalent-combinatorics.counting</a>
<a id="20901" class="Keyword">open</a> <a id="20906" class="Keyword">import</a> <a id="20913" href="univalent-combinatorics.decidable-dependent-function-types.html" class="Module">univalent-combinatorics.decidable-dependent-function-types</a>
<a id="20972" class="Keyword">open</a> <a id="20977" class="Keyword">import</a> <a id="20984" href="univalent-combinatorics.decidable-dependent-pair-types.html" class="Module">univalent-combinatorics.decidable-dependent-pair-types</a>
<a id="21039" class="Keyword">open</a> <a id="21044" class="Keyword">import</a> <a id="21051" href="univalent-combinatorics.decidable-subtypes.html" class="Module">univalent-combinatorics.decidable-subtypes</a>
<a id="21094" class="Keyword">open</a> <a id="21099" class="Keyword">import</a> <a id="21106" href="univalent-combinatorics.dependent-product-finite-types.html" class="Module">univalent-combinatorics.dependent-product-finite-types</a>
<a id="21161" class="Keyword">open</a> <a id="21166" class="Keyword">import</a> <a id="21173" href="univalent-combinatorics.dependent-sum-finite-types.html" class="Module">univalent-combinatorics.dependent-sum-finite-types</a>
<a id="21224" class="Keyword">open</a> <a id="21229" class="Keyword">import</a> <a id="21236" href="univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.html" class="Module">univalent-combinatorics.distributivity-of-set-truncation-over-finite-products</a>
<a id="21314" class="Keyword">open</a> <a id="21319" class="Keyword">import</a> <a id="21326" href="univalent-combinatorics.double-counting.html" class="Module">univalent-combinatorics.double-counting</a>
<a id="21366" class="Keyword">open</a> <a id="21371" class="Keyword">import</a> <a id="21378" href="univalent-combinatorics.embeddings-standard-finite-types.html" class="Module">univalent-combinatorics.embeddings-standard-finite-types</a>
<a id="21435" class="Keyword">open</a> <a id="21440" class="Keyword">import</a> <a id="21447" href="univalent-combinatorics.embeddings.html" class="Module">univalent-combinatorics.embeddings</a>
<a id="21482" class="Keyword">open</a> <a id="21487" class="Keyword">import</a> <a id="21494" href="univalent-combinatorics.equality-finite-types.html" class="Module">univalent-combinatorics.equality-finite-types</a>
<a id="21540" class="Keyword">open</a> <a id="21545" class="Keyword">import</a> <a id="21552" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a>
<a id="21607" class="Keyword">open</a> <a id="21612" class="Keyword">import</a> <a id="21619" href="univalent-combinatorics.equivalences-standard-finite-types.html" class="Module">univalent-combinatorics.equivalences-standard-finite-types</a>
<a id="21678" class="Keyword">open</a> <a id="21683" class="Keyword">import</a> <a id="21690" href="univalent-combinatorics.equivalences.html" class="Module">univalent-combinatorics.equivalences</a>
<a id="21727" class="Keyword">open</a> <a id="21732" class="Keyword">import</a> <a id="21739" href="univalent-combinatorics.fibers-of-maps-between-finite-types.html" class="Module">univalent-combinatorics.fibers-of-maps-between-finite-types</a>
<a id="21799" class="Keyword">open</a> <a id="21804" class="Keyword">import</a> <a id="21811" href="univalent-combinatorics.finite-choice.html" class="Module">univalent-combinatorics.finite-choice</a>
<a id="21849" class="Keyword">open</a> <a id="21854" class="Keyword">import</a> <a id="21861" href="univalent-combinatorics.finite-connected-components.html" class="Module">univalent-combinatorics.finite-connected-components</a>
<a id="21913" class="Keyword">open</a> <a id="21918" class="Keyword">import</a> <a id="21925" href="univalent-combinatorics.finite-function-types.html" class="Module">univalent-combinatorics.finite-function-types</a>
<a id="21971" class="Keyword">open</a> <a id="21976" class="Keyword">import</a> <a id="21983" href="univalent-combinatorics.finite-presentations.html" class="Module">univalent-combinatorics.finite-presentations</a>
<a id="22028" class="Keyword">open</a> <a id="22033" class="Keyword">import</a> <a id="22040" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="22077" class="Keyword">open</a> <a id="22082" class="Keyword">import</a> <a id="22089" href="univalent-combinatorics.finitely-presented-types.html" class="Module">univalent-combinatorics.finitely-presented-types</a>
<a id="22138" class="Keyword">open</a> <a id="22143" class="Keyword">import</a> <a id="22150" href="univalent-combinatorics.image-of-maps.html" class="Module">univalent-combinatorics.image-of-maps</a>
<a id="22188" class="Keyword">open</a> <a id="22193" class="Keyword">import</a> <a id="22200" href="univalent-combinatorics.inequality-types-with-counting.html" class="Module">univalent-combinatorics.inequality-types-with-counting</a>
<a id="22255" class="Keyword">open</a> <a id="22260" class="Keyword">import</a> <a id="22267" href="univalent-combinatorics.injective-maps.html" class="Module">univalent-combinatorics.injective-maps</a>
<a id="22306" class="Keyword">open</a> <a id="22311" class="Keyword">import</a> <a id="22318" href="univalent-combinatorics.lists.html" class="Module">univalent-combinatorics.lists</a>
<a id="22348" class="Keyword">open</a> <a id="22353" class="Keyword">import</a> <a id="22360" href="univalent-combinatorics.maybe.html" class="Module">univalent-combinatorics.maybe</a>
<a id="22390" class="Keyword">open</a> <a id="22395" class="Keyword">import</a> <a id="22402" href="univalent-combinatorics.pi-finite-types.html" class="Module">univalent-combinatorics.pi-finite-types</a>
<a id="22442" class="Keyword">open</a> <a id="22447" class="Keyword">import</a> <a id="22454" href="univalent-combinatorics.pigeonhole-principle.html" class="Module">univalent-combinatorics.pigeonhole-principle</a>
<a id="22499" class="Keyword">open</a> <a id="22504" class="Keyword">import</a> <a id="22511" href="univalent-combinatorics.presented-pi-finite-types.html" class="Module">univalent-combinatorics.presented-pi-finite-types</a>
<a id="22561" class="Keyword">open</a> <a id="22566" class="Keyword">import</a> <a id="22573" href="univalent-combinatorics.ramsey-theory.html" class="Module">univalent-combinatorics.ramsey-theory</a>
<a id="22611" class="Keyword">open</a> <a id="22616" class="Keyword">import</a> <a id="22623" href="univalent-combinatorics.retracts-of-finite-types.html" class="Module">univalent-combinatorics.retracts-of-finite-types</a>
<a id="22672" class="Keyword">open</a> <a id="22677" class="Keyword">import</a> <a id="22684" href="univalent-combinatorics.skipping-element-standard-finite-types.html" class="Module">univalent-combinatorics.skipping-element-standard-finite-types</a>
<a id="22747" class="Keyword">open</a> <a id="22752" class="Keyword">import</a> <a id="22759" href="univalent-combinatorics.standard-finite-pruned-trees.html" class="Module">univalent-combinatorics.standard-finite-pruned-trees</a>
<a id="22812" class="Keyword">open</a> <a id="22817" class="Keyword">import</a> <a id="22824" href="univalent-combinatorics.standard-finite-trees.html" class="Module">univalent-combinatorics.standard-finite-trees</a>
<a id="22870" class="Keyword">open</a> <a id="22875" class="Keyword">import</a> <a id="22882" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
<a id="22928" class="Keyword">open</a> <a id="22933" class="Keyword">import</a> <a id="22940" href="univalent-combinatorics.sums-of-natural-numbers.html" class="Module">univalent-combinatorics.sums-of-natural-numbers</a>
<a id="22988" class="Keyword">open</a> <a id="22993" class="Keyword">import</a> <a id="23000" href="univalent-combinatorics.surjective-maps.html" class="Module">univalent-combinatorics.surjective-maps</a>
</pre>
## Univalent foundation

<pre class="Agda"><a id="23078" class="Keyword">open</a> <a id="23083" class="Keyword">import</a> <a id="23090" href="univalent-foundations.isolated-points.html" class="Module">univalent-foundations.isolated-points</a>
</pre>
## Wild algebra

<pre class="Agda"><a id="23158" class="Keyword">open</a> <a id="23163" class="Keyword">import</a> <a id="23170" href="wild-algebra.html" class="Module">wild-algebra</a>
<a id="23183" class="Keyword">open</a> <a id="23188" class="Keyword">import</a> <a id="23195" href="wild-algebra.magmas.html" class="Module">wild-algebra.magmas</a>
<a id="23215" class="Keyword">open</a> <a id="23220" class="Keyword">import</a> <a id="23227" href="wild-algebra.universal-property-lists-wild-monoids.html" class="Module">wild-algebra.universal-property-lists-wild-monoids</a>
<a id="23278" class="Keyword">open</a> <a id="23283" class="Keyword">import</a> <a id="23290" href="wild-algebra.wild-groups.html" class="Module">wild-algebra.wild-groups</a>
<a id="23315" class="Keyword">open</a> <a id="23320" class="Keyword">import</a> <a id="23327" href="wild-algebra.wild-monoids.html" class="Module">wild-algebra.wild-monoids</a>
<a id="23353" class="Keyword">open</a> <a id="23358" class="Keyword">import</a> <a id="23365" href="wild-algebra.wild-unital-magmas.html" class="Module">wild-algebra.wild-unital-magmas</a>
</pre>
## Everything

See the list of all Agda modules [here](everything.html).

