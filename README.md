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
<a id="930" class="Keyword">open</a> <a id="935" class="Keyword">import</a> <a id="942" href="category-theory.initial-objects-precategories.html" class="Module">category-theory.initial-objects-precategories</a>
<a id="988" class="Keyword">open</a> <a id="993" class="Keyword">import</a> <a id="1000" href="category-theory.isomorphisms-categories.html" class="Module">category-theory.isomorphisms-categories</a>
<a id="1040" class="Keyword">open</a> <a id="1045" class="Keyword">import</a> <a id="1052" href="category-theory.isomorphisms-large-precategories.html" class="Module">category-theory.isomorphisms-large-precategories</a>
<a id="1101" class="Keyword">open</a> <a id="1106" class="Keyword">import</a> <a id="1113" href="category-theory.isomorphisms-precategories.html" class="Module">category-theory.isomorphisms-precategories</a>
<a id="1156" class="Keyword">open</a> <a id="1161" class="Keyword">import</a> <a id="1168" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>
<a id="1201" class="Keyword">open</a> <a id="1206" class="Keyword">import</a> <a id="1213" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="1249" class="Keyword">open</a> <a id="1254" class="Keyword">import</a> <a id="1261" href="category-theory.monomorphisms-large-precategories.html" class="Module">category-theory.monomorphisms-large-precategories</a>
<a id="1311" class="Keyword">open</a> <a id="1316" class="Keyword">import</a> <a id="1323" href="category-theory.natural-isomorphisms-categories.html" class="Module">category-theory.natural-isomorphisms-categories</a>
<a id="1371" class="Keyword">open</a> <a id="1376" class="Keyword">import</a> <a id="1383" href="category-theory.natural-isomorphisms-large-precategories.html" class="Module">category-theory.natural-isomorphisms-large-precategories</a>
<a id="1440" class="Keyword">open</a> <a id="1445" class="Keyword">import</a> <a id="1452" href="category-theory.natural-isomorphisms-precategories.html" class="Module">category-theory.natural-isomorphisms-precategories</a>
<a id="1503" class="Keyword">open</a> <a id="1508" class="Keyword">import</a> <a id="1515" href="category-theory.natural-transformations-categories.html" class="Module">category-theory.natural-transformations-categories</a>
<a id="1566" class="Keyword">open</a> <a id="1571" class="Keyword">import</a> <a id="1578" href="category-theory.natural-transformations-large-precategories.html" class="Module">category-theory.natural-transformations-large-precategories</a>
<a id="1638" class="Keyword">open</a> <a id="1643" class="Keyword">import</a> <a id="1650" href="category-theory.natural-transformations-precategories.html" class="Module">category-theory.natural-transformations-precategories</a>
<a id="1704" class="Keyword">open</a> <a id="1709" class="Keyword">import</a> <a id="1716" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>
<a id="1746" class="Keyword">open</a> <a id="1751" class="Keyword">import</a> <a id="1758" href="category-theory.terminal-objects-precategories.html" class="Module">category-theory.terminal-objects-precategories</a>
<a id="1805" class="Keyword">open</a> <a id="1810" class="Keyword">import</a> <a id="1817" href="category-theory.slice-precategories.html" class="Module">category-theory.slice-precategories</a>
</pre>
## Elementary number theory

<pre class="Agda"><a id="1895" class="Keyword">open</a> <a id="1900" class="Keyword">import</a> <a id="1907" href="elementary-number-theory.html" class="Module">elementary-number-theory</a>
<a id="1932" class="Keyword">open</a> <a id="1937" class="Keyword">import</a> <a id="1944" href="elementary-number-theory.absolute-value-integers.html" class="Module">elementary-number-theory.absolute-value-integers</a>
<a id="1993" class="Keyword">open</a> <a id="1998" class="Keyword">import</a> <a id="2005" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a>
<a id="2048" class="Keyword">open</a> <a id="2053" class="Keyword">import</a> <a id="2060" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="2110" class="Keyword">open</a> <a id="2115" class="Keyword">import</a> <a id="2122" href="elementary-number-theory.arithmetic-functions.html" class="Module">elementary-number-theory.arithmetic-functions</a>
<a id="2168" class="Keyword">open</a> <a id="2173" class="Keyword">import</a> <a id="2180" href="elementary-number-theory.binomial-coefficients.html" class="Module">elementary-number-theory.binomial-coefficients</a>
<a id="2227" class="Keyword">open</a> <a id="2232" class="Keyword">import</a> <a id="2239" href="elementary-number-theory.bounded-sums-arithmetic-functions.html" class="Module">elementary-number-theory.bounded-sums-arithmetic-functions</a>
<a id="2298" class="Keyword">open</a> <a id="2303" class="Keyword">import</a> <a id="2310" href="elementary-number-theory.catalan-numbers.html" class="Module">elementary-number-theory.catalan-numbers</a>
<a id="2351" class="Keyword">open</a> <a id="2356" class="Keyword">import</a> <a id="2363" href="elementary-number-theory.collatz-bijection.html" class="Module">elementary-number-theory.collatz-bijection</a>
<a id="2406" class="Keyword">open</a> <a id="2411" class="Keyword">import</a> <a id="2418" href="elementary-number-theory.collatz-conjecture.html" class="Module">elementary-number-theory.collatz-conjecture</a>
<a id="2462" class="Keyword">open</a> <a id="2467" class="Keyword">import</a> <a id="2474" href="elementary-number-theory.congruence-integers.html" class="Module">elementary-number-theory.congruence-integers</a>
<a id="2519" class="Keyword">open</a> <a id="2524" class="Keyword">import</a> <a id="2531" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a>
<a id="2583" class="Keyword">open</a> <a id="2588" class="Keyword">import</a> <a id="2595" href="elementary-number-theory.decidable-dependent-function-types.html" class="Module">elementary-number-theory.decidable-dependent-function-types</a>
<a id="2655" class="Keyword">open</a> <a id="2660" class="Keyword">import</a> <a id="2667" href="elementary-number-theory.decidable-types.html" class="Module">elementary-number-theory.decidable-types</a>
<a id="2708" class="Keyword">open</a> <a id="2713" class="Keyword">import</a> <a id="2720" href="elementary-number-theory.difference-integers.html" class="Module">elementary-number-theory.difference-integers</a>
<a id="2765" class="Keyword">open</a> <a id="2770" class="Keyword">import</a> <a id="2777" href="elementary-number-theory.dirichlet-convolution.html" class="Module">elementary-number-theory.dirichlet-convolution</a>
<a id="2824" class="Keyword">open</a> <a id="2829" class="Keyword">import</a> <a id="2836" href="elementary-number-theory.distance-integers.html" class="Module">elementary-number-theory.distance-integers</a>
<a id="2879" class="Keyword">open</a> <a id="2884" class="Keyword">import</a> <a id="2891" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a>
<a id="2941" class="Keyword">open</a> <a id="2946" class="Keyword">import</a> <a id="2953" href="elementary-number-theory.divisibility-integers.html" class="Module">elementary-number-theory.divisibility-integers</a>
<a id="3000" class="Keyword">open</a> <a id="3005" class="Keyword">import</a> <a id="3012" href="elementary-number-theory.divisibility-modular-arithmetic.html" class="Module">elementary-number-theory.divisibility-modular-arithmetic</a>
<a id="3069" class="Keyword">open</a> <a id="3074" class="Keyword">import</a> <a id="3081" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a>
<a id="3135" class="Keyword">open</a> <a id="3140" class="Keyword">import</a> <a id="3147" href="elementary-number-theory.divisibility-standard-finite-types.html" class="Module">elementary-number-theory.divisibility-standard-finite-types</a>
<a id="3207" class="Keyword">open</a> <a id="3212" class="Keyword">import</a> <a id="3219" href="elementary-number-theory.equality-integers.html" class="Module">elementary-number-theory.equality-integers</a>
<a id="3262" class="Keyword">open</a> <a id="3267" class="Keyword">import</a> <a id="3274" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a>
<a id="3324" class="Keyword">open</a> <a id="3329" class="Keyword">import</a> <a id="3336" href="elementary-number-theory.euclidean-division-natural-numbers.html" class="Module">elementary-number-theory.euclidean-division-natural-numbers</a>
<a id="3396" class="Keyword">open</a> <a id="3401" class="Keyword">import</a> <a id="3408" href="elementary-number-theory.eulers-totient-function.html" class="Module">elementary-number-theory.eulers-totient-function</a>
<a id="3457" class="Keyword">open</a> <a id="3462" class="Keyword">import</a> <a id="3469" href="elementary-number-theory.exponentiation-natural-numbers.html" class="Module">elementary-number-theory.exponentiation-natural-numbers</a>
<a id="3525" class="Keyword">open</a> <a id="3530" class="Keyword">import</a> <a id="3537" href="elementary-number-theory.factorials.html" class="Module">elementary-number-theory.factorials</a>
<a id="3573" class="Keyword">open</a> <a id="3578" class="Keyword">import</a> <a id="3585" href="elementary-number-theory.falling-factorials.html" class="Module">elementary-number-theory.falling-factorials</a>
<a id="3629" class="Keyword">open</a> <a id="3634" class="Keyword">import</a> <a id="3641" href="elementary-number-theory.fibonacci-sequence.html" class="Module">elementary-number-theory.fibonacci-sequence</a>
<a id="3685" class="Keyword">open</a> <a id="3690" class="Keyword">import</a> <a id="3697" href="elementary-number-theory.finitary-natural-numbers.html" class="Module">elementary-number-theory.finitary-natural-numbers</a>
<a id="3747" class="Keyword">open</a> <a id="3752" class="Keyword">import</a> <a id="3759" href="elementary-number-theory.finitely-cyclic-maps.html" class="Module">elementary-number-theory.finitely-cyclic-maps</a>
<a id="3805" class="Keyword">open</a> <a id="3810" class="Keyword">import</a> <a id="3817" href="elementary-number-theory.fractions.html" class="Module">elementary-number-theory.fractions</a>
<a id="3852" class="Keyword">open</a> <a id="3857" class="Keyword">import</a> <a id="3864" href="elementary-number-theory.goldbach-conjecture.html" class="Module">elementary-number-theory.goldbach-conjecture</a>
<a id="3909" class="Keyword">open</a> <a id="3914" class="Keyword">import</a> <a id="3921" href="elementary-number-theory.greatest-common-divisor-integers.html" class="Module">elementary-number-theory.greatest-common-divisor-integers</a>
<a id="3979" class="Keyword">open</a> <a id="3984" class="Keyword">import</a> <a id="3991" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a>
<a id="4056" class="Keyword">open</a> <a id="4061" class="Keyword">import</a> <a id="4068" href="elementary-number-theory.group-of-integers.html" class="Module">elementary-number-theory.group-of-integers</a>
<a id="4111" class="Keyword">open</a> <a id="4116" class="Keyword">import</a> <a id="4123" href="elementary-number-theory.groups-of-modular-arithmetic.html" class="Module">elementary-number-theory.groups-of-modular-arithmetic</a>
<a id="4177" class="Keyword">open</a> <a id="4182" class="Keyword">import</a> <a id="4189" href="elementary-number-theory.inequality-integers.html" class="Module">elementary-number-theory.inequality-integers</a>
<a id="4234" class="Keyword">open</a> <a id="4239" class="Keyword">import</a> <a id="4246" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a>
<a id="4298" class="Keyword">open</a> <a id="4303" class="Keyword">import</a> <a id="4310" href="elementary-number-theory.inequality-standard-finite-types.html" class="Module">elementary-number-theory.inequality-standard-finite-types</a>
<a id="4368" class="Keyword">open</a> <a id="4373" class="Keyword">import</a> <a id="4380" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a>
<a id="4426" class="Keyword">open</a> <a id="4431" class="Keyword">import</a> <a id="4438" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="4472" class="Keyword">open</a> <a id="4477" class="Keyword">import</a> <a id="4484" href="elementary-number-theory.iterating-functions.html" class="Module">elementary-number-theory.iterating-functions</a>
<a id="4529" class="Keyword">open</a> <a id="4534" class="Keyword">import</a> <a id="4541" href="elementary-number-theory.lower-bounds-natural-numbers.html" class="Module">elementary-number-theory.lower-bounds-natural-numbers</a>
<a id="4595" class="Keyword">open</a> <a id="4600" class="Keyword">import</a> <a id="4607" href="elementary-number-theory.maximum-natural-numbers.html" class="Module">elementary-number-theory.maximum-natural-numbers</a>
<a id="4656" class="Keyword">open</a> <a id="4661" class="Keyword">import</a> <a id="4668" href="elementary-number-theory.mersenne-primes.html" class="Module">elementary-number-theory.mersenne-primes</a>
<a id="4709" class="Keyword">open</a> <a id="4714" class="Keyword">import</a> <a id="4721" href="elementary-number-theory.minimum-natural-numbers.html" class="Module">elementary-number-theory.minimum-natural-numbers</a>
<a id="4770" class="Keyword">open</a> <a id="4775" class="Keyword">import</a> <a id="4782" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a>
<a id="4848" class="Keyword">open</a> <a id="4853" class="Keyword">import</a> <a id="4860" href="elementary-number-theory.modular-arithmetic.html" class="Module">elementary-number-theory.modular-arithmetic</a>
<a id="4904" class="Keyword">open</a> <a id="4909" class="Keyword">import</a> <a id="4916" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a>
<a id="4965" class="Keyword">open</a> <a id="4970" class="Keyword">import</a> <a id="4977" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a>
<a id="5033" class="Keyword">open</a> <a id="5038" class="Keyword">import</a> <a id="5045" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="5086" class="Keyword">open</a> <a id="5091" class="Keyword">import</a> <a id="5098" href="elementary-number-theory.nonzero-natural-numbers.html" class="Module">elementary-number-theory.nonzero-natural-numbers</a>
<a id="5147" class="Keyword">open</a> <a id="5152" class="Keyword">import</a> <a id="5159" href="elementary-number-theory.ordinal-induction-natural-numbers.html" class="Module">elementary-number-theory.ordinal-induction-natural-numbers</a>
<a id="5218" class="Keyword">open</a> <a id="5223" class="Keyword">import</a> <a id="5230" href="elementary-number-theory.prime-numbers.html" class="Module">elementary-number-theory.prime-numbers</a>
<a id="5269" class="Keyword">open</a> <a id="5274" class="Keyword">import</a> <a id="5281" href="elementary-number-theory.products-of-natural-numbers.html" class="Module">elementary-number-theory.products-of-natural-numbers</a>
<a id="5334" class="Keyword">open</a> <a id="5339" class="Keyword">import</a> <a id="5346" href="elementary-number-theory.proper-divisors-natural-numbers.html" class="Module">elementary-number-theory.proper-divisors-natural-numbers</a>
<a id="5403" class="Keyword">open</a> <a id="5408" class="Keyword">import</a> <a id="5415" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a>
<a id="5457" class="Keyword">open</a> <a id="5462" class="Keyword">import</a> <a id="5469" href="elementary-number-theory.relatively-prime-integers.html" class="Module">elementary-number-theory.relatively-prime-integers</a>
<a id="5520" class="Keyword">open</a> <a id="5525" class="Keyword">import</a> <a id="5532" href="elementary-number-theory.relatively-prime-natural-numbers.html" class="Module">elementary-number-theory.relatively-prime-natural-numbers</a>
<a id="5590" class="Keyword">open</a> <a id="5595" class="Keyword">import</a> <a id="5602" href="elementary-number-theory.repeating-element-standard-finite-type.html" class="Module">elementary-number-theory.repeating-element-standard-finite-type</a>
<a id="5666" class="Keyword">open</a> <a id="5671" class="Keyword">import</a> <a id="5678" href="elementary-number-theory.retracts-of-natural-numbers.html" class="Module">elementary-number-theory.retracts-of-natural-numbers</a>
<a id="5731" class="Keyword">open</a> <a id="5736" class="Keyword">import</a> <a id="5743" href="elementary-number-theory.square-free-natural-numbers.html" class="Module">elementary-number-theory.square-free-natural-numbers</a>
<a id="5796" class="Keyword">open</a> <a id="5801" class="Keyword">import</a> <a id="5808" href="elementary-number-theory.stirling-numbers-of-the-second-kind.html" class="Module">elementary-number-theory.stirling-numbers-of-the-second-kind</a>
<a id="5869" class="Keyword">open</a> <a id="5874" class="Keyword">import</a> <a id="5881" href="elementary-number-theory.strong-induction-natural-numbers.html" class="Module">elementary-number-theory.strong-induction-natural-numbers</a>
<a id="5939" class="Keyword">open</a> <a id="5944" class="Keyword">import</a> <a id="5951" href="elementary-number-theory.sums-of-natural-numbers.html" class="Module">elementary-number-theory.sums-of-natural-numbers</a>
<a id="6000" class="Keyword">open</a> <a id="6005" class="Keyword">import</a> <a id="6012" href="elementary-number-theory.triangular-numbers.html" class="Module">elementary-number-theory.triangular-numbers</a>
<a id="6056" class="Keyword">open</a> <a id="6061" class="Keyword">import</a> <a id="6068" href="elementary-number-theory.twin-prime-conjecture.html" class="Module">elementary-number-theory.twin-prime-conjecture</a>
<a id="6115" class="Keyword">open</a> <a id="6120" class="Keyword">import</a> <a id="6127" href="elementary-number-theory.unit-elements-standard-finite-types.html" class="Module">elementary-number-theory.unit-elements-standard-finite-types</a>
<a id="6188" class="Keyword">open</a> <a id="6193" class="Keyword">import</a> <a id="6200" href="elementary-number-theory.unit-similarity-standard-finite-types.html" class="Module">elementary-number-theory.unit-similarity-standard-finite-types</a>
<a id="6263" class="Keyword">open</a> <a id="6268" class="Keyword">import</a> <a id="6275" href="elementary-number-theory.universal-property-natural-numbers.html" class="Module">elementary-number-theory.universal-property-natural-numbers</a>
<a id="6335" class="Keyword">open</a> <a id="6340" class="Keyword">import</a> <a id="6347" href="elementary-number-theory.upper-bounds-natural-numbers.html" class="Module">elementary-number-theory.upper-bounds-natural-numbers</a>
<a id="6401" class="Keyword">open</a> <a id="6406" class="Keyword">import</a> <a id="6413" href="elementary-number-theory.well-ordering-principle-natural-numbers.html" class="Module">elementary-number-theory.well-ordering-principle-natural-numbers</a>
<a id="6478" class="Keyword">open</a> <a id="6483" class="Keyword">import</a> <a id="6490" href="elementary-number-theory.well-ordering-principle-standard-finite-types.html" class="Module">elementary-number-theory.well-ordering-principle-standard-finite-types</a>
</pre>
## Finite group theory

<pre class="Agda"><a id="6598" class="Keyword">open</a> <a id="6603" class="Keyword">import</a> <a id="6610" href="finite-group-theory.html" class="Module">finite-group-theory</a>
<a id="6630" class="Keyword">open</a> <a id="6635" class="Keyword">import</a> <a id="6642" href="finite-group-theory.abstract-quaternion-group.html" class="Module">finite-group-theory.abstract-quaternion-group</a>
<a id="6688" class="Keyword">open</a> <a id="6693" class="Keyword">import</a> <a id="6700" href="finite-group-theory.concrete-quaternion-group.html" class="Module">finite-group-theory.concrete-quaternion-group</a>
<a id="6746" class="Keyword">open</a> <a id="6751" class="Keyword">import</a> <a id="6758" href="finite-group-theory.finite-groups.html" class="Module">finite-group-theory.finite-groups</a>
<a id="6792" class="Keyword">open</a> <a id="6797" class="Keyword">import</a> <a id="6804" href="finite-group-theory.orbits-permutations.html" class="Module">finite-group-theory.orbits-permutations</a>
<a id="6844" class="Keyword">open</a> <a id="6849" class="Keyword">import</a> <a id="6856" href="finite-group-theory.permutations.html" class="Module">finite-group-theory.permutations</a>
<a id="6889" class="Keyword">open</a> <a id="6894" class="Keyword">import</a> <a id="6901" href="finite-group-theory.transpositions.html" class="Module">finite-group-theory.transpositions</a>
</pre>
## Foundation

<pre class="Agda"><a id="6964" class="Keyword">open</a> <a id="6969" class="Keyword">import</a> <a id="6976" href="foundation.html" class="Module">foundation</a>
<a id="6987" class="Keyword">open</a> <a id="6992" class="Keyword">import</a> <a id="6999" href="foundation.0-maps.html" class="Module">foundation.0-maps</a>
<a id="7017" class="Keyword">open</a> <a id="7022" class="Keyword">import</a> <a id="7029" href="foundation.1-types.html" class="Module">foundation.1-types</a>
<a id="7048" class="Keyword">open</a> <a id="7053" class="Keyword">import</a> <a id="7060" href="foundation.2-types.html" class="Module">foundation.2-types</a>
<a id="7079" class="Keyword">open</a> <a id="7084" class="Keyword">import</a> <a id="7091" href="foundation.algebras-polynomial-endofunctors.html" class="Module">foundation.algebras-polynomial-endofunctors</a>
<a id="7135" class="Keyword">open</a> <a id="7140" class="Keyword">import</a> <a id="7147" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="7172" class="Keyword">open</a> <a id="7177" class="Keyword">import</a> <a id="7184" href="foundation.axiom-of-choice.html" class="Module">foundation.axiom-of-choice</a>
<a id="7211" class="Keyword">open</a> <a id="7216" class="Keyword">import</a> <a id="7223" href="foundation.binary-embeddings.html" class="Module">foundation.binary-embeddings</a>
<a id="7252" class="Keyword">open</a> <a id="7257" class="Keyword">import</a> <a id="7264" href="foundation.binary-equivalences.html" class="Module">foundation.binary-equivalences</a>
<a id="7295" class="Keyword">open</a> <a id="7300" class="Keyword">import</a> <a id="7307" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="7335" class="Keyword">open</a> <a id="7340" class="Keyword">import</a> <a id="7347" href="foundation.boolean-reflection.html" class="Module">foundation.boolean-reflection</a>
<a id="7377" class="Keyword">open</a> <a id="7382" class="Keyword">import</a> <a id="7389" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="7409" class="Keyword">open</a> <a id="7414" class="Keyword">import</a> <a id="7421" href="foundation.cantors-diagonal-argument.html" class="Module">foundation.cantors-diagonal-argument</a>
<a id="7458" class="Keyword">open</a> <a id="7463" class="Keyword">import</a> <a id="7470" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="7505" class="Keyword">open</a> <a id="7510" class="Keyword">import</a> <a id="7517" href="foundation.choice-of-representatives-equivalence-relation.html" class="Module">foundation.choice-of-representatives-equivalence-relation</a>
<a id="7575" class="Keyword">open</a> <a id="7580" class="Keyword">import</a> <a id="7587" href="foundation.coherently-invertible-maps.html" class="Module">foundation.coherently-invertible-maps</a>
<a id="7625" class="Keyword">open</a> <a id="7630" class="Keyword">import</a> <a id="7637" href="foundation.commuting-squares.html" class="Module">foundation.commuting-squares</a>
<a id="7666" class="Keyword">open</a> <a id="7671" class="Keyword">import</a> <a id="7678" href="foundation.complements.html" class="Module">foundation.complements</a>
<a id="7701" class="Keyword">open</a> <a id="7706" class="Keyword">import</a> <a id="7713" href="foundation.conjunction.html" class="Module">foundation.conjunction</a>
<a id="7736" class="Keyword">open</a> <a id="7741" class="Keyword">import</a> <a id="7748" href="foundation.connected-components-universes.html" class="Module">foundation.connected-components-universes</a>
<a id="7790" class="Keyword">open</a> <a id="7795" class="Keyword">import</a> <a id="7802" href="foundation.connected-components.html" class="Module">foundation.connected-components</a>
<a id="7834" class="Keyword">open</a> <a id="7839" class="Keyword">import</a> <a id="7846" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="7873" class="Keyword">open</a> <a id="7878" class="Keyword">import</a> <a id="7885" href="foundation.constant-maps.html" class="Module">foundation.constant-maps</a>
<a id="7910" class="Keyword">open</a> <a id="7915" class="Keyword">import</a> <a id="7922" href="foundation.contractible-maps.html" class="Module">foundation.contractible-maps</a>
<a id="7951" class="Keyword">open</a> <a id="7956" class="Keyword">import</a> <a id="7963" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="7993" class="Keyword">open</a> <a id="7998" class="Keyword">import</a> <a id="8005" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="8032" class="Keyword">open</a> <a id="8037" class="Keyword">import</a> <a id="8044" href="foundation.coslice.html" class="Module">foundation.coslice</a>
<a id="8063" class="Keyword">open</a> <a id="8068" class="Keyword">import</a> <a id="8075" href="foundation.decidable-dependent-function-types.html" class="Module">foundation.decidable-dependent-function-types</a>
<a id="8121" class="Keyword">open</a> <a id="8126" class="Keyword">import</a> <a id="8133" href="foundation.decidable-dependent-pair-types.html" class="Module">foundation.decidable-dependent-pair-types</a>
<a id="8175" class="Keyword">open</a> <a id="8180" class="Keyword">import</a> <a id="8187" href="foundation.decidable-embeddings.html" class="Module">foundation.decidable-embeddings</a>
<a id="8219" class="Keyword">open</a> <a id="8224" class="Keyword">import</a> <a id="8231" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a>
<a id="8261" class="Keyword">open</a> <a id="8266" class="Keyword">import</a> <a id="8273" href="foundation.decidable-maps.html" class="Module">foundation.decidable-maps</a>
<a id="8299" class="Keyword">open</a> <a id="8304" class="Keyword">import</a> <a id="8311" href="foundation.decidable-propositions.html" class="Module">foundation.decidable-propositions</a>
<a id="8345" class="Keyword">open</a> <a id="8350" class="Keyword">import</a> <a id="8357" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="8387" class="Keyword">open</a> <a id="8392" class="Keyword">import</a> <a id="8399" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="8426" class="Keyword">open</a> <a id="8431" class="Keyword">import</a> <a id="8438" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="8470" class="Keyword">open</a> <a id="8475" class="Keyword">import</a> <a id="8482" href="foundation.diagonal-maps-of-types.html" class="Module">foundation.diagonal-maps-of-types</a>
<a id="8516" class="Keyword">open</a> <a id="8521" class="Keyword">import</a> <a id="8528" href="foundation.disjunction.html" class="Module">foundation.disjunction</a>
<a id="8551" class="Keyword">open</a> <a id="8556" class="Keyword">import</a> <a id="8563" href="foundation.distributivity-of-dependent-functions-over-coproduct-types.html" class="Module">foundation.distributivity-of-dependent-functions-over-coproduct-types</a>
<a id="8633" class="Keyword">open</a> <a id="8638" class="Keyword">import</a> <a id="8645" href="foundation.distributivity-of-dependent-functions-over-dependent-pairs.html" class="Module">foundation.distributivity-of-dependent-functions-over-dependent-pairs</a>
<a id="8715" class="Keyword">open</a> <a id="8720" class="Keyword">import</a> <a id="8727" href="foundation.double-negation.html" class="Module">foundation.double-negation</a>
<a id="8754" class="Keyword">open</a> <a id="8759" class="Keyword">import</a> <a id="8766" href="foundation.effective-maps-equivalence-relations.html" class="Module">foundation.effective-maps-equivalence-relations</a>
<a id="8814" class="Keyword">open</a> <a id="8819" class="Keyword">import</a> <a id="8826" href="foundation.elementhood-relation-w-types.html" class="Module">foundation.elementhood-relation-w-types</a>
<a id="8866" class="Keyword">open</a> <a id="8871" class="Keyword">import</a> <a id="8878" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="8900" class="Keyword">open</a> <a id="8905" class="Keyword">import</a> <a id="8912" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="8935" class="Keyword">open</a> <a id="8940" class="Keyword">import</a> <a id="8947" href="foundation.epimorphisms-with-respect-to-sets.html" class="Module">foundation.epimorphisms-with-respect-to-sets</a>
<a id="8992" class="Keyword">open</a> <a id="8997" class="Keyword">import</a> <a id="9004" href="foundation.equality-cartesian-product-types.html" class="Module">foundation.equality-cartesian-product-types</a>
<a id="9048" class="Keyword">open</a> <a id="9053" class="Keyword">import</a> <a id="9060" href="foundation.equality-coproduct-types.html" class="Module">foundation.equality-coproduct-types</a>
<a id="9096" class="Keyword">open</a> <a id="9101" class="Keyword">import</a> <a id="9108" href="foundation.equality-dependent-function-types.html" class="Module">foundation.equality-dependent-function-types</a>
<a id="9153" class="Keyword">open</a> <a id="9158" class="Keyword">import</a> <a id="9165" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="9206" class="Keyword">open</a> <a id="9211" class="Keyword">import</a> <a id="9218" href="foundation.equality-fibers-of-maps.html" class="Module">foundation.equality-fibers-of-maps</a>
<a id="9253" class="Keyword">open</a> <a id="9258" class="Keyword">import</a> <a id="9265" href="foundation.equivalence-classes.html" class="Module">foundation.equivalence-classes</a>
<a id="9296" class="Keyword">open</a> <a id="9301" class="Keyword">import</a> <a id="9308" href="foundation.equivalence-induction.html" class="Module">foundation.equivalence-induction</a>
<a id="9341" class="Keyword">open</a> <a id="9346" class="Keyword">import</a> <a id="9353" href="foundation.equivalence-relations.html" class="Module">foundation.equivalence-relations</a>
<a id="9386" class="Keyword">open</a> <a id="9391" class="Keyword">import</a> <a id="9398" href="foundation.equivalences-maybe.html" class="Module">foundation.equivalences-maybe</a>
<a id="9428" class="Keyword">open</a> <a id="9433" class="Keyword">import</a> <a id="9440" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="9464" class="Keyword">open</a> <a id="9469" class="Keyword">import</a> <a id="9476" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="9514" class="Keyword">open</a> <a id="9519" class="Keyword">import</a> <a id="9526" href="foundation.extensional-w-types.html" class="Module">foundation.extensional-w-types</a>
<a id="9557" class="Keyword">open</a> <a id="9562" class="Keyword">import</a> <a id="9569" href="foundation.faithful-maps.html" class="Module">foundation.faithful-maps</a>
<a id="9594" class="Keyword">open</a> <a id="9599" class="Keyword">import</a> <a id="9606" href="foundation.fiber-inclusions.html" class="Module">foundation.fiber-inclusions</a>
<a id="9634" class="Keyword">open</a> <a id="9639" class="Keyword">import</a> <a id="9646" href="foundation.fibered-maps.html" class="Module">foundation.fibered-maps</a>
<a id="9670" class="Keyword">open</a> <a id="9675" class="Keyword">import</a> <a id="9682" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="9708" class="Keyword">open</a> <a id="9713" class="Keyword">import</a> <a id="9720" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="9755" class="Keyword">open</a> <a id="9760" class="Keyword">import</a> <a id="9767" href="foundation.functions.html" class="Module">foundation.functions</a>
<a id="9788" class="Keyword">open</a> <a id="9793" class="Keyword">import</a> <a id="9800" href="foundation.functoriality-cartesian-product-types.html" class="Module">foundation.functoriality-cartesian-product-types</a>
<a id="9849" class="Keyword">open</a> <a id="9854" class="Keyword">import</a> <a id="9861" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="9902" class="Keyword">open</a> <a id="9907" class="Keyword">import</a> <a id="9914" href="foundation.functoriality-dependent-function-types.html" class="Module">foundation.functoriality-dependent-function-types</a>
<a id="9964" class="Keyword">open</a> <a id="9969" class="Keyword">import</a> <a id="9976" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="10022" class="Keyword">open</a> <a id="10027" class="Keyword">import</a> <a id="10034" href="foundation.functoriality-function-types.html" class="Module">foundation.functoriality-function-types</a>
<a id="10074" class="Keyword">open</a> <a id="10079" class="Keyword">import</a> <a id="10086" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="10136" class="Keyword">open</a> <a id="10141" class="Keyword">import</a> <a id="10148" href="foundation.functoriality-set-quotients.html" class="Module">foundation.functoriality-set-quotients</a>
<a id="10187" class="Keyword">open</a> <a id="10192" class="Keyword">import</a> <a id="10199" href="foundation.functoriality-set-truncation.html" class="Module">foundation.functoriality-set-truncation</a>
<a id="10239" class="Keyword">open</a> <a id="10244" class="Keyword">import</a> <a id="10251" href="foundation.functoriality-w-types.html" class="Module">foundation.functoriality-w-types</a>
<a id="10284" class="Keyword">open</a> <a id="10289" class="Keyword">import</a> <a id="10296" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="10345" class="Keyword">open</a> <a id="10350" class="Keyword">import</a> <a id="10357" href="foundation.global-choice.html" class="Module">foundation.global-choice</a>
<a id="10382" class="Keyword">open</a> <a id="10387" class="Keyword">import</a> <a id="10394" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="10416" class="Keyword">open</a> <a id="10421" class="Keyword">import</a> <a id="10428" href="foundation.identity-systems.html" class="Module">foundation.identity-systems</a>
<a id="10456" class="Keyword">open</a> <a id="10461" class="Keyword">import</a> <a id="10468" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="10494" class="Keyword">open</a> <a id="10499" class="Keyword">import</a> <a id="10506" href="foundation.images.html" class="Module">foundation.images</a>
<a id="10524" class="Keyword">open</a> <a id="10529" class="Keyword">import</a> <a id="10536" href="foundation.impredicative-encodings.html" class="Module">foundation.impredicative-encodings</a>
<a id="10571" class="Keyword">open</a> <a id="10576" class="Keyword">import</a> <a id="10583" href="foundation.indexed-w-types.html" class="Module">foundation.indexed-w-types</a>
<a id="10610" class="Keyword">open</a> <a id="10615" class="Keyword">import</a> <a id="10622" href="foundation.induction-principle-propositional-truncation.html" class="Module">foundation.induction-principle-propositional-truncation</a>
<a id="10678" class="Keyword">open</a> <a id="10683" class="Keyword">import</a> <a id="10690" href="foundation.induction-w-types.html" class="Module">foundation.induction-w-types</a>
<a id="10719" class="Keyword">open</a> <a id="10724" class="Keyword">import</a> <a id="10731" href="foundation.inequality-w-types.html" class="Module">foundation.inequality-w-types</a>
<a id="10761" class="Keyword">open</a> <a id="10766" class="Keyword">import</a> <a id="10773" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="10799" class="Keyword">open</a> <a id="10804" class="Keyword">import</a> <a id="10811" href="foundation.interchange-law.html" class="Module">foundation.interchange-law</a>
<a id="10838" class="Keyword">open</a> <a id="10843" class="Keyword">import</a> <a id="10850" href="foundation.involutions.html" class="Module">foundation.involutions</a>
<a id="10873" class="Keyword">open</a> <a id="10878" class="Keyword">import</a> <a id="10885" href="foundation.isolated-points.html" class="Module">foundation.isolated-points</a>
<a id="10912" class="Keyword">open</a> <a id="10917" class="Keyword">import</a> <a id="10924" href="foundation.isomorphisms-of-sets.html" class="Module">foundation.isomorphisms-of-sets</a>
<a id="10956" class="Keyword">open</a> <a id="10961" class="Keyword">import</a> <a id="10968" href="foundation.law-of-excluded-middle.html" class="Module">foundation.law-of-excluded-middle</a>
<a id="11002" class="Keyword">open</a> <a id="11007" class="Keyword">import</a> <a id="11014" href="foundation.lawveres-fixed-point-theorem.html" class="Module">foundation.lawveres-fixed-point-theorem</a>
<a id="11054" class="Keyword">open</a> <a id="11059" class="Keyword">import</a> <a id="11066" href="foundation.locally-small-types.html" class="Module">foundation.locally-small-types</a>
<a id="11097" class="Keyword">open</a> <a id="11102" class="Keyword">import</a> <a id="11109" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="11141" class="Keyword">open</a> <a id="11146" class="Keyword">import</a> <a id="11153" href="foundation.lower-types-w-types.html" class="Module">foundation.lower-types-w-types</a>
<a id="11184" class="Keyword">open</a> <a id="11189" class="Keyword">import</a> <a id="11196" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="11213" class="Keyword">open</a> <a id="11218" class="Keyword">import</a> <a id="11225" href="foundation.mere-equality.html" class="Module">foundation.mere-equality</a>
<a id="11250" class="Keyword">open</a> <a id="11255" class="Keyword">import</a> <a id="11262" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="11291" class="Keyword">open</a> <a id="11296" class="Keyword">import</a> <a id="11303" href="foundation.monomorphisms.html" class="Module">foundation.monomorphisms</a>
<a id="11328" class="Keyword">open</a> <a id="11333" class="Keyword">import</a> <a id="11340" href="foundation.multisets.html" class="Module">foundation.multisets</a>
<a id="11361" class="Keyword">open</a> <a id="11366" class="Keyword">import</a> <a id="11373" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="11393" class="Keyword">open</a> <a id="11398" class="Keyword">import</a> <a id="11405" href="foundation.non-contractible-types.html" class="Module">foundation.non-contractible-types</a>
<a id="11439" class="Keyword">open</a> <a id="11444" class="Keyword">import</a> <a id="11451" href="foundation.path-algebra.html" class="Module">foundation.path-algebra</a>
<a id="11475" class="Keyword">open</a> <a id="11480" class="Keyword">import</a> <a id="11487" href="foundation.path-split-maps.html" class="Module">foundation.path-split-maps</a>
<a id="11514" class="Keyword">open</a> <a id="11519" class="Keyword">import</a> <a id="11526" href="foundation.polynomial-endofunctors.html" class="Module">foundation.polynomial-endofunctors</a>
<a id="11561" class="Keyword">open</a> <a id="11566" class="Keyword">import</a> <a id="11573" href="foundation.propositional-extensionality.html" class="Module">foundation.propositional-extensionality</a>
<a id="11613" class="Keyword">open</a> <a id="11618" class="Keyword">import</a> <a id="11625" href="foundation.propositional-maps.html" class="Module">foundation.propositional-maps</a>
<a id="11655" class="Keyword">open</a> <a id="11660" class="Keyword">import</a> <a id="11667" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="11704" class="Keyword">open</a> <a id="11709" class="Keyword">import</a> <a id="11716" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="11740" class="Keyword">open</a> <a id="11745" class="Keyword">import</a> <a id="11752" href="foundation.pullbacks.html" class="Module">foundation.pullbacks</a>
<a id="11773" class="Keyword">open</a> <a id="11778" class="Keyword">import</a> <a id="11785" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="11820" class="Keyword">open</a> <a id="11825" class="Keyword">import</a> <a id="11832" href="foundation.ranks-of-elements-w-types.html" class="Module">foundation.ranks-of-elements-w-types</a>
<a id="11869" class="Keyword">open</a> <a id="11874" class="Keyword">import</a> <a id="11881" href="foundation.reflecting-maps-equivalence-relations.html" class="Module">foundation.reflecting-maps-equivalence-relations</a>
<a id="11930" class="Keyword">open</a> <a id="11935" class="Keyword">import</a> <a id="11942" href="foundation.replacement.html" class="Module">foundation.replacement</a>
<a id="11965" class="Keyword">open</a> <a id="11970" class="Keyword">import</a> <a id="11977" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="12000" class="Keyword">open</a> <a id="12005" class="Keyword">import</a> <a id="12012" href="foundation.russells-paradox.html" class="Module">foundation.russells-paradox</a>
<a id="12040" class="Keyword">open</a> <a id="12045" class="Keyword">import</a> <a id="12052" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="12072" class="Keyword">open</a> <a id="12077" class="Keyword">import</a> <a id="12084" href="foundation.set-presented-types.html" class="Module">foundation.set-presented-types</a>
<a id="12115" class="Keyword">open</a> <a id="12120" class="Keyword">import</a> <a id="12127" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="12154" class="Keyword">open</a> <a id="12159" class="Keyword">import</a> <a id="12166" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="12182" class="Keyword">open</a> <a id="12187" class="Keyword">import</a> <a id="12194" href="foundation.singleton-induction.html" class="Module">foundation.singleton-induction</a>
<a id="12225" class="Keyword">open</a> <a id="12230" class="Keyword">import</a> <a id="12237" href="foundation.slice.html" class="Module">foundation.slice</a>
<a id="12254" class="Keyword">open</a> <a id="12259" class="Keyword">import</a> <a id="12266" href="foundation.small-maps.html" class="Module">foundation.small-maps</a>
<a id="12288" class="Keyword">open</a> <a id="12293" class="Keyword">import</a> <a id="12300" href="foundation.small-multisets.html" class="Module">foundation.small-multisets</a>
<a id="12327" class="Keyword">open</a> <a id="12332" class="Keyword">import</a> <a id="12339" href="foundation.small-types.html" class="Module">foundation.small-types</a>
<a id="12362" class="Keyword">open</a> <a id="12367" class="Keyword">import</a> <a id="12374" href="foundation.small-universes.html" class="Module">foundation.small-universes</a>
<a id="12401" class="Keyword">open</a> <a id="12406" class="Keyword">import</a> <a id="12413" href="foundation.split-surjective-maps.html" class="Module">foundation.split-surjective-maps</a>
<a id="12446" class="Keyword">open</a> <a id="12451" class="Keyword">import</a> <a id="12458" href="foundation.structure-identity-principle.html" class="Module">foundation.structure-identity-principle</a>
<a id="12498" class="Keyword">open</a> <a id="12503" class="Keyword">import</a> <a id="12510" href="foundation.structure.html" class="Module">foundation.structure</a>
<a id="12531" class="Keyword">open</a> <a id="12536" class="Keyword">import</a> <a id="12543" href="foundation.subterminal-types.html" class="Module">foundation.subterminal-types</a>
<a id="12572" class="Keyword">open</a> <a id="12577" class="Keyword">import</a> <a id="12584" href="foundation.subtype-identity-principle.html" class="Module">foundation.subtype-identity-principle</a>
<a id="12622" class="Keyword">open</a> <a id="12627" class="Keyword">import</a> <a id="12634" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="12654" class="Keyword">open</a> <a id="12659" class="Keyword">import</a> <a id="12666" href="foundation.subuniverses.html" class="Module">foundation.subuniverses</a>
<a id="12690" class="Keyword">open</a> <a id="12695" class="Keyword">import</a> <a id="12702" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="12729" class="Keyword">open</a> <a id="12734" class="Keyword">import</a> <a id="12741" href="foundation.truncated-equality.html" class="Module">foundation.truncated-equality</a>
<a id="12771" class="Keyword">open</a> <a id="12776" class="Keyword">import</a> <a id="12783" href="foundation.truncated-maps.html" class="Module">foundation.truncated-maps</a>
<a id="12809" class="Keyword">open</a> <a id="12814" class="Keyword">import</a> <a id="12821" href="foundation.truncated-types.html" class="Module">foundation.truncated-types</a>
<a id="12848" class="Keyword">open</a> <a id="12853" class="Keyword">import</a> <a id="12860" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="12889" class="Keyword">open</a> <a id="12894" class="Keyword">import</a> <a id="12901" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="12924" class="Keyword">open</a> <a id="12929" class="Keyword">import</a> <a id="12936" href="foundation.type-arithmetic-cartesian-product-types.html" class="Module">foundation.type-arithmetic-cartesian-product-types</a>
<a id="12987" class="Keyword">open</a> <a id="12992" class="Keyword">import</a> <a id="12999" href="foundation.type-arithmetic-coproduct-types.html" class="Module">foundation.type-arithmetic-coproduct-types</a>
<a id="13042" class="Keyword">open</a> <a id="13047" class="Keyword">import</a> <a id="13054" href="foundation.type-arithmetic-dependent-pair-types.html" class="Module">foundation.type-arithmetic-dependent-pair-types</a>
<a id="13102" class="Keyword">open</a> <a id="13107" class="Keyword">import</a> <a id="13114" href="foundation.type-arithmetic-empty-type.html" class="Module">foundation.type-arithmetic-empty-type</a>
<a id="13152" class="Keyword">open</a> <a id="13157" class="Keyword">import</a> <a id="13164" href="foundation.type-arithmetic-unit-type.html" class="Module">foundation.type-arithmetic-unit-type</a>
<a id="13201" class="Keyword">open</a> <a id="13206" class="Keyword">import</a> <a id="13213" href="foundation.uniqueness-image.html" class="Module">foundation.uniqueness-image</a>
<a id="13241" class="Keyword">open</a> <a id="13246" class="Keyword">import</a> <a id="13253" href="foundation.uniqueness-set-quotients.html" class="Module">foundation.uniqueness-set-quotients</a>
<a id="13289" class="Keyword">open</a> <a id="13294" class="Keyword">import</a> <a id="13301" href="foundation.uniqueness-set-truncations.html" class="Module">foundation.uniqueness-set-truncations</a>
<a id="13339" class="Keyword">open</a> <a id="13344" class="Keyword">import</a> <a id="13351" href="foundation.uniqueness-truncation.html" class="Module">foundation.uniqueness-truncation</a>
<a id="13384" class="Keyword">open</a> <a id="13389" class="Keyword">import</a> <a id="13396" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="13417" class="Keyword">open</a> <a id="13422" class="Keyword">import</a> <a id="13429" href="foundation.univalence-implies-function-extensionality.html" class="Module">foundation.univalence-implies-function-extensionality</a>
<a id="13483" class="Keyword">open</a> <a id="13488" class="Keyword">import</a> <a id="13495" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="13517" class="Keyword">open</a> <a id="13522" class="Keyword">import</a> <a id="13529" href="foundation.univalent-type-families.html" class="Module">foundation.univalent-type-families</a>
<a id="13564" class="Keyword">open</a> <a id="13569" class="Keyword">import</a> <a id="13576" href="foundation.universal-multiset.html" class="Module">foundation.universal-multiset</a>
<a id="13606" class="Keyword">open</a> <a id="13611" class="Keyword">import</a> <a id="13618" href="foundation.universal-property-booleans.html" class="Module">foundation.universal-property-booleans</a>
<a id="13657" class="Keyword">open</a> <a id="13662" class="Keyword">import</a> <a id="13669" href="foundation.universal-property-cartesian-product-types.html" class="Module">foundation.universal-property-cartesian-product-types</a>
<a id="13723" class="Keyword">open</a> <a id="13728" class="Keyword">import</a> <a id="13735" href="foundation.universal-property-coproduct-types.html" class="Module">foundation.universal-property-coproduct-types</a>
<a id="13781" class="Keyword">open</a> <a id="13786" class="Keyword">import</a> <a id="13793" href="foundation.universal-property-dependent-pair-types.html" class="Module">foundation.universal-property-dependent-pair-types</a>
<a id="13844" class="Keyword">open</a> <a id="13849" class="Keyword">import</a> <a id="13856" href="foundation.universal-property-empty-type.html" class="Module">foundation.universal-property-empty-type</a>
<a id="13897" class="Keyword">open</a> <a id="13902" class="Keyword">import</a> <a id="13909" href="foundation.universal-property-fiber-products.html" class="Module">foundation.universal-property-fiber-products</a>
<a id="13954" class="Keyword">open</a> <a id="13959" class="Keyword">import</a> <a id="13966" href="foundation.universal-property-identity-types.html" class="Module">foundation.universal-property-identity-types</a>
<a id="14011" class="Keyword">open</a> <a id="14016" class="Keyword">import</a> <a id="14023" href="foundation.universal-property-image.html" class="Module">foundation.universal-property-image</a>
<a id="14059" class="Keyword">open</a> <a id="14064" class="Keyword">import</a> <a id="14071" href="foundation.universal-property-maybe.html" class="Module">foundation.universal-property-maybe</a>
<a id="14107" class="Keyword">open</a> <a id="14112" class="Keyword">import</a> <a id="14119" href="foundation.universal-property-propositional-truncation-into-sets.html" class="Module">foundation.universal-property-propositional-truncation-into-sets</a>
<a id="14184" class="Keyword">open</a> <a id="14189" class="Keyword">import</a> <a id="14196" href="foundation.universal-property-propositional-truncation.html" class="Module">foundation.universal-property-propositional-truncation</a>
<a id="14251" class="Keyword">open</a> <a id="14256" class="Keyword">import</a> <a id="14263" href="foundation.universal-property-pullbacks.html" class="Module">foundation.universal-property-pullbacks</a>
<a id="14303" class="Keyword">open</a> <a id="14308" class="Keyword">import</a> <a id="14315" href="foundation.universal-property-set-quotients.html" class="Module">foundation.universal-property-set-quotients</a>
<a id="14359" class="Keyword">open</a> <a id="14364" class="Keyword">import</a> <a id="14371" href="foundation.universal-property-set-truncation.html" class="Module">foundation.universal-property-set-truncation</a>
<a id="14416" class="Keyword">open</a> <a id="14421" class="Keyword">import</a> <a id="14428" href="foundation.universal-property-truncation.html" class="Module">foundation.universal-property-truncation</a>
<a id="14469" class="Keyword">open</a> <a id="14474" class="Keyword">import</a> <a id="14481" href="foundation.universal-property-unit-type.html" class="Module">foundation.universal-property-unit-type</a>
<a id="14521" class="Keyword">open</a> <a id="14526" class="Keyword">import</a> <a id="14533" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="14560" class="Keyword">open</a> <a id="14565" class="Keyword">import</a> <a id="14572" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>
<a id="14599" class="Keyword">open</a> <a id="14604" class="Keyword">import</a> <a id="14611" href="foundation.w-types.html" class="Module">foundation.w-types</a>
<a id="14630" class="Keyword">open</a> <a id="14635" class="Keyword">import</a> <a id="14642" href="foundation.weak-function-extensionality.html" class="Module">foundation.weak-function-extensionality</a>
<a id="14682" class="Keyword">open</a> <a id="14687" class="Keyword">import</a> <a id="14694" href="foundation.weakly-constant-maps.html" class="Module">foundation.weakly-constant-maps</a>
</pre>
## Foundation Core

<pre class="Agda"><a id="14759" class="Keyword">open</a> <a id="14764" class="Keyword">import</a> <a id="14771" href="foundation-core.0-maps.html" class="Module">foundation-core.0-maps</a>
<a id="14794" class="Keyword">open</a> <a id="14799" class="Keyword">import</a> <a id="14806" href="foundation-core.1-types.html" class="Module">foundation-core.1-types</a>
<a id="14830" class="Keyword">open</a> <a id="14835" class="Keyword">import</a> <a id="14842" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="14882" class="Keyword">open</a> <a id="14887" class="Keyword">import</a> <a id="14894" href="foundation-core.coherently-invertible-maps.html" class="Module">foundation-core.coherently-invertible-maps</a>
<a id="14937" class="Keyword">open</a> <a id="14942" class="Keyword">import</a> <a id="14949" href="foundation-core.commuting-squares.html" class="Module">foundation-core.commuting-squares</a>
<a id="14983" class="Keyword">open</a> <a id="14988" class="Keyword">import</a> <a id="14995" href="foundation-core.constant-maps.html" class="Module">foundation-core.constant-maps</a>
<a id="15025" class="Keyword">open</a> <a id="15030" class="Keyword">import</a> <a id="15037" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="15071" class="Keyword">open</a> <a id="15076" class="Keyword">import</a> <a id="15083" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="15118" class="Keyword">open</a> <a id="15123" class="Keyword">import</a> <a id="15130" href="foundation-core.dependent-pair-types.html" class="Module">foundation-core.dependent-pair-types</a>
<a id="15167" class="Keyword">open</a> <a id="15172" class="Keyword">import</a> <a id="15179" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="15206" class="Keyword">open</a> <a id="15211" class="Keyword">import</a> <a id="15218" href="foundation-core.empty-types.html" class="Module">foundation-core.empty-types</a>
<a id="15246" class="Keyword">open</a> <a id="15251" class="Keyword">import</a> <a id="15258" href="foundation-core.equality-cartesian-product-types.html" class="Module">foundation-core.equality-cartesian-product-types</a>
<a id="15307" class="Keyword">open</a> <a id="15312" class="Keyword">import</a> <a id="15319" href="foundation-core.equality-dependent-pair-types.html" class="Module">foundation-core.equality-dependent-pair-types</a>
<a id="15365" class="Keyword">open</a> <a id="15370" class="Keyword">import</a> <a id="15377" href="foundation-core.equality-fibers-of-maps.html" class="Module">foundation-core.equality-fibers-of-maps</a>
<a id="15417" class="Keyword">open</a> <a id="15422" class="Keyword">import</a> <a id="15429" href="foundation-core.equivalence-induction.html" class="Module">foundation-core.equivalence-induction</a>
<a id="15467" class="Keyword">open</a> <a id="15472" class="Keyword">import</a> <a id="15479" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="15508" class="Keyword">open</a> <a id="15513" class="Keyword">import</a> <a id="15520" href="foundation-core.faithful-maps.html" class="Module">foundation-core.faithful-maps</a>
<a id="15550" class="Keyword">open</a> <a id="15555" class="Keyword">import</a> <a id="15562" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
<a id="15593" class="Keyword">open</a> <a id="15598" class="Keyword">import</a> <a id="15605" href="foundation-core.functions.html" class="Module">foundation-core.functions</a>
<a id="15631" class="Keyword">open</a> <a id="15636" class="Keyword">import</a> <a id="15643" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
<a id="15694" class="Keyword">open</a> <a id="15699" class="Keyword">import</a> <a id="15706" href="foundation-core.fundamental-theorem-of-identity-types.html" class="Module">foundation-core.fundamental-theorem-of-identity-types</a>
<a id="15760" class="Keyword">open</a> <a id="15765" class="Keyword">import</a> <a id="15772" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="15799" class="Keyword">open</a> <a id="15804" class="Keyword">import</a> <a id="15811" href="foundation-core.identity-systems.html" class="Module">foundation-core.identity-systems</a>
<a id="15844" class="Keyword">open</a> <a id="15849" class="Keyword">import</a> <a id="15856" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="15887" class="Keyword">open</a> <a id="15892" class="Keyword">import</a> <a id="15899" href="foundation-core.logical-equivalences.html" class="Module">foundation-core.logical-equivalences</a>
<a id="15936" class="Keyword">open</a> <a id="15941" class="Keyword">import</a> <a id="15948" href="foundation-core.negation.html" class="Module">foundation-core.negation</a>
<a id="15973" class="Keyword">open</a> <a id="15978" class="Keyword">import</a> <a id="15985" href="foundation-core.path-split-maps.html" class="Module">foundation-core.path-split-maps</a>
<a id="16017" class="Keyword">open</a> <a id="16022" class="Keyword">import</a> <a id="16029" href="foundation-core.propositional-maps.html" class="Module">foundation-core.propositional-maps</a>
<a id="16064" class="Keyword">open</a> <a id="16069" class="Keyword">import</a> <a id="16076" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="16105" class="Keyword">open</a> <a id="16110" class="Keyword">import</a> <a id="16117" href="foundation-core.retractions.html" class="Module">foundation-core.retractions</a>
<a id="16145" class="Keyword">open</a> <a id="16150" class="Keyword">import</a> <a id="16157" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
<a id="16182" class="Keyword">open</a> <a id="16187" class="Keyword">import</a> <a id="16194" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>
<a id="16215" class="Keyword">open</a> <a id="16220" class="Keyword">import</a> <a id="16227" href="foundation-core.singleton-induction.html" class="Module">foundation-core.singleton-induction</a>
<a id="16263" class="Keyword">open</a> <a id="16268" class="Keyword">import</a> <a id="16275" href="foundation-core.subtype-identity-principle.html" class="Module">foundation-core.subtype-identity-principle</a>
<a id="16318" class="Keyword">open</a> <a id="16323" class="Keyword">import</a> <a id="16330" href="foundation-core.subtypes.html" class="Module">foundation-core.subtypes</a>
<a id="16355" class="Keyword">open</a> <a id="16360" class="Keyword">import</a> <a id="16367" href="foundation-core.truncated-maps.html" class="Module">foundation-core.truncated-maps</a>
<a id="16398" class="Keyword">open</a> <a id="16403" class="Keyword">import</a> <a id="16410" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="16442" class="Keyword">open</a> <a id="16447" class="Keyword">import</a> <a id="16454" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
<a id="16488" class="Keyword">open</a> <a id="16493" class="Keyword">import</a> <a id="16500" href="foundation-core.type-arithmetic-cartesian-product-types.html" class="Module">foundation-core.type-arithmetic-cartesian-product-types</a>
<a id="16556" class="Keyword">open</a> <a id="16561" class="Keyword">import</a> <a id="16568" href="foundation-core.type-arithmetic-dependent-pair-types.html" class="Module">foundation-core.type-arithmetic-dependent-pair-types</a>
<a id="16621" class="Keyword">open</a> <a id="16626" class="Keyword">import</a> <a id="16633" href="foundation-core.univalence.html" class="Module">foundation-core.univalence</a>
<a id="16660" class="Keyword">open</a> <a id="16665" class="Keyword">import</a> <a id="16672" href="foundation-core.universe-levels.html" class="Module">foundation-core.universe-levels</a>
</pre>
## Graph theory

<pre class="Agda"><a id="16734" class="Keyword">open</a> <a id="16739" class="Keyword">import</a> <a id="16746" href="graph-theory.html" class="Module">graph-theory</a>
<a id="16759" class="Keyword">open</a> <a id="16764" class="Keyword">import</a> <a id="16771" href="graph-theory.connected-undirected-graphs.html" class="Module">graph-theory.connected-undirected-graphs</a>
<a id="16812" class="Keyword">open</a> <a id="16817" class="Keyword">import</a> <a id="16824" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="16853" class="Keyword">open</a> <a id="16858" class="Keyword">import</a> <a id="16865" href="graph-theory.edge-coloured-undirected-graphs.html" class="Module">graph-theory.edge-coloured-undirected-graphs</a>
<a id="16910" class="Keyword">open</a> <a id="16915" class="Keyword">import</a> <a id="16922" href="graph-theory.equivalences-undirected-graphs.html" class="Module">graph-theory.equivalences-undirected-graphs</a>
<a id="16966" class="Keyword">open</a> <a id="16971" class="Keyword">import</a> <a id="16978" href="graph-theory.finite-graphs.html" class="Module">graph-theory.finite-graphs</a>
<a id="17005" class="Keyword">open</a> <a id="17010" class="Keyword">import</a> <a id="17017" href="graph-theory.incidence-undirected-graphs.html" class="Module">graph-theory.incidence-undirected-graphs</a>
<a id="17058" class="Keyword">open</a> <a id="17063" class="Keyword">import</a> <a id="17070" href="graph-theory.mere-equivalences-undirected-graphs.html" class="Module">graph-theory.mere-equivalences-undirected-graphs</a>
<a id="17119" class="Keyword">open</a> <a id="17124" class="Keyword">import</a> <a id="17131" href="graph-theory.morphisms-directed-graphs.html" class="Module">graph-theory.morphisms-directed-graphs</a>
<a id="17170" class="Keyword">open</a> <a id="17175" class="Keyword">import</a> <a id="17182" href="graph-theory.morphisms-undirected-graphs.html" class="Module">graph-theory.morphisms-undirected-graphs</a>
<a id="17223" class="Keyword">open</a> <a id="17228" class="Keyword">import</a> <a id="17235" href="graph-theory.orientations-undirected-graphs.html" class="Module">graph-theory.orientations-undirected-graphs</a>
<a id="17279" class="Keyword">open</a> <a id="17284" class="Keyword">import</a> <a id="17291" href="graph-theory.paths-undirected-graphs.html" class="Module">graph-theory.paths-undirected-graphs</a>
<a id="17328" class="Keyword">open</a> <a id="17333" class="Keyword">import</a> <a id="17340" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>
<a id="17362" class="Keyword">open</a> <a id="17367" class="Keyword">import</a> <a id="17374" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
<a id="17404" class="Keyword">open</a> <a id="17409" class="Keyword">import</a> <a id="17416" href="graph-theory.regular-undirected-graphs.html" class="Module">graph-theory.regular-undirected-graphs</a>
<a id="17455" class="Keyword">open</a> <a id="17460" class="Keyword">import</a> <a id="17467" href="graph-theory.simple-undirected-graphs.html" class="Module">graph-theory.simple-undirected-graphs</a>
<a id="17505" class="Keyword">open</a> <a id="17510" class="Keyword">import</a> <a id="17517" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
## Group theory

<pre class="Agda"><a id="17578" class="Keyword">open</a> <a id="17583" class="Keyword">import</a> <a id="17590" href="group-theory.html" class="Module">group-theory</a>
<a id="17603" class="Keyword">open</a> <a id="17608" class="Keyword">import</a> <a id="17615" href="group-theory.abelian-groups.html" class="Module">group-theory.abelian-groups</a>
<a id="17643" class="Keyword">open</a> <a id="17648" class="Keyword">import</a> <a id="17655" href="group-theory.abelian-subgroups.html" class="Module">group-theory.abelian-subgroups</a>
<a id="17686" class="Keyword">open</a> <a id="17691" class="Keyword">import</a> <a id="17698" href="group-theory.abstract-group-torsors.html" class="Module">group-theory.abstract-group-torsors</a>
<a id="17734" class="Keyword">open</a> <a id="17739" class="Keyword">import</a> <a id="17746" href="group-theory.category-of-groups.html" class="Module">group-theory.category-of-groups</a>
<a id="17778" class="Keyword">open</a> <a id="17783" class="Keyword">import</a> <a id="17790" href="group-theory.category-of-semigroups.html" class="Module">group-theory.category-of-semigroups</a>
<a id="17826" class="Keyword">open</a> <a id="17831" class="Keyword">import</a> <a id="17838" href="group-theory.cayleys-theorem.html" class="Module">group-theory.cayleys-theorem</a>
<a id="17867" class="Keyword">open</a> <a id="17872" class="Keyword">import</a> <a id="17879" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="17915" class="Keyword">open</a> <a id="17920" class="Keyword">import</a> <a id="17927" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="17956" class="Keyword">open</a> <a id="17961" class="Keyword">import</a> <a id="17968" href="group-theory.concrete-subgroups.html" class="Module">group-theory.concrete-subgroups</a>
<a id="18000" class="Keyword">open</a> <a id="18005" class="Keyword">import</a> <a id="18012" href="group-theory.conjugation.html" class="Module">group-theory.conjugation</a>
<a id="18037" class="Keyword">open</a> <a id="18042" class="Keyword">import</a> <a id="18049" href="group-theory.embeddings-groups.html" class="Module">group-theory.embeddings-groups</a>
<a id="18080" class="Keyword">open</a> <a id="18085" class="Keyword">import</a> <a id="18092" href="group-theory.equivalences-group-actions.html" class="Module">group-theory.equivalences-group-actions</a>
<a id="18132" class="Keyword">open</a> <a id="18137" class="Keyword">import</a> <a id="18144" href="group-theory.equivalences-semigroups.html" class="Module">group-theory.equivalences-semigroups</a>
<a id="18181" class="Keyword">open</a> <a id="18186" class="Keyword">import</a> <a id="18193" href="group-theory.examples-higher-groups.html" class="Module">group-theory.examples-higher-groups</a>
<a id="18229" class="Keyword">open</a> <a id="18234" class="Keyword">import</a> <a id="18241" href="group-theory.furstenberg-groups.html" class="Module">group-theory.furstenberg-groups</a>
<a id="18273" class="Keyword">open</a> <a id="18278" class="Keyword">import</a> <a id="18285" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="18312" class="Keyword">open</a> <a id="18317" class="Keyword">import</a> <a id="18324" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="18344" class="Keyword">open</a> <a id="18349" class="Keyword">import</a> <a id="18356" href="group-theory.higher-groups.html" class="Module">group-theory.higher-groups</a>
<a id="18383" class="Keyword">open</a> <a id="18388" class="Keyword">import</a> <a id="18395" href="group-theory.homomorphisms-abelian-groups.html" class="Module">group-theory.homomorphisms-abelian-groups</a>
<a id="18437" class="Keyword">open</a> <a id="18442" class="Keyword">import</a> <a id="18449" href="group-theory.homomorphisms-group-actions.html" class="Module">group-theory.homomorphisms-group-actions</a>
<a id="18490" class="Keyword">open</a> <a id="18495" class="Keyword">import</a> <a id="18502" href="group-theory.homomorphisms-groups.html" class="Module">group-theory.homomorphisms-groups</a>
<a id="18536" class="Keyword">open</a> <a id="18541" class="Keyword">import</a> <a id="18548" href="group-theory.homomorphisms-monoids.html" class="Module">group-theory.homomorphisms-monoids</a>
<a id="18583" class="Keyword">open</a> <a id="18588" class="Keyword">import</a> <a id="18595" href="group-theory.homomorphisms-semigroups.html" class="Module">group-theory.homomorphisms-semigroups</a>
<a id="18633" class="Keyword">open</a> <a id="18638" class="Keyword">import</a> <a id="18645" href="group-theory.invertible-elements-monoids.html" class="Module">group-theory.invertible-elements-monoids</a>
<a id="18686" class="Keyword">open</a> <a id="18691" class="Keyword">import</a> <a id="18698" href="group-theory.isomorphisms-abelian-groups.html" class="Module">group-theory.isomorphisms-abelian-groups</a>
<a id="18739" class="Keyword">open</a> <a id="18744" class="Keyword">import</a> <a id="18751" href="group-theory.isomorphisms-group-actions.html" class="Module">group-theory.isomorphisms-group-actions</a>
<a id="18791" class="Keyword">open</a> <a id="18796" class="Keyword">import</a> <a id="18803" href="group-theory.isomorphisms-groups.html" class="Module">group-theory.isomorphisms-groups</a>
<a id="18836" class="Keyword">open</a> <a id="18841" class="Keyword">import</a> <a id="18848" href="group-theory.isomorphisms-semigroups.html" class="Module">group-theory.isomorphisms-semigroups</a>
<a id="18885" class="Keyword">open</a> <a id="18890" class="Keyword">import</a> <a id="18897" href="group-theory.mere-equivalences-group-actions.html" class="Module">group-theory.mere-equivalences-group-actions</a>
<a id="18942" class="Keyword">open</a> <a id="18947" class="Keyword">import</a> <a id="18954" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>
<a id="18975" class="Keyword">open</a> <a id="18980" class="Keyword">import</a> <a id="18987" href="group-theory.orbits-group-actions.html" class="Module">group-theory.orbits-group-actions</a>
<a id="19021" class="Keyword">open</a> <a id="19026" class="Keyword">import</a> <a id="19033" href="group-theory.precategory-of-group-actions.html" class="Module">group-theory.precategory-of-group-actions</a>
<a id="19075" class="Keyword">open</a> <a id="19080" class="Keyword">import</a> <a id="19087" href="group-theory.precategory-of-groups.html" class="Module">group-theory.precategory-of-groups</a>
<a id="19122" class="Keyword">open</a> <a id="19127" class="Keyword">import</a> <a id="19134" href="group-theory.precategory-of-semigroups.html" class="Module">group-theory.precategory-of-semigroups</a>
<a id="19173" class="Keyword">open</a> <a id="19178" class="Keyword">import</a> <a id="19185" href="group-theory.principal-group-actions.html" class="Module">group-theory.principal-group-actions</a>
<a id="19222" class="Keyword">open</a> <a id="19227" class="Keyword">import</a> <a id="19234" href="group-theory.semigroups.html" class="Module">group-theory.semigroups</a>
<a id="19258" class="Keyword">open</a> <a id="19263" class="Keyword">import</a> <a id="19270" href="group-theory.sheargroups.html" class="Module">group-theory.sheargroups</a>
<a id="19295" class="Keyword">open</a> <a id="19300" class="Keyword">import</a> <a id="19307" href="group-theory.stabilizer-groups.html" class="Module">group-theory.stabilizer-groups</a>
<a id="19338" class="Keyword">open</a> <a id="19343" class="Keyword">import</a> <a id="19350" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
<a id="19373" class="Keyword">open</a> <a id="19378" class="Keyword">import</a> <a id="19385" href="group-theory.substitution-functor-group-actions.html" class="Module">group-theory.substitution-functor-group-actions</a>
<a id="19433" class="Keyword">open</a> <a id="19438" class="Keyword">import</a> <a id="19445" href="group-theory.symmetric-groups.html" class="Module">group-theory.symmetric-groups</a>
<a id="19475" class="Keyword">open</a> <a id="19480" class="Keyword">import</a> <a id="19487" href="group-theory.transitive-group-actions.html" class="Module">group-theory.transitive-group-actions</a>
</pre>
## Linear algebra

<pre class="Agda"><a id="19557" class="Keyword">open</a> <a id="19562" class="Keyword">import</a> <a id="19569" href="linear-algebra.html" class="Module">linear-algebra</a>
<a id="19584" class="Keyword">open</a> <a id="19589" class="Keyword">import</a> <a id="19596" href="linear-algebra.constant-matrices.html" class="Module">linear-algebra.constant-matrices</a>
<a id="19629" class="Keyword">open</a> <a id="19634" class="Keyword">import</a> <a id="19641" href="linear-algebra.constant-vectors.html" class="Module">linear-algebra.constant-vectors</a>
<a id="19673" class="Keyword">open</a> <a id="19678" class="Keyword">import</a> <a id="19685" href="linear-algebra.diagonal-matrices-on-rings.html" class="Module">linear-algebra.diagonal-matrices-on-rings</a>
<a id="19727" class="Keyword">open</a> <a id="19732" class="Keyword">import</a> <a id="19739" href="linear-algebra.functoriality-matrices.html" class="Module">linear-algebra.functoriality-matrices</a>
<a id="19777" class="Keyword">open</a> <a id="19782" class="Keyword">import</a> <a id="19789" href="linear-algebra.functoriality-vectors.html" class="Module">linear-algebra.functoriality-vectors</a>
<a id="19826" class="Keyword">open</a> <a id="19831" class="Keyword">import</a> <a id="19838" href="linear-algebra.matrices-on-rings.html" class="Module">linear-algebra.matrices-on-rings</a>
<a id="19871" class="Keyword">open</a> <a id="19876" class="Keyword">import</a> <a id="19883" href="linear-algebra.matrices.html" class="Module">linear-algebra.matrices</a>
<a id="19907" class="Keyword">open</a> <a id="19912" class="Keyword">import</a> <a id="19919" href="linear-algebra.multiplication-matrices.html" class="Module">linear-algebra.multiplication-matrices</a>
<a id="19958" class="Keyword">open</a> <a id="19963" class="Keyword">import</a> <a id="19970" href="linear-algebra.scalar-multiplication-matrices.html" class="Module">linear-algebra.scalar-multiplication-matrices</a>
<a id="20016" class="Keyword">open</a> <a id="20021" class="Keyword">import</a> <a id="20028" href="linear-algebra.scalar-multiplication-vectors.html" class="Module">linear-algebra.scalar-multiplication-vectors</a>
<a id="20073" class="Keyword">open</a> <a id="20078" class="Keyword">import</a> <a id="20085" href="linear-algebra.transposition-matrices.html" class="Module">linear-algebra.transposition-matrices</a>
<a id="20123" class="Keyword">open</a> <a id="20128" class="Keyword">import</a> <a id="20135" href="linear-algebra.vectors-on-rings.html" class="Module">linear-algebra.vectors-on-rings</a>
<a id="20167" class="Keyword">open</a> <a id="20172" class="Keyword">import</a> <a id="20179" href="linear-algebra.vectors.html" class="Module">linear-algebra.vectors</a>
</pre>
## Order theory

<pre class="Agda"><a id="20232" class="Keyword">open</a> <a id="20237" class="Keyword">import</a> <a id="20244" href="order-theory.html" class="Module">order-theory</a>
<a id="20257" class="Keyword">open</a> <a id="20262" class="Keyword">import</a> <a id="20269" href="order-theory.chains-posets.html" class="Module">order-theory.chains-posets</a>
<a id="20296" class="Keyword">open</a> <a id="20301" class="Keyword">import</a> <a id="20308" href="order-theory.chains-preorders.html" class="Module">order-theory.chains-preorders</a>
<a id="20338" class="Keyword">open</a> <a id="20343" class="Keyword">import</a> <a id="20350" href="order-theory.decidable-subposets.html" class="Module">order-theory.decidable-subposets</a>
<a id="20383" class="Keyword">open</a> <a id="20388" class="Keyword">import</a> <a id="20395" href="order-theory.decidable-subpreorders.html" class="Module">order-theory.decidable-subpreorders</a>
<a id="20431" class="Keyword">open</a> <a id="20436" class="Keyword">import</a> <a id="20443" href="order-theory.finite-posets.html" class="Module">order-theory.finite-posets</a>
<a id="20470" class="Keyword">open</a> <a id="20475" class="Keyword">import</a> <a id="20482" href="order-theory.finite-preorders.html" class="Module">order-theory.finite-preorders</a>
<a id="20512" class="Keyword">open</a> <a id="20517" class="Keyword">import</a> <a id="20524" href="order-theory.finitely-graded-posets.html" class="Module">order-theory.finitely-graded-posets</a>
<a id="20560" class="Keyword">open</a> <a id="20565" class="Keyword">import</a> <a id="20572" href="order-theory.interval-subposets.html" class="Module">order-theory.interval-subposets</a>
<a id="20604" class="Keyword">open</a> <a id="20609" class="Keyword">import</a> <a id="20616" href="order-theory.largest-elements-posets.html" class="Module">order-theory.largest-elements-posets</a>
<a id="20653" class="Keyword">open</a> <a id="20658" class="Keyword">import</a> <a id="20665" href="order-theory.largest-elements-preorders.html" class="Module">order-theory.largest-elements-preorders</a>
<a id="20705" class="Keyword">open</a> <a id="20710" class="Keyword">import</a> <a id="20717" href="order-theory.least-elements-posets.html" class="Module">order-theory.least-elements-posets</a>
<a id="20752" class="Keyword">open</a> <a id="20757" class="Keyword">import</a> <a id="20764" href="order-theory.least-elements-preorders.html" class="Module">order-theory.least-elements-preorders</a>
<a id="20802" class="Keyword">open</a> <a id="20807" class="Keyword">import</a> <a id="20814" href="order-theory.locally-finite-posets.html" class="Module">order-theory.locally-finite-posets</a>
<a id="20849" class="Keyword">open</a> <a id="20854" class="Keyword">import</a> <a id="20861" href="order-theory.maximal-chains-posets.html" class="Module">order-theory.maximal-chains-posets</a>
<a id="20896" class="Keyword">open</a> <a id="20901" class="Keyword">import</a> <a id="20908" href="order-theory.maximal-chains-preorders.html" class="Module">order-theory.maximal-chains-preorders</a>
<a id="20946" class="Keyword">open</a> <a id="20951" class="Keyword">import</a> <a id="20958" href="order-theory.planar-binary-trees.html" class="Module">order-theory.planar-binary-trees</a>
<a id="20991" class="Keyword">open</a> <a id="20996" class="Keyword">import</a> <a id="21003" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="21023" class="Keyword">open</a> <a id="21028" class="Keyword">import</a> <a id="21035" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
<a id="21058" class="Keyword">open</a> <a id="21063" class="Keyword">import</a> <a id="21070" href="order-theory.subposets.html" class="Module">order-theory.subposets</a>
<a id="21093" class="Keyword">open</a> <a id="21098" class="Keyword">import</a> <a id="21105" href="order-theory.subpreorders.html" class="Module">order-theory.subpreorders</a>
<a id="21131" class="Keyword">open</a> <a id="21136" class="Keyword">import</a> <a id="21143" href="order-theory.total-posets.html" class="Module">order-theory.total-posets</a>
<a id="21169" class="Keyword">open</a> <a id="21174" class="Keyword">import</a> <a id="21181" href="order-theory.total-preorders.html" class="Module">order-theory.total-preorders</a>
</pre>
## Polytopes

<pre class="Agda"><a id="21237" class="Keyword">open</a> <a id="21242" class="Keyword">import</a> <a id="21249" href="polytopes.html" class="Module">polytopes</a>
<a id="21259" class="Keyword">open</a> <a id="21264" class="Keyword">import</a> <a id="21271" href="polytopes.abstract-polytopes.html" class="Module">polytopes.abstract-polytopes</a>
</pre>
## Ring theory

<pre class="Agda"><a id="21329" class="Keyword">open</a> <a id="21334" class="Keyword">import</a> <a id="21341" href="ring-theory.html" class="Module">ring-theory</a>
<a id="21353" class="Keyword">open</a> <a id="21358" class="Keyword">import</a> <a id="21365" href="ring-theory.commutative-rings.html" class="Module">ring-theory.commutative-rings</a>
<a id="21395" class="Keyword">open</a> <a id="21400" class="Keyword">import</a> <a id="21407" href="ring-theory.discrete-fields.html" class="Module">ring-theory.discrete-fields</a>
<a id="21435" class="Keyword">open</a> <a id="21440" class="Keyword">import</a> <a id="21447" href="ring-theory.division-rings.html" class="Module">ring-theory.division-rings</a>
<a id="21474" class="Keyword">open</a> <a id="21479" class="Keyword">import</a> <a id="21486" href="ring-theory.eisenstein-integers.html" class="Module">ring-theory.eisenstein-integers</a>
<a id="21518" class="Keyword">open</a> <a id="21523" class="Keyword">import</a> <a id="21530" href="ring-theory.gaussian-integers.html" class="Module">ring-theory.gaussian-integers</a>
<a id="21560" class="Keyword">open</a> <a id="21565" class="Keyword">import</a> <a id="21572" href="ring-theory.homomorphisms-commutative-rings.html" class="Module">ring-theory.homomorphisms-commutative-rings</a>
<a id="21616" class="Keyword">open</a> <a id="21621" class="Keyword">import</a> <a id="21628" href="ring-theory.homomorphisms-rings.html" class="Module">ring-theory.homomorphisms-rings</a>
<a id="21660" class="Keyword">open</a> <a id="21665" class="Keyword">import</a> <a id="21672" href="ring-theory.ideals.html" class="Module">ring-theory.ideals</a>
<a id="21691" class="Keyword">open</a> <a id="21696" class="Keyword">import</a> <a id="21703" href="ring-theory.invertible-elements-rings.html" class="Module">ring-theory.invertible-elements-rings</a>
<a id="21741" class="Keyword">open</a> <a id="21746" class="Keyword">import</a> <a id="21753" href="ring-theory.isomorphisms-commutative-rings.html" class="Module">ring-theory.isomorphisms-commutative-rings</a>
<a id="21796" class="Keyword">open</a> <a id="21801" class="Keyword">import</a> <a id="21808" href="ring-theory.isomorphisms-rings.html" class="Module">ring-theory.isomorphisms-rings</a>
<a id="21839" class="Keyword">open</a> <a id="21844" class="Keyword">import</a> <a id="21851" href="ring-theory.localizations-rings.html" class="Module">ring-theory.localizations-rings</a>
<a id="21883" class="Keyword">open</a> <a id="21888" class="Keyword">import</a> <a id="21895" href="ring-theory.nontrivial-rings.html" class="Module">ring-theory.nontrivial-rings</a>
<a id="21924" class="Keyword">open</a> <a id="21929" class="Keyword">import</a> <a id="21936" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
## Synthetic homotopy theory

<pre class="Agda"><a id="21997" class="Keyword">open</a> <a id="22002" class="Keyword">import</a> <a id="22009" href="synthetic-homotopy-theory.html" class="Module">synthetic-homotopy-theory</a>
<a id="22035" class="Keyword">open</a> <a id="22040" class="Keyword">import</a> <a id="22047" href="synthetic-homotopy-theory.23-pullbacks.html" class="Module">synthetic-homotopy-theory.23-pullbacks</a>
<a id="22086" class="Keyword">open</a> <a id="22091" class="Keyword">import</a> <a id="22098" href="synthetic-homotopy-theory.24-pushouts.html" class="Module">synthetic-homotopy-theory.24-pushouts</a>
<a id="22136" class="Keyword">open</a> <a id="22141" class="Keyword">import</a> <a id="22148" href="synthetic-homotopy-theory.25-cubical-diagrams.html" class="Module">synthetic-homotopy-theory.25-cubical-diagrams</a>
<a id="22194" class="Keyword">open</a> <a id="22199" class="Keyword">import</a> <a id="22206" href="synthetic-homotopy-theory.26-descent.html" class="Module">synthetic-homotopy-theory.26-descent</a>
<a id="22243" class="Keyword">open</a> <a id="22248" class="Keyword">import</a> <a id="22255" href="synthetic-homotopy-theory.26-id-pushout.html" class="Module">synthetic-homotopy-theory.26-id-pushout</a>
<a id="22295" class="Keyword">open</a> <a id="22300" class="Keyword">import</a> <a id="22307" href="synthetic-homotopy-theory.27-sequences.html" class="Module">synthetic-homotopy-theory.27-sequences</a>
<a id="22346" class="Keyword">open</a> <a id="22351" class="Keyword">import</a> <a id="22358" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
<a id="22391" class="Keyword">open</a> <a id="22396" class="Keyword">import</a> <a id="22403" href="synthetic-homotopy-theory.cyclic-types.html" class="Module">synthetic-homotopy-theory.cyclic-types</a>
<a id="22442" class="Keyword">open</a> <a id="22447" class="Keyword">import</a> <a id="22454" href="synthetic-homotopy-theory.double-loop-spaces.html" class="Module">synthetic-homotopy-theory.double-loop-spaces</a>
<a id="22499" class="Keyword">open</a> <a id="22504" class="Keyword">import</a> <a id="22511" href="synthetic-homotopy-theory.functoriality-loop-spaces.html" class="Module">synthetic-homotopy-theory.functoriality-loop-spaces</a>
<a id="22563" class="Keyword">open</a> <a id="22568" class="Keyword">import</a> <a id="22575" href="synthetic-homotopy-theory.groups-of-loops-in-1-types.html" class="Module">synthetic-homotopy-theory.groups-of-loops-in-1-types</a>
<a id="22628" class="Keyword">open</a> <a id="22633" class="Keyword">import</a> <a id="22640" href="synthetic-homotopy-theory.infinite-cyclic-types.html" class="Module">synthetic-homotopy-theory.infinite-cyclic-types</a>
<a id="22688" class="Keyword">open</a> <a id="22693" class="Keyword">import</a> <a id="22700" href="synthetic-homotopy-theory.interval-type.html" class="Module">synthetic-homotopy-theory.interval-type</a>
<a id="22740" class="Keyword">open</a> <a id="22745" class="Keyword">import</a> <a id="22752" href="synthetic-homotopy-theory.iterated-loop-spaces.html" class="Module">synthetic-homotopy-theory.iterated-loop-spaces</a>
<a id="22799" class="Keyword">open</a> <a id="22804" class="Keyword">import</a> <a id="22811" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
<a id="22849" class="Keyword">open</a> <a id="22854" class="Keyword">import</a> <a id="22861" href="synthetic-homotopy-theory.pointed-dependent-functions.html" class="Module">synthetic-homotopy-theory.pointed-dependent-functions</a>
<a id="22915" class="Keyword">open</a> <a id="22920" class="Keyword">import</a> <a id="22927" href="synthetic-homotopy-theory.pointed-equivalences.html" class="Module">synthetic-homotopy-theory.pointed-equivalences</a>
<a id="22974" class="Keyword">open</a> <a id="22979" class="Keyword">import</a> <a id="22986" href="synthetic-homotopy-theory.pointed-families-of-types.html" class="Module">synthetic-homotopy-theory.pointed-families-of-types</a>
<a id="23038" class="Keyword">open</a> <a id="23043" class="Keyword">import</a> <a id="23050" href="synthetic-homotopy-theory.pointed-homotopies.html" class="Module">synthetic-homotopy-theory.pointed-homotopies</a>
<a id="23095" class="Keyword">open</a> <a id="23100" class="Keyword">import</a> <a id="23107" href="synthetic-homotopy-theory.pointed-maps.html" class="Module">synthetic-homotopy-theory.pointed-maps</a>
<a id="23146" class="Keyword">open</a> <a id="23151" class="Keyword">import</a> <a id="23158" href="synthetic-homotopy-theory.pointed-types.html" class="Module">synthetic-homotopy-theory.pointed-types</a>
<a id="23198" class="Keyword">open</a> <a id="23203" class="Keyword">import</a> <a id="23210" href="synthetic-homotopy-theory.spaces.html" class="Module">synthetic-homotopy-theory.spaces</a>
<a id="23243" class="Keyword">open</a> <a id="23248" class="Keyword">import</a> <a id="23255" href="synthetic-homotopy-theory.triple-loop-spaces.html" class="Module">synthetic-homotopy-theory.triple-loop-spaces</a>
<a id="23300" class="Keyword">open</a> <a id="23305" class="Keyword">import</a> <a id="23312" href="synthetic-homotopy-theory.universal-cover-circle.html" class="Module">synthetic-homotopy-theory.universal-cover-circle</a>
</pre>
## Tutorials

<pre class="Agda"><a id="23388" class="Keyword">open</a> <a id="23393" class="Keyword">import</a> <a id="23400" href="tutorials.basic-agda.html" class="Module">tutorials.basic-agda</a>
</pre>
## Univalent combinatorics

<pre class="Agda"><a id="23462" class="Keyword">open</a> <a id="23467" class="Keyword">import</a> <a id="23474" href="univalent-combinatorics.html" class="Module">univalent-combinatorics</a>
<a id="23498" class="Keyword">open</a> <a id="23503" class="Keyword">import</a> <a id="23510" href="univalent-combinatorics.2-element-subtypes.html" class="Module">univalent-combinatorics.2-element-subtypes</a>
<a id="23553" class="Keyword">open</a> <a id="23558" class="Keyword">import</a> <a id="23565" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="23605" class="Keyword">open</a> <a id="23610" class="Keyword">import</a> <a id="23617" href="univalent-combinatorics.binomial-types.html" class="Module">univalent-combinatorics.binomial-types</a>
<a id="23656" class="Keyword">open</a> <a id="23661" class="Keyword">import</a> <a id="23668" href="univalent-combinatorics.cartesian-product-types.html" class="Module">univalent-combinatorics.cartesian-product-types</a>
<a id="23716" class="Keyword">open</a> <a id="23721" class="Keyword">import</a> <a id="23728" href="univalent-combinatorics.classical-finite-types.html" class="Module">univalent-combinatorics.classical-finite-types</a>
<a id="23775" class="Keyword">open</a> <a id="23780" class="Keyword">import</a> <a id="23787" href="univalent-combinatorics.complements-isolated-points.html" class="Module">univalent-combinatorics.complements-isolated-points</a>
<a id="23839" class="Keyword">open</a> <a id="23844" class="Keyword">import</a> <a id="23851" href="univalent-combinatorics.coproduct-types.html" class="Module">univalent-combinatorics.coproduct-types</a>
<a id="23891" class="Keyword">open</a> <a id="23896" class="Keyword">import</a> <a id="23903" href="univalent-combinatorics.counting-decidable-subtypes.html" class="Module">univalent-combinatorics.counting-decidable-subtypes</a>
<a id="23955" class="Keyword">open</a> <a id="23960" class="Keyword">import</a> <a id="23967" href="univalent-combinatorics.counting-dependent-function-types.html" class="Module">univalent-combinatorics.counting-dependent-function-types</a>
<a id="24025" class="Keyword">open</a> <a id="24030" class="Keyword">import</a> <a id="24037" href="univalent-combinatorics.counting-dependent-pair-types.html" class="Module">univalent-combinatorics.counting-dependent-pair-types</a>
<a id="24091" class="Keyword">open</a> <a id="24096" class="Keyword">import</a> <a id="24103" href="univalent-combinatorics.counting-fibers-of-maps.html" class="Module">univalent-combinatorics.counting-fibers-of-maps</a>
<a id="24151" class="Keyword">open</a> <a id="24156" class="Keyword">import</a> <a id="24163" href="univalent-combinatorics.counting-function-types.html" class="Module">univalent-combinatorics.counting-function-types</a>
<a id="24211" class="Keyword">open</a> <a id="24216" class="Keyword">import</a> <a id="24223" href="univalent-combinatorics.counting-maybe.html" class="Module">univalent-combinatorics.counting-maybe</a>
<a id="24262" class="Keyword">open</a> <a id="24267" class="Keyword">import</a> <a id="24274" href="univalent-combinatorics.counting.html" class="Module">univalent-combinatorics.counting</a>
<a id="24307" class="Keyword">open</a> <a id="24312" class="Keyword">import</a> <a id="24319" href="univalent-combinatorics.cubes.html" class="Module">univalent-combinatorics.cubes</a>
<a id="24349" class="Keyword">open</a> <a id="24354" class="Keyword">import</a> <a id="24361" href="univalent-combinatorics.decidable-dependent-function-types.html" class="Module">univalent-combinatorics.decidable-dependent-function-types</a>
<a id="24420" class="Keyword">open</a> <a id="24425" class="Keyword">import</a> <a id="24432" href="univalent-combinatorics.decidable-dependent-pair-types.html" class="Module">univalent-combinatorics.decidable-dependent-pair-types</a>
<a id="24487" class="Keyword">open</a> <a id="24492" class="Keyword">import</a> <a id="24499" href="univalent-combinatorics.decidable-subtypes.html" class="Module">univalent-combinatorics.decidable-subtypes</a>
<a id="24542" class="Keyword">open</a> <a id="24547" class="Keyword">import</a> <a id="24554" href="univalent-combinatorics.dependent-product-finite-types.html" class="Module">univalent-combinatorics.dependent-product-finite-types</a>
<a id="24609" class="Keyword">open</a> <a id="24614" class="Keyword">import</a> <a id="24621" href="univalent-combinatorics.dependent-sum-finite-types.html" class="Module">univalent-combinatorics.dependent-sum-finite-types</a>
<a id="24672" class="Keyword">open</a> <a id="24677" class="Keyword">import</a> <a id="24684" href="univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.html" class="Module">univalent-combinatorics.distributivity-of-set-truncation-over-finite-products</a>
<a id="24762" class="Keyword">open</a> <a id="24767" class="Keyword">import</a> <a id="24774" href="univalent-combinatorics.double-counting.html" class="Module">univalent-combinatorics.double-counting</a>
<a id="24814" class="Keyword">open</a> <a id="24819" class="Keyword">import</a> <a id="24826" href="univalent-combinatorics.embeddings-standard-finite-types.html" class="Module">univalent-combinatorics.embeddings-standard-finite-types</a>
<a id="24883" class="Keyword">open</a> <a id="24888" class="Keyword">import</a> <a id="24895" href="univalent-combinatorics.embeddings.html" class="Module">univalent-combinatorics.embeddings</a>
<a id="24930" class="Keyword">open</a> <a id="24935" class="Keyword">import</a> <a id="24942" href="univalent-combinatorics.equality-finite-types.html" class="Module">univalent-combinatorics.equality-finite-types</a>
<a id="24988" class="Keyword">open</a> <a id="24993" class="Keyword">import</a> <a id="25000" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a>
<a id="25055" class="Keyword">open</a> <a id="25060" class="Keyword">import</a> <a id="25067" href="univalent-combinatorics.equivalences-cubes.html" class="Module">univalent-combinatorics.equivalences-cubes</a>
<a id="25110" class="Keyword">open</a> <a id="25115" class="Keyword">import</a> <a id="25122" href="univalent-combinatorics.equivalences-standard-finite-types.html" class="Module">univalent-combinatorics.equivalences-standard-finite-types</a>
<a id="25181" class="Keyword">open</a> <a id="25186" class="Keyword">import</a> <a id="25193" href="univalent-combinatorics.equivalences.html" class="Module">univalent-combinatorics.equivalences</a>
<a id="25230" class="Keyword">open</a> <a id="25235" class="Keyword">import</a> <a id="25242" href="univalent-combinatorics.fibers-of-maps-between-finite-types.html" class="Module">univalent-combinatorics.fibers-of-maps-between-finite-types</a>
<a id="25302" class="Keyword">open</a> <a id="25307" class="Keyword">import</a> <a id="25314" href="univalent-combinatorics.finite-choice.html" class="Module">univalent-combinatorics.finite-choice</a>
<a id="25352" class="Keyword">open</a> <a id="25357" class="Keyword">import</a> <a id="25364" href="univalent-combinatorics.finite-connected-components.html" class="Module">univalent-combinatorics.finite-connected-components</a>
<a id="25416" class="Keyword">open</a> <a id="25421" class="Keyword">import</a> <a id="25428" href="univalent-combinatorics.finite-function-types.html" class="Module">univalent-combinatorics.finite-function-types</a>
<a id="25474" class="Keyword">open</a> <a id="25479" class="Keyword">import</a> <a id="25486" href="univalent-combinatorics.finite-presentations.html" class="Module">univalent-combinatorics.finite-presentations</a>
<a id="25531" class="Keyword">open</a> <a id="25536" class="Keyword">import</a> <a id="25543" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="25580" class="Keyword">open</a> <a id="25585" class="Keyword">import</a> <a id="25592" href="univalent-combinatorics.finitely-presented-types.html" class="Module">univalent-combinatorics.finitely-presented-types</a>
<a id="25641" class="Keyword">open</a> <a id="25646" class="Keyword">import</a> <a id="25653" href="univalent-combinatorics.image-of-maps.html" class="Module">univalent-combinatorics.image-of-maps</a>
<a id="25691" class="Keyword">open</a> <a id="25696" class="Keyword">import</a> <a id="25703" href="univalent-combinatorics.inequality-types-with-counting.html" class="Module">univalent-combinatorics.inequality-types-with-counting</a>
<a id="25758" class="Keyword">open</a> <a id="25763" class="Keyword">import</a> <a id="25770" href="univalent-combinatorics.injective-maps.html" class="Module">univalent-combinatorics.injective-maps</a>
<a id="25809" class="Keyword">open</a> <a id="25814" class="Keyword">import</a> <a id="25821" href="univalent-combinatorics.lists.html" class="Module">univalent-combinatorics.lists</a>
<a id="25851" class="Keyword">open</a> <a id="25856" class="Keyword">import</a> <a id="25863" href="univalent-combinatorics.maybe.html" class="Module">univalent-combinatorics.maybe</a>
<a id="25893" class="Keyword">open</a> <a id="25898" class="Keyword">import</a> <a id="25905" href="univalent-combinatorics.orientations-cubes.html" class="Module">univalent-combinatorics.orientations-cubes</a>
<a id="25948" class="Keyword">open</a> <a id="25953" class="Keyword">import</a> <a id="25960" href="univalent-combinatorics.pi-finite-types.html" class="Module">univalent-combinatorics.pi-finite-types</a>
<a id="26000" class="Keyword">open</a> <a id="26005" class="Keyword">import</a> <a id="26012" href="univalent-combinatorics.pigeonhole-principle.html" class="Module">univalent-combinatorics.pigeonhole-principle</a>
<a id="26057" class="Keyword">open</a> <a id="26062" class="Keyword">import</a> <a id="26069" href="univalent-combinatorics.presented-pi-finite-types.html" class="Module">univalent-combinatorics.presented-pi-finite-types</a>
<a id="26119" class="Keyword">open</a> <a id="26124" class="Keyword">import</a> <a id="26131" href="univalent-combinatorics.ramsey-theory.html" class="Module">univalent-combinatorics.ramsey-theory</a>
<a id="26169" class="Keyword">open</a> <a id="26174" class="Keyword">import</a> <a id="26181" href="univalent-combinatorics.retracts-of-finite-types.html" class="Module">univalent-combinatorics.retracts-of-finite-types</a>
<a id="26230" class="Keyword">open</a> <a id="26235" class="Keyword">import</a> <a id="26242" href="univalent-combinatorics.skipping-element-standard-finite-types.html" class="Module">univalent-combinatorics.skipping-element-standard-finite-types</a>
<a id="26305" class="Keyword">open</a> <a id="26310" class="Keyword">import</a> <a id="26317" href="univalent-combinatorics.species.html" class="Module">univalent-combinatorics.species</a>
<a id="26349" class="Keyword">open</a> <a id="26354" class="Keyword">import</a> <a id="26361" href="univalent-combinatorics.standard-finite-pruned-trees.html" class="Module">univalent-combinatorics.standard-finite-pruned-trees</a>
<a id="26414" class="Keyword">open</a> <a id="26419" class="Keyword">import</a> <a id="26426" href="univalent-combinatorics.standard-finite-trees.html" class="Module">univalent-combinatorics.standard-finite-trees</a>
<a id="26472" class="Keyword">open</a> <a id="26477" class="Keyword">import</a> <a id="26484" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
<a id="26530" class="Keyword">open</a> <a id="26535" class="Keyword">import</a> <a id="26542" href="univalent-combinatorics.sums-of-natural-numbers.html" class="Module">univalent-combinatorics.sums-of-natural-numbers</a>
<a id="26590" class="Keyword">open</a> <a id="26595" class="Keyword">import</a> <a id="26602" href="univalent-combinatorics.surjective-maps.html" class="Module">univalent-combinatorics.surjective-maps</a>
</pre>
## Wild algebra

<pre class="Agda"><a id="26672" class="Keyword">open</a> <a id="26677" class="Keyword">import</a> <a id="26684" href="wild-algebra.html" class="Module">wild-algebra</a>
<a id="26697" class="Keyword">open</a> <a id="26702" class="Keyword">import</a> <a id="26709" href="wild-algebra.magmas.html" class="Module">wild-algebra.magmas</a>
<a id="26729" class="Keyword">open</a> <a id="26734" class="Keyword">import</a> <a id="26741" href="wild-algebra.universal-property-lists-wild-monoids.html" class="Module">wild-algebra.universal-property-lists-wild-monoids</a>
<a id="26792" class="Keyword">open</a> <a id="26797" class="Keyword">import</a> <a id="26804" href="wild-algebra.wild-groups.html" class="Module">wild-algebra.wild-groups</a>
<a id="26829" class="Keyword">open</a> <a id="26834" class="Keyword">import</a> <a id="26841" href="wild-algebra.wild-monoids.html" class="Module">wild-algebra.wild-monoids</a>
<a id="26867" class="Keyword">open</a> <a id="26872" class="Keyword">import</a> <a id="26879" href="wild-algebra.wild-unital-magmas.html" class="Module">wild-algebra.wild-unital-magmas</a>
</pre>
## Everything

See the list of all Agda modules [here](everything.html).

