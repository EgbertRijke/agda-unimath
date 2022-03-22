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
</pre>
## Elementary number theory

<pre class="Agda"><a id="1847" class="Keyword">open</a> <a id="1852" class="Keyword">import</a> <a id="1859" href="elementary-number-theory.html" class="Module">elementary-number-theory</a>
<a id="1884" class="Keyword">open</a> <a id="1889" class="Keyword">import</a> <a id="1896" href="elementary-number-theory.absolute-value-integers.html" class="Module">elementary-number-theory.absolute-value-integers</a>
<a id="1945" class="Keyword">open</a> <a id="1950" class="Keyword">import</a> <a id="1957" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a>
<a id="2000" class="Keyword">open</a> <a id="2005" class="Keyword">import</a> <a id="2012" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="2062" class="Keyword">open</a> <a id="2067" class="Keyword">import</a> <a id="2074" href="elementary-number-theory.arithmetic-functions.html" class="Module">elementary-number-theory.arithmetic-functions</a>
<a id="2120" class="Keyword">open</a> <a id="2125" class="Keyword">import</a> <a id="2132" href="elementary-number-theory.binomial-coefficients.html" class="Module">elementary-number-theory.binomial-coefficients</a>
<a id="2179" class="Keyword">open</a> <a id="2184" class="Keyword">import</a> <a id="2191" href="elementary-number-theory.bounded-sums-arithmetic-functions.html" class="Module">elementary-number-theory.bounded-sums-arithmetic-functions</a>
<a id="2250" class="Keyword">open</a> <a id="2255" class="Keyword">import</a> <a id="2262" href="elementary-number-theory.catalan-numbers.html" class="Module">elementary-number-theory.catalan-numbers</a>
<a id="2303" class="Keyword">open</a> <a id="2308" class="Keyword">import</a> <a id="2315" href="elementary-number-theory.collatz-bijection.html" class="Module">elementary-number-theory.collatz-bijection</a>
<a id="2358" class="Keyword">open</a> <a id="2363" class="Keyword">import</a> <a id="2370" href="elementary-number-theory.collatz-conjecture.html" class="Module">elementary-number-theory.collatz-conjecture</a>
<a id="2414" class="Keyword">open</a> <a id="2419" class="Keyword">import</a> <a id="2426" href="elementary-number-theory.congruence-integers.html" class="Module">elementary-number-theory.congruence-integers</a>
<a id="2471" class="Keyword">open</a> <a id="2476" class="Keyword">import</a> <a id="2483" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a>
<a id="2535" class="Keyword">open</a> <a id="2540" class="Keyword">import</a> <a id="2547" href="elementary-number-theory.decidable-dependent-function-types.html" class="Module">elementary-number-theory.decidable-dependent-function-types</a>
<a id="2607" class="Keyword">open</a> <a id="2612" class="Keyword">import</a> <a id="2619" href="elementary-number-theory.decidable-types.html" class="Module">elementary-number-theory.decidable-types</a>
<a id="2660" class="Keyword">open</a> <a id="2665" class="Keyword">import</a> <a id="2672" href="elementary-number-theory.difference-integers.html" class="Module">elementary-number-theory.difference-integers</a>
<a id="2717" class="Keyword">open</a> <a id="2722" class="Keyword">import</a> <a id="2729" href="elementary-number-theory.dirichlet-convolution.html" class="Module">elementary-number-theory.dirichlet-convolution</a>
<a id="2776" class="Keyword">open</a> <a id="2781" class="Keyword">import</a> <a id="2788" href="elementary-number-theory.distance-integers.html" class="Module">elementary-number-theory.distance-integers</a>
<a id="2831" class="Keyword">open</a> <a id="2836" class="Keyword">import</a> <a id="2843" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a>
<a id="2893" class="Keyword">open</a> <a id="2898" class="Keyword">import</a> <a id="2905" href="elementary-number-theory.divisibility-integers.html" class="Module">elementary-number-theory.divisibility-integers</a>
<a id="2952" class="Keyword">open</a> <a id="2957" class="Keyword">import</a> <a id="2964" href="elementary-number-theory.divisibility-modular-arithmetic.html" class="Module">elementary-number-theory.divisibility-modular-arithmetic</a>
<a id="3021" class="Keyword">open</a> <a id="3026" class="Keyword">import</a> <a id="3033" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a>
<a id="3087" class="Keyword">open</a> <a id="3092" class="Keyword">import</a> <a id="3099" href="elementary-number-theory.divisibility-standard-finite-types.html" class="Module">elementary-number-theory.divisibility-standard-finite-types</a>
<a id="3159" class="Keyword">open</a> <a id="3164" class="Keyword">import</a> <a id="3171" href="elementary-number-theory.equality-integers.html" class="Module">elementary-number-theory.equality-integers</a>
<a id="3214" class="Keyword">open</a> <a id="3219" class="Keyword">import</a> <a id="3226" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a>
<a id="3276" class="Keyword">open</a> <a id="3281" class="Keyword">import</a> <a id="3288" href="elementary-number-theory.euclidean-division-natural-numbers.html" class="Module">elementary-number-theory.euclidean-division-natural-numbers</a>
<a id="3348" class="Keyword">open</a> <a id="3353" class="Keyword">import</a> <a id="3360" href="elementary-number-theory.eulers-totient-function.html" class="Module">elementary-number-theory.eulers-totient-function</a>
<a id="3409" class="Keyword">open</a> <a id="3414" class="Keyword">import</a> <a id="3421" href="elementary-number-theory.exponentiation-natural-numbers.html" class="Module">elementary-number-theory.exponentiation-natural-numbers</a>
<a id="3477" class="Keyword">open</a> <a id="3482" class="Keyword">import</a> <a id="3489" href="elementary-number-theory.factorials.html" class="Module">elementary-number-theory.factorials</a>
<a id="3525" class="Keyword">open</a> <a id="3530" class="Keyword">import</a> <a id="3537" href="elementary-number-theory.falling-factorials.html" class="Module">elementary-number-theory.falling-factorials</a>
<a id="3581" class="Keyword">open</a> <a id="3586" class="Keyword">import</a> <a id="3593" href="elementary-number-theory.fibonacci-sequence.html" class="Module">elementary-number-theory.fibonacci-sequence</a>
<a id="3637" class="Keyword">open</a> <a id="3642" class="Keyword">import</a> <a id="3649" href="elementary-number-theory.finitary-natural-numbers.html" class="Module">elementary-number-theory.finitary-natural-numbers</a>
<a id="3699" class="Keyword">open</a> <a id="3704" class="Keyword">import</a> <a id="3711" href="elementary-number-theory.finitely-cyclic-maps.html" class="Module">elementary-number-theory.finitely-cyclic-maps</a>
<a id="3757" class="Keyword">open</a> <a id="3762" class="Keyword">import</a> <a id="3769" href="elementary-number-theory.fractions.html" class="Module">elementary-number-theory.fractions</a>
<a id="3804" class="Keyword">open</a> <a id="3809" class="Keyword">import</a> <a id="3816" href="elementary-number-theory.goldbach-conjecture.html" class="Module">elementary-number-theory.goldbach-conjecture</a>
<a id="3861" class="Keyword">open</a> <a id="3866" class="Keyword">import</a> <a id="3873" href="elementary-number-theory.greatest-common-divisor-integers.html" class="Module">elementary-number-theory.greatest-common-divisor-integers</a>
<a id="3931" class="Keyword">open</a> <a id="3936" class="Keyword">import</a> <a id="3943" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a>
<a id="4008" class="Keyword">open</a> <a id="4013" class="Keyword">import</a> <a id="4020" href="elementary-number-theory.group-of-integers.html" class="Module">elementary-number-theory.group-of-integers</a>
<a id="4063" class="Keyword">open</a> <a id="4068" class="Keyword">import</a> <a id="4075" href="elementary-number-theory.groups-of-modular-arithmetic.html" class="Module">elementary-number-theory.groups-of-modular-arithmetic</a>
<a id="4129" class="Keyword">open</a> <a id="4134" class="Keyword">import</a> <a id="4141" href="elementary-number-theory.inequality-integers.html" class="Module">elementary-number-theory.inequality-integers</a>
<a id="4186" class="Keyword">open</a> <a id="4191" class="Keyword">import</a> <a id="4198" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a>
<a id="4250" class="Keyword">open</a> <a id="4255" class="Keyword">import</a> <a id="4262" href="elementary-number-theory.inequality-standard-finite-types.html" class="Module">elementary-number-theory.inequality-standard-finite-types</a>
<a id="4320" class="Keyword">open</a> <a id="4325" class="Keyword">import</a> <a id="4332" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a>
<a id="4378" class="Keyword">open</a> <a id="4383" class="Keyword">import</a> <a id="4390" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="4424" class="Keyword">open</a> <a id="4429" class="Keyword">import</a> <a id="4436" href="elementary-number-theory.iterating-functions.html" class="Module">elementary-number-theory.iterating-functions</a>
<a id="4481" class="Keyword">open</a> <a id="4486" class="Keyword">import</a> <a id="4493" href="elementary-number-theory.lower-bounds-natural-numbers.html" class="Module">elementary-number-theory.lower-bounds-natural-numbers</a>
<a id="4547" class="Keyword">open</a> <a id="4552" class="Keyword">import</a> <a id="4559" href="elementary-number-theory.maximum-natural-numbers.html" class="Module">elementary-number-theory.maximum-natural-numbers</a>
<a id="4608" class="Keyword">open</a> <a id="4613" class="Keyword">import</a> <a id="4620" href="elementary-number-theory.mersenne-primes.html" class="Module">elementary-number-theory.mersenne-primes</a>
<a id="4661" class="Keyword">open</a> <a id="4666" class="Keyword">import</a> <a id="4673" href="elementary-number-theory.minimum-natural-numbers.html" class="Module">elementary-number-theory.minimum-natural-numbers</a>
<a id="4722" class="Keyword">open</a> <a id="4727" class="Keyword">import</a> <a id="4734" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a>
<a id="4800" class="Keyword">open</a> <a id="4805" class="Keyword">import</a> <a id="4812" href="elementary-number-theory.modular-arithmetic.html" class="Module">elementary-number-theory.modular-arithmetic</a>
<a id="4856" class="Keyword">open</a> <a id="4861" class="Keyword">import</a> <a id="4868" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a>
<a id="4917" class="Keyword">open</a> <a id="4922" class="Keyword">import</a> <a id="4929" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a>
<a id="4985" class="Keyword">open</a> <a id="4990" class="Keyword">import</a> <a id="4997" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="5038" class="Keyword">open</a> <a id="5043" class="Keyword">import</a> <a id="5050" href="elementary-number-theory.nonzero-natural-numbers.html" class="Module">elementary-number-theory.nonzero-natural-numbers</a>
<a id="5099" class="Keyword">open</a> <a id="5104" class="Keyword">import</a> <a id="5111" href="elementary-number-theory.ordinal-induction-natural-numbers.html" class="Module">elementary-number-theory.ordinal-induction-natural-numbers</a>
<a id="5170" class="Keyword">open</a> <a id="5175" class="Keyword">import</a> <a id="5182" href="elementary-number-theory.prime-numbers.html" class="Module">elementary-number-theory.prime-numbers</a>
<a id="5221" class="Keyword">open</a> <a id="5226" class="Keyword">import</a> <a id="5233" href="elementary-number-theory.products-of-natural-numbers.html" class="Module">elementary-number-theory.products-of-natural-numbers</a>
<a id="5286" class="Keyword">open</a> <a id="5291" class="Keyword">import</a> <a id="5298" href="elementary-number-theory.proper-divisors-natural-numbers.html" class="Module">elementary-number-theory.proper-divisors-natural-numbers</a>
<a id="5355" class="Keyword">open</a> <a id="5360" class="Keyword">import</a> <a id="5367" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a>
<a id="5409" class="Keyword">open</a> <a id="5414" class="Keyword">import</a> <a id="5421" href="elementary-number-theory.relatively-prime-integers.html" class="Module">elementary-number-theory.relatively-prime-integers</a>
<a id="5472" class="Keyword">open</a> <a id="5477" class="Keyword">import</a> <a id="5484" href="elementary-number-theory.relatively-prime-natural-numbers.html" class="Module">elementary-number-theory.relatively-prime-natural-numbers</a>
<a id="5542" class="Keyword">open</a> <a id="5547" class="Keyword">import</a> <a id="5554" href="elementary-number-theory.repeating-element-standard-finite-type.html" class="Module">elementary-number-theory.repeating-element-standard-finite-type</a>
<a id="5618" class="Keyword">open</a> <a id="5623" class="Keyword">import</a> <a id="5630" href="elementary-number-theory.retracts-of-natural-numbers.html" class="Module">elementary-number-theory.retracts-of-natural-numbers</a>
<a id="5683" class="Keyword">open</a> <a id="5688" class="Keyword">import</a> <a id="5695" href="elementary-number-theory.square-free-natural-numbers.html" class="Module">elementary-number-theory.square-free-natural-numbers</a>
<a id="5748" class="Keyword">open</a> <a id="5753" class="Keyword">import</a> <a id="5760" href="elementary-number-theory.stirling-numbers-of-the-second-kind.html" class="Module">elementary-number-theory.stirling-numbers-of-the-second-kind</a>
<a id="5821" class="Keyword">open</a> <a id="5826" class="Keyword">import</a> <a id="5833" href="elementary-number-theory.strong-induction-natural-numbers.html" class="Module">elementary-number-theory.strong-induction-natural-numbers</a>
<a id="5891" class="Keyword">open</a> <a id="5896" class="Keyword">import</a> <a id="5903" href="elementary-number-theory.sums-of-natural-numbers.html" class="Module">elementary-number-theory.sums-of-natural-numbers</a>
<a id="5952" class="Keyword">open</a> <a id="5957" class="Keyword">import</a> <a id="5964" href="elementary-number-theory.triangular-numbers.html" class="Module">elementary-number-theory.triangular-numbers</a>
<a id="6008" class="Keyword">open</a> <a id="6013" class="Keyword">import</a> <a id="6020" href="elementary-number-theory.twin-prime-conjecture.html" class="Module">elementary-number-theory.twin-prime-conjecture</a>
<a id="6067" class="Keyword">open</a> <a id="6072" class="Keyword">import</a> <a id="6079" href="elementary-number-theory.unit-elements-standard-finite-types.html" class="Module">elementary-number-theory.unit-elements-standard-finite-types</a>
<a id="6140" class="Keyword">open</a> <a id="6145" class="Keyword">import</a> <a id="6152" href="elementary-number-theory.unit-similarity-standard-finite-types.html" class="Module">elementary-number-theory.unit-similarity-standard-finite-types</a>
<a id="6215" class="Keyword">open</a> <a id="6220" class="Keyword">import</a> <a id="6227" href="elementary-number-theory.universal-property-natural-numbers.html" class="Module">elementary-number-theory.universal-property-natural-numbers</a>
<a id="6287" class="Keyword">open</a> <a id="6292" class="Keyword">import</a> <a id="6299" href="elementary-number-theory.upper-bounds-natural-numbers.html" class="Module">elementary-number-theory.upper-bounds-natural-numbers</a>
<a id="6353" class="Keyword">open</a> <a id="6358" class="Keyword">import</a> <a id="6365" href="elementary-number-theory.well-ordering-principle-natural-numbers.html" class="Module">elementary-number-theory.well-ordering-principle-natural-numbers</a>
<a id="6430" class="Keyword">open</a> <a id="6435" class="Keyword">import</a> <a id="6442" href="elementary-number-theory.well-ordering-principle-standard-finite-types.html" class="Module">elementary-number-theory.well-ordering-principle-standard-finite-types</a>
</pre>
## Finite group theory

<pre class="Agda"><a id="6550" class="Keyword">open</a> <a id="6555" class="Keyword">import</a> <a id="6562" href="finite-group-theory.html" class="Module">finite-group-theory</a>
<a id="6582" class="Keyword">open</a> <a id="6587" class="Keyword">import</a> <a id="6594" href="finite-group-theory.abstract-quaternion-group.html" class="Module">finite-group-theory.abstract-quaternion-group</a>
<a id="6640" class="Keyword">open</a> <a id="6645" class="Keyword">import</a> <a id="6652" href="finite-group-theory.concrete-quaternion-group.html" class="Module">finite-group-theory.concrete-quaternion-group</a>
<a id="6698" class="Keyword">open</a> <a id="6703" class="Keyword">import</a> <a id="6710" href="finite-group-theory.finite-groups.html" class="Module">finite-group-theory.finite-groups</a>
<a id="6744" class="Keyword">open</a> <a id="6749" class="Keyword">import</a> <a id="6756" href="finite-group-theory.orbits-permutations.html" class="Module">finite-group-theory.orbits-permutations</a>
<a id="6796" class="Keyword">open</a> <a id="6801" class="Keyword">import</a> <a id="6808" href="finite-group-theory.transpositions.html" class="Module">finite-group-theory.transpositions</a>
</pre>
## Foundation

<pre class="Agda"><a id="6871" class="Keyword">open</a> <a id="6876" class="Keyword">import</a> <a id="6883" href="foundation.html" class="Module">foundation</a>
<a id="6894" class="Keyword">open</a> <a id="6899" class="Keyword">import</a> <a id="6906" href="foundation.0-maps.html" class="Module">foundation.0-maps</a>
<a id="6924" class="Keyword">open</a> <a id="6929" class="Keyword">import</a> <a id="6936" href="foundation.1-types.html" class="Module">foundation.1-types</a>
<a id="6955" class="Keyword">open</a> <a id="6960" class="Keyword">import</a> <a id="6967" href="foundation.2-types.html" class="Module">foundation.2-types</a>
<a id="6986" class="Keyword">open</a> <a id="6991" class="Keyword">import</a> <a id="6998" href="foundation.algebras-polynomial-endofunctors.html" class="Module">foundation.algebras-polynomial-endofunctors</a>
<a id="7042" class="Keyword">open</a> <a id="7047" class="Keyword">import</a> <a id="7054" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="7079" class="Keyword">open</a> <a id="7084" class="Keyword">import</a> <a id="7091" href="foundation.axiom-of-choice.html" class="Module">foundation.axiom-of-choice</a>
<a id="7118" class="Keyword">open</a> <a id="7123" class="Keyword">import</a> <a id="7130" href="foundation.binary-embeddings.html" class="Module">foundation.binary-embeddings</a>
<a id="7159" class="Keyword">open</a> <a id="7164" class="Keyword">import</a> <a id="7171" href="foundation.binary-equivalences.html" class="Module">foundation.binary-equivalences</a>
<a id="7202" class="Keyword">open</a> <a id="7207" class="Keyword">import</a> <a id="7214" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="7242" class="Keyword">open</a> <a id="7247" class="Keyword">import</a> <a id="7254" href="foundation.boolean-reflection.html" class="Module">foundation.boolean-reflection</a>
<a id="7284" class="Keyword">open</a> <a id="7289" class="Keyword">import</a> <a id="7296" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="7316" class="Keyword">open</a> <a id="7321" class="Keyword">import</a> <a id="7328" href="foundation.cantors-diagonal-argument.html" class="Module">foundation.cantors-diagonal-argument</a>
<a id="7365" class="Keyword">open</a> <a id="7370" class="Keyword">import</a> <a id="7377" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="7412" class="Keyword">open</a> <a id="7417" class="Keyword">import</a> <a id="7424" href="foundation.choice-of-representatives-equivalence-relation.html" class="Module">foundation.choice-of-representatives-equivalence-relation</a>
<a id="7482" class="Keyword">open</a> <a id="7487" class="Keyword">import</a> <a id="7494" href="foundation.coherently-invertible-maps.html" class="Module">foundation.coherently-invertible-maps</a>
<a id="7532" class="Keyword">open</a> <a id="7537" class="Keyword">import</a> <a id="7544" href="foundation.commuting-squares.html" class="Module">foundation.commuting-squares</a>
<a id="7573" class="Keyword">open</a> <a id="7578" class="Keyword">import</a> <a id="7585" href="foundation.complements.html" class="Module">foundation.complements</a>
<a id="7608" class="Keyword">open</a> <a id="7613" class="Keyword">import</a> <a id="7620" href="foundation.conjunction.html" class="Module">foundation.conjunction</a>
<a id="7643" class="Keyword">open</a> <a id="7648" class="Keyword">import</a> <a id="7655" href="foundation.connected-components-universes.html" class="Module">foundation.connected-components-universes</a>
<a id="7697" class="Keyword">open</a> <a id="7702" class="Keyword">import</a> <a id="7709" href="foundation.connected-components.html" class="Module">foundation.connected-components</a>
<a id="7741" class="Keyword">open</a> <a id="7746" class="Keyword">import</a> <a id="7753" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="7780" class="Keyword">open</a> <a id="7785" class="Keyword">import</a> <a id="7792" href="foundation.constant-maps.html" class="Module">foundation.constant-maps</a>
<a id="7817" class="Keyword">open</a> <a id="7822" class="Keyword">import</a> <a id="7829" href="foundation.contractible-maps.html" class="Module">foundation.contractible-maps</a>
<a id="7858" class="Keyword">open</a> <a id="7863" class="Keyword">import</a> <a id="7870" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="7900" class="Keyword">open</a> <a id="7905" class="Keyword">import</a> <a id="7912" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="7939" class="Keyword">open</a> <a id="7944" class="Keyword">import</a> <a id="7951" href="foundation.coslice.html" class="Module">foundation.coslice</a>
<a id="7970" class="Keyword">open</a> <a id="7975" class="Keyword">import</a> <a id="7982" href="foundation.decidable-dependent-function-types.html" class="Module">foundation.decidable-dependent-function-types</a>
<a id="8028" class="Keyword">open</a> <a id="8033" class="Keyword">import</a> <a id="8040" href="foundation.decidable-dependent-pair-types.html" class="Module">foundation.decidable-dependent-pair-types</a>
<a id="8082" class="Keyword">open</a> <a id="8087" class="Keyword">import</a> <a id="8094" href="foundation.decidable-embeddings.html" class="Module">foundation.decidable-embeddings</a>
<a id="8126" class="Keyword">open</a> <a id="8131" class="Keyword">import</a> <a id="8138" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a>
<a id="8168" class="Keyword">open</a> <a id="8173" class="Keyword">import</a> <a id="8180" href="foundation.decidable-maps.html" class="Module">foundation.decidable-maps</a>
<a id="8206" class="Keyword">open</a> <a id="8211" class="Keyword">import</a> <a id="8218" href="foundation.decidable-propositions.html" class="Module">foundation.decidable-propositions</a>
<a id="8252" class="Keyword">open</a> <a id="8257" class="Keyword">import</a> <a id="8264" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="8294" class="Keyword">open</a> <a id="8299" class="Keyword">import</a> <a id="8306" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="8333" class="Keyword">open</a> <a id="8338" class="Keyword">import</a> <a id="8345" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="8377" class="Keyword">open</a> <a id="8382" class="Keyword">import</a> <a id="8389" href="foundation.diagonal-maps-of-types.html" class="Module">foundation.diagonal-maps-of-types</a>
<a id="8423" class="Keyword">open</a> <a id="8428" class="Keyword">import</a> <a id="8435" href="foundation.disjunction.html" class="Module">foundation.disjunction</a>
<a id="8458" class="Keyword">open</a> <a id="8463" class="Keyword">import</a> <a id="8470" href="foundation.distributivity-of-dependent-functions-over-coproduct-types.html" class="Module">foundation.distributivity-of-dependent-functions-over-coproduct-types</a>
<a id="8540" class="Keyword">open</a> <a id="8545" class="Keyword">import</a> <a id="8552" href="foundation.distributivity-of-dependent-functions-over-dependent-pairs.html" class="Module">foundation.distributivity-of-dependent-functions-over-dependent-pairs</a>
<a id="8622" class="Keyword">open</a> <a id="8627" class="Keyword">import</a> <a id="8634" href="foundation.double-negation.html" class="Module">foundation.double-negation</a>
<a id="8661" class="Keyword">open</a> <a id="8666" class="Keyword">import</a> <a id="8673" href="foundation.effective-maps-equivalence-relations.html" class="Module">foundation.effective-maps-equivalence-relations</a>
<a id="8721" class="Keyword">open</a> <a id="8726" class="Keyword">import</a> <a id="8733" href="foundation.elementhood-relation-w-types.html" class="Module">foundation.elementhood-relation-w-types</a>
<a id="8773" class="Keyword">open</a> <a id="8778" class="Keyword">import</a> <a id="8785" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="8807" class="Keyword">open</a> <a id="8812" class="Keyword">import</a> <a id="8819" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="8842" class="Keyword">open</a> <a id="8847" class="Keyword">import</a> <a id="8854" href="foundation.epimorphisms-with-respect-to-sets.html" class="Module">foundation.epimorphisms-with-respect-to-sets</a>
<a id="8899" class="Keyword">open</a> <a id="8904" class="Keyword">import</a> <a id="8911" href="foundation.equality-cartesian-product-types.html" class="Module">foundation.equality-cartesian-product-types</a>
<a id="8955" class="Keyword">open</a> <a id="8960" class="Keyword">import</a> <a id="8967" href="foundation.equality-coproduct-types.html" class="Module">foundation.equality-coproduct-types</a>
<a id="9003" class="Keyword">open</a> <a id="9008" class="Keyword">import</a> <a id="9015" href="foundation.equality-dependent-function-types.html" class="Module">foundation.equality-dependent-function-types</a>
<a id="9060" class="Keyword">open</a> <a id="9065" class="Keyword">import</a> <a id="9072" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="9113" class="Keyword">open</a> <a id="9118" class="Keyword">import</a> <a id="9125" href="foundation.equality-fibers-of-maps.html" class="Module">foundation.equality-fibers-of-maps</a>
<a id="9160" class="Keyword">open</a> <a id="9165" class="Keyword">import</a> <a id="9172" href="foundation.equivalence-classes.html" class="Module">foundation.equivalence-classes</a>
<a id="9203" class="Keyword">open</a> <a id="9208" class="Keyword">import</a> <a id="9215" href="foundation.equivalence-induction.html" class="Module">foundation.equivalence-induction</a>
<a id="9248" class="Keyword">open</a> <a id="9253" class="Keyword">import</a> <a id="9260" href="foundation.equivalence-relations.html" class="Module">foundation.equivalence-relations</a>
<a id="9293" class="Keyword">open</a> <a id="9298" class="Keyword">import</a> <a id="9305" href="foundation.equivalences-maybe.html" class="Module">foundation.equivalences-maybe</a>
<a id="9335" class="Keyword">open</a> <a id="9340" class="Keyword">import</a> <a id="9347" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="9371" class="Keyword">open</a> <a id="9376" class="Keyword">import</a> <a id="9383" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="9421" class="Keyword">open</a> <a id="9426" class="Keyword">import</a> <a id="9433" href="foundation.extensional-w-types.html" class="Module">foundation.extensional-w-types</a>
<a id="9464" class="Keyword">open</a> <a id="9469" class="Keyword">import</a> <a id="9476" href="foundation.faithful-maps.html" class="Module">foundation.faithful-maps</a>
<a id="9501" class="Keyword">open</a> <a id="9506" class="Keyword">import</a> <a id="9513" href="foundation.fiber-inclusions.html" class="Module">foundation.fiber-inclusions</a>
<a id="9541" class="Keyword">open</a> <a id="9546" class="Keyword">import</a> <a id="9553" href="foundation.fibered-maps.html" class="Module">foundation.fibered-maps</a>
<a id="9577" class="Keyword">open</a> <a id="9582" class="Keyword">import</a> <a id="9589" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="9615" class="Keyword">open</a> <a id="9620" class="Keyword">import</a> <a id="9627" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="9662" class="Keyword">open</a> <a id="9667" class="Keyword">import</a> <a id="9674" href="foundation.functions.html" class="Module">foundation.functions</a>
<a id="9695" class="Keyword">open</a> <a id="9700" class="Keyword">import</a> <a id="9707" href="foundation.functoriality-cartesian-product-types.html" class="Module">foundation.functoriality-cartesian-product-types</a>
<a id="9756" class="Keyword">open</a> <a id="9761" class="Keyword">import</a> <a id="9768" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="9809" class="Keyword">open</a> <a id="9814" class="Keyword">import</a> <a id="9821" href="foundation.functoriality-dependent-function-types.html" class="Module">foundation.functoriality-dependent-function-types</a>
<a id="9871" class="Keyword">open</a> <a id="9876" class="Keyword">import</a> <a id="9883" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="9929" class="Keyword">open</a> <a id="9934" class="Keyword">import</a> <a id="9941" href="foundation.functoriality-function-types.html" class="Module">foundation.functoriality-function-types</a>
<a id="9981" class="Keyword">open</a> <a id="9986" class="Keyword">import</a> <a id="9993" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="10043" class="Keyword">open</a> <a id="10048" class="Keyword">import</a> <a id="10055" href="foundation.functoriality-set-quotients.html" class="Module">foundation.functoriality-set-quotients</a>
<a id="10094" class="Keyword">open</a> <a id="10099" class="Keyword">import</a> <a id="10106" href="foundation.functoriality-set-truncation.html" class="Module">foundation.functoriality-set-truncation</a>
<a id="10146" class="Keyword">open</a> <a id="10151" class="Keyword">import</a> <a id="10158" href="foundation.functoriality-w-types.html" class="Module">foundation.functoriality-w-types</a>
<a id="10191" class="Keyword">open</a> <a id="10196" class="Keyword">import</a> <a id="10203" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="10252" class="Keyword">open</a> <a id="10257" class="Keyword">import</a> <a id="10264" href="foundation.global-choice.html" class="Module">foundation.global-choice</a>
<a id="10289" class="Keyword">open</a> <a id="10294" class="Keyword">import</a> <a id="10301" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="10323" class="Keyword">open</a> <a id="10328" class="Keyword">import</a> <a id="10335" href="foundation.identity-systems.html" class="Module">foundation.identity-systems</a>
<a id="10363" class="Keyword">open</a> <a id="10368" class="Keyword">import</a> <a id="10375" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="10401" class="Keyword">open</a> <a id="10406" class="Keyword">import</a> <a id="10413" href="foundation.images.html" class="Module">foundation.images</a>
<a id="10431" class="Keyword">open</a> <a id="10436" class="Keyword">import</a> <a id="10443" href="foundation.impredicative-encodings.html" class="Module">foundation.impredicative-encodings</a>
<a id="10478" class="Keyword">open</a> <a id="10483" class="Keyword">import</a> <a id="10490" href="foundation.indexed-w-types.html" class="Module">foundation.indexed-w-types</a>
<a id="10517" class="Keyword">open</a> <a id="10522" class="Keyword">import</a> <a id="10529" href="foundation.induction-principle-propositional-truncation.html" class="Module">foundation.induction-principle-propositional-truncation</a>
<a id="10585" class="Keyword">open</a> <a id="10590" class="Keyword">import</a> <a id="10597" href="foundation.induction-w-types.html" class="Module">foundation.induction-w-types</a>
<a id="10626" class="Keyword">open</a> <a id="10631" class="Keyword">import</a> <a id="10638" href="foundation.inequality-w-types.html" class="Module">foundation.inequality-w-types</a>
<a id="10668" class="Keyword">open</a> <a id="10673" class="Keyword">import</a> <a id="10680" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="10706" class="Keyword">open</a> <a id="10711" class="Keyword">import</a> <a id="10718" href="foundation.interchange-law.html" class="Module">foundation.interchange-law</a>
<a id="10745" class="Keyword">open</a> <a id="10750" class="Keyword">import</a> <a id="10757" href="foundation.involutions.html" class="Module">foundation.involutions</a>
<a id="10780" class="Keyword">open</a> <a id="10785" class="Keyword">import</a> <a id="10792" href="foundation.isolated-points.html" class="Module">foundation.isolated-points</a>
<a id="10819" class="Keyword">open</a> <a id="10824" class="Keyword">import</a> <a id="10831" href="foundation.isomorphisms-of-sets.html" class="Module">foundation.isomorphisms-of-sets</a>
<a id="10863" class="Keyword">open</a> <a id="10868" class="Keyword">import</a> <a id="10875" href="foundation.law-of-excluded-middle.html" class="Module">foundation.law-of-excluded-middle</a>
<a id="10909" class="Keyword">open</a> <a id="10914" class="Keyword">import</a> <a id="10921" href="foundation.lawveres-fixed-point-theorem.html" class="Module">foundation.lawveres-fixed-point-theorem</a>
<a id="10961" class="Keyword">open</a> <a id="10966" class="Keyword">import</a> <a id="10973" href="foundation.locally-small-types.html" class="Module">foundation.locally-small-types</a>
<a id="11004" class="Keyword">open</a> <a id="11009" class="Keyword">import</a> <a id="11016" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="11048" class="Keyword">open</a> <a id="11053" class="Keyword">import</a> <a id="11060" href="foundation.lower-types-w-types.html" class="Module">foundation.lower-types-w-types</a>
<a id="11091" class="Keyword">open</a> <a id="11096" class="Keyword">import</a> <a id="11103" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="11120" class="Keyword">open</a> <a id="11125" class="Keyword">import</a> <a id="11132" href="foundation.mere-equality.html" class="Module">foundation.mere-equality</a>
<a id="11157" class="Keyword">open</a> <a id="11162" class="Keyword">import</a> <a id="11169" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="11198" class="Keyword">open</a> <a id="11203" class="Keyword">import</a> <a id="11210" href="foundation.monomorphisms.html" class="Module">foundation.monomorphisms</a>
<a id="11235" class="Keyword">open</a> <a id="11240" class="Keyword">import</a> <a id="11247" href="foundation.multisets.html" class="Module">foundation.multisets</a>
<a id="11268" class="Keyword">open</a> <a id="11273" class="Keyword">import</a> <a id="11280" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="11300" class="Keyword">open</a> <a id="11305" class="Keyword">import</a> <a id="11312" href="foundation.non-contractible-types.html" class="Module">foundation.non-contractible-types</a>
<a id="11346" class="Keyword">open</a> <a id="11351" class="Keyword">import</a> <a id="11358" href="foundation.path-algebra.html" class="Module">foundation.path-algebra</a>
<a id="11382" class="Keyword">open</a> <a id="11387" class="Keyword">import</a> <a id="11394" href="foundation.path-split-maps.html" class="Module">foundation.path-split-maps</a>
<a id="11421" class="Keyword">open</a> <a id="11426" class="Keyword">import</a> <a id="11433" href="foundation.polynomial-endofunctors.html" class="Module">foundation.polynomial-endofunctors</a>
<a id="11468" class="Keyword">open</a> <a id="11473" class="Keyword">import</a> <a id="11480" href="foundation.propositional-extensionality.html" class="Module">foundation.propositional-extensionality</a>
<a id="11520" class="Keyword">open</a> <a id="11525" class="Keyword">import</a> <a id="11532" href="foundation.propositional-maps.html" class="Module">foundation.propositional-maps</a>
<a id="11562" class="Keyword">open</a> <a id="11567" class="Keyword">import</a> <a id="11574" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="11611" class="Keyword">open</a> <a id="11616" class="Keyword">import</a> <a id="11623" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="11647" class="Keyword">open</a> <a id="11652" class="Keyword">import</a> <a id="11659" href="foundation.pullbacks.html" class="Module">foundation.pullbacks</a>
<a id="11680" class="Keyword">open</a> <a id="11685" class="Keyword">import</a> <a id="11692" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="11727" class="Keyword">open</a> <a id="11732" class="Keyword">import</a> <a id="11739" href="foundation.ranks-of-elements-w-types.html" class="Module">foundation.ranks-of-elements-w-types</a>
<a id="11776" class="Keyword">open</a> <a id="11781" class="Keyword">import</a> <a id="11788" href="foundation.reflecting-maps-equivalence-relations.html" class="Module">foundation.reflecting-maps-equivalence-relations</a>
<a id="11837" class="Keyword">open</a> <a id="11842" class="Keyword">import</a> <a id="11849" href="foundation.replacement.html" class="Module">foundation.replacement</a>
<a id="11872" class="Keyword">open</a> <a id="11877" class="Keyword">import</a> <a id="11884" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="11907" class="Keyword">open</a> <a id="11912" class="Keyword">import</a> <a id="11919" href="foundation.russells-paradox.html" class="Module">foundation.russells-paradox</a>
<a id="11947" class="Keyword">open</a> <a id="11952" class="Keyword">import</a> <a id="11959" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="11979" class="Keyword">open</a> <a id="11984" class="Keyword">import</a> <a id="11991" href="foundation.set-presented-types.html" class="Module">foundation.set-presented-types</a>
<a id="12022" class="Keyword">open</a> <a id="12027" class="Keyword">import</a> <a id="12034" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="12061" class="Keyword">open</a> <a id="12066" class="Keyword">import</a> <a id="12073" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="12089" class="Keyword">open</a> <a id="12094" class="Keyword">import</a> <a id="12101" href="foundation.singleton-induction.html" class="Module">foundation.singleton-induction</a>
<a id="12132" class="Keyword">open</a> <a id="12137" class="Keyword">import</a> <a id="12144" href="foundation.slice.html" class="Module">foundation.slice</a>
<a id="12161" class="Keyword">open</a> <a id="12166" class="Keyword">import</a> <a id="12173" href="foundation.small-maps.html" class="Module">foundation.small-maps</a>
<a id="12195" class="Keyword">open</a> <a id="12200" class="Keyword">import</a> <a id="12207" href="foundation.small-multisets.html" class="Module">foundation.small-multisets</a>
<a id="12234" class="Keyword">open</a> <a id="12239" class="Keyword">import</a> <a id="12246" href="foundation.small-types.html" class="Module">foundation.small-types</a>
<a id="12269" class="Keyword">open</a> <a id="12274" class="Keyword">import</a> <a id="12281" href="foundation.small-universes.html" class="Module">foundation.small-universes</a>
<a id="12308" class="Keyword">open</a> <a id="12313" class="Keyword">import</a> <a id="12320" href="foundation.split-surjective-maps.html" class="Module">foundation.split-surjective-maps</a>
<a id="12353" class="Keyword">open</a> <a id="12358" class="Keyword">import</a> <a id="12365" href="foundation.structure-identity-principle.html" class="Module">foundation.structure-identity-principle</a>
<a id="12405" class="Keyword">open</a> <a id="12410" class="Keyword">import</a> <a id="12417" href="foundation.structure.html" class="Module">foundation.structure</a>
<a id="12438" class="Keyword">open</a> <a id="12443" class="Keyword">import</a> <a id="12450" href="foundation.subterminal-types.html" class="Module">foundation.subterminal-types</a>
<a id="12479" class="Keyword">open</a> <a id="12484" class="Keyword">import</a> <a id="12491" href="foundation.subtype-identity-principle.html" class="Module">foundation.subtype-identity-principle</a>
<a id="12529" class="Keyword">open</a> <a id="12534" class="Keyword">import</a> <a id="12541" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="12561" class="Keyword">open</a> <a id="12566" class="Keyword">import</a> <a id="12573" href="foundation.subuniverses.html" class="Module">foundation.subuniverses</a>
<a id="12597" class="Keyword">open</a> <a id="12602" class="Keyword">import</a> <a id="12609" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="12636" class="Keyword">open</a> <a id="12641" class="Keyword">import</a> <a id="12648" href="foundation.truncated-equality.html" class="Module">foundation.truncated-equality</a>
<a id="12678" class="Keyword">open</a> <a id="12683" class="Keyword">import</a> <a id="12690" href="foundation.truncated-maps.html" class="Module">foundation.truncated-maps</a>
<a id="12716" class="Keyword">open</a> <a id="12721" class="Keyword">import</a> <a id="12728" href="foundation.truncated-types.html" class="Module">foundation.truncated-types</a>
<a id="12755" class="Keyword">open</a> <a id="12760" class="Keyword">import</a> <a id="12767" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="12796" class="Keyword">open</a> <a id="12801" class="Keyword">import</a> <a id="12808" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="12831" class="Keyword">open</a> <a id="12836" class="Keyword">import</a> <a id="12843" href="foundation.type-arithmetic-cartesian-product-types.html" class="Module">foundation.type-arithmetic-cartesian-product-types</a>
<a id="12894" class="Keyword">open</a> <a id="12899" class="Keyword">import</a> <a id="12906" href="foundation.type-arithmetic-coproduct-types.html" class="Module">foundation.type-arithmetic-coproduct-types</a>
<a id="12949" class="Keyword">open</a> <a id="12954" class="Keyword">import</a> <a id="12961" href="foundation.type-arithmetic-dependent-pair-types.html" class="Module">foundation.type-arithmetic-dependent-pair-types</a>
<a id="13009" class="Keyword">open</a> <a id="13014" class="Keyword">import</a> <a id="13021" href="foundation.type-arithmetic-empty-type.html" class="Module">foundation.type-arithmetic-empty-type</a>
<a id="13059" class="Keyword">open</a> <a id="13064" class="Keyword">import</a> <a id="13071" href="foundation.type-arithmetic-unit-type.html" class="Module">foundation.type-arithmetic-unit-type</a>
<a id="13108" class="Keyword">open</a> <a id="13113" class="Keyword">import</a> <a id="13120" href="foundation.uniqueness-image.html" class="Module">foundation.uniqueness-image</a>
<a id="13148" class="Keyword">open</a> <a id="13153" class="Keyword">import</a> <a id="13160" href="foundation.uniqueness-set-quotients.html" class="Module">foundation.uniqueness-set-quotients</a>
<a id="13196" class="Keyword">open</a> <a id="13201" class="Keyword">import</a> <a id="13208" href="foundation.uniqueness-set-truncations.html" class="Module">foundation.uniqueness-set-truncations</a>
<a id="13246" class="Keyword">open</a> <a id="13251" class="Keyword">import</a> <a id="13258" href="foundation.uniqueness-truncation.html" class="Module">foundation.uniqueness-truncation</a>
<a id="13291" class="Keyword">open</a> <a id="13296" class="Keyword">import</a> <a id="13303" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="13324" class="Keyword">open</a> <a id="13329" class="Keyword">import</a> <a id="13336" href="foundation.univalence-implies-function-extensionality.html" class="Module">foundation.univalence-implies-function-extensionality</a>
<a id="13390" class="Keyword">open</a> <a id="13395" class="Keyword">import</a> <a id="13402" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="13424" class="Keyword">open</a> <a id="13429" class="Keyword">import</a> <a id="13436" href="foundation.univalent-type-families.html" class="Module">foundation.univalent-type-families</a>
<a id="13471" class="Keyword">open</a> <a id="13476" class="Keyword">import</a> <a id="13483" href="foundation.universal-multiset.html" class="Module">foundation.universal-multiset</a>
<a id="13513" class="Keyword">open</a> <a id="13518" class="Keyword">import</a> <a id="13525" href="foundation.universal-property-booleans.html" class="Module">foundation.universal-property-booleans</a>
<a id="13564" class="Keyword">open</a> <a id="13569" class="Keyword">import</a> <a id="13576" href="foundation.universal-property-cartesian-product-types.html" class="Module">foundation.universal-property-cartesian-product-types</a>
<a id="13630" class="Keyword">open</a> <a id="13635" class="Keyword">import</a> <a id="13642" href="foundation.universal-property-coproduct-types.html" class="Module">foundation.universal-property-coproduct-types</a>
<a id="13688" class="Keyword">open</a> <a id="13693" class="Keyword">import</a> <a id="13700" href="foundation.universal-property-dependent-pair-types.html" class="Module">foundation.universal-property-dependent-pair-types</a>
<a id="13751" class="Keyword">open</a> <a id="13756" class="Keyword">import</a> <a id="13763" href="foundation.universal-property-empty-type.html" class="Module">foundation.universal-property-empty-type</a>
<a id="13804" class="Keyword">open</a> <a id="13809" class="Keyword">import</a> <a id="13816" href="foundation.universal-property-fiber-products.html" class="Module">foundation.universal-property-fiber-products</a>
<a id="13861" class="Keyword">open</a> <a id="13866" class="Keyword">import</a> <a id="13873" href="foundation.universal-property-identity-types.html" class="Module">foundation.universal-property-identity-types</a>
<a id="13918" class="Keyword">open</a> <a id="13923" class="Keyword">import</a> <a id="13930" href="foundation.universal-property-image.html" class="Module">foundation.universal-property-image</a>
<a id="13966" class="Keyword">open</a> <a id="13971" class="Keyword">import</a> <a id="13978" href="foundation.universal-property-maybe.html" class="Module">foundation.universal-property-maybe</a>
<a id="14014" class="Keyword">open</a> <a id="14019" class="Keyword">import</a> <a id="14026" href="foundation.universal-property-propositional-truncation-into-sets.html" class="Module">foundation.universal-property-propositional-truncation-into-sets</a>
<a id="14091" class="Keyword">open</a> <a id="14096" class="Keyword">import</a> <a id="14103" href="foundation.universal-property-propositional-truncation.html" class="Module">foundation.universal-property-propositional-truncation</a>
<a id="14158" class="Keyword">open</a> <a id="14163" class="Keyword">import</a> <a id="14170" href="foundation.universal-property-pullbacks.html" class="Module">foundation.universal-property-pullbacks</a>
<a id="14210" class="Keyword">open</a> <a id="14215" class="Keyword">import</a> <a id="14222" href="foundation.universal-property-set-quotients.html" class="Module">foundation.universal-property-set-quotients</a>
<a id="14266" class="Keyword">open</a> <a id="14271" class="Keyword">import</a> <a id="14278" href="foundation.universal-property-set-truncation.html" class="Module">foundation.universal-property-set-truncation</a>
<a id="14323" class="Keyword">open</a> <a id="14328" class="Keyword">import</a> <a id="14335" href="foundation.universal-property-truncation.html" class="Module">foundation.universal-property-truncation</a>
<a id="14376" class="Keyword">open</a> <a id="14381" class="Keyword">import</a> <a id="14388" href="foundation.universal-property-unit-type.html" class="Module">foundation.universal-property-unit-type</a>
<a id="14428" class="Keyword">open</a> <a id="14433" class="Keyword">import</a> <a id="14440" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="14467" class="Keyword">open</a> <a id="14472" class="Keyword">import</a> <a id="14479" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>
<a id="14506" class="Keyword">open</a> <a id="14511" class="Keyword">import</a> <a id="14518" href="foundation.w-types.html" class="Module">foundation.w-types</a>
<a id="14537" class="Keyword">open</a> <a id="14542" class="Keyword">import</a> <a id="14549" href="foundation.weak-function-extensionality.html" class="Module">foundation.weak-function-extensionality</a>
<a id="14589" class="Keyword">open</a> <a id="14594" class="Keyword">import</a> <a id="14601" href="foundation.weakly-constant-maps.html" class="Module">foundation.weakly-constant-maps</a>
</pre>
## Foundation Core

<pre class="Agda"><a id="14666" class="Keyword">open</a> <a id="14671" class="Keyword">import</a> <a id="14678" href="foundation-core.0-maps.html" class="Module">foundation-core.0-maps</a>
<a id="14701" class="Keyword">open</a> <a id="14706" class="Keyword">import</a> <a id="14713" href="foundation-core.1-types.html" class="Module">foundation-core.1-types</a>
<a id="14737" class="Keyword">open</a> <a id="14742" class="Keyword">import</a> <a id="14749" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="14789" class="Keyword">open</a> <a id="14794" class="Keyword">import</a> <a id="14801" href="foundation-core.coherently-invertible-maps.html" class="Module">foundation-core.coherently-invertible-maps</a>
<a id="14844" class="Keyword">open</a> <a id="14849" class="Keyword">import</a> <a id="14856" href="foundation-core.commuting-squares.html" class="Module">foundation-core.commuting-squares</a>
<a id="14890" class="Keyword">open</a> <a id="14895" class="Keyword">import</a> <a id="14902" href="foundation-core.constant-maps.html" class="Module">foundation-core.constant-maps</a>
<a id="14932" class="Keyword">open</a> <a id="14937" class="Keyword">import</a> <a id="14944" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="14978" class="Keyword">open</a> <a id="14983" class="Keyword">import</a> <a id="14990" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="15025" class="Keyword">open</a> <a id="15030" class="Keyword">import</a> <a id="15037" href="foundation-core.dependent-pair-types.html" class="Module">foundation-core.dependent-pair-types</a>
<a id="15074" class="Keyword">open</a> <a id="15079" class="Keyword">import</a> <a id="15086" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="15113" class="Keyword">open</a> <a id="15118" class="Keyword">import</a> <a id="15125" href="foundation-core.empty-types.html" class="Module">foundation-core.empty-types</a>
<a id="15153" class="Keyword">open</a> <a id="15158" class="Keyword">import</a> <a id="15165" href="foundation-core.equality-cartesian-product-types.html" class="Module">foundation-core.equality-cartesian-product-types</a>
<a id="15214" class="Keyword">open</a> <a id="15219" class="Keyword">import</a> <a id="15226" href="foundation-core.equality-dependent-pair-types.html" class="Module">foundation-core.equality-dependent-pair-types</a>
<a id="15272" class="Keyword">open</a> <a id="15277" class="Keyword">import</a> <a id="15284" href="foundation-core.equality-fibers-of-maps.html" class="Module">foundation-core.equality-fibers-of-maps</a>
<a id="15324" class="Keyword">open</a> <a id="15329" class="Keyword">import</a> <a id="15336" href="foundation-core.equivalence-induction.html" class="Module">foundation-core.equivalence-induction</a>
<a id="15374" class="Keyword">open</a> <a id="15379" class="Keyword">import</a> <a id="15386" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="15415" class="Keyword">open</a> <a id="15420" class="Keyword">import</a> <a id="15427" href="foundation-core.faithful-maps.html" class="Module">foundation-core.faithful-maps</a>
<a id="15457" class="Keyword">open</a> <a id="15462" class="Keyword">import</a> <a id="15469" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
<a id="15500" class="Keyword">open</a> <a id="15505" class="Keyword">import</a> <a id="15512" href="foundation-core.functions.html" class="Module">foundation-core.functions</a>
<a id="15538" class="Keyword">open</a> <a id="15543" class="Keyword">import</a> <a id="15550" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
<a id="15601" class="Keyword">open</a> <a id="15606" class="Keyword">import</a> <a id="15613" href="foundation-core.fundamental-theorem-of-identity-types.html" class="Module">foundation-core.fundamental-theorem-of-identity-types</a>
<a id="15667" class="Keyword">open</a> <a id="15672" class="Keyword">import</a> <a id="15679" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="15706" class="Keyword">open</a> <a id="15711" class="Keyword">import</a> <a id="15718" href="foundation-core.identity-systems.html" class="Module">foundation-core.identity-systems</a>
<a id="15751" class="Keyword">open</a> <a id="15756" class="Keyword">import</a> <a id="15763" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="15794" class="Keyword">open</a> <a id="15799" class="Keyword">import</a> <a id="15806" href="foundation-core.logical-equivalences.html" class="Module">foundation-core.logical-equivalences</a>
<a id="15843" class="Keyword">open</a> <a id="15848" class="Keyword">import</a> <a id="15855" href="foundation-core.negation.html" class="Module">foundation-core.negation</a>
<a id="15880" class="Keyword">open</a> <a id="15885" class="Keyword">import</a> <a id="15892" href="foundation-core.path-split-maps.html" class="Module">foundation-core.path-split-maps</a>
<a id="15924" class="Keyword">open</a> <a id="15929" class="Keyword">import</a> <a id="15936" href="foundation-core.propositional-maps.html" class="Module">foundation-core.propositional-maps</a>
<a id="15971" class="Keyword">open</a> <a id="15976" class="Keyword">import</a> <a id="15983" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="16012" class="Keyword">open</a> <a id="16017" class="Keyword">import</a> <a id="16024" href="foundation-core.retractions.html" class="Module">foundation-core.retractions</a>
<a id="16052" class="Keyword">open</a> <a id="16057" class="Keyword">import</a> <a id="16064" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
<a id="16089" class="Keyword">open</a> <a id="16094" class="Keyword">import</a> <a id="16101" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>
<a id="16122" class="Keyword">open</a> <a id="16127" class="Keyword">import</a> <a id="16134" href="foundation-core.singleton-induction.html" class="Module">foundation-core.singleton-induction</a>
<a id="16170" class="Keyword">open</a> <a id="16175" class="Keyword">import</a> <a id="16182" href="foundation-core.subtype-identity-principle.html" class="Module">foundation-core.subtype-identity-principle</a>
<a id="16225" class="Keyword">open</a> <a id="16230" class="Keyword">import</a> <a id="16237" href="foundation-core.subtypes.html" class="Module">foundation-core.subtypes</a>
<a id="16262" class="Keyword">open</a> <a id="16267" class="Keyword">import</a> <a id="16274" href="foundation-core.truncated-maps.html" class="Module">foundation-core.truncated-maps</a>
<a id="16305" class="Keyword">open</a> <a id="16310" class="Keyword">import</a> <a id="16317" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="16349" class="Keyword">open</a> <a id="16354" class="Keyword">import</a> <a id="16361" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
<a id="16395" class="Keyword">open</a> <a id="16400" class="Keyword">import</a> <a id="16407" href="foundation-core.type-arithmetic-cartesian-product-types.html" class="Module">foundation-core.type-arithmetic-cartesian-product-types</a>
<a id="16463" class="Keyword">open</a> <a id="16468" class="Keyword">import</a> <a id="16475" href="foundation-core.type-arithmetic-dependent-pair-types.html" class="Module">foundation-core.type-arithmetic-dependent-pair-types</a>
<a id="16528" class="Keyword">open</a> <a id="16533" class="Keyword">import</a> <a id="16540" href="foundation-core.univalence.html" class="Module">foundation-core.univalence</a>
<a id="16567" class="Keyword">open</a> <a id="16572" class="Keyword">import</a> <a id="16579" href="foundation-core.universe-levels.html" class="Module">foundation-core.universe-levels</a>
</pre>
## Graph theory

<pre class="Agda"><a id="16641" class="Keyword">open</a> <a id="16646" class="Keyword">import</a> <a id="16653" href="graph-theory.html" class="Module">graph-theory</a>
<a id="16666" class="Keyword">open</a> <a id="16671" class="Keyword">import</a> <a id="16678" href="graph-theory.connected-undirected-graphs.html" class="Module">graph-theory.connected-undirected-graphs</a>
<a id="16719" class="Keyword">open</a> <a id="16724" class="Keyword">import</a> <a id="16731" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="16760" class="Keyword">open</a> <a id="16765" class="Keyword">import</a> <a id="16772" href="graph-theory.edge-coloured-undirected-graphs.html" class="Module">graph-theory.edge-coloured-undirected-graphs</a>
<a id="16817" class="Keyword">open</a> <a id="16822" class="Keyword">import</a> <a id="16829" href="graph-theory.equivalences-undirected-graphs.html" class="Module">graph-theory.equivalences-undirected-graphs</a>
<a id="16873" class="Keyword">open</a> <a id="16878" class="Keyword">import</a> <a id="16885" href="graph-theory.finite-graphs.html" class="Module">graph-theory.finite-graphs</a>
<a id="16912" class="Keyword">open</a> <a id="16917" class="Keyword">import</a> <a id="16924" href="graph-theory.incidence-undirected-graphs.html" class="Module">graph-theory.incidence-undirected-graphs</a>
<a id="16965" class="Keyword">open</a> <a id="16970" class="Keyword">import</a> <a id="16977" href="graph-theory.mere-equivalences-undirected-graphs.html" class="Module">graph-theory.mere-equivalences-undirected-graphs</a>
<a id="17026" class="Keyword">open</a> <a id="17031" class="Keyword">import</a> <a id="17038" href="graph-theory.morphisms-undirected-graphs.html" class="Module">graph-theory.morphisms-undirected-graphs</a>
<a id="17079" class="Keyword">open</a> <a id="17084" class="Keyword">import</a> <a id="17091" href="graph-theory.orientations-undirected-graphs.html" class="Module">graph-theory.orientations-undirected-graphs</a>
<a id="17135" class="Keyword">open</a> <a id="17140" class="Keyword">import</a> <a id="17147" href="graph-theory.paths-undirected-graphs.html" class="Module">graph-theory.paths-undirected-graphs</a>
<a id="17184" class="Keyword">open</a> <a id="17189" class="Keyword">import</a> <a id="17196" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>
<a id="17218" class="Keyword">open</a> <a id="17223" class="Keyword">import</a> <a id="17230" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
<a id="17260" class="Keyword">open</a> <a id="17265" class="Keyword">import</a> <a id="17272" href="graph-theory.simple-undirected-graphs.html" class="Module">graph-theory.simple-undirected-graphs</a>
<a id="17310" class="Keyword">open</a> <a id="17315" class="Keyword">import</a> <a id="17322" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
## Group theory

<pre class="Agda"><a id="17383" class="Keyword">open</a> <a id="17388" class="Keyword">import</a> <a id="17395" href="group-theory.html" class="Module">group-theory</a>
<a id="17408" class="Keyword">open</a> <a id="17413" class="Keyword">import</a> <a id="17420" href="group-theory.abelian-groups.html" class="Module">group-theory.abelian-groups</a>
<a id="17448" class="Keyword">open</a> <a id="17453" class="Keyword">import</a> <a id="17460" href="group-theory.abelian-subgroups.html" class="Module">group-theory.abelian-subgroups</a>
<a id="17491" class="Keyword">open</a> <a id="17496" class="Keyword">import</a> <a id="17503" href="group-theory.abstract-group-torsors.html" class="Module">group-theory.abstract-group-torsors</a>
<a id="17539" class="Keyword">open</a> <a id="17544" class="Keyword">import</a> <a id="17551" href="group-theory.category-of-groups.html" class="Module">group-theory.category-of-groups</a>
<a id="17583" class="Keyword">open</a> <a id="17588" class="Keyword">import</a> <a id="17595" href="group-theory.category-of-semigroups.html" class="Module">group-theory.category-of-semigroups</a>
<a id="17631" class="Keyword">open</a> <a id="17636" class="Keyword">import</a> <a id="17643" href="group-theory.cayleys-theorem.html" class="Module">group-theory.cayleys-theorem</a>
<a id="17672" class="Keyword">open</a> <a id="17677" class="Keyword">import</a> <a id="17684" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="17720" class="Keyword">open</a> <a id="17725" class="Keyword">import</a> <a id="17732" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="17761" class="Keyword">open</a> <a id="17766" class="Keyword">import</a> <a id="17773" href="group-theory.concrete-subgroups.html" class="Module">group-theory.concrete-subgroups</a>
<a id="17805" class="Keyword">open</a> <a id="17810" class="Keyword">import</a> <a id="17817" href="group-theory.conjugation.html" class="Module">group-theory.conjugation</a>
<a id="17842" class="Keyword">open</a> <a id="17847" class="Keyword">import</a> <a id="17854" href="group-theory.embeddings-groups.html" class="Module">group-theory.embeddings-groups</a>
<a id="17885" class="Keyword">open</a> <a id="17890" class="Keyword">import</a> <a id="17897" href="group-theory.equivalences-group-actions.html" class="Module">group-theory.equivalences-group-actions</a>
<a id="17937" class="Keyword">open</a> <a id="17942" class="Keyword">import</a> <a id="17949" href="group-theory.equivalences-semigroups.html" class="Module">group-theory.equivalences-semigroups</a>
<a id="17986" class="Keyword">open</a> <a id="17991" class="Keyword">import</a> <a id="17998" href="group-theory.examples-higher-groups.html" class="Module">group-theory.examples-higher-groups</a>
<a id="18034" class="Keyword">open</a> <a id="18039" class="Keyword">import</a> <a id="18046" href="group-theory.furstenberg-groups.html" class="Module">group-theory.furstenberg-groups</a>
<a id="18078" class="Keyword">open</a> <a id="18083" class="Keyword">import</a> <a id="18090" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="18117" class="Keyword">open</a> <a id="18122" class="Keyword">import</a> <a id="18129" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="18149" class="Keyword">open</a> <a id="18154" class="Keyword">import</a> <a id="18161" href="group-theory.higher-groups.html" class="Module">group-theory.higher-groups</a>
<a id="18188" class="Keyword">open</a> <a id="18193" class="Keyword">import</a> <a id="18200" href="group-theory.homomorphisms-abelian-groups.html" class="Module">group-theory.homomorphisms-abelian-groups</a>
<a id="18242" class="Keyword">open</a> <a id="18247" class="Keyword">import</a> <a id="18254" href="group-theory.homomorphisms-group-actions.html" class="Module">group-theory.homomorphisms-group-actions</a>
<a id="18295" class="Keyword">open</a> <a id="18300" class="Keyword">import</a> <a id="18307" href="group-theory.homomorphisms-groups.html" class="Module">group-theory.homomorphisms-groups</a>
<a id="18341" class="Keyword">open</a> <a id="18346" class="Keyword">import</a> <a id="18353" href="group-theory.homomorphisms-monoids.html" class="Module">group-theory.homomorphisms-monoids</a>
<a id="18388" class="Keyword">open</a> <a id="18393" class="Keyword">import</a> <a id="18400" href="group-theory.homomorphisms-semigroups.html" class="Module">group-theory.homomorphisms-semigroups</a>
<a id="18438" class="Keyword">open</a> <a id="18443" class="Keyword">import</a> <a id="18450" href="group-theory.invertible-elements-monoids.html" class="Module">group-theory.invertible-elements-monoids</a>
<a id="18491" class="Keyword">open</a> <a id="18496" class="Keyword">import</a> <a id="18503" href="group-theory.isomorphisms-abelian-groups.html" class="Module">group-theory.isomorphisms-abelian-groups</a>
<a id="18544" class="Keyword">open</a> <a id="18549" class="Keyword">import</a> <a id="18556" href="group-theory.isomorphisms-group-actions.html" class="Module">group-theory.isomorphisms-group-actions</a>
<a id="18596" class="Keyword">open</a> <a id="18601" class="Keyword">import</a> <a id="18608" href="group-theory.isomorphisms-groups.html" class="Module">group-theory.isomorphisms-groups</a>
<a id="18641" class="Keyword">open</a> <a id="18646" class="Keyword">import</a> <a id="18653" href="group-theory.isomorphisms-semigroups.html" class="Module">group-theory.isomorphisms-semigroups</a>
<a id="18690" class="Keyword">open</a> <a id="18695" class="Keyword">import</a> <a id="18702" href="group-theory.mere-equivalences-group-actions.html" class="Module">group-theory.mere-equivalences-group-actions</a>
<a id="18747" class="Keyword">open</a> <a id="18752" class="Keyword">import</a> <a id="18759" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>
<a id="18780" class="Keyword">open</a> <a id="18785" class="Keyword">import</a> <a id="18792" href="group-theory.orbits-group-actions.html" class="Module">group-theory.orbits-group-actions</a>
<a id="18826" class="Keyword">open</a> <a id="18831" class="Keyword">import</a> <a id="18838" href="group-theory.precategory-of-group-actions.html" class="Module">group-theory.precategory-of-group-actions</a>
<a id="18880" class="Keyword">open</a> <a id="18885" class="Keyword">import</a> <a id="18892" href="group-theory.precategory-of-groups.html" class="Module">group-theory.precategory-of-groups</a>
<a id="18927" class="Keyword">open</a> <a id="18932" class="Keyword">import</a> <a id="18939" href="group-theory.precategory-of-semigroups.html" class="Module">group-theory.precategory-of-semigroups</a>
<a id="18978" class="Keyword">open</a> <a id="18983" class="Keyword">import</a> <a id="18990" href="group-theory.principal-group-actions.html" class="Module">group-theory.principal-group-actions</a>
<a id="19027" class="Keyword">open</a> <a id="19032" class="Keyword">import</a> <a id="19039" href="group-theory.semigroups.html" class="Module">group-theory.semigroups</a>
<a id="19063" class="Keyword">open</a> <a id="19068" class="Keyword">import</a> <a id="19075" href="group-theory.sheargroups.html" class="Module">group-theory.sheargroups</a>
<a id="19100" class="Keyword">open</a> <a id="19105" class="Keyword">import</a> <a id="19112" href="group-theory.stabilizer-groups.html" class="Module">group-theory.stabilizer-groups</a>
<a id="19143" class="Keyword">open</a> <a id="19148" class="Keyword">import</a> <a id="19155" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
<a id="19178" class="Keyword">open</a> <a id="19183" class="Keyword">import</a> <a id="19190" href="group-theory.substitution-functor-group-actions.html" class="Module">group-theory.substitution-functor-group-actions</a>
<a id="19238" class="Keyword">open</a> <a id="19243" class="Keyword">import</a> <a id="19250" href="group-theory.symmetric-groups.html" class="Module">group-theory.symmetric-groups</a>
<a id="19280" class="Keyword">open</a> <a id="19285" class="Keyword">import</a> <a id="19292" href="group-theory.transitive-group-actions.html" class="Module">group-theory.transitive-group-actions</a>
</pre>
## Linear algebra

<pre class="Agda"><a id="19362" class="Keyword">open</a> <a id="19367" class="Keyword">import</a> <a id="19374" href="linear-algebra.html" class="Module">linear-algebra</a>
<a id="19389" class="Keyword">open</a> <a id="19394" class="Keyword">import</a> <a id="19401" href="linear-algebra.constant-matrices.html" class="Module">linear-algebra.constant-matrices</a>
<a id="19434" class="Keyword">open</a> <a id="19439" class="Keyword">import</a> <a id="19446" href="linear-algebra.constant-vectors.html" class="Module">linear-algebra.constant-vectors</a>
<a id="19478" class="Keyword">open</a> <a id="19483" class="Keyword">import</a> <a id="19490" href="linear-algebra.functoriality-matrices.html" class="Module">linear-algebra.functoriality-matrices</a>
<a id="19528" class="Keyword">open</a> <a id="19533" class="Keyword">import</a> <a id="19540" href="linear-algebra.functoriality-vectors.html" class="Module">linear-algebra.functoriality-vectors</a>
<a id="19577" class="Keyword">open</a> <a id="19582" class="Keyword">import</a> <a id="19589" href="linear-algebra.matrices-on-rings.html" class="Module">linear-algebra.matrices-on-rings</a>
<a id="19622" class="Keyword">open</a> <a id="19627" class="Keyword">import</a> <a id="19634" href="linear-algebra.matrices.html" class="Module">linear-algebra.matrices</a>
<a id="19658" class="Keyword">open</a> <a id="19663" class="Keyword">import</a> <a id="19670" href="linear-algebra.multiplication-matrices.html" class="Module">linear-algebra.multiplication-matrices</a>
<a id="19709" class="Keyword">open</a> <a id="19714" class="Keyword">import</a> <a id="19721" href="linear-algebra.scalar-multiplication-matrices.html" class="Module">linear-algebra.scalar-multiplication-matrices</a>
<a id="19767" class="Keyword">open</a> <a id="19772" class="Keyword">import</a> <a id="19779" href="linear-algebra.scalar-multiplication-vectors.html" class="Module">linear-algebra.scalar-multiplication-vectors</a>
<a id="19824" class="Keyword">open</a> <a id="19829" class="Keyword">import</a> <a id="19836" href="linear-algebra.transposition-matrices.html" class="Module">linear-algebra.transposition-matrices</a>
<a id="19874" class="Keyword">open</a> <a id="19879" class="Keyword">import</a> <a id="19886" href="linear-algebra.vectors-on-rings.html" class="Module">linear-algebra.vectors-on-rings</a>
<a id="19918" class="Keyword">open</a> <a id="19923" class="Keyword">import</a> <a id="19930" href="linear-algebra.vectors.html" class="Module">linear-algebra.vectors</a>
</pre>
## Order theory

<pre class="Agda"><a id="19983" class="Keyword">open</a> <a id="19988" class="Keyword">import</a> <a id="19995" href="order-theory.html" class="Module">order-theory</a>
<a id="20008" class="Keyword">open</a> <a id="20013" class="Keyword">import</a> <a id="20020" href="order-theory.chains-posets.html" class="Module">order-theory.chains-posets</a>
<a id="20047" class="Keyword">open</a> <a id="20052" class="Keyword">import</a> <a id="20059" href="order-theory.chains-preorders.html" class="Module">order-theory.chains-preorders</a>
<a id="20089" class="Keyword">open</a> <a id="20094" class="Keyword">import</a> <a id="20101" href="order-theory.decidable-subposets.html" class="Module">order-theory.decidable-subposets</a>
<a id="20134" class="Keyword">open</a> <a id="20139" class="Keyword">import</a> <a id="20146" href="order-theory.decidable-subpreorders.html" class="Module">order-theory.decidable-subpreorders</a>
<a id="20182" class="Keyword">open</a> <a id="20187" class="Keyword">import</a> <a id="20194" href="order-theory.finite-posets.html" class="Module">order-theory.finite-posets</a>
<a id="20221" class="Keyword">open</a> <a id="20226" class="Keyword">import</a> <a id="20233" href="order-theory.finite-preorders.html" class="Module">order-theory.finite-preorders</a>
<a id="20263" class="Keyword">open</a> <a id="20268" class="Keyword">import</a> <a id="20275" href="order-theory.finitely-graded-posets.html" class="Module">order-theory.finitely-graded-posets</a>
<a id="20311" class="Keyword">open</a> <a id="20316" class="Keyword">import</a> <a id="20323" href="order-theory.interval-subposets.html" class="Module">order-theory.interval-subposets</a>
<a id="20355" class="Keyword">open</a> <a id="20360" class="Keyword">import</a> <a id="20367" href="order-theory.largest-elements-posets.html" class="Module">order-theory.largest-elements-posets</a>
<a id="20404" class="Keyword">open</a> <a id="20409" class="Keyword">import</a> <a id="20416" href="order-theory.largest-elements-preorders.html" class="Module">order-theory.largest-elements-preorders</a>
<a id="20456" class="Keyword">open</a> <a id="20461" class="Keyword">import</a> <a id="20468" href="order-theory.least-elements-posets.html" class="Module">order-theory.least-elements-posets</a>
<a id="20503" class="Keyword">open</a> <a id="20508" class="Keyword">import</a> <a id="20515" href="order-theory.least-elements-preorders.html" class="Module">order-theory.least-elements-preorders</a>
<a id="20553" class="Keyword">open</a> <a id="20558" class="Keyword">import</a> <a id="20565" href="order-theory.locally-finite-posets.html" class="Module">order-theory.locally-finite-posets</a>
<a id="20600" class="Keyword">open</a> <a id="20605" class="Keyword">import</a> <a id="20612" href="order-theory.maximal-chains-posets.html" class="Module">order-theory.maximal-chains-posets</a>
<a id="20647" class="Keyword">open</a> <a id="20652" class="Keyword">import</a> <a id="20659" href="order-theory.maximal-chains-preorders.html" class="Module">order-theory.maximal-chains-preorders</a>
<a id="20697" class="Keyword">open</a> <a id="20702" class="Keyword">import</a> <a id="20709" href="order-theory.planar-binary-trees.html" class="Module">order-theory.planar-binary-trees</a>
<a id="20742" class="Keyword">open</a> <a id="20747" class="Keyword">import</a> <a id="20754" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="20774" class="Keyword">open</a> <a id="20779" class="Keyword">import</a> <a id="20786" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
<a id="20809" class="Keyword">open</a> <a id="20814" class="Keyword">import</a> <a id="20821" href="order-theory.subposets.html" class="Module">order-theory.subposets</a>
<a id="20844" class="Keyword">open</a> <a id="20849" class="Keyword">import</a> <a id="20856" href="order-theory.subpreorders.html" class="Module">order-theory.subpreorders</a>
<a id="20882" class="Keyword">open</a> <a id="20887" class="Keyword">import</a> <a id="20894" href="order-theory.total-posets.html" class="Module">order-theory.total-posets</a>
<a id="20920" class="Keyword">open</a> <a id="20925" class="Keyword">import</a> <a id="20932" href="order-theory.total-preorders.html" class="Module">order-theory.total-preorders</a>
</pre>
## Polytopes

<pre class="Agda"><a id="20988" class="Keyword">open</a> <a id="20993" class="Keyword">import</a> <a id="21000" href="polytopes.html" class="Module">polytopes</a>
<a id="21010" class="Keyword">open</a> <a id="21015" class="Keyword">import</a> <a id="21022" href="polytopes.abstract-polytopes.html" class="Module">polytopes.abstract-polytopes</a>
</pre>
## Ring theory

<pre class="Agda"><a id="21080" class="Keyword">open</a> <a id="21085" class="Keyword">import</a> <a id="21092" href="ring-theory.html" class="Module">ring-theory</a>
<a id="21104" class="Keyword">open</a> <a id="21109" class="Keyword">import</a> <a id="21116" href="ring-theory.commutative-rings.html" class="Module">ring-theory.commutative-rings</a>
<a id="21146" class="Keyword">open</a> <a id="21151" class="Keyword">import</a> <a id="21158" href="ring-theory.discrete-fields.html" class="Module">ring-theory.discrete-fields</a>
<a id="21186" class="Keyword">open</a> <a id="21191" class="Keyword">import</a> <a id="21198" href="ring-theory.division-rings.html" class="Module">ring-theory.division-rings</a>
<a id="21225" class="Keyword">open</a> <a id="21230" class="Keyword">import</a> <a id="21237" href="ring-theory.eisenstein-integers.html" class="Module">ring-theory.eisenstein-integers</a>
<a id="21269" class="Keyword">open</a> <a id="21274" class="Keyword">import</a> <a id="21281" href="ring-theory.gaussian-integers.html" class="Module">ring-theory.gaussian-integers</a>
<a id="21311" class="Keyword">open</a> <a id="21316" class="Keyword">import</a> <a id="21323" href="ring-theory.homomorphisms-commutative-rings.html" class="Module">ring-theory.homomorphisms-commutative-rings</a>
<a id="21367" class="Keyword">open</a> <a id="21372" class="Keyword">import</a> <a id="21379" href="ring-theory.homomorphisms-rings.html" class="Module">ring-theory.homomorphisms-rings</a>
<a id="21411" class="Keyword">open</a> <a id="21416" class="Keyword">import</a> <a id="21423" href="ring-theory.ideals.html" class="Module">ring-theory.ideals</a>
<a id="21442" class="Keyword">open</a> <a id="21447" class="Keyword">import</a> <a id="21454" href="ring-theory.invertible-elements-rings.html" class="Module">ring-theory.invertible-elements-rings</a>
<a id="21492" class="Keyword">open</a> <a id="21497" class="Keyword">import</a> <a id="21504" href="ring-theory.isomorphisms-commutative-rings.html" class="Module">ring-theory.isomorphisms-commutative-rings</a>
<a id="21547" class="Keyword">open</a> <a id="21552" class="Keyword">import</a> <a id="21559" href="ring-theory.isomorphisms-rings.html" class="Module">ring-theory.isomorphisms-rings</a>
<a id="21590" class="Keyword">open</a> <a id="21595" class="Keyword">import</a> <a id="21602" href="ring-theory.localizations-rings.html" class="Module">ring-theory.localizations-rings</a>
<a id="21634" class="Keyword">open</a> <a id="21639" class="Keyword">import</a> <a id="21646" href="ring-theory.nontrivial-rings.html" class="Module">ring-theory.nontrivial-rings</a>
<a id="21675" class="Keyword">open</a> <a id="21680" class="Keyword">import</a> <a id="21687" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
## Synthetic homotopy theory

<pre class="Agda"><a id="21748" class="Keyword">open</a> <a id="21753" class="Keyword">import</a> <a id="21760" href="synthetic-homotopy-theory.html" class="Module">synthetic-homotopy-theory</a>
<a id="21786" class="Keyword">open</a> <a id="21791" class="Keyword">import</a> <a id="21798" href="synthetic-homotopy-theory.23-pullbacks.html" class="Module">synthetic-homotopy-theory.23-pullbacks</a>
<a id="21837" class="Keyword">open</a> <a id="21842" class="Keyword">import</a> <a id="21849" href="synthetic-homotopy-theory.24-pushouts.html" class="Module">synthetic-homotopy-theory.24-pushouts</a>
<a id="21887" class="Keyword">open</a> <a id="21892" class="Keyword">import</a> <a id="21899" href="synthetic-homotopy-theory.25-cubical-diagrams.html" class="Module">synthetic-homotopy-theory.25-cubical-diagrams</a>
<a id="21945" class="Keyword">open</a> <a id="21950" class="Keyword">import</a> <a id="21957" href="synthetic-homotopy-theory.26-descent.html" class="Module">synthetic-homotopy-theory.26-descent</a>
<a id="21994" class="Keyword">open</a> <a id="21999" class="Keyword">import</a> <a id="22006" href="synthetic-homotopy-theory.26-id-pushout.html" class="Module">synthetic-homotopy-theory.26-id-pushout</a>
<a id="22046" class="Keyword">open</a> <a id="22051" class="Keyword">import</a> <a id="22058" href="synthetic-homotopy-theory.27-sequences.html" class="Module">synthetic-homotopy-theory.27-sequences</a>
<a id="22097" class="Keyword">open</a> <a id="22102" class="Keyword">import</a> <a id="22109" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
<a id="22142" class="Keyword">open</a> <a id="22147" class="Keyword">import</a> <a id="22154" href="synthetic-homotopy-theory.cyclic-types.html" class="Module">synthetic-homotopy-theory.cyclic-types</a>
<a id="22193" class="Keyword">open</a> <a id="22198" class="Keyword">import</a> <a id="22205" href="synthetic-homotopy-theory.double-loop-spaces.html" class="Module">synthetic-homotopy-theory.double-loop-spaces</a>
<a id="22250" class="Keyword">open</a> <a id="22255" class="Keyword">import</a> <a id="22262" href="synthetic-homotopy-theory.functoriality-loop-spaces.html" class="Module">synthetic-homotopy-theory.functoriality-loop-spaces</a>
<a id="22314" class="Keyword">open</a> <a id="22319" class="Keyword">import</a> <a id="22326" href="synthetic-homotopy-theory.infinite-cyclic-types.html" class="Module">synthetic-homotopy-theory.infinite-cyclic-types</a>
<a id="22374" class="Keyword">open</a> <a id="22379" class="Keyword">import</a> <a id="22386" href="synthetic-homotopy-theory.interval-type.html" class="Module">synthetic-homotopy-theory.interval-type</a>
<a id="22426" class="Keyword">open</a> <a id="22431" class="Keyword">import</a> <a id="22438" href="synthetic-homotopy-theory.iterated-loop-spaces.html" class="Module">synthetic-homotopy-theory.iterated-loop-spaces</a>
<a id="22485" class="Keyword">open</a> <a id="22490" class="Keyword">import</a> <a id="22497" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
<a id="22535" class="Keyword">open</a> <a id="22540" class="Keyword">import</a> <a id="22547" href="synthetic-homotopy-theory.pointed-dependent-functions.html" class="Module">synthetic-homotopy-theory.pointed-dependent-functions</a>
<a id="22601" class="Keyword">open</a> <a id="22606" class="Keyword">import</a> <a id="22613" href="synthetic-homotopy-theory.pointed-equivalences.html" class="Module">synthetic-homotopy-theory.pointed-equivalences</a>
<a id="22660" class="Keyword">open</a> <a id="22665" class="Keyword">import</a> <a id="22672" href="synthetic-homotopy-theory.pointed-families-of-types.html" class="Module">synthetic-homotopy-theory.pointed-families-of-types</a>
<a id="22724" class="Keyword">open</a> <a id="22729" class="Keyword">import</a> <a id="22736" href="synthetic-homotopy-theory.pointed-homotopies.html" class="Module">synthetic-homotopy-theory.pointed-homotopies</a>
<a id="22781" class="Keyword">open</a> <a id="22786" class="Keyword">import</a> <a id="22793" href="synthetic-homotopy-theory.pointed-maps.html" class="Module">synthetic-homotopy-theory.pointed-maps</a>
<a id="22832" class="Keyword">open</a> <a id="22837" class="Keyword">import</a> <a id="22844" href="synthetic-homotopy-theory.pointed-types.html" class="Module">synthetic-homotopy-theory.pointed-types</a>
<a id="22884" class="Keyword">open</a> <a id="22889" class="Keyword">import</a> <a id="22896" href="synthetic-homotopy-theory.spaces.html" class="Module">synthetic-homotopy-theory.spaces</a>
<a id="22929" class="Keyword">open</a> <a id="22934" class="Keyword">import</a> <a id="22941" href="synthetic-homotopy-theory.triple-loop-spaces.html" class="Module">synthetic-homotopy-theory.triple-loop-spaces</a>
<a id="22986" class="Keyword">open</a> <a id="22991" class="Keyword">import</a> <a id="22998" href="synthetic-homotopy-theory.universal-cover-circle.html" class="Module">synthetic-homotopy-theory.universal-cover-circle</a>
</pre>
## Tutorials

<pre class="Agda"><a id="23074" class="Keyword">open</a> <a id="23079" class="Keyword">import</a> <a id="23086" href="tutorials.basic-agda.html" class="Module">tutorials.basic-agda</a>
</pre>
## Univalent combinatorics

<pre class="Agda"><a id="23148" class="Keyword">open</a> <a id="23153" class="Keyword">import</a> <a id="23160" href="univalent-combinatorics.html" class="Module">univalent-combinatorics</a>
<a id="23184" class="Keyword">open</a> <a id="23189" class="Keyword">import</a> <a id="23196" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="23236" class="Keyword">open</a> <a id="23241" class="Keyword">import</a> <a id="23248" href="univalent-combinatorics.binomial-types.html" class="Module">univalent-combinatorics.binomial-types</a>
<a id="23287" class="Keyword">open</a> <a id="23292" class="Keyword">import</a> <a id="23299" href="univalent-combinatorics.cartesian-product-types.html" class="Module">univalent-combinatorics.cartesian-product-types</a>
<a id="23347" class="Keyword">open</a> <a id="23352" class="Keyword">import</a> <a id="23359" href="univalent-combinatorics.classical-finite-types.html" class="Module">univalent-combinatorics.classical-finite-types</a>
<a id="23406" class="Keyword">open</a> <a id="23411" class="Keyword">import</a> <a id="23418" href="univalent-combinatorics.coproduct-types.html" class="Module">univalent-combinatorics.coproduct-types</a>
<a id="23458" class="Keyword">open</a> <a id="23463" class="Keyword">import</a> <a id="23470" href="univalent-combinatorics.counting-decidable-subtypes.html" class="Module">univalent-combinatorics.counting-decidable-subtypes</a>
<a id="23522" class="Keyword">open</a> <a id="23527" class="Keyword">import</a> <a id="23534" href="univalent-combinatorics.counting-dependent-function-types.html" class="Module">univalent-combinatorics.counting-dependent-function-types</a>
<a id="23592" class="Keyword">open</a> <a id="23597" class="Keyword">import</a> <a id="23604" href="univalent-combinatorics.counting-dependent-pair-types.html" class="Module">univalent-combinatorics.counting-dependent-pair-types</a>
<a id="23658" class="Keyword">open</a> <a id="23663" class="Keyword">import</a> <a id="23670" href="univalent-combinatorics.counting-fibers-of-maps.html" class="Module">univalent-combinatorics.counting-fibers-of-maps</a>
<a id="23718" class="Keyword">open</a> <a id="23723" class="Keyword">import</a> <a id="23730" href="univalent-combinatorics.counting-function-types.html" class="Module">univalent-combinatorics.counting-function-types</a>
<a id="23778" class="Keyword">open</a> <a id="23783" class="Keyword">import</a> <a id="23790" href="univalent-combinatorics.counting-maybe.html" class="Module">univalent-combinatorics.counting-maybe</a>
<a id="23829" class="Keyword">open</a> <a id="23834" class="Keyword">import</a> <a id="23841" href="univalent-combinatorics.counting.html" class="Module">univalent-combinatorics.counting</a>
<a id="23874" class="Keyword">open</a> <a id="23879" class="Keyword">import</a> <a id="23886" href="univalent-combinatorics.cubes.html" class="Module">univalent-combinatorics.cubes</a>
<a id="23916" class="Keyword">open</a> <a id="23921" class="Keyword">import</a> <a id="23928" href="univalent-combinatorics.decidable-dependent-function-types.html" class="Module">univalent-combinatorics.decidable-dependent-function-types</a>
<a id="23987" class="Keyword">open</a> <a id="23992" class="Keyword">import</a> <a id="23999" href="univalent-combinatorics.decidable-dependent-pair-types.html" class="Module">univalent-combinatorics.decidable-dependent-pair-types</a>
<a id="24054" class="Keyword">open</a> <a id="24059" class="Keyword">import</a> <a id="24066" href="univalent-combinatorics.decidable-subtypes.html" class="Module">univalent-combinatorics.decidable-subtypes</a>
<a id="24109" class="Keyword">open</a> <a id="24114" class="Keyword">import</a> <a id="24121" href="univalent-combinatorics.dependent-product-finite-types.html" class="Module">univalent-combinatorics.dependent-product-finite-types</a>
<a id="24176" class="Keyword">open</a> <a id="24181" class="Keyword">import</a> <a id="24188" href="univalent-combinatorics.dependent-sum-finite-types.html" class="Module">univalent-combinatorics.dependent-sum-finite-types</a>
<a id="24239" class="Keyword">open</a> <a id="24244" class="Keyword">import</a> <a id="24251" href="univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.html" class="Module">univalent-combinatorics.distributivity-of-set-truncation-over-finite-products</a>
<a id="24329" class="Keyword">open</a> <a id="24334" class="Keyword">import</a> <a id="24341" href="univalent-combinatorics.double-counting.html" class="Module">univalent-combinatorics.double-counting</a>
<a id="24381" class="Keyword">open</a> <a id="24386" class="Keyword">import</a> <a id="24393" href="univalent-combinatorics.embeddings-standard-finite-types.html" class="Module">univalent-combinatorics.embeddings-standard-finite-types</a>
<a id="24450" class="Keyword">open</a> <a id="24455" class="Keyword">import</a> <a id="24462" href="univalent-combinatorics.embeddings.html" class="Module">univalent-combinatorics.embeddings</a>
<a id="24497" class="Keyword">open</a> <a id="24502" class="Keyword">import</a> <a id="24509" href="univalent-combinatorics.equality-finite-types.html" class="Module">univalent-combinatorics.equality-finite-types</a>
<a id="24555" class="Keyword">open</a> <a id="24560" class="Keyword">import</a> <a id="24567" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a>
<a id="24622" class="Keyword">open</a> <a id="24627" class="Keyword">import</a> <a id="24634" href="univalent-combinatorics.equivalences-cubes.html" class="Module">univalent-combinatorics.equivalences-cubes</a>
<a id="24677" class="Keyword">open</a> <a id="24682" class="Keyword">import</a> <a id="24689" href="univalent-combinatorics.equivalences-standard-finite-types.html" class="Module">univalent-combinatorics.equivalences-standard-finite-types</a>
<a id="24748" class="Keyword">open</a> <a id="24753" class="Keyword">import</a> <a id="24760" href="univalent-combinatorics.equivalences.html" class="Module">univalent-combinatorics.equivalences</a>
<a id="24797" class="Keyword">open</a> <a id="24802" class="Keyword">import</a> <a id="24809" href="univalent-combinatorics.fibers-of-maps-between-finite-types.html" class="Module">univalent-combinatorics.fibers-of-maps-between-finite-types</a>
<a id="24869" class="Keyword">open</a> <a id="24874" class="Keyword">import</a> <a id="24881" href="univalent-combinatorics.finite-choice.html" class="Module">univalent-combinatorics.finite-choice</a>
<a id="24919" class="Keyword">open</a> <a id="24924" class="Keyword">import</a> <a id="24931" href="univalent-combinatorics.finite-connected-components.html" class="Module">univalent-combinatorics.finite-connected-components</a>
<a id="24983" class="Keyword">open</a> <a id="24988" class="Keyword">import</a> <a id="24995" href="univalent-combinatorics.finite-function-types.html" class="Module">univalent-combinatorics.finite-function-types</a>
<a id="25041" class="Keyword">open</a> <a id="25046" class="Keyword">import</a> <a id="25053" href="univalent-combinatorics.finite-presentations.html" class="Module">univalent-combinatorics.finite-presentations</a>
<a id="25098" class="Keyword">open</a> <a id="25103" class="Keyword">import</a> <a id="25110" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="25147" class="Keyword">open</a> <a id="25152" class="Keyword">import</a> <a id="25159" href="univalent-combinatorics.finitely-presented-types.html" class="Module">univalent-combinatorics.finitely-presented-types</a>
<a id="25208" class="Keyword">open</a> <a id="25213" class="Keyword">import</a> <a id="25220" href="univalent-combinatorics.image-of-maps.html" class="Module">univalent-combinatorics.image-of-maps</a>
<a id="25258" class="Keyword">open</a> <a id="25263" class="Keyword">import</a> <a id="25270" href="univalent-combinatorics.inequality-types-with-counting.html" class="Module">univalent-combinatorics.inequality-types-with-counting</a>
<a id="25325" class="Keyword">open</a> <a id="25330" class="Keyword">import</a> <a id="25337" href="univalent-combinatorics.injective-maps.html" class="Module">univalent-combinatorics.injective-maps</a>
<a id="25376" class="Keyword">open</a> <a id="25381" class="Keyword">import</a> <a id="25388" href="univalent-combinatorics.lists.html" class="Module">univalent-combinatorics.lists</a>
<a id="25418" class="Keyword">open</a> <a id="25423" class="Keyword">import</a> <a id="25430" href="univalent-combinatorics.maybe.html" class="Module">univalent-combinatorics.maybe</a>
<a id="25460" class="Keyword">open</a> <a id="25465" class="Keyword">import</a> <a id="25472" href="univalent-combinatorics.orientations-cubes.html" class="Module">univalent-combinatorics.orientations-cubes</a>
<a id="25515" class="Keyword">open</a> <a id="25520" class="Keyword">import</a> <a id="25527" href="univalent-combinatorics.pi-finite-types.html" class="Module">univalent-combinatorics.pi-finite-types</a>
<a id="25567" class="Keyword">open</a> <a id="25572" class="Keyword">import</a> <a id="25579" href="univalent-combinatorics.pigeonhole-principle.html" class="Module">univalent-combinatorics.pigeonhole-principle</a>
<a id="25624" class="Keyword">open</a> <a id="25629" class="Keyword">import</a> <a id="25636" href="univalent-combinatorics.presented-pi-finite-types.html" class="Module">univalent-combinatorics.presented-pi-finite-types</a>
<a id="25686" class="Keyword">open</a> <a id="25691" class="Keyword">import</a> <a id="25698" href="univalent-combinatorics.ramsey-theory.html" class="Module">univalent-combinatorics.ramsey-theory</a>
<a id="25736" class="Keyword">open</a> <a id="25741" class="Keyword">import</a> <a id="25748" href="univalent-combinatorics.retracts-of-finite-types.html" class="Module">univalent-combinatorics.retracts-of-finite-types</a>
<a id="25797" class="Keyword">open</a> <a id="25802" class="Keyword">import</a> <a id="25809" href="univalent-combinatorics.skipping-element-standard-finite-types.html" class="Module">univalent-combinatorics.skipping-element-standard-finite-types</a>
<a id="25872" class="Keyword">open</a> <a id="25877" class="Keyword">import</a> <a id="25884" href="univalent-combinatorics.standard-finite-pruned-trees.html" class="Module">univalent-combinatorics.standard-finite-pruned-trees</a>
<a id="25937" class="Keyword">open</a> <a id="25942" class="Keyword">import</a> <a id="25949" href="univalent-combinatorics.standard-finite-trees.html" class="Module">univalent-combinatorics.standard-finite-trees</a>
<a id="25995" class="Keyword">open</a> <a id="26000" class="Keyword">import</a> <a id="26007" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
<a id="26053" class="Keyword">open</a> <a id="26058" class="Keyword">import</a> <a id="26065" href="univalent-combinatorics.sums-of-natural-numbers.html" class="Module">univalent-combinatorics.sums-of-natural-numbers</a>
<a id="26113" class="Keyword">open</a> <a id="26118" class="Keyword">import</a> <a id="26125" href="univalent-combinatorics.surjective-maps.html" class="Module">univalent-combinatorics.surjective-maps</a>
</pre>
## Wild algebra

<pre class="Agda"><a id="26195" class="Keyword">open</a> <a id="26200" class="Keyword">import</a> <a id="26207" href="wild-algebra.html" class="Module">wild-algebra</a>
<a id="26220" class="Keyword">open</a> <a id="26225" class="Keyword">import</a> <a id="26232" href="wild-algebra.magmas.html" class="Module">wild-algebra.magmas</a>
<a id="26252" class="Keyword">open</a> <a id="26257" class="Keyword">import</a> <a id="26264" href="wild-algebra.universal-property-lists-wild-monoids.html" class="Module">wild-algebra.universal-property-lists-wild-monoids</a>
<a id="26315" class="Keyword">open</a> <a id="26320" class="Keyword">import</a> <a id="26327" href="wild-algebra.wild-groups.html" class="Module">wild-algebra.wild-groups</a>
<a id="26352" class="Keyword">open</a> <a id="26357" class="Keyword">import</a> <a id="26364" href="wild-algebra.wild-monoids.html" class="Module">wild-algebra.wild-monoids</a>
<a id="26390" class="Keyword">open</a> <a id="26395" class="Keyword">import</a> <a id="26402" href="wild-algebra.wild-unital-magmas.html" class="Module">wild-algebra.wild-unital-magmas</a>
</pre>
## Everything

See the list of all Agda modules [here](everything.html).

