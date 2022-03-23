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
<a id="6796" class="Keyword">open</a> <a id="6801" class="Keyword">import</a> <a id="6808" href="finite-group-theory.permutations.html" class="Module">finite-group-theory.permutations</a>
<a id="6841" class="Keyword">open</a> <a id="6846" class="Keyword">import</a> <a id="6853" href="finite-group-theory.transpositions.html" class="Module">finite-group-theory.transpositions</a>
</pre>
## Foundation

<pre class="Agda"><a id="6916" class="Keyword">open</a> <a id="6921" class="Keyword">import</a> <a id="6928" href="foundation.html" class="Module">foundation</a>
<a id="6939" class="Keyword">open</a> <a id="6944" class="Keyword">import</a> <a id="6951" href="foundation.0-maps.html" class="Module">foundation.0-maps</a>
<a id="6969" class="Keyword">open</a> <a id="6974" class="Keyword">import</a> <a id="6981" href="foundation.1-types.html" class="Module">foundation.1-types</a>
<a id="7000" class="Keyword">open</a> <a id="7005" class="Keyword">import</a> <a id="7012" href="foundation.2-types.html" class="Module">foundation.2-types</a>
<a id="7031" class="Keyword">open</a> <a id="7036" class="Keyword">import</a> <a id="7043" href="foundation.algebras-polynomial-endofunctors.html" class="Module">foundation.algebras-polynomial-endofunctors</a>
<a id="7087" class="Keyword">open</a> <a id="7092" class="Keyword">import</a> <a id="7099" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="7124" class="Keyword">open</a> <a id="7129" class="Keyword">import</a> <a id="7136" href="foundation.axiom-of-choice.html" class="Module">foundation.axiom-of-choice</a>
<a id="7163" class="Keyword">open</a> <a id="7168" class="Keyword">import</a> <a id="7175" href="foundation.binary-embeddings.html" class="Module">foundation.binary-embeddings</a>
<a id="7204" class="Keyword">open</a> <a id="7209" class="Keyword">import</a> <a id="7216" href="foundation.binary-equivalences.html" class="Module">foundation.binary-equivalences</a>
<a id="7247" class="Keyword">open</a> <a id="7252" class="Keyword">import</a> <a id="7259" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="7287" class="Keyword">open</a> <a id="7292" class="Keyword">import</a> <a id="7299" href="foundation.boolean-reflection.html" class="Module">foundation.boolean-reflection</a>
<a id="7329" class="Keyword">open</a> <a id="7334" class="Keyword">import</a> <a id="7341" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="7361" class="Keyword">open</a> <a id="7366" class="Keyword">import</a> <a id="7373" href="foundation.cantors-diagonal-argument.html" class="Module">foundation.cantors-diagonal-argument</a>
<a id="7410" class="Keyword">open</a> <a id="7415" class="Keyword">import</a> <a id="7422" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="7457" class="Keyword">open</a> <a id="7462" class="Keyword">import</a> <a id="7469" href="foundation.choice-of-representatives-equivalence-relation.html" class="Module">foundation.choice-of-representatives-equivalence-relation</a>
<a id="7527" class="Keyword">open</a> <a id="7532" class="Keyword">import</a> <a id="7539" href="foundation.coherently-invertible-maps.html" class="Module">foundation.coherently-invertible-maps</a>
<a id="7577" class="Keyword">open</a> <a id="7582" class="Keyword">import</a> <a id="7589" href="foundation.commuting-squares.html" class="Module">foundation.commuting-squares</a>
<a id="7618" class="Keyword">open</a> <a id="7623" class="Keyword">import</a> <a id="7630" href="foundation.complements.html" class="Module">foundation.complements</a>
<a id="7653" class="Keyword">open</a> <a id="7658" class="Keyword">import</a> <a id="7665" href="foundation.conjunction.html" class="Module">foundation.conjunction</a>
<a id="7688" class="Keyword">open</a> <a id="7693" class="Keyword">import</a> <a id="7700" href="foundation.connected-components-universes.html" class="Module">foundation.connected-components-universes</a>
<a id="7742" class="Keyword">open</a> <a id="7747" class="Keyword">import</a> <a id="7754" href="foundation.connected-components.html" class="Module">foundation.connected-components</a>
<a id="7786" class="Keyword">open</a> <a id="7791" class="Keyword">import</a> <a id="7798" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="7825" class="Keyword">open</a> <a id="7830" class="Keyword">import</a> <a id="7837" href="foundation.constant-maps.html" class="Module">foundation.constant-maps</a>
<a id="7862" class="Keyword">open</a> <a id="7867" class="Keyword">import</a> <a id="7874" href="foundation.contractible-maps.html" class="Module">foundation.contractible-maps</a>
<a id="7903" class="Keyword">open</a> <a id="7908" class="Keyword">import</a> <a id="7915" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="7945" class="Keyword">open</a> <a id="7950" class="Keyword">import</a> <a id="7957" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="7984" class="Keyword">open</a> <a id="7989" class="Keyword">import</a> <a id="7996" href="foundation.coslice.html" class="Module">foundation.coslice</a>
<a id="8015" class="Keyword">open</a> <a id="8020" class="Keyword">import</a> <a id="8027" href="foundation.decidable-dependent-function-types.html" class="Module">foundation.decidable-dependent-function-types</a>
<a id="8073" class="Keyword">open</a> <a id="8078" class="Keyword">import</a> <a id="8085" href="foundation.decidable-dependent-pair-types.html" class="Module">foundation.decidable-dependent-pair-types</a>
<a id="8127" class="Keyword">open</a> <a id="8132" class="Keyword">import</a> <a id="8139" href="foundation.decidable-embeddings.html" class="Module">foundation.decidable-embeddings</a>
<a id="8171" class="Keyword">open</a> <a id="8176" class="Keyword">import</a> <a id="8183" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a>
<a id="8213" class="Keyword">open</a> <a id="8218" class="Keyword">import</a> <a id="8225" href="foundation.decidable-maps.html" class="Module">foundation.decidable-maps</a>
<a id="8251" class="Keyword">open</a> <a id="8256" class="Keyword">import</a> <a id="8263" href="foundation.decidable-propositions.html" class="Module">foundation.decidable-propositions</a>
<a id="8297" class="Keyword">open</a> <a id="8302" class="Keyword">import</a> <a id="8309" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="8339" class="Keyword">open</a> <a id="8344" class="Keyword">import</a> <a id="8351" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="8378" class="Keyword">open</a> <a id="8383" class="Keyword">import</a> <a id="8390" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="8422" class="Keyword">open</a> <a id="8427" class="Keyword">import</a> <a id="8434" href="foundation.diagonal-maps-of-types.html" class="Module">foundation.diagonal-maps-of-types</a>
<a id="8468" class="Keyword">open</a> <a id="8473" class="Keyword">import</a> <a id="8480" href="foundation.disjunction.html" class="Module">foundation.disjunction</a>
<a id="8503" class="Keyword">open</a> <a id="8508" class="Keyword">import</a> <a id="8515" href="foundation.distributivity-of-dependent-functions-over-coproduct-types.html" class="Module">foundation.distributivity-of-dependent-functions-over-coproduct-types</a>
<a id="8585" class="Keyword">open</a> <a id="8590" class="Keyword">import</a> <a id="8597" href="foundation.distributivity-of-dependent-functions-over-dependent-pairs.html" class="Module">foundation.distributivity-of-dependent-functions-over-dependent-pairs</a>
<a id="8667" class="Keyword">open</a> <a id="8672" class="Keyword">import</a> <a id="8679" href="foundation.double-negation.html" class="Module">foundation.double-negation</a>
<a id="8706" class="Keyword">open</a> <a id="8711" class="Keyword">import</a> <a id="8718" href="foundation.effective-maps-equivalence-relations.html" class="Module">foundation.effective-maps-equivalence-relations</a>
<a id="8766" class="Keyword">open</a> <a id="8771" class="Keyword">import</a> <a id="8778" href="foundation.elementhood-relation-w-types.html" class="Module">foundation.elementhood-relation-w-types</a>
<a id="8818" class="Keyword">open</a> <a id="8823" class="Keyword">import</a> <a id="8830" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="8852" class="Keyword">open</a> <a id="8857" class="Keyword">import</a> <a id="8864" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="8887" class="Keyword">open</a> <a id="8892" class="Keyword">import</a> <a id="8899" href="foundation.epimorphisms-with-respect-to-sets.html" class="Module">foundation.epimorphisms-with-respect-to-sets</a>
<a id="8944" class="Keyword">open</a> <a id="8949" class="Keyword">import</a> <a id="8956" href="foundation.equality-cartesian-product-types.html" class="Module">foundation.equality-cartesian-product-types</a>
<a id="9000" class="Keyword">open</a> <a id="9005" class="Keyword">import</a> <a id="9012" href="foundation.equality-coproduct-types.html" class="Module">foundation.equality-coproduct-types</a>
<a id="9048" class="Keyword">open</a> <a id="9053" class="Keyword">import</a> <a id="9060" href="foundation.equality-dependent-function-types.html" class="Module">foundation.equality-dependent-function-types</a>
<a id="9105" class="Keyword">open</a> <a id="9110" class="Keyword">import</a> <a id="9117" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="9158" class="Keyword">open</a> <a id="9163" class="Keyword">import</a> <a id="9170" href="foundation.equality-fibers-of-maps.html" class="Module">foundation.equality-fibers-of-maps</a>
<a id="9205" class="Keyword">open</a> <a id="9210" class="Keyword">import</a> <a id="9217" href="foundation.equivalence-classes.html" class="Module">foundation.equivalence-classes</a>
<a id="9248" class="Keyword">open</a> <a id="9253" class="Keyword">import</a> <a id="9260" href="foundation.equivalence-induction.html" class="Module">foundation.equivalence-induction</a>
<a id="9293" class="Keyword">open</a> <a id="9298" class="Keyword">import</a> <a id="9305" href="foundation.equivalence-relations.html" class="Module">foundation.equivalence-relations</a>
<a id="9338" class="Keyword">open</a> <a id="9343" class="Keyword">import</a> <a id="9350" href="foundation.equivalences-maybe.html" class="Module">foundation.equivalences-maybe</a>
<a id="9380" class="Keyword">open</a> <a id="9385" class="Keyword">import</a> <a id="9392" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="9416" class="Keyword">open</a> <a id="9421" class="Keyword">import</a> <a id="9428" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="9466" class="Keyword">open</a> <a id="9471" class="Keyword">import</a> <a id="9478" href="foundation.extensional-w-types.html" class="Module">foundation.extensional-w-types</a>
<a id="9509" class="Keyword">open</a> <a id="9514" class="Keyword">import</a> <a id="9521" href="foundation.faithful-maps.html" class="Module">foundation.faithful-maps</a>
<a id="9546" class="Keyword">open</a> <a id="9551" class="Keyword">import</a> <a id="9558" href="foundation.fiber-inclusions.html" class="Module">foundation.fiber-inclusions</a>
<a id="9586" class="Keyword">open</a> <a id="9591" class="Keyword">import</a> <a id="9598" href="foundation.fibered-maps.html" class="Module">foundation.fibered-maps</a>
<a id="9622" class="Keyword">open</a> <a id="9627" class="Keyword">import</a> <a id="9634" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="9660" class="Keyword">open</a> <a id="9665" class="Keyword">import</a> <a id="9672" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="9707" class="Keyword">open</a> <a id="9712" class="Keyword">import</a> <a id="9719" href="foundation.functions.html" class="Module">foundation.functions</a>
<a id="9740" class="Keyword">open</a> <a id="9745" class="Keyword">import</a> <a id="9752" href="foundation.functoriality-cartesian-product-types.html" class="Module">foundation.functoriality-cartesian-product-types</a>
<a id="9801" class="Keyword">open</a> <a id="9806" class="Keyword">import</a> <a id="9813" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="9854" class="Keyword">open</a> <a id="9859" class="Keyword">import</a> <a id="9866" href="foundation.functoriality-dependent-function-types.html" class="Module">foundation.functoriality-dependent-function-types</a>
<a id="9916" class="Keyword">open</a> <a id="9921" class="Keyword">import</a> <a id="9928" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="9974" class="Keyword">open</a> <a id="9979" class="Keyword">import</a> <a id="9986" href="foundation.functoriality-function-types.html" class="Module">foundation.functoriality-function-types</a>
<a id="10026" class="Keyword">open</a> <a id="10031" class="Keyword">import</a> <a id="10038" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="10088" class="Keyword">open</a> <a id="10093" class="Keyword">import</a> <a id="10100" href="foundation.functoriality-set-quotients.html" class="Module">foundation.functoriality-set-quotients</a>
<a id="10139" class="Keyword">open</a> <a id="10144" class="Keyword">import</a> <a id="10151" href="foundation.functoriality-set-truncation.html" class="Module">foundation.functoriality-set-truncation</a>
<a id="10191" class="Keyword">open</a> <a id="10196" class="Keyword">import</a> <a id="10203" href="foundation.functoriality-w-types.html" class="Module">foundation.functoriality-w-types</a>
<a id="10236" class="Keyword">open</a> <a id="10241" class="Keyword">import</a> <a id="10248" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="10297" class="Keyword">open</a> <a id="10302" class="Keyword">import</a> <a id="10309" href="foundation.global-choice.html" class="Module">foundation.global-choice</a>
<a id="10334" class="Keyword">open</a> <a id="10339" class="Keyword">import</a> <a id="10346" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="10368" class="Keyword">open</a> <a id="10373" class="Keyword">import</a> <a id="10380" href="foundation.identity-systems.html" class="Module">foundation.identity-systems</a>
<a id="10408" class="Keyword">open</a> <a id="10413" class="Keyword">import</a> <a id="10420" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="10446" class="Keyword">open</a> <a id="10451" class="Keyword">import</a> <a id="10458" href="foundation.images.html" class="Module">foundation.images</a>
<a id="10476" class="Keyword">open</a> <a id="10481" class="Keyword">import</a> <a id="10488" href="foundation.impredicative-encodings.html" class="Module">foundation.impredicative-encodings</a>
<a id="10523" class="Keyword">open</a> <a id="10528" class="Keyword">import</a> <a id="10535" href="foundation.indexed-w-types.html" class="Module">foundation.indexed-w-types</a>
<a id="10562" class="Keyword">open</a> <a id="10567" class="Keyword">import</a> <a id="10574" href="foundation.induction-principle-propositional-truncation.html" class="Module">foundation.induction-principle-propositional-truncation</a>
<a id="10630" class="Keyword">open</a> <a id="10635" class="Keyword">import</a> <a id="10642" href="foundation.induction-w-types.html" class="Module">foundation.induction-w-types</a>
<a id="10671" class="Keyword">open</a> <a id="10676" class="Keyword">import</a> <a id="10683" href="foundation.inequality-w-types.html" class="Module">foundation.inequality-w-types</a>
<a id="10713" class="Keyword">open</a> <a id="10718" class="Keyword">import</a> <a id="10725" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="10751" class="Keyword">open</a> <a id="10756" class="Keyword">import</a> <a id="10763" href="foundation.interchange-law.html" class="Module">foundation.interchange-law</a>
<a id="10790" class="Keyword">open</a> <a id="10795" class="Keyword">import</a> <a id="10802" href="foundation.involutions.html" class="Module">foundation.involutions</a>
<a id="10825" class="Keyword">open</a> <a id="10830" class="Keyword">import</a> <a id="10837" href="foundation.isolated-points.html" class="Module">foundation.isolated-points</a>
<a id="10864" class="Keyword">open</a> <a id="10869" class="Keyword">import</a> <a id="10876" href="foundation.isomorphisms-of-sets.html" class="Module">foundation.isomorphisms-of-sets</a>
<a id="10908" class="Keyword">open</a> <a id="10913" class="Keyword">import</a> <a id="10920" href="foundation.law-of-excluded-middle.html" class="Module">foundation.law-of-excluded-middle</a>
<a id="10954" class="Keyword">open</a> <a id="10959" class="Keyword">import</a> <a id="10966" href="foundation.lawveres-fixed-point-theorem.html" class="Module">foundation.lawveres-fixed-point-theorem</a>
<a id="11006" class="Keyword">open</a> <a id="11011" class="Keyword">import</a> <a id="11018" href="foundation.locally-small-types.html" class="Module">foundation.locally-small-types</a>
<a id="11049" class="Keyword">open</a> <a id="11054" class="Keyword">import</a> <a id="11061" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="11093" class="Keyword">open</a> <a id="11098" class="Keyword">import</a> <a id="11105" href="foundation.lower-types-w-types.html" class="Module">foundation.lower-types-w-types</a>
<a id="11136" class="Keyword">open</a> <a id="11141" class="Keyword">import</a> <a id="11148" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="11165" class="Keyword">open</a> <a id="11170" class="Keyword">import</a> <a id="11177" href="foundation.mere-equality.html" class="Module">foundation.mere-equality</a>
<a id="11202" class="Keyword">open</a> <a id="11207" class="Keyword">import</a> <a id="11214" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="11243" class="Keyword">open</a> <a id="11248" class="Keyword">import</a> <a id="11255" href="foundation.monomorphisms.html" class="Module">foundation.monomorphisms</a>
<a id="11280" class="Keyword">open</a> <a id="11285" class="Keyword">import</a> <a id="11292" href="foundation.multisets.html" class="Module">foundation.multisets</a>
<a id="11313" class="Keyword">open</a> <a id="11318" class="Keyword">import</a> <a id="11325" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="11345" class="Keyword">open</a> <a id="11350" class="Keyword">import</a> <a id="11357" href="foundation.non-contractible-types.html" class="Module">foundation.non-contractible-types</a>
<a id="11391" class="Keyword">open</a> <a id="11396" class="Keyword">import</a> <a id="11403" href="foundation.path-algebra.html" class="Module">foundation.path-algebra</a>
<a id="11427" class="Keyword">open</a> <a id="11432" class="Keyword">import</a> <a id="11439" href="foundation.path-split-maps.html" class="Module">foundation.path-split-maps</a>
<a id="11466" class="Keyword">open</a> <a id="11471" class="Keyword">import</a> <a id="11478" href="foundation.polynomial-endofunctors.html" class="Module">foundation.polynomial-endofunctors</a>
<a id="11513" class="Keyword">open</a> <a id="11518" class="Keyword">import</a> <a id="11525" href="foundation.propositional-extensionality.html" class="Module">foundation.propositional-extensionality</a>
<a id="11565" class="Keyword">open</a> <a id="11570" class="Keyword">import</a> <a id="11577" href="foundation.propositional-maps.html" class="Module">foundation.propositional-maps</a>
<a id="11607" class="Keyword">open</a> <a id="11612" class="Keyword">import</a> <a id="11619" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="11656" class="Keyword">open</a> <a id="11661" class="Keyword">import</a> <a id="11668" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="11692" class="Keyword">open</a> <a id="11697" class="Keyword">import</a> <a id="11704" href="foundation.pullbacks.html" class="Module">foundation.pullbacks</a>
<a id="11725" class="Keyword">open</a> <a id="11730" class="Keyword">import</a> <a id="11737" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="11772" class="Keyword">open</a> <a id="11777" class="Keyword">import</a> <a id="11784" href="foundation.ranks-of-elements-w-types.html" class="Module">foundation.ranks-of-elements-w-types</a>
<a id="11821" class="Keyword">open</a> <a id="11826" class="Keyword">import</a> <a id="11833" href="foundation.reflecting-maps-equivalence-relations.html" class="Module">foundation.reflecting-maps-equivalence-relations</a>
<a id="11882" class="Keyword">open</a> <a id="11887" class="Keyword">import</a> <a id="11894" href="foundation.replacement.html" class="Module">foundation.replacement</a>
<a id="11917" class="Keyword">open</a> <a id="11922" class="Keyword">import</a> <a id="11929" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="11952" class="Keyword">open</a> <a id="11957" class="Keyword">import</a> <a id="11964" href="foundation.russells-paradox.html" class="Module">foundation.russells-paradox</a>
<a id="11992" class="Keyword">open</a> <a id="11997" class="Keyword">import</a> <a id="12004" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="12024" class="Keyword">open</a> <a id="12029" class="Keyword">import</a> <a id="12036" href="foundation.set-presented-types.html" class="Module">foundation.set-presented-types</a>
<a id="12067" class="Keyword">open</a> <a id="12072" class="Keyword">import</a> <a id="12079" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="12106" class="Keyword">open</a> <a id="12111" class="Keyword">import</a> <a id="12118" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="12134" class="Keyword">open</a> <a id="12139" class="Keyword">import</a> <a id="12146" href="foundation.singleton-induction.html" class="Module">foundation.singleton-induction</a>
<a id="12177" class="Keyword">open</a> <a id="12182" class="Keyword">import</a> <a id="12189" href="foundation.slice.html" class="Module">foundation.slice</a>
<a id="12206" class="Keyword">open</a> <a id="12211" class="Keyword">import</a> <a id="12218" href="foundation.small-maps.html" class="Module">foundation.small-maps</a>
<a id="12240" class="Keyword">open</a> <a id="12245" class="Keyword">import</a> <a id="12252" href="foundation.small-multisets.html" class="Module">foundation.small-multisets</a>
<a id="12279" class="Keyword">open</a> <a id="12284" class="Keyword">import</a> <a id="12291" href="foundation.small-types.html" class="Module">foundation.small-types</a>
<a id="12314" class="Keyword">open</a> <a id="12319" class="Keyword">import</a> <a id="12326" href="foundation.small-universes.html" class="Module">foundation.small-universes</a>
<a id="12353" class="Keyword">open</a> <a id="12358" class="Keyword">import</a> <a id="12365" href="foundation.split-surjective-maps.html" class="Module">foundation.split-surjective-maps</a>
<a id="12398" class="Keyword">open</a> <a id="12403" class="Keyword">import</a> <a id="12410" href="foundation.structure-identity-principle.html" class="Module">foundation.structure-identity-principle</a>
<a id="12450" class="Keyword">open</a> <a id="12455" class="Keyword">import</a> <a id="12462" href="foundation.structure.html" class="Module">foundation.structure</a>
<a id="12483" class="Keyword">open</a> <a id="12488" class="Keyword">import</a> <a id="12495" href="foundation.subterminal-types.html" class="Module">foundation.subterminal-types</a>
<a id="12524" class="Keyword">open</a> <a id="12529" class="Keyword">import</a> <a id="12536" href="foundation.subtype-identity-principle.html" class="Module">foundation.subtype-identity-principle</a>
<a id="12574" class="Keyword">open</a> <a id="12579" class="Keyword">import</a> <a id="12586" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="12606" class="Keyword">open</a> <a id="12611" class="Keyword">import</a> <a id="12618" href="foundation.subuniverses.html" class="Module">foundation.subuniverses</a>
<a id="12642" class="Keyword">open</a> <a id="12647" class="Keyword">import</a> <a id="12654" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="12681" class="Keyword">open</a> <a id="12686" class="Keyword">import</a> <a id="12693" href="foundation.truncated-equality.html" class="Module">foundation.truncated-equality</a>
<a id="12723" class="Keyword">open</a> <a id="12728" class="Keyword">import</a> <a id="12735" href="foundation.truncated-maps.html" class="Module">foundation.truncated-maps</a>
<a id="12761" class="Keyword">open</a> <a id="12766" class="Keyword">import</a> <a id="12773" href="foundation.truncated-types.html" class="Module">foundation.truncated-types</a>
<a id="12800" class="Keyword">open</a> <a id="12805" class="Keyword">import</a> <a id="12812" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="12841" class="Keyword">open</a> <a id="12846" class="Keyword">import</a> <a id="12853" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="12876" class="Keyword">open</a> <a id="12881" class="Keyword">import</a> <a id="12888" href="foundation.type-arithmetic-cartesian-product-types.html" class="Module">foundation.type-arithmetic-cartesian-product-types</a>
<a id="12939" class="Keyword">open</a> <a id="12944" class="Keyword">import</a> <a id="12951" href="foundation.type-arithmetic-coproduct-types.html" class="Module">foundation.type-arithmetic-coproduct-types</a>
<a id="12994" class="Keyword">open</a> <a id="12999" class="Keyword">import</a> <a id="13006" href="foundation.type-arithmetic-dependent-pair-types.html" class="Module">foundation.type-arithmetic-dependent-pair-types</a>
<a id="13054" class="Keyword">open</a> <a id="13059" class="Keyword">import</a> <a id="13066" href="foundation.type-arithmetic-empty-type.html" class="Module">foundation.type-arithmetic-empty-type</a>
<a id="13104" class="Keyword">open</a> <a id="13109" class="Keyword">import</a> <a id="13116" href="foundation.type-arithmetic-unit-type.html" class="Module">foundation.type-arithmetic-unit-type</a>
<a id="13153" class="Keyword">open</a> <a id="13158" class="Keyword">import</a> <a id="13165" href="foundation.uniqueness-image.html" class="Module">foundation.uniqueness-image</a>
<a id="13193" class="Keyword">open</a> <a id="13198" class="Keyword">import</a> <a id="13205" href="foundation.uniqueness-set-quotients.html" class="Module">foundation.uniqueness-set-quotients</a>
<a id="13241" class="Keyword">open</a> <a id="13246" class="Keyword">import</a> <a id="13253" href="foundation.uniqueness-set-truncations.html" class="Module">foundation.uniqueness-set-truncations</a>
<a id="13291" class="Keyword">open</a> <a id="13296" class="Keyword">import</a> <a id="13303" href="foundation.uniqueness-truncation.html" class="Module">foundation.uniqueness-truncation</a>
<a id="13336" class="Keyword">open</a> <a id="13341" class="Keyword">import</a> <a id="13348" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="13369" class="Keyword">open</a> <a id="13374" class="Keyword">import</a> <a id="13381" href="foundation.univalence-implies-function-extensionality.html" class="Module">foundation.univalence-implies-function-extensionality</a>
<a id="13435" class="Keyword">open</a> <a id="13440" class="Keyword">import</a> <a id="13447" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="13469" class="Keyword">open</a> <a id="13474" class="Keyword">import</a> <a id="13481" href="foundation.univalent-type-families.html" class="Module">foundation.univalent-type-families</a>
<a id="13516" class="Keyword">open</a> <a id="13521" class="Keyword">import</a> <a id="13528" href="foundation.universal-multiset.html" class="Module">foundation.universal-multiset</a>
<a id="13558" class="Keyword">open</a> <a id="13563" class="Keyword">import</a> <a id="13570" href="foundation.universal-property-booleans.html" class="Module">foundation.universal-property-booleans</a>
<a id="13609" class="Keyword">open</a> <a id="13614" class="Keyword">import</a> <a id="13621" href="foundation.universal-property-cartesian-product-types.html" class="Module">foundation.universal-property-cartesian-product-types</a>
<a id="13675" class="Keyword">open</a> <a id="13680" class="Keyword">import</a> <a id="13687" href="foundation.universal-property-coproduct-types.html" class="Module">foundation.universal-property-coproduct-types</a>
<a id="13733" class="Keyword">open</a> <a id="13738" class="Keyword">import</a> <a id="13745" href="foundation.universal-property-dependent-pair-types.html" class="Module">foundation.universal-property-dependent-pair-types</a>
<a id="13796" class="Keyword">open</a> <a id="13801" class="Keyword">import</a> <a id="13808" href="foundation.universal-property-empty-type.html" class="Module">foundation.universal-property-empty-type</a>
<a id="13849" class="Keyword">open</a> <a id="13854" class="Keyword">import</a> <a id="13861" href="foundation.universal-property-fiber-products.html" class="Module">foundation.universal-property-fiber-products</a>
<a id="13906" class="Keyword">open</a> <a id="13911" class="Keyword">import</a> <a id="13918" href="foundation.universal-property-identity-types.html" class="Module">foundation.universal-property-identity-types</a>
<a id="13963" class="Keyword">open</a> <a id="13968" class="Keyword">import</a> <a id="13975" href="foundation.universal-property-image.html" class="Module">foundation.universal-property-image</a>
<a id="14011" class="Keyword">open</a> <a id="14016" class="Keyword">import</a> <a id="14023" href="foundation.universal-property-maybe.html" class="Module">foundation.universal-property-maybe</a>
<a id="14059" class="Keyword">open</a> <a id="14064" class="Keyword">import</a> <a id="14071" href="foundation.universal-property-propositional-truncation-into-sets.html" class="Module">foundation.universal-property-propositional-truncation-into-sets</a>
<a id="14136" class="Keyword">open</a> <a id="14141" class="Keyword">import</a> <a id="14148" href="foundation.universal-property-propositional-truncation.html" class="Module">foundation.universal-property-propositional-truncation</a>
<a id="14203" class="Keyword">open</a> <a id="14208" class="Keyword">import</a> <a id="14215" href="foundation.universal-property-pullbacks.html" class="Module">foundation.universal-property-pullbacks</a>
<a id="14255" class="Keyword">open</a> <a id="14260" class="Keyword">import</a> <a id="14267" href="foundation.universal-property-set-quotients.html" class="Module">foundation.universal-property-set-quotients</a>
<a id="14311" class="Keyword">open</a> <a id="14316" class="Keyword">import</a> <a id="14323" href="foundation.universal-property-set-truncation.html" class="Module">foundation.universal-property-set-truncation</a>
<a id="14368" class="Keyword">open</a> <a id="14373" class="Keyword">import</a> <a id="14380" href="foundation.universal-property-truncation.html" class="Module">foundation.universal-property-truncation</a>
<a id="14421" class="Keyword">open</a> <a id="14426" class="Keyword">import</a> <a id="14433" href="foundation.universal-property-unit-type.html" class="Module">foundation.universal-property-unit-type</a>
<a id="14473" class="Keyword">open</a> <a id="14478" class="Keyword">import</a> <a id="14485" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="14512" class="Keyword">open</a> <a id="14517" class="Keyword">import</a> <a id="14524" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>
<a id="14551" class="Keyword">open</a> <a id="14556" class="Keyword">import</a> <a id="14563" href="foundation.w-types.html" class="Module">foundation.w-types</a>
<a id="14582" class="Keyword">open</a> <a id="14587" class="Keyword">import</a> <a id="14594" href="foundation.weak-function-extensionality.html" class="Module">foundation.weak-function-extensionality</a>
<a id="14634" class="Keyword">open</a> <a id="14639" class="Keyword">import</a> <a id="14646" href="foundation.weakly-constant-maps.html" class="Module">foundation.weakly-constant-maps</a>
</pre>
## Foundation Core

<pre class="Agda"><a id="14711" class="Keyword">open</a> <a id="14716" class="Keyword">import</a> <a id="14723" href="foundation-core.0-maps.html" class="Module">foundation-core.0-maps</a>
<a id="14746" class="Keyword">open</a> <a id="14751" class="Keyword">import</a> <a id="14758" href="foundation-core.1-types.html" class="Module">foundation-core.1-types</a>
<a id="14782" class="Keyword">open</a> <a id="14787" class="Keyword">import</a> <a id="14794" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="14834" class="Keyword">open</a> <a id="14839" class="Keyword">import</a> <a id="14846" href="foundation-core.coherently-invertible-maps.html" class="Module">foundation-core.coherently-invertible-maps</a>
<a id="14889" class="Keyword">open</a> <a id="14894" class="Keyword">import</a> <a id="14901" href="foundation-core.commuting-squares.html" class="Module">foundation-core.commuting-squares</a>
<a id="14935" class="Keyword">open</a> <a id="14940" class="Keyword">import</a> <a id="14947" href="foundation-core.constant-maps.html" class="Module">foundation-core.constant-maps</a>
<a id="14977" class="Keyword">open</a> <a id="14982" class="Keyword">import</a> <a id="14989" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="15023" class="Keyword">open</a> <a id="15028" class="Keyword">import</a> <a id="15035" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="15070" class="Keyword">open</a> <a id="15075" class="Keyword">import</a> <a id="15082" href="foundation-core.dependent-pair-types.html" class="Module">foundation-core.dependent-pair-types</a>
<a id="15119" class="Keyword">open</a> <a id="15124" class="Keyword">import</a> <a id="15131" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="15158" class="Keyword">open</a> <a id="15163" class="Keyword">import</a> <a id="15170" href="foundation-core.empty-types.html" class="Module">foundation-core.empty-types</a>
<a id="15198" class="Keyword">open</a> <a id="15203" class="Keyword">import</a> <a id="15210" href="foundation-core.equality-cartesian-product-types.html" class="Module">foundation-core.equality-cartesian-product-types</a>
<a id="15259" class="Keyword">open</a> <a id="15264" class="Keyword">import</a> <a id="15271" href="foundation-core.equality-dependent-pair-types.html" class="Module">foundation-core.equality-dependent-pair-types</a>
<a id="15317" class="Keyword">open</a> <a id="15322" class="Keyword">import</a> <a id="15329" href="foundation-core.equality-fibers-of-maps.html" class="Module">foundation-core.equality-fibers-of-maps</a>
<a id="15369" class="Keyword">open</a> <a id="15374" class="Keyword">import</a> <a id="15381" href="foundation-core.equivalence-induction.html" class="Module">foundation-core.equivalence-induction</a>
<a id="15419" class="Keyword">open</a> <a id="15424" class="Keyword">import</a> <a id="15431" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="15460" class="Keyword">open</a> <a id="15465" class="Keyword">import</a> <a id="15472" href="foundation-core.faithful-maps.html" class="Module">foundation-core.faithful-maps</a>
<a id="15502" class="Keyword">open</a> <a id="15507" class="Keyword">import</a> <a id="15514" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
<a id="15545" class="Keyword">open</a> <a id="15550" class="Keyword">import</a> <a id="15557" href="foundation-core.functions.html" class="Module">foundation-core.functions</a>
<a id="15583" class="Keyword">open</a> <a id="15588" class="Keyword">import</a> <a id="15595" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
<a id="15646" class="Keyword">open</a> <a id="15651" class="Keyword">import</a> <a id="15658" href="foundation-core.fundamental-theorem-of-identity-types.html" class="Module">foundation-core.fundamental-theorem-of-identity-types</a>
<a id="15712" class="Keyword">open</a> <a id="15717" class="Keyword">import</a> <a id="15724" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="15751" class="Keyword">open</a> <a id="15756" class="Keyword">import</a> <a id="15763" href="foundation-core.identity-systems.html" class="Module">foundation-core.identity-systems</a>
<a id="15796" class="Keyword">open</a> <a id="15801" class="Keyword">import</a> <a id="15808" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="15839" class="Keyword">open</a> <a id="15844" class="Keyword">import</a> <a id="15851" href="foundation-core.logical-equivalences.html" class="Module">foundation-core.logical-equivalences</a>
<a id="15888" class="Keyword">open</a> <a id="15893" class="Keyword">import</a> <a id="15900" href="foundation-core.negation.html" class="Module">foundation-core.negation</a>
<a id="15925" class="Keyword">open</a> <a id="15930" class="Keyword">import</a> <a id="15937" href="foundation-core.path-split-maps.html" class="Module">foundation-core.path-split-maps</a>
<a id="15969" class="Keyword">open</a> <a id="15974" class="Keyword">import</a> <a id="15981" href="foundation-core.propositional-maps.html" class="Module">foundation-core.propositional-maps</a>
<a id="16016" class="Keyword">open</a> <a id="16021" class="Keyword">import</a> <a id="16028" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="16057" class="Keyword">open</a> <a id="16062" class="Keyword">import</a> <a id="16069" href="foundation-core.retractions.html" class="Module">foundation-core.retractions</a>
<a id="16097" class="Keyword">open</a> <a id="16102" class="Keyword">import</a> <a id="16109" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
<a id="16134" class="Keyword">open</a> <a id="16139" class="Keyword">import</a> <a id="16146" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>
<a id="16167" class="Keyword">open</a> <a id="16172" class="Keyword">import</a> <a id="16179" href="foundation-core.singleton-induction.html" class="Module">foundation-core.singleton-induction</a>
<a id="16215" class="Keyword">open</a> <a id="16220" class="Keyword">import</a> <a id="16227" href="foundation-core.subtype-identity-principle.html" class="Module">foundation-core.subtype-identity-principle</a>
<a id="16270" class="Keyword">open</a> <a id="16275" class="Keyword">import</a> <a id="16282" href="foundation-core.subtypes.html" class="Module">foundation-core.subtypes</a>
<a id="16307" class="Keyword">open</a> <a id="16312" class="Keyword">import</a> <a id="16319" href="foundation-core.truncated-maps.html" class="Module">foundation-core.truncated-maps</a>
<a id="16350" class="Keyword">open</a> <a id="16355" class="Keyword">import</a> <a id="16362" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="16394" class="Keyword">open</a> <a id="16399" class="Keyword">import</a> <a id="16406" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
<a id="16440" class="Keyword">open</a> <a id="16445" class="Keyword">import</a> <a id="16452" href="foundation-core.type-arithmetic-cartesian-product-types.html" class="Module">foundation-core.type-arithmetic-cartesian-product-types</a>
<a id="16508" class="Keyword">open</a> <a id="16513" class="Keyword">import</a> <a id="16520" href="foundation-core.type-arithmetic-dependent-pair-types.html" class="Module">foundation-core.type-arithmetic-dependent-pair-types</a>
<a id="16573" class="Keyword">open</a> <a id="16578" class="Keyword">import</a> <a id="16585" href="foundation-core.univalence.html" class="Module">foundation-core.univalence</a>
<a id="16612" class="Keyword">open</a> <a id="16617" class="Keyword">import</a> <a id="16624" href="foundation-core.universe-levels.html" class="Module">foundation-core.universe-levels</a>
</pre>
## Graph theory

<pre class="Agda"><a id="16686" class="Keyword">open</a> <a id="16691" class="Keyword">import</a> <a id="16698" href="graph-theory.html" class="Module">graph-theory</a>
<a id="16711" class="Keyword">open</a> <a id="16716" class="Keyword">import</a> <a id="16723" href="graph-theory.connected-undirected-graphs.html" class="Module">graph-theory.connected-undirected-graphs</a>
<a id="16764" class="Keyword">open</a> <a id="16769" class="Keyword">import</a> <a id="16776" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="16805" class="Keyword">open</a> <a id="16810" class="Keyword">import</a> <a id="16817" href="graph-theory.edge-coloured-undirected-graphs.html" class="Module">graph-theory.edge-coloured-undirected-graphs</a>
<a id="16862" class="Keyword">open</a> <a id="16867" class="Keyword">import</a> <a id="16874" href="graph-theory.equivalences-undirected-graphs.html" class="Module">graph-theory.equivalences-undirected-graphs</a>
<a id="16918" class="Keyword">open</a> <a id="16923" class="Keyword">import</a> <a id="16930" href="graph-theory.finite-graphs.html" class="Module">graph-theory.finite-graphs</a>
<a id="16957" class="Keyword">open</a> <a id="16962" class="Keyword">import</a> <a id="16969" href="graph-theory.incidence-undirected-graphs.html" class="Module">graph-theory.incidence-undirected-graphs</a>
<a id="17010" class="Keyword">open</a> <a id="17015" class="Keyword">import</a> <a id="17022" href="graph-theory.mere-equivalences-undirected-graphs.html" class="Module">graph-theory.mere-equivalences-undirected-graphs</a>
<a id="17071" class="Keyword">open</a> <a id="17076" class="Keyword">import</a> <a id="17083" href="graph-theory.morphisms-directed-graphs.html" class="Module">graph-theory.morphisms-directed-graphs</a>
<a id="17122" class="Keyword">open</a> <a id="17127" class="Keyword">import</a> <a id="17134" href="graph-theory.morphisms-undirected-graphs.html" class="Module">graph-theory.morphisms-undirected-graphs</a>
<a id="17175" class="Keyword">open</a> <a id="17180" class="Keyword">import</a> <a id="17187" href="graph-theory.orientations-undirected-graphs.html" class="Module">graph-theory.orientations-undirected-graphs</a>
<a id="17231" class="Keyword">open</a> <a id="17236" class="Keyword">import</a> <a id="17243" href="graph-theory.paths-undirected-graphs.html" class="Module">graph-theory.paths-undirected-graphs</a>
<a id="17280" class="Keyword">open</a> <a id="17285" class="Keyword">import</a> <a id="17292" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>
<a id="17314" class="Keyword">open</a> <a id="17319" class="Keyword">import</a> <a id="17326" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
<a id="17356" class="Keyword">open</a> <a id="17361" class="Keyword">import</a> <a id="17368" href="graph-theory.regular-undirected-graphs.html" class="Module">graph-theory.regular-undirected-graphs</a>
<a id="17407" class="Keyword">open</a> <a id="17412" class="Keyword">import</a> <a id="17419" href="graph-theory.simple-undirected-graphs.html" class="Module">graph-theory.simple-undirected-graphs</a>
<a id="17457" class="Keyword">open</a> <a id="17462" class="Keyword">import</a> <a id="17469" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
## Group theory

<pre class="Agda"><a id="17530" class="Keyword">open</a> <a id="17535" class="Keyword">import</a> <a id="17542" href="group-theory.html" class="Module">group-theory</a>
<a id="17555" class="Keyword">open</a> <a id="17560" class="Keyword">import</a> <a id="17567" href="group-theory.abelian-groups.html" class="Module">group-theory.abelian-groups</a>
<a id="17595" class="Keyword">open</a> <a id="17600" class="Keyword">import</a> <a id="17607" href="group-theory.abelian-subgroups.html" class="Module">group-theory.abelian-subgroups</a>
<a id="17638" class="Keyword">open</a> <a id="17643" class="Keyword">import</a> <a id="17650" href="group-theory.abstract-group-torsors.html" class="Module">group-theory.abstract-group-torsors</a>
<a id="17686" class="Keyword">open</a> <a id="17691" class="Keyword">import</a> <a id="17698" href="group-theory.category-of-groups.html" class="Module">group-theory.category-of-groups</a>
<a id="17730" class="Keyword">open</a> <a id="17735" class="Keyword">import</a> <a id="17742" href="group-theory.category-of-semigroups.html" class="Module">group-theory.category-of-semigroups</a>
<a id="17778" class="Keyword">open</a> <a id="17783" class="Keyword">import</a> <a id="17790" href="group-theory.cayleys-theorem.html" class="Module">group-theory.cayleys-theorem</a>
<a id="17819" class="Keyword">open</a> <a id="17824" class="Keyword">import</a> <a id="17831" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="17867" class="Keyword">open</a> <a id="17872" class="Keyword">import</a> <a id="17879" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="17908" class="Keyword">open</a> <a id="17913" class="Keyword">import</a> <a id="17920" href="group-theory.concrete-subgroups.html" class="Module">group-theory.concrete-subgroups</a>
<a id="17952" class="Keyword">open</a> <a id="17957" class="Keyword">import</a> <a id="17964" href="group-theory.conjugation.html" class="Module">group-theory.conjugation</a>
<a id="17989" class="Keyword">open</a> <a id="17994" class="Keyword">import</a> <a id="18001" href="group-theory.embeddings-groups.html" class="Module">group-theory.embeddings-groups</a>
<a id="18032" class="Keyword">open</a> <a id="18037" class="Keyword">import</a> <a id="18044" href="group-theory.equivalences-group-actions.html" class="Module">group-theory.equivalences-group-actions</a>
<a id="18084" class="Keyword">open</a> <a id="18089" class="Keyword">import</a> <a id="18096" href="group-theory.equivalences-semigroups.html" class="Module">group-theory.equivalences-semigroups</a>
<a id="18133" class="Keyword">open</a> <a id="18138" class="Keyword">import</a> <a id="18145" href="group-theory.examples-higher-groups.html" class="Module">group-theory.examples-higher-groups</a>
<a id="18181" class="Keyword">open</a> <a id="18186" class="Keyword">import</a> <a id="18193" href="group-theory.furstenberg-groups.html" class="Module">group-theory.furstenberg-groups</a>
<a id="18225" class="Keyword">open</a> <a id="18230" class="Keyword">import</a> <a id="18237" href="group-theory.group-actions.html" class="Module">group-theory.group-actions</a>
<a id="18264" class="Keyword">open</a> <a id="18269" class="Keyword">import</a> <a id="18276" href="group-theory.groups.html" class="Module">group-theory.groups</a>
<a id="18296" class="Keyword">open</a> <a id="18301" class="Keyword">import</a> <a id="18308" href="group-theory.higher-groups.html" class="Module">group-theory.higher-groups</a>
<a id="18335" class="Keyword">open</a> <a id="18340" class="Keyword">import</a> <a id="18347" href="group-theory.homomorphisms-abelian-groups.html" class="Module">group-theory.homomorphisms-abelian-groups</a>
<a id="18389" class="Keyword">open</a> <a id="18394" class="Keyword">import</a> <a id="18401" href="group-theory.homomorphisms-group-actions.html" class="Module">group-theory.homomorphisms-group-actions</a>
<a id="18442" class="Keyword">open</a> <a id="18447" class="Keyword">import</a> <a id="18454" href="group-theory.homomorphisms-groups.html" class="Module">group-theory.homomorphisms-groups</a>
<a id="18488" class="Keyword">open</a> <a id="18493" class="Keyword">import</a> <a id="18500" href="group-theory.homomorphisms-monoids.html" class="Module">group-theory.homomorphisms-monoids</a>
<a id="18535" class="Keyword">open</a> <a id="18540" class="Keyword">import</a> <a id="18547" href="group-theory.homomorphisms-semigroups.html" class="Module">group-theory.homomorphisms-semigroups</a>
<a id="18585" class="Keyword">open</a> <a id="18590" class="Keyword">import</a> <a id="18597" href="group-theory.invertible-elements-monoids.html" class="Module">group-theory.invertible-elements-monoids</a>
<a id="18638" class="Keyword">open</a> <a id="18643" class="Keyword">import</a> <a id="18650" href="group-theory.isomorphisms-abelian-groups.html" class="Module">group-theory.isomorphisms-abelian-groups</a>
<a id="18691" class="Keyword">open</a> <a id="18696" class="Keyword">import</a> <a id="18703" href="group-theory.isomorphisms-group-actions.html" class="Module">group-theory.isomorphisms-group-actions</a>
<a id="18743" class="Keyword">open</a> <a id="18748" class="Keyword">import</a> <a id="18755" href="group-theory.isomorphisms-groups.html" class="Module">group-theory.isomorphisms-groups</a>
<a id="18788" class="Keyword">open</a> <a id="18793" class="Keyword">import</a> <a id="18800" href="group-theory.isomorphisms-semigroups.html" class="Module">group-theory.isomorphisms-semigroups</a>
<a id="18837" class="Keyword">open</a> <a id="18842" class="Keyword">import</a> <a id="18849" href="group-theory.mere-equivalences-group-actions.html" class="Module">group-theory.mere-equivalences-group-actions</a>
<a id="18894" class="Keyword">open</a> <a id="18899" class="Keyword">import</a> <a id="18906" href="group-theory.monoids.html" class="Module">group-theory.monoids</a>
<a id="18927" class="Keyword">open</a> <a id="18932" class="Keyword">import</a> <a id="18939" href="group-theory.orbits-group-actions.html" class="Module">group-theory.orbits-group-actions</a>
<a id="18973" class="Keyword">open</a> <a id="18978" class="Keyword">import</a> <a id="18985" href="group-theory.precategory-of-group-actions.html" class="Module">group-theory.precategory-of-group-actions</a>
<a id="19027" class="Keyword">open</a> <a id="19032" class="Keyword">import</a> <a id="19039" href="group-theory.precategory-of-groups.html" class="Module">group-theory.precategory-of-groups</a>
<a id="19074" class="Keyword">open</a> <a id="19079" class="Keyword">import</a> <a id="19086" href="group-theory.precategory-of-semigroups.html" class="Module">group-theory.precategory-of-semigroups</a>
<a id="19125" class="Keyword">open</a> <a id="19130" class="Keyword">import</a> <a id="19137" href="group-theory.principal-group-actions.html" class="Module">group-theory.principal-group-actions</a>
<a id="19174" class="Keyword">open</a> <a id="19179" class="Keyword">import</a> <a id="19186" href="group-theory.semigroups.html" class="Module">group-theory.semigroups</a>
<a id="19210" class="Keyword">open</a> <a id="19215" class="Keyword">import</a> <a id="19222" href="group-theory.sheargroups.html" class="Module">group-theory.sheargroups</a>
<a id="19247" class="Keyword">open</a> <a id="19252" class="Keyword">import</a> <a id="19259" href="group-theory.stabilizer-groups.html" class="Module">group-theory.stabilizer-groups</a>
<a id="19290" class="Keyword">open</a> <a id="19295" class="Keyword">import</a> <a id="19302" href="group-theory.subgroups.html" class="Module">group-theory.subgroups</a>
<a id="19325" class="Keyword">open</a> <a id="19330" class="Keyword">import</a> <a id="19337" href="group-theory.substitution-functor-group-actions.html" class="Module">group-theory.substitution-functor-group-actions</a>
<a id="19385" class="Keyword">open</a> <a id="19390" class="Keyword">import</a> <a id="19397" href="group-theory.symmetric-groups.html" class="Module">group-theory.symmetric-groups</a>
<a id="19427" class="Keyword">open</a> <a id="19432" class="Keyword">import</a> <a id="19439" href="group-theory.transitive-group-actions.html" class="Module">group-theory.transitive-group-actions</a>
</pre>
## Linear algebra

<pre class="Agda"><a id="19509" class="Keyword">open</a> <a id="19514" class="Keyword">import</a> <a id="19521" href="linear-algebra.html" class="Module">linear-algebra</a>
<a id="19536" class="Keyword">open</a> <a id="19541" class="Keyword">import</a> <a id="19548" href="linear-algebra.constant-matrices.html" class="Module">linear-algebra.constant-matrices</a>
<a id="19581" class="Keyword">open</a> <a id="19586" class="Keyword">import</a> <a id="19593" href="linear-algebra.constant-vectors.html" class="Module">linear-algebra.constant-vectors</a>
<a id="19625" class="Keyword">open</a> <a id="19630" class="Keyword">import</a> <a id="19637" href="linear-algebra.functoriality-matrices.html" class="Module">linear-algebra.functoriality-matrices</a>
<a id="19675" class="Keyword">open</a> <a id="19680" class="Keyword">import</a> <a id="19687" href="linear-algebra.functoriality-vectors.html" class="Module">linear-algebra.functoriality-vectors</a>
<a id="19724" class="Keyword">open</a> <a id="19729" class="Keyword">import</a> <a id="19736" href="linear-algebra.matrices-on-rings.html" class="Module">linear-algebra.matrices-on-rings</a>
<a id="19769" class="Keyword">open</a> <a id="19774" class="Keyword">import</a> <a id="19781" href="linear-algebra.matrices.html" class="Module">linear-algebra.matrices</a>
<a id="19805" class="Keyword">open</a> <a id="19810" class="Keyword">import</a> <a id="19817" href="linear-algebra.multiplication-matrices.html" class="Module">linear-algebra.multiplication-matrices</a>
<a id="19856" class="Keyword">open</a> <a id="19861" class="Keyword">import</a> <a id="19868" href="linear-algebra.scalar-multiplication-matrices.html" class="Module">linear-algebra.scalar-multiplication-matrices</a>
<a id="19914" class="Keyword">open</a> <a id="19919" class="Keyword">import</a> <a id="19926" href="linear-algebra.scalar-multiplication-vectors.html" class="Module">linear-algebra.scalar-multiplication-vectors</a>
<a id="19971" class="Keyword">open</a> <a id="19976" class="Keyword">import</a> <a id="19983" href="linear-algebra.transposition-matrices.html" class="Module">linear-algebra.transposition-matrices</a>
<a id="20021" class="Keyword">open</a> <a id="20026" class="Keyword">import</a> <a id="20033" href="linear-algebra.vectors-on-rings.html" class="Module">linear-algebra.vectors-on-rings</a>
<a id="20065" class="Keyword">open</a> <a id="20070" class="Keyword">import</a> <a id="20077" href="linear-algebra.vectors.html" class="Module">linear-algebra.vectors</a>
</pre>
## Order theory

<pre class="Agda"><a id="20130" class="Keyword">open</a> <a id="20135" class="Keyword">import</a> <a id="20142" href="order-theory.html" class="Module">order-theory</a>
<a id="20155" class="Keyword">open</a> <a id="20160" class="Keyword">import</a> <a id="20167" href="order-theory.chains-posets.html" class="Module">order-theory.chains-posets</a>
<a id="20194" class="Keyword">open</a> <a id="20199" class="Keyword">import</a> <a id="20206" href="order-theory.chains-preorders.html" class="Module">order-theory.chains-preorders</a>
<a id="20236" class="Keyword">open</a> <a id="20241" class="Keyword">import</a> <a id="20248" href="order-theory.decidable-subposets.html" class="Module">order-theory.decidable-subposets</a>
<a id="20281" class="Keyword">open</a> <a id="20286" class="Keyword">import</a> <a id="20293" href="order-theory.decidable-subpreorders.html" class="Module">order-theory.decidable-subpreorders</a>
<a id="20329" class="Keyword">open</a> <a id="20334" class="Keyword">import</a> <a id="20341" href="order-theory.finite-posets.html" class="Module">order-theory.finite-posets</a>
<a id="20368" class="Keyword">open</a> <a id="20373" class="Keyword">import</a> <a id="20380" href="order-theory.finite-preorders.html" class="Module">order-theory.finite-preorders</a>
<a id="20410" class="Keyword">open</a> <a id="20415" class="Keyword">import</a> <a id="20422" href="order-theory.finitely-graded-posets.html" class="Module">order-theory.finitely-graded-posets</a>
<a id="20458" class="Keyword">open</a> <a id="20463" class="Keyword">import</a> <a id="20470" href="order-theory.interval-subposets.html" class="Module">order-theory.interval-subposets</a>
<a id="20502" class="Keyword">open</a> <a id="20507" class="Keyword">import</a> <a id="20514" href="order-theory.largest-elements-posets.html" class="Module">order-theory.largest-elements-posets</a>
<a id="20551" class="Keyword">open</a> <a id="20556" class="Keyword">import</a> <a id="20563" href="order-theory.largest-elements-preorders.html" class="Module">order-theory.largest-elements-preorders</a>
<a id="20603" class="Keyword">open</a> <a id="20608" class="Keyword">import</a> <a id="20615" href="order-theory.least-elements-posets.html" class="Module">order-theory.least-elements-posets</a>
<a id="20650" class="Keyword">open</a> <a id="20655" class="Keyword">import</a> <a id="20662" href="order-theory.least-elements-preorders.html" class="Module">order-theory.least-elements-preorders</a>
<a id="20700" class="Keyword">open</a> <a id="20705" class="Keyword">import</a> <a id="20712" href="order-theory.locally-finite-posets.html" class="Module">order-theory.locally-finite-posets</a>
<a id="20747" class="Keyword">open</a> <a id="20752" class="Keyword">import</a> <a id="20759" href="order-theory.maximal-chains-posets.html" class="Module">order-theory.maximal-chains-posets</a>
<a id="20794" class="Keyword">open</a> <a id="20799" class="Keyword">import</a> <a id="20806" href="order-theory.maximal-chains-preorders.html" class="Module">order-theory.maximal-chains-preorders</a>
<a id="20844" class="Keyword">open</a> <a id="20849" class="Keyword">import</a> <a id="20856" href="order-theory.planar-binary-trees.html" class="Module">order-theory.planar-binary-trees</a>
<a id="20889" class="Keyword">open</a> <a id="20894" class="Keyword">import</a> <a id="20901" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="20921" class="Keyword">open</a> <a id="20926" class="Keyword">import</a> <a id="20933" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
<a id="20956" class="Keyword">open</a> <a id="20961" class="Keyword">import</a> <a id="20968" href="order-theory.subposets.html" class="Module">order-theory.subposets</a>
<a id="20991" class="Keyword">open</a> <a id="20996" class="Keyword">import</a> <a id="21003" href="order-theory.subpreorders.html" class="Module">order-theory.subpreorders</a>
<a id="21029" class="Keyword">open</a> <a id="21034" class="Keyword">import</a> <a id="21041" href="order-theory.total-posets.html" class="Module">order-theory.total-posets</a>
<a id="21067" class="Keyword">open</a> <a id="21072" class="Keyword">import</a> <a id="21079" href="order-theory.total-preorders.html" class="Module">order-theory.total-preorders</a>
</pre>
## Polytopes

<pre class="Agda"><a id="21135" class="Keyword">open</a> <a id="21140" class="Keyword">import</a> <a id="21147" href="polytopes.html" class="Module">polytopes</a>
<a id="21157" class="Keyword">open</a> <a id="21162" class="Keyword">import</a> <a id="21169" href="polytopes.abstract-polytopes.html" class="Module">polytopes.abstract-polytopes</a>
</pre>
## Ring theory

<pre class="Agda"><a id="21227" class="Keyword">open</a> <a id="21232" class="Keyword">import</a> <a id="21239" href="ring-theory.html" class="Module">ring-theory</a>
<a id="21251" class="Keyword">open</a> <a id="21256" class="Keyword">import</a> <a id="21263" href="ring-theory.commutative-rings.html" class="Module">ring-theory.commutative-rings</a>
<a id="21293" class="Keyword">open</a> <a id="21298" class="Keyword">import</a> <a id="21305" href="ring-theory.discrete-fields.html" class="Module">ring-theory.discrete-fields</a>
<a id="21333" class="Keyword">open</a> <a id="21338" class="Keyword">import</a> <a id="21345" href="ring-theory.division-rings.html" class="Module">ring-theory.division-rings</a>
<a id="21372" class="Keyword">open</a> <a id="21377" class="Keyword">import</a> <a id="21384" href="ring-theory.eisenstein-integers.html" class="Module">ring-theory.eisenstein-integers</a>
<a id="21416" class="Keyword">open</a> <a id="21421" class="Keyword">import</a> <a id="21428" href="ring-theory.gaussian-integers.html" class="Module">ring-theory.gaussian-integers</a>
<a id="21458" class="Keyword">open</a> <a id="21463" class="Keyword">import</a> <a id="21470" href="ring-theory.homomorphisms-commutative-rings.html" class="Module">ring-theory.homomorphisms-commutative-rings</a>
<a id="21514" class="Keyword">open</a> <a id="21519" class="Keyword">import</a> <a id="21526" href="ring-theory.homomorphisms-rings.html" class="Module">ring-theory.homomorphisms-rings</a>
<a id="21558" class="Keyword">open</a> <a id="21563" class="Keyword">import</a> <a id="21570" href="ring-theory.ideals.html" class="Module">ring-theory.ideals</a>
<a id="21589" class="Keyword">open</a> <a id="21594" class="Keyword">import</a> <a id="21601" href="ring-theory.invertible-elements-rings.html" class="Module">ring-theory.invertible-elements-rings</a>
<a id="21639" class="Keyword">open</a> <a id="21644" class="Keyword">import</a> <a id="21651" href="ring-theory.isomorphisms-commutative-rings.html" class="Module">ring-theory.isomorphisms-commutative-rings</a>
<a id="21694" class="Keyword">open</a> <a id="21699" class="Keyword">import</a> <a id="21706" href="ring-theory.isomorphisms-rings.html" class="Module">ring-theory.isomorphisms-rings</a>
<a id="21737" class="Keyword">open</a> <a id="21742" class="Keyword">import</a> <a id="21749" href="ring-theory.localizations-rings.html" class="Module">ring-theory.localizations-rings</a>
<a id="21781" class="Keyword">open</a> <a id="21786" class="Keyword">import</a> <a id="21793" href="ring-theory.nontrivial-rings.html" class="Module">ring-theory.nontrivial-rings</a>
<a id="21822" class="Keyword">open</a> <a id="21827" class="Keyword">import</a> <a id="21834" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
## Synthetic homotopy theory

<pre class="Agda"><a id="21895" class="Keyword">open</a> <a id="21900" class="Keyword">import</a> <a id="21907" href="synthetic-homotopy-theory.html" class="Module">synthetic-homotopy-theory</a>
<a id="21933" class="Keyword">open</a> <a id="21938" class="Keyword">import</a> <a id="21945" href="synthetic-homotopy-theory.23-pullbacks.html" class="Module">synthetic-homotopy-theory.23-pullbacks</a>
<a id="21984" class="Keyword">open</a> <a id="21989" class="Keyword">import</a> <a id="21996" href="synthetic-homotopy-theory.24-pushouts.html" class="Module">synthetic-homotopy-theory.24-pushouts</a>
<a id="22034" class="Keyword">open</a> <a id="22039" class="Keyword">import</a> <a id="22046" href="synthetic-homotopy-theory.25-cubical-diagrams.html" class="Module">synthetic-homotopy-theory.25-cubical-diagrams</a>
<a id="22092" class="Keyword">open</a> <a id="22097" class="Keyword">import</a> <a id="22104" href="synthetic-homotopy-theory.26-descent.html" class="Module">synthetic-homotopy-theory.26-descent</a>
<a id="22141" class="Keyword">open</a> <a id="22146" class="Keyword">import</a> <a id="22153" href="synthetic-homotopy-theory.26-id-pushout.html" class="Module">synthetic-homotopy-theory.26-id-pushout</a>
<a id="22193" class="Keyword">open</a> <a id="22198" class="Keyword">import</a> <a id="22205" href="synthetic-homotopy-theory.27-sequences.html" class="Module">synthetic-homotopy-theory.27-sequences</a>
<a id="22244" class="Keyword">open</a> <a id="22249" class="Keyword">import</a> <a id="22256" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
<a id="22289" class="Keyword">open</a> <a id="22294" class="Keyword">import</a> <a id="22301" href="synthetic-homotopy-theory.cyclic-types.html" class="Module">synthetic-homotopy-theory.cyclic-types</a>
<a id="22340" class="Keyword">open</a> <a id="22345" class="Keyword">import</a> <a id="22352" href="synthetic-homotopy-theory.double-loop-spaces.html" class="Module">synthetic-homotopy-theory.double-loop-spaces</a>
<a id="22397" class="Keyword">open</a> <a id="22402" class="Keyword">import</a> <a id="22409" href="synthetic-homotopy-theory.functoriality-loop-spaces.html" class="Module">synthetic-homotopy-theory.functoriality-loop-spaces</a>
<a id="22461" class="Keyword">open</a> <a id="22466" class="Keyword">import</a> <a id="22473" href="synthetic-homotopy-theory.groups-of-loops-in-1-types.html" class="Module">synthetic-homotopy-theory.groups-of-loops-in-1-types</a>
<a id="22526" class="Keyword">open</a> <a id="22531" class="Keyword">import</a> <a id="22538" href="synthetic-homotopy-theory.infinite-cyclic-types.html" class="Module">synthetic-homotopy-theory.infinite-cyclic-types</a>
<a id="22586" class="Keyword">open</a> <a id="22591" class="Keyword">import</a> <a id="22598" href="synthetic-homotopy-theory.interval-type.html" class="Module">synthetic-homotopy-theory.interval-type</a>
<a id="22638" class="Keyword">open</a> <a id="22643" class="Keyword">import</a> <a id="22650" href="synthetic-homotopy-theory.iterated-loop-spaces.html" class="Module">synthetic-homotopy-theory.iterated-loop-spaces</a>
<a id="22697" class="Keyword">open</a> <a id="22702" class="Keyword">import</a> <a id="22709" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
<a id="22747" class="Keyword">open</a> <a id="22752" class="Keyword">import</a> <a id="22759" href="synthetic-homotopy-theory.pointed-dependent-functions.html" class="Module">synthetic-homotopy-theory.pointed-dependent-functions</a>
<a id="22813" class="Keyword">open</a> <a id="22818" class="Keyword">import</a> <a id="22825" href="synthetic-homotopy-theory.pointed-equivalences.html" class="Module">synthetic-homotopy-theory.pointed-equivalences</a>
<a id="22872" class="Keyword">open</a> <a id="22877" class="Keyword">import</a> <a id="22884" href="synthetic-homotopy-theory.pointed-families-of-types.html" class="Module">synthetic-homotopy-theory.pointed-families-of-types</a>
<a id="22936" class="Keyword">open</a> <a id="22941" class="Keyword">import</a> <a id="22948" href="synthetic-homotopy-theory.pointed-homotopies.html" class="Module">synthetic-homotopy-theory.pointed-homotopies</a>
<a id="22993" class="Keyword">open</a> <a id="22998" class="Keyword">import</a> <a id="23005" href="synthetic-homotopy-theory.pointed-maps.html" class="Module">synthetic-homotopy-theory.pointed-maps</a>
<a id="23044" class="Keyword">open</a> <a id="23049" class="Keyword">import</a> <a id="23056" href="synthetic-homotopy-theory.pointed-types.html" class="Module">synthetic-homotopy-theory.pointed-types</a>
<a id="23096" class="Keyword">open</a> <a id="23101" class="Keyword">import</a> <a id="23108" href="synthetic-homotopy-theory.spaces.html" class="Module">synthetic-homotopy-theory.spaces</a>
<a id="23141" class="Keyword">open</a> <a id="23146" class="Keyword">import</a> <a id="23153" href="synthetic-homotopy-theory.triple-loop-spaces.html" class="Module">synthetic-homotopy-theory.triple-loop-spaces</a>
<a id="23198" class="Keyword">open</a> <a id="23203" class="Keyword">import</a> <a id="23210" href="synthetic-homotopy-theory.universal-cover-circle.html" class="Module">synthetic-homotopy-theory.universal-cover-circle</a>
</pre>
## Tutorials

<pre class="Agda"><a id="23286" class="Keyword">open</a> <a id="23291" class="Keyword">import</a> <a id="23298" href="tutorials.basic-agda.html" class="Module">tutorials.basic-agda</a>
</pre>
## Univalent combinatorics

<pre class="Agda"><a id="23360" class="Keyword">open</a> <a id="23365" class="Keyword">import</a> <a id="23372" href="univalent-combinatorics.html" class="Module">univalent-combinatorics</a>
<a id="23396" class="Keyword">open</a> <a id="23401" class="Keyword">import</a> <a id="23408" href="univalent-combinatorics.2-element-subtypes.html" class="Module">univalent-combinatorics.2-element-subtypes</a>
<a id="23451" class="Keyword">open</a> <a id="23456" class="Keyword">import</a> <a id="23463" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="23503" class="Keyword">open</a> <a id="23508" class="Keyword">import</a> <a id="23515" href="univalent-combinatorics.binomial-types.html" class="Module">univalent-combinatorics.binomial-types</a>
<a id="23554" class="Keyword">open</a> <a id="23559" class="Keyword">import</a> <a id="23566" href="univalent-combinatorics.cartesian-product-types.html" class="Module">univalent-combinatorics.cartesian-product-types</a>
<a id="23614" class="Keyword">open</a> <a id="23619" class="Keyword">import</a> <a id="23626" href="univalent-combinatorics.classical-finite-types.html" class="Module">univalent-combinatorics.classical-finite-types</a>
<a id="23673" class="Keyword">open</a> <a id="23678" class="Keyword">import</a> <a id="23685" href="univalent-combinatorics.complements-isolated-points.html" class="Module">univalent-combinatorics.complements-isolated-points</a>
<a id="23737" class="Keyword">open</a> <a id="23742" class="Keyword">import</a> <a id="23749" href="univalent-combinatorics.coproduct-types.html" class="Module">univalent-combinatorics.coproduct-types</a>
<a id="23789" class="Keyword">open</a> <a id="23794" class="Keyword">import</a> <a id="23801" href="univalent-combinatorics.counting-decidable-subtypes.html" class="Module">univalent-combinatorics.counting-decidable-subtypes</a>
<a id="23853" class="Keyword">open</a> <a id="23858" class="Keyword">import</a> <a id="23865" href="univalent-combinatorics.counting-dependent-function-types.html" class="Module">univalent-combinatorics.counting-dependent-function-types</a>
<a id="23923" class="Keyword">open</a> <a id="23928" class="Keyword">import</a> <a id="23935" href="univalent-combinatorics.counting-dependent-pair-types.html" class="Module">univalent-combinatorics.counting-dependent-pair-types</a>
<a id="23989" class="Keyword">open</a> <a id="23994" class="Keyword">import</a> <a id="24001" href="univalent-combinatorics.counting-fibers-of-maps.html" class="Module">univalent-combinatorics.counting-fibers-of-maps</a>
<a id="24049" class="Keyword">open</a> <a id="24054" class="Keyword">import</a> <a id="24061" href="univalent-combinatorics.counting-function-types.html" class="Module">univalent-combinatorics.counting-function-types</a>
<a id="24109" class="Keyword">open</a> <a id="24114" class="Keyword">import</a> <a id="24121" href="univalent-combinatorics.counting-maybe.html" class="Module">univalent-combinatorics.counting-maybe</a>
<a id="24160" class="Keyword">open</a> <a id="24165" class="Keyword">import</a> <a id="24172" href="univalent-combinatorics.counting.html" class="Module">univalent-combinatorics.counting</a>
<a id="24205" class="Keyword">open</a> <a id="24210" class="Keyword">import</a> <a id="24217" href="univalent-combinatorics.cubes.html" class="Module">univalent-combinatorics.cubes</a>
<a id="24247" class="Keyword">open</a> <a id="24252" class="Keyword">import</a> <a id="24259" href="univalent-combinatorics.decidable-dependent-function-types.html" class="Module">univalent-combinatorics.decidable-dependent-function-types</a>
<a id="24318" class="Keyword">open</a> <a id="24323" class="Keyword">import</a> <a id="24330" href="univalent-combinatorics.decidable-dependent-pair-types.html" class="Module">univalent-combinatorics.decidable-dependent-pair-types</a>
<a id="24385" class="Keyword">open</a> <a id="24390" class="Keyword">import</a> <a id="24397" href="univalent-combinatorics.decidable-subtypes.html" class="Module">univalent-combinatorics.decidable-subtypes</a>
<a id="24440" class="Keyword">open</a> <a id="24445" class="Keyword">import</a> <a id="24452" href="univalent-combinatorics.dependent-product-finite-types.html" class="Module">univalent-combinatorics.dependent-product-finite-types</a>
<a id="24507" class="Keyword">open</a> <a id="24512" class="Keyword">import</a> <a id="24519" href="univalent-combinatorics.dependent-sum-finite-types.html" class="Module">univalent-combinatorics.dependent-sum-finite-types</a>
<a id="24570" class="Keyword">open</a> <a id="24575" class="Keyword">import</a> <a id="24582" href="univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.html" class="Module">univalent-combinatorics.distributivity-of-set-truncation-over-finite-products</a>
<a id="24660" class="Keyword">open</a> <a id="24665" class="Keyword">import</a> <a id="24672" href="univalent-combinatorics.double-counting.html" class="Module">univalent-combinatorics.double-counting</a>
<a id="24712" class="Keyword">open</a> <a id="24717" class="Keyword">import</a> <a id="24724" href="univalent-combinatorics.embeddings-standard-finite-types.html" class="Module">univalent-combinatorics.embeddings-standard-finite-types</a>
<a id="24781" class="Keyword">open</a> <a id="24786" class="Keyword">import</a> <a id="24793" href="univalent-combinatorics.embeddings.html" class="Module">univalent-combinatorics.embeddings</a>
<a id="24828" class="Keyword">open</a> <a id="24833" class="Keyword">import</a> <a id="24840" href="univalent-combinatorics.equality-finite-types.html" class="Module">univalent-combinatorics.equality-finite-types</a>
<a id="24886" class="Keyword">open</a> <a id="24891" class="Keyword">import</a> <a id="24898" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a>
<a id="24953" class="Keyword">open</a> <a id="24958" class="Keyword">import</a> <a id="24965" href="univalent-combinatorics.equivalences-cubes.html" class="Module">univalent-combinatorics.equivalences-cubes</a>
<a id="25008" class="Keyword">open</a> <a id="25013" class="Keyword">import</a> <a id="25020" href="univalent-combinatorics.equivalences-standard-finite-types.html" class="Module">univalent-combinatorics.equivalences-standard-finite-types</a>
<a id="25079" class="Keyword">open</a> <a id="25084" class="Keyword">import</a> <a id="25091" href="univalent-combinatorics.equivalences.html" class="Module">univalent-combinatorics.equivalences</a>
<a id="25128" class="Keyword">open</a> <a id="25133" class="Keyword">import</a> <a id="25140" href="univalent-combinatorics.fibers-of-maps-between-finite-types.html" class="Module">univalent-combinatorics.fibers-of-maps-between-finite-types</a>
<a id="25200" class="Keyword">open</a> <a id="25205" class="Keyword">import</a> <a id="25212" href="univalent-combinatorics.finite-choice.html" class="Module">univalent-combinatorics.finite-choice</a>
<a id="25250" class="Keyword">open</a> <a id="25255" class="Keyword">import</a> <a id="25262" href="univalent-combinatorics.finite-connected-components.html" class="Module">univalent-combinatorics.finite-connected-components</a>
<a id="25314" class="Keyword">open</a> <a id="25319" class="Keyword">import</a> <a id="25326" href="univalent-combinatorics.finite-function-types.html" class="Module">univalent-combinatorics.finite-function-types</a>
<a id="25372" class="Keyword">open</a> <a id="25377" class="Keyword">import</a> <a id="25384" href="univalent-combinatorics.finite-presentations.html" class="Module">univalent-combinatorics.finite-presentations</a>
<a id="25429" class="Keyword">open</a> <a id="25434" class="Keyword">import</a> <a id="25441" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="25478" class="Keyword">open</a> <a id="25483" class="Keyword">import</a> <a id="25490" href="univalent-combinatorics.finitely-presented-types.html" class="Module">univalent-combinatorics.finitely-presented-types</a>
<a id="25539" class="Keyword">open</a> <a id="25544" class="Keyword">import</a> <a id="25551" href="univalent-combinatorics.image-of-maps.html" class="Module">univalent-combinatorics.image-of-maps</a>
<a id="25589" class="Keyword">open</a> <a id="25594" class="Keyword">import</a> <a id="25601" href="univalent-combinatorics.inequality-types-with-counting.html" class="Module">univalent-combinatorics.inequality-types-with-counting</a>
<a id="25656" class="Keyword">open</a> <a id="25661" class="Keyword">import</a> <a id="25668" href="univalent-combinatorics.injective-maps.html" class="Module">univalent-combinatorics.injective-maps</a>
<a id="25707" class="Keyword">open</a> <a id="25712" class="Keyword">import</a> <a id="25719" href="univalent-combinatorics.lists.html" class="Module">univalent-combinatorics.lists</a>
<a id="25749" class="Keyword">open</a> <a id="25754" class="Keyword">import</a> <a id="25761" href="univalent-combinatorics.maybe.html" class="Module">univalent-combinatorics.maybe</a>
<a id="25791" class="Keyword">open</a> <a id="25796" class="Keyword">import</a> <a id="25803" href="univalent-combinatorics.orientations-cubes.html" class="Module">univalent-combinatorics.orientations-cubes</a>
<a id="25846" class="Keyword">open</a> <a id="25851" class="Keyword">import</a> <a id="25858" href="univalent-combinatorics.pi-finite-types.html" class="Module">univalent-combinatorics.pi-finite-types</a>
<a id="25898" class="Keyword">open</a> <a id="25903" class="Keyword">import</a> <a id="25910" href="univalent-combinatorics.pigeonhole-principle.html" class="Module">univalent-combinatorics.pigeonhole-principle</a>
<a id="25955" class="Keyword">open</a> <a id="25960" class="Keyword">import</a> <a id="25967" href="univalent-combinatorics.presented-pi-finite-types.html" class="Module">univalent-combinatorics.presented-pi-finite-types</a>
<a id="26017" class="Keyword">open</a> <a id="26022" class="Keyword">import</a> <a id="26029" href="univalent-combinatorics.ramsey-theory.html" class="Module">univalent-combinatorics.ramsey-theory</a>
<a id="26067" class="Keyword">open</a> <a id="26072" class="Keyword">import</a> <a id="26079" href="univalent-combinatorics.retracts-of-finite-types.html" class="Module">univalent-combinatorics.retracts-of-finite-types</a>
<a id="26128" class="Keyword">open</a> <a id="26133" class="Keyword">import</a> <a id="26140" href="univalent-combinatorics.skipping-element-standard-finite-types.html" class="Module">univalent-combinatorics.skipping-element-standard-finite-types</a>
<a id="26203" class="Keyword">open</a> <a id="26208" class="Keyword">import</a> <a id="26215" href="univalent-combinatorics.species.html" class="Module">univalent-combinatorics.species</a>
<a id="26247" class="Keyword">open</a> <a id="26252" class="Keyword">import</a> <a id="26259" href="univalent-combinatorics.standard-finite-pruned-trees.html" class="Module">univalent-combinatorics.standard-finite-pruned-trees</a>
<a id="26312" class="Keyword">open</a> <a id="26317" class="Keyword">import</a> <a id="26324" href="univalent-combinatorics.standard-finite-trees.html" class="Module">univalent-combinatorics.standard-finite-trees</a>
<a id="26370" class="Keyword">open</a> <a id="26375" class="Keyword">import</a> <a id="26382" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
<a id="26428" class="Keyword">open</a> <a id="26433" class="Keyword">import</a> <a id="26440" href="univalent-combinatorics.sums-of-natural-numbers.html" class="Module">univalent-combinatorics.sums-of-natural-numbers</a>
<a id="26488" class="Keyword">open</a> <a id="26493" class="Keyword">import</a> <a id="26500" href="univalent-combinatorics.surjective-maps.html" class="Module">univalent-combinatorics.surjective-maps</a>
</pre>
## Wild algebra

<pre class="Agda"><a id="26570" class="Keyword">open</a> <a id="26575" class="Keyword">import</a> <a id="26582" href="wild-algebra.html" class="Module">wild-algebra</a>
<a id="26595" class="Keyword">open</a> <a id="26600" class="Keyword">import</a> <a id="26607" href="wild-algebra.magmas.html" class="Module">wild-algebra.magmas</a>
<a id="26627" class="Keyword">open</a> <a id="26632" class="Keyword">import</a> <a id="26639" href="wild-algebra.universal-property-lists-wild-monoids.html" class="Module">wild-algebra.universal-property-lists-wild-monoids</a>
<a id="26690" class="Keyword">open</a> <a id="26695" class="Keyword">import</a> <a id="26702" href="wild-algebra.wild-groups.html" class="Module">wild-algebra.wild-groups</a>
<a id="26727" class="Keyword">open</a> <a id="26732" class="Keyword">import</a> <a id="26739" href="wild-algebra.wild-monoids.html" class="Module">wild-algebra.wild-monoids</a>
<a id="26765" class="Keyword">open</a> <a id="26770" class="Keyword">import</a> <a id="26777" href="wild-algebra.wild-unital-magmas.html" class="Module">wild-algebra.wild-unital-magmas</a>
</pre>
## Everything

See the list of all Agda modules [here](everything.html).

