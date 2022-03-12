# Univalent mathematics in Agda

Welcome to the website of the `agda-unimath` formalization project.

[![build](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml/badge.svg?branch=master)](https://github.com/UniMath/agda-unimath/actions/workflows/ci.yaml)

<pre class="Agda"><a id="281" class="Symbol">{-#</a> <a id="285" class="Keyword">OPTIONS</a> <a id="293" class="Pragma">--without-K</a> <a id="305" class="Pragma">--exact-split</a> <a id="319" class="Symbol">#-}</a>
</pre>
## Category theory

<pre class="Agda"><a id="356" class="Keyword">open</a> <a id="361" class="Keyword">import</a> <a id="368" href="category-theory.adjunctions-large-precategories.html" class="Module">category-theory.adjunctions-large-precategories</a>
<a id="416" class="Keyword">open</a> <a id="421" class="Keyword">import</a> <a id="428" href="category-theory.categories.html" class="Module">category-theory.categories</a>
<a id="455" class="Keyword">open</a> <a id="460" class="Keyword">import</a> <a id="467" href="category-theory.equivalences-categories.html" class="Module">category-theory.equivalences-categories</a>
<a id="507" class="Keyword">open</a> <a id="512" class="Keyword">import</a> <a id="519" href="category-theory.equivalences-large-precategories.html" class="Module">category-theory.equivalences-large-precategories</a>
<a id="568" class="Keyword">open</a> <a id="573" class="Keyword">import</a> <a id="580" href="category-theory.equivalences-precategories.html" class="Module">category-theory.equivalences-precategories</a>
<a id="623" class="Keyword">open</a> <a id="628" class="Keyword">import</a> <a id="635" href="category-theory.functors-categories.html" class="Module">category-theory.functors-categories</a>
<a id="671" class="Keyword">open</a> <a id="676" class="Keyword">import</a> <a id="683" href="category-theory.functors-large-precategories.html" class="Module">category-theory.functors-large-precategories</a>
<a id="728" class="Keyword">open</a> <a id="733" class="Keyword">import</a> <a id="740" href="category-theory.functors-precategories.html" class="Module">category-theory.functors-precategories</a>
<a id="779" class="Keyword">open</a> <a id="784" class="Keyword">import</a> <a id="791" href="category-theory.homotopies-natural-transformations-large-precategories.html" class="Module">category-theory.homotopies-natural-transformations-large-precategories</a>
<a id="862" class="Keyword">open</a> <a id="867" class="Keyword">import</a> <a id="874" href="category-theory.isomorphisms-categories.html" class="Module">category-theory.isomorphisms-categories</a>
<a id="914" class="Keyword">open</a> <a id="919" class="Keyword">import</a> <a id="926" href="category-theory.isomorphisms-large-precategories.html" class="Module">category-theory.isomorphisms-large-precategories</a>
<a id="975" class="Keyword">open</a> <a id="980" class="Keyword">import</a> <a id="987" href="category-theory.isomorphisms-precategories.html" class="Module">category-theory.isomorphisms-precategories</a>
<a id="1030" class="Keyword">open</a> <a id="1035" class="Keyword">import</a> <a id="1042" href="category-theory.large-categories.html" class="Module">category-theory.large-categories</a>
<a id="1075" class="Keyword">open</a> <a id="1080" class="Keyword">import</a> <a id="1087" href="category-theory.large-precategories.html" class="Module">category-theory.large-precategories</a>
<a id="1123" class="Keyword">open</a> <a id="1128" class="Keyword">import</a> <a id="1135" href="category-theory.monomorphisms-large-precategories.html" class="Module">category-theory.monomorphisms-large-precategories</a>
<a id="1185" class="Keyword">open</a> <a id="1190" class="Keyword">import</a> <a id="1197" href="category-theory.natural-isomorphisms-categories.html" class="Module">category-theory.natural-isomorphisms-categories</a>
<a id="1245" class="Keyword">open</a> <a id="1250" class="Keyword">import</a> <a id="1257" href="category-theory.natural-isomorphisms-large-precategories.html" class="Module">category-theory.natural-isomorphisms-large-precategories</a>
<a id="1314" class="Keyword">open</a> <a id="1319" class="Keyword">import</a> <a id="1326" href="category-theory.natural-isomorphisms-precategories.html" class="Module">category-theory.natural-isomorphisms-precategories</a>
<a id="1377" class="Keyword">open</a> <a id="1382" class="Keyword">import</a> <a id="1389" href="category-theory.natural-transformations-categories.html" class="Module">category-theory.natural-transformations-categories</a>
<a id="1440" class="Keyword">open</a> <a id="1445" class="Keyword">import</a> <a id="1452" href="category-theory.natural-transformations-large-precategories.html" class="Module">category-theory.natural-transformations-large-precategories</a>
<a id="1512" class="Keyword">open</a> <a id="1517" class="Keyword">import</a> <a id="1524" href="category-theory.natural-transformations-precategories.html" class="Module">category-theory.natural-transformations-precategories</a>
<a id="1578" class="Keyword">open</a> <a id="1583" class="Keyword">import</a> <a id="1590" href="category-theory.precategories.html" class="Module">category-theory.precategories</a>
</pre>
## Elementary number theory

<pre class="Agda"><a id="1662" class="Keyword">open</a> <a id="1667" class="Keyword">import</a> <a id="1674" href="elementary-number-theory.html" class="Module">elementary-number-theory</a>
<a id="1699" class="Keyword">open</a> <a id="1704" class="Keyword">import</a> <a id="1711" href="elementary-number-theory.absolute-value-integers.html" class="Module">elementary-number-theory.absolute-value-integers</a>
<a id="1760" class="Keyword">open</a> <a id="1765" class="Keyword">import</a> <a id="1772" href="elementary-number-theory.addition-integers.html" class="Module">elementary-number-theory.addition-integers</a>
<a id="1815" class="Keyword">open</a> <a id="1820" class="Keyword">import</a> <a id="1827" href="elementary-number-theory.addition-natural-numbers.html" class="Module">elementary-number-theory.addition-natural-numbers</a>
<a id="1877" class="Keyword">open</a> <a id="1882" class="Keyword">import</a> <a id="1889" href="elementary-number-theory.binomial-coefficients.html" class="Module">elementary-number-theory.binomial-coefficients</a>
<a id="1936" class="Keyword">open</a> <a id="1941" class="Keyword">import</a> <a id="1948" href="elementary-number-theory.classical-finite-types.html" class="Module">elementary-number-theory.classical-finite-types</a>
<a id="1996" class="Keyword">open</a> <a id="2001" class="Keyword">import</a> <a id="2008" href="elementary-number-theory.collatz-bijection.html" class="Module">elementary-number-theory.collatz-bijection</a>
<a id="2051" class="Keyword">open</a> <a id="2056" class="Keyword">import</a> <a id="2063" href="elementary-number-theory.collatz-conjecture.html" class="Module">elementary-number-theory.collatz-conjecture</a>
<a id="2107" class="Keyword">open</a> <a id="2112" class="Keyword">import</a> <a id="2119" href="elementary-number-theory.congruence-integers.html" class="Module">elementary-number-theory.congruence-integers</a>
<a id="2164" class="Keyword">open</a> <a id="2169" class="Keyword">import</a> <a id="2176" href="elementary-number-theory.congruence-natural-numbers.html" class="Module">elementary-number-theory.congruence-natural-numbers</a>
<a id="2228" class="Keyword">open</a> <a id="2233" class="Keyword">import</a> <a id="2240" href="elementary-number-theory.decidable-dependent-function-types.html" class="Module">elementary-number-theory.decidable-dependent-function-types</a>
<a id="2300" class="Keyword">open</a> <a id="2305" class="Keyword">import</a> <a id="2312" href="elementary-number-theory.decidable-dependent-pair-types.html" class="Module">elementary-number-theory.decidable-dependent-pair-types</a>
<a id="2368" class="Keyword">open</a> <a id="2373" class="Keyword">import</a> <a id="2380" href="elementary-number-theory.difference-integers.html" class="Module">elementary-number-theory.difference-integers</a>
<a id="2425" class="Keyword">open</a> <a id="2430" class="Keyword">import</a> <a id="2437" href="elementary-number-theory.distance-integers.html" class="Module">elementary-number-theory.distance-integers</a>
<a id="2480" class="Keyword">open</a> <a id="2485" class="Keyword">import</a> <a id="2492" href="elementary-number-theory.distance-natural-numbers.html" class="Module">elementary-number-theory.distance-natural-numbers</a>
<a id="2542" class="Keyword">open</a> <a id="2547" class="Keyword">import</a> <a id="2554" href="elementary-number-theory.divisibility-integers.html" class="Module">elementary-number-theory.divisibility-integers</a>
<a id="2601" class="Keyword">open</a> <a id="2606" class="Keyword">import</a> <a id="2613" href="elementary-number-theory.divisibility-natural-numbers.html" class="Module">elementary-number-theory.divisibility-natural-numbers</a>
<a id="2667" class="Keyword">open</a> <a id="2672" class="Keyword">import</a> <a id="2679" href="elementary-number-theory.divisibility-standard-finite-types.html" class="Module">elementary-number-theory.divisibility-standard-finite-types</a>
<a id="2739" class="Keyword">open</a> <a id="2744" class="Keyword">import</a> <a id="2751" href="elementary-number-theory.equality-integers.html" class="Module">elementary-number-theory.equality-integers</a>
<a id="2794" class="Keyword">open</a> <a id="2799" class="Keyword">import</a> <a id="2806" href="elementary-number-theory.equality-natural-numbers.html" class="Module">elementary-number-theory.equality-natural-numbers</a>
<a id="2856" class="Keyword">open</a> <a id="2861" class="Keyword">import</a> <a id="2868" href="elementary-number-theory.euclidean-division-natural-numbers.html" class="Module">elementary-number-theory.euclidean-division-natural-numbers</a>
<a id="2928" class="Keyword">open</a> <a id="2933" class="Keyword">import</a> <a id="2940" href="elementary-number-theory.eulers-totient-function.html" class="Module">elementary-number-theory.eulers-totient-function</a>
<a id="2989" class="Keyword">open</a> <a id="2994" class="Keyword">import</a> <a id="3001" href="elementary-number-theory.exponentiation-natural-numbers.html" class="Module">elementary-number-theory.exponentiation-natural-numbers</a>
<a id="3057" class="Keyword">open</a> <a id="3062" class="Keyword">import</a> <a id="3069" href="elementary-number-theory.factorials.html" class="Module">elementary-number-theory.factorials</a>
<a id="3105" class="Keyword">open</a> <a id="3110" class="Keyword">import</a> <a id="3117" href="elementary-number-theory.falling-factorials.html" class="Module">elementary-number-theory.falling-factorials</a>
<a id="3161" class="Keyword">open</a> <a id="3166" class="Keyword">import</a> <a id="3173" href="elementary-number-theory.fibonacci-sequence.html" class="Module">elementary-number-theory.fibonacci-sequence</a>
<a id="3217" class="Keyword">open</a> <a id="3222" class="Keyword">import</a> <a id="3229" href="elementary-number-theory.finitary-natural-numbers.html" class="Module">elementary-number-theory.finitary-natural-numbers</a>
<a id="3279" class="Keyword">open</a> <a id="3284" class="Keyword">import</a> <a id="3291" href="elementary-number-theory.finitely-cyclic-maps.html" class="Module">elementary-number-theory.finitely-cyclic-maps</a>
<a id="3337" class="Keyword">open</a> <a id="3342" class="Keyword">import</a> <a id="3349" href="elementary-number-theory.fractions.html" class="Module">elementary-number-theory.fractions</a>
<a id="3384" class="Keyword">open</a> <a id="3389" class="Keyword">import</a> <a id="3396" href="elementary-number-theory.goldbach-conjecture.html" class="Module">elementary-number-theory.goldbach-conjecture</a>
<a id="3441" class="Keyword">open</a> <a id="3446" class="Keyword">import</a> <a id="3453" href="elementary-number-theory.greatest-common-divisor-integers.html" class="Module">elementary-number-theory.greatest-common-divisor-integers</a>
<a id="3511" class="Keyword">open</a> <a id="3516" class="Keyword">import</a> <a id="3523" href="elementary-number-theory.greatest-common-divisor-natural-numbers.html" class="Module">elementary-number-theory.greatest-common-divisor-natural-numbers</a>
<a id="3588" class="Keyword">open</a> <a id="3593" class="Keyword">import</a> <a id="3600" href="elementary-number-theory.inequality-integers.html" class="Module">elementary-number-theory.inequality-integers</a>
<a id="3645" class="Keyword">open</a> <a id="3650" class="Keyword">import</a> <a id="3657" href="elementary-number-theory.inequality-natural-numbers.html" class="Module">elementary-number-theory.inequality-natural-numbers</a>
<a id="3709" class="Keyword">open</a> <a id="3714" class="Keyword">import</a> <a id="3721" href="elementary-number-theory.inequality-standard-finite-types.html" class="Module">elementary-number-theory.inequality-standard-finite-types</a>
<a id="3779" class="Keyword">open</a> <a id="3784" class="Keyword">import</a> <a id="3791" href="elementary-number-theory.infinitude-of-primes.html" class="Module">elementary-number-theory.infinitude-of-primes</a>
<a id="3837" class="Keyword">open</a> <a id="3842" class="Keyword">import</a> <a id="3849" href="elementary-number-theory.integers.html" class="Module">elementary-number-theory.integers</a>
<a id="3883" class="Keyword">open</a> <a id="3888" class="Keyword">import</a> <a id="3895" href="elementary-number-theory.iterating-functions.html" class="Module">elementary-number-theory.iterating-functions</a>
<a id="3940" class="Keyword">open</a> <a id="3945" class="Keyword">import</a> <a id="3952" href="elementary-number-theory.lower-bounds-natural-numbers.html" class="Module">elementary-number-theory.lower-bounds-natural-numbers</a>
<a id="4006" class="Keyword">open</a> <a id="4011" class="Keyword">import</a> <a id="4018" href="elementary-number-theory.modular-arithmetic-standard-finite-types.html" class="Module">elementary-number-theory.modular-arithmetic-standard-finite-types</a>
<a id="4084" class="Keyword">open</a> <a id="4089" class="Keyword">import</a> <a id="4096" href="elementary-number-theory.modular-arithmetic.html" class="Module">elementary-number-theory.modular-arithmetic</a>
<a id="4140" class="Keyword">open</a> <a id="4145" class="Keyword">import</a> <a id="4152" href="elementary-number-theory.multiplication-integers.html" class="Module">elementary-number-theory.multiplication-integers</a>
<a id="4201" class="Keyword">open</a> <a id="4206" class="Keyword">import</a> <a id="4213" href="elementary-number-theory.multiplication-natural-numbers.html" class="Module">elementary-number-theory.multiplication-natural-numbers</a>
<a id="4269" class="Keyword">open</a> <a id="4274" class="Keyword">import</a> <a id="4281" href="elementary-number-theory.natural-numbers.html" class="Module">elementary-number-theory.natural-numbers</a>
<a id="4322" class="Keyword">open</a> <a id="4327" class="Keyword">import</a> <a id="4334" href="elementary-number-theory.ordinal-induction-natural-numbers.html" class="Module">elementary-number-theory.ordinal-induction-natural-numbers</a>
<a id="4393" class="Keyword">open</a> <a id="4398" class="Keyword">import</a> <a id="4405" href="elementary-number-theory.prime-numbers.html" class="Module">elementary-number-theory.prime-numbers</a>
<a id="4444" class="Keyword">open</a> <a id="4449" class="Keyword">import</a> <a id="4456" href="elementary-number-theory.products-of-natural-numbers.html" class="Module">elementary-number-theory.products-of-natural-numbers</a>
<a id="4509" class="Keyword">open</a> <a id="4514" class="Keyword">import</a> <a id="4521" href="elementary-number-theory.proper-divisors-natural-numbers.html" class="Module">elementary-number-theory.proper-divisors-natural-numbers</a>
<a id="4578" class="Keyword">open</a> <a id="4583" class="Keyword">import</a> <a id="4590" href="elementary-number-theory.rational-numbers.html" class="Module">elementary-number-theory.rational-numbers</a>
<a id="4632" class="Keyword">open</a> <a id="4637" class="Keyword">import</a> <a id="4644" href="elementary-number-theory.relatively-prime-integers.html" class="Module">elementary-number-theory.relatively-prime-integers</a>
<a id="4695" class="Keyword">open</a> <a id="4700" class="Keyword">import</a> <a id="4707" href="elementary-number-theory.relatively-prime-natural-numbers.html" class="Module">elementary-number-theory.relatively-prime-natural-numbers</a>
<a id="4765" class="Keyword">open</a> <a id="4770" class="Keyword">import</a> <a id="4777" href="elementary-number-theory.repeating-element-standard-finite-type.html" class="Module">elementary-number-theory.repeating-element-standard-finite-type</a>
<a id="4841" class="Keyword">open</a> <a id="4846" class="Keyword">import</a> <a id="4853" href="elementary-number-theory.retracts-of-natural-numbers.html" class="Module">elementary-number-theory.retracts-of-natural-numbers</a>
<a id="4906" class="Keyword">open</a> <a id="4911" class="Keyword">import</a> <a id="4918" href="elementary-number-theory.retracts-of-standard-finite-types.html" class="Module">elementary-number-theory.retracts-of-standard-finite-types</a>
<a id="4977" class="Keyword">open</a> <a id="4982" class="Keyword">import</a> <a id="4989" href="elementary-number-theory.skipping-element-standard-finite-type.html" class="Module">elementary-number-theory.skipping-element-standard-finite-type</a>
<a id="5052" class="Keyword">open</a> <a id="5057" class="Keyword">import</a> <a id="5064" href="elementary-number-theory.stirling-numbers-of-the-second-kind.html" class="Module">elementary-number-theory.stirling-numbers-of-the-second-kind</a>
<a id="5125" class="Keyword">open</a> <a id="5130" class="Keyword">import</a> <a id="5137" href="elementary-number-theory.strong-induction-natural-numbers.html" class="Module">elementary-number-theory.strong-induction-natural-numbers</a>
<a id="5195" class="Keyword">open</a> <a id="5200" class="Keyword">import</a> <a id="5207" href="elementary-number-theory.sums-of-natural-numbers.html" class="Module">elementary-number-theory.sums-of-natural-numbers</a>
<a id="5256" class="Keyword">open</a> <a id="5261" class="Keyword">import</a> <a id="5268" href="elementary-number-theory.triangular-numbers.html" class="Module">elementary-number-theory.triangular-numbers</a>
<a id="5312" class="Keyword">open</a> <a id="5317" class="Keyword">import</a> <a id="5324" href="elementary-number-theory.twin-prime-conjecture.html" class="Module">elementary-number-theory.twin-prime-conjecture</a>
<a id="5371" class="Keyword">open</a> <a id="5376" class="Keyword">import</a> <a id="5383" href="elementary-number-theory.universal-property-natural-numbers.html" class="Module">elementary-number-theory.universal-property-natural-numbers</a>
<a id="5443" class="Keyword">open</a> <a id="5448" class="Keyword">import</a> <a id="5455" href="elementary-number-theory.upper-bounds-natural-numbers.html" class="Module">elementary-number-theory.upper-bounds-natural-numbers</a>
<a id="5509" class="Keyword">open</a> <a id="5514" class="Keyword">import</a> <a id="5521" href="elementary-number-theory.well-ordering-principle-natural-numbers.html" class="Module">elementary-number-theory.well-ordering-principle-natural-numbers</a>
<a id="5586" class="Keyword">open</a> <a id="5591" class="Keyword">import</a> <a id="5598" href="elementary-number-theory.well-ordering-principle-standard-finite-types.html" class="Module">elementary-number-theory.well-ordering-principle-standard-finite-types</a>
</pre>
## Finite group theory

<pre class="Agda"><a id="5706" class="Keyword">open</a> <a id="5711" class="Keyword">import</a> <a id="5718" href="finite-group-theory.abstract-quaternion-group.html" class="Module">finite-group-theory.abstract-quaternion-group</a>
<a id="5764" class="Keyword">open</a> <a id="5769" class="Keyword">import</a> <a id="5776" href="finite-group-theory.concrete-quaternion-group.html" class="Module">finite-group-theory.concrete-quaternion-group</a>
<a id="5822" class="Keyword">open</a> <a id="5827" class="Keyword">import</a> <a id="5834" href="finite-group-theory.finite-groups.html" class="Module">finite-group-theory.finite-groups</a>
<a id="5868" class="Keyword">open</a> <a id="5873" class="Keyword">import</a> <a id="5880" href="finite-group-theory.orbits-permutations.html" class="Module">finite-group-theory.orbits-permutations</a>
<a id="5920" class="Keyword">open</a> <a id="5925" class="Keyword">import</a> <a id="5932" href="finite-group-theory.transpositions.html" class="Module">finite-group-theory.transpositions</a>
</pre>
## Foundation

<pre class="Agda"><a id="5995" class="Keyword">open</a> <a id="6000" class="Keyword">import</a> <a id="6007" href="foundation.html" class="Module">foundation</a>
<a id="6018" class="Keyword">open</a> <a id="6023" class="Keyword">import</a> <a id="6030" href="foundation.0-maps.html" class="Module">foundation.0-maps</a>
<a id="6048" class="Keyword">open</a> <a id="6053" class="Keyword">import</a> <a id="6060" href="foundation.1-types.html" class="Module">foundation.1-types</a>
<a id="6079" class="Keyword">open</a> <a id="6084" class="Keyword">import</a> <a id="6091" href="foundation.2-types.html" class="Module">foundation.2-types</a>
<a id="6110" class="Keyword">open</a> <a id="6115" class="Keyword">import</a> <a id="6122" href="foundation.algebras-polynomial-endofunctors.html" class="Module">foundation.algebras-polynomial-endofunctors</a>
<a id="6166" class="Keyword">open</a> <a id="6171" class="Keyword">import</a> <a id="6178" href="foundation.automorphisms.html" class="Module">foundation.automorphisms</a>
<a id="6203" class="Keyword">open</a> <a id="6208" class="Keyword">import</a> <a id="6215" href="foundation.axiom-of-choice.html" class="Module">foundation.axiom-of-choice</a>
<a id="6242" class="Keyword">open</a> <a id="6247" class="Keyword">import</a> <a id="6254" href="foundation.binary-embeddings.html" class="Module">foundation.binary-embeddings</a>
<a id="6283" class="Keyword">open</a> <a id="6288" class="Keyword">import</a> <a id="6295" href="foundation.binary-equivalences.html" class="Module">foundation.binary-equivalences</a>
<a id="6326" class="Keyword">open</a> <a id="6331" class="Keyword">import</a> <a id="6338" href="foundation.binary-relations.html" class="Module">foundation.binary-relations</a>
<a id="6366" class="Keyword">open</a> <a id="6371" class="Keyword">import</a> <a id="6378" href="foundation.boolean-reflection.html" class="Module">foundation.boolean-reflection</a>
<a id="6408" class="Keyword">open</a> <a id="6413" class="Keyword">import</a> <a id="6420" href="foundation.booleans.html" class="Module">foundation.booleans</a>
<a id="6440" class="Keyword">open</a> <a id="6445" class="Keyword">import</a> <a id="6452" href="foundation.cantors-diagonal-argument.html" class="Module">foundation.cantors-diagonal-argument</a>
<a id="6489" class="Keyword">open</a> <a id="6494" class="Keyword">import</a> <a id="6501" href="foundation.cartesian-product-types.html" class="Module">foundation.cartesian-product-types</a>
<a id="6536" class="Keyword">open</a> <a id="6541" class="Keyword">import</a> <a id="6548" href="foundation.choice-of-representatives-equivalence-relation.html" class="Module">foundation.choice-of-representatives-equivalence-relation</a>
<a id="6606" class="Keyword">open</a> <a id="6611" class="Keyword">import</a> <a id="6618" href="foundation.coherently-invertible-maps.html" class="Module">foundation.coherently-invertible-maps</a>
<a id="6656" class="Keyword">open</a> <a id="6661" class="Keyword">import</a> <a id="6668" href="foundation.commuting-squares.html" class="Module">foundation.commuting-squares</a>
<a id="6697" class="Keyword">open</a> <a id="6702" class="Keyword">import</a> <a id="6709" href="foundation.complements.html" class="Module">foundation.complements</a>
<a id="6732" class="Keyword">open</a> <a id="6737" class="Keyword">import</a> <a id="6744" href="foundation.conjunction.html" class="Module">foundation.conjunction</a>
<a id="6767" class="Keyword">open</a> <a id="6772" class="Keyword">import</a> <a id="6779" href="foundation.connected-components-universes.html" class="Module">foundation.connected-components-universes</a>
<a id="6821" class="Keyword">open</a> <a id="6826" class="Keyword">import</a> <a id="6833" href="foundation.connected-components.html" class="Module">foundation.connected-components</a>
<a id="6865" class="Keyword">open</a> <a id="6870" class="Keyword">import</a> <a id="6877" href="foundation.connected-types.html" class="Module">foundation.connected-types</a>
<a id="6904" class="Keyword">open</a> <a id="6909" class="Keyword">import</a> <a id="6916" href="foundation.constant-maps.html" class="Module">foundation.constant-maps</a>
<a id="6941" class="Keyword">open</a> <a id="6946" class="Keyword">import</a> <a id="6953" href="foundation.contractible-maps.html" class="Module">foundation.contractible-maps</a>
<a id="6982" class="Keyword">open</a> <a id="6987" class="Keyword">import</a> <a id="6994" href="foundation.contractible-types.html" class="Module">foundation.contractible-types</a>
<a id="7024" class="Keyword">open</a> <a id="7029" class="Keyword">import</a> <a id="7036" href="foundation.coproduct-types.html" class="Module">foundation.coproduct-types</a>
<a id="7063" class="Keyword">open</a> <a id="7068" class="Keyword">import</a> <a id="7075" href="foundation.coslice.html" class="Module">foundation.coslice</a>
<a id="7094" class="Keyword">open</a> <a id="7099" class="Keyword">import</a> <a id="7106" href="foundation.decidable-dependent-function-types.html" class="Module">foundation.decidable-dependent-function-types</a>
<a id="7152" class="Keyword">open</a> <a id="7157" class="Keyword">import</a> <a id="7164" href="foundation.decidable-dependent-pair-types.html" class="Module">foundation.decidable-dependent-pair-types</a>
<a id="7206" class="Keyword">open</a> <a id="7211" class="Keyword">import</a> <a id="7218" href="foundation.decidable-embeddings.html" class="Module">foundation.decidable-embeddings</a>
<a id="7250" class="Keyword">open</a> <a id="7255" class="Keyword">import</a> <a id="7262" href="foundation.decidable-equality.html" class="Module">foundation.decidable-equality</a>
<a id="7292" class="Keyword">open</a> <a id="7297" class="Keyword">import</a> <a id="7304" href="foundation.decidable-maps.html" class="Module">foundation.decidable-maps</a>
<a id="7330" class="Keyword">open</a> <a id="7335" class="Keyword">import</a> <a id="7342" href="foundation.decidable-propositions.html" class="Module">foundation.decidable-propositions</a>
<a id="7376" class="Keyword">open</a> <a id="7381" class="Keyword">import</a> <a id="7388" href="foundation.decidable-subtypes.html" class="Module">foundation.decidable-subtypes</a>
<a id="7418" class="Keyword">open</a> <a id="7423" class="Keyword">import</a> <a id="7430" href="foundation.decidable-types.html" class="Module">foundation.decidable-types</a>
<a id="7457" class="Keyword">open</a> <a id="7462" class="Keyword">import</a> <a id="7469" href="foundation.dependent-pair-types.html" class="Module">foundation.dependent-pair-types</a>
<a id="7501" class="Keyword">open</a> <a id="7506" class="Keyword">import</a> <a id="7513" href="foundation.diagonal-maps-of-types.html" class="Module">foundation.diagonal-maps-of-types</a>
<a id="7547" class="Keyword">open</a> <a id="7552" class="Keyword">import</a> <a id="7559" href="foundation.disjunction.html" class="Module">foundation.disjunction</a>
<a id="7582" class="Keyword">open</a> <a id="7587" class="Keyword">import</a> <a id="7594" href="foundation.distributivity-of-dependent-functions-over-coproduct-types.html" class="Module">foundation.distributivity-of-dependent-functions-over-coproduct-types</a>
<a id="7664" class="Keyword">open</a> <a id="7669" class="Keyword">import</a> <a id="7676" href="foundation.distributivity-of-dependent-functions-over-dependent-pairs.html" class="Module">foundation.distributivity-of-dependent-functions-over-dependent-pairs</a>
<a id="7746" class="Keyword">open</a> <a id="7751" class="Keyword">import</a> <a id="7758" href="foundation.double-negation.html" class="Module">foundation.double-negation</a>
<a id="7785" class="Keyword">open</a> <a id="7790" class="Keyword">import</a> <a id="7797" href="foundation.effective-maps-equivalence-relations.html" class="Module">foundation.effective-maps-equivalence-relations</a>
<a id="7845" class="Keyword">open</a> <a id="7850" class="Keyword">import</a> <a id="7857" href="foundation.elementhood-relation-w-types.html" class="Module">foundation.elementhood-relation-w-types</a>
<a id="7897" class="Keyword">open</a> <a id="7902" class="Keyword">import</a> <a id="7909" href="foundation.embeddings.html" class="Module">foundation.embeddings</a>
<a id="7931" class="Keyword">open</a> <a id="7936" class="Keyword">import</a> <a id="7943" href="foundation.empty-types.html" class="Module">foundation.empty-types</a>
<a id="7966" class="Keyword">open</a> <a id="7971" class="Keyword">import</a> <a id="7978" href="foundation.epimorphisms-with-respect-to-sets.html" class="Module">foundation.epimorphisms-with-respect-to-sets</a>
<a id="8023" class="Keyword">open</a> <a id="8028" class="Keyword">import</a> <a id="8035" href="foundation.equality-cartesian-product-types.html" class="Module">foundation.equality-cartesian-product-types</a>
<a id="8079" class="Keyword">open</a> <a id="8084" class="Keyword">import</a> <a id="8091" href="foundation.equality-coproduct-types.html" class="Module">foundation.equality-coproduct-types</a>
<a id="8127" class="Keyword">open</a> <a id="8132" class="Keyword">import</a> <a id="8139" href="foundation.equality-dependent-function-types.html" class="Module">foundation.equality-dependent-function-types</a>
<a id="8184" class="Keyword">open</a> <a id="8189" class="Keyword">import</a> <a id="8196" href="foundation.equality-dependent-pair-types.html" class="Module">foundation.equality-dependent-pair-types</a>
<a id="8237" class="Keyword">open</a> <a id="8242" class="Keyword">import</a> <a id="8249" href="foundation.equality-fibers-of-maps.html" class="Module">foundation.equality-fibers-of-maps</a>
<a id="8284" class="Keyword">open</a> <a id="8289" class="Keyword">import</a> <a id="8296" href="foundation.equivalence-classes.html" class="Module">foundation.equivalence-classes</a>
<a id="8327" class="Keyword">open</a> <a id="8332" class="Keyword">import</a> <a id="8339" href="foundation.equivalence-induction.html" class="Module">foundation.equivalence-induction</a>
<a id="8372" class="Keyword">open</a> <a id="8377" class="Keyword">import</a> <a id="8384" href="foundation.equivalence-relations.html" class="Module">foundation.equivalence-relations</a>
<a id="8417" class="Keyword">open</a> <a id="8422" class="Keyword">import</a> <a id="8429" href="foundation.equivalences-maybe.html" class="Module">foundation.equivalences-maybe</a>
<a id="8459" class="Keyword">open</a> <a id="8464" class="Keyword">import</a> <a id="8471" href="foundation.equivalences.html" class="Module">foundation.equivalences</a>
<a id="8495" class="Keyword">open</a> <a id="8500" class="Keyword">import</a> <a id="8507" href="foundation.existential-quantification.html" class="Module">foundation.existential-quantification</a>
<a id="8545" class="Keyword">open</a> <a id="8550" class="Keyword">import</a> <a id="8557" href="foundation.extensional-w-types.html" class="Module">foundation.extensional-w-types</a>
<a id="8588" class="Keyword">open</a> <a id="8593" class="Keyword">import</a> <a id="8600" href="foundation.faithful-maps.html" class="Module">foundation.faithful-maps</a>
<a id="8625" class="Keyword">open</a> <a id="8630" class="Keyword">import</a> <a id="8637" href="foundation.fiber-inclusions.html" class="Module">foundation.fiber-inclusions</a>
<a id="8665" class="Keyword">open</a> <a id="8670" class="Keyword">import</a> <a id="8677" href="foundation.fibered-maps.html" class="Module">foundation.fibered-maps</a>
<a id="8701" class="Keyword">open</a> <a id="8706" class="Keyword">import</a> <a id="8713" href="foundation.fibers-of-maps.html" class="Module">foundation.fibers-of-maps</a>
<a id="8739" class="Keyword">open</a> <a id="8744" class="Keyword">import</a> <a id="8751" href="foundation.function-extensionality.html" class="Module">foundation.function-extensionality</a>
<a id="8786" class="Keyword">open</a> <a id="8791" class="Keyword">import</a> <a id="8798" href="foundation.functions.html" class="Module">foundation.functions</a>
<a id="8819" class="Keyword">open</a> <a id="8824" class="Keyword">import</a> <a id="8831" href="foundation.functoriality-cartesian-product-types.html" class="Module">foundation.functoriality-cartesian-product-types</a>
<a id="8880" class="Keyword">open</a> <a id="8885" class="Keyword">import</a> <a id="8892" href="foundation.functoriality-coproduct-types.html" class="Module">foundation.functoriality-coproduct-types</a>
<a id="8933" class="Keyword">open</a> <a id="8938" class="Keyword">import</a> <a id="8945" href="foundation.functoriality-dependent-function-types.html" class="Module">foundation.functoriality-dependent-function-types</a>
<a id="8995" class="Keyword">open</a> <a id="9000" class="Keyword">import</a> <a id="9007" href="foundation.functoriality-dependent-pair-types.html" class="Module">foundation.functoriality-dependent-pair-types</a>
<a id="9053" class="Keyword">open</a> <a id="9058" class="Keyword">import</a> <a id="9065" href="foundation.functoriality-function-types.html" class="Module">foundation.functoriality-function-types</a>
<a id="9105" class="Keyword">open</a> <a id="9110" class="Keyword">import</a> <a id="9117" href="foundation.functoriality-propositional-truncation.html" class="Module">foundation.functoriality-propositional-truncation</a>
<a id="9167" class="Keyword">open</a> <a id="9172" class="Keyword">import</a> <a id="9179" href="foundation.functoriality-set-quotients.html" class="Module">foundation.functoriality-set-quotients</a>
<a id="9218" class="Keyword">open</a> <a id="9223" class="Keyword">import</a> <a id="9230" href="foundation.functoriality-set-truncation.html" class="Module">foundation.functoriality-set-truncation</a>
<a id="9270" class="Keyword">open</a> <a id="9275" class="Keyword">import</a> <a id="9282" href="foundation.functoriality-w-types.html" class="Module">foundation.functoriality-w-types</a>
<a id="9315" class="Keyword">open</a> <a id="9320" class="Keyword">import</a> <a id="9327" href="foundation.fundamental-theorem-of-identity-types.html" class="Module">foundation.fundamental-theorem-of-identity-types</a>
<a id="9376" class="Keyword">open</a> <a id="9381" class="Keyword">import</a> <a id="9388" href="foundation.global-choice.html" class="Module">foundation.global-choice</a>
<a id="9413" class="Keyword">open</a> <a id="9418" class="Keyword">import</a> <a id="9425" href="foundation.homotopies.html" class="Module">foundation.homotopies</a>
<a id="9447" class="Keyword">open</a> <a id="9452" class="Keyword">import</a> <a id="9459" href="foundation.identity-systems.html" class="Module">foundation.identity-systems</a>
<a id="9487" class="Keyword">open</a> <a id="9492" class="Keyword">import</a> <a id="9499" href="foundation.identity-types.html" class="Module">foundation.identity-types</a>
<a id="9525" class="Keyword">open</a> <a id="9530" class="Keyword">import</a> <a id="9537" href="foundation.images.html" class="Module">foundation.images</a>
<a id="9555" class="Keyword">open</a> <a id="9560" class="Keyword">import</a> <a id="9567" href="foundation.impredicative-encodings.html" class="Module">foundation.impredicative-encodings</a>
<a id="9602" class="Keyword">open</a> <a id="9607" class="Keyword">import</a> <a id="9614" href="foundation.indexed-w-types.html" class="Module">foundation.indexed-w-types</a>
<a id="9641" class="Keyword">open</a> <a id="9646" class="Keyword">import</a> <a id="9653" href="foundation.induction-principle-propositional-truncation.html" class="Module">foundation.induction-principle-propositional-truncation</a>
<a id="9709" class="Keyword">open</a> <a id="9714" class="Keyword">import</a> <a id="9721" href="foundation.induction-w-types.html" class="Module">foundation.induction-w-types</a>
<a id="9750" class="Keyword">open</a> <a id="9755" class="Keyword">import</a> <a id="9762" href="foundation.inequality-w-types.html" class="Module">foundation.inequality-w-types</a>
<a id="9792" class="Keyword">open</a> <a id="9797" class="Keyword">import</a> <a id="9804" href="foundation.injective-maps.html" class="Module">foundation.injective-maps</a>
<a id="9830" class="Keyword">open</a> <a id="9835" class="Keyword">import</a> <a id="9842" href="foundation.interchange-law.html" class="Module">foundation.interchange-law</a>
<a id="9869" class="Keyword">open</a> <a id="9874" class="Keyword">import</a> <a id="9881" href="foundation.involutions.html" class="Module">foundation.involutions</a>
<a id="9904" class="Keyword">open</a> <a id="9909" class="Keyword">import</a> <a id="9916" href="foundation.isolated-points.html" class="Module">foundation.isolated-points</a>
<a id="9943" class="Keyword">open</a> <a id="9948" class="Keyword">import</a> <a id="9955" href="foundation.isomorphisms-of-sets.html" class="Module">foundation.isomorphisms-of-sets</a>
<a id="9987" class="Keyword">open</a> <a id="9992" class="Keyword">import</a> <a id="9999" href="foundation.law-of-excluded-middle.html" class="Module">foundation.law-of-excluded-middle</a>
<a id="10033" class="Keyword">open</a> <a id="10038" class="Keyword">import</a> <a id="10045" href="foundation.lawveres-fixed-point-theorem.html" class="Module">foundation.lawveres-fixed-point-theorem</a>
<a id="10085" class="Keyword">open</a> <a id="10090" class="Keyword">import</a> <a id="10097" href="foundation.locally-small-types.html" class="Module">foundation.locally-small-types</a>
<a id="10128" class="Keyword">open</a> <a id="10133" class="Keyword">import</a> <a id="10140" href="foundation.logical-equivalences.html" class="Module">foundation.logical-equivalences</a>
<a id="10172" class="Keyword">open</a> <a id="10177" class="Keyword">import</a> <a id="10184" href="foundation.maybe.html" class="Module">foundation.maybe</a>
<a id="10201" class="Keyword">open</a> <a id="10206" class="Keyword">import</a> <a id="10213" href="foundation.mere-equality.html" class="Module">foundation.mere-equality</a>
<a id="10238" class="Keyword">open</a> <a id="10243" class="Keyword">import</a> <a id="10250" href="foundation.mere-equivalences.html" class="Module">foundation.mere-equivalences</a>
<a id="10279" class="Keyword">open</a> <a id="10284" class="Keyword">import</a> <a id="10291" href="foundation.monomorphisms.html" class="Module">foundation.monomorphisms</a>
<a id="10316" class="Keyword">open</a> <a id="10321" class="Keyword">import</a> <a id="10328" href="foundation.multisets.html" class="Module">foundation.multisets</a>
<a id="10349" class="Keyword">open</a> <a id="10354" class="Keyword">import</a> <a id="10361" href="foundation.negation.html" class="Module">foundation.negation</a>
<a id="10381" class="Keyword">open</a> <a id="10386" class="Keyword">import</a> <a id="10393" href="foundation.non-contractible-types.html" class="Module">foundation.non-contractible-types</a>
<a id="10427" class="Keyword">open</a> <a id="10432" class="Keyword">import</a> <a id="10439" href="foundation.path-algebra.html" class="Module">foundation.path-algebra</a>
<a id="10463" class="Keyword">open</a> <a id="10468" class="Keyword">import</a> <a id="10475" href="foundation.path-split-maps.html" class="Module">foundation.path-split-maps</a>
<a id="10502" class="Keyword">open</a> <a id="10507" class="Keyword">import</a> <a id="10514" href="foundation.polynomial-endofunctors.html" class="Module">foundation.polynomial-endofunctors</a>
<a id="10549" class="Keyword">open</a> <a id="10554" class="Keyword">import</a> <a id="10561" href="foundation.propositional-extensionality.html" class="Module">foundation.propositional-extensionality</a>
<a id="10601" class="Keyword">open</a> <a id="10606" class="Keyword">import</a> <a id="10613" href="foundation.propositional-maps.html" class="Module">foundation.propositional-maps</a>
<a id="10643" class="Keyword">open</a> <a id="10648" class="Keyword">import</a> <a id="10655" href="foundation.propositional-truncations.html" class="Module">foundation.propositional-truncations</a>
<a id="10692" class="Keyword">open</a> <a id="10697" class="Keyword">import</a> <a id="10704" href="foundation.propositions.html" class="Module">foundation.propositions</a>
<a id="10728" class="Keyword">open</a> <a id="10733" class="Keyword">import</a> <a id="10740" href="foundation.pullbacks.html" class="Module">foundation.pullbacks</a>
<a id="10761" class="Keyword">open</a> <a id="10766" class="Keyword">import</a> <a id="10773" href="foundation.raising-universe-levels.html" class="Module">foundation.raising-universe-levels</a>
<a id="10808" class="Keyword">open</a> <a id="10813" class="Keyword">import</a> <a id="10820" href="foundation.ranks-of-elements-w-types.html" class="Module">foundation.ranks-of-elements-w-types</a>
<a id="10857" class="Keyword">open</a> <a id="10862" class="Keyword">import</a> <a id="10869" href="foundation.reflecting-maps-equivalence-relations.html" class="Module">foundation.reflecting-maps-equivalence-relations</a>
<a id="10918" class="Keyword">open</a> <a id="10923" class="Keyword">import</a> <a id="10930" href="foundation.replacement.html" class="Module">foundation.replacement</a>
<a id="10953" class="Keyword">open</a> <a id="10958" class="Keyword">import</a> <a id="10965" href="foundation.retractions.html" class="Module">foundation.retractions</a>
<a id="10988" class="Keyword">open</a> <a id="10993" class="Keyword">import</a> <a id="11000" href="foundation.russells-paradox.html" class="Module">foundation.russells-paradox</a>
<a id="11028" class="Keyword">open</a> <a id="11033" class="Keyword">import</a> <a id="11040" href="foundation.sections.html" class="Module">foundation.sections</a>
<a id="11060" class="Keyword">open</a> <a id="11065" class="Keyword">import</a> <a id="11072" href="foundation.set-presented-types.html" class="Module">foundation.set-presented-types</a>
<a id="11103" class="Keyword">open</a> <a id="11108" class="Keyword">import</a> <a id="11115" href="foundation.set-truncations.html" class="Module">foundation.set-truncations</a>
<a id="11142" class="Keyword">open</a> <a id="11147" class="Keyword">import</a> <a id="11154" href="foundation.sets.html" class="Module">foundation.sets</a>
<a id="11170" class="Keyword">open</a> <a id="11175" class="Keyword">import</a> <a id="11182" href="foundation.singleton-induction.html" class="Module">foundation.singleton-induction</a>
<a id="11213" class="Keyword">open</a> <a id="11218" class="Keyword">import</a> <a id="11225" href="foundation.slice.html" class="Module">foundation.slice</a>
<a id="11242" class="Keyword">open</a> <a id="11247" class="Keyword">import</a> <a id="11254" href="foundation.small-maps.html" class="Module">foundation.small-maps</a>
<a id="11276" class="Keyword">open</a> <a id="11281" class="Keyword">import</a> <a id="11288" href="foundation.small-multisets.html" class="Module">foundation.small-multisets</a>
<a id="11315" class="Keyword">open</a> <a id="11320" class="Keyword">import</a> <a id="11327" href="foundation.small-types.html" class="Module">foundation.small-types</a>
<a id="11350" class="Keyword">open</a> <a id="11355" class="Keyword">import</a> <a id="11362" href="foundation.small-universes.html" class="Module">foundation.small-universes</a>
<a id="11389" class="Keyword">open</a> <a id="11394" class="Keyword">import</a> <a id="11401" href="foundation.split-surjective-maps.html" class="Module">foundation.split-surjective-maps</a>
<a id="11434" class="Keyword">open</a> <a id="11439" class="Keyword">import</a> <a id="11446" href="foundation.structure-identity-principle.html" class="Module">foundation.structure-identity-principle</a>
<a id="11486" class="Keyword">open</a> <a id="11491" class="Keyword">import</a> <a id="11498" href="foundation.structure.html" class="Module">foundation.structure</a>
<a id="11519" class="Keyword">open</a> <a id="11524" class="Keyword">import</a> <a id="11531" href="foundation.subterminal-types.html" class="Module">foundation.subterminal-types</a>
<a id="11560" class="Keyword">open</a> <a id="11565" class="Keyword">import</a> <a id="11572" href="foundation.subtype-identity-principle.html" class="Module">foundation.subtype-identity-principle</a>
<a id="11610" class="Keyword">open</a> <a id="11615" class="Keyword">import</a> <a id="11622" href="foundation.subtypes.html" class="Module">foundation.subtypes</a>
<a id="11642" class="Keyword">open</a> <a id="11647" class="Keyword">import</a> <a id="11654" href="foundation.subuniverses.html" class="Module">foundation.subuniverses</a>
<a id="11678" class="Keyword">open</a> <a id="11683" class="Keyword">import</a> <a id="11690" href="foundation.surjective-maps.html" class="Module">foundation.surjective-maps</a>
<a id="11717" class="Keyword">open</a> <a id="11722" class="Keyword">import</a> <a id="11729" href="foundation.truncated-maps.html" class="Module">foundation.truncated-maps</a>
<a id="11755" class="Keyword">open</a> <a id="11760" class="Keyword">import</a> <a id="11767" href="foundation.truncated-types.html" class="Module">foundation.truncated-types</a>
<a id="11794" class="Keyword">open</a> <a id="11799" class="Keyword">import</a> <a id="11806" href="foundation.truncation-levels.html" class="Module">foundation.truncation-levels</a>
<a id="11835" class="Keyword">open</a> <a id="11840" class="Keyword">import</a> <a id="11847" href="foundation.truncations.html" class="Module">foundation.truncations</a>
<a id="11870" class="Keyword">open</a> <a id="11875" class="Keyword">import</a> <a id="11882" href="foundation.type-arithmetic-cartesian-product-types.html" class="Module">foundation.type-arithmetic-cartesian-product-types</a>
<a id="11933" class="Keyword">open</a> <a id="11938" class="Keyword">import</a> <a id="11945" href="foundation.type-arithmetic-coproduct-types.html" class="Module">foundation.type-arithmetic-coproduct-types</a>
<a id="11988" class="Keyword">open</a> <a id="11993" class="Keyword">import</a> <a id="12000" href="foundation.type-arithmetic-dependent-pair-types.html" class="Module">foundation.type-arithmetic-dependent-pair-types</a>
<a id="12048" class="Keyword">open</a> <a id="12053" class="Keyword">import</a> <a id="12060" href="foundation.type-arithmetic-empty-type.html" class="Module">foundation.type-arithmetic-empty-type</a>
<a id="12098" class="Keyword">open</a> <a id="12103" class="Keyword">import</a> <a id="12110" href="foundation.type-arithmetic-unit-type.html" class="Module">foundation.type-arithmetic-unit-type</a>
<a id="12147" class="Keyword">open</a> <a id="12152" class="Keyword">import</a> <a id="12159" href="foundation.uniqueness-image.html" class="Module">foundation.uniqueness-image</a>
<a id="12187" class="Keyword">open</a> <a id="12192" class="Keyword">import</a> <a id="12199" href="foundation.uniqueness-set-quotients.html" class="Module">foundation.uniqueness-set-quotients</a>
<a id="12235" class="Keyword">open</a> <a id="12240" class="Keyword">import</a> <a id="12247" href="foundation.uniqueness-set-truncations.html" class="Module">foundation.uniqueness-set-truncations</a>
<a id="12285" class="Keyword">open</a> <a id="12290" class="Keyword">import</a> <a id="12297" href="foundation.uniqueness-truncation.html" class="Module">foundation.uniqueness-truncation</a>
<a id="12330" class="Keyword">open</a> <a id="12335" class="Keyword">import</a> <a id="12342" href="foundation.unit-type.html" class="Module">foundation.unit-type</a>
<a id="12363" class="Keyword">open</a> <a id="12368" class="Keyword">import</a> <a id="12375" href="foundation.univalence-implies-function-extensionality.html" class="Module">foundation.univalence-implies-function-extensionality</a>
<a id="12429" class="Keyword">open</a> <a id="12434" class="Keyword">import</a> <a id="12441" href="foundation.univalence.html" class="Module">foundation.univalence</a>
<a id="12463" class="Keyword">open</a> <a id="12468" class="Keyword">import</a> <a id="12475" href="foundation.univalent-type-families.html" class="Module">foundation.univalent-type-families</a>
<a id="12510" class="Keyword">open</a> <a id="12515" class="Keyword">import</a> <a id="12522" href="foundation.universal-multiset.html" class="Module">foundation.universal-multiset</a>
<a id="12552" class="Keyword">open</a> <a id="12557" class="Keyword">import</a> <a id="12564" href="foundation.universal-property-booleans.html" class="Module">foundation.universal-property-booleans</a>
<a id="12603" class="Keyword">open</a> <a id="12608" class="Keyword">import</a> <a id="12615" href="foundation.universal-property-cartesian-product-types.html" class="Module">foundation.universal-property-cartesian-product-types</a>
<a id="12669" class="Keyword">open</a> <a id="12674" class="Keyword">import</a> <a id="12681" href="foundation.universal-property-coproduct-types.html" class="Module">foundation.universal-property-coproduct-types</a>
<a id="12727" class="Keyword">open</a> <a id="12732" class="Keyword">import</a> <a id="12739" href="foundation.universal-property-dependent-pair-types.html" class="Module">foundation.universal-property-dependent-pair-types</a>
<a id="12790" class="Keyword">open</a> <a id="12795" class="Keyword">import</a> <a id="12802" href="foundation.universal-property-empty-type.html" class="Module">foundation.universal-property-empty-type</a>
<a id="12843" class="Keyword">open</a> <a id="12848" class="Keyword">import</a> <a id="12855" href="foundation.universal-property-fiber-products.html" class="Module">foundation.universal-property-fiber-products</a>
<a id="12900" class="Keyword">open</a> <a id="12905" class="Keyword">import</a> <a id="12912" href="foundation.universal-property-identity-types.html" class="Module">foundation.universal-property-identity-types</a>
<a id="12957" class="Keyword">open</a> <a id="12962" class="Keyword">import</a> <a id="12969" href="foundation.universal-property-image.html" class="Module">foundation.universal-property-image</a>
<a id="13005" class="Keyword">open</a> <a id="13010" class="Keyword">import</a> <a id="13017" href="foundation.universal-property-maybe.html" class="Module">foundation.universal-property-maybe</a>
<a id="13053" class="Keyword">open</a> <a id="13058" class="Keyword">import</a> <a id="13065" href="foundation.universal-property-propositional-truncation-into-sets.html" class="Module">foundation.universal-property-propositional-truncation-into-sets</a>
<a id="13130" class="Keyword">open</a> <a id="13135" class="Keyword">import</a> <a id="13142" href="foundation.universal-property-propositional-truncation.html" class="Module">foundation.universal-property-propositional-truncation</a>
<a id="13197" class="Keyword">open</a> <a id="13202" class="Keyword">import</a> <a id="13209" href="foundation.universal-property-pullbacks.html" class="Module">foundation.universal-property-pullbacks</a>
<a id="13249" class="Keyword">open</a> <a id="13254" class="Keyword">import</a> <a id="13261" href="foundation.universal-property-set-quotients.html" class="Module">foundation.universal-property-set-quotients</a>
<a id="13305" class="Keyword">open</a> <a id="13310" class="Keyword">import</a> <a id="13317" href="foundation.universal-property-set-truncation.html" class="Module">foundation.universal-property-set-truncation</a>
<a id="13362" class="Keyword">open</a> <a id="13367" class="Keyword">import</a> <a id="13374" href="foundation.universal-property-truncation.html" class="Module">foundation.universal-property-truncation</a>
<a id="13415" class="Keyword">open</a> <a id="13420" class="Keyword">import</a> <a id="13427" href="foundation.universal-property-unit-type.html" class="Module">foundation.universal-property-unit-type</a>
<a id="13467" class="Keyword">open</a> <a id="13472" class="Keyword">import</a> <a id="13479" href="foundation.universe-levels.html" class="Module">foundation.universe-levels</a>
<a id="13506" class="Keyword">open</a> <a id="13511" class="Keyword">import</a> <a id="13518" href="foundation.unordered-pairs.html" class="Module">foundation.unordered-pairs</a>
<a id="13545" class="Keyword">open</a> <a id="13550" class="Keyword">import</a> <a id="13557" href="foundation.w-types.html" class="Module">foundation.w-types</a>
<a id="13576" class="Keyword">open</a> <a id="13581" class="Keyword">import</a> <a id="13588" href="foundation.weak-function-extensionality.html" class="Module">foundation.weak-function-extensionality</a>
<a id="13628" class="Keyword">open</a> <a id="13633" class="Keyword">import</a> <a id="13640" href="foundation.weakly-constant-maps.html" class="Module">foundation.weakly-constant-maps</a>
</pre>
## Foundation Core

<pre class="Agda"><a id="13705" class="Keyword">open</a> <a id="13710" class="Keyword">import</a> <a id="13717" href="foundation-core.0-maps.html" class="Module">foundation-core.0-maps</a>
<a id="13740" class="Keyword">open</a> <a id="13745" class="Keyword">import</a> <a id="13752" href="foundation-core.1-types.html" class="Module">foundation-core.1-types</a>
<a id="13776" class="Keyword">open</a> <a id="13781" class="Keyword">import</a> <a id="13788" href="foundation-core.cartesian-product-types.html" class="Module">foundation-core.cartesian-product-types</a>
<a id="13828" class="Keyword">open</a> <a id="13833" class="Keyword">import</a> <a id="13840" href="foundation-core.coherently-invertible-maps.html" class="Module">foundation-core.coherently-invertible-maps</a>
<a id="13883" class="Keyword">open</a> <a id="13888" class="Keyword">import</a> <a id="13895" href="foundation-core.commuting-squares.html" class="Module">foundation-core.commuting-squares</a>
<a id="13929" class="Keyword">open</a> <a id="13934" class="Keyword">import</a> <a id="13941" href="foundation-core.constant-maps.html" class="Module">foundation-core.constant-maps</a>
<a id="13971" class="Keyword">open</a> <a id="13976" class="Keyword">import</a> <a id="13983" href="foundation-core.contractible-maps.html" class="Module">foundation-core.contractible-maps</a>
<a id="14017" class="Keyword">open</a> <a id="14022" class="Keyword">import</a> <a id="14029" href="foundation-core.contractible-types.html" class="Module">foundation-core.contractible-types</a>
<a id="14064" class="Keyword">open</a> <a id="14069" class="Keyword">import</a> <a id="14076" href="foundation-core.dependent-pair-types.html" class="Module">foundation-core.dependent-pair-types</a>
<a id="14113" class="Keyword">open</a> <a id="14118" class="Keyword">import</a> <a id="14125" href="foundation-core.embeddings.html" class="Module">foundation-core.embeddings</a>
<a id="14152" class="Keyword">open</a> <a id="14157" class="Keyword">import</a> <a id="14164" href="foundation-core.empty-types.html" class="Module">foundation-core.empty-types</a>
<a id="14192" class="Keyword">open</a> <a id="14197" class="Keyword">import</a> <a id="14204" href="foundation-core.equality-cartesian-product-types.html" class="Module">foundation-core.equality-cartesian-product-types</a>
<a id="14253" class="Keyword">open</a> <a id="14258" class="Keyword">import</a> <a id="14265" href="foundation-core.equality-dependent-pair-types.html" class="Module">foundation-core.equality-dependent-pair-types</a>
<a id="14311" class="Keyword">open</a> <a id="14316" class="Keyword">import</a> <a id="14323" href="foundation-core.equality-fibers-of-maps.html" class="Module">foundation-core.equality-fibers-of-maps</a>
<a id="14363" class="Keyword">open</a> <a id="14368" class="Keyword">import</a> <a id="14375" href="foundation-core.equivalence-induction.html" class="Module">foundation-core.equivalence-induction</a>
<a id="14413" class="Keyword">open</a> <a id="14418" class="Keyword">import</a> <a id="14425" href="foundation-core.equivalences.html" class="Module">foundation-core.equivalences</a>
<a id="14454" class="Keyword">open</a> <a id="14459" class="Keyword">import</a> <a id="14466" href="foundation-core.faithful-maps.html" class="Module">foundation-core.faithful-maps</a>
<a id="14496" class="Keyword">open</a> <a id="14501" class="Keyword">import</a> <a id="14508" href="foundation-core.fibers-of-maps.html" class="Module">foundation-core.fibers-of-maps</a>
<a id="14539" class="Keyword">open</a> <a id="14544" class="Keyword">import</a> <a id="14551" href="foundation-core.functions.html" class="Module">foundation-core.functions</a>
<a id="14577" class="Keyword">open</a> <a id="14582" class="Keyword">import</a> <a id="14589" href="foundation-core.functoriality-dependent-pair-types.html" class="Module">foundation-core.functoriality-dependent-pair-types</a>
<a id="14640" class="Keyword">open</a> <a id="14645" class="Keyword">import</a> <a id="14652" href="foundation-core.fundamental-theorem-of-identity-types.html" class="Module">foundation-core.fundamental-theorem-of-identity-types</a>
<a id="14706" class="Keyword">open</a> <a id="14711" class="Keyword">import</a> <a id="14718" href="foundation-core.homotopies.html" class="Module">foundation-core.homotopies</a>
<a id="14745" class="Keyword">open</a> <a id="14750" class="Keyword">import</a> <a id="14757" href="foundation-core.identity-systems.html" class="Module">foundation-core.identity-systems</a>
<a id="14790" class="Keyword">open</a> <a id="14795" class="Keyword">import</a> <a id="14802" href="foundation-core.identity-types.html" class="Module">foundation-core.identity-types</a>
<a id="14833" class="Keyword">open</a> <a id="14838" class="Keyword">import</a> <a id="14845" href="foundation-core.logical-equivalences.html" class="Module">foundation-core.logical-equivalences</a>
<a id="14882" class="Keyword">open</a> <a id="14887" class="Keyword">import</a> <a id="14894" href="foundation-core.negation.html" class="Module">foundation-core.negation</a>
<a id="14919" class="Keyword">open</a> <a id="14924" class="Keyword">import</a> <a id="14931" href="foundation-core.path-split-maps.html" class="Module">foundation-core.path-split-maps</a>
<a id="14963" class="Keyword">open</a> <a id="14968" class="Keyword">import</a> <a id="14975" href="foundation-core.propositional-maps.html" class="Module">foundation-core.propositional-maps</a>
<a id="15010" class="Keyword">open</a> <a id="15015" class="Keyword">import</a> <a id="15022" href="foundation-core.propositions.html" class="Module">foundation-core.propositions</a>
<a id="15051" class="Keyword">open</a> <a id="15056" class="Keyword">import</a> <a id="15063" href="foundation-core.retractions.html" class="Module">foundation-core.retractions</a>
<a id="15091" class="Keyword">open</a> <a id="15096" class="Keyword">import</a> <a id="15103" href="foundation-core.sections.html" class="Module">foundation-core.sections</a>
<a id="15128" class="Keyword">open</a> <a id="15133" class="Keyword">import</a> <a id="15140" href="foundation-core.sets.html" class="Module">foundation-core.sets</a>
<a id="15161" class="Keyword">open</a> <a id="15166" class="Keyword">import</a> <a id="15173" href="foundation-core.singleton-induction.html" class="Module">foundation-core.singleton-induction</a>
<a id="15209" class="Keyword">open</a> <a id="15214" class="Keyword">import</a> <a id="15221" href="foundation-core.subtype-identity-principle.html" class="Module">foundation-core.subtype-identity-principle</a>
<a id="15264" class="Keyword">open</a> <a id="15269" class="Keyword">import</a> <a id="15276" href="foundation-core.subtypes.html" class="Module">foundation-core.subtypes</a>
<a id="15301" class="Keyword">open</a> <a id="15306" class="Keyword">import</a> <a id="15313" href="foundation-core.truncated-maps.html" class="Module">foundation-core.truncated-maps</a>
<a id="15344" class="Keyword">open</a> <a id="15349" class="Keyword">import</a> <a id="15356" href="foundation-core.truncated-types.html" class="Module">foundation-core.truncated-types</a>
<a id="15388" class="Keyword">open</a> <a id="15393" class="Keyword">import</a> <a id="15400" href="foundation-core.truncation-levels.html" class="Module">foundation-core.truncation-levels</a>
<a id="15434" class="Keyword">open</a> <a id="15439" class="Keyword">import</a> <a id="15446" href="foundation-core.type-arithmetic-cartesian-product-types.html" class="Module">foundation-core.type-arithmetic-cartesian-product-types</a>
<a id="15502" class="Keyword">open</a> <a id="15507" class="Keyword">import</a> <a id="15514" href="foundation-core.type-arithmetic-dependent-pair-types.html" class="Module">foundation-core.type-arithmetic-dependent-pair-types</a>
<a id="15567" class="Keyword">open</a> <a id="15572" class="Keyword">import</a> <a id="15579" href="foundation-core.univalence.html" class="Module">foundation-core.univalence</a>
<a id="15606" class="Keyword">open</a> <a id="15611" class="Keyword">import</a> <a id="15618" href="foundation-core.universe-levels.html" class="Module">foundation-core.universe-levels</a>
</pre>
## Graph theory

<pre class="Agda"><a id="15680" class="Keyword">open</a> <a id="15685" class="Keyword">import</a> <a id="15692" href="graph-theory.directed-graphs.html" class="Module">graph-theory.directed-graphs</a>
<a id="15721" class="Keyword">open</a> <a id="15726" class="Keyword">import</a> <a id="15733" href="graph-theory.finite-graphs.html" class="Module">graph-theory.finite-graphs</a>
<a id="15760" class="Keyword">open</a> <a id="15765" class="Keyword">import</a> <a id="15772" href="graph-theory.polygons.html" class="Module">graph-theory.polygons</a>
<a id="15794" class="Keyword">open</a> <a id="15799" class="Keyword">import</a> <a id="15806" href="graph-theory.reflexive-graphs.html" class="Module">graph-theory.reflexive-graphs</a>
<a id="15836" class="Keyword">open</a> <a id="15841" class="Keyword">import</a> <a id="15848" href="graph-theory.undirected-graphs.html" class="Module">graph-theory.undirected-graphs</a>
</pre>
## Group theory

<pre class="Agda"><a id="15909" class="Keyword">open</a> <a id="15914" class="Keyword">import</a> <a id="15921" href="group-theory.html" class="Module">group-theory</a>
<a id="15934" class="Keyword">open</a> <a id="15939" class="Keyword">import</a> <a id="15946" href="group-theory.abstract-abelian-groups.html" class="Module">group-theory.abstract-abelian-groups</a>
<a id="15983" class="Keyword">open</a> <a id="15988" class="Keyword">import</a> <a id="15995" href="group-theory.abstract-abelian-subgroups.html" class="Module">group-theory.abstract-abelian-subgroups</a>
<a id="16035" class="Keyword">open</a> <a id="16040" class="Keyword">import</a> <a id="16047" href="group-theory.abstract-group-actions.html" class="Module">group-theory.abstract-group-actions</a>
<a id="16083" class="Keyword">open</a> <a id="16088" class="Keyword">import</a> <a id="16095" href="group-theory.abstract-group-torsors.html" class="Module">group-theory.abstract-group-torsors</a>
<a id="16131" class="Keyword">open</a> <a id="16136" class="Keyword">import</a> <a id="16143" href="group-theory.abstract-groups.html" class="Module">group-theory.abstract-groups</a>
<a id="16172" class="Keyword">open</a> <a id="16177" class="Keyword">import</a> <a id="16184" href="group-theory.abstract-subgroups.html" class="Module">group-theory.abstract-subgroups</a>
<a id="16216" class="Keyword">open</a> <a id="16221" class="Keyword">import</a> <a id="16228" href="group-theory.concrete-group-actions.html" class="Module">group-theory.concrete-group-actions</a>
<a id="16264" class="Keyword">open</a> <a id="16269" class="Keyword">import</a> <a id="16276" href="group-theory.concrete-groups.html" class="Module">group-theory.concrete-groups</a>
<a id="16305" class="Keyword">open</a> <a id="16310" class="Keyword">import</a> <a id="16317" href="group-theory.concrete-subgroups.html" class="Module">group-theory.concrete-subgroups</a>
<a id="16349" class="Keyword">open</a> <a id="16354" class="Keyword">import</a> <a id="16361" href="group-theory.examples-higher-groups.html" class="Module">group-theory.examples-higher-groups</a>
<a id="16397" class="Keyword">open</a> <a id="16402" class="Keyword">import</a> <a id="16409" href="group-theory.furstenberg-groups.html" class="Module">group-theory.furstenberg-groups</a>
<a id="16441" class="Keyword">open</a> <a id="16446" class="Keyword">import</a> <a id="16453" href="group-theory.higher-groups.html" class="Module">group-theory.higher-groups</a>
<a id="16480" class="Keyword">open</a> <a id="16485" class="Keyword">import</a> <a id="16492" href="group-theory.sheargroups.html" class="Module">group-theory.sheargroups</a>
</pre>
## Linear algebra

<pre class="Agda"><a id="16549" class="Keyword">open</a> <a id="16554" class="Keyword">import</a> <a id="16561" href="linear-algebra.matrices.html" class="Module">linear-algebra.matrices</a>
<a id="16585" class="Keyword">open</a> <a id="16590" class="Keyword">import</a> <a id="16597" href="linear-algebra.vectors.html" class="Module">linear-algebra.vectors</a>
</pre>
## Order theory

<pre class="Agda"><a id="16650" class="Keyword">open</a> <a id="16655" class="Keyword">import</a> <a id="16662" href="order-theory.html" class="Module">order-theory</a>
<a id="16675" class="Keyword">open</a> <a id="16680" class="Keyword">import</a> <a id="16687" href="order-theory.finite-posets.html" class="Module">order-theory.finite-posets</a>
<a id="16714" class="Keyword">open</a> <a id="16719" class="Keyword">import</a> <a id="16726" href="order-theory.finite-preorders.html" class="Module">order-theory.finite-preorders</a>
<a id="16756" class="Keyword">open</a> <a id="16761" class="Keyword">import</a> <a id="16768" href="order-theory.finitely-graded-posets.html" class="Module">order-theory.finitely-graded-posets</a>
<a id="16804" class="Keyword">open</a> <a id="16809" class="Keyword">import</a> <a id="16816" href="order-theory.planar-binary-trees.html" class="Module">order-theory.planar-binary-trees</a>
<a id="16849" class="Keyword">open</a> <a id="16854" class="Keyword">import</a> <a id="16861" href="order-theory.posets.html" class="Module">order-theory.posets</a>
<a id="16881" class="Keyword">open</a> <a id="16886" class="Keyword">import</a> <a id="16893" href="order-theory.preorders.html" class="Module">order-theory.preorders</a>
</pre>
## Polytopes

<pre class="Agda"><a id="16943" class="Keyword">open</a> <a id="16948" class="Keyword">import</a> <a id="16955" href="polytopes.abstract-polytopes.html" class="Module">polytopes.abstract-polytopes</a>
</pre>
## Ring theory

<pre class="Agda"><a id="17013" class="Keyword">open</a> <a id="17018" class="Keyword">import</a> <a id="17025" href="ring-theory.html" class="Module">ring-theory</a>
<a id="17037" class="Keyword">open</a> <a id="17042" class="Keyword">import</a> <a id="17049" href="ring-theory.eisenstein-integers.html" class="Module">ring-theory.eisenstein-integers</a>
<a id="17081" class="Keyword">open</a> <a id="17086" class="Keyword">import</a> <a id="17093" href="ring-theory.gaussian-integers.html" class="Module">ring-theory.gaussian-integers</a>
<a id="17123" class="Keyword">open</a> <a id="17128" class="Keyword">import</a> <a id="17135" href="ring-theory.ideals.html" class="Module">ring-theory.ideals</a>
<a id="17154" class="Keyword">open</a> <a id="17159" class="Keyword">import</a> <a id="17166" href="ring-theory.localizations-rings.html" class="Module">ring-theory.localizations-rings</a>
<a id="17198" class="Keyword">open</a> <a id="17203" class="Keyword">import</a> <a id="17210" href="ring-theory.rings-with-properties.html" class="Module">ring-theory.rings-with-properties</a>
<a id="17244" class="Keyword">open</a> <a id="17249" class="Keyword">import</a> <a id="17256" href="ring-theory.rings.html" class="Module">ring-theory.rings</a>
</pre>
## Synthetic homotopy theory

<pre class="Agda"><a id="17317" class="Keyword">open</a> <a id="17322" class="Keyword">import</a> <a id="17329" href="synthetic-homotopy-theory.html" class="Module">synthetic-homotopy-theory</a>
<a id="17355" class="Keyword">open</a> <a id="17360" class="Keyword">import</a> <a id="17367" href="synthetic-homotopy-theory.23-pullbacks.html" class="Module">synthetic-homotopy-theory.23-pullbacks</a>
<a id="17406" class="Keyword">open</a> <a id="17411" class="Keyword">import</a> <a id="17418" href="synthetic-homotopy-theory.24-pushouts.html" class="Module">synthetic-homotopy-theory.24-pushouts</a>
<a id="17456" class="Keyword">open</a> <a id="17461" class="Keyword">import</a> <a id="17468" href="synthetic-homotopy-theory.25-cubical-diagrams.html" class="Module">synthetic-homotopy-theory.25-cubical-diagrams</a>
<a id="17514" class="Keyword">open</a> <a id="17519" class="Keyword">import</a> <a id="17526" href="synthetic-homotopy-theory.26-descent.html" class="Module">synthetic-homotopy-theory.26-descent</a>
<a id="17563" class="Keyword">open</a> <a id="17568" class="Keyword">import</a> <a id="17575" href="synthetic-homotopy-theory.26-id-pushout.html" class="Module">synthetic-homotopy-theory.26-id-pushout</a>
<a id="17615" class="Keyword">open</a> <a id="17620" class="Keyword">import</a> <a id="17627" href="synthetic-homotopy-theory.27-sequences.html" class="Module">synthetic-homotopy-theory.27-sequences</a>
<a id="17666" class="Keyword">open</a> <a id="17671" class="Keyword">import</a> <a id="17678" href="synthetic-homotopy-theory.circle.html" class="Module">synthetic-homotopy-theory.circle</a>
<a id="17711" class="Keyword">open</a> <a id="17716" class="Keyword">import</a> <a id="17723" href="synthetic-homotopy-theory.cyclic-types.html" class="Module">synthetic-homotopy-theory.cyclic-types</a>
<a id="17762" class="Keyword">open</a> <a id="17767" class="Keyword">import</a> <a id="17774" href="synthetic-homotopy-theory.double-loop-spaces.html" class="Module">synthetic-homotopy-theory.double-loop-spaces</a>
<a id="17819" class="Keyword">open</a> <a id="17824" class="Keyword">import</a> <a id="17831" href="synthetic-homotopy-theory.functoriality-loop-spaces.html" class="Module">synthetic-homotopy-theory.functoriality-loop-spaces</a>
<a id="17883" class="Keyword">open</a> <a id="17888" class="Keyword">import</a> <a id="17895" href="synthetic-homotopy-theory.infinite-cyclic-types.html" class="Module">synthetic-homotopy-theory.infinite-cyclic-types</a>
<a id="17943" class="Keyword">open</a> <a id="17948" class="Keyword">import</a> <a id="17955" href="synthetic-homotopy-theory.interval-type.html" class="Module">synthetic-homotopy-theory.interval-type</a>
<a id="17995" class="Keyword">open</a> <a id="18000" class="Keyword">import</a> <a id="18007" href="synthetic-homotopy-theory.iterated-loop-spaces.html" class="Module">synthetic-homotopy-theory.iterated-loop-spaces</a>
<a id="18054" class="Keyword">open</a> <a id="18059" class="Keyword">import</a> <a id="18066" href="synthetic-homotopy-theory.loop-spaces.html" class="Module">synthetic-homotopy-theory.loop-spaces</a>
<a id="18104" class="Keyword">open</a> <a id="18109" class="Keyword">import</a> <a id="18116" href="synthetic-homotopy-theory.pointed-dependent-functions.html" class="Module">synthetic-homotopy-theory.pointed-dependent-functions</a>
<a id="18170" class="Keyword">open</a> <a id="18175" class="Keyword">import</a> <a id="18182" href="synthetic-homotopy-theory.pointed-equivalences.html" class="Module">synthetic-homotopy-theory.pointed-equivalences</a>
<a id="18229" class="Keyword">open</a> <a id="18234" class="Keyword">import</a> <a id="18241" href="synthetic-homotopy-theory.pointed-families-of-types.html" class="Module">synthetic-homotopy-theory.pointed-families-of-types</a>
<a id="18293" class="Keyword">open</a> <a id="18298" class="Keyword">import</a> <a id="18305" href="synthetic-homotopy-theory.pointed-homotopies.html" class="Module">synthetic-homotopy-theory.pointed-homotopies</a>
<a id="18350" class="Keyword">open</a> <a id="18355" class="Keyword">import</a> <a id="18362" href="synthetic-homotopy-theory.pointed-maps.html" class="Module">synthetic-homotopy-theory.pointed-maps</a>
<a id="18401" class="Keyword">open</a> <a id="18406" class="Keyword">import</a> <a id="18413" href="synthetic-homotopy-theory.pointed-types.html" class="Module">synthetic-homotopy-theory.pointed-types</a>
<a id="18453" class="Keyword">open</a> <a id="18458" class="Keyword">import</a> <a id="18465" href="synthetic-homotopy-theory.spaces.html" class="Module">synthetic-homotopy-theory.spaces</a>
<a id="18498" class="Keyword">open</a> <a id="18503" class="Keyword">import</a> <a id="18510" href="synthetic-homotopy-theory.triple-loop-spaces.html" class="Module">synthetic-homotopy-theory.triple-loop-spaces</a>
<a id="18555" class="Keyword">open</a> <a id="18560" class="Keyword">import</a> <a id="18567" href="synthetic-homotopy-theory.universal-cover-circle.html" class="Module">synthetic-homotopy-theory.universal-cover-circle</a>
</pre>
## Tutorials

<pre class="Agda"><a id="18643" class="Keyword">open</a> <a id="18648" class="Keyword">import</a> <a id="18655" href="tutorials.basic-agda.html" class="Module">tutorials.basic-agda</a>
</pre>
## Univalent combinatorics

<pre class="Agda"><a id="18717" class="Keyword">open</a> <a id="18722" class="Keyword">import</a> <a id="18729" href="univalent-combinatorics.html" class="Module">univalent-combinatorics</a>
<a id="18753" class="Keyword">open</a> <a id="18758" class="Keyword">import</a> <a id="18765" href="univalent-combinatorics.2-element-types.html" class="Module">univalent-combinatorics.2-element-types</a>
<a id="18805" class="Keyword">open</a> <a id="18810" class="Keyword">import</a> <a id="18817" href="univalent-combinatorics.binomial-types.html" class="Module">univalent-combinatorics.binomial-types</a>
<a id="18856" class="Keyword">open</a> <a id="18861" class="Keyword">import</a> <a id="18868" href="univalent-combinatorics.cartesian-product-finite-types.html" class="Module">univalent-combinatorics.cartesian-product-finite-types</a>
<a id="18923" class="Keyword">open</a> <a id="18928" class="Keyword">import</a> <a id="18935" href="univalent-combinatorics.coproduct-finite-types.html" class="Module">univalent-combinatorics.coproduct-finite-types</a>
<a id="18982" class="Keyword">open</a> <a id="18987" class="Keyword">import</a> <a id="18994" href="univalent-combinatorics.counting-cartesian-product-types.html" class="Module">univalent-combinatorics.counting-cartesian-product-types</a>
<a id="19051" class="Keyword">open</a> <a id="19056" class="Keyword">import</a> <a id="19063" href="univalent-combinatorics.counting-coproduct-types.html" class="Module">univalent-combinatorics.counting-coproduct-types</a>
<a id="19112" class="Keyword">open</a> <a id="19117" class="Keyword">import</a> <a id="19124" href="univalent-combinatorics.counting-decidable-subtypes.html" class="Module">univalent-combinatorics.counting-decidable-subtypes</a>
<a id="19176" class="Keyword">open</a> <a id="19181" class="Keyword">import</a> <a id="19188" href="univalent-combinatorics.counting-dependent-function-types.html" class="Module">univalent-combinatorics.counting-dependent-function-types</a>
<a id="19246" class="Keyword">open</a> <a id="19251" class="Keyword">import</a> <a id="19258" href="univalent-combinatorics.counting-dependent-pair-types.html" class="Module">univalent-combinatorics.counting-dependent-pair-types</a>
<a id="19312" class="Keyword">open</a> <a id="19317" class="Keyword">import</a> <a id="19324" href="univalent-combinatorics.counting-fibers-of-maps.html" class="Module">univalent-combinatorics.counting-fibers-of-maps</a>
<a id="19372" class="Keyword">open</a> <a id="19377" class="Keyword">import</a> <a id="19384" href="univalent-combinatorics.counting-function-types.html" class="Module">univalent-combinatorics.counting-function-types</a>
<a id="19432" class="Keyword">open</a> <a id="19437" class="Keyword">import</a> <a id="19444" href="univalent-combinatorics.counting-maybe.html" class="Module">univalent-combinatorics.counting-maybe</a>
<a id="19483" class="Keyword">open</a> <a id="19488" class="Keyword">import</a> <a id="19495" href="univalent-combinatorics.counting.html" class="Module">univalent-combinatorics.counting</a>
<a id="19528" class="Keyword">open</a> <a id="19533" class="Keyword">import</a> <a id="19540" href="univalent-combinatorics.decidable-dependent-function-types.html" class="Module">univalent-combinatorics.decidable-dependent-function-types</a>
<a id="19599" class="Keyword">open</a> <a id="19604" class="Keyword">import</a> <a id="19611" href="univalent-combinatorics.decidable-dependent-pair-types.html" class="Module">univalent-combinatorics.decidable-dependent-pair-types</a>
<a id="19666" class="Keyword">open</a> <a id="19671" class="Keyword">import</a> <a id="19678" href="univalent-combinatorics.decidable-subtypes.html" class="Module">univalent-combinatorics.decidable-subtypes</a>
<a id="19721" class="Keyword">open</a> <a id="19726" class="Keyword">import</a> <a id="19733" href="univalent-combinatorics.dependent-product-finite-types.html" class="Module">univalent-combinatorics.dependent-product-finite-types</a>
<a id="19788" class="Keyword">open</a> <a id="19793" class="Keyword">import</a> <a id="19800" href="univalent-combinatorics.dependent-sum-finite-types.html" class="Module">univalent-combinatorics.dependent-sum-finite-types</a>
<a id="19851" class="Keyword">open</a> <a id="19856" class="Keyword">import</a> <a id="19863" href="univalent-combinatorics.distributivity-of-set-truncation-over-finite-products.html" class="Module">univalent-combinatorics.distributivity-of-set-truncation-over-finite-products</a>
<a id="19941" class="Keyword">open</a> <a id="19946" class="Keyword">import</a> <a id="19953" href="univalent-combinatorics.double-counting.html" class="Module">univalent-combinatorics.double-counting</a>
<a id="19993" class="Keyword">open</a> <a id="19998" class="Keyword">import</a> <a id="20005" href="univalent-combinatorics.embeddings-standard-finite-types.html" class="Module">univalent-combinatorics.embeddings-standard-finite-types</a>
<a id="20062" class="Keyword">open</a> <a id="20067" class="Keyword">import</a> <a id="20074" href="univalent-combinatorics.embeddings.html" class="Module">univalent-combinatorics.embeddings</a>
<a id="20109" class="Keyword">open</a> <a id="20114" class="Keyword">import</a> <a id="20121" href="univalent-combinatorics.equality-finite-types.html" class="Module">univalent-combinatorics.equality-finite-types</a>
<a id="20167" class="Keyword">open</a> <a id="20172" class="Keyword">import</a> <a id="20179" href="univalent-combinatorics.equality-standard-finite-types.html" class="Module">univalent-combinatorics.equality-standard-finite-types</a>
<a id="20234" class="Keyword">open</a> <a id="20239" class="Keyword">import</a> <a id="20246" href="univalent-combinatorics.equivalences-standard-finite-types.html" class="Module">univalent-combinatorics.equivalences-standard-finite-types</a>
<a id="20305" class="Keyword">open</a> <a id="20310" class="Keyword">import</a> <a id="20317" href="univalent-combinatorics.equivalences.html" class="Module">univalent-combinatorics.equivalences</a>
<a id="20354" class="Keyword">open</a> <a id="20359" class="Keyword">import</a> <a id="20366" href="univalent-combinatorics.fibers-of-maps-between-finite-types.html" class="Module">univalent-combinatorics.fibers-of-maps-between-finite-types</a>
<a id="20426" class="Keyword">open</a> <a id="20431" class="Keyword">import</a> <a id="20438" href="univalent-combinatorics.finite-choice.html" class="Module">univalent-combinatorics.finite-choice</a>
<a id="20476" class="Keyword">open</a> <a id="20481" class="Keyword">import</a> <a id="20488" href="univalent-combinatorics.finite-connected-components.html" class="Module">univalent-combinatorics.finite-connected-components</a>
<a id="20540" class="Keyword">open</a> <a id="20545" class="Keyword">import</a> <a id="20552" href="univalent-combinatorics.finite-function-types.html" class="Module">univalent-combinatorics.finite-function-types</a>
<a id="20598" class="Keyword">open</a> <a id="20603" class="Keyword">import</a> <a id="20610" href="univalent-combinatorics.finite-presentations.html" class="Module">univalent-combinatorics.finite-presentations</a>
<a id="20655" class="Keyword">open</a> <a id="20660" class="Keyword">import</a> <a id="20667" href="univalent-combinatorics.finite-types.html" class="Module">univalent-combinatorics.finite-types</a>
<a id="20704" class="Keyword">open</a> <a id="20709" class="Keyword">import</a> <a id="20716" href="univalent-combinatorics.finitely-presented-types.html" class="Module">univalent-combinatorics.finitely-presented-types</a>
<a id="20765" class="Keyword">open</a> <a id="20770" class="Keyword">import</a> <a id="20777" href="univalent-combinatorics.image-of-maps.html" class="Module">univalent-combinatorics.image-of-maps</a>
<a id="20815" class="Keyword">open</a> <a id="20820" class="Keyword">import</a> <a id="20827" href="univalent-combinatorics.inequality-types-with-counting.html" class="Module">univalent-combinatorics.inequality-types-with-counting</a>
<a id="20882" class="Keyword">open</a> <a id="20887" class="Keyword">import</a> <a id="20894" href="univalent-combinatorics.injective-maps.html" class="Module">univalent-combinatorics.injective-maps</a>
<a id="20933" class="Keyword">open</a> <a id="20938" class="Keyword">import</a> <a id="20945" href="univalent-combinatorics.lists.html" class="Module">univalent-combinatorics.lists</a>
<a id="20975" class="Keyword">open</a> <a id="20980" class="Keyword">import</a> <a id="20987" href="univalent-combinatorics.maybe.html" class="Module">univalent-combinatorics.maybe</a>
<a id="21017" class="Keyword">open</a> <a id="21022" class="Keyword">import</a> <a id="21029" href="univalent-combinatorics.pi-finite-types.html" class="Module">univalent-combinatorics.pi-finite-types</a>
<a id="21069" class="Keyword">open</a> <a id="21074" class="Keyword">import</a> <a id="21081" href="univalent-combinatorics.pigeonhole-principle.html" class="Module">univalent-combinatorics.pigeonhole-principle</a>
<a id="21126" class="Keyword">open</a> <a id="21131" class="Keyword">import</a> <a id="21138" href="univalent-combinatorics.presented-pi-finite-types.html" class="Module">univalent-combinatorics.presented-pi-finite-types</a>
<a id="21188" class="Keyword">open</a> <a id="21193" class="Keyword">import</a> <a id="21200" href="univalent-combinatorics.ramsey-theory.html" class="Module">univalent-combinatorics.ramsey-theory</a>
<a id="21238" class="Keyword">open</a> <a id="21243" class="Keyword">import</a> <a id="21250" href="univalent-combinatorics.retracts-of-finite-types.html" class="Module">univalent-combinatorics.retracts-of-finite-types</a>
<a id="21299" class="Keyword">open</a> <a id="21304" class="Keyword">import</a> <a id="21311" href="univalent-combinatorics.standard-finite-pruned-trees.html" class="Module">univalent-combinatorics.standard-finite-pruned-trees</a>
<a id="21364" class="Keyword">open</a> <a id="21369" class="Keyword">import</a> <a id="21376" href="univalent-combinatorics.standard-finite-trees.html" class="Module">univalent-combinatorics.standard-finite-trees</a>
<a id="21422" class="Keyword">open</a> <a id="21427" class="Keyword">import</a> <a id="21434" href="univalent-combinatorics.standard-finite-types.html" class="Module">univalent-combinatorics.standard-finite-types</a>
<a id="21480" class="Keyword">open</a> <a id="21485" class="Keyword">import</a> <a id="21492" href="univalent-combinatorics.sums-of-natural-numbers.html" class="Module">univalent-combinatorics.sums-of-natural-numbers</a>
<a id="21540" class="Keyword">open</a> <a id="21545" class="Keyword">import</a> <a id="21552" href="univalent-combinatorics.surjective-maps.html" class="Module">univalent-combinatorics.surjective-maps</a>
</pre>
## Univalent foundation

<pre class="Agda"><a id="21630" class="Keyword">open</a> <a id="21635" class="Keyword">import</a> <a id="21642" href="univalent-foundations.isolated-points.html" class="Module">univalent-foundations.isolated-points</a>
</pre>
## Wild algebra

<pre class="Agda"><a id="21710" class="Keyword">open</a> <a id="21715" class="Keyword">import</a> <a id="21722" href="wild-algebra.magmas.html" class="Module">wild-algebra.magmas</a>
<a id="21742" class="Keyword">open</a> <a id="21747" class="Keyword">import</a> <a id="21754" href="wild-algebra.universal-property-lists-wild-monoids.html" class="Module">wild-algebra.universal-property-lists-wild-monoids</a>
<a id="21805" class="Keyword">open</a> <a id="21810" class="Keyword">import</a> <a id="21817" href="wild-algebra.wild-groups.html" class="Module">wild-algebra.wild-groups</a>
<a id="21842" class="Keyword">open</a> <a id="21847" class="Keyword">import</a> <a id="21854" href="wild-algebra.wild-monoids.html" class="Module">wild-algebra.wild-monoids</a>
<a id="21880" class="Keyword">open</a> <a id="21885" class="Keyword">import</a> <a id="21892" href="wild-algebra.wild-unital-magmas.html" class="Module">wild-algebra.wild-unital-magmas</a>
</pre>
## Everything

See the list of all Agda modules [here](everything.html).

