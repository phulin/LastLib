# Depth, Complete Intersections, and Fitting Ideals

## Contents

1. [From equations to modules](#1-from-equations-to-modules)
   - [The next layer of local algebra](#11-the-next-layer-of-local-algebra)
   - [Standing conventions](#12-standing-conventions)
   - [Three kinds of numerical information](#13-three-kinds-of-numerical-information)
2. [Nonzerodivisors and regular sequences](#2-nonzerodivisors-and-regular-sequences)
   - [Why one equation at a time matters](#21-why-one-equation-at-a-time-matters)
   - [Regular elements on modules](#22-regular-elements-on-modules)
   - [Regular sequences and properness](#23-regular-sequences-and-properness)
   - [Order, locality, and finiteness](#24-order-locality-and-finiteness)
   - [Maximal sequences and associated primes](#25-maximal-sequences-and-associated-primes)
   - [Worked examples and warnings](#26-worked-examples-and-warnings)
3. [The Koszul mechanism](#3-the-koszul-mechanism)
   - [A complex built from multiplication](#31-a-complex-built-from-multiplication)
   - [One element and the tensor construction](#32-one-element-and-the-tensor-construction)
   - [Regularity detected by homology](#33-regularity-detected-by-homology)
   - [Self-duality and the depth formula](#34-self-duality-and-the-depth-formula)
   - [Koszul resolutions and base change](#35-koszul-resolutions-and-base-change)
4. [Depth: regular sequences and Ext](#4-depth-regular-sequences-and-ext)
   - [What depth measures](#41-what-depth-measures)
   - [Depth in an ideal](#42-depth-in-an-ideal)
   - [The Ext characterization](#43-the-ext-characterization)
   - [The local formula and first computations](#44-the-local-formula-and-first-computations)
   - [The depth lemma](#45-the-depth-lemma)
   - [Sharpness and nonconverses](#46-sharpness-and-nonconverses)
5. [Localization and completion](#5-localization-and-completion)
   - [Why depth must travel](#51-why-depth-must-travel)
   - [Localizing regular sequences](#52-localizing-regular-sequences)
   - [Depth at primes](#53-depth-at-primes)
   - [Flat base change of regular sequences](#54-flat-base-change-of-regular-sequences)
   - [Completion preserves depth](#55-completion-preserves-depth)
6. [Free resolutions over local rings](#6-free-resolutions-over-local-rings)
   - [Relations among relations](#61-relations-among-relations)
   - [Minimal free resolutions](#62-minimal-free-resolutions)
   - [Betti numbers and Tor detection](#63-betti-numbers-and-tor-detection)
   - [Projective dimension and syzygies](#64-projective-dimension-and-syzygies)
   - [Examples of finite and infinite resolutions](#65-examples-of-finite-and-infinite-resolutions)
7. [The Auslander--Buchsbaum formula](#7-the-auslander--buchsbaum-formula)
   - [The expected balance](#71-the-expected-balance)
   - [The homological depth calculation](#72-the-homological-depth-calculation)
   - [Proof of the formula](#73-proof-of-the-formula)
   - [Consequences and missing hypotheses](#74-consequences-and-missing-hypotheses)
8. [Cohen--Macaulay modules and rings](#8-cohen--macaulay-modules-and-rings)
   - [When parameters impose independent conditions](#81-when-parameters-impose-independent-conditions)
   - [Dimension of a module and systems of parameters](#82-dimension-of-a-module-and-systems-of-parameters)
   - [Equivalent Cohen--Macaulay criteria](#83-equivalent-cohen--macaulay-criteria)
   - [Unmixedness and equidimensionality](#84-unmixedness-and-equidimensionality)
   - [Examples and counterexamples](#85-examples-and-counterexamples)
9. [Regular local rings through resolutions](#9-regular-local-rings-through-resolutions)
   - [Regularity revisited](#91-regularity-revisited)
   - [Finite global dimension](#92-finite-global-dimension)
   - [Maximal Cohen--Macaulay modules over regular rings](#93-maximal-cohen--macaulay-modules-over-regular-rings)
10. [Complete-intersection local rings](#10-complete-intersection-local-rings)
    - [Equations of the expected codimension](#101-equations-of-the-expected-codimension)
    - [Definitions and codimension](#102-definitions-and-codimension)
    - [Independence of presentation](#103-independence-of-presentation)
    - [The conormal module](#104-the-conormal-module)
    - [Elementary complete-intersection criteria](#105-elementary-complete-intersection-criteria)
    - [Examples and boundary cases](#106-examples-and-boundary-cases)
11. [Stability of complete intersections](#11-stability-of-complete-intersections)
    - [Completion and quotients](#111-completion-and-quotients)
    - [Flat base change](#112-flat-base-change)
    - [Completed tensor products](#113-completed-tensor-products)
    - [What can fail](#114-what-can-fail)
12. [Fitting ideals from presentations](#12-fitting-ideals-from-presentations)
    - [Why annihilators are not enough](#121-why-annihilators-are-not-enough)
    - [Definition by minors](#122-definition-by-minors)
    - [Independence and the chain of ideals](#123-independence-and-the-chain-of-ideals)
    - [Base change and localization](#124-base-change-and-localization)
    - [Cyclic modules and direct sums](#125-cyclic-modules-and-direct-sums)
13. [Support, annihilators, and faithfulness](#13-support-annihilators-and-faithfulness)
    - [Zeroth Fitting ideals detect support](#131-zeroth-fitting-ideals-detect-support)
    - [Annihilator bounds](#132-annihilator-bounds)
    - [Full support versus faithfulness](#133-full-support-versus-faithfulness)
    - [Scheme-theoretic support](#134-scheme-theoretic-support)
14. [Exact sequences, determinants, and numerical size](#14-exact-sequences-determinants-and-numerical-size)
    - [Fitting ideals in exact sequences](#141-fitting-ideals-in-exact-sequences)
    - [Finite free resolutions and determinants](#142-finite-free-resolutions-and-determinants)
    - [Modules over a discrete valuation ring](#143-modules-over-a-discrete-valuation-ring)
    - [Congruence modules](#144-congruence-modules)
15. [Finite local maps and freeness criteria](#15-finite-local-maps-and-freeness-criteria)
    - [Depth and dimension across a finite map](#151-depth-and-dimension-across-a-finite-map)
    - [Miracle freeness over a regular source](#152-miracle-freeness-over-a-regular-source)
    - [Maximal Cohen--Macaulay does not mean free](#153-maximal-cohen--macaulay-does-not-mean-free)
    - [Finite projective dimension restores freeness](#154-finite-projective-dimension-restores-freeness)
16. [The patching dictionary](#16-the-patching-dictionary)
    - [Reading depth data](#161-reading-depth-data)
    - [Reading complete-intersection data](#162-reading-complete-intersection-data)
    - [Reading Fitting and support data](#163-reading-fitting-and-support-data)
    - [A reliable implication chain](#164-a-reliable-implication-chain)
    - [Conclusion](#165-conclusion)

## 1. From equations to modules

### 1.1 The next layer of local algebra

Book 69 turned tangent and obstruction calculations into presentations of complete local rings. A presentation records variables and equations, but patching arguments ask more. They produce modules over those rings, and the decisive question is often whether the equations cut independently enough that a large module must be free or faithful.

The invariant that measures independence is **depth**. Its elementary definition counts successive nonzerodivisors; its homological definition finds the first nonvanishing Ext group. The bridge between them is the Koszul complex. Once depth is connected to free resolutions, the Auslander--Buchsbaum formula turns a depth equality into projective dimension zero. This is the source of many freeness arguments.

Complete intersections form the corresponding class of rings. They are quotients of regular local rings by regular sequences, so their number of equations equals their codimension for a structural reason, not merely by a generator count. Fitting ideals supply a complementary language: presentation matrices give canonical ideals that commute with base change and detect precisely where a finite module vanishes.

The aim is not a catalogue of these notions. The chapters follow one mechanism:

$$
\text{regular elements}
\longrightarrow \text{Koszul homology}
\longrightarrow \text{depth}
\longrightarrow \text{resolutions}
\longrightarrow \text{freeness},
$$

while a second mechanism runs in parallel:

$$
\text{presentation matrices}
\longrightarrow \text{Fitting ideals}
\longrightarrow \text{support}
\longrightarrow \text{faithfulness tests}.
$$

Their meeting point is the algebra used in patching: a module with maximal possible depth and sufficiently large support can constrain both its own resolution and the ring acting on it.

### 1.2 Standing conventions

All rings are commutative with identity and all modules are unital. Unless explicitly stated otherwise, $(R,\mathfrak m,k)$ is a Noetherian local ring and modules are finitely generated. The zero module requires conventions that can obscure statements, so assertions about regular sequences and Cohen--Macaulay modules concern nonzero modules. We set $\operatorname{depth}_R0=+\infty$ only when it makes exact-sequence formulas uniform.

For a finite $R$-module $M$,

$$
\operatorname{Supp}_R(M)=\{\mathfrak p\in\operatorname{Spec}R:M_{\mathfrak p}\ne0\},
\qquad
\dim_RM=\dim\operatorname{Supp}_R(M).
$$

Ring depth means $\operatorname{depth}_RR$; module depth means $\operatorname{depth}_RM$. They need not agree. A maximal Cohen--Macaulay module has depth equal to the dimension of the ring, whereas a Cohen--Macaulay module of smaller support has depth equal to its own dimension.

When completeness is invoked, it is maximal-ideal-adic completeness and includes separatedness. A complete local coefficient ring $\mathcal O$ is fixed only in sections about completed tensor products. The ordinary commutative-algebra statements do not require completeness.

### 1.3 Three kinds of numerical information

Three measurements must remain distinct.

First, $\dim R$ measures chains of prime ideals. Second, $\operatorname{depth}_RM$ measures how many successive equations from $\mathfrak m$ act injectively on $M$. Third, the Fitting ideals measure ranks of presentation matrices. Equalities among them are theorems with hypotheses, never definitions.

For instance, in

$$
R=k[[x,y]]/(xy),
$$

the ring has dimension and depth one but embedding dimension two. The module $R/(x)$ also has depth one, so it is maximal Cohen--Macaulay, yet it is not free over $R$. Its support is only the component $V(x)$, and its annihilator is nonzero. Thus maximal depth alone proves neither freeness nor faithfulness.

By contrast, over the regular local ring $k[[x,y]]$, every finite module has finite projective dimension. There maximal depth does force freeness. The difference between these examples is the homological quality of the ambient ring, which Chapters 6--10 make precise.

## 2. Nonzerodivisors and regular sequences

### 2.1 Why one equation at a time matters

Quotienting by one equation can lower dimension, but only when the equation is not already collapsing part of the module. Multiplication is the correct test. If multiplication by $x$ is injective on $M$, then imposing $x=0$ removes one genuine direction without killing a hidden submodule first. Repeating this test after each quotient leads to regular sequences.

The order in the definition is essential because each test takes place on a new quotient. Under the finite local hypotheses the resulting notion is eventually symmetric, but that symmetry is a theorem powered by Nakayama's lemma. Writing an unordered set at the outset would conceal both the mechanism and the hypotheses.

### 2.2 Regular elements on modules

An element $x\in R$ is an **$M$-nonzerodivisor** if multiplication

$$
M\xrightarrow{x}M
$$

is injective. Equivalently, $(0:_Mx)=0$. We call $x$ **$M$-regular** when it is an $M$-nonzerodivisor and $M/xM\ne0$. If $x\in\mathfrak m$ and $M$ is nonzero finite, the second condition is automatic by Nakayama.

The qualification “on $M$” cannot be dropped. In $R=k[[x,y]]/(xy)$, $x$ is a zerodivisor on $R$, but it is a nonzerodivisor on $R/(y)\simeq k[[x]]$. Conversely, a ring nonzerodivisor can act as zero on a quotient module: $x$ is regular on $k[[x]]$ and is not regular on $k[[x]]/(x)$.

For finite modules, associated primes give the geometric test

$$
x\text{ is an }M\text{-nonzerodivisor}
\quad\Longleftrightarrow\quad
x\notin\bigcup_{\mathfrak p\in\operatorname{Ass}_R(M)}\mathfrak p.
$$

Indeed the zerodivisors on $M$ are precisely the union of its associated primes. This finite union is what makes prime avoidance available.

### 2.3 Regular sequences and properness

A sequence $x_1,\ldots,x_r\in R$ is **$M$-regular** if

1. $x_i$ is a nonzerodivisor on $M/(x_1,\ldots,x_{i-1})M$ for every $i$; and
2. $M/(x_1,\ldots,x_r)M\ne0$.

For a sequence contained in $\mathfrak m$ and a nonzero finite module, properness again follows from Nakayama. The empty sequence is regular. A sequence is **$R$-regular** when it is regular on $R$.

Each step is represented by a short exact sequence

$$
0\longrightarrow M_{i-1}\xrightarrow{x_i}M_{i-1}
\longrightarrow M_i\longrightarrow0,
\qquad
M_i=M/(x_1,\ldots,x_i)M.
$$

Thus a regular sequence supplies much more than a dimension count: it supplies a chain of exact sequences. Koszul complexes will package all of them at once.

If $x_1,\ldots,x_r$ is $M$-regular, then every initial segment is regular, but an arbitrary subsequence need not be visibly regular until order-independence is proved. Also, an ideal may contain regular sequences of different lengths if locality or finite generation is absent. The local finite setting is designed to eliminate this ambiguity.

### 2.4 Order, locality, and finiteness

**Theorem (permutability).** Let $R$ be Noetherian, let $M$ be finite, and suppose $x_1,\ldots,x_r$ lie in the Jacobson radical of $R$. If they form an $M$-regular sequence, every permutation forms an $M$-regular sequence.

**Proof strategy.** Adjacent transpositions suffice. For a pair $x,y$, regularity says that $x$ is injective on $M$ and that $y$ is injective on $M/xM$. If $ym=0$, the second assertion gives $m=xm_1$; injectivity of $x$ then gives $ym_1=0$. Hence

$$
(0:_My)=x(0:_My).
$$

The annihilator is finite, and $x$ lies in the Jacobson radical, so Nakayama gives $(0:_My)=0$. Thus $y$ is regular on $M$.

Now suppose $xm\in yM$, say $xm=yn$. Reducing modulo $xM$ shows $yn=0$ there, so $n=xn_1$. Then $x(m-yn_1)=0$, whence $m=yn_1$. Therefore multiplication by $x$ is injective on $M/yM$. Properness is unchanged because the final quotient is the same. This exchanges $x$ and $y$; applying the argument after earlier quotients proves the theorem. $\square$

The proof displays the exact hypotheses. Finiteness and the Jacobson-radical condition enter only at the Nakayama step, but without them the conclusion can fail. Let

$$
R=k\times k[t]\times k[u,v],\qquad
x=(1,t,u),\quad y=(0,1,v).
$$

Then $x,y$ is an $R$-regular sequence: after quotienting by $x$, only $k[t]/(t)$ and $k[u,v]/(u)$ remain, and $y$ acts there as $1$ and $v$. The final quotient is nonzero. But $y$ is a zerodivisor on $R$, since it kills the first factor. The elements do not lie in the Jacobson radical, and order matters.

### 2.5 Maximal sequences and associated primes

Fix an ideal $I\subseteq\mathfrak m$. An $M$-regular sequence in $I$ is **maximal in $I$** if it cannot be extended by another element of $I$. If $x_1,\ldots,x_r$ has been chosen and $\overline M=M/(x_1,\ldots,x_r)M$, extension is possible precisely when $I$ is not contained in the union of $\operatorname{Ass}(\overline M)$. Prime avoidance then shows:

$$
\text{the sequence is maximal in }I
\quad\Longleftrightarrow\quad
I\subseteq\mathfrak p
\text{ for some }\mathfrak p\in\operatorname{Ass}(\overline M).
$$

At this point it is not yet clear that all maximal sequences have the same length. That is the problem solved by depth. The Ext characterization in Chapter 4 proves that their common length depends only on $I$ and $M$.

### 2.6 Worked examples and warnings

In the regular local ring $k[[x_1,\ldots,x_d]]$, the variables form a regular sequence. More generally, any permutation does, and the successive quotients are power-series rings of decreasing dimension.

In $R=k[[x,y]]/(xy)$, neither $x$ nor $y$ is regular on $R$. The element $x+y$ is regular: it lies in neither minimal prime $(x)$ nor $(y)$. Its quotient has dimension zero. Thus regular elements need not be members of a preferred coordinate system.

The sequence $x^2,y^3$ is regular in $k[[x,y]]$. Regularity is not the same as linear independence in $\mathfrak m/\mathfrak m^2$; both elements have zero cotangent class. It measures injectivity in successive quotients, not tangent directions.

Finally, two generators and height two do not by themselves form a regular sequence on an arbitrary module. In $R=k[[x,y]]$ and $M=R/(x)$, the ideal $(x,y)$ has height two in $R$, but $x$ annihilates $M$. The ambient ring and the chosen module must never be conflated.

## 3. The Koszul mechanism

### 3.1 A complex built from multiplication

Regular sequences are defined successively, but computations need a single object that sees the whole sequence, behaves under base change, and interacts with resolutions. The Koszul complex does exactly this. It replaces a list of multiplication maps by an exterior-algebra complex whose homology measures every failure of regularity.

Let $F=R^r$ with basis $e_1,\ldots,e_r$, and let $\mathbf x=(x_1,\ldots,x_r)$. The **Koszul complex** $K(\mathbf x;R)$ has

$$
K_i(\mathbf x;R)=\bigwedge^iF
$$

and differential determined by

$$
d(e_{j_1}\wedge\cdots\wedge e_{j_i})
=\sum_{a=1}^i(-1)^{a-1}x_{j_a}
e_{j_1}\wedge\cdots\widehat{e_{j_a}}\cdots\wedge e_{j_i}.
$$

For an $R$-module $M$, set $K(\mathbf x;M)=K(\mathbf x;R)\otimes_RM$. Its zeroth homology is always

$$
H_0(\mathbf x;M)=M/(\mathbf x)M.
$$

Every $x_i$ acts null-homotopically on the complex, so the ideal $(\mathbf x)$ annihilates every Koszul homology module. This small fact drives the Auslander--Buchsbaum proof later.

### 3.2 One element and the tensor construction

For one element,

$$
K(x;M):\qquad 0\longrightarrow M\xrightarrow{x}M\longrightarrow0,
$$

with the two copies in degrees one and zero. Hence

$$
H_1(x;M)=(0:_Mx),\qquad H_0(x;M)=M/xM.
$$

Thus $H_1=0$ says exactly that $x$ is a nonzerodivisor.

For several elements there is a canonical tensor decomposition

$$
K(x_1,\ldots,x_r;M)
\simeq K(x_r;R)\otimes_RK(x_1,\ldots,x_{r-1};M).
$$

Consequently adjoining $x_r$ gives short exact sequences relating its multiplication on the earlier Koszul homology to the new homology. This is the inductive engine behind regularity detection.

### 3.3 Regularity detected by homology

**Theorem (Koszul criterion).** Let $(R,\mathfrak m)$ be local, let $M$ be nonzero finite, and let $\mathbf x\subseteq\mathfrak m$. The following are equivalent:

1. $\mathbf x$ is $M$-regular;
2. $H_i(\mathbf x;M)=0$ for every $i>0$ and $M/(\mathbf x)M\ne0$;
3. the augmentation $K(\mathbf x;M)\to M/(\mathbf x)M$ is a resolution whose terms are finite direct sums of $M$.

**Proof strategy.** Induct on the length. The one-element calculation is the base. If the first $r-1$ elements are regular, their Koszul complex has homology only in degree zero. Tensoring with $K(x_r;R)$ then leaves the two-term complex

$$
0\to M/(x_1,\ldots,x_{r-1})M
\xrightarrow{x_r}
M/(x_1,\ldots,x_{r-1})M\to0.
$$

Its positive homology vanishes precisely when $x_r$ is regular on the quotient. Conversely, if all positive homology for the full complex vanishes, the exact sequences from the tensor decomposition show first that the shorter complex has no positive homology and then that multiplication by $x_r$ is injective on its zeroth homology. Nakayama rules out hidden homology on which $x_r$ acts surjectively. $\square$

The local and finite hypotheses in the converse are the same structural hypotheses that made order-independence work. Koszul homology therefore not only tests a given order; it explains why the order becomes irrelevant in the intended setting.

### 3.4 Self-duality and the depth formula

Exterior multiplication gives a perfect pairing

$$
\bigwedge^iF\times\bigwedge^{r-i}F\longrightarrow\bigwedge^rF\simeq R.
$$

After the usual signs, it identifies the dual Koszul complex with a shift of itself:

$$
\operatorname{Hom}_R(K(\mathbf x;R),R)
\simeq K(\mathbf x;R)[-r].
$$

This self-duality converts homology at the top into cohomology at the bottom. If $I=(\mathbf x)$ and $I$ lies in the Jacobson radical, then for finite $M$

$$
\operatorname{depth}_I(M)
=r-\sup\{i:H_i(\mathbf x;M)\ne0\}.
$$

The right side does not say that the generators are regular. Rather, it says how far their Koszul complex is from exact. If $\mathbf x$ is $M$-regular, the supremum is zero and the depth in $I$ is $r$. If every element of $I$ is a zerodivisor on $M$, top Koszul homology survives and the depth is zero.

The formula is independent of the chosen finite generating tuple for $I$. One way to see this is to identify both sides with the first nonvanishing Ext group, which is the subject of the next chapter.

### 3.5 Koszul resolutions and base change

If $x_1,\ldots,x_r$ is $R$-regular, the augmentation gives a finite free resolution

$$
0\to\bigwedge^rR^r\to\cdots\to R^r\to R
\to R/(\mathbf x)\to0.
$$

Thus a regular sequence produces both the quotient and a canonical resolution of it. Because the sequence is proper in the local ring, every $x_i$ lies in $\mathfrak m$, so this free resolution is minimal. In particular its projective dimension is exactly $r$.

For every ring map $R\to S$,

$$
K(\mathbf x;R)\otimes_RS\simeq K(\mathbf xS;S).
$$

If $S$ is flat, homology commutes with this tensor product. Hence regular sequences remain regular after flat base change whenever the final quotient stays nonzero. Faithfully flat base change also reflects regularity, because vanishing and nonvanishing of finite modules can be checked after tensoring. These observations will govern completion and complete-intersection base change.

## 4. Depth: regular sequences and Ext

### 4.1 What depth measures

Dimension asks how many independent prime-theoretic directions a support possesses. Depth asks how many of those directions can be cut successively without creating torsion. The inequality

$$
\operatorname{depth}_RM\leq\dim_RM
$$

expresses the fact that injective cuts cannot outnumber geometric dimensions. Equality is the Cohen--Macaulay condition.

The definition through maximal regular sequences is intuitive but initially ambiguous: why should two maximal sequences have equal length? Ext removes the ambiguity and makes exact sequences accessible. The equivalence of the two definitions is therefore foundational, not cosmetic.

### 4.2 Depth in an ideal

Let $I\subseteq\mathfrak m$ and suppose $M/IM\ne0$. Define $\operatorname{depth}_I(M)$ to be the supremum of lengths of $M$-regular sequences contained in $I$. Since $M$ is finite Noetherian, maximal sequences exist.

The key initial test is

$$
\operatorname{depth}_I(M)=0
\quad\Longleftrightarrow\quad
\operatorname{Hom}_R(R/I,M)\ne0.
$$

Indeed a nonzero homomorphism has image annihilated by $I$, so every element of $I$ is a zerodivisor. Conversely, if no element of $I$ is regular, prime avoidance places $I$ inside some associated prime $\mathfrak p=\operatorname{Ann}(m)$; a suitable multiple of $m$ then gives a nonzero element annihilated by $I$.

For the maximal ideal we write

$$
\operatorname{depth}_RM=\operatorname{depth}_{\mathfrak m}(M).
$$

### 4.3 The Ext characterization

**Theorem (grade equals depth).** Let $R$ be Noetherian local, let $M$ be nonzero finite, and let $I\subseteq\mathfrak m$ with $M/IM\ne0$. Then

$$
\operatorname{depth}_I(M)
=\inf\{i\ge0:\operatorname{Ext}_R^i(R/I,M)\ne0\}.
$$

Consequently every maximal $M$-regular sequence in $I$ has the same length.

**Proof strategy.** The proof follows a regular element through the long exact Ext sequence. The depth-zero test supplies the base case and prime avoidance supplies the next regular element.

Choose an $M$-regular $x\in I$ when the depth is positive, and put $\overline M=M/xM$. Apply $\operatorname{Hom}_R(R/I,-)$ to

$$
0\to M\xrightarrow{x}M\to\overline M\to0.
$$

Multiplication by $x$ on every $\operatorname{Ext}_R^i(R/I,M)$ is zero because $x$ annihilates the first argument. The long exact sequence therefore breaks into exact pieces

$$
0\to\operatorname{Ext}_R^i(R/I,M)
\to\operatorname{Ext}_R^i(R/I,\overline M)
\to\operatorname{Ext}_R^{i+1}(R/I,M)\to0.
$$

Moreover $\operatorname{Hom}_R(R/I,M)=0$, since an element annihilated by $I$ would in particular be annihilated by the injective element $x$. It follows that the first nonzero Ext degree for $M$ is exactly one larger than that for $\overline M$. Induction along a maximal regular sequence ends at a quotient of depth zero, where degree zero Ext is nonzero. This proves both the formula and equality of maximal lengths. $\square$

The theorem requires finite generation for associated primes and prime avoidance, and locality to keep regular elements inside the Jacobson radical. Ext can be defined much more generally, but this clean equivalence should not be exported without its hypotheses.

### 4.4 The local formula and first computations

Taking $I=\mathfrak m$ gives

$$
\operatorname{depth}_RM
=\inf\{i:\operatorname{Ext}_R^i(k,M)\ne0\}.
$$

Thus depth zero means that $M$ has nonzero socle. A discrete valuation ring $V$ has depth one: a uniformizer is regular, while its residue field has depth zero. If $R=k[[x_1,\ldots,x_d]]$, the variables form an $R$-regular sequence, so $\operatorname{depth}R=d$.

For $R=k[[x,y]]/(xy)$, the element $x+y$ is regular and the quotient is Artinian, so $\operatorname{depth}R=1$. The residue field has depth zero. The module $R/(x)\simeq k[[y]]$ also has depth one as an $R$-module, because $y$ acts regularly. This is the first example of a maximal Cohen--Macaulay module that is not free.

If $x$ is $M$-regular, the preceding proof also gives the useful shift

$$
\operatorname{depth}_R(M/xM)=\operatorname{depth}_RM-1.
$$

The formula is local: $x$ must lie in $\mathfrak m$, and $M$ must be finite and nonzero.

There is also a useful ideal-theoretic computation. If $I$ is generated by $r$ elements, then the Koszul depth formula shows

$$
0\le\operatorname{depth}_I(M)\le r.
$$

Equality on the right means that a generating $r$-tuple of $I$ is $M$-regular. At the other extreme, depth zero means that $I$ is contained in an associated prime of $M$. For

$$
R=k[[x,y,z]],\qquad M=R/(xy,xz),\qquad I=(y,z),
$$

the element $x$ in $M$ is annihilated by $I$, so $\operatorname{depth}_I(M)=0$ even though $I$ has height two in $R$. This again separates ambient height from module depth.

### 4.5 The depth lemma

Short exact sequences are the basic operations in resolutions. Depth interacts with all three terms, but asymmetrically.

**Theorem (depth lemma).** For a short exact sequence of finite modules over a Noetherian local ring,

$$
0\longrightarrow A\longrightarrow B\longrightarrow C\longrightarrow0,
$$

one has

$$
\begin{aligned}
\operatorname{depth}B&\ge
\min\{\operatorname{depth}A,\operatorname{depth}C\},\\
\operatorname{depth}A&\ge
\min\{\operatorname{depth}B,\operatorname{depth}C+1\},\\
\operatorname{depth}C&\ge
\min\{\operatorname{depth}A-1,\operatorname{depth}B\}.
\end{aligned}
$$

**Proof.** Apply $\operatorname{Hom}_R(k,-)$. In the resulting long exact sequence, if the Ext groups of both neighboring terms vanish through a given range, exactness forces the middle group to vanish in that range. For the first inequality, vanishing for $A$ and $C$ below $n$ forces vanishing for $B$ below $n$. For the second, vanishing for $B$ below $n$ and for $C$ below $n-1$ forces vanishing for $A$ below $n$. The third is obtained similarly from vanishing for $A$ below $n+1$ and for $B$ below $n$. The Ext characterization of depth translates these three vanishing statements into the displayed inequalities. $\square$

Two equality refinements are constantly useful:

- if $\operatorname{depth}A<\operatorname{depth}C$, then $\operatorname{depth}B=\operatorname{depth}A$;
- if $\operatorname{depth}A>\operatorname{depth}C+1$, then $\operatorname{depth}B=\operatorname{depth}C$;
- if $\operatorname{depth}B>\operatorname{depth}C$, then $\operatorname{depth}A=\operatorname{depth}C+1$.

They follow by combining the inequalities. Equal-depth boundary cases are deliberately not assigned a forced value.

### 4.6 Sharpness and nonconverses

Let $V$ be a discrete valuation ring with uniformizer $\pi$. In

$$
0\to V\xrightarrow{\pi}V\to k\to0,
$$

the depths are $(1,1,0)$. The second and third inequalities are equalities. For a sharp first inequality, use the split sequence

$$
0\to k\to k\oplus V\to V\to0,
$$

whose depths are $(0,0,1)$.

These examples also show why the three inequalities cannot be replaced by one symmetric equality. When the end terms have equal depth, the inequalities alone do not determine the middle term. For example, over $R=k[[x,y]]$, the sequence

$$
0\to R/(x)\xrightarrow{y}R/(xy)\to R/(y)\to0
$$

has all three terms of depth one. The inequalities permit this equality but do not prove it without further information. Exactness constrains depth, but it does not determine it in every boundary case.

A practical version of the equality refinements is worth recording. If two depths are unequal, the smaller one usually propagates to the adjacent term:

$$
\begin{aligned}
\operatorname{depth}A<\operatorname{depth}C
&\Longrightarrow \operatorname{depth}B=\operatorname{depth}A,\\
\operatorname{depth}A>\operatorname{depth}C+1
&\Longrightarrow \operatorname{depth}B=\operatorname{depth}C,\\
\operatorname{depth}B>\operatorname{depth}C
&\Longrightarrow \operatorname{depth}A=\operatorname{depth}C+1.
\end{aligned}
$$

The strict offset in the second line is deliberate. At the boundary $\operatorname{depth}A=\operatorname{depth}C+1$, both $\operatorname{depth}B=\operatorname{depth}C$ and larger values are compatible with the three inequalities.

## 5. Localization and completion

### 5.1 Why depth must travel

Support is assembled from localizations, while deformation rings are usually replaced by their completions. An invariant useful in both geometry and patching must survive these moves with precisely stated hypotheses. Regular sequences make the behavior intuitive; Ext and flatness make it reliable.

Localization can remove zerodivisors supported away from a chosen prime, so depth may rise. Completion is faithfully flat and retains the closed fiber, so local depth is unchanged. Confusing these two behaviors is a common source of false equalities.

### 5.2 Localizing regular sequences

Let $S\subseteq R$ be multiplicatively closed. If $x_1,\ldots,x_r$ is $M$-regular and the final localized quotient is nonzero, then

$$
x_1/1,\ldots,x_r/1
$$

is $S^{-1}M$-regular. Exactness of localization proves injectivity at every stage. The nonzero final quotient is essential and also ensures that none of the localized $x_i$ is a unit: a sequence containing a unit has zero final quotient.

At a prime $\mathfrak p$ containing all the $x_i$, the properness issue disappears whenever $M_{\mathfrak p}/(\mathbf x)M_{\mathfrak p}\ne0$. In particular, if $\mathfrak p\in\operatorname{Supp}(M/(\mathbf x)M)$, the localized sequence remains regular.

The converse does not hold from one localization. In $k[[x,y]]/(xy)$, the element $x$ becomes zero after localizing at the minimal prime $(x)$ and becomes a unit after localizing at $(y)$; neither observation makes it regular at the maximal ideal. Regularity is a statement over the whole relevant support.

### 5.3 Depth at primes

For $\mathfrak p\in\operatorname{Supp}M$, define

$$
\operatorname{depth}_{R_{\mathfrak p}}M_{\mathfrak p}
=\inf\{i:\operatorname{Ext}_{R_{\mathfrak p}}^i(\kappa(\mathfrak p),M_{\mathfrak p})\ne0\}.
$$

This is not generally equal to $\operatorname{depth}_RM$. For example, a positive-dimensional Cohen--Macaulay local domain has depth zero at its generic point and positive depth at its closed point, because the localized ring at the generic point is a field of dimension zero.

What localizes directly is depth in a finitely generated ideal:

$$
\operatorname{Ext}_R^i(R/I,M)_{\mathfrak p}
\simeq
\operatorname{Ext}_{R_{\mathfrak p}}^i(R_{\mathfrak p}/IR_{\mathfrak p},M_{\mathfrak p}).
$$

Thus vanishing of the global Ext groups gives vanishing after localization. When $I\subseteq\mathfrak p$, every $M$-regular sequence in $I$ that remains proper gives a lower bound for the localized depth. Depth can increase because the first nonzero global Ext module may vanish at $\mathfrak p$.

For a Cohen--Macaulay module $M$, localization behaves especially cleanly: for every $\mathfrak p\in\operatorname{Supp}M$,

$$
M_{\mathfrak p}\text{ is Cohen--Macaulay over }R_{\mathfrak p}.
$$

This statement uses Noetherian locality and finite generation. Its proof chooses parameters adapted to a chain through $\mathfrak p$ and localizes the corresponding regular sequence.

### 5.4 Flat base change of regular sequences

Let $R\to S$ be flat and let $M$ be finite. If $\mathbf x$ is $M$-regular and

$$
(M/(\mathbf x)M)\otimes_RS\ne0,
$$

then $\mathbf xS$ is regular on $M\otimes_RS$. Tensor each defining short exact sequence with $S$; flatness preserves its injective left map. If the map is faithfully flat, nonvanishing is automatic and regularity is reflected as well.

Flatness cannot be omitted. The element $x$ is regular on $R=k[[x]]$, but after the nonflat base change $R\to R/(x)$ it becomes zero and hence a zerodivisor on the nonzero target. Nor can one silently replace flatness by torsion-freeness over an arbitrary base: torsion-free and flat agree over a discrete valuation ring, not over general rings.

For a flat local map $(R,\mathfrak m)\to(S,\mathfrak n)$ of Noetherian local rings and a finite nonzero $M$, a regular sequence from $\mathfrak m$ preserves its length. Additional regular elements may come from the closed fiber $S/\mathfrak mS$. The exact depth formula is

$$
\operatorname{depth}_S(M\otimes_RS)
=\operatorname{depth}_RM+\operatorname{depth}(S/\mathfrak mS).
$$

The formula is best understood by concatenating a regular sequence from the base with lifts of a maximal regular sequence from the closed fiber, and then using Ext to prove maximality. No Cohen--Macaulay assumption on the fiber is needed; Cohen--Macaulayness is relevant when one wants to replace its depth by its dimension.

For example, adjoining a formal variable gives a flat local map

$$
R\longrightarrow R[[t]]
$$

whose closed fiber is $k[[t]]$ of depth one. Hence

$$
\operatorname{depth}_{R[[t]]}(M\otimes_RR[[t]])
=\operatorname{depth}_RM+1.
$$

The new regular element is $t$, after the regular sequence transported from $R$. By contrast, completion has zero-dimensional closed fiber and adds no depth.

### 5.5 Completion preserves depth

Let $\widehat R$ be the $\mathfrak m$-adic completion and $\widehat M=M\otimes_R\widehat R$. The map $R\to\widehat R$ is faithfully flat, local, and has closed fiber $k$. Hence

$$
\operatorname{depth}_{\widehat R}\widehat M
=\operatorname{depth}_RM,
\qquad
\dim_{\widehat R}\widehat M=\dim_RM.
$$

One proof of the depth equality transports a maximal regular sequence and then uses the Ext characterization to rule out a longer one. Another uses flat base change for $\operatorname{Ext}_R^i(k,M)$ and the identification $k\otimes_R\widehat R\simeq k$.

Thus completion preserves regularity, Cohen--Macaulayness, and the numerical gap $\dim M-\operatorname{depth}M$. It may introduce new prime ideals, so it does not preserve every fine statement about irreducible components. Later equidimensional claims will therefore use only those consequences actually established.

## 6. Free resolutions over local rings

### 6.1 Relations among relations

A finite presentation

$$
R^{b_1}\longrightarrow R^{b_0}\longrightarrow M\longrightarrow0
$$

records generators and their first relations. The kernel of the first map records relations among relations. Iterating produces a free resolution

$$
\cdots\longrightarrow F_2\xrightarrow{d_2}F_1
\xrightarrow{d_1}F_0\longrightarrow M\longrightarrow0.
$$

Over a local ring there is a canonical notion of having removed all redundant free summands. This minimality turns the ranks of the $F_i$ into invariants and lets reduction to the residue field read the resolution without any differentials.

### 6.2 Minimal free resolutions

A free resolution $F_\bullet\to M$ over $(R,\mathfrak m,k)$ is **minimal** if

$$
d_i(F_i)\subseteq\mathfrak mF_{i-1}
\qquad(i\ge1).
$$

Every finite module over a Noetherian local ring has a minimal free resolution with each $F_i$ finite free. Construct it recursively: choose a minimal set of generators of $M$, then a minimal set of generators of the kernel, and continue. Nakayama identifies minimal generation with a basis after reduction modulo $\mathfrak m$.

Any free resolution splits as a direct sum of a minimal resolution and contractible two-term complexes

$$
0\to R\xrightarrow{1}R\to0.
$$

Indeed a unit entry in a differential can be isolated by row and column operations, producing such a summand. Repeating removes every unit entry. It follows that minimal resolutions are unique up to isomorphism of complexes.

Over a local ring, finite projective modules are free. If $P$ is finite projective, choose a minimal surjection $R^r\twoheadrightarrow P$. It splits, and reduction modulo $\mathfrak m$ shows the complementary summand has zero residue quotient; Nakayama kills it. This is why free and projective resolutions coincide for the finite local theory.

### 6.3 Betti numbers and Tor detection

The **Betti numbers** of $M$ are

$$
\beta_i^R(M)=\operatorname{rank}_RF_i
$$

in a minimal free resolution. Tensoring that resolution with $k$ makes every differential zero, so

$$
\operatorname{Tor}_i^R(k,M)\simeq F_i\otimes_Rk,
\qquad
\beta_i^R(M)=\dim_k\operatorname{Tor}_i^R(k,M).
$$

This proves both invariance and the basic detection theorem:

$$
\operatorname{pd}_RM
=\sup\{i:\operatorname{Tor}_i^R(k,M)\ne0\}.
$$

If one of these numbers is finite, it is the last index in the minimal resolution. In particular $M$ is free precisely when $\operatorname{Tor}_1^R(k,M)=0$. The conclusion is local and finite: for an arbitrary infinitely generated module, vanishing of one Tor group need not give finite freeness.

### 6.4 Projective dimension and syzygies

The **projective dimension** $\operatorname{pd}_RM$ is the least length of a projective resolution, or $+\infty$ if none is finite. In the local finite setting it is the length of the minimal free resolution.

The kernel $\Omega M$ of a minimal surjection $F_0\to M$ is the first syzygy. If $0<\operatorname{pd}M<\infty$, then

$$
\operatorname{pd}_R(\Omega M)=\operatorname{pd}_RM-1.
$$

The depth lemma applied to

$$
0\to\Omega M\to F_0\to M\to0
$$

already suggests that depth and projective dimension should add to the fixed number $\operatorname{depth}R$. The equal-depth boundary prevents this observation alone from being a proof. Koszul homology resolves that boundary in Chapter 7.

### 6.5 Examples of finite and infinite resolutions

If $x_1,\ldots,x_r$ is an $R$-regular sequence, its Koszul resolution shows

$$
\operatorname{pd}_R R/(\mathbf x)=r,
\qquad
\beta_i^R(R/(\mathbf x))=\binom ri.
$$

For the dual numbers $R=k[\epsilon]/(\epsilon^2)$, the residue field has the infinite periodic minimal resolution

$$
\cdots\xrightarrow{\epsilon}R\xrightarrow{\epsilon}R
\xrightarrow{\epsilon}R\longrightarrow k\longrightarrow0.
$$

Thus every Betti number is one and $\operatorname{pd}_Rk=\infty$. The ring is a zero-dimensional hypersurface and hence a complete intersection, but it is not regular. Complete intersection does not mean finite global dimension.

For $R=k[[x,y]]/(xy)$ and $M=R/(x)$, a matrix-factorization resolution alternates multiplication by $x$ and $y$:

$$
\cdots\xrightarrow{x}R\xrightarrow{y}R\xrightarrow{x}R
\longrightarrow M\longrightarrow0.
$$

The module is maximal Cohen--Macaulay and has infinite projective dimension. This example will guard every later freeness statement.

## 7. The Auslander--Buchsbaum formula

### 7.1 The expected balance

If $M=R/(x_1,\ldots,x_r)$ for a regular sequence, then its projective dimension is $r$ and its depth is $\operatorname{depth}R-r$. The Auslander--Buchsbaum formula says that every nonzero finite module of finite projective dimension obeys the same balance:

$$
\operatorname{pd}_RM+\operatorname{depth}_RM=\operatorname{depth}R.
$$

The finiteness of projective dimension is indispensable. Over the dual numbers, the residue field has depth zero and the ring has depth zero, but the projective dimension is infinite. Treating infinity as though it were zero would destroy the theorem's content.

### 7.2 The homological depth calculation

The depth lemma handles a syzygy whenever its depth differs from that of a free module. Only one boundary case needs extra work: a module of projective dimension one. Minimality and a common regular element resolve it.

**Lemma (the length-one case).** If a nonzero finite module $M$ has $\operatorname{pd}_RM=1$, then

$$
\operatorname{depth}_RM=\operatorname{depth}R-1.
$$

**Proof strategy.** A minimal resolution has the form

$$
0\longrightarrow F_1\xrightarrow{d}F_0\longrightarrow M\longrightarrow0,
$$

with $F_1\ne0$ and every matrix entry of $d$ in $\mathfrak m$. First suppose $\operatorname{depth}R=0$. There is a nonzero socle element $a\in R$ with $\mathfrak ma=0$. Multiplying a basis vector of $F_1$ by $a$ gives a nonzero element killed by $d$, contradicting injectivity. Thus no nonzero finite module of projective dimension one exists when $R$ has depth zero.

Now put $d_R=\operatorname{depth}R>0$. The depth lemma gives $\operatorname{depth}M\ge d_R-1$. Suppose instead that $\operatorname{depth}M\ge d_R$. Prime avoidance chooses

$$
x\in\mathfrak m\setminus
\left(\bigcup\operatorname{Ass}R\cup\bigcup\operatorname{Ass}M\right),
$$

so $x$ is regular on both $R$ and $M$. Tensoring the displayed resolution with $R/(x)$ remains exact because

$$
\operatorname{Tor}_1^R(M,R/(x))=(0:_Mx)=0.
$$

It remains minimal and has length one over $R/(x)$. Both ring depth and module depth drop by one. Repeating $d_R$ times would produce a module of projective dimension one over a depth-zero local ring, contradicting the first paragraph. Hence $\operatorname{depth}M=d_R-1$. $\square$

This argument is homological at two decisive points. Minimality turns a socle element into an obstruction to an injective first differential, while Tor detects exactness after quotienting by a common regular element. Koszul theory supplies the regular-element depth drop used at every repetition.

### 7.3 Proof of the formula

**Theorem (Auslander--Buchsbaum).** Let $(R,\mathfrak m,k)$ be Noetherian local and let $M$ be a nonzero finite $R$-module with finite projective dimension. Then

$$
\operatorname{pd}_RM+\operatorname{depth}_RM=\operatorname{depth}R.
$$

**Proof.** Write $n=\operatorname{pd}_RM$ and induct on $n$. If $n=0$, then $M$ is nonzero finite free and has the same depth as $R$. The case $n=1$ is the lemma.

Suppose $n>1$ and begin a minimal resolution with

$$
0\longrightarrow K\longrightarrow F\longrightarrow M\longrightarrow0.
$$

The first syzygy $K$ has projective dimension $n-1$. Induction gives

$$
\operatorname{depth}K=\operatorname{depth}R-(n-1).
$$

This is strictly smaller than $\operatorname{depth}F=\operatorname{depth}R$. The three depth inequalities now force

$$
\operatorname{depth}M=\operatorname{depth}K-1
=\operatorname{depth}R-n.
$$

Rearranging proves the formula. Notice that if the right side were negative, the asserted finite resolution could not exist; the argument therefore also proves $n\le\operatorname{depth}R$. $\square$

The proof explains every hypothesis. Finite generation provides finite associated-prime sets and minimal finite-rank free covers. Locality makes minimality visible modulo one maximal ideal and supplies Nakayama. Finite projective dimension permits induction from a last syzygy. For an infinite resolution there is no terminal free stage and no finite equality.

### 7.4 Consequences and missing hypotheses

If $M$ has finite projective dimension, then

$$
\operatorname{depth}M\le\operatorname{depth}R.
$$

If equality holds, $\operatorname{pd}M=0$, so $M$ is free. This is the form most often used in patching.

If $R$ is Cohen--Macaulay of dimension $d$ and $M$ is maximal Cohen--Macaulay with finite projective dimension, then $M$ is free. The phrase “finite projective dimension” cannot be deleted, even when $R$ is a complete intersection: $R/(x)$ over $k[[x,y]]/(xy)$ is the counterexample.

Auslander--Buchsbaum is not a formula for arbitrary projective modules over nonlocal rings, nor for arbitrary infinitely generated modules. Such settings have their own localizations and finiteness issues. Here its force comes from the exact match among finite generation, local minimality, and Koszul depth.

## 8. Cohen--Macaulay modules and rings

### 8.1 When parameters impose independent conditions

A system of parameters cuts a finite module down to finite length. Dimension predicts how many cuts are needed, but it does not say that those cuts act injectively. Cohen--Macaulayness is the assertion that the geometric count and the injective count agree.

This condition eliminates embedded components and makes dimension cutting predictable. It does not make the ring regular, and it does not make every maximal-depth module free. Those stronger conclusions require control of resolutions.

### 8.2 Dimension of a module and systems of parameters

For a nonzero finite module $M$, its dimension is

$$
\dim_RM=\dim R/\operatorname{Ann}_R(M).
$$

A sequence $x_1,\ldots,x_d\in\mathfrak m$, where $d=\dim_RM$, is a **system of parameters for $M$** if

$$
M/(x_1,\ldots,x_d)M
$$

has finite length. Equivalently, the radical of $(\mathbf x)+\operatorname{Ann}M$ is $\mathfrak m$. A partial system of parameters is an initial segment extendable to a full one.

Krull's principal ideal theorem shows that one element can lower support dimension by at most one. Inductively, a regular sequence on $M$ has length at most $d$, proving

$$
\operatorname{depth}_RM\le d.
$$

The inequality can be strict. For $R=k[[x,y]]/(x^2,xy)$, the maximal ideal $(x,y)$ is associated because $x$ is annihilated by it. Hence $\operatorname{depth}R=0$, while $\dim R=1$.

### 8.3 Equivalent Cohen--Macaulay criteria

A nonzero finite module $M$ is **Cohen--Macaulay** if

$$
\operatorname{depth}_RM=\dim_RM.
$$

The local ring $R$ is Cohen--Macaulay if it is so as an $R$-module. A finite module is **maximal Cohen--Macaulay** if

$$
\operatorname{depth}_RM=\dim R.
$$

This forces $\dim_RM=\dim R$, but says nothing yet about its annihilator.

**Theorem (parameters and depth).** Let $M$ be a nonzero finite module of dimension $d$. The following are equivalent:

1. $M$ is Cohen--Macaulay;
2. some system of parameters for $M$ is $M$-regular;
3. every system of parameters for $M$ is $M$-regular;
4. every partial system of parameters is $M$-regular.

**Proof strategy.** A regular system of parameters has length $d$, giving depth $d$. Conversely, if depth equals $d$, an element that begins a parameter system avoids all top-dimensional minimal primes of the support. Cohen--Macaulayness ensures there are no smaller-dimensional associated primes, so it avoids every associated prime and is regular. The quotient has dimension and depth $d-1$; induction proves that all remaining parameter elements are regular. The same induction proves the partial form. $\square$

Consequently quotienting a Cohen--Macaulay module by a regular element preserves Cohen--Macaulayness and lowers its dimension by one.

### 8.4 Unmixedness and equidimensionality

The preceding proof contains a geometric consequence worth isolating.

**Theorem (unmixedness).** If $M$ is Cohen--Macaulay of dimension $d$ over a Noetherian local ring, then

$$
\operatorname{Ass}_R(M)=
\{\mathfrak p\in\operatorname{Supp}M:\dim R/\mathfrak p=d
\text{ and }\mathfrak p\text{ is minimal in }\operatorname{Supp}M\}.
$$

In particular $M$ has no embedded associated primes, and all irreducible components of its support have dimension $d$.

**Reason.** Localizing at an associated prime gives depth zero. Localization of a Cohen--Macaulay module is Cohen--Macaulay, so its localized dimension is zero; hence the prime is minimal in the support. Extending a parameter sequence from that component shows its global component dimension is $d$. $\square$

Taking $M=R$ shows that a Cohen--Macaulay local ring is unmixed and equidimensional in this sense: its minimal primes all have dimension $\dim R$, and it has no embedded associated primes. This is a statement about the local ring itself. We do not infer stronger universal catenarity or geometric reducedness; neither follows merely from Cohen--Macaulayness.

One way to see the equal-dimensional assertion without hiding the dimension step is to choose a parameter sequence adapted to an associated prime $\mathfrak p$. Regularity of every parameter sequence prevents a parameter from entering an associated prime of the preceding quotient. If $\dim R/\mathfrak p<d$, a system of parameters beginning with enough elements to cut the component $V(\mathfrak p)$ would eventually force exactly that contradiction before all $d$ regular cuts had occurred. Hence every associated component has dimension $d$.

### 8.5 Examples and counterexamples

Every regular local ring is Cohen--Macaulay: a regular system of parameters is a regular sequence. Every quotient of a Cohen--Macaulay local ring by a regular sequence is Cohen--Macaulay. Thus

$$
k[[x_1,\ldots,x_n]]/(f_1,\ldots,f_c)
$$

is Cohen--Macaulay whenever $f_1,\ldots,f_c$ is regular.

The nodal ring $k[[x,y]]/(xy)$ is Cohen--Macaulay of dimension one but not regular. It is reduced and equidimensional. The ring $k[[x,y]]/(x^2,xy)$ has dimension one and depth zero; its embedded associated prime $(x,y)$ explains the failure.

Over $R=k[[x,y]]/(xy)$, the module $(x)\simeq R/(y)$ is maximal Cohen--Macaulay. It is not free: its annihilator contains $y$. Thus even a maximal Cohen--Macaulay module over a hypersurface may be nonfree and nonfaithful.

The module $R\oplus R/(x)$ has full support and is faithful because of its free summand, and its depth is one. It is maximal Cohen--Macaulay but still not free. Faithfulness plus maximal depth is therefore insufficient over a singular ring. The missing input is finite projective dimension.

## 9. Regular local rings through resolutions

### 9.1 Regularity revisited

Book 69 characterized a Noetherian local ring as regular when

$$
\operatorname{edim}R=\dim R.
$$

That equality says the maximal ideal has as few generators as dimension permits. Depth now gives a stronger interpretation. If $d=\dim R$ and $x_1,\ldots,x_d$ minimally generate $\mathfrak m$, Book 69 identified

$$
\operatorname{gr}_{\mathfrak m}R
\simeq k[X_1,\ldots,X_d],
$$

with $X_i$ the initial form of $x_i$. Multiplication by $X_1$ is injective on the graded ring. If $x_1a=0$ in $R$, taking the lowest nonzero initial form of $a$ would therefore give $X_1\operatorname{in}(a)=0$, a contradiction. Thus $x_1$ is regular. The associated graded ring of $R/(x_1)$ is the quotient by $X_1$, and induction proves that $x_1,\ldots,x_d$ is an $R$-regular sequence. Hence a regular local ring is Cohen--Macaulay of depth $d$. This argument is important: equality of embedding dimension and dimension does not imply regular-sequence exactness merely by counting; the polynomial associated graded ring supplies the missing injectivity.

The resolution-theoretic characterization is more remarkable: regularity means that every finite module has a finite free resolution, with a uniform length bound. Thus smooth local geometry is equivalent to finite homological complexity.

### 9.2 Finite global dimension

**Theorem (homological characterization of regular local rings).** For a Noetherian local ring $(R,\mathfrak m,k)$ of dimension $d$, the following are equivalent:

1. $R$ is regular;
2. $\operatorname{pd}_Rk<\infty$;
3. every finite $R$-module has finite projective dimension.

When these conditions hold,

$$
\operatorname{pd}_Rk=d,
\qquad
\sup_M\operatorname{pd}_RM=d,
$$

where $M$ ranges over nonzero finite modules.

**Proof strategy.** If $R$ is regular, Section 9.1 shows that a minimal generating set of $\mathfrak m$ is a regular sequence of length $d$. Its Koszul complex is a length-$d$ free resolution of $k$, so $\operatorname{pd}k=d$. For every finite $M$, the same resolution computes $\operatorname{Tor}_i^R(k,M)$ and makes it zero for $i>d$. Tor detection in a minimal resolution of $M$ then gives $\operatorname{pd}_RM\le d$.

The converse uses the decisive change-of-rings step in the Auslander--Buchsbaum--Serre theorem. We record the step explicitly. If $x\in\mathfrak m\setminus\mathfrak m^2$ is $R$-regular and $\overline R=R/(x)$, then the change-of-rings construction for minimal resolutions gives

$$
\operatorname{pd}_Rk
=\operatorname{pd}_{\overline R}k+1
$$

whenever either side is finite. One obtains the construction by lifting a minimal resolution over $\overline R$ and adjoining the two-term complex for multiplication by $x$; conversely, reducing a finite minimal resolution over $R$ and cancelling the one degree-one class represented by $x$ recovers a finite resolution over $\overline R$. The condition $x\notin\mathfrak m^2$ is what makes this class minimal.

Now suppose $k$ has finite projective dimension. Auslander--Buchsbaum gives

$$
\operatorname{pd}_Rk=\operatorname{depth}R,
$$

because $\operatorname{depth}k=0$. If $R$ is not a field, this depth is positive. Prime avoidance, applied also to $\mathfrak m^2$, supplies an $R$-regular element $x\in\mathfrak m\setminus\mathfrak m^2$. The change-of-rings step makes $k$ have finite projective dimension over $\overline R=R/(x)$. Induction on $\operatorname{pd}_Rk$ shows that $\overline R$ is regular. Since $x$ is both regular and part of a minimal generating set,

$$
\dim R=\dim\overline R+1
=\operatorname{edim}\overline R+1
=\operatorname{edim}R.
$$

Thus $R$ is regular. The implication from (3) to (2) is immediate. This also shows exactly where finite termination enters; Auslander--Buchsbaum by itself gives a depth equality but does not by itself prove regularity. $\square$

The supremum above is the finite-module global dimension. For a general module one may define global dimension using all modules; the same value occurs for a Noetherian regular local ring, but the finite-module form is all that is needed here.

Two examples calibrate the theorem. A discrete valuation ring has global dimension one on finite modules: torsion modules have length-one resolutions and free modules have projective dimension zero. The ring $k[[x,y]]$ has dimension two, and the Koszul resolution of $k$ has ranks $1,2,1$. In contrast, $k[[x,y]]/(xy)$ has the same dimension as a discrete valuation ring but its residue field and many maximal Cohen--Macaulay modules have infinite projective dimension. Dimension alone does not control resolution length.

### 9.3 Maximal Cohen--Macaulay modules over regular rings

Let $R$ be regular local of dimension $d$ and let $M$ be finite. The preceding theorem gives finite projective dimension, so Auslander--Buchsbaum yields

$$
\operatorname{pd}_RM=d-\operatorname{depth}_RM.
$$

Therefore

$$
M\text{ is maximal Cohen--Macaulay}
\quad\Longleftrightarrow\quad
M\text{ is finite free}.
$$

This equivalence is a property of the regular ambient ring. Over a singular Cohen--Macaulay ring, the implication from free to maximal Cohen--Macaulay remains true, but the converse can fail spectacularly through periodic resolutions.

A related criterion is useful. If $R$ is regular and $M$ is finite of dimension $d$, then $M$ is maximal Cohen--Macaulay exactly when it has no positive Tor with $k$. In practice one usually proves depth $d$ and invokes Auslander--Buchsbaum rather than checking every Tor group.

## 10. Complete-intersection local rings

### 10.1 Equations of the expected codimension

A presentation $A=Q/I$ may use many equations, but dimension sees only the height of $I$. The ideal defines a complete intersection when its equations are as independent as possible: they form a regular sequence. Then each equation lowers dimension by exactly one, the Koszul complex resolves the quotient, and the number of equations is the codimension.

This is a property stronger than Cohen--Macaulayness and weaker than regularity. Regular local rings correspond to zero equations. Hypersurfaces correspond to one nonzerodivisor. Singular complete intersections retain controlled homological behavior but can still possess nonfree maximal Cohen--Macaulay modules.

### 10.2 Definitions and codimension

Let $(Q,\mathfrak n)$ be regular local and let $I\subsetneq Q$. A quotient

$$
A=Q/I
$$

is a **complete-intersection presentation** if $I$ is generated by a $Q$-regular sequence $f_1,\ldots,f_c$. Then $A$ is a **complete-intersection local ring**.

For an arbitrary Noetherian local ring $A$, one commonly allows completion: $A$ is complete intersection if

$$
\widehat A\simeq Q/(f_1,\ldots,f_c)
$$

for some complete regular local $Q$ and a regular sequence. This definition is intrinsic and is the appropriate one when a regular presentation exists naturally only after completion. For the complete coefficient rings of Book 69, no extra completion is needed.

In a complete-intersection presentation,

$$
\dim A=\dim Q-c,
\qquad
\operatorname{depth}A=\dim A,
\qquad
\operatorname{pd}_QA=c.
$$

The first equality follows by successive principal ideal theorem together with regularity; the second follows because regular local rings are Cohen--Macaulay and regular quotients preserve Cohen--Macaulayness; the third comes from the Koszul resolution and Auslander--Buchsbaum.

A presentation is **minimal** if $I\subseteq\mathfrak n^2$. In that case the map on cotangent spaces is an isomorphism and

$$
\operatorname{edim}A=\operatorname{edim}Q=\dim Q.
$$

Hence the **absolute codimension** is

$$
\operatorname{codim}A
:=\operatorname{edim}A-\dim A=c.
$$

If the presentation is not minimal, a relation with nonzero linear term eliminates a variable. Its raw number of equations is not the intrinsic codimension.

This elimination can be seen directly. Suppose

$$
A=k[[x_1,\ldots,x_n,z]]/(z-h(\mathbf x),f_1(\mathbf x),\ldots,f_c(\mathbf x)).
$$

The first relation has unit coefficient on $z$, so substitution removes both $z$ and that relation:

$$
A\simeq k[[x_1,\ldots,x_n]]/(f_1,\ldots,f_c).
$$

The nonminimal presentation has $c+1$ equations but the same intrinsic codimension $c$. Requiring the kernel to lie in the square of the source maximal ideal prevents precisely this artificial inflation.

Over a coefficient ring $\mathcal O$, a relative power-series presentation may have a **relative codimension**, the number of equations in a minimal relative complete-intersection presentation. Absolute and relative codimension need not agree when a coefficient parameter becomes dependent in the absolute cotangent space. The mixed-characteristic ring

$$
\mathcal O[[x,y]]/(xy-\varpi)
$$

has one relative equation but is a regular local ring, hence has absolute codimension zero.

### 10.3 Independence of presentation

The definition appears to depend on $Q$, but the property and the number $c$ do not.

**Theorem (independence).** Suppose a complete Noetherian local ring $A$ admits a surjection $Q\twoheadrightarrow A$ from a complete regular local ring, with kernel contained in $\mathfrak n_Q^2$. Then $A$ is complete intersection if and only if that kernel is generated by a regular sequence. When this holds, every minimal regular-local presentation has exactly

$$
c=\operatorname{edim}A-\dim A
$$

relations.

**Proof strategy.** Minimality identifies the embedding dimensions of $Q$ and $A$. If the kernel is generated by a regular sequence, dimension drops by its length, giving the intrinsic formula for $c$. For two minimal Cohen presentations, lift minimal cotangent bases in both directions. After adjoining the same number of formal variables, the resulting comparison maps between the complete regular sources become isomorphisms: surjectivity is detected on cotangent spaces, and equal source dimensions kill the kernel. Under this common source the two kernel ideals differ by an automorphism. Thus their minimal generator numbers agree. Since a regular local source is Cohen--Macaulay, an ideal whose generator number equals its height is generated by a regular sequence, by Section 10.5. Complete-intersection quality therefore transfers from one minimal presentation to every other one. $\square$

This theorem is why “number of equations equals codimension” is meaningful only for a minimal presentation. A nonminimal presentation can add a variable $z$ and the relation $z$, increasing both source dimension and relation count without changing $A$.

### 10.4 The conormal module

For $A=Q/I$, the **conormal module** is

$$
I/I^2,
$$

an $A$-module. It records equations to first order along the quotient, rather than only at the closed point. There is an exact conormal sequence

$$
I/I^2\longrightarrow
\Omega_{Q/B}\otimes_QA
\longrightarrow\Omega_{A/B}\longrightarrow0
$$

relative to any base $B$.

If $I=(f_1,\ldots,f_c)$ is generated by a regular sequence, then the residue classes of the $f_i$ form an $A$-basis of $I/I^2$:

$$
I/I^2\simeq A^c.
$$

To see independence, suppose $\sum a_if_i\in I^2$. Modulo the earlier $f_j$, regularity of $f_i$ successively forces each coefficient into $I$. Generation is immediate. Thus the conormal module remembers the codimension everywhere on the quotient.

The converse “$I/I^2$ is free, therefore $I$ is generated by a regular sequence” is not safe without additional hypotheses. Conormal freeness is an infinitesimal condition; finite projective dimension or a height/generator condition is needed to rule out hidden higher relations.

### 10.5 Elementary complete-intersection criteria

The most useful elementary criterion is numerical but must be applied in a Cohen--Macaulay ambient ring.

**Proposition.** Let $(Q,\mathfrak n)$ be Cohen--Macaulay and let $I$ be a proper ideal generated by $c$ elements. If $\operatorname{ht}I=c$, then every minimal generating $c$-tuple of $I$ is a $Q$-regular sequence.

**Proof.** Cohen--Macaulayness gives

$$
\operatorname{depth}_I(Q)=\operatorname{ht}I=c.
$$

For any generating tuple $f_1,\ldots,f_c$ of $I$, the Koszul depth formula reads

$$
c=c-\sup\{i:H_i(f_1,\ldots,f_c;Q)\ne0\}.
$$

Thus every positive Koszul homology module vanishes, and the Koszul criterion makes the tuple regular. In particular this applies to every minimal generating $c$-tuple. $\square$

When $Q$ is regular and $A=Q/I$ is Cohen--Macaulay, Auslander--Buchsbaum gives

$$
\operatorname{pd}_QA
=\dim Q-\dim A=\operatorname{ht}I.
$$

Therefore the following are equivalent if $I$ can be generated by $c=\operatorname{ht}I$ elements:

$$
I\text{ is generated by a regular sequence}
\quad\Longleftrightarrow\quad
\mu_Q(I)=\operatorname{ht}I.
$$

A useful conormal version is: if $Q$ is Cohen--Macaulay local and $I/I^2$ is a free $A=Q/I$-module of rank $c=\operatorname{ht}I$, then

$$
\frac{I/I^2}{\mathfrak m_A(I/I^2)}
\simeq\frac{I}{\mathfrak n_QI}
$$

has dimension $c$ over the residue field. Nakayama gives $\mu_Q(I)=c$, and the proposition makes any minimal generators a regular sequence. The rank/height match and the Cohen--Macaulay ambient ring are the decisive hypotheses here. In the more general conormal criterion with a non-Cohen--Macaulay ambient ring, conormal projectivity must be supplemented by a finite-projective-dimension, or finite Tor-dimension, hypothesis; conormal freeness alone does not control higher relations.

### 10.6 Examples and boundary cases

Every hypersurface $Q/(f)$ with $Q$ regular local and $0\ne f\in\mathfrak n$ is a complete intersection. It may be nonreduced, as $k[[x]]/(x^n)$ shows, or reducible, as $k[[x,y]]/(xy)$ shows.

The Artinian ring

$$
A=k[[x,y]]/(x^2,y^2)
$$

is a codimension-two complete intersection. Its length is four and its socle is generated by $xy$.

By contrast,

$$
B=k[[x,y]]/(x^2,xy,y^2)
$$

has dimension zero and embedding dimension two, so a minimal complete-intersection presentation would need two equations. Its defining ideal needs three generators. Hence $B$ is not a complete intersection. It is Cohen--Macaulay because every zero-dimensional local ring is, showing that Cohen--Macaulayness is strictly weaker.

The quotient $k[[x,y,z]]/(xy,xz)$ has an ideal generated by two elements of height one. The generator count exceeds height, and the displayed pair is not regular: after quotienting by $xy$, the class of $xz$ is killed by $y$. Raw relation number again fails to measure codimension.

Conormal modules distinguish the two codimension-two Artinian examples above. For $A=k[[x,y]]/(x^2,y^2)$, the classes of $x^2$ and $y^2$ freely generate $I/I^2$. For $B$, the three classes of $x^2,xy,y^2$ minimally generate its conormal module at the closed point. Since the intrinsic codimension is two, that excess generator witnesses failure of the complete-intersection condition.

## 11. Stability of complete intersections

### 11.1 Completion and quotients

Complete intersections must survive the operations used to pass between local presentations. Completion is the cleanest. If $A$ is a quotient $Q/(\mathbf f)$ by a regular sequence, faithful flatness gives

$$
\widehat A\simeq\widehat Q/(\mathbf f)\widehat Q,
$$

and the sequence stays regular. Conversely, the standard local definition declares $A$ complete intersection exactly when $\widehat A$ is. Thus completion neither creates nor destroys the property in this sense.

If $A$ is complete intersection and $x\in\mathfrak m_A$ is $A$-regular, then $A/(x)$ is complete intersection. To justify the statement from a regular presentation $A=Q/(\mathbf f)$, lift $x$ to $\widetilde x\in Q$. Since $x$ is regular modulo $(\mathbf f)$, the concatenation

$$
f_1,\ldots,f_c,\widetilde x
$$

is $Q$-regular. Hence $A/(x)$ is a regular-local quotient by a regular sequence of length $c+1$.

The converse requires care. If $x$ is regular and $A/(x)$ is complete intersection, then $A$ is complete intersection under the usual Noetherian local hypotheses; one lifts a regular presentation and uses the conormal criterion to remove the final equation. If $x$ is a zerodivisor, no such conclusion is valid.

### 11.2 Flat base change

Suppose $A=Q/(f_1,\ldots,f_c)$ and $Q\to Q'$ is flat. If the quotient after base change is nonzero, then

$$
A\otimes_QQ'\simeq Q'/(f_1,\ldots,f_c)Q'
$$

and the displayed sequence is $Q'$-regular. This is a presentation-level ascent statement. To conclude that the target is a complete-intersection **local ring**, one must also know that the chosen localization of $Q'$ is regular local. Flatness alone does not preserve regularity of the ambient ring; the fibers matter.

In particular, for a flat local map of Noetherian local rings, regularity of the source and of the closed fiber implies regularity of the target. Base-changing a complete-intersection presentation along such a regular ambient change therefore gives a complete intersection.

The descent statement needed at presentation level is equally precise. If $Q\to Q'$ is faithfully flat, $I\subseteq Q$ is finitely generated, and $Q'/IQ'$ is nonzero, then a chosen generating tuple of $I$ is $Q$-regular if and only if its image is $Q'$-regular. This follows by reflecting vanishing of its finite Koszul homology and nonvanishing of its final quotient. Consequently complete-intersection quality descends for a fixed presentation under a faithfully flat regular-ambient change. Descent from an unrelated complete-intersection presentation of the target is a deeper theorem and is not being used here.

These qualifications prevent a common overstatement. “Complete intersections are stable under arbitrary flat base change” is meaningful for the morphism or presentation, but an arbitrary target base may already be singular. The absolute ring property requires a regular ambient base after the change.

### 11.3 Completed tensor products

Completed tensor products combine two complete local problems and therefore need a version of the preceding base-change argument with topology included.

Over a field $k$, suppose

$$
A\simeq k[[\mathbf x]]/(\mathbf f),
\qquad
B\simeq k[[\mathbf y]]/(\mathbf g),
$$

where $\mathbf f$ and $\mathbf g$ are regular sequences. Then

$$
A\widehat\otimes_kB
\simeq
k[[\mathbf x,\mathbf y]]/(\mathbf f,\mathbf g).
$$

Flatness of the two formal power-series extensions shows that the concatenated sequence is regular. Hence the completed tensor product is a complete intersection, and its codimension is the sum of the two codimensions.

Over a complete discrete valuation ring $\mathcal O$, assume $A$ and $B$ are complete Noetherian local, topologically of finite type over $\mathcal O$, and flat over $\mathcal O$, with presentations

$$
A\simeq\mathcal O[[\mathbf x]]/(\mathbf f),
\qquad
B\simeq\mathcal O[[\mathbf y]]/(\mathbf g)
$$

by relative regular sequences. Then

$$
A\widehat\otimes_{\mathcal O}B
\simeq
\mathcal O[[\mathbf x,\mathbf y]]/(\mathbf f,\mathbf g).
$$

The flatness of the intermediate quotient over $\mathcal O$ ensures that the second sequence remains regular after the first quotient. The result is a relative complete intersection and relative codimensions add. The shared coefficient parameter occurs only once.

### 11.4 What can fail

Three boundaries should remain visible.

First, nonflat specialization can turn a regular element into zero. Second, a completed tensor product need not be Noetherian or local without topological finite-type and residue-field compatibility assumptions. Third, over a discrete valuation base, if one factor has coefficient torsion, equations from the two factors can interact through the uniformizer and concatenation need not remain regular.

For the simplest illustration, take $A=B=k=\mathcal O/(\varpi)$. Both are hypersurface quotients of $\mathcal O$, but

$$
A\widehat\otimes_{\mathcal O}B\simeq k.
$$

Combining the two presentations would list $\varpi,\varpi$ in the same ambient ring; the second copy is zero after the first quotient and is not regular. The output happens still to be a complete intersection, but codimensions do not add. Flatness is what prevents this duplication in the theorem of Section 11.3.

Absolute codimension also need not be the sum of relative codimensions. The ring $\mathcal O[[x,y]]/(xy-\varpi)$ is relatively a hypersurface but absolutely regular. Any codimension formula must state which cotangent space and which base it uses.

## 12. Fitting ideals from presentations

### 12.1 Why annihilators are not enough

The annihilator of a module records which scalars act as zero. It detects support set-theoretically, but it does not interact transparently with presentation matrices or arbitrary base change. Fitting ideals solve this problem by extracting determinantal data from a finite presentation.

The zeroth Fitting ideal detects where a module vanishes. Higher Fitting ideals stratify the spectrum by the number of local generators. Because minors commute with every scalar extension, these ideals are exceptionally well suited to families and patching.

### 12.2 Definition by minors

Let $M$ be a finitely presented $R$-module and choose a presentation

$$
R^p\xrightarrow{A}R^q\longrightarrow M\longrightarrow0.
$$

For $i\ge0$, define

$$
\operatorname{Fitt}_i^R(M)=I_{q-i}(A),
$$

the ideal generated by all $(q-i)\times(q-i)$ minors of the matrix $A$. We use the conventions

$$
I_t(A)=R\quad(t\le0),
\qquad
I_t(A)=0\quad(t>\min\{p,q\}).
$$

Thus

$$
\operatorname{Fitt}_0(M)\subseteq
\operatorname{Fitt}_1(M)\subseteq\cdots,
$$

and $\operatorname{Fitt}_i(M)=R$ for $i\ge q$. Locally, $\operatorname{Fitt}_i(M)=R$ precisely where $M$ can be generated by at most $i$ elements.

### 12.3 Independence and the chain of ideals

Although the definition uses a matrix, the ideals depend only on $M$.

**Theorem (presentation independence).** Elementary row and column operations, adjoining redundant relation generators, and stabilization by a generator--relation block $R\xrightarrow{1}R$ do not change the appropriately indexed determinantal ideals. Any two finite presentations admit a common refinement by these presentation moves. Therefore $\operatorname{Fitt}_i(M)$ is intrinsic.

**Proof strategy.** Invertible row or column operations replace minors by invertible linear combinations of minors of the same size. A redundant relation adds a column already generated by the old relation columns and changes no determinantal ideal. Stabilization by an identity block converts each relevant minor into either zero or an old minor, with the indexing shift exactly compensated by the added target generator. Lifting the generators of either presentation through the other produces a common refinement. $\square$

Finite presentation is essential over a general ring. A finite module over a Noetherian ring is automatically finitely presented, which is why the distinction is often invisible in local algebra. For an arbitrary noncoherent ring, finite generation alone does not provide a finite relation matrix, so the stated construction and base-change theorem are unavailable.

### 12.4 Base change and localization

For every ring map $R\to S$ and finitely presented $M$,

$$
\operatorname{Fitt}_i^S(M\otimes_RS)
=\operatorname{Fitt}_i^R(M)S.
$$

No flatness is required: tensor the chosen finite presentation and observe that its minors are the images of the old minors. Exactness on the left of the presentation is irrelevant; right exactness is enough to present the tensor product.

Taking $S=R_{\mathfrak p}$ gives

$$
\operatorname{Fitt}_i^{R_{\mathfrak p}}(M_{\mathfrak p})
=\operatorname{Fitt}_i^R(M)R_{\mathfrak p}.
$$

Taking a quotient gives the corresponding formula modulo any ideal. This unconditional base-change behavior is the central advantage of Fitting ideals over many invariants defined from a chosen minimal resolution.

### 12.5 Cyclic modules and direct sums

For a cyclic module $M=R/I$, the presentation by generators of $I$ gives

$$
\operatorname{Fitt}_0(R/I)=I,
\qquad
\operatorname{Fitt}_i(R/I)=R\quad(i\ge1).
$$

For finite free $R^r$,

$$
\operatorname{Fitt}_i(R^r)=
\begin{cases}
0,&i<r,\\
R,&i\ge r.
\end{cases}
$$

Direct sums satisfy the convolution formula

$$
\operatorname{Fitt}_n(M\oplus N)
=\sum_{i+j=n}
\operatorname{Fitt}_i(M)\operatorname{Fitt}_j(N).
$$

It follows from the block-diagonal presentation matrix and Laplace expansion of its minors. In particular,

$$
\operatorname{Fitt}_0(M\oplus N)
=\operatorname{Fitt}_0(M)\operatorname{Fitt}_0(N).
$$

For example,

$$
\operatorname{Fitt}_0(R/(a)\oplus R/(b))=(ab),
$$

whereas its annihilator is $(a)\cap(b)$. This difference anticipates the next chapter.

## 13. Support, annihilators, and faithfulness

### 13.1 Zeroth Fitting ideals detect support

The zeroth Fitting ideal has a precise geometric meaning.

**Theorem.** If $M$ is a finitely presented $R$-module, then

$$
\operatorname{Supp}_R(M)=V(\operatorname{Fitt}_0^R(M)).
$$

**Proof.** Localize at $\mathfrak p$. By base change,

$$
\operatorname{Fitt}_0(M)R_{\mathfrak p}
=\operatorname{Fitt}_0(M_{\mathfrak p}).
$$

If $M_{\mathfrak p}=0$, it has the presentation $0\to0$, and its zeroth Fitting ideal is the unit ideal. Conversely, suppose $\operatorname{Fitt}_0(M_{\mathfrak p})=R_{\mathfrak p}$. In a presentation $R_{\mathfrak p}^p\to R_{\mathfrak p}^q\to M_{\mathfrak p}\to0$, some $q\times q$ minor is a unit. The corresponding $q$ columns give a surjection onto $R_{\mathfrak p}^q$, so the cokernel is zero. Therefore

$$
M_{\mathfrak p}\ne0
\quad\Longleftrightarrow\quad
\operatorname{Fitt}_0(M)\subseteq\mathfrak p.
$$

This is exactly the asserted equality. $\square$

For finite modules over Noetherian rings, finite presentation is automatic. Outside that setting, one must either assume a finite presentation or use a separately defined generalized Fitting ideal.

Higher Fitting ideals refine the statement:

$$
\{\mathfrak p:\mu_{R_{\mathfrak p}}(M_{\mathfrak p})>i\}
=V(\operatorname{Fitt}_i(M)).
$$

They therefore give closed generator-rank strata, not merely a single support.

As a worked matrix example, let

$$
A=
\begin{pmatrix}
x&z\\
0&y
\end{pmatrix},
\qquad
M=\operatorname{coker}(A:R^2\to R^2).
$$

Then

$$
\operatorname{Fitt}_0(M)=(xy),
\qquad
\operatorname{Fitt}_1(M)=(x,y,z),
\qquad
\operatorname{Fitt}_2(M)=R.
$$

Thus $M$ is supported on $V(xy)$, and at a prime of that support it needs two generators precisely when the prime also contains $x,y,z$. The off-diagonal entry does not change the zeroth determinant, but it changes the higher generator stratum.

### 13.2 Annihilator bounds

Suppose $M$ can be generated by $q$ elements. Then

$$
\operatorname{Fitt}_0(M)
\subseteq\operatorname{Ann}_R(M),
\qquad
\operatorname{Ann}_R(M)^q
\subseteq\operatorname{Fitt}_0(M).
$$

For the first inclusion, a maximal minor of a presentation matrix annihilates its cokernel by the adjugate identity. For the second, let $a_1,\ldots,a_q\in\operatorname{Ann}M$. Multiplication by each $a_i$ sends each chosen generator into the relation module. Expanding the determinant of the resulting $q$ relation columns shows that $a_1\cdots a_q$ lies in the ideal of maximal minors. Such products generate $\operatorname{Ann}(M)^q$.

Consequently

$$
\sqrt{\operatorname{Fitt}_0(M)}
=\sqrt{\operatorname{Ann}(M)}.
$$

This radical equality is another proof that the two ideals define the same underlying closed subset. They generally define different closed subschemes.

For $M=R/(a)\oplus R/(b)$,

$$
\operatorname{Ann}M=(a)\cap(b),
\qquad
\operatorname{Fitt}_0(M)=(ab).
$$

The ideals can agree in a domain for some choices but differ in rings with common factors or nilpotents. For cyclic modules they always agree.

### 13.3 Full support versus faithfulness

A module is **faithful** if $\operatorname{Ann}_R(M)=0$. Every nonzero faithful finite module has

$$
\operatorname{Supp}M=\operatorname{Spec}R,
$$

but the converse says only that $\sqrt{\operatorname{Ann}M}$ is the nilradical. Full support does not detect nilpotent elements acting by zero.

The Fitting conditions fit between these notions as follows:

$$
M\text{ faithful}
\Longrightarrow
\operatorname{Fitt}_0(M)=0
\Longrightarrow
\operatorname{Supp}M=\operatorname{Spec}R.
$$

Neither converse holds over an arbitrary nonreduced ring. Let

$$
R=k[\epsilon]/(\epsilon^2),\qquad M=k=R/(\epsilon).
$$

Then $M$ has full support because $R$ has one prime, but

$$
\operatorname{Fitt}_0(M)=\operatorname{Ann}M=(\epsilon)\ne0.
$$

For

$$
N=k\oplus k,
$$

the direct-sum formula gives $\operatorname{Fitt}_0(N)=(\epsilon)^2=0$, while $\operatorname{Ann}N=(\epsilon)$. Thus vanishing zeroth Fitting ideal is still weaker than faithfulness.

If $R$ is reduced, the annihilator bound reverses the missing implication: $\operatorname{Fitt}_0(M)=0$ implies $\operatorname{Ann}(M)^q=0$, hence $\operatorname{Ann}(M)=0$. Therefore, for a finitely presented module over a reduced ring,

$$
M\text{ faithful}
\quad\Longleftrightarrow\quad
\operatorname{Fitt}_0(M)=0
\quad\Longleftrightarrow\quad
\operatorname{Supp}M=\operatorname{Spec}R.
$$

The last reverse implication uses reducedness too: full support makes the radical of the annihilator the nilradical, which is zero. For cyclic modules the first equivalence holds without reducedness because Fitting ideal and annihilator coincide, but full support can still fail to imply faithfulness in a nonreduced ring.

### 13.4 Scheme-theoretic support

The underlying support is a set of primes. A scheme-theoretic closed support requires an ideal. The annihilator defines the smallest closed subscheme through which the action of $R$ on $M$ factors. The zeroth Fitting ideal defines a generally thicker determinantal subscheme with the same underlying topological space.

It is therefore imprecise to call $\operatorname{Fitt}_0(M)$ “the annihilator of the support.” What is true is

$$
V(\operatorname{Fitt}_0(M))
=V(\operatorname{Ann}M)
=\operatorname{Supp}M.
$$

In arguments concerned only with components, radicals may suffice. In arguments measuring congruence length or nilpotent thickness, replacing one ideal by the other can change the answer.

## 14. Exact sequences, determinants, and numerical size

### 14.1 Fitting ideals in exact sequences

Fitting ideals are multiplicative on direct sums but only satisfy containments for general extensions.

If

$$
M'\longrightarrow M\longrightarrow M''\longrightarrow0
$$

is exact and the modules are finitely presented, then

$$
\operatorname{Fitt}_0(M')\operatorname{Fitt}_0(M'')
\subseteq\operatorname{Fitt}_0(M).
$$

A presentation of $M$ can be built from presentations of $M'$ and $M''$ using a block upper-triangular matrix. Products of maximal minors of the diagonal blocks occur among its maximal minors, proving the inclusion. If the sequence splits, the matrix is block diagonal and equality follows from the direct-sum formula.

Equality can also hold in important nonsplit cases, but it is not formal. For example, over a discrete valuation ring, lengths are additive in every short exact sequence, and the valuation formula of Section 14.3 forces equality of zeroth Fitting ideals for finite-length modules. Over a general ring, extension data can add determinantal relations, so only the inclusion is automatic.

There are broader formulas involving all higher Fitting ideals and the number of generators of one term. Their indexing depends on the precise presentation hypotheses. For patching, the safe operations are arbitrary base change, localization, direct-sum convolution, and the displayed zeroth-ideal containment.

### 14.2 Finite free resolutions and determinants

If $M$ has a square presentation

$$
R^n\xrightarrow{A}R^n\longrightarrow M\longrightarrow0,
$$

then

$$
\operatorname{Fitt}_0(M)=(\det A).
$$

The adjugate identity $\operatorname{adj}(A)A=(\det A)I_n$ explains directly why the determinant annihilates the cokernel. If $R$ is a domain and $M$ is torsion, a length-one finite free resolution necessarily has equal ranks after tensoring with the fraction field, so this square situation is natural.

For a longer finite free resolution

$$
0\to F_n\to\cdots\to F_1\xrightarrow{d_1}F_0\to M\to0,
$$

$\operatorname{Fitt}_0(M)$ is still computed from the maximal minors of $d_1$; later differentials impose the syzygies that make this presentation exact. One should not take an alternating product of determinants unless ranks, torsion hypotheses, and a determinant-line trivialization make that expression meaningful. Over a normal domain, perfect torsion modules lead to characteristic ideals through height-one localization, but that refinement is not needed here.

For a cyclic presentation, the determinant is simply the defining element. For a direct sum of cyclic torsion modules, block diagonality multiplies the defining elements. This is the elementary origin of determinant formulas for numerical size.

Consider the nonsquare presentation

$$
R^3\xrightarrow{
\begin{pmatrix}
a&b&0\\
0&c&d
\end{pmatrix}}
R^2\longrightarrow M\longrightarrow0.
$$

Then

$$
\operatorname{Fitt}_0(M)=(ac,ad,bd),
\qquad
\operatorname{Fitt}_1(M)=(a,b,c,d).
$$

There is no single determinant, yet maximal minors still detect the vanishing locus and entries detect where one generator suffices. Fitting ideals are the correct extension of determinant data to rectangular presentations.

### 14.3 Modules over a discrete valuation ring

Let $\mathcal O$ be a discrete valuation ring with uniformizer $\varpi$ and normalized valuation $v(\varpi)=1$. Every finite-length $\mathcal O$-module has an invariant-factor decomposition

$$
M\simeq\bigoplus_{j=1}^r\mathcal O/(\varpi^{a_j}),
\qquad a_j\ge1.
$$

The direct-sum and cyclic formulas give

$$
\operatorname{Fitt}_0^{\mathcal O}(M)
=(\varpi^{a_1+\cdots+a_r}),
$$

and therefore

$$
v(\operatorname{Fitt}_0(M))
=\operatorname{length}_{\mathcal O}M.
$$

Here $v((a))$ means $v(a)$ for a nonzero principal ideal; this is independent of the chosen generator because units have valuation zero. The zeroth Fitting ideal of a nonzero finite-length module is nonzero, so the notation is unambiguous.

If $M$ has a square presentation matrix $A$ with nonzero determinant, Smith normal form gives the same formula:

$$
\operatorname{length}_{\mathcal O}M=v(\det A).
$$

This is a precise numerical-size interpretation. It relies on the principal ideal structure of a discrete valuation ring and on finite length. Over a higher-dimensional local ring, a single valuation cannot recover module length, and over a nondomain a determinant may be a zerodivisor.

### 14.4 Congruence modules

A congruence module arises when two integral systems agree after passing to a common generic object but fail to split integrally. At the elementary algebraic level, let $L$ be a finite free $\mathcal O$-lattice inside a vector space over the fraction field, and let $L_1,L_2$ be sublattices whose generic fibers give complementary pieces. A quotient such as

$$
C=L/(L_1+L_2)
$$

is finite length when the sum has full rank. It measures the integral overlap between the two pieces.

The ideal $\operatorname{Fitt}_0^{\mathcal O}(C)$ then records exactly the total congruence length. If a basis turns the inclusion $L_1+L_2\hookrightarrow L$ into a square matrix $A$, then

$$
\operatorname{Fitt}_0(C)=(\det A),
\qquad
\operatorname{length}_{\mathcal O}C=v(\det A).
$$

This language explains why zeroth Fitting ideals occur in numerical comparison arguments. We stop at the size mechanism. Criteria comparing a congruence module to a cotangent module and deducing an isomorphism of rings belong to Book 71.

## 15. Finite local maps and freeness criteria

### 15.1 Depth and dimension across a finite map

Let $(A,\mathfrak m)\to(B,\mathfrak n)$ be a finite local homomorphism of Noetherian local rings, and let $M$ be a nonzero finite $B$-module. Since $B/\mathfrak mB$ is a finite local algebra over $A/\mathfrak m$, its maximal ideal is nilpotent. Hence

$$
\sqrt{\mathfrak mB}=\mathfrak n.
$$

Choose generators of $\mathfrak m$. Their Koszul complex on $M$ is the same complex whether the scalars are viewed through $A$ or through $B$, and they generate $\mathfrak mB$ after extension. The Koszul depth formula therefore gives

$$
\operatorname{depth}_AM
=\operatorname{depth}_{\mathfrak mB}^B(M).
$$

Depth in an ideal depends only on its radical for finite modules, by the Ext characterization or the Koszul formula. Therefore

$$
\operatorname{depth}_AM
=\operatorname{depth}_{\mathfrak mB}M
=\operatorname{depth}_BM.
$$

Here the left side regards $M$ as an $A$-module. This equality does **not** say $\operatorname{depth}A=\operatorname{depth}B$. It compares the depth of the same module under two actions.

Likewise $B/\operatorname{Ann}_B(M)$ is finite and integral over the injected ring $A/\operatorname{Ann}_A(M)$. Lying over, going up, and incomparability identify the lengths of prime chains in the two supports and give

$$
\dim_AM=\dim_BM.
$$

For $M=B$ this yields

$$
\dim B=\dim(A/\operatorname{Ann}_AB)
=\dim(A/\ker(A\to B)).
$$

Thus a finite map can lower dimension through its kernel. If $B$ is faithful as an $A$-module, the map is injective and dimensions agree. If $B$ is finite flat and nonzero, it is finite free over the local ring $A$, hence faithful; then

$$
\operatorname{depth}B=\operatorname{depth}A,
\qquad
\dim B=\dim A.
$$

Finite locality is essential. The quotient map

$$
k[[x,y]]\longrightarrow k[[x,y]]/(x)
$$

is finite local, but its kernel lowers dimension from two to one; the target is not faithful over the source. At the other extreme,

$$
k[[t^2,t^3]]\longrightarrow k[[t]]
$$

is finite, local, and injective. Both rings have dimension one, but the source is singular and the target is regular. Finiteness and equal dimension do not force an isomorphism or equality of embedding dimensions.

### 15.2 Miracle freeness over a regular source

The preceding comparison combines with Auslander--Buchsbaum to give the basic patching-shaped freeness criterion.

**Theorem (miracle freeness).** Let $A\to B$ be a finite local map with $A$ regular local of dimension $d$. Let $M$ be a nonzero finite $B$-module. If

$$
\operatorname{depth}_BM=d,
$$

then $M$ is finite free as an $A$-module.

**Proof.** Finiteness over $B$ and finiteness of $B$ over $A$ make $M$ finite over $A$. The finite-map depth comparison gives $\operatorname{depth}_AM=d=\operatorname{depth}A$. Since $A$ is regular, $M$ has finite projective dimension over $A$. Auslander--Buchsbaum gives $\operatorname{pd}_AM=0$, and finite projective modules over local rings are free. $\square$

The depth equality forces $\dim_AM=d$, so $\operatorname{Ann}_A(M)$ has height zero. Freeness proves more: a nonzero free $A$-module is faithful, hence $\operatorname{Ann}_A(M)=0$. The conclusion concerns the source action. It does not by itself make $M$ faithful or free as a $B$-module.

For example, a finite local algebra $B$ can contain a nilpotent ideal that acts trivially on an $A$-free quotient module. Source freeness sees no such hidden part of the $B$-action. Faithfulness over the acting ring must be proved separately, often through an annihilator or a reducedness-plus-Fitting argument.

When faithfulness is available, source freeness can constrain the ring action sharply. If $M$ is $A$-free of rank $r$ and faithful over $B$, the action gives an injection

$$
B\hookrightarrow\operatorname{End}_A(M)\simeq M_r(A).
$$

For $r=1$, this already forces $A\to B$ to be an isomorphism. Indeed the injection $B\hookrightarrow A$ obtained from the action is a left inverse to the structural inclusion $A\hookrightarrow B$, and injectivity shows that every $b\in B$ equals the image of its scalar action in $A$. For larger rank this conclusion is false: many finite $A$-algebras act faithfully on free modules of rank greater than one.

There is another useful special case. If $A\twoheadrightarrow B$ is surjective and $M$ is both nonzero $A$-free and a faithful $B$-module, then the kernel of $A\to B$ annihilates $M$. A nonzero free $A$-module is faithful, so the kernel is zero and the surjection is an isomorphism. Here ring equality is forced by combining source freeness, target faithfulness, and a pre-existing surjection; none of the three alone is sufficient.

### 15.3 Maximal Cohen--Macaulay does not mean free

Suppose $B$ is Cohen--Macaulay of dimension $d$ and $M$ is maximal Cohen--Macaulay. Then $\operatorname{depth}_BM=d$, but $M$ need not be $B$-free. The module $B/(y)$ over

$$
B=k[[x,y]]/(xy)
$$

is the basic example. It has depth one and infinite projective dimension.

Nor does faithfulness repair the implication. The module

$$
B\oplus B/(y)
$$

is faithful and maximal Cohen--Macaulay, but not free. Its minimal resolution contains the infinite periodic tail of the second summand.

Over a complete intersection of positive codimension, such periodic or eventually structured resolutions are typical rather than exceptional. The ring controls their complexity, but complete intersection alone does not terminate them. Consequently any statement that a maximal Cohen--Macaulay module over a complete intersection is free must include an additional hypothesis.

### 15.4 Finite projective dimension restores freeness

The exact additional hypothesis is finite projective dimension.

**Proposition.** Let $B$ be a Cohen--Macaulay local ring, including in particular a complete-intersection local ring. If a nonzero finite $B$-module $M$ is maximal Cohen--Macaulay and has finite projective dimension over $B$, then $M$ is free.

**Proof.** Cohen--Macaulayness gives

$$
\operatorname{depth}B=\dim B=\operatorname{depth}_BM.
$$

Auslander--Buchsbaum gives $\operatorname{pd}_BM=0$. Local finite projectivity is freeness. $\square$

If $B$ is regular, finite projective dimension is automatic for every finite module, recovering Chapter 9. If $B$ is a singular complete intersection, it is a genuine extra condition.

There is a relative version useful for finite maps. If $A\to B$ is finite local, $A$ is regular, and $M$ is maximal Cohen--Macaulay over $B$ with $\dim B=\dim A$, then miracle freeness makes $M$ free over $A$. To conclude $B$-freeness one still needs finite projective dimension over $B$; to conclude faithfulness over $B$ one needs $\operatorname{Ann}_B(M)=0$, or a sufficient substitute such as $B$ reduced together with $\operatorname{Fitt}_0^B(M)=0$.

## 16. The patching dictionary

### 16.1 Reading depth data

Patching eventually produces a large finite module over one or more local rings. Before drawing conclusions, identify exactly which ring acts and over which ring depth is computed.

For a finite local map $A\to B$ and finite $B$-module $M$,

$$
\operatorname{depth}_AM=\operatorname{depth}_BM,
\qquad
\dim_AM=\dim_BM.
$$

If $A$ is regular of dimension $d$ and the common depth is $d$, then $M$ is $A$-free. This is a resolution theorem, not a support theorem. It uses finite generation, the finite local map, regularity of $A$, and Auslander--Buchsbaum.

If only $\operatorname{depth}_BM=\dim B$ is known, then $M$ is maximal Cohen--Macaulay over $B$. That conclusion ensures good dimension cutting and unmixed support, but it does not imply $B$-freeness. A separate finite-projective-dimension input is required unless $B$ is regular.

### 16.2 Reading complete-intersection data

A minimal presentation

$$
B\simeq Q/(f_1,\ldots,f_c)
$$

from a regular local ring proves that $B$ is complete intersection only when the $f_i$ form a regular sequence. Equality between the number of equations and the height of the kernel proves this regularity because $Q$ is Cohen--Macaulay. A raw relation count without a height equality does not.

Once the presentation is complete intersection,

$$
\operatorname{codim}B=c,
\qquad
\dim B=\dim Q-c,
\qquad
I/I^2\simeq B^c.
$$

The property survives completion and quotient by a regular element. It survives flat presentation base change when the new ambient ring is regular, and it survives completed tensor products under the field or flat coefficient-ring hypotheses of Chapter 11.

These facts control ring structure, but they still do not make all maximal-depth modules free. Complete intersections are Cohen--Macaulay; they are regular only in codimension zero.

### 16.3 Reading Fitting and support data

For a finite module $M$ over a Noetherian ring $B$,

$$
\operatorname{Supp}_B(M)=V(\operatorname{Fitt}_0^B(M))
=V(\operatorname{Ann}_B(M)).
$$

Thus $\operatorname{Fitt}_0(M)$ controls the underlying support and commutes with localization and arbitrary base change. It also retains multiplicity information invisible to the radical, especially over a discrete valuation ring where its valuation equals length.

The implications governing faithfulness are

$$
\begin{array}{c}
M\text{ faithful}\\
\Downarrow\\
\operatorname{Fitt}_0(M)=0\\
\Downarrow\\
\operatorname{Supp}M=\operatorname{Spec}B.
\end{array}
$$

When $B$ is reduced, both reverse implications hold, so all three conditions are equivalent. For a cyclic module the first reverse implication holds even without reducedness, because its zeroth Fitting ideal equals its annihilator. Full support alone over a nonreduced ring allows a nilpotent annihilator. Scheme-theoretic conclusions therefore require the actual annihilator or an argument eliminating nilpotents.

### 16.4 A reliable implication chain

The following workflow isolates the hypotheses usually distributed across a patching argument.

1. **Fix the rings.** Specify a finite local map $A\to B$, the common residue behavior, completeness if completed products are used, and whether codimension is absolute or relative.
2. **Obtain a depth bound.** Use regular sequences, the depth lemma, or Ext vanishing to prove a statement about the finite module $M$, always naming the acting ring.
3. **Compare across the finite map.** Replace $\operatorname{depth}_BM$ by $\operatorname{depth}_AM$ only because $\sqrt{\mathfrak m_AB}=\mathfrak m_B$.
4. **Force source freeness.** If $A$ is regular and the depth reaches $\dim A$, finite global dimension and Auslander--Buchsbaum make $M$ free over $A$.
5. **Analyze the target ring separately.** A height-equals-relations argument in a regular presentation can make $B$ complete intersection. Source freeness of $M$ does not itself do so.
6. **Determine support.** Compute or bound $\operatorname{Fitt}_0^B(M)$. Vanishing gives full support; over a reduced $B$ it gives faithfulness.
7. **Eliminate hidden annihilators.** If $B$ is not known reduced, prove $\operatorname{Ann}_B(M)=0$ directly or supply another argument that kills its nilpotent part.
8. **Claim target freeness only with homological input.** Maximal Cohen--Macaulay plus finite projective dimension over $B$ gives $B$-freeness. Without the latter, singular complete intersections have counterexamples.

If the comparison map $A\to B$ is already known to be surjective, steps 4 and 7 can finish a ring comparison: an $A$-free nonzero module that is faithful over $B$ kills the kernel. If the module has $A$-rank one, faithfulness forces the same conclusion even for a finite map not initially known surjective. These are structural consequences of the dictionary, not the numerical criteria reserved for the next volume.

This chain separates three logically different outcomes:

$$
\begin{array}{c|c}
\text{desired outcome}&\text{typical sufficient mechanism}\\ \hline
A\text{-freeness of }M&A\text{ regular and }\operatorname{depth}_AM=\dim A\\
B\text{-faithfulness of }M&\operatorname{Ann}_B(M)=0\\
B\text{-freeness of }M&B\text{ Cohen--Macaulay, }M\text{ maximal CM, }\operatorname{pd}_BM<\infty\\
B\text{ complete intersection}&\text{regular presentation with height = minimal relation count}.
\end{array}
$$

None of the four rows can simply be substituted for another. Their power in patching comes from proving them simultaneously from different inputs.

### 16.5 Conclusion

Depth begins with a simple question: how many elements can act injectively, one after another, on a finite module? The Koszul complex turns that successive question into homology, and Ext turns it into an invariant independent of all choices. Exact sequences then obey the three inequalities of the depth lemma, while localization and completion transport the invariant under the operations local algebra actually uses.

Minimal free resolutions reveal the second face of depth. Their Betti numbers are Tor dimensions, their length is projective dimension, and their interaction with Koszul homology proves the Auslander--Buchsbaum formula. The formula pinpoints the freeness mechanism: maximal possible depth forces freeness only when projective dimension is finite. Regular local rings provide that finiteness for every finite module; singular complete intersections do not.

Complete intersections are precisely the regular-local quotients whose defining equations form a regular sequence. Their codimension is intrinsic in a minimal presentation, their conormal module is free of the expected rank, and their stability under completion, regular quotients, suitable flat base change, and carefully controlled completed tensor products makes them compatible with deformation-theoretic constructions. They are Cohen--Macaulay and unmixed, but need not be reduced or regular.

Fitting ideals supply the determinantal counterpart. They are independent of presentation, commute with arbitrary base change, stratify generator number, and recover support through

$$
\operatorname{Supp}(M)=V(\operatorname{Fitt}_0(M)).
$$

Their relation to annihilators explains exactly what support does and does not prove. Over a discrete valuation ring, the zeroth Fitting ideal becomes a numerical size through length and determinants; over a general local ring, it retains scheme-theoretic information that a radical discards.

The resulting patching dictionary is deliberately conditional. Depth over a regular source can force source freeness. Finite projective dimension can turn maximal Cohen--Macaulay into target freeness. Annihilators or reduced Fitting criteria can force faithfulness. Height and regular-sequence arguments can force complete-intersection structure. The numerical comparisons that make several of these conclusions occur at once are the next subject; the present volume supplies the algebra that makes every step in that comparison legitimate.
