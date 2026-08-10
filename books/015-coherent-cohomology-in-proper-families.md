# Coherent Cohomology in Proper Families

## Contents

1. [The questions asked by a family](#1-the-questions-asked-by-a-family)
   - [Fibers are not the whole family](#11-fibers-are-not-the-whole-family)
   - [Standing language and hypotheses](#12-standing-language-and-hypotheses)
   - [The base-change map](#13-the-base-change-map)
   - [Three warnings](#14-three-warnings)
2. [Finite complexes behind projective cohomology](#2-finite-complexes-behind-projective-cohomology)
   - [Why one complex should govern every fiber](#21-why-one-complex-should-govern-every-fiber)
   - [The projective-space calculation](#22-the-projective-space-calculation)
   - [Finite-complex theorem](#23-finite-complex-theorem)
   - [From projective to proper](#24-from-projective-to-proper)
3. [Finiteness for proper morphisms](#3-finiteness-for-proper-morphisms)
   - [Coherence of higher direct images](#31-coherence-of-higher-direct-images)
   - [Vanishing bounds and cohomological dimension](#32-vanishing-bounds-and-cohomological-dimension)
   - [Projection and composition](#33-projection-and-composition)
   - [Why properness and coherence matter](#34-why-properness-and-coherence-matter)
4. [Upper semicontinuity](#4-upper-semicontinuity)
   - [The rank of fiber cohomology](#41-the-rank-of-fiber-cohomology)
   - [The semicontinuity theorem](#42-the-semicontinuity-theorem)
   - [Euler characteristics in flat families](#43-euler-characteristics-in-flat-families)
   - [Jumping examples](#44-jumping-examples)
5. [Cohomology and base change](#5-cohomology-and-base-change)
   - [A local normal form](#51-a-local-normal-form)
   - [The exact criterion](#52-the-exact-criterion)
   - [Flat and arbitrary change of base](#53-flat-and-arbitrary-change-of-base)
   - [Local freeness and constant fiber dimension](#54-local-freeness-and-constant-fiber-dimension)
   - [Curves as a two-degree case](#55-curves-as-a-two-degree-case)
6. [Flatness, Hilbert polynomials, and flattening](#6-flatness-hilbert-polynomials-and-flattening)
   - [The cohomological meaning of a Hilbert polynomial](#61-the-cohomological-meaning-of-a-hilbert-polynomial)
   - [Constancy and the converse](#62-constancy-and-the-converse)
   - [Flattening strata](#63-flattening-strata)
   - [Uniform generation and embeddings](#64-uniform-generation-and-embeddings)
7. [Formal functions](#7-formal-functions)
   - [Infinitesimal neighborhoods remember completion](#71-infinitesimal-neighborhoods-remember-completion)
   - [The theorem on formal functions](#72-the-theorem-on-formal-functions)
   - [Proof by Artin--Rees and effacement](#73-proof-by-artin--rees-and-effacement)
   - [Consequences and limitations](#74-consequences-and-limitations)
8. [Completion and coherent passages](#8-completion-and-coherent-passages)
   - [Ordinary and derived completion](#81-ordinary-and-derived-completion)
   - [Completed base change](#82-completed-base-change)
   - [Lifting sections through thickenings](#83-lifting-sections-through-thickenings)
   - [What is not yet algebraization](#84-what-is-not-yet-algebraization)
9. [Duality interfaces in relative dimension one](#9-duality-interfaces-in-relative-dimension-one)
   - [Trace and the relative dualizing line](#91-trace-and-the-relative-dualizing-line)
   - [Perfect pairings for smooth proper curves](#92-perfect-pairings-for-smooth-proper-curves)
   - [Base change and the Hodge bundle](#93-base-change-and-the-hodge-bundle)
   - [Nodal and Gorenstein curves](#94-nodal-and-gorenstein-curves)
10. [Proper curves and Picard representability](#10-proper-curves-and-picard-representability)
   - [The relative Picard functor](#101-the-relative-picard-functor)
   - [Divisors provide finite-dimensional charts](#102-divisors-provide-finite-dimensional-charts)
   - [The Picard scheme of a smooth proper curve](#103-the-picard-scheme-of-a-smooth-proper-curve)
   - [Tangent spaces, smoothness, and the Jacobian](#104-tangent-spaces-smoothness-and-the-jacobian)
11. [Abelian schemes and their coherent cohomology](#11-abelian-schemes-and-their-coherent-cohomology)
   - [Invariant differentials](#111-invariant-differentials)
   - [The exterior algebra theorem](#112-the-exterior-algebra-theorem)
   - [The dual abelian scheme](#113-the-dual-abelian-scheme)
   - [Polarizations and base change](#114-polarizations-and-base-change)
12. [Hodge bundles in low-dimensional PEL families](#12-hodge-bundles-in-low-dimensional-pel-families)
   - [What is assumed and what is proved](#121-what-is-assumed-and-what-is-proved)
   - [Endomorphisms and decompositions](#122-endomorphisms-and-decompositions)
   - [Determinants, ranks, and bad primes](#123-determinants-ranks-and-bad-primes)
   - [Compactifications and boundary behavior](#124-compactifications-and-boundary-behavior)
13. [Integral modular forms as coherent sections](#13-integral-modular-forms-as-coherent-sections)
   - [The geometric definition](#131-the-geometric-definition)
   - [Finiteness and change of coefficients](#132-finiteness-and-change-of-coefficients)
   - [Cusp forms and the boundary](#133-cusp-forms-and-the-boundary)
   - [The exact base-change test](#134-the-exact-base-change-test)
14. [Representability consequences and their boundary](#14-representability-consequences-and-their-boundary)
   - [A coherent representability package](#141-a-coherent-representability-package)
   - [Curves, abelian schemes, and PEL data](#142-curves-abelian-schemes-and-pel-data)
   - [Failures when hypotheses are weakened](#143-failures-when-hypotheses-are-weakened)
15. [Synthesis](#15-synthesis)
   - [The chain of implications](#151-the-chain-of-implications)
   - [A theorem checklist for later use](#152-a-theorem-checklist-for-later-use)
   - [Conclusion](#153-conclusion)

## 1. The questions asked by a family

### 1.1 Fibers are not the whole family

A proper scheme over a field has finite-dimensional coherent cohomology. In a family, that familiar statement divides into several different questions. Are the cohomology groups of every fiber finite? Do their dimensions vary predictably? Is there a coherent sheaf on the base whose fiber is the cohomology of the geometric fiber? Does that sheaf survive extension of scalars? What can infinitesimal neighborhoods of one fiber tell us about the completed family?

The answers are related but not interchangeable. A single finite complex on the base is the organizing object. Its cohomology gives higher direct images; tensoring it with a residue field gives fiber cohomology; ranks of its differentials give semicontinuity; tensoring with quotient rings gives infinitesimal cohomology; and completion turns the resulting inverse system into the theorem on formal functions. The point of this book is to build that complex, explain exactly when it exists, and then extract each geometric consequence without hiding a flatness or finiteness assumption.

There is also a moduli-theoretic reason for caring. A line bundle in a proper family is controlled infinitesimally by $H^1(mathcal O)$ and obstructed in $H^2(mathcal O)$. Differentials on an abelian scheme form a vector bundle only because coherent base change works. Integral modular forms are sections of powers of such a bundle; their finiteness and reduction properties are therefore cohomological statements. Thus coherent cohomology is not an invariant added after a family has been constructed. It is one of the mechanisms that makes families representable and arithmetic sections controllable.

### 1.2 Standing language and hypotheses

All schemes are schemes in the ordinary sense. A scheme is **locally noetherian** when it has an affine cover by spectra of noetherian rings, and **noetherian** when it is also quasi-compact. A morphism is **proper** when it is separated, of finite type, and universally closed. Over a locally noetherian base, a finite-type morphism is finitely presented. We nevertheless say “finitely presented” when that property is the one used, especially in base-change statements that remain meaningful beyond noetherian schemes.

For $f:X\to S$ and a quasi-coherent sheaf $\mathcal F$, write

$$
R^if_*\mathcal F
$$

for the $i$th higher direct image in the Zariski topology. Its restriction to an open $U\subseteq S$ is the sheaf associated with $H^i(X_U,\mathcal F|_{X_U})$ when $U$ is affine and the usual comparison hypotheses hold. For a point $s\in S$, write

$$
X_s=X\times_S\operatorname{Spec}\kappa(s),
\qquad \mathcal F_s=\mathcal F\otimes_{\mathcal O_S}\kappa(s).
$$

The last tensor is ordinary when $\mathcal F$ is flat over $S$. Without flatness, the correct fiber of a complex uses derived tensor, and Tor terms can alter cohomology.

A coherent sheaf $\mathcal F$ on $X$ is **flat over $S$** if every stalk $\mathcal F_x$ is flat over $\mathcal O_{S,f(x)}$. This is not the same as being locally free on $X$. For example, the structure sheaf of any flat finitely presented family is flat over the base even when the total space is singular.

The main finiteness and formal-functions theorems use a proper morphism between locally noetherian schemes and a coherent sheaf. The sharp semicontinuity and exact base-change criteria add flatness of $\mathcal F$ over $S$. Whenever we pass to an arbitrary nonnoetherian base, we explicitly replace coherence by finite presentation and add the needed perfectness or boundedness hypothesis.

### 1.3 The base-change map

Given a cartesian square

$$
\begin{array}{ccc}
X_T&\xrightarrow{g'}&X\\
\downarrow f_T&&\downarrow f\\
T&\xrightarrow{g}&S,
\end{array}
$$

adjunction gives a canonical morphism

$$
Lg^*Rf_*\mathcal F\longrightarrow
Rf_{T*}Lg'^*\mathcal F.
$$

Taking degree $i$ and suppressing higher Tor produces, under flatness in the appropriate place, the familiar map

$$
g^*R^if_*\mathcal F\longrightarrow
R^if_{T*}\mathcal F_T.
$$

For $T=\operatorname{Spec}\kappa(s)$ it induces

$$
\beta_s^i:(R^if_*\mathcal F)\otimes\kappa(s)longrightarrow
H^i(X_s,\mathcal F_s).
$$

The map always exists in its derived form. Properness makes both sides finite; flatness and vanishing determine when the displayed underived map is an isomorphism. This separation between existence and invertibility will prevent several common mistakes.

### 1.4 Three warnings

First, properness cannot be replaced by “all fibers are proper.” A family can fail to be universally closed even if its visible fibers look complete, and then sections may escape in a varying direction. Finiteness is a global assertion about the map.

Second, finite-dimensional fibers do not imply that $R^if_*\mathcal F$ is locally free. On an elliptic curve $E$ over a field, let $\mathcal P$ be a Poincare line bundle on $E\times E$, with the second factor as base. For a nontrivial degree-zero line bundle $L$, both $H^0(E,L)$ and $H^1(E,L)$ vanish; at the identity, both dimensions are one. The higher direct images therefore have torsion concentrated at the identity rather than constant rank.

Third, an isomorphism after every residue-field extension need not by itself give arbitrary base change unless the relevant objects are finitely presented and Tor is controlled. Nilpotent thickenings see relations invisible at points. Exact criteria must be formulated using a finite complex, not only geometric fibers.

## 2. Finite complexes behind projective cohomology

### 2.1 Why one complex should govern every fiber

Let $A$ be noetherian, $X$ projective over $A$, and $\mathcal F$ coherent and $A$-flat. One wants a bounded complex $K^\bullet$ of finite free $A$-modules such that for every $A$-module $M$,

$$
H^i(K^\bullet\otimes_A M)
\simeq H^i(X,\mathcal F\otimes_A M).
$$

This is stronger than merely saying each cohomology module is finite. It says all coefficient changes are governed by the same matrices. The strength is exactly what semicontinuity and base change require.

The construction begins with a projective embedding and the standard affine cover. A Cech complex directly computes cohomology because finite intersections are affine, but its terms are generally large localizations, not finite $A$-modules. Positive twists and finite resolutions replace that large complex, in any fixed cohomological range, by a bounded finite one. Flatness over $A$ ensures that tensoring with $M$ preserves the resolutions used in this replacement.

### 2.2 The projective-space calculation

On $\mathbf P^r_A$, cover by $D_+(x_0),\ldots,D_+(x_r)$. The alternating Cech complex of $\mathcal O(n)$ splits into subcomplexes indexed by Laurent monomials. A monomial whose negative exponents occur in a proper nonempty subset of the variables contributes a simplex complex and is acyclic. The survivors give

$$
H^q(\mathbf P^r_A,\mathcal O(n))=0
\quad(0<q<r),
$$

and

$$
H^0(\mathbf P^r_A,\mathcal O(n))
=A[x_0,\ldots,x_r]_n\quad(n\geq0).
$$

Top cohomology is generated by monomials in which every exponent is negative; in particular it is finite free in every degree. The entire calculation commutes with tensoring $A\to B$, because its monomial summands and differentials are defined over the integers.

If $i:X\hookrightarrow\mathbf P^r_A$ is closed, then $H^q(X,\mathcal F)=H^q(\mathbf P^r_A,i_*\mathcal F)$. A coherent sheaf on projective space has, after choosing sufficiently many twists, a finite beginning of a resolution by finite sums of $\mathcal O(-n)$. To compute degrees at most $N$, continue the resolution through $N+r+1$ steps. The unused tail contributes only above the range, because projective space has cohomological dimension $r$. Replacing every twist by its explicit Cech complex yields a bounded double complex of finite free $A$-modules in the required range.

### 2.3 Finite-complex theorem

**Finite-complex theorem.** Let $A$ be noetherian, let $f:X\to\operatorname{Spec}A$ be projective, and let $\mathcal F$ be coherent and flat over $A$. There is a bounded complex $K^\bullet$ of finite free $A$-modules, concentrated in degrees $0$ through some fixed bound after harmless acyclic summands are removed, and functorial isomorphisms

$$
H^i(K^\bullet\otimes_A M)
\simeq H^i(X,\mathcal F\otimes_A M)
$$

for every $A$-module $M$ and every $i$. On an open neighborhood of any point of a locally noetherian base, the analogous statement holds for a projective finitely presented morphism.

**Proof.** Embed $X$ into projective space. Choose a finite graded presentation of the module corresponding to $i_*\mathcal F$ and successively resolve its kernels by finite sums of graded free modules. Sheafification gives a resolution by sums of twists. Since the standard Cech cover is acyclic for quasi-coherent sheaves, the total Cech complex computes cohomology. The projective-space calculation replaces the terms outside a finite strip by acyclic finite complexes. Truncate after more than $r$ syzygies; dimension shifting shows that the remaining tail has no effect in any degree.

Every construction so far commutes with tensoring if the sheaf resolution stays exact. The $A$-flatness of $\mathcal F$, together with flatness of the twists, makes each successive kernel $A$-flat. Hence tensoring by an arbitrary $M$ preserves the resolution. The resulting bounded complex has finite flat terms. Over a noetherian ring, finitely presented flat modules are projective; after restricting to an affine neighborhood they are free. Adding finite contractible summands aligns the local complexes and gives the stated $K^\bullet$. The same argument on affine opens of the base proves the local assertion. $\square$

The theorem is often called a theorem of finite presentation for cohomology. Its decisive feature is universality in $M$. Without $A$-flatness of $\mathcal F$, one still obtains a bounded finite model for derived coefficient change, but ordinary tensor with $\mathcal F$ no longer describes every fiber.

### 2.4 From projective to proper

Not every proper morphism is projective. Finiteness must therefore be detached from the chosen embedding. The bridge is a projective modification and noetherian induction.

**Proper reduction lemma.** Let $f:X\to S$ be proper with $S$ noetherian. There is a proper surjection $p:X'\to X$ with $X'\to S$ projective, and an ideal $\mathcal J\subseteq\mathcal O_X$ whose vanishing has strictly smaller support such that

$$
\mathcal J\mathcal F\longrightarrow
p_*p^*(\mathcal J\mathcal F)
$$

is injective for every coherent $\mathcal F$ after replacing $\mathcal J$ by a sufficiently high power.

**Proof strategy.** A projective modification exists by taking the closure of a quasi-projective dense open and then applying the graph construction. Over that dense open, $p$ is an isomorphism. The kernel of $\mathcal F\to p_*p^*\mathcal F$ is therefore supported on the complement. Multiplying by a power of the ideal of the complement kills the kernel, since a coherent module supported on a closed subset is annihilated by a power of its defining ideal. The resulting map is injective. $\square$

Its cokernel and $\mathcal F/\mathcal J\mathcal F$ are supported on a smaller closed subset. The map $p$ may be chosen projective, so its higher direct images of coherent sheaves are coherent by the projective case. The spectral sequence

$$
H^a(X,R^bp_*\mathcal G)\Longrightarrow H^{a+b}(X',\mathcal G)
$$

then compares cohomology upstairs with cohomology of these sheaves downstairs. For $b>0$ they vanish over the dense locus where $p$ is an isomorphism, hence have smaller support. Thus an exact-sequence argument reduces statements about $\mathcal F$ to the projective composite $X'\to S$ and cases with smaller support. Noetherian induction terminates. This device proves coherence of proper pushforwards, but it does not generally produce the universal finite-free complex of Section 2.3. For that stronger conclusion one uses projectivity, or separately assumes that the derived pushforward is perfect over the base.

## 3. Finiteness for proper morphisms

### 3.1 Coherence of higher direct images

**Proper finiteness theorem.** Let $f:X\to S$ be a proper morphism of locally noetherian schemes and let $\mathcal F$ be coherent on $X$. Then $R^if_*\mathcal F$ is coherent for every $i\geq0$. If $S=\operatorname{Spec}A$ is noetherian, each $H^i(X,\mathcal F)$ is a finite $A$-module.

**Proof.** The assertion is local on $S$, so take an affine noetherian base. In the projective case, resolve $i_*\mathcal F$ on projective space far enough by finite sums of twists. The Cech calculation makes the cohomology of each twist finite over $A$; repeated long exact sequences then make $H^i(X,\mathcal F)$ finite.

For a general proper $X$, apply the proper reduction lemma. The projective sheaf $p^*(\mathcal J\mathcal F)$ has finite cohomology. The comparison with $\mathcal J\mathcal F$ has kernel and cokernel supported on a smaller closed subset; their finiteness follows by noetherian induction. The exact sequences

$$
0\to\mathcal J\mathcal F\to\mathcal F\to
\mathcal F/\mathcal J\mathcal F\to0
$$

and the corresponding sequence involving $p_*p^*(\mathcal J\mathcal F)$ transfer finiteness to $\mathcal F$. Sheafifying the finite modules on affine opens gives coherence, and localization compatibility makes the local sheaves agree. $\square$

Proper finiteness is the coherent analogue of compactness. It says that infinitely many local sections and cocycles collapse to finitely many parameters over the base.

### 3.2 Vanishing bounds and cohomological dimension

If $X$ is noetherian of dimension $d$, then

$$
H^i(X,\mathcal F)=0\quad(i>d)
$$

for every quasi-coherent $\mathcal F$. One proof chooses an affine open containing every generic point, whose complement has smaller dimension. Cohomology with support and induction reduce the degree by one at each passage to the complement. For a projective embedding into $\mathbf P^r_S$, the standard affine cover gives the cruder relative bound $R^if_*\mathcal F=0$ for $i>r$.

For a proper morphism whose fibers have dimension at most $d$, one obtains $R^if_*\mathcal F=0$ for $i>d$ under the usual noetherian hypotheses. Indeed, if a nonzero coherent $R^if_*\mathcal F$ existed, choose a point in its support where base change can be tested after a suitable flat replacement and specialization. Fiber cohomology above dimension $d$ vanishes, contradicting the minimal-degree choice in the resulting spectral sequence. Equivalently, the noetherian-induction proof of finiteness can be refined by relative dimension.

For a proper curve, only $R^0$ and $R^1$ occur. For an abelian scheme of relative dimension $g$, only degrees $0$ through $g$ occur. These short ranges are what make the later applications especially exact.

### 3.3 Projection and composition

Let $f:X\to S$ be proper, $\mathcal F$ coherent, and $\mathcal E$ finite locally free on $S$. The projection formula gives

$$
R^if_*(\mathcal F\otimes f^*\mathcal E)
\simeq R^if_*\mathcal F\otimes\mathcal E.
$$

To prove it, trivialize $\mathcal E$ locally. Both sides then become a finite direct sum of $R^if_*\mathcal F$, and the natural map is the identity under this description. The local isomorphisms glue by naturality.

For proper maps $X\xrightarrow fY\xrightarrow hS$, the truncation filtration of the composite yields

$$
E_2^{p,q}=R^ph_*(R^qf_*\mathcal F)
\Longrightarrow R^{p+q}(h\circ f)_*\mathcal F.
$$

Every term is coherent by proper finiteness, and the sequence has only finitely many terms on each diagonal. This is the precise derived-to-coherent passage: bounded coherent cohomology sheaves, filtered by truncations, recover the coherent cohomology of the composite. Degeneration would identify graded pieces, not canonically split the target.

### 3.4 Why properness and coherence matter

For $j:\mathbf A^1_k\to\operatorname{Spec}k$, the sheaf $j_*\mathcal O$ has global sections $k[t]$, infinite-dimensional over $k$. Thus finite type without properness does not give finite cohomology.

Even on a proper scheme, a noncoherent quasi-coherent sheaf can have infinite-dimensional global sections. On $\mathbf P^1_k$, the direct sum $\bigoplus_{n\geq0}\mathcal O$ has an infinite-dimensional space of sections. Coherence supplies finite generation; properness prevents those generators from proliferating at infinity.

Noetherianity is also doing real work. It makes submodules of finite modules finite, makes coherent support admit induction, and supplies Artin--Rees later. There are useful finitely presented versions over more general bases, but they require explicit pseudo-coherence and perfectness assumptions rather than the word “coherent” alone.

## 4. Upper semicontinuity

### 4.1 The rank of fiber cohomology

Let $K^\bullet$ be a bounded complex of finite free modules over a ring $A$. At a point $s\in\operatorname{Spec}A$,

$$
\dim_{\kappa(s)}H^i(K^\bullet\otimes\kappa(s))
=\operatorname{rank}K^i-operatorname{rank}_s d^{i-1}
-\operatorname{rank}_s d^i.
$$

The rank of a matrix is at least $r$ exactly where one of its $r\times r$ minors is nonzero, an open condition. Therefore matrix rank is lower semicontinuous. The negative of each adjacent rank is upper semicontinuous, so the displayed cohomology dimension is upper semicontinuous.

This elementary observation contains the geometry: specialization can make a differential lose rank, creating cohomology, but it cannot make the differential gain rank at a special point. Fiber cohomology can jump upward on closed loci.

### 4.2 The semicontinuity theorem

**Semicontinuity theorem.** Let $f:X\to S$ be proper and finitely presented, with $S$ locally noetherian, and let $\mathcal F$ be coherent and flat over $S$. For every $i\geq0$, the function

$$
h^i_{\mathcal F}(s)=
\dim_{\kappa(s)}H^i(X_s,\mathcal F_s)
$$

is upper semicontinuous. Equivalently, for every integer $n$, the set

$$
\{s\in S:h^i_{\mathcal F}(s)\geq n\}
$$

is closed.

**Proof.** The claim is local on $S$. In the projective case, use the finite-complex theorem and the matrix-rank calculation. For a proper nonprojective family, the projective-modification induction of Section 2.4 can be performed compatibly with fibers after flattening the finitely many kernels and cokernels that occur. On each resulting locally closed stratum, a finite complex computes cohomology. The rank loci are closed on that stratum, and noetherian induction shows the same set is closed in $S$. Equivalently, the general finite-presentation theorem for proper cohomology supplies a bounded complex of finite flat modules in the fixed degree range, to which the matrix argument applies. $\square$

The flatness of $\mathcal F$ is indispensable to identify ordinary fiber restriction with tensoring the universal cohomology complex. Without it, derived fibers include Tor terms and the naive fiber dimensions need not obey this theorem.

### 4.3 Euler characteristics in flat families

Suppose the hypotheses of the theorem hold and the fibers have uniformly bounded dimension. Define

$$
\chi(X_s,\mathcal F_s)=
\sum_i(-1)^ih^i_{\mathcal F}(s).
$$

**Euler-characteristic theorem.** This integer is locally constant on $S$.

**Proof.** Locally, the finite complex $K^\bullet$ computes every fiber. Over a field, the Euler characteristic of its cohomology equals the alternating sum of the dimensions of its terms:

$$
\sum_i(-1)^i\dim H^i(K\otimes\kappa(s))
=\sum_i(-1)^i\operatorname{rank}K^i.
$$

The right side is constant on each connected open where the terms have fixed ranks. The proper reduction gives the same conclusion in the nonprojective case by additivity in exact sequences. $\square$

For a proper flat curve and a line bundle of fiberwise degree $d$, later Riemann--Roch identifies this constant as $d+1-g$. Here we need only the cohomological constancy, not that formula.

### 4.4 Jumping examples

Let $C$ be a smooth projective curve of positive genus. In a family of degree-zero line bundles parameterized by its Picard variety, the trivial bundle has a section while a general nontrivial bundle does not. Thus $h^0$ jumps upward at the origin. Upper semicontinuity predicts precisely this direction.

Flatness cannot be read from constant support. Let $A=k[\epsilon]/(\epsilon^2)$ and let $M=A/(\epsilon)$. There is only one topological point, so every pointwise dimension function is constant, but $M$ is not flat. Nilpotent test schemes reveal the missing relation. This is why flattening and base change must be scheme-theoretic rather than merely pointwise.

## 5. Cohomology and base change

### 5.1 A local normal form

The exact base-change criterion is linear algebra over a local ring. Let $(A,\mathfrak m,k)$ be local and $K^\bullet$ a bounded complex of finite free $A$-modules. Whenever some matrix entry of a differential is a unit, elementary row and column operations split off a contractible summand

$$
0\longrightarrow A\xrightarrow{1}A\longrightarrow0.
$$

Repeating this process writes

$$
K^\bullet\simeq K^\bullet_{\min}\oplus K^\bullet_{\mathrm{ctr}},
$$

where the second summand is contractible and every entry of every differential of the **minimal complex** $K_{\min}$ lies in $\mathfrak m$. Tensoring the minimal complex with $k$ kills all differentials, so

$$
H^i(K^\bullet\otimes k)=K^i_{\min}\otimes k.
$$

Consider the canonical map

$$
H^i(K^\bullet)\otimes k\longrightarrow H^i(K^\bullet\otimes k).
$$

It is surjective exactly when $d^i_{\min}=0$. Indeed, surjectivity says

$$
\ker d^i_{\min}+\mathfrak mK^i_{\min}=K^i_{\min};
$$

Nakayama's lemma then gives $\ker d^i_{\min}=K^i_{\min}$. Once $d^i_{\min}=0$, one has

$$
H^i(K_{\min})=\operatorname{coker}d^{i-1}_{\min}.
$$

This module is free precisely when $d^{i-1}_{\min}=0$: if the cokernel is free, its quotient map splits, making the image of $d^{i-1}$ a direct summand contained in $\mathfrak mK^i$; a direct summand contained there must vanish. Thus neighboring differentials encode both base change and local freeness.

### 5.2 The exact criterion

**Cohomology-and-base-change theorem.** Let $f:X\to S$ be proper and finitely presented, where $S$ is locally noetherian, and let $\mathcal F$ be coherent and flat over $S$. Fix $s\in S$ and $i\geq0$.

1. If

   $$
   \beta_s^i:(R^if_*\mathcal F)\otimes\kappa(s)
   \longrightarrow H^i(X_s,\mathcal F_s)
   $$

   is surjective, then after shrinking to a neighborhood $U$ of $s$, the degree-$i$ base-change map is an isomorphism for every morphism $T\to U$.

2. Assuming $\beta_s^i$ is surjective, the following are equivalent after shrinking around $s$:

   - $R^if_*\mathcal F$ is finite locally free;
   - $\beta_s^{i-1}$ is surjective, with the condition omitted when $i=0$.

3. If both adjacent conditions hold, then $R^if_*\mathcal F$ is finite locally free on $U$ and, for every morphism $T\to U$,

   $$
   (R^if_*\mathcal F)|_U\otimes_{\mathcal O_U}\mathcal O_T
   \xrightarrow{\sim}R^if_{T*}\mathcal F_T.
   $$

**Proof.** Work over the local ring at $s$ and use a finite free complex computing cohomology and coefficient change. By Section 5.1, surjectivity in degree $i$ says that the $i$th differential in a minimal model vanishes. Vanishing of a matrix persists after shrinking because it is an equality of finitely many functions. Then both $H^i(K)\otimes M$ and $H^i(K\otimes M)$ are the cokernel of $d^{i-1}\otimes M$ for every coefficient module $M$. Thus base change is an isomorphism in degree $i$.

Under this vanishing, $H^i(K)$ is locally free exactly when $d^{i-1}$ also vanishes in a minimal model. The latter is exactly surjectivity of base change in degree $i-1$. If both differentials vanish, $K$ has zero differential into and out of degree $i$, so formation of $H^i$ commutes with every tensor product. Sheafifying proves all three assertions. $\square$

The theorem is deliberately asymmetric: surjectivity in degree $i$ controls the outgoing differential, while local freeness in degree $i$ also requires control of the incoming differential. Remembering this avoids the false claim that constancy of $h^i$ alone always proves base change.

### 5.3 Flat and arbitrary change of base

If $g:T\to S$ is flat, then ordinary pullback is exact. Proper flat base change for coherent sheaves gives

$$
g^*R^if_*\mathcal F\xrightarrow{\sim}R^if_{T*}g'^*\mathcal F
$$

without requiring $R^if_*\mathcal F$ to be locally free. One proof takes a bounded finite presentation of the relevant cohomology complex: flat tensor commutes with kernels and images, hence with cohomology. For a general proper morphism, the same statement follows by the proper-reduction induction.

Arbitrary base change is subtler. The derived morphism

$$
Lg^*Rf_*\mathcal F\longrightarrow Rf_{T*}Lg'^*\mathcal F
$$

is an isomorphism when $f$ is proper of finite presentation and the relevant complex is perfect relative to $S$; in the projective case with $\mathcal F$ flat and finitely presented, the finite-complex theorem supplies the needed model. Passing from this derived isomorphism to degree-$i$ coherent sheaves requires the vanishing of Tor contributions from neighboring cohomology. The criterion of Section 5.2 is precisely that passage.

For a quotient $A\to A/I$, even when a two-row universal-coefficient sequence applies, one sees

$$
0\to H^i(K)\otimes_AA/I
\to H^i(K\otimes_AA/I)
\to\operatorname{Tor}_1^A(H^{i+1}(K),A/I)\to0.
$$

Thus torsion in the next cohomology group creates new classes after reduction. This is the most common arithmetic failure of naive base change.

### 5.4 Local freeness and constant fiber dimension

**Constant-rank corollary.** Under the hypotheses of Section 5.2, suppose $h^i_{\mathcal F}$ is locally constant and base change is surjective in degree $i$ at one point of each connected component. Then $R^if_*\mathcal F$ is locally free and commutes with arbitrary base change provided the same holds in degree $i-1$. Conversely, if $R^if_*\mathcal F$ is locally free and its formation commutes with residue fields, then $h^i_{\mathcal F}$ is locally constant.

The proof is immediate from the local minimal complex: constancy fixes the dimension of $K^i_{\min}\otimes k(s)$, while the adjacent surjectivity kills both differentials. Conversely a vector bundle has constant fiber rank.

A particularly useful downward induction begins above the cohomological dimension, where both sides vanish. If all fiber dimensions $h^j$ are locally constant for $j\geq i$, then descending through the minimal complex shows that every $R^jf_*\mathcal F$ for $j\geq i$ is locally free and commutes with arbitrary base change. The alternating constancy of Euler characteristic often lets one deduce the last missing degree.

### 5.5 Curves as a two-degree case

Let $f:C\to S$ be a proper flat finitely presented family of curves and $\mathcal F$ coherent and $S$-flat. Only degrees zero and one occur. Since degree two vanishes, base change in degree one is automatically surjective in the finite-complex model. Hence $R^1f_*\mathcal F$ commutes with residue fields; it is locally free exactly when base change in degree zero is surjective. If $h^0$ is locally constant, then both $f_*\mathcal F$ and $R^1f_*\mathcal F$ are locally free and commute with arbitrary base change.

For $\mathcal F=\mathcal O_C$ and geometrically connected reduced fibers, $h^0=1$. The unit map

$$
\mathcal O_S\longrightarrow f_*\mathcal O_C
$$

is an isomorphism on every geometric fiber and hence an isomorphism. Consequently $R^1f_*\mathcal O_C$ is locally free and universally compatible with base change. Its dual will be the Hodge bundle.

## 6. Flatness, Hilbert polynomials, and flattening

### 6.1 The cohomological meaning of a Hilbert polynomial

Let $f:X\to S$ be projective and finitely presented, let $\mathcal O_X(1)$ be relatively ample, and let $\mathcal F$ be coherent. For a geometric point $\bar s\to S$, the function

$$
n\longmapsto\chi(X_{\bar s},\mathcal F_{\bar s}(n))
$$

agrees for all sufficiently large $n$ with a numerical polynomial $P_{\bar s}(n)$. The projective-space resolution proves this: the Euler characteristic of $\mathcal O(n-a)$ is $\binom{n-a+r}{r}$, and additivity through a finite graded resolution expresses the answer as an integral combination of such binomial polynomials.

When $\mathcal F$ is flat over $S$, Section 4.3 applied to every twist shows that $P_{\bar s}$ is locally constant. More concretely, relative Serre vanishing gives, locally on $S$ and for $n\gg0$,

$$
R^if_*\mathcal F(n)=0\quad(i>0),
$$

and base change identifies

$$
f_*\mathcal F(n)\otimes\kappa(\bar s)
\simeq H^0(X_{\bar s},\mathcal F_{\bar s}(n)).
$$

The pushforward is then finite locally free of rank $P_{\bar s}(n)$. Thus a Hilbert polynomial is not merely a fiberwise count. It is the eventual rank profile of a sequence of vector bundles on the base.

### 6.2 Constancy and the converse

Constancy of the Hilbert polynomial detects flatness only with the correct hypotheses.

**Fiberwise flatness criterion.** Let $S$ be locally noetherian, $f:X\to S$ projective and finitely presented, and $\mathcal F$ coherent. Near a point $s\in S$, the sheaf $\mathcal F$ is flat over $S$ if and only if, for every sufficiently large $n$, $f_*\mathcal F(n)$ is locally free and its formation commutes with residue fields.

**Proof.** Flatness gives the conclusion by the preceding section. Conversely, choose $n$ so large that $\mathcal F(n)$ is generated relative to $S$ and write

$$
f^*\mathcal E\twoheadrightarrow\mathcal F(n),
\qquad \mathcal E=f_*\mathcal F(n).
$$

Let $\mathcal K$ be the kernel. Increase $n$ so that $\mathcal K$ is controlled by its own high twists. The assumed base-change property says that the presentation remains right exact on every fiber and that the fiber of $\mathcal K$ is the kernel of the fiber presentation. The local criterion for flatness says that a finitely presented quotient of a flat module is flat exactly when this kernel remains injective after tensoring with every residue field. Since $f^*\mathcal E$ is flat and the fiber presentation is exact, $\mathcal F(n)$ is flat. Undoing the twist proves the assertion. $\square$

Constancy of the integer $\chi(\mathcal F_s)$ for one twist is far too weak. Different sheaves can have the same Euler characteristic, and torsion in adjacent cohomological degrees can cancel in the alternating sum. One needs the polynomial for all large twists, or equivalently the exact high-degree presentation.

### 6.3 Flattening strata

Suppose $S$ is noetherian, $X\to S$ projective and finitely presented, and $\mathcal F$ coherent. The base can be decomposed into locally closed pieces on which $\mathcal F$ becomes flat.

**Flattening-stratification theorem.** For every numerical polynomial $P$, there is a locally closed subscheme $S_P\subseteq S$ with the following universal property. A morphism $T\to S$ factors through $S_P$ exactly when $\mathcal F_T$ is flat over $T$ and every geometric fiber has Hilbert polynomial $P$. The strata are pairwise disjoint and their underlying sets cover $S$.

**Proof strategy.** Choose $n$ beyond a common regularity bound. The finite module $f_*\mathcal F(n)$ has a universal flattening locus where it is locally free of rank $P(n)$; Fitting ideals cut out this locus scheme-theoretically. Repeat in finitely many consecutive degrees, enough that multiplication by degree-one sections reconstructs the saturated graded module. On their intersection, the multiplication maps and their kernels have the ranks forced by $P$. The evaluation presentation of Section 6.2 then proves flatness of $\mathcal F$. Conversely a flat family with polynomial $P$ makes all these high-degree modules locally free with the prescribed ranks, so its classifying map annihilates the same Fitting ideals and factors uniquely through the stratum. A regularity bound makes the construction finite. $\square$

The scheme structure matters. A map from a nonreduced $T$ may send its only point into the correct set while failing to factor through the stratum because an infinitesimal Fitting equation is nonzero. Flattening is designed to detect exactly that failure.

For a proper morphism without a chosen ample line bundle there is still a flattening decomposition in broad generality, but it need not be described by Hilbert polynomials. The projective form is the one needed for the parameter spaces considered here.

### 6.4 Uniform generation and embeddings

Let $f:X\to S$ be projective, flat, and finitely presented with $S$ noetherian, and let $\mathcal L$ be relatively ample. For $n\gg0$, relative Serre vanishing and base change give

$$
R^if_*\mathcal L^n=0\quad(i>0),
\qquad f_*\mathcal L^n\text{ finite locally free}.
$$

The evaluation map $f^*f_*\mathcal L^n\to\mathcal L^n$ is surjective. A still larger $n$ separates length-two subschemes in every fiber, so it defines a closed immersion

$$
X\hookrightarrow\mathbf P_S(f_*\mathcal L^n).
$$

To prove uniformity, apply Serre vanishing not only to $\mathcal O_X$ but to the ideal of the diagonal and to the universal length-two subscheme supplied by the finite-length Hilbert scheme. Vanishing makes restriction of sections surjective on every length-two fiber; properness of that parameter scheme turns pointwise largeness of $n$ into one bound. This explains why cohomological finiteness produces uniform projective embeddings.

## 7. Formal functions

### 7.1 Infinitesimal neighborhoods remember completion

Let $S=\operatorname{Spec}A$ be noetherian, let $I\subseteq A$, and set

$$
A_n=A/I^{n+1},\qquad
X_n=X\times_A\operatorname{Spec}A_n,
\qquad \mathcal F_n=\mathcal F/I^{n+1}\mathcal F.
$$

The schemes $X_n$ are the successive infinitesimal neighborhoods of the closed fiber $X_0$. They remember more than the reduced fiber: a section on $X_n$ records normal behavior up to order $n$.

There is a natural comparison

$$
H^i(X,\mathcal F)\otimes_AA_n
\longrightarrow H^i(X_n,\mathcal F_n).
$$

It is not generally an isomorphism for fixed $n$; the base-change criterion may fail. The theorem on formal functions says that the discrepancy disappears after taking the inverse limit. Completion is therefore more stable than any individual infinitesimal base change.

### 7.2 The theorem on formal functions

**Theorem on formal functions.** Let $f:X\to S$ be proper, with $S$ locally noetherian, let $\mathcal F$ be coherent, and let $\mathcal I\subseteq\mathcal O_S$ be a coherent ideal. Write

$$
S_n=(S,\mathcal O_S/\mathcal I^{n+1}),
\qquad X_n=X\times_SS_n,
\qquad \mathcal F_n=\mathcal F/\mathcal I^{n+1}\mathcal F.
$$

Then for every $i$ the natural map of sheaves along $V(\mathcal I)$ is an isomorphism

$$
(R^if_*\mathcal F)^{\wedge}_{\mathcal I}
\xrightarrow{\sim}
\varprojlim_n R^if_{n*}\mathcal F_n.
$$

On an affine open $\operatorname{Spec}A\subseteq S$, this reads

$$
H^i(X,\mathcal F)^{\wedge}_I
\xrightarrow{\sim}
\varprojlim_nH^i(X_n,\mathcal F_n).
$$

No flatness of $f$ or $\mathcal F$ over $S$ is required. Properness, coherence, and noetherianity are the essential hypotheses.

### 7.3 Proof by Artin--Rees and effacement

The proof has two algebraic mechanisms. First, the Artin--Rees lemma says that if $N\subseteq M$ are finite modules over a noetherian ring, then for some $c$ and all $n\geq c$,

$$
I^nM\cap N=I^{n-c}(I^cM\cap N).
$$

Consequently the $I$-adic topology induced on $N$ agrees with its own $I$-adic topology, and completion is exact on finite modules. Second, higher cohomology can be effaced by embedding a coherent sheaf into one whose relevant higher cohomology vanishes.

We give the argument in the projective case first. Resolve $\mathcal F$ far enough by finite sums of twists. The projective-space Cech calculation commutes with $A/I^{n+1}$ and produces a finite cochain model in any fixed range. For degree zero, compare

$$
\Gamma(X,\mathcal F)/I^{n+1}\Gamma(X,\mathcal F)
\longrightarrow\Gamma(X_n,\mathcal F_n).
$$

Its kernel and cokernel are controlled by the intersection of $\Gamma(X,\mathcal F)$ with $I^{n+1}$ inside a finite module of cochains. Artin--Rees shows that the two filtrations are cofinal, so they have the same inverse limit.

For higher degree, choose a short exact sequence

$$
0\to\mathcal F\to\mathcal G\to\mathcal Q\to0
$$

with $H^i(\mathcal G)=0$ and with the corresponding vanishing on every $X_n$. The long exact sequences identify the degree-$i$ comparison for $\mathcal F$ with the degree-$(i-1)$ comparison for $\mathcal Q$. Induction reduces to degree zero. Exactness of completion for finite modules permits passage through the long exact sequences; the transition systems satisfy the Mittag--Leffler condition because their images are descending submodules of finite modules and become stationary modulo each fixed power.

For a general proper morphism, use the projective modification of Section 2.4. The projective term satisfies the theorem. Kernel and cokernel are supported on a smaller closed subset, where noetherian induction applies. The two long exact cohomology systems, together with Artin--Rees exactness, transfer the isomorphism to $\mathcal F$. This proves the theorem. $\square$

The proof explains why formal functions is not simply repeated base change. Fixed-level errors can survive, but Artin--Rees makes their filtrations cofinal, so completion forgets the bounded displacement.

### 7.4 Consequences and limitations

If $A$ is complete for $I$ and $X$ is proper over $A$, then

$$
H^i(X,\mathcal F)
\simeq\varprojlim_nH^i(X_n,\mathcal F_n),
$$

because proper finiteness makes $H^i(X,\mathcal F)$ a finite, hence complete, $A$-module. Thus a coherent cohomology class is determined by its compatible restrictions to all infinitesimal neighborhoods.

This does not say every compatible family of coherent sheaves $\mathcal F_n$ comes from a coherent sheaf on $X$. That is an existence theorem for coherent objects on a completed proper space and belongs to a stronger algebraization theory. Formal functions compares cohomology of a sheaf already given on $X$.

Properness remains essential. For an open family, sections can have unbounded poles toward the omitted boundary, and the inverse limit of infinitesimal sections can be larger than the completion of global sections.

## 8. Completion and coherent passages

### 8.1 Ordinary and derived completion

For a complex $K$ of $A$-modules, the completion appropriate to exact constructions is

$$
R\widehat K=R\varprojlim_n(K\otimes_A^LA/I^{n+1}).
$$

There is a Milnor exact sequence

$$
0\to R^1\varprojlim_nH^{i-1}(K\otimes_A^LA/I^{n+1})
\to H^i(R\widehat K)
\to\varprojlim_nH^i(K\otimes_A^LA/I^{n+1})\to0.
$$

When $K$ has finite cohomology over a noetherian ring, Artin--Rees makes the relevant towers Mittag--Leffler and annihilates the first derived limit. Ordinary completion is exact on those cohomology modules. Hence

$$
H^i(R\widehat K)\simeq H^i(K)^{\wedge}_I.
$$

This is the derived-to-coherent passage behind formal functions. It is valid because finiteness removes both possible defects: Tor is organized inside derived tensor, and inverse-limit failure is removed by Mittag--Leffler.

Without finite generation the conclusion can fail. A tower may have images that shrink forever, producing a nonzero $R^1\varprojlim$, and an infinitely generated module need not be separated or complete for its $I$-adic topology.

### 8.2 Completed base change

Suppose $A\to B$ is a homomorphism of noetherian rings, $B$ is complete for $IB$, and $X$ is proper over $A$. If the derived base-change morphism is an isomorphism for the coherent complex under consideration, then completion and formal functions yield

$$
R\Gamma(X,\mathcal F)\widehat\otimes_A^LB
\simeq
R\varprojlim_nR\Gamma
\bigl(X_{B/I^{n+1}B},\mathcal F_{B/I^{n+1}B}\bigr).
$$

If in addition the neighboring cohomology modules satisfy the local-freeness criterion, taking degree $i$ gives the ordinary formula

$$
H^i(X,\mathcal F)\otimes_AB
\simeq H^i(X_B,\mathcal F_B).
$$

The first statement is robust; the second discards Tor and therefore needs the extra condition. This distinction is particularly important when $B$ has residue characteristic dividing torsion in $H^{i+1}$.

### 8.3 Lifting sections through thickenings

Let $A'\twoheadrightarrow A$ have square-zero kernel $J$, and let $X'$ be a proper flat lift of $X$ with a coherent $A'$-flat sheaf $\mathcal F'$. The exact sequence

$$
0\to J\otimes_A\mathcal F\to\mathcal F'\to\mathcal F\to0
$$

gives

$$
H^0(X',\mathcal F')\to H^0(X,\mathcal F)
\xrightarrow{\delta}H^1(X,J\otimes_A\mathcal F).
$$

A section lifts exactly when its obstruction $\delta(s)$ vanishes; if it lifts, the set of lifts is a torsor under $H^0(X,J\otimes_A\mathcal F)$. Iterating through $A/I^{n+1}$ makes the role of $H^1$ concrete. If all these obstructions vanish and compatible sections exist, formal functions produces a section of the completed cohomology module. When $A$ is complete and cohomology finite, that is an actual global section of $\mathcal F$.

For line bundles the analogous obstruction lies one degree higher: infinitesimal automorphisms are $H^0(\mathcal O)$, deformations form a torsor under $H^1(\mathcal O)\otimes J$, and obstructions lie in $H^2(\mathcal O)\otimes J$. On a curve $H^2=0$, which is the cohomological reason its Picard functor is smooth.

### 8.4 What is not yet algebraization

Completion remembers every infinitesimal neighborhood, but an object over all neighborhoods need not automatically come from the algebraic family without an existence theorem. Nor does an isomorphism of completions imply an isomorphism on an unspecified open neighborhood unless finite presentation and an effectivity argument are supplied.

The safe conclusions here are these: cohomology of a given coherent sheaf completes correctly; compatible sections algebraize because they belong to a finite complete module; and morphisms between already-given coherent sheaves can often be recovered from completed Hom modules under properness. Constructing schemes or sheaves from purely completed data requires the separate proper existence theory developed later.

## 9. Duality interfaces in relative dimension one

### 9.1 Trace and the relative dualizing line

Let $f:C\to S$ be smooth, proper, and finitely presented of relative dimension one. The sheaf

$$
\omega_{C/S}=\Omega^1_{C/S}
$$

is invertible. Fiberwise residues define a trace

$$
\operatorname{Tr}_f:R^1f_*\omega_{C/S}\longrightarrow\mathcal O_S.
$$

To construct it, choose locally on $S$ a relative finite map from $C$ to $\mathbf P^1_S$ after a sufficiently positive projection. On the affine line, a meromorphic differential has residues at the finitely many poles; the coefficient of $t^{-1}dt$ is unchanged by a change of local parameter. The sum of residues, including the point at infinity, is zero. Cech representatives on the standard two-open cover therefore define a functional on $H^1(\omega)$. Compatibility of residue with finite trace makes the functional independent of the chosen projection. These local traces agree under base change and glue over $S$.

On every geometrically connected fiber, the trace is an isomorphism

$$
H^1(C_s,\omega_{C_s})\simeq\kappa(s).
$$

One proves this first for $\mathbf P^1$ by the Laurent-monomial calculation and then for a finite map to $\mathbf P^1$ using the trace pairing; normalization and exact sequences reduce a general smooth projective curve to that case. Coherent base change upgrades the fiberwise isomorphisms to

$$
R^1f_*\omega_{C/S}\simeq\mathcal O_S.
$$

### 9.2 Perfect pairings for smooth proper curves

Multiplication followed by trace gives, for a vector bundle $\mathcal E$ on $C$,

$$
R^if_*\mathcal E\otimes
R^{1-i}f_*(\mathcal E^\vee\otimes\omega_{C/S})
\longrightarrow\mathcal O_S.
$$

**Relative duality for curves.** If the indicated higher direct images are locally free and commute with base change—as they do on any open where their fiber dimensions are constant—the pairing is perfect. Equivalently,

$$
(R^if_*\mathcal E)^\vee
\simeq R^{1-i}f_*(\mathcal E^\vee\otimes\omega_{C/S}),
\qquad i=0,1.
$$

**Proof.** The residue construction is compatible with arbitrary base change. On a geometric fiber it becomes the usual pairing between a Cech cocycle and a section of the dual twist. A divisor large enough to kill $H^1$ gives a two-term resolution by principal parts. In that resolution the residue pairing identifies the transpose of the evaluation matrix with the connecting matrix. Elementary linear algebra then proves nondegeneracy. Thus the displayed map is an isomorphism on every geometric fiber. Since both sides are vector bundles, its determinant is nonzero on every fiber and hence a unit. $\square$

Taking $\mathcal E=\mathcal O_C$ gives

$$
f_*\omega_{C/S}\simeq(R^1f_*\mathcal O_C)^\vee.
$$

This is the precise duality interface used below. It requires no general duality statement in higher relative dimension.

### 9.3 Base change and the Hodge bundle

Assume the fibers of $C/S$ are geometrically connected of genus $g$. Then $f_*\mathcal O_C=\mathcal O_S$, $R^1f_*\mathcal O_C$ is locally free of rank $g$, and

$$
\mathbb E_C=f_*\omega_{C/S}
$$

is locally free of rank $g$. It commutes with every base change. We call $\mathbb E_C$ the **Hodge bundle** of the curve.

The assertion follows from Section 5.5 and relative duality. Notice the order of reasoning. Fiberwise dimension $g$ gives local constancy; base change in top degree starts the downward criterion; only then may one treat $f_*\omega$ as a vector bundle. Writing a determinant before proving local freeness would conceal the main issue.

For genus one with a section, $\omega_{C/S}$ is pulled back from $\mathbb E_C$ by translation, and $\mathbb E_C$ is a line bundle. A nowhere-vanishing invariant differential is therefore a trivialization of the Hodge line, not merely a differential chosen separately on each fiber.

### 9.4 Nodal and Gorenstein curves

If $f:C\to S$ is proper, flat, finitely presented, and Gorenstein of pure relative dimension one, there is an invertible relative dualizing sheaf $\omega_{C/S}$ even when fibers are nodal. At a node with local equation $xy=a$, a dualizing differential can be written

$$
\frac{dx}{x}=-\frac{dy}{y}.
$$

On the normalization of a nodal fiber, sections are meromorphic differentials with at most simple poles at the two branches and residues summing to zero. This residue condition makes the trace and the perfect pairings extend across the node.

The proof reduces to the smooth normalization and the exact sequence comparing functions on the curve with functions on its normalization. The cokernel is supported at the nodes. Dualizing that finite-length sequence turns the difference of values into the sum-of-residues condition. Fiberwise perfectness and coherent base change then give the relative pairing. If the family is not Gorenstein, the dualizing object need not be a line bundle; treating it as one would make the Hodge formulas false.

## 10. Proper curves and Picard representability

### 10.1 The relative Picard functor

Let $f:C\to S$ be proper, flat, and finitely presented with geometrically integral fibers, and suppose a section $e:S\to C$ is fixed. For an $S$-scheme $T$, begin with

$$
\operatorname{Pic}(C_T)/\operatorname{Pic}(T).
$$

The associated faithfully flat sheaf is denoted $\operatorname{Pic}_{C/S}$. After a faithfully flat cover of $T$, a class has a representative rigidified along $e_T$: tensor by the inverse of $e_T^*\mathcal L$. Rigidification removes scalar automorphisms and makes a set-valued relative functor plausible.

The sheafification is essential. A line bundle can exist locally on $T$ with compatible relative classes yet have no chosen global representative. The section does not eliminate this gluing phenomenon, but it eliminates automorphisms of a rigidified representative, so effective gluing is unique.

Degree is locally constant in flat families. Thus

$$
\operatorname{Pic}_{C/S}=\coprod_{d\in\mathbf Z}
\operatorname{Pic}^d_{C/S}.
$$

The central problem is to show that these sheaves are schemes of finite presentation, not infinite-dimensional collections of line bundles.

### 10.2 Divisors provide finite-dimensional charts

Assume now that $C/S$ is smooth and projective of genus $g$, with geometrically connected fibers. The relative symmetric power $C^{(d)}$ represents effective relative divisors of degree $d$. Sending a divisor $D$ to $\mathcal O_C(D)$ defines the Abel transformation

$$
a_d:C^{(d)}\longrightarrow\operatorname{Pic}^d_{C/S}.
$$

This notation does not assume the target is already represented: it is a natural transformation from a represented functor.

If $d\geq2g-1$, then for every degree-$d$ line bundle $L$ on a fiber,

$$
H^1(C_s,L)=0.
$$

Indeed, relative duality identifies its dual with $H^0(C_s,L^{-1}\otimes\omega)$, whose degree $2g-2-d$ is negative. A nonzero section would define an effective divisor of negative degree, impossible. It remains to calculate the Euler characteristic. Tensoring by the line bundle of one point changes Euler characteristic by one, as follows from

$$
0\to L(-x)\to L\to L|_x\to0.
$$

After a finite extension one can express a divisor as a sum and difference of closed points; additivity and descent give $\chi(L)=\deg L+\chi(\mathcal O_C)=d+1-g$. Since $H^1(C_s,L)=0$, this proves $h^0(L)=d+1-g$ without importing a stronger curve theorem.

In a family, semicontinuity and base change show that $p_*\mathcal L$ is locally free of that rank for any locally given universal degree-$d$ line bundle $\mathcal L$ on $C_T$. Its projective bundle of nonzero sections up to scalar parametrizes effective divisors whose associated line bundle is $\mathcal L$. Thus the fibers of $a_d$ are projective spaces of dimension $d-g$ and vary as projective bundles.

This is the decisive boundedness statement. Every degree-$d$ line bundle with $d\geq2g-1$ has a section, hence comes from a divisor; and the ambiguity in the divisor is a finite-rank projective bundle controlled by coherent base change.

### 10.3 The Picard scheme of a smooth proper curve

**Picard representability theorem for curves.** Let $S$ be locally noetherian and let $C\to S$ be smooth, projective, and finitely presented with geometrically connected fibers of genus $g$ and a section. Then the rigidified relative Picard sheaf is represented by a separated $S$-scheme locally of finite presentation. Each $\operatorname{Pic}^d_{C/S}$ is smooth and proper over $S$, and formation of the Picard scheme commutes with arbitrary base change.

**Proof strategy and decisive details.** Choose $n\geq2g-1-d$. Tensoring by $\mathcal O(ne)$ identifies degree $d$ with degree $d+n$, so it suffices to construct a component in high degree. On $C^{(m)}$, the universal divisor supplies a universal rigidified line bundle after correcting along $e$. Two divisors determine the same line-bundle class exactly when their difference is principal. For $m\geq2g-1$, the preceding section identifies each equivalence class with the projective space of sections of one line bundle.

Locally on the symmetric power, cohomology and base change turns these spaces of sections into projective bundles. The relation “same associated line bundle” is therefore represented by a smooth, proper equivalence relation whose two projections are projective bundles. Affine invariant neighborhoods are obtained by trivializing the finite locally free module of sections; on such a neighborhood, the quotient is the spectrum of functions constant along the projective fibers. These local quotients glue because rigidification makes the relation effective and removes stabilizers. They form a separated finitely presented scheme $P^m$, and the universal property identifies $P^m$ with $\operatorname{Pic}^m_{C/S}$.

Properness follows because the surjective Abel map $C^{(m)}\to P^m$ has proper source and properness descends under a surjective proper cover. For another degree, translation by $\mathcal O((d-m)e)$ gives an isomorphism of components. Arbitrary base change preserves the universal divisor, the vector bundles of sections, and the quotient relation, proving compatibility.

Smoothness can be checked infinitesimally. For a square-zero extension $T_0\subset T$ with ideal $J$, the obstruction to lifting a line bundle lies in

$$
H^2(C_{T_0},\mathcal O_{C_{T_0}})\otimes J=0.
$$

Thus lifts exist locally; rigidified automorphisms vanish, and the difference between two lifts lies in $H^1(\mathcal O)\otimes J$. This is the infinitesimal lifting criterion for smoothness. $\square$

The construction uses the selected Hilbert spaces of effective divisors and the coherent base-change theorem. It does not require a general parameter space for all quotients.

### 10.4 Tangent spaces, smoothness, and the Jacobian

Apply the square-zero calculation to $T=\operatorname{Spec}(k[\epsilon]/(\epsilon^2))$. A line bundle trivial modulo $\epsilon$ is glued by functions $1+\epsilon a_{ij}$. The cocycle condition says $(a_{ij})$ is a Cech $1$-cocycle; changing trivializations changes it by a coboundary. Hence

$$
T_0\operatorname{Pic}_{C_s/\kappa(s)}
\simeq H^1(C_s,\mathcal O_{C_s}).
$$

In families, the tangent bundle along the identity is $R^1f_*\mathcal O_C$, locally free of rank $g$. Its dual is the Hodge bundle $f_*\omega_{C/S}$.

The identity component

$$
\operatorname{Pic}^0_{C/S}
$$

is a smooth proper group scheme of relative dimension $g$, the Jacobian of $C/S$. The group law comes from tensor product of rigidified line bundles, inversion from dualization, and the identity from $\mathcal O_C$. Their compatibility with base change is functorial. The construction of canonical polarizations and detailed divisor theory belongs to the later study of Jacobians; the representability, smoothness, tangent space, and Hodge cotangent space are already consequences of the present cohomology.

## 11. Abelian schemes and their coherent cohomology

### 11.1 Invariant differentials

Let $p:A\to S$ be an abelian scheme of relative dimension $g$: a proper, smooth, finitely presented group scheme with geometrically connected fibers. Let $e:S\to A$ be its identity. Translation by a section $a\in A(T)$ identifies the cotangent spaces along $e_T$ and $a$. These identifications glue to an isomorphism

$$
p^*\omega_A\xrightarrow{\sim}\Omega^1_{A/S},
\qquad \omega_A=e^*\Omega^1_{A/S}.
$$

To see this, pull a differential back along multiplication $A\times_SA\to A$, then restrict one factor to the identity. The resulting invariant differential agrees with the original at $e$; translating shows equality everywhere. Since $\Omega^1_{A/S}$ is locally free of rank $g$, so is $\omega_A$. Its determinant

$$
\lambda_A=\det\omega_A
$$

is the Hodge line bundle. Both $\omega_A$ and $\lambda_A$ commute with arbitrary base change because relative differentials do for smooth morphisms and the identity section base-changes.

The relative canonical line is

$$
\omega_{A/S}^{\mathrm{top}}
=\bigwedge^g\Omega^1_{A/S}
\simeq p^*\lambda_A.
$$

It is not generally trivial on the total family: it is pulled back from the Hodge line on the base. Fiberwise it is trivial because the base line becomes one-dimensional.

### 11.2 The exterior algebra theorem

The structure-sheaf cohomology of an abelian scheme is controlled by degree one.

**Exterior algebra theorem.** For an abelian scheme $p:A\to S$ of relative dimension $g$,

$$
R^ip_*\mathcal O_A
\simeq\bigwedge^iR^1p_*\mathcal O_A,
\qquad 0\leq i\leq g,
$$

and $R^ip_*\mathcal O_A=0$ for $i>g$. Every displayed sheaf is finite locally free, its rank is $\binom gi$, and its formation commutes with arbitrary base change. Moreover

$$
R^1p_*\mathcal O_A\simeq\omega_{A^\vee}^\vee
$$

once the dual abelian scheme is constructed.

**Proof strategy.** Proper smoothness and connected fibers give $p_*\mathcal O_A=\mathcal O_S$. Fiber dimensions $h^i(A_s,\mathcal O)$ equal $\binom gi$. This can be proved over an algebraically closed field by choosing an ample line bundle $L$, using a sufficiently high multiplication map $[n]$, and decomposing the trace action on cohomology: translation invariance makes primitive degree-one classes generate, while the action of $[n]^*$ has weight $n^i$ in degree $i$. The cup product therefore gives an isomorphism

$$
\bigwedge^iH^1(A_s,\mathcal O_{A_s})
\xrightarrow{\sim}H^i(A_s,\mathcal O_{A_s}).
$$

This argument can be carried out integrally without dividing by $n$ by choosing two coprime values of $n$ and using the resulting polynomial identities.

The fiber dimensions are constant. Starting above degree $g$ and applying the downward base-change criterion proves that all $R^ip_*\mathcal O_A$ are locally free and universally compatible with base change. Cup product defines the relative exterior-algebra map. It is an isomorphism on every geometric fiber, hence its determinant is a unit locally on $S$. This proves the theorem. $\square$

The group law is essential. A general smooth proper $g$-fold does not have structure-sheaf cohomology generated in degree one, nor binomial Hodge numbers.

Relative duality is compatible with this description. Multiplication and trace give perfect pairings

$$
R^ip_*\mathcal O_A\otimes
R^{g-i}p_*\mathcal O_A\longrightarrow
R^gp_*\mathcal O_A\simeq\lambda_A^\vee.
$$

The last identification follows from duality applied to $p^*\lambda_A$: the trace maps $R^gp_*p^*\lambda_A$ to $\mathcal O_S$, and the projection formula gives $R^gp_*\mathcal O_A\otimes\lambda_A\simeq\mathcal O_S$.

### 11.3 The dual abelian scheme

For an $S$-scheme $T$, consider line bundles $\mathcal L$ on $A_T$ rigidified along the identity and algebraically equivalent to zero on every geometric fiber. Tensor product defines a group functor.

**Dual representability theorem.** If $A/S$ is an abelian scheme, this functor is represented by an abelian scheme $A^\vee/S$ of relative dimension $g$. It commutes with arbitrary base change and carries a universal rigidified line bundle

$$
\mathcal P\quad\text{on}\quad A\times_SA^\vee,
$$

the Poincare bundle.

**Proof strategy.** Choose a relatively ample symmetric line bundle $L$ on $A$. The theorem of the cube shows that for a degree-zero rigidified line bundle $M$, sufficiently positive $L^n\otimes M$ has a Hilbert polynomial independent of $M$, while translation changes it in a controlled way. High powers have no higher cohomology and are generated by sections, uniformly by semicontinuity and base change. Effective divisors in these bundles therefore lie in one projective Hilbert scheme.

As for curves, pairs of divisors differing by a principal divisor form a projective-bundle relation. Rigidification removes scalar stabilizers. The quotient gives a separated group scheme locally of finite presentation representing the degree-zero functor. The theorem of the cube implies that the connected component is stable under tensor product and inversion and that translation acts transitively on its geometric components.

Properness follows from the valuative criterion. A degree-zero bundle on the generic fiber of an abelian scheme extends after twisting by a vertical divisor; rigidification and translation invariance force that vertical ambiguity to come from the base, hence to vanish in the relative class. Smoothness is subtler than the curve case because $H^2(\mathcal O_A)$ need not vanish. For algebraically trivial rigidified bundles, the cubical relation kills the obstruction: its pullbacks under the three projections cancel, while evaluation at the identity forces the remaining base class to vanish. The tangent space is $R^1p_*\mathcal O_A$, of rank $g$. Thus the representing group is smooth and proper of relative dimension $g$, hence an abelian scheme. The universal rigidified bundle follows from the representing property. $\square$

The proof isolates the contribution of coherent cohomology: high-twist local freeness bounds the Hilbert construction, degree-one cohomology gives the tangent bundle, and base change makes the construction relative. The cubical group structure supplies the extra unobstructedness not available for an arbitrary higher-dimensional proper scheme.

### 11.4 Polarizations and base change

A line bundle $L$ on $A$ defines

$$
\phi_L:A\longrightarrow A^\vee,\qquad
a\longmapsto t_a^*L\otimes L^{-1}.
$$

The theorem of the square proves that $\phi_L$ is a homomorphism: expanding the expression at $a+b$ cancels the cross terms. If $L$ is relatively ample, $\phi_L$ is finite and surjective on every geometric fiber, hence finite locally free after the usual constant-degree condition. It is a polarization.

Every part of the construction commutes with base change. In particular, the kernel, degree, and induced map on Hodge bundles specialize correctly. The cotangent map at the identity is

$$
\omega_{A^\vee}\longrightarrow\omega_A.
$$

For a principal polarization it is an isomorphism. This self-duality will later identify the two halves of the Hodge data in symplectic moduli problems; here it is simply a morphism of finite locally free sheaves justified by coherent base change.

## 12. Hodge bundles in low-dimensional PEL families

### 12.1 What is assumed and what is proved

A PEL family in this chapter means an abelian scheme $A\to T$ of relative dimension $g\leq2$, together with an action

$$
\iota:\mathcal O\longrightarrow\operatorname{End}_T(A)
$$

of a fixed finite free order, a polarization compatible with a chosen involution on $\mathcal O$, and any finite level structure already defined over $T$. We do not construct a parameter space for these data. Given such a family, we prove the coherent statements that are stable under changing $T$: local freeness and decomposition of Hodge bundles, closed rank conditions, finite modules of sections on a proper parameter space, and exact coefficient-change criteria.

This boundary is important. Cohomology can show that a condition on an existing universal family is closed or that its sections are finite. It cannot by itself supply the universal family, compactification, or level structure.

### 12.2 Endomorphisms and decompositions

The action on $A$ differentiates to an action of $\mathcal O$ on

$$
\omega_A=e^*\Omega^1_{A/T}
$$

and hence on $\lambda_A=\det\omega_A$. If

$$
\mathcal O\otimes_{\mathbf Z}\mathcal O_T
\simeq\prod_{\tau} \mathcal O_T
$$

through orthogonal idempotents $e_\tau$, then

$$
\omega_A=\bigoplus_\tau\omega_\tau,
\qquad \omega_\tau=e_\tau\omega_A.
$$

Each summand is finite locally free because the image of an idempotent on a vector bundle is a direct summand. Its rank is locally constant. The determinant condition prescribing ranks $r_\tau$ is therefore open and closed.

In dimension one this gives the familiar Hodge line. In dimension two, the possibilities include one rank-two bundle, two Hodge lines, or conjugate rank-one pieces tied together by the polarization. If a polarization identifies the relevant dual action, the perfect pairing on relative first cohomology identifies complementary eigensummands. These statements follow from the idempotent decomposition and the nondegenerate polarization pairing; no classification of the parameter problem is needed.

### 12.3 Determinants, ranks, and bad primes

At a prime where $\mathcal O$ is not etale over the base, the idempotents may not exist. One must not write a direct sum indexed by embeddings. The integral replacement is the characteristic-polynomial condition

$$
\det(T-\iota(a)\mid\omega_A)
=\prod_\tau(T-\tau(a))^{r_\tau}
$$

for every $a$ in a finite set of generators of $\mathcal O$. Equality of coefficients is a finite collection of equations on $T$, so it cuts out a closed subscheme. On the etale locus it is equivalent to the rank decomposition above.

This explains a typical special-fiber phenomenon. Two eigenspaces distinct in characteristic zero can coalesce modulo a ramified prime. The total Hodge bundle remains locally free of rank $g$, but the individual characteristic-zero summands need not extend as vector bundles. Determinant equations survive because they avoid choosing idempotents.

For the low-dimensional families considered here, these rank and determinant equations are the coherent conditions we use. Even in dimension two, one must not infer that they define a flat parameter space at a ramified prime: a particular ramified unitary problem can require an additional incidence or wedge condition. Such a condition is again expressed as vanishing of a map between finite exterior powers of the Hodge bundle, hence is closed and commutes with base change. Determining which extra condition gives the correct flat parameter space is separate local geometry, not a consequence of coherent cohomology.

### 12.4 Compactifications and boundary behavior

Suppose a low-dimensional PEL parameter scheme $M$ and an abelian scheme $A/M$ are already given. Then $\lambda_A$ is a line bundle and

$$
H^0(M,\lambda_A^k)
$$

is finite over the base whenever $M$ is proper and noetherian. If $M$ is not proper, this finiteness need not hold.

Often one has a proper compactification $\bar M$ with boundary divisor $D$ and an extension $\bar\lambda$ of the Hodge line. The present theory applies once these objects are given and coherent. It proves finiteness of $H^i(\bar M,\bar\lambda^k(-D))$, semicontinuity in a flat family, and base change under the adjacent-degree criteria. It does not prove that $\bar M$, $D$, or $\bar\lambda$ exists. That geometric construction is a separate input.

If $\bar M$ is a curve or surface, coherent cohomology vanishes above degree one or two respectively. This small amplitude makes reduction questions tractable: on a curve, only $H^1$ can obstruct base change of global sections; on a surface, both $H^1$ and $H^2$ enter, and constancy of Euler characteristic alone cannot distinguish them.

## 13. Integral modular forms as coherent sections

### 13.1 The geometric definition

Let $R$ be a noetherian ring and let $q:Y\to\operatorname{Spec}R$ be a proper flat finitely presented curve that is already known to carry the relevant compactified modular interpretation. Assume its universal generalized elliptic family supplies an invertible Hodge sheaf $\omega$ on $Y$. For $k\geq0$, define

$$
M_k(Y/R)=H^0(Y,\omega^k).
$$

An element is an integral modular form of weight $k$ for this given modular problem. The transformation law is built into the line bundle: trivializing $\omega$ by an invariant differential turns a section into a function, and rescaling the differential by $u$ rescales that function by $u^{-k}$ under the quotient convention.

This definition is geometric and integral. It requires neither a complex variable nor division by the level. It also makes the foundational boundary exact: the present book studies sections once $Y$ and $\omega$ exist; it does not assert the representability or compactification of a modular problem.

### 13.2 Finiteness and change of coefficients

Proper finiteness immediately gives:

**Integral finiteness theorem.** The $R$-module $M_k(Y/R)$ is finite. If $R\to R'$ is flat, then

$$
M_k(Y/R)\otimes_RR'\xrightarrow{\sim}
M_k(Y_{R'}/R')
$$

provided $\omega$ pulls back to the Hodge sheaf of the changed family.

For arbitrary $R'$, flatness is not available. Because $Y/R$ is a curve, a finite complex in degrees zero and one governs $\omega^k$. When $R'=R/I$ and the quotient has Tor dimension at most one, the exact sequence is

$$
0\to M_k(Y/R)\otimes_RR/I
\to M_k(Y_{R/I}/(R/I))
\to\operatorname{Tor}_1^R
\bigl(H^1(Y,\omega^k),R/I\bigr)\to0.
$$

Thus reduction creates extra modular forms exactly from torsion in $H^1(Y,\omega^k)$. If $R$ is a discrete valuation ring with uniformizer $\pi$, the last term is the $\pi$-torsion of $H^1(Y,\omega^k)$.

For $k\gg0$, ampleness of $\omega$—when it is known for the given compactification—implies $H^1(Y,\omega^k)=0$. Then $M_k$ is locally free and commutes with every coefficient change. If $\omega$ is not ample, eventual vanishing cannot be inferred merely from its name as a Hodge bundle.

### 13.3 Cusp forms and the boundary

Let $D\subset Y$ be a finite flat effective Cartier divisor marking the cusps. Define

$$
S_k(Y/R)=H^0(Y,\omega^k(-D)).
$$

The exact sequence

$$
0\to\omega^k(-D)\to\omega^k\to\omega^k|_D\to0
$$

shows that a modular form is cuspidal exactly when its restriction to every cusp vanishes scheme-theoretically. The quotient is finite locally free over $R$ when $D/R$ is finite locally free. Its connecting map gives

$$
0\to S_k(Y/R)\to M_k(Y/R)\to
H^0(D,\omega^k|_D)\to H^1(Y,\omega^k(-D)).
$$

Consequently surjectivity of evaluation at the cusps is controlled by the last $H^1$. This remains meaningful over nonreduced bases: vanishing on the underlying cusp points is weaker than vanishing on the Cartier divisor.

If $\omega^k(-D)$ is sufficiently positive, its $H^1$ vanishes, cusp evaluation is onto, and both modular and cusp forms commute with arbitrary base change. The proof is relative Serre vanishing followed by the exact base-change theorem.

### 13.4 The exact base-change test

Let $s\in\operatorname{Spec}R$. The reduction map

$$
M_k(Y/R)\otimes\kappa(s)\longrightarrow
H^0(Y_s,\omega_s^k)
$$

is surjective if and only if the outgoing differential in a local minimal cohomology complex vanishes. When it is surjective, it is an isomorphism near $s$. Moreover $M_k(Y/R)$ is locally free near $s$ exactly when the corresponding preceding condition is satisfied; in degree zero this amounts, through the two-term curve complex, to flatness of the cokernel or equivalently the absence of the relevant torsion in $H^1$.

Over a discrete valuation ring, the statement is particularly transparent:

$$
M_k(Y/R)\otimes_RR/\pi
\xrightarrow{\sim}M_k(Y_{R/\pi}/(R/\pi))
$$

if and only if $H^1(Y,\omega^k)$ has no $\pi$-torsion. The same criterion with $\omega^k(-D)$ governs cusp forms. This is the exact integral content of “forms reduce correctly”; a dimension comparison over the fraction field and residue field is only a consequence.

## 14. Representability consequences and their boundary

### 14.1 A coherent representability package

The arguments above repeatedly use one pattern. Let $f:X\to S$ be projective, flat, and finitely presented, with $S$ locally noetherian, and let $\mathcal F$ be coherent and $S$-flat. On an open where $R^1f_*\mathcal F=0$, the sheaf $f_*\mathcal F$ is finite locally free and commutes with arbitrary base change. Therefore the functor

$$
T\longmapsto H^0(X_T,\mathcal F_T)
$$

is represented by the affine bundle

$$
\mathbf V((f_*\mathcal F)^\vee)
=\operatorname{Spec}_S\operatorname{Sym}(f_*\mathcal F)^\vee.
$$

Indeed, a map $T\to\mathbf V(\mathcal E^\vee)$ is a section of $\mathcal E_T$, and base change identifies this with a section of $\mathcal F_T$. Nonzero sections up to scaling are represented by the corresponding projective bundle when they generate a line in every fiber. Vanishing along a fixed finite flat subscheme is the kernel of a map of vector bundles, hence a closed linear condition whenever the cokernel is flat.

This elementary representability result is the local engine behind Abel maps, divisors in a fixed line bundle, Hodge tensors, and spaces of forms. It requires vanishing or the exact base-change criterion; a merely coherent pushforward need not represent fiberwise sections correctly.

### 14.2 Curves, abelian schemes, and PEL data

For a smooth proper curve with a section, high-degree divisors form a symmetric power and their linear systems are projective bundles. Their quotient represents the Picard scheme. Degree-one cohomology gives its tangent bundle, and vanishing of degree two makes it smooth.

For an abelian scheme, high ample divisors again give a bounded Hilbert construction. The theorem of the cube cuts out algebraically trivial rigidified classes, giving the dual abelian scheme. Its tangent and cotangent bundles are respectively $R^1p_*\mathcal O_A$ and $\omega_{A^\vee}$.

For a given low-dimensional PEL family, idempotent rank conditions are open and closed on the unramified locus, while characteristic-polynomial conditions are closed integrally. A prescribed Hodge tensor is the zero locus or fixed locus of a map between finite locally free sheaves. A choice of a Hodge section is represented by an affine bundle, and a line in a rank-two Hodge bundle by a projective bundle. These are genuine representability consequences. They do not amount to construction of the entire PEL parameter space, which also requires group objects, level structures, descent, and compactification.

### 14.3 Failures when hypotheses are weakened

The following boundary cases summarize why the hypotheses have been repeated.

- If $f$ is not proper, $f_*\mathcal F$ can be infinitely generated and formal functions can fail.

- If $\mathcal F$ is not coherent, properness does not force finite cohomology.

- If $\mathcal F$ is not flat over the base, ordinary fibers omit Tor and semicontinuity in the stated form can fail.

- If fiber dimensions jump, higher direct images need not be vector bundles; the Poincare bundle on an elliptic curve gives a basic example.

- If an order ramifies on the base, characteristic-zero Hodge eigenspaces may merge and must be replaced by determinant equations.

- If a compactified modular or PEL family is not already constructed, coherent finiteness does not construct it.

- If a dualizing sheaf is not invertible, determinant formulas requiring a dualizing line are invalid.

Each failure has the same moral: a fiberwise slogan loses extension, nilpotent, or boundary information. Finite complexes and coherent sheaves preserve it.

## 15. Synthesis

### 15.1 The chain of implications

The theory can be read as one chain:

$$
\begin{array}{c}
\text{properness and coherence}\\
\Downarrow\\
\text{finite higher direct images}\\
\Downarrow\quad\text{with flatness}\\
\text{finite complexes controlling fibers}\\
\Downarrow\\
\text{semicontinuity and exact base-change criteria}\\
\Downarrow\\
\text{local freeness, flattening, and uniform linear systems}\\
\Downarrow\\
\text{Picard charts, Hodge bundles, and finite spaces of forms}.
\end{array}
$$

In a different direction, noetherian finiteness plus Artin--Rees gives

$$
\text{proper cohomology}
\Longrightarrow
\text{formal functions}
\Longrightarrow
\text{control by all infinitesimal neighborhoods}.
$$

The derived language supplies the maps and remembers Tor and inverse-limit terms. The coherent language supplies finite modules, vector bundles, rank loci, and parameter spaces. Passing from the first to the second is justified only after boundedness, finite generation, and the adjacent-degree tests have been checked.

### 15.2 A theorem checklist for later use

For a proper morphism of locally noetherian schemes and a coherent sheaf, all higher direct images are coherent. For a projective finitely presented family and a base-flat coherent sheaf, a bounded finite locally free complex governs arbitrary coefficient modules. Fiber cohomology dimensions are upper semicontinuous, and Euler characteristic is locally constant.

At a point, surjectivity of the degree-$i$ base-change map persists nearby. Under that surjectivity, $R^if_*\mathcal F$ is locally free exactly when base change is also surjective in degree $i-1$. When both adjacent conditions hold, degree-$i$ cohomology commutes with arbitrary base change. Flat base change needs no local-freeness conclusion.

For a coherent ideal on a noetherian base, the completion of $R^if_*\mathcal F$ is the inverse limit of cohomology on infinitesimal thickenings. If the base is complete, finite cohomology is recovered from that limit. This is a statement about a sheaf already present on the proper family, not an unrestricted existence theorem for completed objects.

For smooth proper connected curves, $R^1f_*\mathcal O$ and $f_*\omega$ are dual vector bundles, and the Picard scheme is smooth, proper, and compatible with base change. For abelian schemes, structure-sheaf cohomology is the exterior algebra on degree one, the Hodge bundle is finite locally free, and algebraically trivial rigidified line bundles form the dual abelian scheme.

Given a proper low-dimensional PEL or modular family, Hodge bundles, their integral determinant conditions, modular forms, and cusp forms are coherent constructions. Their modules of sections are finite. Reduction of forms is exact precisely when the neighboring coherent cohomology contributes no Tor.

### 15.3 Conclusion

Coherent cohomology in a proper family is finite linear algebra carrying geometric memory. The matrices in a finite complex remember how fiber classes appear and disappear. Their minors draw the jumping loci. Their neighboring differentials decide whether cohomology is a vector bundle. Their reductions record torsion, and their completions gather every infinitesimal neighborhood into one finite module.

That linear algebra is powerful because its hypotheses are geometric. Properness closes the boundary, coherence bounds the data, flatness makes fibers honest tensor products, finite presentation makes rank conditions visible, and noetherianity makes completion exact. Relative duality then turns degree-one cohomology into Hodge cotangent data. On curves it yields Picard schemes; on abelian schemes it yields the dual family and exterior cohomology; on a given PEL or modular family it yields integral Hodge bundles and finite modules of forms.

The resulting toolkit is deliberately exact about its frontier. It proves the cohomological and representability consequences available from proper projective geometry and derived comparison. It does not assume later constructions of modular or PEL parameter spaces, nor does it turn completed data into algebraic objects without an existence theorem. Within that frontier, finiteness, semicontinuity, base change, formal functions, duality, and Hodge theory form one coherent mechanism.
