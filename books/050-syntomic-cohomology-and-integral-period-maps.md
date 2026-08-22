# Syntomic Cohomology and Integral Period Maps

## Contents

1. [The integral comparison problem](#1-the-integral-comparison-problem)
   - [Three cohomologies and one missing lattice](#11-three-cohomologies-and-one-missing-lattice)
   - [Standing hypotheses](#12-standing-hypotheses)
   - [What weight means](#13-what-weight-means)
   - [The route through the book](#14-the-route-through-the-book)
2. [The crystalline period sheaves](#2-the-crystalline-period-sheaves)
   - [Finite divided-power levels](#21-finite-divided-power-levels)
   - [The structure ideal and its filtration](#22-the-structure-ideal-and-its-filtration)
   - [Frobenius and divided Frobenius](#23-frobenius-and-divided-frobenius)
   - [Why a modified filtration is necessary](#24-why-a-modified-filtration-is-necessary)
3. [The weight-zero and weight-one complexes](#3-the-weight-zero-and-weight-one-complexes)
   - [Mapping fibers and conventions](#31-mapping-fibers-and-conventions)
   - [Weight zero](#32-weight-zero)
   - [Weight one](#33-weight-one)
   - [Change of Frobenius lift](#34-change-of-frobenius-lift)
4. [The local fundamental calculation](#4-the-local-fundamental-calculation)
   - [Divided-power exponential and logarithm](#41-divided-power-exponential-and-logarithm)
   - [The fixed points in weight zero](#42-the-fixed-points-in-weight-zero)
   - [The fixed points in weight one](#43-the-fixed-points-in-weight-one)
   - [Syntomic covers from monic equations](#44-syntomic-covers-from-monic-equations)
   - [Local surjectivity of the Frobenius differences](#45-local-surjectivity-of-the-frobenius-differences)
   - [The fundamental exact sequences](#46-the-fundamental-exact-sequences)
5. [Syntomic cohomology and its exact sequences](#5-syntomic-cohomology-and-its-exact-sequences)
   - [Hypercohomology](#51-hypercohomology)
   - [The long exact sequence](#52-the-long-exact-sequence)
   - [The two-term kernel-cokernel description](#53-the-two-term-kernel-cokernel-description)
   - [Pullback and reduction](#54-pullback-and-reduction)
6. [Weight zero as integral fixed-point theory](#6-weight-zero-as-integral-fixed-point-theory)
   - [Constant classes](#61-constant-classes)
   - [Connected bases and degree zero](#62-connected-bases-and-degree-zero)
   - [Degree one and finite etale torsors](#63-degree-one-and-finite-etale-torsors)
   - [An affine calculation](#64-an-affine-calculation)
7. [Weight one as Kummer theory](#7-weight-one-as-kummer-theory)
   - [The syntomic Kummer quasi-isomorphism](#71-the-syntomic-kummer-quasi-isomorphism)
   - [Units and root torsors](#72-units-and-root-torsors)
   - [Line bundles and the degree-two boundary](#73-line-bundles-and-the-degree-two-boundary)
   - [The first syntomic Chern class](#74-the-first-syntomic-chern-class)
8. [Integral period morphisms](#8-integral-period-morphisms)
   - [Generic fibers and nearby classes](#81-generic-fibers-and-nearby-classes)
   - [Construction in weights zero and one](#82-construction-in-weights-zero-and-one)
   - [The extendable-class theorem](#83-the-extendable-class-theorem)
   - [Functoriality and normalization](#84-functoriality-and-normalization)
9. [Products, symbols, and Chern classes](#9-products-symbols-and-chern-classes)
   - [Cup products of mapping fibers](#91-cup-products-of-mapping-fibers)
   - [Kummer symbols](#92-kummer-symbols)
   - [Compatibility of period maps with products](#93-compatibility-of-period-maps-with-products)
   - [Projective space and a divisor calculation](#94-projective-space-and-a-divisor-calculation)
10. [Smooth proper curves](#10-smooth-proper-curves)
    - [The filtered crystalline model](#101-the-filtered-crystalline-model)
    - [The weight-one exact sequence](#102-the-weight-one-exact-sequence)
    - [Picard classes and the Jacobian](#103-picard-classes-and-the-jacobian)
    - [Trace and duality](#104-trace-and-duality)
11. [Abelian schemes and degree one](#11-abelian-schemes-and-degree-one)
    - [The crystalline Hodge extension revisited](#111-the-crystalline-hodge-extension-revisited)
    - [Syntomic classes attached to torsion line bundles](#112-syntomic-classes-attached-to-torsion-line-bundles)
    - [Isogenies and division torsors](#113-isogenies-and-division-torsors)
    - [Polarizations and the weight-one pairing](#114-polarizations-and-the-weight-one-pairing)
12. [Finite-flat group schemes](#12-finite-flat-group-schemes)
    - [What compatibility can mean](#121-what-compatibility-can-mean)
    - [Characters and Cartier pairings](#122-characters-and-cartier-pairings)
    - [Exact sequences and boundary classes](#123-exact-sequences-and-boundary-classes)
    - [Finite-flat extension classes on the generic fiber](#124-finite-flat-extension-classes-on-the-generic-fiber)
13. [Limits and integral lattices](#13-limits-and-integral-lattices)
    - [Reduction from level $n+1$ to level $n$](#131-reduction-from-level-n1-to-level-n)
    - [Derived inverse limits](#132-derived-inverse-limits)
    - [The completed syntomic complexes](#133-the-completed-syntomic-complexes)
    - [Rationalization does not recover the lattice](#134-rationalization-does-not-recover-the-lattice)
14. [Descent, base change, and exactness](#14-descent-base-change-and-exactness)
    - [Syntomic descent](#141-syntomic-descent)
    - [Unramified change of the base](#142-unramified-change-of-the-base)
    - [Coefficient exact sequences](#143-coefficient-exact-sequences)
    - [A hypothesis ledger](#144-a-hypothesis-ledger)
15. [The low-weight integral comparison package](#15-the-low-weight-integral-comparison-package)
    - [The main theorem](#151-the-main-theorem)
    - [What the theorem does not say](#152-what-the-theorem-does-not-say)
    - [A reusable calculation protocol](#153-a-reusable-calculation-protocol)
    - [Conclusion](#154-conclusion)

## 1. The integral comparison problem

The guiding question is not merely how to compare two vector spaces after denominators have been inverted. It is how to recognize, inside generic cohomology, the classes which preserve an integral geometric model. This opening chapter isolates that question, fixes the low-weight normalization, and marks the exact good-reduction range in which it will be answered.

### 1.1 Three cohomologies and one missing lattice

Crystalline cohomology records a smooth special fiber together with its infinitesimal divided-power neighborhoods. Generic-fiber etale cohomology records finite covers and Galois descent after the residue characteristic has become invertible. Flat cohomology on an integral model records torsors which remain meaningful before that inversion. In low weight these three theories are linked by a remarkably concrete device: take a filtered crystalline object, compare Frobenius with the identity, and form a mapping fiber.

The need for a third theory is integral. After $p$ is inverted, a Frobenius module can often be compared with a rational Galois representation. That comparison does not specify which lattice in the representation extends over the valuation ring. Distinct lattices may have the same rational span, and a generic torsor may be ramified in a way which prevents any finite-flat extension. Syntomic cohomology is designed to retain the divisibility information which separates an extendable class from an arbitrary generic one.

Weight zero and weight one are the first two cases. Their coefficients are already familiar:

$$
\mathbf Z/p^n\mathbf Z
\qquad\text{and}\qquad
\mu_{p^n}.
$$

The first is finite etale even in residue characteristic $p$; the second is finite locally free but usually nonreduced on the special fiber. Thus weight zero is controlled by Artin--Schreier-type fixed points, while weight one is controlled by Kummer theory in the flat topology. The mapping-fiber construction explains why these apparently different coefficients arise from the same crystalline pattern.

Book 29 established fppf torsors, Kummer sequences, cup products, and finite-flat boundary maps. Book 34 supplied Cartier duality, evaluation, exactness, and character pushout for arbitrary finite locally free commutative groups. Book 48 constructed divided-power ideals, crystalline sites, crystals, and divided Frobenius. Book 49 supplied perfect crystalline complexes, Frobenius, base change, products, trace, and the degree-one theory of curves and abelian schemes. The schematic Weil pairing used with abelian torsion is the perfect finite-flat pairing of Book 35. We shall use precisely those results, with their hypotheses recalled when they enter. Everything specific to syntomic complexes and period morphisms is proved here.

### 1.2 Standing hypotheses

Fix a prime $p$, a perfect field $k$ of characteristic $p$, and

$$
V=W(k),\qquad V_n=V/p^nV,\qquad K=V[1/p].
$$

The Witt Frobenius is denoted by $\sigma$. Our main geometric object is a smooth separated $V$-scheme $X$ of finite presentation, with $p$-adic completion $\mathfrak X$. Write

$$
X_n=X\times_VV_n,\qquad
X_1=X\times_Vk,\qquad
X_K=X\times_VK
$$

for its finite levels, special fiber, and generic fiber. The completion organizes the compatible crystalline levels, while torsors and generic restriction are taken on $X$. Whenever global coherent or crystalline finiteness is used, $X$ is assumed proper.

The unramified choice $V=W(k)$ is substantive. It provides a canonical Frobenius on the base and gives the clean divisibility needed for weights $0$ and $1$. Ramified bases require additional divided-power envelopes and, in general, a ramification bound or logarithmic theory. No theorem below is silently extended to that setting.

We use the small $p$-adic syntomic site attached to $X$. Its algebraic objects are syntomic morphisms $U\to X$; the period sheaves evaluate their compatible reductions $U_m\to X_m$ and the divided-power thickenings of $U_1$. A morphism is called syntomic if it is flat, of finite presentation, and locally on the source factors as a regular immersion into a smooth scheme over the target. A covering is jointly surjective and consists of syntomic morphisms. This convention is important: the coefficient sheaves below classify torsors on the integral model, not torsors on the special fiber alone. Etale covers are syntomic, and the finite-flat root covers used in Kummer theory are syntomic; Section 4.4 proves this for root covers from their monic equations, with no cotangent-complex input. For the two coefficients used here, $\mathbf Z/p^n$ and $\mu_{p^n}$, degree-one torsors have the same classification in the syntomic and fppf topologies; the comparison is proved in Theorem 7.1. No such comparison is asserted for an arbitrary finite locally free group scheme without the local-complete-intersection hypothesis.

Complexes are cohomological. For a map $f:A^\bullet\to B^\bullet$, the complex

$$
\operatorname{Fib}(f)=\operatorname{Cone}(f)[-1]
$$

fits into the distinguished triangle

$$
\operatorname{Fib}(f)\longrightarrow A^\bullet
\xrightarrow{f}B^\bullet\longrightarrow
\operatorname{Fib}(f)[1].
$$

This fixes every sign in the long exact sequences below.

### 1.3 What weight means

On a smooth lift, the first step of the Hodge filtration on a de Rham complex is

$$
F^1\Omega^\bullet=
[p\mathcal O\xrightarrow d\Omega^1\xrightarrow d\Omega^2\to\cdots]
$$

when the special fiber is embedded by $(p)$. Frobenius carries a $q$-form into a multiple of $p^q$. In weight $r$, one asks to divide Frobenius by $p^r$ on the $r$th filtered part. The range $r=0,1$ is special because the required divisibility is elementary and because the corresponding integral coefficients are geometric finite-flat group schemes.

Our convention is covariant on coefficients:

$$
\mathbf Z_p(0)=\mathbf Z_p,\qquad
\mathbf Z_p(1)=\varprojlim_n\mu_{p^n}.
$$

The arithmetic Frobenius on the crystalline weight-one line is $p\sigma$. Thus dividing it by $p$ produces the operator whose fixed points correspond to roots of unity. A different convention for Tate twists would reverse some displayed powers of $p$; the present choice agrees with the trace normalization of Book 49.

Weight is not merely a label on an eventual rational representation. It controls an integral filtration and the exact power of $p$ which may be divided out. Forgetting the filtration but retaining the rational Frobenius destroys the construction.

### 1.4 The route through the book

The argument has four stages. First we construct the crystalline structure sheaves and the honest divided Frobenius in weights zero and one. Second we prove the local fundamental exact sequences by Artin--Schreier equations and the divided-power logarithm. Third we globalize by mapping fibers, obtaining exact sequences and period morphisms. Finally we apply the result to curves, abelian schemes, and finite-flat torsors, where it identifies precisely the generic classes which come from the integral model.

The central diagram is

$$
\begin{array}{ccc}
\text{filtered crystalline complex}&\xrightarrow{1-\varphi_r}&
\text{crystalline complex}\\
\downarrow&&\downarrow\\
\text{finite-flat coefficient}&\longrightarrow&
\text{generic etale coefficient}.
\end{array}
$$

The top row defines syntomic cohomology. The left column is the fundamental exact sequence. The bottom arrow is restriction to the generic fiber. Proving that this square is canonical and compatible with boundaries is the integral period comparison in low weight.

## 2. The crystalline period sheaves

To compare Frobenius with the identity, both operators must act on one intrinsic filtered object. This chapter constructs that object from completed divided-power envelopes and explains the sole delicate operation in weight one: dividing Frobenius by $p$ without making the answer depend on a lift from one finite level to the next.

### 2.1 Finite divided-power levels

The syntomic complex is built locally and then sheafified. Let $U\to X$ be an object of the small $p$-adic syntomic site and put $U_1=U\times_Vk$. Choose, locally on $U_1$, a closed immersion

$$
U_1\hookrightarrow Z_n
$$

into a scheme smooth over $V_n$. Let $D_n(U,Z)$ be the divided-power envelope, compatible with the canonical divided powers on $(p)\subset V_n$, of the defining ideal. The envelope and its de Rham complex are independent of the chosen embedding after passage through the diagonal-envelope comparisons of Book 48.

For the period sheaves we use the mixed completion of the envelope with respect to the neighborhoods $p^a+\mathcal J^{[b]}$, equivalently the compatible system of its finite $p$-power and PD-order quotients. This is the topology in which divided-power Taylor, logarithm, and exponential series are evaluated. Write

$$
\mathscr O_n^{\mathrm{cr}}(U)
=\Gamma(D_n(U,Z),\mathcal O_{D_n})
$$

locally, with descent on overlaps. More invariantly, $\mathscr O_n^{\mathrm{cr}}$ is the direct image of the crystalline structure sheaf from the crystalline site to the syntomic site. Its defining ideal is

$$
\mathscr J_n=\ker(\mathscr O_n^{\mathrm{cr}}\to\mathcal O_{X_1}),
$$

and $\mathscr J_n^{[r]}$ denotes its $r$th divided-power filtration. The notation does not assert that one chosen envelope is final; the sheaf is obtained by the crystalline descent which compares all embeddings.

The transition maps

$$
\mathscr O_{n+1}^{\mathrm{cr}}\longrightarrow
\mathscr O_n^{\mathrm{cr}}
$$

are surjective locally. Indeed a smooth presentation and its divided-power envelope may be reduced modulo $p^n$, and every divided monomial has a lift one level higher. The same holds for $\mathscr J^{[r]}$ after the modified filtration of Section 2.4 is used. Surjectivity is important when inverse limits are formed; it is not a decorative finiteness assertion.

### 2.2 The structure ideal and its filtration

The filtered crystalline de Rham complex in weight $r$ is obtained by assigning divided-power order $r-q$ in de Rham degree $q$:

$$
\mathscr J_n^{[r-\bullet]}\Omega^\bullet:
\mathscr J_n^{[r]}\longrightarrow
\mathscr J_n^{[r-1]}\otimes\Omega^1\longrightarrow
\mathscr J_n^{[r-2]}\otimes\Omega^2\longrightarrow\cdots,
\tag{2.1}
$$

where $\mathscr J^{[a]}=\mathscr O^{\mathrm{cr}}$ for $a\leq0$. The differential is well defined because

$$
d(x^{[m]})=x^{[m-1]}dx.
$$

For the two weights at issue,

$$
\begin{aligned}
r=0:&\quad
\mathscr O_n^{\mathrm{cr}}\to
\mathscr O_n^{\mathrm{cr}}\otimes\Omega^1\to\cdots,\\
r=1:&\quad
\mathscr J_n\to
\mathscr O_n^{\mathrm{cr}}\otimes\Omega^1\to
\mathscr O_n^{\mathrm{cr}}\otimes\Omega^2\to\cdots.
\end{aligned}
\tag{2.2}
$$

On the global smooth lift $X/V$, crystalline--de Rham comparison identifies the completed objects with the ordinary de Rham complex and its first integral filtered subcomplex

$$
F^1\Omega^\bullet_{X/V}
=[p\mathcal O_X\longrightarrow\Omega^1_{X/V}\longrightarrow\cdots].
\tag{2.3}
$$

At coefficient level $n$, the first term means the derived reduction of this lattice: the abstract copy $p\mathcal O_X/p^{n+1}\mathcal O_X$, mapped to $\mathcal O_{X_n}$ by inclusion. It is not the literal image ideal $p\mathcal O_{X_n}$. The modified filtration of Section 2.4 is the intrinsic envelope-theoretic realization of that derived reduction.

For a local embedding with a larger ideal, (2.1), not the simplified formula (2.3), is the intrinsic definition.

The filtration is multiplicative:

$$
\mathscr J^{[a-\bullet]}\Omega^\bullet
\otimes
\mathscr J^{[b-\bullet]}\Omega^\bullet
\longrightarrow
\mathscr J^{[a+b-\bullet]}\Omega^\bullet.
\tag{2.4}
$$

This follows from $\mathscr J^{[i]}\mathscr J^{[j]}\subseteq\mathscr J^{[i+j]}$ and the wedge product of forms. It will produce cup products on syntomic complexes.

### 2.3 Frobenius and divided Frobenius

The Frobenius of $X_1$ and Witt Frobenius on $V_n$ induce a semilinear endomorphism

$$
\varphi:\mathscr O_n^{\mathrm{cr}}\longrightarrow
\mathscr O_n^{\mathrm{cr}}.
$$

Locally, choose a Frobenius lift on a smooth embedding. The universal property of the divided-power envelope extends it. Two choices agree in the derived construction because their difference factors through the divided-power diagonal, where Taylor transport gives a homotopy. This is the same independence mechanism used to construct crystalline Frobenius in Book 49.

If $x$ lies in the defining ideal, then $\varphi(x)$ is divisible by $p$. To see the basic case, write a local lift as $x$ modulo the special fiber. Since $\varphi$ reduces to $p$th power,

$$
\varphi(x)=x^p+p a=p\bigl((p-1)!x^{[p]}+a\bigr).
\tag{2.5}
$$

For sums and divided monomials, the divided-power identities give the same conclusion. Likewise $d\varphi$ is divisible by $p$, so on the weight-one de Rham complex one may divide Frobenius by $p$ degreewise. In degree $q\geq1$, the pullback of a $q$-form is divisible by $p^q$, hence certainly by $p$.

At an infinite $p$-torsion-free level this defines

$$
\varphi_1=\frac{\varphi}{p}:F^1\mathscr O^{\mathrm{cr}}\Omega^\bullet
\longrightarrow\mathscr O^{\mathrm{cr}}\Omega^\bullet.
\tag{2.6}
$$

At a finite level, however, division by $p$ is ambiguous: if an element is known only modulo $p^n$, two lifts modulo $p^{n+1}$ can yield quotients differing modulo $p^n$. The next section repairs this point.

### 2.4 Why a modified filtration is necessary

Finite-level division is defined one level higher, where its ambiguity can be measured. For $s\geq1$, let $E_{n,s}$ be the subsheaf of $\mathscr J_{n+s}$ consisting of sections $x$ for which $\varphi(x)$ belongs to $p\mathscr O_{n+s}^{\mathrm{cr}}$, and set

$$
\mathscr J_n^{\langle1\rangle}
=E_{n,s}/p^n\mathscr J_{n+s}.
\tag{2.7}
$$

Here $p^n\mathscr J_{n+s}\subseteq E_{n,s}$ by (2.5). The quotient is an abstract source module, equipped with a structural map

$$
\iota_n:\mathscr J_n^{\langle1\rangle}
\longrightarrow\mathscr O_n^{\mathrm{cr}}
$$

induced by inclusion followed by reduction. It need not be a subsheaf of $\mathscr O_n^{\mathrm{cr}}$. For example, on the smooth lift it is $p\mathcal O_X/p^{n+1}\mathcal O_X$, while $\iota_n$ is multiplication by $p$ after identifying this abstract module with $\mathcal O_{X_n}$. This is exactly the extra digit which the image ideal $p\mathcal O_{X_n}$ would discard.

The quotient in (2.7) is independent of $s\geq1$. In weight one, formula (2.5), followed by the PD sum and product identities, in fact shows $E_{n,s}=\mathscr J_{n+s}$; retaining $E_{n,s}$ in the notation records the divisibility needed to define the quotient map. Locally, a syntomic object is a regular immersion into a smooth $V$-scheme. The divided-power monomials in a regular sequence filter its envelope with flat graded pieces, so reduction from level $n+s+1$ to $n+s$ identifies $\mathscr J_{n+s+1}/p^n\mathscr J_{n+s+1}$ with $\mathscr J_{n+s}/p^n\mathscr J_{n+s}$. Thus the transition maps induce isomorphisms on (2.7), proving stabilization without treating an image ideal as the filtered lattice.

More generally $\mathscr J_n^{\langle r\rangle}$ would require divisibility of $\varphi(x)$ by $p^r$, but only $r=0,1$ is used. Put

$$
\mathscr J_n^{\langle0\rangle}=\mathscr O_n^{\mathrm{cr}}.
$$

If $x$ is represented in (2.7), choose $\widetilde x\in E_{n,s}$ and set

$$
\varphi_1(x)=\frac{\varphi(\widetilde x)}p\pmod {p^n}.
\tag{2.8}
$$

If the representative changes by $p^ny$ with $y\in\mathscr J_{n+s}$, then (2.5) writes $\varphi(y)=pz$, so the quotient changes by $p^nz$ and has the same image modulo $p^n$. Together with stabilization, this proves that (2.8) is independent of every choice. Notice that divisibility of an element already reduced in $\mathscr O_n^{\mathrm{cr}}$ would not suffice: its quotient would be defined only modulo $p^{n-1}$. The abstract quotient one level higher is what retains the missing digit. We use the modified object at every prime, including $p=2$, so no exceptional-prime cancellation is hidden.

The full weight-one filtered de Rham complex is denoted

$$
\mathscr J_n^{\langle1-\bullet\rangle}\Omega^\bullet.
\tag{2.9}
$$

Its degree-zero term is (2.7), and its structural map to the ordinary crystalline de Rham complex is $\iota_n$. In degree $q\geq1$ the source is $\mathscr O_n^{\mathrm{cr}}\otimes\Omega^q$ and the divided Frobenius map is $p^{-1}\varphi^*$. Frobenius pullback of a $q$-form is divisible by $p^q$, so this quotient is integral. The map $\varphi_1$ is a chain map because $d\varphi=p\varphi_1d$ in degree zero and the degreewise divisibilities are compatible with the de Rham differential.

## 3. The weight-zero and weight-one complexes

The period sheaves become cohomology only after their filtration and Frobenius are assembled into a complex. Mapping fibers are the natural assembly: they retain both fixed elements and failures of surjectivity, and they behave well under descent and derived global sections. The two low weights differ only in the filtered source and the normalization of Frobenius.

### 3.1 Mapping fibers and conventions

The syntomic complex measures simultaneous filtration and Frobenius fixedness. For $r=0,1$, define on the small $p$-adic syntomic site of $X$

$$
\mathscr S_n(r)=
\operatorname{Fib}\left(
1-\varphi_r:
\mathscr J_n^{\langle r-\bullet\rangle}\Omega^\bullet
\longrightarrow
\mathscr O_n^{\mathrm{cr}}\Omega^\bullet
\right),
\tag{3.1}
$$

where $\varphi_0=\varphi$ and the symbol $1$ in weight one means the structural map $\iota_n$ in degree zero and the ordinary filtered inclusion in positive degrees. When only the sheaf-level two-term presentation is needed, the crystalline Poincare lemma contracts the de Rham directions and gives

$$
\mathscr S_n(r)\simeq
[\mathscr J_n^{\langle r\rangle}
\xrightarrow{1-\varphi_r}
\mathscr O_n^{\mathrm{cr}}],
\tag{3.2}
$$

with the first term in degree $0$ and the second in degree $1$. Formula (3.2) is a quasi-isomorphism, not an equality of the filtered de Rham complexes before contraction.

The fiber convention shows immediately that a section in degree zero is a filtered crystalline section fixed by divided Frobenius. A degree-one class is a crystalline section modulo Frobenius differences, together with any geometric gluing contribution. The fundamental calculation will show that the apparent cokernel vanishes locally in the syntomic topology.

### 3.2 Weight zero

In weight zero no filtration is imposed:

$$
\mathscr S_n(0)=
\operatorname{Fib}(1-\varphi:
\mathscr O_n^{\mathrm{cr}}\Omega^\bullet
\to\mathscr O_n^{\mathrm{cr}}\Omega^\bullet).
\tag{3.3}
$$

The expected fixed coefficient is $\mathbf Z/p^n\mathbf Z$. Over the residue field this is the familiar fact that the solutions of $a^p-a=0$ are the prime-field elements. Over a divided-power thickening, successive approximation lifts those fixed points uniquely modulo the freedom already present in $\mathbf Z/p^n\mathbf Z$.

One should not replace $1-\varphi$ by $p^n-\varphi$. Weight zero means that Frobenius has slope zero and is compared directly with the identity. Multiplying the identity by $p^n$ would change both the fixed points and the rational normalization.

### 3.3 Weight one

Weight one inserts the first filtration and divides Frobenius once:

$$
\mathscr S_n(1)=
\operatorname{Fib}(1-\varphi_1:
\mathscr J_n^{\langle1-\bullet\rangle}\Omega^\bullet
\to\mathscr O_n^{\mathrm{cr}}\Omega^\bullet).
\tag{3.4}
$$

The expected coefficient is $\mu_{p^n}$. The reason is visible from logarithms. For a root of unity $u$ infinitesimally close to $1$,

$$
\varphi(\log u)=\log(u^p)=p\log u,
$$

so $\log u$ is fixed by $\varphi_1$. Conversely a fixed logarithm exponentiates to a root of unity at the finite level. This argument uses divided-power exponential and logarithm; ordinary power series would introduce forbidden denominators.

The shift in (3.4) is essential. Without it the kernel would be a set of logarithms, not a coefficient placed in degree zero. With the mapping-fiber convention, the Kummer coefficient appears in the same cohomological degrees as its flat cohomology.

### 3.4 Change of Frobenius lift

The local formula for $\varphi_r$ uses a Frobenius lift on a smooth embedding, so independence must be proved before the complex is intrinsic.

**Proposition 3.1.** Two local Frobenius lifts induce canonically chain-homotopic maps on the crystalline de Rham model, and the homotopy preserves the weight-zero and modified weight-one filtrations. Consequently $\mathscr S_n(0)$ and $\mathscr S_n(1)$ are independent, up to canonical quasi-isomorphism, of all local embeddings and Frobenius lifts.

**Proof strategy.** Two lifts coincide on the special fiber, so their pair factors through the divided-power envelope of the diagonal. Taylor expansion along that envelope supplies the homotopy. Divisibility by $p$ in weight one must be checked term by term.

**Proof.** Let $\varphi$ and $\psi$ be two lifts on a smooth algebra with local coordinates $t_1,\ldots,t_d$. Then

$$
\varphi(t_i)-\psi(t_i)=p a_i
$$

for some $a_i$. The standard de Rham homotopy between pullbacks along infinitesimally close maps is obtained by integrating along the divided-power segment joining them. On a function $f$ its first term is

$$
H(df)=\sum_i a_i\frac{\partial f}{\partial t_i},
$$

and higher Taylor terms use divided monomials in the $p a_i$. The identity

$$
\varphi^*-\psi^*=dH+Hd
$$

follows from the divided Taylor formula and may be checked on coordinates, then on products by the Leibniz rule. Every positive Taylor difference contains a factor $p$. Thus after restricting to $F^1$, division of the Frobenius maps by $p$ leaves an integral homotopy. The modified filtration guarantees the same conclusion at finite level and at $p=2$.

For three lifts, the homotopies agree up to the second homotopy obtained from the triple diagonal envelope. Hence the comparisons satisfy the cocycle condition in the derived category. Embedding independence follows by applying the same construction to the product of two embeddings. Taking mapping fibers preserves these quasi-isomorphisms. $\square$

The proposition does not choose a globally preferred Frobenius lift. It proves that no such choice is needed.

## 4. The local fundamental calculation

The definition of a mapping fiber does not yet reveal its coefficient. The decisive local task is to compute the kernel and cokernel of the Frobenius difference. Weight zero reduces to derivative-one additive equations; weight one converts multiplicative torsion into additive fixed points through divided-power logarithms. Once local surjectivity is proved, the abstract complexes become the familiar finite-flat sheaves.

### 4.1 Divided-power exponential and logarithm

Let $(A,I,\gamma)$ be a ring with a nilpotent divided-power ideal. Define

$$
\operatorname{Exp}_{\mathrm{PD}}(x)
=\sum_{m\geq0}x^{[m]},
\qquad
\operatorname{Log}_{\mathrm{PD}}(1+x)
=\sum_{m\geq1}(-1)^{m-1}(m-1)!x^{[m]}.
\tag{4.1}
$$

At a PD-nilpotent level the sums are finite. In the mixed completed envelopes of Section 2.1, their tails tend to zero in divided-power order, so both series converge. Reduction to a finite $p$-level is always taken after this completed evaluation; ordinary nilpotence alone would not make the exponential a finite sum.

**Lemma 4.1.** The maps in (4.1) are inverse group isomorphisms

$$
(I,+)\xrightarrow{\sim}(1+I,\cdot).
\tag{4.2}
$$

They commute with PD morphisms and satisfy

$$
\operatorname{Exp}_{\mathrm{PD}}(x+y)
=\operatorname{Exp}_{\mathrm{PD}}(x)
\operatorname{Exp}_{\mathrm{PD}}(y),
\tag{4.3}
$$

$$
\operatorname{Log}_{\mathrm{PD}}(uv)
=\operatorname{Log}_{\mathrm{PD}}(u)
+\operatorname{Log}_{\mathrm{PD}}(v).
\tag{4.4}
$$

**Proof.** Expand both sides of (4.3). The coefficient of $x^{[a]}y^{[b]}$ on the left is $1$ by the divided-power addition formula, and on the right it is also $1$. For (4.4), substitute the product expansion

$$
(1+x)(1+y)=1+(x+y+xy)
$$

and repeatedly use the addition and product axioms. In total divided-power degree $m$, the desired cancellation is the integer coefficient identity obtained by partitioning an $m$-element set according to the nonempty blocks contributed by $x$, $y$, and $xy$. Equivalently, it is the coefficient identity in the formal relation $\log((1+X)(1+Y))=\log(1+X)+\log(1+Y)$ after multiplying the degree-$m$ coefficient by $m!$; every resulting coefficient is an integer, so no cancellation in $A$ is used.

The same coefficient calculation for the formal compositions $\log(\exp X)$ and $\exp(\log(1+X))$ gives respectively $X$ and $1+X$: in degree $m>1$, the signed sum over ordered set partitions is zero, while in degree one it is one. These are identities over $\mathbf Z$ among divided monomials, so they remain valid in rings with torsion. Convergence in the mixed completion permits termwise evaluation. Naturality is immediate. $\square$

If $\varphi$ is a PD-compatible Frobenius, naturality gives

$$
\varphi(\operatorname{Log}_{\mathrm{PD}}u)
=\operatorname{Log}_{\mathrm{PD}}(\varphi(u)).
\tag{4.5}
$$

This is the bridge between multiplicative torsion and divided Frobenius.

### 4.2 The fixed points in weight zero

**Lemma 4.2.** On the small syntomic site,

$$
\ker(1-\varphi:\mathscr O_n^{\mathrm{cr}}
\to\mathscr O_n^{\mathrm{cr}})
=\mathbf Z/p^n\mathbf Z.
\tag{4.6}
$$

**Proof strategy.** Reduce first modulo the divided-power ideal and $p$, where the equation is $a^p=a$. Then lift through successive square-zero layers.

**Proof.** Work first on a finite mixed quotient by $p^n$ and by sufficiently high divided-power order. Filter it by the combined $p$-adic and positive divided-power order. On the quotient by the positive part and by $p$, fixedness is the equation

$$
a^p-a=0.
$$

The algebra adjoining a solution is finite etale because the derivative is $-1$, so syntomically locally the solutions are precisely the $p$ constant sections in $\mathbf F_p$.

There are two kinds of successive layer. On a coefficient layer, write a lift as $c+p^my$ modulo $p^{m+1}$. Since Witt Frobenius fixes the integer $c$, fixedness reduces modulo $p$ to $y^p-y=0$; the next digit is therefore locally an element of $\mathbf F_p$. On a positive divided-power layer, (2.5) and the product formula show that Frobenius strictly raises the combined filtration. Hence its induced map on the first nonzero associated-graded layer is nilpotent. If a fixed element has zero coefficient digits, its initial positive graded term $z$ satisfies $z=\bar\varphi(z)$; iterating until the nilpotence exponent gives $z=0$. Induction removes every positive layer.

The fixed sections at the finite mixed quotient are thus exactly the locally constant Witt integers modulo $p^n$. Passing through the separated mixed completion introduces no new fixed section, since a nonzero difference would have a first nonzero finite quotient. This proves (4.6). $\square$

The conclusion is sheaf-theoretic. On global sections a base may have several connected components, in which case one obtains locally constant functions with values in $\mathbf Z/p^n\mathbf Z$.

### 4.3 The fixed points in weight one

There is a canonical crystalline logarithm map

$$
\lambda_n:\mu_{p^n}\longrightarrow
\mathscr J_n^{\langle1\rangle},
\qquad
u\longmapsto\ell_n(u),
\tag{4.7}
$$

constructed as follows. On a finite mixed quotient, only finitely many divided powers enter the logarithm. Syntomically locally, choose a finite root tower long enough for that quotient,

$$
u=u_n,\qquad u_{m+1}^p=u_m\quad(n\leq m\leq N).
$$

Such extensions are obtained successively by the finite free root covers $T^p-u_m$. Choose multiplicative representatives $\widetilde u_m$ in the corresponding divided-power envelopes. One must not claim that $\widetilde u_m-1$ lies in $\mathscr J$: on a nonreduced special fiber the root itself can remain infinitesimal. Instead use the Frobenius defects

$$
d_m=\varphi(\widetilde u_{m+1})\widetilde u_m^{-1}\in1+\mathscr J.
$$

The inclusion holds because both factors have the same image $u_{m+1}^p=u_m$ on the special-fiber object. Apply the finite truncation of $\operatorname{Log}_{\mathrm{PD}}$ to the $d_m$ and descend the resulting additive recursion along the root tower. This produces an element of the abstract quotient (2.7); the terminal term is invisible once $N$ exceeds the chosen divided-power order. A longer tower gives the same element because the added defects contribute either a multiple of $p^n\mathscr J$ or divided-power order beyond the quotient. Two towers acquire a common refinement, and (4.4) shows that changing representatives changes the result by the corresponding additive coboundary. The constructions are compatible as the mixed quotient varies, so they define $\ell_n(u)$ in the completed sheaf. Only finitely many root adjunctions occur in each sheaf-local calculation; no infinite cover is being treated as a syntomic object.

**Lemma 4.3.** The logarithm identifies

$$
\mu_{p^n}\xrightarrow{\sim}
\ker(1-\varphi_1:
\mathscr J_n^{\langle1\rangle}\longrightarrow
\mathscr O_n^{\mathrm{cr}}).
\tag{4.8}
$$

**Proof.** On each finite quotient, Frobenius shifts the chosen finite root tower. The terminal ambiguity is invisible by the choice of its length, and therefore

$$
\varphi(\ell_n(u))=p\ell_n(u),
$$

so $\varphi_1(\ell_n(u))=\ell_n(u)$. This proves that (4.7) lands in the kernel.

Conversely, let $x$ be fixed by $\varphi_1$. Choose a representative $\widetilde x$ one level higher as in (2.7), and put $v=\operatorname{Exp}_{\mathrm{PD}}(\widetilde x)$; all following equalities are read in the level-$n$ quotient. Changing the representative by $p^n\mathscr J$ changes the logarithm by zero in the modified source and hence does not change the resulting coefficient section. Fixedness gives

$$
\varphi(v)=\operatorname{Exp}_{\mathrm{PD}}(\varphi\widetilde x)
=\operatorname{Exp}_{\mathrm{PD}}(p\widetilde x)=v^p.
$$

The equation says that the successive Frobenius pullbacks of $v$ form the same finite root data used in the construction of $\ell_n$. Evaluate $v$ on the tautological level-$n$ thickening of the syntomic object and call the resulting unit $u$. Since multiplication of $x$ by $p^n$ is zero in the modified source, Lemma 4.1 gives

$$
u^{p^n}=\operatorname{Exp}_{\mathrm{PD}}(p^nx)=1.
$$

Thus $u$ belongs to $\mu_{p^n}$. Lemma 4.1 shows on every finite mixed quotient that the two constructions are inverse. Compatibility of those inverses gives the assertion on the completion, and descent makes it canonical. The modified filtration guarantees throughout that $\varphi(x)/p$ is an actual level-$n$ section rather than a quotient defined only modulo $p^{n-1}$. $\square$

This proof retains the nonreduced structure of $\mu_{p^n}$. Counting geometric roots would give only the identity in characteristic $p$ and would miss the theorem.

### 4.4 Syntomic covers from monic equations

The syntomic topology is used through finite-flat root adjunctions, so the fact that such adjunctions produce syntomic covers must be proved rather than invoked. This section isolates the argument. Recall the working notion of Section 1.2: a morphism of $V$-schemes is **syntomic** if it is flat, of finite presentation, and locally on the source factors as a regular immersion into a smooth scheme over the target; a family of morphisms is a **syntomic cover** if it is jointly surjective and each member is syntomic.

**Lci lemma.** Let $S$ be a scheme and let $u\in\Gamma(S,\mathcal O_S)^\times$ be a unit. Then

$$
P_u=\operatorname{Spec}\mathcal O_S[T]/\bigl(T^{p^n}-u\bigr)
$$

is finite locally free of rank $p^n$ over $S$, the morphism $P_u\to S$ is syntomic, and it is surjective. Moreover every fppf torsor under $\mu_{p^n}$ is Zariski-locally on its base of this form, and is therefore itself a syntomic cover of its base. The constant group $\mathbf Z/p^n$ and its torsors are finite etale, hence syntomic.

**Proof.** Because $T^{p^n}-u$ is monic, division with remainder makes $\mathcal O_S[T]/(T^{p^n}-u)$ a free module of rank $p^n$ over $\mathcal O_S$ with basis $1,T,\ldots,T^{p^n-1}$: for any polynomial, replace the leading term $aT^m$, $m\ge p^n$, by $a\,uT^{m-p^n}$, which lowers the degree. So $P_u\to S$ is finite locally free, hence flat and of finite presentation, and of positive constant rank; a finite flat morphism of positive rank hits every point of the target, since its fibers have degree $p^n>0$, so the morphism is surjective.

It remains to see the local complete intersection property. The polynomial $T^{p^n}-u$ is monic, and a monic polynomial is never a zero divisor in a polynomial ring: multiplication by it shifts the filtration by degree, so it is injective. Hence the single equation $T^{p^n}-u=0$ is a regular sequence of length one in the polynomial algebra $\mathcal O_S[T]$, which is smooth over $\mathcal O_S$. Thus $P_u\to S$ is, Zariski-locally on $S$, the regular immersion of a hypersurface into the smooth $S$-scheme $\mathbf A^1_S$: exactly the factorization required by the definition, with no cotangent-complex input. Therefore $P_u\to S$ is syntomic.

For the torsor statement, Book 29 classifies fppf torsors under $\mu_{p^n}$ by pairs $(L,\varphi)$ consisting of a line bundle $L$ and an isomorphism $\varphi:L^{\otimes p^n}\xrightarrow{\sim}\mathcal O_X$; the torsor is the relative spectrum of the graded algebra $\mathcal O_X\oplus L^{-1}\oplus\cdots\oplus L^{-(p^n-1)}$. Choose a local frame $e$ of $L$ and put $\varphi(e^{\otimes p^n})=c$. Over that same Zariski open, multiplication by powers of a root coordinate identifies the graded algebra with $\mathcal O_X[T]/(T^{p^n}-c^{-1})$, which is exactly the scheme $P_u$ analyzed above with $u=c^{-1}$. Since being finite locally free and locally a regular immersion into a smooth scheme are Zariski-local properties of the morphism, an arbitrary $\mu_{p^n}$-torsor is syntomic over its base, and being finite locally free of positive rank it is surjective; as a torsor, its own total space trivializes it. For $\mathbf Z/p^n$, the group scheme is a disjoint union of copies of the base and both statements are immediate. $\square$

Two consequences are recorded for repeated use. First, adjoining a root of a monic equation to any algebra returns a finite free extension: the free basis above is compatible with base change along an arbitrary morphism. Second, a successive adjunction of finitely many roots of monic equations is again covered by the lemma layer by layer, because each layer is flat and of finite presentation over the previous one and a composite of regular immersions into smooth schemes is presented by the concatenated regular sequence. Both facts are used, without further comment, in the refinement arguments below.

### 4.5 Local surjectivity of the Frobenius differences

Identifying kernels is only half of an exact sequence. We must prove that $1-\varphi_r$ is locally surjective in the syntomic topology.

**Lemma 4.4.** For $r=0,1$, the morphism

$$
1-\varphi_r:\mathscr J_n^{\langle r\rangle}
\longrightarrow\mathscr O_n^{\mathrm{cr}}
\tag{4.9}
$$

is an epimorphism of sheaves on the small syntomic site.

**Proof strategy.** Filter source and target simultaneously by powers of $p$ and divided-power order. In weight zero the graded lifting equations have invertible derivative and give finite-etale covers. In weight one the extra source digit instead produces monic $p$-power equations; by the lci lemma of Section 4.4 their root algebras are syntomic over the previous layer. The finitely many generators of a local PD presentation solve all divided monomials compatibly.

**Proof.** Work locally with a regular immersion into a smooth algebra, choose its finite regular sequence of generators, and first pass to a finite mixed quotient. Filter source and target by the combined $p$-adic and divided-power order. In weight zero, every associated-graded correction module is finite locally free and the equation has the form

$$
z_i-F_i(z_1,\ldots,z_d)=a_i\qquad(1\leq i\leq d).
\tag{4.10a}
$$

Here each $F_i$ is an additive $p$th-power polynomial. The resulting map $1-F$ of vector groups is finite etale: its differential is the identity, its geometric fibers are translates of its finite kernel, and the monic coordinate equations bound their degree by $p^d$. Its image is an open subgroup of a connected vector group and hence the whole group. It is therefore a finite-etale epimorphism. In the first layer this is the familiar equation

$$
x-x^p=b.
\tag{4.10b}
$$

Weight one is different because the symbol $1$ is the structural map $\iota_n$. On the extra coefficient digit, $\iota_n$ vanishes modulo $p$, whereas divided Frobenius is the $p$th-power map. The first equation is therefore, up to a unit,

$$
z^p=a.
\tag{4.10c}
$$

For a regular-immersion generator, (2.5) adds terms depending only on earlier divided-power order. Ordering the regular generators and then the divided monomials consequently makes the system triangular, with equations either (4.10a) or a monic equation $z^p+bz=a$ in the current variable. Adjoining their roots successively gives a finite free algebra: division by a monic polynomial supplies the free basis. The equations form a regular sequence in that free algebra, so the resulting faithfully flat cover is a local complete intersection, hence syntomic by the lci lemma of Section 4.4. This includes the purely inseparable root covers which weight one genuinely needs.

Order the finitely many coefficient layers. Suppose a solution has been found modulo the next layer. Its defect lies in a square-zero graded module. The preceding finite-etale or finite-free root algebra supplies a correction, and triangularity ensures that the correction does not disturb earlier layers. A finite succession of syntomic refinements therefore solves every coefficient-layer equation.

No infinite tower of covers is needed for the divided-power completion. The local PD algebra is generated by the divided monomials in the same finite regular sequence. Once roots for those generators and the finitely many coefficient digits have been adjoined, the PD identities determine the correction in every higher monomial. Equivalently, on the residual positive-order part the triangular operator has continuous inverse obtained, on each strictly order-raising block, from

$$
1+\bar\varphi_r+\bar\varphi_r^2+\cdots.
\tag{4.11}
$$

The series is finite on every divided-power quotient and hence converges in the mixed completion. It corrects the residual defect on the same finite syntomic refinement. This produces an exact solution of (4.9) and proves sheaf surjectivity. $\square$

Weight zero uses the etale part of the syntomic topology, while weight one also uses its finite-flat complete-intersection covers. Zariski localization alone need solve neither (4.10b) nor (4.10c).

### 4.6 The fundamental exact sequences

Combining the kernel and surjectivity calculations gives the local theorem on which the rest of the book rests.

**Theorem 4.5 (low-weight fundamental exact sequences).** On the small $p$-adic syntomic site of $X$, there are natural short exact sequences

$$
0\longrightarrow\mathbf Z/p^n\mathbf Z
\longrightarrow\mathscr O_n^{\mathrm{cr}}
\xrightarrow{1-\varphi}\mathscr O_n^{\mathrm{cr}}
\longrightarrow0,
\tag{4.12}
$$

and

$$
0\longrightarrow\mu_{p^n}
\xrightarrow{\lambda_n}
\mathscr J_n^{\langle1\rangle}
\xrightarrow{1-\varphi_1}
\mathscr O_n^{\mathrm{cr}}
\longrightarrow0.
\tag{4.13}
$$

Consequently there are canonical quasi-isomorphisms

$$
\mathbf Z/p^n\mathbf Z\xrightarrow{\sim}\mathscr S_n(0),
\qquad
\mu_{p^n}\xrightarrow{\sim}\mathscr S_n(1).
\tag{4.14}
$$

**Proof.** Exactness at the first two nonzero terms is Lemmas 4.2 and 4.3. Sheaf surjectivity is Lemma 4.4. A two-term complex whose differential is surjective has cohomology only in degree zero, equal to its kernel. The crystalline Poincare comparison from (3.1) to (3.2) then gives (4.14). Naturality follows from naturality of Frobenius, divided-power logarithm, and the local lifting equations. $\square$

The theorem is integral and includes $p=2$ because weight one was defined with $\mathscr J^{\langle1\rangle}$. If the unmodified ideal is used at $p=2$, the statement requires an additional divisibility argument and is not asserted here.

## 5. Syntomic cohomology and its exact sequences

Local exactness identifies the coefficient sheaves, while arithmetic applications require global classes and the relation between their crystalline pieces. Derived global sections preserve the mapping-fiber triangle and turn it into exact sequences whose kernel and cokernel terms can be calculated. This chapter establishes that global bookkeeping before any special geometry is imposed.

### 5.1 Hypercohomology

Let $\epsilon$ denote the morphism of topoi from the small $p$-adic syntomic site of $X$ to the small etale site of $X_1$ induced by special-fiber reduction. Concretely, the inverse image of an etale sheaf is evaluated on the special fibers $U_1$ of syntomic objects $U\to X$; this does not assert that $U_1\to X_1$ is itself etale. The crystalline sheaves on $U$ retain all compatible divided-power levels. Define the derived syntomic complex on $X_1$ by

$$
R\mathscr S_n(r)=R\epsilon_*\mathscr S_n(r),
\qquad r=0,1,
\tag{5.1}
$$

and the global groups by

$$
H^q_{\mathrm{syn}}(X,\mathbf Z/p^n(r))
=\mathbb H^q(X_1,R\mathscr S_n(r)).
\tag{5.2}
$$

When no confusion is possible we abbreviate this to $H^q_{\mathrm{syn}}(X,r;n)$. The notation $\mathbf Z/p^n(1)$ means the finite-flat sheaf $\mu_{p^n}$, not a constant etale sheaf on the special fiber.

The fundamental quasi-isomorphisms imply

$$
R\mathscr S_n(0)\simeq R\epsilon_*\mathbf Z/p^n,
\qquad
R\mathscr S_n(1)\simeq R\epsilon_*\mu_{p^n}.
\tag{5.3}
$$

In degrees zero and one the right sides may equally be computed in the fppf topology. Indeed sections are the same, and a torsor under either coefficient is trivialized by its own total space, which the lci lemma of Section 4.4 and Theorem 7.1 show to be a syntomic cover; hence the Cech classifications coincide. This assertion in higher degrees would require a topology-comparison theorem and is not used without proof.

### 5.2 The long exact sequence

Write

$$
R\Gamma_{\mathrm{cr}}(X_n)
=R\Gamma(X_{1,\mathrm{syn}},
\mathscr O_n^{\mathrm{cr}}\Omega^\bullet)
\tag{5.4}
$$

and

$$
F^rR\Gamma_{\mathrm{cr}}(X_n)
=R\Gamma(X_{1,\mathrm{syn}},
\mathscr J_n^{\langle r-\bullet\rangle}\Omega^\bullet).
\tag{5.5}
$$

The notation $F^r$ here names a filtered complex. It is not the subgroup obtained by taking the image on cohomology. Those two constructions agree only under a strictness or degeneration theorem.

Taking derived global sections in (3.1) gives a distinguished triangle

$$
R\Gamma_{\mathrm{syn}}(X,r;n)
\longrightarrow F^rR\Gamma_{\mathrm{cr}}(X_n)
\xrightarrow{1-\varphi_r}
R\Gamma_{\mathrm{cr}}(X_n)
\longrightarrow.
\tag{5.6}
$$

Therefore:

**Proposition 5.1 (syntomic long exact sequence).** For $r=0,1$ there is a functorial exact sequence

$$
\begin{aligned}
\cdots\to&H^{q-1}_{\mathrm{cr}}(X_n)
\to H^q_{\mathrm{syn}}(X,r;n)\\
\to&H^q(F^rR\Gamma_{\mathrm{cr}}(X_n))
\xrightarrow{1-\varphi_r}
H^q_{\mathrm{cr}}(X_n)\to\cdots.
\end{aligned}
\tag{5.7}
$$

**Proof.** This is the cohomology sequence of (5.6). Functoriality follows because pullback respects the filtered crystalline complexes and Frobenius. $\square$

The first arrow in (5.7) is induced by the inclusion of the second term into the mapping cone. It should not be confused with a geometric boundary from a short exact sequence of group schemes, though Theorem 4.5 will relate the two descriptions.

### 5.3 The two-term kernel-cokernel description

Every mapping fiber gives a useful short exact sequence.

**Corollary 5.2.** For every $q$ and $r=0,1$,

$$
0\longrightarrow
\operatorname{coker}\left(
1-\varphi_r:H^{q-1}(F^rR\Gamma_{\mathrm{cr}})
\to H^{q-1}_{\mathrm{cr}}
\right)
\longrightarrow H^q_{\mathrm{syn}}
\tag{5.8}
$$

$$
\longrightarrow
\ker\left(
1-\varphi_r:H^q(F^rR\Gamma_{\mathrm{cr}})
\to H^q_{\mathrm{cr}}
\right)
\longrightarrow0.
$$

All groups are at level $n$ on $X$.

**Proof.** Exactness of (5.7) identifies the kernel of the middle-to-right map with the cokernel from the preceding degree and identifies its image with the displayed kernel. $\square$

This sequence need not split. Its left term measures the failure of a crystalline class to be a Frobenius difference; its right term measures filtered divided-Frobenius fixed points. The syntomic group is the extension in which both phenomena coexist.

In weight zero, $F^0R\Gamma_{\mathrm{cr}}=R\Gamma_{\mathrm{cr}}$, so (5.8) becomes

$$
0\to\operatorname{coker}(1-\varphi:H^{q-1}_{\mathrm{cr}}\to H^{q-1}_{\mathrm{cr}})
\to H^q_{\mathrm{syn}}(0)
\to\ker(1-\varphi:H^q_{\mathrm{cr}}\to H^q_{\mathrm{cr}})
\to0.
\tag{5.9}
$$

In weight one, replacing $H^q(F^1R\Gamma)$ by the Hodge submodule of $H^q_{\mathrm{cr}}$ is legitimate only after the required filtered strictness has been proved for the geometry at hand.

### 5.4 Pullback and reduction

Let $k\to k'$ be an extension of perfect fields, put $V'=W(k')$, and let $X'=X\times_VV'$. Crystalline derived base change from Book 49 and naturality of divided Frobenius give a map between the two arrows defining (5.6). Taking mapping fibers produces a canonical pullback

$$
R\Gamma_{\mathrm{syn}}(X,r;n)
\longrightarrow
R\Gamma_{\mathrm{syn}}(X',r;n).
\tag{5.10}
$$

There is deliberately no tensor product with $V'_n$ in (5.10). Although the two crystalline complexes are complexes of $V_n$-modules, $1-\varphi_r$ is only $\mathbf Z/p^n$-linear because Frobenius is semilinear. Its mapping fiber is therefore naturally a complex of $\mathbf Z/p^n$-modules. Moreover fixed points and torsors can change after extending the residue field, so pullback is not an isomorphism without an additional geometric comparison theorem.

When $X$ is proper, Chapter 13 constructs the completed complex and proves the reduction triangle

$$
R\Gamma_{\mathrm{syn}}(r)\xrightarrow{p^n}
R\Gamma_{\mathrm{syn}}(r)
\longrightarrow R\Gamma_{\mathrm{syn}}(r;n)
\longrightarrow,
\tag{5.11}
$$

Thus, under this properness hypothesis,

$$
0\to H^q_{\mathrm{syn}}(r)/p^n
\to H^q_{\mathrm{syn}}(r;n)
\to H^{q+1}_{\mathrm{syn}}(r)[p^n]
\to0.
\tag{5.12}
$$

No finite-level group is identified with a reduction until the rightmost torsion term is known to vanish.

## 6. Weight zero as integral fixed-point theory

Weight zero is the cleanest test of the construction. It shows that syntomic cohomology is not an exotic replacement for finite-etale cohomology: it is a crystalline presentation of the same torsors. At the same time, its exact sequence warns that global degree one contains both base classes and Frobenius-fixed geometric classes.

### 6.1 Constant classes

Theorem 4.5 identifies the weight-zero complex with the constant finite etale coefficient. Hence

$$
H^q_{\mathrm{syn}}(X,\mathbf Z/p^n(0))
\simeq H^q_{\mathrm{syn}}(X,\mathbf Z/p^n).
\tag{6.1}
$$

In degrees zero and one this is ordinary finite-etale descent. The crystalline description (5.9) is therefore an integral fixed-point presentation of familiar torsors.

This equality does not say that every fixed vector of the rational crystalline Frobenius produces an integral class. A rational fixed vector may not lie in the integral crystalline lattice, and an integral fixed vector modulo $p^n$ may fail to lift compatibly through all $n$. The mapping fiber retains the cokernel term which measures that failure.

### 6.2 Connected bases and degree zero

Assume $X$ is connected. Then

$$
H^0_{\mathrm{syn}}(X,\mathbf Z/p^n(0))
=\mathbf Z/p^n\mathbf Z.
\tag{6.2}
$$

From the crystalline exact sequence, this says

$$
\ker(1-\varphi:H^0_{\mathrm{cr}}(X_n)
\to H^0_{\mathrm{cr}}(X_n))
=\mathbf Z/p^n\mathbf Z.
\tag{6.3}
$$

For a proper smooth geometrically connected scheme, Book 49 gives $H^0_{\mathrm{cr}}=V_n$, and (6.3) reduces to the fixed ring of Witt Frobenius on the coefficient component. If $k$ is algebraically closed, that fixed ring is still $\mathbf Z/p^n$, not all of $W_n(k)$.

For a disconnected scheme, one obtains one copy for each connected component. This is an example in which geometric connectedness is a necessary hypothesis, not a stylistic simplification.

### 6.3 Degree one and finite etale torsors

A class in $H^1_{\mathrm{syn}}(X,\mathbf Z/p^n)$ is a torsor under the constant finite etale group. It is represented locally by an equation of Artin--Schreier--Witt type, and its crystalline presentation lies in

$$
0\to\operatorname{coker}(1-\varphi:H^0_{\mathrm{cr}}\to H^0_{\mathrm{cr}})
\to H^1_{\mathrm{syn}}(0)
\to\ker(1-\varphi:H^1_{\mathrm{cr}}\to H^1_{\mathrm{cr}})
\to0.
\tag{6.4}
$$

The left term is often nonzero over a nonclosed coefficient base. It records torsors pulled back from the base. The right term records geometric fixed classes. Treating $H^1_{\mathrm{syn}}$ as merely the fixed part of $H^1_{\mathrm{cr}}$ would discard the arithmetic base contribution.

If $X$ is normal and connected, restriction of a finite etale torsor from $X$ to its dense generic fiber is injective on isomorphism classes. Indeed a generic section of a finite etale $X$-scheme extends uniquely: its graph has finite closure, and normality identifies the closure with $X$ because it is finite birational. Thus a torsor trivial on the generic fiber was already trivial.

### 6.4 An affine calculation

Take the affine henselian base itself, $X=\operatorname{Spec}V$. Finite-etale covers of $V$ and of its residue field $k$ are equivalent, so

$$
H^1_{\mathrm{syn}}(V,\mathbf Z/p)
\simeq H^1_{\mathrm{et}}(k,\mathbf Z/p).
\tag{6.5}
$$

The Artin--Schreier sequence on the affine scheme $\operatorname{Spec}k$ gives

$$
H^1_{\mathrm{syn}}(V,\mathbf Z/p)
\simeq k/(F-1)k.
\tag{6.6}
$$

This is exactly the degree-zero cokernel in (6.4): the crystalline complex of $V$ is $V_n$ in degree zero, and reduction of $1-\sigma$ modulo $p$ is $1-F$. For a finite field $k$, the quotient is one-dimensional over $\mathbf F_p$; for algebraically closed $k$, it vanishes. Thus even the simplest affine calculation records arithmetic of the coefficient base rather than merely geometric fixed vectors.

On larger affine schemes geometric Artin--Schreier classes may also occur, while on proper curves finite-etale $p$-covers can contribute through the fixed part of crystalline degree one. No special-fiber calculation is silently identified here with integral syntomic cohomology.

## 7. Weight one as Kummer theory

Weight one is where integral geometry becomes visible. Roots of unity cease to be etale on the closed fiber, but they remain finite flat, and the syntomic topology sees their torsors. The fundamental sequence therefore turns filtered crystalline fixed points into units, powered line bundles, and Chern classes through the fppf Kummer sequence.

### 7.1 The syntomic Kummer quasi-isomorphism

The second quasi-isomorphism of (4.14) gives

$$
\mathscr S_n(1)\simeq\mu_{p^n}
\tag{7.1}
$$

on the syntomic site. Since $\mu_{p^n}$ is finite locally free, its degree-one syntomic torsors are exactly its fppf torsors. Therefore:

**Theorem 7.1 (weight-one Kummer comparison).** There are natural isomorphisms

$$
H^0_{\mathrm{syn}}(X,\mathbf Z/p^n(1))
\simeq\mu_{p^n}(X),
\tag{7.2}
$$

$$
H^1_{\mathrm{syn}}(X,\mathbf Z/p^n(1))
\simeq H^1_{\mathrm{fppf}}(X,\mu_{p^n}).
\tag{7.3}
$$

**Proof.** Equation (7.1) identifies sections and torsor classes on the syntomic site, so it remains to compare the two topologies on $\mu_{p^n}$-torsors. Every syntomic cover is flat and of finite presentation, hence an fppf cover; this gives the arrow from syntomic to fppf classification. Conversely, let $P\to X$ be an arbitrary fppf $\mu_{p^n}$-torsor. By the lci lemma of Section 4.4, applied to the Kummer presentation of Book 29, the scheme $P$ is finite locally free of rank $p^n$, surjective, and syntomic over $X$. Thus $P$ itself is a syntomic cover trivializing $P$, so every fppf torsor is syntomically locally trivial and the two Cech classifications coincide. No cotangent-complex criterion is used: syntomy of a root cover was verified from its monic equation. $\square$

The theorem is not an etale comparison on the special fiber. When $p$ is the residue characteristic, $\mu_{p^n}$ is nonetale and its infinitesimal torsors would be lost in the etale topology.

### 7.2 Units and root torsors

The fppf Kummer sequence from Book 29 gives

$$
1\to\mu_{p^n}\to\mathbf G_m
\xrightarrow{p^n}\mathbf G_m\to1.
\tag{7.4}
$$

Its boundary sends a unit $u$ to the torsor

$$
P_u=\operatorname{Spec}
\mathcal O_X[T]/(T^{p^n}-u).
\tag{7.5}
$$

Under (7.3), this torsor has a crystalline representative. Choose a syntomic cover on which there is a root $v$, choose multiplicative crystalline lifts of the local roots, and compare them on double overlaps. Their ratios lie in $\mu_{p^n}$; the map $\ell_n$ of (4.7) turns those ratios into fixed elements of $\mathscr J_n^{\langle1\rangle}$. Together with the local forms $d\log\widetilde v$, these fixed overlap elements form the total Cech--mapping-fiber cocycle. Its cone component is computed from the Frobenius defects of the chosen lifts exactly as in Section 4.3. Changing a lift multiplies a defect by an element of $1+\mathscr J$, whose PD logarithm is a mapping-fiber coboundary. This description uses neither $\ell_n$ on a nontorsion root nor an unproved division of a finite-level logarithm by $p^n$.

For a local or semilocal base, the Picard group vanishes and Theorem 7.1 yields

$$
H^1_{\mathrm{syn}}(X,\mathbf Z/p^n(1))
\simeq
\mathcal O_X(X)^\times/
\mathcal O_X(X)^{\times p^n}.
\tag{7.6}
$$

For a general scheme, (7.6) is incomplete because $p^n$-torsion line bundles contribute.

### 7.3 Line bundles and the degree-two boundary

The full degree-one Kummer exact sequence is

$$
0\longrightarrow
\Gamma(X,\mathcal O_X)^\times/
\Gamma(X,\mathcal O_X)^{\times p^n}
\longrightarrow H^1_{\mathrm{syn}}(X,1;n)
\longrightarrow\operatorname{Pic}(X)[p^n]
\longrightarrow0.
\tag{7.7}
$$

A class over a torsion line bundle $L$ consists of an isomorphism

$$
\tau:L^{\otimes p^n}\xrightarrow{\sim}\mathcal O.
\tag{7.8}
$$

Its torsor is the spectrum of the graded algebra

$$
\mathcal O\oplus L^{-1}\oplus\cdots\oplus L^{-(p^n-1)},
\tag{7.9}
$$

with multiplication across the last degree defined by $\tau$. This construction remains valid in residue characteristic $p$ because it uses the grading of the diagonalizable group scheme, not eigenspaces of its geometric points.

The next part of the Kummer sequence gives

$$
0\to\operatorname{Pic}(X)/p^n
\longrightarrow H^2_{\mathrm{fppf}}(X,\mu_{p^n})
\longrightarrow\operatorname{Br}'(X)[p^n]
\to0.
\tag{7.10}
$$

Whenever the topology comparison in degree two is available, (7.1) identifies this with $H^2_{\mathrm{syn}}$. We will only use the canonical map from the left term, which can be constructed directly by the gerbe of $p^n$th roots and therefore requires no blanket degree-two topology comparison.

### 7.4 The first syntomic Chern class

For a line bundle $L$, define

$$
c^{\mathrm{syn}}_{1,n}(L)
\in H^2_{\mathrm{syn}}(X,\mathbf Z/p^n(1))
\tag{7.11}
$$

as the boundary of $L$ in the Kummer sequence. Locally choose transition functions $g_{ij}$ and crystalline lifts $\widetilde g_{ij}$. The Cech--mapping-fiber representative has differential-form component $d\log\widetilde g_{ij}$ and divided-power logarithm component measuring

$$
\widetilde g_{ij}\widetilde g_{jk}\widetilde g_{ki}\in1+\mathscr J_n.
$$

The logarithm converts multiplication on triple overlaps to addition, so the total cocycle condition holds. A change of lifts changes the representative by a total coboundary.

**Proposition 7.2.** The first syntomic Chern class satisfies

$$
c^{\mathrm{syn}}_{1,n}(L\otimes M)
=c^{\mathrm{syn}}_{1,n}(L)+c^{\mathrm{syn}}_{1,n}(M),
\tag{7.12}
$$

is functorial under pullback, vanishes on $p^n$th powers, and maps under the crystalline edge morphism to the crystalline Chern class modulo $p^n$.

**Proof.** Tensor product multiplies transition functions, and the PD logarithm changes products into sums. Pullback is termwise. If $L=N^{\otimes p^n}$, its Kummer boundary is zero by exactness. Finally, forgetting the Frobenius component of the mapping fiber leaves exactly the Cech--de Rham cocycle defining the crystalline first Chern class in Book 49. $\square$

Thus weight-one syntomic cohomology refines the crystalline first Chern class by retaining a compatible Frobenius trivialization.

## 8. Integral period morphisms

The local model now has both a crystalline description and a finite-flat description. The period morphism is the canonical passage from either description to the generic etale coefficient. Its central property in low degree is an image theorem: it remembers exactly which generic torsors extend across the closed fiber.

### 8.1 Generic fibers and nearby classes

Let $j:X_K\hookrightarrow X$ denote the generic-fiber inclusion for a smooth $V$-scheme $X$, and let $i:X_1\hookrightarrow X$ be the special-fiber inclusion. On the generic fiber, $p$ is invertible, so both

$$
\mathbf Z/p^n\mathbf Z
\quad\text{and}\quad
\mu_{p^n}
$$

are finite etale sheaves. The complexes

$$
i^*Rj_*\mathbf Z/p^n(r),\qquad r=0,1,
\tag{8.1}
$$

record generic etale classes viewed from the special fiber. They include classes which may be ramified along the closed fiber. Syntomic classes form the integral, extendable part.

There is a natural restriction map of finite-flat sheaves on $X$

$$
\mathbf Z/p^n\to j_*\mathbf Z/p^n,
\qquad
\mu_{p^n,X}\to j_*\mu_{p^n,X_K}.
\tag{8.2}
$$

Deriving and restricting to $X_1$ gives maps into (8.1). The fundamental quasi-isomorphisms transport them to syntomic complexes.

### 8.2 Construction in weights zero and one

**Definition 8.1.** The integral period morphism is the composite

$$
\alpha_{r,n}:R\mathscr S_n(r)
\xleftarrow{\sim}R\epsilon_*\mathbf Z/p^n(r)
\longrightarrow i^*Rj_*\mathbf Z/p^n(r),
\qquad r=0,1,
\tag{8.3}
$$

where the left arrow is (4.14) and is inverted in the derived category.

This definition may look formal, but the hard input is precisely the integral fundamental sequence which constructed the left quasi-isomorphism. No rationalization occurs. At the cocycle level, $\alpha_{0,n}$ restricts an Artin--Schreier--Witt torsor to the generic fiber, while $\alpha_{1,n}$ restricts the root torsor $T^{p^n}=u$ and its line-bundle generalizations.

Taking hypercohomology always gives

$$
\alpha_{r,n}^q:
H^q_{\mathrm{syn}}(X,\mathbf Z/p^n(r))
\longrightarrow
\mathbb H^q(X_1,i^*Rj_*\mathbf Z/p^n(r)).
\tag{8.4}
$$

If $X$ is proper over $V$, proper base change identifies the target with

$$
H^q_{\mathrm{et}}(X_K,\mathbf Z/p^n(r)).
\tag{8.5}
$$

For arbitrary smooth $X$, restriction of sections and torsors still gives maps in degrees zero and one directly to generic etale cohomology. We use the same symbol $\alpha_{r,n}^q$ for those maps; when $X$ is proper they agree with (8.4) through (8.5). No global nearby-cycle identification is asserted in the nonproper case.

### 8.3 The extendable-class theorem

**Theorem 8.2 (integral comparison in degrees zero and one).** Let $X$ be smooth over $V$, hence regular and normal. For $r=0,1$:

1. $\alpha_{r,n}^0$ is the ordinary restriction of sections and is injective.
2. $\alpha_{r,n}^1$ is injective.
3. Its image consists exactly of generic torsor classes under $\mathbf Z/p^n(r)$ which extend to torsors under the finite locally free group scheme $\mathbf Z/p^n(r)$ over $X$.

For $r=1$, these are exactly the finite-flat Kummer classes.

**Proof strategy.** Use Theorem 4.5 to replace syntomic classes by torsors. Extension gives the image statement by construction. Normality proves uniqueness and injectivity.

**Proof.** In degree zero, a section of a separated finite $X$-scheme is determined on the dense generic fiber, proving injectivity.

In degree one, Theorem 4.5 and torsor classification identify a syntomic class with a finite locally free torsor $P\to X$. Its image is its generic restriction, so every image class extends. Conversely, an extension of a generic torsor is by definition such a finite locally free torsor and hence yields a syntomic class.

It remains to prove injectivity. Suppose $P_K$ is trivial. Choose a generic section $s_K:X_K\to P_K$. Since $P$ is finite over $X$, the schematic closure $Z$ of $s_K(X_K)$ is finite over $X$. The map $Z\to X$ is birational. Because $X$ is normal and $Z$ lies in a finite $X$-scheme, the coordinate algebra of $Z$ is an integral subalgebra of the function field finite over $\mathcal O_X$; integral closedness forces it to be $\mathcal O_X$. Thus $Z\simeq X$, and the inclusion $Z\hookrightarrow P$ is a global section. A torsor with a section is trivial. $\square$

The theorem deliberately characterizes an image instead of claiming surjectivity. For example, over $X=\operatorname{Spec}V$ the generic Kummer class of a uniformizer $p$ is represented by $T^{p^n}=p$. This finite cover is ramified and is not a $\mu_{p^n}$-torsor over $V$, since $p$ is not a unit. Its generic class is not in the image of $\alpha_{1,n}^1$.

### 8.4 Functoriality and normalization

**Proposition 8.3.** The maps $\alpha_{r,n}$ commute with pullback, coefficient reduction, connecting morphisms, and the identifications

$$
\mathbf Z/p^n(0)=\mathbf Z/p^n,
\qquad
\mathbf Z/p^n(1)=\mu_{p^n}.
$$

They are compatible with unramified extension of $V$.

**Proof.** Every operation is induced from a commutative diagram of the fundamental short exact sequences. Divided-power logarithm commutes with pullback and reduction. Restriction of a torsor commutes with changing coefficients and with forming a torsor of lifts, so the boundary squares commute. Witt Frobenius is natural under extension of perfect residue fields, which proves the base statement. $\square$

The normalization in weight one is fixed by requiring that the syntomic class of a unit $u$ map to the generic Kummer torsor $T^{p^n}=u$. There is no remaining sign ambiguity.

## 9. Products, symbols, and Chern classes

Comparison maps become useful only when they preserve the operations from which arithmetic classes are built. Filtration is multiplicative, Kummer boundaries have cup products, and line bundles have Chern classes. This chapter checks that these structures agree, while stopping honestly at the boundary beyond which a weight-two syntomic complex would be required.

### 9.1 Cup products of mapping fibers

The filtered multiplication (2.4) and multiplicativity of Frobenius induce products

$$
\mathscr S_n(a)\otimes^L\mathscr S_n(b)
\longrightarrow\mathscr S_n(a+b)
\tag{9.1}
$$

whenever the target weight has been constructed. Within this book the intrinsically defined targets are weights $0$ and $1$. Thus we use

$$
\mathscr S_n(0)\otimes\mathscr S_n(0)\to\mathscr S_n(0)
$$

and the module action

$$
\mathscr S_n(0)\otimes\mathscr S_n(1)\to\mathscr S_n(1).
\tag{9.2}
$$

A product of two weight-one classes naturally has weight two. Rather than pretending that a weight-two integral complex has been constructed, we send such products through Kummer cup product to $H^2(\mu_{p^n}^{\otimes2})$. This retains the coefficient twist and avoids crossing the low-weight boundary.

At the cone level, if $(a,b)$ and $(a',b')$ represent fiber elements, the product is the filtered product in the first component and the signed sum of cross terms in the cone component. The identity

$$
1-\varphi_{a+b}
=(1-\varphi_a)+\varphi_a(1-\varphi_b)
\tag{9.3}
$$

is the algebra which makes the differential obey the Leibniz rule. Different cone conventions produce chain-isomorphic formulas; our fiber convention fixes the displayed signs.

### 9.2 Kummer symbols

For units $u,v$ on $X$, their Kummer boundaries give

$$
\delta(u),\delta(v)\in H^1_{\mathrm{syn}}(X,\mathbf Z/p^n(1)).
$$

Their cup product is

$$
\{u,v\}_{p^n}
=\delta(u)\smile\delta(v)
\in H^2_{\mathrm{fppf}}(X,\mu_{p^n}^{\otimes2}).
\tag{9.4}
$$

It is bilinear and depends only on the unit classes modulo $p^n$th powers. If a primitive $p^n$th root of unity is chosen on the generic fiber, one may identify the tensor square with one Tate twist and recover the usual symbol algebra description. Without that choice, the tensor twist in (9.4) is the correct canonical target.

On the generic fiber, where $p$ is invertible, Book 29 gives the Steinberg relation

$$
\{u_K,1-u_K\}_{p^n}=0
\tag{9.5}
$$

whenever both entries are units. One proof is the norm identity

$$
N(1-\sqrt[p^n]{u})=1-u
$$

in the corresponding cyclic etale algebra after making the standard root-of-unity base change. We do not infer from this a vanishing statement in integral fppf degree two: Book 29 proved the displayed relation in the invertible-coefficient range, and generic restriction on $H^2$ has not been proved injective here. Establishing an integral Steinberg relation would require an additional weight-two or norm-residue input and is outside the present low-weight package.

### 9.3 Compatibility of period maps with products

**Theorem 9.1.** Integral period morphisms commute with every product defined in (9.2) and with first Chern classes. Generic restriction also carries the fppf cup product of two Kummer classes to the corresponding generic etale cup product. If $X$ is proper over $V$, so that (8.5) identifies the period target with generic etale cohomology, then in particular

$$
\alpha_{1,n}^2(c^{\mathrm{syn}}_{1,n}(L))
=c^{\mathrm{et}}_{1,n}(L_K),
\tag{9.6}
$$

For every smooth $X$, independently of properness,

$$
\operatorname{res}_{X_K/X}(\{u,v\}_{p^n})
=\{u_K,v_K\}_{p^n}.
\tag{9.7}
$$

**Proof strategy and proof.** The fundamental maps (4.14) are multiplicative in the constructed weights: in weight one the identity $\log(uv)=\log u+\log v$ identifies tensoring root torsors with addition in the mapping fiber. Generic restriction is a morphism of ringed topoi and therefore preserves derived cup products. Naturality carries the Kummer boundary of a line bundle to the nearby first Chern class; under proper base change this is (9.6). Applying generic restriction to the two fppf unit boundaries and then cupping proves (9.7) without a properness hypothesis; no weight-two syntomic mapping fiber is used. $\square$

This compatibility is more informative than equality after rationalization: it states that the actual integral Kummer torsor and its products are preserved.

### 9.4 Projective space and a divisor calculation

Let $X=\mathbf P^m_V$. Its global units are $V^\times$, and

$$
\operatorname{Pic}(X)=\mathbf Z[\mathcal O(1)].
$$

Because this Picard group has no $p^n$-torsion, (7.7) gives

$$
H^1_{\mathrm{syn}}(X,\mathbf Z/p^n(1))
\simeq V^\times/V^{\times p^n}.
\tag{9.8}
$$

In degree two, the Kummer boundary of $\mathcal O(1)$ gives a class

$$
h_n=c^{\mathrm{syn}}_{1,n}(\mathcal O(1)).
$$

Its crystalline image is the hyperplane class modulo $p^n$, and its generic period is the etale hyperplane class. On $\mathbf P^1$, crystalline Frobenius sends the integral lift $h$ to $ph$, so divided Frobenius fixes its weight-one normalization. This is the simplest global example of the equation $\varphi_1(h)=h$.

The generic Kummer class of $p\in K^\times$ supplies a contrasting example. It does not occur in (9.8), because $p\notin V^\times$. The period map therefore separates horizontal divisor information, which extends, from the valuation-direction Kummer class, which does not.

## 10. Smooth proper curves

For a curve, the crystalline complex has only three cohomological degrees and the filtered de Rham model has only two terms. This makes the weight-one exact sequence unusually transparent. The same classes can be read through units and the Picard group, through filtered Frobenius, or through the Jacobian, and the agreement among these readings is the first substantial geometric application.

### 10.1 The filtered crystalline model

Let $C/V$ be a smooth proper geometrically connected curve of genus $g$. Book 49 proves that its crystalline cohomology is finite locally free in degrees $0,1,2$, of ranks $1,2g,1$, and commutes with arbitrary divided-power base change. Because $C$ itself is a smooth lift, the crystalline complex at level $n$ is

$$
K_n=R\Gamma(C_n,[\mathcal O_{C_n}\xrightarrow d
\Omega^1_{C_n/V_n}]).
\tag{10.1}
$$

The weight-one filtered complex is the derived reduction of the integral lattice $[p\mathcal O_C\to\Omega^1_{C/V}]$. It may be represented as

$$
F^1K_n=R\Gamma(C_n,
[\mathcal O_{C_n}\xrightarrow{p\,d}
\Omega^1_{C_n/V_n}]),
\tag{10.2}
$$

where the map from (10.2) to (10.1) is multiplication by $p$ in degree zero and the identity in degree one. Under the identification $\mathcal O_{C_n}\simeq p\mathcal O_C/p^{n+1}\mathcal O_C$, this is exactly the modified finite-level interpretation of Chapter 2. In particular, the degree-zero term is not the smaller literal ideal $p\mathcal O_{C_n}$.

There is a triangle

$$
F^1K_n\longrightarrow K_n\longrightarrow
R\Gamma(C_1,\mathcal O_{C_1})\otimes_V^LV_n
\longrightarrow.
\tag{10.3}
$$

Indeed this is the derived reduction of the integral triangle obtained by quotienting $[p\mathcal O_C\to\Omega^1]$ inside $[\mathcal O_C\to\Omega^1]$. The last term is derived: it has the familiar two-row contribution coming from the complex $[V_n\xrightarrow pV_n]$ tensored with $\mathcal O_{C_1}$. Replacing it by ordinary $R\Gamma(C_1,\mathcal O_{C_1})$ would lose the Tor row and precisely the finite-level digit retained by the modified filtration. Triangle (10.3) computes the filtered complex without pretending that a filtration on cohomology is automatically strict.

The Hodge-to-de Rham sequence of Book 49 is

$$
0\longrightarrow H^0(C_n,\Omega^1)
\longrightarrow H^1_{\mathrm{cr}}(C_1/V_n)
\longrightarrow H^1(C_n,\mathcal O)
\longrightarrow0.
\tag{10.4}
$$

Its outer terms are finite locally free of rank $g$. On the filtered complex, the differential-form term is unchanged, while the map from the degree-zero copy to the ordinary de Rham complex is multiplication by $p$. The distinction controls the integral lattice in the syntomic mapping fiber.

### 10.2 The weight-one exact sequence

Applying (5.8) to (10.2) gives

$$
0\to
\operatorname{coker}\left(
1-\varphi_1:H^{q-1}(F^1K_n)\to H^{q-1}(K_n)
\right)
\to H^q_{\mathrm{syn}}(C,1;n)
\tag{10.5}
$$

$$
\to
\ker\left(
1-\varphi_1:H^q(F^1K_n)\to H^q(K_n)
\right)
\to0.
$$

For $q=1$, Theorem 7.1 and Kummer theory give a second, geometric presentation:

$$
0\to V^\times/V^{\times p^n}
\to H^1_{\mathrm{syn}}(C,1;n)
\to\operatorname{Pic}(C)[p^n]
\to0.
\tag{10.6}
$$

The units are $V^\times$ because a global function on a proper geometrically connected smooth curve comes from the base. The two exact sequences (10.5) and (10.6) describe the same group from opposite sides: filtered Frobenius on the one hand, root torsors and torsion line bundles on the other.

**Proposition 10.1.** Under the identification of (10.5) with (10.6), a unit class is represented by the Frobenius-difference cokernel in degree zero, while a $p^n$-torsion line bundle maps to a divided-Frobenius fixed class in filtered crystalline degree one.

**Proof strategy.** Use Cech representatives for a powered line bundle and compare their logarithms with the mapping fiber.

**Proof.** A unit $u$ has no nontrivial transition functions. Its root torsor is described entirely by choosing local roots, and the discrepancy among possible crystalline logarithms changes by $(1-\varphi_1)$ of a degree-zero section. Hence it lies in the cokernel term.

For a pair $(L,\tau:L^{p^n}\simeq\mathcal O)$, choose frames $e_i$ of $L$ and transition units $g_{ij}$. The $p^n$th-power trivialization makes $g_{ij}^{p^n}$ a Cech coboundary, so after a syntomic refinement one may choose compatible local roots. Their ratios on overlaps belong to $\mu_{p^n}$. Applying $\ell_n$ to those torsion ratios, and using $d\log$ only on multiplicative crystalline lifts, produces the degree-one filtered crystalline cocycle of Section 7.2. Lemma 4.3 says that its class is fixed by $\varphi_1$. Changing frames changes it by a filtered coboundary, and changing $\tau$ by a unit adds precisely the degree-zero cokernel class already described. This is exactly the extension relation in (10.6). $\square$

The proposition does not split either exact sequence. A choice of splitting would amount to choosing Frobenius-compatible logarithms of all units or power trivializations of all torsion line bundles, and no natural choice exists.

### 10.3 Picard classes and the Jacobian

Let $J=\operatorname{Pic}^0_{C/V}$ be the Jacobian. Assume first that $C$ has a section, used to rigidify line bundles. The connected component of a $p^n$-torsion line bundle is then a section of $J[p^n]$. More precisely, the degree map gives

$$
0\to\operatorname{Pic}^0(C)[p^n]
\to\operatorname{Pic}(C)[p^n]
\to\mathbf Z[p^n]=0,
$$

so every torsion line bundle has degree zero. Since rigidification removes pullback from the base and $\operatorname{Pic}(V)=0$, consequently

$$
\operatorname{Pic}(C)[p^n]=J(V)[p^n]
\tag{10.7}
$$

when the relative Picard functor is evaluated on $V$. Without a section, the statement holds after a faithfully flat base change admitting one; the resulting Jacobian map descends, but an equality of raw Picard groups is not asserted without accounting for the descent obstruction.

Book 49 identifies

$$
H^1_{\mathrm{cr}}(J_1/V_n)
\xrightarrow{\sim}H^1_{\mathrm{cr}}(C_1/V_n)
\tag{10.8}
$$

through the Abel--Jacobi map, compatibly with Frobenius and the alternating pairings. The syntomic construction respects this map because it is functorial on filtered crystalline complexes. Thus the fixed crystalline class attached in Proposition 10.1 to $L$ may be calculated on either $C$ or $J$.

There is an important variance distinction. A point of $J[p^n](V)$ is a torsion line bundle and hence yields a $\mu_{p^n}$-torsor only after a power trivialization has been chosen. A point of $J(V)/p^nJ(V)$ instead yields a $J[p^n]$-torsor of division points. These classes live in different coefficient groups. They are related by the Poincare pairing, not by identifying $J[p^n]$ with $\mu_{p^n}$.

### 10.4 Trace and duality

The curve pairing of Book 49 is perfect and alternating:

$$
\langle x,y\rangle_C=
\operatorname{Tr}_{\mathrm{cr}}(x\smile y):
H^1_{\mathrm{cr}}\otimes H^1_{\mathrm{cr}}\longrightarrow V_n(-1).
\tag{10.9}
$$

It satisfies

$$
\langle\varphi x,\varphi y\rangle
=p\,\sigma\langle x,y\rangle.
\tag{10.10}
$$

Equation (10.10) is the undivided Frobenius compatibility. One must not divide both arguments by $p$ formally: doing so would introduce $p^{-1}$ in the target. Integrality of any pairing on filtered pieces must instead use the actual filtration and its isotropy. The Hodge submodule $H^0(\Omega^1)$ is Lagrangian, so two differential classes pair to zero.

**Proposition 10.2.** The period morphism carries the syntomic first Chern class of a line bundle on $C$ to its generic etale Chern class. If $f:C\to D$ is finite locally free, then on the Chern-class subgroup the norm square

$$
\begin{array}{ccc}
\operatorname{Pic}(C)/p^n&\xrightarrow{c^{\mathrm{syn}}_{1,n}}&
\operatorname{im}(c^{\mathrm{syn}}_{1,n})\\
\downarrow N_f&&\downarrow N_f^{c_1}\\
\operatorname{Pic}(D)/p^n&\xrightarrow{c^{\mathrm{syn}}_{1,n}}&
\operatorname{im}(c^{\mathrm{syn}}_{1,n})
\end{array}
$$

commutes, and its generic period is the analogous etale norm-corestriction square.

Here $N_f^{c_1}$ is defined on the displayed image by $c_1(L)\mapsto c_1(N_fL)$.

**Proof.** Chern compatibility is (9.6). The Kummer sequence makes $c^{\mathrm{syn}}_{1,n}$ injective on $\operatorname{Pic}/p^n$, so $N_f^{c_1}$ is well defined. Book 29 proves that norm of line bundles commutes with the Kummer boundary. Thus the left and right routes in the displayed square both classify the gerbe of roots of the normed line bundle; on Cech representatives they both take the norm of the transition functions. Generic restriction commutes with the norm functor, and generic etale corestriction on these Kummer classes has the same description. This proves the final compatibility. No pushforward on all syntomic cohomology is being asserted. $\square$

No division by $\deg f$ occurs. If one wants an inverse to pullback, the degree must separately be a unit.

## 11. Abelian schemes and degree one

An abelian scheme adds group law, duality, isogenies, and a universal Poincare bundle. Its crystalline degree one is the primitive generator of all higher cohomology, but its finite-flat torsion coefficients are much larger than $\mu_{p^n}$. The role of weight-one syntomic cohomology is therefore to receive characters of those torsion groups through the Weil pairing, not to collapse them into a single coefficient.

### 11.1 The crystalline Hodge extension revisited

Let $A/V$ be an abelian scheme of relative dimension $g$. Book 49 gives the finite free crystal

$$
M_n=H^1_{\mathrm{cr}}(A_1/V_n)
$$

of rank $2g$, with Hodge extension

$$
0\to\omega_{A/V_n}\to M_n
\to\omega_{A^\vee/V_n}^{\vee}\to0.
\tag{11.1}
$$

It also constructs the semilinear finite-level Frobenius, compatible with reduction, and proves that the completed Frobenius becomes an isogeny over the $p$-torsion-free Witt ring. At one finite level, where $p$ is nilpotent, calling Frobenius an isogeny would be meaningless. Finally, Book 49 proves that

$$
H^*_{\mathrm{cr}}(A_1/V_n)
\simeq\bigwedge^*M_n.
\tag{11.2}
$$

The weight-one syntomic complex uses not merely $M_n$ but the filtered derived complex

$$
F^1R\Gamma_{\mathrm{cr}}(A_1/V_n).
$$

On the chosen lift $A/V$ it is represented by

$$
[p\mathcal O_A\to\Omega^1_{A/V}\to
\Omega^2_{A/V}\to\cdots].
\tag{11.3}
$$

In degree one, the induced filtered submodule is the Hodge line bundle $\omega_A$ together with the $p$-multiple of the complementary extension direction. It is not canonically the direct sum $\omega_A\oplus p\omega_{A^\vee}^\vee$, because (11.1) need not split.

The syntomic exact sequence (5.8) therefore retains precisely the non-split integral Hodge extension. Replacing it with the associated graded would lose extension data and could change the set of divided-Frobenius fixed points.

### 11.2 Syntomic classes attached to torsion line bundles

A $p^n$-torsion line bundle $L$ on $A$ with a chosen power trivialization defines

$$
[L,\tau]\in H^1_{\mathrm{syn}}(A,\mathbf Z/p^n(1)).
\tag{11.4}
$$

If $L$ is algebraically trivial, it corresponds to a point of $A^\vee[p^n](V)$. The Poincare bundle $\mathcal P$ on $A\times A^\vee$ is universal for these line bundles. For $y\in A^\vee[p^n](V)$, pull back $\mathcal P$ along $1\times y$ to obtain a rigidified line bundle $L_y$ on $A$. Since $[p^n]y=0$ in the rigidified Picard functor, $L_y^{\otimes p^n}$ has a unique rigidified trivialization $\tau_y$: an automorphism of a rigidified line bundle on a proper geometrically connected group is a base unit whose value at the identity is $1$, hence is the identity. The pair $(L_y,\tau_y)$, not the degree-two Chern class of $L_y$, produces the desired degree-one root torsor.

**Proposition 11.1.** The construction

$$
A^\vee[p^n](V)\longrightarrow
H^1_{\mathrm{syn}}(A,\mathbf Z/p^n(1))
\tag{11.5}
$$

is a homomorphism after power trivializations are rigidified along the identity, and its period is the generic Kummer class of the corresponding line bundle.

**Proof.** The biextension law for $\mathcal P$ identifies the rigidified line bundle attached to $y+y'$ with $L_y\otimes L_{y'}$. By uniqueness, its power trivialization is $\tau_y\otimes\tau_{y'}$. The graded-algebra construction (7.9) therefore identifies the associated root torsor with the contracted product of the two root torsors, proving additivity in $H^1$. Generic restriction carries $(L_y,\tau_y)$ to $(L_{y,K},\tau_{y,K})$, so Theorem 8.2 identifies its period with the generic Kummer class. $\square$

Without a rigidification, changing $\tau$ by a unit changes the class by the left term of (7.7). The homomorphism statement must therefore include this normalization.

### 11.3 Isogenies and division torsors

Multiplication by $p^n$ on $A$ is finite locally free and gives the fppf-exact sequence

$$
0\to A[p^n]\to A\xrightarrow{[p^n]}A\to0.
\tag{11.6}
$$

For $P\in A(V)$, the boundary

$$
\delta_A(P)\in H^1_{\mathrm{fppf}}(V,A[p^n])
\tag{11.7}
$$

is the torsor of division points $Q$ with $p^nQ=P$. This is not itself a weight-one syntomic class because its coefficient is $A[p^n]$, not $\mu_{p^n}$. The bridge is the schematic Weil pairing of Book 35,

$$
e_{p^n}:A[p^n]\times A^\vee[p^n]
\longrightarrow\mu_{p^n}.
\tag{11.8}
$$

For $y\in A^\vee[p^n](V)$, pushout along $e_{p^n}(-,y)$ gives

$$
e_y{}_*(\delta_A(P))
\in H^1_{\mathrm{fppf}}(V,\mu_{p^n})
\simeq H^1_{\mathrm{syn}}(V,\mathbf Z/p^n(1)).
\tag{11.9}
$$

**Proposition 11.2.** The period of (11.9) is the pushout, under the generic Weil pairing, of the generic division torsor of $P_K$. The construction is functorial in homomorphisms of abelian schemes and compatible with the Kummer boundary.

**Proof.** Formation of the kernel of $[p^n]$, the Weil pairing, pushout of torsors, and generic restriction all commute with base change. Naturality of the degree-zero boundary for a commutative diagram of short exact sequences, proved in Book 29, gives the required commutative square. Theorem 8.2 identifies the resulting $\mu_{p^n}$-torsor with its syntomic class. $\square$

This is the precise sense in which the low-weight period map sees division torsors: it sees every character of the finite-flat coefficient through a weight-one class. It does not identify the whole $A[p^n]$-torsor group with one copy of syntomic cohomology.

### 11.4 Polarizations and the weight-one pairing

Let $\lambda:A\to A^\vee$ be a principal polarization. Book 49 supplies a perfect alternating crystalline pairing

$$
\psi_\lambda:M_n\otimes M_n\to V_n(-1)
\tag{11.10}
$$

with

$$
\psi_\lambda(\varphi x,\varphi y)
=p\,\sigma(\psi_\lambda(x,y)).
\tag{11.11}
$$

At finite level the Weil pairing identifies $A[p^n]$ with its Cartier dual. Because the pairing is defined by the Poincare biextension over $V$, torsor pushout by it commutes with both completion and generic restriction.

**Theorem 11.3.** For a principally polarized abelian scheme, the diagram

$$
\begin{array}{ccc}
H^1_{\mathrm{fppf}}(V,A[p^n])\times A[p^n](V)
&\longrightarrow&H^1_{\mathrm{syn}}(V,\mathbf Z/p^n(1))\\
\downarrow&&\downarrow\alpha_{1,n}^1\\
H^1_{\mathrm{et}}(K,A[p^n]_K)\times A[p^n](K)
&\longrightarrow&H^1_{\mathrm{et}}(K,\mu_{p^n})
\end{array}
\tag{11.12}
$$

commutes. The top and bottom arrows are pushout by the Weil pairing.

**Proof.** The Weil pairing is induced by the commutator of the Poincare biextension. It is defined over $V$ and restricts to the generic Weil pairing. Pushout of a torsor is the contracted product with the target coefficient; contracted products commute with flat base change. Hence restricting the upper pushout to $K$ gives the lower pushout. The right vertical period map is generic restriction under Theorem 7.1, so the square commutes. $\square$

For a nonprincipal polarization, the pairing need not be perfect integrally. All compatibility remains valid with the actual finite-flat pairing, but identifying a module with its dual requires inverting the polarization degree.

## 12. Finite-flat group schemes

The catalogued compatibility with finite-flat group schemes must be stated at the right strength. The two syntomic Tate coefficients are universal endpoints, not a classification of every finite-flat group. This chapter proves the exact functorial statements that survive for a general coefficient: generic restriction, character pushout, Cartier pairing, and compatibility of boundary classes.

### 12.1 What compatibility can mean

Let $S$ be a normal smooth $V$-scheme and let $G/S$ be a finite locally free commutative group scheme killed by $p^n$. Its generic fiber $G_K$ is finite etale because the characteristic is zero. There is always a restriction map

$$
\rho_G:H^1_{\mathrm{fppf}}(S,G)
\longrightarrow H^1_{\mathrm{et}}(S_K,G_K).
\tag{12.1}
$$

Syntomic complexes of weights zero and one do not classify torsors under every possible $G$. They provide the two universal low-weight coefficients $\mathbf Z/p^n$ and $\mu_{p^n}$ and test a general torsor through maps to those coefficients. This distinction is essential: a connected group scheme such as $\alpha_p$ in equal characteristic has no generic characteristic-zero counterpart in our setting, while a mixed finite-flat group may have several independent characters.

There are three precise compatibilities to prove:

1. restriction sends an integral $G$-torsor to its generic torsor and detects triviality;
2. a character $G\to\mu_{p^n}$ sends the integral class to a weight-one syntomic class, compatibly with periods;
3. exact sequences and Cartier pairings commute with all boundary and cup-product maps.

These statements are strong enough to preserve finite-flat extension data without claiming a classification of all finite-flat group schemes. Such a classification requires further structure beyond the present dependency range.

### 12.2 Characters and Cartier pairings

The Cartier dual of $G$ is

$$
G^D=\mathcal Hom(G,\mathbf G_m),
$$

and evaluation gives a perfect finite-flat pairing

$$
G\times G^D\longrightarrow\mu_{p^n},
\tag{12.2}
$$

because $G$ is killed by $p^n$. A section $\chi\in G^D(S)$ is exactly a character $G\to\mu_{p^n}$. Pushing out a $G$-torsor $P$ gives a $\mu_{p^n}$-torsor $P\wedge^G\mu_{p^n}$.

**Theorem 12.1 (character compatibility).** For every $[P]\in H^1_{\mathrm{fppf}}(S,G)$ and $\chi\in G^D(S)$,

$$
\alpha_{1,n}^1(\chi_*[P])
=(\chi_K)_*\rho_G([P]).
\tag{12.3}
$$

**Proof.** Pushout is a quotient of $P\times\mu_{p^n}$ by the diagonal $G$-action. All objects are finite locally free, and formation of this quotient commutes with the flat base change $S_K\to S$. Thus restricting the pushed-out torsor is the same as pushing out the restricted torsor. The period morphism in degree one is generic restriction under the Kummer identification, so the two classes agree. $\square$

If the sections of $G^D$ do not separate $G$ over $S$, the collection of character pushouts need not determine $P$. The theorem asserts compatibility, not an unjustified detection statement. After a faithfully flat base change splitting an appropriate diagonalizable part, more characters may become available, and descent controls the return to $S$.

The full Cartier pairing gives cup products

$$
H^a_{\mathrm{fppf}}(S,G)\times
H^b_{\mathrm{fppf}}(S,G^D)
\longrightarrow H^{a+b}_{\mathrm{fppf}}(S,\mu_{p^n}).
\tag{12.4}
$$

Where the right side is represented syntomically, generic restriction and the period morphism preserve (12.4) because cup products are natural in coefficient pairings.

### 12.3 Exact sequences and boundary classes

Let

$$
0\to G'\to G\to G''\to0
\tag{12.5}
$$

be fppf-exact with all three group schemes finite locally free over $S$. For $x\in G''(S)$, the boundary $\delta(x)$ is the $G'$-torsor of lifts of $x$. Generic restriction gives the torsor of lifts of $x_K$, so

$$
\rho_{G'}(\delta(x))=\delta(x_K).
\tag{12.6}
$$

For a character $\chi:G'\to\mu_{p^n}$, Theorem 12.1 turns (12.6) into a commutative square with weight-one syntomic cohomology.

**Proposition 12.2.** Suppose (12.5) maps to the Kummer sequence through a commutative diagram of coefficient sheaves. Then the induced diagram of degree-zero sections, degree-one torsors, syntomic Kummer classes, and generic etale classes commutes, including both connecting morphisms.

**Proof.** The boundary of a section is the fiber torsor. A commutative diagram sends the fiber torsor to the pushout of that torsor, which is the fiber torsor in the lower row. This proves naturality before taking cohomology. Restriction preserves fiber products, and the period map is restriction under Theorem 7.1. Every square therefore commutes. $\square$

Exactness here is sheaf exactness. Surjectivity of $G\to G''$ does not imply that every $S$-point lifts; the boundary class measures precisely that failure.

### 12.4 Finite-flat extension classes on the generic fiber

The following theorem isolates the integral content of finite flatness.

**Theorem 12.3 (finite-flat image theorem).** If $S$ is normal and integral, then (12.1) is injective. Its image consists of the generic $G_K$-torsors admitting a $G$-torsor model over $S$. This image is stable under pushout, pullback, Cartier dual cup products, and boundaries from exact sequences such as (12.5).

**Proof.** The image description is tautological once restriction is defined. For injectivity, a generic trivialization is a generic section of the finite morphism $P\to S$. Its schematic closure is finite birational over $S$ and hence is $S$ by normality, exactly as in Theorem 8.2. The resulting section trivializes $P$.

Pullback and pushout commute with base change by their universal properties. The Cartier cup product is built from pullback to a product torsor followed by the coefficient pairing, so it also commutes. Boundary compatibility is (12.6). $\square$

The theorem does not say that every generic representation which is crystalline of weights $0$ and $1$ admits a finite-flat lattice. It begins with a specified finite-flat group scheme and preserves its torsors. Producing such a model from filtered linear algebra is a separate classification theorem.

Two endpoint examples clarify the result. If $G=\mathbf Z/p^n$, the image consists of finite etale torsors extending across the closed fiber and is controlled by weight zero. If $G=\mu_{p^n}$, the image consists of finite-flat Kummer torsors and is controlled by weight one. A general $G$ interpolates between these behaviors, while its Cartier characters land in the multiplicative endpoint.

## 13. Limits and integral lattices

One finite coefficient level does not determine a $p$-adic lattice. Classes must lift coherently, Bockstein obstructions must vanish, and derived inverse limits may contribute an extra term. This chapter constructs the completed syntomic complexes from all levels and explains why rationalization cannot reconstruct the integral data they retain.

### 13.1 Reduction from level $n+1$ to level $n$

The coefficient groups fit into exact sequences

$$
0\to\mathbf Z/p^m(r)
\longrightarrow\mathbf Z/p^{m+n}(r)
\longrightarrow\mathbf Z/p^n(r)\to0,
\qquad r=0,1.
\tag{13.1}
$$

For $r=0$ these are constant groups. For $r=1$, the last map is $u\mapsto u^{p^m}$ and its kernel is $\mu_{p^m}$; fppf local surjectivity follows by adjoining a $p^m$th root through a finite free monic algebra.

The fundamental exact sequences identify (13.1) with coefficient triangles of syntomic complexes:

$$
\mathscr S_m(r)\longrightarrow
\mathscr S_{m+n}(r)\longrightarrow
\mathscr S_n(r)\longrightarrow\mathscr S_m(r)[1].
\tag{13.2}
$$

**Proposition 13.1.** The triangles (13.2) commute with crystalline reduction, period morphisms, Kummer boundaries, and finite-flat character pushouts.

**Proof.** On the coefficient side all maps come from (13.1). Additivity of the Frobenius-defect construction gives $\ell(u^{p^m})=p^m\ell(u)$, so the fundamental diagrams commute in weight one. Mapping fibers transport the coefficient sequence to (13.2). Generic restriction commutes with powers and with pushout, proving the remaining assertions. $\square$

The long exact sequence of (13.2) contains Bockstein maps. They record the obstruction to lifting a mod-$p^n$ class to level $m+n$. A class at one level does not define a $p$-adic class unless all these obstructions vanish compatibly.

### 13.2 Derived inverse limits

Define the completed coefficient complexes by

$$
R\mathscr S_{\mathbf Z_p}(r)
=R\varprojlim_nR\mathscr S_n(r).
\tag{13.3}
$$

For any inverse system $K_n$, there is a Milnor exact sequence

$$
0\to R^1\!\varprojlim_n H^{q-1}(K_n)
\to H^q(R\varprojlim_nK_n)
\to\varprojlim_nH^q(K_n)\to0.
\tag{13.4}
$$

Thus completed syntomic cohomology is not, by definition, the ordinary inverse limit of finite-level groups.

If the transition maps on $H^{q-1}$ are surjective, the first term vanishes. Surjectivity on the terms of a chosen complex is not by itself surjectivity on cohomology. For proper smooth curves and abelian schemes, the finite free crystalline models of Book 49 and the bounded filtered de Rham representatives allow one to choose degreewise surjective perfect models. The mapping fibers then form a Mittag--Leffler system at the complex level; additional cohomological surjectivity may be checked from the coefficient exact sequence.

For weight one in degree one, Kummer theory gives a concrete test. A compatible system consists of compatible classes in

$$
0\to\Gamma(X,\mathcal O)^\times/
\Gamma(X,\mathcal O)^{\times p^n}
\to H^1_{\mathrm{syn}}(X,1;n)
\to\operatorname{Pic}(X)[p^n]\to0.
\tag{13.5}
$$

The line-bundle components must be compatible under multiplication by $p$, and the power trivializations must agree. An arbitrary sequence of torsion line bundles of increasing order does not suffice.

### 13.3 The completed syntomic complexes

Assume now that $X/V$ is smooth and proper. Book 49 supplies a bounded finite free $V$-complex $K$ representing completed crystalline cohomology. The smooth lift supplies a bounded filtered complex $F^1K$ represented by derived global sections of $[p\mathcal O\to\Omega^1\to\cdots]$. Define

$$
R\Gamma_{\mathrm{syn}}(X,\mathbf Z_p(r))
=\operatorname{Fib}(1-\varphi_r:F^rK\to K),
\qquad r=0,1.
\tag{13.6}
$$

**Theorem 13.2.** The complex (13.6) is derived $p$-complete, and

$$
R\Gamma_{\mathrm{syn}}(X,\mathbf Z_p(r))
\otimes^L_{\mathbf Z_p}\mathbf Z/p^n
\xrightarrow{\sim}
R\Gamma_{\mathrm{syn}}(X,\mathbf Z/p^n(r)).
\tag{13.7}
$$

It agrees with the derived inverse limit (13.3).

**Proof strategy and proof.** Work first over the $p$-torsion-free ring $V$. The de Rham complex of the smooth proper lift is a bounded complex of vector bundles, and so is its first filtered subcomplex

$$
[p\mathcal O_X\longrightarrow\Omega^1_{X/V}
\longrightarrow\Omega^2_{X/V}\longrightarrow\cdots],
$$

because multiplication by $p$ identifies the abstract module $\mathcal O_X$ with $p\mathcal O_X$. Proper coherent finiteness makes the derived global sections $K$ and $F^1K$ perfect over $V$. Choose bounded finite free representatives. The integral divisibility from Chapter 2 defines compatible maps $\varphi_r:F^rK\to K$.

The finite-level source is the **derived reduction** of this integral filtered lattice. In degree zero,

$$
p\mathcal O_X\otimes_VV_n
\simeq p\mathcal O_X/p^{n+1}\mathcal O_X,
\tag{13.8}
$$

which is a free copy of $\mathcal O_{X_n}$ mapped into $\mathcal O_{X_n}$ by multiplication by $p$. It is not the literal ideal $p\mathcal O_{X_n}$, whose last $p$-adic digit has been lost. Definition (2.7) retains exactly that extra digit, so (13.8) identifies the derived reduction of $F^1K$ with the modified finite-level filtered complex. The same comparison is immediate in positive de Rham degrees, and Book 49 identifies $K\otimes_V^LV_n$ with $K_n$. The divided Frobenius maps agree because (2.8) was defined by division one level higher. Therefore derived reduction of the arrow $1-\varphi_r$ is the finite-level arrow defining $R\Gamma_{\mathrm{syn}}(X,\mathbf Z/p^n(r))$.

Derived tensor product commutes with a finite homotopy limit, so reducing the mapping fiber gives the mapping fiber of the reduced arrow. This proves (13.7). The bounded finite free representatives are derived $p$-complete and have degreewise surjective quotient towers. Their inverse limits therefore have no $R^1\!\varprojlim$ term. Since derived inverse limits also commute with mapping fibers, (13.6) agrees with (13.3) and is derived $p$-complete. $\square$

Taking cohomology of (13.7) still yields the correction term (5.12). The theorem is a statement about complexes, not automatic torsion-freeness of their cohomology.

### 13.4 Rationalization does not recover the lattice

After tensoring (13.6) with $K$, Frobenius becomes invertible on crystalline cohomology for smooth proper special fibers. The rational mapping fiber is then governed by slope and filtration linear algebra. But the integral syntomic complex remembers more:

- the actual subcomplex $F^1K$, not merely its $K$-span;
- divisibility of Frobenius by $p$ before cancellation;
- the cokernels of $1-\varphi_r$ on lattices;
- compatible torsors at every finite level.

For example, a rational weight-one line $Ke$ with $\varphi(e)=pe$ contains every homothetic lattice $p^aVe$. Rational Frobenius does not single out one of them or canonically identify their embedded finite quotients inside a chosen ambient representation. The finite-level systems and their period maps require an actual lattice together with its filtered embedding; forgetting that embedding erases the datum the construction is meant to recover.

The Kummer example is even more concrete. A unit $u\in V^\times$ defines a $\mu_{p^n}$-torsor over $V$, while $pu\in K^\times$ defines only a generic root torsor: the equation $T^{p^n}=pu$ is not a $\mu_{p^n}$-torsor on the special fiber. This valuation obstruction is invisible if one retains only an unspecified rational comparison object. Rational comparison is therefore a consequence one may later extract; it cannot serve as the definition of the lattice.

## 14. Descent, base change, and exactness

The preceding constructions used local embeddings, local Frobenius lifts, and several coefficient levels. They become reusable only after their independence and functoriality have been consolidated. This chapter proves descent, states the correct pullback behavior under unramified coefficient change, and collects the precise hypotheses that guard every clean formula.

### 14.1 Syntomic descent

The local constructions were made after choosing smooth embeddings and Frobenius lifts. Proposition 3.1 handled independence in the derived category. We now record the corresponding descent theorem.

**Theorem 14.1.** The assignments

$$
U\longmapsto\mathscr S_n(r)|_U,
\qquad r=0,1,
$$

satisfy descent for syntomic covers. Their pullback maps are transitive, the fundamental quasi-isomorphisms descend, and the period morphisms are compatible with descent.

**Proof strategy and proof.** On a cover choose smooth embeddings and Frobenius lifts. On a double overlap, use the divided-power envelope of the product embedding to obtain the canonical comparison. On a triple overlap, the three comparisons pull back from the triple product envelope and satisfy the cocycle condition by transitivity of crystalline Taylor transport. Thus the local filtered complexes and Frobenius maps descend in the derived category.

The local kernel identifications are natural: constants pull back to constants, and divided-power logarithm commutes with every PD morphism. Hence (4.14) descends with the complex. Generic restriction of torsors is already a morphism of topoi and respects descent. Therefore the period maps descend as well. $\square$

This theorem is why local Frobenius lifts may be used freely in calculations without becoming part of the final data.

### 14.2 Unramified change of the base

Let $k\subset k'$ be an extension of perfect fields and $V'=W(k')$. Put $X'=X\times_VV'$. Witt Frobenius is compatible with the base map, and divided powers on $(p)$ extend canonically.

**Theorem 14.2.** There are canonical pullback morphisms

$$
R\Gamma_{\mathrm{syn}}(X,\mathbf Z/p^n(r))
\longrightarrow
R\Gamma_{\mathrm{syn}}(X',\mathbf Z/p^n(r)),
\tag{14.1}
$$

and similarly at the completed level. They commute with fundamental sequences, period maps, cup products, Chern classes, traces for curves, and Poincare pairings for abelian schemes. The underlying filtered crystalline complexes satisfy derived $V$-base change, but the syntomic fibers themselves are only $\mathbf Z/p^n$-linear and need not be unchanged by extending $k$.

**Proof.** Crystalline derived base change and filtered de Rham base change compare both arrows $1-\varphi_r$. Functoriality of mapping fibers gives (14.1). The fundamental coefficient sheaves pull back to the corresponding constants and roots of unity. Every listed operation is constructed from pullback, tensor product, trace, or the Poincare bundle, all of which commute with unramified base change by Books 29 and 49. $\square$

Even when crystalline cohomology base-changes perfectly, Frobenius fixed points need not be obtained by tensoring fixed points. The pullback in (14.1) is therefore the unconditional statement.

### 14.3 Coefficient exact sequences

The exact coefficient sequences (13.1) make syntomic cohomology a genuine integral cohomology theory in low weight.

**Proposition 14.3.** For $m,n\geq1$ and $r=0,1$, there is a natural long exact Bockstein sequence

$$
\cdots\to H^q_{\mathrm{syn}}(X,\mathbf Z/p^m(r))
\to H^q_{\mathrm{syn}}(X,\mathbf Z/p^{m+n}(r))
\to H^q_{\mathrm{syn}}(X,\mathbf Z/p^n(r))
\xrightarrow{\beta}H^{q+1}_{\mathrm{syn}}(X,\mathbf Z/p^m(r))
\to\cdots.
\tag{14.2}
$$

Under the period morphism it maps to the generic etale Bockstein sequence. In weight one and degree zero, $\beta$ sends a root of unity modulo $p^n$ to its torsor of lifts to a $p^{m+n}$th root.

**Proof.** Apply hypercohomology to the triangle (13.2). Period compatibility follows from Proposition 13.1. The description of the degree-zero boundary is the general torsor-of-lifts description of a connecting morphism from Book 29, applied to the exact sequence of roots of unity. $\square$

For short exact sequences of finite-flat coefficient groups other than the two Tate coefficients, Chapter 12 supplies compatible torsor boundaries but not necessarily a syntomic mapping-fiber realization. Keeping these two levels distinct prevents a false generalization.

### 14.4 A hypothesis ledger

The following table records the precise scope of the constructions.

| Assertion                                          | Hypotheses used                                             | What fails without them                                            |
| -------------------------------------------------- | ----------------------------------------------------------- | ------------------------------------------------------------------ |
| canonical base Frobenius                           | $V=W(k)$ with $k$ perfect                                   | a ramified base has no such unqualified lift                       |
| $\varphi_1=\varphi/p$ at finite level              | modified filtration $\mathscr J^{\langle1\rangle}$          | division by $p$ can depend on a lift                               |
| local fundamental sequences                        | weights $0,1$, smooth unramified setting, syntomic topology | derivative-one lifting or Frobenius divisibility may fail          |
| $\mathscr S_n(1)\simeq\mu_{p^n}$                   | finite-flat, not merely etale, coefficient theory           | geometric points lose infinitesimal roots                          |
| degree-one syntomic/fppf comparison                | the lci coefficients $\mathbf Z/p^n$ and $\mu_{p^n}$        | an arbitrary finite-flat torsor need not be a syntomic cover       |
| injectivity of generic restriction                 | normality on every component                                | a generic section need not extend over a nonnormal base            |
| image equals extendable classes                    | a fixed integral coefficient model                          | a generic group alone does not select a model                      |
| ordinary reduction of completed cohomology         | vanishing of the neighboring $p^n$-torsion group            | derived reduction may have a correction term                       |
| ordinary inverse limit computes completion         | Mittag--Leffler condition                                   | an $R^1\varprojlim$ term survives                                  |
| curve and abelian finite crystalline modules       | smoothness and properness                                   | nonproper or singular cohomology has different finiteness behavior |
| perfect polarization pairing                       | principal polarization, or inversion of its degree          | the integral pairing can have cokernel                             |
| character tests determine a $G$-torsor             | enough characters after a stated cover                      | Cartier characters need not separate a general $G$ over the base   |
| full integral classification of finite-flat groups | additional low-height classification theory                 | the two syntomic Tate coefficients do not classify arbitrary $G$   |

Each restriction is attached to a step in a proof. None is inferred merely from the existence of a rational Frobenius module.

## 15. The low-weight integral comparison package

The final chapter packages the theory in the form needed later: intrinsic complexes, fundamental exact sequences, integral period maps, and finite-flat compatibility. It also separates the proved good-reduction low-weight range from nearby statements that require ramification bounds, logarithmic structures, or a classification of finite-flat objects.

### 15.1 The main theorem

We can now collect the constructions into one statement.

**Theorem 15.1 (low-weight syntomic and period package).** Let $k$ be perfect of characteristic $p$, let $V=W(k)$, and let $X/V$ be smooth. Use the modified first filtration at finite level. For every $n\geq1$:

1. The complexes

   $$
   \mathscr S_n(0)=\operatorname{Fib}(1-\varphi),
   \qquad
   \mathscr S_n(1)=\operatorname{Fib}(1-\varphi_1:F^1K_n\to K_n)
   $$

   are intrinsic and satisfy syntomic descent.
2. There are fundamental quasi-isomorphisms

   $$
   \mathbf Z/p^n\xrightarrow{\sim}\mathscr S_n(0),
   \qquad
   \mu_{p^n}\xrightarrow{\sim}\mathscr S_n(1).
   $$
3. Derived global sections fit into the Frobenius mapping-fiber triangle (5.6) and the kernel-cokernel exact sequence (5.8).
4. There are canonical integral period morphisms

   $$
   R\mathscr S_n(r)\to i^*Rj_*\mathbf Z/p^n(r),
   \qquad r=0,1.
   $$
5. In degrees zero and one, the period map is injective and its image is exactly the torsor classes extending over $X$ under the indicated finite locally free coefficient.
6. The construction commutes with pullback under unramified base change, coefficient sequences, Kummer boundaries, the available cup products, and first Chern classes.
7. Characters of any finite locally free commutative $p^n$-torsion group scheme carry its integral torsors to weight-one syntomic classes, and this operation commutes with generic realization. Exact sequences and Cartier pairings are compatible as in Chapter 12.
8. If $X$ is proper, the completed complexes are derived $p$-complete and recover all finite levels by derived reduction. For curves and abelian schemes they inherit the finite crystalline, Frobenius, Hodge, trace, and polarization structures proved in Book 49.

**Proof.** Intrinsic construction and descent are Proposition 3.1 and Theorem 14.1. The fundamental sequences are Theorem 4.5. The mapping-fiber and kernel-cokernel sequences are Proposition 5.1 and Corollary 5.2. Period maps are Definition 8.1, and their degree-zero and degree-one image theorem is Theorem 8.2. Functorialities are Theorems 9.1 and 14.2 together with Propositions 8.3, 13.1, and 14.3. Finite-flat compatibility is Theorems 12.1 and 12.3 and Proposition 12.2. Completion is Theorem 13.2. The curve and abelian structures are Chapters 10 and 11. $\square$

The theorem is a construction theorem, an exact-sequence theorem, and an image theorem. Its strongest integral assertion is not that every generic class is syntomic, but that syntomic degree-one classes are exactly those generic torsors which possess the stated finite-flat model.

### 15.2 What the theorem does not say

Several nearby statements are false or require later theory.

First, weights zero and one do not automatically construct weight two. A cup product of two weight-one classes has coefficient $\mu_{p^n}^{\otimes2}$, but an integral mapping-fiber description in weight two requires stronger Frobenius divisibility and a corresponding range theorem.

Second, a rational crystalline representation with Hodge weights in $\{0,1\}$ does not by itself select a finite-flat lattice. The present theory starts from the integral crystalline filtration or from an actual finite-flat coefficient and proves compatibility. Reconstructing group schemes from filtered modules is a deeper equivalence.

Third, the unramified hypothesis cannot be discarded by notation. Over a ramified valuation ring, divided Frobenius interacts with the ramification index, and generic nearby cycles can contain additional classes. Semistable reduction requires logarithmic structures and monodromy; the smooth good-reduction complex here has no monodromy operator.

Fourth, a period morphism need not be surjective. The generic Kummer class of a uniformizer is the elementary counterexample. Surjectivity becomes plausible only after replacing the source by a theory designed to include ramification or after truncating and imposing a comparison range with its full hypotheses.

Finally, perfectness of a derived complex does not force its cohomology to be torsion-free. Every passage from derived reduction to ordinary reduction must check the neighboring torsion term.

### 15.3 A reusable calculation protocol

A reliable low-weight calculation follows a fixed order.

1. Specify the integral base, its Frobenius, and whether the geometry is smooth and proper.
2. Form the crystalline complex and the actual filtered subcomplex; do not replace the latter by an associated graded module.
3. Use the modified first filtration before dividing Frobenius by $p$.
4. Form the mapping fiber with the convention $\operatorname{Cone}(1-\varphi_r)[-1]$.
5. Write the long exact sequence and then the kernel-cokernel short exact sequence.
6. In weight zero identify the coefficient with $\mathbf Z/p^n$; in weight one identify it with $\mu_{p^n}$ through divided-power logarithm.
7. Translate degree-one classes into actual torsors and apply Kummer theory when $r=1$.
8. Apply the period map as generic restriction and state its image as the extendable subgroup.
9. Check coefficient reduction and inverse-limit error terms before passing to a $p$-adic lattice.
10. For a general finite-flat group scheme, use its actual characters and Cartier pairing; do not replace it by one of the two Tate coefficients without a map.

This order keeps filtration, Frobenius, topology, and generic restriction visible at the points where each matters.

### 15.4 Conclusion

Syntomic cohomology in weights zero and one is the integral fixed-point theory of crystalline Frobenius. Weight zero compares the identity with Frobenius on the whole crystalline complex and recovers constant $p$-power torsors. Weight one enters the first Hodge filtration, divides Frobenius exactly once, and recovers the nonreduced finite-flat group schemes of roots of unity. The divided-power exponential and logarithm make the second identification integral, including at the residue prime.

The mapping fiber carries local exactness into global arithmetic. Its long exact sequence separates Frobenius-difference cokernels from filtered fixed points; Kummer theory translates the same group into units, powered line bundles, and root torsors. The integral period morphism then has a concrete meaning: it restricts an integral torsor to the generic fiber. On a normal smooth model it is injective in degree one, and its image is exactly the extendable finite-flat subgroup. A uniformizer class shows why this subgroup is generally proper.

For curves and abelian schemes, the crystalline package of Book 49 supplies finite free degree-one modules, Hodge extensions, Frobenius, traces, Poincare classes, and polarizations. Syntomic cohomology adds the missing integral comparison with torsors. Cartier characters and Weil pairings carry the construction to arbitrary specified finite-flat group schemes without pretending to classify them. Coefficient triangles and derived inverse limits preserve the information through every $p^n$-level.

The resulting chain is now complete:

$$
\text{divided-power filtration and Frobenius}
\longrightarrow
\text{low-weight syntomic mapping fiber}
\longrightarrow
\text{finite-flat torsor}
\longrightarrow
\text{generic etale class}.
$$

Every arrow is integral, functorial, and accompanied by its exact hypotheses. That is the period map needed in low-weight finite-flat geometry: not a rational identification with an unspecified lattice, but a controlled passage from crystalline divisibility to the actual generic torsors which extend across the closed fiber.
