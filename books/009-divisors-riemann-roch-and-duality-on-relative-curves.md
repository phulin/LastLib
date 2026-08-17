# Divisors, Riemann--Roch, and Duality on Relative Curves

## Contents

1. [Curves and the questions divisors answer](#1-curves-and-the-questions-divisors-answer)
   - [The absolute and relative settings](#11-the-absolute-and-relative-settings)
   - [Dimension one as a meeting point](#12-dimension-one-as-a-meeting-point)
   - [Standing conventions and hypotheses](#13-standing-conventions-and-hypotheses)
2. [Cartier divisors](#2-cartier-divisors)
   - [Local equations modulo units](#21-local-equations-modulo-units)
   - [Effective Cartier divisors](#22-effective-cartier-divisors)
   - [Pullback, restriction, and flatness](#23-pullback-restriction-and-flatness)
   - [Orders along a curve](#24-orders-along-a-curve)
3. [Weil divisors and regularity](#3-weil-divisors-and-regularity)
   - [Codimension-one cycles](#31-codimension-one-cycles)
   - [From Cartier to Weil](#32-from-cartier-to-weil)
   - [Normal curves and regular models](#33-normal-curves-and-regular-models)
   - [Where the dictionaries fail](#34-where-the-dictionaries-fail)
4. [Line bundles, rational sections, and Picard groups](#4-line-bundles-rational-sections-and-picard-groups)
   - [The bundle attached to a divisor](#41-the-bundle-attached-to-a-divisor)
   - [Rational sections recover divisors](#42-rational-sections-recover-divisors)
   - [Principal divisors and linear equivalence](#43-principal-divisors-and-linear-equivalence)
   - [The divisor--Picard correspondence](#44-the-divisor--picard-correspondence)
5. [Degree and intersection with fibers](#5-degree-and-intersection-with-fibers)
   - [Degree over a field](#51-degree-over-a-field)
   - [Euler characteristic and degree](#52-euler-characteristic-and-degree)
   - [Degree in a proper flat family](#53-degree-in-a-proper-flat-family)
   - [Horizontal divisors and fibers](#54-horizontal-divisors-and-fibers)
6. [Effective relative divisors and symmetric powers](#6-effective-relative-divisors-and-symmetric-powers)
   - [The correct relative notion](#61-the-correct-relative-notion)
   - [Smooth curves turn points into divisors](#62-smooth-curves-turn-points-into-divisors)
   - [Universal divisors and addition](#63-universal-divisors-and-addition)
   - [Nodal fibers and the boundary](#64-nodal-fibers-and-the-boundary)
7. [Differentials on curves](#7-differentials-on-curves)
   - [Kähler differentials and local parameters](#71-kähler-differentials-and-local-parameters)
   - [Canonical divisors on smooth curves](#72-canonical-divisors-on-smooth-curves)
   - [Differentials at singular points](#73-differentials-at-singular-points)
8. [Residues](#8-residues)
   - [What a residue must be, and why the obvious definition fails](#81-what-a-residue-must-be-and-why-the-obvious-definition-fails)
   - [Residues on the affine line](#82-residues-on-the-affine-line)
   - [The local residue on a smooth curve](#83-the-local-residue-on-a-smooth-curve)
   - [The principal-part pairing](#84-the-principal-part-pairing)
   - [The global residue theorem](#85-the-global-residue-theorem)
   - [Finite maps and trace](#86-finite-maps-and-trace)
9. [Dualizing sheaves](#9-dualizing-sheaves)
   - [Why ordinary differentials are not enough](#91-why-ordinary-differentials-are-not-enough)
   - [Dualizing sheaves on proper curves](#92-dualizing-sheaves-on-proper-curves)
   - [The relative dualizing sheaf](#93-the-relative-dualizing-sheaf)
   - [Smooth and Gorenstein families](#94-smooth-and-gorenstein-families)
   - [Proper pushforward, Stein factorization, and connected fibers](#95-proper-pushforward-stein-factorization-and-connected-fibers)
10. [Nodes, normalization, and opposite residues](#10-nodes-normalization-and-opposite-residues)
    - [The local node](#101-the-local-node)
    - [Functions under normalization](#102-functions-under-normalization)
    - [Rosenlicht differentials](#103-rosenlicht-differentials)
    - [Families of nodal curves](#104-families-of-nodal-curves)
    - [The completed local model at a node](#105-the-completed-local-model-at-a-node)
11. [Riemann--Roch over a field](#11-riemann--roch-over-a-field)
    - [The theorem and its meaning](#111-the-theorem-and-its-meaning)
    - [Proof by adding points](#112-proof-by-adding-points)
    - [Consequences and examples](#113-consequences-and-examples)
    - [Gorenstein and nodal curves](#114-gorenstein-and-nodal-curves)
12. [Serre duality](#12-serre-duality)
    - [The residue pairing](#121-the-residue-pairing)
    - [Perfectness](#122-perfectness)
    - [Duality for line bundles and vector bundles](#123-duality-for-line-bundles-and-vector-bundles)
    - [Functoriality](#124-functoriality)
13. [Relative Riemann--Roch and cohomology in families](#13-relative-riemann--roch-and-cohomology-in-families)
    - [A two-term model](#131-a-two-term-model)
    - [Semicontinuity and base change](#132-semicontinuity-and-base-change)
    - [Relative Riemann--Roch](#133-relative-riemann--roch)
    - [Useful vanishing ranges](#134-useful-vanishing-ranges)
14. [Relative duality and base change](#14-relative-duality-and-base-change)
    - [Trace and the relative pairing](#141-trace-and-the-relative-pairing)
    - [The base-change theorem](#142-the-base-change-theorem)
    - [The Hodge bundle in smooth and nodal families](#143-the-hodge-bundle-in-smooth-and-nodal-families)
    - [Failure modes](#144-failure-modes)
15. [Divisor and differential tools for later geometry](#15-divisor-and-differential-tools-for-later-geometry)
    - [Abel maps before the Picard scheme](#151-abel-maps-before-the-picard-scheme)
    - [The infinitesimal Abel map](#152-the-infinitesimal-abel-map)
    - [A formal-immersion criterion](#153-a-formal-immersion-criterion)
    - [A reusable theorem package](#154-a-reusable-theorem-package)
    - [Conclusion](#155-conclusion)

## 1. Curves and the questions divisors answer

### 1.1 The absolute and relative settings

A function on a curve carries two kinds of information. Away from finitely many points it is a unit; at the exceptional points it has zeros or poles, each with an integer order. A differential carries similar local information, but its coefficient of $dt/t$ survives every change of parameter and produces a residue. Divisor theory extracts the first pattern, while duality explains why the second pattern controls global cohomology.

The relative problem is subtler. If a curve varies over a base $S$, a point of one fiber need not extend to a section, and a closed subscheme of constant length can collide or acquire nilpotents. Degrees should nevertheless remain constant in a flat proper family. Spaces of functions and differentials may jump, yet their Euler characteristic should not. At a nodal specialization the sheaf of ordinary differentials develops torsion, while the differentials relevant to duality remain well behaved.

This book develops one language that survives all these changes. Its central objects are

$$
\text{divisors}\longleftrightarrow\text{line bundles},
\qquad
\text{residues}\longleftrightarrow\text{duality},
$$

and its central numerical identity is Riemann--Roch. Book 8 constructed projective families, Hilbert polynomials, finite flat length-$d$ subschemes, and symmetric powers. We now explain why those parameter spaces are divisor spaces and how their infinitesimal geometry is read by differentials.

### 1.2 Dimension one as a meeting point

Codimension one is where a single equation ought to define a subspace. On a regular curve every closed point has codimension one and its local ring is a discrete valuation ring. Thus an integer at each closed point is simultaneously a cycle, a collection of local equations, and a prescription for allowing poles. This coincidence is special. On a singular curve a codimension-one cycle need not be locally principal; on a higher-dimensional normal space a codimension-one prime can fail to be Cartier.

Dimension one also forces coherent cohomology into degrees $0$ and $1$. A proper curve has no higher coherent cohomology. Consequently an Euler characteristic is a difference of two dimensions, and duality can exchange the two. These elementary-looking facts are the reason the theory is both computable and powerful.

There is also a useful tension between local and global reasoning. Orders of vanishing, Cartier equations, and residues are checked in one-dimensional local rings. Degree, linear equivalence, and the existence of a differential with prescribed poles are global matters. Completeness is what joins the two scales: on an affine curve a rational function may have one uncompensated pole at the missing boundary, whereas on a proper curve every local contribution participates in a global balance. Throughout the book, exact sequences are the mechanism that makes this passage visible. Their quotient terms are supported at finitely many points, so a global change can be measured by a finite sum of local lengths or residues.

The relative dimension-one condition suggests a two-term character. We will prove that
the cohomology of a vector bundle in a projective flat family is locally represented by a map
between two finite free modules. Kernels may jump,
cokernels may jump, but their rank difference does not. This is the algebra beneath
semicontinuity, base change, and relative Riemann--Roch.

### 1.3 Standing conventions and hypotheses

A **proper curve over a field** $k$ means a proper $k$-scheme of finite type, pure of dimension one. When integrality, reducedness, geometric connectedness, smoothness, or the Gorenstein property is needed, it will be stated. For a field extension $K/k$, write $X_K=X\times_k K$.

A **relative curve** is a proper, flat, finitely presented morphism

$$
f:X\longrightarrow S
$$

whose geometric fibers are pure of dimension one. We generally assume $S$ locally noetherian when using finiteness or duality. A smooth relative curve has smooth geometric fibers. A nodal relative curve is a relative curve whose geometric fibers are reduced and have only ordinary double points; for the strongest relative statements we additionally require the morphism to be Gorenstein. Standard nodal families, locally cut out by one equation in a smooth surface over $S$, are Gorenstein.

For a coherent sheaf $\mathcal F$ on a proper $k$-curve,

$$
h^i(X,\mathcal F)=\dim_k H^i(X,\mathcal F),
\qquad
\chi(X,\mathcal F)=h^0(X,\mathcal F)-h^1(X,\mathcal F).
$$

If $X$ is geometrically connected and proper over $k$, then $H^0(X,\mathcal O_X)=k$ when $X$ is geometrically reduced. Its arithmetic genus is

$$
p_a(X)=1-\chi(X,\mathcal O_X)=h^1(X,\mathcal O_X).
$$

No algebraic closure is silently assumed. Degrees of closed points always include residue-field degrees.

We use the elementary noetherian fact that a one-dimensional normal local domain is a discrete
valuation ring. Valuations are normalized by $\operatorname{ord}_x(t)=1$, and finite local lengths
are module lengths. Factoriality of regular local rings is **not** assumed anywhere. The only
consequence of it that this book uses is that a height-one prime of a regular local ring of
dimension at most two is principal, and that statement is proved from scratch in Proposition 3.1
below; every scheme to which we apply it has regular local rings of dimension at most two.

The cohomological background is the quasi-coherent formalism of Books 7a and 7b, used as a fixed
interface rather than reconstructed. From Book 7b we take: the affine dictionary
(Corollaries 2.4--2.6); permanence of quasi-coherence under kernels, cokernels, extensions,
colimits, tensor products, pullback, and quasi-compact quasi-separated pushforward
(Theorems 2.7, 2.8, 2.10); coherent exhaustion of a quasi-coherent sheaf on a noetherian scheme
(Theorem 2.11); Serre's affine vanishing theorem (Theorem 3.9), acyclicity of affine opens
(Corollary 3.10), and cohomological invisibility of affine morphisms (Corollary 3.11); the finite
alternating Čech model on a quasi-compact separated scheme (Theorem 4.2) with its long exact
sequences (Corollary 4.4) and Mayer--Vietoris (Theorem 4.3); quasi-coherence of higher direct
images (Theorem 4.7); the cohomological-dimension bound supplied by a finite affine cover
(Corollary 4.8); the Leray spectral sequence for quasi-coherent sheaves and its degeneration over
an affine base (Corollary 4.9); derived coefficient change and derived base change for a base-flat
quasi-coherent sheaf (Lemma 5.1, Theorem 5.2), together with the underived flat-base-change
statements (Theorem 5.3, Corollary 5.4); commutation of cohomology with filtered colimits
(Propositions 5.5 and 5.6, Corollary 5.7); Grothendieck's vanishing theorem on a noetherian space
of finite dimension (Theorem 5.8, Corollary 5.9); the complete computation of the cohomology of
the twisting sheaves on projective space, its freeness and base-change behaviour, and its perfect
top pairing (Theorem 6.5, Corollary 6.6, Theorem 6.7); and the graded syzygy theorem with its
stability under field extension (Theorem 7.4, Corollary 7.5). From Book 7a we take the derived
category and its replacement theory: K-injective and K-flat complexes, their existence, and the
internal refinement needed for sheaf-valued Hom (Sections 3.2--3.6, summarized in the checklist of
Section 3.8); derived global sections, derived tensor product, derived internal Hom, and the
tensor--Hom and projection formulas (Sections 4.1--4.4); change of rings (Section 4.5); strong
convergence and edge maps for first-quadrant spectral sequences (Sections 6.1, 6.3); and the Leray
spectral sequence with its functoriality (Sections 8.1, 8.2).

Two immediate consequences of that interface are used constantly and are worth isolating. First, a
proper curve over a field is a noetherian scheme of dimension one, so Corollary 5.9 of Book 7b
gives $H^p(X,\mathcal F)=0$ for $p\geq2$ and every quasi-coherent $\mathcal F$; the same conclusion
follows from Corollary 4.8(1) of Book 7b once a two-element affine cover is available. Second, a
zero-dimensional noetherian scheme is affine, so Theorem 3.9 of Book 7b makes its higher cohomology
vanish; this is what allows the quotient terms of the divisor sequences below to be counted by
lengths alone. Finite-dimensionality of coherent cohomology is supplied by Book 8 in the projective
case and is proved for arbitrary proper curves in Section 9.3.

The substantial projective inputs are the results of Book 8: Serre vanishing, polynomiality and
constancy of Euler characteristics in flat projective families, and the universal-divisor
description of symmetric powers of smooth relative curves.
Whenever a relative statement needs projectivity rather than properness alone, that hypothesis is
stated in the theorem.

The second half needs more homological algebra than the preceding books. We develop the required
dimension-one portion rather than assuming a general exceptional-inverse-image formalism.
The proof has three concrete ingredients: finite locally free resolutions on projective space,
the Čech coefficient pairing for projective-space duality, and concentration of the dual
resolution in the codimension prescribed by Cohen--Macaulayness. The same complexes over a
base prove relative duality, embedding independence, perfect pushforward, and arbitrary base
change. The divisor calculation

$$
\chi(\mathcal O_X(D))-\chi(\mathcal O_X)=\deg D
$$

and the resulting Euler-characteristic form of Riemann--Roch do not use duality. We preserve
this separation so that numerical Riemann--Roch is not made to depend circularly on the theorem
which later supplies its symmetric form.

## 2. Cartier divisors

### 2.1 Local equations modulo units

A zero of a function is not determined by the function: multiplying by a nowhere-vanishing function changes no zero or multiplicity. This suggests recording local meromorphic equations only modulo regular units.

Let $X$ be a locally noetherian scheme. Its sheaf of total quotient rings $\mathcal K_X$ is obtained on each open set by inverting regular elements, meaning non-zero-divisors. A **Cartier divisor** is a global section of

$$
\mathcal K_X^\times/\mathcal O_X^\times.
$$

Concretely it is an open cover $X=\bigcup U_i$ with $f_i\in\mathcal K_X^\times(U_i)$ such that $f_i/f_j\in\mathcal O_X^\times(U_i\cap U_j)$. Addition multiplies equations, the negative replaces each equation by its inverse, and zero is represented by units.

This definition works on reducible and nonreduced schemes because regular elements, rather than merely nonzero elements, are inverted. On an integral scheme $\mathcal K_X$ is the constant sheaf of the function field. On a reduced scheme with finitely many irreducible components, it is generically a product of their function fields.

The support of a Cartier divisor $D$ is the locus where no local equation is a unit. It is closed when $X$ is noetherian. A Cartier divisor may have positive and negative parts only under additional hypotheses; the definition itself is signed local data, not a closed subscheme.

### 2.2 Effective Cartier divisors

A Cartier divisor $D$ is **effective** if it has local equations $f_i\in\mathcal O_X(U_i)$ that are regular elements. Then the ideals $(f_i)$ agree on overlaps and define an invertible ideal sheaf

$$
\mathcal I_D=\mathcal O_X(-D)\subseteq\mathcal O_X.
$$

The associated closed subscheme has structure sheaf fitting into

$$
0\longrightarrow\mathcal O_X(-D)
\longrightarrow\mathcal O_X
\longrightarrow\mathcal O_D
\longrightarrow0. \tag{2.1}
$$

Conversely, a closed subscheme whose ideal is locally generated by one regular element is an effective Cartier divisor. The regular-element condition is decisive: if $f$ is a zero-divisor, multiplication by $f$ is not injective, (2.1) is not exact on the left, and the putative hypersurface can contain an entire component.

For example, on $X=\operatorname{Spec}k[x,y]/(xy)$, the function $x$ vanishes on one irreducible component and is a zero-divisor. Its zero scheme is not an effective Cartier divisor. The function $x+y$, however, avoids both minimal primes and does define one.

If $D$ and $E$ are effective Cartier divisors, their sum is defined by $\mathcal I_D\mathcal I_E$. Multiplicities are built in: $nD$ has local equation $f^n$. Scheme structure is therefore essential even when the support is a single point.

### 2.3 Pullback, restriction, and flatness

Given $g:Y\to X$, one would like to pull back local equations of $D$. This is possible precisely when every pulled-back equation remains a regular element of $\mathcal O_Y$. In particular, flat morphisms preserve regular elements, so every Cartier divisor pulls back along a flat morphism. An arbitrary morphism can fail: pulling a divisor back along a map whose image lies inside its support turns its equation into zero.

If $D$ is effective and $g$ is flat, then

$$
0\to\mathcal O_Y(-g^*D)\to\mathcal O_Y\to\mathcal O_{D\times_XY}\to0
$$

is the pullback of (2.1). Thus effective Cartier divisors commute with flat base change as closed subschemes.

A useful refinement concerns a relative curve $X\to S$. Suppose $D\subset X$ is an effective Cartier divisor and $D\to S$ is flat. For every $s\in S$, the fiber $D_s$ is an effective Cartier divisor on $X_s$: tensoring (2.1) with $\kappa(s)$ preserves injectivity. Without flatness of $D$ over $S$, the equation may become a zero-divisor or even zero on a special fiber. The divisor cut out by a parameter of the base is the simplest warning: it is Cartier on $X$ but contains a whole fiber and is not a divisor on that fiber.

### 2.4 Orders along a curve

Let $X$ be a regular integral noetherian curve and $x$ a closed point. The local ring $\mathcal O_{X,x}$ is a discrete valuation ring. Its normalized valuation

$$
\operatorname{ord}_x:k(X)^\times\longrightarrow\mathbf Z
$$

measures the exponent of a uniformizer. For a Cartier divisor represented near $x$ by $f$, define $\operatorname{ord}_x(D)=\operatorname{ord}_x(f)$. A unit changes this by zero.

Only finitely many orders are nonzero. Indeed the support is closed and omits the generic point; on a noetherian one-dimensional scheme it is a finite set. Thus

$$
D=\sum_{x\in X^{(1)}}\operatorname{ord}_x(D)[x].
$$

If $f\in k(X)^\times$, its **principal divisor** is

$$
\operatorname{div}(f)=\sum_x\operatorname{ord}_x(f)[x].
$$

The valuation law immediately gives $\operatorname{div}(fg)=\operatorname{div}(f)+\operatorname{div}(g)$. This innocent identity is the algebraic source of linear equivalence.

## 3. Weil divisors and regularity

### 3.1 Codimension-one cycles

Local equations are excellent for tensor products and pullback, but sometimes one first sees only irreducible subspaces with multiplicities. On a noetherian scheme $X$, a **prime divisor** is an integral closed subscheme of codimension one. A **Weil divisor** is a finite formal sum

$$
Z=\sum_{\xi\in X^{(1)}}n_\xi[\overline{\{\xi\}}],
\qquad n_\xi\in\mathbf Z.
$$

Here $X^{(1)}$ denotes codimension-one points. Effectivity means $n_\xi\geq0$. Weil divisors remember generic multiplicity along codimension-one components but generally forget embedded points and detailed scheme structure.

If $X$ is normal and integral, every local ring at a codimension-one point is a discrete valuation ring. Hence a rational function has a well-defined order there, and

$$
\operatorname{div}(f)=\sum_{\xi\in X^{(1)}}\operatorname{ord}_\xi(f)[\overline{\{\xi\}}].
$$

Finiteness follows by writing $f=a/b$ on an affine open and using that a noetherian ring has only finitely many minimal primes over $(a)$ and $(b)$.

### 3.2 From Cartier to Weil

On a normal integral noetherian scheme, a Cartier divisor $D$ determines a Weil divisor by taking the valuation of a local equation at each codimension-one point. This gives a homomorphism

$$
\operatorname{CaDiv}(X)\longrightarrow\operatorname{Div}(X).
$$

It is injective if $X$ is locally noetherian, normal, and integral. The key fact is the intersection description

$$
\mathcal O_X(U)=\bigcap_{\xi\in U^{(1)}}\mathcal O_{X,\xi}
\quad\text{inside }k(X)
$$

for every open $U$: a rational function with no codimension-one zero or pole is a unit after applying the statement to it and its inverse. Normality is doing real work here; codimension-two defects would otherwise be invisible to valuations.

Surjectivity is equivalent to local principality of height-one primes. A prime divisor is Cartier
exactly when its height-one prime ideal becomes principal in every local ring. The general
statement that this holds in every regular noetherian local ring is a genuine theorem, and it is
not available here; it is proved later in this collection, and citing it now would be circular.
What we need is only the case of dimension at most two, and that case has a short direct proof
which we give in full.

**Proposition 3.1 (height-one primes in low-dimensional regular local rings).** Let $R$ be a
regular noetherian local ring with $\dim R\leq2$ and let $\mathfrak p\subset R$ be a prime of
height one. Then $\mathfrak p$ is principal.

**Proof.** A regular local ring is a domain, and in dimension zero it is a field, which has no
height-one prime. If $\dim R=1$ then $R$ is a regular local domain of dimension one, hence a
discrete valuation ring, and $\mathfrak p=\mathfrak m$ is generated by a uniformizer. So assume
$\dim R=2$, with maximal ideal $\mathfrak m$ and residue field $\ell$.

_Step 1: every finite $R$-module has projective dimension at most two._ Choose a regular system
of parameters $x_1,x_2$, so that $\mathfrak m=(x_1,x_2)$ and $\dim_\ell\mathfrak m/\mathfrak m^2=2$.
The sequence $x_1,x_2$ is regular: $R$ is a domain so $x_1$ is a non-zero-divisor, and $R/x_1R$ is
a regular local ring of dimension one, hence a discrete valuation ring and in particular a domain,
so the image of $x_2$ is a non-zero-divisor there. Consequently the Koszul complex
$K_\bullet(x_1,x_2)$, the tensor product of the two-term complexes
$R\xrightarrow{x_i}R$, is a free resolution of $\ell$ of length two: exactness follows by tensoring
the two-term complexes successively, using at each stage that the next element is a
non-zero-divisor on the quotient. Now let $M$ be a finite $R$-module and choose a minimal free
resolution $F_\bullet\to M$, obtained by lifting at each stage a basis of
$K/\mathfrak mK$ for the current kernel $K$; minimality means that every differential of
$F_\bullet$ has entries in $\mathfrak m$, so $F_\bullet\otimes_R\ell$ has zero differentials and
$\operatorname{Tor}^R_j(M,\ell)=F_j\otimes_R\ell$. Computing the same Tor modules with the Koszul
resolution of $\ell$ gives $\operatorname{Tor}^R_j(M,\ell)=0$ for $j>2$. Nakayama therefore forces
$F_j=0$ for $j>2$, which is the assertion.

_Step 2: $\operatorname{Ext}^2_R(R/\mathfrak p,R)=0$._ Choose $t\in\mathfrak m$ with
$t\notin\mathfrak p$; this is possible because $\mathfrak p$ has height one and $\mathfrak m$ has
height two, so $\mathfrak p\neq\mathfrak m$. Multiplication by $t$ is injective on the domain
$R/\mathfrak p$, giving

$$
0\longrightarrow R/\mathfrak p\xrightarrow{\ t\ }R/\mathfrak p
\longrightarrow R/(\mathfrak p+tR)\longrightarrow0 .
$$

The long exact sequence of $\operatorname{Ext}_R(-,R)$ contains

$$
\operatorname{Ext}^2_R(R/\mathfrak p,R)\xrightarrow{\ t\ }
\operatorname{Ext}^2_R(R/\mathfrak p,R)\longrightarrow
\operatorname{Ext}^3_R\bigl(R/(\mathfrak p+tR),R\bigr)=0,
$$

the last group vanishing by Step 1. So multiplication by the element $t\in\mathfrak m$ is
surjective on the finite $R$-module $\operatorname{Ext}^2_R(R/\mathfrak p,R)$, and Nakayama makes
that module zero.

_Step 3: $\mathfrak p$ is free._ The sequence
$0\to\mathfrak p\to R\to R/\mathfrak p\to0$ gives

$$
\operatorname{Ext}^1_R(R,R)=0\longrightarrow\operatorname{Ext}^1_R(\mathfrak p,R)
\longrightarrow\operatorname{Ext}^2_R(R/\mathfrak p,R)=0,
$$

so $\operatorname{Ext}^1_R(\mathfrak p,R)=0$. Take a minimal free resolution of $\mathfrak p$; by
Step 1 applied to $R/\mathfrak p$ it has the form
$0\to F_2\xrightarrow{\,A\,}F_1\to\mathfrak p\to0$ with the entries of $A$ in $\mathfrak m$.
Applying $\operatorname{Hom}_R(-,R)$ gives the exact sequence

$$
F_1^\vee\xrightarrow{\ A^{\mathsf T}\ }F_2^\vee
\longrightarrow\operatorname{Ext}^1_R(\mathfrak p,R)=0 ,
$$

so $A^{\mathsf T}$ is surjective. Its entries lie in $\mathfrak m$, so
$A^{\mathsf T}\otimes_R\ell=0$ and Nakayama gives $F_2^\vee=0$, hence $F_2=0$. Thus
$\mathfrak p\simeq F_1$ is free. Finally $\mathfrak p\otimes_R\operatorname{Frac}(R)$ is a nonzero
ideal of the fraction field, hence one-dimensional, so $F_1$ has rank one and $\mathfrak p$ is
principal. $\square$

Consequently, on a regular noetherian integral scheme all of whose local rings have dimension at
most two, every Weil divisor is Cartier: the inverse map is constructed by choosing a local
generator for each height-one prime and multiplying the corresponding powers. This covers every
situation in this book. Curves are the case $\dim\leq1$, and the total space of a relative curve
over a Dedekind base is at most two-dimensional. Nothing below uses the Cartier--Weil dictionary
on a regular scheme of dimension three or more.

### 3.3 Normal curves and regular models

For a noetherian integral curve, normality and regularity are equivalent. Indeed every non-generic local ring has dimension one; a one-dimensional noetherian normal local domain is a discrete valuation ring and hence regular. Therefore on a normal integral curve

$$
\operatorname{CaDiv}(X)\simeq\operatorname{Div}(X).
$$

This is the cleanest divisor dictionary in the book. It applies to smooth curves over any field, because smoothness implies regularity. By Proposition 3.1 it also applies to the regular total space of a relative curve over a Dedekind base, a two-dimensional situation: there too regularity makes every codimension-one cycle Cartier.

There is a particularly useful picture over a Dedekind scheme. Let $S$ be integral, regular, noetherian, and one-dimensional, and let $X\to S$ be an integral normal proper flat relative curve. Every prime divisor on the surface $X$ is of one of two kinds. A **horizontal** prime dominates $S$; it is the closure of a closed point of the generic fiber. It is proper and quasi-finite over $S$, hence finite, and its integral coordinate algebra is torsion-free over the Dedekind base, hence flat. Its finite-flat rank is its degree over the generic fiber. A **vertical** prime is an irreducible component of a closed fiber. Normality supplies an order valuation at either kind of prime, so rational functions have horizontal and vertical orders simultaneously.

If $X$ is regular, every such prime is Cartier. If $X$ is only normal, its Weil divisor is still defined but need not be locally principal at closed points of the surface. Horizontal degree can be read by intersecting with a fiber, while vertical components require a component pairing and self-intersection theory not yet available. This separation prevents two common mistakes: treating an entire fiber component as a divisor on that same fiber, and assuming that normality of a surface makes every horizontal closure Cartier.

There is an important distinction between regular and smooth over an imperfect field. A regular curve can fail to be smooth after a purely inseparable field extension. Its divisor theory is still controlled by discrete valuation rings, but statements involving geometric fibers or ordinary differentials require the stronger smoothness hypothesis.

### 3.4 Where the dictionaries fail

On the nodal affine curve $xy=0$, each component is a codimension-zero component, while the node is codimension one but its local ring is not a domain. Weil divisors in the normal-integral sense are unavailable, although Cartier divisors and dualizing differentials remain meaningful.

On the integral cusp $y^2=x^3$, the singular point defines a Weil divisor but its maximal ideal $(x,y)$ is not principal in the local ring. Thus the point is not an effective Cartier divisor. After normalization $x=t^2$, $y=t^3$, the inverse image is the Cartier point $t=0$, but descending it loses information. This explains why symmetric powers classify relative effective Cartier divisors on smooth curves, not on arbitrary singular curves.

In dimension at least two, normality alone also does not suffice. A normal surface may possess a nontrivial divisor class group, so a height-one prime can be Weil without being Cartier. Later intersection theory must therefore state regularity or a suitable Cartier hypothesis rather than silently converting cycles into equations.

## 4. Line bundles, rational sections, and Picard groups

### 4.1 The bundle attached to a divisor

Let $D$ have local equations $f_i$. The ratios $f_i/f_j$ are units and hence transition functions. Define the invertible subsheaf of $\mathcal K_X$

$$
\mathcal O_X(D)(U)=
\{g\in\mathcal K_X(U): gf_i\in\mathcal O_X(U\cap U_i)\text{ for every }i\}.
$$

Locally it is generated by $f_i^{-1}$. Its dual is $\mathcal O_X(-D)$, and multiplication gives

$$
\mathcal O_X(D+E)\simeq
\mathcal O_X(D)\otimes\mathcal O_X(E).
$$

If $D$ is effective, $\mathcal O_X(-D)$ is its ideal and the constant rational function $1$ is a regular section of $\mathcal O_X(D)$ vanishing exactly along $D$. This apparent reversal of signs is worth remembering: allowing a pole along $D$ produces $\mathcal O(D)$, while functions forced to vanish along $D$ form $\mathcal O(-D)$.

On a regular integral curve the description becomes

$$
\mathcal O_X(D)(U)=
\{g\in k(X):\operatorname{ord}_x(g)+n_x\geq0
\text{ for all }x\in U\}.
$$

Thus $H^0(X,\mathcal O_X(D))$ is the space of rational functions whose poles are bounded by $D$.

### 4.2 Rational sections recover divisors

Let $X$ be integral and $\mathcal L$ a line bundle. A nonzero **rational section** is a generator of the one-dimensional $k(X)$-space $\mathcal L_\eta$ at the generic point. Trivialize $\mathcal L$ on $U_i$ by $e_i$ and write $s=f_i e_i$. The ratios of the $f_i$ differ by the inverse transition functions, hence define a Cartier divisor $\operatorname{div}(s)$.

There is a canonical isomorphism

$$
\mathcal O_X(\operatorname{div}(s))\simeq\mathcal L
$$

carrying the canonical rational section to $s$. On a reduced scheme with several components, the same construction works for a rational section that is a basis at every generic point. A line bundle need not possess such a section on a scheme with infinitely many components, but on a noetherian scheme one chooses local generators at finitely many generic points and clears denominators.

A regular section $s\in H^0(X,\mathcal L)$ defines an effective Cartier divisor precisely when multiplication

$$
\mathcal L^{-1}\xrightarrow{s}\mathcal O_X
$$

is injective, equivalently when $s$ is regular at every associated point. On an integral scheme every nonzero section has this property. On a reducible curve, a section vanishing identically on one component does not.

### 4.3 Principal divisors and linear equivalence

Two Cartier divisors are **linearly equivalent**, written $D\sim E$, if

$$
D-E=\operatorname{div}(f)
$$

for a global rational unit $f$. Multiplication by $f$ gives $\mathcal O_X(D)\simeq\mathcal O_X(E)$. Conversely, an isomorphism between these line bundles compares their canonical rational sections and produces such an $f$. Hence linear equivalence is exactly the equivalence relation that forgets a chosen rational trivialization while retaining the line bundle.

For a proper integral curve over a field, every global regular unit is constant if the curve is geometrically connected and reduced. Principal divisors therefore remember nonconstant rational functions, not arbitrary global regular functions. Their total degree will be zero; geometrically, zeros and poles balance on a complete curve.

### 4.4 The divisor--Picard correspondence

The Picard group $\operatorname{Pic}(X)$ is the group of isomorphism classes of line bundles under tensor product. The preceding construction gives

$$
\operatorname{CaDiv}(X)/\operatorname{Prin}(X)
\longrightarrow\operatorname{Pic}(X). \tag{4.1}
$$

If every line bundle has a rational section that generates it at all associated points, (4.1) is an isomorphism. This holds for integral noetherian schemes and, more generally, for many noetherian schemes without embedded associated points. For a regular integral curve it yields the familiar identity

$$
\operatorname{Pic}(X)\simeq
\operatorname{Div}(X)/\{\operatorname{div}(f):f\in k(X)^\times\}.
$$

On a relative curve the distinction between absolute and relative Picard information matters. Tensoring by $f^*\mathcal M$ for a line bundle $\mathcal M$ on $S$ changes the line bundle on $X$ but not its class after restricting to any fiber. The relative Picard functor will eventually quotient by these pullbacks. For now, divisor constructions are made on every base change $X_T$ and are compatible with further base change; this functorial viewpoint is enough to prepare that theory without assuming its representability.

## 5. Degree and intersection with fibers

### 5.1 Degree over a field

Let $X$ be a proper regular integral curve over $k$. For

$$
D=\sum_x n_x[x],
$$

define

$$
\deg_k D=\sum_x n_x[\kappa(x):k]. \tag{5.1}
$$

The residue-field factor makes degree invariant under extending scalars and then summing geometric points with multiplicity. A $k$-rational point has degree one; a closed point cut out by an irreducible polynomial of degree $r$ on $\mathbf P^1_k$ has degree $r$.

Principal divisors have degree zero. A constant function is immediate. A nonconstant $f$ gives a
finite morphism $X\to\mathbf P^1_k$: properness makes the quasi-finite rational-function map
finite. Its direct image is torsion-free over every local discrete valuation ring of
$\mathbf P^1$, hence is flat. The zero and pole divisors are the fibers over $0$ and $\infty$,
and finite flat fibers have the same length. If $f$ is inseparable, length still records
inseparable multiplicity, so no separability assumption is needed. Consequently degree descends
to $\operatorname{Pic}(X)$.

For a possibly singular proper curve, define the degree of a line bundle by

$$
\deg\mathcal L=\chi(X,\mathcal L)-\chi(X,\mathcal O_X). \tag{5.2}
$$

On a regular integral curve this agrees with (5.1). Formula (5.2) is especially robust on reducible and nodal curves, where a line bundle has a multidegree on components but also a well-defined total degree.

### 5.2 Euler characteristic and degree

The equality between (5.1) and (5.2) begins with one effective point. For an effective Cartier divisor $D$ on a proper curve, tensoring (2.1) by $\mathcal O_X(D)$ gives

$$
0\longrightarrow\mathcal O_X
\longrightarrow\mathcal O_X(D)
\longrightarrow\mathcal O_D(D)
\longrightarrow0. \tag{5.3}
$$

Since $D$ is zero-dimensional it is a finite, hence affine, noetherian scheme, so Serre's affine
vanishing theorem (Book 7b, Theorem 3.9) gives $H^1(D,\mathcal F)=0$ for every quasi-coherent
$\mathcal F$; alternatively this is Grothendieck vanishing in dimension zero (Book 7b,
Corollary 5.9). Because the sheaf $\mathcal O_D(D)$ is pushed forward from $D$ along a finite,
hence affine, morphism, Corollary 3.11 of Book 7b identifies its cohomology on $X$ with its
cohomology on $D$. Its Euler characteristic is therefore the $k$-dimension
of its global sections. On a regular integral curve the local equation has order $n_x$ and the
quotient has length $n_x$, so

$$
\chi(\mathcal O_X(D))-\chi(\mathcal O_X)=\deg D.
$$

On an arbitrary proper curve the same equation reads
$\deg D=\sum_x\operatorname{length}_{\mathcal O_{X,x}}(\mathcal O_{D,x})
[\kappa(x):k]$ and is the Cartier-divisor degree; no Weil multiplicity at a singular point is
being assumed.

Differences of effective point divisors give the general case on a regular integral curve, because
the positive and negative valuation parts of a divisor are effective Cartier divisors. Thus (5.1)
and (5.2) agree and additivity follows in that setting. For a singular curve, (5.2) is at this
stage a numerical definition only; clearing a rational Cartier divisor by a positive divisor
requires projectivity and is not imported from a later chapter here.

### 5.3 Degree in a proper flat family

Let $f:X\to S$ be a projective flat relative curve and $\mathcal L$ a line bundle. Define

$$
\deg_s\mathcal L=
\chi(X_s,\mathcal L_s)-\chi(X_s,\mathcal O_{X_s}).
$$

Book 8 showed that the Hilbert polynomial of a flat projective family is locally constant. Apply
that result to $\mathcal L\otimes\mathcal A^n$ and $\mathcal A^n$, where $\mathcal A$ is
relatively ample. Its Euler-characteristic polynomial lemma says that tensoring by $\mathcal L$
changes the polynomial on a curve by a constant: the first difference is supported in dimension
zero. Evaluating that constant at $n=0$ identifies it with
$\chi(\mathcal L_s)-\chi(\mathcal O_{X_s})=\deg_s\mathcal L$. Both Hilbert polynomials are
locally constant in $s$, so $s\mapsto\deg_s\mathcal L$ is locally constant on $S$.

The conclusion uses flatness of $X$ and invertibility of $\mathcal L$, hence flatness of $\mathcal L$ over $S$. In a nonflat family the arithmetic genus can jump. For a coherent sheaf that is not flat over the base, torsion supported on a special fiber can change the Euler characteristic. Constancy is a theorem with hypotheses, not a property of notation.

The theorem in this subsection is deliberately stated only in the projective range. Proper
families are treated later, after the proper-cohomology theorem and the construction of a
relative polarization have been proved; no later projectivity result is imported here.

If fibers are reducible, total degree is locally constant but degree on an individual component need not even be globally labelable because components can permute. After a base change that labels components, one obtains a multidegree, and specialization can redistribute it. Later component-group theory measures precisely this extra information.

### 5.4 Horizontal divisors and fibers

Suppose $D\subset X$ is a relative effective Cartier divisor, meaning that $D$ is Cartier on $X$ and $D\to S$ is finite flat of rank $d$. Then every fiber $D_s$ is a length-$d$ effective Cartier divisor on $X_s$, and

$$
\deg_s\mathcal O_X(D)=d. \tag{5.4}
$$

Indeed (5.3) remains exact after base change, and $\dim_{\kappa(s)}H^0(D_s,\mathcal O_{D_s}(D_s))=d$ because twisting by a line bundle does not change the length of a zero-dimensional scheme.

When the total space is a regular surface over a one-dimensional regular base, (5.4) is written as an intersection number

$$
(D\cdot X_s)=d.
$$

This notation should not conceal the elementary content: it is the length of the scheme-theoretic intersection with the fiber. More generally, if a Cartier divisor $D$ meets $X_s$ properly, then

$$
(D\cdot X_s)=
\sum_{x\in D\cap X_s}
\operatorname{length}_{\mathcal O_{X,x}}
\frac{\mathcal O_{X,x}}{(f_D,f_s)}[\kappa(x):\kappa(s)],
$$

provided $f_D,f_s$ form the expected regular sequence. A vertical divisor containing $X_s$ does not meet it properly, and this length formula is not defined. Self-intersections and component pairings require the surface intersection theory developed later.

## 6. Effective relative divisors and symmetric powers

### 6.1 The correct relative notion

A collection of $d$ points in each fiber should form a family even when the points collide. Ordered sections are too rigid, and a reduced union discards multiplicity. The right object is a closed subscheme

$$
D\hookrightarrow X_T
$$

that is an effective Cartier divisor on $X_T$ and finite flat of rank $d$ over $T$. We call this a **relative effective divisor of degree $d$**. Both clauses matter. Cartier says that $D$ is cut out by one regular equation in the curve; finite flat of rank $d$ says that no point disappears or turns into a vertical component under specialization.

The construction is stable under every base change $T'\to T$. Flatness of $D/T$ preserves the Cartier property on fibers, while finite locally free modules remain finite locally free after tensor product. Its associated line bundle $\mathcal O_{X_T}(D)$ has fiberwise degree $d$ and a canonical section whose zero scheme is $D$.

If $T$ is connected, finite flat rank cannot jump. By contrast, the closed subscheme of $\mathbf A^1_T$ cut out by $tx=0$ over $T=\operatorname{Spec}k[t]$ is not flat: away from $t=0$ it is one point, while at $t=0$ it is the entire affine line. This is exactly the degeneration excluded by the definition.

### 6.2 Smooth curves turn points into divisors

Let $f:X\to S$ be smooth of relative dimension one. Every closed subscheme $Z\subset X_T$ finite flat of rank $d$ over $T$ is an effective Cartier divisor. This is the key curve-specific result behind the identification of the length-$d$ Hilbert space with the symmetric power.

The assertion is local on $X_T$ and $T$. Take a point $z\in Z$ above $t\in T$. Because $X_T/T$ is smooth of relative dimension one, it is locally modeled by a smooth algebra with one relative parameter. The ideal of a finite flat quotient has fiberwise codimension one. On the fiber, the local ring is regular of dimension one and the ideal is generated by a non-zero-divisor. Lifting a generator and applying Nakayama shows that the ideal is locally principal; flatness of both ambient ring and quotient over the base makes the generator regular. Thus $Z$ is Cartier.

Smoothness cannot simply be replaced by nodality. At a node with local ring $k[[x,y]]/(xy)$, the reduced point has ideal $(x,y)$, which needs two generators and is not Cartier. It is a length-one subscheme but not a divisor. The Hilbert space of points on a singular curve is therefore larger than its Cartier-divisor locus.

### 6.3 Universal divisors and addition

Book 8 constructed the symmetric power

$$
X^{(d)}=\operatorname{Sym}^d_S(X)
$$

for a smooth projective relative curve and identified it with the space of length-$d$ finite flat subschemes. By the preceding theorem it therefore represents relative effective Cartier divisors of degree $d$. There is a universal divisor

$$
\Delta_d\subset X\times_S X^{(d)}
$$

finite flat of rank $d$ over $X^{(d)}$. A map $T\to X^{(d)}$ is equivalent to pulling back $\Delta_d$ to a degree-$d$ divisor on $X_T$.

Addition of divisors produces a morphism

$$
X^{(d)}\times_S X^{(e)}
\longrightarrow X^{(d+e)}.
$$

Scheme-theoretically, it multiplies the two invertible ideals. If two sections meet in a special fiber, their sum specializes to a nonreduced divisor of length two rather than losing a point. On geometric points the map is the familiar concatenation

$$
(p_1+\cdots+p_d,\ q_1+\cdots+q_e)
\longmapsto p_1+\cdots+p_d+q_1+\cdots+q_e.
$$

For a section $p:S\to X$, repeated addition gives the diagonal divisor $dp$. Locally, if $p$ has equation $t$, then $dp$ has equation $t^d$ and structure sheaf $\mathcal O_X/(t^d)$. Multiplicity is thus a genuine infinitesimal thickening.

### 6.4 Nodal fibers and the boundary

For a nodal relative curve, the functor of relative effective Cartier divisors is still open inside the length-$d$ Hilbert space. Being locally principal by a regular element is an open condition in a flat finite presentation. But the open subset need not be proper: a Cartier point approaching a node may have a non-Cartier limit.

The failure appears after a ramified base change of the standard smoothing. Let $R$ be a discrete
valuation ring with uniformizer $\pi$ and consider

$$
C=\operatorname{Spec}R[x,y]/(xy-\pi^2).
$$

Its generic fiber is smooth and its special fiber is nodal. The generic-fiber point $(x,y)=(\pi,\pi)$
extends to a section through the node, with ideal $(x-\pi,y-\pi)$. At the local ring of the node
the two displayed generators have independent images in $\mathfrak m/\mathfrak m^2$; the relation
$xy-\pi^2$ has no linear term. Since $\mathfrak mI\subseteq\mathfrak m^2$, they remain independent
in $I/\mathfrak mI$. Nakayama therefore says that $I$ needs two generators. Hence this
height-one ideal is not principal, and the section is
not Cartier on the total space. The Hilbert compactification remembers the limit, while the
Cartier-divisor space omits it. This boundary distinction is essential when constructing
compactified Jacobians; it is not present for smooth families.

On the smooth locus $X^{\mathrm{sm}}\subset X$, symmetric powers still give Cartier divisors supported away from nodes. Many later arguments deliberately choose cusps or marked points in this locus so that their divisor and Abel constructions remain ordinary even when the fiber is nodal.

## 7. Differentials on curves

### 7.1 Kähler differentials and local parameters

Divisors measure multiplicative change. Differentials measure first-order additive change. For a morphism $X\to S$, the sheaf $\Omega^1_{X/S}$ is generated locally by symbols $da$ subject to

$$
d(a+b)=da+db,\qquad d(ab)=a\,db+b\,da,\qquad d(c)=0
$$

for functions $c$ pulled back from $S$. It represents derivations: maps $\Omega^1_{X/S}\to\mathcal M$ correspond naturally to $S$-derivations $\mathcal O_X\to\mathcal M$.

If $f:X\to S$ is smooth of relative dimension one, $\Omega^1_{X/S}$ is a line bundle. At a geometric point one may choose an étale local parameter $t$, and $dt$ is a basis. Under a new parameter $u$, one has

$$
du=\frac{du}{dt}\,dt
$$

with $du/dt$ a unit. Thus the line spanned by differentials is intrinsic even though a parameter is not.

The conormal sequence explains equations. If $X$ is cut out in a smooth $S$-scheme $P$ by an ideal $\mathcal I$, then

$$
\mathcal I/\mathcal I^2
\longrightarrow \Omega^1_{P/S}|_X
\longrightarrow \Omega^1_{X/S}
\longrightarrow0. \tag{7.1}
$$

When $X$ is a relative hypersurface $F=0$, the first map sends the class of $F$ to $dF$. Smoothness means that the partial derivatives do not vanish simultaneously on a fiber.

### 7.2 Canonical divisors on smooth curves

Let $X$ be a smooth proper geometrically connected curve over $k$. The line bundle

$$
\omega_X=\Omega^1_{X/k}
$$

is the **canonical bundle**. A nonzero rational differential $\eta$ is a rational section and defines its canonical divisor

$$
K_X=\operatorname{div}(\eta).
$$

Changing $\eta$ to $f\eta$ adds $\operatorname{div}(f)$, so the canonical divisor class is
independent of the differential. Riemann--Roch and duality will give

$$
\deg\omega_X=2g-2.
$$

Examples calibrate the sign. On $\mathbf P^1$ with affine coordinate $t$, the differential $dt$ has no finite zero or pole. At infinity put $u=t^{-1}$; then $dt=-u^{-2}du$, so

$$
\operatorname{div}(dt)=-2[\infty].
$$

Thus $\omega_{\mathbf P^1}\simeq\mathcal O_{\mathbf P^1}(-2)$. On a smooth plane curve of degree $n$, the conormal sequence together with the determinant of the cotangent bundle of $\mathbf P^2$ yields

$$
\omega_X\simeq\mathcal O_X(n-3).
$$

For a smooth cubic this is trivial, foreshadowing genus one.

### 7.3 Differentials at singular points

Ordinary differentials cease to be the right canonical sheaf at singularities. At the node

$$
A=k[[x,y]]/(xy),
$$

the conormal sequence gives

$$
\Omega^1_{A/k}=
(A\,dx\oplus A\,dy)/(y\,dx+x\,dy).
$$

This module is not locally free. It has torsion: the nonzero element $x\,dy=-y\,dx$ is killed by
the regular element $x+y$, since $x^2dy=-xy\,dx=0$. A family can therefore have an invertible
differential bundle on smooth fibers but a noninvertible $\Omega^1$ on the nodal fiber.

At the cusp $k[[t^2,t^3]]$, the image of ordinary differentials inside $k[[t]]dt$ is generated by $2t\,dt$ and $3t^2dt$. In characteristic not two, it misses $dt$; in small characteristic its behavior changes further. The singularity is visible in the failure of ordinary differentials to capture all regular differentials on the normalization.

Duality calls for a different object: the Rosenlicht sheaf, which allows controlled poles on the
normalization whose residues cancel across branches. It is invertible at a node even though
$\Omega^1$ is not; the later duality construction will identify the two without being used here.

## 8. Residues

### 8.1 What a residue must be, and why the obvious definition fails

Let $X$ be a smooth integral curve over $k$ and let $x$ be a closed point. We want a canonical
$k$-linear functional

$$
\operatorname{Res}_x:\Omega^1_{k(X)/k}\longrightarrow k
$$

which vanishes on the regular differentials $\Omega^1_{X,x}$, which kills exact differentials, whose
associated pairing against the finite algebras $\mathcal O_{nx}$ is perfect, and whose values sum to
zero over a proper curve. Over an algebraically closed field all of this is familiar: the completed
local ring is a power series ring $\kappa[[t]]$, a differential is $\bigl(\sum a_nt^n\bigr)dt$, and
the residue is $a_{-1}$. The whole difficulty of this section is that over a general field none of
that description survives.

The obstruction is not the failure of $\kappa(x)$ to equal $k$; it is the possible inseparability of
$\kappa(x)/k$. One example exhibits all three symptoms at once. Let $p$ be a prime, let
$k=\mathbf F_p(a)$, let $X=\mathbf A^1_k=\operatorname{Spec}k[z]$, and let $x$ be the closed point
cut out by the irreducible polynomial $P=z^p-a$, so that

$$
\kappa(x)=k[z]/(z^p-a)=k\bigl(a^{1/p}\bigr)
$$

is purely inseparable of degree $p$ over $k$, and $t:=P(z)$ is a uniformizer at $x$.

_The field trace is useless._ For a purely inseparable extension of degree $p>1$ the trace form is
identically zero, so $\operatorname{Tr}_{\kappa(x)/k}=0$ and no formula of the shape
$\operatorname{Tr}_{\kappa(x)/k}(a_{-1})$ can define a nonzero functional.

_The residue field does not sit inside the completion._ Suppose $K\subseteq\widehat{\mathcal
O}_{X,x}$ were a subfield containing $k$ and mapping isomorphically onto $\kappa(x)$. Then $K$ would
contain an element $w$ with $w^p=a$. Since $z^p=a+t$ we would get
$(w-z)^p=w^p-z^p=-t$, so the uniformizer $t$ would have a $p$-th root in the completed local ring.
That is impossible, because the normalized valuation of a $p$-th power is divisible by $p$ while
$v_x(t)=1$. So there is no coefficient field containing $k$, and the expansion of an element of
$\widehat{\mathcal O}_{X,x}$ as a power series with coefficients in $\kappa(x)$ is not available over
$k$. Book 1, Theorem 13.15, does supply a coefficient field for any complete local ring containing a
field; the computation just made shows that in equal characteristic $p$ it cannot always be chosen
to contain a prescribed base field, and this is exactly the phenomenon that makes the naive
definition of the residue unavailable.

_A uniformizer is not a coordinate._ In this example $dt=d(z^p-a)=pz^{p-1}dz=0$, while
$\Omega^1_{X/k}=k[z]\,dz$ is free of rank one on $dz$. So $\eta=h\,dt$ is not even a legitimate way
to write a differential: the differential of a uniformizer may vanish identically.

What survives is the invertibility of $\Omega^1_{X/k}$ itself. Because $X/k$ is smooth of relative
dimension one, $\Omega^1_{X/k}$ is a line bundle and $\Omega^1_{k(X)/k}$ is a one-dimensional
$k(X)$-vector space. Call $z\in k(X)$ a **separating element** if $dz\neq0$ in $\Omega^1_{k(X)/k}$,
and call it an **étale coordinate at $x$** if moreover $z\in\mathcal O_{X,x}$ and $dz$ generates the
stalk $\Omega^1_{X,x}$. Two remarks are needed.

First, a separating element deserves its name: if $dz\neq0$ then $\Omega^1_{k(X)/k}=k(X)\,dz$ by
dimension count, hence $\Omega^1_{k(X)/k(z)}=0$, so $k(X)/k(z)$ is separably algebraic; and $z$ is
transcendental over $k$, since otherwise $k(X)$ would be algebraic over $k$, contradicting the fact
that a one-dimensional $\Omega^1$ forces transcendence degree one.

Second, étale coordinates exist at every closed point: $\Omega^1_{X,x}$ is generated by the
differentials $da$ with $a\in\mathcal O_{X,x}$, so by Nakayama one of them generates. For such a $z$
the induced morphism $\pi_z:U\to\mathbf A^1_k$ on a neighbourhood $U$ of $x$ is unramified, because
$\Omega^1_{U/\mathbf A^1}=\Omega^1_{U/k}/\mathcal O_U\,dz=0$ after shrinking; and it is flat, because
$\mathcal O_{X,x}$ is a one-dimensional regular local domain, hence torsion free over the discrete
valuation ring $\mathcal O_{\mathbf A^1,y}$ below it, where $y=\pi_z(x)$. So $\pi_z$ is étale at $x$.

The construction now proceeds in three steps. Section 8.2 defines residues on the affine line by an
elementary partial-fraction recipe, which is manifestly $k$-linear and compatible with extension of
the base field. Section 8.3 transports them to $X$ along an étale coordinate, using the local traces
of a finite separable extension of complete discretely valued fields, and proves that the result is
independent of every choice by descending the question to an algebraic closure, where all the
classical formulas are available. Section 8.4 records the resulting principal-part duality.

### 8.2 Residues on the affine line

Write $\mathbf A^1_k=\operatorname{Spec}k[z]$ and $\mathbf P^1_k=\mathbf A^1_k\cup\{\infty\}$. Closed
points $y$ of $\mathbf A^1_k$ correspond to monic irreducible polynomials $P_y\in k[z]$, and
$\mathcal O_{\mathbf A^1,y}=k[z]_{(P_y)}$ is a discrete valuation ring with uniformizer $P_y$ and
residue field $\kappa(y)=k[z]/(P_y)$.

Every nonzero polynomial has invertible leading term in the field $k((z^{-1}))$ of Laurent series in
$z^{-1}$, so there is a canonical embedding $k(z)\subseteq k((z^{-1}))$, the **expansion at
infinity**. Let

$$
\lambda_\infty:k((z^{-1}))\longrightarrow k
$$

be the $k$-linear map extracting the coefficient of $z^{-1}$.

**Lemma 8.1 (partial fractions).** Every $h\in k(z)$ has a unique expression

$$
h=h_0+\sum_{y}h_y,
\qquad h_0\in k[z],
\qquad h_y=\frac{g_y}{P_y^{\,n_y}},\quad \deg g_y<n_y\deg P_y,
$$

with only finitely many $h_y$ nonzero. Moreover $h_y=0$ if and only if $h\in\mathcal O_{\mathbf
A^1,y}$, and $h_y$ depends only on the class of $h$ in $k(z)/\mathcal O_{\mathbf A^1,y}$.

**Proof.** Write $h=g/f$ with $f=\prod_yP_y^{n_y}$ its factorization into monic irreducibles. The
ideals $(P_y^{n_y})$ are pairwise comaximal, so repeated use of Bézout gives
$1/f=\sum_yu_y/P_y^{\,n_y}$ with $u_y\in k[z]$, whence $h=\sum_ygu_y/P_y^{\,n_y}$; Euclidean division
of each numerator by $P_y^{\,n_y}$ moves a polynomial into $h_0$ and leaves a numerator of degree
less than $n_y\deg P_y$. For uniqueness, a difference of two such expressions is a rational function
with no poles, hence a polynomial, whose non-polynomial parts $\sum_y(h_y-h'_y)$ lie in
$z^{-1}k[[z^{-1}]]$ and therefore vanish; comparing poles at each $y$ separates the terms. If
$h\in\mathcal O_{\mathbf A^1,y}$ then subtracting the terms at the other points shows that $h_y$ is
regular at $y$ and lies in $z^{-1}k[[z^{-1}]]$ with denominator a power of $P_y$, so $h_y=0$. The
last clause follows, since $h\mapsto h_y$ is $k$-linear by uniqueness and kills $\mathcal O_{\mathbf
A^1,y}$. $\square$

**Definition.** For $h\in k(z)$ and a closed point $y$ of $\mathbf A^1_k$ set

$$
\operatorname{res}_y(h\,dz):=\lambda_\infty(h_y),
\qquad
\operatorname{res}_\infty(h\,dz):=-\lambda_\infty(h).
$$

Since $h_y$ lies in $z^{-1}k[[z^{-1}]]$ the first expression is the coefficient of $z^{-1}$ in the
expansion of $h_y$ at infinity.

**Proposition 8.2 (basic properties on the line).** Fix a closed point $y$ of $\mathbf A^1_k$.

1. $\operatorname{res}_y(-\,dz)$ is $k$-linear and vanishes on $\mathcal O_{\mathbf A^1,y}\,dz$;
   it factors through $k(z)/\mathcal O_{\mathbf A^1,y}$.
2. It extends uniquely to a $k$-linear functional on $\widehat K_y\,dz$ vanishing on
   $\widehat{\mathcal O}_y\,dz$, where $\widehat{\mathcal O}_y$ is the completion and $\widehat K_y$
   its fraction field.
3. For every $h\in k(z)$ one has
   $\sum_{y\in\mathbf A^1}\operatorname{res}_y(h\,dz)+\operatorname{res}_\infty(h\,dz)=0$.
4. If $\kappa(y)=k$, say $P_y=z-b$, then $\operatorname{res}_y(h\,dz)$ is the coefficient of
   $(z-b)^{-1}$ in the Laurent expansion of $h$ at $b$.
5. For every field extension $k'/k$ and every $h\in k(z)$,
   $\operatorname{res}_y(h\,dz)=\sum_{y'\mapsto y}\operatorname{res}_{y'}(h\,dz)$ inside $k'$, the
   sum being over the closed points of $\mathbf A^1_{k'}$ lying over $y$.

**Proof.** (1) is Lemma 8.1. For (2), the transition maps identify
$\mathcal O_{\mathbf A^1,y}/P_y^{\,n}=\widehat{\mathcal O}_y/P_y^{\,n}$, so
$k(z)/\mathcal O_{\mathbf A^1,y}=\varinjlim_n P_y^{-n}\mathcal O_{\mathbf A^1,y}/\mathcal
O_{\mathbf A^1,y}=\widehat K_y/\widehat{\mathcal O}_y$, and a functional on the left is the same
thing as one on the right. (3) is immediate from Lemma 8.1: $\lambda_\infty$ is $k$-linear and kills
polynomials, so $\lambda_\infty(h)=\sum_y\lambda_\infty(h_y)$. For (4), the expansion of
$(z-b)^{-m}$ at infinity is $z^{-m}(1-b/z)^{-m}$, whose $z^{-1}$ coefficient is $1$ for $m=1$ and
$0$ for $m\geq2$; since $h_y$ is a $k$-linear combination of the $(z-b)^{-m}$ with $m\geq1$, and
those are exactly the terms of the Laurent expansion with negative index, the two prescriptions
agree. For (5), the identity $h=h_0+\sum_yh_y$ persists in $k'(z)$. The summand $h_y$ has poles only
at the points of $\mathbf A^1_{k'}$ above $y$ and lies in $z^{-1}k'[[z^{-1}]]$, so its own
partial-fraction expression over $k'$ has zero polynomial part and components exactly at those
points; and $h-h_y$ is regular at each of them, so those components are the components of $h$.
Applying $\lambda_\infty$, which is compatible with the inclusion $k((z^{-1}))\subseteq
k'((z^{-1}))$, gives $\operatorname{res}_y(h\,dz)=\lambda_\infty(h_y)=\sum_{y'\mapsto
y}\operatorname{res}_{y'}(h\,dz)$. $\square$

Part (3) is the residue theorem on $\mathbf P^1_k$, proved without any duality or trace. Part (4)
says that over a field where the point is rational the definition is the classical one, and part (5)
is the mechanism by which every later statement will be reduced to that classical case.

### 8.3 The local residue on a smooth curve

Let $X$ be a smooth integral curve over $k$, let $x$ be a closed point, and let $z$ be an étale
coordinate at $x$ in the sense of Section 8.1. Write $y$ for the closed point of $\mathbf A^1_k$
below $x$, that is, the centre on $\mathbf A^1_k$ of the discrete valuation $v_x$. Completing,
Book 1, Section 12, gives an inclusion $\widehat{\mathcal O}_y\subseteq\widehat{\mathcal O}_{X,x}$
of complete discrete valuation rings, and the completed product theorem of Book 1, Section 12.2,
identifies

$$
k(X)\otimes_{k(z)}\widehat K_y\;\simeq\;\prod_{x'\mapsto y}\widehat K_{x'},
\qquad
\operatorname{Tr}_{k(X)/k(z)}=\sum_{x'\mapsto y}\operatorname{Tr}_{\widehat K_{x'}/\widehat K_y},
\tag{8.1a}
$$

the product being over the closed points of $X$ above $y$. All the field extensions occurring here
are separable, since $k(X)/k(z)$ is, so all these traces are the traces of separable field
extensions and are nonzero.

**Definition.** For $\eta\in\Omega^1_{k(X)/k}$ write $\eta=h\,dz$ with $h\in k(X)$ and set

$$
\operatorname{Res}^{\,z}_x(\eta)
:=\operatorname{res}_y\!\bigl(\operatorname{Tr}_{\widehat K_x/\widehat K_y}(h)\,dz\bigr), \tag{8.1b}
$$

using the extension of $\operatorname{res}_y$ to $\widehat K_y$ furnished by Proposition 8.2(2).

Because $z$ is an étale coordinate at $x$, the stalk $\Omega^1_{X,x}$ equals $\mathcal
O_{X,x}\,dz$, so $\eta$ is regular at $x$ exactly when $h\in\mathcal O_{X,x}$. In that case
$\operatorname{Tr}(h)\in\widehat{\mathcal O}_y$, because the trace of a finite extension of discrete
valuation rings carries integers to integers (Book 1, Section 11.8), and therefore
$\operatorname{Res}^{\,z}_x(\eta)=0$. Thus (8.1b) already kills regular differentials, and it
factors through $\Omega^1_{k(X)/k}/\Omega^1_{X,x}$.

Two reductions make everything else routine. The first isolates one point of a fibre.

**Lemma 8.3 (separating the points of a fibre).** Let $S$ be the set of closed points of $X$ above
$y$ and let $\eta\in\Omega^1_{k(X)/k}$. There is $\tilde\eta\in\Omega^1_{k(X)/k}$ with
$\tilde\eta-\eta$ regular at $x$ and $\tilde\eta$ regular at every point of $S\setminus\{x\}$.

**Proof.** The semilocal ring $\mathcal O_{X,S}$ is a principal ideal domain, being a semilocal
Dedekind domain, so its invertible modules are free; choose a generator $\omega$ of
$\Omega^1_{X,S}$ and write $\eta=f\omega$ with $f\in k(X)$. Approximation in a semilocal Dedekind
domain provides $\tilde f\in k(X)$ congruent to $f$ modulo $\mathcal O_{X,x}$ and regular at the
other points of $S$: take $\tilde f$ to be the part of a partial-fraction decomposition of $f$ in
$\mathcal O_{X,S}$ supported at $x$, which exists because the localizations at the finitely many
maximal ideals are comaximal. Put $\tilde\eta=\tilde f\omega$. $\square$

The second reduction is base change. Let $k'/k$ be a field extension. Since $X/k$ is smooth,
$X_{k'}$ is a smooth $k'$-curve, hence regular, hence a disjoint union of integral curves; and
$k(X)\otimes_kk'$ is the product of their function fields, because $k(X)/k$ is separably generated
and so $k(X)\otimes_kk'$ is reduced. An étale coordinate $z$ at $x$ remains an étale coordinate at
every point $x'$ of $X_{k'}$ above $x$, because $\Omega^1_{X_{k'}/k'}=\Omega^1_{X/k}\otimes_kk'$.

**Proposition 8.4 (base change).** With this notation, for every $\eta\in\Omega^1_{k(X)/k}$,

$$
\operatorname{Res}^{\,z}_x(\eta)=\sum_{x'\mapsto x}\operatorname{Res}^{\,z}_{x'}(\eta)
\qquad\text{in }k' . \tag{8.1c}
$$

**Proof.** Replace $\eta$ by the $\tilde\eta$ of Lemma 8.3; this changes neither side, since
$\tilde\eta-\eta$ is regular at $x$ and hence at every $x'$ above $x$, and since both sides kill
differentials regular at the relevant points. Write $\tilde\eta=\tilde h\,dz$. Summing (8.1b) over
the fibre and using (8.1a) both over $k$ and over $k'$,

$$
\sum_{x''\mapsto y}\operatorname{Res}^{\,z}_{x''}(\tilde\eta)
=\operatorname{res}_y\!\bigl(\operatorname{Tr}_{k(X)/k(z)}(\tilde h)\,dz\bigr),
$$

and likewise over $k'$ for each point $y'$ of $\mathbf A^1_{k'}$ above $y$, with
$\operatorname{Tr}_{k(X)/k(z)}(\tilde h)$ unchanged because the trace of a finite separable
extension commutes with extension of the base field. Proposition 8.2(5) now gives

$$
\sum_{y'\mapsto y}\ \sum_{x'\mapsto y'}\operatorname{Res}^{\,z}_{x'}(\tilde\eta)
=\operatorname{res}_y\!\bigl(\operatorname{Tr}_{k(X)/k(z)}(\tilde h)\,dz\bigr)
=\sum_{x''\mapsto y}\operatorname{Res}^{\,z}_{x''}(\tilde\eta).
$$

On the left the points $x'$ occurring are exactly the points of $X_{k'}$ above the points $x''$ of
$S$; on both sides every term with $x''\neq x$ vanishes, because $\tilde\eta$ is regular there and
hence at every point above. What remains is (8.1c). $\square$

**Theorem 8.5 (the residue is canonical).** The functional (8.1b) does not depend on the choice of
the étale coordinate $z$ at $x$. Writing $\operatorname{Res}_x$ for the common value, the map

$$
\operatorname{Res}_x:\Omega^1_{k(X)/k}\longrightarrow k \tag{8.2}
$$

is $k$-linear, vanishes on $\Omega^1_{X,x}$, and vanishes on exact differentials $df$ with
$f\in k(X)$.

**Proof.** Apply Proposition 8.4 with $k'=\overline k$ an algebraic closure. Since $k\to\overline k$
is injective, it suffices to prove that for each closed point $\bar x$ of $X_{\overline k}$ above
$x$ the functional $\operatorname{Res}^{\,z}_{\bar x}$ is independent of $z$ and kills exact
differentials.

So assume $k=\overline k$ and $\kappa(x)=k$. Let $z$ be an étale coordinate at $x$ and $y$ its image
in $\mathbf A^1_k$; then $\kappa(y)=k$ as well. The extension $\widehat{\mathcal
O}_y\subseteq\widehat{\mathcal O}_{X,x}$ is unramified, because $\pi_z$ is étale at $x$, and its
residue extension is $k=k$; so its ramification index and residue degree are both one and the
inclusion is an isomorphism. Hence $\operatorname{Tr}_{\widehat K_x/\widehat K_y}$ is the identity
and, by Proposition 8.2(4), $\operatorname{Res}^{\,z}_x(h\,dz)$ is the coefficient of $u^{-1}$ in
the expansion of $h$ in the parameter $u=z-z(x)$, which is a uniformizer at $x$. By Book 1,
Corollary 13.17, $\widehat{\mathcal O}_{X,x}=k[[u]]$, and the assertion becomes the classical
statement that the coefficient of $u^{-1}\,du$ in a Laurent series is unchanged by a change of
parameter. That statement is the computation already familiar from the affine line: if $u'$ is
another uniformizer, then $u'=uv$ with $v$ a unit and $du'/u'=du/u+dv/v$ with $dv/v$ regular, while
termwise differentiation gives

$$
d\Bigl(\sum a_nu^n\Bigr)=\sum na_nu^{n-1}du ,
$$

whose $u^{-1}du$ coefficient is zero because it could only arise from $n=0$. This is valid in every
characteristic, and it simultaneously proves that exact differentials have zero residue: every
change of parameter is a unit multiplication followed by a formal substitution, and the chain rule
transports the coefficient extraction. $\square$

The reduction in the proof is worth restating, because every later local assertion about residues
uses it. A $k$-linear identity among residues at a point of a smooth $k$-curve may be verified after
extending scalars to an algebraic closure, where residues are the classical Laurent coefficients.

**Corollary 8.6 (separable residue fields).** Suppose $\kappa(x)/k$ is separable. Then
$\widehat{\mathcal O}_{X,x}$ has a coefficient field containing $k$: writing $\kappa(x)=k(\theta)$
by the primitive element theorem, Book 1, Lemma 13.6, applied to the subfield $k$ and the separable
residue element $\theta$ produces one. Choose such a field and a uniformizer $t$; then by Book 1,
Corollary 13.17, $\widehat{\mathcal O}_{X,x}=\kappa(x)[[t]]$ and every
differential is $\eta=\bigl(\sum_{n\gg-\infty}a_nt^n\bigr)dt$ with $a_n\in\kappa(x)$. In this case

$$
\operatorname{Res}_x(\eta)=\operatorname{Tr}_{\kappa(x)/k}(a_{-1}). \tag{8.3}
$$

**Proof.** Both sides are $k$-linear in $\eta$ and vanish for $\eta$ regular, so it suffices to
treat $\eta=at^{-m}dt$ with $a\in\kappa(x)$ and $m\geq1$. Extend scalars to $\overline k$. Since
$\kappa(x)/k$ is separable, $\kappa(x)\otimes_k\overline k=\prod_{\sigma}\overline k$ over the
$[\kappa(x):k]$ distinct $k$-embeddings $\sigma:\kappa(x)\to\overline k$, and correspondingly $x$
splits into that many points $\bar x_\sigma$, each with $t$ a uniformizer and with $a$ specializing
to $\sigma(a)$. By Proposition 8.4 and the classical description of residues at rational points,
$\operatorname{Res}_x(\eta)=\sum_\sigma\sigma(a)\,[m=1]$, and $\sum_\sigma\sigma(a)$ is
$\operatorname{Tr}_{\kappa(x)/k}(a)$ for a separable extension. $\square$

When $\kappa(x)/k$ is inseparable this formula degenerates and (8.1b), not the field trace, is the
definition; the example of Section 8.1 shows that no substitute involving
$\operatorname{Tr}_{\kappa(x)/k}$ can exist.

### 8.4 The principal-part pairing

The residue is not merely a functional: it trivializes the dualizing module of every finite Cartier
subscheme concentrated at $x$. This is the statement that the rest of the book consumes.

**Theorem 8.7 (principal-part duality).** Let $X$ be a smooth integral curve over $k$, let $x$ be a
closed point and $n\geq1$. Then

$$
\Omega^1_{X/k}(nx)/\Omega^1_{X/k}
\;\xrightarrow{\ \sim\ }\;
\operatorname{Hom}_k(\mathcal O_{nx},k),
\qquad
\eta\longmapsto\bigl(f\mapsto\operatorname{Res}_x(f\eta)\bigr), \tag{8.1}
$$

is an isomorphism of $\mathcal O_{nx}$-modules. In particular the pairing
$(\eta,f)\mapsto\operatorname{Res}_x(f\eta)$ is a perfect pairing of finite-dimensional
$k$-vector spaces, and $\operatorname{Hom}_k(\mathcal O_{nx},k)$ is free of rank one over
$\mathcal O_{nx}$ with the class of any $\eta$ having a pole of exact order $n$ as generator. These
isomorphisms are compatible as $n$ grows, since restriction along $\mathcal
O_{(n+1)x}\twoheadrightarrow\mathcal O_{nx}$ matches the inclusion of principal-part spaces.

**Proof.** The map is well defined: $f\eta$ has poles of order at most $n$ at $x$ and none
elsewhere, and $\operatorname{Res}_x$ kills regular differentials, so the value depends only on the
class of $\eta$. It is $\mathcal O_{nx}$-linear by construction. Both sides have the same
$k$-dimension $n[\kappa(x):k]$: the left side is $\Omega^1_{X/k}\otimes\mathcal O_{nx}$, an
invertible $\mathcal O_{nx}$-module, and the right side is the $k$-dual of $\mathcal O_{nx}$. So it
suffices to prove injectivity, and for that we may extend scalars to $\overline k$: the exact
sequence $0\to\Omega^1_{X/k}\to\Omega^1_{X/k}(nx)\to\Omega^1_{X/k}\otimes\mathcal O_{nx}\to0$ and
the algebra $\mathcal O_{nx}$ both base-change, and by Proposition 8.4 the pairing base-changes to
the corresponding pairing on $X_{\overline k}$ against the divisor $n\,x_{\overline k}$, where
$x_{\overline k}=\sum_{\bar x\mapsto x}e_{\bar x}\bar x$ is the pullback of $x$. That pairing is the
orthogonal direct sum over the points $\bar x$ of the pairings

$$
\bigl(u^{-i}du\bigr)_{1\le i\le ne_{\bar x}}\times\bigl(u^{\,j}\bigr)_{0\le j<ne_{\bar x}}
\longrightarrow\overline k,
\qquad
(u^{-i}du,\,u^{\,j})\longmapsto[\,i=j+1\,],
$$

in a uniformizer $u$ at $\bar x$, by Theorem 8.5. Its matrix is antidiagonal with entries $1$, hence
invertible. So the base-changed pairing is perfect, and therefore so was the original. $\square$

Passing to the limit over $n$, Theorem 8.7 says that $\operatorname{Res}_x$ identifies the space of
principal parts $\Omega^1_{k(X)/k}/\Omega^1_{X,x}$ with the continuous $k$-dual of
$\widehat{\mathcal O}_{X,x}$. This is the local half of Serre duality, and it has been obtained
without any global input.

### 8.5 The global residue theorem

**Theorem 8.8 (residue theorem).** If $X$ is a smooth proper geometrically connected curve over $k$
and $\eta$ is a rational differential, then

$$
\sum_{x\in X^{(1)}}\operatorname{Res}_x(\eta)=0. \tag{8.4}
$$

Only finitely many terms are nonzero. Properness is essential: $dt/t$ on $\mathbf G_m$ has residues
visible at the omitted points $0$ and $\infty$, and discarding either boundary destroys the
cancellation.

For $X=\mathbf P^1_k$ this was proved in Proposition 8.2(3) by partial fractions, with no duality
and no trace, and with no assumption on the residue fields. That elementary case is what fixes the
normalization of the whole theory.

For a general $X$ the statement is the global counterpart of Theorem 8.7, and we deduce it from the
absolute duality theorem of Section 9.2 together with the local computation just performed. This
is legitimate and not circular: Section 9 is developed from the projective-space Čech pairing of
Book 7b and the Ext calculus of Book 7a, and at no point uses Section 8. The reader who prefers a
strictly linear reading may take Sections 8.1--8.4 first, then Section 9, and return here.

**Proof of Theorem 8.8.** Let $\underline{\Omega}$ denote the constant sheaf on $X$ with value
$\Omega^1_{k(X)/k}$. Since $X$ is integral, every nonempty open is dense and irreducible, so
$\underline{\Omega}(U)=\Omega^1_{k(X)/k}$ for every nonempty open $U$ and all restriction maps are
the identity; thus $\underline{\Omega}$ is flasque and hence acyclic by Proposition 3.2(1) of
Book 7b. There is an exact sequence of sheaves

$$
0\longrightarrow\Omega^1_{X/k}\longrightarrow\underline{\Omega}
\longrightarrow\bigoplus_{x\in X^{(1)}}i_{x*}\bigl(\Omega^1_{k(X)/k}/\Omega^1_{X,x}\bigr)
\longrightarrow0,
$$

whose exactness is checked on stalks: at a closed point $x$ the sequence is
$\Omega^1_{X,x}\to\Omega^1_{k(X)/k}\to\Omega^1_{k(X)/k}/\Omega^1_{X,x}$, while at the generic point
the third term has zero stalk, a section of the direct sum being supported at finitely many closed
points and hence dying on a smaller open. The last sheaf is flasque as well: each summand is the
direct image of a sheaf on a point, hence flasque by Lemma 3.1(4) of Book 7b; finite direct sums of
flasque sheaves are flasque by the same lemma; and on the noetherian space $X$ a filtered colimit of
flasque sheaves is flasque by Proposition 5.6(3) of Book 7b. Both outer-flanking sheaves being
acyclic, taking cohomology therefore identifies

$$
H^1(X,\Omega^1_{X/k})
=\operatorname{coker}\Bigl(\Omega^1_{k(X)/k}\longrightarrow
\bigoplus_{x}\Omega^1_{k(X)/k}/\Omega^1_{X,x}\Bigr), \tag{8.4a}
$$

so that a class in $H^1$ is a finite collection of principal parts modulo global ones.

By Section 9.4 the dualizing sheaf of the smooth curve $X$ is $\omega_X=\Omega^1_{X/k}$, and
Theorem 9.1 supplies the trace $\operatorname{tr}:H^1(X,\omega_X)\to k$. Composing
$\operatorname{tr}$ with (8.4a) and with the inclusion of the summand at $x$ gives $k$-linear
functionals

$$
R_x:\Omega^1_{k(X)/k}/\Omega^1_{X,x}\longrightarrow k,
\qquad\text{with}\qquad
\sum_xR_x(\eta)=0\ \text{ for every }\eta\in\Omega^1_{k(X)/k}
$$

by exactness of (8.4a). So it suffices to prove that $R_x$ is a nonzero constant multiple of
$\operatorname{Res}_x$, by one and the same constant $c\in k^\times$ for all $x$ and all smooth
proper curves: the displayed vanishing then gives $c\sum_x\operatorname{Res}_x(\eta)=0$ and hence
(8.4).

Both are $k$-linear functionals killing $\Omega^1_{X,x}$, and both are compatible with the
$\mathcal O_X$-module structure in the sense that $\eta\mapsto R_x(f\eta)$ and
$\eta\mapsto\operatorname{Res}_x(f\eta)$ describe the induced maps to
$\operatorname{Hom}_k(\mathcal O_{nx},k)$. For $R_x$ this is exactly the zero-dimensional case (9.7)
of Theorem 9.1: applied to the skyscraper $\mathcal T=\mathcal O_{nx}$ it gives
$\operatorname{Ext}^1_X(\mathcal O_{nx},\omega_X)\simeq H^0(X,\mathcal O_{nx})^\vee$, and the
connecting map of $0\to\mathcal O_X(-nx)\to\mathcal O_X\to\mathcal O_{nx}\to0$ tensored with
$\omega_X$ identifies $\operatorname{Ext}^1_X(\mathcal O_{nx},\omega_X)$ with the principal-part
space $\Omega^1_{X/k}(nx)/\Omega^1_{X/k}$; under these identifications $R_x$ is evaluation at $1$.
Hence $R_x$ also induces an isomorphism
$\Omega^1_{X/k}(nx)/\Omega^1_{X/k}\to\operatorname{Hom}_k(\mathcal O_{nx},k)$ of
$\mathcal O_{nx}$-modules, as does $\operatorname{Res}_x$ by Theorem 8.7. Two such isomorphisms
differ by an $\mathcal O_{nx}$-module automorphism of an invertible module, that is, by
multiplication by a unit $c_n\in\mathcal O_{nx}^\times$; and the compatibility of both families with
the surjections $\mathcal O_{(n+1)x}\to\mathcal O_{nx}$ makes the $c_n$ compatible, so they define a
single unit $c\in\widehat{\mathcal O}_{X,x}^\times$ with
$R_x(\eta)=\operatorname{Res}_x(c\,\eta)$.

It remains to see that $c$ is a scalar in $k^\times$ and is the same at every point; this is where
the elementary case does the work. Take $X=\mathbf P^1_k$ first, with coordinate $z$, and let
$x_0=\infty$, at which the local parameter is $u=1/z$ and $\widehat{\mathcal
O}_{x_0}=k[[u]]$. Write $c_0=\sum_{j\geq0}\gamma_ju^j\in k[[u]]^\times$ for the unit with
$R_{x_0}=\operatorname{Res}_{x_0}(c_0\,\cdot\,)$. For every integer $m\geq0$ the differential
$\eta_m=z^m\,dz$ is regular on $\mathbf A^1_k$, so its only pole is at $x_0$; the vanishing of both
total sums therefore gives $R_{x_0}(\eta_m)=0$ and $\operatorname{Res}_{x_0}(\eta_m)=0$. In the
parameter $u$ one has $\eta_m=-u^{-m-2}du$, and
$\operatorname{Res}_{x_0}(c_0u^{-n}du)=\gamma_{n-1}$ for $n\geq1$ by Proposition 8.2(4). Hence
$0=R_{x_0}(\eta_m)=-\gamma_{m+1}$ for every $m\geq0$, so $\gamma_j=0$ for $j\geq1$ and
$c_0=\gamma_0=:c$ lies in $k^\times$.

Now let $x\in\mathbf A^1_k$ be any closed point and $\xi$ a class in $\Omega^1(nx)/\Omega^1$. By
Lemma 8.1 the partial-fraction component $h_x$ realizes $\xi$ by a rational differential
$\eta=h_x\,dz$ regular on $\mathbf A^1\setminus\{x\}$, so its only other pole is at $x_0=\infty$.
Then $R_x(\xi)+R_{x_0}(\eta)=0$ and $\operatorname{Res}_x(\xi)+\operatorname{Res}_{x_0}(\eta)=0$, and
$R_{x_0}=c\operatorname{Res}_{x_0}$ gives $R_x(\xi)=c\operatorname{Res}_x(\xi)$. So
$R=c\operatorname{Res}$ throughout $\mathbf P^1_k$, with one scalar constant.

Now take a general $X$ and a separating element $z\in k(X)$, with resulting finite separable
morphism $\pi=\pi_z:X\to\mathbf P^1_k$. By Section 9.4 both dualizing sheaves are the sheaves of
differentials, and by (9.8) the finite morphism $\pi$ carries a trace of sheaves
$\operatorname{Tr}_\pi:\pi_*\Omega^1_{X/k}\to\Omega^1_{\mathbf P^1/k}$, compatible with the global
traces in the sense that
$\operatorname{tr}_{\mathbf P^1}\circ H^1(\operatorname{Tr}_\pi)=\operatorname{tr}_X$; here we use
that $\pi$ is finite, hence affine, so $H^1(\mathbf P^1,\pi_*\mathcal F)=H^1(X,\mathcal F)$ by
Corollary 3.11 of Book 7b. Because $\operatorname{Tr}_\pi$ is a morphism of sheaves it induces, for
each closed point $x$ with image $w$, a map of principal-part spaces
$T_x:\Omega^1_{k(X)/k}/\Omega^1_{X,x}\to\Omega^1_{k(z)/k}/\Omega^1_{\mathbf P^1,w}$, and the
flasque resolution of (8.4a) is functorial, so the class maps satisfy
$q_{\mathbf P^1}\circ\bigoplus_xT_x=H^1(\operatorname{Tr}_\pi)\circ q_X$. Composing with the traces
gives an equality of $k$-linear maps on the direct sum
$\bigoplus_x\Omega^1_{k(X)/k}/\Omega^1_{X,x}$, and evaluating on a family concentrated at a single
$x$ isolates one summand:

$$
R_x=R^{\mathbf P^1}_{w}\circ T_x=c\cdot\operatorname{res}_{w}\circ T_x . \tag{8.4b}
$$

Let $T:\Omega^1_{k(X)/k}\to\Omega^1_{k(z)/k}$ be the map induced by $\operatorname{Tr}_\pi$ on
generic stalks. It is $k(z)$-linear and nonzero, and
$\operatorname{Hom}_{k(z)}(k(X),k(z))$ is one-dimensional over $k(X)$ because $k(X)/k(z)$ is
separable; so $T=\operatorname{Tr}_{k(X)/k(z)}(\theta\,\cdot\,)$ for a unique $\theta\in k(X)^\times$.
Completing at $x$ and using (8.1a), the map $T_x$ is induced by
$\operatorname{Tr}_{\widehat K_x/\widehat K_w}(\theta\,\cdot\,)$. Hence, if $z$ happens to be an
étale coordinate at $x$, comparison of (8.4b) with the definition (8.1b) and Theorem 8.5 gives

$$
R_x(\eta)=c\,\operatorname{Res}_x(\theta\eta)\qquad\text{for all }\eta . \tag{8.4c}
$$

Finally, every closed point of $X$ admits an étale coordinate, the locus where a given $z$ is an
étale coordinate is open, and $X$ is quasi-compact; so finitely many separating elements
$z_1,\ldots,z_r$ have étale loci covering $X$. Each $z_i$ produces a $\theta_i\in k(X)^\times$
satisfying (8.4c) on its étale locus. If $x$ lies in the étale loci of both $z_i$ and $z_j$, then
$\operatorname{Res}_x(\theta_i\eta)=\operatorname{Res}_x(\theta_j\eta)$ for all $\eta$, so
$\theta_i=\theta_j$ in $\widehat{\mathcal O}_{X,x}$ by Theorem 8.7 and hence in $k(X)$. As the
étale loci are dense open sets in an irreducible space, any two of them meet, and all the
$\theta_i$ coincide with a single $\theta\in k(X)^\times$ for which (8.4c) holds at **every** closed
point. In particular $\theta$ is a unit at every closed point, because $R_x$ and
$\operatorname{Res}_x$ are both generators of the same invertible module by Theorem 8.7 and the
paragraph above; so $\operatorname{div}(\theta)=0$ and $\theta$ is a global regular unit, hence
$\theta\in k^\times$ since $X$ is proper, geometrically connected, and reduced.

Therefore $R_x=(c\theta)\operatorname{Res}_x$ for every $x$, with one nonzero constant $c\theta$,
and $\sum_xR_x=0$ yields (8.4). $\square$

The constant $c\theta$ is a normalization of the trace of Theorem 9.1, not a feature of residues:
the pair $(\omega_X,\operatorname{tr})$ is determined only up to rescaling $\operatorname{tr}$ by a
unit of $k$, and the proof shows that exactly one rescaling makes the trace agree with the sum of
residues. From now on we fix that normalization, so that for a smooth proper curve

$$
\operatorname{tr}\Bigl(\text{class of }(\xi_x)_x\text{ in }H^1(X,\Omega^1_{X/k})\Bigr)
=\sum_x\operatorname{Res}_x(\xi_x). \tag{8.4d}
$$

Normalizing the traces of $\mathbf P^1_k$ and of $X$ in this way makes $c=1$ and $c\theta=1$, hence
$\theta=1$; so (8.4c) also shows that the generic-stalk map $T$ of $\operatorname{Tr}_\pi$ is exactly
the field trace $\operatorname{Tr}_{k(X)/k(z)}$, and that $\operatorname{Tr}_\pi$ carries regular
differentials on $X$ to regular differentials on $\mathbf P^1_k$.

The conceptual consequence is more important than the chosen proof. A collection of local polar parts can be the polar part of a global rational differential only if its total residue is zero; duality will show that this is the only obstruction when the allowed poles are sufficiently specified.

### 8.6 Finite maps and trace

Let $\pi:Y\to X$ be a finite separable morphism of smooth proper integral curves over $k$. Since
$\Omega^1_{k(Y)/k}=k(Y)\otimes_{k(X)}\Omega^1_{k(X)/k}$ for a separable extension, the field trace
induces an intrinsic trace on rational differentials,

$$
\operatorname{Tr}_{k(Y)/k(X)}:
\Omega^1_{k(Y)/k}\longrightarrow\Omega^1_{k(X)/k},
\qquad h\,dz\longmapsto\operatorname{Tr}_{k(Y)/k(X)}(h)\,dz,
$$

independent of the chosen separating element $z\in k(X)$.

**Theorem 8.9 (local trace formula).** For every closed point $x\in X$ and every
$\eta\in\Omega^1_{k(Y)/k}$,

$$
\operatorname{Res}_x\bigl(\operatorname{Tr}_{k(Y)/k(X)}\eta\bigr)
=\sum_{y\mapsto x}\operatorname{Res}_y(\eta). \tag{8.5}
$$

**Proof.** The argument is the one already used inside the proof of Theorem 8.8, now applied to
$\pi$ instead of to a map to the projective line.

By Section 9.4 both dualizing sheaves are the sheaves of differentials, and by (9.8) the finite
morphism $\pi$ carries a trace of sheaves
$\operatorname{Tr}_\pi:\pi_*\Omega^1_{Y/k}\to\Omega^1_{X/k}$,
compatible with the global traces in the sense that
$\operatorname{tr}_X\circ H^1(\operatorname{Tr}_\pi)=\operatorname{tr}_Y$; here we use that
$\pi$ is finite, hence affine, so $H^1(X,\pi_*\mathcal F)=H^1(Y,\mathcal F)$ by Corollary 3.11 of
Book 7b. Because $\operatorname{Tr}_\pi$ is a morphism of sheaves it induces, for each closed point
$x$, a map on principal parts

$$
T_x:\bigoplus_{y\mapsto x}\Omega^1_{k(Y)/k}\big/\Omega^1_{Y,y}
\longrightarrow\Omega^1_{k(X)/k}\big/\Omega^1_{X,x},
$$

and the flasque resolution used in (8.4a) is functorial, so the class maps satisfy
$q_X\circ\bigoplus_xT_x=H^1(\operatorname{Tr}_\pi)\circ q_Y$. Composing with the traces and using
the normalization (8.4d) on both curves gives an equality of $k$-linear maps defined on the whole
direct sum $\bigoplus_y\Omega^1_{k(Y)/k}/\Omega^1_{Y,y}$:

$$
\sum_x\operatorname{Res}_x\circ T_x=\sum_y\operatorname{Res}_y .
$$

Evaluating on a family concentrated at the points above a single $x$ isolates one summand and gives

$$
\operatorname{Res}_x(T\eta)=\sum_{y\mapsto x}\operatorname{Res}_y(\eta) \tag{8.5a}
$$

for every $x$ and every $\eta$, where $T$ denotes the map induced by $\operatorname{Tr}_\pi$ on
generic stalks.

It remains to identify $T$ with the field trace, and this is the last paragraph of the proof of
Theorem 8.8 read for $\pi$. Both maps are nonzero and $k(X)$-linear, and
$\operatorname{Hom}_{k(X)}(k(Y),k(X))$ is one-dimensional over $k(Y)$ by separability, so
$T=\operatorname{Tr}_{k(Y)/k(X)}(\theta\,\cdot\,)$ for a unique $\theta\in k(Y)^\times$. Choose a
separating element $z\in k(X)$ which is simultaneously an étale coordinate at a given
$y\in Y$ and at its image $x$; this is possible because $\Omega^1_{Y,y}$ and $\Omega^1_{X,x}$ are
free of rank one and $\pi$ is unramified at all but finitely many points, so a $z$ whose
differential generates $\Omega^1_{X,x}$ also has $dz$ generating $\Omega^1_{Y,y}$ whenever $\pi$ is
unramified at $y$. Transitivity of the local traces through $\widehat K_x$, together with the
definition (8.1b) applied on $Y$ and on $X$ with this common $z$, turns (8.5a) into
$\operatorname{Res}_x(\operatorname{Tr}_{k(Y)/k(X)}(\theta\eta))=
\operatorname{Res}_x(\operatorname{Tr}_{k(Y)/k(X)}(\eta))$ for all $\eta$, and Theorem 8.7 with the
nondegeneracy of the trace pairing forces $\theta$ to be a unit at $y$ equal to $1$ there. As the
unramified locus is dense, $\theta=1$. Substituting into (8.5a) gives (8.5). $\square$

Two special cases are worth recording. If the residue extensions are separable, Corollary 8.6
rewrites (8.5) as the familiar formula with residue-field traces of Laurent coefficients. And
combining (8.5) with the residue theorem on $X$ reproves the residue theorem on $Y$, so (8.5) is the
precise sense in which residues are functorial for finite separable maps.

For a purely inseparable map the ordinary field trace can be zero and does not define a map on
Kähler differentials at all; there the correct statement is the trace (9.8) on dualizing sheaves,
which is evaluation at $1$ in a Hom module and is available for every finite morphism. That
construction, and with it the extension of residue functoriality to singular curves, is carried out
in Section 9 and used in Section 12.4.

## 9. Dualizing sheaves

### 9.1 Why ordinary differentials are not enough

On a smooth curve, regular differentials serve two roles: they are first-order forms and they are dual to $H^1(\mathcal O_X)$. At a node the first role is played by $\Omega^1$, but that sheaf is not invertible and does not give the correct duality. The second role persists under degeneration and singles out the dualizing sheaf.

The guiding requirement is a trace functional

$$
\operatorname{tr}:H^1(X,\omega_X)\longrightarrow k
$$

such that multiplication followed by trace makes

$$
H^i(X,\mathcal F)\times
\operatorname{Ext}^{1-i}_X(\mathcal F,\omega_X)
\longrightarrow k
$$

a perfect pairing for coherent $\mathcal F$. For a vector bundle $\mathcal E$, the second factor becomes the cohomology of $\mathcal E^\vee\otimes\omega_X$. This property determines $\omega_X$ uniquely up to unique isomorphism compatible with trace.

A word on the logical order. The whole of this chapter is built from the projective-space Čech
computation of Book 7b, the Ext calculus and replacement theory of Book 7a, and the projective
results of Book 8. It uses nothing from Chapter 8: no residue, no principal-part pairing, and no
residue theorem enters any argument below. This is what allows Chapter 8 to borrow the global trace
constructed here in order to prove the residue theorem, without circularity. The comparison between
the trace of this chapter and the residues of Chapter 8 is carried out in Section 8.5 and refined in
Section 12.2.

### 9.2 Dualizing sheaves on proper curves

We first justify the projective embeddings used in the construction. This is not automatic from
the smooth-curve result of Book 8, because the curve here may be reducible, nonreduced, or
singular.

**Lemma 9.1A (proper curves are projective).** Every proper $k$-scheme of finite type and pure
dimension one which has no embedded associated points is projective over $k$.

**Proof.** Let $\nu:\widetilde X\to X_{\mathrm{red}}$ be the disjoint union of the normalizations
of the irreducible components. It is finite by Book 8, and the same book's compactification
argument makes each normal proper component projective without using duality or Riemann--Roch.
Choose a very ample bundle on every component. A sufficiently high power is generated with
prescribed values at the finite set over the conductor and the component intersections, so it has
a section nonvanishing there. Its zero divisor $E_i$ is nonempty and lies where $\nu$ is an
isomorphism. On a small affine neighborhood of every point of its image, lift its parameter from
$X_{\mathrm{red}}$ to $X$. Because $X$ has no embedded associated points and the reduction of
the parameter avoids every minimal prime, the lift is a non-zero-divisor. Remove any other zeros
and glue to the unit equation on the complement. The resulting effective Cartier divisor $D$ on
$X$ pulls back on each normalized component to $E_i$ and meets every component.

For completeness, ampleness descends here without invoking a general finite-descent theorem.
On the reduced curve, the kernel and cokernel of
$F\to\nu_*\nu^*F$ are supported on the finite conductor for every coherent $F$. Since
$\mathcal O(E_i)$ is ample upstairs, Serre vanishing and eventual generation hold for
$\nu^*F\otimes\mathcal O(nE_i)$. The conductor terms have no higher cohomology, and after one
more power the restriction maps onto them are surjective. The two kernel--cokernel sequences
therefore give vanishing and generation for $F\otimes\mathcal O(nD)$ downstairs. Serre's
criterion makes $\mathcal O(D)|_{X_{\mathrm{red}}}$ ample. Finally filter the nilradical of $X$
by its powers. Its successive quotients are coherent sheaves on $X_{\mathrm{red}}$, so the same
vanishing-and-generation argument lifts ampleness across the nilpotent thickening.

A sufficiently high power of an ample line bundle is very ample by the embedding theorem of Book
8, and properness turns the resulting immersion into a closed immersion. Thus $X$ is projective.
$\square$

**Theorem 9.1 (absolute curve duality).** A proper Cohen--Macaulay curve $X/k$ has a maximal
Cohen--Macaulay dualizing sheaf $\omega_X$ and a trace
$H^1(X,\omega_X)\to k$ for which (9.6) is functorial and perfect for every bounded coherent
complex. The trace-compatible pair is independent of every projective embedding. Finite maps
of such curves have the transitive trace (9.8).

**Proof.** We reduce the theorem to an explicit calculation on projective space. On the
regular ambient projective space a coherent sheaf has a finite vector-bundle resolution, so
there we apply $\mathcal Hom$ term by term and identify homotopy-equivalent resolutions. On
the possibly singular curve we do not make that assertion: the change-of-rings construction
below uses injective coinduction and the finite ambient resolution. Strict dg currying
supplies the comparison, and Ext concentration supplies the required bounded dual.

First consider $P=\mathbf P^N_k$. It is separated and covered by the $N+1$ standard affine charts
(Book 7b, Proposition 6.1), so by the Čech model theorem (Book 7b, Theorem 4.2) the alternating
Čech complex of that cover, which has length $N$, represents $R\Gamma(P,\mathcal F)$ for every
quasi-coherent $\mathcal F$. For a twist $\mathcal O_P(a)$ this is the homogeneous Čech complex,
whose terms are the graded pieces $(S_{X_I})_a$ of localized polynomial rings (Book 7b,
Lemma 6.2); its cohomology is computed in Book 7b, Theorem 6.5, and Corollary 6.6 records that
all the resulting modules are free with formation commuting with every ring map. Its top Čech term
consists of Laurent monomials of total degree
$a$ in which every $X_i$ may be inverted. Multiplication followed by extraction of the
coefficient of

$$
(X_0X_1\cdots X_N)^{-1}
$$

gives a pairing of complexes

$$
C^\bullet(\mathcal O_P(a))\otimes
C^{N-\bullet}(\mathcal O_P(-a-N-1))\longrightarrow k[-N]. \tag{9.1}
$$

Indeed the Čech complex splits as a direct sum indexed by exponent vectors. The summand for a
fixed exponent is the augmented simplex on the variables whose exponents allow inversion, so
it is contracted by inserting the least available variable unless it lies in degree $0$ or in
the unique top-degree range. Only finitely many exponent summands survive. A monomial $X^u$ in
a surviving summand pairs with the unique monomial $X^{-u-(1,\ldots,1)}$ on the other side;
the contracted summands pair with contracted summands. Thus (9.1) retracts to a perfect pairing
of finite-dimensional cohomology complexes and proves perfectness, not merely equality of
dimensions. Direct sums and total complexes extend (9.1) to every bounded complex
$E^\bullet$ of vector bundles:

$$
R\operatorname{Hom}_k(R\Gamma(P,E^\bullet),k)
\simeq
R\Gamma\!\left(P,
\mathcal Hom(E^\bullet,\omega_P[N])\right),
\qquad \omega_P=\mathcal O_P(-N-1). \tag{9.2}
$$

Here a vector bundle is resolved by sums of twists. This is Hilbert's syzygy theorem, proved in
Book 7b, Theorem 7.4: over the homogeneous coordinate ring $R=k[X_0,\ldots,X_N]$ every finite
graded module has a graded free resolution of length at most $N+1$ by finite sums of shifts, and
by Corollary 7.5 of the same book such a resolution stays exact under extension of the base field.
Sheafifying gives a finite resolution by sums of twists; irrelevant
torsion sheafifies to zero. The same argument resolves every coherent sheaf on $P$.

Let now $i:X\hookrightarrow P$ be a projective embedding supplied by Lemma 9.1A and
put $c=N-1$. Choose a finite locally free resolution $E^\bullet\to i_*\mathcal O_X$. At every
$x\in X$, the local codimension in $P$ is $c$ and Cohen--Macaulayness says
$\operatorname{depth}\mathcal O_{X,x}=\dim\mathcal O_{X,x}$. The elementary depth lemma
applied successively to a shortest free resolution gives

$$
\operatorname{pd}_{\mathcal O_{P,x}}\mathcal O_{X,x}
=N-1=c. \tag{9.3}
$$

For completeness, the Ext concentration used next follows by induction on
$\dim\mathcal O_{X,x}$. In dimension zero, devissage by a composition series reduces to the
residue field of a regular local ring, whose Koszul resolution has dual cohomology only in top
degree. In positive dimension choose a regular parameter which is also regular on the
Cohen--Macaulay module. (After adjoining an indeterminate the residue field is infinite, so
prime avoidance supplies it; faithful flatness descends the conclusion.) The two short exact
sequences given by multiplication by this element identify adjacent Ext groups with those for
the quotient. Induction shifts the unique nonzero degree by the codimension, which is unchanged.
Thus the dual complex $\mathcal Hom(E^\bullet,\omega_P)$ has cohomology only in degree $c$.
Define the coherent sheaf $\omega_X$ by

$$
i_*\omega_X=
\mathcal Ext^c_P(i_*\mathcal O_X,\omega_P). \tag{9.4}
$$

The same local computation shows that $\omega_X$ has depth one at every closed point, hence is
maximal Cohen--Macaulay.

For a coherent $\mathcal F$ on $X$, Ext concentration alone is not enough: one needs a
functorial change-of-rings map. We construct it by a genuine dg adjunction, avoiding the invalid
procedure of lifting differentials one at a time. Let $I^\bullet$ be a bounded-below injective
resolution of the ambient dualizing line; it exists by the bounded-below replacement theorem of
Book 7a, Section 3.4, applied in the Grothendieck abelian category of $\mathcal O_P$-modules.
Such a complex is $K$-injective by the bounded-below criterion of Book 7a, Section 3.2, and it is
moreover internally $K$-injective in the sense of Book 7a, Section 3.4, so that by Section 4.3 of
that book it computes the sheaf-valued $R\mathcal Hom$ in the second variable. Put

$$
i^bI^\bullet=
\mathcal Hom_P(i_*\mathcal O_X,I^\bullet),
$$

viewed as a complex of sheaves on $X$. For every acyclic complex $A^\bullet$ on $X$, the exactness
of $i_*$ and the ordinary coinduction adjunction give an equality of dg complexes

$$
\operatorname{Hom}_X(A^\bullet,i^bI^\bullet)
=\operatorname{Hom}_P(i_*A^\bullet,I^\bullet),
$$

and the right side is acyclic. Thus $i^bI^\bullet$ is $K$-injective on $X$. More generally, for
every complex $M^\bullet$ on $X$, currying is the strict equality of sheaf dg Hom complexes

$$
\mathcal Hom_P(i_*M^\bullet,I^\bullet)
=i_*\mathcal Hom_X(M^\bullet,i^bI^\bullet). \tag{9.5a}
$$

On an affine $R\twoheadrightarrow B$ this is the termwise identity
$\operatorname{Hom}_R(M,I)=
\operatorname{Hom}_B(M,\operatorname{Hom}_R(B,I))$; hence (9.5a) is global from its
construction, not an affine comparison glued by a uniqueness assertion in the derived category.
The two sides compute the corresponding derived sheaf Homs because $I^\bullet$ and
$i^bI^\bullet$ are $K$-injective. The finite ambient resolution $E^\bullet$ identifies
$i^bI^\bullet$ with $\omega_X[-c]$ by (9.4). This gives the functorial change-of-rings
quasi-isomorphism

$$
R\mathcal Hom_P(i_*\mathcal F,\omega_P[N])
\simeq
i_*R\mathcal Hom_X(\mathcal F,\omega_X[1]). \tag{9.5}
$$

Naturality is strict in the coinduction equality (9.5a) and hence survives passage to the derived
category. Combining (9.2) and (9.5) proves, functorially,

$$
R\operatorname{Hom}_k(R\Gamma(X,\mathcal F),k)
\simeq
R\operatorname{Hom}_X(\mathcal F,\omega_X[1]). \tag{9.6}
$$

For $\mathcal F=\mathcal O_X$, the coefficient functional in (9.1) induces the trace
$H^1(X,\omega_X)\to k$. For a zero-dimensional coherent sheaf $\mathcal T$, taking
cohomology gives

$$
\operatorname{Ext}^1_X(\mathcal T,\omega_X)
\simeq H^0(X,\mathcal T)^\vee. \tag{9.7}
$$

Taking cohomology for general $\mathcal F$ gives the perfect pairings of Section 9.1.

The construction is independent of the embedding. The pair $(\omega_X,\operatorname{tr})$
represents the functor

$$
\mathcal F\longmapsto
R\operatorname{Hom}_k(R\Gamma(X,\mathcal F),k)[-1].
$$

If a second embedding produces $(\omega'_X,\operatorname{tr}')$, applying the two representing
isomorphisms to the identity of either object gives mutually inverse maps
$\omega_X\leftrightarrows\omega'_X$. Naturality makes them trace-compatible, and the same
argument shows uniqueness. For three embeddings these unique maps satisfy the cocycle
condition automatically.

Finally let $\pi:Y\to X$ be finite between proper Cohen--Macaulay curves. Affine-locally, for
$A\to B$ finite and an $A$-module $W$, the adjunction

$$
\operatorname{Hom}_A(M,W)
\simeq
\operatorname{Hom}_B(M,\operatorname{Hom}_A(B,W))
$$

is evaluation/currying. Applying the $K$-injective dg version used in (9.5a)--so no finite
$A$-resolution of $B$ is assumed--and using uniqueness of the representing pair gives

$$
\pi_*\omega_Y\simeq
\mathcal Hom_X(\pi_*\mathcal O_Y,\omega_X), \tag{9.8}
$$

and the trace is evaluation at $1$. This recovers the local compatibility already proved for
smooth curves. In a tower $A\to B\to C$, currying identifies
$\operatorname{Hom}_B(C,\operatorname{Hom}_A(B,W))$ with
$\operatorname{Hom}_A(C,W)$ by $\phi\mapsto(c\mapsto\phi(c)(1_B))$. Evaluation first at
$1_C$ and then at $1_B$ is therefore direct evaluation at $1_C$. Thus these traces are
transitive.
$\square$

The Cohen--Macaulay hypothesis excludes embedded zero-dimensional components. Without it, duality is represented by more than one sheaf degree; a single $\omega_X$ cannot encode the whole theory. Pure reduced curves are Cohen--Macaulay because every local ring has dimension one and a function avoiding the finitely many minimal primes is a non-zero-divisor.

A curve is **Gorenstein** if its dualizing sheaf is invertible. Smooth curves, local complete-intersection curves, and nodal curves are Gorenstein. A reduced curve need not be Gorenstein; at a non-Gorenstein singularity $\omega_X$ is torsion-free of rank one but not a line bundle. Divisor formulas involving a canonical Cartier divisor then require modification.

### 9.3 The relative dualizing sheaf

We first remove a possible projectivity ambiguity.

**Lemma 9.2A (fpqc-local projectivity of a Cohen--Macaulay curve).** A proper flat finitely
presented morphism with pure one-dimensional Cohen--Macaulay fibers is projective after a
faithfully flat base change of finite presentation around any point of the base.

**Proof.** Work around a geometric point $\bar s$. On the fiber choose, on every irreducible
component, a closed point outside all other components and outside the finite set of associated
points. At each chosen point prime avoidance gives a parameter $h$: its image in the fiber
ring is a non-zero-divisor and its zero scheme is zero-dimensional near that point. After a
finite residue-field extension, the parameters and the chosen affine neighborhoods descend.

We record the spreading argument, since it is what prevents projectivity from being smuggled
into the proof. Shrink each affine neighborhood so that the fiberwise zero set of $h$ is the
chosen finite set and $h$ is a unit along its boundary. After shrinking the base, the same is
true in the total space. The equation $h$ then glues with the unit equation on the complement
to an effective Cartier divisor $D\subset X$: on the overlap the quotient is a unit. The
local flatness criterion applied to

$$
0\longrightarrow\mathcal O_X\xrightarrow{h}\mathcal O_X
\longrightarrow\mathcal O_D\longrightarrow0
$$

shows that $D$ is flat over the base, because $X$ is base-flat and $h$ remains a
non-zero-divisor on the fiber. It is quasi-finite after a further shrinking, and it is proper
as a closed subscheme of $X$; hence it is finite, and finite flat finite presentation makes it
finite locally free. Repeating points if necessary makes $D_{\bar s}$ have positive degree on
every reduced component.

The line $\mathcal O_X(D)$ is ample on the fiber. Indeed its pullback to the finite
normalization of the reduced fiber has positive degree on every component, so powers have
affine nonvanishing loci covering that normalization; finiteness descends affineness. A
nilpotent thickening of an affine scheme is affine by its finite filtration by quasi-coherent
ideals, so the same criterion applies to the possibly nonreduced fiber.

It remains to prove that this fiberwise ample line spreads; we do not assume openness of
ampleness. The input is the following proper-curve complex lemma.

> If $g:Z\to\operatorname{Spec}A$ is proper, flat, and finitely presented with fibers of
> dimension at most one over a noetherian ring, and $\mathcal F$ is finitely presented and
> $A$-flat, then locally on $\operatorname{Spec}A$ there is a bounded complex of finite
> projective $A$-modules which computes $R\Gamma(Z_B,\mathcal F_B)$ after every base change
> $A\to B$.

We include the proof without assuming $Z$ projective. Four ingredients are separated so that
neither formal functions nor nonflat base change is hidden in a kernel--cokernel induction. It is
worth recording at the outset that the first two ingredients are proved for an arbitrary proper
morphism $g:Z\to\operatorname{Spec}A$ with $A$ noetherian and an arbitrary coherent sheaf: neither
the flatness of $g$ nor the bound on the fiber dimension is used in (i) or (ii). Only (iii) and (iv)
consume those hypotheses. Section 9.5 uses (i) and (ii) in that greater generality.

**(i) Proper finiteness.** We first prove the precise relative Chow lemma needed here.

> Let $A$ be noetherian and let $T$ be separated and of finite type over $A$. There is a projective
> surjection $p:T'\to T$ and a dense open $U\subseteq T$ such that $p^{-1}(U)\to U$ is an
> isomorphism and $T'$ is quasi-projective over $A$. If $T$ is proper over $A$, then $T'$ is
> projective over $A$.

The construction begins with a finite affine cover having a common dense core. Write
$T_1,\ldots,T_r$ for the irreducible components and $\eta_1,\ldots,\eta_r$ for their generic
points. Every $x\in T$ has an affine neighborhood containing all the $\eta_j$. Indeed, start
with an affine neighborhood $W$ of $x$. If $W$ meets $T_j$, then it contains $\eta_j$. For each
remaining component choose an affine neighborhood of $\eta_j$ inside
$T\setminus\bigcup_{\ell\ne j}T_\ell$; these neighborhoods are pairwise disjoint and disjoint
from $W$, so their finite disjoint union with $W$ is affine. Quasi-compactness now gives a finite
affine cover

$$
T=U_1\cup\cdots\cup U_m
$$

in which every $U_i$ contains every generic point. Hence
$U=U_1\cap\cdots\cap U_m$ is dense. Replace $T$ by the scheme-theoretic closure of $U$ in $T$.
This is a surjective closed immersion, is an isomorphism over $U$, and its intersection with every
$U_i$ is a closed affine subscheme. Composing a projective modification of this closure with that
closed immersion gives the required modification of the original $T$, so we rename the closure
$T$. This makes $U$ schematically dense.

Each affine $U_i$ is of finite type over $A$, so generators of its coordinate algebra give an
immersion

$$
j_i:U_i\longrightarrow P_i=\mathbf P_A^{n_i}.
$$

Let $Z_i\subseteq P_i$ be its scheme-theoretic closure. Then $U_i\subseteq Z_i$ is a
schematically dense open and $Z_i$ is projective over $A$. The graph closures implicit in this
construction have an explicit finite Rees description. Fix an affine
$W=\operatorname{Spec}R$ from the finite cover above and one of the standard affine charts of
some $P_i$. The inverse image of that chart in $U\cap W$ is a
quasi-compact open of $W$, hence is covered by finitely many principal opens $D(f)\subseteq W$.
On $D(f)$ the affine
coordinates of the map are fractions in $R_f$. Multiplying by a common power of $f$ gives
homogeneous coordinates $a_0,\ldots,a_n\in R$ with $a_0=f^N$, say, and
$I=(a_0,\ldots,a_n)$. The tuple defines a map on $D(I)$, and the closure of its graph is

$$
\operatorname{Bl}_I(\operatorname{Spec}R)
=\operatorname{Proj}_R\!\left(\bigoplus_{d\geq0}I^d\right). \tag{9.8d}
$$

On the chart where $a_i$ is the chosen homogeneous coordinate, both sides have coordinate ring
$R[I/a_i]\subseteq R_{a_i}$; these charts cover, proving (9.8d), projectivity, and the fact that
the blowup is an isomorphism where $I$ is the unit ideal. The closure of the graph from the
smaller open $D(f)$ is a closed subscheme of this blowup. There are only finitely many $W$, $i$,
standard charts, and principal opens $D(f)$, so only finitely many ideals $I$ occur. Consequently
the global scheme-theoretic graph closure is covered by closed subschemes of finitely many
explicit Rees charts $R[I/a_i]$ and, independently, is projective over $T$ because it is closed in
$T\times_A P_i$. This is all the graph-and-blowup input used below; no compactification theorem is
being inserted.

Now form

$$
j=(j_1|_U,\ldots,j_m|_U):
U\longrightarrow P_1\times_A\cdots\times_A P_m
$$

and let $Z$ be its scheme-theoretic closure. The product map is an immersion, so $U$ is open and
schematically dense in $Z$; the preceding Rees calculation is also the affine-chart construction
of the closure of its graph. The scheme $Z$ is closed in a product of projective spaces, hence
projective over $A$. The $i$th projection $Z\to P_i$ factors through $Z_i$: the ideal of $Z_i$
vanishes on the schematically dense open $U$. Denote the resulting map by
$p_i:Z\to Z_i$ and put

$$
V_i=p_i^{-1}(U_i),
\qquad
T'=V_1\cup\cdots\cup V_m\subseteq Z.
$$

The map $p_i$ is proper: an $A$-map from the $A$-proper scheme $Z$ to the $A$-separated scheme
$Z_i$ is proper, as follows by factoring it through its closed graph in $Z\times_A Z_i$ and then
the base change $Z\times_A Z_i\to Z_i$ of $Z\to\operatorname{Spec}A$. Thus $T'$ is
quasi-projective over $A$. The maps $p_i|_{V_i}:V_i\to U_i\subseteq T$ agree on
overlaps: they agree on $U$, which is schematically dense in every $V_i\cap V_j$, and the
equalizer of two maps to the separated $A$-scheme $T$ is closed. They therefore glue to
$p:T'\to T$.

We verify properness rather than inferring it from the graph. First
$p^{-1}(U_i)=V_i$. One inclusion is immediate. Inside $p^{-1}(U_i)$ the open immersion
$V_i\hookrightarrow p^{-1}(U_i)$ is proper because $V_i\to U_i$ is the restriction of the
proper map $p_i$ and $p^{-1}(U_i)\to U_i$ is separated. Explicitly, its graph is closed and its
projection to $p^{-1}(U_i)$ is the base change of $V_i\to U_i$. It is therefore also closed, and it
contains the schematically dense open $U$; hence it is the whole inverse image. Consequently
$p$ is proper on the finite open cover $\{U_i\}$ and is proper globally. The same argument with
$U$ in place of $U_i$ gives $p^{-1}(U)=U$. Finally, the image of the proper map $p$ is closed
and contains the dense open $U$, so it is all of $T$. This proves the asserted surjectivity and
the modification statement, or proper birationality in the sense appropriate to a possibly
reducible and nonreduced scheme.

This modification is literally the graph closure just described. Let
$P=P_1\times_A\cdots\times_A P_m$ and let $\iota:T'\hookrightarrow P$ be the immersion already
constructed. The map $(p,\iota):T'\to T\times_A P$ is proper over $T$: its source is proper over
$T$ and its target is separated over $T$, so the same closed-graph factorization applies. Since it
is also an immersion (factor the graph of $p$ through $T\times_A T'$ and use the immersion
$T'\hookrightarrow P$), it is a closed immersion. Its image is the scheme-theoretic closure of
the graph of $j:U\to P$, because $U$ is schematically dense in $T'$. Thus the finitely many Rees
blowups above are affine-chart models of the actual modification, not merely auxiliary examples.

If $T$ is proper over $A$, then so is $T'$. Choose the immersion
$T'\hookrightarrow\mathbf P_A^N$ supplied by the product projective space and the Segre map.
Any $A$-map from the proper scheme $T'$ to the separated scheme $\mathbf P_A^N$ is proper; a
proper immersion is closed. Thus this immersion is a closed immersion and $T'$ is projective over
$A$, completing the relative Chow lemma.

We now prove proper finiteness by noetherian induction on a closed support; the empty support is
the initial case. Let $T\subseteq Z$ be a closed support. Given a coherent $G$ supported on $T$,
equip its support with the closed scheme
structure cut out by $\operatorname{Ann}(G)$, so that $G$ is genuinely a coherent sheaf on that
proper scheme. Apply the lemma to it. We obtain a projective modification $p:T'\to T$ which is an
isomorphism over a dense open $U$ meeting every generic point. Put $G'=p^*G$. The adjunction map
$\alpha:G\to p_*G'$ is the identity over $U$. Hence

$$
K=\ker\alpha,
\qquad C=\operatorname{coker}\alpha,
\qquad R^bp_*G'\ (b>0)
$$

are coherent and supported on the proper closed subset $W=T\setminus U$. Quasi-coherence of the
higher direct images is Theorem 4.7 of Book 7b, which also identifies them over an affine open
$V\subseteq T$ with $\widetilde{H^b(p^{-1}V,G')}$; their coherence follows from the projective
graded-resolution theorem of Book 8 applied to
$p:T'\to T$. A coherent sheaf supported on $W$ is killed by a power of the ideal of $W$ and has
a finite filtration whose quotients are pushforwards of coherent sheaves on $W_{\mathrm{red}}$.
The induction hypothesis therefore makes the cohomology of $K,C$, and every $R^bp_*G'$ for
$b>0$ finite over $A$.

The cohomology of $G'$ on the projective $A$-scheme $T'$ is finite by Book 8. Now use the Leray
spectral sequence for quasi-coherent sheaves, Corollary 4.9 of Book 7b, whose construction and
strong first-quadrant convergence are those of Book 7a, Sections 8.1 and 6.1:

$$
E_2^{a,b}=H^a(T,R^bp_*G')
\Longrightarrow H^{a+b}(T',G').
$$

It is bounded because $T$ and $T'$ are noetherian of finite dimension, so Corollary 5.9 of Book 7b
makes all but finitely many rows and columns vanish. All rows $b>0$ are finite by induction. The
bottom row is finite as well: $E_\infty^{a,0}$ is a
subquotient of the finite abutment, and, page by page backwards, the only incoming differential
comes from a finite higher row while every outgoing differential from $b=0$ is zero. Thus
$H^a(T,p_*G')$ is finite. If $I=\operatorname{im}\alpha$, the two exact sequences

$$
0\to K\to G\to I\to0,
\qquad
0\to I\to p_*G'\to C\to0
$$

and their long cohomology sequences now prove that every $H^a(T,G)$ is finite over $A$. This is a
genuine induction on closed subsets of the noetherian space and terminates.

Applying the result to the cohomology sheaves of a bounded coherent complex gives proper
finiteness for such complexes. In particular, $R\Gamma(Z,G)$ lies in
$D^b_{\mathrm{finite}}(A)$ once the cohomological-dimension bound in (iii) is known, and hence is
pseudo-coherent: resolve its finite cohomology modules successively by finite free modules.

**(ii) Formal functions, with the pro-step included.** Let $I\subset A$ and $G$ be coherent.
Put $G_n=I^nG$ and $\mathcal R=\bigoplus_{n\geq0}I^n$. This is a noetherian graded
$A$-algebra. The graded Rees module $\bigoplus_nG_n$ is finite over the pullback of
$\mathcal R$ to $Z$, so it corresponds to a coherent sheaf $\mathcal H$ on
$Z_{\mathcal R}=Z\times_A\operatorname{Spec}\mathcal R$. The latter is proper over the
noetherian ring $\mathcal R$, and part (i), now applied with base $\mathcal R$, makes
$H^q(Z_{\mathcal R},\mathcal H)$ finite over $\mathcal R$. The projection
$Z_{\mathcal R}\to Z$ is affine, so it does not change cohomology (Book 7b, Corollary 3.11), and
its pushforward of $\mathcal H$ is the direct sum $\bigoplus_nG_n$; cohomology on the
quasi-compact separated $Z$ commutes with that filtered colimit of finite partial sums by
Proposition 5.5 of Book 7b. These two facts identify the module with

$$
\bigoplus_{n\geq0}H^q(Z,G_n)
$$

as a graded $\mathcal R$-module. Thus it is finite.
Write $M_n^r=H^r(Z,I^nG)$ and $M_0^r=H^r(Z,G)$. Finite generation gives a constant $c_r$
with two consequences. First, the image of
$M_{n+m}^r\to M_n^r$ is contained in $I^{m-e}M_n^r$, where
$e=\max(0,c_r-n)$. Second, if
$K_n^r=\ker(M_n^r\to M_0^r)$, then

$$
K_n^r=\ker(M_n^r\longrightarrow M_{n-c_r}^r)
\qquad(n\geq c_r). \tag{9.8a}
$$

Indeed the first assertion follows after choosing homogeneous generators in degrees at most
$c_r$. For the second, $\bigoplus_nK_n^r$ is a graded submodule of the finite graded Rees module
$\bigoplus_nM_n^r$, hence has homogeneous generators in bounded degrees; multiplying those
generators and using compatibility with the transition maps gives (9.8a).

Now put $N_n^q=H^q(Z,G/I^nG)$ and let $P_n^q$ be the image of
$M_0^q\to N_n^q$. Apply (9.8a) in degree $q+1$ to the two long exact sequences for
$I^nG\subset G$ and $I^{n+m}G\subset G$. A diagram chase gives, for one fixed $c$ and every
$m\geq c$,

$$
\operatorname{im}(N_{n+m}^q\longrightarrow N_n^q)=P_n^q.
$$

Thus $(N_n^q)_n$ is Mittag--Leffler and has the same inverse limit as $(P_n^q)_n$; no
surjectivity of the transition maps of $N_n^q$ is asserted. If
$L_n^q=\ker(M_0^q\to P_n^q)$, the first Rees bound in degree $q$ gives, after enlarging $c$,

$$
I^nM_0^q\subseteq L_n^q\subseteq I^{n-c}M_0^q.
$$

Hence the quotient topology defined by the $P_n^q=M_0^q/L_n^q$ is exactly the $I$-adic
topology. Taking limits therefore gives

$$
H^q(Z,G)^\wedge_I\simeq
\varprojlim_n H^q(Z,G/I^nG). \tag{9.8b}
$$

This is the theorem on formal functions in exactly the form used below.

**(iii) Cohomological dimension one.** Localize $A$ at a point and complete it. Every
infinitesimal fiber has the same noetherian topological space as the closed fiber, of dimension at
most one. Grothendieck's vanishing theorem on a noetherian topological space of finite dimension
(Book 7b, Theorem 5.8) says that every sheaf of abelian groups has no cohomology above the
dimension; here the dimension is at most one, so all the coherent sheaves on the infinitesimal
fibers have vanishing cohomology in degrees $q>1$. Formula (9.8b) therefore makes the completion of
$R^qg_*G$ zero for $q>1$. Proper finiteness and faithful flatness of completion imply
$R^qg_*G=0$ for coherent $G$. For an arbitrary quasi-coherent $\mathcal G$ on the noetherian $Z$,
coherent exhaustion (Book 7b, Theorem 2.11) writes $\mathcal G$ as the filtered union of its
coherent subsheaves and Corollary 5.7 of the same book computes $H^q(Z,\mathcal G)$ as the colimit
of the $H^q$ of those subsheaves. Thus $g$ has quasi-coherent cohomological dimension at most
one, not just coherent cohomological dimension at closed fibers. (Corollary 5.9 of Book 7b gives
the same bound directly whenever $Z$ itself has dimension at most one, which is the case in the
applications below; the argument through formal functions is what covers a $Z$ whose total space
is of larger dimension than its fibers.)

**(iv) Derived base change and perfectness.** This is Book 7b, Theorem 5.2, applied to the
quasi-compact separated morphism $g:Z\to\operatorname{Spec}A$ and the $A$-flat quasi-coherent sheaf
$\mathcal F$. We recall what that theorem provides, since the shape of the complex, not merely the
existence of the isomorphism, is used below. Choose a finite affine cover of $Z$; because $Z$ is
separated, all its finite intersections are affine, so by the Čech model theorem (Book 7b,
Theorem 4.2) the alternating Čech complex $C^\bullet(\mathcal F)$ of that cover is a bounded
complex representing $R\Gamma(Z,\mathcal F)$. Lemma 5.1 of Book 7b records the two properties that
matter: each term is $A$-flat, being the module of sections of the $A$-flat sheaf $\mathcal F$ over
an affine intersection, so the complex is $K$-flat in the sense of Book 7a, Section 3.3; and its
formation commutes with scalar extension on the nose, $C^\bullet(\mathcal F)\otimes_AB
=C^\bullet(\mathcal F_B)$. Theorem 5.2 of Book 7b concludes that for every $A$-algebra $B$ the
canonical map

$$
B\otimes_A^LR\Gamma(Z,\mathcal F)
\xrightarrow{\sim}R\Gamma(Z_B,\mathcal F_B) \tag{9.8c}
$$

is an isomorphism, and that more generally, for every $A$-module $M$,
$C^\bullet(\mathcal F)\otimes_AM$ computes $R\Gamma(Z,\mathcal F\otimes_AM)$ and
$R\Gamma(Z,\mathcal F)\otimes^L_AM\simeq R\Gamma(Z,\mathcal F\otimes_AM)$. Part (iii) places its
cohomology in degrees
$0,1$. Thus the pseudo-coherent complex $R\Gamma(Z,\mathcal F)$ has Tor-amplitude $[0,1]$.
Truncating a finite free resolution below that interval makes the last syzygy finitely presented
and flat, hence finite projective; the complex is perfect and is locally represented by two
finite projective modules. Formula (9.8c) says that this same complex computes every base
change. This proves the proper-curve complex lemma.

Choose $n$ so that $L_{\bar s}=\mathcal O_{X_{\bar s}}(nD)$ is very ample and
$H^1(X_{\bar s},L_{\bar s})=0$. Apply the proper-curve complex lemma to
$L=\mathcal O_X(nD)$, which is base-flat. Shortening its complex at $\bar s$ shows, after
shrinking, that $f_*L$ is finite locally free, commutes with base change, and that the
restriction map

$$
f_*L\otimes\kappa(\bar s)\longrightarrow H^0(X_{\bar s},L_{\bar s})
$$

is onto. The evaluation $f^*f_*L\to L$ is onto on the chosen fiber. Its cokernel has closed
support, whose image under the proper map $f$ is closed; shrinking removes that image. Hence
evaluation is onto and defines a proper morphism
$\phi:X\to\mathbf P_S(f_*L)$ in the quotient convention of Book 8.

The fiber $\phi_{\bar s}$ is a closed immersion. This property spreads without a hidden
section-lifting assertion. Upper semicontinuity of fiber dimension makes $\phi$ quasi-finite
on a neighborhood of $X_{\bar s}$; the complementary closed locus has proper image on the
base, so shrinking makes $\phi$ quasi-finite everywhere. Being proper, it is then finite.
For a finite morphism, closed immersion is the surjectivity of
$\mathcal O_{\mathbf P}\to\phi_*\mathcal O_X$. Its cokernel is finite and has zero special
fiber because $\phi_{\bar s}$ is a closed immersion. Nakayama and properness of projective
space remove its support after one more shrinking. Thus the algebra map is surjective and
$\phi$ is a closed immersion. We have produced the projective embedding directly. The
residue-field extension and the shrinking form the required faithfully flat
finite-presentation neighborhood.
$\square$

For geometrically reduced fibers one may choose the points in the smooth locus, so after an
étale extension the divisor is simply a sum of sections. The longer argument above is needed
for nonreduced Cohen--Macaulay fibers, whose smooth locus may be empty.

**Theorem 9.2 (relative curve duality).** Let $f:X\to S$ be a proper flat finitely presented
Cohen--Macaulay morphism of pure relative dimension one, with $S$ locally noetherian. There is
an $S$-flat coherent sheaf $\omega_{X/S}$ with trace (9.12) and functorial duality (9.11).
The sheaf, trace, and pairing are independent of projective embeddings and commute with every
base change $S'\to S$ as in (9.10).

**Proof.** We first work after the faithfully flat finite-presentation neighborhood supplied by
Lemma 9.2A; there the curve has an embedding
$i:X\hookrightarrow P=\mathbf P^N_S$. The final paragraph descends the resulting canonical
objects to the original base. Put $c=N-1$.

We first record the relative form of the two algebraic ingredients used above. Over an affine
$\operatorname{Spec}A\subseteq S$, the exponentwise contractions used after (9.1) are defined
with coefficients $0,1,-1$. They therefore retract the Čech complexes to finite free
$A$-complexes and are unchanged after tensoring with any $A$-algebra. The surviving monomials
pair perfectly. This proves duality first for sums of twists. For an arbitrary vector bundle
$V$ on $P$, Book 8 supplies finite projective complexes, compatible with every scalar extension,
for $R\Gamma(P,V)$ and $R\Gamma(P,V^\vee\otimes\omega_{P/S})$. Cup product followed by the top
coefficient defines a map between the latter complex (shifted by $N$) and the dual of the former.
On every geometric fiber this is the absolute projective-space quasi-isomorphism (9.2). Its cone
is a perfect $A$-complex with zero derived fiber at every prime; successively taking the first
nonzero cohomology and applying Nakayama makes the cone zero. Consequently projective-space
duality holds for every vector bundle over $A$. The construction and the fiber test use the
fixed base-change-compatible complexes, so the isomorphism commutes with arbitrary base change.

Next, $i_*\mathcal O_X$ has a finite locally free resolution on $P$ which remains a resolution
after every base change. We spell out the relative syzygy lemma which makes this true even
when the base is singular.

**Relative syzygy lemma.** Let $A\to R$ be a flat finitely presented algebra, let $M$ be a
finitely presented $R$-module flat over $A$, and suppose that for every geometric point
$\bar s\to\operatorname{Spec}A$ the $R_{\bar s}$-module $M_{\bar s}$ has projective dimension
at most $c$. Then, locally on $\operatorname{Spec}R$, $M$ has a length-$c$ resolution by
finite free $R$-modules, all of whose syzygies are $A$-flat. The resolution stays exact after
every $A$-algebra extension.

Choose successive finite-free surjections $F_j\twoheadrightarrow K_j$, beginning with
$K_0=M$. If $K_j$ is $A$-flat, the kernel $K_{j+1}$ is $A$-flat by the Tor sequence. On each
geometric fiber the $c$th syzygy is projective. The fiberwise flatness criterion now makes
$K_c$ flat over $R$: for a local map $A\to R$ and a finite $R$-module $N$, flatness of $N$
over $A$ together with flatness of $N\otimes_A\kappa(\mathfrak p)$ over
$R\otimes_A\kappa(\mathfrak p)$ implies $R$-flatness. To prove the criterion, apply the two
Tor spectral sequences for
$(-)\otimes_RN$ and reduction modulo a finitely generated ideal of $R$; the base-flatness
kills the rows with positive $A$-Tor, and fiber-flatness kills the remaining positive row.
The equational criterion then gives $R$-flatness. Finite presentation turns flatness into
local projectivity, and shrinking makes $K_c$ free. Finally, each short exact sequence remains
exact after arbitrary base change because its quotient $K_j$ is $A$-flat. This proves the
lemma.

Apply it on affine charts of $P$. On a geometric fiber $P_{\bar s}$ is regular and
$X_{\bar s}$ is Cohen--Macaulay of codimension $c$; the depth calculation (9.3) gives projective
dimension exactly $c$. Globalizing the successive surjections by sufficiently positive sums
of twists yields a universally exact resolution $E^\bullet\to i_*\mathcal O_X$: after each
surjection the kernel is coherent and $S$-flat, so it may be twisted until globally generated;
at the $c$th step the relative syzygy lemma makes the kernel flat and finitely presented over
$P$, hence finite locally free. Exactness after every scalar extension follows at each step from
flatness of the quotient, so this is a global finite locally free resolution, not merely a
collection of affine resolutions.

We also need the dual form of the lemma.

**Fiberwise acyclicity lemma.** Let $A\to R$ be flat and finitely presented, and let
$C^\bullet$ be a bounded complex of finitely presented $R$-modules which are flat over $A$.
If $H^j(C^\bullet\otimes_A\overline{\kappa(s)})=0$ for every geometric fiber and every
$j\ne c$, then $H^j(C^\bullet)=0$ for $j\ne c$, the $R$-module $H^c$ is flat over $A$, and
these conclusions commute with every $A$-algebra extension.

Here is the local proof. At the left endpoint the fiber differential is injective. The local
flatness criterion for a cokernel says that a map between flat modules is universally
injective with flat cokernel exactly when it is injective on every residue-field fiber. For a
finitely generated ideal $J\subset A$, this follows from

$$
0\to\operatorname{Tor}_1^A(Q,A/J)\to C^a\otimes_AA/J
\to C^{a+1}\otimes_AA/J,
$$

followed by the equational criterion for flatness. This is checked locally at a prime of $R$:
reduce modulo the corresponding prime of $A$, use fiberwise injectivity, and apply Nakayama to
the finitely generated $R$-kernels. Thus the cokernel is a finitely presented $R$-module flat
over $A$. Replace the first two terms by it and repeat until degree $c$. From the right,
fiberwise surjectivity and Nakayama give an actual surjection; its kernel is $A$-flat because
its quotient is. Repetition leaves in degree $c$ an extension of $A$-flat modules, hence an
$A$-flat module. Every short exact sequence constructed is universally exact, so tensoring by
an arbitrary $A$-algebra repeats the argument verbatim and proves base change. Notice that no
module is required to be finite over $A$; finite presentation over $R$ is exactly what the
local Nakayama argument uses.

Apply this lemma to the dual of $E^\bullet$ against $\omega_{P/S}$, whose terms are locally
free over the $S$-flat scheme $P$. Fiberwise Ext concentration shows that its cohomology is
concentrated in degree $c$, is $S$-flat there, and retains this description after arbitrary
base change. Define

$$
i_*\omega_{X/S}=
\mathcal Ext^c_P(i_*\mathcal O_X,\omega_{P/S}). \tag{9.9}
$$

This sheaf is $S$-flat. The universally exact dual resolution also proves that
for every $g:S'\to S$,

$$
Lg'^*\omega_{X/S}=g'^*\omega_{X/S}
\xrightarrow{\sim}\omega_{X_{S'}/S'}. \tag{9.10}
$$

For a vector bundle $\mathcal E$ on $X$, the same relative syzygy construction resolves
$i_*\mathcal E$: it is base-flat and its geometric fibers remain Cohen--Macaulay modules of
codimension $c$. Apply the strict dg currying map (9.5a). Locally it may be computed with the
universally exact finite resolutions of $i_*\mathcal E$ and $i_*\mathcal O_X$: evaluation
$\mathcal E\otimes\mathcal E^\vee\to\mathcal O_X$ gives the comparison, and the fiberwise
acyclicity lemma identifies its target with
$i_*(\mathcal E^\vee\otimes\omega_{X/S})[-c]$ before and after arbitrary tensor product. Thus
the dg map is a base-change-compatible quasi-isomorphism. Relative projective-space duality then
gives

$$
R f_*(\mathcal E^\vee\otimes\omega_{X/S})[1]
\simeq
R\mathcal Hom_S(Rf_*\mathcal E,\mathcal O_S). \tag{9.11}
$$

All objects here are represented locally by the finite resolutions and finite Čech complexes
just constructed. Thus (9.11) is an isomorphism of explicit bounded complexes, not an appeal to
an undeveloped exceptional inverse-image theory.

For $\mathcal E=\mathcal O_X$, evaluation followed by the top Čech coefficient functional gives
the counit. In degree one it is the trace

$$
\operatorname{tr}_f:R^1f_*\omega_{X/S}\longrightarrow\mathcal O_S. \tag{9.12}
$$

The tensor compatibility of the Čech pairing shows directly that (9.10), the trace, and (9.11)
commute with arbitrary base change.

It remains to prove, rather than infer from an undersized test category, independence of the
embedding. We first record the local-to-global replacement for a nonexistent global Koszul
complex.

**Regular-immersion fundamental-class lemma.** If $j:W\hookrightarrow Y$ is a regular immersion
of codimension $d$, then $\mathcal O_W$ is a perfect $\mathcal O_Y$-complex and, for every
complex $K$ on $Y$, local Koszul duality gives a canonical isomorphism

$$
R\mathcal Hom_Y(\mathcal O_W,K)
\simeq
j_*\bigl(Lj^*K\otimes\det(\mathcal I/\mathcal I^2)^\vee\bigr)[-d]. \tag{9.12a}
$$

To construct it, cover $Y$ by affines on which $\mathcal I=(f_1,\ldots,f_d)$ is a regular
sequence and use the Koszul complex $K(f)$; tensoring $K(f)$ with $K$ computes $Lj^*K$. If
$g=Af$ is a second sequence, the induced Koszul
comparison acts in top degree by $\det(A)$, exactly the transition function of
$\det(\mathcal I/\mathcal I^2)^\vee$. Two lifts of the same conormal change differ by a Koszul
homotopy. Consequently the local maps agree in the derived category on double overlaps; on
triple overlaps matrix multiplication gives the cocycle. They therefore glue to (9.12a).
For composable regular immersions, the conormal exact sequence and the tensor product of the two
local Koszul complexes identify this fundamental class with that of the composite. These
identities survive every base change for which the immersions remain regular; in particular they
do so for a section of a smooth morphism.

Now suppose $i_a:X\hookrightarrow P_a$ are two projective embeddings. The product embedding
$i=(i_1,i_2):X\hookrightarrow P_1\times_SP_2$ is a common refinement. To compare it with
$i_1$, base-change a resolution of $X\subset P_1$ to resolve
$X\times_SP_2\subset P_1\times_SP_2$. The graph of $i_2$ is a section
$X\hookrightarrow X\times_SP_2$ of the smooth projection and is therefore a regular immersion
of codimension $\dim(P_2/S)$. The fundamental-class lemma says globally in the derived category
that this graph is perfect over $X\times_SP_2$; the base-changed resolution says that
$X\times_SP_2$ is perfect over $P_1\times_SP_2$. Perfectness is local and closed under
composition, so the product embedding is perfect. The global relative-syzygy construction above
now supplies a universally exact finite ambient resolution of it. On every
Koszul chart that resolution is homotopy equivalent to the composite perfect object, and the
fundamental-class cocycle makes these identifications canonical in the derived category. On
duals, the canonical identification is the sheafified dg currying isomorphism. Writing
$Q=P_1\times_SP_2$, $Y=X\times_SP_2$, $k:Y\hookrightarrow Q$, and
$j:X\hookrightarrow Y$ for the graph, it is

$$
R\mathcal Hom_Q(k_*j_*\mathcal O_X,\omega_{Q/S})
\simeq
k_*R\mathcal Hom_Y\!\left(j_*\mathcal O_X,
  k^!\omega_{Q/S}\right),
$$

where $k^!\omega_{Q/S}$ is notation here for the explicitly computed dg coinduction
$R\mathcal Hom_Q(k_*\mathcal O_Y,\omega_{Q/S})$, viewed as a complex on $Y$; no general
exceptional inverse-image functor is being assumed. Affine-locally this is the equality of dg Hom
complexes (9.5a), so it is canonical and associative. The determinant cancellation in this
comparison is explicit. If $N_a=\dim(P_a/S)$ and $\omega_X^{(1)}$ is the Ext sheaf constructed
from $i_1$, base change of the universally exact resolution for $i_1$ gives

$$
k^!\omega_{Q/S}\simeq
\operatorname{pr}_X^*\omega_X^{(1)}[-(N_1-1)]
\otimes\operatorname{pr}_{P_2}^*\omega_{P_2/S}.
$$

The conormal bundle of the graph $j$ is $i_2^*\Omega^1_{P_2/S}$, whose determinant is
$i_2^*\omega_{P_2/S}$. Formula (9.12a) therefore cancels the last tensor factor and adds the
shift $-N_2$, leaving
$\omega_X^{(1)}[-(N_1+N_2-1)]$, exactly the Ext complex defining the dualizing sheaf from the
product embedding. This calculation uses derived pullback in (9.12a), so it remains valid without
assuming that $\omega_X^{(1)}$ is a line bundle. The two Čech coefficient
functionals are compatible because
extracting the top coefficient first in the $P_2$ variables and then in the $P_1$ variables is
the same as extracting the coefficient of the product monomial. Thus the common refinement gives
a canonical trace-compatible isomorphism between the two Ext sheaves. A triple product gives the
cocycle identity: the Koszul fundamental classes compose, and both coefficient maps are the
associativity isomorphism for a threefold tensor product. This proves embedding independence
without postulating a global Koszul resolution and without claiming that vector bundles alone
detect all coherent objects on a singular $X$.

The same calculation proves the transitivity in the range constructed here. If
$j:Z\hookrightarrow X$ is a
regular immersion of codimension $d$ and $Z/S$ is Cohen--Macaulay of pure relative dimension
$1-d$, the fundamental-class lemma gives

$$
\omega_{Z/S}\simeq
j^*\omega_{X/S}\otimes
\det(\mathcal I/\mathcal I^2)^\vee. \tag{9.12b}
$$

The ordinary pullback in (9.12b) is justified rather than assumed. Flatness of $X/S$ and $Z/S$
makes the Koszul resolution of $\mathcal O_Z$ universally exact. On each geometric fiber its
regular sequence is also regular on the maximal Cohen--Macaulay module $\omega_{X_s}$ by the
depth criterion. Since $\omega_{X/S}$ is $S$-flat, the fiberwise acyclicity lemma lifts this
exactness and gives $Lj^*\omega_{X/S}=j^*\omega_{X/S}$, compatibly with every base change.

For two regular immersions, the conormal exact sequence identifies the determinant on the
composite with the tensor product of the two determinants. The local tensor product of Koszul
complexes shows that evaluation in succession equals evaluation of the composite; hence
adjunction and trace are associative.

There is also the proper--finite transitivity used for maps of curves. If
$\pi:Y\to X$ is finite and both $Y/S$ and $X/S$ satisfy the hypotheses of the theorem, dg
currying gives, compatibly with arbitrary base change,

$$
\pi_*\omega_{Y/S}
\simeq\mathcal Hom_X(\pi_*\mathcal O_Y,\omega_{X/S}). \tag{9.12c}
$$

Here concentration in ordinary $\mathcal Hom$ and its base change are consequences of the
ambient resolutions, not formal properties of underived Hom. After embedding $X$ in
$P=\mathbf P^N_S$, both $i_*\mathcal O_X$ and $i_*\pi_*\mathcal O_Y$ are $S$-flat coherent
$\mathcal O_P$-modules. On a geometric fiber the second is Cohen--Macaulay of codimension
$N-1$: finiteness identifies its support dimension and its depth with the depth on $Y_s$.
The relative syzygy lemma therefore gives universally exact finite ambient resolutions of both
modules, and the fiberwise acyclicity lemma concentrates both dual resolutions in degree $N-1$.
Applying the strict currying identity (9.5a) to the finite algebra
$\mathcal O_X\to\pi_*\mathcal O_Y$ identifies the second Ext sheaf with the right side of
(9.12c). Because every resolution and every concentration statement remains exact after tensoring
with an arbitrary $\mathcal O_S$-algebra, this identification proves the asserted base change.

Evaluation at $1$ defines $\operatorname{Tr}_\pi$. In the projective-space model,
$\operatorname{tr}_{f\circ\pi}$ extracts the ambient top coefficient after evaluation at $1$;
this is exactly $\operatorname{tr}_f\circ R^1f_*(\operatorname{Tr}_\pi)$. For a tower of finite
maps, currying identifies iterated evaluation at $1$ with direct evaluation at $1$, proving
associativity. For products of projective spaces, the same assertion is the Fubini identity for
coefficient extraction. These arguments establish regular-immersion and proper--finite trace
transitivity. No claim about nonflat dualizing complexes, which have not been constructed in
this book, is made.

Finally descend from the fpqc projectivity cover of Lemma 9.2A. The canonical common-refinement
isomorphisms just constructed provide descent data and satisfy the cocycle condition. The
descent itself is the elementary module equalizer: for a faithfully flat $A\to B$ and a
$B$-module with a cocycle, take the equalizer of its two pullbacks to $B\otimes_A B$. After
tensoring with $B$, the first three terms of the Amitsur complex are contracted by multiplication
in the extra tensor factor, so faithful flatness proves that the equalizer pulls back to the
original module. Apply this on affine opens and glue. Finite presentation, flatness, the trace,
and the displayed maps descend because they can be checked after faithfully flat pullback.
The base-change isomorphisms descend as well and are independent of every resolution and
embedding. This proves relative duality, trace, embedding independence, transitivity, and
arbitrary base change in the stated Cohen--Macaulay relative-curve setting.
$\square$

### 9.4 Smooth and Gorenstein families

If $f$ is smooth of relative dimension one, the construction of Section 9.3 identifies

$$
\omega_{X/S}\simeq\Omega^1_{X/S}.
$$

Indeed, on an étale coordinate chart both candidates are freely generated by $dt$. Resolve the
diagonal in the product of the chart with the affine line: its conormal generator $t_1-t_2$
dualizes to $dt$. The coefficient trace of Section 9.3 is the residue coefficient in this
coordinate, so these local identifications preserve trace. Uniqueness in Section 9.3 glues them.

The morphism $f$ is **Gorenstein** when it is flat and its fibers have Gorenstein local rings, equivalently in this setting when $\omega_{X/S}$ is invertible. A relative local complete intersection of pure dimension one is Gorenstein. In particular, a family locally given inside a smooth relative surface by one regular equation has an invertible dualizing sheaf.

For a relative hypersurface $X=(F=0)$ in a smooth $S$-scheme $P$ of relative dimension two, adjunction gives

$$
\omega_{X/S}\simeq
\left(\omega_{P/S}\otimes\mathcal O_P(X)\right)|_X. \tag{9.13}
$$

Unlike $\Omega^1_{X/S}$, the right side stays invertible when a smooth fiber acquires a node.
Formula (9.13) is the practical construction of invariant differentials on many modular and
plane-curve families.

### 9.5 Proper pushforward, Stein factorization, and connected fibers

The proof of Lemma 9.2A established two facts about a proper morphism which are of independent
importance and are used repeatedly later: coherence of the higher direct images, part (i) of the
proper-curve complex lemma, and the theorem on formal functions (9.8b), part (ii). Neither of those
two parts used flatness or the one-dimensionality of the fibers; both were proved for an arbitrary
proper morphism to the spectrum of a noetherian ring, by Chow's lemma and noetherian induction on a
closed support in (i) and by the Rees construction in (ii). Flatness and the fiber dimension entered
only in parts (iii) and (iv). We now draw the standard consequence, which is the statement that a
proper morphism
factors canonically into a morphism with connected fibers followed by a finite morphism. This is the
tool that converts the vanishing $f_*\mathcal O_X=\mathcal O_Y$ into geometric connectedness of
fibers, and it is used in the surface theory of later volumes exactly in that form.

Throughout, $Y$ is a locally noetherian scheme and $f:X\to Y$ is proper.

**Theorem 9.3 (Stein factorization).** Let $f:X\to Y$ be a proper morphism with $Y$ locally
noetherian. Put

$$
\mathcal A=f_*\mathcal O_X,
\qquad
Y'=\operatorname{\mathbf{Spec}}_Y(\mathcal A),
$$

and let $f=p\circ g$ be the induced factorization, with $g:X\to Y'$ and $p:Y'\to Y$. Then:

1. $\mathcal A$ is a coherent $\mathcal O_Y$-algebra, so $p$ is a finite morphism and $Y'$ is
   locally noetherian;
2. $g$ is proper, surjective, and satisfies $g_*\mathcal O_X=\mathcal O_{Y'}$;
3. every fiber of $g$ is connected and nonempty;
4. if in addition $f_*\mathcal O_X=\mathcal O_Y$, then $p$ is an isomorphism, so $f$ itself has
   connected nonempty fibers;
5. if $X$ is reduced, respectively integral, respectively normal, then so is $Y'$.

**Proof.** (1) The question is local on $Y$, so let $Y=\operatorname{Spec}A$ with $A$ noetherian.
The sheaf $f_*\mathcal O_X$ is quasi-coherent by Theorem 2.10 of Book 7b, and by Theorem 4.7 of that
book it is the sheaf associated with the $A$-module $H^0(X,\mathcal O_X)$. Part (i) of the
proper-curve complex lemma, proved inside Lemma 9.2A for an arbitrary proper morphism to the
spectrum of a noetherian ring, makes that module finite over $A$. Hence $\mathcal A$ is a coherent
$\mathcal O_Y$-algebra, its relative spectrum $p:Y'\to Y$ is finite, and $Y'$ is locally noetherian.

(2) The morphism $p$ is separated, being affine, so $g$ is proper because $f=p\circ g$ is proper and
$p$ is separated. For the pushforward, $p$ is affine, so $p_*$ is exact and reflects isomorphisms of
quasi-coherent sheaves (Book 7b, Lemma 2.9 and Corollary 3.11); since
$p_*g_*\mathcal O_X=f_*\mathcal O_X=\mathcal A=p_*\mathcal O_{Y'}$ and the identification is the
canonical map, we get $g_*\mathcal O_X=\mathcal O_{Y'}$.

For surjectivity, note that a proper morphism is closed, so the image of $g$ is a closed subset of
$Y'$. The ideal sheaf of the scheme-theoretic image of $g$ is
$\ker(\mathcal O_{Y'}\to g_*\mathcal O_X)$, which is zero by the previous paragraph; so the
scheme-theoretic image is all of $Y'$, and since $g$ is closed its set-theoretic image is the
underlying space of the scheme-theoretic image. Hence $g$ is surjective.

(3) Fix a point $y'\in Y'$ and let $A=\mathcal O_{Y',y'}$, a noetherian local ring with maximal ideal
$\mathfrak m$ and residue field $\kappa$. Base change along the flat morphism
$\operatorname{Spec}A\to Y'$ preserves properness and, by flat base change for quasi-coherent
cohomology (Book 7b, Theorem 5.3 and Corollary 5.4), preserves the identity $g_*\mathcal
O_X=\mathcal O_{Y'}$; so we may assume $Y'=\operatorname{Spec}A$ with $A$ noetherian local, and then
$H^0(X,\mathcal O_X)=A$.

Write $X_n$ for the closed subscheme of $X$ defined by $\mathfrak m^{n+1}\mathcal O_X$. All the
$X_n$ have the same underlying topological space, namely the fiber $g^{-1}(y')$, which is nonempty
by (2). The theorem on formal functions (9.8b), applied with $I=\mathfrak m$ and $q=0$, gives

$$
\widehat A\;=\;H^0(X,\mathcal O_X)^{\wedge}_{\mathfrak m}
\;\simeq\;\varprojlim_n H^0(X_n,\mathcal O_{X_n}). \tag{9.14}
$$

Suppose the fiber $g^{-1}(y')$ were disconnected. Then its structure sheaf on $X_0$ has a global
idempotent $e_0\in H^0(X_0,\mathcal O_{X_0})$ with $e_0\neq0$ and $e_0\neq1$, namely the
characteristic function of one of the two pieces of a decomposition into disjoint nonempty opens.
The kernel of $\mathcal O_{X_{n+1}}\to\mathcal O_{X_n}$ is the ideal
$\mathfrak m^{n+1}\mathcal O_X/\mathfrak m^{n+2}\mathcal O_X$, whose square is zero; hence the
kernel of $H^0(X_{n+1},\mathcal O_{X_{n+1}})\to H^0(X_n,\mathcal O_{X_n})$ is a square-zero ideal.
Idempotents lift uniquely along a square-zero ideal: if $\tilde e$ lifts $e$ and $\varepsilon
=\tilde e^2-\tilde e$ lies in the square-zero kernel, then $\tilde e-(2\tilde e-1)\varepsilon$ is
idempotent and reduces to $e$, and two idempotent lifts differ by an element of the kernel that is
both idempotent and square-zero, hence zero. Inductively we obtain a compatible family
$e_n\in H^0(X_n,\mathcal O_{X_n})$ of idempotents lifting $e_0$, and hence by (9.14) an idempotent
$e\in\widehat A$ reducing to $e_0$. Now $\widehat A$ is a local ring, so its only idempotents are
$0$ and $1$; and $e$ reduces to $e_0\notin\{0,1\}$ in $H^0(X_0,\mathcal O_{X_0})$, whereas the images
of $0$ and $1$ are $0$ and $1$. This contradiction shows that every fiber of $g$ is connected.

(4) If $f_*\mathcal O_X=\mathcal O_Y$ then $\mathcal A=\mathcal O_Y$, so $p$ is an isomorphism and
$g=f$ up to that identification. Then (3) applies to $f$.

(5) By (2), for every affine open $V\subseteq Y'$ we have
$\mathcal O_{Y'}(V)=\mathcal O_X(g^{-1}V)$, and $g^{-1}V$ is a nonempty open subscheme of $X$ by
surjectivity. If $X$ is reduced then so is each such ring of sections, hence $Y'$ is reduced. If $X$
is integral then each such ring is a subring of $k(X)$, hence a domain, and $Y'$ is connected
because $X$ is and $g$ is surjective; a connected scheme all of whose local rings are domains and
which is covered by affines with domain coordinate rings is integral. If $X$ is normal then
$\mathcal O_X(g^{-1}V)$ is integrally closed in $k(X)$, being the intersection of the integrally
closed local rings $\mathcal O_{X,\xi}$ over the points $\xi$ of $g^{-1}V$; an element of the
fraction field of $\mathcal O_{Y'}(V)$, which lies in $k(X)$, and is integral over
$\mathcal O_{Y'}(V)=\mathcal O_X(g^{-1}V)$, therefore already lies in it. So $Y'$ is normal.
$\square$

Three comments delimit the theorem. First, no flatness and no hypothesis on the fibers is needed;
the only inputs are properness, local noetherianity of the base, coherence of $f_*$, and formal
functions. Second, the connectedness produced in (3) is connectedness of the fiber as a topological
space; geometric connectedness of fibers is a strictly stronger statement, requiring a separate
argument after base change to an algebraic closure of the residue field, and is not asserted here.
Third, part (4) is the form in which the theorem is normally applied: one checks
$f_*\mathcal O_X=\mathcal O_Y$, for instance because $Y$ is normal and $f$ is proper birational, and
concludes that all fibers are connected.

**Corollary 9.4 (proper birational morphisms to a normal base).** Let $f:X\to Y$ be a proper
surjective morphism of integral locally noetherian schemes with $Y$ normal and with
$k(X)/k(Y)$ an isomorphism of function fields, that is, $f$ birational. Then
$f_*\mathcal O_X=\mathcal O_Y$ and every fiber of $f$ is connected.

**Proof.** By Theorem 9.3(1) the algebra $\mathcal A=f_*\mathcal O_X$ is a coherent sheaf of
$\mathcal O_Y$-algebras, and it is a sheaf of domains contained in the constant sheaf $k(X)=k(Y)$
because $X$ is integral and $f$ dominant. So over an affine open $V=\operatorname{Spec}B\subseteq Y$
the ring $\mathcal A(V)$ is a finite $B$-algebra contained in the fraction field of $B$, hence
consists of elements integral over $B$; normality of $B$ forces $\mathcal A(V)=B$. Thus
$f_*\mathcal O_X=\mathcal O_Y$, and Theorem 9.3(4) gives connected fibers. $\square$

Corollary 9.4 is the statement invoked whenever a blowup or a resolution is compared with its base:
the exceptional fiber over a point is connected, so the exceptional divisor of a birational proper
morphism from a normal surface cannot be split into two pieces meeting no common point. The
intersection-theoretic consequences of that connectedness belong to the surface theory of the next
volumes; what is proved here is precisely the input those arguments require.

## 10. Nodes, normalization, and opposite residues

### 10.1 The local node

Over an algebraically closed field, a node has completed local ring

$$
A=k[[x,y]]/(xy).
$$

Its normalization is

$$
\widetilde A=k[[x]]\oplus k[[y]],
$$

corresponding to two branches. The hypersurface-adjunction candidate for the dualizing module of
$A$ is free of rank one. Inside meromorphic differentials on the branches, a generator is
represented by

$$
\theta=\left(\frac{dx}{x},-\frac{dy}{y}\right). \tag{10.1}
$$

The two residues are $1$ and $-1$. This is the origin of the opposite-residue rule.

For the smoothing $xy=a$ over a base ring, relative differentiation gives

$$
y\,dx+x\,dy=0.
$$

On the locus where $x$ or $y$ is invertible,

$$
\frac{dx}{x}=-\frac{dy}{y}.
$$

The common expression extends as a generator of the relative adjunction line through the node,
although neither $dx/x$ nor $dy/y$ is an ordinary regular differential there. By the
compatibility clause of Section 9.3, this adjunction line is the relative dualizing sheaf.

### 10.2 Functions under normalization

Let $C$ be a reduced proper nodal curve over $k$, and $\nu:\widetilde C\to C$ its normalization. For simplicity first assume every node and both branches are $k$-rational. If a node $q$ has inverse images $q',q''$, a regular function on $\widetilde C$ descends exactly when its values at $q'$ and $q''$ agree. Therefore

$$
0\longrightarrow\mathcal O_C
\longrightarrow\nu_*\mathcal O_{\widetilde C}
\longrightarrow\bigoplus_{q\in\operatorname{Sing}C}k_q
\longrightarrow0, \tag{10.2}
$$

where the last map is $(f',f'')\mapsto f'(q')-f''(q'')$.

Over a nonclosed field, put
$B_q=H^0(\nu^{-1}(q),\mathcal O_{\nu^{-1}(q)})$; this is a degree-two étale algebra over
$\kappa(q)$. The intrinsic discrepancy line is

$$
Q_q=B_q/\kappa(q),
$$

where $\kappa(q)$ is embedded diagonally. Thus the last term in (10.2) must in general be
replaced by $\bigoplus_q i_{q*}Q_q$. It is a one-dimensional $\kappa(q)$-vector space, but it is
not canonically the residue field: ordering two split branches identifies it with
$\kappa(q)$ and reversing the order changes the sign. This formulation is Galois invariant.

Taking Euler characteristics is now unambiguous. If $C$ is connected and $\widetilde C$ has
connected components $\widetilde C_1,\ldots,\widetilde C_r$, then

$$
p_a(C)=\sum_i p_a(\widetilde C_i)
+\sum_q[\kappa(q):k]-r+1.
$$

In the split case, when the normalization components are smooth of genera $g_i$ and there are
$\delta$ nodes, this becomes

$$
p_a(C)=\sum_i g(\widetilde C_i)+\delta-r+1. \tag{10.3}
$$

The term $\delta-r+1$ is the first Betti number of the connected dual graph. The preceding general
formula shows explicitly that residue-field degrees are not lost before splitting.

### 10.3 Rosenlicht differentials

The right side below can be defined directly, without global duality; call it the **Rosenlicht
sheaf**. After splitting the branches, write $\operatorname{res}$ for the Laurent coefficient of
$dt/t$ on a branch. In the geometrically nodal setting the normalization is smooth over $k$:
after a separable splitting extension it is regular with smooth completed branches, and smoothness
descends. Thus ordinary differentials on the normalization are legitimate here. The absolute
theorem of Section 9.2 shows that the Rosenlicht sheaf is
the dualizing sheaf and

$$
\omega_C=
\left\{
\eta\in\nu_*\Omega^1_{\widetilde C}
\Big(\sum(q'+q'')\Big):
\operatorname{res}_{q'}(\eta)+\operatorname{res}_{q''}(\eta)=0
\text{ for every node }q
\right\}. \tag{10.4}
$$

When the nodes and branches are rational, the residues in (10.4) are the literal Laurent
coefficients of Section 8.3, by Theorem 8.5. In general, (10.4) means the same condition after a field extension
that splits the branches; it is invariant under descent. Intrinsically it says

$$
\sum_{p\mapsto q}\operatorname{Res}_p(f\eta)=0
\quad\text{for every }f\in\mathcal O_{C,q},
$$

where the residues are the canonical $k$-valued functionals (and the condition may equivalently
be tested after scalar extension). Thus sections are regular differentials on the normalization
allowed simple poles over nodes, with opposite residues on the two geometric branches. At a
node, (10.1) shows that this module is free of rank one. Away from the nodes, normalization is an
isomorphism and (10.4) is the ordinary canonical bundle.

The local calculation identifies the completed stalk with the expected rank-one adjunction
module. In the completed split local ring,
write a pair with at most simple poles as

$$
\left(a(x)\frac{dx}{x},\,b(y)\frac{dy}{y}\right).
$$

The residue condition is $a(0)+b(0)=0$. Put $g(y)=-b(y)$; then
$a(0)=g(0)$, so $(a(x),g(y))$ is an element of
$k[[x,y]]/(xy)\subset k[[x]]\oplus k[[y]]$, and the displayed pair is that element times
$\theta$ from (10.1). Conversely every multiple of $\theta$ has opposite residues. Hence the
right side of (10.4) has the expected completed adjunction stalk at every node and the ordinary
canonical stalk elsewhere. Coherent sheaves on a noetherian curve are detected by these completed
stalks. Embedding independence and adjunction from Section 9 identify these stalks with those
of $\omega_C$; this proves (10.4), and descent gives the
nonsplit case.

In the split situation there is an exact sequence

$$
0\longrightarrow\nu_*\omega_{\widetilde C}
\longrightarrow\omega_C
\xrightarrow{\operatorname{res}}
\bigoplus_q k_q
\longrightarrow0, \tag{10.5}
$$

where the displayed residue may be taken on either branch, the other being its negative. Surjectivity is local: multiples of (10.1) realize any residue. Globally, the individual component residue theorems impose relations on global sections, exactly matching cycles in the dual graph.

Without a chosen splitting, replace $k_q$ in (10.5) by the one-dimensional residue line obtained
by descending the anti-diagonal branch residues. It is dual, under finite local duality, to the
discrepancy line $Q_q$ above. No orientation of the branches is needed for the descended exact
sequence; only an identification of its last line with $\kappa(q)$ requires such a choice.

For a reduced curve with more general singularities one must make one further correction over an
imperfect field. Its normalization is regular but need not be smooth, so
$\Omega^1_{\widetilde C/k}$ need not be the normalization's dualizing line. Let
$\mathfrak c=\operatorname{Ann}_{\mathcal O_C}
(\nu_*\mathcal O_{\widetilde C}/\mathcal O_C)$ be the conductor. Its extension to the regular
curve $\widetilde C$ is an invertible ideal and cuts out an effective Cartier divisor
$D_{\mathfrak c}$. For the finite part of this divisor over $q$, Cartier adjunction identifies

$$
\omega_{\widetilde C/k}(D_{\mathfrak c})/
\omega_{\widetilde C/k}
\simeq
\mathcal Hom_k(\mathcal O_{D_{\mathfrak c}},k).
$$

This is the zero-dimensional case (9.7) of Theorem 9.1 applied to the proper curve $\widetilde C$
and the skyscraper $\mathcal O_{D_{\mathfrak c}}$, combined with the connecting map of
$0\to\mathcal O(-D_{\mathfrak c})\to\mathcal O\to\mathcal O_{D_{\mathfrak c}}\to0$ tensored with
$\omega_{\widetilde C/k}$; when $\widetilde C$ is smooth over $k$ it is Theorem 8.7 and the
functional below is $\operatorname{Res}$ itself.
Evaluation at $1$ defines the local residue even when the residue fields are inseparable. The
precise Rosenlicht formula is

$$
\omega_C=
\left\{
\eta\in\nu_*\omega_{\widetilde C/k}(D_{\mathfrak c}):
\sum_{p\mapsto q}\operatorname{Res}_p(f\eta)=0
\text{ for every }q\in C\text{ and }f\in\mathcal O_{C,q}
\right\}. \tag{10.5a}
$$

To prove this locally, write $A\subset\widetilde A$ and $Q=\widetilde A/A$. The conductor kills
$Q$, so all relevant polar functionals are detected on the conductor thickenings. Applying
$\operatorname{Hom}_A(-,\omega_A)$ to $0\to A\to\widetilde A\to Q\to0$, finite duality
identifies $\operatorname{Hom}_A(\widetilde A,\omega_A)$ with $\omega_{\widetilde A}$ and local
duality identifies $\operatorname{Ext}^1_A(Q,\omega_A)$ with $\operatorname{Hom}_k(Q,k)$.
The resulting exact sequence identifies
$\omega_A/\omega_{\widetilde A}$ with $\operatorname{Hom}_k(Q,k)$. On the other hand Cartier
adjunction identifies the conductor-bounded polar quotient with
$\operatorname{Hom}_k(\widetilde A/\mathfrak c,k)$, under which the class of $\eta$ evaluates
$f$ as $\sum_{p\mapsto q}\operatorname{Res}_p(f\eta)$. Dualizing
$0\to A/\mathfrak c\to\widetilde A/\mathfrak c\to Q\to0$ identifies
$\operatorname{Hom}_k(Q,k)$ with the annihilator of $A/\mathfrak c$. Thus this annihilator is
exactly $\omega_A/\omega_{\widetilde A}$, proving (10.5a). The resulting sheaf need not be
invertible when the curve is not Gorenstein. When the normalization is smooth, in particular for
the geometrically nodal curves under discussion, $\omega_{\widetilde C/k}$ is
$\Omega^1_{\widetilde C/k}$ and this recovers (10.4). At a split rational node, testing $f=1$
gives the opposite-residue rule and the other tests enforce no additional condition.

### 10.4 Families of nodal curves

If $f:C\to S$ is a proper flat nodal curve
that is a relative local complete intersection, then $\omega_{C/S}$ is a line bundle, commutes
with arbitrary base change, and restricts on every geometric fiber to the sheaf in (10.4). This
is the stable replacement for $\Omega^1_{C/S}$.

A simultaneous normalization need not exist over an arbitrary base: normalizing the total space can fail to normalize every fiber after base change. Consequently the branch-and-residue description should be used fiberwise unless a simultaneous normalization is part of the hypotheses. Since the family is assumed relative local complete intersection, the adjunction calculation of Section 9.4 already proves that $\omega_{C/S}$ is invertible; this subsection does not use a local normal form that has not yet been proved.

The next subsection independently proves that, after strict-henselian base change and completion at
a node, the family has the form

$$
xy=a
$$

with $a$ in the maximal ideal of the completed base. Once proved, that presentation gives the
useful completed frame $dx/x=-dy/y$ for the already constructed adjunction line. It is a
consequence and a coordinate description, not an input to the assertion above. The stronger
étale-local statement, that the family is étale locally cut out by $xy=a$ in a smooth relative
surface, is not proved here and is nowhere used here. For the families in which it is first
genuinely consumed, namely regular total spaces over a discrete valuation ring, where the
smoothing parameter is forced to be the uniformizer, it is established later in the collection
in Book 21, Theorem 19.2, by an elementary argument that needs no approximation theory.

If sections mark smooth points $p_1,\ldots,p_n$, then

$$
\omega_{C/S}(p_1+\cdots+p_n)
$$

allows simple poles at the markings as well as the implicit branch poles at nodes. A global section has total residue zero on each geometric fiber, with node residues cancelling internally. This is the differential package used for degenerating pointed curves.

### 10.5 The completed local model at a node

The preceding section used a local normal form for a node in a family. That normal form is neither part of the definition of a nodal family nor a consequence of the fiberwise picture alone: it is an assertion about the total space, and it must be proved. This section proves it in the form the later theory actually consumes, namely after completion over a strictly henselian base, and marks precisely the stronger étale-local assertion that is _not_ proved here.

Throughout the section $\Lambda$ is a noetherian complete local ring with maximal ideal $\mathfrak m$ and residue field $k$, and $S=\operatorname{Spec}\Lambda$ with closed point $s$. Let

$$
f:X\longrightarrow S
$$

be flat and locally of finite type, and let $x\in X_s$ be a closed point of the closed fiber at which

$$
\kappa(x)=k,
\qquad
\widehat{\mathcal O}_{X_s,x}\simeq k[[u,v]]/(uv). \tag{10.6}
$$

Condition (10.6) says that the fiber has an ordinary node at $x$ whose two branches are individually defined. No separate hypothesis of relative dimension one is required: (10.6) supplies it near $x$. When $k$ is separably closed, (10.6) is exactly the condition that the geometric fiber have an ordinary double point over $x$. Indeed a geometric node has reduced geometric local ring, so $\kappa(x)\otimes_k\bar k$ is reduced, $\kappa(x)/k$ is separable, and therefore $\kappa(x)=k$; and the algebra of branches of an ordinary double point is finite étale of degree two over the residue field, hence split when that field is separably closed. Separable closedness enters nowhere else: what the proof uses is that the node is split.

Write $B=\widehat{\mathcal O}_{X,x}$. It is a noetherian complete local ring with residue field $k$, and it is flat over $\Lambda$, because $\mathcal O_{X,x}$ is $\Lambda$-flat by flatness of $f$ and the completion of a noetherian local ring is faithfully flat over it. Moreover $B/\mathfrak mB\simeq\widehat{\mathcal O}_{X_s,x}$, since completion commutes with the quotient $\mathcal O_{X,x}\to\mathcal O_{X,x}/\mathfrak m\mathcal O_{X,x}=\mathcal O_{X_s,x}$ and the induced topology on the quotient is its maximal-adic one.

**Theorem 10.5 (completed local model at a node).** With the hypotheses above there exist an element $a\in\mathfrak m$ and an isomorphism of $\Lambda$-algebras

$$
\widehat{\mathcal O}_{X,x}\;\simeq\;\Lambda[[u,v]]/(uv-a), \tag{10.7}
$$

which reduces modulo $\mathfrak m$ to the presentation (10.6) of the fiber. Moreover the ideal $a\Lambda$ depends only on the $\Lambda$-algebra $\widehat{\mathcal O}_{X,x}$, so $a$ is unique up to multiplication by a unit of $\Lambda$.

**Why a complete base with separably closed residue field costs nothing.** Let $S$ be an arbitrary locally noetherian scheme, $f:X\to S$ flat and locally of finite type, $s\in S$, and let $\bar x$ be a geometric point of $X_s$ at which the geometric fiber has an ordinary node. Let $\bar s$ be the induced geometric point of $S$ and put

$$
\Lambda=\widehat{\mathcal O^{\mathrm{sh}}_{S,\bar s}},
$$

the completion of a strict henselization; it is a noetherian complete local ring whose residue field is the separable closure of $\kappa(s)$, hence separably closed. This is the ring written $\widehat{\mathcal O}^{\,\mathrm{unr}}_{S,s}$ in the applications. Base change along $\operatorname{Spec}\Lambda\to S$ preserves flatness and local finite presentation, and the closed fiber of $X_\Lambda=X\times_S\operatorname{Spec}\Lambda$ is $X_s\otimes_{\kappa(s)}\kappa(s)^{\mathrm{sep}}$, which has an ordinary split node at the point $x$ determined by $\bar x$. So the theorem applies to $X_\Lambda\to\operatorname{Spec}\Lambda$ at $x$, and produces the smoothing parameter $a\in\mathfrak m_\Lambda$ that all later uses refer to. In the only case used in this collection the base is a discrete valuation ring $R$, henselian by convention, and $\Lambda=\widehat{R^{\mathrm{sh}}}$ is a complete discrete valuation ring; since $R\to\Lambda$ is unramified, a uniformizer of $R$ remains one in $\Lambda$ and the normalized valuation of $a$ is unaffected by the passage.

The proof of the theorem occupies the rest of the section. It has three ingredients: a completeness lemma allowing the passage to the limit, the fact that a flat family truncates to flat families over the Artinian quotients of the base, and a single square-zero deformation step in which the whole ambiguity of the node collapses onto one scalar.

**Lemma (ideal-adic completeness).** Let $C$ be a noetherian local ring, complete for its maximal ideal $\mathfrak n$, and let $J\subseteq\mathfrak n$ be any ideal. Then the natural map $C\to\varprojlim_nC/J^n$ is an isomorphism.

_Proof._ Injectivity holds because $\bigcap_nJ^n\subseteq\bigcap_n\mathfrak n^n=0$: applied to the
finite module $M=C$ over the complete noetherian local ring $C$, Lemma 13.1(1) of Book 1 gives
$\bigcap_n\mathfrak n^n=0$ and the completeness of $C$ for the $\mathfrak n$-adic topology.
For surjectivity, take a compatible system and lift it to a sequence $(c_N)$
in $C$ with $c_{M}-c_{N}\in J^{N}$ for $M\geq N$. Since
$J^N\subseteq\mathfrak n^N$, the sequence is Cauchy for the $\mathfrak n$-adic topology and
converges to some $c\in C$. Each ideal $J^N$ is closed in that topology: the quotient $C/J^N$ is
again a complete noetherian local ring by Lemma 13.2 of Book 1, so Lemma 13.1(1) of Book 1 applied
to it gives $\bigcap_m\bigl(\mathfrak n^m(C/J^N)\bigr)=0$, that is
$\bigcap_m(J^N+\mathfrak n^m)=J^N$. As $c-c_N\in J^N+\mathfrak n^m$ for every $m$, we get
$c-c_N\in J^N$, so $c$ maps to the given system. $\square$

Applied to $C=B$ and $J=\mathfrak mB$, the lemma says that $B$ is recovered from its truncations $B_n=B/\mathfrak m^{n+1}B$. Applied to $C=\Lambda[[u,v]]/(uv-a)$, which is a quotient of the complete local noetherian ring $\Lambda[[u,v]]$ and hence again complete local noetherian, it says the same for the model. This is the only role of completeness of the base, and it is the reason the theorem is stated after completion rather than for $\mathcal O_{X,x}$ itself.

**Flatness of the truncations.** Put $\Lambda_n=\Lambda/\mathfrak m^{n+1}$ and $B_n=B/\mathfrak m^{n+1}B=B\otimes_\Lambda\Lambda_n$. Since $B$ is flat over $\Lambda$, each $B_n$ is flat over $\Lambda_n$: flatness is preserved by base change. This elementary step is where the flatness hypothesis on $f$ is consumed, and it is indispensable. Without it the conclusion fails outright: if $\mathfrak m\neq0$ and $X=\operatorname{Spec}k[u,v]/(uv)$ is viewed as an $S$-scheme through $\Lambda\to k$, then $X$ is locally of finite type with nodal closed fiber, yet $\widehat{\mathcal O}_{X,x}=k[[u,v]]/(uv)$ is killed by $\mathfrak m$ and so cannot have the form (10.7). Every model $\Lambda[[u,v]]/(uv-a)$ with $a\in\mathfrak m$ is indeed $\Lambda$-flat: the relation $uv=a$ rewrites each monomial $u^iv^j$ with $i,j\geq1$ as $a^{\min(i,j)}$ times a pure power, the resulting rearrangement converges because $a\in\mathfrak m$ and $\Lambda$ is complete, and the ring is thereby identified as a $\Lambda$-module with $\Lambda[[u]]\oplus v\Lambda[[v]]$, which is flat over the noetherian ring $\Lambda$ because $\Lambda[u]\to\Lambda[[u]]$ is an adic completion of a noetherian ring.

**Lemma (one square-zero step).** Let $A'\to A$ be a surjection of noetherian local rings with kernel $I$ satisfying $\mathfrak m_{A'}I=0$, and write $k=A'/\mathfrak m_{A'}$, so $I$ is a finite-dimensional $k$-vector space and $I^2=0$. Let $B'$ be a noetherian complete local $A'$-algebra, flat over $A'$, with residue field $k$, and suppose given an isomorphism of $A$-algebras

$$
\psi:A[[u,v]]/(uv-a)\;\xrightarrow{\ \sim\ }\;B:=B'/IB'
$$

for some $a\in\mathfrak m_A$. Then there exist $a'\in\mathfrak m_{A'}$ lifting $a$ and an isomorphism of $A'$-algebras

$$
\psi':A'[[u,v]]/(uv-a')\;\xrightarrow{\ \sim\ }\;B'
$$

whose reduction modulo $I$ is $\psi$.

_Proof._ Write $U_0=\psi(u)$ and $V_0=\psi(v)$; these lie in $\mathfrak m_B$, so they admit lifts $U,V\in\mathfrak m_{B'}$, the maximal ideal of $B'$ being the preimage of $\mathfrak m_B$. Because $B'$ is $\mathfrak m_{B'}$-adically complete, substitution of $U$ and $V$ defines a continuous $A'$-algebra homomorphism $\Phi:A'[[u,v]]\to B'$. Its reduction modulo $I$ is surjective, since $\psi$ is. Hence $B'=C+IB'$ with $C=\operatorname{im}\Phi$, and therefore $IB'=I(C+IB')=IC+I^2B'=IC\subseteq C$, so $B'=C$ and $\Phi$ is surjective. No Nakayama argument is needed; the square-zero hypothesis does the work.

Next, flatness identifies the kernel of $B'\to B$. The multiplication map $I\otimes_{A'}B'\to B'$ is injective with image $IB'$ because $B'$ is $A'$-flat, and $I$ is a $k$-vector space, so

$$
IB'\;\simeq\;I\otimes_{A'}B'\;\simeq\;I\otimes_k\bigl(B'/\mathfrak m_{A'}B'\bigr)\;\simeq\;I\otimes_kB_0,
\qquad
B_0=k[[u,v]]/(uv),
$$

the last identification because $a\in\mathfrak m_A$, so reducing $\psi$ modulo $\mathfrak m_{A'}$ gives $B'/\mathfrak m_{A'}B'\simeq k[[u,v]]/(uv)$. Two consequences: every element of $IB'$ is uniquely $\sum_i\epsilon_ig_i(u,v)$ for a fixed $k$-basis $\epsilon_1,\ldots,\epsilon_r$ of $I$ and uniquely determined $g_i\in B_0$; and for $\epsilon\in I$ and $\gamma\in B'$ the product $\epsilon\gamma$ depends only on the image of $\gamma$ in $B_0$.

Fix any lift $\tilde a\in\mathfrak m_{A'}$ of $a$. The element $w=UV-\tilde a$ of $B'$ dies in $B$, so $w\in IB'$ and we may write

$$
UV-\tilde a=\sum_{i=1}^r\epsilon_ig_i(u,v),
\qquad
g_i\in k[[u,v]]/(uv).
$$

Now use the vector-space decomposition $k[[u,v]]/(uv)=k\oplus u\,k[[u]]\oplus v\,k[[v]]$ and write $g_i=c_i+u\,p_i(u)+v\,q_i(v)$ with $c_i\in k$. Correct the coordinates by

$$
U'=U-\sum_i\epsilon_i\,q_i(v),
\qquad
V'=V-\sum_i\epsilon_i\,p_i(u),
$$

where each coefficient is interpreted in $B_0$, which is legitimate by the previous paragraph. Because $I^2=0$, the cross term vanishes and

$$
U'V'=UV-U\sum_i\epsilon_ip_i(u)-V\sum_i\epsilon_iq_i(v)
=UV-\sum_i\epsilon_i\bigl(u\,p_i(u)+v\,q_i(v)\bigr),
$$

the products again being computed in $B_0$, where the images of $U$ and $V$ are $u$ and $v$. Therefore

$$
U'V'=\tilde a+\sum_i\epsilon_ic_i=:a',
$$

and $a'$ lies in $A'$, indeed in $\mathfrak m_{A'}$, because $\sum_i\epsilon_ic_i\in I\subseteq\mathfrak m_{A'}$ and $\tilde a\in\mathfrak m_{A'}$. It reduces to $a$ modulo $I$.

The point of the computation is that a coordinate change $u\mapsto u+\epsilon\alpha$, $v\mapsto v+\epsilon\beta$ alters the product $uv$ by $\epsilon(u\beta+v\alpha)$, and the image of the map $(\alpha,\beta)\mapsto u\beta+v\alpha$ on $B_0$ is exactly the maximal ideal $(u,v)B_0=u\,k[[u]]\oplus v\,k[[v]]$, since $uv=0$ kills all cross terms. Thus a coordinate change can absorb every part of $g_i$ except its constant term, and precisely one scalar per basis vector of $I$ survives, to be added to the smoothing parameter. Equivalently, the ambiguity space of the node is the one-dimensional space $k[[u,v]]/(uv,u,v)=k$; this single dimension is the reason the normal form has exactly one parameter and no moduli.

Since $U'\equiv U$ and $V'\equiv V$ modulo $IB'$, the elements $U',V'$ still lift $\psi(u),\psi(v)$, and the same argument as above shows that the substitution homomorphism $\Phi':A'[[u,v]]\to B'$ sending $u\mapsto U'$, $v\mapsto V'$ is surjective. It kills $uv-a'$, hence induces a surjection

$$
\psi':R'=A'[[u,v]]/(uv-a')\longrightarrow B'
$$

whose reduction modulo $I$ is $\psi$. Let $J=\ker\psi'$. Tensoring $0\to J\to R'\to B'\to0$ with $A=A'/I$ and using $\operatorname{Tor}^{A'}_1(B',A)=0$, which holds because $B'$ is $A'$-flat, gives an exact sequence

$$
0\longrightarrow J/IJ\longrightarrow A[[u,v]]/(uv-a)\xrightarrow{\ \psi\ }B\longrightarrow0 .
$$

As $\psi$ is an isomorphism, $J=IJ$, and then $J=IJ=I^2J=0$. So $\psi'$ is an isomorphism. $\square$

_Proof of Theorem 10.5, existence._ Apply the lemma inductively along the truncations of the base. Set $\Lambda_n=\Lambda/\mathfrak m^{n+1}$ and $B_n=B/\mathfrak m^{n+1}B$, which is flat over $\Lambda_n$ and, being a quotient of the complete local noetherian ring $B$, is itself complete local noetherian with residue field $k$. For $n=0$ we have $\Lambda_0=k$, $a_0=0$, and $\psi_0$ the isomorphism (10.6). Given $\psi_n:\Lambda_n[[u,v]]/(uv-a_n)\to B_n$ with $a_n\in\mathfrak m\Lambda_n$, apply the lemma to

$$
A'=\Lambda_{n+1},
\qquad
A=\Lambda_n,
\qquad
I=\mathfrak m^{n+1}/\mathfrak m^{n+2},
\qquad
B'=B_{n+1},
$$

noting that $\mathfrak m_{A'}I=\mathfrak m^{n+2}/\mathfrak m^{n+2}=0$, that $I$ is a finite-dimensional $k$-vector space because $\Lambda$ is noetherian, and that $B_{n+1}\otimes_{\Lambda_{n+1}}\Lambda_n=B_n$. The lemma produces $a_{n+1}\in\mathfrak m\Lambda_{n+1}$ lifting $a_n$ and an isomorphism $\psi_{n+1}$ reducing to $\psi_n$.

The systems are compatible by construction, so $a=\varprojlim a_n$ exists in $\Lambda=\varprojlim\Lambda_n$ and lies in $\mathfrak m$, and $\varprojlim\psi_n$ is an isomorphism

$$
\varprojlim_n\Lambda_n[[u,v]]/(uv-a_n)\;\xrightarrow{\ \sim\ }\;\varprojlim_nB_n .
$$

By the completeness lemma the right-hand side is $B$, and the left-hand side is $\Lambda[[u,v]]/(uv-a)$: this ring is complete local noetherian, and its quotient by $\mathfrak m^{n+1}$ is $\Lambda_n[[u,v]]/(uv-a_n)$. This proves (10.7), and the construction started from (10.6), so the isomorphism reduces to the given presentation of the fiber. $\square$

**Proposition (the smoothing ideal is intrinsic).** Let $\Lambda$ be a noetherian complete local ring and let $a,a'\in\mathfrak m$. If $\Lambda[[u,v]]/(uv-a)$ and $\Lambda[[u,v]]/(uv-a')$ are isomorphic as $\Lambda$-algebras, then $a\Lambda=a'\Lambda$. More precisely, if $B=\Lambda[[u,v]]/(uv-a)$ then

$$
a\Lambda=\ker\Bigl(\Lambda\longrightarrow B\big/\operatorname{Fitt}_1\widehat\Omega^1_{B/\Lambda}\Bigr),
$$

a construction depending only on the $\Lambda$-algebra $B$.

_Proof._ For the topologically finitely presented complete local $\Lambda$-algebras occurring
here, let $\widehat\Omega^1_{B/\Lambda}$ be the module of continuous differentials, equivalently
the inverse limit of the finite-level differential modules. This avoids treating the usually
nonfinite ordinary differential module of a power-series ring as finite. The continuous module is
finite and intrinsic: a $\Lambda$-algebra isomorphism of complete noetherian local rings carries
the maximal ideal to the maximal ideal, is continuous, and transports continuous derivations.
Fitting ideals are independent of a finite presentation, so
$\operatorname{Fitt}_1\widehat\Omega^1_{B/\Lambda}$ is intrinsic.

Now compute it for $B=\Lambda[[u,v]]/(uv-a)$. Continuous differentials of a formal
power-series ring are free,
$\widehat\Omega^1_{\Lambda[[u,v]]/\Lambda}=\Lambda[[u,v]]\,du\oplus
\Lambda[[u,v]]\,dv$. At every Artinian quotient the conormal sequence is right exact; taking
the inverse limit preserves this presentation because all transition maps are surjective. Thus,
writing $F=uv-a$, the continuous conormal sequence gives

$$
B\xrightarrow{\ (v,\;u)\ }B\,du\oplus B\,dv\longrightarrow\widehat\Omega^1_{B/\Lambda}\longrightarrow0,
$$

because $d(uv-a)=v\,du+u\,dv$; the term $da$ is absent since $a\in\Lambda$ and the differentials are relative. The first Fitting ideal is generated by the $1\times1$ minors of the presentation matrix, so $\operatorname{Fitt}_1\widehat\Omega^1_{B/\Lambda}=(u,v)B$, and

$$
B/(u,v)B=\Lambda[[u,v]]/(uv-a,u,v)=\Lambda/a\Lambda .
$$

Hence the kernel of $\Lambda\to B/\operatorname{Fitt}_1\widehat\Omega^1_{B/\Lambda}$ is
$a\Lambda$. In a local ring two nonzero generators of the same principal ideal differ by a
unit: if $a=ra'$ and $a'=sa$, then $(1-rs)a=0$, and $rs$ cannot lie in the maximal ideal unless
$a=0$. The zero case is immediate. This proves both assertions. $\square$

Geometrically, $\operatorname{Fitt}_1\widehat\Omega^1$ cuts out the locus where the relative differentials fail to be generated by a single element; for the model it is the closed subscheme $V(u,v)$, the locus carrying the singularity, and the proposition says that this locus maps isomorphically onto the closed subscheme $\operatorname{Spec}\Lambda/a\Lambda$ of the base. The ideal $a\Lambda$ therefore records exactly the base directions along which the node persists. Two consequences are what later books need. First, when $\Lambda$ is a complete discrete valuation ring with uniformizer $\pi$, the integer

$$
n=\operatorname{length}_\Lambda\bigl(\Lambda/a\Lambda\bigr)=v(a)
$$

depends only on the family and the node, not on the coordinates used to write (10.7); writing
$a=\pi^n\cdot(\text{unit})$ and rescaling $u$ by that unit puts the model in the form
$\Lambda[[u,v]]/(uv-\pi^n)$. In this discrete-valuation, hence domain, situation $a\ne0$
exactly when the node is smoothed over the generic point, while $a=0$ means that the singularity
propagates over the whole base. Over a general complete local ring there may be several minimal
primes, and the correct statement is componentwise: the node smooths over precisely those generic
points at which the image of $a$ is nonzero. This is the well-definedness that thickness requires.

**Remark (the étale-local refinement).** The normal form proved above is a statement about completed local rings. The stronger statement usually quoted, that there are an étale neighborhood $U\to X$ of $x$ and an étale $S$-morphism

$$
U\longrightarrow\operatorname{Spec}\Lambda[u,v]/(uv-a)
$$

carrying $x$ to the origin, so that the family is étale locally the hypersurface $uv=a$ in a
smooth relative surface, is _not_ proved here. Deducing it from (10.7) is an approximation
problem: one has an isomorphism over the completion and wants to realize it over an étale
neighborhood, which is the content of Artin approximation and requires excellence hypotheses on
the base. Artin approximation is not developed in this collection. The completed form is used
in place of it everywhere in this book, and this suffices: the arguments that invoke the local model, in
the completed-frame discussion above and the later theory of nodal degenerations test freeness, length, and
valuation, all of which are detected on completed stalks. Where the étale form would genuinely
be needed is in producing an actual open or étale neighborhood with the displayed equation, for
instance to construct global charts or to descend a formal isomorphism to a morphism of schemes;
no argument in this book does that.

Two cases should be kept apart. For a general flat family over a general complete local base, with
$a$ an arbitrary element of $\mathfrak m$, the étale-local refinement remains unproved in this
collection, and nothing anywhere relies on it. For the special case that the later semistable theory
actually needs — the base a discrete valuation ring, the total space regular, so that the smoothing
parameter has valuation one — the refinement is a theorem, proved in Book 21, Theorem 19.2. The
proof there does not descend the formal isomorphism (10.7) at all, and so needs neither approximation
nor excellence: regularity makes the local ring of the total space a two-dimensional regular local
ring in which the uniformizer has a leading quadratic form with two independent linear factors, and
splitting that form is the extraction of a simple root of a monic quadratic, hence a standard étale
extension. The present remark is therefore a statement about the scope of this section, not a
permanent limitation of the theory; nothing proved here uses anything from a later book.

## 11. Riemann--Roch over a field

### 11.1 The theorem and its meaning

Let $X$ be a smooth proper geometrically connected curve of genus $g$ over $k$, and let $\mathcal L$ be a line bundle of degree $d$. Riemann--Roch states

$$
\chi(X,\mathcal L)=d+1-g. \tag{11.1}
$$

Equivalently, after choosing a canonical divisor $K$ and a divisor $D$ for $\mathcal L$,

$$
\ell(D)-\ell(K-D)=\deg D+1-g, \tag{11.2}
$$

where $\ell(D)=\dim_k H^0(X,\mathcal O_X(D))$. The second form uses the duality theorem already
proved in Section 9.2 to identify $h^1(\mathcal O(D))$ with $\ell(K-D)$; no later residue
description enters the proof. The first form is logically independent
of duality and remains valid, with
degree defined by Euler characteristic, for proper curves; on regular curves the divisor
calculation below identifies it with the usual divisor degree.

Riemann--Roch says that each unit of degree contributes one unit to the Euler characteristic. It
does not say that $h^0$ itself always grows by one: a new allowed pole can instead remove an
obstruction in $H^1$. The correction term $\ell(K-D)$ measures this
**speciality**. Once $d>2g-2$, its degree is negative, it vanishes, and the naive count becomes
exact:

$$
h^0(X,\mathcal L)=d+1-g.
$$

### 11.2 Proof by adding points

We first prove the Euler-characteristic form without duality. Every line bundle is represented by a divisor. If $D$ is an effective Cartier divisor, (5.3) gives

$$
\chi(\mathcal O_X(D))-\chi(\mathcal O_X)
=\chi(\mathcal O_D(D)).
$$

The sheaf $\mathcal O_D(D)$ is invertible as an $\mathcal O_D$-module, so its $k$-dimension is the length of $D$:

$$
\chi(\mathcal O_D(D))
=\sum_x n_x[\kappa(x):k]=\deg D.
$$

For a general divisor write $D=D_+-D_-$ with disjoint effective parts. Apply the effective calculation first to $D_+$ and then to the exact sequence obtained by subtracting $D_-$. Additivity of Euler characteristic gives

$$
\chi(\mathcal O_X(D))=\deg D+\chi(\mathcal O_X).
$$

Since $\chi(\mathcal O_X)=1-g$, this is (11.1).

This proof reveals why regularity was convenient: it represented every line bundle by a difference of effective point divisors. On a singular Gorenstein curve one can instead use the definition (5.2), for which (11.1) is immediate once degree is defined. The nontrivial content then shifts to identifying degree with Cartier divisors and proving duality.

### 11.3 Consequences and examples

A line bundle of negative degree has no nonzero section. Indeed a nonzero section defines an effective divisor and hence has nonnegative degree. This uses integrality; on a reducible curve a line bundle of negative total degree can have a section supported on components where its degree is positive.

Apply the duality theorem of Section 9.2 to
$D=0$. Since
$\ell(0)=1$,

$$
h^0(X,\omega_X)=g. \tag{11.3}
$$

Applying it to $D=K$ gives

$$
\deg K=2g-2. \tag{11.4}
$$

For $X=\mathbf P^1$, $g=0$ and

$$
h^0(\mathcal O(n))=
\begin{cases}
n+1,&n\geq0,\\
0,&n<0,
\end{cases}
$$

while $h^1(\mathcal O(n))=\max\{-n-1,0\}$. This realizes every term in (11.2). For genus one, $\omega_X$ has degree zero and a nonzero section, hence is trivial. For $g\geq2$, the canonical bundle has positive degree and its sections define the canonical linear system.

If $\deg\mathcal L\geq2g$, then $\mathcal L$ is globally generated. For any closed geometric point $p$, duality applied to $\mathcal L(-p)$ gives

$$
H^1(X,\mathcal L(-p))^\vee
\simeq H^0(X,\omega_X\otimes\mathcal L^{-1}(p))=0
$$

because the latter degree is at most $-1$. The evaluation map at $p$ is therefore surjective. If $\deg\mathcal L\geq2g+1$, the same argument with every length-two divisor proves that sections separate points and tangent directions, so $\mathcal L$ is very ample. These bounds connect Riemann--Roch to the projective embeddings of Book 8.

### 11.4 Gorenstein and nodal curves

Let $C$ be a proper geometrically connected Gorenstein curve over $k$, pure of dimension one,
and let $g=p_a(C)$. Lemma 9.1A makes $C$ projective. Consequently a rational Cartier divisor
can be cleared by an effective one: after twisting $\mathcal O(D)$ by a high power of an ample
bundle, Serre generation and homogeneous prime avoidance (the finite-field-safe argument of Book
8) supply a section regular at every associated point; do the same for that ample power itself.
The two zero divisors express $D$ up to a principal divisor as a difference of effective Cartier
divisors. The length
calculation of Section 5.2 now proves that the Euler-characteristic degree is additive on
$\operatorname{Pic}(C)$ and agrees with Cartier-divisor degree. The Euler-characteristic
identity, which is independent of duality, is

$$
\chi(C,\mathcal L)=\deg\mathcal L+1-g, \tag{11.5}
$$

and duality gives

$$
h^0(C,\mathcal L)-h^0(C,\omega_C\otimes\mathcal L^{-1})
=\deg\mathcal L+1-g. \tag{11.6}
$$

Moreover $\deg\omega_C=2g-2$. Indeed duality exchanges $H^0(\omega_C)$ with
$H^1(\mathcal O_C)^\vee$ and $H^1(\omega_C)$ with $H^0(\mathcal O_C)^\vee$, so
$\chi(\omega_C)=-\chi(\mathcal O_C)$; the Euler-characteristic definition of degree gives the
formula. For a connected nodal curve, normalization makes the formula visible. Tensor (10.2) by
$\mathcal L$ and take Euler characteristics. Each node subtracts one from $\chi$, while gluing
component constants produces the graph contribution in (10.3). Applying ordinary
Riemann--Roch on normalized components and adding yields (11.5). The opposite-residue description
yields the dual term.

On a reducible curve, negative total degree does not force vanishing. A section may vanish identically on some components, so its zero is a zero-divisor rather than a Cartier divisor. A safe vanishing criterion is componentwise: if $\mathcal L$ has negative degree on every irreducible component of a reduced connected curve, then $H^0(C,\mathcal L)=0$. More refined inequalities must account for nodes where a nonzero componentwise section is forced to vanish.

## 12. Serre duality

### 12.1 The residue pairing

The absolute theorem of Section 9.2 proves perfectness and trace functoriality. The residue
formulas below identify that pairing concretely.

Riemann--Roch counts the difference between functions and obstructions. Serre duality identifies those obstructions as linear functionals given by differentials. Let $X$ be a smooth proper geometrically connected curve and $D$ a divisor. Choose an affine cover $X=U\cup V$ such that the relevant poles lie in $U\setminus V$. A class in $H^1(X,\mathcal O_X(D))$ is represented by a rational function $g$ on $U\cap V$, modulo functions extending to either side.

For $\eta\in H^0(X,\omega_X(-D))$, define

$$
\langle[g],\eta\rangle
=\sum_{x\in X\setminus V}\operatorname{Res}_x(g\eta). \tag{12.1}
$$

Changing $g$ by a function regular on $U$ contributes residues of a regular differential. Changing it by a function on $V$ changes the chosen partial sum by the negative of its complement; the residue theorem (Theorem 8.8) makes the total zero. Thus (12.1) is well defined. In sheaf language it is cup product followed by trace:

$$
H^1(X,\mathcal O_X(D))
\times H^0(X,\omega_X(-D))
\longrightarrow H^1(X,\omega_X)
\xrightarrow{\operatorname{tr}}k. \tag{12.2}
$$

### 12.2 Perfectness

The pairing is perfect:

$$
H^1(X,\mathcal O_X(D))^\vee
\simeq H^0(X,\omega_X(-D)). \tag{12.3}
$$

This is the degree-zero consequence of the proved isomorphism (9.6), not a dimension count.
That the trace furnished by (9.6) agrees with the residue trace of (12.2) is not an extra
assumption: it was proved in Theorem 8.8, where the functionals $R_x$ obtained by composing
$\operatorname{tr}$ with the principal-part description (8.4a) of $H^1(X,\Omega^1_{X/k})$ were
identified with the canonical residues $\operatorname{Res}_x$ of Section 8.3. Formula
(9.6), applied to $\mathcal F=\mathcal O_X(D)$, is therefore precisely (12.3), and the pairing it
induces is (12.1).

The usual divisor devissage makes the mechanism explicit. For a closed point $p$, compare

$$
0\to\mathcal O_X(D)\to\mathcal O_X(D+p)\to\mathcal Q_p\to0
$$

with its dual triangle against $\omega_X[1]$. Local duality identifies the dual of the
zero-dimensional quotient $\mathcal Q_p$ with its principal-part residue functional. The two
long exact cohomology sequences are therefore transposes. The global calculation (9.6) supplies
the initial comparison; adding or removing closed points one at a time and using the
two-out-of-three property recovers the same pairing in divisor language. This comparison does
not assume Riemann--Roch.

The decisive local calculation, over a rational point, is

$$
\left(t^{-1}k\right)\times(k\,dt)\longrightarrow k,
\qquad (a/t,b\,dt)\longmapsto ab.
$$

At a nonrational point the local principal-part quotient is paired with
$\operatorname{Hom}_k(\kappa(p),k)$ as in (8.1), and evaluation supplies the perfect $k$-pairing.
When $\kappa(p)/k$ is separable this is the familiar field-trace formula; in the inseparable case
the finite dualizing module replaces the degenerate field trace. Thus no perfection assumption on
$k$ is hidden.

### 12.3 Duality for line bundles and vector bundles

For a line bundle $\mathcal L$,

$$
H^1(X,\mathcal L)^\vee
\simeq H^0(X,\mathcal L^{-1}\otimes\omega_X),
\qquad
H^0(X,\mathcal L)^\vee
\simeq H^1(X,\mathcal L^{-1}\otimes\omega_X). \tag{12.4}
$$

For a vector bundle $\mathcal E$,

$$
H^i(X,\mathcal E)^\vee
\simeq H^{1-i}(X,\mathcal E^\vee\otimes\omega_X),
\qquad i=0,1. \tag{12.5}
$$

These formulas are the two cohomology degrees of (9.6). For a vector bundle, internal Hom into
$\omega_X$ is $\mathcal E^\vee\otimes\omega_X$ and its higher sheaf Ext groups vanish. For an
arbitrary coherent sheaf $\mathcal F$, the precise form is instead

$$
H^i(X,\mathcal F)^\vee
\simeq \operatorname{Ext}^{1-i}_X(\mathcal F,\omega_X).
$$

The Ext term cannot generally be replaced by cohomology of a sheaf dual when $\mathcal F$ has torsion. On a proper Cohen--Macaulay curve the same statement holds with its dualizing sheaf; if the curve is Gorenstein, (12.4)--(12.5) retain their line-bundle form.

### 12.4 Functoriality

By the finite-morphism theorem (9.8), if $\pi:Y\to X$ is finite between proper
Cohen--Macaulay curves, there is a trace

$$
\pi_*\omega_Y\longrightarrow\omega_X
$$

characterized, in the finite case, by

$$
\pi_*\omega_Y\simeq
\mathcal Hom_X(\pi_*\mathcal O_Y,\omega_X).
$$

Evaluation at $1$ gives the trace. On smooth generically separable curves this recovers the trace of rational differentials and (8.5). Pullback of functions and trace of differentials are adjoint:

$$
\langle \pi^*\alpha,\eta\rangle_Y
=\langle\alpha,\operatorname{Tr}_\pi\eta\rangle_X.
$$

Likewise, maps of vector bundles induce transpose maps on cohomology after dualizing and twisting by $\omega$. This transposition principle later controls correspondences on curves.

## 13. Relative Riemann--Roch and cohomology in families

### 13.1 A two-term model

**Theorem 13.1 (perfect pushforward and base change).** Let $f:X\to S$ be proper, flat, and
finitely presented with one-dimensional fibers, let $S$ be locally noetherian, and let
$\mathcal E$ be a vector bundle on $X$. Then $Rf_*\mathcal E$ is perfect of Tor-amplitude
$[0,1]$, and the canonical map

$$
Lg^*Rf_*\mathcal E\longrightarrow Rf'_*Lg'^*\mathcal E
$$

is an isomorphism for every base change $g:S'\to S$.

**Proof.** Work over an affine neighborhood $U=\operatorname{Spec}A$. The proper-curve
complex lemma proved inside Lemma 9.2A applies directly to the base-flat sheaf $\mathcal E$.
It gives a bounded finite projective complex $K^\bullet$ representing $Rf_*\mathcal E$ such
that $K^\bullet\otimes_A B$ represents the derived pushforward after every $A\to B$. This
use is independent of the projective embedding subsequently constructed in Lemma 9.2A; in
particular Theorem 13.1 is not being used circularly to prove that embedding.

Every fiber has coherent cohomology only in degrees $0$ and $1$. We now shorten
$K^\bullet$ without losing base-change compatibility. Starting at its left end, fiberwise
vanishing says that the endpoint differential is injective on every residue-field fiber.
The cokernel is base-flat by the Tor criterion in the relative syzygy lemma, and the injection
is therefore universally injective. Here both adjacent terms are finite projective
$A$-modules, so the cokernel is finitely presented as well as flat, hence finite projective.
The resulting short exact sequence consequently splits locally (equivalently, a suitable
maximal minor becomes a unit). Replace the adjacent term by this projective cokernel and
repeat. At the right end use the dual argument for a fiberwise
surjection. After shrinking $U$, all terms outside degrees $0,1$ have been eliminated without
changing any derived base change. Shrinking once more makes the two remaining finite projective
modules free. Thus there are finite free $A$-modules $K^0,K^1$
and a map

$$
d:K^0\longrightarrow K^1 \tag{13.1}
$$

such that, for every $A$-algebra $B$, the cohomology of $\mathcal E_B$ on $X_B$ is computed by

$$
K^0\otimes_A B\longrightarrow K^1\otimes_A B. \tag{13.2}
$$

Tensoring this matrix with any $A$-algebra computes the base-changed cohomology. This proves
perfectness, Tor-amplitude, and arbitrary derived base change simultaneously. No descent of
chosen matrices is required: $Rf_*\mathcal E$ and its canonical base-change morphism are already
global derived objects, while being perfect of a fixed Tor-amplitude is local on the base. On an
overlap the two matrices are merely quasi-isomorphic representatives of that same object; they
need not be uniquely chain-isomorphic. $\square$

The model is stronger than a fiberwise dimension statement. It records every specialization by one matrix with entries in $A$. It is exactly the cohomological amount demanded by dimension one.

### 13.2 Semicontinuity and base change

From (13.2),

$$
H^0(X_B,\mathcal E_B)=\ker(d\otimes B),\qquad
H^1(X_B,\mathcal E_B)=\operatorname{coker}(d\otimes B). \tag{13.3}
$$

The function $s\mapsto h^0(X_s,\mathcal E_s)$ is upper semicontinuous because a bound on matrix rank is cut out by minors. Since

$$
\chi(X_s,\mathcal E_s)=\operatorname{rank}K^0-\operatorname{rank}K^1,
$$

$h^1$ is upper semicontinuous as well.

There are natural maps

$$
(f_*\mathcal E)\otimes\kappa(s)\longrightarrow
H^0(X_s,\mathcal E_s), \tag{13.4}
$$

$$
(R^1f_*\mathcal E)\otimes\kappa(s)\longrightarrow
H^1(X_s,\mathcal E_s). \tag{13.5}
$$

In the present perfect two-term situation, (13.5) is an isomorphism because cokernels commute with tensor product. The first can fail because kernels need not commute with tensor product. Near $s$, the following conditions are equivalent: (13.4) is universally an isomorphism; $R^1f_*\mathcal E$ is locally free; and $h^1(X_t,\mathcal E_t)$ is locally constant. Then $f_*\mathcal E$ is also locally free and both terms commute with arbitrary base change.

In particular, if $H^1(X_s,\mathcal E_s)=0$ for every $s$, then $R^1f_*\mathcal E=0$ and $f_*\mathcal E$ is locally free with arbitrary base change. This is the workhorse that turns fiberwise vanishing into a vector bundle of sections.

### 13.3 Relative Riemann--Roch

Assume that the geometric fibers are connected and reduced of constant arithmetic genus $g$. For
a line bundle $\mathcal L$ of relative degree $d$,

$$
\chi(X_s,\mathcal L_s)=d+1-g \tag{13.6}
$$

for every $s$. Theorem 13.1 expresses $d$ as the difference of two locally constant virtual
ranks, so both $d$ and $g$ are locally constant and the formula is interpreted component by
component on $S$.

For a vector bundle $\mathcal E$ of rank $r$, put $\deg\mathcal E=\deg\det\mathcal E$. Then

$$
\chi(X_s,\mathcal E_s)=\deg(\mathcal E_s)+r(1-g). \tag{13.7}
$$

We include the reduction to line bundles. A reduced pure curve is Cohen--Macaulay, and the
projectivity and clearing argument of Section 11.4 applies without the Gorenstein hypothesis; thus
Euler-characteristic degree is additive on the Picard group of each fiber. It is enough to extend the fiber field to an algebraic
closure, since cohomology dimensions, determinant, and degree are unchanged by that extension.
Choose an effective divisor $D$ so positive on every component that $\mathcal E(D)$ is generated
by global sections. If $r>1$, a section can be chosen nonzero at every point. Indeed, in the
incidence variety of pairs $(s,x)$ with $s(x)=0$, the fibers over $x$ have codimension $r$ in the
section space; since the curve has dimension one, its image is a proper closed subset. Such a
section is a subbundle inclusion. After untwisting, it gives

$$
0\longrightarrow\mathcal O_X(-D)
\longrightarrow\mathcal E
\longrightarrow\mathcal E'\longrightarrow0,
$$

where $\mathcal E'$ is a vector bundle of rank $r-1$ and
$\det\mathcal E'=\det\mathcal E\otimes\mathcal O_X(D)$. Induction on $r$, additivity of Euler
characteristic, and the line-bundle formula give

$$
\begin{aligned}
\chi(\mathcal E)
&=(-\deg D+1-g)
 +(\deg\det\mathcal E+\deg D+(r-1)(1-g))\\
&=\deg\det\mathcal E+r(1-g).
\end{aligned}
$$

The incidence argument works component by component on any reduced projective curve, so it covers
every fiber considered here. The finite free model has virtual rank equal to the right side.
The numerical identity itself is fiberwise and was proved independently of the model. Neither
$h^0$ nor $h^1$ need be constant separately; their jumps
cancel.

### 13.4 Useful vanishing ranges

Fiberwise Serre duality supplies the vanishing below, and the two-term theorem turns it into a
statement over the base.

Let $f:X\to S$ be a smooth proper curve with geometrically connected fibers of genus $g$. If
$\deg(\mathcal L_s)>2g-2$ on every geometric fiber, duality and negative-degree vanishing give

$$
R^1f_*\mathcal L=0.
$$

Consequently $f_*\mathcal L$ is locally free of rank $d+1-g$ and commutes with arbitrary base change. Degree at least $2g$ makes the evaluation map $f^*f_*\mathcal L\to\mathcal L$ surjective; degree at least $2g+1$ separates every length-two divisor and gives a relative projective embedding.

For nodal or reducible fibers, a total-degree bound alone is insufficient. A bundle may be very
negative on one component and very positive on another. A useful sufficient condition is

$$
\deg(\mathcal L_s|_Z)>
2p_a(Z)-2
$$

for every nonempty connected union $Z$ of irreducible components of every geometric fiber,
including the whole fiber. To prove the claim, suppose a nonzero section of
$\omega_{X_s}\otimes\mathcal L_s^{-1}$ exists and let $Z$ be a connected component of the union
of components on which it is not identically zero. At every boundary branch of $Z$, gluing to
the zero section on the complementary component forces one zero. Since

$$
\deg(\omega_{X_s}|_Z)=2p_a(Z)-2+\#\partial Z,
$$

the induced nonzero section on $Z$ has degree
$2p_a(Z)-2-\deg(\mathcal L_s|_Z)$ after those boundary zeros are removed. The displayed
inequality makes this negative, a contradiction. Duality gives $H^1=0$. Any application using
reducible fibers must verify such componentwise control or prove vanishing separately.

## 14. Relative duality and base change

### 14.1 Trace and the relative pairing

We now combine the relative duality theorem of Section 9.3 with the perfect-pushforward theorem
of Section 13.1.

Let $f:X\to S$ be a proper flat finitely presented Gorenstein relative curve with geometrically
reduced fibers over a locally noetherian scheme. This includes the smooth and nodal families of
the standing conventions. Relative duality supplies

$$
\operatorname{tr}_f:R^1f_*\omega_{X/S}\longrightarrow\mathcal O_S.
$$

For a vector bundle $\mathcal E$, multiplication and trace give

$$
R^1f_*\mathcal E\ \times\
f_*(\mathcal E^\vee\otimes\omega_{X/S})
\longrightarrow\mathcal O_S. \tag{14.1}
$$

This identifies

$$
f_*(\mathcal E^\vee\otimes\omega_{X/S})
\simeq(R^1f_*\mathcal E)^\vee. \tag{14.2}
$$

Locally, if $K^0\to K^1$ computes $\mathcal E$, then the transpose dual map with degrees reversed computes $\mathcal E^\vee\otimes\omega_{X/S}$. This is the precise algebra beneath relative Serre duality.

If the cohomology sheaves are locally free, (14.1) is a perfect pairing of vector bundles and also

$$
(f_*\mathcal E)^\vee
\simeq R^1f_*(\mathcal E^\vee\otimes\omega_{X/S}). \tag{14.3}
$$

Fiberwise these are the pairings of Chapter 12.

### 14.2 The base-change theorem

The arbitrary-base-change statement here was proved from the dual resolution in Section 9.3;
it is not merely a consequence of transposing the cohomology matrix. Under these hypotheses, for
$T\to S$,

$$
\omega_{X/S}|_{X_T}\simeq\omega_{X_T/T},
$$

and the pullback of $\operatorname{tr}_f$ is the trace for $X_T/T$. The finite free model makes
their effect on cohomology explicit: its matrix
pulls back by tensoring, its dual matrix is the transpose, and transposition and evaluation
commute with tensor product.

Suppose all geometric fibers are connected and reduced. Then $f_*\mathcal O_X\simeq\mathcal O_S$, compatibly with base change. Duality yields

$$
R^1f_*\omega_{X/S}\simeq\mathcal O_S, \tag{14.4}
$$

through the trace, and

$$
f_*\omega_{X/S}\simeq(R^1f_*\mathcal O_X)^\vee. \tag{14.5}
$$

Indeed, fiberwise $h^0(\mathcal O)=1$, while constancy of Euler characteristic makes $h^1$
locally constant. Section 13.2 therefore makes both pushforwards locally free and base-change
compatible; the unit $\mathcal O_S\to f_*\mathcal O_X$ is an isomorphism on every fiber and hence
an isomorphism. When the genus is constant, both sides of (14.5) are locally free of rank $g$ and
commute with arbitrary base change.

### 14.3 The Hodge bundle in smooth and nodal families

For a proper smooth family with geometrically connected fibers of genus $g$, the **Hodge bundle** is

$$
\mathbb E=f_*\Omega^1_{X/S}=f_*\omega_{X/S}.
$$

It is locally free of rank $g$, with fiber $H^0(X_s,\Omega^1_{X_s/\kappa(s)})$. For a proper
nodal Gorenstein family with geometrically connected fibers of constant arithmetic genus $g$,
the correct definition is still

$$
\mathbb E=f_*\omega_{X/S}.
$$

Its fiber consists of normalization differentials with opposite residues at the branches of each node. Its rank is the arithmetic genus, not merely the sum of the genera of normalized components. Differential forms with node poles account for cycles in the dual graph.

In a smoothing, $f_*\Omega^1_{X/S}$ can acquire torsion or fail base change, whereas $f_*\omega_{X/S}$ is the locally free extension selected by duality. This is why integral families use dualizing differentials.

### 14.4 Failure modes

Each hypothesis has a visible role.

- Without properness, cohomology need not be finite and residue traces acquire boundary terms.

- Without flatness, fiber dimension and arithmetic genus may jump, and specialization of the dualizing sheaf can fail.

- Without the Cohen--Macaulay condition, duality need not be concentrated in one sheaf.

- Without the Gorenstein condition, the dualizing sheaf may not be invertible; canonical Cartier divisors then need not exist.

- Without geometric connectedness, $f_*\mathcal O_X$ has more than one geometric summand, so (14.4) must be replaced by its dual.

- Without locally constant cohomology dimensions, individual pushforwards may fail to be locally free even though the two-term object stays perfect.

These are not technical decorations. The cusp exposes non-smooth differentials, a curve with an embedded point exposes failure of Cohen--Macaulayness, and a reducible curve with unbalanced multidegree exposes failure of total-degree vanishing.

## 15. Divisor and differential tools for later geometry

### 15.1 Abel maps before the Picard scheme

The universal divisor on $X\times_S X^{(d)}$ defines, functorially in $T$,

$$
D\longmapsto\mathcal O_{X_T}(D).
$$

Once the degree-$d$ relative Picard functor is represented, this becomes the Abel map

$$
a_d:X^{(d)}\longrightarrow\operatorname{Pic}^d_{X/S}. \tag{15.1}
$$

Even before representability, its fibers are concrete. On a smooth integral fiber, two divisors
have the same image exactly when they are linearly equivalent. With the quotient convention for
projective bundles fixed in Book 8, the fiber over $\mathcal L$ is
$\mathbf P(H^0(X,\mathcal L)^\vee)$ when sections exist: it parametrizes one-dimensional
subspaces of sections. By Serre duality, for $d>2g-2$ this dimension is constantly
$d-g$, preparing the projective-bundle description used in Picard theory.

### 15.2 The infinitesimal Abel map

Let $X$ be a smooth proper curve over $k$ and $D$ an effective divisor of degree $d$. First-order deformations of $D$ inside $X$ are sections of its normal bundle:

$$
T_DX^{(d)}\simeq H^0(D,\mathcal O_D(D)). \tag{15.2}
$$

Indeed an embedded deformation of the quotient
$\mathcal O_X\twoheadrightarrow\mathcal O_D$ over $k[\epsilon]/(\epsilon^2)$ is obtained by
changing its ideal through an $\mathcal O_X$-linear map
$\mathcal I_D\to\mathcal O_D$. Two changes give the same deformation exactly when the maps
agree. Since $\mathcal I_D=\mathcal O_X(-D)$, this Hom group is
$H^0(D,\mathcal O_D(D))$. Book 8 identifies the length-$d$ Hilbert functor with $X^{(d)}$, so
this calculation also covers nonreduced divisors.

The tangent space to the degree-zero Picard object at the identity is $H^1(X,\mathcal O_X)$.
Indeed a line bundle on $X\times\operatorname{Spec}k[\epsilon]/(\epsilon^2)$ reducing to the
trivial bundle has transition functions $1+\epsilon f_{ij}$. The cocycle condition says that the
$f_{ij}$ form an additive Cech $1$-cocycle, and changing trivializations adds a coboundary. The
differential of (15.1) is the connecting map in

$$
0\longrightarrow\mathcal O_X
\longrightarrow\mathcal O_X(D)
\longrightarrow\mathcal O_D(D)
\longrightarrow0:
$$

$$
da_D:
H^0(D,\mathcal O_D(D))
\xrightarrow{\delta_D}H^1(X,\mathcal O_X). \tag{15.3}
$$

To check the sign, trivialize $\mathcal O_X(D)$ and lift the infinitesimal normal section on each
member of an affine cover. On an overlap, the difference of two lifts is a regular function; the
Cech cocycle of these differences is exactly the displayed boundary. It is also the first-order
change of the transition functions of $\mathcal O_X(D)$, so the convention
$D\mapsto\mathcal O_X(D)$ introduces no minus sign.

Its transpose under Serre duality is
restriction:

$$
H^0(X,\omega_X)
\longrightarrow H^0(D,\omega_X|_D). \tag{15.4}
$$

The proof pairs a principal part representing the displacement with a differential and takes its residue. At $D=dp$, the source of (15.3) and target of (15.4) retain jets through order $d-1$.

### 15.3 A formal-immersion criterion

For a finite-type morphism $\varphi:Y\to Z$ and a $k$-rational point $x$ mapping to $z$, call $\varphi$ a **formal immersion at $x$** if

$$
\widehat{\mathcal O}_{Z,z}\longrightarrow
\widehat{\mathcal O}_{Y,x}
$$

is surjective. This implies surjectivity on cotangent spaces, equivalently injectivity on tangent
spaces. Conversely, suppose the residue fields agree and the cotangent map is surjective. Choose
lifts in $\mathfrak m_{Z,z}$ of generators of
$\mathfrak m_{Y,x}/\mathfrak m_{Y,x}^2$. Nakayama says their images generate
$\mathfrak m_{Y,x}$. Induction on $n$ then shows that
$\mathcal O_{Z,z}\to\mathcal O_{Y,x}/\mathfrak m_{Y,x}^n$ is surjective for every $n$: degree
$n$ monomials in the chosen lifts generate the next associated-graded piece. Taking inverse
limits and using noetherian completeness gives the required surjection of completed local rings.

For the Abel map at $D$, the following three conditions are equivalent:

1. its tangent map is injective;
2. the boundary map $\delta_D$ is injective;
3. the restriction map

   $$
   H^0(X,\omega_X)\longrightarrow H^0(D,\omega_X|_D)
   $$

   is surjective.

When the Picard target exists with the stated tangent space, these conditions give a formal immersion. Necessarily $d\leq g$. For distinct rational points, restriction evaluates differentials at them; for $D=dp$, it evaluates their first $d$ power-series coefficients.

The three-way statement also holds on a nodal fiber when $D$ lies in
the smooth locus and $\omega_X$ is the dualizing sheaf. Opposite node residues ensure that the
residue comparison has no extra boundary term. This is the exact criterion later
used to turn equality of Abel images into equality in a formal neighborhood.

### 15.4 A reusable theorem package

**Divisors.** On a regular noetherian integral scheme whose local rings have dimension at most two -- in particular on a regular curve and on the regular total space of a relative curve over a Dedekind base -- Cartier and Weil divisors agree, by Proposition 3.1. On a proper regular integral curve, divisor classes equal line-bundle classes, principal divisors have degree zero, and

$$
\deg D=\sum_x n_x[\kappa(x):k]
=\chi(\mathcal O(D))-\chi(\mathcal O).
$$

On singular or reducible curves, Cartier divisors remain valid, while conversion from cycles requires separate justification.

**Families.** For a projective flat relative curve and a line bundle, fiberwise degree and Euler characteristic are locally constant. A relative effective Cartier divisor finite flat of rank $d$ has degree $d$ on every fiber. For a smooth projective relative curve these divisors are represented by $X^{(d)}$, with a universal divisor compatible with base change.

**Differentials and duality.** By Sections 9.2--9.3, smooth families have
$\omega_{X/S}=\Omega^1_{X/S}$. Proper flat Gorenstein nodal
families have invertible, base-change-compatible $\omega_{X/S}$; on a nodal fiber its sections
are normalization differentials with simple branch poles and opposite residues. For a vector
bundle,

$$
f_*(\mathcal E^\vee\otimes\omega_{X/S})
\simeq(R^1f_*\mathcal E)^\vee,
$$

with perfect fiberwise Serre duality.

**Nodes in families.** Over a noetherian complete local base $\Lambda$ with separably closed residue field, a flat family of finite type with a split ordinary node in its closed fiber has completed local ring $\Lambda[[u,v]]/(uv-a)$ with $a$ in the maximal ideal, and the ideal $a\Lambda$ is intrinsic, being the ideal defining the image of the non-smooth locus. Over a complete discrete valuation ring this makes $v(a)$ an invariant of the family at the node. The étale-local refinement of the normal form is not proved here.

**Residues.** On a smooth integral curve over any field, including one with inseparable residue
extensions at closed points, there is a canonical $k$-linear residue $\operatorname{Res}_x$
(Theorem 8.5) which kills regular and exact differentials, which identifies
$\Omega^1_{X/k}(nx)/\Omega^1_{X/k}$ with $\operatorname{Hom}_k(\mathcal O_{nx},k)$ perfectly
(Theorem 8.7), which sums to zero on a proper curve (Theorem 8.8), and which satisfies the local
trace formula (8.5) for a finite separable map (Theorem 8.9). Residues commute with extension of the
base field in the form (8.1c).

**Proper pushforward and Stein factorization.** For a proper morphism $f:X\to Y$ with $Y$ locally
noetherian, $f_*\mathcal O_X$ is a coherent $\mathcal O_Y$-algebra and the factorization
$X\to\operatorname{\mathbf{Spec}}_Y(f_*\mathcal O_X)\to Y$ has a proper surjective first factor with
connected nonempty fibers and $\mathcal O$-trivial pushforward, and a finite second factor
(Theorem 9.3). If $f_*\mathcal O_X=\mathcal O_Y$, every fiber of $f$ is connected; if $X$ is
reduced, integral, or normal, so is the intermediate scheme. A proper birational morphism onto a
normal integral base satisfies $f_*\mathcal O_X=\mathcal O_Y$ and therefore has connected fibers
(Corollary 9.4).

**Cohomology and infinitesimals.** By Section 13.1,
cohomology is locally a two-term finite free model, fiber dimensions are upper semicontinuous,
and fiberwise $H^1$-vanishing gives a locally free pushforward with arbitrary base change.
At an effective divisor,

$$
T_DX^{(d)}=H^0(D,\mathcal O_D(D));
$$

the Abel differential is a cohomology boundary. Its transpose restricts
dualizing differentials to $D$.

### 15.5 Conclusion

Divisors begin as local equations, but on curves they become a global organizing principle. Regularity converts equations into codimension-one cycles. Rational sections convert cycles into line bundles. Properness forces principal divisors to have degree zero, while flatness makes degree survive specialization. Smoothness identifies finite flat points with Cartier divisors and lets symmetric powers carry their universal family.

Differentials reveal the second half of the story. Residues are invariant local coefficients whose
global sum vanishes, and at a node the two branches contribute opposite residues. The local
Rosenlicht module is invertible even when ordinary differentials fail. It is the dualizing
sheaf, turns $H^1$ into the dual of global differentials, and gives Riemann--Roch its symmetric
form. Perfect pushforward shows that the
relative pairing is encoded by a two-term finite model and respects specialization and base
change.

Moving a divisor produces a principal part; its Abel class is the resulting cohomology boundary;
a global differential tests that boundary by a residue. The resulting
perfect pairing reduces the formal-immersion test to an explicit restriction map on
differentials. The chain

$$
\text{points and jets}
\longrightarrow\text{divisors}
\longrightarrow\text{line bundles}
\longrightarrow\text{cohomology}
\longleftrightarrow\text{differentials}
$$

is the divisor-and-duality toolkit carried forward to Picard schemes, modular curves, and formal-immersion arguments.
