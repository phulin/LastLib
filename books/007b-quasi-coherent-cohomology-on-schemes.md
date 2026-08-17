# Quasi-coherent Cohomology on Schemes

A scheme is assembled from spectra of rings, and the sheaves that carry geometric information are
assembled in the same way from modules. Such a sheaf is called quasi-coherent. On a single affine
piece it is nothing but a module, and every question about it is a question of commutative algebra;
what is genuinely global is the gluing. Cohomology is the exact measurement of that gluing. It
answers, in a computable way, whether locally defined sections patch, whether a surjection of
sheaves is surjective on sections, and how the answers vary when the base ring is changed.

This book supplies that measurement in the generality later volumes need, and it does so with no
noetherian hypothesis where none is required. Three facts organize everything. First, on an affine
scheme a quasi-coherent sheaf has no higher cohomology: the failure of gluing is entirely a global
phenomenon. Second, because an affine cover of a separated scheme has affine intersections, one
finite Čech complex of modules computes all cohomology of a quasi-coherent sheaf at once. Third,
that complex consists of modules over the base ring and is functorial in the base, so change of
coefficients, flat base change, passage to filtered colimits, and vanishing bounds all become
statements about a single finite complex.

Book 7a built the homological apparatus: derived functors on complexes bounded below, the
acyclic-resolution criterion, hypercohomology, the two spectral sequences of a first-quadrant
double complex, and an abstract comparison theorem identifying Čech and derived cohomology when the
members of a cover are acyclic. The present book supplies the geometric input that theorem
requires, and then applies it. Nothing here is imported from a later volume, and no result about
proper morphisms — coherence of higher direct images, semicontinuity, base-change criteria, formal
functions — is used or proved; those belong to the theory of proper families and are developed
where properness is available.

The last three chapters exist to serve concrete computations. Chapter 6 works out
$H^i(\mathbf P^r_A,\mathcal O(n))$ for every $i$ and every $n$ over an arbitrary ring, by splitting
the Čech complex of the standard cover into one summand for each Laurent monomial and recognizing
each summand as the cochain complex of a simplex. Chapter 7 proves two theorems of graded algebra —
Hilbert's syzygy theorem and Grothendieck's generic freeness lemma — that belong with projective
cohomology because they are what turns a fiberwise computation into a statement over a base.
Chapter 8 records the resulting interface.

## Contents

- [1. Modules, sheaves, and unimodular families](#1-modules-sheaves-and-unimodular-families)
  - [1.1 What this book supplies](#11-what-this-book-supplies)
  - [1.2 Conventions and imported machinery](#12-conventions-and-imported-machinery)
  - [1.3 The extended Čech complex of a unimodular family](#13-the-extended-čech-complex-of-a-unimodular-family)
- [2. Quasi-coherent sheaves](#2-quasi-coherent-sheaves)
  - [2.1 The sheaf attached to a module](#21-the-sheaf-attached-to-a-module)
  - [2.2 Quasi-coherence and its local character](#22-quasi-coherence-and-its-local-character)
  - [2.3 Kernels, cokernels, extensions, and pullback](#23-kernels-cokernels-extensions-and-pullback)
  - [2.4 Pushforward along quasi-compact morphisms](#24-pushforward-along-quasi-compact-morphisms)
- [3. Cohomology of quasi-coherent sheaves](#3-cohomology-of-quasi-coherent-sheaves)
  - [3.1 Flasque sheaves and functorial resolutions](#31-flasque-sheaves-and-functorial-resolutions)
  - [3.2 Čech complexes and the comparison spectral sequence](#32-čech-complexes-and-the-comparison-spectral-sequence)
  - [3.3 Serre's affine vanishing theorem](#33-serres-affine-vanishing-theorem)
- [4. Čech models on separated schemes](#4-čech-models-on-separated-schemes)
  - [4.1 Alternating and ordered complexes](#41-alternating-and-ordered-complexes)
  - [4.2 The finite affine Čech model](#42-the-finite-affine-čech-model)
  - [4.3 Higher direct images and dimension bounds](#43-higher-direct-images-and-dimension-bounds)
- [5. Base change, colimits, and vanishing](#5-base-change-colimits-and-vanishing)
  - [5.1 Coefficient change and flat base change](#51-coefficient-change-and-flat-base-change)
  - [5.2 Cohomology and filtered colimits](#52-cohomology-and-filtered-colimits)
  - [5.3 Grothendieck's vanishing theorem](#53-grothendiecks-vanishing-theorem)
- [6. The cohomology of projective space](#6-the-cohomology-of-projective-space)
  - [6.1 Projective space and its twisting sheaves](#61-projective-space-and-its-twisting-sheaves)
  - [6.2 The complete computation](#62-the-complete-computation)
  - [6.3 Freeness, base change, and the top pairing](#63-freeness-base-change-and-the-top-pairing)
- [7. Graded algebra for projective methods](#7-graded-algebra-for-projective-methods)
  - [7.1 Hilbert's syzygy theorem](#71-hilberts-syzygy-theorem)
  - [7.2 Generic freeness](#72-generic-freeness)
- [8. Synthesis](#8-synthesis)
  - [8.1 The reusable package](#81-the-reusable-package)
  - [8.2 Conclusion](#82-conclusion)

## 1. Modules, sheaves, and unimodular families

### 1.1 What this book supplies

A module over a ring is a rigid object: it has no local behavior, because the ring has no
geometry of its own until one agrees to view its prime ideals as points. A sheaf on a scheme is
the opposite: it is defined by local data, and the interesting questions about it are questions of
assembly. Quasi-coherent sheaves are exactly the sheaves that are modules locally and sheaves
globally. Every construction performed on them may be checked on affine pieces, where it is
commutative algebra, and every obstruction to performing a construction globally is measured by
one invariant, cohomology.

It is worth being precise about what obstruction means here, because it is the reason cohomology
is unavoidable rather than merely convenient. Suppose $\mathcal F\to\mathcal G$ is a surjection of
sheaves. Surjectivity is a statement about stalks; it says that every section of $\mathcal G$ lifts
locally. Whether a _global_ section of $\mathcal G$ lifts globally is a different question. Choose
lifts on the members of a cover; on each overlap the two lifts differ by a section of the kernel
$\mathcal K$; those differences satisfy a cocycle identity, and modifying the chosen lifts changes
them by a coboundary. The resulting class in $H^1(X,\mathcal K)$ vanishes if and only if the
section lifts. Higher degrees record the same phenomenon one stage further out: a class in
$H^p$ is a discrepancy among discrepancies. If one wants such classes to be computable, one needs
two things: a class of sheaves for which the local pieces are transparent, and covers on which the
local pieces are acyclic so that the naive cocycle calculation is the right answer. The whole of
this book grows from those two requirements.

Three theorems do the work. The first is Serre's affine vanishing theorem: a quasi-coherent sheaf
on an affine scheme has no cohomology in positive degrees. This is the statement that a module has
no local behavior, in cohomological form. The second is the Čech model: on a quasi-compact
separated scheme, an affine open cover has affine intersections, so the finite Čech complex built
from that cover computes all cohomology. The third is the computation of the cohomology of the
twisting sheaves on projective space, which is the one nontrivial example from which every later
projective vanishing theorem is bootstrapped.

The Čech model is not only a computational device; it is the reason the later theory has content
over a base. The complex it produces is a finite complex of modules over the base ring, it is
functorial in that ring, and its terms are flat whenever the sheaf is. Consequently, statements
that would otherwise require delicate arguments — that cohomology commutes with flat base change,
that it commutes with filtered colimits, that it vanishes above a bound depending only on the size
of a cover, that it may be represented after base change by one matrix — all reduce to visible
properties of that finite complex. Chapters 4 and 5 exploit exactly this.

Two boundaries are deliberate. First, no noetherian hypothesis is imposed where none is needed:
affine vanishing, the Čech model, coefficient change, and the projective computation hold over an
arbitrary commutative ring, because later applications base-change to rings that are not
noetherian. Noetherian hypotheses appear only in Chapter 5, where dimension enters, and in
Chapter 7, where finiteness is the subject. Second, nothing about proper morphisms is proved here.
Coherence of higher direct images, semicontinuity, the theorem on formal functions, and the exact
criteria for cohomology to commute with arbitrary base change require properness and belong to the
theory of proper families; this book stops at the general machinery that such a theory takes for
granted.

### 1.2 Conventions and imported machinery

All rings are commutative with identity. For a ring $A$ we write $\operatorname{Spec}A$ for its
prime spectrum with the Zariski topology, and

$$
D(f)=\{\mathfrak p\in\operatorname{Spec}A: f\notin\mathfrak p\}
$$

for the principal open attached to $f\in A$. The sets $D(f)$ form a basis closed under finite
intersection, $D(f)\cap D(g)=D(fg)$, each $D(f)$ is quasi-compact, and the canonical
homeomorphism $\operatorname{Spec}A_f\simeq D(f)$ identifies the structure sheaf of $D(f)$ with
that of $\operatorname{Spec}A_f$. A family $f_1,\ldots,f_n\in A$ is called **unimodular** if it
generates the unit ideal, equivalently if the $D(f_i)$ cover $\operatorname{Spec}A$.

Schemes are locally ringed spaces admitting an open cover by affine schemes; no separatedness or
finiteness is built into the definition. A morphism $f:X\to Y$ is **quasi-compact** if the preimage
of every quasi-compact open is quasi-compact, **quasi-separated** if the diagonal
$\Delta_f:X\to X\times_YX$ is quasi-compact, **separated** if $\Delta_f$ is a closed immersion, and
**affine** if the preimage of every affine open of $Y$ is affine. A scheme is quasi-compact,
quasi-separated, or separated when it is so over $\operatorname{Spec}\mathbf Z$. We use repeatedly
the elementary fact that a scheme $X$ is separated if and only if for every pair of affine opens
$U,V\subseteq X$ the intersection $U\cap V$ is affine and
$\mathcal O(U)\otimes\mathcal O(V)\to\mathcal O(U\cap V)$ is surjective; and that it suffices to
check this on the members of one affine open cover.

For a topological space $X$ we write $\mathrm{Ab}(X)$ for the category of sheaves of abelian
groups and, for a ringed space $(X,\mathcal O_X)$, $\mathrm{Mod}(\mathcal O_X)$ for the category of
$\mathcal O_X$-modules. Both are Grothendieck abelian categories with enough injectives. Sheaf
cohomology is the right derived functor of global sections,

$$
H^p(X,\mathcal F)=R^p\Gamma(X,\mathcal F),
$$

computed in $\mathrm{Ab}(X)$. Section 3.1 shows that the derived functors computed in
$\mathrm{Mod}(\mathcal O_X)$ agree with these, so the notation is unambiguous; until that point,
cohomology means the abelian-sheaf version. Short exact sequences of sheaves give long exact
cohomology sequences, functorially.

The homological apparatus is imported from Book 7a and is used exactly as stated there. We use:
the construction of right-derived functors on complexes with cohomology bounded below, together
with the acyclicity criterion that a bounded-below resolution by $F$-acyclic objects computes $RF$
(7a, Sections 3.4 and 3.7); the definitions of $R\Gamma$, $Rf_*$, and $H^n$ (7a, Section 4.1);
totalization of a double complex and its two spectral sequences, both strongly convergent in the
first quadrant (7a, Sections 7.1 and 7.2); hypercohomology and its spectral sequences (7a,
Section 7.3); the abstract Čech comparison theorem, which identifies Čech and derived cohomology
for a finite cover whose sheafified augmented Čech complex is exact and whose finite intersections
are acyclic (7a, Section 7.4); and the composition theorem producing the Leray spectral sequence
under the hypothesis that direct images of injectives are acyclic (7a, Section 8.1). Chapter 3
supplies the geometric hypotheses these results require; no statement of Book 7a is used outside
the range for which it was proved there.

From commutative algebra we assume standard material: localization and its exactness, flat and
faithfully flat modules, the local nature of exactness, Nakayama's lemma, the Hilbert basis
theorem, prime filtrations of finite modules over noetherian rings, Noether normalization, and the
elementary theory of graded rings and modules. Complexes are cohomological, with differentials
raising degree, following the conventions of Book 7a, Section 1.3.

### 1.3 The extended Čech complex of a unimodular family

Everything in Chapters 2 and 3 rests on a single algebraic identity, which we isolate here because
it will be used three times over in different disguises: to prove that the module construction of
Section 2.1 produces a sheaf, to prove Serre's affine vanishing theorem in Section 3.3, and — with
the unimodularity hypothesis deliberately removed — to compute the cohomology of projective space
in Section 6.2. The identity says that a module can be reconstructed from its localizations at a
unimodular family, together with all the higher coherence data, and that no further information is
hidden in the higher terms.

Fix a ring $A$, a finite family $\underline f=(f_1,\ldots,f_n)$ of elements of $A$, and an
$A$-module $M$. For a subset $I\subseteq\{1,\ldots,n\}$ put $f_I=\prod_{i\in I}f_i$, with
$f_\varnothing=1$, and write $M_{f_I}$ for the localization of $M$ at the multiplicative set
generated by $f_I$; thus $M_{f_\varnothing}=M$. Localizing twice is localizing once,
$(M_{f_I})_{f_J}=M_{f_{I\cup J}}$, so all the natural maps below are unambiguous.

**Definition.** The **Čech complex** $\check C^\bullet(\underline f,M)$ has

$$
\check C^p(\underline f,M)=\prod_{\substack{I\subseteq\{1,\ldots,n\}\\ |I|=p+1}}M_{f_I}
\qquad(p\ge0),
$$

and differential $d:\check C^{p}\to\check C^{p+1}$ given on the component indexed by
$I=\{i_0<\cdots<i_{p+1}\}$ by

$$
(d\sigma)_I=\sum_{k=0}^{p+1}(-1)^k\,\sigma_{I\setminus\{i_k\}}\big|_{M_{f_I}},
$$

the bar denoting the canonical localization map. The **extended Čech complex**
$\check C_{\mathrm{ext}}^\bullet(\underline f,M)$ is obtained by placing $M$ in degree $-1$ and
using the localization maps $M\to M_{f_i}$ as the differential in degree $-1$. A direct
computation gives $d\circ d=0$ in every degree, for the usual reason: each term
$\sigma_{I\setminus\{i_k,i_l\}}$ occurs twice with opposite signs.

The complex is small enough to write out for $n=2$. It reads

$$
0\longrightarrow M\longrightarrow M_{f_1}\times M_{f_2}
\longrightarrow M_{f_1f_2}\longrightarrow 0,
$$

with the last map the difference of the two localization maps. If $f_1,f_2$ generate the unit
ideal, exactness in the middle says that a pair of sections agreeing on the overlap comes from a
unique global section, and exactness on the right says that the overlap is not overdetermined.
These are precisely the two halves of a sheaf axiom for a two-element cover, plus the assertion
that nothing obstructs the gluing in higher degree.

**Theorem 1.1 (unimodular exactness).** Let $f_1,\ldots,f_n\in A$ generate the unit ideal and let
$M$ be any $A$-module. Then the extended Čech complex

$$
0\longrightarrow M\longrightarrow\prod_{i}M_{f_i}
\longrightarrow\prod_{i<j}M_{f_if_j}\longrightarrow\cdots
\longrightarrow M_{f_1\cdots f_n}\longrightarrow0
$$

is exact.

The proof is a two-line argument once the complex is recognized structurally. For $1\le i\le n$
let $K_i$ denote the two-term complex of $A$-modules

$$
K_i=\bigl[\,A\longrightarrow A_{f_i}\,\bigr],
$$

placed in degrees $-1$ and $0$, with the localization map as differential. The point is that the
extended Čech complex is, up to a shift and a harmless change of signs, the tensor product of
these $n$ complexes with $M$.

**Lemma 1.2 (tensor description).** There is an isomorphism of complexes of $A$-modules

$$
\check C_{\mathrm{ext}}^\bullet(\underline f,M)\;\simeq\;
\bigl(K_1\otimes_A\cdots\otimes_AK_n\otimes_AM\bigr)[\,1-n\,].
$$

**Proof.** Write $T^\bullet=K_1\otimes_A\cdots\otimes_AK_n\otimes_AM$, with the sign conventions
for tensor products of complexes recalled in Book 7a, Section 7.1. A summand of $T^\bullet$ is
obtained by choosing, for each index $i$, either the degree $-1$ term $A$ or the degree $0$ term
$A_{f_i}$. Let $I$ be the set of indices where the degree $0$ term is chosen. The corresponding
summand is

$$
A_{f_{i_1}}\otimes_A\cdots\otimes_AA_{f_{i_m}}\otimes_AM=M_{f_I},
\qquad I=\{i_1,\ldots,i_m\},
$$

because tensoring with a localization is localization, and it sits in total degree
$|I|-n$. Hence $T^{p+1-n}=\prod_{|I|=p+1}M_{f_I}=\check C^p(\underline f,M)$ for
$-1\le p\le n-1$, which is the asserted equality of graded modules after the shift by $1-n$.

The differential of $T^\bullet$ takes the $I$-summand to the summands indexed by $I\cup\{j\}$ for
$j\notin I$, by the localization map, with the Koszul sign
$(-1)^{\#\{i<j\,:\,i\notin I\}}$; the Čech differential uses the same maps with the sign
$(-1)^{\#\{i<j\,:\,i\in I\}}$, since that exponent is the position of $j$ in the ordered set
$I\cup\{j\}$. The two exponents add up to $j-1$, so the two differentials differ, on the map out of
the $I$-summand into the $(I\cup\{j\})$-summand, by the factor $(-1)^{j-1}$. Consequently the
diagonal automorphism which is multiplication by

$$
\varepsilon_I=(-1)^{\sum_{i\in I}(i-1)}
$$

on the $I$-summand carries one differential to the other: indeed
$\varepsilon_{I\cup\{j\}}\varepsilon_I^{-1}=(-1)^{j-1}$. This is an isomorphism of complexes.
$\square$

**Proof of Theorem 1.1.** Exactness of a complex of $A$-modules may be tested after localizing at
a unimodular family. Indeed localization is exact, so it commutes with the formation of cohomology
modules, and a module $N$ with $N_{f_i}=0$ for all $i$ vanishes: given $x\in N$ there is $m$ with
$f_i^mx=0$ for every $i$, and the elements $f_1^m,\ldots,f_n^m$ again generate the unit ideal,
because a power of the ideal they generate contains a power of $(f_1,\ldots,f_n)=A$; hence
$x=1\cdot x=0$. Applying this to the cohomology modules of
$\check C^\bullet_{\mathrm{ext}}(\underline f,M)$, it suffices to prove that each localization
$\check C^\bullet_{\mathrm{ext}}(\underline f,M)_{f_j}$ is exact.

Localization commutes with the finite products and with each $M_{f_I}$, so

$$
\check C_{\mathrm{ext}}^\bullet(\underline f,M)_{f_j}
=\check C_{\mathrm{ext}}^\bullet\bigl(\underline f^{\,\prime},M_{f_j}\bigr),
$$

the extended Čech complex over the ring $A_{f_j}$ for the image family
$\underline f^{\,\prime}=(f_1/1,\ldots,f_n/1)$ and the module $M_{f_j}$. In that ring the $j$-th
member of the family is invertible, so the $j$-th factor
$K_j'=[\,A_{f_j}\to(A_{f_j})_{f_j}\,]$ has an isomorphism as its differential. A two-term complex
whose differential is an isomorphism is contractible: the inverse isomorphism, placed in the
opposite degree, is a homotopy between the identity and zero. Tensoring a contractible complex
with any complex gives a contractible complex, since the homotopy tensors along. By Lemma 1.2 the
localized extended Čech complex is therefore contractible, in particular exact. $\square$

It is worth recording the contracting homotopy explicitly, because it is the mechanism behind
every later Čech vanishing statement. Suppose $f_j$ is invertible in $A$. Then for $I$ with
$j\notin I$ the localization map $M_{f_I}\to M_{f_{I\cup\{j\}}}$ is an isomorphism, and one may
define $h:\check C^p_{\mathrm{ext}}\to\check C^{p-1}_{\mathrm{ext}}$ by

$$
(h\sigma)_I=\begin{cases}
\pm\,\sigma_{I\cup\{j\}}&j\notin I,\\[2pt]
0&j\in I,
\end{cases}
$$

with the sign dictated by the position of $j$ in $I\cup\{j\}$; then $dh+hd=\mathrm{id}$. In words:
in the presence of a member of the cover on which everything is already defined, every cocycle is
the coboundary of its own restriction to that member. This is the algebraic shadow of the
geometric statement that a cover with a member equal to the whole space is a trivial cover.

Two consequences will be used verbatim.

**Corollary 1.3 (sheaf axiom in module form).** If $f_1,\ldots,f_n$ generate the unit ideal of $A$
and $M$ is an $A$-module, then

$$
0\longrightarrow M\longrightarrow\prod_iM_{f_i}\longrightarrow\prod_{i<j}M_{f_if_j}
$$

is exact. In particular $M\to\prod_iM_{f_i}$ is injective, and a family of elements
$m_i\in M_{f_i}$ agreeing in every $M_{f_if_j}$ comes from a unique element of $M$.

**Corollary 1.4 (Čech vanishing for a principal cover).** With the same hypotheses, the
unextended complex $\check C^\bullet(\underline f,M)$ has cohomology $M$ in degree $0$ and zero in
all positive degrees.

Both are immediate from Theorem 1.1. Notice how much has been assumed and how little: $A$ is an
arbitrary commutative ring, $M$ an arbitrary module, not necessarily finitely generated, and no
noetherian or finiteness hypothesis appears. This is the reason the cohomological theory built on
Theorem 1.1 will remain valid after base change to rings with nilpotents or without ascending
chain conditions, a robustness the later applications genuinely require.

Finally, a warning that is also a preview. Unimodularity is essential. If the $f_i$ do not
generate the unit ideal, the extended complex is usually far from exact, and its failure is a
meaningful invariant: for the family $(x_0,\ldots,x_r)$ in a polynomial ring, the top cohomology
of the unextended complex is a free module on the Laurent monomials with all exponents negative.
Chapter 6 identifies that module with $H^r(\mathbf P^r_A,\mathcal O(n))$ summed over $n$. Thus the
same complex, exact when the elements cover the spectrum and inexact when they cut out a nonempty
closed set, produces both the vanishing theorem on affines and the single nonvanishing computation
that drives projective geometry.

## 2. Quasi-coherent sheaves

### 2.1 The sheaf attached to a module

The spectrum of a ring was designed so that the ring becomes a sheaf: the structure sheaf assigns
$A_f$ to the principal open $D(f)$, and the sheaf axiom for that assignment is exactly the case
$M=A$ of Corollary 1.3. A module deserves the same treatment. Given an $A$-module $M$ we want a
sheaf on $\operatorname{Spec}A$ whose sections over $D(f)$ are $M_f$, so that restricting a section
to a smaller open means inverting more elements, and so that the germ at a prime is the
localization there. There is essentially no choice in the matter, and the only thing to prove is
that the assignment is consistent and satisfies the sheaf axiom.

Write $X=\operatorname{Spec}A$. Two preliminary remarks make the construction unambiguous. First,
if $D(g)\subseteq D(f)$ then $g$ lies in every prime containing $f$, so $g^m=af$ for some $m\ge1$
and $a\in A$; hence $f$ becomes invertible in $A_g$ and there is a canonical $A$-algebra map
$A_f\to A_g$, and correspondingly a canonical map $M_f\to M_g$. Second, these maps compose
correctly, and when $D(f)=D(g)$ the two canonical maps are mutually inverse. So $D(f)\mapsto M_f$
is a well-defined presheaf on the basis of principal opens, depending only on the open set and not
on the chosen generator.

**Proposition 2.1.** The assignment $D(f)\mapsto M_f$ satisfies the sheaf axiom for coverings of
principal opens by principal opens, and therefore extends uniquely to a sheaf $\widetilde M$ of
$\mathcal O_X$-modules on $X=\operatorname{Spec}A$ with

$$
\Gamma(D(f),\widetilde M)=M_f,\qquad\text{in particular}\qquad
\Gamma(X,\widetilde M)=M.
$$

**Proof.** Let $D(f)=\bigcup_{i\in J}D(g_i)$ with all $g_i\in A$. Replacing $A$ by $A_f$ and $M$ by
$M_f$ we may assume $f=1$, since $D(g_i)\subseteq D(f)$ gives $D(g_i)=D(fg_i)$ and hence
$M_{g_i}=M_{fg_i}=(M_f)_{g_i}$ canonically. So assume the $D(g_i)$ cover $X$; then the $g_i$
generate the unit ideal, and since $X$ is quasi-compact finitely many of them already do. Fix such
a finite subfamily $g_{i_1},\ldots,g_{i_n}$.

Separatedness of sections: if $m\in M$ restricts to $0$ in every $M_{g_i}$, then it restricts to
$0$ in the finite subfamily, so $m=0$ by Corollary 1.3. Gluing: let $(m_i)_{i\in J}$ be a family
with $m_i\in M_{g_i}$ agreeing in $M_{g_ig_j}$ for all $i,j$. Corollary 1.3 applied to the finite
subfamily produces a unique $m\in M$ restricting to $m_{i_k}$ for $k=1,\ldots,n$. For an arbitrary
$i\in J$, the elements $m$ and $m_i$ of $M_{g_i}$ agree in each $M_{g_ig_{i_k}}$, and the opens
$D(g_ig_{i_k})$ cover $D(g_i)$; the already-proved separatedness over the ring $A_{g_i}$ gives
$m|_{D(g_i)}=m_i$. Thus the basis presheaf is a sheaf on the basis. A sheaf on a basis extends
uniquely to a sheaf on the whole space, by taking the equalizer defining sections over an
arbitrary open, and the extension is a module over $\mathcal O_X=\widetilde A$ because the
$A_f$-module structures on the $M_f$ are compatible with restriction. $\square$

The construction is as functorial and as exact as localization is.

**Proposition 2.2.** Let $X=\operatorname{Spec}A$.

1. For $\mathfrak p\in X$ the stalk is $(\widetilde M)_{\mathfrak p}=M_{\mathfrak p}$.
2. $M\mapsto\widetilde M$ is an exact functor from $A$-modules to $\mathcal O_X$-modules.
3. It is fully faithful: $\operatorname{Hom}_{\mathcal O_X}(\widetilde M,\widetilde N)
   =\operatorname{Hom}_A(M,N)$.
4. It commutes with arbitrary direct sums and filtered colimits, and
   $\widetilde{M\otimes_AN}=\widetilde M\otimes_{\mathcal O_X}\widetilde N$.
5. For $f\in A$ one has $\widetilde M|_{D(f)}=\widetilde{M_f}$ under
   $D(f)\simeq\operatorname{Spec}A_f$.

**Proof.** (1) The stalk is the filtered colimit of $M_f$ over $f\notin\mathfrak p$, which is
$M_{\mathfrak p}$. (2) Exactness of a sequence of sheaves is exactness on stalks, and localization
at a prime is exact; conversely $M$ is recovered as global sections, so a sequence of modules whose
tilde is exact is exact. (3) A map $\varphi:\widetilde M\to\widetilde N$ gives an $A$-linear map
$\Gamma(\varphi)$ on global sections. It determines $\varphi$: on $D(f)$ every element of $M_f$ is
$m/f^k$ with $m\in M$, and $\mathcal O$-linearity forces
$\varphi_{D(f)}(m/f^k)=f^{-k}\Gamma(\varphi)(m)|_{D(f)}$. Conversely an $A$-linear $u:M\to N$
induces compatible maps $u_f:M_f\to N_f$ on the basis, hence a map of sheaves; the two
constructions are inverse. (4) Filtered colimits and arbitrary direct sums of modules commute with
localization, so the presheaf colimit already has the correct values on the basis of principal
opens; each such open is quasi-compact with quasi-compact pairwise intersections, so the finite
sheaf conditions of Corollary 1.3 pass through the filtered colimit and the presheaf colimit is
already a sheaf on the basis. It is therefore the colimit in sheaves. The tensor assertion is
checked on stalks, where it is $(M\otimes_AN)_{\mathfrak p}=M_{\mathfrak p}\otimes_{A_{\mathfrak p}}
N_{\mathfrak p}$. (5) Both sides have the same sections on the basis $D(fg)$ of $D(f)$. $\square$

Two consequences deserve emphasis, because they are the properties that fail for a general
$\mathcal O_X$-module. Exactness in (2) says that the kernel and cokernel of a map of tilde sheaves
are again tilde sheaves, with no sheafification correction: the presheaf cokernel of
$\widetilde M\to\widetilde N$ is already a sheaf, since on the basis it is
$D(f)\mapsto\operatorname{coker}(M_f\to N_f)=(\operatorname{coker})_f$. Full faithfulness in (3)
says that a morphism of such sheaves is nothing more than a morphism of modules; there is no extra
global geometry in the maps.

Finally, taking global sections of a tilde sheaf is exact, by (2) and
$\Gamma(X,\widetilde M)=M$. This is the underived form of Serre's vanishing theorem, and it is
worth noticing that we already have it: what Chapter 3 must add is that the derived functors also
vanish, which does not follow formally from exactness of $\Gamma$ on this subcategory alone,
because higher cohomology is computed by resolutions that need not stay inside the subcategory.

### 2.2 Quasi-coherence and its local character

On a general scheme there is no single ring to take modules over, so the definition must be local.
The right formulation is not "locally isomorphic to some $\widetilde M$", which would be awkward
to verify, but the presentational one: a sheaf is quasi-coherent when it is locally the cokernel
of a map of free modules. That this is equivalent to the tilde description on every affine open —
and hence that the class of such sheaves is affine-local — is the content of this section, and it
is the theorem that lets us move freely between geometry and algebra for the rest of the book.

**Definition.** An $\mathcal O_X$-module $\mathcal F$ on a scheme $X$ is **quasi-coherent** if
every point of $X$ has an open neighborhood $U$ for which there is an exact sequence of
$\mathcal O_U$-modules

$$
\mathcal O_U^{(J)}\longrightarrow\mathcal O_U^{(I)}\longrightarrow\mathcal F|_U\longrightarrow0
$$

with $I,J$ arbitrary index sets. We write $\mathrm{QCoh}(X)$ for the full subcategory of
$\mathrm{Mod}(\mathcal O_X)$ they span. If $X$ is locally noetherian, $\mathcal F$ is **coherent**
if every point has an affine neighborhood $\operatorname{Spec}A$ with
$\mathcal F|_{\operatorname{Spec}A}\simeq\widetilde M$ for a finitely generated $A$-module $M$;
the corresponding category is $\mathrm{Coh}(X)$.

Both index sets are allowed to be infinite: no finiteness is imposed, and none is available in the
generality we need. By Proposition 2.2, every $\widetilde M$ is quasi-coherent, since a
presentation $A^{(J)}\to A^{(I)}\to M\to0$ tildes to an exact sequence of sheaves.

**Theorem 2.3 (affine criterion).** Let $X=\operatorname{Spec}A$ and let $\mathcal F$ be an
$\mathcal O_X$-module. The following are equivalent.

1. $\mathcal F$ is quasi-coherent.
2. $\mathcal F\simeq\widetilde M$ for some $A$-module $M$.
3. The canonical map $\widetilde{\Gamma(X,\mathcal F)}\to\mathcal F$ is an isomorphism.
4. For every $f\in A$ the canonical map
   $\Gamma(X,\mathcal F)_f\to\Gamma(D(f),\mathcal F)$ is an isomorphism.

**Proof.** Clearly (3) implies (2), and (2) implies (1) by the remark above; and (2) implies (4)
and (3) by Proposition 2.1, since global sections of $\widetilde M$ are $M$. It remains to prove
that (1) implies (4), and that (4) implies (3).

Assume (1). Each point lies in an open $U$ carrying a presentation, and each such $U$ contains a
principal open $D(g)$ around the point. Restricting the presentation to $D(g)$ and using
Proposition 2.2, the sheaf $\mathcal F|_{D(g)}$ is the cokernel of a map of free
$\mathcal O_{D(g)}$-modules, hence is the tilde of the cokernel of the corresponding map of free
$A_g$-modules; exactness of the tilde functor is what allows the cokernel to be computed
modulewise. Since $X$ is quasi-compact, finitely many such principal opens
$D(g_1),\ldots,D(g_n)$ cover $X$, and on each of them, and on each intersection
$D(g_ig_j)$, the restriction of $\mathcal F$ is a tilde sheaf: indeed
$\widetilde{N}|_{D(g_j)}=\widetilde{N_{g_j}}$.

Now fix $f\in A$ and abbreviate $F(V)=\Gamma(V,\mathcal F)$. The opens $D(fg_i)$ cover $D(f)$ and
their pairwise intersections are the $D(fg_ig_j)$, so the sheaf axiom gives an exact sequence

$$
0\longrightarrow F(D(f))\longrightarrow\prod_iF(D(fg_i))
\longrightarrow\prod_{i,j}F(D(fg_ig_j)).
$$

Taking $f=1$ gives the corresponding sequence for $X$, and localizing it at $f$ keeps it exact
because localization is exact and commutes with the finite products appearing here. We therefore
have a commutative diagram with exact rows

$$
\begin{array}{ccccccc}
0&\to&F(X)_f&\to&\prod_iF(D(g_i))_f&\to&\prod_{i,j}F(D(g_ig_j))_f\\
 & &\downarrow& &\downarrow& &\downarrow\\
0&\to&F(D(f))&\to&\prod_iF(D(fg_i))&\to&\prod_{i,j}F(D(fg_ig_j)).
\end{array}
$$

On $D(g_i)$ and on $D(g_ig_j)$ the sheaf $\mathcal F$ is a tilde sheaf, so the second and third
vertical maps are isomorphisms: localizing $N$ at the image of $f$ is exactly restricting
$\widetilde N$ to the locus where $f$ is invertible. The five lemma now shows that the first
vertical map is an isomorphism, which is (4).

Assume (4), and set $M=\Gamma(X,\mathcal F)$. The canonical map $\widetilde M\to\mathcal F$ is,
over $D(f)$, the map $M_f\to\Gamma(D(f),\mathcal F)$, an isomorphism by hypothesis. A map of
sheaves that is an isomorphism on a basis is an isomorphism. $\square$

**Corollary 2.4.** For a ring $A$, the functors $M\mapsto\widetilde M$ and
$\mathcal F\mapsto\Gamma(\operatorname{Spec}A,\mathcal F)$ are mutually inverse equivalences

$$
\mathrm{Mod}_A\;\simeq\;\mathrm{QCoh}(\operatorname{Spec}A),
$$

exact in both directions. Under it, finitely generated modules correspond to sheaves admitting a
presentation with $I$ finite, and, when $A$ is noetherian, finitely generated modules correspond
to coherent sheaves.

**Proof.** Combine Theorem 2.3 with the full faithfulness and exactness of Proposition 2.2.
$\square$

Two reformulations of condition (4) are used constantly and are worth stating separately, since
they are the form in which the criterion is applied to sections rather than to sheaves.

**Corollary 2.5 (extension and annihilation of sections).** Let $\mathcal F$ be quasi-coherent on
$X=\operatorname{Spec}A$ and let $f\in A$.

1. If $s\in\Gamma(X,\mathcal F)$ restricts to $0$ on $D(f)$, then $f^ns=0$ for some $n\ge0$.
2. Every $t\in\Gamma(D(f),\mathcal F)$ satisfies $f^nt=s|_{D(f)}$ for some $n\ge0$ and some
   $s\in\Gamma(X,\mathcal F)$.

These are the injectivity and the surjectivity of $\Gamma(X,\mathcal F)_f\to\Gamma(D(f),\mathcal F)$
written out.

The affine criterion makes quasi-coherence a condition that may be tested on any one affine cover,
which is what "local character" means here.

**Corollary 2.6 (locality).** Let $\mathcal F$ be an $\mathcal O_X$-module on a scheme $X$. The
following are equivalent: $\mathcal F$ is quasi-coherent; for every affine open
$U=\operatorname{Spec}A\subseteq X$ one has $\mathcal F|_U\simeq\widetilde{\Gamma(U,\mathcal F)}$;
this holds for the members of one affine open cover of $X$.

**Proof.** The first condition is local by definition and restricts to opens, so it implies the
second by Theorem 2.3 applied to each affine open. The second trivially implies the third. If the
third holds, then each member of the cover carries a presentation of $\mathcal F$ by Theorem 2.3
again, and these neighborhoods cover $X$. $\square$

A counterexample shows that quasi-coherence is a genuine restriction and that the tilde
description can fail badly. Let $R$ be a discrete valuation ring with uniformizer $\pi$, fraction
field $K$, and $X=\operatorname{Spec}R=\{\eta,s\}$ with $\eta$ the generic point and
$U=D(\pi)=\{\eta\}$. Let $\mathcal G=j_!(\mathcal O_U)$ be the extension by zero, so that
$\Gamma(X,\mathcal G)=0$ while $\Gamma(U,\mathcal G)=K$. Condition (4) of Theorem 2.3 fails at
$f=\pi$: the source is $0$ and the target is $K$. Concretely, the nonzero section over $U$ cannot
be killed by any power of $\pi$, as Corollary 2.5 would require. By contrast the skyscraper
$i_*(R/\pi)$ at the closed point is quasi-coherent, being $\widetilde{R/\pi}$; extension by zero
along an open immersion destroys quasi-coherence, while pushforward along a closed immersion
preserves it. Section 2.4 explains which direct images are safe.

### 2.3 Kernels, cokernels, extensions, and pullback

For quasi-coherent sheaves to be a usable category, the operations of homological algebra must not
lead out of it. This is not automatic for a subcategory of $\mathcal O_X$-modules: cokernels
involve sheafification, and a subsheaf of a well-behaved sheaf can be arbitrary. What saves the
situation is Theorem 2.3. Every operation below is local on $X$, so it may be computed on affine
opens; there, by Corollary 2.4, it is the corresponding operation on modules, transported by an
exact equivalence. The proofs are therefore short, but the conclusion is what makes the theory
work.

**Theorem 2.7 (permanence).** Let $X$ be a scheme.

1. If $\varphi:\mathcal F\to\mathcal G$ is a map of quasi-coherent sheaves, then
   $\ker\varphi$, $\operatorname{im}\varphi$, and $\operatorname{coker}\varphi$ are
   quasi-coherent. Consequently $\mathrm{QCoh}(X)$ is an abelian category and the inclusion into
   $\mathrm{Mod}(\mathcal O_X)$ is exact.
2. Arbitrary direct sums and filtered colimits of quasi-coherent sheaves, formed in
   $\mathrm{Mod}(\mathcal O_X)$, are quasi-coherent.
3. If $\mathcal F,\mathcal G$ are quasi-coherent so is
   $\mathcal F\otimes_{\mathcal O_X}\mathcal G$.
4. For any morphism of schemes $f:X\to Y$ and any quasi-coherent $\mathcal G$ on $Y$, the pullback
   $f^*\mathcal G$ is quasi-coherent; if $Y=\operatorname{Spec}A$, $X=\operatorname{Spec}B$ and
   $\mathcal G=\widetilde M$, then $f^*\mathcal G=\widetilde{M\otimes_AB}$.

**Proof.** (1) The assertions are local, so let $X=\operatorname{Spec}A$ and write
$\varphi=\widetilde u$ for a map $u:M\to N$ of modules, using Corollary 2.4. The tilde functor is
exact, so $\widetilde{\ker u}$, $\widetilde{\operatorname{im}u}$ and
$\widetilde{\operatorname{coker}u}$ are the kernel, image, and cokernel of $\varphi$ in
$\mathcal O_X$-modules; in particular the presheaf cokernel is already a sheaf and no
sheafification correction occurs. (2) By Proposition 2.2(4) the colimit computed in
$\mathcal O_X$-modules is the tilde of the colimit of modules on each affine open, and quasi-coherence
is affine-local by Corollary 2.6. (3) Same argument with Proposition 2.2(4). (4) Pullback is right
exact and carries $\mathcal O_Y^{(I)}$ to $\mathcal O_X^{(I)}$, so it transforms a local
presentation of $\mathcal G$ into a local presentation of $f^*\mathcal G$; this is the one place
where the presentational definition pays for itself immediately. For the formula, both
$M\mapsto f^*\widetilde M$ and $M\mapsto\widetilde{M\otimes_AB}$ are right exact and agree on free
modules, hence agree on all modules by choosing a presentation. $\square$

Extensions require one further input. If $0\to\mathcal F'\to\mathcal F\to\mathcal F''\to0$ is exact
with the outer terms quasi-coherent, the affine criterion for $\mathcal F$ needs global sections
over an affine to surject onto global sections of $\mathcal F''$, and that is a vanishing
statement, not a formal one.

**Theorem 2.8 (extensions).** Let $0\to\mathcal F'\to\mathcal F\to\mathcal F''\to0$ be an exact
sequence of $\mathcal O_X$-modules on a scheme $X$ with $\mathcal F'$ and $\mathcal F''$
quasi-coherent. Then $\mathcal F$ is quasi-coherent.

**Proof.** The question is local, so let $X=\operatorname{Spec}A$ and verify condition (4) of
Theorem 2.3. Write $F'(V),F(V),F''(V)$ for sections. By Theorem 3.9 below,
$H^1(V,\mathcal F')=0$ for every affine open $V$ of $X$, so the sequence of sections

$$
0\to F'(V)\to F(V)\to F''(V)\to0
$$

is exact for $V=X$ and for $V=D(f)$. Localizing the first at $f$ preserves exactness, and the outer
vertical comparison maps $F'(X)_f\to F'(D(f))$ and $F''(X)_f\to F''(D(f))$ are isomorphisms
because $\mathcal F'$ and $\mathcal F''$ are quasi-coherent. The five lemma gives the middle
isomorphism. There is no circularity: the proof of Theorem 3.9 uses only Theorem 1.1, Section 2.2,
and the general machinery of Chapter 3, none of which invokes the present statement. $\square$

Thus $\mathrm{QCoh}(X)$ is what is sometimes called a weak Serre subcategory of
$\mathrm{Mod}(\mathcal O_X)$: closed under kernels, cokernels, and extensions. In particular an
exact sequence of $\mathcal O_X$-modules with quasi-coherent outer terms may be used freely, and
its long exact cohomology sequence, once cohomology is available, stays within the theory.

Two classes of examples will recur. A **locally free** sheaf of rank $r$ is one that is locally
isomorphic to $\mathcal O_X^r$; it is quasi-coherent, being $\widetilde{A^r}$ on suitable affine
opens, and it is coherent when $X$ is locally noetherian. An **invertible** sheaf is a locally free
sheaf of rank one. For a finitely presented quasi-coherent $\mathcal F$ and arbitrary
quasi-coherent $\mathcal G$, the sheaf $\mathcal Hom_{\mathcal O_X}(\mathcal F,\mathcal G)$ is
quasi-coherent, with value $\operatorname{Hom}_A(M,N)$ on an affine open where the two sheaves are
$\widetilde M$ and $\widetilde N$: apply $\operatorname{Hom}(-,\mathcal G)$ to a finite presentation
of $\mathcal F$ and use left exactness together with
$\mathcal Hom(\mathcal O^n,\mathcal G)=\mathcal G^n$. Finite presentation matters here; without it
the formation of $\operatorname{Hom}$ need not commute with localization.

On a locally noetherian scheme the finiteness conditions behave as expected. If
$X=\operatorname{Spec}A$ with $A$ noetherian, then $\widetilde M$ is coherent exactly when $M$ is
finitely generated, submodules of finitely generated modules are finitely generated, and
consequently $\mathrm{Coh}(X)$ is an abelian subcategory of $\mathrm{QCoh}(X)$: kernels, cokernels,
images, extensions, finite direct sums, and tensor products of coherent sheaves are coherent.
Arbitrary direct sums are not; coherence is exactly the finiteness that infinite colimits destroy.
That failure is the subject of the last result of the next section, which says that the destruction
is orderly: every quasi-coherent sheaf on a noetherian scheme is the increasing union of its
coherent subsheaves.

### 2.4 Pushforward along quasi-compact morphisms

Pullback preserved quasi-coherence for a formal reason. Pushforward cannot, as the extension by
zero at the end of Section 2.2 already shows in the guise of a direct image along an open
immersion from a scheme that is too small. The correct hypotheses are finiteness hypotheses on the
morphism, and they enter through exactly one mechanism: to identify $f_*\mathcal F$ we must express
its sections as a finite limit of sections over affines, and that requires the preimage of an
affine to be covered by finitely many affines with finitely many affines in each intersection.
This is what quasi-compactness and quasi-separatedness say.

Start with the easiest case. A morphism $f:X\to Y$ is affine when preimages of affine opens are
affine; closed immersions and morphisms between affine schemes are affine, and an affine morphism
is quasi-compact and separated.

**Lemma 2.9.** Let $f:X\to Y$ be an affine morphism and $\mathcal F$ quasi-coherent on $X$. Then
$f_*\mathcal F$ is quasi-coherent, and for every affine open $V=\operatorname{Spec}A\subseteq Y$
one has $f_*\mathcal F|_V=\widetilde{\Gamma(f^{-1}V,\mathcal F)}$, the module being viewed over $A$
through $A\to\Gamma(f^{-1}V,\mathcal O_X)$.

**Proof.** Quasi-coherence may be checked on the affine opens of $Y$ by Corollary 2.6, so let
$V=\operatorname{Spec}A$ and $U=f^{-1}V=\operatorname{Spec}B$, an affine scheme. For $g\in A$ we
have $f^{-1}(D(g))=D(g')$ where $g'$ is the image of $g$ in $B$, whence

$$
\Gamma(D(g),f_*\mathcal F)=\Gamma(D(g'),\mathcal F)=\Gamma(U,\mathcal F)_{g'}
=\Gamma(U,\mathcal F)_g,
$$

using Theorem 2.3 on $U$. This is condition (4) of Theorem 2.3 for $f_*\mathcal F$ on $V$.
$\square$

In particular, for a closed immersion $i:Z\to X$ the functor $i_*$ carries quasi-coherent sheaves
to quasi-coherent sheaves and is exact, being exact on stalks. The kernel of
$\mathcal O_X\to i_*\mathcal O_Z$ is then quasi-coherent by Theorem 2.7, which is the statement
that the ideal sheaf of a closed subscheme is quasi-coherent; conversely a quasi-coherent ideal
sheaf defines a closed subscheme, since on an affine open it is $\widetilde I$ for an ideal
$I\subseteq A$ and the closed subscheme is $\operatorname{Spec}A/I$.

**Theorem 2.10.** Let $f:X\to Y$ be a quasi-compact and quasi-separated morphism of schemes and
let $\mathcal F$ be quasi-coherent on $X$. Then $f_*\mathcal F$ is quasi-coherent. If
$Y=\operatorname{Spec}A$ is affine, then $f_*\mathcal F=\widetilde{\Gamma(X,\mathcal F)}$.

**Proof.** The assertion is local on $Y$, so assume $Y=\operatorname{Spec}A$; then $X$ is
quasi-compact and quasi-separated. Choose a finite affine open cover $X=\bigcup_{i=1}^nU_i$. Each
intersection $U_i\cap U_j$ is quasi-compact, because the diagonal is quasi-compact, so it admits a
finite affine open cover $U_i\cap U_j=\bigcup_kU_{ijk}$. Write $a_i:U_i\to Y$ and
$a_{ijk}:U_{ijk}\to Y$ for the restrictions of $f$; these are morphisms from affine schemes to an
affine scheme, hence affine morphisms.

For every open $V\subseteq Y$ the sheaf axiom on $f^{-1}V$, applied to the cover by the
$U_i\cap f^{-1}V$ and to the covers of the overlaps by the $U_{ijk}\cap f^{-1}V$, gives an exact
sequence of abelian groups

$$
0\to\Gamma(f^{-1}V,\mathcal F)\to\prod_i\Gamma(U_i\cap f^{-1}V,\mathcal F)
\to\prod_{i,j,k}\Gamma(U_{ijk}\cap f^{-1}V,\mathcal F).
$$

These are precisely the sections over $V$ of $f_*\mathcal F$, of
$\prod_ia_{i*}(\mathcal F|_{U_i})$, and of $\prod_{i,j,k}a_{ijk*}(\mathcal F|_{U_{ijk}})$, and the
maps are maps of sheaves. Hence $f_*\mathcal F$ is the kernel of a map between finite products of
sheaves that are quasi-coherent by Lemma 2.9. Finite products of quasi-coherent sheaves are
quasi-coherent, and kernels of maps of quasi-coherent sheaves are quasi-coherent by Theorem 2.7;
therefore $f_*\mathcal F$ is quasi-coherent. Its module of global sections over the affine $Y$ is
$\Gamma(X,\mathcal F)$, which with Theorem 2.3 gives the displayed identification. $\square$

The hypotheses are not decoration. In the counterexample of Section 2.2 the morphism is the open
immersion $j:U\to X$ with $U$ the generic point of a spectrum of a discrete valuation ring; it is
quasi-compact and separated, and indeed $j_*\mathcal O_U=\widetilde K$ is quasi-coherent. What
failed there was $j_!$, not $j_*$. Quasi-compactness genuinely fails, and with it the theorem, for
an infinite disjoint union mapped into a point in an unbounded way; quasi-separatedness fails for
schemes glued from infinitely many copies of an affine along a common open, where the overlap
computation above has no finite form.

We close the chapter with the finiteness statement promised at the end of Section 2.3. It is used
later to reduce assertions about arbitrary quasi-coherent sheaves on noetherian schemes to
assertions about coherent ones.

**Theorem 2.11 (coherent exhaustion).** Let $X$ be a noetherian scheme and $\mathcal F$ a
quasi-coherent $\mathcal O_X$-module. Then the coherent subsheaves of $\mathcal F$ form a filtered
system under inclusion whose colimit is $\mathcal F$; that is, $\mathcal F$ is the increasing union
of its coherent subsheaves.

**Proof.** The system is filtered: the sum of two coherent subsheaves is a quotient of their direct
sum, hence coherent. We must produce enough coherent subsheaves.

First a gluing lemma: if $U\subseteq X$ is open, $\mathcal G\subseteq\mathcal F|_U$ is a coherent
subsheaf, and $V\subseteq X$ is an affine open, then there is a coherent subsheaf
$\mathcal G^\sharp\subseteq\mathcal F|_{U\cup V}$ with $\mathcal G^\sharp|_U=\mathcal G$. To see
this, let $j:U\to X$ be the inclusion and set

$$
\mathcal H=\mathcal F\times_{j_*(\mathcal F|_U)}j_*\mathcal G\subseteq\mathcal F,
$$

the preimage of $j_*\mathcal G$ under $\mathcal F\to j_*(\mathcal F|_U)$. Since $X$ is noetherian
it is quasi-compact and quasi-separated, so $j_*$ preserves quasi-coherence by Theorem 2.10, and
$\mathcal H$ is quasi-coherent by Theorem 2.7. Restriction to $U$ is exact and
$(j_*\mathcal K)|_U=\mathcal K$, so $\mathcal H|_U=\mathcal G$. Now write
$V=\operatorname{Spec}A$ and $P=\Gamma(V,\mathcal H)$, so $\mathcal H|_V=\widetilde P$. The open
$U\cap V$ is a quasi-compact open of $V$, hence a finite union of principal opens
$D(f_1),\ldots,D(f_m)$, and on each of them $\mathcal H$ agrees with the coherent sheaf
$\mathcal G$, so $P_{f_l}$ is a finitely generated $A_{f_l}$-module. Each of its generators, after
multiplication by a power of $f_l$, is the image of an element of $P$ by Corollary 2.5. Let
$N\subseteq P$ be the finitely generated submodule generated by all these finitely many elements;
then $N_{f_l}=P_{f_l}$ for every $l$, so $\widetilde N$ and $\mathcal H$ agree on $U\cap V$. Since
$\widetilde N|_{U\cap V}=\mathcal G|_{U\cap V}$ as subsheaves of $\mathcal F|_{U\cap V}$, the
sheaves $\mathcal G$ on $U$ and $\widetilde N$ on $V$ glue to a subsheaf $\mathcal G^\sharp$ of
$\mathcal F|_{U\cup V}$, coherent because it is coherent on $U$ and on $V$.

Now let $X=V_1\cup\cdots\cup V_n$ be a finite affine cover and let $s$ be a section of
$\mathcal F$ over some affine open $W$. The $\mathcal O_W$-submodule of $\mathcal F|_W$ generated
by $s$ is coherent, and applying the gluing lemma $n$ times, adding one $V_r$ at a time, extends
it to a coherent subsheaf of $\mathcal F$ over all of $X$ whose restriction to $W$ contains $s$.
Every section of $\mathcal F$ over every affine open therefore lies in some coherent subsheaf.
Since the affine opens form a basis and the coherent subsheaves form a filtered system, the
colimit of the system has the same sections as $\mathcal F$ over a basis of opens, so the
inclusion of the colimit into $\mathcal F$ is an isomorphism. $\square$

The same argument with "coherent" replaced by "quasi-coherent of finite type" works on any
quasi-compact quasi-separated scheme, the noetherian hypothesis being used above only to know that
submodules of finitely generated modules are finitely generated. We will need only the noetherian
form.

## 3. Cohomology of quasi-coherent sheaves

### 3.1 Flasque sheaves and functorial resolutions

Cohomology was defined in Book 7a by injective resolutions. That definition is the right one for
proving general theorems and the wrong one for computing anything: injective sheaves are enormous
and no example of one is ever written down. The standard remedy is the acyclicity criterion of
Book 7a, Section 3.7 — any bounded-below resolution by objects with vanishing higher cohomology
computes the derived functor — together with a supply of acyclic objects that can be produced by
hand. The simplest such supply consists of the flasque sheaves, those in which every section
extends. Their acyclicity is elementary, and, what matters later just as much, there is a
resolution by flasque sheaves that is functorial in the sheaf being resolved. Functoriality is not
a convenience: Section 5.2 obtains the compatibility of cohomology with filtered colimits by
passing to the colimit inside a functorial resolution, an argument that no choice-dependent
resolution could support.

**Definition.** A sheaf $\mathcal G$ of abelian groups on a topological space $X$ is **flasque** if
for all opens $U\subseteq V$ the restriction map $\mathcal G(V)\to\mathcal G(U)$ is surjective.
Equivalently, $\mathcal G(X)\to\mathcal G(U)$ is surjective for every open $U$.

**Lemma 3.1.** Let $X$ be a topological space.

1. If $0\to\mathcal F'\to\mathcal F\to\mathcal F''\to0$ is exact and $\mathcal F'$ is flasque, then
   $0\to\mathcal F'(U)\to\mathcal F(U)\to\mathcal F''(U)\to0$ is exact for every open $U$.
2. If moreover $\mathcal F$ is flasque, then $\mathcal F''$ is flasque.
3. Every injective object of $\mathrm{Ab}(X)$ is flasque, and for a ringed space $(X,\mathcal O_X)$
   every injective object of $\mathrm{Mod}(\mathcal O_X)$ is flasque.
4. Restrictions to opens, arbitrary products, and direct images $f_*$ of flasque sheaves are
   flasque.

**Proof.** (1) Only surjectivity requires an argument. Fix $s''\in\mathcal F''(U)$ and consider
pairs $(V,s)$ with $V\subseteq U$ open and $s\in\mathcal F(V)$ mapping to $s''|_V$. The set of such
pairs is nonempty, because $\mathcal F\to\mathcal F''$ is surjective on stalks and hence locally on
sections, and it is partially ordered by extension. A totally ordered family glues, since its
members agree on overlaps by comparability, so Zorn's lemma provides a maximal pair $(V,s)$.
Suppose $V\ne U$ and pick $x\in U\setminus V$, an open $W\ni x$ with $W\subseteq U$, and
$t\in\mathcal F(W)$ lifting $s''|_W$. On $V\cap W$ the difference $s-t$ maps to zero in
$\mathcal F''$, so it is the image of some $u'\in\mathcal F'(V\cap W)$. Because $\mathcal F'$ is
flasque, $u'$ extends to $\tilde u\in\mathcal F'(W)$. Replacing $t$ by $t+\tilde u$ makes $t$ agree
with $s$ on $V\cap W$, so the two glue to a lift over $V\cup W$, contradicting maximality. Hence
$V=U$.

(2) Let $U\subseteq V$ and $s''\in\mathcal F''(U)$. By (1) lift it to $s\in\mathcal F(U)$, extend
$s$ to $\mathcal F(V)$ by flasqueness of $\mathcal F$, and map the extension into
$\mathcal F''(V)$.

(3) For an open $U\subseteq X$ let $\mathbf Z_U=j_!(\mathbf Z|_U)$ be the extension by zero of the
constant sheaf along $j:U\to X$; then
$\operatorname{Hom}_{\mathrm{Ab}(X)}(\mathbf Z_U,\mathcal G)=\mathcal G(U)$ naturally, and for
$U\subseteq V$ the induced map $\mathbf Z_U\to\mathbf Z_V$ is injective. Applying
$\operatorname{Hom}(-,\mathcal I)$ for $\mathcal I$ injective turns this injection into a
surjection $\mathcal I(V)\to\mathcal I(U)$. The same argument in
$\mathrm{Mod}(\mathcal O_X)$ uses $j_!(\mathcal O_X|_U)$, which represents sections over $U$ in the
category of $\mathcal O_X$-modules.

(4) Immediate from the definition, since sections of a product are products of sections and
$(f_*\mathcal G)(U)=\mathcal G(f^{-1}U)$. $\square$

**Proposition 3.2 (acyclicity).** Let $X$ be a topological space.

1. If $\mathcal G$ is flasque then $H^p(X,\mathcal G)=0$ for $p>0$, and the same holds on every
   open subset.
2. Every bounded-below flasque resolution $\mathcal F\to\mathcal G^\bullet$ computes cohomology:
   $H^p(X,\mathcal F)=H^p\bigl(\Gamma(X,\mathcal G^\bullet)\bigr)$.
3. For a ringed space, the right derived functors of $\Gamma(X,-)$ on
   $\mathrm{Mod}(\mathcal O_X)$ agree with those computed in $\mathrm{Ab}(X)$.
4. If $f:X\to Y$ is a morphism of ringed spaces, then $f_*$ carries injective and flasque objects
   to flasque, hence $\Gamma(Y,-)$-acyclic, objects; consequently the Leray spectral sequence of
   Book 7a, Section 8.1 is available for $f$, and $R^pf_*\mathcal F$ is the sheafification of
   $V\mapsto H^p(f^{-1}V,\mathcal F)$. If $f_*$ is exact, as for a closed immersion
   $i:Z\to X$, then $H^p(X,i_*\mathcal G)=H^p(Z,\mathcal G)$ for all $p$.

**Proof.** (1) Embed $\mathcal G$ in an injective sheaf $\mathcal I$ and let
$\mathcal Q=\mathcal I/\mathcal G$. By Lemma 3.1(3) $\mathcal I$ is flasque, so by Lemma 3.1(2) so
is $\mathcal Q$. By Lemma 3.1(1) the sequence of global sections is exact, whence
$H^1(X,\mathcal G)=\operatorname{coker}(\Gamma(X,\mathcal I)\to\Gamma(X,\mathcal Q))=0$. For
$p\ge2$ the long exact sequence gives $H^p(X,\mathcal G)\simeq H^{p-1}(X,\mathcal Q)$, which
vanishes by induction on $p$ since $\mathcal Q$ is flasque. Restrictions of flasque sheaves are
flasque, so the argument applies on every open. (2) This is the acyclicity criterion of Book 7a,
Section 3.7, given (1). (3) An injective $\mathcal O_X$-module is flasque by Lemma 3.1(3), hence
acyclic for $\Gamma$ in $\mathrm{Ab}(X)$ by (1); so an injective resolution in
$\mathrm{Mod}(\mathcal O_X)$ is an acyclic resolution in $\mathrm{Ab}(X)$ and computes the same
groups. (4) The first assertions are Lemma 3.1(3), (4) together with (1), and they are exactly the
hypothesis under which Book 7a, Section 8.1 constructs the Leray spectral sequence; the description
of $R^pf_*$ follows by computing with a flasque resolution. If $f_*$ is exact, it carries a flasque
resolution of $\mathcal G$ to a flasque resolution of $f_*\mathcal G$, and taking global sections
gives the same complex. $\square$

Part (3) settles a point of language once and for all: for a sheaf of modules on a scheme it does
not matter whether cohomology is computed in modules or in abelian groups, and we shall not
distinguish them again.

We now record the functorial resolution.

**Proposition 3.3 (Godement resolution).** There is a functor
$\mathcal F\mapsto\mathcal C^\bullet(\mathcal F)$ from $\mathrm{Ab}(X)$ to complexes of sheaves,
together with a natural augmentation $\mathcal F\to\mathcal C^\bullet(\mathcal F)$, such that each
$\mathcal C^p(-)$ is an exact functor with flasque values and each
$\mathcal F\to\mathcal C^\bullet(\mathcal F)$ is a resolution. Consequently
$H^p(X,\mathcal F)=H^p\bigl(\Gamma(X,\mathcal C^\bullet(\mathcal F))\bigr)$, naturally in
$\mathcal F$.

**Proof.** For $x\in X$ let $i_x:\{x\}\to X$ be the inclusion and set

$$
\mathcal C^0(\mathcal F)=\prod_{x\in X}(i_x)_*\bigl(\mathcal F_x\bigr),
\qquad\text{so}\qquad
\Gamma\bigl(U,\mathcal C^0(\mathcal F)\bigr)=\prod_{x\in U}\mathcal F_x,
$$

the sheaf of arbitrary, not necessarily coherent, families of germs. Restriction maps are
projections, hence surjective, so $\mathcal C^0(\mathcal F)$ is flasque; the map sending a section
to its family of germs is an injection $\mathcal F\to\mathcal C^0(\mathcal F)$, natural in
$\mathcal F$. The functor $\mathcal C^0$ is exact: a short exact sequence of sheaves gives short
exact sequences of stalks, hence of the displayed section groups on every open, and sectionwise
exactness implies exactness of sheaves. Now define inductively
$\mathcal Z^0=\mathcal F$, $\mathcal Z^{p+1}=\operatorname{coker}
(\mathcal Z^p\to\mathcal C^0(\mathcal Z^p))$ and
$\mathcal C^p(\mathcal F)=\mathcal C^0(\mathcal Z^p)$, with differentials the composites
$\mathcal C^0(\mathcal Z^p)\to\mathcal Z^{p+1}\to\mathcal C^0(\mathcal Z^{p+1})$. Each step is
functorial and exact, so each $\mathcal C^p(-)$ is an exact functor with flasque values, and the
resulting complex is a resolution by construction. The final assertion is Proposition 3.2(2).
$\square$

The last item of this section is the statement that positive-degree cohomology classes are locally
trivial. It is the precise sense in which cohomology measures gluing, and it is the engine of the
vanishing criterion in Section 3.2.

**Lemma 3.4 (local triviality).** Let $\mathcal F$ be a sheaf of abelian groups on $X$, let $p>0$,
and let $\xi\in H^p(X,\mathcal F)$. Then there is an open cover $X=\bigcup_iU_i$ with
$\xi|_{U_i}=0$ in $H^p(U_i,\mathcal F)$ for every $i$.

**Proof.** Choose a flasque resolution $\mathcal F\to\mathcal G^\bullet$, for instance the Godement
resolution. Then $\xi$ is represented by a section $s\in\Gamma(X,\mathcal G^p)$ with $ds=0$.
Because the resolution is exact as a complex of sheaves and $p\ge1$, the sheaf-theoretic kernel of
$d$ in degree $p$ is the image of $d$ from degree $p-1$; so every point has an open neighborhood
$U$ and a section $t\in\Gamma(U,\mathcal G^{p-1})$ with $dt=s|_U$. Restriction of a flasque
resolution is a flasque resolution of $\mathcal F|_U$, so $H^p(U,\mathcal F)$ is computed by
$\Gamma(U,\mathcal G^\bullet)$ and $\xi|_U$ is the class of $s|_U=dt$, which is zero. $\square$

### 3.2 Čech complexes and the comparison spectral sequence

Čech cohomology is the naive answer to the gluing question: take sections on the members of a
cover, compare on overlaps, compare the comparisons. It is computable, it is manifestly finite when
the cover is finite, and it is what one actually writes down. What it is not, in general, is
cohomology. The discrepancy is entirely due to the possibility that the members of the cover
themselves carry cohomology, and it is measured by a spectral sequence which we now construct. The
sequence has two uses in this book: read one way it says that a cover with acyclic pieces computes
cohomology, which is the Čech model of Chapter 4; read the other way it converts vanishing of Čech
cohomology for a family of covers into vanishing of genuine cohomology, which is the route to
Serre's theorem in Section 3.3.

Let $\mathfrak U=(U_i)_{i\in I}$ be an open cover of $X$, and write
$U_{i_0\ldots i_p}=U_{i_0}\cap\cdots\cap U_{i_p}$. For a presheaf $\mathcal P$ of abelian groups on
$X$ set

$$
\check C^p(\mathfrak U,\mathcal P)=\prod_{(i_0,\ldots,i_p)\in I^{p+1}}
\mathcal P(U_{i_0\ldots i_p}),\qquad
(d\sigma)_{i_0\ldots i_{p+1}}=\sum_{k=0}^{p+1}(-1)^k
\sigma_{i_0\ldots\widehat{i_k}\ldots i_{p+1}}\big|_{U_{i_0\ldots i_{p+1}}} .
$$

A cochain is **alternating** if it vanishes whenever two indices coincide and changes sign under a
transposition of indices; the alternating cochains form a subcomplex
$\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal P)$. Choosing a total order on $I$ identifies
$\check C^p_{\mathrm{alt}}$ with $\prod_{i_0<\cdots<i_p}\mathcal P(U_{i_0\ldots i_p})$, the
**ordered** complex; this is the complex of Chapter 1 when $X=\operatorname{Spec}A$, the cover is
by principal opens, and $\mathcal P$ is a tilde sheaf. We write
$\check H^p(\mathfrak U,\mathcal P)$ for the cohomology of the alternating complex. Every statement
below refers to the alternating complex and holds verbatim, with the same proof, for the full one;
Corollary 4.5 will show that in the situation we actually use — a cover whose finite intersections
are acyclic — the inclusion of the alternating complex into the full complex is a
quasi-isomorphism, so the two conventions agree there.

**Lemma 3.5 (sheafified Čech resolution).** Let $\mathcal G$ be a sheaf on $X$ and let
$j_{i_0\ldots i_p}:U_{i_0\ldots i_p}\to X$ be the inclusions. Put

$$
\mathcal C^p(\mathfrak U,\mathcal G)=\Bigl[\prod_{(i_0,\ldots,i_p)}
(j_{i_0\ldots i_p})_*\bigl(\mathcal G|_{U_{i_0\ldots i_p}}\bigr)\Bigr]_{\mathrm{alt}},
$$

the alternating part of the displayed product, so that
$\Gamma(X,\mathcal C^p(\mathfrak U,\mathcal G))=\check C^p_{\mathrm{alt}}(\mathfrak U,\mathcal G)$.
Then the augmented complex

$$
0\longrightarrow\mathcal G\longrightarrow\mathcal C^0(\mathfrak U,\mathcal G)
\longrightarrow\mathcal C^1(\mathfrak U,\mathcal G)\longrightarrow\cdots
$$

is exact, and if $\mathcal G$ is flasque then every $\mathcal C^p(\mathfrak U,\mathcal G)$ is
flasque.

**Proof.** Exactness may be checked locally, so fix $j\in I$ and work over an open
$V\subseteq U_j$. For $\sigma\in\Gamma(V,\mathcal C^p)$ define
$(h\sigma)_{i_0\ldots i_{p-1}}=\sigma_{j\,i_0\ldots i_{p-1}}$, which makes sense because
$V\cap U_{i_0\ldots i_{p-1}}\subseteq V\cap U_{j\,i_0\ldots i_{p-1}}$ is an equality for
$V\subseteq U_j$, and which is again alternating. In degree $0$ interpret $h$ as
$\sigma\mapsto\sigma_j$, landing in $\mathcal G(V)$. A direct computation of the two sums gives
$dh+hd=\mathrm{id}$ on the augmented complex over $V$: all terms of $hd\sigma$ except the one
omitting the inserted index $j$ cancel against $dh\sigma$. So the augmented complex restricted to
$U_j$ is contractible, in particular exact, and the $U_j$ cover $X$. Flasqueness is Lemma 3.1(4),
the alternating part being a direct factor of the product. $\square$

**Lemma 3.6 (Čech vanishing for flasque sheaves).** If $\mathcal G$ is flasque then
$\check H^0(\mathfrak U,\mathcal G)=\Gamma(X,\mathcal G)$ and
$\check H^p(\mathfrak U,\mathcal G)=0$ for $p>0$, for every open cover $\mathfrak U$.

**Proof.** By Lemma 3.5 the augmented complex of sheaves is exact with flasque terms. Break it into
short exact sequences $0\to\mathcal Z^p\to\mathcal C^p\to\mathcal Z^{p+1}\to0$ with
$\mathcal Z^0=\mathcal G$. Inductively each $\mathcal Z^p$ is flasque by Lemma 3.1(2), so by
Lemma 3.1(1) each sequence remains exact after $\Gamma(X,-)$. Splicing them back together shows
that $0\to\Gamma(X,\mathcal G)\to\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal G)$ is
exact. $\square$

**Theorem 3.7 (Čech-to-derived comparison).** Let $\mathfrak U$ be an open cover of $X$ and
$\mathcal F$ a sheaf of abelian groups. Let $\underline H^q(\mathcal F)$ denote the presheaf
$V\mapsto H^q(V,\mathcal F)$. There is a first-quadrant, strongly convergent spectral sequence

$$
E_2^{p,q}=\check H^p\bigl(\mathfrak U,\underline H^q(\mathcal F)\bigr)
\Longrightarrow H^{p+q}(X,\mathcal F),
$$

whose edge map $H^n(X,\mathcal F)\to E_2^{0,n}$ is the map sending a class to the family of its
restrictions to the members of $\mathfrak U$.

**Proof.** Choose the Godement resolution $\mathcal F\to\mathcal G^\bullet$ of Proposition 3.3, all
of whose terms are flasque, and form the first-quadrant double complex

$$
K^{p,q}=\check C^p_{\mathrm{alt}}(\mathfrak U,\mathcal G^q).
$$

By Book 7a, Section 7.2, its totalization carries two strongly convergent spectral sequences.

Filter so that vertical cohomology is taken first. For fixed $p$ the complex $K^{p,\bullet}$ is a
product of the complexes $\Gamma(U_{i_0\ldots i_p},\mathcal G^\bullet)$, and products of complexes
of abelian groups have cohomology the product of the cohomologies. Restrictions of flasque sheaves
are flasque, so $\mathcal G^\bullet|_V$ is a flasque resolution of $\mathcal F|_V$ and computes
$H^q(V,\mathcal F)$ by Proposition 3.2(2). Hence
${}'E_1^{p,q}=\check C^p_{\mathrm{alt}}(\mathfrak U,\underline H^q(\mathcal F))$, and taking
horizontal cohomology gives the asserted $E_2$ page.

Filter the other way. For fixed $q$ the row $K^{\bullet,q}$ is the alternating Čech complex of the
flasque sheaf $\mathcal G^q$, so by Lemma 3.6 its cohomology is $\Gamma(X,\mathcal G^q)$
concentrated in $p=0$. That spectral sequence therefore degenerates at $E_2$ and identifies the
cohomology of the totalization with $H^n(\Gamma(X,\mathcal G^\bullet))=H^n(X,\mathcal F)$. The
edge map is induced by the inclusion of the column $p=0$, which on cochains is precisely
restriction of a class to the members of the cover. $\square$

The spectral sequence immediately yields the criterion we need. Its hypothesis concerns only
finite covers, which is what makes it usable on spectra of rings.

**Theorem 3.8 (vanishing criterion).** Let $X$ be a topological space and $\mathcal B$ a basis of
quasi-compact open sets closed under finite intersection. Let $\mathcal F$ be a sheaf of abelian
groups such that

$$
\check H^p(\mathfrak V,\mathcal F)=0\qquad\text{for all }p>0
$$

whenever $U\in\mathcal B$ and $\mathfrak V$ is a finite cover of $U$ by members of $\mathcal B$.
Then $H^p(U,\mathcal F)=0$ for every $U\in\mathcal B$ and every $p>0$.

**Proof.** Induct on $p$, the statement being empty for $p=0$; assume $H^t(W,\mathcal F)=0$ for all
$W\in\mathcal B$ and all $0<t<p$. Fix $U\in\mathcal B$ and a finite cover
$\mathfrak V=(V_1,\ldots,V_n)$ of $U$ by members of $\mathcal B$, and apply Theorem 3.7 on the
space $U$. All the intersections $V_{i_0\ldots i_s}$ lie in $\mathcal B$, so for $0<t<p$ the
presheaf $\underline H^t(\mathcal F)$ vanishes on every term of the Čech complex and
$E_2^{s,t}=0$. For $t=0$ and $s>0$ we have $E_2^{s,0}=\check H^s(\mathfrak V,\mathcal F)=0$ by
hypothesis. Hence in total degree $p$ the only possibly nonzero term of the $E_2$ page is
$E_2^{0,p}$, and strong convergence gives an injection

$$
H^p(U,\mathcal F)\hookrightarrow E_2^{0,p}\subseteq\prod_iH^p(V_i,\mathcal F),
$$

which by Theorem 3.7 is the restriction map. Now let $\xi\in H^p(U,\mathcal F)$. By Lemma 3.4 there
is an open cover of $U$ on which $\xi$ restricts to zero; refining it by basis elements and
extracting a finite subcover, possible since $U$ is quasi-compact, we obtain a finite cover
$\mathfrak V$ of $U$ by members of $\mathcal B$ with $\xi|_{V_i}=0$ for all $i$. The displayed
injection gives $\xi=0$. $\square$

### 3.3 Serre's affine vanishing theorem

All the pieces are now in place, and they fit together in one paragraph. On the spectrum of a ring
the principal opens form a basis of quasi-compact sets closed under finite intersection; a
quasi-coherent sheaf has modules of sections over them; a finite cover of a principal open by
principal opens is a unimodular family after inverting one element; and Chapter 1 computed the
Čech cohomology of exactly that configuration. The vanishing criterion converts the computation
into a theorem about derived functors.

**Theorem 3.9 (Serre).** Let $A$ be a ring, $X=\operatorname{Spec}A$, and let $\mathcal F$ be a
quasi-coherent $\mathcal O_X$-module. Then

$$
H^p(X,\mathcal F)=0\qquad\text{for all }p>0 .
$$

**Proof.** Take $\mathcal B$ to be the set of principal opens $D(f)$, $f\in A$. It is a basis, each
of its members is quasi-compact, and it is closed under finite intersection because
$D(f)\cap D(g)=D(fg)$. We verify the hypothesis of Theorem 3.8.

Let $U=D(f)$ and let $\mathfrak V$ be a finite cover of $U$ by principal opens. Under the canonical
isomorphism $D(f)\simeq\operatorname{Spec}A_f$ the restriction $\mathcal F|_{D(f)}$ is
quasi-coherent, hence equals $\widetilde{M}$ for the $A_f$-module $M=\Gamma(D(f),\mathcal F)$ by
Theorem 2.3, and each member of $\mathfrak V$ is a principal open of $\operatorname{Spec}A_f$.
Replacing $A$ by $A_f$ and $\mathcal F$ by $\widetilde M$, we may assume $U=X=\operatorname{Spec}A$
and $\mathfrak V=(D(g_1),\ldots,D(g_n))$ with $g_1,\ldots,g_n\in A$. That these cover $X$ means
precisely that $g_1,\ldots,g_n$ generate the unit ideal.

Because $D(g_{i_0})\cap\cdots\cap D(g_{i_p})=D(g_{i_0}\cdots g_{i_p})$ and
$\Gamma(D(g),\widetilde M)=M_g$, the ordered Čech complex of $\mathfrak V$ with coefficients in
$\mathcal F$ is

$$
\check C^p_{\mathrm{alt}}(\mathfrak V,\mathcal F)
=\prod_{i_0<\cdots<i_p}M_{g_{i_0}\cdots g_{i_p}}
=\check C^p(\underline g,M),
$$

the complex of Chapter 1 for the unimodular family $\underline g=(g_1,\ldots,g_n)$. By
Corollary 1.4 its cohomology is $M$ in degree $0$ and zero in positive degrees. So
$\check H^p(\mathfrak V,\mathcal F)=0$ for $p>0$, the hypothesis of Theorem 3.8 holds, and
$H^p(D(f),\mathcal F)=0$ for every $f$ and every $p>0$. Taking $f=1$ gives the theorem. $\square$

Notice what the proof did not use. There is no noetherian hypothesis, no finiteness assumption on
$\mathcal F$, and no hypothesis on the ring $A$ whatsoever; the only inputs are Theorem 1.1, the
affine criterion of Section 2.2, and the general machinery of Sections 3.1 and 3.2. This is exactly
the non-circularity promised in the proof of Theorem 2.8, whose remaining step we can now complete,
and it is also why the theory survives the base changes to non-noetherian rings that later
applications perform.

**Corollary 3.10.** Let $X$ be a scheme.

1. If $U\subseteq X$ is an affine open and $\mathcal F$ is quasi-coherent, then
   $H^p(U,\mathcal F)=0$ for $p>0$; affine opens are acyclic for quasi-coherent sheaves.
2. If $0\to\mathcal F'\to\mathcal F\to\mathcal F''\to0$ is an exact sequence of
   $\mathcal O_X$-modules with $\mathcal F'$ quasi-coherent, then
   $0\to\Gamma(U,\mathcal F')\to\Gamma(U,\mathcal F)\to\Gamma(U,\mathcal F'')\to0$ is exact for
   every affine open $U$. In particular the proof of Theorem 2.8 is complete, and
   $\mathrm{QCoh}(X)$ is closed under extensions.

**Proof.** (1) is Theorem 3.9 applied to $U$, using that $\mathcal F|_U$ is quasi-coherent. (2) The
long exact cohomology sequence on $U$ ends the segment
$\Gamma(U,\mathcal F)\to\Gamma(U,\mathcal F'')\to H^1(U,\mathcal F')$, and the last group vanishes
by (1). $\square$

**Corollary 3.11 (affine morphisms are cohomologically invisible).** Let $f:X\to Y$ be an affine
morphism of schemes and $\mathcal F$ quasi-coherent on $X$. Then $R^pf_*\mathcal F=0$ for $p>0$ and

$$
H^p(Y,f_*\mathcal F)\;\simeq\;H^p(X,\mathcal F)\qquad\text{for all }p\ge0 .
$$

**Proof.** By Proposition 3.2(4) the sheaf $R^pf_*\mathcal F$ is the sheafification of
$V\mapsto H^p(f^{-1}V,\mathcal F)$. For $V$ affine, $f^{-1}V$ is affine and $\mathcal F$ restricted
to it is quasi-coherent, so this group vanishes for $p>0$ by Theorem 3.9; affine opens form a
basis, so the sheafification is zero. The Leray spectral sequence of Proposition 3.2(4) therefore
degenerates, giving the displayed isomorphism. $\square$

The special case of a closed immersion $i:Z\to X$ recovers, with a different proof,
$H^p(X,i_*\mathcal G)=H^p(Z,\mathcal G)$: cohomology of a sheaf on a closed subscheme may be
computed on the ambient scheme, which is what allows projective methods on $\mathbf P^r_A$ to
control cohomology on all its closed subschemes.

It is worth being clear about what has and has not been proved. Theorem 3.9 says that affineness
implies vanishing. The converse — Serre's criterion, that a quasi-compact scheme all of whose
quasi-coherent sheaves have vanishing $H^1$ is affine — is true but is not needed anywhere in this
book or in what follows it, and we do not prove it. Nor does Theorem 3.9 say anything about
non-quasi-coherent sheaves on an affine scheme: the extension by zero $j_!\mathcal O_U$ of
Section 2.2 has nonvanishing $H^1$ on the spectrum of a discrete valuation ring, since
$\Gamma(X,j_!\mathcal O_U)=0$ while the sequence
$0\to j_!\mathcal O_U\to\mathcal O_X\to i_*(R/\pi)\to0$ has
$\Gamma(X,\mathcal O_X)=R\to R/\pi$ surjective — so $H^1(X,j_!\mathcal O_U)$ contains the cokernel
of $0\to R/\pi$, which is nonzero. Quasi-coherence is not a technical convenience in Theorem 3.9;
it is the hypothesis.

Finally, the theorem supplies exactly the acyclicity input that the abstract Čech comparison of
Book 7a, Section 7.4 requires. If $X$ is separated, the intersections of affine opens are affine,
hence acyclic for quasi-coherent sheaves by Corollary 3.10, and one finite affine cover computes
everything. Chapter 4 develops this into the computational tool that the rest of the book uses.

## 4. Čech models on separated schemes

### 4.1 Alternating and ordered complexes

Before combining Theorem 3.9 with the comparison spectral sequence we record why the alternating
convention, rather than the full one, is the convention to compute with. The reason is a single
line of bookkeeping with large consequences: an alternating cochain vanishes as soon as two of its
indices coincide, so a cover with $n$ members supports no nonzero alternating cochains in degrees
$\ge n$. All the finiteness statements of this book — bounded cohomological dimension, finite
complexes of modules representing $R\Gamma$, matrices computing cohomology after base change —
trace back to that observation.

**Lemma 4.1.** Let $\mathfrak U=(U_i)_{i\in I}$ be an open cover of $X$ with $I$ finite of
cardinality $n$, and let $\mathcal P$ be a presheaf of abelian groups.

1. $\check C^p_{\mathrm{alt}}(\mathfrak U,\mathcal P)=0$ for $p\ge n$; the alternating complex has
   length at most $n-1$.
2. Choosing a total order on $I$ gives an isomorphism
   $\check C^p_{\mathrm{alt}}(\mathfrak U,\mathcal P)\simeq
   \prod_{i_0<\cdots<i_p}\mathcal P(U_{i_0\ldots i_p})$ of complexes, so the alternating complex is
   the ordered complex; the alternating complex itself is defined without reference to an order,
   and consequently $\check H^p(\mathfrak U,\mathcal P)$ does not depend on the ordering used to
   compute it.
3. If $\mathcal P$ is a sheaf then $\check H^0(\mathfrak U,\mathcal P)=\Gamma(X,\mathcal P)$.

**Proof.** (1) A tuple $(i_0,\ldots,i_p)$ with $p+1>n$ entries in a set of $n$ elements has a
repetition, and an alternating cochain vanishes there. (2) An alternating cochain is determined by
its values on strictly increasing tuples, and any prescription of such values extends uniquely; the
differential matches by construction. (3) This is the sheaf axiom: $\check H^0$ is the equalizer of
the two maps $\prod_i\mathcal P(U_i)\rightrightarrows\prod_{i<j}\mathcal P(U_{ij})$. $\square$

### 4.2 The finite affine Čech model

The geometric input is separatedness. On a separated scheme the intersection of two affine opens is
affine, hence acyclic for quasi-coherent sheaves by Corollary 3.10, and the same then holds for all
higher intersections. This is exactly the hypothesis of the abstract Čech comparison theorem of
Book 7a, Section 7.4, and the spectral sequence of Theorem 3.7 delivers the conclusion in one step.

**Theorem 4.2 (Čech model).** Let $X$ be a scheme, $\mathcal F$ a quasi-coherent
$\mathcal O_X$-module, and $\mathfrak U=(U_1,\ldots,U_n)$ a finite cover of $X$ by affine opens all
of whose finite intersections are affine — for instance any finite affine open cover of a separated
scheme. Then the natural map

$$
\check H^p(\mathfrak U,\mathcal F)\xrightarrow{\ \sim\ }H^p(X,\mathcal F)
$$

is an isomorphism for every $p$; equivalently, the finite complex
$\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F)$, of length at most $n-1$, represents
$R\Gamma(X,\mathcal F)$.

**Proof.** Apply Theorem 3.7 to the cover $\mathfrak U$. Every intersection
$U_{i_0\ldots i_p}$ is affine and $\mathcal F$ restricted to it is quasi-coherent, so
$H^q(U_{i_0\ldots i_p},\mathcal F)=0$ for $q>0$ by Corollary 3.10. Hence the presheaf
$\underline H^q(\mathcal F)$ vanishes on every term of the Čech complex for $q>0$, so
$E_2^{p,q}=0$ for $q>0$, while $E_2^{p,0}=\check H^p(\mathfrak U,\mathcal F)$. A first-quadrant
spectral sequence concentrated in the row $q=0$ degenerates and identifies the abutment with that
row. The edge map is the natural comparison map, and Lemma 4.1(1) bounds the length. $\square$

If $X$ is separated, the criterion recalled in Section 1.2 shows that all the intersections in a
finite affine cover are affine, so the theorem applies to every finite affine open cover of a
quasi-compact separated scheme. The relative form is the one used later: if $f:X\to S$ is a
quasi-compact separated morphism and $S=\operatorname{Spec}A$ is affine, then $X$ is a
quasi-compact separated scheme and each $\Gamma(U_{i_0\ldots i_p},\mathcal F)$ is an $A$-module, so
$R\Gamma(X,\mathcal F)$ is represented by a finite complex of $A$-modules, functorially in
$\mathcal F$. Chapter 5 exploits precisely this.

Two remarks delimit the theorem. First, quasi-coherence is essential, since it is what makes affine
opens acyclic. Second, separatedness is what makes the intersections affine, not a technical
convenience: for a nonseparated scheme, such as the affine line with a doubled origin over a field,
the intersection of the two evident affine charts is not affine, and the two-term Čech complex of
that cover computes something else. The nonseparated case is handled below by induction, at the
cost of a longer complex rather than a wrong one.

**Theorem 4.3 (Mayer–Vietoris).** Let $X=U\cup V$ be a union of two open subsets and let
$\mathcal F$ be any sheaf of abelian groups on $X$. There is a long exact sequence

$$
\cdots\to H^p(X,\mathcal F)\to H^p(U,\mathcal F)\oplus H^p(V,\mathcal F)
\to H^p(U\cap V,\mathcal F)\to H^{p+1}(X,\mathcal F)\to\cdots,
$$

functorial in $\mathcal F$, with the middle map the difference of restrictions.

**Proof.** Choose a flasque resolution $\mathcal F\to\mathcal G^\bullet$, for example the Godement
resolution. For each $q$ the sequence of abelian groups

$$
0\to\Gamma(X,\mathcal G^q)\to\Gamma(U,\mathcal G^q)\oplus\Gamma(V,\mathcal G^q)
\to\Gamma(U\cap V,\mathcal G^q)\to0
$$

is exact: exactness on the left and in the middle is the sheaf axiom for the cover $\{U,V\}$, and
surjectivity on the right holds because $\mathcal G^q$ is flasque, so any section over $U\cap V$
extends to $U$ and may be paired with $0$ on $V$. Restrictions of flasque sheaves are flasque, so
each of the three complexes computes the cohomology of $\mathcal F$ on the corresponding open by
Proposition 3.2. The long exact sequence of the resulting short exact sequence of complexes is the
assertion. $\square$

**Corollary 4.4 (long exact sequence in the Čech model).** Let $X$ be quasi-compact and separated,
$\mathfrak U$ a finite affine open cover, and $0\to\mathcal F'\to\mathcal F\to\mathcal F''\to0$ an
exact sequence of quasi-coherent sheaves. Then

$$
0\to\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F')
\to\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F)
\to\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F'')\to0
$$

is a short exact sequence of finite complexes, and its long exact cohomology sequence is the long
exact sequence of $H^\bullet(X,-)$.

**Proof.** Each term of the Čech complexes is a product of groups of sections over affine opens,
where the sequence of sections is exact by Corollary 3.10(2); products of exact sequences of
abelian groups are exact. Theorem 4.2 identifies the three complexes with $R\Gamma$ of the three
sheaves compatibly with the maps, and the connecting maps agree because both long exact sequences
arise from the same short exact sequence of complexes computing $R\Gamma$. $\square$

**Corollary 4.5 (alternating versus full).** In the situation of Theorem 4.2 the inclusion
$\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F)\subseteq
\check C^\bullet(\mathfrak U,\mathcal F)$ is a quasi-isomorphism, both complexes computing
$H^\bullet(X,\mathcal F)$.

**Proof.** Lemma 3.5, Lemma 3.6, and Theorem 3.7 hold with the same proofs for the full Čech
complex, whose sheafified augmented version is contractible over each member of the cover by the
same homotopy. The argument of Theorem 4.2 therefore applies to it as well, and the inclusion
induces the identity on the common abutment $H^\bullet(X,\mathcal F)$, being compatible with the
edge maps. $\square$

### 4.3 Higher direct images and dimension bounds

Relative cohomology is the cohomology of the fibers of a morphism, organized into sheaves on the
base. The sheaf $R^pf_*\mathcal F$ was defined in Proposition 3.2(4) as the sheafification of
$V\mapsto H^p(f^{-1}V,\mathcal F)$; to make it usable we must know that it is quasi-coherent and
that no sheafification is really needed on affine opens of the base. Both follow from one
localization statement, which says that taking cohomology commutes with inverting an element of
the base ring. On a separated source this is visible in the Čech model: inverting $g$ inverts it in
every term of a finite complex, and localization is exact. The general case is an induction on the
number of separated pieces, with Mayer–Vietoris as the inductive step.

**Lemma 4.6 (localization).** Let $A$ be a ring, $S=\operatorname{Spec}A$, let $f:X\to S$ be a
quasi-compact quasi-separated morphism, and let $\mathcal F$ be quasi-coherent on $X$. Then for
every $g\in A$ and every $p$ the natural map

$$
H^p(X,\mathcal F)_g\longrightarrow H^p\bigl(f^{-1}D(g),\mathcal F\bigr)
$$

is an isomorphism of $A_g$-modules.

**Proof.** Since $X$ is quasi-compact it admits a finite cover by affine opens, and affine schemes
are quasi-compact and separated; so $X$ is covered by finitely many quasi-compact separated opens.
We induct on the number $n$ of such opens needed.

Suppose $n=1$, that is, $X$ itself is quasi-compact and separated. Choose a finite affine open
cover $\mathfrak U=(U_i)$; all finite intersections are affine. For an affine open
$U\subseteq X$ with $\Gamma(U,\mathcal O_X)=B$, the open $U\cap f^{-1}D(g)$ is the principal open
of $U$ where the image of $g$ in $B$ is invertible, hence affine, and

$$
\Gamma\bigl(U\cap f^{-1}D(g),\mathcal F\bigr)=\Gamma(U,\mathcal F)_g
=\Gamma(U,\mathcal F)\otimes_AA_g
$$

by Theorem 2.3. Therefore $\mathfrak U$ restricts to a finite affine cover of $f^{-1}D(g)$ with
affine intersections, and

$$
\check C^\bullet_{\mathrm{alt}}\bigl(\mathfrak U|_{f^{-1}D(g)},\mathcal F\bigr)
=\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F)\otimes_AA_g .
$$

Localization is exact, so it commutes with the cohomology of a complex, and Theorem 4.2 applied on
both $X$ and $f^{-1}D(g)$ gives the claim.

For $n>1$ write $X=U\cup W$ with $U$ quasi-compact separated and $W$ a union of $n-1$ quasi-compact
separated opens. Then $U\cap W$ is the union of the $n-1$ opens $U\cap W_j$, each of which is
quasi-compact because $f$ is quasi-separated and $U,W_j$ are quasi-compact opens, and separated
because it is open in $U$. So the inductive hypothesis applies to $U$, to $W$, and to $U\cap W$,
each viewed over $S$. Mayer–Vietoris (Theorem 4.3) for $X=U\cup W$ and for
$f^{-1}D(g)=\bigl(U\cap f^{-1}D(g)\bigr)\cup\bigl(W\cap f^{-1}D(g)\bigr)$ gives two long exact
sequences; localizing the first at $g$ preserves exactness, and the restriction maps give a
morphism from it to the second. Four out of every five comparison maps are isomorphisms by
induction, so the five lemma gives the remaining one. $\square$

**Theorem 4.7 (quasi-coherence of higher direct images).** Let $f:X\to Y$ be a quasi-compact
quasi-separated morphism of schemes and $\mathcal F$ a quasi-coherent $\mathcal O_X$-module. Then
every $R^pf_*\mathcal F$ is quasi-coherent, and for every affine open
$V=\operatorname{Spec}A\subseteq Y$,

$$
R^pf_*\mathcal F|_V=\widetilde{H^p(f^{-1}V,\mathcal F)} .
$$

**Proof.** By Proposition 3.2(4), $R^pf_*\mathcal F$ is the sheafification of the presheaf
$V'\mapsto H^p(f^{-1}V',\mathcal F)$. Fix an affine open $V=\operatorname{Spec}A$ and put
$M=H^p(f^{-1}V,\mathcal F)$. By Lemma 4.6 the presheaf restricted to the basis of principal opens
of $V$ is $D(g)\mapsto M_g$, which by Proposition 2.1 is already a sheaf on that basis, namely
$\widetilde M$. A presheaf whose restriction to a basis is a sheaf has the corresponding sheaf as
its sheafification, so $R^pf_*\mathcal F|_V=\widetilde M$. Quasi-coherence now follows from
Corollary 2.6. $\square$

For $p=0$ this recovers Theorem 2.10. The theorem is the reason the entire relative theory can be
phrased over affine bases: a statement about $R^pf_*\mathcal F$ is a statement about the
$A$-modules $H^p(f^{-1}V,\mathcal F)$, and those are computed by a finite complex whenever $f$ is
separated.

**Corollary 4.8 (cohomological dimension bounds).** Let $\mathcal F$ be quasi-coherent.

1. If $X$ is separated and covered by $n$ affine opens, then $H^p(X,\mathcal F)=0$ for $p\ge n$.
2. If $f:X\to Y$ is quasi-compact and separated and the preimage of every affine open of $Y$ is
   covered by $n$ affine opens, then $R^pf_*\mathcal F=0$ for $p\ge n$.
3. If $X$ is quasi-compact and quasi-separated, there is an integer $d$, depending only on $X$,
   with $H^p(X,\mathcal F)=0$ for $p>d$ and all quasi-coherent $\mathcal F$.

**Proof.** (1) By Theorem 4.2 the cohomology is computed by the alternating Čech complex of that
cover, which vanishes in degrees $\ge n$ by Lemma 4.1(1). (2) Combine (1) with Theorem 4.7. (3)
Cover $X$ by finitely many quasi-compact separated opens and induct as in Lemma 4.6: if $X=U\cup W$
with bounds $d_U,d_W,d_{U\cap W}$ available for the three pieces, Mayer–Vietoris gives the bound
$\max(d_U,d_W,d_{U\cap W}+1)$ for $X$, and the base case is (1). $\square$

Part (1) is the form used constantly later. On $\mathbf P^r_A$, covered by the $r+1$ standard
charts, it says that cohomology of quasi-coherent sheaves vanishes above degree $r$; that single
bound is what makes descending induction on the degree a finite argument, and every projective
vanishing theorem proved in later volumes begins there.

**Corollary 4.9 (Leray for quasi-coherent sheaves).** Let $f:X\to Y$ be a quasi-compact
quasi-separated morphism and $\mathcal F$ quasi-coherent on $X$. There is a strongly convergent
first-quadrant spectral sequence of quasi-coherent cohomology

$$
E_2^{p,q}=H^p\bigl(Y,R^qf_*\mathcal F\bigr)\Longrightarrow H^{p+q}(X,\mathcal F),
$$

all of whose $E_2$ terms are the cohomology groups of quasi-coherent sheaves on $Y$. If $f$ is
affine it degenerates to $H^p(Y,f_*\mathcal F)=H^p(X,\mathcal F)$; if $Y$ is affine it degenerates
to the edge isomorphism $H^n(X,\mathcal F)=\Gamma(Y,R^nf_*\mathcal F)$.

**Proof.** The spectral sequence is the Leray sequence, available by Proposition 3.2(4); its terms
are quasi-coherent by Theorem 4.7. The affine case is Corollary 3.11. If $Y$ is affine then
$E_2^{p,q}=0$ for $p>0$ by Theorem 3.9, since $R^qf_*\mathcal F$ is quasi-coherent, and the
sequence collapses to the row $p=0$. $\square$

The last degeneration is worth restating, since it is the form in which relative cohomology is
computed in practice: over an affine base, the higher direct image sheaf has no cohomology of its
own, so all the information in $R\Gamma(X,\mathcal F)$ sits in the modules
$H^n(X,\mathcal F)=\Gamma(Y,R^nf_*\mathcal F)$. Combined with the finite Čech model of
Theorem 4.2, this reduces every relative question over an affine base to a finite complex of
modules — the object Chapter 5 now subjects to base change.

## 5. Base change, colimits, and vanishing

### 5.1 Coefficient change and flat base change

A family of schemes over $\operatorname{Spec}A$ is studied by changing the ring: restricting to a
fiber, extending scalars, completing, passing to a residue field. The question is always the same.
The cohomology of the sheaf on the new scheme is defined by a new derived functor on a new space;
in what sense is it computed by the old answer? The Čech model turns this into a question about a
complex of modules, where the answer is visible: the model is a _finite complex of $A$-modules
whose formation commutes with scalar extension on the nose_, before taking cohomology. Every base
change statement in this section is that observation plus an exactness property of the ring map.

Throughout, $A$ is a ring, $S=\operatorname{Spec}A$, and $f:X\to S$ is a quasi-compact separated
morphism, so that $X$ has a finite affine open cover $\mathfrak U=(U_1,\ldots,U_n)$ all of whose
intersections are affine. For an $A$-algebra $B$ write

$$
X_B=X\times_S\operatorname{Spec}B,\qquad
\mathcal F_B=\mathrm{pr}^*\mathcal F,
$$

and for an $A$-module $M$ write $\mathcal F\otimes_AM=\mathcal F\otimes_{\mathcal O_X}f^*\widetilde M$,
a quasi-coherent sheaf with $\Gamma(U,\mathcal F\otimes_AM)=\Gamma(U,\mathcal F)\otimes_AM$ on
affine opens $U$. A quasi-coherent sheaf $\mathcal F$ is **flat over $A$** if $\Gamma(U,\mathcal F)$
is a flat $A$-module for every affine open $U\subseteq X$; since flatness of a module over $A$ may
be tested after localizing at the primes of the ring of the affine open, this is equivalent to
flatness of every stalk $\mathcal F_x$ over $\mathcal O_{S,f(x)}$.

**Lemma 5.1 (the model is universal).** With the notation above, put
$C^\bullet=\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F)$, a complex of $A$-modules
concentrated in degrees $0,\ldots,n-1$ and representing $R\Gamma(X,\mathcal F)$. Then:

1. for every $A$-algebra $B$, the base-changed cover $\mathfrak U_B=(U_{i,B})$ is a finite affine
   open cover of the separated scheme $X_B$ with affine intersections, and there is an equality of
   complexes of $B$-modules

   $$
   \check C^\bullet_{\mathrm{alt}}(\mathfrak U_B,\mathcal F_B)=C^\bullet\otimes_AB;
   $$

2. for every $A$-module $M$ there is an equality
   $\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F\otimes_AM)=C^\bullet\otimes_AM$;
3. if $\mathcal F$ is flat over $A$, every term of $C^\bullet$ is a flat $A$-module.

**Proof.** (1) Separatedness and quasi-compactness are preserved by base change, and
$U_{i,B}=U_i\times_S\operatorname{Spec}B$ is the spectrum of $\Gamma(U_i,\mathcal O_X)\otimes_AB$,
hence affine; the same applies to the intersections, since
$(U_{i_0}\cap\cdots\cap U_{i_p})_B=U_{i_0,B}\cap\cdots\cap U_{i_p,B}$. For an affine open
$U\subseteq X$ with $\Gamma(U,\mathcal O_X)=R$ and $\Gamma(U,\mathcal F)=M_U$, the pullback of
$\mathcal F$ to $U_B=\operatorname{Spec}(R\otimes_AB)$ is $\widetilde{M_U\otimes_R(R\otimes_AB)}$ by
Theorem 2.7(4), whose module of sections is $M_U\otimes_AB$. Taking products over the tuples gives
the displayed equality, the differentials being the base changes of the original ones. (2) The same
computation with $f^*\widetilde M$ in place of the base change. (3) Each term is a finite product of
modules $\Gamma(U_{i_0\ldots i_p},\mathcal F)$ over affine opens, flat by hypothesis, and a finite
product of flat modules is flat. $\square$

Part (1) is an equality, not merely a quasi-isomorphism, and the matrices of the differentials are
fixed before $B$ is chosen. That is the entire content of base change; the rest is bookkeeping about
when $\otimes_AB$ may be moved through cohomology.

**Theorem 5.2 (coefficient change).** Let $f:X\to S=\operatorname{Spec}A$ be quasi-compact and
separated and let $\mathcal F$ be quasi-coherent and flat over $A$. Then:

1. for every $A$-module $M$ the complex $C^\bullet\otimes_AM$ computes
   $R\Gamma(X,\mathcal F\otimes_AM)$, and there is a canonical isomorphism in the derived category

   $$
   R\Gamma(X,\mathcal F)\otimes^L_AM\;\xrightarrow{\ \sim\ }\;
   R\Gamma(X,\mathcal F\otimes_AM);
   $$

2. for every $A$-algebra $B$ there is a canonical isomorphism

   $$
   B\otimes^L_AR\Gamma(X,\mathcal F)\;\xrightarrow{\ \sim\ }\;
   R\Gamma\bigl(X_B,\mathcal F_B\bigr).
   $$

**Proof.** By Lemma 5.1(3) the finite complex $C^\bullet$ consists of flat $A$-modules and is
bounded, hence is K-flat by the criterion recalled in Book 7a, Section 3.8; therefore
$C^\bullet\otimes_AM$ computes $C^\bullet\otimes^L_AM=R\Gamma(X,\mathcal F)\otimes^L_AM$. On the
other hand Lemma 5.1(2) identifies $C^\bullet\otimes_AM$ with the Čech model of
$\mathcal F\otimes_AM$ for the cover $\mathfrak U$, which computes
$R\Gamma(X,\mathcal F\otimes_AM)$ by Theorem 4.2, the sheaf $\mathcal F\otimes_AM$ being
quasi-coherent. This proves (1). For (2), apply the same argument with Lemma 5.1(1): the complex
$C^\bullet\otimes_AB$ is simultaneously a representative of $B\otimes^L_AR\Gamma(X,\mathcal F)$ and
the Čech model of $\mathcal F_B$ on $X_B$ for the cover $\mathfrak U_B$, which computes
$R\Gamma(X_B,\mathcal F_B)$ by Theorem 4.2. $\square$

Taking $M=B$ in (1) and comparing with (2) shows that $\mathcal F\otimes_AB$ and the pullback
$\mathcal F_B$ have the same cohomology, as they must: one is computed on $X$ and the other on
$X_B$, and the two Čech complexes are equal. In practice statement (2) is used through its
cohomological consequence: the cohomology of $\mathcal F_B$ is computed by the finite complex
$C^\bullet\otimes_AB$, which is one fixed matrix presentation base-changed, so nothing about the
new ring $B$ — noetherian or not, reduced or not — enters the computation.

Flatness of $\mathcal F$ cannot be dropped from Theorem 5.2, since without it $C^\bullet$ need not
be K-flat and $C^\bullet\otimes_AB$ computes the wrong object. It can be dropped, however, if the
ring map itself is flat, because then $\otimes_AB$ is exact and commutes with cohomology directly.

**Theorem 5.3 (flat base change).** Let $f:X\to S=\operatorname{Spec}A$ be quasi-compact and
separated, let $\mathcal F$ be any quasi-coherent sheaf on $X$, and let $A\to B$ be a flat ring
map. Then for every $p$

$$
H^p(X,\mathcal F)\otimes_AB\;\xrightarrow{\ \sim\ }\;H^p\bigl(X_B,\mathcal F_B\bigr).
$$

**Proof.** By Lemma 5.1(1) the cohomology of $\mathcal F_B$ on $X_B$ is the cohomology of
$C^\bullet\otimes_AB$. Since $B$ is flat over $A$, the functor $-\otimes_AB$ is exact and therefore
commutes with the formation of kernels, images, and cohomology of the complex $C^\bullet$.
$\square$

**Corollary 5.4 (flat base change for higher direct images).** Consider a cartesian square

$$
\begin{array}{ccc}
X'&\xrightarrow{\;g'\;}&X\\
\downarrow f'& &\downarrow f\\
S'&\xrightarrow{\;g\;}&S
\end{array}
$$

with $f$ quasi-compact and separated and $g$ flat. Then for every quasi-coherent $\mathcal F$ on
$X$ and every $p$ the base-change map

$$
g^*R^pf_*\mathcal F\longrightarrow R^pf'_*\bigl(g'^*\mathcal F\bigr)
$$

is an isomorphism.

**Proof.** Both sides are quasi-coherent by Theorem 4.7 and their formation is local on $S'$ and on
$S$, so we may assume $S=\operatorname{Spec}A$ and $S'=\operatorname{Spec}B$ affine with $A\to B$
flat. Then Theorem 4.7 identifies the two sides with the tilde sheaves of
$H^p(X,\mathcal F)\otimes_AB$ and $H^p(X_B,\mathcal F_B)$, and Theorem 5.3 identifies those.
$\square$

The special case $B=A_g$ recovers Lemma 4.6, as it must. Another frequently used flat map is the
completion of a noetherian local ring, or a localization at a prime, so Theorem 5.3 lets one
compute cohomology after passing to a local or completed base without changing anything.

We close with the observation that later volumes take as their starting point. When $\mathcal F$ is
flat over $A$, the object $R\Gamma(X,\mathcal F)$ is represented by a bounded complex of flat
$A$-modules of length at most $n-1$; consequently it has finite Tor-amplitude, and for every
$A$-module $M$ there is no ambiguity between derived and underived tensor products. Whether this
complex can be replaced by a bounded complex of _finite projective_ modules is a finiteness
question, requiring properness or projectivity and a coherence hypothesis, and it is not addressed
here; what is supplied here is the flat model together with the universality of its formation,
which is the input such finiteness arguments consume.

### 5.2 Cohomology and filtered colimits

Cohomology is a limit-like construction, built from resolutions and kernels, so there is no formal
reason for it to commute with colimits, and on a general space it does not. Two hypotheses rescue
it, and both are available in the situations we care about. The first is a finite Čech model: if
cohomology is computed by a finite complex whose terms are sections over affines, then it commutes
with filtered colimits because finite products and filtered colimits commute and filtered colimits
are exact. The second is a noetherian topological space, where the sharper statement holds for
arbitrary sheaves of abelian groups; the proof passes to the colimit inside the functorial
resolution of Proposition 3.3, which is exactly the use for which functoriality was demanded.

**Proposition 5.5 (quasi-coherent case).** Let $X$ be a quasi-compact separated scheme and let
$(\mathcal F_\lambda)$ be a filtered system of quasi-coherent sheaves with colimit $\mathcal F$.
Then for every $p$

$$
\operatorname*{colim}_\lambda H^p(X,\mathcal F_\lambda)
\xrightarrow{\ \sim\ }H^p(X,\mathcal F).
$$

**Proof.** Fix a finite affine open cover $\mathfrak U$ with affine intersections. On each affine
open $U$ we have $\Gamma(U,\mathcal F)=\operatorname*{colim}\Gamma(U,\mathcal F_\lambda)$ by
Proposition 2.2(4), since the colimit in $\mathcal O_X$-modules is computed there by the colimit of
modules. The Čech complex involves only finite products of such groups, and finite products commute
with filtered colimits, so
$\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F)
=\operatorname*{colim}_\lambda\check C^\bullet_{\mathrm{alt}}(\mathfrak U,\mathcal F_\lambda)$.
Filtered colimits of abelian groups are exact, hence commute with cohomology of complexes, and
Theorem 4.2 identifies both sides. $\square$

The same holds on a quasi-compact quasi-separated scheme, by the Mayer–Vietoris induction of
Lemma 4.6; we will not need that refinement.

**Proposition 5.6 (noetherian spaces).** Let $X$ be a noetherian topological space and let
$(\mathcal F_\lambda)$ be a filtered system of sheaves of abelian groups with colimit
$\mathcal F$. Then:

1. the presheaf colimit $U\mapsto\operatorname*{colim}\mathcal F_\lambda(U)$ is already a sheaf,
   and equals $\mathcal F$;
2. $\Gamma(X,-)$ commutes with filtered colimits;
3. a filtered colimit of flasque sheaves is flasque;
4. $\operatorname*{colim}_\lambda H^p(X,\mathcal F_\lambda)\xrightarrow{\sim}H^p(X,\mathcal F)$
   for every $p$.

**Proof.** (1) Every open subset of a noetherian space is quasi-compact. Let $\mathcal P$ denote
the presheaf colimit and let $U=\bigcup_iU_i$ be an open cover; choose a finite subcover
$U_{i_1},\ldots,U_{i_m}$. If $s\in\mathcal P(U)$ restricts to zero on every $U_i$, represent $s$ by
$s_\lambda\in\mathcal F_\lambda(U)$; for each $k\le m$ there is $\mu_k\ge\lambda$ killing the
restriction of $s_\lambda$ to $U_{i_k}$, and a common $\mu$ above the finitely many $\mu_k$ makes
$s_\mu$ restrict to zero on a cover of $U$, whence $s_\mu=0$ and $s=0$. Given compatible sections
$s_i\in\mathcal P(U_i)$, represent the finitely many $s_{i_k}$ over a common index $\lambda$;
their finitely many compatibilities on the overlaps $U_{i_k}\cap U_{i_l}$ hold in a filtered
colimit, hence after enlarging $\lambda$ once more; gluing in $\mathcal F_\lambda$ produces
$s\in\mathcal P(U)$ restricting to $s_{i_k}$ for $k\le m$, and the separatedness just proved,
applied on each $U_i$ covered by the $U_i\cap U_{i_k}$, gives $s|_{U_i}=s_i$ for every $i$. So
$\mathcal P$ is a sheaf, and being the presheaf colimit it is the colimit in sheaves.

(2) Immediate from (1). (3) By (1) the restriction maps of the colimit are filtered colimits of the
restriction maps of the $\mathcal F_\lambda$; a filtered colimit of surjections is surjective.

(4) Let $\mathcal C^\bullet(-)$ be the Godement resolution of Proposition 3.3, functorial in the
sheaf. Then $\operatorname*{colim}_\lambda\mathcal C^\bullet(\mathcal F_\lambda)$ is a complex of
flasque sheaves by (3), and it is a resolution of $\mathcal F$ because filtered colimits of sheaves
are exact. By Proposition 3.2(2) it computes $H^p(X,\mathcal F)$. Using (2) and the exactness of
filtered colimits of abelian groups,

$$
H^p(X,\mathcal F)=H^p\Bigl(\operatorname*{colim}_\lambda
\Gamma\bigl(X,\mathcal C^\bullet(\mathcal F_\lambda)\bigr)\Bigr)
=\operatorname*{colim}_\lambda H^p\bigl(\Gamma(X,\mathcal C^\bullet(\mathcal F_\lambda))\bigr)
=\operatorname*{colim}_\lambda H^p(X,\mathcal F_\lambda). \qquad\square
$$

**Corollary 5.7.** Let $X$ be a noetherian scheme and $\mathcal F$ a quasi-coherent sheaf. Then

$$
H^p(X,\mathcal F)=\operatorname*{colim}_{\mathcal G\subseteq\mathcal F\ \mathrm{coherent}}
H^p(X,\mathcal G),
$$

the colimit being over the filtered system of coherent subsheaves of $\mathcal F$.

**Proof.** Combine Theorem 2.11 with Proposition 5.6(4). $\square$

This is the standard device for reducing a statement about quasi-coherent sheaves on a noetherian
scheme to the coherent case, and it is used in exactly that way in the next section, where the
sheaves involved are not even quasi-coherent and Proposition 5.6 is applied in its full generality.

### 5.3 Grothendieck's vanishing theorem

Corollary 4.8 bounded cohomological dimension by the number of affines needed to cover a scheme.
That bound is convenient but crude: it depends on a chosen cover, not on the geometry. The
intrinsic bound is the dimension, and the theorem is purely topological — it holds for every sheaf
of abelian groups on a noetherian space, with no scheme structure and no quasi-coherence. The
statement matters later precisely because it applies to sheaves that are not quasi-coherent, and
because it converts a geometric hypothesis on fiber dimension into a vanishing range.

Recall that the **dimension** of a topological space $X$ is the supremum of the integers $n$ for
which there is a chain $Z_0\subsetneq Z_1\subsetneq\cdots\subsetneq Z_n$ of irreducible closed
subsets of $X$. A noetherian space has finitely many irreducible components, every subspace is
again noetherian, and every open is quasi-compact. If $X$ is irreducible and $Y\subsetneq X$ is
closed, then $\dim Y\le\dim X-1$, since any chain in $Y$ may be extended by $X$ itself.

We use three standard sequences. For an open $j:W\to X$ with closed complement $i:Y\to X$ and any
sheaf $\mathcal G$ on $X$,

$$
0\to j_!(\mathcal G|_W)\to\mathcal G\to i_*(\mathcal G|_Y)\to0
$$

is exact, as one checks on stalks. If $\mathcal G|_W=0$ then $\mathcal G=i_*(\mathcal G|_Y)$. If
$W$ is contained in a closed subset $Y'\subseteq X$, then extension by zero from $W$ to $X$ factors
as extension by zero to $Y'$ followed by $i_{Y'*}$. Finally $H^p(X,i_*\mathcal G)=H^p(Y,\mathcal G)$
for $i$ a closed immersion of spaces, by Proposition 3.2(4). We write $\mathbf Z_W=j_!(\mathbf Z|_W)$
for the extension by zero of the constant sheaf.

**Theorem 5.8 (Grothendieck).** Let $X$ be a noetherian topological space of finite dimension $d$
and let $\mathcal F$ be any sheaf of abelian groups on $X$. Then

$$
H^p(X,\mathcal F)=0\qquad\text{for all }p>d.
$$

**Proof.** Induction on $d$; we assume the theorem for all noetherian spaces of dimension $<d$.

_Step 1: reduction to irreducible $X$._ Let $X_1,\ldots,X_m$ be the irreducible components of $X$
and induct on $m$, the case $m=1$ being Step 2 below. For $m\ge2$ set $X'=X_2\cup\cdots\cup X_m$,
a closed subspace with $m-1$ components and dimension at most $d$, and $W=X\setminus X'$, an open
subset contained in the closed irreducible subspace $X_1$. From the first displayed sequence,

$$
0\to j_!(\mathcal F|_W)\to\mathcal F\to i_*(\mathcal F|_{X'})\to0 .
$$

The right-hand term has $H^p(X,i_*(\mathcal F|_{X'}))=H^p(X',\mathcal F|_{X'})=0$ for $p>d$ by the
induction on the number of components. Since $W\subseteq X_1$ with $X_1$ closed, the left-hand term
is $i_{X_1*}$ of the extension by zero of $\mathcal F|_W$ to $X_1$, so its cohomology on $X$ is
computed on the irreducible noetherian space $X_1$, of dimension at most $d$, and vanishes for
$p>d$ by Step 2. The long exact sequence gives $H^p(X,\mathcal F)=0$ for $p>d$.

_Step 2: $X$ irreducible._ Suppose first $d=0$. If $Z\subsetneq X$ were a nonempty closed subset,
one of its irreducible components would be an irreducible closed subset properly contained in $X$,
producing a chain of length one; hence the only closed subsets are $\varnothing$ and $X$, the only
opens are $\varnothing$ and $X$, and every sheaf is flasque. So $H^p(X,\mathcal F)=0$ for $p>0$ by
Proposition 3.2(1).

Now let $d\ge1$. Every sheaf is the filtered colimit of the subsheaves generated by finitely many
sections over opens: such subsheaves form a filtered system, since the subsheaf generated by a
union of two finite families contains both, and every germ lies in one of them. By
Proposition 5.6(4) it suffices to treat a sheaf generated by finitely many sections. If
$\mathcal F$ is generated by $s_1,\ldots,s_k$ with $k\ge2$, let $\mathcal F'$ be the subsheaf
generated by $s_1,\ldots,s_{k-1}$; then $\mathcal F/\mathcal F'$ is generated by one section, and
the long exact sequence reduces the claim for $\mathcal F$ to the claims for $\mathcal F'$ and
$\mathcal F/\mathcal F'$. So we may assume $\mathcal F$ is generated by a single section over an
open $U$, that is, $\mathcal F$ is a quotient of $\mathbf Z_U$: the section corresponds by
adjunction to a map $\mathbf Z_U\to\mathcal F$, whose image is all of $\mathcal F$.

Write $0\to\mathcal R\to\mathbf Z_U\to\mathcal F\to0$ with $\mathcal R\subseteq\mathbf Z_U$. Its
long exact sequence

$$
H^p(X,\mathbf Z_U)\to H^p(X,\mathcal F)\to H^{p+1}(X,\mathcal R)
$$

shows that everything follows from the assertion

$$
(\star)\qquad H^p(X,\mathcal R)=0\ \text{ for }p>d,\ \text{ for every open }U
\text{ and every subsheaf }\mathcal R\subseteq\mathbf Z_U,
$$

applied both to $\mathcal R$ and to the subsheaf $\mathbf Z_U$ of itself.

_Proof of $(\star)$._ We may assume $\mathcal R\ne0$. Every nonempty open $V\subseteq U$ is
irreducible, hence connected, so $\Gamma(V,\mathbf Z_U)=\mathbf Z$ and all restriction maps between
nonempty opens contained in $U$ are the identity. Since $\mathcal R\ne0$, some stalk
$\mathcal R_x$ is nonzero; such an $x$ lies in $U$, because the stalks of $\mathbf Z_U$ vanish
outside $U$, and a nonzero germ is represented by a nonzero element of $\mathcal R(V)\subseteq
\mathbf Z$ for some nonempty open $V\subseteq U$. Let

$$
n=\min\{a>0:\ a\in\mathcal R(V)\ \text{for some nonempty open }V\subseteq U\},
$$

and fix a nonempty open $W\subseteq U$ with $n\in\mathcal R(W)$. For every nonempty open
$V\subseteq W$ the group $\mathcal R(V)$ is a subgroup of $\mathbf Z$ containing $n$, say
$\mathcal R(V)=m\mathbf Z$ with $m\mid n$ and $m>0$; minimality of $n$ forces $m=n$. Hence
$\mathcal R|_W$ is the constant sheaf $n\mathbf Z$ on $W$, so $\mathcal R|_W\simeq\mathbf Z|_W$ and

$$
j_{W!}\bigl(\mathcal R|_W\bigr)\simeq\mathbf Z_W .
$$

Let $Y=X\setminus W$, a proper closed subset of the irreducible $X$, so $\dim Y\le d-1$. The
sequence $0\to j_{W!}(\mathcal R|_W)\to\mathcal R\to i_*(\mathcal R|_Y)\to0$ has right-hand term
with cohomology $H^p(Y,\mathcal R|_Y)$, which vanishes for $p>d-1$ by the induction on dimension.
For the left-hand term, apply $\Gamma$-cohomology to

$$
0\to\mathbf Z_W\to\mathbf Z_X\to i_*\bigl(\mathbf Z_Y\bigr)\to0 .
$$

The constant sheaf $\mathbf Z_X$ on the irreducible space $X$ is flasque, since all its groups of
sections over nonempty opens are $\mathbf Z$ with identity restrictions; so $H^p(X,\mathbf Z_X)=0$
for $p>0$ by Proposition 3.2(1). The long exact sequence

$$
H^{p-1}(Y,\mathbf Z_Y)\to H^p(X,\mathbf Z_W)\to H^p(X,\mathbf Z_X)
$$

therefore gives $H^p(X,\mathbf Z_W)=0$ for $p>d$: the left term vanishes because $p-1>d-1$ and
$\dim Y\le d-1$, and the right term because $p>0$. Feeding both vanishings into the long exact
sequence of the previous display yields $H^p(X,\mathcal R)=0$ for $p>d$, which is $(\star)$ and
completes Step 2 and the induction. $\square$

**Corollary 5.9.** Let $X$ be a noetherian scheme of dimension $d$. Then $H^p(X,\mathcal F)=0$ for
$p>d$ and every sheaf of abelian groups $\mathcal F$, in particular for every quasi-coherent sheaf.
If $f:X\to Y$ is a morphism of noetherian schemes whose fibers have dimension at most $d$ and which
is quasi-compact and separated, then $R^pf_*\mathcal F=0$ for $p>d$ and $\mathcal F$
quasi-coherent, provided each $f^{-1}(V)$, $V\subseteq Y$ affine open, has dimension at most $d$.

**Proof.** The first assertion is Theorem 5.8 applied to the underlying noetherian space. The second
follows from Theorem 4.7, which computes $R^pf_*\mathcal F$ on an affine open $V$ as the tilde of
$H^p(f^{-1}V,\mathcal F)$, together with the first assertion applied to $f^{-1}V$. $\square$

The two vanishing bounds now available are genuinely different and neither implies the other. On an
affine scheme of dimension $17$, Theorem 3.9 gives vanishing above degree $0$ while Theorem 5.8
gives only degree $17$; on a projective space $\mathbf P^r_A$ over a large-dimensional base,
Corollary 4.8 gives vanishing above degree $r$ while the dimension bound is much weaker. The
dimension bound is the one that survives when no cover is prescribed and the sheaf is not
quasi-coherent, which is why it is stated here in its topological form.

## 6. The cohomology of projective space

### 6.1 Projective space and its twisting sheaves

Everything so far has been machinery. This chapter contains the one computation that gives the
machinery something to compute, and it is the computation on which all later projective geometry
rests: the cohomology of the invertible sheaves $\mathcal O(n)$ on $\mathbf P^r_A$, in every degree,
for every integer $n$, over an arbitrary commutative ring $A$. Everything else in the projective
theory — vanishing for coherent sheaves in high twists, finiteness of cohomology, Hilbert
polynomials, duality — is derived from this one answer by resolutions and long exact sequences, so
the answer must be exact, must be a statement about free $A$-modules with named bases, and must
commute with change of $A$. It will be.

We need $\mathbf P^r_A$ only as a scheme glued from $r+1$ affine charts, so we construct it that
way; no general theory of homogeneous spectra is required. Let

$$
S=A[x_0,\ldots,x_r],
$$

graded by total degree, and for a subset $\varnothing\ne I\subseteq V:=\{0,1,\ldots,r\}$ write
$x_I=\prod_{i\in I}x_i$ and $S_{x_I}$ for the localization, graded by $\mathbf Z$. For a graded
ring or module $T$ we write $T_n$ for its degree-$n$ part.

**Proposition 6.1 (construction).** For each $i\in V$ put
$U_i=\operatorname{Spec}(S_{x_i})_0$, an affine $A$-scheme whose ring
$(S_{x_i})_0=A[x_0/x_i,\ldots,x_r/x_i]$ is a polynomial ring in the $r$ variables $x_j/x_i$,
$j\ne i$. The identifications

$$
D\bigl(x_j/x_i\bigr)\subseteq U_i,\qquad
\Gamma\bigl(D(x_j/x_i),\mathcal O\bigr)=(S_{x_ix_j})_0
=\Gamma\bigl(D(x_i/x_j),\mathcal O\bigr)
$$

glue the $U_i$ into a separated $A$-scheme $\mathbf P^r_A$, covered by the $r+1$ affine opens
$U_i$, with

$$
U_I:=\bigcap_{i\in I}U_i=\operatorname{Spec}(S_{x_I})_0
$$

affine for every nonempty $I\subseteq V$. Its formation commutes with base change:
$\mathbf P^r_A\times_{\operatorname{Spec}A}\operatorname{Spec}B=\mathbf P^r_B$ for every
$A$-algebra $B$.

**Proof.** The gluing data are the canonical isomorphisms between the two descriptions of
$(S_{x_ix_j})_0$, and the cocycle condition holds because all three identifications take place
inside $(S_{x_ix_jx_k})_0$. Fix $i_0\in I$; then

$$
U_I=\bigcap_{i\in I\setminus\{i_0\}}D\bigl(x_i/x_{i_0}\bigr)
=D\Bigl(\prod_{i\in I\setminus\{i_0\}}x_i/x_{i_0}\Bigr)\subseteq U_{i_0},
$$

a principal open of an affine scheme, hence affine, and inverting those elements in
$(S_{x_{i_0}})_0$ produces exactly the degree-zero part of $S_{x_I}$. For separatedness we use the
criterion of Section 1.2: the intersections $U_i\cap U_j$ are affine, and
$(S_{x_i})_0\otimes_A(S_{x_j})_0\to(S_{x_ix_j})_0$ is surjective, because a degree-zero Laurent
monomial whose negative exponents occur only at $i$ and $j$ has as many numerator letters as
denominator letters and can therefore be written as a product of factors $x_k/x_i$ and $x_k/x_j$.
Base change is clear chart by chart, since
$(S_{x_i})_0\otimes_AB=(S^B_{x_i})_0$ for $S^B=B[x_0,\ldots,x_r]$, and the gluings correspond.
$\square$

Because $\mathbf P^r_A$ is separated and covered by $r+1$ affine opens, Corollary 4.8(1) already
gives the bound

$$
H^p\bigl(\mathbf P^r_A,\mathcal F\bigr)=0\qquad(p>r)
$$

for every quasi-coherent $\mathcal F$; the content of this chapter is what happens in degrees
$0$ through $r$.

**Definition and Lemma 6.2 (twisting sheaves).** For $n\in\mathbf Z$ let $\mathcal O(n)$ be the
$\mathcal O_{\mathbf P^r_A}$-module obtained by gluing the quasi-coherent sheaves on $U_i$
associated with the $(S_{x_i})_0$-modules $(S_{x_i})_n$. Then:

1. $\mathcal O(n)$ is invertible, with $\mathcal O(n)|_{U_i}$ free of rank one on the basis
   $x_i^n$ and transition factor $(x_i/x_j)^n$ from the $j$-th to the $i$-th chart;
2. $\Gamma(U_I,\mathcal O(n))=(S_{x_I})_n$ for every nonempty $I\subseteq V$;
3. $\mathcal O(0)=\mathcal O$, and multiplication induces isomorphisms
   $\mathcal O(m)\otimes\mathcal O(n)\simeq\mathcal O(m+n)$; in particular
   $\mathcal O(n)^{-1}=\mathcal O(-n)$;
4. the formation of $\mathcal O(n)$ commutes with base change $A\to B$.

**Proof.** The modules $(S_{x_i})_n$ are free of rank one over $(S_{x_i})_0$ with basis $x_i^n$,
which gives (1) once the gluing is checked: on $U_i\cap U_j$ both descriptions give
$(S_{x_ix_j})_n$, since localizing $(S_{x_i})_n$ at $x_j/x_i$ inverts $x_j$ in degree-preserving
fashion, and the two bases differ by the unit $(x_i/x_j)^n$. The cocycle condition is the identity
$(x_i/x_j)^n(x_j/x_k)^n=(x_i/x_k)^n$. Assertion (2) follows from the description of $U_I$ in
Proposition 6.1: sections over a principal open are the corresponding localization, and localizing
$(S_{x_{i_0}})_n$ at $\prod_{i\in I\setminus\{i_0\}}x_i/x_{i_0}$ gives $(S_{x_I})_n$. For (3),
multiplication $(S_{x_i})_m\otimes(S_{x_i})_n\to(S_{x_i})_{m+n}$ takes the basis
$x_i^m\otimes x_i^n$ to the basis $x_i^{m+n}$, hence is an isomorphism, and these are compatible
with the gluings. (4) is again chart by chart. $\square$

For a quasi-coherent $\mathcal F$ on $\mathbf P^r_A$ we write
$\mathcal F(n)=\mathcal F\otimes_{\mathcal O}\mathcal O(n)$.

Global sections can be read off immediately, and the answer already exhibits the shape of the
general computation: sections are the Laurent monomials that survive on _every_ chart.

**Proposition 6.3 (global sections).** Let $r\ge1$. Then
$\Gamma(\mathbf P^r_A,\mathcal O(n))=S_n$, the free $A$-module with basis the monomials of degree
$n$ in $x_0,\ldots,x_r$; it has rank $\binom{n+r}{r}$ for $n\ge0$ and is zero for $n<0$. For
$r=0$ one has $\mathbf P^0_A=\operatorname{Spec}A$, $\mathcal O(n)\simeq\mathcal O$ and
$\Gamma(\mathbf P^0_A,\mathcal O(n))=A\cdot x_0^n$ for every $n$.

**Proof.** By the sheaf axiom, $\Gamma(\mathbf P^r_A,\mathcal O(n))$ is the subgroup of
$\bigoplus_i(S_{x_i})_n$ of families agreeing on overlaps, that is, the intersection
$\bigcap_{i}(S_{x_i})_n$ taken inside $(S_{x_0\cdots x_r})_n$. A Laurent monomial
$x^a=\prod_kx_k^{a_k}$ lies in $S_{x_i}$ exactly when $a_k\ge0$ for all $k\ne i$; intersecting over
all $i$ with $r\ge1$ forces $a_k\ge0$ for all $k$, so the intersection is $S_n$. The rank of $S_n$
is the number of monomials of degree $n$ in $r+1$ variables, which is $\binom{n+r}{r}$ for $n\ge0$,
and $S_n=0$ for $n<0$. The case $r=0$ is the definition. $\square$

We now set up the complex that computes all the cohomology at once. Let $\mathfrak U=(U_0,\ldots,U_r)$
be the standard cover. It is a finite affine cover of the separated scheme $\mathbf P^r_A$ with
affine intersections, so by Theorem 4.2 the alternating Čech complex computes cohomology. By
Lemma 6.2(2) its terms are the graded pieces of localizations of $S$. It is more efficient to treat
all twists simultaneously: define the complex of $A$-modules

$$
K^p=\bigoplus_{\substack{I\subseteq V\\|I|=p+1}}S_{x_I}\qquad(0\le p\le r),
$$

with the alternating Čech differential, in which the map from the $I$-component to the
$(I\cup\{j\})$-component is the localization map with sign $(-1)^{\#\{i\in I\,:\,i<j\}}$. Each
$S_{x_I}$ is graded, the localization maps preserve degree, and by Lemma 6.2(2) the degree-$n$ part
of $K^\bullet$ is exactly the alternating Čech complex of $\mathcal O(n)$ for the standard cover.
Hence

$$
H^p\bigl(\mathbf P^r_A,\mathcal O(n)\bigr)=H^p(K^\bullet)_n\qquad\text{for all }p,n. \tag{6.1}
$$

The complex $K^\bullet$ decomposes further. As an $A$-module, $S_{x_I}$ is free with basis the
Laurent monomials $x^a$, $a\in\mathbf Z^{r+1}$, such that $a_k\ge0$ for every $k\notin I$. Writing

$$
\operatorname{Neg}(a)=\{k\in V:\ a_k<0\},
$$

this condition reads $\operatorname{Neg}(a)\subseteq I$. Since the differential sends $x^a$ in the
$I$-component to $\pm x^a$ in the $(I\cup\{j\})$-component, each Laurent exponent vector is
preserved, and $K^\bullet$ splits as a direct sum of complexes of free $A$-modules

$$
K^\bullet=\bigoplus_{a\in\mathbf Z^{r+1}}K^\bullet(a),\qquad
K^p(a)=\bigoplus_{\substack{|I|=p+1\\ I\supseteq\operatorname{Neg}(a)}}A\cdot x^a, \tag{6.2}
$$

with $K^\bullet(a)$ concentrated in the degree $n=\sum_ka_k$ of the monomial. Cohomology commutes
with direct sums of complexes, so the entire computation reduces to the combinatorics of the
single complex $K^\bullet(a)$, whose terms are indexed by the subsets of $V$ containing the fixed
set $\operatorname{Neg}(a)$. Section 6.2 identifies that complex and reads off the answer.

### 6.2 The complete computation

The complex attached to one Laurent exponent is a simplex. Precisely, for a finite set $W$ let

$$
D^q(W)=\bigoplus_{\substack{J\subseteq W\\|J|=q+1}}A\qquad(q\ge-1),
$$

with the differential that sends the $J$-component to the $J\cup\{j\}$-component, $j\notin J$, by
the sign $(-1)^{\#\{i\in J\,:\,i<j\}}$ relative to a fixed total order on $W$. The term $q=-1$
corresponds to $J=\varnothing$. This is the augmented simplicial cochain complex of the simplex
with vertex set $W$, and its exactness expresses the contractibility of a simplex.

**Lemma 6.4 (simplex lemma).** If $W\ne\varnothing$ then $D^\bullet(W)$ is exact in every degree,
indeed contractible. If $W=\varnothing$ then $D^\bullet(W)=A$ concentrated in degree $-1$.

**Proof.** The second statement is the definition. Let $W\ne\varnothing$ and let $w$ be its
smallest element. Define $h:D^q(W)\to D^{q-1}(W)$ by $(h\sigma)_J=\sigma_{\{w\}\cup J}$ if
$w\notin J$ and $(h\sigma)_J=0$ if $w\in J$. Let $\sigma\in D^q(W)$ and let $J$ have $q+1$
elements. If $w\notin J$, write $J=\{j_0<\cdots<j_q\}$; since $w$ occupies position $0$ in
$\{w\}\cup J$,

$$
(hd\sigma)_J=(d\sigma)_{\{w\}\cup J}
=\sigma_J-\sum_{k}(-1)^{k}\sigma_{\{w\}\cup(J\setminus j_k)},
\qquad
(dh\sigma)_J=\sum_k(-1)^k\sigma_{\{w\}\cup(J\setminus j_k)},
$$

so $(dh+hd)\sigma=\sigma$ on this component. If $w\in J$, then $(hd\sigma)_J=0$ while in
$(dh\sigma)_J=\sum_k(-1)^k(h\sigma)_{J\setminus j_k}$ only the term removing $w$ survives, and it
equals $\sigma_J$ with sign $+1$. In degree $q=-1$ the identity reads
$(hd\sigma)_\varnothing=(d\sigma)_{\{w\}}=\sigma_\varnothing$. Hence $dh+hd=\mathrm{id}$. $\square$

**Theorem 6.5 (cohomology of the twisting sheaves).** Let $A$ be a ring and $r\ge1$. For every
$n\in\mathbf Z$:

1. $H^0(\mathbf P^r_A,\mathcal O(n))=S_n$, the free $A$-module with basis the monomials of degree
   $n$ in $x_0,\ldots,x_r$; it has rank $\binom{n+r}{r}$ for $n\ge0$ and is zero for $n<0$;
2. $H^p(\mathbf P^r_A,\mathcal O(n))=0$ for $0<p<r$;
3. $H^r(\mathbf P^r_A,\mathcal O(n))$ is the free $A$-module with basis the Laurent monomials
   $x^a=x_0^{a_0}\cdots x_r^{a_r}$ with $a_k\le-1$ for every $k$ and $\sum_ka_k=n$; its rank is
   $\binom{-n-1}{r}$ for $n\le-r-1$, and it is zero for $n\ge-r$;
4. $H^p(\mathbf P^r_A,\mathcal O(n))=0$ for $p>r$.

For $r=0$ one has $H^0(\mathbf P^0_A,\mathcal O(n))=A\cdot x_0^n$ and $H^p=0$ for $p>0$.

**Proof.** By (6.1) and (6.2) it suffices to compute $H^\bullet(K^\bullet(a))$ for each
$a\in\mathbf Z^{r+1}$ and to collect the answers in the degree $n=\sum_ka_k$. Put
$N=\operatorname{Neg}(a)$ and $W=V\setminus N$. The assignment $I\mapsto J=I\setminus N$ is a
bijection from the subsets $I$ with $N\subseteq I\subseteq V$ and $|I|=p+1$ onto the subsets
$J\subseteq W$ with $|J|=p+1-|N|$, so as graded $A$-modules

$$
K^p(a)\simeq D^{\,p-|N|}(W).
$$

The differentials agree up to sign: the Čech differential from the $I$-component to the
$(I\cup\{j\})$-component carries the sign $(-1)^{\#\{i\in I:i<j\}}$ while the simplex differential
carries $(-1)^{\#\{i\in J:i<j\}}$, and the two differ by $(-1)^{\#\{i\in N:i<j\}}$. As in
Lemma 1.2, the diagonal automorphism multiplying the $J$-component by
$(-1)^{\sum_{j\in J}\#\{i\in N:\,i<j\}}$ converts one differential into the other, so
$K^\bullet(a)\simeq D^{\bullet-|N|}(W)$ as complexes, with the caveat that the component
$J=\varnothing$ occurs on the left only if $I=N$ is nonempty.

Three cases exhaust the possibilities.

_Case $N=\varnothing$_, that is $a_k\ge0$ for all $k$. Then $W=V\ne\varnothing$ and the subsets $I$
appearing are the nonempty subsets of $V$, so $K^\bullet(a)$ is the complex $D^\bullet(V)$ with its
degree $-1$ term deleted. Lemma 6.4 says the augmented complex is exact, so the truncated one has
$H^0=A$, generated by the image of the deleted term, and $H^p=0$ for $p>0$. The contribution is
therefore one free rank-one summand of $H^0$ for each monomial $x^a$ with $a\ge0$.

_Case $\varnothing\ne N\subsetneq V$._ Then $W\ne\varnothing$, and every subset $J\subseteq W$
occurs, including $J=\varnothing$, which corresponds to the nonempty set $I=N$. So
$K^\bullet(a)$ is the full augmented complex $D^\bullet(W)$ shifted by $|N|$, which is exact by
Lemma 6.4. Such exponent vectors contribute nothing in any degree.

_Case $N=V$_, that is $a_k\le-1$ for all $k$. Then $W=\varnothing$ and the only admissible $I$ is
$V$ itself, of cardinality $r+1$, sitting in Čech degree $p=r$. So $K^\bullet(a)$ is $A$
concentrated in degree $r$, contributing one free rank-one summand to $H^r$.

Collecting: $H^0(K^\bullet)$ is free on the monomials with all exponents $\ge0$, that is $S$, whose
degree-$n$ part is $S_n$; $H^p(K^\bullet)=0$ for $0<p<r$; and $H^r(K^\bullet)$ is free on the
Laurent monomials with all exponents $\le-1$. Assertion (4) is Corollary 4.8(1), the standard cover
having $r+1$ members, and is also visible from $K^p=0$ for $p>r$. It remains to count. For (1) the
monomials of degree $n\ge0$ in $r+1$ variables number $\binom{n+r}{r}$, and there are none for
$n<0$. For (3) substitute $b_k=-a_k-1\ge0$; then $\sum_kb_k=-n-r-1$, so the basis is in bijection
with the monomials of degree $-n-r-1$ in $r+1$ variables. That number is
$\binom{-n-r-1+r}{r}=\binom{-n-1}{r}$ when $-n-r-1\ge0$, and there are no such vectors when
$n\ge-r$. The case $r=0$ was recorded in Proposition 6.3, the standard cover having a single
member. $\square$

The shape of the answer deserves a comment. Cohomology is concentrated at the two extremes, degree
$0$ and degree $r$, with nothing in between, and the two extremes are populated by complementary
sets of monomials: those with all exponents nonnegative, and those with all exponents negative. The
middle degrees vanish because a Laurent monomial with some but not all exponents negative has both
a nonempty "negative" set $N$, forcing it to appear only in Čech degrees $\ge|N|-1$, and a nonempty
complementary set $W$, which contracts its complex. Section 6.3 turns the complementarity of the
two extremes into a perfect pairing.

### 6.3 Freeness, base change, and the top pairing

The computation was performed with named bases and with homotopies whose coefficients are $0$ and
$\pm1$. Both features matter downstream, and we record them explicitly.

**Corollary 6.6 (freeness, base change, Euler characteristic).** Let $r\ge1$.

1. Every $H^p(\mathbf P^r_A,\mathcal O(n))$ is a free $A$-module of finite rank, with the monomial
   basis described in Theorem 6.5.
2. For every ring map $A\to B$ the canonical map is an isomorphism

   $$
   H^p\bigl(\mathbf P^r_A,\mathcal O(n)\bigr)\otimes_AB
   \xrightarrow{\ \sim\ }H^p\bigl(\mathbf P^r_B,\mathcal O(n)\bigr),
   $$

   and $R\Gamma(\mathbf P^r_A,\mathcal O(n))\otimes^L_AB\simeq
   R\Gamma(\mathbf P^r_B,\mathcal O(n))$. The ranks are therefore independent of $A$.
3. If $A=k$ is a field, then for every $n\in\mathbf Z$

   $$
   \chi\bigl(\mathbf P^r_k,\mathcal O(n)\bigr)
   =\sum_p(-1)^p\dim_kH^p\bigl(\mathbf P^r_k,\mathcal O(n)\bigr)
   =\binom{n+r}{r},
   $$

   where the binomial coefficient means the polynomial
   $(n+r)(n+r-1)\cdots(n+1)/r!$ evaluated at $n$.

**Proof.** (1) is Theorem 6.5. (2) The sheaf $\mathcal O(n)$ is invertible, hence flat over $A$, so
Theorem 5.2(2) applies and gives the derived statement, using that $\mathbf P^r_B$ with its
standard cover is the base change of $\mathbf P^r_A$ with its standard cover by Proposition 6.1 and
Lemma 6.2(4). Since the cohomology modules are free, the derived tensor product has no higher terms
and reduces to the displayed underived isomorphism. Alternatively one may argue directly: the
complex $K^\bullet$ over $A$ is $K^\bullet_{\mathbf Z}\otimes_{\mathbf Z}A$, its Laurent
decomposition is defined over $\mathbf Z$, and the contracting homotopies of Lemma 6.4 have
coefficients $0,\pm1$, so all the identifications of Theorem 6.5 persist verbatim over any ring.
(3) For $n\ge0$ only $H^0$ is nonzero, of dimension $\binom{n+r}{r}$, which is the value of the
polynomial. For $-r\le n\le-1$ all cohomology vanishes, and the polynomial
$(n+r)\cdots(n+1)/r!$ has one of its factors equal to zero. For $n\le-r-1$ only $H^r$ is nonzero,
so $\chi=(-1)^r\binom{-n-1}{r}$; writing $n=-m-r-1$ with $m\ge0$ gives
$\binom{-n-1}{r}=\binom{m+r}{r}$, while

$$
\frac{(n+r)\cdots(n+1)}{r!}=\frac{(-m-1)(-m-2)\cdots(-m-r)}{r!}
=(-1)^r\binom{m+r}{r},
$$

which agrees. $\square$

Part (2) is the assertion that later volumes use when they base-change a projective computation to
a residue field, to a completion, or to a ring with nilpotents: the answer is one fixed complex of
free modules with integral matrices, so no hypothesis on the target ring is needed.

Finally we record the duality visible in Theorem 6.5. The two nonvanishing degrees carry
complementary monomial bases, and multiplication of monomials matches them exactly. Multiplication
of sections gives, for all $m,n$, a pairing

$$
H^0\bigl(\mathcal O(m)\bigr)\otimes_AH^r\bigl(\mathcal O(n)\bigr)
\longrightarrow H^r\bigl(\mathcal O(m+n)\bigr),
$$

induced by $\mathcal O(m)\otimes\mathcal O(n)\simeq\mathcal O(m+n)$ of Lemma 6.2(3); at the level of
the complex $K^\bullet$ it is multiplication by an element of $S_m$, which preserves the Čech
complex because it preserves each $S_{x_I}$. The module $H^r(\mathcal O(-r-1))$ is free of rank one
by Theorem 6.5, with basis the class of $(x_0x_1\cdots x_r)^{-1}$; we call the resulting isomorphism

$$
\operatorname{tr}:H^r\bigl(\mathbf P^r_A,\mathcal O(-r-1)\bigr)\xrightarrow{\ \sim\ }A,
\qquad
\bigl[(x_0\cdots x_r)^{-1}\bigr]\longmapsto1,
$$

the **top coefficient functional**; it is compatible with every base change $A\to B$ by
Corollary 6.6(2).

**Theorem 6.7 (perfect top pairing).** Let $r\ge1$ and $n\in\mathbf Z$. The pairing

$$
H^0\bigl(\mathbf P^r_A,\mathcal O(n)\bigr)\otimes_A
H^r\bigl(\mathbf P^r_A,\mathcal O(-n-r-1)\bigr)
\xrightarrow{\ \cdot\ }H^r\bigl(\mathbf P^r_A,\mathcal O(-r-1)\bigr)
\xrightarrow{\ \operatorname{tr}\ }A
$$

is a perfect pairing of finite free $A$-modules: it identifies each factor with the $A$-linear dual
of the other. Its formation commutes with arbitrary base change $A\to B$.

**Proof.** By Theorem 6.5 the first factor is free with basis the monomials $x^b$, $b\ge0$,
$\sum_kb_k=n$, and the second is free with basis the classes of the Laurent monomials $x^a$,
$a_k\le-1$, $\sum_ka_k=-n-r-1$. In $H^r$, computed as the cokernel of the last Čech differential,
the class of a Laurent monomial is a basis element if all its exponents are negative and is zero
otherwise, since the monomials with at least one nonnegative exponent span the image of that
differential. Hence

$$
\operatorname{tr}\bigl(x^b\cdot[x^a]\bigr)=
\begin{cases}
1,&a+b=(-1,-1,\ldots,-1),\\
0,&\text{otherwise},
\end{cases}
$$

because $\sum_k(a_k+b_k)=-r-1$ together with $a_k+b_k\le-1$ for all $k$ forces
$a_k+b_k=-1$ for all $k$, while any other product has some nonnegative exponent and dies in $H^r$.
For each basis element $x^b$ of the first factor, the unique partner is $a=-\mathbf 1-b$, which is
admissible precisely because $b\ge0$; so in these bases the pairing matrix is a permutation matrix,
which is invertible over any ring. Compatibility with base change follows from Corollary 6.6(2),
the bases being defined over $\mathbf Z$. $\square$

Two features of this statement will be used exactly as proved. First, it is a statement about free
modules over an arbitrary ring, not about vector spaces, so it survives every specialization.
Second, the isomorphism $\operatorname{tr}$ is given by an explicit coefficient of an explicit Čech
representative, so a duality argument that begins from it can be carried out with matrices; later
volumes construct the duality theory of projective schemes by resolving a coherent sheaf by sums of
twists and transporting this pairing through the resolution. The numerical shadow of the pairing is
the identity $\operatorname{rank}H^r(\mathcal O(-n-r-1))=\operatorname{rank}H^0(\mathcal O(n))$,
both being $\binom{n+r}{r}$, which is already visible in the two counts of Theorem 6.5.

## 7. Graded algebra for projective methods

### 7.1 Hilbert's syzygy theorem

Theorem 6.5 computes the cohomology of the twisting sheaves and nothing else. The standard way to
convert it into information about an arbitrary coherent sheaf on projective space is to resolve
that sheaf by finite direct sums of twists and to run the long exact sequence. For the method to
terminate, the resolution must be finite, and its length must be bounded by something independent
of the sheaf; otherwise a descending induction never reaches its base. Hilbert's syzygy theorem
provides exactly this bound: over a polynomial ring in $r+1$ variables, every finite graded module
has a graded free resolution of length at most $r+1$. Together with the vanishing
$H^p(\mathbf P^r,-)=0$ for $p>r$, this is what makes projective cohomology a finite computation.

The theorem belongs in this book rather than in the volumes that apply it, because it is pure
graded algebra with no geometric content, and because the same volumes need the second theorem of
this chapter for the same reason: to control a family of such resolutions over a base.

Throughout, $k$ is a field and $S=k[x_0,\ldots,x_r]$ is graded by total degree, with irrelevant
ideal $S_+=(x_0,\ldots,x_r)$ and $S/S_+=k$. A **graded** $S$-module is one with a decomposition
$M=\bigoplus_{n\in\mathbf Z}M_n$ satisfying $S_dM_n\subseteq M_{n+d}$; morphisms preserve degree.
For $d\in\mathbf Z$ the shift $M(d)$ is $M$ with $M(d)_n=M_{n+d}$. A **finite graded free** module
is a finite direct sum $\bigoplus_jS(-a_j)$. A finitely generated graded module can be generated by
finitely many homogeneous elements, each $M_n$ is a finite-dimensional $k$-vector space, and $M_n=0$
for $n\ll0$; submodules of finite graded modules are finite and graded by the Hilbert basis theorem.

**Lemma 7.1 (graded Nakayama and minimal generators).** Let $M$ be a finite graded $S$-module.

1. If $M=S_+M$ then $M=0$.
2. Homogeneous elements $m_1,\ldots,m_s$ whose images form a $k$-basis of $M/S_+M$ generate $M$;
   the number $s=\dim_kM/S_+M$ and the multiset of their degrees are determined by $M$.
3. If $F_0=\bigoplus_{j=1}^sS(-a_j)\to M$ sends the standard basis to such a minimal system of
   homogeneous generators, then $\ker(F_0\to M)\subseteq S_+F_0$.

**Proof.** (1) A finite graded module is bounded below, so if $M\ne0$ there is a least $d$ with
$M_d\ne0$. But $(S_+M)_d=\sum_{e>0}S_eM_{d-e}=0$ since $M_{d-e}=0$ for $e>0$, contradicting
$M=S_+M$. (2) Let $M'\subseteq M$ be the submodule generated by the $m_i$. Then
$M'+S_+M=M$, so $M/M'$ satisfies $S_+(M/M')=M/M'$ and vanishes by (1). The invariance of $s$ and of
the degrees is the statement that $M/S_+M$ is a graded $k$-vector space determined by $M$, the
degrees being those in which it is nonzero, counted with multiplicity. (3) Let
$\xi=(f_1,\ldots,f_s)\in\ker$ be homogeneous of degree $d$, so $f_j$ is homogeneous of degree
$d-a_j$. If some $f_j\notin S_+$, then $f_j$ is a nonzero scalar and $d=a_j$; the relation
$\sum_if_im_i=0$ then expresses $m_j$ as an $S$-combination of the other $m_i$, so their images
would already span $M/S_+M$, contradicting minimality. $\square$

**Proposition 7.2 (minimal free resolutions).** Every finite graded $S$-module $M$ admits a
resolution

$$
\cdots\longrightarrow F_2\longrightarrow F_1\longrightarrow F_0\longrightarrow M\longrightarrow0
$$

by finite graded free modules with all differentials satisfying $d(F_{i+1})\subseteq S_+F_i$. For
such a resolution, $F_i\otimes_Sk$ has zero differentials, so

$$
\operatorname{Tor}^S_i(M,k)\simeq F_i\otimes_Sk\qquad\text{for all }i\ge0 .
$$

**Proof.** Apply Lemma 7.1(2) to obtain $F_0\to M$ with kernel $Z_1\subseteq S_+F_0$; the kernel is
a finite graded module because $S$ is noetherian. Repeat with $Z_1$ in place of $M$, and so on. The
resulting complex is exact by construction and each differential lands in $S_+F_i$ by
Lemma 7.1(3). Since $F_\bullet\to M$ is a free, hence projective, resolution, it computes
$\operatorname{Tor}^S_\bullet(M,k)$; the induced differentials on $F_\bullet\otimes_Sk$ are zero
because they are given by matrices with entries in $S_+$, which die in $k=S/S_+$. Hence the
homology of $F_\bullet\otimes_Sk$ is $F_\bullet\otimes_Sk$ itself. $\square$

The bound now comes from computing the same $\operatorname{Tor}$ with a resolution of the _other_
variable. Here the Koszul complex is explicit and short.

**Lemma 7.3 (Koszul resolution of the residue field).** Let $K_\bullet$ be the tensor product over
$S$ of the $r+1$ two-term complexes $[\,S(-1)\xrightarrow{\,x_i\,}S\,]$, so that
$K_j\simeq S(-j)^{\binom{r+1}{j}}$ for $0\le j\le r+1$ and $K_j=0$ otherwise. Then $K_\bullet$ is a
graded free resolution of $k=S/S_+$ of length $r+1$. Consequently
$\operatorname{Tor}^S_i(M,k)=0$ for every $S$-module $M$ and every $i>r+1$.

**Proof.** Write $K_\bullet(f_1,\ldots,f_m)$ for the analogous complex attached to elements
$f_1,\ldots,f_m$. We prove by induction on $m$ that if $f_1,\ldots,f_m$ is a regular sequence —
each $f_l$ a nonzerodivisor on $S/(f_1,\ldots,f_{l-1})$ — then $H_j(K_\bullet)=0$ for $j>0$ and
$H_0(K_\bullet)=S/(f_1,\ldots,f_m)$. For $m=1$ this is the statement that $f_1$ is injective on
$S$. In general $K_\bullet(f_1,\ldots,f_m)$ is the mapping cone of multiplication by $f_m$ on
$K_\bullet(f_1,\ldots,f_{m-1})$, so its long exact homology sequence reads

$$
H_j(K^{(m-1)})\xrightarrow{\ \pm f_m\ }H_j(K^{(m-1)})\to H_j(K^{(m)})
\to H_{j-1}(K^{(m-1)})\xrightarrow{\ \pm f_m\ }H_{j-1}(K^{(m-1)}).
$$

For $j\ge2$ both outer groups vanish by induction, so $H_j(K^{(m)})=0$. For $j=1$ the sequence
gives an injection of $H_1(K^{(m)})$ into the kernel of $f_m$ on
$H_0(K^{(m-1)})=S/(f_1,\ldots,f_{m-1})$, which is zero by regularity. And
$H_0(K^{(m)})=S/(f_1,\ldots,f_m)$. Now $x_0,\ldots,x_r$ is a regular sequence, since
$S/(x_0,\ldots,x_{l-1})=k[x_l,\ldots,x_r]$ is an integral domain in which $x_l\ne0$. So
$K_\bullet$ is a free resolution of $S/S_+=k$, graded because all the maps are homogeneous, and it
has length $r+1$. The exterior-power description of the terms is the definition of the tensor
product of the two-term complexes. Since $\operatorname{Tor}$ may be computed from a projective
resolution of either variable — the derived tensor product of Book 7a, Section 4.2 being symmetric,
with $\operatorname{Tor}^S_i(M,N)=H^{-i}(M\otimes^L_SN)$ — we get
$\operatorname{Tor}^S_i(M,k)=H_i(M\otimes_SK_\bullet)=0$ for $i>r+1$. $\square$

**Theorem 7.4 (Hilbert's syzygy theorem).** Let $k$ be a field, $S=k[x_0,\ldots,x_r]$, and let $M$
be a finite graded $S$-module. Then $M$ admits a graded free resolution

$$
0\longrightarrow F_{r+1}\longrightarrow F_r\longrightarrow\cdots
\longrightarrow F_1\longrightarrow F_0\longrightarrow M\longrightarrow0
$$

of length at most $r+1$, in which every $F_i$ is a finite direct sum of shifts $S(-a)$.

**Proof.** Take a minimal resolution as in Proposition 7.2. For $i>r+1$ we have
$F_i\otimes_Sk=\operatorname{Tor}^S_i(M,k)=0$ by Lemma 7.3, and a finite free module with
$F\otimes_Sk=0$ is zero. So the minimal resolution has $F_i=0$ for $i>r+1$, which is the assertion;
its terms are finite sums of shifts by construction. $\square$

Two properties of the resolution produced here are used in applications and are worth stating
separately, since they are what allow a resolution over one field to be transported.

**Corollary 7.5 (stability under field extension).** Let $F_\bullet\to M$ be as in Theorem 7.4 and
let $K/k$ be any field extension. Then $F_\bullet\otimes_kK\to M\otimes_kK$ is a graded free
resolution of the finite graded $K[x_0,\ldots,x_r]$-module $M\otimes_kK$, of the same length and
with the same shifts.

**Proof.** The resolution is an exact sequence of $k$-vector spaces, and $-\otimes_kK$ is exact, so
exactness is preserved. Each $S(-a)\otimes_kK$ is $S_K(-a)$ with $S_K=K[x_0,\ldots,x_r]$, and the
differentials are the original matrices with entries viewed in $S_K$. $\square$

The form in which the theorem is consumed downstream is worth spelling out. Given a finite graded
module over a polynomial ring in $r+1$ variables over a field, one obtains a bounded complex of
finite sums of shifts $S(-a)$, with at most $r+2$ terms, whose matrices involve only finitely many
coefficients. Over a base ring $A$, those finitely many coefficients live in a localization of $A$;
Section 7.2 is the statement that after inverting one element of $A$ the whole configuration
becomes flat over the base, so that a resolution constructed at one point of $\operatorname{Spec}A$
remains a resolution on a neighborhood and after every specialization inside it.

### 7.2 Generic freeness

A construction carried out over the fraction field of a domain involves finitely many coefficients,
so it descends to a localization. That much is bookkeeping. What is not bookkeeping is that the
_modules_ involved, not merely the equations, become free over the base after one further
localization, so that the construction survives every specialization inside the corresponding open
set. This is Grothendieck's generic freeness lemma. Its role is to turn a fiberwise statement into
a statement over a neighborhood: exactness of a complex at the generic point becomes exactness at
every point of an open set, and moreover exactness that persists after arbitrary base change,
because flatness makes the short exact sequences universally exact.

**Theorem 7.6 (generic freeness).** Let $A$ be a noetherian domain with fraction field $F$, let $B$
be a finitely generated $A$-algebra, and let $M$ be a finite $B$-module. Then there is a nonzero
$f\in A$ such that $M_f$ is a free $A_f$-module.

**Proof.** _Dévissage._ Since $B$ is noetherian and $M$ is finite, $M$ has a filtration
$0=M_0\subseteq M_1\subseteq\cdots\subseteq M_t=M$ by $B$-submodules with
$M_i/M_{i-1}\simeq B/\mathfrak p_i$ for prime ideals $\mathfrak p_i\subseteq B$. If each
$B/\mathfrak p_i$ becomes $A$-free after inverting some nonzero $f_i$, invert $f=\prod_if_i$: each
layer is then free over $A_f$, and an extension of a free module by any module splits, so $M_f$ is
a direct sum of the layers and is free. We may therefore assume $M=C:=B/\mathfrak p$, a domain that
is a finitely generated $A$-algebra.

_Injectivity of $A\to C$._ If some nonzero $a\in A$ dies in $C$, then $C_a=0$, which is free. So
assume $A\subseteq C$.

_Induction._ Let $C_F=C\otimes_AF$, a nonzero finitely generated $F$-algebra and a domain, being a
localization of $C$; let $d$ be the transcendence degree of its fraction field over $F$. We induct
on $d$.

By Noether normalization there are $z_1,\ldots,z_d\in C_F$, algebraically independent over $F$,
such that $C_F$ is a finite $F[z_1,\ldots,z_d]$-module; multiplying by nonzero elements of $A$ we
may take $z_i\in C$. Choose $w_1,\ldots,w_s\in C$ generating $C_F$ over $F[z]$, with $w_1=1$, and
write

$$
w_iw_j=\sum_lg_{ijl}w_l,\qquad y_u=\sum_ih_{ui}w_i,
$$

where $y_1,\ldots,y_m$ generate $C$ as an $A$-algebra and $g_{ijl},h_{ui}\in F[z]$. Let $f\in A$ be
a nonzero common denominator of the finitely many coefficients occurring in the $g_{ijl}$ and
$h_{ui}$. Then $N=\sum_iA_f[z]w_i\subseteq C_f$ is closed under multiplication, contains $1$ and
every $y_u$, hence contains $A_f[y_1,\ldots,y_m]=C_f$; so

$$
C_f=\sum_{i=1}^sA_f[z_1,\ldots,z_d]\,w_i
$$

is a finite module over $P=A_f[z_1,\ldots,z_d]$.

If $d=0$ this says $C_f=\sum_iA_fw_i$ is a finite $A_f$-module, and the $w_i$ may be chosen to be an
$F$-basis of $C_F$, hence linearly independent over $A_f$; so $C_f$ is free and we are done.

If $d\ge1$, filter the finite $P$-module $C_f$ with layers $P/\mathfrak q$ for primes
$\mathfrak q\subseteq P$, as in the dévissage step; it suffices to treat one layer. If
$\mathfrak q\cap A_f\ne0$, invert a nonzero element of that intersection and the layer becomes zero.
If $\mathfrak q=0$, the layer is $P=A_f[z_1,\ldots,z_d]$, which is free over $A_f$ with basis the
monomials in the $z_i$. Otherwise $\mathfrak q\ne0$ and $\mathfrak q\cap A_f=0$, so
$C'=P/\mathfrak q$ is a domain, a finitely generated $A_f$-algebra containing $A_f$, and

$$
C'\otimes_{A_f}F=F[z_1,\ldots,z_d]/\mathfrak qF[z_1,\ldots,z_d]
$$

is a nonzero domain, a proper quotient of $F[z_1,\ldots,z_d]$ by a nonzero prime. A proper quotient
of a finitely generated domain over a field has strictly smaller dimension, hence strictly smaller
transcendence degree, so the induction hypothesis applies to $C'$ and makes it free over a further
localization. Inverting the product of the finitely many elements produced by the finitely many
layers finishes the induction. $\square$

For the applications the module carries a grading, and one wants information about the individual
graded pieces as well.

**Corollary 7.7 (graded form).** Let $A$ be a noetherian domain, $W=A[x_0,\ldots,x_r]$ with its
standard grading, and let $M$ be a finite graded $W$-module. Then there is a nonzero $f\in A$ such
that $M_f$ is free over $A_f$; consequently every graded piece $(M_n)_f=(M_f)_n$ is a finite flat,
hence finite locally free, $A_f$-module, and this persists after every further localization and
every base change $A_f\to B$.

**Proof.** Theorem 7.6 applies to $B=W$ and gives $f$ with $M_f$ free, hence flat, over $A_f$. As
an $A_f$-module $M_f=\bigoplus_n(M_n)_f$, and a direct summand of a flat module is flat, so each
$(M_n)_f$ is flat. Each $M_n$ is a finite $A$-module because $M$ is a finite graded module over
$W$, and a finite flat module over a noetherian ring is finite projective, that is, finite locally
free. Flatness and finite local freeness are preserved by base change. $\square$

The ranks of the pieces $(M_n)_f$ vary with $n$, so one cannot demand a single localization making
all of them free simultaneously with a common basis; but finitely many of them can always be made
free at once by inverting one more element.

The form in which the two theorems of this chapter are used together is the following spreading-out
statement, which converts a resolution over one field into a resolution valid over a neighborhood
and stable under all specializations.

**Corollary 7.8 (spreading out an exact complex).** Let $A$ be a noetherian domain and
$W=A[x_0,\ldots,x_r]$. Let

$$
0\to G_t\to G_{t-1}\to\cdots\to G_0\to M\to0
$$

be an exact complex of finite graded $W$-modules. Then there is a nonzero $f\in A$ such that all the
cycle modules of the complex, and $M$ itself, are free over $A_f$ after inverting $f$, and such that
the complex

$$
0\to (G_t)_f\otimes_{A_f}B\to\cdots\to(G_0)_f\otimes_{A_f}B\to M_f\otimes_{A_f}B\to0
$$

is exact for every $A_f$-algebra $B$; in particular it is exact after passage to every residue field
of $A_f$.

**Proof.** Let $Z_i=\ker(G_i\to G_{i-1})$, with $Z_0=\ker(G_0\to M)$; these are finite graded
$W$-modules because $W$ is noetherian. Apply Theorem 7.6 to $M$ and to the finitely many $Z_i$ and
let $f$ be the product of the resulting elements, so that all of them are free, hence flat, over
$A_f$. The exact complex splits into short exact sequences

$$
0\to Z_i\to G_i\to Z_{i-1}\to0,\qquad Z_{-1}:=M,
$$

whose right-hand terms are $A_f$-flat after inverting $f$. Tensoring a short exact sequence with
flat cokernel over $A_f$ with any $B$ preserves exactness, and splicing the resulting short exact
sequences reconstructs the base-changed complex, which is therefore exact. $\square$

This is exactly the mechanism by which a syzygy computation performed over the fraction field, or
over the residue field of a generic point, is propagated: Theorem 7.4 produces the resolution over
one field with finitely many coefficients; clearing denominators places it over a localization of
the base; Corollary 7.8 makes it exact over the whole localization and after every specialization,
because the cycles have been made flat. Combined with the projective computation of Chapter 6,
which is itself insensitive to the base ring by Corollary 6.6, this converts a single fiberwise
calculation into a statement holding uniformly on an open subset of the base — which is how
noetherian induction on the base becomes a finite argument in the volumes that follow.

## 8. Synthesis

### 8.1 The reusable package

The results of this book are used later as a fixed interface, and it is worth collecting the
statements in the form in which they are consumed, with the hypotheses that each one actually
needs. The recurring theme is that three hypotheses do all the work — quasi-coherence, so that
affine opens are acyclic; separatedness and quasi-compactness, so that a finite Čech complex
exists; and flatness, so that the complex may be tensored — and that no finiteness or noetherian
condition is required except where dimension or finite generation is the subject.

**1. The affine dictionary.** Over a ring $A$, the functors $M\mapsto\widetilde M$ and
$\Gamma(\operatorname{Spec}A,-)$ are inverse exact equivalences between $A$-modules and
quasi-coherent sheaves (Corollary 2.4), quasi-coherence may be tested on any one affine open cover
(Corollary 2.6), and a section over $D(f)$ becomes the restriction of a global section after
multiplication by a power of $f$ (Corollary 2.5).

**2. Permanence.** Quasi-coherent sheaves are stable under kernels, cokernels, images, extensions,
arbitrary colimits, tensor products, and pullback along any morphism (Theorems 2.7 and 2.8), and
under pushforward along any quasi-compact quasi-separated morphism, with
$f_*\mathcal F=\widetilde{\Gamma(X,\mathcal F)}$ over an affine base (Lemma 2.9, Theorem 2.10). On a
noetherian scheme every quasi-coherent sheaf is the filtered union of its coherent subsheaves
(Theorem 2.11).

**3. Affine vanishing.** $H^p(\operatorname{Spec}A,\mathcal F)=0$ for $p>0$ and every quasi-coherent
$\mathcal F$, over an arbitrary ring $A$ (Theorem 3.9); affine opens are acyclic (Corollary 3.10);
affine morphisms have vanishing higher direct images and do not change cohomology
(Corollary 3.11).

**4. The Čech model.** If $X$ is quasi-compact and separated and $\mathfrak U$ is a finite affine
open cover with $n$ members, the alternating Čech complex $\check C^\bullet_{\mathrm{alt}}
(\mathfrak U,\mathcal F)$ is a complex of length at most $n-1$ representing $R\Gamma(X,\mathcal F)$
for every quasi-coherent $\mathcal F$ (Theorem 4.2); short exact sequences of quasi-coherent
sheaves give short exact sequences of these complexes (Corollary 4.4). Mayer–Vietoris holds for
arbitrary sheaves and arbitrary pairs of opens (Theorem 4.3).

**5. Higher direct images.** For $f$ quasi-compact and quasi-separated, $R^pf_*\mathcal F$ is
quasi-coherent and equals $\widetilde{H^p(f^{-1}V,\mathcal F)}$ over an affine open
$V\subseteq Y$ (Theorem 4.7); the Leray spectral sequence is available and degenerates over an
affine base (Corollary 4.9). If $X$ is separated and covered by $n$ affines then
$H^p(X,\mathcal F)=0$ for $p\ge n$, and correspondingly $R^pf_*\mathcal F=0$ (Corollary 4.8).

**6. Base change.** With $X$ quasi-compact separated over $A$ and $\mathcal F$ quasi-coherent and
$A$-flat, the Čech model is a bounded complex of flat $A$-modules whose formation commutes with
scalar extension on the nose (Lemma 5.1), so that

$$
R\Gamma(X,\mathcal F)\otimes^L_AM\simeq R\Gamma(X,\mathcal F\otimes_AM),
\qquad
B\otimes^L_AR\Gamma(X,\mathcal F)\simeq R\Gamma(X_B,\mathcal F_B)
$$

for every $A$-module $M$ and every $A$-algebra $B$ (Theorem 5.2). Without flatness of $\mathcal F$,
the same holds in underived form whenever $A\to B$ is flat (Theorem 5.3), and likewise for higher
direct images along a flat base change of the base (Corollary 5.4).

**7. Colimits.** Cohomology commutes with filtered colimits of quasi-coherent sheaves on a
quasi-compact separated scheme (Proposition 5.5) and with filtered colimits of arbitrary abelian
sheaves on a noetherian space (Proposition 5.6); on a noetherian scheme it is the colimit over
coherent subsheaves (Corollary 5.7).

**8. Grothendieck vanishing.** On a noetherian topological space of dimension $d$, every sheaf of
abelian groups has $H^p=0$ for $p>d$ (Theorem 5.8, Corollary 5.9).

**9. Projective space.** $\mathbf P^r_A$ is separated, covered by $r+1$ affine charts, and commutes
with base change (Proposition 6.1); the sheaves $\mathcal O(n)$ are invertible with
$\Gamma(U_I,\mathcal O(n))=(S_{x_I})_n$ (Lemma 6.2). For $r\ge1$ and all $n$,
$H^0(\mathcal O(n))=S_n$ is free of rank $\binom{n+r}{r}$ for $n\ge0$ and zero otherwise,
$H^p(\mathcal O(n))=0$ for $0<p<r$, and $H^r(\mathcal O(n))$ is free on the Laurent monomials with
all exponents negative, of rank $\binom{-n-1}{r}$ for $n\le-r-1$ and zero for $n\ge-r$
(Theorem 6.5). All these modules are free, their formation commutes with every ring map, and over a
field $\chi(\mathcal O(n))=\binom{n+r}{r}$ as a polynomial in $n$ (Corollary 6.6). Multiplication
against the top coefficient functional gives a perfect pairing
$H^0(\mathcal O(n))\times H^r(\mathcal O(-n-r-1))\to A$, compatible with base change
(Theorem 6.7).

**10. Graded algebra.** Over a polynomial ring in $r+1$ variables over a field, every finite graded
module has a graded free resolution of length at most $r+1$ by finite sums of shifts, stable under
field extension (Theorem 7.4, Corollary 7.5). Over a noetherian domain, a finite module over a
finitely generated algebra becomes free after inverting one element (Theorem 7.6); the graded pieces
become finite locally free (Corollary 7.7); and an exact complex of finite graded modules can be
spread out so that it remains exact after every base change (Corollary 7.8).

### 8.2 Conclusion

The subject of this book is the passage from modules to sheaves and back. Chapter 2 established the
dictionary; the remaining chapters measured its failure to be perfect. That failure is cohomology,
and the three principal theorems say, in three different registers, that it is smaller and more
computable than one might fear. On an affine scheme it vanishes altogether, so all of it comes from
gluing. On a separated quasi-compact scheme it is computed by one finite complex of modules built
from a chosen cover, so all of it is linear algebra over the base ring. On a noetherian space it
vanishes above the dimension, so all of it is bounded by geometry rather than by the accident of a
cover.

The three registers are not independent. Affine vanishing is what makes the Čech complex correct;
the Čech complex is what makes base change, filtered colimits, and the projective computation
possible; the projective computation is the one place in the theory where a nonzero answer is
produced, and it is produced by the same complex, applied to a family of elements that fails to be
unimodular. Theorem 1.1 and Theorem 6.5 are the two halves of one calculation, separated only by
whether the elements $x_0,\ldots,x_r$ generate the unit ideal.

What has been deliberately left out is everything that requires properness. Nothing here shows that
the cohomology of a coherent sheaf is a finite module, that it is computed by a complex of finite
projective modules, that its rank jumps only on closed subsets, or that it commutes with arbitrary
base change under precise conditions. Those statements need a hypothesis this book never makes,
and they belong to the theory of proper families. What this book supplies is what such a theory
must assume: an exact affine dictionary, a finite functorial model for $R\Gamma$, unrestricted
change of coefficients, and one completely explicit computation on projective space, over an
arbitrary base ring, together with the graded algebra needed to reduce arbitrary sheaves to that
computation.
