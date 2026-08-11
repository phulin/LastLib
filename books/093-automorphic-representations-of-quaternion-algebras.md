# Automorphic Representations of $D^\times$

## Contents

1. [From finite quaternionic forms to global representations](#1-from-finite-quaternionic-forms-to-global-representations)
   - [The question behind the finite modules](#11-the-question-behind-the-finite-modules)
   - [Standing notation and actions](#12-standing-notation-and-actions)
   - [The anisotropic and totally definite hypotheses](#13-the-anisotropic-and-totally-definite-hypotheses)
   - [The route through the book](#14-the-route-through-the-book)
2. [The adelic group and compactness modulo the center](#2-the-adelic-group-and-compactness-modulo-the-center)
   - [Restricted products and rational points](#21-restricted-products-and-rational-points)
   - [Adelic reduction for the anisotropic norm form](#22-adelic-reduction-for-the-anisotropic-norm-form)
   - [Totally definite finite-level quotients](#23-totally-definite-finite-level-quotients)
   - [Haar measures and quotient measures](#24-haar-measures-and-quotient-measures)
3. [Automorphic forms when there are no cusps](#3-automorphic-forms-when-there-are-no-cusps)
   - [Why the definition simplifies](#31-why-the-definition-simplifies)
   - [Constant terms and their absence](#32-constant-terms-and-their-absence)
   - [The full character spectrum](#33-the-full-character-spectrum)
   - [Three spectra that must not be conflated](#34-three-spectra-that-must-not-be-conflated)
4. [The right regular discrete spectrum](#4-the-right-regular-discrete-spectrum)
   - [The Hilbert space](#41-the-hilbert-space)
   - [Why compactness produces discreteness](#42-why-compactness-produces-discreteness)
   - [Smooth vectors and irreducible automorphic representations](#43-smooth-vectors-and-irreducible-automorphic-representations)
   - [Character summands inside the regular spectrum](#44-character-summands-inside-the-regular-spectrum)
5. [From one adelic representation to its local factors](#5-from-one-adelic-representation-to-its-local-factors)
   - [Why factorization should exist](#51-why-factorization-should-exist)
   - [The factorization theorem](#52-the-factorization-theorem)
   - [Split and division local factors](#53-split-and-division-local-factors)
   - [Spherical factors and their Hecke characters](#54-spherical-factors-and-their-hecke-characters)
   - [Ramified reference data](#55-ramified-reference-data)
6. [Admissibility and finite multiplicity](#6-admissibility-and-finite-multiplicity)
   - [Three finiteness statements](#61-three-finiteness-statements)
   - [Finite-dimensional fixed-level spaces](#62-finite-dimensional-fixed-level-spaces)
   - [Admissibility of the local factors](#63-admissibility-of-the-local-factors)
   - [Finite spectral multiplicity](#64-finite-spectral-multiplicity)
7. [Multiplicity spaces and quaternionic unit multiplicity](#7-multiplicity-spaces-and-quaternionic-unit-multiplicity)
   - [What compactness proves](#71-what-compactness-proves)
   - [The global multiplicity space](#72-the-global-multiplicity-space)
   - [Why the additive theta kernel is not the proof](#73-why-the-additive-theta-kernel-is-not-the-proof)
   - [The character-clean simple trace identity](#74-the-character-clean-simple-trace-identity)
   - [Multiplicity one and strong determination](#75-multiplicity-one-and-strong-determination)
8. [Archimedean weights in the totally definite case](#8-archimedean-weights-in-the-totally-definite-case)
   - [Why weight becomes a local representation](#81-why-weight-becomes-a-local-representation)
   - [The dual forced by the action convention](#82-the-dual-forced-by-the-action-convention)
   - [Relation with algebraic coefficient systems](#83-relation-with-algebraic-coefficient-systems)
   - [Worked weights and a counterexample](#84-worked-weights-and-a-counterexample)
9. [Exact recovery of the finite algebraic modules](#9-exact-recovery-of-the-finite-algebraic-modules)
   - [The problem of comparing scalar and vector-valued forms](#91-the-problem-of-comparing-scalar-and-vector-valued-forms)
   - [Proof of the scalar--vector identification](#92-proof-of-the-scalar--vector-identification)
   - [The spectral formula at fixed level and weight](#93-the-spectral-formula-at-fixed-level-and-weight)
   - [Evaluation, stabilizers, and central equations](#94-evaluation-stabilizers-and-central-equations)
   - [The exact combined identification](#95-the-exact-combined-identification)
10. [Local convolution and the finite Hecke operators](#10-local-convolution-and-the-finite-hecke-operators)
    - [Why compatibility is not automatic from notation](#101-why-compatibility-is-not-automatic-from-notation)
    - [Global factorization of the Hecke action](#102-global-factorization-of-the-hecke-action)
    - [The class-set matrix](#103-the-class-set-matrix)
    - [Split unramified eigenvalues](#104-split-unramified-eigenvalues)
    - [Division places and level primes](#105-division-places-and-level-primes)
    - [Good eigenvalues identify the representation, not the vector](#106-good-eigenvalues-identify-the-representation-not-the-vector)
11. [Conductors, levels, and compact-open invariants](#11-conductors-levels-and-compact-open-invariants)
    - [Why level depends on a family of compact opens](#111-why-level-depends-on-a-family-of-compact-opens)
    - [Split local conductors](#112-split-local-conductors)
    - [Division local conductors](#113-division-local-conductors)
    - [Exact invariant dimensions at division places](#114-exact-invariant-dimensions-at-division-places)
    - [Global existence and dimension of fixed vectors](#115-global-existence-and-dimension-of-fixed-vectors)
12. [Newvectors, oldvectors, and new levels](#12-newvectors-oldvectors-and-new-levels)
    - [What a newspace is meant to isolate](#121-what-a-newspace-is-meant-to-isolate)
    - [Split-place oldvectors](#122-split-place-oldvectors)
    - [Division-place first occurrence](#123-division-place-first-occurrence)
    - [Global newlevel decomposition](#124-global-newlevel-decomposition)
    - [A dimension formula and its limit](#125-a-dimension-formula-and-its-limit)
13. [Twists, contragredients, and rationality](#13-twists-contragredients-and-rationality)
    - [Norm twists](#131-norm-twists)
    - [Twisting finite algebraic forms](#132-twisting-finite-algebraic-forms)
    - [Contragredients and dual spaces](#133-contragredients-and-dual-spaces)
    - [Fields of rationality](#134-fields-of-rationality)
    - [Galois conjugation and characters](#135-galois-conjugation-and-characters)
14. [Global matrix coefficients and trace distributions](#14-global-matrix-coefficients-and-trace-distributions)
    - [Why matrix coefficients are the next invariant](#141-why-matrix-coefficients-are-the-next-invariant)
    - [Orthogonality in its two correct settings](#142-orthogonality-in-its-two-correct-settings)
    - [Smoothing operators and their kernels](#143-smoothing-operators-and-their-kernels)
    - [Spectral and geometric traces](#144-spectral-and-geometric-traces)
    - [Fixed-level traces and Brandt traces](#145-fixed-level-traces-and-brandt-traces)
15. [Definite quaternion algebras over $\mathbf Q$](#15-definite-quaternion-algebras-over-mathbf-q)
    - [The Hurwitz one-class example](#151-the-hurwitz-one-class-example)
    - [A ray-level two-class calculation](#152-a-ray-level-two-class-calculation)
    - [General ideal classes and Brandt matrices](#153-general-ideal-classes-and-brandt-matrices)
    - [A two-class matrix worked symbolically](#154-a-two-class-matrix-worked-symbolically)
    - [Nontrivial weights](#155-nontrivial-weights)
16. [Reading local shape without asserting transfer](#16-reading-local-shape-without-asserting-transfer)
    - [What the global representation tells us intrinsically](#161-what-the-global-representation-tells-us-intrinsically)
    - [Descriptive contrast at a split place](#162-descriptive-contrast-at-a-split-place)
    - [The boundary of this book](#163-the-boundary-of-this-book)
17. [The final representation dictionary](#17-the-final-representation-dictionary)
    - [From finite input to global constituents](#171-from-finite-input-to-global-constituents)
    - [The dictionary in one table](#172-the-dictionary-in-one-table)
    - [From a global constituent back to finite modules](#173-from-a-global-constituent-back-to-finite-modules)
    - [Conclusion](#174-conclusion)

## 1. From finite quaternionic forms to global representations

### 1.1 The question behind the finite modules

Book 89 constructed finite-dimensional spaces of algebraic quaternionic forms. Compact-open double cosets act on them by finite sums of right translations, as we define and verify directly in Chapter 10. These constructions are deliberately concrete: a form is a function on finite adeles, its values lie in an algebraic weight, and a Hecke operator is a finite sum. They are exactly the objects needed for arithmetic calculations. Yet an eigensystem on one fixed-level space does not by itself explain why eigenvalues at different places belong to one object, why changing level produces old vectors rather than new global forms, or which local representation is being detected at a ramified place.

The missing object is an irreducible representation of the full adelic group. It packages all places at once:

$$
\pi\cong\bigotimes_v'\pi_v.
$$

Its archimedean factors encode weight, its finite factors encode level and ramification, and its compact-open fixed vectors are precisely what a finite algebraic module sees. The point of this book is to prove that this representation-theoretic description and the earlier finite description are not merely compatible but exactly identical after their conventions are aligned.

There is one subtlety from the outset. For a division quaternion algebra there are no proper rational parabolic subgroups, so the usual constant-term definition calls every automorphic form cuspidal. This includes one-dimensional characters obtained from reduced norm. In later comparisons the higher-dimensional spectrum and the character spectrum behave differently. We shall therefore use **intrinsically cuspidal** for the vacuous parabolic condition and **noncharacter** for an irreducible representation of dimension greater than one globally. The word **discrete** refers to occurrence in the discrete Hilbert spectrum. These are three distinct adjectives.

### 1.2 Standing notation and actions

Let $F$ be a number field, $D$ a quaternion algebra over $F$, and

$$
G=D^\times,\qquad Z=F^\times,\qquad PG=G/Z.
$$

For every place $v$, put $D_v=D\otimes_FF_v$ and $G_v=D_v^\times$. Write

$$
\mathbf A=\mathbf A_F,\qquad
G(\mathbf A)=\prod_v'G_v,
\qquad G_f=G(\mathbf A_{F,f}).
$$

At almost every finite place $D_v\cong M_2(F_v)$. After an integral splitting, the distinguished compact subgroup is

$$
K_v\cong\operatorname{GL}_2(\mathcal O_v).
$$

At a finite division place it is $K_v=\mathcal O_{D_v}^\times$. The restricted product is taken relative to these groups. A compact open subgroup of $G_f$ will normally be written $U=\prod_{v<\infty}U_v$, with $U_v=K_v$ almost everywhere.

All representations act on the left of their vector spaces, while the automorphic action on functions is right translation:

$$
(R(h)\phi)(g)=\phi(gh).
$$

Thus $R(h_1)R(h_2)=R(h_1h_2)$. Rational points act on the left and commute with this right action. The finite double-coset operators below use this same convention.

The reduced norm is denoted

$$
\operatorname{Nrd}:G(\mathbf A)\longrightarrow\mathbf A^\times.
$$

On a central scalar $z$ it is $z^2$. That square controls central characters, twists, and the separation of norm characters from genuinely nonabelian constituents.

### 1.3 The anisotropic and totally definite hypotheses

The group $PG$ is anisotropic over $F$ exactly when $D$ is a division algebra over $F$. In that case $PG$ has no nontrivial $F$-split torus and no proper $F$-parabolic subgroup. Section 2.2 proves directly, by reduction of the anisotropic ternary norm form, that

$$
PG(F)\backslash PG(\mathbf A)
$$

is compact. This is a global statement and remains true when some archimedean factor is split and hence noncompact. The proof uses the additive adelic lattice theorem, but with an essential extra step: the $F$-action and the norm tensor are retained during lattice reduction. They force the rational changes of basis into finitely many cosets of $PG(F)$. Without that tensor-retention step, additive compactness alone would not prove the assertion.

The case used most often earlier is stronger. Suppose $F$ is totally real and $D$ is ramified at every real place. Then

$$
G(F_\infty)=\prod_{\tau:F\hookrightarrow\mathbf R}\mathbf H^\times,
\qquad
PG(F_\infty)=\prod_\tau\mathbf H^\times/\mathbf R^\times
$$

is compact. We call $D$ **totally definite**. At fixed finite level, all remaining variables then form a finite set; an algebraic coefficient representation carries the entire archimedean content.

An important counterexample keeps the hypotheses honest. If $D=M_2(F)$, then $PG=\operatorname{PGL}_2$ contains the split diagonal torus. The classes of $\operatorname{diag}(t,1)$ escape to a cusp. Quotienting by scalar matrices removes the determinant direction but not the ratio of the two diagonal entries. Compactness modulo center is therefore a consequence of anisotropy, not of notation.

### 1.4 The route through the book

We first construct the adelic quotient and its measure, then define automorphic forms with a fixed central character. Compactness gives a purely discrete right regular spectrum. We factor its irreducible constituents into local representations and prove admissibility and finite multiplicity. We then isolate the multiplicity spaces. Characters are elementary; for noncharacters we use a character-clean two-place trace identity, global Whittaker multiplicity one and strong multiplicity one on the split group, and a local elliptic Bessel inequality. No Jacquet--Langlands correspondence is assumed. The argument proves both automorphic multiplicity one and strong determination from the almost-everywhere quaternionic Hecke data.

The second half returns to the finite modules. Archimedean weights select finite-dimensional local factors, stabilizer invariants identify fixed-level spaces exactly, and convolution identifies the abstract local Hecke action with the double-coset action already constructed. Conductors, compact-open invariants, twists, duals, rationality, and newlevel decompositions are then read locally. Finally, matrix coefficients and trace kernels prepare the compact trace formula, and examples over $\mathbf Q$ show how Brandt matrices decompose into global constituents.

## 2. The adelic group and compactness modulo the center

### 2.1 Restricted products and rational points

The notation $G(\mathbf A)=\prod_v'G_v$ means more than a product of abstract groups. An element $g=(g_v)$ must lie in $K_v$ for almost every finite $v$, and a basic neighborhood permits arbitrary motion at finitely many places while retaining $K_v$ elsewhere. This topology makes $G(\mathbf A)$ locally compact.

The diagonal subgroup $G(F)$ is discrete. To see the decisive point, embed the four-dimensional $F$-vector space $D$ diagonally in $D(\mathbf A)$. It is discrete by the additive adelic theorem. The condition $\operatorname{Nrd}(x)\ne0$ is open, and inversion is continuous there, so the same conclusion holds for $D^\times$. The quotient $G(F)\backslash G(\mathbf A)$ is consequently locally compact and Hausdorff.

The center is

$$
Z(\mathbf A)=\mathbf A^\times.
$$

It cannot be discarded. Even for totally definite $D$, the idele module gives a noncompact positive-real direction in $F^\times\backslash\mathbf A^\times$. The correct compact quotient is

$$
[PG]=Z(\mathbf A)G(F)\backslash G(\mathbf A)
\cong PG(F)\backslash PG(\mathbf A).
$$

Whenever we call the automorphic quotient compact, this quotient modulo the full adelic center is meant.

### 2.2 Adelic reduction for the anisotropic norm form

Compactness is the geometric engine of the book. We prove the general anisotropic statement here rather than importing it as an unnamed reduction-theory theorem.

**Theorem 2.1 (anisotropic compactness modulo center).** If $D$ is a quaternion division algebra over a number field $F$, then

$$
\boxed{Z(\mathbf A)G(F)\backslash G(\mathbf A)
\cong PG(F)\backslash PG(\mathbf A)\text{ is compact}.}
$$

**Proof strategy.** Conjugation identifies $PG$ with the special orthogonal group of the reduced norm on the trace-zero quaternions. That ternary form is anisotropic. Mahler reduction gives bounded representatives after integral changes of basis; retaining the $F$-module structure and the norm tensor shows that those changes of basis lie in finitely many rational orthogonal cosets. A finite adelic class set then assembles the archimedean reductions into the full quotient.

Put

$$
V=D^0=\ker(\operatorname{Trd}:D\to F),
\qquad q=\operatorname{Nrd}|_V.
$$

The form $q$ is nondegenerate. It is anisotropic over $F$: if $0\ne x\in V(F)$ satisfied $q(x)=0$, then $x$ would be a zero divisor in $D$. Conjugation preserves trace and norm and gives

$$
\operatorname{Ad}:D^\times/F^\times\longrightarrow\operatorname{SO}(V,q).
$$

Its kernel is the center. The image is a closed connected subgroup of dimension three, hence is all of the three-dimensional connected group $\operatorname{SO}(V,q)$. In characteristic zero the resulting bijective morphism of these smooth adjoint groups is an isomorphism. We may therefore write $H=PG=\operatorname{SO}(q)$.

We first prove the archimedean reduction needed below.

**Lemma 2.2 (anisotropic orthogonal reduction).** Let $q$ be a nondegenerate anisotropic quadratic form on a three-dimensional $F$-space $V$, let $H=\operatorname{SO}(q)$, and let $K_f\subset H(\mathbf A_f)$ be compact open. Then

$$
\Gamma_{K_f}\backslash H(F_\infty),
\qquad \Gamma_{K_f}=H(F)\cap K_f,
$$

is compact.

**Proof.** Choose an $\mathcal O_F$-lattice $L\subset V$ on which a scalar multiple of $q$ is integral, and put $K_L=H(\mathbf A_f)\cap\operatorname{GL}(\widehat L)$. The group

$$
H(F)\cap K_f\cap K_L
$$

has finite index both in $H(F)\cap K_f$ and in $H(F)\cap K_L$: the two index maps inject into the finite compact-open quotients $K_f/(K_f\cap K_L)$ and $K_L/(K_f\cap K_L)$. Compactness is unchanged by a finite cover or a finite quotient, so it is enough to use

$$
\Gamma_L=H(F)\cap\operatorname{GL}(L).
$$

Regard $L$ as a full $\mathbf Z$-lattice in

$$
W=\operatorname{Res}_{F/\mathbf Q}V(\mathbf R)
=\prod_{v\mid\infty}V(F_v).
$$

Every $h\in H(F_\infty)$ has real determinant one on $W$, so the lattices $h^{-1}L$ all have the same covolume. They also have a uniform lower bound on their shortest nonzero vector. Indeed, after the integral scaling of $q$, for $0\ne x\in L$,

$$
1\leq
\left|N_{F/\mathbf Q}(q(x))\right|.
$$

Since $h$ preserves $q$, with $y=h^{-1}x$ we have $q(y)=q(x)$. For fixed Euclidean norms at infinity there is a constant $C$ such that

$$
\left|N_{F/\mathbf Q}(q(y))\right|
\leq C\left(\max_{v\mid\infty}\|y_v\|_v\right)^{2[F:\mathbf Q]}.
$$

Thus every nonzero vector of every $h^{-1}L$ has length at least

$$
\varepsilon=C^{-1/(2[F:\mathbf Q])}>0. \tag{2.1}
$$

We recall the precise lattice reduction being used. A family of real lattices of fixed covolume and with shortest vector at least $\varepsilon$ is relatively compact modulo integral basis change. To prove it, choose successive shortest independent vectors. The elementary basis-reduction lemma replaces them by a lattice basis $b_1,\ldots,b_N$ with

$$
\prod_j\|b_j\|\leq C_N\operatorname{covol}(L).
$$

The lower bound on every successive minimum then bounds each $\|b_j\|$ above. The basis matrices are bounded, and their fixed nonzero determinant bounds their inverses. They consequently lie in a compact subset of $\operatorname{GL}(W)$. This is the usual proof of Mahler's compactness lemma and uses no group-specific reduction theorem.

Now take a sequence $h_n\in H(F_\infty)$. Applying this lattice lemma to $h_n^{-1}L$ gives $a_n\in\operatorname{GL}_{\mathbf Z}(L)$ such that

$$
c_n=h_n^{-1}a_n
$$

ranges in a fixed compact subset of $\operatorname{GL}(W)$. At this point an ordinary additive-lattice proof would have a gap: $a_n$ need not yet be $F$-linear or preserve $q$. We now retain the tensors that force both properties.

Choose a $\mathbf Z$-basis $\alpha_1,\ldots,\alpha_d$ of $\mathcal O_F$, and let $m(\alpha_j)$ be multiplication by $\alpha_j$ on $L$. Since $h_n$ is $F_\infty$-linear,

$$
a_n^{-1}m(\alpha_j)a_n
=c_n^{-1}m(\alpha_j)c_n. \tag{2.2}
$$

The left side is an integral matrix, while the right side remains bounded. Only finitely many integral matrices are bounded, so after passing to a subsequence every tensor in (2.2) is constant. Likewise

$$
q(a_nx)=q(c_nx),
$$

because $h_n$ preserves $q$. The coefficients of $q\circ a_n$ are algebraic integers in fixed fractional ideals and are bounded at every embedding by compactness of the $c_n$. There are only finitely many such coefficients. Passing to one further subsequence makes $q\circ a_n$ constant as well.

Fix an index $0$ in this subsequence and put

$$
\gamma_n=a_na_0^{-1}.
$$

The constancy in (2.2) says that $\gamma_n$ commutes with $F$, and constancy of the transported norm says that it preserves $q$. Hence

$$
\gamma_n\in\operatorname{O}(q)(F)\cap\operatorname{GL}_{\mathbf Z}(L).
$$

If its $F$-determinant is $-1$, multiply it by the fixed isometry $-1_V$, which also has determinant $-1$ because $\dim_FV=3$. We thereby obtain an element of $\Gamma_L=\operatorname{SO}(q)(F)\cap\operatorname{GL}(L)$, while changing bounded sets only by one fixed matrix. Finally,

$$
\gamma_n^{-1}h_n=a_0c_n^{-1}
$$

ranges in a compact set. Every sequence in $\Gamma_L\backslash H(F_\infty)$ therefore has a convergent subsequence. The quotient is metrizable and locally compact, so it is compact. $\square$

We assemble the finite and infinite places. For every compact open $K_f\subset H(\mathbf A_f)$, the class set

$$
H(F)\backslash H(\mathbf A_f)/K_f \tag{2.3}
$$

is finite. Here is the reduction to the already proved order theorem. The quotient map

$$
D^\times(\mathbf A_f)\longrightarrow H(\mathbf A_f)
$$

is onto. Indeed, local surjectivity follows from $H^1(F_v,\mathbf G_m)=0$, and at almost every place an integral projective point has an integral lift, so the local lifts form a restricted product. The same argument over $F$ identifies $H(F)$ with $D^\times(F)/F^\times$. Choose a compact open $U\subset D^\times(\mathbf A_f)$ whose image lies in $K_f$. Book 89 proves, by the order-ideal argument and without using definiteness at infinity, that

$$
D^\times(F)\backslash D^\times(\mathbf A_f)/U
$$

is finite. If $g_1,\ldots,g_r$ represent this last set and $h\in H(\mathbf A_f)$, lift $h$ to $g\in D^\times(\mathbf A_f)$ and write $g=\gamma g_i u$. Projecting gives

$$
h=\overline\gamma\,\overline g_i\,\overline u,
\qquad \overline u\in K_f,
$$

so the finitely many $\overline g_i$ cover (2.3).

Choose representatives $h_1,\ldots,h_r$ for (2.3) and put

$$
\Gamma_i=H(F)\cap h_iK_fh_i^{-1}.
$$

Then

$$
H(\mathbf A)
=\bigcup_{i=1}^rH(F)h_iK_fH(F_\infty).
$$

For each $i$, the corresponding part of $H(F)\backslash H(\mathbf A)$ is the continuous image of

$$
K_f\times\bigl(\Gamma_i\backslash H(F_\infty)\bigr).
$$

The first factor is compact and the second is compact by Lemma 2.2. A finite union of their images is compact. This proves Theorem 2.1. $\square$

In the totally definite case there is a shorter proof, and it remains useful. Choose $U=\widehat{\mathcal O}^{\times}$ and representatives $g_1,\ldots,g_h$ for the finite order class set. Every adelic element is $\gamma g_iug_\infty$, while

$$
Z(F_\infty)\backslash G(F_\infty)
=\prod_{v\mid\infty}F_v^\times\backslash D_v^\times
$$

is compact because every factor is Hamiltonian. The quotient is therefore covered by the images of finitely many compact products. Lemma 2.2 is exactly what replaces this last compact real factor when $D$ is split at one or more archimedean places.

The split counterexample also identifies the sharp boundary. For $D=M_2(F)$, the ternary determinant form on the trace-zero matrices has nonzero isotropic vectors. The lower bound (2.1) fails, rank-one rational lines survive reduction, and the diagonal cocharacters attached to them escape to cusps.

### 2.3 Totally definite finite-level quotients

Let $D$ now be totally definite and $U\subset G_f$ compact open. Since $PG(F_\infty)$ is compact, the quotient of $[PG]$ on the right by the image of $U\times G(F_\infty)$ is both compact and discrete, hence finite. Restoring the finite central fiber yields the finite set

$$
X_U=G(F)\backslash G_f/U.
$$

Choose representatives $g_1,\dots,g_h$ and define

$$
\Gamma_i=G(F)\cap g_iUg_i^{-1}.
$$

The subgroup

$$
C=F^\times\cap U
$$

is central and independent of $i$, and $\Gamma_i/C$ is finite. If $U=\widehat{\mathcal O}^{\times}$ for an order $\mathcal O$, then $g_i$ represents a locally principal right $\mathcal O$-ideal $I_i$ and

$$
\Gamma_i=\mathcal O_L(I_i)^\times.
$$

The left order appears because rational multiplication is on the left, whereas the fixed order and the level are on the right.

Compactness of $[PG]$ and finiteness of $X_U$ are related but not identical. The first is a statement about the full adelic quotient modulo center. The second also uses compactness of the archimedean projective group. For a division algebra split at a real place, $[PG]$ remains compact, but quotienting only by a finite level leaves a compact real orbifold rather than a finite set.

### 2.4 Haar measures and quotient measures

Choose Haar measures $dg_v$ on $G_v$ such that $\operatorname{vol}(K_v)=1$ at almost every finite place. Their restricted product gives $dg$ on $G(\mathbf A)$. The group is unimodular: this follows locally from the fact that left and right multiplication on the finite-dimensional algebra $D_v$ have the same determinant modulus, and then globally by restricted products.

Choose also $dz$ on $Z(\mathbf A)$ and quotient measures by Weil's formula. On the compact quotient $[PG]$ we may normalize

$$
\operatorname{vol}([PG])=1.
$$

This normalization is convenient for spectral orthogonality, but it must not be confused with the local convention $\operatorname{vol}(U_v)=1$ used for Hecke operators. Rescaling the global quotient measure rescales inner products and formal degrees; it does not change Hecke eigenvalues. Rescaling a local Haar measure does change the convolution operator unless the characteristic function is correspondingly renormalized.

For a unitary central character $\omega$, products $\phi_1(g)\overline{\phi_2(g)}$ descend to $[PG]$. Thus

$$
\langle\phi_1,\phi_2\rangle
=\int_{[PG]}\phi_1(g)\overline{\phi_2(g)}\,d\dot g
$$

is well defined. For an algebraic, possibly nonunitary character, one first removes its real norm power. Spectral assertions are made in the resulting unitary normalization; the algebraic normalization is restored afterward.

## 3. Automorphic forms when there are no cusps

### 3.1 Why the definition simplifies

For a split reductive group, automorphic forms need growth conditions because a fundamental domain has cuspidal ends, and cuspidality is tested by integrating along unipotent radicals. Here anisotropy removes both problems. Once the center has been fixed, the quotient is compact. Smooth functions and all their derivatives are bounded, and there is no parabolic direction along which a constant term could be taken.

Fix a continuous character

$$
\omega:F^\times\backslash\mathbf A^\times\longrightarrow\mathbf C^\times.
$$

Initially assume it unitary. A smooth automorphic form of central character $\omega$ is a function $\phi:G(\mathbf A)\to\mathbf C$ satisfying

$$
\phi(\gamma zg)=\omega(z)\phi(g)
\qquad (\gamma\in G(F),\ z\in Z(\mathbf A)),
$$

which is locally constant at finite places, smooth at archimedean places, fixed by some compact open subgroup of $G_f$, and finite under a maximal compact subgroup and the infinitesimal center at infinity. On a compact quotient moderate growth is automatic.

The right translates of such functions form the smooth, finite-vector part of the right regular representation. It is important not to define an automorphic representation as a single eigenfunction. An automorphic representation is an irreducible constituent generated by all right translates; a chosen fixed-level eigenvector is only one vector inside it.

### 3.2 Constant terms and their absence

For a connected reductive group, a proper parabolic subgroup $P=MN$ would give a constant term

$$
\phi_P(g)=\int_{N(F)\backslash N(\mathbf A)}\phi(ng)\,dn.
$$

But $D^\times$ has a proper $F$-parabolic subgroup exactly when the algebra $D$ has a nontrivial proper right ideal, equivalently when $D\cong M_2(F)$. If $D$ is division, no such $P$ exists. The condition that all proper constant terms vanish is therefore an empty conjunction.

This gives the useful but potentially misleading slogan that every automorphic form on an anisotropic quaternion algebra is cuspidal. It does **not** imply that every constituent is higher dimensional. Norm characters satisfy the same vacuous condition. Nor does it say anything about what those characters may correspond to in a later comparison with another group.

### 3.3 The full character spectrum

Reduced norm describes every one-dimensional automorphic representation, but its exact global image must be stated carefully. Put

$$
\mathbf A_D^\times=\operatorname{Nrd}(D^\times(\mathbf A)).
$$

At a split or nonarchimedean place the local reduced norm is onto $F_v^\times$; at a real ramified place its image is $\mathbf R_{>0}$. Similarly,

$$
F_D^\times=\operatorname{Nrd}(D^\times(F))
$$

consists of the elements of $F^\times$ positive at every real place ramified in $D$. The required topological abelianization follows from the local results already available:

$$
D^\times(\mathbf A)^{\mathrm{ab}}\cong\mathbf A_D^\times.
$$

At a split place, reduced norm is determinant and elementary matrices generate $\operatorname{SL}_2(F_v)$, the kernel of determinant. At a finite division place, Book 82 proves that the commutator subgroup is the reduced-norm-one group. At a ramified real place,

$$
\mathbf H^\times\cong\mathbf R_{>0}\times\operatorname{SU}(2),
$$

and $\operatorname{SU}(2)$ is perfect: its commutator subgroup has Lie algebra $[\mathfrak{su}_2,\mathfrak{su}_2]=\mathfrak{su}_2$, hence is open, and connectedness leaves no nontrivial discrete quotient. Thus every continuous local character factors uniquely through reduced norm.

The global kernel is the closure of the global commutator subgroup. Indeed, if $(g_v)$ has reduced norm one, truncate it to the identity outside a growing finite set of places. Each truncation is a finite product of local commutators, embedded one place at a time in the restricted product. The truncations converge to $(g_v)$ because its omitted components lie in the reference maximal compact. Conversely every commutator has reduced norm one. Since reduced norm is an open map onto its adelic image, it follows that the quotient by the closed commutator subgroup is topologically $\mathbf A_D^\times$. Thus every continuous character factors uniquely as $\psi\circ\operatorname{Nrd}$. Book 87 proves the global identity

$$
\operatorname{Nrd}(D^\times(F))=F_D^\times.
$$

Hence one-dimensional automorphic representations are exactly

$$
g\longmapsto\psi(\operatorname{Nrd}g),
$$

where $\psi$ is a character of $F_D^\times\backslash\mathbf A_D^\times$. A Hecke character of $F^\times\backslash\mathbf A^\times$ restricts to such a $\psi$, but in the presence of ramified real places this description by a character on the norm image is the intrinsic exhaustive statement.

In fact the inclusion of norm images induces an isomorphism

$$
F_D^\times\backslash\mathbf A_D^\times
\xrightarrow{\sim}
F^\times\backslash\mathbf A^\times. \tag{3.1}
$$

Injectivity follows because $F^\times\cap\mathbf A_D^\times=F_D^\times$. For surjectivity, use weak approximation to choose $a\in F^\times$ whose signs at the ramified real places make $ax$ positive there for a given idele $x$; then $ax\in\mathbf A_D^\times$. Thus every intrinsic $\psi$ has a unique idele-class character extension. We retain the norm-image notation because it records the local positivity restriction, while (3.1) is what pairs quaternionic norm characters with residual determinant characters in Proposition 7.2.

On the center,

$$
\omega_{\psi\circ\operatorname{Nrd}}(z)=\psi(z^2).
$$

Thus central character alone does not recover $\psi$: quadratic ambiguity can remain. In the totally definite algebraic theory, a norm character can occur in an irreducible weight $\bigotimes_\tau\operatorname{Sym}^{n_\tau}V_\tau\otimes\det^{m_\tau}$ only when every $n_\tau=0$. Matching the central exponent without matching the entire archimedean representation is insufficient.

### 3.4 Three spectra that must not be conflated

It is useful to display the terminology in one place:

| phrase | meaning for $D^\times$ | includes norm characters? |
|---|---|---:|
| intrinsically cuspidal | all proper parabolic constant terms vanish | yes, vacuously |
| discrete automorphic | occurs discretely in the right regular $L^2$ representation modulo center | yes |
| noncharacter automorphic | irreducible global constituent not one dimensional | no |

For an anisotropic quaternion algebra, the first two encompass the entire automorphic spectrum with unitary central character. The third is the part that carries genuinely noncommutative information. Over an integral coefficient ring, removing the character subspace need not split as a direct summand; the representation-theoretic separation is most transparent over characteristic zero.

## 4. The right regular discrete spectrum

### 4.1 The Hilbert space

Let $\omega$ be unitary. Define $L^2(G,\omega)$ to be the Hilbert space of measurable functions satisfying

$$
\phi(\gamma zg)=\omega(z)\phi(g)
$$

and square integrable over $[PG]$. Right translation is unitary because $G(\mathbf A)$ is unimodular. The compactness of $[PG]$ implies that the regular representation is a Hilbert direct sum, not a direct integral:

$$
L^2(G,\omega)
\cong\widehat{\bigoplus}_{\pi}m(\pi)\,\pi.
$$

Here $\pi$ runs through irreducible unitary representations with central character $\omega$, and $m(\pi)$ is a nonnegative integer. Chapter 6 first proves it finite; Theorem 7.3 then proves $m(\pi)=1$ for every constituent. We retain the symbol until that theorem has been established.

### 4.2 Why compactness produces discreteness

**Theorem 4.1 (discrete decomposition).** The right regular representation on $L^2(G,\omega)$ has purely discrete spectrum. At fixed compact-open level, fixed archimedean compact types, and bounded infinitesimal character, the corresponding subspace is finite dimensional.

**Proof strategy.** Freeze the finite level and archimedean compact type, so functions become sections of a finite-rank bundle on a compact orbifold. A positive elliptic operator at infinity has compact resolvent there. Its eigenspaces are finite dimensional, and right translations assemble them into irreducibles.

**Proof.** Choose $U\subset G_f$ and finitely many types of a maximal compact $K_\infty$. The $U$-fixed, selected-type functions descend to square-integrable sections on a compact finite union of arithmetic orbifolds. A positive elliptic combination of archimedean Casimir operators has compact resolvent on this compact space. The spectral theorem gives a discrete sequence of finite-dimensional eigenspaces. Taking the increasing union over levels and compact types gives the Hilbert direct sum above. $\square$

In the totally definite case the proof becomes elementary. The archimedean projective group is compact, so Peter--Weyl theory replaces elliptic analysis, and the finite quotient $X_U$ leaves only finitely many stabilizer-invariant fibers for every chosen infinity type.

### 4.3 Smooth vectors and irreducible automorphic representations

The Hilbert summand $\pi$ contains a dense subspace $\pi^\infty$ of smooth vectors: locally constant vectors at finite places and smooth vectors at infinity. Its $K_\infty$-finite, infinitesimal-character-finite part is the automorphic-form realization used algebraically.

An **irreducible automorphic representation of $D^\times$** is one of these irreducible smooth constituents. It comes with an embedding

$$
\iota:\pi\hookrightarrow\mathcal A(G,\omega),
$$

and $m(\pi)$ is the dimension of the space of such embeddings. Different vectors in $\pi^U$ are not different occurrences of $\pi$. Likewise, an eigenspace of dimension greater than one at an old level need not signal $m(\pi)>1$.

### 4.4 Character summands inside the regular spectrum

If $\chi=\psi\circ\operatorname{Nrd}$ has central character $\omega$, the function $g\mapsto\chi(g)$ spans a one-dimensional invariant subspace. Its norm is finite because its absolute value is constant on the compact central quotient in the unitary normalization.

Distinct automorphic characters are orthogonal. Indeed, the quotient of two is a nontrivial character of the compact quotient, and its integral is zero. Thus every automorphic character occurs with multiplicity one already by elementary Fourier theory. The noncharacter assertion is Theorem 7.3.

## 5. From one adelic representation to its local factors

### 5.1 Why factorization should exist

The adelic group permits independent motion at finitely many places. If an irreducible representation really records this product symmetry, its vectors should be assembled from local vectors. A literal infinite tensor product, however, is undefined until one chooses a reference vector at almost every place. The restricted-product topology supplies the correct references: at almost every finite place the group comes with $K_v$, and a global finite-level vector is fixed by all but finitely many $K_v$.

For representations $V_v$ with chosen nonzero vectors $e_v\in V_v^{K_v}$ almost everywhere, the restricted tensor product

$$
\bigotimes_v'V_v
$$

is the span of pure tensors $\bigotimes_vx_v$ for which $x_v=e_v$ except at finitely many places. Replacing $e_v$ by $c_ve_v$ at infinitely many places is not harmless: unless all but finitely many $c_v$ equal $1$, it changes the algebraic restricted product. Reference vectors are part of the construction, although the resulting isomorphism class is canonical when each spherical line is one dimensional.

### 5.2 The factorization theorem

**Theorem 5.1 (restricted tensor factorization).** Let $\pi$ be an irreducible automorphic representation of $G(\mathbf A)$. Then there are irreducible admissible local representations $\pi_v$ of $G_v$, unique up to isomorphism, such that

$$
\boxed{\pi\cong\bigotimes_v'\pi_v.}
$$

At almost every finite place, $D_v$ is split, $\pi_v^{K_v}$ is one dimensional, and the restricted tensor product is taken with respect to a nonzero vector in this line. Moreover

$$
\omega_\pi=\prod_v\omega_{\pi_v}
$$

on $Z(\mathbf A)$.

**Proof strategy.** Start from one nonzero finite-level vector. The commuting actions of finitely many local groups generate tensor products of irreducible local modules. Irreducibility of the global module prevents an extra quotient. Enlarging the finite set of active places and comparing the resulting factorizations produces the local factors and the spherical reference lines.

**Proof.** The compact-quotient argument of Theorem 4.1 first gives the required global admissibility: after fixing a finite compact open, an archimedean compact type, and the infinitesimal character of $\pi$, the corresponding vectors form a finite-dimensional space. Book 92 proves the restricted-product factorization lemma for any irreducible admissible module over

$$
H_\infty\times\prod_{v<\infty}'(H_v,K_v).
$$

Its proof uses the external-tensor-product theorem on every finite set of places, the mutual commutants of local convolution algebras on finite-dimensional compact-type shadows, and the one-dimensional spherical lines in the tail. None of those steps uses a special feature of $\operatorname{GL}_2$; the hypotheses are irreducibility, admissibility, and a restricted-product group. They hold here with $H_v=D_v^\times$. This formulation is important: merely choosing irreducible subquotients of the local restrictions would not construct an embedding and would not prove factorization.

Now choose $0\ne\varphi\in\pi$ fixed by $K_v$ outside a finite set $S$ containing every archimedean and every division place. For a finite set $T\supset S$, apply the finite-product lemma to the commuting action of $\prod_{v\in T}G_v$ and its complementary restricted product. It produces compatible irreducible factors

$$
\bigotimes_{v\in T}\pi_v,
$$

with the complementary factor containing a line fixed by every $K_v$ outside $T$. Compatibility as $T$ grows follows from uniqueness in the finite-product lemma. The union of the resulting finite tensors maps nontrivially and equivariantly to $\pi$, hence onto it; applying the same construction to the contragredient shows that the kernel is zero. At $v\notin S$, the local factor has a nonzero $K_v$-fixed vector. The one-dimensionality theorem for an irreducible spherical representation supplies its reference line. Central elements act factor by factor, giving the product formula for $\omega_\pi$. $\square$

The phrase “almost everywhere unramified” includes two assertions: $D_v$ is split and $\pi_v$ is spherical. The first fails only at the finite ramification set of $D$; the second fails only at finitely many additional places depending on $\pi$.

### 5.3 Split and division local factors

At a split finite place,

$$
G_v\cong\operatorname{GL}_2(F_v).
$$

An infinite-dimensional generic local factor may be principal-series, special, or supercuspidal. A one-dimensional local factor is a character $\mu_v\circ\det$ and is not generic; it requires character-compatible level rather than the generic newvector formulas below. At a division place, $G_v/F_v^\times$ is compact. Every irreducible smooth $\pi_v$ is finite dimensional, kills a sufficiently deep principal congruence subgroup, and is either a norm character or a higher-dimensional representation described by finite Clifford data.

This contrast is descriptive, not comparative. We do not identify a division-place representation with a representation of the split group. In particular, equal-looking conductor integers or character formulas are not themselves a theorem relating the two sides.

At a real ramified place, $D_v^\times\cong\mathbf H^\times$ is also compact modulo its center, and its irreducibles with a specified central character are finite dimensional. At a split real or complex place, ordinary archimedean representation theory is required. The totally definite case avoids those infinite-dimensional infinity types.

### 5.4 Spherical factors and their Hecke characters

Suppose $v$ is finite, split, and $K_v$ is hyperspecial. A spherical irreducible representation is determined by the character through which

$$
\mathcal H(G_v,K_v)
$$

acts on the line $\pi_v^{K_v}$. Let $T_v$ and $S_v$ be the unnormalized characteristic-double-coset operators defined by the convolution convention of Chapter 10. If

$$
T_ve_v=t_ve_v,\qquad S_ve_v=s_ve_v,
$$

then the integral Hecke polynomial is

$$
P_v(X)=1-t_vX+q_vs_vX^2.
$$

Its two reciprocal roots $A_v,B_v$ satisfy

$$
A_v+B_v=t_v,\qquad A_vB_v=q_vs_v.
$$

If normalized Satake parameters $\alpha_v,\beta_v$ are used, then $A_v=q_v^{1/2}\alpha_v$ and $B_v=q_v^{1/2}\beta_v$. Thus the raw double-coset trace is $q_v^{1/2}(\alpha_v+\beta_v)$. Keeping the raw and normalized parameters separate prevents a hidden square-root change in arithmetic formulas.

### 5.5 Ramified reference data

At a finite division place there is no spherical higher-dimensional representation for the maximal compact $\mathcal O_{D_v}^\times$. Indeed,

$$
\dim\pi_v^{\mathcal O_{D_v}^\times}=
\begin{cases}
1,&\pi_v=\mu_v\circ\operatorname{Nrd}
\text{ with }\mu_v\text{ unramified},\\
0,&\text{otherwise}.
\end{cases}
$$

Consequently a global level that is maximal at a division place sees only local norm characters there. To detect a higher-dimensional $\pi_v$, the level must be made smaller. For the normal principal congruence groups $U_{D_v}^m$, invariants are all or nothing:

$$
\pi_v^{U_{D_v}^m}=
\begin{cases}
0,&m<c_D(\pi_v),\\
\pi_v,&m\ge c_D(\pi_v).
\end{cases}
$$

This already shows why “the newvector line” cannot be imported unchanged from the split group.

## 6. Admissibility and finite multiplicity

### 6.1 Three finiteness statements

The following assertions are often compressed into one phrase, but they answer different questions.

1. **Local admissibility:** $\dim\pi_v^{J_v}<\infty$ for every compact open $J_v\subset G_v$.
2. **Global finite level:** for fixed $U$ and fixed infinity type, the automorphic space is finite dimensional.
3. **Finite spectral multiplicity:** $m(\pi)<\infty$ in the right regular representation.

None implies multiplicity one. A representation may occur once but contribute a ten-dimensional $U$-fixed space; conversely it could in principle occur several times while every local fixed space were one dimensional.

### 6.2 Finite-dimensional fixed-level spaces

In the totally definite case, let $\tau$ be a finite-dimensional representation of $G(F_\infty)$ compatible with $\omega_\infty$. The $\tau$-isotypic, $U$-fixed automorphic space is finite dimensional.

**Proof strategy.** Evaluate on the finite class set and record the arithmetic stabilizer at each class. Compactness modulo center makes each effective stabilizer finite.

Choose $g_1,\dots,g_h$ in $G_f$ as before. A vector-valued form is determined by values $w_i$ satisfying

$$
w_i\in W^{\Gamma_i},
$$

with finitely many additional equations if a finite central character is imposed. Since $h$ and $\dim W$ are finite, the result follows. Notice that no division by $|\Gamma_i/C|$ is needed over a field of characteristic zero merely to prove finite dimensionality; averaging is needed only for exactness and integral projectivity.

For an anisotropic algebra that is not totally definite, the same conclusion follows from elliptic theory on the compact real orbifold. Thus compactness modulo center, not total definiteness alone, is the global source of finiteness.

### 6.3 Admissibility of the local factors

**Proposition 6.1.** Every finite local factor $\pi_v$ of an automorphic representation is admissible. The archimedean factors are admissible in the usual compact-type sense.

**Proof strategy.** Embed a proposed local fixed space into a global fixed-type space by holding nonzero vectors at all other places fixed.

**Proof.** Let $v$ be finite and fix a compact open $J_v\subset G_v$. Choose a nonzero pure tensor in $\pi$ away from $v$, fixed by some compact open $U^v$ and of finitely many archimedean compact types. The map

$$
x\longmapsto x\otimes e^v
$$

injects $\pi_v^{J_v}$ into the global $(J_vU^v)$-fixed, fixed-infinity-type space. The target is finite dimensional by the preceding section, so $\pi_v^{J_v}$ is finite dimensional. At a division place this also follows from the stronger local theorem that every irreducible is finite dimensional. $\square$

### 6.4 Finite spectral multiplicity

**Proposition 6.2.** Every irreducible automorphic representation occurs with finite multiplicity.

**Proof.** Choose a compact open $U$ and an irreducible infinity type $\tau$ such that

$$
\pi_f^U\ne0,
\qquad
\operatorname{Hom}_{K_\infty}(\tau,\pi_\infty)\ne0.
$$

Each occurrence of $\pi$ contributes at least one line to the finite-dimensional $U$-fixed, $\tau$-isotypic space. Therefore $m(\pi)$ is bounded by its dimension. $\square$

This proof deliberately stops at finiteness. Compactness alone cannot force multiplicity one: the regular representation of a general compact quotient may contain an irreducible with multiplicity larger than one. The next chapter supplies the additional trace and strong-determination argument which makes every multiplicity space a line in the quaternionic automorphic quotient.

## 7. Multiplicity spaces and quaternionic unit multiplicity

### 7.1 What compactness proves

Compactness modulo the center proves discreteness and finite multiplicity, but not unit multiplicity. This distinction is logical, not stylistic: a compact quotient of a locally compact group can contain repeated irreducible summands. We therefore begin with the honest decomposition

$$
L^2(G,\omega)
\cong
\widehat{\bigoplus}_{\pi}
\mathcal M(\pi)\widehat\otimes\mathcal H_\pi,
\qquad
\mathcal M(\pi)
=\operatorname{Hom}_{G(\mathbf A)}
(\mathcal H_\pi,L^2(G,\omega)), \tag{7.1}
$$

for a unitary central character $\omega$. Chapter 6 proves

$$
0<m(\pi):=\dim\mathcal M(\pi)<\infty
$$

for every constituent which occurs. The group acts trivially on $\mathcal M(\pi)$ and through $\pi$ on $\mathcal H_\pi$.

The character case is elementary. If $\chi$ is one dimensional and $f(gh)=\chi(h)f(g)$ for every $h$, then $f(h)=f(1)\chi(h)$. Hence

$$
m(\chi)=1. \tag{7.2}
$$

The noncharacter proof below uses a genuinely global detector. It is important that it not be confused with compactness, local Schur orthogonality, or the tensor-factorization theorem.

### 7.2 The global multiplicity space

Choose a compact open $U\subset G_f$ and an irreducible infinity type $\tau$ occurring in $\pi_\infty$. The finite-dimensional shadow of (7.1) is

$$
\mathcal A(U,\tau,\omega)[\pi]
\cong
\mathcal M(\pi)\otimes
\operatorname{Hom}_{K_\infty}(\tau,\pi_\infty)
\otimes\pi_f^U. \tag{7.3}
$$

This separates three different dimensions:

$$
m(\pi),\qquad
\dim\operatorname{Hom}_{K_\infty}(\tau,\pi_\infty),
\qquad
\dim\pi_f^U.
$$

The first counts global embeddings, the second a compact type inside one archimedean factor, and the third level vectors inside one finite tensor product. Formula (7.3) proves finite multiplicity but cannot make its first factor a line.

Indeed, on the $\pi$-isotypic Hilbert summand,

$$
\operatorname{End}_{G(\mathbf A)}
(\mathcal M(\pi)\widehat\otimes\mathcal H_\pi)
\cong\operatorname{End}_{\mathbf C}(\mathcal M(\pi)). \tag{7.4}
$$

Every ordinary automorphic convolution operator is $1_{\mathcal M(\pi)}\otimes\pi(f)$. Thus the convolution algebra, however many local factors it contains, cannot by itself see off-diagonal endomorphisms of the multiplicity space.

### 7.3 Why the additive theta kernel is not the proof

The tempting additive kernel is

$$
\Theta_\Phi(g,h)=\sum_{x\in D(F)}\Phi(g^{-1}xh),
\qquad \Phi\in\mathcal S(D(\mathbf A)). \tag{7.5}
$$

This time Poisson summation is available, but it must be invoked with its complete normalization. Tensoring Book 98's one-dimensional Fourier theorem over an $F$-basis of $D$, and using the trace pairing

$$
(x,y)\longmapsto\psi(\operatorname{Trd}(xy)),
$$

gives a self-dual measure on $D(\mathbf A)$, Fourier inversion, and

$$
\sum_{x\in D(F)}\Phi(x)
=\sum_{x\in D(F)}\widehat\Phi(x). \tag{7.6}
$$

For $(L_gR_h\Phi)(x)=\Phi(g^{-1}xh)$, change of variables gives

$$
\widehat{L_gR_h\Phi}
=|\operatorname{Nrd}g|^2|\operatorname{Nrd}h|^{-2}
L_hR_g\widehat\Phi,
$$

so (7.6) does transpose the two variables, with the displayed similitude factor.

That valid identity still does not prove multiplicity one. Away from $x=0$, (7.5) is exactly the automorphic kernel obtained by periodizing the test function $\Phi|_{D^\times(\mathbf A)}$. On (7.1) its operator is

$$
1_{\mathcal M(\pi)}\otimes\pi(\Phi|_{D^\times}). \tag{7.7}
$$

Left and right translates change the second tensor factor and leave the first untouched. Hence these kernels do not separate $\operatorname{End}(\mathcal M(\pi))$. Any argument claiming that their pairings separate all localized two-variable kernels has already assumed that $\mathcal M(\pi)$ is a line. The zero orbit only contributes norm-character functionals and does not cure this obstruction. Poisson summation repairs the analytic identity, not the circular separation step.

### 7.4 The character-clean simple trace identity

We now introduce the global input which does see enough. It is a trace comparison, but it assumes neither local nor global Jacquet--Langlands. Only orbital integrals are matched. The split spectral side is then controlled by the Whittaker and Rankin--Selberg theorems already proved for $\operatorname{GL}_2$.

Let $R$ be the set of places at which $D$ is division. The local-invariant product formula says that $|R|$ is even. Since $D$ is a division algebra, $R$ is nonempty, and therefore

$$
|R|\geq2.
$$

At $v\in R$, regular conjugacy classes in $D_v^\times$ match elliptic regular classes in $\operatorname{GL}_2(F_v)$ by equality of reduced characteristic polynomials. With compatible quotient measures, write

$$
f_v^*\leftrightarrow f_v
$$

when

$$
O_{\gamma_v}(f_v^*)=-O_{\delta_v}(f_v)
$$

on matching regular classes and the split regular orbital integrals of $f_v^*$ vanish. At a split place the two functions are identical. The local minus sign is the Euler sign of the rank-one building; it disappears from a global product because $|R|$ is even.

We need a local geometric transfer and one estimate. Neither identifies a split representation attached to a division representation.

**Lemma 7.1 (local elliptic transfer and Bessel inequality).** Fix $v\in R$ and a unitary central character.

1. Every smooth compact-finite function on $D_v^\times$, compactly supported modulo the center and with the prescribed inverse central covariance, has a regular transfer to $\operatorname{GL}_2(F_v)$. The transfer can be chosen with zero split regular orbital integrals. Consequently its trace on every full normalized principal-series representation is zero.

2. For every irreducible representation $\rho$ of $D_v^\times$, choose a normalized matrix-coefficient pseudo-coefficient $e_\rho$, so

$$
\operatorname{tr}\rho'(e_\rho)=\delta_{\rho,\rho'}.
$$

Choose any regular transfer $e_\rho^*$ as in part 1. If $\sigma$ is an irreducible **generic** unitary representation of $\operatorname{GL}_2(F_v)$, then for every finite set $A$ of such $\rho$,

$$
\sum_{\rho\in A}
\left|\operatorname{tr}\sigma(e_\rho^*)\right|^2\leq1. \tag{7.8}
$$

If $\sigma$ is not square-integrable modulo the center, every term is zero.

**Proof.** We first construct the transfer. The trace--norm map is a submersion on the regular set. On a sufficiently small invariant-coordinate patch, integration along the conjugacy orbit therefore has a smooth local section: multiplying a transverse bump by the reciprocal orbit Jacobian prescribes its orbital integral. A partition of unity gives transfer on every compact regular subset.

Only accumulation at a scalar requires more. There the rank-one slice has precisely two nilpotent orbits, zero and regular nilpotent, so its orbital transform has two germs. On the division side only the zero germ occurs. On the split side use the alternating vertex--edge function on the Bruhat--Tits tree. For an elliptic torus its fixed subtree has a compact quotient and the weighted number of fixed vertices minus fixed edges equals its Euler characteristic; for a split torus the fixed apartment has Euler characteristic zero.

More concretely, separate the even and odd determinant-valuation shells and let $E_m$ be the normalized vertex--edge function on shell $m$. Its split orbital integrals are zero, while its elliptic orbital integral $b_m(t,n)$ is the nonzero weighted Euler characteristic of the fixed core. For the division orbital transform $A_D(t,n)=O_\delta(f_v)$ define, on each elliptic shell,

$$
A_m(t,n)=-\frac{A_D(t,n)}{b_m(t,n)}.
$$

Both numerator and denominator are locally constant in the regular trace--norm variables; the two-germ calculation says that $A_m$ has the required locally constant extension through every scalar-reduction annulus. Then

$$
f_v^*=\sum_m A_m(\operatorname{tr},\det)E_m
$$

has exactly the required orbital integrals. Only finitely many central shells occur modulo the prescribed central covariance, so the sum is a smooth compact-mod-center function. This completes the nonarchimedean transfer. At a ramified real place, the same construction is the two-term Euler--Poincare function; the elementary elliptic formula is the sine quotient displayed below. These constructions also show that changing the transfer without changing its regular orbital integrals changes no irreducible character trace: Weyl integration sees only the regular set.

The character of a normalized principal series is supported, in the Weyl formula, on split regular tori. Its trace against a transfer is consequently zero. This is trace-level cuspidality. We do not claim that a finite Euler transfer has zero two-sided parabolic operator; the two-place argument in Proposition 7.2 is designed precisely so that no such stronger assertion is needed.

Now the quotient $D_v^\times/F_v^\times$ is compact. Schur orthogonality, with the formal-degree normalization built into $e_\rho$, makes the irreducible division characters an orthonormal basis of its fixed-central-character elliptic trace space.

More explicitly, on either group use the elliptic character pairing

$$
\langle\Theta_1,\Theta_2\rangle_{\mathrm{ell}}
=\sum_T\frac1{|W(T)|}
\int_{F_v^\times\backslash T_{\mathrm{reg}}}
|D(t)|\Theta_1(t)\overline{\Theta_2(t)}\,dt, \tag{7.8a}
$$

where $T$ runs over elliptic maximal tori and every measure is the quotient measure used for orbital transfer. Weyl integration identifies the coefficient of $\Theta_\rho$ in this pairing with $\operatorname{tr}\rho(e_{\rho'})$, so the chosen division characters have pairing $\delta_{\rho,\rho'}$.

On the split group, Weyl integration separates split and elliptic tori. The rank-one unitary classification says that a generic irreducible is either induced or square-integrable modulo the center. An induced character is zero on elliptic regular classes. A square-integrable character has elliptic norm one. At a real place this is the elementary sine orthogonality of the discrete-series formula

$$
\frac{\sin((k-1)\theta)}{\sin\theta}.
$$

At a nonarchimedean place the same equality follows from the vertex--edge resolution of the Bruhat--Tits tree. Apply the alternating trace to the coefficient system of compact-fixed vectors. Exactness off the invariant vector identifies the boundary complex with the Jacquet module. An elliptic element has no fixed boundary point, so that term vanishes; Schur orthogonality on the remaining compact stabilizers gives one for a square-integrable irreducible and zero between inequivalent ones. For an induced irreducible the coefficient complex is its boundary complex, so its elliptic Euler character is zero. This proves the asserted norms without assigning a division representation to $\sigma$.

Signed regular transfer is an isometry for these elliptic pairings: matching tori, Weyl orders, discriminants, and quotient measures are identical, and the sign has absolute value one. Therefore the numbers $\operatorname{tr}\sigma(e_\rho^*)$ are Fourier coefficients of a vector of norm zero or one against an orthonormal family. Bessel's inequality gives (7.8). $\square$

We next record the global identity in exactly the form needed.

**Proposition 7.2 (character-clean two-place trace identity).** Let $f=\sum_j\otimes_v f_{j,v}$ be a finite sum of smooth test functions on $D^\times(\mathbf A)$ with fixed inverse central character. Assume that it has zero trace on every global norm character in the fixed finite level, infinity-type, and spectral window under consideration. At every $v\in R$, choose regular transfers as in Lemma 7.1. Normalize their scalar germs so that, for the quotient measures in use,

$$
\operatorname{vol}\bigl(PG(F)\backslash PG(\mathbf A)\bigr)f(1)
=\operatorname{vol}\bigl(\operatorname{PGL}_2(F)\backslash
\operatorname{PGL}_2(\mathbf A)\bigr)f^*(1). \tag{7.8b}
$$

Write the resulting split function as $f^*=\sum_j\otimes_v f_{j,v}^*$. Then

$$
\boxed{
\sum_{\sigma\ \mathrm{cuspidal}}
m_{\mathrm{GL}_2}(\sigma)\operatorname{tr}\sigma(f^*)
=
\sum_{\pi\ \mathrm{noncharacter}}
m_D(\pi)\operatorname{tr}\pi(f).} \tag{7.9}
$$

Both sums are finite after the stated projectors are imposed. Moreover, inside such a finite window the character-clean and scalar-germ conditions can be imposed while prescribing the trace coordinates of any finite list of noncharacter local tensor types.

**Proof.** We spell out the four independent ingredients.

First, the pre-multiplicity form of Chapter 14 gives the compact quaternionic trace as $\sum_\pi m_D(\pi)\operatorname{tr}\pi(f)$ and as a sum over rational conjugacy classes. Its kernel and geometric expansion use only compactness, so invoking them here does not use Theorem 7.3; Chapter 14 inserts $m_D(\pi)=1$ only after the present proof.

On the split side we use the following rank-one two-place form of the simple trace formula. Suppose a factorizable test has, at two distinct places $a$ and $b$, trace zero on every normalized principal series and zero split regular orbital integrals. After the residual determinant characters are written separately, its spectral and geometric expansions contain only the cuspidal and the central-plus-elliptic terms. Here is the proof. The constant-term spectral expansion from Books 100--103 is an integral of

$$
\operatorname{tr}\bigl(M(\chi,it)^{-1}M'(\chi,it)I(\chi,it)(f^*)\bigr).
$$

Factor $M$ and $I(f^*)$ locally and logarithmically differentiate $M$. Each summand has a derivative at one place. If that place is $a$, the undifferentiated trace factor at $b$ is zero; if it is $b$, the factor at $a$ is zero; if it is elsewhere, both are zero. The endpoint terms have the same factorization. On the geometric side, truncation organizes every split or unipotent boundary term as a sum in which at most one local Abel factor is differentiated; the zero split orbital transforms at $a$ and $b$ give the identical cancellation.

For completeness, removal of truncation is absolute here. The finite components confine $(\operatorname{tr}\gamma,\det\gamma)$ to a fixed fractional lattice and finitely many determinant ideals. The lattice count in a height ball is polynomial. Every archimedean factor and all of its derivatives decrease faster than any chosen power after the smoothing multiplier is inserted, while the torus-volume and local-orbital coefficients have polynomial growth by the idele-class and reduction estimates of Books 4 and 102. Taking the decay exponent larger than the sum of those polynomial exponents makes the elliptic series and its differentiated truncation tails summable. The trace-class factorization of Book 100 and the cusp-tail and constant-term bounds of Books 101--103 then justify taking the trace, differentiating the product, and passing to the limit. Thus two trace-cuspidal places suffice even when neither local operator is strongly cuspidal. Since $|R|\ge2$, Lemma 7.1 supplies $a$ and $b$ in every summand.

Second, rational regular classes on both sides are classified by the same trace and norm. A split rational class which has no division partner is split at some $v\in R$, where its orbital integral is zero. Matching classes have the same quadratic centralizer and the same adelic torus-volume coefficient. The product of the local transfer signs is $(-1)^{|R|}=1$. The split-torus and unipotent boundary terms are exactly the terms removed by the two-place cancellation just proved.

Third, the residual terms and the division characters match before they are removed. Identify a norm character with its unique idele-class extension $\eta$ by (3.1). If $\eta_v$ has the prescribed central square, Weyl integration and the local transfer sign give

$$
\operatorname{tr}(\eta_v\circ\det)(f_v^*)
=-\operatorname{tr}(\eta_v\circ\operatorname{Nrd})(f_v)
\qquad(v\in R).
$$

At split places the traces are equal. Multiplying over all places removes the signs because $|R|$ is even. Hence the trace of every residual determinant character on $f^*$ equals the trace of the corresponding quaternionic norm character on $f$. The character-clean hypothesis kills both, rather than pretending that an Euler function annihilates a residual quotient operator.

Fourth, regular transfer does not by itself determine the scalar term. Near a scalar, the split orbital transform has the zero and regular-nilpotent germs, while the division transform has only the zero germ. The alternating vertex--edge function makes the regular-nilpotent coefficient zero. A matching central bump changes the remaining coefficient by a nonzero scalar, so the resulting triangular two-germ system imposes equality of the two scalar distributions without disturbing matching away from that neighborhood.

It remains to justify the interpolation clause. Only finitely many irreducible characters and norm characters occur in the chosen window. Their local character distributions are linearly independent. The scalar distribution is a point mass, so it is independent of those locally integrable character distributions. Choose finitely many regular neighborhoods, disjoint from the scalar neighborhood, on which the resulting character-value matrix has full rank; local slice functions supported there give its inverse matrix. Tensoring these functions at finitely many auxiliary places separates the required global tensor types and the finitely many norm characters. The central bump then solves the last scalar equation. This finite triangular linear system prescribes the noncharacter coordinates, makes every character coordinate zero, and keeps the regular transfers matched. After these choices, the two trace formulas have equal central and regular terms, no continuous term, and no residual or norm-character term. Their remaining spectral expansions are exactly (7.9). Absolute convergence justifies the regrouping. $\square$

Nothing in Proposition 7.2 asserts a representation correspondence. Its inputs are the compact trace formula, the rank-one simple split trace formula, and orbital matching. In particular, it neither cites Book 94 nor assumes the theorem to be proved below.

### 7.5 Multiplicity one and strong determination

**Theorem 7.3 (quaternionic multiplicity one and strong determination).** Let $D$ be a quaternion division algebra over a number field $F$.

1. Every irreducible automorphic representation $\pi$ of $D^\times(\mathbf A)$ occurs with multiplicity one:

   $$
   \boxed{m_D(\pi)=1.} \tag{7.10}
   $$

2. If two irreducible automorphic representations $\pi$ and $\pi'$ are locally isomorphic at all but finitely many places, then

   $$
   \boxed{\pi\cong\pi'.} \tag{7.11}
   $$

**Proof strategy.** Localize the compact spectrum at one almost-everywhere spherical Hecke character. The split trace identity has at most one cuspidal constituent, occurring once, by global Whittaker multiplicity one and strong multiplicity one for $\operatorname{GL}_2$. Expand its ramified elliptic characters in the orthonormal division-character bases. A quaternionic multiplicity is one coefficient of that tensor expansion. Bessel bounds its absolute value by one, while occurrence makes it a positive integer.

**Proof.** The character assertion in (7.10) is (7.2), so let $\pi$ be a noncharacter and first make its central character unitary. Some local factor $\pi_u$ is not one dimensional; otherwise the restricted tensor product itself would be one dimensional. Choose a finite set $S$ containing $u$, all archimedean places, the ramification set $R$, and every finite place where $\pi$ is not spherical. Choose finite level, compact types, and a bounded infinitesimal-character window detecting $\pi$. The resulting automorphic space is finite dimensional.

The exact bounded window is legitimate in the trace identity. On each fixed level and compact type, the positive elliptic operator has discrete spectrum and trace-class heat kernel. Its Riesz projector onto a bounded interval is finite rank and is a trace-norm limit of rapidly decreasing functional-calculus multipliers. The kernel and orbital identities are continuous under that limit by the diagonal estimates used in Proposition 7.2. At split archimedean places the same Casimir multiplier is placed on both sides; at a ramified real place the finite-dimensional character projector and its discrete-series Euler transfer already select the desired infinitesimal character. Thus no formal infinite spectral projector is being inserted into (7.9).

The corresponding fixed-level, fixed-type, bounded window on the split cuspidal side is finite dimensional by the cuspidal compactness theorem of Book 102. Outside $S$, the spherical Hecke operators and their adjoints generate a commuting finite-dimensional $*$-algebra on the direct sum of the quaternionic window and this split window. Only finitely many characters of that algebra occur. For every character different from the full tail of $\pi$, choose one good place where it differs; finitely many such places and Lagrange interpolation then produce the exact projector onto

$$
\lambda^S=(\lambda_{\pi_v})_{v\notin S}. \tag{7.12}
$$

Apply this projector in (7.9), retaining arbitrary separating test functions at the places in $S$. On the split side, Book 104's global Whittaker theorem gives

$$
m_{\mathrm{GL}_2}(\sigma)=1
$$

for every cuspidal $\sigma$, and Book 106's Rankin--Selberg strong multiplicity-one theorem says that at most one such $\sigma$ has the good local data (7.12).

To prove existence without a scalar-term ambiguity, let $\mathscr P$ be the finite set of quaternionic constituents left by the window and (7.12). Irreducible local characters remain linearly independent when restricted to the regular noncentral set. Hence local slice functions at the finitely many places in $S$ give a finite tensor trace selector which is one on $\pi$ and zero on every other member of $\mathscr P$. At $u$, require it also to vanish on every one-dimensional local factor in the window; this is compatible with trace one on the non-one-dimensional $\pi_u$. Choose one slice support away from the scalar set. Its transfer is supplied by the regular slice construction in Lemma 7.1 and is also supported away from scalars. Thus both central terms are zero, while the factor at $u$ makes the test character-clean. The right side of (7.9) is $m_D(\pi)>0$, so a split cuspidal constituent exists. Call the unique one $\sigma$.

We now extract the tensor coefficient. Keep the character-killing condition at $u$ and vary the other local slice functions through the regular noncentral sets; at $u$ vary within the finite-codimension subspace annihilating the one-dimensional characters. Equation (7.9) is therefore an equality of finite sums of locally integrable tensor-character distributions on this regular product. The omitted scalar and singular sets have Haar measure zero. Cutting off successively smaller neighborhoods of them and using the finite elliptic $L^2$ norms in Lemma 7.1 extends the equality to the elliptic character Hilbert spaces. This is why the scalar interpolation in Proposition 7.2 introduces no extra coefficient here.

At a split place in $S$, transfer is the identity. Local character independence in the preceding distribution identity forces $\sigma_v\cong\pi_v$; otherwise a dual regular slice would make the quaternionic coefficient nonzero and the split coefficient zero. At $v\in R$, put

$$
c_v(\rho)=\operatorname{tr}\sigma_v(e_\rho^*)
$$

and express the same statement as the elliptic character expansion

$$
\Theta_{\sigma_v}^{\mathrm{ell},*}
=\sum_{\rho}c_v(\rho)\Theta_\rho,
\qquad
\sum_{\rho\in A}|c_v(\rho)|^2\leq1 \tag{7.13}
$$

for every finite set $A$, by Lemma 7.1. Evaluating the selected tensor in (7.9) now gives

$$
m_D(\pi)=\prod_{v\in R}c_v(\pi_v). \tag{7.14}
$$

All split-place coefficients are one. The left side of (7.14) is a positive integer, whereas (7.13) gives $|c_v(\pi_v)|\leq1$. Hence

$$
1\leq m_D(\pi)
=\left|\prod_{v\in R}c_v(\pi_v)\right|
\leq1.
$$

This proves (7.10). Notice that no local character identity was assumed: equality forces every coefficient occurring in (7.14) to have absolute value one after the global argument is complete.

It remains to prove (7.11) in all character cases. The central characters of nearly equivalent representations agree: their quotient is an idele-class character whose local components are trivial outside a finite set, and weak approximation in the product of the remaining local multiplicative groups forces it to be trivial.

If both representations are characters, write them as $\psi\circ\operatorname{Nrd}$ and $\psi'\circ\operatorname{Nrd}$. Local equality outside a finite set and surjectivity of reduced norm there make $\psi_v/\psi_v'$ trivial outside that set; the same weak-approximation argument gives $\psi=\psi'$. If exactly one representation is a character, apply the preceding split detector to the noncharacter one. At almost every split place its good local representation is then one dimensional. The unique spherical representation with that full $T_v,S_v$ Hecke character is the same one-dimensional representation, whereas every local factor of the cuspidal $\sigma$ is generic and hence infinite dimensional by Book 104. This contradiction rules out the mixed case.

Finally suppose both $\pi$ and $\pi'$ are noncharacters. Put them in the same localized window. They produce the same split cusp $\sigma$ by Book 106. The coefficient extraction above forces $\pi_v\cong\sigma_v\cong\pi_v'$ at every split place in $S$. If they differed at a ramified place $w$, formulas (7.10)--(7.14) would give

$$
|c_w(\pi_w)|=|c_w(\pi_w')|=1,
$$

contradicting the Bessel inequality

$$
|c_w(\pi_w)|^2+|c_w(\pi_w')|^2\leq1.
$$

Thus all local factors agree, and restricted tensor uniqueness gives (7.11).

Finally, an algebraic nonunitary normalization differs by a common real reduced-norm power. Twisting the automorphic space is an isomorphism, preserves occurrence dimensions and near equivalence, and reduces to the unitary case. $\square$

Consequently every $\mathcal M(\pi)$ in (7.1) is a line, though it has no preferred basis. A complete good-place Hecke character determines the unique global constituent, but it still does not determine a vector: infinity-type multiplicity and local oldvectors remain.

Here are the two downstream interfaces in exact form. Book 94 may begin its compact spectral comparison with $\sum_\pi m_D(\pi)\operatorname{tr}\pi(f)$ in order to track origins, but it must replace $m_D(\pi)$ by one using (7.10); neither Book 94's representation correspondence nor its later global theorem is used to obtain that value. For the one-split-real-place division algebra of Book 132, Matsushima's summand is

$$
\mathcal M(\pi)\otimes\pi_f^U\otimes A^1(\pi_\infty),
\qquad
\dim\mathcal M(\pi)=1,
\quad \dim A^1(\pi_\infty)=2,
$$

and therefore has the exact dimension $2\dim\pi_f^U$. This invocation uses the trace proof above, not the rejected additive-kernel argument of Section 7.3, and it requires no total-definiteness hypothesis.

## 8. Archimedean weights in the totally definite case

### 8.1 Why weight becomes a local representation

At a ramified real place $\tau$, write

$$
D_\tau^\times\cong\mathbf H^\times
\cong\mathbf R_{>0}\times\operatorname{SU}(2)
$$

up to the central sign. The projective factor is compact. Hence an irreducible representation with prescribed central character is finite dimensional and is determined by an irreducible $\operatorname{SU}(2)$-type together with its scalar action.

After complexification $D_\tau\otimes_\mathbf R\mathbf C\cong M_2(\mathbf C)$. For integers $n_\tau\ge0$ and $m_\tau\in\mathbf Z$, set

$$
W_\tau=\operatorname{Sym}^{n_\tau}V_\tau
\otimes\det^{m_\tau}.
$$

Its dimension is $n_\tau+1$, and a real scalar $a$ acts by $a^{c_\tau}$ with

$$
c_\tau=n_\tau+2m_\tau.
$$

The parity condition $c_\tau\equiv n_\tau\pmod2$ is unavoidable. A projective weight has $c_\tau=0$, hence $n_\tau$ even.

### 8.2 The dual forced by the action convention

Let

$$
W=\bigotimes_{\tau\mid\infty}W_\tau
$$

with action $\rho$. Book 89 used $W$-valued functions satisfying

$$
\Phi(g_fk_\infty)=\rho(k_\infty)^{-1}\Phi(g_f).
$$

Pairing with $\lambda\in W^\vee$ gives a scalar function

$$
\phi_\lambda(g)=\lambda(\Phi(g)).
$$

Then

$$
R(k_\infty)\phi_\lambda
=\phi_{\rho^\vee(k_\infty)\lambda},
\qquad
\rho^\vee(k)\lambda=\lambda\circ\rho(k)^{-1}.
$$

Therefore the scalar automorphic representation selected by the coefficient system $W$ has archimedean component $W^\vee$, not $W$. This dual is not a discretionary aesthetic choice; it is forced by left rational covariance together with right translation.

The central compatibility equation is equally forced. If the scalar automorphic central character is $\omega$, then

$$
\omega_\infty=\rho|_{Z_\infty}^{-1}.
$$

Thus the center of $W^\vee$ acts by $\omega_\infty$, exactly as it must.

### 8.3 Relation with algebraic coefficient systems

For the familiar weight tuple $k_\tau\ge2$, one takes $n_\tau=k_\tau-2$ and chooses determinant powers according to the desired algebraic normalization. The coefficient system is defined over a number field only after the quaternionic factors split and the tuple of embeddings descends. A nonparallel tuple may require a larger field than the field generated by its dimensions.

Local existence is not global compatibility. If an algebraic idele-class central character is to satisfy $\omega_\infty=\rho|_{Z_\infty}^{-1}$, its triviality on $F^\times$ and the unit theorem force the magnitude exponents $c_\tau=n_\tau+2m_\tau$ to be parallel. Its sign at each real place is then prescribed by $(-1)^{c_\tau}=(-1)^{n_\tau}$. The symmetric-power degrees $n_\tau$ may be nonparallel, but the determinant powers must compensate so that the central exponents have one common value and parity. A tuple of locally valid weights violating this condition selects no global automorphic representation with the proposed central character.

Over a coefficient ring, choose a stable lattice $W_A\subset W$. Stability under the finitely many arithmetic stabilizers is enough for the finite module; stability under a Hecke semigroup is an additional requirement for integral Hecke operators. The complex representation-theoretic decomposition is semisimple. Its integral lattice need not decompose, especially at primes dividing projective stabilizer orders.

### 8.4 Worked weights and a counterexample

Over $F=\mathbf Q$, weight two with $m=0$ has $W=\mathbf C$ and selects the trivial infinity type. Weight four has $W=\operatorname{Sym}^2\mathbf C^2$ up to its determinant normalization and selects its dual in the scalar spectrum. If the class set has one element with stabilizer the Hurwitz units, the automorphic module is

$$
W^{\mathcal H^\times}.
$$

It can be zero even though the class set is nonempty. The class number counts base points; it does not guarantee stabilizer-invariant vectors in a nontrivial weight.

As another counterexample, suppose two weights have the same central exponent but different $n$. Their central characters agree, but their $\operatorname{SU}(2)$-types have different dimensions and are nonisomorphic. A central-character match never substitutes for an archimedean-type match.

## 9. Exact recovery of the finite algebraic modules

### 9.1 The problem of comparing scalar and vector-valued forms

The spectral theory uses scalar-valued functions because a Hilbert inner product is then immediate. The definite algebraic theory uses $W$-valued functions because this removes the archimedean variable. To identify the two, one must retain the dual in Section 8.2 and the central character at both finite and infinite places.

Let $\mathcal A(\omega)$ denote the smooth automorphic forms of central character $\omega$, and let $\mathcal A(\omega)^U$ be its $U$-fixed subspace at the finite adeles. The exact comparison is

$$
\boxed{
S(U,W,\omega_f)
\cong
\operatorname{Hom}_{G(F_\infty)}
(W^\vee,\mathcal A(\omega)^U).}
$$

Here the Hom space uses the right regular action on $\mathcal A(\omega)$ and the contragredient action on $W^\vee$.

There is one normalization hypothesis behind the spectral use of this formula. If $\omega$ is unitary, $W^\vee$ is viewed in the corresponding unitary central normalization. If the algebraic data carry a real norm power, twist both the scalar automorphic action and the coefficient system by the same inverse norm power first. The Hom space is unchanged after this simultaneous renormalization, while the Hilbert decomposition becomes legitimate. A nonunitary algebraic central character must never be inserted directly into an $L^2$ decomposition on $[PG]$.

### 9.2 Proof of the scalar--vector identification

**Proof strategy.** Pair a vector-valued form with every linear functional on $W$. Conversely, reconstruct the vector from its scalar coordinates. Equivariance is precisely the right archimedean transformation law.

Given $\Phi\in S(U,W,\omega_f)$ and $\lambda\in W^\vee$, define

$$
T_\Phi(\lambda)(g)=\lambda(\Phi(g)).
$$

Section 8.2 proves that $T_\Phi$ intertwines $W^\vee$ with right translation. Rational invariance, finite level, and central character follow from the defining laws of $\Phi$.

Conversely, let $T:W^\vee\to\mathcal A(\omega)^U$ be an intertwiner. Choose a basis $e_1,\dots,e_d$ of $W$ with dual basis $e_1^\vee,\dots,e_d^\vee$ and put

$$
\Phi_T(g)=\sum_{j=1}^dT(e_j^\vee)(g)e_j.
$$

This formula is independent of the basis because it is the tensor corresponding to $T$ under $\operatorname{Hom}(W^\vee,\mathbf C)\cong W$. The intertwining law gives

$$
\Phi_T(gk_\infty)=\rho(k_\infty)^{-1}\Phi_T(g).
$$

The remaining covariance laws are checked coordinatewise. The two constructions are inverse, proving the claimed isomorphism.

### 9.3 The spectral formula at fixed level and weight

Insert the multiplicity-free decomposition, retaining each canonical occurrence line,

$$
\mathcal A(\omega)
\cong\bigoplus_\pi
\mathcal M(\pi)\otimes\pi_\infty\otimes\pi_f
$$

into the Hom space. One obtains

$$
\boxed{
S(U,W,\omega_f)
\cong
\bigoplus_{\pi:\,\omega_\pi=\omega}
\mathcal M(\pi)\otimes
\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\otimes\pi_f^U.}
$$

Only finitely many $\pi$ contribute. If $W$ is irreducible, the archimedean Hom factor is one dimensional precisely when $\pi_\infty\cong W^\vee$, and is zero otherwise. Thus in the standard irreducible-weight case,

$$
S(U,W,\omega_f)
\cong
\bigoplus_{\substack{\pi_\infty\cong W^\vee\\
\omega_\pi=\omega}}
\mathcal M(\pi)\otimes\pi_f^U.
$$

This is the fundamental fixed-level dictionary. Theorem 7.3 makes every $\mathcal M(\pi)$ a line, so the exact dimension formula is

$$
\dim S(U,W,\omega_f)
=\sum_\pi
\dim\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\cdot\dim\pi_f^U.
$$

The line $\mathcal M(\pi)$ remains in the canonical isomorphism because it has no preferred nonzero vector, but it contributes no numerical factor. Any dimension greater than one comes from the archimedean Hom space or from local fixed vectors, not from repeated automorphic occurrence.

### 9.4 Evaluation, stabilizers, and central equations

The same space has the finite description of Book 89. Choose

$$
G_f=\coprod_{i=1}^hG(F)g_iU,
\qquad
\Gamma_i=G(F)\cap g_iUg_i^{-1}.
$$

Without fixing the finite center, evaluation gives

$$
S(U,W)\xrightarrow{\sim}
\bigoplus_{i=1}^hW^{\Gamma_i}.
$$

Indeed, if $g=\gamma g_iu$, the inverse formula is

$$
f(g)=\rho(\gamma)w_i.
$$

It is well defined exactly because $w_i$ is fixed by $\Gamma_i$. If $g_i$ is replaced by $b_ig_iu_i$, then the invariant space is transported by $\rho(b_i)$; evaluation coordinates change, but the module does not.

For a fixed $\omega_f$, the center acts on $X_U$. If

$$
g_iz=\gamma_{i,z}g_{j(i,z)}u_{i,z},
$$

then the central-character subspace is cut out by

$$
\rho(\gamma_{i,z})w_{j(i,z)}
=\omega_f(z)w_i.
$$

Only finitely many $z$ need be used, representing

$$
F^\times\backslash\mathbf A_{F,f}^\times/(U\cap Z_f).
$$

The compatibility conditions

$$
\omega_\infty=\rho|_{Z_\infty}^{-1},
\qquad
\omega_f|_{U\cap Z_f}=1
$$

are what make these equations independent of every decomposition choice.

### 9.5 The exact combined identification

Putting the spectral and stabilizer descriptions together gives

$$
\boxed{
\left(\bigoplus_iW^{\Gamma_i}\right)_{\omega_f}
\cong
\bigoplus_\pi
\mathcal M(\pi)\otimes
\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\otimes\pi_f^U.}
$$

The subscript on the left means the finite central equations, not merely an abstract eigenspace when the coefficient ring is integral. Over $\mathbf C$ the central action is semisimple. Over a ring in which the order of the finite central quotient is not invertible, character idempotents may not exist and the integral module need not split.

For order level $U=\widehat{\mathcal O}^\times$, the left side becomes

$$
\left(
\bigoplus_{[I]}W^{\mathcal O_L(I)^\times}
\right)_{\omega_f}.
$$

Thus a local tensor product is not an extra structure placed beside ideal classes. It is the simultaneous irreducible decomposition of the same finite module of stabilizer-invariant ideal-class values.

## 10. Local convolution and the finite Hecke operators

### 10.1 Why compatibility is not automatic from notation

There are two apparent Hecke actions. The local representation $\pi_v$ admits convolution by compactly supported functions. The finite algebraic module admits the right-coset sums defined below. Their symbols agree only after Haar measure, right translation, and the choice of right cosets have been audited.

Normalize $dx_v$ by $\operatorname{vol}(U_v)=1$. For $\phi_v\in\mathcal H(G_v,U_v)$ define

$$
\pi_v(\phi_v)x
=\int_{G_v}\phi_v(h)\pi_v(h)x\,dh.
$$

If

$$
U_vaU_v=\coprod_ra_rU_v,
$$

then on $U_v$-fixed vectors

$$
\pi_v(\mathbf1_{U_vaU_v})x
=\sum_r\pi_v(a_r)x.
$$

No factor $[U_v:U_v\cap aU_va^{-1}]^{-1}$ appears. This is the unnormalized integral convention.

### 10.2 Global factorization of the Hecke action

The fixed-level Hecke algebra is the restricted tensor product

$$
\mathcal H(G_f,U)
=\bigotimes_{v<\infty}'\mathcal H(G_v,U_v),
$$

with reference idempotent $\mathbf1_{U_v}$. Under the spectral decomposition of Section 9.3, a pure tensor $\phi_f=\bigotimes_v\phi_v$ acts as

$$
1\otimes\pi_f(\phi_f)
=1\otimes\bigotimes_v\pi_v(\phi_v).
$$

Under the stabilizer model it acts by the finite correspondence

$$
(T_{UaU}f)(g)=\sum_{a_rU\subset UaU}f(ga_r).
$$

These are the same action. Indeed, both are obtained by integrating the right regular representation against $\mathbf1_{UaU}$, and each right coset has volume one. This proof also settles operator order:

$$
T_\phi T_\psi=T_{\phi*\psi},
\qquad
(\phi*\psi)(x)=\int\phi(y)\psi(y^{-1}x)\,dy.
$$

### 10.3 The class-set matrix

To compute the action, write

$$
g_ia_r=\gamma_{i,r}g_{j(i,r)}u_{i,r}.
$$

Then

$$
(T_{UaU}f)(g_i)
=\sum_r\rho(\gamma_{i,r})f(g_{j(i,r)}).
$$

This is a block matrix whose $(i,j)$ block sums the weight operators $\rho(\gamma_{i,r})$ for transitions from source row $i$ to target $j$. In trivial weight it becomes a Brandt matrix. Right multiplication by $a_r$ changes the right ideal, while $\gamma_{i,r}$ restores the chosen global representative on the left. Reversing either side produces the transpose correspondence with generally different weight factors.

Stabilizers also govern adjoints. With the mass pairing, the adjoint of $[UaU]$ is $[Ua^{-1}U]$. Ordinary matrix symmetry occurs only after the basis and stabilizer weights have been normalized appropriately. At an oriented level prime the inverse double coset can be genuinely different.

### 10.4 Split unramified eigenvalues

At a split hyperspecial place choose an integral splitting and a uniformizer $\varpi_v$. The operators are

$$
T_v=[K_v\operatorname{diag}(\varpi_v,1)K_v],
\qquad
S_v=[K_v\varpi_vI K_v].
$$

The first double coset has $q_v+1$ right cosets; the second has one. Hence constants have $T_v$-eigenvalue $q_v+1$. On a central-character space,

$$
S_v=\omega_f(z_v),
$$

where $z_v$ is the finite idele equal to $\varpi_v$ at $v$ and $1$ elsewhere. It is not a diagonal rational scalar.

If $f$ belongs to the $\pi$-summand, its eigenvalues on the spherical line are exactly those of $\pi_v^{K_v}$. Therefore

$$
1-T_vX+q_vS_vX^2
$$

specializes to the local polynomial $1-t_vX+q_v\omega_v(\varpi_v)X^2$. This is the precise compatibility promised by the finite construction.

### 10.5 Division places and level primes

At a finite division place with maximal compact $K_D$, a division uniformizer $\Pi$ gives one right coset

$$
K_D\Pi K_D=\Pi K_D.
$$

Thus $R_\Pi$ is literal right translation on $K_D$-fixed vectors and

$$
R_\Pi^2=S_v
$$

as a double-coset identity. There is no $q_v+1$ neighbor operator. At smaller level $J$, the double coset $J\Pi J$ may have several right cosets unless $J$ is normalized by $\Pi$.

At a split $K_0$-level, the operator usually called $U_v$ is likewise a characteristic-double-coset sum, generally of degree $q_v$. Its adjoint is the inverse-oriented operator $V_v$, not automatically a scalar multiple of $U_v$. These local asymmetries remain visible in the abstract action on $\pi_v^{U_v}$.

### 10.6 Good eigenvalues identify the representation, not the vector

The complete spherical Hecke character away from a finite set identifies the local factors there. Strong determination in Theorem 7.3 says that at most one global quaternionic constituent has those factors. Its contribution at level $U$ is

$$
\mathcal M(\pi)\otimes
\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\otimes\pi_f^U.
$$

The occurrence line $\mathcal M(\pi)$ has dimension one. The eigenspace can nevertheless be larger because the selected infinity type occurs more than once or because $\pi_f^U$ contains oldvectors. Level-prime operators act on those local fixed-vector factors and may separate vectors; they act trivially on the occurrence line. Repeated roots or a noncommutative local Hecke algebra can also prevent a simultaneous eigenbasis. Thus complete good-place eigenvalues select the global representation and its unique automorphic occurrence, but not a vector inside its fixed-level realization.

## 11. Conductors, levels, and compact-open invariants

### 11.1 Why level depends on a family of compact opens

A representation has no conductor until one specifies which compact subgroups are used to measure ramification. At a split place, the standard $K_1$ filtration singles out a canonical conductor exponent. At a division place, the normal principal congruence filtration measures how deeply the representation acts, but its first nonzero invariant space may have dimension greater than one. These are related notions, not interchangeable definitions.

Suppose first that every split finite factor of $\pi$ is infinite dimensional and generic. Let $a_v(\pi)$ be its $K_1$ conductor at a split place and the transfer-facing exponent $a_D(\pi_v)$ of Book 82 at a division place. Then define the selected conductor ideal

$$
\mathfrak f(\pi)=\prod_{v<\infty}\mathfrak p_v^{a_v(\pi)}.
$$

Only finitely many exponents are nonzero because $\pi_v$ is spherical with respect to the reference compact at almost every split place, while $D$ has only finitely many division places.

If a split local factor is one dimensional, no generic $K_1$ conductor exists for it. Such a factor must instead be recorded by the conductor of its defining character together with the compact type on which that character occurs. Assigning it the generic formula would be ill typed. Thus the displayed global ideal is used only under the generic-at-split-places hypothesis; arbitrary representations carry a family of typed local level data. This distinction is especially important for global norm characters.

### 11.2 Split local conductors

When $D_v$ is split, identify $G_v$ with $\operatorname{GL}_2(F_v)$ and define

$$
K_{1,v}(\mathfrak p_v^n)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in\operatorname{GL}_2(\mathcal O_v):
c\equiv0,\ d\equiv1\pmod{\mathfrak p_v^n}
\right\}.
$$

For an irreducible infinite-dimensional generic representation, put

$$
a_v(\pi)=\min\{n:\pi_v^{K_{1,v}(\mathfrak p_v^n)}\ne0\}.
$$

The invariant space at the minimal exponent is one dimensional. At exponent $m\ge a_v(\pi)$ its dimension is

$$
m-a_v(\pi)+1.
$$

This formula belongs to the $K_1$ filtration and to the generic category. It must not be transplanted to $K_0$ invariants without the central-character correction, nor to division principal congruence groups.

A one-dimensional representation $\mu_v\circ\det$ is different. Because the upper-left entry of $K_{1,v}(\mathfrak p_v^n)$ ranges over $\mathcal O_v^\times$, it has a $K_1$-fixed vector at some level if and only if $\mu_v$ is unramified; in that case it is already hyperspecial-fixed. A ramified norm character is detected by imposing the matching character on a $K_0$-type, or by shrinking to a principal congruence subgroup on which $\mu_v\circ\det$ is trivial. Its usual character conductor is finite, but it is not the minimum in the displayed generic $K_1$ definition.

### 11.3 Division local conductors

At a finite division place use the valuation normalized by

$$
v_D(x)=v_{F_v}(\operatorname{Nrd}x),
$$

so $v_D(\Pi)=1$ and $v_D(z)=2v_{F_v}(z)$ for central $z$. Let

$$
U_D^0=\mathcal O_D^\times,
\qquad U_D^m=1+\mathfrak P_D^m\quad (m\ge1).
$$

The congruence exponent and level are

$$
c_D(\pi_v)=\min\{m:U_D^m\text{ acts trivially on }\pi_v\},
\qquad
\ell_D(\pi_v)=\max\{c_D(\pi_v)-1,0\}.
$$

The conductor convention prepared in Book 82 is

$$
a_D(\pi_v)=
\begin{cases}
1,&\pi_v=\mu_v\circ\operatorname{Nrd},\ a(\mu_v)=0,\\
2a(\mu_v),&\pi_v=\mu_v\circ\operatorname{Nrd},\ a(\mu_v)>0,\\
\ell_D(\pi_v)+2,&\dim\pi_v>1.
\end{cases}
$$

The separate unramified character clause matters: its congruence exponent is zero, but its selected special-packet conductor is one. For a higher-dimensional level-zero representation, $a_D=2$. Thus selected conductor is not identical to first principal-congruence depth; it is the normalization fixed in Book 82 for the later local comparison.

### 11.4 Exact invariant dimensions at division places

Normality of $U_D^m$ gives

$$
\dim\pi_v^{U_D^m}=
\begin{cases}
0,&m<c_D(\pi_v),\\
\dim\pi_v,&m\ge c_D(\pi_v).
\end{cases}
$$

For a more refined compact open $H$, a compact-induction model $\pi_v=\mathrm{c\text{-}Ind}_J^{D_v^\times}\Lambda$ gives

$$
\dim\pi_v^H
=\sum_{x\in J\backslash D_v^\times/H}
\dim\operatorname{Hom}_{J\cap xHx^{-1}}(\Lambda,\mathbf1).
$$

This finite Mackey formula is the reliable way to calculate invariants for toral or Eichler-like levels. Conductor alone does not determine the answer. Two representations with the same $a_D$ can have different residue characters and hence different $H$-fixed dimensions.

### 11.5 Global existence and dimension of fixed vectors

For a factorizable level $U=\prod_vU_v$,

$$
\pi_f^U\cong\bigotimes_{v<\infty}\pi_v^{U_v},
\qquad
\dim\pi_f^U=\prod_{v<\infty}\dim\pi_v^{U_v}.
$$

All but finitely many factors equal one. If $W$ is irreducible, $\pi$ occurs in $S(U,W,\omega_f)$ precisely when

$$
\pi_\infty\cong W^\vee,
\qquad
\pi_v^{U_v}\ne0\text{ for every finite }v,
$$

and the central character matches. Its full isotypic contribution has the exact dimension

$$
\boxed{\prod_{v<\infty}\dim\pi_v^{U_v}.}
$$

There is no automorphic multiplicity factor: Theorem 7.3 gives $m(\pi)=1$ for characters and noncharacters alike.

For reducible $W$, multiply further by $\dim\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)$ and replace the displayed equality of infinity types by nonvanishing of that Hom space.

This criterion exposes a common false inference. Divisibility $\mathfrak f(\pi)\mid\mathfrak n$ guarantees invariants only when $\mathfrak n$ denotes the matching standard filtration. An arbitrary compact open of the same numerical index may detect a different type and have no invariants at all.

## 12. Newvectors, oldvectors, and new levels

### 12.1 What a newspace is meant to isolate

A fixed-level space mixes two phenomena. Some representations first become visible at that level; others were already visible at a coarser level and acquire more invariant vectors after the level is deepened. The first phenomenon is global variety, the second local multiplicity inside one representation. A newspace should isolate the first appearance of the local invariant type.

Let $U'\subset U$. Pullback is simply inclusion of invariants,

$$
\pi_f^U\hookrightarrow\pi_f^{U'},
$$

and on automorphic functions it is the identity function regarded at the deeper level. More general degeneracy maps first translate by an adelic element and then use such an inclusion. Their images span the oldspace.

There is no canonical notion of “all proper lower levels” among arbitrary compact opens. A newlevel decomposition therefore requires a specified directed family, such as $K_1(\mathfrak p^n)$ at a split place or $U_D^m$ at a division place.

### 12.2 Split-place oldvectors

At a split place suppose first that $\pi_v$ is infinite dimensional and generic, and let $n=a_v(\pi)$. Choose a nonzero local newvector $e_v^{\mathrm{new}}$ fixed by $K_{1,v}(\mathfrak p_v^n)$. For $m\ge n$, the vectors

$$
e_{v,j}=\pi_v\left(
\begin{pmatrix}\varpi_v^{-j}&0\\0&1\end{pmatrix}
\right)e_v^{\mathrm{new}},
\qquad 0\le j\le m-n,
$$

form a basis of $\pi_v^{K_{1,v}(\mathfrak p_v^m)}$. Thus the minimal space is a line and each extra exponent adds one old direction.

Globally, if the chosen split level exceeds the conductor by

$$
\mathfrak r=\prod_v\mathfrak p_v^{r_v},
$$

then tensor products of these local translates give

$$
\prod_v(r_v+1)
$$

oldvectors in the one global representation, before division-place and archimedean multiplicities are included. This count is not an automorphic multiplicity.

For a one-dimensional factor $\mu_v\circ\det$, the matching tower must instead remember the character on the determinant of its compact subgroup. Along any such tower the invariant or type-isotypic space is either zero or the same one-dimensional representation; there is no generic $m-n+1$ growth. Consequently character constituents must be added as their own blocks in a global oldspace calculation.

### 12.3 Division-place first occurrence

At a division place the normal chain behaves differently. Suppose $c=c_D(\pi_v)>0$. Then

$$
\pi_v^{U_D^{c-1}}=0,
\qquad
\pi_v^{U_D^c}=\pi_v.
$$

The representation first appears as a block of dimension $\dim\pi_v$, not as a distinguished line. At every deeper normal level $m>c$, the invariant space is still the same whole representation, so the inclusion from level $c$ is an isomorphism. There is no further oldvector growth along this chain.

This gives a quaternionic **newlevel block** rather than a canonical newvector. A line may become distinguished only after adding a toral type or another nonnormal compact-open condition. The finite Mackey formula determines whether such a type occurs and with what multiplicity.

For an unramified norm character, first occurrence is already at $U_D^0$ and the invariant line is one dimensional. For a level-zero higher-dimensional representation, first occurrence along the principal chain is at $U_D^1$, where the whole representation is fixed. Treating both as “level zero with one newvector” would erase their essential difference.

### 12.4 Global newlevel decomposition

Fix standard local towers at all finite places. In characteristic zero, decompose the automorphic space representation by representation. Its newlevel part at $U$ is

$$
S(U,W,\omega_f)^{\mathrm{new}}
=\bigoplus_{\pi:\,U\text{ is a first-occurrence type for }\pi}
\mathcal M(\pi)\otimes
\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\otimes N_U(\pi_f),
$$

where $N_U(\pi_f)$ is the tensor product of split generic newvector lines, split character-type lines, and division newlevel blocks. One may add another type-isotypic factor only after proving the corresponding local first-occurrence and oldspace-spanning statement. The oldspace is the sum of degeneracy images from proper coarser levels in these specified towers.

Because $\mathcal M(\pi)$ is a line, the numerical contribution of $\pi$ to the newlevel space is exactly

$$
\dim\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\cdot\dim N_U(\pi_f). \tag{12.1}
$$

With an invariant positive-definite inner product, the orthogonal complement of the oldspace equals this representation-theoretic newspace. Indeed, the spectral decomposition is orthogonal by isomorphism class, and every degeneracy map acts as the identity on the occurrence line $\mathcal M(\pi)$ while applying the local inclusion or translate on $\pi_f$. Local invariant theory therefore decides whether every vector in the unique occurrence comes from a coarser level or whether a first-occurrence summand remains.

Over an integral coefficient ring, the sum of old images may fail to be saturated, and its orthogonal complement may not split the module. The honest integral object is then the old submodule and the quotient by its saturation. Characteristic-zero newspace formulas must not be asserted unchanged after reduction.

### 12.5 A dimension formula and its limit

If all varying places are split, use $K_1$ towers, and all constituents being counted are generic at those places, write $D(\mathfrak n)$ for the fixed-level dimension. Let $N(\mathfrak d)$ be the sum, over representations of exact conductor $\mathfrak d$, of the archimedean multiplicity times every fixed local invariant dimension away from the varying split places. Automorphic multiplicity contributes no factor by Theorem 7.3. Then

$$
D(\mathfrak n)
=\sum_{\mathfrak d\mid\mathfrak n}
N(\mathfrak d)
\prod_{v\mid\mathfrak n}
\bigl(v(\mathfrak n)-v(\mathfrak d)+1\bigr).
$$

At one prime, second differences recover $N(m)$ from $D(m)$. Split character types contribute a different, constant first-occurrence kernel. At a division place the kernel is not the linear function $m-c+1$: it is zero before $c$ and $\dim\pi_v$ afterward. Consequently the inversion formula must be changed place by place. There is no universal divisor-sum formula independent of the local compact-open family.

## 13. Twists, contragredients, and rationality

### 13.1 Norm twists

Let $\eta$ be a character of $F_D^\times\backslash\mathbf A_D^\times$, or the restriction of a Hecke character when that notation is more convenient. Define

$$
(\pi\otimes\eta)_v
=\pi_v\otimes(\eta_v\circ\operatorname{Nrd}).
$$

Globally this is the representation generated by

$$
\phi(g)\longmapsto
\eta(\operatorname{Nrd}g)\phi(g).
$$

Its central character is

$$
\omega_{\pi\otimes\eta}=\omega_\pi\eta^2,
$$

where $\eta^2(z)$ abbreviates $\eta(z^2)$ on the available central norm image. At an unramified split place,

$$
t_v\longmapsto\eta_v(\varpi_v)t_v,
\qquad
s_v\longmapsto\eta_v(\varpi_v)^2s_v.
$$

Both roots of the raw Hecke polynomial acquire the factor $\eta_v(\varpi_v)$.

An unramified twist preserves conductor. A ramified twist may raise it, leave it unchanged, or lower it by cancellation. At a division place,

$$
(\mu\circ\operatorname{Nrd})\otimes\eta
=(\mu\eta)\circ\operatorname{Nrd},
$$

so its selected conductor is $1$ if $\mu\eta$ is unramified and $2a(\mu\eta)$ otherwise. In particular it is not a function of $a(\mu)$ and $a(\eta)$ alone.

### 13.2 Twisting finite algebraic forms

On finite-adelic forms the formula is

$$
(\operatorname{Tw}_\eta f)(g_f)
=\eta_f(\operatorname{Nrd}g_f)f(g_f).
$$

It preserves level only if $\eta_f\circ\operatorname{Nrd}$ is trivial on $U$, or if the level is refined to carry the corresponding type. Rational left covariance changes the algebraic weight by the inverse archimedean norm character. Thus a finite-order twist trivial at infinity preserves the weight, while an algebraic norm-power twist changes its determinant exponents.

If $UaU=\coprod a_rU$, all $a_r$ have the same norm-character value, and

$$
T_{UaU}\operatorname{Tw}_\eta
=\eta_f(\operatorname{Nrd}a)
\operatorname{Tw}_\eta T_{UaU}.
$$

This finite-sum identity proves the same eigenvalue transformation as the tensor-product description.

### 13.3 Contragredients and dual spaces

The contragredient factors locally:

$$
\pi^\vee\cong\bigotimes_v'\pi_v^\vee,
\qquad
\omega_{\pi^\vee}=\omega_\pi^{-1}.
$$

For unitary $\pi$, complex conjugation identifies the Hilbert contragredient with the conjugate representation. Algebraically, one should retain the smooth dual rather than silently applying complex conjugation to coefficients.

The finite mass pairing pairs

$$
S(U,W,\omega_f)
\times S(U,W^\vee,\omega_f^{-1})
\longrightarrow\mathbf C.
$$

Under it,

$$
[UaU]^*=[Ua^{-1}U].
$$

This is the finite shadow of the local pairing between $\pi_v$ and $\pi_v^\vee$. At a self-inverse spherical double coset, an appropriate central scalar may make the operator self-adjoint on a unitary central-character space. At oriented level, the inverse operator remains distinct.

### 13.4 Fields of rationality

For a finite automorphic representation $\pi_f$, define its field of rationality as the fixed field of

$$
\{\sigma\in\operatorname{Aut}(\mathbf C):
\pi_f^\sigma\cong\pi_f\}.
$$

For an algebraic infinity type, choose a number-field model of $W$, the central character, and the finite module. The Hecke operators then have matrices over a number field. Their eigenvalues are algebraic, and finitely many operators generate the image algebra. Hence every eigensystem occurring in $S(U,W,\omega_f)$ is valued in a finite extension.

The almost-everywhere spherical Hecke character has its own rationality field, generated by the $T_v$ and $S_v$ eigenvalues outside a finite set. Every automorphism fixing $\pi_f$ fixes this field. Conversely, if an automorphism fixes those good-place values, the conjugate constituent is nearly equivalent to $\pi$ and Theorem 7.3 identifies it with $\pi$. Thus the good Hecke field is the field of rationality of $\pi_f$. Both $T_v$ and the central value $S_v$ must be included; traces alone do not determine determinants when the central character is not fixed.

A field of rationality need not be a field of definition for the entire representation. Descent can be obstructed by a nontrivial endomorphism division algebra, and a particular ramified type may require a larger splitting field. What the finite Hecke calculation gives immediately is a number-field model of the eigencharacter and, when the eigenspace is a line, of that line.

### 13.5 Galois conjugation and characters

If $\sigma\in\operatorname{Aut}(\mathbf C)$, applying $\sigma$ to the algebraic finite module and its eigenvalues produces a conjugate good-place eigensystem with

$$
t_v^\sigma=\sigma(t_v),
\qquad
s_v^\sigma=\sigma(s_v)
$$

at unramified places in the raw algebraic normalization. The conjugate eigenspace is nonzero because the defining matrices and eigenvector equations are conjugated together. Strong determination gives one constituent, canonically denoted $\pi^\sigma$, with those conjugate good local factors. Its infinity type is transported through the algebraic coefficient system, not by applying $\sigma$ to analytic square roots $q_v^{1/2}$.

For a norm character $\psi\circ\operatorname{Nrd}$, the rationality field is generated by the relevant character values. Two characters can have the same central character $\psi^2$ but different rationality fields. This is another reason the character parameter itself, not only its restriction to the center, must be retained.

## 14. Global matrix coefficients and trace distributions

### 14.1 Why matrix coefficients are the next invariant

Hecke eigenvalues observe a representation through compact-open fixed vectors. Matrix coefficients observe all vectors and all group elements:

$$
c_{v,\lambda}(g)=\lambda(\pi(g)v),
\qquad v\in\pi,\ \lambda\in\pi^\vee.
$$

They are the bridge from local representation theory to convolution traces. Locally at a division place they are compactly supported modulo the center because the whole group is compact modulo center. A global abstract matrix coefficient is a function on $G(\mathbf A)$, however, and is generally not left invariant under $G(F)$. It therefore does **not** define a function on $[PG]$. Compactness of the automorphic quotient applies to automorphic vectors in their realization as functions, not to the group variable of an abstract matrix coefficient.

For a pure tensor $v=\bigotimes_vv_v$ and $\lambda=\bigotimes_v\lambda_v$, normalized so that $\lambda_v(v_v)=1$ at almost every spherical place,

$$
c_{v,\lambda}(g)=\prod_vc_{v_v,\lambda_v}(g_v).
$$

The product is restricted: almost every factor equals $1$ on $K_v$. Changing infinitely many reference normalizations would destroy this formula, which is why the reference vectors in Chapter 5 were recorded explicitly. At split places these coefficients need not be compactly supported modulo the center; the trace kernel below, rather than a quotient integral of $c_{v,\lambda}$, is the correct global object.

### 14.2 Orthogonality in its two correct settings

Let $\varphi$ and $\varphi'$ be vectors in the automorphic realizations of unitary $\pi$ and $\pi'$ with the same central character. These vectors are sections on the compact central quotient, and the spectral decomposition gives

$$
\int_{[PG]}
\varphi(g)\overline{\varphi'(g)}\,d\dot g=0
$$

when $\pi\not\cong\pi'$. This is global orthogonality of automorphic functions. It must not be replaced by the same-looking integral of abstract group matrix coefficients.

There is also a local statement. At a division place, matrix coefficients with inverse central characters can be integrated over the compact group $D_v^\times/F_v^\times$. Schur orthogonality gives the formal degree

$$
d(\pi_v)=
\frac{\dim\pi_v}
{\operatorname{vol}(D_v^\times/F_v^\times)}.
$$

This formula cannot be quoted numerically until the quotient volume is specified. These two orthogonality statements play different roles: the first separates global summands, while the second normalizes local convolution.

### 14.3 Smoothing operators and their kernels

Let $f$ be a smooth test function on $G(\mathbf A)$, compactly supported modulo $Z(\mathbf A)$ and satisfying

$$
f(zg)=\omega(z)^{-1}f(g).
$$

Right convolution defines

$$
(R(f)\phi)(x)=\int_{Z(\mathbf A)\backslash G(\mathbf A)}
f(g)\phi(xg)\,dg.
$$

On the compact quotient this is a smoothing, hence trace-class, operator. Its automorphic kernel is

$$
K_f(x,y)=
\sum_{\gamma\in Z(F)\backslash G(F)}
f(x^{-1}\gamma y).
$$

Compact support modulo center and discreteness of rational points make the sum locally finite; smoothness at infinity gives the regularity needed on the diagonal. The central equivariance of $f$ is exactly what makes both the quotient integral and the kernel independent of representatives.

### 14.4 Spectral and geometric traces

Integrating the diagonal kernel gives the spectral expansion

$$
\operatorname{tr}R(f)
=\boxed{\sum_\pi\operatorname{tr}\pi(f)},
$$

where $\pi$ runs only over constituents of central character $\omega$. Theorem 7.3 is exactly what removes the automorphic multiplicity coefficient. On the other hand, grouping rational elements by conjugacy gives

$$
\operatorname{tr}R(f)
=\sum_{[\gamma]}
\operatorname{vol}\bigl(
Z(\mathbf A)G_\gamma(F)\backslash G_\gamma(\mathbf A)
\bigr)
O_\gamma(f),
$$

with orbital integral

$$
O_\gamma(f)=
\int_{G_\gamma(\mathbf A)\backslash G(\mathbf A)}
f(x^{-1}\gamma x)\,dx.
$$

Here $[\gamma]$ runs over $G(F)$-conjugacy classes in $Z(F)\backslash G(F)$. The same quotient measures must be used in the coefficient and orbital integral. For regular noncentral $\gamma$, put $E=F(\gamma)$. Its centralizer is $E^\times$, and the coefficient quotient is

$$
Z(\mathbf A)E^\times\backslash\mathbf A_E^\times.
$$

It is compact, hence has finite volume. To prove this from Book 4, note that scalar extension sends an idele of $F$ with module $t$ to an idele of $E$ with module $t^2$. Thus every class modulo $Z(\mathbf A)$ has a norm-one representative. The norm-one idele class group $C_E^1$ is compact, so its continuous image covers the displayed quotient. In $Z(F)\backslash G(F)$ all central rational elements give the single identity class; its orbital integral is $f(1)$ and its coefficient is the volume of $[PG]$.

Because the quotient is compact, there are no truncation operators, continuous spectral integrals, or parabolic terms. This is the simple trace distribution prepared for later use. Nothing in its construction compares orbital integrals with those of another group.

### 14.5 Fixed-level traces and Brandt traces

Take $\mathbf1_{UaU}$ with $\operatorname{vol}(U)=1$ and form its central-character average

$$
f_f^\omega(g)
=\int_{Z_f}
\mathbf1_{UaU}(zg)\omega_f(z)\,dz,
$$

with the central measure normalized compatibly with quotient integration. Then $f_f^\omega(z_0g)=\omega_f(z_0)^{-1}f_f^\omega(g)$ and its support is compact modulo $Z_f$. Weil's formula shows that convolution by $f_f^\omega$ on the $\omega_f$-space is exactly convolution by $\mathbf1_{UaU}$, hence the unnormalized double-coset operator of Chapter 10. Choose the corresponding normalized central-character projector onto $W^\vee$ at infinity. The resulting global test function satisfies the equivariance required in Section 14.3. For irreducible $W$, the spectral trace is

$$
\sum_{\substack{\pi_\infty\cong W^\vee\\
\omega_\pi=\omega}}
\operatorname{tr}\bigl(\pi_f(\mathbf1_{UaU})\mid\pi_f^U\bigr).
$$

For reducible $W$, the corresponding $\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)$ multiplicity must also be inserted. The same number is the trace of the finite block matrix on the central-character submodule computed from

$$
g_ia_r=\gamma_{i,r}g_{j(i,r)}u_{i,r}.
$$

Thus a Brandt trace is already a compact automorphic trace. The geometric kernel explains its fixed points, while the irreducible decomposition explains its eigenvalues.

## 15. Definite quaternion algebras over $\mathbf Q$

### 15.1 The Hurwitz one-class example

Let

$$
D=(-1,-1)_{\mathbf Q}
$$

and let $\mathcal H$ be the Hurwitz maximal order. The algebra is ramified at $2$ and $\infty$, and the right ideal class set of $\mathcal H$ has one element. At maximal finite level and trivial weight,

$$
S(\widehat{\mathcal H}^\times,\mathbf C)=\mathbf C.
$$

The unique vector is the constant function, so the unique global constituent is the trivial norm character. For every odd prime $p$, the algebra is split and the raw operator $T_p$ has $p+1$ cosets. Therefore

$$
T_p=p+1,\qquad S_p=1,
$$

and

$$
1-(p+1)X+pX^2=(1-X)(1-pX).
$$

This factorization is not evidence of a hidden two-dimensional constituent. It is the spherical polynomial of the one-dimensional trivial representation in raw normalization. The example is a useful counterweight to the habit of calling every definite quaternionic eigenform noncharacter.

### 15.2 A ray-level two-class calculation

Keep the Hurwitz algebra but impose principal level at $3$. The level-three calculation of Book 89 gives

$$
X_{U(3)}\cong\mathbf F_3^\times=\{1,-1\},
$$

so the trivial-weight space is $\mathbf C^2$. For a prime $\ell\ne2,3$,

$$
B_\ell=
\begin{cases}
(\ell+1)I,&\ell\equiv1\pmod3,\\
(\ell+1)
\begin{pmatrix}0&1\\1&0\end{pmatrix},
&\ell\equiv-1\pmod3.
\end{cases}
$$

The eigenvectors are

$$
e_+=(1,1),\qquad e_-=(1,-1).
$$

The first is the trivial norm character. The second is the quadratic ray character modulo $3$ composed with reduced norm. Both have trivial central character because the square of the quadratic character is trivial. Thus the two simultaneous eigenlines are two distinct global constituents, each occurring once, but both lie in the character spectrum.

This example shows that being orthogonal to constants does not by itself imply being noncharacter. If the norm class quotient has nontrivial characters, they also occupy nonconstant eigenlines.

### 15.3 General ideal classes and Brandt matrices

Let $D/\mathbf Q$ be definite, $\mathcal O$ a maximal order, and

$$
I_1,\dots,I_h
$$

represent its right ideal classes. Trivial-weight forms are functions on these classes. For $p$ away from the discriminant, the Brandt matrix $B_p=(b_{ij})$ counts the $p+1$ local neighbors of $I_i$ that lie in the class of $I_j$, with automorphism orbits restored. Hence

$$
\sum_jb_{ij}=p+1.
$$

If $e_i$ is the effective projective stabilizer order, the mass adjoint relation is

$$
\frac{b_{ij}}{e_i}=\frac{b_{ji}}{e_j}.
$$

The commuting matrices $B_p$ are simultaneously diagonalizable for the positive mass pairing. The complete good-prime eigenpacket determines one global constituent by Theorem 7.3. If its class function factors through the reduced-norm class quotient, it lies in the norm-character subspace; the converse holds for every norm character visible at this weight and level. At maximal trivial weight every local invariant factor which occurs is a line, so the simultaneous good-prime eigenspace itself is a line. At deeper level the same unique constituent can instead have a larger oldspace.

### 15.4 A two-class matrix worked symbolically

Suppose the class set has two elements and the degree-$p+1$ Brandt matrix is

$$
B_p=
\begin{pmatrix}
a&p+1-a\\
b&p+1-b
\end{pmatrix}.
$$

The row-sum condition gives the eigenvector $(1,1)$ with eigenvalue $p+1$. The second eigenvalue is

$$
\lambda_p=a-b.
$$

A corresponding vector is $(p+1-a,-b)$ when it is nonzero. If the stabilizer orders are $e_1,e_2$, weighted self-adjointness forces

$$
\frac{p+1-a}{e_1}=\frac{b}{e_2}.
$$

This equality is a strong check on a neighbor enumeration.

One matrix does not determine whether the second line is a norm character. Compute the norm map on the two ideal classes. If they have distinct norm classes and the vector is the pullback of a character of that two-element quotient, the line lies in the one-dimensional character spectrum. If the two ideal classes lie in the same norm fiber, every nonconstant function on them is outside the norm-character subspace. The complete family of good $B_\ell$ determines the unique global constituent containing the line; the single number $\lambda_p$ determines much less.

### 15.5 Nontrivial weights

For weight $W$, replace scalar entries by blocks

$$
(B_p)_{ij}
=\sum_{r:\,j(i,r)=j}\rho(\gamma_{i,r}).
$$

The ambient space is

$$
\bigoplus_iW^{\mathcal O_L(I_i)^\times},
$$

not $W^h$. A class with a large unit group can contribute fewer weight vectors than a class with a small unit group. The spectral decomposition says that a common block-matrix eigensystem is a sum of contributions from global $\pi$ whose infinity component is $W^\vee$ and whose good local factors realize that eigensystem.

In particular, a one-class order can support a noncharacter global representation at nontrivial weight if $W^{\mathcal O^\times}\ne0$. The finite class coordinate is one dimensional as a set, but the coefficient fiber may contain a nontrivial irreducible infinity type. Conversely the invariant fiber may vanish, so class number one alone predicts neither existence nor dimension in higher weight.

## 16. Reading local shape without asserting transfer

### 16.1 What the global representation tells us intrinsically

For every automorphic constituent $\pi$, the tensor product supplies an actual representation $\pi_v$ at each place. Its intrinsic invariants include

- dimension and central character;
- compact-open invariant spaces and their Hecke actions;
- conductor relative to the appropriate local filtration;
- contragredient and norm twists;
- at division places, congruence level and Clifford or admissible-pair data;
- at split unramified places, the spherical polynomial.

These data are already enough to reconstruct every fixed-level finite module and every double-coset eigenvalue considered here.

### 16.2 Descriptive contrast at a split place

At a split finite place, the projective group is noncompact. Higher-dimensional irreducible representations are typically infinite dimensional, parabolic induction exists, hyperspecial spherical lines occur abundantly, and the lattice tree produces the degree-$q_v+1$ operator. Standard $K_1$ newvector theory gives a minimal line and linearly growing oldspaces.

At a division place, the projective group is compact. Every irreducible is finite dimensional, no parabolic induction exists inside $D_v^\times$, the maximal order is unique, and maximal-compact invariants occur only for unramified norm characters. Principal-congruence invariants jump from zero to the whole representation.

These statements compare geometry and invariant theory only. They do not pair an irreducible from one column with an irreducible from the other.

### 16.3 The boundary of this book

The proof of Theorem 7.3 uses the split cuspidal spectrum as a detector. For a noncharacter quaternionic constituent it forces a unique auxiliary cuspidal $\operatorname{GL}_2$ constituent with the same almost-everywhere spherical Hecke character. The equality case in the Bessel estimate says that, for this global pair, each ramified elliptic functional has one division-character coefficient. We do **not** promote that observation to a place-by-place correspondence for arbitrary local representations, compute its character sign, prove surjectivity onto a local or global image, or compare conductors, epsilon factors, and newvectors. Those are the transfer conclusions reserved for Book 94.

What has been established before that transfer theorem is the complete intrinsic input it needs: a discrete unit-multiplicity quaternionic spectrum, canonical occurrence lines, strong determination from almost all local factors, local tensor factors, fixed-level vectors, exact Hecke normalization, and the compact trace distribution. Book 94 may retain multiplicities while comparing traces; Theorem 7.3 supplies the exact quaternionic value one independently of its later local identifications.

## 17. The final representation dictionary

### 17.1 From finite input to global constituents

Start with a totally real field $F$, a totally definite quaternion algebra $D/F$, a compact open $U=\prod_vU_v$, an algebraic weight $W$, and a compatible central character $\omega$. Compute representatives

$$
G_f=\coprod_iG(F)g_iU
$$

and stabilizers $\Gamma_i=G(F)\cap g_iUg_i^{-1}$. The finite algebraic module is

$$
M(U,W,\omega_f)
=\left(\bigoplus_iW^{\Gamma_i}\right)_{\omega_f}.
$$

Simultaneously decompose the commuting good-place Hecke action. A complete characteristic-zero good-place eigensystem determines one global constituent by strong determination. It contributes precisely when

$$
\pi_\infty\cong W^\vee,
\qquad
\omega_\pi=\omega,
\qquad
\pi_v^{U_v}\ne0\quad (v<\infty).
$$

Its contribution is $\mathcal M(\pi)\otimes\pi_f^U$ in the irreducible-weight case. Since $\mathcal M(\pi)$ is a line, its dimension is exactly the product of the local invariant dimensions.

### 17.2 The dictionary in one table

| finite algebraic datum | global representation datum | exact local content |
|---|---|---|
| value in $W^{\Gamma_i}$ | scalar automorphic vectors of infinity type | $\pi_\infty\cong W^\vee$ |
| compatible $\omega_f$ equations | central character $\omega_\pi$ | $\omega_\infty=\rho|_Z^{-1}$ |
| class-set dimension | fixed-vector sum over constituents | $\sum_\pi\dim\pi_f^U$ for irreducible $W$ |
| right-coset sum $[UaU]$ | convolution on $\pi_f^U$ | $\sum_r\pi_f(a_r)$ |
| $T_v,S_v$ at a good split place | spherical Hecke character | $1-t_vX+q_vs_vX^2$ |
| Brandt common eigensystem | unique global constituent | $\mathcal M(\pi)\otimes\pi_f^U$ with $\dim\mathcal M(\pi)=1$ |
| level $U_v$ | local invariant condition | $\pi_v^{U_v}\ne0$ |
| standard exact level | conductor exponent | generic $K_1$, split character type, or division congruence data |
| degeneracy image | oldvector | translate of a smaller-level invariant |
| division first-occurrence block | local newlevel contribution | whole $\pi_v$ for the normal principal chain |
| finite twist of class functions | norm twist of $\pi$ | $\omega\mapsto\omega\eta^2$ |
| inverse-double-coset adjoint | contragredient | $\pi^\vee=\bigotimes_v'\pi_v^\vee$ |
| algebraic Hecke eigenvalues | good-place rationality field | field generated by the $T_v,S_v$ eigenvalues |
| functions through the norm class quotient | one-dimensional spectrum | $\psi\circ\operatorname{Nrd}$ |
| mass trace of a Brandt matrix | automorphic trace | spectral sum equals compact orbital sum |

Every line contains a convention that matters. The ideals are right ideals because the rational quotient is on the left and level is on the right. The stabilizer is a left-order unit group. The coefficient weight is dualized in the scalar spectrum. The $T_v$ operator is a sum, not an average. The central term is $q_vS_v$, and a central scalar has reduced norm equal to its square.

### 17.3 From a global constituent back to finite modules

Conversely, let

$$
\pi=\bigotimes_v'\pi_v
$$

be an irreducible automorphic representation of $D^\times(\mathbf A)$. To realize it in a finite algebraic module:

1. choose $W$ with $W^\vee\cong\pi_\infty$;
2. take $\omega=\omega_\pi$ and verify the finite and infinite compatibility laws;
3. choose $U_v$ with $\pi_v^{U_v}\ne0$ at every finite place, using $K_v$ almost everywhere;
4. form $U=\prod_vU_v$ and the finite stabilizer module;
5. identify the $\pi$-isotypic summand with $\mathcal M(\pi)\otimes\pi_f^U$;
6. read each local Hecke action from $\pi_v^{U_v}$.

If $\pi$ is a norm character, the resulting class function factors through reduced norm and may occur only in a compatible one-dimensional infinity weight. Characters and noncharacters both occur exactly once. Deeper level can nevertheless supply several vectors in that occurrence; their number is governed entirely by local invariant spaces.

### 17.4 Conclusion

For an anisotropic quaternion algebra, compactness modulo the center changes the nature of automorphic theory. There are no cuspidal ends, no parabolic constant terms, and no continuous spectrum. The right regular representation breaks discretely into irreducible tensor products, each with a one-dimensional occurrence space. Characters are handled directly; noncharacters require the character-clean trace and elliptic Bessel argument. The same argument proves that one near-equivalence class contains at most one global constituent.

In the totally definite case, the global spectrum is visible through finite algebra. The exact identity

$$
\left(\bigoplus_iW^{\Gamma_i}\right)_{\omega_f}
\cong
\bigoplus_{\substack{\pi_\infty\cong W^\vee\\
\omega_\pi=\omega}}
\mathcal M(\pi)\otimes\pi_f^U
$$

places ideal classes, stabilizer invariants, algebraic weights, occurrence lines, and local fixed vectors in one formula. Under this identity the Brandt operator is literally local convolution, its eigenvalues are the local spherical eigenvalues in the raw integral normalization, and a complete common eigenpacket determines one global constituent. Conductors describe first occurrence only relative to specified compact-open towers; split generic factors supply newvector lines, split characters require matching types, and division principal levels supply finite-dimensional newlevel blocks.

The resulting picture is both finite and global. A vector can be evaluated on finitely many ideal classes, yet its translates generate a representation spanning every place. A Hecke matrix can be computed by finitely many neighbor reductions, yet its eigencharacter records and determines the unramified tail of an adelic tensor product. A compact trace can be counted through rational conjugacy classes or summed once through each irreducible representation. This is the quaternionic automorphic representation: one coherent global symmetry whose finite shadows are exactly the algebraic modules constructed earlier.
