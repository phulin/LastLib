# Automorphic Representations of Quaternion Algebras

## Contents

1. [From finite quaternionic forms to global representations](#1-from-finite-quaternionic-forms-to-global-representations)
   - [The question behind the finite modules](#11-the-question-behind-the-finite-modules)
   - [Standing notation and actions](#12-standing-notation-and-actions)
   - [The anisotropic and totally definite hypotheses](#13-the-anisotropic-and-totally-definite-hypotheses)
   - [The route through the book](#14-the-route-through-the-book)
2. [The adelic group and compactness modulo the center](#2-the-adelic-group-and-compactness-modulo-the-center)
   - [Restricted products and rational points](#21-restricted-products-and-rational-points)
   - [Why anisotropy gives compactness](#22-why-anisotropy-gives-compactness)
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
7. [Multiplicity one by intrinsic quaternionic analysis](#7-multiplicity-one-by-intrinsic-quaternionic-analysis)
   - [The scope of the theorem](#71-the-scope-of-the-theorem)
   - [The quaternionic kernel](#72-the-quaternionic-kernel)
   - [The simple-spectrum lemma](#73-the-simple-spectrum-lemma)
   - [Strong determination from almost all places](#74-strong-determination-from-almost-all-places)
   - [What multiplicity one does and does not imply](#75-what-multiplicity-one-does-and-does-not-imply)
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
    - [Eigenvalues identify constituents, not vectors](#106-eigenvalues-identify-constituents-not-vectors)
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

Books 35 and 36 constructed finite-dimensional spaces of algebraic quaternionic forms and made compact-open double cosets act on them. Those constructions are deliberately concrete: a form is a function on finite adeles, its values lie in an algebraic weight, and a Hecke operator is a finite sum of right translations. They are exactly the objects needed for arithmetic calculations. Yet an eigensystem on one fixed-level space does not by itself explain why eigenvalues at different places belong to one object, why changing level produces old vectors rather than new global forms, or which local representation is being detected at a ramified place.

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

Thus $R(h_1)R(h_2)=R(h_1h_2)$. Rational points act on the left and commute with this right action. This convention is the same one used for the finite double-coset operators of Book 36.

The reduced norm is denoted

$$
\operatorname{Nrd}:G(\mathbf A)\longrightarrow\mathbf A^\times.
$$

On a central scalar $z$ it is $z^2$. That square controls central characters, twists, and the separation of norm characters from genuinely nonabelian constituents.

### 1.3 The anisotropic and totally definite hypotheses

The group $PG$ is anisotropic over $F$ exactly when $D$ is a division algebra over $F$. In that case $PG$ has no nontrivial $F$-split torus and no proper $F$-parabolic subgroup. The adelic quotient

$$
PG(F)\backslash PG(\mathbf A)
$$

is compact. This is a global statement. It may hold even when some archimedean factor is split and hence noncompact.

The case used most often earlier is stronger. Suppose $F$ is totally real and $D$ is ramified at every real place. Then

$$
G(F_\infty)=\prod_{\tau:F\hookrightarrow\mathbf R}\mathbf H^\times,
\qquad
PG(F_\infty)=\prod_\tau\mathbf H^\times/\mathbf R^\times
$$

is compact. We call $D$ **totally definite**. At fixed finite level, all remaining variables then form a finite set; an algebraic coefficient representation carries the entire archimedean content.

An important counterexample keeps the hypotheses honest. If $D=M_2(F)$, then $PG=\operatorname{PGL}_2$ contains the split diagonal torus. The classes of $\operatorname{diag}(t,1)$ escape to a cusp. Quotienting by scalar matrices removes the determinant direction but not the ratio of the two diagonal entries. Compactness modulo center is therefore a consequence of anisotropy, not of notation.

### 1.4 The route through the book

We first construct the adelic quotient and its measure, then define automorphic forms with a fixed central character. Compactness gives a purely discrete right regular spectrum. We factor its irreducible constituents into local representations and prove admissibility and finite multiplicity. A separate intrinsic argument proves multiplicity one; it uses harmonic analysis on the quaternion algebra itself and does not presuppose any comparison with a matrix group.

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

### 2.2 Why anisotropy gives compactness

The compactness theorem is the geometric engine of the book.

**Theorem 2.1 (compactness modulo center).** If $D$ is a division quaternion algebra over $F$, then

$$
Z(\mathbf A)G(F)\backslash G(\mathbf A)
$$

is compact.

**Proof strategy.** Apply the adelic anisotropy criterion to the projective group. In the quaternionic case its only possible escape direction would produce a rational isotropic line for the reduced norm. Division excludes that line.

**Proof.** Reduction theory for a connected semisimple group $H/F$ says that $H(F)\backslash H(\mathbf A)$ is compact exactly when $H$ has no proper $F$-parabolic subgroup. The compactness direction can be seen through the adelic lattice criterion: a sequence escaping every compact fundamental set has, after rational reduction, a shortest vector tending to zero; its limiting rational line is fixed by a proper parabolic. Conversely an $F$-parabolic contains a nontrivial split cocharacter, whose adelic translates escape.

Take $H=PG$. A proper $F$-parabolic of $PG$ is the stabilizer of a nonzero proper right ideal of $D$. Such an ideal exists exactly when $D$ is split. Equivalently, in the four-dimensional norm model, the limiting rational line would be spanned by a nonzero $x\in D(F)$ with $\operatorname{Nrd}(x)=0$. A division algebra has no such element. Hence $PG$ is anisotropic and

$$
PG(F)\backslash PG(\mathbf A)
$$

is compact. The identification with $Z(\mathbf A)G(F)\backslash G(\mathbf A)$ proves the theorem. $\square$

This argument is a quaternionic form of reduction theory. In the split algebra $M_2(F)$ the last contradiction fails: rank-one matrices are nonzero and have determinant zero. They are precisely the limiting shapes that create cusps.

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

consists of the elements of $F^\times$ positive at every real place ramified in $D$. The commutator theorem for $D^\times$ gives

$$
D^\times(\mathbf A)^{\mathrm{ab}}\cong\mathbf A_D^\times.
$$

Hence one-dimensional automorphic representations are exactly

$$
g\longmapsto\psi(\operatorname{Nrd}g),
$$

where $\psi$ is a character of $F_D^\times\backslash\mathbf A_D^\times$. A Hecke character of $F^\times\backslash\mathbf A^\times$ restricts to such a $\psi$, but in the presence of ramified real places this description by a character on the norm image is the intrinsic exhaustive statement.

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

For an anisotropic quaternion algebra, the first two encompass the entire automorphic spectrum with unitary central character. The third is the part that carries genuinely noncommutative information. Over an integral coefficient ring, removing the character subspace need not split as a direct summand; the representation-theoretic separation is cleanest over characteristic zero.

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

Here $\pi$ runs through irreducible unitary representations with central character $\omega$, and $m(\pi)$ is a nonnegative integer. At this stage we know only that it is finite. Multiplicity one is a later, special theorem.

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

Distinct automorphic characters are orthogonal. Indeed, the quotient of two is a nontrivial character of the compact quotient, and its integral is zero. Thus every automorphic character occurs with multiplicity one already by elementary Fourier theory. The difficult multiplicity-one assertion concerns higher-dimensional representations.

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

**Proof.** The compact-quotient argument of Theorem 4.1 first gives the required global admissibility: after fixing a finite compact open, an archimedean compact type, and the infinitesimal character of $\pi$, the corresponding vectors form a finite-dimensional space. We use the product theorem from the local representation theory of Book 38: over $\mathbf C$, an irreducible admissible representation of a finite product is the external tensor product of unique irreducible admissible representations of its factors. Its proof factors compact-open Hecke algebras, applies the density theorem to their simple nondegenerate modules, and then passes through the increasing union of compact types. This formulation is important: merely choosing irreducible subquotients of the restrictions would not construct an embedding and would not prove factorization. The archimedean analogue follows after fixing compact type and infinitesimal character.

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

acts on the line $\pi_v^{K_v}$. Let $T_v$ and $S_v$ be the unnormalized characteristic-double-coset operators of Book 36. If

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

This proof deliberately stops at finiteness. Compactness alone cannot force multiplicity one: the regular representation of a general compact quotient may contain an irreducible with multiplicity larger than one. The next chapter uses special arithmetic of a quaternion algebra.

## 7. Multiplicity one by intrinsic quaternionic analysis

### 7.1 The scope of the theorem

The theorem needed later has three parts.

**Theorem 7.1 (multiplicity one and strong determination).** Let $D$ be a division quaternion algebra over a number field $F$.

1. Every irreducible automorphic representation $\pi$ of $D^\times(\mathbf A)$ occurs in the discrete spectrum with multiplicity one.
2. If two noncharacter automorphic representations $\pi$ and $\pi'$ have $\pi_v\cong\pi'_v$ at all but finitely many places, then $\pi\cong\pi'$.
3. Automorphic norm characters also occur once. Two such characters agreeing locally almost everywhere agree globally. A norm character and a noncharacter representation are never identified by the theorem.

The proof below is internal to $D$. It uses the two-sided quaternionic kernel, Poisson summation on the four-dimensional additive adelic space $D(\mathbf A)$, and density of local convolution operators. No global transfer theorem is assumed.

### 7.2 The quaternionic kernel

Multiplicity one is deep even though the quotient is compact. The useful intrinsic input is not the standard zeta integral of one matrix coefficient: that integral controls a standard $L$-function, but orthogonal automorphic copies have identically zero mixed Hilbert coefficients, so their vanishing cannot contradict the existence of two copies. The required argument instead uses the two-sided action of $D^\times$ on the additive quaternion space.

Choose a nontrivial character of $F\backslash\mathbf A$ and the self-dual pairing

$$
(x,y)\longmapsto
\psi(\operatorname{Trd}(x\overline y)).
$$

For a Schwartz--Bruhat function $\Phi$ on $D(\mathbf A)$, form the two-sided kernel

$$
\Theta_\Phi(g,h)
=\sum_{x\in D(F)}
\Phi(g^{-1}xh).
$$

Central norm factors are inserted when $|\operatorname{Nrd}g|\ne|\operatorname{Nrd}h|$; equivalently one first works on equal-norm classes and then Mellin decomposes the remaining idele-module variable. Poisson summation on the four-dimensional additive quotient gives the Fourier identity for this kernel. The rational orbits in $D(F)$ are especially simple: $0$ is the singular orbit, and every nonzero element is invertible because $D$ is division. Thus the complement of $0$ is one $G(F)\times G(F)$-orbit, with diagonal stabilizer.

Unfolding the open orbit produces the diagonal pairing on automorphic forms. The zero orbit factors through reduced norm and therefore acts only on the character spectrum. This separation is exactly why norm characters must be removed before the nonabelian argument and restored afterward by ordinary Fourier theory.

### 7.3 The simple-spectrum lemma

The analytic consequence of the quaternionic kernel is the following form of the quaternionic multiplicity lemma.

**Lemma 7.2 (simple spectrum in a near-equivalence class).** Fix a unitary central character and prescribe an irreducible spherical factor at every place outside a finite set $S$. In the noncharacter part of $L^2(G,\omega)$, the sum of constituents with those prescribed factors is either zero or an irreducible representation of $G_S=\prod_{v\in S}G_v$. In particular it contains one global constituent, once.

**Proof strategy.** Localize the automorphic kernel by the spherical Hecke characters outside $S$. Poisson inversion makes the resulting two-sided kernels generate rank-one operators on the localized noncharacter space. An endomorphism commuting with $G_S$ must commute with all of them, hence is scalar. A semisimple finite-multiplicity $G_S$-module with scalar commutant is irreducible.

**Proof.** Work first at fixed level outside $S$ and fixed archimedean type, where Chapter 6 gives a finite-dimensional spectral space. Polynomial projectors in the finitely many spherical Hecke operators separate the characters occurring on this space. Enlarging the set of operators and taking the compatible intersection isolates the prescribed almost-everywhere spherical character; finite multiplicity makes the construction stable on every fixed-type block.

Apply the kernel of Section 7.2 on both sides of this projector. Unfolding the invertible orbit identifies its action with the diagonal $G_S$-pairing and places the resulting operators in the strong closure of the $G_S$ convolution algebra. Test functions supported in arbitrarily small neighborhoods of elements of $D_S^\times$, together with the Fourier-transformed kernel supplied by Poisson summation, separate every pair of nonzero compact-type vectors. Polarization then supplies the elementary matrix operators between them. The singular orbit contributes a product of reduced-norm functionals; it vanishes after projection to the noncharacter part. Therefore the strong closure of the localized convolution algebra contains the finite-rank operators on each fixed-type block.

Let $A$ commute with $G_S$. It commutes with its convolution algebra and its strong closure, hence with every rank-one operator just obtained. Linear algebra then makes $A$ scalar on each block. Compatibility as level and compact type vary makes the scalar independent of the block. The commutant of the localized $G_S$-module is consequently $\mathbf C$. The module is a Hilbert sum of irreducibles with finite multiplicities, so a scalar commutant forces exactly one irreducible summand with multiplicity one. $\square$

This is the decisive arithmetic input. It uses only the additive space underlying $D$, its reduced trace and norm, Poisson summation, and harmonic analysis on the same adelic group. No representation of another global group is constructed or invoked.

### 7.4 Strong determination from almost all places

Let $\pi$ and $\pi'$ be noncharacter automorphic representations with $\pi_v\cong\pi'_v$ outside a finite set $S$. They lie in the same localized space of Lemma 7.2. That space contains only one irreducible $G_S$-summand, so their remaining local tensor products agree and

$$
\pi\cong\pi'.
$$

Taking $\pi'=\pi$ in the same lemma proves that the occurrence multiplicity is one. For characters, multiplicity one was proved directly in Section 4.4. If two norm characters agree locally away from $S$, their quotient is a character of $F_D^\times\backslash\mathbf A_D^\times$ trivial on all ideles supported outside $S$. Approximation by principal elements, including the positivity condition at ramified real places, moves every $S$-component into those outside $S$; the quotient character is therefore trivial. Finally, a character and a noncharacter cannot be locally isomorphic almost everywhere: at every place a local isomorphism preserves dimension. This proves all parts of Theorem 7.1.

### 7.5 What multiplicity one does and does not imply

Multiplicity one gives

$$
m(\pi)=1.
$$

It does not give $\dim\pi_f^U=1$. At a deep division level the entire finite-dimensional local representation can be fixed; at an old split level the fixed space can have several degeneracy vectors. Nor does strong determination say that a short list of numerical invariants at bad places determines $\pi_v$. It uses the full local isomorphism class at almost every place.

A final caution concerns a commuting Hecke algebra. If one looks only at operators away from a finite set $S$, one global representation is determined, but its $U$-fixed vectors may form a multi-dimensional eigenspace. If too many good operators are omitted, different global representations may also share the remaining truncated eigensystem. Multiplicity one is a statement about representations, not about every finite list of matrices.

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

with action $\rho$. Book 35 used $W$-valued functions satisfying

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

Insert the multiplicity-one decomposition

$$
\mathcal A(\omega)
\cong\bigoplus_\pi\pi_\infty\otimes\pi_f
$$

into the Hom space. One obtains

$$
\boxed{
S(U,W,\omega_f)
\cong
\bigoplus_{\pi:\,\omega_\pi=\omega}
\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\otimes\pi_f^U.}
$$

Only finitely many $\pi$ contribute. If $W$ is irreducible, the first factor is one dimensional precisely when $\pi_\infty\cong W^\vee$, and is zero otherwise. Thus in the standard irreducible-weight case,

$$
S(U,W,\omega_f)
\cong
\bigoplus_{\substack{\pi_\infty\cong W^\vee\\
\omega_\pi=\omega}}
\pi_f^U.
$$

This is the fundamental fixed-level dictionary. It separates three dimensions that are easily confused:

$$
\dim S(U,W,\omega_f)
=\sum_\pi
\dim\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\cdot\dim\pi_f^U.
$$

There is no factor $m(\pi)$ because multiplicity one has been proved. An oldspace dimension belongs to $\pi_f^U$, not to the automorphic multiplicity.

### 9.4 Evaluation, stabilizers, and central equations

The same space has the finite description of Book 35. Choose

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

There are two apparent Hecke actions. The local representation $\pi_v$ admits convolution by compactly supported functions. The finite algebraic module admits the right-coset sums of Book 36. Their symbols agree only after Haar measure, right translation, and the choice of right cosets have been audited.

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

### 10.6 Eigenvalues identify constituents, not vectors

By strong determination, the complete spherical Hecke characters at almost all places identify at most one global noncharacter representation. Once that representation is identified, however, the eigenspace at level $U$ is

$$
\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\otimes\pi_f^U.
$$

It can have dimension greater than one. Adding level-prime operators may diagonalize it, but repeated roots or a noncommutative local Hecke algebra can prevent a simultaneous eigenbasis. Thus the dictionary is between a good-place eigensystem and a global constituent, not between such an eigensystem and a unique vector at every level.

## 11. Conductors, levels, and compact-open invariants

### 11.1 Why level depends on a family of compact opens

A representation has no conductor until one specifies which compact subgroups are used to measure ramification. At a split place, the standard $K_1$ filtration singles out a canonical conductor exponent. At a division place, the normal principal congruence filtration measures how deeply the representation acts, but its first nonzero invariant space may have dimension greater than one. These are related notions, not interchangeable definitions.

For every finite $v$, let $a_v(\pi)$ denote the exponent attached to the chosen standard local family: the generic $K_1$ conductor at a split generic factor, $2a(\mu_v)$ together with its character type for a split factor $\mu_v\circ\det$, and $a_D$ at a division factor. The factor two in the character case is the reduced-norm convention already used in Book 40; the least principal-congruence depth on which the character is trivial is instead $a(\mu_v)$. Define the resulting global conductor ideal

$$
\mathfrak f(\pi)=\prod_{v<\infty}\mathfrak p_v^{a_v(\pi)}.
$$

Only finitely many exponents are nonzero because $\pi_v$ is spherical with respect to the reference compact at almost every place.

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

The conductor convention prepared in Book 40 is

$$
a_D(\pi_v)=
\begin{cases}
2a(\mu_v),&\pi_v=\mu_v\circ\operatorname{Nrd},\\
\ell_D(\pi_v)+2,&\dim\pi_v>1.
\end{cases}
$$

The separate character clause matters: an unramified norm character has conductor zero, not two. For a higher-dimensional level-zero representation, $a_D=2$.

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

All but finitely many factors equal one. Thus $\pi$ occurs in $S(U,W,\omega_f)$ precisely when

$$
\pi_\infty\cong W^\vee,
\qquad
\pi_v^{U_v}\ne0\text{ for every finite }v,
$$

and the central character matches. The contribution has dimension the displayed product.

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
\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)
\otimes N_U(\pi_f),
$$

where $N_U(\pi_f)$ is the tensor product of split generic newvector lines, split character-type lines, division newlevel blocks, and any prescribed type-isotypic multiplicity spaces. The oldspace is the sum of degeneracy images from proper coarser levels.

With an invariant positive-definite inner product, the orthogonal complement of the oldspace equals this representation-theoretic newspace. The proof is immediate after the multiplicity-one spectral decomposition: local invariant theory decides, inside each $\pi$, whether every vector comes from a coarser level or whether a first-occurrence summand remains.

Over an integral coefficient ring, the sum of old images may fail to be saturated, and its orthogonal complement may not split the module. The honest integral object is then the old submodule and the quotient by its saturation. Characteristic-zero newspace formulas must not be asserted unchanged after reduction.

### 12.5 A dimension formula and its limit

If all varying places are split, use $K_1$ towers, and all constituents being counted are generic at those places, write $D(\mathfrak n)$ for the fixed-level dimension. Let $N(\mathfrak d)$ include the archimedean multiplicity and every fixed local invariant dimension away from the varying split places for representations of exact conductor $\mathfrak d$. Then

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

so its conductor is $2a(\mu\eta)$, not a function of $a(\mu)$ and $a(\eta)$ alone.

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

Strong determination shows that the field fixed by automorphisms preserving almost all spherical Hecke characters is the field of rationality of $\pi_f$. One must include both $T_v$ and the central value $S_v$, or else representations with different central characters can be conflated.

A field of rationality need not be a field of definition for the entire representation. Descent can be obstructed by a nontrivial endomorphism division algebra, and a particular ramified type may require a larger splitting field. What the finite Hecke calculation gives immediately is a number-field model of the eigencharacter and, when the eigenspace is a line, of that line.

### 13.5 Galois conjugation and characters

If $\sigma\in\operatorname{Aut}(\mathbf C)$, applying $\sigma$ to the algebraic finite module and its eigenvalues produces a conjugate constituent $\pi^\sigma$ with

$$
t_v(\pi^\sigma)=\sigma(t_v(\pi)),
\qquad
s_v(\pi^\sigma)=\sigma(s_v(\pi))
$$

at unramified places in the raw algebraic normalization. The infinity type is transported through the algebraic coefficient system, not by applying $\sigma$ to analytic square roots $q_v^{1/2}$.

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
=\sum_\pi m(\pi)\operatorname{tr}\pi(f)
=\sum_\pi\operatorname{tr}\pi(f),
$$

where $\pi$ runs only over constituents of central character $\omega$; the final equality uses multiplicity one and includes compatible norm characters. On the other hand, grouping rational elements by conjugacy gives

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

Here $[\gamma]$ runs over $G(F)$-conjugacy classes in $Z(F)\backslash G(F)$. The same quotient measures must be used in the coefficient and orbital integral. For regular noncentral $\gamma$, the centralizer is the multiplicative group of the quadratic field $F(\gamma)$, and the displayed central quotient has finite volume. In $Z(F)\backslash G(F)$ all central rational elements give the single identity class; its orbital integral is $f(1)$ and its coefficient is the volume of $[PG]$.

Because the quotient is compact, there are no truncation operators, continuous spectral integrals, or parabolic terms. This is the simple trace distribution prepared for later use. Nothing in its construction compares orbital integrals with those of another group.

### 14.5 Fixed-level traces and Brandt traces

Take $\mathbf1_{UaU}$ with $\operatorname{vol}(U)=1$ and form its central-character average

$$
f_f^\omega(g)
=\int_{Z_f}
\mathbf1_{UaU}(zg)\omega_f(z)\,dz,
$$

with the central measure normalized compatibly with quotient integration. Then $f_f^\omega(z_0g)=\omega_f(z_0)^{-1}f_f^\omega(g)$ and its support is compact modulo $Z_f$. Weil's formula shows that convolution by $f_f^\omega$ on the $\omega_f$-space is exactly convolution by $\mathbf1_{UaU}$, hence the unnormalized double-coset operator of Book 36. Choose the corresponding normalized central-character projector onto $W^\vee$ at infinity. The resulting global test function satisfies the equivariance required in Section 14.3. For irreducible $W$, the spectral trace is

$$
\sum_{\substack{\pi_\infty\cong W^\vee\\
\omega_\pi=\omega}}
\operatorname{tr}\bigl(\pi_f(\mathbf1_{UaU})\mid\pi_f^U\bigr).
$$

For reducible $W$, the corresponding $\operatorname{Hom}_{G(F_\infty)}(W^\vee,\pi_\infty)$ multiplicity must be inserted. The same number is the trace of the finite block matrix on the central-character submodule computed from

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

Keep the Hurwitz algebra but impose principal level at $3$. In the elementary model of Book 36,

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

The commuting matrices $B_p$ are simultaneously diagonalizable for the positive mass pairing. Each common eigenpacket determines, through Chapter 10 and strong determination, an irreducible global automorphic representation $\pi$ together with a vector in $\pi_f^{\widehat{\mathcal O}^\times}$. The packet is a norm character exactly when its class function factors through the reduced-norm class quotient.

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

One matrix does not determine whether the second line is a norm character. Compute the norm map on the two ideal classes. If they have distinct norm classes and the vector is the pullback of a character of that two-element quotient, the constituent is one dimensional. If the two ideal classes lie in the same norm fiber, every nonconstant function on them is automatically noncharacter. In either case, the complete family of good $B_\ell$ determines the global constituent, not the single number $\lambda_p$.

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

not $W^h$. A class with a large unit group can contribute fewer weight vectors than a class with a small unit group. The spectral decomposition says that a common block-matrix eigensystem belongs to a unique global $\pi$ whose infinity component is $W^\vee$.

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

No theorem in this book transports $\pi$ to an automorphic representation of $\operatorname{GL}_2(\mathbf A_F)$. We have not asserted that local conductors match across such a comparison, that a division character becomes a special representation, that character values differ by a sign, or that unramified Hecke polynomials are preserved by a global transfer. Those are conclusions requiring the transfer theorem reserved for Book 44.

What has been established independently is the complete quaternionic side to which such a theorem could later be applied: a multiplicity-one global spectrum, local tensor factors, fixed-level vectors, exact Hecke normalization, and trace distributions.

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

Simultaneously decompose the commuting good-place Hecke action. A characteristic-zero eigensystem determines a unique irreducible global representation $\pi$ provided the complete almost-everywhere spherical character is specified. It contributes precisely when

$$
\pi_\infty\cong W^\vee,
\qquad
\omega_\pi=\omega,
\qquad
\pi_v^{U_v}\ne0\quad (v<\infty).
$$

Its contribution is $\pi_f^U$, with dimension the product of local invariant dimensions.

### 17.2 The dictionary in one table

| finite algebraic datum | global representation datum | exact local content |
|---|---|---|
| value in $W^{\Gamma_i}$ | scalar automorphic vectors of infinity type | $\pi_\infty\cong W^\vee$ |
| compatible $\omega_f$ equations | central character $\omega_\pi$ | $\omega_\infty=\rho|_Z^{-1}$ |
| class-set dimension | sum of fixed-vector dimensions | $\sum_\pi\dim\pi_f^U$ for irreducible $W$ |
| right-coset sum $[UaU]$ | convolution on $\pi_f^U$ | $\sum_r\pi_f(a_r)$ |
| $T_v,S_v$ at a good split place | spherical Hecke character | $1-t_vX+q_vs_vX^2$ |
| Brandt common eigensystem | one global constituent | unique by strong determination |
| level $U_v$ | local invariant condition | $\pi_v^{U_v}\ne0$ |
| standard exact level | conductor exponent | generic $K_1$, split character type, or division congruence data |
| degeneracy image | oldvector | translate of a smaller-level invariant |
| division first-occurrence block | local newlevel contribution | whole $\pi_v$ for the normal principal chain |
| finite twist of class functions | norm twist of $\pi$ | $\omega\mapsto\omega\eta^2$ |
| inverse-double-coset adjoint | contragredient | $\pi^\vee=\bigotimes_v'\pi_v^\vee$ |
| algebraic Hecke eigenvalues | field of rationality | field fixed by $\pi_f^\sigma\cong\pi_f$ |
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
5. identify the $\pi$-summand with $\pi_f^U$;
6. read each local Hecke action from $\pi_v^{U_v}$.

If $\pi$ is a norm character, the resulting class function factors through reduced norm and may occur only in a compatible one-dimensional infinity weight. If $\pi$ is noncharacter, its full good-place eigenpacket cannot coincide with that of a norm character. At deeper level, several vectors may realize the same $\pi$; none creates an additional global occurrence.

### 17.4 Conclusion

For an anisotropic quaternion algebra, compactness modulo the center changes the nature of automorphic theory. There are no cuspidal ends, no parabolic constant terms, and no continuous spectrum. The right regular representation breaks discretely into irreducible tensor products, each with finite multiplicity; intrinsic quaternionic zeta analysis sharpens that multiplicity to one. One-dimensional norm characters remain present and must be separated by their full reduced-norm parameter rather than by central character alone.

In the totally definite case, the global spectrum is visible through finite algebra. The exact identity

$$
\left(\bigoplus_iW^{\Gamma_i}\right)_{\omega_f}
\cong
\bigoplus_{\substack{\pi_\infty\cong W^\vee\\
\omega_\pi=\omega}}
\pi_f^U
$$

places ideal classes, stabilizer invariants, algebraic weights, and local fixed vectors in one formula. Under this identity the Brandt operator is literally local convolution, its eigenvalues are the local spherical eigenvalues in the raw integral normalization, and its common eigenpackets are global irreducible constituents. Conductors describe first occurrence only relative to specified compact-open towers; split generic factors supply newvector lines, split characters require matching types, and division principal levels supply finite-dimensional newlevel blocks.

The resulting picture is both finite and global. A vector can be evaluated on finitely many ideal classes, yet its translates generate a representation spanning every place. A Hecke matrix can be computed by finitely many neighbor reductions, yet its eigencharacter determines an adelic tensor product. A compact trace can be counted through rational conjugacy classes or summed through irreducible representations. This is the quaternionic automorphic representation: one coherent global symmetry whose finite shadows are exactly the algebraic modules constructed earlier.
