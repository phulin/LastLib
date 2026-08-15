# Archimedean GL₂ and Discrete Series

## Contents

- [1. The archimedean problem](#1-the-archimedean-problem)
  - [1.1 Why infinity is a local place](#11-why-infinity-is-a-local-place)
  - [1.2 Conventions that govern the book](#12-conventions-that-govern-the-book)
- [2. The real reductive group](#2-the-real-reductive-group)
  - [2.1 Components, center, and derived group](#21-components-center-and-derived-group)
  - [2.2 Polar decomposition and maximal compact subgroups](#22-polar-decomposition-and-maximal-compact-subgroups)
  - [2.3 The upper half-plane and Cartan decomposition](#23-the-upper-half-plane-and-cartan-decomposition)
  - [2.4 Split and elliptic Cartan subgroups](#24-split-and-elliptic-cartan-subgroups)
- [3. Lie algebra and infinitesimal structure](#3-lie-algebra-and-infinitesimal-structure)
  - [3.1 Cartan involution and root vectors](#31-cartan-involution-and-root-vectors)
  - [3.2 Compact weights and raising operators](#32-compact-weights-and-raising-operators)
  - [3.3 The center of the enveloping algebra](#33-the-center-of-the-enveloping-algebra)
- [4. From continuous representations to Harish--Chandra modules](#4-from-continuous-representations-to-harish--chandra-modules)
  - [4.1 Smooth and compact-finite vectors](#41-smooth-and-compact-finite-vectors)
  - [4.2 Admissibility and finite generation](#42-admissibility-and-finite-generation)
  - [4.3 Infinitesimal and central characters](#43-infinitesimal-and-central-characters)
  - [4.4 Irreducibility and globalization](#44-irreducibility-and-globalization)
- [5. Principal series in rank one](#5-principal-series-in-rank-one)
  - [5.1 Normalized induction](#51-normalized-induction)
  - [5.2 The compact picture and compact types](#52-the-compact-picture-and-compact-types)
  - [5.3 Intertwining and reducibility](#53-intertwining-and-reducibility)
  - [5.4 Unitary, complementary, and finite-dimensional cases](#54-unitary-complementary-and-finite-dimensional-cases)
- [6. Discrete and limit-of-discrete series](#6-discrete-and-limit-of-discrete-series)
  - [6.1 Lowest- and highest-weight modules](#61-lowest--and-highest-weight-modules)
  - [6.2 Passage from the identity component to GL2](#62-passage-from-the-identity-component-to-gl2)
  - [6.3 The reducible principal series and the modules D-k](#63-the-reducible-principal-series-and-the-modules-d-k)
  - [6.4 Square integrability and its boundary](#64-square-integrability-and-its-boundary)
  - [6.5 Classification in the required range](#65-classification-in-the-required-range)
- [7. Parameters and exact normalizations](#7-parameters-and-exact-normalizations)
  - [7.1 The family D-k-s](#71-the-family-d-k-s)
  - [7.2 Infinitesimal character and contragredient](#72-infinitesimal-character-and-contragredient)
  - [7.3 Weil parameters](#73-weil-parameters)
- [8. Explicit characters](#8-explicit-characters)
  - [8.1 Characters as invariant distributions](#81-characters-as-invariant-distributions)
  - [8.2 Principal-series characters](#82-principal-series-characters)
  - [8.3 Discrete-series characters](#83-discrete-series-characters)
  - [8.4 Limits, singularities, and checks](#84-limits-singularities-and-checks)
- [9. Formal degrees](#9-formal-degrees)
  - [9.1 Measures and square integrability modulo the center](#91-measures-and-square-integrability-modulo-the-center)
  - [9.2 The rank-one calculation](#92-the-rank-one-calculation)
  - [9.3 Scaling rules and the limit case](#93-scaling-rules-and-the-limit-case)
- [10. Relative Lie algebra cohomology](#10-relative-lie-algebra-cohomology)
  - [10.1 The relative complex](#101-the-relative-complex)
  - [10.2 The rank-one calculation](#102-the-rank-one-calculation)
  - [10.3 Components and signs](#103-components-and-signs)
  - [10.4 Split-center conventions](#104-split-center-conventions)
- [11. Algebraic coefficients and cohomological representations](#11-algebraic-coefficients-and-cohomological-representations)
  - [11.1 Algebraic representations of GL2](#111-algebraic-representations-of-gl2)
  - [11.2 The cohomology criterion](#112-the-cohomology-criterion)
  - [11.3 Several real places](#113-several-real-places)
- [12. Parallel weight two](#12-parallel-weight-two)
  - [12.1 The local infinity type](#121-the-local-infinity-type)
  - [12.2 Holomorphic and antiholomorphic realizations](#122-holomorphic-and-antiholomorphic-realizations)
  - [12.3 Cohomology and sign decomposition](#123-cohomology-and-sign-decomposition)
  - [12.4 A normalization ledger](#124-a-normalization-ledger)
- [13. Final synthesis](#13-final-synthesis)

## 1. The archimedean problem

### 1.1 Why infinity is a local place

At a finite place, a two-dimensional automorphic representation is described by vectors fixed by compact open subgroups, induction from a Borel subgroup, and a parameter recording Frobenius and monodromy. At a real place the topology changes completely: every sufficiently small subgroup is connected, differentiation produces an action of a Lie algebra, and compact rotations carry an infinite ladder of weights. The same three questions nevertheless remain.

1. Which irreducible representations occur?
2. How can one recognize them from characters and infinitesimal data?
3. Which of them contribute to the cohomology attached to algebraic automorphic forms?

For $\mathrm{GL}_2(\mathbf R)$, these questions admit unusually explicit answers. The principal series is visible on functions on a circle. The discrete series is built from one-sided ladders of rotation weights. Its character is a quotient of two elementary trigonometric functions. Its formal degree is linear in the lowest weight. Relative Lie algebra cohomology is detected by the meeting of one compact weight from the discrete series with the extreme weight of an algebraic coefficient system.

The apparent simplicity hides a persistent danger: several equally standard normalizations coexist. One may divide out the positive center or the full center; normalize $\mathrm{SO}(2)$ or $\mathrm{O}(2)$ to have volume one; call a Weil-group character $|\cdot|^s$ using either the real or complex absolute value; and put an algebraic coefficient system or its dual into cohomology. A formula copied without its convention can be wrong by a sign, a factor of two, or a dual. We therefore make every normalization explicit and later collect them in a ledger.

The goal is not merely to name the representation of weight two. It is to make the statement

$$
\pi_v \simeq D_2
$$

an exact mathematical assertion: the central character, compact types, infinitesimal character, Weil parameter, character, formal degree, and cohomology class will all be determined.

### 1.2 Conventions that govern the book

Throughout,

$$
G=\mathrm{GL}_2(\mathbf R),\qquad G^+=\{g\in G:\det g>0\},
$$

$Z$ is the center, $K=\mathrm O(2)$, and $K^0=\mathrm{SO}(2)$. We write

$$
r(\theta)=
\begin{pmatrix}
\cos\theta&\sin\theta\\
-\sin\theta&\cos\theta
\end{pmatrix}.
$$

Thus the character $e_m$ of $K^0$ is $e_m(r(\theta))=e^{im\theta}$. This choice of the sign in $r(\theta)$ fixes which ladder is called holomorphic.

Characters of $\mathbf R^\times$ are written

$$
\chi_{\epsilon,t}(x)=\operatorname{sgn}(x)^\epsilon |x|^t,
\qquad \epsilon\in\{0,1\},\quad t\in\mathbf C.
$$

Induction from the upper triangular Borel is always normalized. For Haar measure and formal degree we first specify the measure on the identity component of $G/Z$; the effect of other normalizations is stated separately. The symbol $D_k$ will mean the irreducible representation of the full, disconnected group $G$ whose restriction to $G^+$ is the sum of the holomorphic and antiholomorphic members of weight $k$. For $k\ge2$ it is square-integrable modulo $Z$; $D_1$ is its tempered limiting analogue.

All vector spaces are complex unless a real structure is explicitly mentioned. A representation of moderate growth is understood to be continuous on a complete locally convex space, with the usual smoothness assumptions when differentiation is used. The algebraic heart of such a representation is its space of $K$-finite vectors.

## 2. The real reductive group

### 2.1 Components, center, and derived group

The determinant gives the component sequence

$$
1\longrightarrow G^+\longrightarrow G
\xrightarrow{\operatorname{sgn}\det}\{\pm1\}\longrightarrow1.
$$

The center and derived group are

$$
Z=\{xI_2:x\in\mathbf R^\times\},
\qquad G^{\mathrm{der}}=\mathrm{SL}_2(\mathbf R).
$$

Multiplication induces a surjection

$$
\mathbf R_{>0}\times \mathrm{SL}_2(\mathbf R)\longrightarrow G^+,
\qquad (a,h)\longmapsto ah,
$$

whose kernel is trivial: a positive scalar of determinant one is $1$. Hence $G^+$ is actually the direct product $\mathbf R_{>0}\times\mathrm{SL}_2(\mathbf R)$. If one uses the whole $\mathbf R^\times$ instead, the map to $G$ has kernel $\{(1,I),(-1,-I)\}$. These elementary observations explain two later facts. First, the positive central character and the representation of $\mathrm{SL}_2(\mathbf R)$ can be varied independently. Second, an element of negative determinant exchanges the holomorphic and antiholomorphic halves.

The quotient $G/Z$ is $\mathrm{PGL}_2(\mathbf R)$. It has two components, with identity component $\mathrm{PSL}_2(\mathbf R)$. Discrete series of $G$ are not square-integrable on $G$, because a unitary central character has constant modulus along the noncompact center. The correct condition is square integrability on $G/Z$.

A real matrix group is reductive when its Lie algebra is a direct sum of a semisimple algebra and an abelian center and the group has only finitely many connected components, with the adjoint action compatible with this decomposition. For $G$ this is visible without general structure theory:

$$
\mathfrak{gl}_2(\mathbf R)=\mathbf R I_2\oplus\mathfrak{sl}_2(\mathbf R).
$$

The first summand is central, the second is simple, and $G/G^+$ has order two. Reductivity rules out a normal unipotent radical. The upper triangular Borel is not reductive because its strictly upper triangular subgroup is a nontrivial connected normal unipotent group. This counterexample matters: induction uses the nonreductive Borel, but spectral finiteness belongs to the ambient reductive group.

There are three related centers one must not conflate. The group center is $\mathbf R^\times$; its identity component is $\mathbf R_{>0}$; and the Lie algebra center is the line $\mathbf R I_2$. Differentiation sees the second and third but cannot see the sign of a negative scalar. This is why parity must be recorded alongside the infinitesimal parameter.

### 2.2 Polar decomposition and maximal compact subgroups

The geometry of a real reductive group is organized by a maximal compact subgroup. For $G$ it arises from the polar decomposition.

**Polar decomposition.** Every $g\in G$ has a unique expression

$$
g=kp,\qquad k\in\mathrm O(2),\quad p=p^{\mathsf T}>0.
$$

Indeed, set $p=(g^{\mathsf T}g)^{1/2}$ and $k=gp^{-1}$. The positive square root exists and is unique by the spectral theorem. Then

$$
k^{\mathsf T}k=p^{-1}g^{\mathsf T}gp^{-1}=I.
$$

Uniqueness follows because $k^{-1}k'=pp'^{-1}$ is both orthogonal and positive definite, hence is $I$. Thus multiplication is a diffeomorphism

$$
K\times\mathcal P\longrightarrow G,
$$

where $\mathcal P$ is the cone of positive-definite symmetric matrices.

This proves more than a factorization. The cone $\mathcal P$ is contractible, so $K$ is a deformation retract of $G$. It also proves maximality. If a compact subgroup $C$ contains $K$, average the standard inner product over $C$. The resulting $C$-invariant positive form is already $K$-invariant; invariance under all rotations and one reflection forces its Gram matrix to be a positive scalar multiple of the identity. Hence every element of $C$ preserves the standard inner product and $C\subseteq K$, so $C=K$. The same averaging argument, followed by a change of orthonormal basis for the averaged form, shows that every compact subgroup is conjugate into $K$. Consequently every maximal compact subgroup of $G$ is conjugate to $\mathrm O(2)$.

The word “maximal” cannot be replaced by “maximum.” There is no preferred maximal compact before choosing a positive form: conjugating $K$ by a nonorthogonal matrix gives a different maximal compact. What is canonical is the conjugacy class. Nor is $K^0$ maximal compact in $G$, since it is properly contained in $K$. It is maximal connected compact, a distinction that later accounts for the two cohomological sign lines.

The Cartan involution is

$$
\vartheta(g)=(g^{-1})^{\mathsf T}.
$$

Its fixed points are exactly $K$. Notice that $K$ is disconnected. Replacing it by $K^0$ is sometimes convenient, but loses the operator that exchanges positive and negative rotation weights. We will keep track of both.

### 2.3 The upper half-plane and Cartan decomposition

The derived symmetric space is the upper half-plane

$$
\mathfrak H=\{x+iy:y>0\}.
$$

$\mathrm{SL}_2(\mathbf R)$ acts by fractional linear transformations, and the stabilizer of $i$ is $\mathrm{SO}(2)$. Hence

$$
\mathrm{SL}_2(\mathbf R)/\mathrm{SO}(2)\simeq\mathfrak H.
$$

For $G$, the extra positive scalar gives

$$
G/K\simeq \mathbf R_{>0}\times\mathfrak H.
$$

The Iwasawa decomposition makes this explicit. Put

$$
n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix},\qquad
a(y)=\begin{pmatrix}y^{1/2}&0\\0&y^{-1/2}\end{pmatrix}.
$$

Every element of $\mathrm{SL}_2(\mathbf R)$ has a unique expression $n(x)a(y)k$ with $y>0$ and $k\in\mathrm{SO}(2)$. The invariant measure on $\mathfrak H$ is

$$
d\mu_{\mathfrak H}(z)=\frac{dx\,dy}{y^2}.
$$

The Cartan decomposition instead uses

$$
a_t=\begin{pmatrix}e^{t/2}&0\\0&e^{-t/2}\end{pmatrix},\qquad t\ge0,
$$

and says $\mathrm{SL}_2(\mathbf R)=K^0A^+K^0$. The parameter $t$ is hyperbolic distance from $i$ to $a_ti$. Matrix coefficients of a discrete series decay exponentially in $t$; the competition between that decay and the Jacobian growth is exactly the square-integrability test.

### 2.4 Split and elliptic Cartan subgroups

Regular semisimple elements of $G$ fall into two geometrically different types. A split Cartan is

$$
A=\left\{\begin{pmatrix}a&0\\0&b\end{pmatrix}:a,b\in\mathbf R^\times\right\}.
$$

An elliptic Cartan is

$$
T=\left\{
\begin{pmatrix}x&y\\-y&x\end{pmatrix}:(x,y)\ne(0,0)
\right\}\simeq\mathbf C^\times.
$$

A regular element is split when it has two distinct real eigenvalues, and elliptic when its eigenvalues are a nonreal conjugate pair. An elliptic element has positive determinant and can be written, up to conjugacy, as $r\,r(\theta)$ with $r\in\mathbf R^\times$ and $\theta\notin\pi\mathbf Z$. A positive-determinant split element can be written as

$$
r\begin{pmatrix}e^{t/2}&0\\0&e^{-t/2}\end{pmatrix},\qquad r\in\mathbf R^\times,\quad t\ne0.
$$

Negative-determinant regular elements are necessarily split.

The existence of an elliptic Cartan modulo the center is the structural reason discrete series exist. Indeed, $T/Z$ is compact, whereas $A/Z$ is not. Here the connection is proved directly in the rotation-weight construction of Chapter 6, so no general existence criterion for discrete series is required.

The two Cartans also explain why one formula cannot be recovered from the other by real conjugacy. The matrices $a_t$ and $r(\theta)$ become conjugate only after complexification and analytic continuation. A principal series is induced from real eigenlines, so its character is naturally visible on the split regular set. A discrete series is detected on the compact Cartan as well. The elliptic formula is therefore what distinguishes a discrete constituent from the principal series containing it.

## 3. Lie algebra and infinitesimal structure

### 3.1 Cartan involution and root vectors

Let $\mathfrak g=\mathfrak{gl}_2(\mathbf R)$. Differentiating the Cartan involution gives $X\mapsto-X^{\mathsf T}$ and the decomposition

$$
\mathfrak g=\mathfrak k\oplus\mathfrak p,
$$

where $\mathfrak k=\mathfrak{so}_2(\mathbf R)$ consists of skew-symmetric matrices and $\mathfrak p$ consists of symmetric matrices. The brackets satisfy

$$
[\mathfrak k,\mathfrak k]\subseteq\mathfrak k,\qquad
[\mathfrak k,\mathfrak p]\subseteq\mathfrak p,\qquad
[\mathfrak p,\mathfrak p]\subseteq\mathfrak k.
$$

Separate the central direction $\zeta=I_2$ and use the standard basis of $\mathfrak{sl}_2$:

$$
H=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
E=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
F=\begin{pmatrix}0&0\\1&0\end{pmatrix}.
$$

Then

$$
[H,E]=2E,\qquad[H,F]=-2F,\qquad[E,F]=H.
$$

These relations are the algebraic engine of the entire representation theory. Once the eigenvalue of one compact type and the Casimir are known, they determine the coefficients along the whole ladder.

### 3.2 Compact weights and raising operators

Put $W=E-F$, so that $r(\theta)=\exp(\theta W)$. Over $\mathbf C$, define

$$
X_+=\frac12\bigl(H+i(E+F)\bigr),\qquad
X_-=\frac12\bigl(H-i(E+F)\bigr).
$$

A direct calculation gives

$$
[W,X_+]=2iX_+,\qquad [W,X_-]=-2iX_-.
$$

If $v$ has $K^0$-weight $m$, meaning $r(\theta)v=e^{im\theta}v$, then $X_+v$ has weight $m+2$ and $X_-v$ has weight $m-2$. Thus the noncentral noncompact tangent space decomposes as

$$
\mathfrak p_{0,\mathbf C}=\mathbf C X_+\oplus\mathbf C X_-,
$$

with weights $2$ and $-2$. The remaining line $\mathbf C\zeta\subset\mathfrak p_{\mathbf C}$ is central and has weight zero.

The step size two has an immediate consequence: all weights in an irreducible module have the same parity. The ladder picture can be checked in $\operatorname{Sym}^n(\mathbf C^2)$, whose weights are $n,n-2,\ldots,-n$. Both arrows eventually vanish, so the ladder is finite. In a generic principal series neither end vanishes. In a holomorphic discrete series only the lowering operator vanishes at the bottom. These finite, two-sided, and one-sided patterns anticipate the classification.

The reflection

$$
j=\begin{pmatrix}1&0\\0&-1\end{pmatrix}\in K
$$

satisfies $jr(\theta)j^{-1}=r(-\theta)$, so it exchanges weight $m$ with weight $-m$ and exchanges $X_+$ with $X_-$ up to the harmless sign fixed by the displayed basis.

### 3.3 The center of the enveloping algebra

The universal enveloping algebra of $\mathfrak{sl}_2(\mathbf C)$ has central generator

$$
\Omega=H^2+2H+4FE=H^2-2H+4EF.
$$

Centrality follows by commuting the displayed expression with $H,E,F$ and using the three bracket relations. For example, the terms in $[E,H^2+2H]$ cancel those in $4[E,FE]$; the calculation for $F$ is symmetric.

It also generates the whole center. Filter the enveloping algebra by degree. The leading symbol of a central element is an adjoint-invariant polynomial on $\mathfrak{sl}_2$. Writing a traceless matrix as

$$
\begin{pmatrix}h&e\\ f&-h\end{pmatrix}
$$

shows directly, first on the dense semisimple set and then polynomially everywhere, that every invariant polynomial is a polynomial in $h^2+ef$, equivalently in the determinant. The leading symbol of $\Omega$ is the corresponding quadratic invariant. Subtracting a polynomial in $\Omega$ cancels the leading symbol of any central element; induction on the filtration degree leaves only a scalar. Hence $Z(U(\mathfrak{sl}_2))=\mathbf C[\Omega]$.

On the irreducible finite-dimensional module of highest weight $n\ge0$, a highest-weight vector $v$ satisfies $Ev=0$ and $Hv=nv$, whence

$$
\Omega v=n(n+2)v.
$$

It is useful to shift by one:

$$
\Omega+1\quad\hbox{has eigenvalue}\quad(n+1)^2.
$$

The square makes the Weyl symmetry $\lambda\leftrightarrow-\lambda$ visible. Since

$$
U(\mathfrak{gl}_2(\mathbf C))\simeq
U(\mathfrak{sl}_2(\mathbf C))\otimes\mathbf C[\zeta],
$$

an infinitesimal character for $G$ is determined by the scalar for $\zeta$ and the Weyl orbit of a number $\lambda$, with $\Omega+1$ acting by $\lambda^2$.

## 4. From continuous representations to Harish--Chandra modules

### 4.1 Smooth and compact-finite vectors

Let $(\pi,V)$ be a continuous representation of $G$. A vector $v$ is smooth if $g\mapsto\pi(g)v$ is smooth, and is $K$-finite if the span of $\pi(K)v$ is finite-dimensional. For $K=\mathrm O(2)$, density of such vectors is an elementary Fourier statement. Restrict the orbit map to the rotations and form its Fejér sums

$$
\sigma_N(v)=\frac1{2\pi}\int_0^{2\pi}
F_N(\theta)\pi(r(\theta))v\,d\theta,
$$

where $F_N$ is the Fejér kernel. Each $\sigma_N(v)$ is a finite sum of rotation weights; adjoining its translates by the reflection $j$ makes it $K$-finite. The Fejér kernels are a positive approximate identity, so $\sigma_N(v)\to v$. Applying the same argument after any differential operator on the smooth orbit map gives convergence in the smooth topology. Thus the $K$-finite vectors are dense, with no compact-group decomposition theorem left implicit. Projection to an individual weight is the Fourier integral

$$
P_m(v)=\frac1{2\pi}\int_0^{2\pi}
e^{-im\theta}\pi(r(\theta))v\,d\theta;
$$

the pair $P_m(v),P_{-m}(v)$ is stable under $K$.

Differentiation makes the space $V_K$ of $K$-finite smooth vectors a module for $U(\mathfrak g_\mathbf C)$. The compatibility

$$
k(Xv)=(\operatorname{Ad}(k)X)(kv)
$$

turns it into a $(\mathfrak g,K)$-module. This small algebraic object retains the compact-type decomposition and all infinitesimal operators while discarding analytic completion. For $G$ it can be pictured as a collection of finite-dimensional weight spaces connected by the two arrows $X_+$ and $X_-$.

### 4.2 Admissibility and finite generation

A $(\mathfrak g,K)$-module $M$ is **admissible** if every irreducible $K$-type occurs with finite multiplicity. It is a **Harish--Chandra module** if it is admissible and finitely generated over $U(\mathfrak g_\mathbf C)$.

Both conditions matter. Finite generation alone permits an infinite-dimensional multiplicity at one compact type; admissibility alone permits unrelated ladders with no finite set of generators. Together they imply strong finiteness. An irreducible Harish--Chandra module has an infinitesimal character for an elementary reason. A central element preserves each finite-dimensional $K$-isotypic space, so it has an eigenvector there. The kernel of the corresponding scalar difference is nonzero and stable under both $\mathfrak g$ and $K$; irreducibility makes it the whole module. Thus every central element acts by a scalar. More generally, on a finite-length module a product of the scalar differences from its composition factors annihilates the module, so the center acts locally finitely and the module decomposes into generalized infinitesimal-character summands.

For $\mathrm{GL}_2(\mathbf R)$ the multiplicities in an irreducible principal or discrete series are at most one after restriction to $K^0$. This is not part of the definition; it is a rank-one consequence of the compact picture and the ladder relations.

The hypotheses should not be weakened casually. The Hilbert direct sum of countably many trivial representations is smooth but not admissible, because the trivial $K$-type has infinite multiplicity. An algebraic direct sum of infinitely many modules with unrelated infinitesimal characters cannot be finitely generated. Neither object has the finite-length behavior required here. By contrast, every principal series below is generated by one or two compact types, and every rotation weight occurs with multiplicity at most one.

For the fixed-infinitesimal-character modules used below, finite length is concrete rather than an additional assumption. Choose finitely many generators and follow their ladders. The Casimir relation makes each product of successive raising and lowering arrows a fixed quadratic polynomial in the compact weight, so only finitely many breaks occur. Away from those breaks a nonzero weight generates the whole intervening string. The finitely many resulting two-sided, one-sided, and finite strings therefore give a finite composition series. This argument applies in particular to every principal series and every subquotient constructed in Chapters 5 and 6; no general finite-length theorem is being used implicitly.

### 4.3 Infinitesimal and central characters

The **central character** is a character $\omega_\pi:Z\to\mathbf C^\times$ through which the group center acts. The **infinitesimal character** describes the action of the center of $U(\mathfrak g_\mathbf C)$. They are related but not identical. The derivative of $\omega_\pi$ on $Z^0$ gives the scalar for $\zeta$, while the value at $-I$ is invisible to differentiation.

For example, $1$ and $\operatorname{sgn}\det$ have the same infinitesimal character and different behavior on the disconnected group. Conversely, two representations with the same group central character can have different Casimir eigenvalues. This distinction becomes decisive when algebraic coefficients cancel the positive central character in cohomology.

The trivial representation and $D_2$ give a sharper warning. They have the same infinitesimal character, the same trivial central character, and both occur at the endpoint of the spherical principal series. Yet the trivial representation has only compact weight zero, whereas $D_2$ begins at weights $\pm2$. Infinitesimal and central characters narrow the possibilities but do not classify them; the compact-type pattern completes the diagnosis.

### 4.4 Irreducibility and globalization

For the representations in this book, algebraic irreducibility is proved from the explicit ladder and then implies topological irreducibility of the realization. Indeed, let $V_K$ be irreducible and let $W\subset V$ be a nonzero closed $G$-invariant subspace. Smoothing a nonzero vector of $W$ by a compactly supported function on $G$, and then applying a nonzero compact Fourier projection, produces a vector in $W\cap V_K$. That intersection is a nonzero $(\mathfrak g,K)$-submodule, hence equals $V_K$. Since the compact-finite vectors are dense, $W=V$.

The reverse implication for an arbitrary completion is subtler and is not needed here. Every algebraic module below is realized explicitly either in a principal-series compact picture or in the holomorphic Hilbert space of Section 6.1, and its ladder is checked inside that realization. Thus no general completion theorem is hidden in the later irreducibility arguments.

## 5. Principal series in rank one

### 5.1 Normalized induction

Let $B=TN$ be the upper triangular Borel, with diagonal torus $T$ and unipotent radical $N$. Its modular character is

$$
\delta_B\left(\begin{pmatrix}a&*\\0&d\end{pmatrix}\right)
=\left|\frac ad\right|.
$$

For characters $\chi_1,\chi_2$ of $\mathbf R^\times$, the normalized principal series

$$
I(\chi_1,\chi_2)=
\operatorname{Ind}_B^G(\chi_1\boxtimes\chi_2)
$$

consists of smooth functions $f:G\to\mathbf C$ satisfying

$$
f\left(\begin{pmatrix}a&x\\0&d\end{pmatrix}g\right)
=\left|\frac ad\right|^{1/2}\chi_1(a)\chi_2(d)f(g),
$$

with $G$ acting by right translation. The factor $\delta_B^{1/2}$ is not decoration. It makes unitary induction unitary when $\chi_1$ and $\chi_2$ are unitary, makes the Weyl symmetry exchange the two characters without an additional shift, and centers the infinitesimal parameter at zero.

The central character is immediately

$$
\omega_I(x)=\chi_1(x)\chi_2(x).
$$

Twisting commutes with induction:

$$
I(\chi_1,\chi_2)\otimes(\eta\circ\det)
\simeq I(\chi_1\eta,\chi_2\eta).
$$

Thus the ratio $\chi_1\chi_2^{-1}$ controls reducibility and the product controls the center.

### 5.2 The compact picture and compact types

Iwasawa decomposition gives $G=BK$, so a function in the induced representation is determined by its restriction to $K$. On $B\cap K=\{\pm I,\pm j\}$ the transformation rule records only parity. If

$$
\chi_i=\chi_{\epsilon_i,t_i},
$$

then the restriction to $K^0$ has precisely the weights

$$
m\equiv \epsilon_1+\epsilon_2\pmod2,
$$

each with multiplicity one. On the full $K$, the two weights $m$ and $-m$ join into a two-dimensional irreducible type when $m>0$; weight zero has two possible extensions distinguished by reflection.

This proves admissibility directly. It also explains why changing the continuous exponents $t_i$ does not change the compact types: all principal series with fixed parity live on the same compact model, while the noncompact Lie algebra operators depend on the exponents.

Choose a weight vector $v_m$. With a consistent scaling of these vectors, the ladder action has the form

$$
X_+v_m=\frac12(\nu+1+m)v_{m+2},
\qquad
X_-v_m=\frac12(\nu+1-m)v_{m-2},
$$

where $\nu=t_1-t_2$ after moving any sign in the ratio into the parity condition. The precise placement of harmless factors of $i$ depends on the chosen $X_\pm$ and basis vectors, but the zeros do not. A ladder breaks exactly when $m=\nu+1$ or $m=-\nu-1$ is an allowed compact weight.

The coefficients come directly from the induced transformation law, rather than from a classification theorem. Represent $v_m$ in the compact picture by $e^{im\theta}$. Factoring $r(\theta)\exp(tH)$ and $r(\theta)\exp(t(E+F))$ into an upper triangular matrix times a rotation and retaining the terms linear in $t$ gives

$$
\begin{aligned}
d\pi(H)f&=(\nu+1)\cos(2\theta)f+\sin(2\theta)f',\\
d\pi(E+F)f&=(\nu+1)\sin(2\theta)f-\cos(2\theta)f'.
\end{aligned}
$$

Combining these formulas according to

$$
X_\pm=\frac12(H\pm i(E+F))
$$

gives respectively $(\nu+1+m)/2$ and $(\nu+1-m)/2$. Rescaling all $v_m$ by the same nonzero parity-dependent constant changes neither formula. This calculation also shows that there are no unrecorded arrows between compact weights.

The irreducible representations of $K$ make the passage from weights to full compact types explicit. Besides the two one-dimensional characters $1$ and $\det$, there is for every $m\ge1$ a two-dimensional representation $\tau_m$ whose restriction to $K^0$ is

$$
e_m\oplus e_{-m}.
$$

Reflection exchanges the two lines. Thus a full-group principal series contains one $\tau_m$ for every positive $m$ of the required parity, together in the even case with one possible one-dimensional type at weight zero. The full-group discrete series $D_k$ contains $\tau_k,\tau_{k+2},\ldots$. This formulation prevents the misleading statement that $D_k$ has two minimal $K$-types: it has two minimal $K^0$-weights but one irreducible minimal $K$-type $\tau_k$.

The compact picture also proves finite generation. At a generic parameter, one nonzero weight vector and its reflection generate every allowed weight by repeated raising and lowering. At a reducibility point, a vector just outside a break generates a half-ladder, while the finitely many middle weights generate the finite constituent. No analytic convergence is needed for this algebraic statement.

### 5.3 Intertwining and reducibility

For parameters in a convergence half-plane, define the standard intertwining operator

$$
(M f)(g)=\int_{\mathbf R}f\left(
\begin{pmatrix}0&-1\\1&0\end{pmatrix}
\begin{pmatrix}1&x\\0&1\end{pmatrix}g\right)\,dx.
$$

It maps $I(\chi_1,\chi_2)$ to $I(\chi_2,\chi_1)$. Its continuation on the compact-finite module is elementary in rank one. On the weight-zero or weight-one type from which the ladder starts, the integral is a beta integral and hence a quotient of gamma functions, meromorphic in $t_1-t_2$. If $c_m(\nu)=\frac12(\nu+1+m)$ is the raising coefficient, the intertwining identity gives

$$
c_m(\nu)a_{m+2}(\nu)=a_m(\nu)c_m(-\nu)
$$

for its weight scalars $a_m(\nu)$. This recurrence continues every scalar meromorphically, and the lowering relation gives the same continuation in the other direction. Its zeros and poles occur exactly where a raising or lowering coefficient vanishes. Therefore the same exceptional parameters are detected both algebraically and analytically.

For the integral parameters needed here, set

$$
I_k=I\left(\operatorname{sgn}^{k}|\cdot|^{(k-1)/2},
|\cdot|^{-(k-1)/2}\right),\qquad k\ge2.
$$

The ratio of the inducing characters is

$$
\operatorname{sgn}^{k}|\cdot|^{k-1}.
$$

The compact weights have parity $k$, and the ladder breaks at $\pm k$. As a module for $\mathrm{SL}_2(\mathbf R)$, the weights between the breaks,

$$
-(k-2),-(k-4),\ldots,k-4,k-2,
$$

form the irreducible algebraic representation

$$
F_{k-2}=\operatorname{Sym}^{k-2}(\mathbf C^2).
$$

The action of the full center needs one further normalization. Define

$$
L_{k-2}=\operatorname{Sym}^{k-2}(\mathbf C^2)
\otimes|\det|^{-(k-2)/2}.
$$

On $xI$, this module acts by $\operatorname{sgn}(x)^{k-2}=\operatorname{sgn}(x)^k$, exactly the central character of $I_k$. Thus $L_{k-2}$ is finite-dimensional and has the same restriction to $\mathrm{SL}_2(\mathbf R)$ as $F_{k-2}$, but need not be algebraic as a representation of $G$. The two outer half-ladders form the discrete-series submodule. Consequently there is an exact sequence

$$
0\longrightarrow D_k\longrightarrow I_k
\longrightarrow L_{k-2}\longrightarrow0.
$$

For the reverse ordering of the inducing characters the arrows reverse:

$$
0\longrightarrow L_{k-2}\longrightarrow
I\left(|\cdot|^{-(k-1)/2},
\operatorname{sgn}^{k}|\cdot|^{(k-1)/2}\right)
\longrightarrow D_k\longrightarrow0.
$$

These sequences prove reducibility and identify every constituent; no dimension count is hidden. They also give a robust check on character formulas, because distribution characters are additive in short exact sequences.

The first two cases make the normalization concrete. For $k=2$,

$$
I_2=I(|\cdot|^{1/2},|\cdot|^{-1/2})
$$

is spherical. Its quotient $L_0$ is the trivial representation and its submodule is $D_2$. Thus weight two sits exactly at the endpoint of the spherical complementary series. For $k=3$,

$$
I_3=I(\operatorname{sgn}|\cdot|,|\cdot|^{-1}),
$$

and the finite quotient is

$$
L_1=\mathbf C^2\otimes|\det|^{-1/2}.
$$

It has rotation weights $1,-1$ and central character $\operatorname{sgn}$. The discrete submodule begins at $\pm3$. These examples show why the absolute-value twist in $L_{k-2}$ cannot be omitted.

More generally, normalized principal induction is reducible precisely when, after possibly exchanging the two inducing characters,

$$
\chi_1\chi_2^{-1}
=\operatorname{sgn}^{n+1}|\cdot|^n
$$

for an integer $n\ge1$. The case $n=k-1$ is the sequence above. The boundary ratio $\operatorname{sgn}$ behaves differently: on the identity component it splits into two limit-of-discrete-series modules, while on the full group the negative component exchanges them.

To see why no other reducibility occurs, suppose a nonzero proper submodule exists and choose one of its compact weights. Moving along the ladder remains possible until a coefficient vanishes; otherwise the submodule contains every compact type and equals the whole principal series. A zero forces $\nu+1$ to be an allowed integer weight. Matching the parity with the sign character gives precisely $\operatorname{sgn}^{n+1}|\cdot|^n$. Conversely, at every such parameter the displayed broken ladders produce a proper submodule. This proves both necessity and sufficiency.

### 5.4 Unitary, complementary, and finite-dimensional cases

If $\chi_1$ and $\chi_2$ are unitary, normalized induction carries the invariant norm

$$
\|f\|^2=\int_K|f(k)|^2\,dk
$$

and is called unitary principal series. There is also a complementary series. Up to a unitary twist it has the form

$$
I(|\cdot|^u,|\cdot|^{-u}),\qquad 0<|u|<\frac12.
$$

Its invariant positive form is obtained by composing the standard pairing with the normalized intertwining operator. Write $\nu=2u$ and normalize the scalar on weight zero to be positive. The recurrence above gives, for nonnegative even $m$,

$$
\frac{a_{m+2}(\nu)}{a_m(\nu)}
=\frac{m+1-\nu}{m+1+\nu}.
$$

The ratios in both directions are positive exactly when $|\nu|<1$, which is the displayed interval. At $|u|=1/2$ the first ratio vanishes; the invariant form becomes semidefinite and separates the trivial constituent from $D_2$. Beyond the endpoint a ratio is negative. On an irreducible spherical principal series, an invariant Hermitian form gives an intertwiner to the Hermitian dual, and the multiplicity-one compact ladder makes that intertwiner unique up to scalar. Hence the sign change rules out every other positive invariant form, not merely the one initially constructed.

Finite-dimensional irreducible continuous representations are, up to isomorphism,

$$
\operatorname{Sym}^n(\mathbf C^2)\otimes|\det|^u
\otimes(\operatorname{sgn}\det)^\epsilon,
\qquad n\ge0,\quad u\in\mathbf C,
\quad\epsilon\in\{0,1\}.
$$

This list follows from the ladder relations. In a finite-dimensional irreducible $\mathfrak{sl}_2$-module, choose an $H$-eigenvector at the top of an $E$-string. If its eigenvalue is $\lambda$, then

$$
E F^r v=r(\lambda-r+1)F^{r-1}v.
$$

The identity follows by induction from $[E,F]=H$. If $F^{n+1}v=0$ with $F^nv\ne0$, applying $E$ forces $\lambda=n\in\mathbf Z_{\ge0}$. The vectors $v,Fv,\ldots,F^nv$ form the unique irreducible string of dimension $n+1$, namely $\operatorname{Sym}^n(\mathbf C^2)$. Irreducibility rules out any further string. The central Lie-algebra line then acts by a scalar, which is supplied by a unique twist $|\det|^u$ after the scalar action already present on $\operatorname{Sym}^n$ is removed. Finally the other component can act in two ways, differing by $\operatorname{sgn}\det$. This proves the displayed classification.

The symmetric power fixes the derived-group action, the absolute-value twist fixes the positive-center derivative, and the sign twist fixes the action of the other component. Algebraic representations form the integral subfamily described in Section 11.1. Except for unitary characters, finite-dimensional representations are not unitary. They occur at the same integral semisimple infinitesimal characters as discrete series, but on the opposite side of a reducible principal-series exact sequence. This is the first indication that an infinitesimal character alone does not identify a representation.

The complementary interval is genuinely open. At $u=0$ one is in the unitary principal series. At $u=1/2$ the invariant form becomes semidefinite and separates the trivial quotient from $D_2$. There is no complementary representation with $u>1/2$: the compact-type eigenvalues of the intertwiner eventually have opposite signs. This supplies a useful counterexample to the naive idea that a real induction parameter always gives a unitarizable representation.

Up to unitary character twist, the irreducible unitary representations in the range needed here are therefore easy to locate. The unitary principal series lies on the imaginary induction axis; the complementary series occupies the open real segment between the two first reducibility points; $D_k$ for $k\ge2$ is discrete; $D_1$ is the tempered endpoint; and unitary characters are the one-dimensional cases. The proof is constructive: the compact-picture norm handles the imaginary axis, the positive intertwiner handles the complementary segment, the holomorphic norm handles the discrete ladders, and the sign change of an intertwiner eigenvalue excludes the remaining real parameters. This is enough for the archimedean components of weight-two cuspidal representations without asserting a classification of all possible nonunitary completions.

## 6. Discrete and limit-of-discrete series

### 6.1 Lowest- and highest-weight modules

Fix $k\ge1$. A lowest-weight module $D_k^+$ is generated by a vector $v_k$ satisfying

$$
r(\theta)v_k=e^{ik\theta}v_k,\qquad X_-v_k=0,
$$

and has compact weights

$$
k,k+2,k+4,\ldots.
$$

Similarly, a highest-weight module $D_k^-$ is generated by $v_{-k}$ with $X_+v_{-k}=0$ and has weights

$$
-k,-k-2,-k-4,\ldots.
$$

The bracket relations determine the action up to rescaling the weight vectors. To prove irreducibility, take a nonzero vector in a submodule and decompose it into compact weights. Repeatedly applying the operator that moves toward the endpoint reaches the nonzero extreme vector; applying the other operator then generates the whole ladder. For $k\ge2$ these modules admit invariant positive-definite forms and are the holomorphic and antiholomorphic discrete series of $G^+$ after the positive center is specified. For $k=1$ the same construction gives the two limits of discrete series.

The adjectives “holomorphic” and “antiholomorphic” come from the upper half-plane. In a holomorphic realization, $D_k^+$ acts on holomorphic functions with norm

$$
\|f\|_k^2=\int_{\mathfrak H}|f(z)|^2y^{k-2}\,dx\,dy,\qquad k>1,
$$

by

$$
(\pi_k(g)f)(z)=\det(g)^{k/2}(cz+d)^{-k}f(gz)
$$

on the positive-determinant group, with the scalar factor interpreted so that positive scalars act trivially in the untwisted representation. A Cayley transform to the unit disk identifies the lowest vector with the constant function and successive weights with monomials. At $k=1$ the integral norm reaches its logarithmic boundary, which is why the limiting module is tempered but not square-integrable.

The invariance of the norm is worth checking. For $g=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)$ with positive determinant,

$$
\operatorname{Im}(gz)=\frac{\det(g)\operatorname{Im}z}{|cz+d|^2},
\qquad
dx'\,dy'=\frac{\det(g)^2}{|cz+d|^4}\,dx\,dy.
$$

The two powers contributed by the transformed function, the factor $y^{k-2}$, and the Jacobian cancel exactly. This explains both the exponent $k$ in the automorphy factor and the exponent $k-2$ in the measure. For $k>1$ the constant vector in the disk model has finite norm; for $k=1$ its radial integral is proportional to $\int_0^1(1-\rho^2)^{-1}\rho\,d\rho$ and diverges.

### 6.2 Passage from the identity component to GL2

Conjugation by $j=\operatorname{diag}(1,-1)$ sends $r(\theta)$ to $r(-\theta)$ and therefore sends $D_k^+$ to $D_k^-$. The two are inequivalent representations of $G^+$: one has a lowest compact weight, the other a highest compact weight. Induction across the index-two subgroup gives

$$
D_k=\operatorname{Ind}_{G^+}^{G}D_k^+.
$$

Its restriction is

$$
D_k|_{G^+}\simeq D_k^+\oplus D_k^-.
$$

This induced representation is irreducible. Indeed, any nonzero $G$-stable subspace restricts to a sum of some irreducible $G^+$-summands, but $j$ exchanges the two, so the only possibilities are zero and the whole space.

There appears to be a choice in how $j$ acts, and twisting by $\operatorname{sgn}\det$ changes its sign. The two representations are nevertheless isomorphic: multiply one $G^+$ summand by $1$ and the other by $-1$. Thus $D_k\otimes\operatorname{sgn}\det\simeq D_k$. Its central character is

$$
\omega_{D_k}(x)=\operatorname{sgn}(x)^k.
$$

The value at $-1$ follows because $-I=r(\pi)$ acts by $(-1)^k$ on every compact weight.

### 6.3 The reducible principal series and the modules D-k

For $k\ge2$, the exact sequence of the preceding chapter gives a second construction of $D_k$. Its $K^0$-types are

$$
\ldots,-k-4,-k-2,-k
\quad\text{and}\quad
k,k+2,k+4,\ldots,
$$

each once. There are no weights strictly between $-k$ and $k$. This missing band is a convenient diagnostic: a representation with infinitesimal character $k-1$ and parity $k$ is discrete series precisely when the middle finite string has been removed in this way.

At $k=1$ define

$$
D_1=I(\operatorname{sgn},1).
$$

On $G^+$ it is the direct sum $D_1^+\oplus D_1^-$, with weights $1,3,5,\ldots$ and $-1,-3,-5,\ldots$. On the full group it is irreducible for the same exchange argument. It has no missing finite-dimensional quotient because there is no algebraic representation of highest weight $-1$. This is the cleanest way to see why a limit of discrete series is a boundary object rather than an ordinary discrete series with a degenerate finite-dimensional companion.

### 6.4 Square integrability and its boundary

A unitary representation with central character is discrete series for $G$ if one, hence every, nonzero $K$-finite matrix coefficient is square-integrable on $G/Z$. For $D_k^+$ the lowest-weight coefficient in Cartan coordinates is, up to a phase,

$$
\left(\cosh\frac t2\right)^{-k}.
$$

The Cartan Jacobian grows like $\sinh t$. Thus the square of the coefficient times the Jacobian behaves for large $t$ like

$$
e^{-kt}e^t=e^{-(k-1)t}.
$$

The integral converges exactly when $k>1$. This proves square integrability for $k\ge2$ and failure for $k=1$. At $k=1$ the decay is exactly the square root of the volume growth; the representation remains tempered because its coefficients have the borderline decay allowed by temperedness.

This calculation also shows why $D_2$ is the smallest genuine discrete series. Its lowest compact weight is two, its Harish--Chandra parameter is one, and its matrix coefficients have just enough extra decay to be integrable after squaring.

### 6.5 Classification in the required range

The ladder method gives the relevant classification without invoking the general classification of real reductive groups.

**Rank-one classification.** Let $M$ be an irreducible admissible $(\mathfrak g,K)$-module with a central and infinitesimal character. Then, after a character twist, one of the following occurs:

- the compact weights extend infinitely in both directions, and $M$ is an irreducible principal-series constituent;
- the weights form a finite string, and $M$ is finite-dimensional;
- the weights form one positive and one negative half-ladder exchanged by the negative component, and $M=D_k$ for some $k\ge2$;
- the same statement holds at the boundary $k=1$, giving $D_1$.

To prove the assertion, first note that every compact weight has multiplicity at most one. Choose a nonzero vector $v$ of one weight. By the PBW ordering and the relations among $W,X_+,X_-$, every word that starts and ends at this weight reduces to a polynomial in $W$ and the Casimir. Both act by scalars on $v$, so the cyclic module generated by $v$ has at most one dimension in each weight. Irreducibility makes this cyclic module all of $M$.

The Casimir identity now expresses the product of a raising and a lowering coefficient as a quadratic polynomial in the weight. Unless this polynomial vanishes, the ladder continues, and the polynomial has at most two zeros. No zero gives a two-sided principal ladder; two inward-facing zeros enclose a finite-dimensional string; two outward-facing zeros leave the discrete half-ladders; a zero at the boundary parameter gives the limit. The explicit coefficients of Section 5.2 identify the two-sided pattern with a principal-series constituent having the same parity, central derivative, and Casimir scalar. Irreducibility prevents a mixture of patterns. The full group then joins opposite half-ladders through reflection. This proves existence and exhaustiveness, rather than merely listing the possible diagrams.

One-dimensional characters are included among the finite-dimensional cases. Complementary series and unitary principal series have the first ladder pattern. The classification deliberately says nothing about arbitrary nonadmissible continuous representations: compact multiplicities and finite generation are essential hypotheses.

Temperedness cuts across the list in a revealing way. Unitary principal series and $D_k$ are tempered; $D_1$ is tempered at the boundary; complementary series are unitary but not tempered; nontrivial finite-dimensional representations are not tempered. Square integrability is stronger: among these, only $D_k$ with $k\ge2$ is square-integrable modulo the center. Thus “unitary,” “tempered,” and “discrete” are three different conditions, not interchangeable labels.

## 7. Parameters and exact normalizations

### 7.1 The family D-k-s

For $k\ge1$ and $s\in\mathbf C$, define

$$
D_{k,s}=D_k\otimes|\det|^s.
$$

This two-parameter notation separates the compact weight $k$ from the positive central exponent. On a scalar $xI$,

$$
|\det(xI)|^s=|x|^{2s},
$$

so

$$
\omega_{k,s}(x)=\operatorname{sgn}(x)^k|x|^{2s}.
$$

The differential of the central element $\zeta=I_2$ is $2s$. This factor two is a frequent source of mistakes: the path $e^tI$ has determinant $e^{2t}$.

$D_{k,s}$ is unitary precisely when $s$ is purely imaginary. It is essentially unitary for arbitrary real part, and essentially square-integrable for $k\ge2$. The limit $D_{1,s}$ is essentially tempered when the real part of $s$ is removed by twisting.

Two twists illustrate what $s$ does and does not change. $D_{k,s}$ and $D_{k,0}$ have exactly the same compact types, because $|\det k_0|=1$ for $k_0\in K$. Their matrix coefficients differ by a scalar character along the split center, and their central derivatives differ by $2s$. By contrast, changing $k$ changes the lowest compact type, Casimir eigenvalue, elliptic character, formal degree, and algebraic coefficient system. The variables $k$ and $s$ measure independent features.

### 7.2 Infinitesimal character and contragredient

On $D_k$, the Casimir acts by

$$
k(k-2)=(k-1)^2-1.
$$

One proof uses the broken principal-series ladder: $D_k$ and $L_{k-2}$ are constituents of the same principal series and hence have the same infinitesimal character. Their $\mathfrak{sl}_2$ actions have the infinitesimal character of $F_{k-2}$, and Section 3.3 gives the Casimir scalar $(k-2)k$. Therefore $D_{k,s}$ has infinitesimal character

$$
(2s,\{\pm(k-1)\}),
$$

meaning that $\zeta$ acts by $2s$ and $\Omega+1$ acts by $(k-1)^2$.

The full-group representation $D_k$ is self-contragredient: duality exchanges the positive and negative half-ladders, which already occur together. Hence

$$
D_{k,s}^\vee\simeq D_{k,-s}.
$$

For real $s$, the Hermitian dual has the same formula. Twisting by $\operatorname{sgn}\det$ changes nothing up to isomorphism, whereas twisting by $|\det|^s$ changes both the positive central character and the infinitesimal character.

The finite constituent clarifies the Weyl orbit. $L_{k-2}$ has a highest $\mathfrak{sl}_2$ weight $k-2$, whose shifted value is $k-1$. $D_k$ has no highest weight as a full-group module, but it belongs to the same principal series and so has the same central action of the enveloping algebra. The two possible parameters $k-1$ and $1-k$ are exchanged by the Weyl group and describe one infinitesimal character. Forgetting this quotient would incorrectly distinguish a representation from its contragredient.

### 7.3 Weil parameters

Let

$$
W_{\mathbf R}=\mathbf C^\times\sqcup j\mathbf C^\times,
\qquad j^2=-1,\qquad jzj^{-1}=\bar z.
$$

Use the Weil absolute value

$$
|z|_W=z\bar z\quad(z\in\mathbf C^\times),
\qquad |j|_W=1.
$$

Put $m=k-1$ and $u(z)=z/|z|$ with $|z|=(z\bar z)^{1/2}$. The parameter of $D_{k,s}$ is

$$
\phi_{k,s}(z)=|z|_W^s
\begin{pmatrix}u(z)^m&0\\0&u(z)^{-m}\end{pmatrix},
$$

and one may take

$$
\phi_{k,s}(j)=
\begin{pmatrix}0&(-1)^m\\1&0\end{pmatrix}.
$$

The relation $\phi(j)^2=\phi(-1)$ and conjugation relation are immediate. For $m>0$ this is the irreducible induction

$$
\operatorname{Ind}_{W_{\mathbf C}}^{W_{\mathbf R}}
\left(u^m|\cdot|_W^s\right).
$$

At $m=0$ it is reducible as a Weil representation; this reflects the fact that the limit $D_1$ lies at a principal-series boundary rather than in the genuine discrete series.

The reciprocity convention can be stated without ambiguity on the abelianization of $W_{\mathbf R}$. The image of $z\in\mathbf C^\times$ corresponds to $z\bar z\in\mathbf R_{>0}$, and the image of $j$ corresponds to $-1$. Indeed, the commutator relation kills $z/\bar z$, leaving the norm of $z$, while $j$ supplies the remaining element of order two. Thus $|\cdot|^t$ pulls back to $|\cdot|_W^t$, and $\operatorname{sgn}$ pulls back to the character trivial on $\mathbf C^\times$ and equal to $-1$ on $j$.

The determinant is $|\cdot|_W^{2s}$ on $\mathbf C^\times$ and takes the value $(-1)^{m+1}=(-1)^k$ on $j$. Under this reciprocity convention it therefore corresponds to

$$
\operatorname{sgn}^k|\cdot|^{2s},
$$

exactly the central character computed directly. This determinant check fixes both the parity and the factor of two. In particular,

$$
\phi_{2,0}=\operatorname{Ind}_{W_{\mathbf C}}^{W_{\mathbf R}}(z/|z|)
$$

has determinant equal to the trivial character of $\mathbf R^\times$.

The parameter also fixes the archimedean local factor. Define

$$
\Gamma_{\mathbf C}(z)=2(2\pi)^{-z}\Gamma(z).
$$

With the Weil absolute value used above,

$$
L(z,D_{k,s})=
\Gamma_{\mathbf C}\left(z+s+\frac{k-1}{2}\right).
$$

For the additive character $x\mapsto e^{2\pi i x}$ and $s=0$, the epsilon sign at the central point is $i^k$. Here is the rank-one calculation behind both assertions. Give the angular variable mass one and take multiplicative radial measure $2\,dr/r$. Pair $u^m|\cdot|_W^s$ with the Schwartz function $2\bar w^m e^{-2\pi w\bar w}$. The angular factors cancel, and the radial Mellin integral is, after $y=2\pi r^2$,

$$
2(2\pi)^{-(z+s+m/2)}\Gamma(z+s+m/2).
$$

This is $\Gamma_{\mathbf C}(z+s+m/2)$, and induction from $W_{\mathbf C}$ preserves this local factor. The Fourier transform of the angular harmonic of degree $m$ contributes $i^m$, while the passage from the complex character to its two-dimensional real induction contributes the remaining $i$; hence the epsilon factor is $i^{m+1}=i^k$. At weight two the local factor is $\Gamma_{\mathbf C}(z+1/2)$ in the unitary normalization. Twisting by $|\det|^t$ replaces its argument by $z+t$; it does not alter the compact weights.

## 8. Explicit characters

### 8.1 Characters as invariant distributions

An infinite-dimensional representation rarely assigns a trace to an individual group element: $\pi(g)$ need not be trace class. The correct character is the distribution

$$
\Theta_\pi(f)=\operatorname{tr}\pi(f),
\qquad
\pi(f)=\int_G f(g)\pi(g)\,dg,
$$

for compactly supported smooth $f$. For the admissible finite-length representations in this book, $\pi(f)$ is trace class and $\Theta_\pi$ is conjugation invariant. To see trace class directly, average $f$ on the left and right against compact characters. Repeated integration by parts in the two compact variables makes these Fourier coefficients decay faster than every power of the two compact weights. The compact multiplicities here are at most one, while the ladder operators grow only polynomially; the resulting diagonal trace norm is therefore summable. Conjugating $f$ conjugates $\pi(f)$, proving invariance. The fixed-point calculations below then give a real-analytic representative on each regular semisimple Cartan.

Three rules determine all formulas needed below. Characters are additive in short exact sequences. Twisting multiplies the character pointwise. Finally, the character of normalized induction is computed by the fixed points of an element on $G/B$. The last rule has a simple rank-one interpretation. The flag variety $G/B$ is the real projective line. A regular split element fixes its two eigenlines, producing two terms. An elliptic element has no real eigenline, producing zero. The Jacobian at a fixed line supplies the Weyl denominator.

Additivity deserves emphasis because the reducible principal representation is not a Hilbert direct sum of its two constituents. The exact sequence need not split, yet trace is additive for the corresponding triangular operator $\pi(f)$. This is precisely why subtracting the finite character computes the discrete character even though there is no invariant complementary subspace in the induced model.

### 8.2 Principal-series characters

Let $g$ be regular split with eigenvalues $a,d\in\mathbf R^\times$, $a\ne d$. Put

$$
\Delta(g)=\frac{|a-d|}{|ad|^{1/2}}.
$$

The character of normalized induction is

$$
\Theta_{I(\chi_1,\chi_2)}(g)
=\frac{\chi_1(a)\chi_2(d)+\chi_1(d)\chi_2(a)}{\Delta(g)}.
$$

On regular elliptic elements it is zero. To justify the denominator, choose a coordinate $u$ near one eigenline in $\mathbf P^1(\mathbf R)$. The derivative of the projective action is $q=d/a$ there, so the fixed-point Jacobian contributes $|1-q|^{-1}$. Normalized induction acts on the corresponding half-density by the factor $|q|^{1/2}$. Their product is

$$
\frac{|d/a|^{1/2}}{|1-d/a|}
=\frac{|ad|^{1/2}}{|a-d|}=\Delta(g)^{-1}.
$$

The inducing character on the fiber supplies $\chi_1(a)\chi_2(d)$, and the other eigenline gives the second term.

For the special principal series $I_k$ and

$$
g=r\begin{pmatrix}e^{t/2}&0\\0&e^{-t/2}\end{pmatrix},
\qquad r\ne0,\quad t\ne0,
$$

this becomes

$$
\Theta_{I_k}(g)
=\operatorname{sgn}(r)^k
\frac{e^{(k-1)t/2}+e^{-(k-1)t/2}}
{|e^{t/2}-e^{-t/2}|}.
$$

The formula is symmetric in $t$, as conjugacy requires.

### 8.3 Discrete-series characters

We first compute on the identity component. Formally summing the compact weights of the lowest-weight module gives, for $0<\theta<\pi$,

$$
\sum_{j\ge0}e^{i(k+2j)\theta}
=-\frac{e^{i(k-1)\theta}}{e^{i\theta}-e^{-i\theta}},
$$

where the equality is understood by analytic continuation from a damped sum. Likewise,

$$
\sum_{j\ge0}e^{-i(k+2j)\theta}
=\frac{e^{-i(k-1)\theta}}{e^{i\theta}-e^{-i\theta}}.
$$

These are the regular elliptic characters of $D_k^+$ and $D_k^-$. Adding them gives the full-group character on the positive component:

$$
\Theta_{D_k}(r\,r(\theta))
=-\operatorname{sgn}(r)^k
\frac{\sin((k-1)\theta)}{\sin\theta},
\qquad \theta\notin\pi\mathbf Z.
$$

For the split formula, use the exact sequence $0\to D_k\to I_k\to L_{k-2}\to0$. The finite-dimensional character is the elementary geometric sum

$$
\Theta_{L_{k-2}}\left(
r\begin{pmatrix}e^{t/2}&0\\0&e^{-t/2}\end{pmatrix}
\right)
=\operatorname{sgn}(r)^k
\frac{e^{(k-1)|t|/2}-e^{-(k-1)|t|/2}}
{|e^{t/2}-e^{-t/2}|}.
$$

Subtracting it from the principal-series formula yields

$$
\Theta_{D_k}\left(r
\begin{pmatrix}e^{t/2}&0\\0&e^{-t/2}\end{pmatrix}\right)
=2\operatorname{sgn}(r)^k
\frac{e^{-(k-1)|t|/2}}
{|e^{t/2}-e^{-t/2}|}.
$$

If $\det g<0$, then $\Theta_{D_k}(g)=0$. This follows directly from induction across $G^+$: an element outside the inducing subgroup acts off-diagonally on the two summands, so its trace is zero. It also follows by subtracting the finite-dimensional character from the principal-series character on an opposite-sign pair of eigenvalues.

Twisting gives the complete formula. For $D_{k,s}$, multiply every displayed value by $|\det g|^s$. Thus

$$
\boxed{
\Theta_{D_{k,s}}(r\,r(\theta))
=-|r|^{2s}\operatorname{sgn}(r)^k
\frac{\sin((k-1)\theta)}{\sin\theta}}
$$

and

$$
\boxed{
\Theta_{D_{k,s}}(r a_t)
=2|r|^{2s}\operatorname{sgn}(r)^k
\frac{e^{-(k-1)|t|/2}}
{|e^{t/2}-e^{-t/2}|}}.
$$

### 8.4 Limits, singularities, and checks

At $k=1$ the formulas read

$$
\Theta_{D_1}(r\,r(\theta))=0,
\qquad
\Theta_{D_1}(r a_t)
=2\operatorname{sgn}(r)\frac1{|e^{t/2}-e^{-t/2}|}.
$$

This is exactly the character of $I(\operatorname{sgn},1)$ on the positive component. The vanishing on the elliptic set expresses the disappearance of genuine elliptic concentration at the limit.

The denominators tend to zero at singular elements. This is expected: the character is locally integrable, not bounded. Multiplying by the Weyl denominator removes the singularity and leaves a finite sum of exponentials, the characteristic form of regularity in rank one.

The elliptic numerator has an algebraic meaning. For $k\ge2$,

$$
\frac{\sin((k-1)\theta)}{\sin\theta}
$$

is the character of $\operatorname{Sym}^{k-2}$ on $r(\theta)$. The minus sign in the discrete character is forced by the vanishing of the induced character on the elliptic set. Changing the convention for which half-ladder is holomorphic changes the two individual characters but not their full-group sum.

Several checks are worth retaining. At an elliptic element, $\Theta_{D_k}=-\Theta_{L_{k-2}}$ because the principal-series character is zero there. At $k=2$, the elliptic character is the constant $-1$. The split formula is positive for $r>0$ in the unitary normalization and decays exponentially with exponent $(k-1)/2$. Replacing $r$ by $-r$ multiplies the answer by $(-1)^k$, exactly the value of the central character at $-1$. Replacing $t$ by $-t$ changes nothing, because the Weyl group exchanges the eigenvalues.

## 9. Formal degrees

### 9.1 Measures and square integrability modulo the center

Let $\pi$ be an irreducible unitary representation with unitary central character and square-integrable matrix coefficients on $G/Z$. Its formal degree $d(\pi)$ is defined by

$$
\int_{G/Z}
\langle\pi(g)v_1,w_1\rangle
\overline{\langle\pi(g)v_2,w_2\rangle}\,d\bar g
=d(\pi)^{-1}
\langle v_1,v_2\rangle\overline{\langle w_1,w_2\rangle}.
$$

This is Schur orthogonality for a noncompact group. The number depends inversely on the Haar measure: replacing $d\bar g$ by $c\,d\bar g$ replaces $d(\pi)$ by $d(\pi)/c$.

We choose the following normalization. On $(G/Z)^0=\mathrm{PSL}_2(\mathbf R)$ the compact subgroup $\mathrm{PSO}(2)$ has volume one, and the quotient measure on $\mathfrak H$ is $dx\,dy/y^2$, equivalently

$$
\frac{4\,du\,dv}{(1-u^2-v^2)^2}
$$

on the unit disk. The other component is given the translate of this measure. Thus the full maximal compact $\mathrm{PO}(2)$ has volume two. This last sentence is part of the normalization, not a convention to be suppressed.

### 9.2 The rank-one calculation

Take a unit lowest-weight vector $v$ in $D_k^+$, $k\ge2$, and use the disk model. If $g$ sends the origin to $z$, then

$$
|\langle\pi(g)v,v\rangle|^2=(1-|z|^2)^k.
$$

The compact variable contributes one because its measure has total mass one. Therefore

$$
\begin{aligned}
\int_{\mathrm{PSL}_2(\mathbf R)}
|\langle\pi(g)v,v\rangle|^2\,dg
&=\int_0^{2\pi}\int_0^1
(1-\rho^2)^k\frac{4\rho\,d\rho\,d\theta}{(1-\rho^2)^2}\\
&=8\pi\int_0^1\rho(1-\rho^2)^{k-2}\,d\rho\\
&=\frac{4\pi}{k-1}.
\end{aligned}
$$

Schur orthogonality gives $d(D_k^+)=(k-1)/(4\pi)$. For the full-group representation $D_k$, choose a vector in the $D_k^+$ summand. Its matrix coefficient vanishes on the negative component and agrees with the preceding coefficient on the positive component. Under our measure normalization the same integral results. Hence

$$
\boxed{d(D_k)=\frac{k-1}{4\pi}}.
$$

Unitary twists $D_{k,s}$ with $s\in i\mathbf R$ have the same formal degree, because the twisting character has absolute value one.

The calculation with one vector suffices because the integral defines a $G$-equivariant operator. Fixing three vectors and viewing the left side as a functional of the fourth produces an intertwiner from the representation to itself. Irreducibility makes it scalar. Polarization then reduces that scalar to the diagonal integral just computed. This is the decisive use of irreducibility in Schur orthogonality.

Formal degree measures spectral density, not vector-space dimension. $D_k$ is infinite-dimensional for every $k$, yet its degree grows linearly with $k$. Larger lowest weight produces faster matrix-coefficient decay, a smaller coefficient integral, and therefore a larger formal degree. This gives an intuitive reason for the factor $k-1$.

### 9.3 Scaling rules and the limit case

Some conventions normalize all of $\mathrm{PO}(2)$, rather than its identity component, to have volume one. That measure is one half of ours on each component. With that convention,

$$
d(D_k)=\frac{k-1}{2\pi}.
$$

Neither formula is meaningful without the measure statement. Passing from $G/Z$ to its identity component while replacing the full induced representation by one of $D_k^\pm$ returns $(k-1)/(4\pi)$ under the probability normalization of $\mathrm{PSO}(2)$.

The expression $(k-1)/(4\pi)$ tends to zero at $k=1$. This does not assign formal degree zero to a discrete representation; it signals that $D_1$ is no longer in the discrete spectrum. Its coefficient integral diverges logarithmically, as Section 6.4 predicted.

## 10. Relative Lie algebra cohomology

### 10.1 The relative complex

Characters distinguish representations spectrally; relative Lie algebra cohomology distinguishes those compatible with the topology of locally symmetric spaces. Let $\mathfrak h\subseteq\mathfrak g$ be the Lie algebra of a compact subgroup $H$. For a $(\mathfrak g,H)$-module $V$, define

$$
C^q(\mathfrak g,H;V)
=\operatorname{Hom}_H\left(\bigwedge^q(\mathfrak g/\mathfrak h)_\mathbf C,V\right).
$$

The differential is

$$
\begin{aligned}
(d\varphi)(X_0,\ldots,X_q)
={}&\sum_i(-1)^iX_i\varphi(X_0,\ldots,\widehat X_i,\ldots,X_q)\\
&+\sum_{i<j}(-1)^{i+j}
\varphi([X_i,X_j],X_0,\ldots,\widehat X_i,\ldots,
\widehat X_j,\ldots,X_q),
\end{aligned}
$$

with brackets taken modulo $\mathfrak h$. The Jacobi identity and representation identity give $d^2=0$. The cohomology is denoted $H^q(\mathfrak g,H;V)$. The same formula applies to the pair obtained by adjoining the positive split center to $H$: one replaces $\mathfrak h$ by $\mathfrak h\oplus\mathbf R\zeta$ and imposes invariance under that center. This is the only noncompact relative subgroup used below.

This complex has a geometric origin. An $H$-equivariant alternating map from the tangent space $\mathfrak g/\mathfrak h$ to $V$ is the value at the base point of a $G$-equivariant differential form on $G/H$. The displayed differential is the exterior derivative evaluated on invariant vector fields. Relative Lie algebra cohomology is therefore the infinitesimal model for differential forms on an arithmetic quotient, not an unrelated algebraic construction.

For the semisimple rank-one pair $(\mathfrak{sl}_2,K^0)$,

$$
(\mathfrak{sl}_2/\mathfrak{so}_2)_\mathbf C
=\mathbf C X_+\oplus\mathbf C X_-
$$

has compact weights $2$ and $-2$. Consequently a degree-one cochain is determined by vectors of weights $2$ and $-2$ in $V$. This turns a cohomology calculation into a compact-weight calculation.

### 10.2 The rank-one calculation

We first isolate the necessity argument, because counting degree-one cochains alone is insufficient: mismatched coefficient systems can have such cochains whose classes are killed by the differential.

**Infinitesimal-character lemma.** Suppose $A$ is an irreducible $(\mathfrak{sl}_2,K^0)$-module and $B$ is a finite-dimensional irreducible module, with infinitesimal characters $\lambda_A$ and $\lambda_B$. If

$$
H^q(\mathfrak{sl}_2,K^0;A\otimes B^\vee)\ne0
$$

for some $q$, then $\lambda_A=\lambda_B$.

To prove the lemma, identify $A\otimes B^\vee$ with $\operatorname{Hom}(B,A)$. The relative complex computing its cohomology is obtained by applying $\operatorname{Hom}_{(\mathfrak{sl}_2,K^0)}(-,A)$ to the relative standard resolution

$$
U(\mathfrak{sl}_2)\otimes_{U(\mathfrak{so}_2)}
\bigwedge^q(\mathfrak{sl}_2/\mathfrak{so}_2)\otimes B.
$$

A central element $z$ can be moved across this resolution in two ways: left multiplication on the enveloping-algebra factor gives its action on the target, while moving it all the way to $B$ gives its action on the source. For a monomial $z=X_1\cdots X_r$, move the factors one at a time. The alternating sum of the $r$ intermediate insertion maps telescopes; the defining differential of the resolution shows that it is a homotopy $h_z$ satisfying

$$
d h_z+h_zd=(\lambda_A(z)-\lambda_B(z))\operatorname{id}.
$$

If the two scalars differ, division by their difference contracts the complex. Thus nonzero cohomology forces equality on every central element. For $\mathfrak{sl}_2$, it is enough to use $z=\Omega+1$.

Take $A=D_k^+$ or $D_k^-$ and $B=F_n=\operatorname{Sym}^n(\mathbf C^2)$. The module $F_n$ is self-dual on $\mathrm{SL}_2$, its shifted Casimir scalar is $(n+1)^2$, and that of $D_k^\pm$ is $(k-1)^2$. Since $n\ge0$ and $k\ge2$, equality forces

$$
n=k-2.
$$

It remains to calculate the matched complex and prove sufficiency. The $K^0$-weights of $F_n$ are $n,n-2,\ldots,-n$. In $D_k^+\otimes F_n$, the lowest possible compact weight is obtained by pairing the lowest weight $k$ with $-n$:

$$
k-n=2.
$$

It occurs once. All other weights in this tensor product are at least $2$. Similarly, all weights in $D_k^-\otimes F_n$ are at most $-2$, with $-2$ occurring once. Therefore

$$
C^0=0,\qquad \dim C^1=2,\qquad C^2=0
$$

for $D_k\otimes F_{k-2}$ relative to $K^0$. Since the neighboring terms vanish, both degree-one cochains are closed and neither is exact. Thus

$$
H^q(\mathfrak{sl}_2,K^0;D_k\otimes F_{k-2})
\simeq
\begin{cases}
\mathbf C^2,&q=1,\\
0,&q\ne1.
\end{cases}
$$

One line comes from the holomorphic ladder and one from the antiholomorphic ladder. Together with the infinitesimal-character lemma, this proves both necessity and sufficiency; in particular it does not confuse the existence of a cochain with the survival of its cohomology class.

For $k=2$, the coefficient is trivial. The two degree-one cochains send $X_+$ to a lowest-weight vector of $D_2^+$ and $X_-$ to a highest-weight vector of $D_2^-$. For $k=4$, the coefficient is $F_2$: the tensor of the weight $4$ vector with the weight $-2$ coefficient vector has total weight $2$, exactly matching $X_+$. A trivial coefficient at $k=4$ gives no weight $2$ and hence no cohomology. This makes $n=k-2$ visible without infinitesimal-character terminology.

### 10.3 Components and signs

The preceding calculation used $K^0$. The reflection $j\in K/K^0$ exchanges $X_+$ and $X_-$ and exchanges the holomorphic and antiholomorphic cohomology lines. Its action may include a sign depending on the chosen oriented basis, but it always has two one-dimensional eigenspaces. Passing to full $K$ means taking invariants, and therefore

$$
H^q(\mathfrak{sl}_2,K;D_k\otimes F_{k-2})
\simeq
\begin{cases}
\mathbf C,&q=1,\\
0,&q\ne1.
\end{cases}
$$

Twisting the coefficient system by a determinant sign interchanges which eigenspace is called invariant, without changing its dimension. It is often better to retain the two lines and label them by the two characters of $K/K^0$; that convention is the source of sign decompositions in Hilbert modular cohomology.

For the limit $D_1$, the matching algebraic highest weight would be $-1$, which does not exist. Hence limits of discrete series are not cohomological with finite-dimensional algebraic coefficients in this regular rank-one sense. They can occur in boundary phenomena, but not in the interior weight range developed here.

### 10.4 Split-center conventions

The full symmetric space $G/K$ has an extra positive central direction. Automorphic cohomology normally removes it by using

$$
K^\dagger=Z(\mathbf R)^0K=\mathbf R_{>0}\mathrm O(2),
$$

whose Lie algebra is $\mathfrak k\oplus\mathbf R\zeta$. Relative cochains must be invariant under the positive center. If $\zeta$ acts nontrivially on the coefficient module, all cochains vanish.

If one instead computes relative to $K$ alone and the central action is trivial, the central line contributes an exterior factor:

$$
H^q(\mathfrak g,K;V)
\simeq H^q(\mathfrak{sl}_2,K;V)
\oplus H^{q-1}(\mathfrak{sl}_2,K;V).
$$

Thus a class concentrated in semisimple degree one appears in degrees one and two. This is not a contradiction with the usual assertion that a weight-$k$ discrete series contributes in degree one: that assertion uses $K^\dagger$, or equivalently quotients the split center. We always state which convention is meant.

If the central action is a nonzero scalar $c$, the one-dimensional central part of the relative differential is multiplication by $c$. Its two-term complex is contractible, so the entire cohomology vanishes. This proves the central-cancellation condition used next rather than merely imposing it as notation.

## 11. Algebraic coefficients and cohomological representations

### 11.1 Algebraic representations of GL2

Every irreducible algebraic representation of $\mathrm{GL}_2$ over $\mathbf C$ is

$$
E_{n,a}=\operatorname{Sym}^n(\mathbf C^2)\otimes\det^a,
\qquad n\ge0,\quad a\in\mathbf Z.
$$

Indeed, restriction to the derived group is the highest-weight string $\operatorname{Sym}^n$ proved in Section 5.4. The remaining central character is algebraic, hence is an integral power on the diagonal torus. If the two torus weights are $b_1\ge b_2$, then $n=b_1-b_2\ge0$ and $a=b_2$, giving exactly the displayed module. Conversely every such symmetric power and determinant twist is algebraic and irreducible, so the list has neither omissions nor repetitions.

Its highest weight is $(n+a,a)$. On a scalar $xI$ it acts by $x^{n+2a}$, so $\zeta$ acts by $n+2a$. Its restriction to $K^0$ has weights $n,n-2,\ldots,-n$; the determinant twist does not alter them because rotations have determinant one.

The dual is

$$
E_{n,a}^\vee\simeq E_{n,-n-a}.
$$

Indeed, $(\operatorname{Sym}^n V)^\vee\simeq\operatorname{Sym}^nV\otimes\det^{-n}$ for a two-dimensional $V$. This formula is important when translating between the convention that puts $E$ into cohomology and the convention that puts $E^\vee$ there.

### 11.2 The cohomology criterion

Consider $D_{k,s}\otimes E_{n,a}$ relative to $K^\dagger$. Two independent conditions are forced. The infinitesimal-character lemma of Section 10.2, followed by the matched compact-weight calculation there, requires $n=k-2$. Triviality on the positive center requires

$$
2s+n+2a=0.
$$

They are also sufficient by the calculation of Chapter 10. The parity at the disconnected center is then automatically compatible. On $-I$, the discrete series contributes $(-1)^k$ and $E_{k-2,a}$ contributes $(-1)^{k-2}$; their product is $1$. Thus positive-center invariance and compact-weight matching also give invariance under the scalar $-I$ contained in $K$.

**Cohomology theorem.** Let $k\ge2$, $n\ge0$, $a\in\mathbf Z$, and $s\in\mathbf C$. Then

$$
H^q(\mathfrak g,(K^\dagger)^0;
D_{k,s}\otimes E_{n,a})
$$

vanishes unless

$$
n=k-2,\qquad 2s+n+2a=0.
$$

When these conditions hold, it is two-dimensional in degree one and zero in every other degree. For full $K^\dagger$ it is one-dimensional in degree one and zero otherwise.

Here $(K^\dagger)^0=Z(\mathbf R)^0K^0$. The theorem includes both infinitesimal and central matching. The first equation identifies the Weyl orbits of infinitesimal parameters; the second cancels the split-center derivative.

If the coefficient convention uses $E_{n,a}^\vee$, the central condition becomes

$$
2s-(n+2a)=0.
$$

Thus a representation cohomological with $E_{n,a}^\vee$ is

$$
D_{n+2,(n+2a)/2}.
$$

Writing the dual explicitly is safer than trying to remember the sign of a weight parameter.

### 11.3 Several real places

Let $F$ be totally real of degree $d$, and write

$$
G_\infty=\prod_{v\mid\infty}\mathrm{GL}_2(\mathbf R).
$$

For weights $k_v\ge2$, parameters $s_v$, and coefficient systems $E_{k_v-2,a_v}$ satisfying local central cancellation, take the external tensor product of the local modules. The relative complex is the tensor product of the local relative complexes. The Künneth formula therefore gives cohomology only in total degree $d$.

Relative to the identity components $(K_v^\dagger)^0$, each place supplies two lines, so

$$
\dim H^d=2^d.
$$

The component group

$$
\prod_{v\mid\infty}K_v/K_v^0\simeq\{\pm1\}^d
$$

acts by independently exchanging the holomorphic and antiholomorphic choices. Every character of this component group occurs exactly once. Taking invariants under all full orthogonal groups leaves one line. This $2^d$-fold sign decomposition is not an extra multiplicity of automorphic representations; it is the topology of the archimedean relative complex.

The degree statement follows without a spectral sequence. At each real place the local complex is cohomologically concentrated in degree one. The tensor product of $d$ such complexes is therefore concentrated in degree $d$, and its degree-$d$ term is the tensor product of the local two-dimensional spaces. If even one local weight or central exponent fails to match, that local complex is acyclic and the entire tensor product is acyclic.

## 12. Parallel weight two

### 12.1 The local infinity type

We now specialize every convention. The untwisted parallel-weight-two local representation is

$$
\pi_v=D_{2,0}=D_2.
$$

It has trivial central character and

$$
D_2|_{G^+}=D_2^+\oplus D_2^-.
$$

Its $K^0$-types are

$$
2,4,6,\ldots\qquad\text{and}\qquad-2,-4,-6,\ldots.
$$

The minimal $K$-type for full $K$ is the two-dimensional type joining weights $2$ and $-2$. The Casimir acts by $2(2-2)=0$, so $\Omega+1$ acts by $1$ and the Harish--Chandra parameter is the Weyl orbit $\{\pm1\}$. The central Lie algebra acts by zero.

Its Weil parameter is

$$
\phi_{2,0}=
\operatorname{Ind}_{W_{\mathbf C}}^{W_{\mathbf R}}(z/|z|),
$$

or explicitly

$$
\phi_{2,0}(z)=
\begin{pmatrix}z/|z|&0\\0&\bar z/|z|\end{pmatrix},
\qquad
\phi_{2,0}(j)=
\begin{pmatrix}0&-1\\1&0\end{pmatrix}.
$$

Its determinant corresponds to the trivial character of $\mathbf R^\times$. This is the unitary automorphic normalization. For comparison, the explicit rule of Section 7.3 shows that twisting to $D_{2,1/2}$ changes the two characters on $\mathbf C^\times$ from $u,u^{-1}$ to $z,\bar z$, while twisting to $D_{2,-1/2}$ gives their inverses. Neither twist is part of the symbol $D_2$ here. Stating the exponent is therefore enough to translate to a dual or nonunitary convention without an implicit reversal.

### 12.2 Holomorphic and antiholomorphic realizations

$D_2^+$ is the lowest-weight representation generated by a vector of rotation weight $2$; $D_2^-$ is its complex conjugate. A holomorphic differential $f(z)\,dz$ transforms with weight two because

$$
d(gz)=\det(g)(cz+d)^{-2}\,dz
$$

for $g\in G^+$. Thus the lowest compact type is not an arbitrary label: it is the transformation law of a differential on the upper half-plane.

An orientation-reversing element does not preserve holomorphicity. It exchanges $D_2^+$ and $D_2^-$. This is why the representation of $G^+$ naturally has two possible archimedean members, while the representation of the full group packages them into the single irreducible $D_2$.

The passage from a classical holomorphic form can be checked directly. If $f$ has weight $k$ on the upper half-plane, define on the positive component, suppressing finite-place variables,

$$
\Phi_f(g)=\det(g)^{k/2}(ci+d)^{-k}f(gi),
\qquad
g=\begin{pmatrix}a&b\\c&d\end{pmatrix}.
$$

A positive scalar leaves $gi$ unchanged and contributes equal powers in the determinant and automorphy factor, so it acts trivially. Since

$$
r(\theta)i=i,
\qquad
(-\sin\theta)i+\cos\theta=e^{-i\theta},
$$

right translation gives

$$
\Phi_f(gr(\theta))=e^{ik\theta}\Phi_f(g).
$$

Thus a holomorphic weight-$k$ form generates the $+k$ lowest-weight line with our rotation convention. Complex conjugation generates the $-k$ line. At $k=2$ this proves, without relying on terminology, that the full real representation is $D_2$ and not a principal series with the same infinitesimal character.

A finite-order sign twist at the real place does not produce a new full-group infinity type, because $D_2\otimes\operatorname{sgn}\det\simeq D_2$. A twist $|\det|^{it}$ does produce $D_{2,it}$; it remains unitary and has the same compact types, but its central character is $|\cdot|^{2it}$ and its infinitesimal central scalar is $2it$. Therefore the phrase “parallel weight two” determines the compact and semisimple parameter, while a complete global specification must also state the central normalization. In this book “the parallel-weight-two infinity type” means the untwisted unitary choice $D_2$ at every real place.

The explicit character is especially simple. For regular elliptic elements,

$$
\Theta_{D_2}(r\,r(\theta))=-1.
$$

For positive-determinant regular split elements,

$$
\Theta_{D_2}(r a_t)
=2\frac{e^{-|t|/2}}{|e^{t/2}-e^{-t/2}|},
$$

and it vanishes on the negative-determinant component. With the measure of Chapter 9,

$$
d(D_2)=\frac1{4\pi}.
$$

These three formulas—elliptic character $-1$, split decay exponent $1/2$, and formal degree $1/(4\pi)$—form a compact diagnostic for the chosen normalization.

They also show why weight two is suitable as a cuspidal archimedean test type. The nonzero elliptic character detects elliptic conjugacy, while square integrability modulo the center isolates a discrete spectral contribution. The limit $D_1$ would fail both tests: its elliptic character vanishes and it has no positive formal degree. The difference between weights one and two is therefore structural, not a cosmetic shift in the compact label.

### 12.3 Cohomology and sign decomposition

For weight two the algebraic coefficient is trivial: $E_{0,0}=\mathbf C$. The central cancellation condition is automatic, and the local cohomology is

$$
H^q(\mathfrak g,(K^\dagger)^0;D_2)
\simeq
\begin{cases}
\mathbf C^2,&q=1,\\
0,&q\ne1.
\end{cases}
$$

The two lines correspond to the weight $2$ cochain on $X_+$ and the weight $-2$ cochain on $X_-$. Under the full $K^\dagger$ one invariant combination remains, so the dimension is one.

For a totally real field of degree $d$, the parallel infinity type is

$$
\pi_\infty=\bigotimes_{v\mid\infty}D_2.
$$

It contributes in total degree $d$. Relative to connected orthogonal groups the cohomology has dimension $2^d$ and decomposes into one line for every sign character of $\{\pm1\}^d$. The all-holomorphic tensor and all-antiholomorphic tensor are two extreme lines; mixed choices are equally necessary for the full real cohomology.

### 12.4 A normalization ledger

The following statements all refer to the same object and remove the remaining ambiguity.

| Feature                                | Convention and value                                                                                       |
| -------------------------------------- | ---------------------------------------------------------------------------------------------------------- |
| Group                                  | Full $\mathrm{GL}_2(\mathbf R)$                                                                            |
| Maximal compact                        | $K=\mathrm O(2)$; $K^0=\mathrm{SO}(2)$                                                                     |
| Rotation                               | $r(\theta)=\left(\begin{smallmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{smallmatrix}\right)$ |
| Weight-two module                      | $D_2=\operatorname{Ind}_{G^+}^G D_2^+$                                                                     |
| Restriction to $G^+$                   | $D_2^+\oplus D_2^-$                                                                                        |
| Minimal rotation weights               | $+2$ and $-2$                                                                                              |
| Central character                      | Trivial                                                                                                    |
| Central derivative                     | $0$                                                                                                        |
| Casimir                                | $\Omega=H^2+2H+4FE$, eigenvalue $0$                                                                        |
| Harish--Chandra parameter              | $\{\pm1\}$                                                                                                 |
| Weil absolute value                    | $                                                                                                          |
| Weil parameter                         | $\operatorname{Ind}_{W_{\mathbf C}}^{W_{\mathbf R}}(z/                                                     |
| Elliptic character                     | $-1$ on regular elliptic elements                                                                          |
| Formal degree                          | $1/(4\pi)$ when $\mathrm{PSO}(2)$ has volume one                                                           |
| Coefficient system                     | Trivial in the unitary weight-two normalization                                                            |
| Local cohomological degree             | $1$ after quotienting the positive split center                                                            |
| Parallel degree over $[F:\mathbf Q]=d$ | $d$                                                                                                        |

If the Haar measure is halved so that all of $\mathrm{PO}(2)$ has volume one, the formal degree doubles. If the coefficient system is placed in dual form, the sign of the central exponent in the cohomology criterion reverses. If $|\det|^s$ is introduced, the scalar center becomes $|\cdot|^{2s}$ and the central derivative becomes $2s$. None of these translations changes the underlying compact-weight statement.

Three superficially similar assertions should now be kept separate. “Lowest weight two” refers to $D_2^+$ on $G^+$. “Discrete series of weight two” refers to the full $D_2$ after adjoining the antiholomorphic conjugate through the negative component. “Cohomological with trivial coefficients” refers to the matching of $D_2$ with $E_{0,0}$ after quotienting the positive split center. They coincide in the selected normalization, but they express respectively compact representation theory, disconnected-group representation theory, and topology.

## 13. Final synthesis

The representation theory of $\mathrm{GL}_2(\mathbf R)$ is governed by three elementary geometries. Polar decomposition retracts the group onto $\mathrm O(2)$ and turns representations into ladders of rotation types. The two Cartan subgroups separate split and elliptic conjugacy, making principal characters visible on the split set and discrete characters visible on both. The upper half-plane supplies the invariant measure, holomorphic realizations, and the cohomological tangent directions.

From these geometries the principal conclusions follow in a single chain. Normalized induction produces a two-sided compact-weight ladder. At the integral parameter $\operatorname{sgn}^k|\cdot|^{k-1}$ two ladder coefficients vanish. The finite middle string restricts to $\operatorname{Sym}^{k-2}$ on the derived group and is the centrally normalized module $L_{k-2}$ on $G$, while the two outer strings form $D_k$. They are exchanged by the negative component of $G$, so the full-group representation is irreducible. For $k\ge2$ its coefficients are square-integrable modulo the center; at $k=1$ the integral diverges at the tempered boundary.

The same exact sequence computes the character. The same lowest-weight matrix coefficient computes the formal degree. The same extreme compact weights compute relative Lie algebra cohomology. Thus the apparently different invariants

$$
\text{character},\qquad
\text{formal degree},\qquad
\text{infinitesimal character},\qquad
\text{cohomology}
$$

are four readings of one rank-one structure.

At parallel weight two this structure reaches its smallest genuine discrete value. Each real place contributes $D_2$, trivial central character, Harish--Chandra parameter $\{\pm1\}$, Weil parameter $\operatorname{Ind}(z/|z|)$, and one holomorphic plus one antiholomorphic cohomology line. Over a totally real field of degree $d$, their tensor product contributes in degree $d$ and carries all $2^d$ archimedean sign characters. This is the exact infinity type required by cohomological weight-two automorphic representations.

Every entry in that final statement is now forced by an earlier calculation. Lowest weight two forces the Casimir scalar and Weil angular exponent. Trivial positive-center action forces the untwisted unitary normalization. The two extreme compact weights force degree-one cohomology with trivial coefficients. Tensor product forces degree $d$ and the $2^d$ sign lines. Finally, the chosen quotient measure forces the formal degree $1/(4\pi)$ at each place. There is no remaining implicit shift, parity choice, or measure convention.
