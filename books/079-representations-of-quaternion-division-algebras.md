# Representations of Quaternion Division Algebras

## Contents

1. [The anisotropic local group](#1-the-anisotropic-local-group)
   - [The problem and the standing conventions](#11-the-problem-and-the-standing-conventions)
   - [The unramified cyclic model](#12-the-unramified-cyclic-model)
   - [Valuation, order, and residue field](#13-valuation-order-and-residue-field)
   - [Reduced norm and the center](#14-reduced-norm-and-the-center)
2. [The multiplicative group and compactness modulo the center](#2-the-multiplicative-group-and-compactness-modulo-the-center)
   - [Two decompositions of $D^\times$](#21-two-decompositions-of-dtimes)
   - [Why the central quotient is compact](#22-why-the-central-quotient-is-compact)
   - [Finite dimensionality and admissibility](#23-finite-dimensionality-and-admissibility)
   - [What compactness does not say](#24-what-compactness-does-not-say)
3. [Characters and the reduced norm](#3-characters-and-the-reduced-norm)
   - [The abelianization problem](#31-the-abelianization-problem)
   - [Commutators and norm-one elements](#32-commutators-and-norm-one-elements)
   - [Classification of smooth characters](#33-classification-of-smooth-characters)
   - [Central characters of one-dimensional representations](#34-central-characters-of-one-dimensional-representations)
   - [The special packet in the selected normalization](#35-the-special-packet-in-the-selected-normalization)
4. [Congruence layers](#4-congruence-layers)
   - [Why the filtration is the main coordinate system](#41-why-the-filtration-is-the-main-coordinate-system)
   - [The associated graded quotients](#42-the-associated-graded-quotients)
   - [Conjugation on a layer](#43-conjugation-on-a-layer)
   - [Commutators and central intersections](#44-commutators-and-central-intersections)
   - [Characters of the layers](#45-characters-of-the-layers)
5. [Level, conductor, and twisting](#5-level-conductor-and-twisting)
   - [Three related depth measurements](#51-three-related-depth-measurements)
   - [Central conductor constraints](#52-central-conductor-constraints)
   - [Twists and cancellation](#53-twists-and-cancellation)
   - [Minimal twists](#54-minimal-twists)
6. [Clifford theory along the normal filtration](#6-clifford-theory-along-the-normal-filtration)
   - [Why restriction is the classification engine](#61-why-restriction-is-the-classification-engine)
   - [Orbit and stabilizer](#62-orbit-and-stabilizer)
   - [Extension and projective extension](#63-extension-and-projective-extension)
   - [The two-step valuation quotient](#64-the-two-step-valuation-quotient)
7. [An exhaustive finite-quotient classification](#7-an-exhaustive-finite-quotient-classification)
   - [Finite data plus a uniformizer operator](#71-finite-data-plus-a-uniformizer-operator)
   - [The classification theorem](#72-the-classification-theorem)
   - [The invariant-orbit case](#73-the-invariant-orbit-case)
   - [The two-element orbit case](#74-the-two-element-orbit-case)
   - [Coefficients not algebraically closed](#75-coefficients-not-algebraically-closed)
8. [Compact induction and intertwining](#8-compact-induction-and-intertwining)
   - [Compact-mod-center inducing subgroups](#81-compact-mod-center-inducing-subgroups)
   - [Irreducibility from intertwining](#82-irreducibility-from-intertwining)
   - [Isomorphism and admissibility](#83-isomorphism-and-admissibility)
   - [The induced character formula](#84-the-induced-character-formula)
9. [Level zero from the residue field](#9-level-zero-from-the-residue-field)
   - [Regular residue-field characters](#91-regular-residue-field-characters)
   - [The construction and its irreducibility](#92-the-construction-and-its-irreducibility)
   - [Dimensions, centers, and characters](#93-dimensions-centers-and-characters)
   - [Irregular characters as a counterexample](#94-irregular-characters-as-a-counterexample)
10. [Positive depth and tame admissible pairs](#10-positive-depth-and-tame-admissible-pairs)
    - [Why quadratic tori reappear](#101-why-quadratic-tori-reappear)
    - [Regularity and minimality](#102-regularity-and-minimality)
    - [The inducing subgroup and its extension](#103-the-inducing-subgroup-and-its-extension)
    - [Dimension and central character](#104-dimension-and-central-character)
    - [Conductor formulas](#105-conductor-formulas)
    - [The tame ramified and unramified shapes](#106-the-tame-ramified-and-unramified-shapes)
    - [Direct and quadratic-induction normalizations](#107-direct-and-quadratic-induction-normalizations)
11. [The wild range and abstract exhaustivity](#11-the-wild-range-and-abstract-exhaustivity)
    - [What tame pairs do not cover](#111-what-tame-pairs-do-not-cover)
    - [An exhaustive Clifford parameter](#112-an-exhaustive-clifford-parameter)
    - [How projective data enter](#113-how-projective-data-enter)
12. [Duality, twists, and matrix characters](#12-duality-twists-and-matrix-characters)
    - [Contragredients and pairings](#121-contragredients-and-pairings)
    - [Twisting inducing data](#122-twisting-inducing-data)
    - [Regular elements and conjugacy](#123-regular-elements-and-conjugacy)
    - [Character values from inducing data](#124-character-values-from-inducing-data)
13. [Compact-open invariants](#13-compact-open-invariants)
    - [Maximal-order invariants](#131-maximal-order-invariants)
    - [Eichler-like compact opens](#132-eichler-like-compact-opens)
    - [A finite Mackey formula](#133-a-finite-mackey-formula)
    - [Level-zero invariant dimensions](#134-level-zero-invariant-dimensions)
14. [Formal degree and volume](#14-formal-degree-and-volume)
    - [The needed normalization](#141-the-needed-normalization)
    - [Schur orthogonality on the central quotient](#142-schur-orthogonality-on-the-central-quotient)
    - [Compact induction and degree](#143-compact-induction-and-degree)
15. [Type vectors and the newvector question](#15-type-vectors-and-the-newvector-question)
    - [Why normal congruence groups do not select a line](#151-why-normal-congruence-groups-do-not-select-a-line)
    - [The canonical type multiplicity space](#152-the-canonical-type-multiplicity-space)
    - [Toric lines and test vectors](#153-toric-lines-and-test-vectors)
    - [The selected split-side newvector interface](#154-the-selected-split-side-newvector-interface)
16. [Integral lattices and integral pairings](#16-integral-lattices-and-integral-pairings)
    - [Coefficient fields and the existence criterion](#161-coefficient-fields-and-the-existence-criterion)
    - [Lattices in special and dihedral types](#162-lattices-in-special-and-dihedral-types)
    - [Finite free induction and base change](#163-finite-free-induction-and-base-change)
    - [Perfect duality and self-dual lattices](#164-perfect-duality-and-self-dual-lattices)
    - [Reduction and the nonbanal boundary](#165-reduction-and-the-nonbanal-boundary)
17. [Measures, orbital normalization, and transfer data](#17-measures-orbital-normalization-and-transfer-data)
    - [A compatible system of Haar measures](#171-a-compatible-system-of-haar-measures)
    - [Centralizers, discriminants, and orbital integrals](#172-centralizers-discriminants-and-orbital-integrals)
    - [Pointwise characters versus distributions](#173-pointwise-characters-versus-distributions)
    - [The selected comparison package](#174-the-selected-comparison-package)
18. [Examples over $\mathbf Q_p$](#18-examples-over-mathbf-q_p)
    - [Norm characters](#181-norm-characters)
    - [A level-zero representation](#182-a-level-zero-representation)
    - [A positive-depth unramified example](#183-a-positive-depth-unramified-example)
    - [A tame ramified example and the dyadic warning](#184-a-tame-ramified-example-and-the-dyadic-warning)
19. [The transfer-facing dictionary](#19-the-transfer-facing-dictionary)
    - [The classification table](#191-the-classification-table)
    - [Regular-character values](#192-regular-character-values)
    - [What is ready for comparison](#193-what-is-ready-for-comparison)
    - [Conclusion](#194-conclusion)

## 1. The anisotropic local group

### 1.1 The problem and the standing conventions

The multiplicative group of a division algebra is the smallest noncommutative local group whose quotient by its center is compact. That compactness removes parabolic induction, continuous families of principal series, and infinite-dimensional irreducible representations. It does not make the representation theory trivial. The noncommutativity has migrated into the congruence filtration: residue-field characters are moved by Frobenius, positive-depth characters have nontrivial commutator pairings, and extending a representation across a stabilizer may require a projective rather than an ordinary representation.

Throughout, $K$ is a nonarchimedean local field, with normalized valuation

$$
v_K(K^\times)=\mathbf Z,
$$

ring of integers $\mathcal O_K$, maximal ideal $\mathfrak p_K=(\varpi)$, and residue field $k$ of cardinality $q$. The algebra $D$ is the quaternion division algebra over $K$. Its center is $K$, embedded as scalar quaternions. The coefficient field $C$ is algebraically closed of characteristic zero unless a statement explicitly discusses descent to a smaller characteristic-zero field. Representations are smooth left representations on $C$-vector spaces. Induced functions satisfy left covariance and carry the right-translation left action

$$
(g_0f)(x)=f(xg_0).
$$

This convention fixes every inverse in the later Mackey and character formulas.

We write $\operatorname{Trd}$ and $\operatorname{Nrd}$ for reduced trace and reduced norm. Intrinsically, after a splitting $D\otimes_KK^s\cong M_2(K^s)$ they are the descended matrix trace and determinant. Thus every $x\in D$ satisfies

$$
x^2-\operatorname{Trd}(x)x+\operatorname{Nrd}(x)=0,
$$

the equation given by its reduced characteristic polynomial, and canonical conjugation is

$$
\bar x=\operatorname{Trd}(x)-x.
$$

Consequently $x\bar x=\bar x x=\operatorname{Nrd}(x)$, reduced norm is multiplicative, and its restriction to any quadratic subfield is the field norm. These facts make the norm much more than a quadratic form: it supplies the valuation and eventually the entire abelianization of $D^\times$.

The argument has three movements. First, the valuation filtration and compact central quotient reduce every irreducible representation to finite data. Second, Clifford theory and compact induction turn regular residue characters and tame quadratic characters into the special and dihedral packets required in the selected route, while an abstract finite-quotient classification keeps the primitive wild boundary honest. Third, conductors, type multiplicities, pairings, lattices, characters, and compatible measures prepare those packets for comparison with their selected split companions. The general induction, Mackey, contragredient, and character formalism comes from Book 72. The admissible-pair and character-dependent rectifier normalization comes from Book 74. The valuation filtration, division-side types, their intertwining, and all other consequences peculiar to $D^\times$ are proved here.

### 1.2 The unramified cyclic model

Calculations need coordinates adapted to the valuation. Let $L/K$ be the unramified quadratic extension, embedded as a maximal subfield of $D$, and let $\sigma$ be its nontrivial $K$-automorphism. We choose a division uniformizer $\Pi$ so that

$$
D=L\oplus L\Pi,
\qquad
\Pi a=\sigma(a)\Pi,
\qquad
\Pi^2=\varpi.
$$

Changing $\Pi$ by a unit of $L$ changes its square by a norm; the displayed normalization is available because the cyclic algebra $(L/K,\sigma,\varpi)$ represents the unique nontrivial degree-two Brauer class. None of the intrinsic objects below depends on this choice.

Here is the local-algebra argument behind this coordinate model. The local invariant isomorphism

$$
\operatorname{inv}_K:\operatorname{Br}(K)\xrightarrow{\sim}\mathbf Q/\mathbf Z
$$

sends the class of a quaternion division algebra to $1/2$. The unramified cyclic algebra $(L/K,\sigma,\varpi)$ also has invariant $1/2$: norms from $L$ have even valuation, so $\varpi$ is not a norm, while the quadratic cyclic class has order two. It is therefore isomorphic to $D$. This proves simultaneously that $L$ embeds and that the displayed basis and relations may be chosen. More generally, if $E/K$ is any quadratic field, scalar extension multiplies the invariant by two, so $D\otimes_KE$ is split. Degree-two cyclic descent then embeds $E$ in $D$, and conjugacy of embeddings follows from the usual central-simple intertwiner argument. These are the only local Brauer facts used below.

For $x=a+b\Pi$, canonical conjugation is

$$
\overline{x}=\sigma(a)-b\Pi,
$$

and therefore

$$
\operatorname{Trd}(x)=\operatorname{Tr}_{L/K}(a),
\qquad
\operatorname{Nrd}(x)=N_{L/K}(a)-\varpi N_{L/K}(b).
$$

The two summands on the right have valuations of opposite parity unless both vanish. Their failure to cancel is the valuation-theoretic reason this cyclic algebra is division.

### 1.3 Valuation, order, and residue field

The normalization that prevents later factors of two is

$$
v_D(x)=v_K(\operatorname{Nrd}(x))
\qquad(x\in D^\times).
$$

Then $v_D(D^\times)=\mathbf Z$, $v_D(\Pi)=1$, and for a scalar $z\in K^\times$,

$$
v_D(z)=2v_K(z),
$$

because $\operatorname{Nrd}(z)=z^2$. Thus $v_D$ extends twice, not once, the normalized valuation on the center. An alternative convention taking values in $\frac12\mathbf Z$ restricts to $v_K$; we never use it.

Define

$$
\mathcal O_D=\{x\in D\mid v_D(x)\ge0\},
\qquad
\mathfrak P_D=\{x\in D\mid v_D(x)\ge1\}.
$$

These are the unique maximal order and its unique maximal two-sided ideal. In the cyclic coordinates,

$$
\mathcal O_D=\mathcal O_L\oplus\mathcal O_L\Pi,
\qquad
\mathfrak P_D=\Pi\mathcal O_D=\mathcal O_D\Pi.
$$

Reduction kills the $\Pi$-summand and gives

$$
k_D=\mathcal O_D/\mathfrak P_D\cong k_L\cong\mathbf F_{q^2}.
$$

Here is why these assertions follow from the valuation rather than from the chosen coordinates. Multiplicativity of reduced norm makes $v_D$ additive, and the parity separation in Section 1.2 gives the ultrametric inequality. Hence the nonnegative-valuation elements form a local ring, its positive-valuation elements form its unique maximal ideal, and every one-sided ideal generated by an element of least valuation is a power of $\mathfrak P_D$. Any $\mathcal O_K$-order consists of elements integral over $\mathcal O_K$; their reduced characteristic polynomials force nonnegative $v_D$, so every order lies in $\mathcal O_D$. This proves maximality and uniqueness. The residue degree of $D$ is therefore two. It must not be confused with the index two of the division algebra, even though the numbers agree here.

### 1.4 Reduced norm and the center

The reduced norm is surjective:

$$
\operatorname{Nrd}:D^\times\twoheadrightarrow K^\times.
$$

Indeed $\operatorname{Nrd}(\Pi)=-\varpi$ has valuation one. On the embedded unramified field $L$, reduced norm is $N_{L/K}$, and the norm of an unramified extension maps $\mathcal O_L^\times$ onto $\mathcal O_K^\times$. At residue level this is the surjective map $x\mapsto x^{q+1}$ from $k_D^\times$ to $k^\times$; on principal units, successive approximation uses the surjective finite-field trace. This argument remains valid in residue characteristic two and proves surjectivity without an unstated restriction on the residue characteristic.

The norm-one group

$$
D^1=\ker(\operatorname{Nrd})
$$

lies in $\mathcal O_D^\times$ and is compact. The center meets it in the scalars $z$ with $z^2=1$. Reduced norm on the center is the squaring map, not the identity. This elementary fact explains why a norm character has central character $\mu^2$ and is one of the most common normalization checks in the subject.

## 2. The multiplicative group and compactness modulo the center

### 2.1 Two decompositions of $D^\times$

Every nonzero element has a unique valuation and a unit part, so

$$
D^\times=\bigsqcup_{n\in\mathbf Z}\Pi^n\mathcal O_D^\times.
$$

Equivalently, multiplication gives a semidirect description

$$
D^\times=\langle\Pi\rangle\ltimes\mathcal O_D^\times,
$$

where conjugation by $\Pi$ induces Frobenius on the residue field. The corresponding automorphism of $\mathcal O_D^\times$ has square one, and the identity $\Pi^2=\varpi$ records how the valuation factor meets the center: $\langle\Pi\rangle\cap K^\times=\langle\Pi^2\rangle$.

Modulo the center, valuation has only two parities. Hence

$$
D^\times=K^\times\mathcal O_D^\times
\sqcup K^\times\Pi\mathcal O_D^\times.
$$

This two-cell decomposition, rather than a Bruhat decomposition, is the basic global geometry of the group.

### 2.2 Why the central quotient is compact

The quotient $\mathcal O_D^\times/\mathcal O_K^\times$ is compact, and the preceding decomposition maps two copies of it onto $D^\times/K^\times$. Thus

$$
D^\times/K^\times\quad\text{is compact}.
$$

It is not generally finite: $\mathcal O_D^\times$ contains the infinite principal-unit group $U_D^1$. Compactness says that every open subgroup has finite index after the center is included, and that locally constant functions on the quotient factor through finite quotients. It does not turn the quotient into a finite group.

There is also a norm-one proof. Every class in $D^\times/K^\times$ can be scaled so that its norm lies in one of finitely many square classes represented by a compact set; the remaining norm-one part is compact. The parity proof is more concrete and keeps the valuation normalization visible.

### 2.3 Finite dimensionality and admissibility

One must not assume a scalar central character in order to prove finite dimensionality and then invoke finite dimensionality to obtain that character. The correct argument first restricts to the compact normal subgroup.

Let $(\pi,V)$ be irreducible smooth. Choose $0\ne v\in V$ fixed by $U_D^m$. The span

$$
W=C[\mathcal O_D^\times]v
$$

is finite dimensional because the orbit factors through $\mathcal O_D^\times/U_D^m$. It is semisimple by characteristic-zero averaging. Choose an irreducible constituent $\tau$. Conjugation by $\Pi$ has order two on isomorphism classes of $\mathcal O_D^\times$-representations, because $\Pi^2=\varpi$ is central. Hence the orbit of $\tau$ has one or two elements.

Consider first an invariant orbit. After choosing an intertwiner between $\tau$ and $\tau^\Pi$, the action on the $\tau$-multiplicity space is generated by one invertible operator $T$. Irreducibility of $V$ makes this multiplicity space a simple module over

$$
C[T,T^{-1}].
$$

Every simple module over this Laurent polynomial ring is $C[T,T^{-1}]/(T-c)$ for some $c\in C^\times$, because $C$ is algebraically closed. It is one dimensional. In the two-element orbit case the same argument applies to the stabilizer generated by $\mathcal O_D^\times$ and $\Pi^2$, after which induction across its index-two inclusion doubles the dimension. Thus $V$ is finite dimensional in both cases.

Now Schur's lemma over $C$ makes the center act through a smooth character $\omega$. A shorter geometric argument becomes available after that fact. Choose $0\ne v\in V$ fixed by a compact open subgroup $J$. The image of $J$ in $D^\times/K^\times$ is open, so

$$
K^\times J\backslash D^\times
$$

is finite. The orbit of $v$ is spanned by one vector for each coset, since central elements merely rescale $v$. This recovers finite dimensionality directly once the central character is known.

**Theorem 2.1.** Every irreducible smooth representation of $D^\times$ over $C$ is finite dimensional and admissible.

Finite dimensionality implies admissibility immediately. It also gives a common open stabilizer for a basis; taking its normal core and then a sufficiently deep congruence subgroup shows that every irreducible kills $U_D^m$ for some $m$. The infinite group has become finite-level data together with the scalar action of the center.

Over a nonalgebraically closed field, simple modules over the Laurent ring need not have degree one and the center can act through a larger endomorphism division algebra. A scalar central character is then additional descent data rather than an automatic conclusion.

### 2.4 What compactness does not say

A smooth representation of a compact group can be an infinite direct sum, so compactness modulo center does not make every smooth representation finite dimensional. Irreducibility is decisive. Nor does compactness classify the irreducibles: a profinite group can have irreducible representations through arbitrarily deep finite quotients.

There is also no analogue of a nontrivial parabolic subgroup of $D^\times$. Thus the character versus higher-dimensional division is intrinsic, not a principal-series versus supercuspidal division. Every irreducible has matrix coefficients compactly supported modulo the center, simply because the entire central quotient is compact. Book 80 compares these representations with a particular nonprincipal portion of a matrix group, but no matching theorem is asserted here.

## 3. Characters and the reduced norm

### 3.1 The abelianization problem

A homomorphism from a noncommutative group to $C^\times$ kills commutators. To classify one-dimensional representations, we must therefore compute $D^{\times,\mathrm{ab}}$. Reduced norm is an evident candidate: it is surjective and kills commutators. The substantive assertion is that it kills nothing more after abelianization.

**Theorem 3.1.** The sequence

$$
1\longrightarrow D^1=[D^\times,D^\times]
\longrightarrow D^\times
\xrightarrow{\operatorname{Nrd}}K^\times
\longrightarrow1
$$

is exact. Consequently reduced norm induces an isomorphism

$$
D^{\times,\mathrm{ab}}\cong K^\times.
$$

### 3.2 Commutators and norm-one elements

The inclusion $[D^\times,D^\times]\subseteq D^1$ follows immediately from multiplicativity of the norm. For the reverse inclusion there is a direct argument that avoids confusing the commutator subgroup with its topological closure.

Take $x\in D^1$. If $x$ is noncentral, then $E=K[x]$ is a quadratic field, and it is separable. Indeed, the only possible inseparable case is characteristic two with reduced trace zero; then $\operatorname{Nrd}(x)=1$ would give $(x-1)^2=0$, impossible in a division algebra unless $x=1$. The restriction of reduced norm to $E^\times$ is $N_{E/K}$, so $N_{E/K}(x)=1$. Let $\sigma$ be the nontrivial $K$-automorphism of $E$. Hilbert 90 supplies $y\in E^\times$ with

$$
x=y\sigma(y)^{-1}.
$$

Choose $j\in D^\times$ whose conjugation action on $E$ is $\sigma$; such a $j$ exists because the two embeddings of $E$ obtained from the identity and $\sigma$ are conjugate in the central simple algebra $D$. With the convention $[a,b]=aba^{-1}b^{-1}$,

$$
[y,j]=yj y^{-1}j^{-1}
=y\sigma(y)^{-1}=x.
$$

If $x$ is central, then $x^2=\operatorname{Nrd}(x)=1$. The element $1$ is trivial, while $-1$, when distinct from $1$, is the commutator of two anticommuting quaternion generators. Thus every element of $D^1$ is a commutator, and

$$
[D^\times,D^\times]=D^1.
$$

The congruence calculations of Chapter 4 give the infinitesimal shadow of this proof: finite-field Hilbert 90 controls residue units, and additive trace controls positive layers. The direct quadratic-field argument is what proves equality with the abstract commutator subgroup, not merely equality after closure.

### 3.3 Classification of smooth characters

Let $\chi:D^\times\to C^\times$ be smooth. Theorem 3.1 gives a unique character $\mu:K^\times\to C^\times$ such that

$$
\chi=\mu\circ\operatorname{Nrd}.
$$

The resulting $\mu$ is smooth: reduced norm is an open surjection, as is clear on the valuation factor and from the norm maps on unit filtrations. Conversely every smooth $\mu$ gives a smooth character of $D^\times$. Thus:

**Corollary 3.2.** The map

$$
\mu\longmapsto\mu\circ\operatorname{Nrd}
$$

is a bijection from smooth characters of $K^\times$ to one-dimensional smooth representations of $D^\times$.

It is false that restriction to the center classifies such characters: restriction remembers $\mu^2$, and distinct quadratic twists of $\mu$ have the same square. The reduced norm, rather than the central restriction, is the correct coordinate.

### 3.4 Central characters of one-dimensional representations

For $z\in K^\times$,

$$
(\mu\circ\operatorname{Nrd})(z)=\mu(z^2)=\mu(z)^2.
$$

Hence the central character is $\mu^2$. Its conductor can be smaller than that of $\mu$ because squaring characters may cancel quadratic ramification. If the residue characteristic is odd and $a(\mu)\ge2$, then $a(\mu^2)=a(\mu)$: on the last nontrivial principal-unit quotient, multiplication by two is invertible. At conductor one a quadratic residue character can disappear after squaring, and in residue characteristic two cancellation can occur deeper in the filtration. No unjustified equality of conductors is built into our definitions.

As a worked example, an unramified character is determined by $c=\mu(\varpi)$. Its quaternionic norm character is trivial on $\mathcal O_D^\times$ and sends $\Pi$ to $\mu(-\varpi)$. A ramified $\mu$ is already nontrivial on $\mathcal O_K^\times$, and the resulting character of $D^\times$ is nontrivial on a corresponding principal congruence layer.

### 3.5 The special packet in the selected normalization

Why call a one-dimensional representation a special packet? The terminology records its role, not its dimension. In the selected route, a character $\mu$ of $K^\times$ labels a special representation on the split degree-two group. Its division-algebra member is

$$
\operatorname{Sp}_D(\mu)=\mu\circ\operatorname{Nrd}.
$$

There is one member on the division side. The word packet packages the common parameter, central character, twist law, and conductor convention. They are

$$
\omega_{\operatorname{Sp}_D(\mu)}=\mu^2,
\qquad
\operatorname{Sp}_D(\mu)\otimes(\chi\circ\operatorname{Nrd})
=\operatorname{Sp}_D(\mu\chi),
$$

and

$$
a_D(\operatorname{Sp}_D(\mu))=
\begin{cases}
1,&a(\mu)=0,\\
2a(\mu),&a(\mu)>0.
\end{cases}
$$

The exceptional value $1$ for an unramified character is essential: the companion special representation has a single monodromy contribution even though the division-side character is trivial on the maximal compact subgroup. Thus congruence depth alone cannot define the selected conductor for this family. This is the only exceptional clause; ramified special packets and every higher-dimensional packet are read from their last nontrivial unit layer.

At a regular element $d$, the value is simply

$$
\Theta_{\operatorname{Sp}_D(\mu)}(d)=\mu(\operatorname{Nrd}d).
$$

This elementary formula later anchors the sign and normalization of the special comparison.

## 4. Congruence layers

### 4.1 Why the filtration is the main coordinate system

Compactness reduces irreducible representations to finite quotients, but it does not say which finite quotients or how conjugation acts on them. The canonical neighborhood basis is

$$
U_D^0=\mathcal O_D^\times,
\qquad
U_D^n=1+\mathfrak P_D^n\quad(n\ge1).
$$

Every $U_D^n$ is compact, open, and normal in $D^\times$, because $\mathfrak P_D^n$ is the unique two-sided ideal of its valuation. Normality is unusually powerful: for irreducible $\pi$, the invariant subspace $V^{U_D^n}$ is either $0$ or all of $V$.

The filtration is separated and complete,

$$
\bigcap_{n\ge1}U_D^n=\{1\},
$$

and its quotients are finite. It is therefore simultaneously a topological coordinate system and the sequence of finite approximations on which character theory operates.

### 4.2 The associated graded quotients

Reduction gives

$$
U_D^0/U_D^1\cong k_D^\times,
$$

a cyclic group of order $q^2-1$. For $n\ge1$, the map

$$
1+x\longmapsto x\bmod\mathfrak P_D^{n+1}
$$

identifies

$$
U_D^n/U_D^{n+1}
\cong
\mathfrak P_D^n/\mathfrak P_D^{n+1}
\cong(k_D,+).
$$

Indeed $(1+x)(1+y)\equiv1+x+y$ modulo $\mathfrak P_D^{n+1}$. Each positive layer therefore has $q^2$ elements. It follows that

$$
|\mathcal O_D^\times/U_D^m|=(q^2-1)q^{2(m-1)}
\qquad(m\ge1).
$$

This elementary index will later control dimensions of induced representations.

### 4.3 Conjugation on a layer

Write a class in the $n$th layer as $1+\Pi^na$. Conjugation by $\Pi$ sends its coefficient to $\sigma(a)$:

$$
\Pi(1+\Pi^na)\Pi^{-1}
\equiv1+\Pi^n\sigma(a)\pmod{U_D^{n+1}}.
$$

If $u\in\mathcal O_L^\times$, then

$$
u(1+\Pi^na)u^{-1}
\equiv
1+\Pi^n\sigma^n(u)a u^{-1}\pmod{U_D^{n+1}}.
$$

After reduction the multiplier is $\bar u^{q^n-1}$. Thus even and odd layers behave differently. On an even layer the residue torus acts trivially; on an odd layer it acts through $\bar u^{q-1}$. Conjugation by the division uniformizer always acts by Frobenius.

### 4.4 Commutators and central intersections

For $r,s\ge1$,

$$
[U_D^r,U_D^s]\subseteq U_D^{r+s}.
$$

More precisely, if $X=\Pi^ra$ and $Y=\Pi^sb$, then

$$
[1+X,1+Y]
\equiv
1+\Pi^{r+s}
\bigl(\sigma^s(a)b-\sigma^r(b)a\bigr)
\pmod{U_D^{r+s+1}}.
$$

The formula is the first-order identity $[1+X,1+Y]\equiv1+XY-YX$. It explains when a character of one layer extends across a larger subgroup: its defining linear functional must annihilate these commutator values.

Two parity checks make the formula concrete. If $r$ and $s$ are both even, then $\sigma^r=\sigma^s=1$, and the leading coefficient is $ab-ba=0$ because $a,b\in k_D$ commute. The commutator therefore falls one layer deeper than the coarse bound predicts. If $r$ is even and $s$ is odd, the leading coefficient becomes

$$
\sigma(a)b-ba=(\sigma(a)-a)b,
$$

which, for $b\in k^\times$, ranges through the trace-zero $k$-line as $a$ varies. Thus the associated graded group is abelian, but the graded bracket between distinct layers is not zero. Treating the entire principal-unit group as abelian would lose exactly the pairing that creates positive-depth Heisenberg representations.

The center enters the filtration at twice its own rate:

$$
K^\times\cap U_D^n=U_K^{\lceil n/2\rceil},
\qquad
U_K^r=1+\mathfrak p_K^r.
$$

For example $U_K^1$ lies in $U_D^2$, not merely $U_D^1$ as a sharp equality of levels. Forgetting this doubling corrupts central conductor inequalities.

### 4.5 Characters of the layers

Fix a nontrivial additive character $\psi:K\to C^\times$ of conductor zero, meaning it is trivial on $\mathcal O_K$ but not on $\varpi^{-1}\mathcal O_K$. The reduced trace pairing

$$
(x,y)\longmapsto\psi(\operatorname{Trd}(xy))
$$

identifies suitable quotients of fractional ideals with character groups of congruence quotients. Concretely, if $\beta\in D$ has the correct negative valuation, then

$$
\psi_\beta(1+x)=\psi(\operatorname{Trd}(\beta x))
$$

defines a character on $U_D^n/U_D^m$ whenever the omitted quadratic terms land in the kernel of $\psi$. The precise inequality is checked by requiring

$$
v_K(\operatorname{Trd}(\beta xy))\ge0
$$

for $x,y\in\mathfrak P_D^n$.

The word “suitable” can be made exact. With the chosen conductor of $\psi$, the annihilator of $\mathfrak P_D^r$ is

$$
(\mathfrak P_D^r)^\perp=\mathfrak P_D^{-r-1}.
$$

For $r=0$, write $x=a+b\Pi$ and $y=c+d\Pi$. The scalar part of $xy$ is $ac+\varpi b\sigma(d)$. Requiring its field trace to be integral for every $c,d\in\mathcal O_L$ gives

$$
\mathcal O_D^\perp
=\mathcal O_L\oplus\varpi^{-1}\mathcal O_L\Pi
=\mathfrak P_D^{-1}.
$$

Multiplication by powers of $\Pi$ and cyclicity of reduced trace give the general formula. It follows that the character group of

$$
\mathfrak P_D^r/\mathfrak P_D^s\qquad(r<s)
$$

is parametrized exactly by

$$
\mathfrak P_D^{-s-1}/\mathfrak P_D^{-r-1}.
$$

Moreover $1+x\mapsto\psi(\operatorname{Trd}(\beta x))$ is multiplicative on $U_D^r$ whenever

$$
\beta\mathfrak P_D^{2r}\subseteq\mathfrak P_D^{-1};
$$

this is precisely the condition that the quadratic error $\beta xy$ be annihilated. These exact dual lattices will locate both the simple character and the first congruence subgroup in its kernel.

The parameter $\beta$ is not unique: adding the annihilator of $\mathfrak P_D^n/\mathfrak P_D^m$ gives the same character. Conjugation sends $\psi_\beta$ to $\psi_{g\beta g^{-1}}$. Thus the orbit of a filtration character is controlled by the quadratic algebra $K[\beta]$, which is the bridge to admissible pairs.

For a small worked layer, take $n=1$. A character of $U_D^1/U_D^2$ is an additive character of $k_D$. After choosing a nontrivial character $\psi_k$ of $(k,+)$, it has the form

$$
1+\Pi a\longmapsto
\psi_k\!\left(\operatorname{Tr}_{k_D/k}(c\bar a)\right)
$$

for a unique $c\in k_D$. Conjugation by $\Pi$ replaces $c$ by $c^q$. Conjugation by a residue unit $\bar u$ replaces it by $\bar u^{1-q}c$. The zero parameter gives the trivial character; every nonzero parameter has a stabilizer visible in this finite-field action. This is the first orbit calculation behind the ramified conductor-three family.

## 5. Level, conductor, and twisting

### 5.1 Three related depth measurements

Different later comparisons want slightly different integers. We define them together to prevent silent shifts.

For an irreducible $\pi$, its **congruence exponent** is

$$
c_D(\pi)=\min\{m\ge0\mid U_D^m\text{ acts trivially on }\pi\}.
$$

Here $U_D^0=\mathcal O_D^\times$. Its **nonnegative filtration level** is

$$
\ell_D(\pi)=\max\{c_D(\pi)-1,0\}.
$$

Thus unramified norm characters have exponent and filtration level zero; a genuine higher-dimensional level-zero representation is trivial on $U_D^1$ but not on $U_D^0$, so $c_D=1$ and $\ell_D=0$. In the special-packet convention one instead assigns level $-1$ to an unramified norm character. We keep the filtration level nonnegative and display the exceptional conductor explicitly, so the two conventions cannot be confused.

For a smooth character $\mu$ of $K^\times$, put $U_K^0=\mathcal O_K^\times$, $U_K^r=1+\mathfrak p_K^r$ for $r\ge1$, and

$$
a(\mu)=\min\{r\ge0\mid\mu|_{U_K^r}=1\}.
$$

This is the usual character-conductor normalization.

The norm filtration satisfies

$$
\operatorname{Nrd}(U_D^m)=U_K^{\lceil m/2\rceil}
\qquad(m\ge1).
$$

The containment follows by expanding

$$
\operatorname{Nrd}(1+x)=1+\operatorname{Trd}(x)+\operatorname{Nrd}(x),
$$

and using the valuations of reduced trace and norm on $\mathfrak P_D^m$. For the reverse containment, put $s=\lceil m/2\rceil$. Then $U_L^s\subseteq U_D^m$, and the unramified field norm maps $U_L^s$ onto $U_K^s$. Consequently, if $a(\mu)=r>0$, then

$$
c_D(\mu\circ\operatorname{Nrd})=2r-1,
\qquad
\ell_D(\mu\circ\operatorname{Nrd})=2r-2.
$$

The **transfer-facing conductor exponent** is defined by

$$
a_D(\pi)=
\begin{cases}
1,&\pi=\mu\circ\operatorname{Nrd}\text{ and }a(\mu)=0,\\
2a(\mu),&\pi=\mu\circ\operatorname{Nrd}\text{ and }a(\mu)>0,\\
\ell_D(\pi)+2,&\dim\pi>1.
\end{cases}
$$

This convention assigns conductor one to the unramified special packet and conductor two to a higher-dimensional level-zero packet. For a ramified norm character, the preceding calculation shows that $\ell_D+2=2a(\mu)$ as well. Congruence exponent alone does not see the monodromy carried by the selected special parameter, which is why its unramified member requires the exceptional clause.

### 5.2 Central conductor constraints

Let $\omega_\pi$ be the central character and let $a(\omega_\pi)$ be its usual conductor on $K^\times$. If $U_D^m$ acts trivially, then its central intersection does too. Therefore

$$
a(\omega_\pi)\le \left\lceil\frac m2\right\rceil
\qquad\text{for every }m\ge c_D(\pi),
$$

and in particular

$$
a(\omega_\pi)\le\left\lceil\frac{c_D(\pi)}2\right\rceil.
$$

This is a necessary condition, not a converse. A representation can have unramified central character while carrying highly ramified noncentral action. Level-zero examples with residue character trivial on $k^\times$ already demonstrate the failure of a converse.

### 5.3 Twists and cancellation

Every smooth twist is a norm twist. For a character $\chi$ of $K^\times$, write

$$
\pi\otimes\chi=\pi\otimes(\chi\circ\operatorname{Nrd}).
$$

Its central character is

$$
\omega_{\pi\otimes\chi}=\omega_\pi\chi^2.
$$

Unramified twists preserve $c_D$, $\ell_D$, and $a_D$. Ramified twists need not satisfy a formula involving only $a_D(\pi)$ and $a(\chi)$. Leading characters on a congruence layer can cancel. For a one-dimensional representation the exact formula is

$$a_D((\mu\circ\operatorname{Nrd})\otimes\chi)=

\begin{cases}
1,&a(\mu\chi)=0,\\
2a(\mu\chi),&a(\mu\chi)>0.
\end{cases}
$$

The right side can be smaller than both naive maxima.

For an admissible pair $(E/K,\theta)$ constructed later, twisting replaces $\theta$ by

$$
\theta(\chi\circ N_{E/K}).
$$

This gives the exact conductor after the new character is put back into minimal form.

### 5.4 Minimal twists

An irreducible representation is **twist-minimal** if no norm twist has smaller $a_D$. A character $\theta$ of a quadratic extension is minimal over $K$ if no product $\theta(\chi\circ N_{E/K})$ has smaller conductor. Minimality is the hypothesis that turns conductor bounds into equalities: it says the highest nontrivial congruence character is genuinely quadratic-field data rather than scalar norm data.

Every twist class has a minimal member because conductor exponents are nonnegative integers. It need not have a unique one. At equal depth, distinct characters can cancel in more than one way, especially in residue characteristic two. Statements below use minimality only where it is mathematically needed.

## 6. Clifford theory along the normal filtration

### 6.1 Why restriction is the classification engine

Let $N\triangleleft G$ and let $\pi$ be irreducible. Clifford theory studies $\pi$ by restricting it to $N$. In our setting $N$ can be $U_D^m$, $\mathcal O_D^\times$, or a finite quotient of either. Because irreducible representations of $D^\times$ kill some $U_D^m$, all restriction problems eventually occur in finite groups.

If $\rho$ is an irreducible constituent of $\pi|_N$, conjugation produces constituents

$$
\rho^g(n)=\rho(gng^{-1}).
$$

They form one $G$-orbit and occur with equal multiplicity. The stabilizer

$$
G_\rho=\{g\in G\mid\rho^g\cong\rho\}
$$

is the natural inducing subgroup. This is not merely a way to construct examples: applied at a level killed by $\pi$, it is exhaustive.

### 6.2 Orbit and stabilizer

Choose an irreducible $N$-submodule $W\subset V$. The sum of its conjugates is nonzero and $G$-stable, hence all of $V$. Distinct isotypic components have zero intersection, so

$$
V|_N\cong e\bigoplus_{g\in G_\rho\backslash G}\rho^g
$$

for a positive multiplicity $e$. The quotient $G/G_\rho$ is finite in all applications here. The remaining problem is to understand how the multiplicity space carries the stabilizer action.

When $N$ is abelian, $\rho$ is a character and $G_\rho$ is an ordinary character stabilizer. On a nonabelian congruence quotient, $\rho$ may be a Heisenberg representation. The orbit-stabilizer mechanism is unchanged; only the extension problem grows richer.

Equal multiplicity is not a dimension-counting accident. If $g$ carries the $\rho$-isotypic component to the $\rho^g$-isotypic component, $\pi(g)$ is an isomorphism between them. Transitivity gives the same multiplicity everywhere. Conversely, if constituents from two different orbits occurred, the sums of their isotypic components would be two nonzero proper $G$-stable subspaces. Irreducibility rules this out.

### 6.3 Extension and projective extension

Suppose $\rho^g\cong\rho$ for $g\in G_\rho$. Choose intertwiners $T_g$. They are unique only up to scalar when $\operatorname{End}_N(\rho)=C$, and their products satisfy

$$
T_gT_h=\alpha(g,h)T_{gh}
$$

for a two-cocycle $\alpha$. Thus the multiplicity space carries a projective representation with inverse cocycle $\alpha^{-1}$. An honest extension of $\rho$ to $G_\rho$ exists exactly when $\alpha$ is a coboundary.

This obstruction must not be erased from an exhaustive classification. In many tame quadratic cases the cocycle is trivial and a preferred extension can be constructed. In wild cases it may be better to retain the projective multiplicity representation as part of the parameter.

Once a compatible projective representation $\eta$ is chosen, the tensor product $\widetilde\rho\otimes\eta$ is an honest irreducible representation of $G_\rho$, and

$$
\pi\cong\operatorname{Ind}_{G_\rho}^G(\widetilde\rho\otimes\eta).
$$

The quotient is finite in our applications, so ordinary and compact induction coincide.

The standard finite Heisenberg situation illustrates why the extension can have dimension greater than one. Let $H$ be a two-step nilpotent finite quotient with center $Z_H$, and fix a character $\zeta$ of $Z_H$. The commutator induces

$$
\langle\bar x,\bar y\rangle_\zeta=\zeta([x,y])
$$

on $H/Z_H$. If this alternating pairing is nondegenerate, choose a maximal isotropic subgroup $A/Z_H$ and extend $\zeta$ to $A$. Induction from $A$ to $H$ is irreducible: an element outside $A$ moves the extension because nondegeneracy supplies a nontrivial commutator. Its dimension is

$$
[H:A]=\sqrt{[H:Z_H]}.
$$

Every irreducible with central character $\zeta$ is isomorphic to it. This uniqueness lets a quadratic torus stabilizing $\zeta$ act projectively on one canonical Heisenberg space.

### 6.4 The two-step valuation quotient

Take $N=\mathcal O_D^\times$. It is normal, and conjugation by $\Pi$ defines an automorphism

$$
\alpha(h)=\Pi h\Pi^{-1}.
$$

Since $\Pi^2=\varpi$ is central, $\alpha^2=1$. Hence an irreducible constituent $\tau$ of $\pi|_{\mathcal O_D^\times}$ has orbit of size one or two.

The size-two stabilizer is

$$
J=\langle\mathcal O_D^\times,\Pi^2\rangle,
$$

an index-two subgroup of $D^\times$. In the size-one case, extending $\tau$ requires an intertwiner $A$ satisfying

$$
A\tau(h)A^{-1}=\tau(\alpha(h)),
\qquad
A^2=\omega_\pi(\varpi).
$$

Over $C$ a nonzero intertwiner can be rescaled to meet the square relation. The two possible signs give two extensions, differing by the unramified quadratic character that is trivial on $\mathcal O_D^\times$ and sends $\Pi$ to $-1$.

## 7. An exhaustive finite-quotient classification

### 7.1 Finite data plus a uniformizer operator

The phrase “compact modulo center” is a finiteness theorem, not a classification. A precise label must record which finite quotient of $\mathcal O_D^\times$ acts and how the missing odd-valuation element $\Pi$ acts. These two pieces are exactly finite-quotient data plus a semilinear uniformizer operator.

For $m\ge1$, put

$$
H_m=\mathcal O_D^\times/U_D^m.
$$

Conjugation by $\Pi$ induces an involution $\alpha_m$ on $H_m$. Let $\tau$ be an irreducible $C$-representation of $H_m$, inflated to $\mathcal O_D^\times$. We require $m$ to be minimal when uniqueness of the level is desired, but not for the construction itself.

### 7.2 The classification theorem

**Theorem 7.1 (finite-quotient classification).** Every irreducible smooth $C$-representation of $D^\times$ is obtained uniquely up to the equivalences below from:

1. an integer $m\ge1$ and an irreducible representation $\tau$ of $H_m$;
2. the $\alpha_m$-orbit of $\tau$;
3. a scalar $c\in C^\times$ giving the action of $\Pi^2=\varpi$;
4. if the orbit has size one, an intertwiner $A:\tau\to\tau\circ\alpha_m$ with $A^2=c$; if it has size two, the extension of $\tau$ to $J=\langle\mathcal O_D^\times,\Pi^2\rangle$ on which $\Pi^2$ acts by $c$.

In the size-one case, $\Pi$ acts by $A$. In the size-two case,

$$
\pi=\operatorname{Ind}_J^{D^\times}\widetilde\tau.
$$

Two data give isomorphic representations precisely when their $\tau$'s lie in the same $\alpha_m$-orbit, their central scalars agree, and their extension data are equivalent. Representations trivial on $\mathcal O_D^\times$ are included by taking $\tau=\mathbf1$; equivalently one may allow $m=0$.

If nonminimal values of $m$ are allowed, one further identifies a datum with every inflation of it to a deeper quotient. Equivalently, require $m=c_D(\pi)$ when $c_D(\pi)\ge1$ and use $m=0$ for representations trivial on $\mathcal O_D^\times$. With this convention the word “uniquely” in the theorem has literal force.

**Proof strategy.** Kill a congruence subgroup, restrict to the normal maximal compact, and apply the two-element Clifford orbit calculation. Conversely verify the relations and irreducibility in the two cases.

**Proof.** Finite dimensionality gives $m$ with $U_D^m$ in the kernel. Choose an irreducible constituent $\tau$ of the finite-group representation on $H_m$. Section 6.4 shows that its orbit has size one or two. In the invariant case the $\tau$-isotypic space is all of $V$; Schur's lemma makes $\Pi^2$ scalar, and $\Pi$ supplies $A$. In the size-two case the two isotypic components are exchanged by $\Pi$, and one component is stable under $J$; induction reconstructs $V$.

Conversely, the invariant-case relations define a representation of the generators $\mathcal O_D^\times$ and $\Pi$. Any nonzero invariant subspace meets an irreducible $\tau$-space and is therefore all. In the orbit-two case Mackey restriction to $\mathcal O_D^\times$ is $\tau\oplus\tau^\alpha$; a nonzero invariant subspace containing either constituent contains both, proving irreducibility. The same restriction proves the isomorphism criterion. $\square$

The scalar $c$ is genuinely independent of the maximal-compact datum. Fix $\tau$ and vary $c$. The restrictions to $\mathcal O_D^\times$ remain identical, but $\varpi=\Pi^2$ acts by different scalars, so the representations are not isomorphic. After choosing a square root, they differ by an unramified twist. Finite maximal-compact data alone never remembers the full representation; the uniformizer operator is indispensable.

Minimality of $m$ can be recovered from $\pi$: it is $c_D(\pi)$ when $c_D(\pi)\ge1$. Inflating the same $\tau$ from $H_m$ to $H_{m+1}$ creates no new representation. This explains why the later wild parametrization identifies data after inflation to a common deeper quotient.

### 7.3 The invariant-orbit case

If $\tau^\alpha\cong\tau$, then

$$
\dim\pi=\dim\tau.
$$

There are exactly two extensions for each prescribed $c$ over $C$, because scaling a chosen intertwiner reduces $A^2=c$ to a choice of square root. These extensions differ by the unramified quadratic twist. A one-dimensional invariant $\tau$ need not automatically give a norm character until the commutator relations are imposed; Theorem 3.1 then forces the resulting character through reduced norm.

### 7.4 The two-element orbit case

If $\tau^\alpha\not\cong\tau$, the induced representation has

$$
\dim\pi=2\dim\tau.
$$

In the model $V=W\oplus W'$, units act by $\tau$ and $\tau^\alpha$ on the two summands, while $\Pi$ exchanges them; the return map contains the scalar $c$. This explicit matrix form makes the action variance visible and is useful for traces: every odd-valuation element exchanges the summands and therefore has trace zero.

### 7.5 Coefficients not algebraically closed

Over a general characteristic-zero field $E$, three new phenomena can occur. The endomorphism algebra of $\tau$ may be a division algebra larger than $E$; an invariant orbit may fail to possess an intertwiner whose square is the required central scalar; and a projective cocycle may split only after scalar extension. The correct parameter is then a simple module for the crossed-product algebra

$$
\operatorname{End}_{H_m}(\tau)\,{}_{\alpha,c}[T,T^{-1}],
\qquad T^2=c.
$$

Scalar extension to an algebraic closure recovers Theorem 7.1, while descent records Galois orbits and Schur indices. Characteristic zero alone does not justify silently choosing square roots.

## 8. Compact induction and intertwining

### 8.1 Compact-mod-center inducing subgroups

The finite-quotient classification is exhaustive but not always geometrically revealing. Quadratic constructions are better expressed by compact induction. Let $J\subset D^\times$ be open and contain $K^\times$, with $J/K^\times$ compact, and let $\Lambda$ be a finite-dimensional irreducible representation of $J$ with central character $\omega$.

Because $D^\times/K^\times$ is compact, $J$ has finite index. Hence

$$
\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda
=\operatorname{Ind}_J^{D^\times}\Lambda
$$

is finite dimensional, and its functions are compactly supported modulo $J$, equivalently compactly supported modulo the center. With our convention they obey

$$
f(jg)=\Lambda(j)f(g),
\qquad
(g_0f)(x)=f(xg_0).
$$

Thus

$$
\dim\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda
=[D^\times:J]\dim\Lambda.
$$

### 8.2 Irreducibility from intertwining

Define

$$
I_{D^\times}(\Lambda)=
\{g\in D^\times\mid\operatorname{Hom}_{J\cap J^g}(\Lambda,\Lambda^g)\ne0\}.
$$

If $I_{D^\times}(\Lambda)=J$ and $\operatorname{End}_J(\Lambda)=C$, then Mackey theory gives scalar endomorphisms. Here finite dimensionality supplies the semisimplicity missing from the most general compact-induction criterion: after twisting by a unitary character if necessary, the representation factors through a finite group modulo its scalar center, and averaging splits submodules. Consequently the induced representation is irreducible.

Here is the decisive semisimple step. Put $P=\operatorname{Ind}_J^{D^\times}\Lambda$ and suppose $0\ne W\subseteq P$. After imposing the fixed central character, the action is a module for a finite-dimensional twisted group algebra of the finite quotient modulo the center; it need not literally factor through a finite group when the value of $\omega(\varpi)$ has infinite order. Characteristic-zero averaging, equivalently semisimplicity of that twisted group algebra, gives a stable complement, so $P=W\oplus W'$. Projection onto $W$ is then a nontrivial idempotent in $\operatorname{End}_{D^\times}(P)$. Mackey's formula and the intertwining hypothesis identify that algebra with $\operatorname{End}_J(\Lambda)=C$, which has no nontrivial idempotent. Thus $W=P$.

In concrete quadratic constructions, the intertwining calculation has a clear purpose. A group element intertwining the first nontrivial filtration character must normalize the quadratic field cut out by its parameter. Regularity then forces that element into the prescribed inducing subgroup. This is why regular characters, rather than arbitrary torus characters, appear.

### 8.3 Isomorphism and admissibility

For arbitrary inducing data, the exact isomorphism test is the Mackey Hom formula

$$
\operatorname{Hom}_{D^\times}
\left(
\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda,
\mathrm{c\text{-}Ind}_{J'}^{D^\times}\Lambda'
\right)
\cong
\bigoplus_{x\in J'\backslash D^\times/J}
\operatorname{Hom}_{J\cap x^{-1}J'x}
(\Lambda,(\Lambda')^x),
$$

where $(\Lambda')^x(h)=\Lambda'(xhx^{-1})$. When both compact inductions are irreducible, they are isomorphic exactly when at least one summand on the right is nonzero. Conjugacy of inducing data,

$$
J'=g^{-1}Jg,
\qquad
\Lambda'\cong\Lambda^g,
$$

is a sufficient condition. It is also necessary for the level-zero and normalized tame data below, where the leading filtration character recovers the embedded torus and its character up to the stated Galois action. It is not a formal consequence of the two separate self-intertwining equalities $I_{D^\times}(\Lambda)=J$ and $I_{D^\times}(\Lambda')=J'$: those conditions control self-intertwiners, whereas the displayed Mackey sum contains mutual intertwiners. Keeping the exact Hom criterion prevents a false uniqueness claim for general compact types.

Admissibility is immediate either from finite dimensionality or directly: for compact open $H$, Mackey theory expresses fixed vectors as a finite sum of finite-dimensional Hom spaces. The direct proof records their exact dimensions and will be used in Chapter 13.

### 8.4 The induced character formula

Because the index is finite, the ordinary matrix character is defined at every element. Choose representatives $X$ for $J\backslash D^\times$. Then

$$
\Theta_\pi(g)=
\sum_{\substack{x\in X\\xgx^{-1}\in J}}
\operatorname{tr}\Lambda(xgx^{-1}).
$$

There is no integral and no modular factor: the sum is the trace of $g$ on a finite induced module. Changing representatives merely conjugates terms inside $J$. If no conjugate of $g$ belongs to $J$, the character value is zero. This vanishing is often the fastest way to recognize an induced representation on regular elements.

## 9. Level zero from the residue field

### 9.1 Regular residue-field characters

The first nonabelian representations occur before any principal unit is visible. Reduction identifies

$$
\mathcal O_D^\times/U_D^1\cong k_D^\times,
$$

and conjugation by $\Pi$ acts by $x\mapsto x^q$. A character

$$
\bar\theta:k_D^\times\to C^\times
$$

is **regular** if

$$
\bar\theta^q\ne\bar\theta,
\qquad
\bar\theta^q(x)=\bar\theta(x^q).
$$

Equivalently, $\bar\theta$ does not factor through the finite norm $k_D^\times\to k^\times$. These are the cuspidal finite-field character data: Frobenius has a two-element orbit, so the datum cannot descend to the center's residue field.

Choose a character $\theta:L^\times\to C^\times$ trivial on $U_L^1$ whose restriction to $\mathcal O_L^\times$ reduces to $\bar\theta$. Its value on $\varpi$ is free and fixes the eventual central scalar. Put

$$
J=L^\times U_D^1.
$$

Because $L^\times\cap U_D^1=U_L^1$, the formula

$$
\Lambda_\theta(lu)=\theta(l)
\qquad(l\in L^\times,u\in U_D^1)
$$

is a well-defined character of $J$.

### 9.2 The construction and its irreducibility

Define

$$
\pi_\theta=\mathrm{c\text{-}Ind}_{L^\times U_D^1}^{D^\times}\Lambda_\theta.
$$

The subgroup has index two. Indeed its units surject onto $k_D^\times$, while its valuations are even; multiplication by $\Pi$ supplies the other coset. The restriction to $\mathcal O_D^\times$ is

$$
\pi_\theta|_{\mathcal O_D^\times}
\cong\bar\theta\oplus\bar\theta^q,
$$

with both characters inflated from $k_D^\times$.

Regularity makes these summands distinct. Clifford theory therefore proves irreducibility. It also gives the isomorphism criterion

$$
\pi_\theta\cong\pi_{\theta'}
\quad\Longleftrightarrow\quad
\theta'=\theta\text{ or }\theta^\sigma,
$$

provided the values on $K^\times$ agree as included in the equality. Thus parameters occur in Galois pairs.

### 9.3 Dimensions, centers, and characters

The basic invariants are

$$
\dim\pi_\theta=2,
\qquad
c_D(\pi_\theta)=1,
\qquad
\ell_D(\pi_\theta)=0,
\qquad
a_D(\pi_\theta)=2.
$$

Since $K^\times\subset J$, its central character is

$$
\omega_{\pi_\theta}=\theta|_{K^\times}.
$$

This is the direct normalization of the inducing character. In the quadratic-induction normalization of Section 10.7, the same parameter label gives central character $\theta|_{K^\times}\omega_{L/K}$.

For a unit $u\in\mathcal O_D^\times$ whose residue generates $k_D$ over $k$, the character is

$$
\Theta_{\pi_\theta}(u)
=\bar\theta(\bar u)+\bar\theta(\bar u^q).
$$

For an element of odd $D$-valuation, the character is zero because it exchanges the two Clifford summands. For $z\in K^\times$ it is, as always,

$$
\Theta_{\pi_\theta}(z)=2\omega_{\pi_\theta}(z).
$$

These three values already display the pattern needed for later regular-character comparisons: a Galois sum on an unramified torus, vanishing on the other valuation coset, and dimension times the central scalar at the center.

### 9.4 Irregular characters as a counterexample

Suppose $\bar\theta^q=\bar\theta$. Then $\bar\theta=\bar\mu\circ N_{k_D/k}$ for a character $\bar\mu$ of $k^\times$. The induced representation from $J$ is no longer irreducible. The residue character is fixed by $\Pi$, so it has two extensions to $D^\times$ after the value of $\Pi^2$ is fixed. Both are one dimensional and, by Theorem 3.1, are reduced-norm characters.

Thus omitting regularity does not create a new level-zero family; it produces a reducible sum of characters. This is the finite-field shadow of the intertwining criterion.

## 10. Positive depth and tame admissible pairs

### 10.1 Why quadratic tori reappear

A character on a deep congruence quotient is represented through the trace pairing by an element $\beta\in D$. If $\beta$ is noncentral, then $E=K[\beta]$ is a quadratic field embedded in $D$. Its multiplicative group stabilizes the leading character. Thus quadratic extensions do not enter as an imported parametrization: they are forced by the stabilizers of the first nontrivial filtration character.

Both quadratic types occur. The field $E/K$ may be unramified, in which case its residue field is $k_D$, or ramified, in which case its residue field is $k$. Every quadratic field extension embeds in the quaternion division algebra. We write $\sigma$ for its nontrivial automorphism, $e(E/K)$ and $f(E/K)$ for its ramification index and residue degree, and

$$
\Delta(E/K)=v_K(\operatorname{disc}(E/K))
$$

for its discriminant exponent.

### 10.2 Regularity and minimality

A smooth character $\theta:E^\times\to C^\times$ is **regular** if

$$
\theta\ne\theta^\sigma.
$$

Write $U_E^0=\mathcal O_E^\times$ and $U_E^n=1+\mathfrak p_E^n$ for $n\ge1$, and normalize the character conductor by

$$
a_E(\theta)=\min\{n\ge0\mid\theta|_{U_E^n}=1\}.
$$

Thus an unramified character has conductor zero, while a nontrivial residue-field character has conductor one. For quadratic extensions, regularity is equivalent to saying that $\theta$ does not factor through $N_{E/K}$. A pair $(E,\theta)$ is **admissible** if it is regular and also satisfies

$$
\theta/\theta^\sigma\text{ trivial on }U_E^1
\quad\Longrightarrow\quad
E/K\text{ unramified}.
$$

The second condition is essential for a ramified torus. A character whose asymmetry occurs only in residue or valuation data has extra intertwining from the nontrivial normalizer coset, so the positive-depth compact induction below is not irreducible. An admissible character is **$K$-minimal** if

$$
a_E(\theta)\le
a_E(\theta(\chi\circ N_{E/K}))
$$

for every character $\chi$ of $K^\times$. Every tame admissible pair can be put in minimal form: whenever the last unit-layer character comes from the first-order norm, lift the corresponding character of $K^\times$ and cancel it. The conductor strictly decreases, so the process terminates.

At level zero for unramified $E$, regularity is exactly the residue-field condition of Chapter 9. For a tamely ramified quadratic extension, admissibility forces genuine asymmetry on $U_E^1$. On

$$
U_E^r/U_E^{r+1}\cong(k,+),
$$

conjugation by $\sigma$ acts as multiplication by $(-1)^r$: choose a uniformizer $\varpi_E$ with $\sigma(\varpi_E)=-\varpi_E$. If $n=a_E(\theta)$ is the conductor of a minimal admissible character, its last nontrivial layer has index $r=n-1$ and must be moved by $\sigma$. Hence $n-1$ is odd, so $n$ is even and at least two. This parity is what makes the ramified conductor below odd.

### 10.3 The inducing subgroup and its extension

Let $(E,\theta)$ be minimal and put $n=a_E(\theta)>0$. When $E/K$ is unramified and $n=1$, this is exactly the residue-field construction of Chapter 9. Assume now that $n\ge2$. The restriction of $\theta$ to its last nontrivial principal-unit layer is represented by a trace character $\psi_\beta$ with $K[\beta]=E$. From $\psi_\beta$ one constructs an irreducible representation $\eta_\beta$ of a finite quotient of a principal-unit subgroup. If the relevant quotient is abelian, $\eta_\beta$ is itself a character. If it is two-step nilpotent, the commutator formula of Section 4.4 gives a nondegenerate alternating pairing and $\eta_\beta$ is its unique Heisenberg representation with the prescribed central character.

We now give the construction rather than using that summary as a black box. Let

$$
d_E=v_E(\mathfrak D_{E/K})
$$

be the different exponent. Trace duality on $E$ gives a leading element $\beta\in E$ satisfying

$$
v_E(\beta)=-n-d_E
$$

and

$$
\theta(1+x)=\psi(\operatorname{Tr}_{E/K}(\beta x))
$$

on the deep half of the unit filtration. Minimality makes the class of $\beta$ noncentral at the decisive precision: if it were scalar modulo the trace annihilator, its character would factor through the first-order norm and a norm twist would lower $n$. Thus $K[\beta]=E$.

In the tame quadratic range the subgroup can be stated explicitly. Put

$$
r_\theta=
\begin{cases}
n-1,&E/K\text{ unramified},\\
n/2,&E/K\text{ tamely ramified}.
\end{cases}
$$

For the unramified level-zero case $n=1$, the notation $E^\times U_D^0$ and $E^\times U_D^1$ gives the same subgroup, since $\mathcal O_E^\times$ already surjects onto $k_D^\times$; the inducing character is the one constructed in Chapter 9. For $n\ge2$, the torus $E^\times$ normalizes the finite representation built from $\psi_\beta$, and combining that representation with $\theta$ produces $\Lambda_\theta$. In both cases the inducing representation lives on the open compact-mod-center subgroup

$$
J_\theta=E^\times U_D^{r_\theta}.
$$

There are two constructions, and their parity difference explains the dimension formula.

If $E/K$ is unramified, put

$$
J^1=U_E^1U_D^{n-1},
\qquad
H^1=U_E^1U_D^n.
$$

On $H^1$ define

$$
\vartheta_\beta(u(1+x))
=\theta(u)\psi(\operatorname{Trd}(\beta x)),
\qquad
u\in U_E^1,\quad x\in\mathfrak P_D^n.
$$

The two factors agree on their intersection by the trace formula for $\theta$. Since $v_D(\beta)=-2n$, the quadratic error satisfies

$$
\beta\mathfrak P_D^{2n}\subseteq\mathcal O_D\subseteq\mathfrak P_D^{-1},
$$

so the formula is multiplicative and independent of the chosen factorization. If $n$ is odd, the even layer $\mathfrak P_D^{n-1}/\mathfrak P_D^n$ is already filled by $U_E^1$, and $J^1=H^1$. Then $\eta_\beta=\vartheta_\beta$ is one dimensional. If $n$ is even, then

$$
J^1/H^1\cong\mathfrak P_D^{n-1}/\mathfrak P_D^n
$$

has order $q^2$. The rule

$$
\langle\bar x,\bar y\rangle_\beta
=\vartheta_\beta([x,y])
$$

is alternating and nondegenerate. Indeed a radical class commutes with $\beta$ on the associated graded; the centralizer of the noncentral element $\beta$ is $E$, and the $E$-classes have already been absorbed into $H^1$. Choose a maximal isotropic subgroup, extend $\vartheta_\beta$ to it, and induce to $J^1$. Mackey's criterion and nondegeneracy prove that the result $\eta_\beta$ is irreducible, independent of the polarization, and has dimension $q$.

If $E/K$ is tamely ramified, admissibility gives $n=2s$. Put

$$
J^1=U_E^1U_D^s,
\qquad
J_\theta=E^\times J^1=E^\times U_D^s.
$$

Now $d_E=1$ and $v_D(\beta)=-2s-1$. The direct formula

$$
\Lambda_\theta(e(1+x))
=\theta(e)\psi(\operatorname{Trd}(\beta x)),
\qquad
e\in E^\times,\quad x\in\mathfrak P_D^s,
$$

defines a character of $E^\times U_D^s$. Agreement on $E^\times\cap U_D^s=U_E^s$ is the deep trace formula, and

$$
\beta\mathfrak P_D^{2s}\subseteq\mathfrak P_D^{-1}
$$

annihilates the quadratic error. Thus no Heisenberg enlargement is needed in this parity.

It remains in the unramified case to extend $\eta_\beta$ from $J^1$ to $J_\theta=E^\times J^1$. Uniqueness of the Heisenberg representation makes the $E^\times$-action projective. After the prescribed action of $K^\times U_E^1$ is removed, the nontrivial quotient is the cyclic group $k_E^\times/k^\times$. A projective representation of a cyclic group is linearized by rescaling an operator for one generator to satisfy its power relation. Requiring that restriction to $E^\times$ contain the $\theta$-isotypic line, and that $K^\times$ act through $\theta|_{K^\times}$, removes the remaining character ambiguity. This produces $\Lambda_\theta$.

At positive depth $\Lambda_\theta|_{E^\times}$ need not be scalar when the Heisenberg space has dimension $q$; what is canonical is its multiplicity-one $\theta$-line and its scalar action on the center. This distinction is indispensable in later character and toric-functional formulas. A **normalized tame admissible datum** consists of $(E,\theta)$ together with this compatible extension class $[\Lambda_\theta]$. The construction just given selects the class once the tame normalization is fixed. For such a datum,

$$
\dim\Lambda_\theta=
\begin{cases}
1,&E/K\text{ unramified and }n\text{ odd},\\
q,&E/K\text{ unramified and }n\text{ even},\\
1,&E/K\text{ tamely ramified}.
\end{cases}
$$

The middle case is the Heisenberg step. Define

$$
\pi(E,\theta)=\mathrm{c\text{-}Ind}_{J_\theta}^{D^\times}\Lambda_\theta.
$$

Admissibility forces $I_{D^\times}(\Lambda_\theta)=J_\theta$, so this representation is irreducible.

For a nonminimal tame admissible pair, choose

$$
\theta=\theta_0(\chi\circ N_{E/K})
$$

with $\theta_0$ minimal, and define

$$
\pi(E,\theta)
=\pi(E,\theta_0)\otimes(\chi\circ\operatorname{Nrd}).
$$

Two minimal decompositions give isomorphic results because their quotient is itself a norm pullback and twisting the inducing action by reduced norm changes its torus line by precisely that pullback. Thus the construction is independent of the chosen minimization.

The intertwining proof has three steps. First, an intertwiner of $\Lambda_\theta$ must intertwine its restriction to the last nontrivial congruence layer. Exact trace duality translates this into

$$
g^{-1}\beta g\equiv\beta
$$

modulo the dual error lattice at that layer. Second, improve this approximate centralizing statement one layer at a time. On every associated graded quotient, the kernel of

$$
\operatorname{ad}(\beta):x\longmapsto\beta x-x\beta
$$

is the image of $E=C_D(\beta)$; on a complementary $k$-line the map is invertible in the tame range. If $g$ normalizes $E$ modulo $\mathfrak P_D^t$, solve the resulting linear commutator equation for $h\in\mathfrak P_D^t$ and replace $g$ by $g(1+h)$. This improves the congruence by one layer. Completeness and the finite depth of the type eventually put $g$, modulo $J^1$, in $N_{D^\times}(E^\times)$.

Third, the normalizer quotient has order two. Its nontrivial coset replaces $\theta$ by $\theta^\sigma$. At depth zero regularity distinguishes the two residue characters; at positive depth the second admissibility condition ensures that their difference is visible on $U_E^1$. Hence this coset does not intertwine. After removing an element of $E^\times$, any remaining first graded class outside $J^1$ pairs nontrivially with a complementary class under $\langle\ ,\ \rangle_\beta$, again contradicting intertwining. Descending through the remaining finite layers forces the error into $J^1$. What remains is exactly $J_\theta$.

This also explains all three hypotheses. Without minimality, the leading parameter can be central modulo the relevant dual lattice, so the field is not detected at the claimed depth. Without regularity, the Galois-normalizer coset intertwines. For a ramified torus, regularity visible only outside $U_E^1$ is still insufficient, which is exactly why admissibility has its second clause. In either failure the endomorphism algebra enlarges and the induced representation is reducible.

The same leading-character argument gives the isomorphism criterion. For normalized minimal tame data,

$$
\pi(E,\theta)\cong\pi(E',\theta')
$$

if and only if some $g\in D^\times$ carries $E$ to $E'$ and carries the normalized inducing representation for $\theta$ to that for $\theta'$. After identifying the two fields, this says

$$
\theta'=\theta
\qquad\text{or}\qquad
\theta'=\theta^\sigma.
$$

The projective splitting is part of the phrase “normalized inducing representation.” If one works with an unnormalized raw extension, the last criterion must include that extension class as additional data.

### 10.4 Dimension and central character

The general dimension formula is exact and convention-free:

$$
\dim\pi(E,\theta)
=[D^\times:J_\theta]\dim\Lambda_\theta.
$$

For reference, the elementary toral-congruence indices are

$$
[D^\times:E^\times U_D^r]
=2q^{2\lfloor r/2\rfloor}
\quad(E/K\text{ unramified}),
$$

and

$$
[D^\times:E^\times U_D^r]
=(q+1)q^{r-1}
\quad(E/K\text{ ramified}),
$$

for $r\ge1$. These follow by dividing the order of $\mathcal O_D^\times/U_D^r$ by the image of $\mathcal O_E^\times$ and, in the unramified case, adding the missing odd valuation coset. Substitution now proves the advertised dimensions, including their parity. If $E/K$ is unramified and $n$ is odd, then $r=n-1$ is even, the index is $2q^{n-1}$, and $\Lambda_\theta$ has dimension one. If $n$ is even, the index is $2q^{n-2}$ and the Heisenberg representation has dimension $q$. If $E/K$ is ramified, then $r=n/2$ and the index is $(q+1)q^{n/2-1}$, while the inducing type is a character.

For a minimal tame admissible pair the result simplifies to

$$
\dim\pi(E,\theta)=
\begin{cases}
2q^{n-1},&E/K\text{ unramified},\\
(q+1)q^{(n-2)/2},&E/K\text{ tamely ramified}.
\end{cases}
$$

The second exponent is integral because minimal tame ramified admissible characters have even $n$. In every case

$$
\omega_{\pi(E,\theta)}=\theta|_{K^\times},
$$

since the center lies in the inducing subgroup and acts there through $\theta$. This is again the direct normalization; Section 10.7 inserts the rectifier for the selected quadratic-induction label.

### 10.5 Conductor formulas

The minimal admissible-pair conductor formula is

$$
a_D(\pi(E,\theta))
=\Delta(E/K)+f(E/K)a_E(\theta).
$$

Thus

$$
a_D(\pi(E,\theta))=
\begin{cases}
2n,&E/K\text{ unramified},\\
n+1,&E/K\text{ tamely ramified}.
\end{cases}
$$

For these higher-dimensional representations,

$$
c_D(\pi)=a_D(\pi)-1,
\qquad
\ell_D(\pi)=a_D(\pi)-2.
$$

The formula follows directly from the exact dual lattice in Section 4.5. In the unramified case $v_D(\beta)=-2n$. Hence

$$
\beta\mathfrak P_D^{2n-1}\subseteq\mathfrak P_D^{-1},
$$

so $U_D^{2n-1}$ is killed, whereas the class of $\beta$ in

$$
\mathfrak P_D^{-2n}/\mathfrak P_D^{-2n+1}
$$

pairs nontrivially with $\mathfrak P_D^{2n-2}/\mathfrak P_D^{2n-1}$. Thus $U_D^{2n-2}$ is not killed. In the tame ramified case, $d_E=1$, $v_D(\beta)=-n-1$, and the identical calculation shows triviality on $U_D^n$ and nontriviality on $U_D^{n-1}$. These are exactly the two instances of

$$
c_D(\pi)=\Delta(E/K)+f(E/K)n-1.
$$

The discriminant term is the inverse-different displacement, and the factor $f(E/K)$ counts the $K$-length of an $E$-unit layer. The Heisenberg enlargement creates no extra shift: its central character is precisely the simple character just tested. The displayed conductor formula now follows from $a_D=c_D+1$ for higher-dimensional representations. Minimality is exactly what prevents the leading functional from becoming central and being removed by a norm twist.

For a nonminimal pair one must first minimize, or use the exact twisted expression

$$
a_D(\pi(E,\theta)\otimes\chi)
=\Delta(E/K)+f(E/K)
a_E\bigl(\theta(\chi\circ N_{E/K})\bigr)
$$

after putting the twisted pair in admissible normalization. There is no unconditional maximum formula at equal depth.

### 10.6 The tame ramified and unramified shapes

The two tame families can be recognized just from conductor parity and dimension. If $E/K$ is unramified and $n\ge1$, then

$$
a_D=2n,
\qquad
\dim\pi=2q^{n-1}.
$$

If $E/K$ is tamely ramified and $n\ge2$ is even, then

$$
a_D=n+1,
\qquad
\dim\pi=(q+1)q^{(n-2)/2}.
$$

Consequently, for a tame primitive representation of conductor $a\ge2$,

$$
\dim\pi=
\begin{cases}
2q^{(a-2)/2},&a\text{ even},\\
(q+1)q^{(a-3)/2},&a\text{ odd}.
\end{cases}
$$

This parity diagnostic is useful but not a universal classification in residue characteristic two: wild quadratic extensions have larger discriminant exponent, and nonquadratic filtration data can share the same numerical invariants.

### 10.7 Direct and quadratic-induction normalizations

There are two honest ways to name the torus character, and confusing them changes the central character. In the **direct normalization** used in the construction above, the inducing type contains the stated $\theta$-isotypic line on $E^\times$ and the center acts by $\theta|_{K^\times}$. At depth zero the whole type is one dimensional and literally restricts to $\theta$; in a positive-depth Heisenberg case scalar restriction would be false. We write the result as

$$
\pi_D^{\mathrm{dir}}(E,\theta),
\qquad
\omega_{\pi_D^{\mathrm{dir}}}=\theta|_{K^\times}.
$$

The selected quadratic-induction representation on the split group is naturally labelled by a character whose induced two-dimensional parameter has determinant

$$
\theta|_{K^\times}\omega_{E/K},
$$

where $\omega_{E/K}$ is the quadratic character of $K^\times$ attached to $E/K$. To use the same symbol $\theta$ on both sides, use the tame rectifying character

$$
\Delta_{E/K,\theta}:E^\times\longrightarrow C^\times
$$

constructed from the normalized finite Gauss sum of the admissible pair. Its relevant properties, proved in the tame quadratic theory, are

$$
\Delta_{E/K,\theta}|_{K^\times}=\omega_{E/K},
$$

$$
\Delta_{E/K,\theta^\sigma}
=\Delta_{E/K,\theta}^\sigma,
\qquad
\Delta_{E/K,\theta(\chi\circ N_{E/K})}
=\Delta_{E/K,\theta},
\qquad
\Delta_{E/K,\theta^{-1}}
=\Delta_{E/K,\theta}^{-1}.
$$

Put $\theta^\natural=\theta\Delta_{E/K,\theta}$ and define the **quadratic-induction normalization** by

$$
\pi_D(E,\theta)=\pi_D^{\mathrm{dir}}(E,\theta^\natural).
$$

In the unramified case the rectifier is the fixed unramified character whose value on a common uniformizer is $-1$. In the tamely ramified case it has conductor at most one and genuinely depends on $\theta$: the normalized quadratic Gauss sum selects one of the two extensions with the required central restriction. Suppressing this dependence can reverse a Gauss phase and breaks the inversion formula above. Since a ramified admissible character has conductor at least two, the rectifier does not change any conductor formula in the selected tame range. It does change the central-character formula to

$$
\omega_{\pi_D(E,\theta)}
=\theta|_{K^\times}\omega_{E/K}.
$$

This is not a cosmetic convention. If one writes $\theta|_{K^\times}\omega_{E/K}$ while the center of the inducing type actually acts through $\theta|_{K^\times}$, one has asserted two incompatible central actions. Direct normalization is best for constructing and evaluating the type; quadratic-induction normalization is best for placing it beside the selected split representation. We will display both whenever the distinction matters.

The displayed identities give coherence under conjugation, norm twists, and duality. In particular,

$$
\pi_D(E,\theta)\otimes(\chi\circ\operatorname{Nrd})
\cong
\pi_D(E,\theta(\chi\circ N_{E/K})),
$$

and the right-hand central character changes by $\chi^2$, exactly as the left-hand side does. At depth zero, the rectifier places the Frobenius orbit in the chosen parameter normalization. At positive depth, it aligns the one-dimensional torus phase after the two Heisenberg models have been fixed. Establishing the inner-form sign and the full character identity belongs to local transfer; choosing the normalization does not assume that theorem.

## 11. The wild range and abstract exhaustivity

### 11.1 What tame pairs do not cover

The selected quadratic range has an exact boundary. It contains every norm character; every regular depth-zero packet from the unramified quadratic field; and every positive-depth packet whose minimal first noncentral stratum has a tame quadratic centralizer. Thus for odd residue characteristic both ramification types of quadratic field occur. In residue characteristic two, the quadratic part retained here is the unramified type. Ramified quadratic fields are wild and are not put into the tame formulas.

Outside this boundary lie two phenomena. First, in residue characteristic two a ramified quadratic extension has a larger and extension-dependent discriminant shift, and the stabilizer extension need not be the tame one used above. Second, a primitive wild representation can have a first noncentral leading stratum not recovered from any tame quadratic character. Such a representation may still contain Heisenberg data, but its filtration jumps and projective extension are not determined by the pair $(E,\theta)$ used in Chapter 10.

It would therefore be false to claim that the elementary tame admissible pairs label every irreducible in all residue characteristics. None of the tame dimension, parity, rectifier, type-line, or integral-reduction assertions is extended to the primitive wild range. What remains true for all irreducibles is the abstract finite, exhaustive parametrization below. It proves that the omitted range is bounded by explicit finite data at each congruence exponent, without pretending to give those data a tame quadratic name.

### 11.2 An exhaustive Clifford parameter

For $m\ge1$, let

$$
G_m=D^\times/U_D^m.
$$

Although $G_m$ is infinite because the center has unbounded valuation, its quotient by the image of $K^\times$ is finite. Fix a central character $\omega$ trivial on $K^\times\cap U_D^m$ and impose the relations $z=\omega(z)$ in the group algebra. The resulting central-character algebra

$$
\mathcal A_{m,\omega}
=C[G_m]/\langle z-\omega(z)\mid z\in K^\times\rangle
$$

is finite dimensional and semisimple.

**Theorem 11.1 (abstract exhaustive parametrization).** Irreducible smooth representations of $D^\times$ with central character $\omega$ are exactly the simple modules of $\mathcal A_{m,\omega}$ as $m$ varies, with two modules identified when inflation to a common deeper quotient is isomorphic. Equivalently, they are the Clifford data

$$
(m,\rho,G_\rho,[\alpha],\eta),
$$

where $\rho$ is an irreducible constituent on a chosen normal congruence quotient, $G_\rho$ is its stabilizer, $[\alpha]$ is the intertwiner cocycle, and $\eta$ is an irreducible projective representation with inverse cocycle and the prescribed central action.

**Proof.** Every irreducible kills some $U_D^m$ by finite dimensionality and therefore yields a simple module of the displayed finite-dimensional algebra. Conversely such a module inflates to a smooth irreducible representation. Passing to a deeper $m$ only inflates the same module. Ordinary finite-group Clifford theory, applied after the central character relations make the quotient finite, gives the equivalent orbit-stabilizer parameter. $\square$

The finite-dimensional assertion is explicit. Choose valuation representatives $1,\Pi$. Modulo the center and $U_D^m$, every element has a representative in

$$
(\mathcal O_D^\times/U_D^m)
\sqcup
\Pi(\mathcal O_D^\times/U_D^m),
$$

a set of size at most $2(q^2-1)q^{2(m-1)}$. Central powers reduce to scalars through $\omega$, so these representatives span $\mathcal A_{m,\omega}$. Characteristic-zero averaging makes the resulting finite twisted group algebra semisimple. The theorem is therefore an effective finite problem at each depth, not merely a set-theoretic label.

This theorem is exhaustive in the wild range without pretending that every cocycle, stabilizer, or Heisenberg representation has a uniform elementary name.

### 11.3 How projective data enter

The cocycle $[\alpha]$ is not decorative. Suppose a filtration representation $\rho$ is stabilized by two elements $g,h$. Choosing intertwiners separately does not ensure that the intertwiner for $gh$ is their product. The scalar discrepancy is precisely $\alpha(g,h)$. A multiplicity representation with cocycle $\alpha^{-1}$ cancels it so that the tensor product carries an honest stabilizer action.

In cyclic quotient cases over $C$, cocycles can often be removed by rescaling one operator. For larger stabilizers the obstruction may persist at an intermediate step even though the final representation exists. Recording $[\alpha]$ makes the parametrization invariant under all choices and valid over nonclosed coefficient fields after replacing scalars by the appropriate endomorphism division algebra.

## 12. Duality, twists, and matrix characters

### 12.1 Contragredients and pairings

Every irreducible representation here is finite dimensional, so its smooth contragredient is its full algebraic dual:

$$
(g\lambda)(v)=\lambda(g^{-1}v).
$$

It is irreducible, has central character $\omega_\pi^{-1}$, and satisfies $(\pi^\vee)^\vee\cong\pi$. For compact induction of finite index,

$$
(\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda)^\vee
\cong
\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda^\vee.
$$

No modular character appears because both $D^\times$ and its open subgroups are unimodular and the index is finite. Consequently

$$
\pi(E,\theta)^\vee\cong\pi(E,\theta^{-1}),
$$

with the dual extension understood, and

$$
(\mu\circ\operatorname{Nrd})^\vee
=\mu^{-1}\circ\operatorname{Nrd}.
$$

An invariant pairing $\pi\times\pi^\vee\to C$ is evaluation. A bilinear self-duality pairing on $\pi$ exists precisely when $\pi\cong\pi^\vee$; its symmetry type is extra information not determined by the central character alone.

### 12.2 Twisting inducing data

Norm twisting commutes with compact induction:

$$
(\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda)\otimes\chi
\cong
\mathrm{c\text{-}Ind}_J^{D^\times}
(\Lambda\otimes(\chi\circ\operatorname{Nrd})|_J).
$$

For a quadratic torus, reduced norm restricts to the field norm. Therefore

$$
\pi(E,\theta)\otimes\chi
\cong
\pi(E,\theta(\chi\circ N_{E/K})).
$$

This formula simultaneously explains the central-character square, conductor cancellation, preservation of the quadratic field, and compatibility of contragredience with twisting.

### 12.3 Regular elements and conjugacy

An element $g\in D^\times$ is **regular semisimple** if its reduced characteristic polynomial has distinct roots. Such an element is noncentral, and

$$
K[g]
$$

is a separable quadratic field in $D$. Its centralizer is exactly $K[g]^\times$. Two regular semisimple elements are conjugate in $D^\times$ precisely when their reduced characteristic polynomials agree, equivalently when they have the same reduced trace and reduced norm. The forward implication is immediate; the reverse follows by identifying the two quadratic fields through the common polynomial and conjugating their embeddings in $D$.

If the residue characteristic is not two, every noncentral element is regular semisimple. In characteristic two a quaternion division algebra can contain inseparable quadratic subfields, so “noncentral” and “regular semisimple” must not be identified. The word regular also excludes central elements because their centralizer is all of $D^\times$. Near a regular semisimple element, the ordinary finite-dimensional trace $\Theta_\pi(g)$ is already the locally constant matrix-character function. No distributional regularization is needed for $D^\times$.

### 12.4 Character values from inducing data

For $\pi=\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda$, Section 8.4 gives

$$
\Theta_\pi(g)=
\sum_{\substack{x\in J\backslash D^\times\\xgx^{-1}\in J}}
\operatorname{tr}\Lambda(xgx^{-1}).
$$

For a quadratic pair and a sufficiently regular element $t\in E^\times$ whose conjugates meeting $J$ are represented by $1$ and an element inducing $\sigma$, this becomes

$$
\Theta_{\pi(E,\theta)}(t)
=\operatorname{tr}\Lambda_\theta(t)
+\operatorname{tr}\Lambda_\theta(\sigma(t)).
$$

When $\Lambda_\theta$ is one dimensional on these torus elements, the value is $\theta(t)+\theta(\sigma(t))$. At positive depth the Heisenberg factor can contribute a known scalar trace; replacing it blindly by one would be wrong. Elements whose conjugacy class misses $J$ have character zero. Central elements satisfy

$$
\Theta_\pi(z)=\dim(\pi)\omega_\pi(z).
$$

These formulas, not an assertion of correspondence, are the character data handed to the next book.

## 13. Compact-open invariants

### 13.1 Maximal-order invariants

Because $\mathcal O_D^\times$ is normal in $D^\times$, the subspace $\pi^{\mathcal O_D^\times}$ of an irreducible representation is either zero or all of $\pi$. If it is all, the action factors through

$$
D^\times/\mathcal O_D^\times\cong\mathbf Z,
$$

so irreducibility makes $\pi$ a one-dimensional unramified norm character. Therefore

$$
\dim\pi^{\mathcal O_D^\times}=
\begin{cases}
1,&\pi\text{ is an unramified norm character},\\
0,&\text{otherwise}.
\end{cases}
$$

This is unlike the hyperspecial fixed line for a matrix group: no higher-dimensional spherical representation exists on the division side.

For principal congruence groups normality gives an equally sharp answer:

$$
\dim\pi^{U_D^m}=
\begin{cases}
0,&m<c_D(\pi),\\
\dim\pi,&m\ge c_D(\pi).
\end{cases}
$$

There is no oldvector growth because these subgroups are normal.

### 13.2 Eichler-like compact opens

A division algebra has a unique maximal order, so intersections of conjugate maximal orders do not produce a nontrivial local Eichler chain. The useful analogues keep a smaller central or toral residue group while varying the principal depth. Two families are

$$
H_r=\mathcal O_K^\times U_D^r
$$

and, for an embedded quadratic field $E$,

$$
H(E,r)=\mathcal O_E^\times U_D^r.
$$

They are compact open. The first remembers only central residue units; the second remembers a chosen torus. Calling them Eichler-like records their role in level structures, not an assertion that they are unit groups of intersections of distinct maximal orders.

### 13.3 A finite Mackey formula

Let $\pi=\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda$ and let $H$ be compact open. Mackey theory and Frobenius reciprocity give the directly computable formula

$$
\dim\pi^H
=\sum_{x\in J\backslash D^\times/H}
\dim\operatorname{Hom}_{J\cap xHx^{-1}}
(\Lambda,\mathbf1).
$$

The double-coset set is finite. Notice the conjugation direction: our induced functions are left $J$-covariant and acted on by right translation, so the stabilizer inside $J$ is $J\cap xHx^{-1}$. Replacing it by $J\cap x^{-1}Hx$ without simultaneously replacing representatives changes the formula.

There is also the character average

$$
\dim\pi^H
=\frac1{\operatorname{vol}(H)}
\int_H\Theta_\pi(h)\,dh.
$$

It is a finite sum after passing to a congruence quotient. These formulas are more informative than a blanket admissibility statement.

As a consistency check, take $H=U_D^m$, which is normal. If $m<c_D(\pi)$, normality gives $\pi^{U_D^m}=0$, so every nonnegative Hom summand in the Mackey formula vanishes. If $m\ge c_D(\pi)$, the whole representation is fixed and the sum equals $\dim\pi$. Thus the finite Mackey formula recovers the all-or-nothing invariant calculation of Section 13.1.

### 13.4 Level-zero invariant dimensions

Let $\pi_\theta$ be regular level zero. Since $U_D^1$ acts trivially,

$$
\dim\pi_\theta^{U_D^r}=2\qquad(r\ge1).
$$

On $H_r=\mathcal O_K^\times U_D^r$ with $r\ge1$, both Clifford summands restrict to the same character $\bar\theta|_{k^\times}$. Hence

$$
\dim\pi_\theta^{H_r}=
\begin{cases}
2,&\bar\theta|_{k^\times}=1,\\
0,&\bar\theta|_{k^\times}\ne1.
\end{cases}
$$

Meanwhile $H(L,1)=\mathcal O_D^\times$, because $\mathcal O_L^\times$ surjects onto $k_D^\times$, and its fixed space is zero. This is an instructive counterexample: enlarging $U_D^1$ by central units may preserve two fixed vectors, while enlarging it by the full unramified torus destroys both.

## 14. Formal degree and volume

### 14.1 The needed normalization

Character comparisons require a consistent measure but not a full harmonic-analysis apparatus. Let

$$
\bar G=D^\times/K^\times
$$

and choose Haar measure $d\bar g$. Write

$$
V_{\bar G}=\operatorname{vol}(\bar G).
$$

One convenient normalization is $V_{\bar G}=1$. Another is to give the image of $\mathcal O_D^\times$ a prescribed volume. Formulas below display $V_{\bar G}$ so that either choice can be used.

For a unitary central character, matrix coefficients become honest functions on $\bar G$ after pairing one coefficient with the conjugate of another; algebraically one can pair $\pi$ with $\pi^\vee$. Since $\bar G$ is compact, every irreducible is square-integrable modulo the center.

### 14.2 Schur orthogonality on the central quotient

Let $v,v'\in\pi$ and $\lambda,\lambda'\in\pi^\vee$. Schur orthogonality gives

$$
\int_{\bar G}
\lambda(\pi(g)v)
\lambda'(\pi(g^{-1})v')\,d\bar g
=\frac{V_{\bar G}}{\dim\pi}
\lambda(v')\lambda'(v).
$$

Accordingly the formal degree relative to $d\bar g$ is

$$
d(\pi)=\frac{\dim\pi}{V_{\bar G}}.
$$

If $\operatorname{vol}(\bar G)=1$, formal degree is simply dimension. Rescaling Haar measure by $c$ divides formal degree by $c$. Any numerical comparison that omits its volume normalization is incomplete.

### 14.3 Compact induction and degree

If $\pi=\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda$ is irreducible, then

$$
d(\pi)
=\frac{[D^\times:J]\dim\Lambda}{V_{\bar G}}.
$$

Equivalently, if quotient measure is normalized so that the image $\bar J$ has volume $V_{\bar J}$, then $V_{\bar G}=[D^\times:J]V_{\bar J}$ and

$$
d(\pi)=\frac{\dim\Lambda}{V_{\bar J}}.
$$

This is the exact amount of formal-degree theory needed to compare character normalizations later.

## 15. Type vectors and the newvector question

### 15.1 Why normal congruence groups do not select a line

On the split degree-two group, a conductor is often detected by the first compact subgroup fixing a one-dimensional newspace. It is tempting to seek the same object inside $D^\times$. The normality of $U_D^m$ immediately shows why that temptation is misleading. For irreducible $\pi$,

$$
\pi^{U_D^m}=0
\quad\text{or}\quad
\pi^{U_D^m}=\pi.
$$

At the first exponent $m=c_D(\pi)$ the invariant space therefore jumps from zero to dimension $\dim\pi$, not to dimension one. For a depth-zero dihedral packet that jump is from zero to dimension two. For a positive-depth unramified packet of conductor $2n$, it is from zero to dimension $2q^{n-1}$. Calling this whole space a newvector line would erase the most characteristic feature of the division group.

The replacement is a **type vector**: not usually a preferred vector of $\pi$, but a preferred copy of the inducing representation inside $\pi|_{J_\theta}$. This formulation behaves well under conjugation, coefficient extension, and integral structures. It also distinguishes the representation when principal-unit invariants alone do not.

A counterexample makes the point sharp. Two distinct regular characters of $k_D^\times$ can have the same restriction to $k^\times$. Their depth-zero representations have identical dimensions for invariants under every $U_D^m$ and under every $\mathcal O_K^\times U_D^m$, yet their two residue-character orbits are different. The congruence fixed spaces do not recover the packet; the type does.

### 15.2 The canonical type multiplicity space

Let $\pi=\mathrm{c\text{-}Ind}_J^{D^\times}\Lambda$ be one of the tame admissible constructions, with exact self-intertwining set $J$. Frobenius reciprocity gives

$$
\operatorname{Hom}_J(\Lambda,\pi|_J)
\cong
\operatorname{End}_{D^\times}(\pi).
$$

The displayed isomorphism uses the inducing map. Since $\pi$ is irreducible over $C$, the right side is $C$. Hence

$$
\dim_C\operatorname{Hom}_J(\Lambda,\pi)=1.
$$

This one-dimensional multiplicity space is the quaternionic new line. Its nonzero elements embed the full type space $\Lambda$ into $\pi$; scaling an embedding does not change its image. In the induced-function model, the copy supported on the identity coset realizes it concretely. Translating that copy gives the conjugate type spaces supported on the other cosets.

The self-intertwining hypothesis is decisive. If $\bar\theta$ at depth zero is Frobenius-invariant, the induced representation splits into two characters and the endomorphism algebra has dimension two. There is then no unique type embedding. Thus type multiplicity one is another form of regularity, not a consequence of finite index alone.

For a special packet the inducing subgroup is all of $D^\times$ and the type multiplicity line is simply the representation itself. This degenerate case fits the formalism and explains why its distinguished lattice will have rank one.

### 15.3 Toric lines and test vectors

The quadratic field used in a dihedral construction supplies a finer distinguished functional. In direct normalization, restriction of $\Lambda_\theta$ to the decisive part of $E^\times$ contains $\theta$ with multiplicity one. Evaluation on the identity coset therefore gives a nonzero $E^\times$-equivariant functional on the induced model, with the inverse character if the functional is viewed on vectors rather than on the dual.

The relevant multiplicity-one statement is

$$
\dim\operatorname{Hom}_{E^\times}(\pi,\Omega)\le1
$$

whenever $\Omega|_{K^\times}=\omega_\pi$ with the compatible variance. We prove the bound by making the required symmetry explicit. Choose $j_E\in D^\times$ inducing $\sigma$ and write

$$
D=E\oplus Ej_E,
\qquad
j_Ee=\sigma(e)j_E.
$$

Let $\tau=\operatorname{Ad}(j_E)\circ\overline{\phantom{x}}$. This is an anti-involution, it fixes $E$ pointwise, and

$$
\tau(a+bj_E)=a-\sigma(b)j_E.
$$

Every double coset $E^\times dE^\times$ is $\tau$-stable. If $d=a+bj_E$ with $ab\ne0$, Hilbert 90 gives $x\in E^\times$ such that

$$
\frac{x}{\sigma(x)}=-\frac{\sigma(b)}b.
$$

Taking $y=x^{-1}$ gives $xdy=\tau(d)$. If $b=0$, then $d\in E$ is already fixed; if $a=0$, choose $y=1$ and $x=-\sigma(b)/b$. Thus the assertion holds in every case.

Now pass to a principal-unit subgroup that kills $\pi$ and the two characters involved. All operators factor through a finite central extension. On this finite group, transpose with respect to $\tau$ reverses the composition of an $\Omega$-equivariant functional and an $\Omega^{-1}$-equivariant functional. Double-coset stability says the reversed operator equals the original one. If two independent $\Omega$-functionals existed, rank-one compositions with dual functionals would yield two independent endomorphisms of the irreducible representation, contradicting Schur's lemma. Hence

$$
\dim\operatorname{Hom}_{E^\times}(\pi,\Omega)
\dim\operatorname{Hom}_{E^\times}(\pi^\vee,\Omega^{-1})\le1.
$$

Duality identifies the two dimensions and proves the claim.

For the inducing torus and its prescribed character, existence was built into $\Lambda_\theta$, so the Hom space is exactly one dimensional. A generator is a **toric test vector functional**. There need not be such a functional for every character of every other quadratic torus. Multiplicity one proves uniqueness when a functional exists; it does not prove existence.

The invariant pairing between $\pi$ and $\pi^\vee$ identifies the $\theta$-functional with the dual of the $\theta^{-1}$-functional. If $\theta^\sigma=\theta^{-1}$, a normalizer element exchanges the two lines. Its square is central, so the central character determines the scalar square while the induced pairing determines whether the self-dual form is symmetric or alternating.

### 15.4 The selected split-side newvector interface

For each selected parameter there are therefore two different but corresponding minimal objects. On the split side, the conductor subgroup cuts out a one-dimensional newvector line. On the division side, the normal congruence subgroup cuts out the entire representation, while the compact-mod-center type has a one-dimensional multiplicity space. The correct interface is

$$
\text{split newvector line}
\quad\longleftrightarrow\quad
\operatorname{Hom}_{J_\theta}(\Lambda_\theta,\pi_D(E,\theta)).
$$

For special packets, both sides are labelled by $\mu$ and the division multiplicity space has rank one. For depth-zero packets, the division type is the Frobenius pair $\bar\theta\oplus\bar\theta^q$ and its multiplicity is one. At positive depth, the Heisenberg type replaces that pair, again with multiplicity one.

This dictionary is parameter-theoretic and integral: it identifies which minimal line and which lattice should be compared. It does not by itself prove the character identity between the two groups. That later theorem must still match regular classes and verify the inner-form sign. The distinction prevents a circular argument in which a chosen newvector is treated as proof of transfer.

## 16. Integral lattices and integral pairings

### 16.1 Coefficient fields and the existence criterion

Arithmetic applications need more than a complex representation: they need a lattice stable under the group. Let $L_\lambda$ be a finite extension of $\mathbf Q_\ell$, with valuation ring $R$, maximal ideal $\mathfrak m_R$, and fraction field $L_\lambda$. Assume $\ell$ differs from the residue characteristic $p$ of $K$ when using the tame Heisenberg constructions.

An $R$-lattice in an $L_\lambda$-representation $V$ is a finite free $R$-submodule spanning $V$. Stability under both $g$ and $g^{-1}$ forces every central scalar to be a unit. In particular, if $\varpi$ acts by $c$, a stable lattice can exist only when

$$
c\in R^\times.
$$

This condition is sharp for the representations at hand. Once the central scalar is a unit, the remaining action factors through a finite quotient after the center is imposed. A finite set of matrices and their inverses preserves some common lattice: start with any lattice, add its images under representatives of the finite quotient, and use unit central scalars for the omitted central powers. Thus an irreducible selected packet has a stable lattice exactly when its finite-order type values are defined over $L_\lambda$ and its unramified central scalar is integral and invertible, after enlarging the coefficient field if necessary.

The unit condition cannot be dropped. A one-dimensional unramified special packet with $\mu(\varpi)$ of positive $\ell$-adic valuation sends $\Pi$ to a nonunit. Stability under $\Pi^{-1}$ would require multiplication by its inverse, so no nonzero finite lattice survives.

### 16.2 Lattices in special and dihedral types

For $\operatorname{Sp}_D(\mu)$ with unit-valued $\mu$, take the rank-one lattice $R$ with action through $\mu\circ\operatorname{Nrd}$. For a depth-zero datum whose character values lie in $R^\times$, the rank-one lattice in $\Lambda_\theta$ induces the desired model.

At positive depth, begin with the simple character on the last unit layer. Its values have $p$-power order and therefore lie in units when $\ell\ne p$. Choose a maximal isotropic subgroup for the finite commutator pairing and induce its rank-one character lattice. This produces a finite free lattice in the Heisenberg representation. The tame torus extension acts through a finite quotient modulo the prescribed central scalar; after one finite coefficient extension, its operators preserve the lattice.

Changing the polarization changes the model but not the representation. When the finite quotient order is a unit in $R$, the Fourier intertwiners comparing two polarizations are integral isomorphisms after the standard unit normalization. If that order is not invertible, stable lattices still exist, but different choices can yield nonisomorphic reductions. Existence and canonical reduction are separate assertions.

The rectifier is finite order in the selected tame range. Its values are units, so passing from direct normalization to quadratic-induction normalization does not disturb integrality. It only tensors the torus lattice by a rank-one unit-valued lattice.

### 16.3 Finite free induction and base change

Let $\Lambda_R$ be a stable finite free lattice in a selected type on $J$. Define

$$
\pi_R=\operatorname{Ind}_J^{D^\times}\Lambda_R.
$$

Because $J\backslash D^\times$ is finite, evaluation on coset representatives gives

$$
\pi_R\cong\bigoplus_{J\backslash D^\times}\Lambda_R
$$

as an $R$-module. Hence $\pi_R$ is finite free of rank

$$
[D^\times:J]\operatorname{rank}_R\Lambda_R,
$$

and

$$
\pi_R\otimes_RL_\lambda\cong\pi.
$$

No completion or infinite-support argument is hidden here. Compactness modulo the center has turned the entire representation, not merely one fixed-vector space, into a finite module.

If $R\to R'$ is a finite extension of valuation rings, the same finite direct-sum model gives a canonical isomorphism

$$
\pi_R\otimes_RR'
\cong
\operatorname{Ind}_J^{D^\times}(\Lambda_R\otimes_RR').
$$

Thus coefficient enlargement used to acquire character values commutes with construction, twists, and the type multiplicity line. This is the precise integral compatibility needed when the selected split representation and its division companion are placed over one coefficient field.

### 16.4 Perfect duality and self-dual lattices

Put $\Lambda_R^\#=\operatorname{Hom}_R(\Lambda_R,R)$ with contragredient action. For induced functions define

$$
\langle f,f^\#\rangle
=\sum_{x\in J\backslash D^\times}
\langle f(x),f^\#(x)\rangle_\Lambda.
$$

The covariance laws cancel when $x$ is replaced by $jx$, and right translation permutes the finite coset set. The pairing is therefore well defined and $D^\times$-invariant. It is perfect because it is the orthogonal direct sum of perfect evaluation pairings on finitely many copies of $\Lambda_R$. In particular,

$$
\pi_R^\#\cong\operatorname{Ind}_J^{D^\times}\Lambda_R^\#.
$$

No denominator appears: this is a sum, not an average. That fact is crucial at primes dividing $[D^\times:J]$.

If $\pi$ is self-dual, the rational pairing may be symmetric or alternating. A stable lattice $M$ and its dual $M^\#$ are commensurable, so scaling and intersection produce an almost self-dual stable lattice. A genuinely self-dual lattice requires the corresponding unimodular form over $R$; it follows under the usual unit hypotheses on $2$ and the relevant finite quotient, but is not automatic at a dyadic coefficient prime. The perfect pairing between $\pi_R$ and its contragredient lattice is unconditional and is the form used for the selected comparison.

The one-dimensional type multiplicity spaces inherit dual rank-one lattices. Their pairing is perfect after choosing primitive generators, unique up to multiplication by reciprocal units. This is the integral version of the division-side new line in Chapter 15.

### 16.5 Reduction and the nonbanal boundary

Let $\bar R=R/\mathfrak m_R$. If $\ell$ does not divide the orders of the finite quotients controlling the type, the coset permutation action, and the relevant stabilizers, averaging remains exact after reduction. In this banal range, reduction preserves irreducibility, the one-dimensional type multiplicity, the toric functional when present, and the perfect pairing with the contragredient.

Outside that range, only the lattice and its reduction are automatic. For example, if $\ell$ divides $q+1$, two distinct regular characters of $k_D^\times$ can become congruent to their Frobenius conjugates. The reduced index-two induction can split or acquire extra endomorphisms. If $\ell$ divides a finite symplectic quotient order, polarization projectors need not remain exact. These are genuine congruences, not failures of the characteristic-zero construction.

Accordingly the integral package has two layers. Stable finite free lattices and perfect dual-lattice pairings hold for unit-valued selected data. Irreducible reduction and preservation of distinguished lines require the explicitly stated banal hypotheses. Primitive wild types are outside both selected assertions because their integral extension operators have not been constructed here.

## 17. Measures, orbital normalization, and transfer data

### 17.1 A compatible system of Haar measures

Pointwise finite-dimensional characters do not depend on Haar measure, but distributions, orbital integrals, and formal degrees do. We therefore fix a compatible system rather than renormalizing each quotient independently.

Choose multiplicative Haar measures by

$$
\operatorname{vol}(\mathcal O_K^\times,d^\times z)=1,
\qquad
\operatorname{vol}(\mathcal O_D^\times,d^\times d)=1.
$$

For every embedded quadratic field $E$, choose $d^\times e$ with $\operatorname{vol}(\mathcal O_E^\times)=1$. The same $d^\times e$ is used when $E^\times$ is viewed as a centralizer on either inner form. All quotient measures are then defined by Weil's formula. For example,

$$
\int_{D^\times}\Phi(d)\,d^\times d
=\int_{E^\times\backslash D^\times}
\int_{E^\times}\Phi(ed)\,d^\times e\,d\dot d.
$$

One must not separately decree that each quotient compact subgroup has volume one; doing so can contradict this formula. With the two central unit normalizations above, the image of $\mathcal O_D^\times$ in $D^\times/K^\times$ has volume one. The two valuation parities are disjoint and equipotent, so

$$
\operatorname{vol}(D^\times/K^\times)=2.
$$

Thus the formal degree in this normalization is $\dim\pi/2$. If instead the total central quotient is normalized to volume one, every formal degree doubles. Both conventions are legitimate; the conversion factor must be shown.

### 17.2 Centralizers, discriminants, and orbital integrals

Let $d\in D^\times$ be regular and put $E=K[d]$. Its reduced characteristic polynomial has discriminant

$$
\Delta(d)=\operatorname{Trd}(d)^2-4\operatorname{Nrd}(d).
$$

The Weyl discriminant used for degree two is

$$
D_D(d)=\left|\frac{\Delta(d)}{\operatorname{Nrd}(d)}\right|_K.
$$

If a degree-two matrix $g$ has the same characteristic polynomial, then its elliptic centralizer is the same abstract field $E^\times$ and

$$
D_{\mathrm{split}}(g)=D_D(d).
$$

Using the common centralizer measure, define

$$
O_d(f)=\int_{E^\times\backslash D^\times}
f(x^{-1}dx)\,d\dot x.
$$

The normalized orbital integral is $D_D(d)^{1/2}O_d(f)$. A transfer statement must use either ordinary orbital integrals on both groups or normalized orbital integrals on both. Mixing the two conventions inserts the unwanted factor $D_D(d)^{1/2}$.

Trace and norm do three jobs at once: they determine the regular conjugacy class in $D^\times$, identify its matching elliptic characteristic polynomial, and determine the Weyl discriminant. This is why their normalization was fixed before representation theory began.

### 17.3 Pointwise characters versus distributions

For a compactly supported locally constant function $f$, use the action

$$
\pi(f)=\int_{D^\times}f(d)\pi(d)\,d^\times d.
$$

Since $\pi$ is finite dimensional and smooth, subdivision by a sufficiently small compact open subgroup turns the integral into a finite sum. Therefore

$$
\operatorname{tr}\pi(f)
=\int_{D^\times}f(d)\Theta_\pi(d)\,d^\times d.
$$

The pointwise function $\Theta_\pi$ is the ordinary matrix trace and does not change when Haar measure is rescaled. The distribution $f\mapsto\operatorname{tr}\pi(f)$ is represented relative to the chosen measure; changing the measure changes the convolution operator and its integral description together.

Likewise, the finite compact-induction formula contains no volume factor. Volumes enter only after one integrates that pointwise formula or groups it into orbital integrals. This separation is the safest normalization check in the subject.

### 17.4 The selected comparison package

The selected parameter table now has two rows. A character $\mu$ gives the special packet $\operatorname{Sp}_D(\mu)$. A tame admissible quadratic pair $(E,\theta)$ gives the quadratic-induction-normalized packet $\pi_D(E,\theta)$. Their central characters and conductors agree with those of the correspondingly labelled selected split representations:

$$
\mu^2,
\qquad
a_D=
\begin{cases}1,&a(\mu)=0,\\2a(\mu),&a(\mu)>0,
\end{cases}
$$

and

$$
\theta|_{K^\times}\omega_{E/K},
\qquad
a_D=\Delta(E/K)+f(E/K)a_E(\theta).
$$

For matching regular elliptic elements, the transfer normalization to be proved later is the pointwise identity

$$
\Theta_{\mathrm{split}}(g)=-\Theta_D(d).
$$

The minus sign is the degree-two inner-form sign. At depth zero it is visible in the negative finite cuspidal sum on the split side versus the positive Frobenius sum on the division side. At positive depth it is carried by the compatible rectifier and finite Heisenberg traces. Near the center, the full finite double-coset formula must be used on both sides; a two-term torus approximation is not sufficient.

This chapter has fixed every normalization appearing in that assertion: characteristic polynomials, centralizer measures, quotient measures, Weyl discriminants, rectifiers, and pointwise character conventions. It has not assumed the identity. The remaining proof is a comparison theorem, not part of the classification of $D^\times$.

## 18. Examples over $\mathbf Q_p$

### 18.1 Norm characters

Let $D$ be the quaternion division algebra over $\mathbf Q_p$. For any smooth $\mu:\mathbf Q_p^\times\to C^\times$,

$$
\pi=\mu\circ\operatorname{Nrd}
$$

has dimension one and central character $\mu^2$. If $\mu$ is unramified, then $c_D(\pi)=0$ while the selected special conductor is $a_D(\pi)=1$. If $a(\mu)=r>0$, then

$$
a_D(\pi)=2r.
$$

For example a tamely ramified character inflated from $\mathbf F_p^\times$ has $r=1$ and gives a norm character of conductor two. It is not a level-zero higher-dimensional representation even though the same conductor number occurs; dimension separates the families.

### 18.2 A level-zero representation

Assume first that $p$ is arbitrary and let $L/\mathbf Q_p$ be unramified quadratic. Choose a generator $\zeta$ of $\mathbf F_{p^2}^\times$ and a root of unity $\xi\in C^\times$ of order $p^2-1$. Define

$$
\bar\theta(\zeta)=\xi.
$$

Since the exponent $1$ is not divisible by $p+1$, $\bar\theta^p\ne\bar\theta$. Inflate it to $\mathcal O_L^\times$, make it trivial on $U_L^1$, and choose any value on $p$. Then

$$
\pi_\theta=\mathrm{c\text{-}Ind}_{L^\times U_D^1}^{D^\times}\theta
$$

is irreducible of dimension two and conductor two. On a residue-regular unit $u$,

$$
\Theta_{\pi_\theta}(u)
=\bar\theta(\bar u)+\bar\theta(\bar u^p),
$$

and on odd-valuation elements its character is zero.

### 18.3 A positive-depth unramified example

Assume $p$ is odd. Choose an additive character of $L$ of conductor zero and choose $b\in\mathcal O_L^\times$ whose residue is not in $\mathbf F_p$. Define the last unit layer of a character $\theta$ by

$$
\theta(1+px)=
\psi_L(p^{-1}bx)
\qquad(x\in\mathcal O_L),
$$

and extend it so that $a_L(\theta)=2$. The choice $b\notin\mathbf F_p$ makes $\theta$ regular after norm twists. The associated unramified admissible-pair representation has

$$
a_D(\pi)=4,
\qquad
c_D(\pi)=3,
\qquad
\ell_D(\pi)=2,
\qquad
\dim\pi=2p.
$$

In direct normalization its central character is $\theta|_{\mathbf Q_p^\times}$; in quadratic-induction normalization it is $\theta|_{\mathbf Q_p^\times}\omega_{L/\mathbf Q_p}$. The construction uses a nontrivial finite Heisenberg step; writing the inducing representation as a character trivial on all extra principal units would give the wrong dimension and generally fail the intersection compatibility.

### 18.4 A tame ramified example and the dyadic warning

Let $p$ be odd and $E=\mathbf Q_p(\sqrt p)$. Its discriminant exponent is one. Choose a character $\theta$ of $E^\times$ of conductor two whose nontrivial character on

$$
U_E^1/U_E^2\cong(\mathbf F_p,+)
$$

is not fixed by $\sigma$. Since $\sigma(\sqrt p)=-\sqrt p$, every nontrivial such additive character is moved when $p$ is odd. A minimal choice gives

$$
a_D(\pi(E,\theta))=3,
\qquad
c_D=2,
\qquad
\ell_D=1,
\qquad
\dim\pi=p+1.
$$

At $p=2$, the statement “ramified quadratic means discriminant exponent one” is false, sign no longer separates a character from its inverse on a two-element residue layer, and tame parity arguments disappear. The abstract Clifford classification remains exhaustive, but the displayed tame dimension and conductor formulas must not be transplanted unchanged.

## 19. The transfer-facing dictionary

### 19.1 The classification table

The following table collects intrinsic data without asserting a correspondence with another group.

| family                         | parameter                                                                               |                                 dimension |                                                $a_D$ | central character                                                                | contragredient                    |
| ------------------------------ | --------------------------------------------------------------------------------------- | ----------------------------------------: | ---------------------------------------------------: | -------------------------------------------------------------------------------- | --------------------------------- |
| special norm character         | $\mu:K^\times\to C^\times$                                                              |                                       $1$ |               $1$ if $a(\mu)=0$, otherwise $2a(\mu)$ | $\mu^2$                                                                          | $\mu^{-1}\circ\operatorname{Nrd}$ |
| level zero                     | regular $\theta$ on unramified $L^\times$, $a_L(\theta)=1$                              |                                       $2$ |                                                  $2$ | direct: $\theta\vert_{K^\times}$; selected: $\theta\vert_{K^\times}\omega_{L/K}$ | datum for $\theta^{-1}$           |
| tame unramified positive depth | normalized minimal admissible $(L/K,\theta,[\Lambda_\theta])$, $a_L(\theta)=n\ge2$      |                                $2q^{n-1}$ |                                                 $2n$ | direct: $\theta\vert_{K^\times}$; selected: $\theta\vert_{K^\times}\omega_{L/K}$ | dual normalized datum             |
| tame ramified                  | normalized minimal admissible $(E/K,\theta,[\Lambda_\theta])$, $a_E(\theta)=n\ge2$ even |                        $(q+1)q^{(n-2)/2}$ |                                                $n+1$ | direct: $\theta\vert_{K^\times}$; selected: $\theta\vert_{K^\times}\omega_{E/K}$ | dual normalized datum             |
| wild/general                   | Clifford datum $(m,\rho,G_\rho,[\alpha],\eta)$                                          | orbit size $\times\dim\rho\times\dim\eta$ | from minimal killed $U_D^m$; $m+1$ for noncharacters | prescribed $\omega$                                                              | dual Clifford datum               |

For every higher-dimensional row,

$$
c_D=a_D-1,
\qquad
\ell_D=a_D-2.
$$

For characters, use the separate first row. Twisting sends $\omega$ to $\omega\chi^2$, sends $\theta$ to $\theta(\chi\circ N_{E/K})$, and may lower conductor by cancellation. Unramified twists preserve every displayed depth.

### 19.2 Regular-character values

For downstream comparison it is useful to keep three character rules together:

$$
\Theta_\pi(z)=\dim(\pi)\omega_\pi(z)
\qquad(z\in K^\times),
$$

$$
\Theta_{\mathrm{Ind}_J^{D^\times}\Lambda}(g)
=\sum_{\substack{x\in J\backslash D^\times\\xgx^{-1}\in J}}
\operatorname{tr}\Lambda(xgx^{-1}),
$$

and, on torus-regular elements in the regular quadratic range,

$$
\Theta_{\pi(E,\theta)}(t)
=\operatorname{tr}\Lambda_\theta(t)
+\operatorname{tr}\Lambda_\theta(\sigma(t)).
$$

At level zero the last line is simply $\theta(t)+\theta(\sigma(t))$. At positive depth the extension trace must be retained. Contragredience replaces $g$ by $g^{-1}$ in the character, and a norm twist multiplies the value at $g$ by $\chi(\operatorname{Nrd}g)$.

### 19.3 What is ready for comparison

Every irreducible smooth representation of $D^\times$ now enters later theory with the following data defined:

- its finite dimension and formal degree for an explicit quotient volume;
- its central character on $K^\times$;
- its congruence exponent, level, and transfer-facing conductor;
- its behavior under norm twists and contragredience;
- an exhaustive finite-quotient or Clifford label, even in the wild range;
- concrete admissible-pair data in the level-zero and tame quadratic ranges;
- exact compact-induction and isomorphism criteria;
- matrix-character values on regular elements through a finite conjugacy sum;
- maximal and Eichler-like compact-open invariant dimensions through finite Mackey theory;
- a one-dimensional type multiplicity space replacing the split newvector line;
- stable finite free lattices and perfect contragredient pairings for unit-valued selected data;
- compatible centralizer, quotient, orbital-integral, and formal-degree measures.

No representation has yet been matched with a representation of $\mathrm{GL}_2(K)$. In particular, equality of conductors, signs in a character identity, and the placement of one-dimensional norm characters relative to special representations are established by the comparison theorem in Book 80. The present conductor normalization is a prepared interface, not a proof of those statements.

### 19.4 Conclusion

The apparent simplicity of $D^\times/K^\times$ hides a remarkably structured finite theory. The reduced norm fixes the valuation, doubles the center's depth, and identifies every one-dimensional representation. The maximal order supplies a canonical normal filtration whose residue layer is $\mathbf F_{q^2}^\times$ and whose positive layers are additive copies of $\mathbf F_{q^2}$. Frobenius conjugation and commutator pairings then determine which characters descend, which travel in nontrivial orbits, and which require Heisenberg or projective extensions.

Compactness modulo the center turns those filtration calculations into a complete classification. Every irreducible is finite dimensional; every one kills a congruence subgroup; and every one is recovered from a finite representation of the maximal compact together with the action of a division uniformizer. Regular residue characters give the two-dimensional level-zero family. Minimal admissible characters of embedded quadratic fields give the tame positive-depth families, with explicit dimensions, centers, conductors, duals, and twists. Where wild ramification prevents a uniform elementary label, the Clifford datum remains exact and exhaustive rather than hiding the missing cases.

The resulting representation is visible through several compatible shadows: its inducing orbit, its first nontrivial congruence layer, its central character, its finite matrix character on regular classes, its type multiplicity line, its integral lattice, and its formal degree. Compatible centralizer measures and rectifiers make these shadows one coherent local object. The next stage may compare that object with discrete-series representation theory on the split inner form; the division-algebra side itself is complete in the selected special and tame dihedral range, while the primitive wild boundary remains explicit.
