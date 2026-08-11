# Algebraicity and Integral Structures of Weight-Two Packets

## Contents

1. [The arithmetic problem behind a weight-two packet](#1-the-arithmetic-problem-behind-a-weight-two-packet)
   - [Four structures that must be compared](#11-four-structures-that-must-be-compared)
   - [Standing conventions and algebraic normalization](#12-standing-conventions-and-algebraic-normalization)
   - [Packets, representatives, and realizations](#13-packets-representatives-and-realizations)
   - [The logical architecture](#14-the-logical-architecture)
2. [Finite Hecke orders and their characteristic-zero points](#2-finite-hecke-orders-and-their-characteristic-zero-points)
   - [The integral source of algebraicity](#21-the-integral-source-of-algebraicity)
   - [Characters of a finite commutative algebra](#22-characters-of-a-finite-commutative-algebra)
   - [Reduced generic fibers and simultaneous eigenspaces](#23-reduced-generic-fibers-and-simultaneous-eigenspaces)
   - [Why good operators must include determinants](#24-why-good-operators-must-include-determinants)
3. [Rationality fields](#3-rationality-fields)
   - [The Hecke field is a number field](#31-the-hecke-field-is-a-number-field)
   - [Finite generation by finitely many places](#32-finite-generation-by-finitely-many-places)
   - [Field of rationality versus field of definition](#33-field-of-rationality-versus-field-of-definition)
   - [A descent theorem for an eigenline](#34-a-descent-theorem-for-an-eigenline)
4. [Galois conjugation and the packet orbit](#4-galois-conjugation-and-the-packet-orbit)
   - [Semilinear conjugation of modules](#41-semilinear-conjugation-of-modules)
   - [Conjugating an eigensystem](#42-conjugating-an-eigensystem)
   - [The finite orbit and its stabilizer](#43-the-finite-orbit-and-its-stabilizer)
   - [Conjugation of automorphic representations](#44-conjugation-of-automorphic-representations)
5. [Integral eigenvalues and eigenlattices](#5-integral-eigenvalues-and-eigenlattices)
   - [Integrality from a stable lattice](#51-integrality-from-a-stable-lattice)
   - [The saturated intersection lattice](#52-the-saturated-intersection-lattice)
   - [Rank one, fractional ideals, and homothety](#53-rank-one-fractional-ideals-and-homothety)
   - [Denominators of projectors](#54-denominators-of-projectors)
6. [The integral packet and coefficient extension](#6-the-integral-packet-and-coefficient-extension)
   - [The universal packet quotient](#61-the-universal-packet-quotient)
   - [Flat base change and embedding components](#62-flat-base-change-and-embedding-components)
   - [Localization at a coefficient prime](#63-localization-at-a-coefficient-prime)
   - [Congruence does not identify characteristic-zero packets](#64-congruence-does-not-identify-characteristic-zero-packets)
7. [Weight two and cohomological rational structures](#7-weight-two-and-cohomological-rational-structures)
   - [Why weight two belongs in degree one](#71-why-weight-two-belongs-in-degree-one)
   - [A rational Hodge--Hecke module](#72-a-rational-hodge--hecke-module)
   - [The packet summand and its Hodge line](#73-the-packet-summand-and-its-hodge-line)
   - [Complex conjugation and signs](#74-complex-conjugation-and-signs)
8. [Comparison isomorphisms and period lines](#8-comparison-isomorphisms-and-period-lines)
   - [The comparison datum](#81-the-comparison-datum)
   - [Periods as comparison scalars](#82-periods-as-comparison-scalars)
   - [Basis independence and the period class](#83-basis-independence-and-the-period-class)
   - [Determinant periods in higher multiplicity](#84-determinant-periods-in-higher-multiplicity)
9. [Integral periods and coefficient embeddings](#9-integral-periods-and-coefficient-embeddings)
   - [Integral Betti and de Rham lattices](#91-integral-betti-and-de-rham-lattices)
   - [The period matrix of a packet](#92-the-period-matrix-of-a-packet)
   - [Changing the coefficient embedding](#93-changing-the-coefficient-embedding)
   - [What Galois conjugation does not say about periods](#94-what-galois-conjugation-does-not-say-about-periods)
10. [Pairings, dual packets, and polarizations](#10-pairings-dual-packets-and-polarizations)
    - [Adjoint Hecke actions](#101-adjoint-hecke-actions)
    - [The dual eigensystem](#102-the-dual-eigensystem)
    - [Period products from a perfect pairing](#103-period-products-from-a-perfect-pairing)
    - [Complex conjugation and the two signs](#104-complex-conjugation-and-the-two-signs)
11. [The $\mathrm{GL}_2$ weight-two packet](#11-the-mathrmgl_2-weight-two-packet)
    - [From a normalized newform to a packet](#111-from-a-normalized-newform-to-a-packet)
    - [Strong multiplicity one after conjugation](#112-strong-multiplicity-one-after-conjugation)
    - [Ramified components and newvectors](#113-ramified-components-and-newvectors)
    - [Compatibility with every coefficient embedding](#114-compatibility-with-every-coefficient-embedding)
12. [Quaternionic weight-two packets](#12-quaternionic-weight-two-packets)
    - [Finite algebraic models](#121-finite-algebraic-models)
    - [Conjugate near-equivalence blocks](#122-conjugate-near-equivalence-blocks)
    - [When a single constituent is determined](#123-when-a-single-constituent-is-determined)
    - [Integral Brandt lattices](#124-integral-brandt-lattices)
13. [Examples, failures, and normalization checks](#13-examples-failures-and-normalization-checks)
    - [A rational packet](#131-a-rational-packet)
    - [A quadratic packet](#132-a-quadratic-packet)
    - [Oldspaces and repeated eigensystems](#133-oldspaces-and-repeated-eigensystems)
    - [Four instructive failure modes](#134-four-instructive-failure-modes)
14. [The complete algebraic and integral package](#14-the-complete-algebraic-and-integral-package)
    - [The main theorem](#141-the-main-theorem)
    - [The implication chain](#142-the-implication-chain)
    - [Hypothesis and normalization ledger](#143-hypothesis-and-normalization-ledger)
    - [Conclusion](#144-conclusion)

## 1. The arithmetic problem behind a weight-two packet

### 1.1 Four structures that must be compared

A weight-two eigenform first appears analytically, as a vector in a complex automorphic representation. Arithmetic applications ask for much more than that complex vector. They need a number field containing its Hecke eigenvalues, all conjugate eigensystems under embeddings of that field, lattices stable under the Hecke action, and comparison scalars between the automorphic or de Rham normalization and a rational topological normalization. These four structures are related, but none is a formal substitute for another.

The central problem of this book is to construct and compare them without suppressing choices. A complex eigensystem has a **field of rationality**. A representation may require a larger **field of definition**. A one-dimensional newvector space has lattices, but usually no distinguished generator. A period is a scalar only after two bases have been chosen; intrinsically it is a class modulo algebraic rescaling. Finally, an embedding $E\hookrightarrow\mathbf C$ acts on algebraic coefficients, whereas a transcendental period is not thereby endowed with an action of every automorphism of $\mathbf C$.

Weight two is the meeting point in every realization that genuinely occurs in degree one. Its algebraic normalization makes the good Hecke polynomial compatible with an integral Hecke action, while a degree-one realization has Hodge types $(1,0)$ and $(0,1)$. In multiplicity one, comparison then supplies exactly two Betti sign directions and a holomorphic line to be compared with them. This statement is deliberately conditional: over a totally real field of degree $d>1$, the Hilbert modular realization is normally in degree $d$ and has $2^d$ archimedean sign lines, as Book 92 explains. Nothing below turns that higher-degree realization into degree one.

### 1.2 Standing conventions and algebraic normalization

Let $F$ be a totally real field. For the global $\mathrm{GL}_2$ statements we consider an irreducible cuspidal automorphic representation

$$
\pi=\pi_\infty\otimes\pi_f
$$

whose archimedean component is cohomological of parallel weight two. The analogous algebraic discussion applies to finite modules for a quaternion algebra $D/F$ with an algebraic weight corresponding to weight two. The precise geometric period statements will always assume an explicitly given degree-one realization; they will not be inferred merely from the word “automorphic.”

Choose a finite set $\Sigma$ containing every archimedean place, every place where the level, central character, or coefficient lattice is ramified, and every place at which the chosen group is not hyperspecial. For $v\notin\Sigma$, write $q_v$ for the residue cardinality and use the raw, algebraic double-coset operators $T_v,S_v$. Their polynomial is

$$
P_v(X)=1-T_vX+q_vS_vX^2. \tag{1.1}
$$

If $t_v,s_v$ are the corresponding eigenvalues, then the algebraic packet records

$$
P_{v,\lambda}(X)=1-t_vX+q_vs_vX^2. \tag{1.2}
$$

This convention is fixed throughout. Unitary Satake parameters introduce powers of $q_v^{1/2}$ and are useful analytically, but arbitrary coefficient automorphisms do not act coherently on an unrecorded choice of square root. Algebraicity and conjugation will therefore always refer to (1.2).

Let $K$ be a number field held fixed in a chosen arithmetic model, and write $R=\mathcal O_K$. A **rational Hecke module** is a finite-dimensional $K$-space $V$ preserved by the chosen commuting operators. Its faithful acting algebra is the image

$$
B=K[T_v,S_v,S_v^{-1}:v\notin\Sigma]\big/\operatorname{Ann}(V)
\subseteq\operatorname{End}_K(V). \tag{1.3}
$$

An **integral Hecke module** is, in addition, a finite torsion-free $R$-module $M\subset V$ spanning $V$ and preserved by all these operators. Its acting order is

$$
\mathbb T=R[T_v,S_v,S_v^{-1}:v\notin\Sigma]\big/\operatorname{Ann}(M)
\subseteq\operatorname{End}_R(M), \tag{1.4}
$$

and $B=\mathbb T\otimes_RK$. Only image algebras are used. This makes the modules faithful and prevents irrelevant abstract characters from being mistaken for eigensystems that occur.

There are two coefficient-field conventions that must not be mixed. The constructions relative to $K$ produce only $K$-embeddings of a residue field. The absolute field of rationality uses all $\mathbf Q$-embeddings. To obtain the latter from a model initially defined over a field $A$, one either descends the whole arithmetic space to $\mathbf Q$ or takes restriction of scalars together with all conjugate coefficient data. In the holomorphic $\mathrm{GL}_2$ setting, the conjugation-compatible $q$-expansion structures assumed in Book 92 provide precisely those conjugate spaces. Merely viewing one fixed-nebentype complex space in isolation does not.

### 1.3 Packets, representatives, and realizations

A **good Hecke eigensystem** is a $K$-algebra homomorphism

$$
\lambda:B\longrightarrow\overline{\mathbf Q}.
$$

Its Hecke field is

$$
E_\lambda=K\bigl(\lambda(T_v),\lambda(S_v):v\notin\Sigma\bigr). \tag{1.5}
$$

Here and below $K$ acts through the fixed embedding $K\hookrightarrow\overline{\mathbf Q}$. The **relative algebraic packet** $[\lambda]_K$ is the set of conjugate characters $\iota\circ\lambda$ as $\iota$ ranges through $K$-embeddings of $E_\lambda$ into $\mathbf C$, with repetitions removed. Equivalently, it is the closed point of $\operatorname{Spec}(B)$ determined by the kernel of $\lambda$, together with all of its geometric points. We abbreviate it to $[\lambda]$ when the base is clear. When $K=\mathbf Q$, it is the absolute algebraic packet.

This use of “packet” is deliberately algebraic. For a conjugation-compatible $\mathrm{GL}_2$ automorphic module, strong multiplicity one turns each member into a unique cuspidal automorphic representation. For a finite quaternionic Hecke module, the good eigensystem can initially identify only a near-equivalence block; extra ramified data or a separate determination theorem is needed to single out one constituent. A **realization** of $[\lambda]$ means a Hecke module—automorphic, Betti, de Rham, or integral—in which its eigensystem occurs. The book compares realizations but never identifies them merely because their dimensions agree.

### 1.4 The logical architecture

The construction proceeds in four stages. First, finite rational linear algebra gives number fields and conjugate characters; a stable integral lattice then gives algebraic integers and saturated eigenlattices. Second, strong multiplicity one converts good $\mathrm{GL}_2$ Hecke data into global representations and therefore controls even the ramified local factors. Third, degree-one comparison turns a rational Hodge structure carrying the same Hecke action into period classes. Fourth, pairings and integral structures show exactly how duality, signs, coefficient primes, and embeddings interact.

The difficult points are negative as well as positive. Reduction modulo a prime is not flat. Generic projectors can have denominators. A field of rationality need not descend a whole representation. Oldspaces can have dimension greater than one even though the global representation occurs once. These are not peripheral cautions: they determine the correct form of every integral statement below.

## 2. Finite Hecke orders and their characteristic-zero points

### 2.1 The integral source of algebraicity

The algebraicity of weight-two Hecke data does not come from spectral theory alone. It comes from an independently constructed rational arithmetic module. The number-field fixed-level structure assumed in Book 92 supplies such a rational module for holomorphic cohomological $\mathrm{GL}_2$ forms. It does **not** by itself supply a common stable lattice for every Hecke operator; Book 92 explicitly leaves integral models and the $q$-expansion principle as separate arithmetic inputs. For definite quaternionic forms, by contrast, the integral class module and faithful image algebra of Book 91 do supply the lattice.

At the rational level, the image $B\subseteq\operatorname{End}_K(V)$ is automatically finite-dimensional over $K$, so its characters have algebraic values. Once an integral source $M$ is also given, the following stronger order statement yields integrality.

**Proposition 2.1 (finite Hecke order).** Let $R$ be the ring of integers of a number field and let $M$ be a finite torsion-free $R$-module. If $\mathbb T\subseteq\operatorname{End}_R(M)$ is the $R$-algebra generated by any commuting family of endomorphisms, then $\mathbb T$ is a finite torsion-free $R$-module. Hence $\mathbb T\otimes_RK$ is a finite-dimensional commutative $K$-algebra, where $K=\operatorname{Frac}(R)$.

**Proof strategy.** Embed the acting algebra into a finite module and use that a submodule over a Noetherian domain is finite. Torsion-freeness is inherited from the endomorphism module.

**Proof.** Since $M$ is finite torsion-free over the Dedekind domain $R$, it is projective. Thus $\operatorname{End}_R(M)$ is a finite projective, in particular finite torsion-free, $R$-module. The submodule $\mathbb T$ is finite because $R$ is Noetherian, and it is torsion-free because it lies in a torsion-free module. Tensoring with $K$ gives the final assertion. $\square$

The proposition does not assert that $\mathbb T_K$ is reduced. A nonsemisimple operator can create nilpotents. In the automorphic situations at issue, commuting normal or self-adjoint operators on a positive definite complex space are simultaneously diagonalizable; then the image after scalar extension to $\mathbf C$ is reduced, and faithful flatness implies that $\mathbb T_K$ is reduced. We will state reducedness whenever it is used.

### 2.2 Characters of a finite commutative algebra

Let $B$ be a finite-dimensional commutative $K$-algebra. Every homomorphism $\lambda:B\to\mathbf C$ has algebraic image: for $b\in B$, multiplication by $b$ is a $K$-linear endomorphism of $B$, and $\lambda(b)$ is a root of its characteristic polynomial. More is true when $B$ is reduced.

**Theorem 2.2 (generic decomposition).** If $B$ is finite-dimensional, commutative, and reduced over a characteristic-zero field $K$, then

$$
B\cong\prod_{i=1}^rE_i \tag{2.1}
$$

for finite field extensions $E_i/K$. After extension to an algebraic closure $\overline K$,

$$
B\otimes_K\overline K\cong\prod_{\tau:B\to\overline K}\overline K. \tag{2.2}
$$

**Proof.** A finite-dimensional algebra is Artinian. Its nilradical equals its Jacobson radical and is zero by reducedness, so the Chinese remainder theorem decomposes $B$ into its localizations at maximal ideals. Each reduced Artinian local ring is a field: its maximal ideal is nilpotent, hence zero. In characteristic zero each residue field is separable over $K$. Tensoring a finite separable field with $\overline K$ gives one copy of $\overline K$ for each embedding, proving (2.2). $\square$

The primitive idempotent $e_i$ of (2.1) isolates the $i$th characteristic-zero branch. It generally belongs only to $B$, not to the integral order $\mathbb T$. The denominator needed to put a multiple of $e_i$ in $\mathbb T$ measures congruence with the other branches.

### 2.3 Reduced generic fibers and simultaneous eigenspaces

Let $V$ be a rational Hecke module and suppose its acting algebra $B$ is reduced. For a character $\lambda:B\to E$, define

$$
V_\lambda=\{x\in V\otimes_KE:b x=\lambda(b)x\text{ for every }b\in B\}. \tag{2.3}
$$

Equation (2.2) gives a canonical decomposition

$$
V\otimes_K\overline K=\bigoplus_\lambda V_\lambda. \tag{2.4}
$$

The dimensions of the summands need not be one. The algebra remembers joint eigencharacters, not their multiplicities in $V$. At minimal $K_1$-level for a generic $\mathrm{GL}_2$ representation, newvector theory supplies a one-dimensional finite line. At higher level the same $\lambda$ can occur several times through oldvectors. On a quaternionic class module, a near-equivalence block can likewise have several vectors.

If a commuting family is self-adjoint for a positive definite Hermitian form, simultaneous diagonalization proves reducedness directly: its image embeds into a product of copies of $\mathbf C$ by evaluation on common eigenspaces. By contrast, an arbitrary commuting family can act through a Jordan block, and then generalized eigenspaces rather than (2.3) are required.

### 2.4 Why good operators must include determinants

At an unramified split place, the spherical representation is determined by the unordered pair of Satake roots, equivalently by both coefficients of (1.2). The trace coefficient alone is insufficient if the central character varies. Indeed, unordered pairs $\{\alpha,\beta\}$ and $\{\gamma,\delta\}$ can have equal sums and unequal products.

Consequently a packet with unfixed central character records both $T_v$ and $S_v$. If the central character $\omega$ has already been fixed, then $s_v=\omega_v(\varpi_v)$ is known and $T_v$ alone carries the remaining information. Every later use of strong multiplicity one follows this rule. This also explains why Galois conjugation must conjugate the nebentype or central character together with the trace eigenvalues.

## 3. Rationality fields

### 3.1 The Hecke field is a number field

Let $\lambda:B\to\mathbf C$ be an occurring character. Since $B$ is finite-dimensional, its image $E_\lambda$ is a finite extension of $K$. Thus (1.5), although written using infinitely many good places, is a number field. This argument needs the rational arithmetic module $V$, but not yet an integral lattice.

**Theorem 3.1 (algebraicity and finiteness).** Every value $\lambda(b)$ with $b\in B$ is algebraic over $K$. The field $E_\lambda=\lambda(B)$ is finite over $K$, and

$$
[E_\lambda:K]\leq\dim_KB. \tag{3.1}
$$

**Proof.** Multiplication by $b$ on the finite-dimensional space $B$ has a monic characteristic polynomial in $K[X]$. Applying $\lambda$ to the Cayley--Hamilton identity shows that $\lambda(b)$ is a root. The image is a quotient of the finite-dimensional $K$-vector space $B$, so it is finite-dimensional. As the image of a unital homomorphism into a field it is a domain, hence a field. The dimension bound follows. $\square$

For a cohomological normalized newform $f$, the theorem identifies the Hecke field relative to $K$ with

$$
E_f=K(a_v(f),\omega_v(\varpi_v):v\notin\Sigma), \tag{3.2}
$$

in the raw normalization. Strong multiplicity one says that this good-place character names the complex representation, but Theorem 3.1 is what proves its arithmetic finiteness.

### 3.2 Finite generation by finitely many places

Although all good places are useful for recognizing a representation, only finitely many are needed to generate the acting algebra and its field of values.

**Proposition 3.2.** There is a finite set $S\subseteq\{v:v\notin\Sigma\}$ such that the images of $T_v,S_v^{\pm1}$ for $v\in S$ generate $B$ as a $K$-algebra. If an integral module $M$ is present, a possibly larger finite set generates $\mathbb T$ as an $R$-algebra. Consequently

$$
E_\lambda=K(\lambda(T_v),\lambda(S_v):v\in S). \tag{3.3}
$$

**Proof.** Enumerate the good operators. The $K$-subalgebras generated by the first $n$ form an increasing chain of $K$-subspaces of the finite-dimensional space $B$, so the chain stabilizes. This proves the rational assertion. When $M$ exists, Proposition 2.1 makes $\mathbb T$ a Noetherian $R$-module; the same ascending-chain argument with $R$-subalgebras proves the integral assertion. Applying $\lambda$ proves (3.3). $\square$

This statement is not an effective bound on the primes in $S$. It says that the algebraic packet is finite data even though its most natural label is an infinite Hecke sequence.

### 3.3 Field of rationality versus field of definition

The residue field $E_\lambda$ in (1.5) is relative to the chosen base $K$. If $K$ was enlarged merely to write matrices, it need not be the intrinsic rationality field. Define instead the **absolute Hecke field**

$$
E_\pi^{\mathrm{abs}}
=\mathbf Q(t_v,s_v:v\notin\Sigma), \tag{3.4}
$$

Both coefficients are retained in this absolute field. Fixing a central character lets trace eigenvalues alone recognize representations inside that fixed-character family, but it does not remove the central-character values from the intrinsic absolute rationality field. Under the conjugation-compatible arithmetic structure of Book 92, define the rationality field of $\pi_f$ by

$$
\mathbf Q(\pi_f)
=\mathbf C^{\{\sigma\in\operatorname{Aut}(\mathbf C):{}^\sigma\!\pi_f\simeq\pi_f\}}. \tag{3.5}
$$

Here ${}^\sigma\!\pi_f$ is constructed by conjugating the arithmetic eigensystem, not by applying $\sigma$ to an arbitrary analytic representation model. A field of definition is a subfield $L\subset\mathbf C$ carrying an $L$-vector space and group action whose scalar extension is $\pi_f$. A one-dimensional eigencharacter is defined over its value field, but an irreducible representation need not descend to its rationality field: a nontrivial central division algebra can obstruct descent to its center.

For $\mathrm{GL}_2$, the good algebraic Hecke polynomials determine $\pi$ by strong multiplicity one. Hence the stabilizer of their full system equals the stabilizer of the isomorphism class, and

$$
\mathbf Q(\pi_f)=E_\pi^{\mathrm{abs}}. \tag{3.6}
$$

Indeed, every automorphism fixing all polynomial coefficients fixes the isomorphism class by strong multiplicity one. Conversely, an isomorphism ${}^\sigma\!\pi_f\simeq\pi_f$ identifies every unramified spherical character and therefore fixes all coefficients generating $E_\pi^{\mathrm{abs}}$. The two stabilizers are equal, and the fixed field of the pointwise stabilizer of a number field inside $\mathbf C$ is that number field. If the relative module is over $K$, then $E_\lambda=K E_\pi^{\mathrm{abs}}$ provided its scalar field is included in the acting algebra. This conclusion concerns the isomorphism class; it does not furnish a model of every local factor over either field.

### 3.4 A descent theorem for an eigenline

The minimal newvector is the setting in which descent is elementary and exact.

**Theorem 3.3 (eigenline descent).** Let $B$ be a finite-dimensional commutative $K$-algebra acting on a finite-dimensional $K$-space $V$, let $\lambda:B\twoheadrightarrow E$ be a character whose image is the finite extension $E/K$, and suppose

$$
\dim_E V_\lambda=1.
$$

Then $V_\lambda$ is an $E$-defined line. For every $K$-embedding $\iota:E\hookrightarrow\mathbf C$,

$$
V_\lambda\otimes_{E,\iota}\mathbf C
\cong V_{\iota\lambda}\subset V\otimes_K\mathbf C. \tag{3.7}
$$

**Proof.** The equations $(b-\lambda(b))x=0$ defining $V_\lambda$ have coefficients in $E$. Since $B$ is finite-dimensional, finitely many equations suffice. Their common kernel is therefore an $E$-subspace. Base extension along the flat map $E\to\mathbf C$ commutes with this finite kernel, giving (3.7). The assumed dimension makes the kernel a line. $\square$

The theorem descends the eigenline because it is defined by linear equations. It does not descend the entire smooth representation generated by that line unless the group action and all required intertwiners are also known to descend.

## 4. Galois conjugation and the packet orbit

### 4.1 Semilinear conjugation of modules

If $E\subset\mathbf C$ and $\sigma:E\hookrightarrow\mathbf C$ is an embedding, the conjugate of an $E$-space $W$ is

$$
{}^\sigma W=W\otimes_{E,\sigma}\mathbf C. \tag{4.1}
$$

This construction is semilinear in coefficients. If matrices $A_t\in M_n(E)$ describe commuting operators, their conjugates are obtained by applying $\sigma$ entrywise. It follows immediately that a vector satisfying $A_tv=\lambda(t)v$ gives, after scalar extension, a vector satisfying

$$
{}^\sigma A_t({}^\sigma v)=\sigma(\lambda(t)){}^\sigma v. \tag{4.2}
$$

The infinity type is not conjugated by applying $\sigma$ to analytic functions. It is transported through its algebraic coefficient system. For parallel weight two that coefficient system is defined over the chosen base field, so the weight remains weight two.

### 4.2 Conjugating an eigensystem

**Theorem 4.1 (existence of relative conjugates).** Let $V$ be a finite Hecke module defined over $K$, let its acting algebra $B$ be reduced, and let $\lambda:B\twoheadrightarrow E$ be an occurring character whose image is $E$. For every $K$-embedding $\iota:E\hookrightarrow\mathbf C$, the character $\iota\lambda$ occurs in $V\otimes_K\mathbf C$, with the same geometric multiplicity.

**Proof strategy.** Use the primitive field factor of the reduced Hecke algebra, rather than conjugating a chosen complex vector with no rational coordinates.

**Proof.** Let $\mathfrak p=\ker\lambda$. The factor $B/\mathfrak p$ is $E$. The $\mathfrak p$-component of $V$ is an $E$-space $W$. After tensoring with $\mathbf C$ over $K$,

$$
W\otimes_K\mathbf C
\cong\bigoplus_{\substack{\iota:E\hookrightarrow\mathbf C\\ \iota|_K=\mathrm{id}}}
W\otimes_{E,\iota}\mathbf C.
$$

On the $\iota$th summand, $t$ acts as $\iota(\lambda(t))$. Every summand has dimension $\dim_EW$, proving occurrence and equality of multiplicities. $\square$

### 4.3 The finite orbit and its stabilizer

The $K$-embeddings of $E_\lambda$ give exactly $[E_\lambda:K]$ distinct characters: if two embeddings agree on every $\lambda(t)$, they agree on the field generated by those values. Thus the relative packet orbit is finite and transitive under the embeddings of a normal closure. For the absolute orbit one first uses a $\mathbf Q$-model, as explained in Section 1.2; a module over an auxiliary $K$ cannot by itself produce embeddings that move $K$.

Let $L/K$ be a normal closure of $E_\lambda$. Then $\operatorname{Gal}(L/K)$ acts on the characters by

$$
(\sigma\lambda)(t)=\sigma(\lambda(t)). \tag{4.3}
$$

The stabilizer is $\operatorname{Gal}(L/E_\lambda)$, so orbit--stabilizer recovers the degree. This is the precise Galois content of the phrase “all conjugates of the form.” It concerns algebraic eigenvalues and their eigenspaces.

### 4.4 Conjugation of automorphic representations

For a cohomological $\mathrm{GL}_2$ eigensystem in a conjugation-compatible arithmetic module, Theorem 4.1 constructs a conjugate eigenform and hence a cuspidal representation $\pi^\iota$. Here $\iota$ is a $K$-embedding in the relative setting and an arbitrary coefficient embedding when the module has first been placed over $\mathbf Q$. At every $v\notin\Sigma$,

$$
P_v(\pi^\iota;X)=
1-\iota(t_v)X+q_v\iota(s_v)X^2
=\iota(P_v(\pi;X)), \tag{4.4}
$$

where $q_v\in\mathbf Z$ is fixed. Strong multiplicity one proves uniqueness of $\pi^\iota$. Once uniqueness is known globally, its ramified factors are not choices: uniqueness of restricted tensor factors gives a determined $\pi_v^\iota$ at every place.

For a quaternionic finite module the same linear algebra gives a conjugate good-place block. Unless a theorem identifies near-equivalent constituents, it is not legitimate to write a canonically determined $\pi^\iota$ for one constituent. Book 107 retains this distinction throughout.

## 5. Integral eigenvalues and eigenlattices

### 5.1 Integrality from a stable lattice

Algebraicity becomes integrality because the Hecke operators preserve a lattice.

**Theorem 5.1 (integral eigenvalues).** Let $R$ be integrally closed with fraction field $K$, let $M$ be finite projective over $R$, and let $t\in\operatorname{End}_R(M)$. Every eigenvalue of $t$ on $M\otimes_K\overline K$ is integral over $R$. If $R$ is the ring of integers of a number field, the eigenvalue is an algebraic integer.

**Proof.** The characteristic polynomial $\det(X-t\mid M)$ is defined locally on $\operatorname{Spec}R$ and glues to a monic polynomial in $R[X]$. Every eigenvalue is a root, hence integral over $R$. For a number ring, its integral closure in $\overline K$ consists of algebraic integers. $\square$

Thus $t_v$ and $s_v$ are algebraic integers whenever the raw operators preserve the chosen lattice. If $S_v^{-1}$ also preserves it, $s_v$ is a unit in the relevant integer ring. The factor $q_v$ in (1.2) is therefore exactly compatible with integral coefficients.

### 5.2 The saturated intersection lattice

Let $E/K$ be finite, let $\mathcal O_E$ be its ring of integers, and set

$$
M_E=M\otimes_R\mathcal O_E,
\qquad V_E=M\otimes_R E.
$$

For an $E$-subspace $W\subset V_E$, define

$$
L(W)=W\cap M_E. \tag{5.1}
$$

**Proposition 5.2 (intersection lattice).** The module $L(W)$ is finite projective of rank $\dim_EW$, spans $W$ over $E$, and is saturated in $M_E$: if $0\ne a\in\mathcal O_E$ and $ax\in L(W)$ for $x\in M_E$, then $x\in L(W)$.

**Proof.** The intersection is a submodule of the finite projective module $M_E$, hence finite and torsion-free, so it is projective over the Dedekind domain $\mathcal O_E$. Choose an $E$-basis of $W$. Clearing denominators places nonzero multiples of all basis vectors in $M_E$, proving that $L(W)$ spans $W$. Its rank is therefore $\dim_EW$. If $ax\in W$ and $a\ne0$, then $x=a^{-1}(ax)\in W$, which proves saturation. $\square$

For $W=V_\lambda$, this lattice is stable under $\mathbb T$: both $M_E$ and $V_\lambda$ are stable. It is canonical relative to the ambient integral module, not relative to the abstract complex representation alone.

### 5.3 Rank one, fractional ideals, and homothety

If $V_\lambda$ is one dimensional, every full $\mathcal O_E$-lattice in it is a projective rank-one module, hence a fractional ideal after a choice $V_\lambda\simeq E$. Two such lattices are commensurable. They are related by a scalar in $E^\times$ precisely when their ideal classes agree.

This gives the right formulation of a canonical newform lattice. The intersection $L_\lambda=M_E\cap V_\lambda$ is canonical inside the fixed ambient $M_E$. Choosing a nonzero vector $f_\lambda\in V_\lambda$ identifies it with a fractional ideal

$$
\mathfrak a_\lambda={a\in E:af_\lambda\in L_\lambda\}. \tag{5.2}
$$

Replacing $f_\lambda$ by $cf_\lambda$ replaces $\mathfrak a_\lambda$ by $c^{-1}\mathfrak a_\lambda$. Thus the module and its ideal class are intrinsic; a generator is not, unless the ideal is principal and a unit normalization is chosen. A Whittaker condition such as first coefficient $1$ can choose a vector over $E$, but it does not force the corresponding lattice to be free on that vector at every coefficient prime.

### 5.4 Denominators of projectors

Let $e_\lambda\in\mathbb T_E$ be the primitive idempotent isolating $\lambda$. Then $e_\lambda(V_E)=V_\lambda$, and $e_\lambda(M_E)$ is a full lattice in $V_\lambda$, but it need not be contained in $M_E$. Define its denominator ideal by

$$
\mathfrak d(e_\lambda)=
\{a\in\mathcal O_E:ae_\lambda(M_E)\subseteq M_E\}. \tag{5.3}
$$

This is a nonzero ideal: $\operatorname{End}_{\mathcal O_E}(M_E)$ is a full projective lattice in $\operatorname{End}_E(V_E)$, so a nonzero element of $\mathcal O_E$ carries $e_\lambda$ into that lattice. Equivalently, cover $\operatorname{Spec}\mathcal O_E$ by finitely many opens on which $M_E$ is free and clear the finitely many matrix denominators. It is the unit ideal exactly when the generic packet is an integral direct summand under this projector.

**Example.** In the order

$$
A_n=\{(x,y)\in\mathcal O_E^2:x\equiv y\pmod{\varpi^n}\},
$$

the generic projector $(1,0)$ becomes integral only after multiplication by $\varpi^n$: one has $a(1,0)\in A_n$ exactly when $a\in(\varpi^n)$. More explicitly, $A_n$ is free on $1=(1,1)$ and $\epsilon=(\varpi^n,0)$, with relation $\epsilon^2=\varpi^n\epsilon$. Thus for $n>0$ its special fiber is $k[\bar\epsilon]/(\bar\epsilon^2)$, while its two generic projections are distinct. The calculation both exhibits the congruence and explains why one must distinguish the saturated intersection lattice from the image of a rational projector.

## 6. The integral packet and coefficient extension

### 6.1 The universal packet quotient

Let $\mathfrak p=\ker(\lambda:\mathbb T_K\to E)$. Its contraction to $\mathbb T$ need not have quotient equal to $\mathcal O_E$; the image is the **eigenvalue order**

$$
\mathcal O_\lambda=\lambda(\mathbb T)\subseteq\mathcal O_E. \tag{6.1}
$$

It is finite and torsion-free over $R$, has fraction field $E$, and can be nonmaximal. The universal integral packet module is

$$
M[\lambda]=M\otimes_{\mathbb T,\lambda}\mathcal O_\lambda. \tag{6.2}
$$

Tensoring with $E$ gives the maximal quotient on which $t$ acts as $\lambda(t)$. This quotient should not be confused with the intersection lattice $L_\lambda$, which is a submodule of the ambient generic eigenspace. In a self-dual semisimple situation the two are related by the pairing; without such a hypothesis neither determines the other integrally.

### 6.2 Flat base change and embedding components

Let $R\to R'$ be flat. Then the injection $\mathbb T\hookrightarrow\operatorname{End}_R(M)$ remains injective after tensoring, and because $M$ is projective,

$$
\operatorname{End}_R(M)\otimes_RR'
\cong\operatorname{End}_{R'}(M\otimes_RR'). \tag{6.3}
$$

Thus $\mathbb T\otimes_RR'$ is exactly the algebra generated by the base-changed operators. Finite extensions of number fields and localizations at nonzero primes are flat, so characteristic-zero packet formation commutes with both.

For a normal field $L$ containing the images of every $K$-embedding of $E$, the packet factor splits:

$$
E\otimes_KL
\cong\prod_{\substack{\iota:E\hookrightarrow L\\ \iota|_K=\mathrm{id}}}L. \tag{6.4}
$$

The corresponding idempotents decompose its generic realization into the $\iota\lambda$-components. Equation (6.4) is the exact algebra behind compatibility with coefficient embeddings.

### 6.3 Localization at a coefficient prime

Fix a prime $\Lambda$ of $E$ above a rational prime $\ell$. The localized eigenlattice

$$
L_{\lambda,\Lambda}=L_\lambda\otimes_{\mathcal O_E}\mathcal O_{E,\Lambda} \tag{6.5}
$$

is finite free because a local Dedekind domain is a DVR. If $V_\lambda$ is a line, then $L_{\lambda,\Lambda}$ has a generator, unique up to $\mathcal O_{E,\Lambda}^\times$. This is the natural local integral structure attached to the packet and the ambient lattice.

If $\mathfrak d(e_\lambda)$ is prime to $\Lambda$, the projector is integral after localization and $L_{\lambda,\Lambda}$ is a direct summand of $M\otimes\mathcal O_{E,\Lambda}$. If $\Lambda$ divides the denominator ideal, distinct generic branches can meet in the special fiber. The lattice still exists, but integral splitting fails.

The direct-summand assertion has a useful elementary proof. Choose $a\in\mathfrak d(e_\lambda)$ that is a unit at $\Lambda$. Then $ae_\lambda$ preserves the localized ambient lattice, and multiplication by $a^{-1}$ shows that $e_\lambda$ itself preserves it. Hence

$$
M_\Lambda=e_\lambda M_\Lambda\oplus(1-e_\lambda)M_\Lambda. \tag{6.6}
$$

The first summand has generic fiber $V_\lambda$ and is saturated, so it equals $L_{\lambda,\Lambda}$. Conversely, if the generic decomposition is induced by an integral idempotent, that idempotent has unit denominator at $\Lambda$. Thus the support of $\mathfrak d(e_\lambda)$ is exactly the set of coefficient primes at which this particular generic projector fails to extend integrally.

There can be several primes $\Lambda$ above the same rational prime $\ell$. Localizing at one of them selects an embedding of the coefficient field into an algebraic closure of $\mathbf Q_\ell$ up to decomposition group. The resulting lattices are scalar extensions of the same global projective $\mathcal O_E$-module, but they need not be isomorphic after forgetting their $E_\Lambda$-structure. Ramification indices and residue degrees alter their underlying $\mathbf Z_\ell$-ranks. The packet therefore carries a family indexed by coefficient primes, not one unnamed “$\ell$-adic lattice.”

### 6.4 Congruence does not identify characteristic-zero packets

Reduction modulo $\Lambda$ is not flat. The map

$$
\mathbb T\otimes\mathbf F_\Lambda
\longrightarrow
\operatorname{End}_{\mathbf F_\Lambda}(M\otimes\mathbf F_\Lambda) \tag{6.7}
$$

can have a kernel if the inclusion of $\mathbb T$ in the endomorphism module is not saturated. Moreover, two distinct characters $\lambda_1,\lambda_2$ can have the same reduction.

The crossing order $A_n$ shows both phenomena geometrically: its two generic points are separate, while its special fiber has one point and, for $n>0$, nilpotent thickening. A congruence means that algebraic integers agree to positive valuation. It does not make their characteristic-zero representations isomorphic, and it does not give congruent eigenvectors unless the module and its lattice are controlled. This boundary will matter when period lattices are localized.

## 7. Weight two and cohomological rational structures

### 7.1 Why weight two belongs in degree one

The preceding chapters apply to any algebraic eigensystem. Weight two becomes special when the same Hecke algebra acts on degree-one cohomology. A smooth proper complex curve $X$ has

$$
H^1_B(X,\mathbf Q)\otimes_\mathbf Q\mathbf C
=H^{1,0}(X)\oplus H^{0,1}(X), \tag{7.1}
$$

with $H^{1,0}(X)=H^0(X,\Omega_X^1)$. Holomorphic differentials transform with the automorphy factor of weight two. This is the geometric reason that weight-two forms can be realized as the Hodge line of a degree-one rational structure.

We isolate the exact input instead of assuming that every automorphic module is already geometric.

**Definition 7.1 (degree-one weight-two realization).** Fix an embedding $j:K\hookrightarrow\mathbf C$. A degree-one cohomological realization of an algebraic packet $[\lambda]_K$ consists of:

1. a finite-dimensional $K$-space $H_{\mathrm{dR}}$ with a two-step filtration
   $$0\subset F^1H_{\mathrm{dR}}\subset H_{\mathrm{dR}};$$
2. a finite-dimensional $K$-space $H_B$ with a $K$-linear involution $c$;
3. commuting $K$-linear Hecke actions that preserve $F^1$, commute with $c$, and have the same character on corresponding factors;
4. a Hecke-equivariant comparison isomorphism
   $$
   I:H_B\otimes_{K,j}\mathbf C
   \xrightarrow{\sim}
   H_{\mathrm{dR}}\otimes_{K,j}\mathbf C; \tag{7.2}
   $$
5. on the packet factor, a Hodge decomposition of types $(1,0)$ and $(0,1)$, with $F^1=H^{1,0}$, such that the transported $\mathbf C$-linear involution $IcI^{-1}$ exchanges $H^{1,0}$ and $H^{0,1}$.

For a smooth proper curve, Book 27 supplies the Betti--de Rham comparison, its Hodge decomposition, and compatibility with Hecke correspondences. Its rational Betti space can be tensored with $K$. A real model, or a specified descent datum identifying the complex curve with its conjugate, supplies the involution in items 2 and 5; an arbitrary curve over a nonreal subfield of $\mathbf C$ does not automatically carry such a self-involution. In a smooth proper family, Book 52 supplies the de Rham bundle, its Hodge filtration, arbitrary base change, pairing, and Gauss--Manin connection. Thus each item above is genuine prior geometry or an explicit hypothesis, rather than a consequence of the adjective “automorphic.”

### 7.2 A rational Hodge--Hecke module

Let $E=E_\lambda$ and fix a $K$-embedding $\iota:E\hookrightarrow\mathbf C$ extending $j$. The $\iota$-component of the packet is cut out by the equations

$$
(T_v-\iota(t_v))x=(S_v-\iota(s_v))x=0. \tag{7.3}
$$

Suppose first that the packet has multiplicity one in each Hodge direction. Then

$$
\dim_\mathbf C H_{\mathrm{dR},\iota}=2,
\qquad
\dim_\mathbf C F^1H_{\mathrm{dR},\iota}=1. \tag{7.4}
$$

The involution carries its Hodge line isomorphically onto a line of type $(0,1)$. Let $H_E$ denote the field-factor module before choosing an embedding. It has rank two over $E$: after scalar extension to a normal closure, its $[E:K]$ embedding components all have dimension two. No one embedding component is rational over $K$; the whole relative orbit is.

The restriction of scalars

$$
\operatorname{Res}_{E/K}H_E \tag{7.5}
$$

is therefore the correct rational packet object. After tensoring with $\mathbf C$ it separates into all allowed coefficient embeddings. This construction prevents a frequent mistake: one conjugate eigenline by itself need not be defined over $K$, even though the direct sum of its conjugates is.

### 7.3 The packet summand and its Hodge line

Let $\mathfrak p=\ker\lambda$ in the reduced Hecke algebra. The packet summand is the $\mathfrak p$-factor of $H$. It can be described without choosing an idempotent by

$$
H[\mathfrak p]
=\{x:\mathfrak p^Nx=0\text{ for some }N\}. \tag{7.6}
$$

When the generic algebra is reduced, $N=1$ suffices. Because every Hecke operator preserves the Hodge filtration, the same factor cuts the exact sequence

$$
0\longrightarrow F^1H_E
\longrightarrow H_E
\longrightarrow H_E/F^1H_E
\longrightarrow0. \tag{7.7}
$$

In multiplicity one, both outer $E$-modules have rank one. The sequence need not split over $E$. Indeed, the failure of an algebraic splitting to agree with the Betti rational structure is precisely what periods measure.

For a smooth proper curve, $F^1H_{\mathrm{dR}}=H^0(X,\Omega_X^1)$, and the quotient is $H^1(X,\mathcal O_X)$. Serre duality makes the two halves dual. The cup-product pairing is alternating and perfect, and finite correspondences act compatibly in de Rham and Betti cohomology.

### 7.4 Complex conjugation and signs

The involution $c$ on the Betti realization arises from complex conjugation on a real model or from the relevant orientation-reversing involution. Assume $c^2=1$ and characteristic zero. Then

$$
H_B=H_B^+\oplus H_B^-,
\qquad H_B^\pm=\ker(c\mp1). \tag{7.8}
$$

For a rank-two degree-one packet satisfying Definition 7.1, each sign component has rank one over $E$. Indeed, if $0\ne u\in H^{1,0}$, then $c(u)\in H^{0,1}$ and the vectors $u+c(u)$ and $u-c(u)$ are nonzero vectors of signs $+$ and $-$ respectively. They span the two-dimensional space.

The same calculation proves transversality. If a nonzero holomorphic class lay in a sign line, applying $c$ would leave it in that line up to sign while moving it into $H^{0,1}$. Since the Hodge decomposition is direct, this is impossible. Thus projection of the Hodge line onto each sign line is nonzero. Those two nonzero projections produce the two periods. This conclusion uses item 5 of Definition 7.1; it is false for a bare involution unrelated to the Hodge structure.

## 8. Comparison isomorphisms and period lines

### 8.1 The comparison datum

Fix an embedding $j:K\hookrightarrow\mathbf C$. For a smooth proper curve $X/K$, Book 27 constructs the de Rham-to-Betti comparison by integration. We use its inverse and write

$$
I_j:H^1_B(X_j(\mathbf C),\mathbf Q)\otimes\mathbf C
\xrightarrow{\sim}
H^1_{\mathrm{dR}}(X/K)\otimes_{K,j}\mathbf C. \tag{8.1}
$$

It is functorial for pullback and trace, hence for finite correspondences. Therefore the Hecke packet summands on the two sides correspond. If an integral correspondence defines $T$, then it preserves $H^1_B(X,\mathbf Z)$, and its characteristic polynomial lies in $\mathbf Z[X]$ and agrees in both realizations.

There is no canonical map $H_B\to H_{\mathrm{dR}}$ before tensoring with $\mathbf C$. The comparison isomorphism is the bridge, and its matrix entries are periods. Different embeddings $j$ are separate comparison data; a choice of an abstract field isomorphism between $\mathbf C$ and an $\ell$-adic field is neither present nor needed.

### 8.2 Periods as comparison scalars

Let $H_{E,B}$ be the rank-two $E$-packet in Betti cohomology, with rank-one sign spaces $H_{E,B}^\pm$. Let $F^1H_{E,\mathrm{dR}}$ be its rank-one de Rham Hodge line. Choose $E$-rational bases

$$
b^\pm\in H_{E,B}^\pm,
\qquad
\omega\in F^1H_{E,\mathrm{dR}}. \tag{8.2}
$$

For a $K$-embedding $\iota:E\hookrightarrow\mathbf C$, let $b_\iota^\pm$ and $\omega_\iota$ denote their scalar extensions. Transport $\omega_\iota$ to Betti cohomology through $I^{-1}$. Since both sign projections are nonzero, there are unique $\Omega_\iota^\pm\in\mathbf C^\times$ such that

$$
I^{-1}(\omega_\iota)
=\Omega_\iota^+b_\iota^+
+\Omega_\iota^-b_\iota^-. \tag{8.3}
$$

These are the **signed periods** of the chosen $E$-bases. Requiring the bases to be $E$-rational is essential: arbitrary nonzero complex vectors could rescale the alleged periods by arbitrary elements of $\mathbf C^\times$ and would destroy the quotient invariant below. Formula (8.3), rather than a bare integral symbol, records what a period compares: one holomorphic algebraic line with two rational topological lines.

In the classical modular-form normalization, $\omega_f=2\pi i f(z)\,dz$ is algebraic as a differential once the algebraic model is fixed, and evaluation on cycles gives integrals of $2\pi i f(z)\,dz$. If $f(z)=\sum_{n\ge1}a_ne^{2\pi inz}$, the factor $2\pi i$ is forced by $dq/q=2\pi i\,dz$; omitting it changes which de Rham class is algebraic.

### 8.3 Basis independence and the period class

Replacing $\omega_\iota$ by $a\omega_\iota$ and $b_\iota^\pm$ by $u_\pm b_\iota^\pm$, with $a,u_\pm\in\iota(E)^\times$, changes

$$
\Omega_\iota^\pm\longmapsto au_\pm^{-1}\Omega_\iota^\pm. \tag{8.4}
$$

Thus an individual scalar is not canonical. Its class

$$
[\Omega_\iota^\pm]\in\mathbf C^\times/\iota(E)^\times \tag{8.5}
$$

is canonical once the three $E$-lines and comparison map are fixed.

**Proposition 8.1 (well-defined signed period class).** Under the rank-one hypotheses above, (8.5) is independent of all $E$-bases. It is functorial under an isomorphism of cohomological realizations defined over $E$, meaning an isomorphism that respects the Hecke action, filtration, involution, and comparison map.

**Proof.** Every change of basis in a one-dimensional $E$-space is multiplication by an element of $E^\times$, so (8.4) changes the scalar by an element of $\iota(E)^\times$. A Hecke-equivariant $E$-isomorphism changes each chosen basis by such a scalar and commutes with comparison; hence it preserves the quotient class. $\square$

The construction can also be phrased without any bases. Let

$$
\mathcal L_{\mathrm{dR}}=F^1H_{E,\mathrm{dR}},
\qquad
\mathcal L_B^\pm=H_{E,B}^\pm. \tag{8.6}
$$

Projection along the opposite Betti sign gives nonzero complex maps

$$
p_\iota^\pm I^{-1}:
\mathcal L_{\mathrm{dR}}\otimes_{E,\iota}\mathbf C
\longrightarrow
\mathcal L_B^\pm\otimes_{E,\iota}\mathbf C. \tag{8.7}
$$

Thus the signed period is intrinsically the nonzero element

$$
\operatorname{Per}_\iota^\pm
\in
\operatorname{Hom}_\mathbf C(
\mathcal L_{\mathrm{dR},\iota},\mathcal L_{B,\iota}^\pm), \tag{8.8}
$$

considered relative to its $E$-rational source and target lines. With the direction in (8.7), choosing the bases in (8.2) turns (8.8) into $\Omega_\iota^\pm$. The quotient class removes algebraic changes of those bases. The line formulation is preferable when the coefficient ideal class is nontrivial, because then neither rational line need have a global integral generator.

For a curve with the real structure required in Definition 7.1, the nonvanishing of (8.7) is a Hodge-theoretic fact, not a normalization assumption. If the plus projection vanished, the holomorphic class would lie in the minus line. Applying the geometric involution would negate it while carrying it from type $(1,0)$ to type $(0,1)$. A nonzero class cannot lie in both types because the Hodge decomposition is direct. The same argument applies to the minus projection. Analytically, positivity of

$$
i\int_X\omega\wedge\overline\omega>0 \tag{8.9}
$$

gives the same conclusion: if all periods in one sign direction vanished, the Riemann bilinear relation would force the positive norm to vanish.

In a supplied modular-curve realization, one may see the two signs on modular symbols. An oriented path from one cusp to another defines a relative homology class, and the involution induced by reflection decomposes it into plus and minus parts. Integration sends the path to

$$
\int_\alpha^\beta 2\pi i f(z)\,dz. \tag{8.10}
$$

Hecke correspondences act both on paths and on differentials, and change of variables proves

$$
\int_{T\gamma}\omega_f=\int_\gamma T^*\omega_f. \tag{8.11}
$$

Therefore the integration functional is Hecke equivariant. Once the relevant eigenspaces are lines, (8.11) forces every such integral in a fixed sign to be an algebraic multiple of one nonzero period. This is the operational content of the signed period theorem.

If integral lattices are fixed, one may restrict allowable basis changes to units after localization. The resulting complex period is then well defined modulo $\iota(\mathcal O_{E,\Lambda}^\times)$. This does **not** give a canonical $\Lambda$-adic valuation of a transcendental complex period: only algebraic transition factors, lattice indices, and projector denominators carry such valuations without an additional comparison into a valued field.

### 8.4 Determinant periods in higher multiplicity

Oldspaces and ramified type spaces can make the relevant multiplicity $m>1$. A scalar period is then the wrong invariant. Let $W_{\mathrm{dR}}$ and $W_B$ be $m$-dimensional $E$-spaces and let

$$
I:W_B\otimes_{E,\iota}\mathbf C
\xrightarrow{\sim}
W_{\mathrm{dR}}\otimes_{E,\iota}\mathbf C.
$$

To retain the direction used for signed periods, take the top exterior power of $I^{-1}$. Its scalar in chosen $E$-bases has a well-defined class

$$
\Delta_\iota(I^{-1})\in\mathbf C^\times/\iota(E)^\times. \tag{8.12}
$$

**Proposition 8.2.** The class (8.12) is independent of bases and is multiplicative in exact sequences preserved by $I$.

**Proof.** A basis change multiplies the comparison determinant by the quotient of two determinants in $\iota(E)^\times$. For a compatible short exact sequence, choose bases adapted to subspace and quotient. The comparison matrix is block upper triangular, so its determinant is the product of the two diagonal determinants. $\square$

Signed scalar periods are the $m=1$ case after projecting to a sign. Determinant periods retain the theory without falsely claiming one-dimensionality.

## 9. Integral periods and coefficient embeddings

### 9.1 Integral Betti and de Rham lattices

For a smooth proper complex curve, $H^1_B(X,\mathbf Z)$ is free and the cup-product pairing is unimodular. Let $H_{B,\mathbf Z}$ denote this lattice. A smooth proper model over a characteristic-zero number ring may supply an algebraic de Rham lattice $H_{\mathrm{dR},\mathcal O}$; when no such model is specified, one must regard only the $K$-space $H_{\mathrm{dR}}$ as canonical.

Assume now that both lattices are given and stable under the integral Hecke order. Intersecting their scalar extensions with the packet subspaces gives

$$
L_{B,\lambda}=(H_{B,\mathbf Z}\otimes_{\mathbf Z}\mathcal O_E)\cap H_{E,B},
\qquad
L_{\mathrm{dR},\lambda}=(H_{\mathrm{dR},\mathcal O}\otimes_R\mathcal O_E)\cap H_{E,\mathrm{dR}}. \tag{9.1}
$$

By Proposition 5.2 these are saturated projective lattices. Their Hodge and sign intersections are rank-one projective modules in the multiplicity-one case. They need not be globally free over $\mathcal O_E$.

There is a separate integral sign-splitting issue. Suppose $c$ preserves $L_{B,\lambda}$, and put $L_{B,\lambda}^\pm=L_{B,\lambda}\cap H_{E,B}^\pm$. Then

$$
2L_{B,\lambda}
\subseteq L_{B,\lambda}^+\oplus L_{B,\lambda}^-
\subseteq L_{B,\lambda}. \tag{9.2}
$$

The first inclusion follows from $2x=(x+cx)+(x-cx)$. Away from primes above $2$, the idempotents $(1\pm c)/2$ are integral and both inclusions become equality after localization. At a prime above $2$, the middle lattice can have nontrivial finite index in the full Betti lattice. Rank-one sign lines therefore do not by themselves provide an integral Betti basis at every coefficient prime.

The comparison map does not usually carry one integral lattice onto the other: it is defined over $\mathbf C$, and the defect is the period matrix. This failure is expected, not an integrality defect in either realization.

### 9.2 The period matrix of a packet

Choose a local de Rham basis at $\Lambda$ whose first vector generates the Hodge intersection, choose generators of the two localized sign lattices, and extend them along $\iota:E\hookrightarrow\mathbf C$. Relative to the de Rham basis and the sign generators, the map $I^{-1}$ has a matrix

$$
\mathcal P_{\iota}=
\begin{pmatrix}
\Omega_\iota^+&*\\
\Omega_\iota^-&*
\end{pmatrix}. \tag{9.3}
$$

The first column represents the holomorphic line and the second a complementary de Rham line. Changing the adapted de Rham basis or either sign generator changes the determinant only by $\iota(\mathcal O_{E,\Lambda}^\times)$, while the individual entries depend on the complement. If the sign splitting is integral, the two sign generators are a Betti lattice basis and $\mathcal P_\iota$ is an integral-lattice period matrix. Otherwise it is the period matrix relative to the finite-index sign sublattice; comparison with a basis of the full Betti lattice introduces precisely the elementary divisors of

$$
L_{B,\lambda}/(L_{B,\lambda}^+\oplus L_{B,\lambda}^-).
$$

Under the stability hypothesis of Section 9.1 this quotient is supported above $2$, and it must not be absorbed into a claimed period unit.

For a genus-$g$ curve, the full period matrix is obtained by integrating a basis of holomorphic forms over a symplectic basis of $H_1$. Its normalized form $(I_g\ \tau)$ has $\tau$ symmetric with positive definite imaginary part. On a packet factor, the same positivity ensures the two signed projections in (8.3) are nonzero.

### 9.3 Changing the coefficient embedding

Let $L$ be a normal closure of $E/K$. The algebraic packet module over $L$ decomposes as

$$
H_E\otimes_KL
\cong\bigoplus_{\substack{\iota:E\hookrightarrow L\\ \iota|_K=\mathrm{id}}}H_\iota. \tag{9.4}
$$

Every Hecke operator acts on $H_\iota$ through the conjugate character $\iota\lambda$, and the Hodge filtration, sign decomposition, and pairings commute with this field extension. Each projective $\mathcal O_E$-lattice also has a well-defined base change along $\iota:\mathcal O_E\to\mathcal O_L$. However, the direct-sum decomposition (9.4) need not descend to a direct-sum decomposition over $\mathcal O_L$: the embedding idempotents can have denominators at primes dividing the discriminant or the packet-projector ideal. Integral splitting is asserted only after those denominators are inverted. Therefore the family

$$
\bigl(H_\iota,F^1H_\iota,H_\iota^+,H_\iota^-,
[\Omega_\iota^+],[\Omega_\iota^-]\bigr)_\iota \tag{9.5}
$$

is compatible with relative coefficient embeddings in the precise algebraic sense: the same $E$-linear construction, base-changed along every $K$-embedding, produces every member. For the absolute package with $K=\mathbf Q$, these are all coefficient embeddings.

If $\sigma\in\operatorname{Gal}(L/K)$, it permutes the algebraic summands by $H_\iota\mapsto H_{\sigma\iota}$ and sends Hecke eigenvalues accordingly. This is a statement about the algebraic spaces. The comparison maps for the chosen complex embeddings then supply the corresponding period classes separately.

### 9.4 What Galois conjugation does not say about periods

It is tempting to write

$$
\Omega_{\sigma\iota}^\pm=\sigma(\Omega_\iota^\pm)
$$

for every $\sigma\in\operatorname{Aut}(\mathbf C)$. Without extra motivic descent data, this formula is not meaningful as a theorem. Betti cohomology depends on the complex topology associated with an embedding, and a wild automorphism of $\mathbf C$ is not a continuous map of that topology. Moreover, $\Omega_\iota^\pm$ is defined only modulo $\iota(E)^\times$.

What has been proved is both weaker and correct: algebraic conjugation carries the de Rham eigensystem and its algebraic lattice to the conjugate eigensystem, while comparison at each embedding yields a period line. In a realization equipped with the real structure of Definition 7.1, complex conjugation is exceptional because it is a continuous involution of the complex points and genuinely acts on Betti cohomology; its consequences are proved in Chapter 10.

## 10. Pairings, dual packets, and polarizations

### 10.1 Adjoint Hecke actions

Let $H$ carry a perfect bilinear pairing

$$
\langle\ ,\ \rangle:H\times H^\vee\longrightarrow R \tag{10.1}
$$

and suppose the Hecke algebra is stable under an involution $t\mapsto t^*$ satisfying

$$
\langle tx,y\rangle=\langle x,t^*y\rangle. \tag{10.2}
$$

For a correspondence $\Gamma$, the adjoint is its transpose; for a double coset $[UaU]$, it is $[Ua^{-1}U]$, with the central-character correction dictated by the chosen pairing. This formula must be retained at oriented level, where an operator need not equal its adjoint.

If $x$ has character $\lambda$, then for every $y$ in a $\mu$-eigenspace,

$$
\lambda(t)\langle x,y\rangle
=\mu(t^*)\langle x,y\rangle. \tag{10.3}
$$

Thus the pairing is zero unless $\mu(t^*)=\lambda(t)$ for all $t$. In the reduced semisimple generic setting, where the modules are direct sums of their character spaces, perfectness pairs the $\lambda$-space with the unique adjoint character

$$
\lambda^\vee(t)=\lambda(t^*). \tag{10.4}
$$

### 10.2 The dual eigensystem

For an automorphic representation, the dual packet belongs to the contragredient $\pi^\vee$, whose central character is $\omega_\pi^{-1}$. At an unramified place, if $\alpha_v,\beta_v$ are algebraic Satake roots, the roots for the dual are $\alpha_v^{-1},\beta_v^{-1}$ in the corresponding normalized convention. In raw Hecke variables it is safer to use (10.4), because central and modulus factors are then built into the adjoint double coset.

The rationality field of the dual equals that of the original packet: its eigenvalues are rational functions of the original roots with coefficients in the field generated by the central character, and dualizing twice reverses the containment. Integral dual lattices are

$$
L_\lambda^\#=\{y\in V_{\lambda^\vee}:\langle L_\lambda,y\rangle\subseteq\mathcal O_E\}. \tag{10.5}
$$

If the ambient pairing is perfect and the packet is an integral direct summand, then $L_\lambda^\#$ is the intersection lattice of the dual packet. If the projector has denominators, the two can differ by a finite module supported at congruence primes.

### 10.3 Period products from a perfect pairing

Assume the weight-two packet has a polarization pairing compatible with comparison. Choose $E$-bases $b^+,b^-$ of the sign lines such that

$$
\langle b^+,b^-\rangle=\delta\in E^\times,
\qquad
\langle b^+,b^+\rangle=\langle b^-,b^-\rangle=0. \tag{10.6}
$$

Let $\omega$ span $F^1$ and let $\eta$ be a complementary de Rham vector. Write their Betti coordinates under $I^{-1}$ as columns of a matrix $\mathcal P$. In the unnormalized algebraic de Rham convention fixed by Book 27, compatibility of cup products and top traces gives the exact identity

$$
\det(\mathcal P)\,\delta
=2\pi i\,\langle\omega,\eta\rangle_{\mathrm{dR}}. \tag{10.7}
$$

Indeed, the alternating Betti pairing of the two coordinate columns is $\det(\mathcal P)\delta$, while Book 27 proves that it is $2\pi i$ times the algebraic de Rham cup--trace pairing. Thus the determinant period is controlled by the ratio of two algebraic pairings with the displayed factor $2\pi i$. For an abstract comparison datum using a different top-trace convention, (10.7) must be replaced by the explicitly declared comparison multiplier; pairing compatibility alone does not license suppressing it.

Equation (10.7) does not generally determine $\Omega^+\Omega^-$, because the second column depends on $\eta$. With a polarized conjugate choice $\eta=\overline\omega$, it yields a relation between the determinant, the Petersson-type norm, and the signed periods. This relation is well defined only modulo $E^\times$, exactly as expected.

### 10.4 Complex conjugation and the two signs

Let $I^{-1}(\omega)=\Omega^+b^++\Omega^-b^-$. Two operations must be distinguished. The geometric involution $c$ is $\mathbf C$-linear after extension of scalars and acts on the sign basis by

$$
c(b^+)=b^+,
\qquad c(b^-)=-b^-. \tag{10.8}
$$

Therefore

$$
c\bigl(I^{-1}(\omega)\bigr)
=\Omega^+b^+-\Omega^-b^- \tag{10.9}
$$

The anti-linear real-structure operator $\kappa$ instead fixes rational Betti classes and conjugates scalars:

$$
\kappa\bigl(I^{-1}(\omega)\bigr)
=\overline{\Omega^+}b^++\overline{\Omega^-}b^- . \tag{10.10}
$$

Geometric hypotheses can relate the two operations. For example, if the chosen real structure gives

$$
c\bigl(I^{-1}(\omega)\bigr)
=\kappa\bigl(I^{-1}(\omega)\bigr), \tag{10.11}
$$

then comparison of (10.9) and (10.10) gives $\overline{\Omega^+}=\Omega^+$ and $\overline{\Omega^-}=-\Omega^-$. Thus the plus period is real and the minus period is purely imaginary in those bases. If the geometric relation includes algebraic basis factors, the same conclusion holds only after the corresponding allowed algebraic rescaling. Neither (10.9) nor (10.10) alone permits bars and the minus sign to be combined.

One cannot always impose those reality conditions simultaneously over a non-totally-real coefficient field. The invariant statements are (10.9)--(10.10), together with the classes in $\mathbf C^\times/\iota(E)^\times$. Positivity of the polarization controls the sign of the associated Hermitian form, not a canonical sign of either period scalar.

## 11. The $\mathrm{GL}_2$ weight-two packet

### 11.1 From a normalized newform to a packet

Let $F$ be totally real and let $\pi$ be an irreducible cuspidal automorphic representation of $\mathrm{GL}_2(\mathbf A_F)$ of parallel weight two, finite conductor $\mathfrak n$, and finite-order central character $\omega$ compatible with the infinity type. The algebraic and cohomological weight conventions are those fixed in Book 92. At every finite place choose the standard $K_1$ subgroup. The strong multiplicity-one and global newform package of Book 106 gives

$$
\dim_\mathbf C\pi_f^{K_1(\mathfrak n)}=1. \tag{11.1}
$$

Choose the Whittaker normalization in the algebraic convention, so the first nonzero global Whittaker coefficient is $1$. The resulting vector $f$ is a simultaneous eigenvector for the good Hecke algebra. Let $t_v(f),s_v(f)$ be its eigenvalues and define $E_f$ by (3.2).

The arithmetic input has two distinct layers. The conjugation-compatible number-field fixed-level model assumed in Book 92 is enough for Chapter 3 to prove that the relative Hecke field is a number field and for Chapter 4 to produce relative conjugates. To conclude that the raw eigenvalues are algebraic integers and to form the intersection lattice, one must additionally be given a common Hecke-stable lattice; that integral input is not proved in Book 92. Under this extra hypothesis, Chapter 5 proves integrality. The normalized vector belongs to the $E_f$-eigenline by Theorem 3.3. Its coefficient normalization chooses an $E_f$-basis of that line, while the intersection with the ambient integral module defines a possibly nonprincipal fractional ideal relative to this basis.

All statements may be read relative to a coefficient base $K$, in which case only $K$-embeddings of $E_f$ occur. For the full coefficient orbit, take the restriction-of-scalars package of the conjugate $q$-expansion spaces over $\mathbf Q$; then $E_f$ denotes the absolute field (3.4), including the central-character values, and the embeddings below are all $\mathbf Q$-embeddings. This extra sentence is not cosmetic: a single space with one fixed nonrational nebentype is not stable under embeddings that move that nebentype.

It is useful to separate three one-dimensional objects:

$$
\begin{array}{ccl}
E_f f&:&\text{the algebraic normalized eigenline},\\
L_f&:&\text{the integral intersection lattice},\\
\mathbf C f&:&\text{the analytic newform line at one embedding}.
\end{array} \tag{11.2}
$$

They become isomorphic after scalar extension, but they carry different information.

### 11.2 Strong multiplicity one after conjugation

For each allowed embedding $\iota:E_f\hookrightarrow\mathbf C$—a $K$-embedding in the relative setting and every embedding in the absolute setting—Theorem 4.1 produces a weight-two eigenform $f^\iota$ with

$$
t_v(f^\iota)=\iota(t_v(f)),
\qquad
s_v(f^\iota)=\iota(s_v(f)) \tag{11.3}
$$

for $v\notin\Sigma$. Let $\pi^\iota$ be the cuspidal representation it generates.

**Theorem 11.1 (unique conjugate representation).** The isomorphism class of $\pi^\iota$ is uniquely determined by (11.3). If two cuspidal representations of the same algebraic weight have those conjugate good polynomials outside a finite set, they are isomorphic.

**Proof strategy.** Turn equality of polynomial coefficients into equality of spherical local factors, then invoke strong multiplicity one.

**Proof.** At each unramified place under consideration, (11.3) gives equality of both coefficients of the raw spherical polynomial. Hence the unordered Satake pairs agree and the local representations are isomorphic. This holds outside a finite set. Strong multiplicity one for $\mathrm{GL}_2$ makes the global representations isomorphic. $\square$

The proof requires both coefficients unless the central character has already been fixed and conjugated. It also requires cuspidality. The conclusion would not follow merely from simultaneous diagonalization of one finite-level module.

### 11.3 Ramified components and newvectors

Although conjugation was defined from unramified data, Theorem 11.1 determines the full restricted tensor product. Uniqueness of local factors gives a unique isomorphism class

$$
\pi^\iota=\bigotimes_v'\pi_v^\iota \tag{11.4}
$$

and hence determines every ramified $\pi_v^\iota$. This is global determination, not an assertion that a wild automorphism can be applied entrywise to an arbitrary analytic model of $\pi_v$.

The conductor of $\pi^\iota$ equals that of $\pi$, provided the arithmetic module used here is the full fixed-weight cuspidal space at the minimal level $K_1(\mathfrak n)$. Indeed, strong multiplicity one and newvector uniqueness make the original good eigenspace in that full module one dimensional. Theorem 4.1 preserves its dimension under coefficient conjugation. Since $f^\iota$ occurs at level $\mathfrak n$, its conductor $\mathfrak m$ divides $\mathfrak n$. If the divisibility were strict at some place, the local newvector dimension formula of Book 106 would give

$$
\dim (\pi_f^\iota)^{K_1(\mathfrak n)}
=\prod_{v<\infty}\bigl(v(\mathfrak n)-v(\mathfrak m)+1\bigr)>1.
$$

All these oldvectors have the same good eigensystem, contradicting the preserved one-dimensional eigenspace. Therefore

$$
\mathfrak c(\pi^\iota)=\mathfrak c(\pi). \tag{11.5}
$$

At minimal level each conjugate finite newvector space is a line. At a higher level $\mathfrak m$ divisible by $\mathfrak n$,

$$
\dim(\pi_f^\iota)^{K_1(\mathfrak m)}
=\prod_{v<\infty}(m_v-n_v+1), \tag{11.6}
$$

where $m_v=v(\mathfrak m)$ and $n_v=v(\mathfrak n)$, and factors with $m_v=n_v=0$ equal one. Thus coefficient conjugation preserves the entire oldform multiplicity pattern.

### 11.4 Compatibility with every coefficient embedding

Collect the relative conjugates into the restriction-of-scalars packet

$$
\Pi_f^{\mathrm{new}}
=\operatorname{Res}_{E_f/K}(E_ff). \tag{11.7}
$$

After extension to $\mathbf C$ it decomposes canonically as

$$
\Pi_f^{\mathrm{new}}\otimes_K\mathbf C
\cong\bigoplus_{\substack{\iota:E_f\hookrightarrow\mathbf C\\ \iota|_K=\mathrm{id}}}
\mathbf C f^\iota. \tag{11.8}
$$

The Hecke operator $T_v$ acts on the right by the diagonal matrix with entries $\iota(t_v)$; similarly for $S_v$. The characteristic polynomial on the packet is

$$
\prod_{\substack{\iota:E_f\hookrightarrow\mathbf C\\ \iota|_K=\mathrm{id}}}
\bigl(X-\iota(t_v)\bigr)
=\operatorname{N}_{E_f/K}(X-t_v)\in K[X]. \tag{11.9}
$$

If $t_v$ is integral over $R$, this polynomial lies in $R[X]$. Formula (11.9) is a concrete expression of compatibility with relative coefficient embeddings: all complex eigenlines are the scalar components of one rational module, not an unrelated list of forms. With $K=\mathbf Q$ and the absolute package described in Section 11.1, it covers every coefficient embedding.

If a degree-one realization is given, (11.8) is compatible with its Hodge filtration, Betti signs, and period classes. No choice of a preferred complex embedding is built into the rational packet.

## 12. Quaternionic weight-two packets

### 12.1 Finite algebraic models

Let $D/F$ be a totally definite quaternion algebra, $U\subset D_f^\times$ compact open, and $W$ an algebraic coefficient module corresponding to weight two under the fixed action convention. Book 93 identifies its finite algebraic forms with fixed-weight vectors in the quaternionic automorphic spectrum. The finite automorphic module has the form

$$
M(U,W,\omega_f)
=\left(\bigoplus_i W^{\Gamma_i}\right)_{\omega_f}, \tag{12.1}
$$

where the $\Gamma_i$ are finite stabilizer groups of double-coset representatives. Choose an integer ring over which $W$ and the central character are defined and take the corresponding torsion-free integral submodule. Raw Brandt operators are finite sums of integral weight matrices, so they preserve this lattice.

Therefore Chapters 2--6 apply without analytic convergence issues. The acting Brandt algebra is finite over the coefficient ring, its eigenvalues are algebraic integers, every eigensystem has a number field, all allowed conjugate eigensystems occur, and their intersection lattices are saturated. This is a particularly transparent source of integral packets.

### 12.2 Conjugate near-equivalence blocks

An occurring good character $\lambda$ determines a finite near-equivalence block: every constituent in the block has the same unramified local factors outside $\Sigma$. Applying an allowed embedding $\iota:E_\lambda\hookrightarrow\mathbf C$ produces the conjugate block with good polynomial coefficients $\iota(t_v),\iota(s_v)$.

The point requiring care is that unit multiplicity in the global quaternionic spectrum does not by itself make a good Hecke block one dimensional. Several inequivalent constituents can be nearly equivalent, and one constituent can have a multidimensional $U$-fixed space. Thus the algebraic object canonically conjugated by the finite module is

$$
M[\lambda]\otimes_{\mathcal O_\lambda,\iota}\mathbf C, \tag{12.2}
$$

not an unnamed constituent chosen from its spectral decomposition.

### 12.3 When a single constituent is determined

There are two sufficient routes from a block to a constituent. First, enlarge the commuting algebra by ramified operators or type projectors until the joint eigenspace is a line and the corresponding spectral constituent is unique. Second, use an independent global determination theorem whose hypotheses identify near-equivalence classes.

**Proposition 12.1 (conjugation with isolating data).** Suppose a commutative Hecke algebra $\mathbb T^{\mathrm{full}}$, defined over a number field, contains the good Brandt algebra and acts semisimply on (12.1), compatibly with its direct-sum spectral decomposition. Assume the joint $\lambda^{\mathrm{full}}$-eigenspace is one dimensional. Then every allowed coefficient embedding produces a one-dimensional conjugate eigenspace belonging to a unique conjugate constituent $\pi^\iota$.

**Proof.** Theorem 4.1 preserves the dimension of the joint eigenspace under scalar extension. Because the full commuting action preserves the direct-sum spectral decomposition, that eigenspace is the direct sum of its intersections with the irreducible constituents. A one-dimensional eigenspace can have a nonzero intersection with exactly one summand. The same argument applies after every allowed embedding, so the conjugate line lies in a unique constituent. $\square$

The hypothesis is substantive. Good-place eigenvalues alone should not be silently promoted to a canonical quaternionic representation.

### 12.4 Integral Brandt lattices

Write the class-set lattice in (12.1) as $M_{\mathcal O}$. If $B_v$ is a Brandt matrix, its characteristic polynomial belongs to the coefficient integer ring, so all roots are integral. For a one-dimensional isolated packet line $V_\lambda$, the lattice

$$
L_\lambda=V_\lambda\cap(M_{\mathcal O}\otimes\mathcal O_E) \tag{12.3}
$$

is a projective rank-one $\mathcal O_E$-module. Its localization at every $\Lambda$ is free, and the Brandt operators act through $\mathcal O_{E,\Lambda}$.

If the mass pairing is integral and perfect after localization, the dual lattice is described by (10.5). Stabilizer denominators can make the naive coordinate lattice non-self-dual at primes dividing stabilizer orders. One must either invert those primes or retain the weighted dual. This is why “Brandt matrices have integral entries” and “the packet lattice is self-dual” are different assertions.

## 13. Examples, failures, and normalization checks

### 13.1 A rational packet

Suppose a normalized weight-two newform has $t_v\in\mathbf Z$ and a rational central character at all good places. Then $E_f=\mathbf Q$ and its algebraic packet has one member. If it is supplied with the degree-one realization of Definition 7.1, rational Hecke data still do not make its signed periods rational. Rather,

$$
[\Omega_f^\pm]\in\mathbf C^\times/\mathbf Q^\times. \tag{13.1}
$$

The associated newform lattice is a rank-one $\mathbf Z$-module after choosing an ambient lattice. A normalized Fourier coefficient can select a rational generator of the eigenline, but the comparison with integral homology still introduces transcendental periods.

For an elliptic curve realization, the two Betti sign directions correspond to the two real-conjugation eigenspaces in $H_1$. Integrating a Néron differential over primitive cycles gives the familiar real and imaginary periods. Replacing the differential by a rational multiple changes both by that multiple, exactly as (8.4) predicts.

### 13.2 A quadratic packet

Let $E=\mathbf Q(\sqrt d)$ and suppose one good operator has eigenvalue $a+b\sqrt d$ with $a,b\in\mathbf Q$ and $b\ne0$. The two embeddings give eigenvalues

$$
a+b\sqrt d,
\qquad a-b\sqrt d. \tag{13.2}
$$

On the two-dimensional rational packet, that operator has characteristic polynomial

$$
X^2-2aX+(a^2-b^2d)\in\mathbf Q[X]. \tag{13.3}
$$

If the eigenvalue is an algebraic integer, (13.3) is integral. Over $\mathbf C$ the rational packet splits into its two eigenlines; over $\mathbf Q$ neither line need exist separately.

If the packet has a degree-one realization, the two embeddings also give two pairs of signed period classes

$$
([\Omega_1^+],[\Omega_1^-]),
\qquad
([\Omega_2^+],[\Omega_2^-]). \tag{13.4}
$$

They arise from one $E$-linear comparison problem by scalar extension. It is not generally valid to obtain the second pair by applying the nontrivial field automorphism to the transcendental representatives of the first.

### 13.3 Oldspaces and repeated eigensystems

Let $\pi$ have conductor $\mathfrak n$ and raise the level at one unramified prime $v$. The two standard degeneracy vectors span a two-dimensional oldspace with the same away-from-$v$ Hecke character. Thus the good eigenspace at the higher level has multiplicity two even though automorphic multiplicity and the minimal newvector multiplicity are one.

If the level-$v$ operator has distinct roots, adjoining it splits the oldspace into two stabilized lines, possibly over a quadratic extension of $E_f$. If its roots coincide, the operator can fail to diagonalize and a generalized eigenspace remains. This example demonstrates all three fields one must track:

1. the field of the global good packet;
2. a possible splitting field for a selected bad-place operator;
3. the field over which the whole ramified representation is defined.

They need not coincide. Determinant periods, rather than scalar periods, are the canonical comparison invariant before a line is isolated.

### 13.4 Four instructive failure modes

**Using only trace eigenvalues while the central character varies.** Equal traces need not give equal determinant terms, so the spherical representations can differ. Record $S_v$ or fix the central character.

**Applying a complex automorphism to unitary Satake parameters.** The factors $q_v^{1/2}$ are analytic normalization data. Conjugate the raw algebraic polynomial (1.2), then recover the normalized form after choosing the same convention.

**Calling a rational projector integral.** Primitive idempotents of the generic Hecke algebra can have congruence denominators. The saturated intersection lattice always exists, but an integral direct-sum decomposition may fail.

**Calling a period a canonical number.** A period compares bases of algebraic lines. Its natural invariant is a class modulo the coefficient field, or a determinant line in higher multiplicity. Only after fixing integral generators can one discuss a more rigid scalar, still up to units.

## 14. The complete algebraic and integral package

### 14.1 The main theorem

We now collect the results in the form used by subsequent arithmetic constructions.

**Theorem 14.1 (weight-two packet package).** Let $K$ be a number field with ring of integers $R$. Let $M$ be a finite torsion-free $R$-module carrying a commuting raw Hecke action generated by $T_v,S_v^{\pm1}$ outside a finite set $\Sigma$, and assume its generic acting algebra is reduced. Let $\lambda$ be an occurring characteristic-zero eigensystem, and put $E=\lambda(\mathbb T_K)$.

Then:

1. $E/K$ is finite, every $\lambda(T_v)$ and $\lambda(S_v)$ is integral over $R$, and finitely many good operators generate both the acting algebra and $E$.
2. Every $K$-embedding $\iota:E\hookrightarrow\mathbf C$ produces an occurring conjugate eigensystem $\iota\lambda$ with the same multiplicity. Their direct sum is the complex scalar extension of one restriction-of-scalars packet over $K$. If $K=\mathbf Q$, these are all coefficient embeddings; otherwise no embedding moving $K$ is asserted without a conjugation-compatible family of base modules.
3. For any $E$-eigenspace $V_\lambda$, the intersection
   $$
   L_\lambda=V_\lambda\cap(M\otimes_R\mathcal O_E)
   $$
   is a saturated projective $\mathcal O_E$-lattice of rank $\dim_EV_\lambda$. If the dimension is one, it is a projective rank-one module and becomes free over every $\mathcal O_{E,\Lambda}$.
4. The generic packet projector can have a nontrivial denominator ideal. Away from that ideal the packet lattice is an integral direct summand; at primes dividing it, distinct characteristic-zero packets may be congruent.
5. If the generic module is a conjugation-compatible fixed-weight cuspidal $\mathrm{GL}_2$ module and $\lambda$ comes from a parallel-weight-two newform, then each allowed conjugate good system belongs to a unique global cuspidal representation $\pi^\iota$. If, moreover, $M\otimes_RK$ is the full such module at the original minimal level, its conductor equals that of $\pi$, its finite newvector line is one dimensional, and all ramified local factors are uniquely determined by the global representation.
6. For a quaternionic finite module, conjugation canonically produces the conjugate good near-equivalence block. A unique conjugate constituent follows only when additional isolating data or a determination theorem is supplied.
7. Suppose in addition that the packet has a degree-one cohomological realization satisfying Definition 7.1, with rank-one Hodge and Betti sign lines. Then for every allowed $\iota:E\hookrightarrow\mathbf C$ there are nonzero signed period classes
   $$
   [\Omega_\iota^\pm]\in\mathbf C^\times/\iota(E)^\times.
   $$
   They are independent of $E$-bases, compatible with Hecke-equivariant comparison, and arise for all allowed embeddings from one $E$-linear packet. In multiplicity $m$, the corresponding canonical invariant is a determinant period in $\mathbf C^\times/\iota(E)^\times$.
8. If perfect Hecke-adjoint pairings and integral lattices are present, dual packet lattices are given by integral duals away from projector denominators. For a curve comparison in the convention of Book 27, a self-paired rank-two packet satisfies the exact determinant identity $\det(\mathcal P)\delta=2\pi i\langle\omega,\eta\rangle_{\mathrm{dR}}$ of (10.7).

**Proof.** Assertion 1 is Theorems 3.1 and 5.1 together with Proposition 3.2. Assertion 2 is Theorem 4.1 and the splitting (6.4). Assertion 3 is Proposition 5.2 and the structure of projective modules over a Dedekind domain. Assertion 4 follows from the denominator ideal (5.3) and the crossing-order example, with localization giving the direct summand away from its support.

For assertion 5, conjugate occurrence follows from the number-field automorphic module. Equality of conjugated raw Hecke polynomials gives equality of unramified local factors, so Theorem 11.1 gives uniqueness. Under the stated full-minimal-level hypothesis, preservation of eigenspace dimension and the oldvector formula prove the conductor equality (11.5); newvector theory gives the one-dimensional minimal line. Assertion 6 is the content of Chapter 12.

For assertion 7, Hecke-equivariance of comparison identifies packet factors. Hodge decomposition and the sign involution make both projections of the Hodge line nonzero, yielding (8.3); Proposition 8.1 gives basis independence. Proposition 8.2 proves the higher-multiplicity statement. Finally, equations (10.2)--(10.7) prove assertion 8. $\square$

### 14.2 The implication chain

The proof can be read as the following exact chain:

$$
\begin{array}{c}
\text{finite rational Hecke module}\\
\Downarrow\\
\text{number field }E\text{ and its allowed embedding components}\\
\Downarrow\quad(\text{stable integral lattice})\\
\text{finite Hecke order and integral eigenvalues}\\
\Downarrow\\
\text{saturated packet lattices and denominator ideals}\\
\Downarrow\quad(\mathrm{GL}_2\text{ strong multiplicity one})\\
\text{unique conjugate global representations}\\
\Downarrow\quad(\text{degree-one comparison})\\
\text{Hodge lines, Betti sign lines, and period classes}.
\end{array} \tag{14.1}
$$

Every downward arrow has hypotheses. Complex spectral finite-dimensionality alone does not prove arithmetic algebraicity; a number-field rational module is the first input. Without a stable integral lattice, algebraicity does not imply integrality or produce packet lattices. Without reducedness, characters do not give a direct-sum generic decomposition. Without strong multiplicity one, a good block need not name one constituent. Without a degree-one realization, an automorphic eigenline does not by itself have Betti periods.

### 14.3 Hypothesis and normalization ledger

The following ledger fixes the boundaries of the theorem.

- The base coefficient ring is a number ring, or a localization of one, whenever algebraic integrality is asserted. Finite torsion-free modules over it are projective; after localization at a coefficient prime they are free.
- The Hecke algebra is the faithful image on the selected module. Commutativity refers to the specified good operators, not to an arbitrary full local Hecke algebra.
- Reducedness is a characteristic-zero assertion. It follows from simultaneous diagonalization in the self-adjoint settings used here, but is otherwise a stated hypothesis.
- Raw polynomials are $1-t_vX+q_vs_vX^2$. Central-character values are retained unless fixed in advance.
- Relative Galois conjugation fixes the coefficient base $K$. All coefficient embeddings are present only for a $\mathbf Q$-model or a restriction-of-scalars family containing the conjugate coefficient data. Galois conjugation is not defined by conjugating arbitrary analytic models or transcendental period representatives.
- The number-field model assumed for holomorphic $\mathrm{GL}_2$ forms proves algebraicity but not integrality. Every $\mathrm{GL}_2$ lattice or algebraic-integer assertion additionally assumes a common stable integral lattice.
- The $\mathrm{GL}_2$ uniqueness statement assumes cuspidality and equality outside a finite set. No density-only variant is used.
- A quaternionic good packet is a near-equivalence block until isolating data is specified.
- Scalar signed periods require a degree-one realization whose involution exchanges the two Hodge types, as well as rank-one Hodge and sign pieces. Higher multiplicity uses determinant periods. Parallel weight two over a totally real field of degree $d>1$ is normally cohomological in degree $d$ with $2^d$ signs and is not covered by the degree-one period theorem unless a separate degree-one realization is supplied.
- Integral packet projectors exist only away from their denominator ideals. Reduction at a congruence prime may merge branches.
- Even when complex conjugation preserves the Betti lattice, its sign projectors need not be integral above $2$. The sign sublattices split the full Betti lattice away from $2$; at primes above $2$, the finite index in (9.2) must be retained.
- Betti--de Rham comparison for curves is compatible with pullback, trace, cup products, and finite correspondences. With $I$ oriented from Betti to de Rham, its inverse is integration, and the exact pairing factor is the $2\pi i$ displayed in (10.7). Integral embedding idempotents are used only away from their discriminant and projector denominators.

### 14.4 Conclusion

A weight-two packet is not merely a sequence of complex numbers. It is a closed arithmetic Hecke point with a finite residue field and an orbit of allowed embedding components; a stable integral model adds a family of lattices, and a degree-one cohomological realization adds a pair of comparison lines. The rational Hecke algebra creates the arithmetic point, while an integral Hecke order controls its integral closure. Galois conjugation separates its geometric components. Strong multiplicity one turns the $\mathrm{GL}_2$ components into unique global representations, while quaternionic modules honestly retain near-equivalence until further data isolate a constituent.

The integral and transcendental parts meet without being confused. Saturated intersections give packet lattices even when generic projectors have denominators. Periods measure the mismatch between de Rham and Betti rational structures, and therefore live naturally modulo algebraic rescaling. Coefficient embeddings permute the algebraic eigenspaces and their lattices; comparison supplies a period class at each embedding, while only genuine complex conjugation acts topologically on those periods.

The resulting package is stable under the coefficient extensions, localizations, dualities, and conjugations allowed by its hypotheses. It records exactly what later arithmetic arguments may use: algebraic Hecke polynomials from rational modules, integral Hecke polynomials and local lattices when a stable integral module is supplied, intrinsic rationality fields, conjugate automorphic packets, signed or determinant period classes in genuine degree-one realizations, and the hypotheses under which these objects correspond.
