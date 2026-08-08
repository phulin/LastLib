# Ramification Theory

## Contents

1. [From inertia to depth](#1-from-inertia-to-depth)
   - [The question left by inertia](#11-the-question-left-by-inertia)
   - [Inertia revisited](#12-inertia-revisited)
   - [The first infinitesimal action](#13-the-first-infinitesimal-action)
   - [Tame and wild extensions](#14-tame-and-wild-extensions)
   - [The maximal tame stage](#15-the-maximal-tame-stage)
   - [The shape of a tame Galois group](#16-the-shape-of-a-tame-galois-group)
   - [Stability properties of tameness](#17-stability-properties-of-tameness)
2. [Lower ramification groups](#2-lower-ramification-groups)
   - [Why displacement is the right measurement](#21-why-displacement-is-the-right-measurement)
   - [Basic group properties](#22-basic-group-properties)
   - [The tame character](#23-the-tame-character)
   - [Higher graded pieces](#24-higher-graded-pieces)
   - [Action on finite precision and units](#25-action-on-finite-precision-and-units)
   - [Breaks and the shape of a filtration](#26-breaks-and-the-shape-of-a-filtration)
3. [First calculations](#3-first-calculations)
   - [Unramified extensions](#31-unramified-extensions)
   - [Tame Kummer extensions](#32-tame-kummer-extensions)
   - [An equal-characteristic wild extension](#33-an-equal-characteristic-wild-extension)
   - [A mixed-characteristic quadratic contrast](#34-a-mixed-characteristic-quadratic-contrast)
   - [A wild Kummer calculation](#35-a-wild-kummer-calculation)
   - [A mixed unramified–tame extension](#36-a-mixed-unramifiedtame-extension)
   - [Same degree, arbitrarily different depth](#37-same-degree-arbitrarily-different-depth)
4. [Subgroups and the failure of lower quotients](#4-subgroups-and-the-failure-of-lower-quotients)
   - [Passing to an intermediate base](#41-passing-to-an-intermediate-base)
   - [Why quotients require a new scale](#42-why-quotients-require-a-new-scale)
   - [Real lower indices and continuity convention](#43-real-lower-indices-and-continuity-convention)
   - [The Herbrand function](#44-the-herbrand-function)
5. [Upper numbering](#5-upper-numbering)
   - [A numbering designed for quotients](#51-a-numbering-designed-for-quotients)
   - [Herbrand's quotient theorem](#52-herbrands-quotient-theorem)
   - [Tower transitivity](#53-tower-transitivity)
   - [Break conversion in examples](#54-break-conversion-in-examples)
   - [A two-break tower](#55-a-two-break-tower)
   - [Hasse--Arf and the limits of integrality](#56-hasse--arf-and-the-limits-of-integrality)
6. [Ramification in infinite Galois extensions](#6-ramification-in-infinite-galois-extensions)
   - [Why only upper numbering survives inverse limits](#61-why-only-upper-numbering-survives-inverse-limits)
   - [Finite-image representations need only finite levels](#62-finite-image-representations-need-only-finite-levels)
   - [Finite upper-break decompositions](#63-finite-upper-break-decompositions)
7. [The complementary module and the different](#7-the-complementary-module-and-the-different)
   - [Measuring the defect of integral trace duality](#71-measuring-the-defect-of-integral-trace-duality)
   - [Unramifiedness and the different](#72-unramifiedness-and-the-different)
   - [The derivative formula](#73-the-derivative-formula)
   - [Kähler differentials](#74-kähler-differentials)
   - [Exact trace ideals](#75-exact-trace-ideals)
   - [Tame and wild derivative bounds](#76-tame-and-wild-derivative-bounds)
   - [Further derivative calculations](#77-further-derivative-calculations)
8. [Discriminants](#8-discriminants)
   - [From a dual lattice to an ideal downstairs](#81-from-a-dual-lattice-to-an-ideal-downstairs)
   - [Polynomial discriminants and the index correction](#82-polynomial-discriminants-and-the-index-correction)
   - [Transitivity of the different](#83-transitivity-of-the-different)
   - [Discriminants in towers](#84-discriminants-in-towers)
   - [Base change cautions](#85-base-change-cautions)
9. [Hilbert's different formula](#9-hilberts-different-formula)
   - [The formula and its hypotheses](#91-the-formula-and-its-hypotheses)
   - [Proof by a well-chosen generator](#92-proof-by-a-well-chosen-generator)
   - [Tame and wild parts of the different](#93-tame-and-wild-parts-of-the-different)
   - [A tower check](#94-a-tower-check)
   - [Upper-numbered form and a discriminant bound](#95-upper-numbered-form-and-a-discriminant-bound)
10. [Conductors of finite-image representations](#10-conductors-of-finite-image-representations)
    - [What a conductor should measure](#101-what-a-conductor-should-measure)
    - [Artin and Swan conductors](#102-artin-and-swan-conductors)
    - [Independence of the cutting field](#103-independence-of-the-cutting-field)
    - [Immediate specializations](#104-immediate-specializations)
11. [The Artin character and integrality](#11-the-artin-character-and-integrality)
    - [Why the weighted sum is an integer](#111-why-the-weighted-sum-is-an-integer)
    - [Artin's integrality theorem](#112-artins-integrality-theorem)
    - [Additivity and exact sequences](#113-additivity-and-exact-sequences)
    - [Fixed-space calculations](#114-fixed-space-calculations)
12. [Induction, restriction, and base change](#12-induction-restriction-and-base-change)
    - [Why functorial formulas need normalization factors](#121-why-functorial-formulas-need-normalization-factors)
    - [Strategy of the induction formula](#122-strategy-of-the-induction-formula)
    - [Restriction through a finite Galois realization](#123-restriction-through-a-finite-galois-realization)
    - [Towers and transitivity](#124-towers-and-transitivity)
13. [Conductor--discriminant identities](#13-conductor--discriminant-identities)
    - [The permutation representation of embeddings](#131-the-permutation-representation-of-embeddings)
    - [The regular representation](#132-the-regular-representation)
    - [Decomposition into irreducible characters](#133-decomposition-into-irreducible-characters)
    - [A cyclic wild example revisited](#134-a-cyclic-wild-example-revisited)
    - [Discriminants of fields cut out by representations](#135-discriminants-of-fields-cut-out-by-representations)
14. [Nongalois extensions and imperfect residues](#14-nongalois-extensions-and-imperfect-residues)
    - [What remains intrinsic without Galois symmetry](#141-what-remains-intrinsic-without-galois-symmetry)
    - [Normal closures and overcounting](#142-normal-closures-and-overcounting)
    - [Purely inseparable extensions](#143-purely-inseparable-extensions)
    - [A hypothesis map](#144-a-hypothesis-map)
15. [A working synthesis](#15-a-working-synthesis)
    - [The ramification dictionary](#151-the-ramification-dictionary)
    - [A calculation protocol](#152-a-calculation-protocol)
    - [Consequences for two-dimensional arithmetic](#153-consequences-for-two-dimensional-arithmetic)
    - [Final perspective](#154-final-perspective)

## 1. From inertia to depth

### 1.1 The question left by inertia

Let $K$ be complete for a nontrivial discrete valuation. Write $A=\mathcal O_K$, $\mathfrak m_K=(\pi_K)$, and $k=A/\mathfrak m_K$. If $L/K$ is finite, write $B=\mathcal O_L$, $\mathfrak m_L=(\pi_L)$, and $l=B/\mathfrak m_L$, and normalize valuations by

$$
v_L(L^\times)=\mathbf Z,
\qquad v_L|_{K^\times}=e(L/K)v_K.
$$

The preceding theory separated a local extension into residue-field growth and value-group growth. In a finite Galois extension $L/K$, with group $G$, reduction gives a homomorphism

$$
G\longrightarrow\operatorname{Aut}_k(l),
$$

whose kernel $I$ is inertia. This says which automorphisms are invisible modulo $\mathfrak m_L$, but it does not say *how invisible* they are. Two elements of inertia may both fix the residue field while one moves a uniformizer in its first digit and the other only in its hundredth. Ramification theory measures that depth.

The subject has three mutually reinforcing languages. Ramification groups measure automorphisms by displacement. The different and discriminant measure the failure of integral trace duality. Conductors measure the same failure after a Galois group acts on a vector space. Much of the power of the theory comes from proving that these languages assign the same weighted counts.

No finiteness of $k$ is assumed unless stated. Its **characteristic exponent** is

$$
p=\begin{cases}
\operatorname{char}k,&\operatorname{char}k>0,\\
1,&\operatorname{char}k=0.
\end{cases}
$$

Statements about wild inertia are substantive when $p>1$. The clean classical theory of tame extensions uses separability of residue extensions; this is automatic when $k$ is perfect, but not otherwise. We will always expose that hypothesis.

### 1.2 Inertia revisited

Assume first that $L/K$ is finite Galois. Uniqueness of the extended valuation makes every $K$-automorphism preserve $B$, $\mathfrak m_L$, and $v_L$. The inertia group is

$$
G_0=I=\ker\bigl(G\to\operatorname{Aut}_k(l)\bigr).
$$

We already know that its fixed field is the maximal unramified subextension when $l/k$ is separable. In that case reduction is onto $\operatorname{Gal}(l/k)$ and

$$
1\longrightarrow I\longrightarrow G
\longrightarrow\operatorname{Gal}(l/k)\longrightarrow1,
\qquad |I|=e(L/K).
$$

If $l/k$ is inseparable, the image only sees its automorphisms, not its entire degree. Then $|I|$ need not equal $e$. This is why the formula “inertia has order $e$” always carries a residue-separability hypothesis.

When $k=\mathbf F_q$, the quotient has a preferred arithmetic Frobenius $x\mapsto x^q$; geometric Frobenius is its inverse. In a ramified extension these specify cosets modulo $I$, not preferred lifts in $G$. Ramification groups live inside inertia and are unchanged if one reverses the Frobenius convention. Later representations, however, often record both inertia and a chosen Frobenius convention, so the distinction must remain visible.

### 1.3 The first infinitesimal action

An inertial automorphism fixes every residue class. Its first possible nontrivial action is therefore on the cotangent line

$$
\mathfrak m_L/\mathfrak m_L^2.
$$

Choose a uniformizer $\pi_L$. For $\sigma\in I$, the quotient $\sigma(\pi_L)/\pi_L$ is a unit. Its residue defines

$$
\theta_0:I\longrightarrow l^\times,
\qquad
\theta_0(\sigma)=\overline{\frac{\sigma(\pi_L)}{\pi_L}}.
$$

This is a homomorphism because inertia acts trivially on $l$. Changing $\pi_L$ to $u\pi_L$ multiplies the quotient by $\sigma(u)/u$, whose residue is $1$, so $\theta_0$ is intrinsic. It describes the scalar action of inertia on the one-dimensional $l$-space $\mathfrak m_L/\mathfrak m_L^2$.

The kernel consists of automorphisms satisfying

$$
\sigma(\pi_L)\equiv\pi_L\pmod{\mathfrak m_L^2}.
$$

This kernel will be $G_1$, the wild inertia group. Thus the name “wild” does not initially refer to complicated equations: it means that even the first infinitesimal tangent direction fails to detect the automorphism.

### 1.4 Tame and wild extensions

Before defining all higher groups, it is useful to know what distinction they are meant to refine. A finite separable extension $E/K$ is **tamely ramified** if its residue extension is separable and $p\nmid e(E/K)$. It is **unramified** when moreover $e=1$. A finite separable extension is **wildly ramified** if it is not tame. Under the explicit residue-separability hypothesis this says $p\mid e$.

For a finite Galois extension with separable residue extension, the following conditions are equivalent:

1. $L/K$ is tame.
2. $p\nmid |I|$.
3. The wild inertia group $G_1$ is trivial.
4. Every totally ramified stage after the maximal unramified subextension has degree prime to $p$.
5. After a finite unramified base change containing the required roots of unity, the totally ramified stage is generated by an $e$th root of a uniformizer.

The equivalence of the first two uses $|I|=e$. The tame character embeds $I/G_1$ in $l^\times$, whose finite subgroups have order prime to $p$: in characteristic $p$, $X^{p^r}-1=(X-1)^{p^r}$, so there is no nontrivial $p$-power torsion. Conversely, the deeper quotients will be $p$-groups, so a prime-to-$p$ inertia group cannot meet them.

The residue-separability clause is essential. If $k$ is imperfect and $a\notin k^p$, then

$$
k(a^{1/p})((t))/k((t))
$$

has $e=1$ but purely inseparable residue extension. Calling it tame merely because $p\nmid e$ would erase genuine inseparable ramification.

### 1.5 The maximal tame stage

Suppose $L/K$ is finite Galois and $l/k$ is separable. Since $G_1$ is normal in $G$, its fixed field

$$
L^{G_1}
$$

is canonical. The extension $L^{G_1}/K$ is the maximal tame subextension of $L/K$, and $L/L^{G_1}$ is totally wildly ramified: its Galois group is the $p$-group $G_1$, and it has no nontrivial tame quotient.

There are therefore two canonical cuts in the field tower:

$$
K\subseteq L^{G_0}\subseteq L^{G_1}\subseteq L.
$$

The first stage is unramified, the second is totally tamely ramified, and the last is totally wildly ramified. Their degrees are respectively

$$
f(L/K),\qquad |G_0/G_1|,\qquad |G_1|.
$$

This three-stage decomposition is more informative than the earlier unramified–totally ramified split. It isolates the unique part on which prime-to-$p$ radical methods work and leaves a $p$-primary extension for higher ramification groups.

The word “canonical” refers to subfields inside a fixed Galois extension. A totally tame stage need not possess a canonical uniformizer or Kummer equation. Coordinates appear only after choices.

### 1.6 The shape of a tame Galois group

Assume temporarily that $k$ is finite of order $q$ and that $L/K$ is tamely ramified. Choose a lift $F\in G$ of arithmetic Frobenius and a generator $\tau$ of tame inertia of order $e$. Conjugation by $F$ acts on the tame character through residue Frobenius, giving

$$
F\tau F^{-1}=\tau^q.
$$

Thus the Galois group is generated by an unramified direction and a cyclic inertial direction with this relation, together with the relation determining the order of the chosen Frobenius lift. Geometric Frobenius replaces $F$ by $F^{-1}$ and changes the conjugation exponent accordingly. The ramification filtration itself remains

$$
G_{-1}=G,\qquad G_0=\langle\tau\rangle,\qquad G_1=1.
$$

For an arbitrary residue field there need be no distinguished Frobenius element, but the action of $G/G_0$ on $G_0/G_1$ is still the natural action on the finite subgroup of $l^\times$ supplied by the tame character.

### 1.7 Stability properties of tameness

Tameness is designed to survive the ordinary operations on separable local extensions. A subextension of a tame extension is tame, because its ramification index divides the original one and its residue extension is a subextension of a separable extension. A compositum of two tame extensions is tame: after an unramified base change, both ramified parts are generated by prime-to-$p$ roots of uniformizers, and their combined ramification index remains prime to $p$. A finite Galois closure of a tame extension is therefore tame.

In a tower $L/M/K$ of finite separable extensions with separable residue extensions, $L/K$ is tame if and only if both $L/M$ and $M/K$ are tame. This follows from multiplicativity of $e$ and transitivity of residue separability. Wildness, by contrast, can disappear after passing to a subextension: a wildly ramified Galois extension may have a tame quotient after its wild inertia subgroup is killed.

## 2. Lower ramification groups

### 2.1 Why displacement is the right measurement

To refine inertia without choosing coordinates, one should ask how much an automorphism moves *every* integral element. For $\sigma\in G$, define

$$
i_G(\sigma)=\min_{x\in B}v_L(\sigma(x)-x),
$$

where the minimum is finite for $\sigma\ne1$ and $i_G(1)=+\infty$. Then, for every integer $i\geq0$, define

$$
G_i=\{\sigma\in G:i_G(\sigma)\geq i+1\},
$$

and put $G_{-1}=G$. Equivalently,

$$
G_i=\{\sigma\in G:\sigma(x)\equiv x
\pmod{\mathfrak m_L^{i+1}}\text{ for every }x\in B\}.
$$

The shift by one is deliberate. Congruence modulo $\mathfrak m_L$ defines inertia, so it should have index $0$: $G_0=I$. Congruence modulo $\mathfrak m_L^2$ then defines $G_1$.

The minimum formulation makes independence of generators clear. If the residue extension is separable and $\pi_L$ is a uniformizer, then for $\sigma\in I$, $\sigma\ne1$,

$$
i_G(\sigma)=v_L(\sigma(\pi_L)-\pi_L).
$$

Indeed, lift a separating residue generator for the maximal unramified part; inertia fixes that lift. The integral ring is generated over the unramified ring by $\pi_L$, so polynomial differences are divisible by $\sigma(\pi_L)-\pi_L$. Equality follows by using $x=\pi_L$. Without residue separability, the definition using all $x\in B$ remains sound, while this shortcut can fail.

### 2.2 Basic group properties

The first task is to show that depth behaves like a filtration rather than a collection of accidental subsets.

**Proposition 2.1.** For $i\geq-1$, $G_i$ is a normal subgroup of $G$,

$$
G=G_{-1}\supseteq G_0\supseteq G_1\supseteq G_2\supseteq\cdots,
$$

and $G_i=1$ for all sufficiently large $i$.

**Proof strategy.** Congruence is stable under composition and inverses. Conjugation merely replaces the test element by another integral element. Finiteness of $G$ then turns the strict separation of distinct automorphisms into eventual triviality.

If $\sigma$ and $\tau$ fix all elements modulo $\mathfrak m_L^{i+1}$, then

$$
\sigma\tau(x)-x
=\sigma(\tau(x)-x)+(\sigma(x)-x)
$$

lies in $\mathfrak m_L^{i+1}$, since $\sigma$ preserves that ideal. The inverse condition follows by applying $\sigma^{-1}$. For $g\in G$,

$$
g\sigma g^{-1}(x)-x
=g\bigl(\sigma(g^{-1}x)-g^{-1}x\bigr),
$$

so normality follows. Finally, for each nonidentity $\sigma$ choose $x_\sigma$ that it moves. Once $i+1>v_L(\sigma x_\sigma-x_\sigma)$, that $\sigma$ is absent from $G_i$. There are finitely many $\sigma$. $\square$

The filtration also satisfies commutator estimates

$$
[G_i,G_j]\subseteq G_{i+j}\qquad(i,j\geq1).
$$

Power estimates also push elements deeper, but their exact form in mixed characteristic depends on $v_L(p)$: a linear term involving $p$ competes with a $p$th-order term. We will not use a uniform power bound. The commutator estimate comes from composing expansions modulo successively deeper powers of $\mathfrak m_L$; its main conceptual consequence is that deep ramification becomes increasingly abelian. The graded-piece calculation below supplies the precise $p$-primary assertion we need.

### 2.3 The tame character

The map $\theta_0$ of Section 1.3 has kernel $G_1$, hence induces an injection

$$
G_0/G_1\hookrightarrow l^\times.
$$

Therefore $G_0/G_1$ is cyclic of order prime to $p$: every finite subgroup of a field's multiplicative group is cyclic, and in characteristic $p$ it has no $p$-torsion. This quotient is the **tame inertia quotient** of the finite extension.

If $l/k$ is separable, $|G_0|=e$. The subgroup $G_1$ is then the unique Sylow $p$-subgroup of $G_0$. It is normal even in $G$, because it is a canonical kernel. Consequently

$$
e=e_{\mathrm{tame}}e_{\mathrm{wild}},
\qquad e_{\mathrm{tame}}=|G_0/G_1|,
\qquad e_{\mathrm{wild}}=|G_1|,
$$

with $e_{\mathrm{tame}}$ prime to $p$ and $e_{\mathrm{wild}}$ a power of $p$. If $p=1$, then $G_1=1$: residue characteristic zero admits no wild ramification.

The cyclicity conclusion concerns inertia modulo wild inertia, not inertia itself. A wildly ramified inertia group can be nonabelian. Even its $p$-Sylow subgroup can have complicated successive extensions, though every individual positive graded layer will be elementary abelian.

### 2.4 Higher graded pieces

For $i\geq1$ and $\sigma\in G_i$, write

$$
\sigma(\pi_L)=\pi_L+c_\sigma\pi_L^{i+1}
\pmod{\mathfrak m_L^{i+2}}.
$$

The residue $\bar c_\sigma\in l$ depends on the chosen uniformizer, but its vanishing does not. A calculation of a composite gives

$$
c_{\sigma\tau}\equiv c_\sigma+c_\tau\pmod{\mathfrak m_L},
$$

because elements of $G_i$ act trivially on the coefficients at the required precision. Thus

$$
\theta_i:G_i/G_{i+1}\hookrightarrow(l,+),
\qquad \sigma\longmapsto\bar c_\sigma
$$

is an injective homomorphism. More intrinsically, the target is the one-dimensional $l$-space

$$
\operatorname{Hom}_l(\mathfrak m_L/\mathfrak m_L^2,
\mathfrak m_L^{i+1}/\mathfrak m_L^{i+2}),
$$

and choosing $\pi_L$ identifies it with $l$.

Hence, when $p>1$, every $G_i/G_{i+1}$ for $i\geq1$ is an elementary abelian $p$-group, naturally an $\mathbf F_p$-vector subspace of $l^+$. If $p=1$, the additive group of $l$ has no nontrivial finite subgroup, again forcing $G_1=1$.

These injections explain the architecture of inertia:

$$
\text{cyclic prime-to-$p$ layer}
\quad\text{followed by}\quad
\text{additive residue-characteristic layers}.
$$

They do not say that every additive subspace occurs, or that all extensions split. The extension data between layers carry genuine arithmetic information.

### 2.5 Action on finite precision and units

The definition using all of $B$ can be restated as a kernel:

$$
G_i=\ker\left(G\longrightarrow
\operatorname{Aut}\bigl(B/\mathfrak m_L^{i+1}\bigr)\right)
\qquad(i\geq0).
$$

Thus $G/G_i$ is exactly the part of the Galois group visible to precision $i+1$. Completeness says that an automorphism invisible at every finite precision is the identity, explaining once more why the filtration has trivial intersection.

The same depth appears in the unit filtration. For $\sigma\in G_i$ and $u\in U_L^n$,

$$
\frac{\sigma(u)}u\in U_L^{n+i}
\qquad(i,n\geq1).
$$

To see the leading mechanism, write $u=1+x$ with $v_L(x)\geq n$. Since $\sigma$ is the identity on coefficients to depth $i+1$, the difference $\sigma(x)-x$ gains at least $i$ further units of valuation relative to $x$; division by the unit $u$ changes no depth. Precise endpoint statements follow by expanding $x$ in a uniformizer over the maximal unramified subring.

This estimate links the additive displacement filtration on automorphisms with the multiplicative filtration on principal units. It is the reason higher ramification controls norm maps on deep units: products of conjugates linearize to traces, while each ramification group specifies which conjugates remain indistinguishable at a given depth.

### 2.6 Breaks and the shape of a filtration

An integer $i\geq0$ is a **lower break** or **lower jump** if $G_i\ne G_{i+1}$. Since the groups eventually become trivial, there are finitely many breaks. The break at $0$ separates tame from wild inertia. Positive breaks record successive depths of wild motion.

For $\sigma\ne1$, the element belongs precisely to

$$
G_0,G_1,\ldots,G_{i_G(\sigma)-1}
$$

if it is inertial. Thus the filtration and the displacement function determine each other. This elementary observation is the counting engine behind Hilbert's formula for the different.

It is worth separating “ramification index” from “ramification depth.” Two totally ramified cyclic extensions can have the same degree and completely different breaks. The index $e$ counts how many automorphisms lie in inertia; the filtration counts how long each of them remains invisible at finite precision.

## 3. First calculations

### 3.1 Unramified extensions

Let $L/K$ be finite unramified and Galois. Reduction is faithful, so

$$
G_{-1}=G,
\qquad G_0=1.
$$

There is no inertia and hence no positive ramification. If $k$ is finite, arithmetic Frobenius generates $G$ but lies at level $-1$, not level $0$. This placement is conceptually important: Frobenius measures residue motion, while the ramification filtration measures motion invisible in the residue field.

### 3.2 Tame Kummer extensions

Assume $p\nmid e$, that $K$ contains $\mu_e$, and let

$$
L=K(\alpha),\qquad \alpha^e=u\pi_K,\quad u\in A^\times.
$$

The polynomial is Eisenstein, so $L/K$ is totally ramified of degree $e$, and it is Galois with automorphisms $\sigma_\zeta(\alpha)=\zeta\alpha$. For $\zeta\ne1$, reduction of $\zeta$ has the same order, so $\zeta-1$ is a unit. Therefore

$$
i_G(\sigma_\zeta)
=v_L((\zeta-1)\alpha)=1.
$$

It follows that

$$
G_{-1}=G_0=G,
\qquad G_1=1.
$$

All nontrivial ramification is concentrated at the tame break $0$. The tame character sends $\sigma_\zeta$ to $\bar\zeta$ and identifies $G$ with a cyclic subgroup of $l^\times$.

The assumption $\mu_e\subset K$ simplifies the equation, not the intrinsic conclusion. A totally tamely ramified Galois extension always has the same filtration $G_0=G$, $G_1=1$; after a suitable unramified base change it takes this Kummer form.

### 3.3 An equal-characteristic wild extension

Let $K=k((t))$ with $\operatorname{char}k=p>0$, and assume $k$ contains $\mathbf F_p$. Choose $m>0$ with $p\nmid m$, and let

$$
L=K(y),\qquad y^p-y=t^{-m}.
$$

This is a cyclic Artin--Schreier extension of degree $p$, with $\sigma_c(y)=y+c$ for $c\in\mathbf F_p$. It is totally ramified. Normalizing $v_L(t)=p$, the equation gives $v_L(y)=-m$.

To compute the displacement, choose integers $a,b$ with

$$
ap-bm=1,
\qquad 1\leq b\leq p-1,
$$

and put $\pi_L=t^ay^b$. Then $v_L(\pi_L)=1$. For $c\ne0$,

$$
\frac{\sigma_c(\pi_L)}{\pi_L}
=\left(1+\frac c y\right)^b,
$$

and $v_L(c/y)=m$. Since $b$ is nonzero in $k$, the first binomial term does not vanish, so

$$
v_L(\sigma_c(\pi_L)-\pi_L)=m+1.
$$

Thus

$$
G_0=G_1=\cdots=G_m=G,
\qquad G_{m+1}=1.
$$

The integer $m$ is the unique positive lower break. The restriction $p\nmid m$ is a normal-form condition: terms with exponent divisible by $p$ can be altered by replacing $y$ by $y-z$.

### 3.4 A mixed-characteristic quadratic contrast

Let $L=\mathbf Q_p(\sqrt p)$ and put $\pi_L=\sqrt p$. For odd $p$, the nontrivial automorphism sends $\pi_L$ to $-\pi_L$, and $2$ is a unit. Hence

$$
i_G(\sigma)=v_L(2\pi_L)=1.
$$

The extension is tame: $G_0=G$ and $G_1=1$.

For $p=2$, the same equation gives

$$
i_G(\sigma)=v_L(2\pi_L)=2+1=3,
$$

because $v_L(2)=2$. Consequently

$$
G_0=G_1=G_2=G,
\qquad G_3=1.
$$

The extension $\mathbf Q_2(\sqrt2)/\mathbf Q_2$ is wild with break $2$. The example isolates the source of wildness in mixed characteristic: an integer such as $2$, harmless at odd residue characteristic, itself acquires positive valuation.

### 3.5 A wild Kummer calculation

A cyclic radical equation can also be wild. Let $p$ be odd, take $K=\mathbf Q_p(\zeta_p)$ with uniformizer $\lambda=\zeta_p-1$, and let

$$
L=K(\alpha),\qquad \alpha^p=\lambda.
$$

This is a totally ramified cyclic extension of degree $p$, with $\sigma(\alpha)=\zeta_p\alpha$. In $K$, $v_K(\lambda)=1$ and $v_K(p)=p-1$; in $L$, $v_L|_K=pv_K$. Therefore

$$
i_G(\sigma)=v_L((\zeta_p-1)\alpha)=p+1
$$

for every nontrivial $\sigma$. Its unique lower break is $p$:

$$
G_0=\cdots=G_p=G,
\qquad G_{p+1}=1.
$$

This should be compared with the prime-to-$p$ Kummer example. The form “root of a uniformizer” does not determine tameness; divisibility of the degree by the residue characteristic does.

### 3.6 A mixed unramified–tame extension

Let $k=\mathbf F_q$, let $K_f/K$ be the unramified extension of degree $f$, and choose $e$ prime to $p$ with $e\mid q^f-1$. Assume for simplicity that

$$
L=K_f(\alpha),\qquad \alpha^e=\pi_K
$$

has degree $ef$ over $K$. The roots of unity $\mu_e$ lie in $K_f$, so $L/K_f$ is cyclic and tame. Arithmetic Frobenius $F$ of $K_f/K$ extends by $F(\alpha)=\alpha$, while tame inertia is generated by $\tau(\alpha)=\zeta_e\alpha$. Since $F(\zeta_e)=\zeta_e^q$,

$$
F\tau F^{-1}=\tau^q.
$$

The filtration is

$$
G_{-1}=G,\qquad G_0=\langle\tau\rangle,\qquad G_1=1.
$$

Thus the unramified degree $f$ appears only between levels $-1$ and $0$, while the ramification degree $e$ appears at level $0$. Hilbert's formula later gives $d=e-1$, and norming the different gives

$$
\delta=f(e-1).
$$

The residue degree does not change the upstairs different exponent, but it multiplies the downstairs discriminant exponent.

### 3.7 Same degree, arbitrarily different depth

Fix characteristic $p$ and consider, for every $m>0$ prime to $p$,

$$
y^p-y=t^{-m}.
$$

All these extensions have the same invariants

$$
[L:K]=e=p,\qquad f=1,
$$

and the same Galois group. Yet their unique ramification break is $m$, and their different exponent is $(m+1)(p-1)$. Hence $e$, $f$, the abstract Galois group, and even the tame/wild label leave the depth unbounded.

This family is a useful counterexample to any attempted discriminant estimate based only on degree. A discriminant bound requires control of where the ramification filtration ends, not merely how many automorphisms it contains.

## 4. Subgroups and the failure of lower quotients

### 4.1 Passing to an intermediate base

Throughout Chapters 4 and 5, $L/K$ is finite Galois and $l/k$ is separable; the latter is automatic when $k$ is perfect. Let $G=\operatorname{Gal}(L/K)$, and let $H\subseteq G$ have fixed field $M=L^H$. The extension $L/M$ is Galois even if $M/K$ is not. Since both filtrations use the same normalized valuation on the same top field $L$, their displacement tests are identical. Therefore

$$
H_i=H\cap G_i\qquad(i\geq-1).
$$

This is the great advantage of lower numbering: it behaves perfectly under subgroups. In particular, lower breaks of $L/M$ are among those of $L/K$, though a break can disappear if $H$ does not meet the relevant quotient.

If $H$ is not normal, there is no quotient extension $M/K$ with group $G/H$. The subgroup formula still applies to $L/M$, and conjugate subgroups give conjugate intermediate fields with identical ramification data.

### 4.2 Why quotients require a new scale

Now assume $H\triangleleft G$, so $M/K$ is Galois with group $G/H$. One might hope that its $i$th lower group is simply $G_iH/H$. This is generally false. The reason is normalization: the valuation of $M$ is a rescaled restriction of $v_L$, so a displacement depth measured upstairs does not retain the same integer label downstairs. Different automorphisms can also merge in a quotient, and the least displacement among their lifts changes nonlinearly.

Tame examples hide the problem because there is only one nontrivial level. In a tower with several wild breaks, naive quotienting places the quotient jumps at the wrong integers. We need a change of coordinates that accelerates whenever the ramification group becomes smaller. The Herbrand function supplies precisely that clock.

### 4.3 Real lower indices and continuity convention

Before changing coordinates, we must extend lower groups from integers to real indices. For $u\geq0$, set

$$
G_u=G_{\lceil u\rceil},
$$

with $G_0$ retaining its usual meaning, and put $G_u=G$ for $-1\leq u<0$. Thus, for an integer $m\geq0$,

$$
G_u=G_{m+1}\quad\text{when }m<u\leq m+1.
$$

This convention makes the real-indexed filtration left-continuous at positive integers. It is one of two conventions found in use; formulas that employ a floor function instead shift endpoints. All integral groups are unchanged. Our convention is chosen so that

$$
\varphi(1)=\frac{|G_1|}{|G_0|},
$$

the standard first slope calculation.

### 4.4 The Herbrand function

The **Herbrand function** of $L/K$ is the continuous, increasing, piecewise-linear map

$$
\varphi_{L/K}(u)
=\int_0^u\frac{dt}{[G_0:G_t]}
\qquad(u\geq0),
$$

extended by $\varphi(u)=u$ for $-1\leq u\leq0$. Since the integrand is positive, $\varphi$ is a homeomorphism $[-1,\infty)\to[-1,\infty)$. Denote its inverse by

$$
\psi_{L/K}=\varphi_{L/K}^{-1}.
$$

For an integer $m\geq0$ and $m\leq u\leq m+1$,

$$
\varphi(u)
=\frac1{|G_0|}
\left(
\sum_{j=1}^{m}|G_j|+(u-m)|G_{m+1}|
\right).
$$

Empty sums are zero. Thus the slope on $(m,m+1)$ is $|G_{m+1}|/|G_0|$. As groups shrink, the clock slows: a long interval in lower depth may occupy a short interval in upper depth.

The function depends only on inertia and its positive filtration. Unramified automorphisms in $G/G_0$ do not affect it. For a tame totally ramified extension, $G_1=1$, so $\varphi(u)=u/|G_0|$ for $u>0$. For the Artin--Schreier example with one break $m$, $\varphi(u)=u$ up to $m$ and then has slope $1/p$.

## 5. Upper numbering

### 5.1 A numbering designed for quotients

Define the **upper ramification groups** by

$$
G^v=G_{\psi(v)}\qquad(v\geq-1).
$$

Because our lower real filtration is left-continuous, so is the upper filtration. At integral lower breaks $b$, the corresponding upper break is $\varphi(b)$. In particular,

$$
G^{-1}=G,\qquad G^0=G_0,\qquad
G^{0+}:=\bigcup_{v>0}G^v=G_1.
$$

Here $G^{0+}$ denotes the stable group immediately to the right of $0$, not a value at an infinitesimal real number. In a finite extension there is a first positive upper break if $G_1\ne1$.

The definition looks indirect because its purpose is not to simplify one extension. It is calibrated so that quotienting becomes exact.

### 5.2 Herbrand's quotient theorem

**Theorem 5.1 (Herbrand).** Let $H\triangleleft G$, let $M=L^H$, and identify $\operatorname{Gal}(M/K)$ with $G/H$. Then for every $v\geq-1$,

$$
(G/H)^v=G^vH/H.
$$

Thus upper numbering is compatible with quotients.

**Proof strategy.** Compare displacement downstairs with the product of displacements of all lifts upstairs. Norms provide that product, while valuation of a norm supplies the scaling factor. Counting, over each lower interval, how many lifts remain at a given depth produces exactly the integral defining $\varphi$.

For $\bar\sigma\in G/H$, choose a lift $\sigma$. Applied to a suitably chosen integral element, the norm from $L$ to $M$ turns the family of differences indexed by the coset $\sigma H$ into a downstairs difference. The valuation of the product is the sum of the valuations of its factors. As the lower threshold increases, the number of factors still exceeding that threshold is $|H\cap G_t|$. Integrating these cardinalities yields the identity between the two Herbrand clocks. After applying their inverses, membership of $\bar\sigma$ at upper level $v$ is equivalent to the coset $\sigma H$ meeting $G^v$, which is the displayed formula. $\square$

The proof's decisive feature is weighted counting, not a miraculous reindexing. Lower numbering asks for raw depth in the top valuation; upper numbering divides each depth interval by the index already lost. That correction is exactly what a quotient needs.

### 5.3 Tower transitivity

For a Galois tower $L/M/K$, with $L/K$ finite Galois, Herbrand functions satisfy

$$
\varphi_{L/K}
=\varphi_{M/K}\circ\varphi_{L/M},
$$

and hence

$$
\psi_{L/K}
=\psi_{L/M}\circ\psi_{M/K}.
$$

This is the analytic form of ramification transitivity. Differentiating away from breaks reduces the identity to an index calculation among ramification groups; continuity fills in the finitely many break points. Equivalently, apply Herbrand's theorem twice to successive quotients.

The formula must be read with the relevant valuations and groups attached to each stage. It does not assert that lower indices themselves multiply. Rather, it says that passage from raw top-field depth to quotient-stable depth can be performed one field at a time.

If an extension in the tower is not Galois, pass to a finite Galois closure and use the subgroup formula for the upper field and quotient formula where a normal subgroup occurs. Results independent of the closure, such as different and discriminant ideals, can then be descended intrinsically.

### 5.4 Break conversion in examples

If a cyclic group of order $p$ has a unique lower break $m>0$, then $G_u=G$ for $0\leq u\leq m$ and is trivial afterward. Hence

$$
\varphi(u)=
\begin{cases}
u,&0\leq u\leq m,\\
m+(u-m)/p,&u\geq m.
\end{cases}
$$

The unique upper break is also $m$. This equality is special to a single cyclic $p$-layer. In a tower of such layers, later breaks are compressed by the orders of the earlier surviving groups, and lower and upper labels diverge.

For a tame totally ramified group of order $e$, there is only the break $0$. Since $G_u=1$ for every $u>0$, $\varphi(u)=u/e$. The upper group still drops immediately after $0$. The altered slope matters only if another ramified layer is placed above or below it in a tower.

### 5.5 A two-break tower

The first example in which lower and upper labels genuinely differ has two wild layers. Suppose $G$ has order $p^2$ and its lower filtration has the form

$$
G_0=\cdots=G_a=G,\qquad
G_{a+1}=\cdots=G_b=H,\qquad
G_{b+1}=1,
$$

where $H$ has order $p$ and $0<a<b$. Then

$$
\varphi(u)=
\begin{cases}
u,&0\leq u\leq a,\\
a+\dfrac{u-a}{p},&a\leq u\leq b,\\
a+\dfrac{b-a}{p}+\dfrac{u-b}{p^2},&u\geq b.
\end{cases}
$$

The upper breaks are

$$
a,\qquad a+\frac{b-a}{p}.
$$

The second need not be an integer for an arbitrary nonabelian filtration; if $G$ is abelian and $k$ is perfect, Hasse--Arf forces $p\mid b-a$.

Now take $M=L^H$. The subgroup theorem says that $L/M$ has group $H$ through lower level $b$, so its unique lower break is $b$. Herbrand's quotient theorem says that $M/K$ has quotient group $G/H$ until upper level $a$ and is trivial afterward. Since a cyclic group of order $p$ has equal single lower and upper breaks, its lower break is $a$. Thus the two stages have raw breaks $b$ and $a$, while the combined extension compresses the upper label of the later break by a factor $p$.

This example makes tower transitivity visible:

$$
\varphi_{L/K}
=\varphi_{M/K}\circ\varphi_{L/M}.
$$

Up to $b$, the function $\varphi_{L/M}$ is the identity. The function for $M/K$ has slope $1/p$ after $a$, producing exactly the middle line above.

### 5.6 Hasse--Arf and the limits of integrality

Upper breaks are generally rational numbers. The central integrality theorem is therefore striking.

**Theorem 5.2 (Hasse--Arf).** Assume that $k$ is perfect. If $L/K$ is a finite abelian Galois extension, every upper ramification break is an integer.

No finiteness of the residue field is required, but perfection rules out the imperfect-residue refinements for which the classical statement is not the correct one. For nonabelian extensions, fractional upper breaks can occur. Lower breaks remain integers by definition, but they are not quotient-compatible.

One route to Hasse--Arf studies conductors of one-dimensional characters. Their conductor exponents are integers, and an abelian group is detected by its characters; the jump locations are recovered from those exponents. This connection anticipates the conductor theory developed later. We will use Hasse--Arf as an integrality theorem, not as a substitute for the stronger Artin-character integrality needed for arbitrary representations.

## 6. Ramification in infinite Galois extensions

### 6.1 Why only upper numbering survives inverse limits

Assume in this chapter that the residue field is perfect, or more generally restrict to a directed system of finite Galois quotients having separable residue extensions. Absolute Galois groups and Galois representations are profinite, so finite ramification groups must eventually be assembled through finite quotients. Lower numbering is incompatible with quotients and therefore has no canonical inverse-limit definition. Upper numbering was designed precisely to remove this obstruction.

Let $E/K$ be a possibly infinite Galois extension, with profinite group $\Gamma$. For $v\geq-1$, define

$$
\Gamma^v
=\varprojlim_N(\Gamma/N)^v,
$$

where $N$ runs over open normal subgroups and the finite quotient is interpreted as the Galois group of its fixed field. Herbrand's quotient theorem makes the transition maps compatible. Equivalently, $\Gamma^v$ is the intersection of the inverse images of all finite upper groups.

These are closed normal subgroups. We write

$$
I_K=\Gamma^0,
\qquad P_K=\Gamma^{0+}
$$

for inertia and wild inertia when $E$ is a separable closure of $K$, where in the profinite setting

$$
\Gamma^{v+}
=\overline{\bigcup_{w>v}\Gamma^w}.
$$

The closure is immaterial in a finite quotient but is part of the infinite convention. The quotient $I_K/P_K$ is pro-prime-to-$p$ and is procyclic after passage to a separably closed residue field; $P_K$ is pro-$p$. Precise descriptions of the tame quotient can require roots of unity, but its prime-to-$p$ nature is intrinsic.

### 6.2 Finite-image representations need only finite levels

Let $V$ be a finite-dimensional representation of a profinite local Galois group with finite image. Its kernel is open, so it factors through a finite quotient. All invariants in this book—fixed spaces, upper breaks, Artin conductor, and Swan conductor—are computed in that quotient. If a larger quotient is chosen, quotient compatibility gives the same answer.

This observation is enough for later applications to finite Galois modules and finite-image inertial types. No convergence of infinite sums over an absolute Galois group is needed. One computes in the finite field cut out by the representation.

### 6.3 Finite upper-break decompositions

Over a characteristic-zero coefficient field, a finite-image representation is semisimple. After extending scalars to a splitting field, its restriction to inertia decomposes according to finitely many upper breaks:

$$
V=\bigoplus_{r\geq0}V(r),
$$

where only finitely many summands are nonzero, $V(0)$ is the tame part, and for $r>0$ the subgroup $G^u$ acts trivially on $V(r)$ exactly when $u>r$. Then

$$
\operatorname{Sw}(V)=\sum_{r>0}r\dim V(r).
$$

For an abelian representation the breaks are integral by Hasse--Arf. For a general representation, rational breaks can occur, yet the total Swan conductor is still an integer. That stronger fact is a consequence of Artin's character theorem rather than of breakwise integrality.

## 7. The complementary module and the different

### 7.1 Measuring the defect of integral trace duality

Ramification groups require a Galois extension. The different exists for every finite separable extension and gives an intrinsic ideal-theoretic measure of ramification. Its starting point is the trace pairing

$$
(x,y)\longmapsto\operatorname{Tr}_{L/K}(xy).
$$

Over fields this pairing is perfect when $L/K$ is separable. Over valuation rings, however, the dual lattice of $B$ need not equal $B$. The discrepancy is the different.

Let $L/K$ be finite separable. The **complementary module** or **codifferent** is

$$
\mathfrak D_{L/K}^{-1}
=\{x\in L:\operatorname{Tr}_{L/K}(xB)\subseteq A\}.
$$

It is a fractional $B$-ideal containing $B$. Its inverse fractional ideal

$$
\mathfrak D_{L/K}
=\bigl(\mathfrak D_{L/K}^{-1}\bigr)^{-1}
$$

is the **different**. Since $B$ is a DVR,

$$
\mathfrak D_{L/K}=\mathfrak m_L^{d(L/K)}
$$

for a unique integer $d(L/K)\geq0$, the **different exponent**.

The definition has the form it does because $\operatorname{Hom}_A(B,A)$ is naturally a $B$-module. Nondegeneracy of trace identifies it with a lattice in $L$, precisely the codifferent. Inverting that enlarged dual lattice turns “failure of self-duality” into an integral ideal.

### 7.2 Unramifiedness and the different

If $L/K$ is unramified, the trace pairing on $B$ is perfect and

$$
\mathfrak D_{L/K}=B,
\qquad d(L/K)=0.
$$

Conversely, for a finite separable extension with separable residue extension, $d(L/K)=0$ implies that $L/K$ is unramified. Thus the different detects ramification exactly in the classical setting.

The residue-separability condition again prevents a false conclusion over imperfect fields. Extensions with $e=1$ and inseparable residue extension are not unramified, and their module of differentials can be nonzero even though the value group does not change.

### 7.3 The derivative formula

Suppose $B=A[\alpha]$ and let $f(T)\in A[T]$ be the minimal polynomial of $\alpha$. Then

$$
\boxed{\mathfrak D_{L/K}=(f'(\alpha)).}
$$

**Proof strategy.** The power basis has a trace-dual basis whose common denominator is $f'(\alpha)$. Lagrange interpolation supplies the duality explicitly.

Let $\alpha_1,\ldots,\alpha_n$ be the conjugates of $\alpha$ in a splitting field. For a polynomial $g$ of degree below $n$, interpolation expresses the coefficient of $T^{n-1}$ in $g(T)$ as

$$
\sum_{j=1}^n\frac{g(\alpha_j)}{f'(\alpha_j)}.
$$

The right side is a trace from $L$ after writing $g(\alpha)/f'(\alpha)$. Varying $g$ through suitable multiples of powers of $T$ produces the trace-dual of $1,\alpha,\ldots,\alpha^{n-1}$. Hence the complementary module is $f'(\alpha)^{-1}B$, proving the formula. $\square$

For an Eisenstein generator $\pi_L$, this becomes

$$
d(L/K)=v_L(f'(\pi_L)).
$$

It is often the fastest computational formula in nongalois as well as Galois extensions.

### 7.4 Kähler differentials

The derivative appears because infinitesimal variation of the relation $f(\alpha)=0$ gives

$$
f'(\alpha)\,d\alpha=0.
$$

For a monogenic presentation $B=A[\alpha]$,

$$
\Omega_{B/A}\cong B/(f'(\alpha))\,d\alpha.
$$

Thus the zeroth Fitting ideal of $\Omega_{B/A}$ is the different. More generally, for a finite generically separable complete-intersection extension of DVRs, the Kähler different—the zeroth Fitting ideal of $\Omega_{B/A}$—agrees with the trace different.

This gives a geometric interpretation. Unramifiedness means there are no relative infinitesimal directions; ramification creates torsion differentials, and the different measures their total length:

$$
d(L/K)=\operatorname{length}_B\Omega_{B/A}
$$

under the stated complete-intersection hypotheses. In the standard classical setting with separable residue extension, local monogenicity supplies those hypotheses. Without such a presentation, one should retain the complementary-module definition rather than silently assume a derivative generator.

### 7.5 Exact trace ideals

The different refines the coarse trace inclusion from the unit theory into an exact formula. Let $L/K$ be finite separable and write

$$
\mathfrak D_{L/K}=\mathfrak m_L^d.
$$

Then for every integer $n$,

$$
\boxed{
\operatorname{Tr}_{L/K}(\mathfrak m_L^n)
=\mathfrak m_K^{\left\lfloor (n+d)/e\right\rfloor}.}
$$

Here fractional powers are allowed when $n<0$. To understand the exponent, ask for the largest integer $r$ such that the trace ideal lies in $\mathfrak m_K^r$. By definition of the codifferent,

$$
\operatorname{Tr}(\mathfrak m_L^n)\subseteq\mathfrak m_K^r
$$

is equivalent to

$$
\pi_K^{-r}\mathfrak m_L^n
\subseteq\mathfrak D_{L/K}^{-1}
=\mathfrak m_L^{-d}.
$$

Since $v_L(\pi_K)=e$, this says $n-er\geq-d$, or $r\leq(n+d)/e$. The greatest possible integer is the displayed floor. Nondegeneracy of trace duality gives equality rather than only containment.

Several earlier facts now become sharper. In an unramified extension, $d=0$ and $e=1$, so $\operatorname{Tr}(\mathfrak m_L^n)=\mathfrak m_K^n$. In a tame totally ramified extension, $d=e-1$, and

$$
\operatorname{Tr}(B)=A,\qquad
\operatorname{Tr}(\mathfrak m_L)=\mathfrak m_K.
$$

For $\mathbf Q_2(\sqrt2)/\mathbf Q_2$, $e=2,d=3$, so $\operatorname{Tr}(B)=2\mathbf Z_2$. Directly,

$$
\operatorname{Tr}(a+b\sqrt2)=2a,
$$

which confirms the formula. Wild ramification has pushed the integral trace into the maximal ideal.

The formula also sharpens the first-order behavior of norms. If $x\in\mathfrak m_L^n$, then

$$
N_{L/K}(1+x)
=1+\operatorname{Tr}_{L/K}(x)+
\text{terms of degree at least two}.
$$

The different determines the exact ideal in which the linear term ranges. When that trace ideal is unexpectedly deep, successive norm equations can fail to be solvable even though the residue norm is surjective. This is the precise bridge between wild ramification, trace divisibility, and the norm obstructions that were only qualitatively visible from unit filtrations.

### 7.6 Tame and wild derivative bounds

Let $L/K$ be totally ramified of degree $e$, generated by a uniformizer with Eisenstein minimal polynomial

$$
f(T)=T^e+a_{e-1}T^{e-1}+\cdots+a_0.
$$

Every nonleading coefficient has positive $K$-valuation. Evaluating $f'$ at $\pi_L$ shows

$$
d(L/K)\geq e-1.
$$

If $p\nmid e$, the leading derivative term $e\pi_L^{e-1}$ has value $e-1$, while every other term has larger value, so

$$
d(L/K)=e-1.
$$

If $p\mid e$, cancellation or extra divisibility forces

$$
d(L/K)\geq e,
$$

for a nontrivial totally ramified separable extension. Hence, with separable residue extension, tameness is equivalently characterized by

$$
d(L/K)=e(L/K)-1
$$

in the totally ramified case, and in general by

$$
d(L/K)=e(L/K)-1
$$

because the unramified stage contributes zero. Wildness is exactly the presence of excess different beyond the tame baseline.

### 7.7 Further derivative calculations

Cyclotomic and radical equations provide useful mixed-characteristic tests. Let $p$ be odd and $L=\mathbf Q_p(\zeta_p)$. The extension is totally ramified of degree $p-1$, hence tame. If $\lambda=\zeta_p-1$, then $\lambda$ is a uniformizer and its Eisenstein polynomial is

$$
\frac{(1+T)^p-1}{T}.
$$

Tameness already predicts

$$
d(L/\mathbf Q_p)=p-2.
$$

Differentiating the polynomial and evaluating at $\lambda$ gives the same value. Although $p$ itself is highly divisible upstairs, the degree $p-1$ remains prime to the residue characteristic, so there is no wild excess.

For $K=\mathbf Q_p(\zeta_p)$ and $L=K(\alpha)$ with $\alpha^p=\zeta_p-1$, Section 3.5 found a wild break at $p$. The derivative is

$$
f'(\alpha)=p\alpha^{p-1}.
$$

With $v_L(p)=p(p-1)$ and $v_L(\alpha)=1$,

$$
d(L/K)=p(p-1)+(p-1)=p^2-1.
$$

In equal characteristic, the Artin--Schreier equation $y^p-y=t^{-m}$ is not an integral monogenic presentation in the displayed coordinate because $y$ has negative valuation. Hilbert's formula is therefore more natural than differentiating that equation: it immediately gives $(m+1)(p-1)$. A change to an integral generator would recover the same derivative exponent but obscure the transparent Galois action.

## 8. Discriminants

### 8.1 From a dual lattice to an ideal downstairs

The different is an ideal of $B$ and therefore lives upstairs. The discriminant packages the same defect as an ideal of $A$, which makes it suitable for global arithmetic and for comparison among fields.

For an $A$-basis $b_1,\ldots,b_n$ of $B$, define

$$
\operatorname{disc}(b_1,\ldots,b_n)
=\det\bigl(\operatorname{Tr}_{L/K}(b_ib_j)\bigr).
$$

Changing the basis multiplies this element by the square of a unit of $A$. The principal ideal it generates is the **relative discriminant ideal**

$$
\mathfrak d_{L/K}\subseteq A.
$$

For a finite separable extension,

$$
\boxed{\mathfrak d_{L/K}=N_{L/K}(\mathfrak D_{L/K}).}
$$

Indeed, the determinant of the inclusion of $B$ into its trace dual measures the discriminant, while the ideal norm measures the same lattice index. Since

$$
v_K(N_{L/K}(x))=f(L/K)v_L(x),
$$

the discriminant exponent is

$$
\delta(L/K):=v_K(\mathfrak d_{L/K})
=f(L/K)d(L/K).
$$

Confusing $d$ with $\delta$ loses a factor of residue degree. They agree for totally ramified extensions, but not in general.

### 8.2 Polynomial discriminants and the index correction

If $B=A[\alpha]$ and $f$ is the monic minimal polynomial of $\alpha$, then

$$
\operatorname{disc}(1,\alpha,\ldots,\alpha^{n-1})
=(-1)^{n(n-1)/2}N_{L/K}(f'(\alpha)).
$$

Thus its ideal is $\mathfrak d_{L/K}$. If $A[\alpha]$ is a proper order in $B$, the polynomial discriminant is not the field discriminant. If the index ideal of $A[\alpha]\subset B$ is generated by a determinant $c$, then

$$
(\operatorname{disc}f)=\mathfrak d_{L/K}(c)^2.
$$

Repeated reduction of a poorly chosen polynomial can therefore exaggerate ramification. The square index correction is the exact measure of that exaggeration.

For $f(T)=T^e-\pi_K$ with $p\nmid e$, the derivative is $e\pi_L^{e-1}$, so $d=e-1$. For $\mathbf Q_2(\sqrt2)$, $f'(\sqrt2)=2\sqrt2$ has $L$-valuation $3$, hence the discriminant exponent is $3$. The familiar polynomial discriminant $8$ has $2$-adic valuation $3$, agreeing because the extension is totally ramified and the power basis is integral.

### 8.3 Transitivity of the different

Let $K\subseteq M\subseteq L$ be finite separable extensions of complete discretely valued fields. Trace transitivity implies a precise product formula:

$$
\boxed{
\mathfrak D_{L/K}
=\mathfrak D_{L/M}\,
\mathfrak D_{M/K}\mathcal O_L.}
$$

To see the mechanism, first dualize $\mathcal O_L$ over $\mathcal O_M$ using $\operatorname{Tr}_{L/M}$, then dualize $\mathcal O_M$ over $A$ using $\operatorname{Tr}_{M/K}$. The composition is duality over $A$, and inverse fractional ideals turn the two dual enlargements into the displayed product.

Taking valuations gives

$$
d(L/K)
=d(L/M)+e(L/M)d(M/K).
$$

The factor $e(L/M)$ appears because an ideal of $\mathcal O_M$ acquires that many $L$-valuation units after extension to $\mathcal O_L$.

### 8.4 Discriminants in towers

Norming the different transitivity formula down to $K$ gives

$$
\boxed{
\mathfrak d_{L/K}
=\mathfrak d_{M/K}^{[L:M]}
N_{M/K}(\mathfrak d_{L/M}).}
$$

In exponent form,

$$
\delta(L/K)
=[L:M]\delta(M/K)
+f(M/K)\delta(L/M),
$$

where $\delta(L/M)$ is normalized using $v_M$. This can also be checked from $\delta=fd$ together with multiplicativity of $e$ and $f$.

The formula explains why ramification low in a tower is expensive: the discriminant contribution of $M/K$ is repeated once for each dimension of $L$ over $M$. Ramification introduced only at the top is first measured over $M$ and then transferred by the ideal norm.

For a finite separable nongalois extension, these formulas remain valid without passing to a Galois closure. A Galois closure is useful for interpreting the same exponent through ramification groups, but the trace-dual definitions are intrinsic.

### 8.5 Base change cautions

Unramified base change preserves the different exponent of a totally ramified extension when the tensor product remains a field: the uniformizer scale is unchanged and the defining Eisenstein derivative has the same value. Arbitrary ramified base change can reduce, split, or otherwise alter ramification, so there is no unconditional base-change equality.

Discriminants are especially sensitive to splitting. If $L\otimes_KK'$ is a product of fields, its discriminant as a finite $K'$-algebra is the product of the discriminants of the factors; cross terms disappear through orthogonal idempotents. One should not choose a single factor without specifying the corresponding embedding or prime.

## 9. Hilbert's different formula

### 9.1 The formula and its hypotheses

The different was defined using trace, while lower ramification groups were defined using congruence. Hilbert's formula identifies them.

**Theorem 9.1 (Hilbert's different formula).** Let $L/K$ be a finite Galois extension of complete discretely valued fields, and assume $l/k$ is separable. Then

$$
\boxed{
d(L/K)=\sum_{\sigma\ne1}i_G(\sigma)
=\sum_{i\geq0}(|G_i|-1).}
$$

Both sums are finite. No assumption that $k$ is finite, or that $K$ has characteristic zero, is needed.

The residue-separability hypothesis ensures an integral monogenic generator and the uniformizer displacement formula. There are more general versions for imperfect residue phenomena, but the displayed classical formula should not be applied to a fiercely ramified extension without modification.

### 9.2 Proof by a well-chosen generator

The proof has two decisive steps. First, choose an integral generator whose conjugate differences realize the displacement depths. Second, recognize the product of those differences as the derivative of its minimal polynomial.

Choose a lift $\theta$ of a separating generator of $l/k$ in the maximal unramified subextension and a uniformizer $\pi_L$. Put

$$
\alpha=\theta+\pi_L.
$$

The local monogenicity argument recovers $\theta$ from $\alpha$ by Hensel lifting and then recovers $\pi_L=\alpha-\theta$, so $B=A[\alpha]$. Moreover, for every nonidentity $\sigma$,

$$
v_L(\sigma(\alpha)-\alpha)=i_G(\sigma).
$$

Indeed, a residue-moving automorphism moves $\bar\theta$, so the difference has value $0$. An inertial automorphism fixes $\theta$ and is detected by $\sigma(\pi_L)-\pi_L$, whose value is $i_G(\sigma)$. This is the decisive reason for mixing an unramified generator with a ramified parameter.

Let

$$
f(T)=\prod_{\sigma\in G}(T-\sigma\alpha)
$$

be the minimal polynomial. The derivative at $\alpha$ is

$$
f'(\alpha)=\prod_{\sigma\ne1}(\alpha-\sigma\alpha).
$$

Because $B=A[\alpha]$, the derivative formula for the different gives

$$
d(L/K)=v_L(f'(\alpha))
=\sum_{\sigma\ne1}v_L(\alpha-\sigma\alpha)
=\sum_{\sigma\ne1}i_G(\sigma).
$$

It remains only to count. An element $\sigma\ne1$ contributes one to $|G_i|-1$ exactly for

$$
i=0,1,\ldots,i_G(\sigma)-1.
$$

Thus it occurs $i_G(\sigma)$ times in the double sum, and

$$
\sum_{i\geq0}(|G_i|-1)
=\sum_{\sigma\ne1}i_G(\sigma).
$$

This proves the theorem. $\square$

The proof reveals why the shift in $G_i$ was useful: an automorphism of displacement $r$ contributes exactly $r$ units to the different.

### 9.3 Tame and wild parts of the different

Separate the $i=0$ term:

$$
d(L/K)
=(|G_0|-1)+\sum_{i\geq1}(|G_i|-1).
$$

When $l/k$ is separable, $|G_0|=e$. The first term $e-1$ is the tame baseline. The remaining nonnegative integer

$$
\operatorname{sw}(L/K)
:=\sum_{i\geq1}(|G_i|-1)
$$

is the wild excess for the regular action. It vanishes exactly when $G_1=1$, equivalently when $L/K$ is tame.

For the Artin--Schreier extension with break $m$ and group order $p$,

$$
d=(m+1)(p-1).
$$

For $\mathbf Q_2(\sqrt2)/\mathbf Q_2$, the groups $G_0,G_1,G_2$ all have order $2$, giving $d=3$. For the wild Kummer extension of Section 3.5, the groups through $G_p$ have order $p$, giving

$$
d=(p+1)(p-1)=p^2-1.
$$

The derivative gives the same answer:

$$
v_L(p\alpha^{p-1})
=p(p-1)+(p-1)=p^2-1.
$$

### 9.4 A tower check

Hilbert's formula must agree with transitivity of the different. Suppose $H\triangleleft G$ with fixed field $M$. The subgroup formula gives the lower groups for $L/M$, while Herbrand's quotient theorem determines those for $M/K$ after changing scales. Substituting both into

$$
d(L/K)=d(L/M)+e(L/M)d(M/K)
$$

is a nontrivial consistency check on the Herbrand function. Its slopes are exactly the weights needed to transform the two sums correctly.

This is another way to understand why lower groups suit subextensions and upper groups suit quotients. The different is transitive through both operations, so the correct reindexing must reconcile them.

### 9.5 Upper-numbered form and a discriminant bound

Hilbert's formula can be converted to upper numbering. With our left-continuous convention,

$$
d(L/K)
=(|G_0|-1)
+\int_0^\infty(|G_u|-1)\,du.
$$

The isolated term is necessary because the integral begins immediately to the right of $0$, where the lower group is already $G_1$. Under the change of variables $v=\varphi(u)$,

$$
du=[G_0:G^v]\,dv
=\frac{|G_0|}{|G^v|}\,dv.
$$

Hence

$$
d(L/K)
=(|G_0|-1)
+|G_0|\int_0^\infty
\left(1-\frac1{|G^v|}\right)\,dv,
$$

where the integrand is understood to be zero after $G^v$ becomes trivial. This formula is particularly well adapted to a representation-theoretic bound on the last upper break.

Suppose $G^v=1$ for $v>R$. Since $|G_0|=e$ under our residue-separability hypothesis,

$$
d(L/K)\leq(e-1)+eR,
$$

and therefore

$$
\delta(L/K)\leq f\bigl((e-1)+eR\bigr).
$$

The estimate is intentionally coarse, because it ignores all intermediate drops, but it requires only the inertia size and a last-break bound. That is exactly the form needed when a geometric or representation-theoretic argument controls ramification depth without determining every group.

## 10. Conductors of finite-image representations

### 10.1 What a conductor should measure

An extension records ramification of a field. A representation records only the part of that ramification visible on a vector space. If a ramification group acts trivially, its depth should contribute nothing; if it moves a large quotient of the space, it should contribute proportionally to that codimension.

Let $E$ be a field of characteristic zero, and let

$$
\rho:G\longrightarrow\operatorname{GL}(V)
$$

be a finite-dimensional representation with finite image. After replacing $G$ by that finite image together with the finite local Galois quotient through which it arises, we may use the groups $G_i$. Characteristic zero is important: averaging makes invariants exact and finite-group representations semisimple. The same definitions apply to finite-image $\ell$-adic representations after scalar extension. In coefficient characteristic dividing $|G|$, Brauer-character refinements are needed; the simple semisimple assertions below are not being claimed.

### 10.2 Artin and Swan conductors

The **Artin conductor exponent** is

$$
a_K(V)
=\sum_{i\geq0}\frac{|G_i|}{|G_0|}
\operatorname{codim}_E V^{G_i}.
$$

Its tame part is

$$
t_K(V)=\operatorname{codim}V^{G_0},
$$

and its **Swan conductor** is

$$
\operatorname{Sw}_K(V)
=\sum_{i\geq1}\frac{|G_i|}{|G_0|}
\operatorname{codim}V^{G_i}.
$$

Thus

$$
a_K(V)=t_K(V)+\operatorname{Sw}_K(V).
$$

The weights have a structural origin. A lower interval of length one becomes an upper interval of length $|G_i|/|G_0|$. Consequently Swan can also be written as the upper-depth area

$$
\operatorname{Sw}_K(V)
=\int_{0}^{\infty}\operatorname{codim}V^{G^v}\,dv,
$$

with endpoint values irrelevant to the integral. The fixed-space function is a step function with finite support.

### 10.3 Independence of the cutting field

Suppose the representation factors through two finite Galois extensions, one containing the other. In the larger quotient, some normal subgroup acts trivially on $V$. Herbrand's quotient theorem identifies upper ramification groups after projection, so the upper integral is unchanged. Hence $a_K(V)$ and $\operatorname{Sw}_K(V)$ depend only on the representation, not on the chosen finite extension that realizes it.

For an absolute Galois group, this is the definition: choose any finite Galois extension through which the finite image factors and compute there. The quotient compatibility proved earlier is what makes the result canonical.

### 10.4 Immediate specializations

The formulas pass several useful tests.

- If $V$ is unramified, $G_0$ acts trivially and $a_K(V)=0$.
- If $V$ is tamely ramified, $G_1$ acts trivially, so $\operatorname{Sw}_K(V)=0$ and
  $$
  a_K(V)=\operatorname{codim}V^I.
  $$
- The trivial representation has conductor zero.
- A nontrivial one-dimensional tame character has conductor $1$.
- If a one-dimensional character has a unique upper break $r>0$, then
  $$
  \operatorname{Sw}(\chi)=r,
  \qquad a(\chi)=r+1.
  $$

The last statement, together with integrality of character conductors, is the character-theoretic shadow of Hasse--Arf.

## 11. The Artin character and integrality

### 11.1 Why the weighted sum is an integer

The fixed-space formula for $a_K(V)$ is visibly nonnegative but appears merely rational, because of the factors $|G_i|/|G_0|$. Its integrality is a theorem, not a consequence of termwise divisibility.

Assume as before that $L/K$ is finite Galois with separable residue extension. Define a class function $A_G$ on $G$ by

$$
A_G(\sigma)=
\begin{cases}
-f(L/K)i_G(\sigma),&\sigma\ne1,\\
f(L/K)\displaystyle\sum_{\tau\ne1}i_G(\tau),&\sigma=1.
\end{cases}
$$

It is constant on conjugacy classes because displacement is conjugation-invariant. It also has total sum zero. If $\chi_V$ is the character of $V$, then

$$
\boxed{a_K(V)=\langle A_G,\chi_V\rangle_G.}
$$

Here the character pairing may be written with $\chi_V(\sigma^{-1})$; replacing $\sigma$ by $\sigma^{-1}$ does not change $i_G(\sigma)$.

To verify the identity, note that $|G|=ef$ and $|G_0|=e$. Therefore

$$
\langle A_G,\chi_V\rangle_G
=\frac1{|G_0|}\sum_{\sigma\ne1}
i_G(\sigma)\bigl(\dim V-\chi_V(\sigma)\bigr).
$$

Now count $\sigma$ once for every $i$ with $\sigma\in G_i$, and use the averaging projector

$$
\frac1{|G_i|}\sum_{\sigma\in G_i}\rho(\sigma)
$$

onto $V^{G_i}$. The contribution at level $i$ becomes

$$
\frac{|G_i|}{|G_0|}
\bigl(\dim V-\dim V^{G_i}\bigr),
$$

which is precisely the conductor formula.

### 11.2 Artin's integrality theorem

**Theorem 11.1 (integrality).** Under the preceding hypotheses, $A_G$ is the character of a finite-dimensional characteristic-zero representation of $G$. Consequently, for every finite-dimensional characteristic-zero representation $V$,

$$
a_K(V),\ \operatorname{Sw}_K(V)\in\mathbf Z_{\geq0}.
$$

The theorem remains valid for any finite-image representation of the absolute Galois group, since it may be computed in a finite quotient.

A proof of the character assertion proceeds by reducing character inner products to cyclic subgroups. On a cyclic subgroup, the values of $i_G$ are nested by divisibility and the corresponding differences are nonnegative multiples of augmentation characters. Induction from cyclic subgroups and the integrality criterion for rational class functions then assemble $A_G$. The identity of Section 11.1 shows nonnegativity directly for every actual representation. Subtracting the integer tame term gives integrality of Swan.

The exact hypotheses matter. The coefficient field must have characteristic zero, or one must replace ordinary characters by an appropriate modular theory. The local extension used for the classical $i_G$ formula is taken with separable residue extension. Neither the residue field nor the coefficient field needs to be finite.

### 11.3 Additivity and exact sequences

Fixed spaces commute with direct sums, so

$$
a_K(V\oplus W)=a_K(V)+a_K(W),
\qquad
\operatorname{Sw}_K(V\oplus W)
=\operatorname{Sw}_K(V)+\operatorname{Sw}_K(W).
$$

More generally, a short exact sequence of finite-image characteristic-zero representations splits as a representation of the finite image. Hence Artin and Swan conductors are additive in short exact sequences. This is essential when a representation is analyzed through its irreducible constituents.

Duality preserves fixed-space codimensions for finite groups in characteristic zero, so

$$
a_K(V^\vee)=a_K(V),
\qquad
\operatorname{Sw}_K(V^\vee)=\operatorname{Sw}_K(V).
$$

Twisting by an unramified character changes Frobenius but not inertia, and therefore leaves both conductors unchanged. A ramified twist can change break structure; no formula depending only on the two separate conductor exponents exists without information about coincident characters on ramification groups.

### 11.4 Fixed-space calculations

Suppose $V$ is two-dimensional. If inertia acts trivially, $a(V)=0$. If inertia acts tamely through a nontrivial character on one line and trivially on the other, then $\dim V^I=1$ and

$$
a(V)=1.
$$

If tame inertia acts without fixed vectors, the conductor is $2$. These elementary cases are the local patterns later encountered in two-dimensional representations.

For a wild cyclic group of order $p$ with unique lower break $m$, let $\chi$ be a nontrivial one-dimensional character. Then $V^{G_i}=0$ for $0\leq i\leq m$ and equals $V$ afterward. Since $G_i=G_0$ throughout that interval,

$$
a(\chi)=m+1,
\qquad \operatorname{Sw}(\chi)=m.
$$

For the direct sum of all $p-1$ nontrivial characters, additivity gives conductor $(p-1)(m+1)$, already suggesting the different formula for the regular representation.

## 12. Induction, restriction, and base change

### 12.1 Why functorial formulas need normalization factors

Representations are moved between local Galois groups by restriction and induction. Conductors cannot be functorial without correction: induction increases dimension and introduces the ramification of the field extension itself, while restriction changes the valuation scale used to label depth.

Let $M/K$ be finite separable, and let $W$ be a finite-dimensional finite-image characteristic-zero representation of the absolute Galois group of $M$. Then the induction formula is

$$
\boxed{
a_K\bigl(\operatorname{Ind}_{M}^{K}W\bigr)
=f(M/K)\bigl(d(M/K)\dim W+a_M(W)\bigr).}
$$

Equivalently, because $\delta(M/K)=f(M/K)d(M/K)$,

$$
a_K\bigl(\operatorname{Ind}_{M}^{K}W\bigr)
=\delta(M/K)\dim W+f(M/K)a_M(W).
$$

The first term is the cost of permuting the embeddings of $M$; the second transfers the ramification already present in $W$. The residue-degree factor converts an exponent normalized over $M$ into one normalized over $K$.

### 12.2 Strategy of the induction formula

Choose a finite Galois extension of $K$ containing the field cut out by $W$ and a Galois closure of $M$. The induced character is computed by summing the character of $W$ over conjugates whose action returns a chosen coset to itself. Pairing this with the Artin character separates into two contributions.

The off-stabilizer contribution measures the discriminant of the permutation action on embeddings of $M$ and equals $\delta(M/K)\dim W$. The stabilizer contribution is the Artin pairing over $M$, but each $M$-valuation layer contributes $f(M/K)$ base-field units. This yields the formula. For $W=1$, it reduces to the conductor--discriminant identity proved in the next chapter; general $W$ follows from the same character calculation or from additivity after induction from cyclic characters.

### 12.3 Restriction through a finite Galois realization

Suppose $L/K$ is finite Galois, $M=L^H$, and $V$ is a representation of $G$. The lower subgroup theorem gives an exact, if not degree-only, restriction formula:

$$
a_M(V|_H)
=\sum_{i\geq0}
\frac{|H\cap G_i|}{|H\cap G_0|}
\operatorname{codim}V^{H\cap G_i}.
$$

This is often more useful than a purported closed formula: restriction can create fixed vectors, especially by killing tame characters, so the answer cannot depend only on $e(M/K)$ and $a_K(V)$.

Two clean cases deserve emphasis. If $M/K$ is unramified, the absolute inertia groups and their upper numbering agree, and

$$
a_M(V|_{G_M})=a_K(V),
\qquad
\operatorname{Sw}_M(V|_{G_M})=\operatorname{Sw}_K(V).
$$

If $M/K$ is tamely ramified of ramification index $e$, positive upper depth is rescaled by $e$, giving

$$
\operatorname{Sw}_M(V|_{G_M})
=e\operatorname{Sw}_K(V).
$$

The tame term must still be recomputed as $\operatorname{codim}V^{I_M}$, because $I_M$ can be a proper subgroup of $I_K$. For arbitrary wild base change, even Swan requires the full Herbrand transition; there is no universal linear scaling.

### 12.4 Towers and transitivity

For $K\subseteq M\subseteq N$, applying induction twice agrees with induction in one step. The conductor formula respects this because

$$
d(N/K)=d(N/M)+e(N/M)d(M/K)
$$

and $e,f$ multiply. Expanding both routes gives the same coefficient of $\dim W$ and the same transferred conductor $f(N/K)a_N(W)$.

This consistency is a powerful normalization check. Omitting $f(M/K)$ or confusing $d$ with $\delta$ breaks transitivity immediately.

## 13. Conductor--discriminant identities

### 13.1 The permutation representation of embeddings

Let $M/K$ be finite separable, not necessarily Galois. The absolute Galois group of $K$ acts on the set

$$
\operatorname{Hom}_K(M,K^{\mathrm{sep}}).
$$

The associated permutation representation is

$$
\mathbf 1_M^K
=\operatorname{Ind}_{G_M}^{G_K}\mathbf1.
$$

Putting $W=\mathbf1$ in the induction formula gives the fundamental conductor--discriminant relation

$$
\boxed{
a_K(\mathbf1_M^K)=\delta(M/K)
=v_K(\mathfrak d_{M/K}).}
$$

Thus the discriminant of a nongalois extension is the conductor of the action on its embeddings. This formulation is intrinsic and avoids assigning ramification groups directly to a nongalois group that does not exist.

### 13.2 The regular representation

If $L/K$ is Galois with group $G$, the embedding set is $G$ itself with its regular action. Let $E[G]$ denote the regular representation. For a subgroup $G_i$, its invariant functions are constant on $G_i$-orbits, so

$$
\dim E[G]^{G_i}=\frac{|G|}{|G_i|}.
$$

Therefore

$$
\begin{aligned}
a_K(E[G])
&=\sum_{i\geq0}\frac{|G_i|}{|G_0|}
\left(|G|-\frac{|G|}{|G_i|}\right)\\
&=\frac{|G|}{|G_0|}
\sum_{i\geq0}(|G_i|-1)\\
&=f(L/K)d(L/K)\\
&=\delta(L/K).
\end{aligned}
$$

This calculation visibly unites the three languages: fixed-space defects give the ramification-group sum, Hilbert turns it into the different, and the residue-degree factor norms it to the discriminant.

### 13.3 Decomposition into irreducible characters

Over a splitting field of characteristic zero, the regular representation decomposes as

$$
E[G]\cong\bigoplus_{\chi\in\operatorname{Irr}(G)}
(\dim\chi)V_\chi.
$$

Additivity of the conductor yields

$$
\boxed{
\delta(L/K)
=\sum_{\chi\in\operatorname{Irr}(G)}
(\dim\chi)a_K(\chi).}
$$

If $G$ is abelian, every irreducible character is one-dimensional, so

$$
\delta(L/K)=\sum_{\chi\in\widehat G}a_K(\chi).
$$

Writing the conductor ideal of $\chi$ as $\mathfrak f(\chi)=\mathfrak m_K^{a_K(\chi)}$, this becomes the ideal identity

$$
\mathfrak d_{L/K}
=\prod_{\chi\in\widehat G}\mathfrak f(\chi).
$$

The trivial character contributes the unit ideal. This is the local conductor--discriminant formula for abelian extensions.

### 13.4 A cyclic wild example revisited

Take the cyclic degree-$p$ Artin--Schreier extension with break $m$. There are $p-1$ nontrivial characters, each of conductor $m+1$. Hence

$$
\sum_\chi a(\chi)=(p-1)(m+1),
$$

which equals the discriminant exponent because the extension is totally ramified. The same number arose from the derivative, from Hilbert's group count, and from the regular representation. Agreement among four computations is a useful diagnostic for index conventions.

In the tame cyclic case of degree $e$, each of the $e-1$ nontrivial characters has conductor $1$. Their sum is $e-1$, the tame discriminant exponent.

### 13.5 Discriminants of fields cut out by representations

Let $\rho$ have finite image $G$, and let $L/K$ be its fixed field. The discriminant of $L/K$ is not generally equal to the conductor of $V$: the regular representation sees every element of $G$, whereas $V$ may have many fixed directions. What is always true is

$$
\delta(L/K)=a_K(E[G]).
$$

If $V$ is faithful, its upper breaks detect exactly where the finite quotient becomes trivial, so they bound the breaks of $L/K$. Turning those break bounds into a discriminant bound uses

$$
\delta(L/K)=f(L/K)\sum_{i\geq0}(|G_i|-1)
$$

or its upper-numbered integral form. This is the interface used in discriminant estimates for torsion fields: group size controls the height of the integrand, while representation-theoretic ramification bounds control its support.

## 14. Nongalois extensions and imperfect residues

### 14.1 What remains intrinsic without Galois symmetry

For a finite separable nongalois extension $M/K$, the valuation, ramification index, residue degree, complementary module, different, discriminant, and their tower formulas are all intrinsic. A monogenic presentation gives the derivative formula whenever $\mathcal O_M=A[\alpha]$.

What is absent is a group of order $[M:K]$ acting on $M$. Lower and upper ramification groups should therefore not be attached directly to $M/K$. One may pass to a finite Galois closure $L/K$, choose the subgroup $H=\operatorname{Gal}(L/M)$, and study both the filtration of $G$ and its action on $G/H$. The permutation conductor is independent of the chosen closure and recovers $\delta(M/K)$.

A finite separable extension $M/K$ with separable residue extension is tame exactly when $p\nmid e(M/K)$. Equivalently, a Galois closure is tame. This equivalence uses the fact that tame extensions are stable under compositum and subextension. It can fail as phrased if residue inseparability is ignored.

### 14.2 Normal closures and overcounting

Passing to a normal closure can introduce more ramification than is visible in one chosen field. The correct way to descend is through a permutation representation, not by identifying $\delta(M/K)$ with $\delta(L/K)$. The latter discriminant usually has much larger degree and multiplicities.

For example, a nongalois cubic extension has a Galois closure of degree six in the generic case. The cubic discriminant is the conductor of the three-point permutation action, whereas the closure discriminant is the conductor of the six-dimensional regular action. They are related through representation theory but are not equal.

### 14.3 Purely inseparable extensions

If $L/K$ is purely inseparable, the trace pairing is degenerate—indeed the trace may vanish identically—so the complementary-module definition above does not produce the same finite fractional ideal. The derivative of a minimal polynomial can be zero. Artin and Swan conductors, being invariants of separable Galois actions, are not invariants of such an extension.

Valuation theory still supplies $e$, $f$, and $[L:K]=ef$ for finite extensions of complete discretely valued fields. One can also study $\Omega_{B/A}$, which directly records inseparability. These facts belong beside, not inside, the classical separable ramification filtration. The distinction is especially important over imperfect residue fields, where a separable field extension can nevertheless induce inseparable residue growth.

### 14.4 A hypothesis map

It is useful to collect the logical boundaries.

- Completeness and discreteness give unique valuation extension, finite freeness, and $[L:K]=ef$.
- Separability of $L/K$ makes the trace pairing nondegenerate and defines the different as a finite ideal.
- Galois symmetry defines ramification groups on the field itself.
- Separability of $l/k$ gives $|G_0|=e$, local monogenicity in the form used above, and the clean classical Hilbert formula.
- Perfection of $k$ implies separability of every finite residue extension, but is stronger than needed in any one theorem.
- Finiteness of $k$ adds canonical Frobenius, cyclic residue multiplicative groups, and local compactness; it is irrelevant to the definitions of ramification groups, the different, and conductors.
- Characteristic zero for representation coefficients gives semisimplicity and ordinary-character formulas; it is unrelated to the characteristic of $K$.

Keeping these hypotheses separate allows equal- and mixed-characteristic arguments to share one theory without silently treating every residue field as finite.

## 15. A working synthesis

### 15.1 The ramification dictionary

For a finite Galois extension with separable residue extension, all of the main invariants can now be read from one filtration:

$$
\begin{array}{c|c}
\text{object} & \text{ramification meaning}\\
\hline
G/G_0 & \text{residue-field symmetry}\\
G_0/G_1 & \text{cyclic tame inertia}\\
G_i/G_{i+1},\ i\geq1 & \text{additive residue-characteristic layers}\\
\sum_{i\geq0}(|G_i|-1) & d(L/K)\\
f\sum_{i\geq0}(|G_i|-1) & \delta(L/K)\\
\sum_{i\geq0}\dfrac{|G_i|}{|G_0|}
\operatorname{codim}V^{G_i} & a_K(V).
\end{array}
$$

Lower numbering measures actual valuation displacement and survives passage to a subgroup. The Herbrand function converts it into upper numbering, which survives passage to a quotient and therefore extends to profinite Galois groups. The different turns total displacement into an ideal upstairs; the norm turns that ideal into the discriminant downstairs. A conductor replaces the count $|G_i|-1$ by the codimension actually moved in a representation.

### 15.2 A calculation protocol

For a concrete finite local extension, the following order is reliable.

First identify the residue extension and ramification index, checking residue separability. If the extension is Galois, determine inertia and the tame character. Choose an integral generator or uniformizer only after proving it generates the integral ring. Compute displacements $v_L(\sigma(\pi_L)-\pi_L)$ to obtain lower groups. Use the Herbrand function only when quotients or towers require upper numbering.

Next compute the different either from $f'(\alpha)$ or from Hilbert's formula, and compare the answers when both apply. Multiply by $f$ to obtain the discriminant exponent. In a tower, verify

$$
d(L/K)=d(L/M)+e(L/M)d(M/K).
$$

Finally, for a representation compute fixed spaces on each nontrivial group. The tame codimension and the positive-depth area give Artin and Swan conductors. For a nongalois field use its embedding permutation representation. Each step has an independent normalization check, making errors detectable before they propagate.

### 15.3 Consequences for two-dimensional arithmetic

In a two-dimensional representation, inertia can be invisible, move one line, or move the entire space. Tame cases are therefore controlled by a codimension $0$, $1$, or $2$. Wild inertia adds a weighted depth, the Swan conductor. Upper numbering makes these statements stable when the representation is replaced by its finite quotient or when a normal subfield is removed.

For torsion fields, a faithful finite representation determines a finite Galois extension. Bounds on the last upper break and on the group order feed directly into Hilbert's formula and hence into a discriminant bound. In integral geometric situations, separate structure theorems may impose especially small upper breaks; the present theory then converts those local constraints into numerical discriminant estimates without changing language.

For elliptic curves, later reduction theory will identify the shape of inertia on torsion and Tate modules. The conductor formalism will turn fixed subspaces and wild action into local exponents. The discriminant theory developed here concerns field extensions and trace lattices; it must not be confused with the discriminant of a Weierstrass equation, though later the two kinds of discriminant will interact through ramification and reduction.

### 15.4 Final perspective

Ramification begins where reduction stops. Inertia records automorphisms lost modulo the maximal ideal; the lower filtration asks how many further digits are needed before each automorphism appears. Its first quotient is multiplicative and prime to the residue characteristic, while every deeper quotient is additive and residue-characteristic primary. This is the structural division between tame and wild behavior.

Raw depth is not stable under quotienting, so the Herbrand function replaces the valuation clock by one weighted according to the symmetries still present. Upper numbering is therefore the natural language of Galois towers and finite continuous representations. The different reaches the same structure from the opposite direction: it measures how far the integral trace lattice is from self-dual. Hilbert's formula proves that its exponent is exactly the accumulated displacement of nontrivial automorphisms.

Conductors complete the passage from fields to linear actions. They count only the directions a representation actually moves, separating the first inertial defect from its wild depth. The regular and permutation representations return us to discriminants, showing that no new invariant was invented: the same ramification is being observed at different resolutions.

We may now pass coherently among automorphism depth, tower-compatible breaks, trace duality, discriminant growth, and fixed-space defects. That coherence is the durable outcome of ramification theory and the local numerical foundation for the arithmetic constructions that follow.
