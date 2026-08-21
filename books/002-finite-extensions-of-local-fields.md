# Finite Extensions of Local Fields

## Contents

1. [One valuation upstairs](#1-one-valuation-upstairs)
   - [The local extension problem](#11-the-local-extension-problem)
   - [Existence, uniqueness, and the role of completeness](#12-existence-uniqueness-and-the-role-of-completeness)
   - [Completeness of the extension](#13-completeness-of-the-extension)
   - [Two useful absolute-value normalizations](#14-two-useful-absolute-value-normalizations)
2. [The integral extension and the degree formula](#2-the-integral-extension-and-the-degree-formula)
   - [Why the valuation ring must be the integral closure](#21-why-the-valuation-ring-must-be-the-integral-closure)
   - [Finite freeness](#22-finite-freeness)
   - [Ramification index and residue degree](#23-ramification-index-and-residue-degree)
   - [The fundamental equality](#24-the-fundamental-equality)
   - [Examples and warnings](#25-examples-and-warnings)
   - [Finite precision upstairs](#26-finite-precision-upstairs)
3. [Towers, completion, and change of base](#3-towers-completion-and-change-of-base)
   - [Why tower formulas matter](#31-why-tower-formulas-matter)
   - [Intersections and composita](#32-intersections-and-composita)
   - [Completion separates branches](#33-completion-separates-branches)
   - [Scalar extension of a local field](#34-scalar-extension-of-a-local-field)
   - [Mixed and equal characteristic](#35-mixed-and-equal-characteristic)
   - [A quadratic laboratory](#36-a-quadratic-laboratory)
   - [Continuity of embeddings](#37-continuity-of-embeddings)
4. [Trace and norm](#4-trace-and-norm)
   - [Linear algebra turned into arithmetic](#41-linear-algebra-turned-into-arithmetic)
   - [Characteristic polynomials and integral restriction](#42-characteristic-polynomials-and-integral-restriction)
   - [Transitivity](#43-transitivity)
   - [The valuation of a norm](#44-the-valuation-of-a-norm)
   - [Residue-field shadows](#45-residue-field-shadows)
   - [Trace pairings and separability](#46-trace-pairings-and-separability)
   - [Minimal polynomials and multiplicities](#47-minimal-polynomials-and-multiplicities)
   - [Norms of ideals and determinants](#48-norms-of-ideals-and-determinants)
5. [Automorphisms, decomposition, and inertia](#5-automorphisms-decomposition-and-inertia)
   - [From embeddings to local symmetries](#51-from-embeddings-to-local-symmetries)
   - [Why a decomposition group is needed](#52-why-a-decomposition-group-is-needed)
   - [The residue action and inertia](#53-the-residue-action-and-inertia)
   - [Fixed fields of inertia](#54-fixed-fields-of-inertia)
   - [What inertia does not yet measure](#55-what-inertia-does-not-yet-measure)
   - [Counting branches before completion](#56-counting-branches-before-completion)
   - [Three instructive Galois patterns](#57-three-instructive-galois-patterns)
6. [Residue Frobenius](#6-residue-frobenius)
   - [Why Frobenius is canonical](#61-why-frobenius-is-canonical)
   - [Frobenius in an unramified extension](#62-frobenius-in-an-unramified-extension)
   - [Compatibility in towers](#63-compatibility-in-towers)
   - [A polynomial picture](#64-a-polynomial-picture)
   - [Trace and norm under finite-field Frobenius](#65-trace-and-norm-under-finite-field-frobenius)
   - [Frobenius and restriction](#66-frobenius-and-restriction)
7. [Unramified extensions](#7-unramified-extensions)
   - [Isolating residue growth](#71-isolating-residue-growth)
   - [Equivalent characterizations](#72-equivalent-characterizations)
   - [Constructing the unramified lift](#73-constructing-the-unramified-lift)
   - [Finite residue fields](#74-finite-residue-fields)
   - [Examples in both characteristics](#75-examples-in-both-characteristics)
   - [Unramified factorization and base change](#76-unramified-factorization-and-base-change)
   - [Roots of unity of order prime to the residue characteristic](#77-roots-of-unity-of-order-prime-to-the-residue-characteristic)
   - [Unramified extensions and finite precision](#78-unramified-extensions-and-finite-precision)
8. [Total ramification and Eisenstein theory](#8-total-ramification-and-eisenstein-theory)
   - [Isolating value-group growth](#81-isolating-value-group-growth)
   - [Why Eisenstein coefficients have their shape](#82-why-eisenstein-coefficients-have-their-shape)
   - [Every total extension comes from a uniformizer](#83-every-total-extension-comes-from-a-uniformizer)
   - [Worked Eisenstein extensions](#84-worked-eisenstein-extensions)
   - [Monogenicity: what is true and what is not](#85-monogenicity-what-is-true-and-what-is-not)
   - [Recognition through a chosen element](#86-recognition-through-a-chosen-element)
   - [Changing the uniformizer](#87-changing-the-uniformizer)
   - [Prime-to-$p$ radical extensions](#88-prime-to-p-radical-extensions)
   - [A mixed extension in coordinates](#89-a-mixed-extension-in-coordinates)
9. [The maximal unramified subextension](#9-the-maximal-unramified-subextension)
   - [The structural question](#91-the-structural-question)
   - [Construction and maximality](#92-construction-and-maximality)
   - [The clean decomposition theorem](#93-the-clean-decomposition-theorem)
   - [What fails over imperfect residue fields](#94-what-fails-over-imperfect-residue-fields)
   - [A two-stage integral description](#95-a-two-stage-integral-description)
   - [The tame boundary](#96-the-tame-boundary)
10. [Units and successive approximation](#10-units-and-successive-approximation)
    - [Why units need their own filtration](#101-why-units-need-their-own-filtration)
    - [The first quotient](#102-the-first-quotient)
    - [Higher quotients are additive residue fields](#103-higher-quotients-are-additive-residue-fields)
    - [Multiplication, powers, and the residue characteristic](#104-multiplication-powers-and-the-residue-characteristic)
    - [Equal-characteristic example](#105-equal-characteristic-example)
    - [Mixed-characteristic example](#106-mixed-characteristic-example)
    - [Galois action on the layers](#107-galois-action-on-the-layers)
    - [Completeness and inverse limits of units](#108-completeness-and-inverse-limits-of-units)
    - [Unit coordinates and their limitations](#109-unit-coordinates-and-their-limitations)
    - [Roots of unity inside the unit filtration](#1010-roots-of-unity-inside-the-unit-filtration)
11. [Norms and traces along the unit filtration](#11-norms-and-traces-along-the-unit-filtration)
    - [Continuity and the first constraints](#111-continuity-and-the-first-constraints)
    - [Linearizing the norm](#112-linearizing-the-norm)
    - [The unramified case](#113-the-unramified-case)
    - [The totally ramified case](#114-the-totally-ramified-case)
    - [Norms in towers](#115-norms-in-towers)
    - [A worked comparison](#116-a-worked-comparison)
    - [Explicit norm equations in an unramified extension](#117-explicit-norm-equations-in-an-unramified-extension)
    - [Explicit norm equations in a tame total extension](#118-explicit-norm-equations-in-a-tame-total-extension)
    - [Trace versus norm on the first layer](#119-trace-versus-norm-on-the-first-layer)
12. [Krasner's lemma and stability of generators](#12-krasners-lemma-and-stability-of-generators)
    - [Why proximity can force field containment](#121-why-proximity-can-force-field-containment)
    - [The Krasner radius](#122-the-krasner-radius)
    - [Krasner's lemma](#123-krasners-lemma)
    - [Stability of simple roots](#124-stability-of-simple-roots)
    - [Nearby polynomials define the same extension](#125-nearby-polynomials-define-the-same-extension)
    - [What separability is doing](#126-what-separability-is-doing)
13. [How many extensions are there?](#13-how-many-extensions-are-there)
    - [The finiteness question and its exact scope](#131-the-finiteness-question-and-its-exact-scope)
    - [Compact families of Eisenstein polynomials](#132-compact-families-of-eisenstein-polynomials)
    - [Finiteness in characteristic zero](#133-finiteness-in-characteristic-zero)
    - [The tame positive-characteristic range](#134-the-tame-positive-characteristic-range)
    - [Wild equal characteristic: an infinite family](#135-wild-equal-characteristic-an-infinite-family)
    - [Why the residue field must be finite](#136-why-the-residue-field-must-be-finite)
14. [From local fields back to number fields](#14-from-local-fields-back-to-number-fields)
    - [A prime and its completed branches](#141-a-prime-and-its-completed-branches)
    - [Frobenius at an unramified prime](#142-frobenius-at-an-unramified-prime)
    - [Factorization and Frobenius cycle type](#143-factorization-and-frobenius-cycle-type)
    - [Weak approximation for coefficients](#144-weak-approximation-for-coefficients)
    - [Prescribing finitely many local completions](#145-prescribing-finitely-many-local-completions)
    - [What the approximation theorem does not prescribe](#146-what-the-approximation-theorem-does-not-prescribe)
15. [The local extension as a coherent whole](#15-the-local-extension-as-a-coherent-whole)
    - [The structural dictionary](#151-the-structural-dictionary)
    - [The separability map](#152-the-separability-map)
    - [The Galois picture](#153-the-galois-picture)
    - [The multiplicative picture](#154-the-multiplicative-picture)
    - [Conclusion](#155-conclusion)

## 1. One valuation upstairs

### 1.1 The local extension problem

Book 1 developed the language of a complete discretely valued field as a field together with four mutually reinforcing structures: a normalized valuation, a complete nonarchimedean topology, a discrete valuation ring, and a residue field. We now ask what happens to all four structures after a finite field extension.

The answer is much more rigid than it is over a noncomplete field. If $K$ is complete and discretely valued and $L/K$ is finite, there is only one valuation on $L$ extending the valuation of $K$. Its topology makes $L$ complete, its valuation ring is the integral closure of the valuation ring of $K$, and its value group is again discrete. Thus a finite extension does not take us out of the local category.

The word “extending” needs a normalization convention. Let

$$
v_K:K^\times\longrightarrow\mathbf Z
$$

be normalized. The normalized valuation $v_L:L^\times\to\mathbf Z$ will generally not restrict literally to $v_K$. Instead there is a positive integer $e$ such that

$$
v_L(x)=e\,v_K(x)\qquad(x\in K^\times).
$$

The two valuations extend the same place: they define compatible valuation rings and topologies. The factor $e$ measures how much finer the integral scale becomes upstairs. Confusing literal equality with equivalence is the source of many incorrect formulas, so we will always write normalized valuations and display this factor.

Throughout, unless a section says otherwise, $K$ is a field complete for a nontrivial normalized discrete valuation $v_K$. We write

$$
A=\mathcal O_K,\qquad \mathfrak m_K=(\pi_K),\qquad k=A/\mathfrak m_K.
$$

For a finite extension $L/K$, the corresponding objects will be

$$
B=\mathcal O_L,\qquad \mathfrak m_L=(\pi_L),\qquad l=B/\mathfrak m_L.
$$

No assumption on characteristic, separability, or finiteness of the residue field is implicit in this notation.
We use **complete discretely valued field** for this general setting. The shorter term
**nonarchimedean local field** will be reserved for the locally compact case, equivalently the
case in which the residue field is finite. This distinction becomes decisive in the finiteness
theorems of Chapter 13.

### 1.2 Existence, uniqueness, and the role of completeness

For an arbitrary valued field, a valuation extends to every algebraic extension, but it may extend in several inequivalent ways. Completeness changes uniqueness, not existence. The reason is algebraic: a complete valuation ring is henselian, and a henselian valuation has a unique extension to every algebraic field extension.

**Theorem 1.1 (unique extension).** Let $K$ be complete for a nontrivial discrete valuation, and let $L/K$ be algebraic. There is a unique equivalence class of valuations on $L$ extending the valuation of $K$. If $L/K$ is finite, that extension is discrete.

The proof has two conceptual steps. General valuation theory gives existence. For uniqueness, let $C$ be the integral closure of $A$ in a finite subextension $E/K$. Extensions of the valuation correspond to maximal ideals of $C$ above $\mathfrak m_K$. Henselianity forces $C$ to be local, so there is only one such ideal. Passing through the finite subextensions gives the algebraic case. In a finite extension the quotient of value groups is finite, so the extended value group is a cyclic discrete group and may be normalized as $\mathbf Z$.

Completeness is stronger than necessary here. Every henselian discretely valued field has the same uniqueness property. But completeness will soon do more: it will imply completeness of $L$ and allow a lattice argument proving that $B$ is finite over $A$. Those conclusions are not merely formal consequences of uniqueness.

The contrast with a nonhenselian field is concrete. Give $\mathbf Q$ its $5$-adic valuation and consider $L=\mathbf Q(i)$. Since $X^2+1$ has two distinct roots modulo $5$, it factors into two linear factors over $\mathbf Q_5$. The two factors determine two extensions of the $5$-adic valuation to $L$. After replacing $\mathbf Q$ by its completion $\mathbf Q_5$, the tensor product is not a field:

$$
\mathbf Q(i)\otimes_{\mathbf Q}\mathbf Q_5\cong \mathbf Q_5\times\mathbf Q_5.
$$

Each factor is one local branch. A finite extension of the already complete field is a field, and completeness (equivalently, henselianity) forces its valuation to have only one branch.

### 1.3 Completeness of the extension

Uniqueness tells us which topology to use on $L$, but not yet that every Cauchy sequence converges. The missing observation is finite-dimensional: all reasonable nonarchimedean norms on a finite-dimensional vector space over a complete field are equivalent.

Choose a $K$-basis $e_1,\dots,e_n$ of $L$. The coordinate norm

$$
\left\|\sum_i x_i e_i\right\|_0=\max_i|x_i|_K
$$

makes $L$ a complete normed $K$-vector space because it identifies it with $K^n$. The extended absolute value on $L$ is equivalent to this norm. Consequently it has the same Cauchy sequences and makes $L$ complete.

**Theorem 1.2.** Every finite extension of a complete discretely valued field is complete for its uniquely extended valuation.

One should not reverse the logic. Algebraic extensions of infinite degree need not be complete, even with the unique extended valuation. An algebraic closure of $\mathbf Q_p$, for example, is not complete. Finite dimensionality is what makes the coordinate comparison possible.

### 1.4 Two useful absolute-value normalizations

Valuations are simplest when each field is normalized separately. Absolute values admit two conventions, each useful for a different purpose.

Fix $0<c<1$ and put $|x|_K=c^{v_K(x)}$. The absolute value on $L$ that literally extends it is

$$
|y|_{L/K}=c^{v_L(y)/e}.
$$

Then $|x|_{L/K}=|x|_K$ for $x\in K$. Equivalently,

$$
|y|_{L/K}=|N_{L/K}(y)|_K^{1/[L:K]},
$$

a formula proved in Chapter 4.

If the residue fields are finite, say $|k|=q_K$ and $|l|=q_L$, and if $f=[l:k]$ is the residue degree, there is also an intrinsic absolute value on each field:

$$
|x|_K^{\mathrm{can}}=q_K^{-v_K(x)},\qquad
|y|_L^{\mathrm{can}}=q_L^{-v_L(y)}.
$$

Since $q_L=q_K^f$, restriction gives

$$
|x|_L^{\mathrm{can}}=
\left(|x|_K^{\mathrm{can}}\right)^{[L:K]}.
$$

Thus canonical Haar-measure normalization does not literally extend across fields. Both conventions are correct; a formula must reveal which one it uses.

## 2. The integral extension and the degree formula

### 2.1 Why the valuation ring must be the integral closure

Field degree alone does not record which elements are bounded. To do arithmetic in $L$ we need an integral lattice stable under multiplication, reduction, trace, and norm. The natural candidate is the integral closure of $A$ in $L$. Valuation theory identifies it without calculation.

**Theorem 2.1.** Let $L/K$ be finite. Then

$$
B=\{x\in L:v_L(x)\geq0\}
$$

is the integral closure of $A$ in $L$.

Indeed, an element integral over $A$ lies in every valuation ring extending $A$, hence in $B$. Conversely, the uniqueness of the extension means that the integral closure, which is the intersection of all extending valuation rings, is just $B$. The statement uses henselian uniqueness; without it, the integral closure is generally semilocal and is the intersection of several valuation rings.

This characterization immediately gives

$$
A=B\cap K,\qquad \mathfrak m_L\cap A=\mathfrak m_K,\qquad k\hookrightarrow l.
$$

It also separates integrality from separability. Nothing in the proof requires $L/K$ to be separable.

### 2.2 Finite freeness

Integral closure need not be finite in arbitrary valuation-theoretic situations. Here completeness and discreteness force finiteness. This is the decisive structural fact behind exact degree accounting.

**Theorem 2.2 (finite integral closure).** If $L/K$ is finite of degree $n$, then $B$ is a finite free $A$-module of rank $n$. It is a complete DVR, and its fraction field is $L$.

**Proof strategy.** Place the closed unit ball $B$ between two ordinary coordinate lattices. The upper lattice is a finite $A$-module, so Noetherianity makes $B$ finite. The determinant trick identifies its elements as integral, and torsion-freeness over a DVR turns finiteness into freeness.

**Proof.** Choose a $K$-basis of $L$ and let $M\cong A^n$ be its coordinate lattice. Equivalence of the coordinate norm and the extended field norm gives integers $r,s\geq0$ such that

$$
\pi_K^rM\subseteq B\subseteq \pi_K^{-s}M.
$$

The module $\pi_K^{-s}M$ is finite free over the Noetherian ring $A$, so its submodule $B$ is finite. It contains a full lattice, hence spans $L$ over $K$ and has rank $n$. It is torsion-free, and a finite torsion-free module over the PID $A$ is free.

For completeness, $B$ is the closed unit ball in the complete field $L$. It is a DVR because $v_L$ is normalized and discrete. Finally, multiplication by any $x\in B$ is an endomorphism of the finite $A$-module $B$; its characteristic polynomial is monic over $A$ and annihilates $x$. Thus $B$ is contained in the integral closure, agreeing with Theorem 2.1. $\square$

The theorem provides an **integral basis** $b_1,\dots,b_n$ with

$$
B=Ab_1\oplus\cdots\oplus Ab_n.
$$

Such a basis is not usually canonical. Its importance is that determinants of multiplication computed over $K$ may be computed on an integral matrix over $A$.

### 2.3 Ramification index and residue degree

There are two visible ways for a finite extension to acquire degree. The value scale may become finer, and the residue field may become larger. These phenomena are measured separately.

The **ramification index** and **residue degree** are

$$
e(L/K)=[v_L(L^\times):v_L(K^\times)],\qquad
f(L/K)=[l:k].
$$

Because $v_L(L^\times)=\mathbf Z$ and $v_L(K^\times)=e\mathbf Z$, this agrees with

$$
v_L|_{K^\times}=e\,v_K.
$$

If $\pi_K$ and $\pi_L$ are uniformizers, then

$$
\pi_K=u\pi_L^e
$$

for some $u\in B^\times$, and therefore

$$
\mathfrak m_KB=\mathfrak m_L^e.
$$

The residue degree is the vector-space dimension of $l$ over $k$. It may contain a separable part and an inseparable part. We will not silently replace $f$ by the number of residue embeddings: those numbers agree only when $l/k$ is separable.

### 2.4 The fundamental equality

The central accounting theorem says that no degree is hidden. For general valued fields a defect factor can occur, but completeness plus discreteness rules it out.

**Theorem 2.3 (fundamental equality).** Let $K$ be complete for a nontrivial discrete valuation and let $L/K$ be any finite field extension. Then

$$
[L:K]=e(L/K)f(L/K).
$$

Neither separability of $L/K$ nor perfection or finiteness of $k$ is required.

**Proof strategy.** Since $B$ is free of rank $[L:K]$, the quotient $B/\pi_KB$ has that length over $A$. On the other hand $\pi_KB=\mathfrak m_L^e$, whose $e$ successive layers are each one-dimensional over $l$, hence $f$-dimensional over $k$. Comparing the two length computations gives the formula.

**Proof.** Let $n=[L:K]$. From finite freeness,

$$
B/\pi_KB\cong (A/\pi_KA)^n
$$

as $A$-modules, so it has $A$-module length $n$. Since $\pi_KB=\mathfrak m_L^e$, filter the same quotient by

$$
B\supset\mathfrak m_L\supset\cdots\supset\mathfrak m_L^e.
$$

For $0\leq i<e$, multiplication by $\pi_L^i$ identifies

$$
\mathfrak m_L^i/\mathfrak m_L^{i+1}\cong l.
$$

The action of $A$ on each layer factors through $k$, and its $A$-module length is $\dim_k l=f$. Additivity of length gives

$$
n=\operatorname{length}_A(B/\pi_KB)=\sum_{i=0}^{e-1}f=ef.
$$

This proves the equality. $\square$

The proof explains the geometry of the formula. One base-field digit contains $e$ successive $L$-adic layers, and each layer carries $f$ residue-field coordinates. Thus $ef$ is not accidental multiplication; it counts how a block of base precision decomposes upstairs.

### 2.5 Examples and warnings

Let $K=\mathbf Q_p$ and let $L/K$ be generated by a root of a monic polynomial whose reduction is irreducible separable of degree $d$. Under the unramified hypotheses developed later, $e=1$, $f=d$, and $[L:K]=d$ is entirely residue degree.

Let $L=K(\Pi)$ with $\Pi^n=\pi_K$ when $X^n-\pi_K$ is irreducible. This polynomial is Eisenstein, $\Pi$ is a uniformizer, $e=n$, and $f=1$. The degree is entirely ramification.

In equal characteristic, take $K=k((t))$. If $k'/k$ is finite, then $k'((t))/k((t))$ has $e=1$ and $f=[k':k]$. If $L=k((t^{1/n}))$, then $e=n$ and $f=1$. When $\operatorname{char}k=p$ and $n=p$, the latter extension is purely inseparable. The fundamental equality still holds; separability was never part of its proof.

The hypotheses cannot be shortened to “a finite extension of discretely valued fields.” Noncomplete, nonhenselian fields may have several extensions of the valuation, and in more general henselian valued fields defect may occur. Our equality is secured by the finite-lattice theorem for complete discrete fields.

### 2.6 Finite precision upstairs

The proof of the fundamental equality works not only at the first base-field digit. For every $r\geq1$,

$$
\pi_K^rB=\mathfrak m_L^{re},
$$

and finite freeness gives

$$
B/\pi_K^rB\cong(A/\pi_K^rA)^{[L:K]}
$$

as $A$-modules. Its length is therefore $r[L:K]=ref$. Filtering by the $re$ powers of $\mathfrak m_L$ gives the same count one $l$-layer at a time.

When $k$ is finite of order $q$, this becomes a cardinality formula:

$$
|B/\mathfrak m_L^n|=q^{fn},\qquad
|B/\pi_K^rB|=q^{rf e}=q^{r[L:K]}.
$$

The first formula uses the intrinsic $L$-adic precision $n$; the second uses $r$ digits of $K$-precision. They agree when $n=re$. This distinction is useful in computations: reduction modulo $\pi_K^r$ upstairs retains $re$ digits in the uniformizer $\pi_L$.

There is a compatible diagram

$$
\begin{array}{ccc}
A/\pi_K^rA & \longrightarrow & B/\pi_K^rB\\
\downarrow && \downarrow\\
k & \longrightarrow & l,
\end{array}
$$

but the top horizontal map is rarely a field extension: both rings contain nilpotents when $r>1$, and the right-hand ring already contains nilpotents when $e>1$ and $r=1$. Indeed,

$$
B/\pi_KB=B/\mathfrak m_L^e.
$$

Only in the unramified case $e=1$ is this first quotient the residue field $l$. Ramification is visible algebraically as nilpotent thickness over the closed point.

This observation offers another equivalent view of $e$. It is the nilpotence index of the maximal ideal of $B/\pi_KB$. Meanwhile $f$ is the dimension of its residue field over $k$. The Artinian local $k$-algebra $B/\pi_KB$ therefore remembers both invariants, even before the fraction fields are examined.

## 3. Towers, completion, and change of base

### 3.1 Why tower formulas matter

Finite local extensions are rarely constructed in one step. One adjoins a residue-field generator, then a uniformizer; one passes to a normal closure; or one compares two fields inside a common algebraic closure. To make those constructions reliable, the numerical invariants must multiply exactly through intermediate fields.

Let $K\subseteq M\subseteq L$ be finite extensions, all carrying their normalized valuations. Restriction gives

$$
v_L|_{M^\times}=e(L/M)v_M,\qquad
v_M|_{K^\times}=e(M/K)v_K.
$$

Composing the two equalities immediately yields the first tower law. Residue-field degrees give the second.

**Proposition 3.1 (tower laws).** For a tower $L/M/K$ of finite extensions of complete discretely valued fields,

$$
e(L/K)=e(L/M)e(M/K),\qquad
f(L/K)=f(L/M)f(M/K).
$$

Consequently the fundamental equality is compatible with the ordinary degree formula:

$$
[L:K]=[L:M][M:K].
$$

At ring level the same statement reads

$$
\mathfrak m_K\mathcal O_L
=\mathfrak m_L^{e(L/K)}
=\left(\mathfrak m_M\mathcal O_L\right)^{e(M/K)}.
$$

These formulas require no separability. They are index and vector-space identities.

### 3.2 Intersections and composita

Suppose $L_1$ and $L_2$ are finite extensions of $K$ inside a fixed algebraic closure. Their intersection and compositum organize overlap. Degree alone satisfies

$$
[L_1L_2:K][L_1\cap L_2:K]=[L_1:K][L_2:K]
$$

when, for example, one of the two extensions is Galois; without such a hypothesis the corresponding degree statement is an inequality. Ramification invariants behave through the towers but do not obey an unconditional product formula across the square.

Two special cases are particularly clean. A finite unramified extension and a finite totally ramified extension of $K$ have trivial intersection. Indeed, an intermediate field of the first is unramified, while an intermediate field of the second is totally ramified; a field that is both has $e=f=1$ and is $K$. If the unramified extension is Galois, the two are linearly disjoint. This observation is the engine behind the canonical decomposition later in the book.

A warning is useful. A compositum of two totally ramified extensions need not have degree equal to the product of their degrees; they may overlap. Nor does arbitrary scalar extension preserve the ramification index. If $L=K(\sqrt{\pi_K})$ and one changes base to $L$ itself, the scalar product $L\otimes_KL$ is already split in the separable case, and its field factors have ramification index $1$ over $L$.

### 3.3 Completion separates branches

The local theory also explains what completion does to a finite extension of a noncomplete discretely valued field. Let $K_0$ carry a discrete valuation $v$, let $\widehat K_0$ be its completion, and let $E/K_0$ be finite separable, so that by Section 11.2 of Book 1 the integral model $\mathcal O_E$, the integral closure of $\mathcal O_{K_0}$ in $E$, is finite — hence finite free — over $\mathcal O_{K_0}$. This finiteness of the integral model is a genuine hypothesis: without it there is no lattice argument available, and neither the product statement below nor its degree refinement can be formulated.

There may be several extensions $w$ of $v$ to $E$. Completing $E$ at each one produces fields $E_w$. The completed tensor product decomposes at the level of integral models:

$$
\mathcal O_E\otimes_{\mathcal O_{K_0}}\widehat{\mathcal O}_{K_0}
\;\cong\;\prod_{w\mid v}\mathcal O_{E_w}.
$$

The isomorphism is compatible with the natural maps from $\mathcal O_E$: composing with the inclusion $\mathcal O_E\to\mathcal O_E\otimes\widehat{\mathcal O}_{K_0}$ and then projecting to the factor indexed by $w$ is exactly the embedding $\mathcal O_E\to\mathcal O_{E_w}$ attached to that branch. It is also compatible with reduction branchwise: reducing the $w$-factor modulo its maximal ideal reproduces, for each prime $\mathfrak P\mid\mathfrak m_{K_0}$ of the normalization, the residue identification $\mathcal O_E/\mathfrak P\cong$ the residue field of $E_w$ for the corresponding $w$, in the sense of the branch correspondence of Theorem 11.1 in Book 1. Inverting uniformizers turns this integral-model decomposition into the field-level canonical decomposition

$$
E\otimes_{K_0}\widehat K_0\cong\prod_{w\mid v}E_w,
$$

because both sides are obtained from their unit balls by localizing at the respective uniformizers, and tensor products commute with localization.

The factor indexed by $w$ has degree

$$
[E_w:\widehat K_0]=e(w/v)f(w/v),
$$

each completed factor being a finite extension of the complete discretely valued field $\widehat K_0$ by Section 12.6 of Book 1. Summing over the branches recovers

$$
[E:K_0]=\sum_{w\mid v}e(w/v)f(w/v)
$$

under exactly the finite-normalization hypotheses just named — $\mathcal O_E$ finite over $\mathcal O_{K_0}$, which separability of $E/K_0$ supplies — applied through Theorem 12.1 of Book 1. Completion does not merge branches; it turns them into explicit product factors.

If $K_0$ is already complete and $E$ is a field, the tensor product has only one factor. This is another manifestation of valuation uniqueness: uniqueness of the extension of $v$ leaves a single index $w$, so the integral-model product has one factor and the completed tensor product is the field $E_w=E\otimes_{K_0}\widehat K_0$ itself.

### 3.4 Scalar extension of a local field

Let $L/K$ and $K'/K$ be finite extensions inside an algebraic closure, and form

$$
L\otimes_KK'.
$$

If $L/K$ is separable, this is a finite reduced $K'$-algebra, hence a product of finite field extensions of $K'$. Each factor carries the unique local valuation. If $L/K$ is inseparable, nilpotents can occur after scalar extension, so it is wrong to speak automatically of field factors.

Unramified extensions have especially stable base change. If $L/K$ is finite unramified and $K'/K$ finite, every field factor of $L\otimes_KK'$ is unramified over $K'$. On residue fields this is the statement that a finite separable extension remains finite étale after scalar extension, though it may split into a product. Section 7.6 proves the assertion by lifting the resulting residue-field factors.

Total ramification behaves differently under arbitrary base change because the new base may absorb some or all of the value-group enlargement. It is preserved under unramified base change: if $L/K$ is totally ramified and $K'/K$ is unramified, then $L$ and $K'$ are linearly disjoint, $LK'/K'$ is totally ramified, and $LK'/L$ is unramified. Indeed, their intersection is both unramified and totally ramified, hence is $K$. More decisively, the residue field of $LK'/L$ contains the residue field of $K'$, so

$$
[LK':L]\geq f(K'/K)=[K':K].
$$

The reverse inequality is automatic, giving equality and linear disjointness. The tower formulas then give the two asserted ramification types. The square separates the two independent directions of local degree.

### 3.5 Mixed and equal characteristic

The tower formalism is deliberately characteristic-free, but examples look different in the two basic regimes.

In mixed characteristic $(0,p)$, the prime field supplies a distinguished ramified subextension. If $K/\mathbf Q_p$ is finite, then

$$
[K:\mathbf Q_p]=e(K/\mathbf Q_p)f(K/\mathbf Q_p),
$$

and $v_K(p)=e(K/\mathbf Q_p)$. The residue field is finite, hence perfect, so every finite residue extension is separable.

In equal characteristic $p$, the field $k((t))$ is the central model; a choice of coefficient field and uniformizer is what makes such a Laurent-series description literal. In the explicit model $K=k((t))$, regard $k$ as the constant coefficient field and choose the Laurent parameter $t$ with $v_K(t)=1$. Imperfect $k$ then introduces genuinely new behavior. For $a\in k$ not a $p$th power, adjoining a root of $X^p-a$ enlarges the residue field purely inseparably with $e=1$, while adjoining a root of $X^p-t$ is purely inseparable and totally ramified with $e=p$. Both are finite local extensions; neither is Galois in the usual separable sense.

This is why later equivalences involving embeddings, Frobenius, or inertia require explicit separability hypotheses, even though the valuation and degree theory does not.

### 3.6 A quadratic laboratory

Quadratic extensions over odd residue characteristic display the unramified and totally ramified directions with minimal notation. Let $K$ have finite residue field $k$ of odd cardinality, choose a unit $u\in A^\times$ whose residue $\bar u\in k^\times$ is nonsquare, and let $\pi=\pi_K$.

The polynomial $T^2-u$ has irreducible separable reduction, so

$$
K(\sqrt u)/K
$$

is the unramified quadratic extension. The polynomials

$$
T^2-\pi,\qquad T^2-u\pi
$$

are Eisenstein, so the corresponding extensions are totally ramified quadratic extensions.

These are all the quadratic extensions inside a fixed separable closure. Indeed, every principal unit $a\in1+\mathfrak m_K$ is a square: for $h(T)=T^2-a$, the approximation $T=1$ satisfies $h(1)\in\mathfrak m_K$ and $h'(1)=2\in A^\times$, so Hensel's lemma supplies a square root in $1+\mathfrak m_K$. Hence

$$
K^\times/(K^\times)^2
\cong
\bigl(\mathbf Z/2\mathbf Z\bigr)
\times k^\times/(k^\times)^2.
$$

The finite cyclic group $k^\times$ has two square classes, so $K^\times$ has four. The trivial class gives $K$ itself, and the other three give the extensions above.

This example also illustrates base change. After extending scalars to the unramified quadratic field $K(\sqrt u)$, the two ramified fields $K(\sqrt\pi)$ and $K(\sqrt{u\pi})$ become isomorphic because $u$ becomes a square. Conversely, adjoining $\sqrt\pi$ does not turn the unramified quadratic extension into a ramified one; the compositum has an unramified quadratic stage and a totally ramified quadratic stage.

Residue characteristic $2$ is different. The map $u\mapsto u^2$ is not invertible on principal units, and more unit square classes appear. The simple three-extension picture fails for exactly the filtration-theoretic reason that Chapter 10 will make explicit.

### 3.7 Continuity of embeddings

Every $K$-embedding $\sigma:L\hookrightarrow\Omega$ into an algebraic extension preserves the uniquely extended place. The formula depends on normalization. If $w$ is the extension scaled so that $w|_{K^\times}=v_K$, then

$$
w(\sigma x)=w(x).
$$

If $\Omega/K$ is finite and every field instead carries its own normalized integer-valued valuation, then

$$
v_\Omega(\sigma x)
=e(\Omega/\sigma(L))v_L(x),
$$

or, in a form independent of the intermediate normalization,

$$
\frac{v_\Omega(\sigma x)}{e(\Omega/K)}
=\frac{v_L(x)}{e(L/K)}.
$$

Indeed, pulling the valuation on $\Omega$ back along $\sigma$ gives another extension of the place of $K$ to $L$, so uniqueness identifies it with the given one; the displayed factor then comes from the tower law. Thus algebraic embeddings of finite extensions of $K$ are automatically continuous and isometric for an absolute value that literally extends the one on $K$.

This observation removes a common hidden hypothesis. In archimedean analysis, a field embedding need not be topologically harmless. In the present local setting, no separate continuity condition is required for finite algebraic embeddings over $K$. Consequently traces, norms, and Galois actions are continuous, and passage to limits commutes with every finite sum or product over embeddings.

## 4. Trace and norm

### 4.1 Linear algebra turned into arithmetic

The valuation describes one element at a time. Trace and norm compress the action of an element of $L$ on the whole $K$-vector space $L$ back into $K$. They are the additive and multiplicative transfer operations needed in towers, Galois theory, unit groups, and eventually reciprocity.

For $x\in L$, multiplication

$$
m_x:L\longrightarrow L,\qquad y\longmapsto xy
$$

is $K$-linear. Define

$$
\operatorname{Tr}_{L/K}(x)=\operatorname{tr}(m_x),\qquad
N_{L/K}(x)=\det(m_x).
$$

These definitions make sense for every finite extension, including inseparable ones. They immediately give

$$
\operatorname{Tr}(x+y)=\operatorname{Tr}(x)+\operatorname{Tr}(y),\qquad
N(xy)=N(x)N(y),\qquad N(x)=0\iff x=0.
$$

If $L/K$ is separable and $\Omega$ is a normal extension containing $L$, then linear algebra diagonalizes after scalar extension:

$$
\operatorname{Tr}_{L/K}(x)=\sum_{\sigma:L\hookrightarrow\Omega}\sigma(x),\qquad
N_{L/K}(x)=\prod_{\sigma:L\hookrightarrow\Omega}\sigma(x).
$$

The formulas over embeddings are consequences, not definitions. In a nontrivial purely inseparable extension there are too few embeddings. Indeed, the trace of every element in a finite purely inseparable extension of degree greater than one is zero, whereas the norm is generally nontrivial.

### 4.2 Characteristic polynomials and integral restriction

If $x\in B$, multiplication by $x$ preserves the finite free $A$-module $B$. In an integral basis its matrix has entries in $A$. Therefore its characteristic polynomial lies in $A[T]$, and in particular

$$
\operatorname{Tr}_{L/K}(B)\subseteq A,\qquad
N_{L/K}(B)\subseteq A.
$$

For units the norm is a unit. If $u\in B^\times$, then $u^{-1}\in B$ and

$$
N(u)N(u^{-1})=1,
$$

so

$$
N_{L/K}(B^\times)\subseteq A^\times.
$$

The trace of a unit need not be a unit and may vanish. For example, in a quadratic extension of characteristic not $2$, an element of trace zero can be a unit. Norm is adapted to multiplicative size; trace is vulnerable to cancellation.

### 4.3 Transitivity

Transfer operations must respect towers. Let $K\subseteq M\subseteq L$ be finite. Then

$$
\operatorname{Tr}_{L/K}
=\operatorname{Tr}_{M/K}\circ\operatorname{Tr}_{L/M},
$$

and

$$
N_{L/K}
=N_{M/K}\circ N_{L/M}.
$$

For trace, view a $K$-linear endomorphism of $L$ arising from multiplication and compute its trace first in blocks over $M$. For norm, the determinant of an $M$-linear map must itself be transferred from $M$ to $K$; this is exactly the second formula. In the separable case both are also immediate by grouping embeddings.

These identities explain why trace and norm, rather than arbitrary coefficient functions, persist through long towers.

### 4.4 The valuation of a norm

Norm does not merely preserve integrality; it measures valuation exactly.

**Theorem 4.1 (norm valuation formula).** For $x\in L^\times$,

$$
v_K\bigl(N_{L/K}(x)\bigr)=f(L/K)v_L(x).
$$

**Proof strategy.** Both sides are homomorphisms $L^\times\to\mathbf Z$. It is enough to separate a power of a uniformizer from a unit. Units have unit norm, while the determinant on the quotient by a principal ideal computes the remaining exponent.

Write $x=u\pi_L^r$. We already know $N(u)$ is a unit, so its valuation is zero. The principal $A$-module quotient $B/xB$ has length

$$
\operatorname{length}_A(B/xB)=rf,
$$

because it has $r$ successive $l$-layers. On the other hand, put a matrix for multiplication by $x$ into Smith normal form over the DVR $A$. If its nonzero diagonal entries are $d_1,\dots,d_{[L:K]}$, then its cokernel has length $\sum_i v_K(d_i)$, while its determinant has valuation $\sum_i v_K(d_i)$. Thus the valuation of the determinant equals the length of $B/xB$, and

$$
v_K(N(x))=rf=fv_L(x).
$$

The same conclusion for negative $r$ follows by inversion. $\square$

Since $[L:K]=ef$, the formula also gives

$$
\frac{v_L(x)}e=\frac{v_K(Nx)}{[L:K]}.
$$

This proves the norm expression for the extending absolute value from Section 1.4.

As a quick example, if $L/K$ is totally ramified and $\pi_L$ is a uniformizer, then $f=1$ and $N(\pi_L)$ is a uniformizer of $K$ up to a unit. If $L/K$ is unramified of degree $f$, then $v_K(Nx)=f v_L(x)$; a common uniformizer has norm a unit times its $f$th power.

### 4.5 Residue-field shadows

Reduction of trace and norm is slightly subtler than simply replacing $L/K$ by $l/k$, because $B/\pi_KB$ contains $e$ copies of the residue layer.

**Proposition 4.2.** For $x\in B$ and $u\in B^\times$,

$$
\overline{\operatorname{Tr}_{L/K}(x)}
=e\,\operatorname{Tr}_{l/k}(\bar x),
$$

and

$$
\overline{N_{L/K}(u)}
=N_{l/k}(\bar u)^e.
$$

Here the integer $e$ is viewed in $k$, so the trace reduction may vanish when the residue characteristic divides $e$.

To see the formulas, filter $B/\pi_KB=B/\mathfrak m_L^e$ by its powers of $\mathfrak m_L$. Multiplication by an integral element preserves the filtration and acts on every graded layer as multiplication by its residue on $l$. Trace and determinant of a filtered endomorphism are respectively the sum and product of those on the $e$ graded pieces.

For an unramified extension $e=1$, reduction commutes exactly with trace and norm. For a totally ramified extension $l=k$, the residue of the norm of a unit is $\bar u^e$. These two extremes anticipate the different behavior of norms on unit groups.

### 4.6 Trace pairings and separability

The bilinear form

$$
(x,y)\longmapsto\operatorname{Tr}_{L/K}(xy)
$$

is called the trace pairing. It is nondegenerate exactly when $L/K$ is separable. Thus separability has a linear-algebraic signature even before Galois theory enters.

If $L/K$ is inseparable, the trace pairing is degenerate; for a purely inseparable extension of degree greater than one it is identically zero. This is an illuminating counterexample to any attempt to use trace as a universal averaging operator. Norm remains multiplicative, but trace can lose all information.

The integral dual

$$
B^\vee=\{x\in L:\operatorname{Tr}_{L/K}(xB)\subseteq A\}
$$

is a fractional ideal when $L/K$ is separable. Its finer measurement leads to the codifferent and different. Those invariants, along with discriminant formulas, belong to the next book; here we use only the integral containment and the residue formulas above.

### 4.7 Minimal polynomials and multiplicities

Trace and norm become concrete once the minimal polynomial of an element is known, but one must account for the possibility that the element does not generate $L$.

Let $x\in L$, put $E=K(x)$, and write the monic minimal polynomial as

$$
g_x(T)=T^d+c_{d-1}T^{d-1}+\cdots+c_0.
$$

Multiplication by $x$ on $E$ has characteristic polynomial $g_x$. On $L$, viewed as a vector space of dimension $[L:E]$ over $E$, the same action occurs in $[L:E]$ identical blocks after choosing an $E$-basis. Therefore

$$
\operatorname{Tr}_{L/K}(x)
=[L:E]\operatorname{Tr}_{E/K}(x)
=-[L:E]c_{d-1},
$$

and

$$
N_{L/K}(x)
=N_{E/K}(x)^{[L:E]}
=\bigl((-1)^dc_0\bigr)^{[L:E]}.
$$

These formulas are characteristic-free. If the integer $[L:E]$ vanishes in $K$, the trace may disappear. For a purely inseparable extension $L/K$ of degree $p$ in characteristic $p$, every $x\in L$ has a minimal polynomial of the form

$$
T^{p^r}-a.
$$

Its next-to-leading coefficient is zero, and the multiplicity factor is a power of $p$; either way $\operatorname{Tr}_{L/K}(x)=0$. In the simplest case $L=K(\alpha)$ with $\alpha^p=a$,

$$
N_{L/K}(\alpha)=(-1)^{p+1}a.
$$

Thus norm still detects the defining parameter while trace detects no first-order separable motion.

For an integral $x$, the coefficients $c_i$ lie in $A$. If $x$ is a unit, $c_0$ is a unit; if $x$ is a uniformizer in a totally ramified extension and generates $L$, $c_0$ has valuation one and all other nonleading coefficients lie in $\mathfrak m_K$, recovering the Eisenstein shape developed in Chapter 8.

### 4.8 Norms of ideals and determinants

The norm valuation formula has an ideal-theoretic version that explains why the residue degree, rather than the ramification index, appears. Every nonzero fractional ideal of $B$ is $\mathfrak m_L^n$. Define its ideal norm by

$$
N_{L/K}(\mathfrak m_L^n)=\mathfrak m_K^{fn}.
$$

For a principal ideal $(x)$, Theorem 4.1 gives

$$
N_{L/K}(xB)=N_{L/K}(x)A.
$$

The definition is multiplicative because exponents add. In particular,

$$
N_{L/K}(\mathfrak m_KB)
=N_{L/K}(\mathfrak m_L^e)
=\mathfrak m_K^{ef}
=\mathfrak m_K^{[L:K]}.
$$

This is exactly what one expects from extending the principal ideal $(\pi_K)$ to a free module of rank $[L:K]$: multiplication by $\pi_K$ has determinant $\pi_K^{[L:K]}$.

The appearance of $f$ can also be read from one quotient:

$$
|B/\mathfrak m_L|=|l|.
$$

When residue fields are finite, the ideal $\mathfrak m_L$ has additive index $|l|=|k|^f$ in $B$, so its norm down to $A$ must have index $|k|^f$, namely $\mathfrak m_K^f$. Ramification changes how many powers of $\mathfrak m_L$ lie over $\mathfrak m_K$; residue degree changes the norm of each individual power.

## 5. Automorphisms, decomposition, and inertia

### 5.1 From embeddings to local symmetries

Valuation theory becomes group theory when an extension is normal and separable. An arbitrary finite extension has at most $[L:K]$ embeddings into a fixed algebraic closure, with equality exactly in the separable case. A finite **Galois** extension is both normal and separable; then

$$
G=\operatorname{Gal}(L/K)
$$

has order $[L:K]$ and its fixed field is $K$.

These adjectives solve different problems. Separability ensures enough embeddings. Normality ensures that every embedding lands back in $L$. Galois means both. A purely inseparable extension is never nontrivially Galois, even if it has a single valuation and satisfies the degree formula. Conversely, an unramified extension is automatically separable under our definition, but a finite extension with $e=1$ need not be unramified if its residue extension is inseparable.

Because the extended valuation on $L$ is unique, every $K$-automorphism $\sigma$ preserves it:

$$
v_L(\sigma x)=v_L(x).
$$

It follows that $\sigma$ preserves $B$, $\mathfrak m_L$, every power $\mathfrak m_L^n$, and the residue map. Thus local Galois theory naturally acts at every precision.

### 5.2 Why a decomposition group is needed

Over a complete base there is only one prime upstairs, so every automorphism preserves it. The term **decomposition group** looks redundant locally. It is retained because it identifies the local group that appears when a global extension is completed at one chosen prime.

Let $E/F$ be finite Galois, let $v$ be a nontrivial discrete valuation on $F$, and choose an extension $w$ to $E$. The Galois group acts on extended valuations by

$$
(\sigma w)(x)=w(\sigma^{-1}x).
$$

The **decomposition group** is the stabilizer

$$
D_w=\{\sigma\in\operatorname{Gal}(E/F):\sigma w=w\}.
$$

Equivalently, it is the stabilizer of the corresponding maximal ideal in the integral closure. The group acts transitively on the valuations above $v$, so the number of branches is the index of $D_w$.

Completion turns the stabilizer into an actual local Galois group:

$$
D_w\cong\operatorname{Gal}(E_w/F_v).
$$

Here is the degree argument behind this identification. Every element of $D_w$ is continuous for $w$ and therefore extends uniquely to $E_w$, giving an injection into $\operatorname{Aut}_{F_v}(E_w)$. The completed product decomposition from Book 1 has one factor for every valuation above $v$. The global Galois group permutes these factors transitively, with stabilizer $D_w$. If there are $g$ factors, conjugacy makes their degrees equal, so the product decomposition and orbit–stabilizer give

$$
[E:F]=g[E_w:F_v],\qquad
|\operatorname{Gal}(E/F)|=g|D_w|.
$$

The two left sides are equal. Therefore

$$
[E_w:F_v]=|D_w|.
$$

The injection supplies $[E_w:F_v]$ distinct automorphisms, so $E_w/F_v$ is Galois and the injection is the displayed isomorphism. In particular, completion neither loses nor creates automorphisms that preserve the chosen branch.

For a finite Galois extension $L/K$ of complete discretely valued fields, there is one valuation above $v_K$, hence

$$
D=G.
$$

The global terminology therefore fits the local situation without modification.

### 5.3 The residue action and inertia

Return to the standing local setting: let $L/K$ be a finite Galois extension of complete
discretely valued fields. The extended valuation is unique, so the decomposition group is the
whole group $G=\operatorname{Gal}(L/K)$. It acts on $B$ and preserves $\mathfrak m_L$, hence it
acts on $l$. This gives a homomorphism

$$
\rho:G\longrightarrow\operatorname{Aut}_k(l).
$$

Its kernel is the **inertia group**

$$
I(L/K)=\{\sigma\in G:\overline{\sigma(x)}=\bar x\text{ for every }x\in B\}.
$$

The definition answers a precise question: which field automorphisms are invisible after reduction? Inertia consists of symmetries that move elements only by positive valuation. Equivalently,

$$
\sigma\in I
\quad\Longleftrightarrow\quad
v_L(\sigma(x)-x)>0\text{ for all }x\in B.
$$

If the residue extension $l/k$ is separable, then normality of $L/K$ implies that $l/k$ is
normal, as the proof below shows. Thus $l/k$ is Galois, and every $k$-automorphism of $l$ lifts
to $L$. Therefore

$$
1\longrightarrow I(L/K)\longrightarrow G
\xrightarrow{\rho}\operatorname{Gal}(l/k)\longrightarrow1.
$$

In particular,

$$
|G/I|=f,\qquad |I|=e.
$$

**Proof of surjectivity.** Choose a primitive element $\bar\theta$ for the finite separable extension $l/k$, let $\bar g$ be its minimal polynomial, and choose a monic lift $g\in A[T]$. Hensel's lemma gives a root $\theta\in B$ reducing to $\bar\theta$. Since $\bar g$ is irreducible, its monic lift $g$ is irreducible over $K$: a nontrivial factorization over $K$ could be taken monic over the integrally closed valuation ring $A$ and would reduce to a nontrivial factorization of $\bar g$. Moreover, separability of $\bar g$ implies that $g$ is separable. Because $L/K$ is normal and $g$ is the minimal polynomial of $\theta$, all roots of $g$ lie in $L$. They are integral, and their residues are distinct by uniqueness of a Hensel lift of a simple root. Thus $\bar g$ splits in $l$, proving first that $l/k$ is normal and hence Galois.

For $\tau\in\operatorname{Gal}(l/k)$, the element $\tau(\bar\theta)$ is another simple root of $\bar g$, so it has a unique lift $\theta_\tau\in B$ satisfying $g(\theta_\tau)=0$. The assignment $\theta\mapsto\theta_\tau$ defines a $K$-embedding $K(\theta)\hookrightarrow L$. It extends to a $K$-embedding of $L$ into a normal closure, and normality of $L/K$ makes the image equal to $L$. The resulting element of $G$ induces $\tau$ on the residue generator and hence on all of $l$. This proves surjectivity. Exactness at $G$ is the definition of inertia, and $|G|=[L:K]=ef$ gives $|G/I|=f$ and $|I|=e$. $\square$

The separability hypothesis on $l/k$ is essential to the displayed target. If $l/k$ is inseparable, its automorphism group can have order strictly smaller than $f$. The map to $\operatorname{Aut}_k(l)$ still exists and inertia is still its kernel, but the quotient cannot account for the full residue degree. Perfect residue fields, and in particular finite residue fields, eliminate this complication.

### 5.4 Fixed fields of inertia

Assume now that $L/K$ is finite Galois and $l/k$ is separable. Let

$$
L_0=L^I.
$$

The Galois correspondence and the exact sequence give

$$
[L_0:K]=|G/I|=f(L/K),\qquad [L:L_0]=|I|=e(L/K).
$$

To identify the ramification type, reuse the lifted residue generator from the surjectivity proof. The element $\theta$ generates an unramified subextension $E=K(\theta)$ of degree $f(L/K)$. Every $\sigma\in I$ fixes $\theta$: both $\sigma(\theta)$ and $\theta$ are roots of $g$ with the same residue, so Henselian uniqueness makes them equal. Hence $E\subseteq L^I=L_0$. Since both fields have degree $f(L/K)$ over $K$, they are equal. It follows that

$$
e(L_0/K)=1,\quad f(L_0/K)=f(L/K),
$$

and, by the tower formulas,

$$
e(L/L_0)=e(L/K),\quad f(L/L_0)=1.
$$

Thus $L_0/K$ is unramified and $L/L_0$ is totally ramified. The group quotient $G/I$ is the residue-field Galois group, while $I$ is the Galois group of the totally ramified layer.

This is the first appearance of the local extension as two orthogonal directions:

$$
\begin{array}{c}
L\\
|\quad\text{totally ramified, group }I\\
L_0\\
|\quad\text{unramified, group }G/I\\
K.
\end{array}
$$

The construction is canonical in the Galois case because inertia is canonical.

### 5.5 What inertia does not yet measure

Inertia separates what survives in the residue field from what disappears there, but it does not measure how violently an automorphism approaches the identity at higher powers of $\mathfrak m_L$. One can refine $I$ by asking for congruence modulo $\mathfrak m_L^n$. That leads to ramification groups, tame and wild inertia, and lower and upper numbering. We will use only the elementary prime-to-residue-characteristic boundary later in this book. The systematic filtrations, their change under quotients, and their relation to the different and conductors are reserved for Book 3.

### 5.6 Counting branches before completion

The local exact sequence sits inside a broader counting formula. Let $E/F$ be finite Galois, choose a discrete valuation $v$ on $F$, and suppose the relevant integral closure is finite. The Galois group acts transitively on the $g$ valuations above $v$. If $w$ is one of them, orbit–stabilizer gives

$$
|\operatorname{Gal}(E/F)|=g\,|D_w|.
$$

The completion $E_w/F_v$ has Galois group $D_w$ and degree $e_wf_w$, so

$$
[E:F]=g e_wf_w.
$$

All branches have the same $e$ and $f$ because they are conjugate. Thus the three factors have distinct meanings:

$$
g=\text{number of primes},\qquad
f=\text{residue degree},\qquad
e=\text{ramification index}.
$$

Passing to the complete local field chooses one branch and removes $g$ from the picture. It does not force $g=1$ in the original global extension; it replaces the global algebra by the selected completed factor.

Within $D_w$, reduction gives

$$
1\longrightarrow I_w\longrightarrow D_w
\longrightarrow\operatorname{Gal}(l_w/k_v)\longrightarrow1
$$

when the residue extension is separable. Hence $D_w$ accounts for $ef$, inertia for $e$, and the residue quotient for $f$. This is the same degree accounting seen successively as orbit size, local field degree, and group order.

### 5.7 Three instructive Galois patterns

In an unramified Galois extension, $I=1$. Every automorphism is already visible on the residue field, and

$$
G\cong\operatorname{Gal}(l/k).
$$

In a totally ramified Galois extension, $I=G$. Every automorphism becomes invisible after reduction. This does not mean that automorphisms act trivially on integral elements; it means only that their displacement has positive valuation.

A third pattern combines the first two. Suppose $k$ is perfect and $L/K$ is finite Galois with both $e,f>1$. Then

$$
1\to I\to G\to\operatorname{Gal}(l/k)\to1
$$

need not split. Even when it does split, no splitting is generally canonical. A Frobenius element in the quotient can have many lifts to $G$, all differing by inertia. The canonical object is the exact sequence and its quotient element, not a chosen semidirect-product presentation.

Normality also matters. If $L/K$ is finite separable but not normal, its normal closure $\widetilde L/K$ is Galois. The valuation extends uniquely to $\widetilde L$, and the subgroup

$$
H=\operatorname{Gal}(\widetilde L/L)
$$

recovers $L$. Ramification and residue degrees for $L/K$ may be read through the towers $\widetilde L/L/K$, but $L/K$ itself has no Galois group large enough to support an inertia exact sequence of order $ef$. Passing to a normal closure is a tool, not a license to call the original extension Galois.

## 6. Residue Frobenius

### 6.1 Why Frobenius is canonical

For a general residue field, an unramified Galois group is simply the Galois group of a finite separable residue extension. When the residue field is finite, that group has a distinguished generator. This turns abstract unramified symmetry into a canonical element and eventually lets one label primes by conjugacy classes.

Let $k=\mathbf F_q$. The map

$$
\operatorname{Frob}_q:x\longmapsto x^q
$$

fixes $k$. On $l=\mathbf F_{q^f}$ it has order $f$, because its fixed field is exactly $\mathbf F_q$. Hence

$$
\operatorname{Gal}(\mathbf F_{q^f}/\mathbf F_q)
=\langle\operatorname{Frob}_q\rangle
$$

is cyclic.

This generator is called **arithmetic Frobenius**. Its inverse

$$
x\longmapsto x^{q^{f-1}}
$$

is called **geometric Frobenius**. Both conventions are widespread. A statement saying only “Frobenius” is incomplete unless the direction is clear.

### 6.2 Frobenius in an unramified extension

Let $L/K$ be finite unramified and suppose $k=\mathbf F_q$. Reduction identifies

$$
\operatorname{Gal}(L/K)\xrightarrow{\sim}\operatorname{Gal}(l/k).
$$

The **arithmetic Frobenius element** $\mathrm{Frob}_{L/K}$ is the unique automorphism satisfying

$$
\overline{\mathrm{Frob}_{L/K}(x)}=\bar x^q
\qquad(x\in B).
$$

It generates $\operatorname{Gal}(L/K)$. Geometric Frobenius is its inverse.

For a ramified finite Galois extension with finite residue field, Frobenius first lives in the quotient:

$$
G/I\cong\operatorname{Gal}(l/k).
$$

There is a distinguished arithmetic Frobenius **coset**, but generally no distinguished lift in $G$. Any two lifts differ by inertia. This distinction matters: the residue action canonically determines a coset, not an automorphism of the ramified field.

### 6.3 Compatibility in towers

Suppose $k=\mathbf F_q$, and let $L/M/K$ be a tower of unramified extensions with residue degree $f(M/K)=d$. Arithmetic Frobenius for $K$ acts on every residue extension by $x\mapsto x^q$. Arithmetic Frobenius relative to $M$ acts by

$$
x\longmapsto x^{q^d}.
$$

Thus

$$
\mathrm{Frob}_{L/M}=\mathrm{Frob}_{L/K}^{\,d}
$$

on the appropriate field. The formula is an excellent check on normalization. For geometric Frobenius the same power relation holds after inversion.

### 6.4 A polynomial picture

Let $K=\mathbf Q_p$, and choose an irreducible polynomial $\bar g\in\mathbf F_p[T]$ of degree $f$. Lift it monically to $g\in\mathbf Z_p[T]$, and let $L$ be generated by a root $\theta$ whose residue is a root of $\bar g$. Then $L/K$ is unramified of degree $f$. Arithmetic Frobenius sends the residue $\bar\theta$ to $\bar\theta^p$; Henselian uniqueness determines the corresponding automorphism of $L$.

It is usually false that the lift sends $\theta$ literally to $\theta^p$. The congruence

$$
\mathrm{Frob}(\theta)\equiv\theta^p\pmod{\mathfrak m_L}
$$

is canonical, while equality depends on choosing special representatives. This is another instance of residue information determining a unique lift only through the defining equation, not through a naive formula.

### 6.5 Trace and norm under finite-field Frobenius

Let $l=\mathbf F_{q^f}$ over $k=\mathbf F_q$. The conjugates of $a\in l$ are

$$
a,a^q,a^{q^2},\dots,a^{q^{f-1}}.
$$

Therefore

$$
\operatorname{Tr}_{l/k}(a)
=a+a^q+\cdots+a^{q^{f-1}},
$$

and, for $a\ne0$,

$$
N_{l/k}(a)
=a^{1+q+\cdots+q^{f-1}}
=a^{(q^f-1)/(q-1)}.
$$

The trace is surjective because it is a nonzero $k$-linear map to a one-dimensional space. The norm is surjective because $l^\times$ is cyclic and the displayed exponent maps a generator to an element of order $q-1$.

For an unramified extension $L/K$ with these residue fields, the same conjugate pattern holds upstairs modulo $\mathfrak m_L$. For $\bar a\ne0$, let $[\bar a]$ denote its **Teichmüller lift**: the unique root of $T^{q^f-1}-1$ in $B$ reducing to $\bar a$. This root exists and is unique by Hensel's lemma, since $q^f-1$ is invertible in $B$. Frobenius acts literally by

$$
\mathrm{Frob}([\bar a])=[\bar a]^q=[\bar a^q].
$$

Thus

$$
\operatorname{Tr}_{L/K}([\bar a])
=\sum_{i=0}^{f-1}[\bar a]^{q^i},
\qquad
N_{L/K}([\bar a])
=[\bar a]^{(q^f-1)/(q-1)}.
$$

Teichmüller representatives are special precisely because the residue Frobenius formula lifts without correction on them.

### 6.6 Frobenius and restriction

Let $K_f/K$ be the unramified extension of degree $f$ and let $d\mid f$. The unique intermediate field $K_d$ has residue field $\mathbf F_{q^d}$. Restriction sends arithmetic Frobenius on $K_f/K$ to arithmetic Frobenius on $K_d/K$:

$$
\mathrm{Frob}_{K_f/K}|_{K_d}
=\mathrm{Frob}_{K_d/K}.
$$

On the other hand, the relative arithmetic Frobenius of $K_f/K_d$ is the $d$th power:

$$
\mathrm{Frob}_{K_f/K_d}
=\mathrm{Frob}_{K_f/K}^{\,d}.
$$

The first formula concerns restriction to a smaller field over the same base; the second changes the base field. Keeping those operations distinct prevents an easy exponent error.

For a compatible tower of finite Galois extensions that may be ramified, the same statements hold in the relevant quotients by inertia. When restriction between the Galois groups is defined, it carries the arithmetic Frobenius coset for a fixed base to the corresponding Frobenius coset downstairs; changing the base field replaces Frobenius by the appropriate residue-degree power, exactly as above. A chosen lift in a ramified Galois group need not be compatible because it can change by inertia at each level.

## 7. Unramified extensions

### 7.1 Isolating residue growth

An extension with $e=1$ does not refine the value scale. Yet that condition alone does not ensure that the residue growth behaves like an étale field extension: over an imperfect residue field it can be inseparable. The definition of unramified must exclude that pathology.

A finite extension $L/K$ is **unramified** if

$$
e(L/K)=1
$$

and $l/k$ is separable. By the fundamental equality, $[L:K]=[l:k]$. In fact such an $L/K$ is automatically separable. A finite extension with $e=1$ but inseparable residue extension is not unramified; we will describe it explicitly rather than introduce additional terminology.

If $k$ is perfect, every finite residue extension is separable, so unramified is equivalent simply to $e=1$. Finite fields are perfect. No characteristic-zero assumption is involved.

### 7.2 Equivalent characterizations

The point of the definition is that it can be recognized in the field, in the valuation ring, or in the residue field.

**Theorem 7.1 (unramified criteria).** Let $L/K$ be finite. The following are equivalent.

1. $L/K$ is unramified.
2. $e(L/K)=1$ and $l/k$ is separable.
3. $\mathfrak m_L=\mathfrak m_KB$ and $l/k$ is separable.
4. There is an element $\theta\in B$ whose minimal polynomial $g\in A[T]$ reduces to the separable minimal polynomial of $\bar\theta$ over $k$, such that $l=k(\bar\theta)$ and
   $$
   B=A[\theta].
   $$
5. $B$ is finite étale over $A$.

The fifth condition is ring-theoretic shorthand for finite, flat, and unramified in the algebraic sense. In the present one-field situation it can be checked from a monogenic presentation $B\cong A[T]/(g)$ by asking that $g'(T)$ be invertible in the quotient. The equivalence supplies the intuition: no new value step appears, and the residue extension has no infinitesimal multiplicity.

**Proof.** Conditions 1 and 2 agree by definition. Since $\mathfrak m_KB=\mathfrak m_L^e$, conditions 2 and 3 agree as well.

Assume condition 2. Choose a primitive element $\bar\theta$ of the finite separable extension $l/k$, let $\bar g$ be its minimal polynomial, and lift $\bar g$ monically to $g\in A[T]$. Starting from any lift of $\bar\theta$ in $B$, Hensel's lemma produces a root $\theta\in B$ of $g$ reducing to $\bar\theta$. The polynomial $g$ is irreducible because its reduction is irreducible, so

$$
[K(\theta):K]=\deg g=[l:k]=[L:K].
$$

Thus $L=K(\theta)$. Put $C=A[\theta]$. Because $e=1$, the element $\pi_K$ is a uniformizer of $B$, and reduction gives an isomorphism

$$
C/\pi_KC\cong k[T]/(\bar g)\cong l\cong B/\pi_KB.
$$

Hence $B=C+\pi_KB$. Applying Nakayama's lemma to the finite $A$-module $B/C$ gives $B=C$, proving condition 4.

Conversely, condition 4 gives

$$
B/\pi_KB\cong k[T]/(\bar g)=l,
$$

a field separable over $k$. The quotient has no nonzero nilpotent maximal ideal, whereas $B/\pi_KB=B/\mathfrak m_L^e$ would have such an ideal if $e>1$. Therefore $e=1$, and condition 2 follows.

Under condition 4, separability of $\bar g$ says that $g'(\theta)$ is a unit, so the derivative criterion makes $B$ finite étale over $A$. Conversely, if $B/A$ is finite étale, its special fiber $B/\pi_KB$ is a finite étale $k$-algebra and is therefore reduced. Since this special fiber is local and equals $B/\mathfrak m_L^e$, reducedness forces $e=1$; it is then the residue field $l$, finite separable over $k$. Thus condition 5 implies condition 2 and completes the circle of equivalences. $\square$

In condition 4, it is not enough merely to choose any lift of a residue generator, even one that generates the full integral ring. In a ramified monogenic extension, a generator can reduce to a separable element while its own minimal polynomial acquires repeated factors modulo $\mathfrak m_K$. The decisive requirement is that $g$ itself reduce to the separable minimal polynomial of $\bar\theta$, equivalently that $g'(\theta)$ be a unit and $\deg g=[l:k]$.

### 7.3 Constructing the unramified lift

Let $k'/k$ be a finite separable extension. Choose a primitive element $\bar\theta$ with monic minimal polynomial $\bar g\in k[T]$. Lift $\bar g$ to a monic polynomial $g\in A[T]$. Because $\bar g$ is irreducible, $g$ is irreducible over $K$. Let

$$
L=K[T]/(g),\qquad \theta=T\bmod g.
$$

Then $\theta$ is integral, and its residue generates a copy of $k'$. We have $[L:K]=\deg g=[k':k]$, while the fundamental inequality already visible from the residue field gives $f(L/K)\geq[k':k]$. The fundamental equality forces

$$
e(L/K)=1,\qquad l\cong k'.
$$

Moreover $B=A[\theta]$. Both are free $A$-modules of the same rank, and reduction shows that $1,\theta,\dots,\theta^{f-1}$ span $B/\mathfrak m_L$; Nakayama's lemma completes the argument.

Different monic lifts of $\bar g$ produce isomorphic extensions. Indeed, let $L_2$ be produced from a second lift. Inside $\mathcal O_{L_2}$, the first lifted polynomial has a unique root reducing to the chosen $\bar\theta$, because that residue root is simple. Sending the first construction's root to this root gives a $K$-embedding into $L_2$; both fields have degree $[k':k]$, so it is an isomorphism. Thus the construction depends only on $k'/k$, not on the chosen polynomial.

**Fixing the based data.** The classification statement needs one further piece of interface discipline before it can be applied. An intermediate field $E$ of a separable closure does not, by itself, carry a valuation: a field admits many discrete valuations, so an abstract witness "$E$ inside $K^s$" cannot be fed to a reduction functor until a branch has been named. All statements below are therefore made relative to fixed _based data_ chosen once and for all:

1. a rank-one discrete valuation $v_K$ of $K$ that is henselian — for instance complete;
2. a separable closure $K^s$ of $K$ carrying the resulting unique extension of $v_K$, which exists and is unique up to equivalence by the henselian uniqueness criterion (Theorem 12.2 in Book 1);
3. a fixed isomorphism identifying the residue field $\kappa$ of that extension with a chosen residue field $k$.

We say that a finite unramified extension inside $K^s$, its residue-field presentation, and every construction derived from them are _based at $(K,v_K,k)$_. The classification is a classification of based objects: fixing the based data is what makes reduction well defined on the nose, rather than only up to an uncontrolled choice of valuation on each witness.

**Theorem 7.2 (classification).** Fix based data $(K,v_K,k)$ as above, with $K^s$ the chosen based separable closure and $k^s$ a fixed separable closure of $k$. Reduction gives an equivalence between finite unramified extensions of $(K,v_K)$ inside $K^s$ and finite separable extensions of $k$ inside $k^s$. It preserves degrees, inclusions, composita, intersections, and Galois groups.

**Proof.** The construction above produces an unramified lift of every finite separable residue extension, and the comparison of two monic lifts proves uniqueness up to the unique isomorphism inducing the prescribed residue identification. More generally, a $K$-embedding between two unramified extensions reduces to a $k$-embedding of their residue fields. Conversely, choose a primitive residue element in the source. A given residue embedding sends it to a simple root of the same residue polynomial in the target, and Hensel's lemma lifts that root uniquely; this defines the unique $K$-embedding inducing the prescribed residue map. Reduction is therefore essentially surjective and fully faithful. Degrees and Galois groups are preserved, and the assertions about inclusions, composita, and intersections follow by applying this correspondence to the associated residue subfields. $\square$

This theorem is the precise sense in which unramified extensions are residue-field extensions lifted without distortion. Note what the based data do and do not contribute: the equivalence exists only after $v_K$, the branch over $K^s$, and the residue identification have been fixed, since without them neither side has a well-defined reduction map; but once fixed, the preservation clauses — degrees, inclusions, composita, intersections, Galois groups — are independent of the particular choice, because any two identifications of $\kappa$ with $k$ differ by an automorphism of $k$ that transports one classification to the other.

### 7.4 Finite residue fields

Fix based data $(K,v_K,k)$ as in Section 7.3, with $k=\mathbf F_q$ finite. Then there is, within the based separable closure and up to the unique $K$-isomorphism inducing the identity on residue fields, exactly one unramified extension $K_f/K$ of each degree $f\geq1$. Its residue field is $\mathbf F_{q^f}$, and

$$
\operatorname{Gal}(K_f/K)\cong\mathbf Z/f\mathbf Z
$$

is generated by arithmetic Frobenius.

The compositum and intersection laws become numerical, with the composita and intersections formed inside the based separable closure so that the classification applies verbatim:

$$
K_mK_n=K_{\operatorname{lcm}(m,n)},\qquad
K_m\cap K_n=K_{\gcd(m,n)}.
$$

Inside the based separable closure, the union

$$
K^{\mathrm{nr}}=\bigcup_{f\geq1}K_f
$$

— taken over the nested tower of based levels, each carrying the restriction of the unique extended valuation — is the maximal unramified extension. Its Galois group is the profinite completion of the integers,

$$
\operatorname{Gal}(K^{\mathrm{nr}}/K)\cong\widehat{\mathbf Z},
$$

with arithmetic Frobenius corresponding to $1$; the isomorphism is read through the residue identification fixed by the based data, which is what makes "the" Frobenius a specific element rather than a conjugacy-class witness. The completion of $K^{\mathrm{nr}}$ is larger and no longer algebraic over $K$; algebraic maximality and metric completeness should not be conflated. This last statement, too, belongs to the based interface: the completed maximal unramified extension and its nonalgebraicity are properties of the completion of _this_ tower with its branch valuation, not assertions about an arbitrary field presented as a completion without its based data.

### 7.5 Examples in both characteristics

For $K=\mathbf Q_p$, every finite unramified extension is obtained by lifting an irreducible polynomial over $\mathbf F_p$. Its uniformizer may be chosen to be $p$, because $e=1$, and its ring of integers is generated by a lift of a residue generator.

For $K=k((t))$ and a finite separable extension $k'/k$, the unramified lift is simply

$$
k'((t))/k((t)),
$$

with valuation rings $k'[[t]]/k[[t]]$. The parameter $t$ is a uniformizer on both sides.

If $k$ is imperfect of characteristic $p$ and $a\in k\setminus k^p$, then

$$
k(a^{1/p})((t))/k((t))
$$

has $e=1$ and residue degree $p$, but the residue extension is purely inseparable. It is not unramified. This example shows exactly why separability appears in the definition.

### 7.6 Unramified factorization and base change

The classification theorem converts questions about unramified composita into elementary residue-field algebra. Let $K_1/K$ and $K_2/K$ be finite unramified, based as in Section 7.3, with residue fields $k_1$ and $k_2$ inside the chosen separable closure $k^s$ of $k$. Then

$$
\kappa(K_1K_2)=k_1k_2,\qquad
\kappa(K_1\cap K_2)=k_1\cap k_2.
$$

Their ramification indices remain $1$. If one of $k_1/(k_1\cap k_2)$ or
$k_2/(k_1\cap k_2)$ is Galois, the corresponding unramified field extension is Galois and
$K_1,K_2$ are linearly disjoint over $K_1\cap K_2$. Without such a Galois or explicit
disjointness hypothesis, linear disjointness over the intersection is not automatic.

Suppose $\bar g\in k[T]$ is separable but not irreducible:

$$
\bar g=\bar g_1\cdots\bar g_r
$$

with distinct monic irreducible factors. A monic lift $g\in A[T]$ factors uniquely into monic lifts $g_1\cdots g_r$. Consequently

$$
K[T]/(g)\cong\prod_{i=1}^r K[T]/(g_i)
$$

when $g$ is separable and the factors account for its degree. Each field factor is unramified and has residue field $k[T]/(\bar g_i)$. Thus a separable residue algebra, not merely a residue field, lifts to a product of unramified local fields.

This is the local algebra behind unramified scalar extension. If $L/K$ is unramified and $K'/K$ is finite, the residue tensor product

$$
l\otimes_k k'
$$

is a finite product of separable field extensions of $k'$ when interpreted through the residue field of $K'$. Hensel lifting separates the same idempotents upstairs, so $L\otimes_KK'$ is a product of unramified extensions of $K'$.

### 7.7 Roots of unity of order prime to the residue characteristic

Unramified theory controls prime-to-residue-characteristic roots of unity. Let $m$ be invertible in $A$. The polynomial $T^m-1$ has derivative $mT^{m-1}$, which is nonzero at every residue root. Therefore reduction induces a bijection

$$
\mu_m(K^{\mathrm{nr}})\longrightarrow\mu_m(k^{\mathrm{sep}}).
$$

For a finite extension $L/K$, every $m$th root of unity $\bar\zeta\in l$ lifts uniquely in $B$ by Hensel's lemma. The classification theorem places the lift in the unramified intermediate field corresponding to the separable residue subfield $k(\bar\zeta)\subseteq l$. Conversely, reduction preserves the exact order of a root of unity whose order is prime to the residue characteristic. Indeed, if $\zeta$ has exact order $m$ but $\bar\zeta$ has order $d<m$, then $\zeta^d$ is a root of $T^{m/d}-1$ reducing to $1$. That residue root is simple, so its unique lift is $1$, contradicting the order of $\zeta$.

When $k=\mathbf F_q$ and $m\geq2$, the extension generated by a primitive $m$th root of unity, with $\gcd(m,\operatorname{char}k)=1$, is unramified of degree equal to the multiplicative order of $q$ modulo $m$. Indeed, the smallest finite residue field containing such a root is $\mathbf F_{q^d}$ with

$$
m\mid q^d-1.
$$

For example, if $m\mid p^f-1$ and $f$ is minimal, then $\mathbf Q_p(\mu_m)/\mathbf Q_p$ is unramified of degree $f$. Roots of unity of $p$-power order behave very differently in residue characteristic $p$: the derivative is not a unit, their reductions collapse toward $1$, and the resulting extensions are ramified. This contrast is another clean boundary between unramified and wild phenomena.

### 7.8 Unramified extensions and finite precision

If $L/K$ is unramified, then $\pi_K$ is a uniformizer of $L$ and

$$
B/\pi_K^nB
$$

is a finite free $A/\pi_K^nA$-algebra of rank $f$ for every integer $n\geq1$. The extension at all finite precisions is determined by the residue extension. Starting from a separable polynomial $\bar g$, the unique lifted factorization lets one construct compatible roots modulo $\pi_K^n$, and completeness takes their inverse limit.

This does not mean that $B$ is canonically the ring of formal power series over $l$. In equal characteristic with a chosen coefficient field, one has

$$
k'[[t]]
$$

as a literal coefficient extension. In mixed characteristic there is no embedded copy of the residue field, and carries couple the digits. What is canonical is the tower of finite quotients and its unramified lifting property, not a coefficientwise expansion.

## 8. Total ramification and Eisenstein theory

### 8.1 Isolating value-group growth

At the opposite extreme from an unramified extension, no residue-field degree is gained. A finite extension $L/K$ is **totally ramified** if

$$
f(L/K)=1,
$$

or equivalently $l=k$. The fundamental equality then gives

$$
[L:K]=e(L/K).
$$

This definition does not require separability. For example, in characteristic $p$ the extension

$$
k((t^{1/p}))/k((t))
$$

is purely inseparable and totally ramified of degree $p$. By contrast, a Galois extension is separable by definition, so Galois total ramification excludes this example.

Total ramification is inherited by intermediate fields and by subextensions: if $K\subseteq M\subseteq L$ and $L/K$ is totally ramified, tower multiplicativity forces both residue degrees to be $1$. It is also preserved under unramified base change, as seen in Chapter 3.

### 8.2 Why Eisenstein coefficients have their shape

To construct an element of fractional value $1/n$ relative to $K$, one wants an equation whose constant term has value exactly $1$ while every other nonleading coefficient is at least as small. In a root equation

$$
\alpha^n=-a_{n-1}\alpha^{n-1}-\cdots-a_0,
$$

the constant term should balance $\alpha^n$, and all other terms should have strictly larger value. This requirement is encoded by the Eisenstein condition.

A monic polynomial

$$
g(T)=T^n+a_{n-1}T^{n-1}+\cdots+a_0\in A[T]
$$

is **Eisenstein** if

$$
a_i\in\mathfrak m_K\quad(0\leq i<n),
\qquad a_0\notin\mathfrak m_K^2.
$$

Equivalently, every nonleading coefficient has positive valuation and the constant coefficient has valuation exactly $1$.

**Theorem 8.1 (Eisenstein extension).** If $g$ is Eisenstein of degree $n$, $\alpha$ is a root, and $L=K(\alpha)$, then:

1. $g$ is irreducible over $K$;
2. $L/K$ is totally ramified of degree $n$;
3. $\alpha$ is a uniformizer of $L$;
4. $B=A[\alpha]$, with integral basis $1,\alpha,\dots,\alpha^{n-1}$.

**Proof strategy.** Extend the valuation to a splitting field and compare the terms in the root equation. The Newton-polygon balance forces every root to have $K$-relative value $1/n$. Hence a root cannot lie in an extension of degree smaller than $n$. Once the degree is known, distinct congruence classes of valuations prevent cancellation in a power-basis expansion, which identifies the entire integral ring.

Here is the key calculation. Let $w$ extend $v_K$ to a field containing a root $\alpha$, normalized only so that $w|_K=v_K$. If $r=w(\alpha)$, the values in the equation are

$$
nr,\quad v_K(a_i)+ir,\quad v_K(a_0)=1.
$$

The least value in a zero sum must occur at least twice. If $r<1/n$, the unique least term is $\alpha^n$; if $r>1/n$, the unique least term is $a_0$. Thus $r=1/n$. The value group of $K(\alpha)$ therefore contains $\frac1n\mathbf Z$, so its ramification index is at least $n$. Since its degree is at most $n$, the fundamental inequality forces equality throughout. This proves irreducibility and total ramification.

Now use the normalized $v_L$, for which $v_L(\alpha)=1$ and $v_L(a)=nv_K(a)$ for $a\in K$. In an expansion

$$
x=\sum_{i=0}^{n-1}a_i\alpha^i,
$$

the nonzero terms have values $nv_K(a_i)+i$, lying in distinct congruence classes modulo $n$. The least term cannot cancel. Hence $x$ is integral exactly when every $a_i\in A$, proving $B=A[\alpha]$. $\square$

### 8.3 Every total extension comes from a uniformizer

Eisenstein polynomials are not merely a source of examples. They characterize finite totally ramified extensions.

**Theorem 8.2 (uniformizer theorem).** Let $L/K$ be finite and totally ramified, and let $\pi_L$ be any uniformizer of $L$. Then

$$
L=K(\pi_L),\qquad B=A[\pi_L],
$$

and the minimal polynomial of $\pi_L$ over $K$ is Eisenstein of degree $[L:K]$.

**Proof strategy.** Put $M=K(\pi_L)$. The value of $\pi_L$ shows that the value group of $M$ already realizes the full index $e(L/K)=[L:K]$. The roots of its minimal polynomial then control the coefficients, while the norm valuation formula controls the constant term.

**Proof.** Restriction of normalized valuations gives

$$
v_L|_{M^\times}=e(L/M)v_M.
$$

Since $v_L(\pi_L)=1$, the positive integer $e(L/M)$ divides $1$ and is therefore $1$. The tower law now gives $e(M/K)=e(L/K)=[L:K]$. Hence

$$
[L:K]=e(M/K)\leq[M:K]\leq[L:K],
$$

so equality holds and $M=L$.

The element $\pi_L$ is integral, so its minimal polynomial is monic over $A$. In a splitting field, every root of that polynomial has positive valuation by uniqueness of the extended valuation; in the inseparable case the repeated roots are counted with their multiplicities. Every nonleading coefficient, being an elementary symmetric sum of products of positive-valued roots, therefore lies in $\mathfrak m_K$. The constant term is, up to sign, $N_{L/K}(\pi_L)$; because $f=1$, Theorem 4.1 gives it valuation $1$. Thus the polynomial is Eisenstein. Theorem 8.1 then gives $B=A[\pi_L]$. $\square$

This theorem remains valid for inseparable total extensions. The proof by values and degrees does not count embeddings.

### 8.4 Worked Eisenstein extensions

For every prime $p$ and $n\geq1$, the polynomial

$$
T^n-p
$$

is Eisenstein over $\mathbf Q_p$. If $\Pi^n=p$, then $\mathbf Q_p(\Pi)/\mathbf Q_p$ is totally ramified of degree $n$, and

$$
\mathcal O_{\mathbf Q_p(\Pi)}=\mathbf Z_p[\Pi].
$$

This is true even when $p\mid n$. The distinction between tame and wild ramification concerns the divisibility of $e=n$ by $p$, not the validity of Eisenstein's criterion.

Over $k((t))$, the polynomial $T^n-t$ is Eisenstein. If $\operatorname{char}k\nmid n$, the extension is separable; if $\operatorname{char}k=p$ and $n=p$, it is purely inseparable. The valuation-theoretic conclusions are identical, while the automorphism theory is entirely different.

An Eisenstein polynomial need not split into a Galois extension after adjoining one root. For instance, adjoining an $n$th root of a uniformizer need not adjoin the $n$th roots of unity. Total ramification says nothing by itself about normality.

### 8.5 Monogenicity: what is true and what is not

An integral extension is **monogenic** if $B=A[\alpha]$ for one integral element $\alpha$. The primitive element theorem only says $L=K(\alpha)$ for a finite separable field extension. It does not by itself imply equality of integral rings: the order $A[\alpha]$ can be a proper subring of $B$.

Two local situations give clean monogenicity:

- If $L/K$ is unramified, a henselian lift of a primitive residue element generates $B$.
- If $L/K$ is totally ramified, every uniformizer generates $B$.

More generally, suppose the residue extension $l/k$ is separable. Choose a primitive element $\bar\theta$ of $l/k$ and use Hensel's lemma to lift it to an element $\theta\in B$ satisfying a monic lift of its separable minimal polynomial. Then $E=K(\theta)$ is unramified over $K$ with residue field $l$. The tower formulas show that $L/E$ is totally ramified. Consequently, for any uniformizer $\pi_L$ of $L$, the unramified and Eisenstein generation theorems give

$$
B=A[\theta,\pi_L].
$$

In fact the separability of $l/k$ is a clean sufficient hypothesis for monogenicity.

**Theorem 8.3 (local monogenicity).** If $l/k$ is separable, there is an $\alpha\in B$ such that

$$
B=A[\alpha].
$$

**Proof.** Combine the residue generator and the uniformizer just constructed by putting

$$
\alpha=\theta+\pi_L,\qquad C=A[\alpha]\subseteq B.
$$

The finite $A$-algebra $C$ is local. Indeed, $B$ is integral over $C$, so every maximal ideal of $C$ has a maximal ideal of $B$ above it; the only possibility is $\mathfrak m_L$, and therefore the unique maximal ideal of $C$ is $\mathfrak n=C\cap\mathfrak m_L$. Because $C$ is finite over the complete DVR $A$, it is complete for the $\pi_K$-adic topology. The radical of $\pi_KC$ is $\mathfrak n$, so this is also the $\mathfrak n$-adic topology. Thus Hensel's lemma applies in $C$.

Let $g\in A[T]$ be the lifted separable polynomial satisfied by $\theta$. Since $\bar\alpha=\bar\theta$, one has

$$
g(\alpha)\in\mathfrak n,\qquad g'(\alpha)\notin\mathfrak n.
$$

Hensel's lemma in $C$ produces a root $\theta'\in C$ of $g$ congruent to $\alpha$ modulo $\mathfrak n$. Both $\theta'$ and $\theta$ are roots in $B$ reducing to $\bar\theta$; uniqueness in the henselian ring $B$ gives $\theta'=\theta$. Hence $\theta\in C$, and then $\pi_L=\alpha-\theta\in C$. Since $B=A[\theta,\pi_L]$, this proves $B=C=A[\alpha]$. $\square$

In particular, every finite extension of a $p$-adic field is integrally monogenic over its base valuation ring, because finite residue fields are perfect. The theorem is stronger than the field-level primitive element theorem and uses the henselian topology essentially.

There is also a simple obstruction. If $B=A[\alpha]$, then reduction gives $l=k[\bar\alpha]$, so $l/k$ must be a simple extension. Finite separable extensions are simple, but finite inseparable extensions need not be. For an imperfect field with two independent $p$-basis elements, a finite extension such as

$$
k(a^{1/p},b^{1/p})/k
$$

can fail to be simple. The corresponding constant extension of Laurent-series fields has a nonmonogenic residue extension and therefore cannot have its valuation ring generated by one element over the base valuation ring. This is why a blanket monogenicity assertion without residue hypotheses is unsafe.

### 8.6 Recognition through a chosen element

Suppose $\alpha\in B$ has minimal polynomial $g\in A[T]$. If $\bar g$ is irreducible separable and has the same degree as $g$, then $K(\alpha)/K$ is unramified. If $g$ is Eisenstein, it is totally ramified. Between these extremes, reduction of one polynomial can be misleading because $A[\alpha]$ may not be integrally closed. Repeated factors of $\bar g$ suggest ramification, but their multiplicities need not equal the intrinsic ramification index.

The safe procedure is to identify the full valuation ring or prove that the chosen order equals it. Eisenstein's theorem does this automatically. So does the unramified lifting theorem. Outside those settings, polynomial factorization is evidence, not yet an invariant computation.

### 8.7 Changing the uniformizer

The Eisenstein presentation of a totally ramified extension is far from unique. If $\pi_L$ is a uniformizer and $u\in B^\times$, then $u\pi_L$ is another uniformizer. Theorem 8.2 says its minimal polynomial is again Eisenstein and

$$
B=A[u\pi_L].
$$

Thus Eisenstein equations are coordinate descriptions of an intrinsic condition, not extra structure on the extension.

One can also perturb a uniformizer by a higher-order term. If

$$
\pi_L'=\pi_L+a,\qquad v_L(a)\geq2,
$$

then

$$
\pi_L'=\pi_L\left(1+\frac a{\pi_L}\right)
$$

is a uniformizer because the second factor is a unit. Such changes alter the coefficients of the Eisenstein polynomial while leaving the extension unchanged. This flexibility is often used to simplify a coefficient, but it also warns against treating individual coefficients as invariants.

The norm of any uniformizer has the form

$$
N_{L/K}(\pi_L)=u\pi_K
$$

in a totally ramified extension. Replacing $\pi_L$ by $a\pi_L$ multiplies $u$ by $N(a)$. Thus even the unit factor in the norm is coordinate-dependent; only its class modulo the unit norm subgroup has intrinsic meaning.

### 8.8 Prime-to-$p$ radical extensions

Let the residue characteristic exponent be $p$, let $e$ be prime to $p$, and suppose $K$ contains the $e$th roots of unity. If $u\in A^\times$ and

$$
L=K(\alpha),\qquad \alpha^e=u\pi_K,
$$

then $T^e-u\pi_K$ is Eisenstein. The extension is totally ramified of degree $e$. Because all roots $\zeta\alpha$ already lie in $L$, it is Galois and

$$
\operatorname{Gal}(L/K)\cong\mu_e(K)
$$

via $\sigma(\alpha)/\alpha$. This is the basic Kummer model of a totally tamely ramified Galois extension.

If $K$ does not contain $\mu_e$, those roots of unity lie in a suitable finite unramified extension, because $e$ is prime to $p$. After that base change, the particular Eisenstein extension defined by $T^e-u\pi_K$ becomes Galois with the radical description above. This family is the basic model for tame total ramification; a classification of all tame extensions requires additional argument and is not being assumed here.

In positive residue characteristic, the hypothesis $p\nmid e$ is decisive. For $e=p$, the derivative of $T^p-u\pi_K$ is divisible by the maximal ideal in mixed characteristic and is zero in equal characteristic $p$. Roots of unity no longer lift through a separable residue equation, and radical extensions may be inseparable or wildly ramified.

### 8.9 A mixed extension in coordinates

Let $K$ have finite residue field $\mathbf F_q$. First take its unramified extension $K_f$ of degree $f$, then choose a uniformizer $\Pi$ satisfying

$$
\Pi^e=\pi_K
$$

over $K_f$. The resulting field $L=K_f(\Pi)$ has

$$
e(L/K)=e,\qquad f(L/K)=f,\qquad [L:K]=ef.
$$

If $\theta$ is a lifted generator of $\mathbf F_{q^f}/\mathbf F_q$, then

$$
\{\theta^j\Pi^i:0\leq j<f,\ 0\leq i<e\}
$$

is an integral basis. An element of $B$ is expanded first in powers of the ramified parameter $\Pi$, with coefficients in the unramified ring, and then those coefficients are expanded in the residue basis generated by $\theta$.

The construction need not be Galois. If the relevant $e$th roots of unity lie in $K_f$, the ramified stage is Galois; otherwise its normal closure adjoins them. The invariants $e$ and $f$ alone do not decide normality.

## 9. The maximal unramified subextension

### 9.1 The structural question

A general finite local extension may enlarge both residue field and value group. We would like to separate these changes into two stages. The natural plan is to lift as much of the residue extension as possible, then leave a field extension whose residue field no longer grows.

There is one obstruction: only the separable part of the residue extension has an unramified lift. Let $l_s$ be the maximal subfield of $l$ separable over $k$. For a finite extension $l/k$, this is well defined; $l/l_s$ is purely inseparable. The familiar clean decomposition occurs exactly when $l/k$ itself is separable.

### 9.2 Construction and maximality

**Theorem 9.1 (maximal unramified subextension).** Let $L/K$ be finite. There is a unique intermediate field $K_0$ such that

1. $K_0/K$ is unramified;
2. the residue field of $K_0$ is $l_s$ inside $l$;
3. every unramified intermediate extension of $L/K$ is contained in $K_0$.

**Construction.** Choose a primitive element $\bar\theta$ of the finite separable extension $l_s/k$ and its separable minimal polynomial $\bar g$. Lift $\bar g$ monically to $A[T]$. The residue-lift step is not the base-ring form of Hensel's lemma, because $\bar\theta$ lives in $l$, not in $k$: what is needed is the extension property of Theorem 12.3 in Book 1, according to which the valuation ring $B$ of a finite extension of a complete discretely valued field is itself henselian, so a simple residue root in $B/\mathfrak m_B=l$ of a monic polynomial over $A[T]$ lifts uniquely to a root $\theta\in B$. Since $\bar\theta$ is a simple root of $\bar g$, this produces $\theta\in B$. Put $K_0=K(\theta)$. Chapter 7 shows that $K_0/K$ is unramified with residue field $l_s$.

For uniqueness, let $E$ be any unramified intermediate field. Its residue field $k_E$ is a finite
separable subextension of $l/k$, hence lies in $l_s$. Choose a primitive element
$\bar\eta$ of $k_E/k$ and lift its minimal polynomial monically to $A[T]$. The unramified
generation theorem realizes $E$ as the field generated by the unique root in $\mathcal O_E$
reducing to $\bar\eta$. The classification theorem gives a root with the same residue in
$K_0$. Both roots lie in the henselian ring $B$ — henselian by the extension property of Theorem 12.3 in Book 1 — and lift the same simple residue root, so Hensel
uniqueness in $B$ makes them equal. Consequently the given embedded field $E$ is literally contained
in $K_0$, not merely isomorphic to a subfield of it. Applying this argument to two candidates
with residue field $l_s$ proves that they coincide. Thus $K_0$ is not merely maximal by degree;
it is canonically characterized inside $L$.

The remaining extension $L/K_0$ has residue extension $l/l_s$, which is purely inseparable, and

$$
e(L/K_0)=e(L/K),\qquad
f(L/K_0)=[l:l_s].
$$

It is totally ramified precisely when $l/k$ is separable.

### 9.3 The clean decomposition theorem

**Corollary 9.2.** If the residue extension $l/k$ is separable, then the maximal unramified subextension $K_0$ satisfies

$$
[K_0:K]=f(L/K),\qquad [L:K_0]=e(L/K),
$$

$K_0/K$ is unramified, and $L/K_0$ is totally ramified.

Thus every such extension has the shape

$$
K\subseteq K_0\subseteq L
$$

with residue growth first and value growth second. If $k$ is perfect, the residue extension $l/k$ is automatically separable, so the corollary applies to every finite $L/K$. In particular it applies to all finite extensions of $p$-adic fields and all local fields with finite residue field.

When $L/K$ is Galois, $K_0=L^I$, agreeing with Section 5.4. For a nongalois extension the same field is still canonical, but it is constructed by residue lifting rather than as a fixed field.

### 9.4 What fails over imperfect residue fields

Take $K=k((t))$ with imperfect $k$ of characteristic $p$, choose $a\notin k^p$, and let

$$
L=k(a^{1/p})((t)).
$$

Then $e(L/K)=1$ and $f(L/K)=p$, but $l/k$ is purely inseparable. Its maximal separable subextension is $k$, so $K_0=K$. The remainder $L/K_0$ is not totally ramified because its residue degree is $p$. There is no nontrivial unramified subextension capable of absorbing the residue growth.

This counterexample pinpoints the use of perfection in the slogan “every finite extension is unramified followed by totally ramified.” The slogan is correct over perfect residue fields and false without qualification.

### 9.5 A two-stage integral description

Assume $l/k$ is separable. Choose $\theta\in\mathcal O_{K_0}$ lifting a primitive residue element and a uniformizer $\pi_L$ of $L$. Then

$$
\mathcal O_{K_0}=A[\theta],\qquad
B=\mathcal O_{K_0}[\pi_L].
$$

The first presentation is unramified: the derivative of the defining polynomial is a unit. The second is Eisenstein: the minimal polynomial of $\pi_L$ over $K_0$ has degree $e(L/K)$.

Every integral element can therefore be written uniquely as

$$
\sum_{i=0}^{e-1}c_i\pi_L^i,\qquad c_i\in\mathcal O_{K_0},
$$

and each $c_i$ can be expanded in the unramified basis $1,\theta,\dots,\theta^{f-1}$. This produces an explicit integral basis

$$
\{\theta^j\pi_L^i:0\leq j<f, 0\leq i<e\}
$$

of $B$ over $A$. It realizes $[L:K]=ef$ at the level of coordinates.

### 9.6 The tame boundary

Let $p$ denote the characteristic exponent of $k$: $p=\operatorname{char}k$ if that characteristic is positive, and $p=1$ in residue characteristic zero. A finite extension with separable residue extension is **tamely ramified** if

$$
\gcd(e(L/K),p)=1.
$$

In positive residue characteristic this says $p\nmid e(L/K)$. It is **wildly ramified** when $p>1$ and $p\mid e$ in the separable-residue setting. Thus every finite extension with separable residue extension is tame when the residue field has characteristic zero.

For a finite Galois extension with perfect residue field, inertia has order $e$. Consequently the extension is tame exactly when the inertia group has order prime to $p$; when $p>1$, the divisibility $p\mid |I|$ signals wild ramification. The Kummer extensions in Section 8.8 give the elementary radical model when the needed roots of unity and equation are present.

We will not define the wild inertia subgroup here, nor develop its filtration, its jumps, or the comparison between lower and upper numbering. We also will not derive different or discriminant formulas. The role of tameness here is only to mark where prime-to-$p$ power maps on principal units become invertible and norm maps become especially well behaved.

## 10. Units and successive approximation

### 10.1 Why units need their own filtration

The valuation decomposes the multiplicative group into a discrete magnitude and a value-zero part. Fixing a uniformizer gives

$$
L^\times\cong \pi_L^{\mathbf Z}\times B^\times,\qquad
x=\pi_L^{v_L(x)}u.
$$

The factor $\mathbf Z$ is completely understood. All subtler multiplicative arithmetic lies in $B^\times$. Reduction sees its first approximation, but norms and Galois actions often depend on how close a unit is to $1$. This motivates a descending filtration by congruence depth.

Set

$$
U_L^0=B^\times,\qquad
U_L^n=1+\mathfrak m_L^n\quad(n\geq1).
$$

These are subgroups. If $x,y\in\mathfrak m_L^n$, then

$$
(1+x)(1+y)=1+(x+y+xy)\in1+\mathfrak m_L^n,
$$

and the convergent geometric series shows $(1+x)^{-1}\in1+\mathfrak m_L^n$. Each $U_L^n$ is open, and the $U_L^n$ form a neighborhood basis of $1$ in $L^\times$.

The filtration separates a residue unit from successive infinitesimal corrections:

$$
B^\times\supset U_L^1\supset U_L^2\supset\cdots,\qquad
\bigcap_{n\geq1}U_L^n=\{1\}.
$$

### 10.2 The first quotient

Reduction of units is surjective:

$$
B^\times\longrightarrow l^\times.
$$

An integral lift of a nonzero residue is a unit, and the kernel consists exactly of units congruent to $1$. Therefore

$$
U_L^0/U_L^1\cong l^\times.
$$

This quotient is multiplicative. Every higher quotient will instead be additive, reflecting the fact that multiplication linearizes near $1$.

If $l$ is finite of order $q$, Hensel's lemma gives a distinguished multiplicative section. Every $\bar a\in l^\times$ is a simple root of $T^{q-1}-1$, and therefore has a unique lift $[\bar a]\in B^\times$ satisfying

$$
[\bar a]^{q-1}=1,\qquad [\bar a]\equiv\bar a\pmod{\mathfrak m_L}.
$$

Together with $[0]=0$, these are the **Teichmüller representatives**. Hence

$$
B^\times\cong \mu_{q-1}(L)\times U_L^1,
$$

where $\mu_{q-1}(L)$ is the cyclic group of roots of unity of order dividing $q-1$. This splitting depends on finiteness of the residue field; arbitrary residue fields need not admit such a canonical multiplicative section.

### 10.3 Higher quotients are additive residue fields

For $n\geq1$, define

$$
\phi_n:\mathfrak m_L^n/\mathfrak m_L^{n+1}
\longrightarrow U_L^n/U_L^{n+1},\qquad
x\longmapsto1+x.
$$

Because $xy\in\mathfrak m_L^{2n}\subseteq\mathfrak m_L^{n+1}$,

$$
(1+x)(1+y)\equiv1+(x+y)\pmod{\mathfrak m_L^{n+1}}.
$$

Thus $\phi_n$ is a group isomorphism from an additive group to a multiplicative quotient. Choosing $\pi_L$ identifies the ideal layer with $l$:

$$
l^+\xrightarrow{\sim}U_L^n/U_L^{n+1},\qquad
\bar a\longmapsto1+a\pi_L^n.
$$

The identification depends on the uniformizer. Replacing $\pi_L$ by $u\pi_L$ multiplies the coordinate in the $n$th layer by $\bar u^n$. The quotient itself is canonical.

We have therefore reduced the multiplicative group to elementary pieces:

$$
L^\times/U_L^n
$$

has one infinite cyclic valuation coordinate, one residue multiplicative coordinate, and $n-1$ additive residue coordinates. If $|l|=q$, then

$$
[U_L^0:U_L^n]=(q-1)q^{n-1}.
$$

### 10.4 Multiplication, powers, and the residue characteristic

The filtration makes power maps visible one layer at a time. For a positive integer $m$ and $x\in\mathfrak m_L^n$,

$$
(1+x)^m\equiv1+mx\pmod{\mathfrak m_L^{2n}}.
$$

On $U_L^n/U_L^{n+1}$, the $m$th-power map is multiplication by the residue of $m$ in $l$. If $m$ is prime to the residue characteristic, this is an isomorphism on every graded layer. Completeness then lets one correct layer after layer.

**Proposition 10.1.** If the positive integer $m$ is invertible in $B$, the map

$$
U_L^1\longrightarrow U_L^1,\qquad u\longmapsto u^m
$$

is an isomorphism.

To solve $y^m=u$, begin modulo $\mathfrak m_L^2$. Multiplication by $m$ is invertible on the first layer, so choose a correction. Repeat at every layer. The compatible approximations converge, and uniqueness follows because a nontrivial quotient of two solutions would have a first nonzero layer on which multiplication by $m$ vanishes, impossible.

When the residue characteristic divides $m$, the first-order map can vanish. This is the elementary beginning of wild behavior. For example, in residue characteristic $p$,

$$
(1+x)^p=1+px+\cdots+x^p,
$$

and the depth of the result depends on both $v_L(p)$ and $v_L(x)$. Systematically tracking that competition leads to the ramification filtrations reserved for Book 3.

### 10.5 Equal-characteristic example

Let $L=k((t))$. Then

$$
U_L^0=k[[t]]^\times,\qquad U_L^n=1+t^nk[[t]].
$$

Every unit has the form

$$
a_0(1+a_1t+a_2t^2+\cdots),\qquad a_0\in k^\times.
$$

The quotient $U^n/U^{n+1}$ records the coefficient $a_n$ after the earlier coefficients have been removed. If $\operatorname{char}k=p$, the identity

$$
(1+x)^p=1+x^p
$$

shows that $p$th powers jump from depth $n$ to depth $pn$. This starkly differs from prime-to-$p$ powers and exhibits wild behavior without any Galois machinery.

### 10.6 Mixed-characteristic example

For a finite extension $L/\mathbf Q_p$, let $e_L=v_L(p)$. If $x\in\mathfrak m_L^n$, then the two most important terms of $(1+x)^p-1$ have valuations

$$
v_L(px)\geq e_L+n,\qquad v_L(x^p)\geq pn.
$$

Thus the $p$th-power map sends $U_L^n$ at least into

$$
U_L^{\min(e_L+n,pn)}.
$$

For sufficiently large $n$, the linear term $px$ controls and the depth increases by $e_L$; for small $n$, nonlinear terms can compete. This elementary estimate is useful, but a complete account of its transition points belongs to finer ramification theory.

### 10.7 Galois action on the layers

If $L/K$ is Galois, every $U_L^n$ is $G$-stable. On

$$
U_L^0/U_L^1\cong l^\times,
$$

the action is the usual residue action, so inertia acts trivially. On a higher layer, after choosing a uniformizer,

$$
\sigma(1+a\pi_L^n)\equiv
1+\sigma(a)\left(\frac{\sigma(\pi_L)}{\pi_L}\right)^n\pi_L^n
\pmod{U_L^{n+1}}.
$$

For $\sigma\in I$, the residue action on $a$ is trivial, but the residue of $\sigma(\pi_L)/\pi_L$ may be nontrivial. This character is the first visible action of inertia beyond the residue field. Refining the kernels of these actions leads toward tame and wild ramification groups; we stop before introducing that systematic filtration.

### 10.8 Completeness and inverse limits of units

The field $L$ is complete, so its units are recovered from all finite congruence quotients:

$$
U_L^0\cong\varprojlim_n(B/\mathfrak m_L^n)^\times.
$$

Indeed, a compatible family of invertible residues gives a compatible family in $B/\mathfrak m_L^n$, hence an element of $B$. Its first residue is nonzero, so the limit is a unit. Similarly,

$$
U_L^1\cong\varprojlim_n U_L^1/U_L^n.
$$

This description justifies successive approximation as a group-theoretic method. To construct a principal unit with prescribed properties, it is enough to solve compatible finite problems at every depth.

If $l$ is finite, each quotient is finite and $U_L^0$ is compact. The groups $U_L^n$ are compact open subgroups of $L^\times$, and

$$
L^\times/U_L^0\cong\mathbf Z
$$

is discrete. Thus $L^\times$ is locally compact but not compact: its noncompact direction is exactly the valuation.

If $l$ is infinite, $U_L^0/U_L^1\cong l^\times$ is an infinite discrete quotient, so $U_L^0$ is not compact. Completeness alone does not imply local compactness; the residue field must be finite.

### 10.9 Unit coordinates and their limitations

Choosing residue representatives and a uniformizer lets one write a unit as an infinite product of successive corrections:

$$
u=s_0\prod_{n\geq1}(1+s_n\pi_L^n),
$$

with coefficients chosen recursively from residue representatives. The exact indexing and coefficients depend on how earlier factors are removed. The product converges because its factors tend to $1$.

This is a useful multiplicative analogue of a digit expansion, but it is not canonical. Carries change later coefficients, a new uniformizer rescales every graded coordinate, and in mixed characteristic no coefficient field splits reduction additively. The canonical data are the filtration and its graded quotients, not a chosen infinite coordinate sequence.

For sufficiently deep units in characteristic zero, the convergent series

$$
\log(1+x)=x-\frac{x^2}{2}+\frac{x^3}{3}-\cdots
$$

and

$$
\exp(x)=1+x+\frac{x^2}{2!}+\cdots
$$

often identify a deep principal-unit group with an additive ideal. The depth required depends on the residue characteristic and the ramification of $L/\mathbf Q_p$. We do not need precise convergence thresholds here. The first-order congruence $1+x\leftrightarrow x$ already supplies the uniform, characteristic-free part of this linearization.

### 10.10 Roots of unity inside the unit filtration

Every root of unity in $L$ is a unit. Those of order prime to the residue characteristic inject under reduction and lie in the residue-unit factor. Roots of residue-characteristic-power order, when they exist, reduce to $1$ and lie in $U_L^1$.

For a $p$-adic field with residue field of order $q$, the prime-to-$p$ roots of unity form the cyclic group $\mu_{q-1}(L)$ of Teichmüller units. Any additional torsion in $B^\times$ is $p$-power torsion inside $U_L^1$. Thus

$$
B^\times\cong\mu_{q-1}(L)\times U_L^1
$$

separates visible residue torsion from potentially ramified principal-unit torsion.

In equal characteristic $p$, the equation $X^{p^r}=1$ has only the root $1$ in a field, because

$$
X^{p^r}-1=(X-1)^{p^r}.
$$

So principal units have no nontrivial $p$-power roots of unity. Mixed characteristic permits them after ramified cyclotomic extensions. The unit filtration thus registers a genuine difference between equal and mixed characteristic that the formulas for $e$ and $f$ alone do not see.

## 11. Norms and traces along the unit filtration

### 11.1 Continuity and the first constraints

The norm is continuous because it is a polynomial in the coordinates of an element. Since it sends $B^\times$ into $A^\times$ and $1$ to $1$, sufficiently deep principal units map to deep principal units. Valuation theory makes the first bounds explicit.

For a finite separable extension, write the norm in a normal closure $\Omega$. Scale the unique extended valuation $w$ on $\Omega$ so that $w|_L=v_L$. If $x\in\mathfrak m_L^n$, uniqueness gives $w(\sigma x)=v_L(x)\geq n$ for every $K$-embedding $\sigma$. Expanding

$$
N_{L/K}(1+x)=\prod_\sigma(1+\sigma x)
$$

shows that each nonconstant symmetric sum has $w$-value at least $n$. Because the sum lies in $K$ and $w|_K=e(L/K)v_K$, its $K$-valuation is at least $\lceil n/e\rceil$. Purely inseparable norms give the same bound by taking powers, and transitivity handles the general finite extension. Hence

$$
N_{L/K}(U_L^n)\subseteq U_K^{\lceil n/e\rceil}\qquad(n\geq1).
$$

This inclusion is deliberately basic. Exact images at every depth depend on finer ramification data.

At depth zero, Proposition 4.2 gives the precise residue constraint:

$$
\overline{N_{L/K}(u)}=N_{l/k}(\bar u)^e.
$$

Thus the norm on $U_L^0/U_L^1$ is the $e$th power of the residue-field norm.

### 11.2 Linearizing the norm

Near $1$, norm is controlled to first order by trace. For $x\in L$ small enough,

$$
N_{L/K}(1+x)=1+\operatorname{Tr}_{L/K}(x)+\text{terms of degree at least }2.
$$

This is the determinant identity

$$
\det(1+m_x)=1+\operatorname{tr}(m_x)+\cdots.
$$

In the separable case it is also the expansion of the product over embeddings. With the scaled valuation $w$ used in the preceding section, if $x\in\mathfrak m_L^n$ the omitted terms have $w$-value at least $2n$, and therefore $K$-valuation at least $\lceil2n/e\rceil$. Purely inseparable powers and transitivity give the same bound for a general finite extension.

The slogan “the derivative of norm at $1$ is trace” explains much of the unit theory. Surjectivity questions for norms on successive infinitesimal layers become surjectivity questions for trace maps on residue fields.

Trace itself respects a coarse depth bound:

$$
\operatorname{Tr}_{L/K}(\mathfrak m_L^n)
\subseteq\mathfrak m_K^{\lceil n/e\rceil}.
$$

For separable extensions this follows by summing equal-valuation conjugates; for inseparable extensions the trace may vanish. Equality is not promised. Its failure records arithmetic later measured by the different.

### 11.3 The unramified case

Suppose $L/K$ is unramified. We may choose the same uniformizer $\pi$ in both fields, and $e=1$. For $n\geq1$,

$$
N_{L/K}(1+a\pi^n)
\equiv1+\operatorname{Tr}_{l/k}(\bar a)\pi^n
\pmod{U_K^{n+1}}.
$$

Thus on the $n$th graded layer the norm is the additive residue trace

$$
l^+\longrightarrow k^+.
$$

Because $l/k$ is finite separable, its trace map is a nonzero $k$-linear functional and hence is surjective. One may therefore solve a norm equation one layer at a time. Completeness turns the successive corrections into an element of $U_L^1$.

**Proposition 11.1.** If $L/K$ is finite unramified, then

$$
N_{L/K}:U_L^1\twoheadrightarrow U_K^1.
$$

**Proof.** Let $u\in U_K^1$. Starting with $y_1=1$, suppose $y_n\in U_L^1$ has been chosen so that

$$
uN(y_n)^{-1}\in U_K^n.
$$

Surjectivity of the norm on the $n$th graded layer supplies $z_n\in U_L^n$ whose norm agrees with this error modulo $U_K^{n+1}$. Put $y_{n+1}=y_nz_n$. Then the error lies in $U_K^{n+1}$. Since $z_n\to1$, the products $y_n$ converge in $U_L^1$ to an element $y$, and continuity of norm gives $N(y)=u$. $\square$

On all units, the remaining obstruction is the residue norm:

$$
N_{L/K}(U_L^0)
=\{u\in U_K^0:\bar u\in N_{l/k}(l^\times)\}.
$$

For arbitrary residue fields, $N_{l/k}:l^\times\to k^\times$ need not be surjective. For finite residue fields it is surjective because both multiplicative groups are cyclic and the norm is

$$
x\longmapsto x^{(q^f-1)/(q-1)}.
$$

Consequently, if the residue field is finite, the norm from an unramified extension is surjective on units.

The valuation formula supplies the only obstruction on the whole multiplicative group. For an unramified extension of degree $f$ with finite residue field,

$$
N_{L/K}(L^\times)=\pi_K^{f\mathbf Z}\times U_K^0,
$$

so the norm subgroup has index $f$ in $K^\times$.

### 11.4 The totally ramified case

Suppose $L/K$ is totally ramified of degree $e$. The residue fields agree, and on residue units the norm is

$$
\bar u\longmapsto\bar u^e.
$$

Meanwhile the norm of a uniformizer has valuation $1$, so the valuation coordinate is surjective. The subtle part is again the principal units.

If $e$ is prime to the residue characteristic, the extension is tame in the elementary sense. Reduction of trace on an integral element is

$$
\overline{\operatorname{Tr}_{L/K}(x)}=e\bar x,
$$

and multiplication by $e$ is invertible in the residue field. The corresponding norm statement has a particularly direct proof.

**Proposition 11.2.** If $L/K$ is finite, totally ramified, and $e$ is prime to the residue characteristic, then

$$
N_{L/K}:U_L^1\twoheadrightarrow U_K^1.
$$

**Proof.** Since $e$ is invertible in $A$, Proposition 10.1 says that the $e$th-power map is an automorphism of $U_K^1$. Given $u\in U_K^1$, choose $y\in U_K^1$ with $y^e=u$ and view $y$ as an element of $L$. Scalar multiplication by $y$ on the $e$-dimensional $K$-space $L$ has determinant $y^e$, so

$$
N_{L/K}(y)=y^e=u.
$$

Thus every principal unit is a norm. $\square$

The image on all units has residue classes $(k^\times)^e$:

$$
N_{L/K}(U_L^0)
=\{u\in U_K^0:\bar u\in(k^\times)^e\}.
$$

The containment follows from the residue formula. For the reverse containment, first choose a unit of $L$ with the desired residue; its norm has the prescribed residue class, and Proposition 11.2 corrects the quotient by a principal unit.

If $k$ is finite of order $q$, the index of this unit norm subgroup is $\gcd(e,q-1)$. The valuation coordinate contributes no further index.

When the positive residue characteristic divides $e$, multiplication by $e$ vanishes on the first residue layer. The first-order argument breaks precisely where wild ramification begins. Norms still map deep units to deep units, but their exact image depends on higher ramification and the different. No uniform formula using only $e$ and $f$ can recover it.

### 11.5 Norms in towers

Let $K\subseteq M\subseteq L$. Transitivity gives

$$
N_{L/K}(U_L^n)
=N_{M/K}\bigl(N_{L/M}(U_L^n)\bigr).
$$

This is most useful after splitting a finite extension with separable residue extension into

$$
K\subseteq K_0\subseteq L,
$$

where $K_0/K$ is unramified and $L/K_0$ is totally ramified. One first handles residue-field norm and trace through the unramified layer, then handles the value and principal-unit effects through the ramified layer. The two-stage method mirrors the two-stage integral basis from Chapter 9.

For finite residue fields, both residue norm and residue trace are surjective. Any failure of norm surjectivity deep in the units is therefore a genuinely ramified phenomenon, invisible in $e$, $f$, and the residue extension alone.

### 11.6 A worked comparison

Let $K$ have residue field $\mathbf F_q$.

First take the unramified extension $K_f/K$ of degree $f$. A uniformizer remains a uniformizer, and

$$
v_K(Nx)=f\,v_{K_f}(x).
$$

All base units are norms, but a base uniformizer is not a norm unless $f=1$; its valuation is not divisible by $f$.

Now take a totally tamely ramified extension $L/K$ of degree $e$. A uniformizer norm has valuation $1$, and every principal unit is a norm. A residue unit $a\in\mathbf F_q^\times$ is the residue of a norm exactly when it is an $e$th power. Thus the unramified extension puts its obstruction in the valuation coordinate, whereas the tame totally ramified extension puts its elementary obstruction in the residue-unit coordinate.

This comparison is a compact preview of local reciprocity: unramified and ramified extensions are detected by different pieces of $K^\times$. We do not invoke reciprocity here; the conclusion follows directly from valuation, residue norm, and unit filtration.

### 11.7 Explicit norm equations in an unramified extension

Let $L/K$ be unramified with finite residue fields. To solve

$$
N_{L/K}(x)=a
$$

for a given $a\in K^\times$, begin with the valuation. Since

$$
v_K(Nx)=f\,v_L(x),
$$

a necessary condition is $f\mid v_K(a)$. It is also sufficient. Write

$$
a=\pi_K^{fr}u.
$$

The common uniformizer satisfies

$$
N_{L/K}(\pi_K^r)=\pi_K^{fr},
$$

so it remains to solve $N(y)=u$ for a unit $y$. Choose a residue element $\bar y\in l^\times$ with

$$
N_{l/k}(\bar y)=\bar u,
$$

lift it to $y_0\in U_L^0$, and note that $u/N(y_0)\in U_K^1$. Proposition 11.1 supplies $y_1\in U_L^1$ with this norm. Then $y=y_0y_1$ solves the equation.

This constructive proof shows exactly where finiteness of the residue field was used: it made the residue norm surjective. The principal-unit correction used only separability of the residue extension and completeness.

### 11.8 Explicit norm equations in a tame total extension

Now let $L/K$ be totally tamely ramified of degree $e$ with finite residue field $k=\mathbf F_q$. Since the norm of a uniformizer has valuation $1$, there is no valuation obstruction. Principal units are norms, so only the first residue unit matters.

The criterion can be written without hiding the unit contributed by the chosen uniformizer. Put

$$
c=\frac{N_{L/K}(\pi_L)}{\pi_K}\in A^\times.
$$

For $a=\pi_K^r u$ with $u\in A^\times$, an equation $N_{L/K}(x)=a$ is solvable exactly when

$$
\bar u\,\bar c^{-r}\in(k^\times)^e.
$$

Indeed, write $x=\pi_L^r y$ with $y\in B^\times$. Then the remaining equation is $N(y)=uc^{-r}$, and the unit norm description in Section 11.4 gives precisely the displayed condition. Consequently the norm quotient has order

$$
|k^\times/(k^\times)^e|=\gcd(e,q-1).
$$

This formula does not say that the norm quotient of every totally ramified extension has that order. It uses tameness to obtain surjectivity on principal units. In a wild extension, higher unit layers contribute additional obstructions. The factor $c^{-r}$ also shows why one should not split valuation and unit obstructions without recording the chosen uniformizer's norm.

As an example, let $L=K(\Pi)$ with $\Pi^e=\pi_K$ and assume $\mu_e\subset K$. Up to the sign dictated by the constant coefficient,

$$
N_{L/K}(\Pi)=(-1)^{e+1}\pi_K.
$$

For a base unit $u\in K^\times\subset L^\times$,

$$
N_{L/K}(u)=u^e.
$$

But units not lying in $K$ can have more general norms; Proposition 11.2 shows that all principal units occur. It would be incorrect to infer from the formula on base units that the whole unit norm image consists only of $e$th powers in $U_K^0$.

### 11.9 Trace versus norm on the first layer

The residue formulas show a useful asymmetry. For a totally ramified extension,

$$
\overline{\operatorname{Tr}(x)}=e\bar x,\qquad
\overline{N(u)}=\bar u^e.
$$

In tame ramification, multiplication by $e$ is invertible on the additive field $k$, so trace controls additive corrections and norm becomes surjective on principal units. Yet the $e$th-power map on $k^\times$ need not be surjective. Additive and multiplicative residue groups therefore respond differently to the same integer.

In an unramified extension,

$$
\overline{\operatorname{Tr}(x)}=\operatorname{Tr}_{l/k}(\bar x),\qquad
\overline{N(u)}=N_{l/k}(\bar u).
$$

Over finite fields both maps are surjective, but for different reasons: trace is a nonzero linear functional, while norm is an exponent map on a cyclic group. Their simultaneous surjectivity is a finite-field fact, not a formal consequence of unramifiedness over an arbitrary residue field.

These first-layer calculations are often enough to start a lifting argument. When they fail, the failure identifies exactly which deeper information must be supplied by finer ramification theory.

## 12. Krasner's lemma and stability of generators

### 12.1 Why proximity can force field containment

So far, closeness has been used to lift roots and to solve norm equations one congruence at a
time. There is a more surprising use. If an algebraic element is approximated more closely than
any of its distinct conjugates approach it, then the approximating element must carry enough
algebraic information to recover the original one. Metric proximity forces an inclusion of
fields.

This principle is the bridge between continuous and discrete classification. Coefficients of a
polynomial range through a topological space, but the extension generated by a root is an
isomorphism class. Krasner's lemma makes that isomorphism class locally constant around a
separable polynomial. Compactness can then turn local constancy into finiteness.

Fix an algebraic closure $\overline K$ and the unique extension of the absolute value of $K$ to
$\overline K$. The algebraic closure need not be complete; this causes no problem in the lemma
itself. When Hensel's lemma is needed, we work in a finite splitting field, which is complete by
Chapter 1.

### 12.2 The Krasner radius

Let $\alpha\in\overline K$ be separable over $K$, and let

$$
\alpha=\alpha_1,\alpha_2,\ldots,\alpha_d
$$

be its distinct $K$-conjugates. If $d>1$, define the **Krasner radius** of $\alpha$ over $K$ by

$$
\delta_K(\alpha)=\min_{2\leq i\leq d}|\alpha-\alpha_i|.
$$

It is positive because there are finitely many distinct conjugates. If $\alpha\in K$, we put
$\delta_K(\alpha)=+\infty$; then the containment conclusion below is tautological.

The radius depends on the chosen absolute-value normalization, but the open condition
$|\beta-\alpha|<\delta_K(\alpha)$ does not change when the absolute value is replaced by a
positive power. It also depends on the chosen conjugate $\alpha$: another conjugate has the same
multiset of pairwise distances, although the displayed center changes.

The strict inequality is essential. At the boundary, $\beta$ could be another conjugate of
$\alpha$. For instance, if $\alpha$ is quadratic and $\beta$ is its other conjugate, then
$|\beta-\alpha|=\delta_K(\alpha)$, while proximity alone has not selected the original root.

### 12.3 Krasner's lemma

**Theorem 12.1 (Krasner's lemma).** Let $\alpha,\beta\in K^{\mathrm{sep}}$. If $\alpha$ is
separable over $K$ and

$$
|\beta-\alpha|<|\alpha'-\alpha|
$$

for every $K$-conjugate $\alpha'\ne\alpha$, then

$$
K(\alpha)\subseteq K(\beta).
$$

Equivalently, it is enough that $|\beta-\alpha|<\delta_K(\alpha)$.

**Proof strategy.** Any symmetry fixing $\beta$ must preserve distance. It therefore sends
$\alpha$ to a conjugate that is still closer to $\alpha$ than every distinct conjugate is allowed
to be. The ultrametric inequality then forces that conjugate to be $\alpha$ itself. Fixed fields
convert this statement about symmetries into the desired field inclusion.

**Proof.** Choose a finite Galois extension $M/K$ containing $\alpha$ and $\beta$. Let
$\sigma\in\operatorname{Gal}(M/K(\beta))$. Uniqueness of the extended absolute value implies that
$\sigma$ is an isometry. Since $\sigma(\beta)=\beta$,

$$
|\sigma(\alpha)-\beta|
=|\sigma(\alpha-\beta)|
=|\alpha-\beta|.
$$

The strong triangle inequality gives

$$
|\sigma(\alpha)-\alpha|
\leq\max\{|\sigma(\alpha)-\beta|,|\beta-\alpha|\}
=|\beta-\alpha|
<\delta_K(\alpha).
$$

But $\sigma(\alpha)$ is a $K$-conjugate of $\alpha$. By the definition of the Krasner radius, the
only such conjugate at distance less than $\delta_K(\alpha)$ from $\alpha$ is $\alpha$ itself.
Thus every element of $\operatorname{Gal}(M/K(\beta))$ fixes $\alpha$. Galois correspondence now
gives

$$
K(\alpha)\subseteq K(\beta).
$$

This proves the theorem. $\square$

The proof exposes every hypothesis. Separability makes distinct conjugates and a positive
separation radius available. Algebraicity allows us to work in a finite Galois extension.
Completeness supplies uniqueness of the valuation and therefore invariance of distance under
every $K$-automorphism. Henselianity would suffice for that last step.

### 12.4 Stability of simple roots

To use Krasner's lemma on polynomials, one must know that a small change of coefficients produces
a root close to a chosen simple root. This is a Henselian statement.

**Proposition 12.2 (simultaneous stability of simple roots).** Let

$$
f(T)=T^d+a_{d-1}T^{d-1}+\cdots+a_0\in K[T]
$$

be monic and separable. Let $M/K$ be a finite splitting field and write its roots as
$\alpha_1,\ldots,\alpha_d$. Given pairwise disjoint open balls $V_i$ around the roots, there is a
neighborhood $\mathcal V$ of $(a_0,\ldots,a_{d-1})$ in $K^d$ such that every monic

$$
g(T)=T^d+b_{d-1}T^{d-1}+\cdots+b_0
$$

with coefficient vector in $\mathcal V$ has exactly one root $\beta_i$ in each $V_i$. All these
roots lie in $M$, and $g=\prod_i(T-\beta_i)$ there.

**Proof strategy.** At each $\alpha_i$, the derivative $f'(\alpha_i)$ is nonzero. If the
coefficients of $g$ are sufficiently close to those of $f$, then $g(\alpha_i)$ is arbitrarily
small while $g'(\alpha_i)$ remains as large as $f'(\alpha_i)$. The strong form of Hensel's lemma
then produces a unique nearby root.

**Proof.** The Newton form inherited from Book 1 is stated for an integral polynomial evaluated
at an integral point, so we first put the problem into those coordinates. Choose
$c\in K^\times$ of sufficiently small absolute value that every $z_i=c\alpha_i$ is integral
over $\mathcal O_M$ and

$$
F(S)=c^df(S/c)=\prod_i(S-z_i)
$$

belongs to $\mathcal O_M[S]$. For $g$ as in the statement put

$$
G(S)=c^dg(S/c).
$$

After restricting the coefficient neighborhood of $g$, the polynomial $G$ also belongs to
$\mathcal O_M[S]$ and is as close to $F$ as desired coefficient by coefficient. Multiplication
by $c$ carries the prescribed balls about the $\alpha_i$ to pairwise disjoint open balls about
the $z_i$.

Because only finitely many $z_i$ occur, choose a positive radius $r$ so small that the closed
balls of radius $r$ about the $z_i$ lie in those scaled prescribed balls and are pairwise
disjoint. Continuity of polynomial evaluation and derivative evaluation in the coefficients
allows us to require simultaneously that

$$
|G(z_i)|<|G'(z_i)|^2
$$

and that the Newton estimate place the resulting root within distance $r$ of $z_i$. More
explicitly, first keep $|G'(z_i)|=|F'(z_i)|$ by making
$|G'(z_i)-F'(z_i)|<|F'(z_i)|$, and then make $|G(z_i)|$ smaller than both
$|F'(z_i)|^2$ and $r|F'(z_i)|$.

The field $M$ is finite over $K$ and hence complete. Hensel's lemma in $M$ gives a root
$w_i\in M$ satisfying

$$
|w_i-z_i|
=\frac{|G(z_i)|}{|G'(z_i)|}<r.
$$

Set $\beta_i=w_i/c$. Then $g(\beta_i)=0$, and $\beta_i$ lies in $V_i$. The scaled balls are
disjoint, so the $\beta_i$ are distinct. A degree-$d$ polynomial with $d$ distinct roots has no
others, proving the factorization and the assertion of uniqueness in each ball.
$\square$

The proposition is a nonarchimedean root-continuity theorem. Separability is exactly what makes
the derivatives nonzero. There is no uniform stable labeling near a polynomial with a multiple
root.

### 12.5 Nearby polynomials define the same extension

Combine the two preceding results. Let $f$ be the minimal polynomial of a separable element
$\alpha$ of degree $d$. Choose the ball about $\alpha$ to have radius strictly smaller than
$\delta_K(\alpha)$. If a monic degree-$d$ polynomial $g$ is sufficiently close to $f$, Proposition
12.2 gives a root $\beta$ in that ball. Krasner's lemma gives

$$
K(\alpha)\subseteq K(\beta).
$$

But $[K(\beta):K]\leq d=[K(\alpha):K]$, so equality holds. In particular $g$ is irreducible and

$$
K(\beta)=K(\alpha).
$$

We have proved the form used later.

**Corollary 12.3 (local constancy of the generated field).** Around every monic separable
irreducible polynomial $f\in K[T]$ of fixed degree there is an open neighborhood in coefficient
space such that every polynomial in that neighborhood is irreducible and generates, through any
root matched with a root of $f$, a $K$-isomorphic field extension.

This is stronger than mere irreducibility stability. It says that sufficiently many initial
digits of the coefficients determine the entire extension, although how many digits suffice
depends on the distances between the conjugates.

### 12.6 What separability is doing

If $f'(T)=0$, its roots cannot be separated by the derivative argument. In characteristic $p$,
the polynomial $T^p-a$ has one geometric root with multiplicity $p$. Its coefficient can be
perturbed by an arbitrarily small amount to produce fields with behavior that is not controlled
by a positive conjugate-separation radius. Krasner's lemma is therefore a theorem about separable
generators, not a generic continuity theorem for all finite extensions.

This boundary is harmless for finite extensions of characteristic-zero local fields, because all
of them are separable. It becomes decisive over $\mathbf F_q((t))$, where inseparable extensions
exist and, more importantly for finiteness, wildly ramified separable extensions can accumulate
near inseparable equations.

## 13. How many extensions are there?

### 13.1 The finiteness question and its exact scope

Krasner's lemma is often summarized by saying that a local field has only finitely many
extensions of bounded degree. That sentence needs a characteristic hypothesis. The correct
classical statement is:

**Theorem 13.1 (bounded-degree finiteness in characteristic zero).** Let $K$ be a complete
discretely valued field of characteristic $0$ with finite residue field. For every $N\geq1$,
there are only finitely many $K$-isomorphism classes of finite extensions $L/K$ satisfying
$[L:K]\leq N$.

Thus the theorem applies to every finite extension of $\mathbf Q_p$. It does not extend unchanged
to equal characteristic $p$: there are infinitely many degree-$p$ separable extensions of
$\mathbf F_q((t))$. Two ingredients in Theorem 13.1 are essential. Finite residue field gives
compactness of the valuation ring, and characteristic zero makes every defining irreducible
polynomial separable.

There is also a characteristic-free tame version.

**Theorem 13.2 (bounded tame finiteness).** Let $K$ be a complete discretely valued field with
finite residue field of characteristic exponent $p$. For every $N$, there are only finitely many
$K$-isomorphism classes of tamely ramified extensions $L/K$ with $[L:K]\leq N$.

Here unramified extensions count as tame. In characteristic zero, Theorem 13.1 is stronger: it
also includes extensions whose ramification index is divisible by the residue characteristic.
In positive characteristic, Theorem 13.2 excludes the wild families responsible for failure.

### 13.2 Compact families of Eisenstein polynomials

The common proof is a compactness argument built from the decomposition of Chapter 9. Let $E$ be
a complete discretely valued field with finite residue field, and fix $e\geq1$. The monic
Eisenstein polynomials of degree $e$ are parametrized by

$$
\mathfrak m_E^{\,e-1}\times
(\mathfrak m_E\setminus\mathfrak m_E^2),
$$

where the last coordinate is the constant coefficient. The ring $\mathcal O_E$ is compact,
every power of its maximal ideal is compact and open, and
$\mathfrak m_E\setminus\mathfrak m_E^2$ is closed in $\mathfrak m_E$. Hence this parameter space is
compact.

Suppose every polynomial in the family is separable. Corollary 12.3 gives, around each polynomial
$g$, an open set on which the field generated by a root is constant up to $E$-isomorphism. These
open sets cover the compact parameter space. A finite subcover shows that only finitely many
totally ramified degree-$e$ extensions of $E$ arise.

The separability condition holds automatically if $\operatorname{char}E=0$. It also holds when
$e$ is prime to $\operatorname{char}E=p>0$: the derivative of a monic degree-$e$ polynomial has
nonzero leading term $eT^{e-1}$. This is the precise point where the proof separates the
characteristic-zero and tame cases from wild equal characteristic.

One can make the compactness proof effective in principle. A finite subcover may be refined by a
common congruence modulus, so sufficiently many coefficient digits determine the extension.
The theorem does not provide a universal modulus depending only on the degree without further
estimates; conjugate distances vary from one polynomial to another.

### 13.3 Finiteness in characteristic zero

We now prove Theorem 13.1. Fix a degree $d\leq N$. Because the residue field of $K$ is finite,
there is a unique unramified extension $K_f/K$ of each degree $f$. For any degree-$d$ extension
$L/K$, its residue field is finite and therefore separable over that of $K$. The maximal
unramified subextension $K_f\subseteq L$ has degree

$$
f=f(L/K),
$$

and $L/K_f$ is totally ramified of degree

$$
e=e(L/K),\qquad ef=d.
$$

There are only finitely many factorizations $d=ef$. For each one, the base $K_f$ is fixed, and a
uniformizer of $L$ has an Eisenstein minimal polynomial of degree $e$ over $K_f$. In characteristic
zero all these polynomials are separable. Section 13.2 therefore gives only finitely many
$K_f$-isomorphism classes, hence only finitely many $K$-isomorphism classes. Taking the finite
union over $d\leq N$ proves the theorem. $\square$

Notice what the proof does not claim. It does not say that there are finitely many embeddings of
these fields into a fixed algebraic closure; a single isomorphism class can have several
embeddings. It classifies the fields as extensions of $K$. Nor does it claim finiteness of all
finite extensions with no degree bound.

### 13.4 The tame positive-characteristic range

The proof of Theorem 13.2 is the same after one observes where tameness enters. A finite residue
field is perfect, so the maximal unramified subextension $K_f$ always exists and the remaining
stage is totally ramified. For a tame extension its ramification degree $e$ is prime to $p$.
Every degree-$e$ Eisenstein polynomial over $K_f$ is then separable, and its compact parameter
space breaks into finitely many Krasner neighborhoods. Only finitely many pairs $(e,f)$ satisfy
$ef\leq N$, proving the result. $\square$

This theorem also explains a frequently useful fixed-degree corollary. If
$K=\mathbf F_q((t))$ and $d$ is prime to $p$, then every degree-$d$ extension is tame, so there are
only finitely many degree-$d$ extensions up to $K$-isomorphism. Degrees divisible by $p$ require a
separate analysis and do not satisfy a blanket finiteness statement.

### 13.5 Wild equal characteristic: an infinite family

Let

$$
K=\mathbf F_q((t)),\qquad \operatorname{char}K=p.
$$

For every positive integer $m$ not divisible by $p$, consider

$$
L_m=K(y_m),\qquad y_m^p-y_m=t^{-m}.
$$

The polynomial $T^p-T-t^{-m}$ is separable because its derivative is $-1$. We spell out why it
defines a cyclic extension of degree $p$. If $y$ is one root, all roots are $y+c$ with
$c\in\mathbf F_p$, so they already lie in $K(y)$. Hence $K(y)$ is the splitting field of a
separable polynomial and is Galois. Its Galois group injects into the additive group
$\mathbf F_p$ by

$$
\sigma\longmapsto\sigma(y)-y.
$$

It therefore has order $1$ or $p$. The first case occurs exactly when $y\in K$, equivalently
when the right side of the equation is $x^p-x$ for some $x\in K$. In our case no such $x$
exists. Indeed, if $v_K(x)<0$, then

$$
v_K(x^p-x)=p\,v_K(x),
$$

which is divisible by $p$; if $v_K(x)\geq0$, then $x^p-x$ has no pole. Since $t^{-m}$ has pole
order $m$ prime to $p$, it is not of this form. Thus the Galois group has order $p$, proving both
irreducibility and cyclicity.

We also prove directly the isomorphism criterion needed to distinguish the fields. In a cyclic
extension $K(y)/K$ with $y^p-y=a$, choose the generator $\sigma$ satisfying
$\sigma(y)=y+1$. If $z\in K(y)$ generates the same extension and $z^p-z=b\in K$, then
$\sigma(z)-z$ is a root of $T^p-T$ and is nonzero, so it equals some
$c\in\mathbf F_p^\times$. It follows that $z-cy$ is fixed by $\sigma$ and hence belongs to $K$.
Writing $z=cy+x$ gives

$$
b=ca+(x^p-x).
$$

Conversely, such an identity makes $cy+x$ a root of $T^p-T-b$ in $K(y)$, so the two nontrivial
degree-$p$ extensions are the same. This proves, without importing the general classification,
that if the fields defined by $t^{-m}$ and $t^{-n}$ were $K$-isomorphic, there would be a
$c\in\mathbf F_p^\times$ and an $x\in K$ such that

$$
t^{-n}-ct^{-m}=x^p-x
$$

When $m\ne n$, the left side has pole order $\max\{m,n\}$, which is not
divisible by $p$; the right side, if it has a pole, has pole order divisible by $p$. This is
impossible. Hence one fixed local field of positive characteristic has infinitely many
degree-$p$ separable extensions.

This counterexample is not a failure of completeness, discreteness, or residue finiteness. It is
a wild-ramification phenomenon. The defining polynomials become arbitrarily deep in the negative
valuation direction, and there is no compact family of integral separable Eisenstein
presentations that captures them without accumulating at inseparable behavior.

### 13.6 Why the residue field must be finite

If the residue field is infinite, the valuation ring is not compact. More concretely, the
classification of Chapter 7 says that finite unramified extensions of $K$ are exactly finite
separable extensions of $k$. Thus any residue field possessing infinitely many nonisomorphic
separable extensions of a fixed degree immediately gives the same infinitude upstairs.

Even when the residue field has few finite extensions, compactness-based conclusions must not be
asserted merely from completeness. The exact hierarchy is now clear:

- completeness and discreteness give unique valuation extension, finite integral closure, and
  $[L:K]=ef$;
- finite residue field adds local compactness and compact coefficient spaces;
- characteristic zero makes every finite extension separable and yields bounded-degree
  finiteness;
- in positive characteristic, the same finiteness remains valid in the tame range, while wild
  degree-$p$ extensions already form infinite families.

## 14. From local fields back to number fields

### 14.1 A prime and its completed branches

The local theory was designed to be inserted at one prime of a global field. Let $F$ be a number
field, let $E/F$ be finite, and let $\mathfrak p$ be a nonzero prime of $\mathcal O_F$. For every
prime $\mathfrak P$ of $\mathcal O_E$ above $\mathfrak p$, completion gives a finite extension

$$
E_{\mathfrak P}/F_{\mathfrak p}.
$$

Scalar extension to the completed base remembers all branches at once:

$$
E\otimes_FF_{\mathfrak p}
\cong
\prod_{\mathfrak P\mid\mathfrak p}E_{\mathfrak P}.
$$

Its factors satisfy

$$
[E_{\mathfrak P}:F_{\mathfrak p}]
=e(\mathfrak P/\mathfrak p)f(\mathfrak P/\mathfrak p),
$$

and summing over $\mathfrak P$ recovers $[E:F]$. Thus specifying one local completion means
specifying one factor and therefore one prime above $\mathfrak p$, not the entire tensor product.

If $E/F$ is Galois, the factors are permuted transitively. The stabilizer of $\mathfrak P$ is the
decomposition group $D_{\mathfrak P}$, and Chapter 5 gives

$$
D_{\mathfrak P}\cong
\operatorname{Gal}(E_{\mathfrak P}/F_{\mathfrak p}).
$$

This is the precise passage between global Galois symmetry and a local Galois group.

### 14.2 Frobenius at an unramified prime

Write $N\mathfrak p=|\mathcal O_F/\mathfrak p|$. Suppose $E/F$ is finite Galois and
$\mathfrak P\mid\mathfrak p$. Reduction gives

$$
1\longrightarrow I_{\mathfrak P}
\longrightarrow D_{\mathfrak P}
\longrightarrow
\operatorname{Gal}(\kappa(\mathfrak P)/\kappa(\mathfrak p))
\longrightarrow1.
$$

If $\mathfrak p$ is unramified in $E$, then $I_{\mathfrak P}=1$. There is therefore a unique
element

$$
\operatorname{Frob}_{\mathfrak P}\in D_{\mathfrak P}
$$

whose residue action is

$$
x\longmapsto x^{N\mathfrak p}.
$$

This is arithmetic Frobenius. Its inverse is geometric Frobenius. If
$\mathfrak P'=\sigma\mathfrak P$, then

$$
\operatorname{Frob}_{\mathfrak P'}
=\sigma\operatorname{Frob}_{\mathfrak P}\sigma^{-1}.
$$

Consequently the conjugacy class of arithmetic Frobenius depends only on $\mathfrak p$, not on
the chosen prime above it. At a ramified prime, only a Frobenius element in the quotient
$D_{\mathfrak P}/I_{\mathfrak P}$ is canonical; its lifts differ by inertia. These are exactly
the local distinctions of Chapter 6, now expressed globally.

### 14.3 Factorization and Frobenius cycle type

Suppose $E=F(\alpha)$ and the monic minimal polynomial $f\in\mathcal O_F[T]$ of $\alpha$ has good reduction at $\mathfrak p$: its
reduction is separable and the order generated by $\alpha$ agrees with the integral closure after
localization at $\mathfrak p$. If the reduced polynomial factors as

$$
\bar f=\bar f_1\cdots\bar f_g
$$

with distinct irreducible factors of degrees $f_1,\ldots,f_g$, then $\mathfrak p$ is unramified
and has $g$ primes above it with residue degrees $f_1,\ldots,f_g$. Equivalently,

$$
E\otimes_FF_{\mathfrak p}
\cong
\prod_{i=1}^g E_i,
$$

where $E_i/F_{\mathfrak p}$ is unramified of degree $f_i$.

In a Galois closure, arithmetic Frobenius acts on the roots of $f$ with cycle lengths
$f_1,\ldots,f_g$. Indeed, reduction places the roots belonging to one irreducible factor in a
single orbit under $x\mapsto x^{N\mathfrak p}$, and the orbit length is the degree of that factor.
This familiar factorization--cycle dictionary is therefore a residue-field Frobenius statement.

The good-reduction qualification cannot be discarded. Repeated factors may signal ramification,
but they may also reflect a nonmaximal order arising from a poor generator. Intrinsic statements
must use the integral closure and its primes.

### 14.4 Weak approximation for coefficients

The reverse problem is to start with local extensions and place them inside one number field.
The input that makes this possible is weak approximation: for distinct places
$v_1,\ldots,v_r$ of a number field $F$, the diagonal image of $F$ is dense in

$$
F_{v_1}\times\cdots\times F_{v_r}.
$$

Applied coordinate by coordinate, it says that a monic polynomial over each $F_{v_i}$ can be
approximated simultaneously by one monic polynomial over $F$. At nonarchimedean places this is a
simultaneous congruence statement; denominators may first be cleared and the Chinese remainder
theorem applied to sufficiently high powers of the distinct prime ideals. Archimedean places use
ordinary real or complex approximation, though only nonarchimedean places are needed below.

Krasner's lemma tells us what “sufficiently close” buys. If a local separable polynomial has a
factor generating a desired extension, nearby global coefficients preserve that factor and its
generated local field. If the local polynomial has several distinct factors, Hensel stability
preserves the full product decomposition.

### 14.5 Prescribing finitely many local completions

**Theorem 14.1 (prescribed nonarchimedean completions).** Let $F$ be a number field, let
$v_1,\ldots,v_r$ be distinct nonarchimedean places with $r\geq1$, and for each $i$ let $L_i/F_{v_i}$ be a finite
extension of degree $d_i$. Put $n=\max_i d_i$. If $n>1$, there exists a number field extension
$E/F$ of degree $n$ and, for each $i$, a place $w_i$ of $E$ above $v_i$ such that

$$
E_{w_i}\cong L_i
$$

as extensions of $F_{v_i}$. If $n=1$, one may take $E=F$.

**Proof strategy.** Represent each desired local extension by one factor of a separable
degree-$n$ polynomial. Use an auxiliary prime to impose Eisenstein irreducibility globally.
Weak approximation chooses one global polynomial satisfying all these open local conditions.

**Proof.** Every $L_i/F_{v_i}$ is separable because $F_{v_i}$ has characteristic zero. Choose a
primitive element with monic minimal polynomial $h_i$ of degree $d_i$. If $d_i<n$, choose
$n-d_i$ distinct elements of $F_{v_i}$, avoiding the roots of $h_i$, and let $q_i$ be the product
of the corresponding distinct linear factors. Then

$$
g_i=h_iq_i
$$

is monic, separable, and has degree $n$. One of the field factors of
$F_{v_i}[T]/(g_i)$ is exactly $L_i$.

Choose one additional nonarchimedean place $v_0$, distinct from all the $v_i$, and a monic
Eisenstein polynomial $g_0\in F_{v_0}[T]$ of degree $n$. Being Eisenstein is an open condition on
its nonleading coefficients: sufficiently small perturbations remain in the maximal ideal, and
the constant coefficient remains outside its square.

At every $v_i$, Proposition 12.2 and Corollary 12.3 provide an open coefficient neighborhood of
$g_i$ in which the factor corresponding to $h_i$ still generates $L_i$. At $v_0$, choose an open
neighborhood consisting of Eisenstein polynomials. Weak approximation, applied to the $n$
nonleading coefficients, produces a monic $g\in F[T]$ lying in all these neighborhoods.

The polynomial $g$ is Eisenstein over $F_{v_0}$, hence irreducible over $F_{v_0}$ and therefore
over $F$. Put $E=F[T]/(g)$. At $v_i$, the algebra

$$
E\otimes_FF_{v_i}\cong F_{v_i}[T]/(g)
$$

has a field factor isomorphic to $L_i$. By the completed product decomposition, that factor is
$E_{w_i}$ for a place $w_i$ above $v_i$. This proves the theorem. $\square$

The degree $n=\max d_i$ is possible because the unused degree at a place can be filled by
distinct linear factors. More generally, one can prescribe an entire finite separable
$F_{v_i}$-algebra of total dimension $n$ at each selected place, and the same proof realizes all
of those local product decompositions simultaneously.

### 14.6 What the approximation theorem does not prescribe

Theorem 14.1 is strong but deliberately local. It guarantees chosen completions at finitely many
places. It does not make $E/F$ Galois, prescribe its global Galois group, control ramification at
every other prime, or force uniqueness of the global field. Those are different global problems
and can carry genuine compatibility obstructions.

The theorem also explains why Krasner's strict inequality matters in arithmetic constructions.
Weak approximation never needs to reproduce a local polynomial coefficient by coefficient. It
only needs to enter an open stability neighborhood. Once inside, the root may move, but the
completed field it generates does not.

The two applications in this chapter run in opposite directions. Completing a global extension
at a prime extracts decomposition, inertia, residue degree, and Frobenius. Approximation starts
with finitely many complete local extensions and realizes them as selected branches of one
global extension. Together they show that the local theory is neither isolated from global
arithmetic nor merely a shadow of it.

## 15. The local extension as a coherent whole

### 15.1 The structural dictionary

We can now move among the field, ring, residue, and group descriptions without returning to raw valuation arguments each time. For a finite extension $L/K$ of complete discretely valued fields,

$$
B=\overline A^{\,L}
$$

is a complete DVR finite free of rank $[L:K]$ over $A$. The normalized valuations satisfy

$$
v_L|_K=e\,v_K,\qquad \mathfrak m_KB=\mathfrak m_L^e,
$$

and the residue extension has degree $f$. One block of base precision splits into $e$ valuation layers, each of residue dimension $f$, giving

$$
[L:K]=ef.
$$

In a tower, both $e$ and $f$ multiply. Trace and norm transfer additive and multiplicative information down the tower, with

$$
v_K(Nx)=f\,v_L(x),
$$

and with residue shadows

$$
\overline{\operatorname{Tr}(x)}=e\operatorname{Tr}_{l/k}(\bar x),\qquad
\overline{N(u)}=N_{l/k}(\bar u)^e.
$$

These formulas remain valid without separability; embedding formulas and nondegeneracy of trace do not.

### 15.2 The separability map

The theory has several points at which a separability hypothesis enters, and they should now be visible rather than mysterious.

- The valuation extension, finite freeness, and $[L:K]=ef$ require no separability.
- Formulas for trace and norm as sums and products over embeddings require $L/K$ separable.
- Galois means normal and separable; only then does the automorphism group have order $[L:K]$.
- The exact quotient $G/I\cong\operatorname{Gal}(l/k)$ with order $f$ requires the residue extension to be separable.
- Unramified means $e=1$ together with separable residue extension.
- The decomposition into an unramified extension followed by a totally ramified extension requires $l/k$ separable; it is automatic when $k$ is perfect.
- Frobenius is canonical when the residue field is finite, hence perfect.

This list also distinguishes finiteness from perfection. Finiteness of the residue field gives compactness, cyclic residue multiplicative groups, surjective residue norms, and a canonical Frobenius generator. Perfection alone gives separability of finite residue extensions but none of those finiteness conclusions.

### 15.3 The Galois picture

For a finite Galois extension with separable residue extension, uniqueness of the valuation makes the decomposition group the whole group, and reduction gives

$$
1\longrightarrow I\longrightarrow G
\longrightarrow\operatorname{Gal}(l/k)\longrightarrow1.
$$

The fixed field $L^I$ is the maximal unramified subextension. Thus the diagram

$$
\begin{array}{ccc}
G & \longrightarrow & \operatorname{Gal}(l/k)\\
\cup && \\
I &&
\end{array}
$$

has a field-theoretic counterpart

$$
K\subseteq L^I\subseteq L.
$$

When $k=\mathbf F_q$, arithmetic Frobenius $x\mapsto x^q$ generates the quotient. In a ramified extension it determines a coset modulo inertia; in an unramified extension it determines an actual generator. Geometric Frobenius is always the inverse convention.

### 15.4 The multiplicative picture

Choosing a uniformizer decomposes

$$
L^\times\cong\mathbf Z\times U_L^0,
$$

and the unit filtration resolves the second factor into

$$
U_L^0/U_L^1\cong l^\times,\qquad
U_L^n/U_L^{n+1}\cong l^+\quad(n\geq1).
$$

Norm acts on the valuation coordinate by multiplication by $f$, on the residue-unit coordinate by $N_{l/k}^e$, and infinitesimally through trace. This three-part description is the reusable language promised at the beginning:

$$
\text{valuation}\quad|\quad\text{residue unit}\quad|\quad\text{principal units}.
$$

Unramified extensions are visible mainly in the first two columns: their norms multiply valuation by $f$ and use the residue norm. Totally ramified extensions are visible mainly in the last two: their uniformizers control value, their residue norms are $e$th powers, and their principal-unit behavior distinguishes tame from wild ramification.

### 15.5 Conclusion

A finite extension of a complete discretely valued field is not an arbitrary enlargement. It is a controlled redistribution of dimension between two discrete measurements, value and residue, bound together by the exact equality $[L:K]=ef$. Completeness ensures that there is one valuation, one integral closure, and one coherent topology upstairs. Finite freeness turns valuation into linear algebra; trace and norm turn linear algebra back into arithmetic.

When separability is present, automorphisms expose the same structure dynamically. Inertia is precisely what reduction cannot see, the unramified quotient is precisely what residue-field automorphisms can see, and finite residue fields select Frobenius as a canonical direction through that quotient. Eisenstein polynomials then give coordinates for the totally ramified direction, while the unit filtration records increasingly fine motion near the identity.

The resulting picture is both rigid and incomplete in the right way. It explains where ramification lives and supplies the language for measuring its first effects, while leaving its higher jumps untouched. Those deeper layers will refine inertia rather than replace the structure established here: every later ramification group, conductor, different, and discriminant calculation will rest on the valuation, residue, norm, trace, Frobenius, and unit coordinates now assembled into a single local theory.

Krasner's lemma adds a final form of rigidity: near a separable defining polynomial, the field
generated by a root is locally constant. Over a characteristic-zero local field, compactness
turns this stability into finiteness of extensions of bounded degree. Equal characteristic
reveals the exact boundary rather than an exception to be ignored: tame extensions retain the
finiteness property, while wild Artin--Schreier extensions already occur in infinite families of
one fixed degree.

Finally, the local structure returns to global arithmetic. At an unramified prime, residue
Frobenius lifts to the decomposition group and determines a global conjugacy class. In the
opposite direction, weak approximation and Krasner stability realize finitely many prescribed
nonarchimedean completions as branches of one number field. Local fields therefore provide both
the microscope for a chosen prime and a collection of exact conditions from which global fields
can be built.
