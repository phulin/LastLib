# Hilbert--Blumenthal Moduli and Two-Prime Level Covers

## Contents

- [1. The moduli problem behind a two-prime argument](#1-the-moduli-problem-behind-a-two-prime-argument)
  - [1.1 Why one abelian variety must carry several kinds of data](#11-why-one-abelian-variety-must-carry-several-kinds-of-data)
  - [1.2 Standing arithmetic data](#12-standing-arithmetic-data)
  - [1.3 Good primes and the scope of the construction](#13-good-primes-and-the-scope-of-the-construction)
- [2. Real multiplication and the Hilbert determinant condition](#2-real-multiplication-and-the-hilbert-determinant-condition)
  - [2.1 Real multiplication in families](#21-real-multiplication-in-families)
  - [2.2 The determinant polynomial](#22-the-determinant-polynomial)
  - [2.3 Rank one and determinant at unramified primes](#23-rank-one-and-determinant-at-unramified-primes)
  - [2.4 Why ramified primes are excluded here](#24-why-ramified-primes-are-excluded-here)
- [3. Polarization modules and their positive cone](#3-polarization-modules-and-their-positive-cone)
  - [3.1 Why a single principal polarization is the wrong datum](#31-why-a-single-principal-polarization-is-the-wrong-datum)
  - [3.2 The ordered polarization module](#32-the-ordered-polarization-module)
  - [3.3 The tensor polarization and its consequences](#33-the-tensor-polarization-and-its-consequences)
  - [3.4 Isomorphisms and the unit issue](#34-isomorphisms-and-the-unit-issue)
- [4. Auxiliary neat level and the fine Hilbert scheme](#4-auxiliary-neat-level-and-the-fine-hilbert-scheme)
  - [4.1 The lattice model](#41-the-lattice-model)
  - [4.2 Prime-to-the-base level](#42-prime-to-the-base-level)
  - [4.3 Neatness kills automorphisms](#43-neatness-kills-automorphisms)
  - [4.4 Representability and smoothness](#44-representability-and-smoothness)
- [5. The intrinsic determinant pairing on prime torsion](#5-the-intrinsic-determinant-pairing-on-prime-torsion)
  - [5.1 From Weil pairings to an $\mathcal O_F$-balanced form](#51-from-weil-pairings-to-an-mathcal-o_f-balanced-form)
  - [5.2 The coefficient line and the different](#52-the-coefficient-line-and-the-different)
  - [5.3 Perfectness and the determinant isomorphism](#53-perfectness-and-the-determinant-isomorphism)
  - [5.4 The cyclotomic determinant](#54-the-cyclotomic-determinant)
- [6. Paired frames at one prime](#6-paired-frames-at-one-prime)
  - [6.1 Paired local systems](#61-paired-local-systems)
  - [6.2 The frame functor](#62-the-frame-functor)
  - [6.3 The special linear torsor](#63-the-special-linear-torsor)
  - [6.4 Forgetful maps and universal objects](#64-forgetful-maps-and-universal-objects)
- [7. The simultaneous two-prime cover](#7-the-simultaneous-two-prime-cover)
  - [7.1 Independent prime ideals](#71-independent-prime-ideals)
  - [7.2 The fiber product construction](#72-the-fiber-product-construction)
  - [7.3 Degree, deck group, and base change](#73-degree-deck-group-and-base-change)
  - [7.4 Why paired means paired separately](#74-why-paired-means-paired-separately)
- [8. Twists and prescribed residual representations](#8-twists-and-prescribed-residual-representations)
  - [8.1 Descent data as a torsor](#81-descent-data-as-a-torsor)
  - [8.2 Twisting the frame cover](#82-twisting-the-frame-cover)
  - [8.3 The determinant obstruction](#83-the-determinant-obstruction)
  - [8.4 Moduli interpretation of the twist](#84-moduli-interpretation-of-the-twist)
- [9. Complex uniformization and components](#9-complex-uniformization-and-components)
  - [9.1 The symmetric domain](#91-the-symmetric-domain)
  - [9.2 The determinant component map](#92-the-determinant-component-map)
  - [9.3 Connected components of a fixed polarization type](#93-connected-components-of-a-fixed-polarization-type)
  - [9.4 Algebraic and geometric components](#94-algebraic-and-geometric-components)
- [10. Geometric monodromy of a prime-level frame cover](#10-geometric-monodromy-of-a-prime-level-frame-cover)
  - [10.1 Monodromy as reduction of an arithmetic group](#101-monodromy-as-reduction-of-an-arithmetic-group)
  - [10.2 A congruence-surjectivity lemma](#102-a-congruence-surjectivity-lemma)
  - [10.3 Full special-linear monodromy](#103-full-special-linear-monodromy)
  - [10.4 Connectedness of the frame cover](#104-connectedness-of-the-frame-cover)
- [11. Product monodromy at two primes](#11-product-monodromy-at-two-primes)
  - [11.1 Why two surjections are not enough](#111-why-two-surjections-are-not-enough)
  - [11.2 Simultaneous congruence approximation](#112-simultaneous-congruence-approximation)
  - [11.3 The product theorem](#113-the-product-theorem)
  - [11.4 Twists preserve geometric monodromy](#114-twists-preserve-geometric-monodromy)
- [12. The complete two-prime moduli theorem](#12-the-complete-two-prime-moduli-theorem)
  - [12.1 Statement with all hypotheses](#121-statement-with-all-hypotheses)
  - [12.2 Proof of representability and the covering assertions](#122-proof-of-representability-and-the-covering-assertions)
  - [12.3 Proof of components and monodromy](#123-proof-of-components-and-monodromy)
  - [12.4 Variants and sharp boundaries](#124-variants-and-sharp-boundaries)
- [13. A working dictionary for later arithmetic specialization](#13-a-working-dictionary-for-later-arithmetic-specialization)
  - [13.1 Points and Galois representations](#131-points-and-galois-representations)
  - [13.2 Changing auxiliary level and polarization class](#132-changing-auxiliary-level-and-polarization-class)
  - [13.3 What is geometric and what is arithmetic](#133-what-is-geometric-and-what-is-arithmetic)
  - [13.4 Conclusion](#134-conclusion)

## 1. The moduli problem behind a two-prime argument

### 1.1 Why one abelian variety must carry several kinds of data

Hilbert--Blumenthal abelian varieties are the meeting place of two-dimensional Galois representations and higher-dimensional abelian geometry. If $F$ is totally real of degree $d$, an abelian variety of dimension $d$ with real multiplication by $\mathcal O_F$ has, at every prime ideal $\mathfrak p$ of $F$ away from the residue characteristic, a two-dimensional $k_{\mathfrak p}$-module of $\mathfrak p$-torsion. Thus one abelian variety can carry a representation at one prime and a second, arithmetically unrelated representation at another.

That slogan conceals four compatibility problems. First, an arbitrary $\mathcal O_F$-action may put the wrong embeddings on the tangent space; the Hilbert determinant condition selects multiplicity one at every real embedding. Second, polarizations compatible with real multiplication naturally form an invertible $\mathcal O_F$-module, so choosing a single principal polarization would discard legitimate components. Third, a basis of $A[\mathfrak p]$ cannot be prescribed independently of the Weil pairing: its determinant is forced by the cyclotomic character. Fourth, the two separate level covers must have product, rather than diagonally correlated, geometric monodromy.

This book resolves those four problems in that order. The result is a fine smooth Hilbert moduli scheme with an auxiliary rigidifying level, together with a finite étale two-prime cover parametrizing paired torsion frames. Twisting that cover replaces the standard frames by prescribed rank-two local systems. A component calculation and a congruence argument then prove full product monodromy and geometric connectedness over each chosen geometric component.

Local integral conditions such as ordinary, nonordinary finite-flat, or semistable reduction require separate deformation and local-model arguments. They are not part of the present construction. Here all displayed torsion primes and all auxiliary levels are invertible on the base, and the coefficient field is unramified there. This clean setting is exactly what permits frames to form finite étale covers.

### 1.2 Standing arithmetic data

Fix throughout:

- a totally real field $F$ of degree $d$ and ring of integers $\mathcal O_F$;
- its different $\mathfrak d_F$ and discriminant $D_F$;
- an invertible fractional $\mathcal O_F$-ideal $\mathfrak c$, equipped with the cone $\mathfrak c^+$ of elements positive at every real embedding;
- an auxiliary principal level ideal $\mathfrak n=N\mathcal O_F$ for an integer $N\geq3$;
- two distinct prime ideals $\mathfrak p$ and $\mathfrak q$ of $\mathcal O_F$, of residue characteristics $p$ and $q$.

More general neat ideals work as well, but principal integer level keeps the rigidity convention unambiguous and is sufficient for the two-prime construction.

Choose a finite set $\Sigma$ of rational primes containing those below the different of $F$, the numerator and denominator ideals of $\mathfrak c$, and $\mathfrak n$. Assume that the distinct primes $p$ and $q$ lie outside $\Sigma$. Put $M_\Sigma=\prod_{\ell\in\Sigma}\ell$. Thus the working base is

$$
B=\operatorname{Spec}\mathbf Z[1/M_\Sigma pq].
$$

Write

$$
k_{\mathfrak p}=\mathcal O_F/\mathfrak p,
\qquad
k_{\mathfrak q}=\mathcal O_F/\mathfrak q.
$$

These are finite fields, not necessarily prime fields. The two-dimensionality of $A[\mathfrak p]$ is over $k_{\mathfrak p}$; its rank as a finite étale group scheme is $|k_{\mathfrak p}|^2$.

### 1.3 Good primes and the scope of the construction

Three distinct meanings of “good” occur and must not be conflated. A prime is good for the coefficient algebra if $F/\mathbf Q$ is unramified there, so $\mathcal O_F\otimes\mathbf Z_p$ is étale. It is good for the polarization if the local tensor polarization is perfect. It is good for level if the level order is invertible on the base. Our set $\Sigma$ is chosen so all three properties hold outside it.

At such a prime the determinant condition is equivalent to the Rapoport rank-one condition on the Lie algebra, the polarization pairing on Tate modules is unimodular, and torsion of order prime to the residue characteristic is finite étale. The polarized Serre--Tate and Hodge-filtration deformation theorem then proves smoothness of relative dimension $d$ without a ramified local model. This use of Serre--Tate theory is unrelated to ordinarity: unrestricted polarized deformations of a $p$-divisible group are controlled by lifts of its Hodge filtration, whether or not its special fiber is ordinary.

The exclusions are mathematical, not cosmetic. At a ramified prime, the correct characteristic polynomial on $\operatorname{Lie}(A)$ need not make it locally free of rank one over $\mathcal O_F\otimes\mathcal O_S$. If the polarization type is not prime to the residue characteristic, the induced pairing may fail to identify torsion with its dual. If a level prime equals the residue characteristic, geometric frames cease to describe the finite flat group scheme. Every theorem below records the good-prime hypotheses at the point where they are used.

The case $F=\mathbf Q$ is a useful calibration. Then $d=1$, $\mathfrak d_F=\mathbf Z$, a $\mathbf Z$-polarized Hilbert--Blumenthal abelian scheme is an elliptic scheme, and the determinant condition says only that $\operatorname{Lie}(A)$ has rank one. At a prime $p$, the coefficient line is $\mathbf F_p(1)$ and a paired frame is a symplectic basis of $E[p]$. The construction below therefore recovers the familiar full-level cover of a modular curve. Every extra ideal and component in the general theory measures something that disappears for $F=\mathbf Q$.

## 2. Real multiplication and the Hilbert determinant condition

### 2.1 Real multiplication in families

Let $S$ be a $B$-scheme. A **real-multiplication abelian scheme** over $S$ is a pair $(A,\iota)$ in which $A/S$ is an abelian scheme of relative dimension $d$ and

$$
\iota:\mathcal O_F\longrightarrow\operatorname{End}_S(A)
$$

is an injective ring homomorphism. Since a nonzero element of $\mathcal O_F$ acts as an isogeny on every characteristic-zero fiber, injectivity could be checked there when $S$ is flat over $B$. We retain it in the definition because the moduli problem is meant to make sense after arbitrary base change.

The action differentiates to an action on the locally free sheaf $\operatorname{Lie}(A/S)$. Its rank as an $\mathcal O_S$-module is $d$, but that equality alone does not determine how the $d$ embeddings of $F$ occur. For instance, over a splitting field an action could put one embedding twice on the tangent space and omit another. Such an object has the correct abelian dimension but not Hilbert--Blumenthal Hodge type.

### 2.2 The determinant polynomial

For $a\in\mathcal O_F$ define

$$
P_a(T)=\operatorname N_{F/\mathbf Q}(T-a)
=\prod_{\tau:F\hookrightarrow\overline{\mathbf Q}}(T-\tau(a))
\in\mathbf Z[T].
$$

Choose a $\mathbf Z$-basis $a_1,\ldots,a_d$ of $\mathcal O_F$. The **Hilbert determinant condition** is the universal polynomial-law identity

$$
\det\!\left(T-\sum_iX_i\iota(a_i)
\mathrel{\Big|}\operatorname{Lie}(A/S)\right)
=\operatorname N_{F/\mathbf Q}\!\left(T-\sum_iX_i a_i\right)
\quad\text{in }\mathcal O_S[X_1,\ldots,X_d,T].
\tag{2.1}
$$

It is independent of the chosen basis, since a change of basis merely makes an invertible integral substitution in the variables. Specializing the $X_i$ gives

$$
\det\bigl(T-\iota(a)\mid\operatorname{Lie}(A/S)\bigr)=P_a(T)
$$

for every $a\in\mathcal O_F$, and more generally for every element after arbitrary scalar extension. The universal formulation matters in small characteristic: equality on the integral points alone need not determine a polynomial law over a finite residue field. Equation (2.1) is a finite list of coefficient equalities, commutes with arbitrary base change, and cuts out the required closed determinant locus.

### 2.3 Rank one and determinant at unramified primes

The determinant condition becomes especially transparent on $B$.

**Proposition 2.1.** Let $S$ be a $\mathbf Z[1/D_F]$-scheme and let $M$ be a locally free $\mathcal O_S$-module of rank $d$ with an $\mathcal O_F$-action. Then the following are equivalent:

1. $M$ is locally free of rank one over $\mathcal O_F\otimes_{\mathbf Z}\mathcal O_S$;
2. the action on $M$ satisfies the universal determinant identity (2.1).

**Proof.** The assertion is étale-local on $S$. Because $D_F$ is invertible, the finite algebra $\mathcal O_F\otimes\mathcal O_S$ is étale-locally isomorphic to $\mathcal O_S^d$. Let $e_1,\ldots,e_d$ be its primitive idempotents and write $M=\bigoplus M_i$, where $M_i=e_iM$ has rank $r_i$. An element $a$ acts on $M_i$ by the corresponding embedding value $a_i$, so

$$
\det(T-a\mid M)=\prod_i(T-a_i)^{r_i}.
$$

If $M$ has rank one over the product algebra, every $r_i=1$, proving the determinant identity. Conversely, the universal identity may be specialized after the étale base change to the primitive idempotent $e_i$. Its characteristic polynomial on $M$ is

$$
(T-1)^{r_i}T^{d-r_i},
$$

whereas its norm polynomial on the regular rank-$d$ algebra is $(T-1)T^{d-1}$. Equality forces $r_i=1$. Doing this for every $i$ shows that $M$ is rank one over the product algebra, and descent gives the claimed local freeness. This idempotent argument remains valid over arbitrarily small residue fields; it does not require one element whose embedding values are all distinct. $\square$

Applied to $M=\operatorname{Lie}(A/S)$, this says that our Hilbert determinant condition is exactly the rank-one Hodge condition on the good base.

For a concrete quadratic example, let $F=\mathbf Q(\sqrt5)$ and take a rational prime $\ell\nmid5$. If $\ell$ splits, then

$$
\mathcal O_F\otimes\mathbf F_\ell\simeq\mathbf F_\ell\times\mathbf F_\ell,
$$

and the Lie bundle is the sum of two lines, one for each idempotent. If $\ell$ is inert, the coefficient algebra is $\mathbf F_{\ell^2}$; after an étale quadratic extension of the base it again splits into two embedding lines. In both cases Proposition 2.1 says exactly “one copy of each embedding.” At $\ell=5$ the two roots coalesce and the algebra is ramified, illustrating why the idempotent proof cannot be continued across the discriminant.

### 2.4 Why ramified primes are excluded here

Proposition 2.1 fails if $D_F$ is not invertible. The algebra $\mathcal O_F\otimes k$ can contain nilpotents, so it has too few idempotents to recover the module from eigenvalue multiplicities. Two modules over a ramified local algebra can have identical characteristic polynomials for every element while only one is free. Thus the determinant condition by itself does not guarantee the flat local model one wants.

There are integral Hilbert moduli problems at ramified primes, obtained by imposing a rank-one condition where meaningful or by using a polarization-module condition with a refined local model. Their generic fibers agree with ours, but their special fibers can differ. Since the purpose here is a finite étale two-prime cover and its monodromy, working over $B$ isolates the exact geometry needed and avoids claiming a false universal smoothness theorem.

## 3. Polarization modules and their positive cone

### 3.1 Why a single principal polarization is the wrong datum

For an $\mathcal O_F$-abelian scheme $(A,\iota)$, let

$$
\mathcal P(A)=
\operatorname{Hom}_{\mathcal O_F}^{\mathrm{sym}}(A,A^\vee).
$$

Here $\mathcal O_F$ acts on $A^\vee$ by the dual action, and “symmetric” means equal to the dual morphism under biduality. The polarizations in $\mathcal P(A)$ form a positive cone $\mathcal P(A)^+$. On a geometric Hilbert--Blumenthal fiber this is an invertible $\mathcal O_F$-module with its totally positive cone.

If one selected only a principal polarization, ideal-class operations would move objects out of the moduli problem, and some legitimate Hilbert components would disappear. A polarization module retains the whole family of compatible polarizations and records its ideal class. It also produces the correct coefficient line for torsion pairings; that line is what prevents a determinant error later.

### 3.2 The ordered polarization module

A **$\mathfrak c$-polarization** on $(A,\iota)$ is an isomorphism of invertible ordered $\mathcal O_F$-modules

$$
\lambda:(\mathfrak c,\mathfrak c^+)
\xrightarrow{\sim}(\mathcal P(A),\mathcal P(A)^+)
\tag{3.1}
$$

such that the induced morphism

$$
\Lambda_\lambda:A\otimes_{\mathcal O_F}\mathfrak c
\longrightarrow A^\vee,
\qquad x\otimes c\longmapsto\lambda(c)(x),
\tag{3.2}
$$

is an isomorphism. The tensor construction in (3.2) is the Serre tensor construction for the finite projective module $\mathfrak c$. Condition (3.2) is the integral perfectness condition. Merely requiring every positive $c$ to give an isogeny would not control its degree uniformly and would be too weak for the determinant pairing.

For each $c\in\mathfrak c^+$, $\lambda(c)$ is a polarization. Conversely, (3.1) is recovered from all these compatible polarizations, not from one of them alone. Positivity is an actual part of the datum: replacing $\mathfrak c^+$ by its negative changes which symmetric maps are ample.

Suppose $F$ has a nontrivial narrow ideal class represented by $\mathfrak c$. A complex Hilbert--Blumenthal torus can have polarization module isomorphic to $\mathfrak c$ even though no element of that module induces a principal polarization. Indeed a principal polarization would be a totally positive generator of the ordered ideal, forcing its narrow class to be trivial. The $\mathfrak c$-polarized moduli space is nevertheless nonempty: its defining tensor map uses the whole projective module. This example is precisely what a principal-polarization-only definition would erase.

### 3.3 The tensor polarization and its consequences

The isomorphism (3.2) implies three facts used repeatedly.

**Proposition 3.1.** Let $(A,\iota,\lambda)$ be $\mathfrak c$-polarized.

1. The Rosati adjoint of $\iota(a)$ is $\iota(a)$ for every $a\in F$.
2. At every ideal $\mathfrak a$ invertible on the base, (3.2) identifies the $\mathfrak a$-primary torsion of $A^\vee$ with $A[\mathfrak a]\otimes\mathfrak c$.
3. The resulting alternating pairing on $A[\mathfrak a]$ is perfect after its natural coefficient line is retained.

**Proof.** The $\mathcal O_F$-linearity of each $\lambda(c)$ says

$$
\lambda(c)\iota(a)=\iota(a)^\vee\lambda(c).
$$

After inverting one nonzero $c$, this is precisely self-adjointness for the Rosati involution, proving (1). Tensoring the isomorphism (3.2) with the finite locally free kernel of $\mathfrak a$ commutes with base change and gives (2). The ordinary Weil pairing between $A[\mathfrak a]$ and $A^\vee[\mathfrak a]$ is perfect. Substitution of the isomorphism in (2), followed by tensor--Hom adjunction, gives (3). Section 5 makes its coefficient line explicit. $\square$

### 3.4 Isomorphisms and the unit issue

An isomorphism

$$
f:(A,\iota,\lambda)\longrightarrow(A',\iota',\lambda')
$$

must satisfy

$$
f\iota(a)=\iota'(a)f,
\qquad
f^\vee\lambda'(c)f=\lambda(c)
\tag{3.3}
$$

for all $a\in\mathcal O_F$ and $c\in\mathfrak c$. Equality in (3.3), rather than equality up to a totally positive unit, is our convention. If polarizations were identified up to a subgroup $U$ of $\mathcal O_F^{\times,+}$, the moduli problem and its component set would be a quotient by $U$ and stabilizers could reappear.

Multiplication by a unit $u$ on $A$ acts on a symmetric homomorphism by $\lambda(c)\mapsto u^2\lambda(c)$ because $u$ is Rosati self-adjoint. Thus it preserves the ordered map (3.1) only when $u^2=1$ and it preserves the auxiliary level. In a totally real field the torsion units are $\{\pm1\}$; full level at least three excludes $-1$. This is the elementary heart of the fine-moduli argument.

## 4. Auxiliary neat level and the fine Hilbert scheme

### 4.1 The lattice model

Level structures compare the torsion of $A$ with a fixed integral PEL lattice. Choose a projective rank-two $\mathcal O_F$-module $L$ equipped with a perfect alternating $\mathcal O_F$-balanced form

$$
\psi:L\times L\longrightarrow\mathfrak c^\vee,
\qquad
\mathfrak c^\vee=\operatorname{Hom}_{\mathbf Z}(\mathfrak c,\mathbf Z)
=\mathfrak d_F^{-1}\mathfrak c^{-1}.
\tag{4.1}
$$

For example one may take $L=\mathcal O_F\oplus\mathfrak c^\vee$ and $\psi((x,y),(x',y'))=xy'-x'y$. This is perfect as an alternating form with values in the invertible line $\mathfrak c^\vee$. For $c_0\in\mathfrak c^+$, the scalar form $\operatorname{Tr}_{F/\mathbf Q}(c_0\psi)$ is integral; its elementary divisors record the generally nonprincipal polarization $\lambda(c_0)$. It need not itself be unimodular unless the chosen polarization is principal. Different choices in the same genus give canonically related prime-to-$\Sigma$ moduli problems; fixing one prevents hidden changes of determinant normalization.

Let $G$ be the group of $\mathcal O_F$-linear symplectic similitudes of $(L,\psi)$. Since the module has rank two, the multiplier of a matrix equals its determinant locally. This rank-two identity is why a pairing condition is exactly a determinant condition, not an additional unrelated tensor.

### 4.2 Prime-to-the-base level

Let $K(\mathfrak n)\subset G(\widehat{\mathbf Z})$ be the principal congruence subgroup acting trivially on $L/\mathfrak nL$. Over a base on which $\mathfrak n$ is invertible, a full paired $\mathfrak n$-level structure on $(A,\iota,\lambda)$ consists of an $\mathcal O_F$-linear isomorphism

$$
\eta_{\mathfrak n}:L/\mathfrak nL\xrightarrow{\sim}A[\mathfrak n]
\tag{4.2}
$$

and an $\mathcal O_F/\mathfrak n$-linear isomorphism of value lines

$$
\delta_{\mathfrak n}:
(\mathfrak c^\vee/\mathfrak n\mathfrak c^\vee)_S
\xrightarrow{\sim}
(\mathfrak c^\vee/\mathfrak n\mathfrak c^\vee)_S(1)
\tag{4.3}
$$

such that

$$
\bigl\langle\eta_{\mathfrak n}x,\eta_{\mathfrak n}y\bigr\rangle_{\mathfrak n}
=\delta_{\mathfrak n}\bigl(\psi(x,y)\bigr).
\tag{4.4}
$$

The notation $\eta_{\mathfrak n}$ below includes the orientation $\delta_{\mathfrak n}$. The sheaf of choices of (4.3) is the primitive cyclotomic torsor; it does not amount to choosing one primitive root of unity globally on $B$. Equivalently, one can use the appropriate principal-level orbit of a prime-to-$\Sigma$ adelic trivialization. Keeping (4.3) visible prevents a constant determinant line from being silently identified with its Tate twist.

### 4.3 Neatness kills automorphisms

A compact open subgroup $K\subset G(\mathbf A_f)$ is **neat** if, for every $g\in G(\mathbf A_f)$, the subgroup of $\overline{\mathbf Q}^{\times}$ generated by the eigenvalues of $gKg^{-1}\cap G(\mathbf Q)$ is torsion-free. The property relevant to moduli is immediate: a finite-order automorphism preserving a $K$-level structure must be the identity.

**Proposition 4.1.** Principal level $N\geq3$ is neat enough for the Hilbert moduli problem above, and every object with that level has trivial automorphism group.

**Proof.** Let $f$ be an automorphism preserving $\mathcal O_F$, $\lambda$, and the full level. A polarization makes its automorphism group finite, and the action of this group on a prime-to-characteristic Tate module is faithful. Preservation of full level says that $f$ acts as the identity modulo $N$.

We use the integral congruence lemma: if every prime dividing $N$ is invertible in the ground field, the kernel of reduction on the corresponding prime-to-characteristic Tate lattice,

$$
\operatorname{GL}_r\!\left(\prod_{v\mid N}\mathbf Z_v\right)
\longrightarrow
\operatorname{GL}_r(\mathbf Z/N\mathbf Z)
$$

is torsion-free for $N\geq3$. For completeness, replace a nontrivial torsion element by a power $u$ of prime order $\ell$ and work in one $v$-adic factor, writing $u=1+NA$. If a prime $r\mid N$ differs from $\ell$, the binomial identity $u^\ell=1$, divided by $N$ and reduced modulo $r$, gives $A\equiv0\pmod r$. Repeating after writing $A=rA_1$ makes $A$ divisible by every power of $r$, a contradiction. It remains that $N$ is a power of $\ell$. After division by $\ell N$, the same identity reduces to $A\equiv0\pmod\ell$ when $\ell$ is odd, and also when $\ell=2$ provided $4\mid N$; iteration gives the same contradiction. If $N\equiv2\pmod4$ and $N>2$, it has an odd divisor, which handles $\ell=2$ by the first case. This is exactly why level two is exceptional. Apply the lemma to the Tate action of $f$. The action is the identity, and faithfulness gives $f=1$. $\square$

### 4.4 Representability and smoothness

Let $H_{\mathfrak c,\mathfrak n}$ be the functor assigning to a $B$-scheme $S$ the set of isomorphism classes of quadruples

$$
(A,\iota,\lambda,\eta_{\mathfrak n})
\tag{4.5}
$$

satisfying the determinant condition, $\mathfrak c$-polarization condition, and full auxiliary level.

**Theorem 4.2.** The functor $H_{\mathfrak c,\mathfrak n}$ is represented by a smooth quasi-projective $B$-scheme of relative dimension $d$. It carries a universal quadruple.

**Proof.** Faithfully flat descent applies separately to the abelian scheme, the $\mathcal O_F$-action, the polarization homomorphisms, and the two finite level isomorphisms (4.2)--(4.3). The determinant and adjoint identities are closed equations, while positivity and ampleness descend. Thus the moduli groupoid is a stack.

The PEL stack theorem of Book 35a, Section 10.5, applies to precisely these data. Choose a positive $c\in\mathfrak c^+$ and a sufficiently high power of an ample bundle inducing a multiple of $\lambda(c)$. Projective embeddings place the objects in the relevant Hilbert parameter scheme; the group law, zero section, $\mathcal O_F$-action, symmetry, tensor-polarization isomorphism, determinant equations, and level structures define the stated locally closed PEL locus. That theorem gives an algebraic finite-presentation stack with finite separated diagonal and a quasi-projective fine scheme when the level is neat. Proposition 4.1 makes the inertia trivial, so the stack is represented by a quasi-projective scheme and its tautological object is the universal quadruple. This invokes the earlier PEL representability theorem rather than treating a free quotient of one chosen Hilbert presentation as automatic.

It remains to prove smoothness. It is enough to check closed geometric points, because the nonsmooth locus of this finite-presentation morphism is closed and the base is Jacobson. Let $s$ have residue characteristic $\ell\notin\Sigma$. Book 55, Theorems 6.1 and 7.1, replaces deformations of the abelian scheme by deformations of $A_s[\ell^\infty]$ and classifies the latter by lifts of the $\mathcal O_F$-stable Lagrangian Hodge summand. After an étale extension, $\mathcal O_F\otimes k(s)$ splits into $d$ factors. The determinant condition makes the Hodge summand a line in each factor; the tensor polarization gives the same rank statement for the dual Hodge quotient, so each corresponding de Rham factor has rank two. Every line in a rank-two alternating module is Lagrangian, and its lifts across a square-zero thickening form an affine line. Hence the deformation functor is unobstructed with tangent dimension $d$. The $\mathcal O_F$-endomorphisms and every map in the ordered polarization module lift exactly when the filtration is stable and self-dual, which are the conditions just imposed. Prime-to-$\ell$ levels lift uniquely because finite étale schemes are unchanged by nilpotent thickenings. The infinitesimal criterion proves smoothness of relative dimension $d$. $\square$

The proof separates the roles of the hypotheses. Neat level gives a scheme, good coefficient primes split the Hodge problem, perfect polarization makes the lifted filtration self-dual, and invertible level makes the frame rigid under nilpotent lifting.

## 5. The intrinsic determinant pairing on prime torsion

### 5.1 From Weil pairings to an $\mathcal O_F$-balanced form

A frame of $A[\mathfrak p]$ is not just a basis. Polarization forces its determinant, and the target of the determinant is generally a nontrivial line. We now derive that line rather than trivialize it prematurely.

For an integer $m$ invertible on $S$, Book 35's polarization-duality package gives the perfect Weil pairing of finite étale group schemes

$$
e_m:A[m]\times A^\vee[m]\longrightarrow\mu_m.
$$

If $(A,\iota,\lambda)$ is $\mathfrak c$-polarized and $x,y\in A[m]$, define a function of $c\in\mathfrak c$ by

$$
c\longmapsto e_m\bigl(x,\lambda(c)y\bigr).
\tag{5.1}
$$

Additivity of $\lambda$ and bilinearity of $e_m$ make (5.1) an element of

$$
\operatorname{Hom}_{\mathbf Z}(\mathfrak c,\mu_m)
\simeq(\mathfrak d_F^{-1}\mathfrak c^{-1}/m)(1).
$$

Here $(1)$ records the group scheme $\mu_m$; it is not a choice of an abstract cyclic group. The adjoint identity from Proposition 3.1 gives

$$
\langle ax,y\rangle_m=\langle x,ay\rangle_m
\tag{5.2}
$$

when the natural $\mathcal O_F$-action on the coefficient line is used. Thus the form is $\mathcal O_F$-balanced. Symmetry of $\lambda(c)$ and alternation of the polarization Weil pairing give $\langle x,x\rangle_m=0$.

### 5.2 The coefficient line and the different

Let

$$
\mathscr D_m=(\mathfrak c^\vee/m\mathfrak c^\vee)(1),
\qquad
\mathfrak c^\vee=\mathfrak d_F^{-1}\mathfrak c^{-1}.
\tag{5.3}
$$

The inverse different in (5.3) is forced by trace duality:

$$
\operatorname{Hom}_{\mathbf Z}(\mathfrak c,\mathbf Z)
=\{x\in F:\operatorname{Tr}_{F/\mathbf Q}(x\mathfrak c)\subseteq\mathbf Z\}
=\mathfrak d_F^{-1}\mathfrak c^{-1}.
$$

Omitting $\mathfrak d_F^{-1}$ would replace the integral dual by the $\mathcal O_F$-linear dual and would generally make the trace pairing non-unimodular. At primes outside $D_F\mathfrak c$, the distinction is locally a choice of generator, but globally it changes the determinant line and the component bookkeeping.

For a prime $\mathfrak p\mid p$ with $p\notin\Sigma$, apply the idempotent of $\mathcal O_F\otimes\mathbf F_p$ belonging to $\mathfrak p$. The $\mathfrak p$-part

$$
\mathscr D_{\mathfrak p}
=(\mathfrak c^\vee\otimes_{\mathcal O_F}k_{\mathfrak p})(1)
\tag{5.4}
$$

is a one-dimensional $k_{\mathfrak p}$-local system. Projecting (5.1) gives

$$
\langle\ ,\ \rangle_{\mathfrak p}:
A[\mathfrak p]\times A[\mathfrak p]
\longrightarrow\mathscr D_{\mathfrak p}.
\tag{5.5}
$$

The same construction applies to $\mathfrak q$.

### 5.3 Perfectness and the determinant isomorphism

**Theorem 5.1.** For every prime $\mathfrak p\notin\Sigma$, $A[\mathfrak p]$ is a rank-two finite étale $k_{\mathfrak p}$-module scheme, (5.5) is perfect and alternating, and it induces a canonical isomorphism

$$
\det_{k_{\mathfrak p}}A[\mathfrak p]
=\bigwedge_{k_{\mathfrak p}}^2A[\mathfrak p]
\xrightarrow{\sim}\mathscr D_{\mathfrak p}.
\tag{5.6}
$$

**Proof.** Since $p$ is invertible on $S$, $A[p]$ is finite étale. The unramified algebra

$$
\mathcal O_F\otimes\mathbf F_p=\prod_{\mathfrak r\mid p}k_{\mathfrak r}
$$

decomposes it into the $A[\mathfrak r]$. We justify the rank rather than infer it from total order alone. Every connected component of the smooth scheme $H_{\mathfrak c,\mathfrak n}$ meets the characteristic-zero fiber: its image in the integral base is nonempty and open, hence contains the generic point. On a complex fiber, $H_1(A,\mathbf Q)$ has dimension $2d$ over $\mathbf Q$ and is a faithful $F$-module, so it has dimension two over $F$. At an unramified prime its integral Tate lattice is therefore locally free of rank two over $\mathcal O_F\otimes\mathbf Z_p$. Thus $A[\mathfrak p]$ has $k_{\mathfrak p}$-rank two in characteristic zero. The rank of the finite étale group scheme $A[\mathfrak p]$ is locally constant, so the same is true on every fiber of that component.

The Weil pairing identifies $A[p]$ with the Cartier dual of $A^\vee[p]$. The tensor polarization (3.2) identifies $A^\vee[p]$ with $A[p]\otimes\mathfrak c$. Tensor--Hom adjunction and trace duality therefore identify the adjoint of (5.1) with an isomorphism. Passing to the $\mathfrak p$-idempotent proves perfectness of (5.5). A perfect alternating form on a rank-two module with values in a line sends $x\wedge y$ to $\langle x,y\rangle$ and yields (5.6). $\square$

This argument explains why perfectness must be proved before frames are introduced. A rational polarization alone would give a pairing after inverting $p$ but might not give the integral determinant isomorphism (5.6).

### 5.4 The cyclotomic determinant

Let $K$ be a field over $B$, choose a separable closure $K^s$, and let

$$
\rho_{A,\mathfrak p}:G_K\longrightarrow
\operatorname{GL}_2(k_{\mathfrak p})
$$

be the action on $A[\mathfrak p](K^s)$. Galois equivariance of (5.6) gives an isomorphism of one-dimensional $k_{\mathfrak p}$-representations

$$
\det\rho_{A,\mathfrak p}
\simeq
(\mathfrak c^\vee\otimes_{\mathcal O_F}k_{\mathfrak p})
\otimes_{\mathbf F_p}\mathbf F_p(1),
\tag{5.7}
$$

The first factor on the right is a fixed constant line, while $G_K$ acts on the second through the mod-$p$ cyclotomic character $\chi_p:G_K\to\mathbf F_p^\times\subset k_{\mathfrak p}^\times$. After choosing a basis of the constant first factor, (5.7) reads $\det\rho_{A,\mathfrak p}=\chi_p$. The intrinsic line formulation is preferable because it records how that basis changes with the polarization ideal.

Equation (5.7) is not an extra assumption on Hilbert--Blumenthal torsion. It is a theorem forced by polarization. Conversely, any local system intended to be framed against $A[\mathfrak p]$ must have the same determinant line. Equality only after forgetting Galois action is insufficient.

For $F=\mathbf Q$ and an elliptic curve $E/K$, choose a geometric basis $P,Q$ of $E[p]$. If $e_p(P,Q)=\zeta$, then

$$
e_p(\sigma P,\sigma Q)=\sigma(\zeta)=\zeta^{\chi_p(\sigma)}.
$$

On the other hand, bilinearity makes the left side $\zeta^{\det\rho_{E,p}(\sigma)}$. Hence $\det\rho_{E,p}=\chi_p$. Formula (5.7) is the same calculation on each $\mathfrak p$-factor, with the inverse-different polarization line retained instead of silently identifying it with the ground field.

## 6. Paired frames at one prime

### 6.1 Paired local systems

Let $S$ be a connected $B$-scheme. A **paired $\mathfrak p$-local system** is a rank-two finite étale $k_{\mathfrak p}$-module scheme $V_{\mathfrak p}$ together with a perfect alternating pairing

$$
\beta_{\mathfrak p}:V_{\mathfrak p}\times V_{\mathfrak p}
\longrightarrow\mathscr D_{\mathfrak p}.
\tag{6.1}
$$

Equivalently, it is a rank-two representation of $\pi_1(S)$ with a specified equivariant determinant isomorphism

$$
\det V_{\mathfrak p}\xrightarrow{\sim}\mathscr D_{\mathfrak p}.
\tag{6.2}
$$

In rank two, (6.1) and (6.2) contain exactly the same information: define the pairing of $x,y$ to be the image of $x\wedge y$. This equivalence remains valid in characteristic two because alternation is defined by $\beta(x,x)=0$, not inferred from skew-symmetry.

The group of automorphisms preserving (6.1) is

$$
G_{\mathfrak p}=\operatorname{SL}(V_{\mathfrak p},\beta_{\mathfrak p}),
$$

an étale form of the constant finite group $\operatorname{SL}_2(k_{\mathfrak p})$. When the coefficient line and $V_{\mathfrak p}$ are constant, it is that constant group.

### 6.2 The frame functor

Pull the universal abelian scheme $\mathcal A$ to
$H_{\mathfrak c,\mathfrak n}\times_BS$. The **paired frame functor** sends an $S$-scheme $T$ with a point of the Hilbert moduli scheme to

$$
\operatorname{Isom}^{\mathrm{pair}}_{k_{\mathfrak p}}
\bigl(V_{\mathfrak p,T},\mathcal A[\mathfrak p]_T\bigr),
\tag{6.3}
$$

the isomorphisms carrying $\beta_{\mathfrak p}$ to $\langle\ ,\ \rangle_{\mathfrak p}$. Denote the resulting space by

$$
H_{\mathfrak c,\mathfrak n}(V_{\mathfrak p}).
$$

It is important that (6.3) is an isomorphism of finite étale group schemes, not merely a bijection on geometric points. In our good-prime setting the two formulations agree after descent, but the group-scheme definition is stable under arbitrary base change and states exactly what will fail at a residue-characteristic level.

### 6.3 The special linear torsor

**Proposition 6.1.** If the paired determinant lines agree as in (6.2), the forgetful map

$$
H_{\mathfrak c,\mathfrak n}(V_{\mathfrak p})
\longrightarrow H_{\mathfrak c,\mathfrak n}\times_BS
\tag{6.4}
$$

is a finite étale right $G_{\mathfrak p}$-torsor. Its degree is

$$
|\operatorname{SL}_2(k_{\mathfrak p})|
=|k_{\mathfrak p}|\bigl(|k_{\mathfrak p}|^2-1\bigr).
\tag{6.5}
$$

**Proof.** Étale-locally on the base, both rank-two local systems admit symplectic bases, so paired isomorphisms exist. Two such isomorphisms differ uniquely by a pairing-preserving automorphism of the source. This proves the torsor identity

$$
P\times G_{\mathfrak p}\xrightarrow{\sim}P\times_H P.
$$

The isomorphism functor between finite étale schemes is itself finite étale, and the pairing equation selects an open-and-closed subscheme. Hence (6.4) is finite étale. For a finite field $k$ of order $Q$, the first column of an $\operatorname{SL}_2(k)$ matrix can be any nonzero vector, giving $Q^2-1$ choices, and the second column with determinant one forms an affine line of $Q$ choices. This proves (6.5). $\square$

### 6.4 Forgetful maps and universal objects

A point of (6.4) is the tuple

$$
(A,\iota,\lambda,\eta_{\mathfrak n},\alpha_{\mathfrak p}),
\qquad
\alpha_{\mathfrak p}:V_{\mathfrak p}\xrightarrow{\sim}A[\mathfrak p]
$$

with the pairing square commuting. Since the underlying Hilbert scheme is already fine, pulling back its universal object and adjoining the universal isomorphism gives a universal tuple on the frame cover. No new automorphisms appear: any automorphism preserving the underlying neat level was already the identity.

If one forgets pairing compatibility, the analogous frame space is a $\operatorname{GL}_2(k_{\mathfrak p})$-torsor. It is too large for prescribed torsion of cyclotomic determinant. Its determinant map splits it into fibers indexed by isomorphisms between determinant lines; choosing one of those fibers is exactly the paired cover.

## 7. The simultaneous two-prime cover

### 7.1 Independent prime ideals

Take paired local systems $(V_{\mathfrak p},\beta_{\mathfrak p})$ and $(V_{\mathfrak q},\beta_{\mathfrak q})$ over the same connected base $S$. The ideals $\mathfrak p$ and $\mathfrak q$ are distinct and have distinct residue characteristics. This stronger hypothesis makes the two torsion group schemes canonically primary components and keeps their cyclotomic determinant lines separate.

The construction also works for distinct ideals above one rational prime when the coefficient algebra is unramified, but product monodromy then requires simultaneous approximation inside the same $p$-adic factor and the determinant characters share one cyclotomic source. The two-rational-prime hypothesis is the clean form needed here.

### 7.2 The fiber product construction

Define

$$
H_{\mathfrak c,\mathfrak n}(V_{\mathfrak p},V_{\mathfrak q})
=H_{\mathfrak c,\mathfrak n}(V_{\mathfrak p})
\times_{H_{\mathfrak c,\mathfrak n}\times S}
H_{\mathfrak c,\mathfrak n}(V_{\mathfrak q}).
\tag{7.1}
$$

It parametrizes a Hilbert--Blumenthal object together with two paired isomorphisms

$$
\alpha_{\mathfrak p}:V_{\mathfrak p}\xrightarrow{\sim}A[\mathfrak p],
\qquad
\alpha_{\mathfrak q}:V_{\mathfrak q}\xrightarrow{\sim}A[\mathfrak q].
\tag{7.2}
$$

The fiber product in (7.1) says that both frames belong to the same abelian scheme, polarization module, and auxiliary level. It imposes no cross-pairing between torsion of different characteristics; there is no natural nonzero bilinear pairing between them.

### 7.3 Degree, deck group, and base change

**Proposition 7.1.** The forgetful map from (7.1) is a finite étale torsor under

$$
G_{\mathfrak p}\times G_{\mathfrak q}.
\tag{7.3}
$$

Its geometric degree is

$$
|k_{\mathfrak p}|(|k_{\mathfrak p}|^2-1)
\,|k_{\mathfrak q}|(|k_{\mathfrak q}|^2-1).
\tag{7.4}
$$

Formation of the cover and both group actions commutes with arbitrary base change on which the two primes remain invertible.

**Proof.** Fiber products of finite étale morphisms are finite étale. The product of the two torsor identities is the torsor identity for (7.3), because changing the $\mathfrak p$-frame and changing the $\mathfrak q$-frame are independent operations. Multiplying the degrees from (6.5) proves (7.4). Isomorphism schemes, Weil pairings, idempotent primary decompositions, and fiber products all commute with base change. $\square$

### 7.4 Why paired means paired separately

It is tempting to combine $A[\mathfrak p]$ and $A[\mathfrak q]$ into one module and demand a single determinant. That loses information. The determinant of the first representation lives in $k_{\mathfrak p}(1)$ and that of the second in $k_{\mathfrak q}(1)$; the reductions of the cyclotomic character are related arithmetically but are not the same character valued in one field. The correct datum is a pair of determinant diagrams.

Conversely, separate pairing conditions do not prove that the cover is geometrically connected. A subgroup of a product can project surjectively to both factors while remaining diagonal. Product monodromy is a genuine theorem, proved in Chapter 11 by simultaneous congruence approximation.

For example, if two copies of the same finite group $G$ act on two torsors and every loop acts by $(g,g)$, each individual torsor cover is connected but their fiber product has $|G|$ connected components, indexed by the invariant $x^{-1}y$. Thus “both projections are surjective” is not a substitute for the product assertion. The two-prime congruence proof will construct loops acting by $(g,1)$ and $(1,h)$ separately, which rules out this diagonal phenomenon.

## 8. Twists and prescribed residual representations

### 8.1 Descent data as a torsor

Suppose $S$ is connected with geometric point $\bar s$. There is a convenient reference paired local system even when the determinant line is not constant:

$$
V_{\mathfrak p}^0=k_{\mathfrak p}\oplus\mathscr D_{\mathfrak p},
\qquad
\beta^0((a,u),(b,v))=av-bu.
$$

Its determinant is canonically $\mathscr D_{\mathfrak p}$. Any paired local system $V_{\mathfrak p}$ becomes isomorphic to $V_{\mathfrak p}^0$ after a finite étale cover. The sheaf

$$
T_{\mathfrak p}=
\operatorname{Isom}^{\mathrm{pair}}(V_{\mathfrak p}^0,V_{\mathfrak p})
$$

is a right torsor under $G_{\mathfrak p}^0=\operatorname{Aut}^{\mathrm{pair}}(V_{\mathfrak p}^0)$. After choosing geometric paired frames, its geometric fiber is $\operatorname{SL}_2(k_{\mathfrak p})$. Because $V_{\mathfrak p}^0$ itself can have cyclotomic descent, the invariant attached to the torsor is in general a crossed cocycle, not an ordinary homomorphism:

$$
z_{\mathfrak p}:\pi_1(S,\bar s)\longrightarrow
\operatorname{SL}_2(k_{\mathfrak p}),
\qquad
z_{\mathfrak p}(\gamma\delta)
=z_{\mathfrak p}(\gamma)\,{}^\gamma z_{\mathfrak p}(\delta).
\tag{8.1}
$$

Here ${}^\gamma g$ is the action on the automorphism group induced by the descent of $V_{\mathfrak p}^0$. Changing the geometric frame changes $z_{\mathfrak p}$ by a coboundary. The torsor, rather than one chosen matrix cocycle, is the invariant descent datum. When the reference local system is constant, the action is trivial and (8.1) is an ordinary homomorphism up to conjugacy.

If a rank-two representation $r_{\mathfrak p}$ has cyclotomic determinant after a basis of the constant polarization line is chosen, one must still supply the intrinsic isomorphism $\det r_{\mathfrak p}\simeq\mathscr D_{\mathfrak p}$. Only then does the discrepancy from $V_{\mathfrak p}^0$ take values in the special-linear group. Without that determinant isomorphism, it takes values in the general-linear group and cannot twist the paired cover.

### 8.2 Twisting the frame cover

Let

$$
P_{\mathfrak p}^0=
\operatorname{Isom}^{\mathrm{pair}}(V_{\mathfrak p}^0,\mathcal A[\mathfrak p])
\longrightarrow H_S,
\qquad
H_S=H_{\mathfrak c,\mathfrak n}\times_BS,
$$

be the reference paired-frame torsor. If $T_{\mathfrak p}$ is the torsor attached to $V_{\mathfrak p}$, define the twist

$$
{}^{T_{\mathfrak p}}P_{\mathfrak p}^0
=\bigl(T_{\mathfrak p}\times_SP_{\mathfrak p}^0\bigr)/G_{\mathfrak p}^0,
\tag{8.2}
$$

The diagonal action is $(t,a)\cdot g=(t\circ g,a\circ g)$. It is free, its finite étale quotient exists, and the expression $a\circ t^{-1}:V_{\mathfrak p}\to\mathcal A[\mathfrak p]$ is invariant under it. Étale-locally on $S$, a point of $T_{\mathfrak p}$ identifies (8.2) with the reference cover. On overlaps the change is exactly (8.1). Effective descent therefore gives a canonical identification of (8.2) with the directly defined cover $H(V_{\mathfrak p})$ of Chapter 6.

For two primes, twist by $T_{\mathfrak p}\times T_{\mathfrak q}$ under $G_{\mathfrak p}\times G_{\mathfrak q}$. Contracted products commute with the fiber product in (7.1), so one may twist simultaneously or one prime at a time with the same result.

### 8.3 The determinant obstruction

**Proposition 8.1.** A rank-two $k_{\mathfrak p}$-local system $W$ can occur as the $\mathfrak p$-torsion of a point of the paired Hilbert cover only if there is an equivariant isomorphism

$$
\det W\simeq\mathscr D_{\mathfrak p}.
\tag{8.3}
$$

When (8.3) is supplied, $W$ has a unique alternating pairing with this determinant target, and the twisted paired-frame cover exists.

**Proof.** Necessity follows by taking determinants of an isomorphism $W\simeq A[\mathfrak p]$ and applying (5.6). Given (8.3), send $(x,y)$ to the image of $x\wedge y$. This is alternating and perfect because $W$ has rank two and (8.3) is an isomorphism. It is the only such pairing inducing the chosen determinant isomorphism. Chapter 6 then represents its frame functor. $\square$

Equality of determinant characters is weaker than (8.3) when the base has nontrivial line local systems: one-dimensional representations with the same character become identified only after an isomorphism of their underlying coefficient lines has been supplied. Different choices differ by a unit of $k_{\mathfrak p}$ and change the orientation of the paired-frame problem. The choice must therefore be included in the data.

### 8.4 Moduli interpretation of the twist

An $S'$-point of the twisted two-prime cover is not a mysterious form of a scheme. It is exactly a tuple

$$
(A,\iota,\lambda,\eta_{\mathfrak n},
\alpha_{\mathfrak p},\alpha_{\mathfrak q})/S'
$$

in which each $\alpha$ is a pairing-preserving isomorphism from the prescribed local system to the corresponding torsion. This follows after an étale cover trivializing both local systems, where it is the standard frame interpretation; effective descent then returns the tuple over $S'$.

When $S=\operatorname{Spec}K$ is a field, twisting changes arithmetic descent but not the geometric shape. After base change to $K^s$, every $T_{\mathfrak r}$ has a point, so the twisted cover becomes isomorphic to the untwisted one. The same is true for a family pulled back from such an arithmetic local system. It is not true for an arbitrary geometrically nonconstant local system on a positive-dimensional $S$: its restriction to $S_{K^s}$ can retain geometric monodromy. This distinction will be used in Section 11.4.

## 9. Complex uniformization and components

### 9.1 The symmetric domain

Finite étale torsors need not be connected. To determine connectedness we pass to the complex analytic description, where loops are arithmetic matrices and level covers are reduction maps.

Put

$$
G=\operatorname{Res}_{F/\mathbf Q}\operatorname{GL}_2.
$$

The Hilbert symmetric domain is

$$
X=(\mathbf C\setminus\mathbf R)^d.
$$

It has $2^d$ connected components, indexed by a choice of upper or lower half-plane at every real embedding. Let $X^+=\mathfrak H^d$ be the all-upper component. The stabilizer of $X^+$ in $G(\mathbf R)$ consists of matrices whose determinant is positive at every real embedding; denote it by $G(\mathbf R)^+$, and write

$$
G(\mathbf Q)^+=\{g\in\operatorname{GL}_2(F):\det(g)\in F_+^\times\}.
$$

The lattice and polarization data of Chapter 4 select an open compact subgroup $K\subset G(\mathbf A_f)$, neat because it contains the prescribed auxiliary principal level as an equality at the relevant factors. It is useful first to place all narrow polarization types in the ambient similitude moduli space. Its complex points have the analytic description

$$
G(\mathbf Q)\backslash\bigl(X\times G(\mathbf A_f)/K\bigr).
\tag{9.1}
$$

The identification is obtained by sending a complex abelian variety to its rational homology with $F$-action, its Hodge complex structure, and its adelic level trivialization, while retaining the similitude class of its polarization module. Conversely, an $F$-lattice in $F^2$ together with $z\in X$ gives a complex torus. For each positive $c_0$ in the ordered polarization ideal, the scalar form $\operatorname{Tr}_{F/\mathbf Q}(c_0\psi)$ from (4.1), with sign determined by the component of $X$, satisfies the Riemann relations. Hence the torus is algebraic and carries the whole ordered polarization module belonging to its determinant class. Changing the rational or integral trivialization gives the two quotient actions in (9.1). These constructions are inverse because homomorphisms of polarized complex tori are exactly the compatible maps of their integral Hodge lattices.

The fine scheme $H_{\mathfrak c,\mathfrak n}$ with the exact ordered isomorphism (3.1) is the union of those open-and-closed pieces of (9.1) having the selected $\mathfrak c$-type and determinant-level datum. Inside one such piece, the stabilizer preserves the chosen alternating form, not merely its similitude class. Under the rank-two lattice identification this exact stabilizer has determinant one. This distinction is what makes geometric torsion monodromy special linear.

### 9.2 The determinant component map

The determinant sends (9.1) to the finite double quotient

$$
\mathcal C_K=F_+^\times\backslash\mathbf A_{F,f}^\times/\det K.
\tag{9.2}
$$

This quotient is finite: dividing finite ideles by $\widehat{\mathcal O}_F^\times$ gives the ideal class group, and the remaining discrepancy between $F^\times$ and $F_+^\times$ is a finite signature quotient. Thus $\mathcal C_K$ is a ray version of the narrow ideal class group.

When $F=\mathbf Q$ and $K$ is maximal away from a principal level $N$, the ordinary ideal class group disappears, but the determinant of the level still records a class in $(\mathbf Z/N\mathbf Z)^\times$ modulo the chosen multiplier subgroup. Fixing the Weil-pairing value selects one of these determinant components. This is the modular-curve shadow of (9.2): even when the base field has class number one, a full basis has a determinant that must be normalized.

**Theorem 9.1.** The determinant map induces a bijection from the connected components of (9.1) to $\mathcal C_K$.

**Proof.** Choose $g\in G(\mathbf A_f)$. The part of (9.1) represented by $X^+\times gK$ is

$$
\widetilde\Gamma_g\backslash X^+,
\qquad
\widetilde\Gamma_g=G(\mathbf Q)^+\cap gKg^{-1}.
\tag{9.3}
$$

It is connected because $X^+$ is connected. Two such pieces, represented by $g$ and $g'$, agree precisely when

$$
g'=\gamma gk
$$

for $\gamma\in G(\mathbf Q)^+$ and $k\in K$. Their determinants then have the same class in (9.2).

For the converse, suppose $\det g'$ and $\det g$ have the same class. After multiplying $g'$ on the left by an element of $G(\mathbf Q)^+$ and on the right by an element of $K$, we may assume $\det g'=\det g$. Then $h=g'g^{-1}$ lies in $\operatorname{SL}_2(\mathbf A_{F,f})$. Strong approximation for the simply connected group $\operatorname{SL}_2$ says

$$
\operatorname{SL}_2(\mathbf A_{F,f})
=\operatorname{SL}_2(F)\,(gKg^{-1}\cap\operatorname{SL}_2(\mathbf A_{F,f})).
$$

For completeness, density in this instance can be seen directly. A matrix over a field is, after multiplication by the Weyl matrix when necessary, a product of upper and lower elementary matrices; the diagonal determinant-one factor in the Bruhat decomposition is itself such a product. An adelic open coset imposes conditions at only finitely many places and integrality outside them. Approximation in the corresponding ring of $S$-integers chooses the elementary parameters simultaneously in those local neighborhoods while retaining integrality elsewhere. Their product lies in $\operatorname{SL}_2(F)$ and in the prescribed adelic coset. Taking that coset to be $h(gKg^{-1}\cap\operatorname{SL}_2(\mathbf A_{F,f}))$ gives $h=\gamma k'$ with $\gamma\in\operatorname{SL}_2(F)\subset G(\mathbf Q)^+$ and $k'\in gKg^{-1}$. Rearrangement gives $g'=\gamma gk$ and the two pieces coincide. This proves exactly the finite-adelic strong-approximation statement used here. $\square$

### 9.3 Connected components of a fixed polarization type

The moduli problem with one fixed ordered ideal $\mathfrak c$ selects one or several classes in (9.2), depending on the determinant orientation included in the finite level. Make this selection intrinsic by writing

$$
\mathcal C_{\mathfrak c,\mathfrak n}
=\{[a]\in\mathcal C_K:
\text{the lattice in the class }[a]\text{ has ordered polarization module }
(\mathfrak c,\mathfrak c^+)\text{ and paired principal-level orientation as in (4.3)--(4.4)}\}.
$$

Polarization type and finite-level orientation are locally constant, so this is a union of open-and-closed components. Theorem 9.1 now gives the exact statement

$$
\pi_0\bigl(H_{\mathfrak c,\mathfrak n}(\mathbf C)\bigr)
\xrightarrow{\sim}\mathcal C_{\mathfrak c,\mathfrak n}.
\tag{9.3a}
$$

This is also a practical description: starting with a double-coset representative, one computes the trace-dual of its lattice and compares its ordered ideal and reduction modulo $\mathfrak n$ with the fixed data. On a selected component, exact preservation of (3.1) replaces $\widetilde\Gamma_g$ by its polarization-isometry subgroup

$$
\Gamma_g=\{\gamma\in\widetilde\Gamma_g:
\gamma^*\psi=\psi\}.
\tag{9.4}
$$

Locally on the rank-two $F$-space, $\gamma^*\psi=(\det\gamma)\psi$, so $\Gamma_g\subset\operatorname{SL}_2(F)$. The selected component is $\Gamma_g\backslash\mathfrak H^d$ after the determinant-level datum is fixed. It is connected, and $\Gamma_g$ is an arithmetic subgroup commensurable with $\operatorname{SL}_2(\mathcal O_F)$.

Changing $\mathfrak c$ by $a\mathfrak c$ with $a\in F_+^\times$ does not change its ordered narrow ideal class: multiplication by $a$ transports the polarization module and leaves the class in (9.2) unchanged. Multiplication by an element with a negative real sign changes the positive cone and can move to another component of $X$. Changing $\mathfrak c$ by a nonprincipal fractional ideal changes the adelic determinant class. This is the geometric reason the polarization module, rather than a principal polarization, must be retained.

The auxiliary level refines the class set through $\det K$. If $K$ is replaced by a smaller normal neat subgroup $K'$, the map $\mathcal C_{K'}\to\mathcal C_K$ is induced by enlarging the right denominator from $\det K'$ to $\det K$. It may merge algebraic components after forgetting level, but it never creates an unexplained geometric path between distinct determinant classes.

### 9.4 Algebraic and geometric components

For a finite-type complex scheme, algebraic and analytic connected components agree. One way to see this without making a false algebraicity claim about arbitrary holomorphic functions is to decompose the scheme into its finitely many algebraic irreducible components: the analytification of each irreducible component is connected, and the incidence graph of their nonempty intersections is unchanged by analytification. Connected components are the connected components of this finite graph in both categories. Therefore Theorem 9.1 computes the ambient determinant classes, while the selection described in Section 9.3 computes the geometric components of $H_{\mathfrak c,\mathfrak n,\overline{\mathbf Q}}$ exactly.

The absolute Galois group may permute these geometric components. Determining that arithmetic permutation requires additional canonical-model descent data and is not used here: for geometric monodromy, choose one geometric component $H^\circ$ and work over it. A twist can alter the arithmetic permutation of components while becoming trivial over $\overline{\mathbf Q}$; it cannot alter the set or geometry of the geometric components.

## 10. Geometric monodromy of a prime-level frame cover

### 10.1 Monodromy as reduction of an arithmetic group

Fix a complex component

$$
H^\circ(\mathbf C)=\Gamma_g\backslash\mathfrak H^d.
$$

Here $\Gamma_g$ is the exact polarization stabilizer (9.4), not the larger similitude group $\widetilde\Gamma_g$. Neatness makes the action free, so $\mathfrak H^d$ is the analytic universal cover and

$$
\pi_1^{\mathrm{top}}(H^\circ(\mathbf C))\simeq\Gamma_g.
\tag{10.1}
$$

The universal $\mathfrak p$-torsion local system is obtained from the fixed lattice by the action of $\Gamma_g$. Hence the analytification of its paired-frame cover is the quotient of $\mathfrak H^d\times\operatorname{SL}_2(k_{\mathfrak p})$ by $\gamma(z,h)=(\gamma z,\overline\rho_{\mathfrak p}(\gamma)h)$, where

$$
\overline\rho_{\mathfrak p}:\Gamma_g
\longrightarrow\operatorname{SL}_2(k_{\mathfrak p}),
\tag{10.2}
$$

after a reference paired frame is chosen. The image lies in $\operatorname{SL}_2$ because loops in a geometric complex component preserve the determinant trivialization; the similitude or cyclotomic variation belongs to the arithmetic base, not to geometric loops.

This explicit quotient is enough for the argument; no general topological--étale comparison theorem is being imported. Its analytic total space is connected exactly when the image of (10.2) acts transitively on the second factor, equivalently when that image is the full special-linear group. Algebraic and analytic connected components agree by Section 9.4. Once the algebraic torsor is known to be connected, the finite-covering dictionary proves that its étale monodromy is transitive, and a transitive subgroup acting by left translations on a regular $\operatorname{SL}_2(k_{\mathfrak p})$-set is the whole group.

### 10.2 A congruence-surjectivity lemma

We isolate the approximation input and its finite exceptional set.

**Lemma 10.1.** Let $\Gamma\subset\operatorname{SL}_2(F)$ be an arithmetic subgroup commensurable with $\operatorname{SL}_2(\mathcal O_F)$ and containing a principal congruence subgroup

$$
\Gamma(\mathfrak a)=
\ker\bigl(\operatorname{SL}_2(\mathcal O_F)\to
\operatorname{SL}_2(\mathcal O_F/\mathfrak a)\bigr)
$$

after conjugation by some element of $\operatorname{GL}_2(F)$. There is a finite set $\Sigma(\Gamma)$ of primes, containing those dividing $\mathfrak a$ and the denominators of the conjugating matrix, such that for every $\mathfrak p\notin\Sigma(\Gamma)$ the reduction of $\Gamma$ contains $\operatorname{SL}_2(k_{\mathfrak p})$.

**Proof.** Away from the denominators, conjugation identifies the relevant local lattice with $\mathcal O_{F,\mathfrak p}^2$. Since $\mathfrak p\nmid\mathfrak a$, the Chinese remainder theorem gives, for every $x\in k_{\mathfrak p}$, an element $\widetilde x\in\mathcal O_F$ satisfying

$$
\widetilde x\equiv x\pmod{\mathfrak p},
\qquad
\widetilde x\equiv0\pmod{\mathfrak a}.
$$

Therefore the matrices

$$
u(\widetilde x)=\begin{pmatrix}1&\widetilde x\\0&1\end{pmatrix},
\qquad
\ell(\widetilde x)=\begin{pmatrix}1&0\\\widetilde x&1\end{pmatrix}
$$

belong to $\Gamma(\mathfrak a)$ and reduce to all upper and lower elementary matrices over $k_{\mathfrak p}$. These generate $\operatorname{SL}_2(k_{\mathfrak p})$: Gaussian elimination reduces a matrix with nonzero upper-left entry using upper and lower operations, while if that entry is zero multiplication by $\begin{psmallmatrix}0&-1\\1&0\end{psmallmatrix}=u(-1)\ell(1)u(-1)$ makes it nonzero. Hence the reduction image is full. $\square$

The statement is phrased for containment after conjugation because a component lattice can be a projective module rather than $\mathcal O_F^2$. Its localizations are free at all primes, and only finitely many denominators enter when one chooses global coordinates.

The lifting mechanism can be seen numerically over $\mathbf Z$. Take auxiliary level $N=3$ and residual prime $p=5$. To lift $u(2)\in\operatorname{SL}_2(\mathbf F_5)$ while preserving level three, solve

$$
\widetilde x\equiv0\pmod3,
\qquad
\widetilde x\equiv2\pmod5.
$$

The choice $\widetilde x=12$ gives $u(12)\equiv1\pmod3$ and $u(12)\equiv u(2)\pmod5$. For two primes, say $5$ and $7$, one adds $\widetilde x\equiv0\pmod7$ to make the loop trivial in the second factor. This elementary calculation is exactly what the ideal-theoretic Chinese remainder theorem performs over $\mathcal O_F$.

### 10.3 Full special-linear monodromy

**Theorem 10.2.** For every geometric component $H^\circ$ there is a finite set $\Sigma(H^\circ)$ such that, for $\mathfrak p$ outside it and outside the auxiliary level, the geometric monodromy of the paired $\mathfrak p$-frame cover over $H^\circ$ is

$$
\operatorname{SL}_2(k_{\mathfrak p}).
\tag{10.3}
$$

If the component classes are represented by a fixed finite set, one finite exceptional set works for all of them.

**Proof.** The group $\Gamma_g$ in (9.4) is arithmetic and commensurable with $\operatorname{SL}_2(\mathcal O_F)$. More is true here than abstract arithmeticity: by definition it is the rational stabilizer of the fixed component lattice with the fixed adelic principal level. The local open stabilizers therefore contain principal congruence kernels, and after choosing coordinates and clearing finitely many denominators their intersection contains a global $\Gamma(\mathfrak a)$. No congruence-subgroup property for arbitrary finite-index subgroups is being assumed. Lemma 10.1 shows that the reduction map (10.2) is onto.

The explicit analytic quotient of Section 10.1 is consequently connected. Section 9.4 makes the algebraic frame cover geometrically connected, and the finite-covering dictionary then makes its étale monodromy transitive. Since the fiber is a regular special-linear set, the monodromy image is the full group in (10.3). There are finitely many components by (9.2); taking the union of their finite exceptional sets gives the final assertion. $\square$

This proof also explains the phrase **monodromy-admissible prime**: it means a prime outside the explicit finite set formed from $D_F$, the polarization and lattice denominators, the auxiliary level, and the chosen component representatives. No assertion is made at the excluded primes.

### 10.4 Connectedness of the frame cover

A finite étale cover of a connected scheme is connected exactly when its geometric monodromy acts transitively on one geometric fiber. For a right $G$-torsor the fiber is a simply transitive $G$-set, and the monodromy action is transitive exactly when its image is all of $G$.

**Corollary 10.3.** At every monodromy-admissible $\mathfrak p$, the paired $\mathfrak p$-frame cover over $H^\circ$ is geometrically connected. Its deck group is the opposite of the right torsor group, and hence is identified with $\operatorname{SL}_2(k_{\mathfrak p})$ by inversion.

**Proof.** Theorem 10.2 makes the monodromy action on the torsor fiber transitive, proving connectedness. The right torsor action supplies all deck transformations. A deck transformation is determined by its value at one point of a connected cover, so there are no others. Composition of right translations reverses the displayed multiplication, giving the stated opposite-group convention. $\square$

## 11. Product monodromy at two primes

### 11.1 Why two surjections are not enough

Let $G_1$ and $G_2$ be finite groups. A subgroup $M\subset G_1\times G_2$ can project onto each factor without being the product. If $G_1\simeq G_2$, the graph of an isomorphism is the basic counterexample. Therefore two applications of Theorem 10.2 do not by themselves prove connectedness of the fiber product (7.1).

For different residue characteristics the groups often have no common nonabelian quotient, but relying on a classification of their quotients would introduce small-field exceptions and would obscure the source of independence. Simultaneous congruence approximation is stronger and proves the product image directly.

### 11.2 Simultaneous congruence approximation

**Lemma 11.1.** In the setting of Lemma 10.1, let $\mathfrak p$ and $\mathfrak q$ be distinct primes outside $\Sigma(\Gamma)$. Then reduction induces a surjection

$$
\Gamma\longrightarrow
\operatorname{SL}_2(k_{\mathfrak p})
\times\operatorname{SL}_2(k_{\mathfrak q}).
\tag{11.1}
$$

**Proof.** It suffices to lift elementary generators in either factor while making the other factor the identity. Given $x\in k_{\mathfrak p}$, the Chinese remainder theorem for the pairwise coprime ideals $\mathfrak a$, $\mathfrak p$, and $\mathfrak q$ gives $\widetilde x\in\mathcal O_F$ with

$$
\widetilde x\equiv0\pmod{\mathfrak a},
\quad
\widetilde x\equiv x\pmod{\mathfrak p},
\quad
\widetilde x\equiv0\pmod{\mathfrak q}.
$$

Then $u(\widetilde x)$ and $\ell(\widetilde x)$ lie in $\Gamma$ and reduce to the desired elementary matrix in the $\mathfrak p$-factor and the identity in the $\mathfrak q$-factor. Reverse the roles to obtain elementary generators in the second factor. Since elementary matrices generate both special linear groups, the image contains both direct factors and hence their product. $\square$

This proof is insensitive to accidental isomorphisms between small special linear groups. It proves independence at the level of congruence conditions before taking any quotient.

### 11.3 The product theorem

**Theorem 11.2.** Let $\mathfrak p$ and $\mathfrak q$ be distinct monodromy-admissible primes outside the auxiliary level. On every geometric component $H^\circ$, the geometric monodromy of the two-prime paired-frame cover is

$$
\operatorname{SL}_2(k_{\mathfrak p})
\times\operatorname{SL}_2(k_{\mathfrak q}).
\tag{11.2}
$$

Consequently the two-prime cover over $H^\circ$ is geometrically connected.

**Proof.** Under analytic uniformization, both torsion local systems are obtained by reducing the same arithmetic group $\Gamma_g$ at the two primes. Lemma 11.1 says the simultaneous reduction is the product in (11.2). Therefore the explicit analytic quotient with fiber the product group is connected. Algebraic and analytic components agree, so the algebraic two-prime cover is geometrically connected. Its étale monodromy is then transitive by the finite-covering dictionary; on a regular product-group fiber, transitivity forces the image to be the whole product. $\square$

Notice the order of reasoning: product monodromy proves connectedness. Connectedness is not assumed in order to enlarge monodromy, and the product cardinality is not used before surjectivity has been established.

### 11.4 Twists preserve geometric monodromy

Let $K$ be the field of constants and let $P$ be the untwisted two-prime cover. A twist by prescribed local systems changes descent by a cocycle of $G_K$. After base change to $\overline K$, that cocycle becomes a coboundary: choose paired frames of both prescribed local systems over $\overline K$. They give an isomorphism

$$
P_{\overline K}^{\mathrm{tw}}
\xrightarrow{\sim}P_{\overline K}
\tag{11.3}
$$

over the geometric Hilbert scheme. The isomorphism is not canonical, but changing it conjugates the monodromy representation inside the deck group.

**Corollary 11.3.** Every determinant-compatible arithmetic twist over a field $K$ has the same geometric component set, full product geometric monodromy, and geometric connectedness over each $H^\circ$ as the untwisted cover.

Arithmetic connectedness over $K$ is a different question. Galois can permute the geometric base components or act through outer descent on the deck torsor. The corollary asserts the exact geometric property needed when one first chooses a component and later applies arithmetic specialization.

## 12. The complete two-prime moduli theorem

### 12.1 Statement with all hypotheses

We now collect the construction in a form that can be invoked without silently changing polarization, determinant, or component conventions.

**Theorem 12.1 (two-prime Hilbert--Blumenthal cover).** Let $F$ be totally real of degree $d$. Fix an ordered invertible ideal $(\mathfrak c,\mathfrak c^+)$, a rank-two PEL lattice $(L,\psi)$ with value line $\mathfrak c^\vee=\mathfrak d_F^{-1}\mathfrak c^{-1}$, and auxiliary principal level $\mathfrak n=N\mathcal O_F$ with $N\geq3$. Let $\Sigma$ contain:

1. primes dividing $D_F$, $\mathfrak c$, its denominator, or $\mathfrak n$;
2. primes at which $(L,\psi)$ is not self-dual;
3. the finitely many denominators of representatives for the component lattices.

Let $\mathfrak p\mid p$ and $\mathfrak q\mid q$ be distinct prime ideals of distinct rational residue characteristics outside $\Sigma$. Put $M_\Sigma=\prod_{\ell\in\Sigma}\ell$ and $B=\operatorname{Spec}\mathbf Z[1/M_\Sigma pq]$. Over a connected $B$-scheme $S$, let $V_{\mathfrak p}$ and $V_{\mathfrak q}$ be rank-two finite étale local systems with specified determinant isomorphisms

$$
\det V_{\mathfrak p}\simeq
(\mathfrak c^\vee\otimes k_{\mathfrak p})(1),
\qquad
\det V_{\mathfrak q}\simeq
(\mathfrak c^\vee\otimes k_{\mathfrak q})(1).
\tag{12.1}
$$

Then:

1. the determinant-condition, $\mathfrak c$-polarized, auxiliary-level Hilbert functor is a smooth quasi-projective fine scheme $H_{\mathfrak c,\mathfrak n}$ of relative dimension $d$;
2. the functor adjoining pairing-preserving frames $V_{\mathfrak p}\simeq A[\mathfrak p]$ and $V_{\mathfrak q}\simeq A[\mathfrak q]$ is represented by a finite étale cover $Y\to H_{\mathfrak c,\mathfrak n}\times S$;
3. this cover is a torsor under

   $$
   \operatorname{SL}_2(k_{\mathfrak p})
   \times\operatorname{SL}_2(k_{\mathfrak q})
   $$

   after geometric trivialization of the prescribed local systems, and has the degree in (7.4);
4. geometric components of the characteristic-zero base are indexed by the subset $\mathcal C_{\mathfrak c,\mathfrak n}$ of determinant classes in

   $$
   F_+^\times\backslash\mathbf A_{F,f}^\times/\det K(\mathfrak n)
   $$

   defined by the ordered polarization module and level orientation in (9.3a);
5. over every such characteristic-zero geometric component of the untwisted base, the standard two-prime cover has full product geometric monodromy and is geometrically connected;
6. if $S=\operatorname{Spec}K$ for a characteristic-zero field $K$, replacing the standard frames by the determinant-compatible arithmetic twists $V_{\mathfrak p}$ and $V_{\mathfrak q}$ preserves assertions 2--5 after base change to $\overline K$.

### 12.2 Proof of representability and the covering assertions

**Proof.** Proposition 2.1 turns the determinant condition into the rank-one Hodge condition on the stated base. The ordered isomorphism (3.1), together with the tensor perfectness (3.2), fixes both positivity and integral polarization type. Principal level at least three kills all automorphisms by Proposition 4.1. Descent and the polarized Hilbert parameter construction therefore yield a fine quasi-projective scheme. Lifting the $d$ Hodge lines proves smoothness of relative dimension $d$, as in Theorem 4.2.

For either prime, Theorem 5.1 gives a perfect alternating torsion pairing and the determinant isomorphism (5.6). Hypothesis (12.1) makes the paired isomorphism sheaf locally nonempty. Proposition 6.1 represents it by a finite étale special-linear torsor. Taking their fiber product gives the two-prime cover and product torsor by Proposition 7.1. The degree is the product of the two special-linear group orders. Every construction commutes with base change, so the same conclusions hold over $S$. $\square$

### 12.3 Proof of components and monodromy

**Proof.** Complex uniformization identifies each base component with $\Gamma_g\backslash\mathfrak H^d$. The determinant and strong-approximation argument of Theorem 9.1 gives the stated component classes. Because $\Sigma$ contains the component-lattice denominators and the auxiliary level primes, each $\Gamma_g$ contains the congruence subgroup required by Lemma 11.1 at $\mathfrak p$ and $\mathfrak q$. Its simultaneous reduction is therefore the full product of special linear groups. The explicit analytic quotient with that regular fiber is connected; agreement of algebraic and analytic components makes the algebraic cover geometrically connected. The finite-covering dictionary then identifies its étale monodromy as the full product, exactly as in Theorem 11.2.

Finally, under the field hypothesis in assertion 6, every determinant-compatible arithmetic twist becomes isomorphic to the standard cover over an algebraic closure, by (11.3). It has the same geometric components and conjugate geometric monodromy. For a general $S$, assertions 1--3 still hold, while a geometrically varying local system contributes its own monodromy and is deliberately excluded from assertion 6. This proves the remaining assertions. $\square$

### 12.4 Variants and sharp boundaries

The theorem has useful variants, but each changes a precise part of the conclusion.

If $K$ is neat but not principal, the same construction works. Monodromy is the image of the corresponding arithmetic subgroup; it is full at all but finitely many primes, but the exceptional set must be recalculated. If auxiliary level is not neat, the natural base is an algebraic stack with finite inertia. Its frame cover is representable over the stack, but a universal abelian scheme need not descend to the coarse space.

If the pairing is preserved only up to scalar, the deck group is $\operatorname{GL}_2$, with determinant equal to the allowed multiplier. Full geometric monodromy then depends on which multipliers geometric loops can realize. Our paired cover fixes the determinant line and therefore has the clean special-linear group.

If $\mathfrak p$ divides the residue characteristic of the base, $A[\mathfrak p]$ is finite flat rather than finite étale. A basis on geometric points no longer determines it, the frame functor need not be étale, and connectedness cannot be read from the ordinary étale fundamental group. If $F$ is ramified there, even the determinant condition may need a refined local model. These cases require separate local geometry and are not consequences of Theorem 12.1.

## 13. A working dictionary for later arithmetic specialization

### 13.1 Points and Galois representations

Let $K$ be a field over $B$. A $K$-point of the twisted cover gives a Hilbert--Blumenthal abelian variety $A/K$ and equivariant paired isomorphisms

$$
V_{\mathfrak p}\simeq A[\mathfrak p],
\qquad
V_{\mathfrak q}\simeq A[\mathfrak q].
\tag{13.1}
$$

Thus prescribed residual representations are realized exactly, not merely up to semisimplification, and their determinant identifications agree with the polarization Weil pairings. Forgetting the pairing in (13.1) loses the normalization that controls the cyclotomic character. Forgetting the ordered polarization module loses the reason the same normalization is compatible at both primes.

Conversely, if an $\mathcal O_F$-abelian variety with the stated polarization and level has torsion representations isomorphic to the prescribed local systems through determinant-compatible maps, those maps define a unique point of the cover. This is the universal property needed when a global point is produced by an arithmetic approximation theorem.

### 13.2 Changing auxiliary level and polarization class

Suppose $\mathfrak n'\subset\mathfrak n$ gives a finer neat level. Forgetting part of the level defines a finite étale map

$$
H_{\mathfrak c,\mathfrak n'}\longrightarrow H_{\mathfrak c,\mathfrak n}
$$

over the locus where both levels are invertible. Its deck group is the appropriate quotient of congruence groups, subject to the pairing multiplier convention. The universal two-prime cover pulls back to the cover for the finer level. Monodromy at primes away from both levels remains full because the congruence approximation can impose the finer auxiliary condition and the two residual conditions simultaneously by the Chinese remainder theorem.

For a fractional ideal $\mathfrak a$, Serre tensoring gives

$$
(A\otimes_{\mathcal O_F}\mathfrak a)^\vee
\simeq A^\vee\otimes_{\mathcal O_F}\mathfrak a^{-1},
$$

and hence changes the ordered polarization module from $\mathfrak c$ to $\mathfrak c\mathfrak a^{-2}$. Its value line changes correspondingly from $\mathfrak c^\vee$ to $\mathfrak c^\vee\mathfrak a^2$. Thus Serre tensoring moves the determinant class in (9.2) and is not invisible. To compare the two polarization types one must transport the standard lattice, its value line, and both determinant pairings. Merely declaring that all polarizations are equivalent up to isogeny would destroy the fine moduli interpretation.

### 13.3 What is geometric and what is arithmetic

The construction separates three layers:

$$
\begin{array}{ccl}
\text{fine moduli geometry}
&:&(A,\iota,\lambda,\eta_{\mathfrak n}),\\[2mm]
\text{geometric level cover}
&:&\operatorname{SL}_2(k_{\mathfrak p})\times
\operatorname{SL}_2(k_{\mathfrak q}),\\[2mm]
\text{arithmetic descent}
&:&(V_{\mathfrak p},V_{\mathfrak q})\text{ and their twists}.
\end{array}
$$

Neatness belongs to the first layer. Congruence surjectivity and geometric connectedness belong to the second. Determinant-compatible residual representations belong to the third. Confusing the layers leads to the most common false inferences: a fine scheme need not have a connected level cover; two individually connected covers need not have connected fiber product; and a geometric twist need not be arithmetically trivial.

The determinant class set is the bridge between the first two layers. One first chooses a geometric component indexed by (9.2), then proves product monodromy for its arithmetic group. The prescribed local systems do not choose that component automatically. Their twist becomes trivial geometrically, so component selection and arithmetic realization remain two separate tasks.

### 13.4 Conclusion

We have constructed the complete geometric package for two-prime Hilbert--Blumenthal level. Real multiplication is constrained by the Hilbert determinant polynomial, which on the good base is exactly rank-one Hodge type. Polarizations are recorded by the ordered module $(\mathfrak c,\mathfrak c^+)$ and the perfect tensor map $A\otimes\mathfrak c\simeq A^\vee$. Auxiliary principal level at least three removes every automorphism and produces a smooth fine scheme of relative dimension $d$.

The polarization induces, at each good prime, a perfect alternating form with value line

$$
(\mathfrak d_F^{-1}\mathfrak c^{-1}\otimes k_{\mathfrak p})(1),
$$

so its determinant is cyclotomic with the precise polarization coefficient. Paired frames therefore form special-linear, not general-linear, torsors. Two such frame spaces combine into a finite étale product torsor, and determinant-compatible residual representations give its twists.

Finally, the determinant map indexes the geometric Hilbert components by a narrow adelic class set. On each component, simultaneous congruence approximation realizes elementary matrices independently at the two primes. This proves full product geometric monodromy before connectedness is invoked, and hence proves that both the standard and every determinant-compatible twisted two-prime cover are geometrically connected over that component. The resulting scheme is ready to receive arithmetic points while keeping polarizations, determinants, components, and both residual torsion representations under exact control.
