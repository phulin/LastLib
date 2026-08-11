# Local Conditions for Hardly-Ramified Minimal Deformations

## Contents

- [1. The two-place deformation problem](#1-the-two-place-deformation-problem)
  - [1.1 Why hardly ramified is a local design problem](#11-why-hardly-ramified-is-a-local-design-problem)
  - [1.2 Coefficients, determinant, and residual data](#12-coefficients-determinant-and-residual-data)
  - [1.3 Tangents, liftability, and obstruction maps](#13-tangents-liftability-and-obstruction-maps)
- [2. The distinguished local type at 2](#2-the-distinguished-local-type-at-2)
  - [2.1 The tame quotient and Frobenius convention](#21-the-tame-quotient-and-frobenius-convention)
  - [2.2 A quadratic algebra and an order-three inertia operator](#22-a-quadratic-algebra-and-an-order-three-inertia-operator)
  - [2.3 Quadratic induction and the meaning of the name](#23-quadratic-induction-and-the-meaning-of-the-name)
  - [2.4 The conductor is exactly two](#24-the-conductor-is-exactly-two)
- [3. Normal forms at 2](#3-normal-forms-at-2)
  - [3.1 The standard tame pair](#31-the-standard-tame-pair)
  - [3.2 Classification with fixed inertia](#32-classification-with-fixed-inertia)
  - [3.3 The determinant equation is a norm equation](#33-the-determinant-equation-is-a-norm-equation)
  - [3.4 Existence over every coefficient ring](#34-existence-over-every-coefficient-ring)
- [4. Liftability of the condition at 2](#4-liftability-of-the-condition-at-2)
  - [4.1 Lifting the order-three action](#41-lifting-the-order-three-action)
  - [4.2 Correcting Frobenius while fixing determinant](#42-correcting-frobenius-while-fixing-determinant)
  - [4.3 Strict conjugacy and a quadratic Hilbert 90 lemma](#43-strict-conjugacy-and-a-quadratic-hilbert-90-lemma)
  - [4.4 Formal smoothness and uniqueness](#44-formal-smoothness-and-uniqueness)
- [5. Tangent and obstruction calculations at 2](#5-tangent-and-obstruction-calculations-at-2)
  - [5.1 The adjoint representation](#51-the-adjoint-representation)
  - [5.2 The fixed-determinant tangent vanishes](#52-the-fixed-determinant-tangent-vanishes)
  - [5.3 Ambient obstruction vanishing](#53-ambient-obstruction-vanishing)
  - [5.4 Framed and unframed local rings](#54-framed-and-unframed-local-rings)
- [6. Finite flatness at the coefficient prime](#6-finite-flatness-at-the-coefficient-prime)
  - [6.1 Why a generic representation is not enough](#61-why-a-generic-representation-is-not-enough)
  - [6.2 The finite-flat deformation condition](#62-the-finite-flat-deformation-condition)
  - [6.3 Exactness and coefficient change](#63-exactness-and-coefficient-change)
  - [6.4 The low-weight classification](#64-the-low-weight-classification)
- [7. Tangent theory at the coefficient prime](#7-tangent-theory-at-the-coefficient-prime)
  - [7.1 First-order lifts as integral self-extensions](#71-first-order-lifts-as-integral-self-extensions)
  - [7.2 The filtered-module tangent complex](#72-the-filtered-module-tangent-complex)
  - [7.3 The dimension formula](#73-the-dimension-formula)
  - [7.4 The ordinary unit calculation](#74-the-ordinary-unit-calculation)
- [8. Liftability at the coefficient prime](#8-liftability-at-the-coefficient-prime)
  - [8.1 Lifting filtrations and divided Frobenius](#81-lifting-filtrations-and-divided-frobenius)
  - [8.2 Fixing the cyclotomic determinant](#82-fixing-the-cyclotomic-determinant)
  - [8.3 Why the restricted obstruction map is zero](#83-why-the-restricted-obstruction-map-is-zero)
  - [8.4 The finite-flat local rings](#84-the-finite-flat-local-rings)
- [9. The local package](#9-the-local-package)
  - [9.1 What a usable local condition must prove](#91-what-a-usable-local-condition-must-prove)
  - [9.2 The two distinguished places](#92-the-two-distinguished-places)
  - [9.3 Minimal conditions elsewhere](#93-minimal-conditions-elsewhere)
  - [9.4 A dimension and obstruction ledger](#94-a-dimension-and-obstruction-ledger)
- [10. The universal global problem](#10-the-universal-global-problem)
  - [10.1 Global hypotheses](#101-global-hypotheses)
  - [10.2 The hardly-ramified minimal functor](#102-the-hardly-ramified-minimal-functor)
  - [10.3 Closedness and the universal ring](#103-closedness-and-the-universal-ring)
  - [10.4 The global tangent space](#104-the-global-tangent-space)
- [11. Compatibility and stability](#11-compatibility-and-stability)
  - [11.1 Change of coefficients](#111-change-of-coefficients)
  - [11.2 Duality and fixed determinant](#112-duality-and-fixed-determinant)
  - [11.3 The integral type lattice at 2](#113-the-integral-type-lattice-at-2)
  - [11.4 Base change of local fields](#114-base-change-of-local-fields)
- [12. The hardly-ramified local-condition theorem](#12-the-hardly-ramified-local-condition-theorem)
  - [12.1 Main theorem](#121-main-theorem)
  - [12.2 Hypothesis ledger and boundary cases](#122-hypothesis-ledger-and-boundary-cases)
  - [12.3 Conclusion](#123-conclusion)

## 1. The two-place deformation problem

This opening chapter fixes the logical shape of the book. Before studying either local field, we separate residual data, determinant, framing, tangent spaces, and obstruction maps. That separation will let the two very different local constructions feed the same global deformation problem without conflating their proofs.

### 1.1 Why hardly ramified is a local design problem

A two-dimensional Galois representation can be globally complicated while being allowed very little local ramification. The phrase *hardly ramified* describes precisely such a situation. It does not mean unramified everywhere. At the coefficient prime, ramification forced by the cyclotomic determinant must be retained in an integral finite-flat form. At the prime $2$, the representation is allowed one particular tame, irreducible inertial shape of conductor two. Away from these places no new ramification is permitted.

The central problem of this book is to turn that sentence into a deformation condition. A useful local condition must do much more than name the characteristic-zero representations one hopes to obtain. It must make sense over every finite local coefficient algebra, survive reduction and extension of coefficients, be represented by a closed quotient of an ambient deformation space, have a calculable tangent space, and lift through small extensions. These requirements interact. For example, a conductor exponent alone does not specify an integral component, and a tangent-space calculation alone does not prove that integral models lift.

There are two very different mechanisms.

At $2$, the permitted inertia has order $3$. Since the coefficient characteristic will be at least $7$, averaging makes that inertia rigid. The only apparent parameter is Frobenius, and the fixed determinant removes it up to strict conjugacy. The resulting unframed local condition is rigid.

At the coefficient prime $\ell$, averaging is unavailable because the torsion has $\ell$-power order. Finite flatness is instead classified, over an unramified base and in Hodge range $[0,1]$, by exact filtered divided-Frobenius modules. A Hodge line and a Frobenius isomorphism do move, but they move smoothly. For $K/\mathbf Q_\ell$ unramified of degree $f$, the fixed-determinant unframed tangent has dimension $f+h-1$, where $h$ is the dimension of the residual endomorphism algebra.

Our aim is to prove these assertions in the exact form needed to impose them simultaneously on a universal global deformation. The local calculations are independent, but the final global condition is their fiber product.

### 1.2 Coefficients, determinant, and residual data

Let $\ell\ge 7$ be a prime. Let $E/\mathbf Q_\ell$ be a finite extension, let $\mathcal O$ be its ring of integers, let $\varpi$ be a uniformizer, and let

$$
k=\mathcal O/\varpi
$$

be its finite residue field. Write $\mathcal C_{\mathcal O}$ for the category of complete Noetherian local $\mathcal O$-algebras with residue field $k$, and $\operatorname{Art}_{\mathcal O}$ for its Artinian objects.

For a profinite group $G$ and a continuous representation

$$
\bar\rho:G\longrightarrow\operatorname{GL}_2(k),
$$

put

$$
\operatorname{ad}\bar\rho=\operatorname{End}_k(k^2),
\qquad
\operatorname{ad}^0\bar\rho
=\{X:\operatorname{tr}X=0\},
$$

with $G$ acting by conjugation. Since $2$ is a unit in $k$, there is a $G$-equivariant direct sum

$$
\operatorname{ad}\bar\rho
=kI\oplus\operatorname{ad}^0\bar\rho. \tag{1.1}
$$

Fix a continuous character

$$
\delta:G\longrightarrow\mathcal O^\times
$$

lifting $\det\bar\rho$. A deformation over $A\in\operatorname{Art}_{\mathcal O}$ is a continuous lift $\rho_A:G\to\operatorname{GL}_2(A)$, considered up to conjugation by $1+M_2(\mathfrak m_A)$. It has **fixed determinant** if $\det\rho_A=\delta$. A framed deformation retains the chosen basis and is not divided by strict conjugacy.

The global application uses

$$
\delta=\chi_\ell,
$$

the $\ell$-adic cyclotomic character. We use arithmetic Frobenius. Thus at a prime $p\ne\ell$,

$$
\chi_\ell(\phi_p)=p. \tag{1.2}
$$

At the coefficient prime we allow a slightly more general unramified local field $K/\mathbf Q_\ell$ while proving the local theorem. The global problem over $\mathbf Q$ then uses $K=\mathbf Q_\ell$ and $f=1$.

### 1.3 Tangents, liftability, and obstruction maps

The dual numbers $k[\epsilon]/(\epsilon^2)$ isolate the first derivative of a deformation condition. Every first-order lift can be written

$$
\rho_\epsilon(g)=(1+\epsilon c(g))\bar\rho(g).
$$

Multiplicativity is equivalent to

$$
c(gh)=c(g)+\bar\rho(g)c(h)\bar\rho(g)^{-1},
$$

so $c$ is a continuous $1$-cocycle with values in $\operatorname{ad}\bar\rho$. Strict conjugation by $1+\epsilon X$ changes $c$ by the coboundary

$$
g\longmapsto X-\bar\rho(g)X\bar\rho(g)^{-1}.
$$

The unframed tangent space is therefore $H^1(G,\operatorname{ad}\bar\rho)$. Differentiating determinant gives

$$
\det(1+\epsilon X)=1+\epsilon\operatorname{tr}X,
$$

so, in our odd two-dimensional setting, the fixed-determinant tangent is

$$
H^1(G,\operatorname{ad}^0\bar\rho). \tag{1.3}
$$

A local condition $\mathcal D$ determines a subspace

$$
L_{\mathcal D}\subseteq H^1(G,\operatorname{ad}^0\bar\rho).
$$

This subspace records first-order membership, but it is not the whole deformation problem. If

$$
A'\twoheadrightarrow A,
\qquad J=\ker(A'\to A),
\qquad \mathfrak m_{A'}J=0,
$$

is a small extension, an ambient lift has a factor-set obstruction in

$$
H^2(G,\operatorname{ad}^0\bar\rho)\otimes_kJ.
$$

A constrained condition has its own obstruction map into this group, or into a more economical obstruction space. Formal smoothness means that every object of the condition over $A$ lifts to an object of the condition over $A'$. It follows if the complete ambient $H^2$ vanishes, but it can also follow from an explicit constrained lifting construction even when the ambient group is nonzero. We will encounter both patterns: ambient vanishing at $2$, and explicit integral liftability at $\ell$.

## 2. The distinguished local type at 2

The prime $2$ contributes the most rigid local datum, but its name conceals its structure. This chapter derives the type from the tame Frobenius relation, identifies it with unramified-quadratic induction, and proves its conductor. The result supplies the arithmetic meaning that the matrix calculations of the next chapters will preserve integrally.

### 2.1 The tame quotient and Frobenius convention

Let $G_2=G_{\mathbf Q_2}$. Write $P_2$ for wild inertia and choose a tame generator $\tau$ together with a lift $\phi$ of arithmetic Frobenius. The tame quotient has the relation

$$
\phi\tau\phi^{-1}=\tau^2. \tag{2.1}
$$

Because $P_2$ is pro-$2$ and our coefficient rings have odd residue characteristic, any fixed finite wild action is rigid under infinitesimal deformation. The hardly-ramified condition kills $P_2$ entirely. Its local representations therefore factor through the quotient generated by $\tau$ and $\phi$ subject to (2.1).

The residue cardinality $2$ has a striking consequence. The two nontrivial characters of a cyclic group of order $3$ are exchanged by squaring. Thus a two-dimensional representation can have inertia eigencharacters $\eta$ and $\eta^{-1}$ while Frobenius interchanges their lines. The representation is irreducible as a representation of the full decomposition group even though its restriction to inertia splits after adjoining a primitive cube root of unity.

One should contrast this with two nearby shapes. Trivial tame inertia has conductor zero and leaves the whole two-dimensional space fixed. A nontrivial tame unipotent block, possible in an $\ell$-adic family when the tame $\mathbf Z_\ell$-direction is used, fixes a line and has conductor one. The order-three quadratic type fixes no line and has conductor two. These three cases are separated by fixed-space rank, not merely by the assertion that inertia is nontrivial.

There is also a reason order three, rather than an arbitrary odd order, is canonical over $\mathbf Q_2$. If a tame character has order $m$, Frobenius sends it to its square. An orbit of length two requires

$$
2^2\equiv1\pmod m,
\qquad 2\not\equiv1\pmod m.
$$

The smallest solution is $m=3$. For this orbit the two characters already exhaust the nontrivial characters of $C_3$, and their sum and product are integral: the characteristic polynomial is $X^2+X+1$. No choice of character values is needed to define the type over the original coefficient ring.

This is the smallest nontrivial tame irreducible local type at $2$. It is exactly the shape needed here.

### 2.2 A quadratic algebra and an order-three inertia operator

For any $\mathcal O$-algebra $A$, define

$$
B_A=A[u]/(u^2+u+1). \tag{2.2}
$$

Since the discriminant is $-3$ and $\ell\ge7$, $B_A$ is a quadratic finite étale $A$-algebra. It may be split or connected; none of our arguments requires choosing a primitive cube root in $A$. We reserve $S_A$ for the coefficient algebra used at the prime $\ell$ in Chapter 6, so the two unrelated étale algebras cannot be confused.

Let

$$
T_0=
\begin{pmatrix}
0&-1\\
1&-1
\end{pmatrix}.
\tag{2.3}
$$

Then

$$
T_0^2+T_0+I=0,
\qquad T_0^3=I,
\qquad \det T_0=1,
\qquad \operatorname{tr}T_0=-1. \tag{2.4}
$$

The $A$-subalgebra $A[T_0]\subset M_2(A)$ is canonically $B_A$. The nontrivial $A$-automorphism $\sigma$ of $B_A$ is given by

$$
\sigma(u)=u^2=-1-u. \tag{2.5}
$$

Thus the two roots of $X^2+X+1$ are the two nontrivial order-three characters, and $\sigma$ exchanges them.

Every residual matrix with characteristic polynomial $X^2+X+1$ is cyclic and is conjugate over $k$ to $\bar T_0$. For local calculations we fix such a residual basis once and for all. If the representation was initially presented in another basis, transport all framed objects by a fixed lift of the residual change of basis. The unframed condition is unaffected.

We say that a representation $\rho_A:G_2\to\operatorname{GL}_2(A)$ has **tame-quadratic type** if

$$
\rho_A(P_2)=1,
\qquad
\rho_A(\tau)^2+\rho_A(\tau)+I=0. \tag{2.6}
$$

The second equation forces $\rho_A(\tau)^3=I$ and excludes the trivial order-three root. Because $B_A$ is étale, the associated rank-two $A[C_3]$-module is locally the regular pair of nontrivial characters and is rigid under nilpotent thickening.

The definition is independent of the compatible tame generator. Replacing $\tau$ by another generator raises its order-three image to the first or second power. Both $T$ and $T^2=-I-T$ satisfy the same polynomial, and wild inertia remains trivial. It is also invariant under conjugacy. Hence (2.6) is an intrinsic condition on the local representation, despite its convenient matrix presentation.

### 2.3 Quadratic induction and the meaning of the name

The adjective *quadratic* can be misunderstood. It does not mean that inertia acts through a quadratic character. A ramified quadratic character at $2$ is wild, not tame. Here quadratic refers to the unramified quadratic extension and to the quadratic étale centralizer (2.2).

Let $L/\mathbf Q_2$ be the unramified quadratic extension. Its residue field is $\mathbf F_4$, whose multiplicative group has order $3$. Choose a nontrivial character

$$
\theta:W_L\longrightarrow \overline E^\times
$$

whose restriction to tame inertia factors through $\mathbf F_4^\times$. The nontrivial element $s\in\operatorname{Gal}(L/\mathbf Q_2)$ sends $\theta$ to $\theta^2=\theta^{-1}$, so $\theta\ne\theta^s$. Hence

$$
\operatorname{Ind}_{W_L}^{W_{\mathbf Q_2}}\theta \tag{2.7}
$$

is irreducible and has inertia characters $\theta$ and $\theta^{-1}$. Conversely, a tame two-dimensional representation satisfying (2.6) has these two inertia characters after scalar extension, and Frobenius interchanges them by (2.1). Choosing either line identifies the index-two stabilizer with $W_L$, recovering (2.7). Thus the matrix condition and the unramified-quadratic induced description are equivalent.

This equivalence also identifies the associated depth-zero dihedral local type. The integral type lattice attached to the regular character of $\mathbf F_4^\times$ will reappear in Section 11.3.

If the coefficient ring contains a primitive cube root $\zeta$, the representation becomes especially concrete. In an inertia eigenbasis one may take

$$
T=
\begin{pmatrix}\zeta&0\\0&\zeta^{-1}\end{pmatrix},
\qquad
F=
\begin{pmatrix}0&1\\-2&0\end{pmatrix}. \tag{2.8}
$$

Then $FTF^{-1}=T^{-1}=T^2$ and $\det F=2$. Thus (2.8) has cyclotomic determinant on arithmetic Frobenius. The integral normal form using $T_0$ is preferable because it exists without adjoining $\zeta$, but the eigenbasis makes the quadratic induction visible.

### 2.4 The conductor is exactly two

We now justify the conductor label rather than treating it as terminology.

**Proposition 2.1 (conductor calculation).** Let $V$ be a two-dimensional characteristic-zero representation of $G_2$ of tame-quadratic type. Then its Swan conductor is zero and its Artin conductor exponent is $2$.

**Proof strategy.** Tameness eliminates all positive ramification groups. The order-three inertia operator has no fixed vector, so the entire contribution is the codimension of inertia invariants.

**Proof.** Since $P_2$ acts trivially, the representation is tamely ramified. Therefore

$$
\operatorname{Sw}(V)=0
$$

and

$$
a_2(V)=\dim V-\dim V^{I_2}.
$$

If $v$ were fixed by inertia, then $T v=v$, where $T=\rho(\tau)$. Applying $T^2+T+I=0$ would give $3v=0$. Characteristic zero implies $v=0$. Hence $V^{I_2}=0$ and

$$
a_2(V)=2. \qedhere
$$

The proof shows more. In any coefficient characteristic different from $3$, the rank of the inertia-fixed submodule remains zero. Thus every finite-level member of the condition has constant tame conductor in the natural invariant-rank sense. Conductor constancy follows from the fixed order-three action; it is not being imposed as an independent numerical equation.

The converse from the integer $a_2(V)=2$ to our type is false. A wildly ramified character can have conductor two, and other tame representations with no fixed vector can have the same tame conductor. Even within two-dimensional tame representations, conductor remembers only the codimension of invariants. It forgets the order-three polynomial, the Frobenius interchange, and the quadratic inducing field. This is why the deformation condition records the full type and derives its conductor afterward.

## 3. Normal forms at 2

To prove liftability and compute a deformation ring, a qualitative inertial label must be replaced by coordinates. The quadratic centralizer of the inertia operator provides those coordinates. This chapter classifies Frobenius intertwiners, translates determinant into norm, and proves that the required norm values exist over every Artinian coefficient ring.

### 3.1 The standard tame pair

Set

$$
W=
\begin{pmatrix}
0&1\\
1&0
\end{pmatrix}.
\tag{3.1}
$$

A direct multiplication gives

$$
WT_0W^{-1}=T_0^2,
\qquad W^2=I,
\qquad \det W=-1. \tag{3.2}
$$

Consequently every matrix $C\in B_A^\times=A[T_0]^\times$ gives a solution

$$
T=T_0,
\qquad F=CW
\tag{3.3}
$$

of the tame relation $FTF^{-1}=T^2$. Conversely, the entire set of Frobenius intertwiners has this form.

**Lemma 3.1 (intertwiner torsor).** Let $A$ be local and let $F\in\operatorname{GL}_2(A)$ satisfy

$$
FT_0F^{-1}=T_0^2.
$$

Then there is a unique $C\in B_A^\times$ such that $F=CW$.

**Proof.** Since $W T_0 W^{-1}=T_0^2$, the matrix $FW^{-1}$ commutes with $T_0$. The centralizer of a cyclic $2\times2$ matrix is the algebra it generates: writing an arbitrary matrix and solving $XT_0=T_0X$ gives $X=aI+bT_0$. Thus $FW^{-1}\in B_A$. It is invertible because $F$ and $W$ are, so it lies in $B_A^\times$. Uniqueness is immediate. $\square$

The lemma makes the geometry transparent. Fixing the inertia operator leaves a torsor under the smooth two-dimensional torus $B_A^\times$. The determinant will cut its norm-one direction.

It is worth locating the two apparent dimensions before quotienting. The fixed-norm elements of $B_A^\times$ form a one-dimensional formal torus. Conjugation by the centralizer also has a one-dimensional effective norm-one direction, because scalar centralizer elements act trivially. The two directions cancel in the unframed quotient. The three remaining framed variables later come from moving the chosen basis relative to the unique representation, not from changing its isomorphism class.

### 3.2 Classification with fixed inertia

We first show that condition (2.6) really fixes inertia up to strict conjugacy.

**Lemma 3.2 (rigidity of the quadratic inertia operator).** Let $A\in\operatorname{Art}_{\mathcal O}$, and let $T\in\operatorname{GL}_2(A)$ reduce to $\bar T_0$ and satisfy

$$
T^2+T+I=0.
$$

Then there exists $U\in1+M_2(\mathfrak m_A)$ such that

$$
UTU^{-1}=T_0.
$$

The conjugator is unique up to left multiplication by an element of $1+\mathfrak m_AB_A$.

**Proof strategy.** Regard $A^2$ as a module over the étale quadratic algebra $B_A$. Its reduction is free of rank one over $B_k$, and Nakayama lifts a generator.

**Proof.** Let $u\in B_A$ act on $A^2$ as $T$. The relation gives a $B_A$-module structure. Modulo $\mathfrak m_A$, this module is the standard rank-one $B_k$-module because $\bar T=\bar T_0$. Choose a vector $v$ lifting the standard generator. Then $v,Tv$ reduce to a $k$-basis, so they form an $A$-basis. The map

$$
B_A\longrightarrow A^2,
\qquad a+bu\longmapsto av+bTv
$$

is therefore a $B_A$-linear isomorphism. Comparing this basis with the standard basis gives a conjugator congruent to the identity. Two such identifications differ by a $B_A$-linear automorphism, namely multiplication by an element of $B_A^\times$ congruent to $1$. $\square$

It follows that every tame-quadratic lift is strictly equivalent to one with the standard inertia matrix and Frobenius $CW$. No eigenvalue or splitting-field choice has entered.

### 3.3 The determinant equation is a norm equation

For $C=aI+bT_0$, its determinant is

$$
\det C=a^2-ab+b^2. \tag{3.4}
$$

This is exactly the norm

$$
N_{B_A/A}(a+bu)
=(a+bu)(a+bu^2).
$$

Since $\det W=-1$, the fixed-determinant equation for $F=CW$ is

$$
N_{B_A/A}(C)=-\delta(\phi). \tag{3.5}
$$

The inertia determinant is automatically one by (2.4), so compatibility also requires $\delta|_{I_2}=1$. This holds for $\delta=\chi_\ell$ because $\ell\ne2$.

The derivative of norm at a unit $C$ is, after translating to the identity, the trace

$$
\operatorname{Tr}_{B_k/k}:B_k\longrightarrow k. \tag{3.6}
$$

As $B_k/k$ is finite étale of degree two and $2\ne0$ in $k$, this trace is surjective: it sends $1$ to $2$. Therefore every fixed-norm fiber is formally smooth of relative dimension one.

### 3.4 Existence over every coefficient ring

We need more than infinitesimal smoothness: a compatible determinant value must actually be a norm.

**Lemma 3.3 (surjectivity of the quadratic norm on units).** Let $A$ be an Artinian local $\mathcal O$-algebra. Then

$$
N_{B_A/A}:B_A^\times\longrightarrow A^\times
$$

is surjective.

**Proof.** On residue fields there are two cases. If $B_k\simeq k\times k$, the norm is multiplication and is visibly onto. If $B_k$ is a quadratic field, its multiplicative group is cyclic and the finite-field norm $x\mapsto x^{|k|+1}$ maps onto $k^\times$.

It remains to lift through nilpotents. Factor $A\to k$ into small extensions. For a small extension with kernel $J$, an element $1+x\in1+J B_A$ has norm

$$
N(1+x)=1+\operatorname{Tr}_{B_k/k}(x),
$$

because $J^2=0$. The trace is onto by (3.6), so any correction in $1+J$ is a norm. Induction proves surjectivity. $\square$

Taking a norm preimage of $-\delta(\phi)$ and using (3.3) constructs a tame-quadratic representation with determinant $\delta$. In particular, the condition is nonempty for the cyclotomic determinant, where $\delta(\phi)=2$.

## 4. Liftability of the condition at 2

Normal forms become deformation theory only when they survive nilpotent thickenings. We now solve every small-extension problem explicitly and then show that all solutions are strictly conjugate. This gives both formal smoothness and unframed uniqueness, two conclusions that a tangent count alone could not provide.

### 4.1 Lifting the order-three action

Let $A'\twoheadrightarrow A$ be a small extension in $\operatorname{Art}_{\mathcal O}$ with kernel $J$, and suppose $\rho_A$ has tame-quadratic type. We explain a lift without appealing to a dimension count.

By Lemma 3.2, after strict conjugacy we may assume

$$
\rho_A(\tau)=T_0,
\qquad
\rho_A(\phi)=C_AW.
$$

The same matrix $T_0$ over $A'$ lifts inertia and still satisfies $T_0^2+T_0+I=0$. This simple observation is the matrix form of prime-to-$\ell$ rigidity. More intrinsically, the idempotents of the finite étale algebra $B_A$ lift uniquely through nilpotent extensions, so the rank-one $B_A$-module lifts to the rank-one $B_{A'}$-module.

No wild action appears: we continue to send $P_2$ to $1$. Continuity follows because inertia has finite image and Frobenius generates a procyclic quotient.

### 4.2 Correcting Frobenius while fixing determinant

Choose any lift $\widetilde C\in B_{A'}^\times$ of $C_A$. Its norm may not yet equal $-\delta(\phi)$. The quotient

$$
r=-\delta(\phi)N(\widetilde C)^{-1}
$$

lies in $1+J$. By the infinitesimal norm calculation, choose $x\in JB_{A'}$ with

$$
\operatorname{Tr}_{B_k/k}(x)=r-1.
$$

Then $C'=(1+x)\widetilde C$ satisfies

$$
N(C')=-\delta(\phi).
$$

Consequently

$$
\rho_{A'}(\tau)=T_0,
\qquad
\rho_{A'}(\phi)=C'W
$$

lifts $\rho_A$, satisfies the tame relation, and has determinant $\delta$. Thus every small-extension lifting problem inside the condition is solvable.

### 4.3 Strict conjugacy and a quadratic Hilbert 90 lemma

Liftability does not yet show that the unframed condition has no parameter. For that we need to compare two fixed-norm Frobenius intertwiners.

Conjugation by $D\in B_A^\times$ fixes $T_0$ and transforms

$$
CW\longmapsto D(CW)D^{-1}
=DC\sigma(D)^{-1}W. \tag{4.1}
$$

Thus two elements $C,C'\in B_A^\times$ with the same norm are conjugate precisely when

$$
C'C^{-1}=D\sigma(D)^{-1}. \tag{4.2}
$$

**Lemma 4.1 (strict quadratic Hilbert 90).** Let $A\in\operatorname{Art}_{\mathcal O}$. If $z\in B_A^\times$ satisfies

$$
N_{B_A/A}(z)=1
$$

and $z\equiv1\pmod{\mathfrak m_A}$, then there is $D\in1+\mathfrak m_AB_A$ such that

$$
z=D\sigma(D)^{-1}.
$$

**Proof strategy.** Solve successively over small extensions. The linearized map is $d\mapsto d-\sigma(d)$, whose image is exactly the trace-zero line.

**Proof.** The assertion is trivial over $k$. Suppose it holds over $A$ and lift across a small extension $A'\to A$ with kernel $J$. After using a lifted solution from $A$, the remaining element has the form $1+x$ with $x\in JB_{A'}$. The norm-one equation gives

$$
\operatorname{Tr}_{B_k/k}(x)=x+\sigma(x)=0.
$$

Because $2$ is invertible, take $d=x/2$. Then $\sigma(x)=-x$, so

$$
d-\sigma(d)=x.
$$

Conjugating by $1+d$ removes the defect, since

$$
(1+d)(1+\sigma(d))^{-1}=1+d-\sigma(d)=1+x.
$$

Induction proves the result. $\square$

This is the exact integral statement required for strict equivalence. It is stronger than an equality of characteristic-zero conjugacy classes and uses only that the quadratic algebra is étale and $2$ is a unit.

### 4.4 Formal smoothness and uniqueness

**Theorem 4.2 (local liftability at $2$).** Let $\ell\ge7$, let $\delta:G_2\to\mathcal O^\times$ be unramified, and suppose the residual representation has tame-quadratic type and determinant $\bar\delta$. Then:

1. the fixed-determinant tame-quadratic condition is stable under every coefficient map in $\operatorname{Art}_{\mathcal O}$;
2. it lifts through every small extension;
3. any two lifts over the same $A$ that reduce to the same residual representation are strictly equivalent;
4. the unframed functor has exactly one element over every $A$.

**Proof.** The defining equations have coefficients in $\mathcal O$, so base change preserves them. Sections 4.1 and 4.2 prove small-extension liftability. Put two lifts into standard inertia form. Their Frobenius matrices are $CW$ and $C'W$ with the same norm. Their ratio $z=C'C^{-1}$ has norm one and reduces to one. Lemma 4.1 supplies a strict centralizing conjugator carrying one to the other. Nonemptiness follows from Lemma 3.3, so there is exactly one strict-equivalence class over every $A$. $\square$

The theorem exhibits the obstruction map of this constrained problem as zero. In the next chapter we prove the stronger fact that the entire fixed-determinant ambient obstruction group is already zero in the stated range.

## 5. Tangent and obstruction calculations at 2

The explicit lifting theorem already proves that the constrained obstruction map vanishes. Cohomology explains why the result is even stronger in characteristic at least $7$: the fixed-determinant ambient tangent and obstruction groups both vanish. The calculation also distinguishes genuine deformation parameters from the three directions contributed only by a frame.

### 5.1 The adjoint representation

Let $\bar V$ be the residual tame-quadratic representation and put

$$
M=\operatorname{ad}^0\bar V.
$$

The centralizer of $\bar T_0$ in $M_2(k)$ is $B_k=k[\bar T_0]$. Its trace-zero part is the line generated by

$$
H=2\bar T_0+I. \tag{5.1}
$$

Indeed $\operatorname{tr}H=2(-1)+2=0$. The involution $\sigma$ sends

$$
H\longmapsto 2(-I-\bar T_0)+I=-H. \tag{5.2}
$$

Since Frobenius acts on the inertia centralizer by $\sigma$, we obtain

$$
M^{I_2}=kH,
\qquad \phi(H)=-H. \tag{5.3}
$$

For the full adjoint module,

$$
(\operatorname{ad}\bar V)^{I_2}=kI\oplus kH,
$$

with Frobenius eigenvalues $1$ and $-1$. The full decomposition-group centralizer is therefore only $kI$. In fact $\bar V$ is absolutely irreducible as a $G_2$-representation, even if the inertia polynomial is already split over $k$.

The last assertion is not being inferred merely from the size of the
centralizer. After extending scalars to an algebraic closure of $k$, inertia
has two distinct eigenlines, with characters of order three. Every
inertia-stable line is one of those eigenlines, while arithmetic Frobenius
interchanges them by the squaring relation. Hence neither line is
$G_2$-stable. The scalar extension of $\bar V$ is irreducible, which is
exactly absolute irreducibility.

### 5.2 The fixed-determinant tangent vanishes

For any finite $G_2$-module $N$, unramified cohomology is

$$
H^1_{\mathrm{ur}}(\mathbf Q_2,N)
\simeq N^{I_2}/(\phi-1)N^{I_2}. \tag{5.4}
$$

A fixed finite prime-to-$\ell$ inertial type has precisely this tangent space: a first-order cocycle may be changed by a coboundary so that it vanishes on inertia, and only the Frobenius value remains.

Applying (5.4) to $M$ and using (5.3), the operator $\phi-1$ is multiplication by $-2$. Since $\ell$ is odd, it is invertible. Hence

$$
L_2
=H^1_{\mathrm{tq}}(\mathbf Q_2,M)
=H^1_{\mathrm{ur}}(\mathbf Q_2,M)
=0. \tag{5.5}
$$

For comparison, the full adjoint fixed-type tangent is the scalar line coming from $kI$, because $\phi-1$ vanishes there. Fixing determinant removes it: the trace of $I$ is $2$, a unit. This gives a second derivation of (5.5).

The vanishing is not a dimension guessed from rigidity. It is the explicit Frobenius cokernel calculation, and it records why odd coefficient characteristic is essential.

### 5.3 Ambient obstruction vanishing

Tate local duality for finite modules, applied away from the residue
characteristic, says

$$
\dim_k H^2(\mathbf Q_2,M)
=\dim_k H^0(\mathbf Q_2,M^*(1)). \tag{5.6}
$$

The trace pairing is nondegenerate on $M=\operatorname{ad}^0\bar V$
because $2$ is invertible, and it identifies $M^*$ with $M$. Thus we must
compute invariants in $M(1)$. Any such invariant first lies in
$(M(1))^{I_2}=M^{I_2}(1)=kH(1)$, since the cyclotomic character is
unramified at $2$. Arithmetic Frobenius acts on that character by $2$ and
on $H$ by $-1$, so on this line it acts by

$$
(-1)\cdot2=-2. \tag{5.7}
$$

An invariant could exist only if $-2=1$ in $k$, that is, only in characteristic $3$. Since $\ell\ge7$,

$$
H^0(\mathbf Q_2,M(1))=0
$$

and hence

$$
H^2(\mathbf Q_2,M)=0. \tag{5.8}
$$

The local Euler characteristic away from $\ell$ gives

$$
h^1(M)=h^0(M)+h^2(M).
$$

Both terms on the right vanish: the full local centralizer is scalar, so $H^0(\mathbf Q_2,M)=0$, and (5.8) kills the second. Therefore

$$
H^1(\mathbf Q_2,M)=0. \tag{5.9}
$$

Thus in this range the tame-quadratic fixed-determinant condition is not merely a smooth component of a larger infinitesimal space. It is the unique fixed-determinant local deformation.

### 5.4 Framed and unframed local rings

**Theorem 5.1 (the local ring at $2$).** Under the hypotheses of Theorem 4.2, the unframed fixed-determinant local deformation functor is represented by $\mathcal O$, and the framed functor is represented noncanonically by

$$
R_2^{\square,\mathrm{tq},\delta}
\simeq \mathcal O[[Y_1,Y_2,Y_3]]. \tag{5.10}
$$

The same rings represent the unrestricted fixed-determinant local problem.

**Proof strategy.** Theorem 4.2 identifies one unframed object over every Artinian coefficient ring. A frame varies through the formal quotient of $\operatorname{GL}_2$ by the scalar centralizer, which has dimension three. Ambient $H^1$ and $H^2$ vanishing show that no omitted fixed-determinant component remains.

**Proof.** The constant one-point functor is represented by $\mathcal O$. The centralizer of the residual representation is $k^\times$, and scalar changes of basis act trivially. The formal change-of-frame space therefore has tangent

$$
M_2(k)/kI,
$$

of dimension three. The general framing theorem gives a formally smooth morphism of relative dimension three from the framed ring to the unframed ring, proving (5.10).

Alternatively, the framed tangent is $Z^1(\mathbf Q_2,M)$. Since $H^1(M)=0$ and $H^0(M)=0$, all three dimensions are coboundaries. Equation (5.8) makes the unrestricted fixed-determinant ambient functor formally smooth, while (5.9) makes it unframed rigid. To justify the final identification of functors, factor any Artinian coefficient ring down to $k$ through small extensions. At each step formal smoothness gives an ambient lift and the zero tangent gives at most one strict-equivalence class of such lifts. Theorem 4.2 supplies a tame-quadratic lift at the same step. The unique ambient class is therefore that constrained class. Induction proves equality on every Artinian ring, both unframed and, after adjoining a frame, framed. $\square$

This theorem is the cleanest local contribution to the global problem: the prime $2$ contributes neither an unframed tangent direction nor a local obstruction.

## 6. Finite flatness at the coefficient prime

At the coefficient prime the order of the torsion is no longer invertible on the base, so the tame averaging argument disappears. The replacement is integral geometry. This chapter defines the condition using marked finite-flat models, establishes its coefficient stability, and recalls the exact low-weight classification that supplies coordinates.

### 6.1 Why a generic representation is not enough

Let $K/\mathbf Q_\ell$ be finite with valuation ring $R_K$. If $A\in\operatorname{Art}_{\mathcal O}$ and $V_A$ is free of rank two over $A$ with a continuous $G_K$-action, then its underlying finite module determines a finite étale group over $K$. To say that $V_A$ is **finite flat** means that this generic group extends to a finite locally free commutative group scheme over $R_K$ carrying the $A$-action.

The integral model is essential. At the coefficient prime, finite flat does not mean unramified: roots of unity give the basic ramified example. Nor do finite-flat diagonal characters force every extension between them to be finite flat. The middle extension must itself have an integral model. Likewise, a rational representation with the desired Hodge labels does not select an integral lattice, and finite flatness of one quotient does not by itself produce compatible models at all higher levels.

Several exact operations are nevertheless available once a model exists. A stable submodule closes schematically inside a chosen model and gives a finite-flat subgroup; the represented quotient is finite flat. Cartier duality produces the Tate-twisted dual. Coefficient actions must be retained on the model, and nonflat coefficient quotients must be formed by closing the generic relation submodule before taking the represented quotient.

These facts explain the formulation below. The local condition is existential, but it is existential in a category with enough exactness to behave under deformation.

There are four logical layers that must remain distinct:

$$
\begin{array}{c|l}
\text{layer}&\text{datum}\\ \hline
\text{generic}&\text{a finite }A[G_K]\text{-module }V_A\\
\text{integral}&\text{a marked finite-flat model }(\mathcal G,\iota)\\
\text{predicate}&\text{existence of at least one such model}\\
\text{rigidity}&\text{uniqueness of the marked model}
\end{array} \tag{6.1a}
$$

General finite-flat theory supplies the first three layers but not the fourth. In the unramified low-weight range used here, low-ramification full faithfulness supplies the fourth as well. If two models have the same marked generic fiber, the generic identity extends in both directions; faithfulness makes the composites the identity. Every generic coefficient endomorphism similarly extends uniquely. This is the exact reason that the existential deformation condition satisfies coefficient fiber-product gluing in Chapters 7--8.

Two examples mark the range of the condition. The constant group $\underline{\mathbf Z/\ell\mathbf Z}$ gives the trivial character, while $\mu_\ell$ gives the cyclotomic character; their generic representations differ over an unramified $K$ because $K$ cannot contain a primitive $\ell$th root of unity. Torsion of an elliptic curve with good reduction gives a rank-two finite-flat representation that may be ordinary or local-local on the special fiber. Thus the condition includes reducible and irreducible residual shapes and is not an ordinarity condition.

### 6.2 The finite-flat deformation condition

Assume from now through Chapter 8 that

$$
K/\mathbf Q_\ell\text{ is unramified of degree }f,
\qquad \ell>2. \tag{6.1}
$$

Let

$$
\bar\rho_\ell:G_K\longrightarrow\operatorname{GL}_2(k)
$$

be finite flat with

$$
\det\bar\rho_\ell=\bar\chi_\ell.
$$

For $A\in\operatorname{Art}_{\mathcal O}$, define $\mathcal D_\ell^{\mathrm{fl},\chi}(A)$ to be the set of strict-equivalence classes of lifts $\rho_A$ such that

$$
\det\rho_A=\chi_\ell
$$

and the $A[G_K]$-module $A^2$ admits an $A$-linear finite-flat model over $R_K$. The framed version retains the basis.

This condition is intrinsic: conjugating $\rho_A$ transports the generic marking of a model. It is also compatible with reduction to $k$, because the residual representation was assumed finite flat. The determinant is not an extra afterthought. In rank two it specifies the exterior pairing target and forces Hodge type $(0,1)$ in the low-weight classification.

### 6.3 Exactness and coefficient change

**Proposition 6.1 (coefficient stability).** If $V_A$ is finite flat and $A\to B$ is a homomorphism in $\operatorname{Art}_{\mathcal O}$, then

$$
B\otimes_A V_A
$$

is finite flat as a $B[G_K]$-module. The assertion remains true when $A\to B$ is not flat.

**Proof.** Choose an $A$-linear finite-flat model $\mathcal G$. If $B=A/I$, take the generic submodule $IV_A\subset V_A$, close it inside $\mathcal G$, and form the finite-flat quotient. Its generic module is $V_A/IV_A=B\otimes_AV_A$, and the quotient inherits the $B$-action.

For a general homomorphism $A\to B$, choose a finite presentation of the $A$-module $B$. It presents $B\otimes_AV_A$ as the quotient of a finite direct sum of copies of $V_A$ by the generic relation submodule arising from the presentation and from multiplication in $B$. Model the direct sum by the corresponding product of copies of $\mathcal G$, take schematic closure of that relation submodule, and then take the represented finite-flat quotient. The multiplication relations descend to commuting endomorphisms and give the quotient its $B$-action. Its generic module is exactly $B\otimes_AV_A$. Independence of the chosen presentation follows because the resulting generic module, rather than the presentation, characterizes the existential finite-flat predicate. $\square$

The proof deliberately avoids taking a raw scheme-theoretic kernel of multiplication by $I$, which need not be flat. Schematic closure and the represented quotient are the exact integral operations.

It follows immediately that $\mathcal D_\ell^{\mathrm{fl},\chi}$ is preserved by every coefficient map. Fiber-product compatibility is subtler because separately chosen models need not glue. Under (6.1), low-ramification full faithfulness supplies uniqueness of the model and removes that ambiguity.

### 6.4 The low-weight classification

We recall the precise prior theorem used in the rest of the book.

**Theorem 6.2 (integral low-weight classification).** Under (6.1), finite-flat $\ell$-power torsion groups over $R_K$ are exactly the generic realizations of torsion divided filtered modules of weights $[0,1]$. The correspondence is exact and fully faithful, reverses arrows before the standard covariant dualization, preserves coefficient actions, Cartier duality, perfect pairings, unramified base change, and compatible coefficient quotients. In rank two with cyclotomic determinant, the covariant form over $A$ is a triple

$$
(M,L,\Phi), \tag{6.2}
$$

where

- $M$ is projective of rank two over $S_A=R_K\otimes_{\mathbf Z_\ell}A$;
- $L\subset M$ is a direct-summand line at each of the $f$ residue embeddings;
- with
  $$
  D_L(M)=\frac{L\oplus M}{\langle(\ell x,-x):x\in L\rangle},
  $$
  the divided Frobenius is an isomorphism
  $$
  \Phi:S_A\otimes_{\sigma,S_A}D_L(M)\xrightarrow{\sim}M.
  $$

The construction commutes with arbitrary Artinian coefficient reduction. Every triple has a unique marked finite-flat realization.

The deep part of this theorem is the integral classification and representability of its solution groups. Its hypotheses are exact: the base is unramified, the residue field is perfect, the weight interval is $[0,1]$, and $\ell>2$. The uniqueness statement uses low-ramification full faithfulness, since the absolute ramification index $1$ is less than $\ell-1$.

Let us also justify why cyclotomic determinant selects one Hodge line. A rank-one finite-flat object in this category has weight zero or weight one at each residue embedding. Exact tensor compatibility for the determinant makes the filtration rank of the determinant equal to the sum of the two rank-one weights of the rank-two object. The cyclotomic character corresponds to weight one at every embedding. Hence

$$
\operatorname{rank}_{A}L_i=1 \tag{6.3}
$$

for every $i$. Neither rank zero nor rank two can occur at an embedding. This argument is integral: it uses the determinant pairing and exact filtration ranks, not merely a list of rational Hodge--Tate numbers.

The classification also closes a possible coefficient gap. An $A$-action on the generic representation extends uniquely to the model by full faithfulness, and its algebra relations remain true integrally by faithfulness. If $A\to A/I$ is nonflat, the classified object for the quotient is the admissible annihilator on the contravariant side; after the covariant dualization it is ordinary tensor reduction. This is why the triples in (6.2) really commute with all Artinian coefficient quotients.

For later calculations, one simple consequence is decisive. After a finite étale coefficient extension splitting $S_A$ into $f$ factors, the data become cyclic tuples

$$
(M_i,L_i,\Phi_i)_{i\in\mathbf Z/f\mathbf Z}, \tag{6.4}
$$

where $M_i\simeq A^2$, $L_i$ is a line, and

$$
\Phi_i:D_{L_i}(M_i)\xrightarrow{\sim}M_{i+1}.
$$

This is the coordinate system in which tangent and lifting arguments become elementary. Faithfully flat descent returns the conclusions to the original coefficient ring.

## 7. Tangent theory at the coefficient prime

The low-weight classification turns first-order finite-flat deformations into linear algebra, but the quotient by automorphisms and the determinant equation must be counted exactly. This chapter builds the tangent complex, proves its dimension formula for every residual shape, and checks the ordinary case against Kummer theory.

### 7.1 First-order lifts as integral self-extensions

Let $V=\bar V_\ell$ be the residual representation. A first-order deformation over $k[\epsilon]$ is an extension

$$
0\longrightarrow V\longrightarrow V_\epsilon
\longrightarrow V\longrightarrow0, \tag{7.1}
$$

where the first copy is $\epsilon V_\epsilon$. The ambient extension class lies in

$$
\operatorname{Ext}^1_{k[G_K]}(V,V)
\simeq H^1(K,\operatorname{ad}V).
$$

The deformation is finite flat exactly when (7.1) is the generic fiber of a faithfully flat exact sequence of coefficient-linear finite-flat models. Under the low-weight classification, this means that the corresponding self-extension of the residual filtered object is exact both on the underlying modules and on their Hodge lines.

This gives an intrinsic vector subspace

$$
H^1_{\mathrm{fl}}(K,\operatorname{ad}V)
\subseteq H^1(K,\operatorname{ad}V). \tag{7.2}
$$

It is a vector space because Baer sum, scalar multiplication, pullback, and pushout exist in the exact filtered category and commute with generic realization. Fixing determinant intersects (7.2) with the kernel of trace. Since $\ell$ is odd, (1.1) identifies the result with

$$
H^1_{\mathrm{fl}}(K,\operatorname{ad}^0V). \tag{7.3}
$$

The notation does not mean the kernel of a restriction map to inertia. At the coefficient prime, principal-unit Kummer classes can be ramified and finite flat. The adjective records an integral extension condition.

There is a useful test for whether a proposed class belongs to (7.2). Choose a cocycle representative and form the middle representation (7.1). It is not enough to model a stable line and the quotient separately. One must model the middle term so that multiplication by $\epsilon$ is an integral endomorphism and the sequence is faithfully flat exact. Once such a middle model exists, schematic closure identifies the endpoint models and the exact filtered classification places the class in (7.2). This criterion prevents extension data from disappearing under semisimplification.

### 7.2 The filtered-module tangent complex

We calculate (7.3) using (6.4). Work temporarily over a coefficient extension that splits the $f$ embeddings. Choose a basis $(e_i,f_i)$ of each residual $M_i$ with

$$
L_i=ke_i.
$$

A first-order line is the graph of a map $L_i\to M_i/L_i$, contributing one scalar $x_i$. An invertible first-order perturbation of $\Phi_i$ contributes a matrix

$$
Y_i\in M_2(k),
$$

so the based deformation data have $5f$ parameters.

A change of basis $1+\epsilon X_i$ on $M_i$ acts on the line and on the two adjacent Frobenius maps. Linearizing produces a map

$$
d^0:\bigoplus_i M_2(k)
\longrightarrow
\bigoplus_i\bigl(\operatorname{Hom}(L_i,M_i/L_i)\oplus M_2(k)\bigr). \tag{7.4}
$$

The formula matters because ordinary conjugation would forget the cyclic
Witt-Frobenius shift. If $\bar\Phi_i$ denotes the residual divided-Frobenius
map, the line component of $d^0(X)$ is

$$
e\longmapsto X_i(e)\bmod L_i,
$$

and its matrix component at $i$ is

$$
X_{i+1}\bar\Phi_i-\bar\Phi_i\widetilde X_i.
$$

Here $\widetilde X_i$ is the differential of the canonical map induced on
$D_{L_i}(M_i)$ while the line itself moves. This formula is the
linearization of

$$
\Phi_i\longmapsto g_{i+1}\Phi_iD(g_i)^{-1};
$$

in particular, the target index is $i+1$. The kernel consists precisely of
infinitesimal endomorphisms of the residual filtered object. Full
faithfulness identifies this kernel with

$$
\operatorname{End}_{k[G_K]}(V).
$$

Put

$$
h=\dim_k\operatorname{End}_{k[G_K]}(V). \tag{7.5}
$$

Thus

$$
\operatorname{rank}d^0=4f-h. \tag{7.6}
$$

The determinant of a rank-two filtered object is a rank-one weight-one object. Fixing it imposes a single cyclic Frobenius equation, not one equation at every embedding. Infinitesimally this gives a surjective map

$$
d^1:\bigoplus_i\bigl(\operatorname{Hom}(L_i,M_i/L_i)\oplus M_2(k)\bigr)
\longrightarrow k. \tag{7.7}
$$

In adapted divided bases its value on matrix perturbations
$\dot\Phi_i$ is the logarithmic derivative

$$
d^1((\dot\Phi_i)_i)
=\sum_i\operatorname{tr}
(\bar\Phi_i^{-1}\dot\Phi_i).
$$

Line perturbations contribute no additional term: changing the chosen
complement adds a multiple of the filtration vector, whose exterior wedge
with that vector is zero. To see surjectivity concretely, take
$\dot\Phi_0=\bar\Phi_0\operatorname{diag}(a,0)$ and all other perturbations
zero. Then the displayed derivative equals $a$. Moreover $d^1d^0=0$.
Taking determinants in the gauge formula gives a cyclic sum of
$\operatorname{tr}X_{i+1}-\operatorname{tr}X_i$, which telescopes.

The fixed-determinant coarse tangent is the middle cohomology

$$
\ker d^1/\operatorname{im}d^0. \tag{7.8}
$$

This complex is not merely a parameter count. The exact low-weight
classification says that every first-order finite-flat deformation gives
such line and divided-Frobenius data, and that two data give the same
unframed deformation exactly when they differ by the displayed gauge
action. Its degree zero therefore records all automorphisms, its middle
term records all deformations, and its last map records exactly the one
determinant constraint. No extension class is lost on passing to filtered
data.

### 7.3 The dimension formula

**Theorem 7.1 (finite-flat tangent dimensions).** Under (6.1), let $V$ be rank two, finite flat, and of cyclotomic determinant. With $h$ as in (7.5),

$$
\dim_kH^1_{\mathrm{fl}}(K,\operatorname{ad}^0V)
=f+h-1. \tag{7.9}
$$

The framed fixed-determinant finite-flat tangent has dimension

$$
f+3. \tag{7.10}
$$

**Proof.** The middle based parameter space in (7.4) has dimension $5f$. By (7.7), its fixed-determinant kernel has dimension $5f-1$. Quotienting by the image of $d^0$, of dimension $4f-h$, gives

$$
(5f-1)-(4f-h)=f+h-1,
$$

proving (7.9).

For framed deformations one does not quotient by changes of the generic frame. The passage from unframed cocycles to framed cocycles adds the coboundary dimension

$$
\dim_k\operatorname{ad}^0V-dim_kH^0(K,\operatorname{ad}^0V).
$$

Because $2$ is invertible, (1.1) gives

$$
\dim_kH^0(K,\operatorname{ad}^0V)=h-1.
$$

The added dimension is therefore $3-(h-1)=4-h$. Adding it to (7.9) gives $f+3$. $\square$

Several cases deserve to be separated. If $V$ is absolutely irreducible or a nonsplit extension of two distinct characters, then $h=1$ and the unframed dimension is $f$. If $V$ is a split sum of distinct characters, then $h=2$ and the coarse tangent has dimension $f+1$, although an unframed universal ring need not exist because the local centralizer is larger than the scalars.

Equal-character semisimplification cannot occur with cyclotomic determinant
and Hodge rank one at every embedding. Indeed, schematic closure of a
stable line inside the unique finite-flat model, followed by the represented
quotient, gives an exact sequence of two rank-one finite-flat models. If
the two generic characters are equal, Raynaud uniqueness identifies their
marked models, so the two rank-one filtered objects have the same Hodge
rank, either zero or one, at each embedding. Exactness then makes the
rank-two Hodge rank there either zero or two. This contradicts the rank-one
condition forced by the cyclotomic determinant.

The framed dimension being independent of $h$ has a geometric explanation. At a split point the coarse filtered object gains one endomorphism and therefore one genuine coarse tangent direction. At the same time its change-of-frame orbit loses one dimension because the stabilizer is larger. These effects cancel. Consequently the framed ring stays smooth of dimension $f+3$ across ordinary split, ordinary nonsplit, and irreducible residual shapes. What changes is the quotient by automorphisms, not the framed local geometry.

### 7.4 The ordinary unit calculation

The ordinary case makes the adjective hardly ramified visible inside Kummer theory. Suppose

$$
0\longrightarrow k(1)\longrightarrow V_c
\longrightarrow k\longrightarrow0. \tag{7.11}
$$

Kummer theory identifies the ambient extension classes with

$$
H^1(K,k(1))
\simeq
\bigl(K^\times/(K^\times)^\ell\bigr)\otimes_{\mathbf F_\ell}k. \tag{7.12}
$$

Because $K/\mathbf Q_\ell$ is unramified,

$$
K^\times=\ell^{\mathbf Z}\times\mu_{\ell^f-1}\times U^1,
\qquad U^1=1+\ell R_K. \tag{7.13}
$$

The root-of-unity factor has order prime to $\ell$. The logarithm identifies $U^1$ with the additive group $\ell R_K$, and taking $\ell$th powers corresponds to multiplication by $\ell$. Hence

$$
\dim_k\bigl(R_K^\times/(R_K^\times)^\ell\bigr)\otimes k=f, \tag{7.14}
$$

while the valuation of $\ell$ supplies one additional ambient class.

The finite-flat extension classes are exactly the unit classes:

$$
H^1_{\mathrm{fl}}(K,k(1))
=\bigl(R_K^\times/(R_K^\times)^\ell\bigr)\otimes k. \tag{7.15}
$$

To prove this equality, finite flat Kummer theory constructs a finite-flat extension from every unit. Conversely, if (7.11) has a finite-flat model, schematic closure of the cyclotomic line and the represented quotient give the unique multiplicative and étale endpoint models. The exact classification of extensions between those endpoints identifies their Kummer classes with units. The valuation class would require the radical of a uniformizer and lies outside the finite-flat extension category.

The $f$-dimensional unit subspace is traditionally called *peu ramifiée*, or hardly ramified. Principal units can still give ramified field extensions. The phrase means that the valuation coordinate vanishes, not that inertia acts trivially.

## 8. Liftability at the coefficient prime

A correct tangent dimension does not remove higher equations. We therefore lift the classified data themselves: first the Hodge lines, then divided Frobenius, then determinant and frame. The construction proves formal smoothness of the restricted condition without making any claim that the ambient local obstruction group vanishes.

### 8.1 Lifting filtrations and divided Frobenius

Let $A'\twoheadrightarrow A$ be a small extension with kernel $J$, and let $(M,L,\Phi)$ represent a finite-flat deformation over $A$. We construct a lift of the filtered object.

After a finite étale coefficient extension splitting the embeddings, each $M_i$ is free of rank two. Lift a basis to obtain a free $A'$-module $M_i'$. A direct-summand line lifts across a nilpotent extension: if $L_i$ is spanned by $e_i$, choose a lift $e_i'$ that remains unimodular and put $L_i'=A'e_i'$. Equivalently, the relative Grassmannian of lines is smooth.

The module $D_{L_i'}(M_i')$ is free of rank two. Choose any matrix lift

$$
\widetilde\Phi_i:D_{L_i'}(M_i')\longrightarrow M_{i+1}'
$$

of $\Phi_i$. Its determinant reduces to a unit, so it is already an isomorphism. Thus lines and divided-Frobenius isomorphisms lift independently before determinant is imposed.

Descent causes no hidden obstruction. Without splitting the embeddings, direct-summand lines lift because the Grassmannian over the finite étale algebra $S_{A'}$ is smooth, and isomorphisms lift because the relevant general linear group is smooth. The construction is compatible with the descent datum, so it returns a triple over the original coefficient ring.

### 8.2 Fixing the cyclotomic determinant

The lifted rank-two object may have the wrong determinant Frobenius by a factor $1+j$ with $j\in J$. We correct one of the matrices. In split coordinates, multiply $\widetilde\Phi_0$ by

$$
\begin{pmatrix}1+j&0\\0&1\end{pmatrix}.
$$

This changes the cyclic determinant by $1+j$ and leaves all reductions unchanged. Choosing the inverse discrepancy produces exactly the prescribed cyclotomic determinant.

There is an intrinsic version. The determinant correction is measured by the norm from the finite étale algebra $S_{A'}$ to $A'$. On $1+J S_{A'}$ its derivative is the trace

$$
\operatorname{Tr}_{S_k/k}:J\otimes_kS_k\longrightarrow J.
$$

The trace is surjective for a finite étale algebra, so the correction descends. This is the same mechanism that corrected Frobenius at $2$, but now the finite étale algebra has degree $f$ and comes from residue embeddings rather than an inertial centralizer.

Finally, a generic frame lifts because

$$
\operatorname{GL}_2(A')\longrightarrow\operatorname{GL}_2(A)
$$

is surjective. We have therefore lifted the filtration, divided Frobenius, determinant, and frame.

### 8.3 Why the restricted obstruction map is zero

**Theorem 8.1 (finite-flat liftability).** Under (6.1), every rank-two finite-flat deformation with determinant $\chi_\ell$ lifts through every small extension. The same holds with a frame. Hence the finite-flat fixed-determinant obstruction map is identically zero.

**Proof.** Sections 8.1 and 8.2 construct a lifted coefficient-flat divided filtered object with the prescribed determinant and frame. The low-weight classification realizes it as a unique marked finite-flat group and identifies its generic representation with a lift of the original one. Every Artinian surjection factors into small extensions, so iteration proves the assertion for all surjections. $\square$

The conclusion must not be restated as

$$
H^2(K,\operatorname{ad}^0V)=0.
$$

That ambient group can be nonzero. A constrained deformation problem has an obstruction map from its lifting problems into the ambient group; the theorem proves that this map is zero by solving every problem explicitly. This distinction is especially visible in small coefficient characteristics, but it remains logically necessary for $\ell\ge7$.

For example, take the split ordinary representation

$$
V=k(1)\oplus k.
$$

Then $V(1)=k(2)\oplus k(1)$, and projection onto the $k(1)$ summand followed by inclusion into the $k(1)$ summand of $V(1)$ gives a nonzero equivariant map

$$
V\longrightarrow V(1).
$$

It is off diagonal relative to the original two summands and has trace zero. Local duality therefore permits a nonzero class in

$$
H^2(K,\operatorname{ad}^0V).
$$

Nevertheless every finite-flat lifting problem is solved by Sections 8.1--8.2. The example proves concretely that ambient obstruction vanishing would be the wrong theorem at the coefficient prime.

### 8.4 The finite-flat local rings

**Theorem 8.2 (finite-flat local rings).** Under (6.1), let $h$ be as in (7.5). Then the framed fixed-determinant finite-flat functor is represented and formally smooth, with

$$
R_\ell^{\square,\mathrm{fl},\chi}
\simeq
\mathcal O[[Z_1,\ldots,Z_{f+3}]]. \tag{8.1}
$$

If $h=1$, the unframed functor is represented and

$$
R_\ell^{\mathrm{fl},\chi}
\simeq
\mathcal O[[X_1,\ldots,X_f]], \tag{8.2}
$$

with a noncanonical isomorphism

$$
R_\ell^{\square,\mathrm{fl},\chi}
\simeq R_\ell^{\mathrm{fl},\chi}[[Y_1,Y_2,Y_3]]. \tag{8.3}
$$

If $h=2$, the framed ring is still (8.1), and the coarse tangent has dimension $f+1$, but no coarse unframed universal ring is asserted without additional rigidifying data.

**Proof.** Closed relative representability of the finite-flat condition follows from uniqueness of integral models in the low-ramification range and from the classified filtered equations. Theorem 8.1 gives formal smoothness. Theorem 7.1 gives the tangent dimensions, so the representing framed ring is a power-series ring in $f+3$ variables. If $h=1$, the scalar-centralizer criterion gives unframed representability, and the unframed tangent dimension $f$ yields (8.2). The framing map adds the three trace-zero change-of-frame directions, giving (8.3). The final assertion records the failure of the scalar-centralizer hypothesis when $h=2$. $\square$

For the global problem over $\mathbf Q$, $K=\mathbf Q_\ell$ and $f=1$. Thus every local residual shape has a smooth framed ring in four variables. In a Schur local case the unframed finite-flat tangent is one-dimensional.

## 9. The local package

The preceding chapters treated two local fields by unrelated methods. This chapter puts their outputs into a common ledger: intrinsic definition, tangent subspace, representing ring, liftability, and conductor. It also specifies the minimal conditions at all remaining places so that the later global functor has no unstated local clause.

### 9.1 What a usable local condition must prove

We now assemble the two calculations. A local predicate is suitable for a universal global problem only after the following statements have been established.

First, it must be invariant under strict equivalence, because global deformations are isomorphism classes. Second, it must be stable under arbitrary Artinian coefficient maps, including nonflat quotients. Third, its framed form must be cut out by a closed quotient of the ambient framed deformation ring. Fourth, its tangent must be an explicitly identified subspace of local $H^1$. Fifth, lifting through small extensions must be proved, either through a complete vanishing theorem or through direct constrained coordinates. Finally, any conductor or type assertion must be constant for a structural reason.

The prime $2$ condition meets these requirements through the quadratic étale algebra $B_A$, the norm equation, and strict Hilbert 90. The coefficient-prime condition meets them through exact finite-flat models and the low-weight filtered classification. The mechanisms are different, but their outputs have the same formal shape.

### 9.2 The two distinguished places

For the global problem over $\mathbf Q$, define

$$
\mathcal L_2
=\mathcal D_2^{\mathrm{tq},\chi},
\qquad
\mathcal L_\ell
=\mathcal D_\ell^{\mathrm{fl},\chi}. \tag{9.1}
$$

At $2$, membership means

$$
\rho(P_2)=1,
\qquad
\rho(\tau)^2+\rho(\tau)+I=0,
\qquad
\det\rho=\chi_\ell. \tag{9.2}
$$

The condition is tame, has conductor two, and is the unramified-quadratic dihedral type. Its unframed tangent is

$$
L_2=0. \tag{9.3}
$$

At $\ell$, membership means that every Artinian representation has an actual coefficient-linear finite-flat model over $\mathbf Z_\ell$, with determinant $\chi_\ell$. Its tangent is

$$
L_\ell
=H^1_{\mathrm{fl}}(\mathbf Q_\ell,
\operatorname{ad}^0\bar\rho). \tag{9.4}
$$

If

$$
h_\ell=\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(\bar V),
$$

then

$$
\dim_kL_\ell=h_\ell. \tag{9.5}
$$

Here (9.5) is (7.9) with $f=1$. The value is $1$ in the local Schur cases and $2$ for a split sum of distinct characters.

### 9.3 Minimal conditions elsewhere

At a finite prime $p\notin\{2,\ell\}$, the hardly-ramified global representation is unramified. If the global Galois group is already taken to be unramified outside $\{2,\ell\}$, no separate local equation is needed. If one begins with a larger ramification set, impose the unramified condition

$$
\rho(I_p)=1.
$$

Its tangent is

$$
H^1_{\mathrm{ur}}(\mathbf Q_p,\operatorname{ad}^0\bar\rho)
\simeq
(\operatorname{ad}^0\bar\rho)^{I_p}/(\phi_p-1)
(\operatorname{ad}^0\bar\rho)^{I_p}. \tag{9.6}
$$

If a residual representation is already ramified at an auxiliary prime, “minimal” cannot be replaced blindly by “unramified.” The correct condition fixes its prime-to-$\ell$ inertial type, or retains existing nonzero tame monodromy. In the present hardly-ramified problem there are no such auxiliary ramified primes, so the only nontrivial away-from-$\ell$ datum is (9.2).

At the real place, oddness is rigid because $2$ is invertible. If $c$ is complex conjugation and $\det\rho(c)=-1$, then $c^2=1$ and the idempotents

$$
\frac{1\pm\rho(c)}2
$$

split the representation into rank-one $+1$ and $-1$ eigenspaces. Their ranks are fixed by reduction. Hence oddness contributes no infinitesimal local direction.

These minimal conditions are compatible with conductors. An unramified lift has conductor zero. A fixed prime-to-$\ell$ finite type preserves every ramification-group invariant rank because the averaging idempotents lift integrally. At $2$, the chosen finite type has no inertia invariants and hence conductor two. None of these conclusions follows from upper semicontinuity alone; each follows from a fixed integral action.

### 9.4 A dimension and obstruction ledger

The two main local conditions can be summarized as follows.

| Place | Intrinsic condition | Unframed fixed-determinant tangent | Framed ring | Lifting mechanism |
|---|---|---:|---|---|
| $2$ | tame order-three quadratic type, conductor $2$ | $0$ | $\mathcal O[[Y_1,Y_2,Y_3]]$ | norm correction and strict quadratic Hilbert $90$ |
| $\ell$ | coefficient-linear finite flat, Hodge type $(0,1)$ | dimension $h_\ell$ over $\mathbf Q_\ell$ | $\mathcal O[[Z_1,Z_2,Z_3,Z_4]]$ | lifting Hodge lines and divided Frobenius |

At $2$, the ambient fixed-determinant $H^2$ vanishes for $\ell\ge7$. At $\ell$, the constrained obstruction map vanishes even if ambient $H^2$ does not. This is precisely the information a global obstruction argument may use. It may not replace the second statement by an unproved ambient vanishing.

## 10. The universal global problem

Local conditions matter only after they can be imposed simultaneously on a global universal family. We now state the residual hypotheses, define the hardly-ramified minimal functor, prove that its local membership conditions cut out a closed universal quotient, and identify its tangent as a localization kernel.

### 10.1 Global hypotheses

Let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k) \tag{10.1}
$$

be continuous and satisfy:

1. $\ell\ge7$ and $\det\bar\rho=\bar\chi_\ell$;
2. $\bar\rho$ is absolutely irreducible;
3. $\bar\rho$ is odd;
4. $\bar\rho$ is unramified outside $\{2,\ell\}$;
5. $\bar\rho|_{G_2}$ has tame-quadratic type;
6. $\bar\rho|_{G_{\mathbf Q_\ell}}$ is finite flat.

The absolute irreducibility hypothesis gives

$$
\operatorname{End}_{k[G_{\mathbf Q}]}(k^2)=k. \tag{10.2}
$$

It is used for a universal unframed global ring. It does not force the local restriction at $\ell$ to have scalar centralizer; a globally irreducible representation may split locally. This is why the framed local theorem in Chapter 8 is the uniform input.

Let $S=\{2,\ell,\infty\}$ and let $G_{\mathbf Q,S}$ be the Galois group of the maximal extension of $\mathbf Q$ unramified outside $S$. All global lifts below factor through this group.

### 10.2 The hardly-ramified minimal functor

For $A\in\operatorname{Art}_{\mathcal O}$, define $D^{\mathrm{hr,min}}(A)$ to be the set of strict-equivalence classes of continuous lifts

$$
\rho_A:G_{\mathbf Q,S}\longrightarrow\operatorname{GL}_2(A) \tag{10.3}
$$

such that

$$
\det\rho_A=\chi_\ell, \tag{10.4}
$$

and

$$
\rho_A|_{G_2}\in\mathcal L_2(A),
\qquad
\rho_A|_{G_{\mathbf Q_\ell}}\in\mathcal L_\ell(A). \tag{10.5}
$$

Oddness is automatic from (10.4) and the residual ranks at complex conjugation. Unramifiedness away from $S$ is built into the source group. Thus (10.3)--(10.5) contain every local requirement and no hidden auxiliary ramification.

The word **minimal** means that the residual ramification is retained without enlargement. At $2$, the exact order-three inertia action is retained, so the conductor remains two. At $\ell$, finite flatness retains the smallest integral Hodge range compatible with cyclotomic determinant. Away from these primes, inertia remains trivial.

### 10.3 Closedness and the universal ring

**Theorem 10.1 (universal hardly-ramified ring).** Under the hypotheses of Section 10.1, the functor $D^{\mathrm{hr,min}}$ is represented by a complete Noetherian local $\mathcal O$-algebra

$$
R^{\mathrm{hr,min}}.
$$

It is a quotient of the universal fixed-determinant deformation ring of $\bar\rho$ unramified outside $S$.

**Proof strategy.** Start with the universal global representation, restrict it to the two decomposition groups, and pull back the closed ideals defining the framed local conditions. Local frames are only a device for expressing the equations; membership itself is conjugacy invariant.

**Proof.** Continuous global cohomology with finite coefficients is finite-dimensional for $G_{\mathbf Q,S}$. Together with (10.2), the standard representability criterion gives an unframed universal deformation ring for $\bar\rho$. Imposing (10.4) is a closed determinant equation and produces the universal fixed-determinant quotient $R^{\delta}$.

Choose a representative of the universal global deformation over $R^{\delta}$. Restriction to $G_2$ gives a framed local deformation after choosing the inherited global basis. The framed tame-quadratic condition is represented by a closed quotient, so its defining ideal pulls back to an ideal $J_2\subset R^{\delta}$. The same construction with the framed finite-flat quotient at $\ell$ gives $J_\ell$. Put

$$
R^{\mathrm{hr,min}}
=R^{\delta}/\overline{J_2+J_\ell}. \tag{10.6}
$$

For an Artinian target $A$, a map from (10.6) to $A$ is exactly a fixed-determinant global deformation whose restrictions factor through both local quotient conditions. Changing the representative of the universal deformation conjugates the local restrictions strictly. Both local predicates are invariant under strict conjugacy, so the resulting quotient functor is independent of that choice. The universal property follows. $\square$

The finite-dimensionality invoked in the first sentence can be seen directly at the level needed here. The group $G_{\mathbf Q,S}$ has finite-dimensional cohomology in degrees zero and one for every finite $k$-module; equivalently, only finitely many first-order extensions with prescribed ramification can occur. The scalar-centralizer condition (10.2) then removes the ambiguity in gluing strict-equivalence classes over coefficient fiber products. No vanishing of global $H^2$ is part of representability. Global $H^2$ controls relations in the ring after the ring has been constructed.

Equivalently, (10.6) is the completed fiber product of the ambient global ring with the two local quotient rings over the product of the ambient local framed rings. The quotient description is convenient because it also covers a split local restriction at $\ell$, where a coarse unframed local universal ring may not exist.

### 10.4 The global tangent space

Put

$$
M=\operatorname{ad}^0\bar\rho.
$$

The tangent of the ambient fixed-determinant global functor is $H^1(G_{\mathbf Q,S},M)$. Evaluating the local fiber-product condition on $k[\epsilon]$ gives

$$
t^{\mathrm{hr,min}}
=\left\{c\in H^1(G_{\mathbf Q,S},M):
\operatorname{res}_2(c)\in L_2,
\ \operatorname{res}_\ell(c)\in L_\ell
\right\}. \tag{10.7}
$$

Since $L_2=0$, this becomes

$$
t^{\mathrm{hr,min}}
=\ker\left(
H^1(G_{\mathbf Q,S},M)
\longrightarrow
H^1(\mathbf Q_2,M)\oplus
\frac{H^1(\mathbf Q_\ell,M)}{H^1_{\mathrm{fl}}(\mathbf Q_\ell,M)}
\right). \tag{10.8}
$$

In fact $H^1(\mathbf Q_2,M)=0$ by (5.9), so the first displayed target is zero. We retain it in (10.8) because it records the local condition and remains meaningful in variants where the coefficient characteristic is exceptional.

**Proposition 10.2 (tangent compatibility).** The tangent space of $R^{\mathrm{hr,min}}$ is canonically (10.8).

**Proof.** A tangent vector is a map from the universal ring to $k[\epsilon]$. For the ambient global ring it is a cohomology class in $H^1(G_{\mathbf Q,S},M)$. Factoring through the ideal $J_v$ is equivalent to the restricted first-order representation belonging to the local tangent subspace $L_v$. Intersecting the two inverse images gives (10.7), and substituting (9.3)--(9.4) gives (10.8). $\square$

This proposition is the precise interface with supported Selmer calculations. It identifies the global variables allowed by the local geometry, but it makes no unsupported claim about the number of global relations. Those require a global obstruction and duality analysis.

There is an equally important small-extension interpretation. Suppose an ambient global lift over $A'$ exists above a locally admissible lift over $A$. Its restrictions at $2$ and $\ell$ need not initially be the chosen admissible local lifts. At $2$ there is only one unframed local lift, so strict conjugacy removes the discrepancy. At $\ell$, the admissible lifts form a torsor under the finite-flat tangent subspace. Correcting a global lift to land in that local torsor is a global localization problem, not a consequence of local formal smoothness. This explains exactly where the present book stops and why the tangent kernel (10.8) is the correct input for the subsequent supported-cohomology calculation.

## 11. Compatibility and stability

Arithmetic applications change coefficient fields, use dual pairings, compare with local types, and restrict to field extensions. Each operation can alter integral data. This chapter records exactly which compatibilities have been proved and gives countervailing warnings where a local-field base change changes the type or its deformation geometry.

### 11.1 Change of coefficients

Let $\mathcal O\to\mathcal O'$ be a finite extension of coefficient DVRs, with residue extension $k\to k'$. Both local conditions have canonical scalar extensions.

At $2$, the matrices $T_0$ and $W$, the quadratic algebra

$$
B_A=A[u]/(u^2+u+1),
$$

and the norm equation all commute with scalar extension. If the quadratic algebra changes from connected to split, the normal form remains the same; only the description by eigenlines changes. The intrinsic condition therefore base-changes without choosing an ordering of those lines.

At $\ell$, finite-flat coefficient extension and quotient are exact by Proposition 6.1, and the low-weight classification commutes with finite coefficient extension. The filtration ranks and cyclotomic determinant remain unchanged. Hence a global deformation satisfying the two local conditions remains admissible after coefficient extension.

Conversely, scalar extension can detect membership. At $2$, the polynomial and wild-triviality equations descend entrywise. At $\ell$, if a scalar extension of the generic module has a finite-flat model, schematic closure of the original module inside the coefficient-restricted model produces a finite-flat model before extension. Descent of a particular chosen model requires descent data, but descent of the existential predicate follows.

Thus the construction of $R^{\mathrm{hr,min}}$ is compatible with finite flat extension of the coefficient base. For a fixed residue field this is expressed by completed tensor product; if the residue field is enlarged, one first scalar-extends the residual representation and then applies the same universal property.

### 11.2 Duality and fixed determinant

For a rank-two representation with determinant $\chi_\ell$, the alternating pairing

$$
V\times V\longrightarrow\det V=\mathcal O(1) \tag{11.1}
$$

identifies

$$
V\simeq V^*(1). \tag{11.2}
$$

At the coefficient prime, the low-weight classification preserves this pairing: Cartier duality exchanges weights zero and one, while the determinant object has weight one. The finite-flat local condition is therefore stable under the adjoint duality forced by (11.2).

At $2$, duality inverts the two inertia characters. Frobenius already interchanges them, so the unordered tame-quadratic type is self-dual. In matrices,

$$
T_0^{-1}=T_0^2
$$

is conjugate to $T_0$ by $W$. The determinant twist restores the prescribed Frobenius determinant. Thus duality preserves $\mathcal L_2$ as well.

On tangent coefficients, the trace pairing is perfect on $M=\operatorname{ad}^0\bar\rho$ because $\ell$ is odd. It identifies the Tate dual with $M(1)$. This is exactly the identification used in the obstruction computation (5.6). Fixed determinant and duality are therefore consistent at the representation, model, and cohomological levels.

### 11.3 The integral type lattice at 2

The tame-quadratic Galois condition has an integral local-type companion. Let $L/\mathbf Q_2$ be unramified quadratic. The nonsplit residue torus is

$$
\mathbf F_4^\times\hookrightarrow\operatorname{GL}_2(\mathbf F_2),
$$

and its two nontrivial characters are regular and Galois-conjugate. The depth-zero cuspidal construction produces a finite free $\mathcal O$-lattice

$$
\sigma_{\mathcal O}(L,\theta) \tag{11.3}
$$

whose characteristic-zero occurrence detects exactly the dihedral inertial class (2.7).

There are no modular denominator difficulties in our range. The finite group $\operatorname{GL}_2(\mathbf F_2)$ has order $6$, and $\ell\ge7$, so averaging idempotents are integral and reduction is semisimple. The companion lattice corresponds to $\theta^{-1}$, which is the Galois conjugate of $\theta$ and hence detects the same unordered quadratic type.

**Proposition 11.1 (type compatibility).** A characteristic-zero point of $R_2^{\square,\mathrm{tq},\chi}$ has Weil representation of the unramified-quadratic induced form (2.7), and the associated smooth representation contains the type lattice (11.3) after extending scalars. Conversely, within the depth-zero dihedral range, occurrence of (11.3) forces the tame-quadratic inertia condition and conductor two.

**Proof.** The forward implication follows from Section 2.3: the matrix relation gives inertia characters $\theta,\theta^{-1}$ and Frobenius interchanges them, hence the Weil representation is the quadratic induction. The depth-zero type-detection theorem then gives occurrence of (11.3). Conversely, that detection theorem recovers the regular character of the nonsplit residue torus up to Galois conjugacy. Its restriction to inertia has the two nontrivial order-three characters, so its matrix satisfies $T^2+T+I=0$. Proposition 2.1 gives conductor two. $\square$

The type lattice is compatible with the deformation condition; it does not define finite flatness at $\ell$. These are separate local entries with separate integral theories.

### 11.4 Base change of local fields

The permitted base changes must be stated with care.

At the coefficient prime, the finite-flat condition and its filtered classification commute with unramified extension $K'/K$. The number of residue embeddings changes, and the tangent dimension becomes

$$
[K':\mathbf Q_\ell]+h'-1.
$$

Ramified base change preserves finite flatness by extending a chosen group scheme, but the converse and the explicit power-series theorem need not hold. Potential finite flatness is weaker than finite flatness over the original base.

At $2$, restrict the tame pair to an unramified extension of residue degree $r$. Its Frobenius becomes $\phi^r$ and acts on the order-three characters by $x\mapsto x^{2^r}$. If $r$ is odd, it still interchanges them and the quadratic type remains irreducible. If $r$ is even, it fixes both characters and the restriction splits into two tame lines. The conductor remains two because inertia still has no fixed vector, but the local centralizer and deformation chart change. Thus the original rigid theorem cannot be transferred blindly to an even-degree unramified extension.

A ramified extension at $2$ can change the tame generator by an index and can kill the order-three inertia if its ramification index is divisible by $3$. The restricted representation must be reclassified from its actual inertia action. The phrase “same local condition after arbitrary base change” would therefore be false.

## 12. The hardly-ramified local-condition theorem

The final chapter collects the local and global conclusions in one theorem with a visible hypothesis ledger. Its purpose is not merely summary: it makes clear which obstruction groups actually vanish, which obstruction maps vanish by construction, and which global questions remain outside the local package.

### 12.1 Main theorem

We can now state the complete package.

**Theorem 12.1 (local conditions for hardly-ramified minimal deformations).** Let $\ell\ge7$, let $\mathcal O$ and $k$ be as in Section 1.2, and let

$$
\bar\rho:G_{\mathbf Q}\to\operatorname{GL}_2(k)
$$

satisfy the six hypotheses of Section 10.1. Fix determinant $\chi_\ell$. Then:

1. At $2$, the equations
   $$
   \rho(P_2)=1,
   \qquad \rho(\tau)^2+\rho(\tau)+I=0
   $$
   define an intrinsic tame unramified-quadratic dihedral condition. Every characteristic-zero member has Artin conductor exponent two.

2. The unframed fixed-determinant condition at $2$ is rigid and formally smooth, represented by $\mathcal O$. Its tangent is zero. Its framed ring is
   $$
   \mathcal O[[Y_1,Y_2,Y_3]].
   $$
   Moreover
   $$
   H^1(\mathbf Q_2,\operatorname{ad}^0\bar\rho)=
   H^2(\mathbf Q_2,\operatorname{ad}^0\bar\rho)=0.
   $$

3. At $\ell$, coefficient-linear finite flatness over $\mathbf Z_\ell$ with determinant $\chi_\ell$ is an intrinsic closed local condition, stable under every Artinian coefficient map. Its framed ring is formally smooth:
   $$
   R_\ell^{\square,\mathrm{fl},\chi}
   \simeq\mathcal O[[Z_1,Z_2,Z_3,Z_4]].
   $$

4. If
   $$
   h_\ell=\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(\bar V),
   $$
   then the finite-flat fixed-determinant tangent has dimension $h_\ell$. If $h_\ell=1$, the unframed local ring is $\mathcal O[[X]]$. If $h_\ell=2$, the framed statement remains valid but no unrigidified local universal ring is inferred.

5. The finite-flat condition lifts through every small extension. This is proved by lifting Hodge lines and divided Frobenius and correcting their determinant. Its restricted obstruction map is zero; no ambient $H^2$-vanishing is required.

6. The global hardly-ramified minimal functor of Section 10.2 is represented by a complete Noetherian local ring $R^{\mathrm{hr,min}}$. Its tangent space is
   $$
   \ker\left(
   H^1(G_{\mathbf Q,S},\operatorname{ad}^0\bar\rho)
   \longrightarrow
   H^1(\mathbf Q_2,\operatorname{ad}^0\bar\rho)
   \oplus
   \frac{H^1(\mathbf Q_\ell,\operatorname{ad}^0\bar\rho)}
   {H^1_{\mathrm{fl}}(\mathbf Q_\ell,\operatorname{ad}^0\bar\rho)}
   \right).
   $$

7. Both local conditions commute with finite extension of coefficient rings, preserve the cyclotomic self-duality, and are compatible with the integral depth-zero type lattice at $2$. Their asserted ground-field base changes are exactly those in Sections 11.4; no arbitrary base-change invariance is claimed.

**Proof.** Proposition 2.1 proves the conductor statement. Theorems 4.2 and 5.1 prove rigidity, liftability, tangents, obstructions, and rings at $2$. Propositions 6.1 and Theorem 6.2 establish the finite-flat predicate and its coefficient behavior. Theorems 7.1, 8.1, and 8.2 give the tangent dimensions, small-extension lifting, and local rings at $\ell$. Theorem 10.1 and Proposition 10.2 give the global ring and its tangent. Chapter 11 proves coefficient, duality, type-lattice, and ground-field compatibility. $\square$

### 12.2 Hypothesis ledger and boundary cases

Every hypothesis has a specific role.

| Hypothesis | What it supplies | What cannot be concluded without it |
|---|---|---|
| $\ell\ge7$ | $2$ and $3$ are units; no adjoint cyclotomic invariant at $2$ | inertia may cease to be étale or the local $H^2$ calculation may acquire an exceptional invariant |
| order-three polynomial at $2$ | the quadratic étale centralizer and no inertia invariants | conductor two and rigid Frobenius normal form are not forced |
| unramified determinant at $2$ | compatibility with determinant-one inertia | the local condition may be empty |
| $K/\mathbf Q_\ell$ unramified | integral low-weight classification and explicit embedding cycle | the power-series and tangent formulas of Chapters 7--8 are not established |
| cyclotomic determinant | one Hodge line at every embedding and a fixed weight-one determinant | the rank pattern and determinant equation change |
| global absolute irreducibility | scalar global centralizer and an unframed universal ring | only a framed universal ring or an unframed hull may exist |
| actual finite-flat models | exact integral extension condition | rational Hodge labels do not control integral coefficient quotients |
| chosen arithmetic Frobenius | eigenvalues $2$ at the prime $2$ and $q$ generally | all displayed twist and obstruction eigenvalues invert under a convention change |

The lower bound $\ell\ge7$ is a unified global range. Several individual local statements hold more widely. The tame quadratic algebra only needs $\ell\ne3$, strict Hilbert 90 only needs $\ell\ne2$, and the coefficient-prime finite-flat smoothness theorem holds for every odd $\ell$ under its unramified low-weight hypotheses. We do not splice these wider ranges into the main theorem because the ambient obstruction at $2$ is exceptional in characteristic $3$, and the catalogued global problem is explicitly in odd characteristic at least $7$.

The exceptional calculations are concrete. In characteristic $3$,

$$
X^2+X+1=(X-1)^2,
$$

so the order-three algebra is no longer étale, its two inertial characters coalesce, and averaging by $C_3$ is impossible. At the same time the Frobenius eigenvalue $-2$ in (5.7) becomes $1$, producing the possible adjoint cyclotomic invariant. In characteristic $2$, trace zero no longer splits from scalars and the division by $2$ in strict Hilbert $90$ is invalid. These are structural failures, not gaps removable by a change of notation.

The phrase tame-quadratic must not be replaced by “quadratic character at $2$.” The latter would be wild. Nor may conductor two replace the full type: unrelated representations can have the same conductor. The order-three inertia polynomial, Frobenius interchange, determinant, and wild-triviality together define the component.

At $\ell$, finite flatness must not be replaced by unramifiedness, by semisimplified endpoint conditions, or by one finite-flat torsion level. The full coefficient-linear integral model and its compatible quotients are essential. At a split local residual point, a chosen stable line gives an enhanced chart but not a decomposition of the smooth framed finite-flat ring into components.

Finally, local smoothness does not imply global smoothness. The local obstruction maps vanish, but a global factor-set obstruction can remain, and moving an ambient global lift into prescribed local torsors is a separate localization problem. The present theorem constructs the exact local inputs and the universal global quotient. It does not anticipate the supported cohomology and global relation analysis that follow.

The dependency boundary is also exact. Ramification theory supplies the tame conductor formula. Local Galois cohomology supplies the Frobenius description of unramified classes and the local Euler characteristic; Tate local duality supplies the top-degree twisted-invariant calculation. Finite-flat geometry supplies marked models, schematic closure, represented quotients, coefficient actions, and Cartier duality. Small-height Oort--Tate rigidity supplies the rank-one endpoint checks. Raynaud full faithfulness and the integral Fontaine--Laffaille equivalence supply uniqueness of marked models, exact low-weight classification, compatible quotients, and unramified base change. The established local-deformation theory supplies the fixed finite-type and finite-flat representability criteria, while integral local-type theory supplies the depth-zero quadratic lattice and its detection theorem. Every use in this book retains the hypotheses stated in those results; no later global duality or relation theorem is used here.

### 12.3 Conclusion

The hardly-ramified deformation problem is governed by two complementary kinds of rigidity.

At $2$, tame inertia of order three generates a quadratic étale algebra. Frobenius acts through its nontrivial involution, determinant becomes a norm equation, and strict conjugacy becomes an integral quadratic Hilbert $90$ calculation. The trace-zero inertia centralizer is the sign line for Frobenius. Because $-2$ is not $1$ in characteristic at least $7$, both the tangent and the obstruction group vanish. The local representation is uniquely determined, has no inertia-fixed vector, and therefore has conductor exactly two.

At the coefficient prime, rigidity does not mean absence of parameters. Finite flatness converts the representation into a Hodge line and an invertible divided-Frobenius cycle. These data have exactly the freedom measured by $f+h-1$ unframed parameters, or $f+3$ framed parameters after determinant is fixed. Every line, Frobenius map, determinant, and frame lifts across a small extension. This direct construction proves that the finite-flat obstruction map vanishes without confusing it with ambient cohomology. In the ordinary case its tangent is visibly the unit part of Kummer theory: hardly ramified means zero valuation coordinate.

The global condition now has no ambiguity. It fixes cyclotomic determinant, imposes the tame-quadratic conductor-two type at $2$, imposes genuine finite flatness at $\ell$, and permits no other finite ramification. Closed local equations cut out a universal global quotient, and its tangent is the exact kernel of localization modulo the two proved local subspaces. Coefficient change, duality, conductor, and the depth-zero type lattice all agree with this construction under their stated hypotheses.

This is the complete local package needed for hardly-ramified minimal deformation theory: intrinsic conditions, represented rings, exact tangent spaces, vanishing local obstruction maps, conductor control, and a defensible passage to the universal global problem.
