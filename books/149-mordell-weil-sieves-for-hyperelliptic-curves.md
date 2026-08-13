# Mordell--Weil Sieves for Hyperelliptic Curves

## Contents

1. [From a known Jacobian to all curve points](#1-from-a-known-jacobian-to-all-curve-points)
   - [The remaining finiteness problem](#11-the-remaining-finiteness-problem)
   - [Standing conventions](#12-standing-conventions)
   - [The three layers of a complete sieve](#13-the-three-layers-of-a-complete-sieve)
2. [Abel--Jacobi embeddings and specialization](#2-abel--jacobi-embeddings-and-specialization)
   - [The pointed embedding](#21-the-pointed-embedding)
   - [Why the Abel map is injective](#22-why-the-abel-map-is-injective)
   - [Reduction at a good prime](#23-reduction-at-a-good-prime)
   - [Changing the base point](#24-changing-the-base-point)
3. [Finite quotients of Mordell--Weil groups](#3-finite-quotients-of-mordell--weil-groups)
   - [Reduction constraints](#31-reduction-constraints)
   - [The basic Mordell--Weil sieve theorem](#32-the-basic-mordell--weil-sieve-theorem)
   - [Several primes and one intersection](#33-several-primes-and-one-intersection)
   - [What a surviving class means](#34-what-a-surviving-class-means)
4. [Coset sieving and refinement](#4-coset-sieving-and-refinement)
   - [Cosets rather than points](#41-cosets-rather-than-points)
   - [Lifting a modulus](#42-lifting-a-modulus)
   - [A proof of exhaustive refinement](#43-a-proof-of-exhaustive-refinement)
   - [Separating known points](#44-separating-known-points)
5. [Local images and reduction sets](#5-local-images-and-reduction-sets)
   - [Good primes away from the modulus](#51-good-primes-away-from-the-modulus)
   - [Primes dividing the modulus](#52-primes-dividing-the-modulus)
   - [Bad reduction and component data](#53-bad-reduction-and-component-data)
   - [Exact finite image certificates](#54-exact-finite-image-certificates)
6. [Saturation and finite-index subgroups](#6-saturation-and-finite-index-subgroups)
   - [Why finite index is not equality](#61-why-finite-index-is-not-equality)
   - [Prime-by-prime saturation](#62-prime-by-prime-saturation)
   - [Reduction kernels as saturation certificates](#63-reduction-kernels-as-saturation-certificates)
   - [Closing the finite list of primes](#64-closing-the-finite-list-of-primes)
7. [Completeness certificates](#7-completeness-certificates)
   - [The global ledger](#71-the-global-ledger)
   - [The finite-prime ledger](#72-the-finite-prime-ledger)
   - [The coset ledger](#73-the-coset-ledger)
   - [A reusable completeness theorem](#74-a-reusable-completeness-theorem)
8. [Prime selection and efficient intersections](#8-prime-selection-and-efficient-intersections)
   - [What makes a prime useful](#81-what-makes-a-prime-useful)
   - [Chinese remaindering finite information](#82-chinese-remaindering-finite-information)
   - [Symmetry and involution](#83-symmetry-and-involution)
   - [Failure modes](#84-failure-modes)
9. [The Chabauty boundary](#9-the-chabauty-boundary)
   - [The rank inequality](#91-the-rank-inequality)
   - [How Chabauty and the sieve cooperate](#92-how-chabauty-and-the-sieve-cooperate)
   - [What happens at and above the boundary](#93-what-happens-at-and-above-the-boundary)
10. [The genus-two curve $X_1(13)$](#10-the-genus-two-curve-x_113)
    - [The curve and its Jacobian](#101-the-curve-and-its-jacobian)
    - [A good reduction at seventeen](#102-a-good-reduction-at-seventeen)
    - [The finite Abel-image calculation](#103-the-finite-abel-image-calculation)
11. [The exhaustive sieve for $X_1(13)$](#11-the-exhaustive-sieve-for-x_113)
    - [The six surviving classes](#111-the-six-surviving-classes)
    - [Completeness and uniqueness](#112-completeness-and-uniqueness)
    - [The exact rational-point set](#113-the-exact-rational-point-set)
12. [The mixed-seven curve](#12-the-mixed-seven-curve)
    - [The curve and the complete Mordell--Weil group](#121-the-curve-and-the-complete-mordell--weil-group)
    - [All twelve reduced classes](#122-all-twelve-reduced-classes)
    - [The terminal Abel-image sieve](#123-the-terminal-abel-image-sieve)
13. [The mixed-seven rational points](#13-the-mixed-seven-rational-points)
    - [Exact determination](#131-exact-determination)
    - [Cuspidal and degenerate meaning](#132-cuspidal-and-degenerate-meaning)
    - [A certificate with no hidden search](#133-a-certificate-with-no-hidden-search)
14. [The completed sieve package](#14-the-completed-sieve-package)
    - [Hypothesis ledger](#141-hypothesis-ledger)
    - [Main theorem](#142-main-theorem)
    - [Conclusion](#143-conclusion)

## 1. From a known Jacobian to all curve points

### 1.1 The remaining finiteness problem

Let $C/\mathbf Q$ be a smooth projective curve of genus at least two, let
$J=\operatorname{Jac}(C)$, and choose a rational point $P_0$. The map

$$
j=j_{P_0}:C\longrightarrow J,
\qquad P\longmapsto[P-P_0] \tag{1.1}
$$

places the rational-point problem inside a finitely generated abelian group.
The Mordell--Weil theorem gives finite generation, and descent may determine
$J(\mathbf Q)$ exactly. Neither statement alone identifies $C(\mathbf Q)$.
The image $j(C)$ is a thin geometric subset of the ambient group, and one
must decide which Mordell--Weil classes lie on it.

Reduction supplies a necessary condition. At a prime of good reduction, a
rational point reduces to a point of the special curve, and its Jacobian
class reduces to the Abel class of that special point. Thus

$$
j(C(\mathbf Q))\ \text{reduces into}\
j_p(C(\mathbf F_p))\subseteq J(\mathbf F_p). \tag{1.2}
$$

The right side is finite and can be enumerated exactly. Pulling it back to a
finite quotient of $J(\mathbf Q)$ gives a congruence condition. Different
primes impose different conditions, and their intersection can be much
smaller than any individual one. This is the Mordell--Weil sieve.

The word *exhaustive* carries real content. A short search for points, a list
of reductions, or an intersection which happens to contain only the known
residue classes is not automatically a proof. One must know the full
Mordell--Weil group or control its index, enumerate every relevant special
fiber, prove every reduction map, and explain why the final finite data rule
out every unlisted rational point. This book builds that chain and then
executes it for the two genus-two curves left open by the preceding descent.

### 1.2 Standing conventions

Unless stated otherwise, $C/\mathbf Q$ is smooth, projective, and
geometrically connected of genus $g\ge2$, and $J$ is its Jacobian. A chosen
$P_0\in C(\mathbf Q)$ defines (1.1). For a good prime $p$, write

$$
\rho_p:J(\mathbf Q)\longrightarrow J(\mathbf F_p),
\qquad
j_p:C(\mathbf F_p)\longrightarrow J(\mathbf F_p) \tag{1.3}
$$

for reduction and the special-fiber Abel map based at $\bar P_0$. Put

$$
X_p=j_p(C(\mathbf F_p)). \tag{1.4}
$$

All groups are written additively. If $G$ is an abelian group and $N\ge1$,
$G/NG$ means the cokernel of multiplication by $N$. A **coset** always means
a coset in a specified Mordell--Weil group or subgroup; it is never silently
identified with one rational point.

For a pointed odd-degree genus-two model

$$
C:y^2=f(x),\qquad f\in\mathbf Q[x]
\text{ monic, squarefree, }\deg f=5, \tag{1.5}
$$

the point at infinity is denoted $\infty$. Book 136 proves that every class
of $J(\mathbf Q)$ has a unique reduced Mumford pair $[u,v]$, with

$$
u\text{ monic},\qquad \deg v<\deg u\le2,
\qquad u\mid f-v^2. \tag{1.6}
$$

In this normalization the Abel image consists exactly of the identity and
the pairs with $\deg u=1$. This literal degree test will terminate the
mixed-seven calculation. The sextic model of $X_1(13)$ has no rational
Weierstrass point, so we use the intrinsic Abel map globally and change to a
pointed quintic only after reduction at a prime where a branch point becomes
rational.

### 1.3 The three layers of a complete sieve

A proof has three independent layers.

The **global layer** identifies a subgroup $\Gamma\subseteq J(\mathbf Q)$,
its generators and torsion, and the index $[J(\mathbf Q):\Gamma]$. If the
index is claimed to be one, descent and saturation must prove it.

The **finite layer** chooses good primes, enumerates $C(\mathbf F_p)$ and the
needed part of $J(\mathbf F_p)$, and determines $\rho_p$ on every global
generator. This produces exact finite sets $X_p$ and exact homomorphisms.

The **exhaustion layer** intersects all pullbacks, refines surviving cosets,
and supplies a terminal reason that no unknown rational point remains. A
terminal reason can be an a priori height region whose every lattice point
has been separated, a complete local residue-disk argument, or, as in both
applications here, a finite Mordell--Weil group in which every class can be
tested.

Keeping these layers separate prevents circularity. The desired point list
does not prove saturation; the desired rank does not prove a local image is
complete; and survival at every chosen prime does not create a rational
point.

## 2. Abel--Jacobi embeddings and specialization

### 2.1 The pointed embedding

The sieve compares a curve point with a group element, so the comparison map
must be fixed precisely. For $P_0\in C(\mathbf Q)$, equation (1.1) is a
morphism: it is the family of degree-zero line bundles
$\mathcal O_C(P-P_0)$ parametrized by $P$. It sends $P_0$ to $0$ and is
defined over $\mathbf Q$.

One may more generally use a rational divisor class $D_0$ of degree one and
send $P$ to $[P-D_0]$. For the present applications a rational point is
available, so no Picard obstruction occurs. This matters under reduction:
a named rational point extends uniquely over every proper smooth model,
whereas an unspecified geometric point does not define a rational base
section.

For the quintic (1.5), reduced uniqueness gives

$$
j_\infty(\infty)=[1,0],\qquad
j_\infty(a,b)=[x-a,b]. \tag{2.1}
$$

Thus $j_\infty(C(\mathbf Q))$ is exactly the set of rational reduced pairs
of degree at most one. The statement is bidirectional: a degree-one pair
$[x-a,b]$ satisfies $b^2=f(a)$ by divisibility, so it comes from the point
$(a,b)$.

### 2.2 Why the Abel map is injective

**Proposition 2.1.** If $C$ has positive genus, then $j_{P_0}$ is injective
on geometric points. If $g\ge1$, it is a closed immersion.

**Proof.** If $j(P)=j(Q)$, then $P-Q$ is principal. For $P\ne Q$, a function
with divisor $P-Q$ has a single simple pole and therefore defines a
degree-one morphism $C\to\mathbf P^1$. Such a morphism is an isomorphism,
contradicting positive genus. Hence $P=Q$.

For the tangent statement, the pullback of invariant differentials on $J$
is the full space $H^0(C,\Omega_C^1)$. At any point some regular
differential is nonzero: otherwise that point would be a base point of the
canonical system, while Riemann--Roch applied to $K_C-P$ gives
$h^0(K_C-P)=g-1<h^0(K_C)$. Thus the differential of $j$ is nonzero. A proper
geometrically injective unramified morphism is radicial and proper, hence a
closed immersion.
$\square$

The elementary first paragraph is the part used at the end of a sieve. Once
the exact class $j(P)$ agrees with the class of a known point, injectivity
proves equality of points; no coordinate recovery ambiguity remains.

### 2.3 Reduction at a good prime

Let $\mathcal C/\mathbf Z_p$ be a smooth proper model and let
$\mathcal J/\mathbf Z_p$ be its relative Jacobian. Properness extends every
$\mathbf Q_p$-point of $C$ and every $\mathbf Q_p$-point of $J$ uniquely to
an integral section. The base point $P_0$ extends as well. Formation of
$\mathcal O(P-P_0)$ commutes with restriction to the special fiber, giving
the commutative square

$$
\begin{array}{ccc}
C(\mathbf Q)&\xrightarrow{j}&J(\mathbf Q)\\
\downarrow&&\downarrow\rho_p\\
C(\mathbf F_p)&\xrightarrow{j_p}&J(\mathbf F_p).
\end{array} \tag{2.2}
$$

**Proposition 2.2 (specialization constraint).** For every good prime $p$,

$$
\rho_p(j(C(\mathbf Q)))\subseteq X_p. \tag{2.3}
$$

**Proof.** Given $P\in C(\mathbf Q)$, reduce the identity
$j(P)=[P-P_0]$ on the smooth proper model. The result is
$\rho_p(j(P))=[\bar P-\bar P_0]=j_p(\bar P)$, which belongs to $X_p$.
$\square$

The good-reduction hypothesis is doing two jobs. It identifies the special
fiber of the relative Picard scheme with the Jacobian of the smooth special
curve, and it makes reduction a homomorphism. At a bad prime a Néron-model
map still exists, but the curve may meet several components and the target is
not obtained by simply taking the Jacobian of a singular plane equation.

### 2.4 Changing the base point

If $P_1$ is another rational base point, then

$$
j_{P_1}(P)=j_{P_0}(P)-j_{P_0}(P_1). \tag{2.4}
$$

Thus changing base point translates every global and local image by one
fixed class. A sieve remains valid after the translation only if the same
translation is made in the global group, at every special fiber, and in
every coset table.

On an even-degree model $z^2=F(x)$ with two rational points
$\infty^+,\infty^-$ at infinity, hyperelliptic conjugation is not group
negation for the embedding based at $\infty^+$. Since

$$
\operatorname{div}(x-a)=P+\iota(P)-\infty^+-\infty^-,
$$

putting $T=[\infty^--\infty^+]$ gives

$$
j_{\infty^+}(P)+j_{\infty^+}(\iota P)=T. \tag{2.5}
$$

This translation is indispensable for $X_1(13)$. Treating conjugation as
negation would replace the correct affine pairs of residues by their wrong
translates.

## 3. Finite quotients of Mordell--Weil groups

### 3.1 Reduction constraints

Let $G=J(\mathbf Q)$, let $N\ge1$, and let
$\pi_N:G\to G/NG$. A good prime $p$ gives a useful constraint on $G/NG$
only when reduction of $NG$ is understood. Define

$$
S_{p,N}=
\left\{a\in G/NG:
(\rho_p(a)+N\rho_p(G))\cap X_p\ne\varnothing\right\}. \tag{3.1}
$$

Here $\rho_p(a)$ means the image of any representative. A different
representative changes it by an element of $N\rho_p(G)$, so (3.1) is well
defined. Equivalently, $a$ survives if some element of its global coset has
reduction in the special Abel image.

If $G$ is given by torsion generators and a free basis, $G/NG$ is explicit:
the free part contributes $(\mathbf Z/N\mathbf Z)^r$, while a cyclic torsion
factor of order $m$ contributes a cyclic factor of order $\gcd(m,N)$. The
reduction matrix on generators turns (3.1) into finite abelian group
arithmetic.

Here is the finite algebra in more detail. Choose an invariant-factor
presentation

$$
G=\mathbf ZP_1\oplus\cdots\oplus\mathbf ZP_r
\oplus\bigoplus_{i=1}^s\mathbf Z/d_i\mathbf Z\,T_i,
\qquad d_i\mid d_{i+1}. \tag{3.1a}
$$

At $p$, express $\rho_p(P_i)$ and $\rho_p(T_i)$ in a proved presentation of
$J(\mathbf F_p)$. For each $Q\in C(\mathbf F_p)$, solving

$$
\rho_p(a)+N\sum_i z_i\rho_p(P_i)
+N\sum_i e_i\rho_p(T_i)=j_p(Q) \tag{3.1b}
$$

is a finite system of linear congruences. Smith normal form turns it into
independent divisibility tests. This proves both membership and
nonmembership: a failed divisibility condition is a witness that the two
finite cosets are disjoint. No discrete logarithm is required in the whole
finite Jacobian when only the image of $G$ is relevant.

The torsion terms in (3.1a) explain why coefficient vectors must be reduced
with care. The free coefficient of $P_i$ is read modulo $N$, but the
coefficient of $T_i$ is read modulo $\gcd(N,d_i)$ in $G/NG$. In the image
$J(\mathbf F_p)$, however, its order may drop if $p$ divides $d_i$ or if the
reduction kernel contains primary torsion. The actual reduced element, not
the abstract order $d_i$, belongs in (3.1b).

### 3.2 The basic Mordell--Weil sieve theorem

**Theorem 3.1.** For every finite set $\mathcal P$ of good primes,

$$
\pi_N(j(C(\mathbf Q)))\subseteq
S_N(\mathcal P):=\bigcap_{p\in\mathcal P}S_{p,N}. \tag{3.2}
$$

In particular, if $S_N(\mathcal P)=\varnothing$, then
$C(\mathbf Q)=\varnothing$.

**Proof strategy.** Follow one rational point through the commuting reduction
square, remembering that only its coset modulo $NG$ is retained.

Let $P\in C(\mathbf Q)$ and put $a=\pi_N(j(P))$. For each $p$, choose
$j(P)$ itself as representative of $a$. Proposition 2.2 gives
$\rho_p(j(P))\in X_p$, so the coset
$\rho_p(j(P))+N\rho_p(G)$ meets $X_p$. Thus $a\in S_{p,N}$ for every
$p\in\mathcal P$, proving (3.2). The final assertion is immediate. $\square$

The theorem is one-sided. A surviving class is locally compatible with the
chosen finite information; it need not come from a rational point. The sieve
proves nonexistence by elimination, not existence by survival.

There is a useful variant for a translated curve. If the global classes to
be tested lie in $W+G$ inside a larger finitely generated group, replace
$X_p$ by $X_p-\rho_p(W)$ and run the same theorem on $G$. This is how one
handles a rational degree-one divisor class not represented by the chosen
base point, or one coset of a finite-index subgroup. The translation must be
carried at every prime. The proof is unchanged because reduction is a
homomorphism.

### 3.3 Several primes and one intersection

Separate prime conditions forget that all reductions must come from the
same element of one global coset. To retain that information, combine the
reductions into

$$
\rho_{\mathcal P}:G\longrightarrow
\prod_{p\in\mathcal P}J(\mathbf F_p), \tag{3.3}
$$

and put $X_{\mathcal P}=\prod_pX_p$. Define the **joint survivor set** by

$$
S^{\mathrm{joint}}_N(\mathcal P)=
\left\{a\in G/NG:
(\rho_{\mathcal P}(a)+N\rho_{\mathcal P}(G))
\cap X_{\mathcal P}\ne\varnothing\right\}. \tag{3.4}
$$

Following one rational point at all primes with one representative proves

$$
\pi_N(j(C(\mathbf Q)))\subseteq
S^{\mathrm{joint}}_N(\mathcal P)
\subseteq S_N(\mathcal P). \tag{3.4a}
$$

The second inclusion follows by projection to each factor. It can be strict:
membership in every $S_{p,N}$ may be witnessed by different elements of the
global coset, whereas (3.4) requires one element whose reductions work
simultaneously. This is why the product formulation can be stronger than the
plain intersection in Theorem 3.1. Independent reduction matrices couple
the local choices through one global coefficient vector.

For a cyclic group $G=\langle T\rangle$ of order $m$, every class is $nT$.
If $N$ is divisible by $m$, then $NG=0$ and the sieve tests the actual class,
not merely a congruence class. At a good prime $p\nmid m$, torsion reduction
is injective, so $\bar T$ still has order $m$. Hence

$$
nT\in j(C(\mathbf Q))
\Longrightarrow n\bar T\in X_p, \tag{3.5}
$$

and a single finite table can be terminal. This is exactly the form used for
$X_1(13)$.

### 3.4 What a surviving class means

Suppose the final set equals the classes of known points. If $NG\ne0$, this
still says only that every unknown point would differ from a known Abel class
by an element of $NG$. There may be infinitely many such elements when the
rank is positive. A completeness proof therefore needs one more step: lift
the modulus, bound the possible coefficients, use sharper local information,
or invoke an independent argument on each surviving residue disk.

By contrast, if $NG=0$, each surviving element is an exact element of $G$.
If it equals $j(Q)$ for a known $Q$, then any $P$ with that class satisfies
$j(P)=j(Q)$ and Proposition 2.1 gives $P=Q$. Finite Jacobians of rational
points are therefore an especially clean terminal setting.

## 4. Coset sieving and refinement

### 4.1 Cosets rather than points

Let $\Gamma\simeq\mathbf Z^r\oplus T$ be a known Mordell--Weil group. A
finite quotient does not enumerate its elements; it partitions them into
cosets. Store a candidate as

$$
a+N\Gamma. \tag{4.1}
$$

At a good prime $p$, this coset is eliminated precisely when

$$
(\rho_p(a)+N\rho_p(\Gamma))\cap X_p=\varnothing. \tag{4.2}
$$

The subgroup $N\rho_p(\Gamma)$, rather than $NJ(\mathbf F_p)$, is the correct
one. The two agree only when the reduction of $\Gamma$ is all of the finite
Jacobian. Replacing one by the other can retain too much or, if used in the
wrong direction, discard a genuine rational point.

### 4.2 Lifting a modulus

Suppose $M\ge1$. The children of $a+N\Gamma$ modulo $MN\Gamma$ are

$$
a+Nb+MN\Gamma,
\qquad b\in B_{M,N}, \tag{4.3}
$$

where $B_{M,N}$ is a set of representatives for the image of
$\Gamma/M\Gamma$ under $b\mapsto Nb$ in $N\Gamma/MN\Gamma$.
Each child is tested by (4.2), perhaps at new primes. This separates global
elements that were indistinguishable modulo $N$.

**Lemma 4.1.** The cosets in (4.3) are disjoint and their union is
$a+N\Gamma$.

**Proof.** Every $N\gamma$ has $\gamma=b+M\delta$ for one class
$b\in\Gamma/M\Gamma$, and replacing it by the chosen representative of its
image changes $Nb$ by an element of $MN\Gamma$. This gives membership in one
of (4.3). Two chosen representatives give the same child exactly when their
images in $N\Gamma/MN\Gamma$ agree, which the definition of $B_{M,N}$
excludes. Thus the children are disjoint and cover the parent. $\square$

### 4.3 A proof of exhaustive refinement

Let $\mathcal A_N$ be a list of surviving cosets modulo $N\Gamma$. Replace
each by all children (4.3), then delete those failing any local test. By
Theorem 3.1 and Lemma 4.1, every class $j(P)$ lying in the original union lies
in exactly one retained child. Induction gives:

**Proposition 4.2.** At every stage of a coset refinement, the retained union
contains $j(C(\mathbf Q))$, provided the initial union does and every deletion
is justified by an exact local image condition.

This invariant is the logical core of an exhaustive sieve. It is stronger
than saying that many primes were tried: it records that no branch containing
a rational point was ever dropped.

Termination needs a finite target. Suppose a proved height argument places
every possible $j(P)$ in a finite subset $B\subset\Gamma$. Choose a modulus
for which distinct elements of $B$ have distinct images; such a modulus
exists because $B-B$ is finite. Refinement to that modulus reduces the
problem to testing the individual elements of $B$. Alternatively, if
$\Gamma$ itself is finite, take $N$ divisible by its exponent and the first
quotient already consists of individual elements.

Let us spell out how a height bound becomes such a finite set. Fix the free
basis $P_1,\ldots,P_r$ and write

$$
Q=T+\sum_{i=1}^rn_iP_i. \tag{4.4}
$$

If $H=(\langle P_i,P_j\rangle)$ is the canonical-height Gram matrix and
$\lambda_{min}>0$ is a proved lower bound for its least eigenvalue, then

$$
\widehat h(Q-T)=\mathbf n^{\!t}H\mathbf n
\ge\lambda_{min}\sum_i n_i^2. \tag{4.5}
$$

An upper bound $\widehat h(j(P)-T)\le B_0$ therefore implies
$|n_i|\le\sqrt{B_0/\lambda_{min}}$ for every $i$. Including the finitely
many torsion possibilities gives an explicit box. The height pairing and its
positive definiteness come from Book 41; an application must still prove the
numerical bounds $B_0$ and $\lambda_{min}$.

Given a finite box, one need not choose one enormous modulus. Refinement may
proceed through small factors, discarding branches as soon as they fail a
prime. The proof remains exhaustive because (4.3) partitions, rather than
samples, every parent. Eventually two distinct box elements are separated:
for their nonzero difference $D$, choose a modulus not dividing all free
coordinates and, if $D$ is torsion, divisible by the exponent of the whole
torsion subgroup. The latter choice makes the torsion projection of the
multiple subgroup zero. Divisibility merely by the order of $D$ would not
suffice: in $\mathbf Z/4\mathbf Z$, the element of order two lies in twice
the group. Taking a common multiple for the finitely many differences proves
termination.

### 4.4 Separating known points

Let $K\subset C(\mathbf Q)$ be a proved list. A convenient ledger labels a
surviving coset as **accounted for** only when a terminal argument shows that
it contains exactly the Abel class of one member of $K$. Merely containing a
known class is insufficient when the coset has other elements.

There are three sound terminal patterns:

1. the coset is a singleton because the ambient group is finite and the
   modulus annihilates it;
2. a height bound shows that its intersection with the finite search region
   is the single known class;
3. a local analytic argument shows that the corresponding residue disk
   contains the single known point.

In every case Abel--Jacobi injectivity converts uniqueness of the class into
uniqueness of the curve point.

## 5. Local images and reduction sets

### 5.1 Good primes away from the modulus

Reduction sets use only $C(\mathbf F_p)$, but it is useful to know when they
are the full local condition. Let $p$ be a good prime and let $N$ be prime
to $p$. The kernel of

$$
J(\mathbf Q_p)\longrightarrow J(\mathbf F_p) \tag{5.1}
$$

is a pro-$p$ formal group. Multiplication by $N$ is an automorphism of that
kernel because its linear term is the unit $N$. The snake lemma therefore
gives

$$
J(\mathbf Q_p)/NJ(\mathbf Q_p)
\simeq J(\mathbf F_p)/NJ(\mathbf F_p). \tag{5.2}
$$

**Proof detail.** Surjectivity of reduction follows from smoothness. On the
formal kernel, successive quotients are additive groups of characteristic
$p$, so multiplication by $N$ is invertible on every quotient and hence on
the inverse limit. Taking kernels and cokernels of multiplication by $N$ in
the reduction exact sequence proves (5.2).

Consequently the image of $C(\mathbf Q_p)$ in the quotient on the left is
the image of $C(\mathbf F_p)$ on the right. Hensel lifting supplies a local
point above every smooth special point. Thus, away from the modulus, the
finite reduction set is not a crude sample: it is the complete local image
at that quotient level.

### 5.2 Primes dividing the modulus

When $p\mid N$, multiplication by $N$ is no longer invertible on the formal
group. Two points with the same reduction can have different classes modulo
$NJ(\mathbf Q_p)$. The special-fiber set remains a necessary condition, but
not the full local condition.

To recover the full image, cover $C(\mathbf Q_p)$ by residue disks. Choose a
local parameter $t$ in each disk and expand the Abel map in the formal group.
After passing to a sufficiently deep formal neighborhood, the formal
logarithm is an isomorphism onto a full $\mathbf Z_p$-lattice. There is then
a depth $e$ such that congruence modulo $p^e$ forces equality modulo
$NJ(\mathbf Q_p)$: on that lattice the assertion is the containment
$p^e\mathbf Z_p^g\subseteq N\mathbf Z_p^g$, after a fixed choice of basis.
Enumerating the finitely many parameter classes modulo the resulting depth
therefore gives the complete local image.

At $p=2$, one must also retain enough unit precision for square decisions;
at an odd $p\mid N$, valuation and residue data together with the formal
depth suffice. Apparent stabilization before a proved depth is evidence, not
a completeness argument.

For a residue disk containing $Q_0$, write $P(t)$ for its points and choose
formal parameters $Z_1,\ldots,Z_g$ at the identity of $J$. The Abel
difference has expansions

$$
Z_i(j(P(t))-j(Q_0))=a_{i,1}t+a_{i,2}t^2+\cdots. \tag{5.3}
$$

If $N=p^km$ with $p\nmid m$, the factor $m$ is invertible on the formal
group. It is enough to retain the expansions modulo the precision at which
every omitted term lies in $p^k\mathbf Z_p^g$ after applying the formal
logarithm. A lower bound on the valuations of $a_{i,n}$ supplies that
precision. The finitely many values of $t$ modulo the resulting power of
$p$ then give every class in the disk modulo $NJ(\mathbf Q_p)$.

Disks meeting a Weierstrass point or infinity require a uniformizer valid
there, not the affine $x$-coordinate. On a quintic, a parameter at infinity
may be chosen so that $x$ has pole order two and $y$ pole order five. At a
branch point, $y$ is a parameter and $x-a$ begins with a nonzero multiple of
$y^2$. These choices ensure that the expansion covers the full disk and does
not silently omit tangent divisors.

### 5.3 Bad reduction and component data

At bad reduction, (5.2) need not hold. Let $\mathcal J$ be the Néron model.
Reduction first lands in $\mathcal J(\mathbf F_p)$, whose identity component
and component group both matter. A regular model of $C$ determines which
components rational points can meet, and the extended Abel map records the
corresponding component classes.

A bad prime can be used safely if the following data are supplied: a regular
or semistable model, the component met by each residue family, the component
group of $J$, the formal identity-neighborhood quotient, and the image of
each family. Without these data, reducing the singular affine equation and
forming its naive Picard group does not define the required constraint.

The two final applications need only good primes for their sieves. Bad
places entered the preceding descent calculations, but they are not reused
as if their special fibers were good.

### 5.4 Exact finite image certificates

For a good prime, a finite certificate consists of:

- a squarefreeness or smoothness check for the reduced curve;
- a complete list of $C(\mathbf F_p)$;
- a proved presentation of the relevant subgroup of $J(\mathbf F_p)$;
- reductions of every global generator;
- the Abel class of every special point in the same presentation.

For an odd-degree genus-two model, the last two rows use the unique Mumford
pairs of Book 136. Curve enumeration and Jacobian order may be checked
independently by counts over $\mathbf F_p$ and $\mathbf F_{p^2}$. If only a
known cyclic subgroup is needed, it is enough to display its entire list of
multiples and compare all curve classes with that list; no assertion about
the rest of the finite Jacobian is required.

## 6. Saturation and finite-index subgroups

### 6.1 Why finite index is not equality

Suppose descent proves that points $P_1,\ldots,P_r$ are independent and that
their subgroup $\Gamma$ has finite index in $J(\mathbf Q)$, but does not
determine the index. Sieving only $\Gamma$ can lose rational points whose
Abel classes lie in another coset. Even an odd index matters: a two-descent
which attains the rank bound proves two-saturation, not saturation at every
odd prime.

For a subgroup of the same rank, define $\Gamma$ to be **$\ell$-saturated**
if

$$
\ell P\in\Gamma\quad\Longrightarrow\quad P\in\Gamma
\qquad(P\in J(\mathbf Q)). \tag{6.1}
$$

Equivalently, $J(\mathbf Q)/\Gamma$ has no element of order $\ell$.
Therefore $\Gamma=J(\mathbf Q)$ precisely when it contains the full torsion,
has the full rank, and is $\ell$-saturated for every prime dividing its
finite index.

### 6.2 Prime-by-prime saturation

Two-descent controls the prime two. If the images of $\Gamma$ span
$J(\mathbf Q)/2J(\mathbf Q)$, then $\Gamma$ is two-saturated. Indeed,
surjectivity says

$$
J(\mathbf Q)=\Gamma+2J(\mathbf Q). \tag{6.1a}
$$

Because $\Gamma$ has finite index, the finite quotient
$A=J(\mathbf Q)/\Gamma$ therefore satisfies $A=2A$. Multiplication by two on
a finite group is then bijective, so $A[2]=0$. If $2P\in\Gamma$, the class
of $P$ in $A$ has order dividing two and must vanish; hence $P\in\Gamma$.
Containing the known rational two-torsion remains necessary when one wants
$\Gamma$ to be the full Mordell--Weil group, but it is not the step that
proves this saturation criterion.

For an odd prime $\ell$, reduction gives a similarly finite test. It is not
enough that one generator have nonzero reduction. One must test the kernel
on the whole vector space $\Gamma/\ell\Gamma$, including torsion
coordinates when they contribute.

### 6.3 Reduction kernels as saturation certificates

**Theorem 6.1 (reduction saturation criterion).** Let
$\Gamma\subseteq J(\mathbf Q)$ contain $J(\mathbf Q)[\ell]$. Let
$p_1,\ldots,p_s$ be good primes, none equal to $\ell$. If

$$
\ker\left(
\Gamma/\ell\Gamma\longrightarrow
\prod_{i=1}^sJ(\mathbf F_{p_i})/\ell J(\mathbf F_{p_i})
\right)=0, \tag{6.2}
$$

then $\Gamma$ is $\ell$-saturated.

**Proof.** Suppose $\ell P=Q\in\Gamma$. For every $i$, the reduction of $Q$
is $\ell\rho_{p_i}(P)$, so the class of $Q$ maps to zero in each finite
quotient. By (6.2), $Q=\ell R$ for some $R\in\Gamma$. Hence
$P-R\in J(\mathbf Q)[\ell]\subseteq\Gamma$, and $P\in\Gamma$. $\square$

To verify (6.2), express the reductions of a basis in invariant-factor
coordinates for each finite Jacobian, reduce the coordinate matrices modulo
$\ell$, and intersect their kernels. Several small primes can give zero
intersection even when no one matrix is injective.

### 6.4 Closing the finite list of primes

Saturation at arbitrarily many primes is not a finite certificate until a
bound restricts which primes can divide the index. Such a bound may come from
a descent index, from a height enumeration, or from regulators.

For the last method, let $P_1,\ldots,P_r$ generate the free part of
$\Gamma$, and let $R_\Gamma$ be the determinant of their canonical-height
Gram matrix. If $Q_1,\ldots,Q_r$ is a basis of the full Mordell--Weil lattice
and $I=[J(\mathbf Q)_{\mathrm{free}}:\Gamma_{\mathrm{free}}]$, change of
basis gives

$$
R_\Gamma=I^2R_J. \tag{6.3}
$$

A proved positive lower bound for $R_J$ therefore bounds $I$. The qualitative
height gap of Book 41 proves discreteness; an effective certificate must
state the numerical lower bound and its hypotheses. After factoring the
resulting index bound, Theorem 6.1 tests the finite list of possible primes.

In both curves treated later the rank is zero. Book 137 proves the entire
torsion subgroup by independent good-reduction upper bounds, so there is no
free-part saturation gap at all.

## 7. Completeness certificates

### 7.1 The global ledger

A complete global ledger records the curve, its smooth projective model, the
base point, and the resulting Abel map. It then gives the structure of
$J(\mathbf Q)$, exact generators, their relations, and the proof that no
additional rank or torsion exists.

The logical provenance matters. Finite generation comes from the
Mordell--Weil theorem of Book 41. Book 148 supplies the marked modular curve
models and the interpretation of their boundary values. Exact polynomial
arithmetic, specialization, finite-field groups, and torsion bounds come from
Book 136 under its pointed quintic hypotheses. The rank and torsion
computations for the two present curves are the completed descents of Book
137. This book uses those results; it does not infer either Mordell--Weil
group from the point set it aims to prove.

If the global result comes from descent, the ledger also distinguishes the
following assertions:

$$
\begin{array}{c}
\text{Selmer dimension}\Rightarrow\text{rank upper bound},\\
\text{displayed independent points}\Rightarrow\text{rank lower bound},\\
\text{good reductions}\Rightarrow\text{torsion upper bound},\\
\text{exact relations}\Rightarrow\text{torsion lower bound},\\
\text{saturation tests}\Rightarrow\text{index one}.
\end{array} \tag{7.0}
$$

No arrow may be reversed without a separate theorem. In particular, a rank
upper bound does not say displayed generators have index one, and a torsion
order dividing a finite-field order does not exhibit rational torsion.

### 7.2 The finite-prime ledger

For each good prime $p$, record:

$$
\bigl(C(\mathbf F_p),\ J(\mathbf F_p),\ X_p,
\rho_p(\text{global generators})\bigr). \tag{7.1}
$$

All entries must use one base point and one sign convention. If a coordinate
change sends a branch point to infinity, record the map, the new base point,
and the images of the old points at infinity. If the transformed quintic is
rescaled to be monic, rescale the $y$-coordinate in every Mumford pair.

Completeness of $C(\mathbf F_p)$ is a finite field enumeration. Completeness
of a cyclic subgroup table follows by displaying one identity at its exact
order and distinct normalized representatives before it. Completeness of a
full finite Jacobian may instead be checked by reduced-pair enumeration and
an independent Frobenius order.

### 7.3 The coset ledger

At stage $k$, a coset ledger contains:

$$
N_k,\qquad \mathcal A_k\subseteq\Gamma/N_k\Gamma,
\qquad\mathcal P_k, \tag{7.2}
$$

where $\mathcal A_k$ is exactly the set surviving all primes used so far.
For every deletion it records a prime $p$ for which (4.2) is empty. For every
refinement it records the parent-child map. Proposition 4.2 then proves by
induction that every rational Abel class remains in the retained union.

The last line must say why each survivor is terminal. A phrase such as “no
new points were found” is not a terminal line. A singleton class, a complete
height box, or a unique local zero is.

It is useful to attach a witness to each discarded coset. For a prime $p$,
the witness can be the image of the representative, generators of
$N\rho_p(\Gamma)$, the complete list $X_p$, and the row-reduced congruence
showing empty intersection. Such witnesses make the direction of every map
visible and prevent a condition computed in $J(\mathbf F_p)/NJ(\mathbf F_p)$
from being confused with one computed modulo $N\rho_p(\Gamma)$.

For an accounted survivor, the witness consists of the known point, its
exact global Abel class, and the terminal reason. When the terminal reason is
local uniqueness, the ledger includes the residue disk, the local function,
and its zero bound. When it is a finite group, it includes the annihilating
modulus and the unique normalized representative.

### 7.4 A reusable completeness theorem

**Theorem 7.1 (finite sieve certificate).** Suppose the following data have
been proved:

1. $j:C\hookrightarrow J$ is an Abel--Jacobi embedding over $\mathbf Q$;
2. $\Gamma=J(\mathbf Q)$ is given exactly, or every coset of a certified
   finite-index $\Gamma$ is included;
3. every local constraint used in a finite coset ledger is complete;
4. a proved global search region contains $j(C(\mathbf Q))$, and the
   intersection of the retained union with that region consists only of the
   exact Abel classes of a finite known set $K\subseteq C(\mathbf Q)$.

Then $C(\mathbf Q)=K$.

**Proof.** Proposition 4.2 places $j(P)$ for every rational $P$ in the final
retained union. Hypothesis 4 identifies that class with $j(Q)$ for some
$Q\in K$. Proposition 2.1 gives $P=Q$. The reverse inclusion is part of the
assertion that $K$ is a known set of rational points. $\square$

When $J(\mathbf Q)$ is finite, the search region is the whole group and a
multiple of its exponent makes every quotient coset a singleton. The theorem
then reduces to a finite Abel-image comparison.

## 8. Prime selection and efficient intersections

### 8.1 What makes a prime useful

A good prime is useful when the reduction of the Mordell--Weil group occupies
a small, nontrivially placed subgroup and the special Abel image meets that
subgroup sparsely. The size of $C(\mathbf F_p)$ alone is not decisive. The
relevant ratio is

$$
\frac{|X_p\cap\rho_p(G)|}{|\rho_p(G)|}. \tag{8.1}
$$

For a cyclic torsion group, a prime at which torsion injects turns (8.1) into
a literal count of allowed exponents. For a positive-rank lattice modulo
$N$, useful primes are those whose reduction matrices detect independent
linear combinations.

There is a second consideration: independence among primes. If two
reductions induce the same kernel on $G/NG$ and their Abel images pull back
to the same subset, the second adds no information. A prime is valuable when
its excluded cosets cut transversely to the exclusions already obtained.
This is measured exactly by recomputing the size of the intersection, not by
the size of either finite Jacobian.

Prime selection never enters the proof after the finite data are certified.
It affects only economy. One may inspect candidate good primes, retain a
small set giving strong independent cuts, and then present the final exact
tables. The proof rests on those tables and Theorem 3.1, not on a statistical
expectation that random subsets should intersect sparsely.

A prime used for torsion injectivity must have residue characteristic prime
to the torsion order. A prime used for the local isomorphism (5.2) must also
be prime to the modulus. A prime merely used for the necessary condition
(2.3) needs only good reduction.

### 8.2 Chinese remaindering finite information

Suppose different primes naturally see different moduli $N_p$, perhaps the
exponent of $\rho_p(G)$. Lift every condition to
$N=\operatorname{lcm}_pN_p$. The projection

$$
G/NG\longrightarrow G/N_pG \tag{8.2}
$$

pulls the $p$-condition back to the common quotient. Intersecting there is
the correct Chinese-remainder operation. Intersecting sets of unrelated
integer labels without transporting them through the global basis has no
invariant meaning.

If the moduli are coprime on the free part, the ordinary Chinese remainder
theorem decomposes the coefficient vectors. Torsion factors require their
own gcds, but the finite abelian group $G/NG$ handles them automatically.

### 8.3 Symmetry and involution

The hyperelliptic involution can halve a finite table when its translation is
recorded correctly. On a pointed quintic,

$$
j_\infty(\iota P)=-j_\infty(P). \tag{8.3}
$$

On a sextic based at $\infty^+$, equation (2.5) gives instead

$$
j_{\infty^+}(\iota P)=T-j_{\infty^+}(P). \tag{8.4}
$$

Thus allowed exponent sets are stable under $n\mapsto-n$ in the first case
and under $n\mapsto1-n$ when $T$ is the chosen generator in the second. The
$X_1(13)$ survivor set below is visibly stable under $n\mapsto1-n$.

### 8.4 Failure modes

The most common incomplete arguments can now be diagnosed precisely.

A finite-index subgroup is used as though saturated; a finite-field order is
used as though it determined group structure; coefficient reduction is used
at a bad prime; a few local points are used as though they formed the whole
local image; or a survivor is called rational merely because it survives.
Another subtle error changes the Abel base point between global and special
calculations. In even degree, confusing conjugation with negation produces
exactly such a translation error.

Each failure has a repair already proved: saturation matrices, invariant
factor certificates, smooth models, local dimension or residue-disk counts,
terminal exhaustion, and the base-point formula (2.4).

## 9. The Chabauty boundary

### 9.1 The rank inequality

The Mordell--Weil sieve and Chabauty's method both place the curve inside its
Jacobian, but they use different structures. Let $p$ be a good prime and let
$r=\operatorname{rank}J(\mathbf Q)$. The $p$-adic logarithms of rational
points span a subspace of the $g$-dimensional tangent space of $J$. If

$$
r<g, \tag{9.1}
$$

there is a nonzero regular differential $\omega$ annihilating the closure of
$J(\mathbf Q)$. Its integral along the Abel image vanishes at every rational
point. On each residue disk this integral is a convergent power series. Its
zero count is controlled by the valuations of its coefficients, through the
nonarchimedean Newton polygon or Strassmann's theorem; merely locating the
first formally nonzero coefficient without a valuation comparison is not a
zero bound.

The dimension count is exact: annihilating differentials form the orthogonal
complement of the logarithmic Mordell--Weil span. When $r<g$ it is nonzero.
When $r\ge g$, linear algebra alone supplies no such differential. This is
the **Chabauty boundary**. Crossing it does not make rational points
infinite; it removes this particular source of a $p$-adic function vanishing
on all of them.

### 9.2 How Chabauty and the sieve cooperate

Chabauty controls points inside a residue disk, while the Mordell--Weil sieve
controls which disks and group cosets are globally compatible. A standard
combined proof proceeds as follows. First, reduction and finite quotients
discard most disks. Second, on each surviving disk an annihilating integral
is expanded. If its normalized reduction has one simple zero, the disk
contains at most one rational point; a known point then accounts for it.

The two completeness checks are independent. The sieve must use the full
finite Abel image, and the local power series must have a proved zero bound.
One cannot infer either from the other. In difficult rank-one genus-two
examples this division of labor is especially effective: congruences select
the disks and the differential proves uniqueness within them.

### 9.3 What happens at and above the boundary

At $r=g$, the annihilator may be zero. The Mordell--Weil sieve still makes
sense because its proof used only finite generation, reduction, and an exact
finite quotient. It can remain decisive if sufficiently many reductions
separate all candidates in a bounded region. At $r>g$ the same statement is
true, although the lattice to be sieved is larger.

Conversely, the inequality $r<g$ does not by itself finish a rational-point
determination. Multiple zeros, residue characteristic issues, and disks on
which the reduced differential vanishes require care. Thus Chabauty is not a
replacement for saturation or for an exact Mordell--Weil group.

Both present curves have rank zero and genus two, so they lie strictly below
the boundary. Nevertheless, their rational Jacobians are completely finite.
Testing all their group classes is shorter and stronger than introducing
local integrals: it gives an exact Abel-image certificate with no unresolved
disk. This also illustrates that the sieve is a method in its own right, not
merely a preliminary to Chabauty.

## 10. The genus-two curve $X_1(13)$

### 10.1 The curve and its Jacobian

Book 148 derives, by reversible changes from the order-thirteen Tate normal
form, the smooth projective modular curve whose affine model is

$$
y^2+(x^3+x^2+1)y=x^2+x. \tag{10.1}
$$

With

$$
z=2y+x^3+x^2+1,
$$

it becomes

$$
C_{13}:z^2=F(x), \tag{10.2}
$$

where

$$
F(x)=x^6+2x^5+x^4+2x^3+6x^2+4x+1,
\qquad \operatorname{disc}(F)=-2^{12}13^2. \tag{10.3}
$$

There are two rational points $\infty^+,\infty^-$ above infinity,
distinguished by $z/x^3\to+1$ and $-1$. Set

$$
j(P)=[P-\infty^+],\qquad
T=[\infty^--\infty^+]. \tag{10.4}
$$

Book 137 proves, by true sextic two-descent and independent good-reduction
torsion bounds, that

$$
J_{13}(\mathbf Q)=\langle T\rangle\simeq\mathbf Z/19\mathbf Z. \tag{10.5}
$$

This imports exactly an equality of groups. The even-degree fake descent was
lifted to the true Selmer group there; no fake-target dimension is being
used as a rank statement here.

The six evident rational points are

$$
\mathcal K_{13}={
\infty^+,\infty^-,(0,0),(0,-1),(-1,0),(-1,-1)}, \tag{10.6}
$$

where the affine coordinates in (10.6) are those of (10.1). Direct
substitution proves that they lie on the curve. The same Tate-normal-form
derivation in Book 148 identifies these six points, including the two
branches at infinity, as precisely the six rational outward cusps. That
identification uses no rational-point classification. We will prove there
are no other rational points.

### 10.2 A good reduction at seventeen

The prime $17$ is good by (10.3), and it is prime to $19$. Hence reduction
is injective on the whole group (10.5). Modulo $17$, the sextic $F$ has the
simple root $x=1$. Send this branch point to infinity by

$$
X=\frac1{x-1},\qquad Y=zX^3,
\qquad w=Y/5. \tag{10.7}
$$

Since $5^2=8$ in $\mathbf F_{17}$, the transformed equation is the pointed
monic quintic

$$
w^2=g(X)=X^5+13X^4+10X^3+16X^2+X+15. \tag{10.8}
$$

Indeed

$$
X^6F(1+X^{-1})
=8X^5+2X^4+12X^3+9X^2+8X+1,
$$

and division by $25=8$ gives (10.8). Its squarefreeness follows either by a
direct gcd with $g'$ or from good reduction and the invertible coordinate
change. The old branch point $(1,0)$ is the new point at infinity. The old
points $\infty^+,\infty^-$ become $(0,7)$ and $(0,10)$ because
$1/5=7$ in $\mathbf F_{17}$.

We use reduced pairs for (10.8), with coefficient lists written as
polynomials in $X$. Subtracting the pair of $(0,7)$ from that of $(0,10)$
gives

$$
\bar T=[X^2,10+6X]. \tag{10.9}
$$

Exact Cantor addition gives $19\bar T=0$, and the following nineteen reduced
pairs are distinct. The table is therefore a complete certificate for the
cyclic subgroup $\langle\bar T\rangle$.

$$
\begin{array}{c|c|c@{\qquad}c|c|c}
n&u_n&v_n&n&u_n&v_n\\ \hline
0&1&0&10&X^2+10X+9&4+14X\\
1&X^2&10+6X&11&X^2+2X+1&11+X\\
2&X^2+10X+9&1+8X&12&X^2+X+13&6X\\
3&X^2+9X&7+8X&13&X^2+X&7\\
4&X^2+9X&10+14X&14&X^2+X&10+3X\\
5&X^2+X&7+14X&15&X^2+9X&7+3X\\
6&X^2+X&10&16&X^2+9X&10+9X\\
7&X^2+X+13&11X&17&X^2+10X+9&16+9X\\
8&X^2+2X+1&6+16X&18&X^2&7+11X\\
9&X^2+10X+9&13+3X&&&
\end{array} \tag{10.10}
$$

Every row is checked by $u_n\mid g-v_n^2$, the reduced degree condition, and
the recurrence $[u_{n+1},v_{n+1}]=[u_n,v_n]+\bar T$. Distinct normalized
pairs prove distinctness without an appeal to numerical approximation.

### 10.3 The finite Abel-image calculation

The complete special-fiber point list is

$$
\begin{aligned}
C_{13}(\mathbf F_{17})=\{&\infty^+,\infty^-,
(0,\pm1),(1,0),(6,\pm6),(8,0),\\
&(12,\pm2),(13,\pm8),(15,0),(16,\pm1)\},
\end{aligned} \tag{10.11}
$$

in the original $(x,z)$ coordinates. Checking the seventeen values of
$F(x)$ against the square list in $\mathbf F_{17}$ proves that (10.11) is
exhaustive.

Transform each point by (10.7), take its degree-one pair relative to the new
branch point, and subtract the pair of $(0,7)$ to retain the global base
$\infty^+$. Comparison with (10.10) gives

$$
\begin{array}{c|c|c}
P&j_{17}(P)=[u,v]&n\text{ if }j_{17}(P)=n\bar T\\ \hline
\infty^+&[1,0]&0\\
\infty^-&[X^2,10+6X]&1\\
(0,1)&[X^2+X,10]&6\\
(0,-1)&[X^2+X,10+3X]&14\\
(1,0)&[X,10]&-\\
(6,6)&[X^2+10X,10+2X]&-\\
(6,-6)&[X^2+10X,10]&-\\
(8,0)&[X^2+12X,10+15X]&-\\
(12,2)&[X^2+3X,10+16X]&-\\
(12,-2)&[X^2+3X,10+2X]&-\\
(13,8)&[X^2+7X,10+6X]&-\\
(13,-8)&[X^2+7X,10+9X]&-\\
(15,0)&[X^2+6X,10+13X]&-\\
(16,1)&[X^2+9X,10+9X]&16\\
(16,-1)&[X^2+9X,10+14X]&4
\end{array} \tag{10.12}
$$

The dashes are exact nonmembership statements: their normalized pairs differ
from every row of (10.10). Thus

$$
X_{17}\cap\langle\bar T\rangle
=\{0,1,4,6,14,16\}\bar T. \tag{10.13}
$$

This calculation needs no determination of the complementary part of
$J(\mathbf F_{17})$. It enumerates the whole special curve and the whole
reduction of the rational Mordell--Weil group, which are precisely the two
sets entering the sieve.

## 11. The exhaustive sieve for $X_1(13)$

### 11.1 The six surviving classes

Take modulus $N=19$. Since $19J_{13}(\mathbf Q)=0$, every coset modulo
$NJ_{13}(\mathbf Q)$ is a singleton. The good-prime sieve at $17$ and
(10.13) give

$$
j(C_{13}(\mathbf Q))
\subseteq\{0,T,4T,6T,14T,16T\}. \tag{11.1}
$$

Reduction is injective on $19$-torsion because $17\ne19$. Comparing the six
known points with (10.12) therefore proves the global identities

$$
\begin{array}{c|c}
P&j(P)\\ \hline
\infty^+&0\\
\infty^-&T\\
(0,0)&6T\\
(0,-1)&14T\\
(-1,0)&16T\\
(-1,-1)&4T.
\end{array} \tag{11.2}
$$

Here $z=2y+x^3+x^2+1$ sends the four affine points in (10.6) to the
corresponding $(0,\pm1)$ and $(16,\pm1)$ rows of (10.12).

Two divisor checks independently confirm the labeling. From
$\operatorname{div}(x)=P_{0,0}+P_{0,-1}-\infty^+-\infty^-$ one gets
$6T+14T=T$. The same identity with $x+1$ gives $16T+4T=T$. Moreover the
pole and zero orders of $y$ give $6T+16T=3T$. All three congruences hold
modulo $19$.

### 11.2 Completeness and uniqueness

Let $P\in C_{13}(\mathbf Q)$. By (10.5), $j(P)=nT$ for a unique
$n\in\mathbf Z/19\mathbf Z$. The commuting square (2.2) and table (10.12)
force $n$ into the six-element set (10.13). Table (11.2) supplies a known
point $Q$ with $j(Q)=nT$. Proposition 2.1 then gives $P=Q$.

Every completeness condition is now visible:

- (10.5) is the complete, true Mordell--Weil group, so no unsieved coset is
  missing;
- $17$ is good and prime to $19$, so reduction of the rational group is
  injective;
- (10.11) is the whole special curve;
- (10.10) is the whole reduced rational subgroup;
- modulus $19$ annihilates the group, so every survivor is a singleton;
- Abel--Jacobi injectivity converts class equality to point equality.

There is no height bound, untested saturation prime, fake descent class, or
unresolved residue disk in this conclusion.

### 11.3 The exact rational-point set

**Theorem 11.1.** On the model (10.1),

$$
\boxed{
C_{13}(\mathbf Q)=
\{\infty^+,\infty^-,(0,0),(0,-1),(-1,0),(-1,-1)\}.} \tag{11.3}
$$

**Proof.** Direct substitution and the two branches at infinity give the
inclusion from right to left. Sections 11.1--11.2 prove the reverse
inclusion. $\square$

These six points are the rational cusps on $X_1(13)$. The modular
interpretation and the boundary identification are the Tate-normal-form
calculation of Book 148; the arithmetic proof of (11.3) itself used only the
smooth curve, its Jacobian, and the exhaustive finite sieve.

## 12. The mixed-seven curve

### 12.1 The curve and the complete Mordell--Weil group

Consider

$$
C_7:z^2=f(t),\qquad
f(t)=t(t-1)(t^3-8t^2+5t+1). \tag{12.1}
$$

Thus

$$
f(t)=t^5-9t^4+13t^3-4t^2-t,
\qquad\operatorname{disc}(f)=7^4. \tag{12.2}
$$

The polynomial is monic and squarefree, and the unique point $\infty$ at
infinity is rational. Use $j=j_\infty$. Define

$$
T_0=[t,0],\qquad T_1=[t-1,0],\qquad
A=[t^2-t+1,1-3t]. \tag{12.3}
$$

Book 137 proves the exact relations and the complete group

$$
J_7(\mathbf Q)=
\langle A\rangle\oplus\langle T_0\rangle\oplus\langle T_1\rangle
\simeq\mathbf Z/3\mathbf Z\oplus(\mathbf Z/2\mathbf Z)^2. \tag{12.4}
$$

The proof there includes the two-Selmer rank bound, exact Cantor relations,
and good-reduction orders $12$ and $48$ at $3$ and $5$. Hence (12.4) is an
equality, not merely a visible subgroup. In rank zero, determining the full
torsion group simultaneously closes every saturation question.

### 12.2 All twelve reduced classes

Write a group element as $aA+bT_0+cT_1$ with
$a\in\{0,1,2\}$ and $b,c\in\{0,1\}$. Exact Cantor addition and reduction
give the complete table

$$
\begin{array}{c|c|c}
(a,b,c)&u&v\\ \hline
(0,0,0)&1&0\\
(0,0,1)&t-1&0\\
(0,1,0)&t&0\\
(0,1,1)&t^2-t&0\\
(1,0,0)&t^2-t+1&1-3t\\
(1,0,1)&t^2-11t+9&15-17t\\
(1,1,0)&t^2-9t-1&1+11t\\
(1,1,1)&t^2-\frac79t-\frac19&\frac5{27}-\frac1{27}t\\
(2,0,0)&t^2-t+1&-1+3t\\
(2,0,1)&t^2-11t+9&-15+17t\\
(2,1,0)&t^2-9t-1&-1-11t\\
(2,1,1)&t^2-\frac79t-\frac19&-\frac5{27}+\frac1{27}t.
\end{array} \tag{12.5}
$$

For example, adding $T_0$ to $A$ first composes to

$$
[t(t^2-t+1),-t^2-2t].
$$

Since

$$
f-(-t^2-2t)^2
=t(t^2-t+1)(t^2-9t-1),
$$

one reduction gives $[t^2-9t-1,1+11t]$, the seventh row. Adding both
two-torsion classes produces the quotient
$-9t^2+7t+1$; monic normalization and reduction of the second coordinate
give the eighth row. Negation supplies the last four rows from the
corresponding $a=1$ rows.

Every row satisfies $u\mid f-v^2$ and $\deg v<\deg u\le2$. Unique reduced
representation proves that the rows are the twelve distinct group elements.
Thus the table is independently checkable by polynomial identities and the
known invariant factors.

### 12.3 The terminal Abel-image sieve

For the pointed quintic, equation (2.1) says that a class lies on $j(C_7)$
exactly when its reduced $u$ has degree zero or one. Inspection of the
complete table (12.5) leaves precisely

$$
[1,0],\qquad[t,0],\qquad[t-1,0]. \tag{12.6}
$$

They are respectively the Abel classes of

$$
\infty,\qquad(0,0),\qquad(1,0). \tag{12.7}
$$

This is the terminal form of a Mordell--Weil sieve. Take a modulus divisible
by the exponent $6$ of (12.4); then $6J_7(\mathbf Q)=0$, so the quotient is
the full twelve-element group. The local or geometric admissible set is the
Abel image, and the unique Mumford degree test computes it exactly. All nine
unwanted singleton cosets are eliminated.

One may also reduce the table at good primes and intersect finite reduction
sets, but doing so would add intermediate congruences without strengthening
the conclusion. The rational normal form already tests the exact class in
the exact global group.

## 13. The mixed-seven rational points

### 13.1 Exact determination

**Theorem 13.1.** The smooth projective curve (12.1) has

$$
\boxed{C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\}.} \tag{13.1}
$$

**Proof.** The three displayed points plainly satisfy (12.1). Conversely,
let $P\in C_7(\mathbf Q)$. The exact group decomposition (12.4) places
$j(P)$ in one of the twelve rows of (12.5). Since $P$ lies on the pointed
Abel image, reduced uniqueness and (2.1) force the degree of its $u$ to be at
most one. Only the three rows (12.6) qualify. They are the classes of the
three displayed points, and injectivity of $j$ proves equality. $\square$

The proof does not assume that rational coordinates have bounded numerator
or denominator. It exhausts the ambient Mordell--Weil group, so a rational
point of arbitrarily large height would still have to occupy one of the same
twelve classes.

### 13.2 Cuspidal and degenerate meaning

We recall the exact handoff proved in Book 148, since its direction is part
of the conclusion. A point of order seven puts an elliptic curve in Tate
normal form with

$$
b=t^3-t^2,\qquad c=t^2-t. \tag{13.2a}
$$

If the curve also has full rational two-torsion, the cubic of two-torsion
$x$-coordinates splits. Its discriminant is therefore a square, and direct
substitution in that discriminant gives

$$
16t^7(t-1)^7(t^3-8t^2+5t+1). \tag{13.2b}
$$

For $t\ne0,1$, division of a square root by $4t^3(t-1)^3$ produces a
rational point on $C_7$. Hence a nondegenerate mixed-seven configuration
would produce a rational point of $C_7$ outside
$\{\infty,(0,0),(1,0)\}$. The values $t=0$ and $t=1$ make the Tate normal
form degenerate, while $\infty$ is its boundary parameter. Theorem 13.1
therefore has the required arithmetic consequence:

$$
\text{every rational mixed-seven point is cuspidal or degenerate}. \tag{13.2}
$$

This conclusion has two parts which should not be conflated. The curve
calculation proves that only the three parameter values occur. The prior
Tate-normal-form calculation identifies those values as degenerate or
boundary and proves that every forbidden configuration maps to a different
curve point. The converse is neither used nor true in general: square
discriminant does not force the two-torsion cubic to split. Thus no
nondegenerate mixed-seven configuration remains, without silently
strengthening the necessary implication to an equivalence.

### 13.3 A certificate with no hidden search

The completeness chain is especially short:

$$
\begin{array}{c}
\text{true two-descent and good reductions}\\
\Downarrow\\
J_7(\mathbf Q)=\mathbf Z/3\oplus(\mathbf Z/2)^2\\
\Downarrow\\
\text{the twelve unique reduced pairs in (12.5)}\\
\Downarrow\\
\deg u\le1\text{ in exactly three rows}\\
\Downarrow\\
C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\}.
\end{array} \tag{13.3}
$$

The descent supplies the upper bound on the group; exact pairs supply all
relations; the degree test is an if-and-only-if description of the Abel
image; and injectivity supplies uniqueness. None of these arrows uses the
conclusion of the next arrow.

## 14. The completed sieve package

### 14.1 Hypothesis ledger

The main constructions and their exact hypotheses are summarized below.

| Assertion | Hypotheses |
|---|---|
| Abel map is a closed immersion | smooth projective curve of genus at least one and a rational degree-one base class |
| specialization square (2.2) | smooth proper model at the chosen prime and compatible base section |
| finite reduction constraint | good reduction; no restriction on the modulus for necessity |
| local quotient isomorphism (5.2) | good reduction and $p\nmid N$ |
| pointed Mumford Abel-image test | monic squarefree quintic, characteristic different from two, rational branch point at infinity |
| torsion reduction injectivity | good reduction and torsion order prime to the residue characteristic |
| reduction saturation criterion | good primes away from $\ell$, full rational $\ell$-torsion contained in the subgroup |
| singleton terminal sieve | complete finite Mordell--Weil group and a modulus annihilating it |

Book 41 supplies finite generation and the height-lattice language. Book 148
derives the two marked curve models from their modular parameter problems,
identifies the six rational $X_1(13)$ cusps, and proves the one-way
mixed-seven implication used in Section 13.2. Book 136 supplies unique
pointed Mumford representatives, exact addition, finite-field enumeration,
specialization, and torsion injection under the hypotheses used here. Book
137 supplies true two-descent, local completeness, saturation criteria, and
the exact groups (10.5) and (12.4). The $X_1(13)$ special-fiber change of
variables produces the monic quintic (10.8) before any pointed Mumford result
is invoked. The mixed-seven equation already satisfies every pointed quintic
hypothesis.

No later arithmetic theorem is needed for either rational-point
determination. In particular, the conclusions are not consequences of a
future irreducibility argument; they are inputs available to it.

### 14.2 Main theorem

**Theorem 14.1 (exhaustive Mordell--Weil sieve).** Let $C/\mathbf Q$ be a
smooth projective curve of genus at least two with a rational degree-one base
class, and let $j:C\hookrightarrow J$ be the associated Abel map. Suppose:

1. a subgroup $\Gamma\subseteq J(\mathbf Q)$ is given with certified finite
   index and full torsion;
2. saturation or an explicit coset list accounts for all of
   $J(\mathbf Q)/\Gamma$;
3. at each chosen place, the complete image of the curve in the relevant
   finite quotient of the Jacobian is known;
4. every retained branch is accounted for by a known point: it is either the
   singleton Abel class of that point, meets a proved global height region
   only in that class, or is paired with a local argument proving that point
   unique in the corresponding residue family.

Then the retained known points are exactly $C(\mathbf Q)$.

**Proof.** Include every Mordell--Weil coset at the initial stage. The
commuting Abel-reduction square shows that each rational point satisfies
every local condition. Lemma 4.1 and Proposition 4.2 preserve it through
every refinement. The accounted terminal branch identifies its Abel class
with that of a known point, either directly or inside the proved global or
local terminal region. Proposition 2.1 identifies the points themselves.
$\square$

Applied to (10.1), the full group is cyclic of order $19$, reduction at
$17$ is injective, and table (10.12) leaves the six singleton classes in
(11.2). Applied to (12.1), the full group has twelve elements and table
(12.5) leaves the three singleton Abel classes in (12.6). Hence

$$
X_1(13)(\mathbf Q)=
\{\infty^+,\infty^-,(0,0),(0,-1),(-1,0),(-1,-1)\}, \tag{14.1}
$$

and

$$
C_7(\mathbf Q)=\{\infty,(0,0),(1,0)\}. \tag{14.2}
$$

### 14.3 Conclusion

The Mordell--Weil theorem turns the Jacobian's rational points into an
arithmetic lattice with finite torsion. Descent and saturation turn a list of
generators into the whole lattice. Good specialization then sends the Abel
image of every rational curve point into a finite, exhaustively enumerable
special Abel image. Pulling those sets back through finite quotients yields
coset constraints, and refinement preserves every genuine point while
discarding incompatible cosets.

The decisive issue is completeness at every interface. The Abel base point
must remain fixed; reduction must come from a smooth model; local images must
be full; a finite-index subgroup must be saturated or all its cosets must be
included; and surviving congruence classes must receive a terminal argument.
With those conditions, the sieve is a proof of exhaustion rather than a
search heuristic. It remains available at the Chabauty boundary because it
depends on finite quotients, not on the existence of an annihilating
differential.

For $X_1(13)$, one good reduction sees the rational cyclic subgroup so
sparsely that exactly the six cuspidal classes survive. For the mixed-seven
curve, unique Mumford representation tests all twelve rational Jacobian
classes and leaves only the point at infinity and the two rational branch
points. Thus the two pending genus-two calculations are complete: the first
curve has exactly its six rational cusps, and the second has only its
cuspidal or degenerate rational points.
