# Congruence Kernels and Metaplectic Duality for Quaternionic Groups

## Status and contents

This manuscript develops the rank-two congruence--metaplectic problem but does **not yet**
prove its full quaternionic theorem. It proves strong-approximation and open-level
preliminaries, an exact finite-quotient formulation of centrality and the stem property, exact
quaternionic Cayley identities, compact transgression, relative finite-to-circle coefficient
comparison, projected-diagonal finite-product cross-term vanishing (including between two
division factors), normalized restricted-product gluing and its compact-splitting converse,
and the terminal scalar duality calculation. The necessary interfaces for the conditional
rank-two package---centrality, the compact-to-adelic pairing, local classification,
compact-tail product coherence, scalar injectivity, and torsion---remain open in the declared
sources. Quaternionic relative normal generation and power--abelian continuity are retained
only as proposed sufficient routes to centrality and the stem property, respectively; no
necessity or logical independence claim is made for those routes.

The purpose of the present version is to advance each layer by exact arguments without
promoting a local or approximate calculation past what it proves. Missing statements remain
visible at the point where they are first needed, and the final export to Book 139 remains
conditional on precisely those statements.

1. [The arithmetic group and its two completions](#1-the-arithmetic-group-and-its-two-completions)
2. [What strong approximation actually proves](#2-what-strong-approximation-actually-proves)
   - [Density at a compact-open level](#21-density-at-a-compact-open-level)
   - [Invariance under open spectator level](#22-invariance-under-open-spectator-level)
   - [The exact finite-quotient centrality criterion](#23-the-exact-finite-quotient-centrality-criterion)
   - [Power criteria and the split model](#24-power-criteria-and-the-split-model)
   - [The exact stem and abelian-continuity criteria](#25-the-exact-stem-and-abelian-continuity-criteria)
   - [Quaternionic Cayley words](#26-quaternionic-cayley-words)
3. [The unconditional compact transgression calculation](#3-the-unconditional-compact-transgression-calculation)
   - [The exact quotient](#31-the-exact-quotient)
   - [Why circle coefficients are a separate theory](#32-why-circle-coefficients-are-a-separate-theory)
   - [Relative cohomology with a chosen dense splitting](#33-relative-cohomology-with-a-chosen-dense-splitting)
   - [The relative finite-to-circle isomorphism](#34-the-relative-finite-to-circle-isomorphism)
4. [The unconditional scalar endpoint](#4-the-unconditional-scalar-endpoint)
5. [The missing congruence--metaplectic hypotheses](#5-the-missing-congruence--metaplectic-hypotheses)
   - [Centrality and perfect duality](#51-centrality-and-perfect-duality)
   - [Local classification](#52-local-classification)
   - [Products, cross terms, and restricted products](#53-products-cross-terms-and-restricted-products)
   - [Adelic-to-scalar reduction](#54-adelic-to-scalar-reduction)
   - [Required interfaces and proposed sufficient routes](#55-required-interfaces-and-proposed-sufficient-routes)
6. [Conditional arithmetic consequences](#6-conditional-arithmetic-consequences)
   - [Odd-primary character vanishing](#61-odd-primary-character-vanishing)
   - [The all-primary size bound](#62-the-all-primary-size-bound)
7. [The exact export to Ihara theory](#7-the-exact-export-to-ihara-theory)
8. [Audit of the rejected proof routes](#8-audit-of-the-rejected-proof-routes)
   - [Stabilization is not vanishing](#81-stabilization-is-not-vanishing)
   - [Approximation does not preserve exact identities](#82-approximation-does-not-preserve-exact-identities)
   - [Finite and Moore coefficients cannot be normalized circularly](#83-finite-and-moore-coefficients-cannot-be-normalized-circularly)
   - [The local multiplier theorems are absent](#84-the-local-multiplier-theorems-are-absent)
   - [Projected diagonals do not control adelic tails](#85-projected-diagonals-do-not-control-adelic-tails)
   - [Restricted-product normalization and scalar injectivity are extra theorems](#86-restricted-product-normalization-and-scalar-injectivity-are-extra-theorems)
9. [Source ledger and conclusion](#9-source-ledger-and-conclusion)

## 1. The arithmetic group and its two completions

Let $F$ be a number field and let $B/F$ be a quaternion algebra. Put

$$
H=\operatorname{SL}_1(B).
$$

Assume that $B$ is split at a real place $\tau$ and at a finite place $v$. Set

$$
S=V_\infty(F)\cup\{v\},
\qquad
G^S=H(\mathbf A_F^S)
=\prod_{w\notin S}'H(F_w).
\tag{1.1}
$$

At every finite $w\notin S$, choose a maximal order $\mathcal O_{B,w}$ and write

$$
K_w^0=\mathcal O_{B,w}^{1}.
\tag{1.2}
$$

Book 82 supplies the order-theoretic meaning of (1.2), including the maximal-order and
Jacobson-radical filtrations. It does not compute central extensions of $H(F_w)$.

Let $K\subset G^S$ be compact open and define

$$
\Gamma(K)=H(F)\cap K.
\tag{1.3}
$$

The group in (1.3) is regarded as an abstract discrete group before completion. Its **full
profinite completion** is

$$
\widehat{\Gamma(K)}
=\varprojlim_{N\triangleleft_f\Gamma(K)}\Gamma(K)/N,
\tag{1.4}
$$

where every finite-index normal subgroup occurs. This is not a pro-$\ell$ completion and not
the completion defined only by congruence subgroups.

Once $\Gamma(K)$ is known to be dense in $K$, the inclusion extends to a continuous
surjection

$$
\rho_K:\widehat{\Gamma(K)}\twoheadrightarrow K.
\tag{1.5}
$$

The **full congruence kernel** at level $K$ is

$$
C(K)=\ker(\rho_K).
\tag{1.6}
$$

Thus the basic extension is

$$
1\longrightarrow C(K)
\longrightarrow\widehat{\Gamma(K)}
\xrightarrow{\rho_K}K
\longrightarrow1.
\tag{1.7}
$$

No centrality, finiteness, or abelianity of $C(K)$ is implicit in this definition.

## 2. What strong approximation actually proves

Book 118 proves strong approximation for the simply connected quaternionic norm-one group
when it has a noncompact archimedean factor. Since $B$ is split at $\tau$, its theorem gives
density of $H(F)$ in the finite adelic group $H(\mathbf A_{F,f})$. Projection away from $v$
therefore gives density in $G^S$.

### 2.1 Density at a compact-open level

**Lemma 2.1.** For every compact open $K\subset G^S$, the group $\Gamma(K)$ is dense in $K$.
Consequently (1.5) is surjective.

**Proof.** Let $xU\subset K$ be an open coset, with $U$ open in $G^S$. Density of $H(F)$ in
$G^S$ gives $h\in H(F)\cap xU$. Since $xU\subset K$, this element belongs to
$H(F)\cap K=\Gamma(K)$. Hence every nonempty open subset of $K$ meets $\Gamma(K)$.

The image of the induced map from the full profinite completion is compact and therefore
closed in the Hausdorff group $K$. It contains the dense image of $\Gamma(K)$, so it is all of
$K$. $\square$

Book 118 proves more than ordinary weak approximation: its norm-quadric argument retains
integrality outside a prescribed finite set. It still gives an approximation theorem. It does
not say that chosen rational approximants satisfy exact root-word identities in $H(F)$, nor
that a principal congruence subgroup is generated by a bounded collection of such exact
words.

### 2.2 Invariance under open spectator level

The following result is Lemma 5.5 of Book 139. We include the proof because it is the only
level-transport statement used below.

**Lemma 2.2 (open-level invariance).** Let $K'\subset K$ be open compact subgroups of $G^S$.
Inclusion induces an embedding

$$
\widehat{\Gamma(K')}\hookrightarrow\widehat{\Gamma(K)}
$$

whose image is $\rho_K^{-1}(K')$. Under this embedding,

$$
C(K')=C(K).
\tag{2.1}
$$

**Proof.** Density identifies the finite coset sets

$$
\Gamma(K)/\Gamma(K')\simeq K/K'.
$$

Thus $\Gamma(K')$ has finite index in $\Gamma(K)$. The full profinite topology of a
finite-index subgroup is the topology induced from the ambient group. Indeed, if
$N'\triangleleft_f\Gamma(K')$, the intersection of its finitely many $\Gamma(K)$-conjugates
contains a subgroup normal and of finite index in $\Gamma(K)$; the converse containment of
topologies is immediate by intersection with finite-index subgroups of $\Gamma(K)$.

It follows that $\widehat{\Gamma(K')}$ is the closure of $\Gamma(K')$ in
$\widehat{\Gamma(K)}$. The subgroup $\rho_K^{-1}(K')$ is open, and its intersection with the
dense subgroup $\Gamma(K)$ is exactly $\Gamma(K')$. Hence that closure is
$\rho_K^{-1}(K')$. Restricting $\rho_K$ shows that its kernel is the full kernel of $\rho_K$,
which proves (2.1). $\square$

For finitely many levels, their common intersection therefore identifies the underlying
kernels. This does not identify the quotient actions or transgression maps. It also does not
transport centrality from the smaller completion to a larger completion. For example, in

$$
(\mathbf Z/3\mathbf Z)\rtimes(\mathbf Z/2\mathbf Z)
$$

with inversion action, the kernel $\mathbf Z/3\mathbf Z$ is central in the inverse image of
the trivial subgroup of the quotient but is not central in the whole semidirect product.

### 2.3 The exact finite-quotient centrality criterion

The failed contraction argument can be removed completely. Centrality has an exact
finite-quotient formulation which uses no local limits.

Let

$$
1\longrightarrow C\longrightarrow E
\xrightarrow{\rho}K\longrightarrow1
\tag{2.2}
$$

denote (1.7), with $E=\widehat\Gamma$. Let $q:E\twoheadrightarrow Q$ be a finite continuous
quotient, put $N=\ker(q|_\Gamma)$, and set

$$
D_q=q(C)\triangleleft Q.
\tag{2.3}
$$

Since $q$ modulo $D_q$ kills $C$, it factors uniquely through a continuous map

$$
\bar q:K\longrightarrow Q/D_q.
\tag{2.4}
$$

Write $L_q=\ker\bar q$.

**Lemma 2.3 (closure and residual image).** The closure of $N$ in $K$ is $L_q$, and

$$
q^{-1}(D_q)\cap\Gamma
=\Gamma\cap L_q.
\tag{2.5}
$$

If $V\triangleleft K$ is any open subgroup contained in $L_q$, then

$$
q(\Gamma\cap V)=D_q.
\tag{2.6}
$$

**Proof.** The inclusion $\overline N\subseteq L_q$ is immediate. For the reverse inclusion,
fix $x\in L_q$ and an open neighborhood $U$ of $x$ in $K$. Shrink $U$ inside the fiber
$\bar q^{-1}(1)$. Density supplies $\gamma\in\Gamma$ with $\rho(\gamma)\in U$, and then
$q(\gamma)=d\in D_q$.

Choose $c\in C$ with $q(c)=d$. For every identity neighborhood $W\subset K$, the set

$$
q^{-1}(d)\cap\rho^{-1}(W)
$$

is an open neighborhood of $c$ in $E$. Density of $\Gamma$ in its full profinite completion
therefore supplies $\delta\in\Gamma$ with $q(\delta)=d$ and $\rho(\delta)\in W$. Taking $W$
small enough gives

$$
n=\delta^{-1}\gamma\in N,
\qquad
\rho(n)\in U.
$$

Thus $N$ is dense in $L_q$. Equation (2.5) follows directly from (2.4).

For (2.6), let $d\in D_q$ and choose $c\in C$ above it. The open set
$q^{-1}(d)\cap\rho^{-1}(V)$ contains $c$, so it meets $\Gamma$. Any point in that intersection
lies in $\Gamma\cap V$ and maps to $d$. The reverse inclusion follows from $V\subset L_q$.
$\square$

The subgroup $D_q$ is exactly the part of the finite quotient invisible to the congruence
topology. It is not obtained by stabilizing a descending list of subgroup images.

**Theorem 2.4 (centrality criterion).** The following conditions are equivalent.

1. $C\subset Z(E)$.
2. For every finite quotient $q:E\twoheadrightarrow Q$, one has $D_q\subset Z(Q)$.
3. For every $N\triangleleft_f\Gamma$, if $q:\Gamma\to\Gamma/N$ is the quotient and the same
   letter denotes its unique continuous extension $E\twoheadrightarrow\Gamma/N$, there is an
   open normal $V\subset K$, with $V\subset L_q$, such that
   $$
   [\Gamma,\Gamma\cap V]\subset N.
   \tag{2.7}
   $$

For an integral reference level, $V$ may be replaced by a sufficiently deep principal
congruence subgroup contained in it.

**Proof.** A closed subgroup of a profinite group is central exactly when its image is central
in every finite quotient; finite quotients separate a nontrivial commutator. This proves the
equivalence of 1 and 2.

Given $q$, choose any open normal $V\subset L_q$. Lemma 2.3 gives
$q(\Gamma\cap V)=D_q$, while $q(\Gamma)=Q$. Hence $D_q$ is central in $Q$ exactly when
$q([\Gamma,\Gamma\cap V])=1$, which is (2.7). Compact-open principal congruence subgroups form
a neighborhood basis at an integral level, proving the last sentence. $\square$

This theorem is a replacement for the false stabilization step, but not yet a proof that its
three equivalent conditions hold for the quaternionic group. A proof must establish (2.7) by
exact group identities for every abstract finite quotient. Approximation alone cannot do so.

### 2.4 Power criteria and the split model

For $m\geq1$ define the characteristic subgroup

$$
P_m=\langle g^m:g\in\Gamma\rangle\triangleleft\Gamma.
\tag{2.7a}
$$

The following packages the exact information required from a power calculation.

**Proposition 2.4A (power--commutator criterion).** Suppose that for every $m\geq1$ there is
an open normal subgroup $U_m\triangleleft K$ such that

$$
[\Gamma,\Gamma\cap U_m]\subseteq[P_m,\Gamma].
\tag{2.7b}
$$

Then $C$ is central in $E=\widehat\Gamma$.

**Proof.** Let $q:E\twoheadrightarrow Q$ be a finite quotient, put
$N=\ker(q|_\Gamma)$, and let $m$ be the exponent of $Q$. Then $P_m\subseteq N$, and normality
of $N$ gives $[P_m,\Gamma]\subseteq N$. Choose an open normal subgroup $V\triangleleft K$
contained in $L_q$, as in Theorem 2.4, and replace it by $V\cap U_m$. Now

$$
[\Gamma,\Gamma\cap(V\cap U_m)]
\subseteq[\Gamma,\Gamma\cap U_m]
\subseteq[P_m,\Gamma]
\subseteq N.
$$

Condition 3 of Theorem 2.4 holds for $q$. Since $q$ was arbitrary, that theorem gives
$C\subseteq Z(E)$. $\square$

The split rank-one model shows exactly where a relative Mennicke theorem would enter. Put

$$
R=\mathcal O_F[v^{-1}],
\qquad
\Gamma_R=\operatorname{SL}_2(R).
$$

In this paragraph $P_m$ is formed inside $\Gamma_R$ as in (2.7a). The $S$-unit theorem
supplies an infinite-order unit $\epsilon\in R^\times$. With

$$
x(r)=\begin{pmatrix}1&r\\0&1\end{pmatrix},
\quad
y(r)=\begin{pmatrix}1&0\\r&1\end{pmatrix},
\quad
h(a)=\begin{pmatrix}a&0\\0&a^{-1}\end{pmatrix},
$$

direct multiplication gives, for every $r\in R$,

$$
\begin{aligned}
[h(\epsilon)^m,x(r)]&=x((\epsilon^{2m}-1)r),\\
[h(\epsilon)^m,y(r)]&=y((\epsilon^{-2m}-1)r).
\end{aligned}
\tag{2.7c}
$$

Set

$$
\mathfrak a_m=(\epsilon^{2m}-1)R
=(\epsilon^{-2m}-1)R,
\tag{2.7d}
$$

and let $E_2(R,\mathfrak a_m)$ be the normal subgroup of $\Gamma_R$ generated by
$x(\mathfrak a_m)$ and $y(\mathfrak a_m)$. Since $h(\epsilon)^m\in P_m$, (2.7c) and
normality show that

$$
E_2(R,\mathfrak a_m)\subseteq[P_m,\Gamma_R].
\tag{2.7e}
$$

This is the complete root calculation; it is not yet (2.7b). For a nonzero ideal
$\mathfrak b\subset R$, write

$$
\Gamma_R(\mathfrak b)
=\ker[\operatorname{SL}_2(R)\to\operatorname{SL}_2(R/\mathfrak b)].
$$

The exact missing relative Mennicke input is

$$
({\rm RM}_m):\qquad
\text{there is a nonzero }\mathfrak b_m\text{ such that }
[\operatorname{SL}_2(R),\Gamma_R(\mathfrak b_m)]
\subseteq E_2(R,\mathfrak a_m).
\tag{2.7f}
$$

If $({\rm RM}_m)$ holds for every $m$, take $U_m$ to be the corresponding principal open
subgroup in the congruence completion. Equations (2.7e)--(2.7f) give (2.7b), and Proposition
2.4A proves centrality. Thus the infinite $S$-unit calculation isolates, but does not prove,
the relative Mennicke inclusion.

### 2.5 The exact stem and abelian-continuity criteria

Centrality and the stem property are distinct conditions in the argument. No implication or
logical-independence assertion between them is used here. The latter has an exact formulation.

**Theorem 2.5 (stem criterion).** The following conditions are equivalent.

1. $C\subset\overline{[E,E]}$.
2. Every continuous homomorphism from $E$ to a finite abelian group kills $C$.
3. Every homomorphism from the abstract group $\Gamma$ to a finite abelian group is continuous
   for the topology induced by $\Gamma\subset K$ and extends uniquely to $K$.
4. For every homomorphism $f:\Gamma\to A$ to a finite abelian group, there is an open normal
   $V\subset K$ such that $f(\Gamma\cap V)=0$.

**Proof.** The intersection of the kernels of all continuous finite abelian quotients of the
profinite group $E$ is its closed commutator subgroup. This proves the equivalence of 1 and 2.
Every homomorphism from $\Gamma$ to a finite group extends uniquely to the full profinite
completion $E$. It factors through $K=E/C$ exactly when its extension kills $C$, proving the
equivalence with 3. A map to a finite discrete group is continuous for the topology induced
from $K$ exactly when its kernel contains $\Gamma\cap V$ for some open normal $V\subset K$.
Density then gives a unique continuous extension to $K$, proving the equivalence with 4.
$\square$

Thus the stem property is itself the full finite-abelian congruence theorem. It cannot be
deduced by silently killing the denominator in the compact transgression quotient.

There is a parallel power condition, separate from Proposition 2.4A. For a fixed $m$, write

$$
({\rm PA}_m):\qquad
\text{there is an open normal }U_m\triangleleft K\text{ such that }
\Gamma\cap U_m\subseteq P_m[\Gamma,\Gamma].
\tag{2.7g}
$$

If $f:\Gamma\to A$ is a homomorphism to a finite abelian group of exponent dividing $m$,
then $f$ kills $P_m[\Gamma,\Gamma]$. Hence $({\rm PA}_m)$ makes $f$ continuous for the
topology induced from $K$. If $({\rm PA}_m)$ holds for every $m$, Theorem 2.5 proves the stem
property. If it is known only for odd $m$, it proves only the corresponding continuity theorem
for finite abelian groups of odd exponent. Proposition 2.4A proves centrality only; the
argument given there supplies none of these abelian-continuity conclusions.

### 2.6 Quaternionic Cayley words

There is nevertheless useful exact quaternionic algebra behind the desired centrality
theorem. It explains both the attraction and the limitation of contraction arguments.

Choose a quadratic field $L/F$ which embeds in $B$ and splits at $\tau$ and $v$. Such an $L$
exists: prescribe a square local class at the two split places, a nonsquare class at every
ramified place of $B$, and one further nonsquare class to ensure that the global quadratic
algebra is a field. Weak approximation realizes these finitely many square classes, and the
quaternionic embedding criterion of Book 77 then embeds $L$ in $B$.

Write

$$
B=L\oplus Lj,
\qquad
j^2=\delta\in F^\times,
\qquad
ja=\bar a j
\quad(a\in L),
\tag{2.8}
$$

where the bar on $L$ is its nontrivial $F$-automorphism. For $b\in L$ put $x_b=bj$. Then
$\overline{x_b}=-x_b$ and $x_b^2=\delta N_{L/F}(b)$. Whenever $1-x_b$ is invertible, define

$$
u(b)=(1+x_b)(1-x_b)^{-1}.
\tag{2.9}
$$

**Lemma 2.6 (exact Cayley conjugation).** One has $u(b)\in H(F)$. If
$t\in L^\times$ satisfies $N_{L/F}(t)=1$, then

$$
t\,u(b)\,t^{-1}=u(t^2b).
\tag{2.10}
$$

Consequently, with the convention $[g,h]=ghg^{-1}h^{-1}$,

$$
[t^m,u(b)]=u(t^{2m}b)u(b)^{-1}.
\tag{2.11}
$$

**Proof.** Since $\overline{1+x_b}=1-x_b$ and $x_b^2\in F$, numerator and denominator in
(2.9) have the same reduced norm $1-x_b^2$. Hence $u(b)$ has reduced norm one. The relation
$N(t)=1$ gives $\bar t=t^{-1}$, and (2.8) gives

$$
t x_b t^{-1}
=tbj t^{-1}
=tb\,\overline{t^{-1}}j
=t^2bj.
$$

Conjugating (2.9) proves (2.10), and (2.11) follows. $\square$

The failure of additivity is itself controlled by an exact identity. Fix $b\in L$, put
$d=x_b^2=\delta N_{L/F}(b)$, and let $r,s\in F$ be such that the displayed Cayley transforms
and $1+rsd$ are defined. Since $rx_b$ and $sx_b$ commute, direct multiplication gives

$$
u(rb)u(sb)
=u\!\left(\frac{r+s}{1+rsd}\,b\right),
\qquad
u(rb)^{-1}=u(-rb).
\tag{2.11a}
$$

Thus every fixed Cayley line has an exact rational group law. It is a one-dimensional torus
law, not the additive root law needed to turn a parameter-ideal containment into group
generation.

After enlarging a finite bad set, (2.9) is integral whenever $b$ is sufficiently deep in the
localized $L$-order: explicitly,

$$
(1-x_b)^{-1}=\frac{1+x_b}{1-\delta N_{L/F}(b)},
\tag{2.12}
$$

and the central denominator is then a unit. Thus these are exact principal-congruence words,
not approximate rational roots.

If $q:\Gamma\to Q$ is finite and $m$ is the exponent of $Q$, then every instance of (2.11)
for which $t,u(b)\in\Gamma$ satisfies

$$
[t^m,u(b)]\in\ker q.
\tag{2.13}
$$

This is genuine information. It still does not prove (2.7). Unlike a split root map,
$b\mapsto u(b)$ is not additive, so (2.11) does not say that all Cayley elements with parameter
in $(t^{2m}-1)\mathfrak a$ lie in $\ker q$.

The exact missing subgroup can nevertheless be named. Allow all embedded quadratic fields
$L\subset B$ and all pairs $(t,b)$ for which $t\in L^1$, $u_L(b)$ is defined, and
$t,u_L(b)\in\Gamma$. Define the **Cayley-word subgroup**

$$
E_m=\left\langle\!\left\langle
[t^m,u_L(b)]:L,t,b\text{ as above}
\right\rangle\!\right\rangle_\Gamma.
\tag{2.14}
$$

Because $t^m\in P_m$ and $[P_m,\Gamma]$ is normal in $\Gamma$, one has the exact containment

$$
E_m\subseteq[P_m,\Gamma].
\tag{2.15}
$$

For an integral reference level and a nonzero ideal $\mathfrak c$, put
$\Gamma(\mathfrak c)=\Gamma\cap K(\mathfrak c)$. The following quaternionic relative
Mennicke statement is a proposed route tailored to the power criterion:

$$
({\rm QRM}_m):\qquad
\text{there is a nonzero ideal }\mathfrak c_m\text{ such that }
[\Gamma,\Gamma(\mathfrak c_m)]\subseteq E_m.
\tag{2.16}
$$

If $({\rm QRM}_m)$ holds for every $m$, then (2.15)--(2.16), with
$U_m=K(\mathfrak c_m)$, satisfy Proposition 2.4A and prove centrality. No earlier book proves
$({\rm QRM}_m)$. The Cayley identities prove only (2.15); approximation cannot supply the
normal-generation inclusion (2.16). Separately, the proposed conditions $({\rm PA}_m)$ would
suffice for the stem or odd-primary abelian-continuity conclusions. Neither family is claimed
to be necessary, and no logical independence between the two families is asserted.

## 3. The unconditional compact transgression calculation

Fix one level and abbreviate

$$
\Gamma=\Gamma(K),\qquad
\widehat\Gamma=\widehat{\Gamma(K)},\qquad
C=C(K).
$$

Let $A$ be a finite abelian group with the discrete topology and trivial action. Define the
compact finite-coefficient multiplier kernel

$$
\mathfrak M_A(K,\Gamma)
=\ker\!\left[
H^2_{\mathrm{cont}}(K,A)
\longrightarrow H^2(\Gamma,A)
\right].
\tag{3.1}
$$

The target is abstract group cohomology. The map pulls a continuous extension of $K$ back
along the dense abstract homomorphism $\Gamma\to K$.

### 3.1 The exact quotient

**Proposition 3.1 (compact transgression).** Transgression for (1.7) induces a canonical
isomorphism

$$
\frac{
\operatorname{Hom}_{\mathrm{cont}}(C,A)^K
}{
\operatorname{res}_C
\operatorname{Hom}_{\mathrm{cont}}(\widehat\Gamma,A)
}
\xrightarrow{\ \sim\ }
\mathfrak M_A(K,\Gamma).
\tag{3.2}
$$

If $C$ is central, the superscript $K$ may be omitted. In that case transgression is an
isomorphism from the entire group $\operatorname{Hom}_{\mathrm{cont}}(C,A)$ for every finite
$A$ if and only if

$$
C\subseteq
\overline{[\widehat\Gamma,\widehat\Gamma]}.
\tag{3.3}
$$

**Proof.** First consider the restriction map

$$
H^2_{\mathrm{cont}}(\widehat\Gamma,A)
\longrightarrow H^2(\Gamma,A).
\tag{3.4}
$$

It is injective. Indeed, a continuous cocycle on $\widehat\Gamma$ defines a profinite
extension by $A$. If its pullback to $\Gamma$ splits abstractly, the splitting is a
homomorphism from $\Gamma$ to a profinite group. Such a homomorphism is continuous for the
full profinite topology, because inverse images of open normal subgroups have finite index.
It therefore extends uniquely to $\widehat\Gamma$. The extended map is a section, since the
section identity holds on the dense subgroup $\Gamma$. Thus the original class is zero.

The five-term sequence for (1.7) contains

$$
\operatorname{Hom}_{\mathrm{cont}}(\widehat\Gamma,A)
\longrightarrow
\operatorname{Hom}_{\mathrm{cont}}(C,A)^K
\xrightarrow{\operatorname{tg}}
H^2_{\mathrm{cont}}(K,A)
\xrightarrow{\operatorname{inf}}
H^2_{\mathrm{cont}}(\widehat\Gamma,A).
\tag{3.5}
$$

By injectivity of (3.4), the kernel of inflation in (3.5) consists exactly of the classes
whose restriction to $\Gamma$ is zero. This is (3.1), and exactness gives (3.2).

If $C$ is central, its $K$-action is trivial. The denominator of (3.2) vanishes for every
finite $A$ exactly when every continuous finite abelian character of $\widehat\Gamma$ kills
$C$. Finite characters separate the profinite abelianization
$\widehat\Gamma/\overline{[\widehat\Gamma,\widehat\Gamma]}$, so this is equivalent to (3.3).
$\square$

Centrality is therefore insufficient for a perfect compact transgression pairing: the stem
condition (3.3) is an additional theorem.

### 3.2 Why circle coefficients are a separate theory

Put

$$
\mathbf D=\mathbf Q/\mathbf Z
$$

with the discrete topology and

$$
\mathbf T=\mathbf R/\mathbf Z
$$

with its usual compact topology. For a profinite group $P$, every continuous homomorphic image
of $P$ in $\mathbf T$ is a compact totally disconnected closed subgroup of the circle, hence
finite. Consequently

$$
\operatorname{Hom}_{\mathrm{cont}}(P,\mathbf T)
=\operatorname{Hom}_{\mathrm{cont}}(P,\mathbf D).
\tag{3.6}
$$

Equation (3.6) compares character groups, not degree-two cohomology. Already for the finite
cyclic group $C_p$,

$$
H^2(C_p,\mathbf Z/p\mathbf Z)\simeq\mathbf Z/p\mathbf Z,
\qquad
H^2(C_p,\mathbf T)=0,
\tag{3.7}
$$

because $H^2(C_p,M)=M/pM$ for trivial coefficients and multiplication by $p$ is surjective on
$\mathbf T$.

In particular, an abstract splitting over the dense group $\Gamma$ cannot be used to
normalize a Borel section on $K$ unless continuity of the resulting splitting has first been
proved. Proving that continuity by assuming that all finite characters of $\Gamma$ are
congruence-continuous would assume the desired congruence conclusion. Proposition 3.1 is the
valid finite-coefficient statement; it does not produce the adelic circle-valued comparison.

### 3.3 Relative cohomology with a chosen dense splitting

We first fix the complete measurable conventions used from here through Section 5. All
locally compact groups in those arguments are Hausdorff and second-countable. A **locally
compact central extension**

$$
1\longrightarrow M\longrightarrow E\xrightarrow{p}L\longrightarrow1
\tag{3.7a}
$$

means that $E$ is also locally compact and second-countable, $M\to E$ is a homeomorphism onto
a closed central subgroup, and $p$ is a continuous open quotient map inducing $E/M\simeq L$.
A Borel section is an everywhere-defined Borel map $s:L\to E$ with $p\circ s=\operatorname{id}$.

For a Polish abelian group $M$ with trivial $L$-action, let
$C^r_{\mathrm B}(L,M)$ be the abelian group of everywhere-defined normalized Borel maps
$L^r\to M$ (a positive-degree cochain is zero whenever one argument is the identity).
In the degrees used here the inhomogeneous differential is

$$
\begin{aligned}
(db)(g,h)&=b(g)+b(h)-b(gh),\\
(dc)(g,h,k)&=c(h,k)-c(gh,k)+c(g,hk)-c(g,h).
\end{aligned}
\tag{3.7b}
$$

We define $H^r_{\mathrm B}(L,M)$ to be the cohomology of this pointwise Borel complex. A
Borel $2$-cocycle $c$ defines the standard Borel group $M\times_cL$ by

$$
(m,g)(m',h)=(m+m'+c(g,h),gh).
\tag{3.7c}
$$

Conversely a Borel section of (3.7a) gives such a cocycle, and changing the section changes it
by a Borel coboundary. Write $H^2_{\mathrm B,\mathrm{lc}}(L,M)$ for the subgroup of classes
for which there are an actual extension (3.7a) and a Borel section whose cocycle represents
the class. Baer sum is obtained from the fiber product of two such extensions by quotienting
the closed antidiagonal copy of $M$, and inversion reverses the kernel identification; these
constructions remain locally compact and second-countable and combine the Borel sections.
Thus these classes form a subgroup. This is the exact degree-two extension model used below.
In this manuscript the notation $H^2_{\mathrm m}$ in (5.1) refers to
$H^2_{\mathrm B,\mathrm{lc}}$; no comparison with an almost-everywhere model of measurable
cohomology is invoked.

The automatic-continuity fact used below is internal to the argument.

**Lemma 3.1A (Baire--Pettis automatic continuity).** A Borel homomorphism
$f:G\to H$ between locally compact second-countable groups is continuous.

**Proof.** We first prove the needed Pettis assertion. If a Borel set $A\subset G$ is
nonmeagre, then it has the Baire property, so there is a nonempty open set $O$ on which $A$
is comeagre. Choose $x\in O$ and an identity neighborhood $N$ such that $Nx\subset O$.
For $g\in N$, the open set $O\cap gO$ is nonempty, while $A$ and $gA$ are comeagre in $O$
and $gO$, respectively. Hence $A\cap gA\ne\varnothing$. Writing a point of the intersection
as $a=gb$ with $a,b\in A$ gives $g=ab^{-1}$. Thus

$$
N\subset AA^{-1}.
\tag{3.7d}
$$

Now let $V$ be an identity neighborhood in $H$, and choose a symmetric identity neighborhood
$W$ with $W^2\subset V$. Second countability makes the subspace $f(G)$ Lindelöf, so countably
many translates $f(g_j)W$ cover it. Therefore

$$
G=\bigcup_j g_j f^{-1}(W).
$$

The locally compact group $G$ is a Baire space, so the Borel set $A=f^{-1}(W)$ is nonmeagre.
By (3.7d), $AA^{-1}$ contains an identity neighborhood $N$, and
$f(N)\subset WW^{-1}=W^2\subset V$. Hence $f$ is continuous at the identity and therefore
everywhere. $\square$

**Lemma 3.1B (open mapping).** A continuous surjective homomorphism
$q:G\to H$ between locally compact second-countable groups is open.

**Proof.** Let $U$ be an identity neighborhood in $G$. Choose an identity neighborhood $V$
with compact closure and $\overline V^{-1}\overline V\subset U$. Second countability supplies
countably many translates $g_jV$ covering $G$. Hence the compact sets
$q(g_j\overline V)$ cover the Baire space $H$, so one has nonempty interior. It follows that
$q(\overline V)$ has nonempty interior and

$$
q(\overline V)^{-1}q(\overline V)
\subset q(U)
$$

is an identity neighborhood. Thus $q(U)$ contains an open identity neighborhood. For an
arbitrary open $O\subset G$ and $q(g)\in q(O)$, apply this conclusion to the identity
neighborhood $g^{-1}O$; a translate of the resulting open neighborhood lies in $q(O)$.
Therefore $q(O)$ is open. $\square$

The coefficient comparison becomes exact only after the splitting is retained as part of the
object. Let $L$ be a locally compact second-countable group, let $\Delta$ be an abstract group
given the discrete topology, and let $i:\Delta\to L$ be a homomorphism. For a Polish trivial
$L$-module $M$, let $C^r(\Delta,M)$ denote the normalized ordinary cochains and put

$$
C^r_{\mathrm{rel}}(L,\Delta;M)
=C^r_{\mathrm B}(L,M)\oplus C^{r-1}(\Delta,M),
\tag{3.8}
$$

with

$$
d(c,b)=(dc,i^*c-db).
\tag{3.9}
$$

The convention $C^{-1}=0$ is understood. Its cohomology is denoted
$H^r_{\mathrm{rel}}(L,\Delta;M)$. The Borel first summand records that the representatives are
actual pointwise Borel cochains, rather than cochains normalized by an unproved continuous
dense splitting.

**Lemma 3.2 (meaning in degree two).** A class in
$H^2_{\mathrm{rel}}(L,\Delta;M)$ is a central Borel extension cocycle of $L$ by $M$, together
with a specified abstract splitting over $\Delta$, modulo Borel cochain equivalence preserving
that splitting. If the cocycle comes from a locally compact extension (3.7a), this
construction remembers that extension and the chosen splitting; the lemma does not
manufacture a locally compact topology from an arbitrary Borel cocycle.

**Proof.** A relative $2$-cocycle is a pair $(c,b)$ with

$$
dc=0,
\qquad
i^*c=db.
\tag{3.10}
$$

The first equality makes $M\times_cL$ a central group whose multiplication and inverse are
Borel maps for the product Borel structure. With additive notation on $M$, the map

$$
\Delta\longrightarrow M\times_cL,
\qquad
\gamma\longmapsto(-b(\gamma),i(\gamma))
\tag{3.11}
$$

is a homomorphism precisely because of the second equality. If $a:L\to M$ is a Borel
$1$-cochain, adding the relative coboundary $d(a,z)$ replaces $c$ by $c+da$ and $b$ by
$b+i^*a$; the constant $z\in M$ has zero ordinary differential because the action is trivial.
The map $(m,g)\mapsto(m-a(g),g)$ is the corresponding Borel extension equivalence and carries
the splitting defined by $b$ to the one defined by $b+i^*a$. Conversely, every equivalence
over $M$ and $L$ has this form. Thus the constructions are inverse. If both Borel groups have
locally compact extension topologies as in (3.7a), this Borel equivalence is a Borel
homomorphism between locally compact second-countable groups and is continuous by Lemma 3.1A.
No locally compact topology, however, is inferred merely from the Borel group (3.7c).
$\square$

The ordinary kernel which forgets a chosen splitting is not the same object. Indeed, projection
onto the first summand in (3.8) gives the short exact sequence of complexes

$$
0\longrightarrow C^{\bullet-1}(\Delta,M)
\longrightarrow C^\bullet_{\mathrm{rel}}(L,\Delta;M)
\longrightarrow C^\bullet_{\mathrm B}(L,M)\longrightarrow0,
\tag{3.11a}
$$

where the shifted complex has differential $-d$ and the connecting map is restriction along
$i$. Its long exact cohomology sequence gives

$$
H^1_{\mathrm B}(L,M)
\longrightarrow H^1(\Delta,M)
\longrightarrow H^2_{\mathrm{rel}}(L,\Delta;M)
\longrightarrow H^2_{\mathrm B}(L,M)
\longrightarrow H^2(\Delta,M).
\tag{3.12}
$$

Thus the fiber over an extension class which merely *admits* a splitting is a quotient of the
possible abstract splittings by Borel characters of $L$; for the finite and circle targets
used below, Lemma 3.1A makes those characters continuous. Discarding this fiber is exactly
what made the earlier normalization circular.

**Lemma 3.2A (relative degree one).** If $i(\Delta)$ is dense in $L$, then

$$
H^1_{\mathrm{rel}}(L,\Delta;\mathbf T)=0.
\tag{3.12a}
$$

**Proof.** A relative $1$-cocycle is a pair $(a,z)$ in which
$a:L\to\mathbf T$ is a Borel homomorphism and $a\circ i=0$; the constant $0$-cochain
$z\in\mathbf T$ is immaterial modulo relative $0$-coboundaries. Lemma 3.1A makes $a$
continuous. Since it vanishes on the dense subgroup $i(\Delta)$, it is zero. The remaining
constant $z$ is the relative coboundary of the same constant $0$-cochain on $L$. $\square$

Retaining the splitting also sharpens compact transgression. Suppose now that $K$ is
profinite, $\Gamma\subset K$ is dense, $\widehat\Gamma\twoheadrightarrow K$ is its full
profinite extension with kernel $C$, and $A$ is finite. Let
$H^2_{\mathrm{rel},\mathrm{lc}}(K,\Gamma;A)$ denote relative classes represented by actual
locally compact extensions, with the chosen abstract splitting over $\Gamma$ retained.

**Proposition 3.2B (relative compact transgression).** There is a canonical isomorphism

$$
H^2_{\mathrm{rel},\mathrm{lc}}(K,\Gamma;A)
\xrightarrow{\ \sim\ }
\operatorname{Hom}_{\mathrm{cont}}(C,A)^K.
\tag{3.12b}
$$

Under the map which forgets the chosen splitting, (3.12b) fits into the exact sequence

$$
0\longrightarrow
\frac{H^1(\Gamma,A)}{\operatorname{res}H^1_{\mathrm{cont}}(K,A)}
\longrightarrow
H^2_{\mathrm{rel},\mathrm{lc}}(K,\Gamma;A)
\longrightarrow
\mathfrak M_A(K,\Gamma)
\longrightarrow0.
\tag{3.12c}
$$

**Proof.** Given $\phi\in\operatorname{Hom}_{\mathrm{cont}}(C,A)^K$, form

$$
E_\phi=(A\times\widehat\Gamma)/
\{(-\phi(c),c):c\in C\}.
\tag{3.12d}
$$

The $K$-invariance of $\phi$ makes the displayed graph normal. Thus $E_\phi$ is a profinite
central extension of $K$ by $A$, and
$\gamma\mapsto[(0,\gamma)]$ is a specified abstract splitting over $\Gamma$.

Conversely, let $X$ be a locally compact extension of $K$ by $A$ with a chosen homomorphic
splitting $s:\Gamma\to X$. The compactness argument used for (3.13) below shows that $X$ is
profinite. Every homomorphism from $\Gamma$ to a profinite group is continuous for the full
profinite topology, so $s$ extends uniquely to
$\widehat s:\widehat\Gamma\to X$. The two maps to $K$ agree on the dense subgroup $\Gamma$
and hence everywhere. Therefore $\widehat s(C)\subset A$, and
$\phi=\widehat s|_C$ is continuous and invariant under conjugation by $K$. The two
constructions are inverse, proving (3.12b).

Finally apply the cone exact sequence. Density makes
$H^1_{\mathrm{cont}}(K,A)\to H^1(\Gamma,A)$ injective, and the image of the forgetful map is
exactly the kernel (3.1), because those and only those compact extensions admit an abstract
splitting over $\Gamma$. This gives (3.12c). Under (3.12b), its left term is the restriction
to $C$ of the extensions to $\widehat\Gamma$ of abstract characters of $\Gamma$; quotienting
by it recovers exactly the denominator in (3.2). $\square$

Thus retaining the splitting removes the denominator whose vanishing would be the stem
condition. Forgetting the splitting restores the exact $H^1$ quotient obstruction. This is a
compact relative statement; it does not prove the ordinary adelic pairing $({\rm PAIR}_\star)$.

There is a useful, and more limited, topological statement. Suppose $L=P$ is profinite,
$M=A$ is finite, and the ambient Borel class is already represented by a locally compact
topological extension $E$ with kernel $A$ and quotient $P$. Then $E$ is compact: the image of
a relatively compact identity neighborhood is open in $P$, finitely many translates cover
$P$, and their chosen lifts together with the finite kernel cover $E$ by finitely many
translates of its compact closure. Its identity component maps trivially to the totally
disconnected quotient and hence lies in the finite
kernel; it is therefore trivial. Thus $E$ is profinite. Choose an open normal subgroup
meeting the finite kernel trivially. The quotient map is a homeomorphism on that subgroup and
on each of its finitely many cosets, producing a global continuous set-theoretic section.
Consequently

$$
H^2_{\mathrm B,\mathrm{lc}}(P,A)=H^2_{\mathrm{cont}}(P,A),
\tag{3.13}
$$

where the left side denotes Borel classes supplied with such a locally compact extension
topology. No assertion that an arbitrary Borel group automatically acquires that topology is
being used. Equation (3.13) also does not make the specified splitting over the dense abstract
group $\Delta$ continuous.

### 3.4 The relative finite-to-circle isomorphism

Identify $A_n$ with the kernel of multiplication by $n$ on $\mathbf T$. If every circle
element is represented uniquely by $t\in[0,1)$, the formula
$r_n(t+\mathbf Z)=t/n+\mathbf Z$ defines a Borel map with $nr_n=\operatorname{id}_{\mathbf T}$.
Applying $r_n$ pointwise shows that

$$
0\longrightarrow C^r_{\mathrm B}(L,A_n)
\longrightarrow C^r_{\mathrm B}(L,\mathbf T)
\xrightarrow{n}C^r_{\mathrm B}(L,\mathbf T)
\longrightarrow0
\tag{3.14}
$$

is exact in every degree; the analogous assertion for the discrete group $\Delta$ is
pointwise. Hence (3.14) gives a short exact sequence of relative cone complexes.

**Theorem 3.3 (relative coefficient comparison).** If $i(\Delta)$ is dense in $L$, coefficient
inclusion induces a natural isomorphism

$$
H^2_{\mathrm{rel}}(L,\Delta;A_n)
\xrightarrow{\ \sim\ }
H^2_{\mathrm{rel}}(L,\Delta;\mathbf T)[n].
\tag{3.15}
$$

Moreover, (3.15) preserves actual locally compact extension representatives in the following
strong sense: if an $n$-torsion class on the right is represented by a locally compact
$\mathbf T$-extension $E$ with its specified splitting over $\Delta$, then its unique
preimage is represented by a locally compact $A_n$-extension whose pushout along
$A_n\hookrightarrow\mathbf T$ is $E$ as a relatively split extension.

**Proof.** Apply cohomology to the short exact sequence of relative complexes obtained from
(3.14). The relevant portion of the long exact sequence is

$$
H^1_{\mathrm{rel}}(\mathbf T)
\xrightarrow{n}H^1_{\mathrm{rel}}(\mathbf T)
\longrightarrow H^2_{\mathrm{rel}}(A_n)
\longrightarrow H^2_{\mathrm{rel}}(\mathbf T)
\xrightarrow{n}H^2_{\mathrm{rel}}(\mathbf T).
$$

Lemma 3.2A kills both relative degree-one terms, so exactness gives (3.15).

For the assertion about representatives, let $E$ represent a class $\xi$ on the right. The
quotient $E/A_n$, with $\mathbf T/A_n\simeq\mathbf T$ through multiplication by $n$,
represents $n\xi=0$. A relative nullhomotopy therefore gives a Borel homomorphic section

$$
\bar s:L\longrightarrow E/A_n
$$

whose restriction to $\Delta$ is the quotient of the specified splitting of $E$. Lemma 3.1A
makes $\bar s$ continuous. Pull back the quotient map
$E\to E/A_n$ along $\bar s$:

$$
E_n=L\times_{E/A_n}E.
\tag{3.16}
$$

This is a closed locally compact subgroup of $L\times E$ and fits into
$1\to A_n\to E_n\to L\to1$. The specified splitting over $\Delta$ lifts to $E_n$, and the
pushout is

$$
\mathbf T\mathop{\times}_{A_n}E_n
=\bigl(\mathbf T\times E_n\bigr)/\{(-a,a):a\in A_n\}.
\tag{3.16a}
$$

The homomorphism $\mathbf T\times E_n\to E$ given by $(t,(l,e))\mapsto te$ has kernel exactly
the displayed copy of $A_n$, so it induces an injective continuous homomorphism from (3.16a)
to $E$. It is surjective because, for $e\in E$ above $l$, the two elements $eA_n$ and
$\bar s(l)$ of $E/A_n$ differ by an element of $\mathbf T/A_n$; multiplying $e$ by a lift in
$\mathbf T$ places it in the fiber product. Lemma 3.1B makes the induced continuous bijection
a homeomorphism. It respects the specified splitting over $\Delta$, so the preimage in (3.15)
has an actual locally compact representative whose pushout is $E$ as claimed. Conversely, the
same explicit quotient (3.16a) is a locally compact extension and gives preservation under
topological pushout. $\square$

Theorem 3.3 closes the Borel-cochain coefficient comparison at the correct relative level. It
does not prove the congruence--metaplectic pairing (5.3): one must still compare the compact
relative extension, including its chosen splitting, with an extension of the full adelic
group. Proposition 3.2B and Theorem 3.3 remove the compact relative coefficient obstruction;
they do not prove the ordinary adelic $({\rm PAIR}_\star)$.

## 4. The unconditional scalar endpoint

For $n\geq1$, let $A_n=\mathbf Z/n\mathbf Z$ with trivial Galois action. Use continuous Galois
cohomology, the Tate modification at real places, and the finite-support direct sum to define

$$
\mathscr Q_n(F)
=\operatorname{coker}\!\left[
H^2(F,A_n)
\longrightarrow
\bigoplus_w H^2(F_w,A_n)
\right].
\tag{4.1}
$$

**Lemma 4.1 (scalar duality endpoint).** There is a canonical isomorphism

$$
\mathscr Q_n(F)
\xrightarrow{\ \sim\ }
\operatorname{Hom}(\mu_n(F),\mathbf D).
\tag{4.2}
$$

If $F$ is totally real, then

$$
\mathscr Q_n(F)=0\quad\text{for odd }n,
\qquad
|\mathscr Q_n(F)|\leq2\quad\text{for every }n.
\tag{4.3}
$$

**Proof.** Book 6 proves finite arithmetic duality for the Cartier-dual pair
$(A_n,\mu_n)$, including Tate cohomology at the real places. Apply its degree-two
compact-support row with the two members of the dual pair interchanged. The cokernel in
(4.1) is then the dual of $H^0(F,\mu_n)=\mu_n(F)$, which is (4.2).

If $F$ is totally real, every root of unity in $F$ maps under every real embedding to a real
root of unity, hence is $1$ or $-1$. Thus $\mu_n(F)$ is trivial for odd $n$ and has order at
most two in general. Equation (4.3) follows from (4.2). $\square$

This is the last, and only the last, scalar step. Book 6 does not construct a map from an
adelic multiplier kernel to $\mathscr Q_n(F)$.

## 5. The missing congruence--metaplectic hypotheses

Define the adelic Moore multiplier kernel

$$
\mathfrak M^S(H)
=\ker\!\left[
H^2_{\mathrm m}(G^S,\mathbf T)
\longrightarrow
H^2(H(F),\mathbf T)
\right].
\tag{5.1}
$$

Here $H^2_{\mathrm m}$ is, by definition for this manuscript, the locally compact extension
subgroup $H^2_{\mathrm B,\mathrm{lc}}$ fixed in Section 3.3. The notation records the
multiplier convention; no comparison theorem with another measurable-cohomology model is
used, and no automatic topologization of an arbitrary Borel group is assumed. The diagonal
group $H(F)$ in the target is discrete. The omitted set is exactly
$S=V_\infty(F)\cup\{v\}$.

The following package is a list of hypotheses, not a theorem proved in this volume.

### 5.1 Centrality and perfect duality

Choose a reference compact open $K_\star\subset G^S$ and put

$$
\Gamma_\star=\Gamma(K_\star),
\qquad
C_\star=C(K_\star).
$$

The first two hypotheses are:

$$
({\rm CEN}_\star):
\qquad
C_\star\subset
Z(\widehat{\Gamma_\star}),
\tag{5.2}
$$

and

$$
({\rm PAIR}_\star):
\qquad
C_\star^\vee
:=\operatorname{Hom}_{\mathrm{cont}}(C_\star,\mathbf T)
\xrightarrow{\ \sim\ }
\mathfrak M^S(H).
\tag{5.3}
$$

The isomorphism in (5.3) must be constructed and proved injective and surjective. It is not
obtained from (3.2) by replacing finite coefficients with $\mathbf T$. Ordinary compact
transgression after forgetting the splitting would require the stem condition (3.3). Relative
compact transgression avoids that denominator by retaining the splitting, but then a new
compact-to-adelic theorem must compare that retained compact splitting with the diagonal
adelic splitting. Neither route is supplied by centrality alone.

### 5.2 Local classification

One part of the split local argument can be completed without applying a profinite theorem to
the noncompact additive group.

One standard locally compact abelian foundation used at exactly this point is not reproved in
this manuscript and is therefore isolated rather than silently attributed to profinite
cohomology.

**Foundational hypothesis $({\rm FND}_{\rm PD})$.** Pontryagin character duality is an exact
contravariant duality on locally compact second-countable abelian groups: it takes a
closed-subgroup quotient sequence to an exact dual sequence, and the evaluation map to the
bidual is a topological isomorphism.

Only the special consequence for an extension of a nonarchimedean additive group by
$\mathbf T$ is used below. No measurable-cohomology assertion is included in
$({\rm FND}_{\rm PD})$.

**Lemma 5.0A (canonical splitting of split root groups).** Let $k$ be a nonarchimedean local
field and let

$$
1\longrightarrow\mathbf T\longrightarrow E
\longrightarrow\operatorname{SL}_2(k)\longrightarrow1
\tag{5.3a}
$$

be a central locally compact extension with a Borel section. Assume
$({\rm FND}_{\rm PD})$. Its restrictions to the upper and lower root groups admit unique
continuous homomorphic splittings which are equivariant for conjugation by the diagonal
torus.

**Proof.** Consider the upper root group $U=x(k)$ and write $E_U$ for its inverse image. The
commutator on $E_U$ is constant on the fibers of the open quotient
$E_U\times E_U\to U\times U$, so it descends to a continuous alternating bicharacter

$$
B:k\times k\longrightarrow\mathbf T.
$$

Let $\pi$ be a uniformizer. Conjugation by any lift of
$h(\pi)=\operatorname{diag}(\pi,\pi^{-1})$ preserves commutators and sends $x(r)$ to
$x(\pi^2r)$. Therefore

$$
B(r,s)=B(\pi^{2m}r,\pi^{2m}s)
$$

for every $m\geq0$. The right side tends to $B(0,0)=0$, so $B=0$. Thus the inverse image of
$U$ is abelian.

By $({\rm FND}_{\rm PD})$, dualizing
$0\to\mathbf T\to E_U\to(k,+)\to0$ gives an exact sequence

$$
0\longrightarrow\widehat{k}
\longrightarrow\widehat{E_U}
\longrightarrow\widehat{\mathbf T}=\mathbf Z
\longrightarrow0.
\tag{5.3ab}
$$

Choose a character of $E_U$ mapping to $1\in\mathbf Z$. Since $\mathbf Z$ is discrete and
free, this choice splits (5.3ab). Dualizing it back and using biduality gives a continuous
retraction $r:E_U\to\mathbf T$ of the kernel inclusion. The restriction of the quotient map
$E_U\to k$ to $\ker r$ is a continuous bijective homomorphism. Lemma 3.1B makes it a
homeomorphism, so its inverse is a continuous homomorphic section $s:k\to E_U$.

Conjugation by a lift of $h(\pi)$ has the form

$$
\widetilde h(\pi)s(r)\widetilde h(\pi)^{-1}
=\chi(r)s(\pi^2r)
\tag{5.3b}
$$

for a continuous additive character $\chi:k\to\mathbf T$. Such a character kills a
sufficiently small additive compact open subgroup: its image on a compact open is the
profinite quotient by the character kernel, hence is a totally disconnected closed subgroup
of the circle and therefore finite. The kernel is then open in that compact open. Consequently
the sum

$$
\psi(r)=-\sum_{j\geq0}\chi(\pi^{2j}r)
\tag{5.3c}
$$

is finite for each $r$, locally finite, and continuous. Replacing $s(r)$ by $\psi(r)s(r)$
defines another homomorphic splitting because the locally finite sum $\psi$ is additive, and
makes (5.3b) equivariant. If two $h(\pi)$-equivariant splittings existed, their quotient would
be a continuous additive character $\eta$ satisfying
$\eta(r)=\eta(\pi^{2m}r)$ for every $m$; continuity forces $\eta=0$.

For $a\in k^\times$, choose a lift $\widetilde h(a)$ and reparameterize the conjugate section
as

$$
s_a(r)=\widetilde h(a)s(a^{-2}r)\widetilde h(a)^{-1}.
$$

This is another splitting of $x(k)$. It is $h(\pi)$-equivariant because the conjugations by
any lifts of $h(a)$ and $h(\pi)$ commute: the commutator of the two lifts is central.
Uniqueness gives $s_a=s$, which is precisely equivariance under $h(a)$. The lower-root proof
is identical after conjugating by $h(\pi)^{-1}$, which sends $y(r)$ to $y(\pi^2r)$ and hence
contracts its parameter. $\square$

Under $({\rm FND}_{\rm PD})$, Lemma 5.0A supplies exact root lifts and proves the step for
which the earlier text incorrectly used finite-quotient factorization on $(k,+)$. It does not
finish the local classification.
One must still prove the full rank-one Steinberg presentation in the topological extension
category, show that the torus defect is a continuous Steinberg symbol, classify every such
symbol with its wild and even-primary layers, and prove that zero symbol makes the extension
split. None of those conclusions follows merely from the existence of root splittings.

For each $n$, a local theorem is required at every finite $w\notin S$.

$$
({\rm LOC}_n):
$$

- when $B_w$ is split, all order-dividing-$n$ Moore multiplier classes of
  $\operatorname{SL}_2(F_w)$ are classified by a correctly normalized, Galois-equivariant
  norm-residue invariant, the Moore--Steinberg extension is universal in the required
  topological category, and trivial invariant detects the trivial extension;
- when $B_w$ is division, the analogous classification and detection theorem is proved
  directly for $\operatorname{SL}_1(B_w)$ and is compatible with scalar extension to a
  splitting field;
- the theorem includes residue characteristics dividing $n$, and it uses continuous or
  measurable cohomology of the actual locally compact group rather than a finite-quotient
  argument valid only for profinite groups.

For a quaternion division algebra $D/k$, the group $D^1$ is compact and profinite. The only
formal coefficient statement available without a division multiplier calculation is the
Bockstein exact sequence

$$
0\longrightarrow
\frac{\operatorname{Hom}_{\mathrm{cont}}(D^1,\mathbf T)}
{n\operatorname{Hom}_{\mathrm{cont}}(D^1,\mathbf T)}
\longrightarrow H^2_{\mathrm{cont}}(D^1,A_n)
\longrightarrow H^2_{\mathrm{cont}}(D^1,\mathbf T)[n]
\longrightarrow0.
\tag{5.3d}
$$

Indeed, if $X$ is profinite and $f:X\to\mathbf T$ is continuous, cover the circle by finitely
many arcs on each of which multiplication by $n$ has a continuous inverse branch. The inverse
images cover $X$ and admit a finite clopen partition subordinate to that cover. Choosing the
corresponding branch on each clopen piece gives a continuous $n$th root of $f$. Apply this to
each continuous cochain space $X=(D^1)^r$; the coefficient sequence is therefore exact on
continuous cochains and gives (5.3d). Equation (5.3d) relates two unknown groups; it neither
computes
$H^2_{\mathrm{cont}}(D^1,A_n)$ nor supplies a norm-residue invariant, detection, or a
division analogue of Steinberg universality.

At a split place, a torus-commutator formula can detect odd-primary information after all
normalizations are proved. It does not by itself classify even-primary extensions. At a
division place there is no split diagonal torus over $F_w$, and
$\operatorname{SL}_1(B_w)$ is not a finite-index subgroup of
$\operatorname{SL}_2(E_w)$ for a quadratic splitting field $E_w$. Thus ordinary
restriction--corestriction for finite-index subgroups does not prove the division theorem.

Nor may a profinite factorization theorem be applied to the additive root group $(F_w,+)$:
that group is noncompact. A continuous cocycle on it need not factor through a finite quotient
of the whole additive group. Any root splitting used in $({\rm LOC}_n)$ must be proved in the
locally compact category.

### 5.3 Products, cross terms, and restricted products

Even a finite direct product has multiplier classes invisible on each factor. If
$\alpha:G_1\to A_n$ and $\beta:G_2\to A_n$ are continuous characters, then

$$
c\bigl((g_1,g_2),(h_1,h_2)\bigr)
=\frac{\alpha(g_1)\beta(h_2)}{n}\pmod{\mathbf Z}
\tag{5.4}
$$

is a continuous $\mathbf T$-valued cocycle. It restricts trivially to each factor, but the
commutator of lifts from the two distinct factors can be nontrivial.

The exact finite-product structure can be proved without any arithmetic input. Write

$$
G^{\mathrm{ab}}_{\mathrm{top}}
=G/\overline{[G,G]}
$$

and let $\operatorname{Bichar}_{\mathrm{cont}}(G_1,G_2;\mathbf T)$ be the group of continuous
maps $\beta:G_1\times G_2\to\mathbf T$ which are homomorphisms in each variable.

**Proposition 5.1 (two-factor extension decomposition).** For locally compact
second-countable groups $G_1,G_2$, restriction to the factors and cross commutator give an
isomorphism

$$
H^2_{\mathrm B,\mathrm{lc}}(G_1\times G_2,\mathbf T)
\simeq
H^2_{\mathrm B,\mathrm{lc}}(G_1,\mathbf T)
\oplus H^2_{\mathrm B,\mathrm{lc}}(G_2,\mathbf T)
\oplus
\operatorname{Bichar}_{\mathrm{cont}}
(G_1^{\mathrm{ab}}_{\mathrm{top}},G_2^{\mathrm{ab}}_{\mathrm{top}};\mathbf T).
\tag{5.4a}
$$

**Proof.** Let $E$ be a central extension of $G_1\times G_2$ by $\mathbf T$. If
$\widetilde g$ and $\widetilde h$ lift $(g,1)$ and $(1,h)$, respectively, define

$$
\beta_E(g,h)=[\widetilde g,\widetilde h].
\tag{5.4b}
$$

The two base elements commute, so their commutator lies in the central kernel and is
independent of the lifts. The commutator identities show that it is multiplicative in each
variable. It is continuous because the continuous commutator map on the two inverse-image
subgroups is constant on the fibers of their open quotient maps and therefore descends to the
product quotient. It kills closed commutator subgroups and hence factors through the displayed
topological abelianizations.

Subtract, in the Baer group of locally compact extensions, the inflations of the two factor
restrictions. The resulting extension has trivial factor restrictions. Choose continuous
homomorphic splittings $s_1,s_2$ of
those restrictions. Every element has a unique expression

$$
z,s_1(g)s_2(h),
\qquad z\in\mathbf T.
$$

Moving $s_2(h_1)$ past $s_1(g_2)$ shows that multiplication is twisted only by
$\beta_E(g_2,h_1)^{-1}$. Thus the reduced extension is determined by $\beta_E$. Conversely a
continuous bicharacter defines exactly this multiplication and hence a reduced central
extension. Changing either splitting by a character does not change the cross commutator.
The constructions are inverse and commute with Baer sum. $\square$

**Lemma 5.1A (split factors have no cross characters).** If $k$ is an infinite field, then
$\operatorname{SL}_2(k)$ is perfect. Consequently every continuous cross bicharacter in
(5.4a) with one split local quaternionic factor is zero.

**Proof.** Put

$$
x(r)=\begin{pmatrix}1&r\\0&1\end{pmatrix},
\quad
y(r)=\begin{pmatrix}1&0\\r&1\end{pmatrix},
\quad
h(a)=\begin{pmatrix}a&0\\0&a^{-1}\end{pmatrix}.
$$

Choose $a\in k^\times$ with $a^2\ne1$. Direct multiplication gives

$$
[h(a),x(r/(a^2-1))]=x(r),
\qquad
[h(a),y(r/(a^{-2}-1))]=y(r).
$$

The upper and lower elementary matrices generate $\operatorname{SL}_2(k)$ by row reduction,
so every generator lies in the commutator subgroup. Hence the group is perfect. Its
topological abelianization is therefore trivial, and Proposition 5.1 kills any cross
bicharacter involving it. $\square$

For a finite set $J$ of finite places put

$$
G_J=\prod_{w\in J}H(F_w),
\qquad
\Delta_J=\operatorname{im}\!\left[H(F)\longrightarrow G_J\right].
\tag{5.4c}
$$

Here the adjective *projected-diagonal* is essential: $\Delta_J$ is the projection of the
global diagonal, not the subgroup of the adeles obtained by putting identity elements outside
$J$.

**Proposition 5.1B (projected-diagonal cross-term vanishing).** Let a locally compact central
extension of $G_J$ by $\mathbf T$ have a homomorphic splitting over $\Delta_J$. Then every
cross bicharacter in the iterated decomposition of Proposition 5.1 is zero, including a cross
term between two division factors.

**Proof.** A cross term involving a split factor vanishes by Lemma 5.1A. It remains to treat
two places $u,z\in J$ at which $B$ is division. Fix noncentral elements
$g\in H(F_u)$ and $h\in H(F_z)$. Since they are not $-1$, their Cayley parameters

$$
X_u=(g-1)(g+1)^{-1}\in B_u^0,
\qquad
X_z=(h-1)(h+1)^{-1}\in B_z^0
$$

are defined in the trace-zero subspaces and recover $g$ and $h$ by
$X\mapsto(1+X)(1-X)^{-1}$.

The $F$-vector space $B^0$ satisfies weak approximation. Choose a sequence
$X_j\in B^0(F)$ approaching $X_u$ at $u$ and $X_z$ at $z$, while remaining close to a fixed
nonzero trace-zero element at every other ramified place of $B$. For large $j$,
$L_j=F(X_j)$ is a quadratic field embedded in $B$: indeed $X_j^2\in F^\times$ is nonsquare
at the division place $u$. Put

$$
T_j=\operatorname{R}^{1}_{L_j/F}\mathbf G_m\subset H.
$$

The local Cayley transforms of $X_j$ tend to $g$ at $u$ and to $h$ at $z$. Each global
quadratic norm-one torus $T_j$ satisfies weak approximation: away from the point $-1$, the
Cayley parameter

$$
r\longmapsto\frac{1+r\sqrt d}{1-r\sqrt d}
$$

is an $F$-rational parametrization when $L_j=F(\sqrt d)$. Applying weak approximation on
$T_j$ with accuracy tending to zero gives $a_j,b_j\in T_j(F)$ such that, in $G_J$,

$$
a_j\longrightarrow(g,1,\ldots,1),
\qquad
b_j\longrightarrow(1,h,\ldots,1),
\tag{5.4d}
$$

with $g$ in the $u$-coordinate and $h$ in the $z$-coordinate. The elements $a_j$ and $b_j$
commute in $H(F)$. Their lifts under the homomorphic splitting of $\Delta_J$ therefore have
trivial commutator.

Iterating Proposition 5.1 expresses that commutator as the product of the same-factor
commutators and the cross bicharacters. In the limit (5.4d), every same-factor term tends to
$1$, because at least one entry tends to the identity. Every cross term does likewise except
the $(u,z)$-term, whose limit is the value of the cross bicharacter at $(g,h)$. That value must
therefore be $1$. Noncentral elements are dense in each local division norm-one group, and the
cross bicharacter is continuous, so it vanishes everywhere. This treats every pair. $\square$

Thus all projected-diagonal finite-product cross terms vanish rigorously. This does **not**
solve the adelic embedded-subproduct problem: the rational approximants used in (5.4d) have
uncontrolled coordinates outside $J$. In an adelic extension, their total commutator can
retain compact-tail terms. Passing from the projected finite product to the actually embedded
finite subproduct requires a coherent homomorphic splitting over the full compact tail.

The normalization needed for a restricted-product tail is not an additional choice of
cocycle once a compact splitting has been fixed.

**Lemma 5.1C (normalization from a compact splitting).** Let $G$ be locally compact and
second-countable, let $K\subset G$ be compact open, and let a locally compact central
extension $E$ of $G$ by $\mathbf T$ have a continuous homomorphic splitting $\sigma$ over
$K$. There is a continuous section of $E\to G$ which restricts to $\sigma$, and its cocycle
vanishes on $K\times K$. If two such sections restrict to the same $\sigma$, their
cochain difference vanishes on $K$.

**Proof.** The discrete space $G/K$ is countable because $G$ is second-countable. Choose one
representative $r$ of every right coset and a lift $\widetilde r\in E$, taking
$\widetilde1=1$. Every $g\in G$ has a unique expression $g=rk$ with $k\in K$. Define

$$
s(rk)=\widetilde r\,\sigma(k).
$$

Each coset $rK$ is clopen, and on it this formula is continuous, so $s$ is continuous. On $K$ it
equals the homomorphism $\sigma$, and therefore its cocycle is zero on $K\times K$. If
$s'$ is a second such section, the unique central cochain $b$ with $s'=b+s$ is zero on $K$.
$\square$

There is now a rigorous sufficient construction for restricted products. Suppose that every
local extension has a chosen continuous splitting over $K_w^0$ for all but finitely many $w$,
and let $J_0$ contain the exceptional places. For $w\notin S\cup J_0$, use Lemma 5.1C to
choose a continuous cocycle $c_w$ representing it and satisfying

$$
c_w(k,k')=0
\qquad(k,k'\in K_w^0).
\tag{5.4e}
$$

On the restricted-product tail away from $J_0$, the expression

$$
c^{J_0}(g,h)=\sum_{w\notin S\cup J_0}c_w(g_w,h_w)
\tag{5.4f}
$$

is a finite sum: almost every pair $(g_w,h_w)$ lies in $K_w^0\times K_w^0$. It is a
continuous cocycle, because near any fixed $(g,h)$ only a fixed finite set of coordinates can
contribute. The cocycle identity follows by summing the local identities. Pull this tail
extension back to $G^S$ and take its Baer sum with the finitely many pullbacks of the given
actual local extensions at $w\in J_0$. This produces a locally compact extension without
asserting that an exceptional extension has a continuous global section. If Borel sections
are chosen at those finitely many places, their cocycles may be added to (5.4f) to give a
pointwise Borel cocycle for the resulting actual extension; that total cocycle is continuous
only when the exceptional sections can also be chosen continuous.

**Proposition 5.2 (normalized restricted-product gluing).** The tail-plus-finite-Baer
construction above gives a central locally compact extension of $G^S$ by $\mathbf T$.
Replacing the normalized tail cocycles $c_w$ by $c_w+db_w$, where every
$b_w:H(F_w)\to\mathbf T$ is continuous and $b_w|_{K_w^0}=0$ for almost all $w$, changes
(5.4f) by the global coboundary of the pointwise-finite continuous sum
$b(g)=\sum_{w\notin S\cup J_0}b_w(g_w)$. Replacing any of the finitely many exceptional
extensions by an equivalent actual extension preserves the finite Baer sum. Hence the
resulting class depends only on the local classes together with their compatible almost-all
compact splittings.

**Proof.** Finiteness, continuity, and the cocycle identity on the tail were checked above.
Pullback and finite Baer sum preserve locally compact second-countable central extensions.
The same pointwise-finiteness argument applies to the tail cochains $b_w$ and gives
$\sum_wdb_w=d(\sum_wb_w)$. Equivalences at the exceptional places pull back and pass through
finite Baer sum. $\square$

The converse is valid under the full compact-splitting hypothesis.

**Proposition 5.3 (compact-product converse).** Put
$K^0=\prod_{w\notin S}K_w^0$. If a locally compact central extension $E$ of $G^S$ by
$\mathbf T$ has a continuous homomorphic splitting $\sigma:K^0\to E$, then $E$, together with
$\sigma$, is equivalent to the normalized restricted-product extension formed from its local
factor restrictions and the splittings $\sigma_w=\sigma|_{K_w^0}$. In particular, local
restriction detects extensions supplied with such a full compact-product splitting.

**Proof.** For two distinct local factors, their cross commutator is zero. If at least one
factor is split, this follows from Lemma 5.1A. If both are division factors, then
$H(F_w)=K_w^0$ at each of the two places, and the lifts supplied by the homomorphism $\sigma$
commute because the corresponding elements commute in $K^0$.

Every $g\in G^S$ has a decomposition

$$
g=\left(\prod_{w\in J}g^{(w)}\right)k,
\qquad k\in K^0,
\tag{5.4g}
$$

where $J$ is the finite set of coordinates for which $g_w\notin K_w^0$ and $g^{(w)}$ is
supported at $w$. Every place in $J$ is split. Lift the finitely many $g^{(w)}$ through the
corresponding local restriction and lift $k$ through $\sigma$. The cross-commutator vanishing
just proved makes their product independent of ordering and compatible with multiplication.
If a compact coordinate is moved between the finite product and $k$, its two lifts agree
because the local splitting is $\sigma_w$. Thus (5.4g) constructs an isomorphism from the
normalized gluing of the local restrictions to $E$. It is continuous on each open piece with
$J$ contained in a fixed finite set, hence globally continuous. The construction preserves
$\sigma$. $\square$

Proposition 5.3 is deliberately conditional on one homomorphic splitting over the **full**
product $K^0$. Unrelated local splittings do not imply it. Without this coherence, an
extension can retain a compact-tail class which no list of factor restrictions sees.

Accordingly, one needs a separate hypothesis

$$
({\rm PROD}_n):
$$

- every relevant adelic class admits, after isolating a finite exceptional set, one coherent
  homomorphic splitting over the full maximal compact tail, compatible with its local
  splittings;
- Proposition 5.3 can then be applied on that tail, and Proposition 5.1B can be transported
  from projected diagonals to the actually embedded finite subproducts without an unrecorded
  tail commutator;
- the resulting restricted-product reciprocity law detects the adelic class from its local
  data and compact-tail normalization.

A diagonal splitting by itself does not supply the first bullet. Proposition 5.1B proves the
finite projected statement, while $({\rm PROD}_n)$ is the still-missing compact-tail and
restricted-product reciprocity theorem needed to use it adelically.

### 5.4 Adelic-to-scalar reduction

After $({\rm LOC}_n)$ and $({\rm PROD}_n)$, one still needs to prove that diagonal splitting
is exactly the scalar reciprocity condition and that no normalized adelic class disappears in
the passage to scalar data. A raw family of local restrictions of an adelic multiplier class
need not be finitely supported, so it is not, by itself, an element of the direct sum in
(4.1). The missing theorem must instead extract one global character

$$
({\rm SC}_n):
\qquad
\chi_n:
\mathfrak M^S(H)[n]
\hookrightarrow
\operatorname{Hom}(\mu_n(F),\mathbf D).
\tag{5.5}
$$

Here both the construction and injectivity of $\chi_n$ are new: they include local detection,
compact-tail coherence, restricted-product reciprocity, the omitted places, and diagonal
normalization. If $\theta_n$ denotes the Book 6 isomorphism (4.2), define only after that
theorem has been proved

$$
\operatorname{sc}_n
=\theta_n^{-1}\chi_n:
\mathfrak M^S(H)[n]\hookrightarrow\mathscr Q_n(F).
\tag{5.5a}
$$

The normalization is separate for each $n$. No compatibility under coefficient inclusions
$A_n\hookrightarrow A_N$ is asserted. There is a concrete warning when $n=4$ and $N=8$.
Suppose $F$ contains $\mu_4$ but not $\mu_8$. The scalar transition induced by
$A_4\hookrightarrow A_8$ is dual, under (4.2), to

$$
\mu_8(F)=\mu_4\longrightarrow\mu_4(F)=\mu_4,
\qquad z\longmapsto z^2.
\tag{5.5b}
$$

It kills the quadratic character $\lambda$ of $\mu_4$ with
$\lambda(i)=\tfrac12\pmod{\mathbf Z}$. Thus the scalar transition is not an inclusion, and no
formal compatibility of the separately normalized maps $\operatorname{sc}_4$ and
$\operatorname{sc}_8$ may be used.

For the sharp finite-kernel conclusion one also needs

$$
({\rm TOR}):
\qquad
\mathfrak M^S(H)\text{ is torsion}.
\tag{5.6}
$$

For odd-primary Ihara theory, it is enough to assume (5.3) and (5.5) for odd $n$; neither the
all-primary classification nor (5.6) is needed for that weaker consequence.

### 5.5 Required interfaces and proposed sufficient routes

The intended source-closed construction has six unresolved **interfaces**. Calling them
interfaces records what this proof architecture must supply; it does not assert that a
different proof of the final theorem could not bypass one of them.

1. $({\rm CEN}_\star)$: centrality of the reference congruence kernel, as stated in (5.2).
2. $({\rm PAIR}_\star)$: the compact-to-adelic character pairing (5.3), including
   compatibility of the retained compact splitting with the adelic diagonal splitting.
   Proposition 3.2B does not supply this comparison.
3. $({\rm LOC}_n)$: split Moore--Steinberg universality, classification, normalization, and
   detection, including wild and even-primary layers, together with the division local $H^2$
   calculation and detection theorem. The Bockstein sequence (5.3d) is not that calculation.
4. $({\rm PROD}_n)$: coherent compact-tail splitting and restricted-product reciprocity,
   transporting Proposition 5.1B from projected diagonals to adelic embedded subproducts.
5. $({\rm SC}_n)$: construction and injectivity of the scalar character $\chi_n$ from the
   normalized adelic data; raw local restrictions need not be finitely supported.
6. $({\rm TOR})$: torsion of $\mathfrak M^S(H)$, or a directly adequate common exponent
   theorem, when the all-primary finite-kernel conclusion is desired.

The conditions $({\rm QRM}_m)$ and $({\rm PA}_m)$ have a different logical status. They are
**proposed sufficient routes**, not necessary interfaces. By (2.15)--(2.16) and Proposition
2.4A, $({\rm QRM}_m)$ for every $m$ suffices for $({\rm CEN}_\star)$. By Theorem 2.5,
$({\rm PA}_m)$ for every $m$ suffices for the stem property, and its odd-$m$ range suffices
for the corresponding odd-primary finite-abelian continuity. The stem property is relevant
to the ordinary compact-transgression route; the retained-splitting route instead asks for
$({\rm PAIR}_\star)$ directly. No converse, mutual implication, or logical independence for
$({\rm QRM}_m)$ and $({\rm PA}_m)$ has been proved here.

The separate $({\rm FND}_{\rm PD})$ is a named foundational hypothesis used only in the
Pontryagin splitting inside Lemma 5.0A; it is not one of these arithmetic interfaces. All
other Borel-extension conventions, automatic continuity, relative-extension calculations,
and finite-to-circle pullbacks used here were defined and proved in Sections 3.3--3.4.

We call the conjunction of $({\rm CEN}_\star)$, $({\rm PAIR}_\star)$,
$({\rm LOC}_n)$, $({\rm PROD}_n)$, and $({\rm SC}_n)$ for every $n$, together with
$({\rm TOR})$, the **conditional rank-two congruence--metaplectic package**
$({\rm R2CM})_{F,B,v}$. The proposed routes $({\rm QRM}_m)$ and $({\rm PA}_m)$ are not part
of its definition.

## 6. Conditional arithmetic consequences

Everything in this chapter is a formal theorem from the hypotheses just stated and the
unconditional scalar Lemma 4.1.

### 6.1 Odd-primary character vanishing

**Theorem 6.1 (conditional odd-primary theorem).** Assume that $F$ is totally real, that
$({\rm PAIR}_\star)$ holds, and that $({\rm SC}_n)$ holds for every odd $n$. Then, for every
compact open $K\subset G^S$ and every finite odd-primary abelian group $A$,

$$
\operatorname{Hom}_{\mathrm{cont}}(C(K),A)=0.
\tag{6.1}
$$

**Proof.** Lemma 2.2 identifies $C(K)$ with $C_\star$ through a common open intersection, so
it is enough to treat $C_\star$. Suppose that
$f:C_\star\to A$ is nonzero. The finite abelian group $f(C_\star)$ has a character
$\lambda:f(C_\star)\to\mathbf T$ for which $\lambda\circ f$ is nonzero. Let $n$ be the order
of that character. Then $n$ is odd and

$$
0\ne\lambda\circ f\in C_\star^\vee[n].
$$

Under (5.3), this character gives a nonzero element of $\mathfrak M^S(H)[n]$. Hypothesis
$({\rm SC}_n)$ injects it into $\operatorname{Hom}(\mu_n(F),\mathbf D)$, equivalently into
$\mathscr Q_n(F)$ by (4.2), but (4.3) says that this scalar group is zero. This contradiction
proves (6.1). $\square$

Notice that the proof uses the perfect pairing before using roots of unity. A roots-of-unity
bound alone says nothing about $C(K)$.

### 6.2 The all-primary size bound

**Theorem 6.2 (conditional finite-kernel theorem).** Assume
$({\rm R2CM})_{F,B,v}$. Let $e$ be the exponent of the finite group $\mu(F)$. Then $C_\star$
is finite, its exponent divides $e$, and

$$
|C_\star|\leq|\mu(F)|.
\tag{6.2}
$$

If $F$ is totally real, then

$$
|C_\star|\leq2.
\tag{6.3}
$$

In that totally real case the common kernel is central in every spectator-level completion,
and every rational routing transition acts trivially on it.

**Proof.** Let $\xi\in\mathfrak M^S(H)$ have order $n$. By $({\rm SC}_n)$, the cyclic group
generated by $\xi$ injects into

$$
\operatorname{Hom}(\mu_n(F),\mathbf D).
$$

The exponent of the latter group divides $e$, so $n$ divides $e$. No compatibility between
different values of $n$ is used here. Hypothesis (5.6) now gives

$$
\mathfrak M^S(H)=\mathfrak M^S(H)[e].
$$

Applying $({\rm SC}_e)$ and then (4.2) yields

$$
|\mathfrak M^S(H)|
\leq
|\operatorname{Hom}(\mu_e(F),\mathbf D)|
=|\mu(F)|.
\tag{6.4}
$$

By (5.2), $C_\star$ is a profinite abelian group. By (5.3), its character group is the finite
group in (6.4). Continuous finite characters separate points of a profinite abelian group:
a nonidentity element survives in a finite abelian quotient, and the characters of that
quotient separate its points. Hence the evaluation map

$$
C_\star\longrightarrow
\operatorname{Hom}(C_\star^\vee,\mathbf T)
$$

is injective. Its target is finite, so $C_\star$ is finite. Finite Pontryagin duality gives
$|C_\star|=|C_\star^\vee|$ and equality of exponents. This proves (6.2).

If $F$ is totally real, $\mu(F)=\{\pm1\}$, giving (6.3). Lemma 2.2 identifies the kernel at
every spectator level with this group. It is normal in each corresponding completion, and a
group of order at most two has trivial automorphism group. Conjugation and every rational
routing transition therefore act trivially. $\square$

The last routing conclusion depends on the all-primary order bound. Reference-level
centrality plus open-level invariance alone would not prove it.

## 7. The exact export to Ihara theory

Book 139 works with routed components. At one such component its exact profinite extension is

$$
1\longrightarrow C_c
\longrightarrow\widehat\Gamma_c
\longrightarrow K_c^v
\longrightarrow1.
\tag{7.1}
$$

For a finite $\ell$-primary trivial coefficient module $A$, its Proposition 5.4 identifies
the noncongruence character quotient with

$$
H^1_{\mathrm{nc}}(\Gamma_c,A)
\simeq
\ker\!\left[
\operatorname{Hom}_{\mathrm{cont}}(C_c,A)^{K_c^v}
\xrightarrow{\operatorname{tg}_{c,A}}
H^2_{\mathrm{cont}}(K_c^v,A)
\right].
\tag{7.2}
$$

This formula needs no centrality. It also shows that vanishing of the entire character group
is stronger than necessary: the geometric application only needs the appropriate routed,
descent-invariant, non-Eisenstein localization of the kernel in (7.2) to vanish.

Let $\mathscr R$ be the finite routed family of constant-coefficient degeneracy rows used in
Book 139. Its named minimal arithmetic hypothesis is

$$
({\rm AC}^{\rm loc}_\ell)_{\mathscr R}:
\qquad
\left(
\bigoplus_c H^1_{\mathrm{nc}}(\Gamma_{R,c},k_R)
\right)^{\Delta_R}_{\mathfrak m_R}=0
\quad\text{for every }R\in\mathscr R.
\tag{7.3}
$$

The exact component and localization conventions are those of Book 139; changing a spectator
level changes the quotient action and transgression map even though Lemma 2.2 identifies the
underlying kernel.

**Theorem 7.1 (conditional routed Ihara consequence).** Assume hypotheses 1--7 of Book 139,
Theorem 14.1, at every row of $\mathscr R$.

1. Hypothesis (7.3) implies residual injectivity of every routed two-degeneracy map,
   saturation of its integral old image, and freeness of its new quotient, with the component,
   monodromy, and branch corrections retained as in Book 139.
2. If $\ell$ is odd and every triple $(F_R,B_R,v_R)$ in the family satisfies the hypotheses of
   Theorem 6.1, then (7.3) holds.

**Proof.** The first assertion is Book 139, Proposition 14.2 and Theorem 14.1. For the second,
Theorem 6.1 gives

$$
\operatorname{Hom}_{\mathrm{cont}}(C_{R,c},k_R)=0
$$

at every actual spectator level. The right side of (7.2) is therefore zero before descent,
routing, or localization. Hence (7.3) holds, and the first assertion applies. $\square$

This is the only Ihara conclusion established here. Book 126 constructs rank-two Galois
representations from already available weight-two Shimura-curve cohomology; it contains no
congruence-kernel, metaplectic, or local-multiplier theorem and does not discharge any
hypothesis of Theorems 6.1 or 7.1.

## 8. Audit of the rejected proof routes

The conditional boundary above is forced by six distinct failures in the attempted
unconditional proof. No claim of logical independence among them is needed.

### 8.1 Stabilization is not vanishing

For a finite quotient $q:\Gamma\to Q$, the descending subgroups

$$
q(\Gamma(\mathfrak a))
\supseteq q(\Gamma(\mathfrak a^2))
\supseteq\cdots
$$

eventually stabilize because $Q$ is finite. Stabilization only gives
$R_j=R_{j+d}$ for a stable subgroup $R_j$; it does not give $R_j=1$. Nor does it show that an
individual approximate root generator maps trivially. A filtration-increasing conjugation on
local coordinates cannot be transported to an arbitrary finite quotient unless an exact
root-word filtration and its separation have first been proved. Neither Book 118 nor Book 82
provides that theorem.

Consequently no ideal-commutator theorem, centrality theorem, or stem theorem follows from the
stabilization argument.

### 8.2 Approximation does not preserve exact identities

Book 118 can choose a rational norm-one point in prescribed local neighborhoods while
retaining integrality away from a finite set. Replacing a local root element by such a rational
point preserves proximity and congruence conditions; it does not preserve an exact identity
such as

$$
z_{j+1}=k_jz_jk_j^{-1}e_j
$$

with $e_j$ in a specified principal congruence subgroup. It also does not prove bounded exact
generation of that subgroup by descended root words. An abstract finite quotient sees exact
equalities, not limits in a local field. The attempted contraction argument therefore cannot
be repaired by choosing successively closer rational points.

### 8.3 Finite and Moore coefficients cannot be normalized circularly

Proposition 3.1 gives the exact finite-coefficient quotient. Equation (3.7) shows that a
finite-kernel extension cannot be converted formally into a circle extension or conversely.
Moreover, a splitting over the abstract dense subgroup $\Gamma$ need not be continuous for
the topology induced by $K$. Normalizing a relative cocycle along that splitting and then
using density to claim continuity is circular: continuity of precisely such abstract data is
the congruence issue being studied. The relative cone (3.8) retains the splitting, and
Lemma 3.2A kills relative degree one, and Theorem 3.3 gives the resulting finite-to-circle
isomorphism, including actual locally compact representatives. Proposition 3.2B likewise
removes the stem denominator only while the compact splitting is retained. Forgetting that
splitting restores the exact $H^1$ quotient (3.12c). What remains unproved is the comparison
from this compact relative calculation to the full adelic extension group and hence the
ordinary perfect pairing (5.3).

### 8.4 The local multiplier theorems are absent

Book 82 proves structural facts about quaternion orders and their radical filtrations. It does
not classify $H^2_{\mathrm m}(\operatorname{SL}_2(F_w),\mathbf T)$ or the corresponding group
for $\operatorname{SL}_1(B_w)$. A split torus calculation does not prove existence and
detection for every local extension, and it gives no division-place classification. Applying
a theorem for profinite groups to $(F_w,+)$ is invalid because that additive group is
noncompact. Subject to the isolated $({\rm FND}_{\rm PD})$, Lemma 5.0A repairs the root-group
step directly in the locally compact category;
split Moore--Steinberg universality, the wild and even-primary classification, and the entire
division calculation are still exactly $({\rm LOC}_n)$. For division $D^1$, only the formal
Bockstein sequence (5.3d) has been proved.

### 8.5 Projected diagonals do not control adelic tails

The cocycle (5.4) has zero restriction to each factor and a nonzero mixed commutator.
Proposition 5.1 identifies all finite-product cross terms with bicharacters of the topological
abelianizations. Proposition 5.1B uses one global quadratic norm-one torus and weak
approximation to kill all of them, including division--division terms, for a finite product
with its **projected** diagonal splitting. It does not put the rational approximants equal to
the identity outside that product. In the full adelic extension, same-factor and cross
commutators in the compact tail remain in the total identity. Removing those terms requires
the coherent compact-tail splitting in $({\rm PROD}_n)$; projected-diagonal vanishing alone
does not solve the embedded-subproduct problem.

### 8.6 Restricted-product normalization and scalar injectivity are extra theorems

Local classes do not automatically assemble to a locally compact extension of a restricted
product. Proposition 5.2 proves pointwise-finite gluing and independence of representatives once
compatible almost-all compact splittings have been supplied. Proposition 5.3 proves the
converse once one homomorphic splitting over the full maximal compact product is supplied; it
does not prove that an arbitrary diagonal-split adelic class has such a splitting. Raw local
restrictions also need not be finitely supported, so they cannot simply be inserted into
(4.1). The missing reciprocity theorem must extract the single character $\chi_n$ of (5.5)
and prove it injective. Books 4--6 give the restricted product of the underlying groups and
scalar reciprocity, but not that compact-tail or extension theorem.

## 9. Source ledger and conclusion

The current repository numbers and titles are the following.

| Current book | What it proves for this problem | What it does not prove |
|---|---|---|
| Book 6, *Global Class Field Theory* | finite arithmetic duality and the scalar isomorphism (4.2), with real Tate terms | a map from quaternionic adelic multipliers to the scalar cokernel |
| Book 24, *Continuous Cohomology of Profinite Groups* | continuous profinite cohomology and Hochschild--Serre transgression used in (3.5) | no use is made of it for Borel or measurable locally compact multiplier theory |
| Book 77, *Quaternion Algebras over Number Fields* | the quadratic-subfield embedding criterion used before (2.8) | exact congruence normal-generation by Cayley words |
| Book 82, *Orders in Quaternion Algebras* | maximal orders, Eichler orders, and radical filtrations | split or division local multiplier classification |
| Book 118, *Shimura Data and Canonical Models in the FLT Cases* | quaternionic strong approximation and integral norm-quadric approximation | exact relative-root generation, ideal commutators, centrality, or the stem property |
| Book 126, *Galois Representations from Weight-Two Shimura-Curve Cohomology* | extraction, continuity, determinant, parity, and good-prime Frobenius for a chosen cohomological packet | congruence kernels, metaplectic duality, and local multiplier theory |
| Book 139, *Ihara Theory and Saturated Degeneracy Maps on Shimura Curves* | (2.1), (3.2), (7.2), the conditional reduction to routed Ihara, and the same scalar endpoint | the six interfaces $({\rm CEN}_\star)$, $({\rm PAIR}_\star)$, $({\rm LOC}_n)$, $({\rm PROD}_n)$, $({\rm SC}_n)$, and $({\rm TOR})$; it also does not prove the proposed $({\rm QRM}_m)$ or $({\rm PA}_m)$ routes |

The catalog assigns Book 138 to *Integral Local Types and Type Lattices* and Book 139 to the
Ihara manuscript. The file labelled 138a has no independent row in `BOOKS.md` or
`BOOK_DEPENDENCIES.md`; it is therefore not a new catalog node or a numbered alias that can
supply a missing source edge. That fact does not make it a rejected or content-free draft.
Book 180a expressly treats 138a as an **honest but noncatalogued interface**: it credits the
proved cohomological, power--commutator, finite-product, normalized-gluing, and scalar
reductions at their stated scope, while retaining the quaternionic
congruence--metaplectic package and Theorems 6.1--7.1 here as conditional.

The rigorous conclusion is still conditional, but the boundary is narrower and exact. The
false root-contraction argument has been replaced by Theorem 2.4, which reduces centrality to
the finite-quotient commutator containment (2.7). Proposition 2.4A reduces it further to
power commutators, the split calculation isolates $({\rm RM}_m)$, and Lemma 2.6 and (2.14)
isolate the proposed quaternionic route $({\rm QRM}_m)$. Theorem 2.5 and the proposed route
$({\rm PA}_m)$ keep the separately formulated stem problem visible without asserting logical
independence. Proposition 3.2B and Theorem 3.3 give the relative compact transgression and
noncircular coefficient isomorphism. Subject to the explicitly isolated
$({\rm FND}_{\rm PD})$, Lemma 5.0A gives the locally compact root splitting. Proposition 5.1B,
Proposition 5.2, and Proposition 5.3 prove respectively projected-diagonal finite-product
cross-term vanishing, normalized gluing, and the converse under a full compact-product
splitting.

What remains for the conditional package is the six-interface ledger in Section 5.5:
$({\rm CEN}_\star)$, $({\rm PAIR}_\star)$, $({\rm LOC}_n)$, $({\rm PROD}_n)$,
$({\rm SC}_n)$, and $({\rm TOR})$ in the required ranges. The unproved
$({\rm QRM}_m)$ and $({\rm PA}_m)$ are possible sufficient routes, not additional necessary
interfaces. In particular, Book 6 identifies the scalar target but does not construct
$\chi_n$ or prove its injectivity. If the separately stated perfect pairing and odd-order
scalar injections are proved, every odd-primary character of every spectator-level
congruence kernel vanishes and Book 139's routed saturated Ihara theorem follows. If the full
all-primary package is proved as well, the congruence kernel over a totally real field has
order at most two.

Until those hypotheses are discharged by new source-closed proofs, no unconditional
rank-two congruence--metaplectic theorem is asserted.
