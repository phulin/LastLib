# Descent and Weak Mordell--Weil for Abelian Varieties

## Contents

1. [The descent problem](#1-the-descent-problem)
   - [Why division points help](#11-why-division-points-help)
   - [Standing hypotheses and notation](#12-standing-hypotheses-and-notation)
   - [Three levels that must be distinguished](#13-three-levels-that-must-be-distinguished)
2. [Isogeny Kummer theory](#2-isogeny-kummer-theory)
   - [The exact sequence of group schemes](#21-the-exact-sequence-of-group-schemes)
   - [The global boundary](#22-the-global-boundary)
   - [Cocycles from division points](#23-cocycles-from-division-points)
   - [The torsor term and the isogeny defect](#24-the-torsor-term-and-the-isogeny-defect)
   - [Functoriality and change of field](#25-functoriality-and-change-of-field)
3. [Coverings and Selmer sets](#3-coverings-and-selmer-sets)
   - [Isogeny coverings](#31-isogeny-coverings)
   - [Twisting the standard covering](#32-twisting-the-standard-covering)
   - [Solubility and Kummer images](#33-solubility-and-kummer-images)
   - [The everywhere locally soluble set](#34-the-everywhere-locally-soluble-set)
4. [Local division](#4-local-division)
   - [Local Kummer maps](#41-local-kummer-maps)
   - [Finiteness over local fields](#42-finiteness-over-local-fields)
   - [Archimedean places](#43-archimedean-places)
   - [Integral Kummer theory at a good place](#44-integral-kummer-theory-at-a-good-place)
   - [The unramified equality](#45-the-unramified-equality)
5. [The global Selmer group](#5-the-global-selmer-group)
   - [Definition and controlling sets](#51-definition-and-controlling-sets)
   - [Finiteness](#52-finiteness)
   - [The Mordell--Weil--Selmer--Tate--Shafarevich sequence](#53-the-mordell--weil--selmer--tate--shafarevich-sequence)
   - [What finiteness does and does not say](#54-what-finiteness-does-and-does-not-say)
6. [Weak Mordell--Weil](#6-weak-mordell--weil)
   - [Finiteness modulo an isogeny](#61-finiteness-modulo-an-isogeny)
   - [Finiteness modulo multiplication](#62-finiteness-modulo-multiplication)
   - [Why this is the algebraic half of Mordell--Weil](#63-why-this-is-the-algebraic-half-of-mordell--weil)
   - [Variants over finite extensions and products](#64-variants-over-finite-extensions-and-products)
7. [Elementary explicit descent](#7-elementary-explicit-descent)
   - [When cohomology becomes arithmetic coordinates](#71-when-cohomology-becomes-arithmetic-coordinates)
   - [Split diagonalizable kernels](#72-split-diagonalizable-kernels)
   - [Local and global coordinate conditions](#73-local-and-global-coordinate-conditions)
   - [A nonsplit character algebra](#74-a-nonsplit-character-algebra)
   - [Relations and the danger of false coordinates](#75-relations-and-the-danger-of-false-coordinates)
8. [Descent by functions](#8-descent-by-functions)
   - [From characters to rational functions](#81-from-characters-to-rational-functions)
   - [Evaluation away from divisors](#82-evaluation-away-from-divisors)
   - [Extending evaluation to every rational point](#83-extending-evaluation-to-every-rational-point)
   - [Compatibility with the Kummer boundary](#84-compatibility-with-the-kummer-boundary)
9. [Finite bad-place data](#9-finite-bad-place-data)
   - [The exceptional set](#91-the-exceptional-set)
   - [Good places require no search](#92-good-places-require-no-search)
   - [Finite precision at nonarchimedean bad places](#93-finite-precision-at-nonarchimedean-bad-places)
   - [Reduction and formal neighborhoods](#94-reduction-and-formal-neighborhoods)
   - [A finite descent protocol](#95-a-finite-descent-protocol)
10. [Composing and comparing descents](#10-composing-and-comparing-descents)
    - [A composition of isogenies](#101-a-composition-of-isogenies)
    - [Maps between Selmer groups](#102-maps-between-selmer-groups)
    - [Restriction and corestriction](#103-restriction-and-corestriction)
    - [Dual isogenies and degree bounds](#104-dual-isogenies-and-degree-bounds)
11. [Guiding examples](#11-guiding-examples)
    - [The multiplicative model](#111-the-multiplicative-model)
    - [Multiplication by two on an elliptic curve](#112-multiplication-by-two-on-an-elliptic-curve)
    - [A rational cyclic isogeny](#113-a-rational-cyclic-isogeny)
    - [Products and reducible kernels](#114-products-and-reducible-kernels)
    - [Why local solubility is not global solubility](#115-why-local-solubility-is-not-global-solubility)
12. [The completed descent package](#12-the-completed-descent-package)
    - [Hypothesis ledger](#121-hypothesis-ledger)
    - [The logical chain](#122-the-logical-chain)
    - [Conclusion](#123-conclusion)

## 1. The descent problem

### 1.1 Why division points help

Let $A$ be an abelian variety over a number field $K$. The group $A(K)$ is defined by polynomial equations, but its group law alone gives no obvious way to list its points. Descent replaces this unbounded problem by a bounded one. Fix an isogeny

$$
\phi:A\longrightarrow B.
$$

For $P\in B(K)$, choose a geometric point $Q\in A(\overline K)$ with $\phi(Q)=P$. The point $Q$ need not be rational, but its failure to be rational is tightly constrained: for every $\sigma\in G_K$,

$$
\sigma Q-Q\in A[\phi]=\ker\phi.
$$

Thus an arbitrary rational point produces a cocycle with values in one finite group. Changing $Q$ changes the cocycle by a coboundary. The infinite group $B(K)$ therefore maps, modulo $\phi A(K)$, into a finite-coefficient cohomology group.

That ambient cohomology group is not usually finite if ramification is allowed everywhere. Nor does every one of its classes come from a rational point. The localizations of a genuine rational point must arise from points of $B(K_v)$ at every place $v$. These local division conditions define the Selmer group. Outside finitely many places they reduce to the uniform condition “unramified,” and restricted global cohomology is finite. This is the entire engine of weak Mordell--Weil.

The argument is simple only after three issues have been settled correctly. The kernel is a finite group scheme, not merely a set of torsion points. The local Kummer image at a good prime must actually be proved equal to unramified cohomology. Finally, finiteness of $A(K)/nA(K)$ is not yet finite generation of $A(K)$: a height is needed to turn the finite quotient into a terminating descent. We develop the algebraic part here and leave that height step to the next stage.

### 1.2 Standing hypotheses and notation

Throughout, $K$ is a number field, $\overline K$ is a fixed algebraic closure, and $G_K=\operatorname{Gal}(\overline K/K)$. A place of $K$ is denoted $v$, its completion by $K_v$, and, at a finite place, its valuation ring and residue field by $\mathcal O_v$ and $k_v$. We choose compatible decomposition groups, but all constructions are independent of those choices up to canonical conjugacy.

The principal datum is an isogeny of abelian varieties

$$
\phi:A\longrightarrow B
$$

of degree $d\geq1$, with finite commutative kernel group scheme $G=A[\phi]$. Since $K$ has characteristic zero, $G$ is finite etale. Consequently its geometric points $G(\overline K)$ form a finite discrete $G_K$-module of order $d$, and fppf and Galois $H^1$ agree. We nevertheless retain the group-scheme notation: it is what extends over valuation rings and explains the integral local condition.

For a field extension $F/K$, write

$$
\delta_{\phi,F}:B(F)/\phi A(F)\longrightarrow H^1(F,G)
$$

for the Kummer map. When $\phi=[n]_A$, we write $A[n]$, $\delta_{n,F}$, and $\operatorname{Sel}_n(A/K)$. Cohomology of $A$ itself means fppf cohomology, or equivalently the Weil--Chatelet group of torsors under the smooth group $A$.

The **Tate--Shafarevich group** is

$$
\Sha(A/K)=\ker\left(H^1(K,A)\longrightarrow\prod_v H^1(K_v,A)\right).
$$

No finiteness assertion about the whole of $\Sha(A/K)$ will be assumed or proved.

### 1.3 Three levels that must be distinguished

Descent moves among three related objects:

$$
\begin{array}{ccc}
B(K)/\phi A(K)&\xrightarrow{\delta_{\phi,K}}&H^1(K,G)\\
\downarrow&&\downarrow\\
\prod_v B(K_v)/\phi A(K_v)&\xrightarrow{\prod\delta_{\phi,v}}&
\prod_vH^1(K_v,G).
\end{array}
$$

The upper-left group contains actual rational points modulo known divisibility. The upper-right group contains finite-kernel torsors, most of which need not be locally soluble. The inverse image of all local Kummer images is the Selmer group. It contains the global Kummer image, and the difference is measured by a finite piece of $\Sha(A/K)$.

These inclusions can be strict:

$$
B(K)/\phi A(K)
\subseteq \operatorname{Sel}^{\phi}(A/K)
\subseteq H^1(K,G).
$$

The first strictness is a failure of the local--global principle for torsors under $A$. The second is the force of local conditions. Treating either inclusion as equality would erase the central arithmetic content of descent.

A basic multiplicative example already exhibits the second strictness. The group $H^1(\mathbf Q,\mu_2)=\mathbf Q^\times/\mathbf Q^{\times2}$ contains the class of every prime number, so it is infinite. Fixing a finite set $S$, the subgroup unramified outside $S$ is generated by $-1$ and the primes in $S$ and is finite. The local conditions are therefore not small cosmetic corrections to an already finite group; they are what force ramification into a finite set.

The first strictness is subtler. A class can be represented by a finite covering with points over $K_v$ for every $v$ but no point over $K$. In that case no local computation has been missed. The obstruction belongs to the global torsor group and survives every completion. Sequence (5.5) will isolate it exactly.

## 2. Isogeny Kummer theory

### 2.1 The exact sequence of group schemes

The geometric input is the quotient theorem for abelian varieties. An isogeny is finite, faithfully flat, and exhibits $B$ as the quotient of $A$ by $G=\ker\phi$. Hence on the fppf site of $\operatorname{Spec}F$, for every extension $F/K$, there is an exact sequence

$$
0\longrightarrow G\longrightarrow A\xrightarrow{\phi}B\longrightarrow0. \tag{2.1}
$$

The last arrow need not be surjective on $F$-points. Exactness says that a point of $B$ lifts after a faithfully flat extension, and its fiber is a $G$-torsor. Over a field of characteristic zero, that fiber is already trivialized by a finite separable extension.

Applying cohomology to (2.1) gives

$$
0\to G(F)\to A(F)\to B(F)
\xrightarrow{\delta_{\phi,F}}H^1(F,G)
\to H^1(F,A)\to H^1(F,B). \tag{2.2}
$$

Exactness at $B(F)$ immediately proves that the boundary factors through an injection

$$
B(F)/\phi A(F)\hookrightarrow H^1(F,G). \tag{2.3}
$$

This is the formal source of every descent map in the book.

### 2.2 The global boundary

The boundary has a concrete geometric meaning. For $P\in B(F)$, form the fiber

$$
X_P=A\times_{B,P}\operatorname{Spec}F.
$$

Translation makes $X_P$ a $G$-torsor. Its class is $\delta_{\phi,F}(P)$. It has an $F$-point exactly when $P=\phi(Q)$ for some $Q\in A(F)$, so the boundary detects precisely the failure of divisibility by $\phi$.

The homomorphism property is also geometric. If $P,P'\in B(F)$, addition on $A$ sends the contracted product $X_P\wedge^G X_{P'}$ to $X_{P+P'}$. Thus

$$
\delta_{\phi,F}(P+P')
=\delta_{\phi,F}(P)+\delta_{\phi,F}(P').
$$

No choice of coordinates or division points is needed for this definition. Coordinates enter later only to calculate the class.

It is useful to verify directly that this construction is compatible with the quotient in the source. If $P'=P+\phi(R)$ for $R\in A(F)$, translation by $R$ gives an isomorphism

$$
X_P\xrightarrow{\sim}X_{P'},
\qquad Q\longmapsto Q+R,
$$

of $G$-torsors. Conversely, an isomorphism between $X_P$ and $X_{P'}$ is translation by some $R\in A(F)$ after one geometric point is chosen, and compatibility with the maps to $B$ forces $P'-P=\phi(R)$. Thus the fibers themselves, not only their cohomology classes, distinguish the cosets in $B(F)/\phi A(F)$.

There are two notions of “fiber” in play. The scheme-theoretic fiber $X_P$ has degree $d$ over $F$ and remains meaningful integrally. The set of its geometric points is a principal homogeneous set under the abstract group $G(\overline F)$. In characteristic zero they contain the same information, but the scheme formulation is the one stable under passage to valuation rings at primes dividing $d$.

### 2.3 Cocycles from division points

Choose $Q\in A(\overline F)$ with $\phi(Q)=P$. Define

$$
c_P(\sigma)=\sigma Q-Q.
$$

Then $c_P(\sigma)\in G(\overline F)$, and

$$
c_P(\sigma\tau)
=\sigma\tau Q-Q
=\sigma(\tau Q-Q)+(\sigma Q-Q)
=\sigma c_P(\tau)+c_P(\sigma).
$$

Thus $c_P$ is a continuous $1$-cocycle. It is continuous because the finite extension over which $Q$ is defined has an open stabilizer. Replacing $Q$ by $Q+T$, $T\in G(\overline F)$, changes $c_P$ by the coboundary $\sigma T-T$. Therefore $[c_P]$ is well defined.

Conversely, $[c_P]=0$ exactly when some choice $Q+T$ is fixed by $G_F$, which is exactly when $P\in\phi A(F)$. This cocycle calculation proves injectivity in (2.3) directly and identifies the cocycle class with the torsor class of $X_P$.

### 2.4 The torsor term and the isogeny defect

Write $\phi_*:H^1(F,A)\to H^1(F,B)$ for extension of structure group. Exactness of (2.2) continues to give

$$
0\longrightarrow B(F)/\phi A(F)
\longrightarrow H^1(F,G)
\longrightarrow H^1(F,A)[\phi]
\longrightarrow0, \tag{2.4}
$$

where

$$
H^1(F,A)[\phi]=\ker\bigl(H^1(F,A)\xrightarrow{\phi_*}H^1(F,B)\bigr).
$$

The notation $[\phi]$ does not mean ordinary integer torsion unless $A=B$ and $\phi=[n]$. It means that the $A$-torsor becomes trivial after its structure group is pushed forward through $\phi$.

To prove surjectivity in (2.4), take an $A$-torsor $X$ whose pushout is trivial as a $B$-torsor. A chosen trivialization of the pushout has a fiber; that fiber is a $G$-torsor mapping to $X$. Changing the trivialization changes the lift by a global Kummer class, exactly as the long exact sequence predicts.

For multiplication, (2.4) becomes the familiar exact sequence

$$
0\longrightarrow A(F)/nA(F)
\longrightarrow H^1(F,A[n])
\longrightarrow H^1(F,A)[n]
\longrightarrow0. \tag{2.5}
$$

One can see the middle arrow without invoking abstract extension of structure group. If $Y$ is a $G$-torsor, form the contracted product

$$
Y\wedge^G A=(Y\times A)/G,
$$

where $T\in G$ acts by $(y,a)\mapsto(y+T,a-T)$. It is an $A$-torsor. Pushing this torsor through $\phi$ makes it trivial because $G$ acts trivially on $B$. The class of $Y\wedge^G A$ is the image of $[Y]$ in (2.4). If it is already trivial as an $A$-torsor, a chosen trivialization recovers a point of $B(F)$ whose division fiber is $Y$.

The short exact sequence (2.4) need not split. A splitting would select, functorially, one finite-kernel lift for every $\phi$-killed $A$-torsor. Such a selection is precisely the kind of global choice that descent is designed to measure. Even when all groups are finite, cardinalities may be multiplied across (2.4), but no canonical decomposition should be inferred.

### 2.5 Functoriality and change of field

Suppose

$$
\begin{array}{ccc}
A&\xrightarrow{\phi}&B\\
\downarrow u&&\downarrow v\\
A'&\xrightarrow{\phi'}&B'
\end{array}
$$

commutes. The induced map $u_G:G\to G'$ carries the fiber of $P$ to the fiber of $v(P)$, so

$$
(u_G)_*\delta_{\phi,F}(P)=\delta_{\phi',F}(v(P)). \tag{2.6}
$$

For an extension $L/F$, pulling back the same fiber gives

$$
\operatorname{res}_{L/F}\delta_{\phi,F}(P)
=\delta_{\phi,L}(P). \tag{2.7}
$$

If $L/F$ is finite separable, corestriction is compatible with the trace map on abelian varieties:

$$
\operatorname{cor}_{L/F}\delta_{\phi,L}(P)
=\delta_{\phi,F}\bigl(\operatorname{Tr}_{L/F}P\bigr), \tag{2.8}
$$

where $\operatorname{Tr}_{L/F}$ is the sum of the conjugates, equivalently the trace obtained from Weil restriction. Both sides are represented by summing conjugate division cocycles.

Here is a proof that does not assume any injectivity after further restriction. Choose representatives $r_1,\ldots,r_m$ with $G_F=\coprod_i r_iG_L$ and a point $Q\in A(\overline F)$ with $\phi(Q)=P$. The standard transfer formula, after reindexing the cosets, is the division cocycle $\sigma\mapsto\sigma Q_0-Q_0$ attached to

$$
Q_0=\sum_{i=1}^m r_iQ,
$$

Indeed, expanding $\sigma Q_0-Q_0$ produces exactly the corestriction sum. Moreover

$$
\phi(Q_0)=\sum_{i=1}^m r_iP=\operatorname{Tr}_{L/F}P.
$$

Thus the transferred class is the division class of the trace. The calculation is independent of the coset representatives up to a coboundary and applies to every finite separable extension. In the Galois case it reduces to the displayed sum over $\operatorname{Gal}(L/F)$; transitivity gives the usual tower formula.

## 3. Coverings and Selmer sets

### 3.1 Isogeny coverings

Cohomology is economical, but a geometric descent calculation usually presents varieties rather than cocycles. A **$\phi$-covering of $B$** over a field $F\supseteq K$ is a triple $(X,\rho,\pi)$ in which $X$ is a torsor under $A$, $\rho$ is the action, and $\pi:X\to B$ satisfies

$$
\pi(x+a)=\pi(x)+\phi(a)
$$

after every field extension. The standard covering is $(A,+,\phi)$. An isomorphism of coverings is an $A$-equivariant isomorphism commuting with the maps to $B$.

Over $\overline F$, every $\phi$-covering is isomorphic to the standard one. Indeed, choose $x\in X(\overline F)$ above $0\in B$. Translation identifies $A_{\overline F}$ with $X_{\overline F}$, and equivariance identifies $\pi$ with $\phi$ after adjusting by an element of $A(\overline F)$. The automorphisms of the standard covering are precisely translations by elements of $G$: translation by $T$ commutes with $\phi$ exactly when $T\in\ker\phi$.

### 3.2 Twisting the standard covering

Forms of an object are classified by cocycles in its automorphism group. Here that statement is elementary enough to prove. Choose an isomorphism

$$
\iota:X_{\overline F}\xrightarrow{\sim}A_{\overline F}
$$

over $B$. For $\sigma\in G_F$, the composite $\iota\,{}^\sigma\!\iota^{-1}$ is translation by a unique $c(\sigma)\in G(\overline F)$. Associativity of descent gives the cocycle identity. Replacing $\iota$ changes $c$ by a coboundary.

Conversely, a cocycle $c$ modifies the ordinary Galois action on $A_{\overline F}$ by

$$
\sigma*x=c(\sigma)+\sigma x.
$$

The cocycle identity makes this an action, and finite Galois descent produces $X$, its $A$-action, and its map to $B$. These constructions are inverse. Therefore

$$
\{\text{isomorphism classes of $\phi$-coverings of $B/F$}\}
\simeq H^1(F,G). \tag{3.1}
$$

Although geometers often call the left side a **Selmer set**, in the present commutative isogeny setting it inherits an abelian group law from $H^1(F,G)$. The set language remains useful because local solubility and rational points are geometric properties of the covering.

The group law has a direct geometric construction. Given coverings $X$ and $Y$, contract $X\times Y$ by the anti-diagonal action $(x,y)\cdot a=(x+a,y-a)$. The resulting torsor is acted on by $A$, and the two maps to $B$ add. After choosing geometric trivializations, its descent cocycle is the sum of the two original cocycles. The inverse covering is obtained by composing the action and the map to $B$ with $[-1]$. Thus the group structure is intrinsic even when individual coverings are presented by unrelated equations.

Twisting also explains why coverings are classified up to isomorphism **over $B$**, not merely by their total spaces. The same variety can carry different maps to $B$, encoding different division problems. The automorphism group relevant to descent is the automorphism group of $A\xrightarrow{\phi}B$, namely $G$, rather than the usually larger automorphism group of $A$ as a variety.

### 3.3 Solubility and Kummer images

Let $X_c$ be the covering attached to $c\in H^1(F,G)$. It has an $F$-point if and only if $c$ lies in the global Kummer image.

To prove this, suppose $x\in X_c(F)$ and put $P=\pi(x)\in B(F)$. Choose a geometric identification with the standard covering carrying $x$ to $Q\in A(\overline F)$. The fact that $x$ is fixed says

$$
c(\sigma)=\sigma Q-Q
$$

up to the fixed sign convention for twisting; hence $c=\delta_{\phi,F}(P)$. Conversely, if $c$ is the division cocycle of $P$, the division point $Q$ becomes fixed for the twisted action and descends to an $F$-point of $X_c$.

Thus the Kummer image is not merely an algebraic subgroup: it is the locus of soluble coverings.

### 3.4 The everywhere locally soluble set

For a number field $K$, call a $\phi$-covering **everywhere locally soluble** if it has a $K_v$-point for every place $v$. By the preceding section this is equivalent to

$$
\operatorname{res}_v(c)\in
\delta_{\phi,v}\bigl(B(K_v)/\phi A(K_v)\bigr)
\quad\text{for every }v. \tag{3.2}
$$

The isomorphism classes satisfying (3.2) form $\operatorname{Sel}^{\phi}(A/K)$. A globally soluble covering is everywhere locally soluble, but the converse can fail. The obstruction is not a defect in the definition: it is exactly the locally trivial torsor term that later appears in $\Sha(A/K)$.

## 4. Local division

### 4.1 Local Kummer maps

For every place $v$, define

$$
\mathcal L_v^\phi
=\operatorname{im}\left(
B(K_v)/\phi A(K_v)\xrightarrow{\delta_{\phi,v}}H^1(K_v,G)
\right). \tag{4.1}
$$

This is a subgroup because all groups are commutative. By exactness,

$$
\mathcal L_v^\phi
=\ker\bigl(H^1(K_v,G)\to H^1(K_v,A)\bigr). \tag{4.2}
$$

Formula (4.2) says that a finite-kernel class is allowed precisely when the associated $A$-torsor is locally trivial. It also shows why replacing the Kummer condition by zero is too strict and replacing it by all of $H^1(K_v,G)$ is usually too relaxed.

### 4.2 Finiteness over local fields

At a nonarchimedean place, $A(K_v)$ and $B(K_v)$ are compact $v$-adic analytic groups because $A$ and $B$ are proper. The derivative

$$
d\phi:\operatorname{Lie}(A)(K_v)\longrightarrow\operatorname{Lie}(B)(K_v)
$$

is an isomorphism. Indeed an isogeny in characteristic zero is etale, so its tangent kernel is zero, and the two Lie spaces have the same dimension. The nonarchimedean inverse function theorem now gives open neighborhoods $U\subset A(K_v)$ and $V\subset B(K_v)$ such that $\phi(U)=V$. Hence $\phi A(K_v)$ is open in $B(K_v)$. An open subgroup of a compact group has finite index, proving

$$
B(K_v)/\phi A(K_v)\quad\text{is finite}. \tag{4.3}
$$

This topological proof also explains effective finite precision: some sufficiently small congruence neighborhood of the identity is already contained in the image.

Local Galois cohomology independently proves that $H^1(K_v,G)$ is finite for every finite $G_K$-module $G$. Thus (4.3) follows from the Kummer injection as well. The analytic proof is more informative because it supplies representatives by a finite quotient of $B(K_v)$.

The openness argument can be made without coordinates on the whole variety. Choose formal parameters $t_1,\ldots,t_g$ at the identity. On a sufficiently small polydisc, the group law is a convergent $g$-tuple of power series, and $\phi$ is a convergent homomorphism with invertible linear term. The inverse function theorem gives an analytic inverse on a smaller polydisc. Translating this local image by elements of $\phi A(K_v)$ shows that the entire image is open. Compactness is used only afterward, to turn openness into finite index.

There is also an exponent bound. A quasi-inverse $\phi':B\to A$ can be chosen with $\phi\phi'=[d]_B$. Hence

$$
dB(K_v)\subseteq\phi A(K_v),
$$

so the local quotient is killed by $d$. This does not bound its order by $d$: a $d$-torsion group may have several generators. The Kummer injection gives the safe bound

$$
|B(K_v)/\phi A(K_v)|\leq |H^1(K_v,G)|.
$$

At good-reduction primes away from $d$, Theorem 4.2 sharpens this to the exact Frobenius count (4.10).

### 4.3 Archimedean places

If $v$ is complex, $G_{K_v}=1$, so $H^1(K_v,G)=0$ and $\mathcal L_v^\phi=0$. Analytically, an isogeny of complex tori is surjective on complex points.

If $v$ is real, $A(\mathbf R)$ and $B(\mathbf R)$ are compact real Lie groups with finitely many connected components. The derivative of $\phi$ is an isomorphism, so the image contains the identity component of $B(\mathbf R)$. Therefore the quotient is a finite quotient of component groups. It is killed by $d$: a quasi-inverse $\psi$ with $\psi\phi=[d]$ gives $[d]B(\mathbf R)\subseteq\phi A(\mathbf R)$. In particular real places can contribute only primes dividing $d$, and for odd $d$ the component groups, which are elementary $2$-groups for real abelian varieties, give no quotient.

### 4.4 Integral Kummer theory at a good place

The decisive uniformity theorem begins with a finite place $v$ at which $A$ and $B$ have good reduction. Thus there are abelian schemes $\mathcal A,\mathcal B$ over $\mathcal O_v$ with generic fibers $A,B$. The extension theorem for homomorphisms of abelian schemes extends $\phi$ uniquely to

$$
\Phi:\mathcal A\longrightarrow\mathcal B.
$$

If $v\nmid d$, then $\Phi$ is an etale isogeny and $\mathcal G=\ker\Phi$ is finite etale over $\mathcal O_v$. Properness gives

$$
\mathcal A(\mathcal O_v)=A(K_v),
\qquad
\mathcal B(\mathcal O_v)=B(K_v). \tag{4.4}
$$

We need one vanishing statement.

**Lemma 4.1.** If $\mathcal C/\mathcal O_v$ is an abelian scheme, then

$$
H^1(\mathcal O_v,\mathcal C)=0.
$$

**Proof.** A $\mathcal C$-torsor $X$ is smooth and proper over $\mathcal O_v$. Its special fiber is a torsor under the abelian variety $\mathcal C_{k_v}$. Lang's theorem gives $X(k_v)\ne\varnothing$. For completeness, the required commutative proper case follows from surjectivity of

$$
x\longmapsto \operatorname{Frob}(x)-x
$$

on $\mathcal C_{k_v}$. Its differential is $-1$, so it is etale and its image is open. It is also proper, so its image is closed. Since $\mathcal C_{k_v}$ is connected, the image is the whole group. A $k_v$-point of the smooth scheme $X$ lifts through the henselian ring $\mathcal O_v$ to an $\mathcal O_v$-point. A torsor with a section is trivial. $\square$

Here is the torsor argument inside Lang's theorem. Choose $x\in X(\overline{k_v})$. There is a unique $a\in\mathcal C(\overline{k_v})$ with $\operatorname{Frob}(x)=x+a$. Surjectivity of the Lang map supplies $b$ with $\operatorname{Frob}(b)-b=-a$. Then $x+b$ is Frobenius-fixed and hence belongs to $X(k_v)$. For an abelian variety the Lang map is proper as well as etale; it is therefore finite, so its image is both open and closed. This fills the only point at which connectedness and finiteness of the residue field enter Lemma 4.1.

Apply fppf cohomology to

$$
0\to\mathcal G\to\mathcal A\xrightarrow{\Phi}\mathcal B\to0.
$$

Using the lemma and (4.4), the integral boundary is an isomorphism

$$
B(K_v)/\phi A(K_v)
\xrightarrow{\sim}H^1(\mathcal O_v,\mathcal G). \tag{4.5}
$$

This is stronger than an injection: every integral $\mathcal G$-torsor arises from dividing an integral point of $\mathcal B$.

### 4.5 The unramified equality

For a finite unramified $G_{K_v}$-module $G$, define

$$
H^1_{\mathrm{ur}}(K_v,G)
=\ker\bigl(H^1(K_v,G)\to H^1(I_v,G)\bigr). \tag{4.6}
$$

Finite etale covers of the henselian DVR $\mathcal O_v$ are equivalent to finite etale covers of its residue field. Passing to torsors gives

$$
H^1(\mathcal O_v,\mathcal G)
\simeq H^1(k_v,\mathcal G_{k_v}). \tag{4.7}
$$

Inflation--restriction for

$$
1\to I_v\to G_{K_v}\to G_{k_v}\to1
$$

identifies the right side of (4.7) with (4.6). Combining (4.5)--(4.7) proves the fundamental good-place theorem:

**Theorem 4.2.** If $A$ and $B$ have good reduction at $v$ and $v\nmid\deg\phi$, then

$$
\mathcal L_v^\phi=H^1_{\mathrm{ur}}(K_v,G). \tag{4.8}
$$

If $F_v$ denotes arithmetic Frobenius on $G$, then

$$
H^1_{\mathrm{ur}}(K_v,G)
\simeq G/(F_v-1)G. \tag{4.9}
$$

Since $G$ is finite, the kernel and cokernel of $F_v-1$ have the same order, and therefore

$$
|\mathcal L_v^\phi|=|G^{F_v}|. \tag{4.10}
$$

The exclusions in Theorem 4.2 are real. At a bad-reduction place there may be component or toric information, and at a place dividing $d$ the integral kernel need not be etale. In either case the Kummer image need not equal the unramified subgroup.

We spell out (4.9), since it is frequently used in computations. A continuous cocycle of $G_{k_v}\simeq\widehat{\mathbf Z}$ is determined by its value $a$ on arithmetic Frobenius. On positive powers it is forced to satisfy

$$
c(F_v^m)=a+F_va+\cdots+F_v^{m-1}a.
$$

Changing $c$ by the coboundary of $b\in G$ changes $a$ by $(F_v-1)b$. Conversely these formulas produce every continuous cocycle after passage to a finite quotient through which the action factors. This proves (4.9). The equality of the kernel and cokernel orders of an endomorphism of a finite group proves (4.10).

For $\phi=[n]$, $G=A[n]$. At a good place $v\nmid n$, the local $n$-descent condition has order

$$
|A[n](k_v)|.
$$

This does not say that every $n$-torsion point is rational over $K_v$; it counts the Frobenius-fixed geometric torsion, equivalently the $n$-torsion in the finite reduction group. The condition is computable from the characteristic polynomial of Frobenius modulo $n$.

## 5. The global Selmer group

### 5.1 Definition and controlling sets

The **$\phi$-Selmer group** is

$$
\operatorname{Sel}^{\phi}(A/K)
=\left\{c\in H^1(K,G):
\operatorname{res}_v(c)\in\mathcal L_v^\phi
\text{ for every }v\right\}. \tag{5.1}
$$

Choose a finite set $S$ containing

* every archimedean place;
* every place dividing $d$;
* every place at which $A$ or $B$ has bad reduction.

The action on $G$ is unramified outside this set. By Theorem 4.2, the local condition outside $S$ is precisely unramified. Hence

$$
\operatorname{Sel}^{\phi}(A/K)
=\ker\left(
H^1(G_{K,S},G)\longrightarrow
\bigoplus_{v\in S}H^1(K_v,G)/\mathcal L_v^\phi
\right). \tag{5.2}
$$

Formula (5.2) is the finite-place form of descent. Infinitely many local tests have collapsed to restricted ramification plus finitely many exceptional tests. Enlarging $S$ does not change the group, provided the unramified condition is imposed at the newly added good places.

Let us justify both directions of (5.2). If $c$ is Selmer, then for $v\notin S$ its localization is a Kummer class and hence is unramified by Theorem 4.2. The restriction of $c$ to every such inertia group is zero. Since the ramification kernel of $G_K\to G_{K,S}$ is the closed normal subgroup generated by these inertia groups, inflation--restriction shows that $c$ comes from a unique element of $H^1(G_{K,S},G)$. Conversely, a class in the right side of (5.2) is unramified outside $S$ by construction, so Theorem 4.2 makes it a Kummer class there; the displayed finite quotient conditions make it Kummer at every $v\in S$. It is therefore Selmer.

This proof also establishes independence of the controlling set. If $S\subset S'$, inflation embeds the old restricted cohomology into the new one as the classes unramified at $S'\setminus S$. Imposing the Kummer condition at those newly listed good places imposes exactly that same unramified requirement. The two kernels are canonically equal inside $H^1(K,G)$.

### 5.2 Finiteness

The group $G$ is finite of order $d$, and $S$ contains all places whose residue characteristic divides $d$. Global finiteness for restricted Galois cohomology therefore gives

$$
H^1(G_{K,S},G)\quad\text{finite}. \tag{5.3}
$$

The Selmer group in (5.2) is a subgroup of (5.3), so it is finite.

This proof is worth separating from local finiteness. Even if every $H^1(K_v,G)$ is finite, the unrestricted global group $H^1(K,G)$ can be infinite because classes may ramify at arbitrarily many primes. The good-place theorem proves that Selmer classes have uniformly bounded ramification; global restricted-cohomology finiteness then finishes the argument.

**Theorem 5.1 (Selmer finiteness).** For every isogeny $\phi:A\to B$ of abelian varieties over a number field,

$$
\operatorname{Sel}^{\phi}(A/K)
$$

is finite.

No polarization hypothesis is required. No reduction hypothesis is imposed globally: bad reduction merely enlarges the finite controlling set.

Although restricted-cohomology finiteness is available as a general theorem, its arithmetic mechanism is important here. Let $L/K$ be the finite Galois extension cut out by the action on $G$. Since $G$ is unramified outside $S$, we have $L\subseteq K_S$. If $S_L$ is the set of places of $L$ above $S$, then $G_{L,S_L}$ is the subgroup of $G_{K,S}$ fixing $L$. Put $\Delta=\operatorname{Gal}(L/K)$. Inflation--restriction gives the five-term fragment

$$
0\to H^1(\Delta,G)
\to H^1(G_{K,S},G)
\to H^1(G_{L,S_L},G)^\Delta
\xrightarrow{\operatorname{tg}}H^2(\Delta,G). \tag{5.4a}
$$

The two finite-group cohomology terms are finite. In the middle-right term the subgroup $G_{L,S_L}$ acts trivially on $G$, so its classes are continuous homomorphisms from the abelianization of $G_{L,S_L}$ to $G$. It therefore suffices for finiteness to show that there are only finitely many abelian extensions of $L$, of exponent dividing the exponent of $G$, unramified outside $S_L$.

Global reciprocity reduces such extensions to finite-exponent quotients of an $S_L$-idele class group. The unramified requirement kills the local unit subgroups outside $S_L$; the surviving valuation data assemble into fractional ideals. After quotienting by principal ideles and by the chosen exponent, they are controlled by the finite $S_L$-class group, while the principal relations are controlled by the finitely generated $S_L$-unit group. Equivalently, after decomposing a constant finite abelian coefficient into cyclic factors and adjoining the necessary roots of unity over one further finite extension unramified outside $S_L$, the exact sequence

$$
0\to\mathcal O_{L,S_L}^\times/\mathcal O_{L,S_L}^{\times n}
\to H^1(G_{L,S_L},\mu_n)
\to\operatorname{Cl}(\mathcal O_{L,S_L})[n]\to0
$$

shows finiteness factor by factor. Taking $\Delta$-invariants and the kernel of the transgression in (5.4a), then adjoining the finite inflation term $H^1(\Delta,G)$, preserves finiteness. This is the arithmetic content behind (5.3): finite coefficients alone are not enough; bounded ramification is the decisive global constraint.

The same proof is an enumeration procedure in the elementary range. Once the splitting field, the finite $\Delta$-action, generators for the $S_L$-unit group, and the relevant $S_L$-class-group torsion are known, one lists the finite group $H^1(G_{L,S_L},G)^\Delta$, computes the finite transgression cocycle, and adjoins the possible inflation classes from $H^1(\Delta,G)$. This gives a finite list for $H^1(G_{K,S},G)$, not merely an order bound. The list is rarely economical because it precedes the local Kummer cuts, but every ambiguity and obstruction in descent from $L$ to $K$ is a calculation in a finite group.

### 5.3 The Mordell--Weil--Selmer--Tate--Shafarevich sequence

Map a Selmer class $c\in H^1(K,G)$ through (2.4) to $H^1(K,A)[\phi]$. At every place, the localization of $c$ lies in the local Kummer image, so its image in $H^1(K_v,A)$ is zero. It therefore lies in $\Sha(A/K)$.

Define

$$
\Sha(A/K)[\phi]
=\ker\bigl(\Sha(A/K)\xrightarrow{\phi_*}\Sha(B/K)\bigr). \tag{5.4}
$$

Then there is an exact sequence

$$
0\longrightarrow B(K)/\phi A(K)
\longrightarrow\operatorname{Sel}^{\phi}(A/K)
\longrightarrow\Sha(A/K)[\phi]
\longrightarrow0. \tag{5.5}
$$

The only nonformal point is surjectivity. Let $\xi\in\Sha(A/K)[\phi]$. By global exactness (2.4), choose a lift $c\in H^1(K,G)$. Since $\xi$ is locally zero, the localization of $c$ lies in the kernel of $H^1(K_v,G)\to H^1(K_v,A)$, which is $\mathcal L_v^\phi$ by (4.2). Thus $c$ is Selmer. Different lifts differ by a global Kummer class, exactly the kernel displayed in (5.5).

For $\phi=[n]_A$, this becomes

$$
0\longrightarrow A(K)/nA(K)
\longrightarrow\operatorname{Sel}_n(A/K)
\longrightarrow\Sha(A/K)[n]
\longrightarrow0. \tag{5.6}
$$

### 5.4 What finiteness does and does not say

Theorem 5.1 and (5.5) prove three finite statements:

$$
B(K)/\phi A(K),\qquad
\operatorname{Sel}^{\phi}(A/K),\qquad
\Sha(A/K)[\phi]
$$

are finite. They do not prove that $A(K)$ is finitely generated, and they do not prove that $\Sha(A/K)$ is finite. The groups $\Sha(A/K)[n]$ are finite one level at a time, while their union over $n$ could still be infinite. Similarly, a group can have finite quotient modulo $n$ without being finitely generated if no height or other descent measure prevents infinite division.

The Selmer group is nevertheless a rigorous finite upper bound:

$$
|B(K)/\phi A(K)|\leq|\operatorname{Sel}^{\phi}(A/K)|.
$$

Its excess over the Mordell--Weil quotient is precisely $|\Sha(A/K)[\phi]|$, not an artifact of the calculation.

## 6. Weak Mordell--Weil

### 6.1 Finiteness modulo an isogeny

The injection in (5.5) and Selmer finiteness immediately give the isogeny form of weak Mordell--Weil.

**Theorem 6.1.** Let $\phi:A\to B$ be an isogeny of abelian varieties over a number field $K$. Then

$$
B(K)/\phi A(K)
$$

is finite.

The theorem includes inseparable-looking integral kernels at primes dividing $d$, because the generic field has characteristic zero and the global kernel is finite etale. Those primes are handled as exceptional local places rather than excluded.

### 6.2 Finiteness modulo multiplication

Taking $A=B$ and $\phi=[n]$ gives:

**Theorem 6.2 (weak Mordell--Weil).** For every abelian variety $A/K$ and every integer $n\geq1$,

$$
A(K)/nA(K)
$$

is finite.

For $n=1$ the statement is tautological. For $n\geq2$, it is the finite injection into $\operatorname{Sel}_n(A/K)$. No choice of a polarization is needed to prove it.

If weak Mordell--Weil is known for one integer $n\geq2$, it follows for every divisor of a power of $n$. Indeed, if $m\mid n^r$, the map $A(K)/n^rA(K)\to A(K)/mA(K)$ is surjective, while repeated exact sequences show $A(K)/n^rA(K)$ finite. The full theorem is cleaner because Kummer descent applies directly to every $m$.

There is a purely group-theoretic reason not to stop here. The additive group $\mathbf Q$ satisfies $\mathbf Q/n\mathbf Q=0$ for every $n$, yet it is not finitely generated. Weak Mordell--Weil rules out infinitely many independent residue classes but does not rule out unlimited divisibility. Rational points on an abelian variety are not expected to behave like $\mathbf Q$, but proving that requires a size function. A canonical height supplies precisely the missing prohibition against endless division.

Torsion is already controlled without heights. The torsion subgroup $A(K)_{\mathrm{tors}}$ injects into $A[n](\overline K)$ on its $n$-primary part at each fixed level, but this alone does not bound all levels simultaneously. At a good finite place $v$ of residue characteristic $p$, the kernel $A_1(K_v)$ of reduction has a filtration by formal neighborhoods whose successive quotients are additive groups over $k_v$. It therefore has no torsion of order prime to $p$. Reduction

$$
A(K)_{\mathrm{tors}}\longrightarrow\mathcal A(k_v)
$$

is consequently injective on the prime-to-$p$ part. Choose two good places $v,w$ of distinct residue characteristics $p$ and $q$. If a torsion point reduces to zero at both, its order is a power of $p$ by the first kernel calculation and a power of $q$ by the second, so the point is zero. Hence diagonal reduction embeds

$$
A(K)_{\mathrm{tors}}
\hookrightarrow\mathcal A(k_v)\times\mathcal A(k_w),
$$

a finite group. Thus $A(K)_{\mathrm{tors}}$ is finite. This observation is compatible with weak Mordell--Weil but logically separate from finite generation of the free quotient.

### 6.3 Why this is the algebraic half of Mordell--Weil

Choose representatives $P_1,\ldots,P_r$ for the finite quotient $A(K)/nA(K)$. Every $P\in A(K)$ can be written

$$
P=P_i+nQ.
$$

This is a descent step, but it is not yet a terminating algorithm: $Q$ may be as complicated as $P$. A height $h$ with

$$
h(nQ)=n^2h(Q)+O(1)
$$

makes $Q$ strictly smaller when $P$ is large. Repetition then reaches a bounded-height set, and Northcott finiteness makes that set finite. Thus weak Mordell--Weil supplies finitely many residue classes, while height theory supplies termination. Keeping these roles separate prevents a circular proof of finite generation.

### 6.4 Variants over finite extensions and products

For every finite extension $L/K$, the same theorem applied over $L$ gives $A(L)/nA(L)$ finite. Restriction carries the quotient over $K$ to that over $L$, while trace carries it back and satisfies

$$
\operatorname{Tr}_{L/K}\circ\operatorname{res}=[L:K].
$$

For a product $A=A_1\times A_2$,

$$
A(K)/nA(K)
\simeq A_1(K)/nA_1(K)\times A_2(K)/nA_2(K).
$$

The product statement follows either directly or from the product decomposition of $A[n]$ and cohomology. Isogeny invariance is also immediate: if $A$ and $B$ are isogenous, weak Mordell--Weil holds for both, independently of which representative of the isogeny class is chosen.

## 7. Elementary explicit descent

### 7.1 When cohomology becomes arithmetic coordinates

The cohomological definition is canonical but not automatically computational. An explicit descent requires a description of $H^1(K,G)$ by elements of finite extensions modulo powers, together with equations cutting out the image of $G$. The cleanest range is when the kernel is diagonalizable and split.

Let the exponent of $G$ divide $n$. Its Cartier dual $G^D$ is the finite group of characters $G\to\mathbf G_m$. Characters separate geometric points, so evaluation gives a closed immersion after a splitting extension:

$$
G\longrightarrow\prod_{\chi\in X}\mu_n,
\qquad g\longmapsto(\chi(g))_\chi, \tag{7.1}
$$

where a generating set $X\subseteq G^D$ suffices. Relations among the characters become multiplicative equations among the coordinates. Descent is explicit only when those relations and the resulting cohomological quotient are retained.

### 7.2 Split diagonalizable kernels

Assume

$$
G\simeq\mu_{n_1}\times\cdots\times\mu_{n_r}
$$

over $K$. Since $K$ has characteristic zero, Kummer theory gives

$$
H^1(K,G)
\simeq\prod_{i=1}^rK^\times/K^{\times n_i}. \tag{7.2}
$$

Under chosen coordinates, the isogeny boundary becomes a homomorphism

$$
\alpha_\phi:B(K)/\phi A(K)
\longrightarrow\prod_{i=1}^rK^\times/K^{\times n_i}. \tag{7.3}
$$

It is injective because it is the Kummer boundary followed by the isomorphism (7.2). Different choices of a basis of $G^D$ change (7.3) by the corresponding integral change of multiplicative coordinates; they do not change the Selmer group.

The hypothesis is restrictive but important. For example, if $G\simeq\mu_n$, one element of $K^\times/K^{\times n}$ records the entire covering. If $G$ is constant cyclic but $K$ does not contain $\mu_n$, its cohomology is a character group rather than $K^\times/K^{\times n}$; identifying the two would be false.

The isomorphism (7.2) is not merely a count of geometric characters. It is obtained by applying fppf cohomology to each exact sequence

$$
1\to\mu_{n_i}\to\mathbf G_m
\xrightarrow{(\cdot)^{n_i}}\mathbf G_m\to1
$$

and using $H^1(K,\mathbf G_m)=0$. It remains valid when a completion has residue characteristic dividing $n_i$, because the field itself has characteristic zero. The integral model of $\mu_{n_i}$ may then be non-etale, which affects the local image but not the generic Kummer coordinate.

Suppose $e_1,\ldots,e_r$ is the chosen basis of $G^D$ and $c$ is a $G$-valued cocycle. Its $i$th coordinate is the cocycle $e_i\circ c$ in $\mu_{n_i}$. Choose $u_i\in\overline K^\times$ with

$$
\frac{\sigma u_i}{u_i}=e_i(c(\sigma)).
$$

Then $u_i^{n_i}\in K^\times$, and its power class is the $i$th entry in (7.2). Conversely, given $a_i\in K^\times$, choose roots $u_i^{n_i}=a_i$; the root cocycles assemble, through the inverse of the chosen kernel decomposition, to a $G$-cocycle. These constructions prove surjectivity and show concretely how a covering field is generated by finitely many radicals.

A different character basis acts by monomials. If

$$
e'_j=\prod_i e_i^{m_{ji}},
$$

then the new coordinate is represented by $\prod_i a_i^{m_{ji}}$, with exponents interpreted in the appropriate cyclic groups. Hence a basis change never alters local solubility; it merely changes the finite system of power-class equations used to express it.

### 7.3 Local and global coordinate conditions

In the split situation, choose a controlling set $S$. An element of the ambient restricted group has coordinates represented by $a_i\in K^\times$ whose valuations outside $S$ satisfy

$$
v(a_i)\equiv0\pmod{n_i}. \tag{7.4}
$$

For each coordinate there is an exact sequence

$$
0\to\mathcal O_{K,S}^\times/\mathcal O_{K,S}^{\times n_i}
\to H^1(G_{K,S},\mu_{n_i})
\to\operatorname{Cl}(\mathcal O_{K,S})[n_i]\to0. \tag{7.5}
$$

Dirichlet's unit theorem and finiteness of the $S$-class group make (7.5) a finite arithmetic object. The Selmer group is obtained by imposing, at each $v\in S$, that $(a_i)$ lie in the image of the local descent map

$$
B(K_v)/\phi A(K_v)
\longrightarrow\prod_iK_v^\times/K_v^{\times n_i}. \tag{7.6}
$$

Thus elementary descent consists of finite linear algebra in finitely generated power-class groups, plus finitely many local image tests. When the $n_i$ are prime, these are vector spaces over finite fields.

The valuation condition alone does not force a coordinate to be an $S$-unit modulo powers. If all valuations outside $S$ are divisible by $n_i$, the fractional ideal generated by $a_i$ outside $S$ is an $n_i$th power of an ideal. That ideal need not be principal; its class is the right-hand term of (7.5). Only after the class-group obstruction vanishes can one multiply $a_i$ by an $n_i$th power and obtain an $S$-unit. This is why an explicit descent that enumerates only $S$-units can miss classes whenever the $S$-class group has relevant torsion.

At a finite place $v\notin S$, write $a_i=\pi_v^{n_i m}u$. Removing the power of the uniformizer leaves a unit $u$. Since $n_i$ is prime to the residue characteristic, the principal-unit group is uniquely $n_i$-divisible, and the unit power class is determined by its residue in $k_v^\times/k_v^{\times n_i}$. This is precisely the Frobenius quotient in (4.9), expressed multiplicatively. Thus the valuation and cohomological descriptions of the good-place condition agree term by term.

### 7.4 A nonsplit character algebra

The split hypothesis can be weakened without pretending that all characters are rational. Let $X=G^D(\overline K)$, regarded as a finite $G_K$-set with its group structure, and form the finite etale algebra

$$
L=\operatorname{Map}_{G_K}(X,\overline K).
$$

After base change to $\overline K$, the restriction of scalars $R_{L/K}\mu_n$ is a product of copies of $\mu_n$ indexed by $X$. Evaluation gives

$$
G\longrightarrow R_{L/K}\mu_n. \tag{7.7}
$$

Shapiro's lemma and Kummer theory identify

$$
H^1(K,R_{L/K}\mu_n)\simeq L^\times/L^{\times n}. \tag{7.8}
$$

The image of a $G$-class in (7.8) is a Galois-compatible package of character evaluations. Norm maps between the field factors express relations in $X$. This étale-algebra language keeps conjugate descent functions together and avoids choosing a splitting field in the final answer.

### 7.5 Relations and the danger of false coordinates

The map (7.7) need not induce an injection on $H^1$. If $Q$ is its cokernel as an fppf sheaf, the long exact sequence begins

$$
Q(K)\longrightarrow H^1(K,G)
\longrightarrow L^\times/L^{\times n}
\longrightarrow H^1(K,Q). \tag{7.9}
$$

Consequently two $G$-torsors can have the same raw character coordinates if they differ by the boundary of a $K$-point of $Q$. A correct nonsplit explicit descent must either quotient by this boundary or choose a character resolution for which the ambiguity is separately controlled. Likewise, not every element of $L^\times/L^{\times n}$ comes from $H^1(K,G)$; it must satisfy the obstruction on the right of (7.9).

This is why the “elementary range” is stated honestly. In the split diagonalizable case (7.2) is an isomorphism and no hidden relation remains. In a general character-algebra calculation, relation and obstruction groups are indispensable parts of the descent data.

## 8. Descent by functions

### 8.1 From characters to rational functions

Arithmetic coordinates are often produced by evaluating rational functions on $B$. We explain the geometric source and the hypothesis needed for the construction.

Let $\chi:G\to\mu_n$ be a $K$-rational character. The perfect kernel pairing identifies $G^D$ with $\ker(\phi^\vee)$. Thus $\chi$ determines an algebraically trivial line bundle class $L_\chi$ on $B$ whose pullback to $A$ is trivial. Choose a divisor $D_\chi$ representing $L_\chi$ and a rational trivialization of $\phi^*L_\chi$. It is represented by a rational function $f_\chi$ on $A$ satisfying

$$
\operatorname{div}(f_\chi)=\phi^*D_\chi. \tag{8.1}
$$

Translation by $T\in G$ preserves the divisor on the right, so

$$
\frac{f_\chi(x+T)}{f_\chi(x)}
$$

is constant in $x$. With compatible normalization that constant is $\chi(T)$. This identity is the function-theoretic shadow of the character pairing.

Now let $P\in B(K)$ and choose $Q\in A(\overline K)$ with $\phi(Q)=P$, initially away from the zero and pole divisor of $f_\chi$. Since $\chi$ takes values in $\mu_n$, the element

$$
a_\chi(P)=f_\chi(Q)^n \tag{8.1a}
$$

is fixed by $G_K$: applying $\sigma$ changes $f_\chi(Q)$ by $\chi(\sigma Q-Q)$, whose $n$th power is one. Replacing $Q$ by $Q+T$ has the same effect, so (8.1a) is independent of the division point. Multiplying $f_\chi$ by a constant $c\in K^\times$ multiplies $a_\chi(P)$ by $c^n$. Hence

$$
P\longmapsto a_\chi(P)\bmod K^{\times n} \tag{8.1b}
$$

is a well-defined character coordinate wherever the displayed evaluation is finite and nonzero. The moving construction below removes that temporary restriction.

There is a second, equivalent presentation more common in multiplication descent. For the character under discussion, put $L=L_\chi$; it is killed by $n$. Because a $K$-point of the rigidified dual represents an actual line bundle over $K$, a nonzero rational section gives a $K$-rational divisor $D$ representing $L$. A chosen trivialization $L^{\otimes n}\simeq\mathcal O_B$ then gives $f\in K(B)^\times$ with

$$
\operatorname{div}(f)=nD. \tag{8.2}
$$

Evaluation of $f$ gives an $n$th-power class. If one starts only with a Galois-stable collection of geometric character classes rather than a $K$-rational character, the individual divisors need not descend separately; they must be retained as a conjugate tuple in the étale algebra of Section 7.4.

With compatible rigidifications, the presentation (8.2) produces the same power class as (8.1b). Indeed, after choosing the two rational trivializations there is a constant $c\in K^\times$ such that

$$
f_\chi^n=c\,\phi^*f. \tag{8.2a}
$$

Both sides have divisor $n\phi^*D$. After choosing the rational sections to be nonvanishing at the points in question, evaluate at a division point of $P$ and at the origin, which divides $0$. This gives

$$
\frac{a_\chi(P)}{a_\chi(0)}
=\frac{f(P)}{f(0)}.
$$

The class of $a_\chi(0)=f_\chi(0)^n$ is trivial, so the two formulas define the same element of $K^\times/K^{\times n}$. The constant in (8.2a) cancels; one does not need to assume that it has an $n$th root in $K$. Lemma 8.1 below guarantees the required nonvanishing choices. This is why explicit formulas may look different while defining the same Kummer coordinate.

### 8.2 Evaluation away from divisors

Suppose first that both $P\in B(K)$ and the origin avoid the support of $D$ and the zero and pole divisor of $f$ in (8.2). Evaluate on the degree-zero cycle $[P]-[0]$ and define

$$
\operatorname{ev}_f(P)=\frac{f(P)}{f(0)}\bmod K^{\times n}. \tag{8.3}
$$

The ratio makes the value independent of multiplying $f$ by a nonzero constant. If the rational section representing $D$ is changed by a factor $h$, then $f$ changes by the $n$th power $h^n$; consequently (8.3) changes by $(h(P)/h(0))^n$ and represents the same class. For any degree-zero zero-cycle $z=\sum m_PP$ disjoint from the relevant divisors, define

$$
f(z)=\prod_P N_{K(P)/K}(f(P))^{m_P}. \tag{8.4}
$$

Changing the rational section that represents $D$ multiplies $f$ by an $n$th power, so (8.4) changes by an $n$th power as well. Norms are included because a Galois-stable zero-cycle can contain closed points of degree greater than one. For the descent map on $B(K)$, the only cycle needed is $[P]-[0]$.

### 8.3 Extending evaluation to every rational point

A point can lie on the chosen divisor, so literal substitution into one fixed formula is not a total map. What must be moved is the rational section representing the torsion line bundle; no unproved rational equivalence of zero-cycles is needed.

**Lemma 8.1 (moving a rational section).** Let $X$ be an integral variety over a field, let $L$ be a line bundle on $X$, and let $Z$ be a finite set of closed points. There is a nonzero rational section of $L$ that is regular and nonvanishing at every point of $Z$.

**Proof.** Restrict $L$ to the semilocal scheme whose local rings are the $\mathcal O_{X,z}$ for $z\in Z$. Every rank-one projective module over a semilocal ring is free: choose generators modulo its finitely many maximal ideals and combine them by the Chinese remainder theorem. A generator of this restriction is represented on some open neighborhood of $Z$ by a regular nowhere-zero section. Since $X$ is integral, that section determines a nonzero rational section of $L$. $\square$

Apply the lemma to $X=B$, $L=\mathcal O(D)$, and $Z=\{0,P\}$. Choose a rational section $s$ nonvanishing at both points and let $D_s=\operatorname{div}(s)$. A fixed trivialization $L^{\otimes n}\simeq\mathcal O_B$ sends $s^n$ to a rational function $f_s$ with

$$
\operatorname{div}(f_s)=nD_s.
$$

Define the value at $P$ by $f_s(P)/f_s(0)$ modulo $n$th powers. If $s'=hs$ is another allowed section, then $h$ is regular and nonzero at $0$ and $P$, and

$$
\frac{f_{s'}(P)}{f_{s'}(0)}
=\left(\frac{h(P)}{h(0)}\right)^n
\frac{f_s(P)}{f_s(0)}.
$$

Thus the power class is independent of the move. Changing the power trivialization multiplies both numerator and denominator by the same constant. This defines the descent coordinate at every rational point, including points on the divisor of an initially chosen section. In an étale-algebra presentation the same argument is applied to the conjugate sections simultaneously and the values are returned by the relevant norms.

This moving step is essential. Simply declaring that points on the original divisor may be ignored would leave the descent map partially defined and could discard entire cosets.

### 8.4 Compatibility with the Kummer boundary

Let $Q\in A(\overline K)$ divide $P\in B(K)$ and let $c_P(\sigma)=\sigma Q-Q$. From the translation law for $f_\chi$,

$$
\frac{\sigma f_\chi(Q)}{f_\chi(Q)}
=\frac{f_\chi(\sigma Q)}{f_\chi(Q)}
=\chi(c_P(\sigma)). \tag{8.5}
$$

Thus $f_\chi(Q)$ is a Kummer trivialization whose Galois coboundary is the character pushforward of the division cocycle. Equation (8.5) proves that evaluation by functions agrees with the abstract Kummer boundary under the coordinate identifications of Chapter 7.

More precisely, the Kummer class of $a_\chi(P)=f_\chi(Q)^n$ is represented by

$$
\sigma\longmapsto
\frac{\sigma f_\chi(Q)}{f_\chi(Q)},
$$

which is exactly $\chi(c_P(\sigma))$ by (8.5). The $n$th power in (8.1a) is indispensable: $f_\chi(Q)$ itself usually lies only in a splitting field and is the chosen root that trivializes the power class.

It also proves homomorphy. The abstract boundary is a homomorphism, so any correctly normalized evaluation formula representing it respects addition modulo powers. Apparent extra constants in an unnormalized formula are not harmless: they signal that the trivializations or the value at the origin have not been made compatible.

## 9. Finite bad-place data

### 9.1 The exceptional set

For a fixed isogeny, choose

$$
S=S_\infty\cup S_d\cup S_{\mathrm{bad}}, \tag{9.1}
$$

where $S_d$ contains places dividing $d$ and $S_{\mathrm{bad}}$ contains the bad-reduction places of $A$ or $B$. One may enlarge $S$ to include denominators of chosen descent functions and primes at which a chosen integral presentation is inconvenient.

The finiteness proof uses only that $S$ is finite. An effective descent uses more: it must be possible to enumerate the restricted global classes and decide their membership in every $\mathcal L_v^\phi$ for $v\in S$. The point of this chapter is that all remaining information is genuinely finite.

### 9.2 Good places require no search

At $v\notin S$, Theorem 4.2 gives

$$
\mathcal L_v^\phi=G/(F_v-1)G.
$$

A global class in $H^1(G_{K,S},G)$ is already unramified there, so it automatically passes the local test. One does not enumerate points of $B(K_v)$ at infinitely many places. Frobenius on the finite group $G$ contains the entire local condition.

In explicit Kummer coordinates, the same assertion is the valuation congruence (7.4). Once an $S$-unit or $S$-class representative has been chosen, all valuations outside $S$ are controlled simultaneously.

### 9.3 Finite precision at nonarchimedean bad places

Let $v\in S$ be finite. Because $\phi A(K_v)$ is open in the compact group $B(K_v)$, there exists an open subgroup $U_v\subseteq B(K_v)$ such that

$$
U_v\subseteq\phi A(K_v). \tag{9.2}
$$

Consequently

$$
B(K_v)/\phi A(K_v)
$$

is a quotient of the finite group $B(K_v)/U_v$. Membership in the local image is therefore determined at finite $v$-adic precision.

To make (9.2) quantitative, choose analytic parameters at the identities. On sufficiently small neighborhoods the group laws are convergent formal power series and $\phi$ has the form

$$
\mathbf t\longmapsto M\mathbf t+\text{terms of degree at least two}, \tag{9.3}
$$

where $M=d\phi$ has nonzero determinant. For a precise finite-depth argument, shrink until the formal logarithms converge and give group isomorphisms

$$
\log_A:U_A\xrightarrow{\sim}\Lambda_A,
\qquad
\log_B:U_B\xrightarrow{\sim}\Lambda_B
$$

onto full $\mathcal O_v$-lattices in the two Lie spaces. Functoriality of the formal logarithm gives

$$
\log_B(\phi(x))=M\log_A(x).
$$

After shrinking $U_A$ if necessary, elementary divisors of the invertible $K_v$-linear map $M$ give an effectively computable integer $c_v$ for which

$$
\mathfrak m_v^{c_v}\Lambda_B\subseteq M\Lambda_A.
$$

Consequently the corresponding parameter neighborhood satisfies

$$
B_{c_v}(K_v)\subseteq\phi A(K_v). \tag{9.4}
$$

Here $B_{c_v}$ is the parameter neighborhood with logarithmic coordinates in $\mathfrak m_v^{c_v}\Lambda_B$. The convergence depth and the elementary divisors of $M$ are finite algebraic data. The quotient can therefore be found by reduction to finitely many residue classes on finitely many analytic charts.

### 9.4 Reduction and formal neighborhoods

When good integral models exist but $v\mid d$, reduction still separates the calculation into a finite residue group and a formal group. There are exact rows

$$
0\to A_1(K_v)\to A(K_v)\to\mathcal A(k_v)\to0,
$$

$$
0\to B_1(K_v)\to B(K_v)\to\mathcal B(k_v)\to0,
$$

where $A_1$ and $B_1$ are kernels of reduction. Let $\phi_1:A_1\to B_1$ and $\overline\phi:\mathcal A(k_v)\to\mathcal B(k_v)$ be the induced maps. The snake lemma gives the exact sequence

$$
0\to\ker\phi_1\to\ker\phi\to\ker\overline\phi
\xrightarrow{\partial}\operatorname{coker}\phi_1
\to\operatorname{coker}\phi
\to\operatorname{coker}\overline\phi\to0. \tag{9.5}
$$

Thus the finite residue map, the formal-group cokernel, and the connecting map $\partial$ determine the desired local quotient exactly. On the formal neighborhoods, (9.3) applies. Applying the logarithm argument of (9.4) inside $A_1$ and $B_1$, choose $c$ so deep that $B_c\subseteq\phi A_1$ and put $A_c=\phi_1^{-1}(B_c)$. Then $A_1/A_c$ and $B_1/B_c$ are finite, their induced map has cokernel $\operatorname{coker}\phi_1$, and the same finite quotients determine $\partial$. No infinite formal limit remains.

At bad reduction one may use projective equations and finitely many analytic charts instead of an abelian-scheme special fiber. Compactness gives a finite cover by charts, and openness of the image gives a finite precision on each. No assertion about a smooth proper integral model is then being made.

### 9.5 A finite descent protocol

A complete elementary isogeny descent has the following finite form.

1. Determine $G=A[\phi]$, its Galois action, and a finite controlling set $S$.
2. Enumerate $H^1(G_{K,S},G)$. In split Kummer coordinates, use $S$-units and $S$-class-group torsion; in a nonsplit presentation, retain the character relations and obstruction groups.
3. For each $v\in S$, compute $B(K_v)/\phi A(K_v)$ to a depth justified by (9.4), and map it into $H^1(K_v,G)$.
4. Keep exactly the global classes whose localizations belong to those finite images.

The survivors are $\operatorname{Sel}^{\phi}(A/K)$. Finding which survivors are globally soluble is a separate problem; the unsuccessful locally soluble coverings represent $\Sha(A/K)[\phi]$. Thus descent gives effective control of all finite bad-place data without promising an automatic solution of the global rational-point problem.

Let us make the finiteness assertions in this protocol precise. In Step 2, a finite presentation of the $S$-unit group modulo the relevant exponents and the finite torsion subgroup of the $S$-class group gives a finite list. If a splitting extension is used, the Galois invariance and character relations are equations in finite groups, so they are decidable by enumeration. In Step 3, (9.4) replaces the compact infinite group $B(K_v)$ by finitely many residue classes. Evaluating the cocycle or descent functions on one lift of each class produces the local image. Finally, localization of each global candidate is a homomorphism between finite groups. No limiting test remains.

One can often reduce the list further before any exceptional local calculation. Character relations impose norm equations in the étale algebra, and the product formula imposes dependencies among valuations. At good places, Frobenius may make $G/(F_v-1)G$ trivial; then the localization is forced to vanish. These reductions do not change the mathematical definition of the Selmer group. They simply compute the same finite kernel in a more economical order.

Effectivity depends on the input model. If $A$, $B$, and $\phi$ are given only abstractly, the theorem proves finiteness but does not manufacture equations. If projective equations, the group law, the isogeny, and the relevant number-field arithmetic are given, all finite objects above can in principle be determined. This distinction separates an effective mathematical reduction from an unsupported claim about the speed of a particular calculation.

## 10. Composing and comparing descents

### 10.1 A composition of isogenies

Let

$$
A\xrightarrow{\phi}B\xrightarrow{\psi}C
$$

be isogenies. Their kernels fit into an exact sequence

$$
0\longrightarrow A[\phi]
\longrightarrow A[\psi\phi]
\xrightarrow{\phi}B[\psi]
\longrightarrow0. \tag{10.1}
$$

Surjectivity on the right is fppf-local: lift an element of $B[\psi]$ through $A\to B$; every lift is killed by $\psi\phi$. Taking cohomology gives a comparison among the three ambient descent groups, with degree-zero and degree-two correction terms. In particular, one must not assert a short exact sequence of Selmer groups merely from (10.1).

On rational points there is an elementary short exact sequence

$$
0\longrightarrow
\frac{B(K)}{\phi A(K)+B(K)[\psi]}
\xrightarrow{\ \psi\ }
\frac{C(K)}{\psi\phi A(K)}
\longrightarrow
\frac{C(K)}{\psi B(K)}
\longrightarrow0. \tag{10.2a}
$$

The middle-to-right arrow is the evident quotient map and is surjective. Its kernel is $\psi B(K)/\psi\phi A(K)$. The map $\psi:B(K)\to\psi B(K)$ has kernel $B(K)[\psi]$, so the first isomorphism theorem identifies this kernel with the left term of (10.2a). This proves exactness.

Thus a $(\psi\phi)$-division problem can be solved first modulo $\psi$ and then modulo $\phi$, but the first-stage ambiguity $B(K)[\psi]$ must be divided out. On cohomology, the connecting map of (10.1) supplies the analogous compatibility obstruction. Successive Selmer descents therefore require both the rational torsion correction in (10.2a) and the local lifting conditions; multiplying two Selmer orders without these corrections is unjustified.

### 10.2 Maps between Selmer groups

A morphism $f:G\to G'$ of kernel modules induces a map of Selmer groups only when it carries every local Kummer condition into the chosen condition for $G'$. Commutative diagrams of isogenies guarantee this by (2.6). Under that hypothesis,

$$
f_*:\operatorname{Sel}^{\phi}(A/K)
\longrightarrow\operatorname{Sel}^{\phi'}(A'/K)
$$

is well defined.

For an exact sequence of kernels, local Kummer conditions may fail to be cartesian: a local class can lift cohomologically without lifting from a local rational point. Therefore kernels and cokernels of maps between Selmer groups contain explicit local defects. The safe procedure is to write the global and local long exact sequences, form the commutative localization diagram, and take the actual kernel. Surjectivity is never inferred merely from surjectivity of coefficient group schemes.

### 10.3 Restriction and corestriction

Let $L/K$ be finite. Restriction sends a Selmer class over $K$ to one over $L$, because a locally soluble covering remains locally soluble after scalar extension. Thus

$$
\operatorname{res}_{L/K}:
\operatorname{Sel}^{\phi}(A/K)
\longrightarrow\operatorname{Sel}^{\phi}(A/L). \tag{10.2}
$$

Corestriction also preserves Kummer conditions when combined with the local trace maps, by (2.8). Summing over places $w\mid v$ gives

$$
\operatorname{cor}_{L/K}:
\operatorname{Sel}^{\phi}(A/L)
\longrightarrow\operatorname{Sel}^{\phi}(A/K). \tag{10.3}
$$

The composite is multiplication by $[L:K]$ on cohomology. Hence if $[L:K]$ is prime to the exponent of $G$, restriction is injective: corestriction supplies an inverse up to an invertible scalar. If the degrees are not coprime, restriction can have a nontrivial kernel.

### 10.4 Dual isogenies and degree bounds

An isogeny $\phi:A\to B$ of degree $d$ has a quasi-inverse $\phi':B\to A$ with

$$
\phi'\phi=[d]_A,
\qquad
\phi\phi'=[d]_B. \tag{10.4}
$$

Thus $G$ is killed by $d$, every $\phi$-Selmer class has exponent dividing $d$, and every local quotient $B(K_v)/\phi A(K_v)$ is killed by $d$. The dual isogeny has Cartier-dual kernel. A polarization can identify this dual kernel with a character dual and thereby turn local Tate pairings into orthogonality statements, but perfect local or global duality is not needed for Selmer finiteness or weak Mordell--Weil.

Equation (10.4) also compares descent levels. Since $[d]$ factors through $\phi$, there is a natural surjection

$$
A(K)/dA(K)\longrightarrow A(K)/\phi'B(K)
$$

and analogous finite comparisons on $B(K)$. These bounds are often enough to transfer finite-index information between isogenous varieties.

## 11. Guiding examples

### 11.1 The multiplicative model

The group $\mathbf G_m$ is not an abelian variety because it is not proper, but its Kummer theory is the exact model for all descent boundaries. Multiplication by $n$ gives

$$
K^\times/K^{\times n}\simeq H^1(K,\mu_n).
$$

Restricted ramification says $v(a)\equiv0\pmod n$ outside $S$, and the global restricted group sits in

$$
0\to\mathcal O_{K,S}^\times/\mathcal O_{K,S}^{\times n}
\to H^1(G_{K,S},\mu_n)
\to\operatorname{Cl}(\mathcal O_{K,S})[n]\to0.
$$

The analogy explains why units and class groups appear in explicit abelian descent. Properness adds the important local fact that $A(K_v)$ is compact, making every isogeny quotient finite; for $K_v^\times$, the valuation direction must instead be handled separately.

The local contrast is instructive. For $(n,p)=1$,

$$
K_v^\times/K_v^{\times n}
\simeq \mathbf Z/n\mathbf Z
\oplus k_v^\times/k_v^{\times n}.
$$

The valuation summand is ramified and the residue-unit summand is unramified. For an abelian variety with good reduction, properness removes the free valuation direction from the group of points. Its entire local Kummer image is the finite unramified group $A[n]/(F_v-1)A[n]$. This is the geometric reason that the good-place theorem for abelian varieties is cleaner than unrestricted multiplicative Kummer theory.

### 11.2 Multiplication by two on an elliptic curve

Let

$$
E:y^2=(x-e_1)(x-e_2)(x-e_3)
$$

with distinct $e_i\in K$. The full two-torsion is rational, and

$$
E[2]\simeq\mu_2^2
$$

after choosing two independent characters. For a point $P=(x,y)$ away from the two-torsion, the three quantities

$$
x-e_1,\qquad x-e_2,\qquad x-e_3
$$

have product $y^2$. Their square classes therefore satisfy one relation, and any two give coordinates in

$$
(K^\times/K^{\times2})^2\simeq H^1(K,E[2]).
$$

At $P=(e_i,0)$ literal evaluation has a zero. Moving divisors, or taking the limiting expression furnished by the tangent line, defines the same Kummer class. This is a concrete instance of Chapter 8 rather than an exception to the descent map.

A controlling set contains the places above $2$, the bad-reduction primes, and infinity. Outside it, each coordinate has even valuation. The $2$-Selmer group is the finite set of pairs of $S$-square classes satisfying the relation and lying in the local images at the exceptional places. The exact sequence

$$
0\to E(K)/2E(K)\to\operatorname{Sel}_2(E/K)\to\Sha(E/K)[2]\to0
$$

explains why a locally soluble intersection of quadrics arising from a surviving pair need not contain a rational point.

The relation among three square classes deserves a direct check. Let $Q=(u,v)$ satisfy $2Q=P$. The tangent line at $Q$ meets $E$ once more, and the chord--tangent law expresses the functions $x-e_i$ at $P$ as squares times constants determined by the two-torsion characters. Galois conjugation of $Q$ by a point $(e_i,0)$ changes the sign of the corresponding square root. Hence the square-root cocycles of $x(P)-e_i$ are exactly the three nonzero characters of the $E[2]$-division cocycle. Their product is the square $y(P)^2$, so only two are independent. This recovers the abstract character calculation without assuming the coordinate formula in advance.

At a two-torsion point $P=(e_i,0)$, one replaces the vanishing factor by the product of the other two differences, or equivalently evaluates a rationally equivalent moved divisor. For example, the tangent parameter shows that the missing square class is represented, up to the fixed normalization, by $(e_i-e_j)(e_i-e_k)$. This value is not obtained by declaring zero to be a square class; it is obtained from the total Kummer map.

### 11.3 A rational cyclic isogeny

Let $E/K$ have a $K$-rational cyclic isogeny $\phi:E\to E'$ of prime degree $\ell$. If $E[\phi]\simeq\mu_\ell$ as a group scheme, then

$$
H^1(K,E[\phi])\simeq K^\times/K^{\times\ell},
$$

and one descent function suffices. If instead $E[\phi]\simeq\mathbf Z/\ell\mathbf Z$ and $\mu_\ell\not\subset K$, the ambient group is

$$
\operatorname{Hom}_{\mathrm{cts}}(G_K,\mathbf Z/\ell\mathbf Z),
$$

not $K^\times/K^{\times\ell}$. Cartier duality exchanges these two kernel types under the dual isogeny. Passing to $K(\mu_\ell)$ permits Kummer coordinates, but descent back to $K$ imposes a Galois eigenspace condition. This example shows exactly why kernel type and roots of unity cannot be suppressed.

At a good prime $v\nmid\ell$, the local image is unramified and has order $|E[\phi]^{F_v}|$. At $v\mid\ell$, formal-group precision determines the extra local condition. Thus even the simplest prime-isogeny descent exhibits the general good-place/bad-place division.

### 11.4 Products and reducible kernels

Let $A=E_1\times E_2$ and take $\phi=[n]_{E_1}\times\psi$ for an isogeny $\psi:E_2\to E_2'$. Then

$$
A[\phi]=E_1[n]\times E_2[\psi]
$$

and

$$
\operatorname{Sel}^{\phi}(A/K)
\simeq\operatorname{Sel}_n(E_1/K)
\times\operatorname{Sel}^{\psi}(E_2/K).
$$

The equality follows because global cohomology, local Kummer maps, and their kernels all commute with finite products. This example is a useful check on every definition: any proposed Selmer construction that does not factor this way has lost either the product structure of the coefficient or the product structure of the local condition.

For a nonsplit extension of kernel modules, no such product formula is available. The connecting map in the coefficient long exact sequence records the obstruction to splitting a descent class into components.

### 11.5 Why local solubility is not global solubility

Suppose $c\in\operatorname{Sel}^{\phi}(A/K)$. The associated covering $X_c$ has a point over every $K_v$. Choosing these local points does not produce compatible coordinates in one number field; there are infinitely many completions and no general gluing theorem for rational points on a proper variety. The image of $c$ in $H^1(K,A)$ is a torsor that is locally trivial everywhere, hence a class of $\Sha(A/K)$.

It vanishes exactly when $X_c(K)\ne\varnothing$, equivalently when $c$ comes from $B(K)/\phi A(K)$. Therefore the quotient of the Selmer group by global Kummer classes measures a genuine local--global failure. Descent narrows the search to finitely many coverings; it does not decree that every locally soluble covering is soluble.

## 12. The completed descent package

### 12.1 Hypothesis ledger

The main conclusions and their precise inputs are summarized below.

| Statement | Hypotheses | Decisive reason |
|---|---|---|
| $G=A[\phi]$ is a finite Galois module | $\phi$ an isogeny over a characteristic-zero field | the kernel is finite etale |
| $B(F)/\phi A(F)\hookrightarrow H^1(F,G)$ | any field extension $F/K$ | fppf exactness of the isogeny sequence |
| $B(K_v)/\phi A(K_v)$ is finite | $v$ any place | compact Lie group and open isogeny image |
| local Kummer image equals unramified cohomology | good reduction and $v\nmid\deg\phi$ | integral Kummer theory and Lang's theorem |
| $\operatorname{Sel}^{\phi}(A/K)$ is finite | $K$ a number field | restricted global cohomology of a finite module |
| $B(K)/\phi A(K)$ is finite | same | injection into the Selmer group |
| $A(K)/nA(K)$ is finite | $n\geq1$ | multiplication isogeny |
| $H^1(K,G)$ is a product of power-class groups | $G$ split diagonalizable | fppf Kummer theory coordinatewise |
| finite bad-place computation | fixed isogeny and finite controlling set | openness gives finite local precision |

The good-place statement does not extend automatically to $v\mid d$ or bad reduction. The power-class description does not extend automatically to constant or nonsplit kernels. Weak Mordell--Weil does not, by itself, imply finite generation. Each boundary corresponds to a real mathematical obstruction.

### 12.2 The logical chain

The descent argument can now be read without hidden steps:

$$
\begin{array}{c}
0\to G\to A\xrightarrow{\phi}B\to0\\
\Downarrow\\
B(K)/\phi A(K)\hookrightarrow H^1(K,G)\\
\Downarrow\ \text{localize}\\
\operatorname{Sel}^{\phi}(A/K)
=\ker\!\left(H^1(G_{K,S},G)\to
\displaystyle\bigoplus_{v\in S}H^1(K_v,G)/\mathcal L_v^\phi\right)\\
\Downarrow\ \text{restricted-cohomology finiteness}\\
B(K)/\phi A(K)\ \text{is finite}.
\end{array}
$$

The vertical passage to $G_{K,S}$ is justified by the integral good-place theorem, not by wishful removal of infinitely many local conditions. The last implication uses an injection, not an equality: the finite difference is $\Sha(A/K)[\phi]$. In explicit descent, character coordinates, $S$-units, class groups, and finite local images make every object in the middle row finite and accessible.

### 12.3 Conclusion

Kummer descent converts division on an abelian variety into torsors under a finite isogeny kernel. The conversion is exact: rational points modulo the isogeny inject into finite-kernel cohomology, locally soluble coverings form the Selmer group, and the remaining gap is precisely the isogeny-torsion in the Tate--Shafarevich group. At good primes away from the isogeny degree, integral extension and Lang's theorem identify the local Kummer image with unramified cohomology. This equality confines every Selmer class to one restricted global cohomology group, whose finiteness proves Selmer finiteness and weak Mordell--Weil.

The theory is also calculational in its honest elementary range. Split character kernels yield power-class coordinates; nonsplit kernels yield finite étale character algebras with explicit relation and obstruction terms. $S$-units and $S$-class groups enumerate the global candidates, while compactness and the local inverse function theorem reduce every exceptional local image to finite precision. Descent by rational functions agrees with the intrinsic Kummer boundary once divisors are moved and character normalizations are respected.

The resulting package is exactly the algebraic foundation needed for the Mordell--Weil theorem. It supplies finitely many classes modulo multiplication and explains all local and global defects. What it deliberately does not supply is termination of repeated division. A quadratic height and Northcott finiteness provide that final step; the present descent theory ensures that, when height enters, only finitely many residue classes remain to be controlled.
