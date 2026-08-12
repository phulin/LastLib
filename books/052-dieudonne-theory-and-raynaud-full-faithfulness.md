# Dieudonné Theory and Raynaud Full Faithfulness

## Contents

1. [From a finite group to linear arithmetic](#1-from-a-finite-group-to-linear-arithmetic)
   - [The two classification problems](#11-the-two-classification-problems)
   - [Standing conventions](#12-standing-conventions)
   - [The route through the book](#13-the-route-through-the-book)
2. [Witt vectors and the Dieudonné ring](#2-witt-vectors-and-the-dieudonné-ring)
   - [Why Witt vectors are the coefficient ring](#21-why-witt-vectors-are-the-coefficient-ring)
   - [Frobenius and Verschiebung](#22-frobenius-and-verschiebung)
   - [The noncommutative operator ring](#23-the-noncommutative-operator-ring)
3. [The finite Dieudonné module of a group](#3-the-finite-dieudonné-module-of-a-group)
   - [Witt covectors and the definition](#31-witt-covectors-and-the-definition)
   - [Exactness and length](#32-exactness-and-length)
   - [The three groups of order $p$](#33-the-three-groups-of-order-p)
4. [The finite-level classification theorem](#4-the-finite-level-classification-theorem)
   - [The fundamental extension calculation](#41-the-fundamental-extension-calculation)
   - [Full faithfulness](#42-full-faithfulness)
   - [Essential surjectivity](#43-essential-surjectivity)
   - [The anti-equivalence](#44-the-anti-equivalence)
5. [Reading geometry from operators](#5-reading-geometry-from-operators)
   - [Connected and étale directions](#51-connected-and-étale-directions)
   - [Multiplicative and local-local directions](#52-multiplicative-and-local-local-directions)
   - [Cartier duality](#53-cartier-duality)
   - [Functorial decompositions](#54-functorial-decompositions)
6. [Finite levels and truncated Barsotti--Tate objects](#6-finite-levels-and-truncated-barsotti--tate-objects)
   - [Truncation by $p^n$](#61-truncation-by-pn)
   - [Level one](#62-level-one)
   - [Liftable higher levels](#63-liftable-higher-levels)
   - [Exact sequences and filtrations](#64-exact-sequences-and-filtrations)
7. [Connected objects in height two](#7-connected-objects-in-height-two)
   - [The local-local plane](#71-the-local-local-plane)
   - [Ordinary and supersingular elliptic $p$-torsion](#72-ordinary-and-supersingular-elliptic-p-torsion)
   - [Polarized modules](#73-polarized-modules)
8. [The crystalline Dieudonné crystal](#8-the-crystalline-dieudonné-crystal)
   - [Why one evaluation is not enough](#81-why-one-evaluation-is-not-enough)
   - [Construction on divided-power thickenings](#82-construction-on-divided-power-thickenings)
   - [Exactness, base change, and duality](#83-exactness-base-change-and-duality)
9. [Torsion in abelian schemes](#9-torsion-in-abelian-schemes)
   - [The comparison problem](#91-the-comparison-problem)
   - [The finite-level comparison theorem](#92-the-finite-level-comparison-theorem)
   - [Frobenius, Verschiebung, and the Hodge subspace](#93-frobenius-verschiebung-and-the-hodge-subspace)
   - [Pairings, endomorphisms, and isogenies](#94-pairings-endomorphisms-and-isogenies)
10. [From the special fiber to a mixed-characteristic model](#10-from-the-special-fiber-to-a-mixed-characteristic-model)
    - [What specialization remembers](#101-what-specialization-remembers)
    - [What it forgets](#102-what-it-forgets)
    - [The role of the Hodge filtration](#103-the-role-of-the-hodge-filtration)
11. [The denominator theorem](#11-the-denominator-theorem)
    - [Integral Hopf lattices](#111-integral-hopf-lattices)
    - [The first elementary modification](#112-the-first-elementary-modification)
    - [The ramification cost](#113-the-ramification-cost)
    - [The isomorphism lemma](#114-the-isomorphism-lemma)
12. [Raynaud full faithfulness](#12-raynaud-full-faithfulness)
    - [Closure of the generic graph](#121-closure-of-the-generic-graph)
    - [The full-faithfulness theorem](#122-the-full-faithfulness-theorem)
    - [Exact and coefficient-linear consequences](#123-exact-and-coefficient-linear-consequences)
    - [Descent and change of base](#124-descent-and-change-of-base)
13. [The ramification boundary](#13-the-ramification-boundary)
    - [Sharp order-$p$ counterexamples](#131-sharp-order-p-counterexamples)
    - [Why the inequality is strict](#132-why-the-inequality-is-strict)
    - [Equal characteristic and imperfect residue fields](#133-equal-characteristic-and-imperfect-residue-fields)
14. [The combined classification package](#14-the-combined-classification-package)
    - [A theorem ledger](#141-a-theorem-ledger)
    - [A hypothesis ledger](#142-a-hypothesis-ledger)
    - [Conclusion](#143-conclusion)

## 1. From a finite group to linear arithmetic

Finite flat group schemes at the residue characteristic carry two kinds of information at once. Their special fibers can be connected and nonreduced, so geometric points do not determine them. Their generic fibers in mixed characteristic are étale, so they also encode finite Galois modules. The central problem is to pass between these nonlinear integral groups and linear objects without erasing either specialization or ramification.

### 1.1 The two classification problems

There are really two classification questions. Over a perfect field $k$ of characteristic $p$, one wants to classify finite commutative $p$-power-order group schemes. Here Frobenius and Verschiebung are visible on the group itself, and Dieudonné theory converts the group into a finite-length module over the Witt ring $W(k)$ equipped with two semilinear operators.

Over a mixed-characteristic discrete valuation ring $R$, the question is different. A finite flat group has an étale generic fiber, hence a finite representation of the absolute Galois group of $K=\operatorname{Frac}(R)$. One asks whether a generic morphism extends over $R$, and whether two models of the same generic group must coincide. Book 42 showed that generic fiber is always faithful but need not be full. Book 51 proved fullness for groups of order $p$ when the absolute ramification index satisfies $e<p-1$. The higher-height theorem is Raynaud full faithfulness.

These problems meet in a degeneration argument. If two mixed-characteristic Hopf lattices differ, their first difference is detected on the special fiber. Dieudonné theory extracts an elementary order-$p$ piece from that difference. The Oort--Tate calculation of Book 51 then shows that moving this piece costs at least $p-1$ units of valuation. When $e<p-1$, there is not enough ramification for even the first modification, so no two lattices can differ.

The other bridge comes from geometry. If $A$ is an abelian variety over a perfect field, the Dieudonné modules of $A[p^n]$ are the reductions modulo $p^n$ of $H^1_{\mathrm{cris}}(A/W(k))$. Thus the finite group, its Frobenius, its duality, and its height are already present in the integral degree-one crystalline lattice constructed in Book 49.

### 1.2 Standing conventions

Throughout Chapters 2--9, $k$ is a perfect field of characteristic $p>0$,

$$
W=W(k),\qquad W_n=W/p^nW,
$$

and $\sigma:W\to W$ is Witt Frobenius. Perfection makes $\sigma$ an automorphism. A finite commutative $p$-group scheme over $k$ means a commutative group scheme, finite over $k$, of order $p^h$ for some $h\geq0$. No reducedness is assumed.

We use the **contravariant** Dieudonné convention. A homomorphism $G\to H$ induces a map $D(H)\to D(G)$. On a Dieudonné module $M$, the operators satisfy

$$
F(am)=\sigma(a)F(m),\qquad
V(am)=\sigma^{-1}(a)V(m),\qquad FV=VF=p.
\tag{1.1}
$$

With this convention the constant group has unit Frobenius, while the multiplicative group has unit Verschiebung:

$$
\begin{array}{c|c|c}
G&D(G)&(F,V)\\
\hline
\mathbf Z/p^n\mathbf Z&W_n&(\sigma,p\sigma^{-1})\\
\mu_{p^n}&W_n&(p\sigma,\sigma^{-1})\\
\alpha_p&k&(0,0).
\end{array}
\tag{1.2}
$$

Chapters 10--13 use a complete mixed-characteristic DVR $R$ with fraction field $K$, perfect residue field $k$, uniformizer $\pi$, and normalized valuation

$$
v(\pi)=1,\qquad e=v(p).
\tag{1.3}
$$

The residue field need not be finite. Completeness may be weakened to henselianity in the structural statements, but completeness keeps the valuation and Galois language uniform. Every finite flat group in the Raynaud theorem is commutative and of $p$-power order. The generic fiber is automatically étale because $\operatorname{char}K=0$.

Book 48 supplies divided powers, crystalline sites, crystals, and Frobenius pullback. Book 49 supplies finite locally free $H^1_{\mathrm{cris}}$ for abelian schemes, arbitrary PD base change, Frobenius, duality, and polarizations. Book 51 supplies schematic closure, connected--étale and multiplicative filtrations, Cartier duality, and the complete Oort--Tate calculation in order $p$. We recall the exact forms used below.

### 1.3 The route through the book

The argument proceeds from linear algebra to geometry and back. Witt vectors first provide the unique unramified characteristic-zero coefficient ring with a Frobenius lift. Witt covectors then define the Dieudonné module of a finite group. A fundamental calculation with additive polynomials proves the anti-equivalence rather than treating it as a black box.

The operators $F$ and $V$ read the connected, étale, multiplicative, and local-local directions. This gives a complete classification of the connected objects needed in height two, including ordinary and supersingular elliptic $p$-torsion. The construction is then sheafified on the crystalline site and compared, level by level, with the first crystalline cohomology of an abelian scheme.

Finally, a Hopf-lattice denominator argument reduces any failure of integral fullness to an order-$p$ elementary modification. The Oort--Tate relation forces that modification to consume at least $p-1$ units of absolute ramification. Graph closure then proves Raynaud full faithfulness when $e<p-1$. The last chapters show that the inequality is sharp and state precisely which parts survive at the boundary.

## 2. Witt vectors and the Dieudonné ring

The coefficient ring cannot simply be $k$. Frobenius on a connected group may be nilpotent, while Verschiebung records information complementary to it, and their composite must remember multiplication by $p$. Witt vectors are the ring in which these three facts coexist.

### 2.1 Why Witt vectors are the coefficient ring

For a perfect field $k$, an element of $W(k)$ has a unique Teichmüller expansion

$$
a=[a_0]+p[a_1]+p^2[a_2]+\cdots,
\qquad a_i\in k.
\tag{2.1}
$$

Here $[a]$ is multiplicative: $[ab]=[a][b]$, and reduction modulo $p$ sends $[a]$ to $a$. Addition is determined by requiring the ghost components

$$
w_r(x_0,x_1,\ldots)=x_0^{p^r}+p x_1^{p^{r-1}}+\cdots+p^r x_r
\tag{2.2}
$$

to be additive and multiplicative. These universal integral polynomials construct $W(k)$ without division in $k$.

The ring $W(k)$ is a complete DVR with uniformizer $p$ and residue field $k$. To see that every nonzero element has the form $p^r u$, take the first nonzero Teichmüller coefficient in (2.1); the remaining factor has nonzero reduction and is therefore a unit. Completeness follows by construction as

$$
W(k)=\varprojlim_n W_n(k).
$$

The Witt Frobenius is

$$
\sigma\left(\sum_{i\geq0}p^i[a_i]\right)
=\sum_{i\geq0}p^i[a_i^p].
\tag{2.3}
$$

Since $k$ is perfect, $a\mapsto a^p$ is bijective, so $\sigma$ is an automorphism. This bijectivity is exactly what makes the semilinear operator $V$ in (1.1) definable using $\sigma^{-1}$.

### 2.2 Frobenius and Verschiebung

On Witt vectors of an arbitrary characteristic-$p$ algebra, Frobenius shifts ghost components and Verschiebung shifts Witt coordinates:

$$
V(x_0,x_1,\ldots)=(0,x_0,x_1,\ldots).
$$

Over a perfect field these operations satisfy

$$
F_WV_W=V_WF_W=p.
\tag{2.4}
$$

The identity follows on ghost components, where both composites multiply every component by $p$; the ghost-polynomial identity is universal over $\mathbf Z$, so it remains valid even though the ghost map is not injective after reduction.

For group schemes, relative Frobenius and Verschiebung satisfy the analogous relation. If $G/k$ is a commutative finite group, relative Frobenius is

$$
F_{G/k}:G\longrightarrow G^{(p)}.
$$

Define Verschiebung by Cartier duality:

$$
V_{G/k}:G^{(p)}\longrightarrow G
$$

as the Cartier dual of relative Frobenius on $G^D$, with the natural Frobenius twists inserted. This definition is functorial and does not require Frobenius itself to be dominant. On a constant group it is multiplication by $p$ after the twist; on a diagonalizable group it is the dual transfer.

This description also proves the identities cleanly. Cartier duality changes the standard Frobenius--Verschiebung composite on the universal commutative group into the composite in the opposite order, while multiplication by $p$ is self-dual. The identity is polynomial in the universal Hopf coordinates, so descent from a presentation gives

$$
F_GV_G=V_GF_G=[p].
\tag{2.5}
$$

### 2.3 The noncommutative operator ring

The **Dieudonné ring** is

$$
\mathbb D_k=
W\langle F,V\rangle/
(FV-p,\ VF-p,\ Fa-\sigma(a)F,\ Va-\sigma^{-1}(a)V).
\tag{2.6}
$$

It is noncommutative unless $\sigma=1$. A left $\mathbb D_k$-module is exactly a $W$-module equipped with operators satisfying (1.1). The alternative relation

$$
aV=V\sigma(a)
$$

is obtained from the last relation in (2.6) by replacing $a$ with $\sigma(a)$.

A **finite Dieudonné module** is a left $\mathbb D_k$-module of finite length as a $W$-module. Such a module is killed by some $p^n$. Conversely, a finitely generated $W$-module killed by a power of $p$ has finite length because $W$ is a DVR.

The category is abelian. If $u:M\to N$ commutes with $F$ and $V$, its kernel and cokernel as $W$-modules inherit the operators. The relation $FV=p$ survives. This elementary fact is important: the group-scheme category will inherit its exact calculus from a genuinely abelian module category over the field $k$, even though finite flat group schemes over a DVR do not form an abelian category.

Every nonzero finite Dieudonné module has a simple quotient. A simple module is killed by $p$, hence is a finite-dimensional $k$-space. If both $F$ and $V$ vanish, simplicity forces dimension one. If $F$ is nonzero, its image is a nonzero submodule and hence all of $M$; thus $F$ is bijective and $V=0$. This is an irreducible semilinear étale module. After a finite separable extension it becomes a direct sum of one-dimensional constant factors, though it need not be one-dimensional over $k$. The case of nonzero $V$ is dual. This trichotomy is the linear origin of $\alpha_p$, finite étale simple forms, and their multiplicative duals.

The semilinear descent is explicit. If $M$ is killed by $p$ and $F$ is bijective, put

$$
T(M)=\{x\in M\otimes_k k^s:F(x)=x\}.
$$

Writing $F$ as $A\sigma$ in a basis, split the equation $F(x)=x$ by a matrix $B$ satisfying

$$
A B^{(p)}=B.
$$

Such a $B$ exists over a finite separable extension: the Lang map $B\mapsto B(B^{(p)})^{-1}$ on $\operatorname{GL}_d$ is étale, and over an algebraic closure its column equations are solved successively. The solutions form a $d$-dimensional $\mathbf F_p$-space, and

$$
k^s\otimes_{\mathbf F_p}T(M)\xrightarrow{\sim}M\otimes_kk^s.
$$

The Galois action on $T(M)$ is continuous and descends its constant group. Conversely, scalar extension of a finite étale $p$-group gives this fixed-vector construction. Thus no separate étale classification is hidden in the later existence proof.

## 3. The finite Dieudonné module of a group

The operator ring becomes useful only after a functor from group schemes has been constructed. Witt covectors provide a universal smooth unipotent target whose endomorphisms contain $W$, $F$, and $V$. Homomorphisms into this target linearize a finite group contravariantly.

### 3.1 Witt covectors and the definition

For $m\geq1$, let $CW_m$ be the affine commutative group whose points on a $k$-algebra $A$ are finite covectors

$$
(a_{-m+1},\ldots,a_{-1},a_0),
$$

with addition given by the Witt addition polynomials read from right to left. The transition $CW_m\hookrightarrow CW_{m+1}$ adds a zero on the left. Put

$$
CW=\varinjlim_m CW_m
$$

as an fppf sheaf. Frobenius raises the covector coordinates to $p$th powers, Verschiebung shifts them, and Teichmüller scalars act through the Witt polynomials. Their endomorphisms satisfy (2.6).

For a finite commutative $p$-group $G/k$, define

$$
D(G)=\operatorname{Hom}_{k\text{-grp}}(G,CW),
\tag{3.1}
$$

where a map lands in some finite stage because $G$ is quasi-compact. Postcomposition makes $D(G)$ a left $\mathbb D_k$-module. A morphism $u:G\to H$ gives

$$
D(u):D(H)\longrightarrow D(G),\qquad f\longmapsto f\circ u,
$$

so the construction is contravariant.

The raw Hom description is left exact but not visibly right exact. The missing fact is the Cartier--Dieudonné lemma. We state it in the finite form needed throughout the book.

**Lemma 3.1 (Cartier--Dieudonné lemma).** On the category of finite commutative $p$-group fppf sheaves over a perfect field:

1. $CW$ is injective, and every nonzero group admits a nonzero map to $CW$;
2. $\operatorname{End}(CW)$ generated by Witt scalars, Frobenius, and Verschiebung is the completed Dieudonné ring, and a map from a finite group sees only a finite quotient of it;
3. for a finite-length left $\mathbb D_k$-module $M$, the fppf sheaf

   $$
   \mathcal G(M)(A)=
   \operatorname{Hom}_{\mathbb D_k}
   \bigl(M,CW(A)\bigr)
   \tag{3.1a}
   $$

   is represented by a finite commutative $p$-group, and evaluation induces isomorphisms

   $$
   M\xrightarrow{\sim}D(\mathcal G(M)),
   \qquad
   G\xrightarrow{\sim}\mathcal G(D(G)).
   \tag{3.1b}
   $$

**Proof strategy.** Everything reduces to finite covectors and additive polynomials. Injectivity is the assertion that a covector-valued homomorphism on a subgroup can be extended after adding finitely many coordinates. Representability is proved first for a simple module and then across one module extension; the same cocycle calculation both writes the representing Hopf algebra and shows that equivalent module extensions give isomorphic group extensions.

**Proof.** Suppose $H\subset G$ and $H\to CW_m$ is given. Since $G$ is affine and finite, the last coordinate can be lifted to an element of $\mathcal O(G)$. Its failure to be primitive is a symmetric normalized two-cocycle in

$$
\ker(\varepsilon)\otimes_k\ker(\varepsilon).
$$

After a separable extension, split the connected and étale parts. On the connected part the augmentation ideal is nilpotent. The Witt addition formula says that the coboundary of the next covector coordinate is the universal carry polynomial for the preceding coordinate, so successively adjoining carry coordinates moves the error into strictly higher powers of that ideal and eventually kills it. On the finite constant étale part, covectors form a $p$-divisible abelian group: division by $p$ is the left shift, so the ordinary extension criterion for homomorphisms of finite abelian $p$-groups applies. The two extensions agree on the intersection and give a homomorphism after the split connected--étale decomposition. All equations used are Witt-polynomial equations over $k$; applying the semilinear descent calculation of §2.3 to their finite solution module descends the extension. Thus one obtains a corrected finite covector homomorphism $G\to CW_{m+r}$ extending the original map. Hence

$$
\operatorname{Hom}(G,CW)\longrightarrow\operatorname{Hom}(H,CW)
$$

is surjective. This proves injectivity. If $G\ne0$, take a quotient of minimal positive order. The semilinear descent calculation of §2.3 identifies the covector homomorphisms from its étale part with the corresponding nonzero simple Dieudonné space; Cartier duality does the same for a multiplicative simple, and a local-local simple is $\alpha_p$ and maps nontrivially to the last covector coordinate. Thus the simple quotient, already over $k$, has a nonzero map to $CW$. Hence $CW$ is a cogenerator.

Postcomposition by Witt scalars, $F$, and $V$ gives the relations (2.6). Conversely, an endomorphism of covectors is determined successively by its effect on the last coordinate. Subtracting a Teichmüller scalar makes that coordinate vanish; division by the shift then reduces the length. Induction writes the endomorphism uniquely as a convergent sum of words in $F,V$, and scalars. A map from a finite group lands in some $CW_m$ and is killed by some $p^n$, so only finitely many terms act. This proves the endomorphism assertion in the only sense used here.

We next prove representability of (3.1a) by induction on $\operatorname{length}_W M$. A simple module is killed by $p$. If $F$ is bijective, semilinear descent from §2.3 represents (3.1a) by the corresponding finite étale group. If $V$ is bijective, Cartier duality gives the multiplicative group. If $F=V=0$, the equations in (3.1a) say that the last covector coordinate is primitive and has $p$th power zero, giving $\alpha_p$. These constructions include nonsplit étale and multiplicative forms over $k$.

For the induction step choose

$$
0\longrightarrow N\longrightarrow M\longrightarrow S\longrightarrow0
\tag{3.1c}
$$

with $S$ simple. After a finite separable extension splitting $S$, choose one basis vector and a $W$-module lift $s$; perform the following construction simultaneously on its finite Galois orbit. For each such vector the module extension is determined by the two defects

$$
Fs-f_Ss=u,
\qquad
Vs-v_Ss=w,
\qquad u,w\in N,
\tag{3.1d}
$$

subject exactly to the two equations obtained from $FV=VF=p$. Replacing $s$ by $s+n$ changes $(u,w)$ by

$$
(u,w)\longmapsto
(u+Fn-f_Sn,\;w+Vn-v_Sn).
\tag{3.1e}
$$

By induction $N$ is represented. Add to its finite Hopf algebra one torsor coordinate for each vector in that orbit. In the étale case each terminal equation is $X^p-X=c$; in the local case it is $X^p=c$; the multiplicative case is the Cartier dual of the reversed construction. Give each $X$ a coproduct

$$
\Delta X=X\otimes1+1\otimes X+z.
\tag{3.1f}
$$

The Witt carry polynomials turn (3.1d) into a unique finite $z$ and a terminal coefficient $c$. The relations $FV=p$ and $VF=p$ are respectively the compatibility of (3.1f) with the terminal equation and coassociativity of (3.1f). Formula (3.1e) is precisely the change of coordinate $X\mapsto X+n$. Thus the resulting finite free Hopf algebra depends only on the extension class and represents $\mathcal G(M)$. All formulas commute with the finite descent datum, so the construction descends from the splitting field.

Evaluation gives the two maps (3.1b). They are isomorphisms for simple objects by the explicit calculation. For (3.1c), they fit into morphisms of short exact sequences whose outer maps are isomorphisms by induction; the middle maps are therefore isomorphisms. This simultaneously proves both assertions for every finite length. $\square$

### 3.2 Exactness and length

Injectivity in Lemma 3.1 shows that a faithfully flat exact sequence

$$
0\longrightarrow G'\longrightarrow G\longrightarrow G''\longrightarrow0
$$

gives an exact sequence

$$
0\longrightarrow D(G'')\longrightarrow D(G)
\longrightarrow D(G')\longrightarrow0.
\tag{3.2}
$$

The last surjectivity is the injectivity calculation for $CW$; exactness in the other places follows directly from the sheaf quotient property.

**Proposition 3.1.** The module $D(G)$ has finite $W$-length and

$$
\operatorname{length}_W D(G)=\log_p|G|.
\tag{3.3}
$$

**Proof strategy.** Filter the group by order-$p$ subquotients after a finite separable extension, compute the three atomic cases, and descend the length.

Over an algebraic closure, choose a nonzero subgroup $H\subseteq G$ of minimal order. If $H$ is étale, it is a simple finite abelian $p$-group and hence $\mathbf Z/p$. If $H$ is connected and $H^D$ is étale, duality gives $H=\mu_p$. In the remaining local-local case, $\ker(F_H)$ is nonzero: on the local coordinate algebra a sufficiently high Frobenius is zero, so there is a first power at which its kernel appears. Minimality forces $\ker(F_H)=H$, and the same argument on the dual forces $V_H=0$. A nonzero primitive element in the cotangent space then has $p$th power zero and defines a nonzero homomorphism $H\to\alpha_p$. Its kernel is a proper subgroup of the minimal group $H$, hence is zero; consequently $H$ embeds in the order-$p$ group $\alpha_p$ and must equal it. Thus every nonzero group contains one of the three order-$p$ groups. Induction on the order gives a filtration with order-$p$ quotients.

Exactness (3.2) turns this into a filtration of $D(G)$ in the reverse order. Direct calculation gives a one-dimensional $k$-module for each of $\mathbf Z/p$, $\mu_p$, and $\alpha_p$. Hence the length is the number of factors, namely $\log_p|G|$. Length and order are unchanged by faithfully flat field extension, so the formula descends. $\square$

The evaluation isomorphism (3.1b) also shows immediately that $p^nG=0$ if and only if $p^nD(G)=0$: multiplication by $p^n$ corresponds under evaluation to multiplication by $p^n$ on the module.

### 3.3 The three groups of order $p$

The atomic calculations fix every convention. For the constant group, a homomorphism to covectors is determined by the image of $1$. Frobenius acts through the Frobenius of the coefficients and is invertible, while $FV=p=0$ on the length-one module. Thus

$$
D(\mathbf Z/p\mathbf Z)=k,\qquad F=\sigma,\quad V=0.
\tag{3.4}
$$

Cartier duality exchanges the constant group and $\mu_p$ and exchanges $F$ with $V$ in the semilinear dual. Hence

$$
D(\mu_p)=k,\qquad F=0,\quad V=\sigma^{-1}.
\tag{3.5}
$$

For $\alpha_p=\operatorname{Spec}k[t]/(t^p)$ with primitive $t$, a map into the first covector coordinate is a scalar multiple of $t$. Both the $p$th-power map and the shift vanish, giving

$$
D(\alpha_p)=k,\qquad F=V=0.
\tag{3.6}
$$

For higher cyclic levels, induction through

$$
0\to\mathbf Z/p^{n-1}\to\mathbf Z/p^n\to\mathbf Z/p\to0
$$

and its Cartier dual gives the first two rows of (1.2). The nonsplit nature of the cyclic extension is recorded by the $W_n$-module: replacing $W_n$ by $k^n$ would forget multiplication by $p$ between adjacent factors.

## 4. The finite-level classification theorem

The construction of $D(G)$ would be incomplete if it merely supplied invariants. Lemma 3.1 already built a candidate inverse. We now separate the three consequences needed later: the extension comparison, control of morphisms, and realization of every finite module.

### 4.1 The fundamental extension calculation

Let $S$ be simple and $N$ finite. Write $G_S=\mathcal G(S)$ and $G_N=\mathcal G(N)$. The construction in the proof of Lemma 3.1 gives more than representability: it identifies the extension classes on the two sides.

**Lemma 4.1 (extension comparison).** If $H$ is a finite commutative $p$-group with $D(H)=N$, the natural map

$$
\operatorname{Ext}^1_{k\text{-grp}}(H,G_S)
\longrightarrow
\operatorname{Ext}^1_{\mathbb D_k}(S,N)
\tag{4.1}
$$

obtained from $D$ is bijective. Here the left side classifies sequences $0\to G_S\to E\to H\to0$, while contravariance gives $0\to N\to D(E)\to S\to0$. The same assertion holds with the two group arguments, and therefore the two module arguments, reversed.

**Proof.** Apply the construction (3.1c)--(3.1f). It sends a module extension to a finite flat group extension and changing its module splitting changes the torsor coordinate by exactly the corresponding coboundary. Applying $D$ recovers (3.1d), so the composite from right to left in (4.1) is the identity. Conversely, start with a group extension and apply $D$. Evaluation (3.1b) gives a morphism from the group extension reconstructed from its module extension to the original group extension. It is an isomorphism on the subgroup and quotient, hence on the middle group by faithfully flat descent. Thus the other composite is the identity. Reversing the short exact sequence and applying Cartier duality proves the reversed form. $\square$

The construction uses Baer sum and pullback of torsor coordinates, so the bijection respects pullback, pushout, Baer sum, Frobenius, Verschiebung, and extension of perfect fields.

### 4.2 Full faithfulness

The extension calculation must now be turned into control of arbitrary morphisms. A map between long objects can be built one simple layer at a time, provided that the obstruction to crossing each layer agrees on the group and module sides. This is why Lemma 4.1 was formulated for extensions rather than merely for objects.

**Theorem 4.2.** For finite commutative $p$-groups $G,H$ over $k$, the natural map

$$
\operatorname{Hom}_{k\text{-grp}}(G,H)
\longrightarrow
\operatorname{Hom}_{\mathbb D_k}(D(H),D(G))
\tag{4.7}
$$

is bijective.

**Proof.** For a module map $a:D(H)\to D(G)$, functoriality of (3.1a) gives a group map

$$
\mathcal G(D(G))\longrightarrow\mathcal G(D(H)).
$$

Conjugating by the evaluation isomorphisms $G\simeq\mathcal G(D(G))$ and $H\simeq\mathcal G(D(H))$ produces a map $G\to H$. Applying $D$ and using the first evaluation isomorphism recovers $a$. Conversely, a group map is recovered from its Dieudonné map by the second evaluation isomorphism. The two constructions are inverse. $\square$

The proof also shows why geometric points alone cannot replace $D$. Both $\mu_p$ and $\alpha_p$ have only the identity geometric point, whereas their $V$ operators are different.

### 4.3 Essential surjectivity

Full faithfulness would still leave open whether the operator category contains spurious modules. Essential surjectivity rules this out by reversing the same induction: build the desired group from its simple module factors while retaining the extension classes that glue those factors.

**Theorem 4.3.** Every finite Dieudonné module is isomorphic to $D(G)$ for a finite commutative $p$-group $G/k$.

**Proof.** Lemma 3.1 represents $\mathcal G(M)$ and gives the evaluation isomorphism

$$
M\xrightarrow{\sim}D(\mathcal G(M)).
$$

Its inductive construction shows explicitly that a simple quotient is realized by the corresponding étale, multiplicative, or local group and that each module extension is realized by the matching group extension. Hence the representing group is defined over $k$ and has order $p^{\operatorname{length}_W M}$. $\square$

### 4.4 The anti-equivalence

We can now package the construction, the morphism theorem, and the existence theorem in a form that can be invoked later. Recording exactness and length in the same statement is essential: later arguments extract simple special-fiber obstructions and must know that their module length is their scheme-theoretic order.

Combining exactness, Theorems 4.2 and 4.3, and the length formula gives the central classification.

**Theorem 4.4 (finite Dieudonné classification).** The functor

$$
D:\{\text{finite commutative }p\text{-group schemes over }k\}^{\mathrm{op}}
\longrightarrow
\{\text{finite-length left }\mathbb D_k\text{-modules}\}
\tag{4.9}
$$

is an exact anti-equivalence. It satisfies

$$
|G|=p^{\operatorname{length}_W D(G)}
\tag{4.10}
$$

and it commutes with extension of perfect fields. If $(G_n)$ is a compatible divisible system, its transition sequences are carried to the reversed exact module sequences; Chapter 6 identifies the resulting inverse system with reduction modulo $p^n$ of a finite free module.

**Proof.** Full faithfulness and essential surjectivity give the anti-equivalence. Exactness is (3.2), and the order formula is Proposition 3.1. Perfect field extension commutes with Witt covectors and their operator polynomials, so

$$
D(G_{k'})\simeq W(k')\otimes_WD(G).
$$

$\square$

The final qualification is essential: an arbitrary finite group need not sit canonically in a divisible system. The quotient formula is proved only after such a system is supplied, as it is for $A[p^n]$ in an abelian variety.

## 5. Reading geometry from operators

The anti-equivalence becomes geometric only after one learns how to read a group from $F$ and $V$. Nilpotence detects connectedness, invertibility detects étaleness or multiplicative type, and stable direct-sum decompositions recover the canonical filtrations of Book 51.

### 5.1 Connected and étale directions

**Theorem 5.1.** Let $G/k$ be a finite commutative $p$-group and $M=D(G)$.

1. $G$ is étale if and only if $F:M\to M$ is bijective.
2. $G$ is connected if and only if $F$ is nilpotent.

**Proof strategy.** Relative Frobenius is an isomorphism precisely on a finite étale group and is nilpotent precisely on a finite connected group. The operator $F$ is the contravariant image of relative Frobenius.

If $G$ is étale, relative Frobenius is an isomorphism because $k$ is perfect, so $F$ is bijective. Conversely, bijectivity of $F$ makes relative Frobenius an isomorphism by full faithfulness. A finite scheme over a perfect field whose relative Frobenius is an isomorphism is reduced and hence étale.

If $G$ is connected, its finite coordinate algebra is local with nilpotent augmentation ideal. A sufficiently high relative Frobenius raises every augmentation element to a $p^r$th power beyond its nilpotence exponent, so the Frobenius morphism becomes the zero group homomorphism. Hence $F^r=0$. Conversely, if $F$ is nilpotent, the maximal étale quotient would have bijective $F$ and must vanish. Thus $G$ is connected. $\square$

For any finite-length $M$, the Fitting decomposition for the semilinear map $F$ gives

$$
M=M_{F\text{-nil}}\oplus M_{F\text{-bij}}.
\tag{5.1}
$$

Both summands are stable under $V$ because $FV=VF$. Under the anti-equivalence this is the connected--étale sequence. Over a perfect field it splits canonically at the module level and hence at the group level:

$$
G\simeq G^0\times G^{\mathrm{et}}.
\tag{5.2}
$$

This splitting is special to a perfect field. Over a henselian mixed-characteristic DVR the connected--étale sequence of the special fiber lifts, but it need not split integrally.

### 5.2 Multiplicative and local-local directions

Cartier duality turns the preceding criterion around.

**Theorem 5.2.** With $M=D(G)$:

1. $G$ is of multiplicative type if and only if $V$ is bijective.
2. $G^D$ is connected if and only if $V$ is nilpotent.
3. $G$ is local-local if and only if both $F$ and $V$ are nilpotent.

**Proof.** A group is multiplicative precisely when its Cartier dual is étale. Section 5.3 below identifies the Frobenius of the dual with the transpose of $V$, so bijectivity of one is bijectivity of the other. The connected statement is the same argument with nilpotence. Combining it with Theorem 5.1 gives the local-local criterion. $\square$

The Fitting decomposition for $V$ inside the $F$-nilpotent summand gives

$$
M=M_{\mathrm{mult}}\oplus M_{\mathrm{ll}}\oplus M_{\mathrm{et}},
\tag{5.3}
$$

where $V$ is bijective on the first summand, both operators are nilpotent on the second, and $F$ is bijective on the third. This is the split perfect-field form of the three-step filtration

$$
0\subset G^{\mathrm{mult}}\subset G^0\subset G
$$

from Book 51.

### 5.3 Cartier duality

For a finite-length $W$-module $M$, put

$$
M^\vee=\operatorname{Hom}_W(M,K_0/W),
\qquad K_0=W[1/p].
\tag{5.4}
$$

This is the Matlis dual; it has the same $W$-length as $M$. Define operators by the adjoint rules

$$
\langle F\phi,m\rangle
=\sigma\bigl(\langle\phi,Vm\rangle\bigr),
\qquad
\langle V\phi,m\rangle
=\sigma^{-1}\bigl(\langle\phi,Fm\rangle\bigr).
\tag{5.5}
$$

They satisfy (1.1) and $FV=VF=p$. A direct check uses, for example,

$$
\langle FV\phi,m\rangle
=\sigma\bigl(\langle V\phi,Vm\rangle\bigr)
=\langle\phi,FVm\rangle=p\langle\phi,m\rangle.
$$

**Theorem 5.3.** There is a functorial isomorphism

$$
D(G^D)\simeq D(G)^\vee
\tag{5.6}
$$

under which Frobenius and Verschiebung are exchanged by (5.5).

**Proof.** Evaluation $G\times G^D\to\mathbf G_m$ followed through finite Witt covectors gives a perfect pairing of the two Dieudonné modules into $K_0/W$. Compatibility of Cartier duality with relative Frobenius says that $F_{G^D}$ is dual to $V_G$, giving (5.5). The pairing is perfect for the three order-$p$ groups by (3.4)--(3.6). Exactness and induction on length make it perfect for every finite group. $\square$

### 5.4 Functorial decompositions

The operator description makes all decompositions functorial. A module map carries an $F$-nilpotent vector to an $F$-nilpotent vector and an $F$-bijective summand to the corresponding bijective summand. The same holds for $V$. Hence every group homomorphism respects connected, étale, multiplicative, and local-local factors.

Ranks become lengths:

$$
\begin{aligned}
|G^{\mathrm{et}}|&=p^{\ell(M_{F\text{-bij}})},\\
|G^{\mathrm{mult}}|&=p^{\ell(M_{V\text{-bij}})},\\
|G^{\mathrm{ll}}|&=p^{\ell(M_{F\text{-nil},V\text{-nil}})}.
\end{aligned}
\tag{5.7}
$$

No count of geometric points is involved. For example, $\mu_{p^n}$ has one geometric point but module length $n$.

## 6. Finite levels and truncated Barsotti--Tate objects

The full anti-equivalence classifies every finite $p$-group over $k$. Abelian torsion occupies a narrower and more rigid part of that category: its levels fit compatibly under multiplication by $p$. We isolate the exact module conditions used later without presupposing a general theory of infinite divisible groups.

### 6.1 Truncation by $p^n$

A **compatible divisible system of height $h$** over $k$ is a sequence $(G_n)_{n\geq1}$ with $|G_n|=p^{nh}$, closed immersions $G_n\hookrightarrow G_{n+1}$, and faithfully flat exact sequences

$$
0\longrightarrow G_n\longrightarrow G_{n+r}
\xrightarrow{[p^n]}G_r\longrightarrow0.
\tag{6.1}
$$

This finite-level definition is all that is required for the torsion groups of an abelian variety. Applying $D$ gives surjections

$$
D(G_{n+1})\twoheadrightarrow D(G_n)
$$

whose kernel is $p^nD(G_{n+1})$, and

$$
D(G_n)\simeq M/p^nM,
\qquad M=\varprojlim_nD(G_n).
\tag{6.2}
$$

**Proposition 6.1.** The inverse limit $M$ is finite free of rank $h$ over $W$, carries semilinear $F,V$ with $FV=VF=p$, and recovers every $G_n$ through (6.2).

**Proof.** Put $N_n=D(G_n)$. Contravariant exactness applied to (6.1) with $r=1$ gives

$$
0\longrightarrow N_1\longrightarrow N_{n+1}
\longrightarrow N_n\longrightarrow0.
$$

The last arrow is induced by the inclusion $G_n\hookrightarrow G_{n+1}$. Its kernel is the image of multiplication by $p^n$ on $N_{n+1}$, because the first group map is $[p^n]:G_{n+1}\to G_1$; hence the transition map is reduction modulo $p^n$. In particular $N_1$ is a $k$-space of dimension $h$.

Assume inductively that $N_n\simeq W_n^h$. Write the elementary-divisor decomposition of the $W_{n+1}$-module $N_{n+1}$ as $\bigoplus_iW_{a_i}$ with $1\leq a_i\leq n+1$. Its quotient modulo $p^n$ is $W_n^h$, so exactly $h$ summands have length at least $n$. Its $W$-length is $(n+1)h$ by the order formula. The kernel $p^nN_{n+1}\simeq N_1$ has dimension $h$, so all those $h$ summands have length $n+1$; the length equality leaves no further summands. Thus $N_{n+1}\simeq W_{n+1}^h$.

The surjective system is now identified compatibly with free reductions. Choose a basis of $N_1$ and lift it successively along the transition maps; the resulting map $W^h\to\varprojlim N_n$ is an isomorphism after reduction modulo every $p^n$, hence is an isomorphism. The compatible operators pass to the limit and recover every $N_n=M/p^nM$. $\square$

The converse is equally direct. A finite free $W$-module with $F,V$ satisfying (1.1) gives finite modules $M/p^nM$. The anti-equivalence produces groups $G_n$, and the quotient maps of modules produce the closed immersions and exact sequences (6.1). Thus compatible divisible systems are equivalent to finite free Dieudonné modules.

### 6.2 Level one

A finite group $G$ killed by $p$ is a **truncated Barsotti--Tate group of level one**, abbreviated BT$_1$, if its Dieudonné module $M$ satisfies

$$
\operatorname{im}F=\ker V,
\qquad
\operatorname{im}V=\ker F.
\tag{6.3}
$$

This definition is intrinsic by the anti-equivalence. It also follows from any compatible divisible system: reduce $FV=p$ modulo $p$, and use freeness over $W$ to check that the two inclusions have equal dimensions.

The equalities are necessary. The group $\alpha_p$ has $F=V=0$ on a one-dimensional module, so both images are zero and both kernels are all of $M$. Hence $\alpha_p$ is not BT$_1$, even though it is killed by $p$ and has order $p$. This is why $W_1$-freeness alone cannot characterize level-one truncations.

For a BT$_1$ module define

$$
h=\dim_kM,
\qquad d=\dim_k\operatorname{im}V=\dim_k\ker F.
\tag{6.4}
$$

Then $h$ is the height and $d$ is its BT dimension, meaning the dimension of the associated compatible divisible system rather than the Krull dimension of the finite scheme. The assertion follows from the cotangent comparison

$$
\omega_G\simeq D(G)/F D(G).
\tag{6.5}
$$

To prove (6.5), evaluate a covector homomorphism on the first infinitesimal neighborhood of the identity. Frobenius terms vanish there, so evaluation factors through $D(G)/FD(G)$ and gives a map to $I/I^2=\omega_G$. Conversely, a linear last coordinate on $I/I^2$ extends recursively through the covector carry polynomials: at each stage the primitive-coordinate condition determines the next coordinate, and changing a choice adds a Frobenius term. This is the first-coordinate part of the lifting calculation in Lemma 3.1 and gives an inverse to the displayed map. For a BT$_1$ module, rank--nullity and (6.3) give

$$
\dim_kM/FM=\dim_k\ker F=\dim_k\operatorname{im}V=d.
$$

Thus $d=\dim_k\omega_G$, which is precisely the BT dimension. Cartier duality replaces $d$ by $h-d$. This also follows from (5.5), because the annihilator of $\operatorname{im}V$ is $\ker V$ on the dual side.

### 6.3 Liftable higher levels

A finite level-$n$ group arising from a compatible divisible system has module $M/p^nM$ for a finite free $W$-module $M$. We call such a module **liftable of level $n$**. This term records exactly the property used here; it does not assert that an arbitrary free $W_n$-module with operators lifts.

Two elementary tests follow.

**Proposition 6.2.** If $N=M/p^nM$ is liftable of height $h$, then:

1. $N$ is free of rank $h$ over $W_n$;
2. $N/pN$ is BT$_1$;
3. for every $r\leq n$, $N/p^rN$ is the module of the level-$r$ truncation;
4. $N^\vee$ is liftable of height $h$.

**Proof.** The first three assertions are immediate from the free lift $M$ and (6.2). The identities (6.3) are checked by lifting a vector in a kernel and using $FV=p$ together with $p$-torsion-freeness of $M$. The dual of a finite free $W$-module is finite free, and (5.5) gives its operators, proving the last assertion. $\square$

The converse from one isolated level is subtler: lifting $F$ and $V$ while preserving $FV=p$ is a deformation problem. No such converse is needed for abelian torsion, because all levels are supplied simultaneously by the multiplication kernels $A[p^n]$.

### 6.4 Exact sequences and filtrations

An exact sequence of compatible divisible systems gives an exact sequence of their finite free Dieudonné modules in the reverse direction. Conversely, a short exact sequence of finite free Dieudonné modules whose quotient is $W$-free remains exact modulo every $p^n$ and hence gives exact sequences at every finite level.

The freeness qualification prevents a hidden Tor term. From

$$
0\to M'\to M\to M''\to0
$$

one gets after reduction

$$
0\to M'/p^nM'\to M/p^nM\to M''/p^nM''\to0
$$

precisely because $M''$ is $W$-flat. Without flatness the left term would be preceded by $M''[p^n]$.

Stable direct summands of $M$ therefore give compatible finite-level subgroup systems. Stable rational summands of $M[1/p]$ do not automatically do so: their intersections with $M$ must be saturated. This is the crystalline version of the integral caution already encountered for idempotents in Book 49.

## 7. Connected objects in height two

Height two is the first level at which a connected group can be genuinely local-local while still being a truncation of a divisible system. This case controls elliptic $p$-torsion and supplies the connected objects needed in the later integral theory.

### 7.1 The local-local plane

Let $M$ be a two-dimensional BT$_1$ module over an algebraically closed field, and assume both $F$ and $V$ are nilpotent. From (6.3), each has one-dimensional image and kernel, and

$$
\operatorname{im}F=\ker V,\qquad
\operatorname{im}V=\ker F.
$$

Nilpotence forces $\operatorname{im}F\subseteq\ker F$ and $\operatorname{im}V\subseteq\ker V$. All four lines are consequently equal. Choose $y$ on this common line and $x$ outside it. After rescaling $x$ and $y$ one has

$$
Fx=y,\quad Fy=0,\qquad
Vx=c y,\quad Vy=0
\tag{7.1}
$$

with $c\ne0$. A further semilinear rescaling solves $c=1$ over an algebraically closed field. Thus there is a unique local-local BT$_1$ module of height two and dimension one:

$$
M_{1,1}=kx\oplus ky,\qquad Fx=Vx=y,\quad Fy=Vy=0.
\tag{7.2}
$$

The corresponding group is often denoted $I_{1,1}$. It is not $\alpha_p\times\alpha_p$: the latter has both operators zero and fails (6.3). It contains an $\alpha_p$ subgroup and has an $\alpha_p$ quotient, but the extension is nonsplit. Indeed a splitting would make both operators zero on a complementary line, contradicting (7.2).

Over a merely perfect field, forms are classified by the semilinear scalar $c$ in (7.1) modulo the change induced by rescaling. After extending to an algebraic closure they all become $I_{1,1}$. Thus uniqueness without qualification is a geometric statement, not necessarily a statement over the original field.

### 7.2 Ordinary and supersingular elliptic $p$-torsion

Let $E/k$ be an elliptic curve. The finite group $E[p]$ is BT$_1$ of height two and dimension one. Its module therefore has dimension two and satisfies (6.3).

If $E$ is ordinary, $F$ has rank one and has a bijective line. The Fitting decomposition gives

$$
D(E[p])\simeq k_{F\text{-bij}}\oplus k_{V\text{-bij}}.
\tag{7.3}
$$

After an algebraic closure this corresponds to

$$
E[p]\simeq\mathbf Z/p\mathbf Z\times\mu_p.
\tag{7.4}
$$

If $E$ is supersingular, neither an étale nor a multiplicative factor exists. Both operators are nilpotent, so §7.1 gives

$$
E[p]_{\bar k}\simeq I_{1,1}.
\tag{7.5}
$$

This proves the classification from the operator identities. It also clarifies a specialization phenomenon from Book 42: ordinary special $p$-torsion has one connected and one étale direction, whereas supersingular special $p$-torsion is entirely connected. Both still have order $p^2$.

The $a$-number is

$$
a(E)=\dim_k\operatorname{Hom}(\alpha_p,E[p])
=\dim_k\frac{D(E[p])}{F D(E[p])+V D(E[p])}.
\tag{7.6}
$$

Indeed contravariance turns a map $\alpha_p\to E[p]$ into a functional $D(E[p])\to k$ annihilating the images of both $F$ and $V$. For the self-dual height-two modules at hand, the perfect alternating form identifies the dual of this quotient with $\ker F\cap\ker V$. Thus the $a$-number is $0$ in the ordinary case and $1$ in the supersingular case.

### 7.3 Polarized modules

A principal quasi-polarization on a compatible divisible system gives an alternating perfect pairing on its finite free module

$$
\langle\, ,\,\rangle:M\times M\longrightarrow W
\tag{7.7}
$$

with adjointness

$$
\langle Fx,y\rangle
=\sigma\langle x,Vy\rangle,
\qquad
\langle Vx,y\rangle
=\sigma^{-1}\langle x,Fy\rangle.
\tag{7.8}
$$

At level $n$ the pairing takes values in $W_n$ and identifies the module with its Dieudonné dual. Equation (7.8) is (5.5) written under that identification.

In height two, choose a symplectic basis. The ordinary decomposition consists of two mutually dual lines, one $F$-bijective and the other $V$-bijective. In the local-local module (7.2), the common image line $ky$ is isotropic and equals its own annihilator modulo $p$. This module calculation is the special-fiber shadow of the self-dual line sequence in Book 51.

The pairing alone does not choose an integral mixed-characteristic lift. It constrains the two factors and their duality, but the Hodge filtration and the Hopf lattice still carry additional information. That distinction becomes central after the crystalline comparison.

## 8. The crystalline Dieudonné crystal

The module $D(G)$ over a perfect field is one evaluation of a more flexible object. Families and deformations require values on every divided-power thickening, with canonical transport between them. Crystalline Dieudonné theory supplies exactly such a crystal.

### 8.1 Why one evaluation is not enough

Let $S_0$ be a characteristic-$p$ scheme over a divided-power base $(S,J,\gamma)$, and let $G/S_0$ be finite locally free and killed by a power of $p$. A single module over $\mathcal O_S$ cannot be functorial if $S_0$ has no chosen lift to $S$. Even when a lift exists, two lifts of a point differ by a divided-power infinitesimal displacement. The comparison between their linearizations is part of the object, not an equality of the underlying modules.

The correct object is therefore a crystal $\mathbf D(G)$ on $(S_0/S)_{\mathrm{cris}}$. Its value on a PD thickening $U\hookrightarrow T$ will be a module $\mathbf D(G)_T$, and an arrow $T'\to T$ will induce an isomorphism

$$
\mathcal O_{T'}\otimes_{\mathcal O_T}\mathbf D(G)_T
\xrightarrow{\sim}\mathbf D(G)_{T'}.
\tag{8.1}
$$

For arbitrary finite $G$, the value can have $p$-torsion and need not be locally free. For finite levels of a compatible divisible system, it is locally the reduction of a finite locally free crystal. This is the range needed for abelian torsion.

### 8.2 Construction on divided-power thickenings

The extension construction must be made on the big crystalline fppf site. The Zariski crystalline site of Book 48 is sufficient for quasi-coherent cohomology, but finite flat torsors are locally trivial only for the fppf topology. On a thickening $U\hookrightarrow T$, let $\mathcal O_{U/T}$ denote the additive crystalline structure sheaf on that site. Define

$$
\mathbf D(G)_T
=\mathcal{E}xt^1_{(U/T)_{\mathrm{cris}}}
(G_U,\mathcal O_{U/T}).
\tag{8.2}
$$

Here $\mathcal{E}xt^1$ means equivalence classes of extensions of abelian fppf sheaves; Baer sum makes it an $\mathcal O_T$-module. The scalar action comes from pushout on the additive kernel. Relative Frobenius on $G$, Frobenius on the crystalline structure sheaf, and Cartier duality define $F$ and $V$; their composites are multiplication by $p$. Passing from the big fppf crystalline site to the Zariski crystalline site does not change this quasi-coherent module, because quasi-coherent modules and their extensions satisfy fppf descent.

Thus an element of $\mathbf D(G)_T$ is an extension

$$
0\longrightarrow\mathcal O_{U/T}\longrightarrow\mathcal E
\longrightarrow G_U\longrightarrow0
\tag{8.3}
$$

on the crystalline fppf site, modulo isomorphism inducing the identity on the two end terms. Pullback in $G$ gives contravariance, while crystalline pullback changes the thickening.

**Theorem 8.1 (crystallinity).** The assignments (8.2) form a crystal. If $S_0=\operatorname{Spec}k$ with $k$ perfect and $T=\operatorname{Spec}W_n(k)$, then their compatible inverse limit is the finite Dieudonné module constructed by Witt covectors in Chapter 3.

**Proof strategy.** Resolve the additive crystalline structure sheaf by crystalline Witt covectors. Those covectors are injective for finite $p$-groups by Lemma 3.1, so an extension is represented by one finite covector cocycle. Witt polynomials commute with PD pullback, which proves crystallinity and identifies the perfect-field evaluation.

Let $CW_{U/T}$ be the sheaf of crystalline Witt covectors. The coordinatewise PD Taylor map gives a resolution of $\mathcal O_{U/T}$ by successive covector sheaves; on a group killed by $p^r$, only the first $r$ steps can contribute. Applying $\mathcal Hom(G,-)$ computes (8.2), because the covector sheaves are injective against finite $p$-groups by the lifting calculation of Lemma 3.1. Every differential in this resolution is a universal Witt polynomial.

For an arrow $T'\to T$, scalar extension carries this finite part of the resolution over $T$ to the corresponding resolution over $T'$. Consequently its first cohomology satisfies (8.1), and the comparison for a composite is the ordinary associativity of scalar extension. This proves crystallinity.

Over the Witt thickenings of a perfect field, the same resolution is the covector resolution used to define (3.1). Taking first cohomology therefore gives

$$
\mathbf D(G)_{W_n}\simeq D(G)/p^nD(G)
$$

for every $n$, with the right side interpreted literally; when $p^rG=0$ and $n\ge r$, it has stabilized. The construction respects $F,V$, so the compatible perfect-field evaluations recover $D(G)$. $\square$

The construction is intrinsic even though covector coordinates entered the proof: two choices give resolutions of the same additive crystalline sheaf, and the comparison theorem for resolutions gives a unique isomorphism on $\mathcal E xt^1$.

### 8.3 Exactness, base change, and duality

The crystalline construction is useful only if it preserves the operations used on finite flat groups. Exactness lets one pass to subquotients, base change makes the values into a genuine crystal, and duality is what identifies Frobenius information with the complementary Verschiebung information.

**Theorem 8.2.** Crystalline Dieudonné theory has the following properties.

1. A faithfully flat exact sequence of finite commutative $p$-groups gives a short exact sequence of crystals in the reverse direction.
2. Formation of $\mathbf D(G)$ commutes with PD base change.
3. If $p^nG=0$, evaluation $G\times G^D\to\mu_{p^n}$ identifies $\mathbf D(G^D)$ with

   $$
   \mathcal Hom\bigl(\mathbf D(G),\mathbf D(\mu_{p^n})\bigr),
   \tag{8.4}
   $$

   interchanging $F$ and $V$. For an inverse-limit divisible system this becomes ordinary duality of finite locally free crystals with the weight-one line.
4. For a compatible divisible system, the inverse-limit crystal is finite locally free and its level-$n$ crystal is its quotient by $p^n$.

**Proof.** Apply $\mathcal Hom(-,\mathcal O_{U/T})$ to a faithfully flat exact sequence. The covector resolution used in Theorem 8.1 is injective for finite $p$-groups and has no second cohomology on such a sequence; the resulting long exact sequence therefore stops after $\mathcal E xt^1$. This gives short exactness in the reverse direction.

PD base change pulls back extensions, and Theorem 8.1 identifies the resulting map with scalar extension of the covector resolution. This proves base change.

Evaluation $G\times G^D\to\mu_{p^n}$ gives the map (8.4). On the three order-$p$ groups it is the perfect pairing calculated in (3.4)--(3.6). Exactness and induction on length prove that it is an isomorphism in general. Cartier duality exchanges relative Frobenius and Verschiebung, giving the operator exchange. Passing to inverse limits turns $\mathbf D(\mu_{p^n})$ into the rank-one weight-one crystal.

Finally, apply exactness to the finite-level sequences (6.1). At every object of the crystalline site the module lengths grow linearly and reduction maps are surjective. The same elementary-divisor argument as in Proposition 6.1 gives a finite locally free inverse limit and identifies its quotients. $\square$

There is no claim here that the crystal of every finite $p$-group is locally free. The group $\alpha_p$, for example, has a length-one torsion crystal. Local freeness belongs to the inverse-limit object of a compatible divisible system.

## 9. Torsion in abelian schemes

An abelian scheme supplies compatible finite levels through its multiplication kernels. Book 49 supplies an apparently different compatible object, namely its finite free first crystalline cohomology with Frobenius. The comparison theorem says that these are the same construction.

### 9.1 The comparison problem

Let $A/k$ be an abelian variety of dimension $g$. Multiplication by $p^n$ is finite locally free of degree $p^{2gn}$, so

$$
A[p^n]=\ker([p^n]:A\to A)
$$

has order $p^{2gn}$. The groups $A[p^n]$ form a compatible divisible system of height $2g$.

On the other hand, Book 49 constructs the finite free $W$-module

$$
H=H^1_{\mathrm{cris}}(A/W)
$$

of rank $2g$, with semilinear Frobenius $\Phi$. Relative Verschiebung on $A$ induces a semilinear operator $\mathcal V$ in the opposite direction, and

$$
\Phi\mathcal V=\mathcal V\Phi=p.
\tag{9.1}
$$

Thus $H$ is a finite free Dieudonné module. Equality of ranks suggests

$$
D(A[p^n])\stackrel{?}{\simeq}H/p^nH,
$$

but rank alone cannot produce the isomorphism or its compatibility with products, duality, and base change.

### 9.2 The finite-level comparison theorem

The required comparison cannot be obtained by matching ranks: many nonisomorphic operator modules have rank $2g$. We construct the map from the universal extension, so functoriality and compatibility with $F,V$ are built in from the outset.

**Theorem 9.1 (abelian torsion comparison).** Let $A/k$ be an abelian variety over a perfect field. There is a canonical functorial isomorphism of finite Dieudonné modules

$$
D(A[p^n])\xrightarrow{\sim}
H^1_{\mathrm{cris}}(A/W)/p^n
\tag{9.2}
$$

for every $n\geq1$. The isomorphisms commute with truncation, extension of perfect fields, homomorphisms of abelian varieties, relative Frobenius, Verschiebung, and Cartier duality. Relatively, the same statement identifies the level-$n$ crystalline Dieudonné crystal of $A[p^n]$ with the quotient by $p^n$ of the first crystalline cohomology crystal.

**Proof strategy.** Apply the crystalline extension construction to the multiplication sequence and then use Cartier duality. A rigidified crystalline extension of $A[p^n]$ is controlled by an extension of $A^\vee$ whose pullback by $[p^n]$ is split. The universal vector extension of $A^\vee$ has Lie algebra $H^1_{\mathrm{cris}}(A/W)$.

Let $\mathcal E(A^\vee)$ denote the universal vector extension of the dual abelian variety: every extension of $A^\vee$ by a vector group is obtained uniquely by pushing out

$$
0\longrightarrow
\mathbf V(\omega_A)\longrightarrow
\mathcal E(A^\vee)\longrightarrow A^\vee\longrightarrow0.
\tag{9.3}
$$

Here $\mathbf V(\omega_A)$ denotes the vector group whose Lie algebra is $\omega_A$. We recall the construction because it is the bridge in the proof. An $S$-point of $\mathcal E(A^\vee)$ is an algebraically trivial line bundle on $A_S$, rigidified at the identity, together with an integrable connection. Forgetting the connection gives a point of $A^\vee(S)$. Two connections on the same rigidified line bundle differ by an invariant one-form, so the fiber is a torsor under $\mathbf V(\omega_A)$. Picard representability and faithfully flat descent represent this functor, and tensor product supplies its group law. Pushing out its vector kernel along a linear map gives every vector extension, because a connection on the pulled-back rigidified line bundle is exactly a splitting of that pushout. This proves the universal property in (9.3). Taking Lie algebras gives

$$
\operatorname{Lie}\mathcal E(A^\vee)
\simeq H^1_{\mathrm{dR}}(A/k),
$$

with exact sequence $0\to\omega_A\to H^1_{\mathrm{dR}}(A/k)\to\operatorname{Lie}(A^\vee)\to0$. Its crystalline evaluations are $H^1_{\mathrm{cris}}(A/W_m)$ by the lift comparison and base change of Book 49.

We use the multiplication lemma for universal extensions. If $B$ is an abelian scheme on a crystalline base and $\mathbb E(B)$ is the Lie crystal of its universal vector extension, restriction to the multiplication kernel gives an exact sequence

$$
\mathbb E(B)\xrightarrow{[p^n]^*}\mathbb E(B)
\longrightarrow\mathbf D(B[p^n]^D)\longrightarrow0.
\tag{9.4a}
$$

Here is the extension calculation. Work fppf locally on a PD thickening and choose a section of the torsor $[p^n]:B\to B$. A rigidified additive extension of its kernel supplies, by translation, descent data for the trivial additive extension over that cover. The failure of those data to descend is a vector extension of $B$, hence a unique pushout of the universal vector extension. Changing the chosen section changes that vector extension by $[p^n]^*$ of another one. Conversely, a vector extension whose class is changed by $[p^n]^*$ has trivial restriction to the kernel, and a trivialization produces the required rigidified kernel extension. These constructions are inverse and compatible with refinement of the cover. They identify the cokernel in (9.4a) with the full extension sheaf $\mathcal E xt^1(B[p^n]^D,\mathcal O_{\mathrm{cris}})$, not merely with a subquotient of it. Because the construction uses only pullback, translation, and pushout, it is crystalline and commutes with every PD base change.

Apply this lemma to the dual of

$$
0\to A[p^n]\to A\xrightarrow{[p^n]}A\to0,
\tag{9.4}
$$

which is the multiplication sequence of $A^\vee$ because $A[p^n]^D\simeq A^\vee[p^n]$. The universal-extension construction identifies $\mathbb E(A^\vee)$ with the first crystalline cohomology crystal of $A$. Thus (9.4a) becomes the exact cokernel presentation

$$
H
\xrightarrow{[p^n]^*}
H
\longrightarrow
\mathbf D(A[p^n])
\longrightarrow0.
\tag{9.5}
$$

Primitivity of degree-one crystalline cohomology, proved in Book 49, says that $[p^n]^*$ is multiplication by $p^n$. Therefore the last term is canonically $H/p^nH$, which proves (9.2).

Every compatibility follows from the construction. A homomorphism of abelian varieties gives a morphism of (9.4); relative Frobenius and Verschiebung give the two operator maps; the Poincaré biextension identifies the dual universal extension; and arbitrary PD base change holds on both sides. The connecting morphism in (9.4a), with the identity rigidifications on both end terms, fixes the normalization of the comparison and leaves no scalar choice. $\square$

This proof also establishes dependency closure: the comparison uses the exact crystalline and abelian-scheme results of Books 48--49, while the universal vector extension is constructed here from rigidified line bundles with connection.

### 9.3 Frobenius, Verschiebung, and the Hodge subspace

Reduce (9.2) modulo $p$:

$$
D(A[p])\simeq H^1_{\mathrm{dR}}(A/k).
\tag{9.6}
$$

The crystalline Hodge sequence is

$$
0\longrightarrow\omega_A
\longrightarrow H^1_{\mathrm{dR}}(A/k)
\longrightarrow\operatorname{Lie}(A^\vee)
\longrightarrow0.
\tag{9.7}
$$

**Proposition 9.2.** Under (9.6),

$$
\omega_A=\operatorname{im}V=\ker F.
\tag{9.8}
$$

Consequently $A[p]$ is BT$_1$ of height $2g$ and dimension $g$.

**Proof strategy.** The pullback of a differential by relative Frobenius is zero, so the Hodge subspace lies in $\ker F$. The cotangent comparison computes the dimension of that kernel, and the BT$_1$ identities then identify it with the image of Verschiebung.

Relative Frobenius kills invariant differentials, giving $\omega_A\subseteq\ker F$. The relation $FV=0$ modulo $p$ also gives $\operatorname{im}V\subseteq\ker F$.

Now use the cotangent comparison (6.5), rather than confusing the kernel of a group morphism with the kernel of its contravariant module map. Since $\omega_{A[p]}=\omega_A$ has dimension $g$, (6.5) gives

$$
g=\dim_k D(A[p])/F D(A[p])=\dim_k\ker F.
$$

The first equality and the inclusion $\omega_A\subseteq\ker F$ show that $\omega_A=\ker F$. The BT$_1$ identity (6.3), already proved from the compatible system $A[p^n]$, gives $\operatorname{im}V=\ker F$. This proves (9.8). $\square$

The quotient $H^1_{\mathrm{dR}}/\omega_A$ is correspondingly $\operatorname{im}F=\ker V$. For an ordinary abelian variety these two directions split into bijective summands. For a supersingular elliptic curve they meet in the local-local configuration of (7.2).

### 9.4 Pairings, endomorphisms, and isogenies

The Poincaré pairing on abelian torsion and the crystalline Poincaré class of Book 49 agree under (9.2). If $\lambda:A\to A^\vee$ is a principal polarization, then

$$
H\times H\longrightarrow W
\tag{9.9}
$$

is perfect alternating and satisfies

$$
\langle\Phi x,\Phi y\rangle
=p\sigma\langle x,y\rangle.
\tag{9.10}
$$

At level $n$ it is the Dieudonné form corresponding to the Weil pairing

$$
A[p^n]\times A[p^n]\longrightarrow\mu_{p^n}.
$$

To prove compatibility, both pairings arise from the normalized Poincaré biextension. On the group side, restrict the biextension to torsion; on the crystalline side, take its divided-power first Chern class. Restriction followed by the logarithm is the same cocycle as logarithm followed by restriction, so the comparison map carries one to the other. Perfectness follows from the principal polarization, and (9.10) follows because Frobenius pulls the Poincaré class to $p$ times itself.

An endomorphism $a\in\operatorname{End}(A)$ acts contravariantly on both sides of (9.2). If $a^\dagger$ is the Rosati adjoint, then

$$
\langle a^*x,y\rangle=\langle x,(a^\dagger)^*y\rangle.
\tag{9.11}
$$

An isogeny of degree divisible by $p$ need not act invertibly on the integral module. It becomes invertible after its degree is inverted and has kernel and cokernel killed by that degree. The same warning holds level by level: an isogeny is not an isomorphism of $p$-power torsion merely because it is an isomorphism on the rational isocrystal.

## 10. From the special fiber to a mixed-characteristic model

Dieudonné theory completely classifies the special fiber over a perfect field. It does not, by itself, classify finite flat lifts over a mixed-characteristic DVR. Understanding exactly what is remembered and forgotten prevents the later full-faithfulness theorem from being overstated.

### 10.1 What specialization remembers

Let $R$ be as in (1.3), and let $\mathcal G/R$ be a finite flat commutative $p$-group. Its special fiber $G=\mathcal G_k$ has a finite Dieudonné module $D(G)$. From this module one reads:

- the order of $\mathcal G$, through $\operatorname{length}_W D(G)$;
- the connected, étale, multiplicative, and local-local ranks of the special fiber;
- Cartier duality and every homomorphism after reduction;
- whether a level-one special fiber is BT$_1$;
- for abelian torsion, the reduction of the first crystalline lattice and its Hodge subspace.

All these statements are invariant under extension of the perfect residue field. They are scheme-theoretic: a connected group with one geometric point can have arbitrarily large order, and its module retains that order.

### 10.2 What it forgets

Distinct mixed-characteristic groups can have isomorphic special fibers and isomorphic generic fibers. Book 51 exhibited equal-characteristic chains distinguished by cotangent length; in mixed characteristic, Oort--Tate parameters with different unit classes or valuation depths can likewise produce different integral lattices.

Even the pair

$$
(\mathcal G_K,\mathcal G_k)
$$

need not determine $\mathcal G$. The gluing between the two fibers is encoded in the $R$-Hopf lattice inside the generic Hopf algebra. The conormal module

$$
\omega_{\mathcal G}=e^*\Omega_{\mathcal G/R}
$$

and its length can distinguish lattices with the same fibers. For an Oort--Tate group $G_{a,b}$, Book 51 computes

$$
\operatorname{length}_R\omega_{G_{a,b}}=v(a).
\tag{10.1}
$$

Thus a classification of special-fiber Dieudonné modules cannot be promoted to a classification of mixed-characteristic models without an additional rigidity hypothesis.

### 10.3 The role of the Hodge filtration

Suppose $\mathcal A/S$ is an abelian scheme over a divided-power lifting $S$ of $k$ to which the finite-level comparison theorem of Book 49 applies. Crystalline base change then identifies

$$
H^1_{\mathrm{cris}}(A/W)\otimes_W R
\simeq H^1_{\mathrm{dR}}(\mathcal A/R)
\tag{10.2}
$$

when $S=\operatorname{Spec}R$ and the displayed scalar extension is defined by the chosen compatible PD map. The lift contributes the Hodge filtration

$$
0\to\omega_{\mathcal A/R}\to
H^1_{\mathrm{dR}}(\mathcal A/R)
\to\operatorname{Lie}(\mathcal A^\vee/R)\to0.
\tag{10.3}
$$

The special-fiber module with $F,V$ describes $A[p^n]$ over $k$; the filtration describes the infinitesimal position of the lift. Both are needed in integral comparison theories. Book 53 will organize the pair into divided filtered modules. Here we use only the lesson: Dieudonné theory classifies the characteristic-$p$ fiber, while Raynaud's theorem controls morphisms between already existing mixed-characteristic models.

For a general ramified DVR, its maximal ideal need not carry divided powers compatible with those on $(p)$. In that situation (10.2) is not an available crystalline base-change formula. The de Rham Hodge filtration of $\mathcal A/R$ still exists, but comparing it with the special-fiber Witt module requires additional integral comparison data. Nothing in the Raynaud argument below uses (10.2).

There is no circularity between the two theorems. The proof of Raynaud full faithfulness uses special-fiber Dieudonné theory only to extract an elementary order-$p$ obstruction. It does not assume that the special fiber determines the lift.

## 11. The denominator theorem

A generic morphism between finite flat groups is a homomorphism between their generic Hopf algebras. Extending it integrally means proving that it introduces no denominator. The essential estimate is that a first nontrivial denominator in a $p$-primary Hopf lattice costs at least $p-1$ units of absolute ramification.

### 11.1 Integral Hopf lattices

Let $A$ be a finite-dimensional commutative Hopf algebra over $K$. An **$R$-Hopf lattice** in $A$ is a finite free $R$-subalgebra $L\subset A$ spanning $A$ over $K$ and stable under coproduct, counit, and antipode. Finite flat models of $\operatorname{Spec}A$ are equivalent to such lattices.

Suppose $L\subset L'$ are two Hopf lattices in the same $A$. Their quotient $L'/L$ is a finite-length torsion $R$-module. Put

$$
c(L,L')=\operatorname{length}_R(L'/L).
\tag{11.1}
$$

The inclusion of algebras corresponds to a morphism

$$
\operatorname{Spec}L'\longrightarrow\operatorname{Spec}L
$$

which is an isomorphism generically. It is an integral isomorphism exactly when $c(L,L')=0$.

Two preliminary reductions cost no ramification. First, strict henselization and completion are faithfully flat and preserve $e$. A lattice inclusion is an equality if and only if it becomes one after either operation. We may therefore assume that $R$ is complete and strictly henselian and that $k$ is algebraically closed. Second, translating by the identity separates constants:

$$
L=R\oplus I,\qquad L'=R\oplus I',
\tag{11.2}
$$

where $I,I'$ are the augmentation ideals. Thus every denominator occurs in the augmentation direction.

### 11.2 The first elementary modification

Put $s=\min\{r\geq1:\pi^rL'\subset L\}$. The filtration

$$
\mathcal F^jL'=L+\pi^{s-j}L'
\qquad(0\leq j\leq s)
\tag{11.3}
$$

is preserved by multiplication, coproduct, counit, and antipode. Its Rees algebra is therefore a graded Hopf algebra after reduction modulo $\pi$. The first nonzero positive graded piece generates a nontrivial finite commutative special-fiber group $P$. Choose a simple subquotient of $P$. Theorem 4.4 and algebraic closedness of $k$ identify it with

$$
\mathbf Z/p\mathbf Z,\qquad\mu_p,\qquad\text{or}\qquad\alpha_p.
\tag{11.4}
$$

We need the coefficient information carried by this simple slice, not a claim that all of $L'/L$ has rank one. The following filtered calculation is the precise bridge.

**Lemma 11.1 (filtered order-$p$ slice).** There are an integer $t\geq1$, a weight-one class $\bar x$ in a simple graded slice, and coefficients $a,b\in R$ such that:

$$
v(a)\geq0,\qquad v(b)\geq t(p-1),\qquad
v(a)+v(b)=e.
\tag{11.5}
$$

The integer $t$ is the denominator of that slice: a lift $x\in I'$ may be chosen with $X=\pi^t x\in I$ and $X\notin\pi I$ modulo older filtration terms.

**Proof strategy.** Teichmüller idempotents isolate the weight-one coordinate of the simple slice. Weight excludes every mixed coproduct degree below $p$. The first surviving multiplication and coproduct coefficients obey the same universal coefficient identity as an order-$p$ Oort--Tate group. Rescaling from $x$ to the integral coordinate $X$ then forces the coproduct coefficient to absorb $\pi^{t(p-1)}$.

**Proof.** The simple group in (11.4) is killed by $p$, hence carries its canonical $\mathbf F_p$-action. Since $p-1$ is a unit, the Teichmüller idempotents split its augmentation algebra. Choose its weight-one line and lift a generator to $x\in I'$. Let $t$ be least such that $X=\pi^t x$ belongs to the preceding filtration lattice.

Work modulo terms of older filtration degree. Multiplication and reduced coproduct have first terms

$$
x^p\equiv ax,
\qquad
\Delta x-x\otimes1-1\otimes x
\equiv bC_p(x\otimes1,1\otimes x).
\tag{11.6}
$$

Indeed a mixed monomial in the reduced coproduct has weight one. Its total degree is congruent to $1$ modulo $p-1$, so degrees $2,\ldots,p-1$ cannot occur. Terms of degree greater than $p$ lie in higher Rees degree and disappear from the first slice. The universal polynomial $C_p$ is primitive in the sense that one of its coefficients is a unit, as proved in the Oort--Tate calculation of Book 51.

The compatibility of the two formulas in (11.6) gives the universal initial-form relation

$$
ab=w_p,
\tag{11.7}
$$

at this filtered degree. Here is the coefficient check that prevents (11.7) from being an unsupported lift of the special-fiber group. Apply $\Delta$ to $x^p-ax$ and compare the coefficient corresponding to a unit coefficient of $C_p$. All terms of degree below $p$ have already vanished by weight; all terms using an older filtration factor vanish in the simple graded quotient. The remaining coefficient is a unit multiple of $w_p-ab$. Since the chosen slice is the first nonzero one, its initial form must vanish. If $v(ab)<e$, the initial form of $ab$ would survive; if $v(ab)>e$, that of $w_p$ would survive. Hence $v(ab)=v(w_p)=e$. After multiplying $x$ by a unit, the unit initial forms agree, which is (11.7) in the normalized slice. This is exactly the universal coefficient calculation, now performed in the Rees algebra rather than assumed to come from an order-$p$ group over $R$.

Because $x$ belongs to the larger Hopf lattice, its multiplication coefficient is integral, so $v(a)\geq0$. Rewrite (11.6) using $X=\pi^t x$. Homogeneity of $C_p$ gives

$$
X^p\equiv\pi^{t(p-1)}aX,
$$

and

$$
\Delta X-X\otimes1-1\otimes X
\equiv
\pi^{-t(p-1)}bC_p(X\otimes1,1\otimes X).
\tag{11.8}
$$

The smaller lattice is closed under coproduct. Since $C_p$ has a unit coefficient and $X$ is primitive in this graded slice, the last coefficient is integral. Thus $v(b)\geq t(p-1)$. Together with $v(a)+v(b)=e$, this proves (11.5). $\square$

The lemma isolates only the first simple direction of the difference. That is enough: any proper difference has such a direction, and its denominator already consumes the stated amount of ramification.

### 11.3 The ramification cost

**First-denominator consequence.** If $L\subsetneq L'$ are $p$-primary Hopf lattices as above, then

$$
e\geq p-1.
\tag{11.9}
$$

**Proof.** Apply Lemma 11.1 to the first simple graded slice. Since $t\geq1$,

$$
e=v(a)+v(b)\geq t(p-1)\geq p-1.
$$

This proves the assertion. $\square$

The direction of the rescaling is important. Enlarging the coordinate lattice replaces the multiplication parameter by a positive $(p-1)$st valuation shift and the coproduct parameter by the complementary negative shift. Their product remains a unit multiple of $p$. A nontrivial shift is possible only if absolute ramification can absorb at least $p-1$.

### 11.4 The isomorphism lemma

We can now pass from one elementary modification to an arbitrary morphism.

**Theorem 11.2 (Raynaud isomorphism lemma).** Assume $e<p-1$. Let

$$
f:\mathcal G\longrightarrow\mathcal H
$$

be a morphism of finite flat commutative $p$-power-order group schemes over $R$. If $f_K$ is an isomorphism, then $f$ is an isomorphism.

**Proof strategy.** On coordinate algebras, a generic isomorphism gives an inclusion of one Hopf lattice into another. If it is proper, the first-denominator consequence contradicts $e<p-1$.

Write $A=\mathcal O(\mathcal G)$ and $B=\mathcal O(\mathcal H)$. The pullback

$$
f^*:B\longrightarrow A
$$

is injective: its kernel becomes zero over $K$, while $B$ is $R$-torsion-free. Identify $B$ with its image. Both $A$ and $B$ are Hopf lattices in the common generic Hopf algebra.

If $B\ne A$, Sections 11.2--11.3 applied to $B\subset A$ force $e\geq p-1$, contradicting the hypothesis. Therefore $B=A$, so $f^*$ and $f$ are isomorphisms. $\square$

The proof does not use a filtration of the generic Galois module by characters. The simple object is extracted from the special-fiber obstruction, where the Dieudonné category always has finite length. This is the step that extends the order-$p$ rigidity of Book 51 to arbitrary $p$-power height.

## 12. Raynaud full faithfulness

The isomorphism lemma concerns an integral morphism already given. A generic morphism need not initially extend. Closing its graph produces the required integral intermediary; the two projections then bring the isomorphism lemma into play.

### 12.1 Closure of the generic graph

Let $\mathcal G,\mathcal H$ be finite flat commutative $p$-groups over $R$, and let

$$
u_K:\mathcal G_K\longrightarrow\mathcal H_K
$$

be a homomorphism. Its graph

$$
\Gamma_K\subset\mathcal G_K\times_K\mathcal H_K
$$

is a closed subgroup. By the schematic closure theorem of Book 51, its closure

$$
\Gamma\subset\mathcal G\times_R\mathcal H
\tag{12.1}
$$

is finite flat. The first projection

$$
q:\Gamma\longrightarrow\mathcal G
\tag{12.2}
$$

is a morphism whose generic fiber is an isomorphism. If $q$ is an isomorphism, define

$$
u=\operatorname{pr}_2\circ q^{-1}.
\tag{12.3}
$$

Then $u_K$ is the prescribed map. Thus fullness reduces exactly to the isomorphism lemma.

It is important that one closes the graph inside a finite flat ambient product. The raw schematic graph of a rational map need not have a flat projection, and extending coordinate functions one at a time need not preserve the Hopf identities. Saturated closure handles all equations simultaneously.

### 12.2 The full-faithfulness theorem

Graph closure converts existence of a rational map into the question whether one generically invertible projection is integrally invertible. The denominator theorem answers that question uniformly in the height, so the full result now has a short proof even though its input estimate was substantial.

**Theorem 12.1 (Raynaud full faithfulness below the boundary).** Let $R$ be a henselian mixed-characteristic DVR with perfect residue field of characteristic $p$, and let $e=v_R(p)$. If

$$
e<p-1,
\tag{12.4}
$$

then generic fiber is fully faithful on finite flat commutative group schemes of $p$-power order:

$$
\operatorname{Hom}_R(\mathcal G,\mathcal H)
\xrightarrow{\sim}
\operatorname{Hom}_K(\mathcal G_K,\mathcal H_K).
\tag{12.5}
$$

Equivalently, every Galois-equivariant homomorphism

$$
\mathcal G_K(K^s)\longrightarrow\mathcal H_K(K^s)
$$

extends uniquely over $R$.

**Proof.** Uniqueness is generic-fiber faithfulness from Book 42: two integral maps agreeing generically agree because the target coordinate algebra of the source is torsion-free. For existence, form the closure (12.1). The first projection is generically an isomorphism, so Theorem 11.2 makes it an integral isomorphism. Formula (12.3) gives the extension.

The equivalence with Galois modules follows from the finite étale--Galois correspondence, since both generic fibers are étale in characteristic zero. $\square$

No finiteness of $k$ is used. Perfection enters the connected--étale and Dieudonné simple-factor arguments. Henselianity suffices after passage to completion because completion is faithfully flat and preserves $e$. More explicitly, if the completed extension carries an element of the original generic Hopf algebra into the completed lattice, saturation gives

$$
(A\otimes_R\widehat R)\cap A_K=A
$$

inside $A_K\otimes_K\widehat K$. Hence the completed map descends to the original Hopf lattice; its identities descend by faithful flatness.

**Corollary 12.2 (uniqueness of models).** Under (12.4), two finite flat commutative $p$-group models of the same marked generic group are uniquely isomorphic as marked models.

**Proof.** The generic marking gives an isomorphism of generic fibers. Fullness extends it and its inverse. The two composites are the identity generically, hence integrally by faithfulness. $\square$

This is essential uniqueness as well as fullness, but not essential surjectivity. Raynaud's theorem does not say that every finite $p$-primary Galois module has a finite flat model.

### 12.3 Exact and coefficient-linear consequences

Suppose

$$
0\to\mathcal G'\to\mathcal G\to\mathcal G''\to0
$$

and

$$
0\to\mathcal H'\to\mathcal H\to\mathcal H''\to0
$$

are finite-flat exact sequences under (12.4). A morphism between their generic sequences extends term by term. The extended squares commute because they commute generically. Thus generic fiber is fully faithful as an exact functor on the declared faithfully flat exact structures.

A $G_K$-stable subgroup of $\mathcal G_K(K^s)$ has the closure model from Book 51. Under (12.4), that model is not merely unique inside $\mathcal G$: it is the unique abstract finite flat model compatible with its embedding. Any other model with the same generic embedding maps to the closure by Theorem 12.1, and equal generic ranks make the map an isomorphism.

Coefficient actions also extend automatically. Let $\Lambda$ be a finite commutative ring and suppose the generic fiber of $\mathcal G$ carries a ring homomorphism

$$
\Lambda\longrightarrow\operatorname{End}_K(\mathcal G_K).
$$

Every scalar endomorphism extends by fullness. Addition, multiplication, and the unit identity hold after generic base change, hence hold integrally by faithfulness. Therefore

$$
\Lambda\longrightarrow\operatorname{End}_R(\mathcal G)
\tag{12.6}
$$

is a unique integral coefficient action. Below the boundary, unlike in the general situation of Book 42, one does not need to replace the chosen model to make its generic coefficients integral.

Cartier duality is equally rigid. A generic pairing

$$
\mathcal G_K\times\mathcal H_K\longrightarrow\mu_{p^n,K}
$$

corresponds to a generic map $\mathcal G_K\to\mathcal H_K^D$ and extends uniquely. Perfectness may be checked generically: the adjoint map is a generic isomorphism and hence an integral isomorphism by Theorem 11.2.

### 12.4 Descent and change of base

Let $R'/R$ be an unramified extension of henselian DVRs. Then $e(R')=e(R)$, so the inequality remains valid. Base change of a finite flat group and all its morphisms is fully faithful on both sides. If an $R'$-model has a generic descent datum, each generic comparison extends uniquely by Theorem 12.1. The cocycle holds integrally because it holds generically. Effective faithfully flat descent then produces an $R$-model.

Thus, below the boundary, generic descent data are enough for a model already known to exist after an unramified extension. This strengthens the general warning of Books 42 and 51: there, generic comparisons might not preserve the integral lattice; here full faithfulness proves that they do.

For a ramified extension of index $d$, the new absolute ramification is $de$. Even if $e<p-1$, one can have $de\geq p-1$. Full faithfulness over $R$ therefore need not imply full faithfulness for all models over $R'$. Base-changed downstairs models remain rigid relative to their descent datum, but new upstairs Hopf lattices may appear.

Conversely, descent from an extension satisfying the low-ramification inequality remains effective once the generic datum descends. This is a statement about morphisms and descent of supplied objects, not a proof that a generically defined group has a model in the first place.

## 13. The ramification boundary

The inequality $e<p-1$ is not an artifact of the proof. At equality, an elementary Oort--Tate modification becomes integral, producing two models of the same generic group and a generic isomorphism whose inverse has a denominator.

### 13.1 Sharp order-$p$ counterexamples

Assume $e\geq p-1$. In the Oort--Tate normalization of Book 51, write

$$
w_p=\epsilon\pi^e,\qquad \epsilon\in R^\times.
$$

Consider

$$
(a,b)=(1,w_p)
$$

and

$$
(a',b')=(\pi^{p-1},\pi^{1-p}w_p).
\tag{13.1}
$$

The second pair is integral exactly because $e\geq p-1$. Both pairs have product $w_p$, so they define finite flat order-$p$ groups $G$ and $G'$. The coordinate substitution

$$
x'\longmapsto\pi x
\tag{13.2}
$$

is a Hopf map and becomes an isomorphism over $K$. It is not an integral isomorphism because its inverse uses $\pi^{-1}$.

Their exponents are

$$
r(G)=0,\qquad r(G')=p-1.
\tag{13.3}
$$

Thus they are nonisomorphic by the cotangent-length formula. Their generic fibers are nevertheless isomorphic by (13.2); since the first is the split constant group, both carry the same trivial generic Galois module. At $e=p-1$, $G$ is the étale endpoint and $G'$ is a multiplicative-type endpoint with exactly the unramified twist required for that generic identification. It need not be the untwisted group $\mu_p$ unless the cyclotomic character itself has the corresponding splitting.

For $p=2$, the inequality $e<p-1$ becomes $e<1$, impossible for a mixed-characteristic DVR. The dyadic family of Book 51 confirms that no nonempty low-ramification range has been lost: order-two generic groups can already have multiple integral models over an unramified dyadic base.

### 13.2 Why the inequality is strict

At equality $e=p-1$, formula (13.1) uses all available valuation: the coefficient $b'$ becomes a unit. The first-denominator estimate is therefore an equality, not a contradiction. This explains both the strict sign and the occurrence of $p-1$.

The number $p-1$ has two simultaneous origins. Representation-theoretically, it is the order of $\mathbf F_p^\times$, so a weight-one coordinate returns to weight one in degree $p$. Algebraically, rescaling $x$ by $\pi$ changes the relation coefficient in $x^p=ax$ by $\pi^{p-1}$. The Oort--Tate product $ab=w_p$ then asks the complementary coefficient to absorb $\pi^{1-p}$. Absolute ramification measures exactly whether it can.

Higher height introduces no smaller denominator. Any first difference between two higher-height lattices has a simple Dieudonné subquotient, and every such subquotient has order $p$. Therefore the first possible cost is already the order-$p$ cost. This is why the sharp higher-height theorem has the same boundary as the rank-one theorem.

### 13.3 Equal characteristic and imperfect residue fields

The mixed-characteristic hypothesis is essential. In equal characteristic $p$, one has $p=0$, so the relation $ab=w_p$ degenerates and supplies no positive valuation budget. The groups

$$
\operatorname{Spec}R[x]/(x^p-t^{i(p-1)}x)
$$

from Book 42 have the same split étale generic group and distinct integral lattices for every $i\geq0$. There is therefore no analogue of Theorem 12.1 obtained by setting $e=\infty$ or $e=0$.

Perfection of $k$ is also structural in the proof given here. It makes Witt Frobenius invertible, gives the clean Dieudonné anti-equivalence with operators (1.1), and makes reduced finite groups étale. Over an imperfect field, relative Frobenius twists cannot be suppressed and simple objects carry inseparable descent data. A more general full-faithfulness theorem may be formulated with a refined display theory, but it is not a consequence of the present argument.

The hypothesis that the groups are commutative is used by Cartier duality, Witt covectors, and the abelian extension category. Noncommutative finite flat groups require different invariants. The hypothesis of $p$-power order isolates the flexible part. Prime-to-$p$ groups are finite étale and already enjoy full faithfulness over a henselian base without the inequality.

## 14. The combined classification package

Dieudonné theory and Raynaud rigidity answer complementary questions. One classifies characteristic-$p$ fibers by operators; the other says that, below a ramification boundary, generic maps between mixed-characteristic models have no hidden denominators. Their combination is the integral language needed for finite torsion in abelian schemes.

### 14.1 A theorem ledger

Let $k$ be perfect of characteristic $p$.

1. Finite commutative $p$-group schemes over $k$ are anti-equivalent to finite-length $W(k)$-modules with semilinear $F,V$ satisfying $FV=VF=p$.

2. Group order is module length:

   $$
   |G|=p^{\operatorname{length}_W D(G)}.
   $$

3. Étale, connected, multiplicative, and local-local groups correspond respectively to $F$ bijective, $F$ nilpotent, $V$ bijective, and both $F,V$ nilpotent. Cartier duality is Matlis duality with $F$ and $V$ adjoint.

4. Compatible divisible systems of height $h$ correspond to finite free Dieudonné modules of rank $h$. Their level-$n$ groups correspond to reduction modulo $p^n$.

5. A BT$_1$ module satisfies

   $$
   \operatorname{im}F=\ker V,
   \qquad\operatorname{im}V=\ker F.
   $$

   In height two and dimension one, the geometric possibilities are the ordinary sum of étale and multiplicative lines and the unique local-local plane $I_{1,1}$.

6. For an abelian variety $A/k$,

   $$
   D(A[p^n])\simeq
   H^1_{\mathrm{cris}}(A/W(k))/p^n,
   $$

   compatibly with $F,V$, duality, endomorphisms, polarizations, and base change. Modulo $p$, the Hodge subspace is $\operatorname{im}V=\ker F$.

Now let $R$ be a henselian mixed-characteristic DVR with perfect residue field and $e=v_R(p)$.

7. If a morphism of finite flat commutative $p$-groups is a generic isomorphism and is not an integral isomorphism, its first elementary Hopf-lattice modification forces $e\geq p-1$.

8. If $e<p-1$, generic fiber is fully faithful. Every generic morphism, coefficient action, duality map, and pairing between supplied models extends uniquely.

9. The inequality is sharp. If $e\geq p-1$, Oort--Tate groups with exponents differing by $p-1$ can have isomorphic generic fibers but nonisomorphic integral models.

These results fit into the diagram

$$
\begin{array}{ccc}
\text{finite flat groups over }R
&\xrightarrow{\text{generic fiber}}&
\text{finite }G_K\text{-modules}\\
\downarrow\text{special fiber}&&\\
\text{finite groups over }k
&\xrightarrow{D}&
\text{finite Dieudonné modules.}
\end{array}
\tag{14.1}
$$

The bottom arrow is an anti-equivalence. The top arrow is fully faithful under $e<p-1$ but is not claimed essentially surjective. The left arrow is neither full nor injective on isomorphism classes in general.

### 14.2 A hypothesis ledger

The final statements are sharp only when their settings remain visible. The following ledger separates hypotheses belonging to the characteristic-$p$ classification, the abelian comparison, and the mixed-characteristic rigidity theorem.

| Assertion | Necessary setting in this book | What fails without it |
|---|---|---|
| $V$ is $\sigma^{-1}$-semilinear | perfect residue field | Witt Frobenius need not be invertible |
| finite Dieudonné anti-equivalence | finite commutative $p$-groups over a perfect field | inseparable twists require a refined theory |
| $F$-nilpotent means connected | perfect base field | reduced need not mean geometrically reduced |
| module quotient $M/p^n$ is a finite level | a supplied compatible divisible system, or a finite free Dieudonné lift | an arbitrary finite group need not embed in such a system canonically |
| BT$_1$ criterion (6.3) | level one of a compatible divisible system | $\alpha_p$ is killed by $p$ but fails the criterion |
| abelian torsion comparison | abelian scheme or abelian variety, crystalline PD base, perfect field for one Witt module | a general finite group has no ambient $H^1$ |
| perfect polarization form | principal polarization | a nonprincipal form can have finite cokernel |
| Hodge subspace equals $\operatorname{im}V$ | contravariant convention used here | covariance exchanges the displayed roles |
| first-denominator estimate | mixed characteristic, commutativity, $p$-power order | equal-characteristic additive lattices move freely |
| Raynaud full faithfulness | $e<p-1$ and perfect residue field | boundary Oort--Tate models give counterexamples |
| descent from generic comparisons | models already exist and low-ramification fullness applies after the chosen base change | existence of a generic group does not create an integral model |

Two logical boundaries deserve emphasis. Full faithfulness is not essential surjectivity: it gives uniqueness of a model and of maps once models exist, not existence for every Galois representation. Dieudonné classification is a special-fiber classification: it does not recover an arbitrary mixed-characteristic Hopf lattice from its reduction.

### 14.3 Conclusion

Finite commutative group schemes in characteristic $p$ become linear only after the coefficient ring is enlarged from $k$ to $W(k)$ and two complementary operators are retained. Frobenius detects the étale and connected directions; Verschiebung detects the multiplicative and dual-connected directions; their product remembers multiplication by $p$. Witt covectors and their extension calculus prove that no information is lost: finite groups and finite-length Dieudonné modules are anti-equivalent.

For torsion in an abelian scheme, this linear object is not new data placed beside crystalline cohomology. It is exactly the finite-level reduction of the first crystalline lattice. The universal vector extension identifies the two constructions, the Hodge subspace becomes $\operatorname{im}V=\ker F$ at level one, and the Poincaré biextension carries Weil duality into the crystalline polarization form. Ordinary and supersingular elliptic torsion then emerge from two transparent operator patterns.

Mixed characteristic adds an integral gluing problem. A generic map may appear to carry denominators, but the first possible denominator has an order-$p$ shadow on the special fiber. Dieudonné theory extracts that shadow, and the Oort--Tate relation measures its valuation cost. No nontrivial modification is possible when

$$
e<p-1.
$$

Closing the generic graph therefore turns every generic homomorphism into a unique integral one. At the boundary, the same calculation constructs the counterexamples and proves sharpness.

The resulting package is both a classification and a rigidity theorem:

$$
\text{abelian }p^n\text{-torsion}
\longleftrightarrow
H^1_{\mathrm{cris}}/p^n
\quad\text{on the special fiber},
$$

while below the ramification boundary

$$
\text{integral morphisms}
\longleftrightarrow
\text{generic Galois-equivariant morphisms}.
$$

This is the complete finite-level language needed to pass from connected special-fiber geometry to rigid generic representations without losing exactness, duality, coefficients, or the integral lattice.
