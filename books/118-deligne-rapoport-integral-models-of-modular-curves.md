# Deligne--Rapoport Integral Models of Modular Curves

## Contents

1. [The integral question at a level prime](#1-the-integral-question-at-a-level-prime)
   - [What changes at the residue characteristic](#11-what-changes-at-the-residue-characteristic)
   - [The three versions of the model](#12-the-three-versions-of-the-model)
   - [Standing hypotheses and notation](#13-standing-hypotheses-and-notation)
   - [The main geometric picture](#14-the-main-geometric-picture)
2. [Deformations of elliptic curves and cyclic isogenies](#2-deformations-of-elliptic-curves-and-cyclic-isogenies)
   - [One parameter for an elliptic curve](#21-one-parameter-for-an-elliptic-curve)
   - [Ordinary and supersingular $p$-torsion](#22-ordinary-and-supersingular-p-torsion)
   - [The isogeny deformation lemma](#23-the-isogeny-deformation-lemma)
   - [Why the crossing equation is exact](#24-why-the-crossing-equation-is-exact)
3. [The integral prime-level moduli problem](#3-the-integral-prime-level-moduli-problem)
   - [Ample cyclic subgroups](#31-ample-cyclic-subgroups)
   - [Closure from the generic modular curve](#32-closure-from-the-generic-modular-curve)
   - [Agreement with the modular functor](#33-agreement-with-the-modular-functor)
   - [Properness, flatness, and projectivity](#34-properness-flatness-and-projectivity)
4. [Smoothness and regularity away from the level](#4-smoothness-and-regularity-away-from-the-level)
   - [The smooth elliptic locus](#41-the-smooth-elliptic-locus)
   - [Cusp charts away from $p$](#42-cusp-charts-away-from-p)
   - [From fine curves to stacks and coarse curves](#43-from-fine-curves-to-stacks-and-coarse-curves)
   - [The good-prime theorem](#44-the-good-prime-theorem)
5. [The two ordinary strata in characteristic $p$](#5-the-two-ordinary-strata-in-characteristic-p)
   - [Connected and etale directions](#51-connected-and-etale-directions)
   - [Frobenius and Verschiebung sections](#52-frobenius-and-verschiebung-sections)
   - [Exhaustion of the ordinary fiber](#53-exhaustion-of-the-ordinary-fiber)
   - [Closures and their normalizations](#54-closures-and-their-normalizations)
6. [Supersingular points and the crossing theorem](#6-supersingular-points-and-the-crossing-theorem)
   - [The unique special subgroup](#61-the-unique-special-subgroup)
   - [The completed local ring](#62-the-completed-local-ring)
   - [Regularity and the node](#63-regularity-and-the-node)
   - [Hypotheses at small primes](#64-hypotheses-at-small-primes)
7. [The global two-component special fiber](#7-the-global-two-component-special-fiber)
   - [Gluing the local branches](#71-gluing-the-local-branches)
   - [The semistable model theorem](#72-the-semistable-model-theorem)
   - [Geometric connectedness and genus](#73-geometric-connectedness-and-genus)
8. [Igusa curves and normalized component covers](#8-igusa-curves-and-normalized-component-covers)
   - [Why generators reappear on a normalization](#81-why-generators-reappear-on-a-normalization)
   - [The Igusa torsor on the ordinary locus](#82-the-igusa-torsor-on-the-ordinary-locus)
   - [Ramification at supersingular points](#83-ramification-at-supersingular-points)
   - [Prime-level generator refinements](#84-prime-level-generator-refinements)
9. [Degeneracy maps on the components](#9-degeneracy-maps-on-the-components)
   - [Source and quotient](#91-source-and-quotient)
   - [The four restrictions](#92-the-four-restrictions)
   - [Finiteness and inseparability](#93-finiteness-and-inseparability)
   - [Compatibility with Igusa structures](#94-compatibility-with-igusa-structures)
10. [Cusps in the integral model](#10-cusps-in-the-integral-model)
    - [The two prime-level cusp charts](#101-the-two-prime-level-cusp-charts)
    - [Regularity at the boundary](#102-regularity-at-the-boundary)
    - [Degeneracy formulas at the cusps](#103-degeneracy-formulas-at-the-cusps)
11. [Component intersections and the dual graph](#11-component-intersections-and-the-dual-graph)
    - [Local intersection multiplicities](#111-local-intersection-multiplicities)
    - [Self-intersections from the fiber relation](#112-self-intersections-from-the-fiber-relation)
    - [The intersection matrix](#113-the-intersection-matrix)
    - [The graph and its arithmetic meaning](#114-the-graph-and-its-arithmetic-meaning)
12. [Coarse quotients and exceptional automorphisms](#12-coarse-quotients-and-exceptional-automorphisms)
    - [Effective actions on a crossing](#121-effective-actions-on-a-crossing)
    - [Thick quotient nodes and their resolution](#122-thick-quotient-nodes-and-their-resolution)
    - [What remains two-component](#123-what-remains-two-component)
    - [Descent of the global model](#124-descent-of-the-global-model)
13. [The Deligne--Rapoport package](#13-the-deligne--rapoport-package)
    - [The main theorem](#131-the-main-theorem)
    - [A calculation protocol](#132-a-calculation-protocol)
    - [Failure modes and hypothesis ledger](#133-failure-modes-and-hypothesis-ledger)
    - [Conclusion](#134-conclusion)

## 1. The integral question at a level prime

### 1.1 What changes at the residue characteristic

Over a field in which the level is invertible, a cyclic subgroup of order $p$ is a set of $p$ distinct torsion points, at least after a separable extension. The map that forgets the subgroup is finite etale on the smooth ordinary moduli problem, and the compactified curve is locally a one-parameter family at each cusp. None of this description survives unchanged in characteristic $p$. A subgroup of rank $p$ can be connected, all of its geometric points can collide at the identity, and the map that was generically etale can become purely inseparable on an entire component.

The special fiber is nevertheless remarkably controlled. For an ordinary elliptic curve there are two limiting directions for a cyclic subgroup: the connected subgroup $\ker(F)$ and the etale subgroup dual to it. At a supersingular elliptic curve these directions coalesce. The coalescence is transverse in the total moduli surface. Thus the characteristic-$p$ fiber has two smooth components meeting at the supersingular points.

This statement contains several logically different assertions. One must first construct a proper integral model, rather than merely draw the desired fiber. One must prove that the two ordinary strata have no hidden third branch. One must calculate the completed local ring at their common supersingular limit. Finally one must distinguish a stack node or a node on a rigidified fine cover from its image on a coarse quotient. The purpose of this book is to prove all four assertions and connect them to degeneracy maps, Igusa curves, and intersection theory.

### 1.2 The three versions of the model

The compactified theory of Book 117 separated three spaces. The same separation is even more important at a level prime:

$$
Y_0(p;M)\longrightarrow
\overline{\mathcal M}_0(p)
\longrightarrow X_0(p).
\tag{1.1}
$$

Here $M\geq3$ is prime to $p$ and denotes an auxiliary full level, or any equivalent prime-to-$p$ rigidifying datum. The left side is a fine moduli scheme: it has no stabilizers and carries a universal generalized elliptic curve. The middle is the moduli stack of generalized elliptic curves with an ample cyclic subgroup of rank $p$. The right side is the coarse curve.

The clean local equation

$$
xy=p
\tag{1.2}
$$

belongs literally to the fine cover and, in the stack sense, to the middle space. A stabilizer can act nontrivially on $x$ and $y$. Its invariant ring need not again have equation (1.2). Consequently the stable coarse special fiber can still have two principal components while the regular resolution of the coarse surface contains additional exceptional curves. Any statement that calls all three spaces “the modular curve” without a qualifier loses this distinction.

Our main construction is therefore made first with rigidifying level. The result descends to the stack. Coarse invariant rings are then calculated separately. This order makes the two-component theorem exact instead of concealing quotient singularities.

### 1.3 Standing hypotheses and notation

Fix a prime $p$. Let $R$ be either $\mathbf Z_{(p)}$, a strict henselization of it, or an unramified complete discrete valuation ring of mixed characteristic $(0,p)$ with perfect residue field $k$. Its uniformizer is denoted $p$. All geometric special-fiber statements are understood after extending $k$ to an algebraic closure.

Let $\mathcal P$ be a prime-to-$p$ rigidifying **branch cover** satisfying the following conditions:

1. it is finite etale over the smooth elliptic moduli stack;
2. its compactification is the normalization of the projective closure of that smooth cover, as in Book 117;
3. it kills automorphisms; and
4. its compactified fine moduli curve $X(\mathcal P)$ is smooth over $R$.

Full level $M\geq3$ with $(M,p)=1$, over the appropriate cyclotomic coefficient ring if a symplectic pairing is fixed, is the standard example. The word “branch” is essential. At a cusp the auxiliary basis is a label on a normalization branch; it is not required to remain a second ample level divisor on the same polygon. Requiring simultaneous ampleness would be impossible when the two level orders are coprime, because full level $M$ forces an $M$-gon while ample cyclic level $p$ forces a one-gon or a $p$-gon.

Write $X(\mathcal P)$ for the normalized compactification of the auxiliary cover of the unlevelled smooth modular curve. We write $\mathscr X=X_0(p;\mathcal P)$ for the normalization of the prime-level generic cover in its projective closure. On the dense smooth locus it classifies triples

$$
(E,\alpha,C),
\tag{1.3}
$$

where $\alpha$ is the auxiliary prime-to-$p$ basis and $C\subset E[p]$ is cyclic of rank $p$. At the boundary, the object is a generalized elliptic curve with an ample cyclic subgroup $C$, together with the selected normalization branch of the auxiliary cover. The branch label kills automorphisms but is not an additional subgroup divisor on $E$. The two degeneracy maps are

$$
\pi_1(E,\alpha,C)=(E,\alpha),\qquad
\pi_2(E,\alpha,C)=(E/C,\alpha/C),
\tag{1.4}
$$

where contraction is inserted at the boundary. On the dense smooth locus, $\alpha/C$ is the transported prime-to-$p$ basis. The maps extend uniquely to the normalized boundary branches. This formulation retains the useful fine cover without imposing incompatible boundary ampleness conditions.

Write $X_k=X(\mathcal P)_k$. Its finite reduced supersingular divisor is denoted

$$
\mathrm{SS}=\sum_s[s].
\tag{1.5}
$$

Over a nonalgebraically closed field, every intersection sum below includes the factor $[\kappa(s):k]$. The terms “component” and “node” without a descent qualifier refer to the geometric special fiber.

### 1.4 The main geometric picture

The special fiber of $\mathscr X$ will be written

$$
\mathscr X_k=C_F\cup C_V.
\tag{1.6}
$$

Both components have normalization $X_k$. On the first, the subgroup is $\ker(F_E)$; on the second it is the kernel of Verschiebung on a Frobenius twist. They meet exactly above $\mathrm{SS}$, once and transversely at every geometric supersingular point. The degeneracy maps restrict as

$$
\begin{array}{c|cc}
&\pi_1&\pi_2\\ \hline
C_F&\operatorname{id}&F_{X_k}\\
C_V&F_{X_k}&\operatorname{id}.
\end{array}
\tag{1.7}
$$

Here $F_{X_k}$ is the absolute Frobenius after the usual identification of the Frobenius-twisted moduli curve with $X_k$ over a perfect field. The table is the global shadow of the two maps $F:E\to E^{(p)}$ and $V:E^{(p)}\to E$.

The local and global pictures agree as follows:

```text
             C_F
              \
               \  supersingular node
                +
               /
              /
             C_V
```

At the node, $C_F$ is $x=0$, $C_V$ is $y=0$, and the arithmetic surface is $xy=p$. Away from the nodes, precisely one of $x,y$ is invertible and the corresponding subgroup has ordinary connected or etale type. The rest of the book turns this picture into a theorem.

## 2. Deformations of elliptic curves and cyclic isogenies

### 2.1 One parameter for an elliptic curve

The special fiber can only be understood after the local moduli problem is known. The first input is that an elliptic curve with rigidifying prime-to-$p$ level has one deformation parameter.

Let $E_0/k$ be an elliptic curve and let $A$ range over complete noetherian local $R$-algebras with residue field $k$. A deformation of $E_0$ is an elliptic curve $E/A$ with an identification of its special fiber with $E_0$. Prime-to-$p$ level lifts uniquely once the curve lifts, because its torsion is finite etale and finite etale objects are invariant under nilpotent thickening.

**Proposition 2.1 (elliptic deformation ring).** If the chosen prime-to-$p$ level kills automorphisms, the deformation functor of $(E_0,\alpha_0)$ is represented by

$$
R[[t]].
\tag{2.1}
$$

Its tangent space is canonically dual to $H^0(E_0,\omega_{E_0}^{\otimes2})$, hence is one-dimensional.

**Proof.** Cover $E_0$ by affine opens and lift one Weierstrass equation. For a square-zero extension $A'\twoheadrightarrow A$ with kernel $I$, changes in the gluing maps form Cech $1$-cocycles with values in the tangent sheaf $T_{E_0}$. Obstructions lie in $H^2(E_0,T_{E_0})$, which vanishes because $E_0$ is a curve. Isomorphism classes of lifts are therefore a torsor under

$$
H^1(E_0,T_{E_0})\otimes_k I.
$$

The invariant differential trivializes $T_{E_0}$ up to the Hodge line, and Serre duality identifies the dual of $H^1(T_{E_0})$ with $H^0(\omega_{E_0}^{\otimes2})$, a one-dimensional space. Thus the functor is formally smooth of relative dimension one. A Weierstrass family gives an effective algebraic lift through every infinitesimal order, and completeness gives a universal formal family. Rigidifying level removes infinitesimal and finite automorphisms, so the hull is a representing ring rather than merely a versal quotient. Hence it is a one-variable power-series ring over $R$. $\square$

The choice of $t$ is not canonical. What is canonical is the smooth one-dimensional formal base. Near a supersingular point we shall select a parameter by the coefficient of the height-one term of the formal multiplication law; this choice makes the crossing equation visible.

### 2.2 Ordinary and supersingular $p$-torsion

The connected--etale theory of Book 56 gives the correct first division of cases. Over an algebraically closed field of characteristic $p$, an ordinary elliptic curve has

$$
0\longrightarrow\ker(F_E)\longrightarrow E[p]
\longrightarrow\ker(F_E)^D\longrightarrow0,
\tag{2.2}
$$

with $\ker(F_E)\simeq\mu_p$ and etale quotient $\mathbf Z/p\mathbf Z$. A supersingular elliptic curve has connected $E[p]$ and connected dual. Its $a$-number is one:

$$
\dim_k\operatorname{Hom}(\alpha_p,E[p])=1.
\tag{2.3}
$$

We recall why (2.3) is special to elliptic curves. The differential of Frobenius on an elliptic curve is zero, while its degree is $p$, so $\ker(F)$ has rank $p$. In the supersingular case it is local-local and hence is $\alpha_p$. Any local-local subgroup of rank $p$ maps into the simultaneous kernel of Frobenius and Verschiebung on the covariant tangent-conormal pair. That simultaneous kernel is one-dimensional because $H^0(E,\Omega^1)$ is one-dimensional. Therefore every such subgroup equals $\ker(F)$. In the ordinary case, the simultaneous local-local kernel is zero and the two endpoint types are distinct.

The following classification is the form needed later.

**Proposition 2.2.** Let $E/k$ be an elliptic curve and let $C\subset E[p]$ be cyclic of rank $p$ in the divisor-theoretic sense.

1. If $E$ is ordinary and $k$ is algebraically closed, $C$ is either $\ker(F_E)$ or the unique etale order-$p$ subgroup.
2. If $E$ is supersingular, $C=\ker(F_E)\simeq\alpha_p$.

**Proof.** For an ordinary elliptic curve over a perfect field, relative Frobenius and Verschiebung split the height-one connected and etale directions after passing to an algebraic closure:

$$
E[p]\simeq \mu_p\oplus\mathbf Z/p\mathbf Z.
$$

One way to see the splitting without choosing an isomorphism $E\simeq E^{(p)}$ is to apply Verschiebung to the inverse Frobenius twist $E^{(p^{-1})}$; its kernel maps etale-isomorphically onto the maximal etale quotient of $E[p]$. Moreover

$$
\operatorname{Hom}(\mathbf Z/p\mathbf Z,\mu_p)=0
$$

over an algebraically closed field of characteristic $p$, since a homomorphism is determined by a $k$-point of $\mu_p$, and its only such point is the identity. Thus the etale complement is unique.

Now project $C$ to the maximal etale quotient. The scheme-theoretic image has rank $1$ or $p$. In the first case $C$ lies in the connected subgroup of rank $p$ and equals $\ker F_E$. In the second case the projection is an isomorphism and $C$ is the unique etale complement.

If $E$ is supersingular, both $E[p]$ and its dual are connected, so every order-$p$ subgroup is local-local and hence isomorphic to $\alpha_p$. Such subgroups are the images of nonzero maps $\alpha_p\to E[p]$. The space of those maps killed by both Frobenius and Verschiebung is the $a$-number space; for a supersingular elliptic curve it is one-dimensional. All nonzero vectors in that one-dimensional space have the same image, namely $\ker F_E$. This proves uniqueness. Finally, all three groups $\mu_p$, $\mathbf Z/p\mathbf Z$, and $\alpha_p$ are cyclic in the Drinfeld divisor sense established in Book 116, so the subgroup classification applies to the present moduli problem. $\square$

The uniqueness at a supersingular point is exactly why two ordinary components can meet there without producing a third component.

### 2.3 The isogeny deformation lemma

We now calculate the decisive local ring. Begin with the deformation functor of a degree-$p$ isogeny

$$
\phi:E\longrightarrow E'
\tag{2.4}
$$

reducing to the supersingular Frobenius isogeny. On a complete local hull, the two Hodge lines are free. Choose trivializations $\eta$ and $\eta'$ lifting fixed special-fiber differentials. These are choices of coordinates on the hull, not extra data in the deformation problem. There are unique functions $x,y$ such that

$$
\phi^*\eta'=x\eta,
\qquad
\widehat\phi^*\eta=y\eta'.
\tag{2.5}
$$

Since $\widehat\phi\phi=[p]$ and $[p]^*\eta=p\eta$, they satisfy

$$
xy=p.
\tag{2.6}
$$

The content of the local theorem is that this is the only relation.

**Theorem 2.3 (isogeny deformation lemma).** Let $\phi_0:E_0\to E_0'$ be a degree-$p$ isogeny between supersingular elliptic curves over a perfect field $k$, with kernel $\alpha_p$. The isomorphism-class deformation functor has hull

$$
R[[x,y]]/(xy-p).
\tag{2.7}
$$

after choosing local trivializations of the Hodge lines. With prime-to-$p$ rigidifying branch data that kill automorphisms, this hull represents the deformation functor. Changing the Hodge trivializations changes $x$ and $y$ by inverse units and leaves the isomorphism class of the ring and the two ideals $(x)$ and $(y)$ unchanged.

**Proof strategy.** The relation (2.6) is forced by the dual isogeny. The real issue is versality: one must show that the formal-group equations determine the two elliptic deformations and all higher coefficients from $x,y$, without making an illicit division by $p$. We isolate the precise coefficient calculation and then algebraize its kernel.

**Formal-group coefficient lemma.** Let $G_0$ and $G_0'$ be one-dimensional height-two formal groups over a perfect field, and let $f_0:G_0\to G_0'$ and $g_0:G_0'\to G_0$ be dual height-one isogenies with $g_0f_0=[p]$. After fixing invariant differentials, the functor of simultaneous deformations $(G,G',f,g)$ with $gf=[p]$ is represented by

$$
W(k)[[x,y]]/(xy-p),
$$

where $x$ and $y$ are the linear coefficients of $f$ and $g$.

**Proof of the coefficient lemma.** We give the recursion carefully enough to identify every possible denominator. In total degree $n$, the associativity equation says that the undetermined homogeneous part of a one-dimensional formal group law is a symmetric additive $2$-cocycle. Changing the coordinate by $T\mapsto T+cT^n$ changes it by

$$
c\big((S+T)^n-S^n-T^n\big).
$$

The ideal generated by the intermediate binomial coefficients $\binom ni$, $0<i<n$, is the unit ideal in $\mathbf Z_{(p)}$ unless $n$ is a power of $p$; when $n=p^r$ its only nonunit common factor is $p$. Indeed a prime divides all those coefficients exactly when $n$ is a power of that prime. Consequently strict coordinate changes eliminate every non-$p$-power homogeneous term without dividing by $p$, while at each degree $p^r$ precisely one scalar coefficient remains. This is the elementary one-dimensional $p$-typicalization recursion.

Now impose the fixed height-two reduction. The identities $[p]_G(F_G(S,T))=F_G([p]_G(S),[p]_G(T))$ and associativity allow the coefficient of $T^{p^2}$ in the special $p$-series to be normalized to a unit. At degree $p$, one coefficient $u$ remains free. At every later $p$-power degree, the new coefficient occurs linearly with that height-two unit, so it is determined by the lower coefficients. This proves, rather than assumes, the usual height-two normal form and gives the deformation ring $W(k)[[u]]$ for one formal group. After a finite unramified scalar extension, normalize likewise the unit coefficients of $T^p$ in $f_0$ and $g_0$ by changing target coordinates. Write

$$
f(T)=xT+T^p+\sum_{r\geq2}a_rT^{p^r},
\qquad
g(T')=yT'+(T')^p+\sum_{r\geq2}b_r(T')^{p^r}.
\tag{2.8}
$$

These are $p$-typical expressions: the displayed ordinary powers abbreviate the corresponding terms in the chosen formal-group coordinates. Compare, in increasing $p$-power degree, the identities

$$
f(F_G(S,T))=F_{G'}(f(S),f(T)),
\quad
g(F_{G'}(S,T))=F_G(g(S),g(T)),
\quad
g(f(T))=[p]_G(T).
\tag{2.9}
$$

The degree-one coefficient of the last identity is $xy=p$. At degree $p$, the first two identities express the free coefficients of $G$ and $G'$ in terms of $x,y$. Suppose the laws and maps are known below degree $p^r$. Insert the next law, map, and residual strict-coordinate coefficients into (2.9), and order them by source law, $f$, target law, and $g$. Modulo the maximal ideal the system is triangular after the coordinate-change coefficient has removed the coboundary term. Every diagonal entry is a power of one of three special-fiber coefficients: the coefficient of $T^p$ in $f_0$, that in $g_0$, or the coefficient of $T^{p^2}$ in $g_0f_0=[p]_{G_0}$. Each is a unit. The new coefficients are therefore uniquely determined over every infinitesimal thickening. The composite identity is automatic in the next degree after this comparison: its difference from $[p]_G$ is an endomorphism whose first possible coefficient is killed by the same height-two unit. Induction constructs a compatible system to every order.

Conversely, every deformation can be put into such normalized coordinates by the preceding strict-coordinate recursion. Residual strict changes act triangularly on the already determined coefficients, so they give isomorphic systems rather than additional parameters. The linear coefficients satisfy only $xy=p$, and the unit-determinant induction recovers the isomorphism class from them. Passing to inverse limits is valid because at the $r$th stage only finitely many coefficients occur. Galois descent from the harmless unramified scalar extension only rescales $x$ and $y$ by inverse units, so the descended ring is again $W(k)[[x,y]]/(xy-p)$. This proves the coefficient lemma. Notice that the height-two unit, not a division by $p$, is the decisive step.

**Proof of the theorem.** We first justify passage between elliptic curves and formal groups in precisely this supersingular case. For a square-zero extension with kernel $I$, lifts of an elliptic curve form a torsor under $H^1(E_0,T_{E_0})\otimes I$, as in Proposition 2.1. The same $p$-typical recursion with no isogeny present shows that lifts of its one-dimensional height-two formal group have one free first coefficient and no obstruction; its deformation ring is therefore $R[[u]]$. Completion defines a natural transformation from elliptic deformations to formal-group deformations, hence a homomorphism $R[[u]]\to R[[t]]$ of their representing rings. On tangent spaces its linear part is pairing with the square of a nonzero invariant differential: changing a Cech gluing derivation changes the coefficient of $T^p$ by exactly that pairing. Since

$$
H^1(E_0,T_{E_0})^\vee\simeq H^0(E_0,\omega_{E_0}^{\otimes2})
$$

and the last space is generated by that square, the linear coefficient of the resulting homomorphism $R[[u]]\to R[[t]]$ is a unit. The formal inverse-function recursion now constructs an inverse power series coefficient by coefficient. Completion therefore identifies the two deformation functors, not merely their tangent spaces. The effective Weierstrass construction in Proposition 2.1 algebraizes the inverse system. Prime-to-$p$ rigidifying level lifts uniquely and adds no deformation parameter.

Apply the coefficient lemma to the formal completions of $E_0,E_0'$ and to $\phi_0,\widehat\phi_0$. The comparison just proved brings the resulting source and target formal groups from unique elliptic deformations, and gives the claimed hull $B=R[[x,y]]/(xy-p)$.

It remains to check that the formal isogeny is an elliptic isogeny rather than only a homomorphism of completions. The power series $f(T)$ reduces to a unit times $T^p$. Weierstrass preparation therefore cuts out a finite locally free rank-$p$ subgroup $C$ of the formal neighborhood of the identity. Translation of its defining Cartier divisor by the formal group law shows that $C$ is a subgroup. The closed immersion of the formal neighborhood into the completed elliptic curve places it in $E[p]$, and the finite-subgroup quotient theorem gives an elliptic curve $E/C$ and an isogeny $E\to E/C$. Its formal completion is the constructed target $G'$. Two proper elliptic deformations with the same completed group and special-fiber identification are uniquely isomorphic, so $E/C\simeq E'$. This algebraizes $f$, and its quotient dual algebraizes $g$.

Finally, a change $\eta\mapsto u\eta$, $\eta'\mapsto u'\eta'$ sends $x$ to $u'u^{-1}x$ and $y$ to $u(u')^{-1}y$. Thus it preserves $xy=p$ and the branch ideals, proving independence of the trivializations. $\square$

The proof is a one-dimensional calculation; it does not assume a later theory of deformations of higher-dimensional abelian varieties. Its height-two step is precisely where supersingularity enters.

### 2.4 Why the crossing equation is exact

The same equation can be read from the order-$p$ kernel. Book 56 associates to a finite flat group of order $p$ complementary Oort--Tate parameters $a,b$ with

$$
ab=w_p,
\qquad w_p/p\in R^\times.
\tag{2.10}
$$

After changing a frame, the harmless unit $w_p/p$ can be absorbed into one parameter. For the kernel of $\phi$, $a$ measures the pullback on invariant differentials of $\phi$; for the Cartier-dual kernel, $b$ measures the pullback for $\widehat\phi$. Thus (2.10) becomes (2.6).

This interpretation explains the two branches. Modulo $p$,

$$
xy=0.
\tag{2.11}
$$

On $x=0$ with $y\ne0$, the kernel is multiplicative and $\phi$ is Frobenius-like. On $y=0$ with $x\ne0$, the dual kernel is multiplicative, so the original kernel is etale and $\phi$ is Verschiebung-like. At $x=y=0$ both kernel and dual are local, which is the supersingular point.

There is no circular use of semistability here. Equation (2.7) is obtained from the isogeny deformation problem. Regularity and the nodal special fiber will be consequences of that equation in Chapter 6.

## 3. The integral prime-level moduli problem

### 3.1 Ample cyclic subgroups

The local equation is useful only after it is attached to a global moduli object. The correct object is not an elliptic curve with a pointwise cyclic set. It is a generalized elliptic curve with an ample finite subgroup divisor.

For an $R$-scheme $S$, define $\mathscr F_0(p)(S)$ to be the groupoid of pairs $(E,C)$ in which:

- $E/S$ is a generalized elliptic curve;
- $C\subset E^{\mathrm{sm}}$ is finite locally free of rank $p$, killed by $p$, and fppf-locally generated in the Drinfeld divisor sense; and
- the divisor $C$ meets every geometric irreducible component of $E$.

The last condition is relative ampleness. On a smooth elliptic curve it is automatic. At a cusp it forces, because $p$ is prime, either the one-gon with $C=\mu_p$ or the $p$-gon with $C$ mapping isomorphically to its component group. This is exactly the boundary dichotomy proved in Book 116.

Every clause survives arbitrary base change. Finite locally free subgroup schemes descend, the generator equation is equality of monic Cartier divisors, and ampleness is faithfully flat local. Hence $\mathscr F_0(p)$ is an fppf stack. It retains inversion and possibly exceptional automorphisms. To obtain a fine scheme, add $\mathcal P$ only on the dense smooth locus and normalize its closure over this stack. Book 117's boundary rigidity shows that no automorphism appears on a chosen normalization branch.

We need two global facts before taking that cover.

**Proposition 3.1 (integral stack).** The stack $\mathscr F_0(p)$ is algebraic, proper, and of finite presentation over $R$, with finite separated diagonal.

**Proof.** Algebraicity and finite presentation use exactly the integral parameter spaces constructed in Book 116. The ample degree-$p$ divisor bounds the polygon size by $p$. A sufficiently high multiple embeds every fiber; generalized-elliptic actions and finite subgroup divisors are imposed in a finite union of Hilbert schemes, while Drinfeld generation is equality of monic divisor equations. The isomorphism functor is a closed subfunctor of the bounded projective isomorphism scheme. Ampleness rules out contractions in a level-preserving generic isomorphism, so the valuative criterion makes that diagonal proper; it is also quasi-finite, hence finite.

For properness, use the stack-valuative criterion. After a finite extension of a valuation field, an elliptic curve has good or split multiplicative reduction, as proved in Book 117. In the good case the generic subgroup closes inside the fixed finite-flat group $E[p]$; Book 56 proves that this closure $C$ is finite flat. After one further finite extension, choose a Drinfeld generator $P_K$ of the generic subgroup. Properness of the good elliptic model extends it to a section $P$, and separatedness extends $[p]P_K=0$ to $[p]P=0$. The relative Cartier divisor

$$
D=\sum_{a\in\mathbf Z/p\mathbf Z}[aP]
$$

is finite flat of degree $p$ and has generic fiber $C_K$. It is therefore the schematic closure of $C_K$, so $D=C$ and cyclicity extends. In the multiplicative case, Tate uniformization measures the component image of the generic cyclic group. Its order is $1$ or $p$. The first choice gives the one-gon with subgroup $\mu_p$; the second gives the $p$-gon with the component subgroup. Book 116 proves that these are the two exhaustive ample extensions. Uniqueness follows because the level divisor has positive degree on every component: the generalized curve is recovered from a high power of its ample level line, and the subgroup is the schematic closure inside the smooth torsion. Thus the valuative existence and uniqueness conditions hold. $\square$

Now apply the finite auxiliary-decontraction construction of Book 117 with a full level $M\geq3$ prime to $p$. It is important that the full $M$-basis lives on its decontracted auxiliary curve and that its contraction to $(E,C)$ is retained; simultaneous ampleness on the same polygon is not required. The resulting cover is representable and finite over $\mathscr F_0(p)$. Full level $M$ kills its object automorphisms. It is therefore a proper fine scheme, and its Hilbert construction makes it projective. Normalize it in its generic function algebra. Excellence makes the normalization finite, so the result remains a projective fine scheme. This normalized scheme is what we denote by $\mathscr X$.

### 3.2 Closure from the generic modular curve

There are two compatible constructions, and comparing them is a valuable correctness check. Take the generic fine curve $X_0(p;\mathcal P)_{\mathbf Q}$ obtained by adjoining the auxiliary basis to the smooth prime-level problem. Embed it projectively, form its schematic closure over $R$, remove base torsion, and normalize in the generic function field. Book 10 proves that this normalization is finite because $R$ is excellent. Denote the resulting normal projective flat curve by

$$
\mathscr X^{\mathrm{nor}}.
\tag{3.1}
$$

The fine cover constructed in Section 3.1 gives a projective closure of the same generic curve together with its map to $\mathscr F_0(p)$. Normalizing it and normalizing any other projective closure both mean taking the integral closure in the same finite product of generic function fields. The universal property of normalization therefore gives a unique isomorphism

$$
\mathscr X^{\mathrm{nor}}\simeq\mathscr X.
\tag{3.2}
$$

This comparison is the safe way to obtain the integral moduli map. A rational map from a normal surface need not extend across codimension two merely because it extends at height one; Book 10's example $[x:y]:\mathbf A^2\dashrightarrow\mathbf P^1$ shows why that shortcut is false. Here the morphism exists before normalization, on the finite auxiliary moduli cover, and hence survives normalization by composition. A point over a cusp remembers the decontracted auxiliary full-level curve and its contraction, equivalently the selected normalization branch.

### 3.3 Agreement with the modular functor

The preceding construction is intrinsic, not tied to an embedding.

**Proposition 3.2.** The normal closure $\mathscr X^{\mathrm{nor}}$ is the normalized $\mathcal P$-branch cover of $\mathscr F_0(p)$. It is independent of the chosen projective embedding and carries a finite representable map to the stack.

**Proof.** The auxiliary decontraction cover is finite and representable before normalization. Normalization is finite by excellence, so its composite with the cover remains finite and representable. Its generic fiber is the prescribed auxiliary cover. If another projective embedding is used, normalize the closure of the diagonal generic curve in the product of the two projective closures. Each projection is finite because both targets are already integral closures in the same generic algebra; the finite birational maps to the two normal targets are isomorphisms. This proves independence.

Over a valuation ring, the modular meaning agrees with schematic closure. In the good case $C$ is the unique closure inside $E[p]$; at a cusp its component image selects the one-gon or $p$-gon, and the auxiliary decontraction selects the branch. These are checks on the already constructed finite cover, not an attempted codimension-two extension principle. $\square$

The construction uses schematic closure only inside the fixed ambient group $E[p]$. It does not claim that an abstract generic cyclic group has a unique integral model; Book 56 shows that such a claim would be false over a ramified base.

### 3.4 Properness, flatness, and projectivity

**Theorem 3.3.** The integral prime-level model $\mathscr X$ is projective, proper, flat, and normal over $R$. Its generic fiber is the compactified modular curve $X_0(p;\mathcal P)_{\mathbf Q}$.

**Proof.** Projectivity and normality come from the normalized projective closure. The coordinate ring of every affine chart injects into its generic fiber, so it is $R$-torsion-free; over a discrete valuation ring this is flatness. Properness follows from projectivity.

For a direct valuative check, let $K'/K$ be a finite extension and begin with a generic elliptic curve, cyclic subgroup, and auxiliary basis. Potential good or split multiplicative reduction extends the underlying curve after replacing the valuation ring by its normalization. In the good case, close the generic subgroup in $E[p]$; saturation makes it finite flat. In the multiplicative case, its component image has order $1$ or $p$ and selects the corresponding Tate one-gon or $p$-gon. The divisor is ample on that polygon. Uniqueness follows from closure in the good case and from the component-image calculation in the Tate case. Integral closure extends the auxiliary generic basis as a branch label. This verifies the same proper object moduli-theoretically. $\square$

Normality is still weaker than the regularity promised by the title. The remaining chapters compute every completed local ring and thereby upgrade the model.

## 4. Smoothness and regularity away from the level

### 4.1 The smooth elliptic locus

Before analyzing the bad prime, we record exactly why other primes are good. Let $\ell\ne p$ and work over a geometric point of residue characteristic $\ell$. Multiplication by $p$ on an elliptic curve is etale. Hence $E[p]$ is finite etale of rank $p^2$, and cyclic subgroups are locally constant lines in a two-dimensional $\mathbf F_p$-space.

Fixing one such line introduces no infinitesimal deformation. More precisely, for a nilpotent thickening $S_0\hookrightarrow S$, finite etale group schemes over $S$ and $S_0$ are equivalent. A cyclic subgroup of $E_0[p]$ therefore lifts uniquely to a cyclic subgroup of $E[p]$. Prime-to-$p$ rigidifying level also lifts uniquely. The completed local deformation ring of $(E,\alpha,C)$ is consequently the same one-variable smooth ring as that of $(E,\alpha)$.

**Proposition 4.1.** On the smooth elliptic locus over $R[1/p]$, the map

$$
\pi_1:\mathscr X[1/p]\longrightarrow X(\mathcal P)[1/p]
$$

is finite etale. In particular $\mathscr X[1/p]$ is smooth over the base wherever $X(\mathcal P)$ is smooth.

**Proof.** Since $E[p]$ is finite etale, it becomes the constant group $(\mathbf Z/p\mathbf Z)^2$ after an etale cover. Its cyclic rank-$p$ subgroups are then the $p+1$ constant lines, so the subgroup functor is finite etale and this property descends. Formal etaleness is also the unique lifting statement just proved. Smoothness is preserved by etale base change. $\square$

### 4.2 Cusp charts away from $p$

The boundary requires its own calculation because the underlying curve is no longer elliptic. Book 116 gives two prime-level Tate charts. When $p$ is invertible on the residue field, both have a single framed smoothing parameter:

$$
(\operatorname{Tate}_1(q),\mu_p),
\qquad
(\operatorname{Tate}_p(t),\langle t\rangle),
\quad q=t^p.
\tag{4.1}
$$

On a fine cover the completed local rings are $A[[q]]$ and $A[[t]]$, where $A$ is finite etale over the coefficient base. These are formally smooth of relative dimension one. The boundary is respectively $q=0$ or $t=0$ and is a relative Cartier divisor.

The relation $q=t^p$ describes a map to the unlevelled cusp; it does not make the source chart singular. Since $p$ is a unit away from the level prime, the map on punctured parameters is tamely ramified and the parameter ring itself remains regular.

### 4.3 From fine curves to stacks and coarse curves

For the rigidified curve, Propositions 4.1 and the cusp calculation cover every point away from $p$. Thus it is smooth there. The moduli stack has the same conclusion in the smooth topology: after adding prime-to-$p$ full level, it is covered etale by the fine curve.

The coarse statement requires care. At a tame geometric point, a stabilizer acts on a regular one-dimensional completed local ring $k[[t]]$. After removing ineffective inertia, the action is linearizable and the invariant ring is $k[[t^e]]$, again regular. Thus tame coarse points are regular even though the coarse map can ramify.

If the stabilizer order equals the residue characteristic, averaging is unavailable. Regularity of the invariant ring is then a separate local calculation, not a consequence of smoothness of the stack. For the unlevelled $j$-line that calculation is elementary from a Weierstrass equation, but for an arbitrary level quotient it must be stated case by case. Our global “smooth away from level” assertion therefore applies without qualification to the fine model and the stack; for a coarse model it includes the tame or directly verified hypothesis.

### 4.4 The good-prime theorem

**Theorem 4.2 (regularity and smoothness away from level).** Let $N$ be the full level integer of a compactified fine modular problem, and let $S=\operatorname{Spec}\mathbf Z[1/N]$. Then its compactified modular curve is smooth over $S$. More generally, a compactified modular stack is smooth over $S$, and its coarse curve is regular at every tame point. In the prime-level situation above, $\mathscr X$ is smooth over $R[1/p]$.

**Proof.** On the elliptic locus, level is finite etale and the deformation ring is a one-variable power-series ring. At every cusp, a Tate parameter gives the same type of ring over a finite etale coefficient algebra. These opens cover the compactification. Smoothness can be checked after the etale rigidifying cover, proving the stack assertion. The tame coarse invariant ring is a power-series ring in an invariant uniformizer, proving regularity there. $\square$

This theorem stops exactly at primes dividing the level. At $p$, the subgroup is no longer infinitesimally rigid, and its two possible deformations create the crossing studied next.

## 5. The two ordinary strata in characteristic $p$

### 5.1 Connected and etale directions

Let $U\subset X_k$ be the ordinary locus. For an ordinary elliptic curve $E/S$ in characteristic $p$, the connected--etale sequence is stable under ordinary deformation:

$$
0\longrightarrow E[p]^0\longrightarrow E[p]
\longrightarrow E[p]^{\mathrm{et}}\longrightarrow0,
\tag{5.1}
$$

where both nonzero terms have rank $p$. The connected subgroup is $\ker(F_E)$. Cartier duality identifies the etale direction with the dual of $\ker(F)$ on the appropriate Frobenius twist.

These are open-and-closed conditions in the ordinary part of the prime-level special fiber. The rank of $C^0$ is locally constant there and can only be $1$ or $p$. Define

$$
U_F=\{(E,\alpha,C):C=\ker(F_E)\},
\tag{5.2}
$$

and let $U_V$ be the locus where $C$ is etale. The notation anticipates that the quotient map in the first case is Frobenius and, after rewriting the second case on a Frobenius twist, is Verschiebung.

### 5.2 Frobenius and Verschiebung sections

There are two canonical maps from the ordinary base curve into the special fiber. The first is

$$
i_F:U\longrightarrow\mathscr X_k,
\qquad
(E,\alpha)\longmapsto(E,\alpha,\ker F_E).
\tag{5.3}
$$

For the second, start with $(E,\alpha)$ and use Verschiebung

$$
V_E:E^{(p)}\longrightarrow E.
$$

Its kernel is etale on the ordinary locus. Put

$$
i_V:U\longrightarrow\mathscr X_k,
\qquad
(E,\alpha)\longmapsto(E^{(p)},\alpha^{(p)},\ker V_E).
\tag{5.4}
$$

Both constructions commute with base change. Their images are $U_F$ and $U_V$. They are inverse to the appropriate degeneracy maps: $\pi_1i_F$ and $\pi_2i_V$ are the identity, while the other composites are Frobenius.

**Proposition 5.1.** The maps $i_F$ and $i_V$ are open immersions onto disjoint open subsets of the ordinary special fiber.

**Proof.** On $U_F$, $\pi_1$ recovers $(E,\alpha)$ and is an inverse to $i_F$. The condition that a finite flat group of rank $p$ be connected is open and closed in the ordinary connected--etale sequence, so the image is open. The same argument with $\pi_2$ applies to $i_V$. A subgroup cannot be both connected and etale unless its rank is one, so the images are disjoint. $\square$

### 5.3 Exhaustion of the ordinary fiber

There is no third ordinary stratum.

**Theorem 5.2.** Every geometric ordinary point of $\mathscr X_k$ lies in exactly one of $U_F$ and $U_V$.

**Proof.** Let $C\subset E[p]$ have rank $p$. Its image in the maximal etale quotient has rank dividing $p$, hence rank $1$ or $p$. In the first case $C$ lies in $E[p]^0$, which also has rank $p$, so equality follows. In the second case the map $C\to E[p]^{\mathrm{et}}$ has equal finite flat ranks and is an isomorphism. At the geometric point, Proposition 2.2 says that the complement of the connected subgroup is unique, so $C$ is the etale direction. The alternatives are disjoint by connectedness. $\square$

This rank argument is stronger than counting geometric points. It remains valid when the connected subgroup has only the identity as a geometric point and when the base contains nilpotents.

**Proposition 5.3 (ordinary deformation neighborhoods).** The fine model is smooth over $R$ at every ordinary point of its special fiber. On the connected branch, $\pi_1$ identifies the complete local deformation functor with that of the source elliptic curve. On the etale branch, $\pi_2$ identifies it with that of the quotient elliptic curve.

**Proof.** Over a henselian ordinary deformation $E/A$, the connected component $E[p]^0$ is finite flat of rank $p$ and is functorial under nilpotent base change. It is therefore the unique lift of the connected special subgroup. Quotienting by it constructs the isogeny, so forgetting the subgroup and taking the canonical connected subgroup are inverse operations on the connected formal neighborhood.

For an etale special subgroup $C_0\subset E_0[p]$, dualize the isogeny. Its dual kernel is connected. Given a deformation of the quotient $E_0/C_0$, take its canonical connected rank-$p$ subgroup, quotient by that subgroup, and dualize the resulting isogeny. This reconstructs uniquely the deformation of the original isogeny with etale kernel. Thus $\pi_2$ is the inverse coordinate on the etale formal neighborhood. Proposition 2.1 makes both deformation rings $R[[t]]$. $\square$

### 5.4 Closures and their normalizations

Let $C_F$ and $C_V$ be the reduced closures of $U_F$ and $U_V$ in $\mathscr X_k$. Since $U$ is dense in $X_k$, the maps $i_F$ and $i_V$ induce finite birational maps

$$
X_k\longrightarrow C_F,
\qquad
X_k\longrightarrow C_V.
\tag{5.5}
$$

Finiteness follows from properness and quasi-finiteness: a fixed level object has only finitely many preimages, and the source is proper. Because $X_k$ is smooth and hence normal, these maps factor through the normalizations of the components. Chapter 6 will show that the branches are already smooth at their missing supersingular points; consequently (5.5) will identify $X_k$ with each normalization.

At this stage every ordinary point belongs to one of two irreducible branches. An additional special-fiber component could still be contracted by both degeneracy maps to a supersingular point; flatness alone does **not** rule out such an exceptional vertical curve. What rules it out is the completed local ring in Chapter 6: $k[[x,y]]/(xy)$ has exactly two minimal primes and no exceptional component. Purity only excludes a zero-dimensional irreducible component. Thus exhaustion of the fiber is deliberately postponed until the supersingular calculation is complete.

## 6. Supersingular points and the crossing theorem

### 6.1 The unique special subgroup

At a supersingular elliptic curve, both ordinary directions must specialize to the same moduli point. Proposition 2.2 identifies that point:

$$
(E_0,\alpha_0,C_0),
\qquad C_0=\ker(F_{E_0})\simeq\alpha_p.
\tag{6.1}
$$

The uniqueness is scheme-theoretic. Although $E_0[p]$ has rank $p^2$ and is nonreduced, its space of $\alpha_p$ directions has dimension one for an elliptic curve. Thus no projective family of subgroup directions appears, in contrast with higher-dimensional superspecial abelian varieties.

The quotient $E_0/C_0$ is $E_0^{(p)}$, and the dual quotient is Verschiebung. Consequently the $F$-branch and $V$-branch have the same closed point after matching the supersingular point with its Frobenius conjugate. Over $\mathbf F_{p^2}$ every supersingular isomorphism class and this matching are defined, while over a smaller field the nodes form Frobenius orbits.

### 6.2 The completed local ring

**Theorem 6.1 (supersingular crossing theorem).** Let $z=(E_0,\alpha_0,C_0)$ be a geometric supersingular point of the fine model $\mathscr X$. Then

$$
\widehat{\mathcal O}_{\mathscr X,z}
\simeq W(k)[[x,y]]/(xy-p),
\tag{6.2}
$$

after replacing $W(k)$ by the corresponding unramified complete coefficient ring. Under this isomorphism,

$$
C_F=(x,p),\qquad C_V=(y,p)
\tag{6.3}
$$

up to interchanging $x$ and $y$.

**Proof.** A cyclic subgroup $C_0$ determines the quotient isogeny $\phi_0:E_0\to E_0/C_0$. Conversely a deformation of this isogeny determines its finite flat kernel. To check cyclicity rather than assume it, pass to the finite etale cover on which the Oort--Tate weight-one coordinate and the Teichmuller scalars are defined. The kernel then has coordinate equation $Z^p-aZ=0$, with $[c]Z=[c]_{\mathrm{Teich}}Z$. The monic cover

$$
A[U]/(U^{p-1}-a)
$$

is finite faithfully flat, and on it

$$
\prod_{c\in\mathbf F_p}(Z-[c]U)=Z^p-aZ.
$$

Thus $U$ is a Drinfeld generator, including when all its geometric values coalesce. The kernel is cyclic fppf-locally. Kernel and quotient are inverse constructions and preserve the prime-to-$p$ rigidifying level, which lifts uniquely.

Trivialize the two Hodge lines on the complete local hull. Theorem 2.3 represents the isogeny deformation problem by $W(k)[[x,y]]/(xy-p)$. Changing the trivializations acts by inverse unit rescaling and does not change the underlying complete local ring. The rigidifying branch cover removes automorphisms of the elliptic curves, so no further invariant quotient is taken. Hence the fine moduli ring is (6.2).

Modulo $p$, the two irreducible ideals are $(x)$ and $(y)$. On the locus $y\ne0$, the Oort--Tate parameter of the kernel is at its multiplicative endpoint, so this is the Frobenius branch. On $x\ne0$, the dual is multiplicative and the kernel is etale, so this is the Verschiebung branch. Taking closures gives (6.3). $\square$

### 6.3 Regularity and the node

The local equation proves both regularity of the total surface and semistability of the fiber.

**Corollary 6.2.** The local ring $W(k)[[x,y]]/(xy-p)$ is a two-dimensional regular local ring. Its special fiber has an ordinary double point, and its two branches meet with local intersection multiplicity one.

**Proof.** In the regular local ambient ring $W(k)[[x,y]]$, the equation $xy-p$ is not in the square of the maximal ideal because its term $-p$ is a regular parameter. The hypersurface criterion therefore makes the quotient regular of dimension two. Modulo $p$ it becomes $k[[x,y]]/(xy)$, the completed ring of a split node. Finally

$$
\operatorname{length}k[[x,y]]/(x,y)=1,
$$

so the two branches meet transversely. $\square$

The two component normalizations are therefore smooth at the added supersingular points: normalizing $k[[x,y]]/(xy)$ gives $k[[x]]\oplus k[[y]]$. This completes the promise left in Section 5.4.

### 6.4 Hypotheses at small primes

Equation (6.2) is a statement about the fine rigidified moduli problem. It remains valid at $p=2$ and $p=3$ once prime-to-$p$ level kills all automorphisms, because the formal-group recursion in Theorem 2.3 did not divide by the stabilizer order. The order-two Oort--Tate calculation uses $xy=2$ directly; in characteristic three the height-two coefficient remains a unit.

Without rigidification, supersingular elliptic curves at small primes have nonetale or non-linearly reductive stabilizers. The stack still has the crossing chart after a smooth cover, but the completed coarse invariant ring is not obtained by a tame averaging argument. Thus the assertions

$$
\text{fine model regular},\qquad
\text{stack semistable},\qquad
\text{coarse model regular}
$$

are three different assertions. The first two are now proved at every prime. The third is treated, with its exact hypotheses, in Chapter 12.

## 7. The global two-component special fiber

### 7.1 Gluing the local branches

We have obtained the global components over the ordinary locus and the complete local branches at every missing point. The next task is to show that these local descriptions glue without a hidden identification.

The maps $i_F$ and $i_V$ extend from the ordinary elliptic locus to all of $X_k$, but their cusp extensions must be described with generalized curves. At a supersingular elliptic point, $\ker(F_E)$ and the Frobenius-twisted Verschiebung construction both land at the unique local-local subgroup after the matching of Section 6.1. At a cusp, $i_F$ uses the one-gon with subgroup $\mu_p$. The extension of $i_V$ uses the $p$-gon with its component subgroup; its quotient and its contraction are the required one-gon. It would be incorrect to leave the component subgroup on a one-gon, where it would meet the node instead of the smooth locus. The two Tate charts prove that these extensions are regular and unique. Properness then glues the elliptic, supersingular, and cusp descriptions.

The extended maps

$$
i_F:X_k\longrightarrow C_F,
\qquad
i_V:X_k\longrightarrow C_V
\tag{7.1}
$$

are finite and birational. They induce isomorphisms on completed local rings of the normalizations: at an ordinary point this follows from the open immersion, and at a supersingular point it is the map $k[[x]]$ or $k[[y]]$ to the corresponding normalized branch. A finite birational map between smooth proper curves that is an isomorphism on completed local rings is an isomorphism. Hence

$$
C_F^{\mathrm{nor}}\simeq X_k,
\qquad
C_V^{\mathrm{nor}}\simeq X_k.
\tag{7.2}
$$

The components themselves are smooth because the branch local rings are discrete valuation rings. Their union, rather than either component, is singular at the supersingular nodes.

### 7.2 The semistable model theorem

**Theorem 7.1 (two-component semistable model).** The fine Deligne--Rapoport model $\mathscr X/R$ is regular. Its geometric special fiber is reduced and equals

$$
\mathscr X_{\bar k}=C_F\cup C_V,
\tag{7.3}
$$

where:

1. $C_F$ and $C_V$ are smooth and each is canonically a Frobenius twist of $X_{\bar k}$;
2. their intersection is the reduced supersingular divisor;
3. at every intersection point the completed total-space ring is $W(\bar k)[[x,y]]/(xy-p)$; and
4. there are no other singular points of the special fiber.

Equivalently, $\mathscr X/R$ is a regular semistable curve.

**Proof.** Away from the special fiber, regularity follows from the good-prime theorem. Proposition 5.3 gives a one-variable smooth deformation ring over $R$ at every ordinary point. At a supersingular point, Corollary 6.2 proves regularity and the nodal equation. At a cusp, Book 116's universal framed Tate charts already give $R'[[q]]$ and $R'[[t]]$ with $R'/R$ finite unramified; Chapter 10 records their level and degeneracy formulas but is not needed as a future premise. These loci cover $\mathscr X$.

The ordinary exhaustion theorem shows that the only possible components are the closures $C_F,C_V$. The supersingular crossing theorem shows that they meet there and that the fiber is reduced. It also shows that every singular special-fiber point is one of those crossings. Finally Section 7.1 identifies the smooth component normalizations. $\square$

The theorem is a construction, not merely a semistable-reduction assertion after a field extension. The base remains unramified at $p$, and the model retains the modular interpretation and both degeneracy maps.

### 7.3 Geometric connectedness and genus

The special fiber is connected. Indeed Stein factorization makes $f_*\mathcal O_{\mathscr X}$ a finite $R$-algebra inside the function field of the geometrically connected generic curve. Its generic fiber is $K$, and $R$ is integrally closed, so this finite algebra is $R$. Connectedness of every fiber follows. Equivalently in the present description, the two components meet because supersingular elliptic curves exist in every characteristic. The dual graph has two vertices and one edge for each geometric supersingular point.

Let $g_X$ be the genus of $X_k$ and let $s=|\mathrm{SS}(\bar k)|$ on the rigidified fine curve. Book 12's normalization formula gives

$$
p_a(\mathscr X_k)=2g_X+s-1.
\tag{7.4}
$$

Indeed the sum of component genera is $2g_X$, while the graph with two vertices and $s$ parallel edges has first Betti number $s-1$. Flatness makes this arithmetic genus equal to the genus of the generic prime-level modular curve. Formula (7.4) is both a consequence and a useful check on the component description.

Over the ground field, Frobenius may permute the supersingular edges and may interchange data used to label the two branches. The geometric graph with its Galois action is the invariant object. Counting only rational supersingular points can give the wrong genus or component data.

## 8. Igusa curves and normalized component covers

### 8.1 Why generators reappear on a normalization

The cyclic subgroup problem forgets a generator. On an ordinary fiber this forgetful operation is a finite etale quotient by $\mathbf F_p^\times$. Near a supersingular point the generator degenerates, and the normalization of its closure becomes a ramified cover of the component. These covers are the Igusa curves.

They solve two related problems. First, they give the correct normalizations of prime-level moduli problems that retain a Drinfeld generator, such as $\Gamma_1(p)$. Second, even for $\Gamma_0(p)$ they provide canonical fine covers of each component on which the connected or etale direction is explicitly trivialized. The word “Igusa” therefore refers to the generator cover of a Frobenius or Verschiebung kernel, not to an additional component of the two-component cyclic model.

### 8.2 The Igusa torsor on the ordinary locus

For an ordinary elliptic curve $E/S$ in characteristic $p$, define an Igusa structure in either of the equivalent ways:

$$
\iota:\mu_p\xrightarrow{\sim}\ker(F_E),
\tag{8.1}
$$

or, after Cartier duality, a generator

$$
Q\in\ker(V_E)(S)
\tag{8.2}
$$

whose multiples fill the etale group $\ker(V_E)$. The automorphism group of either structure is $\mathbf F_p^\times$. Thus over the ordinary locus $U$ the functor $\operatorname{Ig}(p)$ is a finite etale $\mathbf F_p^\times$-torsor.

Let $\overline{\operatorname{Ig}}(p)$ be the normalization of $X_k$ in the function field of this torsor. Finiteness of normalization follows from excellence. It is proper because $X_k$ is proper. The only points at which the map can ramify are the supersingular points: at a cusp and at an ordinary elliptic point, the connected or etale kernel remains of constant endpoint type and its generator torsor is etale.

There are two apparent Igusa covers, one for $\ker F$ and one for $\ker V$. Frobenius twist and Cartier duality identify them after transporting the prime-to-$p$ level. We retain the labels $\operatorname{Ig}_F$ and $\operatorname{Ig}_V$ when their maps to the two components are being compared.

### 8.3 Ramification at supersingular points

The local calculation is governed by the Hasse invariant. For an elliptic curve in characteristic $p$, Verschiebung acts on invariant differentials by

$$
V^*\eta=H(E)\,\eta^{(p)},
\tag{8.3}
$$

where $H$ is a section of $\omega^{\otimes(p-1)}$. It is invertible on the ordinary locus and vanishes precisely at supersingular points.

**Lemma 8.1 (simple Hasse zero).** On the fine one-dimensional deformation space of a supersingular elliptic curve, the Hasse invariant is a uniformizer up to a unit.

**Proof.** Choose the strict formal-group coordinate used in Theorem 2.3. Modulo $p$, write

$$
[p](T)=hT^p+uT^{p^2}+\text{higher terms},
\qquad u\in k[[h]]^\times.
\tag{8.4}
$$

The coefficient $h$ is, up to the differential framing, the Hasse invariant. The height-two special fiber has $h=0$. In the coefficient recursion for deformations, $h$ is the unique free first-order coefficient; all remaining coefficients are determined. Hence the universal deformation ring is $k[[h]]$, so $h$ has order one. $\square$

Trivializing $\ker F$ amounts to choosing a $(p-1)$st root of the Hasse parameter. More concretely, changing an isomorphism $\mu_p\simeq\ker F$ by $a\in\mathbf F_p^\times$ multiplies its differential parameter by $a$. Therefore the completed Igusa map at a supersingular point has the form

$$
k[[h]]\longrightarrow k[[u]],
\qquad h\longmapsto u^{p-1},
\tag{8.5}
$$

up to a unit in $h$.

**Theorem 8.2 (Igusa normalization).** The compactified Igusa curve $\overline{\operatorname{Ig}}(p)$ is smooth. It is finite etale of degree $p-1$ over the ordinary locus and totally tamely ramified of index $p-1$ at every supersingular point. At $p=2$ the index is one.

**Proof.** The ordinary assertion is the torsor construction. At a supersingular point, Lemma 8.1 and (8.5) identify the normalized completed local ring with $k[[u]]$, a discrete valuation ring. There are no other possible ramification points. Since every local ring of the normal proper curve is regular, the curve is smooth over the perfect field. $\square$

If one quotients generators by inversion, the effective degree becomes $(p-1)/2$ when $p>2$. Such a quotient must be stated explicitly; the full Igusa torsor has degree $p-1$.

### 8.4 Prime-level generator refinements

Consider the compactified $\Gamma_1(p)$ problem with the same prime-to-$p$ rigidifier. Its ordinary special fiber again has two loci. On the connected locus, the displayed Drinfeld generator trivializes the multiplicative direction; on the etale locus it is an ordinary generator. Consequently the normalizations of its two special-fiber components are

$$
\overline{\operatorname{Ig}}_F(p)
\quad\text{and}\quad
\overline{\operatorname{Ig}}_V(p).
\tag{8.6}
$$

Forgetting the generator gives the maps from these Igusa curves to $C_F$ and $C_V$, with deck group $\mathbf F_p^\times$. At a supersingular point the generator schemes collide, but (8.5) shows that normalization separates their branches and records the collision as tame ramification.

Thus the cyclic and point-level pictures fit into the diagram

$$
\begin{array}{ccccc}
\overline{\operatorname{Ig}}_F(p)&\cup&
\overline{\operatorname{Ig}}_V(p)&\subset&X_1(p;\mathcal P)_k^{\mathrm{nor}}\\
\downarrow&&\downarrow&&\downarrow\\
C_F&\cup&C_V&\subset&X_0(p;\mathcal P)_k.
\end{array}
\tag{8.7}
$$

The vertical arrows forget generators. The bottom row has exactly two components; the top row explains why their generator refinements are Igusa normalizations rather than copies of the unlevelled base curve.

## 9. Degeneracy maps on the components

### 9.1 Source and quotient

The two maps $\pi_1$ and $\pi_2$ retain different halves of an isogeny. Their restrictions to the special fiber reveal which branch is Frobenius-like.

If $C=\ker(F_E)$, then

$$
E/C\simeq E^{(p)}.
\tag{9.1}
$$

If the object is $(E^{(p)},\ker V_E)$, then

$$
E^{(p)}/\ker(V_E)\simeq E.
\tag{9.2}
$$

Prime-to-$p$ level is transported through these isogenies. Because its order is invertible, pullback and quotient identify the level groups without infinitesimal ambiguity.

### 9.2 The four restrictions

**Theorem 9.1 (degeneracy restrictions).** Under the identifications $C_F^{\mathrm{nor}}\simeq X_k$ and $C_V^{\mathrm{nor}}\simeq X_k$,

$$
\begin{aligned}
\pi_1|_{C_F}&=\operatorname{id},&
\pi_2|_{C_F}&=F_{X_k},\\
\pi_1|_{C_V}&=F_{X_k},&
\pi_2|_{C_V}&=\operatorname{id}.
\end{aligned}
\tag{9.3}
$$

**Proof.** On $C_F$, the universal object is $(E,\ker F_E)$. Forgetting the kernel leaves $E$, while quotienting gives $E^{(p)}$. This is exactly the identity and Frobenius on the moduli functor. On $C_V$, use the presentation $(E^{(p)},\ker V_E)$. Its source is $E^{(p)}$ and its quotient is $E$, giving Frobenius and the identity. The equalities hold on the dense ordinary open. Both sides are morphisms between proper separated curves, so they extend across supersingular points and cusps. $\square$

At a supersingular node, the two formulas agree on the common moduli point after Frobenius matching. They do not identify the two tangent branches: the identity map is separable on one branch, while Frobenius has zero differential on the other.

### 9.3 Finiteness and inseparability

Globally, $\pi_1$ and $\pi_2$ are finite. They are proper by compactification, and a fixed generalized elliptic curve has only finitely many cyclic subgroup divisors on each bounded stratum. Proper plus quasi-finite is finite.

On the generic fiber both maps are separable of the classical degree. On the special fiber each map has one degree-one component and one purely inseparable degree-$p$ component. Thus generic degree does not distribute by counting geometric points. Scheme-theoretic degrees are recovered from

$$
\deg(F_{X_k})=p,
\tag{9.4}
$$

even though Frobenius is bijective on geometric points over a perfect algebraic closure.

This is a useful model for specialization of correspondences: a generically etale Hecke correspondence can acquire a Frobenius component. The correspondence remains finite, but separability does not.

### 9.4 Compatibility with Igusa structures

Frobenius and Verschiebung exchange the two Igusa descriptions under Cartier duality. If $\iota:\mu_p\simeq\ker F_E$, dualizing gives a generator of $\ker V_E$. Conversely an etale generator dualizes to a multiplicative trivialization. Therefore the restrictions (9.3) lift to maps between $\operatorname{Ig}_F$ and $\operatorname{Ig}_V$.

On completed supersingular parameters, Frobenius sends a function to its $p$th power, while the Igusa parameter satisfies $h=u^{p-1}$. These facts are compatible because the Hasse invariant of a Frobenius twist is $H^p$. No choice of a root is canonical without the Igusa structure; the deck group $\mathbf F_p^\times$ records exactly that ambiguity.

## 10. Cusps in the integral model

### 10.1 The two prime-level cusp charts

The compactification is part of the integral theorem, so regularity must also be checked at the boundary. Prime level has exactly two cusp types.

The multiplicative type is

$$
(\operatorname{Tate}_1(q),\mu_p),
\tag{10.1}
$$

with completed framed base $R'[[q]]$. The component type is

$$
(\operatorname{Tate}_p(t),\langle t\rangle),
\qquad q=t^p,
\tag{10.2}
$$

with completed framed base $R'[[t]]$. Here $R'/R$ is the finite unramified or cyclotomic coefficient extension required by the prime-to-$p$ level and cusp labels. The $p$-gon in (10.2) is essential: on the contracted one-gon the section $[t]$ would specialize to the node rather than remain in the smooth locus.

These charts are exhaustive. Ampleness makes the component image of the subgroup surjective. Its order divides the prime $p$, so the polygon has one or $p$ components. On the one-gon the cyclic group is multiplicative; on the $p$-gon it maps isomorphically to the component group.

### 10.2 Regularity at the boundary

**Proposition 10.1.** Every cusp of the fine integral model is a smooth point over $R$. The cusp divisor is relative effective Cartier.

**Proof.** The completed rings $R'[[q]]$ and $R'[[t]]$ are regular of dimension two and formally smooth of relative dimension one over the unramified coefficient ring. The boundary ideals $(q)$ and $(t)$ are generated by non-zero-divisors. The formal charts algebraize because the generalized Tate curves are proper and the level divisors are finite. Thus the completed local criterion proves smoothness at every cusp. $\square$

This also shows that no cusp lies in $C_F\cap C_V$. In characteristic $p$, the one-gon cusp belongs to the connected branch and the $p$-gon cusp to the component branch. Each is a smooth point of its component.

### 10.3 Degeneracy formulas at the cusps

The two maps of (1.4) have the exact completed formulas

$$
\begin{array}{c|cc}
&\pi_1^*q&\pi_2^*q\\ \hline
(\operatorname{Tate}_1(q),\mu_p)&q&q^p\\
(\operatorname{Tate}_p(t),\langle t\rangle)&t^p&t.
\end{array}
\tag{10.3}
$$

For the first row, quotienting $\mathbf G_m/q^{\mathbf Z}$ by $\mu_p$ is induced by $u\mapsto u^p$ and changes the period to $q^p$. For the second, quotienting by the component subgroup enlarges the period lattice from $t^{p\mathbf Z}$ to $t^{\mathbf Z}$, so the quotient period is $t$. Forgetting level contracts the $p$-gon to the one-gon with period $t^p$.

These formulas prove more than regularity of the maps at the boundary. They give the ramification indices on cusp divisors and agree with the identity/Frobenius restrictions in characteristic $p$: the map $q\mapsto q^p$ reduces to Frobenius, while $q\mapsto q$ is the identity.

## 11. Component intersections and the dual graph

### 11.1 Local intersection multiplicities

Let $z$ be a supersingular node with residue field $\kappa(z)$. In the completed regular local ring

$$
A=R_z[[x,y]]/(xy-p),
\tag{11.1}
$$

the two components have ideals $(x)$ and $(y)$ modulo $p$. Their local intersection multiplicity is

$$
i_z(C_F,C_V)
=\operatorname{length}_A A/(x,y)
=1.
\tag{11.2}
$$

When intersections are measured over $k$, this point contributes $[\kappa(z):k]$. There are no other intersections. Consequently

$$
C_F\cdot C_V
=\deg_k(\mathrm{SS})
=\sum_z[\kappa(z):k].
\tag{11.3}
$$

The equality is on the fine regular surface. Stack intersection numbers would weight points by stabilizer orders, and coarse quotient nodes may have larger thickness. Those variants are not substituted silently into (11.3).

### 11.2 Self-intersections from the fiber relation

The scheme-theoretic special fiber is reduced:

$$
F=C_F+C_V=\operatorname{div}(p).
\tag{11.4}
$$

Since $F$ is principal, Book 11's fiber relation gives

$$
F\cdot C_F=F\cdot C_V=0.
\tag{11.5}
$$

Combining (11.3)--(11.5) yields

$$
C_F^2=C_V^2=-\deg_k(\mathrm{SS}).
\tag{11.6}
$$

This proof is preferable to guessing self-intersections from the graph. It uses the scheme-theoretic multiplicity one of both components, which was established by the local equation. Had the fiber contained a multiplicity or a quotient thickness, the diagonal entries would change.

### 11.3 The intersection matrix

Put $s=\deg_k(\mathrm{SS})$. In the ordered basis $(C_F,C_V)$, the vertical intersection matrix is

$$
M=
\begin{pmatrix}
-s&s\\
s&-s
\end{pmatrix}.
\tag{11.7}
$$

Its kernel is generated by $(1,1)$, the multiplicity vector of the full fiber, and its nonzero eigenvalue is $-2s$. Thus it is negative definite modulo the fiber, exactly as the general theorem of Book 11 requires.

For a horizontal degree-zero divisor $D$ with component intersection vector $(a,-a)$, a vertical correction satisfies

$$
v_F-v_V=\frac{a}{s}.
\tag{11.8}
$$

The denominator records genuine component data. On a quotient model the correct $s$ is not obtained by a naive unweighted count of coarse supersingular points; stabilizer and thickness data must first be restored.

### 11.4 The graph and its arithmetic meaning

Over $\bar k$, the dual graph has two vertices joined by one edge for each supersingular point:

```text
             e1
       C_F ===== C_V
             e2
             ...
```

Its first Betti number is $s_{\mathrm{geom}}-1$. The critical group of the unit-edge graph is

$$
\mathbf Z/s_{\mathrm{geom}}\mathbf Z
\tag{11.9}
$$

when the fine supersingular points are rational over the chosen algebraically closed field. Book 12 identifies this graph quotient with the geometric component group of the Jacobian of the fine modular curve.

Over a nonclosed field, one retains the Galois action on the edges. Over a coarse modular curve, an edge can acquire length from an effective stabilizer; after regular resolution it becomes a chain of unit edges. The weighted cycle pairing, not the bare number of coarse nodes, then computes the component group. This observation is indispensable in classical small-level examples.

## 12. Coarse quotients and exceptional automorphisms

### 12.1 Effective actions on a crossing

Return to the quotient presentation by a finite change-of-level group $G$. Let a subgroup $H\subset G$ stabilize a supersingular point of the fine cover. After removing ineffective inertia, its action on the two branch parameters has the form

$$
h(x)=\chi(h)x,
\qquad
h(y)=\chi(h)^{-1}y,
\tag{12.1}
$$

because $xy=p$ is fixed. The absence of a branch exchange is part of this particular quotient. An element of $H$ is an automorphism of the cyclic-level object: it acts on the source elliptic curve, preserves its kernel, and induces an automorphism of the quotient. It therefore scales the two Hodge pullback maps separately and cannot interchange $x$ with $y$. A larger quotient containing the dual-isogeny involution can exchange the branches and must be analyzed as a different moduli problem.

After strict henselization the coefficient ring is fixed, and tameness diagonalizes the action. If the effective character has order $e$, the invariant monomials of smallest branch orders are

$$
X=x^e,\qquad Y=y^e,\qquad XY=p^e.
\tag{12.2}
$$

More precisely, before descending the coefficient field the completed invariant ring is

$$
\left(R'[[x,y]]/(xy-p)\right)^H
\simeq R'[[X,Y]]/(XY-p^e).
\tag{12.3}
$$

Every invariant series is a sum of monomials $x^ay^b$ with $a-b\equiv0\pmod e$; using $xy=p$ reduces it to a series in $x^e,y^e$, which proves (12.3). Descending the unramified coefficient ring can replace the right side by $R'^H[[X,Y]]/(XY-u p^e)$ for a unit $u$; the thickness remains $e$.

Thus the coarse special fiber still has two branches, but the total-space node has thickness $e$. It is regular only when $e=1$.

### 12.2 Thick quotient nodes and their resolution

The surface

$$
XY=p^e
\tag{12.4}
$$

is normal but singular for $e>1$. Books 10 and 11 resolve it by successive blowups. Its minimal regular resolution inserts a chain of $e-1$ rational curves between the strict transforms of the two principal components:

```text
C_F -- E_1 -- E_2 -- ... -- E_{e-1} -- C_V
```

Every edge in the resolved fiber has thickness one, and each interior exceptional curve has self-intersection $-2$. The strict transforms' self-intersections are obtained from the fiber relation after all incidence and residue degrees are included.

**Proposition 12.1.** A tame coarse quotient of a stack node of effective order $e$ has a weighted node of thickness $e$. Its minimal regular resolution replaces that node by a chain of $e$ unit edges and preserves the metric cycle lattice.

**Proof.** Equation (12.3) gives the weighted node. The chart calculation for resolving $XY=p^e$ decreases the exponent by one at each blowup and creates one rational exceptional component. Induction ends at $XY=p$. Book 12's subdivision theorem identifies the length-$e$ edge with the resulting chain in the cycle lattice and monodromy pairing. $\square$

This is why a regular coarse model can have more than two irreducible components even though its stable coarse fiber has two principal components.

### 12.3 What remains two-component

The phrase “two-component Deligne--Rapoport fiber” has three exact meanings:

1. on the fine rigidified model, the special fiber has exactly two components and unit nodes;
2. on the modular stack, it has two stack components crossing semistably in a smooth chart; and
3. on the stable coarse model, it has two principal components but can have thick quotient nodes.

After resolving the coarse surface, exceptional chains count as additional components. Contracting those chains recovers the weighted two-component coarse fiber, but the contracted total space is singular when any length exceeds one.

At a tame smooth point with only one branch parameter, invariants remain a power-series ring and the coarse curve is regular. The new phenomenon at a node is the inverse action on two parameters together with the fixed relation $xy=p$.

In characteristics $2$ and $3$, a stabilizer can be wild or nonreduced. Then (12.1)--(12.3) cannot be obtained by averaging and character diagonalization. The coarse ring must be computed directly from the actual group-scheme action. The fine and stack theorems remain valid; no blanket regular coarse theorem is asserted in the wild case.

### 12.4 Descent of the global model

The fine cover carries an action of the change-of-level group, the universal curve, the cyclic subgroup, and both degeneracy maps. Uniqueness on the dense generic fiber extends the action and all compatibility identities to the integral model. Effective finite descent therefore gives the Deligne--Rapoport stack and its universal isogeny.

Taking the finite quotient gives the projective coarse model. Normality of invariant rings under a constant finite group proves that the coarse model is normal before resolution. The source and target maps descend because they are maps to coarse modular curves, even when the universal elliptic curves themselves do not descend.

If a regular coarse arithmetic surface is required, resolve precisely the quotient singularities and leave the already regular open unchanged. At tame thick nodes the explicit chain construction is canonical after minimality; at wild points one uses the direct invariant ring followed by the surface resolution theorem. Degeneracy maps remain honest on a common regular domination of their graph, though a chosen resolution can introduce vertical curves contracted by one projection.

## 13. The Deligne--Rapoport package

### 13.1 The main theorem

We can now state the result in the form used by later modular-curve geometry.

**Theorem 13.1 (Deligne--Rapoport integral model package).** Let $p$ be prime and let $\mathcal P$ be a prime-to-$p$ rigidifying branch cover as in Section 1.3. Then there is a unique projective normal flat fine cover

$$
\mathscr X=X_0(p;\mathcal P)\longrightarrow\operatorname{Spec}R
$$

obtained by normalizing the compactification of the generic auxiliary cover of the stack of generalized elliptic curves with an ample cyclic subgroup of rank $p$. On the dense smooth locus it represents the auxiliary basis together with the cyclic subgroup; at the boundary the auxiliary datum is a normalization branch. It has the following properties.

1. It is smooth away from $p$ and regular everywhere.
2. Its special fiber is reduced semistable with two smooth components $C_F,C_V$, each normalized by $X(\mathcal P)_k$.
3. The components meet exactly at supersingular points; every completed local ring there is $R_z[[x,y]]/(xy-p)$.
4. The two degeneracy maps restrict to $(\operatorname{id},F)$ on $C_F$ and $(F,\operatorname{id})$ on $C_V$.
5. At the two cusp types their pullbacks of the unlevelled parameter are $(q,q^p)$ and $(t^p,t)$.
6. The generator refinements of the two ordinary components normalize to Igusa curves. Each full Igusa cover is etale of degree $p-1$ on the ordinary locus and has local equation $h=u^{p-1}$ at a supersingular point.
7. If $s=\deg_k\mathrm{SS}$, then

   $$
   C_F\cdot C_V=s,\qquad
   C_F^2=C_V^2=-s,\qquad
   M=\begin{pmatrix}-s&s\\s&-s\end{pmatrix}.
   $$

8. The construction descends to the compactified modular stack. A tame coarse stabilizer of effective order $e$ changes a unit node into a node of thickness $e$; its minimal regular resolution inserts a chain of $e-1$ rational curves.

**Proof.** Existence, uniqueness, properness, flatness, and normality are Proposition 3.1, Proposition 3.2, and Theorem 3.3. The good-prime assertion is Theorem 4.2. Ordinary exhaustion is Theorem 5.2, the local ring is Theorem 6.1, and their global synthesis is Theorem 7.1. Igusa normalization is Theorem 8.2. Degeneracy and cusp formulas are Theorem 9.1 and (10.3). Intersections are (11.3), (11.6), and (11.7). Coarse thickness and resolution are Proposition 12.1. $\square$

Every statement carries the version of the model to which it belongs. In particular, item 8 is not used to retroactively claim that an unrigidified coarse surface has only two components after regular resolution.

### 13.2 A calculation protocol

When applying the theorem to a concrete modular curve, the following order prevents lost multiplicities.

First choose the space: fine cover, stack, stable coarse curve, or regular coarse resolution. Record the residual stabilizer at every exceptional point. Next identify the base modular curve $X(\mathcal P)_k$ and its supersingular divisor, including residue degrees.

On the fine cover, draw two copies of the base curve and join corresponding supersingular points. Label every edge by one. Apply the degeneracy table (9.3) to determine source and quotient on each component. At cusps, use (10.3), not a set-theoretic picture of torsion points.

For a coarse quotient, compute the effective character on both tangent branches. Replace a stabilizer orbit of nodes by its descended residue field and thickness. If a regular model is required, subdivide a length-$e$ edge into $e$ unit edges. Only after this step should the component intersection matrix or graph Jacobian be computed.

Finally check four independent identities:

$$
F=\operatorname{div}(p),
\qquad F\cdot\Gamma=0,
\qquad \pi_2\pi_1^{-1}\sim F\text{ on one branch},
\qquad p_a=\sum g_v+b_1.
\tag{13.1}
$$

A missing component multiplicity breaks the first two. A reversed branch label breaks the third. A lost supersingular orbit or exceptional chain breaks the fourth.

### 13.3 Failure modes and hypothesis ledger

The main false shortcuts can now be stated precisely.

| Shortcut | Failure | Correct statement |
|---|---|---|
| A rank-$p$ subgroup is determined by its geometric points | connected groups can have one visible point | use finite flat subgroup divisors and Drinfeld generation |
| Generic cyclic level has a unique integral model | order-$p$ groups can have several Hopf lattices | close inside the fixed $E[p]$ and impose the moduli condition |
| The ordinary fiber has $p+1$ components because $E[p]$ has $p+1$ generic lines | generic lines collide into two integral types | use the connected--etale rank dichotomy |
| The two ordinary branches remain disjoint | their subgroup schemes coalesce at supersingular curves | the completed ring is $xy=p$ |
| Normality proves regularity | a normal surface can have a thick node | use the completed local equation |
| A coarse quotient of a node is again a unit node | inverse tangent characters create thickness | compute invariants and resolve $XY=p^e$ |
| The number of rational supersingular points is the intersection number | residue extensions and Galois orbits contribute degrees | sum $[\kappa(z):k]$ or work geometrically |
| Igusa curves are extra components of $X_0(p)$ | they are generator normalizations of the two directions | quotient by $\mathbf F_p^\times$ recovers the cyclic components |
| Frobenius is degree one because it is bijective on geometric points | it is purely inseparable of degree $p$ | keep scheme-theoretic degree |
| A regular fine cover makes the coarse surface regular | fixed points can create quotient singularities | distinguish fine, stack, stable coarse, and resolved coarse models |

The dependency chain is equally exact. Normalization, regular surface criteria, and preservation of a good open come from Book 10. Blowup and component intersections come from Book 11. Nodes, weighted edges, and component groups come from Book 12. Finite-flat closure, connected--etale structure, Oort--Tate parameters, and Cartier duality come from Book 56. Generalized elliptic curves, ample Drinfeld level, compactified stacks, coarse curves, Tate charts, and boundary isogenies are established by Books 116 and 117. The new work here is the residue-characteristic deformation calculation and its global synthesis into the two-component model.

### 13.4 Conclusion

At a prime dividing the level, a modular curve does not merely become singular. Its level structure separates into two arithmetic directions. The Frobenius direction has connected kernel; the Verschiebung direction has etale kernel. Ordinary elliptic curves keep the directions apart. A supersingular elliptic curve forces them to share the unique local-local subgroup, and dual isogeny turns that collision into the equation

$$
xy=p.
$$

From this one equation flow the central geometric facts: the total space is regular, the special fiber is reduced and nodal, its two components meet once at each supersingular point, and the degeneracy maps become identity on one component and Frobenius on the other. Tate equations complete the same picture at the cusps. Igusa curves restore the generators forgotten by cyclic level and measure their tame collision through $h=u^{p-1}$.

The component intersection matrix then follows from the principal fiber relation rather than from a picture. Coarse descent adds one final layer: stabilizers can compress a chain of unit crossings into a thick node. Remembering that layer reconciles the two-component stack with regular coarse models containing exceptional chains.

The resulting Deligne--Rapoport package is therefore both geometric and arithmetic. It supplies a canonical proper integral moduli model, proves smoothness away from level, gives a regular semistable crossing at prime level, identifies component normalizations and degeneracy maps, and records exactly how intersections, Igusa covers, cusps, stabilizers, and coarse resolution alter the picture. These are the integral facts needed before modular forms, Jacobians, and Hecke correspondences can use the special fiber without losing either its moduli meaning or its multiplicities.
