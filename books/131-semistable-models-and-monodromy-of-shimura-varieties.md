# Semistable Models and Monodromy of Quaternionic Shimura Curves

## Contents

- [1. Bad reduction as controlled curve geometry](#1-bad-reduction-as-controlled-curve-geometry)
  - [1.1 The problem left by the good model](#11-the-problem-left-by-the-good-model)
  - [1.2 Arithmetic and cohomological conventions](#12-arithmetic-and-cohomological-conventions)
  - [1.3 Exact scope and selected split place](#13-exact-scope-and-selected-split-place)
  - [1.4 Dependency ledger](#14-dependency-ledger)
- [2. Iwahori PEL data and the integral curve](#2-iwahori-pel-data-and-the-integral-curve)
  - [2.1 The periodic self-dual lattice chain](#21-the-periodic-self-dual-lattice-chain)
  - [2.2 The parahoric moduli problem](#22-the-parahoric-moduli-problem)
  - [2.3 Projective representability](#23-projective-representability)
  - [2.4 The local-model diagram](#24-the-local-model-diagram)
- [3. The rank-two Iwahori local model](#3-the-rank-two-iwahori-local-model)
  - [3.1 Incidence of two lines](#31-incidence-of-two-lines)
  - [3.2 The nodal chart](#32-the-nodal-chart)
  - [3.3 Components and thickness](#33-components-and-thickness)
- [4. Global Frobenius and Verschiebung branches](#4-global-frobenius-and-verschiebung-branches)
  - [4.1 The semistable quaternionic curve](#41-the-semistable-quaternionic-curve)
  - [4.2 The height-two display and Hasse locus](#42-the-height-two-display-and-hasse-locus)
  - [4.3 Global branch normalization](#43-global-branch-normalization)
  - [4.4 The component graph](#44-the-component-graph)
  - [4.5 The connected two-branch calculation](#45-the-connected-two-branch-calculation)
- [5. Base change, resolution, and descent](#5-base-change-resolution-and-descent)
  - [5.1 Ramification and thick nodes](#51-ramification-and-thick-nodes)
  - [5.2 Resolution by a chain](#52-resolution-by-a-chain)
  - [5.3 Finite descent and level quotients](#53-finite-descent-and-level-quotients)
- [6. Nearby cycles and the monodromy filtration](#6-nearby-cycles-and-the-monodromy-filtration)
  - [6.1 Local nearby cycles](#61-local-nearby-cycles)
  - [6.2 The global graph complex](#62-the-global-graph-complex)
  - [6.3 The three graded pieces](#63-the-three-graded-pieces)
  - [6.4 Coefficients from PEL geometry](#64-coefficients-from-pel-geometry)
- [7. Monodromy pairing and component data](#7-monodromy-pairing-and-component-data)
  - [7.1 Weighted graph pairing](#71-weighted-graph-pairing)
  - [7.2 Component group and Smith form](#72-component-group-and-smith-form)
  - [7.3 Integral saturation](#73-integral-saturation)
- [8. Conductor and local type](#8-conductor-and-local-type)
  - [8.1 Artin conductor](#81-artin-conductor)
  - [8.2 Split semistable computation](#82-split-semistable-computation)
  - [8.3 Two-dimensional constituents](#83-two-dimensional-constituents)
  - [8.4 Finite and nonsplit descent](#84-finite-and-nonsplit-descent)
- [9. Hecke, degeneracy maps, and level change](#9-hecke-degeneracy-maps-and-level-change)
  - [9.1 Prime-to-$p$ Hecke correspondences](#91-prime-to-p-hecke-correspondences)
  - [9.2 The two degeneracy routes](#92-the-two-degeneracy-routes)
  - [9.3 The Ihara interface](#93-the-ihara-interface)
  - [9.4 Functorial monodromy and projectors](#94-functorial-monodromy-and-projectors)
- [10. The semistable curve theorem](#10-the-semistable-curve-theorem)
  - [10.1 Statement](#101-statement)
  - [10.2 Scope and failure modes](#102-scope-and-failure-modes)
  - [10.3 Conclusion](#103-conclusion)

## 1. Bad reduction as controlled curve geometry

### 1.1 The problem left by the good model

At a hyperspecial place, Book 130 gives a smooth projective integral model of the direct quaternion-trace Shimura curve. Replacing the hyperspecial stabilizer by the Iwahori stabilizer of one adjacent lattice pair forces the Hodge line to move compatibly at both vertices. The resulting morphism is no longer smooth: its special fiber has two branches, and their intersections create vanishing cycles.

For this rank-two minuscule problem, the failure is completely controlled. The exact PEL local model is the incidence of two lines, its unique bad chart is $xy=\pi$, and the total space remains regular. Globally the two branches are not anonymous copies: relative Frobenius and inverse-twist Verschiebung construct their normalizations from the good fiber, and their common locus is the reduced Hasse set. The route is

$$
\text{Iwahori lattice chain}
\longrightarrow \text{PEL incidence model}
\longrightarrow \text{global }F/V\text{ branches}
\longrightarrow R\Psi
\longrightarrow (r,N)
\longrightarrow \text{conductor and type}.                  \tag{1.1}
$$

Each arrow retains data that the next numerical invariant can forget. The conductor remembers a codimension and a Swan correction. The local type also remembers finite inertia, Frobenius, and the nilpotent map. The integral component group remembers the thickness pairing even when the rational monodromy rank is unchanged.

### 1.2 Arithmetic and cohomological conventions

Let $R$ be a henselian excellent DVR with fraction field $K$, uniformizer $\pi$, and perfect residue field $k$ of characteristic $p$. When Frobenius eigenvalues are discussed, take $k=\mathbf F_q$. Fix $\ell\ne p$ and write

$$
E_\ell=\mathbf Q_\ell,\qquad \Lambda_\ell=\mathbf Z_\ell.
$$

At a geometric special point, $\widehat{R^{\mathrm{sh}}}$ is the completed strict henselization, with the same chosen uniformizer. Geometric Frobenius is $F$. The Tate twist is normalized so that $F$ acts on $E_\ell(1)$ by $q^{-1}$. Accordingly

$$
N:V\longrightarrow V(-1),\qquad FNF^{-1}=q^{-1}N.           \tag{1.2}
$$

A proper flat relative curve is **strictly semistable** here if its total space is regular, its geometric irreducible components are smooth, and etale-locally it is either smooth over $R$ or

$$
\operatorname{Spec}R[x,y]/(xy-\pi).                          \tag{1.3}
$$

Requiring the geometric components to be smooth excludes a global self-node of one component and is the convention needed for the ordered-strata complex. If the geometric special fiber is $Y=\bigcup_{v\in V}Y_v$, write

$$
Y^{(1)}=\coprod_vY_v,
\qquad
Y^{(2)}=\coprod_{e}Y_{v(e)}\cap Y_{w(e)},                    \tag{1.4}
$$

where different intersection points give different summands.

### 1.3 Exact scope and selected split place

The only rational datum in scope is the direct quaternion-trace realization $D=V=B$ of Book 127, with $B/F$ division and split at exactly one real place. Fix its selected canonical component union and a neat prime-to-$p$ level.

Choose a finite Galois extension $L/\mathbf Q$ containing the normal closures of the center and reflex field and splitting every simple factor of the PEL algebra. Let $\Sigma$ contain $2$, all relevant discriminants, the polarization degree, the order index, and the primes supporting the fixed level and the exceptional set of Book 127. Choose

$$
p\notin\Sigma
$$

which splits completely in $L$, choose $v\mid p$ in the reflex field, and put

$$
R=\mathcal O_{E,v}^{\mathrm h},\qquad \pi=p,
\qquad k=\mathbf F_p.                                       \tag{1.5}
$$

Thus the maximal order, involution, lattice, determinant orientation, and all primitive idempotents are split over $\mathbf Z_p$. The distinguished vertex is exactly the smooth projective fine model of Book 130, Theorem 12.1. A bad fiber below means bad **Iwahori level** at this otherwise good split prime.

The book does not treat a deeper chain, a ramified algebra, a non-minuscule cocharacter, a nonflat naive determinant locus, or a dyadic local model. A finite extension followed by normalization and explicit resolution of thick nodes is allowed; if the generic field changes, the result is a semistable alteration over the new field, not a model of the original generic curve.

### 1.4 Dependency ledger

Books 10, 11, and 12 supply normalization, blowups and regular models, and graph/component-group algebra. Book 24 supplies the strict-semistable nearby-cycle and weight complexes. Book 26 supplies the Frobenius--Verschiebung formalism, purity, and duality used to identify global strata. Book 38 supplies quotients by finite locally free subgroups and descended polarizations. Book 127 supplies the exact direct rational tensors and the generic parahoric datum. Book 130 supplies the projective good vertex, its integral filtration-lifting theorem, universal family, and ordinary level qualifications.

The exact direct dependency row is

$$
\boxed{131\mid 10,11,12,24,26,38,127,130}.                  \tag{1.6}
$$

There are eight direct dependencies. No automorphic decomposition or later level-raising theorem is assumed.

## 2. Iwahori PEL data and the integral curve

### 2.1 The periodic self-dual lattice chain

Let $U_0,U_1$ be free rank-two $R$-modules with maps

$$
\alpha:U_0\longrightarrow U_1,
\qquad
\beta:U_1\longrightarrow U_0,
$$

satisfying

$$
\beta\alpha=\pi\operatorname{id}_{U_0},
\qquad
\alpha\beta=\pi\operatorname{id}_{U_1}.                    \tag{2.1}
$$

Choose a basis $e,f$ of the active multiplicity plane and set

$$
U_0=Re\oplus Rf,
\qquad
U_1=Re\oplus R\pi^{-1}f.
$$

In the bases $(e,f)$ and $(e,\pi^{-1}f)$,

$$
\alpha=\begin{pmatrix}1&0\\0&\pi\end{pmatrix},
\qquad
\beta=\begin{pmatrix}\pi&0\\0&1\end{pmatrix}.             \tag{2.2}
$$

Over $K$ both maps are isomorphisms. Over $k$ each has rank one, producing the two limiting branches.

We now install this pair in the full PEL lattice. Under the split maximal-order decomposition, pass to a full idempotent in the unique moving determinant packet. Extend the reduced pair periodically by

$$
U_{2m}=\pi^{-m}U_0,
\qquad
U_{2m+1}=\pi^{-m}U_1.
$$

Put the oppositely indexed dual lattice in the $*$-paired packet, use the alternating form to identify it with the opposite lattice when the packet is self-paired, and leave all inactive packets at their fixed vertices. Reassembling and extending the **entire** PEL lattice by $\Lambda_{i+2}=\pi^{-1}\Lambda_i$ gives

$$
\Lambda_0\subset\Lambda_1\subset\pi^{-1}\Lambda_0,
\qquad
\Lambda_i^\#=\Lambda_{-i}                                  \tag{2.3}
$$

after the harmless periodic reindexing of dual vertices.

Only $\Lambda_0$ is asserted to be self-dual for the original perfect form. The neighboring vertex is modular, and its polarization type is dictated by the full chain; it is not a second hyperspecial endpoint. Fixed packets and the common similitude are retained throughout.

Equivalently, let

$$
\operatorname{red}:G_{\mathbf Z_p}(\mathbf Z_p)
\longrightarrow\operatorname{GL}(U_0\otimes k)
$$

be active idempotent reduction, and let $B_0$ stabilize the oriented line selected by (2.2). The exact Iwahori is

$$
K_p^{\mathrm{Iw}}=
\{g\in G_{\mathbf Z_p}(\mathbf Z_p):
\operatorname{red}(g)\in B_0\}.                             \tag{2.4}
$$

This inverse-image definition retains the common similitude and every fixed packet. Forgetting the nonzero vertex recovers precisely the good functor of Book 130.

### 2.2 The parahoric moduli problem

For an $R$-scheme $S$, an object consists of a distinguished good-vertex PEL abelian scheme

$$
(A_0,\iota_0,\lambda_0,\eta^p)
$$

together with an adjacent abelian scheme carrying the induced order action, determinant label, prime-to-$p$ level, and chain polarization type, and an $\mathcal O$-linear isogeny

$$
\phi:A_0\longrightarrow A_1                              \tag{2.5}
$$

whose kernel has the finite locally free packet type prescribed by $\Lambda_0\subset\Lambda_1$. The polarizations satisfy

$$
\phi^\vee\lambda_1\phi=c\lambda_0                         \tag{2.6}
$$

for the scalar and target kernel type determined by the full self-dual chain. Both Lie algebras satisfy their vertexwise determinant and orientation laws.

Equivalently, specify a finite locally free, $\mathcal O$-stable, polarization-isotropic subgroup $H\subset A_0[p^a]$ with the active multiplicity rank and forced $*$-annihilator, put $A_1=A_0/H$, and use Book 38 to descend the required multiple of $\lambda_0$. Unless $H$ is globally Lagrangian, $\lambda_1$ has nontrivial $p$-primary kernel. This is another reason $A_1$ is not a second good endpoint.

Finite local freeness keeps the degree constant in the special fiber. Determinant laws are imposed at both vertices because compatibility at one vertex need not control the other modulo $p$. At neat prime-to-$p$ level automorphisms vanish; at coarser level the same construction gives a finite quotient stack.

### 2.3 Projective representability

Before representability, identify the exact linear algebra on arbitrary test rings.

**Proposition 2.1 (scheme-theoretic local-model comparison).** For the order, lattice, orientation, and chain of Section 2.1, the framed Hodge-filtration functor is exactly the incidence scheme $M^{\mathrm{Iw}}$ defined in Section 3.1. It is flat over $R$ and has no extra vertical associated component.

**Proof.** Work over an arbitrary $R$-algebra $S$, including rings with nilpotents. Split primitive idempotents decompose every framed de Rham lattice and its Hodge summand. Morita reduction turns stability under a matrix factor into a line $L_i\subset U_i\otimes S$ in the active multiplicity module. Inactive factors are forced by their rank-zero or full-rank determinant labels. The $*$-paired factor is the annihilator and is not a second choice; in a self-paired alternating plane every line is isotropic. The only remaining equations are

$$
\alpha L_0\subset L_1,
\qquad
\beta L_1\subset L_0.                                      \tag{2.7}
$$

Thus the comparison is functorial, not merely pointwise. The charts in Section 3 are smooth or $R[x,y]/(xy-\pi)$, all torsion-free over the DVR. Hence the scheme is flat with reduced special fiber and no vertical associated component. $\square$

**Theorem 2.2 (projective parahoric model).** At neat prime-to-$p$ level, the functor of Section 2.2 is represented by a projective flat $R$-scheme $\mathscr C_{\mathrm{Iw}}$ of finite presentation. Its generic fiber is the selected direct quaternionic Shimura curve at level $K_p^{\mathrm{Iw}}K^p$, and it carries the universal isogeny (2.5).

**Proof.** Forget $H$ and map to the projective good model $\mathscr X$ of Book 130. The relative Hilbert scheme of subschemes of the finite flat group $\mathcal A[p^a]$ is projective over $\mathscr X$. Being a subgroup, $\mathcal O$-stable, isotropic, and of the prescribed total and packetwise ranks are closed or open-and-closed conditions. Quotienting by the universal finite locally free subgroup gives $A_1$, and Book 38 descends the required polarization. Equation (2.6), the target kernel type, the determinant laws, and the orientation cut out a closed and open-and-closed locus. This represents the functor and carries its universal chain.

Over $K$, the kernel is the required parahoric flag, so the generic fiber is correct. Valuatively, the good vertex extends by projectivity of $\mathscr X$; the schematic closure of the generic kernel in $A_0[p^a]$ is finite and torsion-free over the valuation ring, hence flat. All subgroup and tensor identities extend by closure, and the quotient and polarization then extend uniquely. Flatness follows from Proposition 2.1 and the local-model diagram below. $\square$

The theorem does not claim smoothness. The failure of smoothness is precisely the node computed in Chapter 3.

### 2.4 The local-model diagram

Frame the de Rham modules at every lattice vertex. This gives

$$
\mathscr C_{\mathrm{Iw}}
\xleftarrow{\ a\ }
\widetilde{\mathscr C}_{\mathrm{Iw}}
\xrightarrow{\ b\ }M^{\mathrm{Iw}}.                         \tag{2.8}
$$

**Proposition 2.3 (local-model principle).** Both arrows in (2.8) are smooth of the same relative dimension, the dimension of the chain-frame group. Thus the moduli curve and $M^{\mathrm{Iw}}$ have smoothly equivalent strict henselian completed local rings. Flatness, regularity, and strict normal crossings may be checked on $M^{\mathrm{Iw}}$.

**Proof.** The integral automorphism group of the chain is smooth. On the active factor it is the standard smooth $\mathrm{GL}_2$ lattice-chain group; its special fiber maps onto the Borel with a smooth affine-unipotent kernel, but is not identified with that lower-dimensional Borel. Inactive factors are the hyperspecial groups of Book 130, and imposing the common smooth similitude character preserves smoothness. Elementary divisors and the dual-annihilator condition make the frame torsor locally nonempty, so $a$ is a torsor.

For $b$, apply Book 130's integral Hodge-filtration lifting at both vertices. On a divided-power evaluation, deformations of the isogeny chain are exactly filtration lifts compatible with the two lattice maps. Proposition 2.1 shows that all algebra, polarization, determinant, and orientation equations are already the equations of $M^{\mathrm{Iw}}$. Compatibility with crystal maps lifts the isogeny; its kernel retains the fixed finite locally free index, and Book 38 reconstructs the quotient and polarization. Prime-to-$p$ level lifts uniquely, and descent reconstructs the abelian chain over the original thickening. Thus $b$ is formally smooth, hence smooth by finite presentation. The frame dimensions agree. $\square$

## 3. The rank-two Iwahori local model

### 3.1 Incidence of two lines

Define

$$
M^{\mathrm{Iw}}(S)=
\left\{(L_0,L_1):
\begin{array}{l}
L_i\subset U_i\otimes\mathcal O_S\text{ are line direct summands},\\
\alpha L_0\subset L_1,\quad \beta L_1\subset L_0
\end{array}
\right\}.                                                    \tag{3.1}
$$

It is closed in $\mathbf P(U_0)\times_R\mathbf P(U_1)$ and therefore projective. Over $K$, either map identifies the two lines and the generic fiber is $\mathbf P^1_K$. The two-vertex formulation is invariant under change of chain bases and retains the universal filtrations needed for the PEL isogeny.

### 3.2 The nodal chart

**Proposition 3.1 (Iwahori chart).** The scheme $M^{\mathrm{Iw}}$ is regular, flat, and semistable over $R$. It is smooth except at one special-fiber point, where an affine neighborhood is

$$
\operatorname{Spec}R[x,y]/(xy-\pi).                          \tag{3.2}
$$

**Proof.** Near the exceptional pair, use the bases of (2.2) and write

$$
L_0=R(x,1),\qquad L_1=R(1,y).
$$

The first condition in (3.1) says that $(x,\pi)$ is proportional to $(1,y)$, hence $xy=\pi$; the second gives the same equation. On the remaining standard charts one line coordinate is eliminated and the chart is smooth. The displayed ring is torsion-free over $R$. At its closed point $\pi=xy$, so the maximal ideal is generated by $x,y$; dimension and embedding dimension are both two. Hence the total space is regular, while the special fiber is the transverse union $xy=0$. $\square$

The special fiber is singular at the crossing, but the total space is not. Nearby cycles measure failure of smoothness of the morphism.

### 3.3 Components and thickness

The geometric special fiber of $M^{\mathrm{Iw}}$ has two projective-line components $C_F$ and $C_V$, meeting once transversely. Locally they are $x=0$ and $y=0$. Pullback through a smooth morphism preserves the two branches and their transverse intersection.

After ramified base change of index $e$, (3.2) becomes

$$
xy=u(\pi')^e.                                                \tag{3.3}
$$

The integer $e$ is the edge thickness. For $e>1$ the total space is not regular. Resolving it inserts $e-1$ rational components and replaces the thick edge by $e$ unit edges. The cycle rank is unchanged, but the integral edge pairing is multiplied by $e$. Rational monodromy rank and integral component data must therefore be kept separate.

## 4. Global Frobenius and Verschiebung branches

### 4.1 The semistable quaternionic curve

Let $\mathscr C_{\mathrm{Iw}}$ be the selected fine scheme of Theorem 2.2.

**Theorem 4.1 (regular semistable model).** The scheme $\mathscr C_{\mathrm{Iw}}$ is a regular projective flat relative curve with reduced nodal special fiber. At every geometric node,

$$
\widehat{\mathcal O}_{\mathscr C_{\mathrm{Iw}},\bar x}^{\,\mathrm{sh}}
\simeq
\widehat{R^{\mathrm{sh}}}[[x,y]]/(xy-\pi).                  \tag{4.1}
$$

Every geometric irreducible component is smooth, so the model is strictly semistable.

**Proof.** Projectivity is Theorem 2.2. Proposition 2.3 transfers flatness, regularity, and the two smooth branch loci from Proposition 3.1. At a crossing, choose parameters cutting the branches. Since the special fiber is principal, $\pi=uxy$ for a unit $u$; replacing one parameter absorbs $u$ and gives (4.1). The lattice-vertex labels globalize the two branch loci, so no geometric component has a self-node. $\square$

At a quotient level with fixed points, the coarse scheme can have quotient singularities. All calculations are made on a fine cover and descended equivariantly unless the effective action is free.

### 4.2 The height-two display and Hasse locus

Let $\mathscr X$ be the distinguished smooth projective hyperspecial model obtained by forgetting the Iwahori flag, and let $X$ be its geometric special fiber. The active idempotent of the universal $p$-divisible group is a one-dimensional height-two group $G$. Verschiebung on its Hodge line defines

$$
\operatorname{Ha}:\omega_G\longrightarrow\omega_G^{(p)},
\qquad
\operatorname{Ha}\in H^0(X,\omega_G^{\otimes(p-1)}).        \tag{4.2}
$$

Write $Z=V(\operatorname{Ha})$.

**Lemma 4.2 (height-two subgroup calculation).** On the ordinary locus, the determinant-compatible rank-$p$ subgroups in the active packet are $\ker F_G$ and the etale subgroup

$$
\ker(V_{G^{(p^{-1})}})\subset G,                             \tag{4.3}
$$

where $G^{(p^{-1})}$ is the inverse Frobenius twist. At a local-local point they coincide in the unique admissible $\alpha_p$ line. At such a point the completed good-vertex deformation ring is $W(\bar k)[[t]]$, and a covariant display basis may be chosen, up to units and semilinearity, so that

$$
F(e)=f,\qquad F(f)=-pe+[t]f.                                \tag{4.4}
$$

The Hasse section is $t$ up to a unit.

**Proof.** Modulo $p$, the active covariant crystal has semilinear $F,V$ with
$\operatorname{im}F=\ker V$ and $\operatorname{im}V=\ker F$. At a local-local point both
operators are nilpotent of rank one. The polarization makes $F$ and $V$ adjoint on the
alternating plane; the adjoint of a rank-one nilpotent endomorphism of an alternating plane
is a scalar multiple of that endomorphism. Thus their images and kernels are one common line.
Choose $f$ on that line and $e$ off it, normalized by the alternating form. Lifting the basis,
the determinant and polarization fix the Frobenius determinant up to a unit, $FV=VF=p$
determines Verschiebung, and adapted triangular basis changes remove every deformation
coefficient except the lower-right entry. That entry has tangent
$\operatorname{Hom}(\omega_G,M/\omega_G)$, the single direction in Book 130's good local
model. Both completed deformation rings are formally smooth of dimension one and the tangent
map is an isomorphism, yielding (4.4). Verschiebung on the Hodge line reduces to multiplication
by $t$.

An ordinary height-two group has multiplicative and etale height-one factors, giving the two subgroups above. The second subgroup must be written on the inverse twist to be a subgroup of the fixed source $G$. In the local-local display their two lines coincide in the unique admissible $\alpha_p$. $\square$

Consequently $Z$ is reduced and finite etale over $\bar k$, and

$$
\#Z(\bar k)=\deg Z=(p-1)\deg\omega_G.                       \tag{4.5}
$$

If the selected generic curve is geometrically connected, proper flatness makes the special fiber connected. Since it has two labeled branches, $Z$ is nonempty. This proves positivity without trivializing the determinant--multiplier line in Book 130's Kodaira--Spencer formula.

### 4.3 Global branch normalization

Write $X_F$ for a labeled copy of $X$ and $X_V$ for its Frobenius-twisted copy. These labels will normalize the two branches; they do not introduce a second hyperspecial lattice vertex.

Reassemble $\ker F_G$ with its forced $*$-paired annihilator and zero summands in inactive packets. If $e,e^*$ are distinct paired primitive idempotents and $\operatorname{Rec}$ denotes integral Morita reassembly, the active subgroup is

$$
H_F=\operatorname{Rec}_{e}(\ker F_G)
\oplus
\operatorname{Rec}_{e^*}\bigl((\ker F_G)^\perp\bigr).       \tag{4.6}
$$

In a self-paired alternating packet the line is its own orthogonal, so only one reassembled summand is taken. The subgroup is finite locally free, $\mathcal O$-stable, and isotropic. Book 38 supplies the quotient and the adjacent polarization type. This gives

$$
j_F:X_F\longrightarrow Y,
$$

where $Y=\mathscr C_{\mathrm{Iw},\bar k}$.

For the other branch use the Frobenius-twisted good family. Reassemble the kernel of

$$
V_G:G^{(p)}\longrightarrow G
$$

inside the twisted source, again with its forced annihilator. Book 38 gives the adjacent polarized quotient and a morphism

$$
j_V:X_V\longrightarrow Y.
$$

This construction does not identify that quotient with the original good family. For a fixed geometric source it is exactly the inverse-twist subgroup (4.3).

Lemma 4.2 shows that these subgroup types exhaust the ordinary locus and coincide precisely on $Z$. Scheme-theoretically, the two choices are the minimal primes $(x)$ and $(y)$ of $\bar k[[x,y]]/(xy)$, while (4.4) identifies their common parameter with the Hasse parameter. The completed map from either labeled good copy to its branch is an isomorphism, after the Frobenius-twist parameterization on the $V$ side. Thus $j_F,j_V$ are proper and quasi-finite, hence finite; they are birational from normal curves and therefore normalize the two branches. Both occur with multiplicity one, meet exactly in the identified copies of $Z$, and cover $Y$.

The degeneracy map retaining the distinguished source is the identity on $X_F$ and Frobenius on $X_V$. The quotient degeneracy map lands first in the adjacent polarization-type functor; only after the fixed opposite dual-chain identification is it Frobenius on $X_F$ and the identity on $X_V$. Calling both legs identities on one good model would erase the chain orientation.

The common embeddings

$$
\iota_F:Z\hookrightarrow X_F,
\qquad
\iota_V:Z\hookrightarrow X_V                              \tag{4.7}
$$

are the Hasse inclusions up to the Frobenius twist on the second normalization. That twist is a universal homeomorphism and hence does not change prime-to-$p$ etale cohomology.

### 4.4 The component graph

The geometric dual graph $\Gamma$ has one vertex for each connected component of $X_F\amalg X_V$. Every $z\in Z(\bar k)$ is an oriented edge from the component containing $\iota_Fz$ to the component containing $\iota_Vz$. Its cellular boundary is

$$
\partial[z]=[\pi_0(\iota_Vz)]-[\pi_0(\iota_Fz)].            \tag{4.8}
$$

At the completely split place, geometric Frobenius fixes the two labels and acts through its permutations of $X$ and $Z$. Under finite descent, exchanging the labels reverses the oriented edge and contributes a sign.

For a connected generic curve,

$$
g(C)=\sum_{v\in V(\Gamma)}g(Y_v)+b_1(\Gamma).               \tag{4.9}
$$

The toric rank of the identity component of the Jacobian special fiber is $b_1(\Gamma)$.

### 4.5 The connected two-branch calculation

Assume $X$ is geometrically connected and put

$$
m=\#Z(\bar k)=(p-1)\deg\omega_G.
$$

Then $\Gamma$ has two vertices and $m$ parallel edges, so

$$
b_1(\Gamma)=m-1.                                             \tag{4.10}
$$

The component intersection matrix is

$$
\begin{pmatrix}-m&m\\m&-m\end{pmatrix}.                     \tag{4.11}
$$

For cycles $c_i=e_i-e_m$, $1\le i<m$, the unit-thickness Gram matrix has diagonal $2$ and off-diagonal $1$. Its determinant is $m$ and its Smith form is

$$
\operatorname{diag}(1,\ldots,1,m).                           \tag{4.12}
$$

Thus the geometric component group is $\mathbf Z/m\mathbf Z$. If $m=1$, the fiber is reducible but the graph is a tree, so both monodromy rank and component group vanish. Nodes must not be counted as independent cycles.

## 5. Base change, resolution, and descent

### 5.1 Ramification and thick nodes

Let $R'/R$ be finite of ramification index $e$ and residue degree $f$. A unit node becomes

$$
xy=\pi\quad\rightsquigarrow\quad xy=u(\pi')^e.              \tag{5.1}
$$

An unramified extension can split components or nodes but does not change geometric thickness. A ramified extension scales edge lengths. Normalization after ramified base change is mandatory: regularity need not survive the tensor product.

If the extension kills a finite inertial action, the strict model over $R'$ computes the unipotent logarithm only after restriction to $G_{K'}$. The original representation still retains the finite descent action.

### 5.2 Resolution by a chain

Over the completed strict henselian DVR, consider

$$
A_n=\widehat{R^{\mathrm{sh}}}[[x,y]]/(xy-\pi^n).
$$

For $n>1$, blow up $(x,\pi)$ and take the strict transform, normalizing if needed. One chart is regular; the other has equation $x_1y=\pi^{n-1}$. Repeating inserts a chain

$$
Y_0-E_1-E_2-\cdots-E_{n-1}-Y_1,                             \tag{5.2}
$$

with unit nodes between adjacent components. Each $E_i$ is rational of valence two.

A cycle crossing the original edge crosses all $n$ subdivided edges with the same coefficient. Hence its pairing contribution changes by

$$
a_eb_e\longmapsto n a_eb_e.                                 \tag{5.3}
$$

Subdivision preserves cycle rank and rational monodromy, while multiplying the integral thickness contribution by $n$.

### 5.3 Finite descent and level quotients

Suppose $K'/K$ is finite Galois with group $\Delta$ and a strict model has been obtained over $R'$. For an element $w$ of the Weil group,

$$
r(w)Nr(w)^{-1}=|w|N.                                        \tag{5.4}
$$

Finite inertia commutes with $N$, permutes vertices and nodes, and acts with a sign on an oriented edge when it exchanges its branches. Form the signed graph chain complex before taking invariants; quotienting the underlying unoriented graph first loses this information.

For finitely many translates of thick-node resolutions, take the union of the rational subdivision vertices after one ramification index clears their denominators, then insert every remaining integral point. The result is a finite invariant unit subdivision. Normalized blowups of the corresponding strata give a projective equivariant regular model. This is the only equivariant resolution needed for the displayed curve charts.

An ordinary prime-to-$p$ deck map does not change the $p$-level or oriented lattice chain. It commutes with the split idempotents and with $F,V$, so it preserves the Hasse and branch strata. A free quotient remains semistable etale-locally. If a deck orbit identifies two geometric branch components, the ordered-strata calculation stays on the fine cover with its descent action. With stabilizers, one works equivariantly on the fine cover or quotient stack; the coarse quotient can be singular, and a universal PEL family descends only under the qualifications of Book 130.

## 6. Nearby cycles and the monodromy filtration

### 6.1 Local nearby cycles

At a smooth point of $Y$, only $R^0\Psi E_\ell=E_\ell$ occurs. At a node, the chart (1.3) gives

$$
R^0\Psi E_\ell=E_\ell,
\qquad
R^1\Psi E_\ell=E_\ell(-1).                                \tag{6.1}
$$

**Proof.** The geometric generic punctured neighborhood is tamely equivalent to a one-dimensional torus. Kummer theory supplies one generator with twist $(-1)$. Smooth coordinates have no higher cohomology. $\square$

Thus $R^1\Psi E_\ell$ is a skyscraper sheaf on the geometric node set. Wild inertia is trivial on a strict chart, but the full nearby-cycle complex has nontrivial unipotent inertia through the extension between its degree-zero and degree-one terms.

Proper comparison gives

$$
R\Gamma(Y,R\Psi E_\ell)
\simeq R\Gamma(C_{\bar K},E_\ell).                           \tag{6.2}
$$

### 6.2 The global graph complex

Choose the orientation in (4.8). Put

$$
C_1(\Gamma,E_\ell)=E_\ell^{E(\Gamma)},
\qquad
C_0(\Gamma,E_\ell)=E_\ell^{V(\Gamma)}.
$$

The map $\partial:C_1\to C_0$ is (4.8), and its transpose is the alternating restriction map

$$
\rho:H^0(Y^{(1)},E_\ell)
\longrightarrow H^0(Y^{(2)},E_\ell).                        \tag{6.3}
$$

Hence

$$
H_1(\Gamma,E_\ell)=\ker\partial,
\qquad
H^1(\Gamma,E_\ell)=\operatorname{coker}\rho.               \tag{6.4}
$$

The adjoint Gysin map is the signed transpose of restriction, with Tate twist. The normalization sequence gives

$$
0\longrightarrow H^1(\Gamma,E_\ell)
\longrightarrow H^1(Y,E_\ell)
\longrightarrow\bigoplus_vH^1(Y_v,E_\ell)
\longrightarrow0.                                           \tag{6.5}
$$

A node contributes global monodromy only when its edge survives in graph homology. Separating nodes disappear from $H_1(\Gamma)$.

### 6.3 The three graded pieces

Let $V=H^1(C_{\bar K},E_\ell)$. Inertia is unipotent and

$$
\rho(\sigma)=1+t_\ell(\sigma)N,
\qquad N^2=0.                                                \tag{6.6}
$$

The monodromy filtration centered at one has

$$
\operatorname{gr}_0^M V=H^1(\Gamma,E_\ell),
$$

$$
\operatorname{gr}_1^M V=
\bigoplus_vH^1(Y_v,E_\ell),
$$

$$
\operatorname{gr}_2^M V=
H_1(\Gamma,E_\ell)(-1).                                    \tag{6.7}
$$

The graph pairing induces

$$
N:\operatorname{gr}_2^M V
\xrightarrow{\sim}
\operatorname{gr}_0^M V(-1),                                \tag{6.8}
$$

so

$$
\operatorname{rank}N=b_1(\Gamma).                           \tag{6.9}
$$

The component cohomology contributes length-one blocks and is killed by $N$; each independent graph cycle contributes one length-two block. Specialization identifies $H^1(Y,E_\ell)$ with $V^{I_K}=\ker N$ at split strict level. Frobenius acts on (6.7) through its actions on normalized components and the signed graph.

### 6.4 Coefficients from PEL geometry

Let $\mathcal L_\ell$ be a lisse $E_\ell$-sheaf obtained from the universal prime-to-$p$ Tate module by an integral algebraic construction, and assume it extends lisse over the semistable model. Etale-locally trivializing it gives

$$
(R^a\Psi\mathcal L_\ell)_x
\simeq \mathcal L_{\ell,x}\otimes(R^a\Psi E_\ell)_x.       \tag{6.10}
$$

If the coefficient sheaf itself is ramified along the special fiber, (6.10) is false: its inertia complex must be combined with the geometric Kummer complex. Constant coefficients, used for the curve cohomology above, have no such defect.

Integral coefficients require saturation checks. Local nearby-cycle modules are free, but global kernels and cokernels of incidence maps can have torsion.

## 7. Monodromy pairing and component data

### 7.1 Weighted graph pairing

Let every geometric edge $e$ have thickness $n_e\ge1$. On the cycle lattice

$$
X_\Gamma=H_1(\Gamma,\mathbf Z),
$$

the polarized monodromy pairing is

$$
q_\Gamma(a,b)=
\sum_{e\in E(\Gamma)}n_ea_eb_e.                             \tag{7.1}
$$

It is positive definite. Its scalar extension identifies the source and target graph pieces in (6.8). Therefore thickness does not alter $\operatorname{rank}N$, but it changes the integral discriminant.

The graph, its orientation, thicknesses, and Frobenius permutation are all geometric outputs of Chapter 4 and Section 5.1. None is reconstructed merely from the number of irreducible components.

### 7.2 Component group and Smith form

The geometric component group of the Jacobian Neron model is

$$
\Phi(\bar k)=\operatorname{coker}\left(
X_\Gamma\xrightarrow{q_\Gamma}X_\Gamma^\vee\right).        \tag{7.2}
$$

Thus a signed boundary matrix computes $X_\Gamma$, the diagonal thickness matrix computes (7.1), and Smith reduction computes $\Phi$ together with its Frobenius action.

In the connected two-branch case with $m$ unit-thickness edges, (4.12) gives

$$
\Phi(\bar k)\simeq\mathbf Z/m\mathbf Z.                     \tag{7.3}
$$

After ramification of common index $e$, the rational rank remains $m-1$ while the Gram matrix is multiplied by $e$ before Smith reduction. The conductor therefore cannot determine the component group.

### 7.3 Integral saturation

Let

$$
T=H^1(C_{\bar K},\mathbf Z_\ell)/\text{torsion}.
$$

The rational monodromy filtration intersects $T$ in a canonical lattice filtration, but the rational isomorphism (6.8) need not be an integral isomorphism. The geometric integral map is

$$
H_1(\Gamma,\mathbf Z_\ell)
\xrightarrow{q_\Gamma}
H_1(\Gamma,\mathbf Z_\ell)^\vee,                            \tag{7.4}
$$

whose cokernel is the $\ell$-primary part of (7.2). Identifying (7.4) with the map on the chosen cohomology lattice requires the integral nearby-cycle filtration and the adjacent graph kernels and images to be saturated. For semistable curves this identification is the standard Jacobian component pairing; for a Hecke-projected lattice it must be checked again after projection.

If a rational projector has an $\ell$-denominator, its image in $T$ can be nonsaturated. An integral local type on that rational summand requires a separately specified stable lattice; intersection with a nonsaturated rational image is not canonical.

## 8. Conductor and local type

### 8.1 Artin conductor

For an $E_\ell$-representation $V$ of $G_K$,

$$
a(V)=\dim V-\dim V^{I_K}+\operatorname{Sw}(V).              \tag{8.1}
$$

After quasi-unipotent reduction, let $(r,N)$ be its Weil--Deligne representation. Then

$$
V^{I_K}=(\ker N)^{r(I_K)},
$$

and

$$
a(V)=\dim V-\dim(\ker N)^{r(I_K)}+
\operatorname{Sw}(r).                                       \tag{8.2}
$$

At split strict semistable level, $r$ is trivial on inertia and the Swan term vanishes, so

$$
a(V)=\operatorname{rank}N.                                  \tag{8.3}
$$

Equation (8.3) must not be used before finite descent has been restored.

### 8.2 Split semistable computation

For the quaternionic curve, (6.9) and (8.3) give

$$
a\left(H^1(C_{\bar K},E_\ell)\right)=b_1(\Gamma).           \tag{8.4}
$$

In the connected two-branch case this is

$$
(p-1)\deg\omega_G-1.                                       \tag{8.5}
$$

The local Euler polynomial is

$$
P(T)=\det\left(1-FT\mid(\ker N)^{r(I_K)}\right).            \tag{8.6}
$$

At split strict level, (6.5) shows that computing (8.6) requires Frobenius on both $H^1(\Gamma)$ and the normalized component cohomology. Neither the conductor nor the component group alone determines it.

### 8.3 Two-dimensional constituents

Let $W$ be a two-dimensional $G_K$- and Hecke-stable direct summand or subquotient of $H^1$. Since $N^2=0$, either $N|_W=0$ or it has rank one. In the latter case choose $e_0,e_1$ with

$$
Ne_1=e_0,\qquad Ne_0=0.                                    \tag{8.7}
$$

If finite inertia is trivial, this is one length-two unipotent block and

$$
a(W)=1.                                                      \tag{8.8}
$$

Its Weil--Deligne type is special: after an unramified character twist, $N$ is the standard nonzero nilpotent operator on a two-dimensional special representation. Geometry determines the nonzero monodromy and conductor jump; the twist and Frobenius eigenvalue come from $F$ on $\ker N$.

If $N|_W=0$, the unipotent part is absent. At split strict level $W$ is unramified, but after descent it can still carry nontrivial finite inertia.

### 8.4 Finite and nonsplit descent

Suppose strict semistability is reached over $K'/K$. The finite group acts on

$$
H^1(\Gamma,E_\ell),
\qquad
H_1(\Gamma,E_\ell)(-1)
$$

dually, with orientation signs. Formula (8.2), not (8.4), gives the conductor over $K$.

A nonsplit multiplicative two-dimensional constituent still has nonzero $N$ and conductor one when its finite character is unramified, but Frobenius acts with the opposite sign on its graph line. A ramified quadratic character can shrink inertia invariants without changing $\operatorname{rank}N$, and wild descent adds the Swan term. Thus local type is the full data $(r,N,F)$, not its conductor exponent.

## 9. Hecke, degeneracy maps, and level change

### 9.1 Prime-to-$p$ Hecke correspondences

For $g\in G(\mathbf A_f^p)$, changing prime-to-$p$ level gives

$$
\mathscr C_{\mathrm{Iw},K}
\xleftarrow{\ p_1\ }
\mathscr C_{\mathrm{Iw},K\cap gKg^{-1}}
\xrightarrow{\ p_2\ }
\mathscr C_{\mathrm{Iw},K}.                                 \tag{9.1}
$$

On a smaller selected union, the right target is its Hecke translate unless $g$ preserves the union. At fine level the legs are finite etale. The universal prime-to-$p$ isogeny preserves the $p$-adic lattice chain, commutes with all split idempotents and with $F,V$, and carries the Hasse section to a unit multiple. Hence it preserves the $F/V$ branch labels, $Z$, the oriented graph, and thickness.

The normalized operator is

$$
T_g=(p_2)_*p_1^*.                                            \tag{9.2}
$$

Normalization factors must match the generic Hecke algebra. Multiplying by a degree preserves commutation with monodromy but can change an integral lattice.

### 9.2 The two degeneracy routes

Forgetting the nonzero lattice vertex gives the source degeneracy map

$$
d_0:\mathscr C_{\mathrm{Iw}}\longrightarrow\mathscr X.      \tag{9.3}
$$

On branch normalizations it is

$$
d_0|_{X_F}=\operatorname{id},
\qquad
d_0|_{X_V}=F.                                                \tag{9.4}
$$

The quotient abelian scheme gives a second route to the adjacent chain-vertex PEL functor. This target is not a second good model of Book 130: its polarization type is the one forced by the modular vertex. After applying the fixed opposite dual-chain reparameterization used in the generic level tower, write the resulting target and map as

$$
d_1:\mathscr C_{\mathrm{Iw}}\longrightarrow\mathscr X'.     \tag{9.5}
$$

Then

$$
d_1|_{X_F}=F,
\qquad
d_1|_{X_V}=\operatorname{id},                               \tag{9.6}
$$

up to the same harmless Frobenius-twist parameterizations used in Chapter 4. Without the dual-chain identification, $\mathscr X'$ must not be silently replaced by $\mathscr X$.

On the common Hasse set the two restrictions agree in the unique admissible local-local subgroup. Equations (9.4)--(9.6), together with (4.8), are the geometric degeneracy data needed for level comparison.

### 9.3 The Ihara interface

After a chosen identification $\mathscr X'\simeq\mathscr X$ in the relevant level tower, the two pullbacks form

$$
d^*=(d_0^*,d_1^*):
H^1(\mathscr X_{\bar K},E_\ell)^{\oplus2}
\longrightarrow
H^1(\mathscr C_{\mathrm{Iw},\bar K},E_\ell),                \tag{9.7}
$$

and proper traces form its adjoint route

$$
d_*=(d_{0*},d_{1*}).                                         \tag{9.8}
$$

On the special fiber, normalization replaces the target by $X_F\amalg X_V$, the restrictions of (9.7) are governed by the identity/Frobenius matrix in (9.4) and (9.6), and the failure to glue independently across the two copies is measured by the edge restriction map (6.3). Thus the old part, the graph quotient, and the monodromy line are all expressed using explicit maps of the good fiber and the Hasse set.

This book supplies that geometric complex but does not assert an Ihara lemma. Injectivity of (9.7), torsion-freeness of its localized cokernel, or a level-raising congruence requires the relevant Hecke localization and arithmetic input. What is available unconditionally is the exact branch routing, the signed graph matrix, the adjoint trace, and their compatibility with $N$, Frobenius, and the component pairing.

For the FLT level-change application, a Hecke-isolated two-dimensional constituent with nonzero image in the graph piece has $N\ne0$, conductor exponent one at split strict level, and special local type. A constituent supported only on normalized component cohomology has $N=0$. This dichotomy is geometric; identifying which Hecke eigensystem occurs is a separate automorphic step.

### 9.4 Functorial monodromy and projectors

Finite etale pullback and trace act on

$$
R\Gamma(Y,R\Psi E_\ell)
$$

and commute with inertia, Frobenius, restriction, Gysin, and $N$. On the graph they commute with $\partial$ and are adjoint for $q_\Gamma$, hence act on the component group (7.2). Every page of the weight spectral sequence is therefore a Hecke module.

For an idempotent $e$ in the rational prime-to-$p\ell$ Hecke algebra,

$$
eN=Ne,\qquad eF=Fe.                                         \tag{9.9}
$$

Thus $(r,N,F)$ restricts to $eV$. Conductors are additive on genuine direct sums, but not across arbitrary nonsplit exact sequences: one length-two monodromy block has conductor one while its two unramified semisimple subquotients each have conductor zero. Semisimplifying away $N$ can therefore change the conductor.

If $e$ exists only after coefficient extension, rational ranks are unchanged. If it has an $\ell$-denominator, it need not preserve an integral direct summand; the saturation warning of Section 7.3 applies.

At the bad prime itself, a degeneracy correspondence changes the lattice chain and need not be finite etale. Its integral extension is the explicit PEL isogeny diagram (9.3)--(9.6), not a consequence of the prime-to-$p$ construction.

## 10. The semistable curve theorem

### 10.1 Statement

**Theorem 10.1 (semistable models and monodromy of quaternionic Shimura curves).** Fix the direct quaternion-trace PEL curve of Book 127, a decomposition-stable canonical component union, and neat prime-to-$p$ level. Choose the completely split odd place (1.5) and impose the oriented Iwahori chain (2.3). Then:

1. the exact parahoric PEL functor is represented by a projective flat model carrying its universal isogeny, and its framed local model is scheme-theoretically the incidence scheme (3.1), with no extra vertical component;
2. the integral curve is regular and strictly semistable with completed node chart (4.1);
3. its two global branches are normalized by the labeled good copy $X_F$ and Frobenius-twisted copy $X_V$, constructed from the actual relative-Frobenius and inverse-twist Verschiebung kernels, and they meet with multiplicity one exactly at the reduced Hasse set $Z$;
4. the dual graph has boundary (4.8), and the weighted monodromy pairing and component group are (7.1) and (7.2);
5. after ramified base change, normalization and the chain resolution (5.2) produce a strict model; finite descent acts on its signed graph complex before invariants are taken;
6. nearby cycles are (6.1), the monodromy filtration is (6.7), and $\operatorname{rank}N=b_1(\Gamma)$;
7. at split strict level the conductor of $H^1$ is $b_1(\Gamma)$, while over the original field it is given by (8.2) with finite inertia and Swan conductor retained;
8. if the good fiber is geometrically connected, then

   $$
   b_1(\Gamma)=(p-1)\deg\omega_G-1,
   \qquad
   \Phi(\bar k)\simeq
   \mathbf Z/((p-1)\deg\omega_G)\mathbf Z;
   $$

9. every prime-to-$p$ Hecke correspondence on the full component union, or on a smaller union it preserves, preserves the $F/V$ kernels, Hasse set, graph pairing, nearby cycles, Frobenius, and $N$; and
10. the two bad-prime degeneracy routes restrict as identity/Frobenius and Frobenius/identity on the branch normalizations, after the required dual-chain identification, giving the explicit geometric complex used by Ihara and level-change arguments.

**Proof.** Proposition 2.1 proves the exact local-model identity over arbitrary test rings, Theorem 2.2 gives projective representability, and Proposition 2.3 transfers the local geometry. Proposition 3.1 and Theorem 4.1 prove statements 1--2. Lemma 4.2 and the reassembled subgroup construction prove statement 3, including exhaustion, multiplicity one, and the precise inverse-twist $V$ label. Sections 4.4 and 7.1--7.2 prove statement 4. Chapter 5 proves statement 5. The graph nearby-cycle calculation in Chapter 6 proves statement 6. Chapter 8 proves statements 7--8. Naturality of prime-to-$p$ isogenies and functoriality of nearby cycles prove statement 9. Section 9.2 proves statement 10. $\square$

### 10.2 Scope and failure modes

The theorem is deliberately restricted to the direct datum at a completely split odd prime and to the one-step rank-two Iwahori. Deeper chains, ramified orders, non-minuscule local models, and wild singularities require different equations. A determinant condition by itself is not enough: Proposition 2.1 works over nilpotent rings and is what excludes a hidden vertical component.

There is no dyadic claim. Book 130's torus-rank argument can prove properness of a direct flat closure once a dyadic integral functor is separately available, but it does not supply the dyadic good vertex, display, or Iwahori local model required here.

Projectivity uses the distinguished good vertex at exactly the strength proved in Book 130. The neighboring lattice vertex has its chain polarization type and is not a second hyperspecial model. Dropping that distinction invalidates both the Hilbert-scheme construction and the degeneracy routes.

At coarse level, fixed points can create quotient singularities. Nearby cycles are then computed equivariantly on a fine cover or stack. After nonsplit descent, branch exchange acts with a sign on oriented edges. A lisse coefficient system satisfies (6.10); a sheaf ramified along the special fiber does not.

The equality $\operatorname{rank}N=b_1(\Gamma)$ is rational. Integral cokernels use the thickness matrix and saturation of the chosen lattice. A rational Hecke projector with an $\ell$-denominator does not select a canonical integral lattice. Finally, the geometric degeneracy complex is input to an Ihara lemma or level-raising theorem, not a proof of either.

### 10.3 Conclusion

The direct quaternionic bad-prime problem reduces integrally to one incidence of two lines. That incidence produces the regular node $xy=p$. Relative Frobenius and inverse-twist Verschiebung then identify the two global branches, while the Hasse section identifies every intersection and its multiplicity. The resulting signed graph is therefore an arithmetic object, not an unlabeled combinatorial approximation.

Nearby cycles turn graph cycles into the length-two monodromy blocks. Their number is the split conductor, their weighted Gram matrix controls the component group, and Frobenius together with finite descent determines the full local type. Prime-to-$p$ Hecke maps preserve this package, while the two explicit degeneracy routes connect it to hyperspecial level. These are exactly the semistable model, component, monodromy, conductor, type, and level-change data needed by the quaternionic FLT blueprint.
