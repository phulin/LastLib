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
  - [4.5 The descended normalization and node complex](#45-the-descended-normalization-and-node-complex)
  - [4.6 The connected two-branch calculation](#46-the-connected-two-branch-calculation)
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
  - [9.3 The actual residue-prime correspondence](#93-the-actual-residue-prime-correspondence)
  - [9.4 The calculation on oriented edges](#94-the-calculation-on-oriented-edges)
  - [9.5 The bad-prime Eichler--Shimura theorem](#95-the-bad-prime-eichler--shimura-theorem)
  - [9.6 The degeneracy complex and its boundary](#96-the-degeneracy-complex-and-its-boundary)
  - [9.7 Functorial monodromy and projectors](#97-functorial-monodromy-and-projectors)
  - [9.8 Principal and ray towers over the parahoric diagram](#98-principal-and-ray-towers-over-the-parahoric-diagram)
- [10. The semistable curve theorem](#10-the-semistable-curve-theorem)
  - [10.1 Statement](#101-statement)
  - [10.2 Scope and failure modes](#102-scope-and-failure-modes)
  - [10.3 Conclusion](#103-conclusion)

## 1. Bad reduction as controlled curve geometry

### 1.1 The problem left by the good model

At a hyperspecial place, Book 121 gives a smooth projective integral model of the direct quaternion-trace Shimura curve. Replacing the hyperspecial stabilizer by the Iwahori stabilizer of one adjacent lattice pair forces the Hodge line to move compatibly at both vertices. The resulting morphism is no longer smooth: its special fiber has two branches, and their intersections create vanishing cycles.

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

At a geometric special point, $\widehat{R^{\mathrm{sh}}}$ is the completed strict
henselization, with the same chosen uniformizer. Geometric Frobenius is $F$; in the
packet comparison we also write $\Phi=F$ to match Books 126--128 and 168. Arithmetic
Frobenius is $\Phi^{-1}$. The Tate twist is normalized so that $F$ acts on
$E_\ell(1)$ by $q^{-1}$. Accordingly

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

The only rational datum in scope is the direct quaternion-trace realization $D=V=B$ of Book 119, with $B/F$ division and split at exactly one real place. Fix its selected canonical component union and a neat prime-to-$p$ level.

This is a conditional input, not an existence theorem in the mixed one-split range. Book 119's
direct trace similitude group is the common-norm group, and Book 118, Proposition 8.2 proves
that when $[F:\mathbf Q]>1$ the one-split adjoint Hodge map cannot lift to it: its reduced-norm
exponent is odd at the active real factor and even at every compact factor. Thus the local-model
and monodromy theorem below remains valid for any supplied datum satisfying its ledger, but it
does not itself produce the raw SP carrier needed in the FLT application. Using a different
central modification requires a new comparison of its parahoric PEL model, components, and raw
packet plane with the basic curve; none is inferred from equality of adjoint groups.

Choose a finite Galois extension $L/\mathbf Q$ containing the normal closures of the center and reflex field and splitting every simple factor of the PEL algebra. Away from two, let $\Sigma_{\mathrm{odd}}$ contain all relevant discriminants, the polarization degree, the order index, the primes supporting the fixed level, and the exceptional set of Book 119. There are two allowed local situations.

In the first, choose an odd prime

$$
p\notin\Sigma_{\mathrm{odd}}
$$

which splits completely in $L$, choose $v\mid p$ in the reflex field, and put

$$
R=\mathcal O_{E,v}^{\mathrm h},\qquad \pi=p,
\qquad k=\mathbf F_p.                                       \tag{1.5}
$$

Thus the maximal order, involution, lattice, determinant orientation, and all primitive idempotents are split over $\mathbf Z_p$. The distinguished vertex is exactly the smooth projective fine model of Book 121, Theorem 12.1.

In the second, $p=2$, the chosen place $v$ has $E_v=\mathbf Q_2$, and the complete local PEL tensor is required to be **dyadically tensor-split** in the following exact sense:

1. $F\otimes\mathbf Q_2$ is a product of copies of $\mathbf Q_2$, $B\otimes\mathbf Q_2$ is the corresponding product of $M_2(\mathbf Q_2)$, and the acting order is the product of $M_2(\mathbf Z_2)$;
2. the involution preserves that order and the direct rational module admits an order-stable lattice $\Lambda_0$ on which the PEL alternating form is perfect and genuinely alternating over $\mathbf Z_2$;
3. after integral Morita reduction, the sole moving determinant packet is the standard plane

   $$
   U=\mathbf Z_2e\oplus\mathbf Z_2f,
   \qquad \langle ae+bf,ce+df\rangle=ad-bc,               \tag{1.5a}
   $$

   its $*$-paired packet is its annihilator, and every inactive packet is fixed by the determinant law;
4. the multiplier and orientation labels extend as finite etale data, the polarization degree is odd, the selected canonical component union is decomposition-stable, and the auxiliary fine level has odd order and is neat.

The last ledger is stronger than saying only that $B$ is split over $\mathbf Q_2$. It is exactly what prevents a ramified dyadic involution or a merely skew form from being mistaken for a smooth integral tensor. In (1.5a), alternation is the identity $\langle x,x\rangle=0$ over $\mathbf Z_2$, not a consequence of reducing a skew matrix modulo two. Section 2.1 constructs the dyadic vertex from these tensors, so the dyadic case does not appeal to an unproved extension of Book 121's odd theorem.

In either situation a bad fiber below means bad **Iwahori level** at an otherwise smooth split vertex. The principal new result is the second situation, where

$$
R=\mathbf Z_2^{\mathrm h},\qquad \pi=2,\qquad k=\mathbf F_2,
\qquad q=2.                                                  \tag{1.5b}
$$

All generic curves and all coefficient fields in the packet theorem have characteristic zero. Residue characteristic two enters only through the integral model and its special fiber. The book does not treat a deeper chain, a ramified algebra or involution, a non-minuscule cocharacter, or a nonflat naive determinant locus. A finite extension followed by normalization and explicit resolution of thick nodes is allowed; if the generic field changes, the result is a semistable alteration over the new field, not a model of the original generic curve.

### 1.4 Dependency ledger

Books 10--12 supply effective finite descent, normalization, blowups, and regular models; Book 13 supplies the divisor definition of a bad-characteristic Drinfeld basis; Book 16 supplies graph/component-group algebra. Book 17 supplies the finite-etale common refinement and effective Galois closure on the generic diagram. Book 22 supplies the strict-semistable nearby-cycle and weight complexes, including the tame strict-node complex and exact reduction by a finite wild image. Book 37 supplies the Frobenius--Verschiebung formalism, purity, and duality used to identify global strata. Book 35 supplies quotients by finite locally free subgroups and descended polarizations. Book 58 supplies faithful flatness and exactness of completion and the distinction between completing a known proper model and algebraizing an abstract formal space. Book 70 supplies the maximal-Cohen--Macaulay freeness criterion over a regular local ring and the warning that it fails over a singular target. Book 76 supplies the selected special Weil--Deligne normalization used to compare the Iwahori scalar with geometric Frobenius. Book 118 supplies the exact common-norm Hodge-lift obstruction that makes the direct mixed-signature input conditional. Book 119 supplies the exact direct rational tensors, generic PEL curve, and generic parahoric datum. Book 121 supplies the projective good vertex at odd places, its integral filtration-lifting theorem, universal family, and, at two, the characteristic-independent toric obstruction and flat-closure properness argument once an exact integral functor has been constructed.

The exact direct dependency row is

$$
\boxed{122\mid 10,11,12,13,16,17,22,35,37,58,70,76,118,119,121}. \tag{1.6}
$$

There are fifteen direct dependencies. The right-double-coset, transpose, central, and degree conventions are chosen to agree with Book 124 and are rederived in Section 9.3 for the residue-prime span. The packet theorem is a characteristic-zero statement conditional only on the already isolated curve packet described in its hypotheses; it imports no Ihara saturation, level-raising theorem, deformation theorem, or modularity-lifting theorem.

The downstream compatibility audit is as follows. Book 124 deliberately leaves a
level-prime polynomial open; (9.8) uses its incoming right-action convention and proves
only the new graph identity, not a spherical polynomial. Book 121's odd theorem is used
only at odd places, while its characteristic-independent rational toric argument is used
at two only after the complete dyadic tensor functor has been constructed here. Book 125
supplies the characteristic-zero packet factorization and multiplicity statement but no
bad-prime compatibility. Book 126's raw determinant convention gives
$\det\Phi=qs_v$, agreeing with (9.19), and its warning against replacing the raw carrier
by its semisimplification is retained. Book 127 constructs the global representation from
the curve packet but supplies no bad local scalar used in this proof. Theorem 9.1 supplies
exactly the graph-multiplicity-one and scalar input denoted $(\mathrm B_v)$ in Book 128,
under the stricter local ledger stated here; Book 128's separate raw-to-global condition
is untouched. Finally, the “normalized bad operator” in Book 168 is the
geometric-normalized scalar $\beta_v$ on the new line: in the present conventions it is
the eigenvalue of the raw unnormalized $U_v$, not of $q^{-1}U_v$. Thus Book 168 may use
this result in the stated split dyadic range, while all of its coefficient-prime,
raw-to-global, and purity hypotheses remain in force.

## 2. Iwahori PEL data and the integral curve

### 2.1 The periodic self-dual lattice chain

The dyadic argument first needs a smooth endpoint. This cannot be borrowed from the odd theorem merely by changing $p$ to $2$.

**Dyadic vertex construction.** Under the dyadically tensor-split ledger of Section 1.3, the distinguished hyperspecial PEL functor is represented by a smooth projective relative curve $\mathscr X/R$. It carries the universal abelian scheme and the exact order action, odd-degree polarization, determinant law, multiplier, orientation, and prime-to-two level. Its framed local model is $\mathbf P(U)$ over $R$.

The construction first identifies the deformation problem over arbitrary dyadic test
rings with one line in the explicitly alternating plane (1.5a); properness is proved only
after that integral identification. No step divides by two.

**Proof.** The projective-frame construction used for the generic PEL curve applies over $R$: embed the polarized abelian schemes by one fixed odd tensor power of an inducing ample line, impose the multiplication table of the product order $\prod M_2(\mathbf Z_2)$, Rosati compatibility, the universal determinant polynomial, multiplier, orientation, and odd prime-to-two level. These are closed or open-and-closed conditions in a bounded Hilbert parameter space. Odd full auxiliary level at least three kills automorphisms. Descent therefore gives a quasi-projective fine scheme $\mathscr M^{\mathrm{amb}}$ with its universal tuple. Its selected generic component union is the direct characteristic-zero Shimura curve of Book 119; take its schematic flat closure $\mathscr X$.

Frame the de Rham homology by the complete tensor $\Lambda_0$. Integral Morita reduction is valid over every $R$-algebra, including rings with nilpotents, because the order is literally a product of matrix rings. It turns the moving Hodge summand into a line direct summand $L\subset U\otimes S$. The $*$-paired summand is its annihilator and all inactive summands are fixed. For $x=ae+bf$, equation (1.5a) gives $\langle x,x\rangle=ab-ba=0$ already in $R$, so every line is isotropic even in residue characteristic two. Conversely the determinant ranks and annihilator condition reconstruct the full Hodge filtration from $L$. Thus the framed local-model functor is scheme-theoretically

$$
\mathbf P(U)\simeq\mathbf P^1_R,                            \tag{2.0}
$$

not merely after reduction or on geometric points.

The chain-frame group is smooth. On the active plane it is
$\operatorname{GSp}(U,\langle\ ,\ \rangle)=\operatorname{GL}(U)$, since for a rank-two alternating plane the multiplier is the determinant; this identity is valid over $\mathbf Z_2$. The inactive matrix factors and the common multiplier fiber product are smooth by the tensor-split hypothesis. The filtration-lifting argument of Book 121, Proposition 4.1, uses Grothendieck--Messing on divided-power evaluations and Serre--Tate reconstruction and does not require $p$ to be odd. With the exact dyadic tensor calculation above, it makes the framed morphism to (2.0) smooth. The frame torsor is smooth and locally nonempty. Hence $\mathscr M^{\mathrm{amb}}$ is smooth of relative dimension one. For a smooth morphism, the relative connected-component sheaf is etale; the decomposition-stability hypothesis in Section 1.3 says that the selected generic union is a union of those etale components. Its flat closure is therefore open and closed in $\mathscr M^{\mathrm{amb}}$. This proves smoothness and constructs the universal dyadic vertex without appealing to Book 121, Theorem 12.1.

It remains to prove properness. The Raynaud torus argument of Book 121, Sections 6.1--6.2 and 11.1, is rational and characteristic-independent: a nonzero toric cocharacter space would be a unital left $B$-module of rational dimension at least $\dim_{\mathbf Q}B$, but the abelian dimension is only half that number. Thus every trait degeneration has potential good reduction. Pass to a normal full level at an odd auxiliary prime. The principal congruence kernel there has no nontrivial finite torsion, so potential good reduction descends to the original trait. The projective-closure argument then excludes a vertical boundary of $\mathscr X$; finite descent returns to the chosen neat level. Therefore $\mathscr X$ is proper, hence projective because it is quasi-projective. $\square$

This proof also shows the exact role of complete splitting. A symplectic basis for one abstract plane would not by itself identify the order action, the $*$-annihilator, or the orientation on the full PEL filtration. Those identifications are hypotheses in Section 1.3 and are used functorially above.

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

This inverse-image definition retains the common similitude and every fixed packet. Forgetting the nonzero vertex recovers precisely the good functor of Book 121.

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
\phi^\vee\lambda_1\phi=p\lambda_0                         \tag{2.6}
$$

and the target kernel type is the one determined by the full self-dual chain. Both Lie
algebras satisfy their vertexwise determinant and orientation laws. The factor in (2.6)
is exactly $p$, not an unspecified similitude: the quotient kernel is killed by $p$, and
isotropy for the perfect pairing on $A_0[p]$ is precisely the descent condition for
$p\lambda_0$. If $g=\dim A_0$ and $d_H=\operatorname{rank}H$, then

$$
\deg\lambda_1=p^{2g}\deg\lambda_0/d_H^2.                  \tag{2.6a}
$$

Thus the packetwise rank of $H$, not merely its total degree, fixes the adjacent
polarization type.

Equivalently, specify a finite locally free, $\mathcal O$-stable,
polarization-isotropic subgroup $H\subset A_0[p]$ with exactly the packetwise ranks
of $\Lambda_1/\Lambda_0$ and the forced $*$-annihilator, put $A_1=A_0/H$, and use
Book 35 to descend $p\lambda_0$. Unless $H$ is globally Lagrangian, $\lambda_1$ has
nontrivial $p$-primary kernel. This is another reason $A_1$ is not a second good
endpoint.

The displayed theorem in Book 35 is stated first for a principal polarization, but
the proof applies here without strengthening its input. Since $p\nmid\deg\lambda_0$,
$\lambda_0$ identifies $A_0[p]$ with $A_0^\vee[p]$, so the induced Weil pairing on
$A_0[p]$ is perfect. The theta-group argument of Book 35, Sections 9.2--9.3, uses
only that perfect pairing: isotropy splits the restricted commutator extension fppf
locally, the resulting polarization homomorphisms glue, and faithful flatness of
$A_0\to A_1$ gives uniqueness. It therefore produces the global $\lambda_1$
satisfying (2.6), while the pullback degree identity gives (2.6a).

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

**Theorem 2.2 (projective parahoric model).** At neat prime-to-$p$ level, in either local situation of Section 1.3, the functor of Section 2.2 is represented by a projective flat $R$-scheme $\mathscr C_{\mathrm{Iw}}$ of finite presentation. Its generic fiber is the selected direct quaternionic Shimura curve at level $K_p^{\mathrm{Iw}}K^p$, and it carries the universal isogeny (2.5).

**Proof.** Forget $H$ and map to the projective good model $\mathscr X$: at an odd place this is Book 121, Theorem 12.1, and at the dyadic place it is the construction at the start of Section 2.1. The relative Hilbert scheme of subschemes of the finite locally free group $\mathcal A[p]$ is projective over $\mathscr X$. Its universal subscheme is flat with its fixed Hilbert polynomial. Being a subgroup, $\mathcal O$-stable, isotropic, and of the prescribed total and packetwise ranks are closed or open-and-closed conditions. Quotienting by the universal finite locally free subgroup gives $A_1$, and Book 35 descends $p\lambda_0$. Equation (2.6), formula (2.6a), the target kernel type, the determinant laws, and the orientation cut out a closed and open-and-closed locus. This represents the functor and carries its universal chain.

Over $K$, the kernel is the required parahoric flag, so the generic fiber is correct. Valuatively, the good vertex extends by projectivity of $\mathscr X$; the schematic closure of the generic kernel in $A_0[p]$ is finite and torsion-free over the valuation ring, hence flat. All subgroup and tensor identities extend by closure, and the quotient and polarization then extend uniquely. Flatness follows from Proposition 2.1 and the local-model diagram below. $\square$

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

**Proof.** The integral automorphism group of the chain is smooth. On the active factor it is the standard smooth $\mathrm{GL}_2$ lattice-chain group; its special fiber maps onto the Borel with a smooth affine-unipotent kernel, but is not identified with that lower-dimensional Borel. Inactive factors are the hyperspecial groups of Book 121, and imposing the common smooth similitude character preserves smoothness. Elementary divisors and the dual-annihilator condition make the frame torsor locally nonempty, so $a$ is a torsor.

For $b$, apply the integral Hodge-filtration lifting argument used in Book 121 at both vertices. It is valid at two because it uses divided-power evaluations and because the full dyadic filtration functor was identified scheme-theoretically in Section 2.1. On such an evaluation, deformations of the isogeny chain are exactly filtration lifts compatible with the two lattice maps. Proposition 2.1 shows that all algebra, polarization, determinant, and orientation equations are already the equations of $M^{\mathrm{Iw}}$. Compatibility with crystal maps lifts the isogeny; its kernel retains the fixed finite locally free index, and Book 35 reconstructs the quotient and polarization. Prime-to-$p$ level lifts uniquely, and descent reconstructs the abelian chain over the original thickening. Thus $b$ is formally smooth, hence smooth by finite presentation. The frame dimensions agree. $\square$

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

**Proof.** Write $L_0=[a:b]$ and $L_1=[c:d]$ in the bases of (2.2). The first incidence condition is

$$
ad-\pi bc=0,                                                 \tag{3.2a}
$$

and the second is the negative of the same equation. Thus no additional equation, embedded component, or factor of two is hidden in the functor. In the chart $b,c\ne0$, put $x=a/b$ and $y=d/c$, so

$$
L_0=R(x,1),\qquad L_1=R(1,y).
$$

Equation (3.2a) is $xy=\pi$; equivalently the first condition says that $(x,\pi)$ is proportional to $(1,y)$, and the second gives the same equation. On $a,c\ne0$ the equation is $d/c=\pi(b/a)$; on $b,d\ne0$ it is $a/b=\pi(c/d)$. These are affine lines over $R$. On $a,d\ne0$ it is $1=\pi(b/a)(c/d)$, so $\pi$ is invertible and the chart is smooth over the generic open. These four charts cover $M^{\mathrm{Iw}}$.

The nodal ring is torsion-free over $R$. At its closed point $\pi=xy$, so the maximal ideal is generated by $x,y$; dimension and embedding dimension are both two. Hence the total space is regular. Modulo $\pi$, equation (3.2a) is $ad=0$: its two reduced components are $a=0$ and $d=0$, each a projective line, and they meet only at $a=d=0$ in the nodal chart. Every calculation is integral over $\mathbf Z$, so in particular it remains valid for $\pi=2$. $\square$

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

Let $\mathscr X$ be the distinguished smooth projective hyperspecial model obtained by forgetting the Iwahori flag. Put $X_0=\mathscr X_k$ and $X=X_0\otimes_k\bar k$. The active idempotent of the universal $p$-divisible group is a one-dimensional height-two group $G$ over $X_0$. Verschiebung on its Hodge line defines over $k$

$$
\operatorname{Ha}:\omega_G\longrightarrow\omega_G^{(p)},
\qquad
\operatorname{Ha}\in H^0(X,\omega_G^{\otimes(p-1)}).        \tag{4.2}
$$

Write $Z_0=V(\operatorname{Ha})$ and $Z=Z_0\otimes_k\bar k$.

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
$\operatorname{Hom}(\omega_G,M/\omega_G)$, the single direction in Book 121's good local
model at odd $p$ and in (2.0) at $p=2$. Both completed deformation rings are formally smooth of
dimension one and the tangent map is an isomorphism, yielding (4.4). Verschiebung on the Hodge
line reduces to multiplication by $t$. This calculation uses only the exact alternating identity
and $FV=VF=p$; it neither divides by $2$ nor infers alternation from skew-symmetry, so it applies
unchanged at the dyadic vertex.

An ordinary height-two group has multiplicative and etale height-one factors, giving the two subgroups above. The second subgroup must be written on the inverse twist to be a subgroup of the fixed source $G$. In the local-local display their two lines coincide in the unique admissible $\alpha_p$. $\square$

The completed equation $t=0$ shows that every geometric zero has multiplicity one. Since $X_0$ is a proper smooth curve, $Z_0$ is therefore finite etale over $k$, and

$$
\#Z(\bar k)=\deg Z=(p-1)\deg\omega_G.                       \tag{4.5}
$$

If the selected generic curve is geometrically connected, proper flatness makes the special fiber connected. Since it has two labeled branches, $Z$ is nonempty. This proves positivity without trivializing the determinant--multiplier line in Book 121's Kodaira--Spencer formula.

### 4.3 Global branch normalization

Put $Y_0=\mathscr C_{\mathrm{Iw},k}$ and $Y=Y_0\otimes_k\bar k$. Write

$$
X_{F,0}=X_0,
\qquad
X_{V,0}=X_0^{(p)},
$$

and let $X_F,X_V$ be their geometric fibers. These are descended labeled copies, not
two hyperspecial lattice vertices. The second label records the Frobenius twist forced by
the source of Verschiebung.

Reassemble $\ker F_G$ with its forced $*$-paired annihilator and zero summands in inactive packets. If $e,e^*$ are distinct paired primitive idempotents and $\operatorname{Rec}$ denotes integral Morita reassembly, the active subgroup is

$$
H_F=\operatorname{Rec}_{e}(\ker F_G)
\oplus
\operatorname{Rec}_{e^*}\bigl((\ker F_G)^\perp\bigr).       \tag{4.6}
$$

In a self-paired alternating packet the line is its own orthogonal, so only one reassembled summand is taken. The subgroup is finite locally free, $\mathcal O$-stable, and isotropic. Book 35 supplies the quotient and the adjacent polarization type. Because relative Frobenius and orthogonal complementation are defined over $k$, this gives

$$
j_{F,0}:X_{F,0}\longrightarrow Y_0,
$$

and its geometric base change $j_F:X_F\to Y$.

For the other branch use the Frobenius-twisted good family. Reassemble the kernel of

$$
V_G:G^{(p)}\longrightarrow G
$$

inside the twisted source, again with its forced annihilator. Book 35 gives the adjacent polarized quotient and a descended morphism

$$
j_{V,0}:X_{V,0}\longrightarrow Y_0,
$$

whose geometric base change is $j_V:X_V\to Y$.

This construction does not identify that quotient with the original good family. For a fixed geometric source it is exactly the inverse-twist subgroup (4.3).

Lemma 4.2 shows that these subgroup types exhaust the ordinary locus and coincide precisely on $Z$. Scheme-theoretically, the two choices are the minimal primes $(x)$ and $(y)$ of $\bar k[[x,y]]/(xy)$, while (4.4) identifies their common parameter with the Hasse parameter. The completed map from either labeled good copy to its branch is an isomorphism, after the Frobenius-twist parameterization on the $V$ side. Thus $j_F,j_V$ are proper and quasi-finite, hence finite; they are birational from normal curves and therefore normalize the two branches. Both occur with multiplicity one, meet exactly in the identified copies of $Z$, and cover $Y$.

The degeneracy map retaining the distinguished source is the identity on $X_F$ and Frobenius on $X_V$. The quotient degeneracy map lands first in the adjacent polarization-type functor; only after the fixed opposite dual-chain identification is it Frobenius on $X_F$ and the identity on $X_V$. Calling both legs identities on one good model would erase the chain orientation.

The common embeddings descend:

$$
\iota_{F,0}:Z_0\hookrightarrow X_{F,0},
\qquad
\iota_{V,0}:Z_0\hookrightarrow X_{V,0}.                   \tag{4.7}
$$

Their geometric base changes are denoted $\iota_F,\iota_V$. They are the Hasse
inclusions up to the Frobenius twist on the second normalization. That twist is a universal
homeomorphism and hence does not change prime-to-$p$ etale cohomology.

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

### 4.5 The descended normalization and node complex

**Theorem 4.3 (two-branch normalization over the residue field).** There is a finite
normalization

$$
\nu_0:\widetilde Y_0=X_{F,0}\amalg X_{V,0}\longrightarrow Y_0. \tag{4.9a}
$$

Write $i_0:Z_0\hookrightarrow Y_0$ for the common image. Its conductor is $Z_0$ on
$Y_0$ and the disjoint union of the two copies in (4.7) on
$\widetilde Y_0$. More precisely, $Y_0$ is the scheme pushout which identifies
$\iota_{F,0}(z)$ with $\iota_{V,0}(z)$ for every $z\in Z_0$, and its structure
sheaf is the fiber product

$$
\mathcal O_{Y_0}\simeq
j_{F,0*}\mathcal O_{X_{F,0}}
\times_{i_{0*}\mathcal O_{Z_0}}
j_{V,0*}\mathcal O_{X_{V,0}}.                              \tag{4.9b}
$$

Thus the conductor square is cartesian on ideals and cocartesian on schemes. For every
$\ell\ne p$ it gives the exact normalization sequence

$$
0\longrightarrow E_{\ell,Y_0}
\longrightarrow \nu_{0*}E_{\ell,\widetilde Y_0}
\xrightarrow{\ \delta\ }i_{0*}E_{\ell,Z_0}
\longrightarrow0,                                           \tag{4.9c}
$$

where, after the displayed order of the branches is fixed,

$$
\delta(a_F,a_V)=\iota_{V,0}^{*}a_V-\iota_{F,0}^{*}a_F.      \tag{4.9d}
$$

**Proof.** The two maps in Section 4.3 are finite, are generically isomorphisms onto
the two irreducible branches, and have normal sources. It remains to identify the
conductor and the gluing, which may be checked faithfully after completing at a geometric
point. At a node the completed special-fiber ring and its normalization are

$$
\bar k[[x,y]]/(xy)
\longrightarrow \bar k[[x]]\oplus\bar k[[y]],
\qquad
f\longmapsto(f(x,0),f(0,y)).                                \tag{4.9e}
$$

The image consists exactly of pairs with the same constant term, and the conductor is
$(x)\oplus(y)$, with quotient $\bar k$ on all three occurrences. Thus the original
ring is the fiber product of the two branch rings over $\bar k$. Away from $Z$ the
normalization is an isomorphism. Completion therefore proves both assertions in (4.9b),
and faithful flat descent proves them over $k$: the branch maps and the two conductor
embeddings were constructed over $k$, while geometric Frobenius preserves their labels.

For an etale test scheme, a locally constant pair of sections on the two branches descends
precisely when its two values at every preimage of a node agree. This proves exactness of
(4.9c) and fixes the sign in (4.9d). Surjectivity is local at a node, where the pair
$(0,1)$ maps to $1$. No division by $p$, and in particular no division by $2$, occurs.
$\square$

After base change to $\bar k$, taking global degree-zero sections in (4.9c) gives the
two-term node complex

$$
C^0=H^0(X_F,E_\ell)\oplus H^0(X_V,E_\ell)
\xrightarrow{\ \rho\ }
C^1=H^0(Z,E_\ell),
\quad
\rho(a_F,a_V)=\iota_V^*a_V-\iota_F^*a_F.                  \tag{4.9f}
$$

On geometric bases its signed transpose is

$$
\partial:E_\ell[Z(\bar k)]\longrightarrow
E_\ell[\pi_0(X_F)]\oplus E_\ell[\pi_0(X_V)],
\qquad
[z]\longmapsto[\iota_Vz]-[\iota_Fz].                       \tag{4.9g}
$$

Consequently $H^1(\Gamma,E_\ell)=\operatorname{coker}\rho$ and
$H_1(\Gamma,E_\ell)=\ker\partial$. These formulas, rather than an unlabeled
normalization, define the signed Frobenius action: a descent element that exchanges the
two labels multiplies an oriented edge by $-1$.

### 4.6 The connected two-branch calculation

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

An ordinary prime-to-$p$ deck map does not change the $p$-level or oriented lattice chain. It commutes with the split idempotents and with $F,V$, so it preserves the Hasse and branch strata. A free quotient remains semistable etale-locally. If a deck orbit identifies two geometric branch components, the ordered-strata calculation stays on the fine cover with its descent action. With stabilizers, one works equivariantly on the fine cover or quotient stack; the coarse quotient can be singular, and a universal PEL family descends only under the qualifications of Book 121.

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
\xleftarrow{\ \pi\ }
\mathscr C_{\mathrm{Iw},K\cap gKg^{-1}}
\xrightarrow{\ r_g\ }
\mathscr C_{\mathrm{Iw},K}.                                 \tag{9.1}
$$

Here $\pi$ is the forgetful leg and $r_g$ first translates the right level structure by
$g$ and then forgets. This is the right-action convention of Book 124. On a smaller
selected union, the right target is its Hecke translate unless $g$ preserves the union. At
fine level the legs are finite etale. The universal prime-to-$p$ isogeny preserves the
$p$-adic lattice chain, commutes with all split idempotents and with $F,V$, and carries the
Hasse section to a unit multiple. Hence it preserves the $F/V$ branch labels, $Z$, the
oriented graph, and thickness.

The unnormalized double-coset operator and its transpose are

$$
T_g=\pi_*r_g^*=[KgK],
\qquad
T_g^t=r_{g*}\pi^*.                                           \tag{9.2}
$$

Thus the pushforward is along the forgetful leg, not along the translated leg. No inverse
degree or square-root factor is hidden in (9.2). Multiplying by a degree preserves
commutation with monodromy but changes the scalar and can change an integral lattice.

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

The quotient abelian scheme gives a second route to the adjacent chain-vertex PEL functor. This target is not a second good model of Book 121: its polarization type is the one forced by the modular vertex. After applying the fixed opposite dual-chain reparameterization used in the generic level tower, write the resulting target and map as

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

Both $d_0$ and $d_1$ are finite locally free of degree $q+1$. Indeed, they are projective and
generically finite of that degree. Theorem 4.3 gives the whole special fiber as the two stated
reduced branches, with no vertical component, and (9.4)--(9.6) restrict either map on each
normalized branch to an identity or a relative Frobenius. These restrictions are finite, so
every geometric special-fiber fiber is finite; the generic fibers are finite as well. Hence the
maps are proper and quasi-finite, and therefore finite. Locally the source and target are
regular surfaces. The source ring is Cohen--Macaulay over the regular target ring, and a target
system of parameters is a source regular sequence. The finite module is consequently maximal
Cohen--Macaulay and hence free. Its rank is the generic degree $q+1$.

### 9.3 The actual residue-prime correspondence

Return to either local situation of Section 1.3 and now write $v$ for the selected
place, $q=q_v$, $I=K_v^{\mathrm{Iw}}$, and

$$
h=\begin{pmatrix}\pi&0\\0&1\end{pmatrix}
$$

in the active Morita plane. In the dyadic case $q=2$. Put
$I_h=I\cap hIh^{-1}$. The generic double-coset span is

$$
C_I\xleftarrow{\ \pi_h\ }D_{I_h}
\xrightarrow{\ r_h\ }C_I,                                  \tag{9.7}
$$

where $\pi_h$ forgets the additional vertex and $r_h$ translates the oriented chain by
$h$ before forgetting. A point of $D_{I_h}$ is equivalently a length-two oriented PEL
isogeny chain, with the same determinant, orientation, and paired-annihilator conditions
at all three vertices. The residue-prime operator is, by definition,

$$
U_v=(\pi_h)_*r_h^*=[IhI],
\qquad
U_v^t=(r_h)_*\pi_h^*.                                      \tag{9.8}
$$

These formulas make $U_v$ the incoming right-coset operator. Indeed

$$
IhI=\coprod_{a\in k}
\begin{pmatrix}\pi&[a]\\0&1\end{pmatrix}I,
                                                        \tag{9.9}
$$

for any Teichmuller lifts $[a]$. Thus both generic legs have the appropriate finite
degree and $U_v$ has degree $q$; in particular it acts by $2$ on constants in the
dyadic case. Let

$$
S_v=[I(\pi I_2)I]                                           \tag{9.10}
$$

be the one-sheet central correspondence. It is retained as an operator, not replaced by
a central-character scalar.

There is a canonical proper integral extension of (9.7). Over the good vertex form the
iterated relative Hilbert scheme of two consecutive finite locally free PEL subgroups,
impose the order action, isotropy, paired annihilators, three determinant laws, and both
chain polarization identities, and take the schematic flat closure of the generic
$D_{I_h}$. Normalize that closure and call it $\mathscr D$. Retaining the first or
second length-one subchain gives the two projections to
$\mathscr C_{\mathrm{Iw}}$, so no choice of an image in the product can identify
different intermediate subgroups. The relative flag Hilbert scheme is projective, hence
$\mathscr D$ is proper over both factors.

To see that no horizontal sheet has been lost, frame all three de Rham lattices. Morita
reduction gives three lines and two consecutive copies of (2.7). The generic fiber is the
disjoint right-coset list (9.9), and schematic flat closure is precisely saturation with
respect to $\pi$; it has no vertical associated component by construction. Normalized
blowups of the nodal strata give a regular common domination if one is needed to define
pull--push on nearby cycles. More intrinsically, the closure of the generic graph, with
generic multiplicity one on every sheet, defines a relative cycle in
$\mathscr C_{\mathrm{Iw}}\times_R\mathscr C_{\mathrm{Iw}}$. On a regular domination
its strict transform, rather than properness of one leg by itself, supplies the
degree-zero cohomological correspondence. The projection formula makes the action
independent of the chosen domination. This qualification matters when a special flag
fiber is contracted by one projection. It constructs the actual residue-prime
correspondence in characteristic zero and its integral specialization.

### 9.4 The calculation on oriented edges

The calculation that distinguishes degree from graph multiplicity is local. Let $z$ be a
geometric node, use the chart $xy=\pi$ of (3.2), and orient its edge from the $F$ branch
to the $V$ branch. Reducing the matrices in (9.9) in the length-two line-incidence
equations gives the following complete list.

1. For $a=0$, both retained length-one chains are local-local. The corresponding
   component of the normalized closure has completed ring

   $$
   R^{\mathrm{sh}}[[u,w]]/(uw-\pi).                         \tag{9.11}
   $$

   On each branch both projection maps have ramification index one. The translated leg
   meets the node $z$, while the forgetful leg meets the node $\Phi z$ obtained by
   geometric Frobenius on the descended Hasse point. The parity change in the periodic
   lattice chain changes which of the two lattice maps is diagonal $(1,\pi)$; with the
   branch labels transported by that chain, both projections preserve the ordered
   $F,V$ labels.

2. For $a\ne0$, the reduction of
   $\left(\begin{smallmatrix}\pi&[a]\\0&1\end{smallmatrix}\right)$ has a
   nonzero off-diagonal entry. Solving the two incidence equations makes one of the two
   retained Hodge lines ordinary. Consequently the closure is smooth there and one
   projection factors through $X_F$ or $X_V$ away from its conductor. Such a sheet
   contributes to the normalization-component term and not to the node-to-node edge
   term.

For completeness, the node-to-node assertion has an equation-level check. In bases for
three consecutive vertices write the active lines on the node charts as

$$
L_0=(x,1),\qquad L_1=(1,y),\qquad L_2=(z,1).
$$

For the representative $a=0$, the two incidence determinants are

$$
xy=\pi,\qquad yz=\pi.                                      \tag{9.12}
$$

Their difference is $y(z-x)=0$. On the generic fiber $y$ is invertible, so saturation
with respect to $\pi$ adds $z-x$; the flat closure is exactly
$R^{\mathrm{sh}}[[x,y]]/(xy-\pi)$. This proves (9.11) and gives expansion index one
for both projections. It also fixes the orientation sign. The first retained subchain has
ordered node coordinates $(x,y)$. Because the maps between the next pair of periodic
lattices are $(\beta,\alpha)$ rather than $(\alpha,\beta)$, the second retained subchain
has ordered node coordinates $(z,y)$, not $(y,z)$. Since $z=x$, each projection carries
$x=0$ to the $F$ branch and $y=0$ to the $V$ branch. Thus the node sheet is orientation
preserving; no hidden minus sign occurs in (9.13).

For $a\ne0$, reduction of the matrix in (9.9) sends the nodal axis $k(0,1)$ to
$k([a],1)$, whereas the unique local-local line at the next incidence is the coordinate
axis $k(0,1)$. These lines differ because $[a]$ is a unit. Hence the two retained
subchains cannot both be nodal. In the corresponding affine incidence chart one coordinate
is a unit, the remaining equation eliminates one variable, and the closure is smooth.
This exhausts (9.9), proves that all relevant local lengths are one, and is unchanged
when $\pi=2$; for $q=2$ the complete list is $a=0,1$.

If a special flag fiber has positive dimension, the same coordinate-unit calculation
shows that both of its images lie in smooth branch strata. Its correspondence class
therefore factors through normalized component cohomology. On the sole node-to-node
stratum (9.11), both maps are finite admissible maps of expansion index one. Thus no
contracted vertical flag curve contributes to the edge complex.

There is a variance point in the first case. The relative-Frobenius quotient morphism on
moduli points sends a $\bar k$-point to its arithmetic $q$-power conjugate
$\Phi^{-1}z$. In (9.8) that morphism occurs on the leg from which one pulls back, while
the trace is along the forgetful leg. Solving for the source of a prescribed translated
point therefore replaces $\Phi^{-1}$ by $\Phi$. This is why the node in the
forgetful fiber is $\Phi z$, rather than $\Phi^{-1}z$.

Book 16's finite-map graph formula on those admissible node strata says that a correspondence
$\beta_*\alpha^*$ sends an oriented edge through every node-to-node branch, weighted by
its expansion index. Applying that formula to (9.11)--(9.12), with
$\alpha=r_h$ and $\beta=\pi_h$, proves the chain-level identity

$$
U_{v,1}[z]=[\Phi z]
\quad\text{on }C_1(\Gamma,E_\ell).                          \tag{9.13}
$$

The same flag calculation on branch endpoints shows
$\partial U_{v,1}=U_{v,0}\partial$, so (9.13) descends to
$H_1(\Gamma,E_\ell)$. The opposite correspondence acts there by $\Phi^{-1}$.
The action of $U_v$ on the dual node complex is the dual of that opposite action, hence
again $\Phi$ on $H^1(\Gamma,E_\ell)$. This is the pull--push variance used in
Theorem 9.1. Notice the normalization check:

$$
\deg U_v=q,\qquad
\deg(U_v\text{ on node-to-node branches})=1.                \tag{9.14}
$$

The remaining $q-1$ sheets have not disappeared; they act through normalized component
cohomology. Thus constants still have eigenvalue $q$.

Two consecutive **node-to-node** modifications replace an oriented lattice edge by its
$\pi$-translate. Although the transported periodic labels remain orientation preserving,
the second lattice inclusion is represented by the opposite diagonal map and therefore
uses the opposite geometric kernel: on the PEL chain the composite kernels are relative
Frobenius followed by Verschiebung, or conversely. Since $FV=VF=[\pi]$, transport
of the prime-to-$v$ level is exactly the central translate (9.10). The other sheets in
the generic convolution pass through a smooth component stratum. Hence the same chart
calculation gives

$$
U_{v,1}^{\,2}=S_v,\qquad
U_{v,1}^{\,t}=U_{v,1}^{-1}=S_v^{-1}U_{v,1}                 \tag{9.15}
$$

on graph homology and cohomology. The middle equality uses the unit edge pairing.
It is not an identity between the two full degree-$q$ correspondences: $U_v^t$ remains
the opposite operator on constants and on the old/component contribution.

### 9.5 The bad-prime Eichler--Shimura theorem

We state the packet hypothesis exactly at the interface supplied by Book 125. Let
$E/\mathbf Q_\ell$ be a finite splitting field with $\ell\ne p$, enlarged once if the
centered notation requires a choice of $q^{1/2}$, and let $\Pi$ be a cohomological
weight-two packet in the established compact quaternionic curve range. Assume the
characteristic-zero automorphic decomposition and global multiplicity-one statement give

$$
H^1(C_{I,\bar K},E)[\Pi]
\simeq P_{\Pi,I}\otimes_E W_\Pi^{\mathrm{raw}},
\qquad \dim_EW_\Pi^{\mathrm{raw}}=2,                        \tag{9.16}
$$

where $P_{\Pi,I}=P_\Pi^v\otimes\Pi_v^I$ and
$\dim\Pi_v^I=1$. Assume also the corresponding good-level decomposition for
$X_F$ and $X_V$: after away-from-$v$ packet extraction, occurrence on either
normalization component forces a nonzero $K_v$-fixed vector in $\Pi_v$. This is the
exact good-level support statement used below; it is not deduced from (9.16) alone.
More precisely, let $A^v$ be a finite semisimple
away-from-$v$ Hecke image separating $\Pi^v$, and for an $A^v$-module $M$ write

$$
\mathcal M_\Pi(M)=
\operatorname{Hom}_{A^v}(P_\Pi^v,M[\Pi^v]).
$$

The word **multiplicity** below means dimension after this Hom extraction and after the
one-dimensional factor $\Pi_v^I$ has been identified; it never means the dimension of
the whole isotypic space $P_{\Pi,I}\otimes W$. Here $\Pi$ is in Book 125's unitary
constant-coefficient automorphic normalization. At the selected place suppose

$$
\Pi_v=\operatorname{St}\otimes\mu_v
$$

with $\mu_v$ unramified, in the selected special row of Book 76. Let
$u_v$ be the scalar of the unnormalized right-coset operator (9.8) on
$\Pi_v^I$, and let $s_v$ be the scalar of $S_v$. With geometric Frobenius and
the uncentered weight-two cohomological normalization, the identities are

$$
u_v=\beta_v=\mu_v(\Phi),
\qquad u_v^2=s_v.                                           \tag{9.17}
$$

Here $\mu_v(\Phi)$ means $\mu_v(\pi)$ under the geometric-reciprocity convention
that sends a uniformizer to $\Phi$. There are two normalizations here and they must
not be merged. Book 76's centered
parameter $\operatorname{Sp}_2(\mu_v)$ has kernel eigenvalue
$\mu_v(\Phi)q^{-1/2}$. Untwisted weight-two $H^1$ uses its cohomological
$|\,\cdot\,|^{-1/2}$ shift, which multiplies both geometric-Frobenius roots by
$q^{1/2}$ and makes the kernel root $\mu_v(\Phi)$. The raw Iwahori-Hecke calculation
has the same normalization: evaluate the $q$ representatives (9.9) on the
one-dimensional Steinberg quotient of the two-dimensional Iwahori-fixed space at the
reducibility wall. The raw operator acts there by $\mu_v(\Phi)$, while on the
one-dimensional character quotient it acts by $q\mu_v(\Phi)$. Twisting twice gives the
one-sheet central action $\mu_v(\Phi)^2$, so $u_v^2=s_v$. Thus neither $q^{-1}U_v$
nor $q^{-1/2}U_v$ occurs in (9.17).

**Theorem 9.1 (bad-prime Eichler--Shimura at a split one-step Iwahori).**
Under these hypotheses, including the dyadically tensor-split case $q=2$:

1. the extracted normalization-component term
   $\mathcal M_\Pi(H^1(X_F,E)\oplus H^1(X_V,E))$ is zero;
2. each of $\mathcal M_\Pi(H^1(\Gamma,E))$ and
   $\mathcal M_\Pi(H_1(\Gamma,E))$ has dimension one, and $N$ has rank one
   on $W_\Pi^{\mathrm{raw}}$;
3. geometric Frobenius on the raw invariant graph line is $u_v=\beta_v$.

Consequently

$$
\operatorname{WD}_v(W_\Pi^{\mathrm{raw}})^{\mathrm{F\!-\!ss}}
=\operatorname{St}(\beta_v),                               \tag{9.18}
$$

so in a basis $Ne_1=e_0$,

$$
\Phi e_0=u_ve_0,\qquad
\Phi e_1=qu_ve_1,\qquad
\det(\Phi)=qu_v^2=qs_v,                                    \tag{9.19}
$$

and

$$
P_v(T)=1-u_vT,\qquad a_v(W_\Pi^{\mathrm{raw}})=1.           \tag{9.20}
$$

**Proof.** The normalization components are good curves with hyperspecial level at
$v$ (the $V$ copy differs only by a Frobenius twist). Their characteristic-zero
automorphic decomposition can contain the $\Pi$-packet only through $\Pi_v^{K_v}$.
But an unramified Steinberg twist has $\Pi_v^{K_v}=0$. Exactness of
$\mathcal M_\Pi$ in characteristic zero therefore kills the entire middle term

$$
\mathcal M_\Pi\bigl(H^1(X_F,E)\oplus H^1(X_V,E)\bigr)=0     \tag{9.21}
$$

of the weight spectral sequence. This proves the first assertion without an Ihara
lemma or a saturation statement.

Apply $\mathcal M_\Pi$ to (6.7). The two outer graph terms are paired perfectly and
$N$ identifies the upper term with the Tate twist of the lower one, so they have the
same dimension, say $d$. Equation (9.16), the one-dimensional space $\Pi_v^I$,
global multiplicity one, and (9.21) give $2=2d$. Hence $d=1$ and $N$ is the
nonzero isomorphism between two lines; in particular it has rank one.

Finally, $U_v$ commutes with $A^v$ and acts on the remaining factor $\Pi_v^I$ in
(9.16) by $u_v$, while geometric Frobenius acts on $W_\Pi^{\mathrm{raw}}$. The
correspondence calculation (9.13), after applying $\mathcal M_\Pi$, identifies these
two endomorphisms on the one-dimensional invariant graph line. Therefore

$$
\Phi\mid H^1(\Gamma,E)[\Pi]=u_v,
$$

with no sign or degree ambiguity. Equations (9.17), (6.8), and
$\Phi N\Phi^{-1}=q^{-1}N$ force the partner eigenvalue $qu_v$ and prove
(9.18)--(9.20). $\square$

Arithmetic Frobenius is $\Phi^{-1}$, so its untwisted eigenvalues in (9.19) are
$u_v^{-1}$ and $(qu_v)^{-1}$. Geometric Frobenius on the Tate twist
$W_\Pi^{\mathrm{raw}}(1)$ has eigenvalues $q^{-1}u_v$ and $u_v$; arithmetic
Frobenius on that twist has eigenvalues $qu_v^{-1}$ and $u_v^{-1}$. None of these
converted pairs is to be substituted into (9.20), which is the untwisted geometric
convention. The transpose acts on the invariant graph line by

$$
u_v^t=s_v^{-1}u_v=u_v^{-1},                                \tag{9.22}
$$

exactly as (9.15) requires. The theorem is a statement about the raw characteristic-zero
cohomological packet. Passing it to a separately constructed global Galois representation
still requires the raw-to-global comparison of Book 128; no modularity lifting theorem,
$R=\mathbf T$ theorem, level raising, Ihara saturation, or higher-dimensional model has
been used here.

In the split dyadic FLT normalization with trivial central component character,
$q=2$ and $s_v=1$. Thus $u_v=\pm1$, the geometric Frobenius eigenvalues are
$u_v,2u_v$, the determinant is $2$, the Euler polynomial is $1-u_vT$, and the
transpose has the same scalar $u_v$ on the new line. This specialization is a
consequence of the proved raw identities, not a replacement of $U_v$ by a
degree-normalized operator.

### 9.6 The degeneracy complex and its boundary

After a chosen identification $\mathscr X'\simeq\mathscr X$ in the relevant level tower, the two pullbacks form

$$
d^*=(d_0^*,d_1^*):
H^1(\mathscr X_{\bar K},E_\ell)^{\oplus2}
\longrightarrow
H^1(\mathscr C_{\mathrm{Iw},\bar K},E_\ell),                \tag{9.23}
$$

and proper traces form its adjoint route

$$
d_*=(d_{0*},d_{1*}).                                        \tag{9.24}
$$

On the special fiber, normalization replaces the target by $X_F\amalg X_V$, the restrictions of (9.23) are governed by the identity/Frobenius matrix in (9.4) and (9.6), and the failure to glue independently across the two copies is measured by the edge restriction map (6.3). Thus the old part, the graph quotient, and the monodromy line are all expressed using explicit maps of the good fiber and the Hasse set.

This book supplies that geometric complex but does not assert an Ihara lemma. Injectivity of (9.23), torsion-freeness of its localized cokernel, or a level-raising congruence requires the relevant Hecke localization and arithmetic input. What is available unconditionally is the exact branch routing, the signed graph matrix, the adjoint trace, and their compatibility with $N$, Frobenius, and the component pairing.

For the FLT level-change application, a Hecke-isolated two-dimensional constituent with nonzero image in the graph piece has $N\ne0$, conductor exponent one at split strict level, and special local type. A constituent supported only on normalized component cohomology has $N=0$. This dichotomy is geometric; identifying which Hecke eigensystem occurs is a separate automorphic step.

### 9.7 Functorial monodromy and projectors

Finite etale pullback and trace act on

$$
R\Gamma(Y,R\Psi E_\ell)
$$

and commute with inertia, Frobenius, restriction, Gysin, and $N$. On the graph they commute with $\partial$ and are adjoint for $q_\Gamma$, hence act on the component group (7.2). Every page of the weight spectral sequence is therefore a Hecke module.

For an idempotent $e$ in the rational prime-to-$p\ell$ Hecke algebra,

$$
eN=Ne,\qquad eF=Fe.                                         \tag{9.25}
$$

Thus $(r,N,F)$ restricts to $eV$. Conductors are additive on genuine direct sums, but not across arbitrary nonsplit exact sequences: one length-two monodromy block has conductor one while its two unramified semisimple subquotients each have conductor zero. Semisimplifying away $N$ can therefore change the conductor.

If $e$ exists only after coefficient extension, rational ranks are unchanged. If it has an $\ell$-denominator, it need not preserve an integral direct summand; the saturation warning of Section 7.3 applies.

At the bad prime itself, a degeneracy correspondence changes the lattice chain and need not be finite etale. Its integral extension is the explicit PEL isogeny diagram (9.3)--(9.6), not a consequence of the prime-to-$p$ construction.

### 9.8 Principal and ray towers over the parahoric diagram

Later type coefficients use objectwise normal principal levels at $v$, a common effective
Galois closure of their finite generic diagram, and, in the scalar family, a global ray
character ramified at $v$.  There are four different assertions here: existence
of the normalized tower, flatness of its objects over the fine base models, identification of
the lifted legs on one common normalization, and the completed stabilizer calculation.  The
first three follow from normalization and integrality; the last requires the principal local
model.

Let $a\in\{0,1,e\}$ denote the two adjacent vertex levels and their oriented edge level.  Write
$\mathscr X^a$ for the corresponding fine integral models; thus the vertex models are smooth
and the edge model is the regular semistable curve of Theorem 4.1.  At each object choose an
open principal subgroup normal in that object's compact level and include the fixed fine
prime-to-$v$ level. Choose a finite common refinement for the finitely many retained degeneracy
and Hecke legs whose chosen fine integral base maps are finite, and take the effective finite
Galois closure of this entire generic diagram
(componentwise, a common finite separable algebra).  Thus

$$
Y^a_\eta\longrightarrow X^a_\eta                              \tag{9.26}
$$

denotes the same effective generic cover equipped with its map to the $a$th quotient, not three
unrelated choices of normal closure.  If a global ray extension $K'/K$ is
used, take the fiber product of (9.26) with $K'$ before normalization.  Define
$\mathscr Y^a$ to be the normalization of $\mathscr X^a$ in that finite generic algebra.  This
definition, rather than a nominal quotient by a compact open with a central kernel, is the
**actual principal/ray tower**.

Such a common algebra exists because the diagram is finite: intersect the finitely many
principal subgroups only to obtain a common refinement, take the finite normal closure of the
resulting separable function-field extensions, and take the finite orbit of the selected
generic component union.  We do **not** assert that one open compact subgroup is normal in both
adjacent maximal parahorics: taking a core in one group does not preserve normality in the
other, so an intersection-of-cores argument does not establish that assertion.  The common
object is the effective Galois closure of actual principal-level covers, so “common” is a
construction, not an equality imposed on independently chosen normal closures.

**Proposition 9.2 (common normalization and flat lifted legs).** Each
$\mathscr Y^a\to\mathscr X^a$ is finite locally free. Every degeneracy or Hecke map whose
chosen fine integral base leg is finite, and which is generically compatible with the chosen
principal level, extends uniquely to a finite map between the corresponding normalizations.
These extensions commute with composition, the deck action,
residue Galois, and transpose on the generic fiber.  Along each finite leg of the fine
vertex--edge diagram, the lift on the common normalization is canonically an isomorphism; in
particular all principal top-level degeneracy legs are finite flat.

**Proof.** The fine models are excellent, so finiteness of normalization in a finite generic
algebra is the normalization theorem of Book 11.  Work at a point of $\mathscr X^a$.  Its local
ring $A$ is regular of dimension at most two.  A local factor $B$ of the normalization is normal
and finite over $A$, has the same dimension, and is Cohen--Macaulay: in dimension two this is
Serre's $S_2$ condition, while dimensions zero and one are immediate.  A regular system of
parameters of $A$ is a system of parameters of $B$ because $B/A$ is finite, hence is a
$B$-regular sequence.  Thus $B$ is maximal Cohen--Macaulay as an $A$-module.  Auslander--Buchsbaum
over the regular local ring $A$ makes $B$ free.  This proves finite local freeness objectwise.

For extension of a map, take an affine target $\operatorname{Spec}A$ and its finite inverse
image $\operatorname{Spec}C$ in the source base model.  An element of the target normalization
is integral over $A$; its generic pullback is therefore integral over $C$ and lies in the source
normalization.  This gives the unique ring map.  The source normalization is already finite as
an $A$-module, hence also finite over the target normalization.  Uniqueness on the schematically
dense generic fiber proves composition and equivariance.

For a leg using the common generic algebra $L$, more is true.  Because $C$ is integral over
$A$, an element of $L$ is integral over $A$ if and only if it is integral over $C$: one
direction uses $A\subset C$, and the other is transitivity of integrality.  Hence the two
integral closures inside $L$ are the same ring.  The lifted leg is therefore an isomorphism.
The argument applies componentwise to a finite generic algebra and to either embedding used by
the two oriented legs. $\square$

The finiteness of the fine integral base leg is essential to this extension argument. A
generic Hecke leg whose chosen integral closure is only proper and has a contracted vertical
fiber is not covered by Proposition 9.2; it must instead be treated by the graph/regular-
domination construction of Section 9.3, or replaced by a separately proved finite Stein
factor. Generic finiteness alone does not make an arbitrary proper integral model finite: the
blowup of $\operatorname{Spec}k[x,y]$ at the origin is normal, proper, and birational over the
normal affine plane, but its exceptional curve prevents the map from being finite. Normalizing
both models in their common function field leaves this nonfinite blowup unchanged.

The common-algebra condition is essential.  If one instead chooses unrelated generic
extensions at two levels, normality does **not** make the induced finite comparison flat.  Over
a field $k$ of characteristic different from two, with

$$
A=k[[u,v,w]]/(uv-w^2)\subset B=k[[s,t]],
\quad u=s^2, v=t^2, w=st,                                \tag{9.27}
$$

both complete surfaces are normal and $B/A$ is finite, but the anti-invariant summand is a
nonfree maximal Cohen--Macaulay $A$-module. Concretely, the generic rank is two whereas

$$
B/(u,v,w)B=k[[s,t]]/(s^2,st,t^2)
$$

has $k$-dimension three, so $B$ cannot be free, hence cannot be finite flat over the local ring
$A$. Normality, equidimensionality, and generic etaleness therefore cannot compare separately
chosen towers.  The actual construction avoids this defect by normalizing every fine object in
one common generic algebra; it does not infer flatness for an arbitrary map of normal models.

There is also an immediate annular consequence.  Once a point of the common normalization is
known to lie above a node on both sides of a fine leg, the lifted map is an isomorphism of its
completed local model.  Its annular expansion index is therefore one.  What normalization
alone does not decide is which completed points are node-to-node, which are routed to smooth
branch strata, or what their decomposition groups are.

The ray factor is completely controlled.  Let $R'/R$ be the integral extension cut out by the
local part of the global ray quotient, of ramification index $r$.  On a smooth chart its
ray-only normalization is the ordinary base change.  At a node it is

$$
R'[[x,y]]/(xy-u(\pi')^r).                                  \tag{9.28}
$$

This ring is a hypersurface, hence $S_2$, and is regular in codimension one; it is therefore
normal.  Thus the ray-only normalization is exactly base change by $R'/R$.  It is finite
locally free, both ray-only degeneracy maps remain finite locally free by base change, and
resolving (9.28) inserts the equivariant chain of Section 5.2.  This does not assert that
normalization of a principal algebra commutes with ramified tensor product: the combined
principal/ray normalization is the object already covered by Proposition 9.2, and it may not
be the raw base change of the principal normalization.  For the associated tautological
rank-one coefficient, Book 22, formula (3.11) gives

$$
R\Psi(\mathcal L\otimes A(\boldsymbol\chi_v))
\simeq R\Psi(\mathcal L)\otimes A(\boldsymbol\chi_v),       \tag{9.29}
$$

with diagonal full inertia action.  Hence the ray character preserves every pull, trace,
normalization, Hecke-routing, and adjunction map.  No unramifiedness of the character is being
asserted: it is geometrically constant because it is pulled back from the trait.  This
statement applies to an automorphic determinant system only after the effective global ray
datum identifies that system with this component/trait pullback.  Such an identification is
part of the global ray hypothesis; a nominal local determinant character does not prove it.

#### The Drinfeld tower and the unavoidable wild ledger

The principal factor can be sharpened before stating the remaining theorem.  This also gives a
test which any proposed proof must pass.  Complete at a local-local point of the good vertex and
factor off the deformation-etale spectator tensors.  This does not assert that every spectator
level cover is unramified; those factors must be restored in the actual common normalization.
Write

$$
A^{(0)}=\widehat{R^{\rm sh}}[[t]]
$$

for the universal deformation ring of the active one-dimensional height-two formal
$\mathcal O_{F_v}$-module $G$, with residue field $k_v$ of cardinality $q$.  The display
(4.4) has the following coefficient-level upgrade.  First linearize the Teichmuller action by
the Reynolds coordinate
$(q-1)^{-1}\sum_{a\in k_v^\times}a^{-1}[\widetilde a]_G(Z)$.  The usual strict-coordinate
recursion can then be performed equivariantly.  It removes every homogeneous degree which is
not a power of the residue characteristic: the intermediate binomial coefficients in degree
$n$ generate the unit ideal unless $n$ is such a power.  Commutation with the linear
Teichmuller action also removes $T^{p^r}$ unless $a^{p^r}=a$ for every $a\in k_v$,
equivalently unless $[k_v:\mathbf F_p]\mid r$.  Thus only powers of $q$ remain.  At degree
$q^r$, order the new unknowns as the strict-coordinate coefficient, the formal-law
coefficient, and the coefficient of $[\pi]_G$.  Linearizing
$[\pi]_G(F_G(S,T))=F_G([\pi]_G(S),[\pi]_G(T))$ modulo the maximal ideal gives a triangular
system: after the coboundary coordinate has been removed, every diagonal entry is a power of
the coefficient of $Z^{q^2}$ in the special $\pi$-series.  Height two makes that coefficient a
unit.  The degree-$q$ coefficient is the sole free deformation parameter; the display (4.4)
identifies it with $t$ up to a unit, and all later coefficients are forced inductively.  Thus
no division by $\pi$ occurs.  Weierstrass preparation then gives the required degree-$q^2$
divisor.
After absorbing units, this gives a compatible $q$-typical coordinate in which, as a divisor
of degree $q^2$ and modulo $\pi$, multiplication has the form

$$
[\pi]_G(Z)\equiv tZ^q+Z^{q^2}\pmod\pi                   \tag{9.29a}
$$

up to units in the two displayed coefficients.  The same recursion says that the coefficient
of $Z$ in the Weierstrass polynomial is $\pi$ times a unit, the coefficient of $Z^q$ is $t$
times a unit modulo $\pi$, and its specialization at $(\pi,t)$ is $Z^{q^2}$.  Those three
coefficient statements, rather than a chosen exact polynomial formula, are what will be used.

They suffice to prove the first Drinfeld normalization theorem rather than leave it as an
input.

**Proposition 9.3 $({\rm DLB}_1)$ (level-one Drinfeld-basis normalization).**  Let
$D_1$ be the complete local ring representing a full Drinfeld $\pi$-basis

$$
\varphi:k_v^2\longrightarrow G[\pi]
$$

at the point where all its geometric values coalesce.  Then $D_1$ is regular of dimension two,
finite flat over $A^{(0)}$, the two universal values

$$
X=\varphi(e_1),\qquad Y=\varphi(e_2)
$$

are a regular system of parameters, and the canonical generic map identifies $D_1$ with the
completed normalization of the good vertex in the generic principal $K_v(\pi)$-cover.

**Proof.**  The Drinfeld-basis functor is a closed subfunctor of $G[\pi]^2$, so its complete
local representing ring $D_1$ is finite over $A^{(0)}$.  Its generic fiber is the ordinary
full-basis cover and is nonempty.  At the closed height-two fiber every section of the formal
group is zero and the divisor is $q^2[0]$, so there is only one geometric Drinfeld-basis point.
The finite closure of every generic component therefore meets that point.  Hence its complete
local ring $D_1$ has Krull dimension two.  It is generated over $A^{(0)}$ by the universal
values $X,Y$.

In $D_1[[Z]]$ the divisor definition is the identity

$$
\operatorname{div}([\pi]_G(Z))
=\sum_{a\in k_v^2}[z_a],
\qquad
z_a=[\widetilde a_1]_G(X)+_G[\widetilde a_2]_G(Y).
$$

Set $X=Y=0$.  The right side becomes the length-$q^2$ divisor $q^2[0]$.  Comparing the
unique monic Weierstrass polynomials makes the left polynomial equal to $Z^{q^2}$; comparing
its linear coefficient gives $\pi=0$ in
$D_1/(X,Y)$.  After that, comparison of the $Z^q$ coefficient in (9.29a) gives $t=0$.
Conversely the zero homomorphism at $(\pi,t)$ is a Drinfeld basis because the special
height-two divisor is $q^2[0]$.  Therefore

$$
D_1/(X,Y)=\bar k.
$$

The maximal ideal of $D_1$ is generated by $X,Y$.  A noetherian local ring of dimension two
whose maximal ideal has two generators is regular.  Thus $D_1$ is a regular domain and $X,Y$
are a regular system of parameters.  Since it is finite over the regular ring $A^{(0)}$ of the
same dimension, the parameters of $A^{(0)}$ form a system of parameters in $D_1$;
Cohen--Macaulayness and Auslander--Buchsbaum make $D_1$ finite free over $A^{(0)}$.

Finally, after inverting $\pi$, a Drinfeld basis is an ordinary basis, so the generic algebra
is exactly the local generic principal $K_v(\pi)$-algebra.  The finite ring $D_1$ is normal.
It is therefore the integral closure of $A^{(0)}$ in that algebra, and completion gives the
claimed normalization. $\square$

For
$a=(a_1,a_2)\in k_v^2$ put

$$
z_a=[\widetilde a_1]_G(X)+_G[\widetilde a_2]_G(Y),
$$

where Teichmuller representatives are used.  The Drinfeld divisor identity and its derivative
at the zero section give, for units $u,u'$,

$$
\pi
=u\prod_{0\ne a\in k_v^2}z_a
=u'\prod_{L\in\mathbf P^1(k_v)}z_L^{q-1}.                \tag{9.29b}
$$

Here $z_L$ is any $z_a$ with $a$ spanning $L$; changing $a$ multiplies it by a unit.  Moreover

$$
z_a\equiv a_1X+a_2Y\pmod{(X,Y)^2}.                        \tag{9.29c}
$$

Consequently the reduced special fiber of $D_1$ has $q+1$ distinct smooth branches through
the closed point, indexed by $\mathbf P^1(k_v)$, and every branch occurs in the divisor of
$\pi$ with multiplicity $q-1$.  At $q=2$ it is a reduced three-branch crossing; for $q>2$ it
also has vertical multiplicities.  In particular the raw principal normalization is neither a
strict node nor smooth over the trait.  Book 22's strict-node complex cannot be applied to it
before taking the appropriate Stein factor and wild invariants.
The normalization of its reduced special fiber has conductor preimages
$c_L$, one on each branch.  The group $G_1$ below acts transitively on the set
$\{c_L\}_{L\in\mathbf P^1(k_v)}$, and the stabilizer of $c_L$ is the same line stabilizer as
the branch.  These $q+1$ tangent directions are exactly the $q+1$ oriented edges leaving the
vertex $[\Lambda_0]$ in the Bruhat--Tits tree; choosing $L$ chooses the adjacent Iwahori edge.
Blowing up the closed point separates the strict transforms, but the exceptional curve occurs
in the total transform of $\pi$ with multiplicity

$$
(q+1)(q-1)=q^2-1,
$$

while each strict transform still has multiplicity $q-1$.  Both integers are prime to the
residue characteristic, so a tame base change can repair these divisor multiplicities, but it
does not erase the wild unipotent deck action calculated below.  This is the precise
distinction between taming a normal-crossings divisor and declaring the principal cover tame.

The same equations determine the first decomposition ledger.  Put

$$
G_1=\operatorname{GL}_2(k_v).
$$

This is the active group before fixing a determinant/Weil-pairing component.  If the chosen
PEL component cuts it down, every group below is intersected with that effective subgroup and
the determinant orbit is retained in the already separated ray/component factor.  The
unipotent group $U_L$, and hence the wild calculation, is unchanged.

The closed Drinfeld point has decomposition group $G_1$.  The branch $z_L=0$ has decomposition
group the line stabilizer $B_L$.  For $L=k_ve_1$, write

$$
B_L=\left\{
\begin{pmatrix}a&b\\0&d\end{pmatrix}:a,d\in k_v^\times, b\in k_v
\right\},
\qquad
U_L=\left\{
\begin{pmatrix}1&b\\0&1\end{pmatrix}:b\in k_v
\right\}.                                                \tag{9.29d}
$$

On the reduced branch, $w=\varphi(e_2)$ satisfies
$w\mapsto[\widetilde d]_G(w)$.  Hence the inertia subgroup is the kernel of the quotient
character $B_L\to k_v^\times$, $\left(\begin{smallmatrix}a&b\\0&d\end{smallmatrix}\right)
\mapsto d$, its wild subgroup is exactly $U_L$, and its remaining inertia quotient has order
$q-1$.  The wild group fixes the reduced branch pointwise but is not trivial on the generic
principal cover.  Indeed, restricting (9.29a) to the generic point of that branch gives

$$
t=-u_Lw^{q(q-1)}                                           \tag{9.29e}
$$

in its residue function field, for a unit $u_L$.  The $q$-part is purely inseparable after
reduction.  Thus the fact that the visible vertical multiplicity in (9.29b) is $q-1$ does not
make the principal cover tame; the wild $U_L$-action is hidden by inseparable residue.

There is also an exact Stein-factor consequence.  Proposition 9.3, normality, and the generic
fixed-field description give

$$
D_1^{G_1}=A^{(0)},
\qquad
D_1^{B_L}=A_e=\widehat{R^{\rm sh}}[[x,y]]/(xy-\pi),       \tag{9.29f}
$$

where the second ring is the generic cyclic-line, or Iwahori, quotient belonging to $L$.
Indeed invariants in a normal finite algebra are the integral closure in the fixed field, and
the right sides are already normal.  Formula (9.29f) explains how a strict node can be a
stabilizer Stein factor of a wild many-branch principal normalization.
More explicitly, after absorbing units, its two parameters pull back as

$$
x\longmapsto\prod_{0\ne a\in L}z_a,
\qquad
y\longmapsto\prod_{a\notin L}z_a,
\qquad xy=\pi.
$$

The first divisor is the single branch $L$ with multiplicity $q-1$; the second is the union of
the other $q$ branches, each with that multiplicity.  Thus this is a quotient equation,
not an assertion that the full-level source itself has only two branches.

For the coefficient systems used later this ledger has a particularly clean consequence.  Let

$$
P=\mathcal O[\mathbf P^1(k_v)],
\qquad s_L=\sum_{M\ne L}e_M.
$$

The group $U_L$ fixes $e_L$ and acts regularly on the affine complement.  Since
$q=|U_L|$ is a unit in the coefficient DVR, wild invariants are exact and

$$
P^{U_L}=\mathcal Oe_L\oplus\mathcal Os_L,                 \tag{9.29g}
$$

$$
(P/\mathcal O\mathbf1)^{U_L}
=\mathcal O\,(e_L\bmod\mathbf1),
\qquad
(\ker\operatorname{aug})^{U_L}
=\mathcal O\,(e_L-q^{-1}s_L).                             \tag{9.29h}
$$

The two generators in (9.29h) pair to $1$.  The diagonal tame quotient fixes both lines.  Thus
the principal cover is wild, while the extreme quotient and augmentation **modules after
wild invariants** are geometrically unramified on the annulus.  Book 22, (3.12)--(3.14), rather
than a declaration that the cover is tame, is the correct passage to its procyclic complex.
For any common generic Galois refinement dominating $D_1$, the two representations are
inflated from $G_1$, so their intrinsic geometric annular monodromy still has wild image
$U_L$ and the deeper generic kernel acts trivially.  Hence the same invariant lines result
before the deeper branch geometry is known.  This does not identify the wild subgroup of a
selected higher special-fiber valuation or assert that its map onto $U_L$ is surjective; that
valuation-theoretic statement is part of $({\rm HDB}_v)$.
Any global ray character remains as the external diagonal inertia action of (9.29).

The finite flag routing itself is already visible in Sections 9.3--9.4.  Under the Bruhat
decomposition

$$
\operatorname{Res}^{G_1}_{B_L}P
\simeq\mathcal Oe_L\oplus\mathcal O[B_L/(B_L\cap sB_Ls^{-1})],
                                                                  \tag{9.29i}
$$

Put $T_L=B_L\cap sB_Ls^{-1}$.  The same fixed-field argument as in (9.29f) identifies
$D_1^{T_L}$ with the selected completed Stein factor of the normalized length-two PEL flag
closure of Section 9.3: its generic fiber is the moving $B_L/T_L$-cover, and both rings are
the integral closure in that field.  Thus the following incidence calculation is an actual
level-one Stein-factor calculation, rather than a count of characteristic-zero flags.

The fixed summand is the identity Iwahori sheet and is node-to-node with multiplicity and
expansion indices one.  The moving orbit is indexed by $a\in k_v$.
Equations (9.11)--(9.12) prove that $a=0$ has
completed ring $\widehat{R^{\rm sh}}[[x,y]]/(xy-\pi)$, both branch maps are the identity in
the ordered coordinates, and its scheme-theoretic multiplicity and both expansion indices are
one.  For every $a\ne0$ a coordinate is a unit, the completed source is smooth, and the sheet
belongs to the normalization-component term.  Hence the node-to-branch generization maps on
the $a=0$ strict-node sheet, restricted to either constant extreme line in (9.29h), are the two
identity maps in degree zero and zero in the independent vanishing degree.  The other
level-one geometric maps are the ordinary restrictions from their smooth branch sources.
This does not yet identify the full generization maps after a higher principal kernel or a
ramified spectator factor is restored.  The level-one routing is compatible with $U_v$ and
its transpose by (9.13)--(9.15), and with prime-to-$v$ Hecke routes because those isogenies
commute with the active Drinfeld basis.

The actual common principal algebra of (9.26) can lie deeper than this first layer.  A basis at
one vertex does not automatically give a basis on the quotient height-two group at the
adjacent vertex; a common Galois closure can require compatible higher Drinfeld division
points.  The following calculation both exhibits the depth jump and proves the active
higher-level normalization.  In the basis of (2.2), put

$$
K_0(1)=1+\pi M_2(\mathcal O_{F_v}),
\qquad
K_1(1)=
\begin{pmatrix}1&0\\0&\pi^{-1}\end{pmatrix}
K_0(1)
\begin{pmatrix}1&0\\0&\pi\end{pmatrix}.
$$

Then

$$
K_0(1)\cap K_1(1)=
\left\{
\begin{pmatrix}
1+\pi a&\pi^2b\\
\pi c&1+\pi d
\end{pmatrix}:a,b,c,d\in\mathcal O_{F_v}
\right\},                                                \tag{9.29j}
$$

and $K_0(2)=1+\pi^2M_2(\mathcal O_{F_v})$ is contained in this intersection.  Thus full
Drinfeld level $\pi^2$ at the first vertex dominates both level-one vertex covers, whereas
level $\pi$ at that vertex does not.  Taking the effective Galois core for the whole finite
diagram can force a still deeper but finite $K_0(n)$.  Formula (9.29j) is only the generic
subgroup calculation, but the same Drinfeld argument identifies the active integral closure.

For $n\ge1$, let $D_n$ be the complete local ring of a full Drinfeld $\pi^n$-basis at the
point where all basis values coalesce, and write $X_n,Y_n$ for the values on a chosen basis.
The functor is finite over $A^{(0)}$, and its generic fiber is the full $K_0(n)$-cover.  The
map to level one sends

$$
X\longmapsto[\pi^{n-1}]_G(X_n),
\qquad
Y\longmapsto[\pi^{n-1}]_G(Y_n).
$$

Consequently $\pi,t\in(X_n,Y_n)$ by Proposition 9.3.  Hence $D_n/(X_n,Y_n)=\bar k$, the
maximal ideal of the two-dimensional finite local ring $D_n$ is generated by $X_n,Y_n$, and
the argument of Proposition 9.3 proves

$$
D_n\text{ regular and finite free over }A^{(0)},
\qquad
D_n=\operatorname{Nor}_{\operatorname{Frac}D_n}(A^{(0)}).
                                                                  \tag{9.29k}
$$

This proves the compatible **active** Drinfeld normalization at every finite depth, not only
at depth one.  More generally, if an active principal generic factor $L$ is an intermediate
field in $\operatorname{Frac}D_n$ and $H$ is its fixing subgroup, then

$$
\operatorname{Nor}_{L}(A^{(0)})=D_n^H.                    \tag{9.29l}
$$

Indeed invariants of a normal domain under a finite group are normal and have the stated
fixed field.  Formula (9.29j) puts every finite collection of adjacent active principal
covers inside such a $D_n$, so (9.29l), together with Proposition 9.2, identifies their
common active vertex--edge normalization.  Moreover $D_n^H$ is finite free over $A^{(0)}$:
it is a two-dimensional normal local ring, hence Cohen--Macaulay, and the
Auslander--Buchsbaum argument of Proposition 9.3 applies.  No invertibility of $|H|$ is used
here.  Regularity is asserted for $D_n$, not for the quotient ring $D_n^H$, which can have
quotient singularities.

What (9.29k)--(9.29l) do not identify is the special-fiber valuation tree of $D_n^H$ above
the $q+1$ branches of $D_1$, its higher wild kernel decomposition groups and generization
maps, or a possibly ramified spectator/ray compositum.  Nor do they identify the strict
transforms used by a proper nonfinite flag leg with the corresponding invariant-ring strata.
The obstruction is visible in the equations, not merely in missing terminology.  If
$z_{a,n}=[\widetilde a_1]_G(X_n)+_G[\widetilde a_2]_G(Y_n)$ and
$z_{a,1}=[\pi^{n-1}]_G(z_{a,n})$, then on the closed height-two base

$$
z_{a,1}\equiv u_{a,n}z_{a,n}^{q^{2(n-1)}}\pmod{(\pi,t)}   \tag{9.29m}
$$

for a unit $u_{a,n}$.  Thus all higher valuations above a fixed level-one branch have the same
reduced tangent direction and coalesce with a large purely inseparable thickness.  Neither
the tangent cone nor the set of Bruhat--Tits neighbors can recover their decomposition groups
or say which strict transform a proper flag correspondence meets.
For the two coefficient representations which factor through $G_1$, however, the complete
level-one **node-annular and boundary-stabilizer** ledger can already be written without
resolving (9.29m).  Continue
with $L=k_ve_1$ and put

$$
I_L=\ker(B_L\xrightarrow{d}k_v^\times)
=U_L\rtimes A_L,
\qquad
A_L=\left\{\begin{pmatrix}a&0\\0&1\end{pmatrix}:a\in k_v^\times\right\}.
                                                                  \tag{9.29n}
$$

As in (9.29d), a determinant- or component-fixed problem replaces $I_L,A_L$ by their
intersections with the effective group; $U_L$ is unchanged, and a removed diagonal character
is retained in the external component/ray action.

After the residue-field quotient $d$ is removed, the connected geometric annular cover has
finite image $I_L$.  Let $\widetilde A_L$ be the procyclic tame annular group acting through
$A_L$, and let $\widetilde I_L$ be its extension by $U_L$; this notation avoids replacing a
pro-$\ell$ annular group by finite-group cohomology when $\ell\mid q-1$.  The closure meets the
branch $L$ at one endpoint with finite stabilizer $I_L$.  At the
other endpoint it meets the affine complement transitively; for $M=k_ve_2$ the stabilizer is
$A_L$, and $I_L/A_L$ is the set of its $q$ branches.  Therefore, for any finite-free
$G_1$-module $W$, the node complex and the two boundary stabilizers are

$$
K_L(W)=R\Gamma_{\rm cont}(\widetilde I_L,W)
       \simeq R\Gamma_{\rm cont}(\widetilde A_L,W^{U_L}),
\qquad (D_L,D_M)=(I_L,A_L).                               \tag{9.29o}
$$

The stabilizer restriction supplies the coefficient inclusion

$$
W^{U_L}\lhook\joinrel\longrightarrow W.                  \tag{9.29p}
$$

The node formula retains any $\ell$-part of $A_L$ in the procyclic complex; no averaging by
$q-1$ is being used.  Equations (9.29o)--(9.29p) do **not** identify the two conductor
complexes or promote the coefficient inclusion to a generization chain map.  Indeed, for the
trivial module the two conductor complexes in Book 22, (3.10), are the coefficient module in
degree zero, whereas replacing either of them by
$R\Gamma_{\rm cont}(\widetilde A_L,\mathcal O)$ would add a spurious degree-one class.  Thus
the annular group-cohomology formula belongs at the node only.  Residue Galois transports the
boundary-stabilizer calculation among the $q$ complementary branches.  A deeper active
principal kernel acts trivially on $W$, so the intrinsic node complex and boundary coefficient
modules are unchanged; a global ray character tensors them diagonally by (9.29).

The complementary summand is integral and explicit.  Let

$$
Q_L=\ker\!\left(
\operatorname{aug}:\mathcal O[\mathbf P^1(k_v)\setminus\{L\}]
\longrightarrow\mathcal O\right).
$$

Because $U_L$ acts regularly on the affine complement and $q$ is a unit in $\mathcal O$,
averaging over $U_L$ gives $A_L$-stable decompositions

$$
\operatorname{St}_v^+
=\mathcal O(e_L\bmod\mathbf1)\oplus Q_L,
\qquad
\operatorname{St}_v^-
=\mathcal O(e_L-q^{-1}s_L)\oplus Q_L,
\qquad Q_L^{U_L}=0.                                      \tag{9.29q}
$$

Thus the node complex for either row is exactly the constant extreme-line complex.  On that
constant line Book 22, (3.10), gives the conductor term in degree zero and generization equal
to the identity in degree zero and zero in the independent vanishing degree.  The summand
$Q_L$ has no node contribution and is routed to the moving normalization-component term, but
its full conductor complex is not $R\Gamma_{\rm cont}(\widetilde A_L,Q_L)$ merely from the
stabilizer calculation.  Determining that branch complex and its generization is part of
$({\rm HDB}_v)$.  This is the exact level-one wild/node ledger without calling the principal
cover tame or discarding the branch term.

There is one further exact higher-level factorization.  Put
$V_n=(\mathcal O_{F_v}/\pi^n)^2$ and let $V_n^{\rm prim}=V_n\setminus\pi V_n$.  For
$c\in V_n^{\rm prim}$ write $z_{c,n}=\varphi_n(c)$.  If $\bar c\ne0$ is its reduction, the
Drinfeld divisor for $[\pi^{n-1}]_G$ evaluated at $z_{c,n}$ gives

$$
z_{\bar c,1}
=u_c\prod_{b\in\pi V_n}z_{c-b,n}.
$$

Multiplying over $0\ne\bar c\in k_v^2$ and using (9.29b) yields

$$
\pi
=u_n\prod_{c\in V_n^{\rm prim}}z_{c,n}
=u_n'\prod_{\lambda\in\mathbf P^1(\mathcal O_{F_v}/\pi^n)}
 z_{\lambda,n}^{q^{n-1}(q-1)}.                           \tag{9.29r}
$$

Each $z_{c,n}$ has nonzero linear term
$\bar c_1X_n+\bar c_2Y_n$, hence is a regular parameter and cuts a smooth prime divisor;
unit multiples of $c$ give associate parameters.  The converse follows at the generic point
of $(z_{c,n})$.  There $\pi=0$ but $t\ne0$: if $t$ also lay in this height-one prime, finiteness
over $A^{(0)}$ would make the one-dimensional quotient finite over the zero-dimensional ring
$A^{(0)}/(\pi,t)$, a contradiction.  Thus the formal module has height one.  Over an algebraic
closure its $\pi^n$-torsion has $q^n$ geometric points, each with connected multiplicity
$q^n$.  The Drinfeld divisor identity makes $V_n$ surject onto those points, so its kernel has
order $q^n$.  Since it contains the primitive vector $c$, that kernel is exactly the free line
$(\mathcal O_{F_v}/\pi^n)c$.  Hence a second primitive $d$ vanishes generically on this divisor
if and only if $d=uc$ for a unit $u$.

Consequently the reduced special fiber of $D_n$ has exactly

$$
\#\mathbf P^1(\mathcal O_{F_v}/\pi^n)=q^{n-1}(q+1)
$$

smooth branches, each of Cartier multiplicity $q^{n-1}(q-1)$.  The group
$G_n=\operatorname{GL}_2(\mathcal O_{F_v}/\pi^n)$ acts transitively, and the decomposition
group of the branch $\lambda$ is its line stabilizer $B_{n,\lambda}$.  For
$\lambda=(\mathcal O_{F_v}/\pi^n)e_1$, put $R_n=\mathcal O_{F_v}/\pi^n$.  At the branch
generic point, $w=Y_n$ is a primitive point of the height-one $\pi^n$-torsion and

$$
B_{n,\lambda}
=\left\{\begin{pmatrix}a&b\\0&d\end{pmatrix}:a,d\in R_n^\times, b\in R_n\right\},
\qquad w\longmapsto[d]_G(w).
$$

Since $X_n,Y_n$ are parameters, the normalized reduced branch has complete local ring
$\bar k[[w]]$.  Thus its residue function field is generated by $w$ over the fixed base
field.  The action on the cyclic group generated by $w$ is faithful because $w$ has exact
$\pi^n$-order.  Hence the raw branch inertia and its wild subgroup are

$$
I_{n,\lambda}=\ker(d)
=\left\{\begin{pmatrix}a&b\\0&1\end{pmatrix}:a\in R_n^\times, b\in R_n\right\},
\quad
P_{n,\lambda}
=\left\{\begin{pmatrix}a&b\\0&1\end{pmatrix}:a\in1+\pi R_n, b\in R_n\right\},
\quad
I_{n,\lambda}/P_{n,\lambda}\simeq k_v^\times.             \tag{9.29s}
$$

Thus $|P_{n,\lambda}|=q^{2n-1}$, and reduction maps it onto the level-one $U_L$.  For $n>1$
even the visible Cartier multiplicity $q^{n-1}(q-1)$ has a wild $q^{n-1}$-part.  Distinct
lifts of one level-one line have the same tangent, exactly as (9.29m) predicts.

The inseparable part of this ledger is also numerical, not conjectural.  Let $\kappa_\lambda$
be the residue function field of the branch.  The full generic cover has degree

$$
|G_n|=q^{4n-3}(q-1)^2(q+1).
$$

There are $q^{n-1}(q+1)$ branches, all with ramification index
$q^{n-1}(q-1)$.  The rank-specialization formula for the finite-free
$A^{(0)}$-algebra $D_n$, followed by the decomposition--inertia exact sequence after
henselizing the height-one base valuation, therefore gives

$$
\begin{aligned}
e_\lambda&=q^{n-1}(q-1),\\
[\kappa_\lambda:\bar k((t))]&=q^{2n-1}(q-1),\\
[\kappa_\lambda:\bar k((t))]_{\rm sep}
 &=|B_{n,\lambda}/I_{n,\lambda}|=q^{n-1}(q-1),\\
[\kappa_\lambda:\bar k((t))]_{\rm insep}&=q^n.
\end{aligned}                                             \tag{9.29t}
$$

Thus $|I_{n,\lambda}|=e_\lambda
[\kappa_\lambda:\bar k((t))]_{\rm insep}$: the subgroup with
$a\in1+\pi R_n$ supplies the wild part of the normal ramification, while the additive
$b$-subgroup is visible in the inseparable residue thickness.  In particular

$$
[\kappa_\lambda^{B_{n,\lambda}}:\bar k((t))]=q^n
$$

is purely inseparable.  Already at $n=1$, normalization of a reduced branch followed by
$B_L$-invariants is therefore a purely inseparable degree-$q$ extension of the reduced branch
of $D_1^{G_1}=A^{(0)}$.  This is an explicit counterexample to commuting wild invariants with
reduction and branch normalization; it is why the invariant surface ring alone does not give
the downstairs conductor ledger.

There is nevertheless a complete raw higher **node-annular and boundary-stabilizer ledger**
over the strict Iwahori Stein factor.  Let $\rho_n:G_n\to G_1$ be reduction and put

$$
\widehat B_{n,L}=\rho_n^{-1}(B_L).
$$

The fixed-field calculation gives

$$
D_n^{\ker\rho_n}=D_1,
\qquad D_n^{\widehat B_{n,L}}=D_1^{B_L}=A_e.              \tag{9.29u}
$$

Fix the branch $\lambda=R_ne_1$ over the $L$-endpoint and a geometric residue embedding there.
The connected geometric annular image is then $I_{n,\lambda}$.  At the opposite endpoint its
branches are the $q^n$ lines $R_n(r,1)$, $r\in R_n$; the affine action
$r\mapsto ar+b$ is transitive.  The stabilizer of $R_ne_2$ and its wild subgroup are

$$
A_{n,\lambda}=\left\{\begin{pmatrix}a&0\\0&1\end{pmatrix}:a\in R_n^\times\right\},
\qquad
A^1_{n,\lambda}=\left\{\begin{pmatrix}a&0\\0&1\end{pmatrix}:a\in1+\pi R_n\right\}.
                                                               \tag{9.29v}
$$

Both $P_{n,\lambda}$ and $A^1_{n,\lambda}$ are $p$-groups, and

$$
I_{n,\lambda}/P_{n,\lambda}\simeq
A_{n,\lambda}/A^1_{n,\lambda}\simeq k_v^\times.
$$

Let $\widetilde C_n$ denote the tame procyclic annular group acting through this common finite
quotient.  For every finite-free $G_n$-module $W$, Book 22, (3.12)--(3.14), gives the node
complex, while the stabilizer calculation gives the two boundary coefficient modules

$$
\begin{aligned}
K_{n,\lambda}(W)
 &\simeq R\Gamma_{\rm cont}(\widetilde C_n,W^{P_{n,\lambda}}),\\
M_{n,\lambda}(W)&=W^{P_{n,\lambda}},
\qquad M_{n,\mu}(W)=W^{A^1_{n,\lambda}},
\qquad \mu=R_ne_2.
\end{aligned}                                             \tag{9.29w}
$$

The boundary stabilizer inclusion is

$$
W^{P_{n,\lambda}}\lhook\joinrel\longrightarrow
W^{A^1_{n,\lambda}},                                     \tag{9.29x}
$$

and residue Galois transports it among the $q^n$ moving branches.  No averaging by $q-1$ is
implicit in the node formula: its $\ell$-part remains in the procyclic complex.  Just as at
level one, (9.29w)--(9.29x) do not identify either full conductor complex or the generization
chain maps; the trivial-module test above forbids replacing those conductor terms by a second
copy of the procyclic node complex.  If $W$ is inflated from $G_1$, then
$P_{n,\lambda}$ has image $U_L$ and $A^1_{n,\lambda}$ acts trivially, so (9.29w)--(9.29x)
recover (9.29o)--(9.29p) at the level of the node complex and boundary modules.  This proves
that the deeper active kernel does not change that intrinsic node ledger for the two
level-one Steinberg rows, while retaining the full wild stabilizer ledger for a genuine
depth-$n$ coefficient.

For an intermediate active ring $D_n^H$, its height-one branches are the $H$-orbits on
$\mathbf P^1(R_n)$.  For a representative $\lambda$, the decomposition group of
$D_n/D_n^H$ is $H_\lambda=H\cap B_{n,\lambda}$; the raw decomposition group over
$A^{(0)}$ remains $B_{n,\lambda}$.  If $H$ is normal, the decomposition group in the quotient
$G_n/H$ is the image of the stabilizer of the $H$-orbit.  These statements determine the
branch set and all raw active stabilizers, but the strict containment exhibited after
(9.29t) shows that they do not determine the reduced residue field after wild descent, its
downstairs Cartier multiplicity, or the full complex carried by a proper component-routed
source.

The proper routing itself can nevertheless be completed for the retained residue-prime
correspondence.

**Proposition 9.4 (node routing on the actual common factor).**  Normalize the length-two flag
closure of Section 9.3 in the same actual common principal/ray algebra as its two targets.  Over
the inverse image of a fine node, its unique node-to-node strict transform is the $a=0$ sheet
of (9.11)--(9.12).  On every selected common-normalization factor both legs of that sheet are
isomorphisms of completed rings.  Its scheme-theoretic correspondence multiplicity and both
expansion indices are one.  Every $a\ne0$ sheet, and every contracted vertical flag stratum,
is routed to the normalization-component term.  This routing commutes with residue Frobenius,
$U_v$, $U_v^t$, and every retained prime-to-$v$ Hecke route.

**Proof.**  Section 9.4 computes the whole fine fiber.  At $a=0$ both projections have
completed strict-node ring $xy=\pi$, are quasi-finite, and have local length one.  At each
$a\ne0$ point a coordinate is a unit, the source is smooth, at least one image lies in a
smooth branch stratum, and the same eliminated-variable calculation makes the noncontracted
projection germs quasi-finite of local length one.  Any positive-dimensional special flag
fiber has both images in smooth strata.  Hence the non-quasi-finite locus of either proper
projection has closed image disjoint from the relevant target nodes.  After deleting those
closed images, both projections are proper and quasi-finite, hence finite.

On these finite neighborhoods, the proof of Proposition 9.2 applies verbatim: source and
target have been normalized in the same generic algebra, and integrality over either of two
finite integral base rings is equivalent.  Thus the selected completed normalization rings
are canonically identical along each leg.  In particular no point above an $a\ne0$ or
contracted fine stratum can become node-to-node, while the $a=0$ generic sheet remains reduced
of multiplicity one and its two lifted maps are isomorphisms.  Expansion one follows from the
completed-ring identity.  Generic equivariance and uniqueness of normalization give the deck,
residue-Galois, Hecke, and transpose compatibilities. $\square$

Proposition 9.4 determines the proper strict-transform **routing** and coefficient one.  It
does not calculate the reduced branch field or the full nearby-cycle complex carried by a
component-routed common-normalization source; those are precisely where wild reduction can
fail to commute with invariants.

**First remaining local input $({\rm HDB}_v)$ (higher Drinfeld branch-complex descent).**  For the
selected $n,H$ in (9.29l), a selected $H$-orbit of raw branches, and the actual normalized
spectator/ray compositum, identify the reduced residue subfield inside the corresponding raw
fixed field, its Cartier multiplicity, and the resulting decomposition and inertia sequence.
Equivalently, calculate exactly the failure of wild invariants to commute with reduction which
is measured in the full-level case by the purely inseparable factor in (9.29t).  Starting from
the node complex and boundary modules in (9.29w)--(9.29x), construct the raw conductor
complexes and generization chain maps, and then descend them through the selected intermediate
and spectator/ray normalization.  On a regular domination of
the proper residue-prime legs, identify the full complexes on the component-routed sources and
their proper pushforward and transpose maps; Proposition 9.4 has already fixed the strict
transform routing and all node-to-node multiplicities.  Normality, (9.29r), and the projective-line orbit
calculation determine the finite rings and branches; (9.29s)--(9.29x) determine the raw active
stabilizers, residue degrees, node-annular complexes, and boundary coefficient maps.  They do
not determine the branch complexes or generization chain maps, even before intermediate or
spectator descent; the strict wild invariant/reduction discrepancy after (9.29t), amplified by
(9.29m), is the first additional obstruction.

It remains to identify the principal factor at a node.  The remaining statement is now a local
algebraic-geometric theorem, not an unspecified nearby-cycle formalism.

**Required local theorem $({\rm PNS}_v)$ (principal node and stabilizer theorem).** Let

$$
A_e=\widehat{R^{\rm sh}}[[x,y]]/(xy-\pi)
$$

be the completed edge ring at a local-local PEL point, let $A_0,A_1$ be the completed smooth
vertex rings at its two images, and choose a finite decomposition orbit $\widetilde x$ in the
common normalization above that edge point.  Let $B_e$ be completion along $\widetilde x$ and
let $B_0,B_1$ be completion of the same finite set in the two isomorphic lifted top objects.
Then $B_e\simeq B_0\simeq B_1$.  These are selected semilocal factors; $B_i$ is not the
completion along every point over the vertex image.  The required assertions are:

1. the normalization branches, conductor points, decomposition and inertia groups of $B_e$ are
   the vertex, edge, and oriented-flag stabilizers inside the effective Galois closure of the
   actual principal quotients.  For each node-to-node **stabilizer-quotient** tube, the actual
   wild subgroup is identified and its geometric quotient is an admissible tame annulus over
   the strict base annulus; this includes the homomorphism from the oriented
   tame annular group and its actions on the two ordered
   endpoints.  It also records the wild annular inertia: on each node-to-node coefficient
   module it first takes the exact wild invariants of Book 22, (3.12)--(3.14), and proves that
   the resulting module is the routed extreme line before the tame procyclic complex is used;
   every non-wild-invariant coefficient summand which does not survive on that extreme line
   must instead be carried, with its full decomposition action and without a smoothness or
   tameness assertion, by its actual completed branch source in the normalization-component
   term of clause 2.  Proper nearby-cycle pushforward from a regular domination then supplies
   its full branch complex.  The resulting node-to-branch generization chain maps are
   identified; no branch with uncomputed monodromy is replaced by an underived module;
2. for each oriented flag incidence contributing to an extreme residue, exactly one
   stabilizer-quotient sheet, of scheme-theoretic multiplicity one, is node-to-node.  Every
   other generic flag sheet is assigned, with its scheme-theoretic multiplicity and
   decomposition action, to the stated normalization-component stratum. This routing is
   compatible with every retained residue-prime Hecke leg treated by the graph/regular-
   domination construction of Section 9.3, including its transpose. On the identified
   node-to-node sheets lying over the finite parahoric base legs, Proposition 9.2 then proves,
   rather than assumes, expansion index one.

Proposition 9.4 proves the sheet classification, common-factor routing, multiplicity one,
expansion one, and retained Hecke/transpose compatibility in clause 2.  What clause 2 still
imports from clause 1 is the full decomposition action and nearby-cycle complex on each
component-routed source after wild intermediate/spectator descent.

This is an exact finite-level theorem.  It can equivalently be proved by constructing the full
Drinfeld level structure on the active height-two $\pi$-divisible group, taking the Stein
factors of the length-one and length-two PEL flag schemes, and calculating their complete local
rings from the universal display (4.4).  The equality with the normalization in (9.26), not
mere equality of characteristic-zero points, is part of the assertion.

It is enough to prove the displayed algebra after completed strict henselization.  All modules
in question are finite, completion is faithfully flat, and equality of two finite subalgebras
together with the decomposition action is reflected by that completion.  This is completion of
the already constructed proper normalization, where Book 58 applies.  It is not an invocation of formal
GAGA to manufacture an algebraic tower from one isolated formal node.  If one instead starts
from an abstract Drinfeld formal moduli space, algebraizing it requires the compatible proper
polarized global datum of Book 58; a complete local equation alone does not supply that datum.

Once $({\rm PNS}_v)$ is known, no further ramified nearby-cycle theorem is missing.  For a
finite-free representation $W$ of the principal quotient, the decomposition group in clause 1
first gives its actual wild subgroup $P_x$.  Take the exact invariants $W^{P_x}$ of Book 22,
(3.12)--(3.13); this is not a claim that the cover is tame.  Let $H_x$ be the prime-to-$\ell$
kernel in the remaining tame group, put $M_x=(W^{P_x})^{H_x}$, and write $T_x$ for the
remaining pro-$\ell$ generator.  Book 22, (3.14), then gives the
full complex

$$
[M_x\xrightarrow{T_x-1}M_x]                               \tag{9.30}
$$

with the residue-Galois action (3.6).  Combining it with the branch complexes and
generization maps gives the normalization--conductor homotopy fiber (3.10).  Clause 2 and
(3.8) make both unsigned extreme expansion coefficients equal to $1$; the only signs are those
from the chosen oriented endpoint difference. They place all remaining sheets in the middle
normalization term. The same formulas make
finite-flat trace adjoint to pull on the contragredient representation and commute with every
retained Hecke route.  Proposition 9.3 proves the level-one ring assertion $({\rm DLB}_1)$.
Equations (9.29k)--(9.29l) also prove the active normalization and intermediate invariant rings
at every finite depth, while (9.29r)--(9.29x) prove the full-level higher branch, inertia,
residue-degree, node-annular, and boundary-stabilizer ledger.  Thus the first unresolved part
of $({\rm PNS}_v)$ in proof order is $({\rm HDB}_v)$: construction of the raw branch conductor
complexes and generization maps, their descent through the selected wild intermediate and
spectator/ray compositum, and the strict transforms for the proper residue-prime legs.
Equations (9.29b)--(9.29i) and (9.29n)--(9.29q) prove the level-one stabilizer, wild-invariant,
multiplicity-one, and constant-line generization consequences on the level-one Stein factor;
Proposition 9.4 promotes the residue-prime routing, coefficient one, expansion one, and
transpose compatibility to the actual common factor.  In particular, the
principal cover is genuinely wild even though its selected extreme invariant lines are tame.

## 10. The semistable curve theorem

### 10.1 Statement

**Theorem 10.1 (semistable models, monodromy, and bad Eichler--Shimura).** Fix
the direct quaternion-trace PEL curve of Book 119, a decomposition-stable canonical
component union, and neat prime-to-$p$ level. Choose either the completely split odd
place or the dyadically tensor-split place of Section 1.3, and impose the oriented
one-step Iwahori chain (2.3). Then:

1. the exact parahoric PEL functor is represented by a projective flat model carrying its universal isogeny, and its framed local model is scheme-theoretically the incidence scheme (3.1), with no extra vertical component;
2. the integral curve is regular and strictly semistable with completed node chart (4.1);
3. its two global branches descend over $k$ and are normalized by
   $X_{F,0}=X_0$ and $X_{V,0}=X_0^{(p)}$, constructed from the actual
   relative-Frobenius and inverse-twist Verschiebung kernels; their conductor is the
   reduced finite etale Hasse scheme $Z_0$, and the conductor square and signed node
   complex are (4.9b)--(4.9g);
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

9. every prime-to-$p$ Hecke correspondence on the full component union, or on a smaller union it preserves, preserves the $F/V$ kernels, Hasse set, graph pairing, nearby cycles, Frobenius, and $N$;
10. the actual unnormalized residue-prime correspondence
    $U_v=(\pi_h)_*r_h^*$ extends properly, has generic degree $q$, and acts on
    oriented graph edges by $[z]\mapsto[\Phi z]$; its graph restriction satisfies
    $U_v^2=S_v$ and $U_v^t=S_v^{-1}U_v$;
11. the two bad-prime degeneracy routes restrict as identity/Frobenius and
    Frobenius/identity on the branch normalizations, after the required dual-chain
    identification;
12. for a characteristic-zero multiplicity-one packet in the curve range with
    $\Pi_v=\operatorname{St}\otimes\mu_v$, the normalization-component packet term is
    zero, both graph multiplicities are one, $N$ has rank one, and geometric Frobenius
    on the invariant graph line is the automorphic new-line scalar
    $u_v=\mu_v(\Phi)$ in the raw unnormalized, uncentered weight-two convention; the
    centered Book 76 kernel root is $q^{-1/2}u_v$; and
13. normalization of the fine vertex--edge diagram in one supplied compatible common finite
    generic principal/ray algebra is finite locally free over each fine object, and every
    retained generic leg whose fine integral base leg is finite extends uniquely. Along such a
    fine finite leg the common
    normalizations are canonically identical.  The ray-only axis and its geometrically constant
    coefficient are explicit.  Proposition 9.3 proves the level-one Drinfeld-basis
    normalization $({\rm DLB}_1)$; (9.29k)--(9.29l) identify every active finite-depth
    normalization and intermediate ring; (9.29r)--(9.29x) compute the raw higher branches,
    inertia, inseparable residue degree, node-annular complexes, and boundary stabilizers; and equations (9.29b)--(9.29i) and
    (9.29n)--(9.29q) force the level-one branch stabilizers, exact
    wild invariants of the two Steinberg rows, unique multiplicity-one flag sheet,
    and constant-line generization maps.  Proposition 9.4 promotes the flag routing,
    multiplicity and expansion one, and residue-prime Hecke/transpose route to the actual
    common factor.  What remains in
    $({\rm PNS}_v)$ begins with $({\rm HDB}_v)$: construction of the raw conductor complexes
    and generization maps, wild branch descent through the selected intermediate and
    spectator/ray compositum, and the full proper pushforward on the component-routed sources.

**Proof.** The dyadic vertex construction, Proposition 2.1, Theorem 2.2, and
Proposition 2.3 prove projective representability and transfer the exact integral local
model over arbitrary test rings. Proposition 3.1 and Theorem 4.1 prove statements 1--2,
including the chart $xy=2$ in the dyadic case. Lemma 4.2, the reassembled subgroup
construction, and Theorem 4.3 prove statement 3. Sections 4.4 and 7.1--7.2 prove
statement 4. Chapter 5 proves statement 5. The graph nearby-cycle calculation in
Chapter 6 proves statement 6. Chapter 8 proves statements 7--8. Naturality of
prime-to-$p$ isogenies and functoriality of nearby cycles prove statement 9.
Sections 9.3--9.4 prove statement 10, Section 9.2 proves statement 11, and
Theorem 9.1 proves statement 12.  Proposition 9.2 and the calculation following it prove
statement 13 and its stated boundary. $\square$

### 10.2 Scope and failure modes

The theorem is deliberately restricted to the direct datum at a completely split odd
prime or at a place satisfying every item of the dyadically tensor-split ledger, and to
the one-step rank-two Iwahori. Mere rational splitting at two is insufficient: a ramified
order or involution, a nonunimodular form, or orientation data that do not extend finite
etale fall outside the proof. Deeper chains, non-minuscule local models, and wild
singularities require different equations. A determinant condition by itself is not
enough: Proposition 2.1 works over nilpotent rings and is what excludes a hidden vertical
component.

At odd places projectivity uses the distinguished good vertex at exactly the strength
proved in Book 121. At two it instead uses the independently constructed dyadic vertex
of Section 2.1; from Book 121 it imports only the characteristic-independent toric and
auxiliary-level trait arguments. The neighboring lattice vertex has its chain
polarization type and is not a second hyperspecial model. Dropping that distinction
invalidates both the Hilbert-scheme construction and the degeneracy routes.

At coarse level, fixed points can create quotient singularities. Nearby cycles are then computed equivariantly on a fine cover or stack. After nonsplit descent, branch exchange acts with a sign on oriented edges. A lisse coefficient system satisfies (6.10); a sheaf ramified along the special fiber does not.

Objectwise finite local freeness alone would not prove flatness of a comparison between
separately chosen normalizations.  Proposition 9.2 proves it for the actual diagram by the
stronger common-algebra argument: the lifted legs are isomorphisms.  That argument still says
nothing by itself about the completed Drinfeld strata.  Proposition 9.3 and
(9.29k)--(9.29l) identify the active normalization rings, while (9.29b)--(9.29e) show that the
level-one principal cover is wild and has a many-branch special fiber; only its exact
$U_L$-invariants give the two tame extreme lines in (9.29h), and (9.29n)--(9.29q) retain the
moving branch stabilizer and coefficient module without replacing its full complex by a
second node complex.  Equations (9.29r)--(9.29x) further compute the raw higher branch,
inertia, residue-degree, node-annular, and boundary-stabilizer ledger.  Constructing the raw
conductor/generization complexes, descending them through the wild intermediate and
spectator/ray normalization, and calculating the full proper nearby-cycle pushforward on
every component-routed source still requires $({\rm HDB}_v)$;
Proposition 9.4 already fixes the actual common-factor strict-transform routing and node
multiplicities.  The ray projection formula applies only to the component/trait-pulled coefficient
identified by an effective global ray datum.

The equality $\operatorname{rank}N=b_1(\Gamma)$ is rational. Integral cokernels use the thickness matrix and saturation of the chosen lattice. A rational Hecke projector with an $\ell$-denominator does not select a canonical integral lattice. The packet theorem is likewise in characteristic zero and concerns the raw curve carrier; it is not an integral Ihara statement and is not a raw-to-global theorem. The geometric degeneracy complex remains input to any Ihara lemma or level-raising theorem, not a proof of either.

### 10.3 Conclusion

The direct quaternionic bad-prime problem reduces integrally to one incidence of two
lines. Under the exact dyadic tensor ledger that incidence is still valid over every
nilpotent test ring and produces the regular node $xy=2$. Relative Frobenius and
inverse-twist Verschiebung identify the two descended global branches, while the Hasse
section identifies every conductor point and its multiplicity. The resulting signed graph
is therefore an arithmetic object, not an unlabeled combinatorial approximation.

Nearby cycles turn graph cycles into the length-two monodromy blocks. Their number is the
split conductor, their weighted Gram matrix controls the component group, and Frobenius
together with finite descent determines the full local type. The residue-prime
correspondence has degree two but one node-to-node sheet; on the Steinberg packet this is
the exact identity between geometric Frobenius and the automorphic $U_v$ new-line
scalar. These are the semistable model, component, monodromy, conductor, type, and
bad-prime Eichler--Shimura data needed by the quaternionic FLT blueprint.
