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
  - [10.3 The non-common-norm dyadic source](#103-the-non-common-norm-dyadic-source)
  - [10.4 The exact comparison boundary](#104-the-exact-comparison-boundary)
  - [10.5 Conditional transfer to the raw carrier](#105-conditional-transfer-to-the-raw-carrier)
  - [10.6 Conclusion](#106-conclusion)

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

Chapters 2--9 and Theorem 10.1 concern the direct quaternion-trace realization $D=V=B$ of Book 119, with $B/F$ division and split at exactly one real place. Fix its selected canonical component union and a neat prime-to-$p$ level. Section 10.3 separately constructs the split dyadic parahoric source for the unitary common-multiplier realization of Book 118. The two realizations are not identified.

This is a conditional input, not an existence theorem in the mixed one-split range. Book 119's
direct trace similitude group is the common-norm group, and Book 118, Proposition 8.2 proves
that when $[F:\mathbf Q]>1$ the one-split adjoint Hodge map cannot lift to it: its reduced-norm
exponent is odd at the active real factor and even at every compact factor. Thus the local-model
and monodromy theorem below remains valid for any supplied datum satisfying its ledger, but it
does not itself produce the raw SP carrier needed in the FLT application. The unitary
construction of Section 10.3 supplies a different exact PEL parahoric curve, but using it as
that raw carrier still requires the integral finite comparison isolated in Section 10.4.
Neither its components nor its raw packet plane are identified with those of the basic curve
merely because the adjoint groups agree.

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

Book 6 supplies the finite local--global character theorem and the ray-class/unit
compatibility used for the strict scalar quotient below. Books 10--12 supply effective finite
descent, normalization, blowups, and regular models; Book 13 supplies the divisor definition of
a bad-characteristic Drinfeld basis; Book 16 supplies graph/component-group algebra. Book 17
supplies the finite-etale common refinement and effective Galois closure on the generic
diagram. Book 20 supplies proper lci orientations, duality counits,
deformation-to-the-normal-cone excess classes, and transpose adjunction. Book 22 supplies the
strict-semistable nearby-cycle and weight complexes, including the tame strict-node complex and
exact reduction by a finite wild image. Book 37 supplies the Frobenius--Verschiebung formalism,
purity, and duality used to identify global strata. Book 35 supplies quotients by finite
locally free subgroups and descended polarizations. Book 58 supplies faithful flatness and
exactness of completion and the distinction between completing a known proper model and
algebraizing an abstract formal space. Book 70 supplies the maximal-Cohen--Macaulay freeness
criterion over a regular local ring and the warning that it fails over a singular target. Book
76 supplies the selected special Weil--Deligne normalization used to compare the Iwahori
scalar with geometric Frobenius. Book 118 supplies the exact common-norm Hodge-lift obstruction,
the unitary common-multiplier PEL datum, and its odd-prime finite component cover. Book 119
supplies the exact direct and unitary rational PEL functors, their good-base fine
representability, and their generic parahoric data; it does not supply the dyadic integral
unitary model constructed in Section 10.3. Book 120 supplies canonical
reciprocity on the abelianized component label; applied to reduced norm/determinant, it
identifies the global ray character's automorphic determinant line with the corresponding
trait-pulled Galois line. Book 121 supplies the
projective good vertex at odd places, its integral filtration-lifting theorem, universal
family, the split odd unitary good model, and, at two, the characteristic-independent toric
obstruction and flat-closure properness argument once an exact integral functor has been
constructed.

The exact dependency row is

$$
\boxed{122\mid 6,10,11,12,13,16,17,20,22,35,37,58,70,76,118,119,120,121}. \tag{1.6}
$$

There are eighteen direct dependencies. The right-double-coset, transpose, central, and degree conventions are chosen to agree with Book 124 and are rederived in Section 9.3 for the residue-prime span. The packet theorem is a characteristic-zero statement conditional only on the already isolated curve packet described in its hypotheses; it imports no Ihara saturation, level-raising theorem, deformation theorem, or modularity-lifting theorem.

The downstream comparison ledger is as follows. Book 124 deliberately leaves a
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
part of the general global ray hypothesis; Proposition 9.9 verifies it for the strict actual
choice by Book 120's canonical reciprocity.  A nominal local determinant character does not
prove it.

#### The Drinfeld tower and the unavoidable wild ledger

The principal factor can be sharpened before stating the full theorem.  This also gives a
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
before the deeper branch geometry is known.  This does not yet identify the wild subgroup of a
selected higher special-fiber valuation or assert that its map onto $U_L$ is surjective; the
raw valuation-theoretic calculation is supplied by Proposition 9.5 below, while the arithmetic
compositum and conductor maps remain in the ledger following that proposition.
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
stabilizer calculation.  Determining that branch complex and its generization is part of the
remaining Kummer branch ledger below.  This is the exact level-one wild/node ledger without
calling the principal
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
level one, (9.29w)--(9.29x) by themselves do not identify either full conductor complex or the
generization chain maps; the trivial-module test above forbids replacing those conductor terms
by a second copy of the procyclic node complex.  Those endpoint complexes remain in the
general $({\rm HDB}_v)_{\rm gen}$.  If $W$ is inflated from $G_1$, then
$P_{n,\lambda}$ has image $U_L$ and $A^1_{n,\lambda}$ acts trivially, so (9.29w)--(9.29x)
recover (9.29o)--(9.29p) at the level of the node complex and boundary modules.  This proves
that the deeper active kernel does not change that intrinsic node ledger for the two
level-one Steinberg rows, while retaining the full wild stabilizer ledger for a genuine
depth-$n$ coefficient.

For an intermediate active ring $D_n^H$, its height-one branches are the $H$-orbits on
$\mathbf P^1(R_n)$.  For a representative $\lambda$, the decomposition group of
$D_n/D_n^H$ is $H_\lambda=H\cap B_{n,\lambda}$; the raw decomposition group over
$A^{(0)}$ remains $B_{n,\lambda}$.  If $H$ is normal, the decomposition group in the quotient
$G_n/H$ is the image of the stabilizer of the $H$-orbit.  The invariant-ring calculation in
Proposition 9.5 below determines the reduced residue field and Cartier multiplicity; in
particular it keeps, rather than suppresses, the strict wild invariant--reduction discrepancy
exhibited after (9.29t).

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
does not by itself calculate the reduced branch field or the full nearby-cycle complex carried
by a component-routed common-normalization source.  The next proposition supplies the part
which follows from the Drinfeld invariant rings: the reduced active branch, its Cartier
multiplicity and groups, and the exact local reduction of a normalized compositum to a Kummer
factorization.  It does **not** calculate the Kummer unit classes or the resulting branch
complexes.

For $\lambda=R_ne_1$, write

$$
a,d:B_{n,\lambda}\longrightarrow R_n^\times,\qquad
\begin{pmatrix}a&b\\0&d\end{pmatrix}\longmapsto a,d,
$$

and put

$$
U_{n,\lambda}=\ker(a,d)
=\left\{\begin{pmatrix}1&b\\0&1\end{pmatrix}:b\in R_n\right\}.
                                                               \tag{9.29y}
$$

For a subgroup $H\subset G_n$, set

$$
H_\lambda=H\cap B_{n,\lambda},\quad
J_\lambda=H\cap I_{n,\lambda},\quad
U_{H,\lambda}=H\cap U_{n,\lambda},\quad
A_{H,\lambda}=a(J_\lambda),\quad
D_{H,\lambda}=d(H_\lambda).                               \tag{9.29z}
$$

The letter $D$ in $D_{H,\lambda}$ denotes the lower-right residue action and not the
Drinfeld ring.  Write $|U_{H,\lambda}|=p^s$ and
$m_n=q^{n-1}(q-1)$.

**Proposition 9.5 (invariant branches and normalized-compositum reduction).**  Let
$\mathfrak p_\lambda=(z_{\lambda,n})\subset D_n$, let
$\kappa_\lambda=\operatorname{Frac}(D_n/\mathfrak p_\lambda)$, and let
$\mathfrak p_{H\lambda}=\mathfrak p_\lambda\cap D_n^H$.  Then the following assertions hold.

1.  Inside $\kappa_\lambda=\bar k((w))$, the function field of the normalized reduced branch
    of $D_n^H$ belonging to the $H$-orbit of $\lambda$ is

    $$
    \kappa_{H\lambda}
      =\bigl(\kappa_\lambda^{D_{H,\lambda}}\bigr)^{p^s}.
                                                                  \tag{9.30}
    $$

    Here $F^{p^s}$ means the image of the $s$-fold absolute Frobenius of the
    one-variable field $F$.  Moreover

    $$
    \begin{aligned}
    e(D_n/D_n^H;\lambda)&=|A_{H,\lambda}|,\\
    \operatorname{mult}_{\mathfrak p_{H\lambda}}(\pi)
       &=\frac{m_n}{|A_{H,\lambda}|},\\
    [\kappa_\lambda:\kappa_{H\lambda}]_{\rm sep}
       &=|D_{H,\lambda}|,\\
    [\kappa_\lambda:\kappa_{H\lambda}]_{\rm insep}
       &=|U_{H,\lambda}|.
    \end{aligned}                                               \tag{9.31}
    $$

    Thus reduction followed by $H$-invariants misses precisely the Frobenius subfield of
    degree $|U_{H,\lambda}|$; it is an equality only when the translation subgroup
    $U_{H,\lambda}$ is trivial.

2.  The decomposition and inertia filtration for $D_n/D_n^H$ at this branch is

    $$
    1\longrightarrow J_\lambda\longrightarrow H_\lambda
      \xrightarrow{\,d\,}D_{H,\lambda}\longrightarrow1,
    \qquad
    1\longrightarrow U_{H,\lambda}\longrightarrow J_\lambda
      \xrightarrow{\,a\,}A_{H,\lambda}\longrightarrow1.       \tag{9.32}
    $$

    If $\overline A_{H,\lambda}$ denotes reduction in $k_v^\times$, the wild subgroup in this
    upward extension and its tame quotient are

    $$
    P_{H,\lambda}=H\cap P_{n,\lambda},\qquad
    J_\lambda/P_{H,\lambda}\simeq\overline A_{H,\lambda}.
                                                                  \tag{9.32a}
    $$

    If $H\triangleleft G_n$, the descended cover $D_n^H/A^{(0)}$ has, at the chosen
    $H$-orbit, decomposition and inertia groups

    $$
    \overline B_\lambda=B_{n,\lambda}/H_\lambda,
    \qquad
    \overline I_\lambda=I_{n,\lambda}/J_\lambda,              \tag{9.33}
    $$

    with exact filtration

    $$
    1\to U_{n,\lambda}/U_{H,\lambda}\to\overline I_\lambda
      \to R_n^\times/A_{H,\lambda}\to1.                      \tag{9.34}
    $$

    Its wild subgroup and tame quotient are

    $$
    \overline P_\lambda
      =P_{n,\lambda}/(H\cap P_{n,\lambda}),\qquad
    \overline I_\lambda/\overline P_\lambda
      \simeq k_v^\times/\overline A_{H,\lambda}.             \tag{9.34a}
    $$

    Its ramification index, separable residue degree, and inseparable residue degree are,
    respectively,

    $$
    \frac{m_n}{|A_{H,\lambda}|},\qquad
    \frac{m_n}{|D_{H,\lambda}|},\qquad
    \frac{q^n}{|U_{H,\lambda}|}.                              \tag{9.35}
    $$

    For nonnormal $H$, the same formulas hold in the decomposition groupoid, with stabilizers
    rather than quotient groups.

3.  The spectator/ray compositum has the following exact local form.  Let $\mathcal V_0$ be
    the henselian DVR at the underlying base branch, with uniformizer $\pi$, residue field
    $\kappa_0$, and fraction field $K_{\mathrm{br}}$.  Let $\mathcal V$ be the henselian DVR of one
    descended active branch, finite over $\mathcal V_0$, put
    $L_{H\lambda}=\operatorname{Frac}(\mathcal V)$, and write $\tau$ and $\kappa$ for its
    uniformizer and residue field.  Then

    $$
    \pi=u\tau^m,\qquad u\in\mathcal V^\times,
    \qquad m=\frac{m_n}{|A_{H,\lambda}|}.
                                                                  \tag{9.36}
    $$

    Let $R^\dagger$ be one arithmetic spectator/ray henselian trait factor over
    $\mathcal V_0$, put
    $K^\dagger=\operatorname{Frac}(R^\dagger)$, and write $\varpi$ and $k^\dagger$ for its
    uniformizer and residue field, with
    $\pi=v\varpi^r$ for $v\in(R^\dagger)^\times$.  The selected arithmetic factor
    $K^\dagger/K_{\mathrm{br}}$ is tame, so in particular $r$ is prime to $p$.  Put
    $c=\gcd(m,r)$, $m=cm_0$, $r=cr_0$, and first choose a field factor $\kappa_j$ of the
    reduced residue compositum

    $$
    (\kappa\otimes_{\kappa_0} k^\dagger)_{\rm red}.
                                                                  \tag{9.36a}
    $$

    Let $\bar u_j$ be the image in $\kappa_j^\times$ of the residue of $u/v$.  Factor the
    separable polynomial

    $$
    T^c-\bar u_j^{-1}=\prod_\alpha F_{j,\alpha}(T)
                                                                  \tag{9.36b}
    $$

    into monic irreducibles over $\kappa_j$.  The normalized base change has one arithmetic
    branch for each pair $(j,\alpha)$, and that branch has residue field

    $$
    \kappa_{j,\alpha}
       =\kappa_j[T]/(F_{j,\alpha}),                              \tag{9.36c}
    $$

    ramification index $r/c$ over $\mathcal V$, and Cartier multiplicity $m/c$ over
    $R^\dagger$.  Over a separable closure (9.36b) has $c$ linear factors, but over the actual
    residue field the number of branches is the number of irreducible factors, not necessarily
    $c$, and their residue extensions cannot be omitted.

    For the generic factor corresponding to $(j,\alpha)$, choose its embedding
    $\iota_{j,\alpha}:L_{H\lambda}\hookrightarrow\Omega$ and view $K^\dagger$ in the same
    separable closure $\Omega$ of the henselian base field $K_{\mathrm{br}}$.
    Set

    $$
    E_{H\lambda,j,\alpha}
      =\iota_{j,\alpha}(L_{H\lambda})\cap K^\dagger.            \tag{9.37}
    $$

    If both extensions are Galois, the decomposition group of the selected compositum factor
    is the compatible-pair group

    $$
    D_{H\lambda,j,\alpha}^\dagger
      \simeq
      \operatorname{Stab}_{(j,\alpha)}\!\left(
        D(\iota_{j,\alpha}(L_{H\lambda})/K_{\mathrm{br}})
        \times_{\operatorname{Gal}(E_{H\lambda,j,\alpha}/K_{\mathrm{br}})}
        D(K^\dagger/K_{\mathrm{br}})\right),                  \tag{9.37a}
    $$

    where the action on $(j,\alpha)$ is the action on the residue-compositum and Kummer
    factors.  Its inertia group is

    $$
    I_{H\lambda,j,\alpha}^\dagger
      =D_{H\lambda,j,\alpha}^\dagger\cap
        \bigl(I(\iota_{j,\alpha}(L_{H\lambda})/K_{\mathrm{br}})
              \times I(K^\dagger/K_{\mathrm{br}})\bigr).     \tag{9.37b}
    $$

    Thus the fiber product is over the **actual intersection field** (with its unramified and
    ramified parts), not over an abstract cyclic group of order $c$.  Since the arithmetic
    ramification is tame, its wild inertia is trivial and
    $E_{H\lambda,j,\alpha}/K_{\mathrm{br}}$ is tame;
    hence the active wild subgroup restricts trivially to $E_{H\lambda,j,\alpha}$.  It fixes the
    residue-compositum and the prime-to-$p$ Hensel factor in (9.36b), so it survives on the
    selected compatible factor.  For nonnormal $H$, the same statement is made in the common Galois closure with
    decomposition stabilizers.  Only when (9.36b) splits linearly over the selected residue
    factor and $E_{H\lambda,j,\alpha}$ is the full common tame subextension of degree $c$ may one replace
    (9.37a) by the shorter fiber-product notation over $C_c$.

The proposition stops at this reduction.  In particular, neither the equality
$c=\gcd(m,r)$ nor geometric splitting after strict henselization determines the arithmetic
branches.  The following is the exact unfinished ledger for an **arbitrary** intermediate
representation and arbitrary arithmetic trait.  Propositions 9.9--9.10 below solve the
strict actual-row specialization without assuming this general ledger.

**General Kummer branch ledger $({\rm KBL}_v)_{\rm gen}$.**  For every selected $H$-orbit, every
deformation-etale spectator sheet, and every arithmetic spectator/ray factor:

1. descend the branch to its actual residue field, list every field factor $\kappa_j$ in
   (9.36a), compute the Kummer class
   $[\bar u_j]\in\kappa_j^\times/(\kappa_j^\times)^c$, and factor
   $T^c-\bar u_j^{-1}$ as in (9.36b);
2. record each residue extension $\kappa_{j,\alpha}/\kappa_j$, its residue-Frobenius orbit,
   the local intersection field $E_{H\lambda,j,\alpha}$ for the corresponding generic factor, and all
   restriction maps in (9.37a)--(9.37b); the integer $c$ is not a substitute for this field
   data;
3. repeat the calculation for the divisorial valuations and conductor endpoints created by
   the chosen equivariant regular domination, including the Kummer classes of the monomial
   blowup ratios and the stabilizers of the actual factors; and
4. from those factors construct the full branch nearby-cycle complexes
   $\mathcal C_v(W)$, their conductor fibers $C_{e,v}(W)$, and the generization chain maps
   $K_e(W)\to C_{e,v}(W)$, with residue Galois and tame inertia.  The raw inclusions in
   (9.29x) give only coefficient maps.  They do not prove
   $C_{e,v}(W)=W^{P_{e,v}}[0]$; that degree-zero formula is available only after the relevant
   Kummer cover has actually been shown to be a geometric disc with no retained branch
   monodromy.

Completing this ledger and proving its compatibility with arbitrary intermediate and
spectator/ray descent is the general input $({\rm HDB}_v)_{\rm gen}$ (higher Drinfeld
branch-complex descent).
The purely inseparable invariant-ring discrepancy is already computed in (9.30)--(9.35), but
it does not determine the prime-to-$p$ Kummer factors above it.

There is a formal, correctly typed pushforward once $({\rm HDB}_v)_{\rm gen}$ has supplied those
complexes.  Let $g$ be the finite normalized-cover map and $h$ the chosen proper regular
domination.  Let $f=(g\circ h)_{\bar s}:\widetilde Z_{\bar s}\to X_{\bar s}$ be one leg, let
$C_v$ be a normalized source component, and write
$f_v=f|_{C_v}$.  Put

$$
\mathcal F_W=Rg_{\bar\eta *}\mathcal L_W,
\qquad
\mathcal K_X(W)=R\Psi_X\mathcal F_W.
$$

Book 22, (2.8) and (3.10), give

$$
\mathcal K_X(W)
 \simeq Rf_*\mathcal N_{\widetilde Z}(W),                    \tag{9.38}
$$

and the right side is the sheaf-valued homotopy fiber

$$
\operatorname{Fib}\!\left(
 \bigoplus_v Rf_{v*}\mathcal C_v(W)
 \oplus\bigoplus_e i_{f(e)*}K_e(W)
 \longrightarrow
 \bigoplus_{e\ni v}i_{f(e)*}C_{e,v}(W)
\right).                                                     \tag{9.39}
$$

Here $i_{f(e)}:\{f(e)\}\hookrightarrow X_{\bar s}$.  If $f_v$ contracts $C_v$ to a point
$x$, then $f_v=i_x\circ p_v$ and

$$
Rf_{v*}\mathcal C_v(W)
 =i_{x*}R\Gamma(C_v,\mathcal C_v(W)).                         \tag{9.40}
$$

If $f_v$ is not contracted, its term remains $Rf_{v*}\mathcal C_v(W)$; it may be replaced by
a finite pushforward only on a locus where finiteness has been proved.  In particular an
unlocated complex $R\Gamma(C_v,-)$ is not a component contribution on the target.

The direct image (9.38) is not a trace.  Properness gives only the duality counit
$Rf_*f^!\to\mathrm{id}$, not an untwisted arrow $Rf_*f^*\to\mathrm{id}$.  The exact second
statement needed is therefore the following.  Proposition 9.8 below constructs it; its
orientation comes from the generic lci correspondence and not from properness.

**Restriction--Gysin/correspondence statement $({\rm RGC}_v)$.**  For the two proper
legs $f_0,f_1$ of a common equivariant regular domination, construct a degree-zero
cohomological correspondence

$$
c_{01}:f_0^*\mathcal K_X(W)\longrightarrow f_1^!\mathcal K_X(W)       \tag{9.41}
$$

for the full normalization--conductor complex just defined, extending the oriented generic
finite correspondence.  Prove that on a noncontracted finite component it is restriction
followed by the oriented finite trace, whereas on a component contracted to a point it is the
appropriate restriction--Gysin map through the term (9.40), with the codimension shift, Tate
twist, inseparable degree and refined intersection multiplicity retained.  Prove independence
of the chosen domination, compatibility with the maps in (9.39), residue Frobenius and retained
prime-to-$v$ Hecke routes, and prove that the construction with the two legs exchanged is
adjoint.  Proposition 9.4 already supplies coefficient and expansion one on the unique
node-to-node sheet; it does not construct (9.41) on the component-routed or contracted terms.

**Proof of Proposition 9.5.**  We prove the three assertions of the proposition.  The ledgers following it are
explicitly not part of the proposition.

On the branch $\lambda=R_ne_1$, use $z=X_n$ and $w=Y_n$.  The upper-triangular action has the
exact form

$$
z\longmapsto[a]_G(z),\qquad
w\longmapsto[b]_G(z)+_G[d]_G(w).                            \tag{9.42}
$$

Consequently $U_{H,\lambda}$ fixes the divisorial parameter $z$ and acts trivially on
$\kappa_\lambda$.  More is visible directly.  In the height-one completed DVR form the orbit
invariant

$$
\Xi_{U_H}(w)=
 \prod_{u\in U_{H,\lambda}}u(w),
 \qquad
 u=\begin{pmatrix}1&b(u)\\0&1\end{pmatrix},\quad
 u(w)=[b(u)]_G(z)+_G w.
$$

Translation by an element of $U_{H,\lambda}$ permutes the factors, while reduction modulo
$z$ gives

$$
\overline{\Xi_{U_H}(w)}=w^{|U_{H,\lambda}|}=w^{p^s}.
$$

The extension obtained by quotienting by $U_{H,\lambda}$ has ramification index one because
$z$ itself is a fixed uniformizer.  The invariant height-one ring is finite (the rings are
excellent normalizations), so the length formula for this finite extension of DVRs has no
missing defect factor.  Its residue extension is consequently purely inseparable of degree
$|U_{H,\lambda}|$.  The displayed orbit invariant puts
$\bar k((w^{p^s}))$ in the lower residue field, and
$[\bar k((w)): \bar k((w^{p^s}))]=p^s$; hence the lower residue field is exactly
$\bar k((w^{p^s}))$.  Next,
$J_\lambda/U_{H,\lambda}$ injects through $a$ into $R_n^\times$.  At the height-one generic
point, $z$ is a primitive point of the connected height-one $\pi^n$-torsion.  The factorization
(9.29r) is its Eisenstein--Lubin--Tate factorization.  For
$A=A_{H,\lambda}$ the orbit norm

$$
\Theta_A(z)=\prod_{\alpha\in A}[\widetilde\alpha]_G(z)
$$

is invariant and has $z$-valuation $|A|$.  Dividing the primitive-vector factorization
(9.29r) into $A$-orbits and applying Weierstrass division by $\Theta_A$ gives

$$
\widehat{\mathcal O}_{U}^{\vphantom A}
  =\bigoplus_{i=0}^{|A|-1}
    \bigl(\widehat{\mathcal O}_{U}^{A}\bigr)z^i,
$$

where $\widehat{\mathcal O}_{U}$ is the height-one complete DVR after the
$U_{H,\lambda}$-quotient; coefficient comparison in the remainder gives the directness.
Thus $\Theta_A$ is a uniformizer downstairs and the invariant value group has index $|A|$.
This step is totally ramified of degree $|A_{H,\lambda}|$ and does not change the residue
field.  Finally
$H_\lambda/J_\lambda$ acts faithfully and separably on $w$ through $D_{H,\lambda}$, by the
exact-order argument preceding (9.29s).  It contributes the separable residue degree
$|D_{H,\lambda}|$ and no ramification.  Reduction of the $a$-character identifies the
$p$-Sylow row (9.32a).

The normalized branch field is therefore a subfield of
$\kappa_\lambda^{D_{H,\lambda}}$ over which the latter has purely inseparable degree
$|U_{H,\lambda}|=p^s$.  A one-variable function field over the perfect field $\bar k$ has
$p$-rank one.  The $p^s$th power of every element lies in the lower field, while the
$p^s$-Frobenius image already has index $p^s$; equality of degrees therefore identifies the
lower field with that Frobenius image.  This proves (9.30)--(9.32).  Since
$v_\lambda(\pi)=m_n$ by (9.29r), restriction of
normalized valuations gives

$$
m_n=e(D_n/D_n^H;\lambda)\,
      v_{\mathfrak p_{H\lambda}}(\pi),
$$

which proves the Cartier formula.  When $H$ is normal, taking the two quotients of the exact
upper-triangular filtration gives (9.33)--(9.35); reduction of the $a$-character gives the
wild/tame row (9.34a).  This also recovers (9.29t) at $H=G_n$ and
the level-one multiplicity $q-1$ at $H=\ker(G_n\to G_1)$, two independent checks on the
formula.  At $H=1$ it returns $\kappa_\lambda$ and multiplicity $m_n$; at $H=G_n$ it says
explicitly

$$
\bar k((t))
  =\bigl(\kappa_\lambda^{R_n^\times}\bigr)^{q^n},
$$

which is the strict invariant--reduction discrepancy recorded after (9.29t).

For the compositum, the deformation-etale spectator factor becomes a product only after the
appropriate residue embedding is chosen; its arithmetic field of definition is retained in
$R^\dagger$.  In $\mathcal V\otimes_{\mathcal V_0}R^\dagger$, (9.36) gives

$$
\tau^m=(u/v)^{-1}\varpi^r.
$$

Every extension of the resulting valuation makes
$T=\tau^{m_0}/\varpi^{r_0}$ a unit satisfying
$T^c=(u/v)^{-1}$.  Because $p\nmid c$, Hensel factorization identifies its unramified factors
with the irreducible factors of $T^c-\bar u_j^{-1}$ over each residue-compositum field
$\kappa_j$.  On the factor indexed by $(j,\alpha)$, normalized valuations satisfy

$$
v(\tau)=r_0,\qquad v(\varpi)=m_0.
$$

Bezout for $(m_0,r_0)=1$ produces a uniformizer of value one, proving the two ramification and
Cartier assertions and the residue formula (9.36c).  Finally, the standard restriction map for
two Galois fields in one separable closure identifies the Galois group of their compositum with
the compatible pairs over their intersection.  Intersecting with the two inertia groups gives
(9.37b).  Tameness of $K^\dagger/K_{\mathrm{br}}$ makes its wild inertia and the wild inertia of the
intersection trivial.  This proves part 3 and the proposition. $\square$

The reduction in Proposition 9.5 can be sharpened after completion at every conductor
endpoint.  Locally, the arbitrary function-field unit then reduces to its valuation and one
constant-field Kummer class.  This does not replace the global class in $\kappa_j^\times$.

**Proposition 9.6 (endpoint Kummer factors and the exact arithmetic datum).**  Retain
$n,H,\lambda$ from Proposition 9.5.  Let $\mathfrak q_{H\lambda}$ be the selected conductor
endpoint on the normalization of the active $H$-branch.  For the chosen equation
$\pi=u\tau^m$ in (9.36), put

$$
d_{H\lambda,\mathfrak q_{H\lambda}}
 =\operatorname{ord}_{\mathfrak q_{H\lambda}}(\bar u).   \tag{9.42a}
$$

This valuation is part of the endpoint Kummer datum.  It is not determined by
$n,H,\lambda$ and the cardinalities in (9.31): changing the chosen vertical equation changes
it by a multiple of $m$, while leaving the Kummer factor fields below unchanged.

Let $\mathfrak q_j$ be an endpoint of the normalization of the residue-compositum function
field $\kappa_j$ in (9.36a), above $\mathfrak q_{H\lambda}$.  After choosing
a coefficient field and branch parameter, its completed valuation ring and field are

$$
\widehat{\mathcal O}_{\kappa_j,\mathfrak q_j}
 \simeq k_{j,\mathfrak q_j}[[\xi]],
\qquad
F_{j,\mathfrak q_j}\simeq k_{j,\mathfrak q_j}((\xi)),
$$

where $k_{j,\mathfrak q_j}$ is the actual residue field: finite on the descended arithmetic
factor and algebraically closed after geometric strict base change.  For the arithmetic trait
factor of (9.36), let

$$
a_{j,\mathfrak q_j}=\overline{u/v}\in F_{j,\mathfrak q_j}^\times,\qquad
c=\gcd(m,r).
$$

Thus $p\nmid c$, because the spectator ramification index $r$ is tame.

Let $e_{j,\mathfrak q_j}$ be the ramification index at this endpoint of the selected
residue-compositum factor over the completed active $H$-branch, let
$h_{j,\mathfrak q_j}=\operatorname{ord}_\xi(\bar v)$, and put

$$
d_{j,\mathfrak q_j}
 =e_{j,\mathfrak q_j}d_{H\lambda,\mathfrak q_{H\lambda}}
       -h_{j,\mathfrak q_j}.                              \tag{9.42b}
$$

For a deformation-etale spectator sheet and a ray extension pulled back only from the trait,
$e_{j,\mathfrak q_j}=1$ and $h_{j,\mathfrak q_j}=0$, so
$d_{j,\mathfrak q_j}=d_{H\lambda,\mathfrak q_{H\lambda}}$.  The more general formula retains
a spectator residue extension which ramifies at the conductor endpoint.

Then:

1. $\operatorname{ord}_\xi(a_{j,\mathfrak q_j})=d_{j,\mathfrak q_j}$.  There is a uniquely
   determined leading
   coefficient

   $$
   \delta_{H\lambda,j,\mathfrak q_j}
     =\overline{\xi^{-d_{j,\mathfrak q_j}}a_{j,\mathfrak q_j}}
       \in k_{j,\mathfrak q_j}^\times,                    \tag{9.42c}
   $$

   relative to the chosen branch parameter, and

   $$
   [a_{j,\mathfrak q_j}]
    =[\delta_{H\lambda,j,\mathfrak q_j}\xi^{d_{j,\mathfrak q_j}}]
   \quad\hbox{in }F_{j,\mathfrak q_j}^\times/
                         (F_{j,\mathfrak q_j}^\times)^c. \tag{9.42d}
   $$

   Changing $\xi$ changes $\delta_{H\lambda,j,\mathfrak q_j}$ so that the product in
   (9.42d) represents the same element.  Changing either vertical uniformizer multiplies it
   by an evident $c$th power.  In either case the factor fields are unchanged.

2. Put $g_{j,\mathfrak q_j}=\gcd(c,|d_{j,\mathfrak q_j}|)$,
   $c=g_{j,\mathfrak q_j}c_{j,\mathfrak q_j}'$, and
   $d_{j,\mathfrak q_j}=g_{j,\mathfrak q_j}d_{j,\mathfrak q_j}'$.  Factor the
   **constant-field polynomial**

   $$
   Z^{g_{j,\mathfrak q_j}}-\delta_{H\lambda,j,\mathfrak q_j}^{-1}
     =\prod_\beta G_{j,\mathfrak q_j,\beta}(Z)             \tag{9.42e}
   $$

   over $k_{j,\mathfrak q_j}$.  The irreducible factors of (9.36b) after completion at this
   endpoint are indexed by the factors $G_{j,\mathfrak q_j,\beta}$.  Put
   $k_{j,\mathfrak q_j,\beta}=k_{j,\mathfrak q_j}[Z]/
   (G_{j,\mathfrak q_j,\beta})$ and let $\zeta_\beta$ be the class of $Z$.  The
   corresponding completed field is

   $$
   k_{j,\mathfrak q_j,\beta}((\xi))[S]\big/
      \left(S^{c_{j,\mathfrak q_j}'}
                   -\zeta_\beta\xi^{-d_{j,\mathfrak q_j}'}\right), \tag{9.42f}
   $$

   after scaling $T$ by the unique principal-unit $c$th root in (9.42d).  It has constant
   residue degree $\deg G_{j,\mathfrak q_j,\beta}$ and tame ramification index
   $c_{j,\mathfrak q_j}'$.  If $k_{j,\mathfrak q_j}$ is finite, its
   arithmetic residue-Frobenius orbit is exactly the orbit of $\zeta_\beta$ under
   $z\mapsto z^{|k_{j,\mathfrak q_j}|}$.  Over an algebraically closed constant field there
   are exactly $g_{j,\mathfrak q_j}$, not necessarily $c$, factors, each of degree
   $c/g_{j,\mathfrak q_j}$.

3. For a **generic** factor $(j,\alpha)$ of (9.36b), let
   $\Pi^{\rm t}_{\mathrm{br}}$ be the tame Galois group of the henselian base branch.  In
   one tame closure let $H_L$ fix
   $\iota_{j,\alpha}(L_{H\lambda})\cap K_{\mathrm{br}}^{\rm t}$ and let $H_\dagger$ fix
   $K^\dagger$.  Then the actual intersection in (9.37) is

   $$
   E_{H\lambda,j,\alpha}
    =(K_{\mathrm{br}}^{\rm t})^{
       \overline{\langle H_L,H_\dagger\rangle}}.           \tag{9.42g}
   $$

   If both fields are Galois, $H_L,H_\dagger$ are normal and
   $\operatorname{Gal}(E/K_{\mathrm{br}})=
   \Pi^{\rm t}_{\mathrm{br}}/overline{\langle H_L,H_\dagger\rangle}$; the two maps in
   (9.37a) are its quotient maps.  Formula (9.42e) determines the arithmetic-Frobenius
   permutation of the constant factors.  Together, (9.42e)--(9.42f) in a chosen tame closure
   determine the local action on the endpoint Kummer roots.  For a selected endpoint
   $(\mathfrak q_j,\beta)$, the corresponding decomposition group is its stabilizer in
   $D_{H\lambda,j,\alpha}^\dagger$, and its vertical inertia is the intersection of that
   stabilizer with $I_{H\lambda,j,\alpha}^\dagger$; the residue and tame-endpoint actions are
   those of (9.42e)--(9.42f).  The two global tame characters are still required to determine
   $H_L$ and $H_\dagger$; neither is replaced by a cyclic group of order $c$.

4. The same calculation is stable under the chosen regular domination.  At a normal-crossing
   chart

   $$
   \pi=\epsilon x^a y^b,\qquad
   \epsilon\in\widehat{\mathcal O}_{\widetilde Z,e}^{\times}, \tag{9.42h}
   $$

   and for $\pi=v\varpi^r$, the $x=0$ branch uses
   $c_x=\gcd(a,r)$ and the polynomial

   $$
   T^{c_x}-
    \left(\overline{\epsilon(0,y)/v}\,y^b\right)^{-1}.    \tag{9.42i}
   $$

   Apply clauses 1--2 with $c=c_x$, and take $d$ and $\delta$ to be the order and
   leading coefficient of $\overline{\epsilon(0,y)y^b/v}$.  Blowing up $x=y=0$ replaces
   the ordered multiplicity pair
   $(a,b)$ by $(a+b,b)$ in the $x$-chart and by $(a,a+b)$ in the $y$-chart.  Iterating this
   rule computes every exceptional-component and conductor-endpoint factor, including its
   constant extension, Frobenius orbit, and stabilizer under the retained decomposition action.

**Proof.**  Formula (9.42b) is the restriction formula for normalized valuations: pulling
$\bar u$ to the selected residue-compositum endpoint multiplies its order by
$e_{j,\mathfrak q_j}$, and division by $\bar v$ subtracts
$h_{j,\mathfrak q_j}$.  There is no uniform replacement of (9.42a) by a quotient of the
group orders in (9.31).  For example, take $n>1$, $H=1$, and the natural branch equation
$\tau=z_{\lambda,n}$.  Besides $\lambda=R_ne_1$,
the raw special fiber has the $q^n$ transverse branches $R_n(r,1)$ and the
$q^{n-1}-1$ further branches $R_n(1,s)$ with $0\ne s\in\pi R_n$.  Every latter branch also
meets the conductor endpoint, with positive intersection multiplicity.  Thus dividing
(9.29r) by the $\lambda$-factor has endpoint order strictly larger than $q^nm_n$; the
omitted same-tangent branches cannot be discarded.  More generally, after pullback to a raw
branch, the divisor of $\bar u$ records the branches outside the selected $H$-orbit together
with their actual endpoint intersection multiplicities.  Those multiplicities and the unit
relating a chosen local branch equation to an orbit equation are endpoint data, not just
decomposition-group cardinalities.

Since $p\nmid c$, Hensel's lemma makes $x\mapsto x^c$ an automorphism of
$1+\xi k_{j,\mathfrak q_j}[[\xi]]$.  Removing that principal unit proves
(9.42c)--(9.42d).  After scaling
$T$, (9.36b) becomes

$$
S^c-\delta_{H\lambda,j,\mathfrak q_j}^{-1}
       \xi^{-d_{j,\mathfrak q_j}}.
$$

Over a field containing a root $\zeta$ of (9.42e), its factors are
$S^{c_{j,\mathfrak q_j}'}-\zeta\xi^{-d_{j,\mathfrak q_j}'}$.  The Newton polygon is one
segment whose relatively prime horizontal and absolute vertical lengths are
$c_{j,\mathfrak q_j}'$ and $|d_{j,\mathfrak q_j}'|$, so each such binomial is irreducible
and totally tamely ramified of degree $c_{j,\mathfrak q_j}'$ when
$d_{j,\mathfrak q_j}\ne0$: a factor of degree $h$ would have integral endpoint height
$h d_{j,\mathfrak q_j}'/c_{j,\mathfrak q_j}'$, forcing
$c_{j,\mathfrak q_j}'\mid h$.  If $d_{j,\mathfrak q_j}=0$, then
$g_{j,\mathfrak q_j}=c$ and only the constant-field factorization remains.  Descent groups
the roots $\zeta$ into precisely the irreducible factors
$G_{j,\mathfrak q_j,\beta}$, proving clause 2 and the Frobenius assertion.

Because $K^\dagger/K_{\mathrm{br}}$ is tame,
$\iota_{j,\alpha}(L_{H\lambda})\cap K^\dagger$ equals
$(\iota_{j,\alpha}(L_{H\lambda})\cap K_{\mathrm{br}}^{\rm t})\cap K^\dagger$.  For these two
tame fields in one tame closure, Galois correspondence gives
$(K_{\mathrm{br}}^{\rm t})^{H_L}\cap
(K_{\mathrm{br}}^{\rm t})^{H_\dagger}
=(K_{\mathrm{br}}^{\rm t})^{\overline{\langle H_L,H_\dagger\rangle}}$; this proves
(9.42g), including the restriction maps.  Finally, along $x=0$ equation (9.42h) reads
$\pi=(\epsilon y^b)x^a$.  Proposition 9.5 applied to that divisorial valuation gives
(9.42i).  The two blowup substitutions $y=xy_1$ and $x=x_1y$ give the stated pairs, so
induction proves clause 4. $\square$

The endpoint constants $\delta_{H\lambda,j,\mathfrak q_j}$ and the tame subgroup
$H_\dagger$ are genuine arithmetic data.  They cannot be recovered from $m,r$ and the
input residue fields.  For example, take
$K_0=\mathbf F_5((\pi))$ and $m=r=c=2$.  Let
$L=K_0(\sqrt\pi)$.  The spectator $K_0(\sqrt\pi)$ has $v=1$ and gives
$T^2-1$, two residue factors, intersection field $L$, and diagonal compatible-pair group
$C_2\times_{C_2}C_2\simeq C_2$.  The equally tame spectator
$K_0(\sqrt{\pi/2})$ has $v=2$ and gives $T^2-2$, which is irreducible over $\mathbf F_5$;
its intersection with $L$ is $K_0$ and the compatible-pair group is $C_2\times C_2$.  All
gcd and ramification-index data in the two examples are identical.  Thus neither a
branch-count rule based on $\gcd(m,r)$ nor an unspecified ``tame ray factor'' determines the
answer.

The endpoint field calculation is not yet a conductor calculation.  In particular, replacing
a smooth branch tube by a punctured special-fiber disc and applying $Rj_*$ would add a
spurious degree-one tame class even for the constant sheaf; Book 22, (3.10), rules out exactly
that substitution.  The correct construction is the following, which also isolates the
remaining local theorem.

**Proposition 9.7 (exact tube construction and the boundary of
$({\rm HDB}_v)_{\rm gen}$).**  Suppose
the actual normalized finite cover $\mathscr Y$ on the chosen regular domination has been
given, together with its generic coefficient $\mathcal L_W$, pulled back to the generic fiber
of that domination.  Let $\mathfrak B_v$ be its
completed two-dimensional branch model along a normalized special-fiber component $C_v$,
let $\mathfrak B_{e,v}$ be the strict-local formal germ at a conductor point $e_v$, and let
$\mathfrak A_e$ be the oriented strict node germ before normalization of its special fiber.
Normalization is an isomorphism on the generic fiber, so $\mathcal L_W$ restricts to the
generic Milnor tube of $\mathfrak A_e$.  Here the generic fiber of a displayed formal germ
means the geometric generic fiber of the corresponding strict localization in Book 22,
(2.2); it is not a punctured special-fiber scheme.  Define

$$
\mathcal C_v(W)=R\Psi_{\mathfrak B_v}\mathcal L_W,
\qquad
C_{e,v}(W)=R\Gamma((\mathfrak B_{e,v})_{\bar\eta},\mathcal L_W),
\qquad
K_e(W)=R\Gamma((\mathfrak A_e)_{\bar\eta},\mathcal L_W). \tag{9.42j}
$$

The specialization of geometric points from the node tube toward the oriented branch gives
the canonical generization morphism

$$
g_{e,v}:K_e(W)\longrightarrow C_{e,v}(W).                 \tag{9.42k}
$$

Here every generic fiber is the actual geometric Milnor tube, not the punctured special-fiber
curve.  Formula (9.42k) is the induced morphism of oriented specialization topoi.  With these
definitions, Book 22, (3.10), gives (9.39) stalkwise and equivariantly.

The global factor $F_{j,\alpha}$ in (9.36b), its decomposition action, and all completed
factors (9.42e)--(9.42f) determine the normalization and inertia labels of those tubes.  They
do **not** determine their cohomology from the reduced branch alone.  To calculate (9.42j)--
(9.42k), one must additionally identify the completed two-dimensional normalization at
$e_v$, the induced map from its generic Milnor tube to the node tube, and the action on
$W$.  When the identified tube is a prime-to-$p$ $K(\pi,1)$, as in the disc and annulus cases
used here, finite wild image is removed exactly by

$$
R\Gamma(\Pi,W)\simeq R\Gamma(\Pi/P,W^P).                 \tag{9.42l}
$$

Only an annular tame quotient then gives the strict procyclic complex
$[M\xrightarrow{T-1}M]$; a geometric disc across which the invariant coefficient extends
gives $M[0]$.  The chain map (9.42k) is restriction along the actual map of tubes, with the
conjugation action of Book 22, (3.6).  Thus the construction preserves residue Frobenius,
wild and tame inertia, and stabilizers without identifying a conductor fiber with a second
node-annular complex.

**Proof.**  Formula (9.42j) is the strict-local Milnor-tube formula for nearby cycles, and
generization in the oriented specialization topos gives (9.42k).  The normalization--
conductor homotopy fiber is then Book 22, (3.10).  For an actual local tube, (9.42l) is Book
22, (3.12)--(3.13), and Book 22, (3.14), supplies the procyclic resolution precisely in the
annular case.
Local acyclicity gives the asserted degree-zero complex in the disc case.  All statements are
functorial for automorphisms of the finite cover, so the arithmetic actions commute with the
maps. $\square$

Thus the general $({\rm KBL}_v)_{\rm gen}$ and $({\rm HDB}_v)_{\rm gen}$ have been reduced to
two irreducible inputs.  First, arbitrary data must name their spectator/ray factor, hence the global function
$\overline{u/v}$, its endpoint valuations and leading coefficients, the fields $\kappa_j$,
and the two tame subgroups in (9.42g); (9.26) currently
chooses only an existential common finite generic algebra, and the scalar case says only ``if
a global ray extension is used.''  Proposition 9.6 factors every completed endpoint and
blowup chart once those data are supplied.  Second, the resulting finite cover must be
identified on the completed two-dimensional branch tubes, not merely on their reduced residue
fields.  Proposition 9.7
turns exactly that local normalization theorem into the conductor complexes and generization
maps.  Neither missing input can be recovered from $\gcd(m,r)$.

More precisely, after an actual $R^\dagger$, the global Kummer function
$\overline{u/v}$, its endpoint valuations and leading coefficients, and the two tame
subgroups have been named, the only remaining local geometric statement is the following
factorwise theorem.

**General Kummer--tube target
$({\rm BTK}^{\rm gen}_{H,\lambda,j,\alpha,\mathfrak q_j,\beta,e})$.**  Let $\widehat A_{0,e}$,
$\widehat A_{H,e}$ and $\widehat A_e^\dagger$ be the completed two-dimensional local base,
active $H$-intermediate, and actual spectator/ray algebras at $e$; for a trait-pulled ray
factor the third is the completed base change of $\widehat A_{0,e}$ along $R^\dagger$.
Localize
$\widehat A_{H,e}\widehat\otimes_{\widehat A_{0,e}}\widehat A_e^\dagger$ at the prime
selected by the global factor $F_{j,\alpha}$ and an endpoint factor
$G_{j,\mathfrak q_j,\beta}$ occurring in its completion, and normalize it in the
corresponding generic compositum field.
This ring is the completed local ring of that factor in the actual common normalization; its
reduced height-one fields are exactly (9.42f), and its endpoint decomposition group is the
stabilizer of $(\mathfrak q_j,\beta)$ in the compatible-pair group (9.37a), with vertical
inertia obtained by intersection with (9.37b), intersection field (9.42g), and endpoint
residue/tame action given by (9.42e)--(9.42f).  Its generic Milnor tube maps to the oriented
node tube with the stated decomposition action.  Compute that tube as a disc, annulus, or
explicit remaining curve tube and identify the induced pullback with (9.42k).

This is a finite, two-dimensional completed-local assertion.  It is stronger than factoring
the reduced polynomial and weaker than reconstructing the global tower.  Its conclusion plus
Book 22 and (9.42l) is exactly the unresolved part of $({\rm HDB}_v)_{\rm gen}$; no further
étale-cohomological comparison is being hidden.

The correspondence part, by contrast, is formal once those actual complexes exist.

**Proposition 9.8 $({\rm RGC}_v)$ (oriented specialization of the proper
correspondence).**  Assume the actual generic coefficient and the normalized regular
domination used in Proposition 9.7 have been supplied, together with the generic
level-transport isomorphism on $\mathcal F_W$.  Then the correspondence (9.41)
exists, is independent after proper pushforward of the chosen equivariant regular domination,
and has all the restrictions, Gysin terms, Frobenius--Hecke compatibilities and transpose
adjunction required in $({\rm RGC}_v)$.

**Proof.**  Work first with finite $\ell$-power coefficients.  On the generic fiber both legs
are finite maps of smooth curves.  On the actual common generic algebra, level transport
induces the coefficient isomorphism
$\alpha_\eta:f_{0,\eta}^*\mathcal F_W\simeq
f_{1,\eta}^*\mathcal F_W$.  The oriented lci fundamental class of the second leg gives

$$
c_\eta:f_{0,\eta}^*\mathcal F_W
 \xrightarrow{\alpha_\eta}f_{1,\eta}^*\mathcal F_W
 \longrightarrow f_{1,\eta}^!\mathcal F_W.               \tag{9.42m}
$$

The total spaces are regular arithmetic surfaces.  Locally each leg factors through a regular
immersion into an affine space smooth over the regular target, so it is lci of virtual relative
dimension zero.  The last arrow in (9.42m) is the restriction of that relative orientation.

Its specialization is the standard nearby-cycle cohomological correspondence

$$
\begin{aligned}
f_{0,\bar s}^*R\Psi_X\mathcal F_W
 &\longrightarrow R\Psi_{\widetilde Z}(f_{0,\bar\eta}^*\mathcal F_W)
 \xrightarrow{R\Psi(c_\eta)}
 R\Psi_{\widetilde Z}(f_{1,\bar\eta}^!\mathcal F_W)\\
 &\longrightarrow f_{1,\bar s}^!R\Psi_X\mathcal F_W.
                                                               \tag{9.42n}
\end{aligned}
$$

The first arrow is ordinary exchange.  The last is its extraordinary, Verdier-dual exchange
map.  Neither exchange map is being declared an isomorphism in a nontransverse square; the excess defect is
retained below.  The construction is degree zero because (9.42m) has virtual relative dimension zero.
Thus (9.42n) is precisely (9.41) for $\mathcal K_X(W)$; proper nearby-cycle comparison is
the identification with the normalization--conductor model in (9.38).  This uses an
orientation before applying the proper counit; it does not manufacture
$Rf_*f^*\to\mathrm{id}$ from properness.

Under Proposition 9.7, (9.42n) is a morphism of the recollement diagram (9.39), since all its
arrows are exchange, restriction, a fundamental class, or a duality counit.  Naturality with
respect to the two oriented tube generizations makes the two squares with (9.42k) commute;
proper base change makes the component and conductor squares commute.  Taking the homotopy
fiber therefore gives one, rather than three unrelated, correspondence maps.  On a component
$C$ on which $f_1$ is nonconstant, $f_1|_C$ is finite.  Purity reduces (9.42n) there to
restriction along $f_0|_C$ followed by the oriented finite trace along $f_1|_C$.  The trace
composite contains the full residue and radicial degrees: for a universal homeomorphism the
duality counit is the counit of an equivalence, while its finite-flat orientation contributes
the inseparable degree, as in Book 20, Section 5.2.  Thus it is not counted as one geometric
sheet.  More explicitly, if
$c_C$ denotes the refined restriction of (9.42n), the component operator is

$$
R(f_1|_C)_*(f_0|_C)^*\mathcal K_X(W)
 \xrightarrow{R(f_1|_C)_*c_C}
R(f_1|_C)_*(f_1|_C)^!\mathcal K_X(W)
 \xrightarrow{\operatorname{Tr}_{f_1|_C}}\mathcal K_X(W).
$$

In the Tor-independent finite case $c_C$ is coefficient restriction followed by the lci
orientation; otherwise its refined excess factor remains part of $c_C$.

If $f_1(C)=x$, write $f_1|_C=i_xp_C$.  Deformation to the normal cone restricts the virtual
dimension-zero fundamental class to a morphism

$$
c_C:(f_0|_C)^*\mathcal K_X(W)
 \longrightarrow (f_1|_C)^!\mathcal K_X(W)
 =p_C^!i_x^!\mathcal K_X(W).                              \tag{9.42o}
$$

Its contribution to the operator is the fully typed composite

$$
\begin{aligned}
i_{x*}Rp_{C*}(f_0|_C)^*\mathcal K_X(W)
 &\xrightarrow{\ i_{x*}Rp_{C*}(c_C)\ }
 i_{x*}Rp_{C*}p_C^!i_x^!\mathcal K_X(W)\\
 &\xrightarrow{\operatorname{Tr}_{p_C}}
 i_{x*}i_x^!\mathcal K_X(W)
 \xrightarrow{\rm counit}\mathcal K_X(W).               \tag{9.42p}
\end{aligned}
$$

Here Book 20's deformation-to-the-normal-cone construction identifies $c_C$ with the refined
excess specialization of (9.42m).  If $x$ lies on a smooth target stratum on which
$\mathcal K_X(W)$ is lisse, then
$i_x^!=i_x^*(-1)[-2]$ and $p_C^!=p_C^*(1)[2]$; these codimension and relative-dimension
shifts cancel inside (9.42o).  The remaining degree-zero coefficient is the localized excess
intersection multiplicity, not the set-theoretic number of sheets.  If $x$ is a node or the
coefficient is not lisse on that stratum, (9.42o) itself is retained and the costalk is
computed through the normalization--conductor complex; no constant-sheaf purity is inserted.
Any constant-field
corestriction belongs to the relevant proper counit, while any scheme length or inseparable
factor belongs to the coefficient exchange and refined orientation in $c_C$; none is supplied
by an untwisted proper trace.

Two regular dominations admit a third dominating both.  On that third domination, transitivity
of lci fundamental classes, proper nearby-cycle comparison, and the projection formula identify
the two proper pushforwards with the specialization of the same generic correspondence.  Thus
their induced maps are identical; this is not an inference from equality of generic point sets.
Every construction in (9.42n) is
defined over the residue field, so it commutes with residue Frobenius.  A retained
prime-to-$v$ Hecke route commutes with the generic level transport; proper base change and the
projection formula carry this equality to (9.42n).  Here the comparison is made on the actual
common finite generic algebra and its strict transforms, not from equality of generic point
sets.  The same argument applies to the routed $U_v$ sheets of Proposition 9.4, whose unique
node sheet has expansion one.

Finally Verdier duality changes $\alpha_\eta$ into its inverse dual, exchanges the two
ordinary/extraordinary exchange arrows, and makes the lci fundamental class adjoint to its
trace.  Hence exchanging $f_0,f_1$ gives the adjoint correspondence under the Verdier pairing
between $\mathcal K_X(W)$ and its dual; when a supplied perfect coefficient pairing identifies
$W$ with its dual, this is the asserted adjunction on $\mathcal K_X(W)$ itself.  On the node
complex this is the oriented adjunction in (3.8), including the sign under branch reversal; on contracted
components it is the adjunction between (9.42o) and the counits in (9.42p).  Passing compatibly through
finite coefficient quotients and taking the derived inverse limit proves the integral
$\Lambda_\ell$ statement; tensoring proves the $E_\ell$ statement. $\square$

Consequently the general principal-node target is no longer conditional on a separate
$({\rm RGC}_v)$ assertion.  For arbitrary representations its remaining inputs are the
arithmetic cover and completed-tube normalization isolated after Proposition 9.7.  The
actual-row specialization is proved below.

**General local target $({\rm PNS}_v)_{\rm gen}$ (principal node and stabilizer theorem).** Let

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
   term of clause 2.  The typed proper direct image (9.39) from a regular domination then
   supplies its full branch contribution.  The resulting node-to-branch generization chain maps are
   identified; no branch with uncomputed monodromy is replaced by an underived module;
2. for each oriented flag incidence contributing to an extreme residue, exactly one
   stabilizer-quotient sheet, of scheme-theoretic multiplicity one, is node-to-node.  Every
   other generic flag sheet is assigned, with its scheme-theoretic multiplicity and
   decomposition action, to the stated normalization-component stratum. This routing is
   compatible with every retained residue-prime Hecke leg treated by the graph/regular-
   domination construction of Section 9.3, including its transpose. On the identified
   node-to-node sheets lying over the finite parahoric base legs, Proposition 9.2 then proves,
   rather than assumes, expansion index one.

Proposition 9.4 proves the sheet classification, common-factor routing, multiplicity one and
expansion one.  Proposition 9.5 proves the raw invariant branch fields, Cartier multiplicities
and active group filtrations, and reduces each arithmetic normalized compositum to
(9.36a)--(9.37b).  Proposition 9.6 computes every completed conductor factor, residue
extension, Frobenius orbit and monomial blowup transform from the actual endpoint valuation
and $\delta_{H\lambda,j,\mathfrak q_j}$, and computes the true intersection from the two actual
tame subgroups.  Proposition 9.7 gives the exact tube definition of the branch, conductor and
generization complexes.  What is still imported in clause 1 is both the selected
spectator/ray cover and the completed two-dimensional normalization theorem for its branch
tubes, namely $({\rm BTK}^{\rm gen}_{H,\lambda,j,\alpha,\mathfrak q_j,\beta,e})$ for every selected factor.  Proposition
9.8 proves $({\rm RGC}_v)$, including component-routed and contracted
terms, transpose, and compatibility with (9.39).  Clause 2 has no remaining
cohomological-correspondence input.

This is an exact finite-level general target.  Its remaining arithmetic branch datum can be
supplied only by naming the actual spectator/ray field and evaluating its global unit and tame
character.  Its remaining geometric datum is the completed two-dimensional normalization and
map of Milnor tubes required in $({\rm BTK}^{\rm gen}_{H,\lambda,j,\alpha,\mathfrak q_j,\beta,e})$.  The active Drinfeld
contribution and every resolution recurrence are already fixed by Propositions 9.5--9.6.  The orientation (9.41) is
supplied independently by Proposition 9.8; complete local rings alone would not have supplied
it.

For the displayed finite algebra it is enough to work after completed strict henselization.  All modules
in question are finite, completion is faithfully flat, and equality of two finite subalgebras
together with the decomposition action is reflected by that completion.  This is completion of
the already constructed proper normalization, where Book 58 applies.  It is not an invocation of formal
GAGA to manufacture an algebraic tower from one isolated formal node.  If one instead starts
from an abstract Drinfeld formal moduli space, algebraizing it requires the compatible proper
polarized global datum of Book 58; a complete local equation alone does not supply that datum.

Once $({\rm PNS}_v)_{\rm gen}$ is known, no further ramified nearby-cycle theorem is missing
for an arbitrary representation.  For a
finite-free representation $W$ of the principal quotient, the decomposition group in clause 1
first gives its actual wild subgroup $P_x$.  Take the exact invariants $W^{P_x}$ of Book 22,
(3.12)--(3.13); this is not a claim that the cover is tame.  Let $H_x$ be the prime-to-$\ell$
kernel in the remaining tame group, put $M_x=(W^{P_x})^{H_x}$, and write $T_x$ for the
remaining pro-$\ell$ generator.  Book 22, (3.14), then gives the
full complex

$$
[M_x\xrightarrow{T_x-1}M_x]                               \tag{9.43}
$$

with the residue-Galois action (3.6).  Combining it with the branch complexes and
generization maps gives the normalization--conductor homotopy fiber (3.10).  Clause 2 and
(3.8) make both unsigned extreme expansion coefficients equal to $1$; the only signs are those
from the chosen oriented endpoint difference. They place all remaining sheets in the middle
normalization term. The same formulas make
finite-flat trace adjoint to pull on the contragredient representation and commute with every
retained Hecke route.  Proposition 9.3 proves the level-one ring assertion $({\rm DLB}_1)$.
Equations (9.29k)--(9.29l) prove the active normalization and intermediate invariant rings at
every finite depth, while (9.29r)--(9.29x) prove the full-level higher branch, inertia,
residue-degree, node-annular, and boundary-stabilizer ledger.  Proposition 9.5 adds the exact
wild invariant-ring residue field, Cartier multiplicity and the normalized-compositum
factorization rule.  Proposition 9.6 turns the actual endpoint valuations, leading constants,
and tame subgroups into completed Kummer factors and intersection groups.  Proposition 9.7 gives the exact
Milnor-tube construction of the conductor/generization complexes and identifies the remaining
two-dimensional local normalization theorem; Proposition 9.8 supplies the oriented component
correspondence.  Proposition 9.4 supplies the residue-prime routing and unit node coefficients.
In particular, the principal cover is genuinely wild even though its selected extreme
invariant lines are tame.

The preceding target is deliberately more general than the coefficient systems which use this
book.  An arbitrary intermediate quotient and an arbitrary cyclic ramified trait can indeed
require the unsolved factorwise calculation just stated.  The quotient and augmentation rows
of Books 138 and 174 have three additional properties: they factor through $G_1$, every
prime-to-$v$ spectator cover is etale over the integral model, and the scalar character is a
pullback from the trait.  These properties remove the arbitrary $H$ and arbitrary Kummer
data.  We now perform that calculation.  It is important that the reduction below is made on
the **generic coefficient sheaf before nearby cycles**.  It does not commute wild invariants
with reduction of $D_n$, which (9.29t) shows would be false.

Put

$$
e_v=\ell^{\operatorname{ord}_\ell(q-1)}.                  \tag{9.44}
$$

When $e_v=1$ there is no scalar ray factor.  Otherwise $\ell$ is odd in the downstream
scalar range, $\mu_{e_v}\subset R$ by Teichmuller lifting, and $e_v\mid q-1$.

**Proposition 9.9 $({\rm KBL}_v)_{\rm act}$ (strict ray choice and its endpoint
Kummer factors).**  Let $K_0$ be the number field over which the chosen canonical Shimura
curve and determinant character are defined, let $v$ be a finite place of $K_0$, and suppose
$R=\mathcal O_{K_0,v}^{\mathrm h}$ and $\ell$ is odd.  Fix a finite protected set $S_0$ of
places of $K_0$ containing $v$, the places above $\ell$, and every already fixed ramified
place.  There is a finite-order global character

$$
c_v:G_{K_0}\longrightarrow \Delta_v=C_{e_v}              \tag{9.45}
$$

which is trivial at $S_0\setminus\{v\}$ and whose localization at $v$, under local
reciprocity, is

$$
K_{0,v}^\times\longrightarrow k_v^\times
 \longrightarrow k_v^\times/(k_v^\times)^{e_v}
 \simeq C_{e_v};                                         \tag{9.46}
$$

the first arrow is reduction on units and sends the chosen uniformizer to $1$.  Its order is
exactly $e_v$.  If $\mathfrak f(c_v)$ is its conductor, then $\Delta_v$ is an effective
quotient of $\operatorname{Cl}_{\mathfrak f(c_v)}(K_0)$, including the global-unit and real-sign
relations, and local inertia at $v$ maps isomorphically to $\Delta_v$.  Any additional finite
places in $\mathfrak f(c_v)$ are retained as fixed spectator levels and all later auxiliary
sets are chosen disjoint from them.  The completed local field and the henselian integral
extension at $v$ are

$$
K_{0,v}'=K_{0,v}(\varpi),\qquad \varpi^{e_v}=\pi,\qquad
R_v'=R[\varpi].                                           \tag{9.47}
$$

Thus the arithmetic unit denoted $v$ in (9.36) is actually $1$, not an unnamed unit.
Let $A(c_v)$ be the tautological rank-one $\mathcal O[\Delta_v]$-system on
$\operatorname{Spec}K_0$ attached to (9.45).  The character
$\boldsymbol\chi_v^{\rm aut}\circ\det$ is trivial on the derived norm-one group, so its
descent line factors through the finite abelian component label.  With the fixed Artin
convention, Book 120, Theorem 6.1 identifies Galois translation on that label with canonical
reciprocity; evaluation by the idele-class character corresponding to (9.45) is exactly
$c_v$.  Hence the automorphic descent line is the pullback of $A(c_v)$ to the generic Shimura
curve.  Consequently its extension at $v$ is the
trait pullback of $A(c_v)$ used in (9.29) and (9.60); this geometric identification is a
consequence of the strict global character, not an additional ray hypothesis.

At the level-one branch $L=k_ve_1$, take
$\tau=z_{e_1}$ and $\xi=z_{e_2}$.  Write
$[\pi]_G(Z)=U_G(Z)W_G(Z)$ for Weierstrass preparation in the chosen arithmetic Drinfeld
coordinate, with $W_G$ monic, and put

$$
\gamma_L=\overline{U_G(0)}\in k_L^\times.                 \tag{9.47a}
$$

Here $k_L$ is the actual residue field of the endpoint; after a deformation-etale spectator
extension, $\gamma_L$ is carried to that residue field.  Its class modulo $e_v$th powers is
intrinsic.  Indeed, rescaling the branch parameter changes the leading coefficient by a
$(q-1)$st power, and rescaling the endpoint parameter changes it by a $q(q-1)$st power;
both are $e_v$th powers.  A change of arithmetic Drinfeld coordinate induces these two
parameter changes.  Thus the factor degrees and intersection field below do not depend on
the displayed coordinate.  The Drinfeld divisor identity gives

$$
\pi=\tau^{q-1}u_L(\tau,\xi),\qquad
\overline{u_L}=\xi^{q(q-1)}\varepsilon_L(\xi),\qquad
\varepsilon_L(0)=\gamma_L.                               \tag{9.48}
$$

Consequently the endpoint valuation and leading coefficient of (9.42a)--(9.42c) are

$$
m=q-1,\qquad d=q(q-1),\qquad \delta=\gamma_L.            \tag{9.49}
$$

After blowing up the closed Drinfeld point, the chart containing the strict transform of
$L$ is

$$
\pi=x^{q-1}y^{q^2-1}\varepsilon_1(x,y),
\qquad \varepsilon_1(0,0)=\gamma_L.                      \tag{9.50}
$$

On the strict-transform side
$(m,d,\delta)=(q-1,q^2-1,\gamma_L)$; on the exceptional side it is
$(q^2-1,q-1,\gamma_L)$.  Every subsequent toroidal blowup replaces an ordered pair $(a,b)$ by
$(a+b,b)$ or $(a,a+b)$ and carries the displayed unit to its value $\gamma_e$ at the new
endpoint.  Thus the resulting leading coefficient is computed by evaluation, not suppressed;
all multiplicities and endpoint orders remain divisible by $e_v$.  At such a later endpoint,
replace $\gamma_L$ by $\gamma_e$ in (9.51)--(9.52b).

For a deformation-etale spectator residue factor $k_j/k_L$, let $\gamma_j$ be the image of
$\gamma_L$ and put

$$
h_j=\operatorname{ord}\!\left(
 [\gamma_j]\in k_j^\times/(k_j^\times)^{e_v}\right).
                                                               \tag{9.51}
$$

Then $h_j\mid e_v$, and the completed constant polynomial of Proposition 9.6 has the exact
factorization pattern

$$
Z^{e_v}-\gamma_j^{-1}
 =\prod_{\beta=1}^{e_v/h_j}G_{j,\beta}(Z),\qquad
\deg G_{j,\beta}=h_j.                                    \tag{9.52}
$$

Over $\bar k$ this is
$\prod_{\zeta\in\mu_{e_v}}(Z-\zeta\gamma_j^{-1/e_v})$.
Each arithmetic factor is the unramified constant extension
$k_{j,\beta}/k_j$ of degree $h_j$ and has no additional vertical ramification, because
$e_v$ divides the endpoint order.  At a chart
$\pi=\epsilon x^ay^b$ occurring above, write
$\epsilon=\widetilde\gamma_j h_0^{e_v}$ after this unramified extension.  Its normalized
factor is the original regular completed ring over that constant extension.  If the selected
root of $G_{j,\beta}$ is $z_\beta$, choose $\rho_\beta$ lifting $z_\beta^{-1}$, and let
$R'_{j,\beta}$ be the resulting unramified constant extension of $R_v'$.  Then

$$
\widehat B_{j,\beta}\simeq
R'_{j,\beta}[[x,y]]/
 (\varpi-\rho_\beta h_0x^{a/e_v}y^{b/e_v}),
\qquad \rho_\beta^{e_v}=\widetilde\gamma_j.              \tag{9.52a}
$$

The map to the original completed chart fixes $x,y$, sends $\pi$ to $\varpi^{e_v}$, and is
compatible with the displayed relation because
$\rho_\beta^{e_v}h_0^{e_v}=\epsilon$.  Thus (9.52a) records the actual monomial map of
Milnor tubes as well as the abstract normalized ring.

If $K_j$ is the corresponding unramified spectator field and
$\varpi^{e_v}=\pi$, the active/ray intersection is

$$
E_{L,j,\beta}=K_j(\varpi^{h_j}),\qquad
[E_{L,j,\beta}:K_j]=e_v/h_j.                             \tag{9.52b}
$$

Thus the compatible-pair group is a fiber product over $C_{e_v/h_j}$.  It is diagonal over
the full $C_{e_v}$ exactly when $[\gamma_j]=1$, and it is a direct product exactly when
$h_j=e_v$.  The geometric roots split into arithmetic-Frobenius orbits of length $h_j$;
each orbit is one factor $G_{j,\beta}$, and Frobenius acts cyclically inside its corresponding
constant field.  Any larger retained residue-Galois action transports these labeled factors
in the evident way.  Equations (9.48)--(9.52b) are the complete Kummer branch ledger for
the scalar ray and spectator data used downstream.

**Proof.**  Prescribe (9.46) at $v$ and the zero class at the places in
$S_0\setminus\{v\}$.  Its local order is the odd integer $e_v$.  Book 6, Theorem 6.1 and the
non-Wang alternative immediately following it globalize this tuple to (9.45); the global order
is $e_v$ because the localization
at $v$ already has that order.  Factoring through the ray class group of its conductor gives
all unit, sign, and central compatibilities rather than assuming them.  Book 120's canonical
component reciprocity gives the determinant/trait identification stated after (9.47).  Local Kummer theory,
$\mu_{e_v}\subset K_{0,v}$, and the condition that the uniformizer have trivial unramified value
give (9.47).

For (9.47a)--(9.48), divide the Drinfeld Weierstrass polynomial by its zero root and evaluate
its constant coefficient.  On $\tau=0$ one has
$z_{(a,b)}=[\widetilde b]_G(\xi)$ for $b\ne0$.  The factors on $L$ have leading coefficients
$a\in k_v^\times$, and the other factors have leading coefficients $b$, repeated $q$ times.
Since $\prod_{a\in k_v^\times}a=-1$, the root factors contribute
$(-1)(-1)^q=1$ (also in characteristic two); the remaining coefficient is precisely
$\overline{U_G(0)}=\gamma_L$.  There are $q-1$ factors on $L$ and
$q(q-1)$ off it, proving (9.48)--(9.49).  Substitution $\tau=xy$, $\xi=y$ gives (9.50).
The blowup recurrence is the one proved in Proposition 9.6.

Now $e_v$ divides both exponents in (9.50), and it continues to divide their sums.  Because
$e_v$ is prime to $p$, Hensel's lemma extracts the principal-unit root.  Since
$\mu_{e_v}\subset k_j$, elementary Kummer theory over the finite cyclic group $k_j^\times$
shows that $Z^{e_v}-\gamma_j^{-1}$ has $e_v/h_j$ factors of degree $h_j$, proving
(9.52).  On the factor selected by $z_\beta$, the base-changed binomial has the linear
relation in (9.52a).  Its maximal ideal is generated by $x,y$, so the two-dimensional ring is
regular and hence normal; this proves that it is the completed normalization factor, not just
a finite birational model.  More explicitly, at the endpoint write
$u=\widetilde\gamma_j\xi^d h^{e_v}$.  Since $e_v$ divides both $m$ and $d$, the element
$\tau^{m/e_v}\xi^{d/e_v}h$ in the active branch field has $e_v$th power
$\pi/\widetilde\gamma_j$.  The ray field contains an $e_v$th root of $\pi$.  Their
Kummer classes span the valuation class $[\pi]$ and the unit class $[\gamma_j]$, a group of
order $e_vh_j$.  The compositum/intersection degree formula therefore gives intersection
degree $e_v/h_j$.  If $b^{e_v}=\widetilde\gamma_j^{h_j}$ and
$\alpha^{e_v}=\pi/\widetilde\gamma_j$, then
$(b\alpha^{h_j})^{e_v}=\pi^{h_j}$; after a root-of-unity adjustment this is
$\varpi^{h_j}$.  Thus $K_j(\varpi^{h_j})$ lies in both fields and already has the computed
degree, proving that it is the exact intersection in (9.52b).  This uses the actual leading unit and the actual
local character; the gcd alone cannot distinguish the diagonal, intermediate, and product
cases.  Finally the deeper active kernel $\ker(G_n\to G_1)$ has $p$-power order, whereas the
ray extension has $\ell$-power degree.  It is therefore linearly disjoint from the ray over
each level-one factor, so (9.52b) is also the active/ray intersection in the actual deeper
common cover; the higher wild and inseparable residue data remain those of
(9.29r)--(9.29x).
$\square$

We next compute the tubes.  Let

$$
E_L^P=\mathcal Oe_L\oplus\mathcal Os_L,\quad
E_L^+=\mathcal O(e_L\bmod\mathbf1),\quad
E_L^-=\mathcal O(e_L-q^{-1}s_L),                           \tag{9.53}
$$

and for $W=P,\operatorname{St}_v^+,\operatorname{St}_v^-$ write $E_L(W)$ for the
corresponding module in (9.53).  Thus $E_L(W)=W^{U_L}$.  Let $S$ be any finite-free
spectator module whose cover is etale at $v$, including the auxiliary diamond factors, and let
$A(\boldsymbol\chi_v)$ denote the trait-pulled tautological ray line, omitted when $e_v=1$.

**Proposition 9.10 $({\rm BTK}_v)_{\rm act}$ (completed tubes for the actual
coefficient rows).**  For

$$
\mathscr W=W\otimes_{\mathcal O}S\otimes_{\mathcal O}
 A(\boldsymbol\chi_v),qquad
W\in\{P,\operatorname{St}_v^+,\operatorname{St}_v^-\},   \tag{9.54}
$$

the completed level-one active/ray factors are the normalized rings (9.52a).  After
equivariant finite pushforward from the actual common normalization and associated-sheaf
descent, every oriented base-node orbit has the following Milnor-tube complex.  At the node
oriented from the $L$-endpoint to a complementary endpoint $M$,

$$
K_L(\mathscr W)=
\left[E_L(W)\otimes S\otimes A(\boldsymbol\chi_v)
 \xrightarrow{\,0\,}
E_L(W)\otimes S\otimes A(\boldsymbol\chi_v)\right]        \tag{9.55}
$$

in degrees zero and one.  The two conductor fibers are

$$
C_L(\mathscr W)=
 E_L(W)\otimes S\otimes A(\boldsymbol\chi_v)[0],qquad
C_M(\mathscr W)=
 W\otimes S\otimes A(\boldsymbol\chi_v)[0].              \tag{9.56}
$$

The oriented generization maps are

$$
g_L=(\operatorname{id},0),qquad
g_M=(E_L(W)\hookrightarrow W,0).                          \tag{9.57}
$$

Every smooth branch contribution after this equivariant pushforward has cohomology only in
degree zero with its actual stabilizer module.  In particular, for either Steinberg row the
splitting (9.29q) gives

$$
\mathcal C_{\rm moving}(W)=E_L(W)[0]\oplus Q_L[0],qquad
K_L(Q_L)=0,                                               \tag{9.58}
$$

and the $Q_L[0]$ term is retained in the normalization-component direct image.  It is not
deleted and is not replaced by a second procyclic complex.

On (9.55), the finite wild image has already been taken by exact $U_L$-invariants, and the
remaining diagonal tame quotient and geometric pro-$\ell$ annular generator act trivially on
$E_L(W)$; the trait-pulled ray inertia is the displayed external diagonal action.  Reversing
the annular orientation multiplies the degree-one identification by $-1$, as in Book 22,
(3.8).

Arithmetic residue Frobenius acts on the degree-zero term of (9.55) by its
stabilizer/spectator action and on the degree-one term by $q^{-1}$ times that action; geometric
residue Frobenius has the inverse factor $q$.  The ray character acts diagonally on both.  On
(9.56)--(9.58) Frobenius acts by the actual permutation/stabilizer action, again tensored
diagonally with the ray character.  These formulas are transported among the complementary
branches and are equivariant for the transpose and every retained Hecke route.

**Proof.**  First remove two apparent complications at the level where they are harmless.
If the common active cover lies in $D_n$, its deeper kernel
$N_n=\ker(G_n\to G_1)$ is a $p$-group and acts trivially on every $W$ in (9.54).  On the
generic fiber, transitivity of associated-sheaf descent gives a canonical identity

$$
(D_n\times W)/G_n\simeq(D_1\times W)/G_1.                 \tag{9.59}
$$

For a determinant- or component-fixed datum, replace both groups by their effective
subgroups and $G_1$ by the image of the upper group; the same kernel quotient proves (9.59).
Thus the generic lisse sheaf, and hence its nearby cycles on the base, may be computed with
$D_1$.  This is an identity after associated descent; it is not a factorwise isomorphism
between the completed raw $D_n$-normalization and $D_1$.
Equation (9.59) is formed before reduction or nearby cycles; it does not assert
$(D_n/N_n)_{\rm red}=D_n{}_{\rm red}/N_n$.  Therefore the purely inseparable discrepancy in
(9.29t) is retained in the proper map and in Proposition 9.8, not incorrectly set equal to
one.  Similarly, a spectator cover etale at $v$ is a disjoint union after strict localization,
so it contributes the constant factor $S$ with its descent action.  Finally Book 22, (3.11),
applied to the globally identified trait pullback gives

$$
R\Psi(\mathcal K\otimes A(\boldsymbol\chi_v))
 =R\Psi(\mathcal K)\otimes A(\boldsymbol\chi_v).          \tag{9.60}
$$

Thus no arbitrary normalized ray compositum is used to compute the coefficient stalk.

It remains to calculate $D_1$.  Blow up its closed point.  Formula (9.50) gives normal
crossings support with multiplicities $q-1$ and $q^2-1$.  Use the $e_v$-Kummer alteration of
the trait.  In the scalar row this is the actual ray base of Proposition 9.9; in the untwisted
row it is only an auxiliary alteration used to identify the geometric tube and is not added to
the coefficient datum.  Proposition 9.9 identifies every completed scalar-ray factor by
(9.52)--(9.52a), with its unramified constant field and Frobenius orbit retained.

Now take one finite tame Kummer alteration which clears the remaining Cartier
multiplicities, and perform the equivariant toroidal normalization and chain resolution of
Section 5.3.  Its degree is prime to $p$, but it need not be prime to $\ell$: when
$q\equiv-1\pmod\ell$, the $\ell$-part of $q+1$ occurs in $q^2-1$ although $e_v=1$.
This one-sided $\ell$-part is not a scalar ray and is not averaged.  Instead, split tame
monodromy into its finite prime-to-$\ell$ kernel and its geometric pro-$\ell$ quotient.  Average
only over the former.  The finite alteration is used to identify the original geometric tube;
one then computes that tube directly by continuous cohomology of its $\mathbf Z_\ell(1)$
quotient, using Book 22's strict procyclic complex.  No derived invariants of a finite
$\ell$-group are substituted for this calculation.  The
remaining geometric tame action on $E_L(W)$ is trivial, so this still gives the zero
differential in (9.55).  This treats the generic, scalar, and
$q\equiv-1\pmod\ell$ rows uniformly; it does not smuggle a $q+1$ ray into the vexing row.

Over the strict henselian completion the saturated toric charts give discs at the conductor
sides and an annular Milnor tube connecting the two oriented ends.  The exceptional chain
subdivides its skeleton; it does not assert that the two strict-transform components meet
directly, and its proper component contribution is retained in Proposition 9.8.  No
nonunit-order alteration group, including the $e_v$-alteration or a possibly $\ell$-power
unramified constant extension in (9.52), is averaged.  In the scalar row the actual ray
descent is the regular ray/Shapiro descent already identified with (9.60).  All auxiliary
$\ell$-primary monodromy is retained in that continuous geometric pro-$\ell$ quotient.  Finite
pushforward is taken over every auxiliary toric and constant-field factor, retaining its
permutation module and arithmetic-Frobenius orbit; the factors reassemble into
$A(\boldsymbol\chi_v)$ in the scalar row and into the original coefficient module in the
untwisted row.  Thus no arithmetic conclusion depends on selecting one auxiliary factor.
At a smooth branch
point the transverse equation is $\pi=u\tau^m$; over the geometric generic point it is a
finite set of discs, so its cohomology is the actual stabilizer permutation module in degree
zero and has no positive degree.  At the crossing the strict alteration gives the annular
two-term procyclic complex.

The actual wild image at the node is $U_L$ by (9.29d), and its invariants are exactly (9.53)
by (9.29g)--(9.29h).  The remaining diagonal tame quotient fixes every module in (9.53), so
the procyclic differential is zero.  At the fixed conductor side the boundary module is
$W^{U_L}=E_L(W)$; at the moving side $A^1_{1,L}=1$ in (9.29v), so it is $W$.  Specialization
of discs into the oriented annulus gives identity on the first module and the stabilizer
inclusion on the second, in degree zero, and zero from the independent annular degree one.
This proves (9.55)--(9.57).  Exactness of $U_L$-invariants and (9.29q) prove (9.58).
Formula (3.6) of Book 22 gives the factor $q^{-1}$ in node degree one; (9.60) gives the
diagonal ray action.  Equivariance follows from Proposition 9.4 and functoriality of all three
reductions. $\square$

**Corollary 9.11 $({\rm HDB}_v)_{\rm act}$ and $({\rm PNS}_v)_{\rm act}$.**
For the quotient, augmentation, and permutation rows (9.54), with all prime-to-$v$
spectators and with the strict global ray datum of Proposition 9.9 when a scalar twist is
present, the higher Drinfeld branch-complex descent and the principal node and stabilizer
theorem hold.  The complete normalization--conductor complex is (9.39) with (9.55)--(9.58).
Its unique node-to-node flag sheet has multiplicity and both expansion indices one; all other
sheets occur with their actual stabilizer action in the component term.  Pull and trace are
the expansion-one maps of Book 22, (3.8), and the full proper component operator, including
radicial degrees and contracted components, is Proposition 9.8.  The transpose is adjoint and
all maps commute with residue Frobenius, the ray action, and retained Hecke routes.

**Proof.**  Proposition 9.2 gives the actual common normalization and identifies the finite
top legs.  Proposition 9.4 supplies the sheet routing, multiplicity and expansion one.
Proposition 9.10 supplies every branch and conductor complex and both generization maps, so
Book 22, (3.10), gives (9.39) without a missing term.  Proposition 9.8 supplies the oriented
restriction--Gysin correspondence on that same homotopy fiber.  These are precisely clauses
1--2 of $({\rm PNS}_v)_{\rm act}$ for the representations (9.54). $\square$

The superscript ``act'' is essential.  Propositions 9.9--9.10 do not prove the earlier
factorwise $({\rm BTK}^{\rm gen}_{H,\lambda,j,\alpha,\mathfrak q_j,\beta,e})$ for an arbitrary
intermediate representation or an arbitrary cyclic trait.  Such data are not used in Books
138 or 174--176.  For their actual rows, however, $({\rm KBL}_v)$,
$({\rm BTK}_v)$, $({\rm HDB}_v)$, and $({\rm PNS}_v)$ are now the proved assertions above,
not hypotheses.

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
    common factor.  Proposition 9.5 computes the reduced invariant branch fields, Cartier
    multiplicities and group filtrations, and reduces every normalized spectator/ray
    compositum to the factorization (9.36b) over its actual residue-compositum field.
    Proposition 9.6 computes each completed endpoint and blowup factor from its valuation and
    one constant-field unit, computes the intersection from the actual tame subgroups, and proves
    that gcd data alone do not determine them.  Proposition 9.7 gives the exact
    conductor/generization construction from the actual Milnor tubes, while Proposition 9.8
    proves the oriented restriction--Gysin correspondence on noncontracted and contracted
    sources.  Proposition 9.9 constructs the strict global ray quotient used by the scalar
    rows, fixes its local field and unit, and factors every actual endpoint polynomial.
    Proposition 9.10 uses the normalized level-one factors to compute the equivariantly
    descended tube cohomology, actions, and generization maps after the valid generic-sheaf
    reduction to level one.  Corollary
    9.11 proves $({\rm KBL}_v)_{\rm act}$, $({\rm BTK}_v)_{\rm act}$,
    $({\rm HDB}_v)_{\rm act}$, and $({\rm PNS}_v)_{\rm act}$ for the permutation, quotient,
    and augmentation rows with their actual spectator/ray factors.  The general factorwise
    $({\rm BTK}^{\rm gen}_{H,\lambda,j,\alpha,\mathfrak q_j,\beta,e})$ remains a boundary only for an
    arbitrary intermediate representation or arbitrary cyclic ray data, neither of which is
    used by those rows.

**Proof.** The dyadic vertex construction, Proposition 2.1, Theorem 2.2, and
Proposition 2.3 prove projective representability and transfer the exact integral local
model over arbitrary test rings. Proposition 3.1 and Theorem 4.1 prove statements 1--2,
including the chart $xy=2$ in the dyadic case. Lemma 4.2, the reassembled subgroup
construction, and Theorem 4.3 prove statement 3. Sections 4.4 and 7.1--7.2 prove
statement 4. Chapter 5 proves statement 5. The graph nearby-cycle calculation in
Chapter 6 proves statement 6. Chapter 8 proves statements 7--8. Naturality of
prime-to-$p$ isogenies and functoriality of nearby cycles prove statement 9.
Sections 9.3--9.4 prove statement 10, Section 9.2 proves statement 11, and
Theorem 9.1 proves statement 12.  Propositions 9.2--9.10 and Corollary 9.11 prove statement
13 and its stated arbitrary-data boundary. $\square$

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
inertia, residue-degree, node-annular, and boundary-stabilizer ledger.  Proposition 9.5
computes the reduced invariant branch fields, Cartier multiplicities and active groups.  Its
normalized-compositum formula is factored at every conductor point by Proposition 9.6 once the
endpoint valuation and leading coefficient are supplied.  For the actual coefficient rows,
Proposition 9.9 supplies those entries: the ray field is
$K_v(\pi^{1/e_v})$, its vertical unit is $1$, the raw endpoint is
$(m,d,\delta)=(q-1,q(q-1),\gamma_L)$, and the blown-up endpoints are
$(q-1,q^2-1,\gamma_L)$ and $(q^2-1,q-1,\gamma_L)$.  If $h$ is the order
of $[\gamma_L]$, the endpoint polynomial has $e_v/h$ factors of degree $h$ and the
active/ray intersection has degree $e_v/h$.  Proposition 9.10 then proves the completed tube theorem
and its generization maps, and Corollary 9.11 proves $({\rm PNS}_v)_{\rm act}$.  The
arbitrary-intermediate factorwise
$({\rm BTK}^{\rm gen}_{H,\lambda,j,\alpha,\mathfrak q_j,\beta,e})$ is not asserted, but it is not an
input to the downstream quotient/augmentation rows.
The proper direct image (9.39) is still not an untwisted trace; Proposition 9.8
uses the generic lci orientation and its excess specialization to construct the component
restriction--Gysin correspondence.  Proposition 9.4 fixes the actual common-factor
strict-transform routing and node multiplicities.  Thus $({\rm PNS}_v)_{\rm gen}$ remains
conditional if one replaces the actual rows by an unspecified intermediate representation or
replaces (9.45)--(9.47) by a nominal cyclic ray group.  The rows used in Books 138 and
174--176 satisfy Corollary 9.11 and are unconditional once their strict global ray choice is
made.  The ray projection formula applies because Proposition 9.9 supplies an effective
global character and hence identifies the automorphic system with the component/trait
pullback; it is not being applied to a merely local character.

The equality $\operatorname{rank}N=b_1(\Gamma)$ is rational. Integral cokernels use the thickness matrix and saturation of the chosen lattice. A rational Hecke projector with an $\ell$-denominator does not select a canonical integral lattice. The packet theorem is likewise in characteristic zero and concerns the raw curve carrier; it is not an integral Ihara statement and is not a raw-to-global theorem. The geometric degeneracy complex remains input to any Ihara lemma or level-raising theorem, not a proof of either.

### 10.3 The non-common-norm dyadic source

There is nevertheless an exact dyadic parahoric curve on the unitary side. Let $F$ be totally
real with $[F:\mathbf Q]>1$, let $B/F$ be division and split at exactly one real place, assume
that $2$ splits completely in $F$ and
that $B$ is split at every dyadic place, and choose an imaginary quadratic field $K$ split at
$2$ such that $L=FK$ embeds in $B$. Retain the unitary common-multiplier datum of Book 118,
Proposition 8.3,

$$
\mathscr D^{\mathrm u}=(L,c,B,\psi,h^{\mathrm u}),
\qquad
\psi(x,y)=\operatorname{Tr}_{L/\mathbf Q}(\xi H(x,y)),
\qquad
H(x,x)=\operatorname{Nrd}_B(x).                         \tag{10.1}
$$

This datum is PEL-exact and its derived group is
$\operatorname{Res}_{F/\mathbf Q}B^1$; it is not the obstructed common-norm group. Fix a
dyadic place $u$ of its reflex field and put $R=\mathcal O_{L,u}^{\mathrm h}$. Thus
$R\simeq\mathbf Z_2^{\mathrm h}$.

**Proposition 10.2 (split dyadic unitary parahoric source).** One may choose $\xi$, an
$\mathcal O_L$-stable lattice $\Lambda^{\mathrm u}\subset B$, a $c$-dual one-step periodic
lattice chain at $u$, a prime-to-two polarization, a decomposition-stable full component
union, and neat prime-to-two fine level so that:

1. the good unitary PEL functor is represented by a smooth projective relative curve
   $\mathscr Y_0/R$ carrying its universal polarized abelian scheme;
2. the oriented parahoric functor is represented by a projective flat curve
   $\mathscr Y_I/R$ carrying the universal isogeny and both chain polarizations;
3. its framed local model is exactly the incidence scheme (3.1), its completed singular
   chart is $xy=2$, and its two special-fiber branches are the relative-Frobenius and
   inverse-twist Verschiebung branches with reduced Hasse conductor; and
4. subject to their stated coefficient and packet hypotheses, the graph, nearby-cycle,
   monodromy-pairing, component-group, degeneracy-route, and raw residue-prime correspondence
   calculations of Chapters 3--9 hold for this unitary source, with component and ray
   characters formed through the actual unitary abelianized quotient.

**Proof.** Complete splitting gives

$$
\mathcal O_L\otimes\mathbf Z_2
\simeq
\prod_{i=1}^{[F:\mathbf Q]}(\mathbf Z_2\times\mathbf Z_2),
\qquad c(a,b)=(b,a).                                      \tag{10.2}
$$

At each paired factor, the split algebra $B\otimes_FF_{v_i}\simeq M_2(\mathbf Q_2)$,
viewed as a right $\mathbf Q_2\times\mathbf Q_2$-module, is a plane and its dual. Scale
$\xi$ by an element of $F^\times$, using weak approximation with the required real signs,
so that its dyadic entries are $(1,-1)$ up to units. Choose the two local lattices dually.
On their direct sum the integral alternating form is

$$
\langle(x,\lambda),(y,\mu)\rangle=\mu(x)-\lambda(y),       \tag{10.3}
$$

which is perfect and satisfies $\langle z,z\rangle=0$ over $\mathbf Z_2$. Prescribed local
lattices at finitely many places globalize to an $\mathcal O_L$-stable lattice in $B$.
Self-duality at two makes the polarization degree odd.

At the active determinant label, the Hodge datum is one line in the displayed plane; its
$c$-paired filtration is the annihilator. At every inactive label the determinant
multiplicity forces zero or the whole summand. Put the pair $U_0,U_1$ of (2.2) in the active
plane, its oppositely indexed dual pair in the conjugate factor, and leave the inactive
factors fixed. This gives

$$
\Lambda^{\mathrm u}_0\subset\Lambda^{\mathrm u}_1
\subset2^{-1}\Lambda^{\mathrm u}_0,
\qquad
(\Lambda^{\mathrm u}_i)^\#=\Lambda^{\mathrm u}_{-i}.       \tag{10.4}
$$

The local common-multiplier group is a product of groups
$\operatorname{GL}_2\times\mathbf G_m$ with a common smooth multiplier. Its chain
stabilizer is smooth, and the split idempotents make the determinant and orientation labels
finite etale. Consequently the arbitrary-test-ring calculation of Proposition 2.1 applies
word for word: the only moving equations are
$\alpha L_0\subset L_1$ and $\beta L_1\subset L_0$. The exact PEL centralizer remains
$G^{\mathrm u}$ by Book 118, Proposition 8.3; no common-norm group has entered.

Book 119 represents the exact characteristic-zero unitary PEL functor and identifies its
generic curve, but its integral representability base has $2$ inverted.  Over the present
dyadic base one instead repeats the projective-frame construction at the start of Section 2.1,
now with the split order $\mathcal O_L\otimes\mathbf Z_2$ and the integral tensors just
constructed.  It gives the quasi-projective ambient fine scheme, and one takes the schematic
flat closure of the selected generic component union.  The filtration-lifting argument used
in Proposition 2.3 is characteristic-independent once (10.3) and the arbitrary-test-ring
incidence calculation are known.  For the good vertex it makes that flat closure open and
closed and smooth; for the chain functor it proves the local-model diagram and hence flatness,
regularity, and the node chart for $\mathscr Y_I$. Properness
uses the unitary boundary argument of Book 121: a toric subspace would be a nonzero
$L$-subspace isotropic for $H$, whereas $H(x,x)=\operatorname{Nrd}_B(x)$ is anisotropic
because $B$ is division. Odd auxiliary full level removes the finite descent action, and
flat closure then gives projectivity. Quotienting by the universal isotropic subgroup and
descending the chain polarization are exactly the constructions of Section 2.2.

The remaining arguments use the active height-two group, the incidence chart, the universal
isogeny, and the exact component character. They therefore give the stated branches and all
the geometric identities, with the unitary multiplier replacing the direct reduced-norm
label. In particular, a basic reduced-norm ray character is not silently substituted for the
unitary component character. $\square$

Proposition 10.2 constructs the needed parahoric geometry but does not yet make it the raw
carrier of a packet originally placed on the basic quaternionic curve. That step is a finite
integral comparison, not another local-model calculation. The proposition also begins with an
eligible pair $(B,K)$; it does not assert that a prescribed global ramification problem always
admits such a pair.

### 10.4 The exact comparison boundary

Write $G$ for the basic quaternionic group, $G^{\mathrm u}$ for the group of (10.1), and
$H=G^{\mathrm{ad}}=(G^{\mathrm u})^{\mathrm{ad}}$. Let $K_0$ and $K_I$ be centrally
saturated basic levels whose dyadic factors are respectively hyperspecial and the oriented
one-step Iwahori, and let $K_0^{\mathrm u}$ and $K_I^{\mathrm u}$ be the corresponding
unitary levels of Proposition 10.2.

The missing statement is now exact. One must construct a finite extension $E/L$ unramified
above $u$, choose $w\mid u$, and construct decomposition-stable full component unions, a
smooth proper model $\mathscr X_0$ and a strictly semistable proper model $\mathscr X_I$ of
the selected basic curves over $\mathcal O_{E,w}^{\mathrm h}$, and finite locally free
surjections fitting into both squares

$$
\begin{array}{ccc}
\mathscr Y_I\otimes_R\mathcal O_{E,w}^{\mathrm h}&\xrightarrow{f_I}&\mathscr X_I\\
\downarrow\scriptstyle{\pi_j^{\mathrm u}}&&\downarrow\scriptstyle{\pi_j}\\
\mathscr Y_0\otimes_R\mathcal O_{E,w}^{\mathrm h}&\xrightarrow{f_0}&\mathscr X_0,
\end{array}
\qquad j=0,1,                                                \tag{10.5}
$$

with the following properties.

1. On generic fibers, (10.5) is induced by the connected common adjoint fiber product
   $P=(G^{\mathrm u}\times_HG)^\circ$, not by a rational identification of the two curves.
   Every selected target component is hit. The map of component labels is the map through
   the actual abelianized quotients of $P$, $G^{\mathrm u}$, and $G$. The full union and both
   maps carry effective unramified descent to $R$, including the decomposition action on
   components and oriented branches.
2. The unitary source retains its polarization, fine level, universal isogeny, determinant,
   orientation, and multiplier. Both squares commute with prime-to-two Hecke spans, the
   dyadic residue correspondence, its transpose and central operator, and the two degeneracy
   routes.
3. Above every routed conductor point, the map on completed strict-node rings is, up to
   exchanging the two branches,

   $$
   x\longmapsto ax',\qquad y\longmapsto a^{-1}y',
   \qquad a\in(\mathcal O_{E,w}^{\mathrm h})^\times.        \tag{10.6}
   $$

   Thus both expansion indices and the conductor multiplicity are one, and the
   Frobenius/Verschiebung orientation and its sign are retained.
4. For every selected packet with trivial central character, central saturation changes no
   vector. Pull and trace select the same characteristic-zero packet plane on the unitary
   source, with the good-normalization support and multiplicity-one line used in Theorem 9.1.

This is the first missing theorem for the mixed one-split dyadic raw carrier. Book 118,
Corollary 10.3A proves its generic finite component cover only while the protected set consists
of odd split hyperspecial primes. Its proof uses that the derived central kernel $\mu_2$ is
etale and that the connected adjoint fiber product has a split reductive integral model.
At two, $\mu_2$ is not etale. No cited result constructs the flat integral fiber product,
proves that its component field is unramified, or proves the expansion-one branch statement
(10.6). The first unsupported assertion is therefore the integral extension of the common
adjoint fiber product across the dyadic hyperspecial--Iwahori diagram. Until it is proved,
neither a characteristic-zero finite cover, equality of adjoint groups, nor a rational
Jacquet--Langlands transfer supplies (10.5).

### 10.5 Conditional transfer to the raw carrier

**Proposition 10.3 (conditional unitary carrier transfer).** Assume the comparison statement
of Section 10.4. Let $\Pi$ be a characteristic-zero multiplicity-one packet on the selected
basic component union, with trivial central character and
$\Pi_2=\operatorname{St}\otimes\mu_2$. Then its pullback to $\mathscr Y_I$ has a unique
invariant graph line, $N$ has rank one on its raw two-dimensional plane, and geometric
Frobenius acts on that line by the raw unnormalized dyadic new-line scalar
$u_2=\mu_2(\Phi)$. The intrinsic monodromy line, its sign, the two branch labels, the central
operator, and all retained Hecke and component routes agree with those on the basic packet.

**Proof.** Since $f_I$ is finite locally free in characteristic zero, trace after pullback is
multiplication by $\deg f_I$. Hence pullback is injective on the selected rational packet
plane. The Hecke and component clauses in Section 10.4 make its image stable under every
retained correspondence. Formula (10.6) identifies the oriented edge generator and the two
generization maps without a ramification factor; functoriality of nearby cycles then commutes
with $N$ and geometric Frobenius. Effective unramified descent retains the original
dyadic Frobenius rather than replacing it by a power at $w$. The packet-support clause puts
this image under the hypotheses used in Theorem 9.1. Its proof, applied to the unitary source
through Proposition 10.2, gives the rank-one monodromy, raw scalar, and sign. The commuting
squares (10.5) carry the result through both degeneracy routes and the actual component-label
maps. $\square$

This proposition adds no unconditional raw carrier: its hypothesis is precisely the theorem
missing in Section 10.4. It also adds no Ihara statement and no arbitrary-intermediate
$({\rm BTK}^{\rm gen})$ assertion. The direct results of Propositions 9.2--9.10 and
Corollary 9.11 remain proved, without an added hypothesis, for the permutation, quotient, and
augmentation rows and their actual spectator and ray factors.

There is an important downstream distinction.  The comparison (10.5) is exact and necessary
if one wants to transport the **raw** packet plane, graph line, and node correspondence from
the unitary model back to the basic model.  It is not necessary merely to identify the
resulting globally semisimple packet system.  When $B$ is split at every dyadic factor, the
generic common-adjoint cover of Book 118 already proves characteristic-zero occurrence of the
same packet on the unitary curve.  The intrinsic unitary model of Proposition 10.2 computes
its raw SP pair.  Book 168, Proposition 7.6A then uses $(\mathrm{HT}_1)$ to make that raw
factor semisimple and compares it with the restriction of the basic system by good Frobenius
polynomials.  At a dyadic prime split in the CM field the two local fields are equal, so the
full SP pair transfers without extending (10.5) integrally.

This later bypass does not weaken the hypotheses of Proposition 10.2.  In particular it still
requires $B$ to be split at every dyadic factor.  It therefore removes (10.5) from the
semisimple FLT interface when an all-dyadic-split automorphic carrier exists, but it does not
construct such a carrier in even degree when quaternionic parity can be corrected only by a
dyadic special place.

### 10.6 Conclusion

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
bad-prime Eichler--Shimura data for every direct datum satisfying the stated ledger.

The unitary common-multiplier datum also has an exact split dyadic parahoric source with the
same incidence geometry; Proposition 10.2 constructs it without reviving the impossible
common-norm Hodge lift. What is not yet supplied is the integral finite comparison (10.5),
including its unramified component field and expansion-one branch routing. Proposition 10.3
shows that this single boundary is exactly what remains before the mixed one-split packet can
use the unitary source as its **raw basic-model** signed-special carrier, once an eligible pair
$(B,K)$ has been supplied.  For the downstream semisimple packet system, Book 168's bypass
removes this comparison whenever $B$ is already split at every dyadic factor.  The unresolved
even-degree case is instead the construction of a mixed-dyadic carrier, or a direct special
local--global theorem with the same output.
