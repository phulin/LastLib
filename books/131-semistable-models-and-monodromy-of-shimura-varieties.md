# Semistable Models and Monodromy of Shimura Varieties

## Contents

1. [Bad reduction as controlled geometry](#1-bad-reduction-as-controlled-geometry)
   - [The problem left by good integral models](#11-the-problem-left-by-good-integral-models)
   - [Standing arithmetic and cohomological conventions](#12-standing-arithmetic-and-cohomological-conventions)
   - [The exact scope of the construction](#13-the-exact-scope-of-the-construction)
   - [Prerequisite audit and the selected split place](#14-prerequisite-audit-and-the-selected-split-place)
2. [Parahoric PEL data and bad-prime moduli](#2-parahoric-pel-data-and-bad-prime-moduli)
   - [A periodic lattice chain](#21-a-periodic-lattice-chain)
   - [The moduli problem](#22-the-moduli-problem)
   - [Representability, generic fiber, and properness](#23-representability-generic-fiber-and-properness)
   - [The local-model diagram](#24-the-local-model-diagram)
3. [The rank-two Iwahori local model](#3-the-rank-two-iwahori-local-model)
   - [Incidence of two lines](#31-incidence-of-two-lines)
   - [The nodal chart](#32-the-nodal-chart)
   - [Components and their intersection](#33-components-and-their-intersection)
   - [Thickness and ramified variants](#34-thickness-and-ramified-variants)
4. [The bad quaternionic curve](#4-the-bad-quaternionic-curve)
   - [Construction of the integral curve](#41-construction-of-the-integral-curve)
   - [Regularity and semistability](#42-regularity-and-semistability)
   - [The global component graph](#43-the-global-component-graph)
   - [A two-component calculation](#44-a-two-component-calculation)
5. [A unitary surface with one bad direction](#5-a-unitary-surface-with-one-bad-direction)
   - [Why one direction can degenerate independently](#51-why-one-direction-can-degenerate-independently)
   - [Local equations and regularity](#52-local-equations-and-regularity)
   - [Global surface components](#53-global-surface-components)
   - [Intersection data](#54-intersection-data)
6. [Two bad directions and semistable regularization](#6-two-bad-directions-and-semistable-regularization)
   - [The product-of-nodes singularity](#61-the-product-of-nodes-singularity)
   - [The small resolution](#62-the-small-resolution)
   - [Strict semistability of the resolved charts](#63-strict-semistability-of-the-resolved-charts)
   - [Components, double curves, and triple points](#64-components-double-curves-and-triple-points)
   - [The choice of diagonal](#65-the-choice-of-diagonal)
7. [Base change, alterations, and descent](#7-base-change-alterations-and-descent)
   - [What finite extension changes](#71-what-finite-extension-changes)
   - [Resolving thick curve nodes](#72-resolving-thick-curve-nodes)
   - [Semistable alteration in the present surface charts](#73-semistable-alteration-in-the-present-surface-charts)
   - [Finite descent data](#74-finite-descent-data)
8. [Strata and incidence complexes](#8-strata-and-incidence-complexes)
   - [The ordered strata](#81-the-ordered-strata)
   - [Restriction and Gysin maps](#82-restriction-and-gysin-maps)
   - [The curve graph and the surface dual complex](#83-the-curve-graph-and-the-surface-dual-complex)
   - [A product-incidence calculation](#84-a-product-incidence-calculation)
9. [Nearby cycles on the bad models](#9-nearby-cycles-on-the-bad-models)
   - [Local nearby-cycle stalks](#91-local-nearby-cycle-stalks)
   - [The quaternionic curve complex](#92-the-quaternionic-curve-complex)
   - [The one-direction surface complex](#93-the-one-direction-surface-complex)
   - [The two-direction surface complex](#94-the-two-direction-surface-complex)
   - [Coefficients from PEL geometry](#95-coefficients-from-pel-geometry)
10. [Weight and monodromy filtrations](#10-weight-and-monodromy-filtrations)
    - [The logarithm of inertia](#101-the-logarithm-of-inertia)
    - [Curves: three graded pieces](#102-curves-three-graded-pieces)
    - [Surfaces: five possible graded pieces](#103-surfaces-five-possible-graded-pieces)
    - [The actual surface monodromy maps](#104-the-actual-surface-monodromy-maps)
    - [Integral lattices and saturation](#105-integral-lattices-and-saturation)
11. [Conductor and type for quaternionic curves](#11-conductor-and-type-for-quaternionic-curves)
    - [The conductor formula](#111-the-conductor-formula)
    - [Graph computation at split semistable level](#112-graph-computation-at-split-semistable-level)
    - [Two-dimensional constituents and special type](#113-two-dimensional-constituents-and-special-type)
    - [Finite and nonsplit descent](#114-finite-and-nonsplit-descent)
12. [Conductor and type for unitary surfaces](#12-conductor-and-type-for-unitary-surfaces)
    - [Ranks of $N$ and $N^2$](#121-ranks-of-n-and-n2)
    - [One bad direction](#122-one-bad-direction)
    - [Two bad directions](#123-two-bad-directions)
    - [Jordan blocks, conductor, and Euler factor](#124-jordan-blocks-conductor-and-euler-factor)
    - [The rank-two Hecke constituent](#125-the-rank-two-hecke-constituent)
13. [Hecke correspondences and functorial monodromy](#13-hecke-correspondences-and-functorial-monodromy)
    - [Extension away from the bad prime](#131-extension-away-from-the-bad-prime)
    - [Action on strata and nearby cycles](#132-action-on-strata-and-nearby-cycles)
    - [Projectors and coefficient fields](#133-projectors-and-coefficient-fields)
    - [The local--global compatibility package](#134-the-local--global-compatibility-package)
14. [The semistable bad-prime theorem](#14-the-semistable-bad-prime-theorem)
    - [Unified construction and computation](#141-unified-construction-and-computation)
    - [Scope ledger and failure modes](#142-scope-ledger-and-failure-modes)
    - [Conclusion](#143-conclusion)

## 1. Bad reduction as controlled geometry

### 1.1 The problem left by good integral models

At a hyperspecial prime, the integral PEL moduli space is smooth. Its special fiber therefore has no local memory beyond ordinary specialization, and inertia acts trivially on prime-to-residue-characteristic cohomology. A prime at which the level stabilizes a nontrivial lattice chain is different. The Hodge filtration must move compatibly through that chain. The resulting local model has several components, and their intersections create vanishing cycles.

The theorem turns that failure of smoothness into usable arithmetic. For the
quaternionic curves, the resulting essential singular fiber is nodal and the total space is
regular. For the compact unitary surfaces used in the modèles étranges construction, one or two
rank-two directions can be parahoric. One bad direction gives a regular strict
normal-crossings model. Two bad directions first give a product of nodes whose total space is
singular; an explicit small modification replaces that *local model* by strict semistable
charts. The comparison with the selected PEL data is carried out below: first the residue place
and periodic chains are selected, then the integral tensor equations are reduced
scheme-theoretically to rank-two incidence, and finally Frobenius and Verschiebung identify all
global branches and their intersections.

The route is thus

$$
\text{lattice chain}
\longrightarrow \text{PEL local model}
\longrightarrow \text{semistable strata}
\longrightarrow R\Psi
\longrightarrow (r,N)
\longrightarrow \text{conductor and local type}.
$$

Each arrow retains information that the next numerical invariant may forget. The conductor remembers a rank and a wild correction. The local type also remembers finite inertia, the nilpotent operator, Frobenius, and, in degree two, whether $N^2$ is nonzero.

### 1.2 Standing arithmetic and cohomological conventions

Let $R$ be a henselian excellent discrete valuation ring with fraction field $K$, uniformizer $\pi$, and perfect residue field $k$ of characteristic exponent $p$. When weights or Frobenius eigenvalues are discussed, $k=\mathbf F_q$ is finite. Fix $\ell\ne p$ and write

$$
E_\ell=\mathbf Q_\ell,\qquad \Lambda_\ell=\mathbf Z_\ell.
$$

At a geometric special point, $\widehat{R^{\mathrm{sh}}}$ denotes the completion of the strict
henselization of $R$ at that point. It has the same chosen uniformizer $\pi$.

All geometric fibers are taken after fixed separable closures. Geometric Frobenius is denoted by $F$. The Tate twist is normalized so that $F$ acts on $E_\ell(1)$ by $q^{-1}$. Accordingly the monodromy operator has the typed form

$$
N:V\longrightarrow V(-1),\qquad FNF^{-1}=q^{-1}N.
$$

A flat $R$-scheme of finite presentation and relative dimension $d\le2$ is **strictly
semistable** if its total space is regular and, étale locally, it is

$$
\operatorname{Spec}R[t_1,\ldots,t_{d+1}]/(t_1\cdots t_r-\pi)
$$

for $1\le r\le d+1$, with unused coordinates smooth. In addition, the geometric irreducible
components $Y_i$ are required to be smooth; this excludes
global self-nodes of one component and is the strict condition used by the ordered-strata
spectral sequence below. Write the geometric special fiber as $Y=\bigcup_{i\in I}Y_i$ and set

$$
Y^{(a)}=\coprod_{i_1<\cdots<i_a}Y_{i_1}\cap\cdots\cap Y_{i_a}.
$$

The ordering of $I$ fixes signs in incidence maps; the resulting cohomology is independent of it.

The normalization, blowup, regular-model, graph, component-group, and low-dimensional nearby-cycle results established earlier are used with their stated hypotheses. We recall every formula that enters a calculation. The generic quaternionic and unitary PEL spaces, their selected canonical components, and their universal families are the ones already constructed. No later automorphic decomposition is assumed.

### 1.3 The exact scope of the construction

Bad integral models are not uniform across all parahoric groups. This book treats exactly the
rank-two minuscule parahorics occurring in the catalogued PEL-exact quaternionic curves and the
standard unitary modèles étranges surfaces. The residue prime is chosen to split every algebra
and coefficient packet. That choice is restrictive enough to make the integral tensors
visible. It is exactly the completely split odd sub-scope consumed by the downstream surface
theorem, not a claim about every parahoric place of the same rational groups.

Three cases result:

1. a quaternionic curve with one Iwahori chain;
2. a unitary surface with one Iwahori direction and one hyperspecial direction;
3. a unitary surface with two Iwahori directions.

In every case the chain has one distinguished self-dual vertex, and forgetting all other
vertices lands in the selected hyperspecial PEL functor constructed previously. This is what
makes the forgetful morphism used in the projectivity argument available. The neighboring
vertices carry the induced parahoric polarization types; they are not silently identified with
additional hyperspecial Book 130 models.

We also allow finite extension of $K$ followed by normalization and the explicit semistable modifications of Chapter 7. This is a semistable alteration when the generic variety is replaced by a finite cover. It is not called a model of the original generic variety. Arbitrary ramified unitary local models, deeper lattice chains, nonflat naive determinant loci, and wild singularities are outside the theorem. Their exclusion is necessary because their nearby cycles are not determined by the charts proved here.

There is one inherited qualification, already discharged for the models used here. Projectivity
of the distinguished good vertex is taken from the current Book 130 theorem, including the Book
205 presentation audit which that theorem imports for every PEL-exact quaternionic realization.
We do not reproduce its Raynaud-boundary proof or promote a central common refinement to an
isomorphism of universal abelian schemes. Section 1.4 verifies the local premises of the
imported theorem. In degree two no monodromy--weight assertion is assumed. Sections 10.4 and 12
compute the induced restriction--Gysin and extreme incidence maps themselves, including their
ranks and radicals.

### 1.4 Prerequisite audit and the selected split place

Fix one of the rational quaternionic PEL-exact data of Book 127, or the standard two-active
unitary-surface datum of Book 129, together with its selected canonical component union and a
neat level away from a finite set of level primes. Let $L/\mathbf Q$ be a finite Galois field containing the normal closures of
the center, reflex field, and, in the unitary case, the CM field, and splitting every simple
factor of the PEL algebra. Put in a finite set $\Sigma$ the prime $2$, the discriminants of these
fields and algebras, the polarization degree, the order index, the primes supporting that level, and the
exceptional places recorded in Books 127 and 129. Choose a rational prime

$$
p\notin\Sigma
$$

which splits completely in $L$, choose one of the resulting places $v$ of the reflex field, and
set

$$
R=\mathcal O_{E,v}^{\mathrm h},\qquad \pi=p,\qquad k=\mathbf F_p.
\tag{1.1}
$$

All conclusions below are for a prime satisfying this displayed selection. A bad fiber means
bad *parahoric level* at this selected prime; the distinguished endpoint PEL data themselves are
unramified.

**Theorem 1.1 (verified prerequisite and place ledger).** At the place (1.1), all algebra
idempotents and both active unitary packets are defined over $\mathbf Z_p$, the maximal order is
split and $*$-stable, and the distinguished polarization lattice is self-dual. The
distinguished hyperspecial models are the smooth projective fine models of Book 130, Theorem
16.1: this applies to every PEL-exact quaternionic realization admitted by Book 127 and to the
standard unitary realization of Book 129. Compatible central and common-refinement quotients
in the quaternionic case, and ordinary level quotients in either case, have exactly the fine,
stack, coarse, and universal-family qualifications in that theorem. The
parahoric chains selected in Section 2.1 therefore have a projective good vertex to which all
extra flag data may be forgotten.

**Proof.** Complete splitting gives

$$
\mathcal O\otimes\mathbf Z_p\simeq
\prod_\tau M_{n_\tau}(\mathbf Z_p)
$$

with $*$ either pairing two factors or acting by the standard adjoint involution. Because
$p\notin\Sigma$, the chosen maximal order is unramified, the polarization degree is a unit, and
the lattice and its tensor stabilizer are respectively self-dual and reductive. The determinant
orientation of Books 127 and 129 singles out one quaternionic rank-two Morita packet or two
independent unitary rank-two packets. Book 130 computes the actual stable-isotropic good-vertex
local model, not merely its generic fiber: it is $\mathbf P^1_R$ in the curve case and
$\mathbf P^1_R\times\mathbf P^1_R$ in the surface case. Its integral
Hodge-filtration lifting theorem gives the smooth framed deformation diagram. Thus every
good-place premise appearing in its boundary theorem is verified at (1.1); the exclusion of
$p=2$ also removes its special alternation qualification.

The properness input is imported at exactly that strength. Book 130 uses Book 205 to compare the
global Raynaud middle form packet by packet, trivialize only the adjoint similarity torsor, and
exclude false flags supported in auxiliary or central packets. Replacing that argument by the
slogan that an arbitrary isotropic subspace has a proper stabilizer would lose precisely the
presentation independence which Book 205 proves. The present book needs only the resulting
projectivity of the distinguished fine model and the stated finite-quotient comparisons. Book
205 is therefore in the dependency closure through Book 130, not an additional direct input
here.

The remaining direct inputs have equally sharp boundaries. Books 127 and 129 provide the exact
rational tensors, determinant orientation, selected components, and Hecke datum, but no
parahoric chain; that chain is constructed in Section 2.1. Book 38 is used only after finite
local freeness and isotropy of a kernel have been proved. Books 10--12 supply normalization,
blowups, graphs, and component groups. Books 24 and 26 supply the semistable nearby-cycle
complex, Frobenius--Verschiebung formalism, purity, duality, and Lefschetz tools, but no global
stratum identification; Sections 4.3, 5.3, and 6.4 construct it. This accounts for every direct
dependency and does not import a theorem from a later book. The exact row is therefore

$$
\boxed{131\mid 10,11,12,24,26,38,127,129,130.}
\tag{1.2}
$$

There are nine direct dependencies. Book 205 is used through the accepted Book 130 interface
and remains transitive. $\square$

## 2. Parahoric PEL data and bad-prime moduli

### 2.1 A periodic lattice chain

At a hyperspecial place a single self-dual lattice is enough. An Iwahori level remembers a neighboring pair, and the Hodge filtration must be compatible with both. This is the smallest parahoric refinement capable of producing a node.

Let $U_0$ and $U_1$ be free rank-two $R$-modules with maps

$$
\alpha:U_0\longrightarrow U_1,
\qquad
\beta:U_1\longrightarrow U_0
$$

such that

$$
\beta\alpha=\pi\operatorname{id}_{U_0},
\qquad
\alpha\beta=\pi\operatorname{id}_{U_1}.
\tag{2.1}
$$

For each active packet $a$, choose a basis $e_a,f_a$ of the endpoint Morita module and set

$$
U_{a,0}=Re_a\oplus Rf_a,\qquad
U_{a,1}=Re_a\oplus R\pi^{-1}f_a.
$$

Let $\alpha$ be inclusion and let $\beta$ be multiplication by $\pi$. In the bases
$(e_a,f_a)$ and $(e_a,\pi^{-1}f_a)$ these maps are

$$
\alpha=\begin{pmatrix}1&0\\0&\pi\end{pmatrix},
\qquad
\beta=\begin{pmatrix}\pi&0\\0&1\end{pmatrix}.
\tag{2.2}
$$

Over $K$, both maps are isomorphisms, so the two filtration lines determine one another. Over
$k$, each map has rank one, and two limiting choices appear. That rank drop is the source of the
two components.

We now place this chain in the exact PEL lattices. Under the split decomposition in Theorem 1.1,
Morita equivalence writes each algebra packet as a matrix module built from a multiplicity
module $U_\tau$. The involution either pairs the $\tau$-packet perfectly with a distinct
$\tau^*$-packet or gives the usual perfect alternating pairing on their sum. At a selected
active packet extend the two displayed lattices to all $n\in\mathbf Z$ by

$$
U_{a,2m}=\pi^{-m}U_{a,0},\qquad
U_{a,2m+1}=\pi^{-m}U_{a,1}.
$$

At the two representative vertices $i=0,1$, put $U_{a,i}$ in the $\tau$-factor and
$U_{a,-i}^{\vee}=\operatorname{Hom}_R(U_{a,-i},R)$ in the $\tau^*$-factor, and leave every
inactive factor equal to its self-dual endpoint lattice. In a self-paired packet, use the
standard alternating form to identify $U_{a,-i}^{\vee}$ with the opposite lattice in the same
plane. Reassemble these two full lattices and extend the *entire* PEL lattice, including inactive
packets, by $\Lambda_{a,i+2}=\pi^{-1}\Lambda_{a,i}$. This gives a periodic $*$-self-dual chain

$$
\Lambda_{a,0}\subset\Lambda_{a,1}\subset
\pi^{-1}\Lambda_{a,0},\qquad
\Lambda_{a,i}^{\#}=\Lambda_{a,-i}
\tag{2.2a}
$$

after the harmless periodic reindexing of the dual vertices. Thus the polarization pairing is
perfect at the full-chain level, not postulated on the single multiplicity module.

Only the vertex indexed by $0$ is asserted to be self-dual for the original perfect form. At an
active factor the neighboring vertex is modular, and globally its dual is the oppositely indexed
vertex as in (2.2a). Multiplying the form on one reduced packet does not make the full PEL lattice
self-dual when inactive packets and the common similitude are retained. The neighboring vertex
therefore carries the polarization type dictated by the full multichain; it is not a second
hyperspecial endpoint. This distinction is essential in a presentation with fixed central
packets and in the one-direction surface case.

For the quaternionic curve, (2.2a) is inserted only in the unique moving rank-one determinant
packet and its $*$-partner. For the unitary surface, insert it in the first active packet and
retain the hyperspecial vertex in the second direction for one-direction level; insert the same
chain independently in both active packets for two-direction level. Complex conjugation supplies
the opposite chains, while every fixed packet retains its labeled vertex. Because all
idempotents lie in the split maximal order, this is an honest $*$-self-dual PEL multichain. Its
stabilizer inside the exact common-similitude group has local factor respectively an Iwahori,
an Iwahori times a hyperspecial factor, or two Iwahori factors. The orientation is the arrow
$\Lambda_{a,0}\to\Lambda_{a,1}$; forgetting every nonzero vertex gives precisely the
distinguished hyperspecial functor of Theorem 1.1.

Equivalently, and without choosing representatives for the neighboring global lattices, let
$\mathrm{red}_a:G_{\mathbf Z_p}(\mathbf Z_p)\to\mathrm{GL}(U_{a,0}\otimes k)$ be the active
Morita reduction and let $B_a$ stabilize the oriented line selected by (2.2). For a set $J$ of
bad directions put

$$
K_p(J)=\{g\in G_{\mathbf Z_p}(\mathbf Z_p):
\mathrm{red}_a(g)\in B_a\text{ for every }a\in J\}.
\tag{2.2b}
$$

This inverse-image definition retains the exact common-similitude and all fixed packets. It is
the Iwahori, Iwahori--hyperspecial, or two-Iwahori level used on the generic fiber; the displayed
multichain is its integral realization.

The presentation audit can now be read without suppressing a packet. The accepted Book 130
interface leaves exactly the following rows at the selected split place:

| rational PEL presentation | active reduced integral packet | modified vertices | framed local model |
|---|---|---|---|
| Book 127 quaternionic-Hermitian-line row, including matrix Morita transfer and derived-trivial central packets | one self-paired alternating rank-two plane; all auxiliary packets fixed | $(\Lambda_0,\Lambda_1)$ in that plane and its full-chain dual | $M^{\mathrm{Iw}}$ |
| Book 127 binary-unitary curve row, including its Morita and central variants | one ordered split CM packet and its forced annihilator packet | $U_{a,i}$ in one factor and $U_{a,-i}^{\vee}$ in its conjugate | $M^{\mathrm{Iw}}$ |
| standard Book 129 surface, one bad direction | first ordered unitary packet chained; second active packet kept hyperspecial | one two-vertex chain and one good line | $M^{\mathrm{Iw}}\times_R\mathbf P^1_R$ |
| standard Book 129 surface, two bad directions | both ordered unitary packets chained independently, with both annihilator packets forced | the commuting square of the two two-vertex chains | $M^{\mathrm{Iw}}\times_RM^{\mathrm{Iw}}$ |

No higher-corestriction, bare hyperbolic, or altered two-active surface presentation is hidden in
this table: those are not additional admitted Book 127 curve rows or the standard Book 129
surface. Fixed packets still retain their order, orientation, polarization, and common-multiplier
labels even though they contribute no moving flag.

### 2.2 The moduli problem

The bad-prime moduli problem must record the integral isogeny rather than merely a subgroup in a
generic fiber. For an $R$-scheme $S$, an object has a distinguished good-vertex PEL abelian
scheme

$$
(A_0,\iota_0,\lambda_0,\eta^p)
$$

together with an adjacent abelian scheme carrying the induced order action, determinant label,
prime-to-$p$ level, and parahoric polarization type, and an $\mathcal O$-linear isogeny

$$
\phi:A_0\longrightarrow A_1
\tag{2.3}
$$

whose kernel has the finite locally free packet type prescribed by
$\Lambda_0\subset\Lambda_1$. The polarizations satisfy

$$
\phi^\vee\lambda_1\phi=c\lambda_0
\tag{2.4}
$$

for the scalar $c$ and the target polarization type determined by the full self-dual multichain,
and the prime-to-$p$ levels correspond under $\phi$. Both Lie algebras satisfy their vertexwise
determinant and orientation laws. Equivalently, one specifies a finite locally free,
$\mathcal O$-stable, polarization-isotropic kernel $H\subset A_0[p^a]$ with the prescribed active
Morita summand and forced $*$-annihilator, puts $A_1=A_0/H$, and uses Book 38 to descend
$p^a\lambda_0$ to the prescribed polarization on $A_1$. Unless $H$ is globally Lagrangian, that
target polarization has nontrivial $p$-primary kernel. This is why $A_1$ is not another good
Book 130 endpoint.

Why insist on finite local freeness? A schematic subgroup of the right generic rank can acquire torsion in its coordinate algebra and cease to define an isogeny in the special fiber. Flatness is exactly what keeps the degree constant. Why impose the determinant law at both vertices? At a bad prime the algebra can fail to be semisimple modulo $p$; a condition at only one vertex need not control the other Lie algebra.

At neat prime-to-$p$ level, automorphisms are trivial. At coarser level the same construction gives a finite quotient stack; all geometric calculations are first made on a fine cover.

For a unitary surface with two bad directions, the object contains two kernels in orthogonal
idempotent packets and the resulting commuting quotient square. The cocycle condition identifies
the two composites. On de Rham homology this becomes the product of two incidence problems. In
the one-direction case the second moving Hodge line remains hyperspecial, but no second global
self-dual lattice representative is inferred from that local-model factor.

### 2.3 Representability, generic fiber, and properness

Before representing the functor, we identify its exact linear algebra. This is the comparison
which cannot be inferred from an abstract rank-two module.

**Proposition 2.1 (datum-specific flat local-model comparison).** For the maximal order,
polarization lattice, idempotent orientation, and chains selected in Sections 1.4 and 2.1, the
framed Hodge-filtration functor is scheme-theoretically

$$
M^{\mathrm{Iw}},\qquad
M^{\mathrm{Iw}}\times_R\mathbf P^1_R,\qquad
M^{\mathrm{Iw}}\times_RM^{\mathrm{Iw}}
\tag{2.4a}
$$

in the quaternionic, one-direction unitary, and two-direction unitary cases, respectively. These
schemes are flat over $R$ and have no extra vertical associated components.

**Proof.** Work over an arbitrary $R$-algebra $B$; this proves equality of functors, including
nilpotent test rings. The split primitive idempotents decompose every framed de Rham lattice and
its Hodge direct summand. Stability under a matrix factor $M_n(R)$ is, by integral Morita
equivalence, exactly the assertion that the corresponding summand is obtained from a direct
summand in the multiplicity module. The determinant polynomial from Book 127 or Book 129 has
rank zero or full rank in every inactive oriented packet and rank one in each active packet.
Consequently inactive Hodge factors are forced, while an active factor is a line subbundle
$L_{a,i}\subset U_{a,i}\otimes B$.

The $*$-paired packet is not a second choice: perfect polarization identifies it with the
annihilator of $L_{a,-i}$. In a self-paired rank-two alternating plane every line is isotropic.
Thus polarization and duality add no equation after the active line has been chosen. The only
remaining equations say that the Hodge summands respect the two maps of the isogeny crystal;
under Morita equivalence they are exactly

$$
\alpha L_{a,0}\subset L_{a,1},\qquad
\beta L_{a,1}\subset L_{a,0}.
\tag{2.4b}
$$

There is no hidden refined condition. The exterior-square determinant relation vanishes
identically on a rank-one direct summand, and the spin condition belongs to even orthogonal
local models, whereas these exact factors are quaternionic type $A_1$ or split unitary type
$A_1$. In the unitary datum the two active primitive idempotents are orthogonal and their
conjugates are already determined by annihilators. The common similitude scalar records the
polarization multiplier but imposes no equation between the two Hodge lines. Hence their
functors are a product, scheme-theoretically, not just on geometric points.

Equations (2.4b) give the first scheme in (2.4a); retaining an unmodified active line gives the
second, and applying them independently twice gives the third. The affine cover calculated in
Section 3 consists of smooth charts and the torsion-free chart
$R[x,y]/(xy-\pi)$. Products with polynomial rings and with a second such chart remain
$R$-torsion-free. Flatness over the DVR follows, and the special fiber is reduced. Therefore no
vertical embedded or associated component remains. $\square$

**Theorem 2.2 (parahoric PEL representability).** At neat prime-to-$p$ level, the one-chain and
two-chain functors of Section 2.2 are represented by projective $R$-schemes of finite
presentation. Their generic fibers are the selected quaternionic or unitary Shimura varieties
at the corresponding parahoric level. They carry the universal isogeny chain and are flat over
$R$.

**Proof strategy.** Forget the parahoric subgroup and map to the already constructed projective
hyperspecial PEL model. The finite subgroup is placed in a relative projective Hilbert scheme,
the PEL and lattice-chain equations cut out a closed locus, and the valuative criterion follows
by taking the unique flat closure of the generic subgroup after the underlying abelian scheme has
extended.

**Proof.** Let $\mathscr M^{\mathrm{hyp}}$ be the selected hyperspecial fine PEL model obtained by
forgetting the parahoric subgroup data. It is projective over $R$ by the verified Book 130 input
in Theorem 1.1. Over $\mathscr M^{\mathrm{hyp}}$, the relative Hilbert scheme of subschemes of the
finite flat group $\mathcal A[p^a]$ is projective. Its universal subscheme is flat with its fixed
Hilbert polynomial. The conditions that it be a subgroup, be stable under a finite generating
set of $\mathcal O$, have the prescribed rank, and be isotropic for the polarization pairing are
closed. Packetwise Hilbert polynomials impose the active Morita rank and the forced
$*$-annihilator; these conditions are open and closed inside that fixed-rank subgroup locus. The
quotient by the resulting finite locally free subgroup exists as an abelian scheme. Book 38
descends the required multiple of the source polarization, and (2.4), its prescribed target
kernel type, the determinant identities at the new vertex, and compatibility of successive
steps are closed conditions. The finite étale determinant-orientation labels select an
open-and-closed union of that projective locus. For two chains the same construction is iterated and equality of
the two composite isogenies is imposed as a closed equality of homomorphisms. Hence the
parahoric functor is represented by a projective scheme of finite presentation over
$\mathscr M^{\mathrm{hyp}}$, and it carries the universal isogeny chain.

Over $K$, the prescribed kernel is étale after passage to a suitable level cover and is exactly a parahoric level flag. Hence the generic fiber is the required Shimura variety.

For completeness, the valuative step can also be read directly from this construction. Given a
point over the fraction field of a valuation ring over $R$, properness of
$\mathscr M^{\mathrm{hyp}}$ extends the underlying PEL abelian scheme; this is exactly where the
imported Book 130 projectivity theorem is used. The schematic closure of each
generic kernel in the finite flat group $A_i[p^a]$ is finite, and its coordinate algebra is
torsion-free over the valuation ring, hence flat. The subgroup, algebra-stability, isotropy, and
cocycle identities extend by schematic closure. The packetwise rank is constant because its
idempotent summands are direct factors. The quotients and their descended polarizations then
extend, and separatedness gives uniqueness. Thus the constructed projective scheme has
precisely the desired generic fiber and valuative extension property. Flatness is smooth-local
from Proposition 2.3 below and Proposition 2.1. $\square$

The theorem does not assert that the model is smooth. Its singularities are precisely the content of the local-model calculation.

### 2.4 The local-model diagram

To compare a moduli singularity with linear algebra, add frames to the de Rham modules at every lattice vertex. This gives

$$
\mathscr M
\xleftarrow{\ p\ }
\widetilde{\mathscr M}
\xrightarrow{\ q\ }
M^{\mathrm{loc}}.
\tag{2.5}
$$

The map $p$ is a torsor under the smooth integral automorphism group of the lattice chain. The map $q$ sends an abelian isogeny chain to its framed Hodge submodules.

**Proposition 2.3 (local-model principle).** Both $p$ and $q$ are smooth, of the same relative
dimension given by the frame group. Consequently $\mathscr M$
and $M^{\mathrm{loc}}$ have isomorphic strict henselian completed local rings after adjoining
equally many formal power-series variables. Their morphisms to $R$ are therefore smoothly
equivalent; regularity, flatness, and the strict-normal-crossings property may be checked on the
displayed local models.

**Proof.** The frame group is smooth in the present data. Under the split Morita decomposition,
an active factor is the standard smooth $\mathrm{GL}_2$ lattice-chain group scheme. Its special
fiber maps onto the corresponding Borel and has a smooth affine-unipotent kernel; it is not
itself identified with that lower-dimensional Borel. Inactive factors are the reductive
hyperspecial groups of Theorem 1.1. Taking the product with the $*$-paired factors and imposing
the common smooth similitude character preserves smoothness.

The frame torsor is locally nonempty. At a geometric special point, the covariant Dieudonne
module of a reduced active height-two packet and the quotient by its prescribed rank-$p$
subgroup form an index-$p$ lattice pair. The elementary-divisor theorem, together with the dual
annihilator condition, gives the maps (2.2); inactive packets give the fixed vertices. Lifting a
frame through a nilpotent thickening is then the smooth lifting property of the just-described
lattice-chain group. Thus $p$ is its torsor.

For $q$, apply the integral Hodge-filtration lifting
theorem used for the good models, now at every vertex of the isogeny chain. On a divided-power
evaluation when the residue characteristic is nilpotent, a deformation of the PEL chain is
equivalent to a lift of its Hodge direct summands compatible with the maps of the lattice chain.
Proposition 2.1 proves that the algebra, polarization, determinant, and refined integral
conditions are exactly the defining conditions of $M^{\mathrm{loc}}$. Book 130's
Hodge-filtration theorem includes the lifting criterion for morphisms of the evaluated crystals,
so compatibility with the two displayed maps lifts the isogeny. Its kernel remains finite
locally free of the same degree by the index-$p$ lattice condition, and Book 38 reconstructs the
quotient abelian vertex and its descended polarization. Prime-to-$p$ level lifts uniquely.
Descent from the divided-power presentation reconstructs the complete abelian chain over the
original square-zero thickening. Thus $q$ is formally smooth, and finite
presentation makes it smooth. Both frame maps
have relative dimension equal to that of the frame group. The statement about completions and
smooth equivalence is the standard local consequence of the two smooth maps. $\square$

This proof is why the actual flat local model must be known. A naive determinant scheme with an extra vertical component would give the wrong completed ring.

## 3. The rank-two Iwahori local model

### 3.1 Incidence of two lines

Define $M^{\mathrm{Iw}}$ over $R$ by

$$
M^{\mathrm{Iw}}(S)=\left\{(L_0,L_1):
L_i\subset U_i\otimes\mathcal O_S\text{ line subbundles},
\ \alpha L_0\subset L_1,
\ \beta L_1\subset L_0\right\}.
\tag{3.1}
$$

It is closed in $\mathbf P(U_0)\times_R\mathbf P(U_1)$, hence projective. Over $K$, $L_1=\alpha L_0$, so its generic fiber is $\mathbf P^1_K$. The special fiber is more informative. The rank-one maps $\bar\alpha$ and $\bar\beta$ have complementary kernel and image. A line away from the kernel determines the other line, but at the kernel there are two limiting branches.

The incidence formulation is preferable to a single determinant equation. It records both vertices, is invariant under change of lattice-chain bases, and carries the universal filtration data needed to extend the PEL isogeny.

### 3.2 The nodal chart

**Proposition 3.1 (Iwahori chart).** The scheme $M^{\mathrm{Iw}}$ is regular, flat, and semistable over $R$. It is smooth except at one point of the special fiber, where an affine neighborhood is

$$
\operatorname{Spec}R[x,y]/(xy-\pi).
\tag{3.2}
$$

**Proof.** Use the bases of (2.2). Near the exceptional pair, write

$$
L_0=R(x,1),\qquad L_1=R(1,y).
$$

The condition $\alpha L_0\subset L_1$ says $(x,\pi)$ is proportional to $(1,y)$, hence $xy=\pi$. The condition involving $\beta$ gives the same equation. The remaining standard affine charts eliminate one line coordinate uniquely and are smooth.

The ring in (3.2) is flat because it is torsion-free over the DVR. At its closed point its maximal ideal is generated by $x,y$, since $\pi=xy$; its dimension is two and its embedding dimension is two, so it is regular. The special fiber is $xy=0$, two smooth branches meeting transversely. This proves the assertion. $\square$

The word “singular” must now be used carefully. The morphism to $R$ is not smooth at the crossing, and the special fiber is singular, but the total space is regular. Nearby cycles arise from failure of smoothness, not from singularity of the total space.

### 3.3 Components and their intersection

The special fiber of $M^{\mathrm{Iw}}$ consists of two copies of $\mathbf P^1_k$, denoted $C_0$ and $C_1$. One corresponds to choosing the limiting line at the first lattice vertex; the other corresponds to the second. They meet once and transversely. Locally they are $x=0$ and $y=0$.

If the local model is pulled back by a smooth morphism of relative dimension $a$, the two components become smooth of dimension $a+1$ and meet along a smooth locus of dimension $a$. The normal bundles of the intersection inside the two components are dual: from $xy=\pi$, $x$ cuts one branch and $y$ the other, while their tensor product is the trivial normal direction defined by $\pi$.

For a proper regular curve model whose special fiber is globally $Y_0+Y_1$, the fiber relation gives

$$
Y_0^2=-(Y_0\cdot Y_1),\qquad
Y_1^2=-(Y_0\cdot Y_1).
\tag{3.3}
$$

If the intersections are geometric points $s$ with residue degrees $f_s$, then

$$
(Y_0\cdot Y_1)=\sum_s f_s.
\tag{3.4}
$$

Thus the component matrix is the negative Laplacian of the two-vertex multigraph.

### 3.4 Thickness and ramified variants

After a ramified base change of index $e$, equation (3.2) becomes

$$
xy=u(\pi')^e.
$$

Absorbing the unit gives thickness $e$. For $e>1$ the total space is not regular. Its minimal semistable resolution inserts a chain of $e-1$ rational components and replaces the weighted edge by $e$ unit edges. The cycle rank is unchanged, but the integral edge pairing is multiplied by $e$.

This separates rational and integral monodromy. Tensoring with $E_\ell$, subdivision changes no rank. On $\Lambda_\ell$, the monodromy map may acquire a larger cokernel, and that cokernel is visible in the component group. Thickness therefore belongs in every integral type calculation even when the Artin conductor is unchanged.

## 4. The bad quaternionic curve

### 4.1 Construction of the integral curve

Use the split place and the unique active quaternionic chain selected in Sections 1.4 and 2.1.
Let

$$
\mathscr C_{\mathrm{Iw}}/R
$$

be the fine moduli scheme of the PEL isogeny (2.3), restricted to the selected canonical component union. Theorem 2.2 makes it projective and identifies its generic fiber with the parahoric Shimura curve.

This moduli construction is important even when one can describe the generic curve by a double quotient. It extends the universal isogeny, the order action, the polarization, and prime-to-$p$ level simultaneously. Those structures later make Hecke actions on nearby cycles canonical.

### 4.2 Regularity and semistability

**Theorem 4.1 (semistable quaternionic model).** For the selected quaternionic datum,
$\mathscr C_{\mathrm{Iw}}$ is a regular projective flat curve over
$R$ with reduced nodal special fiber. At every geometric node its completed strict henselian
local ring is

$$
\widehat{R^{\mathrm{sh}}}[[x,y]]/(xy-\pi).
\tag{4.1}
$$

In particular it is strictly semistable.

**Proof.** Projectivity is Theorem 2.2. Flatness, regularity of the total space, and the property
that the special fiber is a reduced strict-normal-crossings divisor are smooth-local on the
source. Proposition 2.3 transfers them from $M^{\mathrm{Iw}}$, and Proposition 3.1 proves them
there. At a crossing the completed strict henselian local ring of the curve model is a regular
two-dimensional $\widehat{R^{\mathrm{sh}}}$-algebra whose special fiber has two smooth branches meeting
transversely. If $x$ and $y$ cut out those branches, the principal fiber relation gives
$\pi=u xy$ for a unit $u$; replacing $x$ by $ux$ gives (4.1). Away from the crossing
stratum the local model is smooth. The two lattice-vertex labels globalize the two branch loci;
each labeled locus is smooth by the same smooth descent, so every geometric irreducible
component is smooth and no component has a self-node. $\square$

At quotient level, take a fine normal subgroup of the prime-to-$p$ level. If the quotient group acts freely on the integral model, the quotient remains semistable étale locally. If it has fixed points in the special fiber, the coarse quotient can have quotient singularities. Nearby-cycle calculations should then be made equivariantly on the fine cover and descended; silently treating the coarse space as regular is not valid.

### 4.3 The global component graph

Let $\mathscr X$ be the distinguished smooth projective hyperspecial model obtained by
forgetting the parahoric flag, and let $X$ be its geometric special fiber. Write $X_F$ and
$X_V$ for a labeled copy and a labeled Frobenius-twisted copy of $X$; over the selected
$\mathbf F_p$-place both have underlying good fiber $X$. Below they will normalize the two
branches. No second hyperspecial lattice vertex is being introduced. In characteristic $p$, the active idempotent
of the universal $p$-divisible group on $X$ is a one-dimensional height-two group $G$.
Verschiebung on its Hodge line gives the partial Hasse section

$$
\operatorname{Ha}:\omega_G\longrightarrow\omega_G^{(p)},
\qquad
\operatorname{Ha}\in H^0(X,\mathcal L),\qquad
\mathcal L=\omega_G^{\otimes(p-1)}.
\tag{4.2}
$$

Write $Z=V(\operatorname{Ha})$.

**Lemma 4.2 (the reduced height-two calculation).** At a geometric point of $X$, the admissible
rank-$p$ subgroups in the reduced active packet are the Frobenius kernel and the étale subgroup
obtained as the Verschiebung kernel on the inverse Frobenius twist on the ordinary locus. At a
local-local point they coincide in the unique admissible $\alpha_p$ line. At such a local-local
point the completed good-vertex deformation ring is $W(\bar k)[[t]]$, and a basis of the
covariant display may be chosen, up to units and the usual semilinearity, so that

$$
F(e)=f,\qquad F(f)=-p e+[t]f.
\tag{4.3}
$$

In this coordinate the Hasse section is $t$ up to a unit. For two orthogonal active packets the
two calculations are independent and give $W(\bar k)[[t_1,t_2]]$.

**Proof.** We first derive, rather than import, the height-two normal form. Modulo $p$, the
covariant crystal of the active BT$_1$ is a two-dimensional space with semilinear $F,V$,
$\operatorname{im}F=\ker V$, and $\operatorname{im}V=\ker F$. At a local-local point both
operators are nilpotent of rank one, so their images and kernels are one common line. Choose
$f$ on that line and $e$ off it, and rescale using the perfect alternating form. Then
$F(e)=f$, $F(f)=0$ modulo $p$. Lift this symplectic basis to the display. The determinant and
polarization fix the Frobenius determinant up to a unit, $FV=VF=p$ determines Verschiebung, and
successive upper- and lower-triangular adapted basis changes give the special matrix
$\left(\begin{smallmatrix}0&-p\\1&0\end{smallmatrix}\right)$ and remove every deformation
coefficient except the lower-right entry. The tangent of that entry is
$\operatorname{Hom}(\omega_G,M/\omega_G)$, the one tangent direction supplied by the verified
good local model and Book 130's Hodge-filtration lifting theorem. Both the target ring and the
good completed deformation ring are formally smooth of dimension one, and the displayed tangent
map is an isomorphism. Successive lifting through the powers of the maximal ideal therefore
identifies the two complete rings and gives (4.3), rather than merely a map from that ring.
Reduction of Verschiebung on the Hodge line is multiplication by $t$.

Over an algebraically closed field, an ordinary height-two, dimension-one Barsotti--Tate group
has multiplicative and etale height-one factors, so its only determinant-compatible rank-$p$
subgroups are the Frobenius kernel and the étale factor. If $G^{(p^{-1})}$ denotes the inverse
Frobenius twist, the latter is
$\ker(V_{G^{(p^{-1})}})\subset G$; this is the precise meaning of the Verschiebung label for a
fixed source. In the local-local special display, the one-dimensional intersection of the
corresponding Frobenius and Verschiebung lines is the unique admissible $\alpha_p$ line.
Orthogonal primitive idempotents split the display and its deformation functor, which proves the
two-parameter assertion. $\square$

It follows that
$Z=(t=0)$ is a reduced finite étale subscheme of $X$, and

$$
\#Z(\bar k)=\deg Z=(p-1)\deg\omega_G.
\tag{4.4}
$$

If the selected generic curve is geometrically connected, proper flatness makes its geometric
special fiber connected. Since Section 3 gives two labeled branches, they must meet, so $Z$ is
nonempty; (4.4) then also proves $\deg\omega_G>0$. This avoids assuming a trivialization of the
determinant--multiplier correction in Book 130's Kodaira--Spencer formula.

We next identify the parahoric branches globally. Reassemble the active kernel of relative
Frobenius with its forced $*$-paired packets and the zero summands in the inactive factors.
If $e_a,e_a^*$ are the paired primitive idempotents and $\operatorname{Mor}_a$ denotes inverse
integral Morita reassembly from the $e_a$-packet, the subgroup is explicitly

$$
H_{F,a}=\operatorname{Mor}_a(\ker F_{G_a})\oplus
\operatorname{Mor}_{a^*}\bigl((\ker F_{G_a})^\perp\bigr),
\tag{4.4a}
$$

when $a$ and $a^*$ are distinct. In a self-paired alternating packet, the line is its own
orthogonal and only the first Morita-reassembled summand is taken. This subgroup is finite
locally free, $\mathcal O$-stable, and isotropic. Book 38 therefore supplies the PEL quotient,
which is the partial relative-Frobenius isogeny in the active packet. This construction gives a
morphism

$$
j_F:X_F\longrightarrow Y.
$$

Here none of the three kernel properties is inferred from a generic closure. Relative
Frobenius on a Barsotti--Tate group has a finite locally free kernel; the split idempotents make
its reduced active idempotent summand a direct finite locally free factor of rank $p$, and
integral Morita reassembly gives the full packet rank prescribed by the lattice index. The polarization pairs
distinct $*$-packets and is alternating on a self-paired packet, so the selected summand and its
forced annihilator are isotropic. In the display (4.3), quotienting by that line interchanges
the two adjacent-vertex Hodge ranks and leaves every inactive determinant block fixed. Thus the
quotient satisfies the determinant orientation and polarization scalar prescribed by (2.4),
which is the remaining PEL assertion needed to apply Book 38.

For the other branch, use the Frobenius-twisted good family $A^{(p)}$ on $X_V$. The active
$p$-divisible packet has Verschiebung
$V_{G_a}:G_a^{(p)}\to G_a$; reassemble its kernel inside $A^{(p)}[p]$ together with the forced
$*$-annihilator, leaving the other packet summands zero. This does not identify the quotient
with $A$: Book 38 gives it the adjacent polarization type required by (2.4). The resulting
isogeny gives $j_V:X_V\to Y$. Equivalently, for a fixed
geometric source this is the inverse-twist subgroup in Lemma 4.2. That lemma says that the two subgroup types
exhaust the ordinary locus and coincide precisely at $t=0$ in the unique admissible $\alpha_p$
line. It follows that $j_F$ and $j_V$ are isomorphisms over dense ordinary opens,
meet exactly along the identified copies of $Z$, and cover every geometric point of $Y$.

This pointwise classification is scheme-theoretic. In the framed deformation ring the two
choices are the two minimal primes $(x)$ and $(y)$ of $k[[x,y]]/(xy)$; (4.3) identifies their
common vanishing parameter with the Hasse parameter. Proposition 2.3 descends that statement to
the moduli space. More precisely, on the reduced quotient by either minimal prime the completed
map from the corresponding labeled good copy is $\bar k[[t]]\to\bar k[[t]]$, an isomorphism
after the Frobenius-twist parameterization of the V branch. Thus each $j_\epsilon$ is
quasi-finite at the Hasse points as well as on the ordinary open. Since the total model is flat
and the special local equation is reduced, both branches occur with multiplicity one and there
is no third branch. The maps are proper, hence finite; finite birationality and normality of
$X_F,X_V$ show that $j_F,j_V$ are the normalizations of the two global
Kottwitz--Rapoport branch loci. The degeneracy map which retains the distinguished good source is
the identity on $X_F$ and Frobenius on $X_V$. The quotient degeneracy map lands in the adjacent
parahoric polarization-type functor; after using its opposite dual-chain parameterization it is
respectively the corresponding Frobenius map and the identity. Thus one must not call both
degeneracy legs identities on the good model. Neither leg is used to manufacture a second good
endpoint. On the common locus the two embeddings

$$
\iota_F:Z\hookrightarrow X_F,
\qquad
\iota_V:Z\hookrightarrow X_V
\tag{4.5}
$$

are the Hasse inclusion, up to the harmless Frobenius twist caused by changing which
normalization parameterizes the quotient. That twist is a universal homeomorphism and hence
induces an equivalence on prime-to-$p$ étale cohomology.

Thus $Y_F\setminus Z$, $Y_V\setminus Z$, and $Z$ are the two open and one closed
Kottwitz--Rapoport strata. The preceding display calculation proves their scheme structures and
closure relations.

Thus the geometric dual graph is now explicit. Its vertices are the connected components of
$X_F\amalg X_V$, and each $z\in Z(\bar k)$ is an oriented edge from the component containing
$\iota_Fz$ to the one containing $\iota_Vz$. Its boundary matrix is

$$
\partial[z]=[\pi_0(\iota_Vz)]-[\pi_0(\iota_Fz)].
\tag{4.6}
$$

This formula includes the action of geometric Frobenius: at the completely split place it fixes
the two labels and permutes components and points through its action on $X$ and $Z$. After a
descent extension, a label exchange reverses (4.6) and acts by $-1$ on that oriented edge.

For a connected generic curve the arithmetic genus formula is

$$
g(C)=\sum_{v\in V(\Gamma)}g(Y_v)+b_1(\Gamma).
\tag{4.7}
$$

The toric rank of the special identity component of the Jacobian is $b_1(\Gamma)$. With unit
thickness, the monodromy pairing on $X_\Gamma=H_1(\Gamma,\mathbf Z)$ is

$$
q(a,b)=\sum_{e\in E(\Gamma)}a_eb_e,
\tag{4.8}
$$

and the geometric component group is

$$
\Phi(\bar k)=\operatorname{coker}\left(
X_\Gamma\xrightarrow{q}X_\Gamma^\vee\right).
\tag{4.9}
$$

Equations (4.6), (4.8), and Smith reduction compute the component group, its Frobenius action,
and the monodromy rank from the good-model Hasse locus without an unidentified global branch.

### 4.4 A two-component calculation

Suppose the selected good component is geometrically connected. Then $Y=Y_F\cup Y_V$ and the
components meet transversely in

$$
m=(p-1)\deg\omega_G
$$

geometric points. Thus $\Gamma$ has two vertices and $m$ parallel edges, and

$$
b_1(\Gamma)=m-1,
\tag{4.10}
$$

and the component intersection matrix is

$$
\begin{pmatrix}-m&m\\m&-m\end{pmatrix}.
\tag{4.11}
$$

Choose cycles $c_i=e_i-e_m$ for $1\le i<m$. Their Gram matrix has diagonal entries $2$ and off-diagonal entries $1$. Its determinant is $m$, and its Smith form is

$$
\operatorname{diag}(1,\ldots,1,m).
$$

Therefore

$$
\Phi(\bar k)\simeq\mathbf Z/m\mathbf Z.
\tag{4.12}
$$

For $m=1$ the fiber is reducible but the graph is a tree, so both monodromy rank and component group vanish. This example prevents the common error of replacing “independent cycles” by “number of nodes.”

If the closed nodes have residue degrees $f_s$, then the geometric graph is formed after residue extension, while over $k$ the intersection number is $\sum f_s$. Frobenius on (4.12) must be computed from its signed permutation action, not from the integer $m$ alone.

## 5. A unitary surface with one bad direction

### 5.1 Why one direction can degenerate independently

The compact unitary surface has two active signature-$(1,1)$ multiplicity planes. At a good prime each contributes a projective line to the local model. If only the first lattice is replaced by an Iwahori chain, the second line still varies smoothly. The bad local model is therefore

$$
M^{\mathrm{Iw}}\times_R\mathbf P^1_R.
\tag{5.1}
$$

This product is not merely a dimension count. Morita decomposition separates the two algebra
idempotent factors, and the common similitude condition relates determinant lines without
coupling their infinitesimal line choices. Proposition 2.1 proves this independence for the
selected integral datum over arbitrary test rings.

Let
$\mathscr S_{\mathrm{Iw},\mathrm{hyp}}$ denote the selected unitary PEL moduli surface with the
first direction parahoric and the second hyperspecial.

### 5.2 Local equations and regularity

**Theorem 5.1.** For the selected one-direction unitary datum, the surface
$\mathscr S_{\mathrm{Iw},\mathrm{hyp}}$ is projective, regular, flat, and strictly semistable over
$R$. At a point of its double locus it is étale locally

$$
\operatorname{Spec}R[x,y,z]/(xy-\pi),
\tag{5.2}
$$

where $z$ is a smooth parameter.

**Proof.** Theorem 2.2 gives projectivity. Smooth equivalence in Proposition 2.3 transfers
regularity and the strict-normal-crossings property from the product of (3.2) with the smooth
line chart. At a point of the double locus, choose branch parameters $x,y$ and a parameter $z$
along the double curve. The principal fiber relation is $\pi=u xy$ for a unit $u$; rescaling
$x$ gives (5.2). Its maximal ideal is generated by $x,y,z$, equal to the local dimension three.
Thus the total space is regular, the special fiber is reduced, and the chart is strictly
semistable with $r=2$. The two global branch labels likewise make every geometric irreducible
component smooth. $\square$

No triple point occurs in this case. Consequently $N^2=0$ on every cohomology group, although $N$ on middle cohomology may be nonzero.

### 5.3 Global surface components

Let $X$ be the geometric special fiber of the distinguished good surface, and let $X_F,X_V$
be its labeled ordinary and Frobenius-twisted copies, identified as underlying good fibers at
the selected $\mathbf F_p$-place. Its active $p$-divisible group splits as the two independent
height-two, dimension-one packets $G_1,G_2$. For the parahoric direction
the partial Hasse section is

$$
\operatorname{Ha}_1\in H^0(X,\mathcal L_1),
\qquad \mathcal L_1=\omega_1^{\otimes(p-1)},
\qquad Z_1=V(\operatorname{Ha}_1).
\tag{5.3}
$$

At any point of $Z_1$, Lemma 4.2 supplies the transverse parameter $t_1$; the second active line
supplies an independent smooth parameter whether its packet is ordinary or local-local. At a
point where both packets are local-local, the completed good deformation ring is
$W(\bar k)[[t_1,t_2]]$, and $\operatorname{Ha}_a$ reduces to $t_a$ up to a unit. Consequently
$Z_1=(t_1=0)$ is a smooth Cartier divisor. Its cycle class and normal bundle are

$$
[Z_1]=c_1(\mathcal L_1),
\qquad N_{Z_1/X}=\mathcal L_1|_{Z_1}.
\tag{5.4}
$$

The Frobenius- and Verschiebung-kernel constructions of Section 4.3, applied only to $G_1$ and
with the Frobenius twist on the source of the Verschiebung branch retained, give proper maps
$X_F\to Y_F$ and $X_V\to Y_V$. The rank-two Dieudonné classification proves
that these maps have the same completed minimal-prime isomorphisms as in Section 4.3, with the
second good parameter carried along smoothly. They are therefore finite birational maps from
normal surfaces, hence the normalizations of the two Kottwitz--Rapoport branches, and they meet
exactly along the partial-Frobenius identification of $Z_1$. The framed equation $xy=p$ makes
the branches reduced of multiplicity one and proves that they exhaust the fiber. Thus, on every
geometrically connected good component,

$$
Y=Y_F\cup Y_V,
\qquad D=Y_F\cap Y_V\simeq Z_1,
\tag{5.5}
$$

on the chosen component.

The good-source degeneracy map is the identity on $X_F$ and Frobenius on $X_V$; the quotient map
lands in the adjacent parahoric polarization type, with the opposite dual-chain
parameterization reversing those roles. Accordingly one of the two Hasse embeddings is composed
with the universal homeomorphism $\operatorname{Fr}_1$. For a disconnected selected union, apply the
same statement to each good component; the two Hasse embeddings on $\pi_0$ specify which branch
components a connected component of $Z_1$ joins.

The three locally closed pieces

$$
Y_F\setminus D,\qquad Y_V\setminus D,\qquad D
$$

are exactly the one-direction Kottwitz--Rapoport strata. Their closures, Frobenius action, and
degeneracy maps are therefore all fixed by (5.5), not merely by the local equation.

The dual complex is therefore the explicit bipartite graph with the two labeled copies of the
good components as vertices and connected components of $Z_1$ as edges. It has no second
homology. The possible middle
monodromy comes from $H^1(Z_1)$ and the actual maps below, not from an unidentified double locus.

This is the first place where the surface theory differs from the curve graph. A double curve contains its own cohomology. Counting connected components of $D$ sees only $H^0(D)$ and cannot determine $N$ on $H^2$.

### 5.4 Intersection data

Because $Y_F+Y_V$ is the principal divisor of $\pi$, restricting to $D$ gives

$$
N_{D/Y_F}\otimes N_{D/Y_V}\simeq\mathcal O_D.
\tag{5.6}
$$

The display coordinate identifies $N_{D/Y_F}$ with the Hasse normal line in (5.4); hence
$N_{D/Y_V}$ is its inverse after the partial-Frobenius identification. Equivalently, the two
self-intersection classes of $D$ are negatives of one another. If
$i_F:D\hookrightarrow Y_F$ and $i_V:D\hookrightarrow Y_V$, the maps which enter nearby cycles
are exactly

$$
\rho(a_F,a_V)=i_F^*a_F-i_V^*a_V,
\tag{5.7}
$$

and

$$
\gamma(z)=(i_{F*}z,-i_{V*}z).
\tag{5.8}
$$

The degeneracy descriptions identify $i_F^*$ and $i_V^*$ with restriction to the Hasse divisor,
composed on one side with the cohomological isomorphism induced by partial Frobenius. The Gysin
maps are adjoint to these restrictions under Poincaré duality. Thus (5.7)--(5.8) determine the
maps globally, including signs, rather than only their source and target.

For $j=0$, $i_{F*}(1)=[D]_F=c_1(\mathcal L_1)$ and $i_{V*}(1)=[D]_V$;
restriction to $D$ gives opposite first Chern classes by (5.6). For $a,b\in H^1(Y_F)$, and
similarly on the other branch, the projection and self-intersection formulas give

$$
\langle i_F^*a,i_F^*b\rangle_D
=\int_{Y_F}a\smile b\smile[D]_F,
\qquad
i_F^*i_{F*}(1)=c_1(N_{D/Y_F}).
\tag{5.9}
$$

Together with partial-Frobenius pullback and trace, (5.7)--(5.9) are the promised
restriction--Gysin matrix. Its exact cohomological rank is evaluated in Sections 10.4 and 12.2.

## 6. Two bad directions and semistable regularization

### 6.1 The product-of-nodes singularity

With Iwahori chains in both active directions, the local model is the product

$$
M^{\mathrm{Iw}}\times_RM^{\mathrm{Iw}}.
$$

Theorem 2.2 represents the corresponding square of PEL isogenies by a projective flat raw
surface $\mathscr S_{\mathrm{Iw},\mathrm{Iw}}$. Proposition 2.3 and the datum-specific equality
of Proposition 2.1 make its deepest singularities smoothly equivalent to the following product
chart. On the framed local-model cover, after completing at a chosen lift, the chart is (6.1)
with formally smooth frame variables. We do not cancel those variables to assert an
unjustified literal isomorphism of unframed completed rings.

The model ring is

$$
A=\widehat{R^{\mathrm{sh}}}[[x,y,u,v]]/(xy-\pi,uv-\pi).
\tag{6.1}
$$

It is flat of relative dimension two, but it is not regular at the closed origin. Indeed the
local dimension is three, while modulo the square of the maximal ideal both defining equations
have the same linear term $-\pi$; equivalently, after eliminating $\pi$ the tangent cone is
$xy-uv=0$ in four variables. The embedding dimension is four. Regularity and the number and
incidence of branches are invariant under the smooth equivalence, so the corresponding raw
moduli points are singular with the same four-branch pattern.

The special fiber has four local components, obtained by choosing one of $x,y$ and one of $u,v$ to vanish. All four meet at the origin. Four components cannot meet normally in a regular threefold: a strict semistable surface permits at most three. Thus the raw product model cannot be fed directly into the strict semistable nearby-cycle formula.

### 6.2 The small resolution

The singularity has two natural small resolutions, corresponding to the two diagonals of the square of components. Choose the blowup

$$
\rho:\widetilde X=\operatorname{Bl}_{(x,u)}\operatorname{Spec}A
\longrightarrow\operatorname{Spec}A.
\tag{6.2}
$$

**Proposition 6.1 (explicit resolution).** The scheme $\widetilde X$ is regular and every one of
its completed local equations has strict semistable form over $\widehat{R^{\mathrm{sh}}}$. The
morphism $\rho$ is projective and birational, is an isomorphism away from the origin, and its
exceptional fiber over the origin is $\mathbf P^1_{\bar k}$. It introduces no exceptional
divisor.

**Proof.** The blowup has two standard affine charts. On the $x$-chart write $u=xt$. In the
fraction ring, the relations give

$$
x y=\pi=x t v,
$$

and cancellation of the nonzerodivisor $x$ gives $y=tv$. At the point above the origin with
$t=0$, its completed local equation is

$$
\widehat{R^{\mathrm{sh}}}[[x,t,v]]/(xtv-\pi).
\tag{6.3}
$$

On the $u$-chart write $x=us$. Cancellation similarly gives $v=sy$, and at the point with
$s=0$ the completed local equation is

$$
\widehat{R^{\mathrm{sh}}}[[u,s,y]]/(usy-\pi).
\tag{6.4}
$$

Both completed local rings are regular: the uniformizer is the product of the three displayed
parameters, so those parameters generate a maximal ideal of dimension three. At every other
point of either standard chart, one of $t,s$ is a unit or one of the branch parameters is a
unit; after absorbing that unit the completed equation has one or two factors. These are the
remaining smooth or double-crossing strict semistable charts. Hence the two standard charts
cover the blowup by regular strict semistable local rings.

The blowup is projective and birational by construction. The ideal $(x,u)$ is invertible away from the origin on the ordinary double-point factor, so the map is an isomorphism there. Over the origin the homogeneous ratio $[x:u]$ is free, giving $\mathbf P^1$. Since this exceptional locus has dimension one inside a threefold, it has codimension two and is not a divisor. $\square$

The cancellation used in the proof is legitimate because, after eliminating $\pi$, $A$ is the
ordinary-double-point domain
$\widehat{R^{\mathrm{sh}}}[[x,y,u,v]]/(xy-uv,\pi-xy)$. Performing the same manipulation in an
arbitrary quotient with embedded components would be invalid.

### 6.3 Strict semistability of the resolved charts

Equations (6.3) and (6.4) are the deepest strict semistable chart in relative dimension two:

$$
abc=\pi.
\tag{6.5}
$$

At a generic point of one component, the morphism is smooth. Along a double curve, two parameters vanish and the third is a unit, reducing étale locally to $ab=\pi$. At a triple point all three vanish. Hence the local nearby-cycle ranks are respectively

$$
1,\qquad (1,1),\qquad (1,2,1)
$$

in cohomological degrees beginning at zero.

On the model with labeled chain vertices, choose one of the four globally labeled raw branch
components, the corner locally cut out by $(x,u)$. It is a Weil divisor which is Cartier away
from the product-node locus. Let $\mathcal I$ be its coherent ideal sheaf. On the framed
local-model cover, $\mathcal I$ pulls back to $(x,u)$. Blowup commutes
with this smooth base change, so Proposition 6.1 proves on a smooth surjective cover that
$\operatorname{Bl}_{\mathcal I}\mathscr S_{\mathrm{Iw},\mathrm{Iw}}$ is regular and strictly
semistable; those properties descend. Away from the product-node locus the selected divisor
ideal is invertible, so the blowup is an isomorphism. If no global labeling has been chosen,
pass to the finite cover on which the component divisors are labeled, perform the construction
equivariantly, and retain the descent action as in Chapter 7.

### 6.4 Components, double curves, and triple points

Let $X$ be the geometric special fiber of the distinguished good surface and, for
$(\epsilon_1,\epsilon_2)\in\{F,V\}^2$, let $X_{\epsilon_1\epsilon_2}$ be the four labeled
ordinary or Frobenius-twisted copies of $X$ required by those labels. At the selected
$\mathbf F_p$-place they have the same underlying good fiber. On $X$ write

$$
Z_a=V(\operatorname{Ha}_a),\qquad
P=Z_1\cap Z_2.
\tag{6.6}
$$

The independent displays have parameters $t_1,t_2$, so $Z_1$ and $Z_2$ are smooth Cartier
divisors meeting transversely and $P$ is a reduced finite étale scheme. Their classes and
intersection number are

$$
[Z_a]=(p-1)c_1(\omega_a),\qquad
\#P(\bar k)=(p-1)^2
\int_Xc_1(\omega_1)c_1(\omega_2).
\tag{6.7}
$$

For each $\epsilon=(\epsilon_1,\epsilon_2)$, use the Frobenius-twisted source whenever a
Verschiebung label occurs, as in Section 4.3, and quotient successively by the resulting partial
Frobenius or Verschiebung kernels prescribed by $\epsilon_a$. The two kernels lie in orthogonal
idempotent packets, so the quotients commute and the polarization quotient criterion of Book 38
applies in either order. This gives a proper map from $X_\epsilon$ to the correspondingly
labeled branch. On the locus where both Hasse invariants are nonzero, the independent
rank-two classifications give exactly four choices. If only $\operatorname{Ha}_a$ vanishes,
the $F_a$ and $V_a$ choices coalesce, and if both vanish all four coalesce. The framed product
of $k[[x,y]]/(xy)$ and $k[[u,v]]/(uv)$ proves scheme-theoretically that these are all minimal
primes and that each has multiplicity one. On each reduced minimal-prime quotient, the product
of the two one-packet completed maps from Section 4.3 is an isomorphism after retaining the
required Frobenius-twist labels. Hence the four proper maps are quasi-finite, therefore finite,
and finite birationality from the normal $X_\epsilon$ proves that they are precisely the
normalizations of the four global Kottwitz--Rapoport components.

Scheme-theoretically, the raw Kottwitz--Rapoport stratification can be written without further
labels. For $J\subset\{1,2\}$ put

$$
Z_J^\circ=
\left(\bigcap_{a\in J}Z_a\right)
\setminus\left(\bigcup_{b\notin J}Z_b\right),
$$

with $Z_\varnothing^\circ=X\setminus(Z_1\cup Z_2)$. Identify the Frobenius-twisted copies
through their radicial degeneracy maps and the reduced Hasse embeddings established by the
display calculation. Over $Z_J^\circ$ the $F_a$ and $V_a$ labels then coalesce exactly for
$a\in J$ and remain distinct for $a\notin J$. Hence there are
$2^{2-|J|}$ strata over $Z_J^\circ$, and their closures are obtained by allowing additional
Hasse invariants to vanish. This lists every KR stratum and every closure relation; it is stable
under geometric Frobenius and prime-to-$p$ Hecke maps.

Adjacent components differing in direction $a$ meet along the corresponding Hasse copy of
$Z_a$; changing between source and opposite dual-chain parameterizations composes that embedding
with the relevant Frobenius universal homeomorphism. All four meet exactly over $P$. The
good-source degeneracy map is the identity only on the all-F normalization; on a normalization
with V labels it contains the corresponding Frobenius twist. The quotient maps land in the
adjacent parahoric polarization types and reverse these roles under the opposite-chain
parameterization. Thus the raw
incidence square is not only a local label picture: it is the following global
Frobenius-stratum diagram, with one copy of $Z_a$ on every edge and one square for every point
of $P$:

    (0,1) -------- (1,1)
      |                |
      |                |
    (0,0) -------- (1,0)

Choose the labels so that the global blowup ideal has local generator pair $(x,u)$ and selects
the diagonal $(0,0)$--$(1,1)$. If $\beta_\epsilon$ denotes the component modification, then

$$
\widetilde Y_{00}=\operatorname{Bl}_{P}X_{00},\qquad
\widetilde Y_{11}=\operatorname{Bl}_{P}X_{11},\qquad
\widetilde Y_{01}=X_{01},\qquad
\widetilde Y_{10}=X_{10}.
\tag{6.8}
$$

The small resolution adds no surface component. Every original edge curve is its strict
transform, which is isomorphic to $Z_a$ because blowing up a smooth curve at a Cartier point
does not change it. For every $z\in P$ the chosen opposite components meet along a new curve
$E_z\simeq\mathbf P^1$. That curve has two distinguished points; at one it meets the
$(0,0)$, $(1,0)$, $(1,1)$ components, and at the other it meets the
$(0,0)$, $(0,1)$, $(1,1)$ components. These are exactly the two triple points over $z$.
Consequently

$$
Y^{(1)}=\coprod_\epsilon\widetilde Y_\epsilon,
$$

$$
Y^{(2)}=Z_1^{\amalg2}\amalg Z_2^{\amalg2}
\amalg\coprod_{z\in P}E_z,
\qquad
Y^{(3)}=P\amalg P.
\tag{6.9}
$$

All terms in (6.9) are smooth. The exceptional $\mathbf P^1$ is a double curve, not a component
of the special-fiber divisor.

The cycle classes are equally explicit. On either blown-up diagonal component,

$$
[\widetilde Z_a]=\beta^*[Z_a]-\sum_{z\in P} [E_z],
\qquad E_z^2=-1,
\tag{6.10}
$$

where a summand is included only when $z$ lies on the displayed connected curve; on an
unmodified component its adjacent divisor class is $[Z_a]$. On a Frobenius-twisted
normalization this notation means the actual twisted Hasse-divisor class; the universal
homeomorphism identifies prime-to-$p$ cohomology groups but does not erase the degree in
pullback--trace. If $D$ is any double curve and
$T_D$ is its triple-point divisor, restriction of the principal fiber gives the corrected
normal-bundle identity

$$
N_{D/Y_i}\otimes N_{D/Y_j}\otimes\mathcal O_D(T_D)
\simeq\mathcal O_D.
\tag{6.11}
$$

For $E_z$, both normals are $\mathcal O_{\mathbf P^1}(-1)$ and $T_{E_z}$ consists of its two
distinguished points, verifying (6.11). For an old edge, (6.10) gives its two normal classes and
the same identity. Every Gysin map is cup product with these classes followed by pushforward,
and every restriction is pullback along the displayed $Z_a$ or $E_z$ inclusion. Blowup at points
does not change $H^1$ of a component and $H^1(E_z)=0$; after partial-Frobenius identification,
the entire odd restriction matrix is therefore the four-vertex matrix written in (10.15).

Geometric Frobenius fixes the $F/V$ labels at the completely split place, acts on $Z_a$ and
$P$, and sends $E_z$ to $E_{Fz}$ with its two incidence points. Prime-to-$p$ level changes have
the same functorial action. This completes the global component, incidence, normal-bundle, and
cycle-class comparison for the two-direction datum.

### 6.5 The choice of diagonal

Blowing up $(y,u)$ gives the other small resolution. The two resolutions are related by a flop of the exceptional $\mathbf P^1$. Neither is canonically preferred by the singular local equation. A labeled PEL lattice chain can prefer one through its orientation; without a label, both are auxiliary semistable models.

The generic fibers are canonically identical, so their $E_\ell$-cohomology and monodromy
representation are identical. On the special side, changing the diagonal performs a diagonal
flip of the dual square. Theorem 7.2 constructs, after one further even ramified base change, a
regular reduced common subdivision that is invariant even when a descent element exchanges the
two diagonals. Thus cellular cohomology is unchanged, and the two weight complexes are connected
by pull--push through an actual common toroidal modification. Proper functoriality of nearby
cycles identifies their abutments. Integral lattices require more care: the comparison must use
the actual pull--push maps and cannot be inferred only from equality of rational ranks.

## 7. Base change, alterations, and descent

### 7.1 What finite extension changes

Let $R'/R$ be a finite extension of ramification index $e$ and residue degree $f$. A unit-thickness node becomes thickness $e$:

$$
xy=\pi\quad\rightsquigarrow\quad xy=u(\pi')^e.
\tag{7.1}
$$

An unramified extension can split components and nodes but does not change geometric thickness. A ramified extension scales every edge length. If the extension is used to kill a finite inertial action, the resulting strict semistable model computes the unipotent operator only after restriction to $G_{K'}$; the original representation must retain the finite descent action.

Normalization is mandatory after base change. Normality and regularity need not survive a ramified tensor product. The sequence is

$$
\mathscr X_{R'}
\longleftarrow (\mathscr X_{R'})^{\mathrm{nor}}
\longleftarrow \mathscr X^{\mathrm{ss}},
\tag{7.2}
$$

where the last arrow is the explicit resolution appropriate to the local charts.

### 7.2 Resolving thick curve nodes

After replacing the base by the completed strict henselian DVR, consider
$A_n=\widehat{R^{\mathrm{sh}}}[[x,y]]/(xy-\pi^n)$. For $n>1$, blow up the branch ideal
$(x,\pi)$ and take the strict transform, normalizing if necessary. On the $x$-chart the strict
transform is regular; on the $\pi$-chart it has equation $x_1y=\pi^{n-1}$. Thus one chart reduces
the exponent by one and the step creates an exceptional rational component. Repeating produces

    Y_0 -- E_1 -- E_2 -- ... -- E_(n-1) -- Y_1.

Each adjacent pair has local equation $ab=\pi$. Induction on $n$ proves termination because the
remaining exponent drops by one at each step. The exceptional components have genus zero and
valence two.

A cycle crossing the original edge crosses every one of the $n$ unit segments with the same coefficient. Hence its pairing contribution becomes

$$
a_eb_e+\cdots+a_eb_e=n a_eb_e.
\tag{7.3}
$$

This proves both invariance under subdivision and scaling of the integral monodromy pairing under ramified base change.

### 7.3 Semistable alteration in the present surface charts

For one bad direction, first resolve every thick node as in Section 7.2 and take its product with the smooth direction. Every chart is then $ab=\pi$ with one smooth parameter.

For two bad directions, resolve the two thicknesses to unit chains. At each product of crossing points the local ring is again (6.1). Apply one of the small resolutions of Section 6.2. Because the singular points are disjoint after the chain resolutions, these blowups commute. The outcome is a proper strict semistable surface over $R'$.

**Proposition 7.1.** Suppose that the parahoric PEL model is proper under Theorem 2.2 and that,
after a finite extension, its local model is a product of one or two split rank-two chains with
equations of the form $xy=(\pi')^n$. Then normalization, chain resolution, and the small
resolutions above produce a proper strictly semistable model. If the finite extension changed
the generic field, the resulting morphism to the original model is a semistable alteration; it
is a modification only after base change.

**Proof.** The curve-chain construction gives unit nodal charts. Products with smooth charts are strict semistable. Products of two nodes have only the isolated singularities (6.1), and Proposition 6.1 resolves each into charts $abc=\pi'$. All operations are projective. They are isomorphisms on the generic fiber after the chosen field extension. Properness is preserved under base change, normalization is finite over an excellent base, and projective modification preserves properness. $\square$

No general semistable reduction theorem for arbitrary threefolds is hidden here. The proposition is proved only for the displayed toroidal charts.

### 7.4 Finite descent data

Assume $K'/K$ is finite Galois with group $\Delta$ and $\mathscr X^{\mathrm{ss}}/R'$ is a chosen semistable alteration. The action of $G_K$ on generic cohomology is described by a Weil--Deligne pair $(r,N)$ after restricting to an open inertia subgroup. For an element $w$ of the Weil group,

$$
r(w)Nr(w)^{-1}=|w|N.
\tag{7.4}
$$

Here $|w|$ is the unramified norm character, with the Tate twist understood. In particular the finite inertial action commutes with $N$. It permutes components, reverses oriented edges when branches are exchanged, and acts on the cohomology of every stratum.

Different semistable resolutions need not admit the group action without further blowups. For the
displayed toroidal charts this issue has a direct finite construction.

**Theorem 7.2 (finite invariant regular subdivision for the displayed charts).** Let a finite
group act on the raw models of Proposition 7.1, permuting components and possibly exchanging the
two small resolutions at product-node points. After a further finite separable extension of even
ramification index, followed by normalization, there is a projective equivariant toroidal
modification which:

1. dominates every translate of every chosen chain or small resolution;
2. is regular with reduced strict-normal-crossings special fiber; and
3. is obtained from a finite invariant subdivision of the interval and square complexes already
   displayed in Chapters 6--7.

After replacing the field extension by its Galois closure, the assertion holds for the full new
descent group. In particular no equivariant resolution theorem for arbitrary threefolds is being
used.

**Proof.** We first treat the interval factors. The cone slice of
$xy=(\pi')^n$ at valuation one is an interval of integral length $n$. The chain resolution of
Section 7.2 inserts its integral vertices. For a finite family of translates, take the union of
their vertex sets. If they were written over different intermediate ramified fields, first
choose one ramification index clearing the finitely many rational denominators. Insert every
remaining integral point between consecutive chosen vertices. The result is a finite invariant
union of unit intervals. Its toric charts are exactly $ab=\pi''$, so it is regular and has
reduced special fiber. Taking a product with a smooth direction changes nothing.

It remains to reconcile the diagonals in a unit product square. The valuation lattice of

$$
xy=\pi',\qquad uv=\pi'
$$

may be written

$$
N=\{(a,b,c,d)\in\mathbf Z^4:a+b=c+d\},
\qquad h(a,b,c,d)=a+b.
\tag{7.5}
$$

The slice $h=1$ is a square. Its four corner rays, in cyclic order, are

$$
r_{00}=(1,0,1,0),\quad r_{01}=(1,0,0,1),\quad
r_{11}=(0,1,0,1),\quad r_{10}=(0,1,1,0).
\tag{7.6}
$$

The two small resolutions are the two diagonal triangulations of this square. Make an additional
base change of ramification index two. A monomial valuation on the normalized base change is
integral exactly when its old height is divisible by two, because its value on the new
uniformizer is half its value on $\pi'$. Thus the saturated valuation lattice and its new height
map are

$$
N_2=\{w\in N:h(w)\in2\mathbf Z\},\qquad h_2=h/2,
\tag{7.7}
$$

the new height-one square has corners $2r_{ij}$. Add the midpoint of each boundary edge and the
center

$$
m_{ij,i'j'}=r_{ij}+r_{i'j'}\qquad\text{for adjacent corners},
\qquad
c=r_{00}+r_{11}=r_{01}+r_{10}.
\tag{7.8}
$$

Join $c$ to the eight consecutive boundary vertices. This gives eight triangles. It refines
both diagonal triangulations: each old diagonal is the union of two edges from its endpoints to
$c$, and subdividing the boundary edges only refines the adjacent triangles. The construction
is fixed by every automorphism of the square, including both diagonal reflections.

We verify regularity rather than infer it from the picture. The three vectors
$r_{00},r_{01},r_{10}$ form a basis of $N$, while
$r_{11}=-r_{00}+r_{01}+r_{10}$. The lattice $N_2$ has index two in $N$. For one of the eight
cones, its primitive generators are

$$
2r_{00},\qquad r_{00}+r_{01},\qquad c=r_{01}+r_{10}.
$$

Their determinant in the displayed basis of $N$ has absolute value two. It therefore has
absolute value one relative to $N_2$. The dihedral symmetries of the square carry this cone to
the other seven, so every cone is unimodular. All its primitive rays have $h_2=1$. The affine
chart dual to any such cone is consequently regular. In the dual basis the base monomial has
exponent $h_2(v)=1$ on each of the three primitive ray generators $v$, so its map to the new
trait has, after completion, the form

$$
a b c=\pi''
$$

with one or more of $a,b,c$ invertible off the deepest stratum. Thus the special fiber is reduced
and strict normal crossings.

Finally, these subdivisions are geometric. For clarity, consider a toric cone with primitive
rays $v_1,\ldots,v_s$ and the closed stratum cut out by the corresponding boundary parameters.
On a blowup chart one of those parameters generates the pulled-back ideal, so the ratios of all
the other parameters to it become regular. Passing to exponent monoids adds the associated
inequalities; saturation replaces the original cone by the cones obtained after inserting the
ray through $v_1+\cdots+v_s$. Thus the normalization of this stratum blowup is exactly the star
subdivision at that ray. This chart calculation also proves that the construction commutes with
restriction to a face.

For the square, the sum of its four primitive corner rays has the direction of $c$, so the first
normalized stratum blowup inserts the center. On each boundary face, the sum of its two primitive
corner rays has the direction of the midpoint in (7.8), so four further normalized stratum
blowups insert the boundary midpoints. After the center has been inserted those boundary faces
are distinct, and their star subdivisions commute. Ordinary blowups are projective,
normalization is finite here, and a composite remains projective. Since the resulting fan
refines either diagonal fan, the toric gluing maps give morphisms to both original small
resolutions.

Apply the same construction to every product square. The interval vertex set, the set of square
centers, and the set of boundary faces are complete group orbits. Their defining monomial ideals
are therefore invariant. The universal property of a blowup lifts the group action, and
functoriality of normalization lifts it uniquely to the normalized blowup. Face compatibility
from the preceding chart calculation glues the local actions. There are finitely many strata,
hence the construction terminates. Passing to a Galois closure and repeating the same orbit
construction gives equivariance for the full descent group. $\square$

The theorem supplies the common equivariant domination needed for descent. Proper pullback and
trace on nearby cycles then compare the cohomology of every translate. One must still not
quotient the dual graph or dual complex before forming its signed chain complex: stabilizers and
orientation reversal affect invariants.

There is a second finite operation, distinct from residue-field descent. Within a fixed
quaternionic PEL presentation, Book 130 imports the Book 205 central and level deck
representatives. At the selected catalog-good place those representatives are $p$-integral and
have prime-to-$p$ kernels. They therefore identify the presentation's $p$-divisible groups and
commute with every split idempotent and with $F,V$. A central representative acts scalarly on
the active reduced packet and hence preserves the oriented multichain; an ordinary
prime-to-$p$ level deck map leaves the local $p$-level unchanged. These, and only those imported
deck maps whose $p$-component preserves the oriented parahoric, act on the same fine parahoric
model and preserve the Hasse and
Kottwitz--Rapoport strata proved above. A free effective quotient is finite etale and remains
regular with semistable charts étale locally. It is strict in the global convention of Section
1.2 only if no deck orbit identifies two geometric branch components into a self-node; otherwise
the ordered-strata calculation stays on the fine cover with its descent action. With
stabilizers, nearby cycles are likewise computed equivariantly on the smooth proper quotient
stack or the fine cover; the coarse finite scheme may have quotient singularities. A universal
PEL family descends only with the genuine isomorphism linearization and trivial-stabilizer
conditions recorded in Book 130.

An integral representative which merely normalizes the hyperspecial group need not preserve the
chosen Borel line. It then carries this model to the correspondingly translated parahoric model,
just as a nonpreserving prime-to-$p$ Hecke element carries a selected component union to its
translate; no self-action is inferred.

The quaternionic-line--binary-unitary common refinement is weaker. Book 130 compares the good
base curves by finite maps but explicitly does not identify, or canonically isogenize, their
universal abelian schemes. Accordingly this book constructs the parahoric model separately in
each admitted presentation and obtains the same rank-two charts and rational monodromy
formulas; it does not assert a canonical cross-presentation isomorphism of the integral
parahoric functors. Such an isomorphism would require an additional integral tensor or
$p$-divisible-group identification. This is the exact presentation-independence boundary.

## 8. Strata and incidence complexes

### 8.1 The ordered strata

For a strict semistable model $Y=\bigcup_{i\in I}Y_i$, choose an order on $I$. The scheme
$Y^{(a)}$ is the disjoint union indexed by the $a$-element subsets of $I$; its intersections are
closed and are not stripped of their deeper incidence loci. In a curve only $Y^{(1)}$ and
$Y^{(2)}$ occur. In a surface, $Y^{(1)}$ consists of surfaces, $Y^{(2)}$ of double curves, and
$Y^{(3)}$ of triple points.

The disjoint-union convention matters. If two components meet in several connected curves, each curve is a separate edge in the dual complex. If a component meets itself after descent, the two geometric branches still give the correct incidence maps after passage to $\bar k$.

### 8.2 Restriction and Gysin maps

Dropping one component from an intersection gives closed immersions between strata. Alternating pullbacks define restriction maps $\rho$; alternating codimension-one pushforwards define Gysin maps $\gamma$. Their signs satisfy

$$
\rho^2=0,\qquad \gamma^2=0,\qquad
\rho\gamma+\gamma\rho=0.
\tag{8.1}
$$

The first two identities pair the two orders in which components can be dropped. The mixed identity follows from the self-intersection formula and the relation that the total special fiber is principal. Poincaré duality makes $\rho$ and $\gamma$ adjoint, up to the displayed signs and Tate twists.

These maps are computational, not decorative. A local double curve supplies possible vanishing cycles, but a class contributes to global monodromy only if it survives the adjacent restriction and Gysin maps.

### 8.3 The curve graph and the surface dual complex

For a curve, the complex

$$
H^0(Y^{(1)},E_\ell)
\xrightarrow{\rho}
H^0(Y^{(2)},E_\ell)
\tag{8.2}
$$

is the cellular cochain complex of the dual graph $\Gamma$. Its cokernel is $H^1(\Gamma,E_\ell)$, and the kernel of the dual Gysin map is $H_1(\Gamma,E_\ell)(-1)$.

For a surface, the degree-zero restriction row

$$
H^0(Y^{(1)})\longrightarrow H^0(Y^{(2)})
\longrightarrow H^0(Y^{(3)})
\tag{8.3}
$$

is the cellular cochain complex of the dual complex $\Delta(Y)$. Consequently the extreme
$E_2$ terms relevant to middle cohomology are

$$
H^2(\Delta(Y),E_\ell),
\qquad
H_2(\Delta(Y),E_\ell)(-2).
\tag{8.4}
$$

The dual complex supplies the source and target of $N^2$. For an arbitrary semistable surface
their common dimension need not equal the rank of the induced map. For the actual
Frobenius--Kottwitz--Rapoport complex of Section 6.4, the map and its nondegenerate pairing are
computed next. It still does not control all of $N$: $H^1$ of double curves contributes
additional length-two blocks.

### 8.4 A product-incidence calculation

We compute the actual complex in (6.9), without assuming that the surface is a global product.
For clarity first take one geometrically connected good component. Let

$$
\mathcal A_a=\pi_0(Z_a),
$$

and form the bipartite graph $B$ with vertex set
$\mathcal A_1\amalg\mathcal A_2$ and one edge for every geometric point $z\in P$, joining the
components of $Z_1$ and $Z_2$ which contain $z$. Before the diagonal subdivision, each $z$ is a
square $2$-cell. Its cellular boundary is the difference of the two copies of its horizontal
edge plus the difference of the two copies of its vertical edge. Therefore

$$
H_2(\Delta,E_\ell)\simeq H_1(B,E_\ell),
\tag{8.5}
$$

and

$$
h_2:=\dim H_2(\Delta,E_\ell)
=|P|-|\mathcal A_1|-|\mathcal A_2|+c(B),
\tag{8.6}
$$

where $c(B)$ counts connected components, with an isolated component of either $Z_a$ retained
as an isolated vertex. The triangulation of Section 6.4 subdivides every square and hence leaves this
homology unchanged. With a disconnected good fiber, the same statement holds componentwise; or,
without any connectivity convention, $h_2$ is the nullity of the explicit signed square-boundary
matrix determined by the degeneracy maps.

The extreme monodromy map can now be calculated, not hypothesized. Give a square coefficient
vector $c=(c_z)_{z\in P}$ the unit-thickness form

$$
Q_2(c,d)=2\sum_{z\in P}c_zd_z.
\tag{8.7}
$$

The factor $2$ is the two orders of applying the two local logarithms; equivalently,
$(N_1+N_2)^2=2N_1N_2$. The restriction--Gysin identities make the map
$H_2(\Delta)(-2)\to H^2(\Delta)(-2)$ induced by $N^2$ precisely the restriction of (8.7) to
the kernel of the square-boundary matrix. That kernel is defined over $\mathbf Q$, and the
ordinary dot product is positive definite after embedding in $\mathbf R$. Its restriction is
therefore nonsingular over $\mathbf Q$, hence over every $E_\ell$. It follows unconditionally
that

$$
\operatorname{rank}N^2=h_2.
\tag{8.8}
$$

On the integral cellular complex, the corresponding geometric map is twice the restricted
integer Gram matrix, with edge-thickness factors after ramification. After taking the saturated
integer square-cycle lattice, its Smith cokernel is the extreme incidence discriminant. This is
the integral map on a chosen cohomology lattice only when integral nearby-cycle comparison is
torsion-free and saturated in the adjacent degrees. In particular, at $\ell=2$ the factor $2$
is visible in the stratum matrix, while preservation of a chosen lattice by the logarithm still
requires the check of Section 10.5. Formula (8.6) also shows why triple points alone do not force
$N^2$: the corresponding square coefficients must satisfy both families of incidence relations.

## 9. Nearby cycles on the bad models

### 9.1 Local nearby-cycle stalks

Let $x$ lie on exactly $r$ components of a strict semistable model. Put

$$
C_x=\operatorname{coker}\left(
E_\ell\xrightarrow{1\mapsto(1,\ldots,1)}E_\ell^r
\right).
$$

The local semistable calculation gives

$$
(R^a\Psi E_\ell)_x
\simeq\bigwedge^a C_x(-a),
\qquad 0\le a\le r-1.
\tag{9.1}
$$

**Proof.** In the chart $t_1\cdots t_r=\pi$, the geometric generic punctured neighborhood is tamely equivalent to a torus of rank $r-1$. The product equation supplies the one diagonal relation among Kummer classes. Continuous cohomology of its maximal pro-$\ell$ tame group is the exterior algebra on $C_x(-1)$. Smooth coordinates contribute no higher cohomology. $\square$

Wild inertia acts trivially in a strict semistable chart. The action on each sheaf $R^a\Psi$ is trivial, but the full complex can have nontrivial unipotent inertia through extensions among these sheaves.

### 9.2 The quaternionic curve complex

At a smooth point of the special curve, only $R^0\Psi=E_\ell$ occurs. At a node,

$$
R^0\Psi=E_\ell,
\qquad
R^1\Psi=E_\ell(-1).
\tag{9.2}
$$

Globally $R^1\Psi$ is a skyscraper sheaf on the geometric node set. The weight complex glues those generators through the vertex--edge incidence map. Consequently one node need not give one global monodromy block: separating nodes die in the graph homology.

Proper comparison identifies

$$
R\Gamma(Y,R\Psi E_\ell)
\simeq R\Gamma(C_{\bar K},E_\ell).
\tag{9.3}
$$

The specialization map from ordinary $H^1(Y)$ lands in $\ker N$, and in the strict semistable curve case it identifies $H^1(Y)$ with inertia invariants.

### 9.3 The one-direction surface complex

For $Y=Y_0\cup Y_1$ with double curve $D$, the only higher local sheaf is $R^1\Psi$, locally constant of rank one along $D$ with twist $(-1)$. There is no $R^2\Psi$ because there are no triple points.

In degree two, candidate monodromy classes arise from $H^1(D)(-1)$ and their duals. The relevant maps are the alternating restrictions

$$
H^1(Y_0)\oplus H^1(Y_1)\longrightarrow H^1(D)
\tag{9.4}
$$

and the adjoint Gysin map

$$
H^1(D)(-1)\longrightarrow
H^3(Y_0)\oplus H^3(Y_1).
\tag{9.5}
$$

The surviving quotient on the restriction side is dual to the surviving kernel on the Gysin
side. Monodromy is the map induced by the identity of $H^1(D)$ between them. Section 10.4
computes its rank as the dimension of $H^1(D)$ minus twice the restriction rank plus the rank of
an explicit cup-product Gram matrix.

### 9.4 The two-direction surface complex

At a double curve the local stalks are $E_\ell$ and $E_\ell(-1)$. At a triple point they are

$$
E_\ell,\qquad E_\ell(-1)^2,\qquad E_\ell(-2)
\tag{9.6}
$$

in degrees zero, one, and two. The two degree-one generators correspond to three branches modulo their sum; their exterior product gives degree two.

Globally, triple-point generators are joined to double-curve and component cohomology by
$\rho+\gamma$. The extreme $E_2$ survivors are (8.4), and the induced map between them is the
restricted Gram form (8.7). Hence its rank is (8.6), not the number of triple points. The odd
survivors are governed by the four-vertex restriction matrix (10.15).

The small resolution replaces the non-semistable fourfold meeting by two triple-incidence simplices. Formula (9.1) now applies everywhere. Proper birational comparison with the common generic fiber proves that the resulting abutment is the cohomology of the original parahoric Shimura surface.

### 9.5 Coefficients from PEL geometry

Let $\mathcal L_\ell$ be a lisse $E_\ell$-sheaf obtained by an integral algebraic construction from the universal prime-to-$p$ Tate module, and suppose it extends lisse over the chosen semistable model. Then

$$
(R^a\Psi\mathcal L_\ell)_x
\simeq \mathcal L_{\ell,x}\otimes
\bigwedge^a C_x(-a).
\tag{9.7}
$$

This follows by trivializing $\mathcal L_\ell$ étale locally and applying (9.1). If the universal abelian scheme itself has only semiabelian reduction and the coefficient sheaf is ramified along a component, (9.7) is false; its inertia complex must be combined with the geometric Kummer complex. Constant coefficients, which are the inputs for the following cohomological realizations, have no such defect.

Integral coefficients require saturation checks. The local groups in (9.1) are free over $\mathbf Z/\ell^n$, but global kernels and cokernels of incidence maps can have torsion.

## 10. Weight and monodromy filtrations

### 10.1 The logarithm of inertia

On a strict semistable model inertia is unipotent. For $\sigma$ in a sufficiently small open subgroup of inertia,

$$
\rho(\sigma)=\exp(t_\ell(\sigma)N).
\tag{10.1}
$$

Thus for curves $N^2=0$ and

$$
\rho(\sigma)=1+t_\ell(\sigma)N,
$$

while for surfaces $N^3=0$ and

$$
\rho(\sigma)=1+t_\ell(\sigma)N+
\frac{t_\ell(\sigma)^2}{2}N^2.
\tag{10.2}
$$

The nilpotence bounds follow from the maximum number of components meeting: two for curves and three for surfaces. At $\ell=2$, (10.2) is a rational formula; preservation of a chosen lattice is not automatic because of the denominator.

### 10.2 Curves: three graded pieces

For $V=H^1(C_{\bar K},E_\ell)$, the weight spectral sequence yields

$$
\operatorname{gr}_0^M V=H^1(\Gamma,E_\ell),
$$

$$
\operatorname{gr}_1^M V=
\bigoplus_{v}H^1(Y_v,E_\ell),
$$

$$
\operatorname{gr}_2^M V=
H_1(\Gamma,E_\ell)(-1).
\tag{10.3}
$$

There are no possible higher differentials in total degree one. The graph pairing identifies

$$
N:\operatorname{gr}_2^M V
\xrightarrow{\sim}
\operatorname{gr}_0^M V(-1).
\tag{10.4}
$$

Hence this is the monodromy filtration centered at one and

$$
\operatorname{rank}N=b_1(\Gamma).
\tag{10.5}
$$

The component cohomology is killed by $N$. It contributes unramified length-one blocks, while every graph cycle contributes one length-two block.

### 10.3 Surfaces: five possible graded pieces

For $V=H^2(S_{\bar K},E_\ell)$, write $W_\bullet$ for the filtration induced by the weight
spectral sequence. When that sequence degenerates at $E_2$, it has possible indices $0$ through
$4$:

$$
0\subset W_0\subset W_1\subset W_2
\subset W_3\subset W_4=V.
\tag{10.6}
$$

The extreme terms are

$$
\operatorname{gr}_0^W V\simeq H^2(\Delta(Y),E_\ell),
$$

$$
\operatorname{gr}_4^W V\simeq
H_2(\Delta(Y),E_\ell)(-2).
\tag{10.7}
$$

The odd terms are the surviving restriction and Gysin subquotients of $H^1(Y^{(2)})$. The middle term contains compatible classes in $H^2(Y^{(1)})$ and the triple-point correction. Monodromy has maps

$$
N:\operatorname{gr}_{a}^W\to
\operatorname{gr}_{a-2}^W(-1),
\qquad
N^2:\operatorname{gr}_4^W\to
\operatorname{gr}_0^W(-2).
\tag{10.8}
$$

The full $E_1$ complex, rather than a dimension slogan, determines these subquotients. This matters when component surfaces have nonalgebraic middle cohomology or double curves have positive genus.

### 10.4 The actual surface monodromy maps

Assume first that $k$ is finite. The component surfaces and curves are smooth and proper, so
their cohomology is pure of its usual weight. Tate twists shift weights by two. Terms of
different weights admit no nonzero Frobenius-equivariant differential after semisimplifying
Frobenius, so the weight spectral sequence degenerates at $E_2$ in the present dimensions. We
will not infer a monodromy isomorphism from equal dimensions; we calculate its matrix.

Suppress twists while taking ranks and put

$$
V_1=H^1(Y^{(1)},E_\ell),\qquad
W_1=H^1(Y^{(2)},E_\ell),\qquad
\rho:V_1\longrightarrow W_1.
\tag{10.9}
$$

Let $J$ be the direct sum of the Poincaré pairings on the smooth double curves and put
$A=\operatorname{im}\rho$. Poincaré duality and the projection formula identify the alternating
Gysin map with the adjoint of $\rho$, so

$$
\ker\gamma=A^{\perp_J}.
\tag{10.10}
$$

On the $E_1$ page, local monodromy is the identity between the two copies of the double-curve
term. It therefore induces the concrete map

$$
\bar 1:A^{\perp_J}\longrightarrow W_1/A,
\qquad w\longmapsto w\bmod A.
\tag{10.11}
$$

Set

$$
b=\dim W_1,\qquad r=\dim A,\qquad
g=\operatorname{rank}(J|_A).
$$

Since $\dim A^{\perp_J}=b-r$ and
$\dim(A\cap A^{\perp_J})=r-g$, (10.11) has rank

$$
n_2=b-2r+g.
\tag{10.12}
$$

This is the exact number of length-two primitive monodromy blocks. It is a rank formula, not a
nondegeneracy assumption. The matrix $J|_A$ is equivalently the pulled-back Gram matrix
$\rho^\dagger J\rho$; its entries are compositions of the actual restrictions and Gysin maps,
so (5.7)--(5.9) and (6.10)--(6.11) compute it by cup product with the displayed Hasse and
exceptional cycle classes.

For one bad direction, use the Hasse identification, composed with partial Frobenius if quotient
normalizations were chosen, to identify the two labeled good-copy cohomologies and let

$$
r_1:H^1(X,E_\ell)\longrightarrow H^1(Z_1,E_\ell)
$$

be restriction. Then $\rho=[r_1,-r_1u]$, where $u$ is the partial-Frobenius cohomology
isomorphism. Put $s_1=\operatorname{rank}r_1$ and let $g_1$ be the rank of the form on
$\operatorname{im}r_1$ whose pulled-back expression is

$$
G_1(a,b)=\int_{Z_1}r_1(a)\smile r_1(b)
=\int_Xa\smile b\smile[Z_1].
\tag{10.13}
$$

The signs and $u$ insert the corresponding off-diagonal blocks in
$\rho^\dagger J\rho$ but do not change its rank. Hence

$$
n_2=b_1(Z_1)-2s_1+g_1.
\tag{10.14}
$$

For two bad directions, point blowups do not alter component $H^1$ and the exceptional
$\mathbf P^1$ curves have no $H^1$. Identify all four labeled good-copy groups with
$H=H^1(X,E_\ell)$ by the partial Frobenius maps and write
$r_a:H\to H^1(Z_a)$. Transport the Poincaré form on each of the four actual edge copies through
the same identifications and denote it by $\langle\ ,\ \rangle_{a,\epsilon}$. This notation
retains the nonzero partial-Frobenius degree appearing in pullback--trace; it is not silently
replaced by one unweighted form. After replacing the four vertex variables by

$$
x=a_{10}-a_{00},\quad y=a_{01}-a_{00},\quad
z=a_{11}-a_{10}-a_{01}+a_{00},
$$

the full alternating restriction map is

$$
\rho(x,y,z)=
\bigl(r_1x,r_1(x+z),r_2y,r_2(y+z)\bigr).
\tag{10.15}
$$

Let

$$
s_a=\operatorname{rank}r_a,
\qquad
s_{12}=\operatorname{rank}(r_1,r_2):H\longrightarrow
H^1(Z_1)\oplus H^1(Z_2).
$$

The three images in (10.15) meet trivially in the displayed coordinates, so

$$
\operatorname{rank}\rho=s_1+s_2+s_{12}.
\tag{10.16}
$$

Let $g_{12}$ be the rank of the following completely explicit form on the variables
$(x,y,z)$, modulo the kernel of (10.15):

$$
\begin{aligned}
G_{12}((x,y,z),(x',y',z'))={}&
\langle r_1x,r_1x'\rangle_{1,0}+
\langle r_1(x+z),r_1(x'+z')\rangle_{1,1}\\
&+\langle r_2y,r_2y'\rangle_{2,0}+
\langle r_2(y+z),r_2(y'+z')\rangle_{2,1}.
\end{aligned}
\tag{10.17}
$$

Each bracket is the curve cup-product pairing and can also be evaluated on $X$ using (6.7),
(6.10), and the projection formula. Equations (10.12), (10.16), and (10.17) give

$$
n_2=2b_1(Z_1)+2b_1(Z_2)
-2(s_1+s_2+s_{12})+g_{12}.
\tag{10.18}
$$

Here $b_1(Z_a)=\dim_{E_\ell}H^1(Z_a,E_\ell)$, summed over all connected components.

The even extreme map was computed in (8.7): it is nonsingular on the square-cycle space, so
the number of length-three blocks is $h_2$ of (8.6). The bottom and top extreme spaces are
therefore exhausted by those blocks. Purity and $E_2$-degeneration split the five distinct
Frobenius weights after scalar extension, and $FNF^{-1}=q^{-1}N$ lowers the weight by exactly
two. Hence there is no hidden filtration-skipping contribution to the rank: the even chains
contribute $2h_2$ and the odd map contributes (10.12). It follows that the full ranks are

$$
\operatorname{rank}N^2=h_2,
\qquad
\operatorname{rank}N=n_2+2h_2.
\tag{10.19}
$$

Over a general perfect residue field, (10.11) and (8.7) still compute the induced stratum maps,
but the rank sum in (10.19) uses the finite-field purity available at the selected place (1.1).
There the stratum filtration equals the monodromy filtration exactly when $J|_A$ is
nondegenerate, or $g=r$. Whether or not that equality holds, (10.12)--(10.19) give the actual
nilpotent operator's ranks and Jordan blocks at the catalogued split place.

### 10.5 Integral lattices and saturation

Let $T=H^m(X_{\bar K},\Lambda_\ell)$ modulo torsion. The rational monodromy filtration meets $T$
in a canonical lattice filtration, but the rational rank identities need not be integral
isomorphisms. For curves, the integral map is

$$
H_1(\Gamma,\mathbf Z_\ell)
\xrightarrow{q}
H_1(\Gamma,\mathbf Z_\ell)^\vee,
\tag{10.20}
$$

and its cokernel is the $\ell$-primary graph discriminant. For the surfaces here, the integral
stratum matrices are the identity-induced map underlying (10.11) and twice the restricted
square Gram matrix (8.7), with the cycle classes (5.9) and (6.10). To turn their Smith cokernels
into cokernels on $T$, first quotient torsion in every stratum group and verify that the relevant
kernels and images are saturated and that integral nearby-cycle comparison identifies the
resulting lattice with the chosen filtration on $T$. Under those hypotheses the Smith cokernels
are the odd and extreme incidence discriminants. Without them, this book asserts the rational
ranks and records the integral stratum matrices, but not a canonical integral surface
monodromy cokernel. At $\ell=2$, one must additionally verify that the logarithm itself preserves
$T$.

If a Hecke projector is defined only after dividing by an integer divisible by $\ell$, its image
lattice may be nonsaturated. The rational local type is still well defined. An integral type on
that rational summand means the Smith form on a separately specified stable lattice; it is not
manufactured by intersecting with a nonsaturated projector image.

## 11. Conductor and type for quaternionic curves

### 11.1 The conductor formula

For an $E_\ell$-representation $V$ of $G_K$, the Artin conductor exponent is

$$
a(V)=\dim V-\dim V^{I_K}+\operatorname{Sw}(V).
\tag{11.1}
$$

After quasi-unipotent reduction, write the Weil--Deligne representation as $(r,N)$. Then

$$
V^{I_K}=(\ker N)^{r(I_K)},
$$

so

$$
a(V)=\dim V-\dim(\ker N)^{r(I_K)}+
\operatorname{Sw}(r).
\tag{11.2}
$$

For a strict semistable model over $K$, $r$ is trivial on inertia and the Swan term vanishes. Hence

$$
a(V)=\operatorname{rank}N.
\tag{11.3}
$$

The simple formula is not valid before finite descent has been restored.

### 11.2 Graph computation at split semistable level

Apply (11.3) and (10.5) to the quaternionic curve:

$$
a\left(H^1(C_{\bar K},E_\ell)\right)
=b_1(\Gamma).
\tag{11.4}
$$

For two components meeting in $m$ points this is $m-1$. The local Euler polynomial is

$$
P(T)=\det\left(1-FT\mid\ker N\right).
\tag{11.5}
$$

Specialization identifies $\ker N$ with $H^1(Y,E_\ell)$. Its normalization sequence filters it by $H^1(\Gamma)$ and $\bigoplus H^1(Y_v)$, so Frobenius on both the incidence graph and the normalized components is needed to compute (11.5).

The conductor does not determine the component group. Thickness scales the integral pairing and can enlarge (4.9) while leaving $b_1(\Gamma)$ unchanged.

### 11.3 Two-dimensional constituents and special type

Let $W$ be a two-dimensional $G_K$- and Hecke-stable subquotient of $H^1$. Since $N^2=0$, either $N|_W=0$ or it has rank one. In the second case choose a basis $e_0,e_1$ with

$$
Ne_1=e_0,\qquad Ne_0=0.
\tag{11.6}
$$

If finite inertia is trivial, $W$ has one length-two unipotent block and

$$
a(W)=1.
\tag{11.7}
$$

Its Weil--Deligne type is special: after an unramified character twist, the nilpotent operator is the standard nonzero operator on a two-dimensional special representation. This is the precise geometric content behind the phrase “Steinberg type.” The twist and Frobenius eigenvalue are not determined by $N$ alone; they are read from $F$ on $\ker N$.

If $N|_W=0$, the semistable geometry only says that the unipotent part is absent. At strict level $W$ is unramified; after descent it may still have nontrivial finite inertia.

### 11.4 Finite and nonsplit descent

Suppose strict semistability is reached over $K'/K$. The finite group can permute graph vertices and edges, and can reverse an edge orientation. On the graph pieces,

$$
r(I_K)\curvearrowright H^1(\Gamma,E_\ell),
\qquad
r(I_K)\curvearrowright H_1(\Gamma,E_\ell)(-1),
$$

dually. Formula (11.2), not (11.4), gives the conductor over $K$.

A nonsplit multiplicative rank-two constituent still has nonzero $N$ and conductor one when its finite character is unramified, but Frobenius acts with the opposite sign on its graph line. A ramified quadratic finite character can increase the codimension of invariants without changing the rank of $N$. Wild descent contributes the Swan term. These distinctions are exactly why the local type is the pair $(r,N)$ together with Frobenius, rather than the integer conductor.

## 12. Conductor and type for unitary surfaces

### 12.1 Ranks of $N$ and $N^2$

Let

$$
V=H^2(S_{\bar K},E_\ell),
\qquad R_1=\operatorname{rank}N,
\qquad R_2=\operatorname{rank}N^2.
$$

If $n_j$ is the number of Jordan blocks of length $j$, elementary Jordan theory gives

$$
n_3=R_2,
\qquad n_2=R_1-2R_2,
\qquad n_1=\dim V-2R_1+R_2.
\tag{12.1}
$$

Indeed a length-three block contributes ranks $2$ and $1$ to $N$ and $N^2$, a length-two block
contributes $1$ and $0$, and a length-one block contributes neither. Thus $R_1$ alone does not
determine the local type. For the selected models, Sections 8.4 and 10.4 give unconditionally

$$
R_2=h_2,
\qquad R_1=n_2+2h_2,
\tag{12.2}
$$

where $n_2$ is the explicit Gram-rank expression (10.14) or (10.18).

### 12.2 One bad direction

Here $Y=Y_F\cup Y_V$ and $D\simeq Z_1$ on each connected good component. There are no
triple points; with several good components the dual complex is still a graph. Therefore

$$
N^2=0.
\tag{12.3}
$$

Let $r_1:H^1(X)\to H^1(Z_1)$ be the Hasse-divisor restriction and retain the ranks
$s_1,g_1$ of Section 10.4. Then the actual map is

$$
\ker\gamma\longrightarrow\operatorname{coker}\rho,
\qquad z\longmapsto z\bmod\operatorname{im}\rho,
\tag{12.4}
$$

and the rank calculation (10.12) gives

$$
\operatorname{rank}N
=b_1(Z_1)-2s_1+g_1.
\tag{12.5}
$$

The equality includes the possible radical $s_1-g_1$ of the cup-product form; it does not
replace the rank by the larger dimension of the restriction cokernel. With several good
components, use the full signed matrix (4.6) on $\pi_0$ and (10.9) on $H^1$; formula (10.12)
remains exact. If $Z_1$ is rational, its $H^1$ vanishes and so does this monodromy. If it has
positive genus, restrictions from the component surfaces can still remove all or part of it.

### 12.3 Two bad directions

The two-direction resolution can have both length-two and length-three blocks. For the global
strata of Section 6.4, let $B$ be the bipartite incidence graph of the two Hasse divisors. Then

$$
R_2=|P|-|\pi_0(Z_1)|-|\pi_0(Z_2)|+c(B),
\tag{12.6}
$$

and, with the notation of (10.16)--(10.18),

$$
\begin{aligned}
n_2={}&2b_1(Z_1)+2b_1(Z_2)
-2(s_1+s_2+s_{12})+g_{12},\\
R_1={}&n_2+2R_2.
\end{aligned}
\tag{12.7}
$$

These are numerical ranks of the displayed finite-dimensional restriction, cup-product, and
incidence matrices. The level and selected component union determine the genera, connected
components, intersection points, and matrix entries; no datum-independent integer could replace
them.

As a consistency check, if the entire stratum complex happens to factor as two curve complexes
with monodromies $N_1,N_2$, then

$$
N=N_1\otimes1+1\otimes N_2,
\qquad N^2=2N_1\otimes N_2.
\tag{12.8}
$$

This specializes (12.6) to the product of graph cycle ranks. Over $E_\ell$ the factor $2$ does
not affect rank; it remains in the integral stratum matrix at $\ell=2$, with the cohomology
lattice qualification of Section 10.5.

### 12.4 Jordan blocks, conductor, and Euler factor

At split strict semistable level,

$$
a(V)=R_1.
\tag{12.9}
$$

After finite descent,

$$
a(V)=\dim V-\dim(\ker N)^{r(I_K)}+
\operatorname{Sw}(r).
\tag{12.10}
$$

The local Euler polynomial is

$$
P(V,T)=\det\left(
1-FT\mid(\ker N)^{r(I_K)}
\right).
\tag{12.11}
$$

A complete report of the middle-degree type therefore includes

$$
r|_{I_K},\quad N,\quad R_2,\quad
\operatorname{Sw}(r),\quad
F\text{ on }(\ker N)^{r(I_K)}.
\tag{12.12}
$$

Two length-two blocks and one length-three block both give $R_1=2$, but only the latter has
$R_2=1$. Two representations with the same Jordan blocks can have different Euler factors. The
conductor is a necessary summary, not a classification.

### 12.5 The rank-two Hecke constituent

The rank calculation commutes with Hecke projection at the matrix level. If $e$ is a rational
idempotent stable under the Poincaré adjoint, apply $e$ to the domain and codomain of
(10.11), (10.15), and (8.7), and define $b_e,r_e,g_e,h_e$ there. Then

$$
n_{2,e}=b_e-2r_e+g_e,
\qquad
\operatorname{rank}N^2|_{eV}=h_e,
\qquad
\operatorname{rank}N|_{eV}=n_{2,e}+2h_e.
\tag{12.13}
$$

For an idempotent not fixed by the adjoint, the restriction of the Poincare form to $eW_1$ need
not be nondegenerate and must not be used as $J|_{eW_1}$. Instead pair the $e$-piece perfectly
with the $e^\dagger$-piece, take the two paired restriction matrices, and define
$b_e,r_e,g_e,h_e$ by their induced kernel--cokernel and extreme maps. The same rank statement
(12.13) then follows from that paired linear algebra. Independently, $N$ commutes with $e$, so
these ranks equal those of $N|_{eV}$ and $N^2|_{eV}$. Thus projected ranks are outputs of
explicit matrices, not extra hypotheses about a Hecke constituent.

Let $W$ be a two-dimensional Hecke-isotypic direct summand of $H^2$ stable under $G_K$.
Dimensional reasons force $N^2|_W=0$. Hence the alternatives are

$$
N|_W=0
\quad\text{or}\quad
\operatorname{rank}N|_W=1.
$$

At split strict level, the second has conductor one and special Weil--Deligne type after the appropriate unramified twist. The presence of length-three blocks in the full surface cohomology does not imply that a chosen two-dimensional constituent has $N^2\ne0$; it cannot. Instead such blocks must lie in larger Hecke constituents or decompose after coefficient extension into pieces on which the Hecke algebra is not simultaneously isolating two dimensions.

This observation is the precise bridge to local--global compatibility: geometry supplies the operator on full cohomology, while a Hecke projector determines which part of that operator belongs to the automorphic constituent.

## 13. Hecke correspondences and functorial monodromy

### 13.1 Extension away from the bad prime

Let $g\in G(\mathbf A_f^p)$. On the full canonical component union, changing prime-to-$p$ level
gives a diagram of parahoric PEL moduli schemes

$$
\mathscr X_K
\xleftarrow{p_1}
\mathscr X_{K\cap gKg^{-1}}
\xrightarrow{p_2}
\mathscr X_K.
\tag{13.1}
$$

For a smaller selected union, the right-hand target is its Hecke translate; (13.1) is a
self-correspondence only when $g$ preserves that union. All later uses of $T_g$ retain this
component-route condition.

The maps are finite étale at fine level. The universal prime-to-$p$ isogeny respects the $p$-adic lattice chain because its degree is prime to $p$. Hence both maps extend across the bad fiber and preserve the local-model stratification up to permutation.

More precisely, relative Frobenius and Verschiebung are natural in an isogeny defined over
$k$. A prime-to-$p$ PEL isogeny commutes with every split idempotent, so it carries each partial
Frobenius kernel, and each inverse-twist Verschiebung kernel used for the V label, isomorphically
to the corresponding kernel. It also identifies the
Hodge lines and their Verschiebung maps; hence it pulls $\operatorname{Ha}_a$ back to a unit
multiple of $\operatorname{Ha}_a$ and preserves every $Z_a$ and $P$. Thus it preserves the
global Frobenius--Kottwitz--Rapoport labels established in Sections 4.3--6.4, not merely the
abstract local-model labels.

The induced Hecke operator is the normalized pull--push

$$
T_g=(p_2)_*p_1^*.
\tag{13.2}
$$

Normalization factors must be fixed consistently with the generic Hecke algebra; multiplying an operator by a degree does not affect commutation with monodromy but does affect integral lattices.

### 13.2 Action on strata and nearby cycles

For the finite étale legs in (13.1), étale pullback and the finite trace act on

$$
R\Gamma(Y,R\Psi E_\ell)
$$

and commute with inertia, Frobenius, and $N$. Because these level maps preserve the local-model
strata and are étale, they meet every stratum transversely. Hence they induce finite maps of
component surfaces, double curves, and triple points, and projection formulas make their
pull--push commute with the restriction--Gysin differential.

In the two-direction case, the selected branch ideal pulls back to the same selected branch
ideal, and blowup commutes with flat base change. The correspondence therefore extends to the
small resolution. If a finite descent symmetry exchanges the two orientations, use the invariant
common subdivision of Theorem 7.2; proper pull--trace through that subdivision gives the same
operator on generic cohomology. On the curve graph the induced pull and trace commute with the
boundary (4.6) and are adjoint for the thickness pairing (4.8), so they act on the component
group cokernel (4.9). On surfaces they preserve (10.15), the cup-product forms (10.13) and
(10.17), and the square Gram form (8.7).

Consequently every $E_r$ page is a Hecke module and all monodromy filtrations are Hecke-stable. A calculation can therefore be performed before or after applying an idempotent, provided the idempotent is defined over the chosen coefficient field and the relevant functor is exact.

At the bad prime itself, a degeneracy correspondence can change the lattice chain and need not be finite étale. Its extension must be constructed from the explicit PEL isogeny diagram and checked against the local model. No general integral $p$-Hecke action is inferred here.

### 13.3 Projectors and coefficient fields

Let $\mathbb T^p$ be the commutative Hecke algebra away from $p\ell$. For an idempotent $e\in\mathbb T^p\otimes E_\ell$,

$$
eN=Ne,
\qquad eF=Fe.
\tag{13.3}
$$

Thus $(r,N)$ restricts to $eV$. If $e$ exists only after extending $E_\ell$, all dimensions and conductors are unchanged by that coefficient extension. If $e$ is only a generalized eigenspace projector rather than an idempotent in the integral algebra, the rational constituent is still well defined, but an integral direct summand need not be.

The conductor is additive on direct sums, so it may be computed separately on summands cut out
by genuine rational idempotents. It is **not** additive in arbitrary short exact sequences with
unipotent inertia: the nonsplit extension forming one length-two monodromy block has conductor
one, while its two one-dimensional unramified subquotients each have conductor zero. Consequently a
semisimplification that discards $N$ can change the conductor. Generalized Hecke eigenspaces are
safe only as an actual direct-sum decomposition preserved by $N$; extensions inside one such
eigenspace must be retained, and they can also matter for integral lattices.

### 13.4 The local--global compatibility package

For a Hecke-isolated constituent $W$, the geometry supplies the following data at the bad prime:

1. the finite inertial action on the relevant stratum subquotient;
2. the nilpotent map induced by the restriction--Gysin complex;
3. $\operatorname{rank}N$ and, in full surface degree two, $\operatorname{rank}N^2$;
4. the Artin and Swan conductors from (11.2) or (12.10);
5. geometric Frobenius on inertia invariants, hence the local Euler polynomial;
6. the unconditional curve graph cokernel and, for surfaces, the integral odd and extreme
   stratum matrices; their cokernels on a specified Hecke-stable cohomology lattice only after
   the torsion and saturation checks of Section 10.5.

For a two-dimensional constituent with trivial finite inertia, nonzero $N$ is precisely special type and gives conductor exponent one. Zero $N$ gives unramified type. With finite inertia present, the same dichotomy concerns only the unipotent part and must be combined with $r|_{I_K}$.

This package is geometric input to a local--global comparison theorem. Identifying it with the parameter of a particular automorphic representation also uses the automorphic decomposition and local representation theory; those are separate dependencies and are not assumed here.

## 14. The semistable bad-prime theorem

### 14.1 Unified construction and computation

**Theorem 14.1 (semistable models and monodromy).** Fix any catalogued PEL-exact quaternionic
curve datum of Book 127 or the standard unitary modèles étranges surface datum of Book 129, its
selected canonical component union and a neat prime-to-$p$ level. Choose the split place (1.1)
and impose the one- or two-direction parahoric chains (2.2a). Then:

1. the exact parahoric PEL functor is represented by a projective flat model carrying its
   universal isogeny chain, and its local model is scheme-theoretically one of (2.4a);
2. the quaternionic model is regular strictly semistable with charts $xy=p$; its two global
   Frobenius and Verschiebung branches are normalized by the labeled ordinary and
   Frobenius-twisted copies of the distinguished good fiber and meet at the reduced Hasse set
   $Z$, with graph boundary (4.6), monodromy pairing
   (4.8), and component group (4.9);
3. the one-direction unitary model is regular strictly semistable with charts $xy=p$ times a
   smooth parameter; its branch normalizations are the two labeled ordinary and
   Frobenius-twisted good surfaces, its double curve is the smooth partial Hasse divisor $Z_1$,
   and its restriction--Gysin maps are (5.7)--(5.9);
4. the two-direction raw unitary model has four labeled ordinary/Frobenius-twisted good-copy
   normalizations, adjacent Hasse curves $Z_1,Z_2$, and fourfold locus $P=Z_1\cap Z_2$; the
   chosen global branch blowup has the component and stratum decomposition (6.8)--(6.9), cycle
   classes (6.10), and strict charts $xyz=p$;
5. normalization, explicit thick-node resolution, and the small resolutions give the stated
   semistable alterations after finite base change; Theorem 7.2 gives an equivariant regular
   reduced common domination even when descent exchanges the diagonals;
6. nearby cycles are the exterior-algebra stalks (9.1) assembled by the displayed global
   restriction--Gysin complex;
7. on curve $H^1$, $N^2=0$, $\operatorname{rank}N=b_1(\Gamma)$, and the split conductor is
   $b_1(\Gamma)$; when the selected good fiber is geometrically connected this is
   $(p-1)\deg\omega_G-1$ and the geometric component group is
   $\mathbf Z/((p-1)\deg\omega_G)\mathbf Z$;
8. on surface $H^2$, $N^3=0$; one bad direction has rank (12.5), while two bad directions have
   the exact ranks (12.6)--(12.7), and the Jordan counts are (12.1); applying a Hecke idempotent
   gives the projected ranks (12.13);
9. at split strict level the Artin conductor is $\operatorname{rank}N$; after finite descent the
   exact formula is (12.10), with the signed component action, finite inertia, and Swan term
   retained;
10. geometric Frobenius and every prime-to-$p$ Hecke correspondence on the full union, or on a
    selected union which it preserves, preserve the partial
    $F/V$ kernels, Hasse strata, branch blowup, component pairing, restriction--Gysin complex,
    and the operators $N,N^2$; and
11. quaternionic central and level deck maps within a fixed presentation whose $p$-component
    preserves the oriented parahoric act on the fine model and its strata; free quotients remain
    semistable, while stack, coarse, and universal-family conclusions retain the exact
    qualifications of Chapter 7. Different PEL presentations have the same proved local charts
    but no asserted cross-presentation isomorphism of parahoric functors.

**Proof.** Theorem 1.1 verifies the current Book 130 input and projectivity of the distinguished
good models. Section 2.1 selects the full self-dual periodic multichains. Proposition 2.1
derives the exact flat local models from the quaternionic and unitary determinant and
polarization tensors over arbitrary test rings, Proposition 2.3 transfers them to completed
moduli rings, and Theorem 2.2 gives representability and projectivity. These prove statement 1.
Proposition 3.1 and Theorems 4.1 and 5.1 prove the local assertions in statements 2--3. The
display and subgroup classification in Sections 4.3 and 5.3 prove their global branch and Hasse
claims, including multiplicity one. Proposition 6.1 proves the small-resolution charts, while
the commuting partial-kernel construction and blowup calculation in Section 6.4 prove every
global assertion in statement 4. Proposition 7.1 and Theorem 7.2 prove statement 5.

Formula (9.1) and proper comparison prove statement 6. The graph complex, positive thickness
pairing, and Smith calculation prove statement 7. In degree two, (10.11) is the actual odd
monodromy map; its kernel calculation gives (10.12), and (10.15)--(10.18) evaluate it for the
global Hasse strata. The positive square form (8.7) gives (8.8), so (10.19) and elementary
Jordan theory prove statement 8 without a monodromy--weight hypothesis. The Artin formula proves
statement 9. Naturality of partial Frobenius and Verschiebung, flat base change for the branch
blowup, the projection formula, and functoriality of nearby cycles prove statement 10. The final
paragraph of Section 7.4 proves statement 11. $\square$

### 14.2 Scope ledger and failure modes

The theorem is deliberately exact about its scope. The rational inputs are the PEL-exact
quaternionic curves of Book 127 and the standard unitary surface of Book 129. The residue prime
is one of the completely split primes selected in Section 1.4, and the only bad level groups are
the one- and two-factor Iwahoris of Section 2.1. Deeper chains, ramified unitary groups,
non-minuscule cocharacters, and orthogonal spin local models are different problems; no claim
about them is needed for the catalogued varieties.

The odd and completely split qualifications are structural. Book 130 records that its Book 205
input can recover flat-closure properness at a dyadic quaternionic place only after a complete
oriented genus and common multiplier are supplied, but Book 130 does not then provide the smooth dyadic good
vertex and this book has not proved the required dyadic display or parahoric local model. Thus
there is no dyadic semistable conclusion here. Likewise Chapter 7 transports the displayed
charts after a separately supplied finite splitting extension; it does not prove that an
arbitrary nonsplit or ramified initial PEL local model becomes one of those charts.

Every point at which a false generalization could enter has been checked in the construction.
The determinant locus is the incidence model as a functor on nilpotent rings, so it has no extra
vertical component. The two unitary directions are separated by integral primitive idempotents,
not by a generic-fiber dimension count. The branch normalizations are built from actual partial
$F/V$ quotients, and the height-two display proves both exhaustion and multiplicity one. Hasse
parameters identify the intersections globally. Blowup cycle formulas then determine Gysin
maps, rather than inferring them from a local node.

Projectivity also has no suppressed boundary premise. At the chosen prime, every local
hypothesis of Book 130, Theorem 16.1, was verified in Theorem 1.1. Its Book 205 input gives the
presentation-independent parabolic contradiction for quaternionic curves, while the standard
unitary surface retains its recorded anisotropic finite localization. If those boundary
hypotheses were dropped, a compactification theorem would be required.
At coarse level a fixed point can still create a quotient singularity, so the theorem computes
equivariantly on the fine cover unless the quotient action is free.

Ramified base change must be followed by normalization, and the product of nodes must be
resolved before applying strict-semistable nearby cycles. Nonsplit descent must retain the
signed action on oriented graph edges and square cells. A lisse coefficient system satisfies
(9.7); a coefficient sheaf ramified along the divisor has its own inertia complex and lies
outside that formula.

No equality of source and target dimensions is substituted for a monodromy rank. The odd map is
(10.11), whose rank includes the radical correction $r-g$. The extreme map is the positive
restricted square form (8.7). Thus a reducible curve fiber contributes graph cycles, not nodes;
$N^2$ contributes square cycles satisfying both incidence relations, not triple points; and
double-curve monodromy is (10.12), not the sum of the genera. Integral stratum discriminants are
the Smith forms of these same matrices; identifying them with cohomology-lattice cokernels
requires Section 10.5. A rational Hecke projector with an $\ell$-denominator does not
canonically choose an integral lattice, but it does not obstruct the rational model, conductor,
or type calculation.

### 14.3 Conclusion

The active integral linear algebra has rank two, and it has now been installed in the exact
catalogued tensors. The selected maximal order and annihilator chains turn the determinant and
polarization equations into an incidence of two lines over every test ring; that incidence
produces $xy=p$. One bad direction gives the semistable quaternionic curve or a normal crossing
in the unitary surface. Two bad directions produce the product of two nodes; its small
resolution replaces an impermissible fourfold meeting by triple normal crossings. Theorem 7.2
proves that both diagonal choices admit a finite invariant regular common refinement.

Once the model is strict semistable, its arithmetic memory is distributed across its strata. Components retain their own cohomology. Double curves supply possible length-two monodromy. Triple incidences and the topology of the dual complex supply possible length-three blocks. Restriction and Gysin maps decide which local generators survive globally. The logarithm of tame inertia then turns that incidence geometry into $N$, while finite descent restores the part of inertia that semistable base change temporarily removed.

For curves the answer is the weighted graph pairing: graph cycles are exactly the special
blocks, their rank is the conductor at split semistable level, and their integral discriminant
is component data. For surfaces the answer is more precise than a five-step dimension ledger.
The identity map on $H^1$ of the Hasse curves descends from the Gysin kernel to the restriction
cokernel with rank (10.12), and the square-cell dot product gives $N^2$ with rank (8.6). These
two finite matrices give every Jordan count and conductor, even when the odd cup-product image
has a radical.

Prime-to-$p$ Hecke correspondences commute with the partial Frobenius and Verschiebung
constructions, preserve the Hasse and exceptional strata, and respect pullback, trace, cup
product, and signed incidence. The geometric pair $(r,N)$, the curve component group,
conductor, Frobenius polynomial, and integral stratum matrices therefore pass functorially to
rational Hecke summands; a surface lattice cokernel requires the saturation hypotheses already
stated. This supplies the semistable models, global components, nearby cycles,
monodromy, conductor, and type information promised by the catalog, without importing any later
automorphic theorem.
