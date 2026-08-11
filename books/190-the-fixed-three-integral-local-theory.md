# The Fixed-Three Integral Local Theory

## Contents

- [1. The fixed-three problem](#1-the-fixed-three-problem)
  - [1.1 Why a rational compatible member is not enough](#11-why-a-rational-compatible-member-is-not-enough)
  - [1.2 The inherited arithmetic datum](#12-the-inherited-arithmetic-datum)
  - [1.3 Conventions](#13-conventions)
  - [1.4 The route from a member to an integral system](#14-the-route-from-a-member-to-an-integral-system)
- [2. The effective three-adic member](#2-the-effective-three-adic-member)
  - [2.1 Choosing the coefficient place](#21-choosing-the-coefficient-place)
  - [2.2 Compactness and stable lattices](#22-compactness-and-stable-lattices)
  - [2.3 What effectivity does and does not supply](#23-what-effectivity-does-and-does-not-supply)
  - [2.4 The coefficient-prime bridge](#24-the-coefficient-prime-bridge)
- [3. Weight two at the coefficient prime](#3-weight-two-at-the-coefficient-prime)
  - [3.1 The good weight-two comparison](#31-the-good-weight-two-comparison)
  - [3.2 Crystallinity of the effective constituent](#32-crystallinity-of-the-effective-constituent)
  - [3.3 Hodge type and determinant](#33-hodge-type-and-determinant)
  - [3.4 Why unramified Weil--Deligne data alone would not suffice](#34-why-unramified-weil--deligne-data-alone-would-not-suffice)
- [4. Strongly divisible lattices at three](#4-strongly-divisible-lattices-at-three)
  - [4.1 The integral linear problem](#41-the-integral-linear-problem)
  - [4.2 Existence of a height-two lattice](#42-existence-of-a-height-two-lattice)
  - [4.3 The associated Galois lattice](#43-the-associated-galois-lattice)
  - [4.4 Independence from later lattice replacement](#44-independence-from-later-lattice-replacement)
- [5. Every coefficient quotient](#5-every-coefficient-quotient)
  - [5.1 Open ideals, not just powers of three](#51-open-ideals-not-just-powers-of-three)
  - [5.2 Finite-flat models](#52-finite-flat-models)
  - [5.3 Compatible transition maps](#53-compatible-transition-maps)
  - [5.4 Exact sequences between levels](#54-exact-sequences-between-levels)
  - [5.5 Change of coefficients](#55-change-of-coefficients)
- [6. Determinant, pairings, and Cartier duality](#6-determinant-pairings-and-cartier-duality)
  - [6.1 The cyclotomic determinant lattice](#61-the-cyclotomic-determinant-lattice)
  - [6.2 Perfect alternating pairings](#62-perfect-alternating-pairings)
  - [6.3 Duality of finite-flat models](#63-duality-of-finite-flat-models)
  - [6.4 Compatibility with quotients](#64-compatibility-with-quotients)
- [7. The dyadic rational type](#7-the-dyadic-rational-type)
  - [7.1 Tame inertia of order three](#71-tame-inertia-of-order-three)
  - [7.2 The exact Weil--Deligne pair](#72-the-exact-weil--deligne-pair)
  - [7.3 Conductor two](#73-conductor-two)
  - [7.4 Why conductor two is not the type](#74-why-conductor-two-is-not-the-type)
- [8. The tame-unipotent special line](#8-the-tame-unipotent-special-line)
  - [8.1 The integral companion matrix](#81-the-integral-companion-matrix)
  - [8.2 Reduction in characteristic three](#82-reduction-in-characteristic-three)
  - [8.3 The distinguished line](#83-the-distinguished-line)
  - [8.4 A type-adapted global lattice](#84-a-type-adapted-global-lattice)
  - [8.5 Higher quotients and the residual nature of the line](#85-higher-quotients-and-the-residual-nature-of-the-line)
- [9. Ramification away from three](#9-ramification-away-from-three)
  - [9.1 Unramifiedness outside two and three](#91-unramifiedness-outside-two-and-three)
  - [9.2 Finite quotients preserve unramifiedness](#92-finite-quotients-preserve-unramifiedness)
  - [9.3 The dyadic inertia image at every level](#93-the-dyadic-inertia-image-at-every-level)
  - [9.4 Conductor and wild inertia ledger](#94-conductor-and-wild-inertia-ledger)
- [10. Global finite-flat objects away from two](#10-global-finite-flat-objects-away-from-two)
  - [10.1 Why the prime two is removed](#101-why-the-prime-two-is-removed)
  - [10.2 Gluing the local models](#102-gluing-the-local-models)
  - [10.3 Coefficients and transition morphisms](#103-coefficients-and-transition-morphisms)
  - [10.4 Global duality](#104-global-duality)
- [11. The exact Schoof-classification interface](#11-the-exact-schoof-classification-interface)
  - [11.1 The category-ready package](#111-the-category-ready-package)
  - [11.2 Simple-factor data versus classification](#112-simple-factor-data-versus-classification)
  - [11.3 All-level devissage data](#113-all-level-devissage-data)
  - [11.4 The theorem exported by this book](#114-the-theorem-exported-by-this-book)
- [12. Dependency-boundary audit](#12-dependency-boundary-audit)
  - [12.1 Ramification theory](#121-ramification-theory)
  - [12.2 Finite-flat representations](#122-finite-flat-representations)
  - [12.3 Integral Fontaine--Laffaille theory](#123-integral-fontaine--laffaille-theory)
  - [12.4 Local--global compatibility and type lattices](#124-local--global-compatibility-and-type-lattices)
  - [12.5 The compatible-system input](#125-the-compatible-system-input)
- [13. Hostile mathematical audit](#13-hostile-mathematical-audit)
  - [13.1 Rational-to-integral traps](#131-rational-to-integral-traps)
  - [13.2 Quotient and transition traps](#132-quotient-and-transition-traps)
  - [13.3 Dyadic traps](#133-dyadic-traps)
  - [13.4 Global gluing traps](#134-global-gluing-traps)
- [14. Conclusion](#14-conclusion)

## 1. The fixed-three problem

### 1.1 Why a rational compatible member is not enough

A compatible family gives a two-dimensional representation at every coefficient prime and
relates their Frobenius polynomials and rational local parameters.  The member with coefficient
characteristic three is therefore already present.  What is not present is the integral object
needed for a small-ramification argument.

There are several genuinely different statements hidden behind the phrase “take the
three-adic member.”  One must choose a lattice, prove that its restriction at three is the
generic fiber of finite-flat group schemes, do so simultaneously for every coefficient
quotient, and identify the maps between those models.  One must also retain the full local type
at two.  Its rational inertia is semisimple of order three, while its reduction in characteristic
three is unipotent.  The latter carries a line that disappears if one remembers only the
semisimplification.  Finally, the finite quotients must be unramified at every prime other than
two and three so that they extend over $\mathbf Z[1/2]$.

These requirements are coupled.  A lattice selected for good integral Hodge theory at three
need not visibly display the desired dyadic line.  A lattice selected from the dyadic type is
not automatically known to be finite flat at three.  The central task is to show that these two
selections can be reconciled without claiming that a rational representation has a canonical
lattice.

The problem is also genuinely “fixed-three.”  In a varying compatible family, the local datum
at a rational prime $p$ is compared using members whose coefficient characteristic is not $p$.
Once the coefficient place above three is fixed, the prime three falls outside that
prime-to-coefficient comparison.  Conversely, the exceptional prime two now lies in coefficient
characteristic three, precisely where its order-three tame type ceases to be semisimple after
reduction.  The fixed choice therefore creates both the Hodge-theoretic problem at three and the
congruence problem at two.

### 1.2 The inherited arithmetic datum

We begin with the compatible family already constructed over the base field.  Thus $E$ is a
number field and, for every finite place $\lambda$ of $E$, there is a continuous absolutely
irreducible representation

$$
r_\lambda:G_{\mathbf Q}\longrightarrow \operatorname{GL}_2(E_\lambda).
\tag{1.1}
$$

The family has arithmetic-Frobenius polynomials

$$
P_p(X)=X^2-a_pX+p
\tag{1.2}
$$

at its good primes, determinant

$$
\det r_\lambda=\chi_\lambda,
\tag{1.3}
$$

and duality $r_\lambda^\vee\simeq r_\lambda\otimes\chi_\lambda^{-1}$.
For coefficient characteristic different from the local residue characteristic, the family has
one common Frobenius-semisimple Weil--Deligne pair at every finite prime.

The exceptional rational prime is two.  There the pair has $N=0$, trivial wild inertia, and
primitive tame inertia of order three.  Away from two and the varying coefficient
characteristic, the family is unramified.  These are equalities of local objects, not
conclusions guessed from conductor exponents.

### 1.3 Conventions

Fix a place $\lambda\mid3$ of $E$.  Write

$$
K=E_\lambda,\qquad \mathcal O=\mathcal O_K,qquad
\mathfrak m=(\varpi),\qquad k=\mathcal O/\mathfrak m,
\tag{1.4}
$$

and put $V=r_\lambda$.  The cyclotomic character on a lattice is denoted $\chi_3$ and its
reduction modulo an open ideal $I$ by $\chi_I$.  Arithmetic Frobenius is used globally, so
$\chi_3(\operatorname{Frob}_p)=p$ at an unramified prime $p\ne3$.

For a place $p$ of $\mathbf Q$, $I_p$ denotes inertia, $P_p$ wild inertia, and $t_p$ a tame
generator whenever a generator of the relevant finite quotient has been selected.  At two we
choose $t_2$ whose image has order three.  Changing $t_2$ to its inverse exchanges the two
characteristic-zero tame eigencharacters but does not change the special line constructed
below.

An **open coefficient ideal** means a nonzero ideal $I\subset\mathcal O$.  Since $\mathcal O$
is a discrete valuation ring, it is a power of $\mathfrak m$; retaining ideal notation makes
coefficient extension and quotient maps transparent.  A finite-flat model always includes its
coefficient action and an identification of its generic geometric points with the displayed
Galois module.

### 1.4 The route from a member to an integral system

The proof has four stages.

First, the good weight-two comparison at the coefficient prime proves that
$V|_{G_{\mathbf Q_3}}$ is crystalline of Hodge type $(0,1)$.  This is stronger than saying that the common
prime-to-three Weil--Deligne pair at three is unramified.

Second, integral Fontaine--Laffaille theory supplies a strongly divisible lattice and hence a
Galois lattice whose every quotient is finite flat.  Schematic closure shows that the same
property holds for every commensurable stable lattice.

Third, we choose within this commensurability class a lattice adapted to the primitive order-three
inertia at two.  Its residual tame operator is a nontrivial unipotent with one canonical fixed
line.  Commensurability transfers the all-quotient finite-flat property to this lattice.

Fourth, unramifiedness away from two and three and finite flatness at three glue the local
models to finite-flat $3$-primary group schemes over $\mathbf Z[1/2]$.  Determinant and the
exterior pairing provide Cartier duality at every level.  That is precisely the input, and no
more than the input, for the subsequent classification.

## 2. The effective three-adic member

### 2.1 Choosing the coefficient place

The adjective **effective** matters.  The representation $V$ is an actual rank-two summand,
not a formal difference of induced representations.  Consequently restriction to a
decomposition group, formation of a lattice, determinant, duality, and reduction modulo an
ideal all make literal sense.

The field $K$ may be enlarged finitely to split coefficient actions or pairings.  We always
replace $\mathcal O$ by the integral closure and tensor lattices, models, and transition maps
together.  We never enlarge coefficients in order to alter the local type.  In particular,
the polynomial

$$
X^2+X+1
\tag{2.1}
$$

for dyadic tame inertia remains the same polynomial after extension.

### 2.2 Compactness and stable lattices

Continuity makes the image of $G_{\mathbf Q}$ in $\operatorname{GL}(V)$ compact.  If $L_0$ is
any $\mathcal O$-lattice, boundedness of the image and its inverse gives an integer $c$ such
that

$$
\varpi^cL_0\subset gL_0\subset\varpi^{-c}L_0
\qquad(g\in G_{\mathbf Q}).
\tag{2.2}
$$

The sum of all translates is therefore a finitely generated torsion-free $\mathcal O$-module
between the two extreme lattices.  It is free, spans $V$, and is stable.  Thus stable lattices
exist.

This argument contains no local geometry.  It proves neither finite flatness nor a preferred
reduction.  Two stable lattices are commensurable, but their residual extension classes can
differ.

### 2.3 What effectivity does and does not supply

Effectivity supplies an honest direct-sum identity in characteristic zero.  It also permits the
cyclotomic determinant identity (1.3) to be interpreted as an equality of one-dimensional
representations.  It does not make a characteristic-zero projector integral.  Hence it does
not by itself give:

- a saturated lattice in the effective summand;
- a perfect pairing on an arbitrarily selected lattice;
- a finite-flat model at three;
- compatible models for different ideals; or
- a residual line at two.

Each of these points is resolved below by a separate integral construction.  Keeping them
separate prevents the characteristic-zero Brauer cancellation from being reused where
denominators matter.

A simple lattice example explains the warning.  In $K^2$, the two lattices

$$
\mathcal Oe_1+\mathcal Oe_2,
\qquad
\mathcal Oe_1+\mathcal O\varpi^{-1}(e_1+e_2)
\tag{2.3}
$$

span the same vector space.  A rational projection onto $Ke_1$ preserves the first only under
an integrality condition on its matrix and can meet the second in a lattice of different index.
After reduction those indices become extension data.  The compatible family controls the common
rational space, not this relative position.

### 2.4 The coefficient-prime bridge

The missing assertion is local:

**Coefficient-prime bridge theorem.**  The restriction
$V|_{G_{\mathbf Q_3}}$ is crystalline, and its labeled Hodge--Tate weights are $0$ and $1$.

The theorem is proved in the next chapter from the weight-two geometric origin of the effective
constituent.  It is not imported from strict compatibility, since strict compatibility compares
Weil--Deligne objects only when the local residue characteristic differs from the coefficient
characteristic.

## 3. Weight two at the coefficient prime

### 3.1 The good weight-two comparison

At a good place above three, the weight-two packet is isolated in the first cohomology of a
smooth proper curve, or in the already descended rank-two factor of the corresponding smooth
proper carrier.  Smooth proper comparison gives a crystalline representation.  The Hodge
filtration on degree-one cohomology has only steps zero and one.  The packet multiplicity space
is stable under the comparison and therefore has one dimension in each step.

The statement needed here can be isolated without reference to the carrier:

**Lemma 3.1 (weight-two coefficient-prime comparison).**  Let $W$ be a rank-two
cohomological packet factor at a place above an odd coefficient prime.  Assume the selected
carrier has good reduction there, the packet projector is defined on the rational comparison
object, and the rank-two factor is an actual direct summand.  Then $W$ is crystalline.  If its
weight is two and its determinant is cyclotomic up to an unramified finite-order character,
its Hodge--Tate multiset is $\{0,1\}$.

**Proof.**  Crystalline representations form a full subcategory closed under direct sums,
subobjects, and quotients.  Smooth proper comparison places the full degree-one cohomology in
that category.  An actual rational projector has image a subobject, hence the packet factor is
crystalline.  The Hodge filtration of degree one has jumps only at zero and one.  Purity and
the determinant show that the sum of the two labeled weights is one.  Noncharacter weight two
excludes two equal half-weights and the rank-one filtration pieces of the packet give one jump
at each endpoint.  Thus the weights are $0$ and $1$. $\square$

The proof uses a rational projector only inside the abelian category of crystalline
representations.  It makes no claim that the projector preserves an integral cohomology
lattice.

There are two useful checks on the lemma.  For an elliptic curve with good reduction at three,
the two steps are the invariant differential and its quotient in de Rham cohomology; the
associated Tate module has weights $0$ and $1$.  At the opposite extreme, a weight-two packet
factor with two zero weights would have determinant of Hodge weight zero and could not satisfy
the cyclotomic determinant.  These checks show why both the geometric degree and the determinant
enter: the determinant alone fixes only the sum, while the degree-one filtration fixes the
allowed endpoints.

The phrase “actual direct summand” also has content.  If $e$ is a rational idempotent on a
crystalline representation $H$, then $eH$ is crystalline because it is the kernel of $1-e$.
If one has only an equality $[H^+]-[H^-]$ in a Grothendieck group, there is no object to which
the period functor can be applied.  Effectivity supplies the object before any dimension
calculation is made.

### 3.2 Crystallinity of the effective constituent

The effective member was assembled from weight-two packet factors over elementary fields.
At the place above three, the local packet data are good and the comparison factors are
crystalline of weights $0$ and $1$.  Restriction to the common local field, finite direct sum,
and the coefficient twists used in the displaying construction preserve crystallinity.  The
actual cancellation identity has the form

$$
R^+_3\simeq V\oplus R^-_3.
\tag{3.1}
$$

Apply the exact crystalline period functor to (3.1).  Both displaying terms come from the good
weight-two comparison, so their period dimensions equal their representation dimensions.
Additivity gives

$$
\dim D_{\mathrm{cris}}(V)
=\dim V=2.
\tag{3.2}
$$

Thus $V$ is crystalline.  The filtration in (3.1) is strict, and subtracting the equal
auxiliary packet contributions leaves one zero-weight and one one-weight direction.  This
proves the coefficient-prime bridge theorem.

To spell out the dimension calculation, exactness gives

$$
D_{\mathrm{cris}}(R^+_3)
\simeq D_{\mathrm{cris}}(V)\oplus D_{\mathrm{cris}}(R^-_3).
\tag{3.6}
$$

The filtered dimensions of the two displaying terms are sums of the corresponding weight-two
packet dimensions.  The Brauer relation has total degree one, so their difference has total
dimension two.  The same relation applied separately to the zero and one Hodge graded pieces
has difference one in each degree.  Hence

$$
\dim\operatorname{gr}^0D_{\mathrm{cris}}(V)
=\dim\operatorname{gr}^1D_{\mathrm{cris}}(V)=1.
\tag{3.7}
$$

This calculation uses strictness of morphisms between admissible filtered objects.  Without
strictness, subtraction of total dimensions would not determine the dimensions of the graded
pieces.

The order of reasoning is important: actual effectivity gives (3.1), good comparison makes the
two displaying terms crystalline, and only then does closure under direct summands give
crystallinity of $V$.  A virtual equality in a Grothendieck group would not suffice.

### 3.3 Hodge type and determinant

Let

$$
D=D_{\mathrm{cris}}(V).
\tag{3.3}
$$

It is a two-dimensional filtered Frobenius module with

$$
\dim\operatorname{Fil}^1D=1,qquad
\operatorname{Fil}^2D=0,qquad
\operatorname{Fil}^0D=D.
\tag{3.4}
$$

The determinant identity (1.3) becomes

$$
\det D\simeq D_{\mathrm{cris}}(K(1)).
\tag{3.5}
$$

with the corresponding normalization of Frobenius.  This determinant records the sum of the
Hodge weights and will later orient the alternating pairing.  It does not by itself select a
strongly divisible lattice inside $D$.

Weak admissibility supplies the numerical equality behind the lattice construction.  With
$t_H(D)$ the sum of Hodge jumps and $t_N(D)$ the valuation of the Frobenius determinant,

$$
t_H(D)=1=t_N(D),
\tag{3.8}
$$

and every Frobenius-stable line satisfies the corresponding inequality.  These line
inequalities are what prevent the elementary divisors in the iteration of Theorem 4.1 from
drifting indefinitely.  Merely knowing the total equality would not control a destabilizing
line.

### 3.4 Why unramified Weil--Deligne data alone would not suffice

For coefficient places $\lambda'\nmid3$, strict compatibility says that the local
Weil--Deligne pair at three is unramified.  It is tempting to transfer that assertion to the
three-adic member.  This is invalid.  The Weil--Deligne functor in the form used for strict
compatibility excludes equal residue and coefficient characteristic, and an unramified
prime-to-three companion does not prove that a three-adic representation is crystalline.

Nor would potential crystallinity be enough.  A ramified finite character can become trivial
after a finite extension while failing to be crystalline over $\mathbf Q_3$.  The good
weight-two comparison above proves crystallinity over the original local field and is therefore
the indispensable bridge.

One can see the distinction in rank one.  An unramified character with unit Frobenius value is
crystalline of Hodge weight zero.  A nontrivial finite ramified character becomes crystalline
after the extension killing it but is not crystalline over the original field.  Both can look
harmless after passing to a coarser potentially semistable record.  The full period dimension
over $\mathbf Q_3$ separates them.

## 4. Strongly divisible lattices at three

### 4.1 The integral linear problem

Crystallinity is rational.  To obtain finite-flat quotients we need a strongly divisible
lattice $M\subset D$ compatible with the Hodge step.  Put

$$
F_M=M\cap\operatorname{Fil}^1D.
\tag{4.1}
$$

The desired conditions say that $M$ and $F_M$ are finite projective over the appropriate
unramified base with coefficients, that $F_M$ is saturated of rank one, and that the divided
Frobenius maps generate $M$.  Locally one can choose

$$
M=\mathcal Re_0\oplus\mathcal Re_1,qquad F_M=\mathcal Re_1,
\tag{4.2}
$$

where $\mathcal R$ is the unramified base tensored with $\mathcal O$.  Strong divisibility is
equivalent to invertibility of the normal matrix

$$
\begin{pmatrix}a&b\\c&d\end{pmatrix},
\quad
\varphi_0(e_0)=ae_0+ce_1,
\quad
\varphi_1(e_1)=be_0+de_1.
\tag{4.3}
$$

This is the integral content hidden by the two rational Hodge numbers.

### 4.2 Existence of a height-two lattice

**Theorem 4.1 (strongly divisible lattice).**  The filtered Frobenius module $D$ contains a
coefficient-linear strongly divisible lattice $M$ of height two and Hodge type $(0,1)$.

**Proof strategy.**  We use the low-weight lattice argument on $D$ itself.  This is important:
the rational cancellation that produced $D$ need not preserve integral packet lattices.  The
argument alternately saturates the Hodge line and normalizes divided Frobenius.  Weak
admissibility prevents the elementary divisors from escaping to infinity.

Choose any coefficient lattice $M_0\subset D$ for which
$F_0=M_0\cap\operatorname{Fil}^1D$ is saturated.  For such a pair define its normal image

$$
\Phi(M_0,F_0)=arphi(M_0)+3^{-1}\varphi(F_0).
\tag{4.4}
$$

After a scalar rescaling this is again a lattice.  Replace $M_0$ by that lattice and replace
its Hodge submodule by the saturated intersection with $\operatorname{Fil}^1D$.  Iterating gives
pairs $(M_i,F_i)$.  Write the elementary divisors of $M_{i+1}$ relative to $M_i$ as
$3^{u_i},3^{v_i}$, ordered with $u_i\le v_i$.  Rescaling changes both by the same integer, so
normalize $u_i=0$.

Suppose the remaining differences $v_i-u_i$ were unbounded.  Passing to the directions of the
long elementary divisor and using compactness of the projective line over the local field
produces a Frobenius-stable line $D'\subset D$.  The construction of $\Phi$ shows that the
Frobenius slope of $D'$ is strictly smaller than the Hodge number induced on $D'$ if the long
direction repeatedly lies in the Hodge line, and strictly larger for the quotient direction
otherwise.  Either conclusion contradicts weak admissibility of $D$ and of its Frobenius-stable
subobjects.  Hence the normalized relative positions lie in a finite set.

Two normalized pairs in the iteration therefore repeat.  The composite between them is a
homothety.  Taking the sum of the finitely many lattices around this cycle and saturating its
Hodge intersection gives a fixed pair $(M,F_M)$ satisfying

$$
M=\varphi(M)+3^{-1}\varphi(F_M).
\tag{4.5}
$$

Equivalently, the normal map obtained from $\varphi_0=\varphi$ on a complement of $F_M$ and
$\varphi_1=3^{-1}\varphi$ on $F_M$ is an isomorphism.  Since (3.4) makes $F_M$ and $M/F_M$
rank one, $M$ is strongly divisible of height two and Hodge type $(0,1)$.  The construction is
unchanged by carrying the commuting $\mathcal O$-action throughout. $\square$

The proof constructs one lattice.  It does not assert uniqueness; distinct strongly divisible
lattices can span the same rational filtered module.

In rank two the fixed-point condition has a concrete interpretation.  Choose a basis adapted
to $F_M$ as in (4.2).  If the normal matrix in (4.3) has determinant a unit, then its columns
generate $M$ and every reduction modulo $\varpi^n$ has the correct length.  If its determinant
were divisible by $\varpi$, the solution module would lose a residual direction.  If the
determinant had negative valuation, divided Frobenius would not preserve the lattice.  The
iteration in the proof moves between these failures until both elementary divisors are zero.

Two familiar shapes illustrate that the theorem does not force ordinarity.  In an ordinary
basis the normal matrix can be triangular modulo $\mathfrak m$, leaving an étale line and a
multiplicative quotient.  In a local--local basis both diagonal entries can vanish modulo
$\mathfrak m$ while the off-diagonal entries remain units.  The same determinant condition
still gives a valid strongly divisible object.  Finite flatness therefore includes both
geometric shapes and does not mean that the residual representation splits.

### 4.3 The associated Galois lattice

Integral Fontaine--Laffaille realization applied to $M$ gives a finite free
$\mathcal O$-lattice

$$
T_{\mathrm{FL}}\subset V
\tag{4.6}
$$

stable under $G_{\mathbf Q_3}$.  The construction is compatible with the original rational
comparison, so after choosing the rational identification it lies inside the given $V$.
Because the global image is compact, replace $T_{\mathrm{FL}}$ by a commensurable globally
stable lattice when necessary.  The next proposition shows that this replacement cannot lose
finite flatness.

### 4.4 Independence from later lattice replacement

**Proposition 4.2 (commensurability transfer).**  Let $T$ and $T'$ be stable
$\mathcal O$-lattices in the same $K$-representation of a local Galois group.  If every finite
quotient of $T$ is finite flat, then every finite quotient of $T'$ is finite flat.

**Proof.**  Choose $c\ge0$ with

$$
\varpi^cT\subset T'\subset\varpi^{-c}T.
\tag{4.7}
$$

Fix $n$.  The image of $T'$ in the finite module
$\varpi^{-c}T/\varpi^{n+c}T$ is a stable submodule of a finite-flat module.  Its quotient by
the image of $\varpi^nT'$ is naturally $T'/\varpi^nT'$.  Schematic closure of the stable
submodule inside a finite-flat model, followed by the represented finite-flat quotient, proves
that $T'/\varpi^nT'$ is finite flat.  An arbitrary open-ideal quotient is treated identically.
$\square$

Here is the subquotient more explicitly.  Let $A$ be the image of $T'$ in
$\varpi^{-c}T/\varpi^{n+c}T$ and let $B$ be the image of $\varpi^nT'$.  Then $B\subset A$ are
stable finite modules and

$$
A/B\simeq T'/\bigl(T'\cap\varpi^{n+c}T+\varpi^nT'\bigr).
\tag{4.8}
$$

Because $\varpi^cT\subset T'$, one has
$\varpi^{n+c}T\subset\varpi^nT'$, so the denominator is exactly $\varpi^nT'$.  Thus $A/B$
is the required quotient.  This inclusion is the small but decisive reason the ambient level
uses $n+c$ rather than merely $n$.

The proposition would be insufficient if finite-flat modules were known to be closed only
under direct summands.  The lattice quotient generally appears as a nonsplit subquotient.
Schematic closure and represented quotient are precisely the stronger operations required.

This proposition is the hinge of the book.  Fontaine--Laffaille theory is used to produce one
good lattice.  Finite-flat closure calculus then permits a different global or dyadic
type-adapted lattice without redoing integral Hodge theory.

## 5. Every coefficient quotient

### 5.1 Open ideals, not just powers of three

Fix henceforth a globally stable lattice $T\subset V$ in the commensurability class of
$T_{\mathrm{FL}}$.  For every open ideal $I\subset\mathcal O$, put

$$
T_I=T/IT.
\tag{5.1}
$$

It is not enough to prove the statement for $T/3^nT$ when $\mathcal O/\mathbf Z_3$ is ramified:
the ideals $(3^n)$ may skip coefficient levels.  The admissible-annihilator construction for
the actual ideal $I$ avoids this loss.

### 5.2 Finite-flat models

**Theorem 5.1 (all quotient finite-flatness).**  For every open ideal $I\subset\mathcal O$,
the $G_{\mathbf Q_3}$-module $T_I$ is the generic geometric-point module of a finite-flat
commutative group scheme

$$
\mathcal G_{I,3}/\mathbf Z_3
\tag{5.2}
$$

with its full $\mathcal O/I$-action.

**Proof.**  For the original Fontaine--Laffaille lattice this is the height-two integral
equivalence and its arbitrary-open-ideal theorem.  For the chosen lattice $T$, Proposition 4.2
expresses $T_I$ as a stable subquotient of a finite quotient of $T_{\mathrm{FL}}$.  Close the
submodule in the supplied ambient finite-flat group and take the represented quotient.  The
coefficient action extends by the coefficient-linear closure construction. $\square$

The theorem asserts existence of a marked model, not uniqueness among all finite-flat models.
The Fontaine--Laffaille model is uniquely characterized inside its low-weight category, which is
enough to make the transition system canonical once $T$ has been fixed.

For example, suppose the ramification index of $\mathcal O/\mathbf Z_3$ is two, so
$3=u\varpi^2$.  Knowing finite flatness of $T/3T=T/\varpi^2T$ implies it for
$T/\varpi T$ by quotient closure, but it does not by itself name the compatible map or the
filtered object at the intermediate level.  The admissible object $M_{(\varpi)}$ does both.
At the next stage $T/\varpi^3T$ is not a quotient of $T/3T$ at all.  Treating arbitrary open
ideals from the outset prevents the tower from silently dropping every odd level.

### 5.3 Compatible transition maps

If $J\subset I$, there is a quotient map

$$
q_{J,I}:T_J\longrightarrow T_I.
\tag{5.3}
$$

On the contravariant filtered side it corresponds to the admissible inclusion

$$
M_I\hookrightarrow M_J.
\tag{5.4}
$$

On finite-flat groups it gives a faithfully flat morphism

$$
Q_{J,I}:\mathcal G_{J,3}\longrightarrow\mathcal G_{I,3}.
\tag{5.5}
$$

For $K\subset J\subset I$, faithfulness on generic fibers shows

$$
Q_{J,I}\circ Q_{K,J}=Q_{K,I}.
\tag{5.6}
$$

Thus the models form one directed quotient system.  They are not unrelated witnesses of finite
flatness at separate levels.

The direction of (5.4) is a useful variance check.  Generic realization is contravariant on
the filtered side.  Hence the surjection $T_J\twoheadrightarrow T_I$ must arise from an
injection $M_I\hookrightarrow M_J$.  Reversing this arrow would turn a generic quotient into a
generic subgroup and would give the wrong kernel in (5.7).

### 5.4 Exact sequences between levels

For integers $m,n\ge1$, multiplication by $\varpi^m$ gives an exact coefficient sequence with
the evident ramification-index adjustment.  In the simplest unramified coefficient case it is

$$
0\longrightarrow T/\varpi^nT
\xrightarrow{\ \varpi^m\ }
T/\varpi^{m+n}T
\longrightarrow T/\varpi^mT\longrightarrow0.
\tag{5.7}
$$

The corresponding group-scheme sequence is faithfully flat exact.  For general nested ideals,
the kernel of $Q_{J,I}$ is the schematic closure of the generic kernel.  One must not identify
it with a naive tensor product involving $I/J$ unless the required flatness is known.  Exactness
of generic modules plus the supplied middle model is what justifies the integral sequence.

### 5.5 Change of coefficients

Let $K'/K$ be a finite coefficient extension with ring of integers $\mathcal O'$, and let
$T'=\mathcal O'\otimes_{\mathcal O}T$.  For an open ideal $I'\subset\mathcal O'$, choose an
ideal $I$ small enough that $IT'\subset I'T'$.  The quotient $T'/I'T'$ is a coefficient
quotient of a finite scalar extension of $T/IT$, hence is finite flat by coefficient extension
followed by schematic quotient.  The result is independent of the auxiliary $I$ because the
generic module characterizes the admissible object.

No trace self-duality of $\mathcal O'/\mathcal O$ is silently used.  When a scalar extension is
transported to the contravariant filtered side, the coefficient dual appears unless a trace
pairing has been fixed.

There are three compatible notions of “same system” here.  Extending coefficients tensors the
generic modules; reducing coefficients takes an admissible quotient; enlarging the unramified
ground field restricts the local Galois group and base-changes the finite-flat model.  A ramified
ground-field extension is different: finite flatness ascends, but descent of the selected model
requires integral descent data.  Nothing in the fixed-three argument descends from a merely
potential model.

## 6. Determinant, pairings, and Cartier duality

### 6.1 The cyclotomic determinant lattice

The rational identity $\det V=K(1)$ restricts to an isomorphism of one-dimensional
$K$-representations.  The lattice $\bigwedge^2_{\mathcal O}T$ is stable and therefore maps to
a fractional ideal times $\mathcal O(1)$.  Multiplying the rational determinant isomorphism by
one scalar gives an integral isomorphism

$$
\iota_{\det}:\bigwedge^2T\xrightarrow{\sim}\mathcal O(1).
\tag{6.1}
$$

It is unique up to a unit of $\mathcal O$.  This unit ambiguity changes no determinant
character, duality statement, or special line.

Reducing (6.1) modulo $I$ yields

$$
\det T_I\simeq(\mathcal O/I)(1),
\qquad
\det\bar r_I=\chi_I.
\tag{6.2}
$$

### 6.2 Perfect alternating pairings

Define

$$
\langle x,y\rangle_{\mathcal O}=\iota_{\det}(x\wedge y).
\tag{6.3}
$$

This is alternating, $G_{\mathbf Q}$-equivariant, and perfect over $\mathcal O$.  It induces a
stable-lattice isomorphism

$$
T\xrightarrow{\sim}T^\vee(1).
\tag{6.4}
$$

Modulo every $I$ it gives a perfect $\mathcal O/I$-linear pairing

$$
T_I\times T_I\longrightarrow(\mathcal O/I)(1).
\tag{6.5}
$$

The construction uses the actual exterior lattice.  Rational self-duality by itself would not
show that an arbitrarily normalized pairing is integral or perfect.  There is also a coefficient
warning.  Cartier duality is duality over $\mathbf Z_3$, whereas (6.5) is initially duality over
$\mathcal O/I$.  Passing between them requires the coefficient dualizing module, not a tacit
identification of $\mathcal O$ with its trace dual.

### 6.3 Duality of finite-flat models

Put

$$
\mathcal O^\dagger
=\operatorname{Hom}_{\mathbf Z_3}(\mathcal O,\mathbf Z_3).
\tag{6.6}
$$

Under the trace description, this is the inverse different as a fractional $\mathcal O$-ideal.
It is free of rank one over the DVR $\mathcal O$.  Fixing a generator $\delta$ gives a perfect
functional

$$
\ell_\delta(x)=\operatorname{Tr}_{K/\mathbf Q_3}(\delta x)
\tag{6.7}
$$

and compatible perfect functionals on every quotient.  A different generator changes all
pairings by one unit and changes none of the resulting duality classes.

Compose (6.5) with $\ell_\delta$.  At three, integral Fontaine--Laffaille duality transports the
result to a perfect Cartier pairing

$$
e_I:\mathcal G_{I,3}\times\mathcal G_{I,3}
\longrightarrow \boldsymbol\mu_{3^{a(I)}},
\tag{6.8}
$$

where $3^{a(I)}$ kills $\mathcal O/I$ and the pairing factors through the exact finite target
dictated by the exponent.  Equivalently, retaining the coefficient dualizing module,

$$
\mathcal G_{I,3}^{D}
\simeq
\mathcal G_{I,3}\otimes_{\mathcal O/I}(\mathcal O/I)^\dagger.
\tag{6.9}
$$

The chosen generator $\delta$ identifies the right side with $\mathcal G_{I,3}$, noncanonically
but compatibly in $I$.  Thus the system is Cartier self-dual after one explicit trace-dual
normalization; without that normalization the invariant statement is (6.9).

Perfectness can be checked on the generic fiber in this low-weight category because the
adjoint map and its inverse extend uniquely.  This is stronger than a pairing of special-fiber
geometric points, which may fail to display connected directions.

The inverse different cannot be suppressed when $K/\mathbf Q_3$ is ramified.  If
$\mathcal O=\mathbf Z_3[\alpha]$ and the minimal polynomial $f$ of $\alpha$ gives a monogenic
integral basis, then locally

$$
\mathcal O^\dagger=f'(\alpha)^{-1}\mathcal O.
$$

Using the raw trace instead of a generator of this inverse different would produce a pairing
whose cokernel measures the different.  It would be nondegenerate over $K$ but not perfect on
the lattice.  This is exactly the rational-to-integral loss that the explicit dualizing module
prevents.

### 6.4 Compatibility with quotients

For $J\subset I$, the annihilator of the generic kernel of $q_{J,I}$ is the generic image of
the dual transition.  Schematic closure commutes with annihilator, so the square

$$
\begin{array}{ccc}
\mathcal G_{J,3}&\xrightarrow{Q_{J,I}}&\mathcal G_{I,3}\\
\downarrow\scriptstyle{\sim}&&\downarrow\scriptstyle{\sim}\\
\mathcal G_{J,3}^{D}&\xleftarrow{Q_{J,I}^{D}}&\mathcal G_{I,3}^{D}
\end{array}
\tag{6.10}
$$

commutes with the coefficient reductions of the targets.  Thus duality is an all-level
structure, not a separate isomorphism selected at each quotient.

## 7. The dyadic rational type

### 7.1 Tame inertia of order three

The prime two is different from the coefficient prime, so the common Weil--Deligne pair applies
to $V|_{G_{\mathbf Q_2}}$.  Wild inertia acts trivially and monodromy is zero.  The tame inertia
image is cyclic of order three and primitive.  For a generator $t_2$ its action $A$ satisfies

$$
A^2+A+1=0,\qquad A\ne1.
\tag{7.1}
$$

Over a splitting field its eigencharacters are $\theta$ and $\theta^{-1}$, with $\theta$ of
order three.  Thus

$$
\operatorname{tr}(A)=-1,\qquad\det(A)=1.
\tag{7.2}
$$

The representation has no inertia invariants in characteristic zero.

### 7.2 The exact Weil--Deligne pair

The full local record is

$$
D_2=(r_2,N_2),\qquad
N_2=0,\qquad r_2(P_2)=1,\qquad
r_2(t_2)^2+r_2(t_2)+1=0.
\tag{7.3}
$$

Frobenius satisfies the tame relation

$$
r_2(\phi_2)r_2(t_2)r_2(\phi_2)^{-1}=r_2(t_2)^2,
\tag{7.4}
$$

because the residue cardinality is two.  It therefore exchanges the two tame eigenlines.  This
Frobenius intertwiner is part of the type and rules out replacing the pair by a split sum of
unrelated tame characters.

Over a field containing a primitive cube root $\zeta$, an adapted basis gives

$$
A=\begin{pmatrix}\zeta&0\\0&\zeta^{-1}\end{pmatrix},
\qquad
F=\begin{pmatrix}0&u\\v&0\end{pmatrix},
$$

with $u,v\ne0$.  The determinant fixes $-uv$ after the unramified normalization is chosen.
The off-diagonal shape of $F$ is forced by (7.4): a diagonal Frobenius would commute with $A$
and violate the squaring action on the two distinct characters.  Thus the local representation
is irreducible as a representation of the tame Weil group even though its inertia restriction
splits after coefficient extension.

### 7.3 Conductor two

Since wild inertia is trivial, the Swan conductor is zero.  Since the primitive tame action has
no invariant vector, the tame codimension is two.  Therefore

$$
a_2(V)=\operatorname{codim}V^{I_2}+\operatorname{Sw}_2(V)
=2+0=2.
\tag{7.5}
$$

This is the **conductor-two type at two**.  It is tame conductor two, not a special
Weil--Deligne block with rank-one monodromy.  In particular $N_2=0$.

### 7.4 Why conductor two is not the type

Many nonisomorphic two-dimensional local representations have conductor two: a sum of two tame
characters, a tame dihedral representation, and some wild representations can share the same
integer.  Equation (7.5) follows from (7.3); it cannot be used to reconstruct (7.3).

For the later classification we retain all of the following: trivial wild inertia, the order
three tame polynomial, zero monodromy, the Frobenius interchange, and the integral special line
constructed next.  The conductor is only their numerical shadow.

As a comparison, a Steinberg parameter with unramified finite inertia has a one-dimensional
kernel of nonzero monodromy and conductor one.  Twisting it by a ramified tame character can
raise the conductor while retaining nonzero monodromy.  Our pair has the opposite shape:
monodromy vanishes and finite inertia moves both dimensions.  These cases can share coarse
newvector behavior after congruence, which is why the full pair must precede the conductor
calculation.

## 8. The tame-unipotent special line

### 8.1 The integral companion matrix

Choose a vector $e$ such that $e,Ae$ span the tame two-dimensional space.  The lattice

$$
L_2=\mathcal Oe+\mathcal OAe
\tag{8.1}
$$

is stable under $A$, and in the ordered basis $(e,Ae)$ the matrix is

$$
[A]=
\begin{pmatrix}
0&-1\\
1&-1
\end{pmatrix}.
\tag{8.2}
$$

The determinant is one, so $L_2$ is also stable under $A^{-1}$.  Frobenius sends $A$ to
$A^2$ and carries $L_2$ to a commensurable lattice.  Saturating the finite orbit of $L_2$ under
the compact dyadic decomposition-group image gives a dyadically stable lattice with the same
primitive cyclic reduction.

### 8.2 Reduction in characteristic three

Modulo $\mathfrak m$, the polynomial becomes

$$
X^2+X+1=(X-1)^2.
\tag{8.3}
$$

The reduction of (8.2) is not the identity.  Hence

$$
(\bar A-1)^2=0,\qquad \bar A-1\ne0,
\tag{8.4}
$$

and $\bar A$ is a single unipotent Jordan block.  This is the tame-unipotent degeneration:
the inertia group still has prime-to-two order three, but its action is no longer semisimple in
coefficient characteristic three.

The failure of semisimplicity is not an accident to be discarded.  It is the integral residue
of the congruence $\theta\equiv\theta^{-1}\equiv1\pmod{\mathfrak m}$.

The companion calculation makes nontriviality visible.  From (8.2),

$$
A-1=
\begin{pmatrix}-1&-1\\1&-2\end{pmatrix},
\qquad
\det(A-1)=3.
$$

Modulo three this matrix has rank one.  Its kernel is generated, in this basis, by the class of
$e-Ae$, and its image is the same line.  The equality of kernel and image follows abstractly
from square-zero rank one, while this calculation verifies that no choice of tame generator has
turned the line into its quotient.

### 8.3 The distinguished line

Put $\bar T=T/\mathfrak mT$.  For a type-adapted lattice define

$$
\mathscr L_2
=\ker(\bar A-1)
=\operatorname{im}(\bar A-1).
\tag{8.5}
$$

Both spaces are one-dimensional because $\bar A-1$ is a nonzero square-zero endomorphism of a
two-dimensional space.  Formula (8.5) shows that the line is intrinsic: it is unchanged when
$t_2$ is replaced by $t_2^{-1}$, since

$$
\bar A^{-1}-1=-\bar A^{-1}(\bar A-1).
\tag{8.6}
$$

Frobenius preserves the line because it conjugates $\bar A$ to $\bar A^2$.  Thus
$\mathscr L_2$ is stable under the whole dyadic decomposition group.  The quotient
$\bar T/\mathscr L_2$ is also trivial on tame inertia, while the middle extension is non-split
as an $I_2$-module.

### 8.4 A type-adapted global lattice

**Proposition 8.1 (simultaneous lattice selection).**  There is a globally
$G_{\mathbf Q}$-stable lattice $T\subset V$ such that:

1. every open-ideal quotient of $T$ is finite flat at three;
2. $T|_{G_{\mathbf Q_2}}$ is homothetic to the primitive cyclic lattice (8.1); and
3. $T/\mathfrak mT$ contains the unique special line (8.5).

**Proof.**  Begin with the cyclic dyadic lattice and take its orbit under the compact global
image.  Boundedness gives a finite lattice.  Saturate successively at the two-dimensional tame
cyclic summand.  Because $A$ has minimal polynomial $X^2+X+1$, replacing the lattice by a
homothetic saturated $\mathcal O[A]$-lattice preserves the primitive companion form; a scalar
reduction would correspond to the nonsaturated order
$\mathcal O+\mathfrak m\mathcal O[A]$.  The resulting lattice is globally stable and has
nontrivial unipotent reduction at two.  It is commensurable with $T_{\mathrm{FL}}$, so
Proposition 4.2 proves all-quotient finite flatness at three. $\square$

This is a selection theorem, not a canonicity theorem.  Once such a lattice is fixed, the line
is canonical inside its residual representation.

### 8.5 Higher quotients and the residual nature of the line

The line $\mathscr L_2$ lives canonically at the first residual level.  At higher levels the
kernel of $A-1$ need not be a free rank-one direct summand, because

$$
\det(A-1)=3
\tag{8.7}
$$

up to a coefficient unit.  Thus one must not speak of a compatible free inertia-fixed line in
every $T_I$.  What is compatible at all levels is the action of the order-three tame group and
its reduction maps.  The special line is recovered after reduction modulo $\mathfrak m$.

This distinction is exactly what the later finite-flat filtration needs: the integral system
retains odd tame inertia at two, and its first residual object retains the non-split unipotent
orientation.

There is nevertheless a useful filtration on each higher quotient:

$$
0\subset (A-1)T_I\subset\ker(A-1\mid T_I)\subset T_I.
\tag{8.8}
$$

Its terms can have coefficient torsion and need not be direct summands.  Reduction of the
filtration modulo $\mathfrak m$ collapses its two middle terms to $\mathscr L_2$.  Retaining the
filtration as submodules is safe; assigning them rank one over $\mathcal O/I$ is not.

## 9. Ramification away from three

### 9.1 Unramifiedness outside two and three

Let $p\ne2,3$.  Since $p$ differs from the coefficient characteristic, strict compatibility
identifies the local Weil--Deligne pair of $V$ with the common pair $D_p$.  The inherited
compatible-system theorem says $D_p$ is unramified with $N=0$.  Therefore

$$
V^{I_p}=V,
\qquad
\det(1-X\operatorname{Frob}_p\mid V)=P_p(X).
\tag{9.1}
$$

There is no auxiliary exceptional set left over from the Brauer presentation.  Ramification of
positive and negative displaying terms cancels in the actual effective constituent, and the
distinguished member identifies the complement as unramified.

### 9.2 Finite quotients preserve unramifiedness

If inertia acts trivially on $T$, it acts trivially on every $T_I$.  Conversely, no choice of
lattice can create ramification in a rational representation on which inertia is already
trivial.  Hence

$$
T_I\text{ is unramified at every }p\ne2,3.
\tag{9.2}
$$

Since the order of $T_I$ is a power of three and $p\ne3$, its unique finite-flat model over
$\mathbf Z_p$ is finite étale.  Thus unramifiedness supplies exactly the integral local model
away from two and three.

### 9.3 The dyadic inertia image at every level

At two, the rational inertia image is the cyclic group generated by $A$.  Its action on $T_I$
is the reduction of the same integral matrix.  The image can become trivial at some very small
quotient only if $A-1$ lies in $I\operatorname{End}(T)$; the type-adapted first reduction rules
this out for $I=\mathfrak m$.  Therefore every nonzero quotient mapping onto $T/\mathfrak mT$
retains a nontrivial order-three group action, although the matrix is unipotent in the residual
coefficient characteristic.

Wild inertia at two remains trivial on every quotient.  This is the meaning of **odd tame
inertia at two** in the global finite-flat category: the only allowed dyadic ramification
factors through a cyclic group of order three.

### 9.4 Conductor and wild inertia ledger

For the characteristic-zero member the local ledger is

| prime | inertia | monodromy | Swan | Artin conductor |
|---|---|---:|---:|---:|
| $2$ | primitive tame cyclic order $3$ | $0$ | $0$ | $2$ |
| $3$ | crystalline of weights $0,1$ | coefficient-prime datum | not inferred from WD | finite-flat system |
| $p\ne2,3$ | trivial | $0$ | $0$ | $0$ |

For modular coefficient quotients, ordinary characteristic-zero Artin-conductor formulas are
not substituted blindly: the coefficient characteristic divides the dyadic inertia order.
The safe invariant is the actual inertia action and its cutout field.  At two that field is
tame; away from two and three it is unramified; at three its upper ramification is controlled
by finite-flat theory.

## 10. Global finite-flat objects away from two

### 10.1 Why the prime two is removed

The generic module $T_I$ is ramified at two, so it cannot extend to a finite étale group over
$\mathbf Z_2$.  Since its order is a power of three, any finite-flat model over $\mathbf Z_2$
would be finite étale and hence unramified, a contradiction.  Removing two is therefore forced,
not a convenience.

At every remaining prime there is a model: the Fontaine--Laffaille model at three and the
unique finite étale model at $p\ne2,3$.

### 10.2 Gluing the local models

**Theorem 10.1 (global model).**  For every open ideal $I\subset\mathcal O$, there is a
finite-flat commutative group scheme

$$
\mathcal G_I/\mathbf Z[1/2]
\tag{10.1}
$$

with $\mathcal O/I$-action whose generic geometric points are $T_I$.

**Proof strategy.**  Spread the finite étale generic group over the complement of a finite set,
use the marked local model at three, and identify the two over their common generic open.

Let $S$ contain three and the finitely many primes needed to write the finite étale algebra of
$T_I$.  Over $U=\operatorname{Spec}\mathbf Z[1/2S]$, the Galois module gives a finite étale
group scheme.  At each $p\in S\setminus\{2,3\}$, unramifiedness gives its unique finite étale
extension over $\mathbf Z_p$.  At three use $\mathcal G_{I,3}$.  The generic markings identify
all these models over $\mathbf Q_p$.  Finite projective Hopf algebras glue over the Dedekind
base by intersecting the corresponding local Hopf orders inside the common generic Hopf
algebra.  Localization recovers each prescribed order, so the intersection is finite projective
and its Hopf maps preserve it.  The resulting group is finite flat and has generic module
$T_I$. $\square$

For completeness, the Hopf-order intersection has a direct local test.  Let $H_I$ be the
generic Hopf algebra and let $A_p\subset H_I\otimes\mathbf Q_p$ be the selected local Hopf order.
Inside $H_I$ set

$$
A=\{x\in H_I:x\in A_p\text{ for every }p\ne2\}.
$$

Only finitely many conditions differ from an arbitrary spread-out order.  Hence $A$ is a
finitely generated torsion-free $\mathbf Z[1/2]$-module of full rank and therefore finite
projective.  Comultiplication, counit, and antipode preserve every $A_p$ and hence their
intersection.  Localizing at $p$ recovers $A_p$, because the conditions at all other primes
become units.  Thus $A$ is the required finite-flat Hopf algebra.  The same intersection applied
to the graph of a generic morphism proves gluing of transition maps.

No descent from an unspecified ramified extension is used.  Every local model is already over
the required base and comes with the same generic marking.

### 10.3 Coefficients and transition morphisms

The scalar endomorphisms of $T_I$ extend on the local models and agree generically, hence glue
to an $\mathcal O/I$-action on $\mathcal G_I$.  For $J\subset I$, the generic quotient
$T_J\to T_I$ extends at three by (5.5) and away from three by uniqueness of finite étale
extension.  These local maps glue to

$$
Q_{J,I}:\mathcal G_J\longrightarrow\mathcal G_I.
\tag{10.2}
$$

They are faithfully flat because that property can be checked locally on the base.  Their
compositions agree because they agree on the dense generic fiber.  Thus
$(\mathcal G_I,Q_{J,I})$ is one compatible global quotient system.

### 10.4 Global duality

The pairing (6.5) extends at three by integral duality and away from three by finite étale
duality.  The local extensions agree generically and glue to

$$
e_I:\mathcal G_I\times\mathcal G_I\longrightarrow\boldsymbol\mu_{3^{a(I)}}
\tag{10.3}
$$

over $\mathbf Z[1/2]$.  Its adjoint is an isomorphism locally everywhere and hence globally.
The pairings commute with $Q_{J,I}$ and Cartier dual transition maps.  Consequently the entire
global system has cyclotomic determinant and Tate-twisted self-duality.

## 11. The exact Schoof-classification interface

### 11.1 The category-ready package

The classification to follow begins with finite-flat commutative $3$-primary group schemes over
$\mathbf Z[1/2]$ carrying controlled odd tame inertia at two.  The present construction supplies
exactly such objects.  For every open ideal $I$:

1. $\mathcal G_I$ is finite flat over $\mathbf Z[1/2]$;
2. its generic fiber is the actual quotient $T/IT$;
3. it carries the full $\mathcal O/I$-action;
4. its dyadic wild inertia is trivial and tame inertia factors through $C_3$;
5. at the first residual level the tame action is nontrivial unipotent with special line
   $\mathscr L_2$;
6. its determinant is cyclotomic and it has a perfect Cartier pairing;
7. nested ideals give faithfully flat compatible quotient maps; and
8. outside two and three its generic fiber is unramified.

Each clause is integral or local in a different sense.  None may be replaced by the common
Frobenius polynomials alone.

### 11.2 Simple-factor data versus classification

This book does not classify the simple objects of the global category.  In particular, it does
not assert that every simple factor is constant or multiplicative, compute an extension group,
or rearrange a filtration.  Those conclusions require discriminant estimates and global
arithmetic beyond local integral theory.

What is proved here is stability of the input under the operations that classification will
use.  Schematic closure gives subobjects; represented quotients give quotients; Cartier duality
preserves the category; and the all-level transition system supplies the successive kernels.
The odd tame dyadic action is inherited by stable subquotients because it factors through the
same finite group $C_3$.

### 11.3 All-level devissage data

For $n\ge1$, set $I_n=\mathfrak m^n$.  The tower

$$
\cdots\longrightarrow\mathcal G_{I_{n+1}}
\longrightarrow\mathcal G_{I_n}
\longrightarrow\cdots\longrightarrow\mathcal G_{I_1}
\tag{11.1}
$$

has generic fibers $T/\mathfrak m^nT$ and exact multiplication sequences.  Its orders grow as

$$
|T/\mathfrak m^nT|=|\mathcal O/\mathfrak m^n|^2.
\tag{11.2}
$$

The inverse limit of generic points recovers $T$.  Thus any classification that controls all
successive kernels controls the full three-adic lattice rather than only its residual
semisimplification.

The special line belongs to the bottom object and records the nonsplit inertia orientation.
It is not promoted to a fictitious free fixed line in every higher quotient.  This is the exact
amount of integral dyadic information available and needed.

At the bottom level the inertia filtration is

$$
0\longrightarrow\mathscr L_2
\longrightarrow\bar T
\longrightarrow\bar T/\mathscr L_2
\longrightarrow0.
\tag{11.3}
$$

Both endpoints are trivial on tame inertia, but the sequence does not split as an
$I_2$-module.  Consequently passing to the two Jordan--Hölder factors would erase all dyadic
ramification even though the middle module cuts out a nontrivial tame cubic extension.  This is
the model example of why classification must operate on finite-flat objects and extensions,
not only on residual semisimplifications.

### 11.4 The theorem exported by this book

**Theorem 11.1 (fixed-three integral local package).**  Let $(r_\lambda)$ be the effective
weight-two compatible family described in Section 1.2, and fix $\lambda\mid3$.  Then there is
a globally stable rank-two $\mathcal O$-lattice $T\subset r_\lambda$ such that:

$$
\det T=\mathcal O(1),\qquad T\simeq T^\vee(1),
\tag{11.4}
$$

every $T/IT$ has a compatible coefficient-linear finite-flat model over $\mathbf Z_3$, and
these models glue to a compatible Cartier-self-dual system over $\mathbf Z[1/2]$.  The system is
unramified outside $\{2,3\}$.  At two its rational local pair has trivial wild inertia,
$N=0$, primitive tame order-three type, and Artin conductor two.  Modulo $\mathfrak m$, tame
inertia is a nontrivial unipotent Jordan block with the decomposition-group-stable special line

$$
\mathscr L_2=\ker(t_2-1)=\operatorname{im}(t_2-1).
\tag{11.5}
$$

These are precisely the local and integral hypotheses required to place the full torsion tower
in the Schoof finite-flat category.

**Proof.**  Chapters 2 and 3 give the actual member and prove the coefficient-prime bridge.
Theorem 4.1 constructs one strongly divisible lattice, and Proposition 4.2 permits the
simultaneous type-adapted global choice of Proposition 8.1.  Theorems 5.1 and 10.1 produce the
local and global quotient systems, while Sections 5.3 and 10.3 prove compatibility of their
transition maps.  Chapter 6 gives determinant and duality with the inverse-different
normalization made explicit.  Strict compatibility gives unramifiedness away from two and
three.  Finally, (7.3)--(7.5) give the complete dyadic rational type and (8.3)--(8.7) give its
special residual line.  Every assertion in the theorem has therefore been established without
using the classification. $\square$

## 12. Dependency-boundary audit

### 12.1 Ramification theory

The ramification input is used only in its established forms: tame inertia has Swan conductor
zero; the Artin conductor of a characteristic-zero tame representation is the codimension of
invariants; and unramified finite modules define unramified cutout fields.  This gives (7.5) and
the ledger of Chapter 9.

We do not apply ordinary semisimple conductor formulas directly to the characteristic-three
residual representation at two, where the inertia group has order divisible by the coefficient
characteristic.  The actual finite action, rather than its Brauer character, is retained.

### 12.2 Finite-flat representations

The finite-flat theory supplies marked models, schematic closure of stable generic subgroups,
represented finite-flat quotients, coefficient actions, Cartier duality, and the equivalence
between prime-to-residue-characteristic finite flatness and unramifiedness.  These results are
used in Proposition 4.2, Theorem 5.1, and the gluing argument.

No extension is declared finite flat merely because its two endpoints are.  Every extension
used here is a subquotient of a supplied finite-flat middle object or belongs to the compatible
Fontaine--Laffaille system.

### 12.3 Integral Fontaine--Laffaille theory

The hypotheses are exact: coefficient prime $3>2$, local base $\mathbf Q_3$ absolutely
unramified, perfect residue field, and Hodge interval $[0,1]$.  The theory supplies the
height-two strongly divisible lattice, finite-flat models for every open ideal, compatible
admissible transition maps, duality, and coefficient actions.

It does not say that rational Hodge weights select a unique lattice.  The lattice is constructed
in Theorem 4.1.  Later replacement is justified by schematic subquotients, not by an invented
uniqueness theorem.

### 12.4 Local--global compatibility and type lattices

Prime-to-coefficient local--global compatibility supplies the exact dyadic Weil--Deligne pair
and unramifiedness at $p\ne2,3$.  Its coefficient-prime boundary is respected: crystallinity at
three is proved separately in Chapter 3.

Integral type theory supplies the principles used in selecting and reducing a nonbanal type
lattice: take an explicit stable lattice, saturate rather than average, retain the companion and
the special line, and do not expect modular semisimplicity when $3$ divides the tame torus
order.  Conductor is never substituted for the full type.

### 12.5 The compatible-system input

The prior compatible-system theorem supplies an actual absolutely irreducible member, common
Frobenius polynomials, determinant, duality, the exact dyadic pair, unramifiedness away from its
stated exceptional primes, and stable-lattice existence.  It explicitly does not supply a new
finite-flat system at three.  Chapters 3--5 provide that missing assertion.

No rational Brauer cancellation is treated as integral cancellation.  The only use of actual
cancellation at the coefficient prime occurs in the rational crystalline category, after the
displaying objects have independently been shown crystalline.

The complete import ledger is therefore:

| source | exact imported result | use in this book | strengthening explicitly rejected |
|---|---|---|---|
| Book 3 | tame and Swan conductor formulas; fields cut out by finite actions | conductor two and ramification ledger | no modular semisimple conductor formula at dyadic order three |
| Book 48 | marked finite-flat models, schematic closure, quotients, coefficient actions, Cartier duality | commensurability transfer and global local models | no automatic extension closure or ramified descent |
| Book 59 | low-weight integral equivalence, admissible quotients, all open ideals, transitions, base change | the entire finite-flat tower at three | no canonical lattice from rational Hodge data |
| Book 136 | exact prime-to-coefficient Weil--Deligne comparison and its coefficient-prime boundary | dyadic pair and good-place records | no inference of three-adic crystallinity from a companion pair |
| Book 157 | saturation, nonbanal type lattices, companions, special lines, separation of coefficient and local primes | type-adapted lattice at two | no semisimplicity when the tame order is divisible by three |
| Book 189 | effective three-adic member, determinant, duality, exact dyadic type, unramifiedness elsewhere | rational starting object | no integral Brauer cancellation or new finite-flat system |

Every substantial nonfoundational assertion used in the main theorem appears in this ledger.
The coefficient-prime bridge and the simultaneous lattice selection were not supplied at a
prior boundary, so Chapters 3, 4, and 8 prove them here.

## 13. Hostile mathematical audit

### 13.1 Rational-to-integral traps

**Trap: a crystalline rational representation makes every lattice finite flat.**  Rational
crystallinity alone selects no lattice.  We first construct one strongly divisible lattice and
only then transfer the property to commensurable lattices using finite-flat subquotients.

**Trap: determinant equality gives a perfect integral pairing automatically.**  We rescale the
one-dimensional determinant isomorphism so that $\bigwedge^2T$ maps isomorphically, not merely
injectively, to $\mathcal O(1)$.

**Trap: a rational type projector preserves the lattice.**  The dyadic lattice is built by a
cyclic companion construction and saturation.  No averaging denominator is inverted.

### 13.2 Quotient and transition traps

**Trap: proving finite flatness modulo $3^n$ covers every coefficient ideal.**  Ramified
coefficient rings have finer ideal levels.  Theorem 5.1 treats every open ideal directly.

**Trap: separately chosen finite-flat models form a tower.**  The admissible-annihilator
characterization gives canonical maps for nested ideals, and faithfulness forces transitivity.

**Trap: kernels are naive tensor products.**  Kernels are schematic closures of generic
kernels.  No Tor-vanishing is assumed without proof.

### 13.3 Dyadic traps

**Trap: conductor two means Steinberg.**  Here monodromy is zero and finite tame inertia has no
invariants.  The conductor is two for a completely different reason.

**Trap: order-three inertia stays semisimple modulo three.**  The two tame characters become
congruent and the selected lattice reduces to one nontrivial unipotent block.

**Trap: the special line extends as a free fixed line at all levels.**  The determinant of
$A-1$ is divisible by three, so higher fixed modules need not be free direct summands.  Only the
residual line and the full higher-level action are asserted.

**Trap: residual semisimplification remembers the dyadic type.**  Its semisimplification is
trivial on inertia and loses the nonsplit extension.  Equation (11.5) retains the missing
orientation.

### 13.4 Global gluing traps

**Trap: potential finite flatness descends automatically.**  All local models used in gluing
are already defined over $\mathbf Z_p$ and carry compatible generic markings.

**Trap: a ramified three-primary module can extend over $\mathbf Z_2$.**  A finite-flat group
of order prime to two over $\mathbf Z_2$ is finite étale, so removing two is necessary.

**Trap: unramifiedness of the rational member is enough for a global model without checking
quotients.**  Inertia acts trivially on the chosen lattice and hence on every quotient; the
unique finite étale local models then glue with the finite-flat model at three.

All central implications survive these tests.  No result from a later classification or
discriminant argument has been used.

## 14. Conclusion

The effective three-adic member has now acquired the integral structure that rational
compatibility deliberately left open.  Good weight-two comparison at the coefficient prime
places its local representation in the crystalline category with Hodge type $(0,1)$.  Integral
Fontaine--Laffaille theory then produces one strongly divisible lattice and a compatible
finite-flat model for every coefficient quotient.  Schematic closure makes this property
stable under the commensurable lattice replacement needed to see the dyadic type.

At two, primitive tame order-three inertia has zero monodromy and no characteristic-zero
invariants, hence conductor two.  On the selected integral lattice its two tame eigencharacters
coalesce modulo three into a nontrivial unipotent block.  The common kernel and image of
$t_2-1$ is the special line.  This line, rather than residual semisimplification or the conductor
integer, retains the decisive integral local orientation.

For every open ideal $I\subset\mathcal O$, the quotient $T/IT$ is finite flat at three,
unramified away from two and three, and carries only cyclic odd tame ramification at two.  Its
local models glue to a finite-flat group scheme over $\mathbf Z[1/2]$, the transition maps glue
with them, and the cyclotomic exterior pairing gives compatible Cartier duality.  The resulting
tower is therefore ready for the Schoof classification in exactly the required category:

$$
\boxed{
\{\mathcal G_I/\mathbf Z[1/2]\}_I,
\quad
\det=\chi_3,
\quad
\mathcal G_I^D\simeq\mathcal G_I\otimes(\mathcal O/I)^\dagger,
\quad
I_2\twoheadrightarrow C_3,
\quad
\mathscr L_2=\ker(t_2-1)=\operatorname{im}(t_2-1).
}
\tag{14.1}
$$

The classification itself, its discriminant bounds, and its global extension calculations are
not presumed here.  What has been completed is the fixed-three integral local theory on which
those arguments can now act without any loss at a book boundary.
