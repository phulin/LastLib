# Potential Automorphy and Galois Refinement of a Chosen Lift

## Contents

1. [A chosen lift and the fields prepared for it](#1-a-chosen-lift-and-the-fields-prepared-for-it)
   - [The chosen primitive lift](#11-the-chosen-primitive-lift)
   - [The split Galois field and the prepared target field](#12-the-split-galois-field-and-the-prepared-target-field)
   - [How the two constructions fit together](#13-how-the-two-constructions-fit-together)
2. [The signed-special local representation](#2-the-signed-special-local-representation)
   - [Primitive monodromy, line, and sign](#21-primitive-monodromy-line-and-sign)
   - [The resulting local invariants](#22-the-resulting-local-invariants)
   - [Literal preservation at split places](#23-literal-preservation-at-split-places)
3. [The broad deformation ring and its Hecke action](#3-the-broad-deformation-ring-and-its-hecke-action)
   - [The broad ring and its minimal quotient](#31-the-broad-ring-and-its-minimal-quotient)
   - [Restriction of the chosen point](#32-restriction-of-the-chosen-point)
   - [The automorphic packet over the target field](#33-the-automorphic-packet-over-the-target-field)
4. [The cyclic return to the Galois field](#4-the-cyclic-return-to-the-galois-field)
   - [The temporary target-preparation tower](#41-the-temporary-target-preparation-tower)
   - [Selectedness of every descent fibre](#42-selectedness-of-every-descent-fibre)
   - [Residual images and cuspidality](#43-residual-images-and-cuspidality)
5. [Potential automorphy of the chosen lift](#5-potential-automorphy-of-the-chosen-lift)
   - [Automorphy from the target Hecke action](#51-automorphy-from-the-target-hecke-action)
   - [Descent to the split Galois field](#52-descent-to-the-split-galois-field)
   - [Local properties after descent](#53-local-properties-after-descent)
6. [Elementary fixed fields and basic carriers](#6-elementary-fixed-fields-and-basic-carriers)
   - [Construction of the elementary packets](#61-construction-of-the-elementary-packets)
   - [Parity-complete compact carriers](#62-parity-complete-compact-carriers)
   - [Attachment under cyclic change and twisting](#63-attachment-under-cyclic-change-and-twisting)
7. [The selected coefficient place above three](#7-the-selected-coefficient-place-above-three)
   - [Targetwise dyadic parity carriers](#71-targetwise-dyadic-parity-carriers)
   - [The finite-flat irreducibility bridge](#72-the-finite-flat-irreducibility-bridge)
   - [The scope of the selected-three result](#73-the-scope-of-the-selected-three-result)
8. [Auxiliary Galois comparisons](#8-auxiliary-galois-comparisons)
   - [Common unramified algebraic pairs](#81-common-unramified-algebraic-pairs)
   - [Twisting and induction](#82-twisting-and-induction)
   - [Stronger local types lie beyond the comparison](#83-stronger-local-types-lie-beyond-the-comparison)
9. [The selected-three packet theorem](#9-the-selected-three-packet-theorem)
   - [Automorphic packets and their selected-three realizations](#91-automorphic-packets-and-their-selected-three-realizations)
   - [Conclusion](#92-conclusion)

## 1. A chosen lift and the fields prepared for it

Two earlier constructions now meet. Book 178 builds a totally real split Galois field and,
above it, a temporary solvable extension where a broad deformation ring acts on a finite
automorphic module. Book 181 uses the resulting finite signed-special quotient to construct a
characteristic-zero lift over $\mathbf Q$. The present book starts after that point has been
chosen. It proves that the lift is automorphic over the prepared solvable field, brings the
automorphic representation back through the prepared cyclic tower to the split Galois field,
and constructs the elementary fixed-field packets needed for Brauer induction.

Throughout, $\rho$ denotes the Frey lift proved to exist in Book 181, Theorem 1.2, and all
fields and Hecke actions attributed to Book 178 are the objects constructed in its Theorems
12.1--12.2. They are not additional hypotheses. The main result of this book is therefore a
theorem about the already chosen Frey lift, not a conditional criterion with a new automorphic
input.

### 1.1 The chosen primitive lift

Let $\ell\geq7$, let $E/\mathbf Q_\ell$ be finite, and write
$(\mathcal O,(\varpi),k)$ for its ring of integers, maximal ideal, and residue field. We use
covariant representations and arithmetic Frobenius. Book 181 starts from an odd absolutely
irreducible representation

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k)
\tag{1.1}
$$

whose determinant is $\bar\chi_\ell$, whose dyadic restriction has the named primitive
signed-special form, and whose restriction to $G_{\mathbf Q(\zeta_\ell)}$ is absolutely
irreducible. The restricted finite fibre furnished by Book 178, Theorem 12.2 is exactly the
input to Book 181, Theorem 1.1. In the Frey range, Book 181, Theorem 1.2 applies that criterion
and produces, after a finite coefficient extension which we absorb into the notation, a
continuous representation

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\mathcal O)
\tag{1.2}
$$

such that

$$
\det\rho=\chi_\ell,
\qquad
\rho\text{ is unramified outside }\{2,\ell\}.
\tag{1.3}
$$

The chosen lattice is not incidental. At $\ell$, every quotient
$\rho\bmod\varpi^n$ has the selected coefficient-linear finite-flat model of weights
$\{0,1\}$, compatibly in $n$. At $2$, its tame monodromy matrix is primitive modulo
$\varpi$, and the integral line and Frobenius sign are fixed. These are conclusions of Book
181, not fresh assumptions here.

### 1.2 The split Galois field and the prepared target field

We now retain the fields constructed in Book 178. Denote its original split specialization
field by

$$
M/\mathbf Q,
\qquad
\Gamma=\operatorname{Gal}(M/\mathbf Q).
\tag{1.4}
$$

Book 158's regular symmetric presentation, as used in Book 178, may be taken in degree
$d\geq5$. Thus

$$
\Gamma\simeq S_d,
\tag{1.5}
$$

so $\Gamma$ is nonsolvable. The field $M$ is totally real, has positive even degree, and is
disjoint from the full avoidance field chosen before specialization. Every rational prime
specified in that specialization splits completely in $M$; in particular, this holds at

$$
2,\qquad 3,\qquad\ell.
\tag{1.6}
$$

Disjointness from the joint residual--cyclotomic cutout gives

$$
\bar\rho|_{G_M}\text{ absolutely irreducible},
\qquad
\bar\rho|_{G_{M(\zeta_\ell)}}\text{ absolutely irreducible}.
\tag{1.7}
$$

After constructing the upper target packet over $M$, Book 178 forms its actual excess-special
set $P_{\mathrm{tar}}$. Book 109, Corollary 14.6, applied there in target mode, supplies a
prime-cyclic tower

$$
M=K_0\subset K_1\subset\cdots\subset K_t=L,
\qquad [K_i:K_{i-1}]\text{ prime and cyclic}.
\tag{1.8}
$$

The endpoint $L$ is the field denoted $F^{\mathrm{tar}}$ in Book 178. Every place above
$2\ell$ splits at every step, the joint residual--cyclotomic image is preserved at every
$K_i$, and each active place at the top has trivial residual representation and residue
cardinality congruent to one modulo $\ell$. Book 178 verifies Book 109, Proposition 14.4 for
the upper packet and retains its cyclic base-change and attachment compatibilities. We shall
use the tower for a different, simpler purpose: to descend the minimal packet attached to the
chosen point back to $M$.

### 1.3 How the two constructions fit together

The mathematical relation between the constructions is summarized by

$$
\begin{array}{c}
\text{Book 178: broad support and its finite minimal quotient over }L\\
\Downarrow\\
\text{Book 181: the chosen primitive lift }\rho\text{ over }\mathbf Q\\
\Downarrow\\
\rho|_{G_L}\text{ factors through the previously constructed Hecke action}\\
\Downarrow\\
\text{the resulting packet descends through (1.8) to }M.
\end{array}
\tag{1.9}
$$

The upper packet used in Book 178 is special at the auxiliary active places; the chosen lift
$\rho$ is unramified there. They are therefore different points of the broad deformation
space. The upper point proves that the broad Hecke module is nonzero and ultimately that the
broad ring has nilpotent kernel in a finite Hecke algebra. The minimal quotient of that ring
then helps construct $\rho$. Once $\rho$ exists, its unramified local behavior places it back
on the minimal quotient, so the same nilpotent-kernel theorem attaches an automorphic packet
to it. This distinction between the two points is the mathematical reason the argument is not
circular.

## 2. The signed-special local representation

The later packet construction needs more than conductor one at the dyadic place. We therefore
describe on the chosen lattice the local object that must survive every completely split
restriction.

### 2.1 Primitive monodromy, line, and sign

Choose an $\ell$-primary tame parameter

$$
t_\ell:I_2\twoheadrightarrow\mathbf Z_\ell
$$

and arithmetic Frobenius $\phi_2$ satisfying

$$
t_\ell(\phi_2\sigma\phi_2^{-1})=2t_\ell(\sigma).
\tag{2.1}
$$

Wild inertia acts trivially, and on the chosen lattice

$$
\rho(\sigma)=1+t_\ell(\sigma)N,
\qquad
N^2=0,
\qquad
\bar N:=N\bmod\varpi\ne0.
\tag{2.2}
$$

If $F_2=\rho(\phi_2)$, then

$$
F_2NF_2^{-1}=2N.
\tag{2.3}
$$

The matrix $N$ is primitive: at least one of its entries is a unit. Put

$$
\mathscr L=\ker N=\operatorname{im}N.
\tag{2.4}
$$

This is a saturated direct-summand line. In a basis with $N=e_{12}$, the
Frobenius-semisimplification has the form

$$
F_2^{\mathrm{ss}}=
\begin{pmatrix}
2\varepsilon_2&0\\
0&\varepsilon_2
\end{pmatrix},
\qquad
\varepsilon_2\in\{1,-1\}.
\tag{2.5}
$$

Thus arithmetic Frobenius acts on $\mathscr L$ by $2\varepsilon_2$ and on the quotient by
$\varepsilon_2$. The resulting integral tuple is

$$
(N,\mathscr L,\varepsilon_2,F_2NF_2^{-1}=2N,
 N\bmod\varpi\ne0).
\tag{2.6}
$$

### 2.2 The resulting local invariants

**Lemma 2.1 (primitive signed-special invariants).** The rational Weil--Deligne
representation of $\rho|_{G_{\mathbf Q_2}}$ has nonzero rank-one monodromy. Its inertia-fixed
line is $\mathscr L$, its Frobenius sign is $\varepsilon_2$, and its Artin conductor exponent
is one.

**Proof strategy.** Primitivity first makes $N$ nonzero. Linear algebra then determines its
rank, kernel, and image, while the tame exponential formula identifies the inertia invariants.

**Proof.** A nonzero square-zero endomorphism of a two-dimensional characteristic-zero vector
space has rank one. Since $N^2=0$, its image is contained in its kernel; both have dimension
one, proving (2.4). The image of $t_\ell$ is dense in $\mathbf Z_\ell$, so a vector fixed by
inertia is precisely a vector killed by $N$. Hence the invariant space is $\mathscr L$.
Wild inertia is trivial, and the tame conductor exponent is

$$
2-\dim\mathscr L=1.
$$

Equation (2.3) makes the line Frobenius-stable, and (2.5) gives its sign. $\square$

Conductor one alone would forget both the primitive thickness of the integral extension and
the choice of Frobenius eigenline. Later references to the dyadic tuple mean (2.6).

### 2.3 Literal preservation at split places

**Lemma 2.2 (split restriction).** Let $F/\mathbf Q$ be a number field in which $2$ splits
completely. For every $v\mid2$, restriction to $G_{F_v}$ preserves the tuple (2.6) literally,
including primitivity, the saturated line, the sign, and conductor exponent one. If $\ell$
also splits completely, the compatible coefficient-linear finite-flat models of
$\rho\bmod\varpi^n$ are preserved literally at every $v\mid\ell$.

**Proof.** Complete splitting identifies $F_v$ with the corresponding rational local field.
After compatible choices of decomposition groups, restriction is the identity on the local
representation and its lattice. The finite-flat models are simply base-changed along the
identity extension. $\square$

This use of splitting is essential at $2$. Under a ramified extension the tame parameter is
multiplied by the ramification index; if that index is divisible by $\ell$, a primitive
monodromy matrix can become zero after reduction even though its rational monodromy remains
nonzero.

## 3. The broad deformation ring and its Hecke action

The upper packet of Book 178 and the chosen lift have different local behavior at the active
auxiliary primes, so they do not lie on one narrow special deformation component. Both do lie
on a broader tame-unipotent space. The upper packet is used there to prove a finite Hecke
action with nilpotent kernel; the chosen lift reaches the same space through its unramified
quotient. This common ambient ring is what turns the already proved support theorem into
automorphy of the newly chosen point.

### 3.1 The broad ring and its minimal quotient

Let $P_L$ be the set of places of $L$ above Book 178's actual target set. At a member of
$P_L$, the broad problem imposes tame-unipotent inertia with characteristic polynomial
$(X-1)^2$, but it imposes no distinguished special line, sign, or nonzero-monodromy equation.
At the places above $2$ it retains the named signed-special factor (2.6), at the places above
$\ell$ it retains the selected finite-flat factor, and away from these places and $P_L$ it is
unramified. Write its ring as

$$
R_L^{\mathrm{uni}}(P_L).
$$

Setting inertia equal to the identity at every member of $P_L$ gives Book 178's canonical
surjection

$$
R_L^{\mathrm{uni}}(P_L)\twoheadrightarrow R_L^{\mathrm{SP}},
\tag{3.1}
$$

where $R_L^{\mathrm{SP}}$ represents the minimal problem: signed-special at $2$, finite flat
at $\ell$, and unramified everywhere else.

Book 178, Theorems 12.1--12.2 also retain a finite definite Hecke action

$$
R_L^{\mathrm{uni}}(P_L)\longrightarrow
\mathbb T_L^{\mathrm{uni}}(P_L)
\tag{3.2}
$$

whose kernel is nilpotent. In particular, every characteristic-zero field-valued point of the
broad ring factors through the automorphic action. Both (3.1) and (3.2) were constructed from
the upper packet before the minimal point was chosen.

### 3.2 Restriction of the chosen point

**Proposition 3.1 (the chosen point lies on the minimal quotient).** Restriction of (1.2) to
$G_L$ defines a characteristic-zero point

$$
x_L:R_L^{\mathrm{SP}}\longrightarrow\mathcal O'
\tag{3.3}
$$

after a finite coefficient extension $\mathcal O'/\mathcal O$. Its precomposition with (3.1)
is a point of $R_L^{\mathrm{uni}}(P_L)$.

**Proof.** The determinant of $\rho|_{G_L}$ is the restricted cyclotomic character. Every
place above $2\ell$ splits completely in the target-preparation tower, so Lemma 2.2 identifies
the dyadic signed-special condition and the coefficient-prime finite-flat condition with the
represented local factors over $L$. At every other finite place, including every member of
$P_L$, the representation is unramified by (1.3). It therefore satisfies the minimal local
condition everywhere. Universality gives (3.3), and precomposition with (3.1) gives the broad
point. $\square$

The decisive point is the direction of (3.1). A point of the minimal quotient automatically
gives a point of the broad ring. No claim is made that the upper packet's exact enhanced
special ring surjects onto the minimal ring.

### 3.3 The automorphic packet over the target field

The target ring $\mathcal O'$ is a characteristic-zero domain, so the composite

$$
R_L^{\mathrm{uni}}(P_L)\longrightarrow R_L^{\mathrm{SP}}
\xrightarrow{x_L}\mathcal O'
\tag{3.4}
$$

kills the nilpotent kernel of (3.2). It therefore factors through the finite automorphic
action. The corresponding eigencharacter gives a parallel-weight-two packet over $L$.
The represented Galois action agrees with $\rho|_{G_L}$ at all unramified Frobenius elements;
absolute residual irreducibility and Brauer--Nesbitt identify the rational representations.
After one coefficient extension, the stable lattices are homothetic, so the lattice can be
chosen to be the restriction of the lattice in (1.2). Thus the automorphic realization keeps
the integral local structures at $2$ and $\ell$.

## 4. The cyclic return to the Galois field

The support theorem lives over $L$, whereas the later elementary-field construction needs the
Galois field $M$. The tower (1.8) was introduced for the target comparison, but its exact
splitting and disjointness properties also make the return from $L$ to $M$ automatic for the
new minimal packet.

### 4.1 The temporary target-preparation tower

At each step $K_i/K_{i-1}$ of (1.8), every place above $2$ and $\ell$ splits. All other
ramification of $\rho|_{G_{K_{i-1}}}$ is absent. Book 178 proves, using Book 109, Chapter 14,
that the residual image stays unchanged along the tower. In particular,

$$
\bar\rho|_{G_{K_i}}\text{ is absolutely irreducible}
\tag{4.1}
$$

for every $i$.

The original upper packet used to build (3.2) was base-changed upward through this tower with
the selected components and attachment maps preserved. For the minimal packet arising from
(3.4), we must verify descent rather than borrow a property of that different packet.

### 4.2 Selectedness of every descent fibre

**Proposition 4.1 (automatic cyclic descent for the minimal point).** At every step of (1.8),
the packet attached to the appropriate restriction of $\rho$ satisfies all local-fibre,
quotient-twist, trace-comparison, and real-selector conditions required for cyclic descent.

**Proof strategy.** The only ramified local factors of $\rho$ occur at places which split
throughout the tower. At every nonsplit finite place its parameter is an unramified pair, so
Book 109's complete calculation of cyclic extension fibres applies.

**Proof.** Consider $K_i/K_{i-1}$. Take the finite set consisting of the dyadic and
$\ell$-adic places of $K_{i-1}$. It splits completely in $K_i$, and $\rho$ is unramified
outside it. Book 109, Proposition 13.4 therefore applies. At a split protected place the
selected component is repeated literally. At a nonsplit place the upper parameter is a split
unramified pair. For an odd prime cyclic step its two character lines extend separately. For
a quadratic step they either extend separately or are exchanged, in which case the extension
is dihedral. A ramified dyadic quadratic case cannot occur because the dyadic places split.
Consequently every fixed-determinant extension, every norm antecedent, and every quotient
twist is in the selected trace-comparable range. The totally real construction splits the
real places, so the parallel-weight-two discrete-series factor supplies the strongly cuspidal
selector. $\square$

This is stronger than observing that one descent exists. It verifies the complete fibre in
which the quotient-character correction selected by the extending representation must lie.

### 4.3 Residual images and cuspidality

At a cyclic step an arbitrary automorphic descent is defined only up to a quotient character.
The representation $\rho$ is already defined over $\mathbf Q$, hence over every lower field
$K_{i-1}$. Book 109, Theorem 13.3 compares extensions and selects the unique quotient twist
whose attached representation is $\rho|_{G_{K_{i-1}}}$. Repeating this from the top of (1.8)
to the bottom gives a coherent packet over $M$.

Equation (4.1) also forces every intermediate packet to be cuspidal. A noncuspidal rank-two
isobaric representation has a reducible attached representation, while a characteristic-zero
representation with absolutely irreducible residual lattice is irreducible. Thus no
two-character endpoint occurs during descent.

## 5. Potential automorphy of the chosen lift

We now collect the two decisive consequences. Unlike a general potential-automorphy
criterion, their inputs are actual objects already produced in Books 178 and 181.

### 5.1 Automorphy from the target Hecke action

**Theorem 5.1 (automorphy over the prepared target field).** Let $\rho$ be the primitive Frey
lift constructed in Book 181, Theorem 1.2, and let $L$, (3.1), and (3.2) be the field and maps
constructed in Book 178, Theorems 12.1--12.2. Then, after one finite coefficient extension,
there is a
parallel-weight-two cuspidal representation $\pi_L$ such that

$$
r_{\pi_L,\lambda_0}\simeq\rho|_{G_L}.
\tag{5.1}
$$

On the stable lattice corresponding to the chosen lattice of $\rho$, every place above $2$
has the exact tuple (2.6), every place above $\ell$ has the compatible selected finite-flat
models, and every other finite place is unramified.

**Proof.** Proposition 3.1 places $\rho|_{G_L}$ on the minimal quotient and hence on the broad
ring. The composite (3.4) kills the nilpotent kernel of the finite automorphic action (3.2),
so it gives an automorphic eigencharacter. The resulting packet has the same represented
Galois point as $\rho|_{G_L}$. Residual absolute irreducibility makes it cuspidal and identifies
the stable lattice up to homothety. Because the point factors through the exact minimal local
conditions, Lemma 2.2 preserves the dyadic and coefficient-prime structures and unramifiedness
elsewhere. $\square$

### 5.2 Descent to the split Galois field

**Theorem 5.2 (chosen-lift automorphy over the Galois top).** With $M$ and $L$ as in Section
1.2, there is a selected parallel-weight-two cuspidal representation $\pi_M$ satisfying

$$
r_{\pi_M,\lambda_0}\simeq\rho|_{G_M}.
\tag{5.2}
$$

The field $M/\mathbf Q$ is totally real and Galois with nonsolvable symmetric group, is of
positive even degree, is disjoint from the full avoidance field, and is completely split at
$2$, $3$, and $\ell$. The restricted representation remains absolutely irreducible.

**Proof.** Begin with $\pi_L$ from Theorem 5.1. Proposition 4.1 verifies every selected cyclic
descent condition at every step of (1.8). Book 109, Theorem 13.3 uses the extension
$\rho|_{G_{K_{i-1}}}$ to choose the correct quotient twist and descends one step. Induction
gives $\pi_M$ and (5.2). Residual irreducibility throughout the tower proves cuspidality. The
remaining assertions about $M$ were proved in Book 178's split Galois specialization and its
closure-level avoidance argument. $\square$

The direction of this proof matters. We do not try to ascend from an arbitrary field of
potential automorphy to a normal closure. The automorphic support is evaluated at the prepared
top $L$, and the explicitly prepared solvable tower returns the packet to the Galois field
which Book 178 had already constructed.

### 5.3 Local properties after descent

At a place above $2$ or $\ell$, every layer of (1.8) is split. The local packet and attached
representation are therefore repeated, not transformed. Consequently $\pi_M$ retains the
primitive matrix $N$, the saturated line $\mathscr L$, the sign $\varepsilon_2$, the relation
$F_2NF_2^{-1}=2N$, and the nonvanishing of $N\bmod\varpi$. It also retains the compatible
finite-flat models at the original coefficient prime.

At every other finite place the representation $\rho|_{G_M}$ is unramified. The selected
descent may pass through principal or dihedral alternatives in an intermediate local fibre,
but the quotient twist chosen by $\rho$ returns the attached bottom representation to the
unramified member. This conclusion concerns the Galois parameter; it does not assert a
uniform geometric description of every intermediate automorphic type.

## 6. Elementary fixed fields and basic carriers

The nonsolvable Galois group prevents direct cyclic descent from $M$ to $\mathbf Q$, but every
elementary subgroup is solvable. This produces the finite family of automorphic packets used
in Brauer induction.

### 6.1 Construction of the elementary packets

Let $H\leq\Gamma$ be elementary and put

$$
F_H=M^H.
\tag{6.1}
$$

Since $\Gamma\simeq S_d$ with $d\geq5$, no elementary subgroup equals $\Gamma$. Hence

$$
[F_H:\mathbf Q]=[\Gamma:H]\geq2.
\tag{6.2}
$$

Choose a subnormal prime-cyclic series in $H$ and read its fixed fields from $M$ down to
$F_H$. The primes $2$ and $\ell$ split completely at every step, and $\rho$ is unramified
away from them. Book 109, Proposition 13.4 therefore verifies the whole selected extension
and norm-antecedent fibres, all quotient twists, trace comparison, and the real selector.
Book 109, Theorem 13.3 then uses the representation $\rho|_{G_{F_H}}$ to choose coherent
twists. We obtain a selected cuspidal parallel-weight-two packet $\pi_H$ with

$$
r_{\pi_H,\lambda_0}\simeq\rho|_{G_{F_H}}.
\tag{6.3}
$$

The fixed-determinant descent keeps the automorphic central character trivial, in the
normalization where the attached covariant representation has determinant cyclotomic.

The construction also applies to every subgroup appearing inside a chosen prime-cyclic
refinement. Different refinements give the same selected packet: both candidates attach to
the same absolutely irreducible restriction of $\rho$, and strong multiplicity one identifies
them.

Because $3$ splits completely in $M$, it splits completely in every $F_H$ and at every step
of these towers. The packet $\pi_H$ is spherical at every place above $3$. It is likewise
spherical at the automorphic level above $\ell$, while its distinguished $\ell$-adic stable
lattice carries the finite-flat condition.

### 6.2 Parity-complete compact carriers

**Proposition 6.1 (basic carrier for every elementary packet).** For every elementary
$H\leq\Gamma$, the packet $\pi_H$ has a compact one-split quaternionic curve carrier. The
carrier can be chosen split at every place above $3$ and $\ell$, with hyperspecial level there.
Its rational packet block yields a rank-two semisimple Galois realization at every coefficient
place of a common number field.

**Proof strategy.** The finite ramification set of the quaternion algebra corrects the parity
of the $[F_H:\mathbf Q]-1$ compact real factors. Complete dyadic splitting supplies a special
finite place when that correction is needed.

**Proof.** Put $e=[F_H:\mathbf Q]\geq2$. If $e$ is odd, take no finite ramified place. Then
$e-1$ is even. If $e$ is even, choose one dyadic place $w_2$ and ramify the quaternion algebra
there; now

$$
(e-1)+1\equiv0\pmod2.
\tag{6.4}
$$

In both cases the total ramification set has even cardinality and contains all but one real
place, so Book 104 supplies the compact one-split inner form and transfers the selected packet.
The algebra is split at every place above $3\ell$, hence the spherical packet factors there
admit hyperspecial level. Book 125 realizes the packet block in curve cohomology, and Books
126--127 extract its rank-two raw multiplicity representation and its global semisimplification
at every coefficient place. Since only finitely many elementary subgroups occur, one finite
number field contains all packet coefficients and splits all selected packet blocks. $\square$

This proposition proves packet occurrence and attachment. It does not yet identify nonzero
dyadic monodromy after global semisimplification at every coefficient place. The selected
three-adic identification is proved in Chapter 7.

### 6.3 Attachment under cyclic change and twisting

**Proposition 6.2 (cyclic and twisting compatibility).** The semisimple attachments from
Proposition 6.1 commute with every selected prime-cyclic base change and every finite-order
quotient twist used to construct the elementary packets.

**Proof.** At the density-one set of places where the packets, field extensions, and
characters are unramified, cyclic base change restricts the local parameter and a quotient
twist tensors it by the corresponding finite character. The attached semisimple Galois
representations satisfy the same Frobenius-polynomial identities. Chebotarev density and
Brauer--Nesbitt identify the two continuous semisimple representations. $\square$

In particular, the distinguished realization of every elementary packet is not a new
assumption: it is the restriction (6.3), and all overlaps in the cyclic construction carry
the same attachment.

## 7. The selected coefficient place above three

For the final selected member, one coefficient place above $3$ is enough. This narrower
problem has a complete solution from good-reduction finite-flat geometry and avoids any need
for a uniform comparison at every coefficient place.

### 7.1 Targetwise dyadic parity carriers

Fix an elementary field $F_H$ and a dyadic target $v$. If $[F_H:\mathbf Q]$ is odd, the basic
quaternion algebra of Proposition 6.1 is split at every dyadic place. Book 168, Proposition
7.6A uses the split common-adjoint unitary curve to compute the raw signed-special pair at
$v$.

Suppose instead that $[F_H:\mathbf Q]$ is even. Complete splitting of $2$ and (6.2) provide
a second dyadic place $w\ne v$. Use $w$ as the single finite parity place, so the quaternion
algebra is split at the target $v$. Book 118 constructs a CM quadratic field ramified at $w$
and split at every other dyadic place. At $w$, Book 122's extreme local factor is a rigid
one-point integral model; at $v$, the split incidence chart, graph line, and unnormalized
$U_v$ correspondence remain available.

One ramified quadratic comparison could leave a scalar quadratic inertia twist. Book 168,
Proposition 7.6B uses two ramified quadratic classes with distinct inertia characters. A
rank-one-monodromy Weil--Deligne representation has scalar finite inertia, and a scalar
character trivial on both distinct inertia kernels is trivial. Both comparison extensions
have residue degree one, so the Frobenius eigenvalue on the invariant line, and hence the sign
$\varepsilon_2$, is unchanged. Cycling the spectator $w$ gives this construction separately
for every target $v$.

This is a targetwise family of parity carriers. It is not a claim that one integral curve
model simultaneously supplies every dyadic target, and it uses no integral raw-to-raw
comparison between the basic and unitary curves.

### 7.2 The finite-flat irreducibility bridge

Choose the common packet coefficient field $K$ large enough for all elementary packets and
fix a place

$$
\nu\mid3
\tag{7.1}
$$

of $K$.

**Proposition 7.1 (selected-three packet and signed-special bridge).** For every elementary
$H\leq\Gamma$, let $r_{H,\nu}$ be the semisimple realization of $\pi_H$ at $\nu$. Then:

1. $r_{H,\nu}$ is absolutely irreducible;
2. the raw rank-two multiplicity representation on the basic compact carrier is irreducible
   and equals $r_{H,\nu}$; and
3. at every dyadic place, $r_{H,\nu}$ has the scalar realization of the exact common pair
   (2.3)--(2.5): nonzero rank-one monodromy, invariant line $\mathscr L$, sign
   $\varepsilon_2$, and conductor exponent one.

**Proof strategy.** Good unitary covers at the places above $3$ place the raw packet plane
inside the Tate module of an abelian scheme. Finite-flat closure makes any hypothetical
rank-one constituent locally algebraic. Such constituents would force a cuspidal packet to be
an isobaric sum of characters. Irreducibility then makes global semisimplification harmless,
after which the targetwise dyadic comparisons of Section 7.1 transfer the full special pair.

**Proof.** Every place above $3$ is equal to $\mathbf Q_3$, and Proposition 6.1 gives
hyperspecial packet level there. Book 168, Theorem 7.6C constructs a protected good unitary
cover, embeds the raw packet plane after finite restriction into the Tate module of a good
abelian scheme, and applies Book 129's all-level finite-flat closure. If the semisimple
realization were reducible, closure and quotient would give finite-flat towers on its two
rank-one constituents. Book 54's rank-one finite-flat calculation makes those characters
locally algebraic at $3$. Global class field theory and isobaric multiplicity one would then
express the cuspidal packet $\pi_H$ as a sum of two algebraic characters, a contradiction.

Thus $r_{H,\nu}$ is absolutely irreducible. A two-dimensional raw representation with that
semisimplification is itself irreducible and equal to its semisimplification. Book 168,
Corollary 7.6D now applies the split or ramified-spectator comparison of Section 7.1 at each
dyadic target. Since $3\ne2$, the local Weil--Deligne comparison is in the prime-to-coefficient
range and carries the nonzero monodromy, line, and Frobenius sign to $r_{H,\nu}$. $\square$

The finite-flat construction in this proof is a bridge to irreducibility. Proposition 7.1
does not choose the final ground-field integral lattice at $\nu$; that is a separate later
integral construction.

### 7.3 The scope of the selected-three result

Proposition 7.1 concerns the single chosen place $\nu\mid3$. Its proof uses finite-flat
geometry at three and does not require a smooth-proper Hodge--Tate comparison for every
carrier and every coefficient place. It also does not prove absolute irreducibility at the
coefficient places above two. Those two uniform statements are stronger than the
selected-three result and play no role in Theorem 9.1.

The original lift still has its compatible finite-flat lattice at the coefficient prime
$\ell$, but Proposition 7.1 does not construct such lattices at every odd coefficient prime.
An arbitrary stable lattice in a rational packet realization need not have finite-flat
quotients. Thus no all-odd integral-model theorem is asserted or needed here.

## 8. Auxiliary Galois comparisons

Away from the nonzero-monodromy place, the packet array needs only common unramified Galois
pairs. These can be proved without the selected-three argument and without a description of
ramified automorphic types.

### 8.1 Common unramified algebraic pairs

For an elementary $H$, let $W^{\mathrm{raw}}_{H,\tau}$ be the raw rank-two multiplicity
representation on the carrier of Proposition 6.1, and let

$$
r_{H,\tau}=(W^{\mathrm{raw}}_{H,\tau})^{\mathrm{ss}}
\tag{8.1}
$$

be its global semisimplification at a coefficient embedding $\tau$.

**Proposition 8.1 (common unramified algebraic pair).** Let $w$ be a finite place of $F_H$
above a rational prime $p\ne2$, and suppose the residue characteristic of $\tau$ is different
from $p$. Then both

$$
W^{\mathrm{raw}}_{H,\tau}|_{G_{(F_H)_w}}
\quad\text{and}\quad
r_{H,\tau}|_{G_{(F_H)_w}}
\tag{8.2}
$$

are unramified. Over the common packet field there is an unramified algebraic
Frobenius-semisimple pair $D_{H,w}$ such that

$$
\operatorname{WD}_w(r_{H,\tau})^{\mathrm{F\text{-}ss}}
\simeq D_{H,w}\otimes_\tau\Omega.
\tag{8.3}
$$

**Proof strategy.** At the distinguished coefficient embedding the raw representation is
already the irreducible restriction of $\rho$. Its conductor is therefore zero away from
$2\ell$, and coefficient independence carries that zero conductor and its invariant
Frobenius polynomial to every other coefficient. At the rational prime $\ell$, Book 118,
Corollary 10.3A supplies a finite unitary cover protected at $\ell$, while the good-model
argument of Book 121, Section 11.4 makes the unitary cohomology unramified. Pullback and trace
then transfer unramifiedness to the basic carrier.

**Proof.** First assume $p\ne\ell$. At the distinguished embedding $\lambda_0$, equation
(6.3) identifies the semisimplification of $W^{\mathrm{raw}}_{H,\lambda_0}$ with the absolutely
irreducible representation $\rho|_{G_{F_H}}$. Since both have dimension two, the raw
representation is already irreducible and

$$
W^{\mathrm{raw}}_{H,\lambda_0}\simeq\rho|_{G_{F_H}}.
\tag{8.4}
$$

It is unramified at $w$ by (1.3). Book 61 proves coefficient independence of the Artin
conductor and the inertia-invariant Frobenius polynomial for the selected Jacobian
multiplicity factor. The conductor is zero at $\lambda_0$, hence zero at every $\tau$ in the
stated range. Its common Frobenius polynomial defines $D_{H,w}$. Because monodromy is zero,
Book 128's zero-monodromy comparison passes the same pair to the global semisimplification.

Now let $p=\ell$, and write $B_H/F_H$ for the quaternion algebra defining the basic carrier.
Choose an imaginary quadratic field $K_0/\mathbf Q$ which is split at $\ell$ and nonsplit at
every rational prime below the finite ramification of $B_H$. Such a choice exists by weak
approximation because that ramification is empty or consists of the single dyadic spectator.
Put $L_H=F_HK_0$. Then $L_H$ embeds in $B_H$, and $\ell$ splits completely in $L_H$.

After centrally saturating the derived level, which does not change vectors of the
trivial-central-character packet, apply Book 118, Corollary 10.3A with protected set
$S=\{\ell\}$. It gives a finite extension $E_H/L_H$, unramified at every place above $\ell$,
and a finite surjective morphism

$$
f:Y_{E_H}\longrightarrow X_{E_H}                              \tag{8.3a}
$$

from a union of unitary PEL components to the selected basic quaternionic component union.
All level shrinking occurs away from $\ell$, and both sides remain hyperspecial there. At a
place $x\mid\ell$ of $E_H$, the hypotheses of Book 121, Section 11.4 hold: $\ell$ is odd,
$F_H$ and $K_0$ are split at $\ell$, $B_H$ is split above $\ell$, and the level and lattice
are hyperspecial and self-dual. Book 121, Theorem 11.2 therefore gives $Y_{E_H}$ a smooth
projective model at $x$ and makes the identity component of its relative Picard scheme an
abelian scheme. Smooth proper base change shows that its prime-to-$\ell$ cohomology is
unramified.

On rational cohomology, trace after pullback by $f$ is multiplication by the nonzero degree of
$f$. Hence the basic-curve cohomology, and in particular its raw packet factor, is a direct
summand after restriction to $G_{E_H}$. Since $(E_H)_x/(F_H)_w$ is unramified, their inertia
groups agree; the raw factor is therefore unramified already over $(F_H)_w$. Its semisimplification
is unramified as well, and the coefficient-independent Frobenius polynomial defines the same
pair $D_{H,w}$ as before. $\square$

The proposition includes the rational prime $3$ whenever the coefficient embedding does not
induce $\nu$, and it includes the original prime $\ell$ at all coefficient places away from
$\ell$. At a coefficient's own residue characteristic it makes no local Weil--Deligne claim.

### 8.2 Twisting and induction

If an elementary term is twisted by a finite quotient character $\theta$, its local algebraic
pair is

$$
D_{H,w}\otimes\theta_w.
\tag{8.5}
$$

When $D_{H,w}$ is unramified, the conductor of the tensor is twice the conductor of
$\theta_w$. Weil induction of (8.5) is again algebraic. Thus all local Galois objects needed
for restriction, twisting, induction, and Mackey decomposition exist over one finite packet
field. Their formation commutes with coefficient embeddings.

These facts do not say that each twisted term is unramified. A quotient character may be
ramified, and positive and negative induced terms can retain ramification even when a later
rank-two complement is unramified. Proposition 8.1 supplies the untwisted elementary anchor
from which those exact Galois calculations begin.

### 8.3 Stronger local types lie beyond the comparison

An automorphic theorem prescribing a principal or dihedral type at every auxiliary place is
strictly stronger than Proposition 8.1. It would first have to prove that the relevant cyclic
quotient is tame. It would then need a fine semistable model carrying the type projectors,
component routing, character or exchange lines, and normalized Frobenius return maps. The
unramified algebraic Galois pair (8.3) does not manufacture those automorphic objects.

Such a type theorem is unnecessary for Theorem 9.1. The Galois comparison uses the pairs
(8.3), finite-character twisting, and Weil induction, none of which requires a principal or
dihedral automorphic type at every auxiliary place. The stronger automorphic geometry is
outside the scope of this book.

## 9. The selected-three packet theorem

We can now assemble the preceding constructions. The dyadic signed-special comparison is made
at one coefficient place $\nu\mid3$, while the unramified pairs away from two are algebraic
and can be specialized at every coefficient place of different residue characteristic. This
asymmetry is sufficient for the Brauer-induction argument: it provides one irreducible
three-adic member with the full dyadic pair and supplies the coefficient-independent good
local data used in restriction, twisting, and induction.

### 9.1 Automorphic packets and their selected-three realizations

**Theorem 9.1 (selected-three automorphic packet family).** Suppose a normalized primitive
Fermat solution of prime exponent $\ell\geq7$ is given, and let $\rho$ be the primitive lift
whose existence is proved in Book 181, Theorem 1.2. Then the fields and Hecke action constructed
in Book 178, together with the descent and comparison arguments of this book, give the
following objects and properties.

1. There is a totally real Galois extension $M/\mathbf Q$ with
   $\Gamma\simeq S_d$ for some $d\geq5$, disjoint from the full avoidance field and completely
   split at $2$, $3$, and $\ell$. Both $\rho|_{G_M}$ and its residual representation are
   absolutely irreducible.
2. There is a selected cuspidal parallel-weight-two packet $\pi_M$ with

   $$
   r_{\pi_M,\lambda_0}\simeq\rho|_{G_M}.
   \tag{9.1}
   $$

3. For every elementary subgroup $H\leq\Gamma$, there is a selected cuspidal
   parallel-weight-two packet $\pi_H$ over $F_H=M^H$, independent of the chosen prime-cyclic
   refinement, with

   $$
   r_{\pi_H,\lambda_0}\simeq\rho|_{G_{F_H}}.
   \tag{9.2}
   $$

   These attachments commute with the selected cyclic base changes and quotient twists.
4. The chosen lattice in (1.2) has the primitive dyadic record

   $$
   N^2=0,
   \quad N\bmod\varpi\ne0,
   \quad\mathscr L=\ker N=\operatorname{im}N,
   \quad F_2NF_2^{-1}=2N,
   \tag{9.3}
   $$

   with sign $\varepsilon_2$, and compatible coefficient-linear finite-flat quotients at
   $\ell$. Complete splitting preserves these data on $M$ and every $F_H$ at the distinguished
   embedding.
5. Every $\pi_H$ has a parity-correct compact one-split carrier, split and hyperspecial above
   $3\ell$, together with its rank-two semisimple realizations over one common packet field.
   For every dyadic target there is a split or ramified-spectator targetwise carrier computing
   the same raw signed-special pair.
6. For one chosen place $\nu\mid3$ of the common packet field, every $r_{H,\nu}$ is absolutely
   irreducible, equals its raw multiplicity representation, and has at every dyadic place the
   full common signed-special pair: nonzero rank-one monodromy, invariant line $\mathscr L$,
   sign $\varepsilon_2$, and conductor exponent one.
7. For every finite $w\nmid2$ of every $F_H$, there is an unramified algebraic pair $D_{H,w}$
   satisfying (8.3) at each coefficient embedding whose residue characteristic differs from
   that of $w$. These pairs are compatible with finite twisting, Weil induction, and the
   cyclic attachment identities.

**Proof.** Book 178 constructs the fields of Section 1.2 and the Hecke maps of Section 3.1.
Proposition 3.1 places the chosen restricted point on the minimal quotient and therefore on
the broad ring. Theorem 5.1 factors this point through the Hecke action, and Theorem 5.2
uses the target-preparation tower and Book 109's cyclic descent theorem to produce $\pi_M$.
This proves items 1--2 and carries the integral local data of item 4.

For every elementary $H$, Section 6.1 applies Book 109, Proposition 13.4 and Theorem 13.3 to
construct $\pi_H$ and prove (9.2); Proposition 6.2 gives the stated compatibility. Proposition
6.1 constructs the basic carriers and their attachments. Section 7.1 constructs the
targetwise parity carriers, and Proposition 7.1 applies the fixed-three finite-flat bridge to
prove item 6. Finally Proposition 8.1 constructs the common unramified pairs, and Section 8.2
proves their twisting and induction compatibility. $\square$

The only arithmetic starting point of the theorem is the Frey solution from which Book 181
constructs $\rho$; the fields, broad Hecke action, and cyclic tower are theorems of Book 178.
The conclusion is intentionally narrower than a uniform all-coefficient theory. It gives the
raw-to-global dyadic comparison at $\nu\mid3$, not at every coefficient place; it does not
prove coefficient-two absolute irreducibility, finite-flat models at all odd primes, or
principal and dihedral automorphic types at every auxiliary place. None of those stronger
statements is needed for the automorphy and elementary packet family proved here.

### 9.2 Conclusion

The chosen lift is now automorphic over the original split Galois field of the two-prime
construction. Its restriction to the prepared target field satisfies the minimal local
conditions, so the quotient map places it inside the broad deformation problem. The finite
Hecke action attaches a packet there, and cyclic descent through the prepared tower brings
that packet back to the split symmetric field.

From that field, complete splitting and the unramified extending representation make every
elementary descent fibre selected. Parity-correct compact carriers give actual packet
attachments, the good-reduction finite-flat bridge preserves the full dyadic special pair at
the chosen place above three, and coefficient-independent conductor theory supplies the
unramified algebraic pairs away from two. The result preserves the primitive dyadic line and
sign at the selected three-adic realization while giving the algebraic local pairs needed for
restriction, twisting, and induction. This is exactly the mathematical input supplied by the
book; uniform Hodge--Tate comparison, coefficient-two irreducibility, all-odd integral models,
and stronger automorphic local types are neither used nor concluded.
