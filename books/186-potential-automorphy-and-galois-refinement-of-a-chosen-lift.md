# Potential Automorphy and Galois Refinement of a Chosen Lift

## Contents

1. [The exact chosen-lift theorem](#1-the-exact-chosen-lift-theorem)
   - [The fixed characteristic-zero point](#11-the-fixed-characteristic-zero-point)
   - [The simultaneous theorem](#12-the-simultaneous-theorem)
   - [Why the construction is genuinely simultaneous](#13-why-the-construction-is-genuinely-simultaneous)
   - [Conventions](#14-conventions)
2. [The input and avoidance ledgers](#2-the-input-and-avoidance-ledgers)
   - [The balanced minimal lift](#21-the-balanced-minimal-lift)
   - [The represented local tuple](#22-the-represented-local-tuple)
   - [The finite avoidance field](#23-the-finite-avoidance-field)
   - [The obstruction that must be removed geometrically](#24-the-obstruction-that-must-be-removed-geometrically)
3. [A minimal dihedral companion over a harmless real base](#3-a-minimal-dihedral-companion-over-a-harmless-real-base)
   - [An everywhere-unramified CM quadratic extension](#31-an-everywhere-unramified-cm-quadratic-extension)
   - [The auxiliary coefficient prime](#32-the-auxiliary-coefficient-prime)
   - [The algebraic Hecke character](#33-the-algebraic-hecke-character)
   - [The exact local profile of the companion](#34-the-exact-local-profile-of-the-companion)
4. [The projective automorphic-incidence space](#4-the-projective-automorphic-incidence-space)
   - [The split rank-two PEL datum](#41-the-split-rank-two-pel-datum)
   - [Fine moduli and the finite cusp boundary](#42-fine-moduli-and-the-finite-cusp-boundary)
   - [The paired-frame twist](#43-the-paired-frame-twist)
   - [Geometric connectedness and product monodromy](#44-geometric-connectedness-and-product-monodromy)
   - [Local seeds on the exact components](#45-local-seeds-on-the-exact-components)
   - [The projective interior carrier](#46-the-projective-interior-carrier)
5. [A projective moving curve and its generic Galois top](#5-a-projective-moving-curve-and-its-generic-galois-top)
   - [Weil restriction and the local opens](#51-weil-restriction-and-the-local-opens)
   - [A projective incidence curve](#52-a-projective-incidence-curve)
   - [A simply branched presentation with prescribed local fibers](#53-a-simply-branched-presentation-with-prescribed-local-fibers)
   - [The generic normal closure](#54-the-generic-normal-closure)
   - [Evaluation from the top](#55-evaluation-from-the-top)
6. [The controlled simultaneous specialization](#6-the-controlled-simultaneous-specialization)
   - [The specialization theorem](#61-the-specialization-theorem)
   - [Hilbert irreducibility with top-field avoidance](#62-hilbert-irreducibility-with-top-field-avoidance)
   - [Good reduction outside the controlled dyadic set](#63-good-reduction-outside-the-controlled-dyadic-set)
   - [Image preservation](#64-image-preservation)
   - [All completions and fixed fields](#65-all-completions-and-fixed-fields)
7. [Automorphy at the auxiliary prime](#7-automorphy-at-the-auxiliary-prime)
   - [The specialized geometric carrier](#71-the-specialized-geometric-carrier)
   - [The dihedral automorphic source over the top](#72-the-dihedral-automorphic-source-over-the-top)
   - [The exact auxiliary-prime deformation problem](#73-the-exact-auxiliary-prime-deformation-problem)
   - [Integral automorphic realization](#74-integral-automorphic-realization)
   - [The first exact minimal equality](#75-the-first-exact-minimal-equality)
   - [Changing coefficient prime](#76-changing-coefficient-prime)
8. [Automorphic incidence on the chosen component](#8-automorphic-incidence-on-the-chosen-component)
   - [The target-prime carrier](#81-the-target-prime-carrier)
   - [Place-by-place component identification](#82-place-by-place-component-identification)
   - [Exact-minimal residual occurrence](#83-exact-minimal-residual-occurrence)
   - [The simultaneous automorphic-incidence theorem](#84-the-simultaneous-automorphic-incidence-theorem)
9. [The clean target-prime equality](#9-the-clean-target-prime-equality)
   - [The deformation ring and faithful Hecke order](#91-the-deformation-ring-and-faithful-hecke-order)
   - [The Hecke-valued representation](#92-the-hecke-valued-representation)
   - [Taylor--Wiles systems and exact augmentation](#93-taylor-wiles-systems-and-exact-augmentation)
   - [Faithfulness, reducedness, and the equality](#94-faithfulness-reducedness-and-the-equality)
   - [Evaluation at the chosen point](#95-evaluation-at-the-chosen-point)
   - [Integral local--global compatibility](#96-integral-local-global-compatibility)
10. [Elementary fixed fields](#10-elementary-fixed-fields)
    - [The field family](#101-the-field-family)
    - [Prime-cyclic towers](#102-prime-cyclic-towers)
    - [Descent selected by the extending representation](#103-descent-selected-by-the-extending-representation)
    - [Compatibility of all local records](#104-compatibility-of-all-local-records)
11. [Coefficients, Frobenius polynomials, and purity](#11-coefficients-frobenius-polynomials-and-purity)
    - [Coefficient fields and lattices](#111-coefficient-fields-and-lattices)
    - [Frobenius data](#112-frobenius-data)
    - [Purity and conjugation](#113-purity-and-conjugation)
12. [Failure diagnostics](#12-failure-diagnostics)
    - [Why a nonproper carrier is insufficient](#121-why-a-nonproper-carrier-is-insufficient)
    - [Why no component jump is used](#122-why-no-component-jump-is-used)
    - [Why the old automorphy field is not transported](#123-why-the-old-automorphy-field-is-not-transported)
    - [Why the Galois closure is specialized directly](#124-why-the-galois-closure-is-specialized-directly)
13. [Dependency and hypothesis audit](#13-dependency-and-hypothesis-audit)
    - [Direct prerequisites](#131-direct-prerequisites)
    - [The decisive hypothesis matches](#132-the-decisive-hypothesis-matches)
    - [Circularity audit](#133-circularity-audit)
    - [Books not used](#134-books-not-used)
14. [Conclusion](#14-conclusion)

## 1. The exact chosen-lift theorem

Potential modularity of a residual representation is not the assertion needed in this book.
Book 185 has already selected one horizontal characteristic-zero point of a balanced minimal
deformation ring. Its integral finite-flat lattice, its labeled dyadic component, and its
unramified quotients away from the two distinguished primes are part of the object. The task is
to put that exact point on automorphic support over one controlled totally real Galois field.

There is a real obstruction to doing this with the usual nonproper two-prime realization
space. A specialization of that space can acquire new semistable bad primes. At such a prime
the auxiliary automorphic lift is special while the chosen lift is unramified. The two local
conditions meet only on the level-raising divisor; neither contains the other. This book does
not ask patching to cross that divisor.

Instead we alter the geometry before specializing. We construct a smooth projective curve
inside a fine split PEL space, wholly contained in its abelian-scheme locus, and carrying the
two paired torsion systems. We choose the auxiliary dihedral system to be unramified at every
finite place away from the coefficient prime and the already prescribed dyadic type.
Properness of the interior curve then forces the specialized abelian variety to have good
reduction at every other place. Its target-prime Tate factor is consequently an independently
automorphic characteristic-zero point of the exact minimal deformation problem. Only after
that incidence has been proved do we invoke minimal Taylor--Wiles patching.

### 1.1 The fixed characteristic-zero point

Fix a prime $\ell\ge7$, a finite extension $E/\mathbf Q_\ell$ with ring of integers
$\mathcal O$, uniformizer $\varpi$, and residue field $k$. Book 185 supplies, after the
declared finite coefficient extension, a continuous representation

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\mathcal O)
\tag{1.1}
$$

whose reduction is $\bar\rho$ and for which

$$
\det\rho=\chi_\ell,
\qquad
\rho\text{ is unramified outside }\{2,\ell\}.
\tag{1.2}
$$

Wild inertia at $2$ is trivial and a tame generator $\tau$ satisfies

$$
\rho(\tau)^2+\rho(\tau)+I=0.
\tag{1.3}
$$

At $\ell$, every quotient of the selected lattice is the generic fiber of the compatible
coefficient-linear finite locally free group scheme of weight $\{0,1\}$ fixed in Book 185.
The chosen point is not replaced by another horizontal point at any stage below.

For a finite totally real field $L$, let $R_L^{\min}$ denote the fixed-cyclotomic-determinant
deformation ring with the restricted versions of precisely these local conditions. The desired
automorphy assertion is an isomorphism, after embedding the two coefficient completions into a
common finite extension $C/\mathbf Q_\ell$,

$$
\rho|_{G_L}\otimes_EC
\simeq
\rho_{\pi_L,\lambda_L}\otimes_{E_{\pi_L,\lambda_L}}C
\tag{1.4}
$$

for a parallel-weight-two cuspidal representation $\pi_L$.

### 1.2 The simultaneous theorem

We state the endpoint now and prove its clauses in the order in which they are constructed.

**Theorem 1.1 (Galois-refined automorphy of the chosen lift).** Let $\rho$ be the balanced
minimal lift of a modularity-admissible datum in the exact sense of Book 185. Let $D/\mathbf Q$
be any finite Galois avoidance field containing the fields in Section 2.3, and let $S_0$ be any
finite set of rational places containing $\infty,2,\ell$ and the finite local and integral
places named before the construction. Then there are:

1. a real quadratic field $F_0/\mathbf Q$ in which every place in $S_0$ splits, and an
   everywhere-finite-unramified CM quadratic extension $K_0/F_0$;
2. an auxiliary prime $q\ge7$, $q\ne\ell$, and a rank-two dihedral residual representation
   $\bar\sigma$ of $G_{F_0}$ with cyclotomic determinant, coefficient-prime finite-flat type,
   the same tame order-three dyadic type as $\bar\rho$, and no other finite ramification;
3. a finite totally real Galois extension $M/\mathbf Q$ containing $F_0$, with
   $$
   M\cap D=\mathbf Q,
   \tag{1.5}
   $$
   such that every completion above a place in $S_0\cup\{q\}$ is a prescribed finite
   unramified extension (and $2$ splits completely), while every later named integral place
   has its entire prescribed finite local algebra;
4. a polarized PEL abelian variety $A/M$ with exact paired frames
   $$
   A[\lambda]\simeq\bar\rho|_{G_M}\otimes_kk_\lambda,
   \qquad
   A[\mathfrak q]\simeq\bar\sigma|_{G_M}\otimes_{k_q}k_{\mathfrak q},
   \tag{1.6}
   $$
   such that $A$ has good reduction at every finite place not above $2$ and its two rank-two
   factors lie on the restrictions of the named coefficient-prime and dyadic components;
5. a parallel-weight-two cuspidal representation $\Pi_A$ over $M$ whose $q$-adic realization
   is $V_{\mathfrak q}(A)$ and whose $\ell$-adic realization is $V_\lambda(A)$; and
6. a parallel-weight-two cuspidal representation $\pi_M$, a place $\lambda_M\mid\ell$, and a
   common coefficient field $C$ satisfying (1.4) with $L=M$.

The field $M$ is obtained from one connected specialization of a geometrically connected
Galois top. More precisely, for some sufficiently large $d\ge5$ there is a totally real
$S_d$-extension
$P/\mathbf Q$, linearly disjoint from $F_0D$, such that

$$
M=PF_0,
\qquad
\operatorname{Gal}(M/\mathbf Q)\simeq S_d\times C_2.
\tag{1.7}
$$

Let $\mathbb T_M^{\min}$ be the faithful Hecke order on the exact minimal definite-quaternionic
module localized at $\bar\rho|_{G_M}$. Then

$$
\boxed{R_M^{\min}\xrightarrow{\ \sim\ }\mathbb T_M^{\min}}.
\tag{1.8}
$$

The definite inner form is ramified at every real place and at two places above $2$ already
belonging to the named tame-dihedral tuple. Switching one of those dyadic invariants with one
real invariant gives the Shimura-curve carrier used to attach the Hecke-valued representation;
no new deformation place is introduced.

Both rings are finite free complete intersections over the final coefficient DVR, the minimal
module is finite free of positive rank and faithful over the common ring, the generic Hecke
algebra is reduced, and every Taylor--Wiles and rigidifying auxiliary level augments exactly to
the displayed minimal objects. The Galois representation over the Hecke order has determinant
$\chi_\ell$, is finite flat on the selected lattice at every $w\mid\ell$, lies on the labeled
tame-quadratic component at every $w\mid2$, and is unramified elsewhere.

For every elementary subgroup $H\le\operatorname{Gal}(M/\mathbf Q)$, the restriction of
$\rho$ to $G_{M^H}$ is likewise automorphic. These packets are compatible with conjugation and
with prime-cyclic base change through $M/M^H$.

### 1.3 Why the construction is genuinely simultaneous

The logical spine is

$$
\begin{array}{c}
\rho\text{ and }\bar\rho\text{ with their exact integral local data}\\
\Downarrow\\
F_0\subset K_0\text{ and a minimal dihedral }q\text{-companion}\\
\Downarrow\\
\text{smooth projective paired-frame incidence curve }Y/F_0\\
\Downarrow\\
\operatorname{Res}_{F_0/\mathbf Q}Y\supset C
\text{ with a simply branched moving pencil}\\
\Downarrow\\
P/\mathbf Q\text{ a closure-disjoint totally real }S_d\text{-top},\quad M=PF_0\\
\Downarrow\\
A/M\text{ good outside }2\text{ with both exact torsion frames}\\
\Downarrow\\
V_{\mathfrak q}(A)\text{ automorphic by an exact minimal }q\text{-adic }R=\mathbb T\\
\Downarrow\\
V_\lambda(A)\text{ is an automorphic point of the exact target minimal tuple}\\
\Downarrow\\
R_M^{\min}=\mathbb T_M^{\min}\text{ and the fixed point }\rho|_{G_M}\text{ is automorphic}.
\end{array}
\tag{1.9}
$$

The penultimate arrow is the new automorphic-incidence theorem. It is stronger than residual
automorphy: it produces a characteristic-zero automorphic carrier already lying on every local
component used by $\rho$. Thus the last arrow is precisely the clean minimal theorem of Book
155 with all its hypotheses verified; it is not an assertion that a module supported on a
special branch somehow acquires support on an unramified branch.

The already automorphic field used inside Book 185 is not transported to $M$. It remains useful
for the construction of (1.1), but the automorphic carrier over $M$ is made by the same global
specialization that makes $M$.

### 1.4 Conventions

Arithmetic Frobenius is used throughout. The cyclotomic character is $\chi_s$ at coefficient
prime $s$. In the covariant weight-two normalization an unramified polynomial is

$$
P_v(X)=X^2-a_vX+q_v.
\tag{1.10}
$$

All intersections are taken in a fixed algebraic closure. A place splits completely only when
the full tensor product is a product of copies of the base completion. Local decomposition and
inertia groups are defined up to simultaneous conjugacy. Representations at different
coefficient primes are compared through algebraic Frobenius polynomials, never by identifying
their coefficient completions.

## 2. The input and avoidance ledgers

### 2.1 The balanced minimal lift

The residual representation

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k)
\tag{2.1}
$$

is absolutely irreducible, odd, has determinant $\bar\chi_\ell$, is unramified outside
$\{2,\ell\}$, has the exact tame-quadratic condition at $2$, and has the selected
coefficient-linear finite-flat model at $\ell$. Book 185 proves

$$
\bar\rho|_{G_{\mathbf Q(\zeta_\ell)}}
\text{ is absolutely irreducible}.
\tag{2.2}
$$

It also proves the adjoint vanishing and scalar-centralizer statements required by the minimal
lifting theorem. The balanced argument selects a horizontal minimal prime and normalizes its
domain quotient. The resulting point is (1.1); no later coefficient enlargement changes its
strict-equivalence class after scalar extension.

### 2.2 The represented local tuple

Write

$$
\mathcal D(\rho)=
\left(
\det=\chi_\ell;
\ \mathcal C_2^{\mathrm{tq}};
\ \mathcal C_\ell^{\mathrm{fl}};
\ \mathcal C_v^{\mathrm{ur}}\ (v\nmid2\ell)
\right).
\tag{2.3}
$$

Here $\mathcal C_2^{\mathrm{tq}}$ is the represented integral component on which a tame
generator obeys $T^2+T+1=0$. The order-three type projector is integral at both coefficient
primes used below because $\ell,q\ge7$. The condition $\mathcal C_\ell^{\mathrm{fl}}$ is the
clean low-weight finite-flat functor of the selected lattice, including its coefficient action,
pairing, and any connected--étale or local--local label. At every other place the quotient is
the actual unramified functor, not the zero-monodromy locus inside a special functor.

The modularity-admissible record of Book 185 contains local PEL realizations of these
coefficient-prime and dyadic data. Section 4.5 places those realizations on one split PEL frame
twist, and Section 4.6 cuts a projective curve through all their local tubes without changing
the represented local rings.

### 2.3 The finite avoidance field

Fix one finite Galois extension $D/\mathbf Q$ containing:

- the fixed field of $\ker\bar\rho$;
- the joint residual--cyclotomic field used to test (2.2) and the adjoint invariant;
- every finite self-twist and centralizer-detection field;
- the component, orientation, and descent fields named by the original local ledger; and
- every finite field already required by the integral type and coefficient carriers.

Later we enlarge the field used in the Hilbert condition to

$$
D^+=DK_0D_{\bar\sigma}D_{\mathrm{PEL}},
\tag{2.4}
$$

where the three added fields are respectively the CM companion field, the finite image field of
$\bar\sigma\oplus\bar\chi_q$ together with its adjoint-detection modules, and the finite
component and level fields of the split PEL frame space. This
enlargement occurs before the top field is selected. It does not alter the target condition
$M\cap D=\mathbf Q$.

All named objects are finite in number. No infinite avoidance condition is hidden in (2.4).

### 2.4 The obstruction that must be removed geometrically

Suppose an auxiliary abelian variety has a semistable prime $w\nmid2\ell$ and its
$\ell$-torsion is unramified. Its characteristic-zero Tate factor can still be special, with
monodromy divisible by $\varpi$. The closed special condition meets the unramified trace line
only on

$$
T_w^2-(q_w+1)^2=0.
\tag{2.5}
$$

The chosen point $\rho|_{G_{M_w}}$ is not required to satisfy (2.5). Moreover the monodromy
lattice

$$
0\longrightarrow X_w\xrightarrow{q_\Gamma}X_w^\vee
\longrightarrow\Phi_w\longrightarrow0
\tag{2.6}
$$

can have $\Phi_w[\varpi]\ne0$. Thus neither residual unramifiedness nor saturated Ihara
injectivity alone lowers the source. These valid local facts explain why the source must be
made good before the target patch is formed.

The projective carrier of Chapter 4 does exactly that. It has a proper arithmetic model lying
inside the abelian-scheme locus away from a fixed finite set. At every odd place in that set we
impose a good-reduction residue tube. Therefore the specialized abelian variety has no place
$w\nmid2$ at which (2.5) or (2.6) enters. The dyadic factor is already the same
finite-monodromy component as the chosen point, with $N=0$ on both sides.

## 3. A minimal dihedral companion over a harmless real base

The usual auxiliary dihedral construction introduces a signed Steinberg place in order to
obtain a convenient definite-quaternionic localization over a point field of uncontrolled
degree. That place would be superfluous level at the target coefficient prime. Here the final
top has even degree and $2$ splits completely. Two of its already prescribed dyadic
supercuspidal factors can therefore supply the finite ramification needed for the integral
definite-to-curve comparison, without adding any local condition. We can start with a
genuinely minimal dihedral companion.

### 3.1 An everywhere-unramified CM quadratic extension

**Lemma 3.1 (harmless CM base).** Let $D/\mathbf Q$ be finite Galois and let $S_0$ be a finite
set of rational primes containing $2$ and $\ell$. There are distinct primes $a,b>3$ with
$a,b\equiv3\pmod8$
such that, with

$$
F_0=\mathbf Q(\sqrt{ab}),
\qquad
K_0=\mathbf Q(\sqrt{-a},\sqrt{-b}),
\tag{3.1}
$$

the following hold:

1. every prime in $S_0$ splits in $F_0$;
2. $K_0\cap D=\mathbf Q$;
3. $K_0/F_0$ is CM quadratic and unramified at every finite place; and
4. at each place $u\mid2$ of $F_0$, the extension $(K_0)_u/(F_0)_u=\mathbf Q_2$ is the
   unramified quadratic extension.

**Proof.** Choose $a$ and $b$ outside $S_0$ and outside the primes ramified in $D$, by
Dirichlet and the Chinese remainder theorem. Besides $a,b\equiv3\pmod8$, prescribe their
quadratic residue symbols so that $(ab/p)=1$ for every odd $p\in S_0$. The same choice can be
made successively: after $a$ is fixed, the conditions on $b$ are congruence
conditions modulo $8a\ell\prod_{p\in S_0}p$.

The three quadratic subfields of $K_0$ have fundamental discriminants

$$
-a,\qquad -b,\qquad ab.
\tag{3.2}
$$

The discriminant formula for a biquadratic field gives

$$
\operatorname{disc}(K_0)=(-a)(-b)(ab)=a^2b^2
=\operatorname{disc}(F_0)^2.
\tag{3.3}
$$

The relative discriminant formula therefore gives
$N_{F_0/\mathbf Q}(\mathfrak d_{K_0/F_0})=1$, proving finite unramifiedness. Both imaginary
quadratic subfields are exchanged by complex conjugation, whose fixed field is $F_0$, so the
extension is CM.

Since $ab\equiv1\pmod8$, $2$ splits in $F_0$. At either dyadic completion, adjoining
$\sqrt{-a}$ adjoins the square class $5\pmod8$, hence gives the unramified quadratic
extension of $\mathbf Q_2$. Finally, any nontrivial intersection $K_0\cap D$ contains one of
the three quadratic subfields in (3.2). Each is ramified at $a$ or $b$, while $D$ is not, a
contradiction. $\square$

The construction also permits finitely many later splitting requirements on $F_0$: they are
placed in $S_0$ before $a,b$ are selected. All auxiliary level primes chosen afterward will be
chosen split in $F_0$.

We record one elementary consequence used in the character construction. The field $F_0$ has
no unit of norm $-1$. Indeed, such a unit would give

$$
x^2-aby^2=-4
$$

with $x,y\in\mathbf Z$ of the same parity. Reduction modulo $a$ would make $-1$ a quadratic
residue modulo $a$, contrary to $a\equiv3\pmod4$.

### 3.2 The auxiliary coefficient prime

Let $c$ be the nontrivial element of $\operatorname{Gal}(K_0/F_0)$. Chebotarev and the
finite exclusions in Books 72, 95, 155, 162, and 174 give a prime $q\ge7$, $q\ne\ell$, such
that:

1. $q$ splits completely in $F_0$ and its primes are inert in $K_0/F_0$;
2. $q$ is outside the discriminants and coefficient denominators already named;
3. the niveau-two finite-flat local representation below is cyclotomically irreducible and
   has scalar centralizer;
4. the adjoint detection and coefficient-separation exclusions needed in the auxiliary
   Taylor--Wiles problem hold.

Only finitely many conjugacy classes or residue conditions are excluded. The first condition
asks rational Frobenius in the biquadratic extension $K_0/\mathbf Q$ to equal $c$; the
remaining conditions are imposed in its compositum with finitely many detection fields. The
finite-Galois prime-selection theorem of Books 6 and 167 supplies infinitely many such primes.
No equality between a $q$-Frobenius matrix of $\bar\rho$ and an independently chosen PEL
matrix is imposed here. The local alignment in Section 4.5 is instead achieved by a finite
unramified extension, which is harmless for both clean coefficient-prime deformation theories.

### 3.3 The algebraic Hecke character

**Lemma 3.2 (minimal polarized companion character).** There is an algebraic Hecke character
$\Theta_0$ of $K_0$ whose finite conductor is the product of the dyadic primes and such that:

1. its infinity type is $(1,0)$ at one embedding in each CM pair;
2. $\Theta_0\Theta_0^c$ has the cyclotomic norm required by the chosen polarization;
3. the determinant of $\operatorname{Ind}_{G_{K_0}}^{G_{F_0}}\Theta_{0,q}$ is $\chi_q$;
4. at every $u\mid2$, its finite local character on the residue group
   $\mathbf F_4^\times$ has order three and is sent to its inverse by $c$;
5. it is unramified at every odd finite place; and
6. its $q$-adic avatar at $u\mid q$ is crystalline of weights $0$ and $1$ after induction
   from the unramified quadratic completion.

**Proof.** Since $a,b>3$, the roots of unity in $K_0$ are $\{\pm1\}$. The CM unit theorem says

$$
\left[
\mathcal O_{K_0}^{\times}:
\{\pm1\}\mathcal O_{F_0}^{\times}
\right]\le2.
\tag{3.3a}
$$

For a CM type $\Phi$, put
$\lambda_\Phi(u)=\prod_{\tau\in\Phi}\tau(u)$. This is $1$ on $-1$, because
$|\Phi|=2$, and on $\mathcal O_{F_0}^{\times}$ it is the norm to $\mathbf Q$, which is $1$
by the observation after Lemma 3.1. If the quotient in (3.3a) has order two, choose a
representative $u$. Then $u/u^c=-1$ and $\lambda_\Phi(u)=\pm1$. Replacing one member of
$\Phi$ by its conjugate changes that sign. We therefore choose $\Phi$ so that

$$
\lambda_\Phi|_{\mathcal O_{K_0}^{\times}}=1.
\tag{3.3b}
$$

There are two dyadic primes of $K_0$, each with residue field $\mathbf F_4$. At each choose a
nontrivial character of $\mathbf F_4^\times$, with the conjugate character its inverse. Their
product is trivial on every global unit. For units from $F_0$ this follows from
$\mathbf F_2^\times=1$. On the possible second unit coset in (3.3a), its square is in
$\{\pm1\}\mathcal O_{F_0}^{\times}$; the product of the two local values consequently has
order dividing both $2$ and $3$, and is $1$. Together with (3.3b), this proves the full
ray-unit compatibility without introducing a wild dyadic character.

Let $\mathfrak m$ be the product, to exponent one, of the two dyadic primes. The ray sequence

$$
\mathcal O_{K_0}^{\times}\longrightarrow
(\mathcal O_{K_0}/\mathfrak m)^{\times}\longrightarrow
\operatorname{Cl}_{\mathfrak m}(K_0)\longrightarrow
\operatorname{Cl}(K_0)\longrightarrow1
$$

is the finite group in which the extension problem lives. Impose simultaneously, on the image
of the diagonally embedded idèle class group $C_{F_0}$, the central rule

$$
\Theta_0|_{C_{F_0}}
=\eta_{K_0/F_0}|\cdot|^{-1},
\tag{3.3c}
$$

where arithmetic $|\cdot|^{-1}$ has $q$-adic avatar $\chi_q$. The order-three unit characters
restrict trivially to every $F_{0,u}^{\times}$ at $u\mid2$; their unramified uniformizer values
are free and are chosen to satisfy (3.3c). At the odd places the same rule only chooses
unramified values and therefore creates no conductor.

We check the possible capitulation intersection rather than assume it away. If an extended
$F_0$-ideal becomes principal, say
$\mathfrak a\mathcal O_{K_0}=(\alpha)$, then
$\alpha^c/\alpha$ is a global unit. The principal/infinity rule and the central rule differ on
this relation by the value on that unit and by the restrictions of the dyadic unit characters.
Both are $1$ by (3.3b) and the preceding paragraph. Finite unramifiedness supplies no local
different or ramified-uniformizer correction. Hence the two rules define one character on the
subgroup of the ray group generated by principal data, dyadic units, and extended $F_0$-ideals.
The quotient by this subgroup is finite, and $\mathbf C^\times$ is divisible, so the character
extends to the full ray group. This is the subgroup-extension argument of Book 95 with its
determinant compatibility checked; no auxiliary conductor place is needed because the dyadic
characters are already conjugate-regular.

The induction determinant formula and (3.3c) give
$\det\operatorname{Ind}\Theta_{0,q}=\chi_q$. Restricting this identity to $G_{K_0}$ gives,
in the arithmetic Galois normalization,

$$
\Theta_0\Theta_0^c=\chi_q|_{G_{K_0}}.
\tag{3.3d}
$$

The finite conductor is exactly $\mathfrak m$: its two tame residue characters are nontrivial,
while no higher-unit or odd-prime character was used. On complex conjugation the permutation
sign in the induction determinant is the quadratic factor in (3.3c), so both sides have value
$-1$; there is no missing quadratic twist.
The order-three characters at $2$ are unequal to their conjugates, so
$\Theta_0\ne\Theta_0^c$ without an auxiliary ramified witness.

At $q$, the extension is unramified quadratic. The $q$-adic avatar of a type-$(1,0)$ algebraic
character is crystalline with one labeled Hodge--Tate weight at each of the two embeddings.
Induction therefore has weights $\{0,1\}$ and admits the polarized height-two finite-flat
lattice. These are the unramified local-local objects of Books 59, 60, 95, and 174. $\square$

Put

$$
\sigma_q=\operatorname{Ind}_{G_{K_0}}^{G_{F_0}}\Theta_{0,q},
\qquad
\bar\sigma=\sigma_q\bmod\mathfrak m_q.
\tag{3.4}
$$

Here $E_{\mathrm{aux}}/\mathbf Q_q$ is a finite field containing the values of $\sigma_q$ and
the auxiliary type coordinates, $\mathcal O_{\mathrm{aux}}$ is its ring of integers,
$\mathfrak m_q$ its maximal ideal, and $k_q$ its residue field. Enlarge it once so that the
polarized induced lattice and both order-three type lines are defined.

The local character is fixed before the PEL seeds are chosen. Section 4.5 realizes its exact
restriction, including the pairing, after a controlled unramified base change; it does not
replace equality of framed modules by equality of determinants.

### 3.4 The exact local profile of the companion

**Proposition 3.3.** The representation $\bar\sigma$ is absolutely irreducible and remains
absolutely irreducible over $F_0(\zeta_q)$. It is totally odd, has determinant
$\bar\chi_q$, is finite flat of weights $\{0,1\}$ at $q$, has the order-three tame-dihedral
type at every place above $2$, and is unramified at every other finite place. Its
characteristic-zero lift $\sigma_q$ has the same profile. Moreover,

$$
H^0\!\left(F_0,\operatorname{ad}^0\bar\sigma(1)\right)=0.
\tag{3.5}
$$

**Proof.** At a place above $q$, the residual ratio of the two induced crystalline characters
is a niveau-two fundamental character of order divisible by $q+1$. Restriction to the
cyclotomic field kills a quotient of order dividing $q-1$ and cannot make that ratio trivial
for $q\ge7$. Mackey's criterion proves both irreducibility assertions. Complex conjugation
interchanges the two CM-type lines, so its eigenvalues are $1$ and $-1$.

The determinant and finite-flat assertions are Lemma 3.2. At $2$, induction from the unramified
quadratic extension of $\mathbf Q_2$ sends a tame generator to eigenvalues $\zeta_3$ and
$\zeta_3^{-1}$, hence its matrix obeys $T^2+T+1=0$. At an odd place different from $q$,
$K_0/F_0$ and $\Theta_0$ are both unramified, so their induction is unramified.

For the last assertion, write $\epsilon_{K_0/F_0}$ for the quadratic character and
$\psi=\bar\Theta_0/\bar\Theta_0^c$. The dihedral adjoint decomposition is

$$
\operatorname{ad}^0\bar\sigma
\simeq\epsilon_{K_0/F_0}\oplus
\operatorname{Ind}_{G_{K_0}}^{G_{F_0}}\psi.
$$

At $q$, the first summand is unramified while $\bar\chi_q$ is nontrivial on inertia. On the
second summand, $\psi$ has niveau-two inertial order divisible by $q+1$, whereas a cyclotomic
character has niveau one and order dividing $q-1$. Neither summand acquires an invariant after
the Tate twist, proving (3.5). $\square$

This proposition is the first decisive difference from the ordinary two-prime seed. There is
no signed Steinberg place and no auxiliary finite inertial type which disappears modulo
$\ell$. The companion and the target can therefore occur on one compatible system that is
minimal away from $2$ at both coefficient primes.

## 4. The projective automorphic-incidence space

The second decisive change is geometric. The Hilbert--Blumenthal realization space used in
ordinary two-prime potential modularity is quasi-projective, so a specialized point can meet a
new boundary divisor at a prime not named in advance. We do not replace it by a division-
quaternion PEL space: such a fine PEL problem has no suitable real points. Indeed, on a real
point complex conjugation would commute with the global division endomorphism algebra; in its
division commutant an involution is $\pm1$, contradicting the required one-dimensional $+1$
and $-1$ eigenspaces.

Instead we use a split matrix PEL realization of a high-dimensional Hilbert modular variety.
Its minimal compactification has only finitely many cusps. After the two frame twists and all
local seeds have been fixed, we cut a smooth projective curve in the normalization of that
compactification, avoiding every cusp. The universal abelian scheme therefore lives on the
whole curve. This keeps the real Hilbert--Blumenthal seeds and makes properness available at
all unnamed primes.

### 4.1 The split rank-two PEL datum

Retain the auxiliary coefficient field just fixed and put

$$
E_\lambda^{\mathrm{ur}}=W(k)[1/\ell],
\qquad
E_{\mathfrak q}^{\mathrm{ur}}=W(k_q)[1/q].
\tag{4.0}
$$

The possibly ramified fields $E$ and $E_{\mathrm{aux}}$ enter later only by scalar extension.
Choose a totally real field $R$ of degree $g\ge3$ and primes

$$
\lambda\mid\ell,
\qquad
\mathfrak q\mid q
\tag{4.1}
$$

with

$$
R_\lambda\simeq E_\lambda^{\mathrm{ur}},
\qquad
R_{\mathfrak q}\simeq E_{\mathfrak q}^{\mathrm{ur}}.
\tag{4.2}
$$

Polynomial approximation supplies $R$: prescribe $g$ real roots, the two selected unramified
factors, unramified remaining factors at $\ell$ and $q$, complete splitting at $2$, and good
self-dual factors at every previously named prime. At one fresh prime impose an Eisenstein
coefficient box. Weak approximation in the monic coefficient space meets that box, the open
real-root box, and all the Krasner neighborhoods just listed. The resulting polynomial is
irreducible and totally real with the exact completions (4.2). Increasing $g$ leaves those
factors unchanged and provides the codimension needed below.

Put $B_0=M_2(R)$ and define the common-determinant group

$$
G(S)=\left\{
b\in(B_0\otimes_{\mathbf Q}S)^\times:
\det_R(b)\in S^\times
\right\},
\tag{4.3}
$$

where the determinant is required to be the diagonal scalar in $R\otimes_{\mathbf Q}S$. Then

$$
1\longrightarrow
\operatorname{Res}_{R/\mathbf Q}\operatorname{SL}_2
\longrightarrow G\xrightarrow{\nu}\mathbf G_m
\longrightarrow1.
\tag{4.3a}
$$

Choose a totally negative $d\in R^\times$ and, in split coordinates, a pure invertible matrix
$\delta$ with $\delta^2=d$. On $V=B_0$ set

$$
\psi_\delta(x,y)=
\operatorname{Tr}_{R/\mathbf Q}
\operatorname{Tr}_{B_0/R}(x\delta\bar y).
\tag{4.3b}
$$

Here $\bar y$ is the adjugate involution. The trace calculation of Book 123 makes this form
alternating and gives

$$
\psi_\delta(bx,by)=\nu(b)\psi_\delta(x,y).
\tag{4.3c}
$$

Choose a fractional right $M_2(\mathcal O_R)$-lattice $\Lambda\subset V$ dual to itself for
$\psi_\delta$ at $2,\ell,q$ and every previously named good place. Locally this is obtained by
putting the inverse different in one column and its polarization dual in the other; the local
lattices patch because fractional $R$-ideals form the required genus. Put the finite failure of
self-duality into $\Sigma_{\mathrm{PEL}}$. Thus every later hyperspecial or polarization claim
refers to a fixed integral lattice, not only to the rational representation.

Choose the split coordinates at each real embedding so that
$\delta/\sqrt{-d}$ is the standard complex structure. The parallel Hodge map then has matrix
$\left(\begin{smallmatrix}a&b\\-b&a\end{smallmatrix}\right)$ at every embedding; its
determinants are all $a^2+b^2$, so it lands in $G(\mathbf R)$ and polarizes (4.3b). The reflex
field is $\mathbf Q$. Right multiplication by $M_2(R)^{\mathrm{op}}$ is the full commutant,
and double centralizer shows that its polarized similitude group is exactly $G$. Thus

$$
G\longrightarrow\operatorname{GSp}(V,\psi_\delta)
\tag{4.4}
$$

is PEL-exact. Primitive Morita idempotents at $\lambda$ and $\mathfrak q$ cut out

$$
e_\lambda V_\ell\text{ of rank }2\text{ over }\mathcal O_{R,\lambda},
\qquad
e_{\mathfrak q}V_q\text{ of rank }2\text{ over }\mathcal O_{R,\mathfrak q}.
\tag{4.4a}
$$

On either column module the determinant is $\nu$. Hence the two universal Tate factors will
have cyclotomic determinant. Because $B_0$ is a matrix algebra, this datum is Morita equivalent
to the Hilbert--Blumenthal datum at every place, including the real places; the real-locus
obstruction for a division commutant is absent.

### 4.2 Fine moduli and the finite cusp boundary

Choose an auxiliary prime $r\nmid2\ell q$ split completely in both $F_0$ and $R$ and outside
the avoidance and integral ledgers. At $r$ impose a center-detecting
one-sided rigidification: in split coordinates its stabilizer reduces to
$\operatorname{diag}(1,\nu)$ on the marked column. Together with the compatible dyadic chart
and hyperspecial level at the two coefficient primes, this gives a fine level $U$. Its
arithmetic stabilizers are neat, its derived part is sufficiently deep, and its multiplier
remains full:

$$
\nu(U)=\widehat{\mathbf Z}^{\times}.
\tag{4.4b}
$$

These requirements are compatible. In a rank-two totally real arithmetic stabilizer the
nontrivial root-of-unity eigenvalues have orders $2,3,4$, or $6$. Choose $r>3$ away from their
cyclotomic differences. A stabilizer of the marked column has an eigenvalue congruent to $1$
at $r$, so finite order forces that eigenvalue, and then its polarized companion, to be $1$;
the center-detecting mark eliminates the remaining scalar. On the other hand
$\operatorname{diag}(1,u)$ supplies every local multiplier $u\in\mathbf Z_r^\times$.
Thus fine representability is obtained without shrinking the adelic multiplier quotient used
below. This is the one-sided level alternative of Book 169, not a constant real full frame.

The fine PEL functor classifies

$$
(A,\iota,\Lambda,\eta_U).
\tag{4.5}
$$

The matrix action, determinant law, ordered polarization line, and neat level give a smooth
quasi-projective scheme $Z/\mathbf Q$ with a universal abelian scheme $\mathcal A_Z$. Morita
deformation theory gives the local model

$$
(\mathbf P^1)^g,
\tag{4.6}
$$

so $Z$ is smooth of dimension $g$. The component calculation is exact. Determinant is
surjective at every finite place and on rational points; preserving the parallel upper-half-
plane component cuts the rational image to $\mathbf Q_{>0}^\times$. Strong approximation for
$\operatorname{Res}_{R/\mathbf Q}\operatorname{SL}_2$ and (4.4b) therefore give

$$
\pi_0(Z(\mathbf C))\simeq
\mathbf Q_{>0}^{\times}\backslash
\mathbf A_{\mathbf Q,f}^{\times}/
\widehat{\mathbf Z}^{\times}=1.
\tag{4.6a}
$$

Thus $Z$ is geometrically connected and the selected component is already defined over
$\mathbf Q$.

We need a precise compactification fact, not the false assertion that $Z$ itself is proper.

**Lemma 4.1 (minimal compactification with finite boundary).** The scheme $Z$ has a normal
projective compactification $Z^{\min}/\mathbf Q$ such that

$$
Z^{\min}\setminus Z\text{ is a finite reduced set of cusp points.}
\tag{4.7}
$$

There is also a finite set $\Sigma_{\mathrm{PEL}}$, containing
$2,\ell,q,r$ and all discriminant, polarization, and level primes, over whose complement this
is the generic fiber of a projective normal integral model
$\mathscr Z^{\min}$; its open $\mathscr Z$ carries the universal abelian scheme and
$\mathscr Z^{\min}\setminus\mathscr Z$ is finite over the base.

**Proof.** The rational cusps are the double quotient of the Borel parabolics by
$G(\mathbf Q)$ and $U$. Reduction of a cusp to a fractional $R$-ideal and its level class
maps this set into a finite narrow ray-class quotient, with finite fibers. Hence there are
finitely many cusps. Choose, at each one, a rational polyhedral fan modulo its totally positive
unit stabilizer and form the toroidal PEL compactification. Its boundary charts are quotients
of torus embeddings for the unipotent radical of a Borel of
$\operatorname{Res}_{R/\mathbf Q}\operatorname{GL}_2$.

Let $\omega$ be the parallel Hodge line. Koecher's principle holds because $g\ge2$: a
parallel form on $Z$ has no negative Fourier exponent and extends across every toroidal chart.
We record the finite-generation calculation. A finite reduction domain for the totally
positive units meets only finitely many cones. The dual integral monoid of each rational
polyhedral cone is finitely generated by Gordan's lemma. After replacing the weight by one
divisible integer $N$, cusp stabilizers act trivially on the constant term and the generators
on overlaps agree. Serre vanishing on the projective toroidal compactification lifts these
finite boundary generators to global sections. Their cokernel is supported on a union of
lower-dimensional toric strata; induction on the strata, followed by the same argument on the
compact interior complement, gives finite generation of the Veronese algebra

$$
\mathcal R_N=\bigoplus_{m\ge0}H^0(Z,\omega^{\otimes mN}).
\tag{4.7a}
$$

The same calculation separates interior points and tangent directions. On a boundary chart,
all positive Fourier monomials vanish on the closed toric orbit and the constant term is
constant along the connected boundary fiber. Thus the morphism defined by $\mathcal R_N$ is
finite on $Z$ and contracts exactly the toroidal boundary over each rational parabolic to one
point. Set

$$
Z^{\min}=\operatorname{Norm}\operatorname{Proj}(\mathcal R_N).
\tag{4.7b}
$$

The preceding local calculation proves both projectivity and (4.7); it does not assume an
ambient compact PEL datum.

The construction commutes with the component descent in (4.6a), so it is defined over
$\mathbf Q$. Away from the displayed finite set, the same toroidal charts are defined over the
unramified PEL base, the Fourier exponents form constant saturated monoids, and the parallel
Hodge line and its contraction extend. Normalizing the resulting projective model gives
$\mathscr Z^{\min}$; the finitely many rational parabolic classes give a boundary finite over
the base. The universal semiabelian scheme is abelian precisely on $\mathscr Z$. $\square$

The codimension of the boundary is $g\ge3$. This, rather than compactness of the ambient PEL
problem, is what will let a projective carrier avoid degeneration.

### 4.3 The paired-frame twist

Base change $Z$ to $F_0$. The Morita idempotents give rank-two finite étale generic-fiber
groups

$$
\mathcal A_Z[\lambda],
\qquad
\mathcal A_Z[\mathfrak q].
\tag{4.8}
$$

Here and below $A[\lambda]$ and $A[\mathfrak q]$ mean the corresponding primitive Morita
columns $e_\lambda A[\lambda]$ and $e_{\mathfrak q}A[\mathfrak q]$, not the full
matrix-multiplicity kernels; the same convention applies to $V_\lambda(A)$ and
$V_{\mathfrak q}(A)$.

Let $X/F_0$ classify (4.5) together with pairing-preserving frames

$$
\alpha:\bar\rho|_{G_{F_0}}\xrightarrow{\sim}A[\lambda],
\qquad
\beta:\bar\sigma\xrightarrow{\sim}A[\mathfrak q].
\tag{4.9}
$$

This is the descent of the fixed-pairing full-level cover by the product frame cocycle. It is
finite étale over $Z_{F_0}$, smooth and quasi-projective, and it carries the pulled-back
universal abelian scheme

$$
\mathcal A_X\longrightarrow X.
\tag{4.10}
$$

The determinant identities

$$
\bigwedge^2\bar\rho=\bar\chi_\ell,
\qquad
\bigwedge^2\bar\sigma=\bar\chi_q
\tag{4.11}
$$

put both descent cocycles in the pairing-preserving deck groups. Without these pairing
coordinates the twist would permute multiplier components.

### 4.4 Geometric connectedness and product monodromy

The geometric deck group is

$$
\Delta=\operatorname{SL}_2(k)\times\operatorname{SL}_2(k_q).
\tag{4.12}
$$

**Proposition 4.2 (full product monodromy).** The geometric monodromy of $X\to Z_{F_0}$ is
all of $\Delta$. Consequently $X$ is geometrically connected.

**Proof.** Strong approximation for the simply connected derived group in (4.3a), with the
fixed away-level included, makes reduction surjective at $\lambda$ and $\mathfrak q$. A proper
subgroup surjective to both factors would, by Goursat's lemma, produce a common nontrivial
simple quotient. For residue characteristics at least seven the only such quotients are the
corresponding $\operatorname{PSL}_2$ groups, which have different defining characteristics and
are not isomorphic. The monodromy is therefore the product. Twisting changes only arithmetic
descent, so geometric connectedness is unchanged. $\square$

Let $X^{\min}$ be the normalization of $Z^{\min}_{F_0}$ in $F_0(X)$. It is normal and
projective, finite over $Z^{\min}_{F_0}$, and
$X^{\min}\setminus X$ is finite. This normalization is taken only after Proposition 4.2 has
proved that $F_0(X)$ is a field.

Enlarge $\Sigma_{\mathrm{PEL}}$ once, before any specialization, so that the twist and its
frames spread to a finite étale cover $\mathscr X\to\mathscr Z_{\mathcal O_{F_0}}$ away from
that set. Normalize $\mathscr Z^{\min}_{\mathcal O_{F_0}}$ in $F_0(X)$ and call the result
$\mathscr X^{\min}$. It is projective over
$\mathcal O_{F_0}[1/\Sigma_{\mathrm{PEL}}]$, its open $\mathscr X$ carries
$\mathcal A_X$, and

$$
\mathscr B=\mathscr X^{\min}\setminus\mathscr X
\tag{4.12a}
$$

is finite over that fixed base. Every prime excluded here is put into the local set in the next
section. The separate finite set at which the later curve closure meets this boundary is handled
by the vertical-repair argument of Section 4.6 before any top specialization.

### 4.5 Local seeds on the exact components

Let $S$ contain both real places of $F_0$, all places above $S_0\cup\{q\}$, every
place above $\Sigma_{\mathrm{PEL}}$, and every place in the finite local realization ledger.
For each finite $u\in S$ we construct

$$
U_u/F_{0,u}
\tag{4.13}
$$

and one point $x_u\in X(U_u)$. The extension is unramified at $2,\ell,q$ and at the original
places of $S_0$; a later level place may use a recorded ramified extension.

**Local frame-alignment lemma.** If $p$ is odd, $s\ne p$, and two paired rank-two
$k_s$-representations of $G_{\mathbf Q_p}$ are unramified with the same multiplier, they
become isomorphic after a finite unramified extension. At $p=2$, two representations with the
labeled order-three inertia pair and cyclotomic determinant are paired-isomorphic after a
coefficient extension alone.

For the first assertion, take an unramified degree divisible by the orders of both Frobenius
matrices. For the second, diagonalize tame inertia. Frobenius exchanges its two eigenlines and
has matrix

$$
\begin{pmatrix}0&a\\b&0\end{pmatrix},
\qquad -ab=2.
\tag{4.13a}
$$

A diagonal basis change aligns two such matrices, and one coefficient square root makes the
change pairing-preserving. No extension of $\mathbf Q_2$ occurs.

**Matrix Morita lemma.** The split PEL category is equivalent at every place to the
Hilbert--Blumenthal category used in Books 169, 170, 174, and 185. Under

$$
M_2(\mathcal O_R)\otimes\mathbf Z_p
\simeq M_2(\mathcal O_R\otimes\mathbf Z_p),
\tag{4.13b}
$$

a primitive idempotent and inverse column tensor preserve polarizations, determinant laws,
abelian schemes, finite locally free kernels, and the selected rank-two factors. Thus the
actual local comparison objects in the modularity-admissible datum, not abstract finite-flat
representations, give local points on $Z$ and hence on the twist after frame alignment.

Here is the local algebraization step. At a residue-characteristic place, the
modularity-admissible record supplies a polarized height-two PEL comparison
Barsotti--Tate object whose scalar extension belongs to the selected coefficient-linear
finite-flat functor. Put that comparison object in the chosen Morita column and put the
standard ordinary polarized object in every other $R$-factor. Grothendieck--Messing deformation
amounts to lifting one isotropic Hodge line for each embedding, so its completed deformation
space is the product (4.6) and has no obstruction. The formal PEL object algebraizes on the
fine moduli scheme. Smoothness then permits an unramified residue extension and a
characteristic-zero point. After the declared common coefficient extension, its compatible
finite-flat quotients lie in the same represented functor as the chosen lattice. This proves
existence of the required local seed; it is not an inference from a generic Galois module or
an identification of two unequal coefficient DVRs.

At $u\mid\ell$, use the named finite locally free comparison object on
$\mathcal C_\ell^{\mathrm{fl}}$ and align the unramified $\mathfrak q$-frame. Its residue tube
keeps the same represented finite-flat functor, pairing, and connected--étale or local--local
label. At $u\mid q$, use the crystalline induced comparison object of Proposition 3.3 and
align the unramified $\lambda$-frame. Restriction over an even unramified degree may make the
local induction ordinary, but it remains the restriction of the same clean component.

At $u\mid2$, use the common tame-dihedral Hilbert--Blumenthal seed. The two applications of
(4.13a), together with a compatible one-sided rigidification, require no ground-field
extension, so

$$
U_u=\mathbf Q_2.
\tag{4.13c}
$$

Both prime-to-$2$ factors retain the primitive order-three type lattice and $N=0$.

At an odd hyperspecial place, lift a smooth special-fiber point over a finite residue extension
and trivialize both residual frames after a further unramified extension. At a remaining bad
level or discriminant place, use a CM point of the split PEL variety. A CM abelian variety has
potentially good reduction; after a finite extension it has good reduction, the prescribed
level, and the two now-trivial residual frames. Record the Galois closure of that extension.
Thus no division-algebra argument is being used to claim potential good reduction for an
arbitrary Hilbert--Blumenthal point.

At a real place the seed can be seen directly. For two polarization-dual real fractional
ideals $I,J\subset R$, the complex torus

$$
(R\otimes_{\mathbf Q}\mathbf C)/(I+iJ)
\tag{4.13d}
$$

with coordinatewise complex conjugation, its trace polarization, and the determinant action of
$\mathcal O_R$ is a Hilbert--Blumenthal abelian variety over $\mathbf R$. Matrix Morita gives
the required $M_2(\mathcal O_R)$-object. On every primitive torsion column, conjugation has one
$+1$ and one $-1$ line and reverses the alternating pairing. The compatible real descent orbit
of the one-sided auxiliary level was fixed in (4.4b). Total oddness therefore identifies both
residual frames with these two lines, while the ordered trace polarization fixes their
orientation. This produces an actual real point; oddness by itself, without (4.13d) and the
level descent orbit, would not do so.

Around each full local Galois orbit choose a stable open $\Omega_u^X\subset X(U_u)$. At the
coefficient primes these are integral finite-flat residue tubes, at $2$ finite-inertia type
tubes, and elsewhere good-reduction tubes. Every conjunction is witnessed by one local PEL
object. All odd tubes, including those at $\ell$ and $q$, are shrunk inside the
good-reduction locus of that object.

### 4.6 The projective interior carrier

**Lemma 4.3 (projective curve through all local tubes).** There is a smooth projective
geometrically connected curve

$$
Y\hookrightarrow X
\tag{4.14}
$$

such that $Y(U_u)\cap\Omega_u^X$ contains a nonempty stable open for every $u\in S$, including
the real places.

**Proof.** Choose a very ample line bundle on $X^{\min}$. For every finite $u$, move $x_u$
slightly so that its conjugates are distinct. In the coefficient space of $g-1$ sufficiently
positive hyperplanes, require successive incidence with moving points near that orbit and
independent differentials there. The incidence projection is a submersion, so these conditions
give nonempty $F_{0,u}$-adic opens; the same holds over $\mathbf R$.

The boundary $X^{\min}\setminus X$ is finite, and the singular locus of the normal
$X^{\min}$ has codimension at least two. Avoiding both is an open condition on the complete-
intersection coefficients. Bertini gives a Zariski-open set on which the intersection is a
smooth geometrically connected curve. Weak approximation on the common coefficient space
meets all local incidence boxes and that Zariski open. The resulting curve misses the boundary,
so it lies wholly in $X$, not merely generically in it. The implicit function theorem leaves a
stable local open on the curve inside every $\Omega_u^X$. $\square$

Let $\mathcal A/Y$ be the restriction of (4.10), with the frames (4.9). Take the flat
schematic closure of $Y$ in $\mathscr X^{\min}$ after spreading its equations, and normalize
it. Outside a finite set $\Sigma_Y$ this is a proper model contained in $\mathscr X$ and hence
carries $\mathcal A$ as an abelian scheme. The set $\Sigma_Y$ is now known, before the moving
top of Chapter 5 is constructed.

At a newly occurring odd place $u\in\Sigma_Y\setminus S$, local good points still exist. Over
$\mathcal O_{F_{0,u}}$, the flat closure has one-dimensional special fiber, whereas the cusp
boundary is finite. Choose a closed special-fiber point outside the boundary. Intersect the
arithmetic surface through that point with a horizontal curve and normalize it. The resulting
DVR dominates a finite extension $U_u/F_{0,u}$ and gives a point of $Y(U_u)$ whose integral
specialization stays in $\mathscr X$. Pullback of the universal abelian scheme therefore has
good reduction. Passing to a Galois closure and shrinking gives a stable good-reduction tube.
Add these finitely many places and tubes to $S$. This vertical-repair step controls a finite set
discovered from $Y$; it does not recut $Y$ or impose an infinite local condition.

Now set $W=\operatorname{Res}_{F_0/\mathbf Q}Y$. For each controlled rational place $v$ choose
a finite Galois extension $E_v/\mathbf Q_v$ containing the images and Galois closures of all
$U_u/F_{0,u}$ for $u\mid v$, and put $n_v=[E_v:\mathbf Q_v]$. Base change of the local curve
points gives

$$
z_v\in W(E_v)=Y(F_0\otimes_{\mathbf Q}E_v).
\tag{4.14a}
$$

At $v\in S_0\cup\{q\}$ choose $E_v$ unramified. Equation (4.13c) gives

$$
E_2=\mathbf Q_2,
\qquad n_2=1.
\tag{4.14b}
$$

Choose a $\operatorname{Gal}(E_v/\mathbf Q_v)$-stable open
$\Omega_v^W\subset W(E_v)$ around the full orbit. Its factors retain precisely the local
conditions above.

**Theorem 4.4 (projective two-prime automorphic incidence).** The smooth projective
geometrically connected curve $Y/F_0$, its polarized abelian scheme $\mathcal A/Y$, and the
paired frames (4.9) satisfy:

1. the $\lambda$-factor lies in the unramified base change of
   $\mathcal C_\ell^{\mathrm{fl}}$ on every factor of $\Omega_\ell^W$;
2. the $\mathfrak q$-factor lies in the restricted clean finite-flat component of $\sigma_q$
   on every factor of $\Omega_q^W$;
3. both factors have the primitive tame-dihedral type and zero monodromy on
   $\Omega_2^W$;
4. the abelian scheme has good reduction on every other controlled factor and extends over a
   projective arithmetic carrier contained in the integral PEL open away from the fixed
   controlled set; and
5. the ambient frame cover has full product monodromy (4.12), while every component, pairing,
   orientation, coefficient idempotent, local degree, and local algebra was fixed before
   specialization.

Projectivity of $Y$, together with the finite vertical-repair ledger, is the load-bearing
conclusion; projectivity of the Hilbert modular ambient space is neither true nor used. It
converts good reduction at every remaining unnamed prime into a valuative consequence of one
global point.

## 5. A projective moving curve and its generic Galois top

The incidence space is defined over $F_0$, while the top field required later must be Galois
over $\mathbf Q$. Weil restriction puts both conjugate $F_0$-components into one
$\mathbf Q$-variety and makes the field construction equivariant from the outset.

### 5.1 Weil restriction and the local opens

Put

$$
W=\operatorname{Res}_{F_0/\mathbf Q}Y.
\tag{5.1}
$$

Weil restriction along a finite separable extension preserves smoothness and projectivity.
After base change to $\overline{\mathbf Q}$,

$$
W_{\overline{\mathbf Q}}\simeq
Y_{\overline{\mathbf Q}}\times Y^c_{\overline{\mathbf Q}},
\tag{5.2}
$$

so $W$ is geometrically connected and has dimension $2$.

For every controlled finite rational place, Section 4.6 fixed the finite Galois extension
$E_v/\mathbf Q_v$ of degree $n_v$ and a stable open. By adjunction,

$$
W(E_v)=Y(F_0\otimes_{\mathbf Q}E_v)
\tag{5.3}
$$

and

$$
z_v\in\Omega_v^W\subset W(E_v).
\tag{5.4}
$$

This open is stable under $\operatorname{Gal}(E_v/\mathbf Q_v)$. If $v$ splits in $F_0$,
(5.3) is the product of the two familiar $Y(E_v)$ factors. If $v$ is inert or ramified, it is
the corresponding field or product algebra; Sections 4.5--4.6 chose a seed on every factor. At the
real place put $E_\infty=\mathbf R$, $n_\infty=1$, and take the selected real components.
Thus every point in
(5.4) has all the exact component and good-reduction properties of Theorem 4.4.

The adjunction formula is

$$
W(L)=Y(F_0\otimes_{\mathbf Q}L)
\tag{5.5}
$$

for every $\mathbf Q$-algebra $L$. When $L$ is linearly disjoint from $F_0$, the tensor
product is the field $LF_0$. This is how a point of $W$ over the specialized top becomes one
PEL abelian variety over the final field.

### 5.2 A projective incidence curve

**Proposition 5.1 (projective curve with simultaneous local incidence).** There is a smooth
projective geometrically connected curve

$$
C\hookrightarrow W
\tag{5.6}
$$

such that $C(E_v)\cap\Omega_v^W$ contains a nonempty
$\operatorname{Gal}(E_v/\mathbf Q_v)$-stable open subset for every controlled finite place
$v$, and $C(\mathbf R)$ meets $\Omega_\infty^W$ in a nonempty open. Moreover, for one
sufficiently large integer $d$ divisible by every $n_v$, the curve can be chosen with a
base-point-free pencil having a local reduced fiber with algebra
$E_v^{d/n_v}$ supported in that open; at infinity the corresponding fiber is totally real.

**Proof.** Choose a very ample line bundle $\mathcal L$ on $W$. At every finite $v$, choose a
point $z_v\in\Omega_v^W$ whose conjugacy orbit has size $n_v$; points descending to a proper
subfield form a finite union of closed submanifolds and can be avoided. In the
coefficient space of one divisor in a sufficiently large power $\mathcal L^n$, require the
section to vanish at a moving point near every member of this orbit and require its differential
to be nonzero there. The incidence projection to the coefficient space is a submersion, so its
image contains a nonempty $\mathbf Q_v$-adic open. Use the analogous real incidence at
infinity.

The Bertini locus of smooth geometrically connected divisors is a nonempty Zariski open in the
same coefficient space. Weak approximation meets it and all the local incidence boxes. Its
divisor is the required projective curve $C$. Transversality and the implicit function theorem
give stable opens

$$
\Theta_v\subset C(E_v)\cap\Omega_v^W
\tag{5.6a}
$$

containing full $E_v/\mathbf Q_v$-orbits.

We now prove the nonsplit moving statement which is not automatic from equality of degrees.

**Local Galois-packet divisor lemma.** Let $k$ be a local field of characteristic zero,
$E/k$ a finite Galois extension of degree $n$, $C/k$ a smooth projective geometrically
connected curve, $\mathcal U\subset C(E)$ a nonempty stable open containing a point with full
orbit, and $\mathcal L_C$ an ample line bundle of degree $e$. For all sufficiently divisible
$m$, with $n\mid me$, there is a section of $\mathcal L_C^m$ whose zero scheme is reduced,
has algebra $E^{me/n}$ over $k$, and is supported in $\mathcal U$.

For the proof, let $J/k$ be the Jacobian and choose a full-orbit point $P_0\in\mathcal U$.
As $P$ varies in $\mathcal U$, consider

$$
[\operatorname{Tr}_{E/k}(P-P_0)]\in J(k).
\tag{5.6b}
$$

If $J=0$ there is no class obstruction. Otherwise choose sufficiently many points in
$\mathcal U$ so that the Abel differential over $E$ is surjective; this is possible because a
nonzero regular differential cannot vanish on an open set. The differential of
$N_{E/k}:J(E)\to J(k)$ is the field trace and is surjective. Hence a finite sum of the sets
in (5.6b) has interior in $J(k)$. The compact-group argument of Book 168 shows that their
semigroup is an open subgroup $J_{\mathcal U}$ and that a bounded number of summands fills it.
Its index is finite; independently, the norm image contains $nJ(k)$ because norm after base
change is multiplication by $n$.

Take $m=nh$ sufficiently divisible. The degree-zero class

$$
h\bigl(n[\mathcal L_C]-e[\operatorname{Tr}_{E/k}P_0]\bigr)
\tag{5.6c}
$$

then lies in $J_{\mathcal U}$. Express it as a bounded sum of (5.6b) and pad with copies of
$P_0$ until there are $me/n$ trace packets, reserving one submersive block of packet points.
The resulting effective divisor is linearly equivalent to $\mathcal L_C^m$. Move all other
packets generically inside $\mathcal U$ and use the inverse function theorem on the reserved
block to correct the small change of divisor class. This removes repetitions and collisions
among conjugates without changing the class. The divisor is therefore reduced and its
coordinate algebra is $E^{me/n}$. This proves the lemma. For
$(k,E)=(\mathbf R,\mathbf R)$ the identical argument gives a divisor of distinct real points.

Apply the lemma to one ample line bundle $\mathcal A_C$ on $C$ at every controlled place,
with $\mathcal U=\Theta_v$. The finitely many divisibility progressions have a common
sufficiently large solution $m$; put

$$
\mathcal L_C=\mathcal A_C^m,
\qquad d=\deg\mathcal L_C,
\tag{5.6d}
$$

so every $n_v$ divides $d$. We obtain local sections
$s_{\infty,v}$ whose zero algebras are $E_v^{d/n_v}$ and whose supports lie in
$\Theta_v$, and choose $s_{0,v}$ nonzero on those supports. Weak approximation in
$H^0(C,\mathcal L_C)^{\oplus2}$ gives one rational pair close to all these pairs. Avoiding
the proper resultant locus makes it base-point-free. Reducedness, the local algebra, and
support in $\Theta_v$ persist under the approximation. Thus its pencil has all the
asserted local fibers, and the real fiber is totally real. $\square$

Around the supports of the local divisors just constructed, choose and fix stable opens

$$
\mathcal U_v\subset\Theta_v\subset C(E_v)\cap\Omega_v^W.
\tag{5.7}
$$

Unlike a curve obtained by closing a curve in a quasi-projective moduli space, $C$ has no
horizontal boundary point at which the universal PEL abelian scheme can degenerate.

### 5.3 A simply branched presentation with prescribed local fibers

In Proposition 5.1 take the moving-divisor line bundle $\mathcal L_C$ sufficiently positive
also to separate every length-four subscheme. Let $(s_0,s_\infty)$ initially be the
base-point-free pair supplied there and then vary it inside the local coefficient boxes. Put

$$
f=[s_0:s_\infty]:C\longrightarrow\mathbf P^1.
\tag{5.8}
$$

The following refinement combines the moving-cycle construction of Book 168 with the simple
branch calculation needed for full symmetric monodromy.

**Lemma 5.2 (prescribed-fiber simply branched pencil).** The pair $(s_0,s_\infty)$ and a
nonempty open
$H\subset\mathbf P^1_{\mathbf Q}$ can be chosen so that:

1. $f$ is finite of degree $d\ge5$, all its ramification is simple, and distinct ramification
   points have distinct images;
2. $T=f^{-1}(H)\to H$ is finite étale;
3. for every controlled $v$ there are $b_v\in H(\mathbf Q_v)$ and a neighborhood
   $V_v\subset H(\mathbf Q_v)$ for which
   $$
   T_h\simeq
   \coprod_{j=1}^{d/n_v}\operatorname{Spec}E_v
   \tag{5.9}
   $$
   and every evaluated geometric point lies in $\mathcal U_v$ for every $h\in V_v$.
   At the real place, (5.9) means $d$ copies of $\mathbf R$.

**Proof.** Proposition 5.1 constructs the curve, line bundle, and one local reduced divisor
with exactly the algebra in (5.9). Choose a second section not vanishing on that divisor. In a
small local coefficient neighborhood, the quotient of the two sections has a common regular
value on the moving divisor and nonzero derivative at every geometric point. The simultaneous
moving-divisor submersion of Book 168 shows that these are nonempty open conditions on the
section pair. The local Galois-packet divisor lemma is what solved the Picard-class obstruction
before this coefficient approximation was attempted.

It remains to impose simple branching. In a local parameter $z$, ramification is the vanishing
of

$$
\mathcal W=s_\infty\frac{ds_0}{dz}-s_0\frac{ds_\infty}{dz}.
\tag{5.10}
$$

A double ramification point imposes $\mathcal W=\mathcal W'=0$. Allowing the point to vary
leaves a proper incidence locus in the section-pair space. Two distinct ramification points
with the same image impose their two Wronskian equations and

$$
s_0(x)s_\infty(y)-s_\infty(x)s_0(y)=0;
\tag{5.11}
$$

after allowing $(x,y)$ to vary this is again a proper incidence locus. Properness of $C$ makes
their projections closed. Their complement is Zariski open and dense. It meets every
sufficiently small local coefficient box, so weak approximation gives one rational pair which
retains (5.9) and has only distinct simple branch values.

Krasner's lemma and finite-étale local constancy retain the algebra
$E_v^{d/n_v}$ throughout a neighborhood $V_v$; Hensel's lemma retains its support in
$\mathcal U_v$. Delete the branch values to obtain $H$. $\square$

The evaluation map in the moving presentation is simply the inclusion of the moving point in
$C$ followed by (5.6):

$$
e:T\longrightarrow C\longrightarrow W.
\tag{5.12}
$$

### 5.4 The generic normal closure

Let $\widetilde E$ be the normal closure of $\mathbf Q(T)/\mathbf Q(H)$ and normalize $H$ in
$\widetilde E$. After the branch values have been deleted, this gives a finite étale Galois
cover

$$
\widetilde T\longrightarrow H.
\tag{5.13}
$$

**Proposition 5.3 (geometric top monodromy).** The cover (5.13) is geometrically connected and
its deck group is $S_d$ in the natural action on the sheets of $T$.

**Proof.** The geometric monodromy of $C\to\mathbf P^1$ is transitive because $C$ is
geometrically connected. A simple branch point contributes one transposition. The geometric
fundamental group of the complement of the branch values is generated by the branch inertia
groups. Hence geometric monodromy is a transitive subgroup of $S_d$ generated by
transpositions.

Make a graph with the $d$ sheets as vertices and the generating transpositions as edges. Its
connected components are the monodromy orbits. Transitivity makes the graph connected, and
edge transpositions of a connected graph generate $S_d$. Thus geometric monodromy is $S_d$.
Arithmetic monodromy is a subgroup of $S_d$ containing it, so it is also $S_d$. Equality of
the two groups is equivalent to geometric connectedness of the normal closure. $\square$

Let $J\simeq S_{d-1}$ be a sheet stabilizer. Then

$$
T\simeq\widetilde T/J,
\qquad
\operatorname{core}_{S_d}(J)=1.
\tag{5.14}
$$

The faithful sheet action will identify the local decomposition group of the top from the
prescribed root algebra.

### 5.5 Evaluation from the top

Compose the quotient map with (5.12):

$$
\widetilde e:\widetilde T\longrightarrow T\xrightarrow{e}W.
\tag{5.15}
$$

We evaluate the top cover itself, so the stabilizer in the approximation datum is the trivial
subgroup. A connected specialized top fiber $\operatorname{Spec}P$ gives a point of $W(P)$,
not merely a point over the root field $P^{S_{d-1}}$.

**Lemma 5.4 (the local root algebra determines the top).** Suppose
$T_h\simeq E^{d/n}$ over a nonarchimedean local field $K$, where $E/K$ is finite Galois of
degree $n$ with group $G_v$. Then the local Galois image in $S_d$ is the product of $d/n$
copies of the regular permutation action of $G_v$, and

$$
\widetilde T_h\simeq
\coprod_{S_d/G_v}\operatorname{Spec}E.
$$

**Proof.** On each field factor the local absolute Galois group acts through
$\operatorname{Gal}(E/K)=G_v$, and the embeddings of $E$ form its regular set. Thus the root
action is the displayed faithful permutation representation and its image is exactly $G_v$.
The sheet action is faithful by (5.14), so no smaller quotient has the same root algebra. On
the regular $S_d$-set underlying the top torsor, left translation by $G_v$ is free. Its orbits
are the cosets $S_d/G_v$, and each orbit has coordinate field $E$. $\square$

After shrinking $V_v$, finite-étale local constancy and Lemma 5.4 give

$$
\widetilde T_h\simeq
\coprod_{S_d/G_v}\operatorname{Spec}E_v,
\qquad
\widetilde e(\widetilde T_h)\subset\Omega_v^W
\tag{5.16}
$$

where $G_v=\operatorname{Gal}(E_v/\mathbf Q_v)$, for every $h\in V_v$. At infinity this is
the split real torsor. The containment applies to
every top sheet, not merely to one completion.

## 6. The controlled simultaneous specialization

We now impose full top monodromy, closure-level avoidance, all local conditions, and total
reality at one rational parameter. The final field $M$ and the geometric carrier $A/M$ are
both evaluations of this parameter.

### 6.1 The specialization theorem

Let $D^+$ be the finite Galois field in (2.4), enlarged once more to contain $F_0$, $K_0$, and
the normal closures of every finite level and component field introduced in Chapter 4.

**Theorem 6.1 (simultaneous Galois top and projective carrier).** There exist

$$
h\in H(\mathbf Q),
\qquad
\widetilde T_h=\operatorname{Spec}P,
\qquad
M=PF_0,
\tag{6.1}
$$

and a point $y\in Y(M)$ with the following properties.

1. $P/\mathbf Q$ is a totally real Galois extension with group $S_d$.
2. $P\cap D^+=\mathbf Q$.
3. $M/\mathbf Q$ is totally real Galois and
   $$
   \operatorname{Gal}(M/\mathbf Q)\simeq S_d\times C_2.
   \tag{6.2}
   $$
4. $M\cap D=\mathbf Q$.
5. Every controlled rational place has the prescribed local algebra
   $$
   P\otimes\mathbf Q_v\simeq E_v^{d!/n_v},
   \qquad
   M\otimes\mathbf Q_v\simeq
   (F_0\otimes_{\mathbf Q}E_v)^{d!/n_v}.
   \tag{6.2a}
   $$
6. Every localization of $y$ lies in the factor of the corresponding open $\Omega_v^W$ of
   Chapter 4.
7. Pulling back the universal family gives an abelian variety $A/M$ with good reduction at
   every finite place not above $2$ and with the exact paired frames (1.6).

The set of parameters satisfying these conclusions is dense in
$\prod_vV_v$ and is not thin in $H(\mathbf Q)$.

### 6.2 Hilbert irreducibility with top-field avoidance

**Proof of Theorem 6.1, field and local clauses.** For each conjugacy class of maximal proper
subgroups $Q\subsetneq S_d$, use the quotient cover $\widetilde T/Q\to H$. A specialization
whose image lies in a conjugate of $Q$ gives a rational point in that quotient fiber. Excluding
all such rational sheets is a finite Hilbert condition. Call the resulting Hilbert subset
$\mathcal H_{S_d}$. Its points have full specialized group $S_d$.

Proposition 5.3 makes $\widetilde T$ geometrically connected. Hence its base change to $D^+$
is connected. The disjoint-specialization theorem of Book 167 gives a Hilbert subset
$\mathcal H_{D^+}$ on which the specialized top remains connected after tensoring with
$D^+$. Intersect the two Hilbert subsets and the local boxes:

$$
h\in
\mathcal H_{S_d}\cap\mathcal H_{D^+}\cap\bigcap_vV_v.
\tag{6.3}
$$

Hilbert irreducibility with finite local approximation supplies such an $h$. The top fiber is
a connected $S_d$-torsor and therefore is $\operatorname{Spec}P$ with
$\operatorname{Gal}(P/\mathbf Q)=S_d$. Connectedness after base change to $D^+$ gives
$P\cap D^+=\mathbf Q$.

At every controlled finite place, (5.16) gives the first algebra in (6.2a) and places all
evaluated points in (5.4). Tensoring with $F_0$ gives the second algebra. Every field factor is
one of the predeclared extensions of an $F_{0,u}$ and contains the seed field $U_u$, so every
localized PEL point lies in the required Galois-stable open. At the sensitive places
$2,\ell,q$ and the original set $S_0$, the field $F_0$ splits and every completion of $M$ is
the unramified field $E_v/\mathbf Q_v$. In particular, (4.14b) makes $2$ split completely in
$M$. At the real place
it gives
$P\otimes\mathbf R\simeq\mathbf R^{d!}$, so $P$ is totally real. Since $F_0\subset D^+$,
$P\cap F_0=\mathbf Q$. Thus $M=PF_0$ is Galois with the product group (6.2) and is totally
real.

The fields $P,F_0,D$ are jointly linearly disjoint: $F_0\cap D=\mathbf Q$ by Lemma 3.1 and
$P\cap F_0D=\mathbf Q$ by construction. Hence

$$
PF_0\cap D=\mathbf Q,
\tag{6.4}
$$

which is clause 4.

Evaluation gives a point $z\in W(P)$. By (5.5) and $P\cap F_0=\mathbf Q$,

$$
W(P)=Y(P\otimes F_0)=Y(M).
\tag{6.5}
$$

Let $y$ be the corresponding point. Equation (5.16) proves the all-completions local assertion.
The density and nonthinness statements follow from the density clause of the simultaneous
Hilbert theorem; if the good set were thin, one more finite cover condition avoiding it would
contradict the same theorem. $\square$

### 6.3 Good reduction outside the controlled dyadic set

It remains to prove clause 7 globally rather than only at the places named in the local boxes.

**Proposition 6.2 (global good reduction of the specialized carrier).** The pullback
$A=y^*\mathcal A$ has good reduction at every finite place $w\nmid2$ of $M$.

**Proof.** Let $p$ be the rational prime below $w$. If $p$ lies under the final finite local
set $S$, including $\Sigma_{\mathrm{PEL}}$ and the vertical-repair set $\Sigma_Y$, then it was
included in the controlled ledger before the moving top was constructed. Every completion
there is a factor of the prescribed algebra $F_0\otimes E_v$, and the localization of $y$ lies
in the good-reduction residue tube. Thus $A$ is an abelian scheme over
$\mathcal O_{M_w}$.

Suppose $p$ is outside that set. The normalized arithmetic closure of $Y$ is projective over
the corresponding localization of $\mathcal O_{F_0}$ and lies wholly in the integral PEL open
carrying the universal abelian scheme. The map $\operatorname{Spec}M\to Y$ extends over
$\mathcal O_{M_w}$ by the valuative criterion for properness. Pulling back that abelian scheme
gives good reduction. Smoothness of the special fiber of the closure is neither asserted nor
needed.

This covers every odd $p$, including rational primes at which $M/\mathbf Q$ is ramified. Field
ramification does not affect the valuative argument. At $2$ the prescribed potentially good
tame-dihedral PEL chart is used instead, and no good-reduction claim is made. $\square$

Consequently every prime-to-$2$ Tate factor of $A$ is unramified away from its own coefficient
prime. In particular,

$$
V_\lambda(A)\text{ is unramified outside }\{2,\ell\},
\qquad
V_{\mathfrak q}(A)\text{ is unramified outside }\{2,q\}.
\tag{6.6}
$$

There is no specialization-dependent set $P_{\mathrm{bad}}$.

### 6.4 Image preservation

**Lemma 6.3 (simultaneous finite-image preservation).** Let
$r:G_{\mathbf Q}\to A_0$ be a finite-image representation whose fixed field lies in $D$.
For every intermediate field $\mathbf Q\subset L\subset M$,

$$
r(G_L)=r(G_{\mathbf Q}).
\tag{6.7}
$$

Likewise, the joint image of $\bar\sigma\oplus\bar\chi_q$ and the adjoint-detection modules on
$G_M$ equals its image on $G_{F_0}$.

**Proof.** If $D_r$ is the fixed field of $\ker r$, then $L\cap D_r=\mathbf Q$ by (6.4).
Since $D_r/\mathbf Q$ is Galois, restriction identifies
$\operatorname{Gal}(LD_r/L)$ with $\operatorname{Gal}(D_r/\mathbf Q)$.

For $\bar\sigma$, use the joint finite Galois cutout over $F_0$ of the residual,
residual-cyclotomic, and adjoint-detection representations. Its normal closure over
$\mathbf Q$ was placed in $D^+$. The equality $P\cap D^+=\mathbf Q$ gives linear
disjointness after base change to $F_0$, and hence equality of all the relative images.
$\square$

Apply the lemma to $\bar\rho$, the joint residual--cyclotomic representation, and the adjoint
detection modules. Absolute irreducibility on the cyclotomic subgroup, adequacy, scalar
centralizers, adjoint vanishing, and self-twist exclusions all survive over $M$ and every fixed
field of $M/\mathbf Q$.

### 6.5 All completions and fixed fields

Put

$$
\Gamma=\operatorname{Gal}(M/\mathbf Q)\simeq S_d\times C_2.
\tag{6.8}
$$

Fix a place $w\mid v$ of $M$ and let $D_w\le\Gamma$ be its decomposition group. For
$H\le\Gamma$, the places of $M^H$ above $v$ are indexed by

$$
D_w\backslash\Gamma/H,
\tag{6.9}
$$

and the completion belonging to the double coset $D_wgH$ is

$$
(M^H)_{v,g}\simeq M_w^{D_w\cap gHg^{-1}}.
\tag{6.10}
$$

Thus

$$
M^H\otimes_{\mathbf Q}\mathbf Q_v
\simeq
\prod_{D_wgH\in D_w\backslash\Gamma/H}
M_w^{D_w\cap gHg^{-1}}.
\tag{6.11}
$$

At a sensitive finite place $v\in S_0\cup\{q\}$, the field $F_0$ splits and $E_v$ is
unramified. The decomposition group is therefore the cyclic group
$C_{n_v}$ and $M_w=E_v$. Hence (6.11) becomes

$$
M^H\otimes\mathbf Q_v\simeq
\prod_{C_{n_v}gH\in C_{n_v}\backslash\Gamma/H}
E_v^{C_{n_v}\cap gHg^{-1}}.
\tag{6.12}
$$

Every factor is unramified over $\mathbf Q_v$. At every remaining PEL discriminant or level
prime one uses the general formula (6.11), with $M_w$ a field factor of
$F_0\otimes E_v$. The finite-flat
model, tame type, pairing,
coefficient idempotent, and orientation over that factor is the restriction of the original
local object. Formula (6.12), rather than a choice of one favored completion, controls every
place of every fixed field.

## 7. Automorphy at the auxiliary prime

We first use the minimal CM companion to make the $\mathfrak q$-adic factor of the specialized
PEL abelian variety automorphic. Unlike the ordinary two-prime bridge, this step uses no
nonminimal prime and no level-lowering assertion.

### 7.1 The specialized geometric carrier

Pulling the universal tuple of Theorem 4.4 back by $y\in Y(M)$ gives a polarized PEL abelian
variety $A/M$ and exact pairing-preserving identifications

$$
A[\lambda]\simeq
\bar\rho|_{G_M}\otimes_kk_\lambda,
\qquad
A[\mathfrak q]\simeq
\bar\sigma|_{G_M}\otimes_{k_q}k_{\mathfrak q}.
\tag{7.1}
$$

Let

$$
r_{A,q}:G_M\longrightarrow
\operatorname{GL}_2(\mathcal O_{R,\mathfrak q})
\tag{7.2}
$$

be the rank-two $\mathfrak q$-adic Tate factor. Polarization gives

$$
\det r_{A,q}=\chi_q.
\tag{7.3}
$$

At $w\mid q$ it is the restriction to the unramified completion $M_w$ of the selected
finite-flat representation of weights $\{0,1\}$. At $w\mid2$ it has the restricted labeled
tame-dihedral type with zero monodromy. By
Proposition 6.2 it is unramified at every other finite place.

### 7.2 The dihedral automorphic source over the top

Put

$$
K=K_0P=K_0M.
\tag{7.4}
$$

Because $P\cap K_0=\mathbf Q$, the extension $K/M$ is CM quadratic and its finite relative
discriminant is trivial. Pull $\Theta_0$ back by the norm $K\to K_0$ and call the resulting
Hecke character $\Theta_M$. Automorphic induction gives

$$
\Pi_{0,M}=\operatorname{AI}_{K/M}(\Theta_M).
\tag{7.5}
$$

It is a cuspidal parallel-weight-two representation. Indeed, its conjugate ratio restricts at
every dyadic place to the nontrivial order-three character, so it cannot be invariant. Mackey
restriction and norm compatibility identify its residual representation with

$$
\bar r_{\Pi_{0,M},q}\simeq\bar\sigma|_{G_M}
\tag{7.6}
$$

after the declared residue extension. Its determinant is $\bar\chi_q$.

The all-place local automorphic-induction dictionary of Books 95 and 135 gives:

$$
\begin{array}{c|c}
w\mid q&\text{the restricted selected crystalline finite-flat component}\cr
w\mid2&\text{the restricted labeled tame-dihedral component}\cr
w\nmid2q&\text{unramified}.
\end{array}
\tag{7.7}
$$

The local entries in (7.7) are the same represented conditions as those of $r_{A,q}$, not
merely conditions having equal conductor.

Because $2$ splits completely in $M$, the quadratic algebra $K/M$ remains the unramified
quadratic field at every $w\mid2$. The order-three inducing character is regular, so
$\Pi_{0,M,w}$ is depth-zero supercuspidal. Since $[M:\mathbf Q]=2d!\ge4$, fix two distinct
such places $w_\dagger,w_\ddagger\mid2$. The same inertial relation will make every packet in
either minimal deformation problem discrete series at both places. These are existing factors
of the exact dyadic tuple, not auxiliary level primes.

### 7.3 The exact auxiliary-prime deformation problem

Choose once a finite coefficient DVR $\mathcal O_q^\ast$ receiving both
$\mathcal O_{R,\mathfrak q}$ and the ring of integers of $E_{\mathrm{aux}}$, and enlarge its
residue field so that the two versions of $\bar\sigma$ are identified. Scalar-extend
$r_{A,q}$, the companion, every local type, and the automorphic lattice to
$\mathcal O_q^\ast$. Represented local conditions commute with this faithfully flat extension.

Let $R_{A,q}^{\min}$ represent fixed-determinant deformations of
$\bar\sigma|_{G_M}$ with the local tuple in (7.7). The point $r_{A,q}$ factors through this
ring. The image hypotheses hold:

$$
\bar\sigma|_{G_{M(\zeta_q)}}\text{ is absolutely irreducible},
\qquad
H^0\!\left(M,\operatorname{ad}^0\bar\sigma(1)\right)=0.
\tag{7.8}
$$

The first assertion follows from Proposition 3.3 and Lemma 6.3. Equation (3.5) gives the
second, and equality of the joint residual--cyclotomic and adjoint-detection images under
restriction to $M$ preserves that vanishing. Thus Taylor--Wiles primes exist over $M$.

Let $B_q/M$ be the quaternion algebra ramified at every real place and at
$w_\dagger,w_\ddagger$, and nowhere else. Its ramification set has cardinality
$[M:\mathbf Q]+2$, which is even. Global Jacquet--Langlands transfers $\Pi_{0,M}$ to
$B_q^\times$, because both finite local factors are discrete series. It contributes to a
finite definite class-set module with the exact local type lattice in (7.7); ramifying the
inner form at two places already in that tuple has introduced no deformation condition.

### 7.4 Integral automorphic realization

We isolate the field-uniform integral statement used at both coefficient primes.

**Proposition 7.1 (clean definite realization from an exact packet).** Let $s\ge7$, let $L$
be an even-degree totally real field whose coefficient-prime completions are unramified, and let
$\bar r:G_L\to\operatorname{GL}_2(k_s)$ satisfy cyclotomic irreducibility and the adjoint
vanishing. Suppose a cuspidal parallel-weight-two packet $\Pi_0$ realizes $\bar r$ in
characteristic $s$ and its local factors belong to the exact represented tuple, consisting of:

- clean finite-flat weight-$\{0,1\}$ conditions above $s$;
- labeled prime-to-$s$ finite inertial types with integral projectors; and
- unramified conditions elsewhere.

Assume that two distinct named finite inertial types, at $v_\dagger\nmid s$ and
$v_\ddagger\nmid s$, are discrete series. Assume that both local transfers are in
the selected tame or special range and that the primitive $v_\dagger$-type lattice is in the
curve-realizable range of Books 93--95 and 120--135 and the integral inner-form comparison
range of Books 157--160. Finally assume that the minimal level admits a center-detecting
rigidifying cover of degree prime to $s$, with no $s$-torsion arithmetic stabilizer.

Then the exact minimal definite-quaternionic localization required by Book 155 is nonzero and
has all of that book's integral automorphic properties.

**Proof.** Ramify a quaternion algebra $B^{\mathrm{def}}/L$ at every real place and at
$v_\dagger,v_\ddagger$, and nowhere else. The number of ramified places is
$[L:\mathbf Q]+2$, hence even. Weight-two discrete series transfers at infinity, the two
named finite packets transfer at the finite division places, and global Jacquet--Langlands
gives a noncharacter definite packet with every other finite local factor unchanged. Choose a
center-detecting neat cover of the minimal level at auxiliary primes whose covering and
stabilizer orders are prime to $s$, as supplied by the last hypothesis. In both applications
below it is constructed by Chebotarev at a degree-one auxiliary place with residue cardinality
$a\not\equiv0,1,-1\pmod s$, using a marked-column rigidification. Its orbit degree divides a
product of $a$, $a-1$, and $a+1$, while cyclotomic disjointness excludes an order-$s$
polarized stabilizer. The associated double-coset groupoid has trivial
stabilizers, so its integral function module is finite free and its counting pairing is
perfect. The invariant idempotent for the finite rigidifying group is integral; its image is
the module at the original local factors.

At a finite type place, intersect the rational type space with the integral function lattice
and saturate. For the dyadic type the actual inertial image is $C_3$; after adjoining
$\zeta_3$, its two primitive idempotents have denominator $3$, a unit because $s\ge7$. We do
not average over the whole group $\operatorname{GL}_2$ of the residue field, whose order may
well be divisible by $s$. The full compact type lattice is the saturated lattice generated
from those primitive inertia eigenspaces, and the companion lattice is its adjoint saturated
dual, exactly as in Books 157--160. At unramified places the hyperspecial lattice is the full
spherical lattice. Scale the packet vector to be primitive in the saturated tensor product.
Its reduction is nonzero, proving independent nonvanishing of the exact localization.

The faithful Hecke order is the image on this finite free module. In characteristic zero the
cuspidal decomposition and strong multiplicity one embed that image in a product of coefficient
fields, so its generic fiber is reduced. The pairing makes the primary and companion lattices
perfect duals. Averaging over the prime-to-$s$ rigidifying group gives exact invariants and
coinvariants, commutes with the pairing and faithful image, and returns the hyperspecial or
named minimal factor literally. Thus the neat cover introduces no undeclared ramification.

The Galois attachment uses a second quaternion algebra, not the zero-dimensional class set.
Choose one real place $\tau_0$ of $L$ and switch the invariants of $B^{\mathrm{def}}$ at
$\tau_0$ and $v_\dagger$. Thus $B^{\mathrm{curv}}/L$ is split at $\tau_0$ and
$v_\dagger$, ramified at the other $[L:\mathbf Q]-1$ real places and at
$v_\ddagger$, and nowhere else. Its ramification set has cardinality $[L:\mathbf Q]$. Every
generic branch is discrete series at the remaining division places, so global
Jacquet--Langlands transfers it from the definite class set to the one-active-real-place
Shimura curve for $B^{\mathrm{curv}}$. At the now split place $v_\dagger$, retain the
distinguished depth/type level whose new residue is the local transfer of the division type.
Take the full
Galois-stable and Hecke-stable union of its canonical components, and retain the resulting
finite component character in the faithful Hecke order. Thus neither descent of coefficients
nor passage between quaternion algebras silently discards a branch. The primitive
$v_\dagger$-type lattice, the switched-place monodromy lattice, and the saturated integral
Jacquet--Langlands comparison identify the same faithful good Hecke order on the curve and on
the definite module; no averaging by the order of the full residue-field group is used.
Locally, the two order-three inertia lines and
their adjoint lattice have Gram determinant supported only at $2$ and $3$, hence a unit at
$s\ge7$; intersecting the rational Jacquet--Langlands line with each integral lattice is
therefore primitive. Globally, multiplicity one identifies the branch summands, and saturation
then identifies their acting orders rather than merely their generic fibers.

Books 120--135 now attach the rank-two Galois representation on every generic branch through
that curve. The curve has good integral geometry at the coefficient prime, because
$v_\dagger\nmid s$, $v_\ddagger\nmid s$, and the coefficient-prime completions are
unramified. Good Hecke traces,
determinant operators, the labeled type operators, and the coefficient-prime canonical lattices
all lie in the faithful order. Residual absolute irreducibility descends the product of branch
representations to an actual representation over that order. Integral local--global
compatibility on the curve factors it through the finite-flat and finite-type local quotients on
every Artinian specialization.

Finally, adequacy and the adjoint vanishing give the Taylor--Wiles sets with ordered distinct
residual roots. At each such set the map from deep to oriented class groupoids is an effective
diamond torsor, because neatness removes every stabilizer; its function module is therefore
free over the diamond group ring. Diamond augmentation is literal fiberwise coinvariance.
The ordered-root Gram factor is a unit at the localized maximal ideal, and the saturated
old-image theorems of Books 158--160 identify oriented augmentation with the original minimal
lattice and faithful image, not a finite-index substitute. Primary--companion duality gives
the same statement on the adjoint branch. These are precisely the finite-level hypotheses of
the clean minimal theorem of Book 155. $\square$

Apply Proposition 7.1 with $s=q$, $L=M$, and $\Pi_0=\Pi_{0,M}$. Every hypothesis is verified
by (7.7)--(7.8), with $(v_\dagger,v_\ddagger)=(w_\dagger,w_\ddagger)$ as supplied by the
paragraph after (7.7). In particular, no packet at a larger deformation level is being called
minimal; the type level at the switched curve place realizes the same named dyadic condition.
The local matrix (4.13a) identifies the type with the primitive depth-zero $C_3$ lattice, whose
only projector denominator is $3$ and whose switched-place Gram determinant is a unit at
$q\ge7$. This verifies, rather than assumes, the curve-realizable and integral-transfer range
in Proposition 7.1. Moreover $\mathbf Q(\zeta_q)\subset D^+$,
$P\cap D^+=\mathbf Q$, and $F_0\cap\mathbf Q(\zeta_q)=\mathbf Q$ by ramification, so
$M\cap\mathbf Q(\zeta_q)=\mathbf Q$. An arithmetic stabilizer of order $q$ would put
$\zeta_q+\zeta_q^{-1}$ in $M$, which is impossible. The marked-column construction in the
proof of Proposition 7.1 therefore supplies the required prime-to-$q$ rigidifying cover.

### 7.5 The first exact minimal equality

Let $\mathbb T_{A,q}^{\min}$ be the faithful Hecke order on the localization supplied by
Proposition 7.1. The minimal Taylor--Wiles theorem gives

$$
R_{A,q}^{\min}\xrightarrow{\sim}\mathbb T_{A,q}^{\min}.
\tag{7.9}
$$

The common ring is finite free and a complete intersection over the auxiliary coefficient
DVR, and its automorphic module is finite free of positive rank. The point (7.2) of the left
side is therefore a Hecke character. It produces a cuspidal parallel-weight-two representation
$\Pi_A$ and, over a finite common $q$-adic field $C_q$,

$$
V_{\mathfrak q}(A)\otimes C_q
\simeq
\rho_{\Pi_A,\widetilde{\mathfrak q}}\otimes C_q.
\tag{7.10}
$$

This is an equality for the particular Tate-module point. On stable lattices it is integral:
the two lattices have absolutely irreducible common reduction, so a scaled intertwiner has
nonzero residual image, hence is surjective by irreducibility and an isomorphism by Nakayama.
The coefficient-prime finite-flat group schemes agree by full faithfulness.

### 7.6 Changing coefficient prime

At every finite place $w\nmid2\ell q$ the abelian variety has good reduction and its
real-multiplication Frobenius polynomial is

$$
P_{A,w}(X)=X^2-a_w(A)X+q_w\in R[X].
\tag{7.11}
$$

Equation (7.10) identifies this polynomial with the Hecke polynomial of $\Pi_A$ on a
density-one set. Fix once an identification of the algebraic numbers inside
$\overline{\mathbf Q}_q$. Equality in (7.10) then defines an embedding of the Hecke field
generated by the $a_w(\Pi_A)$ into $\overline{\mathbf Q}$ whose image sends every good
$a_w(\Pi_A)$ to $a_w(A)\in R$. This is an algebraic identification of the trace fields, not
an identification of a $q$-adic and an $\ell$-adic completion.

Compose that trace-field embedding with the place $\lambda$ of $R$ and extend the resulting
place through the finite full coefficient field of the packet. Book 135 attaches to the
same packet an $\ell$-adic representation at a resulting place
$\widetilde\lambda\mid\ell$. After embedding the two coefficient completions in a finite
field $C_\lambda/\mathbf Q_\ell$, algebraic equality of (7.11), Chebotarev density, and
Brauer--Nesbitt give

$$
V_\lambda(A)^{\mathrm{ss}}\otimes C_\lambda
\simeq
\rho_{\Pi_A,\widetilde\lambda}^{\mathrm{ss}}\otimes C_\lambda.
\tag{7.12}
$$

The reduction of $V_\lambda(A)$ is the absolutely irreducible module in (7.1), so its generic
fiber is irreducible. The same is then true on the right, and (7.12) is an actual isomorphism.
The marked geometric lattice of $A$ and the canonical automorphic lattice again have the same
absolutely irreducible reduction, so the homothety argument makes (7.12) integral. In
particular,

$$
\bar r_{\Pi_A,\widetilde\lambda}
\simeq\bar\rho|_{G_M}
\tag{7.13}
$$

with the exact paired lattice.

## 8. Automorphic incidence on the chosen component

Residual equality (7.13) is not yet the new theorem. The new theorem is that the
characteristic-zero automorphic point $V_\lambda(A)$ belongs to the entire exact minimal tuple
of the chosen lift. This is where projectivity of the interior incidence curve is used.

### 8.1 The target-prime carrier

Put

$$
r_{A,\ell}=V_\lambda(A).
\tag{8.1}
$$

By (7.12), $r_{A,\ell}$ is the $\widetilde\lambda$-adic realization of $\Pi_A$. By (7.1),
its reduction is $\bar\rho|_{G_M}$. Polarization gives

$$
\det r_{A,\ell}=\chi_\ell.
\tag{8.2}
$$

It remains to compare every local component with $\mathcal D(\rho)|_M$.

### 8.2 Place-by-place component identification

**Proposition 8.1 (exact local coincidence).** The representations $r_{A,\ell}$ and
$\rho|_{G_M}$ factor through the same represented local quotient at every finite place of
$M$.

**Proof.** Let $w\mid\ell$. The completion $M_w/\mathbf Q_\ell$ is the prescribed unramified
extension. The point $y_w$ lies in the residue tube constructed from the integral Morita
comparison in Section 4.5. Its residual finite locally free kernel is therefore the named
model, and every Artinian quotient of the lattice in $r_{A,\ell}$ belongs to the base-changed functor
$\mathcal C_\ell^{\mathrm{fl}}|_{G_{M_w}}$. This is the same coefficient-linear functor,
pairing, and connected--étale or local--local label as the restriction of the chosen lattice
of $\rho$.

Let $w\mid2$. The extension $M_w/\mathbf Q_2$ is unramified, so restriction preserves the
order-three inertia pair. The dyadic local seed puts both factors on the restricted closed
tame-dihedral component with characteristic equation $T^2+T+1=0$ and zero monodromy. The
integral order-three projector is primitive because $3$ is a unit in $\mathcal O$. Thus
$r_{A,\ell}$ and $\rho$ factor through the same restricted labeled quotient
$\mathcal C_2^{\mathrm{tq}}$, not merely through loci with isomorphic generic inertia.

Finally let $w\nmid2\ell$. Proposition 6.2 gives good reduction of $A$ at $w$. Néron--Ogg--
Shafarevich makes $r_{A,\ell}$ unramified. The chosen lift is unramified by (1.2), so both
factor through $\mathcal C_w^{\mathrm{ur}}$.

These cases exhaust the finite places. $\square$

There is no special/unramified intersection in this proof. In particular, no equation (2.5),
component group (2.6), Rees parameter, or multi-prime lowering complex is invoked.

### 8.3 Exact-minimal residual occurrence

Let $B_\ell/M$ be the quaternion algebra ramified at every real place and at
$w_\dagger,w_\ddagger$, and nowhere else. The packet $\Pi_A$ transfers to $B_\ell^\times$:
at both selected dyadic places its local factor is discrete series. At every place above $2$
select the integral tame-dihedral type lattice, using its division-algebra transfer at the two
ramified places; at every other place away from $\ell$ use hyperspecial level, and at $\ell$
use the weight-two coefficient lattice. Proposition 8.1 shows that these are exactly the local
factors of $R_M^{\min}$.

Let

$$
\mathcal M_M^{\min}
\tag{8.3}
$$

be the resulting localized definite-quaternionic module. The $\widetilde\lambda$-reduction of
the transferred vector of $\Pi_A$ is nonzero and has residual Galois representation
$\bar\rho|_{G_M}$. Hence

$$
\mathcal M_M^{\min}/\varpi\mathcal M_M^{\min}\ne0.
\tag{8.4}
$$

Equation (8.4) is independent exact-minimal nonvanishing. It is not obtained by contracting a
maximal ideal from a larger special-level module.

Apply Proposition 7.1 with $s=\ell$, $L=M$, and $\Pi_0=\Pi_A$. Lemma 6.3 supplies
cyclotomic irreducibility and adjoint vanishing. Proposition 8.1 supplies the exact local tuple.
Since $M_{w_\dagger}=\mathbf Q_2$ and the order-three Frobenius exchanges the inertia lines,
$\Pi_{A,w_\dagger}$ is discrete series; the same holds at $w_\ddagger$. They supply the two
finite division factors and the switched curve-realization place in Proposition 7.1. Therefore
all integral automorphic hypotheses of Book 155 hold for (8.3). As in the auxiliary
application, (4.13a) and the primitive $C_3$ lattice make the relevant projector and
switched-place Gram factors units at $\ell\ge7$. Since
$\mathbf Q(\zeta_\ell)\subset D$ and $M\cap D=\mathbf Q$, an order-$\ell$ arithmetic
stabilizer is likewise impossible; the prime-to-$\ell$ rigidifying cover is therefore exact.

### 8.4 The simultaneous automorphic-incidence theorem

**Theorem 8.2 (simultaneous automorphic incidence).** The one specialization $h$ of Theorem
6.1 produces simultaneously:

1. the controlled Galois field $M/\mathbf Q$ of (6.2)--(6.4);
2. the geometric PEL carrier $A/M$ with both exact torsion frames;
3. an automorphic auxiliary-prime realization $V_{\mathfrak q}(A)$;
4. an automorphic target-prime realization $r_{A,\ell}=V_\lambda(A)$; and
5. a nonzero integral automorphic vector in the exact minimal module (8.3), on every local
   component containing the chosen point $\rho|_{G_M}$.

All coefficient actions, alternating pairings, determinant characters, finite-flat quotient
systems, dyadic type labels, and unramified local conditions agree integrally.

**Proof.** Chapters 4--6 construct the field and the PEL point from one top fiber. Proposition 7.1
and (7.9)--(7.10) make the auxiliary Tate factor automorphic. Changing coefficient prime gives
(7.12). Proposition 8.1 identifies every target local component, and the transferred vector of
$\Pi_A$ gives (8.4). The integral lattice comparisons in Sections 7.5--7.6 preserve the paired
frames and coefficient actions. $\square$

Theorem 8.2 is the new input that was absent from the ordinary potential-modularity argument.
It supplies automorphic support before target-prime patching begins.

## 9. The clean target-prime equality

We now prove the complete $R=\mathbb T$ package over the same field $M$. The proof is the clean
minimal Taylor--Wiles argument, but every finite-level hypothesis is repeated here so that no
field-specific certificate is silently transported from Book 185.

### 9.1 The deformation ring and faithful Hecke order

Let $R_M^{\min}$ represent deformations of $\bar\rho|_{G_M}$ with determinant $\chi_\ell$
and the local tuple

$$
\mathcal D_M^{\min}=
\left(
\mathcal C_w^{\mathrm{fl}}\ (w\mid\ell),
\ \mathcal C_w^{\mathrm{tq}}\ (w\mid2),
\ \mathcal C_w^{\mathrm{ur}}\ (w\nmid2\ell)
\right).
\tag{9.1}
$$

Framed rings are used locally when the residual centralizer is not scalar; the global
unframed ring exists because the global residual representation is absolutely irreducible.
The fixed determinant removes the scalar tangent direction.

Let $\mathcal O^\ast$ be the ring of integers of one finite extension of $\mathbf Q_\ell$
receiving $\mathcal O$, $\mathcal O_{R,\lambda}$, all type values, and the coefficient place
of $\Pi_A$. Let $\mathcal M_M^{\min}$ be (8.3) after scalar extension to
$\mathcal O^\ast$. The residual representations and their named finite-flat models are
identified after the corresponding residue extension. For notational economy in the rest of
this chapter, rename $\mathcal O^\ast$ as $\mathcal O$
and its uniformizer as $\varpi$. Faithfully flat descent to the earlier coefficient ring is
performed in Section 9.6. Replace $R_M^{\min}$ by its represented completed base change and
retain the same symbol. Define

$$
\mathbb T_M^{\min}
=\operatorname{im}\!\left(
\mathbb T^{\mathrm{abs}}\longrightarrow
\operatorname{End}_{\mathcal O}(\mathcal M_M^{\min})
\right).
\tag{9.2}
$$

This is the faithful acting order by definition. The module is finite free over $\mathcal O$:
it is a saturated direct summand of a function module on a finite neat double-coset set. Its
primary--companion pairing is perfect. The exact-minimal vector of Theorem 8.2 proves that the
localization is nonzero.

In characteristic zero, strong multiplicity one decomposes the localized module into finitely
many cuspidal eigenspaces. Thus

$$
\mathbb T_M^{\min}[1/\ell]\hookrightarrow\prod_iE_i
\tag{9.3}
$$

and is reduced. Torsion-freeness of the action on a finite free module makes
$\mathbb T_M^{\min}$ finite torsion free over $\mathcal O$.

### 9.2 The Hecke-valued representation

Every factor $E_i$ in (9.3) carries the rank-two Galois representation of Books 134--135. At
a good place $w$ its polynomial is

$$
X^2-T_wX+q_wS_w.
\tag{9.4}
$$

The traces lie in the faithful order. Residual absolute irreducibility and the trace-algebra
descent theorem turn the product of the branch representations into

$$
\rho_{\mathbb T}:G_M\longrightarrow
\operatorname{GL}_2(\mathbb T_M^{\min})
\tag{9.5}
$$

with determinant $\chi_\ell$.

Branchwise local--global compatibility kills the defining ideals of the labeled dyadic and
unramified local quotients in every $E_i$. Since the order embeds in their product, those ideals
vanish integrally. At $w\mid\ell$, the canonical automorphic lattice and its finite-flat
quotients put every Artinian specialization of (9.5) in the represented finite-flat functor.
Thus (9.5) is an object of the deformation problem (9.1), not merely a generic
pseudorepresentation.

Universality gives

$$
R_M^{\min}\longrightarrow\mathbb T_M^{\min}.
\tag{9.6}
$$

Good traces, determinant operators, and the already fixed local type operators generate the
faithful order, so (9.6) is surjective.

### 9.3 Taylor--Wiles systems and exact augmentation

Put $W=\operatorname{ad}^0\bar\rho|_{G_M}$. Lemma 6.3 gives

$$
\bar\rho|_{G_{M(\zeta_\ell)}}\text{ absolutely irreducible},
\qquad
H^0(M,W(1))=0.
\tag{9.7}
$$

Adequacy selects, for every $n$, a set $Q_n$ of Taylor--Wiles primes detecting the dual Selmer
group, with ordered distinct residual Frobenius roots and
$q_w\equiv1\pmod{\ell^n}$. Let $\Delta_n$ be the product of their maximal $\ell$-power tame
quotients.

At $Q_n$ use the oriented local deformation rings and the matching deep-level definite class
sets. The level map is an effective $\Delta_n$-torsor because the base level is neat. Hence the
primary and companion modules

$$
\mathcal M_{Q_n},\qquad\mathcal M_{Q_n}^{\dagger}
\tag{9.8}
$$

are finite free over $\mathcal O[\Delta_n]$ and perfectly paired. The augmentation ideal
$\mathfrak a_n\subset\mathcal O[\Delta_n]$ gives exact identities

$$
\mathcal M_{Q_n}/\mathfrak a_n\mathcal M_{Q_n}
\simeq\mathcal M_M^{\min},
\tag{9.9}
$$

$$
\mathbb T_{Q_n}/\mathfrak a_n\mathbb T_{Q_n}
\simeq\mathbb T_M^{\min}.
\tag{9.10}
$$

The equalities are literal. Freeness makes higher $\operatorname{Tor}$ vanish; saturation of
the type and rigidifying-level maps prevents a finite-index lattice from replacing the right
side. The corresponding oriented deformation ring has the same augmentation to
$R_M^{\min}$.

Let $t$ be the dual Selmer dimension and choose $|Q_n|=t$. The sharp tangent computation for
the unframed clean problem says that the ordered auxiliary ring has exactly $t$ absolute
cotangent generators: the $t$ killed dual classes are replaced by the $t$ ordered tame
directions, while the balanced local terms at $2$, above $\ell$, and at infinity cancel. Thus,
after marking a cotangent basis at each level, there are surjections from the one fixed regular
domain

$$
P_\infty=\mathcal O[[x_1,\ldots,x_t]]
\tag{9.11}
$$

onto every finite auxiliary deformation shadow. The diamond group rings patch to the second
regular domain

$$
S_\infty=\mathcal O[[z_1,\ldots,z_t]],
\qquad
\dim P_\infty=\dim S_\infty=t+1.
\tag{9.12}
$$

Patch marked finite shadows, not the nonnested arithmetic levels. Besides bases, Hecke
operators, pairings, and the three augmentation maps, retain the entire kernel ideal of
$P_\infty$ at every Artinian precision. Diagonalization then gives

$$
R_\infty=P_\infty/I_\infty,
\qquad
\mathcal M_\infty\simeq S_\infty^{\oplus a}\quad(a>0),
\tag{9.12a}
$$

together with its perfectly paired companion. Let

$$
A_\infty=\operatorname{im}\!\left(
P_\infty\longrightarrow R_\infty
\longrightarrow\operatorname{End}_{S_\infty}(\mathcal M_\infty)
\right).
\tag{9.12b}
$$

The structural diamond map makes the composite $S_\infty\to A_\infty$ act by ordinary
scalars. Hence it is injective, because $\mathcal M_\infty$ is a nonzero free
$S_\infty$-module. The image $A_\infty$ is finite over $S_\infty$: after a basis is chosen it
is an $S_\infty$-submodule of the finite matrix algebra
$\operatorname{End}_{S_\infty}(\mathcal M_\infty)$. The marked exact sequences and the
Mittag--Leffler property give literal augmentation identities

$$
\begin{aligned}
R_\infty/(z_1,\ldots,z_t)&\simeq R_M^{\min},\\
\mathcal M_\infty/(z_1,\ldots,z_t)&\simeq\mathcal M_M^{\min},\\
A_\infty/(z_1,\ldots,z_t)&\simeq\mathbb T_M^{\min}.
\end{aligned}
\tag{9.12c}
$$

The first line retains the full deformation ring, including any ideal that might annihilate
all automorphic modules; it is not obtained by patching acting images. No optimization complex
occurs because there is no nonminimal prime.

### 9.4 Faithfulness, reducedness, and the equality

We give the equal-variable step, since it is what rules out the algebra in (12.1). Write
$A_\infty=P_\infty/J$. The scalar injection and finiteness just proved make
$S_\infty\subset A_\infty$ an integral extension. Consequently

$$
\dim A_\infty=\dim S_\infty=\dim P_\infty.
$$

If $J$ contained $0\ne f$, then $f$ would be a nonzerodivisor in the regular domain
$P_\infty$, and

$$
\dim A_\infty\le\dim P_\infty/(f)=\dim P_\infty-1,
$$

a contradiction. Thus $J=0$ and $P_\infty\simeq A_\infty$. Since the map to $A_\infty$
factors through $R_\infty=P_\infty/I_\infty$, this also forces $I_\infty=0$. Hence

$$
R_\infty=P_\infty\xrightarrow{\sim}A_\infty.
\tag{9.13}
$$

The ring $P_\infty$ is finite over $S_\infty$ and is Cohen--Macaulay of the same dimension.
For a finite local extension, depth computed with either maximal ideal agrees; hence
$\operatorname{depth}_{S_\infty}P_\infty=t+1$. Auslander--Buchsbaum over the regular local
ring $S_\infty$ makes $P_\infty$ finite free over $S_\infty$. The parameters
$\varpi,z_1,\ldots,z_t$ are a regular sequence on the $S_\infty$-free module
$\mathcal M_\infty$. Since the two maximal ideals have the same radical on every finite
$P_\infty$-module, this gives
$\operatorname{depth}_{P_\infty}\mathcal M_\infty=t+1$. A second
Auslander--Buchsbaum calculation over the regular ring $P_\infty$ gives

$$
\mathcal M_\infty\simeq P_\infty^{\oplus m}
\qquad(m>0).
\tag{9.13a}
$$

Thus the patched action is scheme-theoretically faithful, including nilpotent directions; this
is stronger than meeting every generic component. The images of $z_1,\ldots,z_t$ form a
regular sequence on both $P_\infty$ and $\mathcal M_\infty$. Augmenting (9.13) with the
literal identities (9.12c) gives

$$
\boxed{R_M^{\min}\xrightarrow{\sim}\mathbb T_M^{\min}},
\tag{9.14}
$$

and

$$
\mathcal M_M^{\min}\text{ is finite free of positive rank over }R_M^{\min}.
\tag{9.15}
$$

Thus the minimal module is faithful. Since the Hecke generic fiber is reduced by (9.3), the
same is true of $R_M^{\min}[1/\ell]$. The balanced presentation and (9.13) make the common
ring a finite free complete intersection over $\mathcal O$ through the regular augmentation
in (9.12c); the perfect pairing gives its
Gorenstein duality.

This proof uses Theorem 8.2 exactly once: it supplies the independently nonzero finite-level
module to which the patching system is attached. Patching then proves faithfulness for the
clean ring. It is never asked to transfer support from another local component.

### 9.5 Evaluation at the chosen point

Restriction of the fixed lift gives a local homomorphism

$$
x_\rho:R_M^{\min}\longrightarrow\mathcal O.
\tag{9.16}
$$

Through (9.14), this is a character of the faithful Hecke order. After inverting $\ell$, it
selects a field factor in (9.3), and a simultaneous eigenvector in
$\mathcal M_M^{\min}[1/\ell]$. Global Jacquet--Langlands transfers that eigenvector to a
cuspidal parallel-weight-two representation $\pi_M$ of
$\operatorname{GL}_2(\mathbf A_M)$.

For every good $w$,

$$
\operatorname{charpol}(\rho(\operatorname{Frob}_w);X)
=X^2-x_\rho(T_w)X+q_w
=\operatorname{charpol}(\rho_{\pi_M,\lambda_M}(\operatorname{Frob}_w);X).
\tag{9.17}
$$

Chebotarev and Brauer--Nesbitt identify the generic representations over a common finite
coefficient field $C$. Both are irreducible because their residual representation is
absolutely irreducible. More strongly, specializing the Hecke-valued representation (9.5)
along $x_\rho$ gives the same strict-equivalence class as the universal representation. After
scaling the generic intertwiner, residual irreducibility and Nakayama identify the stable
lattices. Therefore

$$
\boxed{
\rho|_{G_M}\otimes_EC
\simeq
\rho_{\pi_M,\lambda_M}\otimes C
}
\tag{9.18}
$$

integrally.

In particular, if $\mathfrak p_\rho$ is any minimal prime of
$R_M^{\min}[1/\ell]$ through $x_\rho$, then (9.15) gives, for some $m>0$,

$$
(\mathcal M_M^{\min})_{\mathfrak p_\rho}
\simeq
(R_M^{\min})_{\mathfrak p_\rho}^{\oplus m}\ne0.
\tag{9.18a}
$$

Thus the exact characteristic-zero point selected in Book 185 lies on automorphic support over
the very field $M$ produced with the carrier $A$; it is not merely congruent to an automorphic
point on another branch. Equation (9.18), rather than residual congruence alone, identifies the
point itself.

### 9.6 Integral local--global compatibility

The construction of (9.5) before evaluation records the bad places, so they are not recovered
from the density argument.

- If $w\mid\ell$, both sides of (9.18) use the selected coefficient-linear finite-flat
  lattice. Every quotient is represented by the same finite locally free group scheme, and the
  connected--étale or local--local label is unchanged.
- If $w\mid2$, both sides factor through $\mathcal C_w^{\mathrm{tq}}$. Their tame generator
  obeys $T^2+T+1=0$, wild inertia and monodromy are zero, and the integral type lattice is the
  selected primitive lattice.
- If $w\nmid2\ell$, both sides are unramified. Their local Weil--Deligne parameter has
  $N=0$ and Frobenius polynomial (9.17).

The alternating pairing in the Hecke carrier specializes to the pairing of $\rho$, so

$$
\det\rho_{\pi_M,\lambda_M}=\chi_\ell.
\tag{9.19}
$$

All auxiliary coefficient enlargements are finite and faithfully flat. The local quotient
ideals, module freeness, equality (9.14), and lattice isomorphism descend because their kernels
and cokernels vanish after faithful flat base change. This completes the exact clean package
claimed in Theorem 1.1.

## 10. Elementary fixed fields

The top field was chosen Galois because the later Brauer family uses many fixed fields at once.
Now that $\pi_M$ has been constructed, solvable descent along the upper extensions is an
existence theorem rather than a proposed source of top automorphy.

### 10.1 The field family

Let

$$
\Gamma=\operatorname{Gal}(M/\mathbf Q)=S_d\times C_2.
\tag{10.1}
$$

For every subgroup $H\le\Gamma$, put

$$
F_H=M^H.
\tag{10.2}
$$

Galois correspondence gives

$$
F_{H_1}F_{H_2}=F_{H_1\cap H_2},
\qquad
F_{H_1}\cap F_{H_2}=F_{\langle H_1,H_2\rangle}.
\tag{10.3}
$$

For $\gamma\in\Gamma$,

$$
\gamma(F_H)=F_{\gamma H\gamma^{-1}}.
\tag{10.4}
$$

Every $F_H$ is totally real and disjoint from $D$. Lemma 6.3 therefore preserves the full
residual and residual--cyclotomic images on every $G_{F_H}$.

### 10.2 Prime-cyclic towers

A finite group is elementary when it is a direct product of a cyclic group of order prime to
$p$ and a $p$-group, for some prime $p$. Such a group is solvable. If $H$ is elementary, choose
a subnormal series

$$
1=H_0\triangleleft H_1\triangleleft\cdots\triangleleft H_r=H
\tag{10.5}
$$

whose quotients have prime order. Reversing fixed fields gives

$$
M=F_{H_0}\supset F_{H_1}\supset\cdots\supset F_{H_r}=F_H,
\tag{10.6}
$$

and every upper step is cyclic Galois of prime degree. This is the exact range of Books 96--97.

### 10.3 Descent selected by the extending representation

**Proposition 10.1 (automorphic descent to elementary fixed fields).** For every elementary
$H\le\Gamma$ there is a unique cuspidal parallel-weight-two packet $\pi_H$ over $F_H$, up to
the explicitly fixed central character, such that

$$
\operatorname{BC}_{M/F_H}(\pi_H)=\pi_M
\tag{10.7}
$$

and, over one finite common coefficient field,

$$
\rho|_{G_{F_H}}\simeq\rho_{\pi_H,\lambda_H}.
\tag{10.8}
$$

The packet is independent of the chosen series (10.5).

**Proof.** Descend through (10.6) one cyclic layer at a time. Suppose the current top packet is
defined over $F_{H_{i-1}}$. For an element of
$\operatorname{Gal}(F_{H_{i-1}}/F_{H_i})$, its conjugate has the same good Hecke polynomials:
both are those of the restriction of the representation $\rho$, which is defined already on
$G_{F_{H_i}}$. Strong multiplicity one makes the packet invariant.

The selected cyclic descent theorem gives a packet downstairs, unique up to a character of the
cyclic quotient. The representation $\rho|_{G_{F_{H_i}}}$ supplies extension data, so compare
the finitely many character twists with its traces at primes whose Frobenius maps to each
quotient element. Exactly one twist has the required trace and determinant. Choose it. Its
Galois representation is $\rho|_{G_{F_{H_i}}}$ by Chebotarev. Lemma 6.3 preserves the
self-twist exclusions placed in $D$; hence two distinct quotient characters cannot both pass
this test, even in a dihedral-looking trace-zero coset.

Residual-image preservation makes that representation absolutely irreducible. A noncuspidal
descent would have a reducible two-dimensional Galois parameter, so every stage is cuspidal.
Repeating gives (10.7)--(10.8). If another subnormal series is chosen, both endpoints have the
same good Hecke polynomials and central character; strong multiplicity one identifies them.
$\square$

The proposition uses automorphy at the top established in Chapter 9. It is not used to create
that automorphy.

### 10.4 Compatibility of all local records

At every sensitive rational place in $S_0\cup\{q\}$, (6.12) identifies each completion
of each $F_H$ with a specified unramified subextension of $E_v/\mathbf Q_v$; at the remaining
PEL and vertical-repair primes, (6.11) gives the equally explicit factors. Hence $\pi_H$ has the
corresponding restriction of:

- the exact labeled tame-dihedral factor above $2$;
- the selected finite-flat Galois lattice above $\ell$;
- trivial finite central character in the covariant normalization; and
- the same coefficient, pairing, and orientation labels as $\pi_M$.

At other places the local parameter is the restriction of the parameter of $\rho$ through the
completion in (6.10). The cyclic base-change local dictionary shows that the packets in
(10.7) have precisely these restrictions. Conjugation carries $\pi_H$ to
$\pi_{\gamma H\gamma^{-1}}$, and the identifications agree with (10.4).

## 11. Coefficients, Frobenius polynomials, and purity

### 11.1 Coefficient fields and lattices

Let $E_{\pi_M}$ be the number field generated by the good Hecke eigenvalues of $\pi_M$, the
finite type values, and the central character. Enlarge it once to contain the fields of the
finitely many packets $\pi_H$ used in the elementary family. Choose embeddings into one
algebraic closure of $\mathbf Q_\ell$ and then a finite extension $C/\mathbf Q_\ell$ receiving
all selected completions and $E$.

The integral representation in (9.18) uses a stable lattice whose reduction is absolutely
irreducible. Such a lattice is unique up to homothety. Indeed, after scaling two lattices so
that $L'\subset L$ but $L'\nsubseteq\varpi L$, the image of $L'$ in $L/\varpi L$ is a nonzero
stable subspace and hence the whole space; Nakayama gives $L'=L$. Thus the coefficient
enlargements introduce no lattice ambiguity in the finite-flat quotient system.

### 11.2 Frobenius data

Let $\Sigma_M$ contain the places above $2\ell$ and the finite places where the field or level
ledger excludes the good formula. For $w\notin\Sigma_M$, define

$$
P_w(X)=X^2-a_w(\pi_M)X+q_w
\in E_{\pi_M}[X].
\tag{11.1}
$$

Equation (9.18) gives

$$
P_w(X)=\det\!\left(X-\rho(\operatorname{Frob}_w)\right).
\tag{11.2}
$$

If $u$ is a place of $F_H$ below $w$, the polynomial of $\pi_H$ is the characteristic
polynomial of the appropriate Frobenius power on $\rho|_{G_{F_H}}$. This is exactly the local
base-change relation; it is not obtained by reusing $a_w$ when the residue degree is greater
than one.

At the bad places the record includes the full Weil--Deligne parameter. It has zero monodromy
everywhere for the chosen lift: at $2$ the inertia type is finite tame of order three, and away
from $2\ell$ the representation is unramified. At $\ell$ the integral finite-flat system is
recorded instead of a prime-to-$\ell$ Weil--Deligne assertion.

### 11.3 Purity and conjugation

The packet $\pi_M$ is cuspidal, cohomological of parallel weight two, and noncharacter. The
weight-two realization theorem of Books 134--137 therefore gives

$$
|\iota(\alpha)|=q_w^{1/2}
\tag{11.3}
$$

for every complex embedding $\iota$ and every root $\alpha$ of $P_w$. Thus the chosen lift is
pure of weight one after restriction to $G_M$, and the same is true over every $F_H$.

For $\gamma\in\Gamma$,

$$
P_{\gamma w}(X)=P_w(X)
\tag{11.4}
$$

after transporting the place and coefficient embedding through the extension data of $\rho$.
This conjugation compatibility is what makes the elementary packet family one coherent record
rather than a list of unrelated potential-automorphy fields.

## 12. Failure diagnostics

The successful construction is easiest to audit by locating the precise hypotheses that rule
out the earlier failure modes.

### 12.1 Why a nonproper carrier is insufficient

Finite local approximation on a quasi-projective Hilbert--Blumenthal space controls only the
places named before specialization. It cannot require good reduction at every unnamed place.
A specialized point can therefore acquire a finite set of semistable primes known only after
the field and abelian variety have been chosen.

Lemma 4.3 replaces that space by a projective curve lying wholly inside the framed PEL interior
and carrying the restricted universal abelian scheme. The finitely many vertical boundary
intersections of its arithmetic closure are repaired and entered in the ledger before the top
is moved. Proposition 6.2 then uses the valuative criterion at all remaining unnamed odd
places. This is a global consequence of properness, not an infinite intersection of local
opens.

### 12.2 Why no component jump is used

At an unramified residual point, a closed special local condition and the unramified condition
have only the incidence quotient cut out by (2.5). A patched module supported on the special
branch need not support a chosen generic unramified point. Nothing in Chapters 7--9 contradicts
that fact.

Here $A$ has good reduction at every $w\nmid2$, so $V_\lambda(A)$ is itself unramified there.
At $2$ it is on the same labeled finite-inertia component as $\rho$, and at $\ell$ it is on
the same clean finite-flat component. The automorphic vector (8.4) is therefore already in the
exact module patched in Chapter 9. The support theorem is applied only after this finite-level
incidence has been established.

Nor do we infer faithfulness from that one vector. The elementary counterexample

$$
R=\mathcal O[[x]]/(x(x-\varpi)),
\qquad
N=R/(x)
\tag{12.1}
$$

has a nonzero finite free $\mathcal O$-module on one characteristic-zero branch and misses the
other. The incidence theorem by itself would not rule this out. Chapters 7.4 and 9.3 instead
construct the effective diamond torsors, saturated type lattices, perfect companion pairing,
and literal acting-order augmentation. After patching, the source is a regular domain with the
same dimension as the scalar power-series ring and the patched module is nonzero and free over
that scalar ring. A nonzero kernel would lower dimension, so it is impossible. Geometric
incidence supplies the exact finite-level object and equal-variable rigidity separately proves
scheme-theoretic faithfulness; neither conclusion is substituted for the other.

### 12.3 Why the old automorphy field is not transported

Book 185 used a totally real field $F_{\mathrm{aut}}$ to prove finiteness of a restricted
deformation ring and hence to construct (1.1). Its normal closure can have nonsolvable sheet
stabilizer, so Books 96--97 do not in general carry its packet to a new Galois top.

No inclusion between $F_{\mathrm{aut}}$ and $M$ is asserted here. The packet
$\Pi_{0,M}$ is constructed anew over $M$ by automorphic induction, $\Pi_A$ is constructed by
the first minimal equality over $M$, and $\pi_M$ is constructed by the second. Thus no
nonsolvable base change is hidden in the proof.

### 12.4 Why the Galois closure is specialized directly

Disjointness of a root field from $D$ does not imply disjointness of its normal closure. A
quadratic resolvent can lie in $D$ even when the root field has trivial intersection with it.
Chapter 6 instead imposes connectedness of the generic top after base change to $D^+$ and
specializes that top itself. Therefore $P\cap D^+=\mathbf Q$ is a closure-level statement.

Likewise, local factor degrees of a root polynomial do not determine the full top torsor in
general. Here the complete local algebra $E_v^{d/n_v}$ is prescribed, not merely its factor
degrees. Its local Galois group acts through the displayed repeated regular permutation
representation, and the sheet action is faithful. Lemma 5.4 therefore determines the top
decomposition group and every top
completion. Formula (6.11) then controls every intermediate completion.

## 13. Dependency and hypothesis audit

### 13.1 Direct prerequisites

The following table records the exact imported interfaces.

| Books | Imported result | Use in this book |
|---|---|---|
| 2, 6 | local-field approximation and finite-Galois reciprocity/Chebotarev | globalization of $R$ and the finite prime selections in Chapters 3--4 |
| 59--60, 72 | integral Fontaine--Laffaille and $p$-divisible base change; Taylor--Wiles prime detection | the auxiliary finite-flat lattice and the exact auxiliary-prime systems |
| 93--94 | finite definite quaternionic modules, global Jacquet--Langlands, exact finite local factors, rationality, and multiplicity | the nonzero exact packet modules in Sections 7.4 and 8.3 |
| 95 | algebraic Hecke characters, determinant formula, all-place automorphic induction, lattices, and norm pullback | Lemma 3.2 and $\Pi_{0,M}$ |
| 96--97 | prime-cyclic base change and descent, character fibers, cuspidality, and local compatibility | Proposition 10.1 after top automorphy is known |
| 120--122 | fine Shimura curves, proper integral correspondences, Hecke actions, pairings, and specialization | the integral geometric Hecke module used in Proposition 7.1 |
| 123 | common-determinant rank-two groups, trace-pairing symplectic representations, exact centers, and matrix Morita factors | construction of the split PEL datum |
| 124--125 | CM types, polarized CM abelian varieties, reflex norms, reciprocity, and good reduction | the CM and local PEL seeds in Chapters 3--4 |
| 126--130 | PEL canonical models, fine representability, component reciprocity, universal abelian schemes, local models, and good integral charts | Sections 4.1--4.5 and Proposition 7.1; the finite-cusp contraction itself is proved in Lemma 4.1 |
| 131--133 | semistable and automorphic cohomological decompositions with integral pairings | the branchwise geometric realization and its bad-place boundary |
| 134--135 | rank-two Galois representations, canonical lattices, finite-flat quotient systems, and compatible coefficient realizations | (7.10)--(7.13), (9.5), and local--global compatibility |
| 136--137 | all-place local--global compatibility and purity of compatible weight-two coefficient systems | the bad-place and purity records in Chapters 9 and 11 |
| 148 | rational-isogeny and Frey residual irreducibility results | upstream applications may use it to verify Book 185 admissibility; no theorem of Book 148 is used in the proof here |
| 155 | clean minimal Taylor--Wiles $R=\mathbb T$, exact augmentation, faithfulness, and recovery of every minimal lift | (7.9) and the specialized proof in Chapter 9 |
| 156 | variance of local conditions and the exact nonminimal boundary | identifies the shortcut avoided in Sections 2.4 and 12.2; no nonminimal theorem is invoked |
| 157--166 | integral type lattices, switched-place Jacquet--Langlands order comparison, saturation, Hecke-valued representations, diamond freeness, patching, and support-to-faithfulness | verification and assembly of the finite systems in Chapters 7 and 9 |
| 167 | Hilbert subsets, full-group resolvents, local approximation, and closure-level disjointness | Theorem 6.1 |
| 168 | simultaneous moving cycles, the local Abel/compact-group argument, and local concentration | Proposition 5.1 and Lemma 5.2 |
| 169 | paired-frame descent, product monodromy, local PEL seeds, and exact local opens | the frame and local-seed templates strengthened by the projective interior construction in Chapter 4 |
| 170 | the two-prime coefficient-change architecture and its distinction between residual and chosen-lift automorphy | Chapters 7--8 |
| 171 | Galois top torsors, fixed-field completion formulas, elementary subgroups, and compatible field families | Sections 5.5, 6.5, and Chapter 10 |
| 174 | controlled dihedral data, finite-flat auxiliary components, simultaneous local frames, and integral coefficient carriers | the local companion ledger; the added signed Steinberg place is deliberately replaced by Chapter 3 |
| 185 | the balanced chosen lift, cyclotomic irreducibility, represented local tuple, and modularity-admissible realization data | the fixed input (1.1)--(2.3) |

The split parallel-signature PEL construction in Section 4.1 is not cited as a theorem beyond
the prerequisites. It uses the explicit common-determinant matrix group (4.3), the trace-pairing
representation (4.3b), and matrix Morita theory at the two coefficient primes. Its component
set is computed in (4.6a), rather than inferred from the multiplier by analogy. Lemma 4.1
develops the minimal compactification from the toroidal Fourier charts and Koecher's principle;
only its finite cusp boundary, not projectivity of the ambient PEL moduli problem, is used to
cut the projective interior curve of Lemma 4.3.

### 13.2 The decisive hypothesis matches

At the target coefficient prime, every completion is the predeclared unramified
$E_v/\mathbf Q_\ell$ of Section 4.6, the named residual finite locally free model is built into
the integral Morita seed, and its local ring is the unramified base change of the one
represented in Book 185. At the auxiliary coefficient prime, every completion is the
predeclared unramified $E_v/\mathbf Q_q$ and the seed is the restriction of the induced
finite-flat object; if the
unramified quadratic algebra splits after base change, this restriction is ordinary, on the
same restricted clean component. At $2$, the PEL seed and both Hecke characters use the same
order-three tame torus and the same primitive integral type lattice, unchanged by unramified
base change.

The arithmetic closure of the interior curve is formed before Chapter 5. Its intersection
with the finite cusp scheme is supported at finitely many primes. The vertical-repair argument
constructs an actual good-reduction point over a recorded local extension at each of them, and
only then are the local packet degree, moving pencil, and top cover chosen. Thus Proposition
6.2 does not hide either an infinite local condition or a prime discovered after specialization.

The requirement that $2$ split completely in $M$ is structural, not cosmetic. It leaves
$M_{w_\dagger}=M_{w_\ddagger}=\mathbf Q_2$, so Frobenius exchanges the two nontrivial
inertia lines of the order-three type and both local packets are discrete series. The definite
algebra is ramified at all real places and at these two dyadic places. Switching its invariants
at $w_\dagger$ and one real place produces an algebra split at those two places, ramified at
$w_\ddagger$ and all remaining real places, and hence a one-active-real-place Shimura curve.
This is exactly the orientation of the switched-place integral Jacquet--Langlands theorem:
the curve is split at $w_\dagger$, while the definite algebra is division there. Proposition
7.1 uses the full canonical-component union, the switched monodromy lattice, and the saturated
$w_\dagger$-type lattice, so every branch of the faithful definite Hecke order is realized in
curve cohomology before a Galois representation is attached.

At every other finite place, the two representations used in the corresponding lifting step
are unramified: for the CM companion this follows from finite unramifiedness of $K_0/F_0$ and
Lemma 3.2; for the PEL carrier it follows from Proposition 6.2. Therefore each residual
automorphic packet occurs at the exact minimal tuple. This is the hypothesis that was missing
from the nonproper construction.

Closure-level disjointness preserves the full residual images. Consequently the cyclotomic
irreducibility, adequacy, scalar centralizers, adjoint vanishing, and self-twist exclusions used
by both minimal patches are the original ones, not weaker properties inferred from the image
order.

### 13.3 Circularity audit

The order of proof is:

1. construct $\rho$ in Book 185;
2. construct $F_0,K_0,q,\bar\sigma$ without using target automorphy over $M$;
3. construct the split paired-frame PEL space, its finite-cusp compactification, its local
   seeds, and the projective interior incidence curve;
4. specialize its Galois top and obtain $A/M$;
5. construct the dihedral packet $\Pi_{0,M}$ directly over $M$;
6. use the auxiliary-prime minimal theorem to prove $V_{\mathfrak q}(A)$ automorphic;
7. change coefficient prime to prove that $V_\lambda(A)$ is an automorphic point of the exact
   target tuple;
8. run the target minimal patch and evaluate it at the pre-existing point $\rho|_{G_M}$; and
9. only then descend from $M$ to elementary fixed fields.

The target $R=\mathbb T$ equality is not used to construct its finite-level carrier. The
carrier is $\Pi_A$, proved automorphic by the separate $q$-adic equality. The $q$-adic equality
is seeded by automorphic induction and does not use residual or characteristic-zero automorphy
of $\bar\rho$. Thus the two lifting arguments do not depend on one another in a circle.

### 13.4 Books not used

No theorem from Books 187--189 is used. In particular, no compatible-system Brauer induction,
nonsolvable base change, or later descent theorem is invoked to manufacture $\pi_M$. The
elementary packets of Chapter 10 are obtained only after $\pi_M$ exists and only by the
prime-cyclic theorems of Books 96--97.

## 14. Conclusion

The chosen characteristic-zero lift is automorphic over the controlled Galois field $M$.
The proof does not promote residual automorphy by abstract patching across unmatched local
components. It constructs, in the same specialization that constructs $M$, a point on a
projective PEL incidence curve whose target-prime Tate factor is already an automorphic point
of the exact minimal tuple.

Two changes make this possible. The everywhere-finite-unramified CM companion eliminates the
deliberately added Steinberg place, and the projective curve inside the split PEL interior
eliminates every unpredictable bad-reduction place. The first exact minimal equality makes the
auxiliary Tate factor automorphic. Compatible coefficient realizations then put the target Tate
factor in the exact finite-flat, tame-quadratic, and unramified local conditions of $\rho$.
This supplies the nonzero minimal carrier before the second patch.

The second equality is therefore clean:

$$
R_M^{\min}=\mathbb T_M^{\min},
\qquad
\rho|_{G_M}\simeq\rho_{\pi_M,\lambda_M}.
\tag{14.1}
$$

The acting Hecke order is faithful and generically reduced, the automorphic module is finite
free of positive rank, every auxiliary augmentation is exact, and the integral local--global
record includes the determinant, coefficient actions, finite-flat quotient system, dyadic type,
and all unramified factors. The same representation descends automorphically to every elementary
fixed field with compatible conjugation and cyclic base change.

The dependency audit is therefore **READY**: the chosen-lift theorem is unconditional under the
modularity-admissible hypotheses of Book 185, is closed under the stated prerequisites, and
uses no result from Books 187--189.
