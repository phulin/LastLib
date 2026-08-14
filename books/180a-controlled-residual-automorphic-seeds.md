# Controlled Residual Automorphic Seeds

**Status.** This is a conditional minitextbook. It fixes the exact pre-181 seed contract and
proves only the source-closed constructions identified below. It does not assert
$({\rm Seed}_{\mathrm{SP}})$. Its geometric and arithmetic blocker chains are retained in
proof order in Chapter 12.

## Contents

1. [The seed problem](#1-the-seed-problem)
   - [The required object](#11-the-required-object)
   - [Conventions](#12-conventions)
   - [The proof order and source cutoff](#13-the-proof-order-and-source-cutoff)
2. [The signed-special Frey datum and fixed coefficient seed](#2-the-signed-special-frey-datum-and-fixed-coefficient-seed)
   - [Global residual data](#21-global-residual-data)
   - [The dyadic component](#22-the-dyadic-component)
   - [The coefficient-prime ordinary replacement](#23-the-coefficient-prime-ordinary-replacement)
   - [Restriction to controlled fields](#24-restriction-to-controlled-fields)
3. [The auxiliary prime and dihedral representation](#3-the-auxiliary-prime-and-dihedral-representation)
   - [The auxiliary prime from the fixed Frobenius polynomials](#31-the-auxiliary-prime-from-the-fixed-frobenius-polynomials)
   - [Determinant and ray compatibility](#32-determinant-and-ray-compatibility)
   - [Protected branch correction](#33-protected-branch-correction)
4. [Paired local seeds](#4-paired-local-seeds)
   - [Multiplicative seeds](#41-multiplicative-seeds)
   - [Good seeds](#42-good-seeds)
5. [The singleton moving boundary](#5-the-singleton-moving-boundary)
   - [The fixed Abel-class offset](#51-the-fixed-abel-class-offset)
   - [What the local geometry proves](#52-what-the-local-geometry-proves)
   - [The first missing theorem](#53-the-first-missing-theorem)
   - [The conditional moving implication](#54-the-conditional-moving-implication)
6. [The conditional normal top and raw carrier](#6-the-conditional-normal-top-and-raw-carrier)
   - [Normal-closure avoidance](#61-normal-closure-avoidance)
   - [The conditional normal top](#62-the-conditional-normal-top)
   - [The dyadic raw-carrier boundary](#63-the-dyadic-raw-carrier-boundary)
7. [The auxiliary-prime lifting ledger](#7-the-auxiliary-prime-lifting-ledger)
   - [The active set](#71-the-active-set)
   - [Conditional routed Ihara](#72-conditional-routed-ihara)
   - [The actual global cube](#73-the-actual-global-cube)
   - [The pointed carrier and occurrence](#74-the-pointed-carrier-and-occurrence)
8. [Certified target lowering](#8-certified-target-lowering)
   - [The target active set](#81-the-target-active-set)
   - [The curve-only edge theorem](#82-the-curve-only-edge-theorem)
   - [Component and branch-Smith torsion](#83-component-and-branch-smith-torsion)
   - [Strict inter-edge localization](#84-strict-inter-edge-localization)
9. [Conditional nonvanishing and final occurrence](#9-conditional-nonvanishing-and-final-occurrence)
   - [Induction along a certified path](#91-induction-along-a-certified-path)
   - [The path-compatible carrier](#92-the-path-compatible-carrier)
   - [Rational transfer and a primitive lattice](#93-rational-transfer-and-a-primitive-lattice)
10. [The bottom structural ledger](#10-the-bottom-structural-ledger)
    - [The minimal problem and maximal ideal](#101-the-minimal-problem-and-maximal-ideal)
    - [Modules, pairings, and orders](#102-modules-pairings-and-orders)
    - [Integral Galois attachment](#103-integral-galois-attachment)
    - [Auxiliary augmentation without circularity](#104-auxiliary-augmentation-without-circularity)
11. [The exact seed contract](#11-the-exact-seed-contract)
    - [The packaged datum](#111-the-packaged-datum)
    - [The required theorem](#112-the-required-theorem)
    - [What is deliberately absent](#113-what-is-deliberately-absent)
12. [Construction boundary](#12-construction-boundary)
    - [The exact first blocker chain](#121-the-exact-first-blocker-chain)
    - [Conditional downstream blocker chains](#122-conditional-downstream-blocker-chains)
    - [Source ledger and verdict](#123-source-ledger-and-verdict)

## 1. The seed problem

### 1.1 The required object

The input to a balanced minimal modularity argument is not merely an abstract residual
representation known to be automorphic at almost all primes. It is an exact integral
automorphic datum. The residual representation must occur in the localization dictated by
its represented local conditions, and that localization must already carry the modules,
pairings, faithful Hecke order, Galois representation, and auxiliary-level augmentation used
by patching.

This distinction is unavoidable. Two characteristic-zero branches can have the same residual
good-prime traces while lying on different integral local components. A type lattice can have
the right generic fiber and the wrong reduction. An old image can be injective after inverting
the coefficient uniformizer while failing to be primitive. In each case an abstract residual
eigensystem survives, but the seed needed for a scheme-theoretic comparison does not.

A **controlled residual automorphic seed** will therefore include:

1. a controlled totally real field and its splitting and disjointness certificate;
2. the exact signed-special residual representation over that field;
3. the represented minimal deformation problem, including every line, sign, determinant,
   monodromy, and finite-flat condition;
4. a nonzero non-Eisenstein definite-quaternionic localization on that problem;
5. primary and companion modules with a perfect integral pairing;
6. a generically reduced faithful Hecke order and branchwise integral Galois attachment; and
7. the represented-ring, module, pairing, diamond, and named-operator augmentation data needed
   at Taylor--Wiles level.

Before either nonminimal stage, the coefficient-prime seed is fixed: if the Frey curve is
multiplicative at $\ell$, its selected residual finite-flat model is realized by a good
ordinary replacement. Only after that replacement exists is the auxiliary prime $q$ chosen
from the resulting fixed Frobenius polynomial. The dihedral and paired branches are then
constructed. The first nonminimal stage makes the resulting auxiliary $q$-adic Tate module
automorphic. Only afterward is that packet viewed at the target prime $\ell$, where excess
target level is removed. The active sets, coefficient rings, local conditions, and carriers
in those two stages are not interchangeable.

### 1.2 Conventions

Let $\ell\geq7$ be the target residual characteristic. Let $E/\mathbf Q_\ell$ be a finite
extension with ring of integers $\mathcal O$, uniformizer $\varpi$, and residue field $k$.
Representations are covariant. At a finite place $v$, write $F_v$ for arithmetic Frobenius,
so

$$
\chi_\ell(F_v)=q_v.
$$

For a special representation with monodromy $N_v$ we use

$$
F_vN_vF_v^{-1}=q_vN_v.
$$

With geometric Frobenius $\Phi_v=F_v^{-1}$ this becomes

$$
\Phi_vN_v\Phi_v^{-1}=q_v^{-1}N_v.
$$

Lines, signs, and roots are always carried with the chosen convention. The auxiliary prime is
denoted $q$ and is distinct from $\ell$. The auxiliary lifting set is
$P_{\mathrm{aux}}$; the later target-lowering set is $P_{\mathrm{tar}}$. A distinguished
special place in the auxiliary construction is $v_0$.

### 1.3 The proof order and source cutoff

The intended order is

$$
\begin{array}{c}
\text{Frey datum + exact coefficient-prime finite-flat model}\\
\Downarrow\\
\text{fixed good coefficient-prime seed, ordinary replacement if needed}\\
\Downarrow\\
\text{choose }q\text{ from the fixed good Frobenius polynomials}\\
\Downarrow\\
\text{independently automorphic dihedral datum + paired local Hilbert--Blumenthal seeds}\\
\Downarrow\\
\text{one singleton moving presentation and Galois approximation datum}\\
\hline
\text{normal-top specialization }A/M\\
\Downarrow\\
\text{actual lower dihedral faces and certified }P_{\mathrm{aux}}\text{ comparison}\\
\Downarrow\\
\text{upper automorphic occurrence of }V_{\mathfrak q}(A)\\
\Downarrow\\
\text{cross-prime nonzero upper target localization}\\
\Downarrow\\
\text{path-compatible carrier and certified }P_{\mathrm{tar}}\text{ edges}\\
\Downarrow\\
\text{nonzero bottom minimal SP curve localization}\\
\Downarrow\\
\text{primitive transfer to the definite minimal SP localization}\\
\Downarrow\\
\text{minimal structural ledger}.
\end{array}
\tag{1.1}
$$

The horizontal line separates pre-specialization geometry from post-specialization arithmetic.
Every arrow must be proved before the next object can be used. In particular the replacement
at $\ell$ is fixed before $q$, the $q$-branches do not exist before that choice, a selected
characteristic-zero lift cannot be inserted to prove residual component occurrence, and
Moret--Bailly specialization cannot be credited with the lower automorphic face.

The construction must be logically complete before Book 181. Books 181 and later may be used
only to check the downstream interface, never to prove existence of the seed which they
consume. In particular, the source-closed observations in Book 182, Sections 2 and 4, are useful
consistency checks, but no theorem of Book 182 is a premise below.

The lettered manuscripts 061a, 138a, 157a, and 175a have honest but noncatalogued interfaces.
They have no independent numbered row in `BOOKS.md` or `BOOK_DEPENDENCIES.md`, so they are not
new catalog nodes. Their proved theorems may nevertheless be cited at their stated scope, and
their conditional theorems remain conditional. Thus 138a proves its cohomological,
power--commutator, compact-transgression, finite-product, normalized-gluing, and scalar
reductions, but retains the required interfaces $({\rm CEN}_\star)$,
$({\rm PAIR}_\star)$, $({\rm LOC}_n)$, $({\rm PROD}_n)$, $({\rm SC}_n)$, and
$({\rm TOR})$; its $({\rm QRM}_m)$ and $({\rm PA}_m)$ are only proposed sufficient routes,
and its locally compact Pontryagin input is isolated separately. The manuscript 157a proves
the Raynaud and fan results, explicit homogenized Mumford and Kummer-normalized charts, and
$({\rm BCP})$ in their stated scopes. In rank $d\geq2$ its global projective branch retains
five antecedents: $({\rm GCC})$, $({\rm Raw\text{-}DF\text{-}IIT})$, $({\rm FRCD})$,
$({\rm KFF})$, and the structured Hilbert extension $({\rm TDC\text{-}Ext})$. In rank one,
Book 111, Theorem 13.1 supplies only its stated global
compactification; 157a separately assumes the supplied-model antecedent
$({\rm R1\text{-}FTJ})$ before proving arbitrary-$Z$ avoidance and the empty-slice
$({\rm ICS})$ conclusion. The corrected 175a formal several-place cube remains valid for odd $\ell$,
but does not prove nonunit mixed or higher Ihara, routed coherence, product residue, or joint
occurrence. Finally, 061a places $({\rm SHB})$ first in its height route; only after it come
the sufficient $({\rm Tor})$--$({\rm HT})$--$({\rm SlopeFJ})$ route to
$({\rm CMH})$, while a direct $({\rm CMH})$ bypasses that route and activates the proved
downstream finiteness and semisimplicity chain. Calling these manuscripts either unconditional
solutions or content-free rejected drafts would be equally inaccurate.

## 2. The signed-special Frey datum and fixed coefficient seed

### 2.1 Global residual data

Let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k)
\tag{2.1}
$$

be the residual representation attached to a primitive Frey datum of exponent
$\ell\geq7$. The standing global requirements are:

$$
\det\bar\rho=\bar\chi_\ell,
$$

$\bar\rho$ is absolutely irreducible, and its restriction to
$G_{\mathbf Q(\zeta_\ell)}$ is absolutely irreducible. These are field-control requirements,
not consequences of later automorphy.

The target determinant is the cyclotomic lift

$$
\delta=\chi_\ell.
\tag{2.2}
$$

At all finite places outside the dyadic and coefficient-prime sets, the minimal problem is
unramified. Any auxiliary place introduced during construction belongs to a temporary
nonminimal problem and must be removed before the final seed is declared.

### 2.2 The dyadic component

At $2$, the Frey representation lies on a named signed-special component. This means more than
having a Steinberg semisimplification. The represented condition retains:

- the invariant line;
- the split or nonsplit unramified sign;
- the primitive Kummer or monodromy class;
- the determinant; and
- the arithmetic-Frobenius relation $F_2N_2F_2^{-1}=2N_2$.

The local deformation problem is the schematic closure of that named component. The open
condition $N_2\ne0$ is not imposed on every Artinian quotient; the characteristic-zero point
will later be required to lie in the nonzero-monodromy open.

If $F/\mathbf Q$ is totally real and $2$ splits completely in $F$, then each completion
$F_w$ for $w\mid2$ is literally $\mathbf Q_2$. The line, sign, and primitive monodromy datum
are therefore preserved without multiplying the monodromy parameter by a ramification index.

### 2.3 The coefficient-prime ordinary replacement

At every place above $\ell$, the residual representation is required to have a selected
finite-flat model of weights $\{0,1\}$. The model is part of the represented problem. Equality
of generic residual representations does not identify finite flat group schemes.

When the Frey curve has good reduction at $\ell$, its own finite-flat model supplies the local
seed; denote that good local elliptic scheme by $\mathcal B_\ell$. When the Frey curve has
multiplicative reduction, the residual representation can still be finite flat, but the full
characteristic-zero Tate module is special and is not a point of the good finite-flat
deformation condition. The replacement must be constructed now, before an auxiliary prime or
an auxiliary branch is chosen.

In the multiplicative case the selected residual finite-flat model has a multiplicative
connected line and an etale quotient, so any good realization of that same model must be
ordinary.

Book 157, Proposition 8.4B and Lemma 8.4B.1 give the ordinary local construction. They produce
a principally polarized good ordinary elliptic scheme
$\mathcal B_\ell/\mathbf Z_\ell$ and an identification

$$
\mathcal B_\ell[\ell]\otimes_{\mathbf F_\ell}k
\simeq\mathcal G_{\mathrm{Frey}},
\tag{2.3}
$$

including its line, Kummer class, and sign. In both the good-Frey and replacement cases, fix
$\mathcal B_\ell$ and its arithmetic-Frobenius polynomial

$$
P_\ell(X)=X^2-a_\ell(\mathcal B_\ell)X+\ell,
\qquad
\Delta_\ell=a_\ell(\mathcal B_\ell)^2-4\ell,
\tag{2.4}
$$

before doing anything involving $q$. No $q$-frame or ordered auxiliary branch has yet been
constructed. This is the coefficient-prime ordinary replacement required by the represented
finite-flat problem; it does not construct a global moving presentation or an automorphic
localization.

### 2.4 Restriction to controlled fields

Let $D/\mathbf Q$ contain the matrix cutout of $\bar\rho$, the joint
residual-cyclotomic cutout, and every finite orientation, component, and self-twist field that
must remain visible. A finite Galois field $M/\mathbf Q$ satisfying

$$
M\cap D=\mathbf Q
\tag{2.5}
$$

preserves the residual and cyclotomic residual images on restriction. Disjointness from a
projective cutout would not suffice.

If $2$ and $\ell$ split completely in $M$, all local fields at those primes are the original
rational completions. Thus restriction preserves the exact dyadic component and the exact
coefficient-prime model rather than merely a deformation-theoretic analogue after ramified
base change.

## 3. The auxiliary prime and dihedral representation

### 3.1 The auxiliary prime from the fixed Frobenius polynomials

Only now choose an auxiliary prime $q\geq7$, distinct from $\ell$, outside the finite
exclusion set arising from residual images, determinant lines, local frames, and protected ray
conditions. The already fixed polynomial (2.4) imposes

$$
q\nmid\Delta_\ell.
\tag{3.1}
$$

If the chosen seed at $3$ is also good, impose in addition
$q\nmid a_3(\mathcal B_3)^2-12$, where $\mathcal B_3$ is the already fixed good seed there.
After coefficient extension, each of these fixed good Frobenius polynomials has two distinct
roots modulo $q$. Order those roots. At $\ell$ they are precisely the two unramified branches
of $\mathcal B_\ell[q]$ that the auxiliary construction must match. Thus the logical order is

$$
\mathcal B_\ell\ \text{and }P_\ell
\quad\longrightarrow\quad q
\quad\longrightarrow\quad
\text{ordered good }q\text{-branches}.
\tag{3.2}
$$

Choose a CM quadratic field $L/\mathbf Q$ split at $2$, $3$, $\ell$, and $q$, and an
algebraic Hecke character $\theta$ of $L$ of the required weight. Its automorphic induction is
a parallel-weight-two dihedral packet, while

$$
\bar r=\operatorname{Ind}_{G_L}^{G_{\mathbf Q}}\bar\theta
\tag{3.3}
$$

is the auxiliary residual representation. An extra place detects nontriviality of the
conjugate ratio and is protected through all subsequent character corrections.

### 3.2 Determinant and ray compatibility

For a quadratic induction,

$$
\det\operatorname{Ind}_{G_L}^{G_{\mathbf Q}}\bar\theta
=\bar\theta|_{G_{\mathbf Q}}\,\eta_{L/\mathbf Q},
\tag{3.4}
$$

with restriction interpreted through transfer. At a multiplicative place the desired pair is

$$
(\eta_v\oplus\eta_v\bar\chi_q)\otimes k_q,
\tag{3.5}
$$

and at a good place it is the $q$-torsion of the chosen good elliptic seed. Both have
determinant $\bar\chi_q$. The product condition is necessary for an anti-cyclotomic
correction, since such a correction multiplies the two conjugate branches by inverse
characters.

Over the rational base, Book 178, Lemma 4.1A proves the extra relative-ray compatibility after
the determinant-compatible local branch factors, quadratic conductor, and real sign are
included in the modulus. Book 178, Theorem 4.2 then constructs the controlled dihedral seed
from the corrected ray datum. The corresponding relation remains a hypothesis over a general
totally real base. Neither statement controls all local uniformizer values: an
inertia-preserving ray character can still change an unramified Frobenius root.

### 3.3 Protected branch correction

At each controlled place choose an ordered local branch pair with determinant matching
$\bar r$. Book 178, Lemma 4.3 gives a protected anti-cyclotomic Grunwald correction, producing
a finite-order character
$\psi$ with

$$
\psi^c=\psi^{-1}.
\tag{3.6}
$$

It changes the first branch by the prescribed quotient and the conjugate branch by its
inverse, while remaining trivial at the coefficient-prime finite-flat protection place and at
the conjugate-ratio witness. Replacing $\theta$ by $\theta\psi$ preserves the determinant,
cuspidality witness, and infinity type.

The output is an identity of ordered residual Frobenius branches, not merely of inertia
restrictions. This distinction matters when the dihedral packet is later compared with the
auxiliary Tate module on an exact local component.

## 4. Paired local seeds

### 4.1 Multiplicative seeds

Let $v\in\{2,3\}$ be a place of multiplicative reduction, let $u_v$ be the Frey Tate
parameter, and let $\eta_v$ be the unramified splitting character. The coefficient prime is
deliberately absent: even when the Frey curve is multiplicative at $\ell$, the paired seed
there is the good scheme $\mathcal B_\ell$ already fixed in Section 2.3. Choose a neat integer
$N$ prime to $6\ell q$. Because exponentiation by $qN$ is an automorphism of
$\mathbf Q_v^\times/(\mathbf Q_v^\times)^\ell$, choose $b_v$ such that

$$
[b_v^{qN}]=[u_v]
\quad\text{in}\quad
\mathbf Q_v^\times/(\mathbf Q_v^\times)^\ell.
\tag{4.1}
$$

After multiplying $b_v$ by a sufficiently large $\ell$th power of a uniformizer, put

$$
t_v=b_v^{qN}
$$

with positive valuation. The Tate curve $B_v$ with parameter $t_v$, descended by $\eta_v$ in
the nonsplit case, then satisfies

$$
B_v[\ell]\simeq E[\ell],
\qquad
B_v[q]\simeq\eta_v\oplus\eta_v\bar\chi_q.
\tag{4.2}
$$

At $v=2$, the first isomorphism retains the canonical multiplicative line, the primitive
Kummer class, and the sign. Thus it retains the exact signed-special label.

### 4.2 Good seeds

At a good place take the fixed good elliptic seed: the Frey elliptic curve where it already has
good reduction, and the scheme $\mathcal B_\ell$ fixed in Section 2.3 at the coefficient
prime. The choice of $q$ in Section 3.1 makes its residual Frobenius roots distinct, and the
corrected dihedral branch of Section 3.3 supplies the matching ordered $q$-frame. The identity
supplies the $\ell$-frame. Weil pairings give the determinant orientations on the two-prime
Hilbert--Blumenthal twist.

Book 157, Theorem 13.1 constructs the relevant local points, their paired frames, the corrected
component, and the point-centered opens. It also explains why five different topologies are
needed: real connected components, good integral tubes, ordinary Hasse opens, fixed
nonordinary residue disks, and semistable valuation shells. Corollary 13.2 exports exactly this
local-seed package. These are unconditional local inputs in their stated unramified odd-prime
and tensor-Tate ranges; they are not a global moving theorem.

At $\ell$ the protected branch correction therefore gives the exact identity

$$
\bar r|_{G_{\mathbf Q_\ell}}
\simeq\mathcal B_\ell[q]\otimes_{\mathbf F_q}k_q.
\tag{4.3}
$$

This identity is assembled only after the order (2.3)--(3.2): first the ordinary replacement,
then $q$, then the dihedral branch, and finally the paired local seed. In particular (4.3)
cannot be used retroactively to choose $\mathcal B_\ell$ or to justify the choice of $q$.

## 5. The singleton moving boundary

### 5.1 The fixed Abel-class offset

The local points must occur as fibers of one finite etale incidence cover

$$
T_0\longrightarrow H_0
\tag{5.1}
$$

over an open of affine space. At split certificate places the fiber must split completely and
all sheets must remain in their assigned opens. At a distinguished place $v_0$ the fiber must
contain exactly one special degree-one factor, while every added factor is good minimal.

Flexible split packets can be enlarged to a common degree, and exact packets can be repeated
wholesale. The singleton packet is different: repetition creates more than one special
factor. The obstruction is already visible on the local curve used by a moving pencil. Let
$S$ be the special point, $P$ a good point, and $\mathcal A$ the pencil line bundle of degree
$e$. Put

$$
b=[\mathcal A]-e[P],
\qquad
c=[S-P].
\tag{5.2}
$$

Let $\mathscr R^{\mathrm{good}}_{v_0,d}$ be the set of degree-zero classes represented by
reduced degree-$d$ divisors all of whose residue factors lie in allowed good-minimal tubes. A
fixed special point would require

$$
nb-c\in\mathscr R^{\mathrm{good}}_{v_0,ne-1}
\tag{5.3}
$$

for an exponent synchronized with all other packets. Making $n$ highly divisible can kill
$nb$ in a finite Jacobian quotient without killing $c$. Smoothness and Hensel lifting move
points inside their residue tubes; they do not prove that the special and good tubes occupy
the same norm--Abel coset.

### 5.2 What the local geometry proves

Book 157 proves the parts of the boundary geometry that can be constructed without an
exhaustive global toroidal compactification. The exact locators are Lemmas 13.2A.1--13.2A.2,
Propositions 13.2A.3--13.2A.4, Lemma 13.2B.1, Lemma 13.2B.2, and Propositions
13.2B.2a--13.2B.2c:

1. paired-frame Kummer normalization is finite algebraically before completion;
2. a simultaneous regular projective equivariant fan can be chosen;
3. Raynaud extraction and inverse-to-Mumford comparison hold over complete traits;
4. the correctly dimensioned completed ring represents the Mumford-presented toroidal
   subfunctor;
5. finite-field Bertini and stable complete-intersection slicing work once one global smooth
   projective joining model and ample line have been supplied; and
6. the uniformizer-saturated closure of a proper generic closed subset contains no component
   of an integral special fiber.

The lettered source 157a retains and extends these constructions. Its Theorem 4.2 constructs
the simultaneous regular projective fan, Chapters 6 and 9 construct the explicit homogenized
Mumford family and its finite Kummer normalization, Proposition 10.1 proves bounded conductor
presentation for those explicit charts, and Proposition 11.1 algebraizes the supplied-DF
Mumford charts. Finite normalization here does not prove the finite locally free assertion
$({\rm KFF})$. Nor do these results prove $({\rm GCC})$, recognize all deformations of an
already labelled fiber as Mumford deformations, or coherently choose the framed roots on
conductor faces.

These results prove local nonemptiness, explicit chart construction, and the conditional
implications used in a moving argument. They do not unconditionally construct the exhaustive
global finite-type model joining the selected cusp branch to the good interior. In rank one,
Book 111, Theorem 13.1 supplies only the applicable global compactification;
$({\rm R1\text{-}FTJ})$ separately supplies the selected smooth projective finite-type model,
completed framed Tate--Mumford branch, relatively very ample line, and coefficient and
PEL-frame descent isomorphisms required by 157a, Section 17.1.

### 5.3 The first missing theorem

For arbitrary geometric Hilbert--Blumenthal boundary objects, the first missing assertion is
157a, Hypothesis 3.1, the geometric cusp classification $({\rm GCC})$. It must place every
labelled geometric semiabelic PEL fiber at a nonzero Hilbert cusp in a unique Mumford cusp,
periodic-cell, and fan-face class, with intrinsic normalized stars and conductor arrows.
$({\rm GCC})$ precedes intrinsic recognition: Raw-DF-IIT begins only after such a Mumford
label has been fixed and therefore cannot prove $({\rm GCC})$.

For rank $d\geq2$, the next missing recognition assertion is 157a, Hypothesis 7.1, the raw
Deligne--Faltings intrinsic infinitesimal theorem $({\rm Raw\text{-}DF\text{-}IIT})$. It must
recover from the raw multiplication-defect object the framed Fourier monoid, its sharp
quotient, loop holonomy, leading units, and $\operatorname{Div}(A)$-valued symmetric monoidal
chart. It must also kill the secondary-fan kernel and commute with faces, conductor arrows,
cusp changes, and arbitrary square-zero base change. Only then does 157a, Conditional Theorem
7.2 deduce the older unframed $({\rm IIT})$ interface. Its exact framed conductor-root form
also requires 157a, Hypothesis 9.1, $({\rm FRCD})$.

The elementary obstruction is not cosmetic. Let

$$
C'=k[\epsilon]/(\epsilon^2),
\qquad C=k,
$$

and let the external boundary parameter map to zero. Then

$$
B'=C'[X,Y]/(XY-\epsilon)
\tag{5.4}
$$

is flat over $C'$ and reduces to the labelled node $k[X,Y]/(XY)$. Its intrinsic smoothing
parameter is $\epsilon$, not the external parameter zero times a unit. A character grading,
rank-one weight spaces, and the reduced labelled star do not remove this extra direction.

Declaring the object strict over the external chart excludes (5.4), but that declaration
defines a smaller toroidal subfunctor. It does not prove that the full underlying PEL functor
is strict. The example is one square-zero shadow of the fuller raw defect: it neither recovers
loop holonomy nor rules out the secondary-fan kernel. Book 157 proves monomial reconstruction
after divisibility is supplied; 157a identifies the stronger recognition statement from which
that divisibility follows. Neither proves $({\rm GCC})$, and neither proves
$({\rm Raw\text{-}DF\text{-}IIT})$ in higher rank.

Two further antecedents occur at the framed conductor and descent stages. Hypothesis 9.1,
$({\rm FRCD})$, supplies actual coherent choices of the root-line comparisons across both
conductor arrows. Hypothesis 9.2, $({\rm KFF})$, says that every finite Kummer normalization
used as a descent cover is finite locally free and compatible with faces, compositions, and
base change. The existence of a frame over-lattice does not prove FRCD, and finiteness of a
normalization does not prove KFF.

A fifth antecedent enters only at projectivity. Hypothesis 15.1,
$({\rm TDC\text{-}Ext})$, requires, compatibly with coefficient base change, faces, cusp
changes, conductor descent, and the finite theta-deck action: extension of the structured
interior morphism $h_H^\theta$ to $h^\theta:X_\Sigma^\theta\to Q^\theta$ with corrected
Plucker coordinates having no common zero and agreeing on every overlap; quasi-finiteness of
$h^\theta$; and, for a fixed ample tensor product of the Plucker factors and admissible theta
powers $m_j$, the canonical exact Plucker-line isomorphism

$$
(h^\theta)^*\mathcal O_{Q^\theta}(1)
\simeq\bigotimes_j\mathcal H_{m_j}^{\otimes a_j},
\qquad a_j>0,
\tag{5.4a}
$$

including its interior determinant identity and boundary trivializations. Equality of
numerical classes is not enough. Thus the resulting higher-rank conditional deductions must
be recorded with all five antecedents:

$$
\begin{gathered}
({\rm Raw\text{-}DF\text{-}IIT})
\Longrightarrow({\rm IIT})_{\rm unfr}
\Longrightarrow({\rm MPE})_{\rm unfr},\\
({\rm GCC})+({\rm Raw\text{-}DF\text{-}IIT})
\Longrightarrow({\rm AEC})_{\rm unfr}
\Longrightarrow\text{unframed proper space},\\
\text{unframed proper space}+({\rm Raw\text{-}DF\text{-}IIT})
+({\rm FRCD})+({\rm KFF})
\Longrightarrow({\rm RCD})_{\rm fppf},\\
\text{unframed proper space}+({\rm RCD})_{\rm fppf}
+({\rm TDC\text{-}Ext})\Longrightarrow({\rm TDC})
\Longrightarrow({\rm TCG})_\Sigma.
\end{gathered}
\tag{5.5}
$$

Here 157a, Proposition 10.1 proves $({\rm BCP})$ unconditionally for explicit Mumford charts.
Its exhaustive $({\rm AEC})$, conductor-and-nilpotent $({\rm RCD})$, and global
theta--determinant $({\rm TDC})$ statements are conditional on the antecedents assigned to
them in its exported interface; $({\rm TDC})$ is exactly 157a, Conditional Theorem 15.2.
In particular the determinant calculation does not prove $({\rm TDC\text{-}Ext})$. These
dependencies should not be repeated as unrelated seed blockers, and none follows merely from
a completed chart.

Books 110--111 change only the availability of the rank-one cusp compactification. They do
not prove $({\rm R1\text{-}FTJ})$, arbitrary-$Z$ joining and avoidance, or the stable
connecting-slice consequence $({\rm ICS})$. The exact $({\rm R1\text{-}FTJ})$ interface is
the supplied-model antecedent of 157a, Section 17.1: after base change to the complete DVR
$R$ and passage to the selected fine component, one must supply a smooth projective
finite-type model $\overline{\mathcal Y}/R$ with geometrically connected fibers such that

1. its generic fiber is $Y$ and it contains $\mathcal Y^{\mathrm{good}}$;
2. the selected semistable point extends to an $R$-section whose completed boundary branch is
   the prescribed framed Tate--Mumford branch, with no enlargement of the completion field and
   no change in its valuation, Kummer, theta, polarization, or frame data; and
3. a relatively very ample line and every coefficient and PEL-frame descent isomorphism
   needed for the avoidance and slicing argument extend to the model.

This antecedent contains no assertion about $Z$; 157a proves arbitrary-$Z$ avoidance from the
supplied model. Its exact rank-one exported branch is

$$
\bigl(\text{Book 111, Theorem 13.1}\bigr)+({\rm R1\text{-}FTJ})
\Longrightarrow({\rm FTJ})_{v_0,Z}
\xrightarrow[\text{empty slice}]{\text{avoidance }(17.3)}
({\rm ICS})_{v_0,Z}.
\tag{5.6}
$$

Thus rank one does not inherit the five higher-rank recognition, descent, and projectivity
antecedents, but it does retain the separate $({\rm R1\text{-}FTJ})$ supplied-model gap.

### 5.4 The conditional moving implication

For $d\geq2$, the five antecedents in (5.5) supply $({\rm TCG})_\Sigma$, and 157a,
Conditional Theorems 17.1--17.2 give the joining and stable slicing implications

$$
({\rm GCC})+({\rm Raw\text{-}DF\text{-}IIT})+({\rm FRCD})+({\rm KFF})
+({\rm TDC\text{-}Ext})
\Longrightarrow({\rm TCG})_\Sigma
\Longrightarrow
({\rm FTJ})_{v_0,Z}
\xrightarrow{k\ {\rm finite}}
({\rm ICS})_{v_0,Z}.
\tag{5.7}
$$

The higher-rank ICS step uses finite-field Bertini and therefore also requires the residue
field of the complete DVR to be finite; that condition holds for the local fields used here.

For $d=1$, the input is instead exactly (5.6): Book 111, Theorem 13.1 plus
$({\rm R1\text{-}FTJ})$. The arbitrary-$Z$ avoidance implication and the empty-slice ICS
conclusion are then proved by 157a; they are not part of the Book 111 import.

On the resulting relative curve the nonempty good special-fiber open supplies closed points
of allowed residue degree. Integral-open saturation then solves (5.3) in every sufficiently
large compatible degree. Synchronizing those degrees with the wholesale-repeatable and
flexible packets lets Book 154, Corollary 5.2E produce (5.1), with exactly one special
degree-one factor and all other factors good minimal.

This is a valid conditional theorem, not an existence theorem in the current repository. The
stronger claim that the good open contains a rational point is neither true in general nor
needed. A closed point of higher residue degree suffices.

This is still pre-specialization geometry. Book 154, Theorem 6.1 can select a global point only
after the local opens and one simultaneous moving presentation exist. It creates a field and a
moduli point; it does not create a lower automorphic localization, a level-changing edge, or a
bottom face. Those are post-specialization arithmetic assertions.

Consequently the unconditional construction stops at the paired local opens of Chapter 4. The
singleton moving presentation, and therefore every normal top built from it, remains
conditional in higher rank on $({\rm GCC})$, $({\rm Raw\text{-}DF\text{-}IIT})$,
$({\rm FRCD})$, $({\rm KFF})$, and $({\rm TDC\text{-}Ext})$ through (5.5) and (5.7),
and in rank one on the separate $({\rm R1\text{-}FTJ})$ antecedent through (5.6). Book 111 source-closes neither rank-one
arbitrary-$Z$ avoidance nor ICS.

## 6. The conditional normal top and raw carrier

### 6.1 Normal-closure avoidance

Assume for this chapter that the singleton moving presentation has been externally supplied.
To control its normal closure, retain the full Galois approximation datum of Book 155, Chapter
6, rather than applying ordinary Moret--Bailly approximation and taking a closure afterward.
Let $E_0$ be the generic Galois field of that datum and let $C$ be the algebraic closure of the
rational base inside $E_0$. Constant-field disjointness from the avoidance field $D$ is forced
by split certificate primes; Book 158, Lemma 8.1 is the exact split-certificate argument.

Choose Frobenius conjugacy classes which normally generate
$\operatorname{Gal}(D/\mathbf Q)$, choose large good primes with those classes, and require
the moving fiber to split at them. Every certificate prime then splits in $C$. Hence every
chosen normal generator maps trivially to
$\operatorname{Gal}(C\cap D/\mathbf Q)$, giving

$$
C\cap D=\mathbf Q.
\tag{6.1}
$$

The order of choices is essential: $D$ and the certificate primes are fixed before the moving
presentation, and the constant field is formed only afterward.

### 6.2 The conditional normal top

Book 155, Theorems 7.1 and 8.1 specialize the supplied geometrically connected Galois cover,
its local homomorphisms, and its avoidance condition simultaneously. In applications an
independent geometrically connected ordered-root torsor can be included in the datum before
specialization. Conditional on the moving presentation and that Galois datum, this produces a
finite totally real Galois field

$$
M/\mathbf Q
\tag{6.2}
$$

of even degree, disjoint from $D$, in which $2$, $3$, $\ell$, and the certificate primes split
completely. Taking the point field to be the top makes any upward solvable bridge vacuous.

The local packets were imposed before passage to the top, so each completion above a
controlled rational prime has the assigned paired behavior. Disjointness preserves the two
absolute-irreducibility conditions. This is a conditional field construction from (5.1); it
cannot be counted among the unconditional outputs of this book.

The specialization produces an abelian variety $A/M$ with the prescribed local frames and
geometric reduction types. It does not put the residual dihedral eigensystem on any exact lower
automorphic face. The dihedral packet itself was independently constructed before
specialization by Book 178, Theorem 4.2 and Lemma 4.3. Its occurrence on the lower faces needed
for lifting, and every comparison from those faces to the specialized Tate point, belong to the
post-specialization arithmetic ledger of Chapter 7.

### 6.3 The dyadic raw-carrier boundary

Even after the normal top is supplied, field control does not produce an automorphic carrier.
At each dyadic place the auxiliary Tate module has special monodromy while its residual
dihedral datum is lower level. If the selected auxiliary route passes through a basic one-split
raw signed-special curve row, it must supply the relevant integral carrier comparison.

Book 122, Proposition 10.2 constructs an exact split dyadic unitary parahoric PEL source. The
direct common-norm one-split PEL realization is unavailable in degree greater than one. To use
the unitary source as the raw basic carrier, Book 122, Section 10.4 requires finite locally
free comparison squares

$$
\begin{array}{ccc}
\mathscr Y_I&\longrightarrow&\mathscr X_I\\
\downarrow&&\downarrow\\
\mathscr Y_0&\longrightarrow&\mathscr X_0
\end{array}
\tag{6.3}
$$

for both degeneracy routes, induced generically by the connected common-adjoint fiber product.
They must retain effective unramified component descent and carry completed node parameters by

$$
x\longmapsto ax',
\qquad
y\longmapsto a^{-1}y',
\qquad a\in\mathcal O^\times.
\tag{6.4}
$$

Thus both expansion indices are one and both oriented branches are preserved. This is exactly
the comparison assumed in Book 122, Section 10.4; Proposition 10.3 proves the carrier transfer
conditionally on it. Equality of adjoint groups and rational Jacquet--Langlands transfer do
not prove its integral extension.

This Book 122 condition is an external prerequisite only for a route that uses this
unitary-to-basic dyadic raw-carrier switch. The direct normalization, routing, and
principal/ray rows of Book 122, Propositions 9.2--9.10 and Corollary 9.11 remain proved and
must not be relabelled as missing. Likewise, a route staying entirely on path-compatible
curves does not acquire a flagged node/definite comparison merely because another route uses
one.

## 7. The auxiliary-prime lifting ledger

### 7.1 The active set

Continue conditionally with a supplied normal top and specialization $A/M$. Let
$P_{\mathrm{aux}}$ be the set of places where the characteristic-zero auxiliary Tate module
$V_{\mathfrak q}(A)$ has more level than its residual dihedral automorphic datum. It contains:

1. every dyadic place, because the lower residual auxiliary representation is unramified
   while the Tate seed has nonzero monodromy;
2. every conjugate of the distinguished special place $v_0$;
3. every multiplicative place above $3$ used by the construction; and
4. every accidental auxiliary nonminimal place created by specialization.

The repaired good ordinary coefficient-prime place is absent. An unrepaired multiplicative
place above $\ell$ would be a fatal defect rather than a legitimate active edge.

Complete splitting repeats a controlled rational place over the full conjugate set. Hence
$P_{\mathrm{aux}}$ is genuinely a finite several-place set even before accidental bad
reduction is considered.

### 7.2 Conditional routed Ihara

For a constant-coefficient one-place edge, Book 139, Proposition 5.4 identifies the residual
kernel of the two degeneracy maps. Its congruence-continuous part is Eisenstein; the remaining
term is a routed noncongruence-character quotient. Proposition 14.2 and Theorem 14.1 give
saturation and freeness only under the localized family
$({\rm AC}^{\rm loc}_\ell)_{\mathscr R}$, equivalently the applicable
$({\rm AIH}_{\mathscr F})$, at every actual vertex, edge, permutation row, adjoint companion,
spectator tuple, and auxiliary shadow used later.

Strong approximation does not prove $({\rm AIH}_{\mathscr F})$. Nor does it prove the
centrality, perfect congruence-kernel--metaplectic pairing, local multiplier classification,
restricted-product globalization, or scalar injectivity which would imply it.

The lettered source 138a narrows this boundary substantially. Theorems 2.4--2.5 give exact
centrality, stem, and finite-abelian-continuity criteria; Proposition 2.4A gives the
power--commutator reduction; Propositions 3.1 and 3.2B and Theorem 3.3 give the compact and
relative transgression calculations; Propositions 5.1, 5.1B, 5.2, and 5.3 give the proved
finite-product and normalized-gluing statements; and Lemma 4.1 gives the scalar endpoint.
Subject to its separately isolated locally compact Pontryagin foundation
$({\rm FND}_{\rm PD})$, Lemma 5.0A supplies the root splitting used in the proposed local
route. Its Theorems 6.1, 6.2, and 7.1 remain conditional.

The unresolved arithmetic package owned by 138a is exactly its six required interfaces, in
the order stated in Section 5.5:

1. centrality of the reference congruence kernel $({\rm CEN}_\star)$;
2. the compact-to-adelic character pairing $({\rm PAIR}_\star)$, with the retained compact
   and diagonal adelic splittings compared;
3. the split and division local multiplier classification, normalization, and detection
   theorem $({\rm LOC}_n)$;
4. coherent compact-tail splitting and restricted-product reciprocity $({\rm PROD}_n)$;
5. construction and injectivity of the scalar character $({\rm SC}_n)$; and
6. torsion, or an adequate common-exponent theorem, $({\rm TOR})$ when the all-primary
   finite-kernel conclusion is desired.

The conditions $({\rm QRM}_m)$ and $({\rm PA}_m)$ are merely proposed sufficient routes:
the first would imply $({\rm CEN}_\star)$, while the second would imply the stem or the
corresponding odd-primary continuity property used by an ordinary compact-transgression
route. Neither is a necessary interface, and the retained-splitting route may instead prove
$({\rm PAIR}_\star)$ directly. The separate $({\rm FND}_{\rm PD})$ is foundational, not a
seventh arithmetic interface. For odd-primary Ihara, Theorem 6.1 requires
$({\rm PAIR}_\star)$ and $({\rm SC}_n)$ for odd $n$; the all-primary $({\rm TOR})$ conclusion
is stronger. These items are recorded once here and are not duplicated later as new seed
blockers.

Thus $({\rm AIH}_{\mathscr F})$ remains an independent arithmetic input. Any claim that the
congruence kernel has order at most two over every totally real field is conditional on 138a,
Theorem 6.2's full all-primary hypotheses.

### 7.3 The actual global cube

For each subset $J\subseteq P_{\mathrm{aux}}$, let $C_J^+$ be the primary integral carrier
with upper local condition at the places in $J$ and lower dihedral condition elsewhere. A
simultaneous route requires one actual cube

$$
C_{P_{\mathrm{aux}}}^+
=\{C_J^+,d_{J,v}\}_{J\subseteq P_{\mathrm{aux}},\ v\notin J}
\tag{7.1}
$$

and its strict adjoint cube $C_{P_{\mathrm{aux}}}^-$. Every face must use the actual routed
component and spectator level; every square must commute integrally with the declared Hecke
action and pairing. A list of independently chosen one-place carriers is not such a cube.

Book 176 constructs formal consequences from a supplied cube and isolates its missing
arithmetic inputs. Under its standing convention that $\ell$ is odd, the corrected lettered
source 175a leaves the formal cube architecture valid at greater resolution: Theorem 13.1
constructs the canonical torsion-free top and perfect adjoint from one actual cube, and
Theorems 16.1--16.2 give the all-component and pointed criteria. It does not construct the
arithmetic hypotheses of those criteria. Book 175 proves a conditional
scalar one-place comparison and patching result; it proves no generic or vexing several-place
theorem. Book 174 constructs many actual one-place type rows, but retains
$({\rm AIH}_{\mathscr F})$, the nonbanal quotient-new and primitive filtered-cofiber endpoints,
the application-specific support data, and any switched flagged-node equivalence required by a
chosen route.

After the one-place inputs and an actual common cube have been supplied, 175a locates the
remaining several-place arithmetic in the following order: nonunit mixed sum-primitivity at
two places and mixed higher Ihara vanishing for larger sets; integral routed two-face
comparisons and their higher coherence; relative product residue with its component and
branch-Smith Tor terms; and joint occurrence of the named global product component, including
simultaneous branch verification on the carrier where occurrence is asserted. Once that
carrier and its labels exist, 175a, Theorem 15.1 proves finite-set reciprocity; it is not a
fifth missing reciprocity theorem. The pointed route can bypass mixed exactness and product
residue only if joint occurrence is proved by a different direct argument.

When (7.1) realizes its dyadic faces through the unitary-to-basic raw switch, those faces also
depend on the comparison of Section 6.3. A different route must instead verify its own actual
dyadic carrier and edge hypotheses. In either case an actual cube for this Frey specialization
is not presently constructed.

### 7.4 The pointed carrier and occurrence

Suppose nevertheless that one actual cube and its strict adjoint have been supplied. After
all fixed characters are specialized to the final coefficient DVR, let

$$
Q_{P_{\mathrm{aux}}}=H^{|P_{\mathrm{aux}}|}
(C_{P_{\mathrm{aux}}}^+)
$$

and form the canonical torsion-free top

$$
Q_{P_{\mathrm{aux}}}^{\mathrm{tf}}
=Q_{P_{\mathrm{aux}}}/Q_{P_{\mathrm{aux}}}[\varpi^\infty].
\tag{7.2}
$$

Book 176, Proposition 8.2B proves that this is finite free over $\mathcal O$ and that the
adjoint kernel $K_{P_{\mathrm{aux}}}^-$ is its perfect dual. This formal construction does not
require mixed exactness. It must be performed after every nonflat character specialization.
The same construction is 175a, Theorem 13.1, and the same pointed criterion is its Theorem
16.2. Both begin with an actual cube and retain branch verification and occurrence as
arithmetic inputs; 175a, Theorem 15.1 supplies reciprocity once its carrier hypotheses hold.

Before finite-set reciprocity can be invoked, every generic packet factor of this one carrier
must be checked simultaneously for determinant, local component, ordered line or characters,
sign, monodromy, conductor, coefficient-prime finite-flat realization, and the primary--adjoint
normalization. Vertexwise labels do not prove labels on the top quotient.

Let $x$ be the auxiliary Tate-module point and $\Xi_x$ an irreducible product component
through it. The decisive pointed assertion is

$$
\mathfrak p_{\Xi_x}\in
\operatorname{Supp}_{R_q^{P_{\mathrm{aux}}}}
\left(Q_{P_{\mathrm{aux}}}^{\mathrm{tf}}\right).
\tag{7.3}
$$

This is weaker than support on every product component and stronger than support on every
one-place projection. Once simultaneous branch verification and (7.3) are proved, 175a,
Theorem 15.1 supplies carrier-specific finite-set reciprocity, and Book 176's pointed
annihilator argument puts the carrier annihilator inside $\ker x$ and makes $x$ automorphic.

Neither Book 174, Book 175, 175a, Book 176, nor Book 177 proves (7.3) for the
specialization-dependent Frey tuple. Book 177, Theorem 10.1 and Section 10.4 expressly retain
the actual cube, simultaneous generic branch verification, reciprocity, and joint occurrence. A chosen
characteristic-zero lift on each face cannot replace this one global support statement.

## 8. Certified target lowering

### 8.1 The target active set

Assume independently that the auxiliary-prime point has been proved automorphic. Book 178,
Proposition 11.1 then gives the cross-prime integral comparison, and Corollary 11.1A gives a
nonzero localization on the actual upper target-$\ell$ carrier. Write the resulting packet as
$\Pi_A$ and define

$$
P_{\mathrm{tar}}=\{x_1,\ldots,x_r\}
\tag{8.1}
$$

to be the places where $\Pi_A$ has more level than the exact minimal signed-special problem.
Dyadic places are absent because the final problem retains their signed-special condition.
Places above $\ell$ are absent only after the repaired finite-flat condition has been verified
on the target packet. Distinguished auxiliary special places and multiplicative places above
$3$ usually remain and must be lowered.

The auxiliary and target ledgers can overlap, but their edges are different. The first changes
a $q$-adic Tate module from a dihedral lower datum. The second changes an already automorphic
$\ell$-adic packet. Coefficient rings, local types, modules, and maximal ideals must not be
identified merely because the underlying finite place is the same.

### 8.2 The curve-only edge theorem

Order $P_{\mathrm{tar}}$ as in (8.1). A certified edge at $x_i$ consists of a current integral
path-compatible curve lattice, its adjoint companion, a current maximal ideal, and the exact
normalization and degeneracy maps from Iwahori to hyperspecial level. Book 140, Theorem 12.1
is a curve-only lowering theorem. Its hypotheses require:

1. routed abelian Ihara and primitive old-image saturation at the actual spectator level;
2. a non-Eisenstein adjoint-stable block and perfect residual adjoint pairing;
3. vanishing of the full residual monodromy operator;
4. vanishing of the localized component obstruction;
5. vanishing of the localized normalized-branch Smith obstruction;
6. exactly two normalized lower branches with no stabilizer or coefficient torsion; and
7. a nonzero block with no scalar, self-twist, vexing, or Eisenstein identification that
   invalidates the filtration argument.

The theorem does not construct these hypotheses for the Frey block. In particular its first
clause still depends on the conditional $({\rm AIH}_{\mathscr F})$ of Section 7.2.

The flagged superspecial-node equivalence of Book 140, Hypothesis 5.1 is not a hypothesis of
this curve-only theorem. The chosen path therefore remains on path-compatible curves. A route
which switches the graph lattice to a definite node carrier would need the full equivalence of
flagged node groupoids, including polarizations, levels, automorphisms, active flag, both
oriented branches, Frobenius, Hecke spans, and component routing. Book 174 confirms that this
classification remains conditional. It is deliberately unused here, not falsely declared
proved.

### 8.3 Component and branch-Smith torsion

The two torsion obstructions in Book 139 and Book 140 are distinct. Schematically, monodromy
factors as

$$
X\xrightarrow{q_\Gamma}X^\vee\longrightarrow L_0.
\tag{8.2}
$$

The cokernel of $q_\Gamma$ is the Neron component module. The cokernel of the second map is
the normalized-branch Smith correction. Either can kill a nonzero class modulo $\varpi$.

For example, multiplication by $\varpi$ in $q_\Gamma$ creates component torsion even when the
branch inclusion is primitive. Conversely, $q_\Gamma$ can be unimodular while multiplication
by $\varpi$ in $X^\vee\to L_0$ creates branch-Smith torsion. Perfect duality and zero residual
monodromy do not distinguish these failures.

No current source proves both vanishings on every successive Frey localization. Book 174
retains both modules and its boundary comparison $({\rm BCD}_v)$; it does not turn one into the
other. A signed Gram determinant records only the sum of elementary-divisor valuations when
multiplicity exceeds one and is not a blanket vanishing theorem.

### 8.4 Strict inter-edge localization

After lowering at $x_i$, the output lower block must be identified with the exact
$x_{i+1}$-new input. The identification must preserve:

- contraction to the common away-from-$x_i$ faithful Hecke order;
- every spectator Hecke and component operator;
- every local branch label and the coefficient-prime realization;
- the primary--companion pairing and adjoint convention; and
- the current primitive lattice, not merely its generic packet space.

The first edge changes the lattice, companion, faithful order, and spectator tuple. Clean
edges verified independently on the original upper carrier do not prove that the second edge
is applicable to the first output. Generic equality after inverting $\varpi$ and residual
coincidence of away-from-place eigenvalues are insufficient.

No current pre-181 theorem constructs these strict inter-edge identifications for the ordered
Frey path. Thus even after each isolated edge hypothesis is supplied, iteration remains an
additional application-specific verification.

There is an explicit several-place countermodel to the idea that pairwise paths assemble
automatically. Over a field $k$, put

$$
L=k^2\oplus k^2,
\quad
U=k^2\oplus0,
\quad
V=0\oplus k^2,
\quad
W=\{(x,x):x\in k^2\}.
\tag{8.3}
$$

The three planes are pairwise complementary. Form a three-cube whose top is $L$, whose three
codimension-one aggregate sources map as $U,V,W\hookrightarrow L$, and whose lower vertices
are zero, as in 175a, Section 7.6. Every original two-face is split and exact below its top
degree. The total three-cube nevertheless contains

$$
U\oplus V\oplus W\longrightarrow L,
\qquad (u,v,w)\longmapsto u+v+w,
\tag{8.4}
$$

whose kernel has dimension two. Thus all pairwise routes can be clean while the several-place
object has lower cohomology. In arithmetic language, pairwise certified paths on separately
chosen intermediate carriers do not produce one several-place certified path: one still needs
the iterated-new identifications, the mixed higher-Ihara vanishing, and the coherent common
carrier.

## 9. Conditional nonvanishing and final occurrence

### 9.1 Induction along a certified path

Assume for this chapter that $\Pi_A$, a path-compatible upper lattice $L_0$, and every edge
certificate of Chapter 8 have been supplied. The upper packet gives

$$
(L_0/\varpi)_{\mathfrak m_0}\ne0.
\tag{9.1}
$$

Upper nonvanishing and integral saturation alone do not imply a lower occurrence. Let
$\mathbb T=\mathcal O\times\mathcal O$, let

$$
U=\mathcal Oe_1\oplus\mathcal Oe_2,
\qquad
L=\mathcal Oe_1\hookrightarrow U,
\tag{9.1a}
$$

and let the two idempotents of $\mathbb T$ project onto the two summands of $U$, while $L$ is
supported only on the first factor. The inclusion is split and hence saturated. At the maximal
ideal belonging to the second factor,

$$
(U/\varpi)_{\mathfrak m_2}\simeq k,
\qquad
(L/\varpi)_{\mathfrak m_2}=0.
\tag{9.1b}
$$

The upper eigensystem simply lies outside the saturated old image. A lowering theorem needs
the monodromy filtration, duality, component and branch cleanliness, and the contraction of the
actual maximal ideal; saturation by itself supplies none of them.

At edge $x_i$, Book 140, Theorem 12.1 shows that contraction of the current
away-from-$x_i$ eigensystem occurs in the lower hyperspecial module. Choose a maximal ideal
$\mathfrak m_i$ above that contraction. Then

$$
(L_i/\varpi)_{\mathfrak m_i}\ne0.
\tag{9.2}
$$

Strict inter-edge localization makes this the exact input for $x_{i+1}$. Induction gives a
nonzero residual localization at the fully lowered level.

This argument needs only one current block at a time. It does not require simultaneous product
support. Conversely, writing the places in an order does not prove the edge certificates or
the strict re-identifications. Once those data exist, bottom nonvanishing is a conclusion of
the induction and is not a separate missing hypothesis.

### 9.2 The path-compatible carrier

Book 178, Corollary 11.1A obtains a nonzero upper localization on a compact one-split curve
carrier from a retained special place. That carrier can be ramified at the very finite place
used to satisfy the quaternionic parity condition. Book 140 cannot lower level at a place where
the quaternion algebra is ramified; its changing place must be split.

Therefore an upper occurrence on one compact curve does not automatically supply the entire
ordered lowering path. If the retained place must itself be removed, one needs a separate
path-compatible curve or an integral carrier comparison with a new primitive packet lattice.
Rational equality of almost-all Hecke polynomials does not identify those integral lattices.

This issue belongs to the strict path ledger. It is not repaired by the flagged-node theorem,
and it is not avoided by merely choosing a different characteristic-zero representative of
the same packet.

### 9.3 Rational transfer and a primitive lattice

Once the fully minimal curve localization has actually been constructed, Book 104, Theorems
9.1--9.2 supply the required rational Jacquet--Langlands transfers in their selected definite
and compact one-split ranges. They place the characteristic-zero packet in the corresponding
definite quaternion algebra. Intersect the rational packet subspace with the definite integral
automorphic module and saturate. A primitive vector then has nonzero reduction, so the
transferred minimal maximal ideal occurs in the definite module.

This last step is rational transfer followed by elementary lattice theory. Book 182, Section
4.4 records the same formal propagation and transfer argument, but is not used as a proof
source here. The step does not assert
an integral isomorphism between the curve and definite Hecke orders. It also cannot be moved
to the start of the path: transfer of an upper packet does not prove occurrence after lowering
or any of the component and Smith vanishings used along the way.

## 10. The bottom structural ledger

### 10.1 The minimal problem and maximal ideal

Let $S_M^{\mathrm{SP}}$ be the parallel-weight-two module for a totally definite quaternion
algebra over $M$. The candidate minimal maximal ideal $\mathfrak m^{\min}$ is obtained by
contracting the final path character through a declared common faithful Hecke algebra. It must
remain non-Eisenstein and retain the central character, determinant, component, and every
local-type label.

The represented minimal deformation problem has determinant $\chi_\ell|_{G_M}$, the named
signed-special schematic closure at every dyadic place, the selected coefficient-linear
finite-flat condition at every place above $\ell$, and the unramified condition at all other
finite places. Complete splitting identifies the dyadic and coefficient-prime local fields
with the original rational completions.

The required bottom occurrence is

$$
(S_M^{\mathrm{SP}})_{\mathfrak m^{\min}}/\varpi\ne0.
\tag{10.1}
$$

It is only the first item of the bottom ledger, not a substitute for the remaining structural
data.

### 10.2 Modules, pairings, and orders

The minimal module and every Taylor--Wiles auxiliary module must be finite free over
$\mathcal O$. Stabilizer control and diamond torsors must be effective at the actual levels.
Every primary and companion type lattice and every degeneracy map used in augmentation must
be saturated.

For every auxiliary set $Q$ there must be a perfect pairing

$$
\langle\ ,\ \rangle_Q:
M_Q\times M_Q^-\longrightarrow\mathcal O
\tag{10.2}
$$

with the prescribed inverse-double-coset adjoints and diamond inversion. Perfection only after
inverting $\varpi$ is insufficient for patched depth and exact coinvariants.

The faithful Hecke orders must be finite flat and generically reduced in the range required by
the minimal theorem. The acting image is the actual image on the localized module, not an
abstract polynomial algebra with the same spherical traces. Named local and diamond operators
belong to the order only after their construction has been proved.

### 10.3 Integral Galois attachment

There must be a branchwise integral representation

$$
\rho_{\mathbb T}:G_M\longrightarrow
\operatorname{GL}_2(\mathbb T_M^{\mathrm{SP}})
\tag{10.3}
$$

with determinant $\chi_\ell$, the exact prescribed central character and its invertible
operator $S_v$, and good arithmetic-Frobenius polynomial

$$
X^2-S_v^{-1}T_vX+q_vS_v^{-1}.
\tag{10.4}
$$

This is the arithmetic-Frobenius conversion of the Book 171 normalization, as recorded in
Book 171, equation (12.5). The $S_v$ factor is not discarded or silently set to one: its
eigenvalue remains the exact central character fixed on the automorphic module and is matched
with the determinant character on every branch.

It must factor through every represented local quotient on every Artinian specialization. At
dyadic places this includes the line, sign, and monodromy relation; at coefficient-prime
places it includes the integral finite-flat model. Density of good Frobenius traces cannot
reconstruct these bad-place factorizations.

The same attachment range is needed on every characteristic-zero branch of every auxiliary
module used by patching. Residual occurrence at minimal level does not manufacture an
auxiliary Hecke-valued representation.

### 10.4 Auxiliary augmentation without circularity

For each Taylor--Wiles set $Q$, the represented deformation ring must augment
scheme-theoretically to the exact minimal problem. Primary and companion coinvariants must
recover the minimal lattices without finite index, and the perfect pairing must descend to
the minimal pairing. Named Hecke and diamond actions must commute with these maps, and the
named Hecke operators must specialize onto the full faithful minimal image.

Book 173 uses precisely this clean structural ledger. The represented-ring and module
augmentations are inputs to patching. A separate isomorphism between an auxiliary faithful
acting image modulo augmentation and the minimal faithful image is not assumed: injectivity
of that acting-image map is derived only after patched faithfulness. Importing it into the
seed would be circular.

Books 171--173 describe the ledger and prove the minimal comparison from it. They do not
construct the ledger at the final contracted Frey maximal ideal. Rational transfer and a
primitive residual vector prove neither integral local--global compatibility nor the whole
auxiliary family. These items must be verified before the seed is declared.

## 11. The exact seed contract

### 11.1 The packaged datum

An exact controlled signed-special seed is a tuple

$$
\mathscr S_{\mathrm{SP}}=
(M,\Gamma,\bar\rho_M,\delta,
\mathcal D_M^{\mathrm{SP}},
S_M^{\mathrm{SP}},\mathfrak m^{\min},
\{M_Q,M_Q^-\}_Q,
\{\langle\ ,\ \rangle_Q\}_Q,
\mathbb T_M^{\mathrm{SP}},
\rho_{\mathbb T},
\{\operatorname{aug}_Q\}_Q).
\tag{11.1}
$$

Here $\Gamma$ is the construction certificate recording the normal top, avoidance field,
split certificate primes, local decomposition maps, and all contractions of faithful Hecke
orders. It is retained for later controlled uses but can be forgotten at the minimal seed
interface.

The tuple must satisfy:

1. $M/\mathbf Q$ is finite, totally real, Galois, and of even degree;
2. $2$, $3$, and $\ell$ split completely in $M$;
3. $M$ is disjoint from the full avoidance field, preserving both absolute-irreducibility
   conditions;
4. $\delta=\chi_\ell|_{G_M}$;
5. $\mathcal D_M^{\mathrm{SP}}$ is the exact represented minimal problem of Section 10.1;
6. the minimal definite localization is nonzero modulo $\varpi$; and
7. the modules, pairings, faithful orders, Galois attachment, and augmentations satisfy
   Sections 10.2--10.4.

### 11.2 The required theorem

The reusable pre-181 theorem sought by this volume is the following.

**Required theorem $({\rm Seed}_{\mathrm{SP}})$.** For every primitive Frey signed-special
residual datum of exponent $\ell\geq7$, there exist a finite totally real field
$F/\mathbf Q$ of even degree and an exact clean minimal automorphic datum such that:

1. $2$ and $\ell$ split completely in $F$, and both
   $\bar\rho|_{G_F}$ and $\bar\rho|_{G_{F(\zeta_\ell)}}$ are absolutely irreducible;
2. the represented problem has determinant $\chi_\ell|_{G_F}$, the inherited named
   signed-special schematic closure at every place above $2$, including line, sign, and
   monodromy relation, the selected coefficient-linear finite-flat condition at every place
   above $\ell$, and the unramified condition elsewhere;
3. the residual representation occurs in a nonzero non-Eisenstein localized
   parallel-weight-two definite-quaternionic module with those exact integral local factors;
   and
4. the minimal and auxiliary modules are finite free, have effective stabilizer and
   diamond-torsor control, saturated types and degeneracy maps, perfect primary--companion
   pairings, generically reduced faithful Hecke orders, branchwise integral Galois attachment,
   exact represented-ring and module augmentation, and named-operator surjectivity onto the
   full faithful minimal image.

The controlled construction is designed to take $F=M$. The Galois normal-top, split-three,
and certificate data strengthen the construction record but can be forgotten at the minimal
interface.

This required theorem is not established in the current repository. It fixes the exact
contract and must not be quoted as an existence result.

### 11.3 What is deliberately absent

The seed does not contain a chosen characteristic-zero lift of $\bar\rho$, a compatible
family, finite flatness of the global minimal deformation ring, or an automorphy descent to
the rational base. Those are later constructions. Adding them here would change the topic
from a reusable residual seed into post-seed chosen-lift material and would invite circular
use of a downstream conclusion.

The seed also does not assume injectivity of auxiliary acting-image augmentation. It contains
the represented and module data which allow patching to prove faithfulness. Nor does it
replace the exact local factors by equality of good-prime traces.

## 12. Construction boundary

### 12.1 The exact first blocker chain

The unconditional construction reaches the global Frey datum, fixes the good
coefficient-prime seed, chooses $q$ from its Frobenius polynomial, and only then constructs the
corrected dihedral residual representation and paired local opens of Chapters 2--4. It does
not reach the singleton moving presentation. The exact higher-rank blocker chain exported by
the live 157a is

$$
\begin{array}{c}
\text{paired local semistable and good opens}\\
\Downarrow\\
\text{explicit homogenized Mumford charts, fan, and BCP}\\
\Downarrow\\
\boxed{({\rm GCC})}\\
\Downarrow\\
\boxed{({\rm Raw\text{-}DF\text{-}IIT})_{d\geq2}}\\
\Downarrow\\
({\rm IIT})_{\rm unfr}\Longrightarrow({\rm MPE})_{\rm unfr},\qquad
({\rm AEC})_{\rm unfr}\Longrightarrow\text{unframed proper space}\\
\Downarrow\\
\text{unframed proper space}+({\rm Raw\text{-}DF\text{-}IIT})
+\boxed{({\rm FRCD})}+\boxed{({\rm KFF})}
\Longrightarrow({\rm RCD})_{\rm fppf}\\
\Downarrow\\
\text{unframed proper space}+({\rm RCD})_{\rm fppf}
+\boxed{({\rm TDC\text{-}Ext})}
\Longrightarrow({\rm TDC})\Longrightarrow({\rm TCG})_\Sigma\\
\Downarrow\\
({\rm FTJ})_{v_0,Z}
\xrightarrow{k\ {\rm finite}}({\rm ICS})_{v_0,Z}\\
\Downarrow\\
\text{Book 154 singleton common moving presentation}\\
\Downarrow\\
\text{Book 155 Galois specialization and controlled normal top}.
\end{array}
\tag{12.1a}
$$

The rank-one branch has a different first unsupported input:

$$
\begin{array}{c}
\text{paired local semistable and good opens}\\
\Downarrow\\
\text{Book 111, Theorem 13.1 global rank-one compactification}\\
\Downarrow\\
\boxed{({\rm R1\text{-}FTJ})}\\
\Downarrow\\
({\rm FTJ})_{v_0,Z}
\xrightarrow[\text{empty slice}]{\text{157a avoidance }(17.3)}
({\rm ICS})_{v_0,Z}\\
\Downarrow\\
\text{Book 154 singleton common moving presentation}\\
\Downarrow\\
\text{Book 155 Galois specialization and controlled normal top}.
\end{array}
\tag{12.1b}
$$

The first unsupported arrow for arbitrary geometric objects is $({\rm GCC})$, 157a,
Hypothesis 3.1. For $d\geq2$, Raw-DF-IIT, Hypothesis 7.1, is the next recognition gate; formula
(5.4) shows one reason it cannot be deduced from labelled reduction, flatness, a grading, or an
externally imposed strict chart. FRCD and KFF are independent later gates: a root over-lattice
does not choose coherent conductor roots, and finite normalization need not be finite flat.
Proposition 10.1 already proves bounded conductor presentation for explicit Mumford charts, so
$({\rm BCP})$ is not another primitive gap. TDC-Ext is the later projectivity gate: the
determinant calculation alone proves neither extension and quasi-finiteness of the structured
Hilbert morphism nor the exact Plucker-line identity. The five antecedents and every
conditional arrow
in (12.1a) are assigned exactly by 157a, equation (17.13). Book 111, Theorem 13.1 supplies
only its stated rank-one compactification. It does not supply $({\rm R1\text{-}FTJ})$ or
close arbitrary-$Z$ FTJ or ICS; those dependencies are exactly (12.1b).

Book 154, Corollary 5.2E consumes the joining/saturation conclusion together with the stated
repeatability and degree-compatibility checks. Book 155, Theorems 7.1 and 8.1 then consume a
full Galois approximation datum. Neither theorem creates an automorphic face. Thus the actual
moving theorem inherits the five 157a antecedents in higher rank and $({\rm R1\text{-}FTJ})$
in rank one, and the controlled normal top is only a conditional output. The five higher-rank
antecedents are one owned geometric package, not five new controlled-seed topics.

### 12.2 Conditional downstream blocker chains

Assume the applicable geometric chain (12.1a) or (12.1b) and the specialized $A/M$ have been
supplied. The post-specialization arithmetic must then proceed in the following order.

First, the independently automorphic dihedral datum must occur on every actual lower face used
to compare with $V_{\mathfrak q}(A)$. The constant-coefficient input is the routed localized
Ihara family of Section 7.2. Its primitive missing arithmetic is owned by 138a and consists of
the six required interfaces $({\rm CEN}_\star)$, $({\rm PAIR}_\star)$,
$({\rm LOC}_n)$, $({\rm PROD}_n)$, $({\rm SC}_n)$, and $({\rm TOR})$ in their applicable
ranges; it is not repeated as six new seed hypotheses. The proposed $({\rm QRM}_m)$ and
$({\rm PA}_m)$ routes and the separate $({\rm FND}_{\rm PD})$ foundation do not change that
interface count. Type and node
conditions are additional only when the selected route uses them. In particular, the
unitary-to-basic dyadic raw-carrier route has the external prerequisite

$$
\text{unitary dyadic PEL source}
\longrightarrow
\boxed{\text{Book 122, Section 10.4 comparison (10.5)}}
\longrightarrow
\text{basic routed raw SP faces}.
\tag{12.2}
$$

Book 122, Proposition 10.2 proves the source and Proposition 10.3 proves the transfer from
(10.5); Propositions 9.2--9.10 and Corollary 9.11 remain unconditional on their actual rows.
For nonbanal typed rows, the quotient-new injection, primitive filtered-cofiber comparison,
$({\rm BCD}_v)$ support comparison, and any switched flagged-node equivalence required by Book
174 are likewise external route prerequisites. They are not consequences of Moret--Bailly and
are not imposed on a curve-only route which does not use them.

Second, the auxiliary active set requires either a certified ordered chain whose current
output is the next input, or one actual several-place cube and strict adjoint. In the genuine
several-place route, 175a owns the remaining arithmetic in proof order:

$$
\begin{array}{c}
\text{actual common }P_{\mathrm{aux}}\text{-cube}\\
\Downarrow\\
\boxed{\text{nonunit mixed primitivity and higher Ihara}}\\
\Downarrow\\
\boxed{\text{routed two-face comparisons and higher coherence}}\\
\Downarrow\\
\boxed{\text{relative product residue with component and branch Tor}}\\
\Downarrow\\
\boxed{\text{joint occurrence through the Tate point, with simultaneous branch labels}}\\
\Downarrow\\
\text{175a finite-set reciprocity and auxiliary automorphy}.
\end{array}
\tag{12.3}
$$

For the pointed route, 175a, Theorems 13.1 and 16.2 and Book 176, Proposition 8.2B and Theorem
9.2 permit the shorter implication

$$
\text{actual specialized cube}
\longrightarrow
Q_{P_{\mathrm{aux}}}^{\mathrm{tf}}
\longrightarrow
\boxed{\text{joint pointed occurrence with simultaneous labels}}
\longrightarrow
\text{175a finite-set reciprocity and upper auxiliary automorphy}.
\tag{12.4}
$$

This shorter route bypasses mixed exactness and product residue only if pointed occurrence is
proved directly. Separate one-place supports do not prove it. Reciprocity here is the
source-closed 175a theorem, not another arithmetic blocker. Once upper auxiliary automorphy is
known, Book 178, Proposition 11.1 and Corollary 11.1A source-close the cross-prime comparison
and give a nonzero upper target localization.

Third, target lowering begins on a path-compatible compact curve carrier split at every member
of $P_{\mathrm{tar}}$, with a primitive upper packet lattice. Each current edge must satisfy
Book 140, Theorem 12.1, including the already-owned Ihara input, residual duality, full residual
monodromy vanishing, independent component and branch-Smith cleanliness, exact two-branch
normalization, and the nonexceptional nonzero block condition. Its output must be identified
integrally with the next current new block. Thus

$$
\begin{array}{c}
\text{nonzero path-compatible upper target localization}\\
\Downarrow\\
\boxed{\text{every current Book 140 edge certificate}}\\
\Downarrow\\
\boxed{\text{strict current-block identification at every next edge}}\\
\Downarrow\\
\text{nonzero bottom minimal SP curve localization}\\
\Downarrow\\
\text{primitive rational transfer to the definite minimal SP localization}.
\end{array}
\tag{12.5}
$$

Bottom nonvanishing is the conclusion of this certified induction, not another hypothesis.
The countermodel (9.1a)--(9.1b) shows why upper nonvanishing and saturation without the edge
theorem do not suffice; the three-cube (8.3)--(8.4) shows why pairwise paths do not create a
several-place certificate.

Finally, the nonzero definite localization must carry the full Book 173 structural ledger:

$$
\begin{array}{c}
\text{nonzero definite minimal SP localization}\\
\Downarrow\\
\boxed{\text{complete Book 173 structural ledger at that ideal}}.
\end{array}
\tag{12.6}
$$

This last box means finite-free minimal and auxiliary modules, saturated types and degeneracy
maps, perfect primary--companion pairings, effective diamond torsors, generically reduced
faithful Hecke orders, branchwise integral Galois attachment, and exact represented-ring and
module augmentation. Books 171--173 prove the minimal comparison from such a ledger; they do
not construct it at the contracted Frey ideal.

If an argument additionally requires ambient rational semisimplicity of carrier Jacobians,
061a first places the ramified Neron/formal-identity cotangent base-change assertion
$({\rm SHB})$ at the start of its Faltings-height route. Only after SHB may its restricted
$({\rm Tor})_{\mathscr C,N}$, $({\rm HT})_{\mathscr C,N}$, and
$({\rm SlopeFJ})_{\mathscr C,N}$ packages be used as a sufficient route to
$({\rm CMH})_{\mathscr C,N}$. Alternatively, a direct proof of CMH bypasses SHB and all three
packages. From CMH, Theorem 5.13 supplies carrier semisimplicity, while Theorems 5.7 and 5.12
and Proposition 5.8, Corollary 5.9, and Proposition 5.10 source-close the
height-to-finiteness, finite-isogeny-class, stable-lattice, and Tate-semisimplicity
implications. Neither SHB nor either route to CMH is proved. This is an external carrier
prerequisite, not a new step between upper and bottom residual occurrence and not a duplicate
controlled-seed topic.

### 12.3 Source ledger and verdict

The corpus and locator audit gives the following exact effect. A lettered source is listed as a
proved supplement, not as a numbered catalog dependency.

| source | usable conclusion | retained boundary |
|---|---|---|
| Book 154, Corollary 5.2E and Theorems 6.1, 12.1 | singleton moving from a verified saturation package, then arithmetic approximation | does not construct the saturation package, a Galois top, or an automorphic face |
| Book 155, Theorems 7.1 and 8.1 | Galois-refined, totally real specialization with closure-level avoidance | begins with a full Galois approximation datum |
| Book 157, Proposition 8.4B, Lemma 8.4B.1, Theorem 13.1, Corollary 13.2, and Sections 13.2A--13.2B | ordinary coefficient-prime repair, paired local opens, finite Kummer normalization, fans, trait comparison, and conditional slicing handoff | does not prove exhaustive cusp classification or deformation recognition, Kummer finite flatness, or the singleton moving theorem |
| Book 158, Lemma 8.1 | split-certificate control of the generic constant field | starts from the certificate fibers in one moving presentation |
| 157a, Theorem 2.1, Hypotheses 3.1, 7.1, 9.1--9.2, and 15.1, Theorem 4.2, Chapters 6 and 9, Propositions 10.1 and 11.1, Conditional Theorems 7.2, 11.2, 12.1, and 15.2, Theorems 16.1 and 17.1--17.2, and Sections 17.1 and 17.5 | Raynaud/fan results, explicit homogenized Mumford and finite Kummer-normalized charts, BCP, and the exact two-branch conditional compactification/joining interface | for $d\geq2$, GCC, Raw-DF-IIT, FRCD, KFF, and TDC-Ext remain unproved, with finite residue field also required for the higher-rank ICS Bertini step; for $d=1$, Book 111 supplies only its stated compactification and R1-FTJ remains the separate supplied-model antecedent before 157a proves arbitrary-$Z$ avoidance and empty-slice ICS |
| Book 178, Theorems 2.1 and 4.2, Lemmas 4.1A and 4.3, Proposition 11.1, and Corollary 11.1A | simultaneous coefficients, rational-base ray compatibility, protected dihedral branches, cross-prime comparison, and nonzero upper target occurrence | actual post-specialization auxiliary lifting remains conditional |
| Book 104, Theorems 9.1--9.2 | rational selected transfer between split, compact one-split, and totally definite packets | identifies no integral lattices or congruence indices |
| 138a, Theorems 2.4--2.5 and 3.3, Proposition 2.4A, Propositions 3.1 and 3.2B, Lemma 4.1, Lemma 5.0A, Propositions 5.1, 5.1B, 5.2--5.3, and conditional Theorems 6.1--6.2 and 7.1 | exact cohomological, power--commutator, compact-transgression, finite-product, normalized-gluing, scalar, and conditional Ihara reductions | CEN/PAIR/LOC/PROD/SC/TOR are the six required interfaces; QRM/PA are proposed sufficient routes, and Lemma 5.0A separately assumes $({\rm FND}_{\rm PD})$; it is not a catalog node |
| Book 122, Propositions 9.2--9.10, Corollary 9.11, and Propositions 10.2--10.3 | actual principal/ray rows and a dyadic unitary source; conditional raw-carrier transfer | comparison (10.5) is external only when that dyadic switch is used |
| Book 139, Proposition 5.4, Proposition 14.2, and Theorem 14.1; Book 140, Theorem 12.1 | exact routed kernel and conditional one-place saturation, component control, and level lowering | retain localized Ihara and the current component/branch/duality hypotheses |
| Book 174, Theorem 11.1 | actual conditional typed one-place complex, strict ray, augmentation, and support architecture | retains nonbanal quotient/cofiber, $({\rm BCD}_v)$, Ihara, and route-specific switched-node inputs |
| 175a, Theorems 2.1, 6.1, 8.1, 11.1, 12.1--12.2, 13.1, 15.1, and 16.1--16.2 | the corrected formal odd-$\ell$ cube architecture, canonical pointed carrier, reciprocity on an already verified joint carrier, and all-component/pointed criteria | retains nonunit mixed/higher Ihara, routed two-face and higher coherence, product residue with component/branch Tor, and joint component occurrence with simultaneous branch verification; it is not a catalog node |
| Book 176, Propositions 8.2--8.3 and Theorems 9.1--9.2 | formal several-place reductions, pointed carrier, joint ray quotient, and annihilator implication | retains the actual arithmetic cube and the same all-component or pointed gates |
| Book 170, Theorem 16.1; Book 171, equation (12.5) and Theorem 13.1; Book 172, Theorem 1.1; Book 173, Theorems 1.1 and 10.1 | arithmetic-Frobenius conversion with the exact central operator, reciprocity on an already verified carrier, and minimal comparison from an exact clean datum | do not construct the carrier or bottom structural ledger at the Frey ideal |
| 061a, Section 1.2, Theorem 5.1, Proposition 5.3, Theorem 5.7, Proposition 5.8, Corollary 5.9, Proposition 5.10, and Theorems 5.12--5.13 | one semistable field, conditional stable-height field-independence, and the source-closed CMH-to-finiteness/stable-lattice/semisimplicity chain | SHB is the first height-route gate; afterward Tor/HT/SlopeFJ are a sufficient route to CMH, while direct CMH bypasses them; none of those antecedents is proved, and 061a is not a catalog node |
| Book 182, Lemmas 2.1--2.2 and Sections 4.2--4.4 | later source-closed checks of the coefficient-prime repair, split SP preservation, ledger separation, and certified-path propagation | downstream diagnostic only; no post-180 result is used to construct the seed |

This reconciles with `THEOREM_GAP_INVENTORY.md` by ownership rather than duplication. Its
merged `controlled-residual-automorphic-seed` findings remain the umbrella diagnosis. The five
higher-rank 157a antecedents and the rank-one R1-FTJ branch refine the already merged
controlled-seed local-geometry item; the 138a
interfaces belong to `localized-odd-primary-congruence-vanishing`; and the 175a gates belong
to `several-prime-derived-level-change`. The 061a SHB-first chain belongs to
`height-geometric-interfaces` and remains an external carrier-semisimplicity antecedent. None
is added here as a new controlled-seed topic. The proposed QRM/PA routes,
$({\rm FND}_{\rm PD})$, the proved explicit Mumford/BCP constructions, and the proved 175a
formal consequences likewise do not create additional gap entries. The local foundational
library contains no theorem under the required interfaces or an equivalent automorphic,
toroidal-recognition, congruence--metaplectic, several-place-support, or carrier-height
formulation that closes them.

Accordingly $({\rm Seed}_{\mathrm{SP}})$ is not constructed. For arbitrary geometric cusp
objects the first blocker before the normal top is GCC; in higher rank Raw-DF-IIT follows it,
FRCD and KFF enter at the framed conductor and fppf-descent stages, and TDC-Ext enters at
projectivity before TDC and TCG. In rank one the first joining blocker is R1-FTJ after the
Book 111 compactification; Book 111 itself does not close
the arbitrary-$Z$ FTJ/ICS branch. Conditional on the applicable moving package, the next
blockers in proof order are the 138a-owned localized Ihara interfaces and any route-specific
type/node prerequisites, the odd-$\ell$ 175a-owned auxiliary nonunit mixed/higher-Ihara,
routed-coherence, product-residue, and joint-occurrence package (or its pointed joint-occurrence
alternative), the path-compatible target carrier with every current Book 140 certificate and
strict inter-edge identification, and the bottom Book 173 structural ledger. If carrier
semisimplicity is additionally required, 061a begins with SHB and then uses Tor/HT/SlopeFJ to
reach CMH, unless CMH is proved directly. A certified target path already proves bottom
nonvanishing, so that conclusion is not counted again. Book 182 is cited only as a downstream
diagnostic; no theorem after Book 180 is used as a premise. The mathematically correct endpoint
is the exact seed contract of Chapter 11, not an asserted residual automorphic seed.
