# The Minimal Totally-Real Deformation--Hecke Problem

## Contents

- [1. The comparison problem before patching](#1-the-comparison-problem-before-patching)
  - [1.1 Why two arithmetic constructions should meet](#11-why-two-arithmetic-constructions-should-meet)
  - [1.2 The exact endpoint](#12-the-exact-endpoint)
  - [1.3 Conventions](#13-conventions)
  - [1.4 Standing hypotheses](#14-standing-hypotheses)
- [2. The residual totally real datum](#2-the-residual-totally-real-datum)
  - [2.1 Fields, coefficients, and determinant](#21-fields-coefficients-and-determinant)
  - [2.2 Oddness and scalar endomorphisms](#22-oddness-and-scalar-endomorphisms)
  - [2.3 Residual automorphy](#23-residual-automorphy)
  - [2.4 Adequacy on the cyclotomic restriction](#24-adequacy-on-the-cyclotomic-restriction)
  - [2.5 The controlling set of places](#25-the-controlling-set-of-places)
- [3. Minimal local deformation conditions](#3-minimal-local-deformation-conditions)
  - [3.1 Minimality is a deformation condition](#31-minimality-is-a-deformation-condition)
  - [3.2 Places above the coefficient prime](#32-places-above-the-coefficient-prime)
  - [3.3 Unramified places away from the coefficient prime](#33-unramified-places-away-from-the-coefficient-prime)
  - [3.4 Fixed prime-to-coefficient inertia](#34-fixed-prime-to-coefficient-inertia)
  - [3.5 Minimal special places](#35-minimal-special-places)
  - [3.6 Real places](#36-real-places)
  - [3.7 The local hypothesis ledger](#37-the-local-hypothesis-ledger)
- [4. Local rings, tangents, and determinant data](#4-local-rings-tangents-and-determinant-data)
  - [4.1 Why frames are retained locally](#41-why-frames-are-retained-locally)
  - [4.2 Fixed-determinant tangent spaces](#42-fixed-determinant-tangent-spaces)
  - [4.3 The coefficient-prime calculation](#43-the-coefficient-prime-calculation)
  - [4.4 Neutrality away from the coefficient prime](#44-neutrality-away-from-the-coefficient-prime)
  - [4.5 The completed local base](#45-the-completed-local-base)
- [5. The global minimal deformation ring](#5-the-global-minimal-deformation-ring)
  - [5.1 The functor and its universal ring](#51-the-functor-and-its-universal-ring)
  - [5.2 The framed fiber product](#52-the-framed-fiber-product)
  - [5.3 The primal Selmer group](#53-the-primal-selmer-group)
  - [5.4 The dual Selmer group](#54-the-dual-selmer-group)
  - [5.5 The balanced totally real formula](#55-the-balanced-totally-real-formula)
  - [5.6 Presentations and the two relation counts](#56-presentations-and-the-two-relation-counts)
- [6. Definite-quaternion automorphic data](#6-definite-quaternion-automorphic-data)
  - [6.1 Choosing the inner form](#61-choosing-the-inner-form)
  - [6.2 Level, weight, and local type lattices](#62-level-weight-and-local-type-lattices)
  - [6.3 The finite automorphic module](#63-the-finite-automorphic-module)
  - [6.4 The residual maximal ideal](#64-the-residual-maximal-ideal)
  - [6.5 Exact minimal matching](#65-exact-minimal-matching)
- [7. Hecke algebras, pairings, and branches](#7-hecke-algebras-pairings-and-branches)
  - [7.1 The faithful Hecke image](#71-the-faithful-hecke-image)
  - [7.2 Localization and finite flatness](#72-localization-and-finite-flatness)
  - [7.3 Primary and companion modules](#73-primary-and-companion-modules)
  - [7.4 Perfect pairings and adjoints](#74-perfect-pairings-and-adjoints)
  - [7.5 Generic branches and reducedness](#75-generic-branches-and-reducedness)
- [8. The Hecke-valued representation and the map from deformations](#8-the-hecke-valued-representation-and-the-map-from-deformations)
  - [8.1 Branchwise representations](#81-branchwise-representations)
  - [8.2 Descent to the localized order](#82-descent-to-the-localized-order)
  - [8.3 Verification of the minimal local conditions](#83-verification-of-the-minimal-local-conditions)
  - [8.4 Construction and surjectivity of the comparison map](#84-construction-and-surjectivity-of-the-comparison-map)
  - [8.5 What the comparison map does not prove](#85-what-the-comparison-map-does-not-prove)
- [9. Augmentations and congruence modules](#9-augmentations-and-congruence-modules)
  - [9.1 Selecting an integral automorphic branch](#91-selecting-an-integral-automorphic-branch)
  - [9.2 Cotangent and congruence modules](#92-cotangent-and-congruence-modules)
  - [9.3 The pairing construction](#93-the-pairing-construction)
  - [9.4 Multiplicity and saturation](#94-multiplicity-and-saturation)
  - [9.5 The exact numerical inequalities](#95-the-exact-numerical-inequalities)
- [10. Determinant lines and the numerical bridge](#10-determinant-lines-and-the-numerical-bridge)
  - [10.1 The minimal Selmer complex](#101-the-minimal-selmer-complex)
  - [10.2 Its determinant line](#102-its-determinant-line)
  - [10.3 Local determinants and global transitivity](#103-local-determinants-and-global-transitivity)
  - [10.4 The automorphic determinant](#104-the-automorphic-determinant)
  - [10.5 What can be compared before patching](#105-what-can-be-compared-before-patching)
- [11. Exact Taylor--Wiles numerical data](#11-exact-taylor--wiles-numerical-data)
  - [11.1 The integer that auxiliary primes must address](#111-the-integer-that-auxiliary-primes-must-address)
  - [11.2 The shape of an admissible auxiliary prime](#112-the-shape-of-an-admissible-auxiliary-prime)
  - [11.3 Local auxiliary deformation rings](#113-local-auxiliary-deformation-rings)
  - [11.4 Diamond groups and augmentation ideals](#114-diamond-groups-and-augmentation-ideals)
  - [11.5 The generator--relation ledger](#115-the-generator--relation-ledger)
  - [11.6 Adequacy and the prime-five boundary](#116-adequacy-and-the-prime-five-boundary)
- [12. Coefficient changes and normalization checks](#12-coefficient-changes-and-normalization-checks)
  - [12.1 Extension of the coefficient DVR](#121-extension-of-the-coefficient-dvr)
  - [12.2 Determinant twists and Frobenius conventions](#122-determinant-twists-and-frobenius-conventions)
  - [12.3 Framed and unframed ledgers](#123-framed-and-unframed-ledgers)
  - [12.4 Failure tests](#124-failure-tests)
- [13. The complete minimal comparison package](#13-the-complete-minimal-comparison-package)
  - [13.1 Main construction theorem](#131-main-construction-theorem)
  - [13.2 Numerical theorem](#132-numerical-theorem)
  - [13.3 Dependency closure](#133-dependency-closure)
  - [13.4 Boundary with minimal patching](#134-boundary-with-minimal-patching)
- [14. Conclusion](#14-conclusion)
  - [14.1 The arithmetic object now in hand](#141-the-arithmetic-object-now-in-hand)

## 1. The comparison problem before patching

### 1.1 Why two arithmetic constructions should meet

There are two ways to organize the same congruence phenomenon. On the Galois side, one starts with a residual representation and asks for all lifts obeying specified local rules. The answer is a complete local ring. On the automorphic side, one starts with a finite integral space of definite-quaternion forms and records the commuting Hecke operators on it. The answer is a finite flat operator algebra. If the residual representation is automorphic and the local rules have been matched correctly, every automorphic eigenpacket in the chosen localization supplies a Galois lift. Universality should therefore give a map

$$
R^{\min}\longrightarrow \mathbb T^{\min}.
$$

The difficulty lies in the words “matched correctly.” Equality of conductors is not enough to identify integral deformation components. A rational local type does not determine an integral lattice. An abstract Hecke algebra need not act faithfully on the module under consideration. A family of characteristic-zero representations on separate generic branches need not descend to the order in which those branches meet. Even after the displayed map is constructed and proved surjective, its injectivity is a separate theorem.

This volume builds the comparison problem with every one of those interfaces visible. The aim is not yet to prove $R^{\min}=\mathbb T^{\min}$. The aim is to define the two sides, construct the surjection, place compatible pairings and augmentations on them, and compute the precise tangent, obstruction, determinant, and auxiliary-prime data needed for the later proof of equality.

### 1.2 The exact endpoint

The final object is a pointed diagram

$$
\begin{array}{ccc}
R^{\min}&\xrightarrow{\ \theta\ }&\mathbb T^{\min}\\
\lambda_R\searrow&&\swarrow\lambda_T\\
&\mathcal O&
\end{array}
$$

equipped with the following additional information:

1. a universal fixed-determinant minimal representation over $R^{\min}$;
2. a Hecke-valued representation over $\mathbb T^{\min}$ satisfying the same local conditions on every Artinian quotient;
3. a finite free, faithful automorphic module and its adjoint companion;
4. a balanced primal/dual Selmer calculation;
5. exact framed and unframed generator--relation ledgers;
6. augmentation cotangent and congruence modules;
7. determinant lines for the Selmer complex and the automorphic pairing complex;
8. the integer $q$ and the local one-variable data that a Taylor--Wiles system must supply.

The point of recording all eight items together is that later patching must not repair a mismatch introduced here. Patching can amplify compatible data; it cannot turn the wrong local component, determinant, Frobenius convention, or integral lattice into the right one.

### 1.3 Conventions

Let $F$ be a totally real number field. For a finite place $v$, write $q_v$ for the residue cardinality and $G_v=G_{F_v}$. We use geometric Frobenius $\Phi_v$. Thus an unramified weight-two representation attached to an eigenpacket has characteristic polynomial

$$
X^2-T_vX+q_vS_v.
\tag{1.1}
$$

The character $S_v$ records the central or component action. It is not silently replaced by $1$. Our coefficient ring $\mathcal O$ is the ring of integers in a finite extension $E/\mathbf Q_\ell$, with uniformizer $\varpi$ and finite residue field $k$. All completed tensor products are taken over $\mathcal O$ with the common residue field understood.

For a two-dimensional representation $V$, put

$$
\operatorname{ad}V=\operatorname{End}(V),\qquad
\operatorname{ad}^0V=\{a:\operatorname{tr}(a)=0\}.
$$

Because $\ell$ will be odd, scalar and trace-zero endomorphisms split. The determinant is fixed, so the deformation coefficient module is

$$
M=\operatorname{ad}^0\bar\rho,
\qquad M^*(1)\simeq M(1),
\tag{1.2}
$$

the latter identification using the trace pairing.

### 1.4 Standing hypotheses

The clean minimal problem considered throughout satisfies these hypotheses.

- The coefficient prime obeys $\ell\ge 7$.
- Every $F_v$ for $v\mid\ell$ is unramified over $\mathbf Q_\ell$.
- The representation $\bar\rho:G_F\to\operatorname{GL}_2(k)$ is continuous, absolutely irreducible, and totally odd.
- Its restriction to $G_{F(\zeta_\ell)}$ is absolutely irreducible.
- A continuous determinant lift $\delta:G_F\to\mathcal O^\times$ is fixed and agrees with the determinant of the automorphic packets under consideration.
- At coefficient-prime places the residual representation lies in the proved low-weight finite-flat range with weights $\{0,1\}$. The local determinant is the cyclotomic--central determinant covered by that theorem, or its transport by a fixed integral twist for which finite flatness and the determinant fiber have been proved.
- Away from $\ell$, every ramified place belongs to an unramified, fixed prime-to-$\ell$ finite-type, or clean minimal-special case whose represented local condition and neutral tangent calculation are known.
- The represented local conditions carry compatible complete and effective obstruction theories, and their local-condition complexes make the global Selmer complex perfect. These hypotheses are used for relation bounds and determinant lines, not merely for representability or tangent calculations.
- The residual system occurs in the selected parallel-weight-two definite-quaternion module, is non-Eisenstein, and every characteristic-zero branch in its localization lies in the established rank-two attachment and integral local-compatibility range.
- The localized generic Hecke algebra is reduced, and the selected integral module and all local type lattices satisfy the stated saturation, pairing, and stabilizer hypotheses.

Some conclusions below need fewer assumptions. We indicate that when useful. The uniform package retains the full list because its purpose is to be passed intact to minimal patching.

A first model is $F=\mathbf Q$. There is one real place and one coefficient-prime place, whose contributions are respectively $-1$ and $+1$. If every prime dividing the residual conductor carries a neutral minimal condition, the global defect is zero. This familiar case already contains every logical distinction of the general construction: the local finite-flat ring is framed, the global ring is unframed, and a definite quaternion algebra ramified at infinity must also be ramified at an odd number of finite places.

For a genuinely totally real example, take a real quadratic field in which $\ell$ is inert. There are two real places but only one place over $\ell$; its local degree is two. The cancellation is

$$
2-(1+1)=0,
$$

not a place-by-place pairing. If $\ell$ splits, there are instead two coefficient-prime places of degree one. This illustrates why the local formula uses $[F_v:\mathbf Q_\ell]$ rather than assigning contribution one to every $v\mid\ell$.

## 2. The residual totally real datum

### 2.1 Fields, coefficients, and determinant

Choose a finite set $S$ of places of $F$ containing all real places, all places above $\ell$, every place where $\bar\rho$ or $\delta$ ramifies, and every place used in the quaternion algebra, level, or type datum. The representation factors through

$$
G_{F,S}=\operatorname{Gal}(F_S/F),
$$

the Galois group of the maximal extension unramified outside the finite places in $S$.

The determinant is part of the deformation problem, not a consequence to be recovered from traces. We require

$$
\delta\bmod\varpi=\det\bar\rho,
\qquad
\delta(c_\tau)=-1
\tag{2.1}
$$

for every real embedding $\tau$ and associated complex conjugation $c_\tau$. In the cohomological normalization used here one typically has

$$
\delta=\chi_\ell^{-1}\eta,
\tag{2.2}
$$

where $\chi_\ell$ is normalized compatibly with geometric Frobenius and $\eta$ is the finite-order central-component character. Formula (2.2) is a normalization, not an additional freedom: the same $\eta$ must govern the central action $S_v$ on the automorphic module. In particular,

$$
\delta(\Phi_v)=q_vS_v
\tag{2.3}
$$

under the convention of (1.1).

The central factor cannot be erased. Two packets can have the same $T_v$ but central eigenvalues $s_v$ and $s_v'$. Their Frobenius traces agree, yet their determinants are $q_vs_v$ and $q_vs_v'$. They do not define points of the same fixed-determinant functor unless their central characters agree globally. Trace generation yields the desired target only because the determinant coefficients have already been fixed.

### 2.2 Oddness and scalar endomorphisms

Absolute irreducibility gives

$$
\operatorname{End}_{k[G_F]}(\bar\rho)=k,
\qquad H^0(F,M)=0.
\tag{2.4}
$$

This is the global Schur condition. It removes infinitesimal global conjugacies beyond scalars and makes the unframed fixed-determinant functor representable.

At a real place, $c_\tau^2=1$. Since $2$ is invertible in $k$ and $\det\bar\rho(c_\tau)=-1$, the residual space splits into a $+1$ and a $-1$ line. Conjugation on $M$ fixes the trace-zero diagonal line and negates the two off-diagonal lines. Hence

$$
h^0(F_\tau,M)=1,
\qquad H^1(F_\tau,M)=0.
\tag{2.5}
$$

The odd conjugacy class is rigid: the idempotents $(1\pm\rho(c_\tau))/2$ continue to have rank one in every lift. Nevertheless the invariant dimension in (2.5) contributes to the global Euler characteristic and must not be discarded.

We also impose

$$
H^0(F,M(1))=0.
\tag{2.6}
$$

This is the absence of a trace-zero cyclotomic self-twist. It does not follow from (2.4). It is exactly the global term needed for the balanced formula.

### 2.3 Residual automorphy

The phrase “$\bar\rho$ is automorphic” is too coarse for an integral comparison. We require an actual maximal ideal $\mathfrak m$ of an acting Hecke algebra on a specified integral definite-quaternion module such that

$$
\operatorname{tr}\bar\rho(\Phi_v)=T_v\bmod\mathfrak m,
\qquad
\det\bar\rho(\Phi_v)=q_vS_v\bmod\mathfrak m
\tag{2.7}
$$

for all $v$ outside the controlling set. The maximal ideal contains $\varpi$, has residue field $k$ after an allowed coefficient extension, and is non-Eisenstein. Non-Eisenstein here means that the associated residual pseudorepresentation is not a sum of two characters; absolute irreducibility identifies it with $\bar\rho$.

We further require that at least one characteristic-zero branch through $\mathfrak m$ is a noncharacter, cuspidal, parallel-weight-two packet with the declared determinant and local types. This supplies a distinguished augmentation later. For construction of a representation over the whole localized Hecke order, every generic branch—not just the distinguished one—must lie in the rank-two attachment range and possess the required integral coefficient-prime realization.

### 2.4 Adequacy on the cyclotomic restriction

Auxiliary-prime arguments do not use merely the image of $G_F$. They use the image of

$$
G_{F(\zeta_\ell)}.
$$

Our assumption that $\bar\rho$ remains absolutely irreducible on this subgroup is therefore made at the beginning. In characteristic $\ell\ge7$, the classification of finite projective linear groups implies that every absolutely irreducible two-dimensional finite image is adequate. Thus the restricted image satisfies

$$
H^1(G,k)=0,
\qquad H^1(G,\operatorname{ad}^0 k^2)=0,
\tag{2.8}
$$

and its semisimple elements span all of $M_2(k)$. The spanning statement implies regular-semisimple detection: every nonzero stable adjoint direction pairs nontrivially, under the trace pairing, with some nonscalar semisimple image element.

Adequacy does not imply (2.6), does not compute a Selmer group, and does not itself produce arithmetic primes with specified Frobenius. Its role here is narrower and precise: it certifies that the residual image has the finite-group cohomology and detection properties required when the later auxiliary-prime theorem is applied.

There is a useful counterexample to replacing cyclotomic irreducibility by global irreducibility. A representation induced from a character of a quadratic extension can be absolutely irreducible over $G_F$ while becoming a sum of two characters on a normal subgroup. If that subgroup contains $G_{F(\zeta_\ell)}$, the cyclotomic restriction preserves two lines. The full image still satisfies the global Schur condition, but the subgroup used for auxiliary-prime detection is not adequate. This is why the restricted image itself is tested.

### 2.5 The controlling set of places

It is useful to separate three finite sets. Let $S_\ell$ be the places above $\ell$, let $S_{\min}$ be the finite places away from $\ell$ at which the residual representation or its prescribed minimal type is ramified, and let $S_B$ be the finite ramification set of the definite quaternion algebra. In the clean definite model used here, $S_B\cap S_\ell=\varnothing$ and $S_B\subseteq S_{\min}$; every division-algebra place therefore carries a named matching minimal packet and integral local datum. We take

$$
S_f=S_\ell\cup S_{\min}\cup S_B,
\qquad S=S_f\cup S_\infty.
\tag{2.9}
$$

If a place belongs to more than one subset, its local datum must satisfy all corresponding requirements. Adding an unramified place to $S$ does not by itself relax the deformation problem: the unramified condition must still be imposed. Conversely, omitting a ramified determinant or type place from $S$ makes the global functor incorrectly typed.

## 3. Minimal local deformation conditions

### 3.1 Minimality is a deformation condition

A conductor is a number; a deformation condition is a functor stable under Artinian base change. The former rarely determines the latter. Two representations can have the same conductor but lie on different ordered principal components, have different finite inertia, or carry opposite special signs. We therefore define minimality place by place by a represented fixed-determinant condition $\mathcal D_v^{\min}$.

For an Artinian local $\mathcal O$-algebra $A$ with residue field $k$, an $A$-valued lift belongs to $\mathcal D_v^{\min}(A)$ only when its determinant is $\delta|_{G_v}$ and its restriction has the explicitly named integral structure below. The condition is invariant under strict conjugacy and compatible with quotient maps $A\to A/I$.

### 3.2 Places above the coefficient prime

Let $v\mid\ell$, and put $f_v=[F_v:\mathbf Q_\ell]$. We assume $F_v/\mathbf Q_\ell$ is unramified and $\bar\rho|_{G_v}$ belongs to the rank-two low-weight finite-flat range. The minimal local condition is:

> on every Artinian coefficient quotient $A$, the rank-two $A$-module underlying the lift is the generic fiber of a marked finite locally free group scheme with compatible coefficient action, Hodge weights $\{0,1\}$ at every embedding, and determinant $\delta|_{G_v}$.

The phrase “finite flat” is imposed on every Artinian quotient. It is stronger than asking that the characteristic-zero generic fiber be crystalline. The marked coefficient action and compatible transition maps are part of the integral datum.

Here the determinant is required to lie in the exact determinant fiber covered by the clean finite-flat theorem, as specified in Section 1.4. Under those unramified, low-weight, odd-prime, and determinant hypotheses, the framed fixed-determinant local functor is represented by a formally smooth ring of relative dimension

$$
f_v+3
\tag{3.1}
$$

over $\mathcal O$. Its unframed tangent subspace $L_v\subset H^1(F_v,M)$ satisfies

$$
\dim_kL_v-h^0(F_v,M)=f_v.
\tag{3.2}
$$

If the local residual centralizer is larger than the scalars, the framed statement remains valid and is the one used globally; no nonexistent coarse local ring is invoked.

### 3.3 Unramified places away from the coefficient prime

Suppose $v\nmid\ell$ and $\bar\rho|_{I_v}$ is trivial. The minimal unramified condition requires every lift to be trivial on inertia. Infinitesimally,

$$
L_v=H^1_{\mathrm{unr}}(F_v,M)
=\ker\bigl(H^1(F_v,M)\to H^1(I_v,M)\bigr).
\tag{3.3}
$$

Inflation--restriction identifies this with

$$
M/(\Phi_v-1)M.
$$

For a finite-dimensional endomorphism of a vector space, kernel and cokernel have the same dimension. Since the kernel is $M^{\Phi_v=1}=H^0(F_v,M)$, we obtain

$$
\dim_kL_v=h^0(F_v,M).
\tag{3.4}
$$

Thus an unramified finite place is neutral in the global defect formula. This proof also explains why merely placing $v$ in the allowed ramification set would be wrong: unrestricted ramification has a larger tangent space.

For a concrete calculation, suppose $M$ is unramified and $\Phi_v$ acts semisimply with eigenvalues $1,a,b$. If neither $a$ nor $b$ is one, then both $M/(\Phi_v-1)M$ and $M^{\Phi_v=1}$ are one-dimensional. If $a=1$ as well, both dimensions increase to two. Neutrality survives the jump in local centralizer because it is the equality of a kernel and a cokernel of the same square operator.

### 3.4 Fixed prime-to-coefficient inertia

Suppose the residual inertia factors through a finite group $J_v$ of order prime to $\ell$. Choose a specific integral lift of this inertia representation, including its ordering or finite-type enhancement when required, and impose strict-conjugacy equality with that lift. Averaging over $J_v$ makes the inertia representation rigid. The remaining infinitesimal freedom is unramified in the centralizer of $J_v$.

Let $M^{J_v}$ be that centralizer inside $M$. Then

$$
L_v\simeq M^{J_v}/(\Phi_v-1)M^{J_v},
\tag{3.5}
$$

and the same kernel--cokernel argument gives

$$
\dim_kL_v=h^0(F_v,M).
\tag{3.6}
$$

The type lattice on the automorphic side must detect this exact inertia label. If the label is principal, the ordering is retained whenever reduction cannot distinguish the two characters. If it is tame dihedral, the admissible quadratic pair and Frobenius return datum are retained. Primitive wild types and the excluded residue-characteristic-two ramified quadratic cases are not part of this minimal problem.

### 3.5 Minimal special places

At a special place, inertial semisimplification alone does not record monodromy. Choose an enhanced special condition consisting of scalar finite inertia, an invariant line, a Frobenius eigenvalue or sign compatible with $\delta$, and a nilpotent monodromy operator $N$ satisfying

$$
N^2=0,
\qquad \rho(\Phi_v)N\rho(\Phi_v)^{-1}=q_v^{-1}N.
\tag{3.7}
$$

Minimality means the schematic closure of the component containing the residual special representation, not the open requirement $N\ne0$: nonvanishing is not preserved under quotient. We include a special place only in the clean range where its represented fixed-determinant condition has been constructed and its tangent calculation proves

$$
\dim_kL_v=h^0(F_v,M).
\tag{3.8}
$$

This is an explicit hypothesis, not a deduction from the adjective “special.” It excludes congruence values at which signs collide, extra Kummer directions appear, or the residual monodromy vanishes without an enhanced component choice.

In a basis adapted to the invariant line, the generic special shape can be pictured as

$$
\rho(\sigma)=
\begin{pmatrix}1&t_\ell(\sigma)n\\0&1\end{pmatrix},
\qquad
\rho(\Phi_v)=
\begin{pmatrix}a&*\\0&q_va\end{pmatrix},
\tag{3.8a}
$$

up to finite scalar inertia and normalization. The corresponding monodromy is

$$
N=\begin{pmatrix}0&n\\0&0\end{pmatrix}.
$$

The equations relating Frobenius and $N$ are closed, whereas $n\ne0$ is open. Reduction modulo an ideal containing $n$ produces zero monodromy. The schematic closure correctly retains that quotient; a functor defined by $n\ne0$ would not be stable under coefficient quotients.

### 3.6 Real places

At each real place, impose the odd conjugacy class. Its tangent subspace is

$$
L_v=0.
\tag{3.9}
$$

Together with (2.5), its local contribution to the global defect is

$$
\dim_kL_v-h^0(F_v,M)=-1.
\tag{3.10}
$$

There are $[F:\mathbf Q]$ real places. This negative total is the counterpart of the positive finite-flat contribution at the places over $\ell$.

### 3.7 The local hypothesis ledger

The minimal datum can be summarized without using conductor as shorthand.

| Place | Condition | Necessary clean hypothesis | Tangent contribution |
|---|---|---|---|
| $v\mid\ell$ | finite flat of weights $\{0,1\}$, fixed determinant | $F_v/\mathbf Q_\ell$ unramified, $\ell>2$, low-weight residual range | $f_v$ |
| $v\nmid\ell$, residual inertia trivial | unramified | represented unramified quotient | $0$ |
| $v\nmid\ell$, finite inertia | fixed integral prime-to-$\ell$ type with enhancements | unit-valued label and rigidity | $0$ |
| $v\nmid\ell$, special | enhanced special closure with sign and line | clean chart and separately proved neutrality | $0$ |
| $v\mid\infty$ | odd conjugacy class | $\ell$ odd and determinant $-1$ | $-1$ |

Every row includes determinant compatibility. If one local determinant differs from $\delta|_{G_v}$, there is no global deformation problem obtained by pretending the discrepancy is an extra component.

## 4. Local rings, tangents, and determinant data

### 4.1 Why frames are retained locally

Local residual restrictions may have nonscalar centralizers even though $\bar\rho$ is globally absolutely irreducible. In that situation strict-equivalence classes need not form a representable local functor. A framing—a chosen basis lifting the residual basis—removes local automorphisms and produces a represented functor.

Write

$$
R_v^{\square,\min}
$$

for the framed fixed-determinant ring representing $\mathcal D_v^{\min}$. The frame is bookkeeping, not extra arithmetic. It will be removed globally using the global Schur condition.

### 4.2 Fixed-determinant tangent spaces

For dual numbers $k[\epsilon]/(\epsilon^2)$, write a lift as

$$
\rho(g)=(1+\epsilon c(g))\bar\rho(g).
$$

The homomorphism equation says that $c$ is a continuous $1$-cocycle with values in $\operatorname{ad}\bar\rho$. Fixing determinant gives

$$
\det(1+\epsilon c(g))=1+\epsilon\operatorname{tr}c(g)=1,
$$

so $c(g)\in M$. Strict conjugacy changes $c$ by a coboundary. Hence the unframed local tangent lies in $H^1(F_v,M)$, and the chosen local condition cuts out $L_v$.

The framed tangent retains coboundary directions. Its dimension is

$$
\dim_kL_v+\dim_kM-h^0(F_v,M)
=\dim_kL_v+3-h^0(F_v,M).
\tag{4.1}
$$

Formula (4.1) is valid even when local invariants are nonzero. Forgetting the final term is the common source of an erroneous framing count.

Indeed, framed cocycles form $Z^1_{\mathcal D_v}(F_v,M)$. The exact sequence

$$
0\longrightarrow H^0(F_v,M)
\longrightarrow M
\xrightarrow{a\mapsto(g\mapsto ga-a)}B^1(F_v,M)
\longrightarrow0
$$

shows that coboundaries have dimension $3-h^0(F_v,M)$. The framed tangent is an extension of $L_v$ by these coboundaries, which proves (4.1). If frames are changed through all of $\operatorname{GL}_2$ rather than the determinant-one gauge group, scalar directions must be included locally and removed globally; formula (5.6) performs precisely that correction.

### 4.3 The coefficient-prime calculation

At $v\mid\ell$, combine (3.2) and (4.1):

$$
\dim t_v^{\square,\min}
=f_v+h^0(F_v,M)+3-h^0(F_v,M)
=f_v+3.
\tag{4.2}
$$

Thus formal smoothness of relative dimension $f_v+3$ agrees with the cohomological tangent calculation. The equality is a useful consistency check because it remains valid at a residual point with enlarged centralizer: the unframed condition and the framing correction change in opposite directions.

### 4.4 Neutrality away from the coefficient prime

For each clean finite place $v\nmid\ell$, (3.4), (3.6), or the explicit special calculation gives

$$
\dim_kL_v=h^0(F_v,M).
\tag{4.3}
$$

Consequently its framed tangent dimension is always three:

$$
\dim t_v^{\square,\min}=3.
\tag{4.4}
$$

In the formally smooth cases the ring is therefore a power-series ring in three variables over $\mathcal O$ after a noncanonical choice of coordinates. This apparent uniformity must not be used to identify the conditions: different inertia labels can have isomorphic abstract smooth rings while describing disjoint arithmetic loci.

### 4.5 The completed local base

Choose a nonempty set $T$ of finite places at which frames are retained. Conditions at places outside $T$ are still imposed as closed pullbacks on the global functor; choosing $T$ does not relax them. Define

$$
R_{\mathrm{loc}}^{\min}
=\widehat\bigotimes_{v\in T,\mathcal O}R_v^{\square,\min}.
\tag{4.5}
$$

The completed tensor product is legitimate because the factors are complete Noetherian local $\mathcal O$-algebras with a common residue field and are topologically of finite type. Under the clean smooth hypotheses it is formally smooth over $\mathcal O$ of relative dimension

$$
d_{\mathrm{loc}}
=\sum_{\substack{v\in T\\v\mid\ell}}(f_v+3)
+\sum_{\substack{v\in T\\v\nmid\ell}}3.
\tag{4.6}
$$

When a represented local factor is not known to be smooth, it remains in (4.5), but its equations must be retained and (4.6) must be replaced by the actual dimension. The standing clean problem excludes that ambiguity.

## 5. The global minimal deformation ring

### 5.1 The functor and its universal ring

For an Artinian local $\mathcal O$-algebra $A$ with residue field $k$, let $D^{\min}(A)$ be the set of strict-equivalence classes of continuous lifts

$$
\rho_A:G_{F,S}\longrightarrow\operatorname{GL}_2(A)
$$

such that

$$
\rho_A\bmod\mathfrak m_A=\bar\rho,
\qquad \det\rho_A=\delta,
$$

and $\rho_A|_{G_v}$ belongs to $\mathcal D_v^{\min}(A)$ for every $v\in S$. The global Schur condition and represented, closed, base-change-stable local conditions imply that $D^{\min}$ is represented by a complete Noetherian local ring

$$
R^{\min}=R_{\mathcal D^{\min}}.
\tag{5.1}
$$

Its universal representation is defined up to strict conjugacy. This is sufficient: trace, determinant, and membership in the conjugacy-invariant local conditions are independent of the representative.

### 5.2 The framed fiber product

Let $R_{F,S}^{\square_T,\mathcal D^{S\setminus T}}$ be the global fixed-determinant ring with frames at $T$ and with the minimal conditions outside $T$ already imposed as closed pullbacks. Let $R_v^\square$ be the unrestricted local framed rings. Restriction of representations gives the ring map

$$
\widehat\bigotimes_{v\in T}R_v^\square
\longrightarrow R_{F,S}^{\square_T,\mathcal D^{S\setminus T}}.
$$

The conditioned global framed ring is

$$
R^{\square_T,\min}
=R_{F,S}^{\square_T,\mathcal D^{S\setminus T}}
\widehat\otimes_{\widehat\otimes_{v\in T}R_v^\square}
R_{\mathrm{loc}}^{\min}.
\tag{5.2}
$$

The direction of the structural map is therefore

$$
R_{\mathrm{loc}}^{\min}\longrightarrow R^{\square_T,\min}.
\tag{5.3}
$$

The tensor product in (5.2) reverses a fiber product of functors. Removing frames recovers (5.1). This construction remains valid when an individual local coarse ring does not exist.

### 5.3 The primal Selmer group

The tangent space of the unframed global problem is the Selmer group

$$
H^1_{\mathcal L}(F,M)
=\ker\left(
H^1(G_{F,S},M)\longrightarrow
\bigoplus_{v\in S}H^1(F_v,M)/L_v
\right).
\tag{5.4}
$$

Thus

$$
t_{R^{\min}}\simeq H^1_{\mathcal L}(F,M).
\tag{5.5}
$$

This group measures actual first-order global deformations satisfying every minimal local condition. It is not computed by summing local tangent dimensions: global localization relations remain.

For the ring relative to $R_{\mathrm{loc}}^{\min}$, replace $L_v$ by $0$ at $v\in T$ and write the resulting strict Selmer group as $H^1_{\mathcal L,T}(F,M)$. The relative generator number is

$$
g_T=h^1_{\mathcal L,T}(F,M)
+\sum_{v\in T}h^0(F_v,\operatorname{ad}\bar\rho)
-h^0(F,\operatorname{ad}\bar\rho).
\tag{5.6}
$$

Because the representation is globally Schur, the last term is $1$. The use of $\operatorname{ad}\bar\rho$, rather than $M$, in the framing correction is deliberate: a frame is changed by all infinitesimal matrices, while determinant fixing constrains the representation cocycle.

### 5.4 The dual Selmer group

Local Tate duality pairs

$$
H^1(F_v,M)\times H^1(F_v,M(1))\longrightarrow k.
$$

Let $L_v^\perp$ be the exact annihilator of $L_v$. The dual Selmer group is

$$
H^1_{\mathcal L^\perp}(F,M(1))
=\ker\left(
H^1(G_{F,S},M(1))\longrightarrow
\bigoplus_{v\in S}H^1(F_v,M(1))/L_v^\perp
\right).
\tag{5.7}
$$

Set

$$
q=h^1_{\mathcal L^\perp}(F,M(1)).
\tag{5.8}
$$

This is the absolute dual Selmer dimension and the number later targeted by auxiliary primes.

For a presentation relative to $R_{\mathrm{loc}}^{\min}$, the relevant obstruction bound uses a different group. At places of $T$, the strict primal condition $0$ has full local dual, so define

$$
q_T=h^1_{(\mathcal L_T^0)^\perp}(F,M(1)).
\tag{5.9}
$$

The numbers $q$ and $q_T$ must not be interchanged. The first controls how many auxiliary prime directions are needed in the absolute problem; the second bounds relations in the chosen relative framed presentation.

### 5.5 The balanced totally real formula

Poitou--Tate duality gives

$$
\begin{aligned}
h^1_{\mathcal L}(F,M)-h^1_{\mathcal L^\perp}(F,M(1))
={}&h^0(F,M)-h^0(F,M(1))\\
&+\sum_{v\in S}
\bigl(\dim_kL_v-h^0(F_v,M)\bigr).
\end{aligned}
\tag{5.10}
$$

We now evaluate every term. Equations (2.4) and (2.6) make the two global invariants zero. Every finite place away from $\ell$ contributes zero by (4.3). Each real place contributes $-1$. Each $v\mid\ell$ contributes $f_v$. Since $F$ is totally real,

$$
\sum_{v\mid\ell}f_v=[F:\mathbf Q]=|S_\infty|.
\tag{5.11}
$$

The two sums cancel, and therefore

$$
\boxed{
h^1_{\mathcal L}(F,M)
=h^1_{\mathcal L^\perp}(F,M(1))=q.}
\tag{5.12}
$$

Balanced means equality of the two dimensions, not their vanishing. In particular, the minimal deformation ring can have a large tangent space even though the numerical defect is zero.

The proof of (5.10) is best read as an Euler-characteristic argument. The global localization map and its Tate-dual map belong to one Poitou--Tate exact sequence. Taking alternating dimensions gives the global invariant terms and local Euler characteristics; local duality rewrites the latter as $\dim L_v-h^0(F_v,M)$. The formula is therefore not an empirical parameter count but the Euler characteristic of a self-dual localization complex.

The hypothesis (2.6) is visible in this form. If $s=h^0(F,M(1))>0$, the same local calculation gives

$$
h^1_{\mathcal L}(F,M)-h^1_{\mathcal L^\perp}(F,M(1))=-s.
$$

The dual group is then at least $s$ dimensions larger. Adding frames cannot alter that absolute defect; a cyclotomic self-twist must be ruled out or incorporated into a modified problem.

### 5.6 Presentations and the two relation counts

The obstruction theory of the global deformation problem gives a presentation

$$
R^{\square_T,\min}
\simeq R_{\mathrm{loc}}^{\min}[[x_1,\ldots,x_{g_T}]]
/(f_1,\ldots,f_{r_T})
\tag{5.13}
$$

with

$$
r_T\le q_T.
\tag{5.14}
$$

The inequality reflects the distinction between a complete obstruction space and the minimal relation module. It cannot be upgraded to equality without further information.

For the unframed absolute problem, a minimal Cohen presentation over $\mathcal O$ has $q$ tangent directions by (5.12), after the determinant and coefficient direction are accounted for in the chosen convention, and at most $q$ cohomologically visible relations in the balanced clean setting. The safe invariant statement is the equality of primal and dual dimensions (5.12), together with the framed formula (5.13)--(5.14). A claim that a particular presentation has exactly $q$ equations requires minimality of the obstruction space and will not be assumed here.

## 6. Definite-quaternion automorphic data

### 6.1 Choosing the inner form

The automorphic side should be finite, integral, and free of boundary cohomology. A quaternion algebra definite at every real place provides precisely such a carrier. Let $B/F$ be a quaternion algebra ramified at all real places and at the finite set $\Sigma_B=S_B$ chosen so that the total number of ramified places is even. Thus $B$ is split at every place above $\ell$. At a finite place where $B$ is ramified, the residual and automorphic local packets must lie in the established local correspondence range.

The parity condition is not cosmetic: a quaternion algebra with the declared ramification set exists only when that set has even cardinality. Nor may one choose $B$ solely for convenience. The selected residual packet must transfer to $B^\times$, and the faithful integral Hecke order used below must agree with the order on any alternative geometric carrier whenever such an identification is invoked. Rational transfer alone does not identify integral congruence ideals.

Write

$$
G=(B\otimes_F\mathbf A_F^\infty)^\times.
$$

Choose a compact open subgroup $U=\prod_vU_v\subset G$. Outside $S_f$, take $B_v\simeq M_2(F_v)$ and $U_v\simeq\operatorname{GL}_2(\mathcal O_{F_v})$. At places in $S_f$, the local factor is chosen together with the type datum described next.

### 6.2 Level, weight, and local type lattices

Parallel weight two contributes no nontrivial algebraic weight representation to a totally definite class-set model after the central normalization is fixed. The finite local data remain essential. For each $v\in S_{\min}$, choose a finite free $\mathcal O$-lattice $W_v$ for the compact group $U_v$ that realizes the primary local type matching $\mathcal D_v^{\min}$.

When $B$ is split at $v$, this is the corresponding integral $\operatorname{GL}_2(\mathcal O_{F_v})$-type, for example:

- the trivial spherical lattice for an unramified condition;
- an induced flag lattice for a regular principal finite type;
- the projective-line quotient or its explicitly declared special variant at a special place;
- an integral cuspidal or tame Heisenberg lattice for a controlled dihedral type.

When $B$ is ramified at $v$, $W_v$ is instead the named integral compact type on the quaternion division group, obtained in the verified local Jacquet--Langlands range. Its primary label, companion, and integral pairing are transported by the established integral comparison; a split-group flag or projective-line lattice is not silently used as a representation of $\mathcal O_{B_v}^{\times}$.

Put

$$
W=\bigotimes_{v\in S_{\min}}W_v.
\tag{6.1}
$$

Every character value is required to lie in $\mathcal O^\times$. At nonbanal primes, the explicit lattice is retained rather than replaced by a rational idempotent. Where an ordering, invariant line, Frobenius return map, newness condition, or special sign distinguishes components, it is part of the datum.

For adjunction, choose the companion lattice $W_v^\dagger$ with inverse labels. The pairings constructed for the local types give

$$
W_v\times W_v^\dagger\longrightarrow\mathcal O
\tag{6.2}
$$

perfectly. In the Steinberg case the quotient and augmentation lattices can be distinct even though their generic fibers are dual. This is exactly why the companion is named rather than silently identified with the primary lattice.

### 6.3 The finite automorphic module

Let $Z$ be the finite adelic center and fix a central character compatible with $\eta$ in (2.2). The definite double quotient

$$
B^\times\backslash G/U
\tag{6.3}
$$

is finite. Define $M_U(W)$ to be the $\mathcal O$-module of functions on $G$ with the prescribed left $B^\times$-invariance, right $U$-equivariance through $W$, and central character. Concretely, choosing double-coset representatives $g_i$ identifies it with a direct sum of invariant modules

$$
M_U(W)\simeq\bigoplus_i W^{\overline\Gamma_i},
\qquad
\Gamma_i^{\mathrm{raw}}=B^\times\cap g_iUg_i^{-1},
\quad
C_i=F^\times\cap g_iUg_i^{-1}=F^\times\cap U,
\quad
\overline\Gamma_i=\Gamma_i^{\mathrm{raw}}/C_i,
\tag{6.4}
$$

Here the compatible central character has been absorbed into the coefficient action, so $C_i$ acts trivially and the invariant module in (6.4) means $W^{\overline\Gamma_i}$. Definiteness makes $\overline\Gamma_i$ finite even though $C_i$ need not be. We impose neatness, or the equivalent unit-stabilizer condition needed for the chosen coefficient prime, so that taking $\overline\Gamma_i$-invariants preserves the required integral direct summands. It follows that $M_U(W)$ is finite free over $\mathcal O$.

Formula (6.4) is also a warning. Treating the class set as an unweighted collection of points loses stabilizer multiplicities. The Hecke action and mass pairing below use the exact orbit weights.

Parity gives a simple example of the interaction between global and local choices. If $[F:\mathbf Q]$ is odd, a quaternion algebra ramified only at the real places cannot exist, since a quaternion algebra has an even number of ramified places. One must add a finite ramified place, which then enters the local correspondence and type datum. If $[F:\mathbf Q]$ is even, ramification at precisely the real places is allowed. The two carriers may support the same generic packets, but their integral congruence lattices agree only after an integral comparison theorem.

### 6.4 The residual maximal ideal

At $v\notin S_f$, the spherical right double cosets define commuting operators $T_v$ and invertible central operators $S_v$. Let

$$
\mathbb T_U^{S_f}
=\mathcal O[T_v,S_v^{\pm1}:v\notin S_f]
\subseteq\operatorname{End}_{\mathcal O}(M_U(W))
\tag{6.5}
$$

be the faithful image, not merely the abstract polynomial algebra on symbols. The residual automorphy hypothesis supplies a maximal ideal $\mathfrak m$ containing $\varpi$ such that (2.7) holds. After extending coefficients if necessary, assume its residue field is exactly $k$.

Localize both algebra and module:

$$
\mathbb T^{\min}=(\mathbb T_U^{S_f})_{\mathfrak m},
\qquad
M^{\min}=M_U(W)_{\mathfrak m}.
\tag{6.6}
$$

Because the original algebra is finite over the complete DVR, this localization is already complete for its maximal-ideal topology. Writing it as an inverse-limit completion changes no finite-level object, but it specifies the topology used by the universal deformation ring.

### 6.5 Exact minimal matching

The local automorphic datum and the local deformation datum are declared to **match minimally** when all of the following hold.

1. At $v\mid\ell$, every generic packet branch has an integral rank-two lattice whose every Artinian quotient is finite flat of weights $\{0,1\}$ and determinant $\delta$.
2. At an unramified place, the level is hyperspecial and the packet is unramified.
3. At a finite-type place, occurrence of $W_v$ detects the same inertia label, ordering, and Frobenius enhancement as $\mathcal D_v^{\min}$.
4. At a special place, the chosen primary type and newness or sign datum select the schematic special component used on the Galois side.
5. The central character yields (2.3).
6. Every comparison between a curve carrier and the definite module identifies the faithful integral orders, not merely their generic fibers.

The integral local-type theorem proves the equivalence between occurrence and the named characteristic-zero local parameter in the controlled principal, special, and tame-dihedral cases. The Hecke-valued reciprocity theorem then promotes branchwise membership to the whole reduced order. No statement is made for primitive wild types or an unverified congruent component.

## 7. Hecke algebras, pairings, and branches

### 7.1 The faithful Hecke image

The adjective “faithful” in (6.5) has a precise meaning:

$$
\operatorname{Ann}_{\mathbb T^{\min}}M^{\min}=0.
\tag{7.1}
$$

It follows because the algebra is defined as the image before localization and annihilators localize. Faithfulness does not imply that $M^{\min}$ is free over $\mathbb T^{\min}$, nor that the Hecke algebra is Gorenstein. These are later conclusions under stronger hypotheses.

The algebra is generated by the good $T_v$ together with the prescribed central scalars $S_v$. Since the determinant is fixed, the $S_v$ belong to the coefficient image determined by $\delta$; equivalently, one may define the trace Hecke algebra using only the $T_v$. We assume throughout that no extra local operator outside this trace order has been adjoined. This exact generation statement is what will make the comparison map surjective.

### 7.2 Localization and finite flatness

The module $M^{\min}$ is finite free over $\mathcal O$. The algebra $\mathbb T^{\min}$ embeds in its endomorphism ring, so it is finite and $\mathcal O$-torsion-free. Over a DVR, finite torsion-free modules are free. Thus

$$
\mathbb T^{\min}\ \text{is finite flat over }\mathcal O.
\tag{7.2}
$$

It is complete Noetherian local with residue field $k$. Its generic fiber may be a product of fields, and several factors may meet at the residual point. Its special fiber may have nilpotents even when its generic fiber is reduced.

Localization retains the entire generalized residual summand. It is not the same as quotienting $M_U(W)$ by $\mathfrak m$, and it is not a choice of one characteristic-zero eigenvector. These distinctions are essential because congruences are precisely the integral intersections among the generic branches retained in (6.6).

### 7.3 Primary and companion modules

Form the companion coefficient lattice

$$
W^\dagger=\bigotimes_{v\in S_{\min}}W_v^\dagger
$$

and the corresponding localized module

$$
M^{\dagger,\min}=M_U(W^\dagger)_{\mathfrak m^\dagger},
\tag{7.3}
$$

where the maximal ideal is transported by the adjoint involution. The primary and companion modules have the same generic packet multiplicities after dualizing labels, but their integral reductions need not be isomorphic.

At each local type, the explicit perfect pairing (6.2) is used before taking global invariants. The global mass formula then pairs the two modules without dividing by a potentially nonunit group order. This construction remains valid in the controlled nonbanal Steinberg cases in which an idempotent projector would not be integral.

### 7.4 Perfect pairings and adjoints

For representatives $g_i$ of (6.3), define

$$
\langle f,h\rangle
=\sum_i\frac{1}{|\overline\Gamma_i|}
\langle f(g_i),h(g_i)\rangle_{W,W^\dagger}.
\tag{7.4}
$$

Our stabilizer hypothesis makes every denominator a unit in $\mathcal O$. Together with the perfect local pairings, this makes (7.4) a perfect pairing

$$
M^{\min}\times M^{\dagger,\min}\longrightarrow\mathcal O.
\tag{7.5}
$$

Right-double-coset inversion gives the adjoint. At a spherical place, with central factors left visible,

$$
T_v^\dagger=S_v^{-1}T_v,
\qquad S_v^\dagger=S_v^{-1},
\tag{7.6}
$$

in the customary normalization. More invariantly, the adjoint of $[U h U]$ is $[U h^{-1}U]$. Formula (7.6) is used only after identifying the inverse double coset; it is not a convention imposed independently of the correspondence calculus.

If the central character and local labels identify $W^\dagger$ with $W$, (7.5) becomes a self-dual pairing on $M^{\min}$. Otherwise the two-module form is the correct object. All congruence constructions below can be expressed using this paired pair, so self-duality is never assumed merely for convenience.

### 7.5 Generic branches and reducedness

Let

$$
\mathbb T_E^{\min}=\mathbb T^{\min}\otimes_{\mathcal O}E.
$$

We assume it is reduced. Since it is a finite commutative $E$-algebra, it is then a product of finite field extensions:

$$
\mathbb T_E^{\min}\simeq\prod_{\pi\in\mathcal B}E_\pi.
\tag{7.7}
$$

The finite set $\mathcal B$ consists of the characteristic-zero automorphic branches through $\mathfrak m$. Each branch is required to be a noncharacter cuspidal parallel-weight-two packet in the rank-two attachment range, with full local compatibility and the integral realization at places over $\ell$.

Reducedness is used to test closed represented local conditions on every generic factor and then descend their defining equations to the order. If $\mathbb T_E^{\min}$ had nilpotents, vanishing at every field-valued generic point would not detect them. Reduced generic fiber does not imply reduced special fiber and does not imply that the integral order is normal.

The simplest branch crossing is

$$
A=\mathcal O[X]/(X(X-a)),
\qquad 0\ne a\in\varpi\mathcal O.
\tag{7.8}
$$

Its generic fiber is the product of the branches $X=0$ and $X=a$, hence reduced. Modulo $\varpi$ the two branches meet, and the class of $X$ is nilpotent. Thus special-fiber nilpotence can be the shadow of a genuine congruence between reduced characteristic-zero packets. Passing to the reduced special fiber would destroy precisely the branch contact that the Hecke order records.

## 8. The Hecke-valued representation and the map from deformations

### 8.1 Branchwise representations

For each $\pi\in\mathcal B$, weight-two attachment gives a continuous semisimple representation

$$
\rho_\pi:G_{F,S}\longrightarrow\operatorname{GL}_2(E_\pi)
$$

such that, for every $v\notin S_f$,

$$
\det(X-\rho_\pi(\Phi_v))
=X^2-T_v(\pi)X+q_vS_v(\pi),
\tag{8.1}
$$

and

$$
\det\rho_\pi=\delta.
\tag{8.2}
$$

The good polynomial ultimately comes from the common geometric Hecke correspondence relation

$$
\Phi_v^2-T_v\Phi_v+q_vS_v=0
$$

on the relevant untwisted cohomology, followed by rank-two extraction. Equation (8.1) uses geometric Frobenius; switching to an arithmetic Frobenius on a covariant Tate module inverts and twists the coefficients.

### 8.2 Descent to the localized order

Taking the product of the $\rho_\pi$ gives a representation over $\prod E_\pi$. Good Frobenius traces lie in the suborder $\mathbb T^{\min}$ by construction. Density of good Frobenius classes and continuity put the trace of every Galois element in that order. Residual absolute irreducibility then turns trace coordinates into a rank-four matrix algebra and splits it over the complete local order. The result is a continuous representation

$$
\rho_{\mathbb T}:G_{F,S}\longrightarrow
\operatorname{GL}_2(\mathbb T^{\min}),
\tag{8.3}
$$

unique up to strict conjugacy, with

$$
\operatorname{tr}\rho_{\mathbb T}(\Phi_v)=T_v,
\qquad
\det\rho_{\mathbb T}=\delta.
\tag{8.4}
$$

The common residual representation, completeness, and absolute irreducibility are essential. A tuple of branchwise integral traces need not yield a free rank-two representation over an arbitrary order when the residual representation is reducible.

One can see the descent through trace coordinates. Choose residual image elements whose matrices span $M_2(k)$ and lift them to Galois elements $g_1,\ldots,g_4$. They may be chosen so that the trace Gram determinant

$$
\det\bigl(\operatorname{tr}(\bar\rho(g_ig_j))\bigr)_{i,j}
$$

is nonzero. Its lift is a unit of $\mathbb T^{\min}$. Pairing with the four $g_i$ expresses every element of the algebra generated by the product representation in unique integral trace coordinates. The resulting rank-four algebra is Azumaya and has split residual fiber; completeness lifts residual matrix units, so it is $M_2(\mathbb T^{\min})$. Conjugating into that splitting yields (8.3), and the same unit Gram matrix proves strict uniqueness.

### 8.3 Verification of the minimal local conditions

At every generic branch, local--global compatibility and type detection place $\rho_\pi|_{G_v}$ on the named local component. Because $R_v^{\square,\min}$ represents a closed condition and $\mathbb T^{\min}$ is $\mathcal O$-flat with reduced generic fiber, the defining ideal vanishes over the entire order. Consequently every Artinian quotient of (8.3) satisfies $\mathcal D_v^{\min}$.

At $v\mid\ell$, this argument includes the integral finite-flat comparison: every quotient, not merely every generic branch, comes from the prescribed finite-flat object. At a fixed finite-type place, prime-to-$\ell$ inertia is constant after strict conjugacy. At an ordered principal place, the two lines and characters exist over the order. At a special place, the monodromy operator satisfies (3.7), while its possible vanishing on a quotient is retained as part of the schematic closure.

This step uses the exact minimal matching of Section 6.5. Characteristic-zero conductor equality alone would not prove factorization through the chosen local rings.

### 8.4 Construction and surjectivity of the comparison map

The representation (8.3) is a $\mathbb T^{\min}$-valued point of the functor represented by $R^{\min}$. Universality gives a continuous local homomorphism

$$
\theta:R^{\min}\longrightarrow\mathbb T^{\min}.
\tag{8.5}
$$

Its direction is forced: a point with coefficients in an algebra is a map from the universal coefficient ring to that algebra. The universal representation specializes along $\theta$ to $\rho_{\mathbb T}$ up to strict conjugacy. Hence

$$
\theta(\operatorname{tr}\rho^{\mathrm{univ}}(\Phi_v))=T_v.
\tag{8.6}
$$

The image of $\theta$ is closed because the target is finite over $\mathcal O$. It contains every good trace generator $T_v$ and the determinant-fixed central coefficients. By the trace-generation hypothesis of Section 7.1, these generate $\mathbb T^{\min}$. Therefore

$$
\boxed{\theta:R^{\min}\twoheadrightarrow\mathbb T^{\min}.}
\tag{8.7}
$$

If an extra $U_v$, diamond operator, or type endomorphism were adjoined without an integral generation theorem, the same proof would reach only the trace subalgebra. This is why the target in (8.7) was defined exactly.

### 8.5 What the comparison map does not prove

Surjectivity proves that every Hecke parameter visible in the selected module is governed by the universal minimal deformation. It does not prove that every minimal deformation is automorphic. Algebraically, it says nothing yet about the kernel of $\theta$.

Nor does (8.7) imply that $R^{\min}$ is finite or flat over $\mathcal O$, that it is a complete intersection, or that $M^{\min}$ is free over $\mathbb T^{\min}$. Those statements are the substance of the later minimal patching theorem. Any argument here that used them to compute the kernel would be circular.

## 9. Augmentations and congruence modules

### 9.1 Selecting an integral automorphic branch

Choose a characteristic-zero packet $\pi_0\in\mathcal B$ and enlarge $E$ and $\mathcal O$ so that its eigenvalues define an $\mathcal O$-valued character

$$
\lambda_T:\mathbb T^{\min}\longrightarrow\mathcal O.
\tag{9.1}
$$

Compatibility with (8.5) gives

$$
\lambda_R=\lambda_T\circ\theta:R^{\min}\longrightarrow\mathcal O.
\tag{9.2}
$$

Let

$$
I_T=\ker\lambda_T,
\qquad I_R=\ker\lambda_R.
\tag{9.3}
$$

The chosen branch is isolated in the generic fiber because (7.7) is a finite product of fields. Thus all cotangent and congruence modules below have finite $\mathcal O$-length.

### 9.2 Cotangent and congruence modules

The relative augmentation cotangent modules are

$$
\Phi_T=I_T/I_T^2,
\qquad
\Phi_R=I_R/I_R^2.
\tag{9.4}
$$

The surjection $\theta$ induces a surjection $\Phi_R\twoheadrightarrow\Phi_T$. If $J=\ker\theta$, the exact conormal sequence is

$$
\frac{J}{J\cap I_R^2}
\longrightarrow\Phi_R
\longrightarrow\Phi_T\longrightarrow0.
\tag{9.5}
$$

It records only the first-order part of $J$; even vanishing of its left term would not by itself imply $J=0$.

Define the Hecke congruence ideal and module by

$$
\eta_T=\lambda_T(\operatorname{Ann}_{\mathbb T^{\min}}I_T)
\subseteq\mathcal O,
\qquad
\Psi_T=\mathcal O/\eta_T.
\tag{9.6}
$$

In the generic product (7.7), the idempotent selecting $\pi_0$ generally has denominators. The ideal $\eta_T$ is the set of coefficients that clear those denominators integrally. Thus $\Psi_T$ measures contact between the selected branch and all other branches through the residual point.

### 9.3 The pairing construction

Let $e_0\in\mathbb T_E^{\min}$ be the idempotent of the selected branch. Define saturated lattices

$$
L=e_0M_E^{\min}\cap M^{\min},
\qquad
L^\dagger=e_0^\dagger M_E^{\dagger,\min}\cap M^{\dagger,\min}.
\tag{9.7}
$$

The perfect pairing (7.5) restricts to a pairing $L\times L^\dagger\to\mathcal O$. Its discriminant quotient can be written as

$$
\Psi_M
=\operatorname{coker}\left(
L\longrightarrow\operatorname{Hom}_{\mathcal O}(L^\dagger,\mathcal O)
\right).
\tag{9.8}
$$

Equivalently, using the complementary saturated generic summands, $\Psi_M$ measures the failure of the selected and complementary lattices to split the whole localized module integrally. This description makes its finiteness transparent: the splitting exists after inverting $\varpi$.

### 9.4 Multiplicity and saturation

Suppose the selected generic packet has multiplicity $r$, so $L$ and $L^\dagger$ have rank $r$ over $\mathcal O$. Put

$$
P=e_0M^{\min}\subset e_0M_E^{\min}.
$$

The full perfect pairing identifies $P$ with $\operatorname{Hom}_{\mathcal O}(L^\dagger,\mathcal O)$ under the primitive multiplicity hypothesis. The exact branch-saturation hypothesis is

$$
L=\eta_TP.
\tag{9.8a}
$$

It is an integral lattice equality, not a consequence of faithfulness or generic multiplicity. Under (9.8a), Smith normal form gives

$$
\operatorname{length}_{\mathcal O}\Psi_M
=r\,\operatorname{length}_{\mathcal O}\Psi_T.
\tag{9.9}
$$

Here is the mechanism. In the normalization, an element $a$ belongs to $\operatorname{Ann}I_T$ exactly when its components vanish off the selected branch. Thus $\eta_TP\subseteq L$. Hypothesis (9.8a) says that there is no further branch-saturation quotient. The pairing identifies the target of (9.8) with $P$, so its cokernel is $P/L=P/\eta_TP$. On each of the $r$ multiplicity coordinates the same principal ideal appears. Diagonalizing the inclusion adds its valuation $r$ times, proving (9.9).

Without (9.8a), the exact correction is the finite quotient $L/\eta_TP$, and the module congruence length is smaller than the right side of (9.9) by its length. Without multiplicity control, $\Psi_M$ can contain a matrix discriminant not determined by the ring congruence ideal. Thus dividing a module length by an observed eigenspace dimension is justified only after the hypotheses of (9.9) have been checked.

### 9.5 The exact numerical inequalities

For any finite flat local augmented $\mathcal O$-algebra with separable generic fiber,

$$
\operatorname{length}_{\mathcal O}\Phi_T
\ge
\operatorname{length}_{\mathcal O}\Psi_T.
\tag{9.10}
$$

Equality holds when $\mathbb T^{\min}$ is a complete intersection; conversely, under the standard generic-isolation hypotheses, equality detects that property. The surjection (8.7) gives

$$
\operatorname{length}\Phi_R
\ge\operatorname{length}\Phi_T
\ge\operatorname{length}\Psi_T,
\tag{9.11}
$$

provided $\Phi_R$ has finite length. The first inequality is conormal; the second is determinant--congruence. There is no natural quotient map $\Phi_T\to\Psi_T$ behind the second inequality.

To force $R^{\min}=\mathbb T^{\min}$ by a numerical criterion, one would need an independent upper bound

$$
\operatorname{length}\Phi_R
\le\operatorname{length}\Psi_T.
\tag{9.12}
$$

This volume defines every term and supplies the structural inequalities (9.11), but does not prove (9.12). Minimal patching is the mechanism that later supplies the missing rigidity. Claiming equality here from the balanced dimension formula would confuse a dimension over $k$ with a length over $\mathcal O$.

The crossing algebra (7.8) makes the invariants concrete. Augment at $X=0$. Then $I=(X)$, and $X^2=aX$ gives

$$
\Phi_A=I/I^2\simeq\mathcal O/(a).
$$

An element $u+vX$ annihilates $I$ exactly when $u=-av$, so its augmentation lies in $(a)$ and every element of $(a)$ occurs. Therefore

$$
\Psi_A\simeq\mathcal O/(a),
\qquad
\operatorname{length}\Phi_A=\operatorname{length}\Psi_A.
$$

This agrees with the fact that $A$ is a hypersurface. Surplus relations can make cotangent length strictly larger while leaving the branch denominator fixed; the difference is the complete-intersection defect.

The pointed numerical criterion follows from the same chain. Suppose $R\twoheadrightarrow T$ is compatible with augmentations, $T$ is finite flat, $\Phi_R$ has finite length, and (9.12) holds. The conormal sequence gives

$$
\operatorname{length}\Psi_T
\ge\operatorname{length}\Phi_R
=\operatorname{length}\frac{\ker\theta}{\ker\theta\cap I_R^2}
+\operatorname{length}\Phi_T
\ge\operatorname{length}\Psi_T.
$$

Every inequality is equality. The first-order kernel vanishes and $T$ is a complete intersection. Present both rings as quotients of one power-series ring. A regular sequence generates the target kernel; equality of conormal lattices supplies source relations whose differential matrix differs by a unit. The change-of-relations matrix is invertible, so the presentation ideals agree and $R\simeq T$. This last relation-lattice step explains why first-order kernel vanishing alone was insufficient.

## 10. Determinant lines and the numerical bridge

### 10.1 The minimal Selmer complex

Tangent spaces and obstruction spaces should be assembled before taking dimensions. For every $v\in S$, choose a local-condition complex $U_v^\bullet$ mapping to the continuous cochain complex $C^\bullet(F_v,M)$ and inducing $L_v$ on $H^1$. Define the minimal Selmer complex by

$$
C_{\min}^\bullet
=\operatorname{Cone}\left(
C^\bullet(G_{F,S},M)\oplus\bigoplus_{v\in S}U_v^\bullet
\longrightarrow
\bigoplus_{v\in S}C^\bullet(F_v,M)
\right)[-1].
\tag{10.1}
$$

The map is localization minus the local-condition inclusion. Its first cohomology is (5.4):

$$
H^1(C_{\min}^\bullet)=H^1_{\mathcal L}(F,M).
\tag{10.2}
$$

Under the effective local and global obstruction theories, $H^2(C_{\min}^\bullet)$ is the complete obstruction space. Global duality identifies its dual with the dual Selmer group, up to the endpoint invariant terms already removed by (2.4) and (2.6):

$$
H^2(C_{\min}^\bullet)^\vee
\simeq H^1_{\mathcal L^\perp}(F,M(1)).
\tag{10.3}
$$

The real terms in (10.1) use Tate-modified local cohomology even though positive-degree ordinary real cohomology vanishes for odd $\ell$. This is what preserves the $-1$ contribution in (3.10).

### 10.2 Its determinant line

Choose a perfect representative for the finite Selmer complex. Its determinant is the graded line

$$
\mathscr D_{\min}=\operatorname{Det}_k(C_{\min}^\bullet).
\tag{10.4}
$$

Since the endpoint cohomology vanishes in the clean Schur setting, the cohomology formula gives

$$
\mathscr D_{\min}
\simeq
\det_kH^1_{\mathcal L}(F,M)^{-1}
\otimes_k
\det_kH^1_{\mathcal L^\perp}(F,M(1))^\vee.
\tag{10.5}
$$

Depending on whether (10.3) is written before or after dualization, the second factor can equivalently be expressed using the determinant of $H^2(C_{\min}^\bullet)$. The invariant content is that its graded degree is

$$
-h^1_{\mathcal L}(F,M)+h^2(C_{\min}^\bullet)=0
\tag{10.6}
$$

by (5.12) and (10.3). Thus the minimal determinant line is balanced. A degree-zero line is not canonically trivial: choosing bases of primal and dual Selmer groups would trivialize it, but the result would depend on those choices.

### 10.3 Local determinants and global transitivity

The cone triangle behind (10.1) gives a canonical determinant isomorphism

$$
\operatorname{Det}(C_{\min}^\bullet)
\otimes
\operatorname{Det}\left(\bigoplus_{v\in S}C^\bullet(F_v,M)\right)
\simeq
\operatorname{Det}(C^\bullet(G_{F,S},M))
\otimes
\bigotimes_{v\in S}\operatorname{Det}(U_v^\bullet).
\tag{10.7}
$$

The order of factors follows the exact triangle; reversing two odd virtual-rank factors can introduce a sign. Formula (10.7) is stable under replacing any local complex by a quasi-isomorphic one and under flat coefficient extension.

Taking graded degrees in (10.7) gives the Euler characteristic of the defining cone. After global duality and the global Euler-characteristic formula are used, this degree is

$$
\deg\mathscr D_{\min}
=-\left(
h^1_{\mathcal L}(F,M)
-h^1_{\mathcal L^\perp}(F,M(1))
\right).
\tag{10.7a}
$$

The negative of (10.7a) is then rewritten by (5.10): finite places away from $\ell$ contribute zero, coefficient-prime places contribute $+f_v$, and real places contribute $-1$. Those entries are the normalized Wiles-defect ledger obtained after combining the global Euler characteristic with the local complexes. They are not, without a further normalization of $U_v^\bullet$, assertions that the raw quotient complexes $C^\bullet(F_v,M)/U_v^\bullet$ individually have those virtual ranks. Their total cancels by (5.11), which is exactly the degree-zero conclusion (10.6).

For the framed problem, one tensors (10.7) with the determinant lines of the local gauge complexes and divides by the global gauge line. Taking graded degrees gives precisely the correction in (5.6). Thus the determinant formalism and the explicit framing ledger agree.

### 10.4 The automorphic determinant

The global perfect pairing (7.5) identifies $M^{\min}$ with the full dual of $M^{\dagger,\min}$. On the selected saturated branch, consider the two-term complex

$$
K_{\lambda}=
\left[
L\longrightarrow\operatorname{Hom}_{\mathcal O}(L^\dagger,\mathcal O)
\right]
\tag{10.8}
$$

in degrees $-1$ and $0$. It becomes acyclic over $E$, so its determinant line has a canonical generic trivialization. The pairing map supplies an integral determinant section. If the ranks are $r$, Smith normal form yields

$$
v_\varpi(\det K_{\lambda})
=\operatorname{length}_{\mathcal O}\Psi_M.
\tag{10.9}
$$

Under the saturation and multiplicity hypotheses of Section 9.4, this becomes

$$
v_\varpi(\det K_{\lambda})
=r\,\operatorname{length}_{\mathcal O}\Psi_T.
\tag{10.10}
$$

Thus the automorphic congruence number is genuinely a determinant: it is the divisor of the branch-restricted pairing relative to its generic perfect trivialization.

For instance, if suitable bases make the restricted pairing matrix

$$
\begin{pmatrix}\varpi^2&0\\0&\varpi^5\end{pmatrix},
$$

then the cokernel has elementary divisors $\mathcal O/(\varpi^2)$ and $\mathcal O/(\varpi^5)$, and the determinant section has valuation seven. The determinant records the sum of congruence depths, not merely the number of nonunit directions. A rectangular matrix would have no single determinant; one would instead retain its maximal-minor Fitting ideal or the full perfect complex.

### 10.5 What can be compared before patching

Both sides now have determinant data, but no canonical isomorphism between them has yet been constructed. The Selmer determinant records tangent and obstruction directions of the global deformation functor. The automorphic determinant records the integral failure of a generic branch to split from its companions. The surjection $\theta$ induces the conormal map (9.5), and hence a map on cotangent determinant lines when the relevant complexes are perfect. This yields the direction of the inequalities (9.11).

What is missing is a proof that no determinant is lost in passing from global deformation equations to automorphic congruences. Such a proof requires a system of modules and rings over varying auxiliary levels, together with support and freeness. It is therefore correct here to record

$$
\operatorname{length}\Phi_R
\ge\operatorname{length}\Phi_T
\ge\operatorname{length}\Psi_T,
$$

and incorrect to identify the two determinant sections. The later patched complex supplies the comparison that makes equality rigid.

## 11. Exact Taylor--Wiles numerical data

### 11.1 The integer that auxiliary primes must address

The absolute number

$$
q=h^1_{\mathcal L^\perp}(F,M(1))
\tag{11.1}
$$

is the auxiliary-prime target. By balance it is also

$$
q=h^1_{\mathcal L}(F,M).
\tag{11.2}
$$

The equality has a conceptual meaning. There are as many first-order minimal deformations as dual reciprocity obstructions. An auxiliary system should impose $q$ independent conditions on the dual group while introducing $q$ controlled diamond directions on the primal side.

This $q$ is not $q_T$ from (5.9). The latter depends on the arbitrary framing set and bounds a relative presentation; (11.1) is intrinsic to the unframed minimal problem.

### 11.2 The shape of an admissible auxiliary prime

Fix $N\ge1$. A finite place $x\notin S$ has the required local shape at depth $N$ if

$$
q_x\equiv1\pmod{\ell^N},
\tag{11.3}
$$

$\bar\rho$ is unramified at $x$, and $\bar\rho(\Phi_x)$ has two distinct eigenvalues $\alpha_x,\beta_x\in k$. Choose and retain an ordering of those eigenvalues. The ordering selects a residual Frobenius line and removes the Weyl ambiguity in the local deformation condition.

Let $\Delta_x$ be the maximal $\ell$-power quotient of the residue multiplicative group $k_x^\times$, or its quotient of order $\ell^N$ when a fixed finite depth is desired. Local reciprocity identifies $\Delta_x$ with the allowed tame inertia quotient. Its group algebra has augmentation

$$
\mathcal O[\Delta_x]\longrightarrow\mathcal O.
\tag{11.4}
$$

Killing the augmentation restores the unramified minimal condition at $x$.

The existence of enough primes satisfying both (11.3) and the required cohomological detection conditions is a separate auxiliary-prime theorem. Here we specify and compute the data such primes must carry.

### 11.3 Local auxiliary deformation rings

At a place $x$ as above, the ordered auxiliary condition requires a stable rank-one direct summand lifting the $\alpha_x$-line. In a compatible basis, inertia acts through

$$
\begin{pmatrix}
\chi_x&0\\0&\delta|_{I_x}\chi_x^{-1}
\end{pmatrix},
\tag{11.5}
$$

where $\chi_x$ is the universal character of $\Delta_x$. Frobenius preserves the two lines and lifts the ordered eigenvalues, with determinant fixed by $\delta$.

The clean distinct-root calculation shows that the framed auxiliary local ring is formally smooth over $\mathcal O[\Delta_x]$ in the three framing directions. Relative to the unramified minimal local ring, it adds exactly one unframed tangent direction, the tame character direction. At the augmentation $\chi_x=1$, it specializes to the minimal unramified condition.

This one-dimensional difference is the key numerical fact:

$$
\dim L_x^{\mathrm{aux}}-h^0(F_x,M)=1,
\qquad
\dim L_x^{\min}-h^0(F_x,M)=0.
\tag{11.6}
$$

The determinant is held fixed throughout, so there is only one free tame character, not two.

### 11.4 Diamond groups and augmentation ideals

For a set $Q_N$ of auxiliary primes, put

$$
\Delta_{Q_N}=\prod_{x\in Q_N}\Delta_x,
\qquad
S_N=\mathcal O[\Delta_{Q_N}].
\tag{11.7}
$$

Its augmentation ideal $\mathfrak a_N$ is generated by $|Q_N|$ group elements minus one, subject to their finite-order relations. If $|Q_N|=r$ is fixed and each $\Delta_x$ is replaced by its quotient of order $\ell^N$, then abstractly $\Delta_{Q_N}\simeq(\mathbf Z/\ell^N\mathbf Z)^r$. The formal limiting diamond source and completed group algebra are

$$
\Delta_\infty\simeq\mathbf Z_\ell^r,
\qquad
S_\infty=\mathcal O[[\Delta_\infty]]
\simeq\mathcal O[[z_1,\ldots,z_r]].
\tag{11.8}
$$

For the balanced auxiliary system below, $r=q$.

This is an inverse limit of the abstract marked source groups, not a claim that the arithmetic prime sets $Q_N$ are nested or carry transition maps. The later patching construction obtains coherence from compatible finite marked shadows.

The variables $z_i$ are the limiting diamond directions. The specialization

$$
S_\infty/(z_1,\ldots,z_r)\simeq\mathcal O
\tag{11.9}
$$

is the algebraic form of returning to minimal level.

On the automorphic side, the deeper auxiliary level must carry a free action of $\Delta_{Q_N}$ compatible with the local ordered characters. The Hecke module at that level is therefore an $S_N$-module. Freeness or balancedness over $S_N$ is not automatic from the group action; it is part of the later system construction.

### 11.5 The generator--relation ledger

Assume a set $Q$ of $q$ primes has been chosen so that restriction to the selected one-dimensional local dual quotients is injective on the minimal dual Selmer group. Replacing the minimal local condition at each $x\in Q$ by the auxiliary condition makes the orthogonal local condition one dimension smaller. The injectivity hypothesis therefore gives

$$
H^1_{\mathcal L_Q^\perp}(F,M(1))=0.
\tag{11.10}
$$

The Wiles formula changes by $+1$ at each of the $q$ primes, using (11.6). Hence

$$
h^1_{\mathcal L_Q}(F,M)
-h^1_{\mathcal L_Q^\perp}(F,M(1))=q.
\tag{11.11}
$$

Combining (11.10) and (11.11) gives

$$
\boxed{
h^1_{\mathcal L_Q}(F,M)=q,
\qquad
h^1_{\mathcal L_Q^\perp}(F,M(1))=0.}
\tag{11.12}
$$

These $q$ primal directions match the $q$ generators of the augmentation ideal of $S_\infty$. Thus the exact unframed ledger is

| datum | minimal problem | auxiliary problem |
|---|---:|---:|
| primal Selmer dimension | $q$ | $q$ |
| dual Selmer dimension | $q$ | $0$ |
| local diamond directions | $0$ | $q$ |
| defect primal minus dual | $0$ | $q$ |

The apparent constancy of the primal dimension is important. Auxiliary primes do not merely add $q$ new arbitrary tangent directions; the new local directions and the $q$ killed global reciprocity constraints compensate. At finite level, killing $\mathfrak a_N$ recovers the minimal local conditions. In the inverse limit, the $q$ surviving tangent directions are precisely the regular parameters of $S_\infty$.

As a small numerical model, suppose the minimal primal and dual Selmer groups both have dimension two. Choose two ordered primes $x_1,x_2$ such that evaluation of a dual basis on their selected local quotients has invertible $2\times2$ matrix. The new dual Selmer group is zero. Each prime adds one to the local defect, so the new primal dimension is two. The limiting diamond algebra is $\mathcal O[[z_1,z_2]]$. Choosing only one detecting prime would leave at least a one-dimensional dual kernel; choosing three primes could be useful for other purposes, but the third direction would be surplus relative to the minimal numerical target. The canonical balanced count is exactly two.

With frames at $T$, add the same gauge correction to both minimal and auxiliary presentations. The local auxiliary factors replace their minimal counterparts, and the absolute dual count changes as above; $q_T$ must still be recomputed from its relaxed-at-$T$ definition. No formula obtained by simply substituting $q$ for $q_T$ is valid.

### 11.6 Adequacy and the prime-five boundary

The cyclotomic restricted image is adequate under the standing hypothesis $\ell\ge7$. Its semisimple spanning property supplies elements that detect nonzero adjoint cohomology directions, and its first-cohomology vanishings remove finite-image obstructions in the prime-selection argument. These are exactly the image-theoretic inputs behind the desired injectivity in (11.10).

At $\ell=5$, absolute irreducibility is not a sufficient replacement. A projective $A_5\simeq\operatorname{PSL}_2(\mathbf F_5)$ image in its natural characteristic-five realization has a nonzero one-dimensional adjoint $H^1$ and can fail adequacy. Large images over larger fields also require their own verification. At $\ell=3$ and $2$, further exceptional coincidences and determinant problems occur. Therefore the clean minimal package and its later patching use $\ell\ge7$; there is no blanket small-prime corollary hidden in the notation.

## 12. Coefficient changes and normalization checks

### 12.1 Extension of the coefficient DVR

Let $\mathcal O\to\mathcal O'$ be a finite extension of complete DVRs, with residue field enlarged as necessary. Every represented local condition in the clean datum is compatible with this coefficient change. If the residue field changes, write $R^{\min}_{\mathcal O'}$ for the intrinsic deformation ring of $\bar\rho\otimes_k k'$ at the selected residual point. Scalar extension of the old universal family gives a canonical map in the direction

$$
R^{\min}_{\mathcal O'}
\longrightarrow
\left(
R^{\min}_{\mathcal O}\widehat\otimes_{\mathcal O}\mathcal O'
\right)_{\mathfrak n'}^\wedge,
\tag{12.1}
$$

where $\mathfrak n'$ is the closed point selected by the extended residual representation. This map is an isomorphism when the residue field is unchanged and one merely restricts the old functor to $\mathcal O'$-algebras. For a genuine residue extension it is an isomorphism only when an effective scalar-extension theorem proves that every deformation of $\bar\rho\otimes_k k'$ descends from the scalar-extended universal family. Compatibility of the local conditions alone does not prove that assertion. Whenever completed base change is identified with the intrinsic ring below, this effective hypothesis and the selected local factor are understood.

The type lattices, companion pairings, automorphic modules, and Hecke operators base-change explicitly. Because $\mathcal O'$ is flat and the automorphic module is finite free, the faithful Hecke image base-changes faithfully; a subsequent localization must still be branch preserving. Nonflat reduction would require a separate saturation argument.

If the ramification index is $e$, finite lengths satisfy

$$
\operatorname{length}_{\mathcal O'}(N\otimes_{\mathcal O}\mathcal O')
=e\,\operatorname{length}_{\mathcal O}(N)
\tag{12.2}
$$

for a finite-length $\mathcal O$-module $N$, when lengths are normalized by the respective uniformizers. Thus raw congruence lengths depend on the coefficient normalization; Fitting and congruence ideals base-change more invariantly.

For example, if $N=\mathcal O/(\varpi^m)$ and $\varpi=u(\varpi')^e$ in $\mathcal O'$, then

$$
N\otimes_{\mathcal O}\mathcal O'
\simeq\mathcal O'/((\varpi')^{em}),
$$

which has $\mathcal O'$-length $em$. This is the concrete reason an unqualified statement that “the congruence number is unchanged after enlarging coefficients” is false.

Adequacy is preserved under finite extension of the residual coefficient field. Absolute irreducibility on the cyclotomic restriction must hold before the extension; coefficient extension changes coordinates, not the kernel of the Galois representation.

### 12.2 Determinant twists and Frobenius conventions

Twisting every representation by a fixed character changes trace and determinant according to

$$
\operatorname{tr}(\rho\otimes\chi)(g)
=\chi(g)\operatorname{tr}\rho(g),
\qquad
\det(\rho\otimes\chi)(g)=\chi(g)^2\det\rho(g).
\tag{12.3}
$$

Accordingly, a twist changes both the central character on the automorphic module and the fixed determinant in the deformation problem. It cannot be applied to one side alone.

For geometric Frobenius, the polynomial is (1.1). If $F_v=\Phi_v^{-1}$ is arithmetic Frobenius, then a matrix $A$ with polynomial $X^2-tX+d$ has inverse with polynomial

$$
X^2-d^{-1}tX+d^{-1}.
\tag{12.4}
$$

On a covariant Tate module there is also the visible Tate twist supplied by the comparison with $H^1(1)$. The common correspondence theorem gives the exact converted expression

$$
F_v^2-S_v^{-1}T_vF_v+q_vS_v^{-1}=0.
\tag{12.5}
$$

Equations (1.1) and (12.5) are compatible; mixing their conventions would put $q_v$ or $S_v$ on the wrong side of the determinant identity.

### 12.3 Framed and unframed ledgers

The following table keeps the two deformation presentations separate.

| Feature | Unframed problem | Problem framed at $T$ |
|---|---|---|
| representing ring | $R^{\min}$ | $R^{\square_T,\min}$ |
| tangent | $H^1_{\mathcal L}(F,M)$ | global cocycles plus local frame choices |
| base ring | $\mathcal O$ | $R_{\mathrm{loc}}^{\min}$ |
| generator count | intrinsic tangent count | $g_T$ of (5.6) |
| obstruction target | absolute dual Selmer, with endpoint terms | relaxed-at-$T$ dual group of dimension $q_T$ |
| framing correction | none | $\sum h^0(F_v,\operatorname{ad}\bar\rho)-h^0(F,\operatorname{ad}\bar\rho)$ |

Frames do not change the automorphic Hecke algebra. A framed comparison map can be obtained only after choosing bases for the local Hecke-valued representations; changing those bases changes the map by the expected formally smooth gauge action. The canonical comparison statement is therefore the unframed map (8.7).

### 12.4 Failure tests

Several short tests detect most malformed versions of the minimal problem.

1. If the sum of finite-flat local contributions is not $[F:\mathbf Q]$, either a local degree or a Hodge-weight hypothesis has been misstated.
2. If real places contribute zero to (5.10), ordinary positive-degree cohomology has been confused with the modified Euler characteristic.
3. If $R^{\min}\to\mathbb T^{\min}$ points in the opposite direction, functorial variance has been reversed.
4. If surjectivity uses a $U_v$ not generated by good traces and fixed determinants, the target algebra is too large for the argument.
5. If a local special condition is phrased as $N\ne0$ on all Artinian quotients, it is not a closed deformation condition.
6. If $q$ is declared zero because the problem is balanced, difference zero has been confused with two vanishing groups.
7. If a module congruence length is divided by a multiplicity without saturation and a primitive pairing, the resulting ring congruence number is unsupported.
8. If the degree-zero Selmer determinant is called canonically trivial, a choice of bases has been hidden.
9. If adequacy is asserted at five solely from absolute irreducibility, the icosahedral exception has been missed.
10. If the minimal equality is used to prove the pairing, congruence, or support hypotheses needed for patching, the argument is circular.

## 13. The complete minimal comparison package

### 13.1 Main construction theorem

**Theorem 13.1 (minimal deformation--Hecke comparison).** Assume the standing hypotheses of Section 1.4 and the exact local matching of Section 6.5. Then:

1. the fixed-determinant minimal deformation functor is represented by a complete Noetherian local $\mathcal O$-algebra $R^{\min}$;
2. the selected definite-quaternion module $M^{\min}$ is finite free over $\mathcal O$ and faithful for a complete local finite-flat Hecke algebra $\mathbb T^{\min}$;
3. its companion module is paired perfectly with it, with inverse-double-coset adjunction;
4. there is a Hecke-valued representation $\rho_{\mathbb T}$ of determinant $\delta$ satisfying every minimal local condition on every Artinian quotient and satisfying (8.4) at all good places;
5. universality and trace generation give a surjection

$$
R^{\min}\twoheadrightarrow\mathbb T^{\min};
$$

6. every integral generic branch supplies a compatible augmentation, cotangent module, congruence ideal, and automorphic determinant section as in Chapters 9 and 10.

**Proof.** Representability and the universal ring are established in Chapter 5 from the global Schur hypothesis and the represented local quotients. Chapters 6 and 7 construct the finite-free automorphic module, its faithful image algebra, and the perfect primary--companion pairing. Reduced generic fiber and branchwise weight-two attachment give the product Galois representation; trace-coordinate descent and residual absolute irreducibility give $\rho_{\mathbb T}$ in Chapter 8. Closed local factorization, the integral finite-flat comparison, and exact type matching put this family in the global minimal functor. Universality produces the comparison map, and (8.6) together with trace generation proves surjectivity. Generic isolation and the perfect pairing give the augmentation and determinant constructions of Chapters 9 and 10. $\square$

The theorem deliberately does not assert injectivity, Hecke freeness of $M^{\min}$, a Gorenstein property, or a complete-intersection property.

### 13.2 Numerical theorem

**Theorem 13.2 (balanced and auxiliary numerical package).** Under the same hypotheses, put $M=\operatorname{ad}^0\bar\rho$ and define $q$ by (11.1). Then

$$
h^1_{\mathcal L}(F,M)
=h^1_{\mathcal L^\perp}(F,M(1))=q.
\tag{13.1}
$$

For every framing set $T$, the ring $R^{\square_T,\min}$ has a presentation (5.13) with generator count (5.6) and relation bound $r_T\le q_T$, where $q_T$ is defined by (5.9). The Selmer determinant line has degree zero and the local determinant degrees cancel place by place as in (10.7).

If a set $Q$ of $q$ ordered auxiliary primes satisfies the local congruence, distinct-root, and dual-detection conditions of Chapter 11, then

$$
h^1_{\mathcal L_Q}(F,M)=q,
\qquad
h^1_{\mathcal L_Q^\perp}(F,M(1))=0,
$$

and its limiting diamond algebra is a power-series ring in exactly $q$ variables over $\mathcal O$.

**Proof.** The global duality formula is (5.10). Global invariants vanish by (2.4) and (2.6); finite places away from $\ell$ are neutral; coefficient-prime places sum to $[F:\mathbf Q]$; and the real places sum to its negative. This proves (13.1). The presentation and relation bound follow from the effective obstruction theory and the strict framing calculation. The determinant degree is the same alternating dimension formula expressed through the triangle (10.7). At the auxiliary primes, each local condition adds one to the defect. Dual detection kills the $q$-dimensional dual group, after which the modified Wiles formula forces the primal dimension to be $q$. Finally, the product of $q$ pro-$\ell$ cyclic diamond directions has completed group algebra $\mathcal O[[z_1,\ldots,z_q]]$. $\square$

### 13.3 Dependency closure

The construction uses the direct prerequisites in the following exact forms.

| Established infrastructure | Use in this volume | Hypotheses retained here |
|---|---|---|
| global deformation problems | represented conditioned rings, framed fiber products, Selmer tangents, Poitou--Tate formula, relation bounds | finite controlling set, fixed determinant with $\ell\ne2$, Schur residual representation, represented base-change-stable local conditions, effective obstruction theory |
| numerical criteria for $R=T$ | augmentation cotangents, congruence ideals, determinant inequality, surjective comparison protocol | finite-flat target, generically isolated augmentation, separable generic fiber, saturation and multiplicity when a module is used |
| Hecke algebras and congruences | faithful image, localization, finite flatness, generalized residual summand, pairings and branches | finite-free integral module; no automatic Hecke freeness, Gorensteinness, or reduced special fiber |
| Hecke correspondences on curves and Jacobians | common operator normalization, adjoints, geometric Frobenius polynomial | good split hyperspecial places, stable component union, exact right-double-coset orientation, required integral models |
| weight-two Galois attachment | branchwise rank-two representations, determinant, oddness, good polynomials, integral finite-flat lattices | noncharacter parallel weight two in a verified carrier; full cancellation in any surface realization; integral conclusions only with integral realization data |
| cotangent complexes and determinant lines | determinant of perfect complexes and triangles, two-term determinant length, base change | perfectness, correct grading and factor order; generic acyclicity for divisor calculations |
| integral local types and type lattices | primary and companion lattices, saturation, controlled represented components | places away from $\ell$, unit-valued labels, tame controlled types, clean residual regularity; no primitive wild cases |
| Hecke-valued reciprocity | descent from generic branches, integral local factorization, finite-flat Artinian quotients, trace-generated surjection | residual absolute irreducibility, reduced generic Hecke algebra, all branches verified, exact integral types and local compatibility |
| residual image classification and adequacy | adequacy of the cyclotomic restricted image and the small-prime boundary | $\ell\ge7$ and absolute irreducibility after cyclotomic restriction |

No auxiliary-prime existence theorem, patched-module theorem, support theorem, or later deformation--Hecke equality is used in Theorems 13.1 and 13.2. Chapter 11 computes the required shape and consequences of a detecting auxiliary set conditionally; construction of compatible sets and modules belongs to the next stage.

### 13.4 Boundary with minimal patching

The data passed forward are now exact:

$$
\left(
R^{\min}\twoheadrightarrow\mathbb T^{\min},
M^{\min},M^{\dagger,\min},
\langle\ ,\ \rangle,
q,
R_{\mathrm{loc}}^{\min},
\mathscr D_{\min}
\right).
\tag{13.2}
$$

At auxiliary level one must construct rings $R_{Q_N}$, Hecke algebras $\mathbb T_{Q_N}$, and modules $M_{Q_N}$ carrying the $\Delta_{Q_N}$-action; prove compatibility as $N$ varies; build patched objects over $S_\infty$; prove the necessary depth, support, and freeness statements; and then descend through the augmentation ideal. None of those achievements follows from the existence of (13.2) alone.

This boundary is mathematically productive. Every later equality can be checked against a fixed ledger: $q$ dual conditions must be killed, $q$ diamond variables must appear, local framed dimensions must match, determinant and central characters must remain fixed, and specialization must recover the exact minimal module rather than a rationally isomorphic lattice.

## 14. Conclusion

### 14.1 The arithmetic object now in hand

The minimal totally-real comparison problem is no longer a slogan. Its Galois side is the universal fixed-determinant deformation ring cut out by finite-flat low-weight conditions above $\ell$, exact minimal inertia and monodromy conditions away from $\ell$, and odd conjugacy classes at infinity. Its automorphic side is the faithful local Hecke order acting on a finite-free definite-quaternion module selected by primary integral type lattices and paired with their exact companions.

The two sides meet through a Hecke-valued rank-two representation. Good geometric Frobenius has polynomial $X^2-T_vX+q_vS_v$, the determinant is the fixed character $\delta$, and every Artinian quotient lies on the named local components. Universality therefore gives the surjection

$$
R^{\min}\twoheadrightarrow\mathbb T^{\min}.
$$

Its tangent theory is balanced for a genuinely arithmetic reason: the $[F:\mathbf Q]$ finite-flat directions above $\ell$ cancel the $[F:\mathbf Q]$ odd real-place contributions. The common dimension $q$ of primal and dual Selmer groups is not an error term to suppress; it is the exact size of the auxiliary system. A detecting set of $q$ ordered primes kills the dual group and replaces it with $q$ diamond directions. The Selmer determinant line records the same cancellation before dimensions are taken, while the automorphic pairing determinant records the integral congruence divisor of a selected branch.

What remains is sharply isolated. The structural inequalities point from deformation cotangents toward Hecke congruences, but injectivity requires proof that no determinant, depth, or support is lost. The next stage may now perform that proof without revisiting a hidden convention or repairing an ill-matched local condition. The complete input is a coherent arithmetic package: universal deformations, faithful Hecke operators, integral types, perfect companions, exact pairings, determinant lines, and the full Taylor--Wiles numerical ledger.
