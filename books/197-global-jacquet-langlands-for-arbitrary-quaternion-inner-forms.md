# Global Jacquet--Langlands for Arbitrary Quaternion Inner Forms

## Contents

1. [The comparison and its exact boundary](#1-the-comparison-and-its-exact-boundary)
   - [Why arbitrary real signature is the issue](#11-why-arbitrary-real-signature-is-the-issue)
   - [The two principal theorems](#12-the-two-principal-theorems)
   - [One separate parameter-theoretic boundary](#13-one-separate-parameter-theoretic-boundary)
   - [Logical order](#14-logical-order)
2. [Quaternion algebras of arbitrary real signature](#2-quaternion-algebras-of-arbitrary-real-signature)
   - [Ramification, parity, and anisotropy](#21-ramification-parity-and-anisotropy)
   - [Compactness does not mean compact at infinity](#22-compactness-does-not-mean-compact-at-infinity)
   - [Reduced norms and global characters](#23-reduced-norms-and-global-characters)
   - [The cyclic algebra of a Hermitian plane](#24-the-cyclic-algebra-of-a-hermitian-plane)
3. [A normalization ledger](#3-a-normalization-ledger)
   - [Frobenius and normalized induction](#31-frobenius-and-normalized-induction)
   - [Measures and fixed central character](#32-measures-and-fixed-central-character)
   - [Geometric and signed transfer](#33-geometric-and-signed-transfer)
   - [Good Hecke normalization](#34-good-hecke-normalization)
4. [Local orbital transfer before local representation transfer](#4-local-orbital-transfer-before-local-representation-transfer)
   - [Common regular geometry](#41-common-regular-geometry)
   - [The tree Euler function and arbitrary division tests](#42-the-tree-euler-function-and-arbitrary-division-tests)
   - [The regular-orbital quotients and the Abel transform](#43-the-regular-orbital-quotients-and-the-abel-transform)
   - [Reverse transfer and the scalar-germ extension](#44-reverse-transfer-and-the-scalar-germ-extension)
   - [Principal-series traces](#45-principal-series-traces)
   - [Singular germs and the scalar distribution](#46-singular-germs-and-the-scalar-distribution)
   - [The real transfer function](#47-the-real-transfer-function)
5. [The matched character-clean trace formula](#5-the-matched-character-clean-trace-formula)
   - [The exact test class](#51-the-exact-test-class)
   - [The compact inner-form expansion](#52-the-compact-inner-form-expansion)
   - [The two-place spectral cancellation on the split group](#53-the-two-place-spectral-cancellation-on-the-split-group)
   - [The geometric boundary terms](#54-the-geometric-boundary-terms)
   - [Matching elliptic rational classes](#55-matching-elliptic-rational-classes)
   - [The clean identity](#56-the-clean-identity)
6. [Globalizing one prescribed local representation](#6-globalizing-one-prescribed-local-representation)
   - [Arithmetic realization of a local field](#61-arithmetic-realization-of-a-local-field)
   - [Globalizing a division representation](#62-globalizing-a-division-representation)
   - [Globalizing a split discrete representation](#63-globalizing-a-split-discrete-representation)
   - [Finite-window separation](#64-finite-window-separation)
7. [Full finite local Jacquet--Langlands](#7-full-finite-local-jacquet--langlands)
   - [Construction in the division-to-split direction](#71-construction-in-the-division-to-split-direction)
   - [The character identity without an integral-lattice shortcut](#72-the-character-identity-without-an-integral-lattice-shortcut)
   - [Surjectivity](#73-surjectivity)
   - [The full local theorem](#74-the-full-local-theorem)
8. [The real correspondence and orientations](#8-the-real-correspondence-and-orientations)
   - [The compact and split characters](#81-the-compact-and-split-characters)
   - [The real local theorem](#82-the-real-local-theorem)
   - [Two active factors](#83-two-active-factors)
9. [Conductors, local factors, newvectors, and parameters](#9-conductors-local-factors-newvectors-and-parameters)
   - [Intrinsic division conductor](#91-intrinsic-division-conductor)
   - [The degree-two local zeta problem](#92-the-degree-two-local-zeta-problem)
   - [Convergence and rational continuation](#93-convergence-and-rational-continuation)
   - [The local functional equation and canonical factors](#94-the-local-functional-equation-and-canonical-factors)
   - [The split Whittaker bridge and Fourier exponent](#95-the-split-whittaker-bridge-and-fourier-exponent)
   - [The division Euler factor and Fourier conductor](#96-the-division-euler-factor-and-fourier-conductor)
   - [The global matrix-coefficient integral](#97-the-global-matrix-coefficient-integral)
   - [Comparison for every additive character](#98-comparison-for-every-additive-character)
   - [The split newvector](#99-the-split-newvector)
   - [Weil--Deligne parameters](#910-weil--deligne-parameters)
10. [The two global spectra and exceptional characters](#10-the-two-global-spectra-and-exceptional-characters)
    - [Fixed central character spaces](#101-fixed-central-character-spaces)
    - [The exceptional spectrum](#102-the-exceptional-spectrum)
    - [Why local transfer of a norm character is not global transfer](#103-why-local-transfer-of-a-norm-character-is-not-global-transfer)
11. [Forward global transfer](#11-forward-global-transfer)
    - [Producing the split constituent](#111-producing-the-split-constituent)
    - [Recovering every local component](#112-recovering-every-local-component)
    - [Definition and compatibilities](#113-definition-and-compatibilities)
12. [Reverse transfer and the exact image](#12-reverse-transfer-and-the-exact-image)
    - [Necessity of the local condition](#121-necessity-of-the-local-condition)
    - [Sufficiency](#122-sufficiency)
    - [The global theorem](#123-the-global-theorem)
13. [The cohomological range](#13-the-cohomological-range)
    - [General real weights](#131-general-real-weights)
    - [Exactly two active real places](#132-exactly-two-active-real-places)
14. [Levels, good Hecke modules, and rationality](#14-levels-good-hecke-modules-and-rationality)
    - [Exact conductor and the global newvector](#141-exact-conductor-and-the-global-newvector)
    - [Good Hecke modules](#142-good-hecke-modules)
    - [Algebraicity from the actual arithmetic input](#143-algebraicity-from-the-actual-arithmetic-input)
    - [Exact scope of algebraic conjugation](#144-exact-scope-of-algebraic-conjugation)
15. [Transfer between two quaternion inner forms](#15-transfer-between-two-quaternion-inner-forms)
    - [The common split intermediary](#151-the-common-split-intermediary)
    - [Definite to two-active signature](#152-definite-to-two-active-signature)
16. [The two-active-place surface interface](#16-the-two-active-place-surface-interface)
    - [The exact quaternion algebra](#161-the-exact-quaternion-algebra)
    - [The quaternionic theorem needed by the surface](#162-the-quaternionic-theorem-needed-by-the-surface)
    - [The common-norm intermediary](#163-the-common-norm-intermediary)
    - [What the four orientations do and do not say](#164-what-the-four-orientations-do-and-do-not-say)
17. [Dependency ledger and conclusion](#17-dependency-ledger-and-conclusion)
    - [Exact direct dependency row](#171-exact-direct-dependency-row)
    - [What is now proved](#172-what-is-now-proved)
    - [The proposed prerequisite split](#173-the-proposed-prerequisite-split)
    - [Conclusion](#174-conclusion)


## 1. The comparison and its exact boundary

### 1.1 Why arbitrary real signature is the issue

Let $F$ be a number field, let $D/F$ be a quaternion algebra, and write

$$
G_D=D^\times,
\qquad
G=\operatorname{GL}_{2/F}.
\tag{1.1}
$$

At a split place the two groups are isomorphic. At a division place their regular semisimple classes still have a common elliptic part: $d\in D_v^\times$ and $g\in\operatorname{GL}_2(F_v)$ match when their reduced characteristic polynomials agree. Jacquet--Langlands turns that common regular geometry into a correspondence of representations.

The global source need not be totally definite. If $D$ is a division algebra over $F$, Book 93 proves that

$$
Z_D(\mathbf A_F)D^\times(F)\backslash D^\times(\mathbf A_F)
\tag{1.2}
$$

is compact. Split real factors make (1.2) a positive-dimensional compact orbifold; they do not create a rational parabolic. This is the distinction needed for the Hermitian surface of Book 129, whose derived quaternion algebra is split at two real places.

There is a second, genuinely local issue. Books 80--84 prove local Langlands and local Jacquet--Langlands only for principal, special, and selected dihedral representations. Book 82 classifies every division representation by finite Clifford data, but Book 84 explicitly excludes ramified dyadic and primitive wild character comparison. Book 112 transfers the orbital integrals of arbitrary division test functions, but just as explicitly does not attach a split representation to an arbitrary wild division type. Thus one may not pass from the orbital cocenter to a Grothendieck lattice and declare that an integral isometry has been obtained. The two lattices are different objects, and no such integral map is supplied by those books.

This book closes the representation-theoretic Jacquet--Langlands gap by a global argument. It first proves the exact matched trace formula needed below. It then globalizes one prescribed local representation and uses the trace formula twice, in the two directions, to construct and characterize the local correspondence. Primitive wild representations enter only as irreducible local representations; no fictitious tame quadratic label is assigned to them.

### 1.2 The two principal theorems

For a place $v$, put

$$
R(D)=\{v:D_v\text{ is division}\}.
\tag{1.3}
$$

At a finite division place the local theorem proved in Chapter 7 is a bijection

$$
\operatorname{JL}_v:
\operatorname{Irr}(D_v^\times)
\xrightarrow{\sim}
\operatorname{Irr}_{\mathrm{ess.disc}}(\operatorname{GL}_2(F_v)),
\tag{1.4}
$$

characterized, for matching regular elements, by

$$
\Theta_{\operatorname{JL}_v(\rho)}(g)
=-\Theta_\rho(d).
\tag{1.5}
$$

The target consists of Steinberg twists and supercuspidal representations, including every primitive wild supercuspidal. At a ramified real place Chapter 8 proves

$$
\operatorname{Sym}^n(\mathbf C^2)\otimes|\operatorname{Nrd}|^s
\longmapsto D_{n+2}\otimes|\det|^s.
\tag{1.6}
$$

For nonsplit $D$, the global theorem is

$$
\operatorname{JL}_D:
\mathcal A_0(D^\times)
\xrightarrow{\sim}
\left\{
\pi\in\mathcal A_{\mathrm{cusp}}(\operatorname{GL}_2/F):
\pi_v\text{ is essentially square-integrable for every }v\in R(D)
\right\}.
\tag{1.7}
$$

Here $\mathcal A_0(D^\times)$ is the discrete automorphic spectrum with the global one-dimensional norm characters removed. Every local component is the identity at a split place and (1.4) or (1.6) at a division place. Both sides have automorphic multiplicity one.

The theorem includes arbitrary finite wild behavior. Its proof does not infer existence from strong multiplicity one: strong multiplicity one is used only after the trace formula has produced a constituent.

### 1.3 One separate parameter-theoretic boundary

The full local correspondence of representations and the equality of independently defined nonarchimedean local factors will be proved here. A different theorem is needed to call the common object a two-dimensional Weil--Deligne parameter in every primitive wild case. Books 80--81 construct the Weil--Deligne language and the selected local Langlands correspondence, but they do not prove full local Langlands for $\operatorname{GL}_2$.

The exact missing prerequisite is therefore the following standalone theorem, not local Jacquet--Langlands itself.

**Required parameter theorem $\mathsf{LLC}_2^{\mathrm{wild}}$.** For every nonarchimedean local field $K$ of characteristic zero, there is a bijection from all irreducible smooth representations of $\operatorname{GL}_2(K)$ to all Frobenius-semisimple two-dimensional Weil--Deligne representations, with the established principal, special, and tame-dihedral normalizations, preserving determinants, twists, contragredients, Artin conductors, and the independently defined standard $L$-, $\epsilon$-, and $\gamma$-factors.

A proof requires the full simple-stratum and type classification on the split side, the primitive representations of the Weil group, the extension and rectifier calculation in residue characteristic two, and the comparison of zeta and Artin local constants. None is contained in Books 80--84. Chapter 9 states parameter consequences only under $\mathsf{LLC}_2^{\mathrm{wild}}$ and proves every conductor, factor, and newvector assertion used by the global theorem without it. Thus the local and global Jacquet--Langlands theorems are closed here, while the phrase “wild Weil--Deligne parameter” remains assigned to the precise proposed prerequisite volume rather than being manufactured from a tame label.

### 1.4 Logical order

The noncircular order is

$$
\begin{array}{c}
\text{regular orbital transfer, including scalar germs}\\
\Downarrow\\
\text{matched two-place trace formula}\\
\Downarrow\\
\text{globalization of one prescribed local representation}\\
\Downarrow\\
\text{full local character correspondence}\\
\Downarrow\\
\text{global transfer and its exact image}\\
\Downarrow\\
\text{levels, Hecke fields, and the surface interface}.
\end{array}
\tag{1.8}
$$

Orbital transfer is not representation transfer. A restricted tensor product of proposed local images is not assumed automorphic. A division congruence idempotent is never called a split $K_1$-projector. These distinctions will be retained at every stage.


## 2. Quaternion algebras of arbitrary real signature

### 2.1 Ramification, parity, and anisotropy

For every place $v$ of $F$, write

$$
\operatorname{inv}_v(D)=
\begin{cases}
0,&D_v\simeq M_2(F_v),\\
\frac12,&D_v\text{ is division}.
\end{cases}
\tag{2.1}
$$

Book 87 proves the reciprocity relation

$$
\sum_v\operatorname{inv}_v(D)=0
\quad\text{in }\mathbf Q/\mathbf Z,
\tag{2.2}
$$

and the local-global classification by these invariants. Consequently

$$
|R(D)|\equiv0\pmod2.
\tag{2.3}
$$

If $D$ is nonsplit, it is a division ring over $F$, so $R(D)$ is nonempty and (2.3) gives at least two ramified places. Those two places may both be finite. This is why a quaternion algebra split at every real place can still support the two-place trace argument.

For totally real $F$ of degree $d$, if $D$ is split at exactly $r$ real places, then

$$
|R_f(D)|+d-r\equiv0\pmod2.
\tag{2.4}
$$

Changing the invariant at two real places preserves the global relation. In particular, if $D_0$ is totally definite and $v_1,v_2$ are real places, there is a unique algebra $D_{12}$ with the same finite invariants and split exactly at $v_1,v_2$ among those two changed places.

### 2.2 Compactness does not mean compact at infinity

Put $PD^\times=D^\times/F^\times$. Conjugation on the trace-zero subspace identifies this group with the special orthogonal group of the anisotropic ternary reduced-norm form. Book 93, Theorem 2.1 gives

$$
PD^\times(F)\backslash PD^\times(\mathbf A_F)
\quad\text{compact}.
\tag{2.5}
$$

The proof uses anisotropy over $F$ and adelic lattice reduction. It never requires $PD^\times(F_\infty)$ to be compact. Equivalently, a rational parabolic would give a nonzero proper right ideal of $D$, impossible in a division ring. Thus a factor

$$
\operatorname{PGL}_2(\mathbf R)\times\operatorname{PGL}_2(\mathbf R)
\tag{2.6}
$$

at two active real places is compatible with a compact arithmetic quotient.

### 2.3 Reduced norms and global characters

At a finite division place reduced norm is surjective. At a Hamiltonian real place its image is $\mathbf R_{>0}$. Globally, Book 87 proves

$$
\operatorname{Nrd}(D^\times(F))
=F_D^\times
:=\{a\in F^\times:a_v>0\text{ at every ramified real }v\}.
\tag{2.7}
$$

If $\mathbf A_D^\times=\operatorname{Nrd}(D^\times(\mathbf A_F))$, weak approximation gives

$$
F_D^\times\backslash\mathbf A_D^\times
\xrightarrow{\sim}
F^\times\backslash\mathbf A_F^\times.
\tag{2.8}
$$

Hence every one-dimensional automorphic representation of $D^\times(\mathbf A_F)$ is uniquely

$$
\Xi_\eta=\eta\circ\operatorname{Nrd}
\tag{2.9}
$$

for a Hecke character $\eta$ of $F$. Its central character is $\eta^2$, because $\operatorname{Nrd}(z)=z^2$ on scalars. This square is why the central character alone does not identify the exceptional norm character.

### 2.4 The cyclic algebra of a Hermitian plane

Let $K/F$ be CM with conjugation $c$, and let

$$
W=b\langle1,-a\rangle,
\qquad a,b\in F^\times.
\tag{2.10}
$$

Define

$$
Q_a=(K/F,a)=K\oplus Kj,
\qquad j^2=a,
\qquad jx=c(x)j.
\tag{2.11}
$$

Then

$$
\operatorname{Nrd}(x+yj)
=N_{K/F}(x)-aN_{K/F}(y).
\tag{2.12}
$$

The explicit embedding of Book 129 identifies canonical quaternion conjugation with the adjoint involution of $W$, and taking norm one gives

$$
\operatorname{SL}_1(Q_a)\xrightarrow{\sim}\operatorname{SU}(W).
\tag{2.13}
$$

At a place where $K_v/F_v$ is a field,

$$
Q_{a,v}\text{ is split}
\Longleftrightarrow
a\in N_{K_v/F_v}(K_v^\times).
\tag{2.14}
$$

At a real place, $a_v>0$ gives signature $(1,1)$ and a split quaternion algebra; $a_v<0$ gives a definite plane and $\mathbf H$. Moreover, $W$ is isotropic over $F$ exactly when (2.12) has a nonzero zero, exactly when $Q_a$ has a zero divisor, exactly when $Q_a$ is split. Thus

$$
W\text{ anisotropic over }F
\Longleftrightarrow
Q_a\text{ is a division algebra over }F.
\tag{2.15}
$$

This criterion, rather than any count of compact real factors, is what makes the unitary surface compact.


## 3. A normalization ledger

### 3.1 Frobenius and normalized induction

At a finite place with residue cardinality $q_v$, let $\Phi_v$ be geometric Frobenius. We use

$$
\operatorname{rec}^{\mathrm{geom}}_v(\varpi_v)=\Phi_v,
\qquad
|\varpi_v|_v=q_v^{-1},
\qquad
|\Phi_v|=q_v^{-1}.
\tag{3.1}
$$

Book 6 uses arithmetic Artin reciprocity, so conversion to (3.1) means inversion at unramified finite places. The character formulation of Jacquet--Langlands is independent of this convention; local factors are not.

Normalized induction is

$$
I(\chi_1,\chi_2)
=i_B^{\operatorname{GL}_2}(\chi_1\boxtimes\chi_2),
\tag{3.2}
$$

with the half-modulus $|a/d|^{1/2}$. The centered special block corresponds to $\operatorname{St}\otimes\mu$ and satisfies

$$
L(s,\operatorname{St}\otimes\mu)=L(s+1/2,\mu).
\tag{3.3}
$$

On both inner forms a scalar $z$ has determinant or reduced norm $z^2$. Twisting by $\chi\circ\det$ or $\chi\circ\operatorname{Nrd}$ therefore multiplies the central character by $\chi^2$.

### 3.2 Measures and fixed central character

At almost every split finite place set

$$
\operatorname{vol}(\operatorname{GL}_2(\mathcal O_v))=1,
\tag{3.4}
$$

and at a finite division place set

$$
\operatorname{vol}(\mathcal O_{D_v}^\times)=1.
\tag{3.5}
$$

Fix the same measure on a matching quadratic torus in both groups and use quotient measures. For matching elements the Weyl discriminant

$$
|D(t)|_v
=\left|\frac{(\lambda_1-\lambda_2)^2}{\lambda_1\lambda_2}\right|_v
\tag{3.6}
$$

is literally the same.

For a unitary central character $\omega_v$, a test function satisfies

$$
f_v(zg)=\omega_v(z)^{-1}f_v(g)
\tag{3.7}
$$

and is compactly supported modulo the center. Its action is integrated over the central quotient. Algebraic nonunitary data are first twisted to a unitary line and twisted back after the comparison.

### 3.3 Geometric and signed transfer

For a finite division place, write $d\leftrightarrow g$ when the two elements have the same separable reduced characteristic polynomial. A geometric transfer of $f^D$ satisfies

$$
O_g(f^G)=O_d(f^D)
\quad(d\leftrightarrow g),
\qquad
O_g(f^G)=0
\quad(g\text{ split regular}).
\tag{3.8}
$$

The representation character identity has the sign $-1$. It is convenient in spectral formulas to use the signed transfer

$$
f^\sharp=-f^G,
\tag{3.9}
$$

so that

$$
O_g(f^\sharp)=-O_d(f^D).
\tag{3.10}
$$

There is one such sign at every member of $R(D)$. Parity gives

$$
\prod_{v\in R(D)}(-1)=1.
\tag{3.11}
$$

We use geometric transfer when displaying characters and signed transfer in global spectral identities. No sign appears at a split place.

### 3.4 Good Hecke normalization

At a split unramified finite place, Book 90 defines the raw operators

$$
T_v=[K_v\operatorname{diag}(\varpi_v,1)K_v],
\qquad
S_v=[K_v\varpi_v I K_v],
\tag{3.12}
$$

with $\operatorname{vol}(K_v)=1$. The integral polynomial is

$$
P_v(X)=1-T_vX+q_vS_vX^2.
\tag{3.13}
$$

If the spherical line has eigenvalues $t_v,s_v$, this becomes $1-t_vX+q_vs_vX^2$. Identity transfer at a split place preserves the raw double cosets, so no square root of $q_v$ and no transfer sign enters this polynomial.


## 4. Local orbital transfer before local representation transfer

### 4.1 Common regular geometry

For an element $x$ in either degree-two algebra put

$$
P_x(X)=X^2-\operatorname{Trd}(x)X+\operatorname{Nrd}(x).
\tag{4.1}
$$

On the split algebra these are ordinary trace and determinant. If $P_x$ is separable and irreducible, the centralizer is the quadratic field $F_v[X]/(P_x)$. Rational conjugacy is determined by $P_x$: on the split side this is rational canonical form, and on the division side it is conjugacy of embeddings of a maximal subfield. Split regular classes occur only in the split group.

Book 112 constructs transfers without assuming a representation correspondence. On a compact regular set, a transverse slice to conjugacy makes $(\operatorname{tr},\det)$ a submersion. A bump divided by its orbit Jacobian prescribes a locally constant orbital transform, and a finite disjoint partition patches the result. Near the singular set the rank-one tree supplies the missing Euler function.

### 4.2 The tree Euler function and arbitrary division tests

Let $K=\operatorname{GL}_2(\mathcal O)$ and let $I$ be the standard Iwahori. With the measures of Chapter 3, Book 112 proves that

$$
f_{\mathrm{ell}}=-2\mathbf1_K+(q+1)\mathbf1_I
\tag{4.2}
$$

has zero orbital integral on every split regular class and the required signed elliptic orbital integral. The proof is a weighted fixed-subtree calculation. A split torus fixes an apartment, whose compactly supported vertex-minus-edge Euler characteristic is zero. An unramified elliptic torus has a vertex core; a ramified elliptic torus has an edge core with the orientation-reversing half weight. Extra finite branches cancel in vertex-edge pairs. This remains valid in residue characteristic two because it uses the tree action, not a tame quadratic parametrization.

Conjugation averaging on the compact group $D_v^\times/F_v^\times$ preserves both traces and orbital integrals. On each norm-valuation shell the averaged division function becomes a locally constant function of trace and norm. Extending it from the closed division-admissible subset of the invariant quotient and multiplying by the even or odd tree kernel constructs a signed split transfer. Thus:

**Theorem 4.1 (full orbital transfer).** Every compact-mod-center smooth function on $D_v^\times$ has a geometric transfer satisfying (3.7)--(3.8), and hence, after multiplication by $-1$, a signed transfer satisfying (3.10). Conversely, every split test function with zero averaged Abel transform has a smooth division reverse with the opposite elliptic orbital integrals.  Equivalently, the regular-orbital quotients in (4.2m) are isomorphic.

The last word, “conversely,” is not a formal consequence of the forward construction.  It
requires the scalar-germ argument below.  We now give that argument, including the exact
quotients on which it lives.

### 4.3 The regular-orbital quotients and the Abel transform

Put $K=F_v$, $G=\operatorname{GL}_2(K)$, and let $D/K$ be division.  Fix a smooth central
character $\omega$.  Write $\mathcal H_G(\omega)$ and $\mathcal H_D(\omega)$ for the smooth
functions, compact modulo the center, satisfying

$$
f(zh)=\omega(z)^{-1}f(h).
\tag{4.2a}
$$

All statements may first be read on one compact determinant or reduced-norm fundamental
domain and then extended by (4.2a).  This removes any ambiguity about support in the scalar
direction.  Let

$$
\mathcal N_H(\omega)
=\{f\in\mathcal H_H(\omega):O_x(f)=0
\text{ for every regular semisimple }x\in H\},
\qquad H=G,D,
\tag{4.2b}
$$

and define the **regular-orbital quotient**

$$
\mathscr C_H^{\mathrm{orb}}(\omega)
=\mathcal H_H(\omega)/\mathcal N_H(\omega).
\tag{4.2c}
$$

This is the only quotient of test functions used in the reverse argument.  It is sometimes
called the regular orbital cocenter.  We do not identify it with the algebraic cocenter
$\mathcal H_H/[\mathcal H_H,\mathcal H_H]$, and neither quotient is identified with a
Grothendieck group of representations.

For $t=\operatorname{diag}(a,d)$ define the averaged normalized Abel transform

$$
\mathcal A f(t)
=\delta_B(t)^{1/2}
\int_{K_G}\int_{N(K)}f(k^{-1}tnk)\,dn\,dk.
\tag{4.2d}
$$

Here $\operatorname{vol}(K_G)=1$, $dn$ is the additive measure already used in the trace
formula, and the central covariance makes (4.2d) a compactly supported smooth function on
$T/Z$.  If $a\ne d$, representatives for $T\backslash G$ are $n(x)k$.  Since

$$
n(x)^{-1}tn(x)=t\,n((1-d/a)x),
$$

the change of variable $u=(1-d/a)x$ gives, with the quotient measures of Chapter 3,

$$
|D_G(t)|^{1/2}O_t(f)=\mathcal A f(t).
\tag{4.2e}
$$

Indeed $|D_G(t)|^{1/2}=|1-a/d|\,|a/d|^{-1/2}$, and the Jacobian
$|1-d/a|^{-1}$ leaves $|a/d|^{1/2}=\delta_B(t)^{1/2}$.  Thus no unnamed scalar is hidden in
(4.2e).  It follows first on the regular diagonal and then, by local constancy, everywhere that

$$
\mathcal A f=0
\quad\Longleftrightarrow\quad
O_t(f)=0\quad(t\text{ split regular}).
\tag{4.2f}
$$

Set

$$
\mathcal H_G^{\mathrm{Ab}=0}(\omega)=\ker\mathcal A,
\qquad
\mathscr C_G^{\mathrm{ell}}(\omega)
=\mathcal H_G^{\mathrm{Ab}=0}(\omega)/
\bigl(\mathcal N_G(\omega)\cap\mathcal H_G^{\mathrm{Ab}=0}(\omega)\bigr).
\tag{4.2g}
$$

The explicit signed transfer in Book 112 lies in this space.  To see this without a spectral
argument, write the conjugation average of a division function on its finitely many valuation
shells as $A_m(t,n)$.  With the sign convention (3.9), the prepared split function is

$$
f^\sharp=\sum_m A_m(\operatorname{tr},\det)F_m,
\tag{4.2h}
$$

where $F_{2r}=-2\mathbf1_{\varpi^rK_G}+(q+1)\mathbf1_{\varpi^rI}$ and
$F_{2r+1}=-(q+1)\mathbf1_{\varpi^r\eta I}$.  The tree calculation gives zero split regular
orbital integrals for every $F_m$; multiplication by an invariant function preserves this
property.  Equations (4.2e)--(4.2f) therefore give $\mathcal A f^\sharp=0$.  This proves actual
vanishing of the averaged Abel transform, rather than merely the vanishing of a finite list of
principal-series traces.

On the division side conjugation averaging preserves orbital integrals.  If $E=K[d]$, the
measure calculation in Book 112 is

$$
O_d(f^D)=\iota(E)f^{D,\natural}(d),
\qquad
\iota(E)=f(E/K)\in\{1,2\}.
\tag{4.2i}
$$

The value $2$ occurs for the unramified quadratic field and $1$ for a ramified field.  This
factor is part of the quotient measure; dropping it is exactly what makes a proposed reverse
transfer discontinuous near scalar reduction.

### 4.4 Reverse transfer and the scalar-germ extension

We first isolate the local statement that controls the discriminant-zero boundary.

**Lemma 4.2 (zero-Abel scalar germ).**  Let $h\in\mathcal H_G^{\mathrm{Ab}=0}(\omega)$ and let
$z\in K^\times$.  There are a neighborhood $V_z$ of the scalar $zI$ in the invariant quotient
and a scalar $b_z(h)$, locally constant as $z$ varies, such that for every regular elliptic
$g\in V_z$, with $E=K[g]$,

$$
O_g(h)=\iota(E)b_z(h).
\tag{4.2j}
$$

The assertion is compatible with central translation:
$b_{zz_0}(h)=\omega(z_0)^{-1}b_z(h)$ when the invariant neighborhood is multiplied by
$z_0$.

**Proof.** Translate to $z=1$ and use $1+X$ to identify a sufficiently small invariant
neighborhood with one in $M_2(K)$.  We first give the finite-level germ reduction.  Choose $n$
so that the left and right stabilizers of $h$ contain
$1+\varpi^nM_2(\mathcal O)$.  On the $r$th matrix annulus, with $r>n$, its conjugation integral
is a finite sum on

$$
\varpi^rM_2(\mathcal O)/\varpi^{r+n}M_2(\mathcal O).
\tag{4.2j-a}
$$

Separate a class in (4.2j-a) according to the first depth at which its trace and determinant
do not both vanish.  At that depth a semisimple reduction has a transverse
trace--determinant slice; Hensel lifting makes its slice contribution constant under every
deeper refinement.  Subtract these compatible slice contributions.  The classes left over
are precisely those whose first nonzero reduction is nilpotent.  Refining once more either
keeps a nonzero nilpotent reduction or sends it to zero.  Induction through the $n$ finite
refinement steps therefore expresses the orbital germ, exactly on a sufficiently deep
punctured box, as a linear combination of integration on the nonzero nilpotent orbit and
evaluation at zero.  This is the finite-quotient proof of the rank-two germ decomposition;
no representation character or density theorem enters.

There are no further coefficient functionals.  Every nonzero nilpotent matrix is conjugate to
$N_0=\left(\begin{smallmatrix}0&1\\0&0\end{smallmatrix}\right)$.  Restriction of an invariant
functional to this homogeneous orbit is a multiple of its quotient measure.  After subtracting
that multiple, the functional is supported at zero, where it is a multiple of evaluation
because nonarchimedean test functions have no point-supported derivatives.  The two
functionals are independent: a bump near $N_0$ separates the first from evaluation, and a
bump at zero separates evaluation from the first.  Thus the germ space is exactly
two-dimensional.  The division algebra has no nonzero nilpotent, so only the zero-orbit line
can extend to its invariant quotient.

What matters here is the restriction of these two germs to the split and elliptic annuli.  We
compute it on the tree, level by level.  For a split element the fixed set is a finite-width
tube about an apartment.  Its truncation has the same number of new terminal vertices and
terminal edges, so the compactly supported vertex-minus-edge sum is zero; enlarging the
truncation does not change it.  For an elliptic element, prune all terminal vertex--edge pairs.
The unramified torus leaves one vertex core.  The ramified torus leaves one unoriented edge
core, whose two orientations are identified by the stabilizer.  With the vertex,
oriented-edge, and centralizer measures of Chapter 3, the weighted Euler core contributes $1$
in the unramified case and $1/2$ in the ramified case.  The function
$-f_{\mathrm{ell}}$, which is twice that Euler function, therefore has ordinary orbital values

$$
\bigl(0\text{ on split},\;2\text{ on unramified elliptic},\;
1\text{ on ramified elliptic}\bigr).
\tag{4.2k}
$$

The other germ is detected by the nontrivial unipotent orbit and has nonzero restriction to
sufficiently deep split annuli.  To
see the latter directly in the translated group chart, take a bump supported near $1+N_0$.
For
$t_r=\operatorname{diag}(1+\varpi^r,1)$,

$$
n(x)^{-1}t_rn(x)
=t_rn\!\left(\frac{\varpi^r}{1+\varpi^r}x\right).
\tag{4.2ka}
$$

The set of $x$ with valuation $-r$ and prescribed leading unit carries the conjugate into that
bump and has positive quotient measure.  Thus the regular-nilpotent germ does not vanish on
the split annulus.
Consequently the kernel of restriction of the two-dimensional germ space to all split annuli
is exactly the line (4.2k).  This is the scalar-germ calculation; it is not a density assertion
about representations.

By (4.2f), the split regular orbital integrals of $h$ vanish.  Its germ therefore belongs to
the line (4.2k), with one coefficient $b_1(h)$.  The germ expansion is an exact equality on a
sufficiently small punctured invariant box, not merely a limit, so (4.2j) follows.  Translation
of the box shows that the coefficient is locally constant in $z$.  Central covariance gives
the final formula. $\square$

Away from the discriminant, ordinary slice descent says that $g\mapsto O_g(h)$ is a smooth
compactly supported function of $(\operatorname{tr}g,\det g)$.  The lemma supplies exactly the
extension that descent alone does not provide.

It is useful to name the resulting invariant-function space.  Let
$\mathscr O^{\mathrm{ell}}(\omega)$ consist of functions $\phi$ on the elliptic regular
trace--norm quotient which

1. are locally constant and compactly supported on each of the two projective valuation
   shells;
2. have the central covariance induced by (4.2a); and
3. for every scalar $z$ satisfy

   $$
   \phi(g)=\iota(K[g])b_z
   \tag{4.2j-b}
   $$

   on one punctured invariant neighborhood, for a locally constant family $b_z$.

The division invariant quotient is the closed elliptic quotient with the scalar points added.
Consequently division by $\iota(E)$ identifies $\mathscr O^{\mathrm{ell}}(\omega)$ with the
space of compactly supported locally constant functions on that closed quotient.  Lemma 4.2
says exactly that the elliptic orbital transform of every zero-Abel split test function lies in
$\mathscr O^{\mathrm{ell}}(\omega)$.

**Theorem 4.3 (reverse smooth transfer).**  For every
$h\in\mathcal H_G^{\mathrm{Ab}=0}(\omega)$ there is
$f^D\in\mathcal H_D(\omega)$ such that

$$
O_d(f^D)=-O_g(h)
\qquad(d\leftrightarrow g)
\tag{4.2l}
$$

on every regular class.  The class of $f^D$ in $\mathscr C_D^{\mathrm{orb}}(\omega)$ is unique.
Forward signed transfer and this reverse construction are inverse isomorphisms

$$
\mathscr C_D^{\mathrm{orb}}(\omega)
\xrightarrow{\ \sim\ }
\mathscr O^{\mathrm{ell}}(\omega)
\xleftarrow{\ \sim\ }
\mathscr C_G^{\mathrm{ell}}(\omega).
\tag{4.2m}
$$

The arrows in (4.2m) are, explicitly,
$[f^D]\mapsto(d\leftrightarrow g\mapsto-O_d(f^D))$ and
$[h]\mapsto(g\mapsto O_g(h))$.  Thus the minus sign belongs to the division arrow and agrees
with (3.9)--(3.10); no sign is absorbed into $\iota(E)$.

**Proof.**  On the regular division invariant set define

$$
a(\operatorname{Trd}d,\operatorname{Nrd}d)
=-\frac{O_g(h)}{\iota(K[d])},
\qquad d\leftrightarrow g.
\tag{4.2n}
$$

Slice descent makes $a$ locally constant away from the scalar locus.  Its support is compact on
each of the two projective valuation shells: a nonzero orbital integral forces the invariant
point to lie in the compact image of the support of $h$.  Near $zI$, Lemma 4.2 says that
(4.2n) is the constant $-b_z(h)$, independently of whether the approaching quadratic field is
ramified or unramified.  Hence $a$ extends uniquely to a compactly supported locally constant
function on the entire closed division invariant quotient, including its scalar points.

Pull back $a$ to a conjugation-invariant function $f^D$ on $D^\times$.  On a compact central
fundamental domain it is smooth and compactly supported; extend it by (4.2a).  Formula (4.2i)
now gives (4.2l).  Any two choices differ by an element of $\mathcal N_D(\omega)$, proving
uniqueness in the stated quotient.

Conversely, the construction (4.2h) transfers every division function, lies in
$\ker\mathcal A$, and, because $F_{2r}$ is the scalar translate of $f_{\mathrm{ell}}$ in the even shell, has the negative
of the germ vector (4.2k) multiplied by the division value.  Applying (4.2n), including its
displayed minus sign, recovers the division orbital class.  Starting with $h$, applying (4.2n), and then
(4.2h) recovers every regular orbital integral of $h$ and hence its class in
$\mathscr C_G^{\mathrm{ell}}(\omega)$.  This proves (4.2m). $\square$

There are two useful matrix-coefficient consequences.  If $\rho$ is any irreducible
representation of $D^\times$ and

$$
e_\rho(d)=\kappa_\rho\lambda(\rho(d^{-1})v),
\qquad \kappa_\rho\ne0,
\tag{4.2o}
$$

is a compact-mod-center coefficient with inverse central covariance, normalized if desired to
have trace one on $\rho$, its conjugation average
has a split representative of the form (4.2h).  That representative has zero Abel transform,
the signed elliptic orbital transform of $e_\rho$, and the scalar germ prescribed by (4.2j).
This holds for an arbitrary primitive wild $\rho$ because only smoothness, compactness of
$D^\times/K^\times$, and the tree were used.

In the other direction, if $\sigma$ is split supercuspidal, every compact-mod-center matrix
coefficient has zero two-sided parabolic constant term: a nonzero such term would give a
functional on the Jacquet module of $\sigma$.  It therefore lies in
$\mathcal H_G^{\mathrm{Ab}=0}(\omega)$ and Theorem 4.3 supplies its division-side reverse.  This
is the precise local input used for surjectivity in Chapter 7.

### 4.5 Principal-series traces

Let $f^\sharp$ be a transfer.  Equations (4.2f) and (4.2h) give
$f^{\sharp,B}=0$.  Taking the compact-picture trace, or equivalently applying Weyl integration,
therefore gives

$$
\operatorname{tr}I(\chi_1,\chi_2)(f^\sharp)=0
\tag{4.3}
$$

for every pair of quasicharacters for which the trace is defined, and then by meromorphic
continuation for the compact-mod-center family.  Conversely, Fourier inversion on the compact
part of $T/Z$ and Mellin inversion on its valuation coordinate recover $f^{\sharp,B}=0$ from
the vanishing of all these traces.  This is precisely the averaged Abel transform (4.2d), not
the unaveraged two-sided kernel of Book 109.

Equation (4.3) is trace-level cuspidality. It does not say that the two-sided induced operator is zero. Book 109 explains why one trace-zero factor does not kill a logarithmic-derivative scattering term. Chapter 5 uses two distinct ramified places; after differentiating a factored global intertwiner, every summand still contains an undifferentiated zero trace at the other place.

### 4.6 Singular germs and the scalar distribution

Near a scalar, the split group has two rank-one germs: the zero orbit and the regular nilpotent orbit. The division algebra has only the zero orbit. The tree Euler function kills the split regular-nilpotent coefficient. The remaining zero-orbit coefficient is constrained by regular matching; it cannot be altered on one side while all regular orbital integrals remain fixed.

The central term of a global trace formula is nevertheless a separate distribution. Book 112 constructs a matching pair of small central bumps $(b^D,b^\sharp)$ whose regular-nilpotent coefficient is zero and whose zero-orbit coefficients vary through a nonzero one-dimensional line. Linear combinations of these pairs allow the global scalar equality

$$
I_Z^D(f^D)=I_Z^G(f^\sharp)
\tag{4.4}
$$

to be imposed together with finitely many spectral interpolation conditions. Equation (4.4), not a casual equality of point values, is the scalar hypothesis used below.

### 4.7 The real transfer function

At a ramified real place the compact adjoint group is $\operatorname{SO}(3)$ and the split elliptic torus is $\operatorname{SO}(2)$. The Euler--Poincare function on the upper half-plane has zero hyperbolic orbital integrals. At an elliptic fixed point its Lefschetz index differs from the compact orbital integral by the rank-difference sign $-1$. Its singular endpoint germs have the same zero-orbit normalization. This supplies the archimedean instance of Theorem 4.1 and will yield the explicit character formula in Chapter 8.


## 5. The matched character-clean trace formula

### 5.1 The exact test class

Let $D/F$ be a quaternion division algebra and fix a unitary Hecke character $\omega$. Choose two distinct places

$$
u_1,u_2\in R(D),
\tag{5.1}
$$

which exist by parity. A **matched clean pair** is a finite sum

$$
(f^D,f^G)=
\sum_j\left(\bigotimes_v f^D_{j,v},
\bigotimes_v f^G_{j,v}\right)
\tag{5.2}
$$

with inverse $\omega$-central covariance and the following properties.

1. At a split place the factors are identical under the chosen splitting. At a division place $f^G_{j,v}$ is a signed transfer of $f^D_{j,v}$.
2. Almost every factor is the common hyperspecial unit. Every archimedean factor lies in the kernel-admissible Schwartz class of Books 109--110, and the sum is finite under left and right maximal-compact actions.
3. At $u_1,u_2$, the split regular orbital integrals and the averaged parabolic transforms vanish. By (4.2f), this holds for transferred factors, and (4.3) then gives the trace vanishing.
4. The scalar distributions satisfy (4.4).
5. In the finite level, infinity type, and Casimir window selected by the functions, the pair annihilates every global norm character $\eta\circ\operatorname{Nrd}$ with $\eta^2=\omega$ and every corresponding determinant character.

The last condition is not restrictive for spectral isolation. The precise completion statement is useful enough to record.

**Lemma 5.0 (completion of prescribed local factors).** Fix finitely many local matching factors which are to remain unchanged, and fix finitely many noncharacter automorphic trace coordinates.  Require zero Abel transform at two ramified places.  At one of those ramified places allow the matching function to vary while its listed representation traces are retained; if no ramified factor is allowed to vary, assume that (4.4) has already been imposed.  After adjoining finitely many split auxiliary places, there is a finite linear combination of factorizable matching pairs which retains every frozen factor and prescribed trace coordinate, satisfies (4.4), and annihilates all norm and determinant characters in the resulting window.

**Proof.** A fixed level, infinity type, and Casimir bound contains only finitely many irreducible constituents and only finitely many characters. If two of their global trace characters are distinct, strong determination on the division side or strong multiplicity one on the split side supplies a place outside the prescribed set where their local Hecke characters differ. Repeating this for the finite list gives split auxiliary places $w_1,\ldots,w_r$ at which the tensor product of the local Hecke algebras separates every required global coordinate. Lagrange interpolation in their finite-dimensional image produces mutually orthogonal trace selectors. Because these places are split, the same selectors are inserted on both sides and do not disturb transfer or either zero Abel factor.

It remains to impose the scalar equation.  Regard the difference of the two scalar
distributions as a linear functional on the allowed local matching space at the completion
place.  If that functional is zero, (4.4) is automatic.  Otherwise the matching central-bump
line of Section 4.6 contains a bump on which it is nonzero; scale that bump to impose (4.4).
The bump has zero regular-nilpotent germ and remains zero-Abel on the split side.  For each
local irreducible occurring in a listed global coordinate, its character is nonzero on some
regular noncentral open set.  For a higher-dimensional representation this follows from Schur
orthogonality on the compact projective division group: otherwise its character would have
zero $L^2$ norm, since the scalar set has Haar measure zero.  For a one-dimensional local norm
character, the character is a nonzero quasicharacter at every group element.  A regular
division slice supported in that open set therefore has nonzero trace on the chosen
representation and zero scalar distribution; its prepared signed transfer is zero-Abel and
has zero scalar germ.  Multiply this local matching pair globally by the auxiliary selector
for that one automorphic coordinate.  It corrects that coordinate without changing any other
listed coordinate.  Repeating finitely many times corrects every trace changed by the central
bump.  This is triangular: add the required central bump, then make the selector-supported
regular corrections, so the scalar equation stays solved. Frozen local factors were never
changed, and both zero-Abel conditions remain true. $\square$

We deliberately do not claim an identity for arbitrary matching functions. The class (5.2) is large enough to prescribe every finite collection of noncharacter trace coordinates, to vary one local factor freely through matching pairs, and to isolate either side of the global correspondence. Those are the exact operations used in Chapters 6--12.

### 5.2 The compact inner-form expansion

On the quotient (1.2), the automorphic kernel is

$$
K_{f^D}(x,y)=
\sum_{\gamma\in D^\times(F)/F^\times}
f^D(x^{-1}\gamma y).
\tag{5.3}
$$

Compactness makes the diagonal integral absolutely convergent after the fixed-center quotient. Its spectral and geometric expansions are

$$
\sum_{\Pi}m_D(\Pi)\operatorname{tr}\Pi(f^D)
=I_Z^D(f^D)
+\sum_{[\delta]_{\mathrm{reg}}}
a(\delta)O_\delta(f^D).
\tag{5.4}
$$

Every noncentral rational element of a division quaternion algebra generates a quadratic field, so there are no rational split-torus or noncentral unipotent terms. The coefficient $a(\delta)$ is the volume of the common projective torus quotient with the measures fixed in Chapter 3.

### 5.3 The two-place spectral cancellation on the split group

Books 109--110 prove the unrestricted simple trace formula when one factor is strongly cuspidal. For the transferred functions needed here, the local conclusion supplied a priori is the weaker vanishing (4.3). Rank one and the availability of two such places give the following exact extension.

**Lemma 5.1 (two-trace-cuspidal spectral reduction).** For a tensor in (5.2), every continuous and endpoint term in the regularized spectral expansion of $\operatorname{GL}_2$ vanishes. The only noncuspidal terms left before condition 5 is imposed are the one-dimensional residual representations $\eta\circ\det$ with $\eta^2=\omega$.

**Proof.** Fix inducing data $\chi$ and spectral variable $s$. On a fixed level and compact type, the global induced operator and normalized intertwiner factor as restricted tensors:

$$
I(\chi,s)(f^G)=\bigotimes_v I_v(\chi_v,s)(f_v^G),
\qquad
M(\chi,s)=\bigotimes_v M_v(\chi_v,s).
\tag{5.5}
$$

After choosing the spherical reference vectors, all but finitely many factors are scalar identities. Logarithmic differentiation gives a finite sum

$$
M^{-1}M'
=\sum_w
1\otimes\cdots\otimes(M_w^{-1}M_w')\otimes\cdots\otimes1,
\tag{5.6}
$$

including the derivative of the scalar normalizing product as the corresponding sum of local logarithmic derivatives. Taking the trace of the product with (5.5), the summand indexed by $w$ is

$$
\operatorname{tr}\!\left(M_w^{-1}M_w'I_w(f_w^G)\right)
\prod_{v\ne w}\operatorname{tr}I_v(f_v^G).
\tag{5.7}
$$

If $w=u_1$, the $u_2$ factor is zero; if $w=u_2$, the $u_1$ factor is zero; otherwise both are zero. Thus every logarithmic-derivative integral vanishes pointwise on the unitary axis. Weyl endpoint terms factor without more than one distinguished local intertwining factor and vanish by the same argument. Dominated convergence follows from the trace-class majorants of Book 109, so the zero pointwise integrand may be integrated and the finite compact-type exhaustion removed.

The remaining discrete noncuspidal spectrum of rank one consists exactly of the residues $\eta\circ\det$. They are not discarded by specializing a trace-zero principal series at a reducibility point; they are retained and evaluated separately. This is the distinction emphasized in Book 109. $\square$

### 5.4 The geometric boundary terms

The geometric reduction has a parallel two-place proof, but its input is the Abel transform rather than an induced-operator trace.

**Lemma 5.2 (two-place geometric reduction).** For a tensor in (5.2), the split regular and noncentral unipotent boundary distributions vanish. The geometric side consists of the scalar distribution and the elliptic regular classes.

**Proof.** Book 110 organizes the nonelliptic rational elements by their stable rational line. Unfolding the Borel incidence expresses the main term through the product of local averaged parabolic transforms. It is zero because either $u_1$ or $u_2$ contributes $f_v^B=0$.

The truncation discrepancy is obtained by differentiating a cutoff in the one split-height variable. After Poisson summation on the unipotent coordinate, every resulting global distribution is a sum in which at most one local Abel factor is differentiated. The undifferentiated factor at the other chosen place is zero, exactly as in (5.7). Book 110's cusp estimate bounds the discrepancy by $C\nu(f)T^{-\epsilon}$; the proof uses finite support to bound denominators, polynomial lattice counting, Schwartz decay at infinity, and the rank-one measure $dH/H^2$. These estimates apply tensor by tensor and survive a finite sum.

A split regular rational class also vanishes directly: at every place in $R(D)$ its local orbital integral is zero unless its quadratic algebra is a field. Noncentral repeated-root classes were included in the unfolded unipotent term. The scalar class was excluded before that unfolding and remains as $I_Z^G(f^G)$. $\square$

This proof retains the scalar term; it does not pretend that regular matching determines it automatically.

### 5.5 Matching elliptic rational classes

Let $\delta\in D^\times(F)$ be noncentral and put $E=F[\delta]$. Its reduced polynomial defines a unique elliptic rational conjugacy class $\gamma$ in $\operatorname{GL}_2(F)$. Conversely, a split rational class with nonzero transferred orbital integral has $E_v$ a field at every $v\in R(D)$.

A quadratic field $E/F$ embeds in $D$ exactly when no place in $R(D)$ splits in $E$. Indeed, scalar extension multiplies a local invariant by the local degree. A division invariant $1/2$ becomes zero over a quadratic field and remains $1/2$ on each factor of a split quadratic algebra. The local-global classification of Book 87 and conjugacy of embeddings then give existence and uniqueness of the rational division class.

Thus the contributing noncentral classes are in bijection. Their centralizers are the same torus, their volume coefficients agree, and their orbital integrals acquire one sign at each ramified place. Equation (3.11) removes the total sign. Condition 4 matches the scalar distributions. Therefore the two geometric sides are equal.

### 5.6 The clean identity

Before imposing condition 5, the spectral equality contains division norm characters and split residual determinant characters. At a finite division place, Book 84 proves

$$
\mu\circ\operatorname{Nrd}
\longleftrightarrow
\operatorname{St}\otimes\mu.
\tag{5.8}
$$

At a division place, additivity in the reducible standard module gives

$$
\operatorname{tr}(\mu\circ\det)(f_v^G)
=-\operatorname{tr}(\mu\circ\operatorname{Nrd})(f_v^D).
\tag{5.9}
$$

At a ramified real place the same equation follows directly from the Euler--Poincare calculation of Section 4.7: the full reducible principal module has trace zero, its discrete summand has the signed trace of the compact norm character, and additivity leaves the opposite trace on the determinant quotient. At a split place the traces agree. The even number of ramified places makes the global traces equal. Hence the character terms cancel pairwise, or vanish separately under condition 5.

We have proved the comparison used throughout the book.

**Theorem 5.3 (matched character-clean trace identity).** For every matched clean pair,

$$
\boxed{
\sum_{\Pi\in\mathcal A_0(D,\omega)}
m_D(\Pi)\operatorname{tr}\Pi(f^D)
=
\sum_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\pi_v\ \mathrm{ess.disc}\ (v\in R(D))}}
m_G(\pi)\operatorname{tr}\pi(f^G).}
\tag{5.10}
$$

Both sums converge absolutely in each stated window, and the identity is stable under finite linear combinations and trace-norm limits of the archimedean smoothing multipliers.

The local condition on the right is exact. A cuspidal $\operatorname{GL}_2$ representation is locally generic, so it is never one dimensional. At a ramified place, principal-series traces vanish by (4.3); the remaining generic irreducibles are precisely Steinberg twists and supercuspidals.


## 6. Globalizing one prescribed local representation

### 6.1 Arithmetic realization of a local field

Let $K$ be a nonarchimedean local field of characteristic zero. Choose a monic polynomial defining $K/\mathbf Q_p$. Krasner stability gives a $p$-adic neighborhood of its coefficients in which one completion of the generated number field remains $K$. At every real place, polynomials with distinct real roots form an open set. Weak approximation on the coefficient vector therefore produces a totally real number field $F$ and a finite place $v$ with

$$
F_v\simeq K.
\tag{6.1}
$$

Book 87 then globalizes any prescribed quaternion invariant at $v$: choose an auxiliary place $u\ne v$, put invariant $1/2$ at $v,u$, and put invariant zero elsewhere, with extra real choices if a desired signature is being imposed. Relation (2.2) gives a global quaternion division algebra $B/F$ with

$$
B_v\simeq D_K.
\tag{6.2}
$$

We may choose $u$ of odd residue characteristic and prescribe there a depth-zero dihedral representation in the selected range of Book 84. This auxiliary component will calibrate transfer without imposing any condition on the representation at $v$.

### 6.2 Globalizing a division representation

**Lemma 6.1 (division globalization).** Let $\rho$ be an irreducible unitary smooth representation of $D_K^\times$ with central character $\omega_v$. There are data $(F,v,B)$ as above, a unitary Hecke character $\omega$ extending $\omega_v$, and a noncharacter automorphic representation $\Pi$ of $B^\times(\mathbf A_F)$ such that

$$
\Pi_v\simeq\rho.
\tag{6.3}
$$

The component at the auxiliary division place $u$ may be prescribed in the selected range.

**Proof.** Book 6 globalizes the local central character after allowing compensating ramification at finitely many auxiliary places. Choose dual vectors $x\in\rho$ and $\ell\in\rho^\vee$ with $\ell(x)\ne0$, and use the positive-covariant Poincare coefficient

$$
p_\rho(d)=\ell(\rho(d)x).
\tag{6.3a}
$$

Thus $p_\rho(zd)=\omega_v(z)p_\rho(d)$ and its right-translation span is an irreducible copy of $\rho$.  This is deliberately not the inverse-covariant coefficient used as a Hecke test function in (4.2o).  At $u$ choose the analogous positive-covariant coefficient of the prescribed noncharacter representation.  At finitely many further places choose sufficiently small compact-open factors with the global $\omega$-covariance, and use hyperspecial factors elsewhere.

Form the Poincare series from the resulting global seed $p$,

$$
P_p(g)=\sum_{\gamma\in B^\times(F)/F^\times}p(\gamma g).
\tag{6.4}
$$

The quotient is compact. Shrink one auxiliary support so that its rational translates meeting the support differ only by the center. At $g=1$, the identity term is then nonzero and no other noncentral term contributes, so $P_p\ne0$.  Its positive central covariance gives $P_p(gz)=\omega(z)P_p(g)$, as required for the convention (10.2).  Poincare summation is equivariant for right translation.  The local right spans of the two displayed coefficients are the prescribed irreducibles, so every irreducible quotient of the nonzero tensor image has those components at $v$ and $u$. Decomposing it in the discrete spectrum yields $\Pi$ with (6.3). The prescribed noncharacter component at $u$ prevents $\Pi$ from being a global norm character. $\square$

This is a genuine globalization of an arbitrary finite Clifford representation. It uses no tame label at $v$.
For a nonunitary irreducible, first apply its unique positive unramified real norm twist that is
unitary, use the lemma on that unitary line, and undo the same twist after the trace comparison.
The local construction in Section 7.1 records this step explicitly.

### 6.3 Globalizing a split discrete representation

**Lemma 6.2 (cuspidal split globalization).** Let $\sigma$ be an irreducible unitary supercuspidal representation of $\operatorname{GL}_2(K)$ with central character $\omega_v$. There is a totally real $F$ with $F_v=K$ and a cuspidal automorphic representation $\pi$ of $\operatorname{GL}_2(\mathbf A_F)$ such that

$$
\pi_v\simeq\sigma,
\tag{6.5}
$$

while at one auxiliary place $u$ the component is a prescribed selected depth-zero dihedral supercuspidal representation.

**Proof.** Extend the central character as above. A supercuspidal representation has a compact-mod-center matrix coefficient whose two-sided parabolic constant term is zero.  At $v$ and $u$ choose positive-covariant coefficients $p_\sigma(g)=\ell(\sigma(g)x)$ with $p_\sigma(1)\ne0$.  Their right-translation spans are the prescribed representations; no trace normalization is imposed on these Poincare seeds. Choose small positive-covariant factors at the remaining exceptional places and hyperspecial factors elsewhere. The Poincare series on $Z(\mathbf A_F)G(F)\backslash G(\mathbf A_F)$ is absolutely convergent because one coefficient is cuspidal and all finite supports are compact modulo the center. Shrinking an auxiliary support makes its identity term nonzero exactly as in (6.4), and the resulting series has central character $\omega$.

Unfolding the constant term of the Poincare series moves the unipotent integral to the local coefficient at $v$, where it is zero. Hence the series is cuspidal. Its right translates generate a nonzero cuspidal subspace.  Equivariance of Poincare summation and irreducibility of the local right spans force the asserted components in every irreducible quotient of the nonzero image. $\square$

Steinberg twists are deliberately not included in this Poincare-series lemma: they are already in the selected local correspondence (7.10). This avoids the false assertion that a compact Steinberg type idempotent has the two-sided constant-term vanishing of a supercuspidal coefficient.

### 6.4 Finite-window separation

At fixed finite level and compact type, choose the positive elliptic combination of archimedean Casimir operators used in Book 93. On the compact projective division quotient it has compact resolvent. Its Riesz projector onto a bounded interval is finite rank and is a trace-norm limit of rapidly decreasing functional-calculus multipliers. Put the identical Casimir multiplier at every split real place on the split side; at a ramified real place use the matching finite-dimensional character projector and discrete-series Euler function. The diagonal kernel estimates of Books 93 and 109--110 make both spectral and orbital distributions continuous under this limit. Thus an exact bounded projector may be inserted into (5.10), even though it is obtained as a limit of admissible test functions rather than falsely declared compactly supported.

The resulting fixed-level, fixed-type, bounded spaces on both sides are finite dimensional. Distinct irreducible characters are linearly independent. Consequently finitely many local test functions and polynomial interpolation produce an operator with prescribed traces on the finitely many constituents in the window.

Outside a finite set, the spherical Hecke characters form characters of a commutative algebra. Distinct algebra characters are linearly independent. Book 92 gives strong multiplicity one on the split group, and Book 93 gives strong determination and multiplicity one on the division group. These results let us isolate a chosen global constituent away from one variable place. They do not create that constituent; Lemmas 6.1--6.2 and the trace identity do.


## 7. Full finite local Jacquet--Langlands

### 7.1 Construction in the division-to-split direction

Let $K$ be nonarchimedean of characteristic zero, let $D/K$ be the quaternion division
algebra, and let $\rho\in\operatorname{Irr}(D^\times)$.  There is a unique real number $t$
such that

$$
\rho^{\mathrm u}=\rho\otimes(|\,\cdot\,|^t\circ\operatorname{Nrd})
\tag{7.0}
$$

is unitary.  First globalize $\rho^{\mathrm u}$ by Lemma 6.1 to $\Pi$ on a global algebra
$B$. At the auxiliary division place $u$, choose a selected local pair from Book 84. At all
other ramified places, if any, choose selected pairs as well; the global invariant construction
may be made with only $v,u$ ramified.

Use finite-window interpolation to isolate $\Pi$ on the left of (5.10). At $v$ leave the division factor variable; at $u$ use the selected coefficient and its transfer. The left side is nonzero. Therefore the right side contains at least one cuspidal representation $\pi$. Its local component $\pi_v$ is essentially square-integrable by Theorem 5.3. Strong multiplicity one makes the global $\pi$ with the isolated almost-everywhere Hecke character unique.

Now isolate $\Pi$ and $\pi$ away from $v$ and vary an arbitrary matching pair $(f_v^D,f_v^G)$. Multiplicity one on both global groups gives

$$
\operatorname{tr}\rho^{\mathrm u}(f_v^D)
=\operatorname{tr}\pi_v(f_v^G).
\tag{7.1}
$$

All fixed away-from-$v$ trace factors have been normalized to one. Define

$$
\operatorname{JL}_{D/K}(\rho^{\mathrm u})=\pi_v,
\qquad
\operatorname{JL}_{D/K}(\rho)
=\pi_v\otimes(|\,\cdot\,|^{-t}\circ\det).
\tag{7.2}
$$

The same isolated global pair records the other local components. If $w\ne v$ is split for $B$, leave the $w$-factor variable and use identical functions on the two sides; if $w=u$, use the already calibrated selected correspondence. The same one-place argument gives

$$
\pi_w\simeq\Pi_w\quad(B_w\text{ split}),
\qquad
\pi_u\simeq\operatorname{JL}^{\mathrm{sel}}_u(\Pi_u).
\tag{7.2a}
$$

This observation will be needed when the global functional equations are divided in Chapter 9.
Equation (7.1) also proves independence from every globalization choice for $\rho^{\mathrm u}$:
a second construction has the same trace on every transfer, hence the same elliptic character.
Book 93's local elliptic orthogonality makes the essentially square-integrable characters
linearly independent, so the two unitary local images are isomorphic.  The uniqueness of $t$
then makes (7.2) independent of choices for the original $\rho$.

### 7.2 The character identity without an integral-lattice shortcut

For a geometric transfer $f^G=-f^\sharp$, equation (7.1) reads

$$
\operatorname{tr}\operatorname{JL}(\rho^{\mathrm u})(f^G)
=-\operatorname{tr}\rho^{\mathrm u}(f^D).
\tag{7.3}
$$

Use regular slice functions supported in a small neighborhood of one matching elliptic pair. Weyl integration has the same torus, Weyl order, quotient measure, and discriminant on both sides. Varying the prescribed orbital transform in that neighborhood turns (7.3) into

$$
\boxed{
\Theta_{\operatorname{JL}(\rho)}(g)
=-\Theta_\rho(d)
\quad(d\leftrightarrow g).}
\tag{7.4}
$$

For $\rho^{\mathrm u}$ this follows directly from (7.3).  Multiplication by the common value
$|\operatorname{Nrd}d|^{-t}=|\det g|^{-t}$ gives the displayed identity for the original
$\rho$ and the twist-back definition (7.2).  This argument begins with an actual unitary
representation produced globally. It never maps a test-function lattice to a representation
lattice. Primitive wild cases are covered because Lemma 6.1 globalizes the unitary twist of
every irreducible $\rho$ and Theorem 4.1 transfers every local test function.

If two division representations have the same image, (7.4) makes their characters equal on the regular set. Since the singular set has measure zero and distribution characters are locally integrable, the character distributions agree. Linear independence gives equality of the representations. Thus the map is injective.

### 7.3 Surjectivity

Let $\sigma$ be any irreducible essentially square-integrable representation of $\operatorname{GL}_2(K)$. If it is a Steinberg twist, (7.10) already gives its inverse image. Otherwise it is supercuspidal.  An unramified real norm twist makes $\sigma$ unitary.  The character identity (7.4), already
proved for the injective division-to-split map, shows directly that this map commutes with such
twists.  It is therefore enough to prove surjectivity for the unitary twist and undo the twist
at the end.  We assume from now on that $\sigma$ is unitary.  Globalize it by Lemma 6.2,
choosing at the auxiliary place $u$ a selected component which lies in the image of the selected
local correspondence. Choose a global quaternion algebra ramified exactly at $v,u$.

Choose Haar measure on $Z(K)\backslash G(K)$ and dual vectors $x\in\sigma$,
$\ell\in\sigma^\vee$ with $\ell(x)=1$.  Schur orthogonality gives a formal degree
$d(\sigma)>0$ and the pseudo-coefficient

$$
h_\sigma(g)=d(\sigma)\ell(\sigma(g^{-1})x),
\qquad
\operatorname{tr}\sigma(h_\sigma)=1.
\tag{7.4a}
$$

It has inverse central covariance and is compact modulo the center.  Since $\sigma$ is
supercuspidal, every two-sided parabolic constant term of $h_\sigma$ is zero: a nonzero term,
after pairing with translates of $x$ and $\ell$, would define a nonzero functional on a Jacquet
module of $\sigma$.  In particular $\mathcal A h_\sigma=0$, and (4.2e) gives

$$
O_g(h_\sigma)=0
\qquad(g\text{ split regular}).
\tag{7.4b}
$$

Theorem 4.3, including its scalar-germ clause, supplies
$h_\sigma^D\in\mathcal H_D(\omega_v)$ with the opposite elliptic orbital transform.  This is a
genuine smooth compact-mod-center function; it is not a class in an unspecified cocenter.

We next arrange the global test without altering this local pair.  At $u$ take the selected
division coefficient and its prepared split transfer, normalized to have trace one on the
prescribed auxiliary components.  At every split place used in the Poincare construction take
an identical inverse-covariant test factor on the two inner forms, chosen to have nonzero trace
on $\pi_w$; these test factors need not be the positive-covariant Poincare seeds of Lemma 6.2.
Freeze the pair $(h_\sigma^D,h_\sigma)$ at $v$; at $u$ retain the
selected trace-one coordinate but allow the matching function to vary by the completion
operations of Lemma 5.0.  Fix a finite level, infinity type, and Casimir window containing the
global $\pi$ of Lemma 6.2.  Strong multiplicity one supplies finitely many split places away
from $v,u$ whose Hecke operators separate $\pi$ from every other constituent in this window.
Interpolate there to obtain a right-side selector for $\pi$.  Lemma 5.0 imposes the scalar
equation at $u$, corrects the selected trace there, and imposes the exceptional-character
equations with auxiliary split selectors.  Its proof leaves the frozen pair at $v$ unchanged.
The resulting
matched clean finite sum has right side exactly

$$
\sum_j
\operatorname{tr}\sigma(h_\sigma)
\prod_{w\ne v}\operatorname{tr}\pi_w(f_{j,w}^G)=1
\tag{7.4c}
$$

after normalization.  Now insert an arbitrary element $h$ of the spherical Hecke algebra at
good split places outside the prescribed set.  The same $h$ occurs on both inner forms.  The
right side is $\lambda_\pi(h)$, whereas the left side, in the fixed finite window, is

$$
\sum_{i=1}^r c_i\lambda_{\Pi_i}(h).
\tag{7.4d}
$$

Characters of a commutative algebra are linearly independent.  Equations (7.4c)--(7.4d)
therefore force one nonzero coefficient with
$\lambda_{\Pi_i}=\lambda_\pi$ outside a finite set.  Call that constituent $\Pi$.  Condition 5
in the definition of a clean pair excludes a norm character; no cancellation with the
exceptional spectrum is being used here.

Strong determination on $B^\times$ and strong multiplicity one on $G$ now give projectors away
from $v$ isolating this $\Pi$ and the original $\pi$: a competitor surviving all those
projectors would agree almost everywhere with the chosen representation and hence equal it.
For an arbitrary $f_v^D$, use the forward transfer of Theorem
4.1 at $v$ and invoke Lemma 5.0 only away from $v$ to retain cleanliness.  Varying this pair in
(5.10), with every fixed trace normalized to one, gives

$$
\operatorname{tr}\sigma(f_v^G)
=\operatorname{tr}\Pi_v(f_v^D)
\tag{7.5}
$$

for every matching pair.  Applying the already constructed division-to-split correspondence to
$\Pi_v$ gives the same identity with $\operatorname{JL}(\Pi_v)$ in place of $\sigma$.  Regular
slice functions therefore make their characters equal on every elliptic regular class.  Both
representations are essentially square-integrable; their elliptic characters are linearly
independent, so

$$
\sigma\simeq\operatorname{JL}(\Pi_v).
\tag{7.5a}
$$

Undoing the preliminary unramified twist proves surjectivity for the original $\sigma$.  The only reverse local input was Theorem 4.3 on smooth orbital
functions and scalar germs, and the only existence input was the explicit nonzero automorphic
term (7.4c).

### 7.4 The full local theorem

**Theorem 7.1 (finite local Jacquet--Langlands, full range).** There is a unique bijection

$$
\boxed{
\operatorname{JL}_{D/K}:
\operatorname{Irr}(D^\times)
\xrightarrow{\sim}
\operatorname{Irr}_{\mathrm{ess.disc}}(\operatorname{GL}_2(K))}
\tag{7.6}
$$

satisfying (7.4). It preserves central characters and commutes with twists and contragredients:

$$
\omega_{\operatorname{JL}(\rho)}=\omega_\rho,
\tag{7.7}
$$

$$
\operatorname{JL}(\rho\otimes(\chi\circ\operatorname{Nrd}))
\simeq
\operatorname{JL}(\rho)\otimes(\chi\circ\det),
\tag{7.8}
$$

$$
\operatorname{JL}(\rho^\vee)
\simeq\operatorname{JL}(\rho)^\vee.
\tag{7.9}
$$

**Proof.** Existence, injectivity, and surjectivity are Sections 7.1--7.3. Replacing a matching pair by its scalar translate proves (7.7). Multiplying both character functions by the common value $\chi(\operatorname{Nrd}d)=\chi(\det g)$ proves (7.8). Replacing $d,g$ by their inverses proves (7.9). Uniqueness follows from linear independence of elliptic discrete characters. $\square$

The selected formulas calibrate the abstract construction:

$$
\operatorname{JL}(\mu\circ\operatorname{Nrd})
=\operatorname{St}\otimes\mu,
\tag{7.10}
$$

and for a tame admissible pair in the quadratic-induction normalization of Books 83--84,

$$
\operatorname{JL}(\pi_D(E,\theta))=\pi_G(E,\theta).
\tag{7.11}
$$

No primitive wild representation is assigned a quadratic pair or tame rectifier.

At a finite place the correspondence also commutes with scalar conjugation. Choose Haar measures giving rational volume to compact opens. The construction in Book 112 uses characteristic functions of compact opens, powers of $q$, finite averaging, and extension of locally constant invariant data. Therefore, if $f^G$ transfers $f^D$, then $\iota(f^G)$ transfers $\iota(f^D)$ for every $\iota\in\operatorname{Aut}(\mathbf C)$. Applying $\iota$ to (7.3) and using uniqueness gives

$$
\operatorname{JL}({}^{\iota}\rho)
\simeq{}^{\iota}\operatorname{JL}(\rho).
\tag{7.12}
$$

Here ${}^{\iota}V=\mathbf C\otimes_{\iota,\mathbf C}V$ is the semilinear conjugate of the smooth local representation. Exactness of scalar extension preserves irreducibility, Jacquet modules, and supercuspidality. Equation (7.12) is a finite-place representation statement; at infinity algebraic conjugation is transported through an algebraic coefficient system rather than applied to analytic character values.


## 8. The real correspondence and orientations

### 8.1 The compact and split characters

Every element of $\mathbf H^\times$ is uniquely $ru$ with $r>0$ and $u\in\operatorname{SU}(2)$. Put

$$
\tau_{n,s}(ru)=r^{2s}\operatorname{Sym}^n(u),
\qquad n\ge0.
\tag{8.1}
$$

Its dimension and central character are

$$
\dim\tau_{n,s}=n+1,
\qquad
\omega_{\tau_{n,s}}(x)=\operatorname{sgn}(x)^n|x|^{2s}.
\tag{8.2}
$$

For an elliptic element with compact angle $0<\theta<\pi$,

$$
\Theta_{\tau_{n,s}}(ru_\theta)
=r^{2s}\frac{\sin((n+1)\theta)}{\sin\theta}.
\tag{8.3}
$$

Let $D_k$ denote the irreducible discrete-series representation of the full group $\operatorname{GL}_2(\mathbf R)$ whose restriction to positive determinant is $D_k^+\oplus D_k^-$. Book 99's Harish--Chandra formula gives

$$
\Theta_{D_{n+2}\otimes|\det|^s}(g_\theta)
=-r^{2s}\frac{\sin((n+1)\theta)}{\sin\theta}.
\tag{8.4}
$$

The parity in (8.2) agrees with the central character of the full $D_{n+2}$.

### 8.2 The real local theorem

**Theorem 8.1 (real ramified transfer).** The unique real correspondence is

$$
\boxed{
\operatorname{JL}_{\mathbf H/\mathbf R}(\tau_{n,s})
=D_{n+2}\otimes|\det|^s.}
\tag{8.5}
$$

It satisfies the character sign (8.4), preserves central characters, twists, and contragredients, and gives equal traces on signed Euler--Poincare transfers.

**Proof.** The compact Weyl numerator is $e^{i(n+1)\theta}-e^{-i(n+1)\theta}$. The split discrete-series formula has the same numerator and denominator with the inner-form sign $-1$. Sine orthogonality on the elliptic torus proves uniqueness and bijectivity. Norm twists multiply both sides by $r^{2s}$, and inversion proves contragredient compatibility. The Lefschetz sign of Section 4.7 cancels the character sign in the signed trace identity. $\square$

In particular,

$$
\mathbf1_{\mathbf H^\times}\longleftrightarrow D_2.
\tag{8.6}
$$

At a split real place transfer is the identity on the full disconnected group. Thus $D_2^+$ and $D_2^-$ are not two automorphic representations; they are the two orientation summands after restricting one full $D_2$.

### 8.3 Two active factors

Book 99 computes

$$
H^q(\mathfrak{sl}_2,\operatorname{SO}(2);D_2^\epsilon)
=
\begin{cases}
\mathbf C,&q=1,\\
0,&q\ne1,
\end{cases}
\qquad \epsilon\in\{+,-\}.
\tag{8.7}
$$

The $+$ line has Hodge type $(1,0)$ and the $-$ line type $(0,1)$. For two active real factors, Kunneth gives four degree-two orientation lines:

$$
\begin{array}{c|c}
(+,+)&(2,0)\\
(+,-)&(1,1)\\
(-,+)&(1,1)\\
(-,-)&(0,2).
\end{array}
\tag{8.8}
$$

This is a local derived-group calculation. Chapter 16 will not turn it into a multiplicity formula for the full surface similitude group.


## 9. Conductors, local factors, newvectors, and parameters

### 9.1 Intrinsic division conductor

Let $\mathcal O_D$ be the maximal order, $\mathfrak P_D$ its radical, and

$$
U_D^0=\mathcal O_D^\times,
\qquad
U_D^m=1+\mathfrak P_D^m\quad(m\ge1).
\tag{9.1}
$$

For an irreducible $\rho$, put

$$
c_D(\rho)=\min\{m\ge0:U_D^m\text{ acts trivially on }\rho\}.
\tag{9.2}
$$

Book 82 proves finiteness and defines the transfer-facing exponent

$$
a_D(\rho)=
\begin{cases}
1,&\rho=\mu\circ\operatorname{Nrd},\ a(\mu)=0,\\
2a(\mu),&\rho=\mu\circ\operatorname{Nrd},\ a(\mu)>0,\\
c_D(\rho)+1,&\dim\rho>1.
\end{cases}
\tag{9.3}
$$

For higher-dimensional level-zero representations $c_D=1$ and $a_D=2$. The exceptional first line records the monodromy of the Steinberg image.

### 9.2 The degree-two local zeta problem

The conductor comparison must not be deduced by transferring a division idempotent to a
$K_1$-fixed-vector complex.  We construct the two local functional equations independently.
The only results taken from Book 98 are additive Fourier inversion and Poisson summation, and
the degree-one Tate functional equation when a one-dimensional boundary integral appears.
No degree-two zeta theorem is imported.

Let first $K$ be nonarchimedean, let $A=M_2(K)$ or the quaternion division algebra $D$, and put
$G_A=A^\times$.  Fix a nontrivial additive character $\psi$ and the self-dual measure $dx$ for

$$
(x,y)\longmapsto\psi(\operatorname{Trd}(xy)).
\tag{9.4}
$$

Put $e(A)=1$ for $M_2(K)$ and $e(A)=-1$ for the division algebra.  The second value is the
degree-two anisotropic Hasse sign used in Book 84.  Define the normalized Fourier transform by

$$
\widehat\Phi(y)=e(A)\int_A\Phi(x)\psi(\operatorname{Trd}(xy))\,dx,
\qquad
\widehat{\widehat\Phi}(x)=\Phi(-x).
\tag{9.4a}
$$

The sign does not change self-duality or support; it calibrates the division epsilon factor.
Omitting it would reverse every division gamma factor and would disagree with the selected
special and dihedral calculation at the auxiliary place.  At an archimedean place we use the
same rule: $+1$ for the split algebra and $-1$ for Hamilton's algebra.

Left multiplication by $a\in A^\times$ has additive determinant
$|\operatorname{Nrd}(a)|^2$.  We therefore take

$$
d^\times a=c_A|\operatorname{Nrd}(a)|^{-2}\,da,
\tag{9.4b}
$$

where $c_A$ is chosen so that the standard maximal compact has volume one.  This measure is
both left and right invariant.

Let $\rho$ be an irreducible admissible representation of $G_A$, let $v\in\rho$ and
$\lambda\in\rho^\vee$, and set $c_{v,\lambda}(a)=\lambda(\rho(a)v)$.  For
$\Phi\in\mathcal S(A)$ define, initially in a right half-plane,

$$
Z_A(s,\Phi,c)=
\int_{A^\times}\Phi(a)c(a)
|\operatorname{Nrd}(a)|^{s+1/2}\,d^\times a.
\tag{9.5}
$$

The shift $1/2$ is the centered degree-two normalization.  It makes Fourier transform reflect
$s$ to $1-s$.  If

$$
\check c(a)=c(a^{-1})
=v\bigl(\rho^\vee(a)\lambda\bigr),
\tag{9.5a}
$$

then $\check c$ is a coefficient of $\rho^\vee$.

Two formal compatibilities will be used repeatedly.  For a quasicharacter $\chi$ of $K^\times$,

$$
c_{\rho\otimes(\chi\circ\operatorname{Nrd})}(a)
=\chi(\operatorname{Nrd}a)c_\rho(a),
\tag{9.5b}
$$

so the zeta theory of a twist is obtained by inserting this common Mellin character, not by a
formula involving conductors alone.  Also inversion exchanges $\rho$ and $\rho^\vee$ exactly
as in (9.5a).

### 9.3 Convergence and rational continuation

The issue on $M_2(K)$ is not merely that there are two Cartan indices.  A diagonal Cartan
element does not act repeatedly on one fixed space of compact invariants.  The correct argument
uses one common compact subgroup and the finite-dimensional Jacquet asymptotic.

**Lemma 9.0 (rank-one coefficient asymptotic).**  Let $c$ be a matrix coefficient of an
admissible representation of $\operatorname{GL}_2(K)$.  There is a compact open subgroup $J$
fixing its two coefficient vectors.  For every finite collection of elements
$k_i,k_j\in\operatorname{GL}_2(\mathcal O)$ there are finitely many nonzero numbers $\alpha$ and
polynomials $P_{ij,\alpha}(r)$ such that, for all sufficiently large $r$,

$$
c\left(k_i
\begin{pmatrix}1&0\\0&\varpi^r\end{pmatrix}k_j\right)
=\sum_\alpha P_{ij,\alpha}(r)\alpha^r.
\tag{9.5c}
$$

The finite set of $\alpha$ depends on the representation and $J$, not on $i,j$.

**Proof.**  Intersect compact opens fixing $v$ and $\lambda$ and then replace the intersection
by a normal subgroup of the maximal compact.  This gives one $J$ on both sides.  Let $N$ and
$\bar N$ be the two root groups and put
$a=\operatorname{diag}(1,\varpi)$.  Choose nested compact groups $N_m,\bar N_m$ so that
$aN_ma^{-1}=N_{m+1}$ and $a^{-1}\bar N_ma=\bar N_{m+1}$.  Averaging over these finite-volume
groups gives idempotents $e_{N_m}$ and $e_{\bar N_m}$.

For a fixed $J$-finite vector, the images of $e_{N_m}v$ in the Jacquet quotient
$V_N=V/\langle nv-v\rangle$ stabilize.  The finite-dimensionality used here is the elementary
rank-one Jacquet lemma of Book 92: the two Bruhat cells reduce the quotient to the images of two
compact-fixed spaces, which are finite dimensional by admissibility.  This lemma contains no
zeta or local-factor statement.  Surjectivity of stabilization follows because every Jacquet
class has a representative fixed by some $N_m$, and its kernel stabilizes inside those finite
spaces.  The same statement
holds for $\lambda$ in $(V^\vee)_{\bar N}$.  Moving $a^r$ across the two averaging idempotents
then gives, for $r$ beyond the two stabilization indices,

$$
\lambda_i(\rho(a^r)v_j)
=\langle T^r\bar v_j,\bar\lambda_i\rangle,
\tag{9.5d}
$$

where $T$ is the normalized action of $a$ on the finite-dimensional
$T(\mathcal O)$-fixed part of $V_N$, and bars denote the stabilized Jacquet classes.  One may
verify (9.5d) directly: a vector killed in $V_N$ is a finite sum of $nv-v$; after conjugation
by a sufficiently large $a^r$, the relevant $n$ lies in the compact group fixing the opposite
coefficient, so its pairing is zero.  The dual argument treats the other kernel.

Cayley--Hamilton applied to $T$ makes every sequence in (9.5d) satisfy one recurrence.  On a
generalized $\alpha$-eigenspace its terms are $P(r)\alpha^r$.  The finitely many $k_i,k_j$
only change the vectors in (9.5d), proving the uniform assertion. $\square$

This lemma is the required asymptotic decomposition.  It does not claim that
$\rho(a^r)V^J\subseteq V^J$, and it does not replace the Hecke operators
$e_J\rho(a^r)e_J$ by powers of one of them.

**Proposition 9.1 (local continuation).**  The integral (9.5) converges absolutely for
$\operatorname{Re}(s)$ sufficiently large.  At a finite place it is a rational function of
$q^{-s}$, with a denominator drawn from one finite list depending only on $\rho$.  At an
archimedean place it has a meromorphic continuation to $\mathbf C$.

**Proof at a finite split place.**  Shrink the common $J$ of Lemma 9.0 until $\Phi$ is invariant
under left and right multiplication by $J$.  Refine the two maximal-compact factors into the
finite set of $J$-cosets.  Elementary divisors write every $g\in G$ as

$$
g=k_i\varpi^m
\begin{pmatrix}1&0\\0&\varpi^r\end{pmatrix}k_j,
\qquad m\in\mathbf Z,\quad r\ge0.
\tag{9.5e}
$$

Compact support of $\Phi$ bounds $m$ below.  Centrality gives

$$
c(\varpi^m a_r)=\omega_\rho(\varpi)^m c(a_r),
\qquad
|\det(\varpi^m a_r)|=q^{-(2m+r)}.
\tag{9.5f}
$$

The volume of a $J$-double coset in the $r$th chamber is
$[J:J\cap a_rJa_r^{-1}]$ times a fixed constant.  Intersecting the four matrix-entry lattices
shows that this index is a fixed power of $q^r$ for all large $r$, with only finitely many
initial exceptions.

There are two additive boundary directions.  Local constancy at a rank-one matrix says that,
for each of the finitely many $m$ below a fixed bound, the value
$\Phi(\varpi^mk_i a_rk_j)$ is constant for all large $r$.  Local constancy at zero gives an
$M$, independent of $r,i,j$, such that

$$
\Phi(\varpi^mk_i a_rk_j)=\Phi(0)
\qquad(m\ge M).
\tag{9.5g}
$$

Thus the $(m,r)$-cone is a finite rectangle, finitely many rank-one tails, and one zero
quadrant.  On every tail Lemma 9.0 and (9.5f) reduce the sum to finite combinations of

$$
\sum_{r\ge R}r^jz^r,
\qquad
\sum_{m\ge M}w^m,
\tag{9.5h}
$$

which are rational; the first has denominator $(1-z)^{j+1}$.  The same formulas give absolute
convergence when $|z|,|w|<1$, hence in a right half-plane.  The $r$-tails are precisely the
approach to the rank-one stratum, the $m$-tail is the approach to zero, and the zero quadrant
contains their intersection.  Thus the continuation has not discarded either singular
stratum.

**Proof at a division place.**  Write $D^\times=\bigsqcup_r\Pi^r\mathcal O_D^\times$.  There
are only two projective valuation classes because $\Pi^2$ is central.  After a common
principal-unit averaging, every angular integral is finite and the tail toward zero is an
ordinary geometric series governed by the central character.  Compact support bounds the
opposite tail.  This proves convergence and rationality.

**Archimedean proof.**  Use singular-value coordinates in $M_2(\mathbf R)$ or
$M_2(\mathbf C)$ and polar coordinates in a real division algebra.  First take $K$-finite
coefficient vectors and a $K\times K$-finite Schwartz function.  The angular variables then
belong to a finite sum of compact-group types.  Along the ratio of the two singular values,
the same Jacquet-quotient argument as (9.5d), with the Lie algebra in place of compact
averaging, gives finite sums $t^\alpha(\log t)^j$.  Taylor expand $\Phi$ transversely to rank
one and to zero to any prescribed order.  Mellin integration of a term
$t^\alpha(\log t)^j$ is a derivative of $(s+\alpha)^{-1}$; the Taylor remainder is holomorphic
on a successively larger half-plane after integration by parts.  Increasing the Taylor order
continues the integral across the whole plane.  Schwartz decay controls the large singular
values uniformly.

For general smooth coefficient vectors and a general Schwartz function, convolve the vectors
and $\Phi$ on both compact sides with the Peter--Weyl projectors of degree at most $M$.  The
approximants converge in every smooth, respectively Schwartz, seminorm.  Integration by parts
in the compact variables makes the omitted $K$-types decrease faster than any power of their
highest weights, uniformly on a fixed vertical strip after the same finite Taylor subtraction.
The continued integrals of the approximants therefore form a normally convergent sequence on
that strip.  Its limit is independent of the projectors and agrees with the original integral
in the convergence half-plane.  This proves meromorphic continuation for all data and also
shows that possible poles come only from the rank-one and zero Taylor terms. $\square$

### 9.4 The local functional equation and canonical factors

We next prove that Fourier transform produces one scalar, including at the exceptional
parameters at which singular distributions can occur.

**Lemma 9.2 (generic equivariant uniqueness).**  Fix $\rho$.  If $K$ is nonarchimedean, away
from a finite set of values of $X=q^{-s}$ the space of trilinear forms on
$\mathcal S(A)\otimes\rho\otimes\rho^\vee$ having the left--right covariance of (9.5) is one
dimensional.  At an archimedean place the exceptional set is locally finite in the
$s$-plane.  A second such meromorphic family is therefore a scalar multiple of (9.5), and the
equality continues across the exceptional values.

**Proof.**  On the open orbit $A^\times$, transitivity of $G_A\times G_A$ and Schur's lemma
leave one scalar: evaluation at $1$ identifies the fiber with
$\operatorname{Hom}_{G_A}(\rho,\rho)$.  It remains to rule out a difference supported on the
singular set.

For division $A$, that set is $\{0\}$.  A distribution supported at zero over a
nonarchimedean field is a multiple of evaluation at zero, because test functions are locally
constant.  Its covariance can match the prescribed one only when $\rho$ is one dimensional
and $X$ has one specified value.

For $A=M_2(K)$, restrict first to the rank-one orbit of
$e=\left(\begin{smallmatrix}1&0\\0&0\end{smallmatrix}\right)$.  Its stabilizer contains the
upper unipotent in one factor and the lower unipotent in the other.  Frobenius descent therefore
identifies an equivariant distribution on this orbit with a homomorphism between a character
quotient of $\rho_N$ and one of $(\rho^\vee)_{\bar N}$.  To see this without a descent theorem,
cover the orbit by the two charts $uv^{\mathsf t}$ with one chosen coordinate of $u$ and $v$
a unit, integrate along the two unipotent fibers, and check agreement on the overlap
$(u,v)\sim(au,a^{-1}v)$.  The fiber integrals kill precisely the subspaces generated by
$nv-v$ and $\bar n\lambda-\lambda$, giving the two Jacquet quotients.

Those quotients are finite dimensional.  Their diagonal-torus actions have finitely many
generalized eigencharacters.  The additional norm covariance contains $X$, so an intertwiner
can occur only when $X$ equals one of finitely many eigenvalue ratios.  After the rank-one
restriction is zero, the remaining distribution is supported at zero and the preceding
evaluation argument applies.  This proves uniqueness off a finite set.  Proposition 9.1 makes
both families rational in $X$, so an equality on the complement extends meromorphically across
the exceptional set.  At infinity, transversal derivatives of the rank-one and zero delta
distributions replace point evaluation; each has one fixed homogeneity, hence again occurs at
only a discrete set, and the same continuation argument applies. $\square$

For $h_1,h_2\in A^\times$, set
$\Phi^{h_1,h_2}(x)=\Phi(h_1^{-1}xh_2)$.  A change of variables in (9.4a) gives

$$
\widehat{\Phi^{h_1,h_2}}(y)
=\left|\frac{\operatorname{Nrd}h_1}{\operatorname{Nrd}h_2}\right|^2
\widehat\Phi(h_2^{-1}yh_1).
\tag{9.5i}
$$

Together with $s\leftrightarrow1-s$, this is exactly the covariance of the original zeta
family.  Lemma 9.2 therefore proves a unique nonzero meromorphic function
$\gamma_A(s,\rho,\psi)$ such that

$$
Z_A(1-s,\widehat\Phi,\check c)
=\gamma_A(s,\rho,\psi)Z_A(s,\Phi,c).
\tag{9.6}
$$

This proof includes the rank-one and zero strata: they are the exceptional equivariant
distributions analyzed in Lemma 9.2, and rational continuation, rather than their omission,
extends (9.6) through them.

Return now to nonarchimedean $K$.  Let $R=\mathbf C[X,X^{-1}]$, $X=q^{-s}$.
The span of all zeta integrals is an $R$-module.  Choose $h\in A^\times$ with
$v_K(\operatorname{Nrd}h)=1$ (a division uniformizer or
$\operatorname{diag}(\varpi,1)$).  Right translation $x\mapsto xh$, accompanied by the
corresponding translate of $v$, multiplies the integral by
$|\operatorname{Nrd}h|^{s+1/2}$, a nonzero constant times $X$; translation by $h^{-1}$ gives
$X^{-1}$.  Linearity then gives multiplication by every Laurent polynomial.  Proposition 9.1 gives one common denominator for all the
integrals: its factors are the characteristic polynomials of the finitely many Jacquet
operators in (9.5d), together with the central geometric factor, and do not depend on the
vectors or on $\Phi$.  Choose $a_0\in A^\times$ with $c(a_0)\ne0$ and a sufficiently small
compact-open neighborhood on which both $c$ and the norm are constant.  Its characteristic
function gives a nonzero Laurent monomial.  Rescaling makes that monomial a unit of $R$.
Thus the zeta module contains $R$ and is a submodule of the cyclic module
$Q(X)^{-1}R$.  It is finitely generated because $R$ is noetherian, and hence is a nonzero
fractional ideal.  Since $R$ is a principal ideal domain, clearing powers of $X$ and
normalizing the constant coefficient give a unique generator of the form

$$
L_A(s,\rho)=P_\rho(q^{-s})^{-1},
\qquad P_\rho(0)=1.
\tag{9.6a}
$$

Fourier transform is an automorphism of the Schwartz space.  Equation (9.6) consequently maps
the zeta ideal for $\rho$ onto the reflected ideal for $\rho^\vee$.  The units of $R$ are
$cq^{-ms}$.  Thus there are a nonzero constant $w_A(\rho,\psi)$ and an integer
$a_A(\rho,\psi)$ such that

$$
\gamma_A(s,\rho,\psi)
=\epsilon_A(s,\rho,\psi)
\frac{L_A(1-s,\rho^\vee)}{L_A(s,\rho)},
\qquad
\epsilon_A(s,\rho,\psi)
=w_A(\rho,\psi)q^{-a_A(\rho,\psi)(s-1/2)}.
\tag{9.7}
$$

If $\rho$ is unitary and $\psi$ has conductor zero, then
$|w_A(\rho,\psi)|=1$.  Here is a proof which does not assume that the original Schwartz
function has finite support away from zero.  Give $\rho^\vee$ the conjugate Hilbert structure;
then

$$
\overline{c_{v,\lambda}(a)}
=c_{\lambda,v}(a^{-1})
\tag{9.7-ua}
$$

after identifying the conjugate of a unitary representation with its smooth dual.  Complex
conjugation of (9.6), followed by $a\mapsto a^{-1}$ and the self-dual Parseval identity, gives

$$
\overline{\gamma_A(\bar s,\rho,\psi)}
=\gamma_A(s,\rho^\vee,\psi^{-1}).
\tag{9.7-ub}
$$

The normalized polynomials defining $L_A$ have constant coefficient one, so no scalar is
introduced when the two fractional ideals are compared; for a unitary $\rho$ this also gives
$L_A(1/2,\rho^\vee)=\overline{L_A(1/2,\rho)}$ wherever the values are finite, and then by
meromorphic continuation.  Put $s=1/2$ in (9.7-ub) and use the Fourier-involutivity identity
(9.7b), proved independently immediately below, which says that the two gamma values at the
center are reciprocal.  Their absolute values are therefore one, and the
$L$-quotient in (9.7) has absolute value one.  Hence
$|\epsilon_A(1/2,\rho,\psi)|=|w_A(\rho,\psi)|=1$.

Applying (9.6) twice and using Fourier inversion gives

$$
\gamma_A(s,\rho,\psi)
\gamma_A(1-s,\rho^\vee,\psi)=\omega_\rho(-1).
\tag{9.7a}
$$

Equivalently, since $\psi^{-1}=\psi_{-1}$,

$$
\gamma_A(s,\rho,\psi)
\gamma_A(1-s,\rho^\vee,\psi^{-1})=1.
\tag{9.7b}
$$

After substituting (9.7), comparison of Laurent exponents gives
$a_A(\rho^\vee,\psi^{-1})=a_A(\rho,\psi)$; at $s=1/2$ the two root constants are reciprocal.
Thus, for conductor-zero additive characters,
$a_A(\rho^\vee)=a_A(\rho)$: contragredience preserves the conductor defined by the zeta
equation.

Here is the additive-character calculation needed later.  For $b\in K^\times$, put
$\psi_b(x)=\psi(bx)$.  Since $A$ has dimension four, its self-dual measure is $|b|^2dx$, and

$$
\widehat\Phi^{\,\psi_b}(y)=|b|^2\widehat\Phi^{\,\psi}(by).
\tag{9.7c}
$$

Substitute $h=bg$ in the left side of (9.6).  The three factors are $|b|^2$ from (9.7c),
$|b|^{-2(3/2-s)}$ from the reduced norm, and $\omega_\rho(b)$ from
$\check c(b^{-1}h)=c(h^{-1}b)$.  Therefore

$$
\boxed{
\gamma_A(s,\rho,\psi_b)
=\omega_\rho(b)|b|^{2s-1}\gamma_A(s,\rho,\psi),
}
\tag{9.7d}
$$

and the identical formula holds for $\epsilon_A$.  The $L$-factor is independent of $\psi$.
Define $n(\psi)$ by $\ker(\psi)=\mathfrak p^{-n(\psi)}$; thus
$n(\psi_b)=n(\psi)+v_K(b)$ and a character with kernel $\mathcal O_K$ has exponent zero.
Formula (9.7d) says that the monomial exponent for a general character is

$$
a_A(\rho,\psi)=a_A(\rho)+2n(\psi).
\tag{9.7da}
$$

Formula (9.5b), (9.7b), and (9.7d) prove twist, contragredient, and additive-character
compatibility directly from the integrals.  No maximum rule for the conductor of a twist is
implied.

### 9.5 The split Whittaker bridge and Fourier exponent

Let now $A=M_2(K)$ and let $\sigma$ be irreducible and generic.  We verify that the factor just
constructed is the standard split factor and calculate its epsilon exponent.

**Lemma 9.3 (equality of the two split ideals).**  The fractional ideal generated by the
matrix-coefficient integrals (9.5) is the ideal generated by

$$
\int_{K^\times}
W\!\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right)
|y|^{s-1/2}\,d^\times y,
\qquad W\in\mathcal W(\sigma,\psi).
\tag{9.7e}
$$

The Fourier equations on the two ideals agree.

**Proof.**  Left multiplication by $N$ leaves the bottom row and the determinant unchanged,
and those two data determine the $N$-orbit.  Thus the correct homogeneous-space chart is

$$
N\backslash G\xrightarrow{\ \sim\ }
\bigl(K^2\setminus\{0\}\bigr)\times K^\times,
\qquad
Ng\longmapsto(\text{bottom row of }g,\det g).
\tag{9.7e-a}
$$

The determinant coordinate in (9.7e-a) is essential; the bottom row alone has the wrong
dimension.  The coordinates can be written without hiding a Jacobian.  On the chart $d\ne0$,
put $u=(c,d)$ and write the top row uniquely as

$$
(a,b)=x(c,d)+y(d^{-1},0).
\tag{9.7ea}
$$

Then $\det g=y$, and the determinant of the change $(x,y)\mapsto(a,b)$ is $-1$.  On the chart
$c\ne0$ use $(0,-c^{-1})$ in place of $(d^{-1},0)$; again $\det g=y$ and the additive
Jacobian is one.  A compact-open partition according to which of $c,d$ has smaller valuation
makes these charts disjoint.  Passing from additive measure on the two rows to
$d^\times g=|\det g|^{-2}dg$ and then integrating the nonzero determinant coordinate changes
the exponent $s+1/2$ in (9.5) into $s-1/2$ in (9.7e).

At the finite level fixed by $\Phi,v,\lambda$, Fourier inversion in $x$ is Fourier inversion on
one finite quotient of a compact additive lattice.  Its nonzero frequencies are conjugate
under $\operatorname{diag}(\xi,1)$ to the fixed character $x\mapsto\psi(x)$.  The corresponding
coefficient

$$
\int c(n(x)g)\psi(-\xi x)\,dx
\tag{9.7eb}
$$

is therefore a Whittaker function of $g$ after that diagonal translate.  The zero frequency is
the $N$-coinvariant.  On each generalized torus eigenspace of the finite-dimensional Jacquet
module it is a finite sum $r^j\alpha^r$, exactly as in (9.5d); its Mellin series is a Laurent
polynomial times the Mellin series of a Whittaker function having that same asymptotic
eigencomponent.  Such a Whittaker function is obtained by applying a nonzero-frequency
projector to a vector mapping to the chosen Jacquet class.  Equivalently, the zero-frequency
integral is the degree-one Tate boundary integral, and the one-dimensional Tate equation plus
Cayley--Hamilton gives the same Laurent multiple.  Thus the zero frequency introduces no new
denominator.

A partition of unity on the two bottom-row charts now writes every (9.5) as a finite sum

$$
\sum_i p_i(q^s,q^{-s})Z(s,W_i),
\tag{9.7f}
$$

with $p_i\in R$.  The overlap of the charts changes the chosen bottom-row coordinate by a unit,
so it introduces no denominator.

Conversely, let $W(g)=\ell_\psi(\sigma(g)v)$.  Choose a compact group $N_m$ fixing $v$.  The
maps

$$
\lambda\longmapsto
\int_{N_m}\lambda(\sigma(n)\,cdot\,)\psi(-n)\,dn
\tag{9.7ec}
$$

stabilize, after increasing $m$, to the one-dimensional Whittaker coinvariant of
$\sigma^\vee$; otherwise their union would be zero, contradicting genericity.  Scale a
$\lambda$ whose image is $\ell_\psi$.  Choose a compact-open bottom-row box and a top-row
Schwartz function whose finite Fourier transform selects the character in (9.7ec).
Substitution in (9.7ea), followed by finite Fourier inversion, expresses $Z(s,W)$ as a finite
$R$-linear combination of (9.5).  The two inclusions prove equality of ideals.

Finally, the full Fourier transform on $M_2$ is the successive partial transform in the two row
coordinates.  The preceding changes of variables carry it to the Weyl transform of the
Whittaker function, so the proportionality scalar is the same. $\square$

For completeness, if $W^\circ(1)=1$ is spherical with Satake roots $\alpha,\beta$, the rank-one
Hecke recurrence gives, for $r\ge0$,

$$
W^\circ\!\left(\begin{pmatrix}\varpi^r&0\\0&1\end{pmatrix}\right)
=q^{-r/2}\frac{\alpha^{r+1}-\beta^{r+1}}{\alpha-\beta},
\tag{9.7ed}
$$

with the derivative value when $\alpha=\beta$, and it is zero for $r<0$.  Summing the two
geometric series in (9.7e) gives
$L_G(s,\sigma)=((1-\alpha q^{-s})(1-\beta q^{-s}))^{-1}$.  For a supercuspidal representation,
Kirillov functions are compactly supported on $K^\times$ because the Jacquet module is zero;
their Mellin transforms generate $R$, so $L_G=1$.  For a special representation the
one-dimensional Jacquet tail gives $L(s+1/2,\mu)$.  These conclusions came from the split
integrals themselves.

**Lemma 9.4 (split Fourier exponent).**  Let

$$
n=\min\{r:\sigma^{K_1(\mathfrak p^r)}\ne0\}.
\tag{9.7g}
$$

For an additive character of conductor zero,

$$
\epsilon_G(s,\sigma,\psi)
=\epsilon_G(1/2,\sigma,\psi)q^{-n(s-1/2)}.
\tag{9.7h}
$$

**Proof.**  In the Kirillov model write
$\phi(y)=W(\operatorname{diag}(y,1))$.  Upper-unipotent invariance, diagonal-unit invariance,
and the last-row condition in $K_1(\mathfrak p^r)$ place $\phi$ in one valuation flag.  Apply
the Weyl element.  The lower-unipotent condition places its Weyl transform in the opposite
flag.  On the quotient between consecutive flags the transform is exactly the finite Fourier
pairing

$$
\mathfrak p^{-r}/\mathcal O
\times\mathcal O/\mathfrak p^r
\longrightarrow\mathbf C^\times,
\qquad(x,y)\longmapsto\psi(xy).
\tag{9.7i}
$$

The two-filtration newvector argument of Book 92 proves that the first intersection is at
$r=n$ and is one dimensional.  We recall the point that determines the exponent.  If the
Fourier transform of a generator vanished on the outer layer
$\mathfrak p^{-n}/\mathfrak p^{-n+1}$, finite Fourier inversion on (9.7i) would make it
constant one step earlier.  The same vector would then lie in the intersection at $n-1$, a
contradiction.  Thus the outer coefficient is nonzero.

Mellin transform turns the Weyl relation into the functional equation of Lemma 9.3.  Moving
that nonzero outer layer from valuation $-n$ to valuation zero replaces $y$ by
$\varpi^{-n}y$ and contributes
$q^{-n(s-1/2)}$.  After this power is removed, finite Fourier transform acts on a
one-dimensional line and is therefore a nonzero scalar independent of $s$.  Dividing by the
two normalized generators gives (9.7h).  No classification of $\sigma$ entered, so this
includes primitive wild supercuspidals. $\square$

### 9.6 The division Euler factor and Fourier conductor

The division calculation is finite and uniform in the residue characteristic.

**Lemma 9.5 (division Fourier conductor).**  For every irreducible $\rho$ of $D^\times$ and an
additive character of conductor zero,

$$
L_D(s,\rho)=
\begin{cases}
L(s+1/2,\mu),&\rho=\mu\circ\operatorname{Nrd},\\
1,&\dim\rho>1,
\end{cases}
\tag{9.8}
$$

and

$$
\epsilon_D(s,\rho,\psi)
=\epsilon_D(1/2,\rho,\psi)
q^{-a_D(\rho)(s-1/2)}.
\tag{9.9}
$$

**Proof.**  Average $\Phi$ and the two coefficient vectors by a common principal-unit subgroup
which kills $\rho$.  The integral becomes a finite angular sum on the shells

$$
S_r=\mathfrak P_D^r\setminus\mathfrak P_D^{r+1}
\qquad(r\in\mathbf Z).
\tag{9.10}
$$

Book 82 proves from the cyclic-algebra coordinates that

$$
(\mathfrak P_D^r)^\perp=\mathfrak P_D^{-r-1}.
\tag{9.11}
$$

Let $m=c_D(\rho)\ge1$.  On $S_r$, right $U_D^m$-invariance is additive constancy modulo
$\mathfrak P_D^{r+m}$, since

$$
x(1+u)=x+xu,
\qquad x\mathfrak P_D^m=\mathfrak P_D^{r+m}.
\tag{9.11a}
$$

Hence the finite transform on that shell is the perfect pairing

$$
\frac{\mathfrak P_D^r}{\mathfrak P_D^{r+m}}
\times
\frac{\mathfrak P_D^{-r-m-1}}{\mathfrak P_D^{-r-1}}
\longrightarrow\mathbf C^\times,
\qquad(x,y)\longmapsto\psi(\operatorname{Trd}(xy)).
\tag{9.11b}
$$

It reaches the outer layer
$\mathfrak P_D^{-r-m-1}/\mathfrak P_D^{-r-m}$ for some matrix coefficient.  Otherwise finite
Fourier inversion would make every coefficient right $U_D^{m-1}$-invariant; the intersection
of their kernels would put $U_D^{m-1}$ in the kernel of $\rho$, contradicting the minimality
of $m$.

Now

$$
[\mathcal O_D:\mathfrak P_D^r]=q^{2r},
\qquad d(\Pi x)=q^{-2}dx,
\qquad|\operatorname{Nrd}\Pi|=q^{-1}.
\tag{9.11c}
$$

Using (9.4b), pair shell $r$ with shell $-r-m-1$ in (9.11b).  The powers involving $r$
cancel between the two sides of (9.6); the remaining displacement is

$$
q^{-(m+1)(s-1/2)}.
\tag{9.11d}
$$

After removing it, the transform is a linear map on the finite coefficient block.  It
intertwines the two $D^\times$-actions, hence is scalar by Schur's lemma; finite Fourier
inversion makes the scalar nonzero.  This proves the exact exponent $m+1$ whenever the
$\mathcal O_D^\times$-average is zero.

If $\dim\rho>1$, that average is zero for every coefficient.  A nonzero
$\mathcal O_D^\times$-fixed vector would, by normality and irreducibility, make the entire
compact group act trivially and force $\rho$ to be one dimensional.  On sufficiently deep
shells approaching zero, a Schwartz function is constant in the angular variable, so the
tail vanishes.  Every zeta integral is a Laurent polynomial, and a single-shell choice gives a
unit of its fractional ideal.  Thus $L_D=1$.  Since $m=c_D(\rho)$, (9.11d) gives
$a_D(\rho)=m+1$.

Let $\rho=\mu\circ\operatorname{Nrd}$.  If $\mu$ is unramified, take
$\Phi=\mathbf1_{\mathcal O_D}$.  With $\operatorname{vol}(\mathcal O_D^\times)=1$,

$$
\sum_{j\ge0}\mu(\varpi)^j q^{-j(s+1/2)}
=L(s+1/2,\mu).
\tag{9.11e}
$$

A division uniformizer has norm $-\varpi$, and an unramified character is trivial on $-1$.
Every other integral is this series times a Laurent polynomial, plus a Laurent polynomial, by
separating its eventually constant shell tail.  Thus (9.11e) is the normalized generator.
The identity $\mathcal O_D^\perp=\mathfrak P_D^{-1}$ gives one shell of Fourier displacement,
hence exponent one.

If $a(\mu)=r>0$, the $\mathcal O_D^\times$-average vanishes because reduced norm maps that
group onto $\mathcal O_K^\times$.  Thus $L_D=1$, the ramified Tate factor.  The exact norm
filtration

$$
\operatorname{Nrd}(U_D^m)=U_K^{\lceil m/2\rceil}
\tag{9.12}
$$

gives $c_D(\rho)=2r-1$, and (9.11d) gives exponent $2r$.  This proves (9.8)--(9.9). $\square$

Nothing in this proof uses a tame quadratic label or a Heisenberg model.  In particular,
(9.11b) and finite Fourier inversion remain valid at ramified dyadic places and for every
primitive wild Clifford representation.

### 9.7 The global matrix-coefficient integral

We now prove the global product formula used to compare the two algebras.  Let $F$ be a number
field, let $A/F$ be a central simple algebra of degree two, and put $G_A=A^\times$.  Let $\Pi$
be cuspidal if $A=M_2(F)$ and a noncharacter discrete automorphic representation if $A$ is
division.  For automorphic vectors $\varphi\in\Pi$ and
$\widetilde\varphi\in\Pi^\vee$, define

$$
C_{\varphi,\widetilde\varphi}(g)
=\int_{Z_A(\mathbf A)G_A(F)\backslash G_A(\mathbf A)}
\varphi(xg)\widetilde\varphi(x)\,dx.
\tag{9.12a}
$$

The two central characters cancel.  The integral is absolutely convergent: the quotient is
compact in the division case, while cusp forms and all their derivatives decrease rapidly in
every split cusp.  It is the invariant pairing
$\langle\Pi(g)\varphi,\widetilde\varphi\rangle$.  Normalize local pairings so that for pure
tensors

$$
C_{\varphi,\widetilde\varphi}(g)=\prod_w c_w(g_w).
\tag{9.12b}
$$

With the two vectors interchanged through the canonical double-dual pairing,
$\check C(g)=C(g^{-1})$ is the global coefficient of $\Pi^\vee$ whose local factors are the
$\check c_w$ of (9.5a).

For $\Phi\in\mathcal S(A(\mathbf A))$, set

$$
Z_A(s,\Phi,C)
=\int_{G_A(\mathbf A)}
\Phi(g)C(g)|\operatorname{Nrd}g|_{\mathbf A}^{s+1/2}\,d^\times g.
\tag{9.12c}
$$

For pure data this converges absolutely in a common right half-plane and

$$
Z_A(s,\Phi,C)=\prod_wZ_{A_w}(s,\Phi_w,c_w).
\tag{9.12d}
$$

To justify the infinite Fubini step, first integrate over a finite set of places and over the
standard compact units outside it.  Sum next over finitely supported valuation vectors.  The
absolute integral of the rapidly decreasing global matrix coefficient is a majorant in a far
right half-plane; monotone convergence for absolute values and dominated convergence for the
original integrand give (9.12d).  Almost every local factor is the spherical calculation of
Lemma 9.3, so this is the usual Euler tail.  Meromorphic continuation of the global integral
will continue the product; no termwise product outside the initial half-plane is asserted.

We give the kernel proof of that continuation and of the functional equation.  On
$G_A(\mathbf A)\times G_A(\mathbf A)$ put

$$
\Theta_\Phi(x,y)=\sum_{\xi\in A(F)}\Phi(x^{-1}\xi y),
\qquad
\Theta_\Phi^\times(x,y)=\sum_{\xi\in A(F)^\times}\Phi(x^{-1}\xi y).
\tag{9.12e}
$$

The first kernel is invariant under $G_A(F)$ in each variable and under the diagonal adelic
center.  Thus it lives on

$$
\mathfrak X_A=
\bigl(G_A(F)\backslash G_A(\mathbf A)\bigr)^2/
Z_A(\mathbf A)_{\mathrm{diag}};
\tag{9.12f}
$$

the remaining relative center is exactly the Mellin direction in (9.12c).  Truncate that
direction by
$T^{-1}\le|\operatorname{Nrd}(x^{-1}y)|\le T$.  On this truncated domain all sums and
integrals below are absolutely convergent.  Unfolding the open orbit in the $y$-variable gives

$$
\int_{\mathfrak X_A}^{(T)}
\Theta_\Phi^\times(x,y)\varphi(y)\widetilde\varphi(x)
|\operatorname{Nrd}(x^{-1}y)|^{s+1/2}\,dx\,dy
=Z_A^{(T)}(s,\Phi,C).
\tag{9.12g}
$$

Indeed the translates of a fundamental domain by $A(F)^\times=G_A(F)$ fill
$G_A(\mathbf A)$, the product formula removes the norm of the rational element, and the inner
$x$-integral is exactly (9.12a).  This is the promised automorphic unfolding, not a formal
factorization of local distributions.

Poisson summation on the four-dimensional additive space gives

$$
\Theta_\Phi(x,y)
=|\operatorname{Nrd}(x^{-1}y)|^{-2}
\Theta_{\widehat\Phi}(y,x).
\tag{9.12h}
$$

There is no covolume scalar: the global trace character makes $A(F)$ self-annihilating and the
product of the local self-dual measures is the quotient measure.  The restricted tensor product
of the normalized local transforms (9.4a) is the ordinary global transform in (9.12h): the
local Hasse signs occur exactly at the ramified places of $A$, and their product is
$(-1)^{|R(A)|}=1$.  The power $-2$ is the additive determinant of left or right multiplication
in degree two.  The constants $c_{A_w}$ in the multiplicative measures (9.4b) occur on both
sides of the unfolded identity and cancel; rescaling a local multiplicative Haar measure
multiplies both local zeta integrals, but not its gamma factor.

We must remove the singular terms before applying (9.12h) to (9.12g).

- If $A$ is division, the only singular rational point is $0$.  Its paired kernel is the
  projection of $\Pi$ to an automorphic norm character.  More explicitly, the relative norm
  weight factors into a period of $\varphi(y)|\operatorname{Nrd}y|^{s+1/2}$ and the dual
  period of $\widetilde\varphi(x)|\operatorname{Nrd}x|^{-s-1/2}$.  Either period is an
  intertwiner from $\Pi$ to a one-dimensional norm character, hence is zero because $\Pi$ is
  a noncharacter irreducible.
- If $A=M_2(F)$, the nonzero singular points form the single rank-one
  $G(F)\times G(F)$-orbit of
  $e=\left(\begin{smallmatrix}1&0\\0&0\end{smallmatrix}\right)$.  Unfolding its stabilizer
  writes its pairing as a product of upper and lower unipotent constant terms of
  $\varphi$ and $\widetilde\varphi$.  Both are zero by cuspidality.  In coordinates
  $uv^{\mathsf t}$, the quotient $(u,v)\sim(au,a^{-1}v)$ is the relative scalar Mellin
  variable; the two remaining integrations are exactly those constant terms.  Thus the
  rank-one contribution is identically zero before any limit is taken.
- The zero point on the split side is the same pair of determinant-character periods and also
  vanishes for a cuspidal representation.

These statements account for every rational stratum of a degree-two algebra.  They also show
why no Tate boundary term remains in the cuspidal matrix-coefficient equation: the degree-one
Tate transform describes the rank-one orbit before pairing, and cuspidality kills its
coefficient on both sides.

Here is the boundary passage explicitly.  Write $Z_A^{\ge1}$ for the unfolded integral with
$|\operatorname{Nrd}g|_{\mathbf A}\ge1$.  This integral is entire: on that half the Schwartz
function decreases faster than every norm power, uniformly against the rapidly decreasing
cuspidal coefficient; in the division case the projective variable ranges over a compact set.
On the complementary half insert (9.12h).  The singular kernel has zero pairing by the three
calculations above.  Swapping $x$ and $y$ replaces the relative norm $q$ by $q^{-1}$, while
$q^{s+1/2}q^{-2}=q^{s-3/2}$ becomes
$(q^{-1})^{(1-s)+1/2}$.  Therefore, first between symmetric truncation boundaries and then on
every compact $s$-set by dominated convergence,

$$
Z_A(s,\Phi,C)
=Z_A^{\ge1}(s,\Phi,C)
+Z_A^{\ge1}(1-s,\widehat\Phi,\check C).
\tag{9.12h-a}
$$

Formula (9.12h-a) is the continuation: both terms on its right are entire.  It also lists all
possible boundary contributions.  A zero-orbit Taylor coefficient would be one of the norm
character periods above, and a rank-one Taylor coefficient would be one of the two constant
terms above; every one is zero.  Thus no polar Taylor term, Poisson remainder, or truncation
constant survives.  Applying the same formula to the dual data and using Fourier inversion
gives the next identity.  The reflection $x\mapsto-x$ contributes the global central value
$\omega_\Pi(-1)$, which is $1$ because $-1\in F^\times$ and every automorphic central
character is trivial on $F^\times$:

$$
Z_A(1-s,\widehat\Phi,\check C)=Z_A(s,\Phi,C).
\tag{9.12i}
$$

This proves continuation, the global functional equation, and the absence of an unrecorded
Poisson or boundary term.

Apply the local equations (9.6) to pure data for which every local integral is nonzero.  Use
(9.12d) on the initial half-plane and then meromorphic continuation.  Equation (9.12i) gives

$$
\boxed{\prod_w\gamma_{A_w}(s,\Pi_w,\psi_w)=1.}
\tag{9.12j}
$$

Almost every term is the quotient of the two unramified Euler factors, so the product is
understood through (9.12d).  Changing finitely many local vectors shows that the scalar in
(9.12j) is independent of all choices.  The self-dual measure in (9.12h) shows that it is
exactly $1$.

### 9.8 Comparison for every additive character

First suppose that $\rho$ is unitary.  Globalize it as in Lemma 6.1, with $B$ ramified exactly at $v,u$ and with a selected
auxiliary component at $u$.  Let $\pi$ be the global split representation produced in Chapter
7.  Equation (7.2a) says that $\pi_w=\Pi_w$ at every split place and that the two components at
$u$ form the selected pair.

Use the same global additive character and the same self-dual measures in the product formulas
(9.12j) for $B$ and $M_2$.  Divide those formulas.  At every split place the local algebras,
representations, coefficients, and Fourier normalizations are identical, so the factors
cancel.  At $u$ they cancel by the independently proved selected factor theorem of Books
80--84.  If that theorem is stated for its conductor-zero character, (9.7d) extends it to the
actual component $\psi_u$: the selected pair has the same central character, so the two
change-of-character multipliers are identical.  Only $v$ remains:

$$
\gamma_D(s,\rho,\psi_v)
=\gamma_G(s,\operatorname{JL}(\rho),\psi_v).
\tag{9.13}
$$

This first equality uses the component $\psi_v$ of a global character.  It already implies the
equality for **every** nontrivial local additive character.  Indeed any such character is
$(\psi_v)_b$ for a unique $b\in K^\times$.  Theorem 7.1 gives equality of the two central
characters, and (9.7d) multiplies both sides of (9.13) by the same factor
$\omega_\rho(b)|b|^{2s-1}$.  Thus (9.13) holds for arbitrary local $\psi$, whether or not it is
itself the component of the chosen global character.

It remains to separate $L$ from $\epsilon$.  If $\rho=\mu\circ\operatorname{Nrd}$, (7.10)
identifies its image as $\operatorname{St}\otimes\mu$; Lemma 9.3 and (9.8) give the same factor
$L(s+1/2,\mu)$.  If $\dim\rho>1$, injectivity and (7.10) prevent its essentially
square-integrable image from being special, so it is supercuspidal.  Lemma 9.3 gives $L_G=1$,
agreeing with (9.8).  The normalized generators in (9.7) are therefore equal.  Substitution in
(9.13) gives, for every nontrivial $\psi$,

$$
L_D(s,\rho)=L_G(s,\operatorname{JL}(\rho)),
\qquad
\epsilon_D(s,\rho,\psi)
=\epsilon_G(s,\operatorname{JL}(\rho),\psi).
\tag{9.14}
$$

The same holds for gamma factors and contragredients.  For a nonunitary $\rho$, use the
unitary twist $\rho^{\mathrm u}$ of (7.0).  Formula (9.5b) shifts the Mellin variable by the
same amount on the two inner forms, while (7.2) identifies the two twist-back
representations.  Thus (9.13)--(9.14) hold for the original $\rho$ as well.  Applying the same
argument with an arbitrary quasicharacter $\chi$ proves compatibility for every norm twist;
it does not assume a tame label for the twisted representation.

Choose a conductor-zero additive character.  Unramified real twists do not change either
filtration conductor.  Comparing the exact exponent in (9.9) with
Lemma 9.4 proves

$$
\boxed{a(\operatorname{JL}(\rho))=a_D(\rho).}
\tag{9.15}
$$

This is the wild conductor theorem.  Its inputs are the finite division Fourier pairing
(9.11b), the split two-filtration Fourier pairing (9.7i), and the global product formula
(9.12j).  No transferred invariant-vector complex and no primitive-wild parameter is used.

### 9.9 The split newvector

Book 92 proves the local newvector theorem for every infinite-dimensional irreducible generic representation, explicitly including primitive wild supercuspidals. Combining it with (9.15) gives

$$
\dim\operatorname{JL}(\rho)^{K_1(\mathfrak p^n)}
=
\begin{cases}
0,&n<a_D(\rho),\\
n-a_D(\rho)+1,&n\ge a_D(\rho).
\end{cases}
\tag{9.16}
$$

In particular the minimal split line is one dimensional. No equality with $\rho^{U_D^m}$ is asserted. Because $U_D^m$ is normal, the latter space is either zero or all of $\rho$ and can have dimension greater than one.

### 9.10 Weil--Deligne parameters

In the principal, special, and tame-dihedral range, Books 80--84 already attach the common parameter and (9.14) agrees with their formulas. For example,

$$
\mu\circ\operatorname{Nrd}
\longmapsto
\operatorname{St}\otimes\mu
\longmapsto
\mu\otimes\operatorname{Sp}_2.
\tag{9.17}
$$

For a primitive wild $\rho$, Theorem 7.1 and (9.14)--(9.16) are unconditional. Under the separate theorem $\mathsf{LLC}_2^{\mathrm{wild}}$ of Section 1.3, define

$$
\operatorname{rec}_D(\rho)
:=\operatorname{rec}_2(\operatorname{JL}(\rho)).
\tag{9.18}
$$

Then its Artin conductor is $a_D(\rho)$ and its Artin local factors are (9.14). Without that prerequisite, (9.18) is not presented as an already constructed wild Weil--Deligne object. This is the sole unresolved dependency recorded in Chapter 17.


## 10. The two global spectra and exceptional characters

### 10.1 Fixed central character spaces

Let $D/F$ be nonsplit and fix a unitary Hecke character

$$
\omega:F^\times\backslash\mathbf A_F^\times\longrightarrow\mathbf C^\times.
\tag{10.1}
$$

Let $L^2(D,\omega)$ be the Hilbert space of functions satisfying

$$
\varphi(z\gamma g)=\omega(z)\varphi(g)
\tag{10.2}
$$

for $z\in Z_D(\mathbf A_F)$ and $\gamma\in D^\times(F)$, square-integrable modulo the center. Compactness gives a discrete decomposition

$$
L^2(D,\omega)
=\widehat{\bigoplus}_{\Pi}m_D(\Pi)\Pi.
\tag{10.3}
$$

Book 93 proves $m_D(\Pi)=1$ and strong determination for every constituent, without assuming total definiteness. On the split side, Book 92 proves automorphic multiplicity one and strong multiplicity one for the cuspidal spectrum.

Every infinite-dimensional member of (10.3) is cuspidal because $D^\times$ has no proper rational parabolic. The word “cuspidal” therefore does not separate the exceptional one-dimensional spectrum; it must be removed explicitly.

### 10.2 The exceptional spectrum

By (2.8), the one-dimensional summands of central character $\omega$ are exactly

$$
\Xi_\eta=\eta\circ\operatorname{Nrd},
\qquad \eta^2=\omega.
\tag{10.4}
$$

The corresponding split residual representation is

$$
\chi_\eta=\eta\circ\det.
\tag{10.5}
$$

Each occurs once. For a fixed test-function window, only finitely many such characters have nonzero trace. Define

$$
\mathcal A_0(D,\omega)
=\{\Pi\subset L^2(D,\omega):\Pi\text{ is not globally one dimensional}\}.
\tag{10.6}
$$

A member of $\mathcal A_0(D,\omega)$ may have a one-dimensional local component at a division place. The exclusion in (10.6) is global.

### 10.3 Why local transfer of a norm character is not global transfer

Applying Theorem 7.1 locally to $\Xi_\eta$ would produce Steinberg twists at the members of $R(D)$ and characters at the split places. That restricted tensor product is neither the residual character (10.5) nor a cuspidal automorphic representation. In the trace formula, the actual relation is the cancellation (5.9) multiplied over all places. Parity turns it into

$$
\operatorname{tr}\Xi_\eta(f^D)
=\operatorname{tr}\chi_\eta(f^G).
\tag{10.7}
$$

Thus a global norm character has no cuspidal Jacquet--Langlands image. This is why Theorem 5.3 and the global correspondence use $\mathcal A_0(D,\omega)$ rather than the entire discrete spectrum.


## 11. Forward global transfer

### 11.1 Producing the split constituent

Take $\Pi\in\mathcal A_0(D,\omega)$. At every $v\in R(D)$ choose a normalized matrix coefficient $e_{\Pi_v}^D$ with trace one on $\Pi_v$, and choose a signed transfer. Theorem 7.1 and Weyl integration give

$$
\operatorname{tr}\sigma_v(e_{\Pi_v}^G)
=
\begin{cases}
1,&\sigma_v\simeq\operatorname{JL}_v(\Pi_v),\\
0,&\sigma_v\text{ is a different essentially square-integrable irreducible},
\end{cases}
\tag{11.1}
$$

after finite interpolation within the chosen window. Principal-series traces are zero by (4.3). At a real division place use the Euler--Poincare selector of Chapter 8.

Let $S$ contain $R(D)$, the infinite places, and all ramified data. The fixed-level, fixed-infinity subspace on the compact quotient is finite dimensional. Strong determination and interpolation in the spherical algebra outside $S$ produce an element $p^S$ which has trace one on $\Pi$ and trace zero on every other division constituent in the window. For arbitrary $h$ in the away-from-$S$ spherical algebra, insert $p^Sh$ into a matched clean pair.

The left side of (5.10) is

$$
c_D\lambda_\Pi(h),
\qquad c_D\ne0,
\tag{11.2}
$$

and the right side is a finite sum

$$
\sum_{j=1}^r c_j\lambda_{\pi_j}(h).
\tag{11.3}
$$

Characters of a commutative algebra are linearly independent. Hence one $\pi_j$ has the same almost-everywhere Hecke character as $\Pi$. Call it $\pi$. Book 92's strong multiplicity-one theorem makes $\pi$ unique.

This proves automorphic existence. No formal tensor product of local images was assumed to occur.

### 11.2 Recovering every local component

Fix a place $w$. Strong determination on $D^\times$ permits a projector away from $w$ which isolates $\Pi$ in a finite window: any competitor agreeing away from $w$ would agree almost everywhere and hence equal $\Pi$. Strong multiplicity one gives the analogous projector for $\pi$.

Keep those factors fixed and vary $f_w^D$. If $w$ is split, set $f_w^G=f_w^D$; if it is division, take a signed transfer. The clean identity reduces to

$$
m_D(\Pi)A\operatorname{tr}\Pi_w(f_w^D)
=m_G(\pi)B\operatorname{tr}\pi_w(f_w^G).
\tag{11.4}
$$

Normalize every fixed local trace to one. At split places the fixed traces are identical, and at division places they agree by Theorems 7.1 and 8.1. Thus $A=B\ne0$. Books 92--93 give $m_D(\Pi)=m_G(\pi)=1$. Equality of local trace distributions now yields

$$
\pi_w\simeq
\begin{cases}
\Pi_w,&w\notin R(D),\\
\operatorname{JL}_w(\Pi_w),&w\in R(D).
\end{cases}
\tag{11.5}
$$

This includes every split bad place and every wild finite division place. Agreement at almost all places established uniqueness; variation in (11.4) establishes the claimed equality at all places.

### 11.3 Definition and compatibilities

Define

$$
\operatorname{JL}_D(\Pi)=\pi.
\tag{11.6}
$$

The local identities imply

$$
\omega_{\operatorname{JL}_D(\Pi)}=\omega_\Pi,
\tag{11.7}
$$

$$
\operatorname{JL}_D(\Pi\otimes(\chi\circ\operatorname{Nrd}))
\simeq
\operatorname{JL}_D(\Pi)\otimes(\chi\circ\det),
\tag{11.8}
$$

and

$$
\operatorname{JL}_D(\Pi^\vee)
\simeq\operatorname{JL}_D(\Pi)^\vee.
\tag{11.9}
$$

Strong multiplicity one promotes the local almost-everywhere compatibilities to these global isomorphisms. If two division representations have the same global transfer, (11.5) and local bijectivity recover every component, so the global map is injective.


## 12. Reverse transfer and the exact image

### 12.1 Necessity of the local condition

If $\pi=\operatorname{JL}_D(\Pi)$, then (11.5) forces

$$
\pi_v\in\operatorname{Irr}_{\mathrm{ess.disc}}(\operatorname{GL}_2(F_v))
\qquad(v\in R(D)).
\tag{12.1}
$$

At a finite place this means a Steinberg twist or a supercuspidal representation. At a ramified real place it means a genuine full discrete series. There is no condition at a split place.

### 12.2 Sufficiency

Now let $\pi$ be cuspidal and assume (12.1). For every division place put

$$
\rho_v=\operatorname{JL}_v^{-1}(\pi_v).
\tag{12.2}
$$

Choose normalized local selectors for these representations and identical nonzero trace functions at the split exceptional places. In a finite window, choose an away-from-$S$ Hecke projector isolating the almost-everywhere eigencharacter of $\pi$. Apply (5.10) from right to left. If the left side contained no division constituent with that Hecke character, linear independence of algebra characters would contradict the nonzero isolated term on the right. Hence some

$$
\Pi\in\mathcal A_0(D,\omega)
\tag{12.3}
$$

has the same good Hecke character. The clean identity is essential: it prevents the constituent in (12.3) from being a norm character.

Varying one place at a time as in (11.4) gives

$$
\Pi_v\simeq
\begin{cases}
\pi_v,&v\notin R(D),\\
\rho_v,&v\in R(D).
\end{cases}
\tag{12.4}
$$

The forward transfer of $\Pi$ is therefore $\pi$, and strong determination makes $\Pi$ unique.

### 12.3 The global theorem

**Theorem 12.1 (global Jacquet--Langlands for arbitrary quaternion signature).** Let $F$ be a number field and $D/F$ a quaternion algebra. If $D$ is nonsplit, there is a unique bijection

$$
\boxed{
\operatorname{JL}_D:
\mathcal A_0(D^\times)
\xrightarrow{\sim}
\left\{
\pi\in\mathcal A_{\mathrm{cusp}}(\operatorname{GL}_2/F):
\pi_v\text{ is essentially square-integrable for every }v\in R(D)
\right\}.}
\tag{12.5}
$$

It is the identity at split places and the full local correspondence at division places. It preserves central characters, twists, contragredients, independently defined nonarchimedean local factors, conductor ideals, and automorphic multiplicity. Every occurrence has multiplicity one. Its excluded spectrum consists exactly of the global norm characters.

If $D\simeq M_2(F)$, define $\operatorname{JL}_D$ to be the identity on the cuspidal spectrum. The image condition is then vacuous, and no one-dimensional residual representation is placed in the cuspidal spectrum.

**Proof.** The nonsplit forward construction is Chapter 11; Sections 12.1--12.2 prove the exact image and inverse. The compatibilities are Chapters 7--9 and Section 11.3. The split case is tautological. $\square$

The proof used only global division, not total definiteness. In particular, it applies when $D$ is split at two or at all real places and is ramified at finite places.


## 13. The cohomological range

### 13.1 General real weights

Assume $F$ is totally real. For each real place choose $k_v\ge2$ and a norm exponent $s_v$, with central characters arising from one global algebraic Hecke character. Define

$$
\Pi_v^{\mathrm{coh}}=
\begin{cases}
D_{k_v}\otimes|\det|^{s_v},&D_v\text{ split},\\
\tau_{k_v-2,s_v},&D_v\simeq\mathbf H.
\end{cases}
\tag{13.1}
$$

Theorem 8.1 sends both cases to the same full split discrete series:

$$
\operatorname{JL}_v(\Pi_v^{\mathrm{coh}})
=D_{k_v}\otimes|\det|^{s_v}.
\tag{13.2}
$$

Therefore Theorem 12.1 restricts to a bijection between noncharacter automorphic representations with infinity type (13.1) and cuspidal split representations having (13.2) at every real place and essentially square-integrable components at every finite member of $R(D)$.

The finite condition cannot be omitted. Cohomological infinity type alone does not guarantee an inverse transfer to a quaternion algebra with auxiliary finite ramification.

### 13.2 Exactly two active real places

Suppose $D$ is split at exactly two real places $v_1,v_2$ and ramified at every other real place. For constant coefficients the quaternionic type is

$$
\Pi_{v_1}=\Pi_{v_2}=D_2,
\qquad
\Pi_v=\mathbf1_{\mathbf H^\times}
\quad(v\mid\infty,\ v\ne v_1,v_2).
\tag{13.3}
$$

Its split transfer is

$$
\operatorname{JL}_D(\Pi)_v=D_2
\qquad(v\mid\infty).
\tag{13.4}
$$

At the active places (13.4) is identity transfer. At a definite place it is the nontrivial row (8.6). Restriction at $v_1,v_2$ gives the four orientation lines (8.8), all belonging to one full archimedean representation.

If $D$ is split at all real places but remains a division algebra globally, the same theorem applies. Its even nonempty finite ramification set supplies both the trace-formula places and the local image conditions.


## 14. Levels, good Hecke modules, and rationality

### 14.1 Exact conductor and the global newvector

Let $\Pi\in\mathcal A_0(D^\times)$ and $\pi=\operatorname{JL}_D(\Pi)$. At a split finite place the local representations are identical. At a division finite place, (9.15) applies. Hence

$$
\boxed{
\mathfrak f(\pi)=
\prod_{v\notin R_f(D)}\mathfrak p_v^{a(\Pi_v)}
\prod_{v\in R_f(D)}\mathfrak p_v^{a_D(\Pi_v)}.}
\tag{14.1}
$$

This is an exact ideal, including wild and dyadic places. If $\Pi_v$ is a higher-dimensional wild representation, its exponent is $c_D(\Pi_v)+1$. If it is an unramified norm character, its exponent is one.

Book 92 and (9.16) give

$$
\dim\pi_f^{K_1(\mathfrak f(\pi))}=1.
\tag{14.2}
$$

More generally, for $\mathfrak n=\prod_v\mathfrak p_v^{m_v}$ divisible by $\mathfrak f(\pi)$, with $n_v=a(\pi_v)$,

$$
\dim\pi_f^{K_1(\mathfrak n)}
=\prod_{v\mid\mathfrak n}(m_v-n_v+1).
\tag{14.3}
$$

There is no corresponding equality with a raw division invariant space. At a normal subgroup $U_D^r$ that space jumps from zero to the entire finite-dimensional representation.

### 14.2 Good Hecke modules

Let $\Sigma$ contain $R_f(D)$, all level and central-character primes, and every place without a fixed integral splitting. For $v\notin\Sigma$, both local representations are spherical for the same hyperspecial subgroup. Equation (11.5) identifies their one-dimensional spherical lines and the raw operators of Book 90. Therefore

$$
t_v(\Pi)=t_v(\pi),
\qquad
s_v(\Pi)=s_v(\pi),
\tag{14.4}
$$

and

$$
P_v(X,\Pi)
=1-t_v(\Pi)X+q_vs_v(\Pi)X^2
=P_v(X,\pi).
\tag{14.5}
$$

The whole spherical Hecke character agrees, not merely the two displayed generators. At a common split bad place, the full local group and every chosen compact-open Hecke module are identical. At a division place there is no canonical equality with a split double-coset algebra; comparison there is through the local representation, conductor, and factors.

### 14.3 Algebraicity from the actual arithmetic input

Rationality will be asserted only in the parallel weight-two setting covered by Book 107. Let $\Pi$ have the type (13.3), or more generally a parallel weight-two quaternionic cohomological type, and put $\pi=\operatorname{JL}_D(\Pi)$.

Book 107 starts with the rational fixed-weight cuspidal Hecke module on the split side. Its finite commutative image algebra is defined over a number field and is reduced in characteristic zero. Theorem 3.1 and the weight-two packet theorem there prove that the raw eigenvalues in

$$
E(\pi)=
\mathbf Q(t_v(\pi),s_v(\pi):v\notin\Sigma)
\tag{14.6}
$$

are algebraic and generate a number field. This is the required arithmetic source. We do not infer algebraicity from a complex spectral decomposition or invoke an unstated identification of quaternionic automorphic forms with surface cohomology.

By (14.4), define the quaternionic good Hecke field from the identical coefficients. Then

$$
\boxed{E(\Pi)=E(\pi).}
\tag{14.7}
$$

Enlarging $\Sigma$ does not change this good Hecke field. Indeed, Book 107 realizes every embedding of the field generated outside the larger set by a conjugate split eigensystem. If such an embedding fixes the remaining polynomials, strong multiplicity one fixes $\pi$ and hence all of its good eigenvalues. Equation (14.4) transfers the same conclusion to $\Pi$. This is an argument with the rational split Hecke module plus multiplicity one, not multiplicity one by itself.

### 14.4 Exact scope of algebraic conjugation

Let $\iota:E(\pi)\hookrightarrow\mathbf C$. Book 107 constructs a conjugate split weight-two representation $\pi^\iota$ from the rational Hecke module, with

$$
P_v(X,\pi^\iota)=\iota(P_v(X,\pi))
\tag{14.8}
$$

outside a finite set. This proves that every embedding of the common field (14.7) occurs on the split side. It also proves, when the full minimal-level module is used, that the conductor ideal and parallel weight are unchanged.

There is a distinction which the rationality statement must retain. Book 107 determines the ramified factors of the globally constructed $\pi^\iota$, but it does not identify them with entrywise semilinear conjugates of arbitrary analytic local models. Thus good Hecke conjugation alone does not prove that $\pi_v^\iota$ is essentially square-integrable at each $v\in R(D)$. We therefore do not manufacture a quaternionic $\Pi^\iota$ from (14.8).

The local statement that is actually proved is (7.12): if a local representation is semilinearly conjugated, then local Jacquet--Langlands commutes with that operation. Consequently, whenever a conjugate automorphic representation has those semilinearly conjugated ramified factors, the exact image theorem gives

$$
\operatorname{JL}_D(\Pi^\iota)\simeq\pi^\iota.
\tag{14.9}
$$

The unconditional rationality package needed here is precisely algebraicity of all raw good Hecke coefficients, finiteness and equality of the fields in (14.7), and occurrence of every conjugate good split eigensystem. A stronger assertion about the full bad-place field of definition would require an additional rational structure on the quaternionic automorphic module; it is not inferred from a complex spectral decomposition or from an unstated surface cohomology identification.


## 15. Transfer between two quaternion inner forms

### 15.1 The common split intermediary

Let $D$ and $D'$ be quaternion algebras over $F$. For noncharacter automorphic representations define

$$
\operatorname{JL}_{D\to D'}
=\operatorname{JL}_{D'}^{-1}\circ\operatorname{JL}_D
\tag{15.1}
$$

whenever the inverse is defined. If $\Pi$ is on $D^\times$ and $\pi=\operatorname{JL}_D(\Pi)$, the necessary and sufficient condition is

$$
\pi_v\text{ essentially square-integrable for every }v\in R(D').
\tag{15.2}
$$

When it exists, the transfer is unique and transitive. Locally,

$$
(\operatorname{JL}_{D\to D'}\Pi)_v=
\begin{cases}
\Pi_v,&D_v,D_v'\text{ both split},\\
\operatorname{JL}_v(\Pi_v),&D_v\text{ division},\ D_v'\text{ split},\\
\operatorname{JL}_v^{-1}(\Pi_v),&D_v\text{ split},\ D_v'\text{ division},\\
\operatorname{JL}_{D_v'}^{-1}(\operatorname{JL}_{D_v}(\Pi_v)),
&D_v,D_v'\text{ both division}.
\end{cases}
\tag{15.3}
$$

The last row is meaningful because both local division groups use the same split discrete intermediary.

### 15.2 Definite to two-active signature

Let $F$ be totally real, let $D_0$ be totally definite, and let $D_{12}$ have the same finite invariants but be split at $v_1,v_2$. Suppose $\Pi^0$ has the constant-coefficient type

$$
(\Pi^0)_v=\mathbf1_{\mathbf H^\times}
\qquad(v\mid\infty).
\tag{15.4}
$$

Its split transfer has $D_2$ at every real place. Since $D_0$ and $D_{12}$ have the same finite ramification, condition (15.2) is automatic. The unique representation $\Pi^{12}$ has

$$
(\Pi^{12})_v=
\begin{cases}
D_2,&v=v_1,v_2,\\
\mathbf1_{\mathbf H^\times},&v\ne v_1,v_2,
\end{cases}
\qquad
(\Pi^{12})_w=(\Pi^0)_w\quad(w<\infty).
\tag{15.5}
$$

The finite Hecke character, conductor, finite local factors, and multiplicity are unchanged. The two changed real places each reverse the local orbital sign, so their product is $+1$; this is the real-sign version of (3.11).


## 16. The two-active-place surface interface

### 16.1 The exact quaternion algebra

Let $W=b\langle1,-a\rangle$ be the anisotropic Hermitian plane of Book 129, of signature $(1,1)$ at $v_1,v_2$ and definite elsewhere. Its derived quaternion algebra is the actual cyclic algebra

$$
Q_a=(K/F,a),
\tag{16.1}
$$

not an arbitrary prescribed quaternion algebra agreeing at good places. By (2.15), $Q_a$ is a division algebra. Its complete ramification set is

$$
v\in R(Q_a)
\Longleftrightarrow
K_v/F_v\text{ is a field and }
a\notin N_{K_v/F_v}(K_v^\times).
\tag{16.2}
$$

It is split at $v_1,v_2$, Hamiltonian at every definite real place, and may have auxiliary finite ramification. Every such finite place must be included in the local image condition.

### 16.2 The quaternionic theorem needed by the surface

**Theorem 16.1.** Noncharacter automorphic representations $\Pi$ of $Q_a^\times(\mathbf A_F)$ are in bijection with cuspidal representations $\pi$ of $\operatorname{GL}_2(\mathbf A_F)$ which are essentially square-integrable at every member of the exact set $R(Q_a)$. For the constant-coefficient real type,

$$
\Pi_{v_1}=\Pi_{v_2}=D_2,
\qquad
\Pi_v=\mathbf1_{\mathbf H^\times}
\quad(v\mid\infty,\ v\ne v_1,v_2),
\tag{16.3}
$$

and $\pi_v=D_2$ at every real place. The transfer preserves the exact conductor (14.1), independently defined finite local factors, multiplicity, the good raw polynomial (14.5), and in parallel weight two the common Hecke field (14.7).

**Proof.** Apply Theorem 12.1 to the division algebra $Q_a$. The real assertion is (13.3)--(13.4), and the arithmetic assertions are Chapters 9 and 14. $\square$

If Book 129 starts with a different quaternion algebra $B$, a representation on $B^\times$ passes to $Q_a^\times$ exactly when its common split transfer is discrete at every place in $R(Q_a)$. Agreement away from an auxiliary set proves equality only of the good Hecke systems there; it does not remove this exact local condition.

### 16.3 The common-norm intermediary

The full surface group is not obtained by quotienting $\operatorname{Res}_{F/\mathbf Q}Q_a^\times$ by a center and reading off multiplicities. The correct intermediate group is the fiber product

$$
H=
\operatorname{Res}_{F/\mathbf Q}Q_a^\times
\times_{\operatorname{Res}_{F/\mathbf Q}\mathbf G_m}
\mathbf G_m,
\tag{16.4}
$$

where the first map is reduced norm and the second is the diagonal inclusion. Thus for a $\mathbf Q$-algebra $R$,

$$
H(R)=
\left\{
b\in(Q_a\otimes_F(F\otimes_{\mathbf Q}R))^\times:
\operatorname{Nrd}(b)\in R^\times
\right\}.
\tag{16.5}
$$

The embedding of $Q_a$ into $\operatorname{End}_K(W)$ from Book 129 carries an element of $H$ to a unitary similitude with the same rational multiplier. It induces the already proved derived-group identification

$$
H^{\mathrm{der}}
=\operatorname{Res}_{F/\mathbf Q}\operatorname{SL}_1(Q_a)
\xrightarrow{\sim}
\operatorname{Res}_{F/\mathbf Q}\operatorname{SU}(W)
=G_W^{\mathrm{der}}.
\tag{16.6}
$$

Equations (16.4)--(16.6) are the entire full-group interface asserted here. Restricting an automorphic representation from $Q_a^\times$, ascending it to $H$ or $G_W$, solving central cocycles and component equations, and proving multiplicity on $G_W$ are separate tasks. They are deferred to the later central automorphic descent treatment. No quotient-dimension formula, automatic descent, or full-group multiplicity assertion is made in this book.

### 16.4 What the four orientations do and do not say

At the two active derived real factors, (16.3) restricts as

$$
D_2\boxtimes D_2
\big|_{\operatorname{GL}_2(\mathbf R)^+\times
\operatorname{GL}_2(\mathbf R)^+}
=\bigoplus_{\epsilon_1,\epsilon_2\in\{+,-\}}
D_2^{\epsilon_1}\boxtimes D_2^{\epsilon_2}.
\tag{16.7}
$$

The relative complexes give the four Hodge types in (8.8). Finite Hecke operators commute with this archimedean complex, so the four local orientation lines carry the same derived finite Hecke character before any component selection.

This calculation does not say that all four lines occur on a chosen connected component, that they form four automorphic occurrences, or that an automorphic representation of $G_W$ has multiplicity one. Those conclusions require the restriction, ascension, and component analysis deliberately excluded after (16.6).


## 17. Dependency ledger and conclusion

### 17.1 Exact direct dependency row

The direct numbered dependency row is

$$
\boxed{
\text{197}\mid
6,\ 80\text{--}84,\ 87,\ 90,\ 92\text{--}93,\ 98\text{--}99,\
107,\ 109\text{--}110,\ 112,\ 123,\ 129.}
\tag{17.1}
$$

The uses are as follows.

- Book 6 supplies global character extension, arithmetic reciprocity, and idele-class character determination.
- Books 80--84 supply Weil--Deligne and local-constant normalizations, the exhaustive finite Clifford description of division representations, and the selected special and dihedral local correspondences used at auxiliary places.
- Book 87 supplies quaternion invariants, parity, reduced norms, embeddings, and local-global classification.
- Book 90 supplies the raw good Hecke operators and the polynomial $1-T_vX+q_vS_vX^2$.
- Book 92 supplies the rank-one Jacquet alternative, split multiplicity one, strong multiplicity one, and the full generic newvector theorem, including primitive wild representations.
- Book 93 supplies anisotropic compactness, division multiplicity one, strong determination, and the local elliptic Bessel estimates used in finite-window isolation.
- Book 98 supplies additive Fourier inversion, Poisson summation, self-dual measure normalization, and the degree-one Tate equation used on the rank-one boundary.  Chapter 9 proves the degree-two local and global zeta theory itself.
- Book 99 supplies the full real discrete-series characters and relative Lie algebra calculations.
- Book 107 supplies the actual rational Hecke module, algebraicity, conjugation, and Hecke-field theorem in parallel weight two.
- Books 109--110 supply the regularized spectral terms, trace-class bounds, scalar distribution, parabolic unfolding, cusp-boundary estimate, and absolutely convergent elliptic expansion.
- Book 112 supplies arbitrary orbital transfer, tree Euler functions, singular germs, central matching bumps, and selected spectral calibration.
- Book 123 supplies the inner-form, restriction-of-scalars, and derived-group framework.
- Book 129 supplies the Hermitian plane, cyclic algebra, explicit derived-group isomorphism, rational-multiplier surface group, and auxiliary-place boundary.

Book 94 is not an input: its totally definite selected-range theorem is superseded here. Books 133 and 196 are not inputs. In particular, no unitary-surface cohomology decomposition and no later central automorphic descent theorem is used.

### 17.2 What is now proved

The difficult logical layers are separate:

| layer | input | output |
|---|---|---|
| local geometry | slices, regular-orbital quotients, averaged Abel transform, tree Euler function, scalar germs | forward transfer of every division test and a smooth reverse for every zero-Abel split test |
| global comparison | compact inner trace, two trace-cuspidal places, scalar matching, parity | the character-clean identity (5.10) |
| local spectral transfer | two globalization lemmas and variation of local tests | the full wild bijection and signed character identity |
| arithmetic invariants | division Fourier lattices, global zeta functional equations, split newforms | exact conductors, finite factors, and split newvector lines |
| global automorphy | spectral isolation and local variation | forward and reverse transfer with exact image |
| surface interface | $Q_a$, common norm, two real relative complexes | the quaternionic theorem, group $H$, and four derived orientation lines |

This proof retains the valid signs and removes the invalid shortcuts. The local wild correspondence is produced by actual automorphic constituents, not by confusing orbital and representation lattices. The two-place logarithmic-derivative cancellation is used only inside an already regularized trace formula. Scalar terms and residual characters are written separately. Conductors come from functional equations, not an unconstructed transfer of invariant-vector complexes. Rationality comes from Book 107's arithmetic Hecke module, not an unstated Matsushima identification. The surface discussion stops at the common-norm group (16.4).

### 17.3 The proposed prerequisite split

One dependency remains absent from the numbered route: $\mathsf{LLC}_2^{\mathrm{wild}}$ of Section 1.3. A prerequisite volume inserted after Book 81 should contain, in order:

1. simple strata and maximal simple types for every supercuspidal representation of $\operatorname{GL}_2(K)$, including residue characteristic two;
2. the matching classification of primitive two-dimensional Weil representations and their projective inertia;
3. extension characters and rectifiers with determinant and twist normalization;
4. character-independent construction of the correspondence;
5. comparison of Artin and zeta $L$-, $\epsilon$-, and $\gamma$-factors and equality of Artin and newvector conductors.

Only after that volume exists may (9.18) be called an unconditional primitive-wild Weil--Deligne parameter. It is irreducible as a prerequisite: neither the finite Clifford classification of $D^\times$, the orbital transfer theorem, nor global Jacquet--Langlands constructs the missing Weil-group representation.

### 17.4 Conclusion

For a quaternion division algebra, compactness of the automorphic quotient depends on global anisotropy, not on ramification at every real place. The even ramification set supplies two places at which transferred Abel transforms vanish. Their two zero factors remove every logarithmic-derivative and parabolic boundary term, while matched scalar germs and explicit norm-character subtraction close the singular and residual parts of the trace formula.

Auxiliary globalization then converts this geometric comparison into the full local character correspondence, including ramified dyadic and primitive wild representations. Reversing the same construction proves surjectivity. The resulting local theorem supplies the exact global image condition, and one-place variation recovers every local component. Independent degree-two zeta functional equations prove finite conductor and local-factor compatibility; Book 92 supplies the split newvector. Good split places preserve the raw Hecke polynomial, and Book 107 gives the common parallel-weight-two Hecke field.

For the unitary surface, the applicable algebra is the actual division algebra $Q_a$ with its complete ramification set. The correct full-group bridge begins with the common-norm group $H$, while the four active orientation lines remain a derived archimedean calculation. Central ascension, component selection, and $G_W$ multiplicity lie beyond this book.

The representation-theoretic local and global Jacquet--Langlands theorem is therefore complete. The larger parameter-enhanced statement is not dependency-closed until the proposed full wild local Langlands volume is supplied; that exact boundary is now visible rather than concealed by a tame formula or a false lattice argument.
