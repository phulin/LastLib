# Local--Global Compatibility for Weight-Two Galois Representations

## Contents

1. [The local information carried by a global representation](#1-the-local-information-carried-by-a-global-representation)
   - [1.1 The comparison problem](#11-the-comparison-problem)
   - [1.2 Standing fields and Frobenius conventions](#12-standing-fields-and-frobenius-conventions)
   - [1.3 The geometric carriers](#13-the-geometric-carriers)
   - [1.4 Scope and logical boundary](#14-scope-and-logical-boundary)
2. [The rank-two Weil--Deligne dictionary](#2-the-rank-two-weil--deligne-dictionary)
   - [2.1 From quasi-unipotent inertia to a pair](#21-from-quasi-unipotent-inertia-to-a-pair)
   - [2.2 Frobenius semisimplification](#22-frobenius-semisimplification)
   - [2.3 Unramified and special parameters](#23-unramified-and-special-parameters)
   - [2.4 Finite and dihedral parameters](#24-finite-and-dihedral-parameters)
   - [2.5 Twists, duals, and determinants](#25-twists-duals-and-determinants)
3. [What a compatibility theorem must compare](#3-what-a-compatibility-theorem-must-compare)
   - [3.1 The automorphic local datum](#31-the-automorphic-local-datum)
   - [3.2 The geometric local datum](#32-the-geometric-local-datum)
   - [3.3 A rigidity criterion](#33-a-rigidity-criterion)
   - [3.4 Hecke isolation and exactness](#34-hecke-isolation-and-exactness)
4. [Good primes](#4-good-primes)
   - [4.1 The complete good-place ledger](#41-the-complete-good-place-ledger)
   - [4.2 Smooth proper specialization](#42-smooth-proper-specialization)
   - [4.3 The Frobenius polynomial](#43-the-frobenius-polynomial)
   - [4.4 Unramified local--global compatibility](#44-unramified-local--global-compatibility)
5. [Semistable curves and their packet parts](#5-semistable-curves-and-their-packet-parts)
   - [5.1 The weight complex of a nodal fiber](#51-the-weight-complex-of-a-nodal-fiber)
   - [5.2 Restricting monodromy to a multiplicity space](#52-restricting-monodromy-to-a-multiplicity-space)
   - [5.3 The zero-monodromy branch](#53-the-zero-monodromy-branch)
   - [5.4 The nonzero-monodromy branch](#54-the-nonzero-monodromy-branch)
6. [Steinberg compatibility](#6-steinberg-compatibility)
   - [6.1 The special parameter without square roots](#61-the-special-parameter-without-square-roots)
   - [6.2 The graph line and the bad Hecke operator](#62-the-graph-line-and-the-bad-hecke-operator)
   - [6.3 The Steinberg theorem](#63-the-steinberg-theorem)
   - [6.4 Split and nonsplit multiplicative signs](#64-split-and-nonsplit-multiplicative-signs)
7. [Finite descent and inertial type](#7-finite-descent-and-inertial-type)
   - [7.1 Restoring the descent action](#71-restoring-the-descent-action)
   - [7.2 Type projectors on the stratum complex](#72-type-projectors-on-the-stratum-complex)
   - [7.3 Finite-type compatibility](#73-finite-type-compatibility)
   - [7.4 Wild and tame boundaries](#74-wild-and-tame-boundaries)
8. [Tame dihedral types](#8-tame-dihedral-types)
   - [8.1 Quadratic induction](#81-quadratic-induction)
   - [8.2 The unramified quadratic case](#82-the-unramified-quadratic-case)
   - [8.3 The ramified quadratic case](#83-the-ramified-quadratic-case)
   - [8.4 The tame dihedral comparison theorem](#84-the-tame-dihedral-comparison-theorem)
9. [Unitary surfaces and cancellation](#9-unitary-surfaces-and-cancellation)
   - [9.1 The honest surface monodromy](#91-the-honest-surface-monodromy)
   - [9.2 Local cancellation data](#92-local-cancellation-data)
   - [9.3 The logarithm on a Hom factor](#93-the-logarithm-on-a-hom-factor)
   - [9.4 Surface local--global compatibility](#94-surface-local--global-compatibility)
   - [9.5 Why cancellation hypotheses cannot be weakened](#95-why-cancellation-hypotheses-cannot-be-weakened)
10. [Local factors, conductors, and epsilon factors](#10-local-factors-conductors-and-epsilon-factors)
    - [10.1 Euler factors](#101-euler-factors)
    - [10.2 Artin, Swan, and monodromy conductors](#102-artin-swan-and-monodromy-conductors)
    - [10.3 The basic rank-two calculations](#103-the-basic-rank-two-calculations)
    - [10.4 Epsilon factors](#104-epsilon-factors)
11. [Coefficients and integral structures](#11-coefficients-and-integral-structures)
    - [11.1 Extension of the coefficient field](#111-extension-of-the-coefficient-field)
    - [11.2 Saturated packet lattices](#112-saturated-packet-lattices)
    - [11.3 Integral monodromy and its denominators](#113-integral-monodromy-and-its-denominators)
    - [11.4 The coefficient prime](#114-the-coefficient-prime)
12. [The compatibility theorem](#12-the-compatibility-theorem)
    - [12.1 Complete statement](#121-complete-statement)
    - [12.2 Proof](#122-proof)
    - [12.3 Consequences](#123-consequences)
13. [Diagnostic calculations and false inferences](#13-diagnostic-calculations-and-false-inferences)
    - [13.1 A good prime](#131-a-good-prime)
    - [13.2 One loop and a separating node](#132-one-loop-and-a-separating-node)
    - [13.3 A tame dihedral parameter](#133-a-tame-dihedral-parameter)
    - [13.4 A surface with two bad directions](#134-a-surface-with-two-bad-directions)
    - [13.5 Equal conductors and unequal types](#135-equal-conductors-and-unequal-types)
14. [Dependency and hypothesis audit](#14-dependency-and-hypothesis-audit)
    - [14.1 Imported geometric results](#141-imported-geometric-results)
    - [14.2 Exact hypothesis ledger](#142-exact-hypothesis-ledger)
    - [14.3 Final synthesis](#143-final-synthesis)

## 1. The local information carried by a global representation

A global Galois representation is constructed from the cohomology of a variety, but its restriction at a finite place is controlled by the geometry of one integral fiber. Local--global compatibility is the assertion that this geometric restriction is the same local parameter that the automorphic packet prescribes. At a smooth fiber the assertion is a Frobenius polynomial. At a singular fiber it is much richer: one must compare finite inertia, nilpotent monodromy, Frobenius on the surviving invariant space, and the conductor.

### 1.1 The comparison problem

Let $E$ be the field over which a selected Shimura curve or unitary surface is defined, let $u$ be a finite place of $E$, and let $K=E_u$. A parallel-weight-two packet $\Pi$ gives, by the cohomological extraction already established, a continuous semisimple representation

$$
\rho_{\Pi,\lambda}:G_E\longrightarrow
\operatorname{GL}_2(L_\lambda)
\tag{1.1}
$$

in the curve case. The same notation is used for a rank-two surface factor only when a descended cancellation datum has been supplied. Here $L$ is a finite splitting field for the relevant Hecke algebra and $\lambda\mid\ell$.

Restrict (1.1) to $G_K$, with $u\nmid\ell$. The local monodromy theorem packages this restriction into a Weil--Deligne representation

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})=(r_{u,\lambda},N_{u,\lambda}).
\tag{1.2}
$$

The automorphic local factor $\Pi_v$, at the place $v$ below $u$, supplies a second parameter $D(\Pi_v)$. In the range treated here that second parameter is described explicitly rather than hidden behind a general correspondence: it is unramified, special, or finite with a prescribed tame dihedral inducing datum. The comparison sought is

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq D(\Pi_v)\otimes_{L,\iota_\lambda}L_\lambda.
\tag{1.3}
$$

Frobenius semisimplification is essential. Good characteristic polynomials cannot detect a unipotent extension in the Frobenius direction, while monodromy must not be discarded.

### 1.2 Standing fields and Frobenius conventions

Let $K$ be a nonarchimedean local field with residue field $k$ of cardinality $q$ and residue characteristic $p$. Write $G_K$, $I_K$, and $P_K$ for its absolute Galois group, inertia, and wild inertia. The Weil group fits into

$$
1\longrightarrow I_K\longrightarrow W_K
\xrightarrow{\nu}\mathbf Z\longrightarrow0.
\tag{1.4}
$$

We choose a lift $\Phi$ of **geometric Frobenius**, the inverse of $x\mapsto x^q$, and normalize

$$
\nu(\Phi)=1,
\qquad |w|=q^{-\nu(w)},
\qquad |\Phi|=q^{-1}.
\tag{1.5}
$$

Local reciprocity sends a uniformizer to geometric Frobenius. The Tate twist is fixed by

$$
\Phi\mid L_\lambda(1)=q^{-1}.
\tag{1.6}
$$

Thus a monodromy operator has the typed form

$$
N:V\longrightarrow V(-1),
\tag{1.7}
$$

and, after suppressing the target twist,

$$
r(\Phi)Nr(\Phi)^{-1}=q^{-1}N.
\tag{1.8}
$$

Arithmetic Frobenius is $\Phi^{-1}$. Its eigenvalues are the inverses of the geometric eigenvalues. Every polynomial and local factor below uses geometric Frobenius unless the word arithmetic is written explicitly.

For the extracted weight-two representation, the determinant is

$$
\det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi,
\tag{1.9}
$$

where $\eta_\Pi$ is the finite central-component character. Consequently, at a place where $\eta_\Pi$ is unramified and has geometric Frobenius value $s_v(\Pi)$,

$$
\det r_{u,\lambda}(\Phi)=q_us_v(\Pi).
\tag{1.10}
$$

### 1.3 The geometric carriers

There are two carriers. A compact quaternionic Shimura curve contributes a packet block

$$
P_{\Pi,\lambda}\otimes W_{\Pi,\lambda},
\qquad \dim W_{\Pi,\lambda}=2,
\tag{1.11}
$$

and Galois acts on the multiplicity space $W_{\Pi,\lambda}$. A compact unitary surface contributes an honest middle-cohomology block which is generally four-dimensional and pure of weight two. It contributes a rank-two weight-one representation only if an algebraic cancellation factor, its descent action, and its pairing have all been supplied.

At a good place, the carrier has a smooth proper integral model and ordinary specialization suffices. At a bad parahoric place, a verified rank-two lattice-chain local model gives a strict semistable curve or surface after the explicit regularization. Nearby cycles then replace ordinary specialization. Prime-to-$p$ Hecke correspondences extend to these models and commute with inertia, Frobenius, restriction, Gysin, and monodromy.

### 1.4 Scope and logical boundary

The local results in this book require $u\nmid\ell$. They cover:

- good hyperspecial places;
- strict semistable rank-two Iwahori places, including the Steinberg branch;
- finite inertial descent when its action on the geometric strata is retained;
- tame dihedral types whose quadratic cover, inducing character, and type projector occur in that descent complex;
- rank-two factors of unitary-surface cohomology only under the local cancellation hypotheses stated in Chapter 9.

No claim at $u\mid\ell$ follows from nearby cycles with $\ell$-adic coefficients. No wild type is identified from a tame chart alone. No integral direct summand follows from a rational Hecke projector. No rank-two surface representation is obtained by selecting two Hodge lines. These are theorem boundaries, not omissions to be filled by a change of notation.

## 2. The rank-two Weil--Deligne dictionary

Before comparing geometry and automorphic data, we need a recognition theorem for the possible rank-two parameters. The point is to know exactly which pieces of evidence determine the pair $(r,N)$.

### 2.1 From quasi-unipotent inertia to a pair

Let $V$ be a finite-dimensional $L_\lambda$-representation of $G_K$, with $\ell\ne p$. On an open subgroup $J\subset I_K$, inertia is unipotent. Choose the tame coordinate

$$
t_\ell:I_K\longrightarrow\mathbf Z_\ell(1)
$$

with

$$
t_\ell(w\sigma w^{-1})=|w|t_\ell(\sigma).
\tag{2.1}
$$

There is a unique nilpotent $N$ such that

$$
\rho(\sigma)=\exp(t_\ell(\sigma)N)
\qquad(\sigma\in J).
\tag{2.2}
$$

Removing this exponential by the crossed-homomorphism construction gives a representation $r$ of $W_K$ with finite inertial image and

$$
r(w)Nr(w)^{-1}=|w|N.
\tag{2.3}
$$

The isomorphism class is independent of the auxiliary extension of the tame coordinate. Scaling the coordinate rescales $N$ by a nonzero scalar, so its vanishing, rank, Jordan lengths, conductor, and local factors are unchanged.

For dimension two, $N^2=0$. Thus $N$ has rank zero or one. This elementary dichotomy is the reason semistable curve geometry leads exactly to unramified or special local parameters.

### 2.2 Frobenius semisimplification

The Weil representation $r$ need not be semisimple in the Frobenius direction. Write

$$
r(\Phi)=su=us
$$

for its multiplicative Jordan decomposition. The unipotent part $u$ commutes with the finite inertial image and with $N$. Define

$$
r^{\mathrm{F\!-\!ss}}(w)=r(w)u^{-\nu(w)}.
\tag{2.4}
$$

Then $r^{\mathrm{F\!-\!ss}}$ agrees with $r$ on inertia, sends $\Phi$ to $s$, and leaves $N$ unchanged. The construction is independent of the Frobenius lift up to isomorphism.

This operation is deliberately narrower than ordinary semisimplification. It retains finite inertia and nonzero monodromy. In particular, a special parameter remains indecomposable as a Weil--Deligne object.

### 2.3 Unramified and special parameters

An **unramified rank-two parameter** has $N=0$ and $r|_{I_K}=1$. It is determined, after Frobenius semisimplification, by

$$
\det(X-r(\Phi))=X^2-aX+b.
\tag{2.5}
$$

For $\beta\in\overline L^\times$, define the **special parameter** $\operatorname{St}(\beta)$ on a basis $e_0,e_1$ by

$$
Ne_1=e_0,\qquad Ne_0=0,
\tag{2.6}
$$

$$
r(i)=1\quad(i\in I_K),
\qquad
r(\Phi)e_0=\beta e_0,
\qquad
r(\Phi)e_1=q\beta e_1.
\tag{2.7}
$$

Equation (1.8) is immediate. This is the centered special block of the Weil--Deligne theory, rewritten so that no choice of $q^{1/2}$ is needed. Its determinant and Euler polynomial are

$$
\det r(\Phi)=q\beta^2,
\qquad
P(T)=1-\beta T.
\tag{2.8}
$$

**Proposition 2.1 (rank-two special recognition).** Let $(r,N)$ be a two-dimensional Frobenius-semisimple parameter with trivial finite inertia and $N\ne0$. If $\beta$ is the eigenvalue of $r(\Phi)$ on $\ker N$, then

$$
(r,N)\simeq\operatorname{St}(\beta).
\tag{2.9}
$$

**Proof.** Choose $e_0$ spanning $\ker N$ and choose $e_1$ with $Ne_1=e_0$. Since $N$ commutes with inertia and inertia is trivial, only Frobenius remains. Write $r(\Phi)e_0=\beta e_0$. From $r(\Phi)N=q^{-1}Nr(\Phi)$ we get

$$
N(r(\Phi)e_1)=q\,r(\Phi)Ne_1=q\beta e_0.
$$

Hence $r(\Phi)e_1=q\beta e_1+ce_0$. Frobenius semisimplicity and the distinct eigenvalues $\beta$ and $q\beta$ allow $e_1$ to be replaced by $e_1+c((q-1)\beta)^{-1}e_0$, killing the off-diagonal term. This gives (2.7). $\square$

Thus a special parameter is determined by nonzero monodromy and Frobenius on its one-dimensional kernel. Its determinant forces $\beta^2=b/q$.

Finite descent can coexist with special monodromy. Let $\xi:I_K\to\overline L^\times$ be a finite character invariant under Frobenius conjugation, and let $\delta\ne0$. Define $\operatorname{St}(\xi,\delta)$ by

$$
r(i)=\xi(i)I,
\qquad
r(\Phi)e_0=\delta e_0,
\qquad
r(\Phi)e_1=q\delta e_1,
\tag{2.10}
$$

with $N$ as in (2.6). The Frobenius-invariance of $\xi$ is precisely what makes these formulas respect conjugation in $W_K$. An unramified extension of $\xi$ may be absorbed into $\delta$, so the notation records only the finite inertial character and the actual Frobenius eigenvalue on $\ker N$.

**Proposition 2.2 (special recognition with finite descent).** Let $(r,N)$ be a two-dimensional Frobenius-semisimple parameter with $N\ne0$. Then the finite inertia representation is scalar, say $r(i)=\xi(i)I$, and

$$
(r,N)\simeq\operatorname{St}(\xi,\delta),
\tag{2.11}
$$

where $\delta$ is Frobenius on $\ker N$.

**Proof.** The finite inertial image commutes with $N$. In a basis with $Ne_1=e_0$, the centralizer of $N$ consists of matrices

$$
\begin{pmatrix}a&b\\0&a\end{pmatrix}.
$$

Every element of a finite characteristic-zero matrix group is semisimple. Such a matrix is semisimple only when $b=0$, so inertia acts through a scalar character $\xi$. Frobenius conjugation preserves that character. The argument of Proposition 2.1 then puts Frobenius into the displayed diagonal form. $\square$

### 2.4 Finite and dihedral parameters

A **finite-type parameter** is a pair $(r,0)$ with finite inertial image. It may still have infinite total image because Frobenius eigenvalues need not be roots of unity. The inertial type is $r|_{I_K}$; it forgets unramified twists and therefore does not determine $r$ by itself.

Let $L/K$ be quadratic and let $\theta:W_L\to\overline L^\times$ be a character. The induced representation

$$
D(L/K,\theta)=\operatorname{Ind}_{W_L}^{W_K}\theta
\tag{2.12}
$$

has $N=0$ and is irreducible precisely when $\theta\ne\theta^\sigma$, where $\sigma$ is the nontrivial $K$-automorphism. We call it **dihedral** in that case. It is tame if $P_K$ acts trivially, equivalently if the inducing data are tame after accounting for the quadratic extension.

If $L/K$ is unramified, then $I_L=I_K$ and

$$
D(L/K,\theta)|_{I_K}simeq
\theta|_{I_K}\oplus\theta^\sigma|_{I_K}.
\tag{2.13}
$$

If $L/K$ is ramified, then $I_L$ has index two in $I_K$ and the restriction is induced from $I_L$. These two cases must not be conflated: the same dimension and conductor can conceal different inertial structures.

### 2.5 Twists, duals, and determinants

For a character $\mu$ of $W_K$,

$$
(r,N)\otimes\mu=(r\otimes\mu,N\otimes1).
\tag{2.14}
$$

An unramified twist changes Frobenius eigenvalues but neither type nor conductor. A Tate twist by $n$ is the unramified twist by $|\cdot|^n$:

$$
\operatorname{WD}(V(n))=\operatorname{WD}(V)\otimes|\cdot|^n.
\tag{2.15}
$$

Thus geometric Frobenius eigenvalues are multiplied by $q^{-n}$. The local Euler factor satisfies

$$
L(s,V(n))=L(s+n,V).
\tag{2.16}
$$

The dual is $(r^\vee,-{}^tN)$. The minus sign comes from differentiating the invariant evaluation pairing. The determinant has zero monodromy because $\operatorname{tr}N=0$. These formulas are sensitive checks that the cohomological representation has not accidentally been replaced by a covariant Tate module or by its dual.

## 3. What a compatibility theorem must compare

Naming both sides is not enough. We need a finite set of data which provably determines each parameter, and we need geometric correspondences that transport those data to the packet multiplicity space.

### 3.1 The automorphic local datum

In the elementary weight-two range, the automorphic local datum consists of one of the following packages.

1. **Spherical package:** trivial inertia, $N=0$, and the polynomial

   $$
   X^2-t_v(\Pi)X+q_vs_v(\Pi).
   \tag{3.1}
   $$

2. **Special package:** trivial finite inertia, a nonzero $N$, and a scalar $\beta_v$ on the local new line satisfying

   $$
   \beta_v^2=s_v(\Pi).
   \tag{3.2}
   $$

   The associated parameter is $\operatorname{St}(\beta_v)$.

   More generally, a ramified special package includes a Frobenius-stable finite character $\xi_v$ of inertia and the kernel eigenvalue $\delta_v$; its parameter is $\operatorname{St}(\xi_v,\delta_v)$.

3. **Finite-type package:** a finite representation $\tau_v$ of inertia extending to $W_K$, together with Frobenius on each orbit of its isotypic pieces and the determinant $q_vs_v(\Pi)$.

4. **Tame dihedral package:** a quadratic extension $L/K$, a tame character $\theta_v$ with $\theta_v\ne\theta_v^\sigma$, and the induced parameter (2.12).

The scalars and characters are part of the packet data over its coefficient field. An embedding of that field into $L_\lambda$ transports the datum; it does not alter its algebraic identities.

### 3.2 The geometric local datum

The geometric datum is extracted from a model. At a good place it consists of smooth proper specialization and the extended Hecke correspondence relation. At a semistable place it consists of:

$$
\left(
r|_{I_K},\ N,\
r(\Phi)\text{ on }(\ker N)^{I_K},\
\operatorname{Sw}(r)
\right).
\tag{3.3}
$$

For a surface one also records $\operatorname{rank}N^2$ on the full middle cohomology. The stratum complex supplies these data in the following order: finite descent acts on components and incidence orientations; restriction and Gysin maps determine the surviving subquotients; monodromy joins matching subquotients; Frobenius acts on their cohomology.

Only after this construction may a Hecke projector be applied. Counting nodes, double curves, or triple points before taking the incidence cohomology can give a wrong rank for $N$.

### 3.3 A rigidity criterion

The following elementary lemma will close the finite-type comparisons.

**Lemma 3.1 (finite-inertia rigidity).** Let $r_1,r_2$ be Frobenius-semisimple representations of $W_K$ over an algebraically closed characteristic-zero field. Suppose:

- $r_1|_{I_K}\simeq r_2|_{I_K}=\tau$;
- after choosing such an identification, the return maps induced by the appropriate power of Frobenius are conjugate on the multiplicity space of one representative of every Frobenius orbit of irreducible $I_K$-types.

Then $r_1\simeq r_2$.

**Proof.** Decompose $\tau$ into isotypic components. Frobenius permutes them because it normalizes inertia. On one orbit, choose a component $U$. A representation of the semidirect product generated by inertia and Frobenius is determined by the inertial action on the orbit and by the return map $\Phi^m:U\to U$, where $m$ is the orbit length. By Schur's lemma, on each irreducible multiplicity-one component this return map is a scalar; with multiplicity, it is a semisimple endomorphism of the multiplicity space. The stated agreement identifies these return maps. Inducing around every orbit gives an intertwiner, and their direct sum is an isomorphism. $\square$

For an irreducible dihedral representation the orbit is determined by $\theta$ and $\theta^\sigma$; one return scalar, equivalently the specified inducing character on a Frobenius lift in $W_L$, completes the parameter. In the unramified case, inertial type alone leaves an unramified-twist ambiguity.

### 3.4 Hecke isolation and exactness

Let $H$ be a cohomology group or the total cohomology of a stratum complex, and let a finite semisimple Hecke algebra $A$ commute with $W_K$ and $N$. For a simple module $P$ define

$$
W=\operatorname{Hom}_A(P,H).
\tag{3.4}
$$

Evaluation gives $P\otimes W\simeq H[P]$. Because the Hom functor for a semisimple algebra is exact, kernels, images, and cohomology of the restriction--Gysin complex pass through (3.4). Moreover

$$
(N_Wf)(p)=N_H(f(p))
\tag{3.5}
$$

defines the monodromy on $W$ when Galois acts trivially on $P$. Thus

$$
\ker N_W=\operatorname{Hom}_A(P,\ker N_H),
\tag{3.6}
$$

and similarly for images and invariant subspaces.

This argument is rational. For an integral Hecke order, Hom need not be exact, and a rational projector need not preserve the ambient lattice. Chapter 11 keeps that distinction visible.

## 4. Good primes

Good-prime compatibility is the cleanest case, but even here the phrase “good prime” abbreviates several independent integral conditions.

### 4.1 The complete good-place ledger

Let $u\mid v$ and let $p$ be the residue characteristic. We assume:

- the acting PEL algebra and its center are unramified at $p$;
- the relevant order is maximal and the involution is unramified;
- the alternating lattice is self-dual and the polarization degree is a unit;
- the local group scheme is reductive and the $p$-level is hyperspecial;
- the actual determinant local model is the required smooth projective line, or product of two such lines;
- the selected component union descends and is stable under the Hecke correspondences used;
- the prime-to-$p$ level is fine, or the argument is made rationally through a fine cover;
- the Shimura datum is in the compact anisotropic range, so the model is proper;
- $u\nmid\ell$.

Under exactly these hypotheses, the good integral-model theorem supplies a smooth projective model $\mathscr X/\mathcal O_K$, all prime-to-$p$ Hecke correspondences extend, and the chosen coefficient system extends lisse.

### 4.2 Smooth proper specialization

**Proposition 4.1.** Under the good-place ledger, inertia acts trivially on the packet representation and $N=0$.

**Proof.** Smooth proper base change gives a canonical, Hecke-equivariant isomorphism

$$
H^m(\mathscr X_{\bar k},L_\lambda)
\xrightarrow{\sim}
H^m(\mathscr X_{\bar K},L_\lambda).
\tag{4.1}
$$

The left side is acted on through the residue-field Galois group, so inertia is trivial on the right side. The packet projector and multiplicity Hom commute with (4.1), hence inertia is trivial after extraction. In the Weil--Deligne dictionary, a representation with trivial inertia has trivial finite part and $N=0$. $\square$

The proof uses smoothness and properness. Proper base change without smoothness computes nearby cycles but does not make them constant.

### 4.3 The Frobenius polynomial

On untwisted curve $H^1$, the extended special-fiber correspondence gives

$$
\Phi_u^2-T_v\Phi_u+q_vS_v=0.
\tag{4.2}
$$

On the multiplicity space this becomes

$$
\Phi_u^2-t_v(\Pi)\Phi_u+q_vs_v(\Pi)=0.
\tag{4.3}
$$

The determinant theorem from the alternating cohomological pairing gives

$$
\det(\Phi_u)=q_us_v(\Pi).
\tag{4.4}
$$

When $q_u=q_v$, (4.3) and (4.4) imply

$$
\det(X-\rho_{\Pi,\lambda}(\Phi_u))
=X^2-t_v(\Pi)X+q_vs_v(\Pi).
\tag{4.5}
$$

Indeed, subtracting (4.3) from Cayley--Hamilton yields $(\operatorname{Tr}\Phi_u-t_v)\Phi_u=0$; Frobenius is invertible, so its trace is $t_v$. This proof includes scalar Frobenius.

If the residue extension has degree $f$, the correct statement uses the actual place $u$: geometric Frobenius acts as the $f$th power of the corresponding operator and $q_u=q_v^f$. One must not retain $q_v$ while replacing $\Phi_v$ by $\Phi_u$.

### 4.4 Unramified local--global compatibility

**Theorem 4.2.** Under the good-place ledger and $q_u=q_v$,

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
$$

is the unramified parameter with Frobenius polynomial (4.5). Hence it equals the spherical parameter $D(\Pi_v)$.

**Proof.** Proposition 4.1 gives trivial inertia and $N=0$. Frobenius semisimplification preserves its characteristic polynomial. Equation (4.5) determines a semisimple unramified representation of $W_K$, since $W_K/I_K$ is generated by $\Phi$. This is precisely the spherical package of Section 3.1. $\square$

The corresponding arithmetic-Frobenius polynomial is obtained by reciprocating the two roots. It is not (4.5) with $q$ merely replaced by $q^{-1}$; the middle coefficient is divided by the determinant as well.

## 5. Semistable curves and their packet parts

At a bad rank-two parahoric place, the integral model is no longer smooth. Its nodes create local vanishing cycles, but global monodromy is controlled by cycles in the dual graph rather than by the raw number of nodes.

### 5.1 The weight complex of a nodal fiber

Let $\mathscr C/\mathcal O_K$ be a proper strictly semistable curve with geometric special fiber

$$
Y=\bigcup_{a\in A}Y_a
$$

and dual graph $\Gamma$. The weight spectral sequence in degree one has three graded pieces

$$
H^1(\Gamma,L_\lambda),
\qquad
\bigoplus_a H^1(Y_a,L_\lambda),
\qquad
H_1(\Gamma,L_\lambda)(-1).
\tag{5.1}
$$

It degenerates at the second page by dimension. Monodromy is zero on the middle piece and identifies the two outer pieces through the graph pairing. Consequently

$$
N^2=0,
\qquad
\operatorname{rank}N=b_1(\Gamma).
\tag{5.2}
$$

The invariant-cycle map identifies

$$
H^1(Y,L_\lambda)\simeq
H^1(C_{\bar K},L_\lambda)^{I_K}=\ker N
\tag{5.3}
$$

at split strict level.

To see why nodes cannot simply be counted, take two components meeting at one point. The graph is an interval, so $b_1(\Gamma)=0$ and $N=0$. Two components meeting at $m$ points give $b_1=m-1$. The global restriction map removes one linear combination of the $m$ local vanishing generators.

### 5.2 Restricting monodromy to a multiplicity space

Prime-to-$p$ Hecke correspondences extend over the parahoric model and act on vertices, edges, component cohomology, restriction, and Gysin. Hence they commute with $N$. Let $P_\Pi$ be the finite Hecke module and let

$$
W_\Pi=\operatorname{Hom}_A(P_\Pi,H^1(C_{\bar K},L_\lambda)).
\tag{5.4}
$$

Then (3.5) defines $N_\Pi$ and exactness gives

$$
\operatorname{rank}N_\Pi
=\dim\operatorname{Hom}_A
\left(P_\Pi,\operatorname{im}N\right).
\tag{5.5}
$$

Since $\dim W_\Pi=2$, the rank is zero or one. Formula (5.5), rather than the total Betti number of $\Gamma$, decides which branch the packet occupies.

**Proposition 5.1.** At split strict semistable level, the packet restriction is unramified if $N_\Pi=0$ and has special Weil--Deligne form if $N_\Pi\ne0$.

**Proof.** Strict semistability makes wild inertia trivial and all inertia unipotent. Thus the finite inertial representation $r|_I$ is trivial. If $N_\Pi=0$, the exponential formula makes inertia trivial. If $N_\Pi\ne0$, it has rank one and Proposition 2.1 applies. $\square$

### 5.3 The zero-monodromy branch

The implication $N_\Pi=0\Rightarrow$ unramified is a statement about the representation, not about smoothness of the model. A compact-type singular curve can have a reducible special fiber and $N=0$ on all of $H^1$. More commonly, the full curve has graph cycles but a selected packet projector kills their Hecke-isotypic part.

At split strict level, zero monodromy means

$$
\operatorname{WD}_u(W_\Pi)=(r,0),
\qquad r|_I=1.
\tag{5.6}
$$

The unramified parameter is then determined by Frobenius on the packet part of $H^1(Y)$. If the bad local packet is nevertheless spherical at the chosen level, the same Hecke--Frobenius calculation as at a good place identifies its polynomial. If the local model is singular because of an auxiliary level structure, the singularity alone does not force the automorphic packet to be Steinberg.

### 5.4 The nonzero-monodromy branch

Assume $N_\Pi\ne0$. Put

$$
L_\Pi^{\mathrm{inv}}=(\ker N_\Pi)^{I_K}.
\tag{5.7}
$$

At split strict level this is a line. Frobenius preserves it, so let $\beta_u$ be its eigenvalue. Proposition 2.1 gives

$$
\operatorname{WD}_u(W_\Pi)^{\mathrm{F\!-\!ss}}
\simeq\operatorname{St}(\beta_u).
\tag{5.8}
$$

The global determinant supplies a valuable consistency check:

$$
q_u\beta_u^2
=\det r(\Phi_u)
=q_us_v(\Pi),
$$

so

$$
\beta_u^2=s_v(\Pi).
\tag{5.9}
$$

Thus the only remaining comparison is the sign, or more generally the finite central scalar, on the invariant line. It is measured by the bad Hecke correspondence, not by the rank of $N$.

## 6. Steinberg compatibility

The word “Steinberg” summarizes a precise pair: one nonzero nilpotent arrow and one Frobenius scalar on its kernel. This chapter identifies both pieces geometrically.

### 6.1 The special parameter without square roots

The parameter $\operatorname{St}(\beta)$ from (2.6)--(2.7) has one invariant line and one monodromy partner. Its semisimple Frobenius eigenvalues are

$$
\beta,\qquad q\beta.
\tag{6.1}
$$

They have weights $0$ and $2$ when $\beta$ has finite order, while their nonsplit monodromy extension is pure of weight one in the monodromy sense. This is not a contradiction: purity for a semistable representation is read on monodromy-graded pieces with shifted weights, not by demanding equal absolute values for the two eigenvalues of $r(\Phi)$.

The Euler polynomial and conductor are

$$
P(T)=1-\beta T,
\qquad a(\operatorname{St}(\beta))=1.
\tag{6.2}
$$

The determinant is $q\beta^2$. Hence a weight-two packet with central scalar $s_v$ can have special parameter only when $\beta^2=s_v$, exactly as (5.9) requires.

### 6.2 The graph line and the bad Hecke operator

For an Iwahori curve model, an object is an isogeny chain $A_0\to A_1$ of the prescribed finite locally free type. Forgetting $A_1$, and instead retaining the quotient endpoint with its transported structure, give the two degeneracy morphisms to the adjacent maximal-level moduli problem. They are defined over the integral base because the universal isogeny is part of the parahoric moduli object. Passing to the common level and composing pullback along the first route with trace along the second gives the normalized bad operator $U_v$.

On the generic fiber this is the usual local double-coset operator. The automorphic decomposition therefore makes it act on the one-dimensional local new line of $P_\Pi$ by its new-line scalar $\beta_v$. On the special fiber the two degeneracy morphisms carry branches to branches and act on the graph cochain complex. Since they are actual morphisms of the integral moduli problems, no closure with an unknown vertical component has been introduced. Functoriality of nearby cycles makes the generic and special-fiber actions the same endomorphism of the weight complex.

**Proposition 6.1 (new-line scalar on the invariant graph line).** Assume the rank-two Iwahori local model is the verified flat incidence model, the two integral degeneracy morphisms above preserve the selected component union, and pull--push is normalized by the same double-coset measure as the automorphic Hecke action. If the packet graph multiplicity is one, then

$$
\Phi_u\mid L_\Pi^{\mathrm{inv}}=\beta_v.
\tag{6.3}
$$

**Proof.** Nearby cycles identify generic cohomology with the hypercohomology of the special-fiber complex, equivariantly for both degeneracy morphisms. The packet projector and multiplicity Hom are exact, so the equality persists on the packet graph line. On generic cohomology, the automorphic decomposition identifies the pull--push correspondence with $U_v$ and hence with the scalar $\beta_v$ on the local new line. On the graph side, the Frobenius route through the two adjacent components is the same normalized correspondence. The two actions therefore agree on the common one-dimensional multiplicity space. $\square$

The proposition has three geometric hypotheses which must remain visible:

- the bad correspondence extends over the parahoric moduli scheme, not merely over the generic fiber;
- its closure has no unrecorded vertical component, or all such components have been included in the restriction--Gysin action;
- the normalization of pull--push agrees with the normalization used to define $\beta_v$.

The equality is an operator identity on a one-dimensional multiplicity space. It is stronger than equality of conductors and is precisely the missing scalar in (5.8).

### 6.3 The Steinberg theorem

**Theorem 6.2 (Steinberg compatibility).** Let $u\nmid\ell$ be a split strict semistable rank-two Iwahori place for the selected Shimura curve. Assume the integral degeneracy morphisms, component stability, and normalization hypotheses of Proposition 6.1, and assume the packet graph multiplicity is one. Then

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq\operatorname{St}(\beta_v).
\tag{6.4}
$$

In particular,

$$
N\ne0,\quad \operatorname{rank}N=1,\quad
a_u(\rho_{\Pi,\lambda})=1,
\tag{6.5}
$$

and

$$
L_u(s,\rho_{\Pi,\lambda})
=(1-\beta_vq_u^{-s})^{-1}.
\tag{6.6}
$$

**Proof.** The graph multiplicity hypothesis and (5.5) give $\operatorname{rank}N=1$. Split strict semistability makes finite inertia trivial. Proposition 2.1 identifies the parameter as $\operatorname{St}(\beta_u)$, where $\beta_u$ is geometric Frobenius on the invariant line. Equation (6.3) gives $\beta_u=\beta_v$. Formula (6.2) gives the conductor and Euler factor. $\square$

This proof shows why “conductor one” is not by itself a Steinberg theorem. A nontrivial tame character with $N=0$ also has conductor one.

### 6.4 Split and nonsplit multiplicative signs

In the basic trivial-central-character case, (5.9) gives $\beta=\pm1$. The sign $+1$ is the split multiplicative parameter, and $-1$ is its unramified quadratic twist. The nilpotent operator is nonzero in both cases; the distinction lies in residue Frobenius on the graph orientation line.

Thus nonsplit multiplicative reduction does not introduce ramified inertia. Its torus splits over an unramified quadratic extension, so inertia remains unipotent with trivial finite part, while Frobenius reverses the graph orientation. This is the model example showing that monodromy and Frobenius must be reported separately.

## 7. Finite descent and inertial type

Strict semistability may appear only after a finite extension. The extension simplifies geometry, but its descent action contains genuine local type information and must be restored before compatibility is asserted over the original field.

### 7.1 Restoring the descent action

Let $K'/K$ be a finite Galois extension over which a strict semistable model exists. The geometric special fiber over $K'$ carries an action of the finite descent group. This action can:

- permute components and double intersections;
- reverse the orientation of graph edges or surface simplices;
- act on component cohomology;
- act on a coefficient system;
- contribute a finite wild image.

Form the stratum complex equivariantly before taking invariants. The resulting local representation over $K$ separates as

$$
\text{finite inertia }r|_{I_K}
\quad\text{and}\quad
\text{nilpotent monodromy }N.
\tag{7.1}
$$

The two commute on inertia, but Frobenius scales $N$ by $q^{-1}$. Passing first to a quotient graph can erase stabilizers and orientation characters and therefore produce the wrong type.

### 7.2 Type projectors on the stratum complex

Suppose a finite quotient $J$ of inertia acts on the semistable descent complex and $L$ splits $J$. For an irreducible character $\vartheta$ of $J$, the idempotent

$$
e_\vartheta=
\frac{\dim\vartheta}{|J|}
\sum_{g\in J}\operatorname{Tr}(\vartheta(g^{-1}))g
\tag{7.2}
$$

cuts out its isotypic part over $L$. Because the $J$-action commutes with restriction, Gysin, and prime-to-$p$ Hecke correspondences, the projector acts on the entire complex and its cohomology.

Integrally, the denominator $|J|$ matters. Rationally, however, (7.2) proves that the finite inertia on a packet part is exactly the inertia representation selected from the descent action. If an automorphic type idempotent is identified with the same $e_\vartheta$ under the model-level correspondence, the two inertial types agree.

### 7.3 Finite-type compatibility

**Theorem 7.1 (finite-type compatibility).** Let $u\nmid\ell$. Assume a finite semistable extension and an equivariant strict semistable model have been fixed. Let the packet projector and a local type projector extend to the full stratum complex. Suppose:

1. the geometric type projector cuts out the prescribed automorphic inertial type $\tau_v$;
2. the restriction--Gysin monodromy vanishes on the selected packet part;
3. the normalized Frobenius return maps on every orbit of inertia-isotypic pieces equal those in the automorphic finite-type package.

Then

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq D(\Pi_v),
\tag{7.3}
$$

with $N=0$ and inertia type $\tau_v$.

**Proof.** The first hypothesis identifies the restrictions of the two Weil representations to inertia. The second gives $N=0$. The third identifies the Frobenius return maps. Lemma 3.1 then gives an isomorphism of Frobenius-semisimple Weil representations. $\square$

If monodromy does not vanish, rank two makes the remaining case equally rigid.

**Corollary 7.2 (finite descent with special monodromy).** In the setting of Theorem 7.1, replace the vanishing-monodromy hypothesis by $N\ne0$. Then finite inertia acts through a Frobenius-stable scalar character $\xi_u$. If the type projector identifies it with the automorphic character $\xi_v$ and the normalized Frobenius action on $\ker N$ is $\delta_v$, then

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq\operatorname{St}(\xi_v,\delta_v).
\tag{7.4}
$$

**Proof.** Proposition 2.2 gives the scalar character and the special form. The type projector identifies the character, while the kernel eigenvalue identifies the remaining Frobenius scalar. $\square$

Thus type alone never detects $N$, but type, monodromy, and kernel Frobenius determine the ramified special parameter completely.

### 7.4 Wild and tame boundaries

Strict semistability over $K'$ kills wild inertia on the unipotent factor, but wild inertia over $K$ can survive in finite descent. Its Swan conductor is computed from the upper breaks of that finite action. A tame model does not determine an unspecified wild descent representation.

The finite-type theorem therefore has two different uses. For a tame type, the verified action of $I_K/P_K$ on strata and orientations suffices. For a wild type, the entire finite wild action and its ramification filtration must be part of the descent datum. Without that information one may still compute $N$ after semistable base change, but not the original conductor or type over $K$.

## 8. Tame dihedral types

Tame dihedral parameters are the finite nonabelian rank-two types that occur most naturally in the present geometric range. Their recognition is an induction calculation, not a conductor calculation.

### 8.1 Quadratic induction

Let $L/K$ be quadratic and choose $j\in W_K\setminus W_L$. On the induced space with coset basis $e,je$, an element $w\in W_L$ acts diagonally by

$$
r(w)=
\begin{pmatrix}
\theta(w)&0\\
0&\theta^\sigma(w)
\end{pmatrix}.
\tag{8.1}
$$

The element $j$ exchanges the two lines, with a return scalar determined by $\theta(j^2)$. Consequently the representation is irreducible exactly when the two characters differ. Its determinant is the product character on $W_L$, extended with the sign of the two-coset permutation.

This matrix description proves that the inducing character, including its value on a Frobenius return element, determines the entire parameter. It also displays why the unordered pair of inertial characters may not suffice.

### 8.2 The unramified quadratic case

If $L/K$ is unramified quadratic, then $I_L=I_K$ and geometric Frobenius $\Phi$ exchanges the two inertial characters. Its square is geometric Frobenius over $L$. In a suitable basis,

$$
r(\Phi)=
\begin{pmatrix}
0&\theta(\Phi_L)\\
1&0
\end{pmatrix},
\tag{8.2}
$$

up to exchanging the basis vectors. Hence

$$
\operatorname{Tr}r(\Phi)=0,
\qquad
\det r(\Phi)=-\theta(\Phi_L).
\tag{8.3}
$$

If the inertia characters are nontrivial, then $V^{I_K}=0$ and the Euler factor is $1$. The tame conductor is the codimension of invariants, usually $2$. If both inertia characters are trivial, the induced representation is reducible and belongs to the unramified principal range rather than the irreducible dihedral range.

### 8.3 The ramified quadratic case

If $L/K$ is ramified quadratic, $I_L$ has index two in $I_K$. The inertial representation is

$$
\operatorname{Ind}_{I_L}^{I_K}\theta|_{I_L}.
\tag{8.4}
$$

For a tame ramified quadratic extension, this is possible only when the ramification degree is prime to $p$; in residue characteristic two a ramified quadratic extension is not tame. The unramified quadratic extension remains available in every residue characteristic.

Geometric Frobenius can be chosen in $W_L$ because the residue degree is one. Its action on the two inducing lines has eigenvalues $\theta(\Phi_L)$ and $\theta^\sigma(\Phi_L)$, subject to the conjugation relation with inertia. Thus its trace and determinant need not have the form (8.3). This is a second reason the two quadratic cases require separate bookkeeping.

### 8.4 The tame dihedral comparison theorem

**Theorem 8.1.** Let $u\nmid\ell$, and assume the finite descent complex of the selected Shimura model contains a quadratic cover $L/K$ and a tame character summand $\theta_v$ such that:

- the packet and type projectors cut out the induced descent module $\operatorname{Ind}_{W_L}^{W_K}\theta_v$;
- $\theta_v\ne\theta_v^\sigma$;
- monodromy vanishes on this packet summand;
- the geometric Frobenius return scalar equals $\theta_v$ on the chosen lift in $W_L$.

Then

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})^{\mathrm{F\!-\!ss}}
\simeq
\operatorname{Ind}_{W_L}^{W_K}\theta_v.
\tag{8.5}
$$

**Proof.** The equivariant descent module gives the restriction to inertia, in the form (2.13) or (8.4). Vanishing monodromy gives $N=0$. The Frobenius return scalar supplies the remaining datum in the induced matrices. Lemma 3.1, or directly (8.1), identifies the Weil representations. $\square$

The theorem is unchanged after extending the coefficient field enough to contain the values of $\theta_v$. Its conductor and epsilon factor then agree automatically because they are invariants of the same Weil--Deligne representation.

## 9. Unitary surfaces and cancellation

The surface geometry is indispensable in the two-active-place construction, but it has more cohomology than the desired rank-two representation. Local--global compatibility on a surface must therefore be stated in two stages: first for the honest four-dimensional block, then for a rank-two factor under a genuine cancellation datum.

### 9.1 The honest surface monodromy

For a proper strictly semistable surface, the middle-cohomology weight complex contains component surfaces, double curves, and triple points. Its monodromy satisfies

$$
N^3=0.
\tag{9.1}
$$

If

$$
r_1=\operatorname{rank}N,
\qquad r_2=\operatorname{rank}N^2,
$$

then the numbers of Jordan blocks of lengths three, two, and one are

$$
n_3=r_2,
\qquad n_2=r_1-2r_2,
\qquad n_1=\dim V-2r_1+r_2.
\tag{9.2}
$$

The extreme term $r_2$ is controlled by the second homology of the dual complex. The length-two primitive term is controlled by the quotient of double-curve $H^1$ left after restriction and Gysin. Neither is determined by counting triple points or summing genera.

The honest surface packet $V_{\Pi,\lambda}$ inherits this $N$, the finite descent action, and Frobenius. It remains generally four-dimensional. Formula (9.2) is meaningful on that full block and must not be forced into a rank-two classification.

### 9.2 Local cancellation data

A **local cancellation datum** at $u$ consists of:

1. a two-dimensional $B_\Pi$-module $R_\Pi$ for a descended split algebra $B_\Pi\simeq M_2(L_\lambda)$;
2. compatible $W_K$-actions on $B_\Pi$, $R_\Pi$, and $V_{\Pi,\lambda}$, with Galois normalizing the algebra action;
3. a $W_K$-equivariant evaluation isomorphism

   $$
   R_\Pi\otimes W_\Pi^{\mathrm{surf}}
   \xrightarrow{\sim}V_{\Pi,\lambda};
   \tag{9.3}
   $$

4. an identification of the surface nearby-cycle stratum complex with the tensor product of the cancellation complex and the desired packet complex, compatible with restriction, Gysin, and Frobenius;
5. the pairing factorization which leaves on $W_\Pi^{\mathrm{surf}}$ the target $L_\lambda(-1)\otimes\eta_\Pi$.

The fourth condition is the local addition to the global cancellation datum. A tensor factorization on generic cohomology alone does not say how monodromy divides between its two factors.

### 9.3 The logarithm on a Hom factor

Define

$$
W=\operatorname{Hom}_{B_\Pi}(R_\Pi,V_\Pi)
$$

with

$$
(g\cdot f)(x)=g\bigl(f(g^{-1}x)\bigr).
\tag{9.4}
$$

Let $N_R$ and $N_V$ be the logarithms of inertia on $R$ and $V$. Differentiating (9.4) gives

$$
(N_Wf)(x)=N_V(f(x))-f(N_Rx).
\tag{9.5}
$$

**Proposition 9.1.** Under the local cancellation datum,

$$
N_V=N_R\otimes1+1\otimes N_W
\tag{9.6}
$$

under (9.3), and $(r_W,N_W)$ satisfies the Weil--Deligne relation.

**Proof.** On a sufficiently small inertia subgroup, (9.3) identifies the action with the tensor product of the two actions. The logarithm of a tensor product of commuting unipotent one-parameter groups is the sum of their logarithms, proving (9.6). Solving (9.6) for the Hom factor gives (9.5). Conjugating (9.5) by a Weil element and using the scaling relation for $N_V$ and $N_R$ yields the same relation for $N_W$. $\square$

Although $N_V^3$ may be nonzero on a four-dimensional surface block, dimensional reasoning gives $N_W^2=0$ on the rank-two factor. One cannot infer $N_W$ from $N_V$ without knowing $N_R$ and the tensor factorization.

### 9.4 Surface local--global compatibility

**Theorem 9.2.** Assume a surface cancellation datum globally and the local cancellation datum of Section 9.2 at $u\nmid\ell$. Suppose the desired packet complex satisfies one of the good, special, finite-type, or tame dihedral comparison hypotheses already stated. Then the rank-two surface factor satisfies the corresponding local--global compatibility theorem.

**Proof.** Proposition 9.1 identifies the Weil--Deligne pair on the Hom factor with the pair computed from the desired packet complex after removing the known cancellation pair. The pairing factorization gives determinant $\chi_\ell^{-1}\eta_\Pi$, so the determinant checks in Chapters 4 and 6 remain valid. The relevant recognition theorem then applies: Theorem 4.2 in the good case, Theorem 6.2 in the special case, Theorem 7.1 for finite type, and Theorem 8.1 for tame dihedral type. $\square$

### 9.5 Why cancellation hypotheses cannot be weakened

A four-dimensional surface block can have Hodge numbers $(1,2,1)$ and $N^3=0$. Choosing the $(2,0)$ and $(0,2)$ lines does not give a Galois-stable subspace. Taking a formal half Tate twist is impossible because integral Tate twists change weight by an even integer.

Nor does an abstract vector-space factorization $V\simeq R\otimes W$ suffice. Without descended algebra action, $W$ need not be Galois stable. Without the local tensor factorization, equation (9.6) is unavailable. Without the pairing factorization, the determinant on $W$ is undetermined. Each clause in the cancellation datum supplies one of these missing structures.

## 10. Local factors, conductors, and epsilon factors

Once the full Weil--Deligne pair is identified, its standard local invariants agree formally. It is nevertheless useful to calculate them explicitly, both for applications and as a normalization audit.

### 10.1 Euler factors

For $D=(r,N)$ define

$$
V_N^I=(\ker N)^{I_K}
$$

and

$$
P(D,T)=\det(1-r(\Phi)T\mid V_N^I),
\qquad
L(s,D)=P(D,q^{-s})^{-1}.
\tag{10.1}
$$

The operator on $V_N^I$ is independent of the Frobenius lift. The kernel of $N$ is essential: using all inertia invariants would give the wrong Euler factor for a special parameter.

For an unramified parameter with Frobenius roots $\alpha,\beta$,

$$
P(T)=(1-\alpha T)(1-\beta T).
\tag{10.2}
$$

For $\operatorname{St}(\beta)$,

$$
P(T)=1-\beta T.
\tag{10.3}
$$

For a ramified irreducible finite type with no inertia invariants, $P(T)=1$. These three degrees, two, one, and zero, offer a quick test that finite inertia and monodromy have not been confused.

### 10.2 Artin, Swan, and monodromy conductors

For the finite-inertia representation $r$, let

$$
a(r)=\operatorname{codim}V^{I_K}+\operatorname{Sw}(r).
$$

The Weil--Deligne conductor is

$$
a(D)=a(r)+\dim V^{I_K}-\dim(\ker N)^{I_K},
\tag{10.4}
$$

equivalently

$$
a(D)=\operatorname{Sw}(r)+\dim V-
\dim(\ker N)^{I_K}.
\tag{10.5}
$$

At split strict semistable level, finite inertia and Swan vanish, so

$$
a(D)=\operatorname{rank}N.
\tag{10.6}
$$

After finite descent, (10.6) is generally false. The finite part can remove additional invariants or contribute positive wild breaks.

### 10.3 The basic rank-two calculations

The cases used in the main theorem are:

$$
\begin{array}{c|c|c|c}
D&\dim V_N^I&N&a(D)\\ \hline
\text{unramified rank two}&2&0&0\\
\operatorname{St}(\beta)&1&\operatorname{rank}1&1\\
\chi_{\mathrm{tame}}\oplus\mu_{\mathrm{unr}}&1&0&1\\
\text{tame irreducible dihedral, }V^I=0&0&0&2
\end{array}
\tag{10.7}
$$

Here $\chi_{\mathrm{tame}}$ is nontrivial on inertia and $\mu_{\mathrm{unr}}$ is unramified.

The third and fourth rows show why conductor one does not imply Steinberg and conductor two does not identify a dihedral type. The full inertia representation is necessary.

For a ramified special parameter $\operatorname{St}(\xi,\delta)$ with nontrivial finite inertial character $\xi$,

$$
a(\operatorname{St}(\xi,\delta))=2a(\xi).
\tag{10.8}
$$

Indeed, the underlying Weil representation is the direct sum of two unramified twists of $\xi$, so its conductor is $2a(\xi)$. Both $V^I$ and $(\ker N)^I$ vanish, so the monodromy correction in (10.4) is zero. This calculation explains why a ramified twist of a special parameter need not have conductor one.

For $D(L/K,\theta)$, the induction formula gives

$$
a_K(D(L/K,\theta))
=f(L/K)\bigl(a_L(\theta)+d(L/K)\bigr),
\tag{10.9}
$$

where $d(L/K)$ is the exponent of the different measured over $L$. In an unramified quadratic extension, $d=0$ and the conductor is transported from $\theta$. In a tame ramified quadratic extension, $d=1$ and the extension itself contributes.

### 10.4 Epsilon factors

Fix a nontrivial additive character $\psi$ and its self-dual Haar measure. The epsilon factor is

$$
\epsilon(s,D,\psi)
=\epsilon(s,r,\psi)
\det\left(-q^{-s}r(\Phi)\mid
V^{I_K}/V_N^I\right).
\tag{10.10}
$$

Thus a full isomorphism of Weil--Deligne parameters implies equality of epsilon factors for the same $\psi$ and measure. No separate sign argument is needed. Conversely, equality of conductor and epsilon factor does not imply equality of parameters.

For $\operatorname{St}(\beta)$ and an additive character of conductor zero, (10.10) is the determinant of $-q^{-s}r(\Phi)$ on the line spanned by $e_1$. Since that eigenvalue is $q\beta$,

$$
\epsilon(s,\operatorname{St}(\beta),\psi)
=-\beta\,q^{1-s}.
\tag{10.11}
$$

For an induced dihedral parameter, the induction formula includes the quadratic lambda constant. Omitting it can preserve the conductor exponent while changing the root number. Therefore local--global compatibility of parameters is the clean statement from which compatibility of every local constant follows.

## 11. Coefficients and integral structures

The rational local parameter is stable under coefficient extension. Integral lattices contain finer information, but they require separate saturation and denominator checks.

### 11.1 Extension of the coefficient field

Let $L'/L$ be a finite extension and $\lambda'\mid\lambda$. Formation of the multiplicity space, the Weil--Deligne pair, kernels of $N$, inertia invariants, and Frobenius semisimplification commute with extension to $L'_{\lambda'}$. Hence

$$
\operatorname{WD}_u(\rho_{\Pi,\lambda})
\otimes_{L_\lambda}L'_{\lambda'}
\simeq
\operatorname{WD}_u(\rho_{\Pi,\lambda'}).
\tag{11.1}
$$

This permits splitting a finite inertial representation or adjoining values of a tame character without changing conductor, monodromy rank, or the truth of compatibility. Descent back to the Hecke field can retain a Schur obstruction; the theorem therefore asserts compatibility after the same finite splitting extension used to construct the rank-two representation.

### 11.2 Saturated packet lattices

Let $\Lambda$ be the natural integral cohomology lattice modulo torsion where necessary, and let $e$ be a rational packet idempotent. The canonical lattice in its rational block is

$$
\Lambda[e]=\Lambda\cap e(\Lambda\otimes\mathbf Q_\ell).
\tag{11.2}
$$

It is saturated, Galois stable, and stable under integral Hecke correspondences. It need not be a direct summand. Projector denominators, stabilizer orders from coarse level, and discriminants of Hecke orders are independent possible obstructions.

If a type projector contains the denominator $|J|$ from (7.2) and $\ell\mid|J|$, its rational type summand need not define an integral direct summand. Rational local--global compatibility remains valid; a canonical integral type lattice does not follow.

### 11.3 Integral monodromy and its denominators

For a curve, $N^2=0$ and, after normalizing a tame generator, the integral logarithm is simply $\rho(\tau)-1$. The induced map between the outer graph lattices is the weighted graph pairing. Its finite cokernel records the monodromy discriminant and component information, not the rational conductor.

For a surface, the logarithm can contain

$$
\log(1+U)=U-\frac{U^2}{2}.
\tag{11.3}
$$

At $\ell=2$, rational $N$ is still canonical, but integral preservation requires a separate divisibility argument. Even for odd $\ell$, restriction and Gysin images can be nonsaturated. A rational cancellation factor therefore does not automatically carry a canonical integral monodromy lattice.

Ramified base change of index $e$ scales the normalized integral operator by $e$. It leaves the rational Jordan type unchanged but can change cokernels and component groups. This is why conductor stability under semistable base change does not imply stability of integral monodromy discriminants.

### 11.4 The coefficient prime

All preceding local monodromy arguments assume $u\nmid\ell$. When $u\mid\ell$, the coefficient prime equals the residue characteristic and the tame logarithm construction used here no longer controls the representation. Smooth proper cohomology still exists, but crystalline, semistable, de Rham, or finite-flat conclusions require comparison theorems with their own integral hypotheses.

In particular, neither the good polynomial at places away from $\ell$ nor the bad-prime Weil--Deligne calculation proves finite-flatness of a quotient at $\ell$. Canonical lattices and finite-flat quotients form a separate problem.

## 12. The compatibility theorem

We can now state the result in a form that separates unconditional geometric output from the extra local identifications needed in each automorphic case.

### 12.1 Complete statement

**Theorem 12.1 (local--global compatibility in the weight-two geometric range).** Let $\Pi$ be a noncharacter parallel-weight-two packet occurring in the selected compact quaternionic Shimura-curve cohomology. Let

$$
\rho_{\Pi,\lambda}:G_E\to\operatorname{GL}_2(L_\lambda)
$$

be its semisimple cohomological representation, with

$$
\det\rho_{\Pi,\lambda}=\chi_\ell^{-1}\eta_\Pi.
$$

Let $u\nmid\ell$ be a finite place of $E$, put $K=E_u$, and let $v$ be the corresponding automorphic place. Assume the selected component union and all correspondences used below descend over $K$. Then the following assertions hold.

1. **Good place.** If the complete ledger of Section 4.1 holds, then the restriction is unramified and

   $$
   \det(X-\rho_{\Pi,\lambda}(\Phi_u))
   =X^2-t_v(\Pi)X+q_us_v(\Pi)
   $$

   when the local residue fields agree. Hence compatibility holds with the spherical parameter.

2. **Split semistable curve.** If the verified parahoric model is strict semistable over $K$, then finite inertia is trivial, $N^2=0$, and the packet monodromy is the packet part of the graph restriction--Gysin map. If that part vanishes, the packet is unramified. If it is nonzero, it has rank one and the parameter is $\operatorname{St}(\beta_u)$, where $\beta_u$ is geometric Frobenius on $(\ker N)_\Pi$.

3. **Steinberg place.** Under the model-level bad-correspondence hypotheses of Theorem 6.2, $\beta_u=\beta_v$ and compatibility holds with $\operatorname{St}(\beta_v)$. Its conductor is one and its Euler factor is (6.6).

4. **Finite descent.** If strict semistability occurs over a finite Galois extension, the finite descent action on the full geometric stratum complex is the finite inertial part of the packet parameter. Under the type-projector and Frobenius-return hypotheses of Theorem 7.1, compatibility holds with the prescribed finite type when $N=0$. When $N\ne0$, Corollary 7.2 gives compatibility with the ramified special parameter $\operatorname{St}(\xi_v,\delta_v)$.

5. **Tame dihedral place.** Under the quadratic-cover, character-projector, vanishing-monodromy, and Frobenius-return hypotheses of Theorem 8.1, compatibility holds with $\operatorname{Ind}_{W_L}^{W_K}\theta_v$.

6. **Surface carrier.** The unitary surface supplies unconditionally its full, generally four-dimensional, middle-cohomology Weil--Deligne block. A rank-two compatibility statement holds only when both the global and local cancellation data of Chapter 9 are supplied. Under those data, the corresponding assertion from parts 1--5 holds for the surface Hom factor.

In every compatible case, Euler factors, Artin and Swan conductors, monodromy ranks, and epsilon factors for a fixed additive character and self-dual measure agree on the automorphic and Galois sides.

### 12.2 Proof

At a good place, the good integral-model theorem gives a smooth projective model with extended Hecke correspondences. Smooth proper base change kills inertia and identifies geometric Frobenius with special-fiber Frobenius. The correspondence relation and the independently known determinant give the characteristic polynomial, including the scalar case. This proves part 1.

At a strict semistable curve place, nearby cycles give the three graded pieces (5.1), and monodromy is the graph restriction--Gysin pairing. Hecke functoriality lets the multiplicity Hom construction pass through that complex. Since the multiplicity space is two-dimensional, $N$ has rank zero or one. Strictness over $K$ makes finite inertia trivial. Proposition 5.1 and Proposition 2.1 give part 2. The normalized bad correspondence computes Frobenius on the invariant graph line, so Theorem 6.2 proves part 3.

After a finite semistable extension, the equivariant stratum complex retains the finite descent action. Type projectors commute with every differential and with monodromy. If $N=0$, agreement of the inertial type and Frobenius return maps identifies the whole Weil representation by Lemma 3.1. This proves part 4. For a quadratic character orbit, the same argument is the explicit induction calculation of Chapter 8, proving part 5.

For a surface, the weight complex first computes the honest middle-cohomology pair. Under local cancellation, differentiation of the Hom action gives (9.5), and the nearby-cycle tensor factorization identifies this operator with the desired packet monodromy. The pairing supplies the determinant. The appropriate rank-two recognition theorem then proves part 6.

Finally, the formulas of Chapter 10 depend only on the isomorphism class of the Weil--Deligne parameter. Equality of parameters therefore gives equality of all the listed local invariants. $\square$

### 12.3 Consequences

The theorem provides several useful equivalences in its range.

At a split strict semistable curve place,

$$
\rho_{\Pi,\lambda}\text{ is unramified}
\quad\Longleftrightarrow\quad
N_\Pi=0.
\tag{12.1}
$$

It does not follow that the model is smooth. Under the Steinberg hypotheses,

$$
N_\Pi\ne0
\quad\Longleftrightarrow\quad
a_u(\rho_{\Pi,\lambda})=1
\tag{12.2}
$$

because finite inertia is trivial there. Without that hypothesis, the right side can also arise from a tame character.

Compatibility is stable under unramified twists and coefficient extension. It is also compatible with duality and Tate twists, provided both sides use the same geometric-Frobenius convention. A Tate twist by $n$ multiplies every geometric Frobenius eigenvalue by $q^{-n}$ and shifts the Euler variable as in (2.16); it does not alter the conductor.

## 13. Diagnostic calculations and false inferences

Short calculations expose most normalization or hypothesis errors more effectively than slogans.

### 13.1 A good prime

Suppose $s_v=1$ and the good polynomial is

$$
X^2-a_vX+q.
$$

Then the geometric Frobenius roots have product $q$ and, by weight-one purity, absolute value $q^{1/2}$. Arithmetic Frobenius has reciprocal roots, product $q^{-1}$, and trace $a_v/q$. Writing the same polynomial for arithmetic Frobenius would violate the determinant formula.

Twisting by $(1)$ changes the geometric polynomial to

$$
X^2-q^{-1}a_vX+q^{-1}.
$$

This is the cohomological twist calculation. A covariant Tate-module convention introduces a dual as well; it cannot be reproduced by changing only the constant term.

### 13.2 One loop and a separating node

An irreducible rational special fiber with one self-node has dual graph with one loop. Its $H^1$ has one length-two monodromy block, so $N$ has rank one and the conductor is one at split strict level.

Two smooth components meeting at one separating node have a tree as dual graph. The special fiber is singular, but $N=0$ on $H^1$. If the component genera sum to the generic genus, all cohomology comes from the middle component term in (5.1). Thus “one node gives conductor one” is false.

Two components meeting at two nodes have $b_1=1$. Only one linear combination of the two local vanishing cycles survives globally. Again the conductor is one, not two.

### 13.3 A tame dihedral parameter

Let $L/K$ be unramified quadratic and choose a tame character $\theta$ such that $\theta|_I\ne\theta^\sigma|_I$ and neither is trivial. Then

$$
D=\operatorname{Ind}_{W_L}^{W_K}\theta
$$

is irreducible, $N=0$, and $D^I=0$. Hence $L(s,D)=1$ and $a(D)=2$. Geometric Frobenius has trace zero and determinant $-\theta(\Phi_L)$.

Changing $\theta(\Phi_L)$ by an unramified scalar leaves the inertial type and conductor unchanged but changes the determinant and parameter. This explicitly demonstrates why type plus conductor is not local--global compatibility.

### 13.4 A surface with two bad directions

Suppose a local surface complex is a product of two nodal curve complexes with one graph cycle in each direction. On the tensor product,

$$
N=N_1\otimes1+1\otimes N_2,
$$

so

$$
N^2=2N_1\otimes N_2\ne0
\tag{13.1}
$$

over characteristic zero. The full surface block contains a length-three Jordan block. At $\ell=2$, the factor $2$ is an integral warning even though rational rank is unchanged.

A rank-two cancellation factor nevertheless satisfies $N_W^2=0$. Equation (9.5), not the total rank of $N_V$, determines whether that factor is unramified or special. Assigning the full surface $N^2$ to the rank-two factor would contradict dimension.

### 13.5 Equal conductors and unequal types

The following pairs have equal conductor but different parameters:

- $\operatorname{St}(1)$ and a nontrivial tame character direct-summed with an unramified line can both have conductor one, but only the first has $N\ne0$;
- split and nonsplit multiplicative special parameters both have conductor one, but their invariant Frobenius eigenvalues are $1$ and $-1$;
- two tame dihedral parameters with the same inertial characters and different unramified twists have the same conductor and type but different Frobenius return scalars;
- a surface block with one length-three Jordan block and a block with two length-two blocks can have the same rank of $N$ while their $N^2$ differ.

These examples justify the full comparison target $(r,N)$ and the insistence on Frobenius data.

## 14. Dependency and hypothesis audit

The proof is complete only if every imported geometric statement is used within its actual hypotheses. This chapter records that closure explicitly.

### 14.1 Imported geometric results

The following prior results are used.

**Nearby cycles and monodromy.** The low-dimensional nearby-cycle theory supplies the semistable inertia formula, $N^2=0$ for curves, $N^3=0$ for surfaces, the restriction--Gysin weight complex, the graph and dual-complex descriptions, the conductor formula, finite descent, and the integral saturation warnings. Its hypotheses are proper strict semistability, coefficients prime to the residue characteristic, and purity when surface degeneration at the second page is invoked.

**Semistable abelian varieties.** The semistable abelian-variety theory supplies the interpretation of square-zero monodromy through toric periods, the distinction between rational monodromy and component discriminants, the effect of ramified base change, and the split versus nonsplit multiplicative example. It is used only for abelian or Jacobian realizations, with $\ell\ne p$ and semistability over the stated field.

**Weil--Deligne representations.** The local parameter theory supplies the Weil group convention, extraction and reconstruction of $(r,N)$, Frobenius semisimplification, special blocks, inertial types, conductor formulas, induction, Euler factors, and epsilon factors. Every formula here uses its geometric-Frobenius and reciprocity normalization.

**Good integral models.** The good-model theorem supplies smooth projective curve and surface models, extension of prime-to-$p$ Hecke correspondences, and integral smooth proper specialization. It is invoked only under the unramified-order, self-dual-lattice, hyperspecial-level, smooth-local-model, component-descent, neatness, and anisotropy hypotheses listed in Section 4.1.

**Semistable Shimura models.** The parahoric model theorem supplies the rank-two Iwahori curve, one-direction surface, regularized two-direction surface, equivariant strata, and Hecke action on nearby cycles. It is invoked only for verified flat incidence local models and the explicit strict semistable regularizations. Arbitrary parahoric or ramified local models are not included.

**Cohomological extraction.** The weight-two extraction theorem supplies the rank-two curve multiplicity space, determinant, good Frobenius polynomial, saturated rational packet lattice, and the exact surface cancellation boundary. The present book adds the bad-place comparison; it does not reconstruct the global representation.

### 14.2 Exact hypothesis ledger

| Conclusion | Required hypotheses | What fails without them |
|---|---|---|
| good-prime unramifiedness | smooth proper good PEL model, $u\nmid\ell$ | nearby cycles can be nonconstant |
| good Frobenius polynomial | extended normalized correspondences, component stability, determinant formula | an operator relation may fail or remain only an annihilator |
| curve $N^2=0$ | proper strict semistable curve | finite or wild singularities can add descent data |
| conductor equals rank $N$ | split strict semistability over $K$ | finite inertia and Swan terms are missing |
| Steinberg identification | rank-one packet monodromy and Frobenius on its kernel | conductor one does not determine the parameter |
| finite inertial type | equivariant finite descent complex and matching type projector | quotient strata can lose stabilizers and signs |
| tame dihedral type | quadratic descent cover, inducing character, return scalar, $N=0$ | inertial characters leave an unramified ambiguity |
| surface rank two | descended split cancellation algebra, local tensor complex, pairing | the honest block remains four-dimensional |
| surface $E_2$ description | finite residue field purity or a direct degeneration proof | first-page terms need not equal graded cohomology |
| integral type summand | integral projector, saturated images, split Hecke order | rational summands need not split the lattice |
| integral surface logarithm at $\ell=2$ | separate divisibility check | the coefficient $1/2$ in the logarithm is not integral |
| coefficient-prime statement | a residue-characteristic comparison theorem | prime-to-$p$ nearby-cycle arguments do not apply |

There is no circular use of a compatible-system theorem or a finite-flat quotient theorem. Density of global Frobenius classes is unnecessary for the local arguments: each place is computed directly from its model and correspondences. A comparison between two different global carriers may use a separate density theorem, but carrier comparison is not used to prove the local parameter here.

### 14.3 Final synthesis

Local--global compatibility in weight two is now a geometric equality of Weil--Deligne parameters. At a good place, smooth proper specialization kills inertia, and the Hecke correspondence plus the determinant gives the full quadratic Frobenius polynomial. At a semistable curve place, the dual graph and its restriction--Gysin pairing decide whether the packet monodromy vanishes. A surviving graph line gives one nonzero nilpotent arrow; the normalized bad Hecke correspondence gives Frobenius on its kernel, and together they form the special parameter.

Finite descent supplies the part that semistable base change temporarily removes. Components, orientations, and coefficient systems carry the finite inertial type. Frobenius return maps complete that type to a Weil representation. In the tame dihedral case, this is exactly quadratic induction from the character appearing on the descent cover. Conductors and local factors then follow from the identified pair rather than serving as substitutes for it.

The surface case obeys the same principle at its proper dimension. Its full middle cohomology can contain length-three monodromy and is generally four-dimensional. Only a descended algebraic cancellation factor, compatible with the local nearby-cycle tensor structure and the pairing, exposes a rank-two parameter. Under that hypothesis the Hom logarithm subtracts the auxiliary monodromy and leaves the same unramified, special, or finite-type alternatives as for curves.

Throughout, geometric Frobenius acts on a Tate twist by $q^{-1}$, monodromy satisfies $FNF^{-1}=q^{-1}N$, and local Euler factors use $(\ker N)^I$. Integral lattices retain graph discriminants, component information, and saturation defects that rational conductors forget. The resulting theorem therefore compares exactly the information present on both sides—finite inertia, monodromy, Frobenius, determinant, conductor, and local constants—while keeping good reduction, semistable geometry, coefficient extension, integral structure, and surface cancellation within their proven boundaries.
