# Automorphic Forms on Definite Quaternion Algebras

## Contents

1. [From compactness to finite algebra](#1-from-compactness-to-finite-algebra)
   - [The definite setting](#11-the-definite-setting)
   - [The adelic quotient and its center](#12-the-adelic-quotient-and-its-center)
   - [Why no analytic growth condition remains](#13-why-no-analytic-growth-condition-remains)
   - [The finite problem to be solved](#14-the-finite-problem-to-be-solved)
2. [Finite double-coset spaces](#2-finite-double-coset-spaces)
   - [Levels and class sets](#21-levels-and-class-sets)
   - [Finiteness for an arbitrary compact open](#22-finiteness-for-an-arbitrary-compact-open)
   - [Representatives and stabilizers](#23-representatives-and-stabilizers)
   - [Orders, ideals, and the direction of multiplication](#24-orders-ideals-and-the-direction-of-multiplication)
   - [Central double quotients](#25-central-double-quotients)
3. [Algebraic weights at infinity](#3-algebraic-weights-at-infinity)
   - [Why a finite set can still carry weight](#31-why-a-finite-set-can-still-carry-weight)
   - [Symmetric-power construction](#32-symmetric-power-construction)
   - [Central exponents and parity](#33-central-exponents-and-parity)
   - [Fields of definition and descent](#34-fields-of-definition-and-descent)
   - [Weight lattices](#35-weight-lattices)
4. [Central characters and compatible data](#4-central-characters-and-compatible-data)
   - [Why the center cannot be ignored](#41-why-the-center-cannot-be-ignored)
   - [The compatibility equation](#42-the-compatibility-equation)
   - [Finite order nebentype](#43-finite-order-nebentype)
   - [The intersection with the level](#44-the-intersection-with-the-level)
   - [Failure of compatibility](#45-failure-of-compatibility)
5. [Quaternionic automorphic forms](#5-quaternionic-automorphic-forms)
   - [The finite-adelic definition](#51-the-finite-adelic-definition)
   - [The full-adelic definition](#52-the-full-adelic-definition)
   - [Equivalence of the two conventions](#53-equivalence-of-the-two-conventions)
   - [A warning about inverses and dual weights](#54-a-warning-about-inverses-and-dual-weights)
6. [Evaluation on the class set](#6-evaluation-on-the-class-set)
   - [The decomposition theorem](#61-the-decomposition-theorem)
   - [Proof and inverse formula](#62-proof-and-inverse-formula)
   - [Changing representatives](#63-changing-representatives)
   - [The central-character subspace](#64-the-central-character-subspace)
   - [A projective stabilizer model](#65-a-projective-stabilizer-model)
7. [Coefficient rings and finiteness](#7-coefficient-rings-and-finiteness)
   - [Finite generation](#71-finite-generation)
   - [Projectivity by averaging](#72-projectivity-by-averaging)
   - [When freeness follows](#73-when-freeness-follows)
   - [What bad stabilizer primes do](#74-what-bad-stabilizer-primes-do)
8. [Scalar extension and reduction](#8-scalar-extension-and-reduction)
   - [The base-change map](#81-the-base-change-map)
   - [Clean base change](#82-clean-base-change)
   - [Reduction can create forms](#83-reduction-can-create-forms)
   - [Torsion and saturation](#84-torsion-and-saturation)
9. [Changing level](#9-changing-level)
   - [Pullback to deeper level](#91-pullback-to-deeper-level)
   - [Trace and averaging](#92-trace-and-averaging)
   - [Finite covering fibers](#93-finite-covering-fibers)
   - [Elementary old-level maps](#94-elementary-old-level-maps)
10. [Pairings and integral models](#10-pairings-and-integral-models)
    - [Pairings on weights](#101-pairings-on-weights)
    - [Finite-sum pairings](#102-finite-sum-pairings)
    - [Stabilizer weights and measure normalization](#103-stabilizer-weights-and-measure-normalization)
    - [Perfectness and denominators](#104-perfectness-and-denominators)
    - [Admissible bases](#105-admissible-bases)
11. [The basic function spaces and examples](#11-the-basic-function-spaces-and-examples)
    - [Weight two and trivial coefficients](#111-weight-two-and-trivial-coefficients)
    - [The Hurwitz class-set model](#112-the-hurwitz-class-set-model)
    - [A level-three calculation](#113-a-level-three-calculation)
    - [Nontrivial weights on a one-class order](#114-nontrivial-weights-on-a-one-class-order)
    - [Nebentype decompositions](#115-nebentype-decompositions)
12. [Translations and finite correspondences](#12-translations-and-finite-correspondences)
    - [Right translation and conjugate level](#121-right-translation-and-conjugate-level)
    - [Spans of finite maps](#122-spans-of-finite-maps)
    - [The boundary with the next theory](#123-the-boundary-with-the-next-theory)
13. [Cuspidality in the anisotropic setting](#13-cuspidality-in-the-anisotropic-setting)
    - [No rational parabolics and no continuous spectrum](#131-no-rational-parabolics-and-no-continuous-spectrum)
    - [One-dimensional norm characters](#132-one-dimensional-norm-characters)
    - [The character subspace and its complement](#133-the-character-subspace-and-its-complement)
    - [What definiteness does and does not say](#134-what-definiteness-does-and-does-not-say)
14. [The exact finite module](#14-the-exact-finite-module)
    - [A construction checklist](#141-a-construction-checklist)
    - [The final dictionary](#142-the-final-dictionary)
    - [Conclusion](#143-conclusion)

## 1. From compactness to finite algebra

### 1.1 The definite setting

The preceding two books produced two kinds of input. The first is a quaternion algebra whose local behavior is prescribed place by place. The second is an integral level, encoded by a compact open subgroup of its finite adelic units. The present book explains how those inputs become a space of automorphic forms.

Fix throughout a totally real number field $F$ with ring of integers $R$, and write

$$
\Sigma_\infty=\operatorname{Hom}(F,\mathbf R).
$$

Let $D/F$ be a quaternion algebra ramified at every real place. Thus

$$
D_\tau=D\otimes_{F,\tau}\mathbf R\cong\mathbf H
\qquad(\tau\in\Sigma_\infty).
$$

We call $D$ **totally definite**. Put

$$
G=D^\times,\qquad Z=F^\times,\qquad
D_f=D\otimes_F\mathbf A_{F,f},\qquad G_f=D_f^\times,\qquad
G_\infty=\prod_{\tau\in\Sigma_\infty}D_\tau^\times.
$$

The full adelic group is $G(\mathbf A_F)=G_f\times G_\infty$, and its center is $Z(\mathbf A_F)=\mathbf A_F^\times$. We normally write $G(F)=D^\times$ for the diagonally embedded rational points.

The decisive feature is not merely that every $D_\tau$ is a division algebra. It is that

$$
D_\tau^\times/\mathbf R^\times
$$

is compact. Indeed, every nonzero Hamilton quaternion is a positive scalar times a norm-one quaternion, and the norm-one group is a three-sphere. Consequently $G_\infty/Z_\infty$ is compact. This is the mechanism that removes all noncompact archimedean geometry.

### 1.2 The adelic quotient and its center

The center must be visible from the beginning. The quotient

$$
G(F)\backslash G(\mathbf A_F)
$$

still has a noncompact direction coming from the adelic norm of the center. The correct compactness statement is that the projective quotient

$$
PG(F)\backslash PG(\mathbf A_F),
\qquad PG=G/Z,
$$

is compact. Equivalently, after fixing a central character, or after dividing by a suitable central subgroup, no continuous escape to infinity remains.

This qualification matters. Total definiteness makes $PG$ anisotropic, but it does not make the full idele class group compact. The module map on ideles still supplies a positive real direction. A statement that simply calls $G(F)\backslash G(\mathbf A_F)$ compact has forgotten the center.

Here is the compactness mechanism in a form that will be used repeatedly. Reduced norm gives

$$
\operatorname{Nrd}:G(\mathbf A_F)\longrightarrow\mathbf A_F^\times,
$$

and its restriction to central scalars is $z\mapsto z^2$. Modulo the center, every archimedean component may therefore be placed on the norm-one sphere. At finite places a compact open level bounds all denominators except for a finite ideal-class ambiguity. The norm-one idele class group is compact, and the finite ideal-class quotient contributes only finitely many components. These observations assemble a compact fundamental set for the projective adelic quotient.

There is a useful counterpoint. For $M_2(F)$, the diagonal matrices

$$
\begin{pmatrix}t&0\\0&1\end{pmatrix},
\qquad t\to\infty,
$$

escape every compact subset modulo scalar matrices at a real place. No finite level at the finite adeles can constrain that escape. Total definiteness removes exactly this phenomenon.

Choose a compact open subgroup

$$
U=\prod_{v<\infty}U_v\subset G_f.
$$

Almost every $U_v$ is the unit group of a maximal order. An Eichler order $\mathcal O$ of level $\mathfrak N$ gives the principal example $U=\widehat{\mathcal O}^{\times}$, but the construction needs only compactness and openness.

### 1.3 Why no analytic growth condition remains

For a split real group, an automorphic form depends on a noncompact symmetric space. Smoothness, differential equations, growth, and constant terms are then structural rather than decorative. Here the archimedean projective group is compact. A chosen finite-dimensional algebraic representation of $G_\infty$ records the weight, and the remaining variable lives on a finite set.

This does not say that the theory is trivial. Three sources of arithmetic survive:

- the finite class set can have many elements;
- each class carries a nontrivial stabilizer, so values must lie in invariant submodules;
- integral coefficients remember primes dividing stabilizer orders, at which invariants and reduction behave subtly.

Thus analysis is replaced not by bare counting but by finite representation theory over coefficient rings. That replacement is especially valuable in arithmetic applications: congruences become congruences between vectors in explicit finite modules.

### 1.4 The finite problem to be solved

The central object of this book will be a module

$$
S(U,W,\chi)
$$

built from four pieces of data:

1. the definite algebra $D$;
2. the compact open level $U\subset G_f$;
3. an algebraic weight module $W$ for $G_\infty$;
4. a central character $\chi$ compatible with the central action on $W$ and with $U$.

Its elements may be described either as equivariant functions on $G_f$ or as automorphic functions on the full adelic group. We shall prove that the two descriptions agree, decompose the module by a finite class set, determine when it is finite projective or free, and track exactly what happens under scalar extension and change of level.

No expansion at a boundary is needed because there is no boundary of a noncompact archimedean quotient. The output is a finite, integral, purely algebraic module prepared for finite adelic correspondences.

## 2. Finite double-coset spaces

### 2.1 Levels and class sets

Before attaching coefficients, isolate the finite set carrying them. Define

$$
X_U=G(F)\backslash G_f/U.
$$

The order of the quotients reflects the ideal convention of Book 88. Right multiplication changes a local generator of a right ideal, while left multiplication changes the global ideal representative. Reversing the sides would naturally classify left ideals instead.

When $U=\widehat{\mathcal O}^{\times}$, there is an exact bijection

$$
X_U\cong\operatorname{Cl}_r(\mathcal O),
\qquad
[g]\longmapsto[D\cap g\widehat{\mathcal O}].
$$

Thus $X_U$ is not an analogy for an ideal class set; it is that class set in adelic coordinates.

### 2.2 Finiteness for an arbitrary compact open

**Theorem 2.1.** For every compact open $U\subset G_f$, the set $X_U$ is finite.

**Proof strategy.** Compare $U$ with the unit group of an order. A common smaller compact open has finite index in both, so finiteness passes through finite fibers.

**Proof.** Choose an order $\mathcal O\subset D$. The intersection

$$
V=U\cap\widehat{\mathcal O}^{\times}
$$

is open in each compact group, hence has finite index in each. It is enough to show that $G(F)\backslash G_f/V$ is finite. The natural map from this set to

$$
G(F)\backslash G_f/\widehat{\mathcal O}^{\times}
$$

has fibers of size at most $[\widehat{\mathcal O}^{\times}:V]$. The target is the finite right ideal class set of $\mathcal O$. Therefore the source, and then its quotient $X_U$, are finite. $\square$

This proof separates two facts. Finiteness of ideal classes is algebraic and holds more generally. Total definiteness explains why the full archimedean theory also collapses to this finite set.

There is a second proof that displays the role of definiteness. Project $G$ to $PG=G/Z$. The quotient

$$
PG(F)\backslash PG(\mathbf A_F)
$$

is compact. Divide on the right by the compact archimedean group $PG(F_\infty)$ and by the open subgroup induced by $U$. The result is compact because it is a continuous image of a compact space, and discrete because the finite level is open. It is therefore finite. The fibers of $X_U$ over this projective finite set are controlled by

$$
F^\times\backslash\mathbf A_{F,f}^\times/(U\cap Z_f),
$$

a finite ray-class-type quotient. This proves finiteness again.

The two proofs emphasize different reusable facts. The order proof works for any quaternion algebra and gives the ideal interpretation. The projective proof explains why, in the definite case, adding the archimedean quotient introduces no continuous parameter. Neither proof permits us to discard the center: the projective step and the finite central fiber are both necessary.

### 2.3 Representatives and stabilizers

Choose representatives

$$
G_f=\coprod_{i=1}^h G(F)g_iU.
$$

The stabilizer of the right coset $g_iU$ under left $G(F)$ is

$$
\Gamma_i=G(F)\cap g_iUg_i^{-1}.
$$

The conjugation direction is forced: $\gamma g_iU=g_iU$ precisely when $g_i^{-1}\gamma g_i\in U$.

The center inside this stabilizer is

$$
C_i=F^\times\cap g_iUg_i^{-1}=F^\times\cap U,
$$

since central elements commute with $g_i$. The group $C_i$ can be infinite when $F\ne\mathbf Q$. Definiteness gives the precise finite statement

$$
\overline\Gamma_i=\Gamma_i/C_i\quad\text{is finite}.
$$

Whenever a coefficient action is trivial on $C_i$, invariants under $\Gamma_i$ are therefore invariants under the finite group $\overline\Gamma_i$.

### 2.4 Orders, ideals, and the direction of multiplication

Suppose $U=\widehat{\mathcal O}^{\times}$ and put

$$
I_i=D\cap g_i\widehat{\mathcal O}.
$$

Then $I_i$ is a locally principal proper right $\mathcal O$-ideal and

$$
\mathcal O_L(I_i)=D\cap g_i\widehat{\mathcal O}g_i^{-1}.
$$

Consequently

$$
\Gamma_i=\mathcal O_L(I_i)^\times.
$$

This is why the varying stabilizer is the unit group of the **left** order. The right order remains the fixed order $\mathcal O$. If $g_i$ is replaced by $b g_i u$, then $I_i$ is replaced by $bI_i$, its left order by $b\mathcal O_L(I_i)b^{-1}$, and its stabilizer by $b\Gamma_i b^{-1}$. All formulas below transform accordingly.

For a general $U$, one may choose an order and a finite-index subgroup as in the proof of Theorem 2.1. The clean ideal interpretation may then acquire auxiliary level structure, but the stabilizer formula remains exact.

### 2.5 Central double quotients

Let $Z_f=\mathbf A_{F,f}^\times$. A central character naturally leads to

$$
X_{U,Z}=G(F)\backslash G_f/(UZ_f).
$$

Although $UZ_f$ is not compact, this quotient is finite because it is a quotient of $X_U$. It forgets how the center permutes the ordinary classes. The forgotten information is restored by the central character.

There are therefore two useful finite models:

$$
X_U\quad\text{with a right action of }Z_f,
$$

and

$$
X_{U,Z}\quad\text{with character-twisted stabilizers}.
$$

The first is usually safer over integral coefficient rings because it avoids choices of central orbit representatives. The second is smaller and better reflects the compact quotient modulo center. We shall use both, stating explicitly when a character twist enters a stabilizer.

The reduced norm makes the central fibers concrete. It induces a map

$$
X_U\longrightarrow
F_{+}^{\times}\backslash\mathbf A_{F,f}^{\times}/\operatorname{Nrd}(U),
$$

where $F_{+}^{\times}$ denotes the totally positive elements: reduced norms from a totally definite algebra are positive at every real place. The target is a finite narrow ray-class-type quotient. This norm map is surjective. Indeed, reduced norm is surjective on $D_v^\times$ at every finite place, and these local lifts may be chosen in maximal-order units away from finitely many places, so they assemble to an element of $G_f$. The map need not be injective; its fibers retain genuinely quaternionic information. It records the abelian part of the class set and later detects norm characters.

Central multiplication by $z_f$ changes reduced norm by $z_f^2$. Thus central orbits on $X_U$ move through square classes in this norm quotient. This simple square is the source of the relation between a character $\psi$ of ideles composed with reduced norm and the central character $\psi^2$.

## 3. Algebraic weights at infinity

### 3.1 Why a finite set can still carry weight

If the underlying class set is finite, where can an archimedean weight live? It lives in the transformation law under the rational group. An element $\gamma\in G(F)$ has an archimedean component $\gamma_\infty$, and a value in a representation $W$ is required to transform by $\gamma_\infty$. Stabilizers therefore act on the value at each finite class.

This viewpoint turns the weight into a coefficient system on a finite groupoid. The objects are the classes $[g_i]$; the automorphisms are the stabilizers $\Gamma_i$; and the fiber at every object is $W$. A form is a compatible section of this finite coefficient system.

### 3.2 Symmetric-power construction

For each $\tau\in\Sigma_\infty$, choose an isomorphism after complexification

$$
D\otimes_{F,\tau}\mathbf C\cong M_2(\mathbf C).
$$

Let $V_\tau$ be the standard two-dimensional representation. Given integers

$$
n_\tau\ge0,\qquad m_\tau\in\mathbf Z,
$$

define the complex algebraic representation

$$
W_{\tau,\mathbf C}
=\operatorname{Sym}^{n_\tau}V_\tau
\otimes\det^{m_\tau}.
$$

Negative $m_\tau$ are allowed because the acting group consists of invertible elements. The total complex weight is

$$
W_\mathbf C=\bigotimes_{\tau\in\Sigma_\infty}W_{\tau,\mathbf C}.
$$

The restriction from $\operatorname{GL}_2(\mathbf C)$ to $D_\tau^\times$ is independent, up to isomorphism, of the chosen splitting. Changing the splitting conjugates the matrix representation, and inner conjugation does not change its isomorphism class.

The familiar integer $k_\tau\ge2$ corresponds to

$$
n_\tau=k_\tau-2.
$$

Calling $k_\tau=2$ “trivial weight” is correct only after the determinant normalization has also been chosen so that $m_\tau=0$. Weight two then gives $W_{\tau}=1$.

In the polynomial realization, if $V_\tau$ has basis $X,Y$, then

$$
\operatorname{Sym}^{n_\tau}V_\tau
=\bigoplus_{r=0}^{n_\tau}\mathbf C
X^{n_\tau-r}Y^r.
$$

For a chosen matrix splitting, $g$ acts by substituting the two linear forms obtained from its action on $X,Y$, and the determinant factor multiplies the result by $\det(g)^{m_\tau}$. Hence

$$
\dim W_\mathbf C=\prod_\tau(n_\tau+1).
$$

The choice of standard representation rather than its dual fixes the substitution convention. Replacing it by the dual changes the representation by a determinant twist and reverses certain matrices, but does not change the abstract method.

**Worked example.** Over $F=\mathbf Q$, take $n=k-2$. The polynomial model

$$
\operatorname{Sym}^{n}E^2
=\left\{\sum_{r=0}^{n}a_rX^{n-r}Y^r\right\}
$$

has rank $n+1$. A matrix acts by linear substitution, with the chosen determinant twist. For $k=2$ the polynomials have degree zero. For $k=4$ they are quadratic, and a nontrivial finite stabilizer may leave no vector fixed even though the underlying class set has one element.

### 3.3 Central exponents and parity

A central scalar $a\in\mathbf R^\times$ acts on $W_{\tau,\mathbf C}$ by

$$
a^{c_\tau},
\qquad c_\tau=n_\tau+2m_\tau.
$$

The integer $c_\tau$ is the **central exponent**. Necessarily

$$
c_\tau\equiv n_\tau\pmod2.
$$

This elementary congruence is the parity constraint hidden in many weight conventions. If one prescribes $n_\tau$ and a desired central exponent $c_\tau$, the determinant power

$$
m_\tau=\frac{c_\tau-n_\tau}{2}
$$

exists integrally exactly when the parities agree.

To make the representation factor through $D_\tau^\times/\mathbf R^\times$, one needs $c_\tau=0$. Thus $n_\tau$ must be even and $m_\tau=-n_\tau/2$. Over $\mathbf Q$ this is the customary projective normalization for even classical weight. Odd $n_\tau$ cannot be made projective by an integral determinant twist.

The tensor product action of $a\in F^\times$ on $W_\mathbf C$ is the scalar

$$
\rho(a)=\prod_{\tau}\tau(a)^{c_\tau}.
$$

This formula, including the signs of the real embeddings, controls compatibility with the finite central character.

### 3.4 Fields of definition and descent

The complex construction does not automatically produce a module over an arbitrary coefficient field. Let $E$ be a characteristic-zero field containing the images of all embeddings needed to realize the highest weights, splitting each quaternion factor attached to those embeddings, and stable under the relevant descent data. A weight over $E$ is an $E$-vector space $W_E$ with an algebraic action $\rho$ of the $E$-form obtained from $\operatorname{Res}_{F/\mathbf Q}D^\times$, together with an identification

$$
W_E\otimes_E\mathbf C\cong W_\mathbf C.
$$

One can ensure existence by taking $E$ sufficiently large: first contain the normal closure of $F$ and all character values, and then pass to a finite extension that splits the finitely many quaternion factors. Merely containing the normal closure of $F$ is not enough; a nonsplit quaternion algebra need not acquire a two-dimensional standard module over that field. A smaller field is allowed only when the tuple $(n_\tau,m_\tau)$ and the representation are stable under its Galois action and the required descent cocycle is effective. A nonparallel tuple can be permuted by conjugation and need not descend to $\mathbf Q$.

The distinction is real. Writing down a separate symmetric power for each embedding gives a representation over a splitting field; it does not prove descent to the field generated by its dimensions. Descent requires compatible semilinear identifications satisfying the cocycle condition.

For example, if $F$ is real quadratic with embeddings $\tau_1,\tau_2$, the weight tuple $(n_1,n_2)$ is carried to $(n_2,n_1)$ by the nontrivial automorphism of the normal closure. A parallel weight $(n,n)$ is stable and has the expected smaller field of definition. A genuinely nonparallel weight can still be used, but its coefficient field must remember the ordered embeddings, or one must take the direct sum of its Galois conjugates before descending.

### 3.5 Weight lattices

Arithmetic applications require an integral structure. Let $A$ be a domain with fraction field $E$, usually the ring of integers of a finite extension of $\mathbf Q_\ell$ or a localization of a number ring. An **integral weight lattice** is a finite projective $A$-module $W_A$ such that

$$
W_A\otimes_AE\cong W_E
$$

and such that every arithmetic subgroup $\Gamma_i$ relevant to the chosen level preserves $W_A$.

There are two standard constructions. If integral matrix models are available at the chosen coefficient prime, the polynomial lattice

$$
\operatorname{Sym}^{n}A^2\otimes\det^m
$$

is stable under integral matrices with unit determinant. More generally, suppose first that the central subgroup of every $\Gamma_i$ preserves a chosen lattice $L$. Choose finitely many representatives for each finite quotient $\Gamma_i/C_i$ and replace $L$ by the sum of their translates. Clearing the finitely many denominators that occur yields a lattice stable under every $\Gamma_i$. Without the initial stability under the possibly infinite central unit groups, finiteness of the projective stabilizers alone does not justify this construction.

The word “finitely” is essential. The full group $G(F)$ is infinite, and no arbitrary lattice is expected to be stable under all of it. The automorphic module only needs stability under the stabilizers, or under a specified semigroup if additional correspondences are later introduced.

There is also a uniform local construction. Let $E_\lambda$ be a nonarchimedean coefficient field, let $A$ be its valuation ring, and let $K_{\mathrm{wt}}$ be a compact subgroup of the $E_\lambda$-points of the algebraic group acting on $W_E$. Starting from any lattice $L$, the compact set $K_{\mathrm{wt}}L$ is bounded. Its $A$-span lies in $\varpi^{-N}L$ for some $N$, so it is a finite $A$-module and is stable under $K_{\mathrm{wt}}$. This proves that continuous finite-dimensional representations of compact nonarchimedean groups admit stable lattices.

At infinity the norm-one groups are compact real Lie groups and preserve positive-definite Hermitian forms after extension to $\mathbf C$. That gives a canonical analytic notion of boundedness, not usually a lattice over a nonarchimedean coefficient ring. The integral lattice used in the finite model is instead chosen in the algebraic representation over $E$ and made stable under the relevant arithmetic stabilizers or compact coefficient-place group. Keeping these two meanings of “compact” separate prevents an unjustified passage from a real unitary structure to an integral one.

Different stable lattices are commensurable but need not give isomorphic reductions. Integral structure is therefore data, not a consequence of the complex representation alone.

## 4. Central characters and compatible data

### 4.1 Why the center cannot be ignored

The center acts in two places. At infinity it acts through the central exponents of the weight. At finite places it acts by right translation on $G_f$. A central character connects these two actions so that a function on the adelic quotient is well defined.

Let $A$ be a coefficient ring and suppose the central action on $W_A$ is scalar. A full adelic central character is a continuous homomorphism

$$
\chi:F^\times\backslash\mathbf A_F^\times\longrightarrow A_E^\times,
$$

where $A_E$ is an ambient coefficient field or algebra containing the values. Write $\chi=\chi_f\chi_\infty$ according to finite and archimedean factors whenever this factorization is defined.

### 4.2 The compatibility equation

Our full-adelic convention will impose

$$
\Phi(gz)=\chi(z)\Phi(g)
$$

for central $z$, while the weight convention will impose

$$
\Phi(gk_\infty)=\rho(k_\infty)^{-1}\Phi(g).
$$

Applying both rules to $z_\infty\in Z_\infty$ forces

$$
\boxed{\chi_\infty(z_\infty)=\rho(z_\infty)^{-1}.}
$$

For $a\in F^\times$, the global identity $\chi(a)=1$ then gives the equivalent finite formula

$$
\boxed{\chi_f(a)=\rho(a_\infty).}
$$

In coordinates this reads

$$
\chi_f(a)=\prod_{\tau}\tau(a)^{c_\tau}.
$$

This is the exact compatibility condition; “the parities match” is only one consequence of it.

For a complex algebraic idele-class character, existence imposes a further restriction on the exponents. The image under $\chi_f$ of the compact group $\widehat R^\times$ is bounded, whereas for a totally positive global unit $u$ the displayed compatibility gives the positive real number

$$
\prod_\tau\tau(u)^{c_\tau}.
$$

All integral powers of this number remain in the same bounded image, so it must equal $1$. The logarithms of totally positive units form a full lattice in the hyperplane

$$
\left\{(x_\tau):\sum_\tau x_\tau=0\right\}.
$$

Therefore $(c_\tau)_\tau$ is orthogonal to that hyperplane, so all $c_\tau$ are equal. In other words, a complex algebraic central character over a totally real field has parallel magnitude exponent. An arbitrary algebraic idele-class character may also have sign components at the real places, but for the fixed transformation law used here those signs are not free: the equation $\chi_\infty=\rho^{-1}$ prescribes the sign at $\tau$ to be $(-1)^{c_\tau}=(-1)^{n_\tau}$. Thus compatible weights have parallel central exponent and a common parity. The tuple $(n_\tau)_\tau$ may still be nonparallel, but an arbitrarily prescribed tuple of central exponents or parities need not admit a compatible global complex central character.

### 4.3 Finite order nebentype

Often one separates an algebraic norm power from a finite-order character. Suppose, for simplicity, that all central exponents equal a common integer $c$. Then

$$
\rho(a)=N_{F/\mathbf Q}(a)^c
$$

with its sign, while the finite idele norm supplies the inverse absolute-size factor dictated by the product formula. After removing that norm contribution, the remaining character can be finite order. Its signs at infinity must still agree with the parity of the weight.

A finite-order character of the narrow or ray class quotient is the typical **nebentype**. At a real place its component is either trivial or the sign character. Since $-1$ acts on $W_{\tau}$ by $(-1)^{c_\tau}=(-1)^{n_\tau}$, the allowed sign is prescribed by the weight parity.

It is misleading to demand that $\chi_f$ itself be finite order for arbitrary nonzero central exponents. The algebraic magnitude may be unavoidable. What is finite order is the residual nebentype after the chosen algebraic normalization.

Over $\mathbf Q$, this can be seen directly. A scalar $a\in\mathbf Q^\times$ acts on $\operatorname{Sym}^n\otimes\det^m$ by $a^{n+2m}$. The finite component of the central character must restrict to this power on diagonal rational scalars, while its infinite component restricts to the inverse power. After extracting the adelic absolute-value character, a finite-order factor remains; its value at $-1$ has parity $(-1)^n$. Thus odd and even weights cannot be paired with the same sign data merely by changing level.

### 4.4 The intersection with the level

Right $U$-invariance and right central equivariance can coexist only if

$$
\boxed{\chi_f|_{U\cap Z_f}=1.}
$$

Indeed, for $z\in U\cap Z_f$ the two rules give simultaneously $f(gz)=f(g)$ and $f(gz)=\chi_f(z)f(g)$. Unless $\chi_f(z)=1$, every value is annihilated by $\chi_f(z)-1$; over a field this forces the entire space to vanish.

For $U=\widehat{\mathcal O}^{\times}$ one has

$$
U\cap Z_f=\widehat R^{\times}.
$$

Thus an unramified level admits only central characters trivial on finite integral units. A ramified nebentype requires a smaller central intersection, hence appropriately deeper level.

### 4.5 Failure of compatibility

Two counterexamples fix the role of the conditions.

First, let $F=\mathbf Q$, let $W$ have odd central exponent, and suppose $-1\in U$. Since $-1\in G(F)$ also, finite equivariance gives

$$
f(g)=f((-1)g)=(-1)f(g),
$$

so $2f(g)=0$. Over a ring in which $2$ is invertible, every form is zero. In characteristic $2$, the obstruction disappears after reduction, an early warning that new forms can appear at bad stabilizer primes.

Second, suppose $z\in U\cap Z_f$ but $\chi_f(z)\ne1$. The level and character laws contradict each other even if the archimedean parity is correct. Compatibility with rational scalars and triviality on the central part of the level are separate requirements.

## 5. Quaternionic automorphic forms

### 5.1 The finite-adelic definition

We first omit an independently imposed central character; it will be recovered as an eigenspace for central translation. Let $A$ be a commutative ring and let $W$ be a finite $A$-module carrying an $A$-linear action

$$
\rho:G(F)\longrightarrow\operatorname{Aut}_A(W)
$$

obtained from the archimedean weight. Define the module of algebraic quaternionic automorphic forms of level $U$ and weight $W$ by

$$
S(U,W)=\left\{
f:G_f\to W:
f(\gamma g u)=\rho(\gamma)f(g)
\text{ for all }\gamma\in G(F),u\in U
\right\}.
$$

No continuity clause is needed for the algebraic conclusions: the transformation law makes $f$ locally constant on the right because $U$ is open. If $W$ is given a topology, these functions are automatically continuous precisely when their finitely many values have the expected topology.

For a central character $\chi_f:Z_f\to A^\times$ compatible as in Chapter 4, define

$$
S(U,W,\chi_f)=\left\{
f:G_f\to W:
f(\gamma g u z)=\rho(\gamma)\chi_f(z)f(g)
\right\}.
$$

Here $\gamma\in G(F)$, $u\in U$, and $z\in Z_f$. The compatibility conditions prove that the right side is independent of how the same element is written. Equivalently, this is the $\chi_f$-eigenspace inside $S(U,W)$ for right central translation, with the convention

$$
(R_zf)(g)=f(gz)=\chi_f(z)f(g).
$$

If an algebraically normalized character takes values in $E^\times$ but not in $A^\times$, this definition first gives an $E$-space. An integral model exists only after choosing a lattice preserved by the character factors that actually occur. In most integral applications one removes the norm power and uses a finite-order nebentype valued in $A^\times$.

### 5.2 The full-adelic definition

The full adelic definition reveals why the finite formula has its particular covariance. Let $\chi$ be a character of $F^\times\backslash\mathbf A_F^\times$ satisfying

$$
\chi_\infty=\rho|_{Z_\infty}^{-1}.
$$

This paragraph is initially interpreted over $\mathbf C$, or over another topological field in which the archimedean representation has been realized. An integral nonarchimedean lattice does not acquire an action of arbitrary real points merely because it carries the algebraic action of $G(F)$. The full-adelic description establishes the automorphic meaning; the finite-adelic description is the one that descends cleanly to integral coefficients.

Define $\mathcal S(U,W,\chi)$ to consist of functions

$$
\Phi:G(F)\backslash G(\mathbf A_F)\longrightarrow W
$$

such that

$$
\Phi(guz)=\chi(z)\Phi(g),
\qquad
\Phi(gk_\infty)=\rho(k_\infty)^{-1}\Phi(g),
$$

for $u\in U$, $z\in Z(\mathbf A_F)$, and $k_\infty\in G_\infty$. The two right actions agree on their intersection by the compatibility equation.

Smoothness at finite places amounts to local constancy, already enforced at fixed level. At infinity the prescribed finite-dimensional transformation law leaves no independent variable. Moderate growth is automatic on the compact quotient modulo center once the central character is fixed.

### 5.3 Equivalence of the two conventions

**Theorem 5.1.** Restriction to the slice $G_f\times\{1\}$ gives an isomorphism

$$
\mathcal S(U,W,\chi)\xrightarrow{\sim}S(U,W,\chi_f).
$$

**Proof strategy.** Move every archimedean component to the right and remove it with the weight action. The rational left action then becomes the finite equivariance law.

**Proof.** Given $\Phi$, put $f(g_f)=\Phi(g_f,1)$. For $\gamma\in G(F)$,

$$
(\gamma_fg_f,1)
=\gamma(g_f,\gamma_\infty^{-1}).
$$

Left invariance and the right archimedean law give

$$
f(\gamma_fg_f)
=\Phi(g_f,\gamma_\infty^{-1})
=\rho(\gamma_\infty)f(g_f).
$$

Right $U$-invariance is immediate. For $z_f\in Z_f$, the central law gives $f(g_fz_f)=\chi_f(z_f)f(g_f)$. Thus restriction lands in the finite-adelic space.

Conversely, given $f$, define

$$
\Phi(g_f,g_\infty)=\rho(g_\infty)^{-1}f(g_f).
$$

For $\gamma\in G(F)$,

$$
\Phi(\gamma_fg_f,\gamma_\infty g_\infty)
=\rho(g_\infty)^{-1}\rho(\gamma_\infty)^{-1}
\rho(\gamma_\infty)f(g_f)
=\Phi(g_f,g_\infty).
$$

The $U$-law is clear. The central law follows separately at finite and infinite places, and the compatibility equation makes the factors combine to $\chi(z)$. The two constructions are inverse. $\square$

This proof is also a convention check. The inverse on $\rho(g_\infty)$ is forced by left invariance; choosing the opposite full-adelic convention would replace $W$ by its contragredient or reverse the finite covariance.

The same restriction argument works without dividing by the adelic center, but then compactness is lost in the central direction. At fixed finite level the finite-adelic module is nevertheless finite because rational scalars and ideal-class finiteness already control its double quotient. A central character is what packages that finite model into the customary full adelic quotient modulo center.

### 5.4 A warning about inverses and dual weights

Three definitions occur in the literature:

$$
f(\gamma g)=\rho(\gamma)f(g),
\qquad
f(\gamma g)=\rho(\gamma)^{-1}f(g),
\qquad
f(\gamma g)=f(g)\rho(\gamma)^{-1}.
$$

The last assumes row vectors or a right module. They are equivalent after replacing a representation by a suitable dual and changing how vectors are written, but formulas cannot be mixed term by term. In this book $W$ is a left module and the first finite-adelic formula is always in force.

## 6. Evaluation on the class set

### 6.1 The decomposition theorem

The purpose of introducing $X_U$ is now realized. Choose representatives $g_1,\ldots,g_h$ and put

$$
\Gamma_i=G(F)\cap g_iUg_i^{-1}.
$$

For an $A$-module with $G(F)$-action, write

$$
W^{\Gamma_i}=\{w\in W:\rho(\gamma)w=w
\text{ for all }\gamma\in\Gamma_i\}.
$$

**Theorem 6.1 (finite evaluation decomposition).** Evaluation at the representatives gives a natural isomorphism

$$
\boxed{
S(U,W)\xrightarrow{\sim}
\bigoplus_{i=1}^h W^{\Gamma_i},
\qquad
f\longmapsto(f(g_i))_i.}
$$

The word “natural” here means independent of representatives up to the canonical transport maps described in Section 6.3. It does not mean that the displayed direct sum is literally choice-free.

### 6.2 Proof and inverse formula

**Proof strategy.** The stabilizer condition is exactly what makes a value at one representative extend consistently across its double coset. Because the double cosets are disjoint, the construction can be performed independently on each.

**Proof.** If $\gamma\in\Gamma_i$, write $\gamma=g_iug_i^{-1}$ with $u\in U$. Then

$$
\rho(\gamma)f(g_i)
=f(\gamma g_i)
=f(g_i u)
=f(g_i).
$$

Hence $f(g_i)\in W^{\Gamma_i}$.

Conversely, let $w_i\in W^{\Gamma_i}$. Every $g\in G_f$ has an expression

$$
g=\gamma g_i u,
$$

and we define

$$
f(g)=\rho(\gamma)w_i.
$$

Suppose also $g=\gamma'g_i u'$. Then

$$
\delta=\gamma'^{-1}\gamma
=g_i u'u^{-1}g_i^{-1}\in\Gamma_i.
$$

Since $w_i$ is fixed by $\delta$,

$$
\rho(\gamma)w_i
=\rho(\gamma')\rho(\delta)w_i
=\rho(\gamma')w_i.
$$

Thus $f$ is well defined. Its covariance is built into the formula, and evaluation recovers $(w_i)$. $\square$

The theorem proves finite generation whenever the invariant submodules are finitely generated. It also displays the exact finite module: there are no unrecorded convergence or smoothness conditions.

There is a conceptual way to remember the proof. Form the finite groupoid whose objects are the right $U$-cosets in $G_f$ modulo $G(F)$ and whose arrows are rational elements carrying one coset to another. The fiber functor assigns $W$ to every object and $\rho(\gamma)$ to an arrow labeled by $\gamma$. A form is a global section of this groupoid coefficient system. Choosing one object in each isomorphism class turns global sections into invariants under its automorphism group, which is exactly the displayed direct sum. The groupoid itself is choice-free; representatives merely choose coordinates on it.

### 6.3 Changing representatives

Let

$$
g_i'=b_i g_i u_i,
\qquad b_i\in G(F),\quad u_i\in U.
$$

Then

$$
\Gamma_i'=b_i\Gamma_i b_i^{-1}
$$

and evaluation transforms by

$$
f(g_i')=\rho(b_i)f(g_i).
$$

Accordingly, $\rho(b_i)$ restricts to an isomorphism

$$
W^{\Gamma_i}\xrightarrow{\sim}W^{\Gamma_i'}.
$$

This calculation is the reason one must retain the $b_i$ factor even though $g_i$ and $g_i'$ represent the same class. Values are not scalar functions on $X_U$ unless the weight is trivial.

### 6.4 The central-character subspace

The right action of $Z_f$ on $X_U$ permutes its classes. If $z\in Z_f$ and

$$
g_i z=\gamma_{i,z}g_{j(i,z)}u_{i,z},
$$

then for $f\in S(U,W)$,

$$
(R_zf)(g_i)
=f(g_i z)
=\rho(\gamma_{i,z})f(g_{j(i,z)}).
$$

Therefore $S(U,W,\chi_f)$ corresponds inside $\bigoplus_iW^{\Gamma_i}$ to the simultaneous equations

$$
\rho(\gamma_{i,z})w_{j(i,z)}=\chi_f(z)w_i
\qquad(z\in Z_f).
$$

Only finitely many equations are needed. Choose representatives for the finite quotient

$$
F^\times\backslash Z_f/(U\cap Z_f).
$$

Equations for a rational scalar follow from $\chi_f(a)=\rho(a_\infty)$, and equations for an element of $U\cap Z_f$ follow from triviality of $\chi_f$ there. Thus equations for the chosen finite representatives imply all the others. This model is canonical even though this economical list of equations uses choices, and it avoids dividing the original class set by the center.

When the finite central action is semisimple, the whole space decomposes into nebentype eigenspaces. If a finite abelian quotient $C$ acts and $|C|$ is invertible in $A$, the idempotent for a character $\eta:C\to A^\times$ is

$$
e_\eta=\frac1{|C|}\sum_{c\in C}\eta(c)^{-1}R_c.
$$

If $|C|$ is not invertible, these idempotents need not exist and a direct-sum character decomposition can fail.

### 6.5 A projective stabilizer model

For completeness, one can work directly over $X_{U,Z}$. Choose representatives $g_i$ for that quotient and define the relation group

$$
P_i=\{(\gamma,h)\in G(F)\times(UZ_f)^{\mathrm{op}}:
\gamma g_ih=g_i\}.
$$

The opposite group records that right transformations compose in reverse order. Write $h=uz$ with $u\in U$ and $z\in Z_f$. Then $P_i$ acts on $W$ through

$$
(\gamma,h)\cdot w=\rho(\gamma)\chi_f(z)w.
$$

If $h=u'z'$ is another decomposition, then $z'z^{-1}\in U\cap Z_f$, so the scalar is unchanged. Thus the action is well defined precisely because $\chi_f$ is trivial on $U\cap Z_f$ and compatible with $F^\times$. Evaluation gives

$$
S(U,W,\chi_f)\cong\bigoplus_i W^{P_i}.
$$

The effective image of $P_i$ is finite: after quotienting central redundancies it embeds in the finite projective arithmetic stabilizer. This is the central analogue of Theorem 6.1. The relation-group notation prevents an ambiguity that arises if one writes merely “$\Gamma_i$ twisted by $\chi$” without recording which finite idele supplies the twist.

## 7. Coefficient rings and finiteness

### 7.1 Finite generation

The finite direct-sum formula reduces all coefficient questions to invariant theory. Suppose $W$ is a finitely generated $A$-module. Since

$$
W^{\Gamma_i}=\bigcap_{\gamma\in\Gamma_i}
\ker(\rho(\gamma)-1),
$$

finite generation of the invariants is automatic when $A$ is Noetherian and the effective stabilizer is finite. Indeed, it is then a submodule of the finite module $W$. Consequently $S(U,W)$ is finite over a Noetherian coefficient ring.

Over a non-Noetherian ring a submodule of a finite module need not be finitely generated. Thus finiteness of $X_U$ alone does not prove finite generation over every possible coefficient ring.

In particular, if $A=E$ is a field and $W$ is finite-dimensional, then

$$
\dim_E S(U,W)
=\sum_{i=1}^h\dim_EW^{\Gamma_i}
\le h\dim_EW.
$$

This is the precise finite-dimensionality theorem in the definite setting. The inequality can be strict, dramatically so, because stabilizers may kill all vectors in some fibers.

If the central subgroup $C_i$ acts nontrivially, the invariant module may vanish or be torsion. For the cleanest theory one assumes the weight and central data make $C_i$ act trivially, reducing the action to the finite group $\overline\Gamma_i$.

### 7.2 Projectivity by averaging

**Theorem 7.1.** Assume:

1. $W$ is finite projective over $A$;
2. $C_i$ acts trivially on $W$ for every $i$;
3. $|\overline\Gamma_i|$ is a unit in $A$ for every $i$.

Then $S(U,W)$ is finite projective over $A$.

**Proof strategy.** Average over each finite stabilizer. The averaging operator is an idempotent whose image is the invariant module.

**Proof.** Define

$$
e_i=\frac1{|\overline\Gamma_i|}
\sum_{\gamma\in\overline\Gamma_i}\rho(\gamma)
\in\operatorname{End}_A(W).
$$

The sum is independent of representatives because $C_i$ acts trivially. Reindexing shows $e_i^2=e_i$, and a vector lies in its image exactly when it is fixed by every group element. Hence

$$
W^{\Gamma_i}=e_iW
$$

is a direct summand of the finite projective module $W$. Theorem 6.1 now expresses $S(U,W)$ as a finite direct sum of finite projective modules. $\square$

The same proof applies to the central relation groups $P_i$ once their effective finite orders are invertible.

### 7.3 When freeness follows

Projective does not mean free over an arbitrary ring. Freeness follows under familiar additional hypotheses:

- if $A$ is local, every finite projective $A$-module is free;
- if $A$ is a principal ideal domain, every finite projective module is free;
- if each $W^{\Gamma_i}$ is known independently to be free, their finite direct sum is free.

There is also a stronger lattice statement that does not use averaging. If $A$ is a Dedekind domain and $W$ is finite projective, then every $W^{\Gamma_i}$ is a finite torsion-free submodule and is therefore projective. If $A$ is a principal ideal domain and $W$ is finite free, these invariant modules are finite free. In particular this holds when $A$ is a discrete valuation ring, even when a stabilizer order is not a unit. The conclusion is only projectivity or freeness: the invariant submodule need not be a direct summand of $W$ as a representation, its formation need not commute with reduction, and the restricted pairing need not be perfect. For a central-character space, the same argument applies after realizing it as the kernel of the finitely many central equations in Section 6.4.

Even when $W$ is free of rank $r$, the ranks of $W^{\Gamma_i}$ may vary with $i$. Over a domain with invertible stabilizer orders, their generic ranks are the dimensions of the fixed spaces in $W\otimes_A\operatorname{Frac}(A)$. Thus

$$
\operatorname{rank}_A S(U,W)
=\sum_i\dim_E(W_E^{\Gamma_i})
$$

whenever all invariant summands are projective of constant rank.

For trivial $W=A$, every stabilizer acts trivially and the formula reduces to

$$
S(U,A)\cong A^h.
$$

No inversion of stabilizer orders is needed in this special case.

Over a characteristic-zero splitting field, fixed-space dimensions can be calculated from characters. If $\vartheta_W$ is the character of the effective finite stabilizer, then

$$
\dim W^{\overline\Gamma_i}
=\frac1{|\overline\Gamma_i|}
\sum_{\gamma\in\overline\Gamma_i}\vartheta_W(\gamma).
$$

This is the trace of the averaging idempotent. It is especially useful when unit groups of left orders are known explicitly. The formula belongs to finite representation theory; it is not a dimension formula obtained from analytic index theory.

A sufficiently small level simplifies every coefficient question. Say that $U$ is **neat for the chosen central data** if every projective stabilizer $\overline\Gamma_i$ is trivial. Then, once the central subgroup acts compatibly,

$$
S(U,W)\cong\bigoplus_iW
$$

noncanonically, and arbitrary scalar extension is immediate. Principal congruence subgroups of sufficiently deep level are often neat because a finite-order arithmetic element congruent sufficiently closely to $1$ must be central. The required depth depends on the residue characteristics and on which central torsion is retained.

### 7.4 What bad stabilizer primes do

If a stabilizer order is not invertible, averaging is unavailable. Three distinct failures can occur: invariants need not split off, invariants need not commute with base change, and a perfect pairing on $W$ need not restrict perfectly.

For a concrete projectivity failure, take

$$
A=\mathbf Z/4\mathbf Z,\qquad W=A,
$$

and let a group of order two act by $-1$. Then

$$
W^{C_2}=\{x:2x=0\}=2A\cong\mathbf Z/2\mathbf Z,
$$

which is not projective over $A$. The ambient module is free, but its invariant submodule is not.

This phenomenon is not a defect in the definition. It is genuine arithmetic at primes dividing the torsion of definite order-unit groups. One may avoid it by choosing a sufficiently small level for which projective stabilizers are trivial, or one may retain it because the resulting torsion contains useful congruence information.

## 8. Scalar extension and reduction

### 8.1 The base-change map

Let $A\to B$ be a homomorphism and put $W_B=W_A\otimes_AB$. There is a natural map

$$
\beta:S(U,W_A)\otimes_AB
\longrightarrow S(U,W_B).
$$

Under evaluation it is the direct sum of maps

$$
W_A^{\Gamma_i}\otimes_AB
\longrightarrow(W_A\otimes_AB)^{\Gamma_i}.
$$

The map sends $w\otimes b$ to $w\otimes b$. Its existence is automatic; its being an isomorphism is not.

Flatness of $B$ over $A$ preserves the kernel of any one endomorphism, and because the effective stabilizer is finite, it preserves the finite intersection of kernels. Hence flat scalar extension gives an isomorphism when the action factors through a finite group. Reduction modulo a prime is generally not flat and requires stronger hypotheses.

### 8.2 Clean base change

**Theorem 8.1.** Suppose the hypotheses of Theorem 7.1 hold. Then for every $A$-algebra $B$,

$$
S(U,W_A)\otimes_AB
\xrightarrow{\sim}S(U,W_A\otimes_AB).
$$

**Proof.** The invariant summand is the image of the averaging idempotent $e_i$. Idempotent images commute with arbitrary scalar extension:

$$
(e_iW_A)\otimes_AB\cong(e_i\otimes1)(W_A\otimes_AB).
$$

The latter is exactly the invariant module after base change because the same average is defined over $B$. Sum over $i$. $\square$

The theorem applies equally to central-character spaces if the character values lie in $A$, the relevant central finite quotient has invertible order, and its idempotent is included in the averaging.

It is useful to separate three levels of base-change control:

1. for a flat $A$-algebra, finite-group invariants commute with base change without dividing the group order;
2. for arbitrary $A$-algebras, invertibility of the group order supplies an averaging idempotent and gives compatibility;
3. for nonflat reduction at a bad group prime, compatibility can fail and must be tested by torsion or cohomology.

The first assertion assumes the action is through a finite group, so invariants are the kernel of one map

$$
W\longrightarrow\bigoplus_{\gamma\in\Gamma}W,
\qquad
w\longmapsto((\gamma-1)w)_\gamma.
$$

Flatness preserves this kernel. This proof also shows why an infinite, uncontrolled stabilizer action would require additional hypotheses.

### 8.3 Reduction can create forms

Take $A=\mathbf Z$, let $C_2$ act on $W=A$ by sign, and reduce modulo $2$. In characteristic zero,

$$
W^{C_2}=0.
$$

After reduction the sign becomes trivial, so

$$
(W\otimes\mathbf F_2)^{C_2}=\mathbf F_2.
$$

Therefore

$$
W^{C_2}\otimes\mathbf F_2=0
\ne\mathbf F_2=(W\otimes\mathbf F_2)^{C_2}.
$$

In automorphic language, a mod-$2$ form can exist even though it is not the reduction of a characteristic-zero form of the chosen lattice. The source is stabilizer torsion, not a change in the class set.

More generally, if a central unit acts on $W_A$ by a scalar congruent to $1$ modulo a prime, reduction can make previously incompatible weight or character data compatible. Such forms must not be silently identified with reductions of integral characteristic-zero forms.

### 8.4 Torsion and saturation

Suppose $A$ is a discrete valuation ring with uniformizer $\varpi$ and $W_A$ is free. The inclusion

$$
W_A^{\Gamma}\subset W_A
$$

is automatically **saturated**, meaning that $W_A/W_A^\Gamma$ is torsion-free. Indeed, if $\varpi x$ is invariant, then

$$
\varpi(\gamma x-x)=0
$$

for every $\gamma$, and torsion-freeness of $W_A$ forces $x$ to be invariant. Hence reduction of the invariant lattice injects into invariants after reduction, but saturation does not by itself ensure surjectivity.

The obstruction is measured by group cohomology. From

$$
0\to W_A\xrightarrow{\varpi}W_A\to W_A/\varpi W_A\to0
$$

one obtains the exact segment

$$
0\to W_A^\Gamma/\varpi W_A^\Gamma
\to(W_A/\varpi W_A)^\Gamma
\to H^1(\Gamma,W_A)[\varpi]\to0.
$$

Thus new mod-$\varpi$ invariants are exactly detected by $\varpi$-torsion in $H^1$. If $|\Gamma|$ is a unit, higher cohomology is killed by averaging and the obstruction vanishes. This explains, rather than merely restates, the good-prime hypothesis.

## 9. Changing level

### 9.1 Pullback to deeper level

Let $U'\subset U$ be compact open subgroups. Since a $U$-invariant function is automatically $U'$-invariant, there is an injective pullback

$$
\operatorname{res}_{U}^{U'}:S(U,W)\hookrightarrow S(U',W).
$$

The terminology “restriction” refers to restricting the invariance condition, not the function's domain; both spaces consist of functions on the same group $G_f$.

On class sets there is a surjection

$$
\pi:X_{U'}\longrightarrow X_U.
$$

For trivial weight, pullback is literally composition with $\pi$. For nontrivial weight, values on a fiber are related by the rational transformations that identify its representatives.

### 9.2 Trace and averaging

Choose representatives $u_1,\ldots,u_d$ for the right cosets $U/U'$, so

$$
U=\coprod_{j=1}^d u_jU'.
$$

For $f\in S(U',W)$ define

$$
\operatorname{Tr}_{U'}^U(f)(g)
=\sum_{j=1}^d f(gu_j).
$$

Changing $u_j$ within its right $U'$-coset does not change a summand. Left multiplication of the set of representatives by an element of $U$ permutes the right cosets, so the sum is right $U$-invariant. Left covariance is immediate. Hence the trace maps $S(U',W)$ to $S(U,W)$.

For $f\in S(U,W)$,

$$
\operatorname{Tr}_{U'}^U(\operatorname{res}_{U}^{U'}f)
=[U:U']f.
$$

If the index is invertible in $A$, the normalized average

$$
\operatorname{Av}_{U'}^U=\frac1{[U:U']}\operatorname{Tr}_{U'}^U
$$

is a retraction of pullback. Thus the old level is a direct summand at such coefficients. Without invertibility, trace still exists but need not split pullback.

These maps are transitive. If $U''\subset U'\subset U$, decomposing $U/U''$ first into right $U'$-cosets and then each $U'$-coset into right $U''$-cosets gives

$$
\operatorname{Tr}_{U''}^{U}
=\operatorname{Tr}_{U'}^{U}\circ\operatorname{Tr}_{U''}^{U'},
$$

and pullbacks compose in the evident direction.

Adjointness requires the stabilizer weights, not merely counting each class once. Normalize the quotient-groupoid measure separately at each level so that the image of the relevant projective compact open has volume one. For forms with inverse central characters, the orbit--stabilizer formula then gives

$$
\left\langle \operatorname{res}_{U}^{U'}f,h\right\rangle_{U'}
=
\left\langle f,\operatorname{Tr}_{U'}^Uh\right\rangle_U.
$$

In class-set coordinates these are the mass pairings of Section 10.3, with reciprocal effective stabilizer orders. If instead one fixes a single Haar measure across both levels, then $\operatorname{vol}(U')=\operatorname{vol}(U)/[U:U']$ and the displayed formula acquires the corresponding factor $[U:U']^{-1}$ on its right side. The unweighted finite-sum pairings generally do not satisfy either formula without further corrections: when stabilizers identify points in a fiber, multiplicities remain. This is another reason not to treat $X_{U'}\to X_U$ as a covering of constant degree.

### 9.3 Finite covering fibers

The map $X_{U'}\to X_U$ need not have constant fiber size. Over the class represented by $g_i$, its fiber is naturally

$$
\Gamma_i\backslash g_iU/U'
\cong
(g_i^{-1}\Gamma_i g_i\cap U)\backslash U/U'.
$$

The left stabilizer can identify several right cosets. This is the finite-set shadow of orbifold stabilizers. In particular, one must not infer

$$
|X_{U'}|=[U:U']|X_U|
$$

unless all relevant stabilizer actions on $U/U'$ are free.

If $U'$ is normal in $U$, the finite group $U/U'$ acts on $X_{U'}$ on the right and $X_U$ is its orbit set. Fixed points again arise from arithmetic stabilizers.

### 9.4 Elementary old-level maps

Right translation can give several embeddings of a shallower-level function space into a deeper-level one. At this stage these are only maps of finite function spaces. Their linear span may be called an elementary old-level submodule, but no assertion is yet made about orthogonal complements, newness, eigenvectors, or local representation type.

That restraint is important. A systematic old/new theory depends on the algebra of double-coset correspondences and on relations among its operators. Here we have established only the underlying pullback, trace, and translation maps from which such a theory can later be built.

## 10. Pairings and integral models

### 10.1 Pairings on weights

Pairings turn the finite module into a self-dual or dualizable object and later allow adjoints of correspondences to be discussed. Let $W$ and $W'$ be finite $A$-modules with $G(F)$-actions. Suppose

$$
\langle\ ,\ \rangle_W:W\times W'\longrightarrow A
$$

is bilinear and invariant in the sense that

$$
\langle\rho(\gamma)x,\rho'(\gamma)y\rangle_W
=\langle x,y\rangle_W
\qquad(\gamma\in G(F)).
$$

The basic example is $W'=W^\vee=\operatorname{Hom}_A(W,A)$ with contragredient action

$$
(\rho^\vee(\gamma)\lambda)(w)
=\lambda(\rho(\gamma)^{-1}w).
$$

Then evaluation $\langle w,\lambda\rangle_W=\lambda(w)$ is invariant. If central characters are included, the two form spaces must have inverse central characters so that their scalar factors cancel.

For symmetric powers there is also, after a determinant twist, a natural invariant pairing. On degree-$n$ binary forms it is induced by the alternating form on the standard two-dimensional representation. Its symmetry sign is $(-1)^n$. Over an integral ring, a divided-power lattice can be preferable to the monomial lattice because binomial coefficients affect perfectness.

### 10.2 Finite-sum pairings

Choose representatives $g_1,\ldots,g_h$. Define

$$
\langle f,h\rangle_{\mathrm{sum}}
=\sum_{i=1}^h
\langle f(g_i),h(g_i)\rangle_W.
$$

This is independent of the chosen representatives: replacing $g_i$ by $b_i g_i u_i$ applies $\rho(b_i)$ to the first value and $\rho'(b_i)$ to the second, and weight invariance cancels both actions. It is also plainly independent of the ordering.

Under Theorem 6.1 this is the orthogonal direct sum of the restricted pairings

$$
W^{\Gamma_i}\times(W')^{\Gamma_i}\to A.
$$

The formula uses counting measure on the selected set of orbits. It is integral and involves no denominators. Its possible imperfection lies entirely in the restriction of the weight pairing to invariants.

For trivial coefficients the pairing can be read without representation theory. If

$$
f=\sum_i a_i\mathbf1_i,
\qquad
h=\sum_i b_i\mathbf1_i,
$$

then

$$
\langle f,h\rangle_{\mathrm{sum}}=\sum_i a_ib_i.
$$

This is perfect over every coefficient ring. The mass pairing replaces the diagonal entries $1$ by stabilizer reciprocals. It is the mass normalization, not the underlying function space, that introduces denominators.

### 10.3 Stabilizer weights and measure normalization

There is another canonical normalization modeled on integration over a quotient groupoid. Assume the central action has been removed and the effective stabilizers $\overline\Gamma_i$ are finite. Algebraically, assign the class represented by $g_i$ the groupoid mass

$$
\frac1{|\overline\Gamma_i|}.
$$

The corresponding pairing is

$$
\boxed{
\langle f,h\rangle_{\mathrm{mass}}
=\sum_{i=1}^h
\frac{1}{|\overline\Gamma_i|}
\langle f(g_i),h(g_i)\rangle_W.}
$$

This becomes an adelic integration formula after Haar measures on the projective group and on the remaining central quotient have been fixed compatibly. For a central quotient, $\overline\Gamma_i$ is replaced by the effective finite relation stabilizer from Section 6.5. Scaling the relevant compact-open volume by $c$ multiplies every term by $c$. The central-volume convention, the level volume, and the stabilizer denominator must be changed together; saying only that “$U$ has volume one” is insufficient before the center has been removed.

Over an integral ring these fractions may not exist. One may enlarge coefficients by inverting all stabilizer orders, multiply the entire form by a common denominator, or retain the unweighted sum pairing. These choices give the same characteristic-zero geometry but different integral lattices.

### 10.4 Perfectness and denominators

Suppose $W$ and $W'$ are finite projective and paired perfectly. If $|\overline\Gamma_i|$ is invertible in $A$, averaging identifies

$$
(W^{\Gamma_i})^\vee\cong(W^\vee)^{\Gamma_i}.
$$

Indeed, the averaging idempotent on the dual is the transpose of the averaging idempotent on $W$. Therefore the finite-sum pairing between $S(U,W)$ and $S(U,W^\vee)$ is perfect. Multiplying each direct summand by a unit $|\overline\Gamma_i|^{-1}$ preserves perfectness of the mass pairing.

Without invertibility, the restriction can be degenerate even if the ambient pairing is perfect. Let $C_2$ act by sign on $W=\mathbf Z/4\mathbf Z$ and pair $W$ with itself by multiplication. The invariant submodule is $2W$, and its restricted pairing is zero because $2\cdot2=0$. Thus perfectness cannot be inferred from the weight lattice alone.

For central character spaces, perfectness additionally requires that the character eigenspace be cut out by an idempotent. A sufficient condition is that the order of the finite central quotient be invertible and all character values lie in $A$.

### 10.5 Admissible bases

An **admissible basis** of $S(U,W)$ consists of:

1. ordered representatives $g_1,\ldots,g_h$ of $X_U$;
2. for each $i$, an $A$-basis of $W^{\Gamma_i}$.

Concatenating the component bases through Theorem 6.1 gives a basis of the form space whenever all invariant modules are free. It is adapted simultaneously to the class decomposition, integral structure, and finite correspondences.

If the invariants are merely projective, one should speak of an admissible projective decomposition, not a basis. After localization at a prime where the summands become free, admissible bases exist locally. A change of class representative multiplies a component basis by $\rho(b_i)$; a change of invariant basis acts block diagonally.

This produces a **$q$-free combinatorial model**: a vector is a finite list

$$
(w_1,\ldots,w_h),
\qquad w_i\in W^{\Gamma_i},
$$

and every later finite correspondence is represented by a finite matrix of coefficient-system maps. Nothing is encoded by an expansion parameter or a limiting process.

## 11. The basic function spaces and examples

### 11.1 Weight two and trivial coefficients

Take $n_\tau=0$ and $m_\tau=0$ at every real place. Then $W=A$ with trivial action. This is the algebraic weight-two normalization. The decomposition becomes

$$
S(U,A)=\operatorname{Map}(X_U,A)
\cong A^{|X_U|}.
$$

The characteristic function $\mathbf1_i$ of each double coset gives an admissible basis. No stabilizer prime causes a projectivity problem because invariants of the trivial rank-one module are the whole module.

If a compatible central character is imposed, $S(U,A,\chi_f)$ is the submodule of functions obeying

$$
f([g]z)=\chi_f(z)f([g]).
$$

On each central orbit, the value at one point determines all others, subject to the condition that $\chi_f$ be trivial on the orbit stabilizer. Thus even the scalar case can vanish for an incompatible nebentype.

### 11.2 The Hurwitz class-set model

Let

$$
D=(-1,-1)_{\mathbf Q}
$$

and let $\mathcal H$ be the Hurwitz maximal order. The algebra is ramified at $2$ and infinity, and Book 88 established

$$
D^\times\backslash D_f^\times/\widehat{\mathcal H}^{\times}
=\{[1]\}.
$$

The stabilizer of the sole class is

$$
\Gamma=\mathcal H^\times,
$$

the binary tetrahedral group of order $24$. Consequently

$$
S(\widehat{\mathcal H}^{\times},W)
\cong W^{\mathcal H^\times}.
$$

For trivial $W=A$, this is $A$: every form is constant on the unique class. The mass pairing is

$$
\langle a,b\rangle_{\mathrm{mass}}=\frac1{12}ab
$$

for the projective normalization in which the image of the level has volume one, because $\mathcal H^\times/\{\pm1\}$ has order $12$. If one works before removing the center and normalizes the nonprojective quotient differently, the orbit weight is $1/24$; the two conventions differ by the central volume. The unweighted integral pairing is simply $ab$. This one-class example already shows why a class-number calculation does not determine a nontrivial-weight space: the stabilizer representation still matters.

### 11.3 A level-three calculation

Keep the Hurwitz algebra and maximal level away from $3$, but at $3$ replace

$$
\mathcal H_3^\times\cong\operatorname{GL}_2(\mathbf Z_3)
$$

by the principal congruence subgroup

$$
U(3)_3=\ker\bigl(\operatorname{GL}_2(\mathbf Z_3)
\to\operatorname{GL}_2(\mathbf F_3)\bigr).
$$

Call the resulting global level $U(3)$. Since the maximal class set has one element,

$$
X_{U(3)}\cong
\mathcal H^\times\backslash
\widehat{\mathcal H}^{\times}/U(3).
$$

Reduction at $3$ identifies the right quotient with $\operatorname{GL}_2(\mathbf F_3)$. Direct reduction of the explicit list of $24$ Hurwitz units shows that they remain distinct; their image lies in $\operatorname{SL}_2(\mathbf F_3)$ because every one has reduced norm one. Since $\operatorname{SL}_2(\mathbf F_3)$ also has order $24$, the image is the whole group. Hence

$$
X_{U(3)}\cong
\operatorname{SL}_2(\mathbf F_3)\backslash
\operatorname{GL}_2(\mathbf F_3)
\cong\mathbf F_3^\times,
$$

so this level has two classes. For trivial coefficients,

$$
S(U(3),A)\cong A^2.
$$

The two classes are detected by the determinant modulo $3$. This is a complete finite calculation: deeper level enlarges the class set by a quotient of a local finite group, while global units identify some of its elements.

### 11.4 Nontrivial weights on a one-class order

Again take maximal Hurwitz level, but let $W_\mathbf C=\operatorname{Sym}^2\mathbf C^2$ with the determinant normalization irrelevant on norm-one units. The quotient $\mathcal H^\times/\{\pm1\}$ is the tetrahedral rotation group. Its action on the three-dimensional symmetric-square representation is the standard rotation representation, which has no fixed vector. Therefore

$$
S(\widehat{\mathcal H}^{\times},W_\mathbf C)=0.
$$

This is the simplest counterexample to the idea that “one ideal class gives one form.” It gives one copy of the stabilizer invariants, whose dimension can be zero, one, or larger depending on the weight.

At primes $2$ and $3$, reduction can change these invariants because those primes divide $|\mathcal H^\times|=24$. Away from $6$, averaging guarantees that formation of the invariant lattice commutes with reduction.

### 11.5 Nebentype decompositions

Let $C$ be a finite quotient of $Z_f$ acting on $X_U$, and suppose $A$ contains the values of all its characters. If $|C|$ is invertible in $A$, then

$$
S(U,W)=\bigoplus_{\eta\in\widehat C}S(U,W,\eta),
$$

where only characters compatible with the weight and central level intersection contribute. The projector is the idempotent $e_\eta$ of Section 6.4.

**Worked orbit calculation.** Suppose $C$ acts transitively on an orbit $\mathcal O\subset X_U$ and $x\in\mathcal O$ has stabilizer $C_x$. A scalar function of character $\eta$ on this orbit is determined by $a=f(x)$, while

$$
a=f(xc)=\eta(c)a
\qquad(c\in C_x).
$$

Over a field, the orbit contributes one dimension if $\eta|_{C_x}=1$ and zero otherwise. With a weight fiber $W_x$, replace the scalar condition by invariance under the combined stabilizer action.

If $|C|$ is not invertible, generalized character phenomena and extensions between character submodules can occur. It is then safer to retain the action of $C$ rather than claim a direct-sum nebentype decomposition.

## 12. Translations and finite correspondences

### 12.1 Right translation and conjugate level

For $a\in G_f$ and $f\in S(U,W)$, define

$$
(R_af)(g)=f(ga).
$$

This function has level

$$
aUa^{-1},
$$

because for $u'\in aUa^{-1}$,

$$
(R_af)(gu')=f(gu'a)=f(ga(a^{-1}u'a))=f(ga).
$$

In the middle expression the useful identity is $u'a=a(a^{-1}u'a)$. Left covariance is unchanged. Thus

$$
R_a:S(U,W)\xrightarrow{\sim}S(aUa^{-1},W),
$$

with inverse $R_{a^{-1}}$. If $a$ normalizes $U$, this is an automorphism of the fixed-level space.

On representatives, write

$$
g_i a=\gamma_{i,a}g_{j(i,a)}u_{i,a}.
$$

Then

$$
(R_af)(g_i)=\rho(\gamma_{i,a})f(g_{j(i,a)}).
$$

This is a finite permutation of components decorated by weight matrices.

### 12.2 Spans of finite maps

An element $a$ rarely normalizes $U$. Nevertheless the intersection

$$
U_a=U\cap aUa^{-1}
$$

has finite index in both groups. It gives a span of finite class-set maps

$$
X_{U_a}\longrightarrow X_U,
\qquad
X_{U_a}\longrightarrow X_U,
$$

where the first forgets from $U_a$ to $U$ and the second sends $[g]$ to $[ga]$; it is well defined because $a^{-1}U_a a\subset U$. Pullback along the second map and trace along the first produce an endomorphism-shaped correspondence on $S(U,W)$.

At the level of functions, every ingredient has already been defined: restriction, translation, and finite trace. Composition is therefore a finite sum. The stabilizer formulas ensure it is independent of representatives.

To see the matrix shape, suppose a finite correspondence sends the $i$th source class through finitely many translated points and that each such point is rewritten as

$$
g_i a_r=\gamma_{i,r}g_{j(i,r)}u_{i,r}.
$$

In an admissible decomposition its contribution has the form

$$
w_{j(i,r)}\longmapsto\rho(\gamma_{i,r})w_{j(i,r)}
$$

followed, when necessary, by projection to the target stabilizer invariants. Summing over $r$ gives a block matrix. If stabilizer orders are invertible, the projection is the averaging idempotent; without that hypothesis the trace construction itself remains integral and should be used instead of inserting denominators.

Changing representatives conjugates this matrix by the block-diagonal changes $\rho(b_i)$. Hence its linear map is intrinsic even though its entries are coordinate dependent. This is precisely why admissible bases are useful: they expose the finite calculation without pretending that the chosen matrix is canonical.

### 12.3 The boundary with the next theory

We stop before naming or organizing these endomorphisms. Their systematic theory requires local double-coset algebras, convolution normalizations, relations at unramified and level places, commutativity statements, and compatibility among many choices. Those belong to the next book.

The present preparation is exact but deliberately elementary:

- right translation changes level by $U\mapsto aUa^{-1}$;
- intersections provide a common deeper level;
- pullback and trace turn a finite span into a linear map;
- an admissible basis makes that map a finite matrix.

No eigenform, eigenvalue system, or operator algebra is needed to define the module on which those later objects act.

## 13. Cuspidality in the anisotropic setting

### 13.1 No rational parabolics and no continuous spectrum

Constant terms in the usual automorphic theory are integrals along unipotent radicals of proper rational parabolic subgroups. For $G=D^\times$ with $D$ a division algebra, there is no proper rational parabolic subgroup. Equivalently, $PG$ is anisotropic over $F$.

Thus the parabolic constant-term condition is vacuous. After fixing the center, the automorphic quotient is compact, so there is no continuous spectrum produced by Eisenstein series and no analytic growth problem at cusps. The finite algebraic model captures the entire fixed-weight, fixed-level space.

This statement explains the absence of analytic apparatus. It does not yet identify which definite forms correspond to cuspidal representations on a split group.

### 13.2 One-dimensional norm characters

The reduced norm

$$
\operatorname{Nrd}:D^\times(\mathbf A_F)\longrightarrow\mathbf A_F^\times
$$

allows every idele-class character $\psi$ to produce a scalar-valued one-dimensional automorphic character

$$
g\longmapsto\psi(\operatorname{Nrd}(g)).
$$

On a central scalar $z$, reduced norm is $z^2$, so the central character of this automorphic character is $\psi^2$. It satisfies the vacuous intrinsic cuspidality condition because there are no proper parabolics. Nevertheless it is one-dimensional and belongs to the character spectrum rather than the genuinely nonabelian spectrum.

There is a coefficient-system qualification. The scalar function $\psi\circ\operatorname{Nrd}$ belongs to a space with coefficient module $W$ only when its archimedean character occurs as a one-dimensional subrepresentation of $W$ and its finite conductor and central character match the level data. Over characteristic zero, for the irreducible weight

$$
\bigotimes_\tau\operatorname{Sym}^{n_\tau}V_\tau
\otimes\det^{m_\tau},
$$

this can happen only when every $n_\tau=0$; the resulting algebraic character is a product of determinant, hence reduced-norm, powers. Thus a scalar norm character must not be inserted into a higher-dimensional weight space merely because its central character agrees.

This distinction is essential in comparisons with automorphic forms on $\operatorname{GL}_2$. One-dimensional representations of $D^\times$ do not transfer as cuspidal two-dimensional automorphic representations in the same manner as higher-dimensional constituents.

### 13.3 The character subspace and its complement

Define the **norm-character subspace** $S^{\mathrm{char}}(U,W,\chi)$ to be the span of the compatible one-dimensional automorphic subrepresentations that occur in the chosen coefficient system, equivalently of the embeddings of matching characters $\psi\circ\operatorname{Nrd}$ into the form space. It is zero when $W$ contains no matching one-dimensional weight. In trivial weight it can be described entirely on the class set: such a function factors through the norm map

$$
X_U\longrightarrow
F_+^\times\backslash\mathbf A_{F,f}^\times/\operatorname{Nrd}(U),
$$

with the appropriate archimedean and central identifications.

If a perfect pairing is available over a field, one may define

$$
S^{\mathrm{nonchar}}=(S^{\mathrm{char}})^\perp.
$$

Over an integral ring this orthogonal complement need not split the full module, especially at primes dividing stabilizer or character-group orders. A quotient by the saturated character lattice may be more robust. Accordingly, terms such as “cuspidal quotient” must state whether one means intrinsic parabolic cuspidality, exclusion of norm characters, an orthogonal complement, or a quotient.

### 13.4 What definiteness does and does not say

Definiteness gives:

- compactness modulo center;
- a finite class-set model at fixed level;
- finite stabilizers after quotienting by central units;
- a discrete, algebraic automorphic spectrum.

It does not give:

- absence of one-dimensional representations;
- freeness over every coefficient ring;
- compatibility of invariants with every reduction;
- trivial stabilizers;
- a canonical complement to the character subspace integrally.

The slogan “all forms are cuspidal” is therefore safe only if “cuspidal” means the vacuous vanishing of proper parabolic constant terms. It is unsafe if it is meant to exclude norm characters or to predict the nature of transfer elsewhere.

## 14. The exact finite module

### 14.1 A construction checklist

The whole construction can now be performed without ambiguity.

Start with a totally real field $F$ and a totally definite quaternion algebra $D/F$. Choose a compact open $U\subset D_f^\times$, often the unit group of an Eichler order. Determine the finite class set

$$
X_U=D^\times\backslash D_f^\times/U
$$

and representatives $g_i$. Compute

$$
\Gamma_i=D^\times\cap g_iUg_i^{-1}.
$$

For order level these are the unit groups of the left orders of the associated right ideals.

Next choose weight integers $(n_\tau,m_\tau)$, a field of definition, and a stable coefficient lattice $W_A$. Record the central exponents

$$
c_\tau=n_\tau+2m_\tau.
$$

Choose a central character $\chi$ satisfying

$$
\chi_\infty=\rho|_{Z_\infty}^{-1},
\qquad
\chi_f|_{U\cap Z_f}=1.
$$

Then the exact automorphic module is either the equivariant function space

$$
S(U,W_A,\chi_f)
$$

or, equivalently, the central-character submodule of

$$
\bigoplus_iW_A^{\Gamma_i}.
$$

At coefficient primes not dividing the relevant projective stabilizer and central quotient orders, this module is finite projective, commutes with arbitrary scalar extension, and is free when $A$ is local or a principal ideal domain.

### 14.2 The final dictionary

| Input | Automorphic meaning | Finite model |
|---|---|---|
| totally definite $D/F$ | compact archimedean quotient modulo center | no continuous archimedean variable |
| order $\mathcal O$ | integral structure at finite places | $U=\widehat{\mathcal O}^{\times}$ |
| Eichler level $\mathfrak N$ | prescribed local congruence depth | smaller factors $U_v$ at $v\mid\mathfrak N$ |
| locally principal right ideal $I_i$ | one finite adelic class | representative $g_i$ with $I_i=D\cap g_i\widehat{\mathcal O}$ |
| left order $\mathcal O_L(I_i)$ | automorphisms of that class | $\Gamma_i=\mathcal O_L(I_i)^\times$ |
| archimedean integers $(n_\tau,m_\tau)$ | algebraic weight | $W=\bigotimes_\tau\operatorname{Sym}^{n_\tau}V_\tau\otimes\det^{m_\tau}$ |
| central exponents $c_\tau$ | scalar action and parity | $c_\tau=n_\tau+2m_\tau$ |
| central character $\chi$ | identifies finite and infinite scalar actions | $\chi_\infty=\rho^{-1}$ and $\chi_f|_{U\cap Z_f}=1$ |
| stable lattice $W_A$ | integral coefficient system | invariant summands $W_A^{\Gamma_i}$ |
| class representatives | coordinates for forms | $S(U,W_A)\cong\bigoplus_iW_A^{\Gamma_i}$ |
| deeper level $U'\subset U$ | more finite level structure | pullback and trace along $X_{U'}\to X_U$ |
| invariant weight pairing | duality of coefficient systems | finite sum, optionally weighted by stabilizer masses |
| admissible bases | integral coordinates | block bases of the invariant summands |
| reduced norm | abelian automorphic characters | norm-character subspace |

Every arrow in this table has variance. Right ideals correspond to a left rational quotient and a right level quotient. Their left orders give stabilizers. The weight acts on the left of values, while the archimedean transformation law uses its inverse on the right. Central character factors multiply on the right. These directions are not notational choices that can be changed independently.

### 14.3 Conclusion

Total definiteness turns an adelic automorphic problem into finite algebra because the projective group has no noncompact archimedean direction. The finite adeles retain the arithmetic that matters: compact-open level, right ideal classes, their varying left orders, and the finite stabilizers modulo central units. An algebraic weight places a representation in the fiber above every class, and an automorphic form is exactly a compatible section of those fibers.

The central formula is therefore

$$
S(U,W)\cong
\bigoplus_{[g]\in D^\times\backslash D_f^\times/U}
W^{D^\times\cap gUg^{-1}}.
$$

It contains the whole theory developed here. Trivial weight gives ordinary functions on a finite class set. Nontrivial weight remembers automorphisms of ideal classes. Central characters select eigenspaces for finite central translation, subject to an exact archimedean compatibility law. Stable lattices make the construction integral, while averaging identifies the precise good primes at which projectivity, perfect duality, and reduction behave cleanly. At bad stabilizer primes the failures are meaningful and measurable rather than mysterious.

Change of level, right translation, trace, and finite spans now act on an explicit finite module with admissible coordinates. The analytic features needed for noncompact groups have disappeared, but one-dimensional norm characters have not; separating them prevents compactness from being confused with nonabelian cuspidality. What remains is the exact combinatorial automorphic space promised at the outset: a finite module assembled from orders, ideal classes, algebraic weights, characters, and stabilizer invariants, ready for the systematic study of its finite adelic correspondences.
