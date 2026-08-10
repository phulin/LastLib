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
   - [Translated degeneracy maps](#94-translated-degeneracy-maps)
   - [The standard pair at one new prime](#95-the-standard-pair-at-one-new-prime)
   - [Old images and their integral defects](#96-old-images-and-their-integral-defects)
   - [Adjoints and the preliminary new kernel](#97-adjoints-and-the-preliminary-new-kernel)
   - [The Gram criterion for splitting](#98-the-gram-criterion-for-splitting)
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
   - [A specified arithmetic datum](#142-a-specified-arithmetic-datum)
   - [The base-level module used later](#143-the-base-level-module-used-later)
   - [One-prime level modules](#144-one-prime-level-modules)
   - [Paired and dual modules](#145-paired-and-dual-modules)
   - [The coefficient-change ledger](#146-the-coefficient-change-ledger)
   - [A finite-matrix realization](#147-a-finite-matrix-realization)
   - [Scope boundaries for the next stages](#148-scope-boundaries-for-the-next-stages)
   - [The final dictionary](#149-the-final-dictionary)
   - [Conclusion](#1410-conclusion)

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

More precisely, fix a compact open $U\subset G_f$ and use finiteness of the order class set to choose

$$
G_f=\coprod_{i=1}^hG(F)g_iU.
$$

Let $\overline U$ and $\overline g_i$ denote the images in $PG(\mathbf A_{F,f})$. Every projective adelic class has a representative in one of the sets

$$
\{\overline g_i\}\,\overline U\times PG(F_\infty).
$$

Indeed, lift its finite component to $G_f$, use the displayed decomposition, and remove the rational factor on the left. Now $\overline U$ is compact, while

$$
PG(F_\infty)=\prod_{\tau}D_\tau^\times/\mathbf R^\times
$$

is compact by total definiteness. The quotient is therefore the image of a finite union of compact sets and is compact. This proof gives the exact hypothesis: compactness uses ramification at every real place. Finiteness of the finite class set alone would not control a split archimedean factor.

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

**Proof strategy.** Use the same averaging idempotent before and after scalar extension. Images of idempotents commute with arbitrary base change even when kernels of general maps do not.

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

### 9.4 Translated degeneracy maps

Pullback is only the first way that a lower level can contribute to a deeper one. The second is to change the position of the lower level before forgetting structure. This is the source of the two familiar maps when one prime is newly inserted into the level.

Let $a\in G_f$. Right translation gives

$$
R_a:S(U,W,\chi_f)\xrightarrow{\sim}
S(aUa^{-1},W,\chi_f),
\qquad
(R_af)(g)=f(ga).
$$

The central character is unchanged because $a$ commutes with $Z_f$. If

$$
U'\subseteq aUa^{-1},
$$

we may follow translation by pullback and obtain the **degeneracy map attached to $a$**

$$
\boxed{
\delta_a=
\operatorname{res}_{aUa^{-1}}^{U'}\circ R_a:
S(U,W,\chi_f)\longrightarrow S(U',W,\chi_f).}
$$

The inclusion is the exact well-definedness condition. A vague assertion that $U'$ is deeper than $U$ is not enough: conjugation by $a$ can deepen one matrix entry while making the opposite entry shallower.

The formula is integral. It contains no division by an index or a stabilizer order. On finite class coordinates, if

$$
g_i'a=\gamma_{i,r}g_{j(i,r)}u_{i,r}
$$

for target representatives $g_i'$ and source representatives $g_j$, then the relevant component of $\delta_a$ is obtained from $\rho(\gamma_{i,r})$. A target class may admit several descriptions, but the source stabilizer invariance makes the resulting value independent of all choices. This is the same descent argument as in Theorem 6.1.

Degeneracy maps compose in the expected but order-sensitive way. Suppose

$$
U''\subseteq bU'b^{-1},
\qquad
U'\subseteq aUa^{-1}.
$$

Then $U''\subseteq baU(ba)^{-1}$ and

$$
\delta_b\circ\delta_a=\delta_{ba}.
$$

Indeed, $R_bR_a=R_{ba}$ under our convention, because

$$
(R_bR_af)(g)=f(gba).
$$

This order is easily reversed if right translation is treated as though it were a left action.

### 9.5 The standard pair at one new prime

The local matrix model makes the abstract inclusion concrete. Let $\mathfrak q$ be a finite place at which $D$ is split, choose

$$
D_{\mathfrak q}^{\times}\cong
\operatorname{GL}_2(F_{\mathfrak q}),
$$

and write $\mathcal O_{\mathfrak q}$ for the local integers, $\varpi_{\mathfrak q}$ for a uniformizer, and

$$
K_{\mathfrak q}=\operatorname{GL}_2(\mathcal O_{\mathfrak q}).
$$

The one-step Eichler subgroup is

$$
I_{\mathfrak q}=K_0(\mathfrak q)
=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in K_{\mathfrak q}:c\in\mathfrak q\mathcal O_{\mathfrak q}
\right\}.
$$

Assume that the original level has factor $K_{\mathfrak q}$ and write

$$
U=U^{\mathfrak q}K_{\mathfrak q},
\qquad
U_0(\mathfrak q)=U^{\mathfrak q}I_{\mathfrak q}.
$$

Put

$$
\beta_{\mathfrak q}
=\begin{pmatrix}1&0\\0&\varpi_{\mathfrak q}\end{pmatrix}
$$

at $\mathfrak q$ and $1$ elsewhere. A direct matrix calculation gives

$$
I_{\mathfrak q}\subseteq
\beta_{\mathfrak q}K_{\mathfrak q}\beta_{\mathfrak q}^{-1}.
$$

Indeed,

$$
\beta_{\mathfrak q}
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\beta_{\mathfrak q}^{-1}
=
\begin{pmatrix}
a&\varpi_{\mathfrak q}^{-1}b\\
\varpi_{\mathfrak q}c&d
\end{pmatrix},
$$

so an integral matrix whose lower-left entry is divisible by $\varpi_{\mathfrak q}$ lies in the displayed conjugate. We therefore obtain two maps

$$
\delta_0,\delta_1:
S(U,W,\chi_f)\longrightarrow
S(U_0(\mathfrak q),W,\chi_f),
$$

$$
\delta_0=\operatorname{res}_{U}^{U_0(\mathfrak q)},
\qquad
\delta_1=\delta_{\beta_{\mathfrak q}}.
$$

The diagonal choice matters. If one instead starts from
$\operatorname{diag}(\varpi_{\mathfrak q},1)$, the appropriate map involves the inverse translation or a central multiple, depending on convention. The two descriptions can be reconciled, but their subgroup inclusions cannot be mixed line by line.

This pair is already meaningful without a theory of local eigenvectors. It comes from the two endpoints of the oriented edge fixed by $I_{\mathfrak q}$ in the local lattice tree: one endpoint is remembered by ordinary pullback, the other by translating the hyperspecial vertex before pullback. That geometric picture explains why there are two maps rather than one.

### 9.6 Old images and their integral defects

Let $a_1,\ldots,a_r$ be elements satisfying
$U'\subseteq a_jUa_j^{-1}$. Package the corresponding maps as

$$
\Delta_{U}^{U'}:
S(U,W,\chi_f)^{\oplus r}\longrightarrow
S(U',W,\chi_f),
$$

$$
\Delta_{U}^{U'}(f_1,\ldots,f_r)
=\sum_{j=1}^r\delta_{a_j}f_j.
$$

The **old image contributed by $U$ through this degeneracy family** is

$$
\boxed{
S(U',W,\chi_f)^{\mathrm{old},U}
=\operatorname{im}(\Delta_U^{U'}).}
$$

For the one-prime level $U_0(\mathfrak q)$, the standard family is
$a_1=1$, $a_2=\beta_{\mathfrak q}$. The adjective “old” always depends on a specified collection of lower levels and maps. If several divisors of a level are admitted, the full old image is the sum of their specified degeneracy images.

This definition is robust over an arbitrary coefficient ring, but three stronger statements are not part of it:

1. $\Delta_U^{U'}$ need not be injective;
2. its image need not be a direct summand;
3. over a domain, its image need not be saturated in the target lattice.

The third failure is already visible in the map

$$
A\longrightarrow A,
\qquad x\longmapsto\varpi x,
$$

over a discrete valuation ring. Its image is $\varpi A$, while its generic image is the whole line. The saturation is $A$, and the quotient $A/\varpi A$ measures the lost integral index. Degeneracy images can display exactly this behavior: the generic old subspace may be a direct summand even though its natural integral image sits inside that summand with nonunit index.

It is therefore useful to distinguish

$$
S^{\mathrm{old}}
=\operatorname{im}(\Delta),
$$

$$
S^{\mathrm{old,sat}}
=S(U',W,\chi_f)\cap
\bigl(S^{\mathrm{old}}\otimes_AE\bigr)
$$

when $A$ is a domain with fraction field $E$. Saturating produces a torsion-free quotient but erases the finite quotient
$S^{\mathrm{old,sat}}/S^{\mathrm{old}}$, which can carry precisely the congruence information one wants to retain.

### 9.7 Adjoints and the preliminary new kernel

Old images are defined without a pairing. Newness requires a direction back to lower level, and the trace maps provide it. Suppose $W$ and $W'$ have an invariant perfect pairing, the central characters are inverse, and the mass normalizations of Chapter 10 are in force. Then the adjoint of

$$
\delta_a:
S(U,W,\chi_f)\longrightarrow S(U',W,\chi_f)
$$

is

$$
\boxed{
\delta_a^\dagger
=R_{a^{-1}}\circ
\operatorname{Tr}_{U'}^{aUa^{-1}}.}
$$

The target of the trace is the translated level; the final inverse translation returns to $U$. With one Haar measure fixed simultaneously at both levels, a factor equal to the relevant volume ratio must be inserted. We use $\dagger$ rather than an unqualified star to emphasize that the formula includes the stated pairing and measure normalization.

**Proposition 9.1 (adjoint formula).** Under the hypotheses just stated,

$$
\langle\delta_af,h\rangle_{U'}
=\langle f,\delta_a^\dagger h\rangle_U.
$$

**Proof strategy.** First use adjointness of pullback and trace. Then move the translation from one argument to the other by replacing $a$ with $a^{-1}$.

**Proof.** Write $V=aUa^{-1}$. By definition,
$\delta_a=\operatorname{res}_{V}^{U'}R_a$. Hence

$$
\langle\delta_af,h\rangle_{U'}
=\langle R_af,\operatorname{Tr}_{U'}^Vh\rangle_V.
$$

The invariant weight pairing and inverse central characters give

$$
\langle R_af,k\rangle_V
=\langle f,R_{a^{-1}}k\rangle_U.
$$

Substituting $k=\operatorname{Tr}_{U'}^Vh$ proves the formula. Every sum is finite, so no convergence argument is hidden. $\square$

For the family $a_1,\ldots,a_r$, set

$$
\Delta^\dagger h
=\bigl(\delta_{a_1}^\dagger h,\ldots,
\delta_{a_r}^\dagger h\bigr).
$$

The **preliminary new kernel relative to this family** is

$$
\boxed{
S(U',W',\chi_f^{-1})^{\mathrm{new},U}_{\ker}
=\ker(\Delta^\dagger)
=\bigcap_{j=1}^r\ker(\delta_{a_j}^\dagger).}
$$

When source and target coefficient systems have been identified self-dually, this is a submodule of the same form space. Under perfectness it is exactly the orthogonal complement of the old image:

$$
\ker(\Delta^\dagger)
=(\operatorname{im}\Delta)^\perp.
$$

Without perfectness, the two definitions can differ: orthogonality says only that $\Delta^\dagger h$ lies in the radical of the lower-level pairing. This is why an integral “new submodule” must record its pairing and its adjoint maps rather than being introduced as an unexplained orthogonal complement.

### 9.8 The Gram criterion for splitting

The old and new modules need not form a direct sum. The obstruction can be concentrated in one finite map. Assume now that all relevant modules are finite projective over $A$, that the pairings are perfect, and that chosen self-dual identifications carry the inverse-character partner back to the original coefficient system. Only under this last hypothesis is the adjoint a map between the same named modules. Define the **degeneracy Gram operator**

$$
\mathcal G=\Delta^\dagger\Delta
\in\operatorname{End}_A\bigl(S(U,W,\chi_f)^{\oplus r}\bigr).
$$

Its $(i,j)$ entry is

$$
\delta_{a_i}^\dagger\delta_{a_j},
$$

an explicit finite correspondence at the lower level. In the two-map case,

$$
\mathcal G=
\begin{pmatrix}
\delta_0^\dagger\delta_0&
\delta_0^\dagger\delta_1\\
\delta_1^\dagger\delta_0&
\delta_1^\dagger\delta_1
\end{pmatrix}.
$$

The diagonal entries measure the indices of the two forgetful maps; the off-diagonal entries are the finite correspondences connecting the two endpoints. Their more familiar names and local relations belong to the systematic operator theory that follows this book.

**Theorem 9.2 (old--new splitting criterion).** If $\mathcal G$ is an automorphism, then

$$
S(U',W,\chi_f)
=\operatorname{im}(\Delta)
\oplus\ker(\Delta^\dagger),
$$

after making the stated self-dual identifications. The projector onto the old summand is

$$
e_{\mathrm{old}}
=\Delta\mathcal G^{-1}\Delta^\dagger.
$$

**Proof strategy.** The inverse Gram operator constructs a left inverse to $\Delta$ and an idempotent on the target. Its kernel is forced to be the common adjoint kernel.

**Proof.** Since

$$
\mathcal G^{-1}\Delta^\dagger\Delta=1,
$$

the map $\Delta$ is split injective. Moreover,

$$
e_{\mathrm{old}}^2
=\Delta\mathcal G^{-1}
(\Delta^\dagger\Delta)
\mathcal G^{-1}\Delta^\dagger
=e_{\mathrm{old}}.
$$

Its image is $\operatorname{im}(\Delta)$. If $\Delta^\dagger h=0$, then $e_{\mathrm{old}}h=0$. Conversely, if $e_{\mathrm{old}}h=0$, apply $\Delta^\dagger$ and use

$$
\Delta^\dagger e_{\mathrm{old}}
=\mathcal G\mathcal G^{-1}\Delta^\dagger
=\Delta^\dagger
$$

to obtain $\Delta^\dagger h=0$. Thus the kernel of the idempotent is the new kernel, proving the direct sum. $\square$

If $\mathcal G$ becomes invertible only after passing to a fraction field, the same decomposition holds generically but need not hold integrally. Denominators in $\mathcal G^{-1}$ measure the failure of the old lattice to split. If $\mathcal G$ is singular even generically, the chosen degeneracy maps are dependent on some characteristic-zero constituents. These three cases—unit determinant, nonzero nonunit determinant, and zero determinant—must not be conflated.

This is the appropriate endpoint here. Old images, adjoint traces, new kernels, and the exact splitting criterion are defined. Identifying the entries of $\mathcal G$, proving local relations, and deciding when it is invertible require the next layer of the theory.

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

We stop before naming or organizing the general fixed-level double-coset endomorphisms. Chapter 9 named the particular level-changing maps needed to define old images and adjoint new kernels, but it did not identify the fixed-level entries of their Gram operators. The systematic theory requires local double-coset algebras, convolution normalizations, relations at unramified and level places, commutativity statements, and compatibility among many choices. Those belong to the next book.

The present preparation is exact but deliberately elementary:

- right translation changes level by $U\mapsto aUa^{-1}$;
- intersections provide a common deeper level;
- pullback and trace turn a finite span into a linear map;
- an admissible basis makes that map a finite matrix.

No eigenform, eigenvalue system, or operator algebra is needed to define the module on which those later objects act.

## 13. Cuspidality in the anisotropic setting

### 13.1 No rational parabolics and no continuous spectrum

Constant terms in the usual automorphic theory are integrals along unipotent radicals of proper rational parabolic subgroups. For $G=D^\times$ with $D$ a division algebra, there is no proper rational parabolic subgroup. Equivalently, $PG$ is anisotropic over $F$.

In degree two this can be seen without a classification theorem. A proper parabolic after passing to a splitting field stabilizes a line in the two-dimensional simple module. If such a subgroup were defined over $F$, the corresponding projective homogeneous space would have an $F$-rational point. That point is the same as a nonzero proper right ideal of $D$, or equivalently a nontrivial idempotent in $D$. A division algebra has neither. Thus the only $F$-parabolic is the whole group.

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

### 14.2 A specified arithmetic datum

Later arguments must be able to refer to one module without silently changing its normalization. The minimum reusable datum is the following collection.

- $F$ is a totally real number field with ring of integers $R$.
- $D/F$ is a totally definite quaternion algebra, with finite ramification ideal $\mathfrak d$.
- $U=\prod_{v<\infty}U_v\subset D_f^\times$ is a compact open subgroup.
- $E$ is a characteristic-zero coefficient field, $A\subset E$ is a chosen coefficient ring, and $W_A$ is a finite projective stable weight lattice.
- $\chi_f:Z_f\to A^\times$ is the finite part of a compatible central character.
- $\Sigma$ is a finite set of finite places containing every place at which $D$ is ramified, $U_v$ is not maximal hyperspecial, $W_A$ or $\chi_f$ is ramified, or the chosen coefficient theory requires exclusion.

The set $\Sigma$ does not alter the form space. It records which local places will later be omitted from a uniform family of finite correspondences. Including it now prevents two common ambiguities: changing the module when only the operator family was meant to change, and comparing modules with different central or lattice ramification under the same notation.

For order level, one may specify an Eichler order $\mathcal O$ of level $\mathfrak N$ prime to $\mathfrak d$ and take

$$
U=\widehat{\mathcal O}^{\times}.
$$

Then $\Sigma$ contains the places dividing $\mathfrak d\mathfrak N$ and the coefficient place. At a finite place outside $\Sigma$, a chosen splitting identifies

$$
D_v^\times\cong\operatorname{GL}_2(F_v),
\qquad
U_v\cong\operatorname{GL}_2(R_v).
$$

The splitting is auxiliary. Replacing it conjugates the local compact subgroup and transports every finite correspondence, leaving the global module canonically isomorphic.

The weight datum is not merely the tuple $(k_\tau)$. It consists of integers

$$
n_\tau=k_\tau-2\ge0,
\qquad m_\tau\in\mathbf Z,
$$

a field of definition for

$$
W_E=\bigotimes_\tau
\operatorname{Sym}^{n_\tau}V_\tau\otimes\det^{m_\tau},
$$

and the actual lattice $W_A\subset W_E$. Two commensurable lattices give the same generic space but may give different reductions. Likewise, a central character is part of the datum, not a decoration attached after the space has been formed.

### 14.3 The base-level module used later

For the specified datum, write

$$
\boxed{
M_A(U;W,\chi)
=S(U,W_A,\chi_f).}
$$

This is the finite integral carrier for the Hecke action constructed in the next stage. Once a specified family of finite double-coset correspondences is allowed to act, it is the corresponding finite Hecke module; the underlying module and lattice do not change when that operator family is named.

Explicitly,

$$
M_A(U;W,\chi)
=\left\{
f:D_f^\times\to W_A:
f(\gamma guz)=\rho(\gamma)\chi_f(z)f(g)
\right\},
$$

where $\gamma\in D^\times$, $u\in U$, and $z\in Z_f$. The definition presupposes

$$
\chi_f(a)=\rho(a_\infty)quad(a\in F^\times),
\qquad
\chi_f|_{U\cap Z_f}=1.
$$

These two equations are not later lemmas: they are the descent conditions that make the displayed transformation law consistent.

Choose representatives $g_1,\ldots,g_h$ for $X_U$. Then $M_A(U;W,\chi)$ is the submodule of

$$
\bigoplus_{i=1}^hW_A^{\Gamma_i},
\qquad
\Gamma_i=D^\times\cap g_iUg_i^{-1},
$$

cut out by the finitely many central equations of Section 6.4. This is the **exact finite model**. In particular, it is not the whole direct sum unless no central character has been imposed or the relevant eigenspace conditions are automatic.

When $A$ is a discrete valuation ring and $W_A$ is finite free, the module $M_A(U;W,\chi)$ is finite free. To see this without averaging, realize every stabilizer invariant and every central equation as the kernel of a map between finite free modules. The resulting module is a finite torsion-free $A$-module and hence free. This statement does not imply clean reduction: a kernel can be free and still acquire extra solutions after reducing its defining equations.

For the algebraic weight-two normalization,

$$
n_\tau=m_\tau=0
\quad\text{for all }\tau,
$$

and with trivial central character,

$$
M_A(U;2,1)=\operatorname{Map}(X_U,A).
$$

This scalar module is often the cleanest arithmetic lattice. If norm characters must be excluded, one must separately specify the character submodule, its saturation, and whether the object retained is a quotient or an orthogonal complement. The bare notation $M_A(U;2,1)$ includes those characters.

### 14.4 One-prime level modules

The base module is accompanied by two standard refinements at a split place $\mathfrak q\notin\Sigma$. Keep the notation of Section 9.5. Besides
$I_{\mathfrak q}=K_0(\mathfrak q)$, define

$$
K_1(\mathfrak q)
=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}
\in K_0(\mathfrak q):
d\equiv1\pmod{\mathfrak q}
\right\}.
$$

Reduction of the lower-right entry gives an exact sequence

$$
1\longrightarrow K_1(\mathfrak q)
\longrightarrow K_0(\mathfrak q)
\longrightarrow k_{\mathfrak q}^{\times}
\longrightarrow1.
$$

The map is multiplicative because lower-left entries vanish modulo $\mathfrak q$. Its kernel is exactly $K_1(\mathfrak q)$, and diagonal matrices show surjectivity.

Define global levels

$$
U_0(\mathfrak q)=U^{\mathfrak q}K_0(\mathfrak q),
\qquad
U_1(\mathfrak q)=U^{\mathfrak q}K_1(\mathfrak q),
$$

and finite modules

$$
M_{0,A}(\mathfrak q)
=M_A(U_0(\mathfrak q);W,\chi),
$$

$$
M_{1,A}(\mathfrak q)
=M_A(U_1(\mathfrak q);W,\chi).
$$

The same central character can be used because its triviality on $U\cap Z_f$ implies triviality on the smaller central intersections. Conversely, a central character ramified through
$R_{\mathfrak q}^\times/(1+\mathfrak qR_{\mathfrak q})$ can be compatible with $U_1(\mathfrak q)$ even when it is incompatible with the larger level, because a scalar matrix lies in $K_1(\mathfrak q)$ only when its residue is $1$. Such a character must be inserted into the datum explicitly. A character of the noncentral diamond quotient is instead selected as an eigenspace for the action described next.

Since $U_1(\mathfrak q)$ is normal in $U_0(\mathfrak q)$, the quotient
$k_{\mathfrak q}^{\times}$ acts on $M_{1,A}(\mathfrak q)$ by right translation. These are the **diamond translations** at $\mathfrak q$. Pullback identifies

$$
\boxed{
M_{0,A}(\mathfrak q)
=M_{1,A}(\mathfrak q)^{k_{\mathfrak q}^{\times}}.}
$$

This equality is an equality of invariant submodules, with no need to divide by
$|k_{\mathfrak q}^{\times}|$. If that order is invertible in $A$ and $A$ contains the values of the relevant characters, averaging gives a direct decomposition into diamond-character summands. If the order is not invertible, the invariant equality remains true but a character decomposition may fail after reduction.

The two standard degeneracy maps assemble as

$$
\Delta_{\mathfrak q}:
M_A(U;W,\chi)^{\oplus2}
\longrightarrow M_{0,A}(\mathfrak q),
$$

$$
\Delta_{\mathfrak q}(x,y)
=\delta_0x+\delta_1y.
$$

Thus the base module, the one-prime $K_0$ module, the $K_1$ module with its finite diamond action, and the integral degeneracy map are all defined before any eigenvalue or local newvector is mentioned. This is the finite package needed for later level comparison.

### 14.5 Paired and dual modules

Let

$$
W_A^\vee=\operatorname{Hom}_A(W_A,A)
$$

with contragredient action, and use the inverse central character $\chi_f^{-1}$. The natural partner of $M_A(U;W,\chi)$ is

$$
M_A^\vee(U)
=M_A(U;W^\vee,\chi^{-1}).
$$

Evaluation on the weight fibers gives the finite-sum pairing

$$
M_A(U;W,\chi)\times M_A^\vee(U)
\longrightarrow A.
$$

At good stabilizer and central-character primes it is perfect. Equivalently, the natural map

$$
M_A^\vee(U)
\longrightarrow
\operatorname{Hom}_A(M_A(U;W,\chi),A)
$$

is an isomorphism. At a bad stabilizer prime it need not be: the right-hand side is always the abstract dual of the finite free module, while the left-hand side is formed by taking invariants in the dual coefficient system. Those operations can disagree under reduction.

The mass pairing is obtained from the same fiberwise evaluation by inserting reciprocal effective stabilizer orders. It is the correct pairing for unscaled adjoint formulas once quotient measures are normalized as in Section 10.3. The finite-sum pairing is the safer integral lattice when those orders are not units. A later assertion that a correspondence is self-adjoint must therefore state which pairing is used and whether the coefficient system has been identified with its dual.

At the one-prime level, the adjoint of $\Delta_{\mathfrak q}$ is

$$
\Delta_{\mathfrak q}^\dagger:
M_{0,A}^\vee(\mathfrak q)
\longrightarrow M_A^\vee(U)^{\oplus2},
$$

and the relative new kernel is $\ker(\Delta_{\mathfrak q}^\dagger)$. This is an exact finite submodule. Calling it a direct complement to the old image requires the Gram criterion of Theorem 9.2.

### 14.6 The coefficient-change ledger

Let $A$ be a discrete valuation ring with fraction field $E$, uniformizer $\varpi$, and residue field $k$. Three modules must be kept distinct:

$$
M_A=M_A(U;W,\chi),
$$

$$
M_E^{\mathrm{lat}}=M_A\otimes_AE,
$$

$$
\overline M_A=M_A/\varpi M_A.
$$

Because $E$ is flat over $A$, the generic module agrees with the form space formed directly over $E$:

$$
M_E^{\mathrm{lat}}
\xrightarrow{\sim}
M_E(U;W_E,\chi_E).
$$

There is also a natural injection

$$
\overline M_A
\hookrightarrow
M_k(U;W_A/\varpi W_A,\overline\chi).
$$

Injectivity follows from saturation of the simultaneous kernel defining $M_A$. Surjectivity is the subtle point: the module formed directly over $k$ can contain new stabilizer invariants or new solutions of central-character equations. At good stabilizer and central quotient primes, averaging proves that the injection is an isomorphism.

Consequently a phrase such as “the residual automorphic module” is ambiguous unless one specifies which of the following is meant:

- reduction $\overline M_A$ of the chosen integral lattice;
- the directly formed module $M_k$;
- the image of $\overline M_A$ inside $M_k$ when base change fails.

The same ledger applies to $M_{0,A}(\mathfrak q)$ and
$M_{1,A}(\mathfrak q)$. Even if the base-level module reduces cleanly, a newly introduced diamond group can have order divisible by the residue characteristic, so its character summands may not. Clean coefficient change must be checked at every level actually used.

For a localization $A_{\mathfrak p}$ of a number ring, flatness gives

$$
M_A(U;W,\chi)\otimes_AA_{\mathfrak p}
\cong M_{A_{\mathfrak p}}(U;W_{A_{\mathfrak p}},\chi).
$$

This makes localization harmless at the level of the finite form module. Reduction after localization remains nonflat and returns to the preceding distinction.

### 14.7 A finite-matrix realization

For actual comparison, the preceding objects can be stored as a finite collection of matrices. The construction is mathematical, not dependent on any special presentation.

1. Choose class representatives $g_i$ and determine their stabilizers $\Gamma_i$.
2. Compute bases, or projective decompositions, of $W_A^{\Gamma_i}$.
3. Impose the finite central equations and choose a basis of the resulting module when it is free.
4. At a deeper level repeat the process with representatives $g_j'$ and stabilizers $\Gamma_j'$.
5. Rewrite every translated point $g_j'a$ as $\gamma g_i u$; insert the weight matrix $\rho(\gamma)$ in the corresponding block.
6. Sum repeated contributions with their multiplicities. Do not replace them by set-theoretic fiber counts when stabilizers are present.

The output for one-prime change of level is a pair of matrices

$$
[\delta_0],\ [\delta_1],
$$

their combined matrix $[\Delta_{\mathfrak q}]$, and, when perfect pairings are fixed, the adjoint and Gram matrices

$$
[\Delta_{\mathfrak q}^\dagger],
\qquad
[\mathcal G_{\mathfrak q}]
=[\Delta_{\mathfrak q}^\dagger]
[\Delta_{\mathfrak q}].
$$

Changing class representatives conjugates these matrices by block changes of coordinates; changing bases conjugates them in the usual linear-algebraic sense. Ranks, kernels, images, cokernels, saturation indices, and the invertibility of the Gram operator are intrinsic.

For trivial weight the entries of the translation matrices are nonnegative integers counting finite incidences with stabilizer multiplicity. For nontrivial weight the integer counts are replaced by sums of weight transformations. This is the precise sense in which the later modules are finite: every map is a finite matrix between explicitly described finite coefficient modules.

### 14.8 Scope boundaries for the next stages

The finite modules are now completely defined, including the level maps needed to speak safely about old and new parts. Several stronger structures have intentionally not been smuggled into the definitions.

- No commutative operator algebra has yet been selected.
- No local double-coset relation or polynomial normalization has been imposed.
- No assertion of simultaneous diagonalizability or multiplicity one has been made.
- No old/new direct sum is claimed unless the Gram operator is invertible.
- No direct residual module is identified with reduction without a base-change theorem.
- No norm-character quotient is called cuspidal without specifying the quotient or complement.

These are not gaps in the finite construction. They separate the stable input from the theorems that later act on it. The durable object is the module

$$
M_A(U;W,\chi),
$$

together with its class-set decomposition, central constraints, integral pairing, prescribed deeper-level companions, diamond translations, and degeneracy maps.

### 14.9 The final dictionary

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
| admissible $a$ with $U'\subset aUa^{-1}$ | translated lower-level contribution | degeneracy map $\delta_a$ |
| family of degeneracy maps | old contribution from specified lower levels | image of $\Delta$ |
| adjoint traces | vanishing back at lower level | preliminary new kernel $\ker(\Delta^\dagger)$ |
| degeneracy Gram operator | obstruction to integral splitting | $\mathcal G=\Delta^\dagger\Delta$ |
| $U_1(\mathfrak q)\triangleleft U_0(\mathfrak q)$ | one-prime character level | action of $k_{\mathfrak q}^\times$ by diamond translations |
| invariant weight pairing | duality of coefficient systems | finite sum, optionally weighted by stabilizer masses |
| admissible bases | integral coordinates | block bases of the invariant summands |
| reduced norm | abelian automorphic characters | norm-character subspace |

Every arrow in this table has variance. Right ideals correspond to a left rational quotient and a right level quotient. Their left orders give stabilizers. The weight acts on the left of values, while the archimedean transformation law uses its inverse on the right. Central character factors multiply on the right. These directions are not notational choices that can be changed independently.

### 14.10 Conclusion

Total definiteness turns an adelic automorphic problem into finite algebra because the projective group has no noncompact archimedean direction. The finite adeles retain the arithmetic that matters: compact-open level, right ideal classes, their varying left orders, and the finite stabilizers modulo central units. An algebraic weight places a representation in the fiber above every class, and an automorphic form is exactly a compatible section of those fibers.

The central formula is therefore

$$
S(U,W)\cong
\bigoplus_{[g]\in D^\times\backslash D_f^\times/U}
W^{D^\times\cap gUg^{-1}}.
$$

It contains the whole theory developed here. Trivial weight gives ordinary functions on a finite class set. Nontrivial weight remembers automorphisms of ideal classes. Central characters select eigenspaces for finite central translation, subject to an exact archimedean compatibility law. Stable lattices make the construction integral, while averaging identifies the precise good primes at which projectivity, perfect duality, and reduction behave cleanly. At bad stabilizer primes the failures are meaningful and measurable rather than mysterious.

Change of level, right translation, trace, and finite spans now act on an explicit finite module with admissible coordinates. The analytic features needed for noncompact groups have disappeared, but one-dimensional norm characters have not; separating them prevents compactness from being confused with nonabelian cuspidality. What remains is the exact combinatorial automorphic space promised at the outset: a finite module assembled from orders, ideal classes, algebraic weights, characters, and stabilizer invariants, ready for the systematic study of its finite adelic correspondences.
