# Completed Hecke Pieces and Eisenstein $p$-divisible Groups

## Contents

1. [The passage from finite Eisenstein data to an infinite torsion object](#1-the-passage-from-finite-eisenstein-data-to-an-infinite-torsion-object)
   - [The problem](#11-the-problem)
   - [Prime-level notation](#12-prime-level-notation)
   - [What will be constructed](#13-what-will-be-constructed)
2. [Finite Hecke algebras and their local idempotents](#2-finite-hecke-algebras-and-their-local-idempotents)
   - [The acting algebra](#21-the-acting-algebra)
   - [The semilocal decomposition](#22-the-semilocal-decomposition)
   - [Lifting idempotents](#23-lifting-idempotents)
   - [Rational support and integral completion](#24-rational-support-and-integral-completion)
   - [Why the two projectors cannot be identified](#25-why-the-two-projectors-cannot-be-identified)
3. [The selected Eisenstein quotient](#3-the-selected-eisenstein-quotient)
   - [Optimal quotients attached to rational support](#31-optimal-quotients-attached-to-rational-support)
   - [Independence of denominators](#32-independence-of-denominators)
   - [The Neron model](#33-the-neron-model)
   - [Good reduction away from the level](#34-good-reduction-away-from-the-level)
   - [What extends over the good-reduction base](#35-what-extends-over-the-good-reduction-base)
   - [Saturation of the selected Tate lattice](#36-saturation-of-the-selected-tate-lattice)
4. [The two completed Hecke towers](#4-the-two-completed-hecke-towers)
   - [Two finite-level projectors](#41-two-finite-level-projectors)
   - [Exact transition maps in both towers](#42-exact-transition-maps-in-both-towers)
   - [The resulting divisible groups](#43-the-resulting-divisible-groups)
   - [Comparison maps at every torsion power](#44-comparison-maps-at-every-torsion-power)
   - [The exact scope of the comparison](#45-the-exact-scope-of-the-comparison)
5. [Faithful completed Hecke action](#5-faithful-completed-hecke-action)
   - [Endomorphisms detected on torsion](#51-endomorphisms-detected-on-torsion)
   - [Faithfulness of the local factor](#52-faithfulness-of-the-local-factor)
   - [What faithfulness does not say](#53-what-faithfulness-does-not-say)
6. [The Eisenstein residual shape](#6-the-eisenstein-residual-shape)
   - [The two characters](#61-the-two-characters)
   - [The Hecke-radical filtration](#62-the-hecke-radical-filtration)
   - [A quadratic-density lemma](#63-a-quadratic-density-lemma)
   - [The Eisenstein selection theorem](#64-the-eisenstein-selection-theorem)
   - [Stable filtrations at every finite level](#65-stable-filtrations-at-every-finite-level)
   - [Why Carayol descent is not the missing argument](#66-why-carayol-descent-is-not-the-missing-argument)
   - [Why traces alone are insufficient](#67-why-traces-alone-are-insufficient)
7. [Integral admissibility](#7-integral-admissibility)
   - [Closing the generic filtration](#71-closing-the-generic-filtration)
   - [Odd Eisenstein primes](#72-odd-eisenstein-primes)
   - [Order-two groups over the unramified base](#73-order-two-groups-over-the-unramified-base)
   - [Dyadic admissibility](#74-dyadic-admissibility)
   - [Compatibility with transition maps](#75-compatibility-with-transition-maps)
8. [Connected, etale, and multiplicative parts](#8-connected-etale-and-multiplicative-parts)
   - [The local connected--etale sequence](#81-the-local-connected--etale-sequence)
   - [Recognition of the multiplicative part](#82-recognition-of-the-multiplicative-part)
   - [The Eisenstein exact sequence](#83-the-eisenstein-exact-sequence)
   - [Finite levels and heights](#84-finite-levels-and-heights)
   - [Integral recovery of the quotient tower](#85-integral-recovery-of-the-quotient-tower)
   - [Ordinary structure without a chosen splitting](#86-ordinary-structure-without-a-chosen-splitting)
9. [Cuspidal and Shimura constituents](#9-cuspidal-and-shimura-constituents)
   - [The two canonical cyclic groups](#91-the-two-canonical-cyclic-groups)
   - [Their closures in the completed piece](#92-their-closures-in-the-completed-piece)
   - [Atomic mixed extensions](#93-atomic-mixed-extensions)
   - [What is and is not canonical](#94-what-is-and-is-not-canonical)
10. [Hecke control at finite level](#10-hecke-control-at-finite-level)
    - [The completed Eisenstein ideal](#101-the-completed-eisenstein-ideal)
    - [Control modulo powers](#102-control-modulo-powers)
    - [Annihilators and faithful quotients](#103-annihilators-and-faithful-quotients)
    - [Base change and duality](#104-base-change-and-duality)
11. [Exceptional levels and exceptional primes](#11-exceptional-levels-and-exceptional-primes)
    - [The level prime](#111-the-level-prime)
    - [Trivial Eisenstein index](#112-trivial-eisenstein-index)
    - [The prime three](#113-the-prime-three)
    - [The prime two](#114-the-prime-two)
12. [The completed Eisenstein package](#12-the-completed-eisenstein-package)
    - [Main theorem](#121-main-theorem)
    - [Dependency ledger](#122-dependency-ledger)
    - [Conclusion](#123-conclusion)

## 1. The passage from finite Eisenstein data to an infinite torsion object

### 1.1 The problem

At prime level there are two visibly Eisenstein finite subgroups of the modular Jacobian. The difference of the two cusps generates a constant cyclic group, while the kernel of pullback from $X_0(N)$ to $X_1(N)$ supplies a cyclic group of multiplicative type. Both have the same order

$$
n_N=\operatorname{num}\left(\frac{N-1}{12}\right)
=\frac{N-1}{\gcd(N-1,12)},
$$

and both are annihilated by the Eisenstein ideal. These facts are powerful but finite. Descent requires an object containing compatible torsion at every power of an Eisenstein prime. Three difficulties intervene.

First, localization is an algebraic operation, whereas torsion consists of group schemes. The expression “the localization of $J[\ell^r]$” has no meaning until an actual integral projector has been constructed. Second, the kernel of a Hecke operator on a Neron model need not be finite flat. A generic kernel may acquire vertical components, and a quasi-finite kernel on a Neron model need not be finite. Third, a tower of finite flat groups killed by $\ell^r$ is not automatically an $\ell$-divisible group. The multiplication maps must be faithfully flat with exactly the prescribed kernels.

The correct order of work is therefore

$$
\text{local idempotent}
\Longrightarrow
\text{direct summands of abelian-scheme torsion}
\Longrightarrow
\text{exact compatible towers}
\Longrightarrow
\ell\text{-divisible groups}.
$$

Direct summands, rather than arbitrary kernels, are decisive. An idempotent splits every ambient finite-flat torsion group as a product. Flatness, quotient representability, and compatibility then follow formally from the ambient abelian scheme. There are, however, two ambient abelian schemes: the modular Jacobian and the selected optimal quotient. Their local summands have the same generic Tate lattice, but equality of generic lattices does not by itself identify their finite-flat models at the prime $\ell$. We shall retain both towers and compare them by actual morphisms at every level.

### 1.2 Prime-level notation

Let $N$ be prime and put

$$
S=\operatorname{Spec}\mathbf Z[1/N].
$$

Write $J=J_0(N)$ and let $\mathcal J/S$ be the restriction of its Neron model to $S$. The prime-level curve has good reduction at every prime different from $N$, so $\mathcal J$ is an abelian scheme over $S$.

Let $\mathbb T$ be the faithful commutative Hecke algebra acting on $J$, generated by $T_q$ for primes $q\ne N$ and by $U_N$. Its Eisenstein ideal is

$$
I=(T_q-(1+q):q\ne N)+(U_N-1).
$$

The exact index theorem gives

$$
\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z. \tag{1.1}
$$

Fix a prime $\ell\mid n_N$ and the Eisenstein maximal ideal

$$
\mathfrak m=(\ell,I).
$$

In particular $\ell\mid N-1$, so $\ell\ne N$. Put

$$
d=v_\ell(n_N).
$$

We reserve $q$ for primes away from $N\ell$. This separation of the level prime $N$, the Eisenstein prime $\ell$, and an auxiliary good prime $q$ prevents several common normalization errors.

### 1.3 What will be constructed

There are three related objects, two of them integral.

The first is the **selected Eisenstein quotient** $A_{\mathfrak m}$ of $J$: it is the optimal abelian quotient supported on precisely those characteristic-zero Hecke factors whose integral closures have a prime above $\mathfrak m$. This quotient is canonical as an optimal quotient. A denominator used to write its rational support need not be prime to $\ell$; independence comes from equality of connected kernels, not from cancelling that denominator.

The quotient carries its own **completed Hecke piece**

$$
G_{\mathfrak m}
=e_{\mathfrak m}\mathcal A_{\mathfrak m}[\ell^\infty].
$$

Here $e_{\mathfrak m}$ is the local idempotent in $\mathbb T\otimes\mathbf Z_\ell$. This is the tower used for descent on $A_{\mathfrak m}$: its level $G_r$ is exactly the coefficient group scheme in the Kummer sequence for multiplication by $\ell^r$ on the selected quotient.

There is also the **ambient Jacobian piece**

$$
P_{\mathfrak m}=e_{\mathfrak m}\mathcal J[\ell^\infty].
$$

Both are $\ell$-divisible groups over $S$ with faithful $\mathbb T_{\mathfrak m}$-action and finite-flat levels. The principal polarization makes $P_{\mathfrak m}$ integrally self-dual. Initially the quotient map gives a quasi-isogeny $P_{\mathfrak m}\dashrightarrow G_{\mathfrak m}$ and an isomorphism of their generic Tate lattices. A denominator in the rational projector can have positive $\ell$-adic valuation, so generic saturation alone cannot identify isolated finite-flat levels. After admissibility proves that both compatible towers are ordinary, their canonical endpoint sequences supply the missing integral rigidity and upgrade the comparison to an isomorphism at every level.

The quotient tower $G_{\mathfrak m}$ is the completed object needed in descent. The ambient tower $P_{\mathfrak m}$ supplies a canonical integral polarization and a useful comparison object. Keeping them separate during the construction avoids a false single-level argument; proving that they eventually agree is a theorem, not a definition.

## 2. Finite Hecke algebras and their local idempotents

Localization becomes geometric only after it is represented by an idempotent that acts on integral torsion. This chapter constructs that idempotent and, just as importantly, separates it from the rational projector used to construct an abelian quotient. The two projectors remember different equivalence relations: rational support groups together coefficient conjugates, while the $\ell$-adic projector distinguishes primes above $\ell$.

### 2.1 The acting algebra

Because $\mathbb T$ is the image of the abstract correspondences on a finite free integral lattice of differentials, it is a finite torsion-free $\mathbf Z$-algebra. The Rosati involution attached to the canonical principal polarization fixes every good Hecke operator. At prime level the acting-image identity is $U_N=-w_N$ on weight-two cusp forms. The Atkin--Lehner involution is induced by an involution of the curve, so its Rosati adjoint is its inverse, hence itself. Thus $U_N$ is self-adjoint as well, and Rosati fixes every element of the commutative algebra generated by these operators. The positivity of Rosati is important here: on rational homology it makes every such element self-adjoint for a positive-definite form, and therefore diagonalizable after extending scalars to $\mathbf R$. A nilpotent element is consequently zero. Thus the rational algebra

$$
\mathbb T_{\mathbf Q}=\mathbb T\otimes\mathbf Q
$$

is reduced. Being finite, commutative, and reduced over $\mathbf Q$, it is a product of number fields. Mere invariance under an arbitrary involution would not prove this conclusion; it is the positive Rosati form that rules out nilpotent self-adjoint operators.

This semisimplicity is used only on the rational side. Integrally, $\mathbb T\otimes\mathbf Z_\ell$ can have ramification and nonreduced special fiber. We shall never replace it by the product of its residue fields.

### 2.2 The semilocal decomposition

Set

$$
\mathbb T_\ell=\mathbb T\otimes\mathbf Z_\ell.
$$

It is finite free over the complete DVR $\mathbf Z_\ell$, hence complete for its Jacobson radical. Its maximal ideals are precisely the ideals of $\mathbb T$ above $\ell$. The Chinese remainder theorem at each Artinian level gives

$$
\mathbb T_\ell/\ell^r\mathbb T_\ell
\simeq
\prod_{\mathfrak n\mid\ell}
(\mathbb T_\ell/\ell^r\mathbb T_\ell)_{\mathfrak n}.
$$

Passing to the inverse limit yields a product of complete local rings

$$
\mathbb T_\ell\simeq
\prod_{\mathfrak n\mid\ell}\mathbb T_{\mathfrak n}. \tag{2.1}
$$

Here $\mathbb T_{\mathfrak n}$ denotes completion, or equivalently the corresponding local factor of $\mathbb T_\ell$. Equation (2.1), not a localization symbol applied to a group scheme, is the source of the geometric projector.

### 2.3 Lifting idempotents

For each $\mathfrak n\mid\ell$, let $\bar e_{\mathfrak n}$ be the coordinate idempotent of the product modulo the Jacobson radical. Idempotents lift uniquely through nilpotent ideals. Indeed, if $a^2-a$ lies in a nilpotent ideal, successive correction by

$$
a\longmapsto a-(a^2-a)(2a-1)^{-1}
$$

raises the order of the error, because $(2a-1)^2=1+4(a^2-a)$ is a unit. Completeness gives a limiting idempotent. Uniqueness follows because two congruent idempotents $e,f$ satisfy

$$
(e-f)(e+f-1)=0,
$$

while $e+f-1$ is a unit when $e-f$ is in the Jacobson radical. Multiplication by its inverse gives $e=f$.

Thus (2.1) supplies pairwise orthogonal idempotents $e_{\mathfrak n}$ with sum $1$. We fix

$$
e=e_{\mathfrak m}.
$$

The image $e\mathbb T_\ell$ is $\mathbb T_{\mathfrak m}$, and $(1-e)\mathbb T_\ell$ is the product of the other local factors.

### 2.4 Rational support and integral completion

After tensoring (2.1) with $\mathbf Q_\ell$, the idempotent $e$ becomes a sum of primitive idempotents in the product of the $\ell$-adic completions of the number fields in $\mathbb T_{\mathbf Q}$. There is a subtle descent issue. One rational number-field factor can have several primes above $\ell$, only one of which belongs to $e$. A rational abelian quotient cannot retain one completion of that field and discard another.

Let $E$ be the sum of the rational primitive idempotents whose scalar extension has at least one summand in $e$. Then

$$
E\in\mathbb T_{\mathbf Q},
\qquad eE=e,
$$

but $E\otimes1$ can be strictly larger than $e$. Choose any positive integer $M$ such that

$$
u=ME\in\mathbb T.
$$

No claim is made that $M$ is prime to $\ell$. The rational projector constructs an abelian quotient containing all coefficient conjugates forced by rationality; the integral idempotent subsequently extracts its precise $\mathfrak m$-adic summand. Keeping these two operations separate is essential.

### 2.5 Why the two projectors cannot be identified

The distinction in the preceding section is not a technical nuisance. It is forced by scalar descent. Suppose a field factor $K$ of $\mathbb T_{\mathbf Q}$ has two primes $\lambda_1$ and $\lambda_2$ above $\ell$. Then

$$
K\otimes_{\mathbf Q}\mathbf Q_\ell
\simeq K_{\lambda_1}\times K_{\lambda_2}\times\cdots . \tag{2.2}
$$

The characteristic-zero abelian factor carrying the $K$-action is a rational object. It contains all factors in (2.2). The coordinate projector onto $K_{\lambda_1}$ belongs to $K\otimes\mathbf Q_\ell$, but in general it does not belong to $K$, and therefore cannot define a rational abelian subvariety or quotient. The obstruction is precisely that the field $K$ has no nontrivial rational idempotents even when its scalar extension to $\mathbf Q_\ell$ splits.

By contrast, the same coordinate projector can preserve the integral $\ell$-adic Tate lattice. It comes from the idempotent $e$ of the finite semilocal ring $\mathbb T\otimes\mathbf Z_\ell$, not from an element of $\mathbb T_{\mathbf Q}$. It consequently acts on every $\ell^r$-torsion group scheme even when it has no meaning as a rational endomorphism of $J$.

This produces two legitimate operations with different targets:

$$
\begin{array}{ccl}
E\in\mathbb T_{\mathbf Q}
&\rightsquigarrow&
\text{a rational abelian quotient},\\[4pt]
e\in\mathbb T\otimes\mathbf Z_\ell
&\rightsquigarrow&
\text{an integral direct summand of the }\ell\text{-divisible group}.
\end{array} \tag{2.3}
$$

The relation $eE=e$ says that the local summand occurs inside the rational support. It does not say $e=E\otimes1$. If the field factor has several primes above $\ell$, the inequality is strict. Any proof that silently replaces $e$ by a rational projector has discarded precisely the companion primes that rationality obliges the quotient to retain.

There is a second possible error. One might choose a denominator $M$ for $E$ and argue that the resulting comparison has degree prime to $\ell$. No such choice is generally available. The denominator of $E$ records the failure of the rational decomposition to split the integral Hecke lattice, and that failure can be supported at $\ell$. The saturation theorem below is therefore a theorem about generic Tate lattices. It does not cancel the denominator in the category of finite-flat group schemes.

## 3. The selected Eisenstein quotient

The completed torsion piece can be studied inside $J$, but later descent needs a genuine abelian quotient with a Neron model. Rational support produces that quotient. Its generic $\ell$-adic lattice agrees exactly with the selected lattice in $J$. Integral finite-flat models with the same generic lattice can differ at $\ell$ in general, so equality in the present tower requires the separate ordinary-rigidity argument of Chapter 8.

### 3.1 Optimal quotients attached to rational support

Let

$$
K=(\ker(u:J\to J))^0
$$

be the identity component of the kernel, and define

$$
A_{\mathfrak m}=J/K. \tag{3.1}
$$

The quotient exists as an abelian variety. The map $\pi:J\to A_{\mathfrak m}$ has connected kernel and is therefore optimal. Since $u$ vanishes on $(1-E)J$ and acts as multiplication by $M$ on $EJ$ up to isogeny, $A_{\mathfrak m}$ has exactly the rational Hecke support meeting the selected complete local factor. It can have companion local factors above $\ell$; its $\mathfrak m$-factor is nevertheless exactly the one selected by $e$.

An equivalent denominator-free description uses the saturated ideal

$$
\mathfrak a=E\mathbb T_{\mathbf Q}\cap\mathbb T.
$$

Then $K=(J[\mathfrak a])^0$. Indeed, the elements of $\mathfrak a$ act trivially on the $(1-E)$-support and, after tensoring with $\mathbf Q$, contain an isogeny on every $E$-factor. Their common kernel therefore has $(1-E)J$ as its maximal connected abelian subvariety and only a finite contribution on the $E$-support. Saturation makes this description independent of cleared denominators. Notice that using $(1-E)\mathbb T_{\mathbf Q}\cap\mathbb T$ would select the opposite connected support. The displayed ideal is the canonical denominator-free description of the selected quotient.

The construction is nontrivial exactly when a characteristic-zero Hecke factor lies above $\mathfrak m$. The congruence $\mathbb T/I\ne0$ guarantees that the completed local algebra and completed torsion piece are nonzero, but it does not, by itself, assert that one characteristic-zero branch accounts for the full exponent $d$. Several branches may meet at $\mathfrak m$.

### 3.2 Independence of denominators

Suppose $M'$ is another positive integer with $M'E\in\mathbb T$. The connected kernels of $ME$ and $M'E$ have the same rational tangent space and the same complementary rational support; hence they are equal. More concretely, choose integers $r,s$ with

$$
rM+sM'=\gcd(M,M').
$$

The connected kernels of $ME$ and $M'E$ both equal the connected kernel of $\gcd(M,M')E$, because multiplication by a nonzero integer is an isogeny and does not change the maximal connected abelian subvariety on which $E$ vanishes. Therefore (3.1) is independent of the denominator.

Different choices of an abelian subvariety representing the image of $E$ can differ by isogeny. The optimal quotient removes this ambiguity. Its full $\ell$-divisible group may contain companion local factors, so the integral idempotent must still be applied.

### 3.3 The Neron model

Let $\mathcal A_{\mathfrak m}/\mathbf Z$ denote the Neron model of $A_{\mathfrak m}$. It exists and is unique. Every Hecke endomorphism preserving the rational support descends to $A_{\mathfrak m}$ and extends uniquely to $\mathcal A_{\mathfrak m}$. In particular the order

$$
\mathbb T^{(\mathfrak m)}
=\operatorname{im}(\mathbb T\to\operatorname{End}(A_{\mathfrak m}))
$$

acts on the Neron model.

The Neron mapping property is the right extension principle for endomorphisms, but it does not make their kernels finite. We shall take torsion only after restricting to the good-reduction base $S$, where the model is proper and the usual abelian-scheme torsion theorem applies.

### 3.4 Good reduction away from the level

Over $S$, the modular Jacobian $\mathcal J$ is an abelian scheme. The homomorphism $u$ extends uniquely over $S$, but extension of this endomorphism alone is not enough to identify an integral connected kernel. We first establish good reduction of the quotient and prove exactness separately in the next section.

More directly, the rational support admits a complementary abelian subvariety by Poincare reducibility. The addition map from the support and its complement to $J$ is an isogeny. Extending that isogeny over every localization in $S$ and quotienting by its finite-flat kernel produces good models of both rational factors. The model with generic fiber $A_{\mathfrak m}$ is the restriction of its Neron model, hence is $\mathcal A_{\mathfrak m}|_S$.

There is also an intrinsic argument. Good reduction of an abelian variety is invariant under isogeny. The selected quotient is isogenous to an abelian subvariety of $J$, and both subvarieties and quotients of a good-reduction abelian variety have good reduction. The Neron model is consequently proper over every localization $\mathbf Z_q$ with $q\ne N$, hence an abelian scheme there.

At $N$, properness generally fails. The component group calculated from the two-component special fiber is essential, and no assertion below treats $\mathcal A_{\mathfrak m}[\ell^r]$ over $\mathbf Z_N$ as torsion of an abelian scheme.

### 3.5 What extends over the good-reduction base

The connected kernel gives an exact quotient over the generic field. It is important to separate that fact from the stronger assertion that the same connected kernel remains the scheme-theoretic kernel over every residue field.

Over $\mathbf Q$ there is an fppf exact sequence

$$
0\longrightarrow K\longrightarrow J
\xrightarrow{\pi}A_{\mathfrak m}\longrightarrow0. \tag{3.2}
$$

For every positive integer $n$, it induces an exact sequence

$$
0\longrightarrow K[n]\longrightarrow J[n]
\xrightarrow{\pi}A_{\mathfrak m}[n]\longrightarrow0. \tag{3.3}
$$

The surjectivity at the right is worth proving. Let $y$ be an $n$-torsion point of the quotient over a test scheme. Fppf-locally, lift it to $x\in J$. Then $nx$ lies in $K$. Multiplication by $n$ on the abelian variety $K$ is faithfully flat, so after a further fppf cover there is $k\in K$ with $nk=nx$. The point $x-k$ belongs to $J[n]$ and still maps to $y$. Its ambiguity is exactly $K[n]$. This proves (3.3) as a statement about group schemes, without counting geometric points.

The denominator used to define $K$ also supplies a comparison in the opposite direction. Recall that $u=ME$ and $K=(\ker u)^0$. The restriction of $u$ to $K$ is zero, so $u$ factors uniquely through $\pi$:

$$
J\xrightarrow{\pi}A_{\mathfrak m}
\xrightarrow{s}J,
\qquad s\pi=u. \tag{3.4}
$$

Since $u=ME$ and $E$ is the identity on the selected rational support, we also have

$$
\pi s=[M]_{A_{\mathfrak m}}. \tag{3.5}
$$

One can verify (3.5) after composing with the faithfully flat map $\pi$: both composites with $\pi$ equal $M\pi$. The maps $\pi$ and $s$ are Hecke equivariant because the Hecke algebra is commutative and $\pi$ is an epimorphism of fppf sheaves.

Good reduction and the extension theorem for homomorphisms of abelian varieties extend both maps uniquely to the abelian schemes over $S$:

$$
\mathcal J
\mathop{\longrightarrow}^{\pi}
\mathcal A_{\mathfrak m}
\mathop{\longrightarrow}^{s}
\mathcal J, \tag{3.6}
$$

and the identities $s\pi=u$ and $\pi s=[M]$ still hold. In particular $\pi$ is fiberwise surjective: multiplication by $M$ on an abelian scheme is fppf surjective, and (3.5) factors it through $\pi$. The fibers of $\pi$ have constant dimension, so the standard flatness criterion for morphisms between smooth schemes makes $\pi$ faithfully flat. Its scheme-theoretic kernel is therefore a proper flat group scheme whose generic fiber is $K$.

This is the point at which one must stop. A proper flat group scheme with smooth connected generic fiber need not have smooth special fiber. Nor does equality of the generic identity component prove that the closure of $K$ is the entire integral kernel. A generic monomorphism between good models can acquire a vertical kernel, and a generic quotient can acquire non-smooth vertical structure. Translation of the smooth locus does not repair this: it describes an open subgroup of a special fiber, not the whole fiber. Thus the preceding facts do **not** prove an exact sequence

$$
0\longrightarrow\mathcal K\longrightarrow\mathcal J
\longrightarrow\mathcal A_{\mathfrak m}\longrightarrow0
$$

with $\mathcal K$ an abelian scheme, and they do not prove exactness of the corresponding torsion sequence over $S$. Such a conclusion would require an additional integral theorem controlling the kernel at every good residue characteristic, including the characteristic $\ell$ where the denominator of $E$ can be nonunit.

Nothing needed below is lost. Exact sequence (3.3) over $\mathbf Q$ gives an exact sequence of free $\mathbf Z_\ell$-modules

$$
0\longrightarrow T_\ell K
\longrightarrow T_\ell J
\longrightarrow T_\ell A_{\mathfrak m}
\longrightarrow0. \tag{3.7}
$$

Surjectivity survives the inverse limit because the transition maps on the finite generic torsion groups are surjective. This exact generic Tate sequence is the input to the lattice calculation. Integral finite-flat comparison will instead use the extended maps (3.6) directly.

### 3.6 Saturation of the selected Tate lattice

We can now prove the statement that is lost if one reasons only with rational projectors.

**Theorem 3.1 (generic Tate-lattice saturation).** The quotient map induces an isomorphism

$$
eT_\ell J\xrightarrow{\sim}eT_\ell A_{\mathfrak m}. \tag{3.8}
$$

In particular its image is saturated. For every $r\geq1$ it induces an isomorphism of generic finite etale group schemes

$$
eJ[\ell^r]\xrightarrow{\sim}eA_{\mathfrak m}[\ell^r]
\qquad\text{over }\mathbf Q. \tag{3.9}
$$

**Proof strategy.** Apply the integral idempotent to the exact sequence (3.7). The only point is to show that its part on the connected kernel vanishes integrally. Rational support gives this after tensoring with $\mathbf Q_\ell$; torsion-freeness of the Tate lattice then removes the possible finite error.

**Proof.** The support of $K$ is complementary to $E$. Hence $E$ acts as zero on

$$
T_\ell K\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

Since $eE=e$, the idempotent $e$ also acts as zero on this rational vector space. The module $eT_\ell K$ is a submodule of the free $\mathbf Z_\ell$-module $T_\ell K$. It is therefore torsion-free. Its scalar extension to $\mathbf Q_\ell$ is zero, so

$$
eT_\ell K=0. \tag{3.10}
$$

Applying the exact direct-summand functor $e(-)$ to (3.7) now gives

$$
0\longrightarrow0\longrightarrow eT_\ell J
\longrightarrow eT_\ell A_{\mathfrak m}
\longrightarrow0.
$$

This proves (3.8). Reducing an isomorphism of finite free $\mathbf Z_\ell$-modules modulo $\ell^r$ proves (3.9). $\square$

The proof did not claim that $e$ is rational. It used $E$ to construct the connected quotient and used $e$ only after passing to the generic $\ell$-adic exact sequence. If a coefficient field has several primes above $\ell$, all of them remain in $A_{\mathfrak m}$, while (3.8) extracts exactly the chosen prime.

There is a useful lattice reformulation. Let

$$
L=T_\ell J,\qquad L_A=T_\ell A_{\mathfrak m}.
$$

The rational map identifies $e(L\otimes\mathbf Q_\ell)$ with $e(L_A\otimes\mathbf Q_\ell)$. Theorem 3.1 asserts the stronger equality of generic integral Tate lattices

$$
\pi(eL)=eL_A. \tag{3.11}
$$

This is stronger than equality after tensoring with $\mathbf Q_\ell$, but it is not a theorem about Hopf orders over $\mathbf Z_\ell$. Two finite-flat group schemes can have isomorphic generic Tate data and still be different integral models. Chapter 4 gives the strongest comparison that follows from the available data.

## 4. The two completed Hecke towers

We now apply the local idempotent to the torsion of both abelian schemes. This construction does not ask whether the quotient map has a smooth integral kernel. Each tower is obtained independently as a direct factor of an ambient finite-flat group, and therefore each is exact at every level.

### 4.1 Two finite-level projectors

For every $r\ge1$, both $\mathcal J[\ell^r]$ and $\mathcal A_{\mathfrak m}[\ell^r]$ are finite locally free over $S$. Reduce $e\in\mathbb T_\ell$ modulo $\ell^r$ and define

$$
P_r=e\mathcal J[\ell^r],
\qquad
G_r=e\mathcal A_{\mathfrak m}[\ell^r]. \tag{4.1}
$$

The letter $P$ records the ambient principally polarized Jacobian piece; the letter $G$ records the quotient tower used in descent. The action on $\mathcal A_{\mathfrak m}$ is obtained from the Hecke action on the rational support. Factors not belonging to $E$ act trivially there, while all companion primes above $\ell$ remain until the local idempotent is applied.

The complementary idempotent gives product decompositions

$$
\begin{aligned}
\mathcal J[\ell^r]
&\xrightarrow{\sim}
P_r\times(1-e)\mathcal J[\ell^r],\\
\mathcal A_{\mathfrak m}[\ell^r]
&\xrightarrow{\sim}
G_r\times(1-e)\mathcal A_{\mathfrak m}[\ell^r].
\end{aligned} \tag{4.2}
$$

In both lines the map sends $x$ to $(ex,(1-e)x)$ and the inverse adds the components. Thus $P_r$ and $G_r$ are represented finite-flat groups, and all inclusions and projections are Hecke equivariant. This is stronger than taking a kernel of the Eisenstein ideal: it constructs the summands in every fiber before any kernel or closure operation is considered.

Theorem 3.1 identifies their generic Tate lattices. If their common rank is $h$, then the connectedness of $S$ gives

$$
\operatorname{rank}_S P_r
=\operatorname{rank}_S G_r
=\ell^{rh}. \tag{4.3}
$$

No rank-two or multiplicity-one statement is hidden in $h$.

### 4.2 Exact transition maps in both towers

For either abelian scheme $\mathcal B=\mathcal J$ or $\mathcal A_{\mathfrak m}$, multiplication gives an fppf exact sequence

$$
0\longrightarrow\mathcal B[\ell^r]
\longrightarrow\mathcal B[\ell^{r+s}]
\xrightarrow{\ell^r}\mathcal B[\ell^s]
\longrightarrow0. \tag{4.4}
$$

The projector commutes with multiplication. Applying the direct-summand functor $e(-)$ gives, separately,

$$
0\longrightarrow P_r
\longrightarrow P_{r+s}
\xrightarrow{\ell^r}P_s
\longrightarrow0, \tag{4.5}
$$

and

$$
0\longrightarrow G_r
\longrightarrow G_{r+s}
\xrightarrow{\ell^r}G_s
\longrightarrow0. \tag{4.6}
$$

The final arrows are faithfully flat and the displayed left terms are their exact scheme-theoretic kernels. Taking $s=1$ shows that multiplication $P_{r+1}\to P_r$ and $G_{r+1}\to G_r$ is faithfully flat with kernel $P_1$ and $G_1$, respectively. These statements come from the two ambient abelian schemes and do not use a torsion exact sequence relating them.

### 4.3 The resulting divisible groups

Define

$$
P_{\mathfrak m}=\varinjlim_rP_r,
\qquad
G_{\mathfrak m}=\varinjlim_rG_r. \tag{4.7}
$$

Equations (4.3), (4.5), and (4.6) prove that both are $\ell$-divisible groups of height $h$ over $S$. Their $\ell^r$-torsion groups are exactly $P_r$ and $G_r$. Formation of either tower commutes with arbitrary base change from $S$, because torsion, Hecke action, and the product decompositions (4.2) commute with base change.

The two duality statements are deliberately different. The principal polarization of $J$ and Rosati self-adjointness of $e$ give an integral isomorphism

$$
P_{\mathfrak m}^D\simeq P_{\mathfrak m}. \tag{4.8}
$$

For the quotient one has instead

$$
G_{\mathfrak m}^D
\simeq e^\dagger\mathcal A_{\mathfrak m}^{\vee}[\ell^\infty]. \tag{4.9}
$$

A polarization compatible with the selected Hecke factor gives at most a quasi-polarization on this summand, and its degree can be divisible by $\ell$. Hence (4.9) alone does not promote $G_{\mathfrak m}$ to a perfectly self-dual integral summand. Section 8.5 will recover perfect self-duality only after admissibility has supplied canonical ordinary endpoint sequences on both compatible towers.

### 4.4 Comparison maps at every torsion power

The extended maps (3.6) commute with the Hecke action and therefore preserve the $e$-summands. At every $r$ they give actual morphisms of finite-flat group schemes

$$
\pi_r:P_r\longrightarrow G_r,
\qquad
s_r:G_r\longrightarrow P_r. \tag{4.10}
$$

Because $eE=e$, the relations $s\pi=ME$ and $\pi s=[M]$ restrict to

$$
s_r\pi_r=[M]_{P_r},
\qquad
\pi_rs_r=[M]_{G_r}. \tag{4.11}
$$

These are scheme-theoretic identities, not identities only on geometric points. They commute with multiplication by $\ell$, with the inclusions of lower torsion, with Hecke operators, and with arbitrary base change. For example, for all $r,s\ge1$ there is a commutative diagram with exact rows

$$
\begin{array}{ccccccccc}
0&\longrightarrow&P_r&\longrightarrow&P_{r+s}
&\xrightarrow{\ell^r}&P_s&\longrightarrow&0\\
&&\downarrow\pi_r&&\downarrow\pi_{r+s}
&&\downarrow\pi_s&&\\
0&\longrightarrow&G_r&\longrightarrow&G_{r+s}
&\xrightarrow{\ell^r}&G_s&\longrightarrow&0.
\end{array} \tag{4.12}
$$

Theorem 3.1 says exactly that $(\pi_r)_{\mathbf Q}$ is an isomorphism. More is true away from $\ell$. Over $S[1/\ell]$ the two groups in (4.10) are finite etale. A morphism between finite etale groups over a normal integral base that is an isomorphism on the generic fiber is an isomorphism. Hence

$$
\pi_r:P_r\xrightarrow{\sim}G_r
\qquad\text{over }S[1/\ell]. \tag{4.13}
$$

All possible discrepancy is therefore concentrated over the closed point of $S$ above $\ell$.

Put $c=v_\ell(M)$. The prime-to-$\ell$ part of $M$ acts invertibly on every $\ell$-power torsion group. After multiplying $s_r$ by its inverse in $\mathbf Z/\ell^r\mathbf Z$, equations (4.11) become

$$
\widetilde s_r\pi_r=[\ell^c]_{P_r},
\qquad
\pi_r\widetilde s_r=[\ell^c]_{G_r}. \tag{4.14}
$$

Thus the kernel and fppf-sheaf cokernel of $\pi_r$ are killed by $\ell^c$. They need not themselves be finite flat. Passing through the compatible system gives mutually inverse morphisms after tensoring Hom groups with $\mathbf Q_\ell$:

$$
P_{\mathfrak m}\dashrightarrow G_{\mathfrak m},
\qquad
G_{\mathfrak m}\dashrightarrow P_{\mathfrak m}. \tag{4.15}
$$

In other words, the two completed pieces are quasi-isogenous once a clearing denominator $M$ has been fixed. Their common generic Tate lattice is identified integrally by the canonical quotient map $\pi$, while their integral group-scheme models are, at this stage, controlled only by (4.10)--(4.14).

### 4.5 The exact scope of the comparison

It is tempting to combine generic saturation with equal finite-flat ranks and conclude that $\pi_r$ is an isomorphism over $S$. That implication is false. Over $\mathbf Z_2$, consider

$$
f:\underline{\mathbf Z/2\mathbf Z}\longrightarrow\mu_2
$$

which sends the nonzero section to $-1$. It is an isomorphism over $\mathbf Q_2$. On coordinate rings it is

$$
\mathbf Z_2[t]/(t^2-1)
\longrightarrow
\mathbf Z_2\times\mathbf Z_2,
\qquad
t\longmapsto(1,-1). \tag{4.16}
$$

The image consists of pairs congruent modulo $2$, so (4.16) is not surjective. The source group is etale and the target has connected special fiber. Thus a generic isomorphism between finite-flat groups of equal rank can fail to be an integral isomorphism precisely at the residue characteristic.

The example prevents us from excluding the same obstruction in the present comparison merely from Theorem 3.1. The local idempotent need not descend to a rational projector, and a clearing denominator can have positive $\ell$-adic valuation. Generic saturation by itself supplies no full-faithfulness principle for finite-flat models, and no theorem says that the positive-dimensional kernel of $\mathcal J\to\mathcal A_{\mathfrak m}$ is a smooth abelian scheme. Optimality on the generic fiber supplies neither assertion.

The unconditional comparison available before admissibility is therefore:

1. $\pi_r$ and $s_r$ are actual morphisms of finite-flat group schemes at every torsion power and satisfy (4.11).
2. $\pi_r$ is an isomorphism on the generic fiber and over $S[1/\ell]$.
3. On coordinate rings, generic isomorphism and torsion-freeness make $\pi_r^*$ injective; its finite torsion cokernel is supported at $\ell$.
4. In the fppf-sheaf category, every kernel and cokernel defect is killed by $\ell^c$.
5. If $c=0$, then $[M]$ is invertible on every level, $M^{-1}s_r$ is an actual inverse to $\pi_r$, and the two finite-flat towers are already equal.

This provisional comparison is enough to continue without circularity. Descent on $A_{\mathfrak m}$ uses $G_r=e\mathcal A_{\mathfrak m}[\ell^r]$ itself, whose transition sequences are exact by (4.6). The auxiliary tower $P_r$ supplies integral self-duality. Quasi-isogeny (4.15) identifies their rational Dieudonne modules and hence their Newton slopes and total heights, but it does not yet identify their connected subgroups, etale quotients, or finite-level Hopf orders integrally. After Chapter 7 proves admissibility and Sections 8.1--8.4 extract the ordinary endpoint sequences, Theorem 8.1 will show that every apparent defect in (4.14) vanishes. The counterexample (4.16) remains essential: it explains why that later tower argument cannot be replaced by a single-level appeal to generic saturation.

## 5. Faithful completed Hecke action

A local factor is useful only if its operators remain visible on the selected tower. Faithfulness on the original Jacobian does not automatically imply faithfulness at one finite torsion level, and reduction can erase integral operators. The correct statement is infinite-level: an operator vanishing on every level vanishes on the Tate module and hence in the faithful acting algebra.

### 5.1 Endomorphisms detected on torsion

We need a rigidity lemma.

**Lemma 5.1.** Let $B$ be an abelian scheme over a connected integral base with characteristic-zero generic point, and let $f\in\operatorname{End}(B)$. If $f$ vanishes on $B[\ell^r]$ for every $r$, then $f=0$.

**Proof.** Vanishing on $B[\ell^r]$ means that $f$ factors uniquely through the quotient by this kernel, which is multiplication by $\ell^r$. Thus

$$
f=\ell^r f_r
$$

for an endomorphism $f_r$ and every $r$. Restrict to the generic fiber and then to any complex embedding of a field of definition. On the integral first homology lattice, the matrix of $f$ is divisible by $\ell^r$ for every $r$, hence is zero. A homomorphism of abelian varieties that is zero on homology is zero, and rigidity spreads the equality over the base. $\square$

The complex embedding is only a convenient lattice argument. Equivalently, one may use the free $\mathbf Z_\ell$ Tate module and the fact that a nonzero isogeny-class homomorphism cannot be divisible by arbitrarily high powers of $\ell$ in the finitely generated endomorphism group.

### 5.2 Faithfulness of the local factor

The original Hecke algebra was defined as its faithful image on $J$. Therefore

$$
\mathbb T_\ell\hookrightarrow
\operatorname{End}_{\mathbf Z_\ell}(T_\ell J). \tag{5.1}
$$

Apply the idempotent $e$ on both sides. If $t\in e\mathbb T_\ell=\mathbb T_{\mathfrak m}$ acts trivially on $eT_\ell J$, it acts trivially on $(1-e)T_\ell J$ because $t(1-e)=0$. Hence it acts trivially on the whole Tate module, and (5.1) gives $t=0$. Thus the action on $P_{\mathfrak m}$ is faithful. Theorem 3.1 identifies $eT_\ell J$ with $eT_\ell A_{\mathfrak m}$ Hecke equivariantly. An operator that vanishes on $G_{\mathfrak m}$ therefore vanishes on this Tate lattice and hence is zero. We have proved

$$
\boxed{
\mathbb T_{\mathfrak m}
\hookrightarrow
\operatorname{End}(G_{\mathfrak m}).} \tag{5.2}
$$

At finite level the action factors through a finite quotient

$$
\mathbb T_{\mathfrak m}/\operatorname{Ann}(G_r).
$$

It need not be faithful modulo $\ell^r$ unless the Tate module is faithful with the corresponding integral saturation. What is always true is

$$
\bigcap_{r\ge1}\operatorname{Ann}_{\mathbb T_{\mathfrak m}}(G_r)=0, \tag{5.3}
$$

which is precisely infinite-level faithfulness.

### 5.3 What faithfulness does not say

Faithfulness of the action does not imply that $T_\ell G_{\mathfrak m}$ is free of rank two over $\mathbb T_{\mathfrak m}$, that $G_1$ has dimension two over the residue field, or that $\mathbb T_{\mathfrak m}$ is Gorenstein. Nor does it identify $I/I^2$ with an annihilator or with the congruence quotient.

These distinctions matter. The exact theorem

$$
\mathbb T_{\mathfrak m}/I\mathbb T_{\mathfrak m}
\simeq\mathbf Z_\ell/\ell^d\mathbf Z_\ell \tag{5.4}
$$

measures the scalar Eisenstein quotient. It does not calculate the rank of the completed Tate module over the local Hecke algebra. The present construction needs only the faithful action, the direct-summand torsion, and the selected Eisenstein filtration described next.

## 6. The Eisenstein residual shape

Finite-flat admissibility begins with an actual generic flag. The cusp and Shimura subgroups exhibit two expected lines, but they do not account for every constituent of a possibly higher-dimensional generalized local block. This chapter proves the full flag from an operator identity on the modular Jacobian. The proof retains all nilpotent Hecke directions and never replaces the module by its trace or its semisimplification.

### 6.1 The two characters

The Eisenstein polynomial at a prime $q\nmid N\ell$ is

$$
X^2-(1+q)X+q=(X-1)(X-q). \tag{6.1}
$$

On $\ell$-power torsion, the two roots are represented by the trivial character and the cyclotomic character. We write

$$
\mathbf F_\ell,
\qquad
\mathbf F_\ell(1)
$$

for the corresponding one-dimensional generic modules. Their finite-flat integral models over $S$ are

$$
\underline{\mathbf Z/\ell\mathbf Z},
\qquad
\mu_\ell.
$$

For odd $\ell$ the two characters are distinguished on inertia at $\ell$. At $\ell=2$ they coincide generically, even though their integral models have different connectedness.

### 6.2 The Hecke-radical filtration

The completed summand at level one is larger than the ordinary simultaneous eigenspace. Let

$$
V=G_1(\overline{\mathbf Q})
=eA_{\mathfrak m}[\ell](\overline{\mathbf Q}). \tag{6.2}
$$

By Theorem 3.1 this module is Hecke- and Galois-equivariantly isomorphic to $P_1(\overline{\mathbf Q})=eJ[\ell](\overline{\mathbf Q})$. We use the quotient realization in the notation because $G_r$ is the descent tower. We use the Jacobian realization to import the Eichler--Shimura operator identity. Equivalently, that identity descends through the generic quotient map, since it is a polynomial identity in commuting Hecke and Frobenius operators.

It is a finite-dimensional $\mathbf F_\ell$-space with commuting actions of $\Gamma_{\mathbf Q}$ and of

$$
R=\mathbb T_{\mathfrak m}/\ell\mathbb T_{\mathfrak m}. \tag{6.3}
$$

The ring $R$ is Artinian local. Its maximal ideal

$$
\mathfrak r=\mathfrak m\mathbb T_{\mathfrak m}/
\ell\mathbb T_{\mathfrak m}
$$

is nilpotent, and its residue field is $\mathbf F_\ell$. The last assertion uses the exact Eisenstein quotient: the map $\mathbb T\to\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z$ identifies the residue of $\mathfrak m=(\ell,I)$ with $\mathbf F_\ell$.

The radical powers give a finite filtration

$$
V=\mathfrak r^0V\supseteq\mathfrak rV
\supseteq\cdots\supseteq\mathfrak r^cV=0. \tag{6.4}
$$

Every term is Galois stable because the Hecke and Galois actions commute. On the quotient

$$
W_j=\mathfrak r^jV/\mathfrak r^{j+1}V, \tag{6.5}
$$

the Hecke algebra acts through $R/\mathfrak r=\mathbf F_\ell$. In particular

$$
T_q=1+q
\quad\text{on }W_j
\qquad(q\nmid N\ell). \tag{6.6}
$$

This is the first decisive improvement over a trace congruence. Equation (6.6) is an equality of endomorphisms on an actual Galois module. It holds on every radical layer, regardless of the dimension of $V$, the number of characteristic-zero branches through $\mathfrak m$, or the nilpotence of the special Hecke fiber.

Book 114 gives the integral Eichler--Shimura identity on the full Tate module. Reducing it modulo $\ell$ and passing to $W_j$ gives

$$
\left(\operatorname{Frob}_q-1\right)
\left(\operatorname{Frob}_q-q\right)=0
\quad\text{on }W_j \tag{6.7}
$$

for every prime $q\nmid N\ell$. Here $q$ in the second factor means its image in $\mathbf F_\ell$, equivalently $\bar\chi_\ell(\operatorname{Frob}_q)$. Equation (6.7), not a numerical trace, will force the required constituents.

Via the generic identification with $P_1$, the distinction between $V$ and $J[\mathfrak m]$ is important. The latter is killed by the maximal ideal; the former is the entire generalized local summand and can contain nontrivial Hecke-nilpotent extensions. Filtration (6.4) retains those extensions while reducing their successive layers to honest Eisenstein eigenspaces.

### 6.3 A quadratic-density lemma

We isolate the representation-theoretic argument so that no multiplicity assumption is hidden in it.

**Lemma 6.1 (quadratic-density lemma).** Let $k=\mathbf F_\ell$, let $H$ be a finite group, let

$$
\chi:H\longrightarrow k^\times
$$

be a character, and let $W$ be a finite-dimensional $k[H]$-module. Suppose

$$
(g-1)(g-\chi(g))=0
\quad\text{on }W \tag{6.8}
$$

for every $g\in H$. Then $W$ has an $H$-stable composition series whose factors are $k$ or $k(\chi)$.

**Proof strategy.** Pass to a simple factor. On the kernel of $\chi$, every element acts unipotently with square-zero deviation from the identity. Its finite image is therefore an $\ell$-group. A normal $\ell$-subgroup acts trivially on a simple module in characteristic $\ell$. The simple factor then comes from the cyclic group $\operatorname{im}\chi\subset k^\times$, where the quadratic identity leaves only the two displayed characters.

**Proof.** The identity descends to every subquotient, so let $S$ be a simple $k[H]$-subquotient of $W$. Put $P=\ker\chi$. If $u\in P$, then

$$
(u-1)^2=0 \tag{6.9}
$$

on $S$. In characteristic $\ell$, this implies that the image of $u$ has $\ell$-power order. For odd $\ell$,

$$
(1+X)^\ell=1+X^\ell=1
$$

when $X^2=0$; for $\ell=2$, $(1+X)^2=1$. Thus every element of the finite image of $P$ has $\ell$-power order. If a different prime divided the order of that image, Cauchy's theorem would produce an element of that prime order. Hence the image of $P$ is an $\ell$-group.

A finite $\ell$-group acting on a nonzero vector space in characteristic $\ell$ has a nonzero fixed vector. One proves this by induction on the group order: choose a central subgroup of order $\ell$, take the nonzero kernel of its generator minus $1$, and then apply induction to the quotient action. Because $P$ is normal in $H$, the fixed space $S^P$ is $H$-stable. Simplicity of $S$ gives

$$
S^P=S. \tag{6.10}
$$

Therefore the action on $S$ factors through the subgroup $\operatorname{im}\chi$ of $k^\times$. This subgroup is cyclic of order dividing $\ell-1$, so its representation theory over $k$ is split and semisimple. The simple module $S$ is one-dimensional, given by a power $\chi^a$.

Choose a generator $c$ of $\operatorname{im}\chi$. Identity (6.8) says

$$
(c^a-1)(c^a-c)=0.
$$

Thus $c^a=1$ or $c^a=c$, and the character is respectively $1$ or $\chi$. When $\operatorname{im}\chi$ is trivial, including the case $\ell=2$, the same conclusion reads simply $S=k$. Every simple factor has one of the required forms, and refining a composition series proves the lemma. $\square$

The finiteness hypothesis is exactly what is available in the application: combine the residual Galois representation with the cyclotomic character and pass to its finite image. No semisimplicity of the original module is asserted. The lemma classifies simple factors while allowing arbitrary nonsplit extensions among them.

### 6.4 The Eisenstein selection theorem

We now apply the lemma to each radical layer.

**Theorem 6.2 (Eisenstein selection from the modular Jacobian).** The generic Galois module

$$
G_1(\overline{\mathbf Q})
$$

has a finite Galois-stable filtration whose factors are $\mathbf F_\ell$ or $\mathbf F_\ell(1)$. The filtration may be chosen stable under the full local Hecke algebra. No rank-two, multiplicity-one, Gorenstein, or Hecke-freeness hypothesis is required.

**Proof strategy.** On every radical layer, the integral Eichler--Shimura relation gives the quadratic annihilator at all good Frobenius elements. Chebotarev density turns these Frobenius identities into identities for every element of the finite Galois image. Lemma 6.1 then gives the desired factors. Refining the radical filtration produces a flag in the whole generalized local summand.

**Proof.** Fix $j$ and let $H_j$ be the finite image of

$$
\Gamma_{\mathbf Q}\longrightarrow
\operatorname{GL}(W_j)\times\mathbf F_\ell^\times,
\qquad
\sigma\longmapsto(\rho_j(\sigma),\bar\chi_\ell(\sigma)). \tag{6.11}
$$

The representation is unramified outside $N\ell$. For every conjugacy class of $H_j$, finite Chebotarev density supplies a prime $q\nmid N\ell$ whose arithmetic Frobenius maps to that class. Equation (6.7) is invariant under conjugation, so it implies

$$
(g-1)(g-\bar\chi_\ell(g))=0
$$

for every $g\in H_j$. Lemma 6.1 gives a composition series of $W_j$ with factors $\mathbf F_\ell$ and $\mathbf F_\ell(1)$.

On $W_j$ the Hecke algebra acts by scalars through $\mathbf F_\ell$. Every Galois-stable subspace in this composition series is therefore Hecke stable. Take inverse images in $\mathfrak r^jV$, and concatenate these refinements as $j$ varies. The result is a Galois- and Hecke-stable composition series of $V$ with the asserted factors. $\square$

This theorem is the missing selection statement. The adjective “selected” now refers only to the canonical choice of the local Hecke factor and its rational support. It is no longer an additional reducibility hypothesis.

The theorem does not compute multiplicities. If the dimension of $V$ is $h$, it supplies $h$ one-dimensional factors, but it does not say how many are trivial and how many are cyclotomic. That count will be obtained integrally from the connected--etale sequence. The principal self-duality of $P_{\mathfrak m}$, transported at first only through the quasi-isogeny category, will equate the two endpoint heights. The ordinary-tower argument of Section 8.5 will then strengthen this to a perfect integral pairing on $G_{\mathfrak m}$. Nor does the theorem identify a canonical first line. The cuspidal and Shimura groups give geometric lines in particular levels, while a composition series of the whole local block remains noncanonical.

### 6.5 Stable filtrations at every finite level

Choose the Galois- and Hecke-stable composition series supplied by Theorem 6.2. Pull it back through multiplication by $\ell$ along

$$
0\longrightarrow G_1(\overline{\mathbf Q})
\longrightarrow G_r(\overline{\mathbf Q})
\xrightarrow{\ell}G_{r-1}(\overline{\mathbf Q})
\longrightarrow0. \tag{6.12}
$$

Induction gives a stable filtration of $G_r(\overline{\mathbf Q})$ with the same two kinds of order-$\ell$ factors. The number of factors is $rh$, because $G_r$ has order $\ell^{rh}$. The construction can be made compatible in $r$: begin with the chosen filtration of $G_1$, and at each stage insert it into the kernel of multiplication and pull the preceding filtration back from the quotient.

Here is the exact induction. Suppose

$$
0=F_0\subset F_1\subset\cdots\subset F_{(r-1)h}
=G_{r-1}(\overline{\mathbf Q})
$$

has been constructed. Let $P_i$ be the inverse image of $F_i$ in $G_r$. Then

$$
G_1=P_0\subset P_1\subset\cdots\subset P_{(r-1)h}=G_r,
$$

and $P_i/P_{i-1}\simeq F_i/F_{i-1}$. Insert the fixed $h$-step filtration of $G_1$ below $P_0$. Every term is Galois and Hecke stable. This produces exactly $rh$ factors.

The filtration is generally nonsplit and noncanonical. Nothing in the construction diagonalizes the Galois action or the Hecke algebra. A unipotent extension of the trivial character by itself, an extension of the cyclotomic character by the trivial character, and nilpotent congruence extensions among characteristic-zero branches are all retained.

### 6.6 Why Carayol descent is not the missing argument

Book 62 proves a powerful descent theorem: a continuous representation with absolutely irreducible residual representation descends, after strict conjugacy, to its closed trace algebra. Every word in the absolute-irreducibility hypothesis matters. Burnside density is used to make residual group matrices span a full matrix algebra; that matrix algebra is then split by Henselian lifting.

The Eisenstein residual system has the opposite shape. Its expected simple factors are $1$ and $\bar\chi_\ell$, so it is reducible; at $\ell=2$ the two factors even coincide. Burnside density therefore does not apply. The diagonal counterexamples in Book 62 show that trace containment without absolute irreducibility cannot be repaired by a change of basis. Carayol descent supplies neither a stable line nor a filtration in the present setting.

Nor is a faithful two-dimensional pseudorepresentation needed. The module $V$ may have dimension greater than two, and no multiplicity theorem has reduced it to a free rank-two module over the local Hecke algebra. What we possess instead is an equality of endomorphisms on the entire torsion module: the Eichler--Shimura quadratic polynomial. Passing through the Hecke-radical filtration turns its coefficient $T_q$ into the scalar $1+q$ on every layer. The quadratic-density lemma then classifies all simple Galois factors without constructing a matrix representation over $\mathbb T_{\mathfrak m}$.

This audit also explains why “faithful Hecke action plus Carayol” would be circular here. Faithfulness says that the local Hecke algebra is detected on the full tower. It does not say the Tate module is free of rank two over that algebra. Carayol would require a residual absolutely irreducible matrix representation of a fixed rank before it could begin. Neither assertion follows from the exact Eisenstein index, and neither is used in Theorem 6.2.

### 6.7 Why traces alone are insufficient

From $I\subset\mathfrak m$ one obtains the congruences

$$
T_q\equiv1+q\pmod{\mathfrak m},
\qquad U_N\equiv1\pmod{\mathfrak m}. \tag{6.13}
$$

If one knew only a two-dimensional trace and determinant, these congruences would at most identify the semisimplification $1\oplus\bar\chi_\ell$. They would not produce a stable line or control a nonsplit extension. In higher dimension, a single trace value does not even determine the multiplicities of the two expected characters.

The proof above uses different data. On each actual module $W_j$, it proves the operator identity

$$
(\rho(\operatorname{Frob}_q)-1)
(\rho(\operatorname{Frob}_q)-\bar\chi_\ell(\operatorname{Frob}_q))=0. \tag{6.14}
$$

An annihilating polynomial constrains every vector and every subquotient, whereas a trace constrains only one scalar. Chebotarev transports the operator identity to the whole finite image, and the normal $\ell$-subgroup argument then produces the composition factors. The resulting stable flag is therefore not inferred from trace, index, endpoints, or semisimplification.

The cuspidal and Shimura groups retain a separate role. They give canonical geometric constant and multiplicative directions and exact orders, and they orient later extension calculations. They are not used to claim that the rest of the local block has the same factors. That global assertion is Theorem 6.2, proved from the modular Jacobian and its integral Frobenius polynomial.

## 7. Integral admissibility

Once the generic flag exists, it must be transported into integral geometry one subgroup at a time. Saturated closure supplies finite-flat terms and quotients, but the quotient of order $\ell$ must still be identified. Odd primes are controlled by low ramification; the dyadic prime is controlled by the fact that $\mathbf Z_2$ is unramified and admits only the two endpoint order-two models.

### 7.1 Closing the generic filtration

Fix $r$. Each $G_r$ is a direct factor of the torsion of the abelian scheme $\mathcal A_{\mathfrak m}/S$. Close the terms of the generic stable filtration successively inside $G_r$ and inside the successive quotients. Over the Dedekind scheme $S$, saturated schematic closure of a generic subgroup in a finite-flat group is finite flat, and its quotient is finite flat. We obtain

$$
0=\mathcal F_0\subset\mathcal F_1\subset\cdots
\subset\mathcal F_{rh}=G_r. \tag{7.1}
$$

Every inclusion in (7.1) is a closed finite-flat subgroup inclusion, and every quotient has order $\ell$. Closure uniqueness makes the filtration Hecke stable whenever the generic filtration is Hecke stable.

This fixed-ambient construction is essential. Taking the scheme-theoretic kernel of every element of $I$ and intersecting those kernels can create a nonflat scheme. In (7.1), saturation and quotient formation occur at each step inside an already finite-flat ambient group.

### 7.2 Odd Eisenstein primes

Assume $\ell$ is odd. An order-$\ell$ finite-flat group over $\mathbf Z_\ell$ whose generic character is trivial is the constant group, while one whose generic character is cyclotomic is $\mu_\ell$. The ramification index of $\mathbf Z_\ell$ is $1<\ell-1$, so the required height-one rigidity applies.

Away from $N\ell$, both groups are etale and their generic character determines the model. Equality of the local models at every nonzero prime, together with the lattice intersection property over the Dedekind domain $\mathbf Z[1/N]$, gives globally

$$
\mathcal F_i/\mathcal F_{i-1}\simeq
\underline{\mathbf Z/\ell\mathbf Z}
\quad\text{or}\quad
\mu_\ell. \tag{7.2}
$$

Thus every $G_r$ is Eisenstein-admissible. Notice that admissibility means filtered by the two atoms; it does not mean split or killed by $\ell$.

### 7.3 Order-two groups over the unramified base

At $\ell=2$, Theorem 6.2 still gives stable order-two generic factors, but the generic character cannot label them: $\mathbf F_2^\times$ is trivial. What saves admissibility over the present base is not a character calculation. It is the complete order-two classification over the unramified dyadic DVR.

**Proposition 7.1 (global order-two endpoint theorem).** Let

$$
S=\operatorname{Spec}\mathbf Z[1/N]
$$

with $N$ odd, and let $H/S$ be finite flat of order two. If its generic fiber is the one-dimensional $\mathbf F_2$-module, then

$$
H\simeq\underline{\mathbf Z/2\mathbf Z}
\quad\text{or}\quad
H\simeq\mu_2. \tag{7.3}
$$

The two alternatives are distinguished by the special fiber at $2$: the first is etale and the second is connected.

**Proof strategy.** Oort--Tate classification over $\mathbf Z_2$ has no interior exponent because $v_2(2)=1$. Thus the local group is one of the two endpoints. Away from $2$ the group is finite etale and its trivial generic Galois module has a unique model. The global Hopf lattice is the intersection of these local lattices.

**Proof.** Base change to $\mathbf Z_2$. In the order-two Oort--Tate normal form the parameters satisfy

$$
ab=2.
$$

The exponent $v_2(a)$ is an integer between $0$ and $1$. Hence it is $0$ or $1$. The first case is the etale endpoint $\underline{\mathbf Z/2}$; the second is the multiplicative endpoint $\mu_2$. No local-local order-two model exists over the unramified ring $\mathbf Z_2$.

Suppose first that $H_{\mathbf Z_2}$ is etale. Its generic module is necessarily trivial because $\operatorname{GL}_1(\mathbf F_2)=1$. The henselian finite-etale equivalence therefore identifies it with the constant model over $\mathbf Z_2$. At every prime $r\ne N,2$, the order of $H$ is invertible, so $H_{\mathbf Z_r}$ is finite etale. Again its generic module is trivial, and uniqueness of the finite-etale model identifies it with the constant group. The coordinate Hopf algebra of $H$ and that of the constant group are projective $\mathbf Z[1/N]$-lattices in the same rational Hopf algebra with equal localizations at every nonzero prime. A projective lattice over a Dedekind domain is the intersection of its height-one localizations. Hence $H$ is globally constant.

Suppose instead that $H_{\mathbf Z_2}$ is connected. Cartier duality interchanges the two Oort--Tate endpoints, so $H^D_{\mathbf Z_2}$ is etale. The preceding argument makes $H^D$ globally constant. Dualizing gives $H\simeq\mu_2$. $\square$

The proposition does not choose an endpoint from the generic line. It says that the fixed ambient closure must be one of the two admissible endpoints, and its special-fiber connectedness records which one. This is exactly what admissibility requires. A proposed numerical label such as “cuspidal” or “Shimura” still cannot be read from the generic character at two.

The unramified hypothesis is indispensable. Over a dyadic DVR of ramification index $e_R>1$, Oort--Tate exponents can lie strictly between $0$ and $e_R$, producing local-local order-two models with the same trivial generic character. The present base has completion $\mathbf Z_2$, so those intermediate models do not occur.

### 7.4 Dyadic admissibility

Apply Proposition 7.1 to every successive quotient in the closure filtration (7.1). Each quotient is finite flat of order two and has a one-dimensional generic $\mathbf F_2$-module. It is therefore either $\underline{\mathbf Z/2}$ or $\mu_2$. Thus every $G_r$ is Eisenstein-admissible at $2$ as well.

This conclusion is unconditional for the completed prime-level piece. It does not assume a preassigned dyadic label for every generic line. The label is obtained after closure by inspecting the connectedness of the actual quotient over $\mathbf F_2$. Consequently the dyadic multiplicities are integral invariants, not representation-theoretic invariants.

There are two warnings. First, Proposition 7.1 proves that each factor is an Eisenstein atom; it does not say that a chosen cuspidal order-two line closes to the constant atom or that a chosen Shimura line closes to the multiplicative atom. Such an orientation requires its own geometric argument if a later theorem needs it. Second, a filtration by the two atoms need not split. Even when every generic character is trivial, the integral middle group can carry nontrivial extension, Kummer, and carry data.

The numerical two-primary correction remains independent of this classification:

$$
v_2(n_N)=\max(0,v_2(N-1)-2).
$$

Thus $2$ is an Eisenstein prime exactly when $N\equiv1\pmod8$. The exact denominator comes from the integral Hecke and cusp calculation, while dyadic admissibility comes from the unramified order-two geometry. Neither is obtained by dividing a constant term by $2$.

### 7.5 Compatibility with transition maps

The admissibility of isolated levels would be insufficient if multiplication carried an integral atom to a nonflat image. Here multiplication $G_{r+1}\to G_r$ is faithfully flat by (4.6). Its kernel is $G_1$, already admissible. Pulling a filtration of $G_r$ back along this map and inserting a filtration of the kernel gives an admissible filtration of $G_{r+1}$ compatible with the transition map.

Consequently the entire divisible system is **levelwise Eisenstein-admissible**: all finite levels are admissible, all transition maps are faithfully flat, and their kernels are admissible. Subgroups or quotients formed from terms of the compatible filtration retain these properties.

## 8. Connected, etale, and multiplicative parts

An admissible filtration is noncanonical, while connected and etale parts are canonical. Passing from the former to the latter extracts the intrinsic multiplicities and packages every finite level into one local exact sequence of divisible groups. This is where the list of atoms becomes an ordinary geometric structure rather than a chosen devissage.

### 8.1 The local connected--etale sequence

Base change to $R=\mathbf Z_\ell$. Every finite level has a canonical connected--etale sequence

$$
0\longrightarrow G_r^0
\longrightarrow G_r
\longrightarrow G_r^{\mathrm{et}}
\longrightarrow0. \tag{8.1}
$$

The connected--etale theorem for divisible groups over a complete local base applies directly to $G_{\mathfrak m}$. It says that the finite-level sequences are compatible with the inclusions and multiplication maps, that their connected kernels and etale quotients separately satisfy the divisibility criterion, and that they assemble into

$$
0\longrightarrow G_{\mathfrak m}^0
\longrightarrow G_{\mathfrak m}
\longrightarrow G_{\mathfrak m}^{\mathrm{et}}
\longrightarrow0. \tag{8.2}
$$

The quotient is an etale $\ell$-divisible group and the kernel is a connected $\ell$-divisible group. Thus no rank-growth assertion is being used to manufacture divisibility; compatibility and faithful flatness are conclusions of the connected--etale theorem. Admissibility will identify the connected term as multiplicative in the next section.

### 8.2 Recognition of the multiplicative part

The finite-flat subgroup $G_1^0\subset G_1$ inherits admissibility from $G_1$. Choose an atomic filtration of $G_1^0$. Every term has connected special fiber: a closed subgroup of a finite connected group scheme over a field is connected because its coordinate ring is a quotient of a finite local algebra. Every quotient is connected as well, since the image of a connected finite scheme is connected. A constant atom is etale and nontrivial, so it cannot occur in this filtration. Every factor is therefore $\mu_\ell$.

Cartier duality reverses the filtration and turns every factor into $\underline{\mathbf Z/\ell}$. Extensions of finite etale group schemes over the henselian ring $R$ are finite etale, so $(G_1^0)^D$ is etale. The level-one group of $(G_{\mathfrak m}^0)^D$ is exactly $(G_1^0)^D$. An $\ell$-divisible group over a complete DVR is etale precisely when its level-one group is etale. Hence $(G_{\mathfrak m}^0)^D$ is etale, so $G_{\mathfrak m}^0$ is of multiplicative type.

We therefore write

$$
G_{\mathfrak m}^{\mathrm{mult}}=G_{\mathfrak m}^0.
$$

This equality uses admissibility. A connected $\ell$-divisible group need not be multiplicative in general; formal groups of higher slope give counterexamples. Here the atomic filtration rules out all slopes except $0$ and $1$.

### 8.3 The Eisenstein exact sequence

The canonical local structure is

$$
\boxed{
0\longrightarrow G_{\mathfrak m}^{\mathrm{mult}}
\longrightarrow G_{\mathfrak m}
\longrightarrow G_{\mathfrak m}^{\mathrm{et}}
\longrightarrow0
}\qquad\text{over }\mathbf Z_\ell. \tag{8.3}
$$

After base change to a strict henselian unramified base, the endpoints are isomorphic to sums of the standard height-one groups:

$$
G_{\mathfrak m}^{\mathrm{mult}}
\simeq\mu_{\ell^\infty}^{\,b},
\qquad
G_{\mathfrak m}^{\mathrm{et}}
\simeq(\mathbf Q_\ell/\mathbf Z_\ell)^{a}. \tag{8.4}
$$

The integers $a$ and $b$ are intrinsic. They are equal in the present prime-level situation, but not because a perfect integral pairing on $G_{\mathfrak m}$ has been constructed. Section 8.4 will use the integral self-duality of the Jacobian tower $P_{\mathfrak m}$ together with the quasi-isogeny $P_{\mathfrak m}\dashrightarrow G_{\mathfrak m}$. Thus $h=a+b=2a$.

Sequence (8.3) need not split over $\mathbf Z_\ell$, and it need not spread to a global sequence over $S$ with split multiplicative kernel and constant quotient. Global monodromy away from $\ell$ can obstruct such a separation. Whenever the global Shimura closure and cuspidal quotient supply an actual separation, the extension calculation of Book 134 applies.

### 8.4 Finite levels and heights

Taking $\ell^r$-torsion in (8.3) gives

$$
0\longrightarrow G_{\mathfrak m}^{\mathrm{mult}}[\ell^r]
\longrightarrow G_r
\longrightarrow G_{\mathfrak m}^{\mathrm{et}}[\ell^r]
\longrightarrow0. \tag{8.5}
$$

The ranks are

$$
\ell^{rb},\qquad \ell^{r(a+b)},\qquad\ell^{ra}.
$$

At level one, $b$ is the number of multiplicative atoms and $a$ the number of constant atoms in any admissible filtration. This proves filtration independence directly from the canonical connected--etale sequence.

To justify the count, reduce an admissible filtration of $G_1$ over the perfect residue field $\mathbf F_\ell$. In a faithfully flat exact sequence of finite group schemes, orders of connected components and maximal etale quotients multiply. A factor $\mu_\ell$ contributes order $\ell$ to the connected side and order one to the etale side; a constant factor does the reverse. Induction through the filtration gives

$$
|G_1^0|=\ell^b,
\qquad
|G_1^{\mathrm{et}}|=\ell^a. \tag{8.6}
$$

Since the connected--etale sequence is canonical, the two integers are independent of every choice made in the generic composition series and its closure. Applying the same argument to $G_r$ gives connected and etale orders $\ell^{rb}$ and $\ell^{ra}$. The transition maps preserve the canonical sequences. Their kernels have the corresponding orders, so the restrictions are faithfully flat and assemble into the two endpoint divisible groups in (8.3).

The equality of heights deserves a precise isogeny argument. The principal polarization of $J$ gives a perfect Cartier pairing on the full $\ell$-divisible group. Rosati fixes the prime-level Hecke algebra, hence fixes $e$, so restriction to the direct factor gives

$$
P_{\mathfrak m}^D\simeq P_{\mathfrak m}. \tag{8.7}
$$

The maps $\pi$ and $s$ of Section 4.4 make $G_{\mathfrak m}$ and $P_{\mathfrak m}$ isomorphic after inverting $\ell$. Reduce to the residue field and pass to rational Dieudonne modules. We obtain isomorphisms

$$
D(G_{\mathfrak m})_{\mathbf Q}
\simeq D(P_{\mathfrak m})_{\mathbf Q}
\simeq D(P_{\mathfrak m}^D)_{\mathbf Q}
\simeq D(G_{\mathfrak m}^D)_{\mathbf Q}.
$$

Duality sends a slope $\lambda$ to $1-\lambda$. Sections 8.1--8.2 show that $G_{\mathfrak m}$ has only slope zero, with multiplicity $a$, and slope one, with multiplicity $b$. Its rational Dieudonne module is isomorphic to its dual, so

$$
a=b,
\qquad h=2a. \tag{8.8}
$$

At this point we have proved quasi-self-duality of the selected isocrystal, not yet a perfect Cartier pairing on every $G_r$. It is a multiplicity equality but not complete multiplicity one. The common integer $a$ can exceed one, and nothing here makes the Tate module free of rank two over $\mathbb T_{\mathfrak m}$. The ordinary structure just proved now supplies the additional integral rigidity needed to compare the two towers.

### 8.5 Integral recovery of the quotient tower

The warning in Section 4.5 concerned an isolated finite-flat level. Our comparison is much more structured: the maps occur at every level, the levels form divisible groups, the generic Tate lattice map is saturated, and admissibility has now identified the canonical slope endpoints. These four facts eliminate the possible vertical defect.

**Theorem 8.1 (ordinary-tower rigidity).** The quotient map induces isomorphisms

$$
\pi_r:P_r\xrightarrow{\sim}G_r
\qquad(r\ge1)
\tag{8.9}
$$

over $S$, compatible with Hecke operators, base change, inclusions, and multiplication by $\ell$. Hence

$$
\pi:P_{\mathfrak m}\xrightarrow{\sim}G_{\mathfrak m}.
\tag{8.10}
$$

In particular, the quotient tower is integrally self-dual.

**Proof.** We first work over $R=\mathbf Z_\ell$. The quasi-isogeny (4.15) identifies the rational Dieudonne modules of the special fibers. Since $G_{\mathfrak m}$ has only slopes zero and one by Sections 8.1--8.2, the same is true of $P_{\mathfrak m}$. Its canonical connected--etale sequence is therefore ordinary as well. Indeed, its connected term has only slope one; after Cartier duality its special fiber has only slope zero and is etale. The finite-level criterion for etaleness over a complete DVR then shows that the dual connected term is etale over $R$, so the original connected term is multiplicative. Thus there are functorial exact sequences

$$
\begin{array}{ccccccccc}
0&\longrightarrow&P_{\mathfrak m}^{\mathrm{mult}}
&\longrightarrow&P_{\mathfrak m}
&\longrightarrow&P_{\mathfrak m}^{\mathrm{et}}
&\longrightarrow&0\\
&&\downarrow\pi^{\mathrm{mult}}&&\downarrow\pi
&&\downarrow\pi^{\mathrm{et}}&&\\
0&\longrightarrow&G_{\mathfrak m}^{\mathrm{mult}}
&\longrightarrow&G_{\mathfrak m}
&\longrightarrow&G_{\mathfrak m}^{\mathrm{et}}
&\longrightarrow&0.
\end{array}
\tag{8.11}
$$

The slope multiplicities are invariant under quasi-isogeny, so the two multiplicative terms have the same height $b$ and the two etale terms have the same height $a$.

Pass to the characteristic-zero generic fiber and take Tate modules. At each finite level all group schemes are etale after extension to $\overline{\mathbf Q}_\ell$, so geometric points preserve the exact rows; inverse limits remain exact because the transition maps are surjective. In the following diagram the subscript $\mathfrak m$ is suppressed from the four divisible groups. We obtain

$$
\begin{array}{ccccccccc}
0&\longrightarrow&T_\ell P^{\mathrm{mult}}
&\longrightarrow&T_\ell P
&\longrightarrow&T_\ell P^{\mathrm{et}}
&\longrightarrow&0\\
&&\downarrow T_\ell\pi^{\mathrm{mult}}
&&\downarrow T_\ell\pi
&&\downarrow T_\ell\pi^{\mathrm{et}}&&\\
0&\longrightarrow&T_\ell G^{\mathrm{mult}}
&\longrightarrow&T_\ell G
&\longrightarrow&T_\ell G^{\mathrm{et}}
&\longrightarrow&0.
\end{array}
\tag{8.12}
$$

Every module in (8.12) is finite free over $\mathbf Z_\ell$, and the endpoint inclusions are saturated because their quotients are free. The middle vertical map is an integral isomorphism by Theorem 3.1. Choose $\mathbf Z_\ell$-bases adapted to the two exact rows. The matrix of $T_\ell\pi$ is block upper triangular, with diagonal blocks the matrices of the two endpoint maps. Consequently

$$
\det(T_\ell\pi)
=\det(T_\ell\pi^{\mathrm{mult}})
 \det(T_\ell\pi^{\mathrm{et}}).
\tag{8.13}
$$

The determinant on the left is a unit. Each determinant on the right belongs to $\mathbf Z_\ell$, because both endpoint maps are integral square matrices of the equal ranks just established. Their nonnegative valuations add to zero. Both endpoint determinants are therefore units, and

$$
T_\ell\pi^{\mathrm{mult}}
\quad\text{and}\quad
T_\ell\pi^{\mathrm{et}}
\quad\text{are isomorphisms}.
\tag{8.14}
$$

We now return from Tate lattices to finite-flat groups, but only at the rigid endpoints. For etale $\ell$-divisible groups, reduction modulo $\ell^r$ in (8.14) says that

$$
P^{\mathrm{et}}[\ell^r]_{\mathbf Q_\ell}
\longrightarrow
G^{\mathrm{et}}[\ell^r]_{\mathbf Q_\ell}
$$

is an isomorphism. Both integral groups are finite etale over $R$. The generic-fiber functor on finite etale schemes over a normal henselian DVR is fully faithful: equivalently, each finite etale coordinate algebra is the integral closure of $R$ in its generic algebra. The generic inverse therefore preserves the integral closures, and the endpoint map is an isomorphism over $R$. Cartier duality gives the same conclusion for the multiplicative endpoints.

Taking $\ell^r$-torsion in (8.11) now yields a diagram of exact fppf sheaves whose outer vertical maps are isomorphisms:

$$
\begin{array}{ccccccccc}
0&\longrightarrow&P^{\mathrm{mult}}[\ell^r]
&\longrightarrow&P_r
&\longrightarrow&P^{\mathrm{et}}[\ell^r]
&\longrightarrow&0\\
&&\downarrow\sim&&\downarrow\pi_r&&\downarrow\sim&&\\
0&\longrightarrow&G^{\mathrm{mult}}[\ell^r]
&\longrightarrow&G_r
&\longrightarrow&G^{\mathrm{et}}[\ell^r]
&\longrightarrow&0.
\end{array}
\tag{8.15}
$$

The short five lemma in the abelian category of fppf sheaves makes the middle map an isomorphism. Since it is represented by a morphism of finite-flat group schemes, this is an isomorphism of group schemes over $R$.

It remains to globalize. Section 4.4 already proves that $\pi_r$ is an isomorphism over $S[1/\ell]$. The argument above proves it after the faithfully flat completion of the local ring of $S$ at $\ell$. On coordinate Hopf algebras, $\pi_r^*$ is an injection between finite locally free $S$-modules because it is generically an isomorphism. Its finite cokernel vanishes after localization at every prime: away from $\ell$ by (4.13), and at $\ell$ by faithful flatness of completion. Hence the cokernel is zero and (8.9) holds over $S$. Compatibility was built into (4.10)--(4.12), so the levelwise isomorphisms give (8.10).

Finally, transport the perfect Cartier duality (4.8) across (8.10). This gives

$$
G_{\mathfrak m}^D\simeq G_{\mathfrak m}
$$

integrally, and perfect pairings on every $G_r$. $\square$

The proof also locates exactly why (4.16) is not a counterexample. That map compares one dyadic level and exchanges the etale and multiplicative models; it does not extend to a map of ordinary divisible towers inducing an isomorphism of integral Tate lattices. Theorem 8.1 is therefore not a general full-faithfulness statement for arbitrary finite-flat groups. It is a rigidity theorem for the compatible ordinary situation constructed here. Notice also that it does not make the positive-dimensional kernel of $\mathcal J\to\mathcal A_{\mathfrak m}$ into an abelian scheme. Only the selected torsion direct factors are identified.

### 8.6 Ordinary structure without a chosen splitting

An $\ell$-divisible group over a perfect field is ordinary when only the etale slope zero and multiplicative slope one occur. Sequence (8.3) shows that the special fiber of the completed Eisenstein piece is ordinary. Every finite connected constituent is multiplicative, so no local-local slope can occur; every quotient constituent is etale. Thus the Newton slopes are

$$
0^a,1^a.
$$

Over the algebraic closure of the residue field, the ordinary connected--etale sequence splits canonically at the special fiber. Over $\mathbf Z_\ell$, it generally does not split. Its extension class is precisely integral information invisible in the semisimplified generic Galois representation. This is why the conclusion of the book is an exact sequence rather than a product decomposition.

The distinction may be seen already at height two. Both

$$
\mu_{\ell^\infty}\oplus\mathbf Q_\ell/\mathbf Z_\ell
$$

and a nonsplit ordinary extension have one slope of each kind and the same semisimplified generic characters. Their finite levels have the same atomic multiplicities. They differ in the extension class joining those atoms. At odd $\ell$, Book 134 calculates a global height-two class only after a multiplicative subgroup and a constant quotient have actually been separated. The local ordinary sequence supplies such an orientation over $\mathbf Z_\ell$; it does not automatically globalize it over $S$.

## 9. Cuspidal and Shimura constituents

The selection theorem controls every constituent abstractly, but the two geometric subgroups remain indispensable. They carry canonical orders, Hecke actions, and endpoint generators used in descent. Their role must be stated without promoting them to a complete multiplicity theorem or assuming an unproved intersection formula.

### 9.1 The two canonical cyclic groups

Let

$$
C_N=\langle[0]-[\infty]\rangle,
\qquad
\Sigma_N=\ker(J_0(N)\to J_1(N)).
$$

The prime-level specialization theorem gives

$$
C_N\simeq\mathbf Z/n_N\mathbf Z,
\qquad
\Sigma_N\simeq\mu_{n_N}
$$

on the generic fiber, with the second isomorphism depending on a generator of its character group. Both are annihilated by $I$. Moreover

$$
\mathbb T/I\xrightarrow{\sim}C_N,
\qquad1\longmapsto[0]-[\infty], \tag{9.1}
$$

so the Hecke action on $C_N$ is faithful through the Eisenstein quotient.

Taking $\ell$-primary parts yields cyclic groups of order $\ell^d$. Since the other local Hecke idempotents annihilate an $\mathfrak m$-primary group, both first lie in the generic fiber of the Jacobian summand $P_d$. The generic isomorphism

$$
(\pi_d)_{\mathbf Q}:(P_d)_{\mathbf Q}
\xrightarrow{\sim}(G_d)_{\mathbf Q}
$$

transports them to canonical generic subgroups of the quotient tower. We use these transported subgroups below; this places the named endpoints in the same torsion tower that appears in descent on $A_{\mathfrak m}$.

### 9.2 Their closures in the completed piece

Let $\mathcal C_{\ell}$ and $\mathcal\Sigma_{\ell}$ be their saturated closures in $G_d$. They are finite flat. For odd $\ell$, closing the unique cyclic subgroup of each order gives filtrations

$$
0=\mathcal C_0\subset\cdots\subset\mathcal C_d=\mathcal C_\ell,
\qquad
\mathcal C_i/\mathcal C_{i-1}\simeq\underline{\mathbf Z/\ell}, \tag{9.2}
$$

and

$$
0=\mathcal\Sigma_0\subset\cdots\subset\mathcal\Sigma_d=\mathcal\Sigma_\ell,
\qquad
\mathcal\Sigma_i/\mathcal\Sigma_{i-1}\simeq\mu_\ell. \tag{9.3}
$$

At $2$, closing the same cyclic chains gives filtrations in which every factor is one of the two atoms by Proposition 7.1. The generic character does not determine which factors in the cuspidal closure are constant or which factors in the Shimura closure are multiplicative. Accordingly, (9.2)--(9.3) are asserted with their displayed orientations only for odd $\ell$.

One may also close the original groups inside $P_d$. Before Theorem 8.1 these closures had to be kept separate, because a generic subgroup has a unique saturated closure only after its finite-flat ambient group has been fixed. The isomorphism $\pi_d:P_d\xrightarrow{\sim}G_d$ now carries each closure to the corresponding closure in $G_d$: an isomorphism preserves schematic closure and the finite-flat quotient property. We continue to formulate extension and descent statements in the quotient ambient $G_d$, because that is the coefficient group scheme attached to $A_{\mathfrak m}$.

The exact specialization $C_N\simeq\Phi_N$ proves that the cuspidal line is primitive at the bad fiber over $N$. For odd $\ell$, the Shimura line supplies the displayed multiplicative filtration. At $2$, primitivity at $N$ and diagonalizability of the generic Shimura group do not by themselves determine the model over $\mathbf Z_2$. In every characteristic no claim is made that the intersection of the two closures is the full intersection predicted by a multiplicity-one theorem.

### 9.3 Atomic mixed extensions

Suppose a separated height-two subquotient $H$ of some $G_r$ has an exact sequence

$$
0\longrightarrow\mu_\ell
\longrightarrow H
\longrightarrow\underline{\mathbf Z/\ell}
\longrightarrow0. \tag{9.4}
$$

For odd $\ell$, its extension class lies in

$$
\operatorname{Ext}^1_S(
\underline{\mathbf Z/\ell},\mu_\ell)
\simeq\langle[N]\rangle\simeq\mathbf F_\ell. \tag{9.5}
$$

After choosing endpoint generators, a unique $j\in\mathbf F_\ell$ describes the fiber above $1$ by

$$
T^\ell=N^j. \tag{9.6}
$$

The extension splits exactly when $j=0$. Changing a generator rescales a nonzero $j$, so without chosen generators there are only the split and nonsplit classes.

At $2$, the extension group has three binary invariants: a carry parameter, the sign unit, and the level unit. Consequently (9.6) alone is not a complete dyadic classification.

### 9.4 What is and is not canonical

The completed idempotent, both towers $P_r$ and $G_r$, the divisible groups $P_{\mathfrak m}$ and $G_{\mathfrak m}$, the connected--etale sequence of the quotient tower, and the heights $a,b$ are canonical. The optimal quotient and its quotient map are canonical once the rational support is fixed. Hence the isomorphism $\pi:P_{\mathfrak m}\xrightarrow{\sim}G_{\mathfrak m}$ of Theorem 8.1 is canonical. Choosing an integral multiple $ME$ produces the auxiliary map $s$ and the denominator bound (4.14); changing $M$ changes that displayed auxiliary quasi-inverse, not $\pi$ or the eventual integral identification.

A composition series is not canonical. An identification $\Sigma_N\simeq\mu_{n_N}$ is not canonical. A splitting of (8.3) or (9.4) is not canonical and usually does not exist. The Kummer exponent $j$ is canonical only after endpoint generators have been chosen. These distinctions keep later descent calculations invariant under the automorphisms of the cyclic endpoints.

## 10. Hecke control at finite level

The infinite tower is faithful, but arithmetic arguments are usually performed at finite exponent. This chapter records exactly what descends to each level, how the annihilator filtration recovers the complete algebra, and where the sharp cyclic cusp calculation is stronger than the general completed summand.

### 10.1 The completed Eisenstein ideal

Let

$$
\widehat I=I\mathbb T_{\mathfrak m}.
$$

Completion of the exact global quotient (1.1) gives

$$
\mathbb T_{\mathfrak m}/\widehat I
\simeq\mathbf Z_\ell/\ell^d\mathbf Z_\ell. \tag{10.1}
$$

All other factors above $\ell$ vanish after quotienting by $I$. The $\mathbf Z_\ell$-length of (10.1) is $d$. This is the precise depth of the scalar Eisenstein congruence.

### 10.2 Control modulo powers

Because $G_r$ is killed by $\ell^r$, its continuous action factors through

$$
\mathbb T_{\mathfrak m}/\ell^r\mathbb T_{\mathfrak m}.
$$

Reduction of the idempotent decomposition modulo $\ell^r$ shows that forming $G_r$ commutes with reduction of the Hecke algebra. Explicitly,

$$
G_r=e(\mathcal A_{\mathfrak m}[\ell^r])
=\ker(1-e:\mathcal A_{\mathfrak m}[\ell^r]
\to\mathcal A_{\mathfrak m}[\ell^r]). \tag{10.2}
$$

The equality with a kernel is safe because $1-e$ is an idempotent and (4.2) already proves the kernel is a direct factor. It should not be generalized to an arbitrary element of $I$.

If $s\ge r$, the natural map of acting quotients and multiplication $G_s\to G_r$ are compatible. Thus any identity in $\mathbb T_{\mathfrak m}$ can be checked at all finite levels, and separation of the complete algebra recovers it at the limit.

### 10.3 Annihilators and faithful quotients

Put

$$
\mathfrak k_r=\operatorname{Ann}_{\mathbb T_{\mathfrak m}}(G_r).
$$

Then $\mathfrak k_{r+1}\subseteq\mathfrak k_r$, $\ell^r\mathbb T_{\mathfrak m}\subseteq\mathfrak k_r$, and (5.3) gives $\cap_r\mathfrak k_r=0$. Hence

$$
\mathbb T_{\mathfrak m}
\simeq\varprojlim_r\mathbb T_{\mathfrak m}/\mathfrak k_r. \tag{10.3}
$$

Here is the completeness argument. The algebra $\mathbb T_{\mathfrak m}$ is finite free over $\mathbf Z_\ell$ and therefore compact. For a fixed $n$, the descending images of the $\mathfrak k_r$ in the finite module $\mathbb T_{\mathfrak m}/\ell^n$ stabilize. If their stable image contained a nonzero class $x$, the nested compact sets

$$
\mathfrak k_r\cap(x+\ell^n\mathbb T_{\mathfrak m})
$$

would have nonempty intersection, contradicting $\cap_r\mathfrak k_r=0$. Thus $\mathfrak k_r\subseteq\ell^n\mathbb T_{\mathfrak m}$ for $r$ large enough. Together with $\ell^r\mathbb T_{\mathfrak m}\subseteq\mathfrak k_r$, this proves that the two filtrations are cofinal. Completeness for the $\ell$-adic filtration is therefore exactly (10.3).

This is the exact endomorphism-control statement: the completed Hecke algebra is recovered from its faithful finite images on the tower. It does not claim $\mathfrak k_r=\ell^r\mathbb T_{\mathfrak m}$.

On the cuspidal subgroup the annihilator is sharper. Equation (9.1) gives

$$
\operatorname{Ann}_{\mathbb T_{\mathfrak m}}(C_N[\ell^r])
=I\mathbb T_{\mathfrak m}
+\ell^{\min(r,d)}\mathbb T_{\mathfrak m}
$$

on the $\mathfrak m$ factor. This formula concerns the cyclic cuspidal line, not the entire $G_r$.

### 10.4 Base change and duality

For any $S$-scheme $S'$, the identity (4.2) base changes to the corresponding identity over $S'$. Thus

$$
G_r\times_SS'
=e(\mathcal A_{\mathfrak m,S'}[\ell^r]),
\qquad
P_r\times_SS'=e(\mathcal J_{S'}[\ell^r]). \tag{10.4}
$$

Flatness or connectedness hypotheses are not needed for this projector identity. Connected--etale decomposition, however, is used over a henselian or complete local base. We therefore state (8.3) only after base change to $\mathbf Z_\ell$.

Cartier duality changes the Hecke action by Rosati adjunction. Since the prime-level generators are self-adjoint in the chosen normalization, $I$ and $\mathfrak m$ are stable. The dual of $P_{\mathfrak m}$ is $P_{\mathfrak m}$ integrally. Theorem 8.1 transports that perfect duality to $G_{\mathfrak m}$ and identifies its selected dual piece integrally with $G_{\mathfrak m}$ itself. In either tower, duality exchanges constant and multiplicative factors and reverses atomic extension orientation.

## 11. Exceptional levels and exceptional primes

The construction has two different exceptional directions: the removed level prime $N$ and the residue characteristic $\ell$ of the completed factor. Their geometry must not be mixed. Small levels can make the Eisenstein factor vanish, while the primes two and three alter the exact index and, at two, the integral recognition of endpoint models.

### 11.1 The level prime

An Eisenstein prime $\ell$ divides $n_N$, hence divides $N-1$. Therefore $\ell\ne N$. This elementary observation is indispensable: it places the connected--etale analysis at a good-reduction prime and makes both $\mathcal J[\ell^r]$ and $\mathcal A_{\mathfrak m}[\ell^r]$ finite flat over $S$.

At the level prime $N$, the Neron model is generally not proper. Its component group, rather than an $N$-divisible group, records the specialized cuspidal class. No result in this book asserts finite flatness of all torsion across $N$.

### 11.2 Trivial Eisenstein index

For $N=2,3,5,7,13$, one has $n_N=1$. There is no Eisenstein maximal ideal $(\ell,I)$ and hence no nonzero completed Eisenstein piece of the kind studied here. This is not a failure of construction; the local factor is absent.

At $N=11$, $n_N=5$, and the only Eisenstein prime is $5$. At $N=17$, $n_N=4$, so the dyadic piece has depth two. At $N=19$, $n_N=3$. These examples already display odd, dyadic, and depth phenomena.

### 11.3 The prime three

At $\ell=3$, the trivial and cyclotomic residual characters remain distinct on inertia at $3$. Since $1<3-1$, height-one rigidity applies. Thus the odd-prime admissibility proof works without alteration.

The only exceptional feature is numerical:

$$
v_3(n_N)=\max(0,v_3(N-1)-1).
$$

One factor of $3$ is removed by the elliptic stabilizer contribution already incorporated in the exact index. No additional group-scheme exception occurs.

### 11.4 The prime two

At $2$ there are two independent warnings. Numerically,

$$
v_2(n_N)=\max(0,v_2(N-1)-2),
$$

so a genuine two-primary factor occurs when $N\equiv1\pmod8$. Structurally, $1=\bar\chi_2$, so generic characters do not distinguish constant from multiplicative closures.

The remedy is integral, not representational. Proposition 7.1 shows that over the unramified completion $\mathbf Z_2$ every successive order-two closure is one of the two endpoints; special-fiber connectedness labels the factor after closure. Connected--etale ranks then determine the multiplicities, and the direct-summand construction guarantees all transition maps. No division by $2$, averaging under an involution, or identification of invariants with coinvariants is used.

This statement is deliberately weaker than orienting the named cusp and Shimura closures. Generic diagonalizability does not select the multiplicative model at two, and primitivity at the level-prime component group does not select the constant model at two. The completed piece is nonetheless admissible because admissibility asks that every factor be one of the two atoms, not that a predetermined generic line receive a predetermined label.

## 12. The completed Eisenstein package

All choices and exactness statements can now be assembled. The theorem below records both positive results and scope boundaries so that later descent can cite a single package without silently importing multiplicity one, rational local projectors, or trace-to-representation implications.

### 12.1 Main theorem

We collect the construction and control statements in a form suited to descent.

**Theorem 12.1 (completed prime-level Eisenstein piece).** Let $N$ be prime, let

$$
S=\operatorname{Spec}\mathbf Z[1/N],
\qquad
n_N=\frac{N-1}{\gcd(N-1,12)},
$$

let $\mathbb T$ be the faithful prime-level Hecke algebra, and let

$$
I=(T_q-(1+q):q\ne N)+(U_N-1).
$$

Fix $\ell\mid n_N$, put $d=v_\ell(n_N)$, and let $\mathfrak m=(\ell,I)$. Then the following hold.

1. The finite algebra $\mathbb T\otimes\mathbf Z_\ell$ has a unique idempotent $e_{\mathfrak m}$ selecting its $\mathfrak m$-factor, and

   $$
   e_{\mathfrak m}(\mathbb T\otimes\mathbf Z_\ell)
   =\mathbb T_{\mathfrak m}.
   $$

2. The corresponding rational support defines an optimal abelian quotient $A_{\mathfrak m}$ of $J_0(N)$. Its Neron model restricts to an abelian scheme over $S$, and the definition is independent of the denominator used to realize the rational projector. Companion local factors above $\ell$ are retained by the rational quotient and removed only by applying $e_{\mathfrak m}$ to its $\ell$-power torsion.

3. For every $r\ge1$,

   $$
   P_r=e_{\mathfrak m}\mathcal J[\ell^r],
   \qquad
   G_r=e_{\mathfrak m}\mathcal A_{\mathfrak m}[\ell^r]
   $$

   are finite-flat direct summands of their respective ambient torsion groups. For all $r,s\ge1$ there are fppf exact sequences

   $$
   0\to P_r\to P_{r+s}
   \xrightarrow{\ell^r}P_s\to0,
   \qquad
   0\to G_r\to G_{r+s}
   \xrightarrow{\ell^r}G_s\to0.
   $$

4. The optimal quotient map has saturated selected Tate lattice:

   $$
   e_{\mathfrak m}T_\ell J
   \xrightarrow{\sim}
   e_{\mathfrak m}T_\ell A_{\mathfrak m}.
   $$

   Choose $M>0$ with $ME\in\mathbb T$, where $E$ is the rational support projector, and put $c=v_\ell(M)$. At every level there are comparison maps

   $$
   \pi_r:P_r\longrightarrow G_r,
   \qquad
   s_r:G_r\longrightarrow P_r
   $$

   satisfying $s_r\pi_r=[M]$ and $\pi_rs_r=[M]$. The map $\pi_r$ is an isomorphism generically and over $S[1/\ell]$, and every fppf kernel or cokernel defect is killed by $\ell^c$. If $c=0$, these identities already make the two towers isomorphic. These statements are the comparison available before admissibility. After item 8 supplies the ordinary endpoint sequences, ordinary-tower rigidity proves unconditionally that

   $$
   \pi_r:P_r\xrightarrow{\sim}G_r
   $$

   over $S$ for every $r$, even when $c>0$.

5. The systems

   $$
   P_{\mathfrak m}=\varinjlim_rP_r,
   \qquad
   G_{\mathfrak m}=\varinjlim_rG_r
   $$

   are $\ell$-divisible groups of the same height, and the quotient map identifies them integrally. Both are integrally self-dual. The second remains the actual selected $\ell$-divisible group of the quotient and the coefficient object used for descent; its identification with the Jacobian tower is a proved theorem, not a change of definition.

6. The continuous action

   $$
   \mathbb T_{\mathfrak m}\hookrightarrow
   \operatorname{End}(G_{\mathfrak m})
   $$

   is faithful, and the intersection of the finite-level annihilators is zero.

7. The generic module $G_1(\overline{\mathbf Q})$ has an actual Galois- and Hecke-stable composition series with factors $\mathbf F_\ell$ and $\mathbf F_\ell(1)$. It is obtained from the Hecke-radical filtration and the integral Eichler--Shimura annihilating polynomial, not from trace or semisimplification. Pullback through the exact quotient torsion tower gives compatible such filtrations at every level.

8. Every $G_r$ is Eisenstein-admissible: it has a finite-flat filtration with factors $\underline{\mathbf Z/\ell}$ and $\mu_\ell$. For odd $\ell$ the generic characters determine the endpoint types. At $2$, the unramified Oort--Tate classification proves that every order-two closure is one of the two endpoints, with its label determined by connectedness after closure.

9. Over $\mathbf Z_\ell$ there is a canonical exact sequence

   $$
   0\to G_{\mathfrak m}^{\mathrm{mult}}
   \to G_{\mathfrak m}
   \to G_{\mathfrak m}^{\mathrm{et}}
   \to0.
   $$

   The endpoint heights equal the multiplicative and constant lengths in any admissible level-one filtration. They are equal. First, self-duality of $P_{\mathfrak m}$ and quasi-isogeny with $G_{\mathfrak m}$ make the selected isocrystal self-dual; then Theorem 8.1 upgrades the comparison and transports a perfect integral pairing to every $G_r$.

10. The $\ell$-primary cuspidal and Shimura groups have order $\ell^d$. They lie generically in $P_d$ and transport through $\pi_d:P_d\xrightarrow{\sim}G_d$, which identifies their saturated closures in the two towers. For odd $\ell$, their canonical cyclic filtrations have respectively constant and multiplicative factors. At $2$, each factor is an Eisenstein atom, but its orientation is not inferred from the common generic character. No theorem about the full intersection of the two closures is used.

11. A separated atomic subquotient of $G_r$ with multiplicative kernel and constant quotient is classified, for odd $\ell$, by

   $$
   \operatorname{Ext}^1_S(
   \underline{\mathbf Z/\ell},\mu_\ell)
   \simeq\langle[N]\rangle.
   $$

   The dyadic extension has the additional carry and sign data described in Section 9.3.

12. The completed Eisenstein quotient is

   $$
   \mathbb T_{\mathfrak m}/I\mathbb T_{\mathfrak m}
   \simeq\mathbf Z_\ell/\ell^{v_\ell(n_N)}\mathbf Z_\ell.
   $$

   This controls the scalar Eisenstein depth but asserts neither complete multiplicity one nor freeness of the Tate module over the local Hecke algebra.

**Proof.** Items 1 and 12 follow from the finite-algebra decomposition of Chapter 2 and the exact global Eisenstein index. Chapter 3 constructs the rational quotient and its good model. Generic torsion exactness for the connected optimal kernel proves Theorem 3.1. The extended maps $\pi$ and $s$ and the identities $s\pi=ME$, $\pi s=[M]$ prove the preliminary levelwise comparison in item 4. The constant-to-multiplicative example of Section 4.5 explains why generic saturation alone cannot strengthen it.

The two direct-summand identities (4.2) and the independent transition sequences (4.5)--(4.6) prove item 3 and the divisible-group assertion in item 5. Faithfulness on the Jacobian Tate lattice, transported through Theorem 3.1, proves item 6. For item 7, filter the generalized residual summand by the radical of $\mathbb T_{\mathfrak m}/\ell$. On each layer Eichler--Shimura becomes the operator identity $(F_q-1)(F_q-q)=0$. Finite Chebotarev and Lemma 6.1 force every simple Galois factor to be trivial or cyclotomic.

Chapter 7 closes the resulting actual flag inside the quotient tower. Odd-prime rigidity and Proposition 7.1 identify all closures as Eisenstein atoms, proving item 8. The connected--etale sequence, Cartier-dual recognition, and comparison with the self-dual Jacobian isocrystal first prove the slope and height assertions in item 9. The determinant argument on the two canonical ordinary endpoint sequences then proves Theorem 8.1: the saturated middle Tate map forces integral isomorphisms on both endpoints, and exactness forces $\pi_r$ to be an isomorphism. This completes items 4, 5, and 9 without assuming an integral equality of models in advance. The exact cusp and Shimura calculations give item 10 within its stated odd and dyadic boundaries. The flat Kummer calculation gives item 11. No step uses a nonflat Hecke kernel, a rational form of the local projector, smoothness of the positive-dimensional integral kernel, or an inference from trace to reducibility. $\square$

### 12.2 Dependency ledger

The declared direct dependency row is exactly:

| Book | Direct prerequisites |
|---:|---|
| 147 | 28, 34--35, 38, 51, 55, 57, 85, 114, 132--134, and 142 |

The row includes every earlier source explicitly reused below, even when another listed source
also imports it transitively. Book 62 is mentioned only as a boundary comparison; no result
from it is used in a proof.

Book 35 supplies finite-flat multiplication kernels of abelian schemes, faithfully flat multiplication, finite quotient exactness, extension of homomorphisms over normal good-reduction bases, duality, Weil pairings, and polarization adjunction. In Chapter 3 these facts prove exactness of the generic torsion sequence and extend $\pi$ and $s$ between good abelian-scheme models. They do **not** identify the positive-dimensional integral kernel with the good model of $K$. Section 3.5 explicitly leaves that stronger assertion unmade. The generic fppf lifting proof of (3.3) is the precise reason the selected generic Tate quotient is saturated.

Book 38 supplies Neron models, unique extension of Hecke endomorphisms, properness as the criterion for good reduction, component specialization, and the warning that a Neron extension of an isogeny need not be finite at a bad place. We restrict all torsion constructions to $S$, where the Neron models are abelian schemes. The level-prime component group is used only to state primitivity of the cusp; it is never confused with an $\ell$-adic lattice at a different prime.

Book 28 supplies faithfully flat exact sequences of finite-flat groups, represented quotients, rank multiplication, primary decomposition, and saturated schematic closure in a fixed finite-flat ambient group over a Dedekind base. Chapter 7 uses precisely that closure theorem. It never forms an arbitrary scheme-theoretic Hecke kernel and calls it flat.

Book 34 supplies exact Cartier duality, the exchange of constant and multiplicative groups, annihilator filtrations, compatibility of closure with annihilators, and perfect duality on abelian torsion. These results identify the multiplicative part from the dual etale quotient and make $P_{\mathfrak m}$ integrally self-dual. Equality of the endpoint heights of $G_{\mathfrak m}$ is first deduced in the quasi-isogeny category; Theorem 8.1 subsequently transports the perfect integral duality itself to $G_{\mathfrak m}$.

Book 51 supplies Oort--Tate classification, height-one low-ramification rigidity, the unramified endpoint theorem, and the dyadic warning. For odd $\ell$, $1<\ell-1$ identifies an order-$\ell$ closure from its generic character. For $\ell=2$, the same inequality is unavailable, but the exponent interval over $\mathbf Z_2$ is $\{0,1\}$; Proposition 7.1 uses that complete classification rather than a character label.

Book 55 supplies the finite-level criterion for an $\ell$-divisible group, connected--etale sequences over complete local bases, height and dimension, Cartier duality at infinite level, recognition of etale and multiplicative divisible groups, and isogeny invariance of the rational Dieudonne module. Exact sequences (4.5) and (4.6) verify the required faithful flatness independently for $P_{\mathfrak m}$ and $G_{\mathfrak m}$. Admissibility rules out local-local factors before the quotient special fiber is called ordinary. Isogeny invariance then makes $P_{\mathfrak m}$ ordinary with the same endpoint heights; the functorial endpoint sequences are the input to the determinant and five-lemma proof of Theorem 8.1.

Book 57 supplies completion as an inverse limit, exactness for finite modules, and separation of completed actions. Together with the finite-algebra decomposition and compatible idempotents recalled in Book 85, these facts turn $\mathbb T\otimes\mathbf Z_\ell$ into the product of its complete local factors. Section 2.3 also proves directly the only idempotent-lifting statement used here. We apply this only to the finite torsion-free acting Hecke algebra; no uncontrolled infinite algebra is treated as Noetherian.

Book 62 is not a prerequisite. Section 6.6 mentions its Carayol theorem and counterexamples only to audit an unavailable route: residual absolute irreducibility fails in the Eisenstein problem, so no statement from that book is invoked. The stable flag is proved independently by the Hecke-radical and quadratic-density argument.

Book 142 supplies finite Chebotarev density in exactly the form needed in Theorem 6.2. For each radical layer, we pass to the finite image of the residual Galois representation together with the cyclotomic character. Every conjugacy class in that finite image is represented by an unramified Frobenius, so the Eichler--Shimura operator identity holds for every image element. No density statement for an infinite matrix algebra is used.

Book 85 supplies the acting-image convention, faithfulness after localization, generalized local summands, compatible idempotents, and the distinctions among localization, quotient, ordinary eigenspace, and multiplicity one. The radical filtration (6.4) is necessary precisely because the completed summand can be larger than $J[\mathfrak m]$. No reduction of a faithful integral action is assumed faithful without proof.

Book 114 supplies the integral Hecke action on the modular Jacobian and its Neron model, Rosati adjunction, the good-prime Eichler--Shimura identity

$$
F_q^2-T_qF_q+q=0
$$

on every prime-to-$q$ torsion level, and the explicit warning that it is an annihilating polynomial before any rank-two theorem is known. This operator identity is the decisive Galois input in Chapter 6. It descends to the quotient generic torsion and becomes scalar on each Hecke-radical layer.

Book 132 supplies the faithful prime-level acting algebra, the Eisenstein ideal with $U_N-1$, and the exact quotient $\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z$, including the two- and three-primary exponents. This identifies the residue field and the scalar action on each Hecke-radical layer. It supplies no multiplicity, branch count, Gorenstein property, or stable Galois flag, and none is attributed to it.

Book 133 supplies the exact order and Hecke action of the cuspidal line, its isomorphic specialization in the component group, and the cyclic diagonalizable Shimura kernel of order $n_N$. These objects give named generic subgroups and oriented odd-prime filtrations. We use no theorem about all rational torsion or about the full cuspidal--Shimura intersection.

Book 134 supplies the admissible exact category over $\mathbf Z[1/N]$, the closure criterion for an actual stable generic flag, odd-prime endpoint recognition, filtration independence, inheritance under finite-flat subquotients, and the mixed atomic extension calculation. Its explicitly missing hypothesis is supplied by Theorem 6.2. Its two model-theoretic warnings are both respected: generic characters do not label dyadic endpoints, and a generic isomorphism does not by itself identify finite-flat models. Proposition 7.1 handles the first warning. Sections 4.4--4.5 retain two models until admissibility supplies ordinary endpoint sequences; only then does Theorem 8.1 prove equality by data stronger than a generic isomorphism.

The new arguments in this book are therefore sharply located. Theorem 3.1 proves saturation of the selected generic Tate lattice. Section 4.4 constructs comparison maps at every torsion power and proves the precise denominator bound; Section 4.5 proves why saturation and generic equality alone do not identify finite-flat models. Theorem 6.2 proves the full generic Eisenstein composition series from the radical layers and the Eichler--Shimura operator identity. Theorem 8.1 combines the resulting ordinary endpoint sequences with the saturated Tate map to prove integral equality of the two completed towers. None of these assertions is imported from an index calculation, a trace-descent theorem, or an unproved smoothness statement for the integral optimal kernel.

### 12.3 Conclusion

The completed Eisenstein piece is not obtained by writing an ideal inside a kernel. It is obtained by turning the complete local Hecke factor into an idempotent and applying that idempotent to abelian-scheme torsion. Applied to the quotient, this one choice simultaneously resolves flatness, compatibility, and divisibility:

$$
\mathcal A_{\mathfrak m}[\ell^r]
=G_r\times(1-e_{\mathfrak m})
\mathcal A_{\mathfrak m}[\ell^r],
$$

and multiplication carries these decompositions into one another through faithfully flat exact sequences. Applying the same idempotent to $\mathcal J[\ell^r]$ gives the auxiliary self-dual tower $P_r$.

The rational and local selections first agree on the generic integral Tate lattice. The rational projector retains every coefficient-field conjugate required to define an abelian quotient, while the local idempotent selects one completion on the Tate lattice. Generic exactness of the optimal quotient proves equality of those selected Tate lattices even when a rational field factor has several primes above $\ell$. This fact alone does not identify finite-flat models: the constant-to-$\mu_2$ example proves that point sharply. The maps $P_r\rightleftarrows G_r$ therefore begin as a denominator-bounded comparison. Once admissibility makes both compatible divisible towers ordinary, the saturated middle Tate map has unit determinant, functoriality splits its determinant into the multiplicative and etale endpoint determinants, and both endpoints must be integral isomorphisms. Exactness then proves $P_r\simeq G_r$ for every $r$. Thus the vertical defect vanishes in this completed Eisenstein tower for a reason unavailable at an isolated level.

The full Eisenstein filtration comes from the modular Jacobian rather than from its trace. On each Hecke-radical layer, the integral Eichler--Shimura relation becomes

$$
(F_q-1)(F_q-q)=0.
$$

Chebotarev and the normal $\ell$-subgroup argument force every simple Galois factor to be trivial or cyclotomic. Saturated closure turns that actual stable flag into admissible finite-flat filtrations. The rational cusp and Shimura kernel then supply named geometric directions and exact orders, rather than standing in for a proof about all remaining constituents.

Locally at $\ell$, the admissible filtrations assemble into the canonical sequence

$$
0\to G_{\mathfrak m}^{\mathrm{mult}}
\to G_{\mathfrak m}
\to G_{\mathfrak m}^{\mathrm{et}}
\to0.
$$

At odd primes the two endpoint characters identify their integral models. At two, the unramified Oort--Tate interval has only its endpoints, and connectedness supplies the label that the generic character cannot. The exact exponent $v_\ell(n_N)$ controls the scalar Eisenstein congruence, while faithfulness of the completed action retains every Hecke operator visible on the selected tower.

This is the integral package required for Eisenstein descent: an optimal quotient with a good Neron model over $S$; its own canonical finite-flat selected torsion at every power; exact transition maps; a proved integral identification with the self-dual Jacobian tower; an actual generic Eisenstein flag; admissible constant and multiplicative constituents; controlled atomic extensions; and a faithful complete local endomorphism action. Descent still uses the quotient tower directly, and Theorem 8.1 proves rather than assumes that its completed summand has the canonical integral model selected inside the Jacobian. None of these conclusions requires complete multiplicity one, a full Shimura-intersection theorem, a rational incarnation of the local idempotent, smoothness of the positive-dimensional integral optimal kernel, or Carayol descent outside its absolutely irreducible range.
