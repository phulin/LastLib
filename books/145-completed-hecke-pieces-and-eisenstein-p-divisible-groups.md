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
   - [The exact abelian quotient](#35-the-exact-abelian-quotient)
   - [Saturation of the selected Tate lattice](#36-saturation-of-the-selected-tate-lattice)
4. [The completed Hecke piece](#4-the-completed-hecke-piece)
   - [Finite-level projectors](#41-finite-level-projectors)
   - [Exact transition maps](#42-exact-transition-maps)
   - [The resulting divisible group](#43-the-resulting-divisible-group)
   - [Comparison with the selected quotient](#44-comparison-with-the-selected-quotient)
   - [Equality of the two finite-flat towers](#45-equality-of-the-two-finite-flat-towers)
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
   - [The local connected--etale sequence](#81-the-local-connected-etale-sequence)
   - [Recognition of the multiplicative part](#82-recognition-of-the-multiplicative-part)
   - [The Eisenstein exact sequence](#83-the-eisenstein-exact-sequence)
   - [Finite levels and heights](#84-finite-levels-and-heights)
   - [Ordinary structure without a chosen splitting](#85-ordinary-structure-without-a-chosen-splitting)
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
\text{direct summands of }J[\ell^r]
\Longrightarrow
\text{exact compatible tower}
\Longrightarrow
\ell\text{-divisible group}.
$$

Direct summands, rather than arbitrary kernels, are decisive. An idempotent splits every ambient finite-flat torsion group as a product. Flatness, quotient representability, and compatibility then follow formally from the ambient abelian scheme.

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
e=v_\ell(n_N).
$$

We reserve $q$ for primes away from $N\ell$. This separation of the level prime $N$, the Eisenstein prime $\ell$, and an auxiliary good prime $q$ prevents several common normalization errors.

### 1.3 What will be constructed

There are two related objects.

The first is the **selected Eisenstein quotient** $A_{\mathfrak m}$ of $J$: it is the optimal abelian quotient supported on precisely those characteristic-zero Hecke factors whose integral closures have a prime above $\mathfrak m$. This quotient is canonical as an optimal quotient. A denominator used to write its rational support need not be prime to $\ell$; independence comes from equality of connected kernels, not from cancelling that denominator.

The second is the **completed Hecke piece**

$$
G_{\mathfrak m}=e_{\mathfrak m}\mathcal J[\ell^\infty],
$$

where $e_{\mathfrak m}$ is the local idempotent in $\mathbb T\otimes\mathbf Z_\ell$. It is an $\ell$-divisible group over $S$, equipped faithfully with the complete local algebra $\mathbb T_{\mathfrak m}$. Its finite levels are finite flat, and over $\mathbf Z_\ell$ it has a canonical exact sequence with multiplicative kernel and etale quotient.

The completed object is the one needed in descent. The abelian quotient supplies geometric origin, a Neron model, polarizations up to isogeny, and comparison with rational Hecke factors. The divisible group supplies exact integral torsion at every $\ell$-power level.

## 2. Finite Hecke algebras and their local idempotents

Localization becomes geometric only after it is represented by an idempotent that acts on integral torsion. This chapter constructs that idempotent and, just as importantly, separates it from the rational projector used to construct an abelian quotient. The two projectors remember different equivalence relations: rational support groups together coefficient conjugates, while the $\ell$-adic projector distinguishes primes above $\ell$.

### 2.1 The acting algebra

Because $\mathbb T$ is the image of the abstract correspondences on a finite free integral lattice of differentials, it is a finite torsion-free $\mathbf Z$-algebra. The Rosati involution attached to the canonical principal polarization fixes the good Hecke operators and preserves $U_N$ in the present prime-level normalization. Hence it fixes every element of the commutative algebra they generate. The positivity of Rosati is important here: on rational homology it makes every such element self-adjoint for a positive-definite form, and therefore diagonalizable after extending scalars to $\mathbf R$. A nilpotent element is consequently zero. Thus the rational algebra

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

but $E\otimes1$ can be strictly larger than $e$. Choose any positive integer $a$ such that

$$
u=aE\in\mathbb T.
$$

No claim is made that $a$ is prime to $\ell$. The rational projector constructs an abelian quotient containing all coefficient conjugates forced by rationality; the integral idempotent subsequently extracts its precise $\mathfrak m$-adic summand. Keeping these two operations separate is essential.

### 2.5 Why the two projectors cannot be identified

The distinction in the preceding section is not a technical nuisance. It is forced by scalar descent. Suppose a field factor $K$ of $\mathbb T_{\mathbf Q}$ has two primes $\lambda_1$ and $\lambda_2$ above $\ell$. Then

$$
K\otimes_{\mathbf Q}\mathbf Q_\ell
\simeq K_{\lambda_1}\times K_{\lambda_2}\times\cdots . \tag{2.2}
$$

The characteristic-zero abelian factor carrying the $K$-action is a rational object. It contains all factors in (2.2). The coordinate projector onto $K_{\lambda_1}$ belongs to $K\otimes\mathbf Q_\ell$, but in general it does not belong to $K$, and therefore cannot define a rational abelian subvariety or quotient. Galois conjugacy of the primes above $\ell$ is exactly the obstruction.

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

There is a second possible error. One might choose a denominator $a$ for $E$ and argue that the resulting isogeny has degree prime to $\ell$. No such choice is generally available. The denominator of $E$ records the failure of the rational decomposition to split the integral Hecke lattice, and that failure can be supported at $\ell$. The saturation argument below therefore does not cancel a denominator. It uses the connected kernel of the optimal quotient and exactness of its entire torsion sequence.

## 3. The selected Eisenstein quotient

The completed torsion piece could be studied entirely inside $J$, but later descent also needs a genuine abelian quotient with a Neron model. Rational support produces that quotient. The central question is whether its integral $\ell$-adic lattice agrees with the completed summand already present in $J$. The connected kernel of the optimal quotient will make the answer exact rather than merely up to isogeny.

### 3.1 Optimal quotients attached to rational support

Let

$$
K=(\ker(u:J\to J))^0
$$

be the identity component of the kernel, and define

$$
A_{\mathfrak m}=J/K. \tag{3.1}
$$

The quotient exists as an abelian variety. The map $\pi:J\to A_{\mathfrak m}$ has connected kernel and is therefore optimal. Since $u$ vanishes on $(1-E)J$ and acts as multiplication by $a$ on $EJ$ up to isogeny, $A_{\mathfrak m}$ has exactly the rational Hecke support meeting the selected complete local factor. It can have companion local factors above $\ell$; its $\mathfrak m$-factor is nevertheless exactly the one selected by $e$.

An equivalent denominator-free description uses the saturated ideal

$$
\mathfrak a=E\mathbb T_{\mathbf Q}\cap\mathbb T.
$$

Then $K=(J[\mathfrak a])^0$. Indeed, the elements of $\mathfrak a$ act trivially on the $(1-E)$-support and, after tensoring with $\mathbf Q$, contain an isogeny on every $E$-factor. Their common kernel therefore has $(1-E)J$ as its maximal connected abelian subvariety and only a finite contribution on the $E$-support. Saturation makes this description independent of cleared denominators. Notice that using $(1-E)\mathbb T_{\mathbf Q}\cap\mathbb T$ would select the opposite connected support. The displayed ideal is the canonical denominator-free description of the selected quotient.

The construction is nontrivial exactly when a characteristic-zero Hecke factor lies above $\mathfrak m$. The congruence $\mathbb T/I\ne0$ guarantees that the completed local algebra and completed torsion piece are nonzero, but it does not, by itself, assert that one characteristic-zero branch accounts for the full exponent $e$. Several branches may meet at $\mathfrak m$.

### 3.2 Independence of denominators

Suppose $a'$ is another positive integer with $a'E\in\mathbb T$. The connected kernels of $aE$ and $a'E$ have the same rational tangent space and the same complementary rational support; hence they are equal. More concretely, choose integers $r,s$ with

$$
ra+sa'=\gcd(a,a').
$$

The connected kernels of $aE$ and $a'E$ both equal the connected kernel of $\gcd(a,a')E$, because multiplication by a nonzero integer is an isogeny and does not change the maximal connected abelian subvariety on which $E$ vanishes. Therefore (3.1) is independent of the denominator.

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

### 3.5 The exact abelian quotient

The quotient $A_{\mathfrak m}=J/K$ is more useful than an arbitrary abelian variety isogenous to the image of $E$ because its kernel is connected. We now record the exactness that connectedness buys.

Over $\mathbf Q$ there is an fppf exact sequence

$$
0\longrightarrow K\longrightarrow J
\xrightarrow{\pi}A_{\mathfrak m}\longrightarrow0. \tag{3.2}
$$

For every positive integer $n$, it induces

$$
0\longrightarrow K[n]\longrightarrow J[n]
\xrightarrow{\pi}A_{\mathfrak m}[n]\longrightarrow0. \tag{3.3}
$$

The surjectivity at the right is worth proving. Let $y$ be an $n$-torsion point of the quotient over a test scheme. Fppf-locally, lift it to $x\in J$. Then $nx$ lies in $K$. Multiplication by $n$ on the abelian variety $K$ is faithfully flat, so after a further fppf cover there is $k\in K$ with $nk=nx$. The point $x-k$ belongs to $J[n]$ and still maps to $y$. Its ambiguity is exactly $K[n]$. This proves (3.3) as a sequence of group schemes, without counting geometric points.

The same argument works over $S$, but exactness of the integral abelian sequence deserves justification. Locally at every prime different from $N$, the abelian subvariety $K$ and the quotient $A_{\mathfrak m}$ have good reduction because good reduction is stable under abelian subvarieties and quotients. Their maps extend uniquely between the abelian-scheme models.

Choose a Poincare complementary homomorphism $s:A_{\mathfrak m}\to J$ and an integer $d>0$ such that

$$
\pi s=[d]_{A_{\mathfrak m}}. \tag{3.4}
$$

Both maps extend over the good-reduction base. Since multiplication by $d$ is faithfully flat on every abelian scheme, (3.4) makes $\pi:\mathcal J\to\mathcal A_{\mathfrak m}$ fiberwise surjective. Its fibers have constant dimension $\dim K$; the fiberwise flatness criterion, applied to the smooth source and target, makes $\pi$ faithfully flat.

We now use the relative-kernel decomposition, whose proof in this case is as follows. If $f:X\to Y$ is a faithfully flat homomorphism of abelian schemes over a DVR, put $H=\ker(f)$. The schematic closure in $H$ of the generic identity component is stable under multiplication and inverse. Translating its smooth locus by sections over a strict henselization shows that this locus meets every geometric fiber in a connected proper subgroup of the generic relative dimension. The fiberwise flatness criterion then makes the closure flat, while rigidity extends the group law from the dense smooth locus. It is proper and smooth with geometrically connected fibers, hence is an abelian scheme $H^{\mathrm{ab}}$. The quotient

$$
0\longrightarrow H^{\mathrm{ab}}\longrightarrow H
\longrightarrow D\longrightarrow0
$$

has relative dimension zero. Properness and flatness make $D$ finite flat, and its generic fiber is the component group of $H_{\mathbf Q}$. This last quotient must be kept finite flat: at a residue characteristic it need not be etale.

Apply the decomposition to $H=\ker(\pi)$. Its generic fiber is the connected abelian variety $K$, so $D$ has trivial generic fiber. A finite-flat group over a connected DVR has constant rank; hence $D$ has rank one and is trivial. Thus the whole kernel is an abelian scheme with generic fiber $K$, and uniqueness of the good model identifies it with $\mathcal K$. Repeating this argument at every localization of the Dedekind base gives

$$
0\longrightarrow\mathcal K\longrightarrow\mathcal J
\xrightarrow{\pi}\mathcal A_{\mathfrak m}\longrightarrow0 \tag{3.5}
$$

is exact over $S$, and for every $r$,

$$
0\longrightarrow\mathcal K[\ell^r]
\longrightarrow\mathcal J[\ell^r]
\longrightarrow\mathcal A_{\mathfrak m}[\ell^r]
\longrightarrow0 \tag{3.6}
$$

is fppf exact. This is an exact sequence of torsion of abelian schemes. It is not obtained by taking the kernel of a random endomorphism of a Neron model.

Passing to inverse limits on geometric generic fibers gives an exact sequence of free $\mathbf Z_\ell$-modules

$$
0\longrightarrow T_\ell K
\longrightarrow T_\ell J
\longrightarrow T_\ell A_{\mathfrak m}
\longrightarrow0. \tag{3.7}
$$

Surjectivity survives the inverse limit because the finite transition maps are surjective. Equivalently, (3.6) already says that the quotient lattice $T_\ell A_{\mathfrak m}$ is the honest quotient of $T_\ell J$, not merely a commensurable lattice in the same rational representation.

### 3.6 Saturation of the selected Tate lattice

We can now prove the statement that is lost if one reasons only with rational projectors.

**Theorem 3.1 (integral saturation).** The quotient map induces an isomorphism

$$
eT_\ell J\xrightarrow{\sim}eT_\ell A_{\mathfrak m}. \tag{3.8}
$$

In particular its image is saturated, and for every $r\geq1$ it induces an isomorphism on the corresponding $e$-parts modulo $\ell^r$.

**Proof strategy.** Apply the integral idempotent to the exact sequence (3.7). The only point is to show that its part on the connected kernel vanishes integrally. Rational support gives this after tensoring with $\mathbf Q_\ell$; torsion-freeness of the Tate lattice then removes the possible finite error.

**Proof.** The support of $K$ is complementary to $E$. Hence $E$ acts as zero on

$$
T_\ell K\otimes_{\mathbf Z_\ell}\mathbf Q_\ell.
$$

Since $eE=e$, the idempotent $e$ also acts as zero on this rational vector space. The module $eT_\ell K$ is a submodule of the free $\mathbf Z_\ell$-module $T_\ell K$. It is therefore torsion-free. Its scalar extension to $\mathbf Q_\ell$ is zero, so

$$
eT_\ell K=0. \tag{3.9}
$$

Applying the exact direct-summand functor $e(-)$ to (3.7) now gives

$$
0\longrightarrow0\longrightarrow eT_\ell J
\longrightarrow eT_\ell A_{\mathfrak m}
\longrightarrow0.
$$

This proves (3.8). Reducing an isomorphism of finite free $\mathbf Z_\ell$-modules modulo $\ell^r$ proves the finite-level assertion. $\square$

The proof did not claim that $e$ is rational. It used $E$ to construct the connected quotient and used $e$ only after passing to the $\ell$-adic exact sequence. If a coefficient field has several primes above $\ell$, all of them remain in $A_{\mathfrak m}$, while (3.8) extracts exactly the chosen prime. This is the promised resolution of the companion-prime problem.

There is a useful lattice reformulation. Let

$$
L=T_\ell J,\qquad L_A=T_\ell A_{\mathfrak m}.
$$

The rational map identifies $e(L\otimes\mathbf Q_\ell)$ with $e(L_A\otimes\mathbf Q_\ell)$. Theorem 3.1 asserts the stronger equality of integral lattices

$$
\pi(eL)=eL_A, \tag{3.10}
$$

not merely finite index. Thus there is no residual isogeny kernel to be carried through the later finite-flat arguments.

## 4. The completed Hecke piece

We now apply the local idempotent to finite-flat group schemes. This reverses a common but unsafe order of reasoning: flatness is not deduced from a Hecke kernel. Instead, an idempotent first splits the ambient torsion group, and the desired group is one of the two direct factors. The compatible ambient multiplication sequences then supply divisibility at every level.

### 4.1 Finite-level projectors

For every $r\ge1$, the group $\mathcal J[\ell^r]$ is finite locally free over $S$. The action of $\mathbb T$ on $\mathcal J$ induces an action of

$$
\mathbb T/\ell^r\mathbb T
$$

on this group. Reduce $e\in\mathbb T_\ell$ modulo $\ell^r$ and define

$$
G_r=e\mathcal J[\ell^r]. \tag{4.1}
$$

This image is represented without any flatness argument: the complementary idempotent gives an isomorphism

$$
\mathcal J[\ell^r]
\xrightarrow{\sim}
G_r\times (1-e)\mathcal J[\ell^r],
\qquad x\longmapsto(ex,(1-e)x). \tag{4.2}
$$

The inverse adds the two components. Thus $G_r$ is finite locally free and both its inclusion and projection are Hecke equivariant. This is stronger than taking the schematic closure of a generic local summand: it constructs the summand simultaneously in every fiber.

Because the base is connected, the rank is constant. On the generic fiber, $e$ projects a free $\mathbf Z_\ell$-Tate lattice of some rank $h$, so

$$
\operatorname{rank}_S G_r=\ell^{rh}. \tag{4.3}
$$

The integer $h$ is the height of the completed piece. No rank-two or multiplicity-one assertion is hidden in this notation.

### 4.2 Exact transition maps

Multiplication by $\ell^r$ on the ambient divisible group gives an exact sequence

$$
0\longrightarrow\mathcal J[\ell^r]
\longrightarrow\mathcal J[\ell^{r+s}]
\xrightarrow{\ell^r}\mathcal J[\ell^s]
\longrightarrow0. \tag{4.4}
$$

The projector $e$ commutes with multiplication. Applying the exact direct-summand functor $e(-)$ to (4.4) gives

$$
0\longrightarrow G_r
\longrightarrow G_{r+s}
\xrightarrow{\ell^r}G_s
\longrightarrow0. \tag{4.5}
$$

Exactness here is fppf exactness. In particular the last arrow is faithfully flat and its kernel is exactly $G_r$. This checks the divisibility condition that a mere nested tower would not provide.

Taking $s=1$ also shows that the transition map $\ell:G_{r+1}\to G_r$ is faithfully flat with kernel $G_1$. Induction recovers (4.5), so either family of exactness statements can be used as the finite-level criterion.

### 4.3 The resulting divisible group

Define

$$
G_{\mathfrak m}=\varinjlim_rG_r. \tag{4.6}
$$

Equations (4.3) and (4.5) prove that this is an $\ell$-divisible group of height $h$ over $S$. Its $\ell^r$-torsion is precisely $G_r$. Formation commutes with base change because torsion, the Hecke action, and the direct-summand decomposition (4.2) do.

Cartier duality also commutes with the projector. If the principal polarization identifies $\mathcal J[\ell^\infty]^D$ with $\mathcal J[\ell^\infty]$, then

$$
G_{\mathfrak m}^D\simeq e^\dagger\mathcal J[\ell^\infty], \tag{4.7}
$$

where $e^\dagger$ is the Rosati adjoint. For the prime-level Hecke algebra $e^\dagger=e$, so the completed piece is self-dual, though the induced polarization can be only a quasi-polarization if one passes through a nonprincipal quotient model.

### 4.4 Comparison with the selected quotient

The saturation theorem removes the ambiguity that usually accompanies a passage from a rational support to an integral quotient. The optimal quotient map induces

$$
G_{\mathfrak m}\longrightarrow
\mathcal A_{\mathfrak m}[\ell^\infty]_{\mathfrak m}, \tag{4.8}
$$

where the right side means the $e$-direct factor, not the kernel of a possibly nonflat ideal action. By Theorem 3.1 this map is an isomorphism. At level $r$ it is the restriction of (3.6) to direct factors and gives

$$
e\mathcal J[\ell^r]
\xrightarrow{\sim}
e\mathcal A_{\mathfrak m}[\ell^r]. \tag{4.9}
$$

To see the integral assertion directly, apply $e$ to (3.6). Its kernel is $e\mathcal K[\ell^r]$. The Tate-lattice calculation (3.9) says that the generic fiber of this kernel is zero. But $e\mathcal K[\ell^r]$ is a finite-flat direct summand of $\mathcal K[\ell^r]$. A finite-flat group over the connected base $S$ with trivial generic fiber has rank one and is the zero group. Hence the kernel vanishes. The $e$-part of the last map in (3.6) remains faithfully flat, and equal ranks make it an isomorphism.

Thus one may construct the completed piece inside $\mathcal J$ and then identify it with the selected part of the quotient, or construct the quotient first and apply its local idempotent. The first route makes finite flatness transparent; the second makes the geometric meaning transparent.

### 4.5 Equality of the two finite-flat towers

It is useful to distinguish three statements that are sometimes all called “the selected quotient.”

First, the rational projector $E$ defines the abelian quotient $A_{\mathfrak m}$. Second, the local projector $e$ defines the finite-flat tower $G_r$ inside $\mathcal J[\ell^r]$. Third, the same $e$ acts on the torsion of $\mathcal A_{\mathfrak m}$. The exact comparison just proved identifies the second and third towers:

$$
\left(e\mathcal J[\ell^r]\right)_{r\geq1}
\simeq
\left(e\mathcal A_{\mathfrak m}[\ell^r]\right)_{r\geq1}. \tag{4.10}
$$

The isomorphisms commute with multiplication by $\ell$, with Hecke operators, with arbitrary base change from $S$, and with Cartier duality after applying the Rosati adjoint to the idempotent. Consequently every later filtration may be built in either ambient abelian scheme without changing its integral model.

This conclusion would fail for a nonoptimal isogenous representative of the rational support. If one first replaced $A_{\mathfrak m}$ by an abelian variety linked to it through an $\ell$-power isogeny, the induced Tate lattice could have finite index and the finite levels could differ by nontrivial kernels. Optimality is therefore not merely a convenient normalization. Its connected kernel is the geometric source of the saturated lattice in (3.8).

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

Apply the idempotent $e$ on both sides. If $t\in e\mathbb T_\ell=\mathbb T_{\mathfrak m}$ acts trivially on $eT_\ell J$, it acts trivially on $(1-e)T_\ell J$ because $t(1-e)=0$. Hence it acts trivially on the whole Tate module, and (5.1) gives $t=0$. We have proved

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
\simeq\mathbf Z_\ell/\ell^e\mathbf Z_\ell \tag{5.4}
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
=eJ[\ell](\overline{\mathbf Q}). \tag{6.2}
$$

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

Book 121 gives the integral Eichler--Shimura identity on the full Tate module. Reducing it modulo $\ell$ and passing to $W_j$ gives

$$
\left(\operatorname{Frob}_q-1\right)
\left(\operatorname{Frob}_q-q\right)=0
\quad\text{on }W_j \tag{6.7}
$$

for every prime $q\nmid N\ell$. Here $q$ in the second factor means its image in $\mathbf F_\ell$, equivalently $\bar\chi_\ell(\operatorname{Frob}_q)$. Equation (6.7), not a numerical trace, will force the required constituents.

The distinction between $V$ and $J[\mathfrak m]$ is important. The latter is killed by the maximal ideal; the former is the entire generalized local summand and can contain nontrivial Hecke-nilpotent extensions. Filtration (6.4) retains those extensions while reducing their successive layers to honest Eisenstein eigenspaces.

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

The theorem does not compute multiplicities. If the dimension of $V$ is $h$, it supplies $h$ one-dimensional factors, but it does not say how many are trivial and how many are cyclotomic. That count will be obtained integrally from the connected--etale sequence, and self-duality will equate the two counts. Nor does the theorem identify a canonical first line. The cuspidal and Shimura groups give geometric lines in particular levels, while a composition series of the whole local block remains noncanonical.

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

Book 63 proves a powerful descent theorem: a continuous representation with absolutely irreducible residual representation descends, after strict conjugacy, to its closed trace algebra. Every word in the absolute-irreducibility hypothesis matters. Burnside density is used to make residual group matrices span a full matrix algebra; that matrix algebra is then split by Henselian lifting.

The Eisenstein residual system has the opposite shape. Its expected simple factors are $1$ and $\bar\chi_\ell$, so it is reducible; at $\ell=2$ the two factors even coincide. Burnside density therefore does not apply. The diagonal counterexamples in Book 63 show that trace containment without absolute irreducibility cannot be repaired by a change of basis. Carayol descent supplies neither a stable line nor a filtration in the present setting.

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

Fix $r$. Each $G_r$ is contained in the torsion of the abelian scheme $\mathcal J/S$. Close the terms of the generic stable filtration successively inside $G_r$ and inside the successive quotients. Over the Dedekind scheme $S$, saturated schematic closure of a generic subgroup in a finite-flat group is finite flat, and its quotient is finite flat. We obtain

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

The unramified hypothesis is indispensable. Over a dyadic DVR of ramification index greater than one, Oort--Tate exponents can lie strictly between $0$ and $e$, producing local-local order-two models with the same trivial generic character. The present base has completion $\mathbf Z_2$, so those intermediate models do not occur.

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

The admissibility of isolated levels would be insufficient if multiplication carried an integral atom to a nonflat image. Here multiplication $G_{r+1}\to G_r$ is faithfully flat by (4.5). Its kernel is $G_1$, already admissible. Pulling a filtration of $G_r$ back along this map and inserting a filtration of the kernel gives an admissible filtration of $G_{r+1}$ compatible with the transition map.

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

For an admissible group, every connected order-$\ell$ constituent over $R$ is $\mu_\ell$, and every etale constituent is constant. Cartier duality turns the connected part into an etale group filtered by constant atoms. An $\ell$-divisible group over a complete DVR is etale precisely when its level-one group is etale. Hence $(G_{\mathfrak m}^0)^D$ is etale, so $G_{\mathfrak m}^0$ is of multiplicative type.

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

The integers $a$ and $b$ are intrinsic. Self-duality of the completed piece gives $a=b$ when the polarization pairs the selected factor with itself. Thus $h=a+b=2a$ in the self-dual case.

Sequence (8.3) need not split over $\mathbf Z_\ell$, and it need not spread to a global sequence over $S$ with split multiplicative kernel and constant quotient. Global monodromy away from $\ell$ can obstruct such a separation. Whenever the global Shimura closure and cuspidal quotient supply an actual separation, the extension calculation of Book 144 applies.

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

Self-duality deserves an integral argument. The principal polarization of $J$ gives a perfect Cartier pairing on the full $\ell$-divisible group. Rosati fixes the prime-level Hecke algebra, hence fixes $e$, so the orthogonal complement of the $e$-summand is the $(1-e)$-summand. Restriction gives

$$
G_{\mathfrak m}^D\simeq G_{\mathfrak m}. \tag{8.7}
$$

Duality exchanges the etale quotient and the multiplicative subgroup. It therefore exchanges heights $a$ and $b$. Equality (8.7) forces

$$
a=b,
\qquad h=2a. \tag{8.8}
$$

This is a multiplicity equality, but it is not complete multiplicity one. The common integer $a$ can exceed one, and nothing here makes the Tate module free of rank two over $\mathbb T_{\mathfrak m}$.

### 8.5 Ordinary structure without a chosen splitting

An $\ell$-divisible group over a perfect field is ordinary when only the etale slope zero and multiplicative slope one occur. Sequence (8.3) shows that the special fiber of the completed Eisenstein piece is ordinary. Every finite connected constituent is multiplicative, so no local-local slope can occur; every quotient constituent is etale. Thus the Newton slopes are

$$
0^a,1^b,
$$

and in the self-dual case $0^a,1^a$.

Over the algebraic closure of the residue field, the ordinary connected--etale sequence splits canonically at the special fiber. Over $\mathbf Z_\ell$, it generally does not split. Its extension class is precisely integral information invisible in the semisimplified generic Galois representation. This is why the conclusion of the book is an exact sequence rather than a product decomposition.

The distinction may be seen already at height two. Both

$$
\mu_{\ell^\infty}\oplus\mathbf Q_\ell/\mathbf Z_\ell
$$

and a nonsplit ordinary extension have one slope of each kind and the same semisimplified generic characters. Their finite levels have the same atomic multiplicities. They differ in the extension class joining those atoms. At odd $\ell$, Book 144 calculates a global height-two class only after a multiplicative subgroup and a constant quotient have actually been separated. The local ordinary sequence supplies such an orientation over $\mathbf Z_\ell$; it does not automatically globalize it over $S$.

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

Taking $\ell$-primary parts yields cyclic groups of order $\ell^e$. Since the other local Hecke idempotents annihilate an $\mathfrak m$-primary group, both lie in the generic fiber of $G_e$.

### 9.2 Their closures in the completed piece

Let $\mathcal C_{\ell}$ and $\mathcal\Sigma_{\ell}$ be their closures in $G_e$. They are finite flat. For odd $\ell$, closing the unique cyclic subgroup of each order gives filtrations

$$
0=\mathcal C_0\subset\cdots\subset\mathcal C_e=\mathcal C_\ell,
\qquad
\mathcal C_i/\mathcal C_{i-1}\simeq\underline{\mathbf Z/\ell}, \tag{9.2}
$$

and

$$
0=\mathcal\Sigma_0\subset\cdots\subset\mathcal\Sigma_e=\mathcal\Sigma_\ell,
\qquad
\mathcal\Sigma_i/\mathcal\Sigma_{i-1}\simeq\mu_\ell. \tag{9.3}
$$

At $2$, closing the same cyclic chains gives filtrations in which every factor is one of the two atoms by Proposition 7.1. The generic character does not determine which factors in the cuspidal closure are constant or which factors in the Shimura closure are multiplicative. Accordingly, (9.2)--(9.3) are asserted with their displayed orientations only for odd $\ell$.

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

The completed idempotent, the groups $G_r$, the divisible group $G_{\mathfrak m}$, the connected--etale sequence, and the heights $a,b$ are canonical. The optimal quotient is canonical once the rational support is fixed.

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
\simeq\mathbf Z_\ell/\ell^e\mathbf Z_\ell. \tag{10.1}
$$

All other factors above $\ell$ vanish after quotienting by $I$. The $\mathbf Z_\ell$-length of (10.1) is $e$. This is the precise depth of the scalar Eisenstein congruence.

### 10.2 Control modulo powers

Because $G_r$ is killed by $\ell^r$, its continuous action factors through

$$
\mathbb T_{\mathfrak m}/\ell^r\mathbb T_{\mathfrak m}.
$$

Reduction of the idempotent decomposition modulo $\ell^r$ shows that forming $G_r$ commutes with reduction of the Hecke algebra. Explicitly,

$$
G_r=e(\mathcal J[\ell^r])
=\ker(1-e:\mathcal J[\ell^r]\to\mathcal J[\ell^r]). \tag{10.2}
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
+\ell^{\min(r,e)}\mathbb T_{\mathfrak m}
$$

on the $\mathfrak m$ factor. This formula concerns the cyclic cuspidal line, not the entire $G_r$.

### 10.4 Base change and duality

For any $S$-scheme $S'$, the identity (4.2) base changes to the corresponding identity over $S'$. Thus

$$
G_r\times_SS'=e(\mathcal J_{S'}[\ell^r]). \tag{10.4}
$$

Flatness or connectedness hypotheses are not needed for this projector identity. Connected--etale decomposition, however, is used over a henselian or complete local base. We therefore state (8.3) only after base change to $\mathbf Z_\ell$.

Cartier duality changes the Hecke action by Rosati adjunction. Since the prime-level generators are self-adjoint in the chosen normalization, $I$ and $\mathfrak m$ are stable and the dual of the selected piece is selected again. Constant and multiplicative factors are exchanged, and atomic extension orientation is reversed.

## 11. Exceptional levels and exceptional primes

The construction has two different exceptional directions: the removed level prime $N$ and the residue characteristic $\ell$ of the completed factor. Their geometry must not be mixed. Small levels can make the Eisenstein factor vanish, while the primes two and three alter the exact index and, at two, the integral recognition of endpoint models.

### 11.1 The level prime

An Eisenstein prime $\ell$ divides $n_N$, hence divides $N-1$. Therefore $\ell\ne N$. This elementary observation is indispensable: it places the connected--etale analysis at a good-reduction prime and lets $\mathcal J[\ell^r]$ be finite flat over $S$.

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

Fix $\ell\mid n_N$ and $\mathfrak m=(\ell,I)$. Then the following hold.

1. The finite algebra $\mathbb T\otimes\mathbf Z_\ell$ has a unique idempotent $e_{\mathfrak m}$ selecting its $\mathfrak m$-factor, and

   $$
   e_{\mathfrak m}(\mathbb T\otimes\mathbf Z_\ell)
   =\mathbb T_{\mathfrak m}.
   $$

2. The corresponding rational support defines an optimal abelian quotient $A_{\mathfrak m}$ of $J_0(N)$. Its Neron model restricts to an abelian scheme over $S$, and the definition is independent of the denominator used to realize the rational projector. Companion local factors above $\ell$ are retained by the rational quotient and removed only by applying $e_{\mathfrak m}$ to its $\ell$-power torsion.

3. For every $r\ge1$,

   $$
   G_r=e_{\mathfrak m}\mathcal J[\ell^r]
   $$

   is a finite-flat direct summand of $\mathcal J[\ell^r]$. For all $r,s\ge1$ there is an exact sequence

   $$
   0\to G_r\to G_{r+s}
   \xrightarrow{\ell^r}G_s\to0.
   $$

4. The optimal quotient map has saturated selected Tate lattice:

   $$
   e_{\mathfrak m}T_\ell J
   \xrightarrow{\sim}
   e_{\mathfrak m}T_\ell A_{\mathfrak m}.
   $$

   Consequently

   $$
   G_r\xrightarrow{\sim}
   e_{\mathfrak m}\mathcal A_{\mathfrak m}[\ell^r]
   $$

   at every level. In particular $G_{\mathfrak m}=\varinjlim_rG_r$ is the actual $\mathfrak m$-part of the quotient's $\ell$-divisible group, not merely an isogenous model.

5. The continuous action

   $$
   \mathbb T_{\mathfrak m}\hookrightarrow
   \operatorname{End}(G_{\mathfrak m})
   $$

   is faithful, and the intersection of the finite-level annihilators is zero.

6. The generic module $G_1(\overline{\mathbf Q})$ has an actual Galois- and Hecke-stable composition series with factors $\mathbf F_\ell$ and $\mathbf F_\ell(1)$. It is obtained from the Hecke-radical filtration and the integral Eichler--Shimura annihilating polynomial, not from trace or semisimplification. Pullback through the torsion tower gives compatible such filtrations at every level.

7. Every $G_r$ is Eisenstein-admissible: it has a finite-flat filtration with factors $\underline{\mathbf Z/\ell}$ and $\mu_\ell$. For odd $\ell$ the generic characters determine the endpoint types. At $2$, the unramified Oort--Tate classification proves that every order-two closure is one of the two endpoints, with its label determined by connectedness after closure.

8. Over $\mathbf Z_\ell$ there is a canonical exact sequence

   $$
   0\to G_{\mathfrak m}^{\mathrm{mult}}
   \to G_{\mathfrak m}
   \to G_{\mathfrak m}^{\mathrm{et}}
   \to0.
   $$

   The endpoint heights equal the multiplicative and constant lengths in any admissible level-one filtration. If the selected piece is self-dual, the two heights are equal.

9. The $\ell$-primary cuspidal and Shimura groups have order $\ell^e$, lie in $G_e$ on the generic fiber, and have finite-flat closures. For odd $\ell$, their canonical cyclic filtrations have respectively constant and multiplicative factors. At $2$, each factor is an Eisenstein atom, but its orientation is not inferred from the common generic character. No theorem about the full intersection of the two closures is used.

10. A separated atomic subquotient with multiplicative kernel and constant quotient is classified, for odd $\ell$, by

   $$
   \operatorname{Ext}^1_S(
   \underline{\mathbf Z/\ell},\mu_\ell)
   \simeq\langle[N]\rangle.
   $$

   The dyadic extension has the additional carry and sign data described in Section 9.3.

11. The completed Eisenstein quotient is

   $$
   \mathbb T_{\mathfrak m}/I\mathbb T_{\mathfrak m}
   \simeq\mathbf Z_\ell/\ell^{v_\ell(n_N)}\mathbf Z_\ell.
   $$

   This controls the scalar Eisenstein depth but asserts neither complete multiplicity one nor freeness of the Tate module over the local Hecke algebra.

**Proof.** Items 1 and 11 follow from the finite-algebra decomposition of Chapter 2 and the exact global Eisenstein index. The rational quotient and its good model are constructed in Chapter 3. The exact torsion sequence of its connected kernel and Theorem 3.1 prove the saturation assertion in item 4, including all finite levels. Item 3 and divisibility follow from the direct-summand identity (4.2) and exact sequence (4.5). Faithfulness is (5.2).

For item 6, filter the generalized residual summand by the radical of $\mathbb T_{\mathfrak m}/\ell$. On each layer Eichler--Shimura becomes the operator identity $(F_q-1)(F_q-q)=0$. Chebotarev and Lemma 6.1 force every simple Galois factor to be trivial or cyclotomic. Chapter 7 closes the resulting actual flag. Odd-prime rigidity and Proposition 7.1 identify all closures as Eisenstein atoms, proving item 7. The connected--etale sequence and Cartier-dual recognition prove item 8. The exact cusp and Shimura calculations give item 9 within its stated odd and dyadic boundaries. The flat Kummer calculation gives item 10. No step uses a nonflat Hecke kernel, a rational form of the local projector, or an inference from trace to reducibility. $\square$

### 12.2 Dependency ledger

The construction uses each prerequisite within its stated range.

Book 38 supplies finite-flat multiplication kernels of abelian schemes, faithfully flat multiplication, finite quotient exactness, extension of homomorphisms over normal good-reduction bases, duality, Weil pairings, and polarization adjunction. In Chapter 3 these facts are applied to the connected abelian kernel $K$, not to the kernel of an arbitrary Hecke operator. The positive-dimensional relative-kernel decomposition needed to extend the optimal exact sequence is proved in Section 3.5; it is not attributed to the finite-kernel quotient theorem. The fppf lifting proof of (3.3) is the precise reason the generic Tate quotient is saturated.

Book 39 supplies Neron models, unique extension of Hecke endomorphisms, properness as the criterion for good reduction, component specialization, and the warning that a Neron extension of an isogeny need not be finite at a bad place. We restrict all torsion constructions to $S$, where the Neron models are abelian schemes. The level-prime component group is used only to state primitivity of the cusp; it is never confused with an $\ell$-adic lattice at a different prime.

Book 46 supplies faithfully flat exact sequences of finite-flat groups, represented quotients, rank multiplication, primary decomposition, and saturated schematic closure in a fixed finite-flat ambient group over a Dedekind base. Chapter 7 uses precisely that closure theorem. It never forms an arbitrary scheme-theoretic Hecke kernel and calls it flat.

Book 47 supplies exact Cartier duality, the exchange of constant and multiplicative groups, annihilator filtrations, compatibility of closure with annihilators, and perfect duality on abelian torsion. These results identify the multiplicative part from the dual etale quotient and prove the equality of endpoint heights under self-duality.

Book 56 supplies Oort--Tate classification, height-one low-ramification rigidity, the unramified endpoint theorem, and the dyadic warning. For odd $\ell$, $1<\ell-1$ identifies an order-$\ell$ closure from its generic character. For $\ell=2$, the same inequality is unavailable, but the exponent interval over $\mathbf Z_2$ is $\{0,1\}$; Proposition 7.1 uses that complete classification rather than a character label.

Book 60 supplies the finite-level criterion for an $\ell$-divisible group, connected--etale sequences over complete local bases, height and dimension, Cartier duality at infinite level, and recognition of etale and multiplicative divisible groups. Exact sequence (4.5) verifies the required faithful flatness. Admissibility rules out local-local factors before we call the special fiber ordinary.

Book 62 supplies completion as an inverse limit, exactness for finite modules, lifting of idempotents through nilpotent quotients, and separation of completed actions. Together with the finite-algebra decomposition recalled in Book 91, it turns $\mathbb T\otimes\mathbf Z_\ell$ into the product of its complete local factors. We apply this only to the finite torsion-free acting Hecke algebra; no uncontrolled infinite algebra is treated as Noetherian.

Book 63 supplies Carayol descent only under residual absolute irreducibility. Section 6.6 checks that this hypothesis fails in the Eisenstein problem and therefore does not invoke the theorem. Its counterexamples explain why traces cannot supply the missing stable flag. The replacement proved here is the Hecke-radical and quadratic-density argument.

Book 91 supplies the acting-image convention, faithfulness after localization, generalized local summands, compatible idempotents, and the distinctions among localization, quotient, ordinary eigenspace, and multiplicity one. The radical filtration (6.4) is necessary precisely because the completed summand can be larger than $J[\mathfrak m]$. No reduction of a faithful integral action is assumed faithful without proof.

Book 121 supplies the integral Hecke action on the modular Jacobian and its Neron model, Rosati adjunction, the good-prime Eichler--Shimura identity

$$
F_q^2-T_qF_q+q=0
$$

on every prime-to-$q$ torsion level, and the explicit warning that it is an annihilating polynomial before any rank-two theorem is known. This operator identity is the decisive Galois input in Chapter 6. Finite Chebotarev density is applied only to the finite quotient cut out by the residual module together with $\bar\chi_\ell$.

Book 142 supplies the faithful prime-level acting algebra, the Eisenstein ideal with $U_N-1$, and the exact quotient $\mathbb T/I\simeq\mathbf Z/n_N\mathbf Z$, including the two- and three-primary exponents. This identifies the residue field and the scalar action on each Hecke-radical layer. It supplies no multiplicity, branch count, Gorenstein property, or stable Galois flag, and none is attributed to it.

Book 143 supplies the exact order and Hecke action of the cuspidal line, its isomorphic specialization in the component group, and the cyclic diagonalizable Shimura kernel of order $n_N$. These objects give named generic subgroups and oriented odd-prime filtrations. We use no theorem about all rational torsion or about the full cuspidal--Shimura intersection.

Book 144 supplies the admissible exact category over $\mathbf Z[1/N]$, the closure criterion for an actual stable generic flag, odd-prime endpoint recognition, filtration independence, inheritance under finite-flat subquotients, and the mixed atomic extension calculation. Its explicitly missing hypothesis is supplied by Theorem 6.2. Its dyadic warning is respected: characters do not label endpoints; Proposition 7.1 instead classifies the actual closures over the unramified base.

The new arguments in this book are therefore sharply located. Section 3.5 proves that the connected optimal kernel remains the whole kernel over the good-reduction base. Theorem 3.1 then proves integral saturation for the optimal quotient and local idempotent. Theorem 6.2 proves the full generic Eisenstein filtration from the radical layers and the Eichler--Shimura operator identity. None of these assertions is imported from an index calculation or a trace-descent theorem.

### 12.3 Conclusion

The completed Eisenstein piece is not obtained by writing an ideal inside a kernel. It is obtained by turning the complete local Hecke factor into an idempotent and applying that idempotent to the entire abelian-scheme torsion tower. This one choice simultaneously resolves flatness, compatibility, and divisibility:

$$
\mathcal J[\ell^r]
=G_r\times(1-e_{\mathfrak m})\mathcal J[\ell^r],
$$

and multiplication carries these decompositions into one another through faithfully flat exact sequences.

The rational and local selections then agree integrally. The rational projector retains every coefficient-field conjugate required to define an abelian quotient. The local idempotent selects one completion on the Tate lattice. Exactness of the optimal quotient and vanishing of the complementary $e$-kernel prove that the two selected lattices are equal, even when a rational field factor has several primes above $\ell$.

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

This is the integral package required for Eisenstein descent: an optimal quotient with a good Neron model over $S$, a saturated identification with the canonical completed Hecke summand, finite-flat torsion at every power, exact transition maps, an actual generic Eisenstein flag, admissible constant and multiplicative constituents, controlled atomic extensions, and a faithful complete local endomorphism action. None of these conclusions requires complete multiplicity one, a full Shimura-intersection theorem, a rational incarnation of the local idempotent, or Carayol descent outside its absolutely irreducible range.
