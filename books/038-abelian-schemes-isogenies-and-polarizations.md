# Abelian Schemes, Isogenies, and Polarizations

## Contents

1. [The geometry carried by a proper group](#1-the-geometry-carried-by-a-proper-group)
   - [The organizing questions](#11-the-organizing-questions)
   - [Conventions and standing hypotheses](#12-conventions-and-standing-hypotheses)
   - [Rigidity and its first consequences](#13-rigidity-and-its-first-consequences)
   - [Fibers, dimension, and base change](#14-fibers-dimension-and-base-change)
2. [Line bundles on an abelian scheme](#2-line-bundles-on-an-abelian-scheme)
   - [Why translation is the correct probe](#21-why-translation-is-the-correct-probe)
   - [Rigidification and the theorem of the square](#22-rigidification-and-the-theorem-of-the-square)
   - [The theorem of the cube](#23-the-theorem-of-the-cube)
   - [Symmetry and pullback by multiplication](#24-symmetry-and-pullback-by-multiplication)
   - [Algebraic triviality and numerical triviality](#25-algebraic-triviality-and-numerical-triviality)
3. [The dual abelian scheme](#3-the-dual-abelian-scheme)
   - [The moduli problem](#31-the-moduli-problem)
   - [Representability and the Poincare bundle](#32-representability-and-the-poincare-bundle)
   - [The biextension laws](#33-the-biextension-laws)
   - [Functoriality and biduality](#34-functoriality-and-biduality)
   - [Products and examples](#35-products-and-examples)
4. [Homomorphisms and isogenies](#4-homomorphisms-and-isogenies)
   - [Rigidity of maps](#41-rigidity-of-maps)
   - [Equivalent definitions of an isogeny](#42-equivalent-definitions-of-an-isogeny)
   - [Multiplication maps and torsion](#43-multiplication-maps-and-torsion)
   - [Degree and composition](#44-degree-and-composition)
   - [Dual homomorphisms and dual isogenies](#45-dual-homomorphisms-and-dual-isogenies)
5. [Quotients by finite subgroup schemes](#5-quotients-by-finite-subgroup-schemes)
   - [Why a sheaf quotient is unavoidable](#51-why-a-sheaf-quotient-is-unavoidable)
   - [Construction of the quotient](#52-construction-of-the-quotient)
   - [The quotient theorem](#53-the-quotient-theorem)
   - [Universal properties and base change](#54-universal-properties-and-base-change)
   - [Successive quotients](#55-successive-quotients)
6. [Kernels and duality](#6-kernels-and-duality)
   - [The character hidden in a trivialized pullback](#61-the-character-hidden-in-a-trivialized-pullback)
   - [Kernel of the dual isogeny](#62-kernel-of-the-dual-isogeny)
   - [Annihilators and exact sequences](#63-annihilators-and-exact-sequences)
   - [The dual-isogeny identities](#64-the-dual-isogeny-identities)
7. [Weil pairings](#7-weil-pairings)
   - [Construction from the Poincare bundle](#71-construction-from-the-poincare-bundle)
   - [Bilinearity, functoriality, and base change](#72-bilinearity-functoriality-and-base-change)
   - [Perfectness in every characteristic](#73-perfectness-in-every-characteristic)
   - [Compatibility through levels](#74-compatibility-through-levels)
   - [The prime-to-characteristic pointwise picture](#75-the-prime-to-characteristic-pointwise-picture)
8. [Polarizations](#8-polarizations)
   - [From an ample line bundle to a homomorphism](#81-from-an-ample-line-bundle-to-a-homomorphism)
   - [Intrinsic characterization](#82-intrinsic-characterization)
   - [Symmetry, type, and degree](#83-symmetry-type-and-degree)
   - [Principal polarizations](#84-principal-polarizations)
   - [The induced alternating pairing](#85-the-induced-alternating-pairing)
9. [Polarized isogenies and isotropic kernels](#9-polarized-isogenies-and-isotropic-kernels)
   - [Pulling back a polarization](#91-pulling-back-a-polarization)
   - [Descent across a quotient](#92-descent-across-a-quotient)
   - [Orthogonal kernels](#93-orthogonal-kernels)
   - [Maximal isotropic quotients](#94-maximal-isotropic-quotients)
10. [Extension over normal bases](#10-extension-over-normal-bases)
    - [Why normality is the threshold](#101-why-normality-is-the-threshold)
    - [Extension of homomorphisms](#102-extension-of-homomorphisms)
    - [Extension of isogenies](#103-extension-of-isogenies)
    - [Extension of finite kernels and quotients](#104-extension-of-finite-kernels-and-quotients)
    - [Extension of polarizations](#105-extension-of-polarizations)
    - [What normality does not guarantee](#106-what-normality-does-not-guarantee)
11. [Two-torsion under odd isogenies](#11-two-torsion-under-odd-isogenies)
    - [The Bezout mechanism](#111-the-bezout-mechanism)
    - [Preservation of the full two-torsion group scheme](#112-preservation-of-the-full-two-torsion-group-scheme)
    - [Rational full two-torsion over a field](#113-rational-full-two-torsion-over-a-field)
    - [Elliptic curves and the Frey configuration](#114-elliptic-curves-and-the-frey-configuration)
    - [Limits of the statement](#115-limits-of-the-statement)
12. [A structural synthesis](#12-a-structural-synthesis)
    - [The exact dictionary](#121-the-exact-dictionary)
    - [A safe workflow](#122-a-safe-workflow)
    - [Conclusion](#123-conclusion)

## 1. The geometry carried by a proper group

An abelian scheme is simultaneously a family of projective varieties, a commutative group, and a source of finite flat group schemes. None of these aspects may be discarded. Properness supplies extension and finiteness; smoothness supplies uniform tangent geometry; connected fibers prevent hidden discrete quotients; the group law turns line bundles into homomorphisms. The purpose of this chapter is to fix the language and isolate the rigidity principle that lets information at the identity control the whole family.

### 1.1 The organizing questions

For a smooth proper family $A\to S$, a line bundle can be translated by every point of $A$. The discrepancy between a bundle and its translate is often algebraically trivial, and that discrepancy varies homomorphically. This observation leads to the dual abelian scheme $A^\vee$. Once the dual exists, four constructions fit together:

$$
\begin{array}{ccc}
\text{line bundles}&\longrightarrow&\text{homomorphisms }A\to A^\vee\\
&&\downarrow\\
\text{finite subgroup schemes}&\longleftarrow&\text{isogeny kernels}.
\end{array}
$$

The Poincare bundle on $A\times_SA^\vee$ joins the two rows. Its restriction to torsion gives Weil pairings; its pullback along an ample class gives a polarization; descent along a finite subgroup constructs quotient abelian schemes. Our aim is not merely to list these constructions, but to prove that they commute with base change and remain valid when torsion is nonreduced.

### 1.2 Conventions and standing hypotheses

An **abelian scheme** over $S$ is a smooth, proper, finitely presented group scheme $p:A\to S$ whose geometric fibers are connected. Its relative dimension is locally constant; when it equals $g$ we write $\dim(A/S)=g$. The identity is $e:S\to A$, inversion is $[-1]$, multiplication by $n$ is $[n]$, and translation by a $T$-point $a$ is $t_a:A_T\to A_T$.

All group schemes in this book are commutative. A finite flat group will always mean finite locally free; its order is its locally constant rank. Exactness of finite group schemes means exactness as fppf sheaves, so a quotient arrow is faithfully flat. This qualification matters in residue characteristic: geometric point sets can omit an entire connected infinitesimal kernel.

The dual symbol $A^\vee$ refers to an abelian scheme. The Cartier dual $G^D$ is defined only for a finite locally free commutative group scheme $G$. These operations meet in the formula

$$
A[n]^D\simeq A^\vee[n],
$$

but they are not the same construction.

### 1.3 Rigidity and its first consequences

The group law is useful because maps from a proper connected family into a separated group cannot vary independently in two directions.

**Rigidity lemma.** Let $X\to S$ be proper, flat, and of finite presentation with geometrically connected fibers and $p_*\mathcal O_X=\mathcal O_S$. Let $Y\to S$ be separated. If $f:X\to Y$ sends every point of one geometric fiber $X_s$ to a single point $y\in Y_s$, then, after shrinking $S$ around $s$, $f$ factors through $S$.

**Proof.** Because $Y$ is separated, the graph of $f$ is closed in $X\times_SY$. Choose an affine neighborhood $V$ of $y$ in $Y$ and let $Z=X\setminus f^{-1}(V)$. Properness makes the image of $Z$ closed in $S$; it misses $s$, so after shrinking, $f$ lands in $V=\operatorname{Spec}_S\mathcal B$. A map $X\to V$ is an $\mathcal O_S$-algebra map $\mathcal B\to p_*\mathcal O_X=\mathcal O_S$, hence factors through a section of $V\to S$. $\square$

For an abelian scheme, $p_*\mathcal O_A=\mathcal O_S$: this holds on geometric fibers because a proper connected reduced variety has only constant functions, and coherent base change promotes the fiber statement to the family. Thus rigidity applies.

**Corollary 1.1 (homomorphism lemma).** If $A,B$ are abelian schemes and $f:A\to B$ is an $S$-morphism with $f(e_A)=e_B$, then $f$ is a homomorphism.

**Proof.** On $A\times_SA$ consider

$$
d(x,y)=f(x+y)-f(x)-f(y).
$$

It vanishes on $A\times e$ and $e\times A$. Apply rigidity first in the $x$-direction and then in the $y$-direction: $d$ is pulled back from the base and its value at $(e,e)$ is zero. Hence $d=0$. $\square$

The same argument proves that a morphism $A\to B$ is a translation of a homomorphism: subtract the section $f(e_A)$. It also proves uniqueness statements. Two homomorphisms equal on one fiber agree near that fiber if their equalizer contains that fiber; on a connected base, equality on a schematically dense open implies equality everywhere because the target is separated and the source is flat.

### 1.4 Fibers, dimension, and base change

Every base change $S'\to S$ carries $A$ to an abelian scheme $A_{S'}$. Smoothness, properness, finite presentation, the group laws, and geometric connectedness all survive. Conversely these properties may be tested after a faithfully flat quasi-compact base change. Thus arguments may pass to geometric fibers or to covers where line bundles are represented, provided the resulting data are descended.

Translation identifies all relative tangent spaces. If

$$
\omega_A=e^*\Omega^1_{A/S},
$$

then $\Omega^1_{A/S}\simeq p^*\omega_A$, and $\omega_A$ is locally free of rank $g$. Hence every fiber has the same dimension on each connected component of $S$. The identity section is not merely a marked point: it is the location where differentials, rigidifications, and normalization conditions are recorded.

Smoothness is indispensable here. A proper finite group scheme such as $\mu_p$ in characteristic $p$ is connected and carries a group law, but it is not an abelian scheme: its cotangent space jumps away from the geometry of a positive-dimensional smooth fiber. Geometric connectedness is equally important. The disjoint union $A\times\underline{\mathbf Z/2\mathbf Z}$ is smooth and proper, but its component group contributes functions and defeats the assertion $p_*\mathcal O=\mathcal O_S$.

The definition is insensitive to nilpotents in the base. A square-zero thickening changes the deformation problem but not the geometric-fiber condition. This is why arbitrary base change, rather than only extension of fields, is built into every theorem below.

We will repeatedly choose a relatively ample line bundle. This is justified by the projectivity theorem for abelian schemes. Its construction is local on the base: after a finite flat refinement, a finite multisection and its translates produce positive effective divisors; tensoring their translates gives a cubical bundle with an affine nonvanishing cover. The affine-open criterion makes it relatively ample, a high power gives a projective embedding, and norm and faithfully flat descent return positive data to the original base. Thus an abelian scheme is projective over $S$. All later uses of an ample bundle are local on $S$ and independent of the choice. Replacing $L$ by $L\otimes[-1]^*L$ makes it symmetric while preserving ampleness.

## 2. Line bundles on an abelian scheme

On a general projective variety, translation is unavailable and the tensor relation among pullbacks of a line bundle has no reason to simplify. On an abelian scheme, repeated addition forces a cubic identity. This identity is the engine behind duality, the finiteness of multiplication, and the quadratic behavior of polarizations.

### 2.1 Why translation is the correct probe

Let $L$ be a line bundle on $A$. For a $T$-point $a$ define

$$
\Delta_L(a)=t_a^*L\otimes L^{-1}.
$$

The bundle $\Delta_L(a)$ measures the failure of $L$ to be translation-invariant. It is insensitive to tensoring $L$ by a bundle pulled back from $S$. More importantly, the square theorem will show that $a\mapsto\Delta_L(a)$ is a homomorphism into the degree-zero Picard functor.

A **rigidification** of $L$ is an isomorphism $e^*L\simeq\mathcal O_S$. Any line bundle becomes rigidified after tensoring by $p^*(e^*L)^{-1}$. Rigidification removes the scalar ambiguity in automorphisms of a line bundle and makes canonical isomorphisms genuinely unique.

### 2.2 Rigidification and the theorem of the square

Write $m:A\times A\to A$ for addition and $p_1,p_2$ for projection. For a rigidified $L$ and $a,b\in A(T)$, the **theorem of the square** gives a canonical rigidified isomorphism

$$
t_{a+b}^*L\otimes L
\simeq t_a^*L\otimes t_b^*L
$$

for every $L$. Equivalently, $a\mapsto\Delta_L(a)$ is additive as a map to the degree-zero Picard functor. In universal form,

$$
m^*L\otimes p_1^*L^{-1}\otimes p_2^*L^{-1}
$$

is multiplicative separately after its normalization along the axes.

Here is the rigidity proof of additivity. On $A^3$ compare the two ways of translating $L$ successively by $x$ and $y$. Their quotient is a line bundle trivial on every coordinate plane. The relative Picard class of that quotient defines a map from one factor to a separated group and is zero at the identity. Rigidity forces it to be zero. Rigidifications then turn equality of classes into a unique isomorphism, and evaluating on the coordinate axes verifies the cocycle. Consequently

$$
\Delta_L(a+b)\simeq\Delta_L(a)\otimes\Delta_L(b).
$$

This is the first appearance of a recurring method: prove an identity fiberwise along the axes, use rigidity to make it global, and use rigidification to remove units from the base.

### 2.3 The theorem of the cube

The full cubic relation is more symmetric. For nonempty $I\subseteq\{1,2,3\}$ let $m_I:A^3\to A$ add the coordinates indexed by $I$. Define

$$
\Theta(L)=
\bigotimes_{\varnothing\ne I\subseteq\{1,2,3\}}
m_I^*L^{\otimes(-1)^{3-|I|}}.
$$

**Theorem 2.1 (the cube).** If $L$ is rigidified, $\Theta(L)$ has a unique trivialization compatible with the induced trivializations on the three coordinate hyperplanes. The trivialization is functorial in $L$ and stable under arbitrary base change.

**Proof.** We use only the preliminary relative Picard space supplied by the Hilbert-scheme construction for projective proper families; the identification of its degree-zero component as the dual abelian scheme is proved in Chapter 3. Regard $\Theta(L)$ as a family of rigidified line bundles on the first copy of $A$, parametrized by the last two. Its restriction when either parameter is zero is trivial by cancellation. Its class therefore defines a morphism $c:A\times A\to\operatorname{Pic}_{A/S}$ vanishing on both axes. The homomorphism lemma in each variable makes $c$ bilinear and places its image in the degree-zero component. For fixed $y$, the map $x\mapsto c(x,y)$ is a homomorphism. As $y$ varies, its class defines a map from the connected proper group $A$ into the unramified, hence discrete, space of homomorphisms. The unramified assertion follows directly: an infinitesimal variation would be a homomorphism from $A$ to a vector group, and properness makes all its coordinate functions constant, hence zero. The class is therefore constant in $y$; at $y=0$ it is zero. Thus $c=0$.

The vanishing of the relative Picard class says that $\Theta(L)$ is pulled back from the parameter base. The coordinate rigidification identifies that pullback with the trivial bundle. Two such trivializations differ by a unit on $A^3$; proper connected fibers make the unit come from $S$, and its value on an axis is $1$. This proves uniqueness and forces all cocycle compatibilities. $\square$

The theorem of the square follows by restricting the cube identity. Conversely, the cube is the coherent three-variable form needed to ensure that the Poincare bundle is a biextension rather than merely a collection of line bundles.

### 2.4 Symmetry and pullback by multiplication

A rigidified line bundle is **symmetric** if $[-1]^*L\simeq L$ compatibly with rigidification. The cube theorem yields, by induction on $n$,

$$
[n]^*L\simeq
L^{\otimes n(n+1)/2}\otimes[-1]^*L^{\otimes n(n-1)/2}. \tag{2.1}
$$

For the induction, restrict the cube identity to $(x,nx,-x)$ and cancel the already known terms; the rigidifications make the resulting isomorphisms coherent. If $L$ is symmetric, (2.1) becomes

$$
[n]^*L\simeq L^{\otimes n^2}. \tag{2.2}
$$

Every $L$ has a symmetric companion $L\otimes[-1]^*L$. If $L$ is relatively ample, so is this companion: inversion preserves ampleness and tensor products of ample bundles are ample. Thus no polarization argument loses generality by first choosing a symmetric ample bundle.

### 2.5 Algebraic triviality and numerical triviality

A rigidified bundle $M$ is **algebraically trivial** if each geometric-fiber class belongs to the identity component of the Picard scheme. Equivalently, fppf locally on the base it occurs as the difference of two fibers in a connected family of line bundles. Such bundles satisfy $\Delta_M(a)=0$ for all $a$, so translation preserves their class.

On an abelian variety over an algebraically closed field, algebraic and numerical triviality agree. One direction is immediate because intersection numbers are constant in connected families. Conversely, if $M$ is numerically trivial and $L$ is ample, then $L^r\otimes M$ has the same Hilbert polynomial as $L^r$. For $r$ large, cohomology and base change put these twists in one connected Hilbert parameter space; subtracting a fixed divisor joins $M$ to the identity in the Picard scheme. The relative statement is fiberwise. This criterion will let positivity be recognized through the homomorphism $\lambda_L$ rather than through a chosen divisor.

Two examples clarify the distinction. On an elliptic curve, $\mathcal O(P-Q)$ is algebraically trivial for any two points $P,Q$; translation changes its divisor but not its degree-zero class. By contrast, $\mathcal O(ne)$ has positive degree $n$ and is ample, so its translation discrepancy varies nontrivially with the translating point. On $E\times E$, the divisor $E\times\{e\}$ is nef but not ample: its restriction to the first factor is trivial. Its associated homomorphism has a positive-dimensional kernel, exactly detecting the failure of ampleness.

## 3. The dual abelian scheme

The phrase “dual abelian scheme” does not mean a linear dual. It means a space representing translation-invariant line bundles, with tensor product as its group law. The universal bundle then encodes every such line bundle at once and supplies all later pairings.

### 3.1 The moduli problem

For an $S$-scheme $T$, let $\operatorname{Pic}^0_{A/S}(T)$ be the group of isomorphism classes of line bundles $M$ on $A_T$ that are rigidified along $e_T$ and algebraically trivial on every geometric fiber. Descent of line bundles makes this an fppf sheaf. Rigidification is essential: without it, automorphisms by units on $T$ prevent a universal line bundle from existing in this direct form.

Tensor product gives the group operation and dualization gives inversion. The cube theorem ensures that algebraic triviality and the rigidified group laws commute with every base change.

### 3.2 Representability and the Poincare bundle

**Theorem 3.1 (dual representability).** The sheaf $\operatorname{Pic}^0_{A/S}$ is represented by an abelian scheme $A^\vee/S$ of relative dimension $g$. Formation of $A^\vee$ commutes with arbitrary base change. There is a universal rigidified line bundle

$$
\mathcal P_A\quad\text{on}\quad A\times_SA^\vee,
$$

trivialized along both zero sections.

**Proof.** We recall the construction because each hypothesis has a later use. Choose a relatively ample symmetric line bundle $L$ on $A$. For $r$ sufficiently large, every $L^r\otimes M$ with $M$ algebraically trivial has vanishing higher cohomology, is generated by sections, and has a fixed Hilbert polynomial on each connected component of $S$. Uniformity follows from projective boundedness and coherent base change. Effective divisors in these bundles therefore occupy an open part of one relative Hilbert scheme.

Pairs of such divisors represent the difference $M$; equality of differences is the equivalence relation cut out by a principal divisor. Descent for line bundles and projective schemes makes the quotient an algebraic space, while the cubical group law and the ample embedding produce invariant affine neighborhoods, so the quotient is a scheme. Rigidification kills the remaining scalar stabilizer. The identity component is separated and of finite presentation.

Properness follows from the valuative criterion. Over a valuation ring, extend a generic divisor after adding a sufficiently ample divisor; two extensions differ by a vertical divisor. Translation invariance and rigidification force that vertical difference to be pulled back from the base and hence trivial as a rigidified class. Smoothness is checked infinitesimally. The tangent space at the identity is $R^1p_*\mathcal O_A$, locally free of rank $g$. Although $H^2(\mathcal O)$ need not vanish, the cube relation cancels the obstruction to lifting algebraically trivial rigidified bundles across a square-zero thickening. Thus the representing identity component is smooth of relative dimension $g$. Its geometric fibers are connected by construction, so it is an abelian scheme.

The universal element of the represented functor is $\mathcal P_A$. Normalizing it on both axes is possible because it is already rigidified on the first; tensoring by a pullback from $A^\vee$ supplies the second normalization. Universality makes the normalization unique. Every step commutes with base change: Hilbert schemes, coherent base change, descent, identity components in this smooth proper family, and the universal rigidification do. $\square$

There are two points of the proof worth retaining. First, the full relative Picard functor need not be proper: components corresponding to different numerical classes form a discrete, often infinite, group. The degree-zero component is proper because translation-invariant classes have no direction in which their numerical degree can escape. Second, smoothness of $A^\vee$ is not a formal consequence of representability. The cubical identity removes the higher obstruction that a general higher-dimensional projective variety can possess.

Infinitesimally, the construction gives

$$
\operatorname{Lie}(A^\vee)\simeq R^1p_*\mathcal O_A.
$$

Indeed a line bundle on $A\times\operatorname{Spec}(R[\epsilon]/\epsilon^2)$ trivial modulo $\epsilon$ is represented by a Cech cocycle $1+\epsilon a_{ij}$; tensor product adds the classes $[a_{ij}]$. Rigidification removes the class pulled back from the base. This calculation explains both the tangent rank $g$ and the contravariance of differentials under $f^\vee$.

### 3.3 The biextension laws

The Poincare bundle is additive in each variable. On $A\times A\times A^\vee$ there is a canonical isomorphism

$$
(m_A\times1)^*\mathcal P_A
\simeq p_{13}^*\mathcal P_A\otimes p_{23}^*\mathcal P_A, \tag{3.1}
$$

and on $A\times A^\vee\times A^\vee$,

$$
(1\times m_{A^\vee})^*\mathcal P_A
\simeq p_{12}^*\mathcal P_A\otimes p_{13}^*\mathcal P_A. \tag{3.2}
$$

For (3.2), tensor product is literally the group law represented by $A^\vee$. For (3.1), the theorem of the square says that an algebraically trivial bundle is additive under pullback along addition. Both isomorphisms are normalized on the axes, so rigidity makes them unique and forces associativity and compatibility. This pair of coherent laws is called the **biextension structure**.

### 3.4 Functoriality and biduality

If $f:A\to B$ is a homomorphism, pullback of rigidified algebraically trivial bundles defines

$$
f^\vee:B^\vee\longrightarrow A^\vee. \tag{3.3}
$$

Thus duality is contravariant, $(gf)^\vee=f^\vee g^\vee$, and it commutes with base change. Universality also gives an evaluation morphism

$$
\delta_A:A\longrightarrow A^{\vee\vee}. \tag{3.4}
$$

**Theorem 3.2 (biduality).** The map $\delta_A$ is an isomorphism, natural in $A$, and $\delta_{A^\vee}$ is dual to $\delta_A$.

**Proof.** The assertion is stable under base change, so work fiberwise over an algebraically closed field and choose an ample $L$. Translation defines

$$
\lambda_L:A\to A^\vee,qquad a\mapsto t_a^*L\otimes L^{-1}.
$$

The square theorem makes this a homomorphism. Ampleness implies its kernel is finite: if the connected stabilizer were positive-dimensional, $L$ would restrict to a translation-invariant, hence numerically trivial, bundle there, contradicting ampleness. Its image has dimension $g$ and is therefore all of $A^\vee$; so $\lambda_L$ is an isogeny.

Applying the universal property twice gives

$$
\lambda_L^\vee\circ\delta_A=\lambda_L. \tag{3.5}
$$

The degree of $\lambda_L$ equals the degree of $\lambda_L^\vee$: both are the square of the top self-intersection $c_1(L)^g/g!$. Taking degrees in (3.5) gives $\deg\delta_A=1$. A finite degree-one map between smooth varieties is an isomorphism. Fiberwise isomorphism plus finite presentation proves that (3.4) is an isomorphism over $S$. Naturality follows from the universal bundle. $\square$

### 3.5 Products and examples

The universal property gives

$$
(A\times_SB)^\vee\simeq A^\vee\times_SB^\vee;
$$

a rigidified algebraically trivial bundle on a product is the tensor product of its restrictions, with the possible mixed term killed by normalization and the cube relation.

For an elliptic scheme $E/S$, the divisor of the zero section defines

$$
E\xrightarrow{\sim}E^\vee,qquad
P\longmapsto\mathcal O_E(P-e),
$$

the canonical principal polarization. For a product $E_1\times E_2$, the product polarization is principal, though additional homomorphisms $E_1\to E_2$ can produce non-product line-bundle classes. A Jacobian carries its theta polarization, but its construction belongs to the geometry of curves; the present theory needs only that it is an ample symmetric class inducing an isomorphism with the dual.

## 4. Homomorphisms and isogenies

An isogeny is the finite change of coordinates natural to abelian geometry. It retains dimension and replaces the group by a finite quotient. Over a field one often defines it as a surjective homomorphism with finite kernel. Over a base, surjectivity must be sheaf-theoretic and flatness cannot be omitted. This chapter establishes the equivalent safe formulations.

### 4.1 Rigidity of maps

For abelian schemes $A,B/S$, the functor $\underline{\operatorname{Hom}}_S(A,B)$ is unramified and separated over $S$. The infinitesimal statement is elementary. If two homomorphisms agree modulo a square-zero ideal, their difference lands infinitesimally at the identity; it is represented by a global homomorphism from the proper group $A$ to the vector group attached to $\operatorname{Lie}(B)$. Every regular function on $A$ comes from $S$, and a constant homomorphism taking the identity to zero is zero. Thus there are no nonzero infinitesimal deformations of a homomorphism.

Consequently a homomorphism is determined by any schematically dense restriction. This rigidity will turn generic-fiber maps over normal bases into global maps once existence is proved.

### 4.2 Equivalent definitions of an isogeny

A homomorphism $f:A\to B$ is an **isogeny** if it is finite locally free and faithfully flat. Its degree is its locally constant rank.

**Proposition 4.1.** Suppose $S$ is connected and $A,B$ have the same relative dimension. The following are equivalent:

1. $f$ is an isogeny;
2. $f$ is finite and fiberwise surjective;
3. $\ker f$ is finite locally free and every geometric-fiber image has dimension $\dim B_s$;
4. $f$ is an fppf quotient by the finite locally free subgroup $\ker f$.

**Proof.** An isogeny has finite locally free kernel by base change along $e_B$, is fiberwise surjective, and is a torsor under its kernel. Thus $1$ implies the others. If $f$ is finite and fiberwise surjective, each fiber map is finite between smooth equidimensional varieties. The source is Cohen--Macaulay and the target regular; miracle flatness gives fiberwise flatness. Since both schemes are flat over $S$, the fiberwise criterion gives flatness of $f$. A finite flat morphism of finite presentation is locally free, and fiberwise surjectivity makes it faithful. This proves $2\Rightarrow1$.

Under $3$, quotient $A$ by $\ker f$; the induced map $A/\ker f\to B$ has trivial kernel and full-dimensional geometric image. It is finite of degree one on each fiber, hence an isomorphism. This proves $3\Rightarrow4\Rightarrow1$. $\square$

Over a field, “surjective with finite kernel” is therefore safe. Over a general base, it is safer to say finite locally free and faithfully flat, because a finite closed kernel of a map of finite-flat groups need not itself be flat without additional geometry.

### 4.3 Multiplication maps and torsion

**Theorem 4.2.** If $A/S$ has relative dimension $g$ and $n\ge1$, then

$$
[n]:A\to A
$$

is an isogeny of degree $n^{2g}$. Hence

$$
A[n]=\ker[n]
$$

is finite locally free of order $n^{2g}$, compatibly with arbitrary base change.

**Proof.** Choose a symmetric relatively ample $L$. Formula (2.2) gives $[n]^*L\simeq L^{n^2}$. If a geometric fiber of $[n]$ contained a positive-dimensional closed subscheme, the pullback of $L$ would be trivial there because the map is constant, while $L^{n^2}$ is ample there, a contradiction. Thus $[n]$ is quasi-finite; properness makes it finite. Its fiberwise image is a closed connected subgroup of the same dimension as $A_s$, hence all of $A_s$.

On a geometric fiber, the projection formula for top intersections gives

$$
\deg([n]),c_1(L)^g=c_1([n]^*L)^g=n^{2g}c_1(L)^g.
$$

The positive number $c_1(L)^g$ cancels. Proposition 4.1 proves finite local freeness. The kernel is its base change along the identity and has the same rank. $\square$

If $n$ is invertible on $S$, the differential of $[n]$ is multiplication by $n$, so $[n]$ is etale and $A[n]$ is finite etale. No such claim holds when a residue characteristic divides $n$: $A[n]$ can be connected and nonreduced, but its scheme-theoretic order remains $n^{2g}$.

For an elliptic curve over an algebraically closed field of characteristic different from $p$, this recovers

$$
E[p]\simeq\underline{\mathbf Z/p\mathbf Z}^2.
$$

In characteristic $p$, an ordinary elliptic curve has an exact connected--etale sequence

$$
0\longrightarrow\mu_p\longrightarrow E[p]
\longrightarrow\underline{\mathbf Z/p\mathbf Z}\longrightarrow0,
$$

while a supersingular elliptic curve has connected $E[p]$ of order $p^2$. Neither case contradicts the degree theorem. The first can have only $p$ geometric points and the second only the identity, while both kernels have scheme-theoretic length $p^2$. This is the basic reason every later kernel and orthogonal is kept as a group scheme.

### 4.4 Degree and composition

If $f:A\to B$ and $g:B\to C$ are isogenies, then $gf$ is an isogeny and

$$
\deg(gf)=\deg(g)\deg(f).
$$

This is multiplication of ranks for finite locally free morphisms. There is an exact sequence

$$
0\longrightarrow\ker f\longrightarrow\ker(gf)
\xrightarrow{f}\ker g\longrightarrow0, \tag{4.1}
$$

where the last arrow is fppf-surjective. Indeed a point of $\ker g$ lifts fppf-locally through the torsor $A\to B$, and any lift lies in $\ker(gf)$. Rank multiplicativity in (4.1) gives the same degree formula without counting geometric points.

### 4.5 Dual homomorphisms and dual isogenies

Pullback gives $f^\vee:B^\vee\to A^\vee$. Biduality implies

$$
(f^\vee)^\vee=f
$$

after the canonical identifications. Moreover $([n]_A)^\vee=[n]_{A^\vee}$ because pulling a line-bundle class back by $[n]$ multiplies that class by $n$.

If $f$ is an isogeny, then $f^\vee$ is an isogeny of the same degree. One proof uses the finite kernel calculation of Chapter 6. A preliminary degree argument also works: choose ample bundles on both sides and compare the top intersection of pullbacks under $f$; the transpose correspondence gives equal determinant indices. The kernel proof is stronger, because it canonically identifies

$$
\ker(f^\vee)\simeq(\ker f)^D
$$

and hence proves equal degree in every characteristic.

## 5. Quotients by finite subgroup schemes

The quotient $A/H$ should identify points differing by translation by $H$. On ordinary point sets this prescription is inadequate: an $H$-torsor need not have a section, so a quotient point may acquire a representative only after an fppf cover. The correct object is therefore a sheaf quotient, and its representability is a geometric theorem.

### 5.1 Why a sheaf quotient is unavoidable

Let $H\hookrightarrow A$ be a finite locally free subgroup. Define the fppf sheaf

$$
(A/H)(T)=A(T)/H(T)
$$

only after sheafification. The resulting map $A\to A/H$ is intended to be an $H$-torsor. For example, multiplication $\mathbf G_m\to\mathbf G_m$ is fppf-surjective even when not every unit of a ring has an $n$th root. Abelian quotients have the same local-lifting feature.

Because $A$ is proper rather than affine, the invariant-ring construction for finite affine groups cannot be applied globally. Projectivity and descent supply the missing construction.

### 5.2 Construction of the quotient

Choose a symmetric relatively ample line bundle $L$ on $A$. The naive tensor product of translates

$$
L_H=\bigotimes_{h\in H}t_h^*L
$$

makes sense only when $H$ is a disjoint union of sections. Scheme-theoretically it is replaced by the norm along the finite locally free projection $q:H\times_SA\to A$:

$$
N_q(m^*L)=\det q_*(m^*L)\otimes(\det q_*\mathcal O_{H\times A})^{-1}. \tag{5.1}
$$

The norm commutes with base change. Translation by $H$ on its first factor permutes the family being normed and gives $L_H$ an $H$-linearization after taking a fixed positive power to remove the scalar cocycle. The bundle remains relatively ample: this can be checked fppf-locally where the finite torsor splits into manageable finite pieces, or by the affine-open criterion for norms.

A sufficiently high power gives an $H$-equivariant closed immersion into a projective bundle. On invariant affine charts, take the finite equivalence-relation quotient. These affine quotients glue because their overlap maps are invariant and the relation

$$
H\times_SA\rightrightarrows A,
\qquad(h,a)\mapsto a, a+h,
$$

is finite locally free. The descended ample bundle makes the glued quotient projective over $S$. Call it $B$.

The construction is independent of the chosen $L$ and power: its quotient map represents the same fppf sheaf, and a representing object is unique. Addition and inversion on $A$ respect $H$-orbits and descend to $B$. The image of $e_A$ is the identity.

### 5.3 The quotient theorem

**Theorem 5.1.** Let $A/S$ be an abelian scheme and $H\hookrightarrow A$ a finite locally free subgroup. Then the fppf quotient $A/H$ is represented by an abelian scheme $B/S$. The quotient map

$$
q:A\longrightarrow B
$$

is an isogeny with kernel $H$, is an $H$-torsor, and has degree $|H|$.

**Proof.** The construction above gives a projective group scheme $B$. Pulling $q$ back along itself, two lifts differ uniquely by a point of $H$, so the torsor map

$$
H\times_SA\longrightarrow A\times_BA,qquad(h,a)\mapsto(a+h,a), \tag{5.2}
$$

is an isomorphism. Consequently $q$ is finite locally free of rank $|H|$, a property checked after the faithfully flat cover $A\to B$, where it becomes $H\times A\to A$. Smoothness of $B/S$ descends through the same cover. Properness follows from projectivity, finite presentation from the construction, and geometric connectedness follows because each $A_{\bar s}\to B_{\bar s}$ is surjective from a connected space. Thus $B$ is an abelian scheme. Equation (5.2) identifies the kernel with $H$. $\square$

Conversely, every isogeny $f:A\to B$ exhibits $B\simeq A/\ker f$ by Proposition 4.1. Finite flat subgroup schemes and isogenies are therefore equivalent presentations of the same operation.

### 5.4 Universal properties and base change

If $u:A\to C$ is a homomorphism trivial on $H$, then it is constant on the two arrows of the quotient relation and descends uniquely to $\bar u:A/H\to C$. Hence

$$
\operatorname{Hom}(A/H,C)
\simeq\{u\in\operatorname{Hom}(A,C):u|_H=0\}. \tag{5.3}
$$

Uniqueness follows because $q$ is faithfully flat. The descended map preserves the identity and is therefore a homomorphism by rigidity.

For every $S'\to S$,

$$
(A/H)_{S'}\simeq A_{S'}/H_{S'}. \tag{5.4}
$$

Indeed both sides represent the base-changed fppf quotient; alternatively, the construction by norms, descent, and invariant affine charts commutes with base change. No flatness of $S'\to S$ is needed because the torsor identity (5.2) does.

### 5.5 Successive quotients

If $H\subseteq K\subseteq A$ are finite locally free subgroup schemes and $K/H$ is finite locally free, then its image in $A/H$ is a finite locally free subgroup and

$$
(A/H)/(K/H)\simeq A/K. \tag{5.5}
$$

Both sides represent the sheaf sending $T$ to points of $A$ modulo local translation by $K$. Degrees give

$$
|K|=|H|\,|K/H|.
$$

One must retain the flatness hypotheses. A raw scheme-theoretic intersection or image of finite subgroup schemes over a higher-dimensional base can fail to be flat, in which case it is not an admissible isogeny kernel until flatness is separately proved.

Over a field of characteristic prime to $n$, the quotient theorem recovers the familiar construction from a Galois-stable subgroup $H\subset A[n](k^s)$: finite etale descent turns $H$ into a subgroup scheme, and $A/H$ is defined over $k$. In characteristic dividing $n$, a subgroup of geometric points records only the etale part. The connected subgroup $\mu_p\subset E[p]$ of an ordinary elliptic curve can be a valid isogeny kernel even though its geometric point set is trivial. Thus “quotient by the rational points of the kernel” is not an adequate construction in mixed or positive characteristic.

## 6. Kernels and duality

Duality reverses an isogeny because a line bundle on the quotient becomes trivial after pullback precisely when its descent datum is a character of the kernel. This converts geometric descent into Cartier duality and is the conceptual source of the Weil pairing.

### 6.1 The character hidden in a trivialized pullback

Let $q:A\to B=A/H$. A $T$-point of $\ker(q^\vee)$ is represented by a rigidified algebraically trivial bundle $M$ on $B_T$ together with the assertion that $q_T^*M$ is trivial as a rigidified bundle. Choose such a trivialization fppf-locally on $T$.

For $h\in H(T')$, translation by $h$ preserves $q^*M$. Comparing the chosen trivialization with its translate gives a unit $\chi(h)\in\mathbf G_m(T')$. Compatibility for two translations gives

$$
\chi(h+h')=\chi(h)\chi(h').
$$

Thus $\chi:H_{T'}\to\mathbf G_m$ is a character. Changing the trivialization by a unit from $T'$ changes neither comparison nor character.

Conversely, a character $\chi$ twists the canonical $H$-linearization of the trivial bundle on $A_T$. Faithfully flat descent along the $H$-torsor $q$ produces a rigidified line bundle $M_\chi$ on $B_T$ whose pullback is trivial. The descended bundle is algebraically trivial because its pullback along a finite surjective map is numerically trivial, and numerical triviality is equivalent to algebraic triviality on geometric abelian fibers.

These operations are inverse, functorial in $T$, and compatible with base change.

### 6.2 Kernel of the dual isogeny

**Theorem 6.1.** For an isogeny $f:A\to B$ with kernel $H$, the dual map is an isogeny and there is a canonical isomorphism

$$
\ker(f^\vee)\simeq H^D. \tag{6.1}
$$

In particular $\deg(f^\vee)=\deg(f)$.

**Proof.** Replace $B$ by $A/H$ using the quotient theorem. Section 6.1 identifies the functor of points of $\ker(f^\vee)$ with the character functor of $H$, which is represented by $H^D$. Thus (6.1) is an isomorphism of finite locally free group schemes. The dimensions of $A^\vee$ and $B^\vee$ agree, and a homomorphism with finite locally free kernel and full-dimensional image is an isogeny. Cartier duality preserves rank, so the degrees agree. $\square$

The evaluation pairing becomes a canonical perfect pairing

$$
\ker f\times_S\ker f^\vee\longrightarrow\mathbf G_m. \tag{6.2}
$$

This statement is schematic. In characteristic $p$, both sides can have far fewer geometric points than their common order.

Taking $f=[n]_A$ gives $A[n]^D\simeq A^\vee[n]$. Taking a quotient $q:A\to A/H$ shows that the dual quotient has kernel $H^D$. Constant and multiplicative kernels are therefore interchanged. For example, if an elliptic $p$-isogeny in characteristic $p$ has kernel $\mu_p$, the dual isogeny has constant etale kernel $\underline{\mathbf Z/p\mathbf Z}$; if the original kernel is $\alpha_p$, its dual kernel is again $\alpha_p$. This distinction is invisible if one records only geometric kernel points.

### 6.3 Annihilators and exact sequences

Suppose $H\subseteq A[n]$ is finite locally free. Under the perfect pairing between $A[n]$ and $A^\vee[n]$ constructed in Chapter 7, define

$$
H^\perp=\ker\bigl(A^\vee[n]\longrightarrow H^D\bigr). \tag{6.3}
$$

Cartier exactness gives

$$
0\longrightarrow H^\perp\longrightarrow A^\vee[n]
\longrightarrow H^D\longrightarrow0, \tag{6.4}
$$

and hence

$$
|H^\perp|=\frac{n^{2g}}{|H|},
\qquad (H^\perp)^\perp=H. \tag{6.5}
$$

These are rank identities, not point counts. If $q:A\to B=A/H$ and $H\subseteq A[n]$, the multiplication-by-$n$ diagram for

$$
0\longrightarrow H^D\longrightarrow B^\vee
\xrightarrow{q^\vee}A^\vee\longrightarrow0
$$

gives the precise torsion sequence

$$
0\longrightarrow H^D\longrightarrow B^\vee[n]
\xrightarrow{q^\vee}H^\perp\longrightarrow0. \tag{6.6a}
$$

The last term is the kernel of the connecting map $A^\vee[n]\to H^D$, which is evaluation on $H$ and hence is exactly the annihilator (6.3). More generally, dualizing a finite-flat exact sequence reverses it.

### 6.4 The dual-isogeny identities

Let $f:A\to B$ have degree $d$. Since $H=\ker f$ is killed by its order $d$, multiplication $[d]_A$ is zero on $H$. The universal property of $A/H$ gives a unique homomorphism

$$
f':B\longrightarrow A
$$

such that

$$
f'f=[d]_A. \tag{6.6}
$$

Because $f$ is faithfully flat, composing and comparing after $f$ gives

$$
ff'=[d]_B. \tag{6.7}
$$

The integer $d$ is a uniform but not always minimal choice; the exponent of $H$ suffices. Dualizing (6.6)--(6.7) gives the corresponding identities for $f^\vee$. These formulas show directly that an isogeny becomes invertible after tensoring the Hom group with $\mathbf Q$.

For elliptic curves, a sharper normalization is customary: there is a unique dual isogeny $\widehat f:B\to A$ with

$$
\widehat f f=[d]_A,
\qquad f\widehat f=[d]_B,
$$

and under the canonical principal polarizations it is precisely $f^\vee$. In higher dimension the same notation requires chosen polarizations to identify each scheme with its dual.

## 7. Weil pairings

The finite kernel pairing (6.2) becomes especially useful for multiplication. It packages the cyclotomic twist, duality of torsion, and symplectic linear algebra in a form valid before taking geometric points.

### 7.1 Construction from the Poincare bundle

Restrict the Poincare bundle to $A[n]\times A^\vee[n]$. Its biextension law says that it is multiplicative in each variable. Since both variables are killed by $n$, the biextension commutator has $n$th power one. It therefore defines

$$
e_n:A[n]\times_SA^\vee[n]\longrightarrow\mu_n, \tag{7.1}
$$

the **Weil pairing**.

Concretely, a point $y\in A^\vee[n](T)$ is a rigidified algebraically trivial bundle $M_y$ whose $n$th tensor power is trivial in the Picard group. Along $x\in A[n](T)$, compare the two orders of applying the translation trivialization by $x$ and the $n$-fold tensor trivialization. Their ratio is a unit. Reversing either operation shows its $n$th power is $1$. Changes of local trivialization cancel in the commutator, so the unit descends. The universal version is (7.1).

There is a complementary divisor description over a field. Choose rational functions whose divisors are $n(P)-n(0)$ and $n(Q)-n(0)$ after translating representatives to have disjoint support. Comparing the value of the first function along the divisor of the second with the reverse comparison gives a root of unity; Weil reciprocity proves independence of all auxiliary choices. This is the classical commutator formula. The Poincare construction is preferable in families because it requires neither disjoint divisors nor rational functions and therefore survives nonreduced torsion.

### 7.2 Bilinearity, functoriality, and base change

The two biextension laws immediately give

$$
e_n(x+x',y)=e_n(x,y)e_n(x',y),
\qquad
e_n(x,y+y')=e_n(x,y)e_n(x,y'). \tag{7.2}
$$

For a homomorphism $f:A\to B$ and its dual $f^\vee:B^\vee\to A^\vee$,

$$
e_n^B(fx,y)=e_n^A(x,f^\vee y). \tag{7.3}
$$

Indeed $(f\times1)^*\mathcal P_B$ and $(1\times f^\vee)^*\mathcal P_A$ represent the same family of pulled-back line bundles and have the same rigidifications, so universality identifies them. Their commutators agree.

All constructions in (7.1)--(7.3) commute with arbitrary base change. In particular, the formula does not require $n$ to be invertible.

### 7.3 Perfectness in every characteristic

**Theorem 7.1.** The Weil pairing is perfect. Equivalently, its adjoint is a canonical isomorphism

$$
A^\vee[n]\xrightarrow{\sim}A[n]^D. \tag{7.4}
$$

**Proof.** Apply Theorem 6.1 to $[n]_A$. Its dual is $[n]_{A^\vee}$, so

$$
(\ker[n]_A)^D\simeq\ker[n]_{A^\vee}.
$$

Under the character construction of Section 6.1, evaluation is exactly the Poincare commutator used in Section 7.1. Thus the displayed isomorphism is the adjoint of $e_n$. $\square$

When $n$ is divisible by a residue characteristic, “perfect” cannot be tested on geometric points. For example, $\mu_p$ has only one geometric point over an algebraically closed field of characteristic $p$, yet its Cartier pairing with the constant group of order $p$ is perfect. The same schematic discipline is essential for abelian $p$-torsion.

### 7.4 Compatibility through levels

If $m,n\ge1$, $x\in A[mn]$, and $y\in A^\vee[mn]$, bilinearity and functoriality of the Poincare bundle give

$$
e_{mn}(x,y)^m=e_n(mx,my). \tag{7.5}
$$

Equivalently, the pairings commute with transition maps in the inverse systems of prime-power torsion. If a prime $\ell$ is invertible on $S$, passing to inverse limits on geometric fibers yields a perfect pairing

$$
T_\ell A\times T_\ell A^\vee\longrightarrow\mathbf Z_\ell(1). \tag{7.6}
$$

The Tate twist appears because the finite target is $\mu_{\ell^r}$, not a canonically constant cyclic group.

### 7.5 The prime-to-characteristic pointwise picture

Over a field $k$ with $n$ invertible, $A[n]$ is finite etale and

$$
A[n](k^s)\simeq(\mathbf Z/n\mathbf Z)^{2g}.
$$

The pairing (7.1) becomes a perfect Galois-equivariant pairing of finite modules. After a principal polarization it is alternating and symplectic. If $g=1$ and $P,Q$ is a symplectic basis, then

$$
e_n(\sigma P,\sigma Q)
=e_n(P,Q)^{\det\rho_n(\sigma)}
=e_n(P,Q)^{\chi_n(\sigma)},
$$

so $\det\rho_n=\chi_n$. This familiar pointwise result is a shadow of the group-scheme pairing, not its definition.

For an elliptic scheme with its canonical principal polarization, alternation can also be seen directly. A bundle corresponding to $Q\in E[n]$ has divisor class $(Q)-(0)$. Interchanging $P$ and $Q$ reverses the translation commutator, while setting $P=Q$ makes the two orders identical. If $n$ is invertible, any point $P$ of exact order $n$ admits $Q$ for which $e_n(P,Q)$ is primitive; otherwise $P$ would lie in the radical. In residue characteristic, the corresponding statement is the existence of a character fppf-locally, not necessarily a second geometric point.

## 8. Polarizations

An abelian scheme is projective, but projectivity alone does not choose a geometry on its torsion. A polarization is the extra positive self-duality that turns the canonical pairing between $A$ and $A^\vee$ into a bilinear form on $A$ itself.

### 8.1 From an ample line bundle to a homomorphism

For a line bundle $L$ define

$$
\lambda_L:A\longrightarrow A^\vee,
\qquad a\longmapsto t_a^*L\otimes L^{-1}. \tag{8.1}
$$

The square theorem proves that this is a homomorphism. Tensor products and pullbacks satisfy

$$
\lambda_{L\otimes M}=\lambda_L+\lambda_M,
\qquad
\lambda_{f^*L}=f^\vee\lambda_Lf. \tag{8.2}
$$

If $L$ is algebraically trivial then $\lambda_L=0$; conversely, a rigidified $L$ with $\lambda_L=0$ is algebraically trivial. Thus (8.1) factors through the Neron--Severi group, the quotient of line-bundle classes by algebraic equivalence.

If $L$ is relatively ample, $\lambda_L$ is an isogeny. Fiberwise, its kernel is the translation stabilizer of $L$. A positive-dimensional stabilizer would make $L$ numerically trivial on that subgroup, contradicting ampleness. The image has dimension $g$, hence is all of $A^\vee$; Proposition 4.1 supplies flatness over the base.

### 8.2 Intrinsic characterization

A **polarization** of $A/S$ is a homomorphism $\lambda:A\to A^\vee$ such that fppf locally on $S$ it equals $\lambda_L$ for a relatively ample line bundle $L$. It is **principal** if it is an isomorphism.

The local wording is deliberate. A polarization homomorphism may be globally defined even when no single global ample bundle induces it; the obstruction is a descent class. Positivity is nevertheless fppf-local, while the homomorphism is genuine global data.

**Proposition 8.1.** A homomorphism $\lambda:A\to A^\vee$ is a polarization if and only if:

1. $\lambda$ is symmetric, meaning $\lambda^\vee\delta_A=\lambda$; and
2. on every geometric fiber there is an ample bundle $L_s$ with $\lambda_s=\lambda_{L_s}$.

It suffices to check condition 2 on one geometric fiber of every connected component.

**Proof.** A bundle-induced map is symmetric by the cube theorem: the two pullbacks of the Poincare bundle representing $\lambda_L$ and its transpose have the same normalized cubical structure. Positivity persists under base change.

Conversely, the biextension descent theorem identifies symmetric homomorphisms fppf-locally with maps $\lambda_L$. Indeed, pull $\mathcal P_A$ back along $1\times\lambda$ to obtain a biextension on $A\times A$. Symmetry identifies it with its transpose; the two biextension laws supply a cubical descent datum along the diagonal. After an fppf cover that trivializes the residual line bundle from the base, this datum is the square construction of a rigidified $L$ and gives $\lambda_L=\lambda$. Once one inducing bundle $L_0$ is chosen, every other differs from it by an algebraically trivial bundle and a pullback from the base; if symmetric rigidifications are required, the remaining ambiguity is a torsor under $A^\vee[2]$.

Choose such a local $L$. Fiberwise ampleness is open in a proper finitely presented family. On an abelian scheme the numerical class of $L$ is locally constant, because intersection numbers with translation-invariant cycles and the associated isogeny degree are locally constant. If $L$ is ample on one fiber of a connected component, the Nakai criterion on abelian fibers makes it ample on every fiber, hence relatively ample. This proves the local characterization. $\square$

### 8.3 Symmetry, type, and degree

Over an algebraically closed field, the kernel of a polarization has square order. If the characteristic of the field does not divide the degree, there are unique integers

$$
d_1\mid d_2\mid\cdots\mid d_g
$$

such that

$$
\ker\lambda(\bar k)\simeq
\prod_{i=1}^g(\mathbf Z/d_i\mathbf Z)^2. \tag{8.3}
$$

The tuple $(d_1,\ldots,d_g)$ is the **type**, and

$$
\deg\lambda=(d_1\cdots d_g)^2. \tag{8.4}
$$

In arbitrary characteristic, (8.4) remains the rank formula but (8.3) must be replaced by the finite-flat kernel and its perfect alternating commutator pairing. The elementary-divisor description is valid on the prime-to-characteristic etale part; connected primary factors require group schemes rather than point modules.

For an ample $L$ on a geometric fiber,

$$
\deg\lambda_L=\left(\frac{c_1(L)^g}{g!}\right)^2. \tag{8.5}
$$

To prove this, apply Riemann--Roch on the abelian variety, where the Todd class is $1$ because the tangent bundle is trivial, to obtain $\chi(L)=c_1(L)^g/g!$. The theta group of $L$ identifies the coordinate algebra of the stabilizer with the endomorphisms of the translation representation on cohomology, giving $|\ker\lambda_L|=\chi(L)^2$. For a high power, higher cohomology vanishes and this is ordinary representation rank; polynomiality in tensor powers yields the formula for $L$. This also proves that polarization degree is a square.

The simplest numerical examples are useful checks. On an elliptic curve, a line bundle of degree $d>0$ induces an isogeny of degree $d^2$ and type $(d)$. On $E_1\times E_2$, an external tensor product of positive-degree bundles is ample in both directions. The divisor $E_1\times\{0\}$ alone is trivial along the first direction; its associated homomorphism has a positive-dimensional kernel and is not a polarization. Positivity must occur in every abelian direction.

### 8.4 Principal polarizations

A principal polarization identifies $A$ with $A^\vee$, but it is additional structure. Biduality identifies $A$ with $A^{\vee\vee}$ and does not supply such a self-duality.

An elliptic scheme has the canonical principal polarization from the zero divisor. A product of principally polarized schemes has the product principal polarization. A Jacobian has the theta principal polarization. In contrast, an arbitrary abelian variety need not carry a specified principal polarization, and two principal polarizations on the same underlying variety can be inequivalent.

A principal polarization may be represented fppf-locally by an ample $L$ with $\chi(L)=1$. The associated complete linear system can be small; it is the polarization homomorphism, not a chosen theta divisor, that descends canonically.

### 8.5 The induced alternating pairing

Compose the Weil pairing with a polarization:

$$
e_n^\lambda(x,y)=e_n(x,\lambda(y)):
A[n]\times A[n]\longrightarrow\mu_n. \tag{8.6}
$$

Symmetry of $\lambda$ and antisymmetry of the Poincare commutator give

$$
e_n^\lambda(y,x)=e_n^\lambda(x,y)^{-1},
\qquad e_n^\lambda(x,x)=1. \tag{8.7}
$$

The second identity is genuine alternation, including when $2$ is not invertible; it follows from the canonical diagonal trivialization of the commutator, not merely from skew-symmetry.

The radical is $\ker(\lambda|_{A[n]})$. Hence $e_n^\lambda$ is perfect exactly when

$$
\lambda[n]:A[n]\longrightarrow A^\vee[n]
$$

is an isomorphism. This holds for every $n$ under a principal polarization, and more generally whenever $n$ is relatively prime to $\deg\lambda$. Indeed choose integers $a,b$ with $an+b\deg\lambda=1$ and use an isogeny quasi-inverse to $\lambda$ to prove that its kernel meets $A[n]$ trivially; equal ranks then give an isomorphism.

## 9. Polarized isogenies and isotropic kernels

Quotienting an abelian scheme always produces another abelian scheme, but a chosen polarization does not automatically descend. The obstruction is measured exactly by the commutator pairing on the kernel. This chapter makes the relation precise and explains why maximal isotropic subgroups are the correct kernels for constructing principally polarized quotients.

### 9.1 Pulling back a polarization

Let $f:A\to B$ be a homomorphism and let $M$ be a line bundle on $B$. Formula (8.2) says

$$
\lambda_{f^*M}=f^\vee\lambda_Mf. \tag{9.1}
$$

If $f$ is an isogeny and $M$ is ample, then $f^*M$ is ample, so the right side is a polarization. Thus the pullback of a polarization $\mu:B\to B^\vee$ is

$$
f^*\mu:=f^\vee\mu f:A\to A^\vee. \tag{9.2}
$$

Degrees satisfy

$$
\deg(f^*\mu)=(\deg f)^2\deg\mu. \tag{9.3}
$$

This follows from multiplicativity and $\deg f^\vee=\deg f$. Equation (9.3) is a useful numerical check, but it does not by itself prove descent of a polarization.

### 9.2 Descent across a quotient

Let $q:A\to B=A/H$ and let $L$ be a rigidified line bundle on $A$. To descend $L$, one needs an $H$-linearization: isomorphisms

$$
\alpha_h:t_h^*L\xrightarrow{\sim}L
$$

whose compositions satisfy $\alpha_{h+h'}=\alpha_h\circ t_h^*\alpha_{h'}$. The possible lifts of translations form the **theta group** $\mathcal G(L)$ in an exact sequence

$$
1\longrightarrow\mathbf G_m\longrightarrow\mathcal G(L)
\longrightarrow K(L)\longrightarrow1,
\qquad K(L)=\ker\lambda_L. \tag{9.4}
$$

Its commutator is an alternating pairing

$$
c_L:K(L)\times K(L)\longrightarrow\mathbf G_m. \tag{9.5}
$$

An $H$-linearization is precisely a splitting of (9.4) over $H$. A necessary condition is therefore $c_L|_{H\times H}=1$. Fppf locally on the base it is also sufficient: when the commutator vanishes, the restricted extension is commutative, and characters of $H$ act simply transitively on splittings; a splitting exists after an fppf cover. Descent of line bundles along the $H$-torsor then gives $M$ on $B$ with $q^*M\simeq L$. Ampleness descends along the finite faithfully flat map $q$.

The local qualification cannot simply be erased. Even when the commutator vanishes, the torsor of splittings can have no global section. The descended polarization homomorphism, however, is global whenever the symmetric homomorphism factors through $q$ and $q^\vee$ as below.

### 9.3 Orthogonal kernels

Assume $\lambda$ is a principal polarization on $A$. The pairing $e_n^\lambda$ is perfect on $A[n]$. For finite locally free $H\subseteq A[n]$, define

$$
H^\perp=\{x\in A[n]:e_n^\lambda(x,H)=1\}.
$$

Then

$$
|H|\,|H^\perp|=n^{2g},
\qquad (H^\perp)^\perp=H. \tag{9.6}
$$

The subgroup is **isotropic** if $H\subseteq H^\perp$, and **maximal isotropic** or **Lagrangian** if equality holds. A Lagrangian has order $n^g$.

Let $q:A\to B=A/H$. Work fppf-locally where $\lambda=\lambda_L$ for a symmetric ample bundle $L$. Then $n\lambda=\lambda_{L^n}$ and $H\subseteq A[n]\subseteq K(L^n)$. The commutator pairing of the theta group $\mathcal G(L^n)$ restricts on $A[n]$ to $e_n^\lambda$. Isotropy therefore says exactly that this commutator vanishes on $H$. By Section 9.2, after a further fppf cover $L^n$ admits an $H$-linearization and descends to an ample bundle $M$ on $B$. Formula (9.1) now gives a symmetric homomorphism $\mu=\lambda_M$ satisfying

$$
\mu:B\longrightarrow B^\vee
$$

such that

$$
q^\vee\mu q=n\lambda. \tag{9.7}
$$

Two local choices of linearization differ by a character of $H$, so their descended bundles can differ by an algebraically trivial class. Their associated homomorphisms are therefore equal. Descent for morphisms glues the local maps $\mu$ to a global polarization. This construction also explains why the homomorphism can descend even when no preferred global inducing bundle does.

### 9.4 Maximal isotropic quotients

**Theorem 9.1.** Let $(A,\lambda)$ be principally polarized of relative dimension $g$, and let $H\subseteq A[n]$ be finite locally free and Lagrangian for $e_n^\lambda$. Then $B=A/H$ carries a unique polarization $\mu$ satisfying (9.7), and $\mu$ is principal.

**Proof.** Existence and positivity were proved in Section 9.3. For uniqueness, let $\mu_1,\mu_2$ satisfy (9.7). Since $q$ is an epimorphism of fppf sheaves,

$$
q^\vee(\mu_1-\mu_2)=0.
$$

Thus $\mu_1-\mu_2:B\to B^\vee$ factors through the finite affine group $\ker q^\vee=H^D$. A map from the proper geometrically connected group $B$ to a finite affine group is constant because its coordinate functions come from the base; as a homomorphism it is therefore zero. Hence $\mu_1=\mu_2$.

Taking degrees in (9.7), and using $\deg(n\lambda)=n^{2g}$ because $\lambda$ is principal, gives

$$
(\deg q)^2\deg\mu=n^{2g}.
$$

Since $\deg q=|H|=n^g$, we obtain $\deg\mu=1$. A degree-one isogeny is an isomorphism, so $\mu$ is principal. $\square$

If $H$ is merely isotropic, the same construction gives a polarization whose degree is

$$
\deg\mu=\frac{n^{2g}}{|H|^2}.
$$

This formula explains why half-dimensional isotropic kernels, not arbitrary finite kernels, preserve principality.

For an elliptic curve and $H\subset E[n]$ finite locally free of order $n$, alternation makes a genuinely cyclic prime-to-characteristic subgroup isotropic. Since $|E[n]|=n^2$, it is Lagrangian, and $E/H$ receives its canonical principal polarization. At the residue characteristic the word “cyclic” has competing meanings: $\mu_p$, the constant group, and local group schemes all have order $p$. The safe input is the displayed isotropy condition, which the commutator pairing can test scheme-theoretically.

## 10. Extension over normal bases

Arithmetic applications often begin with a homomorphism or polarization on the generic fiber and need it on an integral family. Properness alone extends points over valuation rings, but a rational map from a higher-dimensional normal scheme to a proper scheme can still have codimension-two indeterminacy. The group law and rigidity are what remove that indeterminacy for homomorphisms of abelian schemes.

Throughout this chapter, $S$ is a connected normal noetherian integral scheme with generic point $\eta$, and $A,B$ are abelian schemes over $S$. These hypotheses are stated explicitly because weaker bases require separate extension theorems.

### 10.1 Why normality is the threshold

For a normal noetherian integral scheme,

$$
\mathcal O_S=\bigcap_{s\in S^{(1)}}\mathcal O_{S,s}
$$

inside its function field, and a finite module is controlled by its behavior at codimension-one points together with reflexivity. A homomorphism of abelian schemes has a graph stable under addition, so its closure inherits far more structure than the graph of an arbitrary rational map. Codimension-one extension plus this group structure is the normal-base mechanism.

Normality is also close to necessary. Over a nonnormal base, two branches can carry generic extensions that agree on the common generic point but disagree at the conductor, and a morphism need not descend to the pinched base.

### 10.2 Extension of homomorphisms

**Theorem 10.1 (extension theorem).** Restriction to the generic fiber is an isomorphism

$$
\operatorname{Hom}_S(A,B)
\xrightarrow{\sim}
\operatorname{Hom}_\eta(A_\eta,B_\eta). \tag{10.1}
$$

**Proof strategy.** Uniqueness follows from separatedness and density. For existence, first extend over every height-one local ring, then show that the resulting rational map has no codimension-two indeterminacy. The decisive extra fact is that its graph is a subgroup.

Let $u_\eta:A_\eta\to B_\eta$. At $s\in S^{(1)}$, the local ring $R=\mathcal O_{S,s}$ is a DVR. An abelian scheme over a DVR has the following mapping property for smooth $R$-schemes: a generic-fiber map into it extends uniquely. To see it in the present case, take the closure $\Gamma$ of the graph in $A_R\times_RB_R$. Properness makes $\Gamma\to A_R$ proper. Translation of the generic graph by its own points preserves it and hence preserves the closure. The special fiber of $\Gamma\to A_R$ cannot contain a positive-dimensional fiber: translating such a fiber would produce the same positive-dimensional vertical defect above every point of the connected smooth special fiber, contradicting that $\Gamma$ has the same dimension as $A_R$ and is generically a graph. Thus the projection is quasi-finite, hence finite. It is birational onto the smooth, therefore normal, scheme $A_R$; the translation-stable conductor has empty generic fiber and cannot contain the identity fiber, so it is empty. The projection is an isomorphism and the second projection extends $u_\eta$.

We now have a rational homomorphism $u:A\dashrightarrow B$ defined at every codimension-one point of $A$ lying over a codimension-one point of $S$, and on the entire generic fiber. Let $I\subset A$ be its indeterminacy locus. The graph closure is stable under

$$
(a,b),(a',b')\longmapsto(a+a',b+b'),
$$

so wherever two of $u(x),u(y),u(x+y)$ are defined, the third is defined and satisfies the homomorphism identity. Consequently each fiberwise translation by a point in the domain preserves $I$. The domain contains a dense open in every fiber, since it contains all codimension-one specializations and the graph is proper. Translating that dense open by its points covers the smooth connected group fiber; hence $I$ meets no fiber. Thus $u$ is everywhere defined. The homomorphism identity holds on the dense generic fiber and hence globally. This proves surjectivity of (10.1). $\square$

The same proof works componentwise if $S$ is normal noetherian with several connected components. It is false that every generic morphism between arbitrary proper smooth schemes extends; translation invariance is essential.

### 10.3 Extension of isogenies

Let $f_\eta:A_\eta\to B_\eta$ be an isogeny of degree $d$. Extend it to $f:A\to B$ by Theorem 10.1. Construct on the generic fiber a quasi-inverse $f'_\eta$ with

$$
f'_\eta f_\eta=[d],
\qquad f_\eta f'_\eta=[d].
$$

Extend $f'_\eta$ as well. Uniqueness gives the same identities over $S$. Hence

$$
\ker f\subseteq A[d].
$$

It follows that $\ker f$ is finite. On every geometric fiber, the identities force the image of $f$ to contain $[d]B_s=B_s$, so $f_s$ is surjective. Proposition 4.1 proves:

**Corollary 10.2.** A generic-fiber isogeny between abelian schemes over $S$ extends uniquely to an isogeny. Its degree is constant and equals its generic degree.

The kernel is consequently finite locally free; flatness is a conclusion of the abelian-scheme argument, not a formal property of the schematic closure of an arbitrary finite generic subgroup.

### 10.4 Extension of finite kernels and quotients

Suppose $H_\eta\subseteq A_\eta$ is the kernel of an isogeny to the generic fiber of an abelian scheme $B/S$. Extending the isogeny and taking its kernel gives a unique finite locally free subgroup $H\subseteq A$ with generic fiber $H_\eta$. The quotient theorem identifies

$$
A/H\simeq B.
$$

Over a DVR, one needs no preselected $B$: choose $n$ killing $H_\eta$, close $H_\eta$ inside the finite flat group $A[n]$, and saturate the defining Hopf ideal. Torsion-free finite modules over a DVR are free, so the closure is finite flat. Then $A/H$ is an abelian scheme extending the generic quotient.

Over a higher-dimensional normal base, the raw closure inside $A[n]$ is finite and torsion-free but need not be locally free. Normality alone does not turn every closure into an admissible finite flat subgroup. Corollary 10.2 avoids this problem when the target abelian scheme already exists; otherwise one must prove flatness of the closure separately.

### 10.5 Extension of polarizations

Let $\lambda_\eta:A_\eta\to A_\eta^\vee$ be a polarization. Dual formation commutes with base change, so Theorem 10.1 extends it uniquely to $\lambda:A\to A^\vee$. Symmetry extends because

$$
\lambda^\vee\delta_A=\lambda
$$

holds on the dense generic fiber. The generic map is an isogeny, so Corollary 10.2 makes $\lambda$ an isogeny.

It remains to retain positivity; a symmetric isogeny need not be a polarization. On a geometric abelian fiber, nondegenerate symmetric homomorphisms form chambers separated by the locus where the degree vanishes. The ample cone is one such chamber. In a connected family, the characteristic polynomial of the symmetric endomorphism obtained after comparison with a fixed local polarization has locally constant integral coefficients. Its real eigenvalues cannot change sign without passing through zero, which would make the isogeny degenerate. Since the generic member lies in the positive chamber, every fiber does. Proposition 8.1 now proves:

**Corollary 10.3.** A generic polarization extends uniquely as a polarization of $A/S$. A generic principal polarization extends uniquely as a principal polarization.

For the last assertion, the extended degree is the constant generic degree $1$, so the polarization is an isomorphism.

### 10.6 What normality does not guarantee

Three boundaries prevent overuse of the extension theorem.

First, a particular ample line bundle inducing $\lambda_\eta$ need not extend globally. Its polarization homomorphism extends, while the bundle can carry a Picard or Brauer descent obstruction. Fppf locally an inducing ample bundle exists.

Second, a finite generic subgroup inside $A_\eta[n]$ need not have a finite locally free closure over an arbitrary higher-dimensional normal base. A quotient abelian scheme or a separate flatness argument repairs the gap.

Third, if the generic abelian variety has no abelian-scheme model—because it has bad or only semistable reduction—the theorem does not manufacture one. Neron models and semiabelian reduction solve a different extension problem.

## 11. Two-torsion under odd isogenies

The Frey argument uses elliptic curves with three visible nonzero points of order two and then moves within an isogeny class of odd degree. The needed fact is stronger and cleaner than a point count: an odd-degree isogeny identifies the entire two-torsion group schemes. The proof is a Bezout identity inside the isogeny category.

### 11.1 The Bezout mechanism

Let $f:A\to B$ be an isogeny of constant odd degree $d$. Section 6.4 supplies $f':B\to A$ with

$$
f'f=[d]_A,
\qquad ff'=[d]_B. \tag{11.1}
$$

On any group scheme killed by $2$, multiplication by odd $d$ equals the identity because $d=1+2r$ gives

$$
[d]=[1]+[2r]=[1]. \tag{11.2}
$$

Restricting (11.1) to two-torsion therefore makes $f'[2]$ a two-sided inverse to $f[2]$.

The use of $d=\deg f$ is convenient rather than optimal. It suffices that the kernel be killed by some odd integer $m$, for then a quasi-inverse satisfying $f'f=[m]$ gives the same proof.

### 11.2 Preservation of the full two-torsion group scheme

**Theorem 11.1 (odd-isogeny invariance).** For an odd-degree isogeny $f:A\to B$ of abelian schemes over any base,

$$
f[2]:A[2]\xrightarrow{\sim}B[2] \tag{11.3}
$$

is an isomorphism of finite locally free group schemes. The isomorphism is compatible with arbitrary base change and Galois actions on geometric fibers.

**Proof.** Multiplication by $2$ commutes with every homomorphism, so $f$ restricts to $A[2]\to B[2]$, and similarly for $f'$. Equations (11.1)--(11.2) show

$$
f'[2]f[2]=1_{A[2]},
\qquad f[2]f'[2]=1_{B[2]}.
$$

Thus the restrictions are inverse. All ingredients commute with base change. $\square$

This proof includes characteristic two. There $A[2]$ may be connected or nonreduced, so preservation as a group scheme is strictly stronger than any assertion about geometric points.

### 11.3 Rational full two-torsion over a field

Let $K$ be a field of characteristic different from $2$. An abelian variety has **full rational two-torsion** if $A[2]$ is the constant group scheme

$$
\underline{(\mathbf Z/2\mathbf Z)^{2g}}.
$$

Equivalently, every geometric two-torsion point is $K$-rational. If $f:A\to B$ is defined over $K$ and has odd degree, (11.3) is defined over $K$, so $A$ has full rational two-torsion if and only if $B$ does.

In characteristic two, the phrase cannot be defined by demanding $2^{2g}$ rational geometric points: even an ordinary elliptic curve has connected two-torsion. The invariant statement remains the group-scheme isomorphism (11.3).

### 11.4 Elliptic curves and the Frey configuration

Suppose $\operatorname{char}K\ne2$ and

$$
E:y^2=x(x-a)(x+b),
$$

with $0,-b,a$ distinct. Then

$$
O,\quad (0,0),\quad(a,0),\quad(-b,0)
$$

are exactly $E[2](K)$. They form a constant group scheme of order four. If $f:E\to E'$ is any $K$-rational isogeny of odd degree, their images are distinct and exhaust $E'[2](K)$ by (11.3). Thus every elliptic curve reached from this Frey curve by odd isogenies retains full rational two-torsion.

The argument uses neither a Weierstrass equation for $E'$ nor separability of the odd isogeny. In positive characteristic an odd degree can still be divisible by the characteristic, but its kernel is of odd order and remains disjoint from two-torsion in the scheme-theoretic Bezout sense.

### 11.5 Limits of the statement

Even-degree isogenies need not preserve two-torsion. The quotient of an elliptic curve by a rational subgroup of order two kills one nonzero two-torsion point, and the target's remaining two-torsion can acquire a different Galois action. The obstruction is exactly the nontrivial intersection of the kernel with $E[2]$.

Odd isogenies preserve the group scheme $A[2]$, but not a chosen labeling of its nonzero points unless the isogeny is included in the data. Nor do they automatically preserve a chosen principal polarization: the pulled-back polarization changes by the square of the isogeny degree as in (9.3). These distinctions matter in polarized moduli problems even when the underlying two-torsion is unchanged.

## 12. A structural synthesis

The theory developed here turns three kinds of data—line bundles, homomorphisms, and finite group schemes—into interchangeable descriptions when their hypotheses match. The value of the package lies as much in its boundaries as in its formulas: positivity is not mere symmetry, finite is not automatically flat, and geometric points are not a substitute for a group scheme in residue characteristic.

### 12.1 The exact dictionary

For an abelian scheme $A/S$ of relative dimension $g$:

$$
\begin{array}{c|c}
\text{geometric datum}&\text{structural consequence}\\
\hline
\text{rigidified algebraically trivial bundles}&A^\vee\\
\text{Poincare biextension}&A[n]^D\simeq A^\vee[n]\\
\text{relatively ample }L&\lambda_L:A\to A^\vee\text{ a polarization}\\
\text{finite locally free }H\subset A&A/H\text{ and an isogeny}\\
f:A\to B\text{ an isogeny}&\ker f^\vee\simeq(\ker f)^D\\
\text{principal }\lambda&e_n^\lambda\text{ perfect alternating}\\
H\subset A[n]\text{ Lagrangian}&A/H\text{ principally polarized}.
\end{array}
$$

The numerical companion is

$$
|A[n]|=n^{2g},\qquad
\deg f=|\ker f|=\deg f^\vee,
$$

$$
\deg(f^*\mu)=(\deg f)^2\deg\mu,
\qquad
|H|\,|H^\perp|=n^{2g}.
$$

Every equality of orders means equality of finite locally free ranks. It remains meaningful when the corresponding geometric point sets are small.

### 12.2 A safe workflow

Given a homomorphism of abelian schemes, first determine whether its kernel is finite. If it is, use the quotient theorem or the fiberwise criterion to establish faithful flatness; do not infer flatness from closedness alone. Given a torsion pairing, identify its adjoint map into a Cartier dual and prove that map is an isomorphism; do not test only geometric points. Given a symmetric homomorphism to the dual, verify positivity before calling it a polarization. Given generic data over a normal base, extend the homomorphism first, then deduce finiteness and positivity; do not assume a chosen inducing line bundle extends.

For two-torsion under an odd isogeny, the shortest reliable route is the quasi-inverse relation $f'f=[d]$. On a group killed by two, odd multiplication is the identity, so the restriction is automatically an isomorphism. This argument is insensitive to reduction type and avoids every point-counting trap.

### 12.3 Conclusion

An abelian scheme carries its dual through algebraically trivial rigidified line bundles, and the Poincare bundle makes that duality bilinear. Finite subgroup schemes produce quotient abelian schemes; duality reverses their isogenies and identifies the opposite kernel with the Cartier dual. Multiplication kernels inherit perfect Weil pairings in every characteristic. Ample classes turn these pairings into polarizations, while isotropic descent explains which quotients retain principality. Over a normal noetherian integral base, rigidity extends generic homomorphisms, isogenies, and polarizations without pretending that every line bundle or subgroup closure is automatically well behaved. Finally, odd isogenies identify full two-torsion as a group scheme, providing exactly the stable structure required in the Frey setting.
