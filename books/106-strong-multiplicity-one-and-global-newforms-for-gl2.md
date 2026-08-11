# Strong Multiplicity One and Global Newforms for $\mathrm{GL}_2$

## Contents

1. [The local-to-global recognition problem](#1-the-local-to-global-recognition-problem)
   - [Almost everywhere is enough](#11-almost-everywhere-is-enough)
   - [Standing conventions](#12-standing-conventions)
   - [The three multiplicity statements](#13-the-three-multiplicity-statements)
   - [The architecture of the book](#14-the-architecture-of-the-book)
2. [Restricted tensor products of automorphic representations](#2-restricted-tensor-products-of-automorphic-representations)
   - [Why infinitely many local factors can be assembled](#21-why-infinitely-many-local-factors-can-be-assembled)
   - [The algebraic restricted tensor product](#22-the-algebraic-restricted-tensor-product)
   - [Local components of a cuspidal summand](#23-local-components-of-a-cuspidal-summand)
   - [Factorization of compact invariants](#24-factorization-of-compact-invariants)
   - [Uniqueness of the local factors](#25-uniqueness-of-the-local-factors)
3. [Strong multiplicity one](#3-strong-multiplicity-one)
   - [Satake data and incomplete products](#31-satake-data-and-incomplete-products)
   - [Pole comparison](#32-pole-comparison)
   - [The strong multiplicity-one theorem](#33-the-strong-multiplicity-one-theorem)
   - [Hecke-polynomial formulations](#34-hecke-polynomial-formulations)
   - [Why the hypotheses cannot be weakened carelessly](#35-why-the-hypotheses-cannot-be-weakened-carelessly)
4. [Automorphic multiplicity one and canonical realization](#4-automorphic-multiplicity-one-and-canonical-realization)
   - [From finite to unit multiplicity](#41-from-finite-to-unit-multiplicity)
   - [Whittaker coefficients distinguish embeddings](#42-whittaker-coefficients-distinguish-embeddings)
   - [The multiplicity-free cuspidal decomposition](#43-the-multiplicity-free-cuspidal-decomposition)
   - [Near equivalence becomes equality](#44-near-equivalence-becomes-equality)
5. [Local conductors and normalized newvectors](#5-local-conductors-and-normalized-newvectors)
   - [The subgroup that measures a directed level](#51-the-subgroup-that-measures-a-directed-level)
   - [The conductor exponent](#52-the-conductor-exponent)
   - [The local newvector theorem revisited](#53-the-local-newvector-theorem-revisited)
   - [Whittaker normalization](#54-whittaker-normalization)
   - [Conductors in the local classification](#55-conductors-in-the-local-classification)
   - [Central characters, duals, and twists](#56-central-characters-duals-and-twists)
6. [The local oldform tower](#6-the-local-oldform-tower)
   - [Raising the level](#61-raising-the-level)
   - [The oldvector basis](#62-the-oldvector-basis)
   - [Two degeneracy maps](#63-two-degeneracy-maps)
   - [A local new quotient](#64-a-local-new-quotient)
   - [Hecke recurrences on the tower](#65-hecke-recurrences-on-the-tower)
7. [Global conductors and adelic levels](#7-global-conductors-and-adelic-levels)
   - [The conductor ideal](#71-the-conductor-ideal)
   - [The global $K_1$ subgroup](#72-the-global-k_1-subgroup)
   - [Factorization of level invariants](#73-factorization-of-level-invariants)
   - [The global newvector line](#74-the-global-newvector-line)
   - [Normalized global Whittaker functions](#75-normalized-global-whittaker-functions)
8. [Old and new subspaces at finite level](#8-old-and-new-subspaces-at-finite-level)
   - [Degeneracy maps between adelic levels](#81-degeneracy-maps-between-adelic-levels)
   - [The closed oldspace](#82-the-closed-oldspace)
   - [The orthogonal newspace](#83-the-orthogonal-newspace)
   - [The global newform decomposition](#84-the-global-newform-decomposition)
   - [Dimension and multiplicity formulas](#85-dimension-and-multiplicity-formulas)
9. [Hecke operators and recognition of newforms](#9-hecke-operators-and-recognition-of-newforms)
   - [Unramified Hecke operators](#91-unramified-hecke-operators)
   - [Eigenvalues determine the unramified component](#92-eigenvalues-determine-the-unramified-component)
   - [Multiplicity one for Hecke eigensystems](#93-multiplicity-one-for-hecke-eigensystems)
   - [Ramified operators and what they do not determine](#94-ramified-operators-and-what-they-do-not-determine)
10. [Classical forms through the adelic dictionary](#10-classical-forms-through-the-adelic-dictionary)
    - [From congruence level to $K_1$ level](#101-from-congruence-level-to-k_1-level)
    - [$q$-expansions and Whittaker normalization](#102-q-expansions-and-whittaker-normalization)
    - [Classical oldforms](#103-classical-oldforms)
    - [Squarefree and prime-power examples](#104-squarefree-and-prime-power-examples)
    - [Hilbert modular forms](#105-hilbert-modular-forms)
11. [Duality, twisting, and level symmetry](#11-duality-twisting-and-level-symmetry)
    - [Contragredient newforms](#111-contragredient-newforms)
    - [Twists and conductor change](#112-twists-and-conductor-change)
    - [Atkin--Lehner symmetry](#113-atkin--lehner-symmetry)
    - [Normalization audits and counterexamples](#114-normalization-audits-and-counterexamples)
12. [The complete global newform package](#12-the-complete-global-newform-package)
    - [The main theorem in one statement](#121-the-main-theorem-in-one-statement)
    - [The implication chain](#122-the-implication-chain)
    - [Conclusion](#123-conclusion)

## 1. The local-to-global recognition problem

### 1.1 Almost everywhere is enough

An automorphic representation of $\mathrm{GL}_2$ is global, but almost all of its visible data are local. At every finite place outside a finite set there is a one-dimensional spherical line. The spherical Hecke algebra acts on that line through two numbers, recorded without an ordering by a quadratic polynomial. It is therefore natural to ask whether the collection of these polynomials determines the global representation.

For an arbitrary restricted tensor product the answer would be no: one could change finitely many factors and obtain a different tensor product with exactly the same remaining data. Cuspidal automorphic representations are more rigid. Their local factors are tied together by a single global Fourier expansion, and their Rankin--Selberg Euler products possess poles governed by global invariant pairings. If two cuspidal representations agree away from finitely many places, the common Euler tail makes a self-pairing pole appear in a cross-pairing product. The pole criterion then forces the two global representations to be isomorphic, including at the places that were never compared.

This is **strong multiplicity one**. Its force lies in its asymmetry: no local classification at the exceptional places is required. A finite amount of missing information is recovered from a global analytic singularity.

Once a representation has been recognized, a second problem begins. At a ramified place the spherical line disappears. There is nevertheless a first congruence subgroup fixing a vector, and at that first level the fixed line is again one dimensional. Its exponent is the local conductor. Tensoring these local lines produces the global newvector, while translating them at deeper levels produces oldvectors. Thus conductor theory turns the multiplicity-one classification into an explicit decomposition of every finite-level cuspidal space.

The point of the present book is to prove that entire chain without confusing three different assertions:

- finite multiplicity of a cuspidal summand in a Hilbert-space decomposition;
- multiplicity one of its automorphic realization;
- strong multiplicity one, which reconstructs the global isomorphism class from almost all local classes.

The first is spectral, the second is Fourier-theoretic, and the third is analytic. Global newform theory uses all three.

### 1.2 Standing conventions

Let $F$ be a number field, $\mathbf A=\mathbf A_F$ its adele ring, and

$$
G=\mathrm{GL}_2.
$$

At a finite place $v$, write

$$
F_v,\qquad \mathcal O_v,\qquad \mathfrak p_v=(\varpi_v),\qquad
q_v=|\mathcal O_v/\mathfrak p_v|,
$$

and normalize $|\varpi_v|_v=q_v^{-1}$. Put

$$
K_v=G(\mathcal O_v).
$$

All automorphic representations in the main theorems are irreducible, unitary, and cuspidal, with unitary central character. This is the normalization in which the Rankin--Selberg criterion at $s=1$ applies without a local factor acquiring a pole at the comparison point. An essentially unitary representation can always be shifted into this normalization; the shift must then also be made in the complex variable of its $L$-functions.

Fix a nontrivial character

$$
\psi:F\backslash\mathbf A\longrightarrow\mathbf C^\times
$$

and its local components $\psi_v$. When discussing local newvectors we first assume that $\psi_v$ has conductor $\mathcal O_v$. The general conductor is obtained by diagonal conjugation, and we record the resulting shift rather than silently changing $\psi_v$.

For a cuspidal representation $\pi$, write

$$
\pi\simeq\bigotimes_v'\pi_v
$$

for its restricted tensor product. This notation will be constructed and justified in Chapter 2. At almost every finite place $\pi_v$ is unramified, $\pi_v^{K_v}$ is one dimensional, and its Satake multiset is

$$
A_v(\pi)=\{\alpha_v,\beta_v\}.
$$

Our normalized spherical Hecke polynomial is

$$
P_v(\pi;X)=(1-\alpha_vX)(1-\beta_vX).
\tag{1.1}
$$

The corresponding local standard factor is $P_v(\pi;q_v^{-s})^{-1}$. This polynomial notation is safer than an unqualified reference to Frobenius: it fixes the representation-theoretic normalization without requiring a choice between arithmetic and geometric terminology.

The cuspidal Hilbert space with central character $\omega$ is denoted

$$
L^2_{\mathrm{cusp},\omega}
=L^2_{\mathrm{cusp}}\bigl(Z(\mathbf A)G(F)\backslash G(\mathbf A),\omega\bigr).
$$

Book 102 proves that it is a discrete Hilbert sum with finite multiplicities. Book 104 proves restricted tensor factorization, local genericity of every finite component of a cuspidal representation, global Whittaker uniqueness, and automorphic multiplicity one. Book 105 proves the exact Rankin--Selberg pole criterion used for strong multiplicity one. Book 77 supplies the Kirillov-model input and proves the $K_1$ theorem in the principal-series, special, depth-zero, and tame-dihedral cases. Its stated theorem does not cover primitive wild supercuspidals. Section 5.3 therefore proves the generic $K_1$ theorem in the generality needed here instead of silently enlarging Book 77's interface.

### 1.3 The three multiplicity statements

It is useful to state the destination before beginning the proof.

**Theorem 1.1 (multiplicity and recognition package).** Fix a unitary idele class character $\omega$.

1. There is a countable Hilbert direct sum

   $$
   L^2_{\mathrm{cusp},\omega}
   =\widehat\bigoplus_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}\mathcal H_\pi,
   \tag{1.2}
   $$

   in which each irreducible cuspidal automorphic representation occurs once.
2. If $\pi_v\simeq\rho_v$ for all but finitely many places, then $\pi\simeq\rho$.
3. At every finite $v$, the local conductor exponent $a(\pi_v)$ is finite and

   $$
   \dim\pi_v^{K_1(\mathfrak p_v^n)}
   =\max\{0,n-a(\pi_v)+1\}.
   \tag{1.3}
   $$
4. The global conductor

   $$
   \mathfrak c(\pi)=\prod_{v<\infty}\mathfrak p_v^{a(\pi_v)}
   \tag{1.4}
   $$

   is a finite ideal, and the finite newvector space

   $$
   \pi_f^{K_1(\mathfrak c(\pi))}
   \tag{1.5}
   $$

   is one dimensional.
5. At any integral ideal $\mathfrak n$, the oldspace generated from proper lower levels and its orthogonal complement give a canonical decomposition. The newspace is precisely the Hilbert sum of the representations with conductor $\mathfrak n$, each contributing its one-dimensional finite newvector line tensored with its archimedean representation.

Parts 1 and 2 are often both called multiplicity one, but they answer different questions. Part 1 says that the same global object is not repeated. Part 2 says that almost all of its local shadows determine which global object it is. Parts 3--5 say how that object first appears in the tower of levels and how all later appearances are generated.

### 1.4 The architecture of the book

Chapters 2--4 establish the global representation-theoretic skeleton. Restricted tensor products make local components meaningful; pole comparison proves strong multiplicity one; global Whittaker uniqueness removes the finite multiplicities left by spectral theory.

Chapters 5 and 6 then work locally. The asymmetric group $K_1(\mathfrak p^n)$ is explained from the geometry of a primitive row vector. The Kirillov model proves existence, uniqueness, and the exact growth of oldvector spaces. Two elementary level-raising maps generate the entire local oldspace.

Chapters 7 and 8 globalize these results. Conductors multiply to an ideal, invariant spaces factor, and the two local degeneracy maps become adelic maps between finite levels. Orthogonality and multiplicity one identify the newspace exactly.

The final chapters compare this representation-theoretic picture with Hecke eigensystems, classical $q$-expansions, duality, twists, and Atkin--Lehner symmetry. These are not decorative translations. They show which parts of the theorem are normalization-independent and which require the precise choices made above.

## 2. Restricted tensor products of automorphic representations

### 2.1 Why infinitely many local factors can be assembled

The adelic group is a restricted product:

$$
G(\mathbf A)=G(F_\infty)\times\prod_{v<\infty}'G(F_v),
$$

where almost every finite component lies in $K_v$. A representation of this group should therefore be built from local representations together with reference vectors fixed by $K_v$ at almost every place. An ordinary infinite tensor product has no preferred meaning: rescaling infinitely many factors would change an infinite product of scalars. The spherical reference lines remove this ambiguity.

There are two tasks. One must first define the restricted tensor product once the local factors are given. One must then prove that an irreducible cuspidal summand actually has such local factors. The second task uses smoothness, admissibility, and irreducibility; it is not a formal consequence of writing the group as a restricted product.

### 2.2 The algebraic restricted tensor product

Let $\pi_v$ be an irreducible admissible representation of $G(F_v)$ for every place. At almost every finite $v$, suppose a nonzero vector $e_v\in\pi_v^{K_v}$ has been chosen and that this fixed space is one dimensional. For a finite set $S$ containing all archimedean places and all exceptional finite places, form

$$
V_S=\bigotimes_{v\in S}\pi_v\otimes
\bigotimes_{v\notin S}\mathbf C e_v.
$$

If $S\subset S'$, the map $V_S\to V_{S'}$ tensors with $e_v$ at the new places. The **algebraic restricted tensor product** is the direct limit

$$
\bigotimes_v'(\pi_v,e_v)=\varinjlim_S V_S.
\tag{2.1}
$$

Its elements are finite linear combinations of pure tensors $\otimes_vx_v$ with $x_v=e_v$ almost everywhere. The restricted product group acts because any adelic element belongs to $K_v$ almost everywhere and hence fixes $e_v$ there.

Changing finitely many $e_v$ merely changes the finite tensor description. Rescaling $e_v$ at infinitely many places is not harmless, which is why the standard normalization matters. For a unitary representation we choose $\|e_v\|=1$. At a place where the additive character has conductor $\mathcal O_v$, a Whittaker model instead permits $W_{e_v}(1)=1$; the two choices differ by a well-defined nonzero scalar, but an infinite simultaneous conversion is not made without fixing a global convention.

**Proposition 2.1 (irreducibility of the restricted product).** If every $\pi_v$ is irreducible and the spherical line is one dimensional outside a finite set, then the smooth restricted tensor product in (2.1) is irreducible.

**Proof strategy.** Any nonzero vector lies in a finite tensor stage. Operators from finitely many local groups isolate a pure tensor and then generate the whole finite tensor product; the spherical Hecke idempotents keep the reference vectors fixed outside that set.

**Proof.** Let $U$ be a nonzero invariant subspace and choose $0\ne x\in U$ lying in $V_S$. Enlarge $S$ until $x$ is a finite sum of tensors in the finite product $\otimes_{v\in S}\pi_v$. Irreducibility of finite external tensor products implies that the group $\prod_{v\in S}G(F_v)$ generates all of $\otimes_{v\in S}\pi_v$ from $x$. This finite-product assertion follows successively from the density form of Schur's lemma: given finitely many linearly independent coordinates in one factor, a finite linear combination of group operators can prescribe their images.

Hence $U$ contains $V_S$. For $w\notin S$ and $y_w\in\pi_w$, irreducibility of $\pi_w$ says that $y_w$ is a finite linear combination of translates of $e_w$. Acting at $w$ therefore shows that $U$ contains the stage $V_{S\cup\{w\}}$. Repeating finitely many times gives every $V_{S'}$, and their union is (2.1). Thus $U$ is the whole restricted tensor product. $\square$

The Hilbert restricted tensor product is obtained by completing with respect to the tensor product inner product when all local representations are unitary and the $e_v$ are unit vectors. Its smooth finite-adelic vectors contain (2.1) densely, and every statement about congruence invariants may be proved on the algebraic space before completion.

### 2.3 Local components of a cuspidal summand

Let $\pi$ be an irreducible summand of $L^2_{\mathrm{cusp},\omega}$. Smooth finite-adelic vectors are dense. Choose one nonzero vector fixed by

$$
K^S=\prod_{v\notin S}K_v
$$

for some finite $S$. The commuting actions of $G(F_v)$ permit us to extract an irreducible local factor $\pi_v$ from the cyclic span at each $v$. Admissibility makes all compact-open fixed spaces finite dimensional, preventing a continuous local multiplicity from appearing.

**Theorem 2.2 (local factorization).** Every irreducible unitary cuspidal automorphic representation admits a factorization

$$
\pi\simeq\bigotimes_v'\pi_v
\tag{2.2}
$$

into irreducible admissible unitary local representations. At almost every finite $v$, $\pi_v$ is unramified and $\dim\pi_v^{K_v}=1$.

**Proof strategy.** This is the factorization theorem proved in Book 104, before that book invokes Whittaker uniqueness. We recall its construction to make clear that neither multiplicity-one theorem is being used. One factors across a finite product and its commuting complement, checks compatibility while the finite set grows, and uses a smooth vector to supply the spherical reference lines.

**Proof.** For a finite set $S$ containing the archimedean places, write $G_S=\prod_{v\in S}G(F_v)$ and let $G^S$ be the restricted complementary group. The product-group factorization theorem established in Book 104 gives

$$
\pi\simeq\pi_S\widehat\otimes\pi^S,
$$

with both factors irreducible; iterating inside $G_S$ gives $\pi_S=\widehat\otimes_{v\in S}\pi_v$. If $S\subset S'$, factor the complementary representation once more. The uniqueness clause of the same theorem, proved from the two commuting von Neumann algebras and Schur's lemma, shows that the previously extracted $\pi_v$ do not change.

Choose a nonzero smooth vector. It is fixed by $K_v$ outside one finite set $S_0$. Factorization of that vector across a finite stage shows that $\pi_v^{K_v}\ne0$ for $v\notin S_0$. Local spherical multiplicity one makes this a one-dimensional line $\mathbf Ce_v$. The compatible finite tensor maps therefore give a nonzero equivariant map

$$
\bigotimes_v'(\pi_v,e_v)\longrightarrow\pi^\infty.
$$

Proposition 2.1 makes the source irreducible, while construction from the cyclic smooth vectors makes the image dense and equal to the smooth representation. The map is therefore an isomorphism on smooth vectors. Completing the unitary tensor norm yields (2.2). $\square$

Book 104 also proves local admissibility by putting each compact level and local type inside a finite global spectral window. Thus the proof uses only local structural theory and the discrete irreducibility of the global summand. It uses neither strong nor automorphic multiplicity one, so local components are defined before either theorem refers to them.

### 2.4 Factorization of compact invariants

The practical value of (2.2) is that finite-level invariant spaces become finite tensor products.

**Proposition 2.3.** Let $J_v\subseteq G(F_v)$ be compact open at the finite places, with $J_v=K_v$ almost everywhere, and put $J_f=\prod_{v<\infty}J_v$. Then

$$
\pi_f^{J_f}\cong\bigotimes_{v<\infty}\pi_v^{J_v},
\tag{2.3}
$$

where almost every factor is the one-dimensional spherical line. In particular,

$$
\dim\pi_f^{J_f}=\prod_{v<\infty}\dim\pi_v^{J_v}.
\tag{2.4}
$$

**Proof.** Averaging over $J_f$ is the tensor product of the local averaging idempotents. On a finite tensor stage, the image of a tensor product of idempotents is the tensor product of their images. Outside a sufficiently large finite set, both the vector and the subgroup are standard and the local image is $\mathbf Ce_v$. Taking the direct limit gives (2.3). Only finitely many factors in (2.4) differ from one. $\square$

This statement would fail for an arbitrary nonfactorizable compact open subgroup without modification. The global newform theory uses the factorizable groups $K_1(\mathfrak n)$, so (2.3) is exactly the needed form.

### 2.5 Uniqueness of the local factors

Suppose

$$
\bigotimes_v'\pi_v\simeq\bigotimes_v'\rho_v
\tag{2.5}
$$

as representations of $G(\mathbf A)$. Fix a place $w$ and a finite stage containing every nonstandard reference vector needed to represent the isomorphism and its inverse on chosen nonzero pure tensors. Apply linear functionals to all tensor factors at that stage except the $w$-factor, choosing the functionals to be nonzero on the selected coordinates. Currying the global intertwiner then gives a nonzero $G(F_w)$-map $\pi_w\to\rho_w$. Repeating the construction with the inverse gives a nonzero map in the other direction. Irreducibility and Schur's lemma yield

$$
\pi_w\simeq\rho_w.
\tag{2.6}
$$

Thus the local factors of a given global representation are unique at every place. This is an elementary uniqueness statement after a global isomorphism is known. Strong multiplicity one proves the converse from isomorphisms at almost every place.

## 3. Strong multiplicity one

### 3.1 Satake data and incomplete products

Let $\pi$ and $\rho$ be irreducible unitary cuspidal automorphic representations. Choose a finite set $S$ containing all archimedean places and every finite place at which either representation is ramified. For $v\notin S$, write

$$
A_v(\pi)=\{\alpha_v,\beta_v\},\qquad
A_v(\rho)=\{\gamma_v,\delta_v\}.
$$

The local Rankin--Selberg factor of $\rho_v\times\widetilde\pi_v$ is

$$
L_v(s,\rho_v\times\widetilde\pi_v)
=\prod_{x\in A_v(\rho)}\prod_{y\in A_v(\widetilde\pi)}
(1-xyq_v^{-s})^{-1}.
\tag{3.1}
$$

If $\rho_v\simeq\pi_v$, then (3.1) equals the self-pair factor $L_v(s,\pi_v\times\widetilde\pi_v)$. Consequently equality of the local representations outside $S$ gives an identity in the half-plane of absolute convergence:

$$
L^S(s,\rho\times\widetilde\pi)
=L^S(s,\pi\times\widetilde\pi).
\tag{3.2}
$$

No assertion about the factors in $S$ is hidden in (3.2). That is precisely why incomplete products are used.

### 3.2 Pole comparison

Book 105 establishes the following analytic criterion with the normalizations of Section 1.2.

**Rankin--Selberg pole criterion.** If $\sigma$ and $\pi$ are irreducible unitary cuspidal representations and $S$ is finite and contains the archimedean places, then

$$
\operatorname{pord}_{s=1}L^S(s,\sigma\times\widetilde\pi)
=\dim\operatorname{Hom}_{G(\mathbf A)}(\sigma,\pi).
\tag{3.3}
$$

Here the polar order is one when $\sigma\simeq\pi$ and zero otherwise. The theorem also proves that deleting the finitely many factors in $S$ does not change this polar order: unitarity makes every deleted finite and archimedean local factor finite and nonzero at $s=1$.

The proof of strong multiplicity one is now short, but the reason it works should remain visible. The right side of (3.2) is a self-convolution, so it has a simple pole at one. If $\rho$ were not isomorphic to $\pi$, the left side would be holomorphic at one. Equality in a right half-plane, followed by meromorphic continuation, cannot identify functions with different orders at the same point.

This is not an argument from coefficientwise equality at $s=1$, where the Euler products need not converge. It is an argument from equality on $\operatorname{Re}(s)>1$ and uniqueness of meromorphic continuation.

### 3.3 The strong multiplicity-one theorem

**Theorem 3.1 (strong multiplicity one for $\mathrm{GL}_2$).** Let $\pi$ and $\rho$ be irreducible unitary cuspidal automorphic representations of $G(\mathbf A_F)$. If

$$
\pi_v\simeq\rho_v
$$

for all but finitely many places $v$, then

$$
\boxed{\pi\simeq\rho.}
\tag{3.4}
$$

In particular $\pi_v\simeq\rho_v$ at every place.

**Proof strategy.** Form the common incomplete Euler tail and compare its pole at one first as a self-product and then as a cross product.

**Proof.** Choose $S$ containing the archimedean places, every ramified finite place of either representation, and every place where the local representations have not been assumed isomorphic. Then (3.2) holds for $\operatorname{Re}(s)>1$. The right side has a simple pole at $s=1$ by (3.3). Equality and meromorphic continuation give the same pole on the left. Applying (3.3) again shows

$$
\operatorname{Hom}_{G(\mathbf A)}(\rho,\pi)\ne0.
$$

Both representations are irreducible, so every nonzero intertwiner is an isomorphism. The final local assertion follows from uniqueness of local factors in Section 2.5. $\square$

The theorem repairs the apparent freedom to alter finitely many factors of a restricted tensor product. Most such altered products simply do not occur cuspidally. Automorphy is the global constraint detected by the pole.

### 3.4 Hecke-polynomial formulations

At an unramified place the isomorphism class of an irreducible spherical representation is determined by its unordered Satake pair, equivalently by the polynomial (1.1). Hence Theorem 3.1 has an immediately usable Hecke form.

**Corollary 3.2.** If

$$
P_v(\pi;X)=P_v(\rho;X)
\tag{3.5}
$$

for all but finitely many $v$, then $\pi\simeq\rho$.

**Proof.** Equality of the quadratic polynomials gives equality of the unordered roots and therefore $\pi_v\simeq\rho_v$ at every place under consideration. Apply Theorem 3.1. $\square$

Let

$$
T_v=\mathbf1_{K_v\operatorname{diag}(\varpi_v,1)K_v},qquad
S_v=\mathbf1_{K_v(\varpi_vI_2)K_v},
$$

with $\operatorname{vol}(K_v)=1$. On the spherical line their eigenvalues are

$$
q_v^{1/2}(\alpha_v+\beta_v),qquad \alpha_v\beta_v.
\tag{3.6}
$$

Thus equality of both eigenvalues almost everywhere implies (3.5). If the two representations have the same central character, equality of the $T_v$ eigenvalues alone is enough, because the $S_v$ eigenvalue is then already common. Without equality of central characters, the trace $\alpha_v+\beta_v$ alone does not determine the determinant $\alpha_v\beta_v$ and therefore does not determine the local representation.

### 3.5 Why the hypotheses cannot be weakened carelessly

Cuspidality is essential to the pole criterion in the form (3.3). For characters, Eisenstein constituents, and more general isobaric sums, the self- and cross-poles count common constituents and residual terms rather than an irreducible cuspidal pairing. Recognition theorems exist in those settings, but they require a differently stated isobaric argument; (3.3) cannot simply be reused unchanged.

Unitarity is also doing real work. For arbitrary nonunitary twists, a deleted local factor can itself have a pole at $s=1$. Then removing that place may change polar order, breaking the passage from the completed pole criterion to (3.3). One may handle essentially unitary representations by first applying the unique real norm twist that makes them unitary and translating $s$ accordingly.

Finally, equality on a density-one set is not automatically the same as equality outside a finite set. Book 105 proves a sparse-exception variant under temperedness and the summability condition

$$
\sum_{v\in T}q_v^{-1}<\infty,
$$

but density zero alone does not imply this convergence. The finite-exception theorem above needs no bound toward temperedness and is the form required for global newforms.

## 4. Automorphic multiplicity one and canonical realization

### 4.1 From finite to unit multiplicity

The discrete spectral theorem gives

$$
L^2_{\mathrm{cusp},\omega}
\simeq\widehat\bigoplus_\pi M_\pi\otimes\mathcal H_\pi,
\tag{4.1}
$$

where $1\leq\dim M_\pi<\infty$. Strong multiplicity one says that two different global isomorphism classes cannot have almost all the same local components. It does not by itself show that $\dim M_\pi=1$, because two copies of the same representation have identical local components everywhere.

The missing input is the global Whittaker coefficient. It sees an automorphic embedding, not merely an abstract isomorphism class. Local Whittaker uniqueness makes the coefficient unique on the abstract restricted tensor product, while the Fourier--Whittaker expansion reconstructs an automorphic form from that coefficient. Together they force any two embeddings to be proportional.

### 4.2 Whittaker coefficients distinguish embeddings

For a smooth cuspidal form $\phi$, define

$$
W_\phi(g)=\int_{F\backslash\mathbf A}
\phi(n(x)g)\psi(-x)\,dx,
\qquad
n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix},
\tag{4.2}
$$

using probability measure on $F\backslash\mathbf A$. Cuspidality removes the zero Fourier coefficient, and Fourier inversion gives

$$
\phi(g)=\sum_{\xi\in F^\times}
W_\phi\left(\begin{pmatrix}\xi&0\\0&1\end{pmatrix}g\right).
\tag{4.3}
$$

For smooth finite-level, finite-type vectors this series converges absolutely and locally uniformly. Every cuspidal irreducible representation is globally generic, and on its smooth restricted tensor product

$$
\dim\operatorname{Hom}_{N(\mathbf A)}(\pi,\psi)=1.
\tag{4.4}
$$

These are the precise Whittaker results established earlier and needed here.

**Theorem 4.1 (automorphic multiplicity one).** Every irreducible cuspidal automorphic representation of $G(\mathbf A)$ occurs in $L^2_{\mathrm{cusp}}$ with multiplicity one.

**Proof strategy.** Pull the automorphic Whittaker functional back along two embeddings. Global uniqueness makes the pullbacks proportional; the Fourier expansion then makes the embedded forms proportional.

**Proof.** Let $i_1,i_2:\mathcal H_\pi\to L^2_{\mathrm{cusp},\omega}$ be equivariant isometric embeddings. On smooth vectors define

$$
\Lambda_j(v)=W_{i_j(v)}(1).
$$

Global genericity makes each $\Lambda_j$ nonzero, and (4.4) gives $\Lambda_2=c\Lambda_1$ for some $c\ne0$. Therefore, for every smooth $v$ and every $g$,

$$
W_{i_2(v)}(g)=\Lambda_2(\pi(g)v)
=c\Lambda_1(\pi(g)v)=cW_{i_1(v)}(g).
$$

Substituting into (4.3) gives $i_2(v)=ci_1(v)$. Density of smooth vectors extends the equality to the Hilbert completion. Thus the space of embeddings is one dimensional, so $\dim M_\pi=1$. $\square$

Notice where cuspidality enters twice: it guarantees a nonzero Whittaker frequency and it makes the Fourier expansion have no constant term. For an Eisenstein representation, equality of one nonzero Fourier coefficient would not recover the missing constant term.

### 4.3 The multiplicity-free cuspidal decomposition

Combining Theorem 4.1 with the discrete finite-multiplicity decomposition gives

$$
\boxed{
L^2_{\mathrm{cusp},\omega}
=\widehat\bigoplus_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
\mathcal H_\pi.}
\tag{4.5}
$$

The sum is countable. Every fixed finite level, archimedean compact type, and bounded elliptic spectral window meets only finitely many summands. Smooth finite-type vectors in each summand are rapidly decreasing in every cusp.

Equation (4.5) is the global stage on which old/new decompositions will be performed. A factorizable compact-open projector acts diagonally on the summands. Because multiplicity is one, a local newvector line gives one global finite newvector line rather than that line tensored with an unexplained multiplicity space.

### 4.4 Near equivalence becomes equality

Two restricted tensor products are **nearly equivalent** if their local factors are isomorphic outside a finite set. Theorem 3.1 says that among irreducible unitary cuspidal representations of $\mathrm{GL}_2$, every near-equivalence class contains at most one global isomorphism class. Theorem 4.1 says that this class occurs at most once in the cuspidal spectrum.

Thus the cuspidal spectrum may be indexed either by global isomorphism classes or by the near-equivalence classes that actually occur. This equivalence of indexing sets is special and powerful. It allows an unramified Hecke eigensystem to label an entire global summand, including its ramified and archimedean factors, while the conductor identifies the first finite level at which that summand appears.

## 5. Local conductors and normalized newvectors

### 5.1 The subgroup that measures a directed level

Fix a nonarchimedean local field $K$, with integer ring $\mathcal O$, maximal ideal $\mathfrak p=(\varpi)$, and residue cardinality $q$. Put $G_K=\mathrm{GL}_2(K)$ and $K_0=\mathrm{GL}_2(\mathcal O)$. For $n\geq0$, define

$$
K_1(\mathfrak p^n)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in K_0:
c\in\mathfrak p^n,\ d\equiv1\pmod{\mathfrak p^n}
\right\}.
\tag{5.1}
$$

At $n=0$ this is $K_0$. The lower row of a matrix in (5.1) fixes the primitive row vector $(0,1)$ modulo $\mathfrak p^n$. Thus $K_1$ remembers a vector, not merely the line that it spans. The larger group

$$
K_0(\mathfrak p^n)=
\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in K_0:
c\in\mathfrak p^n
\right\}
$$

remembers only that line. The distinction is forced by central characters. A newvector is literally invariant under $K_1$, whereas under $K_0$ it generally transforms by a character of the lower-right entry.

The principal congruence subgroup $1+\mathfrak p^nM_2(\mathcal O)$ is too symmetric for this purpose. Its invariant space may have dimension greater than one at the first nonzero level. The asymmetry of $K_1$ singles out the direction used by a Whittaker coefficient and produces a unique minimal vector.

### 5.2 The conductor exponent

Let $\sigma$ be an irreducible admissible generic representation of $G_K$. Genericity gives a Whittaker model, and it also excludes one-dimensional representations. Define

$$
a(\sigma)=\min\{n\geq0:\sigma^{K_1(\mathfrak p^n)}\ne0\}.
\tag{5.2}
$$

Finiteness of the minimum is part of the local newvector theorem, not part of the definition. A nonzero vector in the space at $n=a(\sigma)$ is a **local newvector**.

If $\omega_\sigma$ is the central character and a vector is fixed at level $n$, then the scalar matrix $uI_2$ fixes it for $u\in1+\mathfrak p^n$. Hence

$$
a(\omega_\sigma)\leq a(\sigma).
\tag{5.3}
$$

This divisibility will globalize to the assertion that the conductor of the central character divides the conductor of the representation.

One-dimensional representations are excluded from (5.2). If $\mu$ is ramified, then $\mu\circ\det$ has no $K_1(\mathfrak p^n)$-fixed vector for any $n$, because $\operatorname{diag}(u,1)$ belongs to every $K_1(\mathfrak p^n)$ while $\mu(u)$ need not be one. More importantly, Book 104 proves that every local component of a cuspidal global representation is generic. Thus the local theorem below applies to every representation that will be globalized, without any appeal to a complete local classification.

### 5.3 The local newvector theorem revisited

The local result needed globally is stronger than uniqueness at the first level: it describes every later fixed space.

**Theorem 5.1 (local newvector and oldvector theorem).** Let $\sigma$ be an irreducible admissible generic representation of $G_K$. Then $a=a(\sigma)$ is finite and

$$
\dim\sigma^{K_1(\mathfrak p^n)}=
\begin{cases}
0,&n<a,\\
n-a+1,&n\geq a.
\end{cases}
\tag{5.4}
$$

If $v^\mathrm{new}$ spans the fixed line at level $a$, then for $n\geq a$ the vectors

$$
v_j=\sigma\left(\begin{pmatrix}\varpi^{-j}&0\\0&1\end{pmatrix}\right)v^\mathrm{new},
\qquad 0\leq j\leq n-a,
\tag{5.5}
$$

form a basis of $\sigma^{K_1(\mathfrak p^n)}$.

**Proof strategy.** Upper-unipotent invariance bounds a Kirillov function, unit invariance makes it constant on valuation shells, and lower-unipotent invariance bounds its Weyl transform. These are two transverse one-step filtrations. Their first intersection is a line, and each subsequent level can add at most one dimension; diagonal translates of the first line add exactly one.

**Proof.** Fix an additive character $\psi_K$ of conductor $\mathcal O$ and realize $\sigma$ in its Kirillov model $\mathcal K(\sigma,\psi_K)$. To a vector $v$ associate

$$
\phi_v(y)=W_v\left(\begin{pmatrix}y&0\\0&1\end{pmatrix}\right),
\qquad y\in K^\times.
$$

The action of the upper unipotent is

$$
(\sigma(n(b))\phi)(y)=\psi_K(by)\phi(y).
\tag{5.6}
$$

Since $n(\mathcal O)\subset K_1(\mathfrak p^n)$, (5.6) forces $\phi(y)=0$ unless $y\in\mathcal O$. Invariance under $\operatorname{diag}(u,1)$ for $u\in\mathcal O^\times$ makes $\phi$ constant on each shell $\varpi^r\mathcal O^\times$.

We isolate the remaining filtration calculation. Let $\mathcal A_r$ be the space of $\mathcal O^\times$-invariant Kirillov functions supported on

$$
\{y\in K^\times:v(y)\geq r\}.
$$

Successive shell evaluation gives

$$
\dim(\mathcal A_r/\mathcal A_{r+1})=1.
$$

Let $\mathcal W$ denote the action of a Weyl element. Since $\bar n(c)=\mathcal W^{-1}n(-c)\mathcal W$ up to a central element, (5.6) and finite Fourier duality say that invariance under every $\bar n(c)$ with $c\in\mathfrak p^n$ is equivalent to

$$
\operatorname{supp}(\mathcal W\phi)
\subseteq\{y:v(y)\geq-n\}.
$$

The opposite filtration has a character that must not be discarded. From

$$
w^{-1}\begin{pmatrix}u&0\\0&1\end{pmatrix}w
=\begin{pmatrix}1&0\\0&u\end{pmatrix}
=uI_2\begin{pmatrix}u^{-1}&0\\0&1\end{pmatrix}
$$

one obtains

$$
(\mathcal W\phi)(uy)=\omega_\sigma(u)(\mathcal W\phi)(y)
\qquad(u\in\mathcal O^\times).
$$

Let $\mathcal B_r$ denote the functions with this unit-character law and support in $v(y)\geq r$. Shell evaluation again gives $\dim(\mathcal B_r/\mathcal B_{r+1})=1$.

The diagonal generators add exactly the remaining central-character condition. Gaussian elimination writes every element of $K_1(\mathfrak p^n)$ as a product of an upper unipotent in $n(\mathcal O)$, a lower unipotent in $\bar n(\mathfrak p^n)$, a matrix $\operatorname{diag}(u,1)$ with $u\in\mathcal O^\times$, and a scalar in $1+\mathfrak p^n$. The last factor acts trivially exactly when $n\geq a(\omega_\sigma)$. Consequently the fixed space is the part of

$$
\mathcal A_0\cap\mathcal W^{-1}\mathcal B_{-n}
$$

on which the scalar condition is satisfied; it is zero when $n<a(\omega_\sigma)$.

Here is the two-bound argument in full. Put $E_n=\sigma^{K_1(\mathfrak p^n)}$. Finite Fourier duality on the last quotient $\mathfrak p^{-n}/\mathfrak p^{-n+1}$, with the scalar-character condition included, gives an injection

$$
E_n/E_{n-1}\hookrightarrow
\mathcal B_{-n}/\mathcal B_{-n+1}.
$$

The one-dimensional shell quotient therefore gives $\dim E_n-\dim E_{n-1}\leq1$. The universal Kirillov-model theorem proved in Book 77 says that $C_c^\infty(K^\times)$ lies in $\mathcal K(\sigma,\psi_K)$ and that the quotient is the finite-dimensional asymptotic space controlled by the Jacquet module. In particular the characteristic function of one integral unit shell is available. It is $\mathcal O^\times$-invariant, has the required upper support, and its Weyl transform is bounded below in valuation. For sufficiently large $n$, also with $n\geq a(\omega_\sigma)$, the two bounds and the subgroup factorization above show that this vector belongs to $E_n$. Hence some $E_n$ is nonzero.

Let $a$ be the first such $n$. The one-step bound makes $E_a$ one dimensional. Choose $0\ne v^{\mathrm{new}}\in E_a$. A direct conjugation gives

$$
\begin{pmatrix}\varpi^j&0\\0&1\end{pmatrix}
K_1(\mathfrak p^n)
\begin{pmatrix}\varpi^{-j}&0\\0&1\end{pmatrix}
\subseteq K_1(\mathfrak p^a)
\qquad(0\leq j\leq n-a),
$$

so the vectors in (5.5) lie in $E_n$. In the two flags above, right translation by $\operatorname{diag}(\varpi^{-j},1)$ moves the lower support boundary through exactly $j$ successive one-dimensional shell quotients. Minimality of $a$ says that the boundary coefficient of $v^{\mathrm{new}}$ is nonzero; its $j$th translate therefore has nonzero image in $E_{a+j}/E_{a+j-1}$. The translates are independent. Thus

$$
n-a+1\leq\dim E_n\leq\dim E_a+(n-a)=n-a+1.
$$

This proves (5.4) and the basis assertion. $\square$

The interval argument explains both uniqueness and linear oldform growth. It also explains why rank two is special: the valuation set is one dimensional. In higher rank, a cone of several valuation parameters replaces the interval.

### 5.4 Whittaker normalization

A one-dimensional fixed line still has an arbitrary scalar. The Whittaker model provides the normalization used in Euler products and global Fourier expansions.

**Proposition 5.2 (normalized local newvector).** Assume $\psi_K$ has conductor $\mathcal O$. If $v^\mathrm{new}$ is a nonzero local newvector in the generic representation $\sigma$, then its Whittaker function satisfies

$$
W_{v^\mathrm{new}}(1)\ne0.
\tag{5.7}
$$

Consequently there is a unique newvector $v^\circ$ in the Whittaker model such that

$$
W_{v^\circ}(1)=1.
\tag{5.8}
$$

**Proof.** In the two-bound proof, the first quotient $E_a/E_{a-1}$ is the unit-shell quotient of $\mathcal A_0$: finite Fourier duality identifies its boundary coefficient with $\phi(1)=W(1)$. That identification is an isomorphism, since the Fourier transform on the finite quotient at the boundary has nonzero Gauss determinant. The image of a nonzero vector spanning $E_a$ is therefore nonzero. Thus $W(1)\ne0$, and unique scaling on the one-dimensional line gives (5.8). $\square$

For an arbitrary nontrivial $\psi_K$, choose $c\in K^\times$ such that $x\mapsto\psi_K(cx)$ has conductor $\mathcal O$. If $W$ is in the $\psi_K$-Whittaker model, then

$$
W^{(c)}(g)=W\left(\begin{pmatrix}c&0\\0&1\end{pmatrix}g\right)
$$

is in the $\psi_K(c\,\cdot)$-model. Hence the intrinsic newvector line is normalized by

$$
W\left(\begin{pmatrix}c&0\\0&1\end{pmatrix}\right)=1.
$$

This states the shift without attaching competing sign conventions to an additive conductor exponent.

At an unramified place, $a(\sigma)=0$ and $v^\circ$ is the normalized spherical vector. If its Satake parameters are $\alpha,\beta$, then

$$
W_{v^\circ}\left(\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}\right)
=\begin{cases}
q^{-m/2}\displaystyle\sum_{j=0}^m\alpha^{m-j}\beta^j,&m\geq0,\\
0,&m<0.
\end{cases}
\tag{5.9}
$$

The value at $m=0$ is one, checking compatibility between spherical and newvector normalizations.

### 5.5 Conductors in the local classification

The abstract definition (5.2) becomes calculable through the local classification.

**Proposition 5.3 (conductor formulas).** The following formulas, proved for these selected classes in Book 77, hold.

1. For an irreducible principal series $I(\chi_1,\chi_2)$,

   $$
   a(I(\chi_1,\chi_2))=a(\chi_1)+a(\chi_2).
   \tag{5.10}
   $$
2. For a special representation,

   $$
   a(\operatorname{St}\otimes\mu)=
   \begin{cases}
   1,&a(\mu)=0,\\
   2a(\mu),&a(\mu)>0.
   \end{cases}
   \tag{5.11}
   $$
3. A depth-zero supercuspidal has conductor exponent $2$.
4. For a minimal tame admissible pair $(L/K,\theta)$,

   $$
   a(\pi(L,\theta))
   =\Delta(L/K)+f(L/K)a_L(\theta),
   \tag{5.12}
   $$

   where $\Delta(L/K)$ is the discriminant exponent and $f(L/K)$ the residue degree.

**Proof.** We recall the calculations from Book 77. For the principal series, the double cosets

$$
(B\cap K_0)\backslash K_0/K_1(\mathfrak p^n)
$$

are indexed by an integer $j$ with $0\leq j\leq n$. Compatibility of an induced function with its stabilizer requires

$$
j\geq a(\chi_1),\qquad n-j\geq a(\chi_2).
$$

The first solution appears when $n$ is the sum in (5.10), and it is then unique.

For unramified $\mu$, the spherical line in the reducible principal series belongs to the one-dimensional constituent, while the Steinberg constituent first has an Iwahori line; this gives exponent one. For ramified $\mu$, both inducing characters have conductor $a(\mu)$, and the one-dimensional constituent has no $K_1$ invariants, so the principal-series fixed line gives (5.11).

A depth-zero supercuspidal has no $K_1(\mathfrak p)$ invariants because its reduction is a cuspidal representation of $\mathrm{GL}_2(k)$, while its finite Whittaker model gives a line at level two. Finally, in the tame compact-induction model, the last nontrivial $L$-unit character contributes $f(L/K)a_L(\theta)$ base-field steps, and duality of lattice filtrations under the trace pairing contributes $\Delta(L/K)$. Minimality prevents cancellation by a norm twist. Their sum is (5.12). $\square$

These formulas are examples, not a restriction of the conductor definition. Wild supercuspidals also have finite conductors and unique newvectors by Theorem 5.1, even when no explicit inducing datum is being used.

### 5.6 Central characters, duals, and twists

The local conductor behaves well under duality:

$$
a(\widetilde\sigma)=a(\sigma).
\tag{5.13}
$$

Indeed fixed spaces dualize, or equivalently the Kirillov shell interval is reflected by the invariant pairing without changing its length. The normalized newvectors of $\sigma$ and $\widetilde\sigma$ pair nontrivially.

Unramified twists preserve conductor. Ramified twists do not obey a formula involving only $a(\sigma)$ and $a(\chi)$, because character conductors of equal depth may cancel. Exact formulas are obtained from the classification:

$$
a(I(\chi_1,\chi_2)\otimes\mu)
=a(\chi_1\mu)+a(\chi_2\mu),
\tag{5.14}
$$

with analogous substitution in (5.11) and (5.12). When $\mu$ is deeper than every character visible in the Kirillov asymptotics of $\sigma$, cancellation is impossible and

$$
a(\sigma\otimes\mu)=2a(\mu).
\tag{5.15}
$$

At the boundary of equal depths, (5.15) can fail. This warning becomes important globally: twisting a newform can lower as well as raise some local conductor exponents.

## 6. The local oldform tower

### 6.1 Raising the level

Fix $\sigma$ and write $a=a(\sigma)$. Let

$$
V_n=\sigma^{K_1(\mathfrak p^n)}.
$$

The groups shrink with $n$, so there are inclusions

$$
V_{n-1}\subseteq V_n.
\tag{6.1}
$$

There is also a translated inclusion. Put

$$
t=\begin{pmatrix}\varpi^{-1}&0\\0&1\end{pmatrix}.
$$

If $v\in V_{n-1}$, then $\sigma(t)v\in V_n$. To check this, for $k\in K_1(\mathfrak p^n)$ compute $t^{-1}kt$. The lower-left entry loses one power of $\varpi$ and remains in $\mathfrak p^{n-1}$; the upper-right entry gains one and remains integral; and the lower-right congruence remains at least $n-1$. Hence

$$
t^{-1}K_1(\mathfrak p^n)t
\subseteq K_1(\mathfrak p^{n-1}),
$$

which is enough for the asserted invariance. This elementary conjugation is the local origin of the two classical degeneracy maps $f(z)\mapsto f(z)$ and $f(z)\mapsto f(\varpi z)$, up to the right-action convention.

### 6.2 The oldvector basis

Choose the normalized newvector $v_0=v^\circ$ and set

$$
v_j=\sigma(t^j)v_0.
$$

Theorem 5.1 says

$$
V_n=\bigoplus_{j=0}^{n-a}\mathbf Cv_j
\qquad(n\geq a).
\tag{6.2}
$$

These are called oldvectors when $j>0$ or when they are viewed above the minimal level. Their linear independence has a transparent Whittaker explanation: the Kirillov function of $v_j$ begins on a different valuation shell. Thus no analytic orthogonality is needed to prove that they form a basis.

The basis depends on the uniformizer and on the chosen direction in $K_1$. The subspace $V_n$ and its filtration by lower levels do not. Replacing $\varpi$ by a unit multiple rescales and triangularly changes the basis through the unit action.

### 6.3 Two degeneracy maps

For $n>a$, define

$$
d_0,d_1:V_{n-1}\longrightarrow V_n,
\qquad d_0(v)=v,\qquad d_1(v)=\sigma(t)v.
\tag{6.3}
$$

By (6.2),

$$
d_0(V_{n-1})=\operatorname{span}(v_0,\ldots,v_{n-a-1}),
$$

and

$$
d_1(V_{n-1})=\operatorname{span}(v_1,\ldots,v_{n-a}).
$$

Therefore

$$
d_0(V_{n-1})+d_1(V_{n-1})=V_n
\qquad(n>a).
\tag{6.4}
$$

At $n=a$, the source $V_{a-1}$ is zero and the newvector line is not old. Formula (6.4) is the exact local statement from which the global old/new theorem follows.

The two images overlap in dimension $n-a-1$ when $n\geq a+2$. Hence an oldspace should be defined as their sum, not as a direct sum. Treating degeneracy images as automatically independent gives incorrect dimension formulas at prime-power level.

### 6.4 A local new quotient

Define the algebraic new quotient at level $n$ by

$$
Q_n(\sigma)=
V_n\big/\bigl(d_0(V_{n-1})+d_1(V_{n-1})\bigr).
\tag{6.5}
$$

Then (6.4) gives

$$
\dim Q_n(\sigma)=
\begin{cases}
1,&n=a(\sigma),\\
0,&n\ne a(\sigma).
\end{cases}
\tag{6.6}
$$

Here $V_{-1}=0$. Thus the conductor exponent is characterized without mentioning a minimum: it is the unique level at which the local new quotient is nonzero.

For a unitary representation one may instead take the orthogonal complement of the old sum in $V_n$. It has the same dimension as (6.6), but it need not be spanned by $v_0$ when $n>a$ because the oldvector basis is generally not orthogonal. At the minimal level the distinction disappears.

### 6.5 Hecke recurrences on the tower

When $a=0$, the spherical Hecke operator gives a second-order recurrence among the diagonal translates. If $T$ is the raw double-coset operator and the Satake parameters are $\alpha,\beta$, then the normalized diagonal Whittaker values

$$
c_m=q^{m/2}W_{v_0}\left(\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}\right)
$$

satisfy

$$
c_{m+2}=(\alpha+\beta)c_{m+1}-\alpha\beta c_m,
\qquad c_0=1,\qquad c_1=\alpha+\beta.
\tag{6.7}
$$

Thus $c_m=\sum_{j=0}^m\alpha^{m-j}\beta^j$, recovering (5.9).

At ramified level, operators supported on $K_1(\mathfrak p^n)tK_1(\mathfrak p^n)$ act on the oldvector tower by a companion-type matrix whose boundary terms depend on the central character and local representation. Their detailed eigenvalues are not needed for the decomposition: (6.4), which is purely representation-theoretic, already shows that every appearance above the conductor is old. This separation prevents a choice of ramified Hecke normalization from entering the definition of newness.

## 7. Global conductors and adelic levels

### 7.1 The conductor ideal

Let $\pi=\otimes_v'\pi_v$ be an irreducible cuspidal automorphic representation. Book 104 proves that every $\pi_v$ is generic, so Theorem 5.1 applies at every finite place. Almost every finite $\pi_v$ is spherical, so $a(\pi_v)=0$ almost everywhere. The product

$$
\mathfrak c(\pi)=\prod_{v<\infty}\mathfrak p_v^{a(\pi_v)}
\tag{7.1}
$$

is therefore a well-defined nonzero integral ideal, called the **finite conductor** of $\pi$. Its absolute norm is

$$
N\mathfrak c(\pi)=\prod_{v<\infty}q_v^{a(\pi_v)}.
\tag{7.2}
$$

This is the representation-theoretic conductor. In the Rankin--Selberg functional equation it contributes to the arithmetic conductor together with archimedean normalization and, for a pair, tensor-product local exponents. We do not identify these different conductors merely because they use the same word.

Let $\mathfrak f_\omega$ be the conductor of the finite part of the central character. Inequality (5.3) at every place gives

$$
\mathfrak f_\omega\mid\mathfrak c(\pi).
\tag{7.3}
$$

### 7.2 The global $K_1$ subgroup

For an integral ideal

$$
\mathfrak n=\prod_{v<\infty}\mathfrak p_v^{n_v},
$$

define

$$
K_1(\mathfrak n)=\prod_{v<\infty}K_1(\mathfrak p_v^{n_v}),
\tag{7.4}
$$

where the factor is $K_v$ when $n_v=0$. This is a compact open subgroup of $G(\mathbf A_f)$. The inclusion direction is

$$
\mathfrak m\mid\mathfrak n
\quad\Longrightarrow\quad
K_1(\mathfrak n)\subseteq K_1(\mathfrak m),
\tag{7.5}
$$

so invariant spaces grow with the ideal.

If the central character is ramified, scalar compatibility again matters. A $K_1(\mathfrak n)$-fixed vector can occur only when $\mathfrak f_\omega\mid\mathfrak n$. The corresponding $K_0(\mathfrak n)$ formulation uses the lower-right character; the $K_1$ formulation avoids building that character into every invariant-space notation.

### 7.3 Factorization of level invariants

Apply Proposition 2.3 and Theorem 5.1.

**Theorem 7.1 (global level dimension).** For every integral ideal $\mathfrak n$,

$$
\pi_f^{K_1(\mathfrak n)}\ne0
\quad\Longleftrightarrow\quad
\mathfrak c(\pi)\mid\mathfrak n.
\tag{7.6}
$$

When divisibility holds,

$$
\dim\pi_f^{K_1(\mathfrak n)}
=\prod_{v<\infty}\bigl(n_v-a(\pi_v)+1\bigr).
\tag{7.7}
$$

**Proof.** Factorization gives

$$
\pi_f^{K_1(\mathfrak n)}
\cong\bigotimes_{v<\infty}
\pi_v^{K_1(\mathfrak p_v^{n_v})}.
$$

The local factor is nonzero exactly when $n_v\geq a(\pi_v)$, and then has dimension $n_v-a(\pi_v)+1$. Multiplying proves both assertions. Almost every factor has $n_v=a(\pi_v)=0$ and dimension one, so the product is finite. $\square$

For $F=\mathbf Q$, if $\mathfrak n=(N)$ and the conductor is $(M)$, formula (7.7) becomes

$$
\dim\pi_f^{K_1(N)}
=\prod_{p\mid N}\bigl(v_p(N)-v_p(M)+1\bigr)
$$

when $M\mid N$. This counts tuples of local degeneracy exponents, not divisors with arbitrary prime support: the two descriptions agree because such tuples are exactly the divisors of $N/M$.

### 7.4 The global newvector line

Taking $\mathfrak n=\mathfrak c(\pi)$ in (7.7) gives

$$
\boxed{\dim\pi_f^{K_1(\mathfrak c(\pi))}=1.}
\tag{7.8}
$$

For each finite $v$, choose $c_v\in F_v^\times$ so that $x\mapsto\psi_v(c_vx)$ has conductor $\mathcal O_v$, and normalize the local newvector by

$$
W_v^\circ\left(\begin{pmatrix}c_v&0\\0&1\end{pmatrix}\right)=1.
$$

Both $\psi_v$ and $\pi_v$ are unramified at almost every finite place, so $c_v=1$ may be taken there and $v_v^\circ$ is the normalized spherical reference vector. Consequently the pure tensor

$$
v_f^\mathrm{new}=\bigotimes_{v<\infty}v_v^\circ
\tag{7.9}
$$

is meaningful and spans the line. The line itself is independent of $\psi$; only this scalar normalization uses the additive character.

The associated global newform space inside the representation is

$$
\pi_\infty\otimes\mathbf Cv_f^\mathrm{new}.
\tag{7.10}
$$

It is generally infinite dimensional: no archimedean vector has yet been selected. A classical holomorphic newform arises after choosing a lowest-weight line at the archimedean places. A Maass newform arises after choosing an archimedean compact type and an eigenvector for the center of the enveloping algebra. Calling (7.10) a line without the word “finite” would therefore be incorrect.

### 7.5 Normalized global Whittaker functions

Use the finite normalizations from Section 7.4, and at every archimedean place choose a nonzero Whittaker vector $W_v$. Global Whittaker uniqueness permits one overall normalization for which the pure-tensor automorphic Whittaker function factors:

$$
W(g)=\prod_vW_v(g_v).
\tag{7.11}
$$

Almost every factor at $g_v=1$ is one. Let $c_f=(c_v)_{v<\infty}$, a finite idele, and put $a(c_f)_v=\operatorname{diag}(c_v,1)$ at finite places and $a(c_f)_v=1$ at infinity. If the archimedean product is normalized at the identity, then $W(a(c_f))=1$. When every finite $\psi_v$ already has conductor $\mathcal O_v$, this is the familiar statement $W(1)=1$. More generally it is often preferable to normalize an archimedean vector by its $L^2$ norm or lowest-weight coefficient; (7.11) then records the remaining explicit scalar.

The automorphic form is reconstructed by

$$
\phi(g)=\sum_{\xi\in F^\times}
\prod_vW_v\left(
\begin{pmatrix}\xi&0\\0&1\end{pmatrix}g_v
\right).
\tag{7.12}
$$

This is the adelic newform expansion. Finite conductor controls which local Whittaker functions occur, while archimedean type controls their analytic shape. Strong multiplicity one says that the unramified factors in (7.12) already determine all the ramified factors up to the unique global isomorphism class.

## 8. Old and new subspaces at finite level

### 8.1 Degeneracy maps between adelic levels

Fix a unitary central character $\omega$ and write

$$
\mathcal H(\mathfrak n)
=L^2_{\mathrm{cusp},\omega}{}^{K_1(\mathfrak n)}.
\tag{8.1}
$$

This remains a Hilbert representation of $G(F_\infty)$. If $\mathfrak p\mid\mathfrak n$, choose the finite adele $t_\mathfrak p$ whose $\mathfrak p$-component is $\operatorname{diag}(\varpi_\mathfrak p^{-1},1)$ and whose other components are one. There are two bounded maps

$$
D_{\mathfrak p,0},D_{\mathfrak p,1}:
\mathcal H(\mathfrak n/\mathfrak p)\longrightarrow\mathcal H(\mathfrak n),
\tag{8.2}
$$

given by

$$
D_{\mathfrak p,0}\phi=\phi,qquad
D_{\mathfrak p,1}\phi=R(t_\mathfrak p)\phi.
\tag{8.3}
$$

The first map uses (7.5). The second is well defined by the local conjugation calculation of Section 6.1. Right translation is unitary on the ambient cuspidal space, so both maps are bounded. Their ranges need not be orthogonal and need not meet trivially.

Changing the uniformizer multiplies $t_\mathfrak p$ by a compact diagonal element. This changes the second map inside the span of the same local oldvector tower and therefore does not change the oldspace defined below.

### 8.2 The closed oldspace

Define the **oldspace at level $\mathfrak n$** by

$$
\mathcal H_\mathrm{old}(\mathfrak n)
=\overline{\sum_{\mathfrak p\mid\mathfrak n}
\left(
D_{\mathfrak p,0}\mathcal H(\mathfrak n/\mathfrak p)
+D_{\mathfrak p,1}\mathcal H(\mathfrak n/\mathfrak p)
\right)}.
\tag{8.4}
$$

The closure is included because $\mathcal H(\mathfrak n)$ may still be infinite dimensional at infinity. After fixing an archimedean compact type and bounded spectral window, the relevant space is finite dimensional and the closure becomes unnecessary.

It is enough to use immediate lower levels $\mathfrak n/\mathfrak p$. Iterating the maps reaches every proper divisor level and produces every tuple of local translates. Conversely every immediate image plainly comes from a proper lower level. Thus (8.4) agrees with the closed span of all degeneracy images from all proper divisors of $\mathfrak n$.

### 8.3 The orthogonal newspace

Define

$$
\mathcal H_\mathrm{new}(\mathfrak n)
=\mathcal H_\mathrm{old}(\mathfrak n)^\perp
\subseteq\mathcal H(\mathfrak n).
\tag{8.5}
$$

This definition is intrinsic to the unitary automorphic Hilbert space. It is compatible with archimedean type and spectral projections because the degeneracy maps commute with the archimedean action.

To identify (8.5), use the multiplicity-free decomposition (4.5). Taking $K_1(\mathfrak n)$ invariants gives

$$
\mathcal H(\mathfrak n)
=\widehat\bigoplus_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\mathfrak c(\pi)\mid\mathfrak n}}
\mathcal H_{\pi,\infty}\widehat\otimes
\pi_f^{K_1(\mathfrak n)}.
\tag{8.6}
$$

The sum is orthogonal between distinct $\pi$. It remains to identify the oldspace inside each finite-dimensional factor.

### 8.4 The global newform decomposition

**Theorem 8.1 (global old/new decomposition).** For every integral ideal $\mathfrak n$,

$$
\boxed{
\mathcal H_\mathrm{new}(\mathfrak n)
=\widehat\bigoplus_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
\mathfrak c(\pi)=\mathfrak n}}
\mathcal H_{\pi,\infty}\widehat\otimes
\mathbf Cv_f^\mathrm{new}.}
\tag{8.7}
$$

Moreover

$$
\mathcal H(\mathfrak n)
=\mathcal H_\mathrm{old}(\mathfrak n)
\widehat\oplus
\mathcal H_\mathrm{new}(\mathfrak n).
\tag{8.8}
$$

**Proof strategy.** Work one irreducible summand at a time. If its conductor is strictly smaller than the level, choose a prime at which the exponent is smaller; the two local degeneracy images span the full fixed space. If its conductor equals the level, every immediate lower-level invariant space vanishes at the prime being lowered, so its one-dimensional finite line receives no oldform.

**Proof.** Fix $\pi$ contributing to (8.6), and write $a_v=a(\pi_v)$. If $\mathfrak c(\pi)\ne\mathfrak n$, there is a prime $\mathfrak p$ with $a_\mathfrak p<n_\mathfrak p$. Factorization separates the $\mathfrak p$-component:

$$
\pi_f^{K_1(\mathfrak n)}
\cong
\pi_\mathfrak p^{K_1(\mathfrak p^{n_\mathfrak p})}
\otimes\bigotimes_{v\ne\mathfrak p}
\pi_v^{K_1(\mathfrak p_v^{n_v})}.
$$

By (6.4), the first factor is the sum of the identity and translated images of its level $n_\mathfrak p-1$ fixed space. Tensoring with the other factors shows that the entire $\pi$-part of level $\mathfrak n$ lies in (8.4).

If $\mathfrak c(\pi)=\mathfrak n$, then lowering the exponent at any $\mathfrak p\mid\mathfrak n$ gives $n_\mathfrak p-1<a_\mathfrak p$, so the local invariant factor is zero. Hence no degeneracy map from an immediate lower level has a component in the $\pi$-summand. Its level-$\mathfrak n$ finite fixed space is the line (7.8), and it lies in the orthogonal complement of the oldspace.

The orthogonal decomposition (4.5) now gives (8.7). Since the oldspace was defined as closed, the elementary Hilbert identity $H=M\widehat\oplus M^\perp$ gives (8.8). $\square$

The theorem is exact even when $\mathfrak n$ is divisible by high prime powers. No squarefreeness, trivial central character, or holomorphic archimedean hypothesis is present.

### 8.5 Dimension and multiplicity formulas

At a fixed archimedean compact type $\tau$ and infinitesimal character $\lambda$, all spaces in sight are finite dimensional. Let

$$
m_\infty(\pi,\tau)=\dim\mathcal H_{\pi,\infty}(\tau).
$$

Then (7.7) and (8.6) give

$$
\dim\mathcal H(\mathfrak n,\tau)[\lambda]
=\sum_{\substack{\pi:\ \mathfrak c(\pi)\mid\mathfrak n\\
\lambda_\pi=\lambda}}
m_\infty(\pi,\tau)
\prod_v(n_v-a(\pi_v)+1),
\tag{8.9}
$$

while the newspace dimension is

$$
\dim\mathcal H_\mathrm{new}(\mathfrak n,\tau)[\lambda]
=\sum_{\substack{\pi:\ \mathfrak c(\pi)=\mathfrak n\\
\lambda_\pi=\lambda}}
m_\infty(\pi,\tau).
\tag{8.10}
$$

There is no automorphic multiplicity factor in either formula. The only possible factor is the intrinsic multiplicity of the chosen compact type inside the archimedean representation. For a holomorphic lowest-weight line this is one, recovering the familiar statement that one normalized classical newform represents each Hecke eigensystem.

One can also rewrite the oldvector factor as a divisor count:

$$
\prod_v(n_v-a_v+1)
=\#\{\mathfrak d:\mathfrak d\mid\mathfrak n/\mathfrak c(\pi)\}.
\tag{8.11}
$$

Each divisor $\mathfrak d$ corresponds to the pure tensor translate with local exponent $v(\mathfrak d)$. This is a basis count, not an orthogonality statement.

## 9. Hecke operators and recognition of newforms

### 9.1 Unramified Hecke operators

Let $v$ be finite and suppose $\pi_v$ is unramified. Normalize Haar measure by $\operatorname{vol}(K_v)=1$. The spherical Hecke algebra

$$
\mathcal H_v=C_c(K_v\backslash G(F_v)/K_v)
$$

acts on the line $\pi_v^{K_v}$ through a character. Two convenient generators are

$$
T_v=\mathbf1_{K_v\operatorname{diag}(\varpi_v,1)K_v},
\qquad
S_v=\mathbf1_{K_v(\varpi_vI_2)K_v}.
\tag{9.1}
$$

If $A_v(\pi)=\{\alpha_v,\beta_v\}$, the elementary Satake calculation gives

$$
T_v\longmapsto q_v^{1/2}(\alpha_v+\beta_v),
\qquad
S_v\longmapsto\alpha_v\beta_v.
\tag{9.2}
$$

Equivalently, for the normalized operator $\mathsf T_v=q_v^{-1/2}T_v$, the Hecke polynomial is

$$
1-\mathsf T_vX+S_vX^2
\tag{9.3}
$$

when interpreted on the spherical line. Changing to an algebraic normalization for forms of cohomological weight twists both the parameters and the power of $q_v$ in (9.2). The invariant content is the polynomial (1.1) after the chosen twist has been stated.

The convolution algebra is commutative. One direct reason is that the Satake transform sends it to the symmetric Laurent polynomials in two variables. The Weyl symmetry forgets the ordering of the two diagonal characters, exactly as the spherical representation does.

### 9.2 Eigenvalues determine the unramified component

**Proposition 9.1.** Two irreducible spherical representations $\sigma$ and $\sigma'$ of $G(F_v)$ are isomorphic if and only if the eigenvalues of both $T_v$ and $S_v$ on their spherical lines agree.

**Proof.** The two eigenvalues determine the sum and product of the Satake parameters through (9.2), hence determine the quadratic polynomial whose unordered roots are the parameters. The local spherical classification identifies the unique irreducible spherical constituent attached to that unordered pair. The converse is immediate. $\square$

If the central characters agree, $S_v$ acts by their common value on $\varpi_v$, so $T_v$ alone suffices. If central characters are not fixed, a single trace can come from different determinants. This elementary ambiguity is why a strong multiplicity-one statement based only on unnamed “Hecke eigenvalues” is incomplete.

### 9.3 Multiplicity one for Hecke eigensystems

Let $\mathfrak n$ be a level and fix an archimedean irreducible compact type and infinitesimal character so that the corresponding newspace is finite dimensional.

**Theorem 9.2 (newform eigensystem multiplicity one).** Suppose $\phi$ and $\phi'$ are nonzero simultaneous eigenvectors in the newspace of level $\mathfrak n$, with the same central character and the same archimedean irreducible data. If their $T_v$ eigenvalues agree for all but finitely many $v\nmid\mathfrak n$, then $\phi$ and $\phi'$ belong to the same cuspidal automorphic representation. If the chosen archimedean type occurs with multiplicity one, then $\phi'$ is a scalar multiple of $\phi$.

**Proof strategy.** Attach a global summand to each eigenvector, reconstruct almost every Satake polynomial, use strong multiplicity one, and then use the one-dimensional finite newvector line.

**Proof.** Decomposition (8.7) writes each newvector as a finite orthogonal sum of components from representations of conductor $\mathfrak n$. Every nonzero component of a simultaneous eigenvector has that same unramified Hecke character, because the Hecke operators preserve each orthogonal summand. Choose nonzero components of $\phi$ and $\phi'$ in summands $\pi$ and $\rho$. Since the central characters agree, equality of $T_v$ eigenvalues gives equality of the $S_v$ eigenvalues and hence of the local Hecke polynomials outside a finite set. Corollary 3.2 yields $\pi\simeq\rho$. The same argument identifies any other nonzero component with $\pi$, and automorphic multiplicity one says that there is only one such summand.

The finite newvector space of this representation is one dimensional. Thus the only remaining freedom lies in the chosen archimedean type space. If that type has multiplicity one, the entire tensor line is one dimensional and the two vectors are proportional. $\square$

Thus every occurring unramified eigensystem has one global source. This is stronger than merely saying that every individual summand has a Hecke character: it rules out a linear combination of distinct global sources with the same almost-everywhere eigenvalues.

### 9.4 Ramified operators and what they do not determine

At $v\mid\mathfrak n$, the $K_1(\mathfrak p_v^{n_v})$-fixed space can have dimension greater than one for an old representation. Its Hecke algebra need not act through a single character, and different normalizations of the operator usually called $U_v$ differ by central and modulus factors. Newness is therefore defined by minimal level or by orthogonal complement, not by a prescribed $U_v$ eigenvalue.

On the one-dimensional local newvector line at $n_v=a(\pi_v)$, every operator preserving that line does act by a scalar. This scalar can encode the surviving Euler root: an unramified twist of Steinberg has one standard Euler factor, while a sufficiently ramified principal series or a supercuspidal representation may have standard local factor $1$. The absence of an Euler denominator does not mean the local representation is absent; its conductor, central character, epsilon factor, and ramified Hecke action carry the missing information.

Strong multiplicity one deliberately avoids reconstructing those ramified invariants one by one. Once the global representation is identified from its unramified factors, uniqueness of local factorization recovers the ramified component as a whole.

## 10. Classical forms through the adelic dictionary

### 10.1 From congruence level to $K_1$ level

The adelic theorem contains the familiar theory of classical modular newforms, but the translation must respect the distinction between $K_0$ and $K_1$. Consider first $F=\mathbf Q$. A classical form of level $N$ and nebentype $\chi$ gives an automorphic form whose finite component is fixed by $K_1(N)$. Under $K_0(N)$ it transforms through the lower-right entry by the finite character corresponding to $\chi$:

$$
R(k)\phi=\chi(d)\phi,
\qquad
k=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in K_0(N),
\tag{10.1}
$$

after the standard agreement between the classical slash action and right adelic translation. On $K_1(N)$, $d\equiv1\pmod N$ and the character disappears.

The archimedean component carries the weight. A holomorphic cusp form of weight $k\geq2$ selects a lowest-weight line in a discrete-series representation of $\mathrm{GL}_2(\mathbf R)$, together with a compatible action of the center. A weight-zero Maass form selects a compact type and a Laplace eigenvalue instead. The finite conductor is independent of which nonzero vector is chosen within the archimedean representation.

Thus a classical level is an upper bound for the representation conductor. A classical form may be old at $N$ because its automorphic representation has conductor $M$ properly dividing $N$.

### 10.2 $q$-expansions and Whittaker normalization

For a holomorphic cusp form

$$
f(z)=\sum_{m\geq1}a_m e^{2\pi imz},
\tag{10.2}
$$

the coefficient $a_1$ is the classical shadow of the global Whittaker coefficient at the identity for the standard character of $\mathbf Q\backslash\mathbf A$, whose finite local components have conductor $\mathbf Z_p$, after the fixed archimedean Whittaker function has been normalized. Scaling $f$ so that

$$
a_1=1
\tag{10.3}
$$

corresponds to choosing the product normalization in which the finite local newvectors satisfy $W_p(1)=1$ and the remaining global scalar is absorbed at infinity. For a different global additive character, Section 7.5 replaces the identity by $a(c_f)$.

The Hecke recurrence for a normalized eigenform at a prime $p\nmid N$ is the classical form of (6.7). In a common algebraic normalization,

$$
a_{p^{r+2}}=a_p a_{p^{r+1}}-\chi(p)p^{k-1}a_{p^r}.
\tag{10.4}
$$

The roots of

$$
1-a_pX+\chi(p)p^{k-1}X^2
\tag{10.5}
$$

are the algebraically normalized Satake parameters. The appropriate power of $|\det|$ converts between (10.5) and the unitary polynomial (1.1); the sign of that power depends on which direction the conversion is made. The recurrence itself makes the normalization visible and prevents an unnoticed half-power shift.

**Corollary 10.1 (classical strong multiplicity one).** Let $f$ and $g$ be normalized cuspidal newforms of the same weight and nebentype, not necessarily initially presented with the same level. If

$$
a_p(f)=a_p(g)
$$

for all but finitely many primes $p$, then $f=g$ and their primitive levels are equal.

**Proof.** Equality of nebentype supplies equality of the determinant terms in (10.5); equality of $a_p$ supplies the trace terms. Hence the associated unitary automorphic representations have the same unramified local factors almost everywhere. Strong multiplicity one identifies them. Their conductor ideals, and therefore their primitive levels, agree. Their finite newvector lines and lowest-weight lines are one dimensional, and the normalization $a_1=1$ removes the final scalar. $\square$

The same conclusion can fail if “newform” is replaced by an arbitrary old eigenvector without controlling the degeneracy space: one representation can supply several linearly independent vectors at the same higher level. The primitive representation is still unique, but the oldvector is not.

### 10.3 Classical oldforms

Let $f$ be a primitive form of level $M$, and suppose $M\mid N$. The adelic basis indexed by divisors of $N/M$ translates classically into

$$
f_d(z)=f(dz),
\qquad d\mid N/M,
\tag{10.6}
$$

with conventional powers of $d$ inserted if the slash action is normalized unitarily. These vectors span the contribution of the automorphic representation of $f$ to level $N$.

Their number is

$$
\#\{d:d\mid N/M\}
=\prod_p\bigl(v_p(N)-v_p(M)+1\bigr),
\tag{10.7}
$$

which is exactly (7.7). Linear independence follows adelically from distinct first Kirillov shells and classically from comparing the first nonzero exponents in the Fourier series. The vectors need not be orthogonal for the Petersson inner product. Orthogonalizing them changes the convenient divisor-indexed basis but not their span.

The oldspace at level $N$ is generated already by the two images from each immediate level $N/p$:

$$
h(z)\longmapsto h(z),qquad
h(z)\longmapsto h(pz).
\tag{10.8}
$$

Repeated application gives (10.6). At prime powers the two immediate images overlap substantially, exactly as in Section 6.3.

### 10.4 Squarefree and prime-power examples

Suppose a representation has conductor $M$ and $N/M$ is squarefree with $r$ prime factors. Each such prime contributes a two-dimensional local fixed space at the raised level, so the oldspace contribution has dimension

$$
2^r.
\tag{10.9}
$$

Its natural basis is indexed by subsets of the new primes, equivalently by divisors of $N/M$.

Now suppose $N/M=p^r$. The contribution has dimension $r+1$, with basis

$$
f(z),f(pz),\ldots,f(p^rz).
\tag{10.10}
$$

It is not $2^r$ dimensional. Although two degeneracy maps are available at each step, their images overlap; the recurrence of local invariant dimensions is linear, not exponential.

For an unramified representation raised to level $p^2$, the three local basis vectors are $v_0,v_1,v_2$. The two images from level $p$ are

$$
\operatorname{span}(v_0,v_1),qquad
\operatorname{span}(v_1,v_2),
$$

whose intersection is $\mathbf Cv_1$. Their sum is three dimensional. This elementary example is the best guard against treating degeneracy maps as independent copies.

If a representation has local conductor exponent two, as a depth-zero supercuspidal does, it contributes nothing at levels $1$ and $p$, a one-dimensional new line at $p^2$, and dimensions $2,3,\ldots$ at $p^3,p^4,\ldots$. The same oldform growth occurs regardless of the very different internal construction of the supercuspidal representation.

### 10.5 Hilbert modular forms

For a totally real field $F$, a cohomological cuspidal representation with discrete-series component of weight $k_v$ at each real place gives a Hilbert modular eigenform. Its finite conductor is an ideal rather than an integer. For $\mathfrak c(\pi)\mid\mathfrak n$, its oldforms are indexed by ideals

$$
\mathfrak d\mid\mathfrak n/\mathfrak c(\pi),
$$

and their number is the ideal-divisor function in (8.11). There is no need for the class number to be one: the adelic formulation already includes every connected component and every cusp.

Parallel weight is not required. The finite newvector theorem is independent of the tuple of archimedean weights. After fixing a lowest-weight line at each infinite place, strong multiplicity one says that the unramified Hecke polynomials at almost every prime ideal determine the primitive Hilbert eigenform, provided the normalization and central character supply both trace and determinant.

For number fields with complex places there may be no holomorphic classical model, but the adelic newform space (7.10) and decomposition (8.7) remain unchanged. This illustrates why the representation-theoretic statement is the primary one.

## 11. Duality, twisting, and level symmetry

### 11.1 Contragredient newforms

Local duality preserves conductor exponent, so globally

$$
\mathfrak c(\widetilde\pi)=\mathfrak c(\pi).
\tag{11.1}
$$

The central character becomes $\omega^{-1}$. The invariant pairing between $\pi_v$ and $\widetilde\pi_v$ is nondegenerate on their one-dimensional newvector lines. Scaling the dual newvector gives

$$
\langle v_v^\circ,\widetilde v_v^\circ\rangle_v=1.
\tag{11.2}
$$

At almost every place this agrees with the normalized spherical pairing. Their restricted product therefore pairs the finite global newvector lines perfectly.

In Whittaker models, $\pi_v$ uses $\psi_v$ and $\widetilde\pi_v$ naturally uses $\psi_v^{-1}$. A regularized integral over $F_v^\times$ realizes the pairing; for supercuspidals it is an actual finite shell sum. Confusing the two Whittaker signs would destroy $N$-invariance of the product.

The oldvector basis dualizes by a generally non-diagonal Gram matrix. Contragredience preserves the filtration and its dimensions, not the assertion that corresponding translates are orthogonal.

### 11.2 Twists and conductor change

Let $\chi:F^\times\backslash\mathbf A^\times\to\mathbf C^\times$ be a unitary Hecke character. Then

$$
\pi\otimes\chi
=\bigotimes_v'(\pi_v\otimes\chi_v),
\tag{11.3}
$$

where the local twist means $g\mapsto\chi_v(\det g)$. Its conductor is

$$
\mathfrak c(\pi\otimes\chi)
=\prod_{v<\infty}\mathfrak p_v^{a(\pi_v\otimes\chi_v)}.
\tag{11.4}
$$

An unramified character preserves every local exponent. For a deeply ramified $\chi_v$, stable behavior gives $a(\pi_v\otimes\chi_v)=2a(\chi_v)$. Between these regimes cancellation can occur.

For example, if

$$
\pi_v=I(\mu,\nu)
$$

and $\chi_v=\mu^{-1}$ on the relevant unit quotient, then

$$
a(\pi_v\otimes\chi_v)
=a(1)+a(\nu\mu^{-1}),
$$

which can be smaller than $a(\mu)+a(\nu)$. Thus the tempting formula

$$
\mathfrak c(\pi\otimes\chi)
=\operatorname{lcm}(\mathfrak c(\pi),\mathfrak f_\chi^2)
$$

is false without a noncancellation hypothesis.

Twisting transports the normalized newvector line to the newvector line of the twist only when the level remains minimal under the exact local formula. The underlying vector space may be the same, but its $K_1$ invariance changes because $\chi_v(\det k)$ need not be trivial. Recomputing the conductor is essential.

Strong multiplicity one is compatible with twists: if $\pi_v\simeq\rho_v$ almost everywhere, then $\pi_v\otimes\chi_v\simeq\rho_v\otimes\chi_v$ almost everywhere, and hence $\pi\otimes\chi\simeq\rho\otimes\chi$. Conversely twisting both sides by $\chi^{-1}$ recovers the original theorem.

### 11.3 Atkin--Lehner symmetry

At a local conductor exponent $a$, introduce

$$
w_a=\begin{pmatrix}0&1\\-\varpi^a&0\end{pmatrix}.
\tag{11.5}
$$

This matrix exchanges the two directed lattice filtrations. It conjugates the $K_0(\mathfrak p^a)$ level to itself, but it exchanges the lower-right nebentype with the corresponding upper-left character. The Weyl transform carries the standard line to the opposite line inside the same representation; the invariant pairing compares this construction with the parallel construction in the contragredient. Thus Whittaker normalizations determine a nonzero comparison scalar.

The local functional equation identifies the comparison scalar between Whittaker-normalized standard and opposite vectors, up to the explicit Haar and additive-character factors, with the local epsilon factor at the center. The structural statement needed here is simpler:

**Proposition 11.1 (newvector symmetry).** The action of $w_a$ carries the $K_0$-newvector character line of $\pi_v$ isomorphically to its opposite newvector character line. It does the same for $\widetilde\pi_v$, and the invariant pairing is perfect on the two transported opposite lines.

To state the identification precisely, put

$$
K_1'(\mathfrak p^a)=w_aK_1(\mathfrak p^a)w_a^{-1}.
\tag{11.6}
$$

The opposite line means $\pi_v^{K_1'(\mathfrak p^a)}$. In the $K_0$ formulation, if the standard line transforms by $k\mapsto\omega_v(d)$, the opposite line transforms by $k\mapsto\omega_v(a)$. There is no canonical identification of a line in $\pi_v$ with a line in the different representation $\widetilde\pi_v$. What is canonical is the invariant pairing after both lines are transported, together with the Whittaker functional equation that compares their chosen normalizations.

**Proof.** If $v$ is fixed by $K_1(\mathfrak p^a)$ and $k'=w_akw_a^{-1}$ belongs to $K_1'(\mathfrak p^a)$, then

$$
\pi_v(k')\pi_v(w_a)v
=\pi_v(w_a)\pi_v(k)v
=\pi_v(w_a)v.
$$

Thus $\pi_v(w_a)$ maps the standard line into the opposite line. Applying $w_a^{-1}$ proves that the map is an isomorphism, so the opposite line is one dimensional. Direct conjugation gives the asserted exchange of the two $K_0$ characters. Choose standard newvectors with $\langle v,\widetilde v\rangle_v=1$. Invariance of the pairing gives

$$
\left\langle\pi_v(w_a)v,\widetilde\pi_v(w_a)\widetilde v\right\rangle_v
=\langle v,\widetilde v\rangle_v=1,
$$

so its restriction to the transported opposite lines is perfect. $\square$

Globally, choose an idele representing the conductor ideal and form the product of the local matrices (11.5) at ramified places. The resulting Fricke operator sends a global newform to the corresponding dual or character-conjugate newform. If the representation is identified with that dual by a specified self-duality, the newform line is stable and the operator has an Atkin--Lehner eigenvalue. Without such an identification it is better to call the scalar a comparison constant between two lines, not an eigenvalue on one line.

### 11.4 Normalization audits and counterexamples

Several nearby statements are false, and each failure locates an important hypothesis.

**Using $K_0$ invariance with ramified central character.** A newvector generally transforms under $K_0(\mathfrak p^a)$ by a character; it is not fixed. Literal invariance belongs to $K_1$. Omitting the nebentype can make the predicted newspace vanish.

**Normalizing every Whittaker model at the identity without fixing $\psi$.** Changing $\psi_v$ shifts the conductor shell. The local newvector line persists, but the distinguished nonzero evaluation point moves by diagonal conjugation.

**Recovering Satake data from one trace with no determinant.** The numbers $\{\alpha,\beta\}$ and $\{\gamma,\delta\}$ can have the same sum and different products. The $T_v$ eigenvalue alone determines the local component only after the central character is fixed.

**Inferring automorphic multiplicity one from strong multiplicity one.** Two copies of one representation agree locally everywhere. Their exclusion uses Whittaker uniqueness and Fourier reconstruction, not pole comparison.

**Counting degeneracy maps as independent.** At level $p^r$ the oldspace from an unramified representation has dimension $r+1$, not $2^r$. The two images at successive steps overlap.

**Calling the finite newvector space the whole global newform line.** Before an archimedean type is selected, the contribution is $\pi_\infty\otimes\mathbf Cv_f^\mathrm{new}$ and is usually infinite dimensional.

**Assuming twists can only raise level.** Equal-depth character cancellation can lower conductor. Exact local formulas, not a maximum rule, control twisting.

These counterexamples are part of the theorem's logical boundary. Each prevents a common normalization shortcut from changing the statement being proved.

## 12. The complete global newform package

### 12.1 The main theorem in one statement

We can now assemble the results into the form used by later arithmetic theory.

**Theorem 12.1 (strong multiplicity one and global newforms).** Let $F$ be a number field and let $\omega$ be a unitary character of $F^\times\backslash\mathbf A_F^\times$.

1. The fixed-central-character cuspidal spectrum is multiplicity free:

   $$
   L^2_{\mathrm{cusp},\omega}
   =\widehat\bigoplus_{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)}
   \mathcal H_\pi.
   \tag{12.1}
   $$

2. Every $\pi$ has a unique restricted tensor factorization $\pi=\otimes_v'\pi_v$, with $\pi_v$ spherical at almost every finite place.
3. If two irreducible unitary cuspidal representations have isomorphic local factors at almost every place, or equivalently equal unramified Hecke polynomials there, they are globally isomorphic.
4. The finite conductor ideal

   $$
   \mathfrak c(\pi)=\prod_{v<\infty}\mathfrak p_v^{a(\pi_v)}
   $$

   is finite and is divisible by the conductor of $\omega_f$.
5. For every ideal $\mathfrak n$,

   $$
   \dim\pi_f^{K_1(\mathfrak n)}
   =\begin{cases}
   \displaystyle\prod_v(n_v-a(\pi_v)+1),
   &\mathfrak c(\pi)\mid\mathfrak n,\\
   0,&\text{otherwise}.
   \end{cases}
   \tag{12.2}
   $$

6. At $\mathfrak n=\mathfrak c(\pi)$ the finite fixed space is the line generated by the tensor of normalized local newvectors. At higher levels it has the basis

   $$
   \left\{
   \pi_f\left(
   \prod_{v<\infty}
   \begin{pmatrix}\varpi_v^{-j_v}&0\\0&1\end{pmatrix}
   \right)v_f^\mathrm{new}:
   0\leq j_v\leq n_v-a(\pi_v)
   \right\}.
   \tag{12.3}
   $$

   Only finitely many $j_v$ are nonzero.
7. The closed span of the two degeneracy images from every immediate lower level is the oldspace, and its orthogonal complement is

   $$
   \mathcal H_\mathrm{new}(\mathfrak n)
   =\widehat\bigoplus_{\substack{\pi\in\mathcal A_{\mathrm{cusp}}(G,\omega)\\
   \mathfrak c(\pi)=\mathfrak n}}
   \mathcal H_{\pi,\infty}\widehat\otimes
   \mathbf Cv_f^\mathrm{new}.
   \tag{12.4}
   $$

8. After an archimedean multiplicity-one type is chosen, each almost-everywhere unramified Hecke eigensystem contributes at most one normalized global newform.

**Proof.** The discrete finite-multiplicity spectrum is the spectral conclusion recalled in Chapter 1. The Whittaker argument of Chapter 4 makes it multiplicity free. The restricted tensor factorization and its uniqueness are Theorem 2.2 and Section 2.5. The Rankin--Selberg pole comparison proves part 3 in Theorem 3.1.

The local newvector theorem proves finiteness of every $a(\pi_v)$, and sphericality almost everywhere makes the product conductor finite. Central divisibility is (5.3) place by place. Factorization of invariants and the local dimension formula give (12.2), while the local translate bases tensor to (12.3). Finally, Theorem 8.1 identifies the orthogonal newspace, and Theorem 9.2 gives the eigensystem statement. $\square$

Every assertion in this theorem has a distinct role. Strong multiplicity one identifies the summand; local newvector uniqueness identifies its first finite line; automorphic multiplicity one ensures that line is not repeated; and the oldvector basis describes every later level.

### 12.2 The implication chain

The logical structure can be summarized as follows:

$$
\begin{array}{c}
\text{discrete cuspidal spectrum with finite multiplicity}
\\
\quad +\quad
\text{global Whittaker uniqueness and Fourier expansion}
\end{array}
\Longrightarrow
\text{automorphic multiplicity one},
\tag{12.5}
$$

$$
\begin{array}{c}
\pi_v\simeq\rho_v\text{ outside a finite set}
\\
\Downarrow
\\
L^S(s,\rho\times\widetilde\pi)
=L^S(s,\pi\times\widetilde\pi)
\\
\quad +\quad
\text{self-pole and cross-pole criterion at }s=1
\end{array}
\Longrightarrow
\pi\simeq\rho,
\tag{12.6}
$$

and

$$
\begin{array}{c}
\text{local Kirillov shell interval}
\\
\Downarrow
\\
\dim\pi_v^{K_1(\mathfrak p_v^n)}
=\max(0,n-a_v+1)
\\
\quad +\quad
\text{restricted tensor factorization}
\end{array}
\Longrightarrow
\text{global conductor and old/new decomposition}.
\tag{12.7}
$$

No arrow is reversible without additional information. A multiplicity-free spectrum does not imply strong multiplicity one. A global isomorphism does not select a scalar on the newvector line. Equality of dimensions of level spaces does not identify their Hecke action. The full package works because the analytic, Fourier, and local representation-theoretic inputs meet at exactly the points displayed above.

### 12.3 Conclusion

The cuspidal spectrum of $\mathrm{GL}_2$ is rigid in two complementary directions. Horizontally, across the places of a number field, almost all spherical factors determine every missing local component and the global representation that contains them. The mechanism is the Rankin--Selberg pole at one: a common unramified Euler tail cannot be simultaneously a self-product with a pole and a genuinely different cross product without one.

Vertically, through the tower of congruence levels, each representation has a unique first appearance. The local conductor exponent is the first $K_1$ level with invariants, the invariant line there is normalized by its Whittaker value, and every higher invariant vector is a diagonal translate of that line. Tensoring over the finite places turns the exponents into the conductor ideal and the translates into a divisor-indexed oldform basis.

The global Hilbert space reflects both rigidities exactly. Whittaker expansion removes repeated automorphic copies. The two degeneracy maps from immediate lower levels generate every summand whose conductor is smaller than the stated level. Their orthogonal complement consists precisely of representations whose conductor equals that level, each contributing its finite newvector line and its full archimedean factor. After an archimedean multiplicity-one type and a Whittaker scalar are fixed, this becomes the familiar unique normalized newform.

Strong multiplicity one and newform theory are therefore not separate classification devices. The first says that the unramified Hecke data name one global representation; the second says where that representation first lives and how all of its higher-level copies are generated. Together they provide the canonical decomposition of the cuspidal spectrum by global packets, conductor ideals, normalized newvectors, and oldform towers.
