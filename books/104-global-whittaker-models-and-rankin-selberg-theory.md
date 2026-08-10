# Global Whittaker Models and Rankin–Selberg Theory

## Contents

1. [From cusp forms to Euler products](#1-from-cusp-forms-to-euler-products)
   - [The global problem](#11-the-global-problem)
   - [Standing notation](#12-standing-notation)
   - [Characters and measures](#13-characters-and-measures)
   - [The normalization ledger](#14-the-normalization-ledger)
   - [The main arc](#15-the-main-arc)
2. [Fourier analysis on the global unipotent quotient](#2-fourier-analysis-on-the-global-unipotent-quotient)
   - [Why the unipotent quotient is the right circle](#21-why-the-unipotent-quotient-is-the-right-circle)
   - [Fourier coefficients](#22-fourier-coefficients)
   - [How the torus moves frequencies](#23-how-the-torus-moves-frequencies)
   - [The Fourier–Whittaker expansion](#24-the-fourierwhittaker-expansion)
   - [Convergence and differentiation](#25-convergence-and-differentiation)
3. [Global genericity and uniqueness](#3-global-genericity-and-uniqueness)
   - [Why cuspidality forces a nonzero frequency](#31-why-cuspidality-forces-a-nonzero-frequency)
   - [Global genericity](#32-global-genericity)
   - [Restricted tensor products of local models](#33-restricted-tensor-products-of-local-models)
   - [Global Whittaker uniqueness](#34-global-whittaker-uniqueness)
   - [Cuspidal multiplicity one](#35-cuspidal-multiplicity-one)
4. [Factorization of the global model](#4-factorization-of-the-global-model)
   - [Pure tensors and the normalization problem](#41-pure-tensors-and-the-normalization-problem)
   - [The unramified reference vector](#42-the-unramified-reference-vector)
   - [The factorization theorem](#43-the-factorization-theorem)
   - [Ramified vectors and finite correction factors](#44-ramified-vectors-and-finite-correction-factors)
   - [A factorization counterexample](#45-a-factorization-counterexample)
5. [The standard Whittaker–Mellin integral](#5-the-standard-whittakermellin-integral)
   - [Why the quotient unfolds](#51-why-the-quotient-unfolds)
   - [The global standard integral](#52-the-global-standard-integral)
   - [Euler factorization](#53-euler-factorization)
   - [The unramified degree-two factor](#54-the-unramified-degree-two-factor)
   - [Continuation and the standard functional equation](#55-continuation-and-the-standard-functional-equation)
6. [Eisenstein sections from two-dimensional Schwartz functions](#6-eisenstein-sections-from-two-dimensional-schwartz-functions)
   - [Why a Schwartz variable is needed](#61-why-a-schwartz-variable-is-needed)
   - [The standard section](#62-the-standard-section)
   - [The Eisenstein series](#63-the-eisenstein-series)
   - [The constant term and intertwining operator](#64-the-constant-term-and-intertwining-operator)
   - [Continuation, poles, and residues](#65-continuation-poles-and-residues)
   - [The Eisenstein functional equation](#66-the-eisenstein-functional-equation)
7. [The global Rankin–Selberg integral](#7-the-global-rankinselberg-integral)
   - [The invariant pairing](#71-the-invariant-pairing)
   - [First unfolding](#72-first-unfolding)
   - [Second unfolding](#73-second-unfolding)
   - [The Eulerian integral](#74-the-eulerian-integral)
   - [Exact convergence hypotheses](#75-exact-convergence-hypotheses)
8. [Local Rankin–Selberg zeta integrals](#8-local-rankinselberg-zeta-integrals)
   - [Definition and covariance](#81-definition-and-covariance)
   - [Rationality at a finite place](#82-rationality-at-a-finite-place)
   - [The unramified four-factor calculation](#83-the-unramified-four-factor-calculation)
   - [The local factor and test vectors](#84-the-local-factor-and-test-vectors)
   - [The local functional equation](#85-the-local-functional-equation)
9. [Global Euler products and functional equations](#9-global-euler-products-and-functional-equations)
   - [The completed Rankin–Selberg function](#91-the-completed-rankinselberg-function)
   - [Meromorphic continuation](#92-meromorphic-continuation)
   - [The global functional equation](#93-the-global-functional-equation)
   - [Poles and invariant pairings](#94-poles-and-invariant-pairings)
   - [The self-dual positive case](#95-the-self-dual-positive-case)
10. [Analytic estimates and incomplete products](#10-analytic-estimates-and-incomplete-products)
    - [Absolute convergence](#101-absolute-convergence)
    - [Deleting finitely many factors](#102-deleting-finitely-many-factors)
    - [Logarithmic derivatives](#103-logarithmic-derivatives)
    - [Coefficient bounds from positivity](#104-coefficient-bounds-from-positivity)
    - [A warning about zeros and poles](#105-a-warning-about-zeros-and-poles)
11. [Strong multiplicity one](#11-strong-multiplicity-one)
    - [Why ordinary multiplicity one is not enough](#111-why-ordinary-multiplicity-one-is-not-enough)
    - [The pole comparison](#112-the-pole-comparison)
    - [Strong multiplicity one](#113-strong-multiplicity-one)
    - [Density and finite-exception variants](#114-density-and-finite-exception-variants)
12. [Whittaker analysis in trace formulas](#12-whittaker-analysis-in-trace-formulas)
    - [Whittaker–Parseval identities](#121-whittakerparseval-identities)
    - [Cuspidal convolution kernels](#122-cuspidal-convolution-kernels)
    - [A convergent cuspidal trace identity](#123-a-convergent-cuspidal-trace-identity)
    - [Relative kernels and Rankin–Selberg bounds](#124-relative-kernels-and-rankinselberg-bounds)
    - [What has been achieved](#125-what-has-been-achieved)

## 1. From cusp forms to Euler products

### 1.1 The global problem

A cusp form is defined by the disappearance of one average: its constant term along the upper unipotent subgroup is zero. The arithmetic carried by the form lies in everything that remains. Fourier analysis on the compact quotient $F\backslash\mathbf A_F$ organizes those remaining terms into nonzero frequencies, and diagonal matrices identify all nonzero frequencies with one chosen additive character. The result is the Whittaker model, the coordinate system in which a global cusp form becomes an Euler product.

That last phrase conceals three separate theorems. First, every nonzero cuspidal representation must possess a nonzero Whittaker coefficient. Second, that coefficient is unique up to scalar. Third, on a pure tensor the global coefficient is a product of its local counterparts. None follows merely from the definition of a cusp form. Existence uses completeness of Fourier series on the compact additive quotient; uniqueness uses local multiplicity one together with restricted tensor products; factorization uses the normalized spherical lines at almost every place.

Rankin–Selberg theory then multiplies two such Fourier coordinates and integrates. A naive diagonal integral nearly works, but at an unramified place it gives

$$
\sum_{m\geq0}h_m(\alpha_1,\alpha_2)
h_m(\beta_1,\beta_2)X^m
=
\frac{1-\alpha_1\alpha_2\beta_1\beta_2X^2}
{\prod_{i,j}(1-\alpha_i\beta_jX)}.
$$

The numerator is real information: the diagonal integral alone misses a central-character Euler factor. A two-dimensional Schwartz variable supplies exactly that missing factor. This is why the full integral is not an ornamental enlargement of the simpler one.

The purpose of this book is to prove this local-to-global mechanism with all measures, characters, half-powers, convergence domains, and exceptional poles visible. The final applications are multiplicity one, strong multiplicity one, and the absolute convergence statements that allow cuspidal trace identities to be used without hidden truncations.

### 1.2 Standing notation

Let $F$ be a number field, $\mathbf A=\mathbf A_F$ its adele ring, and $\mathbf A^\times$ its idele group. Put

$$
G=\mathrm{GL}_2,\qquad
Z=\left\{zI_2\right\},\qquad
N=\left\{n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}\right\},
$$

$$
a(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix},\qquad
w=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
e_2=(0,1).
$$

Absolute values are normalized so that $|\varpi_v|_v=q_v^{-1}$ at a finite place, are usual at a real place, and are the square of the usual modulus at a complex place. Hence

$$
\prod_v|r|_v=1\qquad(r\in F^\times).
$$

All automorphic representations in this book are irreducible cuspidal constituents of a fixed unitary-central-character cuspidal space. Their smooth vectors are finite under the archimedean maximal compact subgroup and fixed by a compact open subgroup at the finite places unless explicitly stated otherwise. The reduction and spectral results established earlier imply that these vectors are rapidly decreasing on the central quotient.

If $\pi$ has central character $\omega_\pi$, its contragredient is denoted $\widetilde\pi$. For a local or global Whittaker function, a tilde denotes the transpose-inverse transform appropriate to the contragredient; the exact matrix is displayed when it is used.

### 1.3 Characters and measures

Fix the standard global additive character

$$
\psi:F\backslash\mathbf A\longrightarrow\mathbf C^\times
$$

obtained from the trace to $\mathbf Q$. At each place use the additive measure self-dual for $\psi_v$. Their product $dx$ is self-dual and gives

$$
\operatorname{vol}(F\backslash\mathbf A)=1.
$$

Thus $dx$ itself is the probability measure on the unipotent quotient. This differs from the finite-place convention $\operatorname{vol}(\mathcal O_v)=1$ at the finitely many places dividing the different. The self-dual convention is the one used throughout this book because it makes global Fourier inversion and Poisson summation carry no discriminant scalar.

At a finite place define $d^\times y$ by

$$
\operatorname{vol}(\mathcal O_v^\times)=1.
$$

At infinity use $dy/|y|$ over $\mathbf R$ and the corresponding radial multiplicative measure over $\mathbf C$. Quotient measures are always determined by integration in stages. Maximal compact subgroups have probability measure.

These choices make the Iwasawa formula

$$
dg=\left|\frac ad\right|^{-1}dx\,d^\times a\,d^\times d\,dk
$$

for $g=n(x)\operatorname{diag}(a,d)k$. The quotient measure on $N(F_v)\backslash G(F_v)$ is the last three factors with the same modular density.

### 1.4 The normalization ledger

The Fourier transform has positive phase:

$$
\widehat\Phi(y)=\int\Phi(x)\psi(xy)\,dx,\qquad
\widehat{\widehat\Phi}(x)=\Phi(-x).
$$

The global Whittaker coefficient of an automorphic form $\phi$ is

$$
W_\phi(g)=\int_{F\backslash\mathbf A}
\phi(n(x)g)\psi(-x)\,dx.
\tag{1.1}
$$

Consequently

$$
W_\phi(n(u)g)=\psi(u)W_\phi(g).
\tag{1.2}
$$

For the second member of a Rankin–Selberg pair we use the opposite coefficient

$$
W^-_{\phi'}(g)=\int_{F\backslash\mathbf A}
\phi'(n(x)g)\psi(x)\,dx,
\tag{1.3}
$$

which transforms by $\psi^{-1}$. This opposite sign is what makes equal, rather than opposite, rational frequencies survive when two Fourier expansions are multiplied.

The degree-two local zeta integral uses

$$
\int_{F_v^\times}W(a(y))\chi(y)|y|^{s-1/2}\,d^\times y.
\tag{1.4}
$$

The degree-four local integral uses

$$
\int_{N(F_v)\backslash G(F_v)}
W_1(g)W_2(g)\Phi(e_2g)|\det g|^s\,dg.
\tag{1.5}
$$

The exponents in (1.4) and (1.5) are compatible: after Iwasawa decomposition, (1.5) contains the diagonal weight $|y|^{s-1}$, and each normalized spherical Whittaker value contributes $|y|^{1/2}$.

### 1.5 The main arc

Chapters 2–4 construct the global model and prove existence, uniqueness, factorization, and cuspidal multiplicity one. Chapter 5 treats the standard degree-two Mellin integral. Chapters 6–9 build the two-dimensional Eisenstein section, unfold the degree-four integral, calculate its local factors, and derive continuation, poles, and functional equations. Chapters 10 and 11 turn those analytic properties into strong multiplicity one. Chapter 12 records the precise convergence consequences used when cuspidal kernels enter trace formulas.

Two boundaries will be maintained. General estimates uniform in conductor or archimedean spectral parameter belong to the subsequent analytic theory. The present book proves the fixed-data continuation, functional equations, pole criterion, and finite-exception estimates required for multiplicity arguments and cuspidal trace identities. Likewise, the noncuspidal spectral decomposition is not reconstructed here; only the Eisenstein family needed for the integral is developed.

## 2. Fourier analysis on the global unipotent quotient

### 2.1 Why the unipotent quotient is the right circle

For fixed $g\in G(\mathbf A)$, the function

$$
x\longmapsto\phi(n(x)g)
$$

is a function on the compact additive group $F\backslash\mathbf A$. Compactness gives a complete discrete Fourier theory. Its character group is the diagonal copy of $F$: after fixing $\psi$, every character is

$$
x\longmapsto\psi(\xi x),\qquad \xi\in F.
$$

The zero character is the constant term. Every $\xi\ne0$ lies in one orbit under conjugation by the diagonal torus. Rank one is special here: there is exactly one nonzero orbit. For higher rank, several unipotent coordinates and several orbit types intervene.

The compact quotient is also the reason no convergence hypothesis is needed to define a Fourier coefficient of a smooth automorphic form at a fixed $g$. Convergence becomes an issue only when the coefficients are summed or integrated over the noncompact diagonal direction.

### 2.2 Fourier coefficients

For $\xi\in F$, define

$$
W_{\phi,\xi}(g)=
\int_{F\backslash\mathbf A}
\phi(n(x)g)\psi(-\xi x)\,dx.
\tag{2.1}
$$

Then $W_{\phi,0}=\phi_N$ is the constant term, and $W_{\phi,1}=W_\phi$. Translation gives

$$
W_{\phi,\xi}(n(u)g)=\psi(\xi u)W_{\phi,\xi}(g).
\tag{2.2}
$$

For a smooth finite-level vector, Fourier inversion on the compact quotient gives

$$
\phi(n(x)g)=\sum_{\xi\in F}W_{\phi,\xi}(g)\psi(\xi x).
\tag{2.3}
$$

At first this identity is in the fiberwise $L^2$ sense. Smoothness at infinity and invariance by a compact open subgroup at finite places improve it to absolute locally uniform convergence, as proved in Section 2.5.

### 2.3 How the torus moves frequencies

The identity

$$
a(\xi)n(x)a(\xi)^{-1}=n(\xi x)
$$

and the product formula imply, for $\xi\in F^\times$,

$$
W_{\phi,\xi}(g)=W_\phi(a(\xi)g).
\tag{2.4}
$$

Indeed, substitute $u=\xi x$ in (2.1). Multiplication by $\xi$ preserves Haar measure on $F\backslash\mathbf A$, and left invariance under $a(\xi)\in G(F)$ moves that matrix across $\phi$. No factor $|\xi|_{\mathbf A}$ remains because it equals one.

This formula is the global analogue of the transitivity of the local torus on nonzero additive characters. It converts infinitely many Fourier coefficients into translates of one Whittaker function.

A useful sign check comes from (1.3). If $W^-_{\phi',\xi}$ is defined with phase $\psi(\xi x)$, then

$$
W^-_{\phi',\xi}(g)=W^-_{\phi'}(a(\xi)g)
$$

and its term in the Fourier expansion carries $\psi(-\xi x)$.

### 2.4 The Fourier–Whittaker expansion

**Theorem 2.1 (Fourier–Whittaker expansion).** Let $\phi$ be a smooth, finite-level, finite-type cuspidal automorphic form on $G(F)\backslash G(\mathbf A)$ with unitary central character. Then

$$
\boxed{
\phi(g)=\sum_{\xi\in F^\times}W_\phi(a(\xi)g).
}
\tag{2.5}
$$

The sum converges absolutely and locally uniformly in $g$, as do the sums obtained after applying any fixed invariant differential operator. On a fixed Siegel region it converges rapidly after the usual cusp weights are inserted.

**Proof strategy.** Fourier-expand on $F\backslash\mathbf A$, remove the zero term by cuspidality, identify nonzero terms by (2.4), and prove rapid convergence by combining finite-level support with integration by parts at infinity.

**Proof.** Equation (2.3) at $x=0$ gives

$$
\phi(g)=W_{\phi,0}(g)+\sum_{\xi\in F^\times}W_{\phi,\xi}(g)
$$

in the fiberwise sense. Cuspidality makes $W_{\phi,0}=0$, while (2.4) gives the asserted terms.

Fix a compact set of $g$ and a compact open subgroup fixing $\phi$ at the finite places. The finite component of (2.1) then forces $\xi$ into one fixed fractional ideal. At infinity, apply an invariant unipotent differential operator $D$ of order $r$. On the character $\psi(\xi x)$ it acts by a polynomial $P_D(\xi)$ of degree $r$. Integration by parts on the compact archimedean torus gives

$$
|W_{\phi,\xi}(g)|
\leq C_{D,K}(1+\|\xi\|)^{-r}
\sup_{g'\in K'}|D\phi(g')|.
$$

The enlarged set $K'$ is compact. Taking $r>[F:\mathbf Q]+m$ makes the sum converge absolutely with $m$ spare powers. The same estimate after differentiating in $g$ proves normal convergence of all derived series. In a Siegel region, rapid cuspidal decay bounds the displayed supremum uniformly with any prescribed negative power of height. $\square$

The theorem explains why a cusp form need not be compactly supported: its infinitely many nonzero Fourier modes persist, but each is controlled strongly enough for termwise integration on the domains used below.

For $F=\mathbf Q$ at full finite level, take an archimedean point $z=x+iy$ and a weight-zero cusp form. With the standard character, (2.5) becomes

$$
\phi(x+iy)=\sum_{n\in\mathbf Z\setminus\{0\}}
a(n)\,\mathcal W_n(y)e^{2\pi inx}.
$$

The functions $\mathcal W_n$ are the archimedean diagonal restrictions of one Whittaker function, moved by $a(n)$. A holomorphic form has no negative-frequency terms because its archimedean lowest-weight condition kills them; a general cuspidal eigenfunction has both signs. Cuspidality alone removes only $n=0$. This is an instructive boundary: global genericity does not impose holomorphy or a one-sided expansion.

### 2.5 Convergence and differentiation

Three modes of convergence will be used, and they should not be confused.

For an arbitrary $L^2$ cusp form, (2.5) holds only as a Fourier series in $L^2(F\backslash\mathbf A)$ for almost every remaining coordinate. For a smooth finite-level vector, it is pointwise and locally normally convergent. For a bounded family in a fixed Sobolev space of sufficiently high order, the convergence is uniform on compacta, with a bound depending only on the Sobolev norm.

The last assertion follows from the proof: choose one order $r$ beyond the dimension of the frequency lattice, use Cauchy–Schwarz for the derivatives, and sum $(1+\|\xi\|)^{-r}$. It justifies interchanging the expansion with compact integrations, invariant differentiation, and convolution by a fixed smooth compactly supported function.

Pointwise convergence without uniformity would not justify the Rankin–Selberg unfolding. The rapid estimates in Theorem 2.1 are the decisive analytic input there.

## 3. Global genericity and uniqueness

### 3.1 Why cuspidality forces a nonzero frequency

The constant term of a cusp form vanishes, so a nonzero cusp form must have a nonzero Fourier coefficient. This simple observation becomes a representation-theoretic existence theorem only after one checks that a fixed frequency works on the whole irreducible representation.

Suppose every coefficient at frequency $1$ vanished on an invariant subspace $V$. For $r\in F^\times$, right translation by $a(r)$ and (2.4) would make every frequency-$r$ coefficient vanish on $V$. Cuspidality removes frequency zero. Fourier completeness would then make every vector of $V$ vanish. Thus the standard coefficient cannot be identically zero on a nonzero cuspidal subrepresentation.

One-dimensional automorphic characters show why cuspidality is essential. They are trivial on $N(\mathbf A)$, so all nonzero Fourier coefficients vanish. Their constant term is the function itself.

### 3.2 Global genericity

Let $\pi$ be an irreducible cuspidal automorphic representation and let $V_\pi$ be one realization in the cuspidal spectrum. Evaluation of (1.1) at the identity defines

$$
\lambda_\psi(\phi)=W_\phi(1).
$$

It satisfies

$$
\lambda_\psi(R(n(u))\phi)=\psi(u)\lambda_\psi(\phi).
\tag{3.1}
$$

**Theorem 3.1 (global genericity).** Every irreducible cuspidal automorphic representation of $G(\mathbf A)$ is globally $\psi$-generic: the functional $\lambda_\psi$ is nonzero on its space.

**Proof.** If $\lambda_\psi$ vanished identically, then for every $g$ it would vanish on $R(g)\phi$, so $W_\phi(g)=0$ for every vector and every $g$. Equation (2.5) would give $\phi=0$ for every vector in the realization, a contradiction. $\square$

The associated map

$$
\phi\longmapsto W_\phi,\qquad
W_\phi(g)=\lambda_\psi(R(g)\phi),
\tag{3.2}
$$

is injective because its kernel is an invariant subspace of the irreducible representation. Its image is the global Whittaker model $\mathcal W(\pi,\psi)$.

### 3.3 Restricted tensor products of local models

Write

$$
\pi\simeq\bigotimes_v'\pi_v.
$$

Every $\pi_v$ is infinite-dimensional and generic. At a finite unramified place choose the spherical vector $v_v^\circ$ and the unique local Whittaker functional $\lambda_v$ normalized by

$$
W_v^\circ(1)=\lambda_v(v_v^\circ)=1.
\tag{3.3}
$$

At the remaining places choose any nonzero local functional. For a pure tensor $v=\otimes_vv_v$ with $v_v=v_v^\circ$ almost everywhere, the product

$$
\prod_v\lambda_v(v_v)
$$

is finite in the restricted-product sense: almost every factor equals one. It defines an $N(\mathbf A)$-equivariant functional on the algebraic restricted tensor product.

The point of the spherical normalization is consistency as the finite set of exceptional places grows. Without (3.3), infinitely many arbitrary scalars would be multiplied and there would be no canonical restricted product.

### 3.4 Global Whittaker uniqueness

**Theorem 3.2 (global Whittaker uniqueness).** Let $\pi=\otimes_v'\pi_v$ be an irreducible cuspidal automorphic representation. On its smooth restricted tensor product,

$$
\dim\operatorname{Hom}_{N(\mathbf A)}(\pi,\psi)=1.
\tag{3.4}
$$

Every nonzero global Whittaker functional is a scalar multiple of the restricted product of the normalized local functionals.

**Proof strategy.** Restrict a global functional to vectors varying at finitely many places. Local uniqueness makes that finite tensor-product functional one-dimensional; compatibility among finite sets forces one global scalar.

**Proof.** Fix the spherical reference vector outside a finite set $S$. If $\Lambda$ is a global $\psi$-equivariant functional, then

$$
(v_v)_{v\in S}\longmapsto
\Lambda\left(\bigotimes_{v\in S}v_v\otimes
\bigotimes_{v\notin S}v_v^\circ\right)
$$

is equivariant under $\prod_{v\in S}N(F_v)$ with character $\prod_{v\in S}\psi_v$. Repeated local uniqueness shows that this space of multilinear functionals is at most one-dimensional, generated by $\prod_{v\in S}\lambda_v$.

If $S\subset S'$, the two proportionality constants agree because the added reference vectors have local value one. Hence one scalar works for all finite $S$. Such pure tensors span the smooth restricted tensor product, proving uniqueness. The product functional constructed in Section 3.3 proves existence. $\square$

There is one small point if a functional vanishes on the initial reference tensor. To compare two functionals $\Lambda_1,\Lambda_2$, choose a pure tensor $v^0$ with $\Lambda_1(v^0)\ne0$ and enlarge $S$ until $v^0$ is standard outside $S$. At each place in $S$, normalize the local functional on a translate of the corresponding component of $v^0$ where it is nonzero. Finite-product uniqueness then says

$$
\Lambda_2=c_S\Lambda_1
$$

on the entire tensor space varying in $S$ and fixed outside it. On enlarging $S$, evaluation at $v^0$ forces the same $c_S$. The union of those tensor spaces is the whole restricted tensor product. Thus a functional cannot hide on vectors ramified at a new place, and the argument proves dimension at most one even when the original spherical reference value was zero.

Irreducibility is indispensable. A direct sum of two copies has a two-dimensional space of such functionals. The theorem concerns one abstract irreducible representation; its consequence for automorphic multiplicity is the next result.

### 3.5 Cuspidal multiplicity one

**Theorem 3.3 (cuspidal multiplicity one).** Every irreducible cuspidal automorphic representation of $G(\mathbf A)$ occurs in the cuspidal spectrum with multiplicity one.

**Proof strategy.** Compare two automorphic embeddings of the same abstract representation. Global Whittaker uniqueness makes their coefficients proportional, and the Fourier–Whittaker expansion then makes the embeddings proportional.

**Proof.** Let $i_1,i_2:V_\pi\to L^2_{\mathrm{cusp},\omega}$ be two equivariant embeddings. Pulling the automorphic Whittaker coefficient back along $i_j$ gives a nonzero element $\Lambda_j$ of the one-dimensional space (3.4). Thus $\Lambda_2=c\Lambda_1$ for some $c\ne0$.

For every smooth vector $v$ and every $g$,

$$
W_{i_2(v)}(g)=\Lambda_2(\pi(g)v)
=c\Lambda_1(\pi(g)v)
=cW_{i_1(v)}(g).
$$

Applying (2.5) to both automorphic forms gives $i_2(v)=ci_1(v)$. Density extends this equality to the Hilbert realizations. Hence two independent copies cannot occur. $\square$

This is multiplicity one inside the spectrum. It does not yet say that two representations with the same local components at almost every place are isomorphic. That stronger statement needs the pole comparison developed in Chapters 9–11.

## 4. Factorization of the global model

### 4.1 Pure tensors and the normalization problem

Euler products arise from pure tensors, not from arbitrary vectors. A finite sum of pure tensors gives a finite sum of products, while a general Hilbert vector need not admit a pointwise factorization at all. We therefore work first on the smooth restricted tensor product and then extend analytic identities by density where appropriate.

Fix local Whittaker functionals as in Section 3.3. For $v=\otimes_vv_v$ put

$$
W_v(g_v)=\lambda_v(\pi_v(g_v)v_v).
$$

The product $\prod_vW_v(g_v)$ is well defined for $g=(g_v)\in G(\mathbf A)$ because both $g_v$ and $v_v$ are standard at almost every finite place. It transforms on the left by $\psi$ and on the right by the restricted tensor action.

The automorphic Whittaker function $W_v^{\mathrm{aut}}(g)$ has the same properties. Global uniqueness says the two differ by one scalar independent of $v$ and $g$. Rescaling one exceptional local functional makes that scalar one. This is the only global normalization choice.

### 4.2 The unramified reference vector

At a finite unramified place write the Satake parameters of $\pi_v$ as $\alpha_v,\beta_v$, so

$$
L_v(s,\pi_v)=
\frac1{(1-\alpha_vq_v^{-s})(1-\beta_vq_v^{-s})}.
\tag{4.1}
$$

For the normalized spherical Whittaker function,

$$
W_v^\circ(a(\varpi_v^m))=
\begin{cases}
q_v^{-m/2}
\dfrac{\alpha_v^{m+1}-\beta_v^{m+1}}{\alpha_v-\beta_v},&m\geq0,\ \alpha_v\ne\beta_v,\\
q_v^{-m/2}(m+1)\alpha_v^m,&m\geq0,\ \alpha_v=\beta_v,\\
0,&m<0.
\end{cases}
\tag{4.2}
$$

Equivalently, if

$$
h_m(\alpha,\beta)=\sum_{r=0}^m\alpha^{m-r}\beta^r,
$$

then $W_v^\circ(a(\varpi^m))=q_v^{-m/2}h_m(\alpha_v,\beta_v)$. This notation handles repeated parameters without a limiting argument.

The central character satisfies

$$
\omega_{\pi_v}(\varpi_v)=\alpha_v\beta_v.
\tag{4.3}
$$

All three identities depend on normalized induction. The half-power in (4.2) is later canceled by the Mellin weight.

### 4.3 The factorization theorem

**Theorem 4.1 (factorization).** Normalize the global functional by one choice at an exceptional place. If $v=\otimes_vv_v$ is a pure tensor in an irreducible cuspidal representation, then

$$
\boxed{
W_v(g)=\prod_vW_{v_v}(g_v).
}
\tag{4.4}
$$

At almost every finite place $v_v=v_v^\circ$, $W_{v_v}=W_v^\circ$, and $W_v^\circ(1)=1$.

**Proof.** The restricted product on the right defines a nonzero global $\psi$-equivariant functional. The automorphic coefficient defines another. Theorem 3.2 makes them proportional. Fixing the scalar on one pure tensor makes them equal, and equivariance under the restricted tensor action gives (4.4) for every pure tensor. $\square$

The theorem also shows that changing the global additive character to $\psi_c(x)=\psi(cx)$ translates every local model by $a(c_v)$. If $c\in F^\times$, the global translation is rational and the automorphic realization is unchanged; the product of local scaling constants cancels by the product formula.

### 4.4 Ramified vectors and finite correction factors

At a ramified place there is usually no maximal-compact fixed vector. Factorization does not fail; only the canonical choice of a local vector disappears. A local zeta integral then equals the canonical local factor times a correction function determined by the chosen vector.

For finite places those correction functions are Laurent polynomials in $q_v^{-s}$ after the local factor is divided out. At infinity they are holomorphic functions in the convergence strip and continue with the local zeta integral. Globally only finitely many corrections differ from one for a pure tensor.

This finite-exception principle is crucial. It allows global continuation to be proved using a convenient tensor and then transferred to any other tensor without modifying the Euler tail. It also explains why deleting finitely many Euler factors does not alter a pole at $s=1$ once the deleted factors are known to be finite and nonzero there.

One can make the correction principle concrete. Fix a finite set $S$ containing the archimedean places and every finite place where the representation, vector, character, or Schwartz function is not spherical. In a convergence half-plane, a factorizable zeta integral has the form

$$
\left(\prod_{v\notin S}L_v(s)\right)
\left(\prod_{v\in S}Z_v(s)\right).
$$

At a finite $v\in S$, local rationality writes $Z_v(s)=L_v(s)P_v(q_v^{-s})$ with $P_v$ Laurent polynomial after denominators common to the zeta ideal have been removed. Hence

$$
Z(s)=L^S(s)\prod_{v\in S}L_v(s)P_v(q_v^{-s}).
$$

All dependence on the vector is in the finite product of the $P_v$ and in the finitely many archimedean Mellin transforms. If one correction vanishes at a point, choose a different local vector; the zeta-ideal definition guarantees that the local factor itself has not vanished from the theory. This is why poles and functional equations are stated for the family of integrals before a single test vector is selected.

### 4.5 A factorization counterexample

Let $v=v^{(1)}+v^{(2)}$ be a sum of two pure tensors differing at two places. Then

$$
W_v(g)=\prod_wW_{v_w^{(1)}}(g_w)
+\prod_wW_{v_w^{(2)}}(g_w),
$$

which is generally not one product of local functions. Consequently an integral formed from $v$ is a sum of Euler products, not a single Euler product. The representation has an Euler product; an arbitrary vector need not.

This distinction prevents a common error in unfolding arguments: factorization of the domain and measure does not by itself factor the integrand. Purity of every datum is also required.

## 5. The standard Whittaker–Mellin integral

### 5.1 Why the quotient unfolds

The diagonal restriction $y\mapsto\phi(a(y)g)$ is invariant under $F^\times$ on the left, because $a(r)\in G(F)$ for $r\in F^\times$. Its Fourier–Whittaker expansion is a sum over that same multiplicative lattice. Integrating on the idele class group and then summing over $F^\times$ therefore unfolds to the full idele group.

This is the multiplicative counterpart of unfolding a periodized function on an additive quotient. Absolute convergence is needed to exchange the sum and integral. Rapid cuspidal decay supplies it in every vertical strip after the integral is split at idele module one.

### 5.2 The global standard integral

Let $\chi:F^\times\backslash\mathbf A^\times\to\mathbf C^\times$ be unitary. For a cusp form $\phi$ define

$$
I(s,\phi,\chi)
=\int_{F^\times\backslash\mathbf A^\times}
\phi(a(y))\chi(y)|y|^{s-1/2}\,d^\times y.
\tag{5.1}
$$

Because the norm-one idele class group is compact and $\phi$ is rapidly decreasing in both diagonal directions after a Weyl translation, this integral is entire in $s$. More explicitly, split at $|y|=1$. The part $|y|\geq1$ is dominated by arbitrary negative powers of $|y|$. On $|y|\leq1$, substitute $y\mapsto y^{-1}$ and use the rational Weyl element together with the unitary central character to reduce to another rapidly decreasing integral over $|y|\geq1$. Differentiation in $s$ only inserts powers of $\log|y|$, still dominated by rapid decay.

Insert (2.5). In an initial right half-plane, absolute convergence gives

$$
\begin{aligned}
I(s,\phi,\chi)
&=\int_{F^\times\backslash\mathbf A^\times}
\sum_{r\in F^\times}W_\phi(a(ry))
\chi(y)|y|^{s-1/2}\,d^\times y\\
&=\int_{\mathbf A^\times}
W_\phi(a(y))\chi(y)|y|^{s-1/2}\,d^\times y.
\end{aligned}
\tag{5.2}
$$

The second equality uses the product formula and triviality of $\chi$ on $F^\times$.

### 5.3 Euler factorization

Assume $\phi$ corresponds to a pure tensor and use (4.4). Then in the half-plane of absolute convergence,

$$
I(s,\phi,\chi)=\prod_vZ_v(s,W_v,\chi_v),
\tag{5.3}
$$

where

$$
Z_v(s,W_v,\chi_v)
=\int_{F_v^\times}W_v(a(y))\chi_v(y)|y|_v^{s-1/2}\,d^\times y.
\tag{5.4}
$$

The factorization is justified by first isolating a finite set $S$ containing all exceptional data, integrating on the finite product over $S$, and summing the nonnegative majorant of the unramified valuation tail outside $S$. It is not an unqualified infinite application of Fubini's theorem.

At every finite place the local integrals are the degree-two integrals already characterized by their local fractional ideal. At archimedean places (5.4) is an ordinary Mellin transform of a rapidly decreasing Whittaker function.

### 5.4 The unramified degree-two factor

Suppose $v$ is finite and all data are unramified. Since every multiplicative shell has volume one, (4.2) gives

$$
\begin{aligned}
Z_v(s,W_v^\circ,\chi_v)
&=\sum_{m\geq0}
q_v^{-m/2}h_m(\alpha_v,\beta_v)
\chi_v(\varpi_v)^m q_v^{-m(s-1/2)}\\
&=\frac1{
(1-\alpha_v\chi_v(\varpi_v)q_v^{-s})
(1-\beta_v\chi_v(\varpi_v)q_v^{-s})}.
\end{aligned}
\tag{5.5}
$$

Thus

$$
Z_v(s,W_v^\circ,\chi_v)=L_v(s,\pi_v\otimes\chi_v).
\tag{5.6}
$$

If $\chi_v$ is ramified, the spherical integral can vanish by unit orthogonality. A Kirillov function carrying $\chi_v^{-1}$ on a suitable unit coset gives a nonzero test vector. The local factor belongs to the representation and twist, not to one preferred vector.

### 5.5 Continuation and the standard functional equation

Let

$$
\widetilde W_v(g)=W_v\left(
\begin{pmatrix}0&1\\1&0\end{pmatrix}{}^tg^{-1}\right).
$$

Local uniqueness gives

$$
Z_v(1-s,\widetilde W_v,\chi_v^{-1})
=\gamma_v(s,\pi_v\otimes\chi_v,\psi_v)
Z_v(s,W_v,\chi_v).
\tag{5.7}
$$

At finite principal-series and special places the gamma factor is the product or limiting product of the one-dimensional gamma factors with the normalizations of Chapter 1. At the remaining places (5.7) defines it uniquely.

Globally, the change $y\mapsto y^{-1}$ in (5.1), the rational Weyl element, and the central transformation law identify the transformed integral with the corresponding integral for $\widetilde\pi\otimes\chi^{-1}$ at $1-s$. Comparing with (5.3) gives

$$
\prod_v\gamma_v(s,\pi_v\otimes\chi_v,\psi_v)=1
\tag{5.8}
$$

as a meromorphic identity. Therefore the completed standard product attached to the local zeta integrals is entire for cuspidal $\pi$ and satisfies

$$
\Lambda(s,\pi\otimes\chi)
=\epsilon(s,\pi\otimes\chi)
\Lambda(1-s,\widetilde\pi\otimes\chi^{-1}).
\tag{5.9}
$$

Here $\epsilon$ is the product of the local monomial factors after the Euler denominators have been separated. Formula (5.8), rather than an isolated local convention, is the decisive global consistency check.

The matrix calculation behind the global transformation is worth recording. Since

$$
w^{-1}a(y)w=\operatorname{diag}(1,y)=yI_2a(y^{-1}),
$$

left invariance by the rational matrix $w$ gives

$$
\phi(a(y^{-1}))
=\omega_\pi(y)^{-1}(R(w)\phi)(a(y)).
\tag{5.10}
$$

Thus inversion changes the twist from $\chi$ to $\omega_\pi^{-1}\chi^{-1}$. For rank two,

$$
\widetilde\pi\simeq\pi\otimes\omega_\pi^{-1},
$$

so this is exactly the dual twist in (5.9). Formula (5.10) also proves entire continuation directly: after splitting the idele module at one, both halves become Mellin transforms of rapidly decreasing functions on $[1,\infty)$.

Over $\mathbf Q$, a normalized cuspidal eigenform with unramified parameters $\alpha_p,\beta_p$ therefore gives

$$
L(s)=\prod_p(1-\alpha_pp^{-s})^{-1}(1-\beta_pp^{-s})^{-1}.
$$

At a ramified prime the chosen vector contributes its local factor times a finite correction; at infinity the Whittaker Mellin transform contributes the gamma factor. The functional equation is not a separate symmetry guessed from this product: it is the diagonal inversion (5.10) expressed through local Mellin transforms.

## 6. Eisenstein sections from two-dimensional Schwartz functions

### 6.1 Why a Schwartz variable is needed

The product of two diagonal Whittaker functions sees the four pairwise Satake products, but its generating series has a numerator. Integrating a two-dimensional Schwartz function over the scalar center contributes the reciprocal of that numerator. The full Rankin–Selberg integral is designed so that these two elementary pieces multiply to the degree-four local factor.

The same Schwartz function makes the global Eisenstein family amenable to Poisson summation. It controls the center, supplies continuation, and makes the functional equation a Fourier-transform identity.

### 6.2 The standard section

Let $\eta:F^\times\backslash\mathbf A^\times\to\mathbf C^\times$ be unitary and let $\Phi\in\mathcal S(\mathbf A^2)$. Define

$$
f_{\Phi,\eta,s}(g)
=|\det g|^s
\int_{\mathbf A^\times}
\Phi(e_2tg)\eta(t)|t|^{2s}\,d^\times t,
\tag{6.1}
$$

initially for $\operatorname{Re}(s)$ sufficiently large. Here $e_2t=(0,t)$. If

$$
b=\begin{pmatrix}a&*\\0&d\end{pmatrix},
$$

then substitution $u=td$ gives

$$
f_{\Phi,\eta,s}(bg)
=\eta(d)^{-1}|a/d|^s f_{\Phi,\eta,s}(g),
\tag{6.2}
$$

and scalar multiplication gives

$$
f_{\Phi,\eta,s}(zg)=\eta(z)^{-1}f_{\Phi,\eta,s}(g).
\tag{6.3}
$$

These two identities fix every exponent in (6.1). In normalized induction language the section has the half-modulus already absorbed into the parameter centered at $s=\tfrac12$.

### 6.3 The Eisenstein series

Define

$$
E(g,\Phi,\eta,s)
=\sum_{\gamma\in B(F)\backslash G(F)}
f_{\Phi,\eta,s}(\gamma g).
\tag{6.4}
$$

For $\operatorname{Re}(s)>1$, reduction theory and the rapid decrease of $\Phi$ give absolute locally uniform convergence. The estimate is rank one: in a Siegel region the summand is bounded by a fixed Schwartz seminorm times $H^{\operatorname{Re}(s)}$ in one chamber, while the rational-line count has the complementary decay. Equivalently, after writing primitive bottom rows, the series is dominated by an ideal sum of exponent $2\operatorname{Re}(s)>2$.

The series is left $G(F)$-invariant and has central character $\eta^{-1}$. It is generally not cuspidal. Its constant term contains the two Weyl cells, and those two cells control its entire continuation.

### 6.4 The constant term and intertwining operator

Integrate (6.4) over $N(F)\backslash N(\mathbf A)$. The double-coset decomposition

$$
B(F)\backslash G(F)/N(F)=\{1,w\}
$$

gives

$$
E_N(g,\Phi,\eta,s)
=f_{\Phi,\eta,s}(g)+M(s)f_{\Phi,\eta,s}(g),
\tag{6.5}
$$

where

$$
M(s)f(g)=\int_{\mathbf A}f(wn(x)g)\,dx
\tag{6.6}
$$

in its convergence region. The nonconstant Fourier terms are entire and rapidly decreasing in the cusp; all possible poles therefore lie in the two terms of (6.5).

To calculate $M(s)$, insert (6.1), use the open Bruhat coordinates, and apply two-dimensional Fourier inversion. The result is a section at $1-s$ formed from the Fourier transform

$$
\widehat\Phi(\xi)=\int_{\mathbf A^2}
\Phi(x)\psi(x_1\xi_1+x_2\xi_2)\,dx.
$$

Locally this calculation is a one-dimensional Tate functional equation after one coordinate is held fixed. Globally the products of local gamma factors cancel.

Here are the decisive coordinates. On the open cell, write a nonzero row vector uniquely as

$$
(u,v)=t(1,x),\qquad t=u,\quad x=v/u,
$$

away from the measure-zero line $u=0$; the other Bruhat chart covers that line. The Jacobian is $|t|$, and the determinant and inducing powers in (6.1) turn it into the multiplicative weight required by the one-dimensional local equation. Fourier transformation exchanges the two row coordinates and sends the character $\eta$ to $\eta^{-1}$. The self-dual measure removes any additional scalar. This coordinate check is what fixes the reflection $s\mapsto1-s$.

### 6.5 Continuation, poles, and residues

**Theorem 6.1 (Eisenstein continuation).** For unitary $\eta$, $E(g,\Phi,\eta,s)$ continues meromorphically to $s\in\mathbf C$. If $\eta$ is nontrivial on the norm-one idele class group, the series is entire. Otherwise there is a unique $\tau\in\mathbf R$ such that

$$
\eta=|\cdot|^{i\tau},
$$

and the only possible poles are simple poles at

$$
s=-\frac{i\tau}{2},\qquad
s=1-\frac{i\tau}{2}.
\tag{6.7}
$$

For $\tau=0$, the residue at $s=1$ is

$$
\operatorname*{Res}_{s=1}E(g,\Phi,1,s)
=c_F\widehat\Phi(0),
\tag{6.8}
$$

where $c_F>0$ is the volume constant determined by the quotient and multiplicative measures. The residue is independent of $g$. At $s=0$ the residue is the corresponding negative multiple of $\Phi(0)$.

**Proof strategy.** Subtract the two constant-term asymptotics, use Poisson summation to reflect the small-module range into the large-module range, and observe that the remaining integrals are entire.

**Proof.** Periodize $\Phi$ over $F^2$ and separate the zero vector. Splitting the scalar module at one produces two rapidly convergent integrals. On the small-module part, Poisson summation replaces $\Phi$ by $\widehat\Phi$ and $s$ by $1-s$. The zero vector and its Fourier counterpart contribute

$$
c_F\left(\frac{\widehat\Phi(0)}{s-1}-\frac{\Phi(0)}s\right)
$$

when $\eta=1$. More generally, if $\eta=|\cdot|^{i\tau}$, replace $s$ throughout by $s+i\tau/2$; this moves the poles to the points in (6.7), and the upper residue is $c_F\widehat\Phi(0)|\det g|^{-i\tau/2}$. If $\eta$ is nontrivial on the norm-one idele class group, integration over that compact group kills both constants. The remaining large-module integrals are entire because Schwartz decay dominates every power and every logarithmic derivative. This proves the continuation and residue assertions. $\square$

The qualifier “possible” depends on the test function: $\widehat\Phi(0)=0$ removes the pole at one. The Eisenstein family as a meromorphic distribution nevertheless has that pole.

To see that no pole is hidden in a nonconstant Fourier term, take its Fourier coefficient along $N(F)\backslash N(\mathbf A)$. The closed Bruhat cell contributes only to frequency zero. On the open cell, a nonzero frequency forces an oscillatory integral of a Schwartz function. Repeated integration by parts at infinity and finite Fourier cancellation at finite places make this coefficient entire in $s$ and rapidly decreasing in height. Hence (6.5) accounts for every singularity, not merely for the easiest ones to compute.

### 6.6 The Eisenstein functional equation

Let

$$
\iota(g)=\begin{pmatrix}0&1\\1&0\end{pmatrix}{}^tg^{-1}
\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

Poisson summation and (6.5) give the meromorphic identity

$$
E(g,\Phi,\eta,s)
=E(\iota(g),\widehat\Phi,\eta^{-1},1-s),
\tag{6.9}
$$

after transporting the section through the displayed transpose-inverse map. Applying the identity twice returns $\Phi(-x)$; the rational matrix $-I_2$ and the central character account for the resulting harmless sign. Thus (6.9) is compatible with Fourier inversion.

At factorizable data, comparison of local intertwining equations yields the product formula for their normalized gamma factors. This is the degree-two Schwartz analogue of (5.8).

## 7. The global Rankin–Selberg integral

### 7.1 The invariant pairing

Let $\pi_1,\pi_2$ be cuspidal representations with unitary central characters $\omega_1,\omega_2$. Put

$$
\eta=\omega_1\omega_2.
$$

For cusp forms $\phi_i\in\pi_i$, define

$$
\mathcal I(s,\phi_1,\phi_2,\Phi)
=\int_{Z(\mathbf A)G(F)\backslash G(\mathbf A)}
\phi_1(g)\phi_2(g)E(g,\Phi,\eta,s)\,dg.
\tag{7.1}
$$

The integrand descends because its three central characters multiply to

$$
\omega_1(z)\omega_2(z)\eta(z)^{-1}=1.
$$

This check explains why $\eta$ in (6.1) is the product, not its inverse.

Rapid decay of both cusp forms makes (7.1) absolutely convergent wherever the Eisenstein series is holomorphic and of moderate growth. In particular it converges in the initial half-plane $\operatorname{Re}(s)>1$.

### 7.2 First unfolding

Insert (6.4) into (7.1). Absolute convergence permits the sum to be interchanged with the integral. The quotient by $B(F)\backslash G(F)$ unfolds to

$$
\mathcal I(s,\phi_1,\phi_2,\Phi)
=\int_{Z(\mathbf A)B(F)\backslash G(\mathbf A)}
\phi_1(g)\phi_2(g)f_{\Phi,\eta,s}(g)\,dg.
\tag{7.2}
$$

Now separate $B(F)=T(F)N(F)$. Integrating first over $N(F)\backslash N(\mathbf A)$ extracts the constant term of the product $\phi_1\phi_2$, not the product of the two constant terms. This distinction is decisive: each cusp form has zero constant term, but their product generally does not.

### 7.3 Second unfolding

Use opposite Fourier signs:

$$
\phi_1(n(x)g)
=\sum_{r\in F^\times}W_{1}(a(r)g)\psi(rx),
$$

$$
\phi_2(n(x)g)
=\sum_{r'\in F^\times}W_{2}^{-}(a(r')g)\psi(-r'x).
$$

Orthogonality on $F\backslash\mathbf A$ leaves exactly $r=r'$:

$$
\int_{F\backslash\mathbf A}
\phi_1(n(x)g)\phi_2(n(x)g)\,dx
=\sum_{r\in F^\times}
W_1(a(r)g)W_2^-(a(r)g).
\tag{7.3}
$$

The interchange is justified by the normal convergence of Theorem 2.1. The remaining quotient by the rational diagonal $a(F^\times)$ unfolds the sum in (7.3). Finally insert the $t$-integral in (6.1); the scalar idele $t$ unfolds the center. The result is the full quotient by $N(\mathbf A)$.

There is a useful bookkeeping test. Replacing $g$ by $zg$ in the eventual integrand multiplies the two Whittaker functions by $\omega_1(z)\omega_2(z)$, replaces $\Phi(e_2g)$ by $\Phi(ze_2g)$, and multiplies $|\det g|^s$ by $|z|^{2s}$. Substitution by $z$ in the scalar integral (6.1) contributes the inverse of exactly these factors. Thus no central variable is counted twice or left unintegrated.

### 7.4 The Eulerian integral

**Theorem 7.1 (Rankin–Selberg unfolding).** In the domain $\operatorname{Re}(s)>1$,

$$
\boxed{
\mathcal I(s,\phi_1,\phi_2,\Phi)
=\int_{N(\mathbf A)\backslash G(\mathbf A)}
W_1(g)W_2^-(g)\Phi(e_2g)|\det g|^s\,dg.
}
\tag{7.4}
$$

If all data are pure tensors, then

$$
\mathcal I(s,\phi_1,\phi_2,\Phi)
=\prod_v\Psi_v(s,W_{1,v},W_{2,v}^-,\Phi_v),
\tag{7.5}
$$

where the local integral is defined in (8.1) below.

**Proof.** The preceding two unfoldings reduce (7.2) to an integral over the adelic torus and compact subgroup with a sum over $F^\times$. The substitutions $g\mapsto a(r)g$ and then $g\mapsto tg$ absorb the rational and adelic scalar variables. The product formula removes their determinant weights, while (6.3) cancels the central characters. The Iwasawa quotient formula gives exactly the measure on $N(\mathbf A)\backslash G(\mathbf A)$ and yields (7.4). Factorization follows from Theorem 4.1, purity of $\Phi$, and absolute convergence. $\square$

### 7.5 Exact convergence hypotheses

The first unfolding needs absolute convergence of the Eisenstein series and the quotient integral; $\operatorname{Re}(s)>1$ suffices for unitary cuspidal data. The second needs normal convergence of both Fourier expansions on the compact unipotent fiber. The final Euler factorization needs a pure tensor and absolute convergence of the unramified Euler tail.

After continuation, (7.4) is an identity of meromorphic functions, not necessarily of absolutely convergent integrals. One must not reinsert a continued value under the original integral sign without a convergence argument. All later identities are obtained first in the common convergence region and then extended meromorphically.

## 8. Local Rankin–Selberg zeta integrals

### 8.1 Definition and covariance

Let $K$ now be a local field, let $\pi_1,\pi_2$ be irreducible admissible generic representations of $G(K)$, and choose

$$
W_1\in\mathcal W(\pi_1,\psi),\qquad
W_2\in\mathcal W(\pi_2,\psi^{-1}),\qquad
\Phi\in\mathcal S(K^2).
$$

Define

$$
\Psi(s,W_1,W_2,\Phi)
=\int_{N(K)\backslash G(K)}
W_1(g)W_2(g)\Phi(e_2g)|\det g|^s\,dg.
\tag{8.1}
$$

The product $W_1W_2$ is left $N(K)$-invariant because the two Whittaker characters cancel. The quotient measure is the one induced from the fixed Haar measures. The Schwartz factor controls the scalar center; without it, the center would contribute an unrestricted Mellin integral.

Right translation of all three data leaves (8.1) covariant in the expected way. Scaling $\Phi$ or either Whittaker function scales the integral. These elementary facts ensure that the set of all integrals is an ideal after the spectral variable is converted to $X=q^{-s}$ at a finite place.

### 8.2 Rationality at a finite place

Assume $K$ is nonarchimedean. Iwasawa decomposition gives

$$
\begin{aligned}
\Psi(s,W_1,W_2,\Phi)
=\int_{K^\times}\int_{K^\times}\int_{K_0}
&W_1(\operatorname{diag}(yd,d)k)
W_2(\operatorname{diag}(yd,d)k)\\
&\Phi((0,d)k)|y|^{s-1}|d|^{2s}
\,dk\,d^\times y\,d^\times d,
\end{aligned}
\tag{8.2}
$$

where $K_0=\mathrm{GL}_2(\mathcal O_K)$. The power $|y|^{s-1}$ is the product of $|\det g|^s$ and the quotient modular density $|y|^{-1}$.

Choose a compact open subgroup fixing all data. The $k$-integral becomes a finite sum. The $d$-integral is a finite sum of one-dimensional local zeta integrals. The $y$-integral is a shell sum of products of Kirillov functions; their eventual character-exponential expansions make it rational in $q^{-s}$. Hence

$$
\Psi(s,W_1,W_2,\Phi)\in\mathbf C(q^{-s}).
\tag{8.3}
$$

As the data vary, these rational functions form a fractional ideal of $\mathbf C[q^s,q^{-s}]$. Stability under multiplication by $q^{\pm s}$ comes from diagonal translation. Since this Laurent polynomial ring is principal, there is a unique generator with constant term one:

$$
L(s,\pi_1\times\pi_2).
\tag{8.4}
$$

This intrinsic definition covers principal, special, and cuspidal local representations uniformly. It also proves that every local integral is the local factor times a Laurent polynomial.

The finite-generation assertion implicit here can be seen directly. Fix common levels for the two Whittaker functions and $\Phi$. Outside a finite range of valuation shells, each Kirillov function is a finite sum of terms

$$
c\,v(y)^r\mu(y)|y|^{1/2},
$$

with $r$ bounded and $\mu$ a Jacquet exponent. Mellin transformation turns $v(y)^r$ into a derivative of a geometric series, hence into a denominator $(1-cq^{-s})^{r+1}$. There are only finitely many exponents and finitely many compact $k$-orbits. One common product of these denominators therefore clears every integral at that level. Translating compactly supported Kirillov functions supplies Laurent monomials, so the generated module is nonzero and fractional. Taking the union over levels does not introduce new asymptotic exponents for fixed $\pi_1,\pi_2$; the same finite denominator works. This proves the ideal statement rather than merely rationality one vector at a time.

### 8.3 The unramified four-factor calculation

Suppose $\pi_i$ are unramified with Satake parameters

$$
(\alpha_1,\alpha_2),\qquad(\beta_1,\beta_2),
$$

choose normalized spherical Whittaker functions, and take $\Phi^\circ=\mathbf1_{\mathcal O_K^2}$. Put

$$
\eta(\varpi)=\omega_{\pi_1}(\varpi)\omega_{\pi_2}(\varpi)
=\alpha_1\alpha_2\beta_1\beta_2.
$$

In (8.2), compact invariance removes $k$. The central integral is

$$
\int_{K^\times}\mathbf1_{\mathcal O_K}(d)
\eta(d)|d|^{2s}\,d^\times d
=\frac1{1-\eta(\varpi)q^{-2s}}.
\tag{8.5}
$$

The root integral is

$$
\sum_{m\geq0}
h_m(\alpha_1,\alpha_2)h_m(\beta_1,\beta_2)q^{-ms}.
\tag{8.6}
$$

The elementary generating-series identity

$$
\sum_{m\geq0}h_m(a,b)h_m(c,d)X^m
=\frac{1-abcdX^2}
{(1-acX)(1-adX)(1-bcX)(1-bdX)}
\tag{8.7}
$$

follows by expanding both $h_m$ as finite geometric sums and summing first along the difference of their indices. Multiplying (8.6) by (8.5) cancels the numerator. Therefore

$$
\boxed{
\Psi(s,W_1^\circ,W_2^\circ,\Phi^\circ)
=\prod_{i,j=1}^2(1-\alpha_i\beta_jq^{-s})^{-1}.
}
\tag{8.8}
$$

This proves

$$
L(s,\pi_1\times\pi_2)
=\prod_{i,j=1}^2(1-\alpha_i\beta_jq^{-s})^{-1}
\tag{8.9}
$$

for unramified representations. It also proves why the Schwartz scalar integral is necessary: deleting it leaves the numerator in (8.7).

For completeness, multiply the right side of (8.7) by its four denominator factors. The coefficient of $X^m$ for $m\geq2$ is the second-order difference, in each pair of variables, of $h_m(a,b)h_m(c,d)$. Since

$$
h_m(a,b)=(a+b)h_{m-1}(a,b)-ab,h_{m-2}(a,b),
$$

all coefficients of degree at least three vanish. The constant coefficient is $1$, the coefficient of $X$ vanishes, and the coefficient of $X^2$ is $-abcd$. This proves (8.7), including repeated parameters, without dividing by $a-b$ or $c-d$.

As a diagnostic example, set $a=b=c=d=1$. Then $h_m(1,1)=m+1$ and

$$
\sum_{m\geq0}(m+1)^2X^m=\frac{1+X}{(1-X)^3}
=\frac{1-X^2}{(1-X)^4}.
$$

The central integral contributes $(1-X^2)^{-1}$ and leaves $(1-X)^{-4}$, the expected four equal roots. A diagonal calculation that returned $(1-X)^{-4}$ before the central integration would have counted one factor twice.

### 8.4 The local factor and test vectors

The generator (8.4) need not be attained by a spherical vector when one datum is ramified. Nevertheless it is attained by suitable data. To see this, use the compactly supported core in each Kirillov model. Choose $W_i(a(y))$ on one small multiplicative coset so that their unit characters cancel, and choose $\Phi$ supported on a compatible compact-open subset of $K^2$. The resulting integral is a nonzero Laurent monomial. Combining such compact integrals with vectors realizing each asymptotic denominator shows that the greatest common divisor of all integrals is exactly (8.4).

For principal series the factor is the product of the four one-dimensional factors attached to the inducing characters. At reducibility, cancellation removes the factors belonging to the nongeneric character constituent and leaves the factor of the special constituent. For local cuspidal representations, compact Kirillov support does not force the degree-four factor to be one: the tensor product of two cuspidal parameters can contain unramified invariants, especially when the second representation is an unramified twist of the contragredient. The three-variable integral detects this interaction even though each separate degree-two standard factor may be one.

### 8.5 The local functional equation

Define the contragredient Whittaker transforms using transpose-inverse, and give $K^2$ the self-dual Fourier transform. Local uniqueness for the relevant trilinear zeta functional gives a unique rational function

$$
\gamma(s,\pi_1\times\pi_2,\psi)
$$

such that

$$
\Psi(1-s,\widetilde W_1,\widetilde W_2,\widehat\Phi)
=\gamma(s,\pi_1\times\pi_2,\psi)
\Psi(s,W_1,W_2,\Phi).
\tag{8.10}
$$

**Proof strategy.** Both sides are rational families with the same covariance under $G(K)$ and scalar dilation. On compact open-cell data, two-dimensional Fourier inversion identifies them up to one scalar. Local Whittaker uniqueness makes the scalar independent of the vectors.

**Proof.** Begin where both integrals converge. Resolve the $k$-variable at one finite level and use Bruhat coordinates. On each compact rectangle, the transformation $g\mapsto{}^tg^{-1}$ turns the $e_2g$ variable into the Fourier-dual row variable and exchanges $s$ with $1-s$. Finite Fourier inversion proves proportionality. If two proportionality scalars existed, their difference would define a second Whittaker functional on one local representation after the other data were fixed, contradicting uniqueness. Rationality extends the equality to all $s$. $\square$

Set

$$
\epsilon(s,\pi_1\times\pi_2,\psi)
=\gamma(s,\pi_1\times\pi_2,\psi)
\frac{L(s,\pi_1\times\pi_2)}
{L(1-s,\widetilde\pi_1\times\widetilde\pi_2)}.
\tag{8.11}
$$

The same shell argument shows that $\epsilon$ is a nonzero constant times a monomial in $q^{-s}$. If $\psi_c(x)=\psi(cx)$ and the measure is changed to the self-dual measure for $\psi_c$, then

$$
\gamma(s,\pi_1\times\pi_2,\psi_c)
=\omega_{\pi_1}(c)^2\omega_{\pi_2}(c)^2
|c|^{4s-2}\gamma(s,\pi_1\times\pi_2,\psi).
\tag{8.12}
$$

The exponents are the dimension-four rule: each central character occurs with the dimension of the other factor, and the absolute-value exponent is $4(s-\tfrac12)$.

## 9. Global Euler products and functional equations

### 9.1 The completed Rankin–Selberg function

For finite places define the Euler product

$$
L_f(s,\pi_1\times\pi_2)
=\prod_{v<\infty}L_v(s,\pi_{1,v}\times\pi_{2,v}).
\tag{9.1}
$$

It converges absolutely in a right half-plane. At almost every place its factor is (8.9). At the archimedean places retain the local zeta integrals themselves. For fixed nonzero archimedean data and local correction factors $P_v(s)$ at the exceptional finite places, put

$$
\Lambda(s,\pi_1\times\pi_2;\mathcal D)
=L_f(s,\pi_1\times\pi_2)
\prod_{v\mid\infty}\Psi_v(s,\mathcal D_v)
\prod_{v\in S_f}P_v(s).
\tag{9.2}
$$

The datum $\mathcal D$ records the finitely many choices. The unfolding theorem says that (9.2) is exactly the global integral for a suitable pure tensor. Different choices multiply it by a finite product of holomorphic correction functions. Thus the finite Euler product, pole criterion, and functional equation are intrinsic even though an explicit list of archimedean gamma factors has not been imposed as an extra convention.

### 9.2 Meromorphic continuation

**Theorem 9.1 (Rankin–Selberg continuation).** The global integral $\mathcal I(s,\phi_1,\phi_2,\Phi)$ continues meromorphically to $\mathbf C$. If $\omega_1\omega_2$ is nontrivial on the norm-one idele class group, it is entire. If

$$
\omega_1\omega_2=|\cdot|^{i\tau},
$$

its only possible poles are simple poles at $s=-i\tau/2$ and $s=1-i\tau/2$.

**Proof.** In (7.1), the cusp forms are rapidly decreasing, uniformly on vertical strips after invariant differentiation. Pairing them with the meromorphic Eisenstein family of Theorem 6.1 therefore preserves meromorphic continuation and cannot create new poles. If the Eisenstein family is holomorphic, so is the pairing. If it has a simple pole, the pairing has at most that simple pole. $\square$

It follows from (7.5) that every completed expression (9.2) has the same continuation after its finite correction factors are included. Conversely, choose local data for which none of those corrections vanishes identically; the continuation of the global integral then gives continuation of the canonical finite Euler product after multiplication by the selected archimedean factors.

### 9.3 The global functional equation

Apply (6.9) inside (7.1), use the change of variables $g\mapsto\iota(g)$, and transform both cusp forms to their contragredient realizations. This gives

$$
\mathcal I(s,\phi_1,\phi_2,\Phi)
=\mathcal I(1-s,\widetilde\phi_1,\widetilde\phi_2,\widehat\Phi).
\tag{9.3}
$$

For factorizable data, comparison with (8.10) yields

$$
\prod_v\gamma(s,\pi_{1,v}\times\pi_{2,v},\psi_v)=1.
\tag{9.4}
$$

After the local Euler factors are separated, the completed equation has the form

$$
\boxed{
\Lambda(s,\pi_1\times\pi_2)
=\epsilon(s,\pi_1\times\pi_2)
\Lambda(1-s,\widetilde\pi_1\times\widetilde\pi_2).
}
\tag{9.5}
$$

The global epsilon factor is a root number of modulus one times the conductor monomial $Q^{1/2-s}$. Its exact allocation between $\Lambda$ and $\epsilon$ depends on whether conductor powers are built into the completed function. Equation (9.4) is invariant under that allocation and fixes the normalization used here.

### 9.4 Poles and invariant pairings

Assume first that $\omega_1\omega_2=1$. Taking the residue of (7.1) at $s=1$ and using (6.8) gives

$$
\operatorname*{Res}_{s=1}\mathcal I(s,\phi_1,\phi_2,\Phi)
=c_F\widehat\Phi(0)
\int_{Z(\mathbf A)G(F)\backslash G(\mathbf A)}
\phi_1(g)\phi_2(g)\,dg.
\tag{9.6}
$$

The last integral is a $G(\mathbf A)$-invariant bilinear pairing between $\pi_1$ and $\pi_2$. By irreducibility it is zero unless

$$
\pi_2\simeq\widetilde\pi_1.
\tag{9.7}
$$

If (9.7) holds, choose paired vectors and $\Phi$ with $\widehat\Phi(0)\ne0$; then (9.6) is nonzero. We have proved the precise pole criterion.

The implication from a nonzero invariant pairing to (9.7) is elementary but important. The pairing defines a map

$$
\pi_2\longrightarrow\pi_1^\vee,\qquad
v_2\longmapsto\bigl(v_1\mapsto\langle v_1,v_2\rangle\bigr).
$$

Invariance makes this map equivariant. Its kernel and image are invariant subspaces. If the map is nonzero, irreducibility makes it injective with dense image; admissibility on every finite level and compact type then makes the image closed there, and the smooth representations are isomorphic. Conversely, when $\pi_2\simeq\widetilde\pi_1$, the unitary inner product supplies such a nonzero pairing. Thus the residue criterion contains no unproved orthogonality assertion.

For the general pure-module case, write $\omega_1\omega_2=|\cdot|^{2iu}$. The upper Eisenstein residue is a nonzero constant times $|\det g|^{-iu}$. The residue pairing is therefore

$$
(\phi_1,\phi_2)\longmapsto
\int_{Z(\mathbf A)G(F)\backslash G(\mathbf A)}
\phi_1(g)\phi_2(g)|\det g|^{-iu}\,dg.
\tag{9.8}
$$

It is an invariant pairing between $\pi_1$ and $\pi_2\otimes|\det|^{-iu}$. It is nonzero precisely when

$$
\pi_2\simeq\widetilde\pi_1\otimes|\det|^{iu}.
\tag{9.9}
$$

**Theorem 9.2 (pole theorem).** The completed Rankin–Selberg function for cuspidal $\pi_1,\pi_2$ is entire unless there is a real $u$ such that (9.9) holds. In that exceptional case it has simple poles at

$$
s=-iu,\qquad s=1-iu.
\tag{9.10}
$$

In particular, it has a pole at $s=1$ if and only if $\pi_2\simeq\widetilde\pi_1$.

The theorem concerns the canonical completed function. A particular test integral can miss the pole because its invariant pairing or $\widehat\Phi(0)$ vanishes. Varying the data recovers it.

### 9.5 The self-dual positive case

Let $\pi$ be unitary and take $\pi_2=\widetilde\pi$. Choose $\phi_2=\overline\phi$ in the unitary realization. Then (9.6) becomes

$$
c_F\widehat\Phi(0)\|\phi\|_2^2,
$$

which is positive when $\widehat\Phi(0)>0$. This proves the pole without an appeal to an abstract nonzero pairing.

At unramified finite places the diagonal part of the unfolded integral has coefficients

$$
|h_m(\alpha_1,\alpha_2)|^2\geq0.
$$

Multiplying by the central factor preserves nonnegativity. Hence the self-convolution Euler product has nonnegative Dirichlet coefficients. Positivity prevents cancellation at its first singularity and is the source of several estimates in the next chapter.

## 10. Analytic estimates and incomplete products

### 10.1 Absolute convergence

The global unfolding initially gives absolute convergence for $\operatorname{Re}(s)>1$ when expressed through positive self-convolution majorants. For a cross product, Cauchy–Schwarz on the unramified coefficients gives

$$
|h_m(\alpha_1,\alpha_2)h_m(\beta_1,\beta_2)|
\leq\frac12\left(
|h_m(\alpha_1,\alpha_2)|^2+
|h_m(\beta_1,\beta_2)|^2\right).
\tag{10.1}
$$

After summing over ideals, each majorant is a self Rankin–Selberg series, convergent for $\operatorname{Re}(s)>1$. Thus the Euler product and Dirichlet series for $L_f(s,\pi_1\times\pi_2)$ converge absolutely there after finitely many exceptional factors are removed.

Here is a noncircular proof for the self product. Choose nonnegative local Schwartz data and paired Whittaker vectors so that the unfolded coefficients are nonnegative. For $\sigma>1$, the Eisenstein series and the global integral converge absolutely, hence the resulting Dirichlet series does. The central factor in (8.5) is an absolutely convergent Hecke Euler product at $2\sigma>2$. Multiplying the diagonal positive series by that central product gives the full self Rankin–Selberg series with nonnegative coefficients, so it also converges. For a cross product, apply (10.1) prime-power by prime-power and then Cauchy–Schwarz to the ideal coefficients. This establishes absolute convergence before any logarithmic differentiation is used.

Absolute convergence of the Dirichlet series implies absolute convergence of the Euler product because the logarithm at an unramified place is a sum over positive powers of the four roots. Apply the same self-product majorant to those power sums. Finitely many ramified factors are rational functions and are harmless in a sufficiently far right half-plane; their local functional equations then provide meromorphic continuation elsewhere.

The conclusion is fixed-data absolute convergence. Uniform estimates as the conductor or archimedean parameter varies require additional work and are not inferred from (10.1).

### 10.2 Deleting finitely many factors

For a finite set $S$ containing the archimedean and ramified places, define

$$
L^S(s,\pi_1\times\pi_2)
=\prod_{v\notin S}L_v(s,\pi_{1,v}\times\pi_{2,v}).
\tag{10.2}
$$

Each omitted nonarchimedean local factor is a reciprocal polynomial with constant term one. If the local representations are unitary and generic, their inducing exponents have real parts strictly between $-\tfrac12$ and $\tfrac12$. Consequently every reciprocal root of the degree-four factor has modulus strictly less than $q_v$; the local factor is finite and nonzero at $s=1$.

Therefore deleting finitely many places neither creates nor removes a pole at $s=1$. In particular,

$$
L^S(s,\pi\times\widetilde\pi)
$$

has a simple pole at $s=1$, while $L^S(s,\pi_1\times\pi_2)$ is holomorphic there when $\pi_2\not\simeq\widetilde\pi_1$.

The strict inequalities on the exponents matter. A nonunitary principal series at the boundary can have a local denominator vanishing at $s=1$, so a deleted factor could change the pole order. Unitarity is not a decorative hypothesis in the finite-exception argument.

### 10.3 Logarithmic derivatives

In the absolute-convergence half-plane, differentiating the Euler product gives

$$
-\frac{L^{S\prime}}{L^S}(s,\pi_1\times\pi_2)
=\sum_{v\notin S}\sum_{r\geq1}
\left(\sum_{i,j}(\alpha_{i,v}\beta_{j,v})^r\right)
(\log q_v)q_v^{-rs}.
\tag{10.3}
$$

For $\pi_2=\widetilde\pi_1$, the coefficient in parentheses is

$$
\left|\alpha_{1,v}^r+\alpha_{2,v}^r\right|^2\geq0.
\tag{10.4}
$$

The simple pole at one therefore gives

$$
-\frac{L^{S\prime}}{L^S}(s,\pi\times\widetilde\pi)
=\frac1{s-1}+O(1)
\qquad(s\to1^+).
\tag{10.5}
$$

This logarithmic form measures how much local disagreement can be hidden while retaining a global pole. It is also useful for bounding prime sums that occur in trace comparisons.

### 10.4 Coefficient bounds from positivity

Let

$$
L^S(s,\pi\times\widetilde\pi)=\sum_{\mathfrak a}b(\mathfrak a)(N\mathfrak a)^{-s},
\qquad b(\mathfrak a)\geq0.
$$

For $\sigma>1$ and $X\geq1$,

$$
\sum_{N\mathfrak a\leq X}b(\mathfrak a)
\leq X^\sigma L^S(\sigma,\pi\times\widetilde\pi).
\tag{10.6}
$$

Taking $\sigma=1+1/\log X$ and using the simple pole gives

$$
\sum_{N\mathfrak a\leq X}b(\mathfrak a)
\ll_\pi X\log X.
\tag{10.7}
$$

No cancellation is used. Cauchy–Schwarz then gives corresponding fixed-data bounds for cross coefficients. These estimates suffice to dominate the Whittaker sums and relative kernels used in Chapter 12.

### 10.5 A warning about zeros and poles

Equality of Euler factors outside a finite set gives equality of incomplete products, but it does not give equality of completed products term by term at the exceptional places. The strong multiplicity-one proof uses only the incompatible behavior at $s=1$: one incomplete product has a pole and the other is holomorphic.

It would be circular to claim that a cross product is nonzero at $s=1$ merely from its Euler product, since absolute convergence stops at the boundary. Holomorphy follows from the global Eisenstein integral and the pole criterion, not from a formal substitution into an Euler product.

## 11. Strong multiplicity one

### 11.1 Why ordinary multiplicity one is not enough

Cuspidal multiplicity one says that a fixed irreducible representation has only one automorphic realization. Strong multiplicity one says that almost all local components determine the global representation. The first is a uniqueness statement inside one global isomorphism class; the second identifies the class from incomplete local data.

The bridge is analytic. A representation paired with its contragredient produces a pole at one. Pairing with the contragredient of a genuinely different representation does not. If the two representations agree away from finitely many places, the two incomplete Euler products are identical, and they cannot be simultaneously polar and holomorphic.

### 11.2 The pole comparison

Let $\pi$ and $\pi'$ be irreducible unitary cuspidal representations, and suppose

$$
\pi_v\simeq\pi'_v
\qquad(v\notin S)
\tag{11.1}
$$

for a finite set $S$. Then

$$
L^S(s,\pi\times\widetilde\pi)
=L^S(s,\pi'\times\widetilde\pi).
\tag{11.2}
$$

The left side has a simple pole at $s=1$ by Theorem 9.2 and Section 10.2. If $\pi'\not\simeq\pi$, the right side is holomorphic at $s=1$ by the same theorem. Equality (11.2) is then impossible.

Notice that no separate assumption on central characters is needed. The conclusion will identify the representations and hence their central characters. The local equality outside $S$ is used only to obtain (11.2).

### 11.3 Strong multiplicity one

**Theorem 11.1 (strong multiplicity one for cuspidal $\mathrm{GL}_2$).** Let $\pi$ and $\pi'$ be irreducible unitary cuspidal automorphic representations of $G(\mathbf A_F)$. If $\pi_v\simeq\pi'_v$ for all but finitely many places $v$, then

$$
\pi\simeq\pi'.
$$

**Proof.** Choose $S$ containing every exceptional and archimedean place. Equation (11.2) follows from the unramified factor formula. Its left side has a simple pole at one. If the representations were not isomorphic, its right side would be holomorphic at one. This contradiction proves the theorem. $\square$

An equivalent Hecke formulation is immediate. At an unramified place the local representation is determined by the unordered pair of Satake parameters, equivalently by its Hecke trace and central character. Thus equality of those data outside a finite set determines the cuspidal representation globally.

### 11.4 Density and finite-exception variants

The proof extends whenever the exceptional Euler factors contribute too little to imitate the logarithmic singularity (10.5). One clean version is the following.

**Proposition 11.2.** Suppose the unramified local parameters of $\pi$ and $\pi'$ are tempered, so their Satake parameters have modulus one. Suppose they agree outside a set $S$ of finite places satisfying

$$
\sum_{v\in S}q_v^{-1}<\infty.
\tag{11.3}
$$

Then $\pi\simeq\pi'$.

**Proof.** Under temperedness, the difference between the logarithms of the two Euler products is bounded for $s\to1^+$ by a constant times

$$
\sum_{v\in S}\sum_{r\geq1}q_v^{-rs}
\ll\sum_{v\in S}q_v^{-1},
$$

so it cannot change a $-\log(s-1)$ singularity into a bounded function. The pole comparison therefore remains valid. $\square$

Condition (11.3) is a genuine sparsity condition, not merely density zero. Sharper density thresholds require uniform local bounds and finer control of the logarithmic coefficients. They are not consequences of the fixed-data argument alone.

## 12. Whittaker analysis in trace formulas

### 12.1 Whittaker–Parseval identities

For a smooth cusp form and fixed $g$, Parseval on $F\backslash\mathbf A$ gives

$$
\int_{F\backslash\mathbf A}|\phi(n(x)g)|^2\,dx
=\sum_{r\in F^\times}|W_\phi(a(r)g)|^2.
\tag{12.1}
$$

The zero term is absent by cuspidality. Integrating (12.1) over a truncated set of the remaining coordinates and using monotone convergence gives a global $L^2$ identity. Rapid decay and (10.7) permit the truncation to be removed for smooth finite-type vectors.

More generally, polarization gives

$$
\int_{F\backslash\mathbf A}
\phi_1(n(x)g)\overline{\phi_2(n(x)g)}\,dx
=\sum_{r\in F^\times}
W_{\phi_1}(a(r)g)\overline{W_{\phi_2}(a(r)g)}.
\tag{12.2}
$$

These identities replace a potentially divergent integral over a cusp cross-section by a positive or bilinear sum of Whittaker coefficients. They are the basic estimates behind relative trace constructions.

### 12.2 Cuspidal convolution kernels

Let $f=\otimes_vf_v$ be smooth and compactly supported on $G(\mathbf A)$ modulo the center, with the central transformation compatible with a fixed unitary character. Define

$$
K_f(x,y)=\sum_{\gamma\in Z(F)\backslash G(F)}
f(x^{-1}\gamma y).
\tag{12.3}
$$

Assume that at one finite place $v_0$ the factor $f_{v_0}$ is **strongly cuspidal**, meaning

$$
\int_{N(F_{v_0})}f_{v_0}(gnh)\,dn=0
\qquad\text{for every }g,h\in G(F_{v_0}),
\tag{12.4}
$$

and the same condition holds for the opposite unipotent subgroup. This exact two-sided condition is stronger than requiring the integral only at $g=h=1$.

Unfolding the constant term of (12.3) and grouping rational matrices by their parabolic orbit shows that (12.4) kills every proper-parabolic contribution. Hence $K_f(\cdot,y)$ and $K_f(x,\cdot)$ are cuspidal. Smoothness follows from that of $f$; finite level and finite type follow from compact support and compact averaging. The cuspidal decay theorem then makes the kernel rapidly decreasing in each variable.

### 12.3 A convergent cuspidal trace identity

**Theorem 12.1 (cuspidal trace identity).** Under the hypothesis (12.4), assume in addition that the archimedean factor is bi-$K_\infty$-finite and smoothing of order greater than the polynomial spectral-window exponent of the finitely many compact types it meets. Then $R_{\mathrm{cusp}}(f)$ is trace class and

$$
\operatorname{tr}R_{\mathrm{cusp}}(f)
=\int_{Z(\mathbf A)G(F)\backslash G(\mathbf A)}K_f(x,x)\,dx
=\sum_{[\gamma]}
\operatorname{vol}(Z(\mathbf A)G_\gamma(F)\backslash G_\gamma(\mathbf A))
O_\gamma(f).
\tag{12.5}
$$

The last sum ranges over the central classes and elliptic regular rational conjugacy classes that meet the support, with the central quotient understood, and

$$
O_\gamma(f)=\int_{G_\gamma(\mathbf A)\backslash G(\mathbf A)}
f(x^{-1}\gamma x)\,dx.
$$

**Proof strategy.** Cuspidality gives rapid decay of the kernel, so the diagonal is integrable. Spectral trace class identifies its diagonal integral with the operator trace. Absolute convergence permits the rational sum to be regrouped by conjugacy class.

**Proof.** Bi-$K_\infty$-finiteness leaves only finitely many compact types. On each, the polynomial spectral-window bound and the assumed smoothing order make the sum of singular values converge; the finite-level operator is therefore trace class. On compact truncations the kernel sum is locally finite, and the usual integral-kernel trace identity applies to finite spectral projections. Strong cuspidality and Chapter 10's rapid decay dominate the complement uniformly, so the truncations converge in trace norm and in diagonal $L^1$. This proves the first equality.

For the second, insert (12.3). Reduction theory gives a uniform finite-overlap bound on every truncation, while rapid cuspidal decay supplies an integrable majorant independent of the truncation. Dominated convergence therefore permits interchange of sum and integral. The constant-term calculation implied by (12.4) makes the contributions induced from the split torus and its unipotent degenerations vanish. What remain are central and elliptic regular classes; their centralizers are anisotropic modulo $Z$, so their adelic centralizer quotients have finite volume. For one remaining class, unfolding $G_\gamma(F)\backslash G(F)$ gives its centralizer volume times the orbital integral. The finite-place support bounds denominators and the archimedean support bounds every conjugate, so only finitely many rational characteristic polynomials occur. Summing the resulting absolutely convergent contributions proves (12.5). $\square$

Without (12.4), parabolic constant terms survive and the diagonal integral generally requires truncation; continuous and residual terms then enter. The theorem is a cuspidal trace identity, not a claim that every trace formula is absolutely convergent without regularization.

### 12.4 Relative kernels and Rankin–Selberg bounds

Apply the Whittaker coefficient in both kernel variables:

$$
K_f^{\psi,\psi^{-1}}(x,y)
=\int_{[N]}\int_{[N]}
K_f(n(u)x,n(v)y)\psi(-u)\psi(v)\,du\,dv.
\tag{12.6}
$$

On the spectral side, multiplicity one and factorization give

$$
K_f^{\psi,\psi^{-1}}(x,y)
=\sum_\pi\sum_{e\in\mathcal B_\pi}
W_{\pi(f)e}(x)\overline{W_e(y)},
\tag{12.7}
$$

for an orthonormal basis of smooth vectors, with convergence after the same smoothing hypothesis as in Theorem 12.1. Cauchy–Schwarz, (12.1), and the self Rankin–Selberg estimate (10.7) give an integrable majorant on diagonal torus ranges. Thus Mellin weights may be inserted and the relative spectral sum unfolded term by term.

On the geometric side, (12.6) applies finite Fourier transforms to the two unipotent variables of $f(x^{-1}\gamma y)$. Bruhat decomposition separates the closed and open cells. Strong cuspidality removes the closed-cell constant term; the open cell produces Kloosterman-type orbital integrals. The equality of the two expansions is the analytic core of a Whittaker relative trace formula.

The role of Rankin–Selberg theory is now precise: it supplies positive square-sum bounds for Whittaker coefficients, controls the Mellin tails, and prevents an unjustified exchange of the spectral sum with torus integration.

### 12.5 What has been achieved

The global unipotent quotient turns cuspidality into a nonzero-frequency expansion. Torus conjugation identifies every nonzero frequency with one standard character, proving global genericity. Local uniqueness and normalized spherical reference vectors then turn the global Whittaker functional into a restricted product. The Fourier–Whittaker expansion recovers the automorphic form from that product and forces cuspidal multiplicity one.

The degree-two Mellin integral reads the standard Euler factors directly from spherical Whittaker values. For two representations, the diagonal Whittaker product leaves one central-character numerator. A two-dimensional Schwartz variable contributes its inverse, and the unfolded local integral yields the full four-factor Euler term. Poisson summation gives the Eisenstein functional equation; its constant term gives continuation and residues; the invariant bilinear pairing gives the exact pole criterion.

The pole of $L(s,\pi\times\widetilde\pi)$ at one and the holomorphy of $L(s,\pi'\times\widetilde\pi)$ for $\pi'\not\simeq\pi$ force strong multiplicity one. Positivity of the self-convolution coefficients supplies the bounds needed to control Whittaker sums. Finally, a two-sided cuspidal local test function removes all parabolic kernel terms, making the cuspidal trace identity and its Whittaker-relative version absolutely convergent.

The durable chain is

$$
\text{cuspidality}
\Longrightarrow
\text{global Whittaker expansion}
\Longrightarrow
\text{local factorization}
\Longrightarrow
\text{Euler products and functional equations}
\Longrightarrow
\text{multiplicity and trace consequences}.
$$

Every arrow depends on the normalization ledger: probability measure on $F\backslash\mathbf A$, opposite Fourier signs in the bilinear unfolding, normalized spherical Whittaker functions, the power $|\det g|^s$, and self-dual Fourier measure. With those choices fixed, the global and local theories are not parallel stories but one calculation viewed from opposite ends.
