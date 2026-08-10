# Schwartz–Bruhat Analysis and Tate’s Thesis

## Contents

1. [Why harmonic analysis enters arithmetic](#1-why-harmonic-analysis-enters-arithmetic)
   - [The local–global analytic problem](#11-the-localglobal-analytic-problem)
   - [Standing arithmetic notation](#12-standing-arithmetic-notation)
   - [The normalization ledger](#13-the-normalization-ledger)
   - [What the main theorem will say](#14-what-the-main-theorem-will-say)
2. [Haar measure, additive characters, and duality](#2-haar-measure-additive-characters-and-duality)
   - [Translation-invariant measure](#21-translation-invariant-measure)
   - [Annihilators and conductors](#22-annihilators-and-conductors)
   - [Self-dual local measures](#23-self-dual-local-measures)
   - [The standard global character](#24-the-standard-global-character)
   - [Scaling the character](#25-scaling-the-character)
3. [Local Schwartz–Bruhat spaces](#3-local-schwartzbruhat-spaces)
   - [Rapid decrease at real places](#31-rapid-decrease-at-real-places)
   - [The complex place as a real plane](#32-the-complex-place-as-a-real-plane)
   - [Compact support and local constancy](#33-compact-support-and-local-constancy)
   - [Finite-level models](#34-finite-level-models)
   - [Stability under the basic operations](#35-stability-under-the-basic-operations)
4. [Local Fourier transformation](#4-local-fourier-transformation)
   - [Definition and first identities](#41-definition-and-first-identities)
   - [The transform of a lattice indicator](#42-the-transform-of-a-lattice-indicator)
   - [Inversion at a nonarchimedean place](#43-inversion-at-a-nonarchimedean-place)
   - [Inversion at the archimedean places](#44-inversion-at-the-archimedean-places)
   - [Convolution, Parseval, and Plancherel](#45-convolution-parseval-and-plancherel)
5. [The adelic Schwartz space](#5-the-adelic-schwartz-space)
   - [Why a restricted tensor product is necessary](#51-why-a-restricted-tensor-product-is-necessary)
   - [Definition and elementary tensors](#52-definition-and-elementary-tensors)
   - [Adelic integration and factorization](#53-adelic-integration-and-factorization)
   - [The global transform](#54-the-global-transform)
   - [Approximation by elementary tensors](#55-approximation-by-elementary-tensors)
6. [Poisson summation over a number field](#6-poisson-summation-over-a-number-field)
   - [Periodization on the compact additive quotient](#61-periodization-on-the-compact-additive-quotient)
   - [Fourier coefficients of the periodization](#62-fourier-coefficients-of-the-periodization)
   - [Poisson summation](#63-poisson-summation)
   - [Scaled lattices and fractional ideals](#64-scaled-lattices-and-fractional-ideals)
   - [The rational Gaussian and the theta identity](#65-the-rational-gaussian-and-the-theta-identity)
7. [Multiplicative measure and quasicharacters](#7-multiplicative-measure-and-quasicharacters)
   - [From additive to multiplicative measure](#71-from-additive-to-multiplicative-measure)
   - [Local quasicharacters and conductors](#72-local-quasicharacters-and-conductors)
   - [Archimedean parameters](#73-archimedean-parameters)
   - [Global characters and their local components](#74-global-characters-and-their-local-components)
   - [A warning about Frobenius](#75-a-warning-about-frobenius)
8. [Nonarchimedean local zeta integrals](#8-nonarchimedean-local-zeta-integrals)
   - [Definition and convergence](#81-definition-and-convergence)
   - [Shell decomposition](#82-shell-decomposition)
   - [The unramified calculation](#83-the-unramified-calculation)
   - [Ramified characters](#84-ramified-characters)
   - [Rationality and the local principal ideal](#85-rationality-and-the-local-principal-ideal)
9. [Archimedean local zeta integrals](#9-archimedean-local-zeta-integrals)
   - [The real place](#91-the-real-place)
   - [The complex place](#92-the-complex-place)
   - [Why the absolute value at a complex place is squared](#93-why-the-absolute-value-at-a-complex-place-is-squared)
   - [Holomorphy after division by the local factor](#94-holomorphy-after-division-by-the-local-factor)
10. [The local functional equation](#10-the-local-functional-equation)
    - [The distributional strategy](#101-the-distributional-strategy)
    - [Existence and uniqueness of the gamma factor](#102-existence-and-uniqueness-of-the-gamma-factor)
    - [Epsilon factors and the exact equation](#103-epsilon-factors-and-the-exact-equation)
    - [Finite-place Gauss sums](#104-finite-place-gauss-sums)
    - [Archimedean epsilon factors](#105-archimedean-epsilon-factors)
    - [Change of additive character](#106-change-of-additive-character)
11. [The global zeta integral](#11-the-global-zeta-integral)
    - [Definition on the idele group](#111-definition-on-the-idele-group)
    - [Euler factorization](#112-euler-factorization)
    - [Unfolding along the idele class group](#113-unfolding-along-the-idele-class-group)
    - [Separating the module direction](#114-separating-the-module-direction)
12. [Continuation and the global functional equation](#12-continuation-and-the-global-functional-equation)
    - [The split at module one](#121-the-split-at-module-one)
    - [Poisson summation inside the integral](#122-poisson-summation-inside-the-integral)
    - [Meromorphic continuation and poles](#123-meromorphic-continuation-and-poles)
    - [The global functional equation](#124-the-global-functional-equation)
    - [Why no boundary term is missing](#125-why-no-boundary-term-is-missing)
13. [Completed Hecke functions and exact global factors](#13-completed-hecke-functions-and-exact-global-factors)
    - [The completed product](#131-the-completed-product)
    - [Finite conductor and discriminant](#132-finite-conductor-and-discriminant)
    - [The root number](#133-the-root-number)
    - [The trivial character and the Dedekind zeta function](#134-the-trivial-character-and-the-dedekind-zeta-function)
    - [Nontrivial characters](#135-nontrivial-characters)
14. [The reusable normalization dictionary](#14-the-reusable-normalization-dictionary)
    - [Local data at a finite place](#141-local-data-at-a-finite-place)
    - [Local data at infinity](#142-local-data-at-infinity)
    - [Global compatibility checks](#143-global-compatibility-checks)
    - [Common normalization failures](#144-common-normalization-failures)
    - [Conclusion](#145-conclusion)

## 1. Why harmonic analysis enters arithmetic

### 1.1 The local–global analytic problem

Arithmetic has two kinds of repetition. Additively, a number field $K$ sits as a lattice in its adele ring $\mathbf A_K$. Multiplicatively, $K^\times$ sits inside the idele group $\mathbf A_K^\times$, and the quotient retains a single noncompact size direction. The first fact suggests Fourier series on $\mathbf A_K/K$; the second suggests Mellin transformation along idele classes. Tate's insight is that these two transformations are not separate devices. Poisson summation converts one into the other and thereby forces the analytic continuation and functional equation of Hecke $L$-functions.

The analytic difficulty is to choose a class of test functions that behaves correctly at every place. At a real place, smoothness and rapid decay make integration by parts effective. At a finite place, differentiation is meaningless and decay is replaced by compact support; smoothness becomes local constancy. These conditions look different, but both say that a function and its Fourier transform should remain excellent test functions. Their common adelic home is the Schwartz–Bruhat space.

Three normalizations interact throughout:

- the normalized absolute value, which controls changes of variables;
- the additive character, which identifies a local field with its additive character group;
- the Haar measure, which determines the square of the Fourier transform.

Changing any one of them changes local constants. A functional equation without this ledger is incomplete. We therefore fix every convention before doing any calculation and repeatedly test the choices against inversion, lattice covolumes, and unramified Euler factors.

### 1.2 Standing arithmetic notation

Let $K$ be a number field. Its places are denoted $v$, its completion at $v$ by $K_v$, and its adele and idele groups by $\mathbf A_K$ and $\mathbf A_K^\times$. At a finite place,

$$
\mathcal O_v\subset K_v,
\qquad \mathfrak p_v=(\varpi_v),
\qquad q_v=|\mathcal O_v/\mathfrak p_v|,
$$

and $v_v(\varpi_v)=1$. The normalized absolute value is

$$
|x|_v=q_v^{-v_v(x)}.
$$

At a real place it is the ordinary absolute value; at a complex place it is

$$
|z|_v=|z|_{\mathrm{usual}}^2=z\bar z.
$$

These choices give the product formula

$$
\prod_v|a|_v=1\qquad(a\in K^\times).
$$

The idele module is $|x|_{\mathbf A}=\prod_v|x_v|_v$. Its kernel is $\mathbf A_K^1$, and the norm-one idele class group

$$
C_K^1=K^\times\backslash\mathbf A_K^1
$$

is compact. We use this compactness to reduce all global convergence questions to one real variable.

At a finite place over the rational prime $p$, let $\mathfrak D_v=\mathfrak p_v^{d_v}$ be the local different. Globally, $D_K$ denotes the absolute discriminant and $\mathfrak D_K$ the different of $K/\mathbf Q$. Thus

$$
|D_K|=N_{K/\mathbf Q}(\mathfrak D_K)=\prod_{v<\infty}q_v^{d_v}.
$$

### 1.3 The normalization ledger

On $\mathbf A_{\mathbf Q}$ take the additive character whose real component is

$$
\psi_{\mathbf Q,\infty}(x)=e^{2\pi i x}
$$

and whose $p$-component is $e^{-2\pi i\{x\}_p}$. It is trivial on the diagonal $\mathbf Q$. For $K$, set

$$
\psi_K(x)=\psi_{\mathbf Q}(\operatorname{Tr}_{K/\mathbf Q}^{\mathbf A}x).
$$

Write $\psi_v$ for its local component. At a finite place the annihilator of $\mathcal O_v$ is

$$
\mathcal O_v^\perp=\mathfrak D_v^{-1}=\mathfrak p_v^{-d_v}.
$$

Choose the additive Haar measure $dx_v$ self-dual for the pairing

$$
(x,y)\longmapsto\psi_v(xy).
$$

Then

$$
\operatorname{vol}_{dx_v}(\mathcal O_v)=q_v^{-d_v/2}.
$$

At a real place $dx_v$ is ordinary Lebesgue measure. At a complex place, writing $z=x+iy$, it is

$$
dz_v=2\,dx\,dy.
$$

The Fourier transform will use the positive phase:

$$
\widehat\phi(y)=\int_{K_v}\phi(x)\psi_v(xy)\,dx_v.
$$

Consequently

$$
\widehat{\widehat\phi}(x)=\phi(-x).
$$

For reciprocity, a uniformizer corresponds to arithmetic Frobenius. This convention affects how a multiplicative character is interpreted arithmetically, but the Euler factor below is stated directly in terms of $\chi_v(\varpi_v)$ and is therefore unambiguous.

### 1.4 What the main theorem will say

Let $\omega:K^\times\backslash\mathbf A_K^\times\to\mathbf C^\times$ be unitary and let $\Phi$ be an adelic Schwartz–Bruhat function. Define, initially in a right half-plane,

$$
Z(\Phi,\omega,s)
=\int_{\mathbf A_K^\times}\Phi(x)\omega(x)|x|_{\mathbf A}^s\,d^\times x.
$$

The measure $d^\times x$ will be specified locally in Chapter 7. The central global theorem is

$$
Z(\Phi,\omega,s)
=Z(\widehat\Phi,\omega^{-1},1-s).
$$

Both sides continue meromorphically to $s\in\mathbf C$. If $\omega$ is nontrivial, they are entire. If $\omega=1$, the only possible poles are simple poles at $0$ and $1$, with residues determined exactly by $\Phi(0)$, $\widehat\Phi(0)$, and the volume of $C_K^1$ for the induced quotient measure.

For a factorizable test function, the integral factors into local zeta integrals. Dividing those local integrals by canonical local $L$-factors produces entire local correction terms. Choosing them to equal $1$ place by place yields the completed Hecke function and its functional equation. The proof is therefore simultaneously global and local: global Poisson summation supplies continuation, while local harmonic analysis identifies the exact Euler, gamma, conductor, and root-number factors.

## 2. Haar measure, additive characters, and duality

### 2.1 Translation-invariant measure

Fourier analysis requires a measure compatible with translation. On every locally compact abelian group $G$, a nonzero positive regular measure $dg$ satisfying

$$
\int_G f(x+a)\,dg(x)=\int_G f(x)\,dg(x)
$$

is unique up to a positive scalar. This is Haar measure. Uniqueness is decisive: an automorphism $T$ of $G$ must scale Haar measure by one constant $\Delta(T)>0$.

For the additive group of a local field $F$, multiplication by $a\in F^\times$ scales measure by the normalized absolute value:

$$
d(ax)=|a|_F\,dx.
$$

At a finite place this follows because multiplication by a uniformizer maps $\mathcal O_F$ onto a subgroup of index $q$; at a complex place it is the two-dimensional real Jacobian. The squared complex absolute value is exactly what makes one formula valid at every place.

The uniqueness argument is short and useful. If $dx$ and $dx'$ are two additive Haar measures, choose a nonnegative compactly supported continuous function $h$ with nonzero integral for both. For a compactly supported continuous $f$, apply invariance and Fubini to

$$
\int_F\int_F f(x+y)h(y)\,dx\,dx'.
$$

Integrating first in $x$ produces $(\int f\,dx)(\int h\,dx')$; integrating first in $y$ produces $(\int f\,dx')(\int h\,dx)$. Hence $dx'$ is the fixed scalar $(\int h\,dx')/(\int h\,dx)$ times $dx$. This is why every normalization problem for additive measure reduces to finding one volume.

The same reasoning supplies quotient integration. If $H$ is a closed subgroup of a locally compact abelian group $G$, Haar measures on $G$ and $H$ determine a unique quotient measure on $G/H$ such that

$$
\int_G f(g)\,dg
=\int_{G/H}\int_H f(gh)\,dh\,d\dot g
$$

for compactly supported continuous $f$. Rescaling $dh$ rescales $d\dot g$ inversely. Later, $H$ will be either $K$, $K^\times$, or the norm-one idele classes; residue constants are meaningful only after this quotient convention is fixed.

A common mistake is to normalize $\operatorname{vol}(\mathcal O_F)=1$ and simultaneously call the measure self-dual for the trace character at a ramified place. Both properties hold only when the different is trivial. The discrepancy $q^{-d/2}$ is not cosmetic: it later contributes the discriminant to the completed global function.

### 2.2 Annihilators and conductors

Let $F$ be a local field and $\psi:F\to\mathbf C^\times$ a nontrivial continuous additive character. For an additive subgroup $L\subset F$, define

$$
L^\perp=\{y\in F:\psi(xy)=1\text{ for every }x\in L\}.
$$

If $F$ is nonarchimedean, there is a unique integer $n(\psi)$ such that

$$
\psi\text{ is trivial on }\mathfrak p^{-n(\psi)}
\quad\text{but not on }\mathfrak p^{-n(\psi)-1}.
$$

Then

$$
\mathcal O_F^\perp=\mathfrak p^{-n(\psi)}.
$$

For the standard trace character on $K_v$, $n(\psi_v)=d_v$. Notice the sign: a more ramified trace pairing has a larger annihilator of $\mathcal O_v$.

The pairing $(x,y)\mapsto\psi(xy)$ is nondegenerate. If $y\ne0$, multiplication by $y$ is onto, so some $x$ makes $\psi(xy)\ne1$. Thus $F$ identifies with its additive character group by

$$
y\longmapsto(x\mapsto\psi(xy)).
$$

At the global level, $\mathbf A_K$ identifies with its additive character group, and the annihilator of the diagonal $K$ is again $K$. This equality is the dual statement behind Poisson summation.

### 2.3 Self-dual local measures

Begin with any additive Haar measure $dx$. Fourier transformation twice has the form

$$
\widehat{\widehat\phi}(x)=c\,\phi(-x)
$$

for a constant $c>0$ depending only on $dx$ and $\psi$. Rescaling $dx$ by $c^{-1/2}$ makes the constant one. The resulting measure is the unique self-dual measure.

There is a useful lattice test. Let $L$ be a compact open additive subgroup of a nonarchimedean local field. Direct integration gives

$$
\widehat{\mathbf 1_L}(y)
=\operatorname{vol}(L)\mathbf 1_{L^\perp}(y).
$$

Applying the transform again yields

$$
\widehat{\widehat{\mathbf 1_L}}
=\operatorname{vol}(L)\operatorname{vol}(L^\perp)\mathbf 1_L.
$$

Thus self-duality is equivalent to

$$
\operatorname{vol}(L)\operatorname{vol}(L^\perp)=1.
$$

For $L=\mathcal O_v$ and $L^\perp=\mathfrak p_v^{-d_v}$, scaling gives

$$
\operatorname{vol}(\mathfrak p_v^{-d_v})
=q_v^{d_v}\operatorname{vol}(\mathcal O_v).
$$

The product-one condition forces $\operatorname{vol}(\mathcal O_v)=q_v^{-d_v/2}$.

At a real place the character $e^{2\pi ixy}$ is self-dual for $dx$. At a complex place the trace pairing is

$$
\operatorname{Tr}_{\mathbf C/\mathbf R}(zw)=2\operatorname{Re}(zw).
$$

The determinant of this pairing relative to ordinary area has absolute value $4$, so the square-root rule gives $2\,dx\,dy$.

### 2.4 The standard global character

The product $\psi_K=\prod_v\psi_v$ is well defined on $\mathbf A_K$: at almost every finite place $x_v\in\mathcal O_v$ and $\psi_v$ is trivial there. It is trivial on $K$ because the rational principal parts cancel the real trace phase.

Take the restricted product of the local self-dual measures. The resulting $dx$ on $\mathbf A_K$ is self-dual, and

$$
\operatorname{vol}(\mathbf A_K/K)=1.
$$

One can verify the last assertion without invoking duality abstractly. With ordinary planar measure at complex places and volume one on finite integer rings, the covolume is $2^{-r_2}|D_K|^{1/2}$. Replacing complex area by twice area contributes $2^{r_2}$, while replacing the finite measures contributes

$$
\prod_{v<\infty}q_v^{-d_v/2}=|D_K|^{-1/2}.
$$

The factors cancel. This covolume-one identity is the first global audit of all local choices.

### 2.5 Scaling the character

Every nontrivial additive character of a local field has the form

$$
\psi_b(x)=\psi(bx)
$$

for a unique $b\in F^\times$. If $dx$ is self-dual for $\psi$, then

$$
dx_b=|b|_F^{1/2}\,dx
$$

is self-dual for $\psi_b$. Indeed, one change of variables shows that transforming twice with $dx_b$ returns reflection with coefficient one.

For a finite place,

$$
n(\psi_b)=n(\psi)+v(b).
$$

This relation is a valuable sign check. Multiplying the phase by a uniformizer makes the character less oscillatory, so it becomes trivial on a larger fractional ideal and its exponent increases by one. Indeed, $b\mathfrak p^{-n'}\subseteq\mathfrak p^{-n}$ is equivalent to $n'\le n+v(b)$.

The local epsilon factor will obey

$$
\epsilon(s,\chi,\psi_b)
=\chi(b)|b|_F^{s-1/2}\epsilon(s,\chi,\psi).
$$

Chapter 10 derives this formula directly. It shows why changing additive characters independently at different places can spoil a global functional equation: for a diagonal $b\in K^\times$, the product formula and triviality of a global character on $K^\times$ make the extra factors cancel; for an arbitrary adelic collection, they need not.

## 3. Local Schwartz–Bruhat spaces

### 3.1 Rapid decrease at real places

At an archimedean place, compact support is unnecessarily restrictive: Gaussians should be allowed, and Fourier transformation naturally produces functions extending across all space. The right replacement is rapid decrease of the function together with all derivatives.

For $F=\mathbf R$, define $\mathcal S(\mathbf R)$ to consist of smooth functions $\phi:\mathbf R\to\mathbf C$ such that

$$
p_{m,n}(\phi)
=\sup_{x\in\mathbf R}|x^m\phi^{(n)}(x)|<\infty
$$

for all $m,n\ge0$. The seminorms $p_{m,n}$ describe its natural topology. The definition is stronger than mere integrability. For example,

$$
\phi(x)=\frac1{1+x^2}
$$

is smooth and integrable but not rapidly decreasing, since $x^3\phi(x)$ is unbounded. The extra decay guarantees absolute convergence of lattice sums and permits repeated integration by parts without boundary terms.

The Gaussian $e^{-\pi x^2}$ is the model element. Polynomial times Gaussian functions also lie in $\mathcal S(\mathbf R)$. Smooth compactly supported functions lie there as well, but they are not stable under Fourier transformation as compactly supported functions: a nonzero compactly supported smooth function has a transform extending to an entire function and hence cannot also have compact support. This is why rapid decay, rather than compact support, is the archimedean invariant notion.

### 3.2 The complex place as a real plane

For $F=\mathbf C$, regard $\mathbf C$ as $\mathbf R^2$ with coordinates $z=x+iy$. Define $\mathcal S(\mathbf C)$ by requiring

$$
\sup_{z\in\mathbf C}
|x^a y^b\partial_x^c\partial_y^d\phi(z)|<\infty
$$

for all nonnegative $a,b,c,d$. Equivalently, every polynomial times every real partial derivative is bounded.

The function

$$
\phi_0(z)=e^{-2\pi|z|_{\mathrm{usual}}^2}
$$

is adapted to our trace character and self-dual measure. The coefficient $2\pi$, rather than $\pi$, compensates for the trace factor $2$ and the measure factor $2$. We will verify in Chapter 4 that $\widehat\phi_0=\phi_0$.

Angular behavior matters for ramified archimedean characters. If $m\in\mathbf Z$, then

$$
z^{\max(-m,0)}\bar z^{\max(m,0)}e^{-2\pi|z|^2}
$$

has angular weight $-m$ and gives the basic test vector for the character $(z/|z|)^m$.

### 3.3 Compact support and local constancy

Let $F$ be nonarchimedean. A function $\phi:F\to\mathbf C$ is locally constant if every point has a neighborhood on which $\phi$ is constant. Define

$$
\mathcal S(F)=C_c^\infty(F)
$$

to be the space of locally constant, compactly supported complex-valued functions. The superscript $\infty$ here means smooth in the totally disconnected sense, namely local constancy.

Compactness and local constancy together imply uniform finite control. There exist integers $r,N$ such that

$$
\operatorname{supp}(\phi)\subseteq\mathfrak p^{-r}
$$

and

$$
\phi(x+u)=\phi(x)\qquad(u\in\mathfrak p^N).
$$

To prove uniformity, cover the compact support by finitely many neighborhoods on which $\phi$ is constant and take the deepest common subgroup. Enlarge the compact set slightly so that translations by that subgroup do not cross its boundary.

The hypotheses are independent. The constant function $1$ is locally constant but not compactly supported. The indicator of a compact set with a non-open boundary need not be locally constant. The basic functions are indicators of compact open cosets

$$
\mathbf 1_{a+\mathfrak p^n}.
$$

Every element of $\mathcal S(F)$ is a finite linear combination of such indicators.

Two examples clarify the definition. The function

$$
x\longmapsto\mathbf 1_{\mathcal O}(x)\psi(ax)
$$

is locally constant and compactly supported for every $a\in F$; increasing $|a|$ makes it oscillate on finer residue classes without changing its support. By contrast,

$$
x\longmapsto q^{-v(x)}\mathbf 1_{\mathcal O}(x),\qquad f(0)=0,
$$

is compactly supported and continuous at every nonzero point but is not locally constant at $0$. It approaches zero through infinitely many distinct shell values. Compact support alone therefore does not give a satisfactory finite-level theory.

Local constancy is also more rigid than ordinary continuity. A continuous function on the compact set $\mathcal O$ may vary at every scale; a locally constant one factors through $\mathcal O/\mathfrak p^N$ for one finite $N$. The latter finite quotient is what makes exact finite Fourier inversion possible.

### 3.4 Finite-level models

For integers $r,N$, let $\mathcal S_{r,N}(F)$ consist of functions supported in $\mathfrak p^{-r}$ and invariant under translation by $\mathfrak p^N$. Such a function is exactly a function on the finite quotient

$$
\mathfrak p^{-r}/\mathfrak p^N.
$$

Thus $\mathcal S_{r,N}(F)$ is finite-dimensional and

$$
\mathcal S(F)=\bigcup_{r,N}\mathcal S_{r,N}(F).
$$

This description replaces estimates by finite harmonic analysis. It also predicts how Fourier transformation exchanges support and constancy. If $\phi$ is invariant under $\mathfrak p^N$, its transform is supported in

$$
(\mathfrak p^N)^\perp=\mathfrak p^{-N-n(\psi)}.
$$

If $\phi$ is supported in $\mathfrak p^{-r}$, its transform is invariant under

$$
(\mathfrak p^{-r})^\perp=\mathfrak p^{r-n(\psi)}.
$$

These two statements follow by translating the integral and by multiplying the phase, respectively. They prove at once that the Fourier transform preserves $\mathcal S(F)$.

More precisely, if $n=n(\psi)$, then

$$
\mathcal F:\mathcal S_{r,N}(F)
\longrightarrow
\mathcal S_{N+n,\,-r+n}(F),
$$

where the first target index records support in $\mathfrak p^{-N-n}$ and the second records invariance under $\mathfrak p^{r-n}$. The notation is less important than the reversal: fine constancy becomes broad Fourier support, while broad original support becomes fine Fourier constancy. This is the nonarchimedean uncertainty principle in exact integer form.

### 3.5 Stability under the basic operations

The local Schwartz space is stable under translation, multiplication by a character, dilation, reflection, convolution, and Fourier transformation. The dilation formula is particularly important. For $a\in F^\times$ and $\phi_a(x)=\phi(ax)$,

$$
\widehat{\phi_a}(y)
=|a|_F^{-1}\widehat\phi(a^{-1}y).
$$

This follows from $u=ax$. Translation $T_b\phi(x)=\phi(x+b)$ gives

$$
\widehat{T_b\phi}(y)=\psi(-by)\widehat\phi(y),
$$

because the transform uses the positive phase. Multiplication by $\psi(bx)$ gives translation in the opposite direction:

$$
\widehat{\psi(b\cdot)\phi}(y)=\widehat\phi(y+b).
$$

These signs are easy to reverse. They will be used in the uniqueness argument for local gamma factors, so they are recorded now rather than repaired later.

## 4. Local Fourier transformation

### 4.1 Definition and first identities

Let $F$ be any completion of $K$, let $\psi$ be the chosen additive character, and let $dx$ be self-dual. For $\phi\in\mathcal S(F)$ define

$$
\widehat\phi(y)=\int_F\phi(x)\psi(xy)\,dx.
$$

The integral converges absolutely. At finite places this is immediate from compact support; at infinity it follows from rapid decay. The preceding support–constancy argument and integration by parts show that $\widehat\phi\in\mathcal S(F)$.

Reflection is denoted $\check\phi(x)=\phi(-x)$. Self-duality means

$$
\widehat{\widehat\phi}=\check\phi.
$$

The inverse transform is therefore

$$
\phi(x)=\int_F\widehat\phi(y)\psi(-xy)\,dy.
$$

One should distinguish the inverse transform from the transform itself. They agree only on even functions.

### 4.2 The transform of a lattice indicator

Let $F$ be nonarchimedean, $n=n(\psi)$, and $L=a+\mathfrak p^r$. Then

$$
\widehat{\mathbf 1_L}(y)
=\psi(ay)\operatorname{vol}(\mathfrak p^r)
\mathbf 1_{\mathfrak p^{-r-n}}(y).
$$

Indeed, substitute $x=a+u$. The integral over $\mathfrak p^r$ is its volume when $y$ lies in the annihilator and zero otherwise: if the character is nontrivial, translating by a point with nontrivial phase multiplies the integral by a number other than one, forcing it to vanish.

For the standard character on $K_v$,

$$
\widehat{\mathbf 1_{\mathcal O_v}}
=q_v^{-d_v/2}\mathbf 1_{\mathfrak D_v^{-1}}.
$$

At an unramified rational place $d_v=0$, the integer-ring indicator is fixed. At a ramified place it is not. This single formula contains both the different and the self-dual measure normalization.

### 4.3 Inversion at a nonarchimedean place

The finite-level description gives a decisive proof of inversion. Suppose $\phi$ is supported in $A=\mathfrak p^{-r}$ and invariant under $B=\mathfrak p^N$. Then it descends to $A/B$. Its transform is supported on $B^\perp$ and invariant under $A^\perp$, so it descends to the dual finite group

$$
B^\perp/A^\perp.
$$

The pairing induced by $\psi(xy)$ is perfect between these two finite groups. The measure factors satisfy

$$
\operatorname{vol}(B)\operatorname{vol}(B^\perp)=1.
$$

Finite Fourier inversion therefore gives

$$
\widehat{\widehat\phi}(x)=\phi(-x).
$$

This proof exposes the mechanism: local inversion is ordinary Fourier inversion on a sufficiently large finite quotient, with self-duality supplying exactly the missing scale. No limiting argument is needed.

### 4.4 Inversion at the archimedean places

For $\mathbf R$, the Gaussian calculation is

$$
\int_{\mathbf R}e^{-\pi x^2}e^{2\pi ixy}\,dx=e^{-\pi y^2}.
$$

Translations, modulations, dilations, differentiation, and multiplication by $x$ generate a dense family of polynomial-Gaussian functions. On this family inversion follows directly. For a general Schwartz function, convolve with a narrowing Gaussian and use dominated convergence; the rapid-decay seminorms justify every interchange. This proves inversion on $\mathcal S(\mathbf R)$.

For $\mathbf C$, write $z=x+iy$ and $w=u+iv$. Since

$$
\operatorname{Tr}_{\mathbf C/\mathbf R}(zw)=2(xu-yv),
$$

the transform splits into two real Gaussian integrals. With $dz=2\,dx\,dy$,

$$
\int_{\mathbf C}e^{-2\pi|z|^2}
e^{2\pi i\operatorname{Tr}(zw)}\,dz
=e^{-2\pi|w|^2}.
$$

The same approximation argument proves inversion on $\mathcal S(\mathbf C)$.

### 4.5 Convolution, Parseval, and Plancherel

For suitable functions define

$$
(\phi*\eta)(x)=\int_F\phi(t)\eta(x-t)\,dt.
$$

Fubini's theorem and a change of variables give

$$
\widehat{\phi*\eta}=\widehat\phi\,\widehat\eta.
$$

The product formula is dual:

$$
\widehat{\phi\eta}=\widehat\phi*\widehat\eta.
$$

With the self-dual measure, Parseval's identity reads

$$
\int_F\phi(x)\overline{\eta(x)}\,dx
=\int_F\widehat\phi(y)\overline{\widehat\eta(y)}\,dy.
$$

Take $\eta=\phi$ to obtain preservation of the $L^2$ norm. Density of the local Schwartz space in $L^2(F)$ extends Fourier transformation uniquely to a unitary operator on $L^2(F)$. The extension is conceptually useful, but the zeta integrals below need the stronger pointwise and decay properties of Schwartz–Bruhat functions.

## 5. The adelic Schwartz space

### 5.1 Why a restricted tensor product is necessary

An arbitrary product of local test functions has no reason to define a function on $\mathbf A_K$, and an unrestricted tensor product would allow infinitely many incompatible local modifications. Arithmetic demands a standard vector at almost every finite place. The indicator $\mathbf 1_{\mathcal O_v}$ is the natural choice: it encodes the restricted-product condition defining the adele ring.

This choice is not required to be fixed by the local transform at every place. It is fixed at almost every place because $d_v=0$ away from the different. Finitely many exceptional transforms are harmless in a restricted tensor product.

### 5.2 Definition and elementary tensors

An elementary adelic Schwartz–Bruhat function is a product

$$
\Phi(x)=\prod_v\Phi_v(x_v),
$$

where $\Phi_v\in\mathcal S(K_v)$ for every $v$ and

$$
\Phi_v=\mathbf 1_{\mathcal O_v}
$$

for almost every finite $v$. The product is well defined because an adele is integral almost everywhere. Define

$$
\mathcal S(\mathbf A_K)
=\bigotimes_v'\mathcal S(K_v)
$$

to be the finite linear span of elementary tensors, with respect to these standard vectors.

Equivalently, if $S$ contains all archimedean places and finitely many finite places, a typical element at level $S$ is

$$
\Phi_S(x_S)\prod_{v\notin S}\mathbf 1_{\mathcal O_v}(x_v),
$$

where $\Phi_S$ is a Schwartz function on the finite product $\prod_{v\in S}K_v$. Enlarging $S$ gives compatible inclusions, and the adelic space is their union.

### 5.3 Adelic integration and factorization

Use the restricted product of the self-dual additive measures. If $\Phi=\otimes_v\Phi_v$ is elementary, absolute convergence and the normalization of the tail give

$$
\int_{\mathbf A_K}\Phi(x)\,dx
=\prod_v\int_{K_v}\Phi_v(x_v)\,dx_v.
$$

At almost every place the factor is $1$, because $d_v=0$ and $\operatorname{vol}(\mathcal O_v)=1$. Thus the product is finite in the literal sense outside a finite set.

Fubini's theorem applies after choosing a finite level $S$: the tail is the compact probability space $\prod_{v\notin S}\mathcal O_v$. This reduction avoids any unjustified infinite iteration of integrals.

### 5.4 The global transform

For $\Phi\in\mathcal S(\mathbf A_K)$ define

$$
\widehat\Phi(y)=\int_{\mathbf A_K}\Phi(x)\psi_K(xy)\,dx.
$$

For an elementary tensor,

$$
\widehat\Phi=\bigotimes_v\widehat\Phi_v.
$$

At almost every finite place, $d_v=0$ and

$$
\widehat{\mathbf 1_{\mathcal O_v}}=\mathbf 1_{\mathcal O_v},
$$

so the transformed tensor is again restricted. Hence the global transform is an automorphism of $\mathcal S(\mathbf A_K)$ and

$$
\widehat{\widehat\Phi}(x)=\Phi(-x).
$$

The global factorization is one reason for insisting on the trace character. An unrelated collection of local characters would still define local transforms, but their product might not be trivial on $K$, and the diagonal annihilator needed for Poisson summation would be wrong.

### 5.5 Approximation by elementary tensors

The definition as a finite span is sufficient for every theorem in this book, but it is useful to understand why it is not artificially small. On a finite product of local fields, finite sums of products of local test functions approximate any test function in the natural Schwartz topology. At finite places this is finite-dimensional linear algebra on compact-open partitions. At archimedean places it follows from polynomial-Gaussian expansions or standard tensor-product approximation.

Consequently all integral identities may first be proved for elementary tensors, extended by linearity, and then passed through the relevant seminorm limits. This strategy separates local calculations cleanly without assuming that every global test function is a single pure tensor.

## 6. Poisson summation over a number field

### 6.1 Periodization on the compact additive quotient

For $\Phi\in\mathcal S(\mathbf A_K)$ define its periodization

$$
P\Phi(x)=\sum_{a\in K}\Phi(x+a).
$$

The sum is $K$-periodic. It converges absolutely and uniformly on compact subsets of $\mathbf A_K$. To see the decisive point, choose a finite level for $\Phi$. The finite coordinates restrict $a$ to a fractional ideal, while the archimedean Schwartz bounds make the remaining lattice sum decay faster than any fixed power. Uniformity on a compact set follows because translating the archimedean argument through a bounded set changes the estimates only by a constant.

Thus $P\Phi$ is continuous on the compact group $\mathbf A_K/K$. It is smooth in the archimedean directions and locally constant in the finite directions. Its Fourier series will converge absolutely because repeated archimedean differentiation and finite local constancy force rapid decay of its coefficients.

### 6.2 Fourier coefficients of the periodization

The character group of $\mathbf A_K/K$ is the annihilator of $K$, hence the diagonal $K$. For $b\in K$, the corresponding character is $x\mapsto\psi_K(bx)$. Normalize quotient measure to have total volume one; this agrees with the quotient of the self-dual measure because $\operatorname{vol}(\mathbf A_K/K)=1$.

The $b$th Fourier coefficient is

$$
\begin{aligned}
c_b
&=\int_{\mathbf A_K/K}P\Phi(x)\psi_K(-bx)\,dx\\
&=\int_{\mathbf A_K}\Phi(x)\psi_K(-bx)\,dx\\
&=\widehat\Phi(-b).
\end{aligned}
$$

The unfolding is justified by absolute convergence. Fourier inversion on the compact quotient therefore gives

$$
P\Phi(x)=\sum_{b\in K}\widehat\Phi(-b)\psi_K(bx).
$$

Replacing $b$ by $-b$ yields the more symmetric form

$$
\sum_{a\in K}\Phi(x+a)
=\sum_{b\in K}\widehat\Phi(b)\psi_K(-bx).
$$

### 6.3 Poisson summation

Set $x=0$ in the preceding identity.

**Theorem 6.1 (adelic Poisson summation).** For every $\Phi\in\mathcal S(\mathbf A_K)$,

$$
\sum_{a\in K}\Phi(a)=\sum_{a\in K}\widehat\Phi(a),
$$

and both sums converge absolutely.

The proof strategy is worth retaining: periodize over the lattice, compute Fourier coefficients by unfolding, and use that the dual lattice is the same diagonal $K$. If the global additive character were changed so that the annihilator became a fractional ideal $L\ne K$, the right side would sum over $L$. If the quotient measure had volume $V$, an additional factor $V^{-1}$ would appear. Our standard character and self-dual measures make both corrections equal to one.

Here are the estimates behind the Fourier-series step. Choose a finite set $S$ so that outside $S$ the finite part is an integer-ring indicator. The allowed diagonal points then lie in one fractional ideal $\mathfrak a\subset K$. In the Minkowski space this is a full lattice. For every $M>\dim_{\mathbf R}K_\infty$ there is a constant $C_M$ such that, uniformly for $x$ in a fixed compact adelic set,

$$
|\Phi(x+a)|\le C_M(1+\|a\|)^{-M}
\qquad(a\in\mathfrak a).
$$

The number of lattice points of norm at most $R$ is $O(R^{[K:\mathbf Q]})$, so dyadic shells show absolute and uniform convergence. Applying archimedean differential operators to $\Phi$ gives the same estimate for all derivatives of $P\Phi$.

For the Fourier coefficients, integration by parts in any archimedean direction shows decay by arbitrary powers of the corresponding frequency. At finite places, local constancy makes the coefficient vanish unless the frequency belongs to a fixed fractional lattice. Combining the two facts gives an absolutely summable family $(c_b)_{b\in K}$. Absolute Fourier convergence on the compact quotient now justifies evaluation at every point, not merely almost everywhere. These estimates also prove absolute convergence on the transformed side directly.

### 6.4 Scaled lattices and fractional ideals

For $t\in\mathbf A_K^\times$, apply Poisson summation to $x\mapsto\Phi(tx)$. The dilation formula gives

$$
\sum_{a\in K}\Phi(ta)
=|t|_{\mathbf A}^{-1}
\sum_{a\in K}\widehat\Phi(t^{-1}a).
$$

This is the form used in the global zeta integral.

If the finite component of $t$ represents a fractional ideal $\mathfrak a$, the condition $t_va\in\mathcal O_v$ at all finite places says $a\in\mathfrak a^{-1}$ under the ideal convention fixed for ideles. Thus the scaled formula contains the classical Poisson formula for every ideal lattice in the Minkowski space. The inverse different appears automatically when one transforms an integer-lattice indicator at ramified places.

### 6.5 The rational Gaussian and the theta identity

Take $K=\mathbf Q$, choose $\Phi_p=\mathbf 1_{\mathbf Z_p}$ at every finite prime, and $\Phi_\infty(x)=e^{-\pi x^2}$. Then $\widehat\Phi=\Phi$. For the idele $t$ with real component $\sqrt y$ and finite components $1$, scaled Poisson summation gives

$$
\sum_{n\in\mathbf Z}e^{-\pi y n^2}
=y^{-1/2}\sum_{n\in\mathbf Z}e^{-\pi n^2/y}.
$$

This theta identity is the one-dimensional shadow of the general theorem. It also shows the origin of the substitution $s\leftrightarrow1-s$: Mellin transformation of $y^{-1/2}\theta(1/y)$ reverses the exponent around the midpoint $1/2$.

## 7. Multiplicative measure and quasicharacters

### 7.1 From additive to multiplicative measure

On a local field $F$, the measure $dx/|x|_F$ is invariant under multiplication. We choose its scalar as follows.

At a finite place, with $d=n(\psi)$ and self-dual $dx$, set

$$
d^\times x
=\frac{q^{d/2}}{1-q^{-1}}\frac{dx}{|x|_F}.
$$

Then

$$
\operatorname{vol}_{d^\times x}(\mathcal O_F^\times)=1.
$$

At a real place set

$$
d^\times x=\frac{dx}{|x|},
$$

and at a complex place, with $dz=2\,dx\,dy$ and $|z|_{\mathbf C}=z\bar z$, set

$$
d^\times z=\frac{2\,dx\,dy}{|z|_{\mathbf C}}.
$$

These archimedean choices are direct analogues of $dx/|x|$. They leave a harmless global scalar in the quotient measure on $C_K^1$; every residue statement below records that volume explicitly.

The restricted product $d^\times x=\prod_vd^\times x_v$ is well defined because finite unit groups have volume one almost everywhere. It gives Haar measure on $\mathbf A_K^\times$ and quotient measures on idele class groups.

### 7.2 Local quasicharacters and conductors

A continuous homomorphism $\chi:F^\times\to\mathbf C^\times$ is a quasicharacter. Its absolute value is $|x|_F^\sigma$ for a unique real $\sigma$ times a unitary character. We write the zeta integral using a unitary $\chi$ and a separate complex parameter $s$; this loses no generality.

At a finite place, the conductor exponent $a(\chi)$ is the least $a\ge0$ such that

$$
\chi(1+\mathfrak p^a)=1,
$$

with the convention $1+\mathfrak p^0=\mathcal O_F^\times$ for this sentence. Thus $a(\chi)=0$ exactly when $\chi$ is unramified, meaning trivial on $\mathcal O_F^\times$. If $a>0$, the restriction of $\chi$ to units factors through

$$
\mathcal O_F^\times/(1+\mathfrak p^a).
$$

For a unitary unramified character, $|\chi(\varpi)|=1$. The value on a different uniformizer is unchanged because the quotient is a unit.

### 7.3 Archimedean parameters

Every unitary character of $\mathbf R^\times$ is uniquely

$$
\chi_{m,t}(x)=\operatorname{sgn}(x)^m|x|^{it},
\qquad m\in\{0,1\},\quad t\in\mathbf R.
$$

Every unitary character of $\mathbf C^\times$ is uniquely

$$
\chi_{m,t}(z)
=\left(\frac z{|z|_{\mathrm{usual}}}\right)^m
|z|_{\mathbf C}^{it},
\qquad m\in\mathbf Z,\quad t\in\mathbf R.
$$

The use of $|z|_{\mathbf C}=|z|_{\mathrm{usual}}^2$ means that radial Mellin exponents are measured in units compatible with the product formula. The angular integer $m$ is independent of that choice.

### 7.4 Global characters and their local components

Let

$$
\omega:K^\times\backslash\mathbf A_K^\times\to\mathbf C^\times
$$

be unitary. Restriction to each embedded $K_v^\times$ gives $\omega_v$, and

$$
\omega(x)=\prod_v\omega_v(x_v).
$$

Almost every finite component is unramified. Triviality on $K^\times$ imposes the compatibility

$$
\prod_v\omega_v(a)=1\qquad(a\in K^\times).
$$

The finite conductor is

$$
\mathfrak f(\omega)=\prod_{v<\infty}\mathfrak p_v^{a(\omega_v)}.
$$

Only finitely many exponents are nonzero. The archimedean parameters must also satisfy a constraint on global units; they cannot be assigned independently. That constraint is automatically present when one starts with an idele class character.

### 7.5 A warning about Frobenius

An unramified local character produces the Euler factor

$$
L_v(s,\chi)=\frac1{1-\chi(\varpi_v)q_v^{-s}}.
$$

With arithmetic reciprocity, $\varpi_v$ maps to arithmetic Frobenius. Hence a character transported from the arithmetic side has

$$
\chi(\varpi_v)=\chi_{\mathrm{arith}}(\operatorname{Frob}_{v,\mathrm{arith}}).
$$

If one instead parametrizes a representation by geometric Frobenius, the displayed eigenvalue is inverted. The analytic definition above never changes; only the dictionary relating $\chi(\varpi_v)$ to a named Frobenius changes. This separation prevents an invisible inverse from entering later Euler products.

## 8. Nonarchimedean local zeta integrals

### 8.1 Definition and convergence

Let $F$ be nonarchimedean, $\phi\in\mathcal S(F)$, and $\chi$ unitary. Define

$$
Z(\phi,\chi,s)
=\int_{F^\times}\phi(x)\chi(x)|x|_F^s\,d^\times x.
$$

Because $\phi$ has compact support, only $x\to0$ can cause divergence. Local constancy makes $\phi$ constant near zero. Decomposing into valuation shells shows absolute convergence for

$$
\operatorname{Re}(s)>0.
$$

If $\phi(0)=0$, then local constancy makes $\phi$ vanish on a neighborhood of zero, and the integral is an entire finite Laurent polynomial in $q^{-s}$. Thus the possible denominator comes entirely from the constant germ at zero.

### 8.2 Shell decomposition

Write $x=\varpi^nu$ with $u\in\mathcal O^\times$. Since unit volume is one,

$$
Z(\phi,\chi,s)
=\sum_{n\in\mathbf Z}chi(\varpi)^nq^{-ns}
\int_{\mathcal O^\times}\phi(\varpi^nu)\chi(u)\,d^\times u.
$$

Compact support cuts off the sum for $n\ll0$. For $n\gg0$, $\phi(\varpi^nu)=\phi(0)$. If $\chi$ is nontrivial on units, the unit integral is zero; if $\chi$ is unramified, it equals $\phi(0)$. This is the whole distinction between ramified and unramified denominators.

### 8.3 The unramified calculation

Suppose $\chi$ is unramified and take $\phi=\mathbf 1_{\mathcal O}$. Then only $n\ge0$ occur and

$$
\begin{aligned}
Z(\mathbf 1_{\mathcal O},\chi,s)
&=\sum_{n\ge0}\chi(\varpi)^nq^{-ns}\\
&=\frac1{1-\chi(\varpi)q^{-s}}.
\end{aligned}
$$

This motivates

$$
L(s,\chi)=
\begin{cases}
(1-\chi(\varpi)q^{-s})^{-1},&a(\chi)=0,\\
1,&a(\chi)>0.
\end{cases}
$$

The calculation depends on the choice $\operatorname{vol}(\mathcal O^\times)=1$. Had we used $dx/|x|$ without its normalizing scalar, an unwanted factor $(1-q^{-1})q^{-d/2}$ would remain.

### 8.4 Ramified characters

Suppose $a=a(\chi)>0$. Then for every sufficiently large $n$, the function $u\mapsto\phi(\varpi^nu)$ is constant, so its integral against the nontrivial unit character $\chi$ vanishes. Thus the shell sum has only finitely many nonzero terms and

$$
Z(\phi,\chi,s)\in\mathbf C[q^s,q^{-s}].
$$

There are test functions for which the integral equals one. Define

$$
\phi_\chi(x)=
\begin{cases}
\chi(x)^{-1},&x\in\mathcal O^\times,\\
0,&\text{otherwise}.
\end{cases}
$$

Then

$$
Z(\phi_\chi,\chi,s)=1.
$$

This vector will calculate the ramified epsilon factor exactly.

### 8.5 Rationality and the local principal ideal

For fixed $\chi$, the set of all local zeta integrals is a fractional ideal in the Laurent polynomial ring $\mathbf C[q^s,q^{-s}]$, or equivalently in $\mathbf C[T,T^{-1}]$ with $T=q^{-s}$. Shell decomposition shows that every integral is divisible by $L(s,\chi)$ in the sense that

$$
\frac{Z(\phi,\chi,s)}{L(s,\chi)}
$$

is a Laurent polynomial. Conversely the standard unramified vector or the ramified vector $\phi_\chi$ makes the quotient one. Therefore the ideal is generated by $L(s,\chi)$.

This characterization is more robust than the formula for one test function. It says that the local $L$-factor is the unique generator with constant term one of all possible local zeta integrals.

There is also an explicit finite algorithm for an arbitrary test function. Choose $r,N$ so that $\phi$ is supported in $\mathfrak p^{-r}$ and constant on cosets of $\mathfrak p^N$. For each shell $-r\le n<N$, the unit integral is a finite sum on

$$
\mathcal O^\times/(1+\mathfrak p^{N-n}).
$$

For $n\ge N$, replace $\phi(\varpi^nu)$ by $\phi(0)$. If $\chi$ is unramified, the remaining tail is

$$
\phi(0)\frac{\chi(\varpi)^Nq^{-Ns}}
{1-\chi(\varpi)q^{-s}};
$$

if $\chi$ is ramified, it is zero. Thus every coefficient and every possible denominator is visible at finite residue level. This is useful when one changes a local test vector: the correction polynomial records only finitely much support and congruence data.

The same calculation gives a sharp counterexample to a common shortcut. If $\chi$ is ramified, then

$$
Z(\mathbf 1_{\mathcal O},\chi,s)=0,
$$

not $1$. The standard integer-ring vector generates the unramified factor only when the character is trivial on units. Ramified factors require a vector carrying the inverse unit character.

## 9. Archimedean local zeta integrals

### 9.1 The real place

Put

$$
\Gamma_{\mathbf R}(s)=\pi^{-s/2}\Gamma(s/2).
$$

Let $\chi_{m,t}(x)=\operatorname{sgn}(x)^m|x|^{it}$. The canonical local factor is

$$
L(s,\chi_{m,t})=\Gamma_{\mathbf R}(s+it+m).
$$

For $m=0$, take $\phi_0(x)=e^{-\pi x^2}$. Then

$$
\begin{aligned}
Z(\phi_0,\chi_{0,t},s)
&=2\int_0^\infty e^{-\pi x^2}x^{s+it}\frac{dx}{x}\\
&=\pi^{-(s+it)/2}\Gamma\left(\frac{s+it}{2}\right)\\
&=\Gamma_{\mathbf R}(s+it).
\end{aligned}
$$

For $m=1$, take $\phi_1(x)=xe^{-\pi x^2}$. Since $x\operatorname{sgn}(x)=|x|$,

$$
Z(\phi_1,\chi_{1,t},s)
=\Gamma_{\mathbf R}(s+it+1).
$$

An even test function paired with the sign character gives zero. This is a useful counterexample to the belief that one Gaussian always generates every archimedean factor; parity must match the character.

### 9.2 The complex place

Put

$$
\Gamma_{\mathbf C}(s)=2(2\pi)^{-s}\Gamma(s).
$$

For

$$
\chi_{m,t}(z)=\left(\frac z{|z|_{\mathrm{usual}}}\right)^m|z|_{\mathbf C}^{it},
$$

define

$$
L(s,\chi_{m,t})
=\Gamma_{\mathbf C}\left(s+it+\frac{|m|}{2}\right).
$$

Let

$$
\phi_m(z)=
\pi^{-1}
z^{\max(-m,0)}\bar z^{\max(m,0)}
e^{-2\pi|z|^2}.
$$

In polar coordinates, $d^\times z=2\,dr\,d\theta/r$. The angular factors cancel, and the radial substitution $u=2\pi r^2$ gives

$$
Z(\phi_m,\chi_{m,t},s)
=2(2\pi)^{-s-it-|m|/2}
\Gamma\left(s+it+\frac{|m|}{2}\right).
$$

Thus it equals the stated $L$-factor. Without the scalar $\pi^{-1}$, the angular integral would leave an extra factor $\pi$. The factor $2$ in both $\Gamma_{\mathbf C}$ and $d^\times z$ is forced by the self-dual additive measure.

### 9.3 Why the absolute value at a complex place is squared

Suppose one mistakenly used $|z|_{\mathrm{usual}}$ as the normalized local absolute value. Radial powers would then be $r^s$ instead of $r^{2s}$, the local degree would be off by two, and the product formula for $K^\times$ would fail at complex embeddings. The Mellin substitution would produce $\Gamma((s+|m|)/2)$ rather than the correct $\Gamma(s+|m|/2)$.

The squared normalization is therefore visible independently in three places: the Jacobian of multiplication on $\mathbf C$, the global product formula, and the complex gamma factor. Agreement among them is a strong consistency check.

### 9.4 Holomorphy after division by the local factor

For every $\phi\in\mathcal S(\mathbf R)$ or $\mathcal S(\mathbf C)$, the zeta integral initially converges for $\operatorname{Re}(s)>0$ and extends meromorphically. Taylor-expand $\phi$ at the origin to a sufficiently high order and subtract a compactly supported function having the same finite jet. The remainder vanishes to high order, so its Mellin integral extends farther left. Iterating gives continuation to the whole plane. The subtracted monomials contribute gamma functions with precisely the parity or angular weights above.

Consequently

$$
\frac{Z(\phi,\chi,s)}{L(s,\chi)}
$$

is entire. It is rapidly decreasing in vertical strips after excluding bounded neighborhoods of the poles of the gamma factor. Repeated integration by parts in the logarithmic radial variable proves the decay. This control later justifies multiplying local identities and shifting global Mellin contours.

## 10. The local functional equation

### 10.1 The distributional strategy

The local functional equation compares two meromorphic families of linear functionals on $\mathcal S(F)$:

$$
\phi\longmapsto Z(\phi,\chi,s)
$$

and

$$
\phi\longmapsto Z(\widehat\phi,\chi^{-1},1-s).
$$

Both transform in the same way under dilation. If $\phi_a(x)=\phi(ax)$, then

$$
Z(\phi_a,\chi,s)
=\chi(a)^{-1}|a|^{-s}Z(\phi,\chi,s),
$$

while the Fourier dilation identity gives the same covariance for the second family. The key uniqueness statement is that the space of distributions on $F$ with this multiplicative covariance is one-dimensional, away from the exceptional parameters and then everywhere by meromorphic continuation.

At a finite place, uniqueness follows by decomposing into valuation shells and using the transitive action of $F^\times$ on itself. At infinity, it follows from distributions homogeneous under dilation, with parity or angular type fixed by $\chi$. Possible distributions supported at zero occur only at discrete parameters; continuation across those parameters preserves the identity.

We spell out the finite-place argument because it controls the exceptional cases. Let $T$ be a distribution satisfying

$$
T(\phi_a)=\chi(a)^{-1}|a|^{-s}T(\phi).
$$

On functions supported in $F^\times$, every compact open set is a finite disjoint union of sets $a(1+\mathfrak p^N)$. Covariance determines $T$ on all their indicators from its value on $\mathbf 1_{1+\mathfrak p^N}$. Compatibility as $N$ increases and the prescribed unit character leave one scalar. Thus two such distributions agree on functions supported away from zero after rescaling.

Their difference is supported at zero. A distribution supported at zero on a totally disconnected field is a scalar multiple of evaluation $\phi\mapsto\phi(0)$: local constancy makes every test function constant on some neighborhood of zero. Evaluation has dilation character $1$. It can therefore occur only when $\chi(a)|a|^s=1$ for all $a$, a discrete exceptional condition. Away from that condition the space is one-dimensional. Both zeta families depend rationally on $q^{-s}$, so equality away from the exceptional points extends across them meromorphically.

At a real place, a distribution supported at zero is a finite sum of derivatives of the point mass, and the $r$th derivative has homogeneity $a^r$ together with a parity. At a complex place, derivatives in $z$ and $\bar z$ have specified radial degree and angular weight. These again occur only at a discrete set of $s$. On the complement, restriction to $F^\times$ and multiplicative transitivity leave one scalar. The archimedean zeta families are meromorphic by the Taylor-subtraction argument, so the same continuation completes the uniqueness proof there.

Existence now needs only one nonzero comparison point. In a common strip where both zeta integrals converge, take a test function for which the denominator is nonzero and define their ratio. Uniqueness makes the ratio independent of the test function. The local continuation results extend it meromorphically. This proves the local equation without presupposing any formula for $\gamma$.

### 10.2 Existence and uniqueness of the gamma factor

There is therefore a unique meromorphic function $\gamma(s,\chi,\psi)$ such that

$$
Z(\widehat\phi,\chi^{-1},1-s)
=\gamma(s,\chi,\psi)Z(\phi,\chi,s)
$$

for every $\phi\in\mathcal S(F)$. It is nonzero and satisfies

$$
\gamma(s,\chi,\psi)
\gamma(1-s,\chi^{-1},\psi)=\chi(-1).
$$

To verify the second relation, apply the equation twice and use $\widehat{\widehat\phi}(x)=\phi(-x)$. Replacing $x$ by $-x$ in the zeta integral multiplies it by $\chi(-1)$.

The identity contains all local normalization data. The gamma factor changes if the Fourier phase, additive character, or measure changes. The next decomposition separates its Euler denominator from its root-number term.

### 10.3 Epsilon factors and the exact equation

Define $\epsilon(s,\chi,\psi)$ by

$$
\gamma(s,\chi,\psi)
=\epsilon(s,\chi,\psi)
\frac{L(1-s,\chi^{-1})}{L(s,\chi)}.
$$

Equivalently,

$$
\frac{Z(\widehat\phi,\chi^{-1},1-s)}{L(1-s,\chi^{-1})}
=\epsilon(s,\chi,\psi)
\frac{Z(\phi,\chi,s)}{L(s,\chi)}.
$$

At a finite place, $\epsilon$ is a monomial in $q^{-s}$ times a complex number of modulus one for unitary $\chi$. At infinity it is a constant phase for the standard character. These assertions are calculations, not definitions, and we now make them exact.

### 10.4 Finite-place Gauss sums

Let $F$ have residue cardinality $q$, let $n=n(\psi)$, and let $a=a(\chi)$. Choose $c\in F^\times$ with

$$
v(c)=a+n.
$$

If $a>0$, define the normalized Gauss sum

$$
\tau(\chi,\psi;c)
=q^{-a/2}
\sum_{u\in\mathcal O^\times/(1+\mathfrak p^a)}
\chi(u)^{-1}\psi(u/c).
$$

Then $|\tau(\chi,\psi;c)|=1$, and

$$
\epsilon(s,\chi,\psi)
=\chi(c)\tau(\chi,\psi;c)
q^{(a+n)(1/2-s)}.
$$

For $a=0$, the compatible formula is

$$
\epsilon(s,\chi,\psi)
=\chi(\varpi)^nq^{n(1/2-s)}.
$$

Here is the decisive ramified calculation. Use $\phi_\chi$ from Section 8.4, for which $Z(\phi_\chi,\chi,s)=1$. Its transform is supported on $c^{-1}\mathcal O^\times$. For $y=c^{-1}u$,

$$
\widehat\phi_\chi(y)
=\operatorname{vol}(\mathfrak p^a)
\chi(u)
\sum_{r\in\mathcal O^\times/(1+\mathfrak p^a)}
\chi(r)^{-1}\psi(r/c).
$$

Now

$$
\operatorname{vol}(\mathfrak p^a)=q^{-a-n/2}
$$

for the self-dual measure. Substitution into the dual zeta integral gives

$$
\chi(c)q^{(a+n)(1-s)}q^{-a-n/2}q^{a/2}
\tau(\chi,\psi;c),
$$

which simplifies to the displayed formula. This derivation explains every exponent.

Changing $c$ by a unit changes the Gauss sum by the inverse character factor, so the product $\chi(c)\tau(\chi,\psi;c)$ is independent of the choice. The magnitude-one assertion follows by multiplying the Gauss sum by its complex conjugate and using additive orthogonality on the finite quotient.

Here is that orthogonality calculation. Write the unnormalized sum as $G$. Since $\chi$ is unitary,

$$
|G|^2
=\sum_{u,v}\chi(v/u)\psi((u-v)/c).
$$

Put $v=tu$. For fixed $t$, the inner sum over $u$ is an additive character sum on the unit classes. It vanishes unless $t\equiv1\pmod{\mathfrak p^a}$ at the exact conductor depth, and the surviving contribution is $q^a$. More invariantly, the Fourier transform of a primitive multiplicative character on the finite ring is supported on its unit dual orbit and has constant magnitude $q^{a/2}$. Hence $|G|^2=q^a$ and $|\tau|=1$. If the character were imprimitive at level $a$, the same calculation would vanish; minimality of $a(\chi)$ is essential.

The unramified formula can be checked without a limiting convention. For $a=0$, apply the local equation to $\mathbf 1_{\mathcal O}$. Its transform is

$$
q^{-n/2}\mathbf 1_{\mathfrak p^{-n}}.
$$

Decompose the latter into shells, compare the two geometric series, and obtain

$$
\gamma(s,\chi,\psi)
=\chi(\varpi)^nq^{n(1/2-s)}
\frac{1-\chi(\varpi)q^{-s}}
{1-\chi(\varpi)^{-1}q^{s-1}}.
$$

This is precisely $\epsilon(s,\chi,\psi)L(1-s,\chi^{-1})/L(s,\chi)$.

For the standard trace character on $K_v$, $n=d_v$. Thus even an unramified multiplicative character has a nontrivial epsilon monomial at a prime dividing the different.

### 10.5 Archimedean epsilon factors

For the standard real character $e^{2\pi ix}$,

$$
\epsilon(s,\chi_{m,t},\psi_{\mathbf R})=i^m.
$$

For $m=0$, the Gaussian is fixed. For $m=1$,

$$
\widehat{xe^{-\pi x^2}}(y)=iy e^{-\pi y^2},
$$

which supplies the factor $i$.

For the complex trace character $e^{2\pi i\operatorname{Tr}(z)}$,

$$
\epsilon(s,\chi_{m,t},\psi_{\mathbf C})=i^{|m|}.
$$

Indeed, the transform sends the angularly matched polynomial-Gaussian $\phi_m$ to $i^{|m|}$ times the polynomial-Gaussian of opposite angular weight. The absolute value on $m$ reflects that a positive or negative angular character requires a polynomial of degree $|m|$.

The polynomial transform follows from differentiation of the Gaussian identity. With positive Fourier phase,

$$
\widehat{x f}(y)=\frac1{2\pi i}\frac d{dy}\widehat f(y)
$$

over $\mathbf R$. In complex coordinates the trace pairing sends $z=x+iy$ and $w=u+iv$ to $2(xu-yv)$. Differentiating in $u$ and $v$ shows

$$
\widehat{\bar z,e^{-2\pi|z|^2}}(w)
=iw e^{-2\pi|w|^2},
$$

and

$$
\widehat{z,e^{-2\pi|z|^2}}(w)
=i\bar w e^{-2\pi|w|^2}.
$$

Iteration gives the phase $i^{|m|}$ and reverses angular weight exactly as the dual zeta integral requires.

### 10.6 Change of additive character

Let $\psi_b(x)=\psi(bx)$ and use the self-dual measure $|b|^{1/2}dx$. A direct change of variables in the Fourier transform gives

$$
\widehat\phi^{\,\psi_b}(y)
=|b|^{1/2}\widehat\phi^{\,\psi}(by).
$$

Substitution in the dual zeta integral yields

$$
\gamma(s,\chi,\psi_b)
=\chi(b)|b|^{s-1/2}\gamma(s,\chi,\psi),
$$

and the same formula for $\epsilon$. This proves the scaling law announced in Chapter 2.

The inverse character in the dual integral and the exponent $s-1/2$ are both forced. Replacing either by its negative would contradict the calculation under $b\mapsto b^{-1}$.

## 11. The global zeta integral

### 11.1 Definition on the idele group

For $\Phi\in\mathcal S(\mathbf A_K)$ and a unitary idele class character $\omega$, define

$$
Z(\Phi,\omega,s)
=\int_{\mathbf A_K^\times}
\Phi(x)\omega(x)|x|_{\mathbf A}^s\,d^\times x.
$$

For an elementary tensor this converges absolutely when $\operatorname{Re}(s)>1$. The stronger bound than the local condition $\operatorname{Re}(s)>0$ reflects the accumulation of infinitely many finite shells and is exactly the ordinary Euler-product half-plane.

To justify the half-plane, enlarge a finite set $S$ until all data outside it are standard and unramified. The absolute value of the tail is bounded by

$$
\prod_{v\notin S}(1-q_v^{-\sigma})^{-1},
\qquad \sigma=\operatorname{Re}(s),
$$

because $|\omega_v(\varpi_v)|=1$. Expanding this product gives a sum over integral ideals prime to $S$ of $(N\mathfrak a)^{-\sigma}$. The number of ideals of norm at most $X$ is $O(X)$: every ideal class has a fixed integral representative, and ideals in that class correspond after multiplication to principal ideals generated by lattice points in a bounded Minkowski region. Partial summation then gives convergence for $\sigma>1$. The finitely many places in $S$ contribute bounded local factors on compact subsets of that half-plane.

This also explains why a product of locally convergent integrals need not converge globally for $0<\sigma\le1$. Infinitely many harmless geometric series can accumulate into a divergent Euler product.

The integrand is not invariant under $K^\times$ because $\Phi(ax)$ changes. To expose the quotient, sum over the diagonal multiplicative lattice:

$$
\Theta_\Phi(x)=\sum_{a\in K^\times}\Phi(ax).
$$

Then $\Theta_\Phi$ is $K^\times$-invariant, and the global integral unfolds into an integral of $\Theta_\Phi$ over the idele class group.

### 11.2 Euler factorization

If $\Phi=\otimes_v\Phi_v$ and $\omega=\prod_v\omega_v$, then absolute convergence gives

$$
Z(\Phi,\omega,s)
=\prod_vZ(\Phi_v,\omega_v,s).
$$

At almost every finite place,

$$
\Phi_v=\mathbf 1_{\mathcal O_v},
\qquad \omega_v\text{ is unramified},
$$

so

$$
Z(\Phi_v,\omega_v,s)
=L_v(s,\omega_v).
$$

The product therefore has precisely the expected Euler tail. At the finitely many exceptional places, the quotient

$$
\frac{Z(\Phi_v,\omega_v,s)}{L_v(s,\omega_v)}
$$

is entire. This isolates all dependence on the chosen test function into finitely many entire factors.

The factorization proof should not be read as an infinite use of Fubini without control. At a finite stage $S$, integrate over

$$
\prod_{v\in S}K_v^\times
\times\prod_{v\notin S}\mathcal O_v^\times
$$

and then sum over the finitely supported valuation vectors outside $S$. Absolute convergence permits the sum and finite-product integrals to be interchanged. Passing through an increasing sequence of finite sets yields the Euler product by monotone convergence for absolute values and dominated convergence for the original integrand.

### 11.3 Unfolding along the idele class group

Let $C_K=K^\times\backslash\mathbf A_K^\times$. In the domain of absolute convergence,

$$
Z(\Phi,\omega,s)
=\int_{C_K}\Theta_\Phi(x)\omega(x)|x|_{\mathbf A}^s\,d^\times x.
$$

Indeed, choose a measurable fundamental domain for $K^\times$. Summing its translates fills $\mathbf A_K^\times$, and the product formula plus triviality of $\omega$ on $K^\times$ leaves the weight unchanged. Tonelli's theorem justifies the rearrangement first for absolute values.

The sum excludes $a=0$. Add it temporarily:

$$
\Theta_\Phi(x)=\sum_{a\in K}\Phi(ax)-\Phi(0).
$$

Scaled Poisson summation gives the fundamental identity

$$
\Theta_\Phi(x)+\Phi(0)
=|x|_{\mathbf A}^{-1}
\bigl(\Theta_{\widehat\Phi}(x^{-1})+\widehat\Phi(0)\bigr).
$$

Every term in the continuation argument comes from this equality.

### 11.4 Separating the module direction

The module map gives

$$
C_K/C_K^1\cong\mathbf R_{>0}.
$$

Choose a measurable section $t\mapsto j(t)$ with $|j(t)|_{\mathbf A}=t$. Haar measure decomposes as

$$
d^\times x=d^\times x_1\,\frac{dt}{t},
$$

up to the fixed normalization of the quotient measure on the compact group $C_K^1$. We take this identity as the definition of the compatible quotient measure and write

$$
\kappa_K=\operatorname{vol}(C_K^1).
$$

Because $C_K^1$ is compact, all difficult global behavior lies in the limits $t\to0$ and $t\to\infty$. The Schwartz estimates make $\Theta_\Phi(j(t)x_1)$ rapidly decreasing as $t\to\infty$, uniformly in $x_1$. Poisson summation converts the $t\to0$ behavior into another rapidly decreasing term plus the two explicit constants $\Phi(0)$ and $\widehat\Phi(0)$.

## 12. Continuation and the global functional equation

### 12.1 The split at module one

Split the unfolded integral into $|x|\ge1$ and $|x|\le1$:

$$
Z(\Phi,\omega,s)=I_+(\Phi,\omega,s)+I_-(\Phi,\omega,s).
$$

The large-module part

$$
I_+(\Phi,\omega,s)
=\int_{|x|\ge1}\Theta_\Phi(x)\omega(x)|x|^s\,d^\times x
$$

is entire in $s$. Uniform rapid decay dominates every power of $|x|$ on vertical strips.

For completeness, choose $N>|\operatorname{Re}(s)|+2$ on a fixed compact vertical strip. The theta estimate gives

$$
|\Theta_\Phi(x)|\le C_N|x|^{-N}
\qquad(|x|\ge1),
$$

uniformly on $C_K^1$. Hence the absolute value of the Mellin integrand is bounded by

$$
C_Nt^{-N+\operatorname{Re}(s)}\frac{dt}{t},
$$

which is integrable on $[1,\infty)$. Differentiating with respect to $s$ introduces powers of $\log t$, still dominated after increasing $N$. This proves holomorphy, not merely pointwise convergence.

For the small-module part, insert the scaled Poisson identity. The substitution $x\mapsto x^{-1}$ carries $|x|\le1$ to $|x|\ge1$, preserves multiplicative Haar measure, changes $\omega$ to $\omega^{-1}$, and changes $|x|^s$ to $|x|^{-s}$.

### 12.2 Poisson summation inside the integral

After substitution, the nonconstant term becomes

$$
I_+(\widehat\Phi,\omega^{-1},1-s).
$$

The constant terms contribute only when $\omega$ is trivial on $C_K^1$. For a unitary global character, being trivial on $C_K^1$ means $\omega(x)=|x|^{it_0}$ for some real $t_0$. Since the spectral shift may be absorbed into $s$, it is cleanest to state the pole formula for $\omega=1$ and the corresponding shifted statement for a pure module character.

For $\omega=1$, direct integration over $C_K^1\times(0,1]$ gives

$$
\int_{|x|\le1}|x|^s\,d^\times x
=\kappa_K\int_0^1t^s\frac{dt}{t}
=\frac{\kappa_K}{s}.
$$

Keeping the signs from

$$
\Theta_\Phi(x)
=|x|^{-1}\Theta_{\widehat\Phi}(x^{-1})
+|x|^{-1}\widehat\Phi(0)-\Phi(0)
$$

yields the continuation formula

$$
\begin{aligned}
Z(\Phi,1,s)
={}&I_+(\Phi,1,s)+I_+(\widehat\Phi,1,1-s)\\
&+\kappa_K\left(\frac{\widehat\Phi(0)}{s-1}-\frac{\Phi(0)}s\right).
\end{aligned}
$$

The same formula without the rational terms holds for a character nontrivial on $C_K^1$.

### 12.3 Meromorphic continuation and poles

The right side of the continuation formula is meromorphic on all of $\mathbf C$. Therefore so is $Z(\Phi,\omega,s)$. For $\omega=1$, the only possible poles are simple and

$$
\operatorname*{Res}_{s=1}Z(\Phi,1,s)
=\kappa_K\widehat\Phi(0),
$$

$$
\operatorname*{Res}_{s=0}Z(\Phi,1,s)
=-\kappa_K\Phi(0).
$$

For a nontrivial unitary character not equal to a pure module character, the integral is entire. For $\omega=|\cdot|^{it_0}$, replace $s$ by $s+it_0$ in the trivial-character statement; the possible poles move to $s=-it_0$ and $s=1-it_0$.

The word “possible” matters for an arbitrary test function. If $\Phi(0)=0$, the pole at zero disappears; if $\widehat\Phi(0)=\int\Phi=0$, the pole at one disappears. Poles are features of the zeta distribution, not unavoidable singularities of every test integral.

### 12.4 The global functional equation

The continuation formula is symmetric under

$$
(\Phi,\omega,s)
\longmapsto
(\widehat\Phi,\omega^{-1},1-s).
$$

Indeed, Fourier inversion changes $\widehat{\widehat\Phi}$ to $\Phi(-x)$, and the substitution $a\mapsto-a$ in the lattice sum introduces $\omega(-1)$ twice in matching places. With our definition on $\mathbf A_K^\times$, the result is

$$
\boxed{
Z(\Phi,\omega,s)
=Z(\widehat\Phi,\omega^{-1},1-s).
}
$$

This equality first holds where both sides are represented by their continuation formulas and hence everywhere meromorphically.

For a factorizable $\Phi$, multiply the local functional equations. Wherever the local zeta integrals do not vanish,

$$
\prod_v\gamma(s,\omega_v,\psi_v)=1.
$$

This product identity is not an extra theorem: it is the compatibility condition between local functional equations and the global Poisson theorem. Almost every factor is the quotient of unramified Euler factors, so the product is understood meromorphically.

### 12.5 Why no boundary term is missing

Two analytic points are decisive. First, $I_+$ is entire because the theta sum decays uniformly on the compact norm-one quotient. Pointwise decay alone would not justify integration over $C_K^1$. Second, the terms $\Phi(0)$ and $\widehat\Phi(0)$ must be separated before applying inversion. Omitting the zero term would incorrectly make the trivial-character integral entire and erase both residues.

The argument also explains why compactness of $C_K^1$ is indispensable. Without it, the module would not be the only escape direction, and a one-variable Mellin split would not control the quotient.

## 13. Completed Hecke functions and exact global factors

### 13.1 The completed product

For a unitary idele class character $\omega=\prod_v\omega_v$, define

$$
\Lambda(s,\omega)=\prod_vL_v(s,\omega_v),
$$

where

$$
L_v(s,\omega_v)=
\begin{cases}
(1-\omega_v(\varpi_v)q_v^{-s})^{-1},&v<\infty, a(\omega_v)=0,\\
1,&v<\infty, a(\omega_v)>0,\\
\Gamma_{\mathbf R}(s+it_v+m_v),&K_v=\mathbf R,\\
\Gamma_{\mathbf C}(s+it_v+|m_v|/2),&K_v=\mathbf C.
\end{cases}
$$

The finite Euler product converges absolutely for $\operatorname{Re}(s)>1$. The archimedean product is finite. Choose local test functions with

$$
Z(\Phi_v,\omega_v,s)=L_v(s,\omega_v)
$$

at every exceptional place, using the vectors constructed in Chapters 8 and 9. At almost every place use $\mathbf 1_{\mathcal O_v}$. Then

$$
Z(\Phi,\omega,s)=\Lambda(s,\omega).
$$

Thus the global continuation theorem gives meromorphic continuation of the completed product. Different local test vectors multiply it by entire correction factors but do not change the canonical generator $L_v$.

### 13.2 Finite conductor and discriminant

Let

$$
\mathfrak f(\omega)=\prod_{v<\infty}\mathfrak p_v^{a_v},
\qquad a_v=a(\omega_v).
$$

For the standard trace character, $n(\psi_v)=d_v$. The finite epsilon factors contain

$$
q_v^{(a_v+d_v)(1/2-s)}.
$$

Multiplying over finite places gives

$$
\bigl(N\mathfrak f(\omega)\,|D_K|\bigr)^{1/2-s}.
$$

This is the exact origin of the conductor–discriminant factor. The conductor comes from multiplicative ramification; the discriminant comes from the additive trace character and self-dual measure. Combining them too early obscures their different roles.

At a ramified finite place choose $c_v$ with $v(c_v)=a_v+d_v$ and set

$$
W_v(\omega_v)
=\omega_v(c_v)\tau(\omega_v,\psi_v;c_v).
$$

For an unramified component set $W_v(\omega_v)=\omega_v(\varpi_v)^{d_v}$. Each has modulus one.

### 13.3 The root number

At a real place put $W_v=i^{m_v}$, and at a complex place put $W_v=i^{|m_v|}$. The global root number is

$$
W(\omega)=\prod_vW_v(\omega_v),
\qquad |W(\omega)|=1.
$$

Only finitely many finite factors differ from one. The global epsilon factor is

$$
\epsilon(s,\omega)
=W(\omega)
\bigl(N\mathfrak f(\omega)|D_K|\bigr)^{1/2-s}.
$$

The completed functional equation is

$$
\boxed{
\Lambda(s,\omega)
=\epsilon(s,\omega)
\Lambda(1-s,\omega^{-1}).
}
$$

This form follows from the product of local epsilon equations. Applying it twice gives

$$
W(\omega)W(\omega^{-1})
=\omega(-1),
$$

with the local interpretation already encoded in the double-transform relation. For unitary $\omega$, complex conjugation identifies $\omega^{-1}$ with $\overline\omega$.

To see the relation between the global and local equations without suppressing correction factors, take any factorizable $\Phi$ and put

$$
E_v(\Phi_v,\omega_v,s)
=\frac{Z(\Phi_v,\omega_v,s)}{L_v(s,\omega_v)}.
$$

Almost every $E_v$ is one. The local equations give

$$
E_v(\widehat\Phi_v,\omega_v^{-1},1-s)
=\epsilon_v(s,\omega_v,\psi_v)E_v(\Phi_v,\omega_v,s).
$$

Multiplying and using global Poisson summation yields

$$
\Lambda(s,\omega)\prod_vE_v(\Phi_v,\omega_v,s)
=\Lambda(1-s,\omega^{-1})
\prod_v\epsilon_v(s,\omega_v,\psi_v)E_v(\Phi_v,\omega_v,s).
$$

Choose the local vectors so that no $E_v$ is identically zero and cancel their finite product meromorphically. This proves that the global epsilon factor is independent of every test-vector choice.

Some authors absorb $(N\mathfrak f|D_K|)^{s/2}$ into the definition of the completed function, producing a constant root number. Our convention keeps $\Lambda$ as the direct product of local $L$-factors and places the conductor–discriminant monomial in $\epsilon(s,\omega)$. Both arrangements are equivalent; formulas must not mix them.

### 13.4 The trivial character and the Dedekind zeta function

For $\omega=1$, the finite local factors are

$$
(1-q_v^{-s})^{-1},
$$

whose product is the Dedekind zeta function $\zeta_K(s)$. At real places the factor is $\Gamma_{\mathbf R}(s)$ and at complex places $\Gamma_{\mathbf C}(s)$. Therefore

$$
\Lambda_K(s)
=\Gamma_{\mathbf R}(s)^{r_1}
\Gamma_{\mathbf C}(s)^{r_2}
\zeta_K(s).
$$

Our epsilon factor is

$$
\epsilon(s,1)=|D_K|^{1/2-s}.
$$

Hence

$$
\Lambda_K(s)=|D_K|^{1/2-s}\Lambda_K(1-s).
$$

Equivalently, the symmetrically completed function

$$
\xi_K(s)=|D_K|^{s/2}\Lambda_K(s)
$$

satisfies

$$
\xi_K(s)=\xi_K(1-s).
$$

The global zeta distribution has simple poles at $0$ and $1$. After choosing standard local vectors, this recovers the corresponding poles of $\zeta_K(s)$; the gamma factors account for how the pole at zero appears in the completed expression.

### 13.5 Nontrivial characters

If $\omega$ is nontrivial and not a pure module character shifted into the integration parameter, the global zeta integral is entire. Choose local vectors generating the local factors. The finite product $\Lambda(s,\omega)$ is then entire unless a chosen archimedean gamma factor has a pole canceled by a zero of the finite Euler product; the product as a whole is entire by the global theorem. In particular, nontrivial finite-order Hecke characters have entire completed $L$-functions.

Over $\mathbf Q$, a primitive finite-order idele class character of conductor $N$ is the adelic form of a primitive Dirichlet character $\chi$ modulo $N$, together with a parity $m$ satisfying $\chi(-1)=(-1)^m$. Its completed function is

$$
\Lambda(s,\chi)
=\Gamma_{\mathbf R}(s+m)L(s,\chi),
$$

under the present local-factor convention, and its equation is

$$
\Lambda(s,\chi)
=W(\chi)N^{1/2-s}\Lambda(1-s,\overline\chi).
$$

The finite root number is the normalized Gauss sum, while the real place contributes $i^m$. Writing the classical completion instead as

$$
\left(\frac N\pi\right)^{(s+m)/2}
\Gamma\left(\frac{s+m}{2}\right)L(s,\chi)
$$

moves a power of $N$ from the epsilon factor to the left side. This example illustrates why two familiar-looking functional equations may distribute conductor powers differently while expressing the same identity.

The functional equation relates zeros about the line $\operatorname{Re}(s)=1/2$. It does not by itself locate them on that line. Nor does meromorphic continuation follow from the Euler product alone: the Euler product supplies the right half-plane, while Poisson summation supplies the passage across the critical strip.

## 14. The reusable normalization dictionary

### 14.1 Local data at a finite place

For rapid reference, let $F=K_v$, $q=q_v$, $\mathfrak D_v=\mathfrak p_v^{d_v}$, and let $\chi$ be unitary of conductor exponent $a$.

$$
\begin{array}{c|c}
\text{datum}&\text{normalization}\\ \hline
\text{absolute value}&|\varpi|=q^{-1}\\
\text{additive conductor}&\mathcal O^\perp=\mathfrak p^{-d_v}\\
\text{self-dual additive volume}&\operatorname{vol}(\mathcal O)=q^{-d_v/2}\\
\text{multiplicative volume}&\operatorname{vol}(\mathcal O^\times)=1\\
\text{Fourier phase}&\widehat\phi(y)=\int\phi(x)\psi(xy)\,dx\\
\text{inversion}&\widehat{\widehat\phi}(x)=\phi(-x)\\
\text{unramified factor}&(1-\chi(\varpi)q^{-s})^{-1}\\
\text{ramified factor}&1\\
\text{epsilon exponent}&(a+d_v)(1/2-s).
\end{array}
$$

If $a>0$ and $v(c)=a+d_v$, then

$$
\epsilon(s,\chi,\psi_v)
=\chi(c)q^{-a/2}
\sum_{u\in\mathcal O^\times/(1+\mathfrak p^a)}
\chi(u)^{-1}\psi_v(u/c)
\;q^{(a+d_v)(1/2-s)}.
$$

Arithmetic reciprocity sends $\varpi$ to arithmetic Frobenius. This last line is a dictionary convention; the analytic formulas already stand on their own.

### 14.2 Local data at infinity

At a real place,

$$
\psi(x)=e^{2\pi ix},
\qquad dx\text{ is self-dual},
\qquad d^\times x=dx/|x|,
$$

and

$$
L(s,\operatorname{sgn}^m|\cdot|^{it})
=\Gamma_{\mathbf R}(s+it+m),
\qquad \epsilon=i^m.
$$

At a complex place,

$$
\psi(z)=e^{2\pi i\operatorname{Tr}_{\mathbf C/\mathbf R}(z)},
\qquad dz=2\,dx\,dy,
\qquad d^\times z=\frac{2\,dx\,dy}{z\bar z},
$$

and

$$
L\left(s,(z/|z|)^m|z|_{\mathbf C}^{it}\right)
=\Gamma_{\mathbf C}\left(s+it+\frac{|m|}{2}\right),
\qquad \epsilon=i^{|m|}.
$$

Here

$$
\Gamma_{\mathbf R}(s)=\pi^{-s/2}\Gamma(s/2),
\qquad
\Gamma_{\mathbf C}(s)=2(2\pi)^{-s}\Gamma(s).
$$

### 14.3 Global compatibility checks

The local choices pass four independent global tests.

First, $\psi_K$ is trivial on $K$, so the diagonal is contained in its annihilator. Approximation and local nondegeneracy show equality.

Second, the product of self-dual measures gives

$$
\operatorname{vol}(\mathbf A_K/K)=1.
$$

Third, the product formula makes dilation by $a\in K^\times$ preserve adelic additive volume and makes $|a|_{\mathbf A}^s=1$ in every unfolding.

Fourth, for every global idele class character,

$$
\prod_v\gamma(s,\omega_v,\psi_v)=1.
$$

Equivalently,

$$
\Lambda(s,\omega)
=W(\omega)
\bigl(N\mathfrak f(\omega)|D_K|\bigr)^{1/2-s}
\Lambda(1-s,\omega^{-1}).
$$

Any proposed local convention that fails one of these tests cannot be combined with the others unchanged.

### 14.4 Common normalization failures

Several near-correct formulas are especially dangerous.

Using $\operatorname{vol}(\mathcal O_v)=1$ at a ramified trace place while retaining the self-dual inversion formula loses $q_v^{-d_v/2}$ and eventually loses $|D_K|^{1/2-s}$.

Using $e^{-2\pi ixy}$ for the Fourier transform while retaining the positive-phase translation formulas reverses modulations and conjugates Gauss sums. The theory remains valid after a consistent global reversal, but isolated sign changes do not cancel.

Using $|z|_{\mathrm{usual}}$ at a complex place halves Mellin exponents and breaks the product formula. The normalized complex absolute value is $z\bar z$.

Calling a finite character unramified merely because it has small conductor is imprecise. Unramified means $a(\chi)=0$, or equivalently triviality on all units. A nontrivial tame character has $a(\chi)=1$ and local $L$-factor $1$.

Finally, replacing arithmetic Frobenius by geometric Frobenius without inverting the parameter $\chi(\varpi)$ changes Euler factors. The analytic convention is always the displayed value on a uniformizer; the named Frobenius convention governs only its arithmetic interpretation.

### 14.5 Conclusion

The Schwartz–Bruhat space is the analytic expression of the adelic restriction: rapid decrease governs the finitely many archimedean directions, while compact support and local constancy govern every nonarchimedean direction. The trace character makes the diagonal field self-annihilating, and self-dual measures turn this geometric fact into an exact summation formula with no unexplained covolume.

Poisson summation then does more than compare two lattice sums. Inserted into the Mellin transform on idele classes, it exchanges small and large module, isolates the two zero-orbit terms, continues the zeta integral, and reflects $s$ across $1/2$. Local shell calculations identify the finite Euler factors; Gaussian Mellin integrals identify the archimedean factors; finite Fourier analysis identifies Gauss sums and conductor exponents. Their product yields the completed character equation with discriminant, conductor, and root number all accounted for.

The durable chain of ideas is therefore

$$
\text{self-dual local analysis}
\longrightarrow
\text{adelic Poisson summation}
\longrightarrow
\text{global Mellin continuation}
\longrightarrow
\text{local and global functional equations}.
$$

Every arrow carries exact hypotheses and exact normalizations. That precision is what allows the same local factors and character conventions to pass unchanged into the later analysis of automorphic forms.
