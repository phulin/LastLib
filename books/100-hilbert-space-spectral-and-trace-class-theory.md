# Hilbert-Space Spectral and Trace-Class Theory

## Contents

- [Introduction](#introduction)
- [1. Hilbert-space geometry behind spectral theory](#1-hilbert-space-geometry-behind-spectral-theory)
  - [1.1 Orthogonality as a method of analysis](#11-orthogonality-as-a-method-of-analysis)
  - [1.2 Projections and orthogonal sums](#12-projections-and-orthogonal-sums)
  - [1.3 Adjoint, positive, and unitary operators](#13-adjoint-positive-and-unitary-operators)
  - [1.4 Compactness and finite-dimensional approximation](#14-compactness-and-finite-dimensional-approximation)
- [2. Closed operators and graph domains](#2-closed-operators-and-graph-domains)
  - [2.1 Why a differential operator includes its domain](#21-why-a-differential-operator-includes-its-domain)
  - [2.2 Graphs, graph norms, and closure](#22-graphs-graph-norms-and-closure)
  - [2.3 The adjoint of an unbounded operator](#23-the-adjoint-of-an-unbounded-operator)
  - [2.4 Symmetric is not self-adjoint](#24-symmetric-is-not-self-adjoint)
  - [2.5 Cores and invariant subspaces](#25-cores-and-invariant-subspaces)
- [3. Self-adjointness and the resolvent](#3-self-adjointness-and-the-resolvent)
  - [3.1 The nonreal resolvent estimate](#31-the-nonreal-resolvent-estimate)
  - [3.2 Resolvent criteria for self-adjointness](#32-resolvent-criteria-for-self-adjointness)
  - [3.3 The Cayley transform and boundary conditions](#33-the-cayley-transform-and-boundary-conditions)
  - [3.4 Essential self-adjointness and bounded perturbations](#34-essential-self-adjointness-and-bounded-perturbations)
- [4. Closed quadratic forms](#4-closed-quadratic-forms)
  - [4.1 Energy before operator](#41-energy-before-operator)
  - [4.2 Closed and closable forms](#42-closed-and-closable-forms)
  - [4.3 The representation theorem](#43-the-representation-theorem)
  - [4.4 The Friedrichs extension](#44-the-friedrichs-extension)
  - [4.5 Compact form domains](#45-compact-form-domains)
- [5. Spectral measures and functional calculus](#5-spectral-measures-and-functional-calculus)
  - [5.1 From eigenvectors to spectral projections](#51-from-eigenvectors-to-spectral-projections)
  - [5.2 The bounded spectral theorem](#52-the-bounded-spectral-theorem)
  - [5.3 Borel functional calculus](#53-borel-functional-calculus)
  - [5.4 The unbounded spectral theorem](#54-the-unbounded-spectral-theorem)
  - [5.5 Multiplication models and spectral type](#55-multiplication-models-and-spectral-type)
- [6. Compact operators and compact resolvents](#6-compact-operators-and-compact-resolvents)
  - [6.1 The compact self-adjoint spectral theorem](#61-the-compact-self-adjoint-spectral-theorem)
  - [6.2 Singular values and polar decomposition](#62-singular-values-and-polar-decomposition)
  - [6.3 Compact resolvent and discrete spectrum](#63-compact-resolvent-and-discrete-spectrum)
  - [6.4 Variational eigenvalue principles](#64-variational-eigenvalue-principles)
  - [6.5 Spectral functions and counting](#65-spectral-functions-and-counting)
- [7. Hilbert--Schmidt operators and kernels](#7-hilbertschmidt-operators-and-kernels)
  - [7.1 A square-summable operator ideal](#71-a-square-summable-operator-ideal)
  - [7.2 Basis independence and ideal estimates](#72-basis-independence-and-ideal-estimates)
  - [7.3 Integral kernels](#73-integral-kernels)
  - [7.4 Composition of kernels](#74-composition-of-kernels)
- [8. Trace-class operators and trace identities](#8-trace-class-operators-and-trace-identities)
  - [8.1 Summable singular values](#81-summable-singular-values)
  - [8.2 The operator trace](#82-the-operator-trace)
  - [8.3 Cyclicity and ideal identities](#83-cyclicity-and-ideal-identities)
  - [8.4 Positive operators, projections, and eigenvalue sums](#84-positive-operators-projections-and-eigenvalue-sums)
  - [8.5 Trace-norm convergence](#85-trace-norm-convergence)
- [9. Diagonal kernels and spectral traces](#9-diagonal-kernels-and-spectral-traces)
  - [9.1 Why an arbitrary kernel has no diagonal](#91-why-an-arbitrary-kernel-has-no-diagonal)
  - [9.2 The Hilbert--Schmidt product formula](#92-the-hilbertschmidt-product-formula)
  - [9.3 Positive continuous kernels](#93-positive-continuous-kernels)
  - [9.4 Heat kernels and resolvent powers](#94-heat-kernels-and-resolvent-powers)
- [10. Orthogonal decompositions and commuting actions](#10-orthogonal-decompositions-and-commuting-actions)
  - [10.1 Reducing subspaces](#101-reducing-subspaces)
  - [10.2 Countable Hilbert sums](#102-countable-hilbert-sums)
  - [10.3 Commuting symmetries and finite multiplicity](#103-commuting-symmetries-and-finite-multiplicity)
  - [10.4 Simultaneous spectral organization](#104-simultaneous-spectral-organization)
- [11. The spectral mechanism for cuspidal automorphic spaces](#11-the-spectral-mechanism-for-cuspidal-automorphic-spaces)
  - [11.1 The analytic input and the spectral output](#111-the-analytic-input-and-the-spectral-output)
  - [11.2 Type-by-type compactness](#112-type-by-type-compactness)
  - [11.3 Smoothing kernels and the cuspidal trace](#113-smoothing-kernels-and-the-cuspidal-trace)
  - [11.4 Spectral and geometric expansions](#114-spectral-and-geometric-expansions)
  - [11.5 Twisted traces](#115-twisted-traces)
- [Conclusion](#conclusion)

## Introduction

Spectral theory begins with a finite-dimensional picture. A Hermitian matrix admits an orthonormal basis of eigenvectors, a positive matrix has a positive square root, and the trace is both the sum of diagonal entries and the sum of eigenvalues. None of these statements survives in infinite dimension without a change of language. A bounded self-adjoint operator may have no eigenvectors at all. A differential operator is not even defined on the whole Hilbert space. An integral kernel that is square-integrable is defined only almost everywhere, so its values on the diagonal can be changed arbitrarily. The purpose of this book is to identify the hypotheses and the constructions that recover the finite-dimensional picture in exactly the forms needed by analysis on arithmetic quotients.

Three ideas organize the subject.

First, an unbounded operator is inseparable from its domain. The graph, rather than a formula such as $-d^2/dx^2$, records boundary conditions and controls limits. Closedness says that the graph contains every limit it ought to contain; self-adjointness says that no hidden boundary condition remains in the adjoint domain.

Second, eigenvectors must often be replaced by spectral projections. A self-adjoint operator $A$ is encoded by a projection-valued measure $E_A$, and functions of $A$ are obtained by integration:

$$
f(A)=\int_{\mathbb R} f(\lambda)\,dE_A(\lambda).
$$

When one resolvent of $A$ is compact, these projections become finite-dimensional on bounded spectral intervals. The integral then collapses to an orthogonal eigenfunction expansion. This is the decisive bridge between general spectral theory and a discrete spectrum.

Third, compactness has quantitative refinements. Hilbert--Schmidt operators have square-summable singular values and are represented by square-integrable kernels. Trace-class operators have summable singular values and possess a basis-independent trace. The passage from a kernel to a trace is delicate: square integrability alone gives no meaningful diagonal. We will isolate the additional positivity, continuity, factorization, or smoothing that justifies a diagonal integral.

The final chapter assembles these tools into the abstract spectral argument used for cuspidal automorphic spaces. Geometry and reduction theory must supply closedness, cusp decay, elliptic estimates, and compact embeddings. Once those inputs are known, the Hilbert-space mechanism gives discrete spectral decompositions, finite multiplicities, trace-class smoothing operators, and equality between spectral traces and diagonal kernel integrals.

Throughout, Hilbert spaces are complex and separable unless explicitly stated otherwise. The inner product $\langle x,y\rangle$ is linear in $x$ and conjugate-linear in $y$. The bounded operators from $H$ to $K$ form $\mathcal B(H,K)$, and $\mathcal B(H)=\mathcal B(H,H)$. The identity is $I$. If $M$ is a closed subspace, $P_M$ denotes orthogonal projection onto $M$. This convention fixes all adjoint and kernel formulas and will not be changed later.

## 1. Hilbert-space geometry behind spectral theory

The later theory is infinite-dimensional, but its decisive estimates come from elementary Hilbert geometry. This chapter collects the pieces that will recur: orthogonal projection turns approximation into decomposition, adjoints turn range questions into kernel questions, and compactness turns bounded sequences into convergent subsequences. The goal is not to repeat all of functional analysis, but to make the geometric mechanisms behind the major proofs explicit.

### 1.1 Orthogonality as a method of analysis

The value of a Hilbert space is not merely that it is a complete normed vector space. Its norm comes from an inner product, and orthogonality turns approximation into an exact identity. If $x=y+z$ with $y\perp z$, then

$$
\|x\|^2=\|y\|^2+\|z\|^2.
$$

This Pythagorean identity is the source of projection methods, Fourier expansions, and the square-summability estimates behind Hilbert--Schmidt theory.

Let $(e_n)_{n\geq 1}$ be an orthonormal sequence. For every $x\in H$, Bessel's inequality says

$$
\sum_{n=1}^{\infty}|\langle x,e_n\rangle|^2\leq \|x\|^2.
$$

Indeed, for the partial sum $s_N=\sum_{n\leq N}\langle x,e_n\rangle e_n$, the vector $x-s_N$ is orthogonal to every $e_n$ with $n\leq N$. Hence

$$
\|x\|^2=\|x-s_N\|^2+\sum_{n\leq N}|\langle x,e_n\rangle|^2.
$$

Taking $N\to\infty$ gives the inequality. Equality holds exactly when $x$ belongs to the closed span of the sequence. Thus an orthonormal basis is characterized by Parseval's identity

$$
\|x\|^2=\sum_n |\langle x,e_n\rangle|^2,
\qquad
x=\sum_n\langle x,e_n\rangle e_n.
$$

Both series statements are norm statements. Pointwise convergence, when the vectors are functions, is an additional analytic question.

The Riesz representation theorem will be used repeatedly: every continuous linear functional $\ell$ on $H$ has a unique representing vector $y$ with $\ell(x)=\langle x,y\rangle$. Its proof already exhibits the geometry of the subject. If $\ell\neq0$, project any vector outside $\ker\ell$ onto $(\ker\ell)^\perp$. That complement is one-dimensional; normalizing its generator produces $y$, and uniqueness follows from nondegeneracy of the inner product.

### 1.2 Projections and orthogonal sums

A closed subspace $M\subset H$ has an orthogonal complement

$$
M^\perp=\{x\in H:\langle x,m\rangle=0\text{ for all }m\in M\},
$$

and every $x\in H$ decomposes uniquely as $x=m+n$ with $m\in M$ and $n\in M^\perp$. To prove existence, minimize the distance from $x$ to $M$. A minimizing sequence is Cauchy by the parallelogram identity, its limit lies in $M$ by closedness, and the first-variation identity shows that the error is orthogonal to $M$.

The map $P_Mx=m$ is bounded, $P_M^2=P_M$, and $P_M^*=P_M$. Conversely, every bounded operator $P$ satisfying $P^2=P=P^*$ is orthogonal projection onto its closed range. Idempotence alone is not enough: on $\mathbb C^2$, the map

$$
P(x,y)=(x+y,0)
$$

is a projection, but its kernel is not orthogonal to its range.

For a family $(H_j)_{j\in J}$, the Hilbert direct sum is

$$
\bigoplus_{j\in J}^{2} H_j
=
\left\{(x_j):\sum_j\|x_j\|^2<\infty\right\}.
$$

Only countably many coordinates of any one vector are nonzero. If $(M_j)$ is a mutually orthogonal family of closed subspaces of $H$, summation gives an isometry from $\bigoplus_j^2M_j$ onto $\overline{\sum_jM_j}$. Surjectivity onto all of $H$ is equivalent to

$$
\bigcap_jM_j^\perp=\{0\}.
$$

This criterion will finish several spectral-theorem proofs: after constructing all eigenspaces, it remains to show that their common orthogonal complement is zero.

### 1.3 Adjoint, positive, and unitary operators

For $T\in\mathcal B(H,K)$, the adjoint $T^*\in\mathcal B(K,H)$ is determined by

$$
\langle Tx,y\rangle=\langle x,T^*y\rangle.
$$

Existence follows by applying Riesz representation to $x\mapsto\langle Tx,y\rangle$; the uniform bound $\|T^*y\|\leq\|T\|\|y\|$ makes $T^*$ bounded. Directly from the definition,

$$
(ST)^*=T^*S^*,\qquad \|T^*T\|=\|T\|^2,
\qquad (\operatorname{ran}T)^\perp=\ker T^*.
$$

An operator is self-adjoint if $T=T^*$, normal if $TT^*=T^*T$, and unitary if $T^*T=TT^*=I$. It is positive, written $T\geq0$, if $\langle Tx,x\rangle\geq0$ for all $x$. Positivity forces self-adjointness: the polarization identity recovers $\langle Tx,y\rangle$ from the quadratic function $x\mapsto\langle Tx,x\rangle$, and that function is real.

The rank-one operator determined by $u\in K$ and $v\in H$ is

$$
u\otimes v:x\longmapsto \langle x,v\rangle u.
$$

It satisfies $(u\otimes v)^*=v\otimes u$ and $\|u\otimes v\|=\|u\|\|v\|$. Finite sums of rank-one operators are precisely the finite-rank operators. They are the elementary pieces from which compact and trace-class operators will be approximated.

Two elementary orthogonality facts already foreshadow the spectral theorem. If $T=T^*$ and $Tx=\lambda x$ with $x\neq0$, then

$$
\lambda\|x\|^2=\langle Tx,x\rangle
=\overline{\langle Tx,x\rangle},
$$

so $\lambda\in\mathbb R$. If $Ty=\mu y$ with $\lambda\neq\mu$, then

$$
\lambda\langle x,y\rangle
=\langle Tx,y\rangle
=\langle x,Ty\rangle
=\mu\langle x,y\rangle,
$$

and hence $x\perp y$.

### 1.4 Compactness and finite-dimensional approximation

A bounded operator $T:H\to K$ is compact if it sends the closed unit ball to a relatively compact set. Equivalently, every bounded sequence $(x_n)$ has a subsequence for which $(Tx_n)$ converges. Finite-rank operators are compact, and the operator-norm limit of compact operators is compact. The latter follows from a diagonal subsequence argument, or from total boundedness of the image of the unit ball.

Compact operators form a two-sided ideal:

$$
T\text{ compact},\ A,B\text{ bounded}
\quad\Longrightarrow\quad ATB\text{ compact}.
$$

The identity on an infinite-dimensional Hilbert space is not compact. An orthonormal sequence lies in the unit ball and has pairwise distance $\sqrt2$, so it has no convergent subsequence. This simple example is the obstruction behind finite multiplicity: if a compact operator acted as a nonzero scalar on an infinite-dimensional eigenspace, its restriction would be a nonzero multiple of the identity and could not be compact.

On Hilbert spaces, compactness is exactly norm approximation by finite-rank operators. To see the nontrivial direction, cover the relatively compact set $T(B_H)$ by finitely many balls of radius $\varepsilon$. Let $M$ be the span of their centers and $P_M$ its orthogonal projection. Then every $Tx$ with $\|x\|\leq1$ lies within $\varepsilon$ of $M$, so

$$
\|T-P_MT\|\leq\varepsilon.
$$

This characterization explains why compact operators retain much of finite-dimensional linear algebra, but not all of it. The unilateral weighted shift on $\ell^2(\mathbb N)$,

$$
T(e_n)=\frac1n e_{n+1},
$$

is compact and has no nonzero eigenvalue. Self-adjointness, not compactness alone, is what restores an eigenbasis.

## 2. Closed operators and graph domains

Spectral questions for differential operators cannot begin until limits and boundary conditions have been encoded correctly. This chapter replaces a formal expression by a graph-domain operator, develops the adjoint from ambient-norm duality, and explains why symmetry is only a preliminary condition. The examples show that domains are mathematical data, not technical annotations.

### 2.1 Why a differential operator includes its domain

Consider the expression $-i\,d/dx$ on $L^2(0,1)$. It can be imposed on compactly supported smooth functions, on $H^1$ functions vanishing at both endpoints, on periodic $H^1$ functions, or on functions satisfying $f(1)=e^{i\theta}f(0)$. These choices have different adjoints and different spectra. Thus an unbounded operator is a pair

$$
T=(D(T),x\mapsto Tx),
$$

where $D(T)$ is a linear subspace of $H$. Equality of unbounded operators means equality both of domains and of values.

The domain is normally dense. Density is not needed to write $Tx$, but it is needed for the adjoint to be an operator rather than a multivalued relation. We therefore assume density whenever adjoints are discussed.

The multiplication model gives the most transparent first example. Let $m:X\to\mathbb C$ be measurable on a measure space and define

$$
D(M_m)=\{f\in L^2(X):mf\in L^2(X)\},
\qquad M_mf=mf.
$$

Truncating $f$ to the sets $\{|m|\leq n\}$ shows that $D(M_m)$ is dense. If $m$ is unbounded, $M_m$ is unbounded, yet it is closed. If $m$ is real almost everywhere, it will be self-adjoint. This example is the local model for every self-adjoint operator under the spectral theorem.

### 2.2 Graphs, graph norms, and closure

The graph of $T:D(T)\subset H\to K$ is

$$
\mathcal G(T)=\{(x,Tx):x\in D(T)\}\subset H\oplus K.
$$

The operator is closed when this graph is closed. Equivalently,

$$
x_n\to x,quad Tx_n\to y
\quad\Longrightarrow\quad
x\in D(T),\ Tx=y.
$$

The graph norm

$$
\|x\|_T=(\|x\|^2+\|Tx\|^2)^{1/2}
$$

makes $D(T)$ a normed space, and the map $x\mapsto(x,Tx)$ is an isometry onto $\mathcal G(T)$. Consequently, $T$ is closed exactly when $D(T)$ is complete in the graph norm. Notice that graph-norm convergence is stronger than convergence in $H$; it remembers convergence of the derivatives or other quantities represented by $T$.

An operator is closable if the closure of its graph is again the graph of an operator. This happens exactly when

$$
x_n\to0,quad Tx_n\to y
\quad\Longrightarrow\quad y=0.
$$

Indeed, the only obstruction to the closed relation $\overline{\mathcal G(T)}$ being single-valued is the presence of a point $(0,y)$ with $y\neq0$. When $T$ is closable, the operator whose graph is $\overline{\mathcal G(T)}$ is the closure $\overline T$. Its domain consists of limits $x$ of sequences $x_n\in D(T)$ for which $Tx_n$ converges, and $\overline T x=\lim Tx_n$.

The closed graph theorem supplies a useful warning. If a closed operator has domain all of $H$, then it is bounded. Therefore every genuinely unbounded closed operator must have a proper domain, even though that domain may be dense.

For the multiplication operator above, suppose $f_n\to f$ and $mf_n\to g$ in $L^2$. Pass to a subsequence along which both convergences hold almost everywhere. Then $mf_n\to mf$ and $mf_n\to g$ almost everywhere, so $g=mf$. Hence $M_m$ is closed.

### 2.3 The adjoint of an unbounded operator

Let $T:D(T)\subset H\to K$ be densely defined. A vector $y\in K$ belongs to $D(T^*)$ if the functional

$$
x\longmapsto\langle Tx,y\rangle,qquad x\in D(T),
$$

is bounded with respect to the ambient $H$-norm. There is then a unique $z\in H$ such that

$$
\langle Tx,y\rangle=\langle x,z\rangle
\quad\text{for all }x\in D(T),
$$

and we set $T^*y=z$. The critical point is that the bound uses $\|x\|$, not the graph norm; graph-norm boundedness would hold for every $y$ and would not detect boundary conditions.

**Proposition 2.1.** The adjoint $T^*$ is closed. Moreover, $T$ is closable if and only if $D(T^*)$ is dense, and in that case

$$
\overline T=T^{**}.
$$

**Proof.** If $y_n\to y$ and $T^*y_n\to z$, then for $x\in D(T)$,

$$
\langle Tx,y\rangle
=\lim_n\langle Tx,y_n\rangle
=\lim_n\langle x,T^*y_n\rangle
=\langle x,z\rangle.
$$

Thus $y\in D(T^*)$ and $T^*y=z$, proving closedness.

There is a geometric way to prove the remaining statements. Define the unitary quarter-turn $J:H\oplus K\to K\oplus H$ by $J(x,y)=(-y,x)$. A direct use of the adjoint definition gives

$$
\mathcal G(T^*)=J\mathcal G(T)^\perp.
$$

Taking orthogonal complements shows that $D(T^*)$ fails to be dense precisely when the closure of $\mathcal G(T)$ contains a nonzero vertical vector $(0,y)$. That is precisely failure of closability. If $D(T^*)$ is dense, applying the graph identity twice gives $\mathcal G(T^{**})=\overline{\mathcal G(T)}$. ∎

The range-kernel relations also extend to closed operators:

$$
(\operatorname{ran}T)^\perp=\ker T^*,
\qquad
\overline{\operatorname{ran}T}=(\ker T^*)^\perp.
$$

They follow immediately from the adjoint definition and orthogonal-complement duality. These relations will turn a lower bound into surjectivity in the resolvent argument.

### 2.4 Symmetric is not self-adjoint

A densely defined operator $T$ on $H$ is symmetric if

$$
\langle Tx,y\rangle=\langle x,Ty\rangle
\quad (x,y\in D(T)).
$$

This says exactly that $T\subset T^*$: the adjoint extends $T$. It is self-adjoint if $T=T^*$, including equality of domains. The domain equality is the substantial part.

Take $T_0=-i\,d/dx$ on $C_c^\infty(0,1)\subset L^2(0,1)$. Integration by parts shows that $T_0$ is symmetric. Its closure has domain $H_0^1(0,1)$, while its adjoint has domain $H^1(0,1)$ and acts by the same differential expression. Thus the closure is symmetric but not self-adjoint. The missing information is visible in the boundary form

$$
\langle -if',g\rangle-\langle f,-ig'\rangle
=-i f(1)\overline{g(1)}+i f(0)\overline{g(0)}.
$$

For each $\theta\in\mathbb R$, the domain

$$
D(T_\theta)=\{f\in H^1(0,1):f(1)=e^{i\theta}f(0)\}
$$

makes the boundary form vanish and is maximal with that property. Hence $T_\theta$ is self-adjoint. Solving $-if'=\lambda f$ gives $f(x)=ce^{i\lambda x}$ and

$$
\lambda\in\theta+2\pi\mathbb Z.
$$

The same formal expression has therefore acquired an entire family of spectra, indexed by boundary conditions.

By contrast, the real multiplication operator $M_m$ is self-adjoint on its maximal domain. If $g\in D(M_m^*)$, then $f\mapsto\langle mf,g\rangle$ is ambient-norm bounded on $D(M_m)$. Testing on functions supported where $|m|\leq n$ shows that the representing function must be $mg$ there. Letting $n\to\infty$ yields $mg\in L^2$ and $M_m^*g=mg$. Thus $D(M_m^*)=D(M_m)$.

Every symmetric operator is closable because $D(T)\subset D(T^*)$ is dense. Its closure remains symmetric. But a closed symmetric operator need not be self-adjoint, as the derivative example shows. Confusing these notions is one of the most consequential errors in unbounded analysis.

### 2.5 Cores and invariant subspaces

A subspace $D_0\subset D(T)$ is a core for a closed operator $T$ if it is dense in $D(T)$ for the graph norm. Equivalently, the closure of the restriction $T|_{D_0}$ is $T$. A core permits calculations on regular vectors without changing the operator.

For $M_m$, the vectors supported where $|m|\leq n$ form an increasing family whose union is a core: for $f\in D(M_m)$, the truncations $f_n=1_{\{|m|\leq n\}}f$ satisfy both $f_n\to f$ and $mf_n\to mf$ in $L^2$. In differential problems, compactly supported smooth functions may or may not be a core; boundary conditions decide the issue.

A closed subspace $M$ is invariant for $T$ if $D(T)\cap M$ is carried into $M$. For unbounded operators this is weaker than the decomposition one usually wants. We call $M$ reducing if its orthogonal projection satisfies

$$
P_MD(T)\subset D(T),
\qquad TP_Mx=P_MTx\quad(x\in D(T)).
$$

Then both $M$ and $M^\perp$ inherit closed operators and

$$
T=T|_M\oplus T|_{M^\perp}.
$$

Spectral subspaces will be reducing in precisely this strong sense.

## 3. Self-adjointness and the resolvent

Self-adjointness is powerful because it turns the two open half-planes into a controlled region of invertibility. Resolvent estimates will simultaneously certify boundary conditions, construct bounded transforms of unbounded operators, and provide the object on which compactness can sensibly be imposed. This chapter develops those links before spectral measures are introduced.

### 3.1 The nonreal resolvent estimate

For a closed operator $T$, the resolvent set $\rho(T)$ consists of $z\in\mathbb C$ such that

$$
T-z:D(T)\longrightarrow H
$$

is bijective and has bounded inverse on $H$. The spectrum is $\sigma(T)=\mathbb C\setminus\rho(T)$. Closedness makes boundedness of the inverse automatic by the closed graph theorem, but quantitative estimates are more useful.

If $T$ is symmetric and $z=a+ib$ with $b\neq0$, then

$$
\|(T-z)x\|\,\|x\|
\geq |\langle(T-z)x,x\rangle|
\geq |\operatorname{Im}\langle(T-z)x,x\rangle|
=|b|\|x\|^2.
$$

Therefore

$$
\|(T-z)x\|\geq |\operatorname{Im}z|\,\|x\|.
\tag{3.1}
$$

This has three immediate consequences. The map $T-z$ is injective; its inverse on its range has norm at most $|\operatorname{Im}z|^{-1}$; and if $T$ is closed, its range is closed. The last assertion follows because a convergent sequence $(T-z)x_n$ makes $(x_n)$ Cauchy by (3.1), after which closedness identifies the limit.

**Theorem 3.1.** If $A$ is self-adjoint, then

$$
\mathbb C\setminus\mathbb R\subset\rho(A),
\qquad
\|(A-z)^{-1}\|\leq\frac1{|\operatorname{Im}z|}.
$$

**Proof.** We only need surjectivity. The range of $A-z$ is closed. Its orthogonal complement is

$$
(\operatorname{ran}(A-z))^\perp=\ker(A^*-\overline z)=\ker(A-\overline z).
$$

Estimate (3.1), applied to $\overline z$, makes this kernel zero. Thus the range is both dense and closed, hence all of $H$. ∎

In particular, the spectrum of a self-adjoint operator is real. The resolvent identity

$$
R(z)-R(w)=(z-w)R(z)R(w),
\qquad R(z)=(A-z)^{-1},
\tag{3.2}
$$

follows by multiplying out both sides. It shows that compactness of one resolvent implies compactness of every resolvent: if $R(w)$ is compact, then $R(z)=R(w)+(z-w)R(z)R(w)$ is compact.

### 3.2 Resolvent criteria for self-adjointness

The nonreal range detects whether a symmetric operator has all required boundary conditions.

**Theorem 3.2.** Let $T$ be densely defined and symmetric. The following are equivalent.

1. $T$ is self-adjoint.
2. $\operatorname{ran}(T-i)=\operatorname{ran}(T+i)=H$.
3. $T$ is closed and $\ker(T^*-i)=\ker(T^*+i)=\{0\}$.

**Proof.** Self-adjointness implies the range statement by Theorem 3.1. The orthogonal-complement formulas

$$
(\operatorname{ran}(T-i))^\perp=\ker(T^*+i),
\qquad
(\operatorname{ran}(T+i))^\perp=\ker(T^*-i)
$$

show the relation between ranges and kernels. If $T$ is closed, (3.1) makes both ranges closed, so vanishing of the two kernels makes both ranges all of $H$.

It remains to show that the range condition implies $T=T^*$. Take $y\in D(T^*)$. Choose $x\in D(T)$ with $(T-i)x=(T^*-i)y$. Then $u=y-x\in D(T^*)$ and $(T^*-i)u=0$. The other range equality implies $\ker(T^*-i)=0$, hence $y=x\in D(T)$. Thus $D(T^*)\subset D(T)$, while symmetry gives the reverse inclusion. ∎

The spaces

$$
N_+=\ker(T^*-i),\qquad N_-=\ker(T^*+i)
$$

are the deficiency spaces. Their dimensions measure the missing boundary data. A closed symmetric operator has self-adjoint extensions exactly when the two deficiency dimensions agree; a unitary map $N_+\to N_-$ specifies an extension. The derivative example has one-dimensional deficiency spaces, and the phase $e^{i\theta}$ encodes this unitary choice. The general classification will not be needed later, but it explains why boundary conditions naturally come in unitary families.

### 3.3 The Cayley transform and boundary conditions

The Cayley transform converts an unbounded self-adjoint operator into bounded unitary geometry. For self-adjoint $A$, define

$$
U=(A-i)(A+i)^{-1}=I-2i(A+i)^{-1}.
$$

The resolvent estimate makes $U$ bounded. For $y=(A+i)x$,

$$
\|Uy\|=\|(A-i)x\|=\|(A+i)x\|=\|y\|,
$$

because $\|(A\pm i)x\|^2=\|Ax\|^2+\|x\|^2$. The same calculation for $A$ with the opposite sign shows that $U$ is onto, so it is unitary. Moreover, $Ux=x$ would imply $(A+i)^{-1}x=0$, hence $x=0$: $1$ is not an eigenvalue of $U$.

Conversely, if $U$ is unitary and $\ker(I-U)=0$, set

$$
D(A)=\operatorname{ran}(I-U),
\qquad
A\big((I-U)x\big)=i(I+U)x.
\tag{3.3}
$$

Injectivity of $I-U$ makes this well-defined. The range is dense because its orthogonal complement is $\ker(I-U^*)$, which is also zero. Direct calculation shows that $A$ is self-adjoint and that its Cayley transform is $U$. Formally,

$$
A=i(I+U)(I-U)^{-1};
$$

the domain in (3.3) is what gives this formula meaning.

The Cayley transform is useful conceptually because the difference between symmetry and self-adjointness becomes the difference between a partial isometry and a unitary operator. It is also a reminder that the resolvent, rather than $A$ itself, is the bounded object through which compactness should be tested.

### 3.4 Essential self-adjointness and bounded perturbations

A symmetric operator $T$ is essentially self-adjoint if its closure is self-adjoint. Equivalently, $T^*$ has no nonzero solutions to $(T^*\mp i)u=0$. This is the right uniqueness statement for an operator initially defined on a convenient core: there is exactly one self-adjoint operator compatible with that core.

The following perturbation result is elementary but extremely useful.

**Theorem 3.3.** Let $A$ be self-adjoint and let $B\in\mathcal B(H)$ be self-adjoint. Then $A+B$, with domain $D(A)$, is self-adjoint. Any core for $A$ is a core for $A+B$.

**Proof.** The graph norms are equivalent:

$$
\|x\|_{A+B}\leq (1+\|B\|)\|x\|_A,
\qquad
\|x\|_A\leq (1+\|B\|)\|x\|_{A+B}.
$$

Thus $A+B$ is closed and the core assertion follows. To prove self-adjointness, choose $t>\|B\|$. Since $\|(A-it)^{-1}\|\leq t^{-1}$,

$$
A+B-it=\big(I+B(A-it)^{-1}\big)(A-it).
$$

The first factor is invertible by its Neumann series. Hence $A+B-it$ is onto; the same argument with $+it$ gives the other range. Theorem 3.2 applies. ∎

The boundedness hypothesis cannot simply be discarded. Singular potentials and lower-order differential terms may alter the domain or even destroy essential self-adjointness. A broader theorem allows symmetric $B$ satisfying

$$
\|Bx\|\leq a\|Ax\|+b\|x\|,
\qquad a<1,
$$

but its proof requires a more careful resolvent argument. The strict inequality is decisive: it ensures equivalence of graph norms and makes the perturbation small after moving sufficiently far along the imaginary axis.

## 4. Closed quadratic forms

Many operators arising from geometry are first visible through an energy integral. Forms permit weak first derivatives where the eventual operator requires stronger regularity, and they incorporate boundary conditions through completion. The central task of this chapter is to pass from a closed semibounded energy to a unique self-adjoint operator and to locate compact resolvent at the level of the energy space.

### 4.1 Energy before operator

Second-order operators are often easier to construct from their energy than from a pointwise formula. For a region $\Omega\subset\mathbb R^d$, the formal Dirichlet Laplacian corresponds to

$$
\mathfrak a[u,v]=\int_\Omega \nabla u\cdot\overline{\nabla v},
\qquad D(\mathfrak a)=H_0^1(\Omega).
$$

The form domain asks for only one weak derivative, whereas the operator domain asks that the distributional Laplacian lie in $L^2$ and that the boundary condition be satisfied. Starting with the form therefore separates the robust energy estimate from the subtler regularity problem.

A sesquilinear form $\mathfrak a$ on $H$ consists of a dense subspace $V=D(\mathfrak a)$ and a map $\mathfrak a:V\times V\to\mathbb C$, linear in the first variable and conjugate-linear in the second. It is symmetric if

$$
\mathfrak a[u,v]=\overline{\mathfrak a[v,u]},
$$

and lower semibounded if some $m\in\mathbb R$ satisfies

$$
\mathfrak a[u,u]\geq m\|u\|^2.
$$

For a symmetric form, the quadratic energy $\mathfrak a[u]=\mathfrak a[u,u]$ determines the full form by polarization. Lower semiboundedness is the energy analogue of a self-adjoint operator being bounded below.

Choose $c> -m$ and define

$$
\langle u,v\rangle_{\mathfrak a,c}
=\mathfrak a[u,v]+c\langle u,v\rangle,
\qquad
\|u\|_{\mathfrak a,c}^2=\mathfrak a[u]+c\|u\|^2.
$$

Different choices of such $c$ give equivalent norms. The form is closed if $V$ is complete for one, hence every, form norm. This definition is designed so that a Cauchy sequence whose vectors and energies converge has a legitimate limit in the energy space.

### 4.2 Closed and closable forms

A semibounded form is closable if it has a closed extension. There is an intrinsic test parallel to the graph criterion.

**Proposition 4.1.** A lower-semibounded symmetric form $\mathfrak a$ is closable if and only if, whenever $u_n\in V$ satisfies

$$
u_n\to0\text{ in }H,
\qquad
\mathfrak a[u_n-u_k]+c\|u_n-u_k\|^2\to0,
$$

one has $\mathfrak a[u_n]+c\|u_n\|^2\to0$.

**Proof.** Complete $V$ in the form norm and let $j$ send the class of a form-Cauchy sequence to its $H$-limit. The displayed condition says exactly that $j$ is injective. If it is injective, identify the completion with its image in $H$; the extended form is closed. If it is not injective, a nonzero energy vector is represented by a sequence converging to zero in $H$, and no closed extension can assign it consistently to the zero vector. ∎

The closure $\overline{\mathfrak a}$ is the smallest closed extension. Its domain consists of the $H$-limits of form-Cauchy sequences, and its value is obtained by continuity in the form norm.

An instructive distinction appears on an interval. The form

$$
\int_0^1 u'(x)\overline{v'(x)}\,dx
$$

on $C_c^\infty(0,1)$ closes on $H_0^1(0,1)$ and produces Dirichlet boundary conditions. The same expression initially defined on smooth functions on $[0,1]$ closes on $H^1(0,1)$ and produces Neumann boundary conditions. The energy formula alone does not choose a boundary condition; its initial form domain does.

### 4.3 The representation theorem

The central result turns a closed energy into a self-adjoint operator. We give the construction because it clarifies both the operator domain and the resolvent.

**Theorem 4.2 (representation of closed forms).** Let $\mathfrak a$ be a densely defined, closed, symmetric form with lower bound $m$. There is a unique self-adjoint operator $A\geq mI$ such that

$$
D(A)\subset V,
\qquad
\mathfrak a[u,v]=\langle Au,v\rangle
\quad(u\in D(A),\ v\in V).
\tag{4.1}
$$

Its domain is characterized by

$$
D(A)=\left\{u\in V:\text{there is }f\in H\text{ with }
\mathfrak a[u,v]=\langle f,v\rangle\text{ for all }v\in V\right\},
\tag{4.2}
$$

and then $Au=f$.

**Proof strategy.** Shift the form until it is coercive, solve the weak equation by Hilbert-space geometry, and recognize the solution operator as a resolvent.

Choose $c> -m$ and put $\mathfrak b[u,v]=\mathfrak a[u,v]+c\langle u,v\rangle$. This is the inner product of the Hilbert space $V$. For $f\in H$, the functional $v\mapsto\langle f,v\rangle$ is continuous on $V$, since $\|v\|\leq(c+m)^{-1/2}\|v\|_{\mathfrak b}$. Riesz representation in $V$ gives a unique $u=Gf\in V$ such that

$$
\mathfrak b[u,v]=\langle f,v\rangle
\quad(v\in V).
\tag{4.3}
$$

The map $G:H\to H$ is bounded. Taking $v=Gg$ in (4.3), and using symmetry, gives $\langle Gf,g\rangle=\langle f,Gg\rangle$, so $G$ is self-adjoint. It is positive and injective. Its range is dense because $\ker G=(\operatorname{ran}G)^\perp$ for a self-adjoint operator and $\ker G=0$.

Define $A+c=G^{-1}$ on $\operatorname{ran}G$. A bounded, injective, self-adjoint operator with dense range has a self-adjoint inverse on its range: either apply the resolvent range criterion directly, or observe that the graph of $G^{-1}$ is obtained by flipping the closed graph of $G$. Equation (4.3) now becomes

$$
\mathfrak a[u,v]=\langle Au,v\rangle.
$$

It also gives exactly the characterization (4.2). Finally,

$$
\langle Au,u\rangle=\mathfrak a[u]\geq m\|u\|^2,
$$

so $A\geq mI$. Uniqueness follows from (4.2), which recovers both $D(A)$ and $Au$ from the form. ∎

The proof reveals an important asymmetry: $V$ is usually larger than $D(A)$. Every $u\in V$ has finite energy, but $u$ belongs to $D(A)$ only when the weak functional $v\mapsto\mathfrak a[u,v]$ is represented by an $H$-vector. For the Dirichlet form this is the requirement that the weak Laplacian lie in $L^2$.

The form domain is the square-root domain:

$$
V=D((A-m+1)^{1/2}),
$$

with equivalent, and after normalization equal, norms. This statement will follow transparently from the spectral calculus in Chapter 5. It explains why first derivatives govern a second-order operator.

### 4.4 The Friedrichs extension

Suppose $S$ is densely defined, symmetric, and bounded below by $m$. Its operator form

$$
\mathfrak a_S[u,v]=\langle Su,v\rangle,
\qquad D(\mathfrak a_S)=D(S),
$$

is closable. To see the decisive point, shift so that $S\geq I$. If $u_n\to0$ in $H$ and $(u_n)$ is form-Cauchy, then for fixed $v\in D(S)$,

$$
\mathfrak a_S[u_n,v]=\langle u_n,Sv\rangle\to0.
$$

The form-limit is therefore orthogonal, in the form inner product, to the dense set $D(S)$ and must be zero. The closure of this form produces, by Theorem 4.2, a self-adjoint extension $S_F$, called the Friedrichs extension.

It preserves the lower bound and is distinguished by its energy domain. For the minimal Laplacian on an interval it gives the Dirichlet Laplacian, not an arbitrary self-adjoint boundary condition. More generally, it is the extension obtained by completing the original test domain in energy. This makes it canonical in variational problems.

Semiboundedness matters. The first derivative on an interval has many self-adjoint extensions but no Friedrichs extension selected by a lower-bounded energy, because its quadratic form is not bounded below. The construction is not a universal boundary-condition machine; it is an energy method.

### 4.5 Compact form domains

Let $\mathfrak a$ be closed and semibounded, with associated operator $A$. The inclusion

$$
j:(V,\|\cdot\|_{\mathfrak a,c})\longrightarrow H
$$

is continuous. If it is compact, then $A$ has compact resolvent.

**Proposition 4.3.** If the form-domain inclusion $j$ is compact, then $(A+c)^{-1}$ is compact for every sufficiently large $c$.

**Proof.** In the proof of Theorem 4.2, the weak solution map sends a bounded set of $H$ to a bounded set of $V$: equation (4.3) and coercivity give

$$
\|Gf\|_{\mathfrak b}\leq C\|f\|.
$$

As an operator on $H$, $G=(A+c)^{-1}$ is the composite of this bounded solution map $H\to V$ with the compact inclusion $j:V\to H$. ∎

This is the standard path from geometric analysis to discrete spectrum. One proves an energy estimate, identifies the completed energy space, and then proves that bounded sets in that space are relatively compact in $L^2$. On a bounded Euclidean region, the compactness is the Rellich principle. On a noncompact quotient it is false for the full $L^2$ space: mass can escape to infinity. Cuspidality and cusp decay are what later restore compactness on the relevant subspace.

After the spectral theorem we will prove the converse: for a semibounded self-adjoint operator, compactness of the resolvent is equivalent to compactness of the form-domain inclusion. Thus compact form embedding is not merely a convenient sufficient condition; it is the exact energy-space expression of compact resolvent.

## 5. Spectral measures and functional calculus

An eigenbasis is too narrow a language for general self-adjoint operators. Spectral projections retain the orthogonality of finite-dimensional diagonalization while allowing a continuum of spectral values. This chapter constructs the projection-valued and multiplication-operator forms of the spectral theorem, then uses them to define functions of unbounded operators with exact domains.

### 5.1 From eigenvectors to spectral projections

The operator $M_t$ on $L^2([0,1])$, given by $(M_tf)(t)=tf(t)$, is bounded and self-adjoint. It has no eigenvalue: a function satisfying $tf(t)=\lambda f(t)$ must be supported on the measure-zero set $\{\lambda\}$. Thus no eigenvector basis can exist.

Nevertheless, $M_t$ is perfectly diagonal. For a Borel set $B\subset\mathbb R$, define

$$
(E(B)f)(t)=1_B(t)f(t).
$$

Each $E(B)$ is an orthogonal projection, disjoint sets give orthogonal projections, and countable unions give strongly convergent sums. Moreover,

$$
M_t=\int_{\mathbb R}\lambda\,dE(\lambda).
$$

The spectral theorem says that every self-adjoint operator has this form after a unitary change of coordinates.

A projection-valued measure on $\mathbb R$ is a map $E$ from Borel sets to orthogonal projections on $H$ satisfying

$$
E(\varnothing)=0,qquad E(\mathbb R)=I,qquad
E(B\cap C)=E(B)E(C),
$$

and, for pairwise disjoint $(B_n)$,

$$
E\!\left(\bigcup_nB_n\right)x=\sum_nE(B_n)x
\quad\text{for every }x\in H.
$$

The last sum converges in norm. For $x,y\in H$, the scalar set function

$$
\mu_{x,y}(B)=\langle E(B)x,y\rangle
$$

is a complex measure, and $\mu_x=\mu_{x,x}$ is a positive measure of total mass $\|x\|^2$. These scalar measures allow ordinary integration to define operator integration.

### 5.2 The bounded spectral theorem

**Theorem 5.1 (bounded spectral theorem).** If $A\in\mathcal B(H)$ is self-adjoint, there is a unique projection-valued measure $E_A$ supported on the compact set $\sigma(A)\subset\mathbb R$ such that

$$
A=\int_{\sigma(A)}\lambda\,dE_A(\lambda).
\tag{5.1}
$$

For every bounded Borel function $f$ on $\sigma(A)$,

$$
f(A)=\int f(\lambda)\,dE_A(\lambda)
$$

is a bounded operator satisfying

$$
\|f(A)\|=\|f\|_{L^\infty(E_A)},
\quad
\overline f(A)=f(A)^*,
\quad
(fg)(A)=f(A)g(A).
\tag{5.2}
$$

Here the essential supremum means that sets annihilated by $E_A$ are ignored.

**Construction and proof.** We spell out the architecture, since each step is used later.

For a polynomial $p$, define $p(A)$ algebraically. Self-adjointness and the resolvent estimate imply

$$
\|p(A)\|\leq \sup_{\lambda\in\sigma(A)}|p(\lambda)|.
\tag{5.3}
$$

One way to see the crucial case is to factor a polynomial with no zeros on the real spectrum and use the resolvent; approximation then gives the general inequality. Real polynomial approximation on the compact spectrum extends $p\mapsto p(A)$ uniquely to a unital, norm-preserving, adjoint-preserving homomorphism

$$
C(\sigma(A))\longrightarrow\mathcal B(H),
\qquad f\longmapsto f(A).
\tag{5.4}
$$

For fixed $x,y$, the functional $f\mapsto\langle f(A)x,y\rangle$ on $C(\sigma(A))$ is bounded. The representation theorem for continuous linear functionals on a compact space supplies a complex measure $\mu_{x,y}$ with

$$
\langle f(A)x,y\rangle=\int f\,d\mu_{x,y}.
\tag{5.5}
$$

Define $E_A(B)$ weakly by $\langle E_A(B)x,y\rangle=\mu_{x,y}(B)$. Positivity of the function calculus and approximation of indicators show that $E_A(B)$ is an orthogonal projection, while measure additivity gives strong countable additivity. Taking $f(\lambda)=\lambda$ gives (5.1).

Simple Borel functions are now integrated as $\sum_jc_jE_A(B_j)$. Bounded pointwise approximation, together with dominated convergence for every $\mu_x$, extends the construction to bounded Borel functions and proves (5.2). If two projection-valued measures give (5.1), they give the same continuous functional calculus, hence the same scalar measures in (5.5), so they are equal. ∎

The support statement and the exact norm in (5.2) deserve emphasis. The spectral calculus does not see values of $f$ on a Borel set $B$ for which $E_A(B)=0$. This is the operator analogue of identifying measurable functions almost everywhere.

Several familiar constructions are now immediate. If $A\geq0$, the function $\sqrt\lambda$ defines the unique positive square root $A^{1/2}$. The absolute value of an arbitrary bounded operator is $|T|=(T^*T)^{1/2}$. If $A=A^*$ and $g$ is bounded real-valued, then $g(A)$ is self-adjoint. The spectral projection of an interval is

$$
E_A((a,b))=1_{(a,b)}(A).
$$

### 5.3 Borel functional calculus

The projection-valued integral obeys a scalar norm identity:

$$
\|f(A)x\|^2=\int |f(\lambda)|^2\,d\mu_x(\lambda)
\tag{5.6}
$$

for bounded Borel $f$. It is first checked for simple functions using orthogonality of spectral projections and then obtained by approximation. This formula is the engine of the unbounded calculus.

Spectral projections reduce every function of $A$:

$$
E_A(B)f(A)=f(A)E_A(B).
$$

Conversely, a bounded operator $S$ commutes with $A$ if and only if it commutes with every $E_A(B)$. One direction follows from the functional calculus. For the other, commuting with $A$ implies commuting with its resolvents, then with continuous functions of $A$, and finally with indicators by bounded pointwise approximation. For a nonnormal $S$, the direct reducing statement requires both $S$ and $S^*$ to commute; equivalently, $S$ commutes with every spectral projection.

For $x\in H$, the closed cyclic subspace generated by $A$ and $x$ is

$$
H_x=\overline{\{f(A)x:f\in C(\sigma(A))\}}.
$$

The map $f(A)x\mapsto f$ extends to a unitary $H_x\simeq L^2(\mu_x)$, under which $A$ becomes multiplication by $\lambda$. Decomposing a separable Hilbert space into countably many orthogonal cyclic subspaces yields the multiplication form of the bounded spectral theorem. Spectral measures and multiplication models are therefore two descriptions of the same structure: the former is coordinate-free, while the latter makes the diagonal nature visible.

### 5.4 The unbounded spectral theorem

Let $E$ be a projection-valued measure on $\mathbb R$. Define

$$
D(A)=\left\{x\in H:\int_{\mathbb R}\lambda^2\,d\mu_x(\lambda)<\infty\right\},
\tag{5.7}
$$

and for $x\in D(A)$ define $Ax=\int\lambda\,dE(\lambda)x$ as the norm limit of the truncated integrals over $[-n,n]$. Identity (5.6) shows that the truncations are Cauchy. It also proves that $A$ is closed. Testing the range of $A\pm i$ through the bounded functions $(\lambda\pm i)^{-1}$ proves that $A$ is self-adjoint.

**Theorem 5.2 (unbounded spectral theorem).** For every self-adjoint operator $A$ there is a unique projection-valued measure $E_A$ on $\mathbb R$ such that (5.7) holds and

$$
Ax=\int_{\mathbb R}\lambda\,dE_A(\lambda)x
\quad(x\in D(A)).
\tag{5.8}
$$

For a Borel function $f:\mathbb R\to\mathbb C$,

$$
D(f(A))=
\left\{x:\int|f(\lambda)|^2\,d\mu_x(\lambda)<\infty\right\},
\tag{5.9}
$$

and $f(A)x=\int f\,dE_Ax$. If $f$ is real-valued, $f(A)$ is self-adjoint; if $f$ is bounded, it is the bounded operator already described.

**Proof.** Apply the bounded spectral theorem to the Cayley transform $U=(A-i)(A+i)^{-1}$. The spectral measure of $U$ lives on the unit circle and has no atom at $1$. Pull it back under

$$
\lambda\longmapsto\frac{\lambda-i}{\lambda+i}.
$$

The inverse map is $\zeta\mapsto i(1+\zeta)/(1-\zeta)$, and its square-integrability domain is exactly $D(A)$ by the Cayley-transform formula. This produces (5.8). Uniqueness follows because the resolvent functions $(\lambda-z)^{-1}$ determine finite measures, and the resolvent of $A$ is already fixed. Formula (5.9) follows from truncation and (5.6). ∎

The calculus makes domain questions explicit. For Borel functions $f$ and $g$, one has

$$
f(A)g(A)\subset (fg)(A),
$$

and equality holds on the natural domain

$$
\{x\in D(g(A)):g(A)x\in D(f(A))\}.
$$

Writing an equality of unbounded products without its domain is unsafe.

For a semibounded $A\geq m$, spectral integration proves the assertion postponed in Chapter 4:

$$
D((A-m+1)^{1/2})
=\left\{x:\int(\lambda-m+1)\,d\mu_x(\lambda)<\infty\right\},
$$

and the right side is exactly the closed form domain associated with $A$. Moreover,

$$
\mathfrak a[x,y]
=\left\langle (A-m+1)^{1/2}x,(A-m+1)^{1/2}y\right\rangle
+(m-1)\langle x,y\rangle.
\tag{5.10}
$$

### 5.5 Multiplication models and spectral type

In the separable case, a self-adjoint operator is unitarily equivalent to multiplication by a real measurable function. More precisely, there are mutually singular measure classes, multiplicity spaces, and a unitary under which

$$
(Af)(x)=a(x)f(x),
\qquad
D(A)=\{f:af\in L^2\}.
$$

The cyclic construction in Section 5.3 proves this by an orthogonal induction: choose a cyclic vector, pass to the orthogonal complement of its reducing cyclic subspace, and repeat. Separability makes the process countable.

The scalar spectral measure splits uniquely into pure point, absolutely continuous, and singular continuous parts. Correspondingly,

$$
H=H_{\mathrm{pp}}\oplus H_{\mathrm{ac}}\oplus H_{\mathrm{sc}}.
$$

The pure-point part is the closed span of eigenvectors. The multiplication operator by $t$ on $L^2([0,1])$ is purely absolutely continuous. Multiplication by $t$ with respect to a continuous singular measure gives singular continuous spectrum: it has no eigenvectors, but its spectral measure is supported on a Lebesgue-null set. These examples show why “self-adjoint” does not mean “diagonalizable by an eigenbasis.” Compact resolvent is the hypothesis that will force the whole space to be pure point.

## 6. Compact operators and compact resolvents

Spectral measures describe every self-adjoint operator, but compactness determines when that description becomes a countable eigenfunction expansion. We first prove the compact self-adjoint theorem, then quantify compactness by singular values. Applying this bounded theory to a resolvent yields the discrete-spectrum criterion and the variational principles used to compare eigenvalues.

### 6.1 The compact self-adjoint spectral theorem

**Theorem 6.1.** Let $T\in\mathcal B(H)$ be compact and self-adjoint. Every nonzero spectral value is a real eigenvalue of finite multiplicity; the nonzero eigenvalues form a finite or countable set with no accumulation point except possibly $0$; and

$$
H=\ker T\oplus\bigoplus_{\lambda\neq0}^{2}\ker(T-\lambda I).
\tag{6.1}
$$

**Proof strategy.** Extract an eigenvector at the norm, remove its eigenspace, and repeat on the orthogonal complement. Compactness prevents a nonzero remainder and prevents infinite multiplicity.

For self-adjoint $T$,

$$
\|T\|=\sup_{\|x\|=1}|\langle Tx,x\rangle|.
\tag{6.2}
$$

This follows from polarization and the spectral-radius estimate for self-adjoint operators; it can also be proved directly by applying Cauchy--Schwarz to $T\pm\|T\|I$. Choose unit vectors $x_n$ for which the absolute values in (6.2) tend to $\|T\|$. After changing $T$ to $-T$ along a subsequence, assume $\langle Tx_n,x_n\rangle\to\|T\|$. Compactness gives a subsequence with $Tx_n\to y$. The identity

$$
\|(T-\|T\|I)x_n\|^2
=\|Tx_n\|^2-2\|T\|\langle Tx_n,x_n\rangle+\|T\|^2
$$

tends to zero, so $\|T\|x_n\to y$. If $T\neq0$, the $x_n$ converge to a unit vector $x$ and $Tx=\|T\|x$.

Eigenspaces for distinct eigenvalues are orthogonal. The orthogonal complement of an eigenspace is invariant under $T$, so the argument can be iterated. A nonzero eigenspace is finite-dimensional because $T$ restricts there to a nonzero scalar multiple of the identity. Likewise, infinitely many eigenvalues bounded away from zero would yield orthonormal eigenvectors $(e_n)$ such that $(Te_n)$ has no convergent subsequence, contradicting compactness.

Take a maximal orthonormal collection of eigenvectors for nonzero eigenvalues and let $M$ be its closed span. The complement $M^\perp$ is invariant. If $T$ were nonzero on it, the norm-attainment argument would produce another nonzero eigenvector there, contradicting maximality. Thus $T=0$ on $M^\perp$, which is contained in $\ker T$. This proves (6.1). ∎

The zero eigenspace can be infinite-dimensional, and $0$ need not be an eigenvalue. On $\ell^2$, the diagonal operator $Te_n=n^{-1}e_n$ is compact and injective; zero lies in its spectrum because the inverse is unbounded, but $\ker T=0$.

### 6.2 Singular values and polar decomposition

For $T\in\mathcal B(H,K)$, set $|T|=(T^*T)^{1/2}$. There is a unique partial isometry $U:H\to K$ whose initial space is $(\ker T)^\perp$, whose final space is $\overline{\operatorname{ran}T}$, and for which

$$
T=U|T|.
\tag{6.3}
$$

To construct it, define $U(|T|x)=Tx$. This is well-defined and isometric because

$$
\||T|x\|^2=\langle T^*Tx,x\rangle=\|Tx\|^2.
$$

Extend by continuity to $\overline{\operatorname{ran}|T|}=(\ker T)^\perp$ and set it equal to zero on $\ker T$. This is the polar decomposition.

If $T$ is compact, then $T^*T$ and $|T|$ are compact. The eigenvalues of $|T|$, repeated according to multiplicity and listed in decreasing order, are the singular values

$$
s_1(T)\geq s_2(T)\geq\cdots\geq0.
$$

Choosing orthonormal eigenvectors $e_n$ of $|T|$ for the positive singular values and setting $f_n=Ue_n$ gives the singular-value expansion

$$
Tx=\sum_n s_n(T)\langle x,e_n\rangle f_n,
\tag{6.4}
$$

where $(f_n)$ is orthonormal in $K$ and the series converges in norm. Truncation after $N$ terms gives a rank-$N$ operator $T_N$ with

$$
\|T-T_N\|=s_{N+1}(T).
\tag{6.5}
$$

The upper bound is immediate from (6.4). For the lower bound, any operator of rank at most $N$ has a nonzero kernel vector in the span of $e_1,\ldots,e_{N+1}$; evaluating the error on a unit such vector gives at least $s_{N+1}(T)$. Thus singular values measure optimal finite-rank approximation.

### 6.3 Compact resolvent and discrete spectrum

A self-adjoint operator $A$ has compact resolvent if $(A-z)^{-1}$ is compact for one, hence every, $z\notin\mathbb R$. This definition is formulated in terms of a bounded operator but has a complete spectral interpretation.

**Theorem 6.2.** For self-adjoint $A$, the following are equivalent.

1. $A$ has compact resolvent.
2. $E_A([-R,R])$ has finite rank for every $R>0$.
3. $H$ has an orthonormal basis $(e_n)$ of eigenvectors of $A$, every eigenspace is finite-dimensional, and the eigenvalues $(\lambda_n)$, repeated with multiplicity, satisfy $|\lambda_n|\to\infty$ if $H$ is infinite-dimensional.

**Proof.** By functional calculus,

$$
(A-i)^{-1}=\int\frac1{\lambda-i}\,dE_A(\lambda).
$$

If this operator is compact, its spectral projection for singular values at least $(R^2+1)^{-1/2}$ has finite rank. That projection is exactly $E_A([-R,R])$, up to an immaterial boundary choice. Thus (1) implies (2).

The projections $E_A([-R,R])$ increase strongly to $I$. Under (2), their ranges are finite-dimensional reducing subspaces. Diagonalizing $A$ on successive orthogonal differences produces an orthonormal eigenbasis. Finite rank on bounded intervals gives finite multiplicity and escape of eigenvalues to infinity, proving (3).

Under (3), $(A-i)^{-1}$ is diagonal with eigenvalues $(\lambda_n-i)^{-1}\to0$. Its finite-rank truncations converge in operator norm, so it is compact. ∎

If $A$ is bounded below, its eigenvalues can be listed increasingly,

$$
m\leq\lambda_1\leq\lambda_2\leq\cdots\to+\infty.
$$

The form domain then consists of $x=\sum_nc_ne_n$ such that

$$
\sum_n(\lambda_n-m+1)|c_n|^2<\infty.
$$

The unit ball for this weighted norm has uniformly small tails in $H$, hence is relatively compact. This proves the converse promised in Section 4.5:

**Corollary 6.3.** For a semibounded self-adjoint operator, compact resolvent is equivalent to compactness of the form-domain inclusion into $H$.

### 6.4 Variational eigenvalue principles

Let $A$ be semibounded with compact resolvent, and let $\mathfrak a$ be its form. The ordered eigenvalues are determined without solving the eigenvalue equation.

**Theorem 6.4 (min--max principle).** For $n\geq1$,

$$
\lambda_n
=\min_{\substack{L\subset V\\ \dim L=n}}
\ \max_{0\neq u\in L}
\frac{\mathfrak a[u]}{\|u\|^2}
=\max_{\substack{M\subset H\\ \dim M=n-1}}
\ \min_{\substack{0\neq u\in V\\u\perp M}}
\frac{\mathfrak a[u]}{\|u\|^2}.
\tag{6.6}
$$

**Proof.** Expand $u=\sum_jc_je_j$. Then

$$
\frac{\mathfrak a[u]}{\|u\|^2}
=\frac{\sum_j\lambda_j|c_j|^2}{\sum_j|c_j|^2}.
$$

On $L_0=\operatorname{span}(e_1,\ldots,e_n)$ this quotient is at most $\lambda_n$, giving one inequality in the first formula. Every $n$-dimensional $L$ contains a nonzero vector orthogonal to $e_1,\ldots,e_{n-1}$; its quotient is at least $\lambda_n$, giving the reverse inequality. The second formula is proved by the dual dimension argument: for $M=\operatorname{span}(e_1,\ldots,e_{n-1})$ the lower bound is $\lambda_n$, while any $(n-1)$-dimensional $M$ has a nonzero orthogonal vector in $\operatorname{span}(e_1,\ldots,e_n)$. ∎

The principle has two major consequences. If two closed forms on the same domain satisfy $\mathfrak a[u]\leq\mathfrak b[u]$, then their ordered eigenvalues satisfy $\lambda_n(A)\leq\lambda_n(B)$. If $V_1\subset V_2$ and the forms agree on $V_1$, restricting the domain raises eigenvalues. This is why Dirichlet boundary conditions have eigenvalues no smaller than Neumann boundary conditions.

Multiplicity is also visible variationally. If

$$
\lambda_{n-1}<\lambda_n=\cdots=\lambda_{n+r-1}<\lambda_{n+r},
$$

then the eigenspace has dimension $r$. Small perturbations of the form move the ordered eigenvalues continuously under suitable relative bounds, even when individual eigenvectors cannot be chosen continuously through a multiple eigenvalue.

### 6.5 Spectral functions and counting

For a semibounded compact-resolvent operator, a Borel function $f(A)$ is compact exactly when $f(\lambda_n)\to0$, after ignoring finite-dimensional eigenspaces. It is finite rank if $f$ vanishes on all but finitely many eigenvalues. Two functions are especially important:

$$
e^{-tA},\qquad (A+c)^{-s}.
$$

After shifting $A\geq0$, the heat operator $e^{-tA}$ is compact for every $t>0$, and

$$
e^{-tA}x=\sum_ne^{-t\lambda_n}\langle x,e_n\rangle e_n.
$$

Compactness alone does not imply trace class: the diagonal operator with eigenvalues $1/n$ is compact but has divergent eigenvalue sum. The exact trace criteria will be developed in Chapter 8.

Define the counting function

$$
N_A(\Lambda)=\operatorname{rank}E_A(( -\infty,\Lambda])
=\#\{n:\lambda_n\leq\Lambda\},
$$

counting multiplicity. Then for nonnegative $A$ and $t>0$, whenever either side is finite,

$$
\sum_ne^{-t\lambda_n}
=\int_{[0,\infty)}e^{-t\lambda}\,dN_A(\lambda)
=t\int_0^\infty e^{-t\lambda}N_A(\lambda)\,d\lambda.
\tag{6.7}
$$

The last equality is Stieltjes integration by parts. It translates eigenvalue growth into heat-trace decay. For example, a bound $N_A(\Lambda)\leq C(1+\Lambda)^d$ makes $e^{-tA}$ trace class and gives a bound of order $t^{-d}$ as $t\downarrow0$. This quantitative bridge will later justify spectral trace expansions.

## 7. Hilbert--Schmidt operators and kernels

The first summability refinement of compactness is quadratic. It is strong enough to identify operators with $L^2$ kernels and weak enough to arise naturally from smoothing estimates. This chapter establishes the basis-free ideal, its exact kernel realization, and the composition estimates that prepare the trace class.

### 7.1 A square-summable operator ideal

Compactness says that singular values tend to zero but does not measure how fast. The first quantitative ideal imposes square summability. An operator $T\in\mathcal B(H,K)$ is Hilbert--Schmidt if, for one orthonormal basis $(e_n)$ of $H$,

$$
\|T\|_2^2=\sum_n\|Te_n\|^2<\infty.
\tag{7.1}
$$

The notation anticipates that this number is basis-independent. Rank-one operators provide the normalization:

$$
\|u\otimes v\|_2=\|u\|\|v\|.
$$

For a finite-rank singular-value expansion $T=\sum_js_j f_j\otimes e_j$, orthogonality gives

$$
\|T\|_2^2=\sum_js_j^2.
$$

The general result will follow by approximation.

### 7.2 Basis independence and ideal estimates

**Theorem 7.1.** For $T\in\mathcal B(H,K)$ and any orthonormal bases $(e_n)$ of $H$ and $(f_m)$ of $K$,

$$
\sum_n\|Te_n\|^2
=\sum_{m,n}|\langle Te_n,f_m\rangle|^2
=\sum_m\|T^*f_m\|^2,
\tag{7.2}
$$

with equality allowed to be $+\infty$. Consequently the Hilbert--Schmidt property and norm are basis-independent, and $\|T^*\|_2=\|T\|_2$.

**Proof.** Parseval in $K$ gives

$$
\|Te_n\|^2=\sum_m|\langle Te_n,f_m\rangle|^2.
$$

All summands are nonnegative, so the order of the two sums may be exchanged. Since $\langle Te_n,f_m\rangle=\langle e_n,T^*f_m\rangle$, Parseval in $H$ gives the last expression. ∎

The Hilbert--Schmidt operators form a Hilbert space with inner product

$$
\langle S,T\rangle_2
=\sum_n\langle Se_n,Te_n\rangle.
\tag{7.3}
$$

Absolute convergence follows from Cauchy--Schwarz, and basis independence follows by the same double-Parseval argument. Completeness can be proved by observing that a Cauchy sequence in this norm converges on every basis vector, defining a limit operator, and then using Fatou's lemma and tail estimates to get convergence in $\|\cdot\|_2$.

**Proposition 7.2 (ideal estimates).** If $T$ is Hilbert--Schmidt and $A,B$ are bounded with compatible source and target, then

$$
\|ATB\|_2\leq\|A\|\,\|T\|_2\,\|B\|.
\tag{7.4}
$$

In particular, Hilbert--Schmidt operators form a two-sided operator ideal.

**Proof.** The left multiplication estimate follows immediately from (7.1). For right multiplication, let $(e_n)$ and $(f_m)$ be orthonormal bases of the source and target. Double Parseval gives

$$
\sum_n\|TB e_n\|^2
=\sum_{m,n}|\langle Be_n,T^*f_m\rangle|^2
=\sum_m\|B^*T^*f_m\|^2
\leq\|B\|^2\|T\|_2^2.
$$

The displayed identities are first read for finite partial sums and then passed to the limit by monotone convergence. ∎

Every Hilbert--Schmidt operator is compact. Let $P_N$ project onto the span of the first $N$ basis vectors. Then $TP_N$ has finite rank and

$$
\|T-TP_N\|^2
\leq\|T-TP_N\|_2^2
=\sum_{n>N}\|Te_n\|^2\longrightarrow0.
$$

The inequality $\|S\|\leq\|S\|_2$ follows by expanding a unit vector in the chosen basis and applying Cauchy--Schwarz. The converse fails: $\operatorname{diag}(n^{-1/2})$ on $\ell^2$ is compact but not Hilbert--Schmidt.

For a compact $T$, the singular-value expansion gives the exact criterion

$$
T\text{ is Hilbert--Schmidt}
\quad\Longleftrightarrow\quad
\sum_ns_n(T)^2<\infty,
\qquad
\|T\|_2^2=\sum_ns_n(T)^2.
\tag{7.5}
$$

### 7.3 Integral kernels

Let $(X,\mu)$ and $(Y,\nu)$ be sigma-finite measure spaces with separable $L^2$ spaces. Given

$$
K\in L^2(X\times Y,\mu\times\nu),
$$

define, for almost every $x$,

$$
(T_Kf)(x)=\int_YK(x,y)f(y)\,d\nu(y).
\tag{7.6}
$$

Cauchy--Schwarz in $y$ gives

$$
|T_Kf(x)|^2
\leq\left(\int_Y|K(x,y)|^2d\nu(y)\right)\|f\|_2^2.
$$

Integrating in $x$ proves that $T_K:L^2(Y)\to L^2(X)$ is bounded and $\|T_K\|\leq\|K\|_{L^2(X\times Y)}$.

**Theorem 7.3 (kernel theorem for Hilbert--Schmidt operators).** The map

$$
K\longmapsto T_K
$$

is a unitary isomorphism from $L^2(X\times Y)$ onto the Hilbert space of Hilbert--Schmidt operators $L^2(Y)\to L^2(X)$. In particular,

$$
\|T_K\|_2^2=\int_{X\times Y}|K(x,y)|^2\,d\mu(x)d\nu(y).
\tag{7.7}
$$

**Proof.** Let $(e_n)$ be an orthonormal basis of $L^2(Y)$. Then $(\overline{e_n})$ is also an orthonormal basis. For almost every $x$, expanding the function $y\mapsto K(x,y)$ in the latter basis gives

$$
\sum_n|T_Ke_n(x)|^2=\int_Y|K(x,y)|^2d\nu(y),
$$

because the coefficient of $\overline{e_n}$ is $\int_YK(x,y)e_n(y)d\nu(y)=T_Ke_n(x)$. Integrating and exchanging nonnegative sums proves (7.7).

Conversely, let $T$ be Hilbert--Schmidt and choose an orthonormal basis $(e_n)$ of $L^2(Y)$. The series

$$
K(x,y)=\sum_n(Te_n)(x)\overline{e_n(y)}
\tag{7.8}
$$

converges in $L^2(X\times Y)$ because its summands are orthogonal there and the sum of their squared norms is $\|T\|_2^2$. For a finite linear combination $f$ of the $e_n$, direct substitution shows $T_Kf=Tf$. Density and boundedness extend the equality to every $f\in L^2(Y)$. Uniqueness follows from (7.7). ∎

Formula (7.8) is an $L^2$ identity, not a pointwise expansion. This distinction matters whenever a diagonal value is contemplated.

The adjoint kernel is

$$
K^*(y,x)=\overline{K(x,y)}.
\tag{7.9}
$$

Fubini's theorem proves $T_K^*=T_{K^*}$. Thus $T_K$ on $L^2(X)$ is self-adjoint exactly when $K(x,y)=\overline{K(y,x)}$ almost everywhere.

**Example.** On the circle with normalized measure, a convolution kernel $K(x,y)=k(x-y)$ is Hilbert--Schmidt precisely when $k\in L^2$. The Fourier basis diagonalizes it, and its eigenvalues are the Fourier coefficients $\widehat k(n)$. Parseval becomes

$$
\|T_K\|_2^2=\sum_{n\in\mathbb Z}|\widehat k(n)|^2=\|k\|_2^2.
$$

This is a concrete meeting point of the kernel and spectral descriptions.

### 7.4 Composition of kernels

If $K_1\in L^2(X\times Y)$ and $K_2\in L^2(Y\times Z)$, then

$$
L(x,z)=\int_YK_1(x,y)K_2(y,z)\,d\nu(y)
\tag{7.10}
$$

is defined for almost every $(x,z)$. Cauchy--Schwarz shows

$$
|L(x,z)|
\leq \|K_1(x,\cdot)\|_{L^2(Y)}
\|K_2(\cdot,z)\|_{L^2(Y)}.
$$

Set

$$
a(x)=\|K_1(x,\cdot)\|_{L^2(Y)},
\qquad
b(z)=\|K_2(\cdot,z)\|_{L^2(Y)}.
$$

Then $a\in L^2(X)$, $b\in L^2(Z)$, and $|L(x,z)|\leq a(x)b(z)$. Hence $L\in L^2(X\times Z)$ and

$$
\|L\|_2\leq\|K_1\|_2\|K_2\|_2.
$$

On a dense class of bounded functions supported on sets of finite measure, Fubini gives

$$
T_{K_1}T_{K_2}=T_L,
$$

and boundedness extends the equality to all of $L^2(Z)$. Operator-theoretically the product is better still: it is trace class. This improvement from two square sums to one absolute sum is the subject of the next chapter.

## 8. Trace-class operators and trace identities

A trace must sum infinitely many diagonal contributions without depending on the chosen coordinates. Summability of singular values is exactly the condition that supports this operation. The chapter builds the trace from positive operators, proves the factorization and cyclic identities that make it usable, and identifies the topology in which infinite-dimensional matrix arguments remain valid.

### 8.1 Summable singular values

A compact operator $T:H\to K$ is trace class if

$$
\|T\|_1=\sum_ns_n(T)<\infty.
\tag{8.1}
$$

Equivalently, $|T|$ has summable eigenvalues. The inclusions among the main ideals are

$$
\mathcal B_1(H,K)\subset\mathcal B_2(H,K)
\subset\mathcal K(H,K)\subset\mathcal B(H,K),
$$

and

$$
\|T\|\leq\|T\|_2\leq\|T\|_1.
$$

Each inclusion is strict in infinite dimension. Diagonal sequences $n^{-2}$, $n^{-1}$, and $n^{-1/2}$ provide immediate examples at the boundaries.

Trace class has a useful factorization characterization.

**Theorem 8.1.** An operator $T:H\to K$ is trace class if and only if it can be written

$$
T=AB
$$

through some Hilbert space $L$, with $B:H\to L$ and $A:L\to K$ Hilbert--Schmidt. Moreover,

$$
\|T\|_1=inf_{T=AB}\|A\|_2\|B\|_2.
\tag{8.2}
$$

**Proof.** If $T=U|T|$ is trace class, take $B=|T|^{1/2}$ and $A=U|T|^{1/2}$. Both are Hilbert--Schmidt and

$$
\|A\|_2^2=\|B\|_2^2=\sum_ns_n(T)=\|T\|_1.
$$

Conversely, choose orthonormal bases and apply Cauchy--Schwarz to finite-rank compressions of $AB$. The resulting singular-value inequality gives

$$
\|AB\|_1\leq\|A\|_2\|B\|_2.
\tag{8.3}
$$

This proves trace class and one direction of (8.2); the polar factorization gives equality in the infimum. ∎

The trace class is a two-sided ideal. Singular-value approximation or the factorization theorem gives

$$
\|ATB\|_1\leq\|A\|\,\|T\|_1\,\|B\|.
\tag{8.4}
$$

It is complete in the trace norm. Finite-rank operators are dense: truncating a singular-value expansion gives

$$
\|T-T_N\|_1=\sum_{n>N}s_n(T)\to0.
\tag{8.5}
$$

### 8.2 The operator trace

For a positive trace-class operator $T$, define

$$
\operatorname{tr}(T)=\sum_n\langle Te_n,e_n\rangle
\tag{8.6}
$$

for an orthonormal basis $(e_n)$. This is independent of the basis. Indeed, if $(f_m)$ is another basis and $T^{1/2}$ is Hilbert--Schmidt, then double Parseval gives

$$
\sum_n\langle Te_n,e_n\rangle
=\sum_n\|T^{1/2}e_n\|^2
=\|T^{1/2}\|_2^2
=\sum_m\langle Tf_m,f_m\rangle.
$$

For a general trace-class $T$, the diagonal series is absolutely convergent. From the polar decomposition $T=U|T|$,

$$
|\langle Te_n,e_n\rangle|
=|\langle |T|^{1/2}e_n,|T|^{1/2}U^*e_n\rangle|.
$$

Cauchy--Schwarz after summation bounds the absolute sum by $\|T\|_1$. We define

$$
\operatorname{tr}(T)=\sum_n\langle Te_n,e_n\rangle.
\tag{8.7}
$$

Basis independence follows either by polarizing the positive case or by approximating $T$ in trace norm by finite-rank operators. The estimate

$$
|\operatorname{tr}(T)|\leq\|T\|_1
\tag{8.8}
$$

shows that the trace is continuous in trace norm.

For rank one,

$$
\operatorname{tr}(u\otimes v)=\langle u,v\rangle.
\tag{8.9}
$$

Indeed, Parseval gives $\sum_n\langle e_n,v\rangle\langle u,e_n\rangle=\langle u,v\rangle$. Thus the infinite-dimensional trace has exactly the finite-dimensional normalization.

### 8.3 Cyclicity and ideal identities

The most important trace identity is cyclicity in the range where the products are trace class.

**Theorem 8.2.** If $T:H\to K$ is trace class and $B:K\to H$ is bounded, then

$$
\operatorname{tr}_H(BT)=\operatorname{tr}_K(TB).
\tag{8.10}
$$

In particular, for $T\in\mathcal B_1(H)$ and $B\in\mathcal B(H)$,

$$
\operatorname{tr}(BT)=\operatorname{tr}(TB),
\qquad
|\operatorname{tr}(BT)|\leq\|B\|\|T\|_1.
\tag{8.11}
$$

**Proof.** For rank one $T=u\otimes v$, both traces equal $\langle Bu,v\rangle$. Linearity proves the formula for finite rank. Choose finite-rank $T_n\to T$ in trace norm. The ideal estimate gives $BT_n\to BT$ and $T_nB\to TB$ in trace norm, and trace continuity passes the identity to the limit. ∎

If $S,T$ are Hilbert--Schmidt, then $S^*T$ is trace class and

$$
\operatorname{tr}(S^*T)
=\sum_n\langle Te_n,Se_n\rangle
=\langle T,S\rangle_2.
\tag{8.12}
$$

Thus the Hilbert--Schmidt inner product is itself a trace. The estimate

$$
|\operatorname{tr}(S^*T)|\leq\|S\|_2\|T\|_2
\tag{8.13}
$$

is simply Cauchy--Schwarz in the Hilbert space of Hilbert--Schmidt operators.

Commutators have trace zero whenever one factor is trace class and the other bounded:

$$
\operatorname{tr}([B,T])=0.
$$

The qualification is essential. In infinite dimension the identity can be an algebraic commutator of unbounded or merely bounded expressions for which neither product is trace class; cyclicity cannot then be invoked. Trace manipulations are legitimate only after ideal membership has been established.

Unitary invariance follows at once:

$$
\operatorname{tr}(UTU^*)=\operatorname{tr}(T),
\qquad
\|UTV\|_1=\|T\|_1
$$

for unitaries $U,V$. More generally, if $P$ is an orthogonal projection and $T\geq0$ is trace class, then

$$
\operatorname{tr}(PTP)=\operatorname{tr}(T^{1/2}PT^{1/2})leq\operatorname{tr}(T).
\tag{8.14}
$$

This monotonicity controls traces under increasing finite-dimensional compression.

### 8.4 Positive operators, projections, and eigenvalue sums

For $T\geq0$, trace class is equivalent to finiteness of the diagonal sum in any orthonormal basis, and

$$
\operatorname{tr}(T)=\sum_ns_n(T).
\tag{8.15}
$$

For self-adjoint trace-class $T$, write $T=T_+-T_-$ using the positive and negative parts from the spectral calculus. Both parts are trace class and

$$
\operatorname{tr}(T)=\operatorname{tr}(T_+)-\operatorname{tr}(T_-)
=\sum_n\lambda_n(T),
\tag{8.16}
$$

where nonzero eigenvalues are repeated with algebraic, equivalently geometric, multiplicity and the series converges absolutely. This follows directly by choosing an orthonormal eigenbasis for the compact self-adjoint operator.

For a general, not necessarily normal, trace-class operator, the equality of trace with the absolutely convergent sum of algebraic eigenvalues is deeper because eigenvectors need not be orthogonal and may not span the space. The equality is true, but the automorphic applications developed here require only self-adjoint spectral functions and traces of smoothing operators computed through kernels. We will not use the general eigenvalue-sum theorem without first reducing to those controlled settings.

An orthogonal projection $P$ is trace class exactly when it has finite rank, and then

$$
\operatorname{tr}(P)=\operatorname{rank}P.
\tag{8.17}
$$

Indeed, every nonzero singular value of $P$ is $1$. This identity turns the trace of a spectral projection into eigenvalue multiplicity.

If $A$ has compact resolvent with eigenbasis $(e_n)$ and $f$ is a Borel function on its spectrum, then

$$
f(A)\in\mathcal B_1(H)
\quad\Longleftrightarrow\quad
\sum_n|f(\lambda_n)|<\infty,
\tag{8.18}
$$

and in that case

$$
\operatorname{tr}(f(A))=\sum_nf(\lambda_n).
\tag{8.19}
$$

This includes heat traces and sufficiently high resolvent powers. It is the most direct spectral trace identity in the book.

### 8.5 Trace-norm convergence

Operator-norm convergence does not preserve traces. Let $P_N$ project onto the first $N$ coordinates of $\ell^2$ and set $T_N=N^{-1}P_N$. Then $\|T_N\|=N^{-1}\to0$, but $\operatorname{tr}(T_N)=1$. Trace norm is the correct topology.

If $T_n\to T$ in trace norm, then

$$
\operatorname{tr}(T_n)\to\operatorname{tr}(T),
$$

and multiplication by a uniformly bounded family preserves this convergence. A particularly useful criterion applies to positive operators.

**Proposition 8.3.** Suppose $0\leq T_n\leq T_{n+1}\leq T$ in quadratic-form order and $T$ is trace class. If $T_nx\to Tx$ for every $x$, then

$$
\|T-T_n\|_1=\operatorname{tr}(T-T_n)\longrightarrow0.
$$

**Proof.** In an orthonormal basis, each diagonal term $\langle(T-T_n)e_j,e_j\rangle$ decreases to zero and is dominated by $\langle Te_j,e_j\rangle$. Dominated convergence for the counting measure gives convergence of the sums. Positivity identifies trace norm with trace. ∎

Finite-rank compressions give the standard application. If $P_n\uparrow I$ strongly and $T$ is trace class, then

$$
\|T-P_nTP_n\|_1\to0.
\tag{8.20}
$$

For positive $T$, first handle $T^{1/2}P_nT^{1/2}$ by Proposition 8.3; the remaining comparison follows by factorization and the Hilbert--Schmidt norm. For general $T$, use the polar decomposition. This is often the safest way to justify passage from finite matrix identities to infinite-dimensional trace identities.

## 9. Diagonal kernels and spectral traces

Kernel notation tempts one to copy the finite-matrix formula “trace equals integral of the diagonal.” On a continuous measure space that diagonal may not even be defined. This chapter separates invalid formal restriction from three valid arguments: contraction of two square-integrable kernels, positivity with continuity, and spectral smoothing through heat or resolvent operators.

### 9.1 Why an arbitrary kernel has no diagonal

If $K\in L^2(X\times X)$, then $K$ is an equivalence class modulo sets of product measure zero. For a nonatomic measure, the diagonal

$$
\Delta=\{(x,x):x\in X\}
$$

has product measure zero. One may therefore alter $K$ arbitrarily on $\Delta$ without changing either its $L^2$ class or its operator. The expression $\int_XK(x,x)d\mu(x)$ is not defined by an arbitrary Hilbert--Schmidt kernel.

There is a second obstruction: a Hilbert--Schmidt operator need not be trace class. On $\ell^2$, the diagonal operator $Te_n=n^{-3/4}e_n$ is Hilbert--Schmidt because $\sum n^{-3/2}<\infty$, but its diagonal sum diverges. Thus even a canonical matrix diagonal need not be integrable.

A valid diagonal trace formula requires extra structure. We will use three reliable mechanisms:

1. express the operator as a product of two Hilbert--Schmidt operators and integrate the resulting two-kernel contraction;
2. use a positive continuous kernel, for which positivity controls the diagonal;
3. prove enough smoothing that the operator is trace class and its kernel has a canonical continuous representative.

### 9.2 The Hilbert--Schmidt product formula

Let $S=T_K$ and $T=T_L$ be Hilbert--Schmidt operators on $L^2(X)$ with kernels $K,L\in L^2(X\times X)$. Their product is trace class, and

$$
\operatorname{tr}(ST)
=\int_{X\times X}K(x,y)L(y,x)\,d\mu(y)d\mu(x).
\tag{9.1}
$$

The integrand is absolutely integrable by Cauchy--Schwarz:

$$
\int|K(x,y)L(y,x)|
\leq\|K\|_2\|L\|_2.
$$

To prove the identity, choose an orthonormal basis $(e_n)$. Equation (8.12), first for finite-rank kernels and then by $L^2$ approximation, gives

$$
\operatorname{tr}(ST)
=\sum_n\langle Te_n,S^*e_n\rangle.
$$

Expanding with the kernel theorem and applying Fubini yields (9.1).

The formula is often described as integration of the diagonal of the composite kernel

$$
M(x,z)=\int_XK(x,y)L(y,z)\,d\mu(y).
$$

What makes $M(x,x)$ legitimate is not a restriction of an arbitrary $L^2$ function to the diagonal. It is the explicitly defined contraction

$$
M(x,x)=\int_XK(x,y)L(y,x)\,d\mu(y),
$$

which lies in $L^1(X)$ by Fubini and Cauchy--Schwarz. This distinction prevents a common but serious misuse of kernel notation.

Taking $S=T^*$ in (9.1) recovers

$$
\operatorname{tr}(T^*T)=\|T\|_2^2=\int_{X\times X}|L(x,y)|^2d\mu(x)d\mu(y).
\tag{9.2}
$$

### 9.3 Positive continuous kernels

Continuity can select a canonical representative, while positivity forces summability.

**Theorem 9.1 (positive-kernel trace theorem).** Let $X$ be a compact Hausdorff space with a finite Borel measure of full support. Suppose $K\in C(X\times X)$, $K(y,x)=\overline{K(x,y)}$, and the integral operator $T_K$ on $L^2(X)$ is positive. Then $T_K$ is trace class and

$$
\operatorname{tr}(T_K)=\int_XK(x,x)\,d\mu(x).
\tag{9.3}
$$

If $(\lambda_n,\phi_n)$ are its positive eigenpairs, with the eigenfunctions represented continuously, then

$$
K(x,y)=\sum_n\lambda_n\phi_n(x)\overline{\phi_n(y)},
\tag{9.4}
$$

with uniform convergence on $X\times X$.

**Proof strategy.** The continuous kernel makes $T_K$ compact and sends $L^2$ boundedly into $C(X)$. Positivity and the compact spectral theorem give nonnegative eigenvalues and an $L^2$ eigenfunction expansion. For the partial kernels

$$
K_N(x,y)=\sum_{n\leq N}\lambda_n\phi_n(x)\overline{\phi_n(y)},
$$

positivity of the remainder implies $0\leq K_N(x,x)\leq K(x,x)$. A Cauchy--Schwarz inequality for positive kernels,

$$
|R_N(x,y)|^2\leq R_N(x,x)R_N(y,y),
$$

reduces uniform convergence on $X\times X$ to uniform convergence on the diagonal. Compactness and equicontinuity give convergence of the continuous diagonal remainders; monotonicity then upgrades it to uniform convergence. Integrating the increasing diagonal sums yields

$$
\sum_n\lambda_n
=\lim_N\int_XK_N(x,x)d\mu(x)
=\int_XK(x,x)d\mu(x)<\infty.
$$

This proves trace class, (9.3), and uniform convergence in (9.4). ∎

Both positivity and regularity carry real weight. A continuous kernel can define a non-trace-class operator, and an almost-everywhere kernel for a positive trace-class operator need not have a canonically defined diagonal. The theorem is powerful precisely because its hypotheses remove both obstructions at once.

### 9.4 Heat kernels and resolvent powers

Let $A\geq0$ be self-adjoint with compact resolvent. Spectrally,

$$
e^{-tA}=\sum_ne^{-t\lambda_n}(e_n\otimes e_n).
\tag{9.5}
$$

If $\sum_ne^{-t\lambda_n}<\infty$, then $e^{-tA}$ is positive trace class and

$$
\operatorname{tr}(e^{-tA})=\sum_ne^{-t\lambda_n}.
\tag{9.6}
$$

Suppose geometric analysis also produces a continuous heat kernel $K_t(x,y)$. The semigroup identity gives

$$
K_t(x,y)=\int_XK_{t/2}(x,z)K_{t/2}(z,y)d\mu(z),
$$

and self-adjointness gives $K_{t/2}(z,y)=\overline{K_{t/2}(y,z)}$. Hence

$$
K_t(x,x)=\int_X|K_{t/2}(x,z)|^2d\mu(z)\geq0.
$$

If $K_{t/2}\in L^2(X\times X)$, formula (9.1) yields

$$
\operatorname{tr}(e^{-tA})
=\int_XK_t(x,x)d\mu(x).
\tag{9.7}
$$

Combining (9.6) and (9.7) gives the basic spectral-geometric identity

$$
\sum_ne^{-t\lambda_n}
=\int_XK_t(x,x)d\mu(x).
\tag{9.8}
$$

The same pattern applies to resolvent powers. If

$$
\sum_n(1+\lambda_n)^{-s}<\infty,
$$

then $(I+A)^{-s}$ is trace class. If half the power is Hilbert--Schmidt with kernel $L_{s/2}$, then

$$
\operatorname{tr}((I+A)^{-s})
=\int_{X\times X}|L_{s/2}(x,y)|^2d\mu(x)d\mu(y).
\tag{9.9}
$$

These factorizations are especially valuable on noncompact spaces, where pointwise diagonal estimates may be difficult but square-integrability of a half-power kernel can be proved by energy methods.

## 10. Orthogonal decompositions and commuting actions

Spectral theory becomes representation theory when symmetries preserve the operator. The preservation must be strong enough to respect domains and resolvents; once it is, the Hilbert space breaks into reducing pieces. This chapter develops the direct-sum bookkeeping and explains how compact types and finite spectral windows force finite multiplicity and simultaneous diagonalization.

### 10.1 Reducing subspaces

An orthogonal decomposition becomes useful for an operator only when it respects the domain. Let $A$ be self-adjoint and $M\subset H$ closed. The following are equivalent.

1. $M$ reduces $A$.
2. $P_M$ commutes with one resolvent $(A-z)^{-1}$.
3. $P_M$ commutes with every spectral projection $E_A(B)$.

To pass from (1) to (2), solve $(A-z)x=y$ separately in $M$ and $M^\perp$. From (2), the resolvent identity gives commutation with all resolvents; uniqueness of the spectral measure then gives (3). From (3), the domain formula

$$
\int\lambda^2d\mu_{P_Mx}
\leq\int\lambda^2d\mu_x
$$

shows that $P_MD(A)\subset D(A)$, and spectral integration gives $AP_M=P_MA$ on $D(A)$.

If $M$ is merely invariant, $M^\perp$ need not be invariant. For a bounded self-adjoint operator, invariance of $M$ does imply reduction: if $x\in M^\perp$ and $m\in M$, then

$$
\langle Tx,m\rangle=\langle x,Tm\rangle=0.
$$

For an unbounded operator, the same calculation is insufficient unless domains and projected domains are controlled. Resolvent commutation is the safest formulation.

If a bounded operator $T$ commutes with every $E_A(B)$, it preserves $D(A)$ and commutes with $A$. If only $TA\subset AT$ is known on a small core, one must still prove that $T$ preserves the closed domain before drawing this conclusion. This domain check is frequently the decisive analytic step for symmetry actions on differential operators.

### 10.2 Countable Hilbert sums

Let $H=\bigoplus_j^2H_j$, and let $A_j$ be self-adjoint on $H_j$. The orthogonal sum operator is

$$
A=\bigoplus_jA_j,
$$

with domain

$$
D(A)=\left\{(x_j):x_j\in D(A_j),
\sum_j\|A_jx_j\|^2<\infty\right\}.
\tag{10.1}
$$

It is self-adjoint. Indeed, for $z\notin\mathbb R$, the coordinate resolvents satisfy the uniform bound $\|(A_j-z)^{-1}\|\leq|\operatorname{Im}z|^{-1}$. Their Hilbert sum is therefore a bounded inverse for $A-z$. The resolvent criterion proves self-adjointness.

Its spectral measure is the coordinate sum

$$
E_A(B)=\bigoplus_jE_{A_j}(B),
$$

and $f(A)=\bigoplus_jf(A_j)$ with the square-summability domain dictated by (5.9). If each $A_j$ has compact resolvent, the direct sum need not: compactness additionally requires

$$
\sup_{\lambda\in\sigma(A_j)}\frac1{|\lambda-i|}\longrightarrow0
$$

along the summands, in the sense that only finitely many $j$ contribute spectral values in any bounded interval. Otherwise one can choose a unit vector from each summand with uniformly bounded spectral energy, producing a noncompact resolvent image.

For bounded operators $T_j\in\mathcal B(H_j)$,

$$
\bigoplus_jT_j\text{ is bounded}
\quad\Longleftrightarrow\quad
\sup_j\|T_j\|<\infty.
$$

It is compact exactly when every $T_j$ is compact and the finite-rank approximation can be made uniform, equivalently $\|T_j\|\to0$ after discarding finitely many indices. It is trace class exactly when each $T_j$ is trace class and

$$
\sum_j\|T_j\|_1<\infty,
\tag{10.2}
$$

in which case

$$
\operatorname{tr}\left(\bigoplus_jT_j\right)=\sum_j\operatorname{tr}(T_j)
\tag{10.3}
$$

with absolute convergence. These criteria are what permit a trace to be reorganized by spectral packets.

### 10.3 Commuting symmetries and finite multiplicity

Let a compact group $K$ act unitarily on $H$. For an irreducible representation $\tau$ of $K$, normalized Haar integration defines the isotypic projection

$$
P_\tau=d_\tau\int_K\overline{\chi_\tau(k)}\,U(k)\,dk,
\tag{10.4}
$$

where $d_\tau=\dim\tau$. Character orthogonality proves $P_\tau^2=P_\tau=P_\tau^*$, projections for distinct $\tau$ are orthogonal, and

$$
H=\bigoplus_{\tau\in\widehat K}^2H(\tau).
\tag{10.5}
$$

For second-countable $K$, only countably many types occur in a separable $H$.

Suppose a self-adjoint $A$ commutes with $U(k)$ in the strong domain sense. Then every $H(\tau)$ reduces $A$. If $A|_{H(\tau)}$ has compact resolvent, each joint space

$$
H(\tau,\lambda)=H(\tau)\cap\ker(A-\lambda)
\tag{10.6}
$$

is finite-dimensional. Any bounded operator commuting with both $A$ and the $K$-action preserves these spaces. Thus an infinite-dimensional harmonic-analysis problem is reduced, one spectral value and one compact type at a time, to finite-dimensional linear algebra.

This yields a useful multiplicity principle. Suppose a unitary representation decomposes as a Hilbert sum

$$
H\simeq\bigoplus_{\pi}^{2}m(\pi)H_\pi,
$$

and a central self-adjoint operator acts on the $\tau$-isotypic part of $H_\pi$ by the scalar $\lambda_{\pi,\tau}$. If $A|_{H(\tau)}$ has compact resolvent, then

$$
\sum_{\substack{\pi:\lambda_{\pi,\tau}=\lambda}}
m(\pi)\dim H_\pi(\tau)<\infty.
\tag{10.7}
$$

In particular, every occurring $\pi$ containing $\tau$ has finite multiplicity, and only finitely many such contributions can share a fixed bounded spectral window. Compact resolvent is therefore the analytic origin of finite automorphic multiplicity; representation theory identifies and organizes the finite-dimensional pieces it produces.

### 10.4 Simultaneous spectral organization

A commuting family of bounded normal operators on a finite-dimensional Hilbert space has a common orthonormal eigenbasis. The proof is inductive: choose an eigenspace of one operator; commutation with that operator and its adjoint makes the eigenspace reducing for every other member; diagonalize on it and on its complement.

Applied to the finite-dimensional spaces (10.6), this diagonalizes commuting Hecke-type or symmetry operators without requiring those operators to be compact on all of $H$. If $T_\alpha$ commute with $A$ and with one another, and each $T_\alpha$ is normal on $H(\tau,\lambda)$, then

$$
H(\tau,\lambda)=\bigoplus_{\eta}H(\tau,\lambda,\eta),
$$

where $\eta$ records a joint eigensystem. Since the ambient space is finite-dimensional, only finitely many eigensystems occur there.

For an infinite commuting family, one does not diagonalize operators successively forever. Instead, the finite-dimensional commutative $*$-algebra generated by their restrictions is simultaneously diagonalizable. Any chosen set of algebra generators then distinguishes the same joint eigenspaces. This observation is useful when the global operator algebra has infinitely many generators but each spectral window sees only a finite-dimensional quotient.

Normality is important. Commuting nonnormal matrices can be simultaneously upper triangular but need not possess an orthonormal eigenbasis. In applications, adjoint relations among convolution operators provide the needed $*$-structure.

## 11. The spectral mechanism for cuspidal automorphic spaces

The preceding theory is designed to be an interface: geometry supplies estimates, and Hilbert-space analysis converts them into a discrete spectrum and a trace. This final chapter states that interface carefully for cuspidal automorphic spaces. It distinguishes the typewise compactness that is true from an overly strong global compactness claim, and it keeps the spectral, kernel, and geometric steps logically separate.

### 11.1 The analytic input and the spectral output

Let $[G]$ denote a finite-volume arithmetic quotient of a unimodular locally compact group, with a fixed unitary central character if one is imposed, and let

$$
\mathcal H=L^2([G]).
$$

Constant terms along proper parabolic subgroups detect the noncuspidal directions. The cuspidal space $\mathcal H_{\mathrm{cusp}}$ is the closed subspace on which all proper constant terms vanish in the appropriate almost-everywhere sense. Proving closedness is a theorem of reduction theory, not a formal consequence of writing an intersection of kernels, because constant-term operators require domain and growth control on the full $L^2$ space.

The spectral argument begins only after the following analytic inputs have been established.

- The cuspidal subspace is closed and invariant under the right regular action and the relevant convolution operators.
- On each fixed finite-level and compact-type subspace, a positive symmetric elliptic operator has a canonical self-adjoint realization.
- Its form domain embeds compactly into the corresponding cuspidal $L^2$ subspace. The compactness combines local elliptic compactness on truncated regions with uniform cusp decay preventing mass from escaping.
- Smooth compactly supported convolution operators improve regularity to sufficiently high order, and their automorphic kernels satisfy the convergence estimates needed for Fubini and diagonal integration.

Once these inputs are available, the results of this book turn them into the following outputs.

**Cuspidal spectral principle.** On every fixed level and compact type, the self-adjoint elliptic operator has compact resolvent. Hence the cuspidal space has an orthonormal basis of smooth eigenvectors on that type, bounded spectral intervals are finite-dimensional, commuting normal symmetries admit simultaneous orthogonal decomposition, and each resulting representation occurs with finite multiplicity. Sufficiently smoothing convolution operators are trace class, and their trace has both an absolutely convergent spectral expansion and a diagonal-kernel expression.

The proof is now short because the difficult geometry has been isolated. Compactness of the form embedding gives compact resolvent by Proposition 4.3. Theorem 6.2 gives a discrete eigenbasis and finite-dimensional spectral windows. Elliptic regularity upgrades weak eigenvectors to smooth vectors. Sections 10.3 and 10.4 organize the windows under compact types and commuting operators. Chapters 7--9 give trace class and the kernel trace formula once smoothing and kernel bounds are known.

### 11.2 Type-by-type compactness

It is generally wrong to demand one compact-resolvent operator on the entire right regular representation. An irreducible representation of a noncompact group is itself often infinite-dimensional, and a central differential operator may act by one scalar throughout it. That scalar would then have infinite multiplicity. The correct statement fixes finite level at the nonarchimedean places and a compact type at infinity.

Let $K_f$ be a compact open subgroup and let $\tau$ be an irreducible type of a maximal compact subgroup $K_\infty$. Write

$$
\mathcal H_{K_f,\tau}
=P_\tau\mathcal H_{\mathrm{cusp}}^{K_f}.
$$

The relevant positive elliptic operator $A_\tau$ acts on this space. Its quadratic form typically combines a central invariant differential operator with a positive compact-direction operator. The second term controls derivatives along compact directions; fixing $\tau$ makes it bounded or scalar, while the first term controls the noncompact directions. This is why the resulting operator can be elliptic and semibounded even when a central operator alone is not.

Assume the form-domain inclusion for $A_\tau$ is compact. Then

$$
\mathcal H_{K_f,\tau}
=\widehat\bigoplus_{\lambda}
\ker(A_\tau-\lambda),
\tag{11.1}
$$

and every summand is finite-dimensional. The hat emphasizes Hilbert completion; individual vectors are square-summable sums of eigencomponents.

As $K_f$ ranges through a countable cofinal family and $\tau$ through the countable unitary dual of $K_\infty$, the finite-type spaces exhaust the smooth vectors densely. Representation-theoretic decomposition may initially be given as a direct integral. Compactness forces its measure to be atomic on every type: a nonatomic piece of positive measure would make an appropriate bounded spectral projection on a nonzero type infinite-dimensional. Since types exhaust the representation, only discrete atoms remain. Finite dimensionality in (11.1) bounds the multiplicity of every atom containing $\tau$. Thus one obtains a Hilbert direct sum

$$
\mathcal H_{\mathrm{cusp}}
\simeq
\widehat\bigoplus_{\pi}m(\pi)\,\mathcal H_\pi,
\qquad m(\pi)<\infty.
\tag{11.2}
$$

The passage from typewise atoms to the irreducible summands in (11.2) uses the type-I decomposition theory of the group and the fact that the chosen differential and convolution algebras separate the relevant irreducible representations. Hilbert-space compactness supplies discreteness and finite multiplicity; local and global representation theory supplies the labels $\pi$.

Two qualifications prevent overstatement. First, (11.2) concerns the cuspidal space, not all of $L^2([G])$; Eisenstein series can produce continuous spectrum outside it. Second, finite multiplicity does not mean that the representation spaces $\mathcal H_\pi$ are finite-dimensional. It means that the number of copies $m(\pi)$ is finite.

### 11.3 Smoothing kernels and the cuspidal trace

Let $f$ be a smooth compactly supported test function and let $R(f)$ be right convolution:

$$
(R(f)\varphi)(x)=\int_G f(g)\varphi(xg)\,dg.
$$

On the quotient its formal kernel is

$$
K_f(x,y)=\sum_{\gamma}f(x^{-1}\gamma y),
\tag{11.3}
$$

with the indexing modified as required by the quotient and central character. Formula (11.3) is only a starting point. One must prove convergence, compatibility with the central quotient, and integrability before using it under an integral.

There are two robust routes to trace class on the cuspidal space.

**Factorization route.** If $R(f)|_{\mathrm{cusp}}=ST$ with $S$ and $T$ Hilbert--Schmidt, then it is trace class by Theorem 8.1. Such a factorization may come from writing $f=f_1*f_2$, or from splitting a smoothing operator into two half-order pieces. Formula (9.1) then computes the trace without restricting an arbitrary $L^2$ kernel to the diagonal.

**Elliptic route.** Suppose for some $N>0$ that

$$
R(f)(I+A_\tau)^N
$$

extends boundedly on each fixed-type space, while $(I+A_\tau)^{-N}$ is trace class. Then

$$
R(f)=\big(R(f)(I+A_\tau)^N\big)(I+A_\tau)^{-N}
\tag{11.4}
$$

is trace class. The first assertion is a smoothing estimate; the second follows from eigenvalue counting through (8.18). Summability over all types requires estimates uniform enough that the trace norms form a convergent series as in (10.2).

Once trace class is known and the cuspidal kernel $K_{f,\mathrm{cusp}}$ has a continuous or otherwise canonically integrable diagonal, the trace is

$$
\operatorname{tr}\big(R(f)|_{\mathcal H_{\mathrm{cusp}}}\big)
=\int_{[G]}K_{f,\mathrm{cusp}}(x,x)\,dx.
\tag{11.5}
$$

The order of proof matters. One does not infer trace class from the visual plausibility of the diagonal. One first proves an ideal estimate or a positive-kernel theorem, then identifies the operator kernel, then invokes the justified diagonal formula.

### 11.4 Spectral and geometric expansions

On the decomposition (11.2), convolution acts as

$$
R(f)|_{\mathrm{cusp}}
\simeq
\widehat\bigoplus_\pi
I_{m(\pi)}\otimes\pi(f).
\tag{11.6}
$$

If the left side is trace class, the direct-sum criterion gives absolute convergence and

$$
\operatorname{tr}\big(R(f)|_{\mathrm{cusp}}\big)
=\sum_\pi m(\pi)\operatorname{tr}\pi(f).
\tag{11.7}
$$

This is the cuspidal spectral expansion. Absolute convergence is not a cosmetic improvement: it permits regrouping by local type, infinitesimal character, or transferred packet without changing the value.

Combining (11.5) and (11.7) gives

$$
\sum_\pi m(\pi)\operatorname{tr}\pi(f)
=\int_{[G]}K_{f,\mathrm{cusp}}(x,x)\,dx.
\tag{11.8}
$$

To turn the right side into a geometric conjugacy-class expansion, insert (11.3), justify exchanging the sum and integral, and group terms by rational conjugacy. Centralizers and quotient measures then convert each group into an orbital integral. Those are geometric and measure-normalization arguments beyond Hilbert-space spectral theory. The contribution of the present theory is exact and indispensable: it proves that the left side is a genuine operator trace, that its spectral sum is absolutely convergent, and that the trace may be computed from the diagonal kernel under stated hypotheses.

A cuspidal test factor often removes noncuspidal spectrum before this argument is applied. Analytically, vanishing of proper constant terms makes the kernel land in $\mathcal H_{\mathrm{cusp}}$ in one variable and annihilates continuous and residual contributions. That vanishing must be proved from the chosen local test function and global constant-term formula; it is not a consequence of trace-class theory itself. Once proved, (11.8) is a simple cuspidal trace identity rather than a regularized trace.

### 11.5 Twisted traces

Let $\Theta$ be a unitary operator preserving $\mathcal H_{\mathrm{cusp}}$, for example one induced by a finite-order automorphism, and suppose it intertwines convolution in the expected way. If $R(f)|_{\mathrm{cusp}}$ is trace class, then so is

$$
\Theta R(f)|_{\mathrm{cusp}},
$$

with

$$
\|\Theta R(f)\|_1=\|R(f)\|_1.
$$

Thus the twisted trace is an ordinary trace-class trace; no new ideal is required.

If $\Theta$ permutes the irreducible summands in (11.2), a finite orbit of length greater than one contributes zero to the trace of the resulting off-diagonal block. Only $\Theta$-stable representations contribute. After choosing an intertwiner $I_\pi:\pi\to\pi\circ\Theta$, the spectral expansion takes the form

$$
\operatorname{tr}(\Theta R(f)|_{\mathrm{cusp}})
=\sum_{\pi\simeq\pi\circ\Theta}
m(\pi)\operatorname{tr}(I_\pi\pi(f)),
\tag{11.9}
$$

with the action on the multiplicity space included in $I_\pi$ when it is nontrivial. Normalizing the intertwiner is part of the representation-theoretic data; multiplying it by a scalar changes the twisted character.

On the kernel side, $\Theta$ replaces the ordinary diagonal by a twisted diagonal. If $(\Theta\varphi)(x)=\varphi(\theta^{-1}x)$, then the kernel of $\Theta R(f)$ is obtained from $K_f$ by applying $\theta^{-1}$ in the output variable, and its trace integrates the corresponding twisted diagonal. Grouping its terms produces twisted conjugacy classes. As before, the spectral theory guarantees trace class and legitimate trace expansions; arithmetic geometry and harmonic analysis identify the twisted orbital terms.

## Conclusion

The finite-dimensional spectral picture survives in infinite dimension only after its components are separated and rebuilt with the correct hypotheses. Domains and graphs make unbounded formulas into closed operators. The adjoint detects missing boundary conditions, while the nonreal resolvent distinguishes symmetry from self-adjointness. Closed semibounded forms construct canonical self-adjoint operators from energy, and compact form embeddings turn geometric confinement into compact resolvents.

Projection-valued measures give the general spectral theorem, including multiplication models with continuous spectrum. Compact resolvent is the decisive extra condition that collapses spectral integration to an orthogonal eigenbasis with finite-dimensional eigenspaces and eigenvalues escaping to infinity. The min--max principle then converts energy comparison into eigenvalue comparison.

Hilbert--Schmidt and trace-class ideals quantify smoothing. Square-integrable kernels represent exactly the Hilbert--Schmidt operators, but have no intrinsic diagonal. Trace class arises from a product of two Hilbert--Schmidt operators, has a basis-independent cyclic trace, and admits a diagonal kernel formula only when factorization, positivity and continuity, or sufficient smoothing makes that diagonal meaningful. These distinctions are what keep spectral and geometric trace calculations honest.

For cuspidal automorphic spaces, the Hilbert-space argument is now modular and reusable. Closedness and cusp decay isolate a genuine Hilbert subspace; elliptic estimates and compact embedding produce discrete typewise spectra; orthogonal decomposition and commuting actions produce finite multiplicities; smoothing makes convolution trace class; and the trace becomes both an absolutely convergent sum of representation-theoretic traces and an integral of an automorphic kernel. That chain of implications is the analytic skeleton on which cuspidal spectral expansions and their trace identities rest.
