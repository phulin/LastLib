# Lefschetz Trace Formulas for Curves and Surfaces

## Contents

- [1. From counting to cohomological trace](#1-from-counting-to-cohomological-trace)
  - [1.1 The organizing question](#11-the-organizing-question)
  - [1.2 Conventions and coefficient regimes](#12-conventions-and-coefficient-regimes)
  - [1.3 The route through the book](#13-the-route-through-the-book)
- [2. Frobenius and its fixed points](#2-frobenius-and-its-fixed-points)
  - [2.1 Arithmetic and geometric Frobenius](#21-arithmetic-and-geometric-frobenius)
  - [2.2 Rational points as fixed points](#22-rational-points-as-fixed-points)
  - [2.3 The graph and the diagonal](#23-the-graph-and-the-diagonal)
  - [2.4 Transversality on a smooth scheme](#24-transversality-on-a-smooth-scheme)
- [3. Compact support and the Künneth theorem](#3-compact-support-and-the-künneth-theorem)
  - [3.1 Why products must be derived](#31-why-products-must-be-derived)
  - [3.2 Finite-coefficient Künneth](#32-finite-coefficient-kunneth)
  - [3.3 Integral and rational coefficients](#33-integral-and-rational-coefficients)
  - [3.4 Compatibility with trace and Frobenius](#34-compatibility-with-trace-and-frobenius)
- [4. Cycle classes, graphs, and correspondences](#4-cycle-classes-graphs-and-correspondences)
  - [4.1 The diagonal as the identity kernel](#41-the-diagonal-as-the-identity-kernel)
  - [4.2 Graphs and their actions](#42-graphs-and-their-actions)
  - [4.3 General degree-zero correspondences](#43-general-degree-zero-correspondences)
  - [4.4 Composition, transpose, and base change](#44-composition-transpose-and-base-change)
- [5. Traces of perfect complexes](#5-traces-of-perfect-complexes)
  - [5.1 The alternating trace](#51-the-alternating-trace)
  - [5.2 Additivity and cyclicity](#52-additivity-and-cyclicity)
  - [5.3 Evaluation against the diagonal](#53-evaluation-against-the-diagonal)
- [6. The Lefschetz--Verdier trace theorem](#6-the-lefschetz--verdier-trace-theorem)
  - [6.1 Cohomological correspondences](#61-cohomological-correspondences)
  - [6.2 The global trace class](#62-the-global-trace-class)
  - [6.3 Localization on the fixed locus](#63-localization-on-the-fixed-locus)
  - [6.4 Proof of the trace theorem](#64-proof-of-the-trace-theorem)
- [7. Local terms and isolated fixed points](#7-local-terms-and-isolated-fixed-points)
  - [7.1 What a local term measures](#71-what-a-local-term-measures)
  - [7.2 The clean fixed-point calculation](#72-the-clean-fixed-point-calculation)
  - [7.3 Multiplicity and nontransverse intersections](#73-multiplicity-and-nontransverse-intersections)
  - [7.4 Positive-dimensional fixed loci](#74-positive-dimensional-fixed-loci)
- [8. The Grothendieck--Lefschetz formula over a finite field](#8-the-grothendieck--lefschetz-formula-over-a-finite-field)
  - [8.1 Smooth schemes and constant coefficients](#81-smooth-schemes-and-constant-coefficients)
  - [8.2 Arbitrary curves and surfaces](#82-arbitrary-curves-and-surfaces)
  - [8.3 Constructible coefficients](#83-constructible-coefficients)
  - [8.4 Extension fields and iterated Frobenius](#84-extension-fields-and-iterated-frobenius)
- [9. Curves](#9-curves)
  - [9.1 Proper smooth curves](#91-proper-smooth-curves)
  - [9.2 Open curves and boundary points](#92-open-curves-and-boundary-points)
  - [9.3 Singular curves and normalization](#93-singular-curves-and-normalization)
  - [9.4 Endomorphisms of curves](#94-endomorphisms-of-curves)
- [10. Surfaces](#10-surfaces)
  - [10.1 The five cohomological degrees](#101-the-five-cohomological-degrees)
  - [10.2 Divisors and the middle trace](#102-divisors-and-the-middle-trace)
  - [10.3 Open and singular surfaces](#103-open-and-singular-surfaces)
  - [10.4 Products of curves and a model computation](#104-products-of-curves-and-a-model-computation)
- [11. Trace formulas for correspondences](#11-trace-formulas-for-correspondences)
  - [11.1 Properly supported correspondences](#111-properly-supported-correspondences)
  - [11.2 Fixed points of a correspondence](#112-fixed-points-of-a-correspondence)
  - [11.3 Finite étale and Hecke-type diagrams](#113-finite-etale-and-hecke-type-diagrams)
  - [11.4 Projectors and simultaneous Frobenius traces](#114-projectors-and-simultaneous-frobenius-traces)
- [12. Zeta functions and rationality](#12-zeta-functions-and-rationality)
  - [12.1 The Euler product and point-count exponential](#121-the-euler-product-and-point-count-exponential)
  - [12.2 Cohomological factorization](#122-cohomological-factorization)
  - [12.3 Curves and surfaces explicitly](#123-curves-and-surfaces-explicitly)
  - [12.4 Open--closed factorization](#124-open--closed-factorization)
- [13. Functional equations](#13-functional-equations)
  - [13.1 Reciprocal characteristic polynomials](#131-reciprocal-characteristic-polynomials)
  - [13.2 The functional equation for smooth proper varieties](#132-the-functional-equation-for-smooth-proper-varieties)
  - [13.3 Curves](#133-curves)
  - [13.4 Surfaces and the middle sign](#134-surfaces-and-the-middle-sign)
  - [13.5 Why open varieties require a paired statement](#135-why-open-varieties-require-a-paired-statement)
- [14. Coefficients, families, and good reduction](#14-coefficients-families-and-good-reduction)
  - [14.1 L-functions of constructible sheaves](#141-l-functions-of-constructible-sheaves)
  - [14.2 Base change in a family](#142-base-change-in-a-family)
  - [14.3 Good reduction and local factors](#143-good-reduction-and-local-factors)
  - [14.4 A hypothesis checklist](#144-a-hypothesis-checklist)
- [15. The reusable trace-formula package](#15-the-reusable-trace-formula-package)
  - [15.1 The complete theorem](#151-the-complete-theorem)
  - [15.2 Final synthesis](#152-final-synthesis)

## 1. From counting to cohomological trace

### 1.1 The organizing question

Arithmetic geometry repeatedly asks for the number of solutions of polynomial equations over a finite field. Direct counting sees one field at a time. Geometry suggests that the counts over all extensions should instead be shadows of one finite collection of linear operators. This book explains that suggestion and proves it for curves and surfaces.

Let $X$ be a separated scheme of finite type over $k=\mathbf F_q$. Write $\bar X=X\times_k\bar k$, and let $F$ denote geometric Frobenius acting on $\bar X$ and on its compactly supported étale cohomology. The central identity is

$$
\#X(\mathbf F_{q^n})
=\sum_i(-1)^i\operatorname{Tr}
\left(F^n\mid H_c^i(\bar X,\mathbf Q_\ell)\right),
\qquad \ell\ne\operatorname{char}k.
$$

The right side is finite because compactly supported cohomology is bounded and finite-dimensional. The formula does much more than replace one count by another. Linear algebra packages all powers $F^n$ into characteristic polynomials, giving rationality of the zeta function. Poincaré duality pairs eigenvalues in complementary degrees, giving functional equations for smooth proper varieties. A second operator coming from an algebraic correspondence can be inserted into the same trace, which is the form needed for geometric Hecke operators.

The apparent simplicity of the formula conceals three distinct problems. One must identify rational points with fixed points of Frobenius, turn the global trace on cohomology into an intersection of a graph with a diagonal, and show that each Frobenius fixed point contributes exactly one. Keeping these transitions separate is the main organizing principle of the book.

### 1.2 Conventions and coefficient regimes

All schemes are noetherian in the situations under discussion. Morphisms used with compact support are separated and of finite type. Fix a prime $\ell$ invertible on every scheme in sight, and put

$$
\Lambda_m=\mathbf Z/\ell^m\mathbf Z,
\qquad \Lambda=\mathbf Z_\ell,
\qquad E=\mathbf Q_\ell.
$$

We use $R\Gamma_c$ and $H_c^i$ for compactly supported étale cohomology. At integral level these mean continuous cohomology of the normalized tower $(\Lambda_m)_m$. Rational cohomology is obtained only after taking the derived inverse limit and tensoring with $E$. For curves and surfaces the resulting complexes are perfect, so traces of endomorphisms are defined without choosing cohomology splittings.

If $k=\mathbf F_q$, arithmetic Frobenius is $a\mapsto a^q$ on $\bar k$ and geometric Frobenius is its inverse. The action on geometric cohomology used throughout is geometric Frobenius and is denoted $F$. Thus $F$ acts by $q^d$ on $H^{2d}(\bar X,E)$ when $X$ is smooth, proper, geometrically connected, and $d$-dimensional. If $\varphi$ denotes arithmetic Frobenius, then $F=\varphi^{-1}$. This convention is fixed once and for all.

A **variety** means a separated scheme of finite type over a field; it need not be smooth, proper, connected, or geometrically irreducible. Every theorem states the extra hypotheses it uses. Dimension is at most two unless a proof plainly works in arbitrary dimension and is stated that way.

### 1.3 The route through the book

The first stage is geometric. Frobenius fixed points become an intersection $\Gamma_F\cap\Delta$. Künneth and Poincaré duality then identify kernels on $X\times X$ with endomorphisms of $R\Gamma_c(X,-)$. The Lefschetz--Verdier theorem says that the trace of such an endomorphism is the sum of local contributions on the fixed locus.

The second stage is arithmetic. For Frobenius, the differential vanishes, so the graph meets the diagonal cleanly at smooth rational points. Localization and stratification extend the formula to singular curves and surfaces and to constructible sheaves. Applying the identity to every power of Frobenius produces zeta functions.

The last stage is duality. Reciprocal eigenvalue pairs give functional equations, but only under properness and smoothness in the self-dual form. Open varieties instead pair compactly supported cohomology with ordinary cohomology, and singular varieties use a dualizing complex. Stating this boundary correctly is part of the theorem, not an editorial qualification.

## 2. Frobenius and its fixed points

Finite fields supply a canonical endomorphism, but two inverse conventions coexist. This chapter fixes the geometry before cohomology enters and explains why the geometric normalization is the one that counts points.

### 2.1 Arithmetic and geometric Frobenius

Let $X_0$ be a scheme over $\mathbf F_q$ and $\bar X=X_0\times_{\mathbf F_q}\bar{\mathbf F}_q$. The absolute $q$-power map on functions defines a morphism

$$
\operatorname{Fr}_{X_0}:X_0\longrightarrow X_0.
$$

After base change, it is convenient to separate the relative Frobenius on the geometric scheme from the Galois descent automorphism. The endomorphism whose fixed geometric points are $X_0(\mathbf F_q)$ is the geometric Frobenius correspondence; its action on cohomology is the inverse of the action induced by arithmetic Frobenius in the absolute Galois group. We denote this cohomological and geometric operator by $F$.

This choice passes two consistency tests. On $\mathbf A^1$, the only nonzero compactly supported group is $H_c^2(\mathbf A^1_{\bar k},E)=E(-1)$, and $F$ acts on it by $q$, so its trace is $q=\#\mathbf A^1(\mathbf F_q)$. On a smooth proper $d$-fold, $F$ acts by $q^d$ on top cohomology, matching the leading scale of the point count.

For $n\ge1$, $F^n$ is geometric Frobenius relative to $\mathbf F_{q^n}$. No new convention is introduced when the ground field is enlarged.

### 2.2 Rational points as fixed points

The bridge from arithmetic to geometry is elementary but fundamental.

**Proposition 2.1.** There is a natural bijection

$$
X_0(\mathbf F_{q^n})
\xrightarrow{\sim}
\operatorname{Fix}(F^n)(\bar{\mathbf F}_q).
$$

**Proof.** A geometric point $x:\operatorname{Spec}\bar{\mathbf F}_q\to X_0$ descends to $\mathbf F_{q^n}$ exactly when it is invariant under the subgroup generated topologically by the $n$th power of arithmetic Frobenius. Equivalently it is fixed by the inverse automorphism $F^n$. Galois descent for morphisms from a field then supplies the unique $\mathbf F_{q^n}$-point. $\square$

For a finite-type scheme, this fixed-point set is finite. Indeed, cover $X_0$ by finitely many affine schemes. In an affine embedding, a fixed point has coordinates satisfying $T^{q^n}-T=0$, so only finitely many coordinate tuples occur. Scheme-theoretically the fixed locus may carry nilpotents, but its geometric points are precisely the rational points.

### 2.3 The graph and the diagonal

Fixed points become intersection theory by placing the map in a product. For an endomorphism $f:X\to X$, let

$$
\Gamma_f=(\operatorname{id},f):X\longrightarrow X\times X,
\qquad
\Delta=(\operatorname{id},\operatorname{id}):X\longrightarrow X\times X.
$$

The cartesian square

$$
\begin{array}{ccc}
\operatorname{Fix}(f)&\longrightarrow&X\\
\downarrow&&\downarrow\Gamma_f\\
X&\xrightarrow{\Delta}&X\times X
\end{array}
$$

identifies $\operatorname{Fix}(f)$ with the scheme-theoretic intersection $\Gamma_f\times_{X\times X}\Delta$. If $X$ is proper and smooth of pure dimension $d$, both graph and diagonal are codimension-$d$ regular immersions. When their intersection is finite, the degree of

$$
[\Gamma_f]\cdot[\Delta]
$$

is the sum of local intersection multiplicities. The trace formula will show that the same number is the alternating trace of $f$ on cohomology.

The order $(\operatorname{id},f)$ matters when a cycle kernel is turned into an operator. With the pull--cup--push convention of Chapter 4, $\Gamma_f=(\operatorname{id},f)$ produces the proper pushforward $f_*$, while its transpose $(f,\operatorname{id})$ produces $f^*$. Their intersections with the diagonal are canonically the same fixed scheme. The Frobenius trace formula uses the transpose graph so that the operator is the usual geometric-Frobenius pullback on cohomology.

### 2.4 Transversality on a smooth scheme

The local contribution is simplest when the graph and diagonal are transverse. At a fixed geometric point $x$, their tangent spaces in

$$
T_{(x,x)}(X\times X)=T_xX\oplus T_xX
$$

are

$$
T\Gamma_f=\{(v,df_xv):v\in T_xX\},
\qquad
T\Delta=\{(v,v):v\in T_xX\}.
$$

Their intersection is the kernel of $1-df_x$. Thus the intersection is transverse exactly when $1-df_x$ is invertible.

For the $q^n$-power Frobenius in characteristic $p$, the differential is zero: locally $d(a^{q^n})=q^na^{q^n-1}da=0$. Hence $1-dF^n=1$. On a smooth $X$, every Frobenius fixed point is isolated and transverse, and its intersection multiplicity is one.

To justify the last assertion, choose regular parameters $t_1,\ldots,t_d$ at $x$. In the completed local ring of $X\times X$, the diagonal is cut out by $u_i-v_i$, while the graph is cut out by $v_i-f_i(u)$. Modulo both ideals the fixed intersection is cut out in $\widehat{\mathcal O}_{X,x}$ by $t_i-f_i(t)$. The linear terms form the matrix $1-df_x$. If it is invertible, these elements are a regular system of parameters, so the quotient has length one. This local calculation is the reason every smooth Frobenius fixed point contributes exactly one without a sign or a power of $q$.

## 3. Compact support and the Künneth theorem

The graph of a map lives on a product, so no trace formula can avoid Künneth. Nonproper varieties force compact support, and torsion coefficients force derived tensor products. This chapter proves the precise product statement that the later kernel calculation needs.

### 3.1 Why products must be derived

Before forming products, recall how support enters. Choose a compactification $j:X\hookrightarrow\overline X$ with $\overline X$ proper and set

$$
R\Gamma_c(X,K)=R\Gamma(\overline X,j_!K).
$$

This is independent of the compactification. Given two choices, the closure of the diagonal in their product supplies a proper common refinement. Proper base change identifies the pushforward of extension by zero on the refinement with extension by zero on either original compactification: over $X$ the refinement is the identity, and on the boundary every stalk is zero. A third refinement gives the cocycle condition. Thus compact support is a functor, not a choice made after cohomology. Over $\mathbf F_q$ one chooses the compactification over $\mathbf F_q$; its absolute $q$-power Frobenius restricts to that of $X$, so the construction is Frobenius-equivariant.

For separated finite-type $X,Y$ over a separably closed field and bounded constructible complexes $K,L$, external product gives

$$
R\Gamma_c(X,K)\otimes^L R\Gamma_c(Y,L)
\longrightarrow
R\Gamma_c(X\times Y,K\boxtimes^L L).
$$

If coefficients form a field and all cohomology is finite-dimensional, taking cohomology yields the familiar direct sum

$$
H_c^n(X\times Y,K\boxtimes L)
\cong
\bigoplus_{a+b=n}H_c^a(X,K)\otimes H_c^b(Y,L).
$$

Over $\Lambda_m$, the ordinary tensor formula can fail because cohomology groups need not be flat. The correct consequence is a Künneth spectral sequence

$$
\operatorname{Tor}^{\Lambda_m}_{r}
\bigl(H_c^a(X,K),H_c^b(Y,L)\bigr)
\Longrightarrow
H_c^{a+b-r}(X\times Y,K\boxtimes^L L).
$$

This is not a technical nuisance. The trace is defined on the perfect complex, and passing prematurely to a direct sum of cohomology groups can discard the extension on which an endomorphism acts.

### 3.2 Finite-coefficient Künneth

Finite coefficients are the foundational level because compactification, proper base change, and constructible dévissage all operate there without an inverse-limit ambiguity. Proving the derived statement first also displays exactly where Tor terms enter, so the later integral theorem is not based on a false degreewise tensor formula.

**Theorem 3.1 (compactly supported Künneth).** Let $X,Y$ be separated of finite type over a separably closed field, and let $K\in D_c^b(X,\Lambda_m)$ and $L\in D_c^b(Y,\Lambda_m)$ have finite Tor-amplitude. Then the external-product morphism is an isomorphism:

$$
R\Gamma_c(X,K)\otimes^L_{\Lambda_m}R\Gamma_c(Y,L)
\xrightarrow{\sim}
R\Gamma_c(X\times Y,K\boxtimes^L L).
$$

**Proof.** Choose compactifications $j_X:X\hookrightarrow\overline X$ and $j_Y:Y\hookrightarrow\overline Y$. Their product is a compactification of $X\times Y$, and extension by zero satisfies

$$
(j_X\times j_Y)_!(K\boxtimes L)
\cong j_{X!}K\boxtimes j_{Y!}L
$$

by checking geometric stalks. We may therefore assume $X$ and $Y$ proper.

For proper schemes, form the external-product map and test its cone after pulling back to a geometric point of either factor. Proper base change identifies the stalk with the corresponding cohomology complex of the other fiber. For a finite locally free coefficient sheaf the assertion reduces, by a finite affine étale cover and Čech totalization, to the tensor identity for finite complexes of modules. Finite Tor-amplitude lets us resolve $K$ and $L$ by bounded complexes of such sheaves locally. Constructible dévissage across finitely many strata and the five lemma extend the result to the stated complexes. Applying proper global sections and undoing the compactifications proves the theorem. $\square$

The proof also establishes associativity and symmetry because those identities hold for external products before global sections. When two odd-degree classes are exchanged, the symmetry contributes the Koszul sign $(-1)^{ab}$.

### 3.3 Integral and rational coefficients

Arithmetic representations use $\mathbf Z_\ell$-lattices and $\mathbf Q_\ell$-vector spaces, so a finite-level product is not the endpoint. The issue is to pass through the coefficient tower without losing a derived-limit term; uniform finiteness and perfectness are what make that passage legitimate.

At level $m$, Theorem 3.1 is compatible with reduction $\Lambda_{m+1}\to\Lambda_m$. For curves and surfaces the complexes have a uniform bounded range and finite cohomology. Their towers are therefore Mittag--Leffler, and derived inverse limit gives

$$
R\Gamma_c(X,\mathbf Z_\ell)
\otimes^L_{\mathbf Z_\ell}
R\Gamma_c(Y,\mathbf Z_\ell)
\xrightarrow{\sim}
R\Gamma_c(X\times Y,\mathbf Z_\ell).
$$

Here perfectness is decisive: represent both sides by bounded complexes of finite free $\mathbf Z_\ell$-modules, reduce modulo every $\ell^m$, and observe that the cone has zero reduction at every level. Derived completeness forces the cone to vanish.

Tensoring afterward with $E$ yields rational Künneth. Because $E$ is a field, the spectral sequence degenerates to the direct-sum formula. Nothing in this passage says that the integral cohomology groups themselves are free; it is the complexes that are perfect.

### 3.4 Compatibility with trace and Frobenius

Künneth must respect the structures used later. If $u$ and $v$ are endomorphisms of $X$ and $Y$, naturality of external product gives an action of $u\times v$ corresponding to $u\otimes v$. If both cohomology complexes are perfect, then

$$
\operatorname{Tr}(u\otimes v)
=\operatorname{Tr}(u)\operatorname{Tr}(v).
$$

This follows termwise on bounded finite projective representatives and hence is independent of those representatives.

If $X$ and $Y$ are smooth of dimensions $d$ and $e$, their compact fundamental classes multiply to the class of $X\times Y$, and the trace on top compact cohomology is the tensor product of the two traces. Projection formula and the construction of compact support show that this remains true for open varieties. Frobenius respects external products, so $F_{X\times Y}=F_X\otimes F_Y$ under Künneth. These compatibilities will turn a product count into a product of counts, as arithmetic demands.

## 4. Cycle classes, graphs, and correspondences

A cohomological operator can be represented by a class on a product. This kernel viewpoint is what allows a trace, which is linear algebra, to be localized at geometric fixed points. The purpose of this chapter is to make the dictionary precise, including degrees and twists.

### 4.1 The diagonal as the identity kernel

An operator kernel must have a unit for convolution. Geometry provides it through the diagonal, and verifying that it acts identically fixes the pushforward convention and every later graph formula.

Let $X$ be smooth proper of pure dimension $d$ over a separably closed field. The diagonal is a regular immersion of codimension $d$ and has a class

$$
[\Delta_X]\in H^{2d}(X\times X,\Lambda_m(d)).
$$

For $x\in H^i(X,\Lambda_m)$, define the action of a codimension-$d$ class $\gamma$ by

$$
T_\gamma(x)=p_{2*}(p_1^*x\smile\gamma).
$$

The shifts cancel: cup product raises degree by $2d$ and twist by $d$, while integration along the $d$-dimensional fibers of $p_2$ lowers them by the same amounts.

**Proposition 4.1.** The diagonal class acts as the identity.

**Proof.** Since $p_2\circ\Delta=\operatorname{id}_X$, the projection formula gives

$$
p_{2*}(p_1^*x\smile\Delta_*1)
=(p_2\circ\Delta)_*(\Delta^*p_1^*x)
=x.
$$

Every equality is an equality of maps before taking cohomology, so it remains valid with finite, integral, or rational coefficients. $\square$

Under rational Künneth and Poincaré duality, the diagonal class is the coevaluation element corresponding to $\operatorname{id}_{R\Gamma(X,E)}$. If $(e_j)$ and $(e_j^\vee)$ are homogeneous dual bases, then schematically

$$
[\Delta_X]=\sum_j(-1)^{\deg e_j}e_j^\vee\boxtimes e_j,
$$

with the displayed sign determined by the graded switch. This basis expression is useful for computation, but the geometric class is canonical and does not require a basis.

### 4.2 Graphs and their actions

A morphism should recover its familiar pullback or pushforward when viewed as a kernel. Computing the two possible graph orientations prevents a variance error from propagating into the fixed-point formula.

Let $f:X\to X$ be a morphism of a smooth proper $d$-fold. Its graph $\Gamma_f$ is again a regular codimension-$d$ cycle. With the convention $\Gamma_f=(\operatorname{id},f)$,

$$
T_{[\Gamma_f]}(x)=f_*x.
$$

The transpose graph $(f,\operatorname{id})$ acts as $f^*$. Indeed, for the latter graph, $p_2$ restricts to the identity and $p_1$ restricts to $f$, so the projection formula gives $f^*$. For trace questions it does not matter which convention is chosen provided graph and action are matched: $f^*$ and $f_*$ are adjoint, hence have the same alternating trace when both are endomorphisms of a perfect self-dual complex.

For a nonproper $X$, an arbitrary graph need not define an endomorphism of compactly supported cohomology by pullback: pullback does not preserve proper support unless $f$ is proper. A proper $f$ does act on $R\Gamma_c$ by pullback followed through the proper-support identification, while a general cohomological correspondence must carry its own proper-support condition. This distinction will be explicit in Chapter 11.

### 4.3 General degree-zero correspondences

Graphs are too restrictive for Hecke-type operators, whose source parametrizes several images of one point. A cycle on a product is the correct replacement, but its codimension must determine the degree and Tate-twist shift rather than be hidden in notation.

Let $X$ and $Y$ be smooth of pure dimensions $d_X,d_Y$. A cycle $\Gamma\subset X\times Y$ of codimension $r$ defines

$$
\Gamma_*:H^i(X,E(s))
\longrightarrow
H^{i+2(r-d_X)}(Y,E(s+r-d_X))
$$

provided the support is proper over $Y$. The formula is

$$
\Gamma_*(x)=p_{Y*}(p_X^*x\smile[\Gamma]).
$$

A **degree-zero correspondence** from a pure $d$-fold to itself therefore has codimension $d$. Suppressing the shift for other codimensions would identify different operators and is never harmless.

The cycle formula agrees with a pull–push diagram. If

$$
X\xleftarrow{p}Z\xrightarrow{q}Y
$$

represents $\Gamma=(p,q)_*[Z]$, with $q$ proper and the required orientation, then projection and functoriality of cycle classes give

$$
\Gamma_*=q_*p^*.
$$

This equality is the practical bridge between a moduli-theoretic correspondence and its kernel class.

### 4.4 Composition, transpose, and base change

The kernel dictionary is useful only if it respects composition, adjoints, and change of field. These compatibilities turn geometric convolution into operator multiplication and ensure that a finite-field correspondence commutes with Frobenius.

Suppose $\Gamma\subset X\times Y$ and $\Theta\subset Y\times Z$ have proper support in the necessary directions. Their composite cycle is

$$
\Theta\circ\Gamma
=(p_{XZ})_*
\bigl(p_{XY}^*[\Gamma]\cdot p_{YZ}^*[\Theta]\bigr).
$$

If the intersections are transverse, the dot is ordinary intersection. In general it is the refined intersection product, including excess Chern classes. The projection formula proves

$$
(\Theta\circ\Gamma)_*=\Theta_*\circ\Gamma_*.
$$

Indeed, expand the right side, pull the inner pushforward through the outer cup product, and use proper base change in the middle cartesian square. The resulting expression is exactly the displayed convolution.

For a smooth proper $X$, transposition exchanges the factors. Poincaré duality and the projection formula give

$$
\langle\Gamma_*x,y\rangle
=\langle x,{}^t\Gamma_*y\rangle.
$$

Thus transpose is the geometric adjoint. An arithmetic adjoint may include an additional polarization or involution; geometry supplies only the transpose statement.

Cycle classes, external products, refined intersections, and proper pushforwards commute with field extension. Consequently a correspondence defined over $\mathbf F_q$ commutes with $F$, and its action can be inserted next to $F^n$ inside a trace. In a family, the same conclusion follows from proper base change once the support remains proper and no extra vertical component appears.

## 5. Traces of perfect complexes

The geometric side is now ready, but the cohomological side still needs a trace that behaves well in triangles. The alternating trace is exactly the invariant with that property. This chapter isolates the linear algebra so that no later geometric argument has to choose splittings.

### 5.1 The alternating trace

Taking an ordinary trace in each cohomological degree and alternating the results is forced by localization: a boundary triangle should make traces add. Defining the invariant on the perfect complex first ensures that it is independent of a noncanonical splitting into cohomology groups.

Let $C$ be a perfect complex over a field $E$ and $u:C\to C$ an endomorphism. Choose a bounded complex of finite-dimensional vector spaces representing $C$ and a chain map representing $u$. Define

$$
\operatorname{Tr}(u\mid C)
=\sum_j(-1)^j\operatorname{Tr}(u^j\mid C^j).
$$

This equals

$$
\sum_i(-1)^i\operatorname{Tr}(H^i(u)\mid H^i(C)).
$$

To prove the equality, write in every degree the space of cocycles as boundaries plus a complement representing cohomology, and the whole cochain space as cocycles plus a complement mapping isomorphically to the next boundary space. The boundary and complement traces cancel in consecutive degrees. The remaining terms are precisely the cohomology traces. The argument also shows independence of the chosen representative.

The same definition works over $\mathbf Z_\ell$ for a perfect complex: use finite projective modules and the ordinary projective trace. Reduction modulo $\ell^m$ and extension to $E$ preserve it.

### 5.2 Additivity and cyclicity

Two formal properties drive nearly every reduction later. Additivity permits passage to strata and boundaries, while cyclicity allows a pull--push composition to be reordered without changing its scalar trace.

**Lemma 5.1.** Suppose

$$
C'\longrightarrow C\longrightarrow C''\longrightarrow C'[1]
$$

is a distinguished triangle of perfect complexes and the three endomorphisms form a morphism of triangles. Then

$$
\operatorname{Tr}(u\mid C)
=\operatorname{Tr}(u'\mid C')
+\operatorname{Tr}(u''\mid C'').
$$

**Proof.** Replace the triangle by the mapping-cone triangle of a map between bounded projective complexes. The middle or cone terms are direct sums degree by degree, and the formula follows termwise with the shift sign. $\square$

This additivity is why a locally closed stratification can reduce the trace formula to smooth strata. It is also why nilpotent extensions and boundary triangles introduce no mysterious correction beyond their own cohomology.

If $a:C\to D$ and $b:D\to C$ are morphisms of perfect complexes, then

$$
\operatorname{Tr}(ba\mid C)=\operatorname{Tr}(ab\mid D).
$$

Choose finite projective representatives and use the ordinary rectangular-matrix identity in each degree. This cyclicity implies that conjugate correspondences have the same trace and that pullback and adjoint pushforward have matching Lefschetz numbers when the compositions make sense.

### 5.3 Evaluation against the diagonal

The decisive conceptual step is to express a numerical trace as the contraction of a kernel. Once this is done, the diagonal forces the contraction to occur precisely on the fixed locus of the geometric correspondence.

Let $X$ be smooth proper of dimension $d$, and let $K$ be a lisse finite locally free $E$-sheaf. Poincaré duality identifies the dual of $R\Gamma(X,K)$ with

$$
R\Gamma(X,K^\vee(d))[2d].
$$

Künneth therefore identifies endomorphisms of $R\Gamma(X,K)$ with suitable degree-$2d$, twist-$d$ classes on $X\times X$ carrying the coefficient kernel $K^\vee\boxtimes K$. Under this identification, composition is convolution of kernels and the identity is the diagonal coevaluation class.

The trace of an endomorphism is evaluation after coevaluation:

$$
E\xrightarrow{\operatorname{coev}}
C^\vee\otimes^LC
\xrightarrow{1\otimes u}
C^\vee\otimes^LC
\xrightarrow{\operatorname{ev}}E.
$$

Writing a homogeneous basis verifies that this composite is $\sum_i(-1)^i\operatorname{Tr}(H^i(u))$. Geometrically, coevaluation inserts the diagonal, the kernel inserts the graph or correspondence, and evaluation integrates their intersection. This identity is the conceptual core of every Lefschetz formula below.

## 6. The Lefschetz--Verdier trace theorem

The preceding kernel calculation assumes smoothness and properness. The trace formula needed for open and singular varieties must instead use compact support and the dualizing complex. Verdier duality supplies exactly that replacement. The result is best stated for a cohomological correspondence, because an ordinary morphism is only one source of such data.

### 6.1 Cohomological correspondences

A cycle class alone acts cleanly only in a smooth oriented setting. A cohomological correspondence packages the coefficient map and extraordinary pullback needed on open or singular spaces, so it is the correct input for the general theorem.

Let $X$ be separated of finite type over a separably closed field, let $K\in D_c^b(X,E)$, and let

$$
c=(c_1,c_2):C\longrightarrow X\times X
$$

be a correspondence. A **cohomological correspondence** lifting $c$ is a morphism

$$
u:c_1^*K\longrightarrow c_2^!K.
$$

Assume that pullback along $c_1$ preserves the relevant proper supports; it is enough that $c_1$ be proper. Adjunction for compactly supported direct image then produces an endomorphism

$$
R\Gamma_c(X,K)
\xrightarrow{c_1^*}
R\Gamma_c(C,c_1^*K)
\xrightarrow{u}
R\Gamma_c(C,c_2^!K)
\xrightarrow{\operatorname{Tr}_{c_2}}
R\Gamma_c(X,K).
$$

The last arrow is the counit for $c_2$ and uses $Rc_{2!}$, so $c_2$ need not be proper merely for that arrow to exist. In the standard pull--push situations both legs are proper, or the correspondence has a compactification for which the indicated support condition holds. Equivalently one may begin with a map $Rc_{2!}c_1^*K\to K$ whose support is proper over the point. We denote the induced endomorphism by $R\Gamma_c(u)$.

For the graph of a proper endomorphism $f$, take $C=X$, $c_1=f$, $c_2=\operatorname{id}$, and the natural pullback map. For a finite étale diagram, the identification $c_2^!=c_2^*$ makes $u$ the evident coefficient transport. For a cycle correspondence on a smooth variety, purity and the cycle class create the same operator as the pull--cup--push formula of Chapter 4.

### 6.2 The global trace class

The global alternating trace is a scalar, but localization requires a class before integration. Constructing that class on the fixed scheme is what makes it possible to split the scalar into contributions of separate fixed components.

The fixed locus of $c$ is

$$
\operatorname{Fix}(c)
=C\times_{X\times X,\,c}\Delta_X.
$$

Write $\delta:\operatorname{Fix}(c)\to C$ for its inclusion and $a:\operatorname{Fix}(c)\to\operatorname{Spec}\bar k$. Restricting $u$ to the diagonal and composing evaluation with the Verdier trace gives a class

$$
\operatorname{Tr}_c(u)
\in H^0(\operatorname{Fix}(c),a^!E).
$$

This notation is compact, so we unfold the construction. Verdier duality gives an evaluation $DK\otimes^L K\to\omega_X^\bullet$. The correspondence $u$, by adjunction, is a kernel pairing between $c_1^*DK$ and $c_2^*K$. Pulling to the fixed locus identifies $c_1$ and $c_2$. Evaluation then lands in the pullback of the dualizing complex, and extraordinary base change maps it to $a^!E$. Every arrow is canonical; in particular no orientation of a singular $X$ is guessed.

If the fixed locus is proper, its structural trace

$$
H^0(\operatorname{Fix}(c),a^!E)\longrightarrow E
$$

integrates the trace class. The resulting scalar is called the **geometric trace** of $(c,u)$.

### 6.3 Localization on the fixed locus

Fixed components can have different geometry and must be analyzed independently. The local-term decomposition isolates them while remaining compatible with the open--closed triangles used to remove singularities and boundary strata.

If the fixed locus is a finite disjoint union of open-and-closed pieces $Z_\alpha$, then

$$
H^0(\operatorname{Fix}(c),a^!E)
=\bigoplus_\alpha H^0(Z_\alpha,a_\alpha^!E).
$$

The component of $\operatorname{Tr}_c(u)$ on $Z_\alpha$, integrated to $E$, is the **local term** $LT_{Z_\alpha}(c,u)$. When the fixed locus is finite, the components may be taken point by point. If $x$ has residue field $k(x)$, the point trace includes the field trace from $k(x)$; after base change to an algebraic closure each geometric point appears separately.

Localization is compatible with open--closed decompositions. If $j:U\hookrightarrow X$ is a $c$-stable open and $i:Z\hookrightarrow X$ its closed complement, the triangle

$$
R\Gamma_c(U,j^*K)\longrightarrow
R\Gamma_c(X,K)\longrightarrow
R\Gamma_c(Z,i^*K)\longrightarrow
$$

is equivariant. Additivity of linear trace matches the decomposition of the geometric trace class into its portions over $U$ and $Z$. This compatibility is the engine of dimension induction.

### 6.4 Proof of the trace theorem

The proof now has one task: show that categorical evaluation of the global operator becomes geometric evaluation after pulling the kernel to the diagonal. We keep compactification, Künneth, duality, and proper trace visible because each accounts for one hypothesis in the statement.

**Theorem 6.1 (Lefschetz--Verdier).** Let $X$ be separated of finite type over a separably closed field, let $K\in D_c^b(X,E)$, and let $(c,u)$ be a properly supported cohomological correspondence whose fixed locus is proper. Then

$$
\sum_i(-1)^i
\operatorname{Tr}\bigl(H_c^i(u)\mid H_c^i(X,K)\bigr)
=\int_{\operatorname{Fix}(c)}\operatorname{Tr}_c(u).
$$

If the fixed locus is a disjoint union of proper components $Z_\alpha$, the right side is $\sum_\alpha LT_{Z_\alpha}(c,u)$.

**Proof.** First compactify $X$ and the proper support of $c$. Extension by zero replaces $K$ by $j_!K$ on a proper space. Independence of compactification and proper base change show that both the induced operator and its fixed-locus trace class are unchanged. Thus we may work with proper direct images.

Verdier duality identifies the dual of $R\Gamma_c(X,K)$ with $R\Gamma(X,DK)$. Künneth identifies their tensor product with compactly supported global sections of $DK\boxtimes K$ on $X\times X$. Under this identification, coevaluation of the perfect complex $R\Gamma_c(X,K)$ is the diagonal coevaluation class. The cohomological correspondence $u$ gives a functional on this kernel by pullback to $C$, application of $u$, and the trace for $c_2$.

By Section 5.3, evaluating that functional on coevaluation is the alternating linear trace of $R\Gamma_c(u)$. On the other hand, the cartesian square defining $\operatorname{Fix}(c)$ is precisely the pullback of $C$ along the diagonal. Proper base change moves the kernel evaluation to that square. The projection formula then contracts the coefficient factors by $DK\otimes K\to\omega_X^\bullet$, and transitivity of extraordinary traces integrates the result along the fixed locus. This is exactly $\int\operatorname{Tr}_c(u)$.

Therefore the two scalars are equal. Decomposing a proper fixed locus into open-and-closed components and using additivity gives the final assertion. $\square$

The proof explains the hypotheses. Constructibility and finite cohomology make the global complex perfect. Proper support makes pushforward and integration exist. Properness of the fixed locus makes the final scalar defined. Smoothness is absent because the dualizing complex supplies the orientation.

## 7. Local terms and isolated fixed points

The global theorem is useful only after its local terms can be computed. This chapter handles the cases required for Frobenius and for the curve and surface correspondences used later. It also explains precisely what changes when an intersection is not transverse.

### 7.1 What a local term measures

Suppose $X$ is smooth, $K$ is lisse, and $x$ is an isolated fixed point of an endomorphism $f$. Near $x$, the graph and diagonal are two regular subschemes of complementary codimension in $X\times X$. The local term combines the trace of the coefficient map on $K_x$ with the local intersection class of $\Gamma_f$ and $\Delta$.

When the intersection is transverse, the intersection factor is $1$. When coefficients are constant, the stalk factor is $1$. The intersection factor is an algebraic length, not an orientation sign: the Tate twist in purity already supplies the orientation.

### 7.2 The clean fixed-point calculation

Frobenius will reduce the entire global theorem to this local model. The invertibility of $1-df_x$ says that no infinitesimal fixed direction remains, forcing the geometric multiplicity to be one and leaving only the coefficient trace.

**Proposition 7.1.** Let $X$ be smooth over an algebraically closed field, let $f:X\to X$, and let $x$ be an isolated fixed point such that $1-df_x$ is invertible. Let $K$ be lisse near $x$ and let $u:f^*K\to K$ be a coefficient map. Then

$$
LT_x(f,u)=\operatorname{Tr}(u_x\mid K_x).
$$

**Proof.** Étale-locally at $x$, choose coordinates identifying a neighborhood with an étale neighborhood of affine space. Purity identifies the dualizing complex with $E(d)[2d]$, and the local trace is invariant under this replacement. The graph--diagonal intersection is cut out by $t_i-f_i(t)$.

Invertibility of $1-df_x$ makes these elements a regular system of parameters. Their quotient is the residue field and has length one. The fundamental classes of graph and diagonal therefore cup to the point fundamental class. Integrating this class gives $1$ by normalization of point trace. Since $K$ is lisse, it becomes constant after an étale refinement, and the remaining endomorphism is $u_x$ on its fiber. The local term is its ordinary trace. $\square$

For $f=F^n$, $df_x=0$, and the proposition applies at every smooth fixed point. For constant $K=E$, it gives $LT_x(F^n)=1$.

### 7.3 Multiplicity and nontransverse intersections

If $x$ remains isolated but $1-df_x$ is not invertible, the quotient

$$
\mathcal O_{X,x}/(t_1-f_1(t),\ldots,t_d-f_d(t))
$$

can have length greater than one. When graph and diagonal meet properly, define

$$
i_x(\Gamma_f,\Delta)
=\sum_{r\ge0}(-1)^r
\operatorname{length}
\operatorname{Tor}^{\mathcal O_{X\times X,(x,x)}}_r
(\mathcal O_{\Gamma_f,x},\mathcal O_{\Delta,x}).
$$

The refined intersection theorem and purity give $LT_x(f,E)=i_x(\Gamma_f,\Delta)$. For regular complementary intersections the higher Tor groups vanish and this is the quotient length. With a lisse coefficient action constant along the infinitesimal fixed scheme, the local term is this multiplicity times the stalk trace. In greater generality the coefficient action and derived intersection must be contracted together.

For example, on an affine chart the map $t\mapsto t+t^m$ has a fixed point at $0$ of multiplicity $m$. A set-theoretic count records one point, while its Lefschetz local term records the scheme-theoretic multiplicity. Frobenius avoids this complication because its linear fixed equations have identity Jacobian.

### 7.4 Positive-dimensional fixed loci

When a component $Z$ of the fixed locus has positive dimension, there is no point multiplicity to sum. If $Z$ is smooth and the fixed intersection is clean, the excess intersection formula expresses the local term as an integral over $Z$ of an Euler class of the moving normal complex, multiplied by the coefficient trace. For a surface, $Z$ can be a curve or the whole surface.

The intrinsic and always correct statement is

$$
LT_Z(f,u)=\int_Z\operatorname{Tr}_Z(u),
$$

where $\operatorname{Tr}_Z(u)$ is the Verdier local trace class. In the applications below, either fixed points are isolated and clean or the correspondence is handled through this intrinsic class.

## 8. The Grothendieck--Lefschetz formula over a finite field

We now combine the global theorem with the Frobenius local calculation. Smooth varieties give the essential geometry; localization then removes smoothness. This order makes clear why singular rational points still count with weight one.

### 8.1 Smooth schemes and constant coefficients

The smooth constant-coefficient case contains the essential fixed-point geometry in its purest form. Once proved, all remaining generality will come from additivity rather than a new local computation.

**Theorem 8.1.** Let $X$ be a smooth separated scheme of finite type over $\mathbf F_q$. For every $n\ge1$,

$$
\#X(\mathbf F_{q^n})
=\sum_i(-1)^i
\operatorname{Tr}
\left(F^n\mid H_c^i(\bar X,E)\right).
$$

**Proof.** The graph of $F^n$ has fixed locus $X(\mathbf F_{q^n})$, a finite proper scheme. Theorem 6.1 identifies the alternating cohomological trace with the sum of local terms. At every fixed point, $dF^n=0$, so Proposition 7.1 gives local term $1$ for the constant sheaf. Summing gives the formula. $\square$

Properness of $X$ was not used: compact support absorbs the boundary. Ordinary cohomology would already give the wrong answer for $\mathbf A^1$.

### 8.2 Arbitrary curves and surfaces

Singular schemes should still be counted point by point, but their local dualizing complexes need not look smooth. A Frobenius-stable smooth-locus decomposition avoids inventing a singular point formula and reduces the assertion to lower dimension.

**Theorem 8.2 (Grothendieck--Lefschetz).** Let $X$ be any separated finite-type scheme of dimension at most two over $\mathbf F_q$. Then the formula of Theorem 8.1 holds.

**Proof.** Nilpotents alter neither rational points nor the étale topos, so replace $X$ by $X_{\mathrm{red}}$. Let $U\subset X$ be the smooth locus, defined over $\mathbf F_q$, and let $Z=X\setminus U$. The compact-support localization triangle is Frobenius-equivariant, so trace additivity gives

$$
L(F^n,X)=L(F^n,U)+L(F^n,Z).
$$

Rational points satisfy the same decomposition. Theorem 8.1 treats $U$. Induction on dimension treats $Z$; in dimension zero, cohomology is concentrated in degree zero and Frobenius permutes the finite geometric points, with trace equal to the number fixed. Therefore the two additive functions agree on $X$. $\square$

### 8.3 Constructible coefficients

Replacing the constant sheaf by a coefficient system turns a variety into a function on its finite-field points. The purpose of the sheaf--function formula is to show that the sum of those local values is still one global cohomological trace.

Let $K_0\in D_c^b(X_0,E)$ carry a Frobenius structure, and let $K$ be its pullback to $\bar X$. At $x\in X_0(\mathbf F_{q^n})$, define

$$
\operatorname{Tr}(F_x^n\mid K_{\bar x})
=\sum_j(-1)^j\operatorname{Tr}
(F_x^n\mid\mathcal H^j(K)_{\bar x}).
$$

**Theorem 8.3 (sheaf--function trace formula).** One has

$$
\sum_i(-1)^i\operatorname{Tr}
\left(F^n\mid H_c^i(\bar X,K)\right)
=\sum_{x\in X_0(\mathbf F_{q^n})}
\operatorname{Tr}(F_x^n\mid K_{\bar x}).
$$

**Proof.** Stratify $X_0$ into finitely many Frobenius-stable smooth locally closed subschemes on which every cohomology sheaf of $K_0$ is lisse. Localization and trace additivity reduce to one smooth stratum and one lisse sheaf in one degree. Proposition 7.1 identifies each local term with the stalk trace; a shift supplies $(-1)^j$. Summing strata proves the formula. $\square$

### 8.4 Extension fields and iterated Frobenius

Over $\mathbf F_{q^n}$, geometric Frobenius is $F^n$, while $\bar X$ and its cohomology do not change. Thus one finite-dimensional operator produces every extension-field count. Components permuted by Frobenius are handled automatically: the trace of a permutation is the number of fixed components.

Künneth also gives

$$
L(F^n,X\times Y)=L(F^n,X)L(F^n,Y),
$$

matching the product formula for rational points. This is a useful check on support and signs.

## 9. Curves

Curves display the whole mechanism with only three cohomological degrees. The middle degree carries the arithmetic information; the bottom and top degrees account for connectedness and the main power of $q$. Open and singular curves show how boundary and normalization modify that picture.

### 9.1 Proper smooth curves

In the proper smooth case, compact support disappears and only the middle cohomology is unknown. Separating the universal degree-zero and degree-two contributions reveals exactly where the arithmetic of the curve is stored.

Let $C/\mathbf F_q$ be smooth, proper, and geometrically connected of genus $g$. Then

$$
H^0(\bar C,E)=E,
\qquad \dim_EH^1(\bar C,E)=2g,
\qquad H^2(\bar C,E)=E(-1).
$$

Geometric Frobenius acts as $1$ in degree zero and $q$ in degree two. Hence

$$
\#C(\mathbf F_{q^n})
=1-\operatorname{Tr}(F^n\mid H^1(\bar C,E))+q^n.
$$

This isolates the genuinely geometric term. It does not yet bound that term: absolute values of Frobenius eigenvalues belong to weight theory, not to the trace formula itself.

For $C=\mathbf P^1$, $H^1=0$ and the formula gives $q^n+1$. In genus one, write $a_n=\operatorname{Tr}(F^n\mid H^1)$. If $\alpha,\beta$ are the two eigenvalues, duality gives $\alpha\beta=q$, so

$$
a_{n+2}=a_1a_{n+1}-qa_n.
$$

This recurrence uses duality but no estimate on $\alpha$ and $\beta$.

### 9.2 Open curves and boundary points

Removing finitely many points changes both the count and middle compactly supported cohomology. The localization triangle identifies these two changes and retains the Frobenius permutation of nonrational boundary points.

Let $j:U\hookrightarrow C$ be the complement of a finite reduced closed subscheme $D$ in a smooth proper curve. Localization gives

$$
R\Gamma_c(U,E)\longrightarrow
R\Gamma(C,E)\longrightarrow
R\Gamma(D,E)\longrightarrow.
$$

Taking Frobenius traces yields

$$
\#U(\mathbf F_{q^n})
=\#C(\mathbf F_{q^n})-\#D(\mathbf F_{q^n}).
$$

The advantage over a set-theoretic subtraction is that the same equivariant triangle works with coefficients and correspondence actions.

If $U$ is geometrically connected and nonproper, $H_c^0(U,E)=0$ and $H_c^2(U,E)=E(-1)$. If $D$ consists of $r$ geometric points, the long exact sequence contains

$$
0\longrightarrow E
\longrightarrow E^r
\longrightarrow H_c^1(\bar U,E)
\longrightarrow H^1(\bar C,E)
\longrightarrow0,
$$

so $\dim H_c^1=2g+r-1$. When Frobenius permutes the boundary points, $E^r/E$ retains that permutation action; replacing it by a trivial representation would give wrong counts over extensions.

### 9.3 Singular curves and normalization

Normalization separates the branches of a singular curve, so the discrepancy is concentrated at finitely many points. Encoding that discrepancy by an equivariant exact sequence makes the branch permutation and its effect on every extension-field count explicit.

Let $C$ be a proper reduced curve, $\nu:\widetilde C\to C$ its normalization, $S$ the finite singular locus, and $\widetilde S=\nu^{-1}(S)$. There is a Frobenius-equivariant constructible exact sequence

$$
0\longrightarrow E_C
\longrightarrow \nu_*E_{\widetilde C}\oplus E_S
\longrightarrow \nu_*E_{\widetilde S}
\longrightarrow0.
$$

The last map subtracts branch values from the value at the singular point. Stalkwise exactness is immediate off $S$; at a singular point it says that a locally constant function on $C$ has one common value on all branches.

Taking alternating traces proves

$$
\#C(\mathbf F_{q^n})
=\#\widetilde C(\mathbf F_{q^n})
+\#S(\mathbf F_{q^n})
-\#\widetilde S(\mathbf F_{q^n}).
$$

At a split node, normalization replaces one rational point by two, so the node subtracts one from the normalized count. At a nonsplit node, Frobenius exchanges the two branches and the correction depends on $n$. The equivariant sequence records this automatically.

### 9.4 Endomorphisms of curves

Frobenius is only one endomorphism with a fixed-point formula. On a curve, the cohomological range is short enough to turn the general theorem into a concrete relation among degree, middle trace, and graph--diagonal intersection.

Let $f:C\to C$ be an endomorphism of a smooth proper geometrically connected curve. If its fixed points are isolated, Theorem 6.1 gives

$$
1-\operatorname{Tr}(f^*\mid H^1(\bar C,E))
+\deg(f)
=\sum_{x\in\operatorname{Fix}(f)}i_x(\Gamma_f,\Delta).
$$

Here $f^*$ is $1$ on $H^0$ and multiplication by $\deg(f)$ on $H^2$, since pullback multiplies the degree of a point class by $\deg(f)$. For an automorphism the last term is $1$.

If $f=\operatorname{id}$, the fixed locus is the whole curve, so the isolated formula is inapplicable. The intrinsic local term integrates the Euler class of the tangent bundle and gives $\chi(C)=2-2g$. Positive-dimensional fixed loci are therefore not counted by their number of geometric points.

## 10. Surfaces

Surfaces add a self-dual middle cohomology group, where divisors, transcendental classes, and geometric correspondences all act. The formula is unchanged, but interpreting its five terms requires more care.

### 10.1 The five cohomological degrees

Writing all five terms first prevents the middle degree from obscuring odd cohomology or the top fundamental class. Duality will later pair the terms symmetrically, but the trace formula itself sees each degree separately.

Let $S/\mathbf F_q$ be smooth, proper, and geometrically connected of dimension two. Put

$$
b_i=\dim_EH^i(\bar S,E),
\qquad
P_i(t)=\det(1-tF\mid H^i(\bar S,E)).
$$

Then $H^0=E$, $H^4=E(-2)$, and geometric Frobenius acts there by $1$ and $q^2$. Thus

$$
\#S(\mathbf F_{q^n})
=1-\operatorname{Tr}(F^n\mid H^1)
+\operatorname{Tr}(F^n\mid H^2)
-\operatorname{Tr}(F^n\mid H^3)+q^{2n}.
$$

Poincaré duality pairs $H^1$ with $H^3(2)$ and $H^2$ with itself up to twist. The odd-degree contributions are related, while $H^2$ carries its own reciprocal symmetry. The trace formula does not assert that $H^2$ is generated by divisor classes.

### 10.2 Divisors and the middle trace

Divisors give the most concrete part of surface middle cohomology. Their cup product is geometric intersection, so correspondences assembled from divisors can be traced through an explicit intersection matrix while leaving any nonalgebraic complement visible.

A divisor $D$ on $S$ has a class $[D]\in H^2(\bar S,E(1))$. If $D$ is defined over $\mathbf F_q$, its twisted class is fixed, so $F$ acts by $q$ on the corresponding untwisted line. For divisors $D,E$,

$$
\operatorname{Tr}_S([D]\smile[E])=D\cdot E.
$$

To prove the formula, move the cycles to proper intersection, use purity at each point, and apply the finite trace from its residue field. The local length is the intersection multiplicity, so their sum is $D\cdot E$. Consequently a correspondence built from divisor products has a middle-degree trace computable from the intersection matrix.

The full $H^2$ may contain nonalgebraic classes. A cycle correspondence still acts on them through its class on $S\times S$, and the Lefschetz number includes their trace. Replacing $H^2$ by a divisor span requires a separate justification.

### 10.3 Open and singular surfaces

Boundary divisors and singular curves are precisely the lower-dimensional pieces omitted by the smooth proper formula. Compact-support localization reduces both phenomena to curve and point calculations already established.

For an open immersion $j:U\hookrightarrow S$ with closed complement $D$, compact-support localization gives

$$
L(F^n,U)=L(F^n,S)-L(F^n,D).
$$

If $D$ is a normal-crossings divisor, its components and crossing points form an incidence complex. Frobenius may permute components and branches. The boundary trace on that complex gives $\#D(\mathbf F_{q^n})$, including inclusion--exclusion at crossings.

For a singular surface $Y$, let $U$ be its smooth locus and $Z=Y\setminus U$. Then $\dim Z\le1$. The formula on $Y$ follows from the smooth formula on $U$ and the curve formula on $Z$. This avoids assigning a smooth local term to a singular fixed point; the total singular contribution is computed by its own compactly supported cohomology.

If a resolution $\pi:\widetilde Y\to Y$ is available, one may compare the two spaces using the exceptional divisor and the locus where $\pi$ is an isomorphism. Exceptional curves contribute genuine factors, so no birational invariance of zeta functions is asserted.

### 10.4 Products of curves and a model computation

Products of curves are the best consistency test for a surface formula because their Künneth decomposition is completely visible. The calculation checks that tensor traces and the two factor fundamental classes reproduce the elementary product of point counts.

Let $S=C_1\times C_2$ for smooth proper geometrically connected curves. Künneth gives

$$
H^2(\bar S,E)
\cong E(-1)\oplus
\bigl(H^1(\bar C_1,E)\otimes H^1(\bar C_2,E)\bigr)
\oplus E(-1).
$$

If $a_{j,n}=\operatorname{Tr}(F^n\mid H^1(\bar C_j,E))$, the middle trace is $2q^n+a_{1,n}a_{2,n}$. Substitution in the five-term surface formula gives

$$
\#S(\mathbf F_{q^n})
=(q^n+1-a_{1,n})(q^n+1-a_{2,n}),
$$

exactly the product of the curve counts. This checks the Künneth signs, the two algebraic $E(-1)$ summands, and tensor-product trace simultaneously.

## 11. Trace formulas for correspondences

Point counting uses the graph of Frobenius, but arithmetic applications often insert a second geometric operator. A correspondence defined over the finite field commutes with Frobenius, so its action and the Galois action can be traced simultaneously. The geometry then counts fixed points of a twisted correspondence rather than rational points of the original variety.

### 11.1 Properly supported correspondences

Before tracing a correspondence, one must know that its pull--push action preserves compact support. This section isolates that geometric condition, especially at a compactification boundary where an apparently finite open correspondence may acquire new components.

Let $X/\mathbf F_q$ be a smooth variety of dimension $d$, and let

$$
c=(c_1,c_2):C\longrightarrow X\times X
$$

be defined over $\mathbf F_q$. Suppose $c_2$ is proper, pullback along $c_1$ preserves proper support (for example, $c_1$ is proper), and a cohomological correspondence $u:c_1^*K\to c_2^!K$ is given. If $X$ is nonproper, assume the correspondence extends to a compactification with no unwanted fixed contribution on the added boundary, or more intrinsically that it satisfies the support condition needed on $R\Gamma_c$.

These conditions define an operator $T_c$ on $R\Gamma_c(\bar X,K)$. Since all data descend to $\mathbf F_q$, $T_cF=FT_c$. Hence

$$
L(T_cF^n,X,K)
=\sum_i(-1)^i\operatorname{Tr}
(T_cF^n\mid H_c^i(\bar X,K))
$$

is defined for every $n$.

Properness must be attached to the correct projection. A finite correspondence on an open variety is proper over the open target, but a closure can acquire a boundary component. Such a component can create a fixed-locus contribution. It may be excluded only by a geometric argument, not by the fact that the original open diagram was finite étale.

### 11.2 Fixed points of a correspondence

Inserting Frobenius changes the diagonal equation into a twisted incidence equation between the two legs. Writing this equation explicitly identifies the geometric objects whose local multiplicities compute the simultaneous trace.

Twist the first leg by Frobenius:

$$
c^{(n)}=(F^n\circ c_1,c_2):C\longrightarrow X\times X.
$$

Its fixed locus is

$$
\operatorname{Fix}(c^{(n)})
=\{z\in C:c_2(z)=F^n(c_1(z))\}.
$$

With the pull--push convention defining $T_c$, this is the kernel whose cohomological action is $T_cF^n$ up to the harmless cyclic reordering of two commuting operators. The Lefschetz--Verdier theorem gives

$$
L(T_cF^n,X,K)
=\sum_ZLT_Z(c^{(n)},u^{(n)}),
$$

where $Z$ ranges over proper connected components of the fixed locus.

If the fixed points are isolated, $X$ and $C$ are smooth there, and the two legs meet the Frobenius-twisted diagonal transversely, each local term is the trace on the corresponding coefficient fiber. Nontransverse points carry refined intersection multiplicity. Thus “count fixed points of the correspondence” is accurate only after multiplicities and coefficient traces have been specified.

For a codimension-$d$ cycle $\Gamma$ on a smooth proper $X\times X$, the same formula takes the intersection form

$$
L(\Gamma_*F^n,X)
=\deg\bigl([\Gamma]\cdot[\Gamma_{F^n}]\bigr)
$$

when the intersection is proper. Refined intersection is understood. The identity correspondence $\Delta$ recovers the Frobenius point-count formula.

### 11.3 Finite étale and Hecke-type diagrams

Finite étale legs provide the cleanest arithmetic correspondences: extraordinary pullback becomes ordinary pullback, transfer is a sum over sheets, and transverse local terms are literal coefficient traces. This is the model for prime-to-level Hecke diagrams.

Suppose both legs in

$$
X\xleftarrow{c_1}C\xrightarrow{c_2}X
$$

are finite étale. Then $c_i^!=c_i^*$, and coefficient transport gives the operator

$$
T_c=c_{2*}c_1^*.
$$

At a transverse solution of $c_2(z)=F^nc_1(z)$, the local term is the trace of transport around the resulting coefficient loop. For constant coefficients it is one. Therefore the simultaneous trace counts solutions of the correspondence equation whenever all solutions are transverse.

If $c_2$ is finite flat of degree $m$, then $c_{2*}c_2^*=m$ on constant coefficients. This degree is scheme-theoretic; ramified points do not turn it into the number of distinct geometric sheets. In a composite of correspondences, refined intersection and the projection formula ensure that local multiplicities compose with the operator.

Prime-to-level correspondences on moduli surfaces often have exactly this form on the open locus. Once a compatible proper model of the correspondence is supplied, the operator acts on ordinary, compactly supported, and interior cohomology and commutes with Frobenius. The trace theorem does not itself construct that model; it computes the operator after proper support has been verified.

### 11.4 Projectors and simultaneous Frobenius traces

Correspondence algebras often contain projectors designed to isolate a desired cohomological constituent. Tracing the projector together with Frobenius extracts that constituent without requiring a basis, while denominators explain why the splitting may be only rational.

Let $e$ be an idempotent correspondence acting on a finite-dimensional $E$-cohomology complex and commuting with $F$. Then

$$
H_c^i(\bar X,E)=eH_c^i\oplus(1-e)H_c^i,
$$

and

$$
\operatorname{Tr}(eF^n\mid H_c^i)
=\operatorname{Tr}(F^n\mid eH_c^i).
$$

The equality follows by choosing a basis adapted to the idempotent decomposition. Thus a projector isolates the Frobenius trace on its cohomological summand, and the geometric side is the local trace of the projected correspondence.

If $e$ has denominators divisible by $\ell$, this splitting may exist over $E$ but not over $\mathbf Z_\ell$. Rational trace formulas remain valid; an integral direct summand is not implied. Likewise, an image such as interior cohomology need not split until a genuine projector is constructed.

## 12. Zeta functions and rationality

The trace formula turns infinitely many point counts into traces of powers of finitely many operators. A standard determinant identity then turns the exponential generating series into a rational function. This chapter proves both transformations and records the explicit curve and surface shapes.

### 12.1 The Euler product and point-count exponential

The zeta function has two complementary meanings: an Euler product indexed by closed points and an exponential series indexed by extension fields. Proving their equality makes it possible to feed the trace formula, which controls extension-field counts, into an invariant built from closed points.

For a finite-type $X/\mathbf F_q$, define

$$
Z(X,t)
=\exp\left(\sum_{n\ge1}
\#X(\mathbf F_{q^n})\frac{t^n}{n}\right).
$$

This belongs to $1+t\mathbf Z[[t]]$. It also has the Euler product

$$
Z(X,t)=\prod_{x\in|X|}(1-t^{\deg x})^{-1},
$$

where $|X|$ is the set of closed points.

**Proof.** A closed point of degree $r$ contributes $r$ geometric points fixed by $F^n$ exactly when $r\mid n$. Hence

$$
\#X(\mathbf F_{q^n})
=\sum_{r\mid n}rN_r,
$$

where $N_r$ is the number of degree-$r$ closed points. Therefore

$$
\sum_{n\ge1}\#X(\mathbf F_{q^n})\frac{t^n}{n}
=\sum_{r\ge1}N_r\sum_{m\ge1}\frac{t^{rm}}m
=-\sum_{r\ge1}N_r\log(1-t^r).
$$

Exponentiating gives the product. Every coefficient involves only finitely many closed points, so the formal manipulation is valid. $\square$

### 12.2 Cohomological factorization

The infinite list of traces $\operatorname{Tr}(F^n)$ is finite-dimensional data in disguise. The logarithm of a characteristic polynomial is the exact linear-algebra device that packages those traces and yields rationality.

For a finite-dimensional vector space $V$ and endomorphism $A$,

$$
\exp\left(\sum_{n\ge1}
\operatorname{Tr}(A^n)\frac{t^n}{n}\right)
=\det(1-tA)^{-1}.
$$

To prove this, extend scalars to split the characteristic polynomial. Both trace and determinant depend only on eigenvalues, with algebraic multiplicity. The identity becomes the product of $\exp(\sum_n\alpha^nt^n/n)=(1-\alpha t)^{-1}$. Since both sides descend, the original field is irrelevant.

Put

$$
P_{c,i}(X,t)
=\det(1-tF\mid H_c^i(\bar X,E)).
$$

The Grothendieck--Lefschetz formula and the determinant identity give

$$
\boxed{
Z(X,t)=\prod_iP_{c,i}(X,t)^{(-1)^{i+1}}.
}
$$

Only finitely many factors occur. This proves $Z(X,t)\in E(t)$. In fact it lies in $\mathbf Q(t)$. Indeed, its power-series coefficients are integers. A series is rational precisely when its infinite Hankel matrix of coefficients has finite rank. Since that matrix has rational entries, its rank is unchanged on extending scalars from $\mathbf Q$ to $E$: the same minors vanish. Hence rationality over $E$ implies rationality over $\mathbf Q$.

The individual $P_{c,i}$ can depend on the chosen coefficient field in ways not addressed here; the alternating product is the intrinsic zeta function. No independence-of-$\ell$ assertion for each separate cohomological polynomial is needed for rationality of $Z$.

### 12.3 Curves and surfaces explicitly

The general alternating product becomes especially informative in low dimension because the bottom and top factors are known. Displaying the remaining factors exposes the curve numerator and the surface middle denominator that later duality constrains.

For a smooth proper geometrically connected curve $C$,

$$
Z(C,t)=\frac{P_1(t)}{(1-t)(1-qt)},
\qquad
P_1(t)=\det(1-tF\mid H^1(\bar C,E)),
$$

and $\deg P_1=2g$. For an open curve $U=C\setminus D$,

$$
Z(U,t)=\frac{Z(C,t)}{Z(D,t)}.
$$

The polynomial contributed by $D$ records the Frobenius permutation of its geometric points.

For a smooth proper geometrically connected surface $S$,

$$
Z(S,t)
=\frac{P_1(t)P_3(t)}
{(1-t)P_2(t)(1-q^2t)}.
$$

The degrees are $b_i$. Duality relates $P_3$ to $P_1$ and makes $P_2$ reciprocal up to a sign, but it does not factor $P_2$ into algebraic and transcendental parts.

As a check,

$$
Z(\mathbf P^1,t)=\frac1{(1-t)(1-qt)}
$$

and Künneth gives

$$
Z(\mathbf P^1\times\mathbf P^1,t)
=\frac1{(1-t)(1-qt)^2(1-q^2t)}.
$$

### 12.4 Open--closed factorization

Zeta functions should multiply when a variety is partitioned into an open piece and its closed complement. The cohomological proof shows that this elementary counting rule is the determinant shadow of the localization triangle.

If $i:Z\hookrightarrow X$ is closed with open complement $j:U\hookrightarrow X$, then rational points decompose and

$$
Z(X,t)=Z(U,t)Z(Z,t).
$$

Cohomologically this follows from the localization triangle and determinant multiplicativity. If

$$
C'\to C\to C''\to
$$

is an equivariant triangle of perfect complexes, then

$$
\prod_i\det(1-tF\mid H^i(C))^{(-1)^{i+1}}
$$

is the product of the analogous expressions for $C'$ and $C''$. One proves this by filtering the long exact cohomology sequence into short exact sequences and using multiplicativity of determinant.

For singular curves, the normalization sequence therefore yields

$$
Z(C,t)=Z(\widetilde C,t)\frac{Z(S,t)}{Z(\widetilde S,t)}.
$$

For a resolution of a surface that is an isomorphism off a closed locus $Z$, with exceptional inverse image $E_Z$, the same argument gives

$$
Z(\widetilde S,t)Z(Z,t)=Z(S,t)Z(E_Z,t).
$$

This formula measures rather than suppresses the exceptional contribution.

## 13. Functional equations

Rationality uses only traces of powers. A functional equation needs a symmetry among eigenvalues, and that symmetry comes from Poincaré duality. Smoothness identifies the dualizing complex with a Tate twist, while properness identifies compact and ordinary cohomology. Both hypotheses are essential for a self-reciprocal zeta function.

### 13.1 Reciprocal characteristic polynomials

A functional equation begins with a degree-by-degree eigenvalue pairing. Translating Poincaré duality into an exact identity between characteristic polynomials fixes the powers of $q$, $t$, and the determinant sign before the factors are multiplied.

Let $X/\mathbf F_q$ be smooth, proper, geometrically connected of pure dimension $d\le2$. Put

$$
V_i=H^i(\bar X,E),
\quad b_i=\dim V_i,
\quad \delta_i=\det(F\mid V_i),
\quad P_i(t)=\det(1-tF\mid V_i).
$$

Poincaré duality is an $F$-equivariant perfect pairing

$$
V_i\times V_{2d-i}\longrightarrow E(-d),
$$

and $F$ acts by $q^d$ on the target. Thus if $\alpha$ is an eigenvalue on $V_i$, the paired eigenvalue on $V_{2d-i}$ is $q^d/\alpha$, with multiplicity. It follows directly that

$$
P_{2d-i}(t)
=(-1)^{b_i}q^{db_i}t^{b_i}\delta_i^{-1}
P_i\left(\frac1{q^dt}\right).
$$

Indeed, both sides are the product of $1-q^dt/\alpha$ over the eigenvalues $\alpha$, after extracting the scalar from $P_i(1/(q^dt))$.

In middle degree, $\delta_d^2=q^{db_d}$. If $d$ is odd, the middle pairing is alternating, $b_d$ is even, and the determinant of a symplectic similitude is $q^{db_d/2}$. If $d$ is even, the pairing is symmetric and

$$
\delta_d=\eta q^{db_d/2},
\qquad \eta\in\{1,-1\}.
$$

For surfaces this sign is the normalized determinant of Frobenius on $H^2$.

### 13.2 The functional equation for smooth proper varieties

The reciprocal identities now have to be multiplied with alternating exponents. The only delicate scalar is the alternating product of Frobenius determinants, whose middle-degree sign distinguishes surfaces from curves.

Let

$$
\chi(X)=\sum_i(-1)^ib_i.
$$

**Theorem 13.1.** There is a sign $\varepsilon_X\in\{1,-1\}$ such that

$$
\boxed{
Z\left(X,\frac1{q^dt}\right)
=\varepsilon_Xq^{d\chi(X)/2}t^{\chi(X)}Z(X,t).
}
$$

**Proof.** Write $s_i=(-1)^{i+1}$. The reciprocal-polynomial identity gives

$$
P_i\left(\frac1{q^dt}\right)
=(-1)^{b_i}\delta_iq^{-db_i}t^{-b_i}P_{2d-i}(t).
$$

Multiply with exponents $s_i$. Since $s_{2d-i}=s_i$, the polynomial factors reproduce $Z(X,t)$. The signs contribute $(-1)^{\chi(X)}$, and the powers of $q$ and $t$ outside the determinants contribute $q^{d\chi(X)}t^{\chi(X)}$.

It remains to evaluate $A=\prod_i\delta_i^{s_i}$. Pairing degrees $i$ and $2d-i$ gives $\delta_i\delta_{2d-i}=q^{db_i}$. In middle degree use the alternating or symmetric determinant calculation of Section 13.1. Collecting exponents gives

$$
A=\eta_Xq^{-d\chi(X)/2}
$$

for a sign $\eta_X$. Therefore the total scalar is

$$
(-1)^{\chi(X)}\eta_Xq^{d\chi(X)/2}t^{\chi(X)}.
$$

Set $\varepsilon_X=(-1)^{\chi(X)}\eta_X$. $\square$

The half exponent is always integral in the cases at hand: for $d=2$ this is obvious, and for $d=1$ the Euler characteristic of a proper smooth curve is even.

### 13.3 Curves

For curves the middle pairing is alternating, so its similitude determinant has no residual sign. This collapses the general functional equation to the classical reciprocal numerator and makes the exponent depend only on the genus.

For a smooth proper geometrically connected genus-$g$ curve, the alternating middle pairing has determinant multiplier $q^g$. Hence

$$
P_1(t)=q^gt^{2g}P_1\left(\frac1{qt}\right)
$$

and the sign in the zeta functional equation is $+1$. Since $\chi(C)=2-2g$,

$$
Z\left(C,\frac1{qt}\right)
=q^{1-g}t^{2-2g}Z(C,t).
$$

For $\mathbf P^1$, direct substitution gives $Z(1/(qt))=qt^2Z(t)$, agreeing with $g=0$.

### 13.4 Surfaces and the middle sign

Surface middle cohomology is paired symmetrically, allowing a normalized determinant sign that cannot be discarded. Isolating it gives both the reciprocal law for $P_2$ and the correct global sign, as projective space already demonstrates.

For a smooth proper geometrically connected surface, put $b_2=\dim H^2$ and

$$
\eta_S=q^{-b_2}\det(F\mid H^2(\bar S,E))\in\{1,-1\}.
$$

Then

$$
P_2(t)=(-1)^{b_2}\eta_Sq^{b_2}t^{b_2}
P_2\left(\frac1{q^2t}\right).
$$

The whole zeta function satisfies

$$
Z\left(S,\frac1{q^2t}\right)
=(-1)^{\chi(S)}\eta_Sq^{\chi(S)}t^{\chi(S)}Z(S,t).
$$

For $\mathbf P^2$, $\chi=3$ and $\eta_S=1$, so the sign is negative. Directly,

$$
Z(\mathbf P^2,t)=\frac1{(1-t)(1-qt)(1-q^2t)}
$$

has exactly this transformation. The sign is therefore structural, not a defect in normalization.

### 13.5 Why open varieties require a paired statement

The self-functional equation is not a formal consequence of having a trace formula. On an open variety duality exchanges compactly supported and ordinary cohomology, so the correct reciprocity relates two different complexes rather than the zeta function to itself.

For smooth nonproper $U$ of dimension $d$, Poincaré duality pairs

$$
H_c^i(\bar U,E)
\times H^{2d-i}(\bar U,E(d))
\longrightarrow E.
$$

Thus a compact-support polynomial is reciprocal to an **ordinary** cohomology polynomial:

$$
P_{c,i}(t)
=(-1)^{b_{2d-i}}q^{db_{2d-i}}t^{b_{2d-i}}
\det(F\mid H^{2d-i})^{-1}
P_{2d-i}^{\mathrm{ord}}\left(\frac1{q^dt}\right),
$$

with dimensions matched by duality. Unless $U$ is proper, ordinary and compactly supported complexes are different, so this is not generally a self-functional equation for $Z(U,t)$.

For example, $Z(\mathbf A^1,t)=(1-qt)^{-1}$. Substitution $t\mapsto1/(qt)$ does not return the same rational function times the proper-curve factor predicted above. Compact support explains the point count, while the missing point at infinity prevents self-duality.

For singular proper varieties, Verdier duality pairs the constant sheaf with its Verdier dual, not necessarily with a shifted Tate twist of itself. A self-functional equation therefore requires an appropriate self-duality statement; properness alone does not supply one.

## 14. Coefficients, families, and good reduction

The trace formula is most reusable when it travels with coefficient sheaves and through smooth proper families. This chapter packages those extensions while keeping separate the roles of base change, local terms, and duality.

### 14.1 L-functions of constructible sheaves

The constant-sheaf zeta function is only the first member of a wider construction. Local Frobenius actions on a coefficient complex produce Euler factors whose global rationality follows from the same sheaf--function trace identity.

Let $K_0$ be a constructible $E$-complex on $X_0/\mathbf F_q$ with Frobenius structure. Define

$$
L(X_0,K_0,t)
=\prod_{x\in|X_0|}
\det\left(1-t^{\deg x}F_x
\mid K_{\bar x}\right)^{-1},
$$

where $F_x$ is geometric Frobenius of the residue field $k(x)$ and determinant means the alternating determinant across cohomological degrees. Expanding formal logarithms and grouping geometric points over a closed point gives

$$
\log L(X_0,K_0,t)
=\sum_{n\ge1}\frac{t^n}{n}
\sum_{y\in X_0(\mathbf F_{q^n})}
\operatorname{Tr}(F^n\mid K_{\bar y}).
$$

Theorem 8.3 therefore proves

$$
L(X_0,K_0,t)
=\prod_i
\det(1-tF\mid H_c^i(\bar X,K))^{(-1)^{i+1}}.
$$

Hence this $L$-function is rational. For $K_0=E$ it is $Z(X_0,t)$. If $K_0$ is self-dual up to a Tate twist and $X_0$ is smooth proper, Poincaré duality gives a corresponding functional equation. The shift, twist, and dual coefficient must all be included; self-duality is not automatic for a lisse sheaf.

### 14.2 Base change in a family

Fiberwise trace formulas become useful in arithmetic families only when their operators and pairings specialize compatibly. Smooth proper base change supplies that transport, while compact support records exactly what survives when the total space is open.

Let $f:X\to S$ be smooth and proper of relative dimension at most two over a connected base on which $\ell$ is invertible, and let $K$ be lisse. Proper and smooth base change make each $R^if_*K$ lisse and identify its stalk with fiber cohomology. Cup products, trace, Künneth, and properly supported correspondences commute with arbitrary base change.

Consequently a correspondence $c$ over $S$ defines an endomorphism of the lisse derived direct image $Rf_*K$. At a finite-field point $s$, the simultaneous operator $T_cF_s^n$ on the fiber is the specialization of the global correspondence action followed by geometric Frobenius. The trace formula computes it from the fixed locus on $X_s$.

The proof is a diagram chase at the derived level. Pullback carries the cohomological correspondence to the fiber; proper base change commutes with its pushforward; the projection formula commutes with its coefficient map; and base change for the extraordinary trace carries the global trace class to the fiber trace class. Taking cohomology then preserves the identity.

If the family is not proper, compactly supported direct image still commutes with base change after a compactification, but ordinary cohomology can vary with the boundary. A relative normal-crossings boundary with controlled local monodromy is sufficient in the curve and surface cases; absent such control, only the compact-support statement is automatic.

### 14.3 Good reduction and local factors

Good reduction converts an arithmetic Frobenius problem on the generic fiber into a geometric Frobenius problem over a finite field. The value of the trace formula here is therefore computational transport, not the construction of a model or an eigenvalue estimate.

Suppose a smooth proper curve or surface over the fraction field of a henselian discrete valuation ring extends to a smooth proper model, with residue field $\mathbf F_q$ and $\ell$ invertible. Smooth proper base change identifies geometric generic cohomology with special-fiber cohomology and makes inertia act trivially. The unramified geometric Frobenius on the generic representation corresponds to geometric Frobenius on the special fiber.

Therefore the good-reduction local polynomial

$$
P_i(t)=\det(1-tF\mid H^i(\bar X_\eta,E))
$$

can be computed on the special fiber. A correspondence extending properly over the model commutes with this comparison, so the same is true of

$$
\det(1-tT_cF\mid H^i).
$$

This is a transport statement. The trace formula evaluates alternating traces on the special fiber; it does not by itself prove absolute-value bounds for eigenvalues or construct a smooth model.

### 14.4 A hypothesis checklist

Before applying a trace or zeta formula, the following points must be settled.

1. The prime $\ell$ must be invertible on the schemes involved.
2. Compact support is required for a nonproper space in the point-count formula.
3. A correspondence must have proper support over the target, including at the boundary of any compactification.
4. The fixed locus must be proper for its local trace to integrate to a scalar.
5. A point contributes a bare stalk trace only under the clean condition $1-df$ invertible; otherwise refined multiplicity is present.
6. The smooth-stratum argument, rather than a guessed point term, handles singularities.
7. Integral coefficient towers require uniform boundedness, finiteness, and derived inverse limits; rationalization occurs afterward.
8. A self-functional equation requires smooth proper self-duality. Open varieties pair compact with ordinary cohomology, and singular varieties use the dualizing complex.
9. A transpose correspondence is the Poincaré adjoint; an arithmetic involution or polarization is extra data.
10. Every displayed Frobenius polynomial here uses geometric Frobenius. Arithmetic Frobenius inverts its eigenvalues.

Each item marks a genuine mathematical transition. Checking them prevents the most common trace-formula errors: boundary terms, inverted eigenvalues, missing intersection multiplicities, and unjustified self-duality.

## 15. The reusable trace-formula package

The purpose of the final chapter is to consolidate the arguments into one theorem that can be cited without suppressing its hypotheses. It also marks the exact boundary between trace formulas and the weight theory that follows them.

### 15.1 The complete theorem

Later arguments need a single citation that preserves every support, smoothness, and normalization condition proved above. The following package collects the results without turning their distinct hypotheses into one overstrong slogan.

**Theorem 15.1 (low-dimensional trace and zeta package).** Let $X$ be a separated finite-type scheme of dimension at most two over $\mathbf F_q$, and let $\ell\ne\operatorname{char}\mathbf F_q$.

1. The compactly supported complexes $R\Gamma_c(\bar X,\Lambda_m)$, $R\Gamma_c(\bar X,\mathbf Z_\ell)$, and $R\Gamma_c(\bar X,E)$ are bounded in the established ranges; the integral complex is perfect in the curve and surface cases under the standing finiteness hypotheses.
2. Compactly supported Künneth is a derived isomorphism at finite and integral levels. Over $E$ it yields the ordinary direct-sum Künneth decomposition. It respects Frobenius, traces, cycle classes, and fundamental classes.
3. A properly supported cohomological correspondence with proper fixed locus satisfies the Lefschetz--Verdier formula: its alternating compact-support trace is the sum of its local terms.
4. At a smooth isolated fixed point with $1-df$ invertible and lisse coefficients, the local term is the stalk trace. A nontransverse isolated point contributes the refined graph--diagonal intersection term. A positive-dimensional fixed component contributes its intrinsic Verdier local trace.
5. For every $n\ge1$,

   $$
   \#X(\mathbf F_{q^n})
   =\sum_i(-1)^i\operatorname{Tr}
   (F^n\mid H_c^i(\bar X,E)).
   $$

   More generally, a constructible Frobenius complex satisfies the sheaf--function trace formula with stalk supertraces.
6. Properly supported algebraic correspondences act by pull--cup--push, compose by refined convolution, commute with Frobenius when defined over $\mathbf F_q$, and satisfy the corresponding fixed-locus trace formula. Transpose correspondences are adjoint under Poincaré duality.
7. The zeta function is rational and has the cohomological expression

   $$
   Z(X,t)=\prod_i
   \det(1-tF\mid H_c^i(\bar X,E))^{(-1)^{i+1}}.
   $$

   Open--closed decompositions multiply zeta functions.
8. If $X$ is smooth, proper, and geometrically connected of pure dimension $d\le2$, then

   $$
   Z\left(X,\frac1{q^dt}\right)
   =\varepsilon_Xq^{d\chi(X)/2}t^{\chi(X)}Z(X,t),
   \qquad \varepsilon_X\in\{1,-1\}.
   $$

   For curves $\varepsilon_X=1$; for surfaces it is $(-1)^{\chi(X)}$ times the normalized determinant sign on $H^2$.
9. All statements commute with smooth proper base change and with specialization at good reduction. A properly extending correspondence is transported with them.

**Proof.** Clause 1 is the bounded finiteness and perfectness package for compact support. Clause 2 is Theorem 3.1 and its derived-limit passage. Clause 3 is Theorem 6.1, while Clause 4 is Proposition 7.1 and refined intersection. Clause 5 follows from Frobenius transversality on smooth strata and localization induction. Clause 6 follows from cycle-class compatibility, projection, and the cohomological-correspondence theorem. Clause 7 is the trace-of-powers determinant identity, with rationality over $\mathbf Q$ obtained from the Hankel-rank argument. Clause 8 is Theorem 13.1. Clause 9 follows from proper and smooth base change for compact support, duality, trace, and correspondences. $\square$

### 15.2 Final synthesis

The trace formula succeeds because three languages describe the same scalar. Linear algebra calls it the alternating trace of an endomorphism of a perfect complex. Duality calls it evaluation of a kernel against the diagonal coevaluation. Geometry calls it the integral of local classes on a fixed locus. Künneth and the projection formula identify these descriptions.

Frobenius makes the local geometry exceptionally clean. Rational points are its fixed points, its differential vanishes, and every smooth fixed point has multiplicity one. Stratification and localization extend this clean calculation to singular curves and surfaces without pretending their local geometry is smooth. Constructible coefficients replace the number one by a stalk trace, while algebraic correspondences replace rational points by solutions of a twisted correspondence equation.

Once all powers of Frobenius are known, a determinant identity makes the zeta function rational. Once Poincaré duality is added, complementary eigenvalues multiply to $q^d$ and the zeta function becomes reciprocal, with the middle determinant supplying the surface sign. Properness and smoothness are exactly what turn the paired duality statement into a self-functional equation.

Nothing in these arguments estimates the complex absolute values of Frobenius eigenvalues. Trace formulas organize counts, duality organizes reciprocal pairs, and weights control size. Keeping those achievements distinct leaves a complete and stable foundation for the weight and hard-Lefschetz theory that follows.
