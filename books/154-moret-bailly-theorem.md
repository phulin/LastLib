# Moret–Bailly’s Theorem

## Contents

1. [The local-to-global point problem](#1-the-local-to-global-point-problem)
   - [Local points without a global rational point](#11-local-points-without-a-global-rational-point)
   - [Why a finite extension is the right output](#12-why-a-finite-extension-is-the-right-output)
   - [Places, embeddings, and the strong local requirement](#13-places-embeddings-and-the-strong-local-requirement)
   - [The shape of the argument](#14-the-shape-of-the-argument)
2. [Closed points and finite extensions](#2-closed-points-and-finite-extensions)
   - [One point, one residue field](#21-one-point-one-residue-field)
   - [Separable degree and smooth varieties](#22-separable-degree-and-smooth-varieties)
   - [Base change to a completion](#23-base-change-to-a-completion)
   - [Points and zero-cycles are not the same](#24-points-and-zero-cycles-are-not-the-same)
3. [Reduced cycles and symmetric powers](#3-reduced-cycles-and-symmetric-powers)
   - [Why unordered configurations appear](#31-why-unordered-configurations-appear)
   - [The configuration space](#32-the-configuration-space)
   - [The universal finite étale family](#33-the-universal-finite-étale-family)
   - [Smoothness and local coordinates](#34-smoothness-and-local-coordinates)
   - [Hilbert schemes and the boundary](#35-hilbert-schemes-and-the-boundary)
4. [Encoding local conditions](#4-encoding-local-conditions)
   - [Local opens and conjugate points](#41-local-opens-and-conjugate-points)
   - [Finite étale local algebras](#42-finite-étale-local-algebras)
   - [Building local reduced cycles](#43-building-local-reduced-cycles)
   - [Degree, repetition, and compatibility](#44-degree-repetition-and-compatibility)
   - [Archimedean cycle types](#45-archimedean-cycle-types)
   - [Weil restriction and finite local packets](#46-weil-restriction-and-finite-local-packets)
   - [Arithmetic neighborhoods at finite and real places](#47-arithmetic-neighborhoods-at-finite-and-real-places)
5. [The irreducible-cycle approximation theorem](#5-the-irreducible-cycle-approximation-theorem)
   - [Statement of the engine](#51-statement-of-the-engine)
   - [Étale coordinates near finitely many cycles](#52-étale-coordinates-near-finitely-many-cycles)
   - [Weak approximation in the parameter space](#53-weak-approximation-in-the-parameter-space)
   - [The Hilbert condition that forces a field](#54-the-hilbert-condition-that-forces-a-field)
   - [Proof of the engine](#55-proof-of-the-engine)
   - [What the theorem does and does not say](#56-what-the-theorem-does-and-does-not-say)
6. [Moret–Bailly’s theorem](#6-moretbaillys-theorem)
   - [The exact local-open statement](#61-the-exact-local-open-statement)
   - [Proof of the main theorem](#62-proof-of-the-main-theorem)
   - [Reading the completion condition](#63-reading-the-completion-condition)
   - [The split form](#64-the-split-form)
   - [Degree and non-Galois warnings](#65-degree-and-non-galois-warnings)
7. [Disjointness and prescribed local algebras](#7-disjointness-and-prescribed-local-algebras)
   - [Disjointness as a Hilbert condition](#71-disjointness-as-a-hilbert-condition)
   - [Avoiding a prescribed finite extension](#72-avoiding-a-prescribed-finite-extension)
   - [Exact local algebra prescriptions](#73-exact-local-algebra-prescriptions)
   - [Splitting and one-place behavior](#74-splitting-and-one-place-behavior)
   - [A simultaneous finite-place theorem](#75-a-simultaneous-finite-place-theorem)
8. [The totally real theorem](#8-the-totally-real-theorem)
   - [Total reality is an all-embeddings condition](#81-total-reality-is-an-all-embeddings-condition)
   - [Archimedean neighborhoods](#82-archimedean-neighborhoods)
   - [Proof of the totally real variant](#83-proof-of-the-totally-real-variant)
   - [Reality, disjointness, and finite local behavior together](#84-reality-disjointness-and-finite-local-behavior-together)
   - [Constructing the auxiliary field itself](#85-constructing-the-auxiliary-field-itself)
   - [What changes when the base is not totally real](#86-what-changes-when-the-base-is-not-totally-real)
9. [Finite étale covers, twists, and monodromy](#9-finite-étale-covers-twists-and-monodromy)
   - [Lifting local conditions through a cover](#91-lifting-local-conditions-through-a-cover)
   - [Connected components and twists](#92-connected-components-and-twists)
   - [Selecting a monodromy class](#93-selecting-a-monodromy-class)
   - [Limits of the cover variant](#94-limits-of-the-cover-variant)
10. [Avoidance and density](#10-avoidance-and-density)
   - [Removing a closed subset](#101-removing-a-closed-subset)
   - [Zariski density over varying fields](#102-zariski-density-over-varying-fields)
   - [Avoidance together with local constraints](#103-avoidance-together-with-local-constraints)
   - [Why one fixed extension is different](#104-why-one-fixed-extension-is-different)
11. [Examples and failures](#11-examples-and-failures)
   - [Affine space with coefficient conditions](#111-affine-space-with-coefficient-conditions)
   - [Curves](#112-curves)
   - [A frame variety](#113-a-frame-variety)
   - [Counterexamples and boundary phenomena](#114-counterexamples-and-boundary-phenomena)
12. [A practical package for arithmetic geometry](#12-a-practical-package-for-arithmetic-geometry)
   - [Local inputs from a moduli problem](#121-local-inputs-from-a-moduli-problem)
   - [Auxiliary primes and residue-characteristic primes](#122-auxiliary-primes-and-residue-characteristic-primes)
   - [The reusable theorem](#123-the-reusable-theorem)
   - [A verification checklist](#124-a-verification-checklist)
   - [Conclusion](#125-conclusion)

## 1. The local-to-global point problem

### 1.1 Local points without a global rational point

Let $K$ be a number field and let $X$ be a variety over $K$. Throughout this book, varieties are separated and quasi-projective; this is the setting in which the symmetric powers used below exist without qualification. At a finite collection $S$ of places, suppose that one has found local points

$$
x_v\in X(K_v),\qquad v\in S,
$$

and, more precisely, nonempty open neighborhoods $\Omega_v\subset X(K_v)$. The arithmetic problem is to turn these separate local choices into one algebraic point. The word *open* is essential. A point in a completion usually carries more information than the application truly needs: integrality, a nonsingular reduction, a prescribed isomorphism class, or inequalities at a real place are stable under a small perturbation. Encoding the requirement by $\Omega_v$ records exactly that stability.

It is generally unreasonable to ask for a point of $X(K)$. Rational points can be empty for global reasons even when every completion has a point. Smooth conics over number fields obey the local-to-global principle, but already genus-one torsors, higher-genus curves, and higher-dimensional varieties exhibit failures of existence; failures of weak approximation are more common still. Even when $X(K)$ is nonempty, it need not be dense in a product of the $X(K_v)$. Thus weak approximation on affine space cannot simply be transferred to an arbitrary $X$.

The theorem of this book changes the output rather than weakening the local input. It produces a finite extension $L/K$ and a point

$$
x\in X(L)
$$

whose images at the designated completions lie in the prescribed opens. The extension is chosen as part of the construction. That freedom is precisely what makes the theorem powerful enough for moduli problems.

### 1.2 Why a finite extension is the right output

Every nonempty variety of finite type over $K$ has closed points, and a closed point has a finite residue field over $K$. So passing to finite extensions is not an artificial escape: it is the field-theoretic meaning of allowing arbitrary closed points. The challenge is not mere existence of a closed point. It is to choose one whose conjugates behave correctly at all places in $S$, whose field avoids prescribed extensions, and, in the totally real setting, whose every embedding is real.

The flexibility comes from degree. A single $K$-rational point has one branch at each place. A degree-$d$ closed point has $d$ geometric conjugates. Locally these conjugates may split into several packets, one for each place of the residue field above $v$. By choosing $d$ sufficiently large, one can first build local packets with the desired behavior and then globalize them.

This does not mean that degree is irrelevant. A variety can have an index greater than one, so the degrees of all of its closed points may share a nontrivial common divisor. Local étale algebras also have fixed ranks. The proof therefore chooses a common admissible degree after the local data have been expressed as zero-cycles. It never asserts that every sufficiently large integer is a possible degree without an index hypothesis.

### 1.3 Places, embeddings, and the strong local requirement

Let $L/K$ be finite and $v$ a place of $K$. There is a canonical decomposition

$$
L\otimes_K K_v\simeq\prod_{w\mid v}L_w.
$$

If $x\in X(L)$, base change gives a tuple $x_w\in X(L_w)$. If an open condition is originally stated only in $X(K_v)$, then it makes literal sense for every $w$ only when $L_w=K_v$, equivalently when $v$ splits completely in $L$. In that case

$$
L\otimes_KK_v\simeq K_v^{[L:K]},
$$

and every $K$-embedding $L\hookrightarrow\overline K_v$ actually has image in $K_v$.

There are two useful formulations. In the **split formulation**, one requires complete splitting and asks that every conjugate point belong to $\Omega_v$. In the **local-algebra formulation**, one prescribes a rank-$d$ finite étale $K_v$-algebra

$$
A_v=\prod_i E_{v,i}
$$

and open subsets in the corresponding spaces $X(E_{v,i})$. The conclusion is an isomorphism $L\otimes_KK_v\simeq A_v$ carrying the local components of $x$ into those opens. The second formulation contains the first by taking $A_v=K_v^d$.

The adjective “every” is a major strengthening. Producing one place $w\mid v$ with acceptable $x_w$ is not enough for applications that later choose embeddings without controlling which prime they induce. Our construction arranges the entire tensor product, not one favored factor.

### 1.4 The shape of the argument

The proof has four conceptual stages.

First, local points are expanded into reduced effective zero-cycles of one common degree. Second, these cycles are placed in the smooth configuration locus of a symmetric power. Third, local coordinates and weak approximation globalize the cycle parameters. Fourth, Hilbert irreducibility is imposed on the universal degree-$d$ family so that the resulting finite étale algebra is connected. A connected finite étale algebra over $K$ is a field, and therefore the global cycle is one closed point rather than a sum of smaller closed points.

The last step is decisive. Approximation alone naturally produces zero-cycles. Hilbert irreducibility is what turns an unordered collection into the conjugates of a single field-valued point. Book 153 established the simultaneous local and Hilbert machinery; here it is applied to a geometric parameter space whose universal fiber is the desired point.

The geometric inputs have equally precise roles. Book 8 supplies ample embeddings, symmetric powers, configuration spaces, and their universal finite étale families. Book 10 supplies the effective descent used for finite free families and quotients by the free permutation action. Book 58 explains why a compatible *infinite* formal construction would require proper algebraization and an ample line bundle. We do not need that stronger passage here: all interpolation below is of finite order and takes place in finite-dimensional spaces of sections. The decisive moving argument first slices out one global curve meeting every local open and then moves a divisor in a sufficiently divisible power of one line bundle on that fixed curve. This separation is important; trying to concentrate a complete intersection by prescribing a jet of order equal to its whole intersection number would exceed the available section space in dimension greater than one.

## 2. Closed points and finite extensions

### 2.1 One point, one residue field

Let $X$ be a finite-type $K$-scheme. A closed point $P\in X$ has residue field

$$
\kappa(P)=\mathcal O_{X,P}/\mathfrak m_P,
$$

a finite extension of $K$. The canonical morphism

$$
\operatorname{Spec}\kappa(P)\longrightarrow X
$$

is a $\kappa(P)$-valued point. Conversely, if $L/K$ is finite and $x\in X(L)$, the image of $\operatorname{Spec}L\to X$ is a closed point $P$, together with a $K$-embedding $\kappa(P)\hookrightarrow L$. It is a closed immersion exactly when $L=\kappa(P)$ through this embedding.

Thus an $L$-point need not have degree $[L:K]$: it may descend to a smaller field. The construction below produces a closed point $P$ and then sets $L=\kappa(P)$. This guarantees that the degree is genuine and prevents an artificial enlargement from obscuring local splitting.

### 2.2 Separable degree and smooth varieties

Because $K$ has characteristic zero, every finite extension of $K$ is separable. Accordingly, a degree-$d$ closed point has $d$ distinct geometric conjugates after base change to an algebraic closure. More generally, over a nonperfect field one would have to separate the residue degree into separable and inseparable parts; symmetric configuration spaces see only the separable sheets. The number-field hypothesis removes that complication.

Smoothness supplies the geometric analogue. If $X/K$ is smooth, then it is geometrically reduced, every closed point lies in the smooth locus, and small deformations of a reduced collection of points remain reduced. If $X$ is also geometrically connected, then $X_{\overline K}$ is irreducible: irreducible components of a smooth scheme are disjoint open-and-closed pieces, so geometric connectedness leaves only one.

This irreducibility is what makes the ordered configuration space geometrically connected. Without it, a Hilbert specialization may be trapped in one constant component, and disjointness from the corresponding field of constants can be impossible.

### 2.3 Base change to a completion

Let $P$ be a closed point with $L=\kappa(P)$. At a place $v$ of $K$,

$$
\operatorname{Spec}(L\otimes_KK_v)
=\coprod_{w\mid v}\operatorname{Spec}L_w.
$$

The base-changed point is therefore not one point over $K_v$ unless there is only one $w$. It is a finite étale zero-dimensional $K_v$-scheme. After extending further to $\overline K_v$, it becomes the set of all $K$-embeddings $L\hookrightarrow\overline K_v$.

Suppose $L\otimes_KK_v\simeq K_v^d$. Then there are $d$ embeddings $\sigma:L\hookrightarrow K_v$, and $P$ gives $d$ points $x^\sigma\in X(K_v)$. Requiring all of them to lie in $\Omega_v$ is precisely the statement that the entire local zero-cycle is supported in $\Omega_v$.

For a general factor $E/K_v$, an embedding $E\hookrightarrow\overline K_v$ yields a geometric conjugate. If $U\subset X(E)$ is an open condition, one must say whether it is invariant under the $K_v$-embeddings of $E$. The clean algebraic formulation specifies a point of $X(E)$ and a neighborhood of its full conjugacy orbit; then the statement is independent of a chosen labeling.

Consider a cubic closed point. At a finite place its algebra can have any of the shapes

$$
K_v^3,\qquad K_v\times E_2,\qquad E_3,
$$

where $E_i/K_v$ is a separable field extension of degree $i$; ramified and unramified choices refine the last two shapes. In the first case there are three places above $v$, all of local degree one. In the second there are two places, of local degrees one and two. In the third there is one place. An embedding into $\overline K_v$ still yields three geometric points in every case, but the local Galois group groups them into orbits of sizes $(1,1,1)$, $(1,2)$, or $(3)$. This orbit picture is exactly what the factors of $L\otimes_KK_v$ record.

The topology also depends on the algebra. A neighborhood in $X(E_2)$ is not a neighborhood in $X(K_v)$. When a theorem says that a point is “close to $x_v$,” it must first specify the completion in which closeness is measured. The split theorem avoids this ambiguity by making every factor equal to $K_v$; the algebra form keeps the factors explicit.

### 2.4 Points and zero-cycles are not the same

An effective zero-cycle on $X$ is a finite sum

$$
z=\sum_i n_i[P_i],\qquad n_i\ge 0.
$$

Its degree is $\sum_i n_i[\kappa(P_i):K]$. A degree-$d$ cycle may be reducible, may have multiplicities, and its coordinate algebra may be a product. By contrast, one closed point of degree $d$ is reduced and its coordinate algebra is one field.

For example, if $P,Q\in X(K)$ are distinct, then $[P]+[Q]$ is a reduced degree-two cycle, but it does not define a quadratic field. Its algebra is $K\times K$. A nonreduced cycle $2[P]$ is different again. Confusing either with a degree-two closed point would invalidate every later claim about completions or disjointness.

The proof deliberately works first with reduced cycles, because they form a finite étale family. It then imposes connectedness of the universal fiber. Reducedness says the algebra is finite étale; connectedness says it is a field. Both properties are needed.

## 3. Reduced cycles and symmetric powers

### 3.1 Why unordered configurations appear

A degree-$d$ closed point becomes $d$ distinct points over $\overline K$, permuted transitively by the absolute Galois group. No conjugate is preferred. The natural parameter space must therefore forget the ordering while remembering the collection. This is the role of the $d$-th symmetric power

$$
\operatorname{Sym}^d(X)=X^d/S_d.
$$

For a quasi-projective variety this quotient exists as a variety; for a general separated finite-type variety one works on a quasi-projective neighborhood containing the finitely many points used in the construction. Since the theorem is insensitive to shrinking around those points, this causes no loss.

The whole symmetric power contains cycles with repeated points and, in higher dimension, may be singular along complicated collision strata. We do not use all of it. We use the open locus where the $d$ geometric points are distinct.

### 3.2 The configuration space

Let

$$
\operatorname{Conf}_d(X)=X^d\setminus\bigcup_{i<j}\Delta_{ij}
$$

be the ordered configuration space. The symmetric group acts freely, and the quotient

$$
Q_d(X)=\operatorname{Conf}_d(X)/S_d
$$

is the **reduced symmetric locus**. Its points parametrize reduced effective degree-$d$ zero-cycles after arbitrary field extension.

If $X$ is smooth of pure dimension $r$, then $\operatorname{Conf}_d(X)$ and $Q_d(X)$ are smooth of dimension $rd$, and

$$
\operatorname{Conf}_d(X)\longrightarrow Q_d(X)
$$

is finite étale of degree $d!$. If $X$ is geometrically connected and $r>0$, the ordered configuration space is geometrically irreducible: it is a nonempty open in the geometrically irreducible variety $X^d$. Consequently $Q_d(X)$ is geometrically irreducible as well.

When $r=0$, a smooth geometrically connected $K$-variety is $\operatorname{Spec}K$. The main theorem is then immediate with $L=K$. Hence all deformation arguments may assume $r>0$.

### 3.3 The universal finite étale family

There is a universal incidence scheme

$$
\mathcal Z_d\subset X\times Q_d(X).
$$

Above a geometric cycle $\{x_1,\ldots,x_d\}$ its fiber is exactly the reduced set $\{x_1,\ldots,x_d\}$. The projection

$$
p_d:\mathcal Z_d\longrightarrow Q_d(X)
$$

is finite étale of degree $d$, and the other projection evaluates the universal point in $X$.

For $q\in Q_d(X)(K)$, the fiber $(\mathcal Z_d)_q$ is the spectrum of a rank-$d$ finite étale $K$-algebra $B_q$. It is a product of fields in general. It is connected if and only if $B_q$ is a field, and then the universal map gives one closed point

$$
P_q:\operatorname{Spec}B_q\longrightarrow X
$$

of degree $d$. Thus the desired irreducibility condition is not imposed on the symmetric power itself. It is imposed on the fiber of $p_d$.

Geometrically, $\mathcal Z_d$ is connected. More precisely,

$$
\mathcal Z_d\simeq \operatorname{Conf}_d(X)/S_{d-1},
$$

where $S_{d-1}$ fixes one label and permutes the others. This quotient is geometrically irreducible because $\operatorname{Conf}_d(X)$ is. Its pullback to $\operatorname{Conf}_d(X)$ is instead the disjoint union of $d$ copies of the ordered configuration space, one for each possible marked label. Confusing that disconnected pullback with the incidence scheme would give a false proof. Equivalently, geometric monodromy of the quotient acts transitively on the $d$ members of a generic configuration. This geometric connectedness makes connected specialization a genuine Hilbert condition rather than one obstructed by a constant subfield.

There are two permutation actions nearby, and separating them prevents a common mistake. The cover

$$
\operatorname{Conf}_d(X)\to Q_d(X)
$$

has degree $d!$ and remembers every ordering. Its geometric fiber is the set of bijections from $\{1,\ldots,d\}$ to the support. The incidence cover has degree $d$ and remembers only one marked member. A specialization can act transitively on the $d$ members without realizing the full symmetric group on all orderings. For the residue algebra to be a field, transitivity on members is necessary and sufficient; a full $S_d$ Galois closure is unnecessary.

For example, a cyclic cubic field gives a connected three-point incidence fiber, but its action on the six orderings has two orbits. Hilbert irreducibility applied only to a full-ordering cover would ask for a stronger and sometimes impossible conclusion. The universal incidence family is tailored to the actual point-versus-product question.

### 3.4 Smoothness and local coordinates

At a point $q\in Q_d(X)(k)$ over a local field $k$, smoothness gives étale coordinates of dimension $rd$. Concretely, after choosing a sufficiently small neighborhood $W$ of $q$, there is an étale morphism

$$
\phi:W\longrightarrow\mathbf A_k^{rd}.
$$

On local points, an étale morphism is a local homeomorphism near a rational point. Over a nonarchimedean field this follows from the multivariable Hensel lemma; over $\mathbf R$ or $\mathbf C$ it is the inverse function theorem. Hence a small open box in affine space lifts uniquely to a small neighborhood of $q$.

The global proof needs one moving family compatible with all these local charts, not a list of unrelated local maps. Étale coordinates show that the desired cycles occupy open neighborhoods and that first-jet interpolation is the correct infinitesimal condition. The moving-family lemma in Section 5.2 uses sufficiently positive global linear systems, weak approximation in their coefficient spaces, and Bertini irreducibility to construct one $K$-defined family meeting all those neighborhoods. Local coordinates alone do not perform that globalization.

### 3.5 Hilbert schemes and the boundary

For a smooth curve, $\operatorname{Sym}^d(X)$ itself is smooth, even along repeated cycles. In dimension at least two, symmetric powers usually acquire quotient singularities along the diagonals. The Hilbert scheme $\operatorname{Hilb}^d(X)$ remembers length-$d$ subschemes rather than only cycles; on a smooth surface it resolves much of this collision behavior.

None of that additional boundary geometry is needed here. Our local cycles are chosen reduced and with pairwise distinct geometric support, so they lie in the common open locus

$$
Q_d(X)\simeq \operatorname{Hilb}^d(X)_{\mathrm{reduced\ fibers}}.
$$

On this locus the universal family is finite étale. Allowing collisions would replace a finite étale algebra by an algebra with nilpotents and would destroy the direct Hilbert interpretation of connectedness. The reduced locus is therefore not a cosmetic simplification; it is the exact domain on which “connected fiber” means “one separable closed point.”

## 4. Encoding local conditions

### 4.1 Local opens and conjugate points

Fix a place $v$ and a nonempty open $\Omega_v\subset X(K_v)$. For degree $d$, define

$$
Q_d(\Omega_v)\subset Q_d(X)(K_v)
$$

to consist of reduced split cycles $x_1+\cdots+x_d$ with every $x_i\in\Omega_v$. This is open: distinctness is open, the quotient by $S_d$ is étale, and $\Omega_v^d$ is open in $X(K_v)^d$.

It is nonempty when $\dim X>0$. A nonempty local open in a smooth positive-dimensional variety contains arbitrarily many pairwise distinct points. At a nonarchimedean place this is visible in an étale coordinate ball in $K_v^r$; at a real or complex place it follows from the ordinary manifold topology.

Selecting a point of $Q_d(\Omega_v)$ is stronger than repeating one local point $d$ times. The repeated cycle lies on the diagonal and is not in the reduced locus. Instead one perturbs the given point to $d$ nearby distinct points. Since the original condition is open, all perturbations remain acceptable.

### 4.2 Finite étale local algebras

Let $k$ be a completion of $K$ and let

$$
A=\prod_{i=1}^s E_i
$$

be a finite étale $k$-algebra of rank $d$. An $A$-point of $X$ is a tuple $(x_i)$ with $x_i\in X(E_i)$. It determines a degree-$d$ finite étale zero-cycle over $k$ provided the induced geometric points are pairwise distinct. Equivalently, the map $\operatorname{Spec}A\to X$ is a closed immersion onto a reduced zero-dimensional subscheme.

This last condition is the precise meaning of **local realizability**. Merely knowing that each $X(E_i)$ is nonempty is not always enough if two components are forced to have the same image. In positive dimension, small independent perturbations usually separate them. We will call a pair $(A,\Xi)$ locally realizable if $\Xi\subset X(A)$ is a nonempty open containing such an injective reduced configuration.

The topology on $X(A)$ is the product topology

$$
X(A)=\prod_iX(E_i).
$$

If $E_i$ has several $k$-embeddings into a normal closure, the corresponding geometric support is automatically stable under their action. A condition stated using equations with coefficients in $k$ is invariant. A condition that singles out a labeled root may not be; it must either be enlarged to its conjugacy orbit or supplied together with a labeling that the global problem genuinely remembers.

Suppose, for instance, that $X=\mathbf A^1_k$ and $A=E$ is a quadratic field. An element $a\in E\setminus k$ gives two distinct conjugate points, hence a reduced degree-two configuration. An element $a\in k$ viewed inside $E$ gives only one geometric image counted twice by the map $\operatorname{Spec}E\to\mathbf A^1$; the map is not a closed immersion. The algebra $E$ is étale, but the evaluated cycle on $X$ is not an injective configuration. This is why local realizability concerns the algebra together with its point, not the algebra alone.

Local constancy now gives a neighborhood $\mathcal U\subset Q_d(X)(k)$ on which the pullback of the universal family has constant $k$-algebra isomorphism type $A$. After shrinking, its evaluated points remain in $\Xi$. This is the geometric version of stability of separable polynomials under small changes of coefficients.

### 4.3 Building local reduced cycles

Suppose first that only $\Omega_v\subset X(K_v)$ is prescribed. Choose one point $a_v\in\Omega_v$. Smooth coordinates identify a neighborhood with an open ball in $K_v^r$. Pick $d$ distinct coordinate vectors in that ball and lift them to points $a_{v,1},\ldots,a_{v,d}$. Their unordered sum is a point

$$
q_v\in Q_d(\Omega_v).
$$

Its universal algebra is $K_v^d$.

For a prescribed factor $E/k$, begin with $a\in X(E)$. Its $k$-conjugates form a reduced degree-$[E:k]$ cycle if $a$ does not descend to a proper subfield in a way that identifies conjugates. If necessary, perturb $a$ inside its open condition. The points that descend to a fixed proper intermediate field lie in a lower-dimensional or thin locus; since a finite extension has only finitely many intermediate fields after passing to a normal closure and $X$ is positive-dimensional and smooth, a generic local perturbation has full residue field. Taking the union over the factors $E_i$ and separating coincident conjugates produces the desired $A$-configuration.

This construction explains why the theorem assumes open local conditions rather than exact local points. If one insists that every conjugate equal one fixed point, the corresponding cycle is nonreduced as a configuration and cannot be the fiber of a degree-$d$ étale field.

### 4.4 Degree, repetition, and compatibility

Different places may initially supply cycles of different degrees. We need one global degree $d$, because it will equal $[L:K]$. There are two standard ways to synchronize degrees.

For split conditions there is no obstruction: one may construct a split cycle of any positive degree. For an algebra prescription $A_v$ of rank $n_v$, one may repeat the local pattern $r_v$ times, obtaining $A_v^{r_v}$ of rank $r_vn_v$, provided the application allows repeated packets. Choosing a common multiple of the $n_v$ then aligns all ranks.

If the algebra must be prescribed **exactly**, its rank already fixes $d$, so every other datum must have that same rank and $d$ must be a good global degree. This is a real compatibility condition, not a defect of the proof. For example, a variety of index $2$ has no odd-degree closed point. No approximation theorem can produce a cubic point on it merely because cubic local cycles exist.

In the flexible Moret–Bailly theorem, degree is not part of the input. The moving-family lemma below chooses a sufficiently large degree for which its interpolation and connectedness construction works. For split local conditions, one can then make a reduced local cycle of that degree inside every prescribed open. When nonsplit packets are prescribed, allowed repetition must be performed before the moving family is chosen. One may not simply add an arbitrary global auxiliary cycle: its local support need not lie in the prescribed opens. Exact-rank data therefore remain fixed-rank data, and the existence of a moving family of that rank is an explicit hypothesis in the exact local-algebra theorem.

### 4.5 Archimedean cycle types

Finite étale algebras over $\mathbf R$ are exactly

$$
\mathbf R^r\times\mathbf C^s,
\qquad r+2s=d.
$$

The pair $(r,s)$ is locally constant in a reduced family. A cycle supported entirely on real points has algebra $\mathbf R^d$; a conjugate pair of nonreal complex points contributes one $\mathbf C$ factor. Over $\mathbf C$, the only rank-$d$ finite étale algebra is $\mathbf C^d$.

This is the source of signature control. If $K$ is totally real and the local algebra at every real place is $\mathbf R^d$, then every embedding of the global residue field into $\mathbf C$ has real image. It is not enough to choose one real point at each real place: all $d$ local sheets must remain real.

### 4.6 Weil restriction and finite local packets

Symmetric powers forget labels, which is exactly right for a closed point. A prescribed nonsplit local packet is initially easier to describe with labels: one names a finite étale algebra and one point over each of its factors. Weil restriction converts that extension-valued description into ordinary rational points on a variety over the smaller field.

Let $A/k$ be a finite locally free algebra of rank $d$ and let $Y$ be a quasi-projective $A$-scheme. The Weil restriction $\operatorname{Res}_{A/k}Y$, when it exists, represents the functor

$$
T\longmapsto Y(T\times_k\operatorname{Spec}A).
$$

In particular,

$$
(\operatorname{Res}_{A/k}Y)(k)=Y(A).
$$

For the application $Y=X_A$, this reads

$$
(\operatorname{Res}_{A/k}X_A)(k)=X(A).
$$

We recall the construction because it explains exactly which hypotheses are being used. Suppose first that $Y=\operatorname{Spec}B$ is affine and choose a $k$-basis $e_1,\ldots,e_d$ of $A$. Present

$$
B=A[z_1,\ldots,z_m]/(f_1,\ldots,f_s).
$$

Write a prospective image of $z_j$ as

$$
z_j\longmapsto \sum_{a=1}^d z_{ja}e_a.
$$

Expanding each $f_i$ in the basis $e_a$ gives $d$ polynomial equations over $k$. Their common zero scheme represents the desired functor. A change of basis gives a canonically isomorphic representing scheme, since both represent the same functor. For a quasi-projective $Y$, choose a locally closed immersion into projective space over $A$. The same coefficient construction produces the restriction of the ambient projective space; the equations and nonvanishing conditions defining $Y$ produce a locally closed subvariety. Uniqueness of representing objects glues the affine constructions. Thus finite locally free restriction exists for the quasi-projective spaces used here.

The construction commutes with extension of the ground field. If $A/k$ is finite étale, then over a separable closure $\bar k$ one has

$$
A\otimes_k\bar k\simeq\bar k^d,
$$

and therefore

$$
(\operatorname{Res}_{A/k}X_A)_{\bar k}
\simeq \prod_{\tau:A\to\bar k}X_{\bar k}.
$$

This identity proves the properties needed below. If $X/k$ is smooth, the restriction is smooth, because after the faithfully flat extension to $\bar k$ it is a product of smooth varieties. If $X$ is geometrically connected, the restriction is geometrically connected. Its dimension is $d\dim X$. For a product $A=\prod_iE_i$, restriction is the product of the restrictions from the factors.

There is also a useful topological statement. When $k$ is a completion of a number field, the displayed identification on rational points is a homeomorphism

$$
(\operatorname{Res}_{A/k}X_A)(k)
\simeq \prod_iX(E_i).
$$

This follows on affine charts because both topologies are induced by finitely many coordinate functions, and it then glues. Hence a product of local neighborhoods in the $X(E_i)$ is an ordinary open subset on a smooth $k$-variety. This is the precise device behind the notation $\Xi\subset X(A)$.

To pass from a labeled packet to an unordered cycle, base change a point $\xi\in X(A)$ to $\bar k$. It gives $d$ geometric points indexed by the embeddings of the field factors of $A$. The condition that these points be pairwise distinct is open: equality of two points is a closed diagonal condition. On this injective locus, forgetting the labels gives a morphism

$$
(\operatorname{Res}_{A/k}X_A)^{\mathrm{inj}}
\longrightarrow Q_d(X).
$$

Its image consists exactly of reduced cycles whose finite étale algebra is isomorphic to $A$. Locally on $k$-points this image is open. Indeed, the universal family over $Q_d(X)$ is finite étale, and the isomorphism class of a finite étale algebra over a local field is locally constant. Thus restriction of scalars organizes the input, while the reduced symmetric power organizes the output.

Two warnings matter. First, $X(A)\ne\varnothing$ does not imply that the injective locus is nonempty: a tuple may factor through one geometric point. Second, restriction of scalars does not globalize an arbitrarily chosen local algebra. It only expresses the local datum as a rational point of a parameter variety. The moving and irreducibility arguments must still place compatible packets into one global family.

### 4.7 Arithmetic neighborhoods at finite and real places

The existence theorem consumes open subsets, whereas arithmetic geometry usually produces conditions described by reduction, integrality, or sign. We therefore record how those conditions become neighborhoods.

Let $k$ be a nonarchimedean completion, let $x\in X(k)$, and suppose $X/k$ is smooth of dimension $r$. There is an open neighborhood $U$ of $x$ and an étale map

$$
u:U\longrightarrow\mathbf A_k^r.
$$

After shrinking, $u$ induces a homeomorphism from a neighborhood of $x$ onto a polydisc about $u(x)$. Choose coordinates so that a basic neighborhood has the form

$$
|u_i(y)-u_i(x)|_k<\epsilon_i
\qquad(1\le i\le r).
$$

If $X$ extends to a smooth scheme over the valuation ring and $x$ extends to an integral point, one may take congruence tubes

$$
u_i(y)\equiv u_i(x)\pmod{\mathfrak m_k^{n_i}}.
$$

The multivariable Hensel lemma identifies sufficiently small tubes upstairs and downstairs. Consequently, smooth reduction to a chosen special-fiber point is open. Nonvanishing of a regular function is open. A determinant being a unit is open after an integral model has been fixed. More elaborate structures that are classified by a finite étale fiber are locally constant, by the rigidity theorem for finite étale algebras.

One must distinguish these cases from conditions that are not open. Equality with one exact point is not open in positive dimension. Being singular is usually closed rather than open. A valuation inequality such as $v(a)\ge n$ is open, while equality $v(a)=n$ is the difference of two open-and-closed valuation balls inside $k^\times$ and is still open there; by contrast, a condition involving an unbounded limiting valuation need not define a neighborhood useful for finite approximation. The arithmetic claim must be translated before the global theorem is invoked.

At a real place, $X(\mathbf R)$ is a smooth real manifold. A regular function has locally constant sign away from its zero locus, and a finite collection of strict inequalities defines an open semialgebraic neighborhood. Connected components of $X(\mathbf R)$ are open and closed. For a finite étale family, the number of real sheets is locally constant: a real sheet can become nonreal only after meeting another sheet on the discriminant locus. Thus a configuration of $d$ distinct real points has a neighborhood throughout which the associated algebra remains $\mathbf R^d$.

At a complex place there is no signature choice: every rank-$d$ finite étale algebra is $\mathbf C^d$. Complex neighborhoods can still impose ordinary analytic inequalities, but they cannot contribute to total reality.

These descriptions explain the phrase **arithmetic neighborhood** used later: it is an open subset of local points chosen small enough that every arithmetic property required by the application is constant on it. The theorem preserves membership in that neighborhood; the prior local analysis is what converts membership back into good reduction, a level condition, a sign, or a prescribed local algebra.

## 5. The irreducible-cycle approximation theorem

### 5.1 Statement of the engine

We now isolate the geometric engine. Its formulation includes a Hilbert condition because that is what distinguishes one closed point from a reducible cycle.

**Theorem 5.1 (irreducible-cycle approximation).** Let $K$ be a number field and let $X$ be a smooth geometrically connected $K$-variety of positive dimension. Let $S$ be a finite set of places. For each $v\in S$, let $\mathcal U_v$ be a nonempty open subset of $Q_d(X)(K_v)$ for one common degree $d$. Assume that the local universal algebra on $\mathcal U_v$ has a fixed isomorphism class $A_v$ after the opens have been shrunk, and assume that the local cycles admit a simultaneous moving presentation as in Lemma 5.2 below. In the flexible split theorem, Lemma 5.2 supplies such a presentation after choosing $d$ sufficiently large; for exact local-algebra data, this is the compatibility required of the fixed rank.

Let $E/K$ be a finite extension. Then there is

$$
q\in Q_d(X)(K)
$$

such that:

1. $q$ belongs to $\mathcal U_v$ for every $v\in S$;
2. the fiber $(\mathcal Z_d)_q$ is connected;
3. $(\mathcal Z_d)_q\times_KE$ is connected.

If $L$ is the coordinate algebra of $(\mathcal Z_d)_q$, then $L$ is a degree-$d$ field, $L$ is linearly disjoint from $E$, and

$$
L\otimes_KK_v\simeq A_v
$$

for every $v\in S$, compatibly with the evaluation map to $X$.

The presentation hypothesis packages geometric degree compatibility, not merely equality of the local ranks. In the split local-open application, degree is free and the proof chooses a suitable $d$. When local packets may be repeated, one first replaces them by packets of one sufficiently large common degree. If exact rank-$d$ algebras are prescribed, $d$ must already be large enough for the presentation lemma and must satisfy every global index obstruction; one may not enlarge it silently.

### 5.2 Étale coordinates near finitely many cycles

The first geometric ingredient is a moving lemma. It is the point at which smoothness does the real work.

**Lemma 5.2 (simultaneous moving-family presentation).** Let $X/K$ be smooth, geometrically connected, and positive-dimensional. Given nonempty split opens $\Omega_v\subset X(K_v)$ at finitely many places, there are a sufficiently large degree $d$, cycles $q_v\in Q_d(\Omega_v)$, and sufficiently small neighborhoods $\mathcal U_v$ of $q_v$ for which there exist an integer $N>0$, a nonempty open $H\subset\mathbf A_K^N$, a geometrically integral scheme $\mathcal T$, a finite étale morphism

$$
f:\mathcal T\longrightarrow H
$$

of degree $d$, a $K$-morphism $e:\mathcal T\to X$, and points $h_v\in H(K_v)$ such that $e:\mathcal T_{h_v}\to X_{K_v}$ is a closed immersion with cycle in $\mathcal U_v$. The same remains true on a neighborhood $V_v$ of $h_v$. The cycle construction gives a morphism

$$
\Psi:H\longrightarrow Q_d(X)
$$

with $\Psi(V_v)\subset\mathcal U_v$, and

$$
\mathcal T\simeq\mathcal Z_d\times_{Q_d(X),\Psi}H.
$$

The same construction applies to nonsplit packet conditions when enlargement by auxiliary packets is explicitly allowed. For a fixed degree and exact local algebras, however, the conclusion is available only when the rank-$d$ data admit such a presentation. That condition is automatic in the flexible split application after $d$ is chosen sufficiently large, but it is not a consequence of the bare equality $\dim_{K_v}A_v=d$.

This presentation, rather than rationality of $Q_d(X)$, is the crucial geometric assertion. Symmetric powers of curves of positive genus already show why one must not claim that $Q_d(X)$ itself is an open of affine space. The affine space $H$ parametrizes fibers of one carefully constructed finite map; it need not dominate the whole symmetric power.

Here is the construction. It builds one pencil on one global curve whose fibers carry the required local configurations; it does not assert that a symmetric power is rational.

If the set of designated places is empty, choose by Bertini a geometrically integral complete-intersection curve in $X$, normalize its projective closure, and take a general basepoint-free pair of sections of a sufficiently positive line bundle on that curve. One member has a reduced divisor disjoint from the boundary. Removing the branch values and boundary images gives the required geometrically integral finite étale family. We may therefore assume below that at least one $v$ is present.

**Step 1: slicing out a global curve through all local opens.** Choose $a_v\in\Omega_v$. Put $r=\dim X$, choose a projective closure $X\hookrightarrow\bar X$, and choose a very ample line bundle $\mathcal L$ on $\bar X$. When $r>1$, sufficiently high powers of $\mathcal L$ separate values and first derivatives at $a_v$. Over each $K_v$ choose $r-1$ sections whose common zero set has a smooth one-dimensional germ through $a_v$. The full-rank Jacobian condition persists when the section tuple and the intersection point are perturbed.

All these local tuples belong to scalar extensions of the same finite-dimensional $K$-space of sections. Weak approximation chooses one $K$-tuple close to every local tuple and outside the Bertini loci where a successive cut fails to be geometrically integral. Indeed, a proper algebraic subset of affine coefficient space has empty local interior; shrink the local boxes off the bad locus before applying approximation. Bertini irreducibility, in the form proved for affine linear sections in Book 153, shows that its complement is nonempty.

The intersection inside $X$ is a geometrically integral curve, smooth at all the selected local germs. Normalize its projective closure and call the resulting smooth projective geometrically integral curve $\bar C$. The normalization map identifies a dense open $C^{\mathrm{emb}}\subset\bar C$ with a locally closed smooth curve in $X$; its complement is finite. Every selected germ lies in this open. After taking a sufficiently small neighborhood of the lifted point, we therefore obtain, for every $v$, a nonempty open

$$
\Omega_{C,v}\subset C^{\mathrm{emb}}(K_v)
$$

on which the map to $X(K_v)$ is injective and has image in $\Omega_v$.

When $r=1$, take $\bar C$ to be the normalization of the projective closure of $X$; it is already isomorphic to $X$ over the smooth open under consideration. This step uses only first jets. It does not attempt to encode the final degree-$d$ divisor in one jet.

**Step 2: the moving-divisor fact on a local curve.** We need the following one-dimensional fact.

> Let $k$ be a completion of a number field, let $C/k$ be a smooth projective geometrically connected curve, let $\mathcal A$ be an ample line bundle of degree $e>0$, and let $U\subset C(k)$ be nonempty and open. For every sufficiently large integer $n$ in a suitable arithmetic progression, $\mathcal A^n$ has a section whose zero divisor is reduced, split over $k$, and supported in $U$.

We prove the fact, including the divisibility qualification. Fix $P\in U$. If $g=0$, the point $P$ identifies $C$ with $\mathbf P^1_k$, whose degree-zero divisor-class group is trivial. Any $ne$ distinct points of $U$ then form a divisor linearly equivalent to $\mathcal A^n$, so the assertion is immediate. Assume $g>0$ and write $J(k)$ for the degree-zero divisor-class group of $C$.

We spell out the piece of curve theory used here, rather than importing an unrecorded Picard theorem. For an effective divisor $D$, the space of principal parts $H^0(C,\mathcal O(D)/\mathcal O)$ pairs with $H^0(C,\omega_C)$ by summing local residues. The residue theorem shows that the principal parts of a rational function annihilate every regular differential. Conversely, eliminating polar coefficients one point and one order at a time shows that these residue equations are the only obstruction. The differentials annihilating the whole principal-parts space are exactly $H^0(C,\omega_C(-D))$. Counting dimensions therefore gives

$$
h^0(\mathcal O(D))-1
=\deg D-g+h^0(\omega_C(-D)).
$$

Shifting an arbitrary divisor by an effective one and using the same one-point exact sequences gives the general formula. Equivalently, the divisor exact sequence gives the perfect obstruction pairing

$$
H^1(C,M)\times H^0(C,\omega_C\otimes M^{-1})\longrightarrow k
$$

for every line bundle $M$. In particular,

$$
h^0(M)-h^0(\omega_C\otimes M^{-1})=\deg M+1-g.
$$

This is the elementary principal-parts proof of the precise duality and Riemann–Roch statements needed below. If $\deg M>2g-2$, the second space vanishes because a nonzero section cannot have a divisor of negative degree. Hence $h^0(M)=\deg M+1-g$, over $k$ and after every scalar extension.

It follows that, for $m\ge2g-1$, every degree-$m$ line bundle has a nonzero $k$-section and the Abel map

$$
\operatorname{Sym}^m(C)(k)\longrightarrow\operatorname{Pic}^m(C)(k)
$$

is surjective, with fiber over $M$ equal to the projective space of nonzero sections of $M$ modulo scalars. Give the divisor-class group the quotient topology from this map. Divisor equivalence is closed, its projective fibers give local analytic quotient charts, and addition and inversion come from adding divisors and replacing a divisor by a linearly equivalent complement in a sufficiently positive linear system. Thus $J(k)$ is a Hausdorff locally analytic group. It is compact because $\operatorname{Sym}^m(C)(k)$ is compact. In local parameters, differentiating a moving divisor shows that the differential of the Abel map at $P_1+\cdots+P_m$ is dual to evaluation of regular differentials at the $P_i$. One can choose $g$ distinct points in the arbitrarily small open $U$ for which this evaluation has full rank: otherwise a nonzero regular differential would vanish on infinitely many points of a smooth curve. The inverse function theorem therefore says that a finite sum of classes

$$
B=\{[Q-P]:Q\in U\}\subset J(k)
$$

has nonempty interior.

We use one elementary compact-group lemma. If $G$ is a compact topological group and $B\subset G$ contains the identity and some finite product $B^m$ has interior, then the semigroup $\bigcup_{j\ge0}B^j$ is an open subgroup $G_B$, and compactness gives $G_B=B^{m_0}$ for some $m_0$. To prove the subgroup assertion, put an open set $c+W$ inside $B^m$, with $W$ a symmetric neighborhood of zero. Recurrence of the positive multiples of $c$ in its compact cyclic closure gives $q>0$ for which $(q+1)c\in W$. Hence

$$
(q+1)c+(q+1)W\subset B^{m(q+1)}
$$

contains a neighborhood of zero. Shrink to a symmetric neighborhood $W_0$ contained in the semigroup. If $x$ belongs to the semigroup, recurrence of the positive multiples of $x$ gives $q x\in-x+W_0$; writing $-x=qx+w$ with $w\in W_0$ proves that the inverse also belongs. Thus the semigroup is an open subgroup. Finally choose $W_0\subset B^a$. The translates $x+W_0$, for $x$ in the subgroup, form an open cover; compactness selects finitely many, and their finitely many representatives lie in one $B^b$. Hence $G_B\subset B^{a+b}$, proving the last assertion.

Apply the lemma to $J(k)$. The quotient $J(k)/G_B$ is finite. Let

$$
b=[\mathcal A]-e[P]\in J(k).
$$

If $n$ is divisible by the exponent of this finite quotient and $ne\ge m_0+g$, then $nb\in G_B=B^{m_0}\subset B^{ne}$. Thus there are $ne$ points $Q_i\in U$, allowing repetitions at first, such that

$$
[Q_1+\cdots+Q_{ne}]=[\mathcal A^n].
$$

Hence $\mathcal A^n$ has a section with its entire divisor in $U$. We still have to remove repetitions without losing the divisor class. Choose once and for all distinct points $R_1,\ldots,R_g\in U$ at which the Abel map is a submersion, as above, and put $c_0=\sum_j[R_j-P]$. Since $c_0\in G_B$ and $G_B=B^{m_0}$ is a group, every $x\in G_B$ can be written as

$$
x=\sum_{i=1}^{m_0}[Q_i-P]+\sum_{j=1}^g[R_j-P].
$$

The addition map is submersive at this tuple because of its last $g$ coordinates. Pad the tuple to length $ne$ with copies of $P$, and choose pairwise disjoint small neighborhoods of the $R_j$. Vary the first $ne-g$ points generically, by arbitrarily small amounts inside $U$, so that they are pairwise distinct. Their divisor class changes only slightly. The inverse function theorem moves the last $g$ points inside their respective neighborhoods and corrects that change exactly. The corrected points depend analytically on the free ones. Equality of one of them with a free point is a proper analytic condition, so the free tuple may be chosen off the finitely many such collision loci. All $ne$ points are then distinct, remain in $U$, and represent the original class $x$. Applying this with $x=nb$ gives a reduced divisor in the class of $\mathcal A^n$.

Equivalently, the resulting section of $\mathcal A^n$ has a reduced split zero divisor supported in $U$. Simple-root stability makes this property open in the local section space. This proves the moving-divisor fact.

The proof also explains why “sufficiently divisible” cannot be replaced casually by “every sufficiently large degree.” The finite quotient $J(k)/G_B$ records the component and local divisor-class obstruction. Since only finitely many places occur, one integer $n$ can satisfy all their progressions.

**Step 3: one global pencil with all local split fibers.** Choose an ample line bundle $\mathcal A$ on $\bar C$, for example the pullback of a high power of $\mathcal L$. Apply Step 2 to every pair $(\bar C_{K_v},\Omega_{C,v})$ and choose one sufficiently large common exponent $n$. Put

$$
d=n\deg\mathcal A.
$$

For every $v$, choose a local section $s_{\infty,v}$ of $\mathcal A^n$ whose zero divisor $D_v$ consists of $d$ distinct $K_v$-points in $\Omega_{C,v}$. Choose a second local section $s_{0,v}$ nonzero at every point of $D_v$.

Proper cohomology in degree zero commutes with extension of a ground field, so

$$
H^0(\bar C,\mathcal A^n)\otimes_KK_v
\simeq H^0(\bar C_{K_v},\mathcal A^n).
$$

Weak approximation in the two copies of this finite-dimensional vector space gives global sections $(s_0,s_\infty)$ close to every local pair. We also require that they have no common geometric zero. This is the complement of the resultant locus, a proper Zariski-closed subset: for $n$ large the line bundle is globally generated, and two general sections on a curve have disjoint zero divisors. As in Step 1, weak approximation inside the local boxes can avoid that closed subset. After shrinking the boxes, the divisor of $s_\infty$ over every $K_v$ remains reduced, split, contained in $\Omega_{C,v}$, and disjoint from the divisor of $s_0$.

The pair defines a finite morphism

$$
f=[s_\infty:s_0]:\bar C\longrightarrow\mathbf P^1_K
$$

of degree $d$, whose fiber over $0=[0:1]$ is $\operatorname{div}(s_\infty)$. Its reducedness says precisely that $0$ is not a branch value. Moreover, a point of the finite exceptional set $\bar C\setminus C^{\mathrm{emb}}$ mapping to $0$ would remain an exceptional zero after extension to any one of the fields $K_v$, contradicting the fact that the $d$ local zeros already form the whole degree-$d$ fiber and lie in $C^{\mathrm{emb}}$. Remove from $\mathbf A^1_K=\mathbf P^1_K\setminus\{\infty\}$ all branch values and the images of $\bar C\setminus C^{\mathrm{emb}}$. The resulting open $H$ contains $0$ and is therefore nonempty. Then

$$
\mathcal T=f^{-1}(H)\longrightarrow H
$$

is finite étale of degree $d$, $\mathcal T$ is geometrically integral, and the embedding $\mathcal T\subset C^{\mathrm{emb}}\hookrightarrow X$ gives $e:\mathcal T\to X$. Because $C^{\mathrm{emb}}\to X$ is an immersion identifying it with a locally closed subcurve, every geometric fiber evaluates to $d$ distinct points of $X$. For each $v$, take $h_v=0$. Simple-root stability supplies a neighborhood $V_v\subset H(K_v)$ on which all $d$ points of the fiber remain $K_v$-rational and evaluate into $\Omega_v$.

Every fiber gives a reduced degree-$d$ cycle, hence a morphism

$$
\Psi:H\longrightarrow Q_d(X).
$$

By the universal property of the incidence family,

$$
\mathcal T\simeq\mathcal Z_d\times_{Q_d(X),\Psi}H.
$$

Shrinking the $V_v$ once more produces the required $q_v$, $\mathcal U_v$, and stability. This proves the flexible split assertion of the lemma.

For nonsplit packets, the arithmetic part of the proof is unchanged once a common moving presentation is supplied. Such a presentation may sometimes be obtained by carrying labeled packets through restriction of scalars and retaining enough coefficient directions in the curve-and-pencil construction. It is not automatic from equality of ranks, so the exact local-algebra theorems below continue to state it as a hypothesis.

There are three distinct finite approximation steps in the full argument. The first chooses one global curve meeting all local opens. The second chooses one global pencil with a split local fiber at every designated place. The third, used in Section 5.3, chooses one parameter of that pencil in the required Hilbert subset. Keeping them separate prevents unrelated local coordinate charts from being mistaken for one global morphism.

High degree has now been accounted for: it supplies first-jet separation for the global slice, makes the local Abel images large enough to overcome their finite divisor-class obstructions, and makes the pencil basepoint-free with a reduced split fiber. It is geometric room, not a hidden assertion that every integer is an allowed degree. This proof also explains why the exact-rank form must assume the presentation rather than infer it from local realizability alone.

### 5.3 Weak approximation in the parameter space

Since $H$ is an open of affine space, the diagonal $H(K)$ is dense in

$$
\prod_{v\in S}H(K_v).
$$

The presentation lemma supplies neighborhoods $V_v$ with $\Psi(V_v)\subset\mathcal U_v$. Ordinary weak approximation then gives many $h\in H(K)$ lying in every $V_v$. For any such $h$, local constancy identifies the specialized algebra

$$
\mathcal T_h\otimes_KK_v
$$

with $A_v$.

At this stage $\mathcal T_h$ may be disconnected. Weak approximation controls topology, not irreducibility. A typical fiber might be $K\times M$, which would produce a rational point plus a smaller closed point. The local completions could still look exactly right. Thus no argument based only on closeness can finish the proof.

### 5.4 The Hilbert condition that forces a field

The cover $\mathcal T\to H$ is finite étale and geometrically connected. Consequently the set of $h\in H(K)$ for which $\mathcal T_h$ is connected is a Hilbert subset of $H(K)$. Book 153 showed that such a subset meets every finite product of nonempty local opens.

To impose disjointness from $E$, base change the cover to $E$:

$$
\mathcal T_E\longrightarrow H_E.
$$

Geometric connectedness implies that this cover remains connected. The parameters $h\in H(K)$ for which the fiber remains connected after tensoring with $E$ form another Hilbert subset, descended from $E$ to $K$. At such a parameter, if $B_h$ is the fiber algebra, then

$$
B_h\otimes_KE
$$

is a field. In particular $B_h$ itself is a field and is linearly disjoint from $E$.

It is important that we apply Hilbert irreducibility to the degree-$d$ universal incidence cover, not merely to the ordered $d!$-sheeted configuration cover. Connectedness of the ordered-labeling fiber would control a Galois group acting on orderings; the conclusion we need is transitivity on the $d$ points themselves. The incidence cover expresses exactly that condition.

### 5.5 Proof of the engine

**Proof strategy.** We construct a rational parameter space through the local cycles, translate each local demand to an open box on that space, and then intersect the boxes with two Hilbert subsets: one for connectedness over $K$ and one for connectedness after base change to $E$.

**Proof.** Choose the simultaneous moving presentation assumed in the statement, with parameter space $H$, map $\Psi$, local parameters $h_v$, neighborhoods $V_v$, and geometrically integral cover $\mathcal T\to H$. In the flexible split case, these are supplied by Lemma 5.2.

Let $\mathcal H_1$ be the Hilbert subset on which $\mathcal T_h$ is connected. Let $\mathcal H_E$ be the descended Hilbert subset on which $\mathcal T_h\otimes_KE$ is connected. A finite intersection of Hilbert subsets is Hilbert, and Hilbert subsets of affine space over a number field are dense in finite products of local opens. Hence there is

$$
h\in\mathcal H_1\cap\mathcal H_E\cap\bigcap_{v\in S}V_v.

$$

Put $q=\Psi(h)$. The algebra $L=\Gamma(\mathcal T_h,\mathcal O)$ is finite étale of rank $d$ and connected, hence a field. Connectedness after scalar extension says $L\otimes_KE$ is a field, which is equivalent to linear disjointness. Finally, local constancy on $V_v$ gives

$$
L\otimes_KK_v\simeq A_v.
$$

The evaluation map $\mathcal T\to X$ carries this isomorphism to the prescribed local neighborhoods. $\square$

The proof makes the decisive reasoning visible: the residue algebra becomes a field because a connected finite étale scheme over a field is the spectrum of a finite separable field extension. No Galois assertion enters.

### 5.6 What the theorem does and does not say

Theorem 5.1 simultaneously controls local topology, local algebra type, and finite disjointness. It does not prescribe arbitrary local data. The data must occur in the moving family and must share a global degree. Nor does it claim effectivity: Bertini, weak approximation, and Hilbert irreducibility prove existence but do not supply a useful discriminant bound in this form.

The output field $L$ is generally not normal over $K$. Its embeddings are the $d$ points in the geometric fiber, and transitivity says only that the absolute Galois group acts transitively on them. The Galois closure may be much larger. If an application needs a Galois extension, that is a separate inverse-Galois and local-decomposition problem; it is not part of Moret–Bailly’s theorem.

## 6. Moret–Bailly’s theorem

### 6.1 The exact local-open statement

We can now state the central theorem in its most frequently used form.

**Theorem 6.1 (Moret–Bailly).** Let $K$ be a number field, let $X$ be a smooth geometrically connected variety over $K$, and let $S$ be a finite set of places of $K$. For every $v\in S$, let

$$
\Omega_v\subset X(K_v)
$$

be a nonempty open subset. Let $E/K$ be a finite extension. Then there exist a finite extension $L/K$ and a point $x\in X(L)$ such that:

1. $L$ is linearly disjoint from $E$ over $K$;
2. every $v\in S$ splits completely in $L$;
3. for every $v\in S$ and every $K$-embedding $\sigma:L\hookrightarrow K_v$, the point $x^\sigma\in X(K_v)$ belongs to $\Omega_v$.

The field $E$ may be omitted. The theorem remains true if the $\Omega_v$ are replaced by finite intersections of open conditions.

Smoothness is assumed everywhere on $X$. A common variant requires only a geometrically connected smooth open $X^\circ\subset X$ and local opens meeting $X^\circ(K_v)$; applying the theorem to $X^\circ$ gives the same conclusion.

### 6.2 Proof of the main theorem

**Proof strategy.** At each place we replace the chosen local point by $d$ nearby distinct points, so the desired completion algebra is $K_v^d$. The irreducible-cycle theorem then globalizes all cycles and forces the global algebra to be one field.

**Proof.** If $\dim X=0$, geometric connectedness and smoothness imply $X=\operatorname{Spec}K$, and one takes $L=K$. Assume $\dim X>0$.

Choose $a_v\in\Omega_v$ only to fix the desired local neighborhoods. Apply the flexible part of Lemma 5.2 to obtain one degree $d$, reduced split cycles

$$
q_v\in Q_d(\Omega_v),
$$

and a simultaneous moving presentation. The points in each support may be taken arbitrarily close to $a_v$. Shrink $\mathcal U_v$ so that every support point of every cycle in $\mathcal U_v$ remains in $\Omega_v$ and the universal algebra remains isomorphic to $K_v^d$.

Apply Theorem 5.1 with these neighborhoods and with $E$. It gives $q\in Q_d(X)(K)$ whose universal fiber is $\operatorname{Spec}L$ for a field $L$ linearly disjoint from $E$. The evaluation morphism gives $x\in X(L)$. For each $v\in S$,

$$
L\otimes_KK_v\simeq K_v^d.
$$

Thus $v$ splits completely. Under every projection to a $K_v$ factor, the evaluated point is one support point of a cycle in $\mathcal U_v$, hence lies in $\Omega_v$. $\square$

### 6.3 Reading the completion condition

Fix $v\in S$. Since $v$ splits completely, the places $w$ of $L$ above $v$ are in bijection with the $K$-embeddings $\sigma:L\hookrightarrow K_v$, and every completion $L_w$ equals $K_v$. The conclusion may therefore be written in three equivalent ways:

$$
x_w\in\Omega_v\quad\text{for every }w\mid v;
$$

$$
x^\sigma\in\Omega_v\quad\text{for every }\sigma:L\hookrightarrow K_v;
$$

or the complete local zero-cycle of $x$ is supported in $\Omega_v$.

One must not replace “every” by “some.” If the theorem merely supplied one acceptable $w$, a later embedding $L\hookrightarrow\overline K_v$ could select another completion where the point violates the moduli condition. Complete splitting and support control eliminate that ambiguity.

It is useful to trace one embedding through the construction. A projection

$$
L\otimes_KK_v\simeq K_v^d\longrightarrow K_v
$$

is the same as a $K$-embedding $\sigma:L\to K_v$. Base-changing the evaluation map $\operatorname{Spec}L\to X$ along this projection gives

$$
\operatorname{Spec}K_v\longrightarrow\operatorname{Spec}L\longrightarrow X.
$$

Under the identification of $\operatorname{Spec}(L\otimes_KK_v)$ with the specialized incidence fiber, this is one member of the local configuration. Because the whole configuration lies in $Q_d(\Omega_v)$, that member lies in $\Omega_v$. Nothing depends on numbering the factors: a different isomorphism with $K_v^d$ merely permutes them.

If the local algebra is not split, projections are replaced by its field factors $E_{v,i}$. A place $w_i\mid v$ gives $L_{w_i}\simeq E_{v,i}$, and the localized point belongs to the specified open of $X(E_{v,i})$. Further embeddings $E_{v,i}\hookrightarrow\overline K_v$ recover all geometric conjugates within that factor. Thus factorwise control and embeddingwise control are two levels of the same statement.

### 6.4 The split form

It is convenient to package the theorem as a Skolem datum. Such a datum consists of $X/K$, a finite set $S$, and nonempty local opens $\Omega_v$. A **solution** is a closed point $P\in X$ such that for $L=\kappa(P)$ every $v\in S$ splits completely and every point of $P$ above $v$ lies in $\Omega_v$.

Theorem 6.1 says that every smooth geometrically connected Skolem datum has a solution, even one disjoint from a prescribed finite extension. This language emphasizes that $L$ is the residue field of the point, not an independently chosen ambient field.

If one begins with a finite collection of local conditions at the same $v$, their intersection must be nonempty. The theorem does not reconcile contradictory open sets. For instance, a condition requiring a unit and another requiring positive valuation have empty intersection in $K_v$.

### 6.5 Degree and non-Galois warnings

The proof chooses $d=[L:K]$ large enough for the moving construction. Unless additional geometry supplies a degree estimate, $d$ is not predetermined. Enlarging $L$ after the construction may destroy disjointness and changes the tensor-product data by changing the degree. Passing to the Galois closure preserves complete splitting at a place that already split completely, but it does not preserve a general prescribed local algebra and it need not preserve disjointness from $E$. Therefore the residue field itself is the correct output.

A place can split completely in a non-Galois extension: this simply means $L\otimes_KK_v\simeq K_v^d$. There is no contradiction. Conversely, knowing that one prime above $v$ has local degree one does not imply complete splitting. The tensor-product formulation is the safest one.

## 7. Disjointness and prescribed local algebras

### 7.1 Disjointness as a Hilbert condition

Let $L/K$ be the residue field of the universal cycle and let $E/K$ be finite. Linear disjointness means

$$
L\otimes_KE\text{ is a field},
$$

or equivalently $[LE:E]=[L:K]$. If $E/K$ or $L/K$ is Galois, it is also equivalent to $L\cap E=K$ in a common algebraic closure. Without such a Galois hypothesis, trivial intersection alone is not the right test.

In the parameter family, the tensor product $L\otimes_KE$ is the fiber after base change to $E$. Its connectedness is therefore a Hilbert condition. This is exactly the disjoint-specialization mechanism developed in Book 153, now applied to the incidence cover rather than to a polynomial chosen in advance.

If one wants disjointness from finitely many fields $E_1,\ldots,E_m$, take $E$ to be the compositum of their normal closures. Disjointness from this one field implies disjointness from every $E_i$ and avoids the pitfall that pairwise disjointness need not imply disjointness from the compositum.

Disjointness of $L$ from $E$ does not imply that the Galois closure of $L$ is disjoint from $E$. If an application needs the stronger conclusion, it must impose connectedness after base change for a regular Galois closure of the moving family, usually through the finite collection of resolvent conditions described in Book 153. The root-field condition used in Theorem 5.1 cannot be silently promoted to that stronger assertion.

### 7.2 Avoiding a prescribed finite extension

The practical reason for disjointness is often preservation of a finite Galois image. If $E/K$ is the field cut out by a finite quotient of the absolute Galois group and $L$ is linearly disjoint from $E$, then restriction from $K$ to $L$ does not shrink that quotient. This is a degree calculation in $EL/E$; it does not require $L/K$ to be Galois.

The theorem can also avoid a finite list of bad residue fields or fields over which a geometric component becomes constant. What it cannot do automatically is avoid an arbitrary infinite algebraic extension. Such a demand requires a reduction to finitely many subextensions of bounded degree or a separate group-theoretic argument, as explained in Book 153.

### 7.3 Exact local algebra prescriptions

We state the general local form carefully.

**Theorem 7.1 (local étale algebra form).** Let $X/K$ be smooth and geometrically connected of positive dimension. Fix a degree $d$. For each $v$ in a finite set $S$, let $A_v$ be a rank-$d$ finite étale $K_v$-algebra and let

$$
\Xi_v\subset X(A_v)=\prod_iX(E_{v,i})
$$

be a nonempty open set containing a reduced injective configuration. Assume that these rank-$d$ configurations admit one simultaneous moving-family presentation as in Lemma 5.2. Let $E/K$ be finite. Then there are a degree-$d$ field $L/K$, linearly disjoint from $E$, an $L$-point $x$ of $X$, and isomorphisms

$$
\iota_v:L\otimes_KK_v\xrightarrow{\sim}A_v
$$

such that the image of the localized point belongs to $\Xi_v$.

**Proof.** Each locally realizable pair gives a point $q_v\in Q_d(X)(K_v)$ and a neighborhood on which both the algebra and point conditions are constant. Apply Theorem 5.1. $\square$

The isomorphisms $\iota_v$ are not canonical. Permuting equal factors changes them, and conjugating a field factor changes its labeling. The invariant conclusion is the isomorphism class together with the orbit of the local point data.

### 7.4 Splitting and one-place behavior

Several familiar prescriptions are special cases:

- complete splitting: $A_v=K_v^d$;
- one place above $v$: $A_v$ is a field of degree $d$;
- an unramified partition $(d_1,\ldots,d_r)$: $A_v$ is the product of the unramified extensions of those degrees;
- prescribed ramified behavior: $A_v$ is a specified product of separable extensions.

In each case the algebra must be realized by an $A_v$-point of $X$ in the desired open. Abstractly writing down $A_v$ is not enough. If $X(E)=\varnothing$ for one factor $E$, no global point can acquire that local component.

Here is a concrete mixed prescription. Let $d=5$ and choose two finite places $v$ and $u$. At $v$, take

$$
A_v=K_v\times E_{v,2}\times E_{v,2}',
$$

where the two quadratic fields may have different ramification. At $u$, take

$$
A_u=F_{u,5}
$$

with $F_{u,5}/K_u$ unramified of degree five. If $X$ has locally realizable points on all four field factors and the resulting degree-five configurations admit a common moving presentation, Theorem 7.1 produces one degree-five global field $L$. Above $v$ it has three places with local degrees $(1,2,2)$ and the prescribed two quadratic completions; above $u$ it has one unramified place of degree five. Globally $L/K$ need not be Galois. Indeed, these two decomposition patterns are usually easier to realize in a non-Galois field than in a Galois one.

Complete splitting at another place $z$ is incorporated by taking $A_z=K_z^5$. If the data at $v$ were initially of total rank ten while those at $u$ had rank five, one could repeat the $u$-packet twice only if repetition is allowed; one could not pretend the original exact rank-five prescription already had rank ten.

Local constancy preserves the full local field algebra, hence ramification, residue degrees, and splitting. It does not merely preserve a factorization partition. Conversely, the theorem controls only the listed places. It says nothing about ramification at places outside $S$.

### 7.5 A simultaneous finite-place theorem

Combining the preceding arguments gives the form most useful in practice.

**Theorem 7.2.** Let $X/K$ be smooth and geometrically connected of positive dimension. Partition a finite set of places as $S=S_{\mathrm{split}}\sqcup S_{\mathrm{alg}}$. At a split place choose a nonempty open $\Omega_v\subset X(K_v)$. At an algebra place choose locally realizable rank-$d$ data $(A_v,\Xi_v)$, with a common degree after allowed repetition, and assume that all the resulting degree-$d$ configurations admit one simultaneous moving-family presentation. Given a finite extension $E/K$, there exist $L/K$ and $x\in X(L)$ such that:

- $L$ is linearly disjoint from $E$;
- every $v\in S_{\mathrm{split}}$ splits completely and every conjugate of $x$ lies in $\Omega_v$;
- for $v\in S_{\mathrm{alg}}$, the algebra $L\otimes_KK_v$ and the localized point realize $(A_v,\Xi_v)$.

The proof is one application of Theorem 5.1, not an iteration. Iterating extensions would endanger conditions already achieved and would make disjointness harder to read.

## 8. The totally real theorem

### 8.1 Total reality is an all-embeddings condition

A number field $L$ is **totally real** if every embedding $L\hookrightarrow\mathbf C$ has image in $\mathbf R$. If $K$ is totally real and $L/K$ is finite, this is equivalent to

$$
L\otimes_{K,v}\mathbf R\simeq\mathbf R^{[L:K]}
$$

for every real place $v$ of $K$. Thus total reality is exactly complete splitting at all archimedean places.

Finding one real embedding is far weaker. The cubic field defined by a polynomial with one real root and one complex-conjugate pair has a real embedding but is not totally real. In the cycle language, its real local algebra is $\mathbf R\times\mathbf C$, not $\mathbf R^3$.

### 8.2 Archimedean neighborhoods

Let $v$ be real and suppose $X(K_v)=X(\mathbf R)$ is nonempty. Choose a nonempty open $\Omega_v$. In a smooth coordinate chart it contains arbitrarily many distinct real points. A degree-$d$ cycle supported on such points has algebra $\mathbf R^d$. Because simple real points remain real under sufficiently small perturbations, there is an open neighborhood in $Q_d(X)(\mathbf R)$ on which the universal algebra is still $\mathbf R^d$ and all support remains in $\Omega_v$.

This openness is the real-root stability familiar from separable polynomials. Roots can leave the real axis only by colliding first. Staying in the reduced locus keeps away from that discriminant boundary.

The hypothesis $X(\mathbf R)\ne\varnothing$ at every real place is necessary for a totally real point. If $x\in X(L)$ and $L$ is totally real, any embedding $L\hookrightarrow\mathbf R$ over $v$ produces a real point of $X$ at $v$.

### 8.3 Proof of the totally real variant

**Theorem 8.1 (totally real Moret–Bailly theorem).** Let $K$ be totally real and let $X/K$ be smooth and geometrically connected. Assume

$$
X(K_v)\ne\varnothing
$$

for every real place $v$ of $K$. Let $S_f$ be a finite set of finite places with nonempty opens $\Omega_v\subset X(K_v)$, and at each real place choose a nonempty open $\Omega_v\subset X(K_v)$. Given a finite extension $E/K$, there exist a totally real finite extension $L/K$, linearly disjoint from $E$, and $x\in X(L)$ such that every $v\in S_f$ splits completely and all localized conjugates lie in $\Omega_v$, while the same open condition holds for every embedding above each real place.

**Proof strategy and proof.** Add every real place of $K$ to the finite set of local conditions and apply Theorem 6.1 with disjointness. In its moving-family construction, use one common degree $d$, taking a split real cycle supported in $\Omega_v$ at each real place and a split cycle supported in $\Omega_v$ at each designated finite place. The conclusion gives

$$
L\otimes_{K,v}\mathbf R\simeq\mathbf R^d
$$

at every real $v$, so every embedding of $L$ is real. The finite-place and open conditions are already part of Theorem 6.1. $\square$

Notice that total reality was proved from all archimedean tensor products. It was not inferred from the existence of a real point of $X(L)$.

The familiar polynomial picture verifies the argument. Suppose $K=\mathbf Q$ and a moving degree-$d$ polynomial has, at the real parameter $h_\infty$, $d$ distinct real roots, each evaluating to a point in the desired real open. The discriminant is nonzero there. In a sufficiently small real coefficient neighborhood, the roots remain distinct and real. Choose a rational parameter in that neighborhood and in the relevant Hilbert subset. Irreducibility makes the root algebra a degree-$d$ field; persistence of $d$ real roots makes all of its embeddings real. Irreducibility alone would not do so: $T^3-2$ is irreducible and has only one real root.

Over a general totally real base there is one such real coefficient neighborhood for every real place of $K$. Weak approximation meets all of them simultaneously. This explains why the finite set of archimedean conditions grows with $[K:\mathbf Q]$ but remains finite.

### 8.4 Reality, disjointness, and finite local behavior together

The archimedean conditions, finite local algebra prescriptions, and Hilbert disjointness conditions occupy different parts of the construction and therefore coexist. At real places one takes $A_v=\mathbf R^d$. At designated finite places one takes the desired $A_v$. On the global parameter space one intersects the local boxes with the Hilbert subset enforcing connectedness after base change to $E$.

Thus Theorems 7.1 and 8.1 combine verbatim, subject to a common degree, local realizability, and one compatible moving presentation. This simultaneous statement is stronger and safer than first constructing a totally real field and then enlarging it to meet finite-place conditions: a later extension may introduce complex embeddings, destroy splitting, or meet $E$.

### 8.5 Constructing the auxiliary field itself

The theorem also gives a clean field-existence result with no moduli variety in view.

**Corollary 8.2 (totally real split fields with avoidance).** Let $K$ be totally real, let $S$ be a finite set of finite places of $K$, let $E/K$ be finite, and let $N\ge1$. There exists a finite extension $L/K$ such that

$$
[L:K]\ge N,
$$

$L$ is totally real, every $v\in S$ splits completely in $L$, and $L$ is linearly disjoint from $E$. There are infinitely many such fields. More strongly, they may be chosen successively so that their Galois closures are pairwise linearly disjoint after the corresponding stronger resolvent conditions have been included.

**Proof strategy.** Use the affine line as the variety. Small split packets at every prescribed completion and at every real place determine the local conditions. The moving construction permits the degree to be made arbitrarily large, and the base-changed incidence condition enforces avoidance.

**Proof.** Take $X=\mathbf A^1_K$. At each $v\in S$, choose a small open ball in $K_v$; at each real place choose a bounded real interval. The local moving-divisor step in Lemma 5.2 works for every sufficiently large exponent in one arithmetic progression at each of these finitely many places. Choose a common allowed exponent for which the resulting degree is $d\ge N$, and use split divisors supported in the selected balls and intervals. Apply Theorem 8.1 with avoidance field $E$. The output satisfies

$$
L\otimes_KK_v\simeq K_v^d\quad(v\in S),
\qquad
L\otimes_{K,v}\mathbf R\simeq\mathbf R^d\quad(v\mid\infty),
$$

and $L\otimes_KE$ is a field. These identities are respectively complete splitting, total reality, and linear disjointness.

To obtain infinitely many fields, after constructing $L_1,\ldots,L_m$, enlarge the avoidance field by the compositum of their normal closures and apply the result again. The new field cannot equal any previous one. For the stronger assertion about normal closures, use on $\mathbf A^1$ the universal monic degree-$d$ polynomial family with $d\ge\max\{N,2\}$. At the listed finite and real places choose coefficient neighborhoods of split polynomials with all roots in the selected balls or intervals. Its generic splitting field is regular with group $S_d$. The full-group and base-changed resolvent conditions from Book 153 then produce a totally real degree-$d$ root field whose normal closure is disjoint from the previous compositum. Induction gives pairwise linearly disjoint normal closures. At each stage only finitely many local and resolvent conditions are added. $\square$

This corollary quantifies exactly what is and is not controlled. The lower bound $N$ is arbitrary, but no prescribed exact degree, discriminant bound, solvability, or normality is asserted. Complete splitting is forced only at the listed places. Ramification elsewhere is finite but uncontrolled.

### 8.6 What changes when the base is not totally real

If $K$ has a complex place, no finite extension $L/K$ is a totally real number field, because an embedding $K\hookrightarrow\mathbf C$ with nonreal image extends to an embedding of $L$. One may instead prescribe the signature of $L$ above each archimedean place through local algebras $\mathbf R^r\times\mathbf C^s$; above a complex place the algebra is necessarily $\mathbf C^d$.

Accordingly, the phrase “totally real variant” has the exact hypothesis that $K$ itself is totally real. Without it, the meaningful conclusion is signature control relative to $K$, not total reality in the absolute sense.

## 9. Finite étale covers, twists, and monodromy

### 9.1 Lifting local conditions through a cover

Many moduli conditions are easiest to express after passing to a finite étale cover. Let

$$
\pi:Y\longrightarrow X
$$

be finite étale, with $X$ smooth and geometrically connected. Suppose that at every designated place $v$ one has a nonempty open $\Theta_v\subset Y(K_v)$. If there is a $K$-defined open-and-closed subscheme $Y^\circ\subset Y$ that is geometrically connected and whose local points meet every $\Theta_v$, then Theorem 6.1 applied to $Y^\circ$ gives $y\in Y^\circ(L)$; its image $x=\pi(y)$ has the desired local lifts.

The connected-component hypothesis matters. A connected finite étale cover over $K$ can become disconnected over $\overline K$. Its components may be permuted through a constant extension. Applying the theorem to such a cover without choosing a geometrically connected component can force the residue field to contain that constant field and can contradict a requested disjointness condition.

There is a second, different requirement: instead of asking that $x$ lift to $Y(L)$, one may ask that the fiber $Y_x$ be connected, or that its monodromy avoid specified proper subgroups. Connectedness and full-group conditions are Hilbert conditions after the cover and its resolvents have been pulled back to the moving parameter space. An arbitrary prescribed factorization of $Y_x$ over the varying global field $L$ is not automatically a Hilbert condition. Local factorization can be imposed at designated completions through actual locally realizable fibers; a global orbit pattern requires a separate finite-cover construction whose generic monodromy supports that pattern.

### 9.2 Connected components and twists

A **twist** replaces a cover by another form that becomes isomorphic after a finite separable extension. Suppose for simplicity that $Y\to X$ is a finite étale Galois cover with group $G$, and let

$$
c:G_K\longrightarrow G
$$

be a continuous cocycle for the relevant action. Twisting changes the arithmetic descent action by $c$ but leaves the geometric cover unchanged. An $L$-point of the twist corresponds, after choosing an identification over a separable closure, to a point of $Y$ whose Galois descent is prescribed by $c|_{G_L}$.

This device turns a desired torsor class or level-structure action into an ordinary point problem. The safe procedure is:

1. construct the twist and identify a smooth geometrically connected component;
2. verify nonempty local opens on that component at every designated place;
3. apply the simultaneous Moret–Bailly theorem to the component;
4. translate the resulting point back through the twisting correspondence.

One cannot select a component solely by naming a geometric component over $\overline K$ if it is not defined over $K$. Its stabilizer determines a constant field, and the theorem must be applied over that field or to a $K$-defined union with the corresponding consequences for disjointness.

A Kummer example makes the translation explicit. Let $X=\mathbf G_m$ and consider the finite étale cover

$$
Y\longrightarrow X,\qquad y^m=x,
$$

over a field containing the relevant roots of unity, with $m$ invertible. Twisting by a class $a\in K^\times/K^{\times m}$ gives, with one choice of convention,

$$
Y^{(a)}:\quad y^m=ax.
$$

An $L$-point on the twist is a pair $(x,y)$ with $y^m=ax$, so the class of $x$ in $L^\times/L^{\times m}$ is $a^{-1}$ with this convention. Replacing $a$ by $a^{-1}$ gives the opposite convention; in either form the Kummer class of $x$ is prescribed. Local solvability means exactly that the same equation has a point in every selected completion. Applying the theorem to the geometrically connected twist globalizes those local solutions while controlling $L$.

If instead one applies the theorem only to $X$, then asking that $Y_x$ be connected says that $T^m-x$ remains irreducible over $L$. Asking for a lift says that it has a root. These are incompatible for $m>1$. The twist and fiber formulations therefore encode genuinely different arithmetic demands.

### 9.3 Selecting a monodromy class

Let $Y\to X$ be a finite étale cover with geometric fiber $F$ and arithmetic monodromy group $G\subset\operatorname{Perm}(F)$. For a closed point $x$ with residue field $L$, the fiber $Y_x$ corresponds to the restriction of the monodromy action to $G_L$. Requiring $Y_x$ to be connected means that this restricted action is transitive. Requiring a specified factorization means prescribing its orbit sizes.

When the local fiber at a finite place is unramified, a Frobenius element acts on $F$, and its cycle lengths give the residue degrees of that fiber. Hence a conjugacy class $C\subset G$ can be selected by choosing a locally realizable point whose unramified Frobenius lies in $C$, then shrinking to a neighborhood on which the finite étale algebra is constant. The conclusion is necessarily “up to conjugacy,” because changing a point above the base conjugates the decomposition data.

For ramified local behavior, a conjugacy class of one element is insufficient. The whole decomposition group and inertia subgroup govern the local algebra. The correct input is an actual local fiber, not an abstract class that may violate local ramification constraints.

Globally, full generic monodromy can be retained when the pulled-back cover over the moving family has the required regular generic monodromy. One then adds the resolvent Hilbert conditions of Book 153. Since only finitely many maximal subgroups occur in a finite group, this costs a finite intersection of Hilbert subsets. If the pullback acquires a constant subextension or smaller generic group, no specialization argument restores the lost monodromy. The incidence cover must still be included separately to ensure that the residue algebra of the point itself is a field.

The residue-field Galois closure and the cover monodromy should also be distinguished. The former comes from the action on the $d$ conjugates of the closed point. The latter comes from the action on the fiber $F$ of $Y\to X$. They define two finite permutation representations on the same specialization parameter, but neither generally determines the other. The simultaneous Hilbert argument takes their product cover, or equivalently intersects the corresponding resolvent conditions, and controls both at once.

### 9.4 Limits of the cover variant

Three limitations prevent overstatement.

First, a desired orbit pattern must occur in the monodromy action. A cycle type absent from $G$ cannot appear at an unramified specialization with full group. Second, local behavior must be represented by a point in the chosen local family. Hilbert irreducibility preserves available fibers; it does not manufacture unavailable ones. Third, a lift to $Y$ and a connected fiber of $Y_x$ are opposite kinds of conditions in many covers: a lift gives a fixed point, while connectedness demands transitivity. They should not be imposed simultaneously without checking that the action permits both.

The cover formulation is therefore a translator. It converts finite étale geometric data into finite Hilbert and local-open conditions. It is not a theorem that arbitrary monodromy instructions are compatible.

## 10. Avoidance and density

### 10.1 Removing a closed subset

Let $Z\subsetneq X$ be closed. Since $X$ is smooth and geometrically connected, $X\setminus Z$ is a nonempty smooth geometrically connected open whenever $Z$ does not contain the generic point. Apply Theorem 6.1 to $X\setminus Z$. At each place replace $\Omega_v$ by

$$
\Omega_v\cap(X\setminus Z)(K_v).
$$

This intersection is nonempty for positive-dimensional $X$: a proper closed subvariety has empty interior in the analytic manifold near a smooth point. If a given $\Omega_v$ happened to consist only of points of $Z$, that would contradict openness unless the local component itself lay in $Z$; geometric connectedness and smoothness rule out such a component for proper $Z$.

The resulting closed point avoids $Z$. This argument can remove a finite union of closed subsets in one step. It is better to remove them before constructing the parameter space, because then every universal support point automatically avoids them.

### 10.2 Zariski density over varying fields

Let $\mathscr P$ be the set of closed points produced while keeping fixed local opens, total-reality requirements, and disjointness from $E$. Then $\mathscr P$ is Zariski dense in $X$. Indeed, if its closure were a proper closed subset $Z$, the avoidance form would produce another permitted point in $X\setminus Z$, a contradiction.

This is density of closed points with varying residue fields. It does not say that $X(L)$ is dense for one fixed $L$, nor even that one field works for infinitely many prescribed open boxes. Each invocation may produce a different field and degree.

The same argument gives density inside any nonempty open $U\subset X$: replace $X$ by $U$. In moduli applications this permits simultaneous avoidance of automorphism loci, degenerate discriminants, and finitely many exceptional geometric conditions.

### 10.3 Avoidance together with local constraints

Closed-subset avoidance and field disjointness solve different problems. Removing $Z$ controls where the point lies on $X$. Imposing a Hilbert condition after base change to $E$ controls the intersection of its residue field with $E$. Both are compatible because the first shrinks the geometric parameter space and the second removes a thin set of arithmetic parameters.

For example, one may require a totally real field $L$, complete splitting at a set $S$, a prescribed ramified algebra at an auxiliary prime, $L$ linearly disjoint from $E$, and $x\notin Z$. One first verifies the local data on $X\setminus Z$, constructs all local cycles of one degree, and applies the simultaneous theorem once.

Avoiding an infinite list of closed subsets is different. A countable union can contain all algebraic points even when no member is dense. The theorem handles any finite union at one time; an infinite sequence can be handled inductively only by allowing the residue field and point to change at every stage.

### 10.4 Why one fixed extension is different

It is tempting to hope for one finite $L/K$ such that $X(L)$ meets every later local requirement. Moret–Bailly’s theorem does not say this. Its flexibility comes precisely from choosing the residue field along with the point. Once $L$ is fixed, the problem becomes weak approximation for $X_L$, which can fail for familiar geometric and arithmetic reasons.

Similarly, taking the compositum of fields produced by separate applications does not combine the conclusions. Places that split completely in each of two extensions do split in their compositum, but disjointness from $E$ may fail, total degree changes, and a point defined over one factor need not satisfy conjugate conditions for embeddings of the compositum. The simultaneous theorem should be used from the start.

## 11. Examples and failures

### 11.1 Affine space with coefficient conditions

Take $X=\mathbf A_K^n$. Let $S$ be finite and let $\Omega_v$ be an open box around $a_v\in K_v^n$. Ordinary weak approximation already produces a $K$-point in all boxes, so one may take $L=K$ if no disjointness beyond the trivial one is required.

The theorem becomes nontrivial when one asks for a new field with prescribed completions. Choose degree-$d$ étale algebras $A_v$ and elements

$$
\alpha_v=(\alpha_{v,1},\ldots,\alpha_{v,n})\in A_v^n
$$

whose geometric coordinates are distinct as points of affine space. After a generic linear change of coordinates, the first coordinate may be required to generate the whole product algebra $A_v$: this is the open condition that its values under all geometric homomorphisms $A_v\to\overline K_v$ be pairwise distinct. The universal polynomial coefficient space then supplies the required common moving presentation, so Theorem 7.1 produces a degree-$d$ field $L$, an isomorphism $L\otimes_KK_v\simeq A_v$, and $\alpha\in L^n$ close to every $\alpha_v$. Globally, the connected incidence condition makes the full point have residue field $L$.

A one-variable laboratory is particularly transparent. Let $X=\mathbf A^1$ and choose $d$ distinct elements in each $K_v$. Their elementary symmetric functions determine a separable local monic polynomial. Weak approximation chooses global coefficients, and Hilbert irreducibility makes the global polynomial irreducible. Its root gives the closed point. The general proof is the coordinate-free version of this calculation.

### 11.2 Curves

Let $C/K$ be a smooth geometrically connected curve, possibly of positive genus, and suppose $C(K_v)$ contains a nonempty open $\Omega_v$ for every $v\in S$. The theorem gives a closed point $P$ whose local conjugates all lie in those arcs or residue disks.

On a projective curve, one can see the moving construction through divisors. The moving-family lemma chooses a sufficiently positive line bundle together with local sections whose zeros all lie in $\Omega_v$; the simultaneous choice of the line bundle and local members is part of the construction, not a consequence of weak approximation for an arbitrary divisor class. Sections form a projective space, and away from the discriminant a section has a reduced divisor of degree $d$. Weak approximation chooses a global nearby section, and Hilbert irreducibility forces its divisor to be irreducible over $K$. The irreducible divisor is the desired closed point.

Positive genus explains why one should not claim that every symmetric power is affine or rational. For $d$ large, $\operatorname{Sym}^d(C)$ maps to $\operatorname{Pic}^d(C)$ with projective-space fibers. The proof works in a tailored moving linear system, not by asserting weak approximation on the entire symmetric power.

As a concrete case, let $C$ be the affine curve

$$
y^2=x^3-x+1
$$

with a finite set of small local neighborhoods avoiding the points where $y=0$. The theorem produces a closed point of $C$ whose conjugates retain $y\ne0$ locally, while its residue field can be made disjoint from a fixed $E$. If $K$ is totally real and every real component has a chosen arc, the field can be taken totally real and every real conjugate lies in its designated arc.

### 11.3 A frame variety

Consider

$$
X=\operatorname{Spec}K[a,b,c,d,u]/(u(ad-bc)-1).
$$

Projection to $(a,b,c,d)$ identifies $X$ with $\operatorname{GL}_{2,K}$, with $u$ recording the inverse determinant. It is smooth and geometrically connected. One may regard its points as ordered frames together with a certificate of nondegeneracy, a simple model for a fine moduli problem with a level structure.

At a residue-characteristic place, require the matrix to lie in a chosen congruence neighborhood. At an auxiliary place, require its characteristic polynomial to have distinct roots and its determinant to lie in a chosen square class. At real places, require positive determinant and place the columns in specified open cones. All are open conditions after the determinant-zero boundary is removed.

The totally real simultaneous theorem gives a field $L$ and one frame over $L$ whose every localized conjugate has the prescribed behavior. A finite étale cover obtained by adjoining an $m$-th root of the determinant can be included if its locally desired twist has a geometrically connected component and local points. This example displays the architecture of a moduli application without using the specialized varieties reserved for the next book.

### 11.4 Counterexamples and boundary phenomena

The hypotheses and formulations exclude several genuine failures.

**Rational points are too much to ask.** A smooth projective curve of genus at least one can have points over every completion and no $K$-point. Even when a rational point exists, weak approximation may fail. Allowing the residue field to vary is essential.

**Geometric connectedness controls constants.** Let $M/K$ be a nontrivial finite separable extension and take $X=\operatorname{Spec}M$. It is smooth and connected over $K$ but not geometrically connected. Any $X(L)$-point gives a $K$-embedding $M\hookrightarrow L$. Hence $L$ cannot be linearly disjoint from the normal closure of $M$. The disjoint conclusion fails exactly because a constant field is built into $X$.

**Smoothness supplies movable local points.** Over a real number field consider the geometrically integral quadric cone

$$
x^2+y^2+z^2=0.
$$

Its real locus is only the singular vertex. The singleton is open in the real locus, so any real local condition forces the point into the closed singular subset. The Zariski-open avoidance and reduced moving-cycle argument cannot hold there. A theorem for singular varieties must require local opens meeting a suitable smooth geometrically connected locus; merely deleting the word “smooth” loses the deformation mechanism.

**Nonempty local opens are necessary.** If $X(K_v)=\varnothing$, then no extension in which $v$ splits completely can yield an $L$-point: every completion above $v$ would be $K_v$. Likewise an empty prescribed open cannot be met.

**Local data must be realizable.** If $A_v$ has a factor $E$ with $X(E)=\varnothing$, there is no point in $X(A_v)$. No global field can have completion algebra $A_v$ and support an $X$-point. At a real place, demanding a totally real output while prescribing a $\mathbf C$ factor is internally contradictory.

**A zero-cycle need not be a point.** On any variety with two rational points $P,Q$, the cycle $P+Q$ has degree two but residue algebra $K\times K$. Without the Hilbert connectedness condition it does not produce a quadratic field.

**One acceptable completion is not enough.** A cubic field may have local algebra $K_v\times E_v$ with $E_v/K_v$ quadratic. A point may satisfy the desired condition on the $K_v$ factor and fail it on the quadratic factor. Statements quantified over every embedding require control of both.

**Exact degree can be obstructed.** On a variety of index $m>1$, every closed-point degree is divisible by $m$. Locally realizable rank-$d$ data with $m\nmid d$ cannot be globalized to one degree-$d$ point. Flexible-degree formulations avoid this by choosing an admissible degree; exact algebra formulations must state compatibility.

**The output is not automatically Galois.** An irreducible cubic with nonsquare discriminant defines a non-Galois cubic field. Its three conjugates form a transitive configuration, exactly as the proof requires. Passing to its degree-six Galois closure changes both degree and local tensor products.

## 12. A practical package for arithmetic geometry

### 12.1 Local inputs from a moduli problem

In arithmetic geometry, $X$ often parametrizes objects carrying rigidifying structures. The theorem begins only after the geometric work has established that a relevant component is smooth and geometrically connected. Local constructions then supply points in several kinds of completions.

At a finite place, an integral model may provide a smooth special-fiber point. Hensel lifting gives a local point, and smoothness makes the set of lifts of the desired reduction an open residue disk. If the property is expressed by invertibility of a discriminant, nonvanishing of a determinant, or étaleness of a finite group scheme, it remains true on a sufficiently small disk.

At an archimedean place, topology may select a connected component, sign, polarization type, or ordering. These are encoded by a nonempty open subset of the real manifold. For a totally real conclusion, such an open must be supplied at every real place of the base.

The theorem does not construct these local points and does not prove smoothness or geometric connectedness of the moduli variety. Those are the geometric inputs. Its role is to globalize all of them without losing control of the residue field. The specific moduli spaces, twists, representability arguments, and local-solvability proofs used in potential modularity are developed in the subsequent volume and are not assumed here.

### 12.2 Auxiliary primes and residue-characteristic primes

Three classes of places commonly enter one application.

At primes equal to a residue characteristic of interest, the local open records the required integral or finite-flat behavior. One must verify openness on the generic-fiber variety, often by choosing a smooth integral point and a small congruence neighborhood.

At auxiliary primes, one may impose a Frobenius pattern, a splitting condition, or a condition designed to preserve large monodromy. If this is expressed through a finite étale cover, the desired local fiber must actually occur. Local constancy then turns it into an open condition.

At all real places, one supplies real points and neighborhoods ensuring the intended component and total reality. Omitting even one real place permits complex embeddings above it.

All these places form one finite set. Add to it any places used to force complete splitting. Choose the field $E$ containing every finite extension that the output must avoid, preferably the compositum of normal closures. Finally remove from $X$ every closed degeneracy locus. These preparations convert the application into one invocation of the reusable theorem.

### 12.3 The reusable theorem

The following formulation is designed for later potential-modularity arguments while remaining independent of any particular moduli space.

**Theorem 12.1 (simultaneous Moret–Bailly package).** Let $K$ be a totally real number field and let $X$ be a smooth geometrically connected $K$-variety. Let $Z\subsetneq X$ be closed and let $E/K$ be finite. Assume:

1. for every real place $v$ of $K$, there is a nonempty open
   $$
   \Omega_v\subset (X\setminus Z)(K_v);
   $$
2. at each place in a finite split set $S_{\mathrm{split}}$, there is a nonempty open
   $$
   \Omega_v\subset (X\setminus Z)(K_v);
   $$
3. there is one common degree $d$ such that, at each place in a finite algebra set $S_{\mathrm{alg}}$, there is a locally realizable rank-$d$ finite étale algebra datum $(A_v,\Xi_v)$ on $X\setminus Z$, with all exact-degree requirements compatible after any explicitly allowed repetition, and the algebra configurations together with chosen degree-$d$ split configurations at the real and split places admit one simultaneous moving-family presentation;
4. any finite étale cover, twist, component, or monodromy condition has been converted into finitely many locally realizable open conditions and Hilbert subsets on a geometrically connected moving family.

Then there exist a finite extension $L/K$ and $x\in(X\setminus Z)(L)$ such that:

- $L$ is totally real;
- $L$ is linearly disjoint from $E$ over $K$;
- every $v\in S_{\mathrm{split}}$ splits completely in $L$, and every embedding above $v$ sends $x$ into $\Omega_v$;
- $L\otimes_KK_v\simeq A_v$ with the prescribed point behavior for $v\in S_{\mathrm{alg}}$;
- every real embedding above $v$ sends $x$ into $\Omega_v$;
- all stated finite Hilbert or monodromy conditions hold.

The field $L/K$ is finite and separable but is not asserted to be Galois. Its degree is chosen by the construction unless exact compatible rank has been included in the input.

**Proof.** First replace $X$ by $X\setminus Z$. If an actual lift to a twist or cover is required, apply the construction to the chosen geometrically connected component and compose its point back to $X$. If instead a fiber-monodromy condition is required, keep $X\setminus Z$ as the point space and pull the relevant cover and resolvents back to its moving family. These two operations must not be conflated.

Construct reduced local cycles of one compatible degree: split cycles at the real and split places, and the specified configurations at algebra places. Use the presentation included in hypothesis 3, or the flexible case of Lemma 5.2 when every condition is split, to place them in one affine moving family. Intersect all local boxes with the finite collection of Hilbert subsets enforcing connected incidence fiber, disjointness after base change to $E$, and every requested cover condition whose regular generic compatibility was verified in hypothesis 4. Book 153's approximation theorem supplies a parameter in this intersection. The connected incidence fiber is $\operatorname{Spec}L$ and evaluates to $x$. The real local algebras are $\mathbf R^{[L:K]}$, proving total reality; the other tensor products give the claimed local behavior. $\square$

### 12.4 A verification checklist

Before invoking Theorem 12.1, verify each item below.

1. **Base field.** Is $K$ totally real if total reality is requested? Have all its real places been listed?
2. **Geometry.** Is the chosen variety, open, cover component, or twist smooth and geometrically connected over $K$?
3. **Local nonemptiness.** Is every local open genuinely nonempty on that same component?
4. **Openness.** Are integral, reduction, sign, and level conditions stable under a small local perturbation?
5. **Every embedding.** Does the desired conclusion require complete splitting, or is a general local algebra the correct input?
6. **Local algebra.** Do all factors have points, are conjugates separable and distinct, and do exact ranks agree?
7. **Degree and presentation.** Is degree flexible, may local packets be repeated, or is there an index obstruction to an exact degree? Do all fixed-rank configurations occur in one moving presentation?
8. **Archimedean control.** Are all real sheets required to stay real, rather than merely one?
9. **Disjointness.** Has one finite field $E$ been chosen large enough, usually using normal closures, and is linear disjointness of $L$ sufficient? If the Galois closure must be disjoint, have the stronger resolvent conditions been imposed?
10. **Covers and twists.** Is the desired component defined over the base, and is the monodromy pattern actually realizable?
11. **Avoidance.** Have all unwanted geometric loci been removed before constructing local cycles?
12. **Output language.** Is $L$ treated as the residue field of one closed point, with no unsupported claim that it is Galois?

If these checks pass, the theorem turns the local construction into one global point over a controlled field. If one fails, the failure usually identifies real mathematical work still required: proving local solvability, identifying the correct component, changing the degree, or weakening an impossible decomposition demand.

### 12.5 Conclusion

Moret–Bailly’s theorem is a local-to-global theorem whose freedom lies in the field of definition. Smoothness makes local points movable; geometric connectedness removes constant-field obstructions; symmetric powers organize conjugates as reduced cycles; and the universal incidence cover remembers whether that cycle is one point or many. Weak approximation places a parameter in all prescribed local neighborhoods, while Hilbert irreducibility makes the incidence fiber connected and preserves disjointness and monodromy conditions.

The resulting field is controlled through its tensor products with the chosen completions. Complete splitting means every designated embedding sees the required local point. Real split fibers at every archimedean place mean every embedding is real. General finite étale local algebras record richer splitting and ramification patterns, provided they are locally realizable, degree-compatible, and carried by one moving presentation. Removing closed subsets gives density, and finite étale covers or twists translate additional structure into local and Hilbert conditions.

The final lesson is precise: local points do not by themselves yield a rational point, and a zero-cycle does not by itself yield a field. The theorem succeeds because it moves the local data in a sufficiently large family and then uses arithmetic irreducibility to bind all conjugates into one closed point. That point, and its non-Galois residue field with every completion explicitly accounted for, is the robust global object needed in the arithmetic constructions that follow.
