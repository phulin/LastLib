# Presentation-Independent Properness for Quaternionic PEL Realizations

## Contents

1. [The precise boundary theorem](#1-the-precise-boundary-theorem)
   - [The gap between generic compactness and integral properness](#11-the-gap-between-generic-compactness-and-integral-properness)
   - [What the PEL catalog actually admits](#12-what-the-pel-catalog-actually-admits)
   - [Catalog-good integral places](#13-catalog-good-integral-places)
2. [Polarized Raynaud data and variance](#2-polarized-raynaud-data-and-variance)
   - [The three rational pieces](#21-the-three-rational-pieces)
   - [Left actions, character actions, and the Rosati involution](#22-left-actions-character-actions-and-the-rosati-involution)
   - [The outer pairing and tropical isomorphism](#23-the-outer-pairing-and-tropical-isomorphism)
   - [Geometric Tate realizations, including the residue prime](#24-geometric-tate-realizations-including-the-residue-prime)
3. [The toric determinant bridge](#3-the-toric-determinant-bridge)
   - [The action on the Lie algebra of the torus](#31-the-action-on-the-lie-algebra-of-the-torus)
   - [The positive toric Hodge block](#32-the-positive-toric-hodge-block)
   - [Logarithmic de Rham and determinant factorization](#33-logarithmic-de-rham-and-determinant-factorization)
   - [The opposite-Hodge convention and orientation](#34-the-opposite-hodge-convention-and-orientation)
4. [The global middle form](#4-the-global-middle-form)
   - [The polarized abelian quotient](#41-the-polarized-abelian-quotient)
   - [Betti construction over a finitely generated field](#42-betti-construction-over-a-finitely-generated-field)
   - [Comparison with every finite realization](#43-comparison-with-every-finite-realization)
   - [The global assembly theorem](#44-the-global-assembly-theorem)
5. [The exact polarized Morita packets](#5-the-exact-polarized-morita-packets)
   - [Reduction to classical packets](#51-reduction-to-classical-packets)
   - [Invariants and scalar change](#52-invariants-and-scalar-change)
   - [Local classification in the ranks that occur](#53-local-classification-in-the-ranks-that-occur)
   - [Global existence and product compatibility](#54-global-existence-and-product-compatibility)
   - [Real signatures and common multipliers](#55-real-signatures-and-common-multipliers)
6. [Odd self-dual packet lattices](#6-odd-self-dual-packet-lattices)
   - [The standard integral packets](#61-the-standard-integral-packets)
   - [Alternating, exchange, and unitary packets](#62-alternating-exchange-and-unitary-packets)
   - [Orthogonal and quaternionic packets](#63-orthogonal-and-quaternionic-packets)
   - [Morita transfer, orientation, and one common multiplier](#64-morita-transfer-orientation-and-one-common-multiplier)
   - [The dyadic boundary](#65-the-dyadic-boundary)
7. [Catalog-by-catalog audit](#7-catalog-by-catalog-audit)
   - [Direct quaternion trace presentation](#71-direct-quaternion-trace-presentation)
   - [Matrix Morita presentations](#72-matrix-morita-presentations)
   - [The split-corestriction admission test](#73-the-split-corestriction-admission-test)
   - [The hyperbolic admission test](#74-the-hyperbolic-admission-test)
   - [The binary-unitary replacement](#75-the-binary-unitary-replacement)
   - [Central modifications](#76-central-modifications)
   - [Exhaustion and the complete comparison table](#77-exhaustion-and-the-complete-comparison-table)
8. [The similarity torsor and its adjoint Hasse kernel](#8-the-similarity-torsor-and-its-adjoint-hasse-kernel)
   - [The oriented similarity bitorsor](#81-the-oriented-similarity-bitorsor)
   - [Hasse injectivity for the quaternionic adjoint group](#82-hasse-injectivity-for-the-quaternionic-adjoint-group)
   - [Why no central lifting assertion is needed](#83-why-no-central-lifting-assertion-is-needed)
9. [Monodromy produces a forbidden parabolic](#9-monodromy-produces-a-forbidden-parabolic)
   - [The weight cocharacter and the nonzero operator](#91-the-weight-cocharacter-and-the-nonzero-operator)
   - [Noncentrality and properness](#92-noncentrality-and-properness)
   - [The division contradiction and false-flag audit](#93-the-division-contradiction-and-false-flag-audit)
10. [From potential reduction to properness](#10-from-potential-reduction-to-properness)
    - [Potential good reduction](#101-potential-good-reduction)
    - [Odd auxiliary level kills finite inertia](#102-odd-auxiliary-level-kills-finite-inertia)
    - [Extension of every PEL structure](#103-extension-of-every-pel-structure)
    - [The fine properness theorem](#104-the-fine-properness-theorem)
11. [Finite central quotients before properness](#11-finite-central-quotients-before-properness)
   - [The actual deck group and the central cohomology obstruction](#111-the-actual-deck-group-and-the-central-cohomology-obstruction)
   - [The quaternionic-line--binary-unitary common refinement](#112-the-quaternionic-line--binary-unitary-common-refinement)
   - [Extension of deck transformations to the integral PEL scheme](#113-extension-of-deck-transformations-to-the-integral-pel-scheme)
   - [The finite integral quotient](#114-the-finite-integral-quotient)
   - [Fine, stack, and coarse conclusions](#115-fine-stack-and-coarse-conclusions)
12. [The presentation-independent theorem](#12-the-presentation-independent-theorem)
    - [Main theorem](#121-main-theorem)
    - [Hypothesis and conclusion ledger](#122-hypothesis-and-conclusion-ledger)
    - [Dependency closure](#123-dependency-closure)
    - [Final synthesis](#124-final-synthesis)

## 1. The precise boundary theorem

### 1.1 The gap between generic compactness and integral properness

Let $F$ be totally real, let $B/F$ be a quaternion division algebra split at exactly one real place, and put

$$
G^{\mathrm{ad}}=\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B).
\tag{1.1}
$$

The associated complex Shimura curve is compact because $G^{\mathrm{ad}}$ has no rational proper parabolic. That fact proves properness of the generic canonical curve. It does not by itself prove properness of a spread-out PEL functor. A trait-valued point can fail to extend as an abelian scheme even when its image extends to an abstract proper model of the generic curve.

After finite extension, a semistable abelian variety has a Raynaud extension

$$
0\longrightarrow T\longrightarrow \mathcal G
\longrightarrow A_0\longrightarrow0
\tag{1.2}
$$

and a period lattice $Y$. The only boundary direction is the torus $T$. The task is therefore to prove that $T=0$ without assuming that the faithful PEL module is the quaternion algebra itself.

The proof has four genuinely different parts. First, the torus and period lattice must be turned into a rational polarized block with the correct $D$-action. Second, its determinant contribution must be identified with the actual Lie-theoretic determinant condition, not guessed from toric rank. Third, the abelian quotient $A_0$ must supply one global middle form; unrelated local middle spaces are not enough. Fourth, the resulting monodromy flag must be transported only through the adjoint similarity torsor, because a central lifting obstruction can survive.

There is also a geometric scope boundary. The boundary argument controls specializations of the selected characteristic-zero component; it cannot, by itself, rule out unrelated vertical components of an ambient determinant scheme. Accordingly, the **integral PEL model** in the properness theorem means the schematic flat closure of the selected generic component union inside the Book 127 ambient PEL scheme. Equality with the whole ambient scheme is a separate flatness statement and is never assumed here.

### 1.2 What the PEL catalog actually admits

Fix a quaternionic PEL realization in the sense of Book 127,

$$
\mathscr D=(D,*,V,\psi,h),
\qquad
G_{\mathscr D}=\operatorname{GSim}_D(V,\psi)^\circ,
\tag{1.3}
$$

with

$$
G_{\mathscr D}^{\mathrm{ad}}\simeq G^{\mathrm{ad}}.
\tag{1.4}
$$

Here $D$ is semisimple, $*$ is positive, $V$ is a faithful left $D$-module, and

$$
\psi(bx,y)=\psi(x,b^*y).
\tag{1.5}
$$

There is an important scope correction. Book 127 does not declare every symplectic representation in Book 123 to be PEL-exact. It admits a direct trace realization when its involution is positive, a binary-unitary realization with positive CM involution, a split-corestriction realization only after its central kernel and its full stabilizer have been checked, and a compatible central modification. Matrix Morita transfer preserves an already exact datum. Hyperbolic enlargement supplies an alternating representation, but PEL admission still requires both the exact commutant and a positive acting algebra with involution.

Accordingly, a **catalog presentation** in this book means one of the following, with the stated exactness calculation included:

1. the direct quaternion trace datum;
2. the binary-unitary replacement of Section 7.5;
3. a matrix Morita transfer of any admitted datum;
4. a split-corestriction block passing the stabilizer test of Section 7.3;
5. a hyperbolic alternating enlargement passing both the commutant and positivity tests of Section 7.4; or
6. a connected central modification or common refinement of presentations 1--5.

A tensor representation whose stabilizer still needs a higher tensor is not a PEL realization under (1.3). Section 7 proves, rather than assumes, the sharp restriction this imposes on corestriction and hyperbolic blocks. It also proves that, for the one-active-factor datum, the only genuinely different positive noncentral Morita packet left by the Book 127 hypotheses is the binary-unitary plane. Thus the word “presentation” below is not restricted to coordinates on a quaternionic line.

### 1.3 Catalog-good integral places

The boundary argument uses no local-model smoothness theorem. Its integral hypotheses concern only orders, lattices, levels, and finite central descent.

**Definition 1.1 (catalog-good place).** Let $v$ lie over the rational prime $p$. The place is catalog-good for $\mathscr D$ if:

1. $p$ is odd;
2. every center occurring in $D\otimes\mathbf Q_p$ is unramified, the chosen order $\mathcal O_p$ is maximal and hereditary, and $*$ preserves it;
3. the lattice $\Lambda_p$ is self-dual for the integral alternating form, and its stabilizer is the hyperspecial subgroup selected by the generic component;
4. the polarization degree is a $p$-adic unit;
5. the discriminant, determinant, multiplier-component, and orientation labels of the selected generic lattice genus are fixed, packet by packet;
6. every central modification used at $v$ has $p$-integral representatives, every finite group-scheme kernel occurring in it has order prime to $p$, and its effective deck set at the chosen level is finite; and
7. the adjoint packet is unramified and quasi-split at $p$.

Condition 7 follows from the existence of a hyperspecial adjoint stabilizer, but it is displayed because it is exactly what produces the standard Witt bases in Chapter 6. Conditions 2--5 imply, by the explicit odd integral classification proved there, that every lattice packet is one of the standard packets. No smoothness or flatness of a determinant local model is part of the definition.

At $p=2$, rational Hilbert symbols remain valid, but the integral classification in Chapter 6 does not. The theorem will state the exact additional dyadic genus hypothesis rather than infer it from rational invariants.

## 2. Polarized Raynaud data and variance

The main source of sign and side errors is the coexistence of covariant cocharacters, contravariant characters, dual abelian varieties, and the Rosati involution. We therefore establish the variance before constructing any form.

### 2.1 The three rational pieces

Let $R$ be a complete discrete valuation ring of mixed characteristic $(0,p)$ with fraction field $L$. Let

$$
(A,\iota,\lambda,\eta)/L
\tag{2.1}
$$

be a point of the generic PEL curve. After a finite separable extension, assume that $A$ is semistable and that its Raynaud torus is split. Write its one-motive as

$$
M_A=[Y\longrightarrow\mathcal G]
\tag{2.2}
$$

with (1.2). Put

$$
X=X_*(T)\otimes_{\mathbf Z}\mathbf Q,
\qquad
Y_{\mathbf Q}=Y\otimes_{\mathbf Z}\mathbf Q.
\tag{2.3}
$$

Every integral endomorphism of $A$ extends uniquely to its Neron model and acts functorially on the Raynaud extension and period lattice. Tensoring with $\mathbf Q$ therefore makes $X$, $Y_{\mathbf Q}$, and the rational realizations of $A_0$ left $D$-modules.

### 2.2 Left actions, character actions, and the Rosati involution

For $b\in\mathcal O$, let $b_T:T\to T$ be induced by $\iota(b)$; all formulas below then extend $\mathbf Q$-linearly to $D=\mathcal O\otimes\mathbf Q$. On cocharacters the action is covariant:

$$
b\cdot x=b_T\circ x.
\tag{2.4}
$$

It is a left action because $(bc)_T=b_T\circ c_T$. On characters, pullback is contravariant. Thus

$$
\chi\cdot b=\chi\circ b_T
\tag{2.5}
$$

is a right $D$-action, or equivalently a left $D^{\mathrm{op}}$-action. Confusing (2.4) and (2.5) reverses every later adjoint formula.

The period action is covariant. If $b_Y:Y\to Y$ is induced by $\iota(b)$, then

$$
(bc)_Y=b_Y\circ c_Y.
\tag{2.6}
$$

The identification $Y\simeq X^*(T_{A^\vee})$ from dual Raynaud theory is compatible with (2.6): dualization reverses $b$ and $c$, and character pullback reverses them a second time.

The polarization identity

$$
\lambda\iota(b)=\iota(b^*)^\vee\lambda
\tag{2.7}
$$

is what places $*$ in the outer pairing below. It is not part of the definition of the left action on $Y$.

### 2.3 The outer pairing and tropical isomorphism

The polarized one-motive supplies a perfect rational pairing

$$
e_\lambda:X\times Y_{\mathbf Q}\longrightarrow\mathbf Q
\tag{2.8}
$$

such that

$$
e_\lambda(bx,y)=e_\lambda(x,b^*y).
\tag{2.9}
$$

It also supplies the tropical map

$$
\nu:Y\longrightarrow X_*(T),
\tag{2.10}
$$

injective with finite cokernel, and hence a rational isomorphism

$$
\nu:Y_{\mathbf Q}\xrightarrow{\sim}X.
\tag{2.11}
$$

Functoriality of valuation gives

$$
\nu(by)=b\nu(y).
\tag{2.12}
$$

Indeed, for a character $\chi$ and a period $y$, evaluating after $b_T$ is the same as evaluating the pulled-back character before $b_Y$; applying the valuation gives the commutative square defining (2.12).

Finally,

$$
q_\lambda(y,y')=e_\lambda(\nu y,y')
\tag{2.13}
$$

is symmetric and positive definite. At a catalog-good place the $p$-primary part of the polarization kernel is zero, so

$$
X_*(T)\otimes\mathbf Z_p
\quad\text{and}\quad
Y\otimes\mathbf Z_p
\tag{2.14}
$$

are mutually dual $\mathcal O_p$-lattices for (2.8). The tropical map need not be an integral isomorphism; its finite cokernel is monodromy data and is not discarded.

### 2.4 Geometric Tate realizations, including the residue prime

Book 40 states its Galois and inertia filtration for $\ell\ne p$. For the present comparison one also needs a purely geometric statement at $p$. It follows directly from the same finite-level one-motive construction and does not assert any residue-characteristic etaleness over $R$.

**Lemma 2.1 (geometric one-motive realization).** For every rational prime $\ell$, including $\ell=p$, after taking points over an algebraic closure of the characteristic-zero field $L$ there is an exact filtration

$$
0\subset W_{-2,\ell}\subset W_{-1,\ell}\subset T_\ell A
\tag{2.15}
$$

with graded pieces

$$
\begin{aligned}
\operatorname{Gr}_{-2}&=X\otimes\mathbf Q_\ell(1),\\
\operatorname{Gr}_{-1}&=V_\ell(A_0),\\
\operatorname{Gr}_{0}&=Y_{\mathbf Q}\otimes\mathbf Q_\ell
\end{aligned}
\tag{2.16}
$$

after tensoring with $\mathbf Q_\ell$. It is $D_\ell$-stable, $W_{-2}$ is isotropic, and $W_{-1}=W_{-2}^{\perp}$.

**Proof.** For every $n$, multiplication by $\ell^n$ on the semiabelian variety $\mathcal G$ is surjective on geometric points in characteristic zero. The finite-level description of one-motive torsion therefore gives

$$
0\longrightarrow\mathcal G[\ell^n]
\longrightarrow A[\ell^n]
\longrightarrow Y/\ell^nY\longrightarrow0.
\tag{2.17}
$$

Likewise,

$$
0\longrightarrow T[\ell^n]
\longrightarrow\mathcal G[\ell^n]
\longrightarrow A_0[\ell^n]\longrightarrow0.
\tag{2.18}
$$

Inverse limits are exact because the transition maps on all three torsion systems are surjective. A split torus has $T_\ell T=X_*(T)\otimes\mathbf Z_\ell(1)$ for every $\ell$ over a characteristic-zero algebraic closure. The Poincare pairing on one-motive torsion identifies the annihilators and gives the final assertion. Nothing in this proof claims that $p$-power torsion is etale over the valuation ring or that the $p$-adic inertia formula of Book 40 applies. $\square$

The generic $K_p$-orbit of the selected Shimura component identifies the rational filtration (2.15) with a filtration in $V\otimes\mathbf Q_p$. At $\ell\ne p$ the usual prime-to-residue-characteristic level does the same. Choosing compatible roots of unity identifies the Tate twist with the coefficient line; changing that choice rescales the entire pairing by one unit. Each resulting identification is one $D_\ell$-linear symplectic similitude, so its multiplier is common to every Morita packet.

## 3. The toric determinant bridge

Book 40 supplies the one-motive and tropical pairing, but it does not identify the toric determinant factor in the convention of Book 127. That identification is proved here from the derivative of uniformization and then checked against the positive toric Hodge block.

### 3.1 The action on the Lie algebra of the torus

For a split torus over a characteristic-zero field, differentiation of cocharacters gives a canonical isomorphism

$$
d_T:X_*(T)\otimes_{\mathbf Z}L\xrightarrow{\sim}\operatorname{Lie}(T),
\qquad
x\otimes a\longmapsto a\,dx(1).
\tag{3.1}
$$

It is independent of torus coordinates. If $b_T$ is an endomorphism, then

$$
d(b_T)\,dx(1)=d(b_T\circ x)(1),
\tag{3.2}
$$

so (3.1) is $D$-linear for the covariant action (2.4). Consequently

$$
\det(Z-b\mid\operatorname{Lie}T)
=\det(Z-b\mid X\otimes L).
\tag{3.3}
$$

Using (2.11), the right side is also the characteristic polynomial of $b$ on $Y_{\mathbf Q}\otimes L$. This is the first half of the determinant bridge.

### 3.2 The positive toric Hodge block

Define

$$
H_T=X\oplus Y_{\mathbf Q}
\tag{3.4}
$$

and

$$
\psi_T((x,y),(x',y'))
=e_\lambda(x,y')-e_\lambda(x',y).
\tag{3.5}
$$

Equations (2.9) and (2.12) make this a nondegenerate alternating $D$-adjoint form. On $H_{T,\mathbf R}$ put

$$
J_T(\nu z,y)=(-\nu y,z).
\tag{3.6}
$$

Then $J_T$ is $D$-linear, $J_T^2=-1$, and

$$
\psi_T((\nu z,y),J_T(\nu z,y))
=q_\lambda(z,z)+q_\lambda(y,y)>0
\tag{3.7}
$$

away from zero. Thus $(H_T,\psi_T,J_T)$ is a positive rational weight-one block.

With the homology convention of Book 127, $F^0$ is the $-i$ eigenspace and the Lie quotient is the $i$ eigenspace. Solving $J_Tu=iu$ gives

$$
H_T^i=\{(\nu z,-iz):z\in Y_{\mathbf C}\}.
\tag{3.8}
$$

Projection to the first coordinate identifies (3.8) $D_{\mathbf C}$-linearly with

$$
X_{\mathbf C}\xrightarrow{d_T}\operatorname{Lie}(T)_{\mathbf C}.
\tag{3.9}
$$

Thus the artificial-looking positive block has exactly the same determinant module as the actual toric Lie algebra.

### 3.3 Logarithmic de Rham and determinant factorization

The rigid quotient by the discrete lattice $Y$ has the same tangent space as its covering semiabelian variety. Hence

$$
\operatorname{Lie}(A)\simeq\operatorname{Lie}(\mathcal G).
\tag{3.10}
$$

Differentiating (1.2) gives the $D_L$-linear exact sequence

$$
0\longrightarrow\operatorname{Lie}(T)
\longrightarrow\operatorname{Lie}(A)
\longrightarrow\operatorname{Lie}(A_0)
\longrightarrow0.
\tag{3.11}
$$

This is also the Hodge quotient of the de Rham realization of the Raynaud one-motive: the lattice has zero Lie algebra, the semiabelian term contributes $\operatorname{Lie}(\mathcal G)$, and its weight filtration gives (3.11). Therefore, for the universal algebra element $b$,

$$
P_A(b;Z)=P_T(b;Z)P_0(b;Z),
\tag{3.12}
$$

where

$$
P_T(b;Z)=\det(Z-b\mid X\otimes L)
=\det(Z-b\mid Y_{\mathbf Q}\otimes L).
\tag{3.13}
$$

Since $P_A$ is the fixed Book 127 determinant law, (3.12) proves packetwise divisibility and identifies the quotient with the honest determinant polynomial of $\operatorname{Lie}(A_0)$. There is no inference from total toric rank and no possibility of a negative residual multiplicity.

After splitting

$$
D_{\mathbf C}=\prod_\tau M_{n_\tau}(\mathbf C),
\qquad
Y_{\mathbf C}=\bigoplus_\tau S_\tau\otimes M_\tau,
\tag{3.14}
$$

the toric packet is explicitly

$$
P^T_{b,\tau}(Z)
=\det(Z-b\mid S_\tau)^{\dim M_\tau}.
\tag{3.15}
$$

Equation (3.12) holds for each labeled factor, not merely after multiplying the labels together.

### 3.4 The opposite-Hodge convention and orientation

If one uses invariant differentials instead of the homological Lie quotient, then

$$
\operatorname{Lie}(T)^\vee\simeq X^*(T)\otimes L.
\tag{3.16}
$$

Character pullback is contravariant. Written as a left action compatible with the polarization dual, it is

$$
(b\cdot\varphi)(x)=\varphi(b^*x).
\tag{3.17}
$$

Thus the opposite convention replaces (3.13) by

$$
P_T^{\mathrm{opp}}(b;Z)
=\det(Z-b^*\mid Y_{\mathbf C}^\vee)
\tag{3.18}
$$

and sends the label $\tau$ to the involutive label $\tau^*$. One may change conventions, but one must change both the operator and the packet label. Formula (3.18) is why simply copying (3.15) into the opposite convention is wrong.

In an orthogonal packet, determinant multiplicities can leave two components. Give $H_T$ the ordered orientation determined by $X$, then $Y$, with the second identified with the first through $\nu$ and the positive form $q_\lambda$. The exact determinant-line identity from (3.11) defines the residual orientation by

$$
\operatorname{or}(A)
=\operatorname{or}(H_T)\operatorname{or}(A_0).
\tag{3.19}
$$

If the residual label is not the catalog label, the degeneration is already impossible. At the unique active real factor, (3.19) also retains the selected half-plane. At compact real factors it retains the definite orientation even though no tangent direction moves.

## 4. The global middle form

The earlier local-patching approach obscured the most useful geometric fact: the middle graded piece is the Tate realization of an actual polarized abelian variety $A_0$. That variety produces one rational form over $\mathbf Q$, so determinant, Hasse, and product compatibility are global from the outset.

### 4.1 The polarized abelian quotient

The polarization of the Raynaud one-motive respects weights. On the weight $-1$ quotient it induces a polarization

$$
\lambda_0:A_0\longrightarrow A_0^\vee.
\tag{4.1}
$$

The $D$-action on $A_0$ satisfies

$$
\lambda_0\iota_0(b)=\iota_0(b^*)^\vee\lambda_0.
\tag{4.2}
$$

Positivity is not inferred from symmetry: the ample line bundle in the polarized Raynaud datum restricts to the abelian quotient and gives (4.1). If the degree of $\lambda$ is prime to $p$, so is the degree of (4.1), because the degree formula factors into the abelian degree and squares of lattice indices.

### 4.2 Betti construction over a finitely generated field

The variety $A_0/L$, its polarization, and the finitely many endomorphisms defining the $\mathcal O$-action descend to a finitely generated characteristic-zero subfield $L_0\subset L$ containing the reflex field in the generic PEL datum. Choose an embedding

$$
\sigma:L_0\hookrightarrow\mathbf C.
\tag{4.3}
$$

whose restriction to the reflex field is the fixed complex embedding used to label the PEL determinant packets. Such an extension exists by choosing a transcendence basis and then an embedding of the finite algebraic remainder. This avoids any topological assertion about embedding the complete field $L$ into $\mathbf C$, and it prevents a silent permutation of the active label.

Define

$$
H_0=H_1(A_{0,\sigma}(\mathbf C),\mathbf Q).
\tag{4.4}
$$

The polarization (4.1) gives a nondegenerate alternating form $\psi_0$ on $H_0$, and (4.2) gives

$$
\psi_0(bu,v)=\psi_0(u,b^*v).
\tag{4.5}
$$

The complex structure of $A_{0,\sigma}(\mathbf C)$ is positive for $\psi_0$. Hence

$$
(H_0,\psi_0,J_0)
\tag{4.6}
$$

is an actual rational positive polarized $D$-module. Its Hodge quotient is $\operatorname{Lie}(A_{0,\sigma})$, so its determinant polynomial is exactly $P_0$ in (3.12).

### 4.3 Comparison with every finite realization

For a complex abelian variety $C=U/\Gamma$, one has

$$
C[\ell^n](\mathbf C)=\ell^{-n}\Gamma/\Gamma,
\qquad
T_\ell C=\Gamma\otimes\mathbf Z_\ell.
\tag{4.7}
$$

Finite torsion is unchanged after extension between algebraically closed characteristic-zero fields. More explicitly, choose one separable closure of $L_0$ and embeddings of it into algebraic closures on the complex and valued-field sides; the finite etale group schemes $A_0[\ell^n]$ then have the same geometric points, compatibly in $n$. Consequently (4.7), applied after the two base changes of $A_0$ from $L_0$, gives for every prime $\ell$

$$
H_0\otimes\mathbf Q_\ell\simeq V_\ell(A_0)
\tag{4.8}
$$

as $D_\ell$-modules with polarization pairing. The equality of Weil pairings follows by reducing the integral Riemann form modulo $\ell^n$; its commutator is the Poincare Weil pairing.

Now put

$$
(H,\psi_H)=(H_T,\psi_T)\perp(H_0,\psi_0).
\tag{4.9}
$$

Over $\mathbf Q_\ell$, a polarized splitting of (2.15) identifies its associated graded with (4.9). Here is the correction that makes a chosen $D_\ell$-linear section $s:Y_\ell\to V_\ell A$ isotropic. Put

$$
a(y,y')=\langle s(y),s(y')\rangle.
\tag{4.9a}
$$

The perfect outer pairing identifies $X_\ell$ with $Y_\ell^\vee$. Let $r:Y_\ell\to X_\ell$ be the $D_\ell$-linear map characterized by

$$
\langle r(y),s(y')\rangle=-\frac12a(y,y').
\tag{4.9b}
$$

Adjointness makes $r$ $D_\ell$-linear, and alternation gives

$$
\langle(s+r)y,(s+r)y'\rangle
=a(y,y')-\frac12a(y,y')+\frac12a(y',y)=0.
\tag{4.9c}
$$

The image of $s+r$ pairs perfectly with $W_{-2}$; its orthogonal complement supplies the middle summand. Division by $2$ is legitimate at every rational field $\mathbf Q_\ell$, including $\ell=2$. Thus

$$
(H,\psi_H)_{\mathbf Q_\ell}
\quad\text{is similar to}\quad
(V,\psi)_{\mathbf Q_\ell}
\tag{4.10}
$$

for every finite $\ell$. The multiplier in (4.10) is the single multiplier of the PEL level similarity; it is not chosen packet by packet.

At infinity, (3.12), (3.19), and positivity give the same result. The case-by-case verification is recorded in Section 5.5: alternating and exchange packets have one positive class, binary unitary packets are fixed by their ordered signature, orthogonal packets require signature plus orientation, a quaternionic Hermitian line is fixed by the positivity sign, and a rank-one unitary center packet is fixed by its retained sign component. Hence

$$
(H,\psi_H,J_T\oplus J_0)_{\mathbf R}
\quad\text{is in the selected oriented similarity class of}\quad
(V,\psi,h)_{\mathbf R}.
\tag{4.11}
$$

### 4.4 The global assembly theorem

**Theorem 4.1 (global polarized Raynaud assembly).** A hypothetical semistable degeneration of a catalog PEL point canonically supplies, up to the harmless choice (4.3), a rational polarized $D$-module

$$
H=X\oplus H_0\oplus Y_{\mathbf Q}
\tag{4.12}
$$

such that:

1. $H_0$ is the Betti homology of the polarized Raynaud abelian quotient;
2. its Hodge determinant is the exact quotient $P_A/P_T$ packet by packet;
3. all determinant, discriminant, Hasse, Brauer, signature, and orientation invariants are invariants of one global form;
4. at every finite place, including the residue prime, $H$ is locally similar to $V$ with one common packet multiplier; and
5. at infinity it lies in the selected positive oriented class.

**Proof.** Sections 4.1--4.2 construct $H_0$ and its global form. Equations (3.12) and (3.19) give determinant and orientation. Equations (4.7)--(4.10) give all finite comparisons, while the explicit real classification gives (4.11). Since $H_0$, $H_T$, and their forms are rational, every product formula is automatic. $\square$

This theorem proves existence of the middle form before any Hasse classification is invoked. The next chapter audits its invariants and proves that the classification used in the local comparisons is exactly the low-rank classification forced by PEL-exactness.

## 5. The exact polarized Morita packets

### 5.1 Reduction to classical packets

Decompose $D$ into simple $*$-orbits and apply Morita equivalence on each orbit. The alternating $\mathbf Q$-valued form becomes an $\varepsilon$-Hermitian form over the fixed center of that orbit. Over a separable closure, its connected derived isometry group is one of

$$
\operatorname{SL}_r,
\qquad
\operatorname{Sp}_{2r},
\qquad
\operatorname{SO}_r.
\tag{5.1}
$$

Because (1.4) has only absolute $A_1$ factors, a simple packet contributing a noncentral factor is one of:

1. an exchange or linear packet of reduced rank $2$;
2. an alternating packet of rank $2$;
3. a binary Hermitian packet for a quadratic center extension;
4. an orthogonal packet of rank $3$;
5. an orthogonal packet of rank $4$, whose derived group is of type $A_1\times A_1$; or
6. a quaternionic Hermitian line.

Here is the promised proof of exhaustiveness. For an exchange orbit, Morita reduction gives $\operatorname{GL}_r$ with derived group $\operatorname{SL}_r$, so $A_1$ forces $r=2$. For an involution of the second kind it gives $\operatorname{SU}_r$, again forcing $r=2$. For a first-kind packet it gives either $\operatorname{Sp}_{2r}$ or $\operatorname{SO}_r$. The root systems are $C_r$, $B_{(r-1)/2}$, or $D_{r/2}$; they are $A_1$ only for $\operatorname{Sp}_2$ and $\operatorname{SO}_3$, with the exceptional product

$$
\operatorname{Spin}_4\simeq\operatorname{SL}_2\times\operatorname{SL}_2.
\tag{5.1a}
$$

After a quaternion algebra is split, its Hermitian Morita category is one of these first-kind categories. The reduced rank-one Hermitian case descends $\operatorname{Sp}_2$ to $\operatorname{SL}_1(C)$ and hence gives the quaternionic line in the list. Rank-one field packets and orthogonal rank $2$ contribute only tori. This proves the list from the classical root systems and the exceptional rank coincidences; PEL-exactness is used only to say that no other derived root factor is allowed.

### 5.2 Invariants and scalar change

We fix conventions so that every later product formula is checkable.

For a binary Hermitian form over a quadratic etale algebra $K/k$ with involution $a\mapsto\bar a$, diagonalize it as

$$
h=\langle a_1,a_2\rangle,
\qquad a_i\in k^\times,
\tag{5.2}
$$

and define

$$
\det(h)=a_1a_2
\quad\text{in}\quad
k^\times/N_{K/k}K^\times.
\tag{5.3}
$$

After similarity by $a_1^{-1}$ it is $\langle1,-c\rangle$ with $c=-a_2/a_1$. Its special unitary group is the inner $A_1$ form represented by

$$
(K/k,c),
\tag{5.4}
$$

which splits exactly when $c$ is a norm. Multiplication of $h$ by $s\in k^\times$ changes its determinant by $s^2$, a norm from $K$, so (5.3) is a similarity invariant in rank two.

For a quadratic form

$$
q=\langle a_1,\ldots,a_n\rangle
\tag{5.5}
$$

over a local or global field of characteristic different from $2$, define

$$
d(q)=\prod_i a_i\quad\bmod k^{\times2},
\qquad
\epsilon(q)=\prod_{i<j}(a_i,a_j)_k.
\tag{5.6}
$$

Then

$$
\begin{aligned}
d(q\perp r)&=d(q)d(r),\\
\epsilon(q\perp r)&=\epsilon(q)\epsilon(r)(d(q),d(r))_k,
\end{aligned}
\tag{5.7}
$$

and

$$
\epsilon(sq)
=\epsilon(q)(s,s)_k^{n(n-1)/2}(s,d(q))_k^{n-1}.
\tag{5.8}
$$

Formula (5.8) follows by expanding every pair $(sa_i,sa_j)$ and counting each $a_i$ exactly $n-1$ times.

For $n=3$, the even Clifford algebra is

$$
C^+(q)=(-a_1a_2,-a_1a_3)_k.
\tag{5.9}
$$

For $n=4$, its center is the discriminant etale algebra $k(\sqrt{d(q)})$ and $C^+(q)$ is a quaternion algebra over that center; when the center splits, it is a pair of quaternion algebras. The packet retains the canonical Clifford involution and the orientation of the center. The oriented algebra with involution, together with $d(q)$ and the real signature, is equivalent to the Hasse data in (5.6). Retaining only the Brauer class would lose the descent form.

A quaternionic Hermitian line over $(C,\bar{\ })$ has the form

$$
h_a(x,y)=\bar xay,
\qquad a\in k^\times.
\tag{5.10}
$$

Similarity kills $a$. Its similitude group is $C^\times$, its multiplier is reduced norm, and its adjoint group is $\operatorname{PGL}_1(C)$. At a ramified real place, positivity fixes the sign of $a$.

The derived-trivial packets used by a central refinement must also retain their labels. An exchange pair $P\oplus P^\vee$ has only its rank and the ordering of its two idempotents. A rank-one Hermitian packet over a quadratic etale algebra $K/k$ is $\langle a\rangle$ with isometry label

$$
[a]\in k^\times/N_{K/k}K^\times.
\tag{5.10a}
$$

It has no noncentral derived group, but (5.10a) cannot be discarded: a similarity with the common multiplier $c$ exists exactly when $[a']=[ca]$. At a real nonsplit place its sign is the component label. Thus a central packet contributes a norm and component equation, even though it contributes no Hasse invariant.

An orientation is a trivialization of the relevant determinant line or, equivalently, a choice of connected component when the orthogonal flag space has two. It is additional to (5.3) and (5.6).

### 5.3 Local classification in the ranks that occur

**Proposition 5.1 (local packet classification).** Over a local field of characteristic zero:

1. alternating planes and exchange hyperbolic packets are classified by reduced rank;
2. binary Hermitian forms are classified up to similarity by (5.3), and over $\mathbf R$ also by ordered signature;
3. quadratic forms of ranks $3$ and $4$ are classified by rank, $d(q)$, $\epsilon(q)$, and real signature;
4. a quaternionic Hermitian line has one similarity class at a finite place and one positivity-compatible class at a real place;
5. a rank-one unitary center packet is classified isometrically by (5.10a), with common-multiplier similarities satisfying $[a']=[ca]$; and
6. an oriented similarity additionally requires equality of the orientation label after applying the scalar-change formulas.

**Proof.** An alternating plane has a symplectic basis. An exchange packet is a module paired perfectly with its dual, hence is hyperbolic and has no further form invariant.

For a Hermitian plane, choose a vector of nonzero norm and diagonalize. Similarity makes the first coefficient $1$, so the form is $\langle1,-c\rangle$. Replacing the second basis vector multiplies $c$ by a norm, and conversely a norm change gives a basis change. This proves (5.3)--(5.4). Over $\mathbf R$, Sylvester diagonalization retains the ordered signature.

For quadratic forms, diagonalization reduces an isometry to the square classes of the coefficients. Successive use of

$$
\langle a,b\rangle\simeq
\langle a+b,ab/(a+b)\rangle
\tag{5.11}
$$

when $a+b\ne0$ changes the coefficients without changing (5.6). Hilbert-symbol bilinearity shows that rank, determinant, and Hasse symbol are unchanged and permits reduction to a fixed list of square-class representatives. In ranks $3$ and $4$ that list has one representative for each pair $(d,\epsilon)$. At a dyadic field the same proof uses the full dyadic Hilbert symbol, not an odd-residue formula. Real diagonalization gives the signature.

For (5.10), scaling the form removes $a$ and reduced norm gives the multiplier. For (5.10a), a basis change multiplies $a$ by $z\bar z$, and scaling the form multiplies it by the prescribed $c$; this proves clause 5. Orientation is invisible to these diagonal invariants and must be retained separately. $\square$

### 5.4 Global existence and product compatibility

The low ranks allow a direct global proof; no classification of arbitrary quaternionic skew-Hermitian forms is being imported.

**Proposition 5.2 (global packet theorem).** Let $k$ be a number field. A coherent family of local catalog packets is the localization of a global packet precisely when:

1. ranks and global determinant or discriminant classes agree;
2. binary unitary determinant ratios and rank-one unitary center coefficients obey the quadratic norm reciprocity condition;
3. orthogonal Hasse symbols obey the Hilbert product formula;
4. Clifford quaternion invariants have total Brauer invariant zero and, in rank $4$, satisfy the split-corestriction descent relation over the discriminant etale algebra; and
5. the real signatures and orientations have the stated ranks and determinant signs.

The resulting global packet is unique up to the corresponding isometry or similarity relation.

**Proof.** Alternating and exchange packets have no obstruction. For a binary unitary packet, write the desired similarity form as $\langle1,-c\rangle$. Equality at every completion says that the ratio of two possible values of $c$ is a local norm everywhere. The cyclic quadratic Hasse norm theorem makes it a global norm, proving both existence and uniqueness. The same argument in rank one globalizes the coefficient class (5.10a) and, after a common multiplier has been fixed, the equation $[a']=[ca]$.

For a ternary quadratic packet, (5.9) turns the local Hasse data into local quaternion invariants. The product condition gives a global quaternion algebra by the Brauer invariant sequence. This reversal is explicit. If the desired determinant is $d$ and the quaternion is $(u,v)_k$, take

$$
q=\left\langle\frac{uv}{d},-\frac d v,-\frac d u\right\rangle.
\tag{5.11a}
$$

Its determinant is $d$ and (5.9) gives $(u,v)_k$. Book 87's local--global quaternion classification then gives uniqueness.

For rank $4$, put $K=k(\sqrt d)$ for the prescribed discriminant algebra. The even Clifford algebra of an oriented four-space is a quaternion algebra $C/K$ with its descent involution and

$$
\operatorname{Cor}_{K/k}[C]=0.
\tag{5.11b}
$$

This is seen after splitting the quadratic form: the two half-spin factors are opposite, so their transferred Brauer classes cancel. Conversely, the local invariants and the displayed corestriction relation give a global $C/K$ by the Brauer sequence. A splitting of the corestriction is equivalently a $k$-semilinear unitary involution $\sigma$ on $C$ inducing the nontrivial automorphism of $K/k$. Locally prescribed involutions differ from one choice of $\sigma$ by inner conjugation. To compute the ambiguity, split $C$ and write such an involution as the adjoint of a binary Hermitian matrix. Hermitian diagonalization shows that an inner twist with fixed orientation is measured by its determinant in $k^\times/N_{K/k}K^\times$; the calculation descends because both the inner-conjugacy action and reduced determinant do. The quadratic Hasse norm theorem therefore makes a locally compatible twisting parameter global.

The four-dimensional form is now explicit:

$$
W=C^\sigma,
\qquad
q_W(x)=\operatorname{Nrd}_{C/K}(x)\in k.
\tag{5.11c}
$$

The fixed subspace has dimension $4$ over $k$. Nondegeneracy, discriminant algebra $K$, and the identification of its oriented even Clifford algebra with $(C,\sigma)$ can be checked after a separable splitting: $C$ becomes two matrix algebras exchanged by $\sigma$, $W$ becomes one $M_2$, and (5.11c) becomes the determinant form. These properties descend. Rescaling fixes a representative of the determinant without changing its square class or similarity class. If $K=k\times k$, the construction says that the two quaternion components have the same order-two class and the orientation orders them. Conversely, the Clifford generators recover (5.11c), proving uniqueness. Thus the corestriction and involution relation, not merely a total parity count over $K$, is the exact descent condition.

Quaternionic Hermitian lines have no finite similarity invariant; the global reduced-norm theorem leaves only the stated signs at ramified real places. Those signs are exactly the positivity conditions. Finally, weak approximation chooses diagonal coefficients with the prescribed real signatures, while orientation is an independent global determinant-line label. $\square$

For the forms in Theorem 4.1, the compatibility conditions do not need to be guessed. For example, if $H=H_T\perp H_0$, then (5.7) gives at every orthogonal place

$$
\epsilon(H)=\epsilon(H_T)\epsilon(H_0)
(d(H_T),d(H_0)),
\tag{5.12}
$$

Equivalently, the middle invariants are

$$
\begin{aligned}
d(H_0)&=d(H)d(H_T)^{-1},\\
\epsilon(H_0)&=\epsilon(H)\epsilon(H_T)
\bigl(d(H_T),d(H_0)\bigr),
\end{aligned}
\tag{5.12a}
$$

where signs are their own inverses. In a unitary packet,

$$
\det(H_0)=\det(H)\det(H_T)^{-1}
\quad\text{in }k^\times/N_{K/k}K^\times,
\tag{5.12b}
$$

and the quaternionic line has only its Brauer class and positivity sign. Orientation always satisfies

$$
\operatorname{or}(H_0)
=\operatorname{or}(H)\operatorname{or}(H_T)^{-1}.
\tag{5.12c}
$$

Taking the product over all places in (5.12a) gives $1$ because each entry is global. The corresponding sums of Clifford Brauer invariants vanish. The unit determinant classes in (5.12b) are global, so their local norm residues obey reciprocity. This proves the product compatibility demanded of the middle form without a missing-place sign argument.

### 5.5 Real signatures and common multipliers

At a real unitary packet, (3.8) gives the toric ordered signature and (4.6) gives the middle signature. Their sum is the determinant multiplicity in (3.12). A negative residual entry cannot occur because $H_0$ is an actual abelian Hodge structure. Binary Hermitian classification therefore identifies the result with the fixed packet.

At a real orthogonal packet, the same argument adds ordinary signatures. Equation (3.19) fixes the orientation not detected by the signature. A toric hyperbolic plane has signature $(1,1)$; it cannot occur inside a definite compact packet. Thus a proposed degeneration can already fail at a compact real factor.

An alternating or exchange packet has one positive class, and a quaternionic Hermitian line has no room for a nonzero outer hyperbolic pair. A rank-one unitary center packet retains its real sign, so its comparison is the common-multiplier equation $[a']=[ca]$ rather than an empty derived-group condition. These are direct calculations, not consequences of the phrase PEL-exact.

Finally, the multipliers are common. At a finite place, (4.10) comes from one level similarity. At infinity, each packet comparison can be chosen as an isometry; hence all have multiplier $1$. At the integral place, Chapter 6 constructs every hyperbolic pair with the same prescribed unit multiplier by rescaling its dual basis vector. No step chooses unrelated packet scalars.

Concretely, if the common local multiplier is $c_w$ and a packet has rank $n$, then

$$
\det(V_w)=c_w^n\det(H_w),
\qquad
\epsilon(V_w)=\epsilon(c_wH_w),
\tag{5.13}
$$

with the second term expanded by (5.8); the orientation is transported by the same similarity. In a unitary packet the determinant equality is read modulo norms. These simultaneous equations, rather than independent similarity quotients for each row, define the local point of the bitorsor in Chapter 8.

## 6. Odd self-dual packet lattices

Rational similarity alone does not identify hyperspecial integral data. This chapter proves exactly the self-dual lattice statement used at a catalog-good place. The proof treats each low-rank packet and does not extrapolate a symplectic Gram--Schmidt argument to arbitrary orthogonal or quaternionic lattices.

### 6.1 The standard integral packets

Let $\mathcal R$ be a complete unramified discrete valuation ring of odd residue characteristic, with fraction field $K$ and residue field $k$. The standard packets are:

$$
J_r=
\begin{pmatrix}0&I_r\\-I_r&0\end{pmatrix}
\tag{6.1}
$$

for alternating forms,

$$
H_r=
\begin{pmatrix}0&I_r\\I_r&0\end{pmatrix}
\tag{6.2}
$$

for symmetric or Hermitian hyperbolic forms, and

$$
P\oplus P^\vee
\tag{6.3}
$$

with evaluation pairing for an exchange packet. Orthogonal rank $3$ is $H_1\perp\langle u\rangle$; quasi-split rank $4$ is $H_2$ when its discriminant is square and $H_1\perp\langle1,-u\rangle$ for the prescribed nonsquare discriminant. Here $u\in\mathcal R^\times$ represents the required unit square class.

### 6.2 Alternating, exchange, and unitary packets

**Lemma 6.1.** Every self-dual alternating lattice over $\mathcal R$ has a symplectic basis. Every self-dual exchange lattice is (6.3). Every self-dual lattice for an unramified quadratic Hermitian packet is determined by its rank and determinant label and contains the maximal number of hyperbolic planes allowed by its rational Witt index.

**Proof.** In the alternating case, a primitive vector $e$ defines a primitive functional because the lattice is self-dual. Choose $f$ with $\langle e,f\rangle=1$. The span of $e,f$ is a unimodular direct summand with matrix $J_1$; its orthogonal complement is self-dual. Induction proves the first assertion.

For an exchange involution, the two central idempotents decompose the lattice as $P\oplus Q$. Adjointness makes both summands isotropic and gives a perfect pairing $P\times Q\to\mathcal R$. Hence $Q=P^\vee$ and the packet is (6.3).

For an unramified quadratic extension $\mathcal S/\mathcal R$, reduction of a unimodular Hermitian lattice is nondegenerate. The norm map $k_{\mathcal S}^\times\to k^\times$ is surjective. Hensel lifting makes the norm map $\mathcal S^\times\to\mathcal R^\times$ surjective: solve the residue norm first and then solve each principal-unit equation, whose linearized trace is onto in the unramified extension. A primitive vector of unit norm can therefore be scaled to norm $1$ and split off. If the reduction is isotropic, lift a primitive isotropic vector by Hensel's lemma; the gradient is nonzero because the form is unimodular. Choose a partner of pairing $1$ and subtract half its norm times the first vector to obtain an isotropic partner. This splits $H_1$ integrally. Induction proves the claimed normal form and uniqueness. $\square$

If the quadratic etale algebra is split, its two idempotents turn the Hermitian lattice into two summands paired perfectly with one another; it is therefore the evaluation packet (6.3), and in binary rank it is again $H_1$. Thus Lemma 6.1 covers both unramified possibilities used in Section 7.5.

### 6.3 Orthogonal and quaternionic packets

**Lemma 6.2.** Let $L$ be an odd unimodular quadratic lattice of catalog rank $3$ or $4$.

1. It is integrally diagonalizable by units.
2. Its integral isometry class is determined by rank, unit determinant square class, rational Hasse invariant, and orientation.
3. If its rational group is quasi-split, the standard hyperbolic plane in (6.2) splits integrally.

**Proof.** Because the reduction is nondegenerate and $2$ is invertible, some primitive vector has unit norm. Its orthogonal projection

$$
x\longmapsto x-\frac{(x,v)}{(v,v)}v
\tag{6.4}
$$

is integral and splits a unimodular line. Induction diagonalizes $L$ by units. This is not the whole classification: one must still compare the unit coefficients.

Over the finite residue field, nondegenerate quadratic forms are classified by dimension and determinant. An isometry modulo the maximal ideal lifts successively. If $g_m$ is an isometry modulo $\pi^m$, write $g_m^{\mathsf t}Qg_m=Q+\pi^mE$. Replacing $g_m$ by $g_m(1+\pi^mX)$ changes the error modulo $\pi^{m+1}$ by $X^{\mathsf t}Q+QX$. Since $2$ and $Q$ are invertible, $X=-(1/2)Q^{-1}E$ solves the correction. Completeness gives an integral isometry. The rational Hasse invariant records the rational packet, while the orientation separates the two special-orthogonal choices.

If the rational packet is quasi-split, its reduction has the required isotropic vector in ranks $3$ and $4$. Lift it by Hensel's lemma, choose a partner of pairing one, and correct that partner to be isotropic as in Lemma 6.1. The resulting Gram matrix is $H_1$, its span is unimodular, and the orthogonal complement is self-dual. $\square$

For a split quaternion algebra $A=M_2(K)$ with maximal order $\mathcal A=M_2(\mathcal R)$, put $e=e_{11}$. The two progenerators $\mathcal Ae$ and $e\mathcal A$ are trace-dual, and the matrix-unit identities give mutually inverse maps

$$
\mathcal Ae\otimes_{\mathcal R}eL\longrightarrow L,
\qquad
e(\mathcal Ae\otimes_{\mathcal R}M)\longrightarrow M
\tag{6.4a}
$$

for every projective left $\mathcal A$-lattice $L$ and every $\mathcal R$-lattice $M$. Equip $eL$ with the Morita-reduced form obtained by contracting the $\mathcal A$-valued adjoint form against the standard symplectic matrix. If $L^\#$ denotes the original dual, trace-duality of the two progenerators gives a natural isomorphism

$$
e(L^\#)\xrightarrow{\sim}(eL)^\#.
\tag{6.4b}
$$

Thus self-duality is preserved in both directions, not merely rationally. For a quaternionic Hermitian line with split adjoint $A_1$, the induced form on $eL$ is alternating of rank $2$. Lemma 6.1 gives a basis with matrix $J_1$; the inverse functor in (6.4a) reconstructs the unique standard maximal-order lattice. Its unit multipliers are determinants in $\operatorname{GL}_2(\mathcal R)$ and hence all of $\mathcal R^\times$.

If an acting algebra is $M_m(\mathcal O_C)$ for an unramified maximal order $\mathcal O_C$, the same matrix-unit proof removes only the matrix factor and leaves an $\mathcal O_C$-packet. Heredity makes its torsion-free lattices projective and gives the analogue of (6.4b). In the quaternionic-line row the catalog-good quasi-split adjoint hypothesis then forces $C$ to split, reducing to the preceding calculation. No division algebra is silently Morita-equated with $K$, and no quaternionic Gram--Schmidt assertion is used.

### 6.4 Morita transfer, orientation, and one common multiplier

**Theorem 6.3 (odd catalog lattice theorem).** At a catalog-good place, the associated graded lattice of the Raynaud filtration and the fixed PEL lattice have the same standard packet genus. More precisely:

1. the outer lattice

   $$
   \Lambda_T=(X_*(T)\otimes\mathbf Z_p)
   \oplus(Y\otimes\mathbf Z_p)
   \tag{6.5}
   $$

   is a self-dual hyperbolic $\mathcal O_p$-packet;
2. each exchange, alternating, unitary, orthogonal, and quaternionic packet is one of the normal forms of Sections 6.1--6.3;
3. the admissible outer reduced rank is at most the Witt rank of the fixed packet;
4. the outer packet splits as an integral orthogonal direct summand, with self-dual complement;
5. the quotient orientation is the fixed orientation divided by the ordered orientation of (6.5); and
6. for any common allowed unit multiplier $c_p$, all packet embeddings can be chosen with multiplier $c_p$.

**Proof.** Perfectness of (2.8) over $\mathbf Z_p$ gives clause 1. The middle lattice $T_pA_0$ is self-dual because $\deg\lambda_0$ is a unit. The selected generic $K_p$-orbit identifies $T_pA$ with the genus of $\Lambda_p$. Since the unramified maximal order is hereditary, the two exact sequences of Lemma 2.1 split as $\mathcal O_p$-modules. Applying the alternating correction (4.9a)--(4.9c) integrally is legitimate because $2$ is a unit. Thus the self-dual associated graded is an integral polarized packet in the fixed genus.

The order hypotheses and Lemmas 6.1--6.2 give clause 2, while integral Morita equivalence gives the matrix and quaternionic cases. The generic $p$-adic filtration embeds the rational outer packet in $V_p$, so its reduced rank cannot exceed the rational Witt rank. Quasi-splitness and the explicit lifted Witt bases split exactly that number of hyperbolic planes. A unimodular summand has self-dual orthogonal complement, proving clauses 3--4.

The ordering $X$ before $Y$ fixes the outer orientation. In positive complement rank, a reflection in a unit vector changes the total orientation without changing the form, so the required quotient orientation can be imposed. In rank two, the two ordered isotropic lines are the two possible labels; equality with the catalog label is a separate component condition and a mismatch is a contradiction.

Finally, replace every dual basis vector $f_i$ by $c_pf_i$. This scales each hyperbolic pairing by the same $c_p$ and preserves integrality because $c_p$ is a unit. There is no hidden packetwise freedom. In an alternating or exchange packet every unit occurs. In an unramified binary unitary packet, multiplication of the determinant by $c_p^2$ is a norm, so every unit again occurs. For a rank-one unitary center packet, the exact equation is $[a']=[c_pa]$ from (5.10a), and surjectivity of the unramified unit norm solves it. In orthogonal rank $4$, (5.8) and the fact that Hilbert symbols of two units are trivial at an odd unramified place leave the packet invariants unchanged. In orthogonal rank $3$, the determinant forces $c_p$ to be a square in the similarity image; Hensel lifting then supplies its integral square root. In a split quaternionic line, reduced norm is surjective on units. These are exactly the multiplier images recorded by the catalog component. The complementary standard packet can therefore be chosen with the same $c_p$, proving clause 6. $\square$

This theorem derives the standard packets from oddness, unramified maximal orders, self-duality, quasi-splitness, and the recorded labels. It does not use a local model.

### 6.5 The dyadic boundary

At a dyadic place, alternating lattices still have symplectic bases, but orthogonal and ramified unitary packets have integral invariants invisible in the rational form. Norm ideals, even or odd parity, Jordan constituents, and oddity or Arf-type labels can differ while rank, determinant, rational Hasse invariant, and orientation agree.

**Proposition 6.4 (exact dyadic replacement).** The rational boundary theorem remains valid at $p=2$ if the Raynaud associated graded and the fixed lattice are separately known to have the same complete oriented self-dual genus in every packet, with one common multiplier. No dyadic integral comparison follows from the hypotheses of Definition 1.1 with the word odd removed.

Thus dyadic places stay outside the catalog-good theorem unless this stronger datum is supplied.

## 7. Catalog-by-catalog audit

The purpose of this chapter is to prevent presentation-independence from becoming presentation-ignorance. For each operation named in the catalog we compute the algebra with involution, reduced rank, multiplier, form invariants, orientation, and good lattice.

### 7.1 Direct quaternion trace presentation

Let $B/F$ be quaternionic and choose an invertible pure element $\delta$, so $\bar\delta=-\delta$. On the $\mathbf Q$-space $V=B$, take the left $D=B$ action and

$$
\psi_\delta(x,y)
=\operatorname{Tr}_{F/\mathbf Q}
\operatorname{Trd}_B(x\bar y\delta).
\tag{7.1}
$$

Then

$$
b^*=\delta^{-1}\bar b\delta.
\tag{7.2}
$$

Indeed, cyclicity of reduced trace moves $b$ to the right, and purity of $\delta$ gives (7.2). The commutant is right multiplication by $B^{\mathrm{op}}$. Its adjoint involution is canonical conjugation. Whenever $\operatorname{Nrd}(c)$ is a rational scalar,

$$
\psi_\delta(xc,yc)
=\operatorname{Nrd}(c)\psi_\delta(x,y).
\tag{7.3}
$$

Thus, for $c$ whose reduced norm is a rational scalar, the similitude group is the common-norm group

$$
\{c\in\operatorname{Res}_{F/\mathbf Q}B^\times:
\operatorname{Nrd}(c)\in\mathbf G_m\},
\tag{7.4}
$$

provided the chosen Hodge map lifts and (7.2) is positive. Both qualifications are part of admission.

The $\mathbf Q$-rank of $V$ is $4[F:\mathbf Q]$, so the abelian dimension is $2[F:\mathbf Q]$. After complex splitting, the Hodge quotient contains one copy of the standard two-dimensional simple module at every center label; hence

$$
P_b(Z)=\prod_\tau\det(Z-b\mid S_\tau).
\tag{7.5}
$$

The Morita form on the commutant is a quaternionic Hermitian line. Its only finite similarity invariant is the Brauer class $[B]$; its real sign and active orientation are fixed by positivity. A nonzero outer block has even reduced rank, so it cannot fit in this reduced rank-one packet. This recovers the familiar direct rank obstruction as a special case, but the later proof does not depend on it.

At an odd good place, the adjoint quaternion is split and the maximal-order self-dual lattice is integrally Morita equivalent to the standard symplectic plane. The codifferent and the valuation of $\delta$ are already absorbed in the assumption that the chosen lattice for (7.1) is self-dual; rational invertibility of $\delta$ alone would not imply this.

### 7.2 Matrix Morita presentations

For $m\ge1$, put

$$
D_m=M_m(D),
\qquad
(a_{ij})^{*_m}=(a_{ji}^*),
\qquad
V_m=V^m,
\qquad
\psi_m=\psi\perp\cdots\perp\psi.
\tag{7.6}
$$

The column progenerator gives

$$
\operatorname{End}_{D_m}(V_m)\simeq\operatorname{End}_D(V),
\tag{7.7}
$$

with the same adjoint involution. Hence the similitude group, adjoint quaternion, multiplier character, reduced packet ranks, determinant classes, Hasse invariants, and orientations are unchanged. Ordinary vector-space ranks are multiplied by $m$, but reduced Morita ranks are not.

The Hodge determinant is the determinant of the universal $M_m(D)$ element on the corresponding Morita simple module; applying a full idempotent recovers (7.5). The integral lattice is $\Lambda^m$. Its dual is $(\Lambda^\#)^m$, so self-duality is preserved. The integral column and row progenerators in Chapter 6 show that no new lattice genus appears.

### 7.3 The split-corestriction admission test

Let $L/K$ have degree $r$, let $B/L$ be quaternionic, and suppose

$$
\operatorname{Cor}_{L/K}(B)\simeq\operatorname{End}_K(W),
\qquad \dim_KW=2^r.
\tag{7.8}
$$

Over a separable closure,

$$
W=\bigotimes_{\tau:L\hookrightarrow K^s}S_\tau.
\tag{7.9}
$$

The tensor form $q$ has symmetry $(-1)^r$, multiplier

$$
\nu_T((g_\tau))=\prod_\tau\det(g_\tau),
\tag{7.10}
$$

on the independently varying product. On a common-determinant source with $\det(g_\tau)=\nu$ this restricts to $\nu^r$; the admitted central modification records which of these characters is the rational PEL multiplier. The finite central kernel of the **derived** tensor action is

$$
\{(\varepsilon_\tau)\in\{\pm1\}^r:
\prod_\tau\varepsilon_\tau=1\}.
\tag{7.11}
$$

inside $\prod_\tau\operatorname{SL}_2$. A full similitude source can also have a positive-dimensional scalar kernel, for example scalar tuples with product one. That kernel must be divided out by the stated connected central modification, not confused with (7.11). Both the resulting multiplier character and its image are retained in the admission data.

Kernel removal is necessary but not sufficient for PEL-exactness. Since the tensor representation is absolutely irreducible, its associative commutant is scalar. If $r$ is odd, imposing only that commutant and the alternating form gives the full group $\operatorname{Sp}_{2^r}$; if $r$ is even, it gives $\operatorname{SO}_{2^r}$. Equality with the tensor image can occur only for

$$
r=1
\quad\text{or}\quad
r=2,
\tag{7.12}
$$

because

$$
\operatorname{Sp}_2=\operatorname{SL}_2,
\qquad
\operatorname{Spin}_4=\operatorname{SL}_2\times\operatorname{SL}_2,
\tag{7.13}
$$

whereas for $r\ge3$ the classical group has dimension strictly larger than $3r$ and a different root system. Thus a higher tensor block is not admitted by Book 127 without additional non-PEL tensors.

The $r=1$ row is the ordinary rank-two packet. The $r=2$ row is an orthogonal rank-four input. Its invariants are $d(q)$, $\epsilon(q)$, the quaternion algebra $C^+(q)$ over the discriminant center, and the Clifford orientation. Its multiplier is (7.10). Because $q$ is symmetric, an alternating candidate requires the hyperbolic construction audited in Section 7.4; that bare construction fails the positivity test and is not a PEL presentation. At a good odd place an integral splitting of (7.8) nevertheless carries the tensor of two self-dual symplectic planes to a self-dual unimodular quadratic lattice; Lemma 6.2 gives its standard genus.

For the fixed one-split-real-place datum there is a sharper conclusion. Apply corestriction from the field carrying all quaternionic factors to the final ground field. At the real place below the unique active embedding, exactly $r-1$ branches are Hamiltonian. The corestriction invariant there is

$$
\frac{r-1}{2}\quad\text{in }\mathbf Q/\mathbf Z.
\tag{7.13a}
$$

If $r$ is even, this is $1/2$, so (7.8) is impossible. If $r$ is odd and at least $3$, the corestriction may split, but the stabilizer calculation above shows that the tensor image is not PEL-exact. Hence only $r=1$ survives for the quaternionic curve treated in this book. The rank-four row remains in the table because it is the exact exceptional calculation needed to audit the general catalog language; it is not a nontrivial presentation of the present one-active-factor curve.

### 7.4 The hyperbolic admission test

For an orthogonal tensor block $(W,q)$, the hyperbolic representation is

$$
H(W)=W\oplus W^\vee,
\qquad
\Psi((x,f),(y,g))=g(x)-f(y).
\tag{7.14}
$$

Using $q:W\simeq W^\vee$, choose a symplectic plane $(U,\varepsilon)$ and identify

$$
H(W)\simeq W\otimes U,
\qquad
\Psi=q\otimes\varepsilon.
\tag{7.15}
$$

Let

$$
D_H=\operatorname{End}(U),
\tag{7.16}
$$

with the symplectic adjoint. Then

$$
\widetilde{\operatorname{GSim}}_{D_H}(W\otimes U,q\otimes\varepsilon)
=\operatorname{GO}(W,q),
\qquad
\operatorname{GSim}_{D_H}(W\otimes U,q\otimes\varepsilon)^\circ
=\operatorname{GSO}(W,q).
\tag{7.17}
$$

The tilde denotes the possibly disconnected full linear stabilizer; Book 127 takes the identity component. This is the exact **rational stabilizer** calculation, but it is not yet a PEL admission. The involution on $D_H=M_2(K)$ is the symplectic adjoint. At a real split place it is not positive: for

$$
a=\begin{pmatrix}1&0\\0&-1\end{pmatrix}
$$

one has $a^*=-a$ and $\operatorname{Tr}(aa^*)=-2$. Thus the bare hyperbolic construction (7.15)--(7.17) does not satisfy Definition 1.1 of Book 127. An alternative hyperbolic presentation would have to exhibit a different positive algebra with involution and repeat the full commutant calculation; parity repair alone supplies neither fact.

For $\dim W=4$, the connected derived group in (7.17) is indeed a two-factor $A_1$ group, and its reduced rational packet is the orthogonal rank-four packet of Section 7.3. The ordinary symplectic dimension doubles, while determinant, Hasse, Clifford, and orientation data are unchanged after rational Morita reduction. This explains the exceptional stabilizer coincidence, but it does not promote the construction to a catalog PEL row. Independently, formula (7.13a) shows that the underlying split-corestriction input cannot occur for the fixed one-active-factor curve.

The determinant law of this rejected candidate can also be read without coordinates. The simple left $D_H$-module is $U$, while $V=W\otimes U$ has multiplicity $4$. A putative weight-one Hodge quotient would have half that multiplicity, so for $a\in D_H$ its packet polynomial would be

$$
P_a(Z)=\det(Z-a\mid U)^2.
\tag{7.17a}
$$

The orthogonal signature and Clifford orientation would select the Hodge component not distinguished by (7.17a). This calculation records what the candidate would require; it does not repair the failed positivity test.

For $\dim W>4$, (7.17) is also a larger orthogonal group, so the candidate fails the commutant test in addition to the positivity test. This is the promised admission audit.

If $L_W$ and $L_U$ are self-dual, then $L_W\otimes L_U$ is self-dual for (7.15). In the presentation (7.14), the standard lattice is $L_W\oplus L_W^\vee$. Its ordered orientation is the $W$-then-$W^\vee$ orientation, and a unit multiplier rescales only the dual side.

### 7.5 The binary-unitary replacement

The positive realization needed at mixed real ramification is not merely another coordinate system on the quaternionic-line packet. It has a different acting algebra and a larger center. We now construct it from the quaternion algebra and verify every invariant used by the boundary proof.

Choose a CM quadratic extension $K/F$ embedded in $B$. Such an extension always exists: prescribe a nonsquare quadratic algebra at every finite ramified place of $B$, prescribe $\mathbf C$ at every real place, and use weak approximation to choose one global square class. The local embedding criterion then embeds the resulting field in $B$. Write its conjugation as $a\mapsto\bar a$. Skolem--Noether supplies $j\in B^\times$ and $\beta\in F^\times$ such that

$$
B=K\oplus Kj,
\qquad
ja=\bar a j,
\qquad
j^2=\beta.
\tag{7.18}
$$

Thus $B$ is the cyclic quaternion algebra $(K/F,\beta)$. Regard $V_U=B$ as the faithful left $K$-module $K\oplus Kj$ and let $\operatorname{pr}_K:B\to K$ be projection along $Kj$. The formula

$$
\mathcal H(x,y)=\operatorname{pr}_K(x\bar y)
\tag{7.19}
$$

is Hermitian, linear in the first variable. In the basis $1,j$ it is

$$
\mathcal H(a+bj,c+dj)=a\bar c-\beta b\bar d,
\qquad
\mathcal H\simeq\langle1,-\beta\rangle.
\tag{7.20}
$$

Choose $\delta\in K^\times$ with $\bar\delta=-\delta$ and put

$$
D_U=K,
\qquad
a^*=\bar a,
\qquad
\psi_U(x,y)=\operatorname{Tr}_{K/\mathbf Q}
\bigl(\delta\mathcal H(x,y)\bigr).
\tag{7.21}
$$

The involution on $D_U$ is positive because
$\operatorname{Tr}_{K/\mathbf Q}(a\bar a)>0$ for $a\ne0$. Hermitian symmetry and $\bar\delta=-\delta$ make $\psi_U$ alternating, and the trace pairing plus nondegeneracy of $\mathcal H$ makes it nondegenerate. Moreover

$$
\psi_U(ax,y)=\psi_U(x,\bar a\,y),
\tag{7.22}
$$

so (7.21) is a rational PEL algebra, module, positive involution, and adjoint alternating form.
Moreover $\operatorname{Trd}_B(z\delta)=\operatorname{Tr}_{K/F}(\delta\operatorname{pr}_K z)$, so $\psi_U$ is literally the direct trace form (7.1) for the pure element $\delta\in K$. The involution (7.2) restricts to conjugation on $K$. What changes is the prescribed acting algebra—from $B$ to $K$—and hence the exact commutant and its center, not the underlying rational symplectic space.

The exact stabilizer can be recovered from $\psi_U$; it is not being inferred from its derived group. If a $K$-linear $g$ satisfies $\psi_U(gx,gy)=c\psi_U(x,y)$, apply this equality with $y$ replaced by $ay$ for every $a\in K$. Nondegeneracy of the trace pairing gives

$$
\mathcal H(gx,gy)=c\mathcal H(x,y).
\tag{7.23}
$$

Consequently

$$
G_U=
\left\{g\in\operatorname{Res}_{F/\mathbf Q}\operatorname{GU}(\mathcal H):
\mu(g)\in\mathbf G_m\right\},
\tag{7.24}
$$

where $\mathbf G_m\to\operatorname{Res}_{F/\mathbf Q}\mathbf G_m$ is diagonal and $\mu=c$ is the PEL multiplier. Over $\overline{\mathbf Q}$ it is isomorphic to
$\prod_{\tau:F\hookrightarrow\overline{\mathbf Q}}\operatorname{GL}_2\times\mathbf G_m$, with the last coordinate the common multiplier. Hence $G_U$ is connected reductive. If $d=[F:\mathbf Q]$, its dimensions are

$$
\begin{aligned}
\dim_{\mathbf Q}V_U&=4d,
&g_U&=2d,\\
\dim G_U&=4d+1,
&\dim G_U^{\mathrm{der}}&=3d,\\
Z_U&=\{z\in\operatorname{Res}_{K/\mathbf Q}\mathbf G_m:
z\bar z\in\mathbf G_m\},
&\dim Z_U&=d+1.
\end{aligned}
\tag{7.25}
$$

Here $g_U$ is the dimension of the abelian varieties in the binary-unitary PEL functor.

The determinant and multiplier are related by

$$
N_{K/F}(\det_K g)=\mu(g)^2.
\tag{7.26}
$$

Accordingly its abelianization is the determinant--multiplier torus

$$
G_U/G_U^{\mathrm{der}}
\simeq
\{(a,c)\in\operatorname{Res}_{K/\mathbf Q}\mathbf G_m
\times\mathbf G_m:a\bar a=c^2\},
$$

with the actual image of $G_U(\mathbf A_f)$ retained when components are formed.

Right multiplication gives the required inner form explicitly. The map

$$
B^1\longrightarrow\operatorname{SU}(\mathcal H),
\qquad
b\longmapsto(x\longmapsto x\bar b)
\tag{7.27}
$$

is a homomorphism, since reversal by quaternion conjugation cancels reversal of right multiplication. Formula (7.19) shows that it is an isometry, and its $K$-determinant is $\operatorname{Nrd}(b)$. It is an isomorphism because it is a closed injection between connected three-dimensional groups. Hence

$$
G_U^{\mathrm{der}}\simeq
\operatorname{Res}_{F/\mathbf Q}B^1,
\qquad
G_U^{\mathrm{ad}}\simeq
\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B).
\tag{7.28}
$$

For comparison, the common-norm quaternionic-line group has dimension $3d+1$, derived dimension $3d$, connected center $\mathbf G_m$, and multiplier $\operatorname{Nrd}\in\mathbf G_m$; the binary-unitary group has the dimensions and multiplier in (7.25)--(7.26). Thus the derived and adjoint groups agree, but the connected centers have dimensions $d+1$ and $1$, respectively. This is a genuine change of PEL presentation rather than a central packet appended to a fixed module.

We next construct the positive Hodge map. Write $K=F(\sqrt\Delta)$ with $\Delta$ totally negative. At a real place $\tau$, (7.18) is split exactly when $\tau(\beta)>0$. Thus $\mathcal H_\tau$ has signature $(1,1)$ at the unique split place $\tau_0$ and signature $(2,0)$ at every Hamiltonian place. By multiplying $\delta$ by an element of $F^\times$, arrange

$$
\varphi_\tau(\delta)=it_\tau,
\qquad t_\tau>0,
\tag{7.29}
$$

for chosen extensions $\varphi_\tau:K\hookrightarrow\mathbf C$. In an orthogonal basis with real coefficients $a_1=1$ and $a_2=-\tau(\beta)$, define $J_\tau$ by $+i$ on a positive coordinate and by $-i$ on a negative coordinate. Directly,

$$
\psi_{U,\tau}(x,J_\tau x)
=2t_\tau\sum_i|a_i|\,|x_i|^2>0.
\tag{7.30}
$$

The corresponding $h_U:\mathbb S\to G_{U,\mathbf R}$ has weight one, satisfies
$\mu(h_U(z))=z\bar z$, and has the desired adjoint map. Its determinant law is

$$
P_a(Z)=
\prod_{\varphi:K\hookrightarrow\mathbf C}
(Z-\varphi(a))^{r_\varphi},
\qquad
r_\varphi+r_{\bar\varphi}=2,
\tag{7.31}
$$

with $(r_\varphi,r_{\bar\varphi})=(1,1)$ at $\tau_0$ and $(2,0)$ at a compact place for the extension $\varphi_\tau$ chosen in (7.29). Relabeling that extension by its conjugate writes the latter pair as $(0,2)$; this is the ordered definite CM choice, not a second positive Hodge map for the same labeled $\delta$. Thus every definite CM orientation and the reflex field are retained rather than being read from the adjoint group alone.
At $\tau_0$ the equal multiplicities do not distinguish the two conjugate half-plane components; the sign of the ordered $J_{\tau_0}$-orientation is therefore retained as a separate component label, exactly as in (3.19).

All rational form invariants are explicit. The alternating form $\psi_U$ itself has only its symplectic dimension; determinant, Hasse, and Clifford labels belong to the polarized Morita packet. The binary Hermitian determinant and normalized unitary discriminant are

$$
\det(\mathcal H)=[-\beta],
\qquad
\operatorname{disc}_U(\mathcal H)=[\beta]
\quad\text{in }F^\times/N_{K/F}K^\times.
\tag{7.32}
$$

There is no independent Hermitian Hasse invariant in rank two: (7.32) is equivalent to the inner quaternion class $(K/F,\beta)=[B]$. For comparison with the orthogonal and quaternionic rows, the underlying norm form is

$$
q_{\mathcal H}(a,b)=N_{K/F}(a)-\beta N_{K/F}(b)
=\operatorname{Nrd}_B(a+bj)
\simeq\langle1,-\Delta,-\beta,\Delta\beta\rangle.
\tag{7.33}
$$

It has square determinant and discriminant $1$. At every place $u$ of $F$ its Hasse symbol and oriented even Clifford algebra are

$$
\epsilon_u(q_{\mathcal H})
=(\Delta,\beta)_u(-1,-1)_u,
\qquad
C^+(q_{\mathcal H})\simeq B\times B^{\mathrm{op}}.
\tag{7.34}
$$

Indeed, expanding the three nontrivial coefficient pairs in (7.33) gives
$(-\Delta,-\beta)(-\Delta,\Delta\beta)(-\beta,\Delta\beta)=(\Delta,\beta)(-1,-1)$, while the standard Clifford generators of the two-fold norm form give the two quaternion factors $B$ and $B^{\mathrm{op}}$.
The orientation orders the two split-center Clifford factors. The real signatures are $(2,2)$ at $\tau_0$ and $(4,0)$ at a Hamiltonian place, exactly corresponding to Hermitian signatures $(1,1)$ and $(2,0)$. Thus determinant, discriminant, Hasse, Clifford, orientation, and signature data all recover the same quaternionic inner form and the same active component.

The global-middle-form argument is compatible with this row without any new patching. For a Raynaud degeneration with $D_U=K$, (3.12) subtracts the multiplicities in (7.31), (5.12b) gives

$$
\det(\mathcal H_0)
=\det(\mathcal H)\det(\mathcal H_T)^{-1}
\quad\bmod N_{K/F}K^\times,
\tag{7.35}
$$

and the real signatures and ordered CM orientations subtract in the same labeled factors. The single global $H_0$ of Chapter 4 makes (7.35) satisfy norm reciprocity. If a toric block is nonzero, $N$ in (9.4) is $K$-linear and (9.5) places it in $\operatorname{Lie}(G_U)$; (9.6) then proves that the weight cocharacter is noncentral. Under (7.28) its parabolic is therefore a proper parabolic of the same quaternionic adjoint group. At a compact real factor a nonzero binary outer hyperbolic plane is already incompatible with signature $(2,0)$; when no compact real factor gives that immediate contradiction, the global forbidden-parabolic argument still applies. No central direction of the larger torus $Z_U$ can imitate monodromy.

Finally fix an odd catalog-good $p$ and a place $w\mid p$ of $F$. Put $\mathcal R=\mathcal O_{F_w}$ and $\mathcal S=\mathcal O_{K_w}$, allowing the split unramified quadratic algebra. Since the adjoint group is hyperspecial, $B_w$ is split. There is an integral cyclic presentation

$$
\mathcal O_{B_w}=\mathcal S\oplus\mathcal S j,
\qquad
ja=\bar a j,
\qquad
j^2=1,
\tag{7.36}
$$

The action of this crossed product on the finite etale $\mathcal R$-algebra $\mathcal S$ identifies it with
$\operatorname{End}_{\mathcal R}(\mathcal S)\simeq M_2(\mathcal R)$, so it is a maximal order in $M_2(F_w)$. On the left $\mathcal S$-lattice $L_U=\mathcal O_{B_w}$, (7.20) is $\langle1,-1\rangle$. Because $2$ is a unit, the vectors

$$
u=(1,1),
\qquad
v=\tfrac12(1,-1)
\tag{7.37}
$$

give the Hermitian matrix $H_1$. Choose an anti-invariant unit $\delta_w\in\mathcal S^\times$; in the split case take $(a,-a)$. Unramified trace duality then makes
$\operatorname{Tr}_{K_w/\mathbf Q_p}(\delta_w\mathcal H)$ perfect on $L_U$. Hence $L_U$ is an explicit self-dual integral representative. For a fixed global $\delta$, this does not authorize changing the rational alternating form. Write $\delta=s_w\delta_w$ with $s_w\in F_w^\times$ and rewrite that same form as
$\operatorname{Tr}_{K_w/\mathbf Q_p}(\delta_w\mathcal H_w)$ with $\mathcal H_w=s_w\mathcal H$. At places where $\delta$ and the different are units one can take $s_w=1$. At any other place declared catalog-good, perfect trace duality says that the already chosen alternating self-dual lattice is Hermitian self-dual for $\mathcal H_w$; Lemma 6.1 then transports the pair $(\mathcal H_w,L)$ to the standard unimodular hyperbolic coordinates above. Thus the same normal form results for the fixed PEL pairing without pretending that its displayed global factor $\delta$ is a unit.

Conversely, Lemma 6.1 shows that every self-dual representative of this unramified binary packet with split adjoint is isometric to (7.37): split adjoint means $\beta$ is a local norm, so the Hermitian plane is hyperbolic, and its determinant label fixes its unique unimodular genus. A common unit multiplier $c_p$ is realized in the basis (7.37) by $u\mapsto c_pu$, $v\mapsto v$. This works simultaneously at every $w\mid p$ because the PEL multiplier is the one diagonal $c_p\in\mathbf Z_p^\times$.

The comparison with the quaternionic-line presentation is literal on the underlying symplectic lattice. With $\delta_w\in K_w$, projection and reduced trace give

$$
\operatorname{Tr}_{K_w/\mathbf Q_p}
\bigl(\delta_w\operatorname{pr}_{K_w}(x\bar y)\bigr)
=\operatorname{Tr}_{F_w/\mathbf Q_p}
\operatorname{Trd}_{B_w}(x\bar y\delta_w).
\tag{7.38}
$$

Thus both rows use $L_U=\mathcal O_{B_w}$ with the same alternating form; only the prescribed endomorphism order changes from $\mathcal O_{B_w}$ to $\mathcal S$. Integral Morita reduction sends the quaternionic-line packet to $J_1$, while (7.37) sends the unitary packet to $H_1$, and (7.27) identifies both derived hyperspecial group schemes with $\operatorname{SL}_{2,\mathcal R}$. In the split quaternionic row a matrix of determinant $c_p$ realizes the same unit multiplier. This constructs and classifies every odd good representative and proves compatibility of the two presentations, not merely equality of their rational adjoint groups.

### 7.6 Central modifications

A connected central modification changes the center and multiplier torus but not the adjoint algebra $B$. It does **not**, merely as a group-theoretic operation, determine or preserve a PEL representation: two PEL realizations with the same adjoint datum can have different noncentral Morita packets. The more restrictive operation treated in this section is a central refinement implemented inside a fixed PEL presentation by adjoining derived-trivial packets. For that operation the noncentral Morita ranks and local Clifford and Brauer invariants are unchanged. It can change:

1. the image of the multiplier character;
2. the component set;
3. the ineffective rational center in a level action; and
4. whether the universal family descends to the quotient.

On the PEL side this restricted statement is packetwise concrete. If the common refinement is obtained by adjoining only derived-trivial PEL tensors, the algebra with involution has the form

$$
(D^\natural,*^\natural)
\sim_{\mathrm{Morita}}
(D,*)\times\prod_j(E_j\times E_j^{\mathrm{op}},\mathrm{swap}),
\tag{7.39}
$$

possibly with rank-one unitary center packets in place of a split exchange pair. The corresponding module is $V$ together with evaluation pairs $P_j\oplus P_j^\vee$ or Hermitian lines. These added packets have derived group trivial. An exchange pair retains its rank and ordered idempotents; a unitary line retains the norm class (5.10a) and must satisfy $[a']=[ca]$ for the same rational similitude $c$ as every noncentral packet. Its Hasse invariant is empty, but its real sign remains a component label. Conversely, if a proposed central modification adds a packet of reduced rank at least $2$ with nontrivial derived group, it has changed the adjoint datum and is not central.

The binary-unitary row is not described by (7.39), because it replaces the noncentral packet rather than adjoining a derived-trivial one. Section 7.5 supplies the missing rational and integral comparison; Section 11.2 supplies its common-refinement deck comparison.

Every comparison therefore retains the actual common multiplier and the actual component orientation. One does not replace the abelianized quotient by the multiplier quotient unless surjectivity has been proved. Likewise, a finite tensor kernel is divided out only after its effective action has been computed.

At a catalog-good place the central representatives preserve the hyperspecial lattice, their finite group-scheme kernels are prime to $p$, and the effective deck set is finite. Section 11 uses those facts to extend the deck action before properness is known.

### 7.7 Exhaustion and the complete comparison table

**Proposition 7.1 (exhaustion of Book 127 quaternionic presentations).** For the division quaternionic datum with one active real place, every PEL realization satisfying Definition 1.1 of Book 127 reduces, after full-idempotent Morita equivalence and removal of derived-trivial central packets, to either the quaternionic Hermitian line of Section 7.1 or the binary-unitary plane of Section 7.5. The remaining operations are matrix Morita transfer and the central refinements of Section 7.6.

**Proof.** A polarized Morita decomposition writes the connected derived group as the product of the derived groups of the noncentral simple $*$-orbits; the common similitude condition couples their centers but does not identify two derived factors. The group
$\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B)$ is $\mathbf Q$-simple: over a normal closure its factors are indexed transitively by the embeddings of the field $F$. Exactness therefore leaves one noncentral $*$-orbit. Matrix factors are removed by a full idempotent, and Section 5.1 leaves only the six low-rank packets listed there.

The orthogonal rank-four packet has two absolute $A_1$ factors. The only Book 123 descent that could turn those into the conjugate factors of the required restriction of scalars is the quadratic corestriction row; (7.13a) excludes its split input for the one-active-factor datum. The bare alternating enlargement is independently excluded by the nonpositive symplectic adjoint in Section 7.4. The same positivity calculation excludes an orthogonal rank-three multiplicity packet: at the active split real factor, its commuting acting algebra has symplectic adjoint, whereas a positive involution on a split real matrix algebra is adjoint to a positive definite symmetric form and is orthogonal. An exchange involution on two real simple factors is also not positive: for the scalar element $(1,-1)$ one has $xx^*=(-1,-1)$ and negative total trace. The positive exchange allowed by a nontrivial action on the center is instead complex conjugation on a CM center; that is precisely the unitary packet. An alternating plane is split at every real label of its totally real center; an inner twist compact at the Hamiltonian labels is the quaternionic-line Morita packet. Higher ranks have the wrong root system by Section 5.1.

The survivors are therefore a reduced quaternionic Hermitian line and a binary Hermitian plane over a CM quadratic center. In the binary case, (5.4) identifies its inner class with $(K/F,\beta)$; equality of the adjoint datum forces $(K/F,\beta)\simeq B$, so $K$ embeds in $B$ and the packet is exactly (7.18)--(7.20). Section 7.1 audits the line whenever its global positive Hodge lift exists, while Section 7.5 constructs the positive binary-unitary replacement. Derived-trivial packets do not change this conclusion, and Section 7.6 classifies exactly how they can be adjoined. $\square$

| presentation | ordinary rank | reduced noncentral packet | form invariant | common multiplier | orientation | good lattice |
|---|---:|---|---|---|---|---|
| direct trace | $4[F:\mathbf Q]$ over $\mathbf Q$ | quaternionic Hermitian line | $[B]$ and real positivity | $\operatorname{Nrd}(c)\in\mathbf Q^\times$ | active half-plane | maximal-order lattice, Morita symplectic at good $p$ |
| binary unitary | $4[F:\mathbf Q]$ over $\mathbf Q$ | $\langle1,-\beta\rangle$ over $K/F$ | $[-\beta]$, $[B]=(K/F,\beta)$; (7.34) gives Hasse and Clifford data | $\mu\in\mathbf Q^\times$, $N_{K/F}(\det_K g)=\mu^2$ | active half-plane label and ordered definite CM types | $\mathcal O_{B_w}\simeq\mathcal O_{K_w}^2$ as a module, Hermitian hyperbolic and symplectically self-dual at good $p$ |
| matrix Morita | $m\dim_{\mathbf Q}V$ | same as source | unchanged by full idempotent | unchanged | transported determinant line | $\Lambda^m$ |
| corestriction, $r=1$ | $2$ over the block field | alternating or exchange rank $2$ | rank only | determinant | ordered line | $J_1$ or evaluation packet |
| corestriction, $r=2$ | $4$ over the block field | orthogonal rank $4$ input | $d$, $\epsilon$, $C^+$ | product of the two determinants | Clifford/component label | unimodular standard rank $4$ lattice; excluded by (7.13a) here |
| bare hyperbolic form of $r=2$ | $8$ over the block field | same orthogonal rank $4$ rational packet | same $d$, $\epsilon$, $C^+$ | tensor multiplier | $W$ then $W^\vee$ | outside the PEL catalog: exceptional stabilizer equality, but the symplectic adjoint on $D_H$ is not positive; the input is also excluded here by (7.13a) |
| higher tensor or hyperbolic block | $2^r$ or $2^{r+1}$ | larger classical stabilizer | not PEL-exact | irrelevant | irrelevant | outside the catalog |
| fixed-presentation central refinement | unchanged unless a stated central character summand is added | unchanged adjoint packets; exchange or rank-one unitary center packet | exchange rank or unitary class $[a]$ | exact common central character image | ordered idempotents or real sign retained | same hyperspecial packets and prime-to-$p$ finite kernels; use the quaternionic-line or binary-unitary row for the noncentral lattice |

This table is an admission table, not a claim that every displayed rejected rational representation has a positive Hodge lift. Proposition 7.1 is the passage from the table to literal presentation independence: it includes a change of noncentral packet, not only changes of coordinates or center.

## 8. The similarity torsor and its adjoint Hasse kernel

The global form $H$ is now real and locally comparable with $V$. A rational faithful similarity may still fail because its obstruction can live in a central torus. The boundary argument needs only the adjoint group, so forcing a full lift would be both unnecessary and potentially false.

### 8.1 The oriented similarity bitorsor

Put

$$
G_H=\operatorname{GSim}_D(H,\psi_H)^\circ.
\tag{8.1}
$$

Define the selected oriented similarity space by

$$
\mathscr I(S)=
\left\{(f,c):
\begin{array}{l}
f:H_S\xrightarrow{\sim}V_S\text{ is }D_S\text{-linear},\\
\psi(fx,fy)=c\psi_H(x,y),\quad c\in S^\times,\\
f\text{ preserves every catalog orientation}
\end{array}
\right\}.
\tag{8.2}
$$

It is a left $G_H$--right $G_{\mathscr D}$ bitorsor whenever geometrically nonempty. Theorem 4.1 and the catalog calculations give

$$
\mathscr I(\mathbf Q_w)\ne\varnothing
\quad\text{for every place }w.
\tag{8.3}
$$

At $p$, Theorem 6.3 verifies that the local point lies in the selected self-dual genus with its common multiplier. At infinity, Section 5.5 verifies the selected component.

### 8.2 Hasse injectivity for the quaternionic adjoint group

Quotient (8.2) by both centers. The $D$-linear condition fixes every center field and packet label, and type $A_1$ has no nontrivial Dynkin-diagram automorphism. Thus the resulting twist is inner, rather than a hidden permutation of restriction-of-scalars factors. Its class lies in the Hasse kernel for

$$
G^{\mathrm{ad}}
=\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B).
\tag{8.4}
$$

**Theorem 8.1 (adjoint Hasse kernel).** One has

$$
\ker^1\!\left(\mathbf Q,
\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B)
\right)=1.
\tag{8.5}
$$

**Proof.** Restriction of scalars reduces the assertion to $\operatorname{PGL}_1(B)$ over $F$. From

$$
1\longrightarrow\mathbf G_m\longrightarrow
\operatorname{GL}_1(B)\longrightarrow
\operatorname{PGL}_1(B)\longrightarrow1
\tag{8.6}
$$

and noncommutative Hilbert 90, the connecting map

$$
H^1(F,\operatorname{PGL}_1(B))\longrightarrow\operatorname{Br}(F)
\tag{8.7}
$$

is injective. A locally trivial torsor has Brauer image zero in every $\operatorname{Br}(F_u)$. Global Brauer injectivity makes its global image zero, and (8.7) makes the torsor trivial. $\square$

Therefore there is a rational oriented adjoint identification

$$
\alpha:G_H^{\mathrm{ad}}\xrightarrow{\sim}
G_{\mathscr D}^{\mathrm{ad}}
\simeq\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B).
\tag{8.8}
$$

### 8.3 Why no central lifting assertion is needed

For

$$
1\longrightarrow Z\longrightarrow G_{\mathscr D}
\longrightarrow G^{\mathrm{ad}}\longrightarrow1,
\tag{8.9}
$$

lifting (8.8) can be obstructed in $H^2(\mathbf Q,Z)$, and two lifts can differ by $H^1(\mathbf Q,Z)$. A norm torus can also have a nontrivial Hasse kernel. We make no assertion that these groups vanish.

The surviving class acts trivially on the adjoint parabolic variety. Two rational trivializations of the adjoint bitorsor differ by an inner automorphism, which sends a rational parabolic to a rational conjugate. Hence existence and properness of the parabolic below are independent of every central lift.

## 9. Monodromy produces a forbidden parabolic

### 9.1 The weight cocharacter and the nonzero operator

On (4.12), define

$$
\gamma(t)|_X=t,
\qquad
\gamma(t)|_{H_0}=1,
\qquad
\gamma(t)|_{Y_{\mathbf Q}}=t^{-1}.
\tag{9.1}
$$

It is $D$-linear and preserves $\psi_H$, so

$$
\gamma:\mathbf G_m\longrightarrow G_H.
\tag{9.2}
$$

Its nonnegative-weight parabolic is the stabilizer of

$$
0\subset X\subset X\oplus H_0\subset H.
\tag{9.3}
$$

Define

$$
N(x+u+y)=\nu(y).
\tag{9.4}
$$

Equation (2.12) makes $N$ $D$-linear. Symmetry of (2.13) gives

$$
\psi_H(Na,b)+\psi_H(a,Nb)=0,
\tag{9.5}
$$

so $N\in\operatorname{Lie}(G_H)$. Moreover,

$$
N^2=0,
\qquad
\operatorname{Ad}(\gamma(t))N=t^2N.
\tag{9.6}
$$

If $T\ne0$, then $Y_{\mathbf Q}\ne0$ and $\nu$ is an isomorphism, so $N\ne0$.

### 9.2 Noncentrality and properness

**Lemma 9.1.** If $T\ne0$, the adjoint cocharacter $\gamma_{\mathrm{ad}}$ is nontrivial.

**Proof.** If it were trivial, $\gamma$ would be central in $G_H$ and would act trivially on its Lie algebra. Equation (9.6) would then give $t^2N=N$ for every $t$, forcing $N=0$. $\square$

A nontrivial rational cocharacter of a semisimple adjoint group pairs nontrivially with a root. The opposite root has the negative pairing, so its root subgroup is absent from the nonnegative parabolic. Therefore

$$
P(\gamma_{\mathrm{ad}})\subsetneq G_H^{\mathrm{ad}}
\tag{9.7}
$$

is a proper rational parabolic. Transport through (8.8) gives a proper rational parabolic in (1.1).

### 9.3 The division contradiction and false-flag audit

A proper $F$-parabolic of $\operatorname{PGL}_1(B)$ is equivalent to an $F$-point of its Severi--Brauer conic, hence to a nonzero proper right ideal of $B$, hence to $B\simeq M_2(F)$. Since $B$ is division, (1.1) has no proper rational parabolic. Thus $T=0$.

The use of $N$ is essential. It excludes all five false sources of a flag:

1. a hyperbolic summand fixed by the whole derived group;
2. a Morita multiplicity summand;
3. the even-sign kernel of a tensor representation;
4. a common-norm, unitary determinant--multiplier, or other multiplier center; and
5. a finite central modification.

In cases 1--4, a flag supported only in the auxiliary center would make $\gamma_{\mathrm{ad}}$ trivial, contradicting (9.6). Case 5 does not change the adjoint group. Thus the parabolic is genuinely noncentral even in presentations containing an a priori isotropic hyperbolic summand.

## 10. From potential reduction to properness

### 10.1 Potential good reduction

**Theorem 10.1 (presentation-independent boundary exclusion).** Let $\mathscr D$ be any Book 127 PEL realization of the quaternionic division datum and let $v$ be catalog-good for its exact integral data. Every PEL abelian variety over the fraction field of a complete mixed-characteristic discrete valuation ring above $v$ has potential good reduction.

**Proof.** Proposition 7.1 reduces every such presentation to the quaternionic-line or binary-unitary noncentral packet, with the Morita and central operations already treated in Chapters 5--7. After finite extension the abelian variety is semistable. If its torus were nonzero, Chapters 2--8 would construct the rational adjoint identification and Chapter 9 would produce a forbidden rational parabolic. Hence the toric rank is zero. A semistable abelian variety with toric rank zero has good reduction over the semistable extension. $\square$

The proof uses no smoothness assertion about an integral determinant scheme.

### 10.2 Odd auxiliary level kills finite inertia

Let $q\ne p$ be odd. Potential good reduction makes the inertia image on $T_qA$ finite. On a full level-$q$ cover, inertia acts trivially on $A[q]$, so its image lies in

$$
1+q\operatorname{End}_{\mathbf Z_q}(T_qA).
\tag{10.1}
$$

This group has no nontrivial finite-order element. Indeed, the $q$-adic logarithm converges on it and satisfies $\log(g^n)=n\log(g)$. If $g^n=1$, characteristic zero gives $\log(g)=0$, and the inverse exponential gives $g=1$.

Thus inertia acts trivially on the full Tate module. The Neron--Ogg--Shafarevich criterion gives good reduction over the original trait.

**Proposition 10.2.** On a fine full prime-to-$p$ level divisible by an odd $q$, every generic PEL object has good reduction without extending the fraction field.

### 10.3 Extension of every PEL structure

Let $\mathcal A/R$ be the abelian scheme supplied by good reduction.

1. Every $\mathcal O$-endomorphism extends uniquely by the extension theorem for homomorphisms of abelian schemes. Ring relations extend from the dense generic fiber.
2. The polarization homomorphism extends uniquely. Its symmetry and degree extend, and positivity extends by the polarization-locus theorem. No chosen inducing line bundle is required.
3. Prime-to-$p$ torsion is finite etale. Trivial inertia extends a full level basis, and a $K$-orbit level extends by finite etale descent.
4. The determinant polynomial equality extends coefficientwise on $\operatorname{Lie}(\mathcal A)$ because it is an equality of regular functions holding on the dense generic point.
5. The polarization kernel remains finite locally free of the prescribed prime-to-$p$ type.
6. The orientation cover is finite etale at a catalog-good place. Its generic section extends uniquely over the henselian trait; equivalently, the selected open-and-closed packet label cannot jump.

This order matters: the action and polarization are extended as morphisms before their determinant, positivity, and type conditions are checked.

### 10.4 The fine properness theorem

Let $Q_{K'}^{\mathrm{amb}}$ be the fine quasi-projective integral PEL scheme of Book 127 at a level containing full auxiliary odd level as above. Fix the open-and-closed generic component union carrying the quaternionic curve and define

$$
Q_{K'}^{\mathrm{fl}}
=\overline{Q_{K',E}^{\mathrm{sel}}}^{\,\mathrm{sch}}
\subset Q_{K'}^{\mathrm{amb}}.
\tag{10.2}
$$

This is the **flat-closure PEL model**. On every affine chart its coordinate ring is the image in the localization obtained by inverting the base uniformizer, hence has no uniformizer torsion. It is therefore flat over the discrete valuation base. A mixed-characteristic extension constructed in Section 10.3 factors through (10.2): every function vanishing on the generic component vanishes after pullback to the torsion-free DVR.

**Theorem 10.3.** The morphism

$$
Q_{K'}^{\mathrm{fl}}\longrightarrow\operatorname{Spec}\mathcal O_{E,v}
\tag{10.3}
$$

is proper and therefore projective.

**Proof.** Embed the quasi-projective scheme (10.2) as an open subscheme of its scheme-theoretic closure $\overline Q$ in a projective space over $\mathcal O_{E,v}$. The generic fiber $Q_{K',E}^{\mathrm{sel}}$ is already proper: the division adjoint group has no rational parabolic. Hence it is closed in the generic projective space and

$$
\overline Q_E=Q_{K',E}^{\mathrm{sel}}.
\tag{10.4}
$$

Suppose the boundary $\overline Q\setminus Q_{K'}^{\mathrm{fl}}$ were nonempty. The generic fiber is dense in $\overline Q$ by the definition of schematic closure. The trait-selection lemma for a specialization in a noetherian scheme then gives a DVR $R$ and a map $\operatorname{Spec}R\to\overline Q$ whose generic point lies in (10.4) and whose closed point lies in the boundary. This is a mixed-characteristic vertical trait. Replace $R$ by its completion. The generic point remains in (10.4), the closed point remains over the chosen boundary point, and the reduction theorems of Book 40 now apply with exactly their stated hypotheses. Theorem 10.1 and Proposition 10.2 give good reduction over its fraction field without a further finite extension, and Section 10.3 extends the entire PEL object over $R$. The preceding paragraph makes that extension factor through $Q_{K'}^{\mathrm{fl}}$. Its composite with $\overline Q$ and the completed original trait map agree generically, hence agree everywhere because $\overline Q$ is separated. Their closed points cannot then lie on opposite sides of the boundary, a contradiction.

Thus the boundary is empty and $Q_{K'}^{\mathrm{fl}}=\overline Q$ is projective. Projectivity implies properness. $\square$

No assertion that $Q_{K'}^{\mathrm{amb}}$ is flat or has no extra vertical components is made. If a separate local calculation proves $Q_{K'}^{\mathrm{amb}}=Q_{K'}^{\mathrm{fl}}$, then Theorem 10.3 proves properness of the whole ambient PEL scheme. Smoothness or that equality is not an input to the boundary theorem.

## 11. Finite central quotients before properness

The generic central quotient cannot be invoked only after the source is known proper. One must first show that the actual finite deck operation exists on the integral PEL scheme. The central $H^1$ obstruction also prevents replacing the deck group by a naive quotient of adelic centers.

### 11.1 The actual deck group and the central cohomology obstruction

Let

$$
1\longrightarrow Z\longrightarrow G^\natural
\longrightarrow G'\longrightarrow1
\tag{11.1}
$$

be a central comparison used in a common refinement. The sequences on rational and adelic points contain connecting maps

$$
G'(\mathbf Q)\longrightarrow H^1(\mathbf Q,Z),
\qquad
G'(\mathbf A_f)\longrightarrow H^1(\mathbf A_f,Z).
\tag{11.2}
$$

They need not vanish. Consequently not every target component has a lift to one chosen PEL component, and two lifts need not differ by a rational point of $Z$.

The construction of Book 126 is interpreted as follows. Take the finite disjoint union of the PEL components representing every lift class that actually occurs. Pass to a common sufficiently small normal level. Its generic central comparison supplies a finite deck groupoid on this union. After choosing one representative of each object and, if necessary, inducing from the component stabilizers, that groupoid is presented by a finite group $\Delta$ acting on a finite disjoint union. Its effective form is

$$
\Delta_{\mathrm{eff}}=\Delta/Z_{\mathrm{triv}},
\tag{11.3}
$$

where $Z_{\mathrm{triv}}$ consists of rational central elements already identified by the left action.

Thus $H^1$ is handled by enlarging the component union before taking the quotient. It is not handled by asserting adelic central surjectivity or a Hasse norm theorem that may be false.

Write $Q'_{\mathrm{amb}}$ for the resulting finite disjoint union of fine ambient PEL schemes, and write $Q'_{\mathrm{fl}}$ for the schematic closure of the selected generic component union inside it. Each deck map will first be built on $Q'_{\mathrm{amb}}$; after restriction, schematic density will verify the group law on $Q'_{\mathrm{fl}}$.

### 11.2 The quaternionic-line--binary-unitary common refinement

The preceding construction applies to the genuinely different packet of Section 7.5, not only to a fixed-presentation central refinement. Let

$$
G_B=\{b\in\operatorname{Res}_{F/\mathbf Q}B^\times:
\operatorname{Nrd}(b)\in\mathbf G_m\}
\tag{11.4}
$$

when the direct quaternionic-line Hodge lift is admitted, and let $G_U$ be (7.24). Both map onto
$G^{\mathrm{ad}}$, and (7.27) identifies their derived groups. Their connected common refinement is

$$
G^\sharp=(G_B\times_{G^{\mathrm{ad}}}G_U)^\circ.
\tag{11.5}
$$

The projections induce isomorphisms on adjoint groups and central isogenies on derived groups. Their kernels are central tori. Put
$U(1)=\ker(N_{K/F}:\operatorname{Res}_{K/F}\mathbf G_m\to\mathbf G_m)$; then the unitary center fits into

$$
1\longrightarrow
\operatorname{Res}_{F/\mathbf Q}U(1)
\longrightarrow Z_U\xrightarrow{\ \mu\ }\mathbf G_m
\longrightarrow1
\tag{11.6}
$$

as an exact sequence of fppf sheaves. The equation $z\bar z=c$ makes surjectivity fppf, not necessarily on rational points. Its connecting terms include

$$
H^1\!\left(\mathbf Q,\operatorname{Res}_{F/\mathbf Q}U(1)\right)
=H^1(F,U(1))
=F^\times/N_{K/F}K^\times,
\tag{11.7}
$$

The long exact sequence of (11.6) therefore gives

$$
H^1(\mathbf Q,Z_U)
\simeq
F^\times/
\bigl(N_{K/F}K^\times\cdot\mathbf Q^\times\bigr),
$$

and the analogous local and adelic quotients. Thus a rational or adelic lift cannot be chosen by simply dividing the two centers. Even when the quadratic Hasse norm theorem detects a global norm from all local norms, the group (11.7), and possibly its displayed quotient, need not vanish. For another central refinement its torus can have an additional Hasse kernel. The lift-class enlargement in Section 11.1 remains necessary in this concrete comparison.

The Hodge maps $h_B$ and $h_U$ have the same adjoint projection. Whenever both lifts occur, their pair defines $h^\sharp:\mathbb S\to G^\sharp_{\mathbf R}$. More generally, replacing $G_B$ by any other Book 127 presentation and taking the same connected fiber product gives the common refinement promised by Proposition 7.1. The definite choices in (7.31) can enlarge the unitary reflex field, so all generic comparison maps are first formed over the compositum $E^\sharp$ of the two reflex fields. Their descent datum is part of the same finite component groupoid; no equality of reflex fields is assumed. Choose compact opens $K_i\subset G_i(\mathbf A_f)$ and a sufficiently small
$K^\sharp$ inside their inverse images. On a connected component, let $\Gamma_i$ be the image in $G^{\mathrm{ad}}(\mathbf Q)^+$ of the corresponding rational level stabilizer. The derived isogenies imply that $\Gamma_B$, $\Gamma_U$, and $\Gamma^\sharp$ are commensurable. After replacing $\Gamma^\sharp$ by a normal finite-index subgroup of their intersection, the generic maps are the finite covers

$$
\Gamma^\sharp\backslash X^+
\longrightarrow\Gamma_i\backslash X^+,
\qquad
\Delta_i=\Gamma_i/\Gamma^\sharp.
\tag{11.8}
$$

Choose fine levels in the two PEL schemes whose adjoint arithmetic group is $\Gamma^\sharp$. Their generic component curves are normal by Book 127. The common-refinement comparison of Book 126 identifies their normal generic models over $E^\sharp$: analytically both are $\Gamma^\sharp\backslash X^+$, and the finite birational comparison supplied by the common canonical model is an isomorphism. Denote this common base curve by $Q^\sharp_{E^\sharp}$. It carries a pullback of each presentation's PEL family, but those two families are not identified.

The finitely many components not represented by one such quotient are exactly the lift classes governed by (11.2) and (11.7); include all of them before taking the finite deck quotient. This constructs the generic comparison without claiming that $G_B(\mathbf A_f)\to G^{\mathrm{ad}}(\mathbf A_f)$ or
$G_U(\mathbf A_f)\to G^{\mathrm{ad}}(\mathbf A_f)$ is surjective.

At an odd catalog-good place, (7.36)--(7.38) identify the two derived hyperspecial group schemes and their underlying self-dual symplectic lattice. The norm on units of the unramified or split algebra $\mathcal O_{K_w}/\mathcal O_{F_w}$ is surjective. Condition 6 of the catalog-good Definition 1.1 requires an already occurring lift class to have a $p$-integral representative, while the selected multiplier component requires its multiplier to be a unit. The explicit norm surjectivity now verifies that requirement for the binary-unitary center: multiply by a central unit to place the representative in the chosen unitary hyperspecial without altering its adjoint deck transformation. Shrinking one common prime-to-$p$ principal level clears the finitely many remaining denominators away from $p$. On the binary-unitary PEL family the resulting deck representative is a $K$-linear prime-to-$p$ quasi-isogeny with $\mathcal O_K$-stable kernel; on the quaternionic-line family it is the corresponding $B$-linear quasi-isogeny with $\mathcal O_B$-stable kernel. Their adjoint actions agree through (11.8), and their common multipliers agree through (7.26) and (7.38). The integral comparison is made at a place of $E^\sharp$ above $v$; properness then descends through the finite faithfully flat extension to either original reflex field.

This is the required isogeny comparison. It does not assert that the two universal abelian schemes are canonically isogenous across presentations: different central Hodge lifts can have different generic endomorphism algebras. What is canonical is the finite common-refinement map of bases and, in each PEL presentation, the prime-to-$p$ quasi-isogenies representing its deck action. That is exactly the information needed to extend the action integrally and to compare properness.

### 11.3 Extension of deck transformations to the integral PEL scheme

Fix $\delta\in\Delta_{\mathrm{eff}}$. We extend the actual generic deck transformation just constructed; no new adelic lift is chosen here. At a catalog-good place its representative is $p$-integral and its denominators are prime to $p$. There are two possible moduli descriptions.

If $\delta$ only changes a level trivialization, leave the abelian scheme, action, and polarization fixed and act on the level orbit. This is visibly defined over the integral base.

In the general common-refinement description, $\delta$ is represented by a prime-to-$p$ PEL quasi-isogeny. Because the deck set is finite, first refine the common normal level by one full prime-to-$p$ principal level that clears the denominators of every deck representative. Multiplying $\delta$ by an integer prime to $p$ then gives an isogeny whose kernel is killed by that level integer. On the universal family the kernel is the subgroup of the constant full-level module prescribed by the corresponding catalog lattice map. It is therefore a finite etale subgroup scheme over the whole integral base, not merely the closure of a generic subgroup. Book 38's quotient theorem produces the quotient abelian scheme. The prescribed PEL algebra action descends because the subgroup is stable under it. The extra principal level is removed only afterward by its finite effective level quotient.

On the generic fiber the catalog lattice calculation gives an integer $m$, prime to $p$, and a polarization $\lambda'$ satisfying

$$
f^\vee\lambda'f=m\lambda.
\tag{11.9}
$$

Equivalently, the kernel is isotropic for the commutator pairing required by polarized quotient descent. That isotropy equality extends on the finite etale kernel, so Book 38's polarized quotient theorem constructs $\lambda'$ integrally and preserves its catalog type. Since $f$ is etale, $df$ is an isomorphism; the Lie determinant law and its labeled factors are unchanged. The transformed level and the orientation are the ones computed for $\delta$. The target is therefore another object of the same ambient integral component union. Yoneda gives a morphism

$$
\widetilde\delta:Q'_{\mathrm{amb}}\longrightarrow Q'_{\mathrm{amb}}.
\tag{11.10}
$$

The map (11.10) preserves the selected generic union, so it preserves its schematic closure and restricts to $Q'_{\mathrm{fl}}$. The inverse deck element restricts to its inverse there. Every group relation holds on the generic fiber; since that fiber is schematically dense in $Q'_{\mathrm{fl}}$ and the model is separated, it holds on all of $Q'_{\mathrm{fl}}$. Hence the deck group acts honestly on the flat-closure integral model before that model is known proper. The construction also gives the individual Yoneda maps (11.10) on the ambient scheme, but no density argument is applied to possible extra vertical components.

This action on the base must be distinguished from descent of the universal abelian scheme. In the quasi-isogeny case the maps $f$ above identify fibers only in the prime-to-$p$ isogeny category; they are not a $\Delta_{\mathrm{eff}}$-linearization of the universal PEL object by isomorphisms. Such a genuine linearization is automatic for the pure level action of the preceding paragraph, but it is extra data for a general central or common-refinement quotient.

The prime-to-$p$ finite-central-kernel hypothesis is exact. If a central representative has a nonintegral $p$-component or a finite kernel of $p$-power order, the preceding finite-etale extension fails and that place must be removed from the catalog-good set or treated by a separate finite-flat analysis.

### 11.4 The finite integral quotient

The stable closed subscheme $Q'_{\mathrm{fl}}$ is quasi-projective. In this section abbreviate it to $Q'$. Choose an ample line bundle $L$ and replace it by

$$
L_\Delta=\bigotimes_{\delta\in\Delta_{\mathrm{eff}}}\delta^*L.
\tag{11.11}
$$

It is ample and $\Delta_{\mathrm{eff}}$-linearized. Invariant nonvanishing affine charts cover $Q'$. On such a chart $\operatorname{Spec}A$, the quotient is

$$
\operatorname{Spec}A^{\Delta_{\mathrm{eff}}}.
\tag{11.12}
$$

Every $a\in A$ is integral over the invariant ring because it satisfies

$$
\prod_{\delta\in\Delta_{\mathrm{eff}}}(T-\delta a).
\tag{11.13}
$$

Thus (11.12) is finite. The affine quotients glue along invariant overlaps, giving a finite integral quotient

$$
Q'\longrightarrow Q'/\Delta_{\mathrm{eff}}.
\tag{11.14}
$$

Here are the two descent details hidden by that short construction. The linearization of (11.11) is the canonical one obtained by permuting its factors. Given a finite orbit, a sufficiently high power of $L_\Delta$ has a section nonvanishing at every point of that orbit; multiplying its translates gives an invariant section with the same property. Its nonvanishing locus is a stable affine open. These normed sections supply the asserted cover, and localization commutes with invariants for an invariant section, so the affine quotients really do glue. No properness of $Q'$ was used.

### 11.5 Fine, stack, and coarse conclusions

If the effective action is free, (11.14) is the finite orbit quotient. When the universal PEL object carries a genuine $\Delta_{\mathrm{eff}}$-linearization by PEL isomorphisms, as it does for a pure level action, this quotient is the corresponding fine quotient and the universal object descends. A quasi-isogeny linearization alone does not imply either assertion. If stabilizers occur, the quotient stack

$$
[Q'/\Delta_{\mathrm{eff}}]
\tag{11.15}
$$

is the correct stack quotient of the base action, while the finite scheme quotient is its coarse space. The stack carries the universal PEL abelian scheme exactly when the universal object has the genuine isomorphism linearization just described. Under that hypothesis, it descends to the coarse space exactly when every stabilizer acts trivially on the complete PEL object. Without it, the construction supplies only the prime-to-$p$ quasi-isogenies and their correspondence data; no universal abelian scheme on either quotient is asserted.

After Theorem 10.3, the source $Q'_{\mathrm{fl}}$ is proper. Its finite quotient is therefore proper. A power of (11.11) divisible by $|\Delta_{\mathrm{eff}}|$ has trivial stabilizer action on every geometric fiber and descends to an ample line bundle on the quotient, proving projectivity. Properness at a general neat level also follows by taking a normal full-level subgroup and its finite effective level quotient. At non-neat level the quotient stack and coarse scheme of the flat-closure model are proper, with both the linearization and stabilizer qualifications of the preceding paragraph retained for universal families.

No new boundary can appear under the quaternionic-line--binary-unitary comparison. Indeed, after a finite extension of the fraction field, a generic trait point of a finite quotient lifts to the finite cover; normalizing the trait in that extension gives an integral trait. Properness of the cover extends the lift, and composition extends the original point. Equivalently, a finite image of a proper flat-closure model is closed and proper. The stack has the same valuative conclusion after the corresponding finite cover, while its coarse space forgets stabilizers but not limit points.

## 12. The presentation-independent theorem

### 12.1 Main theorem

**Theorem 12.1 (Book 127 presentation-independent properness).** Let $F$ be totally real and let $B/F$ be a quaternion division algebra split at exactly one real place. Let

$$
\mathscr D=(D,*,V,\psi,h)
\tag{12.1}
$$

be any quaternionic PEL realization in the sense of Book 127 whose adjoint datum is
$\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B)$, including any connected central modification allowed there. Let $v\mid p$ be catalog-good for its exact order, lattice, multiplier component, and orientation data.

Then:

1. every complete-trait-valued generic PEL object has potential good reduction;
2. on a fine cover with full level at an odd auxiliary prime, it has good reduction over the original trait;
3. the fine flat-closure PEL model (10.2) is proper and projective over $\mathcal O_{E,v}$;
4. every normal neat level quotient and every selected component union of that flat-closure model is proper and projective;
5. the finite integral quotient attached to a compatible central modification or to the quaternionic-line--binary-unitary common refinement exists before properness and is proper and projective afterward;
6. at a level with stabilizers, the quotient stack and coarse scheme are proper; a universal PEL abelian scheme exists on the quotient stack only when the deck action has a genuine PEL-isomorphism linearization, and under that hypothesis it descends to the coarse scheme only when every stabilizer acts trivially;
7. the result is independent of replacing a quaternionic Hermitian line by the genuinely different binary-unitary plane, as well as of direct-trace coordinates, matrix Morita transfer, and derived-trivial central refinement; and
8. no new boundary appears after any of the finite common-refinement, neat-level, stack, or coarse quotients.

At a dyadic place, the same conclusion requires the complete oriented self-dual genus and common-multiplier hypothesis of Proposition 6.4. The theorem does not assert that the ambient Book 127 determinant scheme has no additional vertical components. A separate flatness theorem identifies it with (10.2), if available. No integral smoothness conclusion is included.

**Proof.** Proposition 7.1 proves that the Book 127 hypothesis is exhaustive: after polarized Morita reduction there is one noncentral packet, and it is either a quaternionic Hermitian line or the binary-unitary plane (7.19). The global middle form and its local comparisons are Theorem 4.1, with the exact rational invariants and odd self-dual representatives in Chapters 5--7. In particular, (7.35) proves compatibility of the unitary packet with the global middle form and (7.36)--(7.38) compare it integrally with the quaternionic-line packet at every odd good place.

The adjoint bitorsor is trivial by Theorem 8.1. If a torus occurred, Chapter 9 would give a proper rational parabolic in $\operatorname{Res}_{F/\mathbf Q}\operatorname{PGL}_1(B)$, contradicting division; (7.27)--(7.28) show that this is the same adjoint group in the binary-unitary presentation. This proves potential good reduction. Auxiliary level and the congruence argument give actual good reduction, after which every PEL structure extends. The projective-closure argument of Theorem 10.3 gives fine flat-closure properness without an equicharacteristic or local-flatness assumption. Chapter 11 constructs the generic common refinement with its actual $H^1$ lift classes, extends its prime-to-$p$ deck quasi-isogenies before properness, and then constructs the finite orbit, stack, and coarse quotients, including the fine level quotients when the required isomorphism linearization exists. Section 11.5 proves directly that none of those finite operations creates a boundary. $\square$

### 12.2 Hypothesis and conclusion ledger

| issue | exact input | conclusion | excluded overclaim |
|---|---|---|---|
| toric $D$-action | covariant cocharacters and periods, Rosati only in the pairing | (2.9), (2.12) | treating character pullback as the same left action |
| toric determinant | derivative (3.1), tangent exact sequence (3.11) | packet formula (3.15) | deriving the packet from toric rank alone |
| middle form | polarized Raynaud abelian quotient and Betti homology | one global $(H_0,\psi_0)$ | patching unrelated local complements |
| local taxonomy | the six low-rank Morita packets in Section 5.1 | explicit determinant, Hasse, Clifford, and orientation classification | invoking PEL-exactness as a classification theorem |
| product compatibility | global $H_T$, $H_0$, and formulas (5.7)--(5.12) | all reciprocity relations | guessing the last local sign |
| common multiplier | one level similarity at each place | one $c_w$ for all packets | independent packet scalars |
| odd lattices | unramified maximal order, self-duality, quasi-split packet, labels | Theorem 6.3 | arbitrary orthogonal Gram--Schmidt |
| dyadic lattices | complete oriented genus supplied separately | Proposition 6.4 | rational invariants determine a dyadic lattice |
| binary-unitary replacement | $K/F\hookrightarrow B$, $\mathcal H=\langle1,-\beta\rangle$, positive CM involution, labeled signature | (7.24)--(7.38), same quaternionic adjoint and odd hyperspecial derived model | treating equality of adjoint groups as a PEL or integral comparison |
| corestriction | splitting, central-kernel audit, full stabilizer audit | $r=1$ is alternating PEL-exact; $r=2$ is only an orthogonal rational exception and is excluded here by (7.13a); $r\ge3$ has a larger stabilizer | every tensor representation is PEL |
| hyperbolic repair | commutant calculation (7.17), positivity of the acting involution, and the real corestriction invariant | the bare construction is not PEL: rank four passes only the stabilizer test, while the symplectic adjoint fails positivity | parity repair or stabilizer equality implies PEL admission |
| presentation scope | exact Book 127 stabilizer, positive involution, and one quaternionic adjoint factor | Proposition 7.1 exhausts the noncentral packets | restricting the theorem to a preselected catalog row |
| adjoint comparison | local bitorsor points and Brauer injectivity | rational adjoint isomorphism | full similarity torsor is trivial |
| false flags | nonzero $N$ and $\operatorname{Ad}(\gamma)N=t^2N$ | noncentral proper parabolic | an auxiliary invariant Lagrangian is enough |
| actual good reduction | potential good reduction and odd full auxiliary level | trivial inertia | finite inertia vanishes automatically |
| central quotient | actual $H^1$ lift classes, integral representatives, finite action | finite integral quotient and the line--unitary common refinement | naive adelic center surjectivity or a cross-presentation universal isogeny |
| geometry | ambient representability, quasi-projectivity, schematic flat closure, and mixed-characteristic trait extension | projective flat-closure model | asserting ambient flatness, absence of vertical components, or smoothness |

### 12.3 Dependency closure

The proof uses only the following direct predecessors.

**Book 38** supplies dual abelian schemes, polarizations, Weil pairings, extension of homomorphisms and polarizations, and quotients by finite subgroup schemes.

**Book 40** supplies semistable reduction, the Raynaud one-motive, its prime-to-residue-characteristic weight filtration, duality, tropicalization, positivity, monodromy, the congruence argument, and the good-reduction criterion. Lemma 2.1 derives only the geometric characteristic-zero $p$-torsion analogue from its finite-level construction.

**Book 87** supplies quaternion norm calculations, the quadratic embedding criterion, local Hilbert symbols including the dyadic rational symbol, Brauer injectivity, the global invariant sequence, and the quadratic Hasse norm theorem. The low-rank Clifford formulas needed here are proved directly in Chapters 5 and 7 from those quaternion calculations.

**Book 123** supplies restriction and corestriction, the exact splitting test, trace and Hermitian pairings, tensor parity, central kernels, hyperbolic enlargement, Morita language, and multiplier calculations.

**Book 126** supplies the quaternionic and binary-unitary adjoint data, signature and component bookkeeping, central modifications, common refinements, and the finite generic central quotient with its lift-class warning.

**Book 127** supplies the exact PEL definition, determinant convention, integral orders and lattices, the ambient fine quasi-projective scheme, level quotients, universal families, and the distinction between fine, stack, and coarse moduli. This book takes the schematic flat closure inside that ambient scheme; it imports no assertion that the ambient determinant locus is flat.

No theorem about a later integral local model, boundary compactification, or smoothness is used. The only class-field-theoretic inputs are the quadratic norm theorem and the global Brauer invariant sequence already used explicitly in Book 87.

### 12.4 Final synthesis

A Raynaud torus determines two covariant left $D$-modules: its cocharacters and its period lattice. Polarization pairs them with the Rosati involution, while tropicalization identifies them rationally and positively. Differentiation identifies the cocharacter module with $\operatorname{Lie}(T)$, so the toric positive block has exactly the determinant packet required by the PEL Lie convention. The opposite convention is obtained only after dualizing, applying $*$, and exchanging the packet label.

The middle form is not a Hasse-theoretic invention. It is the Betti homology of the polarized Raynaud abelian quotient. Consequently all local determinants, discriminants, Hasse symbols, Clifford classes, signatures, and orientations come from one global object and obey their product formulas automatically. The low-rank Morita classification explains each invariant, while the odd integral calculation proves the precise self-dual standard packets and common multiplier at a good place. In the binary-unitary row, the Hermitian determinant $[-\beta]$, norm form, Hasse symbol, oriented Clifford pair, and signatures explicitly recover $B$, and the lattice $\mathcal O_{K_w}^2$ compares with the quaternionic maximal-order lattice through one identical symplectic form.

Local similarities need not lift through the center. Their adjoint bitorsor does: the quaternionic adjoint Hasse kernel injects into the global Brauer group. The tropical isomorphism then gives a nonzero Lie-algebra element $N$, and the weight cocharacter scales it by $t^2$. This proves that the resulting parabolic is noncentral even in Morita, tensor, hyperbolic, and centrally modified presentations. Division of $B$ forbids that parabolic, so the torus vanishes.

Odd full level kills the remaining finite inertia and extends the complete PEL object. A projective closure then has no boundary because every putative boundary point is reached by such a completed mixed-characteristic trait. The generic quaternionic-line--binary-unitary common refinement retains all central $H^1$ lift classes; its prime-to-$p$ deck quasi-isogenies have already been extended on the ambient PEL schemes, restricted to the schematic flat closures, and quotiented before properness is descended. Thus properness is literally presentation-independent for every Book 127 quaternionic PEL realization, including a change of noncentral packet. The nontrivial tensor candidate fails the stabilizer test, while the bare hyperbolic candidate still fails positivity of its acting involution. No circular local-model assertion, ambient flatness assertion, or smoothness assertion is used.
