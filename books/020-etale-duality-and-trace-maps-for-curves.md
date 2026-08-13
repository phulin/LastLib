# Étale Duality and Trace Maps for Curves

## Contents

- [1. Why duality needs a trace](#1-why-duality-needs-a-trace)
  - [1.1 Cohomology and its missing fundamental class](#11-cohomology-and-its-missing-fundamental-class)
  - [1.2 Conventions, coefficients, and normalizations](#12-conventions-coefficients-and-normalizations)
  - [1.3 The shape of the answer](#13-the-shape-of-the-answer)
- [2. Cohomology with compact support](#2-cohomology-with-compact-support)
  - [2.1 Compactification and extension by zero](#21-compactification-and-extension-by-zero)
  - [2.2 Independence of compactification](#22-independence-of-compactification)
  - [2.3 Localization, functoriality, and examples](#23-localization-functoriality-and-examples)
  - [2.4 Relative compact support](#24-relative-compact-support)
- [3. The extraordinary inverse image](#3-the-extraordinary-inverse-image)
  - [3.1 The adjoint demanded by integration](#31-the-adjoint-demanded-by-integration)
  - [3.2 Construction in the required range](#32-construction-in-the-required-range)
  - [3.3 Composition, base change, and dualizing complexes](#33-composition-base-change-and-dualizing-complexes)
  - [3.4 Verdier duality](#34-verdier-duality)
- [4. Purity and fundamental classes](#4-purity-and-fundamental-classes)
  - [4.1 Smooth purity](#41-smooth-purity)
  - [4.2 Regular immersions and Gysin maps](#42-regular-immersions-and-gysin-maps)
  - [4.3 Cycle classes and excess warnings](#43-cycle-classes-and-excess-warnings)
- [5. Trace maps](#5-trace-maps)
  - [5.1 The universal counit](#51-the-universal-counit)
  - [5.2 Finite maps](#52-finite-maps)
  - [5.3 Smooth maps and integration along fibers](#53-smooth-maps-and-integration-along-fibers)
  - [5.4 Proper oriented maps](#54-proper-oriented-maps)
- [6. Products, projection, and Künneth duality](#6-products-projection-and-künneth-duality)
  - [6.1 Cup products with compact support](#61-cup-products-with-compact-support)
  - [6.2 The projection formula](#62-the-projection-formula)
  - [6.3 External products and Künneth](#63-external-products-and-künneth)
  - [6.4 Degrees, twists, and signs](#64-degrees-twists-and-signs)
- [7. Poincaré duality for smooth curves](#7-poincaré-duality-for-smooth-curves)
  - [7.1 The derived theorem](#71-the-derived-theorem)
  - [7.2 Proper curves](#72-proper-curves)
  - [7.3 Open curves and residues](#73-open-curves-and-residues)
  - [7.4 Explicit calculations](#74-explicit-calculations)
- [8. Local duality on a curve](#8-local-duality-on-a-curve)
  - [8.1 Purity at a closed point](#81-purity-at-a-closed-point)
  - [8.2 Residue and boundary pairings](#82-residue-and-boundary-pairings)
  - [8.3 Ramified coefficients](#83-ramified-coefficients)
- [9. Relative duality](#9-relative-duality)
  - [9.1 The relative theorem](#91-the-relative-theorem)
  - [9.2 Smooth proper curves](#92-smooth-proper-curves)
  - [9.3 Specialization of pairings](#93-specialization-of-pairings)
- [10. Semistable fibers and the limits of ordinary Poincaré duality](#10-semistable-fibers-and-the-limits-of-ordinary-poincaré-duality)
  - [10.1 The normalization complex](#101-the-normalization-complex)
  - [10.2 The dualizing complex of a nodal fiber](#102-the-dualizing-complex-of-a-nodal-fiber)
  - [10.3 Relative semistable duality](#103-relative-semistable-duality)
  - [10.4 What specialization preserves](#104-what-specialization-preserves)
- [11. Exact torsion and adic duality](#11-exact-torsion-and-adic-duality)
  - [11.1 Perfectness at finite level](#111-perfectness-at-finite-level)
  - [11.2 Passage to integral adic coefficients](#112-passage-to-integral-adic-coefficients)
  - [11.3 Free pairings and torsion linking forms](#113-free-pairings-and-torsion-linking-forms)
  - [11.4 Rational duality](#114-rational-duality)
- [12. Base change, Galois actions, and Frobenius](#12-base-change-galois-actions-and-frobenius)
  - [12.1 Base change for compact support and duality](#121-base-change-for-compact-support-and-duality)
  - [12.2 Galois equivariance](#122-galois-equivariance)
  - [12.3 Arithmetic and geometric Frobenius](#123-arithmetic-and-geometric-frobenius)
- [13. Correspondences and cycle classes](#13-correspondences-and-cycle-classes)
  - [13.1 Pull-push actions](#131-pull-push-actions)
  - [13.2 Transpose and adjoint](#132-transpose-and-adjoint)
  - [13.3 Cycle classes and projection](#133-cycle-classes-and-projection)
  - [13.4 Hecke-type correspondences](#134-hecke-type-correspondences)
- [14. The curve duality package](#14-the-curve-duality-package)
  - [14.1 A theorem for later use](#141-a-theorem-for-later-use)
  - [14.2 A hypothesis audit](#142-a-hypothesis-audit)
  - [14.3 Conclusion](#143-conclusion)

## 1. Why duality needs a trace

### 1.1 Cohomology and its missing fundamental class

The preceding volumes constructed derived étale cohomology, its integral towers, cup products, and the comparison maps that move cohomology through proper and smooth families. Those constructions multiply classes, but multiplication alone does not produce a scalar. On an oriented compact real manifold one integrates a top-degree form. The arithmetic-geometric replacement is a trace

$$
H^{2d}_c(X,\Lambda_n(d))\longrightarrow\Lambda_n
$$

for a smooth $d$-dimensional variety over a separably closed field. Cup product followed by this trace turns complementary degrees into duals.

Two features of the formula are structural. The subscript $c$ is forced by nonproper spaces: a top-degree class must not escape through infinity. The Tate twist $(d)$ is forced by descent: the untwisted top class transforms nontrivially under the ground-field Galois group. Once both corrections are present, the trace is canonical and equivariant.

This book constructs that mechanism for curves. The aim is not merely a list of pairings. We need a system in which traces compose, base change preserves them, curve correspondences have transposes, and passage from $\mathbf Z/\ell^n\mathbf Z$ to $\mathbf Z_\ell$ retains every torsion term. Proper and open curves reveal residues and boundary classes; nodal fibers show exactly why smoothness cannot be erased from Poincaré duality.

### 1.2 Conventions, coefficients, and normalizations

Schemes are locally noetherian. Morphisms used for compact support are separated and of finite type and are assumed compactifiable; Book 19 proves compactifiability in the noetherian situations used here. The application range in this volume is absolute curves and relative morphisms with one-dimensional geometric fibers. Bases in the relative statements are excellent noetherian schemes, or limits obtained from them by the continuity arguments of that book. Fix a prime $\ell$ invertible on every scheme in sight, and write

$$
\Lambda_n=\mathbf Z/\ell^n\mathbf Z,
\qquad \Lambda=\mathbf Z_\ell,
\qquad E=\mathbf Q_\ell.
$$

All complexes are cohomological: $H^i(K[r])=H^{i+r}(K)$. Thus the orientation of a smooth morphism of pure relative dimension $d$ is

$$
f^!K\simeq f^*K(d)[2d].
$$

This convention is worth testing immediately. If $a:X\to\operatorname{Spec}k$ is a smooth curve, then $a^!\Lambda_n=\Lambda_n(1)[2]$, and the counit produces $H_c^2(X,\Lambda_n(1))\to\Lambda_n$, as desired.

For a field $k$ choose a separable closure $k^s$, write $G_k=\operatorname{Gal}(k^s/k)$, and put $\bar X=X\times_k k^s$. Arithmetic Frobenius over $\mathbf F_q$ is $x\mapsto x^q$; geometric Frobenius is its inverse. Arithmetic Frobenius acts on $\Lambda_n(1)$ by $q$, while geometric Frobenius acts by $q^{-1}$. Consequently geometric Frobenius acts by $q^d$ on untwisted top cohomology of a smooth proper $d$-fold. We never use the word Frobenius without specifying the normalization when an eigenvalue is involved.

The symbols $Rf_*$ and $Rf_!$ denote ordinary and compactly supported direct image. The extraordinary inverse image $f^!$ is right adjoint to $Rf_!$. A dual $\mathcal F^\vee$ means $\underline{\operatorname{Hom}}(\mathcal F,\Lambda_n)$ for a finite locally free sheaf. For general constructible complexes, derived internal Hom replaces this elementary dual.

### 1.3 The shape of the answer

There are three levels of duality. The most robust is a derived identity

$$
R\Gamma(X,R\mathcal Hom(K,a^!L))
\simeq
R\operatorname{Hom}(R\Gamma_c(X,K),L).
$$

For smooth $X$ and locally free lisse $\mathcal F$, it becomes Poincaré duality. At finite level it gives a perfect pairing of finite modules

$$
H_c^i(X,\mathcal F)\times
H^{2d-i}(X,\mathcal F^\vee(d))
\longrightarrow\Lambda_n.
$$

At the integral adic level the derived identity remains perfect, but torsion prevents an indiscriminate claim that complementary cohomology groups are ordinary linear duals. Free quotients pair in complementary degrees; torsion pairs one degree off through $\mathbf Q_\ell/\mathbf Z_\ell$. After tensoring with $E$, the familiar perfect vector-space pairing returns.

This hierarchy is a safeguard. Derived duality is the theorem. Degreewise finite-level perfection and rational perfection are consequences. Integral degreewise perfection requires a torsion-freeness hypothesis.

## 2. Cohomology with compact support

### 2.1 Compactification and extension by zero

Let $f:X\to S$ be separated and of finite type. A compactification is a factorization

$$
X\xrightarrow{j}\overline X\xrightarrow{\bar f}S
$$

with $j$ an open immersion and $\bar f$ proper. Such factorizations exist in the noetherian situations used here. For $K\in D_c^b(X,\Lambda_n)$ define

$$
Rf_!K=R\bar f_*j_!K.
$$

Extension by zero is exact for an open immersion: its geometric stalk is the original stalk on $X$ and zero on the boundary. The derived symbol is therefore unnecessary on $j_!$. If $S$ is a point, this gives

$$
R\Gamma_c(X,K)=R\Gamma(\overline X,j_!K).
$$

Compact support is not a topological decoration added after cohomology. It is a functor defined before taking cohomology, so it participates in triangles, products, and adjunctions. If $X$ is proper, take $j$ to be the identity and obtain $Rf_!=Rf_*$. If $X$ is not proper, the equality can fail dramatically: $H^0(\mathbf A^1,\Lambda_n)=\Lambda_n$, but $H_c^0(\mathbf A^1,\Lambda_n)=0$.

### 2.2 Independence of compactification

The definition appears to depend on $\overline X$. We now remove that dependence. Given two compactifications $j_i:X\hookrightarrow\overline X_i$, take the schematic closure of the diagonal image of $X$ in $\overline X_1\times_S\overline X_2$. It is proper over $S$ and maps properly to both compactifications. Its intersection with the open $X\times_SX$ is the diagonal, and separatedness shows that the inverse image of $X$ under either projection is exactly this diagonal. Thus $X$ is open in the closure and both projections restrict to its identity. It is enough to compare a compactification with a proper refinement

$$
p:\overline X'\longrightarrow\overline X.
$$

Let $j'$ denote the new open immersion. For every geometric point of $\overline X$, the stalk of $Rp_*j'_!K$ is zero off $X$: the proper fiber lies entirely in the boundary there. On $X$, the map is the identity and the stalk is $K$. Proper base change therefore gives

$$
Rp_*j'_!K\simeq j_!K.
$$

Applying $R\bar f_*$ proves that both compactifications produce canonically isomorphic objects. A third refinement shows the isomorphisms satisfy the cocycle condition. This supplies not merely equality up to some choice, but a functor independent of compactification.

The proof also explains the role of proper base change. Boundary fibers must be inspected after a proper refinement. Without properness, an apparently empty contribution can arrive from infinity.

### 2.3 Localization, functoriality, and examples

Let $i:Z\hookrightarrow X$ be closed and $j:U\hookrightarrow X$ its open complement. The stalkwise exact sequence

$$
j_!j^*K\longrightarrow K\longrightarrow i_*i^*K\longrightarrow
$$

gives the compact-support localization triangle

$$
R\Gamma_c(U,j^*K)\longrightarrow
R\Gamma_c(X,K)\longrightarrow
R\Gamma_c(Z,i^*K)\longrightarrow.
$$

It is the basic computational tool. Compactifying $\mathbf A^1$ inside $\mathbf P^1$ and removing the point at infinity gives

$$
H_c^i(\mathbf A^1,\Lambda_n)=
\begin{cases}
\Lambda_n(-1),&i=2,\\
0,&i\ne2.
\end{cases}
$$

The twist is displayed in the untwisted group; equivalently $H_c^2(\mathbf A^1,\Lambda_n(1))=\Lambda_n$. Applying localization twice gives

$$
H_c^1(\mathbf G_m,\Lambda_n)=\Lambda_n,
\qquad
H_c^2(\mathbf G_m,\Lambda_n)=\Lambda_n(-1).
$$

These groups are dual, respectively, to $H^1(\mathbf G_m,\Lambda_n(1))=\Lambda_n$ and $H^0(\mathbf G_m,\Lambda_n(1))=\Lambda_n(1)$ after twists are placed as in Poincaré duality.

For composable separated finite-type maps $X\xrightarrow fY\xrightarrow gS$, compatible compactifications and independence give

$$
R(g\circ f)_!\simeq Rg_!Rf_!.
$$

An open immersion contributes extension by zero; a proper map contributes ordinary direct image. These two cases generate the general construction.

### 2.4 Relative compact support

Relative compact support records the compactly supported cohomology of every fiber at once. If

$$
\begin{array}{ccc}
X'&\xrightarrow{g'}&X\\
\downarrow f'&&\downarrow f\\
S'&\xrightarrow{g}&S
\end{array}
$$

is cartesian, there is a canonical comparison

$$
g^*Rf_!K\longrightarrow Rf'_!g'^*K.
$$

Choose a compactification. Extension by zero commutes with pullback, and proper base change applies to the proper part; hence the comparison is an isomorphism for finite constructible coefficients of order invertible on the base. Independence of compactification shows that the result does not depend on the choice. In particular,

$$
(R^qf_!K)_{\bar s}\cong H_c^q(X_{\bar s},K_{\bar s}).
$$

This is stronger than ordinary base change for a nonproper map. Compact support controls the boundary precisely because the boundary has been placed inside a proper morphism.

For a normalized adic tower, finite-level comparison, uniform amplitude, and finiteness give the Mittag--Leffler condition established in the preceding volumes. Taking the derived inverse limit therefore produces adic compactly supported base change. No ordinary inverse limit is substituted at this stage.

## 3. The extraordinary inverse image

### 3.1 The adjoint demanded by integration

Pullback $f^*$ is left adjoint to ordinary direct image. Compactly supported direct image needs a different right adjoint. We seek $f^!$ characterized by

$$
\operatorname{Hom}_Y(Rf_!K,L)
\cong
\operatorname{Hom}_X(K,f^!L).
$$

The counit of this adjunction will be the trace. The notation is extraordinary because $f^!$ usually differs from $f^*$. For a smooth map of relative dimension $d$, the difference is exactly the orientation $(d)[2d]$; for a closed immersion, it points in the opposite direction and measures cohomology supported on the closed subset.

The adjunction tells us why the theory is organized at the level of complexes. A trace on one top cohomology group would not determine connecting morphisms, composition, or twisted coefficients. The counit does all of these simultaneously.

### 3.2 Construction in the required range

The construction cannot be obtained merely by declaring a map smooth on a stratification: a singular map need not become smooth after stratifying only its source, and such a declaration would already presuppose purity. We instead use a local adjoint construction whose one geometric input is proved without a trace.

**Affine-line duality lemma.** Let $p:\mathbf A^1_S\to S$, with finite coefficients of order invertible on $S$. For $M\in D_c^b(\mathbf A^1_S,\Lambda_n)$ and $L\in D_c^b(S,\Lambda_n)$ there is a functorial isomorphism

$$
R\mathcal Hom_S(Rp_!M,L)
\simeq
Rp_*R\mathcal Hom_{\mathbf A^1_S}
(M,p^*L(1)[2]). \tag{3.1}
$$

Here is the proof, including the normalization that will later become the trace. Noetherian induction on the base and the support filtration of Book 18 reduce to a lisse sheaf on the complement of finitely many relative points and a sheaf on those points; vertical exceptional loci lie over a smaller closed subset of the base and enter the induction. After an étale change of base the finite monodromy data are constant. On a geometric fiber, the free prime-to-characteristic cochain presentation for the punctured affine line has one generator for each puncture and one relation supplied by infinity. Dualizing that two-term presentation reverses its incidence map. The Kummer boundary of a uniformizer is $1$, so the reversed map is exactly the residue map with target $\Lambda_n(-1)[-2]$. A sheaf on a point is handled by finite adjunction. Thus (3.1) holds on every piece and the two localization triangles glue it for $M$.

The construction is uniform in an étale neighborhood of every geometric point of $S$: all monodromy matrices, punctures, inertia operators, and residue maps are finite data. Over a strict localization, the proper compactification and boundary-presentation arguments of Book 19 identify both sides of (3.1) with these dual finite matrices. This is a strict-local calculation; it does not replace ordinary cohomology of an open family by geometric-fiber cohomology without boundary control. Since geometric stalks are strict-local complexes, they prove (3.1). For $M=\Lambda_n(1)[2]$, its adjoint sends the compact class whose residue at infinity is $1$ to $1$. No trace or purity theorem has been used in this argument.

Iterating (3.1) and using Künneth gives affine-space duality with $p^*L(d)[2d]$. An étale map has $u^!=u^*$, and the residue normalization is unchanged by an étale coordinate change. Hence, for a smooth morphism of pure relative dimension $d$, the local affine-space right adjoints descend to

$$
f^!L=f^*L(d)[2d]. \tag{3.2}
$$

We now construct the adjoint for an arbitrary map in the stated curve-level category. For a closed immersion $i:Z\hookrightarrow P$, the exact functor $i_*$ has a right adjoint on sheaves, namely sections supported on $Z$ restricted to $Z$; deriving it gives $i^!$. If $j:P\setminus Z\hookrightarrow P$, the triangle

$$
i_*i^!L\longrightarrow L\longrightarrow Rj_*j^*L\longrightarrow
$$

and the constructibility and boundedness theorem for $Rj_*$ in Book 19 show that $i^!$ carries bounded constructible complexes to bounded constructible complexes in the required range. Locally on $X$, every finite-type map factors as

$$
X\xrightarrow{i}\mathbf A^N_Y\xrightarrow{p}Y
$$

with $i$ closed. Define the local candidate as $i^!p^!$. On overlaps the two candidates represent the same functor

$$
K\longmapsto
R\mathcal Hom_Y(Rf_!K,L),
$$

so the unique representing isomorphisms satisfy the cocycle condition. A finite support filtration glues them across the chosen affine cover. Boundedness follows from the closed-support bound and (3.2), and constructibility follows by the same finite localization induction. This produces $f^!$ and the adjunction on $D_c^b$.

For an open immersion $j:U\hookrightarrow X$, this construction gives $j^!=j^*$. For a compactification $f=\bar f\circ j$, it gives

$$
f^!=j^*\bar f^!.
$$

Another compactification gives the same object because both candidates are right adjoint to the intrinsic functor $Rf_!$; uniqueness of a right adjoint supplies the canonical comparison and all cocycle compatibilities. This proves existence in the bounded constructible range used by curves and the relative curve families below. No assertion is made here for arbitrary unbounded or nonconstructible coefficients.

### 3.3 Composition, base change, and dualizing complexes

Adjoints turn the composition formula for $Rf_!$ into

$$
(g\circ f)^!\simeq f^!g^!.
$$

The order reverses because right adjoints reverse composition. The isomorphism is associative: both ways of treating three maps are right adjoint to the same compactly supported composite.

In a cartesian square with the stated constructibility and invertibility assumptions, there is an exchange morphism

$$
g'^*f^!L\longrightarrow f'^!g^*L.
$$

It is an isomorphism when the horizontal map is étale, and in the transverse smooth and proper squares used below. It is not the formal right-adjoint mate of proper base change: that mate involves direct image on the other side. Consequently this exchange map must not be promoted to an unrestricted base-change slogan. Pullback through a singular or nontransverse fiber square can acquire a local defect; Chapter 10 makes that defect visible for a node.

For $a:X\to S$, the relative dualizing complex is

$$
\omega_{X/S}^\bullet=a^!\Lambda_n.
$$

Over a field we abbreviate it to $\omega_X^\bullet$. A smooth pure $d$-fold has $\omega_X^\bullet=\Lambda_n(d)[2d]$. A singular curve generally does not. The dualizing complex, rather than a guessed shift of the constant sheaf, is what survives singularities.

### 3.4 Verdier duality

Define

$$
D_XK=R\mathcal Hom(K,\omega_X^\bullet).
$$

Adjunction and the tensor--Hom relation give the global duality isomorphism

$$
R\Gamma(X,D_XK)
\simeq
R\operatorname{Hom}_{\Lambda_n}
(R\Gamma_c(X,K),\Lambda_n).
$$

The proof is direct. A morphism from a test complex $M$ to the left side is, after pullback to $X$, a morphism $a^*M\otimes^LK\to a^!\Lambda_n$. Adjunction converts it to a morphism $M\otimes^LRa_!K\to\Lambda_n$, which is the right side. Yoneda identifies the two complexes.

For bounded constructible $K$, the evaluation map

$$
K\longrightarrow D_XD_XK
$$

is an isomorphism. Nilpotents do not change the étale site. Excellence and noetherian induction give a finite filtration by regular locally closed strata. Embed such a stratum into a smooth affine scheme. The regular-immersion calculation of Section 4.2, whose proof is independent of biduality, identifies its dualizing complex; the assertion there is ordinary biduality for a finite module. Extension by zero and proper pushforward transport the result across strata, and the five lemma closes the induction through localization triangles.

This proof strategy explains both constructibility and finite dimensionality assumptions. Without finite stalks, biduality of modules can fail; without a finite stratification, the induction need not terminate.

Duality exchanges the four operations in a localization. If $j:U\hookrightarrow X$ is open and $i:Z\hookrightarrow X$ is its closed complement, then

$$
D_Xj_!\simeq Rj_*D_U,
\qquad
D_XRj_*\simeq j_!D_U,
$$

and

$$
D_Xi_*\simeq i_*D_Z.
$$

Apply $D_X$ to the triangle $j_!j^*K\to K\to i_*i^*K$. Biduality identifies the resulting reverse triangle with the localization triangle involving $i^!$. This calculation is more informative than a slogan that “boundary terms are dual”: it specifies which extension functor and which restriction occur. On an open curve it becomes the residue sequence at the missing points.

## 4. Purity and fundamental classes

### 4.1 Smooth purity

Let $f:X\to S$ be smooth of pure relative dimension $d$. Smooth purity is the canonical orientation

$$
f^!K\simeq f^*K(d)[2d]
$$

for bounded constructible $K$. This is the isomorphism (3.2), but we now verify its normalization and independence of coordinates. Étale-locally, $f$ factors as an étale map followed by a projection from affine space. Étale maps have $f^!=f^*$. The affine-line duality lemma reduced the projection to the Kummer residue calculation at infinity and showed that

$$
R^2p_!\Lambda_n(1)\simeq\Lambda_n,
$$

with all other compactly supported direct images zero. Its chosen generator is the unique class having residue $1$ at infinity. If $t$ and $u$ are two étale coordinates, the ratio of their local Kummer symbols is a unit; a unit has zero residue. The two generators therefore agree. Products orient affine $d$-space, and étale descent glues the local orientations. This proves that the isomorphism is canonical rather than dependent on coordinates.

The twist is indispensable. Over a nonclosed field, a local parameter changes the Kummer generator by the cyclotomic character. The Tate twist cancels precisely that transformation.

### 4.2 Regular immersions and Gysin maps

Let $i:Z\hookrightarrow X$ be a regular closed immersion of pure codimension one, with both schemes regular in the required neighborhood. This is the codimension needed for closed points on curves and for graphs and finite correspondences on curves. Absolute purity in this range gives

$$
i^!\Lambda_n\simeq\Lambda_n(-1)[-2].
$$

We give the proof because absolute purity is not supplied by the preceding books. In codimension one, a local equation $t$ gives a Kummer class on $X\setminus Z$. On a strict localization at a geometric point of $Z$, the punctured normal trait has the two-term tame-inertia complex; the Kummer boundary of $t$ is its residue generator. It follows there that supported cohomology vanishes outside degree two and equals $\Lambda_n(-1)$ in degree two. Geometric stalks give the asserted complex globally. Multiplying $t$ by a unit does not change the residue, so the class glues.

Adjunction yields the Gysin map

$$
i_*:H^m(Z,\Lambda_n(r))
\longrightarrow
H^{m+2}_Z(X,\Lambda_n(r+1)).
$$

Composing with the map that forgets support gives the ordinary cycle-class pushforward. A closed point on a smooth curve therefore determines a class in $H^2(X,\Lambda_n(1))$.

### 4.3 Cycle classes and excess warnings

For an integral effective Cartier divisor $Z\subset X$, define

$$
\operatorname{cl}_X(Z)=i_*(1)\in H_Z^2(X,\Lambda_n(1)).
$$

Additivity extends the definition to cycles. Proper pushforward and flat pullback commute with cycle classes. For transverse regular immersions, cup product of fundamental classes equals the class of the intersection. The proof reduces étale-locally to concatenating regular sequences, where the product of Kummer boundary symbols is the symbol of the combined sequence.

Nontransverse intersections require an excess bundle and cannot be treated by naive multiplication of multiplicities. Likewise, a singular closed subscheme is not automatically covered by the displayed purity isomorphism. The cases used later avoid that leap. On a regular curve every codimension-one cycle is locally Cartier, so its class is defined by the Kummer boundary of a local equation and additivity. The graph of a map between smooth curves is a regular divisor in their product. Thus points and the finite curve correspondences considered here have cycle classes without invoking purity for an arbitrary singular subscheme.

## 5. Trace maps

### 5.1 The universal counit

For every separated finite-type map in our category, adjunction supplies

$$
\operatorname{Tr}_f:Rf_!f^!K\longrightarrow K.
$$

This is the most general trace in the book. It is compatible with composition:

$$
\operatorname{Tr}_{g\circ f}
=
\operatorname{Tr}_g\circ Rg_!(\operatorname{Tr}_f)
$$

after the canonical identifications. It is also compatible with base change wherever extraordinary base change is an isomorphism.

The formula prevents a common mistake. For a general proper map there is no canonical arrow $Rf_*f^*K\to K$. The canonical counit starts from $Rf_*f^!K$. An orientation, finite étaleness, or another comparison $f^*K\to f^!K$ is needed before one can trace untwisted coefficients.

The trace is characterized by a local normalization. For the identity it is the identity; for affine space it sends the compact fundamental class to $1$; and for a disjoint union it is the sum of the component traces. To see uniqueness, cover the smooth locus by étale charts, where these rules determine the map. The difference of two candidates is supported on a lower-dimensional complement. Localization and purity move that difference into a trace in smaller dimension, where induction applies. This argument is also what makes traces insensitive to the chosen compactification.

The unit and counit identities have a useful computational consequence. Under the adjunction, the identity of $f^!K$ corresponds exactly to $\operatorname{Tr}_f$. Hence any proposed trace can be checked by computing its adjoint. Composition, base change, and the projection formula may then be verified before passing to cohomology, which prevents scalar ambiguities in top degree.

### 5.2 Finite maps

If $f:X\to Y$ is finite, then $Rf_!=Rf_*=f_*$ on sheaves, but $f^!$ still remembers duality along the finite fibers. For a finite étale map there is a canonical identification $f^!=f^*$, and the trace

$$
f_*f^*K\longrightarrow K
$$

is locally the sum map from finitely many copies of $K$. Hence

$$
\operatorname{Tr}_f\circ f^*=(\deg f)\operatorname{id}
$$

when the degree is constant.

For a finite locally free map that is not étale, the duality counit remains canonical, but a trace on ordinary constant coefficients requires an orientation. In the applications, $X$ and $Y$ are regular and $f$ is finite lci—in particular this holds for a finite map between smooth curves, or for a finite flat correspondence explicitly presented as lci. Factoring the graph as a regular immersion followed by a smooth projection gives

$$
\Lambda_n\longrightarrow f^!\Lambda_n.
$$

Composing with the counit defines the oriented finite trace. It agrees on the étale locus with summing sheets and extends across the branch locus by localization and purity. Its composite with pullback is multiplication by the constant scheme-theoretic degree. Without such an orientation, or when flatness is dropped and degrees jump, no untwisted formula is asserted; only the counit from $f^!$ remains canonical.

This distinction matters for correspondences. A finite étale Hecke branch has an immediate transfer. A merely proper branch acts by duality and orientation data, not by pretending that all geometric fibers are a fixed finite set.

Consider the lci map $f:\mathbf A^1\to\mathbf A^1$ given by $t\mapsto t^m$. If $m$ is invertible in the ground field, the map is finite étale away from the origin, and there trace is the sum over the $m$ roots. At the origin the purity construction extends the oriented trace, and $\operatorname{Tr}_f(f^*1)=m$ still holds. If the characteristic divides $m$, the map has an inseparable part. Factor it into a radicial power map followed by a generically separable map. A finite universal homeomorphism induces an equivalence of prime-to-characteristic étale topoi; its oriented trace is multiplication by its inseparable degree, as follows from the Kummer-normalized fundamental class. Transitivity then again gives multiplication by $m$. This example separates geometric points from scheme-theoretic degree.

For a tower of oriented finite locally free lci maps $X\xrightarrow fY\xrightarrow gZ$, the equality

$$
\operatorname{Tr}_{g\circ f}
=\operatorname{Tr}_g\circ g_*\operatorname{Tr}_f
$$

follows from transitivity of regular-immersion and smooth orientations and from the counit composition law. On the common étale locus it is summation twice. Thus the familiar transitivity of field trace is the generic-point shadow of the cohomological composition law, including a purely inseparable factor where no dense étale locus exists.

### 5.3 Smooth maps and integration along fibers

For a smooth map $f$ of pure relative dimension $d$, combine smooth purity with the counit:

$$
\operatorname{Tr}_f:
Rf_!f^*K(d)[2d]\longrightarrow K.
$$

For a complex $K$ on the base, cohomology sheaves receive integration maps

$$
\mathcal H^{m+2d}(Rf_!(f^*K(d)))
\longrightarrow\mathcal H^m(K).
$$

For a sheaf $\mathcal F$ on the base, the only nonzero target degree is $m=0$, giving $R^{2d}f_!f^*\mathcal F(d)\to\mathcal F$. Fiberwise over a separably closed field it sends the fundamental class of each connected component to $1$.

For $\mathbf A^d$, the trace is the product of the one-dimensional traces and identifies $H_c^{2d}(\mathbf A^d,\Lambda_n(d))$ with $\Lambda_n$. For $\mathbf G_m$, it sends the compact fundamental class in degree two to $1$; the degree-one compact class pairs with the Kummer class of the coordinate.

### 5.4 Proper oriented maps

If $f:X\to Y$ is proper and smooth of relative dimension $d$, then $Rf_!=Rf_*$ and the trace reads

$$
Rf_*f^*K(d)[2d]\longrightarrow K.
$$

Equivalently there are pushforwards

$$
f_*:H^m(X,f^*\mathcal F(r))
\longrightarrow
H^{m-2d}(Y,\mathcal F(r-d)).
$$

For a proper local-complete-intersection map between regular schemes, factor it as a regular immersion followed by a smooth map. Purity for the immersion and smooth orientation produce the same formula with $d$ the virtual relative dimension. Independence of factorization follows by comparing two factorizations after embedding them diagonally into a common smooth ambient space; the excess intersection identity cancels the auxiliary normal bundle.

For an oriented finite flat lci map, $d=0$, recovering the degree trace. For the projection $X\times Y\to Y$ with $X$ smooth proper of dimension $d$, the map is ordinary integration over $X$. The composition law is Fubini's theorem in this setting.

## 6. Products, projection, and Künneth duality

### 6.1 Cup products with compact support

If one factor has compact support, intersection of supports remains compact. At the derived level there is a natural product

$$
R\Gamma_c(X,K)\otimes^L R\Gamma(X,L)
\longrightarrow
R\Gamma_c(X,K\otimes^LL).
$$

Choose a compactification $j:X\hookrightarrow\overline X$. The sheaf map

$$
j_!K\otimes^L Rj_*L
\longrightarrow j_!(K\otimes^LL)
$$

is an isomorphism on the open and has zero stalk on the boundary, so it yields the product. Independence of compactification follows from the proper projection formula.

There is also a product of two compactly supported classes. What generally fails is a canonical compactly supported result from two arbitrary ordinary classes on a nonproper space. The missing support condition is geometric, not a defect of notation.

### 6.2 The projection formula

For $f:X\to Y$ and suitable bounded constructible $K,L$,

$$
Rf_!(K\otimes^Lf^*L)
\simeq
Rf_!K\otimes^LL.
$$

For an open immersion this is checked stalkwise; for a proper map it is the proper projection formula; a compactification proves the general case. Combining it with trace gives

$$
f_*(x\smile f^*y)=f_*x\smile y.
$$

This identity is the engine behind adjointness of correspondences and compatibility of cycle pushforward with intersections. It also fixes twists automatically. If $f$ has relative dimension $d$, the left side can be integrated only after $x$ supplies the relative $(d)[2d]$ orientation.

### 6.3 External products and Künneth

For separated finite-type $X,Y$ over a separably closed field,

$$
R\Gamma_c(X,K)\otimes^L_{\Lambda_n}R\Gamma_c(Y,L)
\xrightarrow{\sim}
R\Gamma_c(X\times Y,K\boxtimes^LL)
$$

in the finite constructible range. We recall the proof rather than importing a Künneth theorem. Choose finite étale hypercovers adapted to common constructibility stratifications of $K$ and $L$. The bisimplicial hypercover of $X\times Y$ is their product. The shuffle and Alexander--Whitney maps are inverse up to homotopy, so its total cochain complex is the derived tensor product of the two factor complexes. Finiteness and the dimension bounds of Book 18 make every relevant totalization finite. Dévissage from lisse sheaves to the constructible complexes gives the displayed isomorphism. Compactifying both factors and observing that extension by zero on the product is the external product of the two extensions proves the compact-support version. Finite Tor terms remain part of the derived tensor product.

The trace of a product is the tensor product of traces. In particular, the fundamental class of a product of smooth curves is the external product of the curve fundamental classes; this is the compatibility needed for graph and diagonal kernels on curve products.

### 6.4 Degrees, twists, and signs

If $x$ has degree $a$ and $y$ degree $b$, then

$$
x\smile y=(-1)^{ab}y\smile x
$$

after switching coefficient factors. Twists add but do not contribute a sign. On a curve the middle pairing on $H^1$ is skew-symmetric when $2$ is invertible; for the constant locally free coefficients used below it is in fact alternating for every $\ell$, as Section 7.2 checks separately. With coefficients of characteristic two, “alternating” must always mean $x\smile x=0$ and cannot be inferred from skew-symmetry.

The trace has cohomological degree $-2d$ and twist $-d$. Writing it as a map from a shifted complex makes it degree zero. This is why

$$
H_c^i(X,\mathcal F)\times
H^{2d-i}(X,\mathcal F^\vee(d))
\to\Lambda_n
$$

has no unexplained residual shift or twist.

## 7. Poincaré duality for smooth curves

### 7.1 The derived theorem

Let $C$ be a smooth separated curve of finite type over a separably closed field, and let $\mathcal F$ be a finite locally free lisse $\Lambda_n$-sheaf. Smooth purity and Verdier duality give

$$
R\Gamma(C,\mathcal F^\vee(1))[2]
\simeq
R\operatorname{Hom}_{\Lambda_n}
(R\Gamma_c(C,\mathcal F),\Lambda_n).
$$

Because $\Lambda_n$ is self-injective as a finite ring, taking cohomology gives perfect pairings of finite modules

$$
H_c^i(C,\mathcal F)\times
H^{2-i}(C,\mathcal F^\vee(1))
\longrightarrow\Lambda_n.
$$

The pairing is cup product, evaluation $\mathcal F\otimes\mathcal F^\vee\to\Lambda_n$, and trace. This concrete description agrees with the abstract duality isomorphism because both arise from the same adjunction counit.

The proof has three decisive steps. Smooth purity identifies the dualizing complex. Constructible finiteness makes both sides bounded finite complexes. Biduality reduces étale-locally to the ordinary dual of a finite free module. None of these steps uses properness; properness only permits removal of the subscript $c$.

Perfection can also be read one degree at a time. Exactness of $\operatorname{Hom}_{\Lambda_n}(-,\Lambda_n)$ identifies the complementary cohomology group with the full module dual of $H_c^i$. Hence a class pairing to zero with every complementary class is zero, and every functional is represented. If the sheaf becomes constant only after a finite étale cover, this conclusion does not divide by the covering degree: the adjunction and its sheet-summing trace descend the derived isomorphism itself.

### 7.2 Proper curves

Let $C$ be smooth, proper, and geometrically connected of genus $g$. Then

$$
H^0(C,\Lambda_n)=\Lambda_n,
\qquad
H^1(C,\Lambda_n)=\Lambda_n^{2g},
\qquad
H^2(C,\Lambda_n)=\Lambda_n(-1).
$$

Trace identifies $H^2(C,\Lambda_n(1))$ with $\Lambda_n$. The pairing in degrees $0$ and $2$ says that $1$ and the fundamental class are dual. In degree one it gives a perfect alternating form

$$
H^1(C,\Lambda_n)\times H^1(C,\Lambda_n(1))
\longrightarrow\Lambda_n.
$$

For odd $\ell$, alternation follows from graded commutativity. For $\ell=2$, the free calculations of Book 19 lift $x\in H^1(C,\Lambda_n)$ to $\widetilde x\in H^1(C,\mathbf Z_2)$ and identify $H^2(C,\mathbf Z_2)$ with the torsion-free module $\mathbf Z_2(-1)$. Graded commutativity gives $2\widetilde x^2=0$, hence $\widetilde x^2=0$, and reduction gives $x^2=0$. Thus no exceptional coefficient prime is being suppressed. After choosing a trivialization of the twist over the separably closed field, this is the familiar symplectic form. The trivialization is not Galois invariant over the original field, so the untwisted-looking version is not canonical arithmetically.

For $C=\mathbf P^1$, the middle group vanishes and duality pairs only degrees zero and two. For an elliptic curve, the middle group has rank two and the pairing agrees with the alternating form dual to the Weil pairing on torsion. These examples show that duality fixes the form, not just the ranks.

If $f:C\to C'$ is finite of degree $m$ between smooth proper curves, projection gives

$$
\langle f^*x,y\rangle_C
=
\langle x,f_*y\rangle_{C'}.
$$

Taking $y=f^*z$ yields $f_*f^*z=mz$. Ramification does not alter the degree formula; it is absorbed by the oriented fundamental class of the finite flat map.

### 7.3 Open curves and residues

Let $\overline C$ be smooth proper of genus $g$, let $D$ be a reduced set of $r>0$ geometric points, and put $U=\overline C\setminus D$. Compact-support duality pairs

$$
H_c^i(U,\Lambda_n)\quad\text{with}\quad
H^{2-i}(U,\Lambda_n(1)).
$$

Localization gives

$$
0\longrightarrow\Lambda_n
\xrightarrow{\Delta}\Lambda_n^D
\longrightarrow H_c^1(U,\Lambda_n)
\longrightarrow H^1(\overline C,\Lambda_n)
\longrightarrow0,
$$

where $\Delta(1)=(1,\ldots,1)$, as well as

$$
H_c^0(U,\Lambda_n)=0,
\qquad
H_c^2(U,\Lambda_n)=\Lambda_n(-1).
$$

The dual localization sequence, obtained from purity at $D$, is

$$
0\longrightarrow H^1(\overline C,\Lambda_n(1))
\longrightarrow H^1(U,\Lambda_n(1))
\xrightarrow{(\operatorname{res}_x)}\Lambda_n^D
\xrightarrow{\sum}\Lambda_n
\longrightarrow0.
$$

Thus residues sum to zero. The quotient $\Lambda_n^D/\Delta\Lambda_n$ on the compact side is dual to the kernel of the sum on the ordinary side. Boundary paths and logarithmic Kummer classes are not unrelated decorations: duality identifies them.

Both $H_c^1(U,\Lambda_n)$ and $H^1(U,\Lambda_n)$ have rank $2g+r-1$. Ordinary cohomology alone does not pair perfectly with itself when $U$ is open. The compact support on one side is essential.

### 7.4 Explicit calculations

For $U=\mathbf A^1$, $g=0$ and $r=1$. The boundary quotient vanishes, so $H_c^1=H^1=0$, while

$$
H_c^2(\mathbf A^1,\Lambda_n(1))=\Lambda_n.
$$

For $U=\mathbf G_m$, $g=0$ and $r=2$. The class of the oriented path between $0$ and $\infty$ generates $H_c^1$, while the Kummer class of $t$ generates $H^1(U,\Lambda_n(1))$. Their pairing is $1$ after compatible choices of orientation.

For $\mathbf P^1\setminus\{0,1,\infty\}$, the ordinary degree-one group has rank two. Residues may be written $(a,b,c)$ with $a+b+c=0$. Compact degree-one classes form the quotient $\Lambda_n^3/\Delta\Lambda_n$. The perfect pairing is the evaluation

$$
(\Lambda_n^3/\Delta\Lambda_n)
\times\ker(\Lambda_n^3\xrightarrow{\sum}\Lambda_n)
\longrightarrow\Lambda_n,
$$

which is well defined because every residue vector has sum zero.

A useful counterexample is a varying open family whose boundary points collide. The rank $2g+r-1$ then changes. Smoothness of the open total space does not preserve the pairing as a lisse family unless the compactification and boundary remain a relative normal-crossings pair. Compact support still obeys proper base change through the compactification, but ordinary boundary cohomology can jump.

## 8. Local duality on a curve

### 8.1 Purity at a closed point

Let $C$ be a smooth curve and $i:x\hookrightarrow C$ a closed point, with open complement $j:U\hookrightarrow C$. Purity says

$$
i^!\Lambda_n(1)\simeq\Lambda_n[-2].
$$

Consequently

$$
H_x^q(C,\Lambda_n(1))=0\quad(q\ne2),
\qquad
H_x^2(C,\Lambda_n(1))=\Lambda_n
$$

after passage to a geometric point. The generator is the local fundamental class. The localization boundary

$$
H^1(U,\Lambda_n(1))\longrightarrow
H_x^2(C,\Lambda_n(1))
$$

is the residue at $x$.

For a Kummer class represented by a rational function $f$, the residue is the valuation $v_x(f)$ modulo $\ell^n$. This follows by reducing to a uniformizer: a unit extends across $x$ and has zero boundary, while the Kummer cover obtained by adjoining an $\ell^n$th root of a uniformizer has boundary one. Multiplicativity then gives the valuation formula.

### 8.2 Residue and boundary pairings

The local class at a puncture is dual to the compact boundary class supported near that puncture. Globally, the relation that the sum of residues vanishes is dual to quotienting boundary points by the diagonal constant class. This is a model of a general principle: the dual of a localization triangle is another localization triangle with open and closed terms exchanged by extraordinary pullback.

If $D$ consists of closed points over a nonclosed field, the residue target is not simply one copy of $\Lambda_n$ for each visible equation. It is the induced sheaf from the residue field, followed by the finite-field trace. The global relation is

$$
\sum_{x\in D}\operatorname{cor}_{k(x)/k}
(\operatorname{res}_x\alpha)=0.
$$

After base change to a separable closure this becomes the sum over geometric punctures. The formulation with corestriction is the one compatible with Galois action.

### 8.3 Ramified coefficients

Let $\mathcal F$ be lisse on $U$ but possibly ramified at $D$. The stalks of $Rj_*\mathcal F$ at $x$ are inertia cohomology. If $I_x$ is the local geometric inertia group and $V$ a geometric stalk, then in the tame prime-to-characteristic range the boundary complex has

$$
\mathcal H^0=V^{I_x},
\qquad
\mathcal H^1=H^1(I_x,V),
$$

and no higher cohomology. These are cohomology groups of one derived local object, not the two terms of a canonically split complex.

Local Verdier duality pairs the invariant and coinvariant contributions for $V$ with those for $V^\vee(1)$. The precise maps are induced by evaluation and the local residue trace. This description proves compatibility with the global pairing by comparing the two localization triangles.

If wild inertia acts nontrivially, replacing it by a single tame generator is false. The derived inertia complex must be retained. Likewise, $j_*\mathcal F$ and $j_!\mathcal F$ coincide only when there is no boundary contribution. A lisse sheaf on $U$ need not extend lisse across $D$.

## 9. Relative duality

### 9.1 The relative theorem

Let $f:X\to S$ be separated of finite type in the bounded constructible prime-to-$\ell$ setting. For $K$ on $X$ and $L$ on $S$, relative duality is

$$
Rf_*R\mathcal Hom_X(K,f^!L)
\simeq
R\mathcal Hom_S(Rf_!K,L).
$$

To prove it, test both sides against a complex $M$ on $S$. Tensor--Hom adjunction turns a map into the left side into a map $f^*M\otimes K\to f^!L$. The defining adjunction for $f^!$, followed by the projection formula, turns this into a map $M\otimes Rf_!K\to L$. A second tensor--Hom adjunction gives the right side. Yoneda finishes the proof.

This theorem contains absolute duality by taking $S$ to be a point. It also explains why $Rf_*$ occurs on the left but $Rf_!$ on the right: ordinary sections of the dual object represent functionals on compactly supported sections.

There is a second, equivalent formulation that is often easier to use. Put $D_fK=R\mathcal Hom(K,f^!\Lambda_n)$. Then

$$
Rf_*D_fK\simeq
R\mathcal Hom(Rf_!K,\Lambda_n).
$$

If $f$ is proper, this says that the dual of a proper direct image is the proper direct image of the relative dual. If $f$ is smooth but not proper, it exchanges the ordinary direct image of the relative dual with the compactly supported direct image of the original. The latter exchange is the relative origin of the compact-versus-ordinary Poincaré pairing on each fiber.

### 9.2 Smooth proper curves

Let $f:C\to S$ be a smooth proper curve with geometrically connected fibers, and let $\mathcal F$ be finite locally free lisse. Smooth purity and properness give

$$
Rf_*\mathcal F^\vee(1)[2]
\simeq
R\mathcal Hom_S(Rf_*\mathcal F,\Lambda_n).
$$

Fiberwise this is curve duality. Proper base change identifies its stalks with the pairings already proved, so the map is an isomorphism globally. In particular,

$$
(R^if_*\mathcal F)^\vee
\cong
R^{2-i}f_*\mathcal F^\vee(1)
$$

when the direct-image sheaves are finite locally free. For constant coefficients, $R^1f_*\Lambda_n$ is symplectic with values in $\Lambda_n(-1)$, equivalently its twist-adjusted pairing has scalar values.

Every base change $S'\to S$ carries this form to the corresponding form for $C_{S'}$. Thus specialization in a smooth proper family preserves not merely rank but the full duality structure.

The relative statement also controls determinants. For constant coefficients, the alternating form on $R^1f_*\Lambda_n$ gives

$$
\bigwedge^{2g}R^1f_*\Lambda_n\cong\Lambda_n(-g).
$$

This identity is canonical once the trace orientation is fixed. It is preserved by monodromy and base change, so the determinant of the geometric first-cohomology representation is the $g$th inverse cyclotomic power with the present cohomological convention. For $g=1$, this is the familiar determinant of $H^1$; the dual Tate module carries the opposite twist. Confusing those two representations reverses the cyclotomic character.

### 9.3 Specialization of pairings

Suppose $S$ is a connected base over which $f$ is smooth proper. The relative trace is a morphism of lisse sheaves, and every specialization path carries it to the fiber trace. Hence

$$
\langle\operatorname{sp}(x),\operatorname{sp}(y)\rangle
=\operatorname{sp}(\langle x,y\rangle).
$$

The scalar sheaf is constant after the compensating twist, so the right side is the same scalar. Over a henselian trait, the generic Galois representation is unramified and inertia preserves the pairing.

If smoothness fails, proper base change still identifies fiber cohomology and constructs specialization, but it does not say the map is an isomorphism or preserve a constant-sheaf Poincaré form. The relative dualizing complex is the correct object; the next chapter describes the simplest failure.

## 10. Semistable fibers and the limits of ordinary Poincaré duality

### 10.1 The normalization complex

Let $C$ be a connected proper nodal curve over a separably closed field. Let $\nu:\widetilde C\to C$ be the normalization, let $N$ be the set of nodes, and let $B=\nu^{-1}(N)$ be the set of branches. There is an exact sequence

$$
0\longrightarrow\Lambda_n
\longrightarrow\nu_*\Lambda_n
\longrightarrow i_{N*}\mathcal Q
\longrightarrow0,
$$

where at each node $\mathcal Q$ is the quotient of the two branch values by the diagonal. Thus $\mathcal Q\cong\Lambda_n$ after ordering the branches, though the quotient description is canonical.

Taking cohomology yields

$$
0\longrightarrow H^1(\Gamma_C,\Lambda_n)
\longrightarrow H^1(C,\Lambda_n)
\longrightarrow H^1(\widetilde C,\Lambda_n)
\longrightarrow0,
$$

and

$$
H^2(C,\Lambda_n)\cong
\bigoplus_V\Lambda_n(-1),
$$

one top class for each irreducible component $V$. The graph sequence need not split canonically.

### 10.2 The dualizing complex of a nodal fiber

A node is not a cohomological manifold. Consequently the constant shifted sheaf $\Lambda_n(1)[2]$ is not, in general, the dualizing complex of $C$. Dualize the normalization triangle. Since $\widetilde C$ is a disjoint union of smooth proper curves and $N$ is zero-dimensional, one obtains a distinguished triangle

$$
i_{N*}\mathcal Q^\vee
\longrightarrow
\nu_*\Lambda_n(1)[2]
\longrightarrow
\omega_C^\bullet
\longrightarrow i_{N*}\mathcal Q^\vee[1].
$$

The first arrow is assembled from the two branch fundamental classes with opposite incidence signs. This triangle is the local correction at the nodes. It gives perfect duality

$$
R\Gamma(C,R\mathcal Hom(K,\omega_C^\bullet))
\simeq
R\operatorname{Hom}(R\Gamma(C,K),\Lambda_n)
$$

even though constant-coefficient Poincaré duality fails.

The irreducible rational curve with one node is decisive. Its $H^1$ has rank one. For odd $\ell$, an alternating self-pairing on a rank-one module is degenerate, so no perfect pairing $H^1(C,\Lambda_n)\times H^1(C,\Lambda_n(1))\to\Lambda_n$ can exist. The node term in $\omega_C^\bullet$ supplies the missing dual information.

### 10.3 Relative semistable duality

Let $f:\mathcal C\to T$ be a proper flat semistable curve over a strictly henselian trait, smooth over the generic point. Assume the total space is regular and the local equation at every node is

$$
xy=\pi
$$

after an étale localization. Relative duality still gives

$$
Rf_*R\mathcal Hom(K,f^!\Lambda_n)
\simeq
R\mathcal Hom(Rf_*K,\Lambda_n).
$$

On the smooth locus, $f^!\Lambda_n$ is $\Lambda_n(1)[2]$. In fact the lci orientation of the regular total space extends this identification across the node, but its exchange map to the intrinsic dualizing complex of the singular fiber contains the branch correction of Section 10.2. This is the exact point at which extraordinary pullback cannot be replaced by an unqualified constant twist after singular base change.

The extension across the node uses the regularity of the total space. Embed $\mathcal C$ locally as the hypersurface $xy-\pi=0$ in the smooth relative plane over $T$. The hypersurface immersion is regular of codimension one. Composing its purity isomorphism $(-1)[-2]$ with the plane orientation $(2)[4]$ produces the relative orientation $(1)[2]$. After restriction to the special fiber, however, the square is not cohomologically transverse at the node; the exchange morphism to the intrinsic fiber dualizing complex has the nonzero cone described by the two branches. Thus relative orientation and fiberwise singular duality are compatible without being identical.

One can prove the local assertion directly from $xy=\pi$. Remove the node, apply smooth purity on the punctured neighborhood, and use localization for the closed point. The punctured special fiber has two branches, whereas the punctured generic fiber has one annular cycle. The boundary map is the difference of the two branch residues. Its cone is rank one and is precisely the node correction.

### 10.4 What specialization preserves

Proper base change supplies specialization

$$
H^i(C_{\bar s},\Lambda_n)
\longrightarrow H^i(C_{\bar\eta},\Lambda_n),
$$

but it need not be an isomorphism. Relative duality makes specialization compatible with the maps of dualizing complexes. It does not turn the singular fiber's constant sheaf into a Poincaré self-dual object.

The normalization sequence separates component cohomology from graph cohomology. Each normalized component has its usual curve pairing. Incidence duality pairs vertices and edges in the graph complex. The remaining rank-one local term at each smoothed node accounts for the vanishing class on the generic fiber. This is the semistable duality package needed here. A systematic monodromy filtration and nearby-cycle spectral sequence belong to the next volume.

For a tree of smooth components, graph $H^1$ vanishes, but multiple top classes remain on the special fiber. For a polygon of projective lines, graph $H^1$ has rank one. Neither case has the same constant-sheaf duality as a smooth connected curve, although the dualizing-complex statement is perfect in both.

## 11. Exact torsion and adic duality

### 11.1 Perfectness at finite level

For a smooth $d$-fold and finite locally free lisse $\mathcal F_n$, finite-level duality says

$$
R\Gamma(X,\mathcal F_n^\vee(d))[2d]
\simeq
R\operatorname{Hom}_{\Lambda_n}
(R\Gamma_c(X,\mathcal F_n),\Lambda_n).
$$

The ring $\Lambda_n$ is injective as a module over itself. Therefore $\operatorname{Hom}(-,\Lambda_n)$ is exact on finite modules, and

$$
H^{2d-i}(X,\mathcal F_n^\vee(d))
\cong
\operatorname{Hom}_{\Lambda_n}
(H_c^i(X,\mathcal F_n),\Lambda_n).
$$

This is perfectness with exact $\ell^n$-torsion, not merely after tensoring with a field. It is compatible with reduction in $n$, but the transition maps on cohomology need not be surjective. The derived system, not a guessed tower of dual groups, carries the compatibility.

For a general constructible complex $K_n$, the correct statement uses $D_XK_n$. Replacing it by a shifted elementary dual is justified only when $K_n$ is lisse and finite locally free on a smooth scheme.

### 11.2 Passage to integral adic coefficients

Let $\mathcal F=(\mathcal F_n)$ be a normalized lisse $\Lambda$-system. The preceding volumes prove that the compact and ordinary cohomology complexes for the curves considered here are perfect over $\Lambda$. Finite-level duality maps are compatible with reduction, trace, and cup product. Taking the derived inverse limit gives

$$
R\Gamma(X,\mathcal F^\vee(d))[2d]
\simeq
R\operatorname{Hom}_{\Lambda}
(R\Gamma_c(X,\mathcal F),\Lambda).
$$

To justify the passage, use uniform amplitude and finiteness at every level. Images in each finite cohomology group stabilize, so the relevant systems are Mittag--Leffler. Perfectness permits derived Hom and tensor product to commute with reduction. Since a map between derived-complete perfect complexes is an isomorphism whenever all of its reductions are, the inverse-limit duality map is an isomorphism.

This argument does not assume that integral cohomology is torsion-free. It proves a perfect duality of complexes, which is the correct integral statement.

Reduction deserves a precise check. If $C_c=R\Gamma_c(X,\mathcal F)$ is perfect, then

$$
R\operatorname{Hom}_\Lambda(C_c,\Lambda)
\otimes^L_\Lambda\Lambda_n
\simeq
R\operatorname{Hom}_{\Lambda_n}
(C_c\otimes^L_\Lambda\Lambda_n,\Lambda_n).
$$

The left side is the reduction of the integral dual, while the right side is the finite-level dual. The isomorphism follows by replacing $C_c$ with a bounded complex of finite free modules and checking term by term. This calculation is the exact bridge between finite traces and the adic trace; it would fail for an uncontrolled inverse limit with no perfect representative.

### 11.3 Free pairings and torsion linking forms

Let $M^i=H_c^i(X,\mathcal F)$ and

$$
N^{2d-i}=H^{2d-i}(X,\mathcal F^\vee(d)).
$$

Taking cohomology of the derived dual yields the exact sequence

$$
0\longrightarrow
\operatorname{Ext}^1_\Lambda(M^{i+1},\Lambda)
\longrightarrow N^{2d-i}
\longrightarrow
\operatorname{Hom}_\Lambda(M^i,\Lambda)
\longrightarrow0.
$$

Because $\Lambda$ is a discrete valuation ring,

$$
\operatorname{Ext}^1_\Lambda(M,\Lambda)
\cong
\operatorname{Hom}(M_{\mathrm{tors}},E/\Lambda).
$$

Consequently the torsion-free quotients of $M^i$ and $N^{2d-i}$ pair perfectly over $\Lambda$, while there is a perfect linking pairing

$$
M^{i+1}_{\mathrm{tors}}\times
N^{2d-i}_{\mathrm{tors}}
\longrightarrow E/\Lambda.
$$

The degrees of a torsion pair sum to $2d+1$, not $2d$. This one-degree displacement is the integral universal-coefficient correction. Omitting it produces false claims whenever integral cohomology contains torsion.

The exact sequence need not split canonically. Choosing a splitting amounts to lifting homomorphisms through a torsion extension, and different choices differ by a map into the Ext term. What is canonical is the filtration of $N^{2d-i}$ by its torsion subgroup and the induced pairing on the free quotient. Thus determinant computations may use the perfect complex directly even when no degreewise decomposition exists.

At finite level, reduction can mix the two integral pieces. From multiplication by $\ell^n$ one obtains

$$
0\longrightarrow M^i/\ell^nM^i
\longrightarrow H_c^i(X,\mathcal F_n)
\longrightarrow M^{i+1}[\ell^n]
\longrightarrow0.
$$

Finite-level perfect duality pairs this entire extension with the corresponding complementary group. The left term accounts for reduction of the free and existing torsion classes; the right term accounts for torsion one degree higher. This is why finite-level perfection and integral linking duality contain exactly the same information when the tower is normalized.

If all relevant cohomology groups are torsion-free, the Ext term vanishes and ordinary complementary-degree integral perfection follows. Smooth proper curves with constant coefficients have this property; nonconstant coefficient systems require a separate torsion-freeness check.

### 11.4 Rational duality

Tensoring the perfect integral complexes with $E$ kills the Ext correction and gives

$$
H_c^i(X,\mathcal V)\times
H^{2d-i}(X,\mathcal V^\vee(d))
\longrightarrow E
$$

as a perfect pairing of finite-dimensional vector spaces. It is independent of the chosen stable lattice because any two lattices are commensurable and become equal after inverting $\ell$.

Rational perfection should not be used backward to infer integral perfection. A matrix with determinant $\ell$ is invertible over $E$ but not over $\Lambda$. The finite-level pairings and the linking form record exactly the information lost by rationalization.

## 12. Base change, Galois actions, and Frobenius

### 12.1 Base change for compact support and duality

Compactly supported direct image commutes with arbitrary base change in the finite constructible setting. Smooth purity is stable under arbitrary base change of a smooth map, so its trace and duality pairing are carried to the corresponding objects after base change. A proper lci orientation has the same compatibility for Tor-independent squares; in particular this covers flat and smooth changes of base and the correspondence squares used below. For a nontransverse square only the universal counit is automatic, and an excess term may alter an oriented pull-push formula.

For smooth proper curves, this follows on geometric stalks from absolute Poincaré duality and then globally because the direct images are lisse. For open curves, the compact side transports through a proper compactification; the ordinary side transports when the marked boundary and its local monodromy are controlled. At the adic level, uniform bounds and Mittag--Leffler permit the same conclusion after derived inverse limit.

For semistable curves, proper base change transports the relative duality morphism, but constant-sheaf purity on the singular fiber is not asserted. The normalization and node correction must be transported with it.

### 12.2 Galois equivariance

Let $X/k$ be smooth of dimension $d$. Every construction defining the pairing—pullback to $k^s$, cup product, evaluation, and trace—descends from $k$. Hence

$$
\langle\sigma x,\sigma y\rangle
=\langle x,y\rangle
$$

for $\sigma\in G_k$ when the second argument includes the twist $(d)$. Equivalently, the untwisted pairing has values in $\Lambda_n(-d)$ and is Galois equivariant there.

The statement remains true for continuous integral and rational cohomology. Continuity was established levelwise, and the trace maps form a compatible tower. A correspondence defined over $k$ commutes with $G_k$ because its pullback, cycle class, and proper pushforward do.

### 12.3 Arithmetic and geometric Frobenius

Suppose $k=\mathbf F_q$. Arithmetic Frobenius acts on $\Lambda_n(d)$ by $q^d$, and geometric Frobenius acts by $q^{-d}$. The twisted trace

$$
H_c^{2d}(\bar X,\Lambda_n(d))\to\Lambda_n
$$

is equivariant with trivial action on the target. Thus on untwisted top cohomology of a smooth proper geometrically connected $d$-fold, arithmetic Frobenius acts by $q^{-d}$ and geometric Frobenius by $q^d$.

If $F$ denotes geometric Frobenius, duality implies that the action on complementary cohomology is contragredient up to the twist. For a proper smooth $X$ and rational coefficients, eigenvalues $\alpha$ in degree $i$ pair with eigenvalues $q^d/\alpha$ in degree $2d-i$. This is a duality statement, not yet a purity or absolute-value theorem.

Over a local or number field at a place of good reduction, smooth proper base change identifies geometric Frobenius on the special fiber with the chosen unramified geometric Frobenius on generic cohomology. Using arithmetic Frobenius instead inverts every eigenvalue. This convention must be fixed before comparing characteristic polynomials.

## 13. Correspondences and cycle classes

### 13.1 Pull-push actions

Let $X$ and $Y$ be smooth over a field. A geometric correspondence

$$
X\xleftarrow{p}Z\xrightarrow{q}Y
$$

acts by pullback along $p$ and pushforward along $q$ whenever $q$ is proper and oriented in the required sense. If $p$ and $q$ are finite étale, the action is simply

$$
q_*p^*:H^*(X,\mathcal F)\longrightarrow H^*(Y,\mathcal F).
$$

For a regular lci cycle $\Gamma\subset X\times Y$ of the dimension making degree zero, the equivalent formula is

$$
\Gamma_*(x)=p_{Y*}
(p_X^*x\smile\operatorname{cl}(\Gamma)).
$$

The codimension of $\Gamma$, the twist of its class, and the relative dimension of $p_Y$ cancel. If they do not cancel, the correspondence changes degree and twist; suppressing that shift changes the operator. Divisorial cycles are also allowed through their Kummer classes. An arbitrary singular closure is not silently assigned a purity class; the curve correspondences used here have a regular pull-push presentation or a Cartier cycle representative.

Composition follows by forming the fiber product of correspondences, intersecting the pulled-back cycle classes, and applying the projection formula. Properness of the relevant projection ensures that the composite support remains proper.

If the intersection defining a composite is not transverse, one must use the refined intersection class. Its compatibility follows from deformation to the normal bundle. For a regular immersion $Z\hookrightarrow W$, use

$$
\operatorname{Bl}_{Z\times\{0\}}(W\times\mathbf A^1)
\setminus\widetilde{W\times\{0\}}.
$$

The complement of the special fiber is $W\times\mathbf G_m$ and the special fiber is $N_{Z/W}$. Localization, affine-line duality, and the residue-one normalization identify the generic fundamental class with the zero-section class on the special fiber. Apply this simultaneously to the two immersions being intersected. If their normal directions overlap, quotienting by the normal bundle of the actual fiber product leaves the excess bundle $E$, and the zero-section calculation multiplies its class by $c_{\mathrm{top}}(E)$. Here $c_{\mathrm{top}}(E)$ is defined by zero-section pullback followed by its Gysin map, so no separate Chern-class theorem is assumed. This proves the excess formula and hence associativity of the cohomological composite. In the curve case, the formula is the local intersection length. A set-theoretic fiber product can therefore give the wrong multiplicity even when it has the expected points.

The two asserted fibers can be checked without importing an intersection theorem. Locally, if $I$ is the ideal of $Z$, the displayed open blowup is described by the Rees algebra generated by $s$ and $I/s$. Inverting $s$ gives $\mathcal O_W[s,s^{-1}]$. Setting $s=0$ gives $\operatorname{gr}_I\mathcal O_W$, and regularity of the immersion identifies this graded algebra with $\operatorname{Sym}_{\mathcal O_Z}(I/I^2)$. Its spectrum is the normal bundle. The specialization and excess calculation are therefore reductions to the already proved coordinate zero-section calculation.

Base change commutes with the action when the correspondence and its proper support base-change correctly. For a finite étale correspondence this is immediate from pullback and finite trace. For a compactified open correspondence, it follows from proper base change on the closure and compatibility of the boundary triangle. If a closure acquires an extra vertical component, that component contributes a genuine cycle class; it may not be silently discarded.

### 13.2 Transpose and adjoint

Assume $X$ is smooth proper of pure dimension $d$, and let $\Gamma$ be a codimension-$d$ correspondence on $X\times X$. Let ${}^t\Gamma$ be obtained by exchanging the factors. Then

$$
\langle\Gamma_*x,y\rangle_X
=
\langle x,{}^t\Gamma_*y\rangle_X.
$$

Indeed, expand the left side using the cycle-class formula. Apply the projection formula to move $p_{2*}$ across cup product, switch the two factors, and integrate over $X\times X$. The resulting expression is the right side. All Koszul signs are those already present in graded commutativity; no additional correspondence sign appears.

For the graph of a finite map $f:X\to X$, this says that pullback and pushforward are adjoint. If $f$ has degree $m$, then $f_*f^*=m$. If $m$ is divisible by $\ell$, pullback need not be an integral isomorphism even if it is invertible rationally.

### 13.3 Cycle classes and projection

Cycle classes commute with flat pullback, proper pushforward, and exterior product. Let $f:X\to Y$ be a proper oriented map between smooth proper curves, and let $Z$ be a cycle for which the classes above are defined. Then

$$
f_*\operatorname{cl}_X(Z)
=\operatorname{cl}_Y(f_*Z).
$$

Test both sides against a complementary class. Projection reduces equality to the local degree formula at closed points, where the oriented finite trace is multiplication by residue degree and scheme-theoretic length. Perfect duality then identifies the classes. Flat pullback is proved on local Kummer symbols, exterior products by concatenating them, and localization extends these identities to properly supported classes on open smooth schemes.

The diagonal class recovers the identity correspondence. On a smooth proper curve, its Künneth components encode the unit, the identity on $H^1$, and the fundamental class.

### 13.4 Hecke-type correspondences

In the curve moduli spaces used later, the prime-to-level correspondences under consideration are finite étale on the open space and admit, after a compatible compactification or refinement, a regular lci pull-push model proper over both factors. Their actions therefore exist on ordinary and compactly supported cohomology, commute with the boundary map, and preserve interior cohomology

$$
H_!^i=\operatorname{im}(H_c^i\to H^i).
$$

Transpose correspondences are adjoint for Poincaré duality. If a polarization or an involution changes the geometric transpose into the conventional adjoint operator, that extra involution must be recorded; it is not supplied by duality automatically.

Because all maps descend to the ground field, correspondence actions commute with Galois and Frobenius. Because they are compatible modulo every $\ell^n$, they act on the integral perfect complex. Rational projectors may split eigenspaces after inverting $\ell$, but an integral splitting requires denominators prime to $\ell$.

## 14. The curve duality package

### 14.1 A theorem for later use

We collect the results in a form designed for repeated application.

**Étale duality theorem for curves.** Let $k$ be a field, let $\ell$ be invertible in $k$, and let $X/k$ be a separated finite-type scheme of dimension at most one. Work with bounded constructible $\ell$-primary coefficients.

1. Compactly supported cohomology is defined intrinsically by compactification, satisfies localization and composition, and commutes with base change at finite and adic levels under the established uniform finiteness hypotheses.
2. For every compactifiable map in the absolute or relative curve category, the functor $Rf_!$ has the extraordinary right adjoint $f^!$ on bounded constructible complexes. Its counit is functorial, transitive, and compatible with the valid base-change maps.
3. If $X$ is smooth of pure dimension $d$, then $a^!\Lambda_n=\Lambda_n(d)[2d]$. For finite locally free lisse $\mathcal F_n$, cup product and trace give perfect finite-level pairings

   $$
   H_c^i(\bar X,\mathcal F_n)\times
   H^{2d-i}(\bar X,\mathcal F_n^\vee(d))
   \longrightarrow\Lambda_n.
   $$

4. For a normalized lisse finite-free $\mathbf Z_\ell$-system, the inverse limit is a perfect duality of $\mathbf Z_\ell$-complexes. Free quotients pair in degrees summing to $2d$; torsion has a perfect $\mathbf Q_\ell/\mathbf Z_\ell$-valued linking pairing in degrees summing to $2d+1$. Rationalization gives perfect complementary-degree $\mathbf Q_\ell$-pairings. For a general constructible complex, the same statement uses its Verdier dual rather than an elementary sheaf dual.
5. Smooth proper relative curves satisfy relative duality fiberwise and over the base. Open smooth curve families satisfy the compact-versus-ordinary form when equipped with a controlled marked boundary.
6. A proper nodal curve is dual with respect to its dualizing complex. Its normalization, graph, and node correction describe the curve form; the constant shifted sheaf is not substituted on the singular fiber.
7. Traces and pairings commute with base change, Galois action, and the stated Frobenius normalization. Pull-push compatibility holds for finite étale maps, for oriented proper maps in the transverse or Tor-independent squares specified above, and for the resulting cycle classes and properly supported regular lci algebraic correspondences used here. Transpose correspondences are adjoint.

Every clause is derived from the constructions above. The finite-level theorem rests on compactification, purity, and finite biduality. The adic theorem rests on uniform amplitude, finite-level compatibility, and derived completeness. The relative statement rests on adjunction and the projection formula. The semistable statement rests on normalization and the two-branch local calculation.

### 14.2 A hypothesis audit

Before applying the package, one should make the following checks.

1. Is $\ell$ invertible everywhere? Smooth purity and the tame local calculations are prime-to-residue-characteristic statements.
2. Is the morphism separated and of finite type? These hypotheses supply compactification and a bounded constructible $Rf_!$.
3. Is the space smooth where $\Lambda(d)[2d]$ is used? At a node, use the dualizing complex instead.
4. Is a claimed pushforward the universal map from $f^!$, or has an orientation really supplied a map from ordinary coefficients?
5. For a nonproper space, does one side of the pairing have compact support?
6. For an open family, does the boundary remain relative normal crossings with controlled inertia?
7. At the integral level, are cohomology groups torsion-free? If not, use the derived statement and the linking pairing.
8. Does a correspondence have proper support over the target, and do its degree and codimension give the asserted shift and twist?
9. Is the transpose truly the desired arithmetic adjoint, or is a polarization or involution also involved?
10. Is Frobenius arithmetic or geometric? Top-degree eigenvalues and characteristic polynomials invert when the convention changes.
11. If an oriented lci map is base-changed, is the square Tor-independent, or has the excess class been included?

These are not cosmetic qualifications. Dropping proper support loses compactness, dropping smoothness loses the constant orientation, dropping derived limits loses torsion, and dropping the Tate twist destroys Galois equivariance.

### 14.3 Conclusion

Duality turns cohomology from a collection of groups into a geometry of adjoints. Compactification creates the functor that remembers support. Its extraordinary right adjoint creates the dualizing complex. Purity identifies that complex on smooth spaces, and the counit becomes integration. Cup product then converts integration into perfect pairings.

For curves, this structure explains the symplectic middle cohomology, the residue theorem, and the exact contribution of punctures. In families, it travels through base change and specialization. At a semistable node it does not conceal the singularity: normalization and the two branches contribute the correction that ordinary Poincaré duality lacks.

The integral theory retains more than its rational shadow. Finite-level pairings see exact torsion; the adic derived dual separates free duality from the one-degree-shifted linking form. Galois actions, Frobenius, cycle classes, and algebraic correspondences respect the same trace because all arise from one adjunction and one projection formula.

The resulting package is deliberately focused and complete for its purpose. Smooth curves carry canonical fundamental classes; proper and open versions are distinguished by support; nodal curve fibers carry their true dualizing complexes; and every trace, twist, shift, and adjoint remains visible under arithmetic descent. This is the duality framework on which nearby cycles, trace formulas, and the cohomological actions of later geometric correspondences can safely build.
