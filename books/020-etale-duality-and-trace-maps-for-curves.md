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
  - [14.2 A scope audit](#142-a-scope-audit)
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

Schemes are locally noetherian. Morphisms used for compact support are separated and of finite type and are assumed compactifiable in the sense of Book 19: they admit a factorization into an open immersion followed by a proper morphism. Book 19 proves compactifiability for quasi-projective morphisms over a noetherian base, and proves it for no wider class; Nagata's theorem is stated there but not proved and is not used. Every morphism to which compact support is applied in this volume is quasi-projective — curves and relative curves and their products, the affine and projective space projections used in the constructions, and the locally closed subschemes of these supplied by Book 19's stability lemma — so the quasi-projective theorem covers all of them. Quasi-projectivity is therefore part of the standing conventions whenever a compactification is invoked, so that no general compactification theorem is ever needed. The application range in this volume is absolute curves and relative morphisms with one-dimensional geometric fibers. Bases in the relative statements are excellent noetherian schemes, or limits obtained from them by the continuity arguments of that book. Fix a prime $\ell$ invertible on every scheme in sight, and write

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

with $j$ an open immersion and $\bar f$ proper. Book 19 constructs such a factorization whenever $f$ is quasi-projective over a noetherian base, by taking $\overline X$ to be the scheme-theoretic closure of $X$ in $\mathbf P^N_S$, and shows that the class of quasi-projective morphisms is stable under base change and under passage to locally closed subschemes of the source. That is the only existence statement we use. For $K\in D_c^b(X,\Lambda_n)$ define

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

It is the basic computational tool. Compactifying $\mathbf A^1$ inside $\mathbf P^1$ and removing the point at infinity gives, by the boundary computation carried out in full in Section 3.2,

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

The construction cannot be obtained merely by declaring a map smooth on a stratification: a singular map need not become smooth after stratifying only its source, and such a declaration would already presuppose purity. We instead prove one geometric duality theorem, for the affine line, whose proof uses neither a trace nor a purity statement, and then propagate it by steps that are formal: composition of adjunctions, a global factorization of a quasi-projective morphism through a smooth morphism, and uniqueness of adjoints. Nothing below reconstructs an object of a derived category from local pieces and a cocycle; that operation is not available and is not used.

**The residue at a relative divisor.** Every normalization in this book descends from a single local computation, which we isolate first. Let $q:P\to Y$ be smooth and separated of relative dimension one, with $\ell$ invertible on $Y$, let $\sigma:Y\to P$ be a section with image the relative divisor $Z$, and let $v:P\setminus Z\hookrightarrow P$ be the open complement. Fix a geometric point $\bar z$ of $Z$. The strict localization $P_{(\bar z)}$ is the spectrum of a strictly henselian ring in which $Z$ is cut out by one element that is a regular parameter transverse to the fibers. This is exactly Book 19's boundary situation with a single branch: its §4.2 identifies the punctured strict localization with a punctured strict henselian trait, and its §7.1 records that adjoining a parameter along $Z$ changes neither the inertia group nor its presentation matrix.

Let $R$ be the resulting strictly henselian discrete valuation ring — the localization of $P_{(\bar z)}$ at the generic point of $Z$ — and let $F$ be its fraction field. The residue field of $R$ is separably closed and $\ell$ is invertible, so Hensel's lemma makes every unit of $R$ an $\ell^n$th power. Therefore

$$
F^\times/(F^\times)^{\ell^n}
=\mathbf Z/\ell^n\mathbf Z,
$$

generated by the class of any uniformizer, and this group does not depend on which uniformizer is chosen. Since $F$ is a field its Picard group vanishes, so the Kummer sequence of Book 18 §3.4 collapses to

$$
H^0(F,\Lambda_n(1))=\Lambda_n(1),
\qquad
H^1(F,\Lambda_n(1))
=F^\times/(F^\times)^{\ell^n}
=\Lambda_n,
$$

with $H^q(F,\Lambda_n(1))=0$ for $q\geq2$, the vanishing because the prime-to-residue-characteristic quotient of $G_F$ is procyclic — this is Book 19's two-term tame complex $M\xrightarrow{\tau-1}M$, here with $M=\Lambda_n(1)$ and zero differential.

**Definition.** The _residue_ $\operatorname{res}:H^1(F,\Lambda_n(1))\to\Lambda_n$ is the isomorphism just displayed. On the Kummer class $\{f\}$ of $f\in F^\times$ it is the normalized valuation $v(f)$ modulo $\ell^n$.

The residue uses no choice of tame generator and no choice of uniformizer: changing the uniformizer multiplies it by a unit, and the Kummer class of a unit vanishes because units are $\ell^n$th powers. It is therefore compatible with every étale change of the pair $(P,Z)$ and with every base change $Y'\to Y$, since both preserve uniformizers and valuations. Sheafifying over $Z$, we record the statement in the form used below:

$$
\sigma^*R^0v_*\Lambda_n(1)=\Lambda_n(1),
\qquad
\sigma^*R^1v_*\Lambda_n(1)
\xrightarrow[\ \sim\ ]{\operatorname{res}}\Lambda_n,
\qquad
\sigma^*R^qv_*\Lambda_n(1)=0\ (q\geq2). \tag{3.1a}
$$

**The trace on the affine line.** Let $p:\mathbf A^1_S\to S$ with $S$ excellent noetherian and $\ell$ invertible on $S$. Compactify by $j:\mathbf A^1_S\hookrightarrow\mathbf P^1_S$, with $\bar p$ the projection and $\sigma_\infty:S\to\mathbf P^1_S$ the section at infinity, whose image is a relative divisor of the smooth relative curve $\mathbf P^1_S$ with complement $\mathbf A^1_S$. Applying $R\bar p_*$ to the localization triangle $j_!\Lambda_n(1)\to Rj_*\Lambda_n(1)\to\sigma_{\infty*}\sigma_\infty^*Rj_*\Lambda_n(1)$ on $\mathbf P^1_S$, and using $R\bar p_*\circ\sigma_{\infty*}=\operatorname{id}$, gives

$$
Rp_!\Lambda_n(1)
\longrightarrow
Rp_*\Lambda_n(1)
\longrightarrow
\sigma_\infty^*Rj_*\Lambda_n(1)
\longrightarrow.
$$

Book 19 §7.2 computes the middle term: over a strictly henselian base the cohomology of the affine line with constant prime-to-characteristic coefficients is the coefficient module in degree zero and nothing above, and Book 18 §12.2 identifies the stalks of $Rp_*$ with these strict-local groups, so $Rp_*\Lambda_n(1)=\Lambda_n(1)$. The right-hand term is (3.1a). The map between them is restriction of the constant section, hence the identity of $\Lambda_n(1)$ in degree zero. The triangle therefore leaves exactly one surviving group, and the residue at infinity gives a canonical isomorphism

$$
t_p:\ Rp_!\Lambda_n(1)[2]
\xrightarrow{\ \sim\ }\Lambda_n,
\qquad
R^qp_!\Lambda_n(1)=0\ (q\neq2). \tag{3.1b}
$$

Because every input is stable under base change and under étale localization, so is $t_p$. Combining $t_p$ with the projection formula of Section 6.2 — which is proved for $Rf_!$ from the open-immersion and proper cases and uses no adjoint — gives, for every $L\in D_c^b(S,\Lambda_n)$, an isomorphism

$$
\operatorname{Tr}_p:\
Rp_!\bigl(p^*L(1)[2]\bigr)
\simeq
\bigl(Rp_!\Lambda_n(1)[2]\bigr)\otimes^LL
\xrightarrow{\ \sim\ }L. \tag{3.1c}
$$

**Affine-line duality lemma.** Let $p:\mathbf A^1_S\to S$, with finite coefficients of order invertible on $S$. For $M\in D_c^b(\mathbf A^1_S,\Lambda_n)$ and $L\in D_c^b(S,\Lambda_n)$ the morphism $\theta_{M,L}$ constructed below is an isomorphism

$$
Rp_*R\mathcal Hom_{\mathbf A^1_S}
(M,p^*L(1)[2])
\xrightarrow{\ \sim\ }
R\mathcal Hom_S(Rp_!M,L). \tag{3.1}
$$

**Construction of $\theta$.** The map is defined once and for all, globally, so that functoriality in $M$ and in $L$ and compatibility with distinguished triangles in either variable are properties of the construction rather than assertions about a collection of local choices. There is a canonical natural transformation

$$
Rp_*R\mathcal Hom(M,N)
\longrightarrow
R\mathcal Hom_S(Rp_!M,Rp_!N),
$$

obtained as the adjoint of the composite

$$
Rp_!M\otimes^LRp_*R\mathcal Hom(M,N)
\to
Rp_!\bigl(M\otimes^Lp^*Rp_*R\mathcal Hom(M,N)\bigr)
\to
Rp_!\bigl(M\otimes^LR\mathcal Hom(M,N)\bigr)
\to Rp_!N,
$$

whose three arrows are the projection formula, the counit $p^*Rp_*\to\operatorname{id}$, and evaluation. Take $N=p^*L(1)[2]$ and follow with $\operatorname{Tr}_p$ of (3.1c). This is $\theta_{M,L}$. Each ingredient is natural in $M$ and $L$ and exact in each variable, so $\theta$ commutes with the localization triangles in $M$ and with triangles in $L$; that is precisely the compatibility that a piecewise verification cannot supply.

**Proof that $\theta$ is an isomorphism.** The argument is a dévissage in which every step either reduces the base or replaces the coefficients by constants; each geometric input is one of the strict-local presentations of Book 19.

_Reduction along the base._ Let $j_0:S_0\hookrightarrow S$ be a dense open with closed complement $b:S'\hookrightarrow S$. The triangle $b_*b^!L\to L\to Rj_{0*}j_0^*L$ splits the problem. For the closed part, $p^*b_*=b'_*p'^*$ for the base-changed $p'$ over $S'$, and $R\mathcal Hom(M,b'_*N)=b'_*R\mathcal Hom(b'^*M,N)$, while $Rp_!b'_*=b_*Rp'_!$; under these identifications $\theta_{M,b_*b^!L}$ is $b_*$ applied to $\theta$ over $S'$ with coefficients $b^!L$, which lies in $D^b_c(S')$ by Book 19 §3.3. For the open part, $p^*Rj_{0*}=Rj'_{0*}p_0^*$ by smooth base change (Book 19 §7.1), $R\mathcal Hom(M,Rj'_{0*}N)=Rj'_{0*}R\mathcal Hom(j'^*_0M,N)$, and $Rp_!$ commutes with restriction to an open; so $\theta_{M,Rj_{0*}j_0^*L}$ is $Rj_{0*}$ applied to $\theta$ over $S_0$. By the five lemma it therefore suffices to prove, for each fixed $M$ and $L$, that $\theta$ is an isomorphism over some dense open of $S$, together with noetherian induction on closed subschemes of $S$ for the complementary term.

_Reduction of the coefficients $L$ to $\Lambda_n$._ Work over a dense open of $S$ on which all cohomology sheaves of $L$ are lisse; such an open exists by constructibility. Truncation reduces $L$ to a lisse sheaf. A finite étale surjection $c:S''\to S$ makes it constant; $\theta$ commutes with $c^*$, because $Rp_!$, $Rp_*$, $R\mathcal Hom$ and the residue normalization all do, and $c^*$ is conservative. A constant sheaf with value a finite $\Lambda_n$-module has a finite filtration with graded pieces $\Lambda_n/\ell^i$, and each such piece sits in a triangle built from $\Lambda_n$. Hence it suffices to treat $L=\Lambda_n$, over a varying excellent noetherian base.

_Reduction of $M$._ Truncation reduces $M$ to a constructible sheaf. A constructibility stratification of $M$ has finitely many strata; each is either quasi-finite over $S$ after shrinking $S$, or contains a whole fiber of $p$ over a closed subscheme of $S$, in which case it lies over a proper closed subscheme of $S$ and is handled by the reduction along the base. So, after shrinking, $M$ sits in a triangle

$$
j_!\mathcal L\longrightarrow M\longrightarrow i_{C*}P\longrightarrow,
$$

with $i_C:C\hookrightarrow\mathbf A^1_S$ closed and finite over $S$, $j:U=\mathbf A^1_S\setminus C\hookrightarrow\mathbf A^1_S$, and $\mathcal L$ lisse on $U$. Shrinking $S$ once more, $C\to S$ becomes finite étale composed with a purely inseparable finite universal homeomorphism, and the latter induces an equivalence of prime-to-characteristic étale topoi, so it may be discarded. Since $\theta$ commutes with pullback along a finite étale surjection and such a pullback is conservative, a further finite étale base change lets us assume that $C$ is a disjoint union of $r$ pairwise disjoint sections $\sigma_1,\dots,\sigma_r$ of $\mathbf A^1_S$, each of them a relative divisor.

_The supported term._ Let $C=\sigma(S)$ be one such section and $h=p\circ i_C$, so $h$ is an isomorphism onto $S$ and $Rp_!i_{C*}P=h_*P$. Adjunction for the closed immersion turns the left side of (3.1) into $h_*R\mathcal Hom_C(P,i_C^!p^*\Lambda_n(1)[2])$. Now $i_C^!\Lambda_n(1)[2]$ is computed by the triangle $i_{C*}i_C^!\to\operatorname{id}\to Rj_*j^*$ together with (3.1a) applied to the relative divisor $C\subset\mathbf A^1_S$: the degree-zero terms cancel, the residue identifies the surviving term, and

$$
i_C^!\Lambda_n(1)[2]\simeq\Lambda_n,
$$

with the isomorphism given by the residue along $C$. Under it, $\theta_{i_{C*}P,\Lambda_n}$ is the identity of $R\mathcal Hom_C(P,\Lambda_n)$ transported by the isomorphism $h$; the normalization matches because the trace $t_p$ was itself defined by a residue and residues at the section and at infinity are computed by the same formula in the same local ring after an automorphism of $\mathbf P^1_S$ moving one to the other. Hence $\theta$ is an isomorphism on this term.

_The open term._ Here $M=j_!\mathcal L$ and $Rp_!j_!\mathcal L=Rg_!\mathcal L$ for $g=p\circ j:U\to S$, where $U$ is the complement in $\mathbf P^1_S$ of the $r+1$ pairwise disjoint sections $\sigma_1,\dots,\sigma_r,\sigma_\infty$. Adjunction for an open immersion identifies the left side of (3.1) as

$$
Rp_*R\mathcal Hom(j_!\mathcal L,\Lambda_n(1)[2])
=Rp_*Rj_*R\mathcal Hom(\mathcal L,\Lambda_n(1)[2])
=Rg_*\bigl(\mathcal L^\vee(1)\bigr)[2],
$$

so $\theta$ is a morphism $Rg_*(\mathcal L^\vee(1))[2]\to R\mathcal Hom_S(Rg_!\mathcal L,\Lambda_n)$.

This is exactly Book 19 §12.2's marked relative curve: the boundary is finite étale over $S$ of constant degree, so all the sheaves $R^kg_!\mathcal L$ and $R^kg_*\mathcal L^\vee(1)$ are lisse and commute with arbitrary base change. Since $\Lambda_n$ is self-injective, $\operatorname{Hom}_{\Lambda_n}(-,\Lambda_n)$ is exact on finite modules; hence $R\mathcal Hom_S(Rg_!\mathcal L,\Lambda_n)$ has lisse cohomology sheaves, namely the module duals of the $R^kg_!\mathcal L$, and the same holds for the other side. Both sides of $\theta$ are therefore complexes with lisse cohomology, and for such complexes a morphism is an isomorphism if and only if it is so on geometric stalks. This is the point at which geometric stalks may legitimately be used, and it is available only because the marked boundary is rigid; without that rigidity, ordinary cohomology of the open family is not computed by fiber cohomology, and the reduction would be false.

On a geometric fiber over $\bar s$, write $V$ for the stalk of $\mathcal L$ and $\pi$ for the prime-to-characteristic fundamental group of $U_{\bar s}=\mathbf P^1\setminus\{x_1,\dots,x_r,\infty\}$. Book 18 §7.2 gives the presentation: $\pi$ is free on the inertia generators $\gamma_1,\dots,\gamma_r$ at $x_1,\dots,x_r$, the inertia generator at infinity being $\gamma_\infty=(\gamma_1\cdots\gamma_r)^{-1}$. Cohomology of $\mathcal L$ is the two-term cochain complex

$$
C^\bullet(\mathcal L):\qquad
V\xrightarrow{\ d\ }V^{\oplus r},
\qquad
d(w)=\bigl((\gamma_k-1)w\bigr)_{k=1}^r,
$$

in degrees $0$ and $1$, with no higher cohomology; the vanishing above degree one is Book 18 §6.3 for an affine curve. The stalk of $Rj_*\mathcal L$ at $x\in D=\{x_1,\dots,x_r,\infty\}$ is the local tame complex of Book 19 §4.2,

$$
C_x^\bullet(\mathcal L):\qquad
V\xrightarrow{\ \gamma_x-1\ }V(-1),
$$

in degrees $0$ and $1$, the twist on the target being the identification of tame inertia with $\hat{\mathbf Z}(1)$ that also normalizes the residue in (3.1a); its cohomology is $V^{\gamma_x}$ and $V_{\gamma_x}(-1)$.

The restriction morphism $C^\bullet(\mathcal L)\to\bigoplus_{x\in D}C_x^\bullet(\mathcal L)$ is the diagonal in degree zero. In degree one it is the _residue_: a $1$-cocycle is the tuple $(w_1,\dots,w_r)$ recording $\gamma_k\mapsto w_k$, its component at $x_k$ is $w_k$, and its component at infinity is $-\sum_k(\gamma_1\cdots\gamma_{k-1})w_k$, because $\gamma_\infty$ is the inverse of the product and a cocycle on a product is the twisted sum of its values. For $\mathcal L$ constant this is $-\sum_kw_k$, the statement that residues sum to zero; and for $\mathcal L=\Lambda_n(1)$ it says that the Kummer class of $t-x_k$ has residue $1$ at $x_k$, residue $-1$ at infinity, and residue $0$ elsewhere, which is (3.1a) read on an explicit generator.

The localization triangle on $\mathbf P^1$ therefore reads

$$
R\Gamma_c(U_{\bar s},\mathcal L)
\longrightarrow
C^\bullet(\mathcal L)
\longrightarrow
\bigoplus_{x\in D}C_x^\bullet(\mathcal L)
\longrightarrow,
$$

and $R\Gamma_c$ is the shifted mapping fiber of a map of two-term complexes, hence has amplitude $[0,2]$. Its $H^0$ vanishes, since the degree-zero component of the restriction is injective; its $H^2$ is the cokernel of the residue; and reading the triangle gives the exact sequence

$$
0\to V^{\pi}\to\bigoplus_{x\in D}V^{\gamma_x}
\to H_c^1(U_{\bar s},\mathcal L)
\to H^1(U_{\bar s},\mathcal L)
\xrightarrow{(\operatorname{res}_x)}
\bigoplus_{x\in D}V_{\gamma_x}(-1)
\to H_c^2(U_{\bar s},\mathcal L)\to0
$$

with no compactly supported cohomology outside degrees $1$ and $2$.

Now dualize the presentation for $\mathcal L^\vee(1)$. Since $\Lambda_n$ is self-injective, $\operatorname{Hom}_{\Lambda_n}(-,\Lambda_n)$ is exact, and the transpose of $\gamma-1$ acting on $V^\vee$ is $\gamma^{-1}-1$ acting on $V$. Hence the dual of $C^\bullet(\mathcal L^\vee(1))[2]$ is the complex

$$
V(-1)^{\oplus r}
\xrightarrow{\ \delta\ }V(-1),
\qquad
\delta\bigl((w_k)_k\bigr)
=\sum_{k=1}^r(\gamma_k^{-1}-1)w_k,
$$

in degrees $1$ and $2$, and the dual of $C_x^\bullet(\mathcal L^\vee(1))[2]$ is $V(-1)\xrightarrow{\gamma_x^{-1}-1}V$ in degrees $1$ and $2$; dualizing also interchanges the two elementary identities $(V^\vee)_\gamma\cong(V^\gamma)^\vee$ and $(V^\vee)^\gamma\cong(V_\gamma)^\vee$, so that the dual of the local invariants for $\mathcal L^\vee(1)$ is exactly the local coinvariants for $\mathcal L$, and conversely. The dual of the restriction map is then the transposed incidence matrix, whose components are the sum over the punctures — that is, the residue read backwards.

Comparing the two, the dual of the ordinary localization sequence for $\mathcal L^\vee(1)$ is term for term the compactly supported sequence for $\mathcal L$ displayed above: the local terms match by the two module identities, the maps match because one incidence matrix is the transpose of the other, and the outer degrees match because both sequences begin at zero and end at zero. The morphism $\theta$ induces a map between these two sequences, because $\theta$ was constructed globally and therefore commutes with the localization triangles, and on the local terms it is the elementary module duality just described, an isomorphism. By the five lemma $\theta$ is an isomorphism on the middle terms as well. Finally the resulting pairing is cup product followed by the sum of residues, since $t_p$ was defined in (3.1b) as the residue at infinity and the sequence identifies $H_c^2$ with the cokernel of the residue map; for $\mathcal L=\Lambda_n$ this reads $H_c^2(U_{\bar s},\Lambda_n(1))=\Lambda_n$ with the sum of residues as the trace.

This proves $\theta$ on the open term, and with the supported term and the reductions above, proves (3.1). No trace theorem and no purity theorem has been used: the only geometric inputs are Book 18's tame presentation and affine-curve vanishing, Book 19's boundary presentation, marked-curve base change, and smooth-local calculation, and the Kummer computation of the residue. $\square$

**From the affine line to smooth morphisms.** Since $\mathbf A^N_S=\mathbf A^1_{\mathbf A^{N-1}_S}$, iterating (3.1) and composing the adjunctions shows that $Rp_!$ for $p:\mathbf A^N_S\to S$ has right adjoint $p^*(N)[2N]$. An étale morphism $w$ has $Rw_!=w_!$ with right adjoint $w^*$, so any $V$ étale over $\mathbf A^N_Y$ inherits the statement by composing adjunctions, and the residue normalization is unchanged because the residue is étale-local. Now let $q:W\to Y$ be smooth separated of pure relative dimension $N$. The trace $t_q:Rq_!\Lambda_n(N)[2N]\to\Lambda_n$ is defined without gluing any object: the sheaves $R^mq_!\Lambda_n(N)$ vanish for $m>2N$ and $R^{2N}q_!\Lambda_n(N)$ is canonically $\Lambda_n$ — both are statements about sheaves, verified on the charts and glued as sheaves, which is legitimate — so $t_q$ is the canonical truncation map onto $\mathcal H^0$. Repeating the construction of $\theta$ verbatim with $t_q$ in place of $t_p$ gives a global morphism

$$
\theta^q_{M,L}:\
Rq_*R\mathcal Hom_W(M,q^*L(N)[2N])
\longrightarrow
R\mathcal Hom_Y(Rq_!M,L).
$$

The class of $M\in D^b_c(W,\Lambda_n)$ for which $\theta^q$ is an isomorphism for all $L$ is triangulated and closed under summands. Every constructible sheaf on $W$ is a quotient of a finite direct sum of sheaves $u_!\Lambda_n$ with $u:V\to W$ étale and $V$ affine, and the $V$ may be chosen inside charts étale over $\mathbf A^N_Y$; the resulting resolution has uniformly bounded amplitude on both sides by Book 19 §3.4, so brutal truncation past that bound and the five lemma reduce the general case to $M=u_!\Lambda_n$. For such $M$, adjunction gives $R\mathcal Hom_W(u_!\Lambda_n,q^*L(N)[2N])=Ru_*(qu)^*L(N)[2N]$ and $Rq_!u_!=R(qu)_!$, so $\theta^q$ becomes the statement for $qu:V\to Y$, already proved. Hence for $q$ smooth of pure relative dimension $N$,

$$
q^!L=q^*L(N)[2N] \tag{3.2}
$$

is a right adjoint of $Rq_!$.

**The adjoint of a quasi-projective morphism.** For a closed immersion $i:Z\hookrightarrow P$ the exact functor $i_*$ has a right adjoint on sheaves, namely sections supported on $Z$ restricted to $Z$; deriving it gives $i^!$, defined globally with no choices. If $v:P\setminus Z\hookrightarrow P$, the triangle

$$
i_*i^!L\longrightarrow L\longrightarrow Rv_*v^*L\longrightarrow
$$

together with the constructibility and boundedness theorem for $Rv_*$ in Book 19 §3.3 shows that $i^!$ carries bounded constructible complexes to bounded constructible complexes in the required range.

Let now $f:X\to Y$ be quasi-projective, which by Section 1.2 is the standing convention wherever compact support is used. Then $f$ factors as an immersion into $\mathbf P^N_Y$ followed by the projection, and Book 19 §4.2 factors that immersion as a closed immersion into an open subscheme. Hence there is a _global_ factorization

$$
X\xrightarrow{\ i\ }W\xrightarrow{\ q\ }Y,
\qquad
W\subseteq\mathbf P^N_Y\ \text{open},
$$

with $i$ a closed immersion and $q$ smooth of pure relative dimension $N$, since an open subscheme of $\mathbf P^N_Y$ is smooth over $Y$ of that dimension. By the composition formula of Section 2.3, $Rf_!=Rq_!\circ i_*$, so composing the two adjunctions gives a right adjoint

$$
f^!L=i^!q^!L=i^!\bigl(q^*L(N)[2N]\bigr).
$$

This is a single globally defined functor. No cover is chosen, no local candidate is compared with another on an overlap, and no cocycle is invoked. If a second factorization is chosen, the two resulting functors are canonically isomorphic because both are right adjoint to the same functor $Rf_!$, and the comparison is unique and automatically compatible with all composites; that is the ordinary uniqueness of adjoints, applied to functors that already exist, not a gluing procedure applied to objects that do not.

Boundedness and constructibility of $f^!L$ follow from (3.2) and from the closed-immersion statement above. For an open immersion $j:U\hookrightarrow X$ we may take $W=U$, $N=0$, and $i$ the identity, so $j^!=j^*$. For a compactification $f=\bar f\circ j$, uniqueness of adjoints gives

$$
f^!=j^*\bar f^!,
$$

and independence of the compactification for the same reason. This proves existence of the adjunction on $D_c^b$ in the range used by curves and the relative curve families below. No assertion is made here for arbitrary unbounded or nonconstructible coefficients, nor for morphisms outside the quasi-projective class, where even $Rf_!$ has not been constructed.

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

is an isomorphism. Nilpotents do not change the étale site. Excellence and noetherian induction give a finite filtration by locally closed strata that are smooth over the base; in the curve range of this book, where the base is a field or a Dedekind scheme and the strata have dimension at most one, such a filtration exists because a reduced scheme of finite type has a dense open smooth locus over a suitable finite radicial extension of the base, and radicial changes do not alter the étale site. Embed such a stratum into a smooth affine scheme over the same base. It is then a smooth pair, so the purity calculation of Section 4.2 — whose proof is independent of biduality — identifies its dualizing complex; the assertion there is ordinary biduality for a finite module. Extension by zero and proper pushforward transport the result across strata, and the five lemma closes the induction through localization triangles.

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

with all other compactly supported direct images zero; this is (3.1b). Its chosen generator is the unique class having residue $1$ at infinity. If $t$ and $u$ are two étale coordinates, the ratio of their local Kummer symbols is a unit; a unit has zero residue. The two generators therefore agree. Iterating orients affine $d$-space. What is then glued is not an object of a derived category but the single sheaf $R^{2d}f_!\Lambda_n(d)$, together with the vanishing of $R^mf_!\Lambda_n(d)$ for $m>2d$; the trace is the resulting truncation map, exactly as in Section 3.2. This proves that the orientation is canonical rather than dependent on coordinates.

The twist is indispensable. Over a nonclosed field, a local parameter changes the Kummer generator by the cyclotomic character. The Tate twist cancels precisely that transformation.

### 4.2 Regular immersions and Gysin maps

Absolute purity is not supplied by the preceding books, and it is not proved here in the generality in which it is usually quoted. Unrestricted absolute purity — that $i^!\Lambda_n\simeq\Lambda_n(-c)[-2c]$ for every closed immersion of pure codimension $c$ between regular noetherian schemes with $\ell$ invertible — is a deep theorem whose proof is far outside the reach of the local presentations available to us, and no statement in this book depends on it. What we prove instead is a short list of cases, each with its residue normalization: a closed point of a regular one-dimensional scheme, a pair of schemes smooth over a common base, the pullback of such a divisor along a smooth morphism, and finally one case lying outside all three, the codimension-two computation at a node of a regular semistable model. That last case is the only one the later chapters need beyond the relative range. It is proved at the end of this section, and the proof is global rather than local: instead of presenting the punctured spectrum of the local ring, we exhibit one proper curve carrying such a node and read the answer off its cohomology.

**Purity at a closed point of a regular one-dimensional scheme.** Let $X$ be regular and of dimension one at a closed point $z$ — a smooth curve over a field, or a Dedekind scheme, or a trait — and let $i:z\hookrightarrow X$ be the reduced closed point. Then

$$
i^!\Lambda_n\simeq\Lambda_n(-1)[-2],
$$

canonically, the generator being the residue of the Kummer class of a uniformizer.

_Proof._ Both sides are computed on the strict localization $X_{(\bar z)}$, whose ring is a strictly henselian discrete valuation ring $R$ with fraction field $F$. The morphism $\operatorname{Spec}R\to\operatorname{Spec}R$ is proper, so Book 19 §5.1, applied to the identity, gives $R\Gamma(X_{(\bar z)},K)=K_{\bar z}$ for every bounded constructible $K$; in particular $H^0(X_{(\bar z)},\Lambda_n)=\Lambda_n$ and $H^q(X_{(\bar z)},\Lambda_n)=0$ for $q>0$. The punctured strict localization is $\operatorname{Spec}F$, whose cohomology was computed in Section 3.2: $\Lambda_n$ in degree zero, $\Lambda_n(-1)$ in degree one via the residue, and zero above. Feeding both into the localization sequence for cohomology supported at $z$ kills degrees $0$ and $1$, because $H^0(X_{(\bar z)})\to H^0(F)$ is the identity of $\Lambda_n$, and leaves

$$
H_z^2(X,\Lambda_n)\cong H^1(F,\Lambda_n)=\Lambda_n(-1),
\qquad
H_z^q(X,\Lambda_n)=0\ (q\neq2).
$$

The identification is the residue, hence independent of the uniformizer: multiplying it by a unit changes the Kummer class by the class of a unit, which vanishes in $F^\times/(F^\times)^{\ell^n}$ because units of $R$ are $\ell^n$th powers. $\square$

**Purity for smooth pairs.** Let $S$ be a scheme with $\ell$ invertible, let $X$ and $Z$ be smooth over $S$, and let $i:Z\hookrightarrow X$ be a closed immersion of pure codimension $c$. Then

$$
i^!\Lambda_n\simeq\Lambda_n(-c)[-2c],
$$

canonically and compatibly with étale localization on $X$ and with base change on $S$.

_Proof._ The construction of $i^!$ is local on $X$ for the étale topology, and an isomorphism of complexes on $Z$ may be checked étale-locally, so we may replace $X$ by an étale neighborhood. Near a point $z$ of $Z$, choose $t_1,\dots,t_c$ generating the ideal of $Z$ and $s_1,\dots,s_{d-c}$ restricting to étale coordinates for $Z$ over $S$, where $d$ is the relative dimension of $X$. The Jacobian criterion makes $e=(t,s):X\to\mathbf A^d_S$ étale near $z$, and $Z$ is the preimage of the linear subspace $\{t=0\}=\mathbf A^{d-c}_S$ because the $t_k$ generate the ideal. An étale morphism $e$ has $e^!=e^*$ and commutes with $i^!$, so we are reduced to the zero section of a projection

$$
\pi:\mathbf A^c_{Z}\longrightarrow Z,
\qquad
i_0:Z\longrightarrow\mathbf A^c_Z,
\qquad
\pi\circ i_0=\operatorname{id}_Z.
$$

Composition of adjoints and (3.2) give $i_0^!\pi^!=\operatorname{id}$ and $\pi^!=\pi^*(c)[2c]$, hence $i_0^!\bigl(\Lambda_n(c)[2c]\bigr)=\Lambda_n$. The Tate twist is an invertible sheaf pulled back from the base, and $i^!$ satisfies the projection formula against an invertible object, so this reads $i_0^!\Lambda_n=\Lambda_n(-c)[-2c]$.

For $c=1$ the isomorphism is canonical, independent of the chart: $Z$ is then a relative divisor of $X/S$, so (3.1a) applies and shows that $\mathcal H^2(i^!\Lambda_n)$ is generated by the residue of the Kummer class of a local equation $t$ of $Z$; replacing $t$ by $ut$ for a unit $u$ changes that class by the Kummer class of $u$, which extends across $Z$ and therefore has zero residue. For $c>1$ the canonical generator is the product of the $c$ codimension-one generators attached to a regular sequence cutting out $Z$, which is independent of the sequence by the same unit argument applied one step at a time. $\square$

**Smooth descent of purity.** Let $g:X\to T$ be smooth of pure relative dimension $d$, let $i_T:W\hookrightarrow T$ be a closed immersion of pure codimension one for which purity is known on $T$, and let $Z=g^{-1}(W)$ with $i_X:Z\hookrightarrow X$. Then $i_X^!\Lambda_n\simeq\Lambda_n(-1)[-2]$.

_Proof._ Write $g_W:Z\to W$ for the base change of $g$, which is smooth of the same relative dimension. From $g\circ i_X=i_T\circ g_W$ and the composition law for extraordinary inverse images,

$$
i_X^!g^!\Lambda_n=g_W^!i_T^!\Lambda_n
=g_W^!\bigl(\Lambda_n(-1)[-2]\bigr)
=\Lambda_n(-1)[-2](d)[2d].
$$

Since $g^!\Lambda_n=\Lambda_n(d)[2d]$ and $i_X^!$ commutes with the invertible twist and shift, this gives the assertion. $\square$

Taking $T$ regular of dimension one and $W$ a closed point, the last two results cover every purity statement used in this book except one. Closed points of smooth curves are the first theorem. Graphs of morphisms between smooth curves, diagonals, and the finite correspondences of Chapter 13 sit as codimension-one smooth pairs inside products of smooth curves. The horizontal divisors of a smooth relative curve over a Dedekind base are smooth pairs over that base, and the fibers of such a curve over closed points of the base are covered by smooth descent. That is the range in which the fundamental classes below are immediate: ambient schemes smooth over a regular base of dimension at most one, and closed subschemes that are either smooth over the same base or pullbacks of divisors on it.

Exactly one application in this book falls outside that range, and it is the interesting one. Let $\mathcal C\to T$ be a regular semistable model of a curve over a trait, and let $z$ be a node of its special fiber. The total space is regular of dimension two at $z$, but the morphism to the base is not smooth there, the point $z$ is not the pullback of a divisor on $T$, and no chart presents the situation as a pair of schemes smooth over a common base: the two branches of the special fiber cross at $z$, and their crossing is precisely where the relative structure degenerates. Both proofs above break for that reason. The chart argument for smooth pairs needs the closed subscheme to be cut out by coordinates of a smooth relative chart, and the descent argument needs a smooth morphism along which to transport a known purity statement. A direct local attack is not obviously available either: removing $z$ from a strict localization leaves the punctured spectrum of a two-dimensional strictly henselian regular local ring which is not smooth over the trait, so it is not a punctured relative divisor and the tame boundary presentations of Book 19 do not describe it.

What makes the case tractable is rigidity rather than local presentation. Over a fixed strictly henselian trait there is, up to isomorphism of strict local rings, only one semistable node; and cohomology with support in a closed point depends only on the strict local ring there. So the invariant to be computed is one number's worth of data attached to a single algebra, and it may be computed at whichever node is most convenient. There is a very convenient one. Blow up a rational point of the closed fiber of a projective line over the trait: the result is a regular proper surface whose special fiber is two projective lines crossing at one node, whose cohomology is known from the normalization sequence and proper base change, and whose complement of the node is smooth over the base with an affine special fiber and a projective generic fiber. Every group in the localization sequence of that surface is computable, and the sequence then computes the local term at the node.

**Purity at a semistable node.** Let $T=\operatorname{Spec}W$ be a strictly henselian trait with uniformizer $\pi$, residue field $\kappa$ and fraction field $K$, let $\ell$ be invertible on $T$, and let $\mathcal C\to T$ be flat and of finite type with $\mathcal C$ regular. Call a closed point $z\in\mathcal C$ a _semistable node_ if some étale neighborhood of $z$ in $\mathcal C$ admits an étale $T$-morphism to

$$
\mathcal N=\operatorname{Spec}W[x,y]/(xy-\pi)
$$

carrying $z$ to the origin. For such a point, with $i_z:z\hookrightarrow\mathcal C$ the reduced immersion,

$$
H_z^q(\mathcal C,\Lambda_n)=
\begin{cases}\Lambda_n(-2),&q=4,\\0,&q\neq4,\end{cases}
\tag{4.1}
$$

equivalently $i_z^!\Lambda_n\simeq\Lambda_n(-2)[-4]$. A node of a model over an arbitrary trait is covered after replacing the base by its strict localization, which is the only form in which the statement is used below.

_Proof._ **Reduction to one node.** Cohomology with support in a closed point is computed on the strict localization, $H_z^q(\mathcal C,\Lambda_n)\cong H_z^q(\mathcal C_{(z)},\Lambda_n)$, and passing to an étale neighborhood does not change the strict localization; note that the residue field of $z$ is $\kappa$, because an étale morphism to $\mathcal N$ makes it a finite separable extension of $\kappa$. The strict local ring at any semistable node of any such $\mathcal C$ is therefore the strict local ring of $\mathcal N$ at its origin, one and the same ring. So it suffices to prove (4.1) for a single semistable node of a single scheme over $T$.

**A convenient model.** Since $W$ is strictly henselian, $\kappa$ is separably closed. Let $z_0$ be the $\kappa$-rational point $u=0$ of the closed fiber of $\mathbf P^1_W=\operatorname{Proj}W[u_0,u_1]$, with $u$ the affine coordinate, and let

$$
f:\mathcal C_0=\operatorname{Bl}_{z_0}\mathbf P^1_W\longrightarrow T.
$$

By Book 12, Section 5, the blowup of a regular surface at a closed point is regular and projective and birational over it, with exceptional divisor a projective line over the residue field; so $\mathcal C_0$ is a regular integral surface, proper and flat over $T$. The blowup of the ideal $(u,\pi)$ has two charts. On the chart where $\pi$ generates the pulled-back ideal, $w=u/\pi$ is regular and the chart is $\operatorname{Spec}W[w]$, smooth over $T$. On the chart where $u$ generates, $v=\pi/u$ is regular and the chart is

$$
\operatorname{Spec}W[u][\pi/u]=\operatorname{Spec}W[u,v]/(uv-\pi)=\mathcal N,
$$

the surjection from $W[u,v]/(uv-\pi)$ being injective because that ring is a domain. So $\mathcal C_0$ contains the standard model as an open subscheme, with exceptional divisor $u=0$ and strict transform of the old closed fiber $v=0$. Thus $\mathcal C_0$ has exactly one point $z$ at which $u=v=0$, namely the origin of $\mathcal N$; it is a semistable node in the sense above, and $f$ is smooth of relative dimension one on $V=\mathcal C_0\setminus\{z\}$, since the Jacobian $(v,u)$ of $uv-\pi$ vanishes only at $z$ while the other chart and the untouched part of $\mathbf P^1_W$ are smooth. The special fiber $C_s$ is $uv=0$ on the chart $\mathcal N$ and is $\pi=0$ on the other chart; globally it is the reduced union of the exceptional divisor and the strict transform of the old closed fiber, crossing transversally at $z$ and meeting nowhere else. Both components are copies of $\mathbf P^1_\kappa$: the exceptional divisor by Book 12, and the strict transform because blowing up a regular point of a regular one-dimensional scheme changes nothing.

**The cohomology of the model.** Since $f$ is proper and $T$ is strictly henselian, the strict-local proper theorem of Book 19, Section 5.1, gives $R\Gamma(\mathcal C_0,\Lambda_n)\simeq R\Gamma(C_s,\Lambda_n)$. Let $\nu:\mathbf P^1_\kappa\sqcup\mathbf P^1_\kappa\to C_s$ be the normalization and use the exact sequence

$$
0\longrightarrow\Lambda_n\longrightarrow\nu_*\Lambda_n
\longrightarrow i_{z*}\Lambda_n\longrightarrow0
$$

whose last map takes the difference of the two branch values; this is the sequence that Section 10.1 will use systematically. Because $H^\bullet(\mathbf P^1_\kappa,\Lambda_n)=\Lambda_n,0,\Lambda_n(-1)$ in degrees $0,1,2$, and because $\Lambda_n^2\to\Lambda_n$ is surjective, the long exact sequence gives

$$
H^q(\mathcal C_0,\Lambda_n)=
\begin{cases}
\Lambda_n,&q=0,\\
\Lambda_n(-1)^2,&q=2,\\
0,&q=1\text{ or }q\geq3.
\end{cases}
\tag{4.2}
$$

**The cohomology of the complement.** Write $C_s^\circ=C_s\setminus\{z\}$, a disjoint union of two affine lines over $\kappa$, closed in $V$, with open complement the generic fiber $C_\eta=\mathbf P^1_K$. The morphism $V\to T$ is smooth and $C_s^\circ$ is the preimage of the closed point of $T$, so smooth descent of purity applies and

$$
H_{C_s^\circ}^q(V,\Lambda_n)=H^{q-2}(C_s^\circ,\Lambda_n(-1))=
\begin{cases}\Lambda_n(-1)^2,&q=2,\\0,&q\neq2,\end{cases}
$$

using the vanishing of positive-degree cohomology of the affine line with coefficients of order prime to the residue characteristic. For the generic fiber, $K$ is the fraction field of a strictly henselian discrete valuation ring, so by the local dimension theorem of Book 18 its $\ell$-cohomological dimension is one, its maximal pro-$\ell$ quotient is $\mathbf Z_\ell(1)$, and $\mu_{\ell^n}\subset K$. Hochschild--Serre applied to $\mathbf P^1_{\bar K}$, whose cohomology is $\Lambda_n,0,\Lambda_n(-1)$, gives

$$
H^q(C_\eta,\Lambda_n)=\Lambda_n,\ \Lambda_n(-1),\ \Lambda_n(-1),\ \Lambda_n(-2),\ 0
$$

in degrees $0,1,2,3$ and above. The class in degree one is the Kummer class of the uniformizer: $\operatorname{Pic}(\mathbf P^1_K)$ is torsion free and the units are $K^\times$, so $H^1(C_\eta,\mu_{\ell^n})=K^\times/(K^\times)^{\ell^n}=\Lambda_n\cdot[\pi]$. The boundary map into $H_{C_s^\circ}^2(V,\mu_{\ell^n})=H^0(C_s^\circ,\Lambda_n)$ is, by the residue normalization of the purity isomorphism, the vector of valuations along the two components of $C_s^\circ$. The special fiber is reduced, so both valuations of $\pi$ equal one and the boundary sends $[\pi]$ to $(1,1)$. That map is injective with cokernel $\Lambda_n(-1)$, so the localization sequence of the pair $(V,C_s^\circ)$ gives

$$
H^0(V)=\Lambda_n,\quad H^1(V)=0,\quad
0\to\Lambda_n(-1)\to H^2(V)\to\Lambda_n(-1)\to0,\quad
H^3(V)=\Lambda_n(-2),\quad H^q(V)=0\ (q\geq4).
\tag{4.3}
$$

In particular $H^2(V,\Lambda_n)$ has order $\ell^{2n}$, the same order as $H^2(\mathcal C_0,\Lambda_n)$.

**The punctured local scheme has no covers.** Let $A$ be the strict local ring of $\mathcal C_0$ at $z$, a two-dimensional regular strictly henselian local domain, and put $X_z=\operatorname{Spec}A$ and $U_z=X_z\setminus\{z\}$. Let $U'\to U_z$ be a connected finite étale cover and let $X'$ be the normalization of $X_z$ in the function field of $U'$. That normalization is finite because $A$ is a noetherian normal domain and the field extension is finite separable; $X'$ is normal, every component dominates $X_z$, and $X'\times_{X_z}U_z=U'$ because $U'$ is already normal. Every point of $X_z$ of codimension at most one lies in $U_z$, so $X'\to X_z$ is étale in codimension at most one, and all local rings of $X_z$ have dimension at most two. The purity lemma for surfaces of Book 17, Section 14.3, therefore makes $X'\to X_z$ finite étale, hence split because $A$ is strictly henselian, hence $U'\to U_z$ split. So $\pi_1(U_z)$ is trivial and $H^1(U_z,\Lambda_n)=0$, torsors under a constant finite group being classified by that fundamental group. Since $A$ is strictly henselian, $H^q(X_z,\Lambda_n)=0$ for $q>0$, exactly as in the proof of the first purity theorem above, and the localization sequence of the pair $(X_z,z)$ gives

$$
H_z^2(\mathcal C_0,\Lambda_n)\cong H_z^2(X_z,\Lambda_n)\cong H^1(U_z,\Lambda_n)=0.
$$

**Assembly.** Now read the localization sequence of the pair $(\mathcal C_0,z)$ with the values (4.2) and (4.3). The restriction $H^0(\mathcal C_0)\to H^0(V)$ is the identity of $\Lambda_n$ because both schemes are connected, so $H_z^0=H_z^1=0$. Next,

$$
0=H^2_z\longrightarrow H^2(\mathcal C_0,\Lambda_n)\longrightarrow H^2(V,\Lambda_n)
\longrightarrow H_z^3\longrightarrow H^3(\mathcal C_0,\Lambda_n)=0 .
$$

The vanishing of $H_z^2$ makes the first arrow injective; the two groups it joins both have order $\ell^{2n}$, so it is bijective and $H_z^3=0$. Finally

$$
0=H^3(\mathcal C_0,\Lambda_n)\longrightarrow H^3(V,\Lambda_n)=\Lambda_n(-2)
\longrightarrow H_z^4\longrightarrow H^4(\mathcal C_0,\Lambda_n)=0,
$$

so $H_z^4\cong\Lambda_n(-2)$, and $H_z^q\cong H^{q-1}(V,\Lambda_n)=0$ for $q\geq5$. This is (4.1) for the model, hence, by the reduction step, for every semistable node. $\square$

Three features of this proof deserve emphasis. First, no local presentation of the punctured spectrum is used; the local term is obtained by subtracting known global groups, which is legitimate because it is a local invariant to begin with. Second, the decisive step is the count in the assembly: the number of top classes on the special fiber, two, matches the order of $H^2$ of the complement, and it is the covering-theoretic input — no nontrivial covers of a punctured regular surface germ — that turns that numerical match into the vanishing of $H_z^3$. Third, the theorem is genuinely limited to nodes. It says nothing about an arbitrary closed point of an arbitrary regular two-dimensional scheme, because the rigidity used at the start is a property of nodes, and no such statement is used later.

Adjunction yields the Gysin map

$$
i_*:H^m(Z,\Lambda_n(r))
\longrightarrow
H^{m+2}_Z(X,\Lambda_n(r+1)).
$$

Composing with the map that forgets support gives the ordinary cycle-class pushforward. A closed point on a smooth curve therefore determines a class in $H^2(X,\Lambda_n(1))$.

### 4.3 Cycle classes and excess warnings

For an effective Cartier divisor $Z\subset X$ falling in the range of Section 4.2 — a closed point of a regular curve or trait, a smooth pair over the base, or a pullback of such a divisor along a smooth morphism — define

$$
\operatorname{cl}_X(Z)=i_*(1)\in H_Z^2(X,\Lambda_n(1)).
$$

Additivity extends the definition to cycles supported on such divisors. Proper pushforward and flat pullback commute with cycle classes. For transverse smooth pairs, cup product of fundamental classes equals the class of the intersection. The proof reduces étale-locally to concatenating regular sequences in the linear model of Section 4.2, where the product of Kummer boundary symbols is the symbol of the combined sequence.

Nontransverse intersections require an excess bundle and cannot be treated by naive multiplication of multiplicities. Likewise, a singular closed subscheme, and more generally a regular pair outside the proved range, is not covered by the displayed purity isomorphism. The cases used later avoid that leap. On a regular curve every codimension-one cycle is locally Cartier and is a closed point, so its class is defined by the Kummer boundary of a local equation and additivity. The graph of a map between smooth curves is a smooth divisor in their product, hence a smooth pair. Thus points and the finite curve correspondences considered here have cycle classes without invoking purity for an arbitrary regular or singular subscheme.

## 5. Trace maps

### 5.1 The universal counit

For every separated finite-type map in our category, adjunction supplies

$$
\operatorname{Tr}_f:Rf_!f^!K\longrightarrow K.
$$

This is the most general trace in the book. It is compatible with composition:

$$
\operatorname{Tr}_{g\circ f}=
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

For a finite locally free map that is not étale, the duality counit remains canonical, but a trace on ordinary constant coefficients requires an orientation. In the applications, $X$ and $Y$ are smooth over a common base and $f$ is finite lci—in particular this holds for a finite map between smooth curves, or for a finite flat correspondence explicitly presented as an lci map of smooth curves. Its graph is then a smooth pair inside $X\times Y$, so the purity of Section 4.2 applies. Factoring the graph as that regular immersion followed by a smooth projection gives

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

For a proper local-complete-intersection map $f:X\to Y$ between schemes smooth over a common base, a chosen factorization as a regular immersion followed by a smooth map supplies an orientation: the immersion is a smooth pair, so the purity of Section 4.2 applies, and composition with the smooth orientation produces the same formula with $d$ the virtual relative dimension. Until factorization independence is proved in Section 13.1, every use retains this chosen orientation data; no earlier argument needs to compare two choices. Section 13.1 uses deformation to the normal bundle and the excess identity to prove that the resulting orientation is independent of the factorization. For a proper lci map between regular schemes that are not smooth over a common base, the same factorization exists but its immersion need not be a smooth pair, and the purity isomorphism for such an immersion is not among the cases proved in Section 4.2; no map of that kind is oriented anywhere below.

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
\langle f^*x,y\rangle_C=
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

Let $C$ be a smooth curve and $i:x\hookrightarrow C$ a closed point, with open complement $j:U\hookrightarrow C$. This is the first case of Section 4.2: purity says

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

Throughout this section $f:\mathcal C\to T$ is a proper flat semistable curve over a strictly henselian trait, smooth over the generic point, with regular total space, and every node of its special fiber is a semistable node in the sense of Section 4.2: étale-locally the total space is the standard model $xy=\pi$ over the trait. That last condition delimits the class of models treated here rather than adding information about a given one: Book 16 computes the completed local equation of a node on a model with regular total space to be $xy=\pi$, the thickness being one exactly when the total space is regular, and we work with those models for which the same equation holds étale-locally. Relative duality gives

$$
Rf_*R\mathcal Hom(K,f^!\Lambda_n)
\simeq
R\mathcal Hom(Rf_*K,\Lambda_n).
$$

This is the formal statement of Section 9.1, which needs only the adjunction and the projection formula, and it holds whatever the object $f^!\Lambda_n$ turns out to be. So is the description of the intrinsic fiber dualizing complex in Section 10.2, which was obtained by dualizing the normalization triangle and uses only smooth purity on the normalized components and the zero-dimensionality of the node set.

What remains is to identify the object $f^!\Lambda_n$. On the smooth locus $\mathcal C^{\mathrm{sm}}$ the morphism $f$ is smooth of relative dimension one, so $f^!\Lambda_n$ restricts to $\Lambda_n(1)[2]$ there by (3.2). At a node the total space is still regular but $f$ is not smooth, and extending that orientation across the node is exactly a codimension-two purity question. It is the question settled at the end of Section 4.2, and the following theorem is its payoff.

**Relative orientation of a regular semistable model.** Let $f:\mathcal C\to T$ be as above. Then the orientation of the smooth locus extends uniquely to an isomorphism

$$
f^!\Lambda_n\simeq\Lambda_n(1)[2]
\tag{10.1}
$$

on all of $\mathcal C$, restricting on $\mathcal C^{\mathrm{sm}}$ to the orientation of Section 4.1.

_Proof._ Write $L=\Lambda_n(1)[2]$ and $G=f^!\Lambda_n$, let $N\subset\mathcal C$ be the finite reduced set of nodes with immersion $i:N\hookrightarrow\mathcal C$, and let $j:\mathcal C^{\mathrm{sm}}\hookrightarrow\mathcal C$ be the complementary open immersion. Smooth purity supplies the isomorphism $\alpha:j^*L\xrightarrow{\ \sim\ }j^*G$.

**The orientation extends, uniquely.** Each node is a closed point of the special fiber whose residue field is that of the closed point of $T$, so $f\circ i$ is a disjoint union of copies of the immersion of the closed point of the trait, and the first purity theorem of Section 4.2 together with the composition law gives

$$
i^!G=i^!f^!\Lambda_n=(f\circ i)^!\Lambda_n=\Lambda_n(-1)[-2].
\tag{10.2}
$$

Applying $\operatorname{RHom}(L,-)$ to the localization triangle $i_*i^!G\to G\to Rj_*j^*G$ and using the two adjunctions $\operatorname{Hom}(L,i_*Y)=\operatorname{Hom}(i^*L,Y)$ and $\operatorname{Hom}(L,Rj_*Y)=\operatorname{Hom}(j^*L,Y)$ gives an exact sequence

$$
\operatorname{Hom}(i^*L,i^!G)
\to\operatorname{Hom}_{\mathcal C}(L,G)
\to\operatorname{Hom}_{\mathcal C^{\mathrm{sm}}}(j^*L,j^*G)
\to\operatorname{Hom}(i^*L,i^!G[1]).
$$

Here $i^*L=\Lambda_n(1)[2]$ and $i^!G=\Lambda_n(-1)[-2]$ by (10.2), so the two outer groups are $H^{-4}(N,\Lambda_n(-2))$ and $H^{-3}(N,\Lambda_n(-2))$, both zero because $N$ is a disjoint union of spectra of fields and the degrees are negative. Restriction is therefore bijective, and $\alpha$ has a unique extension $\beta:L\to G$.

**The extension is an isomorphism.** Since $j^*\beta=\alpha$ is an isomorphism, the cone of $\beta$ is supported on $N$, hence equals $i_*M$ with $M=i^!\operatorname{cone}(\beta)=\operatorname{cone}(i^!\beta)$. By the node purity theorem of Section 4.2, $i^!L=(i^!\Lambda_n)(1)[2]=\Lambda_n(-2)[-4](1)[2]=\Lambda_n(-1)[-2]$, which by (10.2) is also $i^!G$. So $i^!\beta$ is multiplication by a scalar $c_z\in\Lambda_n$ at each node $z$, and $\beta$ is an isomorphism precisely when every $c_z$ is a unit.

The scalar is a local invariant. Everything used to construct $\beta$ — smooth purity, the extraordinary inverse image, and the uniqueness just proved — is compatible with étale localization, so the restriction of $\beta$ to an étale neighborhood is the corresponding unique extension there. The standard model $\mathcal N\to T$ is itself affine of finite type, hence quasi-projective, its only non-smooth point is the origin, and the extension argument just given applies to it verbatim, properness having played no role there. If $\varphi:\mathcal C'\to\mathcal N$ is an étale $T$-morphism from an étale neighborhood of $z$ to the standard model, then $\varphi^!=\varphi^*$ and $\varphi^*$ carries the extension for $\mathcal N\to T$ to the extension for $\mathcal C'\to T$. Hence $c_z$ agrees with the scalar attached to the origin of the standard model up to a unit — the only ambiguity being the choice of the two identifications with $\Lambda_n(-1)[-2]$, which cannot affect whether a scalar is a unit. So a single computation at the origin of $\mathcal N$ decides the matter for every node of every model over the given trait. We may therefore compute it on the blowup model $\mathcal C_0=\operatorname{Bl}_{z_0}\mathbf P^1_W$ of Section 4.2, which has exactly one node.

For that model, $M=\operatorname{cone}(c)$ with source and target $\Lambda_n(-1)$ placed in degree two, so $H^1(M)=\ker(c)$ and $H^2(M)=\operatorname{coker}(c)$. The node is a single rational point, so $R\Gamma(\mathcal C_0,i_*M)=M$. Taking global sections of the triangle $L\to G\to i_*M$ and using $H^1(\mathcal C_0,L)=H^3(\mathcal C_0,\Lambda_n(1))=0$ and $H^2(\mathcal C_0,L)=H^4(\mathcal C_0,\Lambda_n(1))=0$, which are the vanishing statements in (4.2) — twisting by $\Lambda_n(1)$ changes nothing, since $\mu_{\ell^n}$ is constant over the strictly henselian base — we get

$$
\ker(c)=H^1(M)\cong H^1(\mathcal C_0,f^!\Lambda_n).
$$

So it suffices to prove that the right-hand group vanishes, and for that we use relative duality itself. Applying the displayed duality isomorphism to $K=\Lambda_n$ gives $Rf_*f^!\Lambda_n\simeq R\mathcal Hom_T(Rf_*\Lambda_n,\Lambda_n)$, hence

$$
H^1(\mathcal C_0,f^!\Lambda_n)=\operatorname{Ext}^1_T(Rf_*\Lambda_n,\Lambda_n).
$$

The complex $R=Rf_*\Lambda_n$ on the trait has $\mathcal H^0(R)=\Lambda_n$ and $\mathcal H^1(R)=0$, and $\mathcal H^2(R)=R^2f_*\Lambda_n$ has stalk $\Lambda_n(-1)^2$ at the closed point and $\Lambda_n(-1)$ at a geometric generic point, by proper base change and the fiber computations of Section 4.2. The truncation triangle $\Lambda_n\to R\to\mathcal H^2(R)[-2]$ gives the exact sequence

$$
\operatorname{Ext}^3_T(\mathcal H^2(R),\Lambda_n)
\longrightarrow\operatorname{Ext}^1_T(R,\Lambda_n)
\longrightarrow\operatorname{Ext}^1_T(\Lambda_n,\Lambda_n)=H^1(T,\Lambda_n)=0,
$$

the last group vanishing because $T$ is strictly henselian. For the left group, write $i_s$ and $j_\eta$ for the closed and generic points of $T$ and use the sequence $0\to j_{\eta!}j_\eta^*\mathcal H^2(R)\to\mathcal H^2(R)\to i_{s*}i_s^*\mathcal H^2(R)\to0$. Adjunction and purity at the closed point of the trait give

$$
R\operatorname{Hom}_T(i_{s*}\Lambda_n(-1)^2,\Lambda_n)
=R\operatorname{Hom}(\Lambda_n(-1)^2,\Lambda_n(-1)[-2]),
$$

concentrated in degree two, while

$$
R\operatorname{Hom}_T(j_{\eta!}\Lambda_n(-1),\Lambda_n)
=R\Gamma(G_K,\Lambda_n(1))
$$

is concentrated in degrees zero and one, since $G_K$ has $\ell$-cohomological dimension one. The long exact sequence attached to the short exact sequence above has these two complexes as its outer terms, and both vanish in degree three, so $\operatorname{Ext}^3_T(\mathcal H^2(R),\Lambda_n)=0$ and therefore $\operatorname{Ext}^1_T(R,\Lambda_n)=0$. Hence $\ker(c)=0$; an injective endomorphism of $\Lambda_n$ is multiplication by a unit; so $c$ is a unit, $\beta$ is an isomorphism, and (10.1) holds. $\square$

Two remarks about the shape of this argument. The extension step is soft: it uses only that the nodes are closed points of the trait's closed fiber, so that the obstruction and ambiguity groups sit in negative degrees. The isomorphism step is where the geometry enters twice, once through the node purity theorem, which is what makes the two extraordinary pullbacks $i^!L$ and $i^!G$ agree at all, and once through the global duality count on a single model, which pins down the scalar comparing them. A local argument would have had to normalize that scalar by residues along the two branches; the global argument avoids the normalization by measuring the same scalar in a group that duality forces to vanish.

It is worth recording why the shortest-looking route does not replace this. Embed $\mathcal C$ locally as the hypersurface $xy-\pi=0$ in the smooth relative plane over $T$, a regular immersion of codimension one; composing a purity isomorphism $(-1)[-2]$ for that immersion with the plane orientation $(2)[4]$ would give the relative orientation $(1)[2]$ in one line. But the source of that immersion is not smooth over $T$, so the pair is not a smooth pair in the sense of Section 4.2 and its purity isomorphism is not one of the cases the chart argument proves. Likewise, removing the node and applying smooth purity on the punctured neighborhood leaves precisely the supported cohomology $H_z^\bullet(\mathcal C,\Lambda_n)$ to be computed, and the punctured strict localization at a node is not a punctured relative divisor, so the tame boundary presentations of Book 19 do not describe it. This is exactly why Section 4.2 computes that supported cohomology globally instead.

The orientation (10.1) does not make the singular fiber behave like a smooth one. The exchange map from the relative orientation to the intrinsic dualizing complex of the singular fiber is not an isomorphism: after restriction to the special fiber the square is not cohomologically transverse at the node, and the exchange morphism has the nonzero cone described by the two branches in Section 10.2. This is the exact point at which extraordinary pullback cannot be replaced by an unqualified constant twist after singular base change. The rank-one cone at each node is the node correction, and it survives even though the relative orientation is as simple as on a smooth family. Combining (10.1) with the duality isomorphism above, the semistable duality package now reads: the relative dualizing complex of a regular semistable model is the constant sheaf twisted once and shifted twice, the fiberwise dualizing complex is not, and the discrepancy between them is measured on each fiber by the branch triangle of Section 10.2.

### 10.4 What specialization preserves

Proper base change supplies specialization

$$
H^i(C_{\bar s},\Lambda_n)
\longrightarrow H^i(C_{\bar\eta},\Lambda_n),
$$

but it need not be an isomorphism. Relative duality makes specialization compatible with the maps of dualizing complexes. It does not turn the singular fiber's constant sheaf into a Poincaré self-dual object.

The normalization sequence separates component cohomology from graph cohomology. Each normalized component has its usual curve pairing. Incidence duality pairs vertices and edges in the graph complex. The remaining rank-one local term at each smoothed node accounts for the vanishing class on the generic fiber. This is the semistable duality package needed here. A systematic monodromy filtration and a nearby-cycle spectral sequence are not developed in this book; the statements above are the ones duality alone supplies.

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

For a cycle $\Gamma\subset X\times Y$ of the dimension making degree zero, whose components are smooth pairs in $X\times Y$ in the sense of Section 4.2 — which is the case for graphs, diagonals, and the finite correspondences between smooth curves used here — the equivalent formula is

$$
\Gamma_*(x)=p_{Y*}
(p_X^*x\smile\operatorname{cl}(\Gamma)).
$$

The codimension of $\Gamma$, the twist of its class, and the relative dimension of $p_Y$ cancel. If they do not cancel, the correspondence changes degree and twist; suppressing that shift changes the operator. Divisorial cycles on smooth curves are also allowed through their Kummer classes. Neither an arbitrary singular closure nor an arbitrary regular one is silently assigned a purity class; the curve correspondences used here have a smooth-pair pull-push presentation or a Cartier cycle representative supported at closed points of a smooth curve.

Composition follows by forming the fiber product of correspondences, intersecting the pulled-back cycle classes, and applying the projection formula. Properness of the relevant projection ensures that the composite support remains proper.

If the intersection defining a composite is not transverse, one must use the refined intersection class. Its compatibility follows from deformation to the normal bundle. For a smooth pair $Z\hookrightarrow W$ over the base, which is the only case used, take

$$
\operatorname{Bl}_{Z\times\{0\}}(W\times\mathbf A^1)
\setminus\widetilde{W\times\{0\}}.
$$

The complement of the special fiber is $W\times\mathbf G_m$ and the special fiber is $N_{Z/W}$. Localization, affine-line duality, and the residue-one normalization identify the generic fundamental class with the zero-section class on the special fiber. Apply this simultaneously to the two immersions being intersected. If their normal directions overlap, quotienting by the normal bundle of the actual fiber product leaves the excess bundle $E$, and the zero-section calculation multiplies its class by $c_{\mathrm{top}}(E)$. Here $c_{\mathrm{top}}(E)$ is defined by zero-section pullback followed by its Gysin map, so no separate Chern-class theorem is assumed. This proves the excess formula and hence associativity of the cohomological composite. In the curve case, the formula is the local intersection length. A set-theoretic fiber product can therefore give the wrong multiplicity even when it has the expected points.

Applied to the diagonal comparison of two smooth-pair factorizations of the same proper lci map, the same excess formula cancels the auxiliary normal bundle. This proves the factorization independence deferred in Section 5.4.

The two asserted fibers can be checked without importing an intersection theorem. Locally, if $I$ is the ideal of $Z$, the displayed open blowup is described by the Rees algebra generated by $s$ and $I/s$. Inverting $s$ gives $\mathcal O_W[s,s^{-1}]$. Setting $s=0$ gives $\operatorname{gr}_I\mathcal O_W$, and regularity of the immersion identifies this graded algebra with $\operatorname{Sym}_{\mathcal O_Z}(I/I^2)$. Its spectrum is the normal bundle, which is smooth over $Z$ and hence over the base, so the deformed pair is again a smooth pair and Section 4.2 applies throughout the degeneration. The specialization and excess calculation are therefore reductions to the already proved coordinate zero-section calculation.

Base change commutes with the action when the correspondence and its proper support base-change correctly. For a finite étale correspondence this is immediate from pullback and finite trace. For a compactified open correspondence, it follows from proper base change on the closure and compatibility of the boundary triangle. If a closure acquires an extra vertical component, that component contributes a genuine cycle class; it may not be silently discarded.

### 13.2 Transpose and adjoint

Assume $X$ is smooth proper of pure dimension $d$, and let $\Gamma$ be a codimension-$d$ correspondence on $X\times X$. Let ${}^t\Gamma$ be obtained by exchanging the factors. Then

$$
\langle\Gamma_*x,y\rangle_X=
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

The correspondences that arise from changing a level structure on a curve — two finite étale coverings of the same curve, glued along a common intermediate curve — all share one shape, and the duality package reacts only to that shape. It is therefore worth isolating the shape as a definition and proving theorems about every diagram that has it. The definition is a condition on a geometric object, checkable for any particular diagram one is handed; nothing below asserts that any particular curve carries such a diagram, and nothing below needs that.

**Definition.** Let $U$ be a smooth separated curve over $k$ with smooth compactification $\overline U$ and reduced boundary $D=\overline U\setminus U$. A _Hecke-type correspondence_ on $U$ is a diagram $U\xleftarrow{p}Z\xrightarrow{q}U$ satisfying the following four conditions.

1. _Étaleness in the interior._ $Z$ is a smooth separated curve over $k$ and both $p$ and $q$ are finite étale. In the motivating examples this is the prime-to-level condition; a diagram in which it fails at some primes is simply not a correspondence of this type there.
2. _A proper model._ There is a proper curve $\overline Z$ over $k$ containing $Z$ as a dense open, together with finite morphisms $\bar p,\bar q:\overline Z\to\overline U$ extending $p$ and $q$, such that $\overline Z$ is smooth and $\bar p^{-1}(D)=\bar q^{-1}(D)=\overline Z\setminus Z$ as sets. In particular the correspondence is proper over both factors and preserves the boundary.
3. _An oriented pull-push presentation._ The graph $(\bar p,\bar q):\overline Z\to\overline U\times\overline U$ is a closed immersion whose image is a smooth pair in $\overline U\times\overline U$ in the sense of Section 4.2, so that its fundamental class and the associated pull-push operator are defined by the purity proved there.
4. _Descent._ $Z$, $\overline Z$, $p$, $q$, and their extensions are defined over the ground field $k$, and over a finite field they commute with the chosen Frobenius.

The four conditions are not independent decorations. The first makes $p^*$ available with an unramified trace; the second is what lets pull-push act on compactly supported and on ordinary cohomology at the same time; the third is what places the correspondence inside the proved range of purity, so that its class is a genuine cohomology class rather than a formal symbol; the fourth is what makes the resulting operators arithmetic.

**Theorem.** Let $U\xleftarrow{p}Z\xrightarrow{q}U$ be a Hecke-type correspondence. Then the operator $q_*p^*$ acts on $H^*(U,\mathcal F)$ and on $H_c^*(U,\mathcal F)$ for every lisse $\mathcal F$ pulled back compatibly, the two actions are intertwined by the natural map $H_c^*\to H^*$ because $\bar p$ and $\bar q$ are proper and preserve the boundary, and consequently the operator preserves interior cohomology

$$
H_!^i=\operatorname{im}(H_c^i\to H^i).
$$

Moreover the transposed correspondence obtained by exchanging $p$ and $q$ acts as the adjoint of $q_*p^*$ for the Poincaré pairing of Section 7.3; the operators commute with the Galois action and with the chosen Frobenius; and they are compatible modulo every $\ell^n$, hence act on the integral perfect complex of Chapter 11.

_Proof._ Condition 1 makes $p$ finite étale, so $p^*$ is defined on both cohomologies and $p_*=Rp_!$ needs no orientation; condition 2 makes $\bar q$ proper, so $q_*$ is defined on compactly supported cohomology and, because $\bar q$ carries the boundary into the boundary, also on ordinary cohomology, compatibly with the natural map $H_c^\bullet\to H^\bullet$. The composite therefore preserves the image of that map, which is the displayed interior cohomology. Condition 3 places the graph in the range of Section 4.2, so Section 13.3 supplies its cycle class and Section 13.1 identifies the operator with the pull-push of that class; Section 13.2 then gives the transpose statement, since exchanging the two projections exchanges the class with its transpose and adjunction for the Poincaré pairing does the rest. Condition 4 gives the Galois and Frobenius statements by transport of structure, and integrality holds because every construction used was performed at finite level with $\Lambda_n$ coefficients and commutes with the reduction maps. $\square$

Two cautions accompany the theorem. First, if a polarization or an involution is needed to convert the geometric transpose into the conventional arithmetic adjoint operator, that extra involution is an additional datum that must be recorded; duality supplies the geometric transpose and nothing more. Second, rational projectors may split eigenspaces after inverting $\ell$, but an integral splitting requires denominators prime to $\ell$; the integral statement above is about an action, not about a decomposition.

## 14. The curve duality package

### 14.1 A theorem for later use

We collect the results in a form designed for repeated application.

**Étale duality theorem for curves.** Let $k$ be a field, let $\ell$ be invertible in $k$, and let $X/k$ be a separated finite-type scheme of dimension at most one. Work with bounded constructible $\ell$-primary coefficients.

1. Compactly supported cohomology is defined intrinsically by compactification, satisfies localization and composition, and commutes with base change at finite and adic levels within the uniform finiteness conditions established above.
2. For every quasi-projective map in the absolute or relative curve category, the functor $Rf_!$ has the extraordinary right adjoint $f^!$ on bounded constructible complexes, constructed globally from a single factorization into a closed immersion followed by a smooth morphism and independent of that factorization by uniqueness of adjoints. Its counit is functorial, transitive, and compatible with the valid base-change maps.
3. If $X$ is smooth of pure dimension $d$, then $a^!\Lambda_n=\Lambda_n(d)[2d]$. For finite locally free lisse $\mathcal F_n$, cup product and trace give perfect finite-level pairings

   $$
   H_c^i(\bar X,\mathcal F_n)\times
   H^{2d-i}(\bar X,\mathcal F_n^\vee(d))
   \longrightarrow\Lambda_n.
   $$

4. For a normalized lisse finite-free $\mathbf Z_\ell$-system, the inverse limit is a perfect duality of $\mathbf Z_\ell$-complexes. Free quotients pair in degrees summing to $2d$; torsion has a perfect $\mathbf Q_\ell/\mathbf Z_\ell$-valued linking pairing in degrees summing to $2d+1$. Rationalization gives perfect complementary-degree $\mathbf Q_\ell$-pairings. For a general constructible complex, the same statement uses its Verdier dual rather than an elementary sheaf dual.
5. Smooth proper relative curves satisfy relative duality fiberwise and over the base. Open smooth curve families satisfy the compact-versus-ordinary form when equipped with a controlled marked boundary.
6. A proper nodal curve is dual with respect to its dualizing complex. Its normalization, graph, and node correction describe the curve form; the constant shifted sheaf is not substituted on the singular fiber. For a regular semistable model over a strictly henselian trait whose nodes are the standard ones, the _relative_ dualizing complex is $\Lambda_n(1)[2]$, by the orientation theorem of Section 10.3; the dualizing complex of the singular fiber is still not the constant shifted sheaf, and the discrepancy between the two is the branch cone at each node.
7. Purity for a closed immersion of pure codimension $c$ is proved, with the residue normalization, for a closed point of a regular one-dimensional scheme, for a smooth pair over the base, and for the pullback of such a divisor along a smooth morphism. Beyond that range one further case is proved: the codimension-two computation $i_z^!\Lambda_n\simeq\Lambda_n(-2)[-4]$ at a semistable node, in Section 4.2. Purity for a general regular pair is neither proved nor used.
8. Traces and pairings commute with base change, Galois action, and the stated Frobenius normalization. Pull-push compatibility holds for finite étale maps, for oriented proper maps in the transverse or Tor-independent squares specified above, and for the resulting cycle classes and properly supported smooth-pair algebraic correspondences used here. Transpose correspondences are adjoint. The Hecke-type correspondences defined in Section 13.4 satisfy these conditions, by the theorem proved there.

Every clause is derived from the constructions above. The finite-level theorem rests on compactification, the affine-line duality lemma, purity in the proved range, and finite biduality. The adic theorem rests on uniform amplitude, finite-level compatibility, and derived completeness. The relative statement rests on adjunction and the projection formula. The semistable statement rests on normalization, the two-branch local calculation, and the node purity computation of Section 4.2 that orients the model.

### 14.2 A scope audit

Before applying the package, one should make the following checks.

1. Is $\ell$ invertible everywhere? Smooth purity and the tame local calculations are prime-to-residue-characteristic statements.
2. Is the morphism separated, of finite type, and quasi-projective? The first two supply finiteness; the third is what Book 19 actually uses to produce a compactification, and it is also what produces the global factorization behind $f^!$.
3. Is the space smooth where $\Lambda(d)[2d]$ is used? At a node, use the dualizing complex instead.
   3a. Is a purity statement being applied to a closed immersion that is a smooth pair, a closed point of a regular curve or trait, a pullback of one of these along a smooth morphism, or a semistable node? Those are the proved cases; a regular pair of any other kind is outside the range of Section 4.2.
   3b. Is a relative orientation being extended across a node of a regular model? Section 10.3 does that, and only for models whose nodes are the standard ones over a trait.
4. Is a claimed pushforward the universal map from $f^!$, or has an orientation really supplied a map from ordinary coefficients?
5. For a nonproper space, does one side of the pairing have compact support?
6. For an open family, does the boundary remain relative normal crossings with controlled inertia?
7. At the integral level, are cohomology groups torsion-free? If not, use the derived statement and the linking pairing.
8. Does a correspondence have proper support over the target, and do its degree and codimension give the asserted shift and twist?
9. Is the transpose truly the desired arithmetic adjoint, or is a polarization or involution also involved? For a diagram claimed to be a Hecke-type correspondence, have the four conditions of the definition in Section 13.4 been checked for the curve at hand?
10. Is Frobenius arithmetic or geometric? Top-degree eigenvalues and characteristic polynomials invert when the convention changes.
11. If an oriented lci map is base-changed, is the square Tor-independent, or has the excess class been included?

These are not cosmetic qualifications. Dropping proper support loses compactness, dropping smoothness loses the constant orientation, dropping derived limits loses torsion, and dropping the Tate twist destroys Galois equivariance.

### 14.3 Conclusion

Duality turns cohomology from a collection of groups into a geometry of adjoints. Compactification creates the functor that remembers support. Its extraordinary right adjoint creates the dualizing complex. Purity identifies that complex on smooth spaces, and the counit becomes integration. Cup product then converts integration into perfect pairings.

For curves, this structure explains the symplectic middle cohomology, the residue theorem, and the exact contribution of punctures. In families, it travels through base change and specialization. At a semistable node it does not conceal the singularity: normalization and the two branches contribute the correction that ordinary Poincaré duality lacks.

The integral theory retains more than its rational shadow. Finite-level pairings see exact torsion; the adic derived dual separates free duality from the one-degree-shifted linking form. Galois actions, Frobenius, cycle classes, and algebraic correspondences respect the same trace because all arise from one adjunction and one projection formula.

The resulting package is deliberately focused. Smooth curves carry canonical fundamental classes; proper and open versions are distinguished by support; nodal curve fibers carry their true dualizing complexes; and every trace, twist, shift, and adjoint remains visible under arithmetic descent. It is also explicit about its range. General absolute purity is not proved and is nowhere used; what is proved is purity for the one-dimensional, smooth-pair, and smooth-descent cases, together with the single codimension-two computation at a semistable node that the semistable chapter needs. That computation was obtained not by presenting the punctured spectrum of the node — an object the local techniques of Books 18 and 19 do not reach — but by exploiting the rigidity of nodes and reading the answer off one blown-up projective line over the trait, and it is what makes the relative orientation of a regular semistable model a theorem rather than a wish. Hecke-type correspondences enter as a defined class of diagrams, with the properties of the class proved for every diagram in it; whether a given moduli curve carries such a diagram is a question about geometry constructed elsewhere, not a gap in the duality theory. Everything here, including the affine-line duality lemma on which $f^!$ rests and the global construction of $f^!$ itself, is proved from the preceding volumes. This is the duality framework on which nearby cycles, trace formulas, and the cohomological actions of later geometric correspondences can build.
