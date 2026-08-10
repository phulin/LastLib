# Minimal Modularity Lifting

## Contents

1. [Scope, imports, and logical order](#1-scope-imports-and-logical-order)
   - [1.1 The claim](#11-the-claim)
   - [1.2 Imported results and new infrastructure](#12-imported-results-and-new-infrastructure)
   - [1.3 The clean rational datum](#13-the-clean-rational-datum)
   - [1.4 Exclusions](#14-exclusions)
   - [1.5 The noncircular route](#15-the-noncircular-route)
2. [The global and local deformation problem](#2-the-global-and-local-deformation-problem)
   - [2.1 Coefficients, determinant, and Frobenius](#21-coefficients-determinant-and-frobenius)
   - [2.2 Unramified minimality](#22-unramified-minimality)
   - [2.3 Nonzero Steinberg minimality](#23-nonzero-steinberg-minimality)
   - [2.4 Finite flatness at the coefficient prime](#24-finite-flatness-at-the-coefficient-prime)
   - [2.5 Oddness and the real place](#25-oddness-and-the-real-place)
   - [2.6 The global ring and Selmer structures](#26-the-global-ring-and-selmer-structures)
3. [Integral quaternionic Taylor--Wiles control](#3-integral-quaternionic-taylor--wiles-control)
   - [3.1 Definite class-set modules](#31-definite-class-set-modules)
   - [3.2 The automorphic control theorem](#32-the-automorphic-control-theorem)
   - [3.3 Why the theorem is integral](#33-why-the-theorem-is-integral)
   - [3.4 Proof architecture](#34-proof-architecture)
4. [Integral definite-to-curve Hecke reciprocity](#4-integral-definite-to-curve-hecke-reciprocity)
   - [4.1 Why generic Jacquet--Langlands is insufficient](#41-why-generic-jacquet--langlands-is-insufficient)
   - [4.2 The reciprocity theorem](#42-the-reciprocity-theorem)
   - [4.3 Construction and proof architecture](#43-construction-and-proof-architecture)
5. [The Hecke representation and the map from deformation to Hecke](#5-the-hecke-representation-and-the-map-from-deformation-to-hecke)
   - [5.1 The minimal Hecke algebra](#51-the-minimal-hecke-algebra)
   - [5.2 Local verification of the Hecke family](#52-local-verification-of-the-hecke-family)
   - [5.3 The canonical surjection](#53-the-canonical-surjection)
6. [Taylor--Wiles primes and auxiliary deformation rings](#6-taylor--wiles-primes-and-auxiliary-deformation-rings)
   - [6.1 Killing dual Selmer](#61-killing-dual-selmer)
   - [6.2 Ordered roots and diamond groups](#62-ordered-roots-and-diamond-groups)
   - [6.3 Local auxiliary rings](#63-local-auxiliary-rings)
   - [6.4 Global auxiliary rings and augmentation](#64-global-auxiliary-rings-and-augmentation)
7. [Full auxiliary modules and diamond freeness](#7-full-auxiliary-modules-and-diamond-freeness)
   - [7.1 Lower, Iwahori, and deep levels](#71-lower-iwahori-and-deep-levels)
   - [7.2 Free diamond action](#72-free-diamond-action)
   - [7.3 Integral pairings at deep level](#73-integral-pairings-at-deep-level)
8. [Exact degeneracy and full Iwahori oldness](#8-exact-degeneracy-and-full-iwahori-oldness)
   - [8.1 Degeneracy maps and trace adjoints](#81-degeneracy-maps-and-trace-adjoints)
   - [8.2 The Gram matrix](#82-the-gram-matrix)
   - [8.3 Saturation and vanishing of the new quotient](#83-saturation-and-vanishing-of-the-new-quotient)
   - [8.4 The Iwahori operator after oldness](#84-the-iwahori-operator-after-oldness)
9. [Primary and companion branches](#9-primary-and-companion-branches)
   - [9.1 Hensel projectors and the primary old line](#91-hensel-projectors-and-the-primary-old-line)
   - [9.2 The deep primary and companion blocks](#92-the-deep-primary-and-companion-blocks)
   - [9.3 Adjointness, not self-adjointness](#93-adjointness-not-self-adjointness)
   - [9.4 Augmentation and ordered Galois control](#94-augmentation-and-ordered-galois-control)
10. [The Taylor--Wiles axiom ledger](#10-the-taylor--wiles-axiom-ledger)
    - [10.1 The paired finite-level system](#101-the-paired-finite-level-system)
    - [10.2 Verification of the axioms](#102-verification-of-the-axioms)
    - [10.3 What has not yet been proved](#103-what-has-not-yet-been-proved)
11. [The framed ledger and absolute patching](#11-the-framed-ledger-and-absolute-patching)
    - [11.1 The exact global generator formula](#111-the-exact-global-generator-formula)
    - [11.2 Local framed dimensions](#112-local-framed-dimensions)
    - [11.3 Gauge variables and the framed presentation](#113-gauge-variables-and-the-framed-presentation)
    - [11.4 Exact frame removal and the square presentation](#114-exact-frame-removal-and-the-square-presentation)
    - [11.5 The exact unframed auxiliary count](#115-the-exact-unframed-auxiliary-count)
    - [11.6 Patching from the minimal absolute source](#116-patching-from-the-minimal-absolute-source)
    - [11.7 Regularity, freeness, and faithful descent](#117-regularity-freeness-and-faithful-descent)
12. [Post-comparison cotangent and congruence theory](#12-post-comparison-cotangent-and-congruence-theory)
    - [12.1 The common complete-intersection presentation](#121-the-common-complete-intersection-presentation)
    - [12.2 The deformation cotangent complex](#122-the-deformation-cotangent-complex)
    - [12.3 The automorphic congruence complex](#123-the-automorphic-congruence-complex)
    - [12.4 The conormal--dualizing comparison](#124-the-conormal--dualizing-comparison)
    - [12.5 Integral normalization and the global unit](#125-integral-normalization-and-the-global-unit)
    - [12.6 The Fitting--congruence equality](#126-the-fitting--congruence-equality)
13. [The numerical audit and structural consequences](#13-the-numerical-audit-and-structural-consequences)
    - [13.1 The specialization square](#131-the-specialization-square)
    - [13.2 The Wiles--Lenstra criterion as an audit](#132-the-wiles--lenstra-criterion-as-an-audit)
    - [13.3 Consequences proved only after equality](#133-consequences-proved-only-after-equality)
14. [Modularity extraction and the reusable theorem](#14-modularity-extraction-and-the-reusable-theorem)
    - [14.1 From a minimal point to an eigenform](#141-from-a-minimal-point-to-an-eigenform)
    - [14.2 Equality of Galois representations](#142-equality-of-galois-representations)
    - [14.3 Minimal modularity lifting over the rationals](#143-minimal-modularity-lifting-over-the-rationals)
15. [The elliptic-curve theorem](#15-the-elliptic-curve-theorem)
    - [15.1 Translating the hypotheses](#151-translating-the-hypotheses)
    - [15.2 The conclusion](#152-the-conclusion)
16. [What changes over a totally real field](#16-what-changes-over-a-totally-real-field)
    - [16.1 The parts that formally persist](#161-the-parts-that-formally-persist)
    - [16.2 The new global and automorphic work](#162-the-new-global-and-automorphic-work)
17. [Failure modes and diagnostic boundaries](#17-failure-modes-and-diagnostic-boundaries)
    - [17.1 Local failures](#171-local-failures)
    - [17.2 Automorphic and integral failures](#172-automorphic-and-integral-failures)
    - [17.3 Numerical and logical failures](#173-numerical-and-logical-failures)
18. [The interface with nonminimal lifting](#18-the-interface-with-nonminimal-lifting)
    - [18.1 What the minimal theorem exports](#181-what-the-minimal-theorem-exports)
    - [18.2 What Book 156 must rebuild](#182-what-book-156-must-rebuild)
    - [18.3 Final perspective](#183-final-perspective)

## 1. Scope, imports, and logical order

The difficulty in a minimal lifting theorem is not naming its two rings but keeping the reasons for every comparison independent. This chapter fixes the exact rational datum, marks the boundary of the theorem, and assigns every deep assertion to a visible source. The resulting order will be used as a dependency check throughout the proof.

### 1.1 The claim

Minimal modularity lifting compares two moduli problems. The Galois problem classifies lifts of a fixed residual representation with a fixed determinant and exact local conditions. The automorphic problem records the Hecke eigensystems occurring at the matching weight, level, and local types. The conclusion is the scheme-theoretic equality

$$
R^{\min}\simeq\mathbb T^{\min},
\tag{1.1}
$$

not merely equality of dimensions, equality after inverting $\ell$, or equality of reduced quotients.

Residual modularity supplies the common closed point. It does not by itself control every characteristic-zero lift through that point. The canonical map goes in the useful direction only after an integral Hecke-valued representation has been constructed and checked at every bad prime:

$$
R^{\min}\twoheadrightarrow\mathbb T^{\min}.
\tag{1.2}
$$

The kernel of (1.2) is the central issue. A support argument can miss nilpotents, and a characteristic-zero packet comparison can miss integral congruences. This book kills the kernel by patching the **absolute unframed** auxiliary rings from a power-series source having exactly as many variables as the diamond source. Diamond freeness then forces the patched action to have full dimension; regularity of the absolute source turns that dimension equality into injectivity, and Auslander--Buchsbaum turns the patched module into a faithful free module. Cotangent--congruence equality is derived only after $R^{\min}=\mathbb T^{\min}$ is known.

### 1.2 Imported results and new infrastructure

The proof uses the preceding books with sharply delimited roles.

| Source | Role used here |
|---|---|
| Books 29--33, 48, 62, and 64--66 | continuous representations, local and global deformation functors, tangent spaces, duality, and representability |
| Book 67 | the finite-flat type-$(0,1)$ deformation ring over $\mathbf Q_\ell$, applied only after Infrastructure II supplies an integral curve factor |
| Book 68 | Poitou--Tate presentations, the exact formulas for $g_T$ and $q_T$, and framed gauge counts |
| Books 71 and 75 | congruence ideals, cotangent modules, Fitting ideals, and the numerical Wiles--Lenstra criterion |
| Books 72 and 73 | ordered Taylor--Wiles local rings, prime selection, diamond augmentation, and the companion-module form of the Taylor--Wiles axioms |
| Book 74 | perfect complexes, regular frame extensions, and derived augmentation |
| Books 89--91 | definite class-set lattices, mass pairings, adjoints, degeneracy maps, and the distinction between faithfulness, freeness, and saturation |
| Books 92--94 | local automorphic types, old/new decompositions, and the scope of generic Jacquet--Langlands |
| Books 120, 122, and 135 | Hecke packets, integral Galois representations, determinants, and local--global compatibility |

Two stronger integral comparison results are needed in addition. They are stated in Chapters 3 and 4 as **Infrastructure I** and **Infrastructure II**. They are standard infrastructure for this clean rational case, but they are not consequences of the cited books as presently stated. Their hypotheses and proof mechanisms are therefore exposed rather than hidden in the phrase “standard Taylor--Wiles theory.” Neither asserts (1.1), injectivity of (1.2), or patched faithfulness.

The logical division is important. Infrastructure I is integral control on definite quaternionic class sets. Its generic new-quotient contradiction may apply Book 135 to individual characteristic-zero constituents, but it constructs no Hecke-valued Galois family and makes no deformation-ring comparison. Infrastructure II transfers the relevant packet to integral curve cohomology and constructs that family. Chapters 6--11 then prove the kernel-killing theorem from the sharp auxiliary tangent count, finite marked shadows, exact augmentation, and commutative algebra. Separate self-dualities on the Galois and automorphic sides are not used to manufacture a cross-complex map.

The theorem ledger is therefore:

| Result | Positive conclusion | Conclusion deliberately absent |
|---|---|---|
| Infrastructure I | integral lattices, old/new control, diamond freeness, primary--companion duality, augmentation | no Galois representation and no deformation ring comparison |
| Infrastructure II | equality of integral automorphic orders and a locally verified Hecke-valued representation | no injectivity of $R\to\mathbb T$ |
| Sharp absolute auxiliary presentation | every $R_n$ is a quotient of $P=\mathcal O[[X_1,\ldots,X_q]]$ | no uniform relation tuple and no finite-level $R_n=\mathbb T_n$ |
| Equal-variable patching, proved in Chapter 11 | $R_\infty=P$, patched freeness, faithful descent, and $R^{\min}=\mathbb T^{\min}$ | no pre-equality determinant comparison |
| Book 71 after equality | the intrinsic complete-intersection Fitting--congruence equality | no role in eliminating the kernel |

Reading any entry upward would be circular. In particular, the structural properties delivered after equal-variable patching cannot be used to establish the integral saturation or exact augmentation that the patch itself needs.

### 1.3 The clean rational datum

Fix a prime $\ell\ge7$, a finite extension $E/\mathbf Q_\ell$ with ring of integers $\mathcal O$, uniformizer $\varpi$, and residue field $k$. Let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k)
\tag{1.3}
$$

be continuous, absolutely irreducible, and odd. We impose all of the following conditions.

1. The determinant is cyclotomic:
   $$
   \det\bar\rho=\bar\chi_\ell.
   \tag{1.4}
   $$
2. With $W=\operatorname{ad}^0\bar\rho$,
   $$
   H^0(\mathbf Q,W(1))=0.
   \tag{1.5}
   $$
3. The image satisfies the split large-image hypotheses of Book 72. In particular, Taylor--Wiles primes with prescribed distinct residual Frobenius eigenvalues can be selected so as to kill dual Selmer.
4. The prime-to-$\ell$ Artin conductor $N$ is squarefree and nontrivial.
5. At every $p\mid N$, residual tame monodromy is nonzero. A fixed unramified quadratic character $\epsilon_p$ specifies the Steinberg sign, and
   $$
   p\not\equiv\pm1\pmod\ell.
   \tag{1.6}
   $$
6. The restriction $\bar\rho|_{G_{\mathbf Q_\ell}}$ is finite flat of type $(0,1)$ and has scalar endomorphism ring:
   $$
   \operatorname{End}_{k[G_{\mathbf Q_\ell}]}
   \bigl(\bar\rho|_{G_{\mathbf Q_\ell}}\bigr)=k.
   \tag{1.7}
   $$
7. The residual eigensystem occurs in an exact-level weight-two newform of level $N$, trivial central character, and the prescribed Steinberg signs. “Exact-level” means new at every $p\mid N$; it is stronger than merely occurring at a level divisible by $N$.
8. Choose one prime $p_0\mid N$. Let $B/\mathbf Q$ be the definite quaternion algebra ramified exactly at $p_0$ and infinity, with the finite local type at $p_0$ corresponding to the prescribed discrete-series packet.

The coefficient field is enlarged once, if necessary, to contain the values of the fixed source eigensystem, the residual Frobenius eigenvalues, and the fixed local signs. No common splitting field for all auxiliary levels is assumed. The Hensel roots at an auxiliary prime live in the corresponding localized Hecke order, and the finite-order tame characters live in the group algebra $\mathcal O[\Delta_v(n)]$. Thus the infinitely many Taylor--Wiles levels do not require one finite coefficient extension containing all of their generic eigenvalues.

### 1.4 Exclusions

The theorem does not cover $\ell<7$, small or exceptional residual image, failure of (1.5), scalar residual Frobenius at a Taylor--Wiles prime, or a coefficient-prime restriction with nonscalar endomorphisms. It excludes $N=1$, nonsquarefree conductor, primes $p\mid N$ with zero residual monodromy, and the vexing congruences $p\equiv\pm1\pmod\ell$. It also excludes a change of Steinberg sign, a determinant other than the fixed cyclotomic determinant, and a residual source that is only old at level $N$.

These boundaries are structural. If residual monodromy is zero, “nonzero Steinberg” is not a closed condition on Artinian points. If $p\equiv\pm1\pmod\ell$, the local tangent calculation or the primitive integral newvector control used below can fail. If the source is old, the localized class-set module need not isolate the desired packet. If the residual image is too small, the auxiliary primes required by Book 72 may not exist.

The definite algebra must be ramified at a conductor prime. Since $N$ is nontrivial, $p_0$ exists; this is why the apparently harmless case $N=1$ is not folded into the theorem. The curve realization in Infrastructure II is likewise part of the hypotheses, not an automatic consequence of generic Jacquet--Langlands.

The theorem is also not asserted if either Infrastructure I or Infrastructure II is unavailable: residual multiplicity greater than one, $\ell$-torsion in a class-set or curve lattice, a nonsaturated old image, failure of equality of integral Hecke orders, or failure of ordered integral local--global compatibility all lie outside its scope. It also requires the exact unpadded auxiliary tangent count and the exact ring, module, action, and augmentation shadows proved in Chapter 11; a merely relative framed presentation does not replace them. Characteristic-zero packet comparison, equality of dimensions, or equality of reduced supports is not accepted as a substitute. Finally, the theorem is over $\mathbf Q$; Chapter 16 explains why a totally real analogue requires new local and automorphic theorems.

### 1.5 The noncircular route

The proof follows this order:

$$
\begin{array}{c}
\text{exact local and global deformation theory}\\
\Downarrow\\
\text{Infrastructure I: integral automorphic control}\\
\Downarrow\\
\text{Infrastructure II: integral curve reciprocity}\\
\Downarrow\\
R^{\min}\twoheadrightarrow\mathbb T^{\min}\\
\Downarrow\\
\text{Taylor--Wiles sets and full lower/Iwahori/deep modules}\\
\Downarrow\\
\text{old/new control, then primary $U$/companion $V$ blocks}\\
\Downarrow\\
\text{paired Taylor--Wiles system and exact absolute tangent count}\\
\Downarrow\\
P=\mathcal O[[X_1,\ldots,X_q]]\twoheadrightarrow R_\infty,
\quad S_\infty=\mathcal O[[Z_1,\ldots,Z_q]]\curvearrowright M_\infty\\
\Downarrow\\
\text{equal-variable dimension rigidity and Auslander--Buchsbaum}\\
\Downarrow\\
R^{\min}\simeq\mathbb T^{\min}\\
\Downarrow\\
\text{complete intersection, post hoc Fitting equality, and modularity.}
\end{array}
\tag{1.8}
$$

No later arrow is used to prove an earlier one. In particular, the curve lattice is constructed before the map $R^{\min}\to\mathbb T^{\min}$; full Iwahori oldness is proved before a root projector is applied; the $U$- and $V$-blocks remain distinct until adjunction identifies their acting orders; and the fixed-source patch uses the exact absolute tangent count rather than a relation determinant. Only after (1.2) is proved injective are the deformation conormal complex and automorphic Frobenius duality placed over their common ring.

## 2. The global and local deformation problem

The word “minimal” becomes meaningful only after it has been translated into represented local conditions. This chapter performs that translation at unramified primes, nonzero Steinberg primes, $\ell$, and infinity, and then assembles the conditions into one global deformation functor. The local tangent dimensions recorded here are the arithmetic inputs to the framed ledger in Chapter 11.

### 2.1 Coefficients, determinant, and Frobenius

Every deformation is taken in the category of complete Noetherian local $\mathcal O$-algebras with residue field $k$. The determinant is fixed to the $\ell$-adic cyclotomic character $\chi_\ell$. We use arithmetic Frobenius. Thus at a good prime $r\nmid N\ell$, the general Hecke polynomial is

$$
X^2-S_r^{-1}T_rX+rS_r^{-1},
\tag{2.1}
$$

where $S_r$ is the central operator. On the trivial-central-character quotient, $S_r=1$ and (2.1) becomes

$$
X^2-T_rX+r.
\tag{2.2}
$$

The inverse powers of $S_r$ in (2.1) are forced by the arithmetic-Frobenius and covariant-representation conventions. Suppressing them before imposing $S_r=1$ changes both trace and determinant.

Put $S=\{\ell,\infty\}\cup\{p:p\mid N\}$. A deformation is unramified outside $S$ and satisfies the following local conditions.

### 2.2 Unramified minimality

At a finite prime $r\nmid N\ell$, minimality means unramifiedness. On tangent spaces the condition is

$$
L_r=H^1_{\mathrm{ur}}(\mathbf Q_r,W)
=\ker\bigl(H^1(\mathbf Q_r,W)\to H^1(I_r,W)\bigr).
\tag{2.3}
$$

Its dimension is $h^0(\mathbf Q_r,W)$. There is no independent choice of a Frobenius trace: the universal trace is a function on the global deformation ring. Minimality is therefore a ramification condition, not the assertion that the characteristic-zero trace equals the residual trace.

Indeed, an unramified cocycle is determined by its value on arithmetic Frobenius, and changing a strict basis changes that value by $(\operatorname{Frob}_r-1)W$. Hence

$$
H^1_{\mathrm{ur}}(\mathbf Q_r,W)
\simeq W/(\operatorname{Frob}_r-1)W.
\tag{2.3a}
$$

For an endomorphism of a finite-dimensional vector space, the cokernel of $F-1$ has the same dimension as its kernel, which proves the dimension assertion. This calculation also explains why an unramified local direction must not be counted again as a free Hecke eigenvalue after the global presentation has already included the good-prime trace functions.

### 2.3 Nonzero Steinberg minimality

Fix $p\mid N$. After choosing a basis adapted to the residual monodromy line, the residual restriction has the form

$$
\bar\rho|_{G_{\mathbf Q_p}}
\sim
\begin{pmatrix}
\bar\chi_\ell\bar\epsilon_p&\bar c_p\\
0&\bar\epsilon_p
\end{pmatrix},
\qquad
\bar c_p|_{I_p}\ne0,
\tag{2.4}
$$

where $\bar\epsilon_p$ is unramified quadratic. The minimal lift keeps the same ordered filtration and sign:

$$
\rho_A|_{G_{\mathbf Q_p}}
\sim
\begin{pmatrix}
\chi_\ell\epsilon_p&c_{p,A}\\
0&\epsilon_p
\end{pmatrix},
\qquad
c_{p,A}|_{I_p}\ne0\pmod{\mathfrak m_A}.
\tag{2.5}
$$

The last condition is meaningful on every Artinian quotient because the residual monodromy is already nonzero. It fixes the constant-conductor component; it is not the open condition obtained by asking a zero residual extension class to become nonzero in characteristic zero.

The local calculation can be seen on the tame quotient. Choose a tame $\ell$-power generator $\tau$ and arithmetic Frobenius $\varphi$ with

$$
\varphi\tau\varphi^{-1}=\tau^p.
\tag{2.5a}
$$

On the fixed Steinberg line a lift may be written

$$
\rho_A(\tau)=
\begin{pmatrix}1&t_A\\0&1\end{pmatrix},
\qquad
\rho_A(\varphi)=
\begin{pmatrix}p\epsilon_p(\varphi)&a_A\\0&\epsilon_p(\varphi)\end{pmatrix}.
\tag{2.5b}
$$

The relation (2.5a) is exactly compatible with the ratio $p$ of the diagonal Frobenius characters. Since $t_A$ reduces to a nonzero element, it is a unit. A strict diagonal conjugation normalizes it to a fixed lift of the residual monodromy, while a strict upper-triangular conjugation removes $a_A$ because $p-1$ is a unit. The nonzero nilpotent recovers its stable line, so there is no separate line parameter. Thus no unframed parameter survives once determinant, sign, and nonzero monodromy have been fixed. The congruence $p\not\equiv1\pmod\ell$ is the condition used in this rigidity calculation; the additional exclusion $p\not\equiv-1\pmod\ell$ is needed for the primitive integral Steinberg newvector lattice and pairing used by Infrastructure I.

For fixed determinant, fixed sign, and nonzero residual monodromy, the unframed local functor has no free character parameter. Its framed ring is formally smooth over $\mathcal O$ of relative dimension $3$:

$$
R_p^{\square,\mathrm{st},\epsilon_p}
\simeq\mathcal O[[x_{p,1},x_{p,2},x_{p,3}]].
\tag{2.6}
$$

The three variables are framing directions: the framed condition is the formal orbit of the rigid unframed object under $\operatorname{PGL}_2$. The residual centralizer is scalar. The congruence $p\not\equiv1\pmod\ell$ makes this orbit calculation transverse, while the full pair of exclusions $p\not\equiv\pm1\pmod\ell$ makes the integral Steinberg newvector lattice and pairing primitive.

The tangent condition $L_p\subset H^1(\mathbf Q_p,W)$ is the image of the tangent space of (2.5). Since $p\not\equiv1\pmod\ell$, an endomorphism commuting with both the nonzero monodromy and Frobenius is scalar; hence $h^0(\mathbf Q_p,W)=0$. The normalization above gives $L_p=0$, so

$$
\dim_kL_p=h^0(\mathbf Q_p,W)=0.
\tag{2.6a}
$$

This equality is the local numerical expression of minimality at $p$.

### 2.4 Finite flatness at the coefficient prime

At $\ell$, require that every Artinian quotient of the lift arise from a finite flat group scheme of type $(0,1)$, equivalently from the finite-flat deformation condition of Book 67 with determinant $\chi_\ell$. The scalar-endomorphism hypothesis (1.7) makes the unframed functor representable and removes hidden infinitesimal automorphisms.

In the present rational, weight-two case, Book 67 gives

$$
R_\ell^{\mathrm{fl}}\simeq\mathcal O[[z_\ell]],
\qquad
R_\ell^{\square,\mathrm{fl}}
\simeq\mathcal O[[z_\ell,x_{\ell,1},x_{\ell,2},x_{\ell,3}]].
\tag{2.7}
$$

Thus the unframed condition contributes one genuine finite-flat coordinate and the framed ring has relative dimension $4$. The tangent space $L_\ell$ is the finite-flat subspace of $H^1(\mathbf Q_\ell,W)$. This single genuine direction is indispensable in the global Euler characteristic balance.

The two dimensions in (2.7) have different origins. The one-dimensional unframed tangent is the extension parameter in the integral finite-flat, equivalently Fontaine--Laffaille, category for weights $0$ and $1$. Passing to a frame adds the three dimensions of $\operatorname{PGL}_2$: the fourth matrix coordinate is the scalar stabilizer, and (1.7) says there are no further local automorphisms. This is why the coefficient-prime entry in the local ledger is $1+3=4$, whereas the partially framed gauge calculation in Chapter 11 still begins with four matrix entries at every chosen place.

Finite flatness of a Hecke-valued family will not be inferred from its characteristic-zero Hodge--Tate weights. Infrastructure II realizes every Artinian Hecke quotient through an actual integral curve factor, to which Book 67 applies.

### 2.5 Oddness and the real place

For complex conjugation $c$, oddness says

$$
\det\bar\rho(c)=-1.
\tag{2.8}
$$

Since the determinant is fixed, the odd local condition has no deformation parameter. For $\ell>2$,

$$
h^0(\mathbf R,W)=1,
\tag{2.9}
$$

and the real term in the fixed-determinant Wiles formula is $-1$. Omitting this term produces the wrong global relation count by one.

### 2.6 The global ring and Selmer structures

Let $\mathcal D^{\min}$ be the fixed-determinant deformation functor defined by (2.3), (2.5), (2.7), and oddness. Absolute irreducibility and the scalar local endomorphism condition give a universal ring $R^{\min}$ and a universal representation

$$
\rho^{\mathrm{univ}}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(R^{\min}).
\tag{2.10}
$$

Let $\mathcal L=(L_v)$ denote the resulting Selmer structure on $W$ and let $\mathcal L^\perp$ be its local Tate-orthogonal structure on $W(1)$. Write

$$
H^1_{\mathcal L}(\mathbf Q,W)
=\ker\!\left(
H^1(G_{\mathbf Q,S},W)
\longrightarrow
\bigoplus_{v\in S}
H^1(\mathbf Q_v,W)/L_v
\right)
\tag{2.11}
$$

and define $H^1_{\mathcal L^\perp}(\mathbf Q,W(1))$ dually. Set

$$
q=h^1_{\mathcal L^\perp}(\mathbf Q,W(1)).
\tag{2.12}
$$

The group in (2.12) measures relations not yet removed by auxiliary primes. It does not directly equal the number of relations in an arbitrary framed presentation. Chapter 11 keeps the unframed Selmer count, local framed dimensions, gauge variables, and padding relations in separate columns before combining them.

## 3. Integral quaternionic Taylor--Wiles control

The definite quaternion algebra converts weight-two automorphic forms into functions on a finite set, making stabilizers, pairings, and level maps directly visible. That advantage is useful only integrally: the proof later needs saturated lattices and free diamond modules, not merely characteristic-zero packets. Infrastructure I packages precisely this automorphic work and nothing from deformation theory.

### 3.1 Definite class-set modules

Let $U\subset(B\otimes\mathbf A_f)^\times$ be a compact open with the prescribed minimal local type. For an $\mathcal O$-algebra $A$, the weight-two definite module is a space of functions on the finite class set

$$
X_U=B^\times\backslash(B\otimes\mathbf A_f)^\times/U,
\tag{3.1}
$$

with the fixed central character and local coefficient system. Denote it by $M(U,A)$. Evaluation on representatives identifies it with a direct sum of invariant submodules indexed by $X_U$. In the localized noncharacter block, all relevant stabilizer orders are prime to $\ell$; hence

$$
M(U,\mathcal O)\otimes_{\mathcal O}A
\xrightarrow{\sim}M(U,A)
\tag{3.2}
$$

for the coefficient changes used below.

Here the phrase “prescribed minimal local type” has exact content. At $r\nmid N\ell$, take the maximal compact. At $\ell$, take $\operatorname{GL}_2(\mathbf Z_\ell)$ and the trivial algebraic coefficient system corresponding to weight two. At a split prime $p\mid N$, $p\ne p_0$, take Iwahori level and localize the oriented $U_p$-operator at the sign $\epsilon_p$, thereby retaining the one-dimensional new line. At $p_0$, use maximal-compact level in $B_{p_0}^\times$ and retain the division-uniformizer operator: local Jacquet--Langlands identifies its selected eigenspace with the character $\epsilon_{p_0}\circ\operatorname{Nrd}$ corresponding to $\operatorname{St}\otimes\epsilon_{p_0}$. The uniformizer operator is essential because the two unramified quadratic signs have the same restriction to the maximal compact. The central character is trivial. These choices make the generic packet have conductor exactly $N$ and match (2.5) place by place.

The residual exact-level hypothesis ensures that localization at the chosen maximal ideal does not merely recover an old packet imported from a proper divisor of $N$. The noncharacter qualifier removes the one-dimensional norm-character spectrum that would otherwise survive on a definite class set and interfere with packet isolation and multiplicity one.

Because the source newform is Steinberg at $p_0$, generic Jacquet--Langlands transfers its characteristic-zero packet to $B^\times$. Choosing a stable lattice and reducing produces the required nonzero localized class-set block. This generic nonvanishing starts the construction, but it does not prove the integral multiplicity-one or order statements of Infrastructure I.

The mass pairing is

$$
\langle f,g\rangle_U
=\sum_{x\in X_U}
\frac{\langle f(x),g(x)\rangle}{|\Gamma_x|},
\tag{3.3}
$$

with the local coefficient pairing and the level-specific normalization understood. In the rational definite case every effective projective stabilizer has order divisible only by primes at most $5$. Hence $\ell\ge7$ makes all denominators in (3.3) units at the outset, and passing to deeper level can only shrink a stabilizer. The pairing is therefore integral and perfect. Localization at the noncharacter block removes norm-character packets; it is not being used to invert an $\ell$-divisible stabilizer order. Different levels are normalized separately. One must not silently transport one mass normalization through a degeneracy map; trace factors are part of its adjoint.

### 3.2 The automorphic control theorem

**Infrastructure I (integral quaternionic Taylor--Wiles control).** Assume the clean datum of Section 1.3, including exact-level residual modularity and the definite algebra $B$. Let $Q$ be any Taylor--Wiles set whose primes $v$ satisfy

$$
v\equiv1\pmod{\ell^n},
\qquad
\bar\rho(\operatorname{Frob}_v)
\text{ has distinct eigenvalues }
\bar\alpha_v,\bar\beta_v.
\tag{3.4}
$$

At every subset of $Q$, form the full lower, Iwahori, and deep class-set modules before applying any $U$-operator projector. Localize at the noncharacter maximal ideal determined by $\bar\rho$ and the prescribed types. Then:

1. all localized class-set lattices are finite free over $\mathcal O$ and carry perfect integral mass pairings;
2. residual multiplicity one holds, and the minimal module $M^{\min}$ is cyclic and regular over its faithful acting order $\mathbb T^{\min}$:
   $$
   M^{\min}\simeq\mathbb T^{\min};
   \tag{3.5}
   $$
   at every distinguished characteristic-zero source point the generic branch has rank one and satisfies the integral branch-saturation equality of Book 75;
3. the deck group $\Delta_Q$ acts freely on the relevant deep class set, and each full deep module is finite free over $\mathcal O[\Delta_Q]$;
4. the two degeneracy maps from lower to Iwahori level have the exact trace adjoints and Gram matrix computed in Chapter 8; their old image is split and saturated;
5. after localization, the Iwahori new quotient is zero: it is torsion-free over $\mathcal O$, while its generic fiber would consist of Steinberg representations whose residual Frobenius polynomial has a repeated root, contradicting (3.4);
6. after full Iwahori oldness has been proved, the primary generalized $U_v$-blocks and companion generalized $V_v$-blocks may be formed at deep level; they are finite free over $\mathcal O[\Delta_Q]$ and pair perfectly with diamond inversion;
7. both systems augment, by saturated coinvariants and degeneracy control, to the same minimal module $M^{\min}$; and
8. the corresponding primary and companion Hecke orders are identified by adjunction; and
9. for a sequence of Taylor--Wiles sets placed under the common presentation sources of Book 73, the adjoint maps, group-ring pairings, and augmentation pairings admit pairing-compatible finite marked shadows along one coherent diagonal subsequence, with the fixed old-level and frame normalizations preserved.

This theorem is an automorphic control statement only. It constructs no Galois representation, makes no assertion about a deformation ring, and does not imply $R=\mathbb T$.

### 3.3 Why the theorem is integral

Each adjective in Infrastructure I prevents a specific gap. Generic multiplicity one does not imply (3.5): two lattices can span the same one-dimensional generic eigenspace and have different integral indices. Generic oldness does not imply a saturated old lattice. Freeness over $\mathcal O$ does not imply freeness over $\mathcal O[\Delta_Q]$. Faithfulness of the Hecke action does not imply that the module is rank one. Finally, the identity $U_v^*=V_v$ does not make a $U_v$-eigenspace self-dual.

The theorem resolves these issues before deformation theory enters. This prevents a later $R=\mathbb T$ conclusion from being used, even implicitly, to supply the lattice freeness, saturation, or adjoint control needed in its own proof. Gorensteinness of the common deformation--Hecke ring is not used here and is deduced only in Section 13.3.

### 3.4 Proof architecture

The proof begins with class-set evaluation. The classification of finite projective stabilizers over $\mathbf Q$, together with $\ell\ge7$, shows directly that their orders are units in $\mathcal O$. Evaluation and averaging therefore give finite free lattices and the perfect mass pairing (3.3). The noncharacter localization has the separate job of deleting the one-dimensional norm-character spectrum.

Geometric mod-$\ell$ multiplicity one identifies the localized residual packet with a single line. Lifting a generator and applying Nakayama shows that $M^{\min}$ is cyclic over its faithful Hecke order. The perfect pairing identifies its congruence dual, and the saturated one-dimensional residual branch forces the cyclic map $\mathbb T^{\min}\to M^{\min}$ to be an isomorphism. This is a theorem about the automorphic order acting on the class-set lattice, not a comparison with $R^{\min}$.

At a deep prime, class-set evaluation also identifies fibers of the map from deep to lower level with $\Delta_v$. The stabilizer calculation shows that the action is free. Orbit representatives then give a basis over $\mathcal O[\Delta_v]$; tensoring over all $v\in Q$ proves the group-ring freeness.

The double-coset calculation gives the degeneracy Gram matrix of Chapter 8. Its residual determinant is a unit, so the old image is split and saturated. Local newvector theory describes the generic new quotient. A generic constituent new at $v$ is Steinberg, and because $v\equiv1\pmod\ell$, its two residual Frobenius eigenvalues coincide. The residual Hecke system away from $v$ is the one attached to $\bar\rho$; applying Book 135 separately to that characteristic-zero constituent, or equivalently using the residual degree-two determinant forced by its good-prime Hecke data, identifies the two residual systems. This contradicts the distinct eigenvalues in (3.4). No Hecke-valued family or deformation-ring comparison is used in this generic contradiction. The integral new quotient is torsion-free by class-set saturation, hence vanishes when its generic fiber vanishes.

Only then are the Hensel projectors applied. The inverse-coset adjoint calculation pairs the $U$-primary and $V$-companion blocks. Exact coinvariants, the saturated degeneracy image, and Nakayama identify each augmentation with $M^{\min}$. At every finite precision the presentation data, adjoint maps, and group-ring pairing matrices form a finite marked set; diagonal stabilization is therefore carried out on these paired shadows simultaneously, rather than appended after patching. These are precisely the ingredients later used for Taylor--Wiles axiom TW8.

## 4. Integral definite-to-curve Hecke reciprocity

Finite class sets give exact automorphic control but do not themselves carry the two-dimensional Galois representation needed for universality. Curve cohomology supplies that representation and the finite-flat geometry at $\ell$. The task of this chapter is to cross between those realizations without losing the integral Hecke order in the crossing.

### 4.1 Why generic Jacquet--Langlands is insufficient

The definite module is ideal for finite-set geometry, but a genuine two-dimensional integral Galois representation is obtained from the cohomology of a Shimura or modular curve. Generic Jacquet--Langlands matches irreducible characteristic-zero packets. By itself it does not identify the integral Hecke order acting on a definite lattice with the order acting on curve cohomology. Two orders can have the same product of fraction fields and differ by a congruence index.

Nor does a stable lattice in a generic Galois representation prove finite flatness of every Artinian specialization at $\ell$. That local condition must come from geometry over $\mathbf Z_\ell$. The required bridge is therefore an integral, saturated packet comparison.

### 4.2 The reciprocity theorem

**Infrastructure II (integral definite-to-curve Hecke reciprocity).** Under the clean datum and the levels occurring in Infrastructure I, there are saturated curve-realizable lattices $C(U)$ with the following properties.

1. After inverting $\ell$, $C(U)$ and the localized definite module $M(U,\mathcal O)$ contain exactly the same automorphic packet and local refinements. Here multiplicity is compared on the automorphic multiplicity space: the universal two-dimensional Galois factor occurring in curve $H^1$ is not counted as a second automorphic copy.
2. Inside their common reduced generic Hecke algebra, the two integral acting orders are equal:
   $$
   \mathbb T_C(U)=\mathbb T_B(U).
   \tag{4.1}
   $$
3. This common order is finite flat over $\mathcal O$, and its generic fiber is reduced.
4. There is a genuine continuous representation
   $$
   \rho_{\mathbb T(U)}:G_{\mathbf Q}\longrightarrow
   \operatorname{GL}_2(\mathbb T(U))
   \tag{4.2}
   $$
   lifting $\bar\rho$, not merely a determinant or pseudorepresentation.
5. On the fixed trivial-central quotient its determinant is $\chi_\ell$. Retaining the ambient Hecke labels, at $r\nmid NQ\ell$ its arithmetic-Frobenius polynomial is
   $$
   X^2-S_r^{-1}T_rX+rS_r^{-1}.
   \tag{4.3}
   $$
   Here $S_r$ maps to $1$ in the common acting order, so the displayed constant term is $r$, as required by the stated determinant.
6. At every $p\mid N$, (4.2) satisfies the integral nonzero Steinberg condition (2.5), with the fixed unramified quadratic sign $\epsilon_p$.
7. At every $v\in Q$, the primary refinement supplies a $G_{\mathbf Q_v}$-stable ordered line. Its unramified factor records the ordered root $\alpha_v$, and its tame factor is the universal diamond character; fixed determinant places the inverse tame character on the complementary line. The companion order records the adjoint $V_v$-refinement and yields the same ordered Galois deformation after adjunction.
8. For every Artinian quotient $A$ of $\mathbb T(U)$, the representation $\rho_{\mathbb T(U)}\otimes A$ at $\ell$ factors through an actual integral good-reduction curve factor. Book 67 therefore proves that it is finite flat of type $(0,1)$.

Infrastructure II asserts reciprocity and local--global compatibility, not $R=\mathbb T$. Equality (4.1) compares two automorphic Hecke orders. It says nothing about the kernel of a deformation-to-Hecke map.

### 4.3 Construction and proof architecture

One first changes the quaternionic ramification set so that the same discrete automorphic packet occurs in degree-one cohomology of an appropriate curve. Idempotents for the fixed local types and the noncharacter residual block cut out a torsion-free curve lattice. Its image in the common generic packet is saturated by taking the intersection of the packet subspace with integral cohomology.

Generic Jacquet--Langlands identifies the fraction algebras. To descend that identification to orders, one compares trace-dual lattices under Poincaré duality on the curve and the mass pairing on the definite class set. Residual multiplicity one makes the packet branch primitive on both sides. The degeneracy maps and their integral adjoints show that the conductor and congruence indices agree prime by prime. Since both lattices are torsion-free, equality after reduction and equality of trace-dual indices force (4.1). This torsion-free packet/order comparison is the step absent from a purely generic argument.

The curve Jacobian or its localized Tate module then gives a two-dimensional determinant with the polynomial (4.3). Absolute residual irreducibility upgrades it uniquely to the matrix representation (4.2). The Weil--Deligne description at $p\mid N$, together with saturated monodromy and the exact-level newvector, proves the integral Steinberg filtration; nonzero residual monodromy prevents degeneration on Artinian quotients. At $v\in Q$, the integral refined correspondence identifies the $U_v$-line and diamond character in the required order.

Finally, the curve has an integral model with the required good reduction at $\ell$. The localized finite-flat group scheme and its Tate module realize every Artinian quotient of the Hecke order. Book 67 applies to those actual integral factors. This is stronger than checking finite flatness at the characteristic-zero points and is exactly what is needed for universality in Chapter 5.

## 5. The Hecke representation and the map from deformation to Hecke

With the automorphic lattice and the curve-valued Galois family separately established, the first comparison map can finally be written. This chapter verifies that the family occupies every local deformation condition before invoking universality, then proves surjectivity from named Hecke generators. It stops deliberately before any claim of injectivity.

### 5.1 The minimal Hecke algebra

Begin with the faithful localized Hecke order on the packet cut out by $\bar\rho$ and the fixed Steinberg signs, keeping the central operators $S_r$ visible so that the normalization (2.1) remains meaningful. Impose the trivial-central equations $S_r=1$ and let $M^{\min}$ be the resulting minimal definite module. Define $\mathbb T^{\min}$ to be the faithful image on $M^{\min}$ of the good Hecke operators and the prescribed bad-prime operators. Thus $\mathbb T^{\min}$ is already the trivial-central-character quotient, although formulas inherited from the ambient order continue to display $S_r$ before specialization.

Infrastructure I gives

$$
M^{\min}\simeq\mathbb T^{\min}
\tag{5.1}
$$

as a module over this automorphic order. Infrastructure II gives finite flatness over $\mathcal O$, reduced generic fiber, and a representation

$$
\rho_{\mathbb T^{\min}}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(\mathbb T^{\min}).
\tag{5.2}
$$

Neither statement compares $\mathbb T^{\min}$ with $R^{\min}$.

### 5.2 Local verification of the Hecke family

The representation (5.2) has determinant $\chi_\ell$ and is unramified outside $N\ell$. At a good prime $r$, its polynomial is (4.3), hence (2.2) on the trivial-central quotient. At each $p\mid N$, it has the filtration (2.5) with fixed $\epsilon_p$ and nonzero integral monodromy. At $\ell$, every Artinian specialization is finite flat of type $(0,1)$ by the curve factor and Book 67. At infinity, its determinant is odd.

These verifications precede the use of universality. A determinant with the right good-prime traces would not suffice: the local deformation problem is a problem of representations, including an ordered nonzero extension at $p$ and finite-flat integral structure at $\ell$.

### 5.3 The canonical surjection

Universality now gives a unique local homomorphism

$$
\phi^{\min}:R^{\min}\longrightarrow\mathbb T^{\min}
\tag{5.3}
$$

such that $\rho^{\mathrm{univ}}\otimes_{R^{\min}}\mathbb T^{\min}$ is isomorphic to (5.2). At every good $r$,

$$
\phi^{\min}\bigl(\operatorname{tr}\rho^{\mathrm{univ}}(
\operatorname{Frob}_r)\bigr)=S_r^{-1}T_r.
\tag{5.4}
$$

The right side is written in the ambient normalization; its image in $\mathbb T^{\min}$ is simply $T_r$ because $S_r=1$ there.

The faithful localized Hecke order is topologically generated by these good-prime traces together with the fixed central and local-type data. Chebotarev and absolute residual irreducibility therefore imply that (5.3) is surjective:

$$
R^{\min}\twoheadrightarrow\mathbb T^{\min}.
\tag{5.5}
$$

At this point only surjectivity is known. Finite flatness of $\mathbb T^{\min}$ does not make $R^{\min}$ flat, and (5.1) does not make the kernel of (5.5) act faithfully on any patched module. The remaining chapters construct the exact auxiliary system and the absolute fixed-source patch that proves this kernel is zero.

## 6. Taylor--Wiles primes and auxiliary deformation rings

Dual Selmer classes obstruct sharp control of the auxiliary deformation rings. Taylor--Wiles primes trade each such global class for a controlled local tame character. This chapter carries out that exchange on the Galois side, including the ordered Frobenius line and the exact finite diamond quotient that later appears geometrically.

### 6.1 Killing dual Selmer

Recall

$$
q=h^1_{\mathcal L^\perp}(\mathbf Q,W(1)).
\tag{6.1}
$$

The split image hypothesis and Book 72 give, for every $n\ge1$, a set $Q_n$ of exactly $q$ primes, disjoint from $N\ell$, such that

$$
v\equiv1\pmod{\ell^n}
\qquad(v\in Q_n),
\tag{6.2}
$$

$\bar\rho(\operatorname{Frob}_v)$ has distinct eigenvalues, and the corresponding localization classes kill the dual Selmer group for the auxiliary local problem. The sets can be chosen with norms tending to infinity and with the uniform presentation bounds required in Book 73.

This use of Chebotarev is not a dimension slogan. A basis of dual Selmer is chosen, one detects each basis vector at a regular semisimple Frobenius element in the residual image, and the split image hypothesis makes those detection conditions simultaneous. The resulting localization matrix is invertible. Distinct eigenvalues at each selected prime are used twice later: to define an ordered local component and to make the degeneracy determinant a unit.

If $q=0$, take $Q_n=\varnothing$ for every $n$, $\Delta_n=\{1\}$, and $\Lambda_n=\mathcal O$. Every assertion about an auxiliary prime is then vacuous, while the numerical formulas below still hold with $t=s+1$.

### 6.2 Ordered roots and diamond groups

For $v\in Q_n$, choose an ordering

$$
\bar\alpha_v,\bar\beta_v
\tag{6.3}
$$

of the eigenvalues of $\bar\rho(\operatorname{Frob}_v)$. The first root is the primary root. Since the determinant is cyclotomic,

$$
\bar\alpha_v\bar\beta_v=v\quad\text{in }k.
\tag{6.4}
$$

Let $\Delta_v(n)$ be the quotient of the $\ell$-Sylow subgroup of $\mathbf F_v^\times$ of exact order $\ell^n$, and put

$$
\Delta_n=\prod_{v\in Q_n}\Delta_v(n),
\qquad
\Lambda_n=\mathcal O[\Delta_n],
\qquad
\mathfrak a_n=\ker(\Lambda_n\to\mathcal O).
\tag{6.5}
$$

The augmentation sends every diamond element to $1$. The ordering in (6.3) is separate data: the group algebra alone does not distinguish the two residual Frobenius lines.

### 6.3 Local auxiliary rings

The ordered Taylor--Wiles functor at $v$ preserves a line lifting the $\bar\alpha_v$-line. On that line inertia acts through the tautological character

$$
I_v\twoheadrightarrow\mathbf F_v^\times
\twoheadrightarrow\Delta_v(n)
\longrightarrow\mathcal O[\Delta_v(n)]^\times.
\tag{6.6}
$$

Let $\eta_{X_v}$ be the unramified character sending arithmetic Frobenius to $\widetilde\alpha_v(1+X_v)$. The two ordered characters are

$$
\eta_{X_v}\boldsymbol\theta_v,
\qquad
\chi_\ell\eta_{X_v}^{-1}\boldsymbol\theta_v^{-1}.
\tag{6.7}
$$

Thus fixed determinant puts the inverse diamond character on the complementary line. Book 72 gives

$$
R_v^{\mathrm{TW}}
\simeq\mathcal O[\Delta_v(n)][[X_v]],
\tag{6.8}
$$

and the framed ring is formally smooth of relative dimension $3$ over the diamond algebra, equivalently of relative dimension $2$ over (6.8):

$$
R_v^{\square,\mathrm{TW}}
\simeq
\mathcal O[\Delta_v(n)][[X_v,Y_v,Z_v]].
\tag{6.9}
$$

The variable $X_v$ changes the ordered unramified Frobenius root; it is not a second diamond variable. The variables $Y_v,Z_v$ move the eigenline inside a frame. They are deliberately not denoted $U_v,V_v$, which below name the two opposite Hecke operators. Under augmentation of $\mathcal O[\Delta_v(n)]$, (6.8) maps to the unramified local deformation ring with the selected Hensel root.

### 6.4 Global auxiliary rings and augmentation

Let $R_n=R_{Q_n}$ be the universal fixed-determinant deformation ring obtained by using (6.8) at every $v\in Q_n$ and the minimal conditions at $N\ell$. It is a local $\Lambda_n$-algebra. The tautological inertia characters define the structure map

$$
\Lambda_n\longrightarrow R_n.
\tag{6.10}
$$

Killing $\mathfrak a_n$ makes every auxiliary inertia character trivial. Because the ordered unramified component specializes to the original minimal local condition, universality gives an exact augmentation identity

$$
R_n/\mathfrak a_nR_n\simeq R^{\min}.
\tag{6.11}
$$

This is a statement about represented local deformation functors. The corresponding automorphic module and Hecke augmentations require separate proofs in Chapters 7--9.

Infrastructure II constructs a representation over the auxiliary Hecke order only after its integral curve lattice has been built. Its ordered line and diamond inertia at $v$ verify (6.6)--(6.7), so universality will give compatible surjections $R_n\twoheadrightarrow\mathbb T_n^+$. No such map is inferred merely from the presence of an operator called $U_v$.

## 7. Full auxiliary modules and diamond freeness

The automorphic side must realize the same finite diamond groups by an honest free action. Before selecting any Frobenius root, this chapter defines the lower, Iwahori, and deep modules on which old/new decomposition makes sense. The class-set torsor and its mass pairing then produce the free group-ring modules and duality needed later.

### 7.1 Lower, Iwahori, and deep levels

Fix $v\in Q_n$ and identify $B_v^\times$ with $\operatorname{GL}_2(\mathbf Q_v)$. Define

$$
K_v=\operatorname{GL}_2(\mathbf Z_v),
\tag{7.1}
$$

$$
I_v=U_0(v)
=\left\{
\begin{pmatrix}a&b\\c&d\end{pmatrix}\in K_v:
c\equiv0\pmod v
\right\},
\tag{7.2}
$$

and, using the projective diagonal-ratio convention compatible with (6.6),

$$
U_1(v,n)
=\ker\!\left(
I_v\longrightarrow\mathbf F_v^\times
\longrightarrow\Delta_v(n)
\right),
\qquad
g\longmapsto a(g)d(g)^{-1}\bmod v.
\tag{7.3}
$$

The ratio convention makes every scalar matrix act trivially and matches the pair of tame characters $\boldsymbol\theta_v,\boldsymbol\theta_v^{-1}$ in (6.7): an Iwahori type with trivial central character transforms by $\boldsymbol\theta_v(a/d)$. Using the upper-left entry alone would leave a central quotient in the deck action and would invalidate the freeness argument below.

At all other places retain the fixed minimal compact open. For a subset $J\subseteq Q_n$, use $I_v$ at $v\in J$ and $K_v$ at $v\notin J$. At full deep level use $U_1(v,n)$ for every $v\in Q_n$.

Before selecting any root or applying any projector, define the localized full modules

$$
M_{K,n},\qquad M_{I,n},\qquad M_{1,n}
\tag{7.4}
$$

at lower, full Iwahori, and full deep level. Here $M_{I,n}$ means Iwahori at every prime of $Q_n$. Intermediate mixed-level modules are retained for induction over $Q_n$. This order matters: the old/new quotient belongs to the full Iwahori module, not to a branch that has already discarded half of it.

### 7.2 Free diamond action

The quotient $I_v/U_1(v,n)$ acts on the right on the deep class set and factors through $\Delta_v(n)$. Suppose an $\ell$-power diamond fixes a class. It then lifts to an element of an arithmetic stabilizer whose projective image has $\ell$-power order. The definite stabilizer classification and $\ell\ge7$ make that projective image trivial, so the lift is central. But the diagonal-ratio map in (7.3) kills every scalar, and therefore the diamond itself is trivial. Hence $\Delta_n$ acts freely on the deep class-set fibers. Noncharacter localization is still needed to isolate the intended packet, but not to remove an $\ell$-divisible stabilizer.

Choosing one representative in each orbit and using class-set evaluation gives

$$
M_{1,n}\simeq\Lambda_n^{\oplus d_n}
\tag{7.5}
$$

for some $d_n$. This is genuine group-ring freeness, not a comparison of $\mathcal O$-ranks. Infrastructure I makes the construction compatible with localization and with every mixed level.

At this stage (7.5) concerns the full deep module. A direct summand selected later by a Hensel idempotent will again be $\Lambda_n$-projective and, because $\Lambda_n$ is local in the localized block, free. Applying the projector before proving full oldness would conceal whether the complementary new quotient was integral torsion.

### 7.3 Integral pairings at deep level

Normalize the mass pairing independently at each lower, Iwahori, and deep level. On the full deep module it is perfect and satisfies

$$
\langle\langle\delta\rangle x,y\rangle
=\langle x,\langle\delta^{-1}\rangle y\rangle
\qquad(\delta\in\Delta_n).
\tag{7.6}
$$

Thus the induced $\Lambda_n$-duality uses the involution

$$
\iota:\Lambda_n\longrightarrow\Lambda_n,
\qquad
\iota(\delta)=\delta^{-1}.
\tag{7.7}
$$

For $x,y$ in the full deep module, package the coefficient-valued pairing into

$$
[x,y]_n
=\sum_{\delta\in\Delta_n}
\langle\delta^{-1}x,y\rangle[\delta]
\in\Lambda_n.
\tag{7.8}
$$

Then

$$
[\lambda x,y]_n=\lambda[x,y]_n,
\qquad
[x,\lambda y]_n=[x,y]_n\iota(\lambda).
\tag{7.9}
$$

The Frobenius self-duality of the finite group algebra and the freeness in (7.5) make (7.8) a perfect $\Lambda_n$-pairing. The inverse in (7.6) is not a normalization choice. It follows from the inverse-double-coset adjoint formula of Book 90. The same formula will give $U_v^*=V_v$ rather than $U_v^*=U_v$.

## 8. Exact degeneracy and full Iwahori oldness

Augmentation from deep level first lands at Iwahori level, not directly at the minimal hyperspecial module. The gap is closed by a two-map degeneracy calculation. Its Gram determinant proves integral saturation, while local newvector theory kills the remaining torsion-free new quotient; only after both steps is it safe to select an ordered branch.

### 8.1 Degeneracy maps and trace adjoints

It is enough to work at one auxiliary prime while holding every other local level fixed. Put

$$
\beta=\begin{pmatrix}1&0\\0&v\end{pmatrix}.
\tag{8.1}
$$

With the convention (7.2), one has $I_v\subset\beta K_v\beta^{-1}$, which is the subgroup inclusion needed for the second map below. The opposite diagonal matrix $\operatorname{diag}(v,1)$ defines the oriented Hecke operator $U_v$; using it here without inverting the translation would make the displayed restriction map undefined.

Let $M_K$ and $M_I$ be the localized modules with level $K_v$ and $I_v$. There are two restriction maps

$$
\delta_0=\operatorname{res}_{K_v}^{I_v},
\qquad
\delta_1=
\operatorname{res}_{\beta K_v\beta^{-1}}^{I_v}\circ R_\beta,
\tag{8.2}
$$

and the degeneracy map is

$$
\delta=(\delta_0,\delta_1):M_K\oplus M_K\longrightarrow M_I.
\tag{8.3}
$$

Because the mass pairings at the two levels were separately normalized, their adjoints contain the exact trace maps:

$$
\delta_0^*=\operatorname{Tr}_{I_v}^{K_v},
\qquad
\delta_1^*=R_{\beta^{-1}}
\circ\operatorname{Tr}_{I_v}^{\beta K_v\beta^{-1}}.
\tag{8.4}
$$

Dropping either trace or replacing it by an unnormalized averaging operator changes the diagonal entries of the next calculation.

### 8.2 The Gram matrix

The double-coset decompositions of $K_v\beta K_v$ and $I_v\backslash K_v$ give

$$
\delta^*\delta
=
\begin{pmatrix}
v+1&T_v\\
T_v&v+1
\end{pmatrix}.
\tag{8.5}
$$

The diagonal composites count the $v+1$ points of $\mathbf P^1(\mathbf F_v)$. One off-diagonal composite gives $K_v\beta K_v$. Since $\beta=vI\cdot\operatorname{diag}(v^{-1},1)$, the central factor $S_v$ cancels the $S_v^{-1}$ in the inverse-coset formula, and this operator is $T_v$. The other off-diagonal entry is its adjoint $S_v^{-1}T_v$; it is also $T_v$ because the modules in this chapter already have trivial central character. This identifies every entry of (8.5); no scalar may be absorbed into the pairing because the trace adjoints were fixed in (8.4).

Modulo the residual maximal ideal, $v=1$, $T_v=\bar\alpha_v+\bar\beta_v$, and $\bar\alpha_v\bar\beta_v=v$. Therefore

$$
\det(\delta^*\delta)
\equiv(v+1)^2-T_v^2
=-(\bar\alpha_v-\bar\beta_v)^2
\pmod{\mathfrak m}.
\tag{8.6}
$$

The right side is a unit. Consequently $\delta^*\delta$ is invertible. An explicit left inverse of $\delta$ is

$$
(\delta^*\delta)^{-1}\delta^*:M_I\longrightarrow M_K\oplus M_K.
\tag{8.7a}
$$

Thus $\delta$ is a split injection, and

$$
M_I^{\mathrm{old}}=\operatorname{im}\delta
\tag{8.7}
$$

is a direct summand. In particular, it is saturated and $M_I/M_I^{\mathrm{old}}$ is $\mathcal O$-torsion-free.

### 8.3 Saturation and vanishing of the new quotient

Suppose the generic fiber of the localized new quotient were nonzero. It would contain an eigenpacket whose local representation at $v$ is Steinberg. The associated local Galois representation has Frobenius eigenvalues in ratio $v$. Since $v\equiv1\pmod\ell$, their reductions coincide. But the residual localization was defined by the two distinct roots $\bar\alpha_v$ and $\bar\beta_v$. This is impossible.

Thus

$$
(M_I/M_I^{\mathrm{old}})\otimes_{\mathcal O}E=0.
\tag{8.8}
$$

The quotient is torsion-free by (8.6), so (8.8) kills it integrally:

$$
M_I=M_I^{\mathrm{old}}.
\tag{8.9}
$$

Repeating the argument one prime at a time proves full Iwahori oldness at all primes of $Q_n$. The order of the two steps is essential: generic vanishing alone cannot kill an integral torsion quotient, and saturation alone does not identify its generic packet.

### 8.4 The Iwahori operator after oldness

Only now use (8.9) to calculate the Iwahori operator $U_v=[I_v\operatorname{diag}(v,1)I_v]$. With the conventions of (8.1)--(8.4), the direct right-coset calculation gives

$$
U_v\delta(x,y)
=\delta(T_vx+vy,-x).
\tag{8.10}
$$

Hence on the old module

$$
U_v^2-T_vU_v+v=0.
\tag{8.11}
$$

The matrix in the coordinates $M_K\oplus M_K$ is

$$
\begin{pmatrix}T_v&v\\-1&0\end{pmatrix}.
\tag{8.12}
$$

Formula (8.10), not a remembered sign convention, determines which old vector belongs to the primary root in the next chapter.

## 9. Primary and companion branches

The ordered Taylor--Wiles deformation remembers one residual Frobenius line, so the automorphic module must select the matching $U_v$-branch. Duality sends that branch to a $V_v$-branch rather than back to itself. This chapter constructs both modules, keeps them distinct, and proves the paired augmentation required by Book 73.

### 9.1 Hensel projectors and the primary old line

Because the residual roots are distinct, Hensel's lemma factors (8.11) in the localized Hecke order:

$$
X^2-T_vX+v=(X-\alpha_v)(X-\beta_v),
\qquad
\alpha_v\equiv\bar\alpha_v,
\quad
\beta_v\equiv\bar\beta_v.
\tag{9.1}
$$

Define

$$
e_{\alpha_v}^U
=\frac{U_v-\beta_v}{\alpha_v-\beta_v}.
\tag{9.2}
$$

From (8.10), the primary $U_v$-old line is explicitly

$$
M_K\longrightarrow e_{\alpha_v}^UM_I,
\qquad
z\longmapsto\delta(-\alpha_vz,z),
\tag{9.3}
$$

since the vector $(-\alpha_v,1)$ is an $\alpha_v$-eigenvector for (8.12). This formula fixes the primary convention; replacing it by $(1,-\alpha_v)$ would correspond to a different matrix convention.

### 9.2 The deep primary and companion blocks

At full deep level, define the primary generalized block $M_n^+$ by localizing the full module at the maximal ideal containing

$$
U_v-\bar\alpha_v
\qquad(v\in Q_n).
\tag{9.4}
$$

Let $V_v$ be the inverse-double-coset operator adjoint to $U_v$. Define the companion block $M_n^-$ by the adjoint maximal ideal containing

$$
V_v-\bar\alpha_v
\qquad(v\in Q_n).
\tag{9.5}
$$

Infrastructure I and (7.5) give finite free $\Lambda_n$-modules $M_n^+$ and $M_n^-$. Let $\mathbb T_n^+$ and $\mathbb T_n^-$ be their faithful acting Hecke orders. The labels $+$ and $-$ distinguish primary and companion; they do not assert that the modules are equal.

### 9.3 Adjointness, not self-adjointness

Book 90 gives the exact identity

$$
U_v^*=V_v.
\tag{9.6}
$$

Consequently

$$
(e_{\alpha_v}^U)^*=e_{\alpha_v}^V,
\qquad
e_{\alpha_v}^V
=\frac{V_v-\beta_v}{\alpha_v-\beta_v},
\tag{9.7}
$$

not $(e_{\alpha_v}^U)^*=e_{\alpha_v}^U$. The mass pairing therefore restricts to a perfect coefficient-valued pairing

$$
M_n^+\times M_n^-
\longrightarrow\mathcal O
\tag{9.8}
$$

satisfying

$$
\langle\lambda x,y\rangle
=\langle x,\iota(\lambda)y\rangle
\qquad(\lambda\in\Lambda_n),
\tag{9.9}
$$

with $\iota$ from (7.7).

Equivalently, restricting (7.8) gives a perfect sesquilinear pairing

$$
[\ ,\ ]_n:M_n^+\times M_n^-
\longrightarrow\Lambda_n,
\qquad
[\lambda x,y]_n=\lambda[x,y]_n,
\quad
[x,\lambda y]_n=[x,y]_n\iota(\lambda).
\tag{9.9a}
$$

This is the precise sense in which the two branch modules are paired perfectly over $\Lambda_n$ with diamond inversion.

For $t\in\mathbb T_n^+$, adjunction defines a unique operator $t^\dagger$ on $M_n^-$ by

$$
\langle tx,y\rangle=\langle x,t^\dagger y\rangle.
\tag{9.10}
$$

Adjunction reverses products. The selected acting orders are the commutative suborders generated by the away operators, diamonds, and the one oriented operator at each auxiliary place, so the resulting anti-isomorphism may be written as an isomorphism

$$
\mathbb T_n^+\xrightarrow{\sim}\mathbb T_n^-,
\qquad t\longmapsto t^\dagger,
\tag{9.11}
$$

This is compatible with diamond inversion. We use (9.11) to compare actions; we do not identify $M_n^+$ with $M_n^-$.

### 9.4 Augmentation and ordered Galois control

Taking $\Delta_n$-coinvariants first descends the full deep module to the full Iwahori module. Full oldness (8.9), followed by the explicit primary line (9.3), then gives saturated isomorphisms

$$
M_n^+/\mathfrak a_nM_n^+
\xrightarrow{\sim}M^{\min},
\qquad
M_n^-/\mathfrak a_nM_n^-
\xrightarrow{\sim}M^{\min}.
\tag{9.12}
$$

The second map uses the adjoint degeneracy diagram. It is not obtained by declaring $M_n^-=M_n^+$. Derived coinvariants are ordinary because both modules are $\Lambda_n$-free, and the augmentation of (9.9a) is the perfect minimal mass pairing between the two copies of $M^{\min}$. Thus the companion duality descends together with the modules, not after them as an unrelated choice.

In particular,

$$
\operatorname{rank}_{\Lambda_n}M_n^+
=\operatorname{rank}_{\Lambda_n}M_n^-
=\operatorname{rank}_{\mathcal O}M^{\min},
\tag{9.12a}
$$

so the normalized module rank is independent of $n$. This is the size condition needed for the finite-shadow construction.

Because the branch lattices and their images are saturated, (9.12) also controls the faithful acting orders:

$$
\mathbb T_n^+/\mathfrak a_n\mathbb T_n^+
\xrightarrow{\sim}\mathbb T^{\min},
\qquad
\mathbb T_n^-/\mathfrak a_n\mathbb T_n^-
\xrightarrow{\sim}\mathbb T^{\min}.
\tag{9.13}
$$

Module coinvariants without saturation would yield only a map between Hecke images, not the isomorphisms (9.13).

Infrastructure II identifies these saturated definite acting orders with the curve acting orders before and after augmentation. Hence (9.13) also controls the integral order over which the Galois family is defined; generic Jacquet--Langlands cannot insert an unseen congruence index at this step.

Infrastructure II supplies a genuine representation over $\mathbb T_n^+$. Its ordered $G_{\mathbf Q_v}$-stable line has residual Frobenius root $\bar\alpha_v$, and tame inertia acts through the tautological diamond character. Thus it lies on the ordered local ring (6.8), and universality gives a compatible surjection

$$
R_n\twoheadrightarrow\mathbb T_n^+.
\tag{9.14}
$$

Surjectivity in (9.14) is a generator statement, not part of universality. Good-prime traces produce the operators $S_r^{-1}T_r$; the tame characters produce every diamond operator; and Frobenius on the ordered line produces the selected $U_v$-root. The remaining original-level operators are fixed by the prescribed local types. These elements generate the faithful localized order, so the universal map has image $\mathbb T_n^+$.

Via (9.11), the companion order carries the adjoint description of the same ordered Galois condition. Under augmentation, (9.14) becomes (5.5).

## 10. The Taylor--Wiles axiom ledger

Prime selection, deformation rings, class-set modules, Hecke actions, augmentation, and duality come from different arguments. A Taylor--Wiles system is valid only when their maps commute and their ranks are uniform. This chapter records that verification line by line and states plainly what the system has not yet proved.

### 10.1 The paired finite-level system

For every $n$ we now have

$$
(R_n,\mathbb T_n^+,M_n^+;
\mathbb T_n^-,M_n^-;\Lambda_n)
\tag{10.1}
$$

together with the minimal datum

$$
(R^{\min},\mathbb T^{\min},M^{\min};\mathcal O).
\tag{10.2}
$$

The primary module carries the deformation-theoretic Hecke action. The companion module supplies the exact dual object demanded by Book 73, axiom TW8. This is the correct replacement for a nonexistent self-adjointness of $U_v$.

### 10.2 Verification of the axioms

The labels below are exactly those of Book 73, Definition 16.1.

1. **TW1: auxiliary arithmetic.** Section 6.1 gives an ordered set $Q_n$ of the fixed cardinality $q$, split regular residual Frobenius, and $v\equiv1\pmod{\ell^n}$. Section 6.2 supplies named generators and the exact quotients $\Delta_v(n)$ of order $\ell^n$, hence $\Delta_n\simeq(\mathbf Z/\ell^n\mathbf Z)^q$ with the declared reciprocity convention.
2. **TW2: rings and covariance.** The maps
   $$
   \Lambda_n\longrightarrow R_n\twoheadrightarrow\mathbb T_n^+
   $$
   commute because Infrastructure II identifies the geometric diamond character with (6.6), and (9.14) is surjective by the listed Hecke generators. The companion order carries the $\iota$-twisted diamond structure under the adjoint isomorphism (9.11).
3. **TW3: factorized module action.** By definition $\mathbb T_n^+$ acts faithfully on $M_n^+$. Its $R_n$-action is the composite through (9.14), and its diamond action is the composite from $\Lambda_n$; no second action is introduced. The analogous statements hold for the companion after transport by adjunction.
4. **TW4: all three augmentations.** Equation (6.11) is TW4a, the first isomorphism in (9.12) is TW4b, and the first isomorphism in (9.13) is TW4c. The last uses saturation of acting orders and is not inferred merely from module coinvariants. These maps commute with (5.5), (9.14), and the two module actions.
5. **TW5: diamond size.** Infrastructure I makes $M_n^+$ finite free over $\Lambda_n$. Equation (9.12a) gives one fixed rank, independent of $n$. The same assertions hold for $M_n^-$.
6. **TW6: deformation control.** Book 72 kills the enlarged dual Selmer group. The minimal datum is balanced by the local calculation recorded at the start of Chapter 11. The $q$ ordered local quotients and the $q$-dimensional dual localization matrix cancel in the exact Poitou--Tate sequence, giving the sharp auxiliary primal dimension $q$ in (11.15). Book 68 and the complete effective local complexes separately give the relative generator and relation-complex ranks computed in (11.3)--(11.12).
7. **TW7: presentation coordinates.** Named diamond generators put every $\Lambda_n$ under $S_\infty=\mathcal O[[Z_1,\ldots,Z_q]]$. Uniform cotangent lifts and variable--linear-relation padding put the framed deformation presentations under one fixed source. Since the sets $Q_n$ are not nested, the only transitions are the coherent finite-shadow pseudo-transitions obtained after the diagonal subsequence of Book 73; no arithmetic map between two original levels is asserted.
8. **TW8: companion duality.** The module $M_n^-$ is finite free over $\Lambda_n$, its faithful order is identified with $\mathbb T_n^+$ by (9.11), and it has its own exact augmentation. Equations (9.8)--(9.9a) give perfect coefficient- and group-ring-valued pairings with diamond inversion. The adjoint maps, augmentation pairing, and pairing-compatible finite shadows are supplied by Infrastructure I; the fixed frame normalization is the one used in Sections 6.3 and 11.3. This is the companion-module form of TW8, not a self-pairing of the primary $U_v$-block.

The automorphic realization clauses (A1)--(A8) of Book 73, Section 17.3, are thereby accounted for as well. Infrastructure I supplies the torsion-free lattices, the geometric diamond action and freeness, the named Hecke action, exact module and order control, uniform multiplicity, duality, and the automorphic old-branch and adjoint normalizations (A1--A3, A5--A7, and the automorphic part of A8). Infrastructure II identifies that geometric diamond action with the reciprocity normalization in (6.6), supplies the genuine family representation, every local verification, and the generator proof of the surjection (the remaining part of A2 and A4), and supplies the curve-order saturation used in A5. Sections 2, 6.3, and 11.3 fix the determinant, auxiliary eigenline coordinates, and framing convention completing A8.

The compatibility maps used in patching are chosen after the orders have been identified by adjunction. No arbitrary isomorphism $M_n^+\simeq M_n^-$ is introduced.

The prime sets $Q_n$ are not nested and there are no arithmetic transition maps between their class sets. Book 73 instead places the abstract diamond groups under one power-series source, chooses uniform presentation coordinates, and stabilizes finite quotient shadows by a diagonal subsequence. Every patched transition below refers to those presentation models. It does not pretend that a prime in $Q_{n+1}$ lies above a prime in $Q_n$.

### 10.3 What has not yet been proved

The axiom ledger proves neither $R_n=\mathbb T_n^+$ nor $R^{\min}=\mathbb T^{\min}$. It does not prove that a patched module is faithful over a patched deformation ring. It also does not show that $R^{\min}$ is finite flat or reduced. At present the known finite-flat ring is the Hecke quotient.

The paired system supplies more than two separately self-dual complexes: its unpadded absolute deformation rings have a sharp tangent count, and its free diamond modules carry exact augmented actions. Chapter 11 patches those data simultaneously. The relative framed ledger remains useful as an audit, but it is not the kernel-killing input; injectivity of (5.5) will come from the absolute fixed-source patch.

## 11. The framed ledger and absolute patching

This chapter first audits the framed relation count, separating absolute dual Selmer, relative obstruction rank, local-ring dimensions, and gauge directions. It then returns to the unpadded absolute auxiliary rings. Their exact $q$-dimensional tangent spaces give a fixed source with $q$ variables, while the diamond algebra also has $q$ variables. Patching from these equal-dimensional sources proves regularity and faithfulness directly.

### 11.1 The exact global generator formula

Let

$$
s=\#\{p:p\mid N\},
\qquad
q=h^1_{\mathcal L^\perp}(\mathbf Q,W(1)),
\tag{11.1}
$$

and set

$$
\mathscr T_n=\{\ell\}\cup\{p:p\mid N\}\cup Q_n,
\qquad
t=|\mathscr T_n|=s+1+q.
\tag{11.2}
$$

We reserve $\mathscr T_n$ for the set of framed places and $\mathbb T_n$ for a Hecke algebra.

Before passing to the relative problem, audit the absolute defect. Absolute irreducibility gives $h^0(\mathbf Q,W)=0$, while (1.5) gives $h^0(\mathbf Q,W(1))=0$. At $\ell$, (1.7) and Book 67 give

$$
\dim L_\ell-h^0(\mathbf Q_\ell,W)=1-0=1.
\tag{11.2a}
$$

At every $p\mid N$, (2.6a) gives zero; every unramified place also contributes zero; and the real place contributes $-1$. The Wiles formula therefore gives

$$
h^1_{\mathcal L}(\mathbf Q,W)
-h^1_{\mathcal L^\perp}(\mathbf Q,W(1))
=1-1=0,
\qquad
h^1_{\mathcal L}(\mathbf Q,W)=q.
\tag{11.2b}
$$

Thus the minimal datum is balanced. Each of the $q$ ordered auxiliary conditions has a one-dimensional quotient over the unramified condition, while the selected localization matrix kills the entire auxiliary dual Selmer group. The exact Poitou--Tate sequence in Section 11.5 shows that these two effects cancel rather than add: the unframed auxiliary tangent dimension remains exactly $q$. This is the sharp absolute assertion in TW6; it is separate from the relative number $q_{\mathscr T_n}$ below.

The absolute number $q$ in (11.1) selects auxiliary primes. The relative number $q_{\mathscr T_n}$ below measures the obstruction rank after the full local rings have been placed in the base. They are different cohomology groups and are never substituted for one another.

Use the definitions of Book 68 exactly:

$$
g_{\mathscr T_n}
=h^1_{\mathcal L,\mathscr T_n}(\mathbf Q,W)
+\sum_{v\in\mathscr T_n}h^0(\mathbf Q_v,\operatorname{ad}\bar\rho)
-h^0(\mathbf Q,\operatorname{ad}\bar\rho),
\tag{11.3}
$$

and

$$
q_{\mathscr T_n}
=\dim_k
H^1_{(\mathcal L^0_{\mathscr T_n})^\perp}
(\mathbf Q,W(1)).
\tag{11.4}
$$

Here $\mathcal L^0_{\mathscr T_n}$ is the locally based condition used for the partially framed problem; it is not obtained by replacing every $L_v$ with zero in the unframed Selmer group without the framing terms in (11.3).

Book 68 first gives the strict/relaxed duality identity

$$
\begin{aligned}
h^1_{\mathcal L,\mathscr T_n}(\mathbf Q,W)
-q_{\mathscr T_n}
={}&h^0(\mathbf Q,W)-h^0(\mathbf Q,W(1))\\
&+\sum_{v\notin\mathscr T_n}
\bigl(\dim L_v-h^0(\mathbf Q_v,W)\bigr)
-\sum_{v\in\mathscr T_n}h^0(\mathbf Q_v,W).
\end{aligned}
\tag{11.4a}
$$

Because $\ell$ is odd, $\operatorname{ad}\bar\rho=k\oplus W$. Hence

$$
h^0(\mathbf Q_v,\operatorname{ad}\bar\rho)
=1+h^0(\mathbf Q_v,W),
\qquad
h^0(\mathbf Q,\operatorname{ad}\bar\rho)=1,
\tag{11.4b}
$$

the last equality using absolute irreducibility. Adding the framing correction in (11.3) to (11.4a) cancels the local $W$-invariants at every place of $\mathscr T_n$. The resulting fixed-determinant formula is

$$
g_{\mathscr T_n}-q_{\mathscr T_n}
=|\mathscr T_n|-1-h^0(\mathbf Q,W(1))
+\sum_{v\notin\mathscr T_n}
\bigl(\dim L_v-h^0(\mathbf Q_v,W)\bigr),
\tag{11.5}
$$

where the sum runs over the remaining places of the global deformation problem, including infinity. Every finite conditioned place is in $\mathscr T_n$. By (1.5) the global dual invariant term is zero. At the real place $L_\infty=0$ and $h^0(\mathbf R,W)=1$. Hence

$$
g_{\mathscr T_n}-q_{\mathscr T_n}
=t-1-1=t-2.
\tag{11.6}
$$

The second subtraction in (11.6) is the real oddness term. Losing it produces $t-1$ and destroys the final square presentation.

### 11.2 Local framed dimensions

The relative dimensions of the framed local bases are:

| Place | Framed local base | Relative dimension |
|---|---|---:|
| $\ell$ | finite flat of type $(0,1)$ | $4$ over $\mathcal O$ |
| $p\mid N$ | fixed-sign nonzero Steinberg | $3$ over $\mathcal O$ |
| $v\in Q_n$ | ordered Taylor--Wiles | $3$ over $\Lambda_v$ |

The dimension $4$ at $\ell$ consists of the genuine finite-flat coordinate and three framing directions. At $p\mid N$, the local type has no genuine unframed parameter, leaving three framing directions. At $v\in Q_n$, the ordered unramified coordinate $X_v$ and the two eigenline-position coordinates $Y_v,Z_v$ give dimension $3$ over $\Lambda_v$. The ordered residual centralizer is a torus, so only two new frame directions are added to the one-dimensional unframed ring.

### 11.3 Gauge variables and the framed presentation

The partially framed global functor remembers a local basis at each of the $t$ places. Its gauge extension count is

$$
c_{\mathscr T_n}
=4t-h^0(\mathbf Q,\operatorname{ad}\bar\rho)
=4t-1,
\tag{11.7}
$$

because absolute irreducibility gives

$$
h^0(\mathbf Q,\operatorname{ad}\bar\rho)=1.
\tag{11.8}
$$

The count is not $3t$. Fixed determinant controls deformations of the representation, but a change of a chosen $2\times2$ local basis has four matrix entries. Only the single global scalar stabilizer is divided out. Confusing local fixed-determinant tangent dimensions with gauge torsors loses $t-1$ variables.

The completed framed local base is, noncanonically,

$$
R_{\mathrm{loc},n}
\simeq
\Lambda_n[[L_1,\ldots,L_{d_{\mathrm{loc}}}]],
\qquad
d_{\mathrm{loc}}=4+3s+3q.
\tag{11.8a}
$$

No coordinate in (11.8a) is counted in the relative tangent rank (11.3). The complete relative Selmer complex gives a finite free presentation complex over this base. If its source and obstruction ranks at one level are $G_n^\square$ and $b_n^\square$, then (11.6) gives

$$
G_n^\square-b_n^\square=t-2.
\tag{11.8b}
$$

This is an equality of the chosen complex ranks, not an assertion that $b_n^\square$ is the minimal number of equations. A complete effective obstruction space gives a generating relation map with possible redundant rows. Uniform boundedness permits simultaneous padding: adding a variable $Z$ together with the actual linear relation $Z=0$ raises both ranks by one and contributes an acyclic unit block. Choose one padded pair of ranks $G^\square,b^\square$ for every $n$, padding further if necessary so that $G^\square\ge s+q$. Then

$$
b^\square=G^\square-t+2.
\tag{11.9}
$$

Adding a variable with a zero relation would instead change the represented ring and falsify the rank count. Appending a redundant relation row without a variable does not change the ring, but it can make a presentation determinant zero. The three ranks $d_{\mathrm{loc}}$, $G^\square$, and $b^\square$ therefore remain in separate columns. None of this padded relative data is substituted for the minimal absolute source used in Section 11.6.

### 11.4 Exact frame removal and the square presentation

Now remove all $\mathscr T_n$-frames by the regular frame-extension map of Books 68 and 74. The partially framed global ring is a formally smooth extension of the unframed ring by exactly $c_{\mathscr T_n}=4t-1$ variables. Before frame removal, the absolute presentation source has

$$
d_{\mathrm{loc}}+G^\square
$$

variables over $\Lambda_n$ and $b^\square$ relation rows. Choosing coordinates on the regular frame torsor and deleting its $4t-1$ smooth variables leaves

$$
\begin{aligned}
d_{\mathrm{loc}}+G^\square-c_{\mathscr T_n}
&=(4+3s+3q)+G^\square-(4t-1)\\
&=G^\square-s-q+1
\end{aligned}
\tag{11.9a}
$$

source variables and introduces no relation. This calculation, rather than an informal subtraction of three variables per place, counts every local-base and gauge coordinate once. Set

$$
G=G^\square-s-q.
\tag{11.10}
$$

Frame removal deletes those smooth source variables but introduces no new obstruction relation, so

$$
b=b^\square.
\tag{11.11}
$$

Using $t=s+1+q$ in (11.9),

$$
b=b^\square
=G^\square-(s+1+q)+2
=G+1.
\tag{11.12}
$$

Equations (11.9a) and (11.12) show that the frame-removed source and relation modules have the same rank $b=G+1$. The surviving one is the net finite-flat direction at $\ell$: the $+1$ coefficient-prime contribution in (11.2a) balances the $-1$ real contribution in (11.2b), while the other local and gauge coordinates cancel. After derived diamond augmentation and cancellation of every acyclic padding pair, the minimal ring has a stable square presentation

$$
R^{\min}
\simeq
\mathcal O[[Y_1,\ldots,Y_b]]/(f_1,\ldots,f_b),
\qquad
b=G+1.
\tag{11.13}
$$

At this stage (11.13) is a presentation with a square relation matrix, not a proof that the $f_i$ form a regular sequence and not a proof that $R^{\min}$ is finite over $\mathcal O$. In particular, the determinant of this chosen presentation cannot eliminate the kernel. Those conclusions will instead follow from the unpadded absolute patch below.

### 11.5 The exact unframed auxiliary count

Write $\mathcal L_{Q_n}$ for the auxiliary Selmer condition and $L_v^{\mathrm{ur}}$ for the unramified tangent condition at $v\in Q_n$. Poitou--Tate gives the exact segment

$$
\begin{aligned}
0\longrightarrow H^1_{\mathcal L}(\mathbf Q,W)
&\longrightarrow H^1_{\mathcal L_{Q_n}}(\mathbf Q,W)
\longrightarrow
\bigoplus_{v\in Q_n}L_v^{\mathrm{TW}}/L_v^{\mathrm{ur}}\\
&\longrightarrow
H^1_{\mathcal L^\perp}(\mathbf Q,W(1))^\vee
\longrightarrow
H^1_{\mathcal L_{Q_n}^\perp}(\mathbf Q,W(1))^\vee
\longrightarrow0.
\end{aligned}
\tag{11.14}
$$

Each summand in the middle is one-dimensional. The final group is zero by the choice of $Q_n$, and the preceding localization map is the $q$-by-$q$ matrix made invertible in Section 6.1. It is therefore an isomorphism. Exactness of (11.14), together with (11.2b), gives

$$
H^1_{\mathcal L}(\mathbf Q,W)
\xrightarrow{\sim}
H^1_{\mathcal L_{Q_n}}(\mathbf Q,W),
\qquad
h^1_{\mathcal L_{Q_n}}(\mathbf Q,W)=q.
\tag{11.15}
$$

The tangent space of the absolute unframed ring $R_n$ is the right-hand group in (11.15). Hence

$$
\dim_k
\frac{\mathfrak m_{R_n}}
{\mathfrak m_{R_n}^2+\varpi R_n}=q.
\tag{11.16}
$$

Choose a tangent basis and lifts. Topological Nakayama gives a continuous surjection of complete local $\mathcal O$-algebras

$$
\beta_n:P:=\mathcal O[[X_1,\ldots,X_q]]
\twoheadrightarrow R_n.
\tag{11.17}
$$

This is an **absolute** presentation with exactly $q$ source variables; it is not the relative framed source of Sections 11.2--11.4. No assertion is made that $\ker\beta_n$ has a uniformly bounded number of generators. If $q=0$, (11.17) reads $\mathcal O\twoheadrightarrow R_n$.

### 11.6 Patching from the minimal absolute source

Set

$$
S:=S_\infty=\mathcal O[[Z_1,\ldots,Z_q]],
\qquad
\mathfrak a=(Z_1,\ldots,Z_q).
\tag{11.18}
$$

The named diamond generators give maps $S\to\Lambda_n\to R_n$. For each $i$, choose $h_{n,i}\in\mathfrak m_P$ lifting the image of $Z_i$ through (11.17), and let

$$
\alpha_n:S\longrightarrow P,
\qquad Z_i\longmapsto h_{n,i}.
\tag{11.19}
$$

Then $\beta_n\alpha_n$ is the diamond map. The level equation

$$
(1+h_{n,i})^{\ell^n}-1\in\ker\beta_n
\tag{11.20}
$$

records that the $i$-th diamond generator has order $\ell^n$.

We now spell out the finite-shadow patch, because retaining only modules would lose the augmentation needed below. At precision $d$, take the standard finite quotient $C_d=S/\mathfrak b_d$ of Book 74. For sufficiently large $n$, put

$$
A_{n,d}=\operatorname{im}\!\left(
P\longrightarrow
\operatorname{End}_{C_d}(M_n^+/\mathfrak b_dM_n^+)
\right).
$$

After a $\Lambda_n$-basis is chosen, the module is $C_d^r$. Each $A_{n,d}$ is a finite local quotient of $P$. Only finitely many image subalgebras of the fixed finite ring $\operatorname{End}_{C_d}(C_d^r)$ occur, so their maximal-ideal nilpotence exponents have one uniform bound. Choose an increasing cofinal function $\nu(d)$ beyond that bound and set

$$
P_d=P/\mathfrak m_P^{\nu(d)},
\qquad
R_{n,d}=R_n/\mathfrak m_{R_n}^{\nu(d)}
=P/\bigl(\ker\beta_n+\mathfrak m_P^{\nu(d)}\bigr).
\tag{11.20a}
$$

The last equality uses $\beta_n(\mathfrak m_P)=\mathfrak m_{R_n}$. These ring shadows are defined independently of the action image $A_{n,d}$. The local surjection $R_n\to R^{\min}$ and the free module augmentation give finite exact sequences

$$
\begin{gathered}
0\longrightarrow\mathfrak a_nR_{n,d}
\longrightarrow R_{n,d}
\longrightarrow
R^{\min}/\mathfrak m_{R^{\min}}^{\nu(d)}
\longrightarrow0,\\
0\longrightarrow
\mathfrak a(M_n^+/\mathfrak b_dM_n^+)
\longrightarrow M_n^+/\mathfrak b_dM_n^+
\longrightarrow M^{\min}/\varpi^dM^{\min}
\longrightarrow0.
\end{gathered}
\tag{11.20b}
$$

Mark simultaneously:

1. the ideal $\ker(P_d\to R_{n,d})$;
2. the elements $h_{n,i}$ in $P_d$;
3. the matrices of the $P$-action on the marked $C_d$-basis of $M_n^+/\mathfrak b_dM_n^+\simeq C_d^r$;
4. both exact sequences in (11.20b), their action square, and the saturated acting-order quotient implementing (9.13) at finite precision; and
5. the fixed canonical action of $R^{\min}/\mathfrak m_{R^{\min}}^{\nu(d)}$ on the corresponding quotient of $M^{\min}/\varpi^dM^{\min}$, together with the pairing-compatible companion shadows required by TW8.

Here $r=\operatorname{rank}_{\mathcal O}M^{\min}>0$. Every ring, module, ideal set, and matrix set at fixed precision is finite because $k$ is finite. In particular, a finite ring has only finitely many ideals, so the diagonal argument needs no uniform relation tuple for $\ker\beta_n$. Refine the Book 73 finite tree so that the marked diagram at precision $d+1$ reduces to the one at precision $d$. The cofinality of $\nu(d)$ ensures that the bottom ring shadows recover all of $R^{\min}$. This is precisely where the pairing-compatible shadows in Infrastructure I, clause 9, are used; the new marks are ideals, actions, and augmentations of the same finite diagrams.

Taking inverse limits gives

$$
R_\infty=P/I_\infty,
\qquad
M_\infty\simeq S^r,
\qquad
P\longrightarrow R_\infty
\longrightarrow A_\infty\subseteq\operatorname{End}_S(M_\infty),
\tag{11.21}
$$

where $A_\infty$ is the image of the patched action. It also gives elements $h_i\in\mathfrak m_P$ and a map

$$
\alpha:S\longrightarrow P,
\qquad Z_i\longmapsto h_i,
\tag{11.22}
$$

such that the composite $S\xrightarrow{\alpha}P\to A_\infty$ is scalar multiplication on $M_\infty$. Finite Mittag--Leffler exactness gives the quotient and action maps in (11.21); it does not create arithmetic transition maps between the original, nonnested $Q_n$. The relations (11.20) disappear in the inverse limit because $(1+h)^{\ell^n}-1$ tends to zero at every fixed Artinian precision for $h\in\mathfrak m_P$.

Let $H=(h_1,\ldots,h_q)P$. At finite level, the images of the $h_{n,i}$ generate $\mathfrak a_nR_n$, so

$$
\frac{\ker\beta_n+(h_{n,1},\ldots,h_{n,q})}
{\ker\beta_n}
=\mathfrak a_nR_n.
\tag{11.23}
$$

Consequently the finite-level control is represented on this absolute source by

$$
P/\bigl(\ker\beta_n+(h_{n,1},\ldots,h_{n,q})\bigr)
\xrightarrow{\sim}R^{\min},
\qquad
M_n^+/(h_{n,1},\ldots,h_{n,q})M_n^+
\xrightarrow{\sim}M^{\min}.
\tag{11.23a}
$$

The exact finite sequences (11.20b), together with the finite reductions of the ideal and action identities (11.23)--(11.23a), were retained in every shadow; no infinite augmentation target was inserted into a finite diagram. Their finite kernels are Mittag--Leffler, and finitely generated ideals in the complete rings are closed. Passing along the cofinal $\nu(d)$-filtration therefore gives the **exact**, action-compatible augmentations

$$
R_\infty/\mathfrak aR_\infty
=R_\infty/HR_\infty
\xrightarrow{\sim}R^{\min},
\qquad
M_\infty/HM_\infty
\xrightarrow{\sim}M^{\min}.
\tag{11.24}
$$

Thus neither equality in (11.24) is inferred from ordinary tensoring of an unknown flat deformation ring.

### 11.7 Regularity, freeness, and faithful descent

We first isolate the commutative algebra that turns equal variable counts into rigidity.

**Lemma 11.1 (equal-variable rigidity).** Let $S=\mathcal O[[Z_1,\ldots,Z_q]]$ and $P=\mathcal O[[X_1,\ldots,X_q]]$. Let $L\ne0$ be finite free over $S$. Suppose $\alpha:S\to P$ is a continuous local $\mathcal O$-algebra map and $\psi:P\to\operatorname{End}_S(L)$ is a continuous unital action homomorphism, giving

$$
S\xrightarrow{\alpha}P
\xrightarrow{\psi}\operatorname{End}_S(L)
\tag{11.25}
$$

Assume $\psi(\alpha(s))=s\operatorname{id}_L$ for every $s\in S$. Then $\psi$ is injective, $P$ is finite free over $S$, and $L$ is finite free over $P$.

**Proof.** Put $A=\psi(P)$. It is an $S$-submodule of the finite free module $\operatorname{End}_S(L)$, hence is finite over the Noetherian ring $S$. Since $L$ is nonzero and $S$-free, scalar multiplication is faithful, so $S\hookrightarrow A$. The finite integral extension has

$$
\dim A=\dim S=q+1.
\tag{11.26}
$$

The surjection $P\twoheadrightarrow A$ and $\dim P=q+1$ force $\ker\psi=0$: if it contained $0\ne f$, then the regular domain $P$ would give $\dim A\le\dim P/(f)\le q$. Hence $A=P$, and $P$ is finite over $S$.

The ideal $\mathfrak m_SP$ is $\mathfrak m_P$-primary, so depth is unchanged when computed over either local ring. Since $P$ is regular of dimension $q+1$,

$$
\operatorname{depth}_SP
=\operatorname{depth}_PP=q+1.
\tag{11.27}
$$

Auslander--Buchsbaum over the regular ring $S$ makes $P$ finite free over $S$. Likewise $L$ is $S$-free, so

$$
\operatorname{depth}_PL
=\operatorname{depth}_SL=q+1;
\tag{11.28}
$$

Auslander--Buchsbaum over $P$ makes $L$ finite free over $P$. $\square$

Apply the lemma to (11.21)--(11.22). The action map $P\to\operatorname{End}_S(M_\infty)$ is injective. Since it factors through $P/I_\infty$, necessarily

$$
q+1=\dim A_\infty
\le\dim R_\infty
\le\dim P=q+1.
\tag{11.28a}
$$

Thus $\dim R_\infty=\dim P$. A nonzero $I_\infty$ would contain a nonzero nonzerodivisor of the regular domain $P$ and force $\dim(P/I_\infty)\le q$. Equivalently, injectivity of the action already forces

$$
I_\infty=0,
\qquad
R_\infty=P=A_\infty,
\qquad
M_\infty\simeq P^e
\quad(e>0).
\tag{11.29}
$$

This proves patched faithfulness rather than assuming it. Combining (11.24) and (11.29) yields

$$
M^{\min}\simeq
(R^{\min})^e.
\tag{11.30}
$$

The canonical action on $M^{\min}$ factors through the surjection $R^{\min}\twoheadrightarrow\mathbb T^{\min}$, and $\mathbb T^{\min}$ acts faithfully by definition. Therefore

$$
\ker(R^{\min}\to\mathbb T^{\min})
=\operatorname{Ann}_{R^{\min}}M^{\min}=0.
\tag{11.31}
$$

Together with (5.5), this proves

$$
\boxed{R^{\min}\xrightarrow{\sim}\mathbb T^{\min}.}
\tag{11.32}
$$

Infrastructure I gives $M^{\min}\simeq\mathbb T^{\min}$, so comparison with (11.30) forces $e=1$. The same argument shows $P$ is finite free over $S$. Consequently $h_1,\ldots,h_q$, the images of the regular parameters $Z_1,\ldots,Z_q$, form a $P$-regular sequence and

$$
B:=R^{\min}=\mathbb T^{\min}
\simeq P/(h_1,\ldots,h_q)
\tag{11.33}
$$

is a finite-flat complete intersection over $\mathcal O$.

The exact tangent count is essential. The two-branch model $S[[u]]/(u(u-\varpi))$ acting on its quotient $S$ has one more residual tangent generator than the $q$ diamond variables. Its minimal absolute source has dimension $q+2$, so the dimension argument in (11.26) cannot make that source inject into the acting quotient. The finite model $\mathcal O[[u]]/(u(u-\varpi))\twoheadrightarrow\mathcal O$ is excluded for the same reason: it cannot occur in a tower satisfying (11.15)--(11.17) and carrying the faithful free $S$-diamond action. Thus (11.32) is not a disguised component-coverage assumption.

## 12. Post-comparison cotangent and congruence theory

The equality (11.32) has already been proved by absolute patching. Only now do deformation cotangents and automorphic congruences live over one ring. This order matters: Tate self-duality of a Selmer complex and mass/Poincaré self-duality of an automorphic complex do not, by themselves, supply a cross-complex morphism or make a global period a unit. The comparison below is the intrinsic complete-intersection comparison over the common ring; it is a consequence of $R=\mathbb T$, not an input to it.

### 12.1 The common complete-intersection presentation

Write

$$
B=R^{\min}=\mathbb T^{\min}
=P/(g_1,\ldots,g_q),
\qquad g_i=h_i=\alpha(Z_i),
\tag{12.1}
$$

using (11.33). The map $\alpha:S\to P$ is finite free, so the images of the regular parameters $Z_1,\ldots,Z_q$ form a $P$-regular sequence. Thus (12.1) is a complete-intersection presentation, not merely a square presentation.

Fix the characteristic-zero source character

$$
\lambda:B\longrightarrow\mathcal O.
\tag{12.2}
$$

After translating the $X_j$ by elements of $\varpi\mathcal O$, assume $\lambda(X_j)=0$. The target $B=\mathbb T^{\min}$ is finite flat with reduced generic fiber by Infrastructure II. It follows that $B$ is reduced, since a nilpotent dies in the generic fiber and $B$ is $\mathcal O$-torsion-free. Being a finite-flat complete intersection, $B$ is also Gorenstein over $\mathcal O$.

### 12.2 The deformation cotangent complex

Let $I=\ker\lambda$ and $\Phi_B=I/I^2$. The correct linear object attached to (12.1) is the evaluated conormal complex

$$
C_\lambda=
\left[
\frac{(g_1,\ldots,g_q)}{(g_1,\ldots,g_q)^2}
\otimes_{B,\lambda}\mathcal O
\xrightarrow{d}
\Omega_{P/\mathcal O}\otimes_{P,\lambda}\mathcal O
\right].
\tag{12.3}
$$

With the ordered bases $g_1,\ldots,g_q$ and $dX_1,\ldots,dX_q$, its matrix is

$$
J_\lambda=
\left(
\lambda\!\left(\frac{\partial g_i}{\partial X_j}\right)
\right)_{1\le i,j\le q}.
\tag{12.4}
$$

The conormal sequence gives

$$
\mathcal O^q\xrightarrow{J_\lambda}
\mathcal O^q\longrightarrow\Phi_B\longrightarrow0,
\qquad
\operatorname{Fitt}_{\mathcal O}^0(\Phi_B)=(\det J_\lambda).
\tag{12.5}
$$

This complex is the linearization of the regular sequence. The Koszul complex $K(g;P)$ itself resolves $B$ over $P$, but after evaluation at $\lambda$ its multiplication differentials are zero; it must not be confused with (12.3) or claimed to present $\Phi_B$.

### 12.3 The automorphic congruence complex

Let $K=\operatorname{Frac}(\mathcal O)$ and let $e_\lambda$ be the idempotent of the distinguished factor of $B\otimes K$. Put

$$
M_\lambda=M^{\min}\cap e_\lambda(M^{\min}\otimes K),
\qquad
P_\lambda=e_\lambda M^{\min}.
\tag{12.6}
$$

The primary--companion pairing, with the adjoint identification of the two acting orders, identifies $P_\lambda$ with $M_\lambda^\vee$. The resulting two-term branch complex is

$$
A_\lambda=[M_\lambda\longrightarrow M_\lambda^\vee].
\tag{12.7}
$$

Infrastructure I supplies the separate branch-saturation statement

$$
M_\lambda=\eta_BP_\lambda,
\qquad
\eta_B=\lambda(\operatorname{Ann}_B I).
\tag{12.8}
$$

Thus $\det A_\lambda$ is the congruence ideal $\eta_B$. Perfect self-duality alone would identify the projected lattice with a dual lattice; it would not imply (12.8). The companion block remains essential because the adjoint of the primary auxiliary operator is the companion operator, not itself.

### 12.4 The conormal--dualizing comparison

Because $g_1,\ldots,g_q$ is regular, $K(g;P)$ is a finite free resolution of $B$. Its Koszul self-duality, followed by the relative residue of Book 71, gives a complete-intersection dualizing generator

$$
\theta_{\mathrm{CI}}:B\xrightarrow{\sim}
\operatorname{Hom}_{\mathcal O}(B,\mathcal O).
\tag{12.9}
$$

The top exterior linearization of this construction is $\det J_\lambda$. Equivalently, the distinguished generic idempotent has residue $1/\det J_\lambda$, so

$$
B\cap Ke_\lambda=(\det J_\lambda)e_\lambda.
\tag{12.10}
$$

On the automorphic side, the adjoint involution is the identity on the minimal commutative order: at a good prime $T_r^*=S_r^{-1}T_r=T_r$ after the trivial-central-character specialization, and the retained bad-prime operators act through their fixed local-type scalars. Choose $B$-bases $m_+$ and $m_-$ under the identifications of the augmented primary and companion modules with $B$. Define

$$
\theta_{\mathrm{aut}}(a)(c)
=\langle acm_+,m_-\rangle.
$$

Adjointness makes this map $B$-linear, and perfectness makes it an isomorphism. Thus it is another integral dualizing generator

$$
\theta_{\mathrm{aut}}:B\xrightarrow{\sim}
\operatorname{Hom}_{\mathcal O}(B,\mathcal O).
\tag{12.11}
$$

There is therefore a unique $b\in B^\times$ with

$$
\theta_{\mathrm{aut}}=b\theta_{\mathrm{CI}}.
\tag{12.12}
$$

Book 71's residue normalization identifies the $\lambda$-weight of $\theta_{\mathrm{CI}}$ with $1/\det J_\lambda$. After the Koszul orientation is fixed, the induced comparison between the determinant line of $C_\lambda$ and that of the branch complex $A_\lambda$ therefore has scalar $\pm\lambda(b)\in\mathcal O^\times$. This is the promised global period-unit statement. Its proof is that both integral maps are generators of the same rank-one $B$-module after $R=\mathbb T$; it is not inferred from two unrelated self-dualities, from scalar residual endomorphisms, or from a product of unnamed local factors. This is a determinant-line comparison, not a claimed quasi-isomorphism between $C_\lambda$ and $A_\lambda$, whose terms have ranks $q$ and $1$ respectively.

### 12.5 Integral normalization and the global unit

The generators in (12.9)--(12.11) use the normalizations already fixed before patching: arithmetic Frobenius and cyclotomic determinant; the adapted Steinberg basis with primitive residual monodromy; the oriented split-prime sign and the division-uniformizer at $p_0$; ordered Taylor--Wiles eigenlines and named diamond generators; and the primary--companion mass pairing with diamond inversion. Changing a basis, a Koszul orientation, a primitive monodromy lift, or a class-set representative multiplies the corresponding generator by a unit. The finite-flat scalar-endomorphism hypothesis at $\ell$ supplies representability and the sharp local tangent calculation, but it is not asserted to control the global period.

The exact augmentation used here is (11.24). Before regularity was proved, derived tensor was the safe language for relation complexes; the patch instead retained the finite exact ideal and module sequences and passed them through Mittag--Leffler inverse limits. After (11.29), $P$ is finite free over $S$, so

$$
P\otimes_S^{\mathbf L}\mathcal O
\simeq P\otimes_S\mathcal O=B,
\qquad
M_\infty\otimes_S^{\mathbf L}\mathcal O
\simeq M_\infty\otimes_S\mathcal O=M^{\min},
\tag{12.13}
$$

and no hidden higher $\operatorname{Tor}$ remains. This derived base-change compatibility is a consequence of patched freeness.

### 12.6 The Fitting--congruence equality

The Jacobian congruence formula of Book 71 applied to (12.1), or equivalently (12.8)--(12.12), gives

$$
\boxed{
\operatorname{Fitt}_{\mathcal O}^0(\Phi_{R^{\min}})
=(\det J_\lambda)
=\eta_B
=\eta_{\mathbb T^{\min}}.}
\tag{12.14}
$$

The ideal is nonzero because the distinguished point is an isolated factor of the reduced generic fiber. Branch saturation is required to identify the automorphic module determinant with the ring congruence ideal; without (12.8), a nonunit lattice index could intervene.

Equation (12.14) is deliberately post hoc. It checks that the now common complete intersection has the expected cotangent and congruence invariants. Neither (12.14) nor the unit in (12.12) appears anywhere in the proof of (11.32).

## 13. The numerical audit and structural consequences

The kernel was eliminated in Section 11.7. This chapter records how the resulting complete intersection fits the numerical framework of Books 71 and 75 and collects the structural consequences without reversing the logical order.

### 13.1 The specialization square

The common augmentation gives the square

$$
\begin{array}{ccc}
R^{\min}&\xrightarrow{\sim}&\mathbb T^{\min}\\
\lambda\downarrow&&\downarrow\lambda\\
\mathcal O&=&\mathcal O.
\end{array}
\tag{13.1}
$$

Infrastructure II gives finite flatness and generically reducedness on the Hecke side; Section 11.7 transports them to the deformation side and proves the complete-intersection presentation. Infrastructure I gives a faithful rank-one module, its perfect primary--companion duality, and the saturated distinguished branch. Section 12.4 compares the two dualizing generators only after all these objects are over $B$.

### 13.2 The Wiles--Lenstra criterion as an audit

The numerical hypothesis of Book 75, Theorem 16.2, is

$$
\operatorname{length}_{\mathcal O}\Phi_{R^{\min}}
\le
\operatorname{length}_{\mathcal O}
(\mathcal O/\eta_{\mathbb T^{\min}}),
\tag{13.2}
$$

equivalently

$$
\eta_{\mathbb T^{\min}}
\subseteq
\operatorname{Fitt}_{\mathcal O}^0(\Phi_{R^{\min}}).
\tag{13.3}
$$

Equation (12.14) verifies this with equality. Thus the specialization square passes the Wiles--Lenstra audit, but this is a consistency check, not the kernel-killing step: the criterion is not invoked to prove the equality already obtained in (11.32). For later reference,

$$
\boxed{R^{\min}\xrightarrow{\sim}\mathbb T^{\min}.}
\tag{13.4}
$$

### 13.3 Consequences proved only after equality

The common ring $B$ is finite flat and a complete intersection by (11.33), reduced by Section 12.1, and therefore Gorenstein. Infrastructure I and (11.32) give

$$
M^{\min}\simeq B
\tag{13.5}
$$

as a free rank-one deformation module. The stronger patched conclusion was proved before descent:

$$
R_\infty=P=A_\infty,
\qquad
M_\infty\simeq P.
\tag{13.6}
$$

Thus finite-level freeness is not being used to infer patched faithfulness. Rather, exact tangent count and equal-variable rigidity first prove patched freeness and faithfulness; exact augmentation then descends them. Finally, (12.14) records the common ring's intrinsic Fitting--congruence equality.

## 14. Modularity extraction and the reusable theorem

An equality of universal rings becomes a lifting theorem by evaluating it at a characteristic-zero Galois point. This chapter turns such a point into a Hecke character, transfers the corresponding quaternionic packet to a classical newform, and identifies the two Galois representations. It then collects the precise hypotheses and conclusions into the reusable rational theorem.

### 14.1 From a minimal point to an eigenform

Let $E'/E$ be finite with ring of integers $\mathcal O'$, and let

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\mathcal O')
\tag{14.1}
$$

be a lift of $\bar\rho$ satisfying the minimal deformation problem. Universality gives a point

$$
x_\rho:R^{\min}\longrightarrow\mathcal O'.
\tag{14.2}
$$

Through (13.4), this is a Hecke character of $\mathbb T^{\min}$. Since the Hecke order acts faithfully on the exact-level definite packet and has the equal saturated curve realization, the character occurs in a weight-two automorphic eigenpacket of level $N$, trivial central character, and the prescribed Steinberg signs. Jacquet--Langlands transfers it to a weight-two newform $f$ on $\operatorname{GL}_2/\mathbf Q$.

The newform has exact level $N$: it is Steinberg at every $p\mid N$ and unramified away from $N\ell$. The local sign is $\epsilon_p$, and its determinant is cyclotomic.

### 14.2 Equality of Galois representations

For every $r\nmid N\ell$, (5.4) gives

$$
\operatorname{tr}\rho(\operatorname{Frob}_r)=a_r(f),
\qquad
\det\rho(\operatorname{Frob}_r)=r.
\tag{14.3}
$$

Equivalently, before trivializing the central operator, the common polynomial is

$$
X^2-S_r^{-1}T_rX+rS_r^{-1}.
\tag{14.4}
$$

Chebotarev makes the Frobenius classes dense, so (14.3) identifies the semisimplifications over the fraction field. A lift of an absolutely irreducible residual representation is itself irreducible, and its stable lattice is unique up to homothety. More directly, the equality of the points through (13.4) makes both representations the same specialization of the universal representation in (2.10). Hence the identification is integral, not merely an equality of characteristic-zero semisimplifications:

$$
\rho\simeq\rho_f.
\tag{14.5}
$$

The local statements at $N$ and $\ell$ were built into both families before the comparison map was defined; they are not reconstructed from (14.3).

### 14.3 Minimal modularity lifting over the rationals

**Theorem 14.1 (minimal modularity lifting over $\mathbf Q$).** Let $\ell\ge7$ and let

$$
\bar\rho:G_{\mathbf Q}\to\operatorname{GL}_2(k)
$$

be absolutely irreducible and odd, with determinant $\bar\chi_\ell$. Assume

$$
H^0(\mathbf Q,\operatorname{ad}^0\bar\rho(1))=0,
$$

the split image hypotheses of Book 72, and all parts of the clean datum in Section 1.3: nontrivial squarefree prime-to-$\ell$ conductor $N$; nonzero residual tame monodromy, fixed unramified quadratic Steinberg sign, and $p\not\equiv\pm1\pmod\ell$ at every $p\mid N$; finite-flat type $(0,1)$ and scalar endomorphisms at $\ell$; an exact-level weight-two newform source; and a definite quaternion algebra ramified at one $p_0\mid N$ and infinity.

Assume, in addition, Infrastructure I at the minimal, Iwahori, and deep levels, including its pairing-compatible finite marked shadows, and Infrastructure II for the same localized packets and ordered refinements.

Then the canonical map is an isomorphism

$$
R^{\min}\simeq\mathbb T^{\min}.
\tag{14.6}
$$

Both sides are finite flat, reduced, complete-intersection, and Gorenstein $\mathcal O$-algebras. The minimal automorphic module is free of rank one over this common ring.

For every finite extension $E'/E$ with ring of integers $\mathcal O'$, every lift

$$
\rho:G_{\mathbf Q}\to\operatorname{GL}_2(\mathcal O')
$$

that is continuous, reduces to $\bar\rho$, has determinant $\chi_\ell$, is unramified outside $N\ell$, is finite flat of type $(0,1)$ at $\ell$, and has the fixed nonzero Steinberg type at every $p\mid N$, is isomorphic to the Galois representation attached to a weight-two newform of exact level $N$, trivial central character, and the prescribed local signs.

**Proof.** Chapters 2--5 construct the exact deformation problem, the integral Hecke family, and the surjection (5.5). Chapters 6--10 construct the paired auxiliary system in the full-level-first order. Sections 11.1 and 11.5 prove the sharp equality $h^1_{\mathcal L_{Q_n}}=q$, and Sections 11.6--11.7 patch the resulting absolute $q$-variable presentations together with the separate $q$-variable diamond action. Equal-variable rigidity gives $R_\infty=P$, Auslander--Buchsbaum gives patched freeness, and exact augmentation gives (11.32), restated as (13.4). Sections 12--13 then prove the structural and post-comparison numerical conclusions; Sections 14.1--14.2 give modularity. Neither infrastructure theorem assumes the conclusion, and Book 75 is used only as an audit after equality. $\square$

## 15. The elliptic-curve theorem

For an elliptic curve, the determinant and weight-two finite-flat condition come from the Tate module, while multiplicative reduction supplies the Steinberg local type. This chapter translates the abstract hypotheses carefully, especially the residual nonvanishing that semistability alone does not guarantee. The resulting statement illustrates exactly what the minimal lifting theorem contributes.

### 15.1 Translating the hypotheses

Let $A/\mathbf Q$ be an elliptic curve and let $\ell\ge7$. Suppose $A$ has good reduction at $\ell$ and semistable reduction of nontrivial squarefree conductor $N$ away from $\ell$. The representation

$$
\rho_{A,\ell}:G_{\mathbf Q}\longrightarrow
\operatorname{GL}_2(T_\ell A)
\tag{15.1}
$$

has determinant $\chi_\ell$, is finite flat of type $(0,1)$ at $\ell$, and is Steinberg at every multiplicative prime.

To place it in Theorem 14.1, require the following residual conditions:

1. $A[\ell]$ is absolutely irreducible and odd, satisfies the split image hypotheses of Book 72, and
   $$
   H^0(\mathbf Q,\operatorname{ad}^0A[\ell](1))=0;
   \tag{15.2}
   $$
2. $\operatorname{End}_{k[G_{\mathbf Q_\ell}]}A[\ell]=k$;
3. at every $p\mid N$, the Tate-curve extension remains nonzero modulo $\ell$, its split or nonsplit multiplicative sign is fixed, and $p\not\equiv\pm1\pmod\ell$;
4. $A[\ell]$ occurs in an exact-level weight-two newform of level $N$ with those signs; and
5. Infrastructures I and II hold for the resulting localized packet, including the exact auxiliary-level and finite-shadow clauses stated in those theorems.

The nonzero Tate extension is exactly the nonzero residual tame monodromy in (2.4). Semistability alone does not imply it after reduction modulo $\ell$.

### 15.2 The conclusion

**Theorem 15.1.** Under the hypotheses of Section 15.1, $\rho_{A,\ell}$ is attached to a weight-two newform of exact level $N$. Hence $A$ is modular.

**Proof.** The representation (15.1) defines a point of $R^{\min}$. Theorem 14.1 turns that point into a newform character of $\mathbb T^{\min}$, and (14.5) identifies the two Galois representations. The equality of their good Euler factors gives equality of the $L$-function of $A$ with the newform $L$-function. $\square$

This theorem isolates the lifting argument. It does not claim that the residual modular source or Infrastructures I--II follow from the geometry of an arbitrary elliptic curve; those are independent inputs.

## 16. What changes over a totally real field

The rational proof suggests a template over a totally real field, but several dimensions and geometric realizations change at once. This chapter separates the formal deformation-theoretic pattern from the new local $\ell$-adic Hodge theory, quaternionic parity, and integral cohomology theorems that a totally real version would require.

### 16.1 The parts that formally persist

Over a totally real field $F$, one can still define fixed-determinant local deformation conditions, Selmer and dual Selmer groups, ordered Taylor--Wiles primes, diamond algebras, and primary--companion pairings. If the exact absolute auxiliary tangent dimension equals the number of diamond variables and exact marked augmentations are available, the equal-variable patching lemma of Section 11.7 formally persists.

The logical prohibitions also persist: local conditions must be checked before writing $R\to\mathbb T$; generic Jacquet--Langlands does not identify integral orders; branch projectors follow full old/new control; $U_v^*=V_v$ requires a companion block; and exact augmentation must be retained in the patch rather than inferred by tensoring a ring not yet known to be flat.

### 16.2 The new global and automorphic work

The rational proof cannot be transported by replacing $\mathbf Q$ with $F$. There are $[F:\mathbf Q]$ real terms in the Euler characteristic, and oddness contributes one balancing term at every real place. Primes above $\ell$ can be ramified and have different residue degrees, so the one-variable finite-flat calculation (2.7) must be replaced by the appropriate integral $p$-adic Hodge deformation rings.

The parity of the ramification set of a quaternion algebra also changes. A totally definite algebra is ramified at every real place, and its finite ramification set must be chosen to satisfy the global parity condition while realizing the desired local packet. The definite-to-curve comparison may involve Shimura curves only when the algebra can be split at exactly one real place; in other signatures, higher-dimensional Shimura varieties and torsion cohomology enter.

Residual multiplicity one, Ihara saturation, integral Jacquet--Langlands, and local--global compatibility must be proved for Hilbert modular packets. Most importantly for this proof, the real-place and coefficient-prime terms must yield the exact absolute tangent count matching the diamond-variable count. Therefore Theorem 14.1 is a theorem over $\mathbf Q$, while the totally real version is a new theorem with analogous architecture and a separately verified ledger.

## 17. Failure modes and diagnostic boundaries

All exclusions from Theorem 14.1 were stated in Section 1.4, before the theorem. This chapter introduces no new hypothesis. It diagnoses which proved arrow fails when one of those stated boundaries is crossed.

### 17.1 Local failures

**Zero residual monodromy.** If $\bar c_p|_{I_p}=0$, the demand that a lift have nonzero Steinberg monodromy is generically open, not represented by the closed minimal quotient used here. The framed ring (2.6), the local tangent term in (11.2b), and the automorphic saturation argument all change.

**Vexing congruences.** If $p\equiv1\pmod\ell$, the local conjugacy calculation acquires the exceptional directions excluded in Section 2.3. If $p\equiv1$ or $-1\pmod\ell$, the primitive integral Steinberg newvector lattice and pairing used in Infrastructure I can fail.

**Scalar coefficient-prime endomorphisms fail.** Then the finite-flat unframed functor may have automorphisms, the framed-to-unframed passage is not (2.7), and the count $b=G+1$ is unsupported.

**A wrong Frobenius convention.** For arithmetic Frobenius the general polynomial is (2.1). Writing $X^2-T_rX+r$ is valid only after imposing $S_r=1$.

### 17.2 Automorphic and integral failures

**Generic packet comparison only.** Generic Jacquet--Langlands can leave two different integral Hecke orders inside the same fraction algebra. Without the torsion-free order comparison of Infrastructure II, the Galois representation may live over the wrong order.

**Generic oldness only.** A new quotient with zero generic fiber can still be nonzero torsion. The unit Gram determinant and saturation in (8.6)--(8.9) are required before it is killed.

**Premature branch selection.** Projecting to $U_v-\bar\alpha_v$ before proving full Iwahori oldness can discard or conceal an integral new quotient. It also makes the source of the old-line formula (9.3) invisible.

**False self-adjointness.** Book 90 says $U_v^*=V_v$. Treating $e_\alpha^U$ as self-adjoint destroys TW8 and can change the congruence determinant. The companion module is not cosmetic.

**Module control without order control.** Coinvariants of $M_n^+$ can equal $M^{\min}$ while the image of the auxiliary Hecke order has a nonsaturated index in $\mathbb T^{\min}$. Equation (9.13) uses integral branch saturation to rule this out.

### 17.3 Numerical and logical failures

**The count $3t$.** Three is the number of framing directions in several fixed-determinant local rings; it is not the partially framed gauge count. The correct number is $4t-1$.

**Missing the real term.** The formula (11.5) gives $t-2$, not $t-1$. This is exactly what changes $b=G$ into the required $b=G+1$ after frame removal.

**Padding by zero relations.** Adding a source variable without the linear relation that kills it changes the represented ring and adds a zero row to the Jacobian. Uniform presentations use acyclic variable--relation pairs.

**Ordinary augmentation of a nonflat ring.** Before (11.29), ordinary tensoring need not preserve a ring exact sequence. Section 11.6 instead marks the finite ideal and module augmentation sequences and passes them through a Mittag--Leffler inverse limit. Only after $P$ is proved $S$-free does (12.13) identify ordinary and derived augmentation.

**Separate self-dualities treated as a cross-map.** Tate self-duality and primary--companion self-duality do not construct a morphism between the two complexes, and scalar residual endomorphisms do not make a global period a unit. This book makes no such pre-equality comparison. The unit in (12.12) is proved only after both dualizing generators live over the common complete intersection.

**Support used as faithfulness.** Even full support can miss nilpotent annihilators. Here faithfulness comes instead from $S\hookrightarrow A_\infty$, the equality $\dim S=\dim P$, and regular-domain rigidity in Lemma 11.1.

**An extra absolute generator.** The two-branch example after (11.33) has the same apparent component support but one extra residual tangent generator. Replacing the sharp count (11.15) by a framed square-presentation count would allow that example and destroy the dimension proof.

These diagnostics locate the first invalid arrow in a failed argument. They are more informative than a final dimension mismatch, because several of the errors above preserve Krull dimension while changing the integral scheme structure.

## 18. The interface with nonminimal lifting

Minimal equality is the base point for allowing new ramification, not a license to ignore new local geometry. This final chapter records the exact package exported to Book 156 and identifies the local, automorphic, and patching comparisons that must be rebuilt when the level changes.

### 18.1 What the minimal theorem exports

Book 156 may take the following package as its base point:

$$
R^{\min}\simeq\mathbb T^{\min},
\tag{18.1}
$$

the finite-flat complete-intersection and Gorenstein structure of this ring, the rank-one minimal module with its perfect pairing, the exact local tangent spaces, the normalized good-prime polynomial (2.1), the paired Taylor--Wiles system, and the equality

$$
\operatorname{Fitt}_{\mathcal O}^0
(\Phi_{R^{\min}})
=\eta_{\mathbb T^{\min}}.
\tag{18.2}
$$

It may also reuse the split-image prime-selection mechanism and the distinction among deformation augmentation, module coinvariants, and saturated Hecke-order augmentation.

### 18.2 What Book 156 must rebuild

At a newly allowed prime, the nonminimal argument must choose a represented local quotient: a specified inertial type, a closed special component, or another precise local deformation condition. If residual monodromy is zero, the generic nonzero special locus must be distinguished from its closed component. The new local tangent quotient changes both Selmer and dual Selmer, so the auxiliary-prime count must be recomputed from Poitou--Tate rather than obtained by adding a guessed local dimension.

On the automorphic side, raising the level requires new degeneracy maps, adjoints, Gram determinants, Ihara injectivity, and saturation. A level-raising congruence proves that a point exists on a component; it does not prove that the full integral Hecke order realizes every component. The Hecke-valued Galois representation must again be checked against the chosen local quotient before the upper map in a comparison diagram is written.

When the local natural transformations exist, the guiding square is

$$
\begin{array}{ccc}
R^{P}&\twoheadrightarrow&\mathbb T^{P}\\
\downarrow&&\downarrow\\
R^{\min}&\xrightarrow{\sim}&\mathbb T^{\min}.
\end{array}
\tag{18.3}
$$

The vertical arrows point in the direction dictated by the actual local deformation maps and saturated level maps; they are not formal decorations. The upper kernel still requires a newly balanced absolute patch or another genuine kernel-killing theorem. Complete-intersection and Gorenstein properties do not automatically survive a singular change of local component.

### 18.3 Final perspective

The clean minimal proof works because its local and global sources of rigidity are independent and exactly balanced. Nonzero residual monodromy makes the Steinberg condition closed. The finite-flat line at $\ell$ balances the real oddness term. Large image converts dual Selmer classes into ordered auxiliary primes. Definite class-set geometry supplies free diamond lattices and exact oldness. Integral curve reciprocity supplies the genuine Galois family. The sharp Poitou--Tate sequence then leaves exactly $q$ absolute deformation generators against exactly $q$ diamond variables.

Equal-variable rigidity, patched freeness, and exact augmentation prove

$$
R^{\min}=\mathbb T^{\min}.
$$

Only afterward do complete-intersection duality and the primitive primary--companion pairing identify cotangent and congruence determinants up to a proved global unit. The equality says exactly what minimal modularity lifting requires: every characteristic-zero point satisfying the stated local conditions is automorphic of the matching exact level and type. Book 156 changes those local conditions, so it must earn the balance again at each newly permitted prime.
