# Dickson Classification and Adequate Residual Image

## Contents

1. [The image problem in dimension two](#1-the-image-problem-in-dimension-two)
   - [From a representation to a projective action](#11-from-a-representation-to-a-projective-action)
   - [Three notions of irreducibility](#12-three-notions-of-irreducibility)
   - [Determinants, scalars, and twists](#13-determinants-scalars-and-twists)
   - [The arithmetic setting](#14-the-arithmetic-setting)
   - [Four model images](#15-four-model-images)
2. [Geometry of finite projective linear groups](#2-geometry-of-finite-projective-linear-groups)
   - [Fixed points of fractional linear transformations](#21-fixed-points-of-fractional-linear-transformations)
   - [Unipotent subgroups](#22-unipotent-subgroups)
   - [Split and nonsplit tori](#23-split-and-nonsplit-tori)
   - [Normalizers and the origin of dihedral groups](#24-normalizers-and-the-origin-of-dihedral-groups)
3. [Dickson's classification](#3-dicksons-classification)
   - [The complete statement](#31-the-complete-statement)
   - [The solvable branch](#32-the-solvable-branch)
   - [The nonsolvable branch](#33-the-nonsolvable-branch)
   - [Small coincidences and exceptional characteristics](#34-small-coincidences-and-exceptional-characteristics)
   - [Orders, orbits, and recognition](#35-orders-orbits-and-recognition)
   - [Two finite-field portraits](#36-two-finite-field-portraits)
4. [Irreducible matrix representations](#4-irreducible-matrix-representations)
   - [Eliminating point stabilizers and cyclic groups](#41-eliminating-point-stabilizers-and-cyclic-groups)
   - [The dihedral induction theorem](#42-the-dihedral-induction-theorem)
   - [Exceptional and large images](#43-exceptional-and-large-images)
   - [The projective trace field](#44-the-projective-trace-field)
   - [Central lifts and determinants](#45-central-lifts-and-determinants)
5. [Restriction and scalar extension](#5-restriction-and-scalar-extension)
   - [Coefficient extension changes coordinates, not kernels](#51-coefficient-extension-changes-coordinates-not-kernels)
   - [Normal restriction and Clifford theory](#52-normal-restriction-and-clifford-theory)
   - [Cyclotomic restriction](#53-cyclotomic-restriction)
   - [Disjoint base change](#54-disjoint-base-change)
6. [Local arithmetic constraints](#6-local-arithmetic-constraints)
   - [Fields cut out by full and projective representations](#61-fields-cut-out-by-full-and-projective-representations)
   - [Conductor restrictions away from the coefficient prime](#62-conductor-restrictions-away-from-the-coefficient-prime)
   - [Finite flatness at the coefficient prime](#63-finite-flatness-at-the-coefficient-prime)
   - [Quadratic characters in the dihedral branch](#64-quadratic-characters-in-the-dihedral-branch)
   - [Exceptional quotients and ray data](#65-exceptional-quotients-and-ray-data)
   - [Local projective inertia by cases](#66-local-projective-inertia-by-cases)
7. [The hardly-ramified image ledger](#7-the-hardly-ramified-image-ledger)
   - [An exact reusable datum](#71-an-exact-reusable-datum)
   - [The small-image alternatives](#72-the-small-image-alternatives)
   - [Oddness and complex conjugation](#73-oddness-and-complex-conjugation)
   - [What local hypotheses do and do not eliminate](#74-what-local-hypotheses-do-and-do-not-eliminate)
   - [A worked rational ledger](#75-a-worked-rational-ledger)
8. [Cohomology of the image](#8-cohomology-of-the-image)
   - [The adjoint module](#81-the-adjoint-module)
   - [Averaging and prime-to-ell groups](#82-averaging-and-prime-to-ell-groups)
   - [Central scalars and inflation--restriction](#83-central-scalars-and-inflation--restriction)
   - [Cohomology for groups containing special linear groups](#84-cohomology-for-groups-containing-special-linear-groups)
   - [The adjoint module in the dihedral case](#85-the-adjoint-module-in-the-dihedral-case)
9. [Adequacy](#9-adequacy)
   - [Why absolute irreducibility is not enough](#91-why-absolute-irreducibility-is-not-enough)
   - [Definition and elementary permanence](#92-definition-and-elementary-permanence)
   - [The semisimple spanning condition](#93-the-semisimple-spanning-condition)
   - [Dihedral and exceptional prime-to-ell images](#94-dihedral-and-exceptional-prime-to-ell-images)
   - [Examples and failure tests](#95-examples-and-failure-tests)
10. [The adequate-image theorem in dimension two](#10-the-adequate-image-theorem-in-dimension-two)
    - [The large-image calculation](#101-the-large-image-calculation)
    - [The theorem for coefficient primes at least seven](#102-the-theorem-for-coefficient-primes-at-least-seven)
    - [Regular semisimple detection](#103-regular-semisimple-detection)
    - [Cyclotomic adequacy](#104-cyclotomic-adequacy)
    - [Normal subgroups and overgroups](#105-normal-subgroups-and-overgroups)
    - [Worked adequacy decisions](#106-worked-adequacy-decisions)
11. [The coefficient-five boundary](#11-the-coefficient-five-boundary)
    - [Why five is structurally different](#111-why-five-is-structurally-different)
    - [The icosahedral cohomology calculation](#112-the-icosahedral-cohomology-calculation)
    - [Safe statements at five](#113-safe-statements-at-five)
    - [The smaller primes](#114-the-smaller-primes)
12. [Big image and arithmetic use](#12-big-image-and-arithmetic-use)
    - [Projectively large versus full special-linear image](#121-projectively-large-versus-full-special-linear-image)
    - [A trace-field big-image criterion](#122-a-trace-field-big-image-criterion)
    - [Taylor--Wiles input](#123-taylor--wiles-input)
    - [Potential modularity and preservation of image](#124-potential-modularity-and-preservation-of-image)
    - [The detection mechanism in detail](#125-the-detection-mechanism-in-detail)
    - [Reconstructing the full image](#126-reconstructing-the-full-image)
13. [A final image protocol](#13-a-final-image-protocol)
    - [The decision tree](#131-the-decision-tree)
    - [The package established](#132-the-package-established)

## 1. The image problem in dimension two

### 1.1 From a representation to a projective action

A two-dimensional residual representation carries two kinds of information. Its matrices remember determinants and scalar characters, while its action on lines remembers the genuinely nonabelian geometry. Separating these layers is the first step toward an image theorem.

Fix a prime $\ell$, a finite field $k$ of characteristic $\ell$, a group $\Gamma$, and a homomorphism

$$
\bar\rho:\Gamma\longrightarrow\operatorname{GL}(V),
\qquad \dim_kV=2.
$$

When $\Gamma$ is profinite we always require continuity; the finite target then implies that $\bar\rho$ factors through a finite quotient. Write $G=\bar\rho(\Gamma)$ and let $Z=k^\times I$ be the scalar subgroup of $\operatorname{GL}(V)$. Projectivization gives

$$
\mathbb P\bar\rho:\Gamma\longrightarrow\operatorname{PGL}(V),
\qquad \overline G=G/(G\cap Z).
\tag{1.1}
$$

The fixed field of $\ker\bar\rho$ records the full matrix image. The larger kernel of $\mathbb P\bar\rho$ records only the projective image. Confusing these two fields loses the scalar layer, and therefore loses determinant information.

After choosing a basis, $\mathbb P(V)$ is the projective line and a matrix
$\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)$ acts by

$$
x\longmapsto\frac{ax+b}{cx+d}.
$$

Thus subgroup classification becomes a problem about finite groups of fractional linear transformations. This geometric form is the source of Dickson's theorem.

### 1.2 Three notions of irreducibility

The words irreducible, absolutely irreducible, and projectively irreducible answer different questions. The distinction matters as soon as coefficients are not algebraically closed.

The representation is **irreducible over $k$** if $V$ has no nonzero proper $G$-stable $k$-subspace. It is **absolutely irreducible** if $V\otimes_k\overline k$ is irreducible. Equivalently,

$$
\bar\rho\text{ is absolutely irreducible}
\quad\Longleftrightarrow\quad
\overline G\text{ fixes no point of }\mathbb P^1(\overline k).
\tag{1.2}
$$

Indeed, points of $\mathbb P^1(\overline k)$ are precisely lines in $V\otimes_k\overline k$. A nonsplit torus gives the standard warning: it can act irreducibly over $k$ while its elements become simultaneously diagonal over a quadratic extension, so the representation is not absolutely irreducible.

For an absolutely irreducible representation, Schur's lemma gives

$$
\operatorname{End}_{k[G]}(V)=k.
\tag{1.3}
$$

Conversely, for a two-dimensional representation over a finite field, (1.3) implies absolute irreducibility provided the representation is semisimple. Without semisimplicity a nonsplit extension of a character by itself has scalar endomorphism ring but is reducible. We will therefore use the invariant-line definition and invoke Schur's lemma only in the safe direction.

### 1.3 Determinants, scalars, and twists

Projectivization forgets exactly scalar multiplication. If $\psi:\Gamma\to k^\times$ is a character, then $\bar\rho$ and $\bar\rho\otimes\psi$ have the same projective representation, while

$$
\det(\bar\rho\otimes\psi)=\det(\bar\rho)\psi^2.
\tag{1.4}
$$

Consequently a projective classification never determines the full representation without a determinant and a central-extension calculation.

There is nevertheless a scalar-invariant class function that remembers the field of definition of the projective group. For $g\in G$ define

$$
\tau(g)=\frac{\operatorname{tr}(g)^2}{\det(g)}.
\tag{1.5}
$$

Multiplying $g$ by a scalar changes numerator and denominator by the same square, so $\tau$ is a function on $\overline G$. It is also invariant under conjugacy and coefficient-field automorphisms. The subfield

$$
k_{\mathrm{ptr}}=\mathbf F_\ell\bigl(\tau(g):g\in G\bigr)\subseteq k
\tag{1.6}
$$

will be called the **projective trace field**.

### 1.4 The arithmetic setting

The main arithmetic example is a continuous representation

$$
\bar\rho:G_F\longrightarrow\operatorname{GL}_2(k)
\tag{1.7}
$$

for a number field $F$. For elliptic-curve torsion, the Weil pairing proves

$$
\det\bar\rho=\bar\chi_\ell,
\tag{1.8}
$$

where $\bar\chi_\ell$ is the mod-$\ell$ cyclotomic character. More general weight-two problems allow a finite-order factor, but the determinant is still prescribed.

At a finite place $v\nmid\ell$, good reduction gives trivial inertia and multiplicative reduction gives a unipotent inertia matrix whose off-diagonal entry is controlled by the minimal-discriminant exponent. At $v\mid\ell$, finite flatness is a geometric extension property, not the same as unramifiedness. These earlier local facts constrain possible image fields; they do not replace the group classification.

### 1.5 Four model images

Concrete matrices keep the later alternatives from becoming mere labels.

First choose a nonsquare $d\in k^\times$ and embed $k(\sqrt d)^\times$ in $\operatorname{GL}_2(k)$ by multiplication on the $k$-basis $1,\sqrt d$. Modulo $k^\times$, this gives a cyclic nonsplit torus. Its natural action is irreducible over $k$, because an invariant line would be an eigenline defined over $k$, but it splits over $k(\sqrt d)$. This is the standard example separating irreducibility from absolute irreducibility.

Second let $r=\operatorname{diag}(a,a^{-1})$ and

$$
s=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

Then $srs^{-1}=r^{-1}$. If $a^2\ne1$, the group generated by $r$ and $s$ is absolutely irreducible: the two eigenlines of $r$ are exchanged by $s$. Its projective image is dihedral. The diagonal subgroup is the restriction to the inducing quadratic field, while $s$ represents its nontrivial automorphism.

Third, the matrices

$$
u(a)=\begin{pmatrix}1&a\\0&1\end{pmatrix},
\qquad
d(t)=\begin{pmatrix}t&0\\0&t^{-1}\end{pmatrix}
$$

generate an affine Borel group if no lower unipotent is present. It fixes the line spanned by the first basis vector. Adding the Weyl element $w$ produces the opposite unipotents and generates a special-linear group. This single change—from one root direction to two—is the geometric transition from reducible to large image.

Finally, scalar twists leave all these projective pictures unchanged. If $\psi$ is any character, the images of $\rho$ and $\rho\otimes\psi$ on $\mathbb P^1$ coincide even though their full cutout fields and determinants can differ. Every arithmetic use of Dickson's theorem must therefore restore the scalar information after the projective case has been identified.

## 2. Geometry of finite projective linear groups

### 2.1 Fixed points of fractional linear transformations

The classification begins with a rigid fact peculiar to the projective line: a nonidentity transformation has at most two fixed points.

**Lemma 2.1.** Let $K$ be algebraically closed and $1\ne g\in\operatorname{PGL}_2(K)$. Then $g$ fixes one or two points of $\mathbb P^1(K)$. It fixes one point exactly when $g$ is represented by a nontrivial unipotent matrix; this can occur only when the order of $g$ equals $\operatorname{char}K$.

**Proof.** A fixed line of a representing matrix is an eigenline. A $2\times2$ matrix has one eigenline precisely when its characteristic polynomial has a repeated root and it is not scalar. After scaling and conjugating it is then

$$
u=\begin{pmatrix}1&a\\0&1\end{pmatrix},\qquad a\ne0.
$$

If the characteristic is $p>0$, then $u^p=1$ and no smaller positive power is $1$. In characteristic zero it has infinite order. In the remaining case there are two distinct eigenlines. $\square$

It follows that any finite-order element whose order is prime to $p=\operatorname{char}K$ is semisimple and fixes two points. The unordered pair of fixed points determines its torus; preserving or interchanging that pair determines the torus normalizer.

### 2.2 Unipotent subgroups

Characteristic $p$ enters Dickson's theorem through $p$-subgroups.

**Lemma 2.2.** Every nontrivial finite $p$-subgroup $U\subset\operatorname{PGL}_2(K)$ fixes a unique point. After conjugation that point is $\infty$ and

$$
U=\{x\mapsto x+a:a\in A\}
\tag{2.1}
$$

for a finite-dimensional $\mathbf F_p$-subspace $A\subset K$. In particular $U$ is elementary abelian.

**Proof strategy.** A central element of order $p$ has a unique fixed point. Centrality forces the whole group to preserve that point, after which upper triangular matrices show that every $p$-element is a translation.

**Proof.** The center of the finite $p$-group $U$ contains an element $z$ of order $p$. By Lemma 2.1, $z$ has a unique fixed point $P$. For $u\in U$, the point $uP$ is fixed by $uzu^{-1}=z$, so $uP=P$. Put $P=\infty$. An element fixing $\infty$ has form $x\mapsto ax+b$. If it has $p$-power order, then $a$ has $p$-power order in $K^\times$, hence $a=1$. Thus every element is a translation. Closure under composition and inverses makes the set of translation parameters an additive subgroup; finiteness makes it a finite $\mathbf F_p$-vector space. $\square$

The normalizer of $U_A$ inside the stabilizer of $\infty$ consists of maps $x\mapsto bx+c$ with $bA=A$. Its quotient by $U_A$ embeds in the cyclic group of scalar multipliers preserving $A$.

### 2.3 Split and nonsplit tori

Let $k=\mathbf F_q$. A split torus in $\operatorname{PGL}_2(k)$ fixes two $k$-rational points and is conjugate to

$$
T_s=\{x\mapsto ax:a\in k^\times\},
$$

which has order $q-1$. A nonsplit torus becomes diagonal over $k_2=\mathbf F_{q^2}$ and corresponds to

$$
k_2^\times/k^\times,
$$

which is cyclic of order $q+1$. Its two fixed points are conjugate over $k_2$ and are not $k$-rational.

**Lemma 2.3.** Every cyclic subgroup of $\operatorname{PGL}_2(k)$ of order prime to $p$ lies in a split or nonsplit torus. Its order therefore divides $q-1$ or $q+1$.

**Proof.** A generator is semisimple. Its two eigenlines are either individually fixed by Frobenius, giving the split case, or exchanged by Frobenius, giving the nonsplit case. Diagonalization over $k_2$ identifies the corresponding torus and its order. $\square$

### 2.4 Normalizers and the origin of dihedral groups

The normalizer of either torus has index two. In coordinates for the split torus, the nontrivial coset is represented by $w:x\mapsto1/x$, and

$$
waw^{-1}=a^{-1}.
$$

Hence a subgroup of a torus normalizer but not of the torus has cyclic rotation subgroup and inversion action. If the rotation subgroup has order $n>2$, its projective image is the dihedral group

$$
D_{2n}=\langle r,s:r^n=s^2=1,\ srs=r^{-1}\rangle.
\tag{2.2}
$$

For $n=2$, this is the Klein four group; notation in the literature varies, so we always record the order. The geometry is more important than the name: an index-two subgroup preserves two lines and an element outside it exchanges them.

## 3. Dickson's classification

### 3.1 The complete statement

We now classify all finite subgroups, including the reducible affine branch needed to make the theorem logically complete.

**Theorem 3.1 (Dickson classification).** Let $k$ be a finite field of characteristic $p$ and let $H\subset\operatorname{PGL}_2(k)$. After conjugation over $\overline k$, one of the following structural alternatives holds:

1. **Borel type:** $H$ fixes a point. It has a normal elementary abelian $p$-subgroup $A$ and cyclic quotient of order prime to $p$ acting on $A$ by scalar multiplication.
2. **Cyclic type:** $H$ is cyclic of order prime to $p$.
3. **Dihedral type:** $H$ is dihedral of order $2n$, with $p\nmid n$, and lies in the normalizer of a torus.
4. **Exceptional type:** $H$ is isomorphic to $A_4$, $S_4$, or $A_5$.
5. **Subfield or large type:** for a finite subfield $k_0\subset\overline k$ of characteristic $p$, one has

   $$
   \operatorname{PSL}_2(k_0)\subseteq H\subseteq\operatorname{PGL}_2(k_0)
   \tag{3.1}
   $$

   after conjugation. More precisely the upper group is a subgroup of the automorphism group induced by projective linear matrices over the relevant field of definition; inside a fixed $\operatorname{PGL}_2(k)$ no field automorphism is added.

The alternatives have small overlaps: $\operatorname{PSL}_2(2)\simeq S_3$, $\operatorname{PSL}_2(3)\simeq A_4$, $\operatorname{PGL}_2(3)\simeq S_4$, and $\operatorname{PSL}_2(4)\simeq\operatorname{PSL}_2(5)\simeq A_5$. Classification means that every subgroup belongs to one of the displayed structural families, not that the labels are disjoint in these small cases.

### 3.2 The solvable branch

The proof is organized by Sylow $p$-subgroups. This exposes both the affine branch and the geometry of tori.

Let $P$ be a Sylow $p$-subgroup of $H$. If $P=1$, every nonidentity element fixes two points. Choose a maximal cyclic subgroup $C$. All elements centralizing a generator of $C$ preserve its two fixed points and hence lie in its torus. The normalizer of $C$ can only preserve or exchange those points, so $N_H(C)/C$ has order at most two after $C$ is enlarged to the full toral part of $H$.

If every conjugate of $C$ has the same fixed pair, then $H$ preserves that pair and is cyclic or dihedral. If distinct fixed pairs occur, count incidences

$$
(h,P),\qquad 1\ne h\in H,\qquad P\in\operatorname{Fix}(h).
$$

Each $h$ contributes two incidences. Stabilizers of points and pairs are cyclic and dihedral, respectively. The orbit--stabilizer identities force the possible rotation stabilizer orders to be $(2,3,3)$, $(2,3,4)$, or $(2,3,5)$; these are the spherical triples. Presentations

$$
\langle x,y:x^2=y^3=(xy)^m=1\rangle,
\qquad m=3,4,5,
\tag{3.2}
$$

then give $A_4,S_4,A_5$. Here is the numerical step. A fundamental orbit triangle has stabilizers $a,b,c$, and counting translates gives

$$
\frac2{|H|}=\frac1a+\frac1b+\frac1c-1>0.
\tag{3.3}
$$

With $2\le a\le b\le c$, positivity yields $a=2$, then $b=2$ (the dihedral family) or $b=3$ and $c=3,4,5$. This proves the prime-to-$p$ branch without assuming the answer.

Now suppose $P\ne1$. By Lemma 2.2, $P$ fixes a unique point $x_P$. If every Sylow $p$-subgroup fixes the same point, that point is $H$-stable and $H$ is of Borel type. The translation subgroup is normal, and the multiplier quotient is cyclic.

It remains to study the case of at least two Sylow $p$-subgroups with distinct fixed points. The subgroup generated by opposite unipotent groups is the mechanism that produces a group over a finite subfield.

### 3.3 The nonsolvable branch

Conjugate one Sylow group to translations $u(a):x\mapsto x+a$ with $a\in A$, and choose an opposite Sylow group fixing $0$, written

$$
v(b)=\begin{pmatrix}1&0\\b&1\end{pmatrix}.
$$

Let $k_0$ be the finite subfield generated by all products $ab$ that occur. The elementary matrix identity

$$
\begin{pmatrix}1&a\\0&1\end{pmatrix}
\begin{pmatrix}1&0\\b&1\end{pmatrix}
=
\begin{pmatrix}1+ab&a\\b&1\end{pmatrix}
\tag{3.4}
$$

and its conjugates show that the generated group contains diagonal elements
$\operatorname{diag}(t,t^{-1})$ for $t$ in the multiplicative group generated by the nonzero parameters. Conjugating $u(a)$ by these diagonal elements multiplies $a$ by $t^2$. Closure under addition, multiplication, and inversion follows from the elementary identities

$$
u(a)u(b)=u(a+b),
\qquad
\begin{pmatrix}t&0\\0&t^{-1}\end{pmatrix}
u(a)
\begin{pmatrix}t^{-1}&0\\0&t\end{pmatrix}
=u(t^2a),
\tag{3.5}
$$

together with the analogous lower-unipotent formulas. Thus the parameter set is a finite field $k_0$ after a common rescaling. The upper and lower elementary matrices over $k_0$ generate $\operatorname{SL}_2(k_0)$: Gaussian elimination writes every determinant-one matrix with nonzero lower-left entry as a product of such matrices, and diagonal matrices follow from

$$
\begin{pmatrix}t&0\\0&t^{-1}\end{pmatrix}
=u(t)v(-t^{-1})u(t)u(-1)v(1)u(-1),
\tag{3.6}
$$

with harmless adjustments at the smallest fields. Projectivizing gives $\operatorname{PSL}_2(k_0)$.

The normalizer of this projective special linear group in the projective linear group over the ambient finite field acts on its two root subgroups and preserves the field generated by their cross-ratios. It is therefore contained in $\operatorname{PGL}_2(k_0)$ after conjugation. This proves (3.1).

For completeness, we spell out the orbit calculation hidden in the phrase “opposite Sylow groups.” Let $\Omega$ be the set of fixed points of nontrivial Sylow $p$-subgroups. Distinct Sylow groups have distinct fixed points: a common fixed point would place both in the translation group at that point, whose finite $p$-subgroups lie in one elementary abelian group and hence in a larger common $p$-subgroup. Thus Sylow groups and points of $\Omega$ correspond bijectively.

Fix $\infty\in\Omega$ and write

$$
H_\infty=P\rtimes C,
\tag{3.7}
$$

where $P$ is a translation group and $C$ is cyclic of order prime to $p$. The subgroup $C$ acts freely on $P\setminus\{1\}$ unless a multiplier fixes a nonzero translation parameter. Hence every nontrivial stabilizer in this action is read from a proper scalar subfield. Choose $0\in\Omega\setminus\{\infty\}$ and let $H_{0,\infty}$ be the pointwise stabilizer of the ordered pair. It is cyclic and embeds in both corresponding multiplier groups.

There are now two possibilities. If $P$ acts regularly on $\Omega\setminus\{\infty\}$, rescale so that $0$ and $1$ belong to that orbit. The translation parameters form an additive set $A$, while the two-point stabilizer gives multipliers. Conjugating by an element exchanging $0$ and $\infty$ turns these into lower translations. Cross-ratios

$$
[\infty,0;a,b]=a/b
\tag{3.8}
$$

of four points in the orbit show that the ratios of nonzero parameters remain in the same parameter set. Thus $A$ is closed under addition, multiplication, and inversion after normalization; it is a finite field $k_0$. Equations (3.4)--(3.6) then give $\operatorname{PSL}_2(k_0)$.

If $P$ is not regular on the complement, a nontrivial element fixes an additional orbit point. But a nontrivial projective $p$-element has only its unique fixed point, so the extra stabilizer has order prime to $p$. Counting the $H_\infty$-orbits and then the $H$-orbits of ordered triples reduces to

$$
\frac1a+\frac1b+\frac1c>1
\tag{3.9}
$$

for the three nontrivial stabilizer orders. As in (3.3), the solutions are the dihedral family and $(2,3,3)$, $(2,3,4)$, $(2,3,5)$. The dihedral solution has no nontrivial $p$-subgroup except possibly at $p=2$ and is already in the torus-normalizer branch. The three remaining presentations have orders $12$, $24$, and $60$: using the coset action on the vertices, edges, and faces of the associated orbit complex identifies them with $A_4,S_4,A_5$. In characteristics dividing these orders the same groups can also appear as the small subfield coincidences recorded below.

This proves that failure of the field-parameter construction produces no further family. Combined with the prime-to-$p$ calculation, it completes the classification. $\square$

### 3.4 Small coincidences and exceptional characteristics

The theorem is uniform, but its interpretation is not. In characteristic $3$, $A_4$ and $S_4$ have order divisible by the characteristic. In characteristic $5$, $A_5$ does. These are exactly the situations in which averaging in group cohomology fails for an exceptional group. At primes $\ell\ge7$, all three exceptional group orders

$$
|A_4|=12,\qquad |S_4|=24,\qquad |A_5|=60
$$

are prime to $\ell$. This elementary observation is the reason the clean adequacy theorem starts at seven rather than five.

### 3.5 Orders, orbits, and recognition

Later arguments often recognize a branch by divisibility before identifying every matrix. The relevant orders are

$$
|\operatorname{GL}_2(\mathbf F_q)|=(q^2-1)(q^2-q),
$$

$$
|\operatorname{PGL}_2(\mathbf F_q)|=q(q^2-1),
\qquad
|\operatorname{PSL}_2(\mathbf F_q)|=
\frac{q(q^2-1)}{\gcd(2,q-1)}.
\tag{3.10}
$$

The first formula comes from choosing a nonzero first column and then a second column outside its span. Dividing by $q-1$ gives the projective order. The determinant map on $\operatorname{PGL}_2$ is well defined modulo squares, so its kernel has index $\gcd(2,q-1)$ and is $\operatorname{PSL}_2$.

The natural projective action has $q+1$ points. Its stabilizer is a Borel of order $q(q-1)$, and its two-point stabilizer is a split torus of order $q-1$. These identities verify orbit--stabilizer:

$$
q(q^2-1)=(q+1)q(q-1).
$$

A nonsplit torus of order $q+1$ acts freely and transitively on a suitable conjugate set of $q+1$ geometric directions. Its normalizer has order $2(q+1)$ when $q>2$. These order checks distinguish split and nonsplit dihedral normalizers.

The exceptional groups can be recognized by element orders and normal subgroups. The group $A_4$ has a normal Klein four subgroup and eight elements of order three. The group $S_4$ has the sign quotient, a normal Klein four subgroup, transpositions, double transpositions, three-cycles, and four-cycles. The simple group $A_5$ has elements only of orders $1,2,3,5$, with conjugacy class sizes $1,15,20,12,12$; the two classes of five-cycles merge under $S_5$ but not inside $A_5$.

Element orders alone do not always identify the group. A dihedral group can also contain many involutions, and $A_4$ coincides with a small projective special-linear group. A safe recognition argument combines order, normal-subgroup structure, and the fixed-point geometry on $\mathbb P^1$.

### 3.6 Two finite-field portraits

Over $\mathbf F_7$, split and nonsplit tori have orders $6$ and $8$. Their normalizers have orders $12$ and $16$. The full projective groups have

$$
|\operatorname{PSL}_2(\mathbf F_7)|=168,
\qquad
|\operatorname{PGL}_2(\mathbf F_7)|=336.
$$

Thus a projective subgroup containing an element of order seven is not automatically large: it might lie in an affine Borel, where the translation subgroup has order seven. If the representation is absolutely irreducible, the Borel case disappears. An exceptional $S_4$ subgroup can occur, while $A_5$ cannot because $60$ does not divide $336$. Any remaining subgroup with two opposing seven-Sylow groups enters the special-linear branch. Every absolutely irreducible case is adequate because the coefficient prime is seven.

Over $\mathbf F_9$, the numerical picture is different:

$$
|\operatorname{PSL}_2(\mathbf F_9)|=360,
\qquad
|\operatorname{PGL}_2(\mathbf F_9)|=720.
$$

Here $\operatorname{PSL}_2(\mathbf F_9)\simeq A_6$, and $A_5$ subgroups occur naturally. Split and nonsplit torus orders are $8$ and $10$. Because the coefficient characteristic is three, the orders of $A_4$, $S_4$, $A_5$, and the large group can all interact with modular cohomology. Dickson's classification remains valid, but the uniform adequacy conclusion does not.

These portraits make two points. Divisibility by $\ell$ distinguishes the affine or large mechanisms from prime-to-$\ell$ tori only after fixed points are considered. And a group name such as $A_5$ does not by itself determine whether it is an isolated exceptional subgroup or part of a defining-characteristic subfield group.

## 4. Irreducible matrix representations

### 4.1 Eliminating point stabilizers and cyclic groups

Let $G\subset\operatorname{GL}_2(k)$ act absolutely irreducibly and let $\overline G$ be its projective image. The Borel branch of Theorem 3.1 is impossible by (1.2). The cyclic branch is also impossible: a cyclic projective group of order prime to $\ell$ is generated by a semisimple element, and all its lifts commute up to scalars. Over $\overline k$ they preserve its two eigenlines. Thus only dihedral, exceptional, and large projective images remain.

This reduction is useful but not reversible. A group with dihedral projective image can still become reducible if its rotation subgroup is scalar. Absolute irreducibility forces the projective rotation order to exceed two in the genuinely induced case, apart from small Klein-four realizations that must be checked directly.

### 4.2 The dihedral induction theorem

**Theorem 4.1.** Let $\Gamma$ be a group and let $\rho:\Gamma\to\operatorname{GL}_2(\overline k)$ be absolutely irreducible. Its projective image lies in a torus normalizer but not in the torus if and only if there is an index-two subgroup $\Gamma_M\subset\Gamma$ and a character $\theta:\Gamma_M\to\overline k^\times$ such that

$$
\rho\simeq\operatorname{Ind}_{\Gamma_M}^{\Gamma}\theta.
\tag{4.1}
$$

Moreover $\rho|_{\Gamma_M}\simeq\theta\oplus\theta^s$, where $s\notin\Gamma_M$, and the projective rotation character is $\theta/\theta^s$.

**Proof.** In the torus-normalizer case, the inverse image of the torus has index two and preserves the two torus eigenlines. Absolute irreducibility makes an element outside exchange those lines. If $L$ is one eigenline and $\theta$ its character, the two cosets give a basis $L\oplus sL$ and the action is exactly the induced action.

Conversely, in an induced basis, elements of $\Gamma_M$ are diagonal and an element outside is antidiagonal. Projectively these matrices lie in a torus normalizer and not in the torus. If $\theta=\theta^s$, the induced representation is reducible; absolute irreducibility is equivalent to their inequality. $\square$

The quotient $\Gamma/\Gamma_M$ is the **dihedral quadratic character**. It is intrinsic when the projective rotation subgroup is characteristic, in particular when its order is greater than two.

### 4.3 Exceptional and large images

Exceptional images are finite and rigid but are not automatically harmless. Their central lifts in $\operatorname{GL}_2(k)$ may differ, and at characteristics dividing $12$, $24$, or $60$ their cohomology can be nonsemisimple.

In the large branch, Theorem 3.1 supplies a subfield $k_0$ and

$$
\operatorname{PSL}_2(k_0)\subseteq\overline G.
\tag{4.2}
$$

This is a projective assertion. The full image need not equal $\operatorname{GL}_2(k)$, and its determinant may occupy only a prescribed subgroup of $k^\times$. Nevertheless the commutator subgroup recovers a special-linear core; Chapter 12 makes this precise.

### 4.4 The projective trace field

The invariant $\tau$ distinguishes a genuine full-field image from a subfield image.

**Proposition 4.2.** If $q_0>3$, the values of $\tau$ on $\operatorname{PSL}_2(\mathbf F_{q_0})$ generate $\mathbf F_{q_0}$. Hence the smallest field over which a projective subgroup containing $\operatorname{PSL}_2(\mathbf F_{q_0})$ can be defined is its projective trace field.

**Proof.** For

$$
g_t=\begin{pmatrix}t&-1\\1&0\end{pmatrix}\in\operatorname{SL}_2(\mathbf F_{q_0}),
$$

one has $\tau(g_t)=t^2$. The squares generate the field additively and multiplicatively: in odd characteristic,
$t=((t+1)^2-(t-1)^2)/4$; in characteristic two every element is a square because Frobenius is an automorphism. Thus all $t\in\mathbf F_{q_0}$ lie in the field generated by the $\tau$-values. The reverse inclusion is clear. $\square$

### 4.5 Central lifts and determinants

A projective group $\overline G$ does not come with a unique subgroup of $\operatorname{GL}_2(k)$. The inverse image fits into a central extension

$$
1\longrightarrow C\longrightarrow G\longrightarrow\overline G\longrightarrow1,
\qquad C\subseteq k^\times.
\tag{4.3}
$$

Choosing arbitrary lifts of projective elements produces a factor set

$$
\widetilde g\widetilde h=c(g,h)\widetilde{gh},
\qquad c(g,h)\in k^\times.
\tag{4.4}
$$

Associativity says that $c$ is a two-cocycle. Changing lifts multiplies it by a coboundary. Thus the obstruction to lifting a projective representation with a prescribed scalar group is a class in $H^2(\overline G,k^\times)$ for the trivial action. This is the precise reason an abstract isomorphism $\overline G\simeq A_5$ does not yet identify the full matrix image.

The determinant supplies an additional restriction. If $g\in\overline G$ has order $n$ and $\widetilde g$ is a lift, then $\widetilde g^n$ is scalar. Its determinant is the square of that scalar, while also equal to $\det(\widetilde g)^n$. In arithmetic applications the prescribed determinant fixes the latter value. This frequently decides which central extension and which conjugacy class of lifts is possible.

For a dihedral projective image, take diagonal and antidiagonal lifts:

$$
r=\begin{pmatrix}\alpha&0\\0&\beta\end{pmatrix},
\qquad
s=\begin{pmatrix}0&x\\y&0\end{pmatrix}.
$$

Then $s^2=xyI$, $srs^{-1}$ interchanges $\alpha$ and $\beta$, and

$$
\det(s)=-xy.
\tag{4.5}
$$

The projective reflection has order two regardless of $xy$, but the full lift can have several orders and determinant signs. Oddness is a statement about (4.5), not merely about the abstract dihedral involution.

## 5. Restriction and scalar extension

### 5.1 Coefficient extension changes coordinates, not kernels

Let $k'/k$ be finite. Extending coefficients gives

$$
\bar\rho_{k'}:\Gamma\to\operatorname{GL}_2(k').
$$

The matrices are the same matrices viewed in a larger field, so

$$
\ker\bar\rho_{k'}=\ker\bar\rho,\qquad
\ker\mathbb P\bar\rho_{k'}=\ker\mathbb P\bar\rho.
\tag{5.1}
$$

Thus full and projective cutout fields do not change. Irreducibility can change: a nonsplit torus becomes diagonal after coefficient extension. Absolute irreducibility, by definition, does not change.

Adequacy will also be stable under finite coefficient extension. Cohomology commutes with extension of finite scalar fields, and the span of semisimple matrices extends by tensor product. This stability never permits one to replace an irreducible representation by an absolutely irreducible one; it merely lets one test absolute properties over a splitting field.

### 5.2 Normal restriction and Clifford theory

Restriction to a normal subgroup is the main source of dihedral alternatives.

**Proposition 5.1 (rank-two Clifford dichotomy).** Let $N\triangleleft\Gamma$ and suppose $\Gamma/N$ is cyclic of order prime to $\ell$. If $\rho$ is absolutely irreducible of dimension two, then either $\rho|_N$ is absolutely irreducible, or there is an index-two subgroup $\Gamma_M$ containing $N$ such that $\rho$ is induced from a character of $\Gamma_M$.

**Proof strategy.** Follow the actual $N$-stable lines rather than assuming modular semisimplicity. Normality makes $\Gamma$ permute those lines, and dimension two leaves a two-point orbit unless $N$ acts projectively by scalars.

**Proof.** Suppose $\rho|_N$ is reducible and choose an $N$-stable line $L$. For $g\in\Gamma$, normality shows that $gL$ is again $N$-stable. If $L$ were the unique stable line, it would be $\Gamma$-stable, contrary to irreducibility. If $N$ has two stable lines and does not act projectively by scalars, these are exactly its two common eigendirections; $\Gamma$ permutes them transitively. Their stabilizer $\Gamma_M$ has index two and contains $N$, so Theorem 4.1 gives induction.

It remains to exclude the possibility that $N$ acts projectively by scalars. Then $\mathbb P\rho$ factors through the cyclic group $\Gamma/N$. Its order is prime to $\ell$, so over $\overline k$ its matrices are simultaneously diagonalizable. That contradicts absolute irreducibility. Thus only the two-line case occurs. $\square$

The cyclic quotient hypothesis is exactly what is available for cyclotomic restriction: the image of $\bar\chi_\ell$ lies in $k^\times$, whose order is prime to $\ell$.

### 5.3 Cyclotomic restriction

Put

$$
F_\ell=F(\zeta_\ell),\qquad
G_{F_\ell}=\ker(\bar\chi_\ell|_{G_F}).
$$

Then $G_{F_\ell}\triangleleft G_F$ and the quotient is cyclic of order dividing $\ell-1$. Proposition 5.1 gives the exact alternative:

**Corollary 5.2.** If $\bar\rho:G_F\to\operatorname{GL}_2(k)$ is absolutely irreducible, then either $\bar\rho|_{G_{F_\ell}}$ is absolutely irreducible, or $\bar\rho$ is induced from a character of a quadratic extension $M/F$ contained in $F_\ell/F$.

**Proof.** Apply Proposition 5.1 with $N=G_{F_\ell}$. The quotient is the image of $\bar\chi_\ell$ and hence is cyclic of order dividing $\ell-1$. In the reducible branch, the index-two subgroup supplied by that proposition contains $G_{F_\ell}$, so its fixed quadratic field lies inside $F_\ell$. $\square$

This result is often paraphrased as “failure of cyclotomic irreducibility is dihedral.” The containment $M\subset F_\ell$ is essential. It turns the representation-theoretic failure into a concrete quadratic character that can be tested by class field theory and local conductor data.

### 5.4 Disjoint base change

Let $L/F$ be finite and let $K/F$ be the field cut out by $\bar\rho$. Restriction has image

$$
\bar\rho(G_L)\simeq\operatorname{Gal}(K/K\cap L).
\tag{5.2}
$$

Therefore, if $K$ and $L$ are linearly disjoint over $F$, the full image is unchanged. The same assertion with the projective cutout field preserves the projective image. This is the clean mechanism used in potential modularity: an auxiliary field chosen disjoint from the residual field preserves absolute irreducibility, projective type, and adequacy. Without disjointness, restriction may become dihedral or reducible.

## 6. Local arithmetic constraints

### 6.1 Fields cut out by full and projective representations

For a finite-image representation of $G_F$, define

$$
K=\overline F^{\ker\bar\rho},\qquad
K^{\mathrm{proj}}=\overline F^{\ker\mathbb P\bar\rho}.
\tag{6.1}
$$

Then $K/K^{\mathrm{proj}}$ is abelian with Galois group $G\cap Z$, while
$\operatorname{Gal}(K^{\mathrm{proj}}/F)=\overline G$. The determinant field is a quotient of the full field but need not equal the scalar field. A nonscalar matrix can have any permitted determinant, and a scalar $aI$ has determinant $a^2$.

At a place $v$, the inertia image in the projective field is simply the projectivization of the matrix inertia image. Thus unramifiedness of $\bar\rho$ implies projective unramifiedness, but the converse permits scalar ramification.

### 6.2 Conductor restrictions away from the coefficient prime

Let $v\nmid\ell$. For a two-dimensional characteristic-$\ell$ module, we use conductor statements only when justified by the known local action, rather than importing characteristic-zero semisimplicity into a modular representation.

If inertia acts trivially, both cutout fields are unramified at $v$. At a multiplicative elliptic-curve place, the residual inertia has form

$$
\begin{pmatrix}1&\overline m_v\,\overline t_\ell\\0&1\end{pmatrix},
\tag{6.2}
$$

where $m_v=v(\Delta_{\min})$. It is trivial exactly when $\ell\mid m_v$. If nontrivial, its image has order $\ell$ and fixes a unique projective point. Therefore an exceptional projective group of order prime to $\ell$ cannot contain such nontrivial inertia. For $\ell\ge7$, this observation forces residual unramifiedness at every multiplicative place in an exceptional branch unless $\ell\mid m_v$ already does so.

More generally, a prescribed Artin conductor or upper-break cutoff restricts the inertia subgroup of $\overline G$ and the ramification of $K^{\mathrm{proj}}$. The earlier ramification theory converts a cutoff $G_{F_v}^u$ acting trivially for $u>R_v$ into

$$
\frac{d(K_w/F_v)}{e(K_w/F_v)}<1+R_v.
\tag{6.3}
$$

This is a field-theoretic consequence and remains valid in modular coefficient characteristic because it is applied to the faithful finite action, not to a falsely semisimplified modular conductor.

### 6.3 Finite flatness at the coefficient prime

At $v\mid\ell$, saying that $\bar\rho|_{G_{F_v}}$ is finite flat means that its finite étale generic module extends to a finite locally free commutative group scheme over $\mathcal O_{F_v}$. It does **not** mean inertia is trivial: $\mu_\ell$ is the basic counterexample.

The finite-flat condition is preserved under supplied subobjects, quotients, duality, unramified base change, and coefficient extension in the forms established by the integral theory. It constrains a dihedral induction because both character lines over the inducing field, when they extend as admissible subquotients of a model, must belong to the corresponding finite-flat character category. One must not infer those line models merely from a generic invariant line without taking schematic closure in an ambient model.

If an additional integral theorem supplies an upper-break bound $R_v$, then (6.3) applies. For a level-$\ell$ module over an unramified extension of $\mathbf Q_\ell$, the standard cutoff $R_v\le1/(\ell-1)$, when available as a proved input, gives

$$
\frac de<\frac\ell{\ell-1}.
\tag{6.4}
$$

Finite flatness alone is not being used to prove that cutoff here. This separation prevents a geometric predicate from being mistaken for a numerical ramification theorem.

### 6.4 Quadratic characters in the dihedral branch

Suppose the projective image is dihedral and let

$$
\delta:G_F\longrightarrow\{\pm1\}
\tag{6.5}
$$

be the character cutting out the inducing quadratic extension $M/F$. Since $\delta$ is a quotient of the projective representation, every place unramified in $\bar\rho$ is unramified in $M$. If the local projective inertia lies in the rotation subgroup, then $\delta$ is unramified there; if inertia meets the reflection coset, $M/F$ is ramified there.

Global class field theory now makes the alternative finite. If $S$ contains all allowed ramified places and the real places permitted to complexify, then $\delta$ is a quadratic character of the ray class group for a modulus supported on $S$, with local exponent bounded by its conductor. Computing that finite ray group lists every possible $M$. Thus the dihedral branch is not an amorphous exception: it is a finite list of quadratic inducing fields followed by character arithmetic over each field.

### 6.5 Exceptional quotients and ray data

Exceptional groups also expose abelian information. Their abelianizations are

$$
A_4^{\mathrm{ab}}\simeq C_3,
\qquad
S_4^{\mathrm{ab}}\simeq C_2,
\qquad
A_5^{\mathrm{ab}}=1.
\tag{6.6}
$$

For $A_4$, the normal Klein four subgroup gives a cyclic cubic quotient. For $S_4$, the sign gives a quadratic quotient, and the normal Klein four subgroup gives an $S_3$ quotient. The group $A_5$ is simple, so it has no nontrivial abelian quotient; abelian class field theory cannot see it directly.

Suppose the projective representation is unramified outside $S$. In the $A_4$ case, the cyclic cubic quotient cuts out an abelian cubic extension unramified outside $S$. In the $S_4$ case, the sign cuts out a quadratic extension with the same support restriction. Their local conductor exponents cannot exceed those of the corresponding quotient of projective inertia. Class field theory therefore gives immediate necessary conditions: the relevant ray class group must have a quotient of order three or two.

These tests can eliminate $A_4$ or $S_4$, but their converses are false. A ray class group with a cubic quotient constructs a cyclic cubic field, not automatically an $A_4$ extension above it. Likewise $A_5$ requires nonabelian information such as a degree bound, a discriminant argument, or a Frobenius calculation. Keeping necessity separate from sufficiency prevents an abelian quotient calculation from pretending to classify a nonabelian extension.

The local inertia possibilities can be read group-theoretically. At a tame place, inertia is cyclic, so in $A_4$ its order is $1$, $2$, or $3$; in $S_4$ it can have order $1$, $2$, $3$, or $4$; in $A_5$ it has order $1$, $2$, $3$, or $5$. Wild inertia is a normal residue-characteristic subgroup of inertia, so its possible images lie in the corresponding Sylow subgroups. At coefficient primes at least seven, none of the exceptional groups contains an $\ell$-subgroup, which recovers the unipotent exclusion of Section 7.4.

### 6.6 Local projective inertia by cases

Local decomposition groups need not have the same Dickson type as the global image. Even inside a globally large group, inertia can be cyclic, dihedral, or affine. The classification becomes useful locally when combined with the normal structure of inertia.

Let $v$ have residue characteristic $p$. Write $I_v\supset P_v$ for inertia and wild inertia. Every finite quotient of $P_v$ is a $p$-group. If its projective image in $\operatorname{PGL}_2(k)$ is nontrivial and $p=\ell$, Lemma 2.2 conjugates it into translations. It fixes a unique projective line. Tame inertia normalizes wild inertia, hence preserves that line and acts on the translation parameters through a cyclic multiplier group. Thus the full projective inertia image is of Borel type:

$$
\overline\rho(I_v)=A\rtimes C,
\tag{6.7}
$$

with $A$ elementary abelian of characteristic $\ell$ and $C$ cyclic of order prime to $\ell$.

If $p\ne\ell$, a finite wild inertia image is a $p$-group in characteristic $\ell$. Its matrices are semisimple when $p$ is odd to their order, but the abstract $p$-group need not be cyclic before projectivization. Dickson's theorem restricts it sharply: it lies in a torus, in a dihedral $2$-group, in an exceptional Sylow group, or in a subfield group. When geometric reduction theory already gives a unipotent matrix of order $\ell$, as at a multiplicative place, that element comes from tame rather than wild inertia because $p\ne\ell$.

At a tamely ramified place, the projective inertia image is cyclic. It lies in a split torus if its two eigenlines are defined over $k$ and in a nonsplit torus otherwise. The decomposition group normalizes inertia, and Frobenius conjugates a tame generator $\tau$ by

$$
\operatorname{Frob}_v\tau\operatorname{Frob}_v^{-1}=\tau^{q_v}.
\tag{6.8}
$$

If Frobenius preserves the two inertia eigenlines, the local projective image lies in the torus. If it exchanges them, the local image lies in the torus normalizer and becomes dihedral. This local dihedrality does not imply that the global representation is induced from a quadratic field; the global image may contain many conjugates of the local torus.

Scalar inertia is the remaining case. It is invisible in $K^{\mathrm{proj}}$ but remains visible in $K$ and in the determinant. For example, a cyclotomic scalar character can be ramified while the projective representation is unramified. Therefore a projective discriminant bound and a full-field discriminant bound are different statements.

These cases give a reliable local protocol: determine wild inertia, determine the tame multiplier, determine Frobenius normalization, and only then place the decomposition group in the global projective image. A conductor number without these subgroup data generally does not identify the local image.

## 7. The hardly-ramified image ledger

### 7.1 An exact reusable datum

“Hardly ramified” should denote recorded local conditions, not an impression that few primes occur. For this chapter, a **hardly-ramified residual datum** consists of:

1. a number field $F$, a prime $\ell>2$, a finite field $k/\mathbf F_\ell$, and a continuous $\bar\rho:G_F\to\operatorname{GL}_2(k)$;
2. a prescribed determinant, usually $\bar\chi_\ell\eta$ with $\eta$ finite order;
3. absolute irreducibility and, when needed, total oddness;
4. a finite set $S$ outside which $\bar\rho$ is unramified;
5. at $v\mid\ell$, a finite-flat model or another precisely named integral condition;
6. at $v\in S$, exact inertia, conductor, or upper-break information;
7. the coefficient field and projective trace field.

Every clause serves a different purpose. The determinant controls scalars. Absolute irreducibility removes Borel and cyclic images. The ramification ledger constrains quotient fields. Finite flatness provides integral geometry at $\ell$. The trace field decides whether a large image is defined over the full coefficient field.

### 7.2 The small-image alternatives

**Theorem 7.1 (small-image ledger).** For an absolutely irreducible hardly-ramified residual datum, exactly one of the following structural cases occurs:

1. **Dihedral:** $\bar\rho\simeq\operatorname{Ind}_{G_M}^{G_F}\theta$ for a quadratic extension $M/F$. The character of $M/F$ is unramified outside the projective ramification set and has the locally prescribed conductor bounds.
2. **Exceptional:** $\mathbb P\bar\rho(G_F)$ is $A_4$, $S_4$, or $A_5$. The projective cutout field has degree $12$, $24$, or $60$, respectively, and each quotient of the exceptional group supplies an abelian subextension subject to the ray-class restrictions.
3. **Large:** the projective image contains $\operatorname{PSL}_2(k_0)$ for the projective trace field $k_0$.

If absolute irreducibility is omitted, Borel and cyclic alternatives must be restored.

**Proof.** The first reduction is Theorem 3.1 together with Section 4.1. The dihedral description and conductor assertion are Theorem 4.1 and Section 6.4. The degrees in the exceptional case are the group orders. Proposition 4.2 identifies the subfield in the large case. $\square$

The theorem “determines” small image in the useful sense: it converts it into quadratic character data or one of three explicit finite groups. Eliminating those alternatives requires arithmetic information about the particular $F$ and local datum; it cannot be done from the adjective hardly ramified alone.

### 7.3 Oddness and complex conjugation

Assume $F$ is totally real and $\bar\rho$ is totally odd. For each complex conjugation $c$, one has $c^2=1$ and

$$
\det\bar\rho(c)=-1.
$$

Since $\ell>2$, the eigenvalues are $1$ and $-1$ after scaling, so $\mathbb P\bar\rho(c)$ is a nontrivial involution. In particular complex conjugation is not projectively scalar.

In a dihedral branch, $c$ may lie in the rotation subgroup or the reflection coset. In the latter case the inducing quadratic field is imaginary at that real place; in the former it is real there. Oddness alone does not choose between these possibilities because a diagonal rotation can also have determinant $-1$ after restoring scalars. The determinant and local character calculation must be retained.

For exceptional groups, oddness specifies a conjugacy class of involutions only after the central lift is known. Projective $A_5$ has one involution class, whereas $S_4$ has transpositions and double transpositions; a full-matrix lift distinguishes their determinant behavior.

### 7.4 What local hypotheses do and do not eliminate

Three reliable deductions summarize the arithmetic interface.

First, unramifiedness passes to every quotient field. Hence quadratic inducing characters and abelian exceptional quotients are supported on the same finite set.

Second, a nontrivial unipotent inertia group of order $\ell$ cannot lie in $A_4,S_4,A_5$ when $\ell\ge7$. Thus a known nontrivial residual multiplicative inertia element rules out the exceptional branch at those primes.

Third, finite flatness at $\ell$ does not by itself rule out dihedral or exceptional image. Any such exclusion must use a proved classification of finite-flat characters, a ramification cutoff combined with a discriminant bound, or an explicit local calculation. This negative statement is mathematically useful: it identifies exactly which additional theorem a small-image argument still needs.

### 7.5 A worked rational ledger

Consider an absolutely irreducible odd representation

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k),
\qquad
\det\bar\rho=\bar\chi_\ell,
\tag{7.1}
$$

unramified outside a finite set $S$ containing $\ell$. Suppose also that the restriction at $\ell$ is finite flat. We will not pretend that these conditions alone settle the image; instead we show exactly what each small branch would require.

In the dihedral branch, write $\bar\rho=\operatorname{Ind}_{G_M}^{G_{\mathbf Q}}\theta$. The discriminant of $M$ is supported on $S$, with its sign determined by the infinite component. If $S=\{\ell\}$ and the quadratic character is unramified at $2$, the fundamental discriminant has no prime divisor other than $\ell$. Hence the only nontrivial possibility is

$$
M=\mathbf Q\left(\sqrt{\ell^*}\right),
\qquad
\ell^*=(-1)^{(\ell-1)/2}\ell.
\tag{7.2}
$$

This is also the unique quadratic subfield of $\mathbf Q(\zeta_\ell)$. To prove uniqueness, note that
$\operatorname{Gal}(\mathbf Q(\zeta_\ell)/\mathbf Q)\simeq(\mathbf Z/\ell\mathbf Z)^\times$ is cyclic and therefore has a unique index-two subgroup. The quadratic Gauss character identifies its fixed field with (7.2). Consequently, for a representation over $\mathbf Q$, failure of absolute irreducibility after cyclotomic restriction has one explicitly named inducing field.

If $2\in S$, more quadratic fields appear because a fundamental discriminant can have a factor $-4$, $8$, or $-8$. The correct list is obtained by squareclasses supported on $2\ell$ followed by the fundamental-discriminant condition; one must not keep all formal products. If auxiliary odd primes occur, their squareclasses enlarge the list similarly. This elementary calculation is the rational version of the ray-class procedure in Section 6.4.

Now suppose the projective image is $A_4$. The projective field $K^{\mathrm{proj}}$ has a normal Klein-four subfield structure and a cyclic cubic quotient. Thus there must be a cyclic cubic extension of $\mathbf Q$ unramified outside $S$. For a modulus $\mathfrak m$, global reciprocity identifies such extensions with order-three quotients of the ray class group. If that group has no $3$-torsion, projective $A_4$ is impossible.

For projective $S_4$, the sign quotient gives a quadratic field supported on $S$. This test can leave several candidates, after which the $S_3$ quotient and the inertia cycle types refine them. For projective $A_5$, no nontrivial abelian quotient exists. The degree of the projective field is $60$, and elimination requires genuinely nonabelian information: for example, a proven discriminant ceiling together with a degree-sensitive lower bound, or enough Frobenius factorizations to contradict the conjugacy classes of $A_5$.

Finally consider the local condition at $\ell$. Finite flatness ensures an integral model but does not say the projective field is unramified. The determinant $\bar\chi_\ell$ itself is ramified at $\ell$, and a scalar part of that ramification disappears projectively. A numerical root-discriminant argument therefore requires an independently established upper-break cutoff for the full module or its projective quotient. Once supplied, the ramification theory converts it to a discriminant bound; before it is supplied, no degree exclusion is justified.

This worked ledger illustrates the general method. Dickson reduces the problem to a short list. Abelian class field theory attacks dihedral, $A_4$, and $S_4$ quotient data. Local finite-flat theory controls the coefficient place only to the extent actually proved. A remaining $A_5$ or large case calls for a nonabelian argument. No step uses the desired image conclusion as an input.

## 8. Cohomology of the image

### 8.1 The adjoint module

Image size matters in deformation theory because infinitesimal deformations are measured by cohomology. Let

$$
\operatorname{ad}V=\operatorname{End}_k(V),
\qquad
\operatorname{ad}^0V=\{A:\operatorname{tr}A=0\},
\tag{8.1}
$$

with conjugation action. If $\ell\ne2$, then

$$
\operatorname{ad}V=k\cdot I\oplus\operatorname{ad}^0V.
\tag{8.2}
$$

Absolute irreducibility gives $(\operatorname{ad}^0V)^G=0$. The group $H^1(G,\operatorname{ad}^0V)$ measures infinitesimal deformations of the finite image not arising from conjugation, while $H^1(G,k)$ measures additive characters of the image.

For a finite group, a cocycle is a function $c:G\to M$ satisfying

$$
c(gh)=c(g)+g\,c(h),
\tag{8.3}
$$

and a coboundary has form $c(g)=g m-m$. These explicit formulas will be enough.

### 8.2 Averaging and prime-to-ell groups

**Lemma 8.1.** If $G$ is finite and $\ell\nmid|G|$, then $H^i(G,M)=0$ for every $i>0$ and every finite-dimensional $k[G]$-module $M$.

**Proof.** The invariants functor is exact: for a surjection $M\to N$ and $n\in N^G$, lift $n$ to $m$ and replace $m$ by

$$
\frac1{|G|}\sum_{g\in G}gm.
$$

This is an invariant lift. Since group cohomology is the derived functor of invariants, higher cohomology vanishes. In degree one one can see it directly: for a cocycle $c$, put
$m=-|G|^{-1}\sum_g c(g)$; then (8.3) gives $c(h)=hm-m$. $\square$

This lemma settles all dihedral images in odd characteristic when their rotation order is prime to $\ell$, and all exceptional images when $\ell\ge7$.

### 8.3 Central scalars and inflation--restriction

The adjoint action kills scalars, so projective calculations can often be lifted to the full image.

Let $C=G\cap Z$. The inflation--restriction sequence begins

$$
0\to H^1(G/C,M^C)\to H^1(G,M)
\to H^1(C,M)^{G/C}.
\tag{8.4}
$$

For $M=\operatorname{ad}^0V$, one has $M^C=M$. Moreover $|C|$ divides $|k^\times|$, so $\ell\nmid|C|$ and $H^1(C,M)=0$. Therefore

$$
H^1(G,\operatorname{ad}^0V)
\simeq H^1(\overline G,\operatorname{ad}^0V).
\tag{8.5}
$$

The same reasoning applies to trivial coefficients. Thus central scalar extensions neither create nor remove the first-cohomology obstruction in characteristic $\ell$.

### 8.4 Cohomology for groups containing special linear groups

The large branch has order divisible by $\ell$, so averaging is unavailable. The required replacement is an explicit rank-one calculation.

**Proposition 8.2.** Let $q=\ell^f$ with $\ell\ge7$, let $V$ be the natural two-dimensional $\mathbf F_q$-module, and let $k$ contain $\mathbf F_q$. Then

$$
H^1(\operatorname{SL}_2(\mathbf F_q),k)=0,
\qquad
H^1(\operatorname{SL}_2(\mathbf F_q),\operatorname{ad}^0V)=0.
\tag{8.6}
$$

**Proof strategy.** The first group vanishes because $\operatorname{SL}_2(\mathbf F_q)$ is perfect. For the second, restrict a cocycle to the upper unipotent subgroup, use the diagonal torus to isolate weights, subtract a coboundary, and then use the Weyl element and the elementary generators.

**Proof.** Write

$$
e=\begin{pmatrix}0&1\\0&0\end{pmatrix},\quad
h=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
f=\begin{pmatrix}0&0\\1&0\end{pmatrix}.
$$

For $d(t)=\operatorname{diag}(t,t^{-1})$, conjugation has weights $t^2,1,t^{-2}$ on $e,h,f$. Let $z$ be a cocycle. Since the torus $T$ has order prime to $\ell$, subtract a coboundary so that $z|_T=0$. From

$$
d(t)u(a)d(t)^{-1}=u(t^2a)
\tag{8.7}
$$

and the cocycle identity, the three coordinates of $z(u(a))$ satisfy respectively the weight relations of degrees $2,0,-2$. To make the coefficient step explicit, conjugation by $u(a)$ acts through

$$
e\longmapsto e,
\qquad
h\longmapsto h-2ae,
\qquad
f\longmapsto f+ah-a^2e.
$$

Write $z(u(a))=A(a)e+B(a)h+C(a)f$. Substitution in $u(a+b)=u(a)u(b)$ gives

$$
\begin{aligned}
C(a+b)&=C(a)+C(b),\\
B(a+b)&=B(a)+B(b)+aC(b),\\
A(a+b)&=A(a)+A(b)-2aB(b)-a^2C(b).
\end{aligned}
$$

Equation (8.7) gives the corresponding three torus-weight identities. Comparing these identities for all $a,b,t\in\mathbf F_q$, and then using the same equations after conjugation by $w$, leaves exactly the coboundary solutions. Equivalently,

$$
z(u(a))=u(a)m-m
\tag{8.8}
$$

for one $m$ fixed by $T$. Subtract this coboundary as well; then $z$ vanishes on $T$ and on the upper unipotent group $U$.

Let $w=\left(\begin{smallmatrix}0&-1\\1&0\end{smallmatrix}\right)$. From $w^2=-I$, whose adjoint action is trivial, we get $(1+w)z(w)=0$. The relation $wd(t)w^{-1}=d(t^{-1})$ says $z(w)$ is $T$-fixed, hence is a multiple of $h$. But $whw^{-1}=-h$, and $(1+w)z(w)=0$ leaves this possibility; the relation

$$
w u(1) w^{-1}=v(-1)
$$

together with the elementary identity expressing $d(t)$ through $u$ and $v$ forces that multiple to be zero. Thus $z(w)=0$. Since $wUw^{-1}$ is the lower unipotent group and $U,w$ generate $\operatorname{SL}_2(\mathbf F_q)$, $z=0$.

The last comparison is ordinary polynomial coefficient comparison of degree at most four. In characteristics at least seven its coefficients $2,3,4,5$ remain distinguishable; in characteristics three and five additional solutions may survive. Finally, elementary matrices show that $\operatorname{SL}_2(\mathbf F_q)$ is perfect for $q>3$: commutators with $d(t)$ generate $U$ and its opposite, and these generate the group. Hence $H^1(\operatorname{SL}_2(\mathbf F_q),k)=\operatorname{Hom}(\operatorname{SL}_2(\mathbf F_q),k^+)=0$. $\square$

If $G$ contains $\operatorname{SL}_2(\mathbf F_q)$ normally with quotient of order prime to $\ell$, inflation--restriction and taking quotient invariants extend (8.6) to $G$.

### 8.5 The adjoint module in the dihedral case

The prime-to-$\ell$ averaging proof already settles dihedral adequacy, but the module decomposition explains what arithmetic classes would appear without that vanishing.

Write $\rho=\operatorname{Ind}_{\Gamma_M}^{\Gamma}\theta$ and set

$$
\varphi=\theta/\theta^s,
\qquad
\delta=\text{the quadratic character of }\Gamma/\Gamma_M.
$$

In the induced basis, trace-zero diagonal matrices form a line on which an element outside $\Gamma_M$ acts by $-1$. Hence that line is $k(\delta)$. The off-diagonal matrices restrict to the two characters $\varphi$ and $\varphi^{-1}$, exchanged by $s$. Therefore

$$
\operatorname{ad}^0\rho
\simeq k(\delta)\oplus
\operatorname{Ind}_{\Gamma_M}^{\Gamma}\varphi.
\tag{8.9}
$$

This can be checked directly. If

$$
e=\begin{pmatrix}0&1\\0&0\end{pmatrix},
\qquad
f=\begin{pmatrix}0&0\\1&0\end{pmatrix},
\qquad
h=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
$$

then $\Gamma_M$ acts on $e,f,h$ through $\varphi,\varphi^{-1},1$, while an antidiagonal element exchanges $e$ and $f$ and negates $h$.

Formula (8.9) shows why merely calling a dihedral image “small” is inadequate. Its adjoint deformation problem separates into a quadratic character direction and an induced rotation direction. Globally, Shapiro's lemma identifies cohomology of the induced summand with cohomology over $M$. Locally, the conductors of $\delta$ and $\varphi$ can behave differently. In the finite image itself, however, Dickson's rotation order is prime to odd $\ell$, so averaging kills both first-cohomology groups.

There are two degeneracies. If $\varphi=1$, the original induction is reducible. If $\varphi$ has order two, the projective image is Klein four and more than one index-two subgroup may serve as a “rotation” subgroup. The intrinsic inducing field statement therefore requires either rotation order greater than two or an explicit choice among the three quadratic characters.

## 9. Adequacy

### 9.1 Why absolute irreducibility is not enough

Absolute irreducibility says that the only invariant endomorphisms are scalars. Prime selection and deformation arguments need more: first cohomology must not hide infinitesimal image deformations, and semisimple elements must detect every endomorphism direction. Adequacy packages exactly these finite-group requirements.

The condition is deliberately weaker than requiring the full image to contain $\operatorname{SL}_2(k)$. Prime-to-$\ell$ dihedral and exceptional images can be adequate even though they are small. Conversely, an image that looks large projectively at coefficient five can fail because its order is divisible by five and an adjoint cohomology class survives.

### 9.2 Definition and elementary permanence

Let $V$ be a finite-dimensional $k$-space and $G\subset\operatorname{GL}(V)$ finite. Assume $V$ is absolutely irreducible. We call $G$ **adequate on $V$** if:

1. $\ell\nmid\dim_kV$;
2. $H^1(G,k)=0$ for the trivial action;
3. $H^1(G,\operatorname{ad}^0V)=0$;
4. the $k$-linear span in $\operatorname{End}(V)$ of the semisimple elements of $G$ is all of $\operatorname{End}(V)$.

For dimension two, clause 1 is exactly $\ell\ne2$. Absolute irreducibility already gives $H^0(G,\operatorname{ad}^0V)=0$.

Finite extension of $k$ preserves adequacy: both cohomology groups tensor with the larger field, and the semisimple span tensors as well. Adding or removing a central subgroup of order prime to $\ell$ preserves clauses 2 and 3 by (8.4); the spanning clause must still be read in the actual matrix image, although scalar multiples do not change semisimplicity.

### 9.3 The semisimple spanning condition

The fourth clause has a useful dual form. The trace pairing

$$
\langle A,B\rangle=\operatorname{tr}(AB)
\tag{9.1}
$$

is nondegenerate on $\operatorname{End}(V)$. Hence semisimple elements span if and only if the only $A$ satisfying $\operatorname{tr}(Ag)=0$ for every semisimple $g\in G$ is $A=0$.

**Lemma 9.1.** If $\ell\nmid|G|$ and $V$ is absolutely irreducible, then the semisimple elements of $G$ span $\operatorname{End}(V)$.

**Proof.** Every element of $G$ is semisimple because its minimal polynomial divides $X^{|G|}-1$, which is separable. Burnside's theorem in dimension two says that the algebra generated by an absolutely irreducible matrix group over an algebraically closed field is the full endomorphism algebra. Here is a direct proof. If the generated algebra $A$ were proper, choose a nonzero vector with $Av$ of minimal positive dimension. If $Av$ were one-dimensional it would be a stable line. If it were two-dimensional, the maps in $A$ sending $v$ through a basis and the absence of a common invariant line produce the four matrix units by linear combinations, forcing $A=\operatorname{End}(V)$. Scalar descent then gives the assertion over $k$. Since every generator is semisimple, their linear span is full. $\square$

### 9.4 Dihedral and exceptional prime-to-ell images

**Proposition 9.2.** Let $\ell>2$ and let $G\subset\operatorname{GL}_2(k)$ act absolutely irreducibly. If $\ell\nmid|\overline G|$, then $G$ is adequate.

**Proof.** The scalar kernel has order dividing $|k^\times|$, hence is prime to $\ell$. Thus $\ell\nmid|G|$. Lemma 8.1 gives both cohomology vanishings, and Lemma 9.1 gives semisimple spanning. $\square$

In particular all absolutely irreducible dihedral images from Dickson's theorem are adequate for odd $\ell$, because their rotation order is prime to $\ell$. Exceptional images are adequate whenever $\ell\nmid60$.

### 9.5 Examples and failure tests

Several examples clarify the independence of the adequacy clauses.

An absolutely irreducible representation of a prime-to-$\ell$ group is automatically adequate, regardless of how small its projective image is. For instance, the matrices $r,s$ of Section 1.5 give an adequate dihedral image as soon as the rotation order and $2$ are prime to $\ell$. Thus “adequate” is not synonymous with “contains a large special-linear group.”

Absolute irreducibility alone gives the zeroth-cohomology statement

$$
H^0(G,\operatorname{ad}^0V)=0,
$$

but it says nothing formal about $H^1$. A nontrivial extension of the finite image by the additive adjoint module can remain invisible to invariant endomorphisms. The characteristic-five icosahedral example in Chapter 11 exhibits exactly this phenomenon.

The semisimple span can also fail independently in small characteristic. If a group is generated entirely by unipotent elements, the individual generators need not span the endomorphism algebra even when the algebra they generate multiplicatively is large. Adequacy asks for a **linear** span by semisimple elements. Lemma 10.1 repairs this for special-linear groups by using semisimple conjugates of diagonal matrices rather than the unipotent generators themselves.

Finally, reducibility always destroys adequacy as defined here. If $L\subset V$ is a stable line, the algebra generated by $G$ lies in a conjugate of the upper triangular algebra, so it cannot span all of $\operatorname{End}(V)$. This remains true even if $H^1(G,k)$ and $H^1(G,\operatorname{ad}^0V)$ happen to vanish. The absolute irreducibility hypothesis is therefore structural, not redundant shorthand for the cohomological clauses.

## 10. The adequate-image theorem in dimension two

### 10.1 The large-image calculation

It remains to verify semisimple spanning in the defining characteristic for the large branch.

**Lemma 10.1.** Let $q=\ell^f>3$ with $\ell>2$. On the natural two-dimensional module, the semisimple elements of $\operatorname{SL}_2(\mathbf F_q)$ span $M_2(\mathbf F_q)$.

**Proof.** Diagonal elements span the diagonal subspace: for $t\ne\pm1$, the matrices $I$ and $d(t)$ are independent there. Conjugate $d(t)$ by $u(a)$:

$$
u(a)d(t)u(a)^{-1}
=\begin{pmatrix}t&a(t^{-1}-t)\\0&t^{-1}\end{pmatrix}.
$$

This is semisimple, being conjugate to $d(t)$, and subtracting $d(t)$ produces a nonzero multiple of $e_{12}$. Conjugation by the Weyl element produces $e_{21}$. Together with diagonal matrices these form a basis of $M_2$. $\square$

Combining Lemma 10.1 with Proposition 8.2 proves adequacy for the special-linear core. If $G$ normalizes that core and the quotient has order prime to $\ell$, inflation--restriction preserves the cohomology vanishings, while the same semisimple matrices remain in $G$ and continue to span.

### 10.2 The theorem for coefficient primes at least seven

**Theorem 10.2 (adequate image in dimension two).** Let $k$ be a finite field of characteristic $\ell\ge7$, and let $G\subset\operatorname{GL}_2(k)$ act absolutely irreducibly. Then $G$ is adequate.

**Proof.** Apply Dickson's classification to $\overline G$. Borel and cyclic cases are excluded by absolute irreducibility. In the dihedral case the projective order is prime to $\ell$, so Proposition 9.2 applies. In the exceptional case $\ell\nmid60$, so the same proposition applies.

In the remaining case, $\overline G$ contains $\operatorname{PSL}_2(k_0)$ for a finite field $k_0$ of characteristic $\ell$. Its inverse image has a normal special-linear central cover, and the quotient contributed by scalars and projective determinants has order prime to $\ell$. Proposition 8.2 and Lemma 10.1, followed by inflation--restriction, give all adequacy clauses. $\square$

The theorem says **every absolutely irreducible** two-dimensional image is adequate at $\ell\ge7$; it does not say every such image contains $\operatorname{SL}_2(k)$. Adequacy is the cohomological conclusion, while “big image” is a stronger group-containment conclusion.

### 10.3 Regular semisimple detection

The spanning clause is designed to detect nonzero stable subspaces of the adjoint module.

**Corollary 10.3.** Suppose $G$ is adequate on a two-dimensional $V$, and let $0\ne W\subset\operatorname{ad}^0V$ be $G$-stable. For every nonzero $w\in W$, after a finite coefficient extension there is a regular semisimple $g\in G$ such that

$$
\operatorname{tr}(wg)\ne0.
\tag{10.1}
$$

**Proof.** If $w$ paired trivially with every semisimple element, adequacy and nondegeneracy of the trace pairing would give $w=0$. Thus some semisimple $g$ has nonzero pairing. A scalar $g$ pairs trivially with $w$ because $\operatorname{tr}w=0$, so $g$ is nonscalar. In dimension two a nonscalar semisimple element has two distinct eigenvalues after a finite coefficient extension, hence is regular semisimple. $\square$

This is the algebraic heart of auxiliary-prime selection: a cohomology class has a direction, and a regular semisimple conjugacy class detects it. Distribution of that conjugacy class among arithmetic primes is a separate global input.

### 10.4 Cyclotomic adequacy

Taylor--Wiles arguments use the image over the cyclotomic extension rather than automatically the image over $F$.

**Theorem 10.4.** Let $\ell\ge7$ and let
$\bar\rho:G_F\to\operatorname{GL}_2(k)$. If
$\bar\rho|_{G_{F(\zeta_\ell)}}$ is absolutely irreducible, then its image is adequate. If the restriction is reducible while $\bar\rho$ is absolutely irreducible, then $\bar\rho$ is induced from the quadratic subextension described in Corollary 5.2.

**Proof.** Apply Theorem 10.2 to the restricted finite image. The second assertion is Corollary 5.2. $\square$

Thus a usable hypothesis is not merely “$\bar\rho$ is absolutely irreducible,” but “the cyclotomic restriction is absolutely irreducible.” The latter can fail only through a sharply described dihedral branch.

### 10.5 Normal subgroups and overgroups

Adequacy is not monotone for arbitrary subgroup inclusion. Restricting to a subgroup can make an irreducible representation reducible, create first cohomology, or lose semisimple detectors. Passing to an overgroup can introduce an $\ell$-power quotient. The safe permanence statements use normality and prime-to-$\ell$ quotients.

**Proposition 10.5.** Let $H\triangleleft G\subset\operatorname{GL}(V)$ with $[G:H]$ prime to $\ell$. Assume $H$ is adequate on $V$. If $H^1(G/H,k)=0$, then $G$ is adequate.

**Proof.** Absolute irreducibility for $H$ implies it for $G$. The semisimple elements of $H$ already span $\operatorname{End}(V)$, so the same is true in $G$. Inflation--restriction gives

$$
0\to H^1(G/H,M^H)\to H^1(G,M)\to H^1(H,M)^{G/H}
\tag{10.2}
$$

for $M=k$ and $M=\operatorname{ad}^0V$. For the adjoint module, $M^H=0$ and the right term vanishes by adequacy. For trivial coefficients, the stated hypothesis kills the left term and adequacy of $H$ kills the right. Thus both first cohomology groups vanish. $\square$

When $G/H$ has order prime to $\ell$, $H^1(G/H,k)=0$ automatically by averaging. This is the form used for a special-linear core inside a group enlarged by determinants and scalars.

The reverse direction requires more. If $G$ is adequate and $H\triangleleft G$ has prime-to-$\ell$ index, $H$ need not remain absolutely irreducible. Proposition 5.1 shows the rank-two failure: $H$ may preserve two lines exchanged by $G$. Cyclotomic restriction is precisely such a normal prime-to-$\ell$ restriction, which is why its absolute irreducibility appears as a separate hypothesis.

There is also a useful equality-of-image criterion. If $N\triangleleft\Gamma$ and the full cutout field of $\rho$ is linearly disjoint from the fixed field of $N$, then $\rho(N)=\rho(\Gamma)$. Adequacy is then literally unchanged, with no permanence theorem needed. Arithmetic constructions should prefer this stronger situation whenever they can impose disjointness.

### 10.6 Worked adequacy decisions

Suppose first that $\ell=7$ and the projective image is $S_4$. Its order is $24$, and the scalar kernel has order dividing $|k^\times|$, which is prime to seven. If the representation is absolutely irreducible, Proposition 9.2 proves adequacy immediately. There is no need to enlarge the image to a special-linear group.

Now let the projective image contain $\operatorname{PSL}_2(\mathbf F_7)$. The group order is divisible by seven, so averaging is invalid. Proposition 8.2 supplies the adjoint cohomology vanishing, Lemma 10.1 supplies semisimple spanning, and perfectness supplies scalar $H^1$ vanishing. This is the large-image proof, and it uses different reasoning from the preceding $S_4$ case even though the conclusion is the same.

Let $k=\mathbf F_7$ and let the image be a nonsplit cyclic torus. The natural representation is irreducible over $k$ but splits over $\mathbf F_{49}$. It fails the absolute irreducibility hypothesis and is not adequate under the definition in Section 9.2. Averaging does make its positive cohomology vanish, but the semisimple matrices span only the two-dimensional torus algebra, not all four dimensions of $M_2(k)$.

Finally, let an adequate representation of $G_F$ become reducible over $G_{F(\zeta_\ell)}$. Proposition 5.1 identifies a quadratic induction. Adequacy of the original image says nothing about adequacy of the reducible restricted image. This example is why Theorem 10.4 tests the cyclotomic image directly rather than trying to descend adequacy through a normal subgroup.

## 11. The coefficient-five boundary

### 11.1 Why five is structurally different

At $\ell=5$, the exceptional group $A_5$ has order divisible by the coefficient characteristic and is simultaneously

$$
A_5\simeq\operatorname{PSL}_2(\mathbf F_5).
\tag{11.1}
$$

Thus “exceptional” and “large over the prime field” meet at precisely the point where the weight-separation argument in Proposition 8.2 can fail. Averaging is unavailable, and absolute irreducibility alone no longer forces adjoint $H^1$ to vanish.

The dihedral cases whose projective order is prime to five remain adequate. The groups $A_4$ and $S_4$ also remain prime-to-five and hence adequate. The only new two-dimensional obstruction in the Dickson list is the icosahedral projective image.

### 11.2 The icosahedral cohomology calculation

**Proposition 11.1.** Let $V$ be the natural two-dimensional $\mathbf F_5$-module for $\operatorname{SL}_2(\mathbf F_5)$. Then

$$
\dim_{\mathbf F_5}H^1(\operatorname{SL}_2(\mathbf F_5),\operatorname{ad}^0V)=1.
\tag{11.2}
$$

Consequently a matrix group with projective image $A_5$ in its natural characteristic-five realization is not adequate.

**Proof.** We record the calculation because it is exactly the boundary of the general theorem. Use the generators

$$
u=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
w=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
d=\begin{pmatrix}2&0\\0&3\end{pmatrix}.
$$

They satisfy $u^5=1$, $w^2=-I$, $d^2=-I$, $dud^{-1}=u^4$, and the elementary Bruhat relations. Write a cocycle's values on $u,w,d$ in the basis $e,h,f$ of Section 8.4. Since $\langle d\rangle$ has order prime to five in the adjoint quotient, subtract a coboundary to make $z(d)=0$. The conjugation relation forces

$$
z(u)=a e+b(h+2f)
$$

for two parameters $a,b$. The relation $w^2=-I$ and the Bruhat relation force

$$
z(w)=b(e-f)+\text{the coboundary determined by }a.
$$

Subtracting that last coboundary kills $a$ and leaves one free parameter $b$. Direct substitution in the remaining relations shows that every $b$ gives a cocycle. A coboundary vanishing on $d$ comes from a $d$-fixed multiple of $h$; its value on $u$ has no $h+2f$ component, so it cannot kill $b$. Hence the quotient of cocycles by coboundaries is one-dimensional.

The center acts trivially on $\operatorname{ad}^0V$ and has order two, so (8.5) carries the same nonzero class to the projective $A_5$ action. $\square$

The calculation also explains the failure in Proposition 8.2: over $\mathbf F_5$, the torus weights used there collide, leaving the $b$-direction.

### 11.3 Safe statements at five

The correct coefficient-five conclusion is therefore a case distinction.

**Theorem 11.2.** Let $G\subset\operatorname{GL}_2(k)$ be absolutely irreducible in characteristic five.

- If its projective image is cyclic or Borel, absolute irreducibility fails.
- If its projective image is dihedral, $A_4$, or $S_4$, and has order prime to five, then $G$ is adequate.
- If its projective image is $A_5\simeq\operatorname{PSL}_2(\mathbf F_5)$ in the natural characteristic-five realization, adequacy can fail and in the basic case does fail by Proposition 11.1.
- If the projective image contains $\operatorname{PSL}_2(\mathbf F_{5^f})$ with $f>1$, it requires its own cohomological verification; it is not justified by quoting the $\ell\ge7$ theorem.

**Proof.** The first clause is Section 4.1. Dihedral, $A_4$, and $S_4$ projective orders are prime to five in the stated cases, so Proposition 9.2 proves the second clause. Proposition 11.1 proves the claimed failure for the natural $A_5$ lift. None of the preceding arguments proves the final large-field case: averaging fails because five divides the group order, while Proposition 8.2 assumes $\ell\ge7$. Thus that case is deliberately left as a required direct verification rather than assigned an unsupported conclusion. $\square$

This volume makes no blanket modularity-lifting or prime-selection assertion at five. Any theorem there must explicitly eliminate the icosahedral case or replace adequacy by a small-image argument. This is a mathematical boundary, not a matter of notation.

### 11.4 The smaller primes

Although the later clean theory begins at seven and the catalog singles out five, a complete image audit should record why two and three are still further away.

At $\ell=2$, the dimension of $V$ is divisible by the coefficient characteristic, violating the first adequacy clause. Trace zero also contains the scalar matrix because $\operatorname{tr}I=0$, so the decomposition

$$
\operatorname{ad}V=kI\oplus\operatorname{ad}^0V
$$

fails. Oddness cannot be read as determinant $-1$, since $-1=1$. The entire dimension-two formulation must be modified.

At $\ell=3$, the exceptional groups $A_4$ and $S_4$ have order divisible by three, and the coincidences

$$
\operatorname{PSL}_2(\mathbf F_3)\simeq A_4,
\qquad
\operatorname{PGL}_2(\mathbf F_3)\simeq S_4
$$

place them in the same dangerous overlap of exceptional and defining-characteristic cases that $A_5$ occupies at five. Torus weights in the cocycle calculation collide even more severely. Consequently neither an $\ell\ge7$ theorem nor the prime-to-$\ell$ averaging theorem applies.

These observations are not claims that every characteristic-three image is inadequate. Prime-to-three dihedral groups, for example, are still handled by Proposition 9.2. They say that there is no uniform conclusion from absolute irreducibility alone. Each small projective group and its central lift must be calculated directly.

## 12. Big image and arithmetic use

### 12.1 Projectively large versus full special-linear image

Suppose $q_0>3$ and $\overline G$ contains $\operatorname{PSL}_2(\mathbf F_{q_0})$. Let $G_0$ be its inverse image in $G$. Commutators kill scalar ambiguity, and the universal central extension represented by $\operatorname{SL}_2(\mathbf F_{q_0})$ yields

$$
\operatorname{SL}_2(\mathbf F_{q_0})\subseteq [G_0,G_0]
\tag{12.1}
$$

after conjugating and extending coefficients if necessary.

To see this concretely, lift upper and lower projective unipotents. Their orders are powers of $\ell$, while the scalar kernel has order prime to $\ell$, so each has a unique lift of the same $\ell$-power order. The commutator relations among these lifts are the elementary $\operatorname{SL}_2$ relations. They generate the special-linear subgroup; scalar errors vanish because an element simultaneously of $\ell$-power order and scalar prime-to-$\ell$ order is trivial.

Thus projective largeness supplies a special-linear core over $k_0$. It supplies $\operatorname{SL}_2(k)$ only if $k_0=k$.

### 12.2 A trace-field big-image criterion

**Theorem 12.1.** Let $k$ have characteristic $\ell\ge7$, let $G\subset\operatorname{GL}_2(k)$ act absolutely irreducibly, and assume its projective image is in the large branch. If the projective trace field is $k$, then, after conjugation,

$$
\operatorname{SL}_2(k)\subseteq G.
\tag{12.2}
$$

**Proof.** Dickson supplies $k_0$ with a projective special-linear core. Proposition 4.2 identifies $k_0$ with the projective trace field, so $k_0=k$. The lifting argument of Section 12.1 gives (12.2). $\square$

If $k_{\mathrm{ptr}}$ is proper, the same proof gives $\operatorname{SL}_2(k_{\mathrm{ptr}})$, not the stronger conclusion. Enlarging coefficient scalars does not enlarge the image, so one cannot manufacture full-field bigness by changing notation.

### 12.3 Taylor--Wiles input

The group-theoretic output used in prime selection can now be stated without slogans. Let

$$
H=\bar\rho(G_{F(\zeta_\ell)}).
$$

For $\ell\ge7$, absolute irreducibility of this restriction gives:

$$
H^1(H,k)=0,\qquad
H^1(H,\operatorname{ad}^0V)=0,
\tag{12.3}
$$

and semisimple elements span $\operatorname{End}(V)$. Corollary 10.3 then supplies regular semisimple detectors for nonzero adjoint directions. These are exactly the finite-image facts needed before an arithmetic distribution theorem is invoked to realize detecting conjugacy classes at auxiliary primes.

One further global group may appear in a deformation argument, namely
$H^0(G_F,\operatorname{ad}^0V(1))$. This is a self-twist question, not one of the four adequacy clauses. A nonzero invariant gives a nonzero map

$$
V\longrightarrow V(1).
$$

By absolute irreducibility it is an isomorphism. Taking determinants forces $\bar\chi_\ell^2=1$ on the relevant group. If that is impossible, the invariant vanishes. If the cyclotomic character becomes quadratic, the surviving possibility must be checked; Clifford theory again turns a nontrivial quadratic self-twist into a dihedral structure. Adequacy and adjoint-twist invariants must therefore be recorded separately.

### 12.4 Potential modularity and preservation of image

Potential modularity changes the ground field, so adequacy must be checked after restriction. If an auxiliary extension $L/F$ is linearly disjoint from the full residual cutout field, equation (5.2) shows that the matrix image is unchanged. Every image property—absolute irreducibility, projective trace field, special-linear containment, and adequacy—is then preserved.

It is enough to impose disjointness from the projective field only for projective type; scalar and determinant fields can still shrink. When a later argument needs the exact determinant image or full matrix image, disjointness must include the full cutout field. This distinction prevents a base change that preserves $A_5$ projectively, for example, from silently changing its central lift.

Solvable base change is not automatically harmless. Solvability says nothing about intersection with the residual field. The correct sequence is: identify the finite field whose image must be preserved, impose disjointness from it, and only then use the arithmetic construction of the auxiliary extension.

### 12.5 The detection mechanism in detail

We finish the arithmetic interface by isolating what the finite image contributes to an auxiliary-prime argument. Let $H$ be the image over the cyclotomic field and put $M=\operatorname{ad}^0V$. Suppose a global cocycle class is represented on the kernel of $\bar\rho$ by a nonzero $H$-equivariant homomorphism

$$
\phi:N\longrightarrow M.
\tag{12.4}
$$

The appearance of such a homomorphism comes from inflation--restriction: the vanishing $H^1(H,M)=0$ ensures that a class not already killed on the residual kernel cannot be absorbed by a cocycle on the finite image. Its image $W=\phi(N)$ is a nonzero $H$-stable subspace.

Choose $0\ne w\in W$. Adequacy supplies a semisimple $h\in H$ with

$$
\operatorname{tr}(wh)\ne0.
\tag{12.5}
$$

Because $w$ is trace zero, $h$ is nonscalar; after extending coefficients it has distinct eigenvalues $\alpha,\beta$. Multiplying an element of the residual kernel mapping to $w$ by a lift of $h$ produces an element in the cocycle extension whose residual semisimple part is $h$ and whose infinitesimal part is detected by (12.5).

At a Taylor--Wiles prime one also prescribes a congruence on the residue cardinality, so that the cyclotomic value is $1$ modulo a chosen power of $\ell$. That congruence concerns an abelian cyclotomic extension. The detecting element concerns the generally nonabelian cocycle extension. Linear disjointness and compatibility of the two conjugacy requirements must be checked before any distribution theorem is applied.

The role of each adequacy clause is now visible:

- $H^1(H,k)=0$ prevents an unwanted additive scalar quotient of the image;
- $H^1(H,M)=0$ makes restriction to the residual kernel detect global adjoint classes;
- semisimple spanning produces an $h$ that sees a chosen nonzero direction;
- absolute irreducibility removes invariant trace-zero endomorphisms and keeps the deformation problem non-Eisenstein.

Adequacy does not itself assert the existence of an arithmetic prime with the desired Frobenius. It proves that the required conjugacy class exists in the finite extension. A separate distribution theorem realizes that class. This division of labor is essential for avoiding a circular prime-selection proof.

### 12.6 Reconstructing the full image

Suppose the projective analysis has shown

$$
\operatorname{PSL}_2(k)\subseteq\overline G\subseteq\operatorname{PGL}_2(k)
$$

and Section 12.1 has lifted the derived subgroup to $\operatorname{SL}_2(k)\subseteq G$. What remains is abelian. The determinant map gives an exact sequence

$$
1\longrightarrow G\cap\operatorname{SL}_2(k)
\longrightarrow G\xrightarrow{\det}\det(G)\longrightarrow1.
\tag{12.6}
$$

Since the kernel already contains $\operatorname{SL}_2(k)$, it equals $\operatorname{SL}_2(k)$. Hence $G$ is the full inverse image under determinant of the subgroup $D=\det(G)\subseteq k^\times$:

$$
G=\{g\in\operatorname{GL}_2(k):\det g\in D\},
\tag{12.7}
$$

The projective image is all of $\operatorname{PGL}_2(k)$ exactly when $D$ contains a nonsquare; if $D$ consists only of squares, it is $\operatorname{PSL}_2(k)$. Thus the projective distinction is already encoded by the determinant squareclasses.

To prove (12.7), take a matrix $x$ with determinant in $D$. Choose $g\in G$ with the same determinant. Then $xg^{-1}\in\operatorname{SL}_2(k)\subseteq G$, so $x\in G$. This elementary argument shows why determinant information completes a genuinely full projective image.

For elliptic-curve torsion over a field $F$, $D$ is the image of $\bar\chi_\ell|_{G_F}$. If $F\cap\mathbf Q(\zeta_\ell)=\mathbf Q$, then $D=\mathbf F_\ell^\times$ for prime-field coefficients. Once $G$ contains $\operatorname{SL}_2(\mathbf F_\ell)$, equation (12.7) gives $G=\operatorname{GL}_2(\mathbf F_\ell)$. If the cyclotomic intersection is nontrivial, the determinant image is smaller and the correct full image is its determinant inverse image, not all of $\operatorname{GL}_2$.

For coefficient fields larger than $\mathbf F_\ell$, the cyclotomic determinant still lands in the prime-field subgroup. A representation can contain $\operatorname{SL}_2(k)$ while its determinants lie in $\mathbf F_\ell^\times$. Thus “big” should usually mean special-linear containment plus a separately recorded determinant image. Requiring equality with $\operatorname{GL}_2(k)$ would be unnecessarily strong and often false.

## 13. A final image protocol

### 13.1 The decision tree

Given a two-dimensional residual representation, the following order avoids circular arguments.

First verify the coefficient characteristic, continuity, determinant, and absolute irreducibility. Then form both full and projective cutout fields; do not identify them. Compute or bound the projective trace field.

Next apply Dickson's theorem. A fixed projective point means reducibility. A cyclic projective image means failure of absolute irreducibility. A dihedral image produces an explicit quadratic character and an induced representation. Exceptional image means one of $A_4,S_4,A_5$, with its central lift still to determine. Large image means a projective special-linear core over the trace field.

Then impose arithmetic. Unramified places remain unramified in every quotient. Multiplicative inertia is read from the minimal-discriminant exponent. Finite flatness at $\ell$ is kept as an integral model condition unless a separate theorem supplies a numerical ramification bound. Dihedral quadratic fields and exceptional abelian quotients are tested in the appropriate ray class groups.

Finally address adequacy on the group that will actually be used. At $\ell\ge7$, absolute irreducibility suffices. For Taylor--Wiles applications this means absolute irreducibility after cyclotomic restriction. At five, isolate projective $A_5$ and perform a separate argument. Under base change, preserve the residual image by linear disjointness rather than by hope.

### 13.2 The package established

The finite subgroup theorem and the arithmetic interfaces now form one reusable package. Every finite projective image in dimension two is Borel, cyclic, dihedral, exceptional, or subfield-large. Absolute irreducibility removes the first two. Dihedrality is exactly quadratic induction; failure of cyclotomic irreducibility is a particularly constrained instance of it. Exceptional images are three named groups. Large images contain a special-linear core over the projective trace field, and full trace field upgrades this to full special-linear containment.

The cohomological conclusions are equally precise. Prime-to-$\ell$ absolutely irreducible images are adequate. Groups containing a defining-characteristic special-linear core are adequate in dimension two for $\ell\ge7$. Hence every absolutely irreducible two-dimensional residual image is adequate at those primes, including after cyclotomic restriction when that restriction remains absolutely irreducible. Adequacy supplies vanishing of scalar and adjoint first cohomology and regular semisimple detection; it does not replace separate adjoint-twist or local-condition checks.

Coefficient five remains outside that uniform conclusion. The coincidence $A_5\simeq\operatorname{PSL}_2(\mathbf F_5)$ leaves a genuine adjoint cohomology class, so the icosahedral branch must be eliminated or handled directly. With that boundary explicit, the image theory is strong enough for later Taylor--Wiles prime selection and potential-modularity constructions without concealing a small-prime exception or a local ramification hypothesis.
