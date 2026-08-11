# Local Jacquet--Langlands

## Contents

1. [The comparison to be made](#1-the-comparison-to-be-made)
   - [Two inner forms and one discrete spectrum](#11-two-inner-forms-and-one-discrete-spectrum)
   - [Standing conventions](#12-standing-conventions)
   - [The selected range](#13-the-selected-range)
   - [The theorem in advance](#14-the-theorem-in-advance)
2. [The common regular geometry](#2-the-common-regular-geometry)
   - [Characteristic polynomials](#21-characteristic-polynomials)
   - [Split and elliptic matrices](#22-split-and-elliptic-matrices)
   - [Regular elements of the division algebra](#23-regular-elements-of-the-division-algebra)
   - [Matching classes and centralizers](#24-matching-classes-and-centralizers)
   - [The separability boundary](#25-the-separability-boundary)
3. [Discriminants, measures, and orbital comparison](#3-discriminants-measures-and-orbital-comparison)
   - [The common Weyl discriminant](#31-the-common-weyl-discriminant)
   - [A compatible measure ledger](#32-a-compatible-measure-ledger)
   - [Ordinary and normalized orbital integrals](#33-ordinary-and-normalized-orbital-integrals)
   - [Geometric versus signed transfer](#34-geometric-versus-signed-transfer)
   - [From characters to traces](#35-from-characters-to-traces)
4. [Characters and the special correspondence](#4-characters-and-the-special-correspondence)
   - [Regular character functions](#41-regular-character-functions)
   - [Why induced representations vanish elliptically](#42-why-induced-representations-vanish-elliptically)
   - [The Steinberg sign](#43-the-steinberg-sign)
   - [Special twists and their invariants](#44-special-twists-and-their-invariants)
5. [Quadratic data on both inner forms](#5-quadratic-data-on-both-inner-forms)
   - [Admissible pairs](#51-admissible-pairs)
   - [Minimal pairs and norm twists](#52-minimal-pairs-and-norm-twists)
   - [Direct and induction normalizations](#53-direct-and-induction-normalizations)
   - [The two compact-mod-center types](#54-the-two-compact-mod-center-types)
   - [Equivalence and recovery of labels](#55-equivalence-and-recovery-of-labels)
6. [Depth-zero character matching](#6-depth-zero-character-matching)
   - [The finite elliptic calculation](#61-the-finite-elliptic-calculation)
   - [Lifting the finite identity](#62-lifting-the-finite-identity)
   - [All regular classes in the packet](#63-all-regular-classes-in-the-packet)
   - [Why regularity cannot be omitted](#64-why-regularity-cannot-be-omitted)
7. [Positive-depth tame matching](#7-positive-depth-tame-matching)
   - [The common last-layer character](#71-the-common-last-layer-character)
   - [Heisenberg enlargement](#72-heisenberg-enlargement)
   - [The opposite Fourier-index lemma](#73-the-opposite-fourier-index-lemma)
   - [The type-regular range](#74-the-type-regular-range)
   - [Near-central correction shells](#75-near-central-correction-shells)
   - [Nonminimal pairs](#76-nonminimal-pairs)
8. [The selected correspondence and uniqueness](#8-the-selected-correspondence-and-uniqueness)
   - [The selected sets](#81-the-selected-sets)
   - [Construction](#82-construction)
   - [Injectivity and surjectivity](#83-injectivity-and-surjectivity)
   - [Uniqueness from elliptic characters](#84-uniqueness-from-elliptic-characters)
9. [Structural compatibilities](#9-structural-compatibilities)
   - [Central characters](#91-central-characters)
   - [Twists](#92-twists)
   - [Contragredients](#93-contragredients)
   - [Why numerical invariants are not enough](#94-why-numerical-invariants-are-not-enough)
10. [Conductors and local factors](#10-conductors-and-local-factors)
    - [Conductor conventions](#101-conductor-conventions)
    - [Special conductor calculation](#102-special-conductor-calculation)
    - [Dihedral conductor calculation](#103-dihedral-conductor-calculation)
    - [The common Weil--Deligne datum](#104-the-common-weil--deligne-datum)
    - [Euler and epsilon factors](#105-euler-and-epsilon-factors)
    - [Changes of additive character and measure](#106-changes-of-additive-character-and-measure)
11. [Types, newvectors, and level](#11-types-newvectors-and-level)
    - [What transfer can compare](#111-what-transfer-can-compare)
    - [Special type lines](#112-special-type-lines)
    - [Dihedral multiplicity lines](#113-dihedral-multiplicity-lines)
    - [Oldvectors and the anisotropic jump](#114-oldvectors-and-the-anisotropic-jump)
12. [Integral type lattices](#12-integral-type-lattices)
    - [Coefficient rings and integrality](#121-coefficient-rings-and-integrality)
    - [Special lattices](#122-special-lattices)
    - [Dihedral type lattices](#123-dihedral-type-lattices)
    - [Saturated multiplicity lines](#124-saturated-multiplicity-lines)
    - [Perfect pairings](#125-perfect-pairings)
    - [Reduction and the nonbanal boundary](#126-reduction-and-the-nonbanal-boundary)
13. [Worked packets and boundary tests](#13-worked-packets-and-boundary-tests)
    - [An unramified special twist](#131-an-unramified-special-twist)
    - [A ramified special twist](#132-a-ramified-special-twist)
    - [An unramified depth-zero pair](#133-an-unramified-depth-zero-pair)
    - [A tame ramified pair](#134-a-tame-ramified-pair)
    - [A cancelling twist](#135-a-cancelling-twist)
    - [The dyadic and primitive-wild boundary](#136-the-dyadic-and-primitive-wild-boundary)
14. [The trace-formula and integral-level interface](#14-the-trace-formula-and-integral-level-interface)
    - [The pointwise local transfer](#141-the-pointwise-local-transfer)
    - [The orbital trace identity](#142-the-orbital-trace-identity)
    - [The integral level-change datum](#143-the-integral-level-change-datum)
    - [A normalization audit](#144-a-normalization-audit)
15. [The complete selected theorem](#15-the-complete-selected-theorem)
    - [The comparison table](#151-the-comparison-table)
    - [Main theorem](#152-main-theorem)
    - [Exact scope](#153-exact-scope)
    - [Conclusion](#154-conclusion)

## 1. The comparison to be made

### 1.1 Two inner forms and one discrete spectrum

Let $F$ be a nonarchimedean local field of characteristic zero and let $D$ be the quaternion division algebra over $F$. We compare

$$
G=\operatorname{GL}_2(F)
\qquad\text{and}\qquad
G'=D^\times.
$$

After extending scalars to a separable closure, the two degree-two central simple algebras become isomorphic. Over $F$ their groups look very different. The split group has a Borel subgroup, principal series, infinite-dimensional supercuspidals, and many split regular classes. The quotient $D^\times/F^\times$ is compact, every irreducible smooth representation of $D^\times$ is finite-dimensional, and no split torus occurs in $D^\times$.

Local Jacquet--Langlands says that the part of the split representation theory which is intrinsically elliptic is nevertheless visible on the division group. It cannot identify representation spaces: a one-dimensional norm character corresponds to an infinite-dimensional Steinberg twist. It cannot identify fixed spaces under superficially similar compact opens: normal principal-unit groups on $D^\times$ have an all-or-nothing fixed-space behavior which has no analogue in the split oldform tower. The common invariant is instead the trace character on regular elliptic conjugacy classes.

In degree two, that common geometry is concrete. A separable irreducible quadratic polynomial determines one regular elliptic conjugacy class in $G$ and one in $G'$. The two centralizers are copies of the same quadratic torus, and their Weyl discriminants agree. The representation-theoretic problem is to prove that the selected characters on those classes differ by exactly one sign.

This volume carries out that problem for the range required later: Steinberg twists and the supercuspidals constructed from tame admissible quadratic pairs. The prior split theory constructs the supercuspidals, proves their exact compact-induction character algorithm, conductors, local factors, and newvectors. The prior division theory constructs the quaternionic types, proves its finite induced-character algorithm, conductors, and integral lattices. The Weil--Deligne theory supplies conductor and local-constant formulas for the parameters. The work here is the genuinely two-sided comparison: every regular class contribution is paired, including the extra terms near the center; the sign is fixed; and all conductor, analytic-factor, and integral-type normalizations are shown to agree. No later local-transfer theorem is used as an input.

### 1.2 Standing conventions

Write

$$
\mathcal O=\mathcal O_F,
\qquad \mathfrak p=(\varpi),
\qquad k=\mathcal O/\mathfrak p,
\qquad |k|=q,
\qquad |\varpi|=q^{-1}.
$$

Reduced trace and reduced norm on $D$ are denoted by $\operatorname{Trd}$ and $\operatorname{Nrd}$. The center of each group is identified with

$$
Z=F^\times.
$$

On scalar elements,

$$
\det(zI_2)=z^2=\operatorname{Nrd}(z).
\tag{1.1}
$$

Complex coefficients are used for analytic characters. Integral statements use a finite extension $L/\mathbf Q_\ell$ with valuation ring $R$, maximal ideal $\mathfrak m_R$, and residue field $\kappa$, where $\ell$ is different from the residue characteristic $p$ of $F$. Every occurrence of integrality will include the necessary unit-valued hypothesis.

For local factors, $\Phi$ is geometric Frobenius and reciprocity is normalized by

$$
\operatorname{rec}_F(\varpi)=\Phi,
\qquad |\Phi|=q^{-1}.
\tag{1.2}
$$

The additive conductor convention is that $n(\psi)=0$ when $\psi$ is trivial on $\mathcal O$ but not on $\varpi^{-1}\mathcal O$. Unless a measure is displayed, the additive Haar measure in an epsilon factor is self-dual for the displayed additive character.

The Steinberg representation is normalized so that its Weil--Deligne datum is the centered block $\operatorname{Sp}_2(1)$. Thus a twist $\operatorname{St}\otimes(\mu\circ\det)$ has datum $\operatorname{Sp}_2(\mu)$ and Euler factor $L(s+1/2,\mu)$.

### 1.3 The selected range

There are two families.

The special family is

$$
\operatorname{St}\otimes(\mu\circ\det)
\quad\longleftrightarrow\quad
\mu\circ\operatorname{Nrd},
\tag{1.3}
$$

for an arbitrary smooth character $\mu:F^\times\to\mathbf C^\times$.

The dihedral family begins with a separable quadratic extension $E/F$ and a smooth character $\theta:E^\times\to\mathbf C^\times$. Let $\sigma$ be the nontrivial $F$-automorphism of $E$. The pair is required to be tame admissible: $\theta\ne\theta^\sigma$, and if $\theta/\theta^\sigma$ is trivial on $U_E^1$, then $E/F$ is unramified. This includes every quadratic extension when $p\ne2$ and includes the unramified quadratic extension in every residue characteristic. Characteristic zero is retained because the division-side type construction on which this comparison rests was proved under that hypothesis; residue characteristic two is still allowed in the stated unramified range.

The theorem does not include a ramified dyadic positive-depth construction or a primitive wild packet. Those representations require strata and extension data not present in a tame quadratic character. It would be mathematically false to infer them from the calculations below. Nor does the theorem include principal series or one-dimensional representations of $G$: they are not essentially square-integrable and have no irreducible division-side partners.

The word selected will always mean precisely the union of (1.3) and the tame admissible-pair family. No argument below silently enlarges it.

### 1.4 The theorem in advance

For every selected representation $\pi$ of $G$ there is a unique selected representation $\pi'$ of $G'$ such that

$$
\boxed{
\Theta_\pi(g)=-\Theta_{\pi'}(d)
}
\tag{1.4}
$$

whenever $g$ and $d$ have the same separable irreducible characteristic polynomial. The correspondence is (1.3) on special representations and uses the same admissible pair on the two sides in the dihedral case.

The minus sign is the degree-two inner-form sign. It is not inserted by changing a Haar measure and cannot be omitted. One may place it either in the spectral character identity or in a signed convention for transferred test functions, but it must occur exactly once.

The theorem preserves central characters, twists, contragredients, conductor exponents, the selected two-dimensional Weil--Deligne datum, and therefore local $L$- and epsilon factors. Over a suitable coefficient ring it also identifies the labels of the distinguished split newvector/type line and the division type multiplicity line, with finite free integral lattices and perfect dual pairings. These additional statements are part of the transfer package, not consequences of a vague similarity between the two groups.

## 2. The common regular geometry

### 2.1 Characteristic polynomials

Before comparing characters one must identify the conjugacy classes on which they are to be evaluated. Degree two supplies a common coordinate system. For $g\in G$, put

$$
P_g(X)=X^2-\operatorname{tr}(g)X+\det(g).
$$

For $d\in G'$, put

$$
P_d(X)=X^2-\operatorname{Trd}(d)X+\operatorname{Nrd}(d).
$$

In either algebra, a semisimple element is regular when its centralizer has dimension two. On the locus relevant here this is equivalent to $P_x$ being separable of degree two. The algebra $F[x]$ is then a quadratic étale algebra.

The characteristic polynomial carries exactly the right amount of information in degree two. It is conjugacy invariant, records both the central character scaling and twisting norm, and determines a regular rational conjugacy class. Trace alone would be insufficient: many nonconjugate elements share a trace. Determinant alone would be still weaker and would not remember the quadratic torus.

### 2.2 Split and elliptic matrices

Let $g\in G$ be regular semisimple. Then

$$
F[g]\simeq F\times F
\quad\text{or}\quad
F[g]\simeq E
$$

for a separable quadratic field $E/F$. In the first case $g$ is split regular and is conjugate to a diagonal matrix with distinct diagonal entries. In the second it is elliptic regular. The terminology is explained by the centralizer:

$$
C_G(g)=F[g]^\times.
$$

If $F[g]=E$, then $E^\times/F^\times$ is compact. If $F[g]=F\times F$, the quotient of the centralizer by the center is isomorphic to $F^\times$ and is not compact.

An irreducible separable polynomial

$$
P(X)=X^2-tX+n
$$

produces the companion matrix

$$
g_P=
\begin{pmatrix}
0&-n\\
1&t
\end{pmatrix}.
$$

Every matrix with polynomial $P$ is conjugate to $g_P$. Indeed, any nonzero vector is cyclic because $g$ has no $F$-eigenline; the basis $(v,gv)$ and the Cayley--Hamilton relation give the displayed companion form. Thus $P$ determines one elliptic conjugacy class, not merely a stable class.

### 2.3 Regular elements of the division algebra

Let $d\in D^\times$ have separable quadratic characteristic polynomial. The algebra $F[d]$ cannot be $F\times F$, since a division algebra has no nontrivial idempotent. Hence $F[d]=E$ is a quadratic field. The centralizer dimension formula gives

$$
C_{D^\times}(d)=E^\times.
\tag{2.1}
$$

If $d_1$ and $d_2$ have the same separable characteristic polynomial, the assignment $d_1\mapsto d_2$ identifies $F[d_1]$ with $F[d_2]$. Conjugacy of embeddings of a separable maximal subfield in a central simple algebra supplies $x\in D^\times$ with $xd_1x^{-1}=d_2$. Conversely conjugate elements plainly have the same polynomial. Thus a separable quadratic polynomial determines one division-side regular class.

Every separable quadratic extension $E/F$ embeds in $D$. One way to see this is through the local invariant: the class of $D$ has invariant $1/2$, and restriction to a quadratic extension multiplies it by two, so $D\otimes_F E$ is split. The degree-two embedding criterion then gives an $F$-embedding $E\hookrightarrow D$.

### 2.4 Matching classes and centralizers

We say that regular elements $g\in G$ and $d\in G'$ match, and write $g\leftrightarrow d$, if

$$
P_g=P_d.
\tag{2.2}
$$

Equivalently,

$$
\operatorname{tr}(g)=\operatorname{Trd}(d),
\qquad
\det(g)=\operatorname{Nrd}(d).
\tag{2.3}
$$

The preceding arguments prove a bijection

$$
\left\{
\begin{array}{c}
\text{regular elliptic conjugacy}\\
\text{classes in }G
\end{array}
\right\}
\longleftrightarrow
\left\{
\begin{array}{c}
\text{separable regular conjugacy}\\
\text{classes in }G'
\end{array}
\right\}.
\tag{2.4}
$$

For a matching pair the two centralizers are copies of the same abstract torus $E^\times$. The identification sends $g$ and $d$ to the class of $X$ in $F[X]/(P_g)$. There is no choice of a preferred root: the nontrivial automorphism $\sigma$ exchanges the two roots and is implemented by a normalizer element on each side.

Matching is compatible with the operations needed later:

$$
zg\leftrightarrow zd,
\qquad
g^{-1}\leftrightarrow d^{-1},
\qquad
\det g=\operatorname{Nrd}d.
\tag{2.5}
$$

The last equality is the reason determinant twists and reduced-norm twists correspond.

### 2.5 The separability boundary

Because $F$ has characteristic zero, every quadratic field extension is separable. The remaining boundary is the repeated-root locus. A scalar matrix and a nontrivial Jordan block can have the same polynomial $(X-z)^2$ on the split side but are not conjugate, while the division algebra contains no nontrivial unipotent element with that polynomial. Thus characteristic polynomials parametrize corresponding classes only when the polynomial is irreducible and separable.

On $D^\times$, every noncentral element has irreducible quadratic minimal polynomial and is regular. Hence the common locus is $D^\times\setminus F^\times$ on the division side and the regular elliptic locus on the split side. It is open and dense. Distribution characters are determined by their regular restrictions, so excluding the repeated-root locus creates no ambiguity. It prevents a false extension of orbital formulas to the singular center, where the conjugation Jacobian vanishes and the two corresponding representations usually have different dimensions.

## 3. Discriminants, measures, and orbital comparison

### 3.1 The common Weyl discriminant

Matching conjugacy classes is not enough for trace comparison; one must also compare the Jacobian of conjugation. For a regular element $x$ in either degree-two algebra define

$$
\Delta(x)=\operatorname{trd}(x)^2-4\operatorname{nrd}(x)
$$

and

$$
D(x)=\left|\frac{\Delta(x)}{\operatorname{nrd}(x)}\right|_F.
\tag{3.1}
$$

Here ordinary trace and determinant are used in $M_2(F)$, and reduced trace and norm are used in $D$.

If the two roots are $\alpha$ and $\beta$, conjugation on the two root directions has eigenvalues $\alpha/\beta$ and $\beta/\alpha$. Therefore

$$
\left|\det(1-\operatorname{Ad}(x))\right|
=|(1-\alpha/\beta)(1-\beta/\alpha)|
=\left|\frac{(\alpha-\beta)^2}{\alpha\beta}\right|,
$$

which is (3.1). Matching preserves trace and norm, so

$$
g\leftrightarrow d
\quad\Longrightarrow\quad
D(g)=D(d).
\tag{3.2}
$$

This is the exact equality needed to compare either ordinary orbital integrals on both sides or normalized orbital integrals on both sides. Mixing the two conventions would insert an unwanted factor $D(x)^{1/2}$.

### 3.2 A compatible measure ledger

Haar measures do not change pointwise matrix traces, but they do change convolution operators and orbital integrals. We fix them in an order that leaves no conflicting quotient choices:

$$
\operatorname{vol}(\operatorname{GL}_2(\mathcal O),dg)=1,
\qquad
\operatorname{vol}(\mathcal O_D^\times,dd)=1,
\tag{3.3}
$$

$$
\operatorname{vol}(\mathcal O^\times,dz)=1,
\qquad
\operatorname{vol}(\mathcal O_E^\times,de)=1
\tag{3.4}
$$

for every separable quadratic $E/F$. When the same $E^\times$ is a centralizer in both groups, the same measure $de$ is used. Quotient measures are then defined by Weil's formula. For example,

$$
\int_G f(x)\,dx
=\int_{E^\times\backslash G}
\int_{E^\times}f(ex)\,de\,d\dot x.
\tag{3.5}
$$

One must not also decree independently that every quotient in sight have volume one. The quotient volumes have already been determined by (3.3)--(3.5). Compatible torus measure is especially important: an independent rescaling on one side would leave a torus-dependent scalar in the trace comparison.

### 3.3 Ordinary and normalized orbital integrals

Let $x$ be regular in a group $H$ and let $T=C_H(x)\simeq E^\times$. For a compactly supported locally constant function $f$ define

$$
O_x(f)=\int_{T\backslash H}f(y^{-1}xy)\,d\dot y.
\tag{3.6}
$$

If a central character is fixed, the same definition is made on the common central quotient with the inverse central transformation law on $f$. The normalized orbital integral is

$$
I_x(f)=D(x)^{1/2}O_x(f).
\tag{3.7}
$$

Because of (3.2), equality of ordinary orbital integrals for matching elements is equivalent to equality of normalized orbital integrals. We call $f$ on $G$ and $f'$ on $G'$ geometrically matching when

$$
O_g(f)=O_d(f')
\tag{3.8}
$$

for every matching regular pair and when the split regular orbital integrals of $f$ vanish in the elliptic transfer situation. For a general split function only its elliptic orbital integrals can be remembered by $f'$; split classes have no division-side partners.

The present theorem identifies the spectral response to functions satisfying (3.8). It does not assert an unrestricted fundamental lemma for every pair of compact opens. That later problem requires a separate analysis of orbital integrals. Here the local packet character identity gives the exact spectral sign once geometrically matching functions have been chosen.

### 3.4 Geometric versus signed transfer

There are two consistent placements of the sign. Under geometric transfer, (3.8) holds and the selected traces differ by $-1$. Under signed spectral transfer one defines matching by

$$
O_g(f)=-O_d(f')
$$

and the selected traces agree. We use geometric transfer throughout. Thus the pointwise relation is always

$$
\Theta_G=-\Theta_{G'}.
$$

Putting a minus sign in both the orbital condition and the character condition would count the degree-two sign twice. Putting it in neither would contradict the Steinberg calculation in Chapter 4.

### 3.5 From characters to traces

Suppose $f$ and $f'$ are geometrically matching and supported on the regular elliptic region modulo the center. Weyl integration writes the trace of a representation as a sum over quadratic tori. For one $E/F$, the contribution has the form

$$
\frac12\int_{E^\times_{\mathrm{reg}}}
\Theta_\pi(t)D(t)O_t(f)\,dt.
\tag{3.9}
$$

The factor $1/2$ is the order of the rational Weyl group generated by $\sigma$. The same factor, torus measure, and discriminant occur for $G'$. Consequently, if

$$
\Theta_\pi(t)=-\Theta_{\pi'}(t)
$$

on matching classes, substitution into (3.9) gives

$$
\operatorname{tr}\pi(f)=-\operatorname{tr}\pi'(f').
\tag{3.10}
$$

The converse requires an existence theorem for matching functions with prescribed small orbital support; that is a separate orbital-integral problem and is not assumed here. What we shall prove is the stronger pointwise character identity directly. It implies (3.10) for every pair of functions already known to satisfy (3.8), which is exactly the interface needed by a later test-function transfer theorem.

## 4. Characters and the special correspondence

### 4.1 Regular character functions

For an infinite-dimensional smooth representation, $\operatorname{tr}\pi(g)$ is not defined as an operator trace. The trace distribution

$$
f\longmapsto\operatorname{tr}\pi(f)
$$

is instead represented by a locally integrable conjugation-invariant function. On the regular semisimple set this Harish--Chandra character $\Theta_\pi$ is locally constant. On $D^\times$, the selected representations are finite-dimensional, so their ordinary matrix traces give the same character function directly.

The regular character is exactly what orbital transfer sees. Its local constancy allows a pointwise calculation on regular torus charts, while local integrability permits Weyl integration near the singular boundary. We will never substitute a scalar or inseparable element into a formula proved only on the regular set.

Characters behave predictably under the operations used later:

$$
\Theta_{\pi\otimes(\chi\circ\det)}(g)
=\chi(\det g)\Theta_\pi(g),
$$

$$
\Theta_{\pi^\vee}(g)=\Theta_\pi(g^{-1}),
\tag{4.1}
$$

and similarly with $\operatorname{Nrd}$ on $D^\times$. These are algebraic contragredient formulas; no complex conjugation is involved.

### 4.2 Why induced representations vanish elliptically

The vanishing of principal-series characters on elliptic classes explains why only the discrete spectrum can transfer. Let

$$
I(\chi_1,\chi_2)
$$

be normalized induction from the upper Borel. The induced model is built from functions on $G/B\simeq\mathbf P^1(F)$. At a finite compact-open level, the trace of a regular element is a weighted count of fixed cosets. A fixed point is precisely an $F$-rational eigenline.

More precisely, the induced-character formula is a sum over $B\backslash G$ fixed by $g$, with one term for each conjugate of $g$ lying in $B$. Such a conjugate exists exactly when $g$ preserves an $F$-line. The formula is locally finite on the regular set and represents the distribution character, so it is legitimate even though the full induced space is infinite dimensional. An elliptic regular matrix has no $F$-eigenline. Hence

$$
\Theta_{I(\chi_1,\chi_2)}(g)=0
\qquad(g\text{ elliptic regular}).
\tag{4.2}
$$

This proof exposes both the geometric and spectral boundary. A split regular matrix has two eigenlines and generally gives two nonzero terms. No class in $D^\times$ can record them. The elliptic quotient of the split character theory kills principal series, leaving Steinberg twists and supercuspidals.

### 4.3 The Steinberg sign

The special correspondence is the normalization anchor for every later sign. The exceptional normalized principal series fits into

$$
0\longrightarrow \mu\circ\det
\longrightarrow I(\mu|\cdot|^{-1/2},\mu|\cdot|^{1/2})
\longrightarrow \operatorname{St}\otimes(\mu\circ\det)
\longrightarrow0.
\tag{4.3}
$$

Trace distributions are additive in short exact sequences. At an elliptic regular $g$, the middle term vanishes by (4.2), while the one-dimensional subrepresentation contributes $\mu(\det g)$. Therefore

$$
\Theta_{\operatorname{St}\otimes\mu}(g)
=-\mu(\det g).
\tag{4.4}
$$

The division-side norm character has ordinary trace

$$
\Theta_{\mu\circ\operatorname{Nrd}}(d)
=\mu(\operatorname{Nrd}d).
\tag{4.5}
$$

For $g\leftrightarrow d$, equations (2.3), (4.4), and (4.5) prove

$$
\Theta_{\operatorname{St}\otimes\mu}(g)
=-\Theta_{\mu\circ\operatorname{Nrd}}(d).
\tag{4.6}
$$

The sign is therefore a theorem forced by the exceptional principal series. It is not the trace of a negative representation and does not arise from the scaling of Haar measure.

### 4.4 Special twists and their invariants

On a scalar $z$, both selected representations act by

$$
\mu(z^2)=\mu(z)^2.
$$

Thus their central character is $\mu^2$. Twisting by another character $\chi$ replaces $\mu$ by $\mu\chi$ on both sides:

$$
(\operatorname{St}\otimes\mu)\otimes(\chi\circ\det)
=\operatorname{St}\otimes(\mu\chi),
$$

$$
(\mu\circ\operatorname{Nrd})\otimes(\chi\circ\operatorname{Nrd})
=(\mu\chi)\circ\operatorname{Nrd}.
$$

The common conductor is

$$
a_{\mathrm{sp}}(\mu)=
\begin{cases}
1,&a_F(\mu)=0,\\
2a_F(\mu),&a_F(\mu)>0.
\end{cases}
\tag{4.7}
$$

The exceptional value one for an unramified twist records monodromy: the split representation has an Iwahori-fixed line but no hyperspecial-fixed line. On the division side the transfer-facing convention assigns conductor one to the unramified norm character, even though it is already trivial on $\mathcal O_D^\times$. This is the convention established for the selected division packets and is the one used throughout this book.

The common parameter is $\operatorname{Sp}_2(\mu)$. In particular,

$$
L(s)=L(s+1/2,\mu),
$$

and the epsilon factor is the one calculated from that same centered special block. These claims will be proved uniformly with the dihedral factor statements in Chapter 10.

## 5. Quadratic data on both inner forms

### 5.1 Admissible pairs

Let $E/F$ be separable quadratic and let $\sigma$ be its nontrivial automorphism. A smooth character $\theta:E^\times\to\mathbf C^\times$ is regular if

$$
\theta\ne\theta^\sigma.
\tag{5.1}
$$

Equivalently, $\theta$ does not factor through $N_{E/F}$. Indeed, a norm character is visibly invariant. Conversely, if $\theta$ is invariant, its restriction to the norm-one subgroup is trivial because every norm-one element has the form $x/\sigma(x)$; it therefore descends through the norm image and extends to a character of $F^\times$.

Regularity is necessary but not sufficient at positive depth. The pair $(E,\theta)$ is admissible when it is regular and, if $\theta/\theta^\sigma$ is trivial on $U_E^1$, the extension $E/F$ is unramified. In a ramified extension, asymmetry visible only on valuation or residue data leaves extra normalizer intertwining and does not produce the desired irreducible tame type.

This definition includes the regular unramified depth-zero pairs: there the two conjugate residue characters are distinct. It also includes tame positive-depth pairs. In residue characteristic two it includes unramified quadratic pairs but not ramified quadratic positive-depth pairs.

### 5.2 Minimal pairs and norm twists

A positive-depth pair is minimal if no character $\chi$ of $F^\times$ lowers the conductor of

$$
\theta(\chi\circ N_{E/F})^{-1}.
$$

Every tame admissible pair is a norm twist of a minimal one. To prove this, examine the last nontrivial unit layer of $\theta$. On that additive quotient the character has the form

$$
1+x\longmapsto\psi_E(\beta x).
\tag{5.2}
$$

If its last layer is Galois invariant, tame trace surjectivity shows that the corresponding additive functional comes from $F$. A character of $F^\times$ then cancels that layer after norm pullback. The conductor strictly decreases, so repeated cancellation terminates. When the last layer is noninvariant, no norm twist removes it, and the pair is minimal.

The reduction to minimal pairs is essential for the proof of positive-depth character matching. Minimality makes the leading coefficient $\beta$ noncentral at the decisive precision, so its centralizer is exactly $E$. Nonminimal pairs will be recovered afterward by the exact twisting law.

### 5.3 Direct and induction normalizations

There are two nearby labels which must not be confused. In direct normalization, the type restricts to $\theta$ on $E^\times$ and has central character $\theta|_{F^\times}$. The two-dimensional induced Weil representation, however, has determinant

$$
\det\operatorname{Ind}_{W_E}^{W_F}\theta
=\theta|_{F^\times}\omega_{E/F},
\tag{5.3}
$$

where $\omega_{E/F}$ is the quadratic character with kernel $N_{E/F}(E^\times)$.

The character-dependent tame rectifier $\Delta_{E/F,\theta}$ reconciles these descriptions. Put

$$
\theta^\natural=\theta\Delta_{E/F,\theta},
\qquad
\Delta_{E/F,\theta}|_{F^\times}=\omega_{E/F}.
\tag{5.4}
$$

It is unramified for an unramified quadratic extension. In the tamely ramified case it can depend on $\theta$: its normalized finite Gauss sum fixes the extension phase, and suppressing that dependence can reverse a positive-depth trace. Its conductor is at most one, whereas ramified admissibility forces $a_E(\theta)\ge2$, so it does not change the conductor in the selected range. The identities proved in the split and division type theories are

$$
\Delta_{E/F,\theta^\sigma}=\Delta_{E/F,\theta}^\sigma,
\qquad
\Delta_{E/F,\theta(\chi\circ N_{E/F})}=\Delta_{E/F,\theta},
\qquad
\Delta_{E/F,\theta^{-1}}=\Delta_{E/F,\theta}^{-1}.
\tag{5.4a}
$$

They are the exact inputs needed for equivalence, twisting, and contragredience. The split and division types used below are the induction-normalized types attached to $\theta^\natural$, while the common Weil parameter is labelled by $\theta$.

Consequently both representation central characters are

$$
\omega_{\theta}=\theta|_{F^\times}\omega_{E/F}.
\tag{5.5}
$$

The rectifier is not optional decoration. Without it, the central character, the determinant of the parameter, and the finite Fourier phase would fail to agree simultaneously. Nor may it be replaced in the ramified case by a character depending only on $E/F$.

### 5.4 The two compact-mod-center types

The split construction gives an irreducible supercuspidal

$$
\pi(E,\theta)
=\operatorname{c\mbox{-}Ind}_{J}^{G}\Lambda_{\theta^\natural},
\qquad J=E^\times J^1.
\tag{5.6}
$$

The division construction gives

$$
\pi'(E,\theta)
=\operatorname{Ind}_{J'}^{G'}\Lambda'_{\theta^\natural},
\qquad J'=E^\times J'^1.
\tag{5.7}
$$

The quotient $J'\backslash G'$ is finite modulo the common central action, so (5.7) is finite-index induction. At depth zero, $E/F$ is unramified, $J'^1=U_D^1$, and the division type is a character induced from an index-two subgroup. At positive depth, $J^1$ and $J'^1$ contain the simple characters determined by the same last-layer datum (5.2), enlarged through finite Heisenberg representations.

Induction from the bare torus would be inadequate. The torus is not open in the split group, and at positive depth it does not remember the noncommutative commutator quotient. The subgroups $J^1$ and $J'^1$ record precisely the congruence information which eliminates unwanted intertwiners.

### 5.5 Equivalence and recovery of labels

Pairs $(E,\theta)$ and $(E',\theta')$ are equivalent if an $F$-isomorphism $E\to E'$ carries one character to the other. For fixed $E$, the equivalence orbit is

$$
\{\theta,\theta^\sigma\}.
\tag{5.8}
$$

Conjugacy of quadratic embeddings shows that equivalent pairs give isomorphic representations on each side. Conversely, intertwining of the types recovers the pair. At depth zero the restriction to the finite nonsplit torus recovers the regular Frobenius orbit of the residue character. At positive depth the last nonconstant layer recovers the conjugacy orbit of $\beta$; its centralizer recovers $E$, and the torus restriction then recovers $\theta$ up to $\sigma$.

Thus the maps

$$
(E,\theta)\longmapsto\pi(E,\theta),
\qquad
(E,\theta)\longmapsto\pi'(E,\theta)
\tag{5.9}
$$

are injective on selected equivalence classes. This label injectivity will make the final bijection immediate once character matching has been proved.

## 6. Depth-zero character matching

### 6.1 The finite elliptic calculation

Assume $E/F$ is unramified and $a_E(\theta)=1$. Let $k_2/k$ be the residue extension and let $\bar\theta:k_2^\times\to\mathbf C^\times$ be the resulting regular character. Regularity says

$$
\bar\theta^q\ne\bar\theta.
$$

The division type is induced from the index-two subgroup $E^\times U_D^1$. For $x\in k_2^\times\setminus k^\times$, its trace is the elementary induced-character sum

$$
\bar\theta(x)+\bar\theta(x^q).
\tag{6.1}
$$

The split depth-zero type contains the finite cuspidal representation of $\operatorname{GL}_2(k)$ attached to the same orbit. Its value at the elliptic class with eigenvalues $x,x^q$ is

$$
-\bar\theta(x)-\bar\theta(x^q).
\tag{6.2}
$$

Formula (6.2) is a proved input from the finite cuspidal construction on the split side, not a guessed Deligne--Lusztig sign. That construction computes the full four-row character table: scalar, nontrivial unipotent, split regular, and elliptic regular. In its finite Fourier proof, all nonstationary translations cancel by additive-character orthogonality; the two stationary torus embeddings contribute $\bar\theta(x)$ and $\bar\theta(x^q)$, and passage to the cuspidal block contributes one alternating sign. Formula (6.1), by contrast, is the ordinary trace of an index-two induction and has a plus sign. Thus the already proved one-sided character formulas give the desired relative sign without importing a transfer theorem.

This finite calculation is basis independent. Replacing the embedding of $k_2$ conjugates the multiplication operator, while replacing $x$ by $x^q$ exchanges the two displayed summands.

### 6.2 Lifting the finite identity

Let $g\leftrightarrow d$ be a matching pair whose classes have depth-zero regular reduction. After multiplying by a common central scalar, both elements lie in their maximal compact groups and reduce to the same $x\in k_2^\times\setminus k^\times$. Inflation of the finite types and compact induction give

$$
\Theta_{\pi(E,\theta)}(g)
=-\bigl(\theta^\natural(e)+(\theta^\natural)^\sigma(e)\bigr),
$$

$$
\Theta_{\pi'(E,\theta)}(d)
=\theta^\natural(e)+(\theta^\natural)^\sigma(e),
\tag{6.3}
$$

where $e$ is the common torus coordinate. The rectifier is trivial on the residue units used in (6.1), but it must be displayed in (6.3) when valuation factors are present. The central scalar contributes the same factor on both sides because of (5.5). Thus the finite identity lifts without an additional sign or measure scalar.

### 6.3 All regular classes in the packet

The preceding calculation begins on a type-regular unit set, but the packet identity is required on every matching regular class. Central scaling makes a regular elliptic element integral, but it need not give regular elliptic reduction: elements arbitrarily close to a scalar have scalar reduction. The missing annuli require an argument.

Use the exact compact-induction formula on the split side. A regular elliptic element fixes a finite subtree in the lattice tree. Filter that subtree inward from its outer boundary. The one-sided depth-zero character table shows what happens when one outer shell is removed. At a nonterminal vertex with scalar reduction $z$, the scalar row contributes $(q-1)\bar\theta(z)$. The $q-1$ transverse directions have nontrivial unipotent reduction, and the unipotent row contributes $-\bar\theta(z)$ in each direction. Their total is therefore the negative scalar contribution. Removing the shell changes neither the total split trace nor its proposed negative division trace.

The fixed subtree is finite: an unbounded fixed subtree would contain a ray, whose end would be an $F$-rational eigenline, contradicting ellipticity. Repeating the cancellation reaches a terminal vertex or terminal edge. The two terminal orientations are the two valuation configurations in the index-two division model. At the terminal piece the reduction is regular elliptic, so (6.1)--(6.3) apply. The telescoped split trace is therefore the negative of the complete division trace. Hence

$$
\Theta_{\pi(E,\theta)}(g)
=-\Theta_{\pi'(E,\theta)}(d)
\tag{6.4}
$$

for every matching regular pair in the depth-zero packet, including the scalar-reduction annuli. This proof is why local constancy alone is not enough: its neighborhoods shrink toward the singular center, whereas the finite shell cancellation controls every intervening annulus.

### 6.4 Why regularity cannot be omitted

If $\bar\theta=\bar\theta^q$, the index-two division induction is reducible: the inducing character extends across the normalizer in two ways. On the split side the finite cuspidal construction degenerates into the principal-series block. The numerical expression (6.1) still exists, but it is not the character of the selected irreducible packet.

At a central element, the division trace is

$$
\dim\pi'(E,\theta)\,\omega_\theta(z),
$$

not the regular two-term formula with two distinct conjugates. Central elements are singular and representations on the two sides have different dimensions. These two failures show why the theorem must state both regularity of the pair and regularity of the class.

## 7. Positive-depth tame matching

### 7.1 The common last-layer character

Let $(E,\theta)$ be a minimal tame admissible pair of positive depth. On the last visible half of the unit filtration there is a noncentral $\beta\in E$ such that

$$
\theta(1+x)=\psi_E(\beta x),
\qquad \psi_E=\psi\circ\operatorname{Tr}_{E/F}.
\tag{7.1}
$$

Embedding $E$ into $M_2(F)$ and $D$ gives simple characters

$$
1+X\longmapsto\psi(\operatorname{tr}(\beta X)),
\qquad
1+Y\longmapsto\psi(\operatorname{Trd}(\beta Y)).
\tag{7.2}
$$

Their restrictions to the common field are the same character (7.1). Minimality implies that the leading class of $\beta$ is noncentral. Since a noncentral element of a quaternion algebra has a quadratic centralizer, the centralizer of this leading datum is $E$. This is the crucial rigidity: any element intertwining the last-layer character must preserve the quadratic torus to the relevant precision.

The comparison is therefore confined to directions complementary to $E$. The torus direction is common; the complementary direction distinguishes the split cyclic algebra from the nonsplit one and is where the sign arises.

### 7.2 Heisenberg enlargement

Let $H^1\subset J^1$ and $H'^1\subset J'^1$ be the simple-character and Heisenberg groups on the two sides. On the finite quotients define alternating forms by

$$
\langle \bar x,\bar y\rangle_\beta
=\vartheta_\beta([x,y]).
\tag{7.3}
$$

After quotienting by the torus radical these forms are nondegenerate. Indeed, an element in the radical commutes with $\beta$ on the last visible layer. Centralizer rigidity places it in the field direction, which has already been absorbed into $H^1$.

Choose a maximal isotropic subgroup $L/H^1$. The simple character extends to $L$, and inducing that extension to $J^1$ gives the unique irreducible Heisenberg representation containing it. Mackey's criterion proves irreducibility: an element intertwines the inducing character exactly when its class lies in the orthogonal complement of $L/H^1$, which equals $L/H^1$. The dimension is

$$
[J^1:H^1]^{1/2}.
$$

The same construction applies on the division side. Extending the Heisenberg representation by the induction-normalized torus character produces $\Lambda_{\theta^\natural}$ and $\Lambda'_{\theta^\natural}$. Different polarizations give isomorphic representations, so their traces are intrinsic.

### 7.3 The opposite Fourier-index lemma

The decisive positive-depth computation is finite.

**Lemma 7.1 (opposite complementary Fourier indices).** Embed the same tame quadratic field $E$ in $A=M_2(F)$ and in $A'=D$. Let $\beta\in E$ have centralizer $E$. On the last nontrivial lattice quotient complementary to $E$, form the finite Fourier trace from

$$
(X,Y)\longmapsto
\psi\bigl(\operatorname{Tr}_{A/F}(\beta[X,Y])\bigr).
\tag{7.4}
$$

Use reduced trace when $A=D$. After quotienting by the common radical and inserting the character-dependent tame rectifier, the normalized split and division Fourier traces differ by $-1$.

**Proof.** Choose $j$ in the complement with

$$
jz=\sigma(z)j
\qquad(z\in E).
$$

Then the complementary line is $Ej$. In the split algebra one may take $j^2=c$ in the norm class which makes the cyclic algebra $(E/F,c)$ split. In $D$ the corresponding square $c'$ lies in the other class of

$$
F^\times/N_{E/F}(E^\times).
$$

On the graded quotient the commutator form is a scalar multiple of

$$
(u,v)\longmapsto u\sigma(v)-v\sigma(u).
$$

Trace-dual coordinates reduce the complementary nondegenerate quotient to a two-dimensional $k$-space. The split quadratic phase is hyperbolic, while the division phase is anisotropic. For every nontrivial additive character $\bar\psi$ of $k$, their normalized sums are

$$
q^{-1}\sum_{u,v\in k}\bar\psi(uv)=1,
\qquad
q^{-1}\sum_{z\in k_2}\bar\psi(N_{k_2/k}z)=-1.
\tag{7.4a}
$$

The first equality follows by summing over $v$: only $u=0$ survives. For the second, zero has one preimage under the norm and every $a\in k^\times$ has $q+1$ preimages, so the unnormalized sum is

$$
1+(q+1)\sum_{a\in k^\times}\bar\psi(a)
=1-(q+1)=-q.
$$

Thus changing $c$ to $c'$ changes the normalized finite Fourier index by

$$
\omega_{E/F}(c'/c)=-1.
$$

A different choice of $j$, additive coordinate, or polarization multiplies both indices by the same norm-class factor. The direct torus extensions contribute one further one-dimensional Gauss phase. By its defining normalized Gauss-sum property, $\Delta_{E/F,\theta}$ removes that phase on both sides. Thus no unrecorded root of unity remains and the quotient of the two intrinsic traces is exactly $-1$. $\square$

Tameness is used in reducing every relevant lattice quotient to this nondegenerate trace form. In a wild ramified quadratic extension the trace-dual jumps and extension operators can contain extra data; Lemma 7.1 makes no claim there.

### 7.4 The type-regular range

Suppose a regular torus element $e\in E^\times$ meets each inducing subgroup only through the two normalizer embeddings. The exact compact-induction character formulas reduce to

$$
\Theta_{\pi(E,\theta)}(g)
=\operatorname{tr}\Lambda_{\theta^\natural}(e)
+\operatorname{tr}\Lambda_{\theta^\natural}(e^\sigma),
$$

$$
\Theta_{\pi'(E,\theta)}(d)
=\operatorname{tr}\Lambda'_{\theta^\natural}(e)
+\operatorname{tr}\Lambda'_{\theta^\natural}(e^\sigma).
\tag{7.5}
$$

Each type trace is a torus value times a finite Heisenberg trace. Lemma 7.1 compares the two Heisenberg traces with sign $-1$, while the rectifier makes the torus values agree. Applying the lemma to $e$ and $e^\sigma$ separately proves

$$
\Theta_{\pi(E,\theta)}(g)
=-\Theta_{\pi'(E,\theta)}(d)
\tag{7.6}
$$

throughout the type-regular range.

This step also explains why it is wrong to compare only $\theta(e)+\theta(e^\sigma)$. At positive depth the Heisenberg traces record the noncommutative congruence quotient. Omitting them loses the Fourier phase which distinguishes the two inner forms.

### 7.5 Near-central correction shells

As a regular element approaches the center, its conjugacy class can meet an inducing subgroup through more than the two normalizer embeddings. The exact formula is

$$
\Theta_\pi(x)=
\sum_{y\in J\backslash H\atop yxy^{-1}\in J}
\operatorname{tr}\Lambda(yxy^{-1}),
\tag{7.7}
$$

with $(H,J,\Lambda)$ equal to either split or division data. A two-term formula used arbitrarily close to the center would therefore be false.

We now pair the additional terms. Let $\mathcal X_r$ and $\mathcal X'_r$ be the conjugate embeddings that agree with the fixed torus embedding through depth $r$ but not through depth $r+1$. The first discrepancy is a class in a quotient of the complement to $E$. The characteristic-polynomial equations say that its trace is zero and its norm is fixed; because the two elements match, these equations give the same affine parameter space on the split and division sides. Conjugation by the next unit quotient acts transitively on each fiber. Linearizing this action shows that its stabilizer is precisely the radical of the commutator form: a stabilizing class commutes with the leading coefficient $\beta$, hence lies in the already removed field direction.

The sum over one shell has the form

$$
|\operatorname{rad}_r|
\sum_{v\in V_r/\operatorname{rad}_r}
\psi(q_r(v)).
\tag{7.8}
$$

Nonstationary affine fibers sum to zero by additive-character orthogonality. On stationary fibers, the quotient form in (7.8) is exactly the complementary form of Lemma 7.1. At the closest-to-central shells the radical can grow, but it grows only in the common torus direction. The trace-dual $E$-lattices therefore give the same radical cardinality on both sides, while the nondegenerate quotient sums differ by $-1$. Hence the entire $r$th split shell is the negative of the division shell.

There are only finitely many shells. Smoothness makes sufficiently deep unit conjugations act trivially, and regularity stops the filtration before the scalar locus. Summing (7.8) over all $r$ extends (7.6) to every matching regular pair.

This shell argument is logically essential. Equality on the type-regular range and local constancy alone would not cross the shrinking regular annuli around the singular center.

### 7.6 Nonminimal pairs

Let an arbitrary tame admissible pair be written

$$
\theta=\theta_0(\chi\circ N_{E/F})
$$

with $\theta_0$ minimal. The type constructions satisfy

$$
\pi(E,\theta)
\simeq\pi(E,\theta_0)\otimes(\chi\circ\det),
$$

$$
\pi'(E,\theta)
\simeq\pi'(E,\theta_0)\otimes(\chi\circ\operatorname{Nrd}).
\tag{7.9}
$$

For matching elements, $\det g=\operatorname{Nrd}d$. Multiplying the minimal identity by the common scalar $\chi(\det g)$ proves the character identity for $\theta$. Together with Chapters 6 and 7, we have proved it for every selected dihedral packet.

## 8. The selected correspondence and uniqueness

### 8.1 The selected sets

Let $\mathcal D_G$ be the set of isomorphism classes of special twists

$$
\operatorname{St}\otimes(\mu\circ\det)
$$

and supercuspidals $\pi(E,\theta)$ for tame admissible pairs, modulo (5.8). Let $\mathcal D_{G'}$ contain the norm characters $\mu\circ\operatorname{Nrd}$ and the representations $\pi'(E,\theta)$ for the same pair classes.

Special labels are unique because reduced norm is surjective. Dihedral labels are unique by the recovery argument of Section 5.5. A special object and a dihedral object cannot coincide: on $G'$ the first is one-dimensional and the second contains a regular noncentral type; on $G$ the first is special and the second supercuspidal.

### 8.2 Construction

Define

$$
\operatorname{JL}_{\mathrm{sel}}
\bigl(\operatorname{St}\otimes(\mu\circ\det)\bigr)
=\mu\circ\operatorname{Nrd},
\tag{8.1}
$$

and

$$
\operatorname{JL}_{\mathrm{sel}}\bigl(\pi(E,\theta)\bigr)
=\pi'(E,\theta).
\tag{8.2}
$$

Chapter 4 proves the regular character identity for (8.1). Chapters 6 and 7 prove it for (8.2), including depth zero, positive depth, near-central correction terms, and nonminimal twists. Thus the construction satisfies

$$
\Theta_\pi(g)
=-\Theta_{\operatorname{JL}_{\mathrm{sel}}(\pi)}(d)
\tag{8.3}
$$

on every matching regular pair.

### 8.3 Injectivity and surjectivity

If two split selected representations have the same image, division-side label recovery gives the same family and the same label. Thus they are isomorphic. Conversely, every member of $\mathcal D_{G'}$ appears on the right side of either (8.1) or (8.2). Therefore

$$
\operatorname{JL}_{\mathrm{sel}}:
\mathcal D_G\xrightarrow{\sim}\mathcal D_{G'}
\tag{8.4}
$$

is a bijection.

Notice what proves surjectivity: the codomain was defined by the selected division constructions whose labels have already been classified. We do not infer that every irreducible representation of $D^\times$ is tame dihedral. Primitive wild representations lie outside both selected sets.

### 8.4 Uniqueness from elliptic characters

Suppose $\rho'\in\mathcal D_{G'}$ has the character prescribed by a fixed $\pi\in\mathcal D_G$ on every matching regular class. If $\pi$ is special, equations (4.4)--(4.5) show that $\rho'$ agrees with a reduced-norm character on the dense regular locus. Equality of finite-dimensional characters then gives the same norm character.

For a uniform proof, let $\pi'=\operatorname{JL}_{\mathrm{sel}}(\pi)$ be the companion already constructed. Then $\Theta_{\rho'}=\Theta_{\pi'}$ on $D^\times\setminus F^\times$. This set is dense: the center is a one-dimensional $F$-subspace of the four-dimensional algebra $D$ and has empty interior. Both representations are finite dimensional and smooth, so their ordinary trace functions are locally constant on all of $D^\times$. Equality on the dense regular set therefore extends to the center and to the identity; in particular, the dimensions and central characters agree.

Choose a principal-unit group acting trivially on both representations and divide by the common scalar central action. The two representations then factor through one finite central extension of a finite quotient of the compact group $D^\times/F^\times$. Its characteristic-zero group algebra is semisimple. Irreducible characters are linearly independent there, so equality of trace functions implies $\rho'\simeq\pi'$. This proves uniqueness inside the selected codomain without dividing by a Heisenberg trace that might vanish on a particular class. It does not claim that a few numerical invariants exclude an arbitrary primitive wild representation; that stronger assertion is neither needed nor established.

## 9. Structural compatibilities

### 9.1 Central characters

For special packets, both central characters equal $\mu^2$. For a dihedral pair, the rectifier calculation gives

$$
\omega_{\pi(E,\theta)}
=\omega_{\pi'(E,\theta)}
=\theta|_{F^\times}\omega_{E/F}.
\tag{9.1}
$$

There is also a character-theoretic proof. Fix a matching regular pair with nonzero character value and compare it with the pair obtained by multiplying both elements by $z\in F^\times$. The two instances of (8.3) differ by the respective central-character scalars. Dividing them proves equality. This argument depends on the orientation $zg\leftrightarrow zd$ fixed in (2.5).

### 9.2 Twists

Let $\chi:F^\times\to\mathbf C^\times$ be smooth. The constructions give

$$
\pi(E,\theta)\otimes(\chi\circ\det)
\simeq
\pi(E,\theta(\chi\circ N_{E/F})),
$$

$$
\pi'(E,\theta)\otimes(\chi\circ\operatorname{Nrd})
\simeq
\pi'(E,\theta(\chi\circ N_{E/F})).
\tag{9.2}
$$

The corresponding formula for special packets replaces $\mu$ by $\mu\chi$. Consequently

$$
\operatorname{JL}_{\mathrm{sel}}
\bigl(\pi\otimes(\chi\circ\det)\bigr)
\simeq
\operatorname{JL}_{\mathrm{sel}}(\pi)
\otimes(\chi\circ\operatorname{Nrd}).
\tag{9.3}
$$

This is also forced by (8.3), because the two twist factors agree on matching elements. On the center, each side is multiplied by $\chi(z^2)=\chi(z)^2$, as required by (1.1).

### 9.3 Contragredients

Inversion preserves matching, and character functions satisfy (4.1). Hence (8.3) gives

$$
\Theta_{\pi^\vee}(g)
=-\Theta_{\operatorname{JL}_{\mathrm{sel}}(\pi)^\vee}(d).
$$

Uniqueness proves

$$
\operatorname{JL}_{\mathrm{sel}}(\pi^\vee)
\simeq
\operatorname{JL}_{\mathrm{sel}}(\pi)^\vee.
\tag{9.4}
$$

On labels, $\mu$ is replaced by $\mu^{-1}$ and the admissible orbit is replaced by the inverse orbit $\{\theta^{-1},(\theta^\sigma)^{-1}\}$. Self-duality therefore requires equivalence of the original and inverse labels; it cannot be inferred from the central character alone.

### 9.4 Why numerical invariants are not enough

Central character and conductor do not determine a dihedral packet. Distinct regular characters of $k_2^\times$ can have the same restriction to $k^\times$ and the same conductor. Their values

$$
\bar\theta(x)+\bar\theta(x^q)
$$

on elliptic residue elements distinguish them. An unramified and a ramified quadratic pair can also acquire the same central character and total conductor after twisting while retaining nonisomorphic centralizer fields.

Local Euler factors are still coarser: every selected irreducible dihedral parameter has Euler factor one. Epsilon factors retain a Gauss phase, but conductor plus epsilon factor is not a complete character table. The full regular elliptic character identity is therefore the defining statement; the structural compatibilities are checks and consequences.

## 10. Conductors and local factors

### 10.1 Conductor conventions

The split conductor $a_G(\pi)$ is the newvector exponent: the least $n$ for which a generic irreducible has a nonzero $\mathcal K_1(\mathfrak p^n)$-fixed vector. On $D^\times$, normal principal-unit fixed spaces jump from zero to the whole representation, so the raw filtration index is not the same notion. The selected division packets carry the transfer-facing conductor established by their types:

$$
a_{G'}(\mu\circ\operatorname{Nrd})
=
\begin{cases}
1,&a_F(\mu)=0,\\
2a_F(\mu),&a_F(\mu)>0,
\end{cases}
\tag{10.1}
$$

and

$$
a_{G'}(\pi'(E,\theta))
=v_F(\mathfrak d_{E/F})
+f(E/F)a_E(\theta).
\tag{10.2}
$$

These conventions make transfer preserve the conductor exponent throughout the selected range. They do not assert equality of the underlying fixed spaces.

### 10.2 Special conductor calculation

If $a_F(\mu)=m>0$, the reduced norm on principal units satisfies

$$
\operatorname{Nrd}(U_D^{2m-1})
=\operatorname{Nrd}(U_D^{2m})
=U_F^m.
\tag{10.3}
$$

To verify (10.3), use the cyclic model

$$
D=F_2\oplus F_2\Pi,
\qquad \Pi^2=\varpi,
\qquad \Pi a=\sigma(a)\Pi,
$$

where $F_2/F$ is unramified quadratic and $\sigma$ is its nontrivial automorphism. For $x$ in the maximal ideal,

$$
\operatorname{Nrd}(1+x)
=1+\operatorname{Trd}(x)+\operatorname{Nrd}(x).
$$

If $x\in\mathfrak P_D^{2m-1}$ or $\mathfrak P_D^{2m}$, the first possible scalar trace lies in $\mathfrak p^m$. On the associated graded quotient it fills $\mathfrak p^m/\mathfrak p^{m+1}$ because $\operatorname{Tr}_{k_2/k}$ is surjective; the norm term is deeper. Successive lifting through the complete unit filtration proves that the image is all of $U_F^m$. Thus the division norm character first becomes trivial on $U_D^{2m-1}$. Its normalized division level is $2m-2$, so the transfer-facing conductor, defined as that level plus two, is $2m$. On the split side the exceptional induced model has two inducing characters of conductor $m$, and the newvector theorem gives exponent $2m$ for the Steinberg constituent.

If $\mu$ is unramified, the norm character is already trivial on $\mathcal O_D^\times$, while the Steinberg twist has an Iwahori line and no hyperspecial line. The transfer-facing value one records this monodromy boundary. Hence

$$
a_G(\operatorname{St}\otimes\mu)
=a_{G'}(\mu\circ\operatorname{Nrd})
=a_{\mathrm{sp}}(\mu).
\tag{10.4}
$$

### 10.3 Dihedral conductor calculation

For a tame pair, both type calculations yield

$$
\boxed{
a_G(\pi(E,\theta))
=a_{G'}(\pi'(E,\theta))
=v_F(\mathfrak d_{E/F})
+f(E/F)a_E(\theta).
}
\tag{10.5}
$$

Here is the mechanism on the division side. The last visible simple character is defined by $\psi_D(\beta x)$. Triviality on an ambient unit group occurs exactly when the corresponding lattice lies in the trace-dual annihilator of $\beta$ and its intersection with $E$ lies in the kernel of $\theta$. The displacement between the $D$-trace-dual lattice and the $E$-trace-dual lattice contributes $v_F(\mathfrak d_{E/F})$. Each $E$-unit layer has $F$-length $f(E/F)$, giving the second term. Minimality proves nontriviality on the preceding layer.

The split newvector calculation reads the same last-layer datum in the hereditary order defining the type. Mackey decomposition shows that exactly one double coset contributes at the exponent in (10.5), while the simple character kills every contribution at lower exponent. Hence the newvector appears there with multiplicity one.

If $E/F$ is unramified, (10.5) becomes $2a_E(\theta)$. Depth zero has conductor two. If $E/F$ is tamely ramified quadratic, it becomes $a_E(\theta)+1$, and admissibility forces $a_E(\theta)\ge2$. Under twisting, the exact formula is obtained by replacing $\theta$ with $\theta(\chi\circ N_{E/F})$; cancellation can lower the result.

### 10.4 The common Weil--Deligne datum

The selected packet labels determine two-dimensional Frobenius-semisimple Weil--Deligne representations:

$$
\operatorname{St}\otimes\mu,
\ \mu\circ\operatorname{Nrd}
\longmapsto
\operatorname{Sp}_2(\mu),
\tag{10.6}
$$

and

$$
\pi(E,\theta),
\ \pi'(E,\theta)
\longmapsto
\operatorname{Ind}_{W_E}^{W_F}\theta,
\qquad N=0.
\tag{10.7}
$$

Regularity makes (10.7) irreducible: restricting to $W_E$ gives $\theta\oplus\theta^\sigma$, and equality of the two characters is exactly the reducibility condition. The determinant of (10.7) is (5.3). The induction formula for Artin conductors gives

$$
a_F(\operatorname{Ind}_{W_E}^{W_F}\theta)
=v_F(\mathfrak d_{E/F})
+f(E/F)a_E(\theta),
\tag{10.8}
$$

which recovers (10.5). For (10.6), the monodromy conductor is one when $\mu$ is unramified and the two ramified character lines contribute $2a_F(\mu)$ otherwise, recovering (10.4).

Thus the common parameter is compatible independently with both the central-character and conductor calculations. It is not inferred merely from equality of those two coarse invariants; it is attached to the common selected label.

### 10.5 Euler and epsilon factors

The common data (10.6)--(10.7) predict the factors, but preservation would be circular if the division factors were merely declared to be the parameter factors. On the split side the earlier Whittaker functional equations calculate the factors independently. On $D^\times$, take a matrix coefficient $c$ and $\Phi_D\in C_c^\infty(D)$ and form

$$
Z_D(s,\Phi_D,c)
=\int_{D^\times}\Phi_D(x)c(x)
|\operatorname{Nrd}(x)|^{s+1/2}\,d^\times x.
\tag{10.9a}
$$

Use the self-dual additive measure for $(x,y)\mapsto\psi(\operatorname{Trd}(xy))$ and the degree-two anisotropic Fourier normalization

$$
\mathcal F_D\Phi_D(y)
=-\int_D\Phi_D(x)\psi(\operatorname{Trd}(xy))\,dx.
\tag{10.9b}
$$

The minus sign is the Hasse sign of the nonsplit degree-two algebra. The functional equation for (10.9a), obtained by finite Fourier transform on sufficiently deep lattice quotients and passage to the limit, defines the analytic division-side $L$- and epsilon factors. We now compare these independent factors with (10.6)--(10.7).

**Proposition 10.1 (division functional equation in the selected range).** For a selected irreducible $\pi'$ and its contragredient, the integrals (10.9a) span fractional ideals generated by rational functions of $q^{-s}$. With (10.9b), Fourier transform carries the normalized integral for $\pi'$ to that for $(\pi')^\vee$ multiplied by one scalar rational function. After removing the Euler generators, that scalar is the epsilon factor calculated below.

**Proof strategy.** Reduce both the test function and the matrix coefficient to finite quotients of the maximal-order filtration. Fourier transform there is an ordinary finite transform. Trace-duality exchanges the two endpoint lattices, while Schur orthogonality makes the resulting scalar independent of the chosen matrix coefficient.

**Proof.** Smoothness and finite dimensionality give $r$ such that $U_D^r$ acts trivially on $\pi'$. Subdivide $D^\times$ into cosets of $U_D^r$ and valuation shells. On every compact valuation interval, (10.9a) is a finite matrix sum. Only the shells approaching zero can form a tail. Multiplication by a prime element translates that tail by one shell, while its square is central; hence the tail satisfies a degree-at-most-two recurrence. The integral is therefore rational in $q^{-s}$.

Reduced-trace duality gives

$$
(\mathfrak P_D^m)^\perp=\mathfrak P_D^{-m-1}.
$$

Thus (10.9b) sends a characteristic function of a coset of $\mathfrak P_D^m$ to an explicit character times the characteristic function of its annihilator. Such coset functions span the test space. On the finite quotients between the two lattices, applying Fourier transform twice is reflection, with the anisotropic Hasse scalar removed by the minus sign in (10.9b). Pair the resulting finite operator with matrix coefficients of $\pi'$ and $(\pi')^\vee$. Finite-group Schur orthogonality shows that the proportionality operator is scalar on the irreducible isotypic block and hence is independent of the chosen coefficient. Passing compatibly through deeper quotients proves the functional equation for every test function. Removing the geometric shell recurrences gives the Euler generators; the remaining scalar is a monomial times a finite Gauss sum, which is the epsilon factor. $\square$

For a special packet,

$$
L(s)=L(s+1/2,\mu).
\tag{10.9}
$$

If $\mu$ is unramified and $\alpha=\mu(\Phi)=\mu(\varpi)$, then

$$
L(s)=\frac1{1-\alpha q^{-s-1/2}},
$$

and for $n(\psi)=0$,

$$
\epsilon(s)=-\alpha q^{-(s-1/2)}.
\tag{10.10}
$$

If $\mu$ is ramified, the Euler factor is one and

$$
\epsilon(s,\operatorname{Sp}_2(\mu),\psi)
=\epsilon(s+1/2,\mu,\psi)
\epsilon(s-1/2,\mu,\psi).
\tag{10.11}
$$

These formulas also follow directly from (10.9a). Decomposing $D^\times$ into reduced-norm valuation shells gives the geometric series in (10.9) when $\mu$ is unramified; unit averaging kills that series when $\mu$ is ramified. Fourier reversal leaves one boundary shell in the unramified case, and the sign in (10.9b) makes its contribution (10.10). In the ramified case the two boundary unit sums are precisely the rank-one Gauss sums for $\mu|\cdot|^{1/2}$ and $\mu|\cdot|^{-1/2}$, giving (10.11). Thus the special division integral, the split Whittaker calculation, and the centered special block agree.

For a dihedral packet, the inertia-invariant space of the irreducible two-dimensional induction is zero. Otherwise it would contain an unramified subrepresentation, contradicting irreducibility. Hence

$$
L(s,\pi(E,\theta))
=L(s,\pi'(E,\theta))=1.
\tag{10.12}
$$

Put $\psi_E=\psi\circ\operatorname{Tr}_{E/F}$. The induction formula for epsilon factors gives

$$
\boxed{
\epsilon_F(s,\operatorname{Ind}_{W_E}^{W_F}\theta,\psi)
=\lambda(E/F,\psi)\epsilon_E(s,\theta,\psi_E).
}
\tag{10.13}
$$

The lambda factor is generally nontrivial for ramified $E/F$ and cannot be dropped. Its monomial exponent, together with the different shift in the conductor of $\psi_E$, is precisely (10.8). This is the parameter-side formula that the independent division integral must reproduce.

It remains to verify that (10.13) is also the factor produced by (10.9a) for $\pi'(E,\theta)$. Choose a matrix coefficient supported on the inducing subgroup $J'$. Frobenius reciprocity reduces the integral to $J'$. On the simple-character subgroup, additive Fourier transform is the finite Heisenberg transform from Lemma 7.1. A maximal isotropic polarization cancels the variables complementary to $E$ in pairs. What remains is the rank-one Tate integral over $E^\times$ for $\theta$ and $\psi_E$. Comparison of the two self-dual measures contributes exactly $\lambda(E/F,\psi)$; the anisotropic sign in (10.9b) and the complementary Fourier index $-1$ cancel. Hence the division functional equation gives (10.13), not merely a factor assigned by the parameter label.

Regularity makes the remaining unit average zero, so its Euler factor is one. This agrees with the parameter argument in (10.12) and with the split Kirillov calculation. We have therefore proved equality of the independently constructed split, division, and Weil--Deligne $L$- and epsilon factors. Equality of gamma factors follows from their definition in terms of $L$, epsilon, and the dual parameter.

### 10.6 Changes of additive character and measure

Let $\psi_a(x)=\psi(ax)$ for $a\in F^\times$. A two-dimensional parameter $V$ satisfies

$$
\epsilon(s,V,\psi_a)
=\det V(a)|a|^{2(s-1/2)}
\epsilon(s,V,\psi).
\tag{10.14}
$$

The determinant is the common central character, so both members of a selected packet transform identically. If an additive Haar measure is multiplied by a positive scalar $b$ while $\psi$ is fixed, the epsilon factor is multiplied by $b^2$. Equality across transfer survives any common change but not an inconsistent measure choice.

For an unramified twist $\chi$ with $\chi(\Phi)=\beta$,

$$
\epsilon(s,V\otimes\chi,\psi)
=\beta^{a(V)+2n(\psi)}\epsilon(s,V,\psi).
\tag{10.15}
$$

This formula jointly checks the geometric Frobenius, reciprocity, conductor, and additive-character conventions.

## 11. Types, newvectors, and level

### 11.1 What transfer can compare

The split representation is infinite-dimensional and has a one-dimensional newvector line at its conductor. The division representation is finite-dimensional, and every principal-unit subgroup $U_D^r$ is normal. Therefore, if one nonzero vector is fixed by $U_D^r$, irreducibility makes the whole representation fixed.

There can consequently be no natural equality

$$
\pi^{\mathcal K_1(\mathfrak p^n)}
\simeq
\pi'^{U_D^r}
$$

based only on matching exponents. The correct integral-level statement compares the split newvector or type multiplicity line with the distinguished multiplicity line of the division type. Equality of conductor exponents identifies where those lines first occur; it does not identify the surrounding fixed spaces.

### 11.2 Special type lines

If $\mu$ is unramified, $\operatorname{St}\otimes\mu$ has a one-dimensional Iwahori-fixed line on which the finite Iwahori quotient acts through the sign character. Its division companion is trivial on $\mathcal O_D^\times$. These are the minimal special type lines selected by conductor one.

If $a_F(\mu)=m>0$, the split newvector first appears at $\mathcal K_1(\mathfrak p^{2m})$. Formula (10.3) places the division character at the corresponding norm depth. In either case the relevant line is defined only up to a nonzero scalar; local transfer does not canonically choose a basis vector.

### 11.3 Dihedral multiplicity lines

Let $\Lambda$ and $\Lambda'$ be the types in (5.6)--(5.7). Their defining multiplicities are

$$
\dim\operatorname{Hom}_{J}(\Lambda,\pi(E,\theta))=1,
$$

$$
\dim\operatorname{Hom}_{J'}(\Lambda',\pi'(E,\theta))=1.
\tag{11.1}
$$

For compact induction, the identity coset supplies a nonzero map. Exact intertwining of a simple type says that every other double coset contributes zero, so Frobenius reciprocity proves multiplicity one. The common last-layer character and Lemma 7.1 identify the labels of the two lines. After choosing a primitive torus vector, the comparison is unique up to a coefficient-field unit.

On the split side, the newvector at exponent (10.5) is obtained from the type line by the standard compact averaging compatible with the central character. Only one double coset survives: at every other coset the last simple-character layer is nontrivial. On the division side the corresponding object remains the type multiplicity line, since averaging over a normal unit subgroup would reveal either no vectors or all vectors.

### 11.4 Oldvectors and the anisotropic jump

For $r\ge a_G(\pi)$, a selected generic split representation satisfies

$$
\dim\pi^{\mathcal K_1(\mathfrak p^r)}
=r-a_G(\pi)+1.
\tag{11.2}
$$

Successive diagonal translates of the newvector give these oldvectors, and their supports in the Kirillov model prove linear independence. The standard recurrence expresses every invariant vector as their span.

There is no analogue of (11.2) on $D^\times$. Once $U_D^r$ enters the kernel, the fixed-space dimension jumps to $\dim\pi'$. This contrast is expected: transfer preserves the elliptic representation and its minimal arithmetic label, not the geometry of the two ambient buildings.

## 12. Integral type lattices

### 12.1 Coefficient rings and integrality

Let $L/\mathbf Q_\ell$ be finite with valuation ring $R$, and assume $\ell\ne p$. A selected label is integral over $R$ if all its character values lie in $L$ and are units of $R$. After enlarging $L$, this includes finite-order tame characters and the roots of unity occurring in simple characters. An unramified scalar is allowed only when its value on $\varpi$ is an $R$-unit.

The unit condition is necessary. If an unramified character sends $\varpi$ to a nonunit, a finite nonzero $R$-lattice cannot be stable under both $\varpi$ and $\varpi^{-1}$. Thus no unconditional integral-lattice statement can be made for an arbitrary complex quasicharacter.

### 12.2 Special lattices

For a unit-valued $\mu$, the division companion has the rank-one stable lattice

$$
R(\mu\circ\operatorname{Nrd}).
$$

The split Steinberg representation has its usual lattice of locally constant $R$-valued functions on $\mathbf P^1(F)$ modulo constant functions, twisted by $\mu$. The quotient is torsion free: a function whose multiple is constant differs from a constant by an $R$-valued function only when it was already constant modulo the lattice. Hence the Steinberg lattice is flat and its minimal Iwahori or ramified newvector line is a free rank-one direct summand.

The exact sequence (4.3) and the fixed-point calculation are integral. Therefore the elliptic sign and the special type-line labels are preserved by finite extension of $R$.

### 12.3 Dihedral type lattices

At depth zero, the inducing characters are unit valued, so they preserve rank-one lattices. Finite induction gives stable lattices in both finite types.

At positive depth, the simple character has $p$-power-order values. Since $\ell\ne p$, those values are units. Choose a maximal isotropic subgroup in the finite Heisenberg quotient and extend the simple character over it. Finite induction produces a finite free $R$-module whose generic fiber is the irreducible Heisenberg representation.

Extending across the tame torus requires more care than scaling one operator: several projective extension operators must preserve one lattice simultaneously. Remove the unit-valued central scalar, choose any full lattice in the finite-dimensional extension space, and take the sum of its translates under representatives of the finite quotient through which the remaining action factors. This orbit sum is full, stable, finitely generated, and torsion free, hence finite free over the DVR $R$. It introduces no averaging denominator and proves existence even at nonbanal primes. We obtain finite free type lattices

$$
\Lambda_R\subset\Lambda_{\theta^\natural},
\qquad
\Lambda'_R\subset\Lambda'_{\theta^\natural}.
\tag{12.1}
$$

The division induction

$$
\pi'_R=\operatorname{Ind}_{J'}^{G'}\Lambda'_R
$$

is finite free because the relevant coset set is finite modulo the central action. On the split side the full compact induction need not be finite over $R$, but every compact-open fixed module used to form the newvector is finite free.

The Fourier sums in Lemma 7.1 are finite sums of integral roots of unity multiplied by powers of $q$. They therefore lie in $R$, although the sums themselves need not be units. The characteristic-zero comparison identifies the labels of the one-dimensional multiplicity spaces; it does not give a canonical linear map between representations of different groups. Saturation in the next section removes the scalar ambiguity after an identification of those two lines is chosen.

### 12.4 Saturated multiplicity lines

Let $M_R$ be the finite free fixed module in which the split type or newvector line $\mathcal L_L$ occurs. Its integral line is the saturated intersection

$$
\mathcal L_R=M_R\cap\mathcal L_L.
$$

Indeed, if $a m\in\mathcal L_R$ for nonzero $a\in R$ and $m\in M_R$, then $m\in\mathcal L_L$ because $\mathcal L_L$ is an $L$-subspace; hence $m\in\mathcal L_R$. Thus $M_R/\mathcal L_R$ is torsion free, so $\mathcal L_R$ is a rank-one direct summand. The same construction gives a division multiplicity line $\mathcal L'_R$.

The character comparison identifies the two lines by their common selected label but supplies no preferred bases. Choose any nonzero $L$-linear identification between them. Multiplying it by one element of $L^\times$ makes a primitive generator map to a primitive generator. Any two such primitive normalizations differ by $R^\times$. Thus there is a well-defined correspondence

$$
\mathcal L_R\longleftrightarrow\mathcal L'_R
\tag{12.2}
$$

up to the unavoidable unit scalar. This is the precise integral type-lattice compatibility needed in level change; it does not assert an isomorphism of the full split and division representations.

### 12.5 Perfect pairings

Put

$$
\Lambda_R^\#=\operatorname{Hom}_R(\Lambda_R,R)
$$

with contragredient action. On the division side, induced functions pair by the finite coset sum

$$
\langle f,f^\#\rangle
=\sum_{x\in J'\backslash G'}
\langle f(x),f^\#(x)\rangle.
\tag{12.3}
$$

The sum is independent of representatives because the two transformation laws cancel. It is invariant because right translation permutes the cosets. It is perfect because, after choosing coset representatives, it is the orthogonal direct sum of perfect pairings on $\Lambda'_R$.

The split newvector lattice pairs perfectly with the contragredient newvector lattice after primitive normalization. Under (9.4), inversion of the admissible label identifies the corresponding dual lines. No denominator is introduced: (12.3) is a sum, not an average.

### 12.6 Reduction and the nonbanal boundary

Stable lattices and their reductions always exist under the unit-valued and $\ell\ne p$ hypotheses. Irreducibility and multiplicity one after reduction require more. A uniform sufficient banal condition for every selected quadratic type here is

$$
\ell\nmid q(q-1)(q+1).
\tag{12.4}
$$

Indeed, the congruence and Heisenberg quotients are $p$-groups, while the remaining depth-zero, torus-normalizer, stabilizer, and coset factors divide products of $q-1$ and $q+1$. Under (12.4) every relevant finite averaging idempotent is defined over $R$, the reduced intertwining calculation is unchanged, and the two reduced multiplicity lines remain one dimensional. The perfect pairing remains nondegenerate. More economically, one may replace (12.4) by the exact requirement that $\ell$ divide none of the finitely many controlling quotient orders for the chosen type; (12.4) is the packet-uniform hypothesis used here.

If $\ell$ divides $q+1$, two distinct depth-zero characters of $k_2^\times$ can become congruent to their Frobenius conjugates. The reduced index-two induction may split or acquire new endomorphisms. At positive depth the Heisenberg quotient is a $p$-group and causes no problem when $\ell\ne p$, but its tame normalizer can have order divisible by $q-1$ or $q+1$. Projectors to tame eigenspaces may then cease to be exact.

The correct conclusion has two layers. Finite free stable lattices, saturated selected lines, and perfect contragredient pairings hold for integral labels with $\ell\ne p$. Preservation of irreducibility and multiplicity under reduction additionally requires (12.4), or the equivalent type-by-type nondivisibility condition just stated.

## 13. Worked packets and boundary tests

### 13.1 An unramified special twist

Let $\mu$ be unramified and put $A=\mu(\varpi)$. The selected pair is

$$
\operatorname{St}\otimes\mu
\quad\longleftrightarrow\quad
\mu\circ\operatorname{Nrd}.
$$

Both central characters are $\mu^2$ and both transfer-facing conductors are one. For $g\leftrightarrow d$,

$$
\Theta_{\operatorname{St}\otimes\mu}(g)
=-\mu(\det g)
=-\mu(\operatorname{Nrd}d).
$$

With $n(\psi)=0$,

$$
L(s)=\frac1{1-Aq^{-s-1/2}},
\qquad
\epsilon(s)=-Aq^{-(s-1/2)}.
$$

The conductor is not $2a(\mu)=0$: the nonzero monodromy in $\operatorname{Sp}_2(\mu)$ contributes one.

### 13.2 A ramified special twist

Let $a_F(\mu)=m>0$. Then both conductors are $2m$ and both Euler factors are one. The epsilon factor is the product (10.11) of the two shifted rank-one factors. Its Gauss phase depends on $\mu$, so two characters with the same conductor need not give the same selected packet.

A particularly useful check is a tame quadratic $\mu$. Twisting the packet by $\mu^{-1}$ cancels the ramification and produces the unramified special packet. The conductor drops from two to one. Any rule using only the maximum of the old conductor and twice the twist conductor gives the wrong result.

### 13.3 An unramified depth-zero pair

Let $E/F$ be unramified quadratic and choose a character $\bar\theta$ of $k_2^\times$ with $\bar\theta^q\ne\bar\theta$. Inflate it to a character $\theta$ of $E^\times$ with $a_E(\theta)=1$. Both packet members have conductor two and central character $\theta|_{F^\times}\omega_{E/F}$.

For a matching elliptic unit whose residue coordinate is $x\in k_2^\times\setminus k^\times$,

$$
\Theta_G=-\bar\theta(x)-\bar\theta(x^q),
\qquad
\Theta_{G'}=\bar\theta(x)+\bar\theta(x^q).
$$

The common Euler factor is one, and

$$
\epsilon_F(s)
=\lambda(E/F,\psi)\epsilon_E(s,\theta,\psi_E).
$$

Changing the value of $\theta$ on a uniformizer can change the epsilon factor without changing the residue-unit character formula. This illustrates again that no single coarse invariant defines transfer.

### 13.4 A tame ramified pair

Assume $p\ne2$, let $E/F$ be ramified quadratic, and choose a minimal admissible $\theta$ with $a_E(\theta)=r\ge2$. Since $v_F(\mathfrak d_{E/F})=1$ and $f(E/F)=1$,

$$
a(\pi(E,\theta))
=a(\pi'(E,\theta))
=r+1.
$$

On the type-regular torus the two characters are sums of two Heisenberg traces and Lemma 7.1 supplies the sign. Near the center, extra conjugate embeddings enter; the shell calculation of Section 7.5 pairs their Fourier sums with the same sign. This is the basic example in which the two-normalizer formula alone is insufficient.

### 13.5 A cancelling twist

Let $E/F$ be unramified and let $\theta_0$ be minimal with $a_E(\theta_0)=2$. Choose $\chi$ so that $a_E(\chi\circ N_{E/F})=4$, and set

$$
\theta=\theta_0(\chi^{-1}\circ N_{E/F}).
$$

Then $a_E(\theta)=4$ and the associated packet has conductor eight. Twisting both sides by $\chi$ cancels the deeper norm layer and leaves the packet of $\theta_0$, whose conductor is four. The exact twisted label in (9.2), not a maximum formula, detects the drop.

### 13.6 The dyadic and primitive-wild boundary

When $p=2$, the unramified quadratic extension is still tame, so the depth-zero and unramified positive-depth constructions remain in the theorem. A ramified quadratic extension is wild. Its different exponent can exceed one, trace may vanish on the layer used in Section 5.2, and the extension of a simple character can require data not fixed by the tame Heisenberg quotient.

Primitive wild representations present the same obstruction more generally: their leading stratum is not captured by the selected tame quadratic pair. The compactness of $D^\times/F^\times$ still makes them finite-dimensional, but compactness does not supply the missing character comparison. This book therefore makes no transfer, conductor, factor, or integral-type assertion for them.

## 14. The trace-formula and integral-level interface

### 14.1 The pointwise local transfer

The datum required at a ramified inner-form place begins with a matching-class rule:

$$
P_g=P_d,
\qquad
\Theta_\pi(g)=-\Theta_{\pi'}(d).
\tag{14.1}
$$

The polynomial equality fixes the class orientation, including determinant/norm equality and compatibility with inversion. The character equality fixes the unique selected packet. No choices of embeddings or bases remain in either statement.

For special packets, (14.1) is the exact sequence calculation of Chapter 4. For depth-zero packets, it is the finite cuspidal calculation of Chapter 6. For positive-depth packets, it is the complementary Fourier-index calculation plus the near-central shell argument of Chapter 7. Thus the pointwise transfer is proved on the entire regular locus, not merely on a convenient torus neighborhood.

### 14.2 The orbital trace identity

Let $f$ and $f'$ be geometrically matching in the sense of (3.8), with compatible central character and elliptic support. Then Weyl integration and (14.1) give

$$
\boxed{
\operatorname{tr}\pi(f)
=-\operatorname{tr}\pi'(f').
}
\tag{14.2}
$$

Every geometric factor cancels term by term: the centralizer torus, its Haar measure, the Weyl group of order two, the discriminant, and the orbital integral. Exactly one spectral minus sign remains.

If a later trace formula uses signed transfer of test functions instead, the minus sign moves into the orbital condition and (14.2) becomes an equality. The two conventions are equivalent, but a single calculation must not mix them.

### 14.3 The integral level-change datum

For an integral selected label, the local level-change object is not an isomorphism of full representation lattices. It is the following package:

$$
(a(\pi),\mathcal L_R,\mathcal L_R^\#)
\quad\longleftrightarrow\quad
(a(\pi'),\mathcal L'_R,(\mathcal L'_R)^\#),
\tag{14.3}
$$

where the conductors are equal, the lines are saturated rank-one type multiplicity lines, and the pairings with the contragredient lines are perfect. The comparison of lines is unique up to $R^\times$. Under banal reduction hypotheses, the reduced lines retain multiplicity one.

This is exactly the amount of integral structure stable under transfer. It is enough to compare primitive local generators in level-change maps while respecting the very different dimensions of the ambient representations.

### 14.4 A normalization audit

The construction is governed by the following linked choices:

| datum | normalization |
|---|---|
| absolute value | $|\varpi|=q^{-1}$ |
| Frobenius | geometric |
| reciprocity | $\operatorname{rec}_F(\varpi)=\Phi$ |
| special block | centered $\operatorname{Sp}_2$ |
| quadratic type label | $\theta^\natural=\theta\Delta_{E/F,\theta}$ |
| additive conductor | $n(\psi)=0$ for kernel $\mathcal O$ |
| epsilon measure | self-dual for $\psi$ |
| torus measure | $\operatorname{vol}(\mathcal O_E^\times)=1$ |
| geometric orbital transfer | $O_g(f)=O_d(f')$ |
| pointwise spectral sign | $\Theta_G=-\Theta_{G'}$ |

Changing one row is possible only if all dependent formulas change with it. Arithmetic Frobenius reciprocates unramified eigenvalues. An uncentered special block shifts Euler factors. Direct quadratic normalization moves the rectifier phase into central-character and Gauss-sum formulas. Signed function transfer moves, but does not erase, the final minus sign.

## 15. The complete selected theorem

### 15.1 The comparison table

| invariant | special label $\mu$ | dihedral label $(E,\theta)$ |
|---|---|---|
| split member | $\operatorname{St}\otimes(\mu\circ\det)$ | $\pi(E,\theta)$ |
| division member | $\mu\circ\operatorname{Nrd}$ | $\pi'(E,\theta)$ |
| central character | $\mu^2$ | $\theta|_{F^\times}\omega_{E/F}$ |
| parameter | $\operatorname{Sp}_2(\mu)$ | $\operatorname{Ind}_{W_E}^{W_F}\theta$ |
| conductor | $1$ if $a(\mu)=0$, otherwise $2a(\mu)$ | $v_F(\mathfrak d_{E/F})+f(E/F)a_E(\theta)$ |
| Euler factor | $L(s+1/2,\mu)$ | $1$ |
| epsilon factor | factor of $\operatorname{Sp}_2(\mu)$ | $\lambda(E/F,\psi)\epsilon_E(s,\theta,\psi_E)$ |
| elliptic character | negative of division value | negative of division value |
| integral object | primitive special line | primitive newvector/type line and division multiplicity line |

Every row respects twisting. In the special column replace $\mu$ by $\mu\chi$. In the dihedral column replace $\theta$ by $\theta(\chi\circ N_{E/F})$ and recompute its actual conductor, allowing cancellation.

### 15.2 Main theorem

**Theorem 15.1 (local Jacquet--Langlands in the selected range).** Let $F$ be a nonarchimedean local field of characteristic zero and let $D/F$ be the quaternion division algebra. There is a unique bijection

$$
\operatorname{JL}_{\mathrm{sel}}:
\mathcal D_G\xrightarrow{\sim}\mathcal D_{G'}
$$

such that, for matching separable regular elements,

$$
\Theta_\pi(g)
=-\Theta_{\operatorname{JL}_{\mathrm{sel}}(\pi)}(d).
\tag{15.1}
$$

It is given by

$$
\operatorname{St}\otimes(\mu\circ\det)
\longmapsto
\mu\circ\operatorname{Nrd}
$$

and

$$
\pi(E,\theta)
\longmapsto
\pi'(E,\theta)
$$

for tame admissible quadratic pairs. It commutes with twists and contragredients and preserves central characters, conductor exponents, the selected Weil--Deligne datum, and local $L$-, epsilon-, and gamma factors. For geometrically matching elliptic test functions it gives the trace identity (14.2).

If the selected label is unit valued over a valuation ring $R$ with residue characteristic $\ell\ne p$, the types admit finite free stable lattices, the saturated selected multiplicity lines correspond up to $R^\times$, and their contragredient pairings are perfect. Under the stated banal finite-quotient hypotheses, multiplicity one and irreducibility of the selected type survive reduction.

**Proof.** The matching-class bijection and measure comparison are Chapters 2 and 3. The special character identity is (4.6). The depth-zero identity is (6.4), and the positive-depth identity follows from Lemma 7.1, the shell calculation, and twisting in Sections 7.4--7.6. Label recovery proves bijectivity and uniqueness in Chapter 8. Chapter 9 proves the structural compatibilities. Chapter 10 proves conductor and factor compatibility. Chapters 11 and 12 prove type-line and integral-lattice compatibility. Weyl integration gives the trace identity in Chapter 14. $\square$

### 15.3 Exact scope

The theorem includes all smooth special twists, all regular unramified depth-zero pairs, all tame positive-depth pairs, and all their norm twists. In residue characteristic two, the unramified quadratic family remains included. Nonminimal labels are included through exact twisting rather than through an incorrect maximum rule for conductors.

The theorem excludes principal series and one-dimensional split representations because they are not in the discrete selected spectrum. It excludes ramified dyadic positive-depth pairs and primitive wild packets because the tame complementary Fourier-index lemma does not construct or compare their extra extension data. It does not claim an equality of full fixed spaces or representation lattices, and it does not claim irreducibility after reduction outside the banal range.

These are exact mathematical boundaries, not promises deferred inside a proof. Within them every selected representation is constructed, every matching regular character contribution is compared, and every catalogued compatibility has been established.

### 15.4 Conclusion

Local Jacquet--Langlands in degree two begins with a simple piece of geometry. A separable irreducible quadratic polynomial determines one elliptic matrix class and one division-algebra class. Their centralizers are the same quadratic torus, their Weyl discriminants agree, and compatible Haar measures let their orbital integrals enter Weyl integration with identical geometric weights.

The spectral sign has a different origin. For a Steinberg twist it comes from the vanishing of the exceptional principal-series character on elliptic classes. For a depth-zero dihedral packet it is the alternating sign in the finite cuspidal construction. At positive depth it is the difference between the two norm classes defining the split and nonsplit cyclic algebras. The resulting opposite finite Fourier indices persist through every near-central correction shell. These three calculations produce the same single sign.

The character identity then organizes the rest of the theory. Central scaling proves equality of central characters, common norm values prove twist compatibility, and inversion proves contragredient compatibility. The common selected Weil--Deligne label explains the conductor and local-factor formulas, including the monodromy contribution for unramified Steinberg twists and the lambda constant for quadratic induction. Integral Heisenberg models and saturated multiplicity lines retain the comparison over valuation rings without pretending that the ambient representations have the same dimension.

The resulting package is the precise local input required for two later operations. Geometric matching of orbital integrals converts the pointwise identity into the signed trace comparison used in global inner-form arguments. Equality of conductors together with corresponding primitive type lattices supplies the local datum used in integral level change. Within the special and selected dihedral range, the transfer is therefore canonical, character-theoretic, normalization-complete, and integrally controlled.
