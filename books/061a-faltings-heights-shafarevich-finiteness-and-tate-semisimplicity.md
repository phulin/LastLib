# Faltings Heights, Shafarevich Finiteness, and Tate Semisimplicity

## Contents

1. [The source-closure audit](#1-the-source-closure-audit)
   - [What Books 1--61 actually supply](#11-what-books-1--61-actually-supply)
   - [The first conditional gate](#12-the-first-conditional-gate)
2. [The exact arithmetic-geometric boundary](#2-the-exact-arithmetic-geometric-boundary)
   - [The restricted arithmetic Siegel package](#21-the-restricted-arithmetic-siegel-package)
   - [The integral Hodge--theta comparison](#22-the-integral-hodge--theta-comparison)
   - [The logarithmic determinant and Fourier--Jacobi package](#23-the-logarithmic-determinant-and-fourier--jacobi-package)
   - [Two counterboundaries](#24-two-counterboundaries)
3. [The maximal honest conditional theorem](#3-the-maximal-honest-conditional-theorem)
4. [The carrier-restricted completion problem](#4-the-carrier-restricted-completion-problem)
5. [The exact conditional and source-closed argument](#5-the-exact-conditional-and-source-closed-argument)
   - [One global semistable field](#51-one-global-semistable-field)
   - [The semistable Hodge-base-change gate](#52-the-semistable-hodge-base-change-gate)
   - [Stable Faltings height](#53-stable-faltings-height)
   - [Hermitian determinants and finite slopes](#54-hermitian-determinants-and-finite-slopes)
   - [The corrected conditional slope theorem](#55-the-corrected-conditional-slope-theorem)
   - [From moduli height to Shafarevich finiteness](#56-from-moduli-height-to-shafarevich-finiteness)
   - [Finite isogeny classes and stable lattices](#57-finite-isogeny-classes-and-stable-lattices)
   - [The lattice criterion and Tate semisimplicity](#58-the-lattice-criterion-and-tate-semisimplicity)
   - [The FLT carrier endpoint](#59-the-flt-carrier-endpoint)
6. [Conclusion](#6-conclusion)

**Status.** Conditional and not source-closed as a Faltings-height proof. The first gate is
$(\mathrm{SHB})$; stable-height field-independence and the restricted carrier-height packages
follow it. The fixed-torsion semistability theorem and the downstream descent/direct-factor,
stable-lattice, and Jacobson-radical implications are proved.

## 1. The source-closure audit

The theory in this volume has a clean sequence of conditional gates. The fixed-torsion
semistability argument, the abstract arithmetic slope algebra, and the entire implication from a
genuine moduli-height bound to Tate semisimplicity are source-closed from Books 1--61. Ramified
semistable Hodge base change is not. It is the first unresolved input. Only after that input is
assumed is the stable Faltings height field-independent in the source chain used here; the next
unresolved inputs are the integral arithmetic geometry at the boundary of Siegel moduli and the
application-specific Fourier--Jacobi determinant estimate.

Accordingly, this volume does not assert any of the following statements unconditionally:

$$
\sup_A h_F^{\mathrm{st}}(A)<\infty,
$$

for abelian varieties of fixed dimension over a fixed number field with good reduction outside a
fixed finite set;

$$
\#\{A/K:\dim A=g,\ A\text{ good outside }S\}/\simeq_K<\infty;
$$

or

$$
V_\ell A\text{ is semisimple as a }\mathbf Q_\ell[G_K]\text{-module}.
$$

The purpose of the volume is positive as well as diagnostic. It closes Book 41's
potential-semistability interface by one fixed torsion field, preserves the proved implications
after a genuine height bound, states $(\mathrm{SHB})$ at its precise complete-DVR strength,
and restricts the later geometric height hypotheses to the finite collection of dimensions and
isogeny loci of the FLT carrier Jacobians. It does not close Book 41's semistable
Hodge-base-change interface.

### 1.1 What Books 1--61 actually supply

The following ledger records the result of symbol searches and equivalent-form searches across
the repository. A statement marked *closed here* is proved below from the cited earlier books;
it is not merely renamed as a hypothesis.

| Claim | Actual earlier source | Status in this volume |
|---|---|---|
| potential semistable reduction | Book 61, Theorem 9.7 | proved earlier |
| persistence after further finite extension | Book 61, Section 9.7 | proved earlier |
| finite-level semistability test | Book 61, Corollary 10.4 | proved earlier |
| one global semistable field | finite-level test applied to $K(A[12])$ | closed here |
| ramified semistable Hodge base change $(\mathrm{SHB})$ | no theorem in Books 1--61; Book 60, Section 8.4 gives independence/descent only through common refinement of analytic uniformizations, and Section 13.1 preserves $E_L/M$ after normalization or admissible modification; Book 38, Sections 8.1--8.4 warn that ramified Neron base change need not be an isomorphism; Book 41, Sections 12.4 and 13.7 retain $(\mathrm{SHB})$ | first conditional gate |
| field-independence of stable Faltings height | Theorem 5.1 and Book 41's Arakelov normalization, conditional on $(\mathrm{SHB})$ | conditional on the first gate |
| determinant, saturation, and finite Plucker slope algebra | Book 41, Lemmas 13.3A--13.3B | reproved here |
| polarized descent and integral factor cancellation | Book 41, Sections 13.5--13.6 | reproved in the form used here |
| finite isogeny class to stable lattices to semisimplicity | Book 41, Chapters 14--15 | reproved here |
| restricted arithmetic toroidal Siegel boundary and integral Hodge--theta comparison | no theorem in Books 1--61 | conditional after $(\mathrm{SHB})$ |
| restricted logarithmic determinant and Fourier--Jacobi estimates | no theorem in Books 1--61 | conditional after $(\mathrm{SHB})$ |

Book 8 constructs relative Proj from an already defined quasi-coherent graded algebra, proves
bounded regularity on a fixed Hilbert locus, and constructs Grassmannians and Hilbert schemes.
Its Plucker calculation concerns the standard maximal minors of the universal quotient and proves
the usual projective embedding of a Grassmannian.

It does not construct the period-indexed graded algebras in a Mumford degeneration. It does not
construct a toroidal compactification of Siegel moduli, a Fourier--Jacobi filtration, an
arithmetic determinant complex, or universal minors with the arithmetic degrees and norm bounds
needed for a slope estimate. Uniform regularity says that finitely many degrees suffice once the
family and its section algebra exist; it does not supply the missing family or the required
determinant identities.

Book 41 deliberately leaves the Faltings-height route conditional. Its Sections 12.4 and 13.7
retain semistable Hodge base change as the hypothesis $(\mathrm{SHB})$. Section 13.7 then lists
the compactification and metric interfaces and the two arithmetic certificates that remain to
be proved after that local gate. In its notation these are

$$
(\mathrm{SHB}),\qquad(\mathrm{SC}),\qquad(\mathrm{MC}),\qquad
(\mathrm{AHS}_{\log}),\qquad(\mathrm{US}_\theta),
$$

with potential semistability supplied here by Theorem 5.1. Book 41 proves the abstract
determinant-and-saturation inequality, the abstract finite Plucker upper-slope criterion, and
the numerical implication from valid application-specific certificates. It expressly does not
prove $(\mathrm{SHB})$ or that the theta multiplication data satisfy those certificates.

After a genuine moduli-height bound is supplied, Book 41 does prove the remaining discrete
implications: Northcott, finite polarized descent, integral Zarhin factor cancellation, the
passage from Shafarevich finiteness to finite isogeny classes, the stable-lattice argument, and
the Jacobson-radical criterion for semisimplicity.

Book 58 algebraizes a proper formal scheme over a noetherian complete base when a compatible
formal ample line bundle is given. Its Grothendieck-existence statements concern coherent data on
a proper scheme over that complete base. They do not say that an arbitrary element of a completed
finite module comes from an etale neighborhood of an uncompleted algebraic base.

In particular, formal functions identifies inverse limits with completed modules. It does not
identify those completed modules with the original modules. A general formal power series in a
completed local ring need not be the image of a function on any etale neighborhood. Book 58 also
warns that formal neighborhoods do not automatically algebraize locally and that a formal generic
fiber requires additional nonarchimedean foundations.

Book 60 develops Raynaud uniformization over a complete discretely valued field. It defines the
two lattices, the period embedding, Poincare biextension data, the semilinear action after a finite
Galois splitting extension, and projective descent of a polarized analytic quotient. Section 8.4
compares choices of semistable model by a common admissible formal refinement and descends the
polarized analytic quotient. Section 13.1 says that finite scalar extension may require
normalization or admissible modification and uses generic-fiber invariance to preserve
$E_L/M$. These results repair important local terminology and make split-coordinate calculations
legitimate in their stated complete-DVR setting.

They do not identify the base change of the formal identity of a Neron model with the formal
identity of the new Neron model across a ramified extension, and they do not identify the two
Neron cotangent lattices. Preservation of an analytic quotient after normalization or admissible
modification does not imply either formal identity. They also do not construct the global
arithmetic toroidal compactification of the Siegel moduli scheme over
$\mathbf Z[1/N,\zeta_N]$, or prove that a local semilinear Galois action on Raynaud data is an
fpqc descent datum for all the integral period charts, their boundary divisors, their theta
lattices, and their chosen fan quotient across a ramified valuation-ring extension.

Book 38 constructs the canonical Neron base-change morphism. It proves that it is an isomorphism
under finite unramified base change, but its Sections 8.3--8.4 explicitly warn that under
ramification the base-changed model need not already be Neron. The component group can grow;
this does not decide whether the identity cotangent lattice happens to remain unchanged. Thus
Book 38 supplies the map occurring in $(\mathrm{SHB})$, not the assertion that the map is an
isomorphism on invariant differentials.

Book 61 proves potential semistable reduction and the monodromy package for abelian varieties
over complete discretely valued fields. It records persistence under further finite extension and
the multiplication of integral monodromy data by the ramification index. These results prove
Theorem 5.1, but they do not compare the Neron cotangent lattices after ramified base change.

These theorems are not stated for arbitrary valuation rings. They therefore cannot be inserted
without a reduction theorem into a valuative-criterion argument whose test object is an
arbitrary valuation ring over an arithmetic moduli base. Book 61 also contains no arithmetic
theta comparison or global height bound.

The search also finds later Hilbert--Blumenthal toroidal material. That is a different moduli
problem, is not among Books 1--61, and does not construct the arithmetic Siegel space needed
here. Thus it does not close any of the carrier-height packages below. Finally, the search finds no
earlier proof of dual invariance of the stable Faltings height and no proof of
$h_F^{\mathrm{st}}(Z(A))=8h_F^{\mathrm{st}}(A)$. Neither assertion is used in this volume.

### 1.2 The first conditional gate

After Books 60 and 61 are used at their stated strength, potential semistability and persistence
are closed, but semistable Hodge base change is not. The first conditional gate is the following
complete-DVR assertion. If $R'/R$ is a finite extension of complete discrete valuation rings,
$A/F$ is semistable, and $\mathcal A/R$ and $\mathcal A'/R'$ are the Neron models, then the
canonical Neron base-change morphism must induce an isomorphism

$$
\boxed{(\mathrm{SHB})\qquad
e'^*\Omega^1_{\mathcal A'^0/R'}
\xrightarrow{\sim}
e^*\Omega^1_{\mathcal A^0/R}\otimes_RR'.}
\tag{1.1}
$$

This is proved for good reduction and for unramified extensions. The ramified, semistable,
nonproper case is not sourced in Books 1--61. Assuming $(\mathrm{SHB})$, the normalized
Faltings height over an everywhere-semistable field is independent of that field, as shown in
Section 5.3.

Only after this first gate comes the carrier-height problem. For the FLT application it is
enough to treat the Zarhin stabilizations of abelian varieties in the isogeny classes of the
actual finite carrier-Jacobian array. A theorem for every abelian variety of a fixed dimension
would be stronger than necessary.

The standard route to that restricted height theorem consists of exactly three packages: a
restricted arithmetic Siegel toroidal construction, its integral metrized Hodge--theta
comparison, and a logarithmic Hilbert determinant/Fourier--Jacobi estimate. Chapter 2 states
their necessary content and nothing more.

## 2. The exact arithmetic-geometric boundary

Assume $(\mathrm{SHB})$ from (1.1) throughout this chapter. Then Section 5.3 makes the
normalized Hodge degree independent of the auxiliary everywhere-semistable field. The three
packages below are the next gates in the carrier-height route; none of them supplies
$(\mathrm{SHB})$.

Fix a finite array

$$
\mathscr C=\{(K_i,J_i)\}_{i=1}^m
\tag{2.1}
$$

of carrier Jacobians, where each $J_i$ is an abelian variety over the number field $K_i$. Put

$$
\mathscr I_i
=\{B/K_i:B\text{ is }K_i\text{-isogenous to }J_i\}/\simeq_{K_i}.
\tag{2.2}
$$

The FLT application needs finiteness of the sets $\mathscr I_i$, not a compactification theorem
in every genus and not Shafarevich finiteness over every number field. For
$B\in\mathscr I_i$, set

$$
Z(B)=(B\times B^\vee)^4.
\tag{2.3}
$$

Book 41 constructs a principal polarization on $Z(B)$. No comparison between the Faltings
heights of $B$, $B^\vee$, and $Z(B)$ will be assumed or needed.

Choose once and for all a full level $N\geq3$. The three packages below are required only in the
finite set of dimensions $8\dim J_i$ and only along the closures of the levelled points
attached to the varieties $Z(B)$ with $B\in\mathscr I_i$. This restriction is important: it
states the exact FLT need without pretending to prove the general arithmetic theory of Siegel
moduli.

### 2.1 The restricted arithmetic Siegel package

The first package, denoted $(\mathrm{Tor})_{\mathscr C,N}$, must construct in the relevant
dimensions a finite-type proper arithmetic toroidal space carrying the following data along the
carrier-isogeny locus:

- the fine level-$N$ Siegel moduli space as its open part;
- a finite admissible fan with genuine face gluings and a Cartier boundary;
- the integral Hodge line and the fixed theta line used for projective moduli coordinates;
- the period-indexed Mumford graded algebras, including their multiplication, Poincare
  cocycles, period actions, and compatibility on triple overlaps;
- the semiabelian or Mumford family needed to evaluate those lines at semistable points; and
- actual descent data, base-change compatibility, finite presentation, separatedness, and
  properness.

A monoid algebra for the base torus embedding is not yet the period quotient carrying the
degenerating abelian family. Relative Proj and Hilbert regularity from Book 8 become applicable
only after the graded algebra, its action, and its finite-generation and gluing properties have
been constructed.

At a ramified integral extension, the last bullet means fpqc descent on the integral charts over
the relevant tensor products. A semilinear action on the generic Raynaud datum is not a
substitute. Likewise, if properness is proved by a valuative criterion, one must either use a
proved reduction to the class of complete DVR tests covered by Books 60--61 or treat the
valuation rings appearing in the criterion. The complete-DVR theorem itself does not make that
reduction.

### 2.2 The integral Hodge--theta comparison

The second package, $(\mathrm{HT})_{\mathscr C,N}$, is an integral and metrized comparison on
the preceding restricted toroidal space. It must identify the tensor powers of the theta and
Hodge lines with their exact boundary and vertical corrections. In particular it must:

- calculate every horizontal boundary order from an integral Fourier--Jacobi expansion;
- prove that the leading coefficient is primitive at every relevant codimension-one point;
- include all vertical components, especially at primes dividing $N$;
- compare the translation-invariant theta metric with the Faltings metric at infinity; and
- produce a uniform projective-height inequality for the points of (2.3).

It is not enough to have an equality on the generic fiber. An unrecorded vertical divisor
changes the Arakelov degree. Nor does cubical rigidification force the determinant of an
integral theta frame to have unit leading coefficient: rigidification normalizes a line bundle
at the identity, whereas primitivity is a calculation about a chosen determinant section at
every codimension-one boundary point.

The comparison is to be applied directly to $Z(B)$. It therefore requires no assertion that
stable Faltings height is invariant under duality and no formula relating
$h_F^{\mathrm{st}}(Z(B))$ to $h_F^{\mathrm{st}}(B)$.

### 2.3 The logarithmic determinant and Fourier--Jacobi package

The third package, $(\mathrm{SlopeFJ})_{\mathscr C,N}$, supplies the application-specific
input to the abstract slope lemmas proved in Section 5.4. It consists of a finite list of
globally defined Hilbert multiplication or relation complexes and determinant maps, together
with the following verified properties:

1. the complexes, their differentials, determinant targets, metrics, and base-change maps are
   explicitly defined and have the asserted exactness;
2. two determinant channels have positive Hodge and effective-degeneration characters with the
   orientation required for integral maps;
3. their least Fourier--Jacobi monomials have primitive coefficients and no omitted vertical
   divisor;
4. a finite normalized tuple has no common zero on each lower-dimensional boundary parameter
   space and gives the required uniform cusp norm estimate; and
5. fixed integral Plucker frames have no common zero on every relevant Grassmannian and satisfy
   uniform Hermitian degree and operator-norm bounds.

The orientation in item 2 is essential. If two rank-one lattices are
$\pi^aR$ and $\pi^bR$, their symmetric distance $|a-b|$ forgets which contains which.
Divisibility by $\pi^{|a-b|}$ cannot be inferred from that number. Each determinant channel
must supply its actual oriented local order. Pairing an unconstructed map with a putative dual
does not restore the missing sign.

Similarly, exactness of an ambient complex does not imply the Plucker condition in item 5. A
$k$-plane can lie in the kernels of all selected minors even while the ambient differentials
have the expected ranks. The no-common-zero assertion is a separate theorem about the actual
finite family of integral sections.

Gaussian convergence supplies useful upper bounds after a least monomial has been identified.
It does not show that the coefficient of that monomial is uniformly bounded away from zero. The
finite nonvanishing tuple and its compact lower-dimensional parameter space are what must
supply that quantitative lower bound.

### 2.4 Two counterboundaries

The first counterboundary concerns completion. Let
$A=\mathbf Q[t]_{(t)}$ and $\widehat A=\mathbf Q[[t]]$. The henselization of $A$ is countable,
as is the union of the images of all finite-presentation etale neighborhoods of its closed
point, whereas $\widehat A$ is uncountable. Thus elements of a completed finite module need not
come from any etale neighborhood. Book 58 gives effectivity for coherent data on a fixed proper
scheme over a complete base, and algebraizes an abstract proper formal scheme when an ample
formal line is supplied. It does not make the map from algebraic sections to completed sections
surjective over an uncompleted cusp chart. Consequently formal tensors and relations may not be
declared algebraic merely because only finitely many of them were selected.

The second counterboundary concerns ramified descent. If
$R=k[[\pi]]$, $R'=k[[u]]$, and $\pi=u^e$, then

$$
R'\otimes_RR'
\simeq k[[u,v]]/(u^e-v^e)
\tag{2.4}
$$

after the appropriate completed interpretation. This overlap is not, in general, a product of
copies of $R'$; its components meet, and in wild characteristic it can carry nilpotent
phenomena. Isomorphisms indexed only by Galois conjugates on the generic fiber do not provide an
isomorphism over this overlap or the cocycle over the triple overlap. Book 61 makes the same
point for stable models: a semilinear action after ramified extension is weaker than integral
descent data. Therefore conjugate period forms lying in related cones do not by themselves
descend an integral fan chart, boundary equation, theta lattice, or Mumford family.

## 3. The maximal honest conditional theorem

For the finite carrier array (2.1), let $(\mathrm{CMH})_{\mathscr C,N}$ be the following
carrier moduli-height assertion: for each $i$ and every $B\in\mathscr I_i$, one can choose the
Zarhin principal polarization and a full level-$N$ structure over its level field so that the
projective heights, with respect to the fixed moduli embedding, of the resulting points

$$
x\bigl(Z(B),\lambda_{Z(B)},\alpha_N\bigr)
\tag{3.1}
$$

are uniformly bounded. The bound may depend on the finite array and on $N$. This formulation is
deliberately direct: it is a height bound for $Z(B)$ and contains no comparison with the height
of $B$.

The conditional carrier-height route and the source-closed downstream arguments prove

$$
\begin{gathered}
(\mathrm{SHB})
\Longrightarrow
\{\text{stable-height field-independence}\},\\
[(\mathrm{SHB})
+(\mathrm{Tor})_{\mathscr C,N}
+(\mathrm{HT})_{\mathscr C,N}
+(\mathrm{SlopeFJ})_{\mathscr C,N}]
\Longrightarrow
(\mathrm{CMH})_{\mathscr C,N}
\Longrightarrow
(\mathrm{IF})_{J_i/K_i}\text{ for every }i
\Longrightarrow
V_\ell J_i\text{ semisimple for every }i,\ell.
\end{gathered}
\tag{3.2}
$$

Here $(\mathrm{IF})_{J_i/K_i}$ says that the $K_i$-isogeny class of $J_i$ contains only
finitely many $K_i$-isomorphism classes. The middle implication uses Northcott, finite polarized
descent, and integral direct-factor cancellation. The final implication uses isogeny quotients
of stable lattices and the Jacobson-radical length argument.

There is also a uniform version. Let $(\mathrm{FH})_{K,S,g}$ denote a uniform projective-height
bound for the stabilized levelled moduli points attached to all $g$-dimensional abelian
varieties over $K$ with good reduction outside $S$. Then

$$
(\mathrm{FH})_{K,S,g}
\Longrightarrow
(\mathrm{FS})_{K,S,g}
\Longrightarrow
(\mathrm{IF})_{A/K}
\Longrightarrow
\{\text{finitely many stable }\mathbf Z_\ell\text{-lattice types in }V_\ell A\}
\Longrightarrow
V_\ell A\text{ semisimple}.
\tag{3.3}
$$

The first line of (3.2) is Proposition 5.3; the three restricted packages enter only after that
first gate. The occurrence of $(\mathrm{SHB})$ in the second line belongs only to the displayed
route from the three geometric packages to the carrier moduli-height assertion. If
$(\mathrm{CMH})_{\mathscr C,N}$ is supplied directly, its implication to isogeny finiteness
and semisimplicity does not use $(\mathrm{SHB})$. Likewise, (3.3) starts from a direct
projective-height hypothesis and its downstream arrows do not use stable-height
field-independence. The carrier theorem (3.2) is the smaller input needed downstream. The
uniform Shafarevich theorem (3.3) is recorded because it is reusable and because it explains
the traditional Faltings route. Neither display proves a conditional antecedent.

## 4. The carrier-restricted completion problem

A future source closes the displayed carrier-height route if it first proves $(\mathrm{SHB})$
and then proves the three packages of Chapter 2 on the points (3.1). The source of
$(\mathrm{SHB})$ need not be the source of the carrier packages. The latter need not develop
toroidal compactifications for unrelated PEL groups or prove a general theory for arbitrary
valuation rings. They must, however, establish every piece actually used on the restricted
locus:

1. algebraic period charts and a proper arithmetic Siegel toroidal space with genuine integral
   descent;
2. the exact integral metrized Hodge--theta identity, including horizontal boundary,
   level-prime, vertical, and archimedean terms; and
3. explicit oriented Hilbert determinant channels, primitive Fourier--Jacobi leading
   coefficients, uniform cusp estimates, and genuine integral Plucker frames.

Books 8 and 58 can be used after the relevant graded algebras or proper formal objects are
defined with the hypotheses of their theorems. Books 60 and 61 can be used after a complete-DVR
test has legitimately been reached, but do not themselves prove $(\mathrm{SHB})$. None of
these books manufactures the three displayed packages from formal expansions, Galois
conjugates, or regularity alone.

Thus the exact first unresolved theorem in the source chain is $(\mathrm{SHB})$. After it is
assumed, $(\mathrm{CMH})_{\mathscr C,N}$ is the next unresolved carrier conclusion, with the
three packages above as a sufficient arithmetic-geometric route. A direct proof of
$(\mathrm{CMH})_{\mathscr C,N}$ would bypass both $(\mathrm{SHB})$ and those packages for the
downstream finiteness argument. The unconditional general Faltings--Shafarevich theorem is not
relabelled as though it had been proved.

## 5. The exact conditional and source-closed argument

The failure of the height theorem does not force every part of the intended volume to remain a
sketch. Book 61 closes potential semistability and persistence, while Book 41 leaves
$(\mathrm{SHB})$ conditional and closes the arithmetic linear-algebra implication and
everything after a moduli-height bound. This chapter separates those statuses: Section 5.1 is
unconditional, Section 5.2 records the first gate, Section 5.3 derives stable-height
field-independence only under that gate, and Sections 5.4 and 5.6--5.8 preserve the proved
determinant, descent, direct-factor, stable-lattice, and Jacobson-radical arguments.

### 5.1 One global semistable field

The local potential-semistability theorem of Book 61 has a particularly clean global
application.

**Theorem 5.1 (simultaneous semistable extension).** Let $A$ be an abelian variety over a
number field $K$. There is a finite extension $L/K$ such that $A_L$ has semistable reduction at
every finite place. Once this is true over $L$, it remains true over every finite extension of
$L$.

**Proof.** Take

$$
L=K(A[12]).
$$

Thus every point of $A[3]$ and every point of $A[4]$ is $L$-rational. Let $w$ be a finite place
of $L$, with residue characteristic $p$, and complete at $w$.

If $p\ne3$, inertia acts trivially on $A[3]$. Book 61's finite-level semistability criterion,
used with $\ell=3\ne p$, says that $A$ is semistable at $w$. If $p=3$, inertia acts trivially
on $A[4]$, and the same criterion with $\ell=2$ says that $A$ is semistable at $w$. This covers
all finite places with one finite global field. Book 61 also proves that semistability persists
under every further finite extension. $\square$

This proof avoids an unproved passage from separately chosen local extensions to one global
field. The fixed torsion field supplies the global extension directly.

### 5.2 The semistable Hodge-base-change gate

Let $F$ be a complete discretely valued field, let $R$ be its valuation ring, and let $A/F$ be
semistable. Write $\mathcal A/R$ for its Neron model. For a finite extension $F'/F$, with
valuation ring $R'$ and Neron model $\mathcal A'/R'$, the generic identity induces the canonical
Neron base-change morphism

$$
h:\mathcal A^0\times_RR'\longrightarrow\mathcal A'^0.
$$

**Conditional Gate 5.2 (semistable Hodge base change, $(\mathrm{SHB})$).** For every such
$F'/F$, pullback along $h$ is required to be an isomorphism

$$
h^*:e'^*\Omega^1_{\mathcal A'^0/R'}
\xrightarrow{\sim}
e^*\Omega^1_{\mathcal A^0/R}\otimes_RR'.
\tag{5.1}
$$

Taking top exterior powers would then give the determinant comparison used below. This gate is
not proved in this volume.

There are two source-closed endpoint cases. If $A$ has good reduction, its Neron model is an
abelian scheme and remains so after arbitrary finite base change; smooth relative
differentials commute with base change. If $R'/R$ is unramified, Book 38, Theorem 8.1 identifies
$\mathcal A\times_RR'$ with $\mathcal A'$, so (5.1) follows again. Neither argument treats a
ramified extension when the connected Neron model is semiabelian and nonproper.

Book 60 does not fill that case. Its Section 8.4 proves independence of choices through a
common admissible formal refinement and effective descent of the polarized analytic quotient.
Its Section 13.1 permits normalization or admissible modification after scalar extension and
uses generic-fiber invariance to preserve the analytic quotient $E_{F'}/M$. Those statements do
not identify the base-changed formal identity neighborhood with the formal identity of the new
Neron model, and hence do not identify their cotangent lattices. Book 38, Sections 8.3--8.4
warn that ramified base change can change the Neron model and its component group; the
canonical morphism exists, but need not be an isomorphism of models. Book 41 therefore states
exactly (5.1) as $(\mathrm{SHB})$ in (12.4b) and leaves it conditional in Section 13.7.

Thus (5.1), including its determinant version, is the first conditional gate. Even if supplied,
it is only a complete-DVR statement and would not by itself justify an
arbitrary-valuation-ring step in a global compactification argument.

### 5.3 Stable Faltings height

Assume $(\mathrm{SHB})$ for the rest of this section.

Suppose first that $A/L$ is semistable at every finite place. Its Hodge line is

$$
\omega_{\mathcal A}
=e^*\det\Omega^1_{\mathcal A^0/\mathcal O_L}.
$$

At an embedding $\sigma:L\hookrightarrow\mathbf C$, give a top invariant differential $\eta$
the norm

$$
\|\eta\|_\sigma^2
=\frac{i^{g^2}}{(2\pi)^g}
\int_{A_\sigma(\mathbf C)}\eta\wedge\overline\eta,
\qquad g=\dim A.
\tag{5.3}
$$

The product formula makes the Arakelov degree

$$
\widehat{\deg}\,\overline\omega_{\mathcal A}
=\log\#(\omega_{\mathcal A}/\mathcal O_L\eta)
-\sum_{\sigma:L\hookrightarrow\mathbf C}\log\|\eta\|_\sigma
\tag{5.4}
$$

independent of the nonzero rational section $\eta$, with the usual fractional-ideal
interpretation. Put

$$
h_F(A/L)=\frac{1}{[L:\mathbf Q]}
\widehat{\deg}\,\overline\omega_{\mathcal A}.
$$

**Proposition 5.3 (conditional field-independence).** Assuming $(\mathrm{SHB})$, if $L'/L$
is finite, then

$$
h_F(A_{L'}/L')=h_F(A/L).
\tag{5.5}
$$

Consequently, for arbitrary $A/K$, the value

$$
h_F^{\mathrm{st}}(A)=h_F(A_L/L),
\tag{5.6}
$$

where $L/K$ is any everywhere-semistable field supplied by Theorem 5.1, is independent of $L$.

**Proof.** The hypothesis $(\mathrm{SHB})$ identifies the finite Hodge lattice after every
completed local base change. Hence its finite Arakelov degree is multiplied by $[L':L]$: the
local length is multiplied by the ramification index and repeated with the residue degree. Every complex
embedding of $L$ has $[L':L]$ extensions counted with multiplicity, and (5.3) is unchanged on
the relabelled complex fiber. Thus the archimedean degree is multiplied by the same factor.
Division by the field degree proves (5.5). Two choices in (5.6) are compared in a common finite
overfield, proving independence. $\square$

Subject to $(\mathrm{SHB})$, stable height is invariant under $K$-isomorphism. It is also
additive on products:

$$
h_F^{\mathrm{st}}(A\times B)
=h_F^{\mathrm{st}}(A)+h_F^{\mathrm{st}}(B).
\tag{5.7}
$$

Indeed, choose one finite field over which both factors are everywhere semistable. Products of
Neron models are Neron models, and at the identity

$$
e^*\Omega^1_{\mathcal A^0\times\mathcal B^0/\mathcal O_L}
\simeq e_A^*\Omega^1_{\mathcal A^0/\mathcal O_L}
\oplus e_B^*\Omega^1_{\mathcal B^0/\mathcal O_L}.
$$

Taking determinants tensors the two Hodge lines. Fubini's theorem and the signs from reordering
holomorphic and antiholomorphic differentials show that the metric (5.3) is the tensor-product
metric. Finite and archimedean degrees therefore add, proving (5.7).

There is also a useful isogeny comparison. Let $f:A\to B$ be a $K$-isogeny and choose a common
everywhere-semistable field $L$. Pullback gives an injection of Hodge lines with finite cokernel

$$
Q_f=\omega_{\mathcal A}/f^*\omega_{\mathcal B}.
$$

Change of variables on complex tori gives
$\|f^*\eta\|_{A,\sigma}^2=(\deg f)\|\eta\|_{B,\sigma}^2$. Comparing the two Arakelov degrees
therefore yields

$$
h_F^{\mathrm{st}}(B)-h_F^{\mathrm{st}}(A)
=\frac12\log\deg f-
\frac{1}{[L:\mathbf Q]}\log\#Q_f,
\tag{5.8}
$$

and hence

$$
h_F^{\mathrm{st}}(B)
\leq h_F^{\mathrm{st}}(A)+\frac12\log\deg f.
\tag{5.9}
$$

The right side is independent of the chosen semistable field by Proposition 5.3. Formula (5.8)
passes the multiplication-by-$n$ test: the complex term and the index of $n^g$ on the Hodge
line cancel. Inequality (5.9) does not bound an isogeny class because the isogeny degree may be
unbounded.

Book 41 constructs a principal polarization on $Z(A)=(A\times A^\vee)^4$. This volume uses
that construction only to place $Z(A)$ on principally polarized moduli. It neither asserts nor
needs a formula for the stable Faltings height of $A^\vee$ or $Z(A)$.

### 5.4 Hermitian determinants and finite slopes

We now separate the proved arithmetic linear algebra from the unproved theta certificates. Let
$L$ be a number field. For a Hermitian $\mathcal O_L$-lattice $\overline E$, define
$\widehat\deg\overline E$ by the determinant formula (5.4), and define

$$
\widehat\mu_{\max}(\overline E)
=\sup_{0\ne F\subset E\ \mathrm{saturated}}
\frac{\widehat\deg\overline F}{\operatorname{rank}F}.
$$

**Lemma 5.4 (determinant and saturation).** Let
$u:\overline F\to\overline E$ have generic rank $k=\operatorname{rank}F$. If

$$
I=E\cap u(F_L),
\qquad Q=I/u(F),
$$

then

$$
\widehat\deg\overline F+\log\#Q
=\widehat\deg\overline I
+\sum_\sigma\log\|\det u_\sigma\|,
\tag{5.10}
$$

and therefore

$$
\widehat\deg\overline F+\log\#Q
\leq k\widehat\mu_{\max}(\overline E)
+\sum_\sigma\log\|\mathop{\bigwedge}\nolimits^ku_\sigma\|.
\tag{5.11}
$$

**Proof.** At a finite place, elementary divisors identify the length of $Q$ with the colength
between the two determinant lattices. At an archimedean embedding, transporting the determinant
norm contributes the last term of (5.10). Summing gives (5.10), with the displayed sign.
Saturation makes $I$ admissible in the definition of maximal slope, and the determinant norm is
bounded by the exterior-power operator norm. This gives (5.11). $\square$

**Lemma 5.5 (finite Plucker criterion).** Let $T$ be a rank-$r$ Hermitian lattice. Suppose that
for each $1\leq k\leq r$ there are finitely many integral maps

$$
q_{k,\nu}:\mathop{\bigwedge}\nolimits^kT\longrightarrow M_{k,\nu}
$$

to Hermitian lines whose associated Plucker sections have no common zero on
$\operatorname{Gr}(k,T_L)$. If

$$
\widehat\deg\overline M_{k,\nu}
+\sum_\sigma\log\|q_{k,\nu,\sigma}\|
\leq kU[L:\mathbf Q],
\tag{5.12}
$$

then

$$
\widehat\mu_{\max}(\overline T)\leq U[L:\mathbf Q].
\tag{5.13}
$$

**Proof.** For a saturated rank-$k$ submodule $F\subset T$, the no-common-zero hypothesis
selects a $q_{k,\nu}$ nonzero on $\det F$. Apply Lemma 5.4 to the resulting map from the line
$\det F$ to $M_{k,\nu}$. Its finite saturation length is nonnegative, and (5.12) gives
$\widehat\deg\overline F\leq kU[L:\mathbf Q]$. Take the supremum. $\square$

The lemma is conditional on an actual Plucker frame. It does not validate an unspecified
family of multiplication minors merely because an ambient complex is exact.

### 5.5 The corrected conditional slope theorem

Assume $(\mathrm{SHB})$, followed by $(\mathrm{Tor})_{\mathscr C,N}$ and
$(\mathrm{HT})_{\mathscr C,N}$ on the relevant carrier locus. For a semistable moduli point
$x/L$, let $\overline\lambda_x$ be its metrized Hodge line. The package
$(\mathrm{SlopeFJ})_{\mathscr C,N}$ must supply a Hermitian line
$\overline{\mathscr D}_x$ whose finite lattice and archimedean metric are explicitly defined
and whose degree is

$$
B_x:=\widehat\deg\overline{\mathscr D}_x
=\sum_{w\nmid N,\rho}m_{w,\rho}\log Nw
+\sum_{w\mid N}\Delta_w(x)\log Nw
+\sum_{\sigma}\log(1+\operatorname{tr}Y_\sigma)
\geq0.
\tag{5.14}
$$

Here the $m_{w,\rho}$ are proved primitive boundary orders, and the $\Delta_w(x)$ are oriented
effective orders supplied by the actual determinant maps. They are not defined as symmetric
distances between two lattices.

The same package supplies fixed positive integers $a,b_0,b_1$, Hermitian lattices
$T_{0,x},T_{1,x}$, and nonzero integral maps

$$
\Phi_{0,x}:\overline{\mathscr D}_x^{b_0}\longrightarrow\overline T_{0,x},
\qquad
\Phi_{1,x}:\overline\lambda_x^a\otimes
\overline{\mathscr D}_x^{b_1}\longrightarrow\overline T_{1,x},
\tag{5.15}
$$

such that

$$
\sum_\sigma\log\|\Phi_{j,x,\sigma}\|
\leq V_j[L:\mathbf Q].
\tag{5.16}
$$

The word “integral” in (5.15) includes the oriented local assertion that the determinant vector
has the order inserted in its source at every $w\mid N$. This is a hypothesis to be verified
from the integral Fourier--Jacobi and level-prime calculation. It is not a consequence of an
absolute lattice length.

Finally, $(\mathrm{SlopeFJ})_{\mathscr C,N}$ supplies genuine Plucker frames for the
$T_{j,x}$ satisfying (5.12), with constants $U_j$ independent of $x$ and of the auxiliary
semistable field.

**Theorem 5.6 (conditional logarithmic slope bound).** Assuming the data just stated, one has

$$
\max\{\widehat\deg\overline\lambda_x,0\}+B_x
\leq C[L:\mathbf Q],
\tag{5.17}
$$

where $C$ depends only on the fixed carrier, level, and arithmetic data.

**Proof.** Put $d=\widehat\deg\overline\lambda_x$. Lemma 5.5 gives

$$
\widehat\mu_{\max}(\overline T_{j,x})\leq U_j[L:\mathbf Q].
$$

Apply Lemma 5.4 to the two maps (5.15), discard only their nonnegative saturation lengths, and
use (5.16). The result is

$$
b_0B_x\leq(U_0+V_0)[L:\mathbf Q],
\qquad
ad+b_1B_x\leq(U_1+V_1)[L:\mathbf Q].
\tag{5.18}
$$

If $d<0$, the first inequality bounds $B_x$. If $d\geq0$, then

$$
\min(a,b_1)(d+B_x)\leq ad+b_1B_x,
$$

and the second inequality bounds $d+B_x$. This proves (5.17). $\square$

The integral Hodge--theta comparison converts (5.17) directly into a height bound for the
stabilized point $x$ of $Z(B)$. Thus $(\mathrm{SHB})$ followed by the three packages of
Chapter 2 implies $(\mathrm{CMH})_{\mathscr C,N}$. If $(\mathrm{SHB})$ and the same packages
are supplied uniformly for every $g$-dimensional $A/K$ with good reduction outside $S$, they
imply $(\mathrm{FH})_{K,S,g}$.

### 5.6 From moduli height to Shafarevich finiteness

Fix a number field $K$, a finite set $S$ of finite places, and $g\geq1$. For every
$g$-dimensional $A/K$ with good reduction outside $S$, form the principally polarized
$8g$-dimensional variety $Z(A)$. Choose one fixed full level $N\geq3$ after passing to its level
field.

The degree of a level field is bounded by the order of one fixed finite symplectic similitude
group, and it is unramified outside $S$ and the primes dividing $N$. The bounded-ramification
field lemma proved in Book 41 gives only finitely many possible level fields.

The last step of the Northcott argument needs an integral, rather than merely rational,
direct-factor theorem. We prove the required form before using it.

**Direct-factor theorem.** Let $B/K$ be an abelian variety. Up to $K$-isomorphism, only
finitely many abelian varieties $A/K$ occur in product decompositions

$$
B\simeq_K A\times C.
$$

**Proof.** Put

$$
\Gamma=\operatorname{End}_K(B),
\qquad E=\Gamma\otimes_{\mathbf Z}\mathbf Q.
$$

Book 36 proves that $\Gamma$ is finite free over $\mathbf Z$ and that $E$ is semisimple. If
$B\simeq A\times C$, then

$$
P_A=\operatorname{Hom}_K(B,A)
$$

is a direct summand of the regular right $\Gamma$-module. This construction is fully faithful
on direct factors. Indeed, choose inclusion and projection maps $i_A,p_A$. For a right
$\Gamma$-linear map $\varphi:P_A\to P_{A'}$, put
$f=\varphi(p_A)i_A:A\to A'$. Every $h:B\to A$ satisfies $h=p_A(i_Ah)$, and therefore
$\varphi(h)=fh$. Thus an isomorphism $P_A\simeq P_{A'}$ gives an isomorphism $A\simeq A'$.

It remains to prove that the regular $\Gamma$-module has finitely many direct-summand types.
There are only finitely many rational types: the regular semisimple $E$-module has finitely many
simple constituents, and the multiplicity of each constituent in a summand is bounded by its
multiplicity in $E$. We use the following integral assertion.

For an order $\Gamma$ in a finite-dimensional semisimple $\mathbf Q$-algebra and a fixed
finite-dimensional right $E$-module $W$, there are only finitely many isomorphism classes of
$\Gamma$-lattices $P$ with $P\otimes\mathbf Q\simeq W$. First suppose $W$ is simple. Fix a
Euclidean norm on $W_{\mathbf R}$ and a $\mathbf Z$-basis of $\Gamma$. Simplicity implies that
$x\Gamma$ is a full lattice for every nonzero $x\in W$. Hadamard's inequality, applied to the
finitely many choices of a maximal independent subset of the vectors obtained from that basis,
gives

$$
\operatorname{covol}(x\Gamma)\leq C\|x\|^n,
\qquad n=\dim_{\mathbf R}W_{\mathbf R}.
\tag{5.19}
$$

Scale any $\Gamma$-lattice $P$ to covolume one and let $x$ be a shortest nonzero vector. Since
$x\Gamma\subseteq P$, equation (5.19) gives
$1\leq\operatorname{covol}(x\Gamma)\leq C\|x\|^n$. Hence the shortest-vector length is bounded
below uniformly. The elementary compactness theorem for covolume-one lattices now gives bases
whose vectors, after passage to a subsequence, converge to a basis. For completeness, choose a
shortest primitive vector, project to its orthogonal complement, and argue by induction on $n$;
the lower bound for the shortest vector and covolume one give uniform upper bounds for all basis
vectors, while the determinant remains one in the limit. In these convergent bases the matrices
of a fixed $\mathbf Z$-basis of $\Gamma$ are integral and converge. They are therefore eventually
constant. The corresponding lattices are isomorphic as $\Gamma$-modules. This proves the simple
case.

For general $W$, induct on its dimension. Choose a nonzero proper $E$-submodule $U$. For a
$\Gamma$-lattice $P\subset W$, both $P\cap U$ and $P/(P\cap U)$ are full lattices in $U$ and
$W/U$. Induction leaves finitely many possibilities for their isomorphism classes. For fixed
lattices $P_1,P_2$, the possible middle terms form
$\operatorname{Ext}^1_\Gamma(P_2,P_1)$. This group is finitely generated over $\mathbf Z$
from a finite presentation of $P_2$. After tensoring with $\mathbf Q$ it vanishes because $E$
is semisimple. It is therefore a finitely generated torsion group, hence finite. The induction
proves the integral assertion. Applying it to each of the finitely many rational summand types
proves the theorem. $\square$

**Theorem 5.7 (height implies Shafarevich).** Assume $(\mathrm{FH})_{K,S,g}$: over each of
those finitely many level fields, the projective heights of all stabilized levelled moduli points
are uniformly bounded. Then only finitely many $K$-isomorphism classes of $g$-dimensional
abelian varieties over $K$ have good reduction outside $S$.

**Proof.** On the fixed projective compactification, Northcott gives finitely many rational
moduli points over each level field. Fine level turns equality of points into isomorphism of the
levelled principally polarized varieties. Thus only finitely many stabilized polarized objects
occur over the finite list of level fields.

For one polarized object $(B,\lambda)$ over a finite Galois extension $M/K$, its polarized
automorphism group is finite. One way to see this is to use the Rosati involution $\dagger$:
polarized automorphisms satisfy $u^\dagger u=1$, and the Rosati trace form is positive definite
on the lattice $\operatorname{End}_M(B)$. A sphere meets a lattice in finitely many points.
The polarized $K$-forms of $(B,\lambda)$ inject into the nonabelian cohomology set of the finite
group $\operatorname{Gal}(M/K)$ with values in this finite automorphism group. Even the set of
all maps between the two finite groups is finite, so only finitely many forms occur. Forgetting
polarization leaves finitely many $K$-varieties $B$ which can occur as $Z(A)$.

The direct-factor theorem now recovers actual factors, not merely rational isogeny factors.
Since

$$
Z(A)=A\times\bigl(A^3\times(A^\vee)^4\bigr),
$$

every original $A$ is a factor of one of the finitely many possible stabilized varieties.
Taking the finite union over those varieties proves the theorem. $\square$

Every step of this proof follows the height bound. It does not use Tate semisimplicity or
Hom--Tate surjectivity.

### 5.7 Finite isogeny classes and stable lattices

**Proposition 5.8.** If $A$ and $B$ are isogenous abelian varieties over $K$, then $A$ has
good reduction at a finite place $v$ if and only if $B$ does.

**Proof.** If $A$ extends to an abelian scheme $\mathcal A$ over the local valuation ring, take
the schematic closure $\mathcal H$ of the isogeny kernel in a finite multiplication group
$\mathcal A[n]$. Its coordinate modules are torsion-free over the DVR and hence finite free, so
$\mathcal H$ is finite flat. The fppf quotient $\mathcal A/\mathcal H$ is an abelian scheme and
has generic fiber $B$. A quasi-inverse isogeny proves the converse. $\square$

Under the conditional conclusion of Theorem 5.7, every member of the $K$-isogeny class of a
fixed $A$ has the same dimension and is good outside the finite bad-reduction set of $A$.
Shafarevich finiteness therefore gives:

**Corollary 5.9 (conditional finite isogeny class).** Let $S_A$ be the bad-reduction set of
$A$. Assuming $(\mathrm{FH})_{K,S_A,\dim A}$, the $K$-isogeny class of $A$ contains only
finitely many $K$-isomorphism classes.

Fix a prime $\ell$ and write

$$
T=T_\ell A,
\qquad V=V_\ell A.
$$

**Proposition 5.10 (stable lattices are isogeny quotients).** If the $K$-isogeny class of $A$
contains only finitely many $K$-isomorphism classes, then $V$ contains only finitely many
isomorphism classes of full $G_K$-stable $\mathbf Z_\ell$-lattices.

**Proof.** There is a canonical $G_K$-equivariant identification

$$
V/T\simeq A[\ell^\infty](\overline K).
\tag{5.20}
$$

Let $L\subset V$ be a full stable lattice. Replacing it by a homothetic lattice does not change
its abstract $G_K$-module type, so arrange

$$
T\subseteq L\subseteq\ell^{-n}T.
$$

Then $H=L/T$ is a finite $G_K$-stable subgroup of the right side of (5.20). In characteristic
zero it descends to a finite etale $K$-subgroup scheme of $A$. Form the quotient

$$
q_H:A\longrightarrow A_H=A/H.
$$

After identifying $V_\ell A_H$ with $V$ through the inverse of $V_\ell(q_H)$, a vector belongs
to $T_\ell A_H$ exactly when its class modulo $T$ lies in $H$. Thus the pulled-back Tate lattice
is precisely $L$. Only finitely many $K$-isomorphism classes of $A_H$ occur, and isomorphic
abelian varieties have isomorphic Tate lattices. $\square$

### 5.8 The lattice criterion and Tate semisimplicity

The final implication is representation-theoretic and unconditional.

**Lemma 5.11 (Tate's lattice criterion).** Let $k$ be a characteristic-zero nonarchimedean
local field with valuation ring $\mathcal O$. Let $G$ be a group and let $V$ be a
finite-dimensional $k$-representation with a stable lattice. If only finitely many isomorphism
classes of full $G$-stable $\mathcal O$-lattices occur in $V$, then $V$ is semisimple.

**Proof.** Let $R\subset\operatorname{End}_k(V)$ be the finite-dimensional algebra generated by
the image of $G$, and let $J=\operatorname{rad}R$. Because $R$ acts faithfully on $V$, the
module $V$ is semisimple if and only if $J=0$.

Suppose $J\ne0$. Choose $a\geq2$ minimal with $J^a=0$, and put

$$
W=J^{a-1}V\ne0.
$$

Fix a stable lattice $T$. Let $\Lambda$ be the image of $\mathcal O[G]$ in
$\operatorname{End}_{\mathcal O}(T)$, put

$$
I=\Lambda\cap J^{a-1},
\qquad X=T\cap W,
$$

and let $\varpi$ be a uniformizer. The ideal $I$ spans $J^{a-1}$ over $k$, so $IT$ is a full
lattice in $W$. Minimality of $a$ gives $IW=0$. For $n\geq0$, define

$$
T_n=T+\varpi^{-n}X.
$$

Every $T_n$ is a full $\Lambda$-stable lattice, and

$$
T_n\cap W=\varpi^{-n}X,
\qquad IT_n=IT.
$$

Therefore

$$
\delta(T_n)=\operatorname{length}_{\mathcal O}
\frac{T_n\cap W}{IT_n}
=n\dim_kW+\delta(T_0).
\tag{5.21}
$$

A $G$-linear lattice isomorphism extends $k$-linearly and commutes with $R$. It therefore
preserves the intrinsic subspace $W$, the ideal action of $I$, and the length (5.21). The
lattices $T_n$ are pairwise nonisomorphic, contradicting the hypothesis. Hence $J=0$ and $V$ is
semisimple. $\square$

Combining Proposition 5.10 and Lemma 5.11 gives the exact honest endpoint.

**Theorem 5.12 (Tate semisimplicity from isogeny finiteness).** If the $K$-isogeny class of
$A$ contains only finitely many $K$-isomorphism classes, then, for every rational prime $\ell$,

$$
V_\ell A
$$

is a semisimple $\mathbf Q_\ell[G_K]$-module. In particular the conclusion follows from
$(\mathrm{FH})_{K,S_A,\dim A}$, where $S_A$ is the bad-reduction set of $A$.

**Proof.** Proposition 5.10 supplies finitely many stable lattice types and Lemma 5.11 proves
semisimplicity. For the final assertion, Theorem 5.7 and Proposition 5.8 give finiteness of the
$K$-isogeny class. $\square$

### 5.9 The FLT carrier endpoint

We finally return to the finite carrier array $\mathscr C$ of (2.1). The following theorem is
the precise export needed by the later curve-carrier arguments.

**Theorem 5.13 (conditional carrier semisimplicity).** If
$(\mathrm{CMH})_{\mathscr C,N}$ holds, then for every $i$ and every prime $\ell$,

$$
V_\ell J_i
\quad\text{and}\quad
H^1_{\mathrm{et}}(C_{i,\overline K_i},\mathbf Q_\ell)
$$

are semisimple $\mathbf Q_\ell[G_{K_i}]$-modules, where $C_i$ is the smooth projective carrier
curve with Jacobian $J_i$.

**Proof.** Let $S_i$ be the bad-reduction set of $J_i$. Proposition 5.8 shows that every
$B\in\mathscr I_i$ has the same dimension as $J_i$ and has good reduction outside $S_i$.
The bounded-level-field argument in Section 5.6 therefore gives only finitely many level fields
for all $Z(B)$ with $B\in\mathscr I_i$. The hypothesis
$(\mathrm{CMH})_{\mathscr C,N}$ and Northcott give finitely many stabilized levelled moduli
points. Polarized descent gives finitely many possible $K_i$-varieties $Z(B)$, and the
direct-factor theorem gives finitely many possibilities for $B$ because $B$ is an actual factor
of $Z(B)$. Thus $(\mathrm{IF})_{J_i/K_i}$ holds.

Proposition 5.10 now gives finitely many stable lattice types in $V_\ell J_i$, and Lemma 5.11
gives its semisimplicity. With the convention of Book 36 one has
$H^1_{\mathrm{et}}(C_{i,\overline K_i},\mathbf Q_\ell)\simeq V_\ell J_i(-1)$.
Character twists preserve semisimplicity, proving the cohomological assertion.
$\square$

Combining Theorem 5.13 with Section 5.5 gives the exact conditional FLT chain

$$
\begin{gathered}
(\mathrm{SHB})
\Longrightarrow
\{\text{stable-height field-independence}\},\\
[(\mathrm{SHB})
+(\mathrm{Tor})_{\mathscr C,N}
+(\mathrm{HT})_{\mathscr C,N}
+(\mathrm{SlopeFJ})_{\mathscr C,N}]
\Longrightarrow
(\mathrm{CMH})_{\mathscr C,N}
\Longrightarrow
\text{carrier-Jacobian and carrier-}H^1\text{ semisimplicity}.
\end{gathered}
\tag{5.22}
$$

If $(\mathrm{CMH})_{\mathscr C,N}$ is proved directly, its downstream arrow remains valid
without $(\mathrm{SHB})$. No Hom--Tate surjectivity or algebraization of a formal invariant
tensor is used in this chain.

## 6. Conclusion

The proved portions of the Faltings--Tate route are now separated from its hypotheses. A single
fixed torsion field gives global semistability. Hermitian determinant and saturation, finite
Plucker slope control, Northcott and polarized descent, integral direct-factor cancellation,
isogeny quotients of stable lattices, and the Jacobson-radical criterion form a continuous proved
argument once the corresponding direct moduli-height or isogeny-finiteness input is supplied.

The first unresolved input in the Faltings-height source chain is $(\mathrm{SHB})$: Book 60's
analytic base-change compatibility after admissible modification is not a formal-identity or
Neron-cotangent theorem, Book 38 warns that ramified Neron base change need not preserve the
model, and Book 41 leaves the cotangent comparison conditional. Stable Faltings height is
field-independent here only subject to $(\mathrm{SHB})$. After that gate, the actual FLT
carrier-isogeny loci still need the restricted arithmetic Siegel toroidal construction, the
integral metrized Hodge--theta comparison, and the oriented logarithmic
determinant/Fourier--Jacobi package. Completion does not algebraize arbitrary tensors over an
etale neighborhood, and ramified Galois conjugates do not constitute fpqc descent.

Accordingly, the package route to $(\mathrm{CMH})_{\mathscr C,N}$ is not ready: it is
conditional on $(\mathrm{SHB})$ and all three carrier packages. A direct proof of
$(\mathrm{CMH})_{\mathscr C,N}$ would still activate the proved descent, direct-factor,
stable-lattice, and semisimplicity chain without those inputs. No unconditional
Shafarevich-finiteness or Tate-semisimplicity claim is made here.
