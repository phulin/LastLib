# Coherent Cohomology in Proper Families

## Contents

1. [The questions asked by a family](#1-the-questions-asked-by-a-family)
   - [Fibers are not the whole family](#11-fibers-are-not-the-whole-family)
   - [Standing language and hypotheses](#12-standing-language-and-hypotheses)
   - [The base-change map](#13-the-base-change-map)
   - [Three warnings](#14-three-warnings)
2. [Finite complexes behind projective cohomology](#2-finite-complexes-behind-projective-cohomology)
   - [Why one complex should govern every fiber](#21-why-one-complex-should-govern-every-fiber)
   - [The projective-space calculation](#22-the-projective-space-calculation)
   - [Finite-complex theorem](#23-finite-complex-theorem)
   - [From projective to proper](#24-from-projective-to-proper)
3. [Finiteness for proper morphisms](#3-finiteness-for-proper-morphisms)
   - [Coherence of higher direct images](#31-coherence-of-higher-direct-images)
   - [Vanishing bounds and cohomological dimension](#32-vanishing-bounds-and-cohomological-dimension)
   - [Projection and composition](#33-projection-and-composition)
   - [Why properness and coherence matter](#34-why-properness-and-coherence-matter)
4. [Upper semicontinuity](#4-upper-semicontinuity)
   - [The rank of fiber cohomology](#41-the-rank-of-fiber-cohomology)
   - [The semicontinuity theorem](#42-the-semicontinuity-theorem)
   - [Euler characteristics in flat families](#43-euler-characteristics-in-flat-families)
   - [Jumping examples](#44-jumping-examples)
5. [Cohomology and base change](#5-cohomology-and-base-change)
   - [A local normal form](#51-a-local-normal-form)
   - [The exact criterion](#52-the-exact-criterion)
   - [Flat and arbitrary change of base](#53-flat-and-arbitrary-change-of-base)
   - [Local freeness and constant fiber dimension](#54-local-freeness-and-constant-fiber-dimension)
   - [Curves as a two-degree case](#55-curves-as-a-two-degree-case)
6. [Flatness, Hilbert polynomials, and flattening](#6-flatness-hilbert-polynomials-and-flattening)
   - [The cohomological meaning of a Hilbert polynomial](#61-the-cohomological-meaning-of-a-hilbert-polynomial)
   - [Constancy and the converse](#62-constancy-and-the-converse)
   - [Flattening strata](#63-flattening-strata)
   - [Uniform generation and embeddings](#64-uniform-generation-and-embeddings)
7. [Formal functions](#7-formal-functions)
   - [Infinitesimal neighborhoods remember completion](#71-infinitesimal-neighborhoods-remember-completion)
   - [The theorem on formal functions](#72-the-theorem-on-formal-functions)
   - [Proof by Artin--Rees and pro-systems](#73-proof-by-artin--rees-and-pro-systems)
   - [Consequences and limitations](#74-consequences-and-limitations)
8. [Completion and coherent passages](#8-completion-and-coherent-passages)
   - [Ordinary and derived completion](#81-ordinary-and-derived-completion)
   - [Completed base change](#82-completed-base-change)
   - [Lifting sections through thickenings](#83-lifting-sections-through-thickenings)
   - [What is not yet algebraization](#84-what-is-not-yet-algebraization)
9. [Duality interfaces in relative dimension one](#9-duality-interfaces-in-relative-dimension-one)
   - [Trace and the relative dualizing line](#91-trace-and-the-relative-dualizing-line)
   - [Perfect pairings for smooth proper curves](#92-perfect-pairings-for-smooth-proper-curves)
   - [Base change and the Hodge bundle](#93-base-change-and-the-hodge-bundle)
   - [Nodal and Gorenstein curves](#94-nodal-and-gorenstein-curves)
10. [Proper curves and Picard representability](#10-proper-curves-and-picard-representability)

- [The relative Picard functor](#101-the-relative-picard-functor)
- [Divisors provide finite-dimensional charts](#102-divisors-provide-finite-dimensional-charts)
- [The Picard scheme of a smooth proper curve](#103-the-picard-scheme-of-a-smooth-proper-curve)
- [Tangent spaces, smoothness, and the Jacobian](#104-tangent-spaces-smoothness-and-the-jacobian)

11. [Abelian schemes and their coherent cohomology](#11-abelian-schemes-and-their-coherent-cohomology)

- [Invariant differentials](#111-invariant-differentials)
- [The dual abelian scheme](#112-the-dual-abelian-scheme)
- [The exterior algebra theorem](#113-the-exterior-algebra-theorem)
- [Polarizations and base change](#114-polarizations-and-base-change)

12. [Hodge bundles in low-dimensional PEL families](#12-hodge-bundles-in-low-dimensional-pel-families)

- [What is assumed and what is proved](#121-what-is-assumed-and-what-is-proved)
- [Endomorphisms and decompositions](#122-endomorphisms-and-decompositions)
- [Determinants, ranks, and bad primes](#123-determinants-ranks-and-bad-primes)
- [Compactifications and boundary behavior](#124-compactifications-and-boundary-behavior)

13. [Integral modular forms as coherent sections](#13-integral-modular-forms-as-coherent-sections)

- [The geometric definition](#131-the-geometric-definition)
- [Finiteness and change of coefficients](#132-finiteness-and-change-of-coefficients)
- [Cusp forms and the boundary](#133-cusp-forms-and-the-boundary)
- [The exact base-change test](#134-the-exact-base-change-test)

14. [Representability consequences and their boundary](#14-representability-consequences-and-their-boundary)

- [A coherent representability package](#141-a-coherent-representability-package)
- [Curves, abelian schemes, and PEL data](#142-curves-abelian-schemes-and-pel-data)
- [Failures when hypotheses are weakened](#143-failures-when-hypotheses-are-weakened)

15. [Synthesis](#15-synthesis)

- [The chain of implications](#151-the-chain-of-implications)
- [A theorem checklist for later use](#152-a-theorem-checklist-for-later-use)
- [Conclusion](#153-conclusion)

## 1. The questions asked by a family

### 1.1 Fibers are not the whole family

A proper scheme over a field has finite-dimensional coherent cohomology. In a family, that familiar statement divides into several different questions. Are the cohomology groups of every fiber finite? Do their dimensions vary predictably? Is there a coherent sheaf on the base whose fiber is the cohomology of the geometric fiber? Does that sheaf survive extension of scalars? What can infinitesimal neighborhoods of one fiber tell us about the completed family?

The answers are related but not interchangeable. A single finite complex on the base is the organizing object. Its cohomology gives higher direct images; tensoring it with a residue field gives fiber cohomology; ranks of its differentials give semicontinuity; tensoring with quotient rings gives infinitesimal cohomology; and completion turns the resulting inverse system into the theorem on formal functions. The point of this book is to build that complex, explain exactly when it exists, and then extract each geometric consequence without hiding a flatness or finiteness assumption.

There is also a moduli-theoretic reason for caring. A line bundle in a proper family is controlled infinitesimally by $H^1(\mathcal O)$ and obstructed in $H^2(\mathcal O)$. Differentials on an abelian scheme form a vector bundle only because coherent base change works. Integral modular forms are sections of powers of such a bundle; their finiteness and reduction properties are therefore cohomological statements. Thus coherent cohomology is not an invariant added after a family has been constructed. It is one of the mechanisms that makes families representable and arithmetic sections controllable.

### 1.2 Standing language and hypotheses

All schemes are schemes in the ordinary sense. A scheme is **locally noetherian** when it has an affine cover by spectra of noetherian rings, and **noetherian** when it is also quasi-compact. A morphism is **proper** when it is separated, of finite type, and universally closed. Over a locally noetherian base, a finite-type morphism is finitely presented. We nevertheless say “finitely presented” when that property is the one used, especially in base-change statements that remain meaningful beyond noetherian schemes.

For $f:X\to S$ and a quasi-coherent sheaf $\mathcal F$, write

$$
R^if_*\mathcal F
$$

for the $i$th higher direct image in the Zariski topology. Its restriction to an open $U\subseteq S$ is the sheaf associated with $H^i(X_U,\mathcal F|_{X_U})$ when $U$ is affine and the usual comparison hypotheses hold. For a point $s\in S$, write

$$
X_s=X\times_S\operatorname{Spec}\kappa(s),
\qquad \mathcal F_s=\mathcal F\otimes_{\mathcal O_S}\kappa(s).
$$

The last tensor is ordinary when $\mathcal F$ is flat over $S$. Without flatness, the correct fiber of a complex uses derived tensor, and Tor terms can alter cohomology.

A coherent sheaf $\mathcal F$ on $X$ is **flat over $S$** if every stalk $\mathcal F_x$ is flat over $\mathcal O_{S,f(x)}$. This is not the same as being locally free on $X$. For example, the structure sheaf of any flat finitely presented family is flat over the base even when the total space is singular.

The main finiteness and formal-functions theorems use a proper morphism between locally noetherian schemes and a coherent sheaf. The sharp semicontinuity and exact base-change criteria add flatness of $\mathcal F$ over $S$. Whenever we pass to an arbitrary nonnoetherian base, we explicitly replace coherence by finite presentation and add the needed perfectness or boundedness hypothesis.

### 1.3 The base-change map

Given a cartesian square

$$
\begin{array}{ccc}
X_T&\xrightarrow{g'}&X\\
\downarrow f_T&&\downarrow f\\
T&\xrightarrow{g}&S,
\end{array}
$$

adjunction gives a canonical morphism

$$
Lg^*Rf_*\mathcal F\longrightarrow
Rf_{T*}Lg'^*\mathcal F.
$$

Taking degree $i$ and suppressing higher Tor produces, under flatness in the appropriate place, the familiar map

$$
g^*R^if_*\mathcal F\longrightarrow
R^if_{T*}\mathcal F_T.
$$

For $T=\operatorname{Spec}\kappa(s)$ it induces

$$
\beta_s^i:(R^if_*\mathcal F)\otimes\kappa(s)\longrightarrow
H^i(X_s,\mathcal F_s).
$$

The map always exists in its derived form. Properness makes both sides finite; flatness and vanishing determine when the displayed underived map is an isomorphism. This separation between existence and invertibility will prevent several common mistakes.

### 1.4 Three warnings

First, properness cannot be replaced by “all fibers are proper.” A family can fail to be universally closed even if its visible fibers look complete, and then sections may escape in a varying direction. Finiteness is a global assertion about the map.

Second, finite-dimensional fibers do not imply that $R^if_*\mathcal F$ is locally free. On an elliptic curve $E$ over a field, let $\mathcal P$ be a Poincaré line bundle on $E\times E$, with the second factor as base. For a nontrivial degree-zero line bundle $L$, both $H^0(E,L)$ and $H^1(E,L)$ vanish; at the identity, both dimensions are one. In fact the degree-zero direct image is zero and the degree-one direct image is supported at the identity. Thus the latter is torsion rather than a vector bundle, and degree-zero base change fails at the identity.

Third, an isomorphism after every residue-field extension need not by itself give arbitrary base change unless the relevant objects are finitely presented and Tor is controlled. Nilpotent thickenings see relations invisible at points. Exact criteria must be formulated using a finite complex, not only geometric fibers.

## 2. Finite complexes behind projective cohomology

### 2.1 Why one complex should govern every fiber

Let $A$ be noetherian, $X$ projective over $A$, and $\mathcal F$ coherent and $A$-flat. One wants a bounded complex $K^\bullet$ of finite free $A$-modules such that for every $A$-module $M$,

$$
H^i(K^\bullet\otimes_A M)
\simeq H^i(X,\mathcal F\otimes_A M).
$$

This is stronger than merely saying each cohomology module is finite. It says all coefficient changes are governed by the same matrices. The strength is exactly what semicontinuity and base change require.

The construction begins with a projective embedding and the standard affine cover. A Čech complex directly computes cohomology because finite intersections are affine, but its terms are generally large localizations, not finite $A$-modules. Positive twists and finite resolutions replace that large complex, in any fixed cohomological range, by a bounded finite one. Flatness over $A$ ensures that tensoring with $M$ preserves the resolutions used in this replacement.

### 2.2 The projective-space calculation

On $\mathbf P^r_A$, cover by $D_+(x_0),\ldots,D_+(x_r)$. The alternating Čech complex of $\mathcal O(n)$ splits into subcomplexes indexed by Laurent monomials. A monomial whose negative exponents occur in a proper nonempty subset of the variables contributes a simplex complex and is acyclic. The survivors give

$$
H^q(\mathbf P^r_A,\mathcal O(n))=0
\quad(0<q<r),
$$

and

$$
H^0(\mathbf P^r_A,\mathcal O(n))
=A[x_0,\ldots,x_r]_n\quad(n\geq0).
$$

Top cohomology is generated by monomials in which every exponent is negative; in particular it is finite free in every degree. The entire calculation commutes with tensoring $A\to B$, because its monomial summands and differentials are defined over the integers.

If $i:X\hookrightarrow\mathbf P^r_A$ is closed, then $H^q(X,\mathcal F)=H^q(\mathbf P^r_A,i_*\mathcal F)$. A coherent sheaf on projective space has, after choosing sufficiently many twists, a finite beginning of a resolution by finite sums of $\mathcal O(-n)$. To compute degrees at most $N$, continue the resolution through $N+r+1$ steps. The unused tail contributes only above the range, because projective space has cohomological dimension $r$. Replacing every twist by its explicit Čech complex yields a bounded double complex of finite free $A$-modules in the required range.

### 2.3 Finite-complex theorem

**Finite-complex theorem.** Let $A$ be noetherian, let $f:X\to\operatorname{Spec}A$ be projective, and let $\mathcal F$ be coherent and flat over $A$. There is a bounded complex $K^\bullet$ of finite projective $A$-modules, concentrated in degrees $0$ through some fixed bound, and functorial isomorphisms

$$
H^i(K^\bullet\otimes_A M)
\simeq H^i(X,\mathcal F\otimes_A M)
$$

for every $A$-module $M$ and every $i$. On an open neighborhood of any point of a locally noetherian base, the analogous statement holds for a projective finitely presented morphism.

**Proof.** Embed $X$ into projective space. Choose a finite graded presentation of the module corresponding to $i_*\mathcal F$ and successively resolve its kernels by finite sums of graded free modules. Sheafification gives a resolution by sums of twists. Since the standard Čech cover is acyclic for quasi-coherent sheaves, the total Čech complex computes cohomology. The projective-space calculation replaces the terms outside a finite strip by acyclic finite complexes. Truncate after more than $r$ syzygies; dimension shifting shows that the remaining tail has no effect in any degree.

Every construction so far commutes with tensoring if the sheaf resolution stays exact. The $A$-flatness of $\mathcal F$, together with flatness of the twists, makes each successive kernel $A$-flat. Hence tensoring by an arbitrary $M$ preserves the resolution. The resulting bounded complex has finite flat terms. Over a noetherian ring, finitely presented flat modules are projective. A finite projective module need not be free on all of $\operatorname{Spec}A$, so this is the correct global statement; after restricting to a sufficiently small affine neighborhood, every term is finite free. Removing contractible summands puts the complex in nonnegative degrees because coherent cohomology has no negative degrees. The same argument on affine opens proves the local assertion over a scheme. $\square$

The theorem is often called a theorem of finite presentation for cohomology. Its decisive feature is universality in $M$. Without $A$-flatness of $\mathcal F$, one still obtains a pseudo-coherent model for derived coefficient change, but it need not have finite Tor amplitude over $A$, and ordinary tensor with $\mathcal F$ no longer describes every fiber.

### 2.4 From projective to proper

Not every proper morphism is projective. Finiteness must therefore be detached from the chosen embedding. The bridge is a projective modification and noetherian induction. The modification is produced by Chow's lemma, which we prove in full because later books invoke exactly this statement.

**Chow's lemma.** Let $S$ be noetherian and let $f:X\to S$ be separated and of finite type. Assume that $X$ is covered by finitely many open subschemes that are quasi-projective over $S$; this is automatic when $S$ is affine, which is the only case used below. Then there is an $S$-morphism $p:X'\to X$ with the following properties.

1. $p$ is projective and surjective.
2. There is a dense open $V\subseteq X$, necessarily containing every generic point of $X$, such that $p^{-1}(V)\to V$ is an isomorphism.
3. There is an immersion $X'\hookrightarrow\mathbf P^N_S$ over $S$ for some $N$. If $f$ is proper, then $X'\to S$ is proper and that immersion is closed, so $X'\to S$ is projective.

**Proof.** We first reduce to an irreducible $X$; no reducedness will be assumed anywhere. Let $X_1,\ldots,X_m$ be the irreducible components of the noetherian space $X$, and for each $k$ let $V_k=X\setminus\bigcup_{l\neq k}X_l$, a nonempty open subscheme of $X$ whose space lies in $X_k$. Let $X_k^\sharp\subseteq X$ be the scheme-theoretic closure of $V_k$, a closed subscheme with underlying space $X_k$; it is separated and of finite type over $S$, proper over $S$ when $f$ is, and its intersections with the given cover are closed subschemes of quasi-projective $S$-schemes, hence quasi-projective over $S$ by the permanence properties of Book 8. Restricting a scheme-theoretic closure to an open subscheme computes the closure there, so $X_k^\sharp$ induces on $V_k$ its original structure. Granting the lemma for irreducible schemes, choose $p_k:X_k'\to X_k^\sharp$ and a dense open $W_k\subseteq X_k^\sharp$ over which $p_k$ is an isomorphism, and put $V_k'=W_k\cap V_k$, a nonempty open of $X$. Let $X'=\coprod_kX_k'$ with $p$ the disjoint union of the composites $X_k'\to X_k^\sharp\hookrightarrow X$ and let $V=\bigcup_kV_k'$; the $V_k'$ are pairwise disjoint because $V_k\cap V_l=\varnothing$ for $k\neq l$, and $V$ is dense because it meets every component. Since $p_l$ has image $X_l$, which misses $V_k'$ for $l\neq k$, the preimage of $V_k'$ is $p_k^{-1}(V_k')\simeq V_k'$, so $p^{-1}(V)\to V$ is an isomorphism, and $p$ is surjective because the $X_k$ cover $X$. A finite disjoint union of projective, respectively quasi-projective, schemes over a base is again such: embed the pieces in one $\mathbf P^N$ over that base and place $m$ copies of $\mathbf P^N$ as pairwise disjoint linear subspaces of $\mathbf P^{m(N+1)-1}$, so that the images have pairwise disjoint closures and their union is closed in a single open subscheme. This gives the three assertions for $X$ from the same assertions for the $X_k^\sharp$.

So let $X$ be irreducible. Choose nonempty opens $U_1,\ldots,U_r$ covering $X$, each quasi-projective over $S$, and for each $i$ an immersion $\phi_i:U_i\to P_i=\mathbf P^{n_i}_S$ together with an open $A_i\subseteq P_i$ in which $\phi_i$ is a closed immersion. When $S=\operatorname{Spec}A$ is affine one takes the $U_i$ affine; a finite set of algebra generators of $\mathcal O(U_i)$ over $A$ then gives a closed immersion into $A_i=\mathbf A^{n_i}_S\subseteq P_i$. Put $P=P_1\times_S\cdots\times_SP_r$ and $U=\bigcap_iU_i$, which is nonempty and dense because $X$ is irreducible, and quasi-compact because $X$ is separated. Let

$$
j=(\iota,\phi_1|_U,\ldots,\phi_r|_U):U\longrightarrow X\times_SP
$$

with $\iota$ the inclusion, and let $X'$ be the scheme-theoretic image of $j$, that is, the smallest closed subscheme of $X\times_SP$ through which $j$ factors. Since $j$ is quasi-compact, this closure may be computed on any open subscheme of $X\times_SP$, and $U$ is schematically dense in $X'$: no closed subscheme of an open $Y\subseteq X'$ other than $Y$ contains $U\cap Y$. Write $p:X'\to X$ and $q:X'\to P$ for the two projections and $q_i$ for the $i$th component of $q$.

The morphism $X\times_SP\to X$ is proper, being a base change of $P\to S$, and the Segre immersion of Book 8 makes $P$ a closed subscheme of $\mathbf P^N_S$ with $N=\prod_i(n_i+1)-1$. Hence $X'$ is a closed subscheme of $\mathbf P^N_X$ and $p$ is projective. Over $U$ it is an isomorphism: the graph of $(\phi_i|_U)_i$ is a closed subscheme of $U\times_SP$ isomorphic to $U$, because $P$ is separated over $S$, and $X'\cap(U\times_SP)$ is the scheme-theoretic closure of $U$ inside that open subscheme, hence is exactly this graph. Being proper, $p$ is closed, and its image contains the dense $U$, so $p$ is surjective. This proves the first two assertions with $V=U$.

The crux is that $q$ is an immersion. Fix $i$ and let $\Gamma_i\subseteq X\times_SP_i$ be the image of $(\iota_i,\phi_i):U_i\to X\times_SP_i$, where $\iota_i$ is the inclusion of $U_i$. It is an immersion, since its composite with the projection to $X$ is an open immersion and that projection is separated. It is closed in $U_i\times_SP_i$, being the graph of a morphism to a scheme separated over $S$. It is also closed in $X\times_SA_i$: the composite $\Gamma_i\to X\times_SA_i\to A_i$ is the closed immersion $\phi_i$ and in particular proper, while $X\times_SA_i\to A_i$ is separated because $X\to S$ is, so cancellation makes $\Gamma_i\to X\times_SA_i$ proper, and a proper immersion is a closed immersion. Closedness is local on the target, so $\Gamma_i$ is a closed subscheme of the open subscheme

$$
C_i=(U_i\times_SP_i)\cup(X\times_SA_i)\subseteq X\times_SP_i.
$$

The second closedness statement carries the geometric content of the argument: a point of $X'$ whose $i$th coordinate stays inside the affine chart $A_i$ cannot have escaped from $U_i$, precisely because $U_i$ was made closed in $A_i$. Only separatedness of $X$ over $S$ is used for it.

Apply this to $(p,q_i):X'\to X\times_SP_i$. The preimage of $U_i\times_SP_i$ is the open $X_i'=p^{-1}(U_i)$, the preimage of $X\times_SA_i$ is the open $Y_i=q_i^{-1}(A_i)$, and the preimage of $C_i$ is $X_i'\cup Y_i$, which contains $U$. On $U$ the morphism $(p,q_i)$ is $(\iota_i,\phi_i)|_U$ and therefore factors through $\Gamma_i$. Its preimage is a closed subscheme of $X_i'\cup Y_i$ containing $U$, so by schematic density it is all of $X_i'\cup Y_i$. Composing with the two projections of $\Gamma_i\simeq U_i$ now gives $p(X_i'\cup Y_i)\subseteq U_i$ and $q_i(X_i'\cup Y_i)\subseteq A_i$, whence

$$
X_i'=p^{-1}(U_i)=q_i^{-1}(A_i)=Y_i,
$$

and on this open subscheme $(p,q_i)$ factors through $\Gamma_i$, that is, $q_i=\phi_i\circ p$ there.

Let $\Omega_i\subseteq P$ be the preimage of $A_i$ under the $i$th projection and let $G_i\subseteq X\times_S\Omega_i$ be the preimage of $\Gamma_i$ under $X\times_S\Omega_i\to X\times_SA_i$, a closed subscheme whose projection $G_i\to\Omega_i$ is a closed immersion, being the base change of the closed immersion $\Gamma_i\to A_i$ along $\Omega_i\to A_i$. The displayed equality gives $q^{-1}(\Omega_i)=X_i'$, so $X_i'=X'\cap(X\times_S\Omega_i)$ is closed in $X\times_S\Omega_i$, and the factorization through $\Gamma_i$ places it inside $G_i$. Hence $X_i'$ is a closed subscheme of $G_i$ and $q$ restricts to a closed immersion $X_i'\to\Omega_i$. The opens $X_i'$ cover $X'$ because the $U_i$ cover $X$, so $q$ maps $X'$ into the open subscheme $\Omega=\bigcup_i\Omega_i$ and $q^{-1}(\Omega_i)\to\Omega_i$ is a closed immersion for every $i$. Being a closed immersion is local on the target, so $X'\to\Omega$ is a closed immersion and $q:X'\to P$ is an immersion. Composing with Segre gives an immersion $X'\to\mathbf P^N_S$.

Finally suppose $f$ is proper. Then $X'\to S$ is proper, being the composite of the proper morphisms $p$ and $f$; since $P\to S$ is separated, cancellation makes $q$ proper, and a proper immersion is a closed immersion. Thus $X'$ is a closed subscheme of $\mathbf P^N_S$ and $X'\to S$ is projective. $\square$

The construction cannot be simplified to a single chart. Taking one dense affine open $U_1\subseteq X$ and closing up its graph in $X\times_S\mathbf P^{n_1}_S$ does produce a scheme projective over $X$ and proper over $S$, but its projection to $\mathbf P^{n_1}_S$ need not be an immersion, since points of $X\setminus U_1$ can contribute positive-dimensional fibers over the hyperplane at infinity. Projectivity over $S$ is exactly what the induction below consumes, so the full cover, with one projective factor for each chart, is needed.

**Proper reduction lemma.** Let $f:X\to S$ be proper with $S$ noetherian. There is a projective surjection $p:X'\to X$ with $X'\to S$ projective and an ideal $\mathcal J\subseteq\mathcal O_X$ whose zero set omits every generic point of $X$, such that, for each coherent $\mathcal F$, after replacing $\mathcal J$ by a power the map

$$
\mathcal J\mathcal F\longrightarrow
p_*p^*(\mathcal J\mathcal F)
$$

is injective.

**Proof.** The assertion is local on $S$, so first take $S$ affine. Every affine open of $X$ is then of finite type over an affine base, hence quasi-projective over $S$, and Chow's lemma applies: it gives a projective surjection $p:X'\to X$ with $X'\to S$ projective, together with a dense open $V\subseteq X$ over which $p$ is an isomorphism. Let $\mathcal J$ be the ideal of the reduced closed complement of $V$; its zero set omits every generic point because $V$ is dense. Direct image commutes with restriction to an open subscheme of the target, so the kernel $\mathcal K$ of $\mathcal F\to p_*p^*\mathcal F$ restricts to zero on $V$; being coherent, it is killed by a power of $\mathcal J$. Artin--Rees gives, for one $c$ and all large $n$,

$$
\mathcal K\cap\mathcal J^n\mathcal F
=\mathcal J^{n-c}(\mathcal K\cap\mathcal J^c\mathcal F)=0.
$$

Thus the composite $\mathcal J^n\mathcal F\to p_*p^*\mathcal F$ is injective. It factors through $p_*p^*(\mathcal J^n\mathcal F)$, so the first map in that factorization is injective as asserted. Quasi-compactness gives one exponent on $X$. $\square$

Its cokernel and $\mathcal F/\mathcal J\mathcal F$ are supported on a closed subset containing no generic point. The map $p$ is projective, so its higher direct images of coherent sheaves are coherent by the projective case. The spectral sequence

$$
H^a(X,R^bp_*\mathcal G)\Longrightarrow H^{a+b}(X',\mathcal G)
$$

then compares cohomology upstairs with cohomology of these sheaves downstairs. For $b>0$ they vanish over $V$, hence have smaller support. The two long exact sequences associated with the injection and its cokernel reduce any assertion stable under extensions to the projective composite $X'\to S$ and to coherent sheaves supported on a proper closed subset. Noetherian induction terminates.

For base change one needs a stronger conclusion, and the flatness hypothesis supplies it.

**Proper cohomology-complex theorem.** Let $f:X\to S$ be proper and finitely presented with $S$ locally noetherian, and let $\mathcal F$ be coherent and flat over $S$. Zariski-locally on $S$, there is a bounded complex $K^\bullet$ of finite free modules such that, for every module $M$ over the chosen affine open,

$$
H^i(K^\bullet\otimes M)
\simeq H^i(X,\mathcal F\otimes M)
$$

functorially in $M$ and in every degree. Equivalently, $Rf_*\mathcal F$ is locally represented by a bounded complex of finite locally free modules, and its derived pullback to every base is the derived direct image of the pulled-back sheaf.

**Proof.** The projective case is the finite-complex theorem. For a general proper morphism, first run the reduction of Section 2.4 in the derived category without a flatness assertion on its error terms. The projective terms have bounded-above resolutions by finite free modules. The kernels, cokernels, and positive higher direct images are supported on a proper closed subset and have such pseudo-coherent resolutions by noetherian induction. Mapping cones for the two exact sequences and the Leray filtration therefore give a bounded-above finite-free complex $P$ representing $Rf_*\mathcal F$. The same construction after derived tensoring gives, functorially in an $A$-module $M$,

$$
P\otimes_A^LM
\simeq R\Gamma(X,\mathcal F\otimes_A^LM).
$$

This is the derived projection formula inside the explicit projective-modification construction; no ordinary base-change assertion has been used.

Now use flatness. It identifies $\mathcal F\otimes_A^LM$ with the ordinary sheaf $\mathcal F\otimes_AM$. The relative cohomological-dimension induction of Section 3.2, whose projective and closed-support steps are the same ones just used, puts the cohomology of the right side in one fixed finite interval for every $M$. Thus the pseudo-coherent complex $P$ has finite Tor amplitude. A bounded-above finite-free resolution with finite Tor amplitude can be truncated to a bounded finite-projective complex: below the Tor bound the last syzygy remains exact after tensoring with every module, hence is flat; it is finitely presented, so it is projective. Shrinking the affine base makes every term free. The displayed comparison then gives the asserted formula and remains functorial after any further base change. $\square$

This theorem is the proper form of the finite-presentation theorem for cohomology. Flatness of $\mathcal F$ is what turns the finite coherent derived object into a perfect complex over the base; without it, proper finiteness remains true but an arbitrary ordinary coefficient module need not be computed by tensoring one finite locally free complex.

## 3. Finiteness for proper morphisms

### 3.1 Coherence of higher direct images

**Proper finiteness theorem.** Let $f:X\to S$ be a proper morphism of locally noetherian schemes and let $\mathcal F$ be coherent on $X$. Then $R^if_*\mathcal F$ is coherent for every $i\geq0$. If $S=\operatorname{Spec}A$ is noetherian, each $H^i(X,\mathcal F)$ is a finite $A$-module.

**Proof.** The assertion is local on $S$, so take an affine noetherian base. In the projective case, resolve $i_*\mathcal F$ on projective space far enough by finite sums of twists. The Čech calculation makes the cohomology of each twist finite over $A$; repeated long exact sequences then make $H^i(X,\mathcal F)$ finite.

For a general proper $X$, apply the proper reduction lemma. The projective sheaf $p^*(\mathcal J\mathcal F)$ has finite cohomology. The comparison with $\mathcal J\mathcal F$ has kernel and cokernel supported on a smaller closed subset; their finiteness follows by noetherian induction. The exact sequences

$$
0\to\mathcal J\mathcal F\to\mathcal F\to
\mathcal F/\mathcal J\mathcal F\to0
$$

and the corresponding sequence involving $p_*p^*(\mathcal J\mathcal F)$ transfer finiteness to $\mathcal F$. Sheafifying the finite modules on affine opens gives coherence, and localization compatibility makes the local sheaves agree. $\square$

Proper finiteness is the coherent analogue of compactness. It says that infinitely many local sections and cocycles collapse to finitely many parameters over the base.

### 3.2 Vanishing bounds and cohomological dimension

If $X$ is noetherian of dimension $d$, then

$$
H^i(X,\mathcal F)=0\quad(i>d)
$$

for every quasi-coherent $\mathcal F$. One proof chooses an affine open containing every generic point, whose complement has smaller dimension. Cohomology with support and induction reduce the degree by one at each passage to the complement. For a projective embedding into $\mathbf P^r_S$, the standard affine cover gives the cruder relative bound $R^if_*\mathcal F=0$ for $i>r$.

**Relative cohomological-dimension theorem.** If $f:X\to S$ is proper between noetherian schemes and every fiber has dimension at most $d$, then $R^if_*\mathcal F=0$ for every quasi-coherent $\mathcal F$ and every $i>d$.

**Proof.** The assertion is local on the base. In the projective case, relative Noether normalization applies after stratifying the noetherian base: a general linear projection gives a finite map from each stratum of the support to $\mathbf P^d$ over that stratum. Finite direct image is exact, and the standard cover of $\mathbf P^d$ has Čech length $d$, so cohomology vanishes above $d$ there. Noetherian induction across the complements of the strata transfers the same vanishing to the original base. For a general proper morphism, use the proper reduction lemma. Its projective term has the asserted bound. The closed-support error terms have strictly smaller relative support dimension, so the same induction gives a bound no larger than $d$ for them. The two Leray and long exact sequences in Section 2.4 transfer the vanishing to $\mathcal F$. Filtered colimits of quasi-coherent sheaves are exact and commute with cohomology on the finite affine covers used in the argument, so the coherent case extends to every quasi-coherent sheaf. $\square$

For a proper curve, only $R^0$ and $R^1$ occur. For an abelian scheme of relative dimension $g$, only degrees $0$ through $g$ occur. These short ranges are what make the later applications especially exact.

### 3.3 Projection and composition

Let $f:X\to S$ be proper, $\mathcal F$ coherent, and $\mathcal E$ finite locally free on $S$. The projection formula gives

$$
R^if_*(\mathcal F\otimes f^*\mathcal E)
\simeq R^if_*\mathcal F\otimes\mathcal E.
$$

To prove it, trivialize $\mathcal E$ locally. Both sides then become a finite direct sum of $R^if_*\mathcal F$, and the natural map is the identity under this description. The local isomorphisms glue by naturality.

For proper maps $X\xrightarrow fY\xrightarrow hS$, the truncation filtration of the composite yields

$$
E_2^{p,q}=R^ph_*(R^qf_*\mathcal F)
\Longrightarrow R^{p+q}(h\circ f)_*\mathcal F.
$$

Every term is coherent by proper finiteness, and the sequence has only finitely many terms on each diagonal. This is the precise derived-to-coherent passage: bounded coherent cohomology sheaves, filtered by truncations, recover the coherent cohomology of the composite. Degeneration would identify graded pieces, not canonically split the target.

### 3.4 Why properness and coherence matter

For $j:\mathbf A^1_k\to\operatorname{Spec}k$, the sheaf $j_*\mathcal O$ has global sections $k[t]$, infinite-dimensional over $k$. Thus finite type without properness does not give finite cohomology.

Even on a proper scheme, a noncoherent quasi-coherent sheaf can have infinite-dimensional global sections. On $\mathbf P^1_k$, the direct sum $\bigoplus_{n\geq0}\mathcal O$ has an infinite-dimensional space of sections. Coherence supplies finite generation; properness prevents those generators from proliferating at infinity.

Noetherianity is also doing real work. It makes submodules of finite modules finite, makes coherent support admit induction, and supplies Artin--Rees later. There are useful finitely presented versions over more general bases, but they require explicit pseudo-coherence and perfectness assumptions rather than the word “coherent” alone.

## 4. Upper semicontinuity

### 4.1 The rank of fiber cohomology

Let $K^\bullet$ be a bounded complex of finite free modules over a ring $A$. At a point $s\in\operatorname{Spec}A$,

$$
\dim_{\kappa(s)}H^i(K^\bullet\otimes\kappa(s))
=\operatorname{rank}K^i-\operatorname{rank}_s d^{i-1}
-\operatorname{rank}_s d^i.
$$

The rank of a matrix is at least $r$ exactly where one of its $r\times r$ minors is nonzero, an open condition. Therefore matrix rank is lower semicontinuous. The negative of each adjacent rank is upper semicontinuous, so the displayed cohomology dimension is upper semicontinuous.

This elementary observation contains the geometry: specialization can make a differential lose rank, creating cohomology, but it cannot make the differential gain rank at a special point. Fiber cohomology can jump upward on closed loci.

### 4.2 The semicontinuity theorem

**Semicontinuity theorem.** Let $f:X\to S$ be proper and finitely presented, with $S$ locally noetherian, and let $\mathcal F$ be coherent and flat over $S$. For every $i\geq0$, the function

$$
h^i_{\mathcal F}(s)=
\dim_{\kappa(s)}H^i(X_s,\mathcal F_s)
$$

is upper semicontinuous. Equivalently, for every integer $n$, the set

$$
\{s\in S:h^i_{\mathcal F}(s)\geq n\}
$$

is closed.

**Proof.** The claim is local on $S$. The proper cohomology-complex theorem supplies a bounded finite free complex computing every ordinary fiber because $\mathcal F$ is $S$-flat. Apply the matrix-rank calculation of Section 4.1. The condition that the sum of the two adjacent ranks is at most a fixed integer is closed, so every locus $h^i_{\mathcal F}\geq n$ is closed. $\square$

The flatness of $\mathcal F$ is indispensable to identify ordinary fiber restriction with tensoring the universal cohomology complex. Without it, derived fibers include Tor terms and the naive fiber dimensions need not obey this theorem.

### 4.3 Euler characteristics in flat families

Suppose the hypotheses of the theorem hold and the fibers have uniformly bounded dimension. Define

$$
\chi(X_s,\mathcal F_s)=
\sum_i(-1)^ih^i_{\mathcal F}(s).
$$

**Euler-characteristic theorem.** This integer is locally constant on $S$.

**Proof.** Locally, the finite complex $K^\bullet$ computes every fiber. Over a field, the Euler characteristic of its cohomology equals the alternating sum of the dimensions of its terms:

$$
\sum_i(-1)^i\dim H^i(K\otimes\kappa(s))
=\sum_i(-1)^i\operatorname{rank}K^i.
$$

The right side is constant on each connected open where the terms have fixed ranks. The proper reduction gives the same conclusion in the nonprojective case by additivity in exact sequences. $\square$

For a proper flat curve and a line bundle of fiberwise degree $d$, later Riemann--Roch identifies this constant as $d+1-g$. Here we need only the cohomological constancy, not that formula.

### 4.4 Jumping examples

Let $C$ be a smooth projective curve of positive genus. In a family of degree-zero line bundles parameterized by its Picard variety, the trivial bundle has a section while a general nontrivial bundle does not. Thus $h^0$ jumps upward at the origin. Upper semicontinuity predicts precisely this direction.

Flatness cannot be read from constant support. Let $A=k[\epsilon]/(\epsilon^2)$ and let $M=A/(\epsilon)$. There is only one topological point, so every pointwise dimension function is constant, but $M$ is not flat. Nilpotent test schemes reveal the missing relation. This is why flattening and base change must be scheme-theoretic rather than merely pointwise.

## 5. Cohomology and base change

### 5.1 A local normal form

The exact base-change criterion is linear algebra over a local ring. Let $(A,\mathfrak m,k)$ be local and $K^\bullet$ a bounded complex of finite free $A$-modules. Whenever some matrix entry of a differential is a unit, elementary row and column operations split off a contractible summand

$$
0\longrightarrow A\xrightarrow{1}A\longrightarrow0.
$$

Repeating this process writes

$$
K^\bullet\simeq K^\bullet_{\min}\oplus K^\bullet_{\mathrm{ctr}},
$$

where the second summand is contractible and every entry of every differential of the **minimal complex** $K_{\min}$ lies in $\mathfrak m$. Tensoring the minimal complex with $k$ kills all differentials, so

$$
H^i(K^\bullet\otimes k)=K^i_{\min}\otimes k.
$$

Consider the canonical map

$$
H^i(K^\bullet)\otimes k\longrightarrow H^i(K^\bullet\otimes k).
$$

It is surjective exactly when $d^i_{\min}=0$. Indeed, surjectivity says

$$
\ker d^i_{\min}+\mathfrak mK^i_{\min}=K^i_{\min};
$$

Nakayama's lemma then gives $\ker d^i_{\min}=K^i_{\min}$. Once $d^i_{\min}=0$, one has

$$
H^i(K_{\min})=\operatorname{coker}d^{i-1}_{\min}.
$$

This module is free precisely when $d^{i-1}_{\min}=0$: if the cokernel is free, its quotient map splits, making the image of $d^{i-1}$ a direct summand contained in $\mathfrak mK^i$; a direct summand contained there must vanish. Thus neighboring differentials encode both base change and local freeness.

### 5.2 The exact criterion

**Cohomology-and-base-change theorem.** Let $f:X\to S$ be proper and finitely presented, where $S$ is locally noetherian, and let $\mathcal F$ be coherent and flat over $S$. Fix $s\in S$ and $i\geq0$.

1. If

   $$
   \beta_s^i:(R^if_*\mathcal F)\otimes\kappa(s)
   \longrightarrow H^i(X_s,\mathcal F_s)
   $$

   is surjective, then after shrinking to a neighborhood $U$ of $s$, the degree-$i$ base-change map is an isomorphism for every morphism $T\to U$.

2. Assuming $\beta_s^i$ is surjective, the following are equivalent after shrinking around $s$:

   - $R^if_*\mathcal F$ is finite locally free;
   - $\beta_s^{i-1}$ is surjective, with the condition omitted when $i=0$.

3. If both adjacent conditions hold, then $R^if_*\mathcal F$ is finite locally free on $U$ and, for every morphism $T\to U$,

   $$
   (R^if_*\mathcal F)|_U\otimes_{\mathcal O_U}\mathcal O_T
   \xrightarrow{\sim}R^if_{T*}\mathcal F_T.
   $$

**Proof.** Work over the local ring at $s$ and use a finite free complex computing cohomology and coefficient change. By Section 5.1, surjectivity in degree $i$ says that the $i$th differential in a minimal model vanishes. Vanishing of a matrix persists after shrinking because it is an equality of finitely many functions. Then both $H^i(K)\otimes M$ and $H^i(K\otimes M)$ are the cokernel of $d^{i-1}\otimes M$ for every coefficient module $M$. Thus base change is an isomorphism in degree $i$.

Under this vanishing, $H^i(K)$ is locally free exactly when $d^{i-1}$ also vanishes in a minimal model. The latter is exactly surjectivity of base change in degree $i-1$. If both differentials vanish, $K$ has zero differential into and out of degree $i$, so formation of $H^i$ commutes with every tensor product. Sheafifying proves all three assertions. $\square$

The theorem is deliberately asymmetric: surjectivity in degree $i$ controls the outgoing differential, while local freeness in degree $i$ also requires control of the incoming differential. Remembering this avoids the false claim that constancy of $h^i$ alone always proves base change.

### 5.3 Flat and arbitrary change of base

If $g:T\to S$ is flat, then ordinary pullback is exact. Proper flat base change for coherent sheaves gives

$$
g^*R^if_*\mathcal F\xrightarrow{\sim}R^if_{T*}g'^*\mathcal F
$$

without requiring $R^if_*\mathcal F$ to be locally free. One proof takes a bounded finite presentation of the relevant cohomology complex: flat tensor commutes with kernels and images, hence with cohomology. For a general proper morphism, the same statement follows by the proper-reduction induction.

Arbitrary base change is subtler. Under the standing proper, noetherian, and $S$-flat hypotheses on $\mathcal F$, the derived morphism

$$
Lg^*Rf_*\mathcal F\longrightarrow Rf_{T*}Lg'^*\mathcal F
$$

is an isomorphism. This is exactly the base-change assertion in the proper cohomology-complex theorem: locally, both sides are represented by $K^\bullet\otimes^L\mathcal O_T$, and $Lg'^*\mathcal F=g'^*\mathcal F$ because $\mathcal F$ is flat over $S$. More generally, the same conclusion holds for a coherent complex of finite Tor amplitude over $S$. Passing from the derived isomorphism to degree-$i$ coherent sheaves requires control of Tor contributions from neighboring cohomology. The criterion of Section 5.2 is precisely that passage.

For a quotient $A\to A/I$ of Tor dimension at most one, the two-row universal-coefficient sequence gives

$$
0\to H^i(K)\otimes_AA/I
\to H^i(K\otimes_AA/I)
\to\operatorname{Tor}_1^A(H^{i+1}(K),A/I)\to0.
$$

Thus torsion in the next cohomology group creates new classes after reduction. This is the most common arithmetic failure of naive base change.

### 5.4 Local freeness and constant fiber dimension

**Constant-rank corollary.** Under the hypotheses of Section 5.2, on the open locus where base change is surjective in degrees $i$ and $i-1$, the sheaf $R^if_*\mathcal F$ is finite locally free and commutes with arbitrary base change. Conversely, if $R^if_*\mathcal F$ is locally free and its formation commutes with residue fields, then $h^i_{\mathcal F}$ is locally constant.

This is immediate from the local minimal complex and the exact criterion. Local constancy of fiber dimensions alone is not a replacement for adjacent surjectivity on a nonreduced base: the entries of a differential can lie in the nilradical and vanish at every point without vanishing as functions.

A particularly useful downward induction begins above the cohomological dimension, where both sides vanish. If the base is reduced and all fiber dimensions $h^j$ are locally constant for $j\geq i$, descending through the minimal complex shows that every $R^jf_*\mathcal F$ for $j\geq i$ is locally free and commutes with arbitrary base change: the relevant residual matrix entries vanish at every point and hence vanish on a reduced scheme. On an arbitrary base the same conclusion holds when the corresponding base-change maps are explicitly assumed surjective. The alternating constancy of Euler characteristic often lets one deduce the last missing fiber dimension.

### 5.5 Curves as a two-degree case

Let $f:C\to S$ be a proper flat finitely presented family of curves and $\mathcal F$ coherent and $S$-flat. Only degrees zero and one occur. Since degree two vanishes, base change in degree one is automatically surjective in the finite-complex model. Hence $R^1f_*\mathcal F$ commutes with residue fields; it is locally free exactly when base change in degree zero is surjective. If $S$ is reduced and both $h^0$ and $h^1$ are locally constant, the local minimal differentials vanish at every point and therefore vanish, so both direct images are locally free and commute with arbitrary base change. Over a nonreduced base one must retain the explicit degree-zero base-change condition.

For $\mathcal F=\mathcal O_C$ and geometrically connected, geometrically reduced fibers, one has the stronger degree-zero connected-fiber theorem

$$
\mathcal O_S\longrightarrow f_*\mathcal O_C
$$

and this isomorphism is preserved by every base change. Indeed, a proper geometrically connected, geometrically reduced scheme over a field has only constant global functions: its finite algebra of global functions becomes a finite reduced connected algebra after algebraic closure and is therefore the ground field. Thus $H^0(C_s,\mathcal O_{C_s})=\kappa(s)$. The degree-zero base-change map is surjective because the class of $1$ already spans its target. The exact base-change theorem now makes $f_*\mathcal O_C$ a line bundle commuting with arbitrary base change near every point. The unit map from $\mathcal O_S$ is an isomorphism on every fiber, hence an isomorphism of line bundles. The degree-zero criterion then gives that $R^1f_*\mathcal O_C$ is finite locally free and universally compatible with base change. Its dual will be the Hodge bundle.

## 6. Flatness, Hilbert polynomials, and flattening

### 6.1 The cohomological meaning of a Hilbert polynomial

Let $f:X\to S$ be projective and finitely presented, let $\mathcal O_X(1)$ be relatively ample, and let $\mathcal F$ be coherent. For a geometric point $\bar s\to S$, the function

$$
n\longmapsto\chi(X_{\bar s},\mathcal F_{\bar s}(n))
$$

agrees for all sufficiently large $n$ with a numerical polynomial $P_{\bar s}(n)$. The projective-space resolution proves this: the Euler characteristic of $\mathcal O(n-a)$ is $\binom{n-a+r}{r}$, and additivity through a finite graded resolution expresses the answer as an integral combination of such binomial polynomials.

When $\mathcal F$ is flat over $S$, Section 4.3 applied to every twist shows that $P_{\bar s}$ is locally constant. More concretely, relative Serre vanishing gives, locally on $S$ and for $n\gg0$,

$$
R^if_*\mathcal F(n)=0\quad(i>0),
$$

and base change identifies

$$
f_*\mathcal F(n)\otimes\kappa(\bar s)
\simeq H^0(X_{\bar s},\mathcal F_{\bar s}(n)).
$$

The pushforward is then finite locally free of rank $P_{\bar s}(n)$. Thus a Hilbert polynomial is not merely a fiberwise count. It is the eventual rank profile of a sequence of vector bundles on the base.

### 6.2 Constancy and the converse

Constancy of the Hilbert polynomial detects flatness only with the correct hypotheses.

**Fiberwise flatness criterion.** Let $S$ be locally noetherian, $f:X\to S$ projective and finitely presented, and $\mathcal F$ coherent. Near a point $s\in S$, the sheaf $\mathcal F$ is flat over $S$ if and only if, for every sufficiently large $n$, $f_*\mathcal F(n)$ is locally free and its formation commutes with residue fields.

**Proof.** Flatness gives the conclusion by the preceding section. Conversely, choose $n$ so large that $\mathcal F(n)$ is generated relative to $S$ and write

$$
f^*\mathcal E\twoheadrightarrow\mathcal F(n),
\qquad \mathcal E=f_*\mathcal F(n).
$$

Let $\mathcal K$ be the kernel. Choose a common regularity bound for $\mathcal F$ and $\mathcal K$, and apply the hypothesis in enough consecutive degrees beyond that bound. Multiplication by degree-one coordinates then presents every later graded piece from those finitely many pieces. The assumed local freeness and residue-field compatibility say that these presentations and their kernels remain exact after every residue-field tensor product. By the local flatness criterion, the resulting high-degree graded module is flat over the base. Sheafification discards only bounded-degree irrelevant torsion, so $\mathcal F(n)$ is flat. This is precisely the graded flatness argument used in the flattening theorem of Book 8; twisting back proves that $\mathcal F$ is flat. $\square$

Constancy of the integer $\chi(\mathcal F_s)$ for one twist is far too weak. Different sheaves can have the same Euler characteristic, and torsion in adjacent cohomological degrees can cancel in the alternating sum. One needs the polynomial for all large twists, or equivalently the exact high-degree presentation.

### 6.3 Flattening strata

Suppose $S$ is noetherian, $X\to S$ projective and finitely presented, and $\mathcal F$ coherent. The base can be decomposed into locally closed pieces on which $\mathcal F$ becomes flat.

**Flattening-stratification theorem.** For every numerical polynomial $P$, there is a locally closed subscheme $S_P\subseteq S$ with the following universal property. A morphism $T\to S$ factors through $S_P$ exactly when $\mathcal F_T$ is flat over $T$ and every geometric fiber has Hilbert polynomial $P$. The strata are pairwise disjoint and their underlying sets cover $S$.

**Proof strategy.** Choose $n$ beyond a common regularity bound. The finite module $f_*\mathcal F(n)$ has a universal flattening locus where it is locally free of rank $P(n)$; Fitting ideals cut out this locus scheme-theoretically. Repeat in finitely many consecutive degrees, enough that multiplication by degree-one sections reconstructs the saturated graded module. On their intersection, the multiplication maps and their kernels have the ranks forced by $P$. The evaluation presentation of Section 6.2 then proves flatness of $\mathcal F$. Conversely a flat family with polynomial $P$ makes all these high-degree modules locally free with the prescribed ranks, so its classifying map annihilates the same Fitting ideals and factors uniquely through the stratum. A regularity bound makes the construction finite. $\square$

The scheme structure matters. A map from a nonreduced $T$ may send its only point into the correct set while failing to factor through the stratum because an infinitesimal Fitting equation is nonzero. Flattening is designed to detect exactly that failure.

For a proper morphism without a chosen ample line bundle there is still a flattening decomposition in broad generality, but it need not be described by Hilbert polynomials. The projective form is the one needed for the parameter spaces considered here.

### 6.4 Uniform generation and embeddings

Let $f:X\to S$ be projective, flat, and finitely presented with $S$ noetherian, and let $\mathcal L$ be relatively ample. For $n\gg0$, relative Serre vanishing and base change give

$$
R^if_*\mathcal L^n=0\quad(i>0),
\qquad f_*\mathcal L^n\text{ finite locally free}.
$$

The evaluation map $f^*f_*\mathcal L^n\to\mathcal L^n$ is surjective. A still larger $n$ separates length-two subschemes in every fiber, so it defines a closed immersion

$$
X\hookrightarrow\mathbf P_S(f_*\mathcal L^n).
$$

To prove uniformity, apply Serre vanishing not only to $\mathcal O_X$ but to the ideal of the diagonal and to the universal length-two subscheme on the finite-length Hilbert scheme constructed in Book 8. Vanishing makes restriction of sections surjective on every length-two fiber; properness of that parameter scheme turns pointwise largeness of $n$ into one bound. This explains why cohomological finiteness produces uniform projective embeddings.

## 7. Formal functions

### 7.1 Infinitesimal neighborhoods remember completion

Let $S=\operatorname{Spec}A$ be noetherian, let $I\subseteq A$, and set

$$
A_n=A/I^{n+1},\qquad
X_n=X\times_A\operatorname{Spec}A_n,
\qquad \mathcal F_n=\mathcal F/I^{n+1}\mathcal F.
$$

The schemes $X_n$ are the successive infinitesimal neighborhoods of the closed fiber $X_0$. They remember more than the reduced fiber: a section on $X_n$ records normal behavior up to order $n$.

There is a natural comparison

$$
H^i(X,\mathcal F)\otimes_AA_n
\longrightarrow H^i(X_n,\mathcal F_n).
$$

It is not generally an isomorphism for fixed $n$; the base-change criterion may fail. The theorem on formal functions says that the discrepancy disappears after taking the inverse limit. Completion is therefore more stable than any individual infinitesimal base change.

### 7.2 The theorem on formal functions

**Theorem on formal functions.** Let $f:X\to S$ be proper, with $S$ locally noetherian, let $\mathcal F$ be coherent, and let $\mathcal I\subseteq\mathcal O_S$ be a coherent ideal. Write

$$
S_n=(S,\mathcal O_S/\mathcal I^{n+1}),
\qquad X_n=X\times_SS_n,
\qquad \mathcal F_n=\mathcal F/\mathcal I^{n+1}\mathcal F.
$$

Then for every $i$ the natural map of sheaves along $V(\mathcal I)$ is an isomorphism

$$
(R^if_*\mathcal F)^{\wedge}_{\mathcal I}
\xrightarrow{\sim}
\varprojlim_n R^if_{n*}\mathcal F_n.
$$

On an affine open $\operatorname{Spec}A\subseteq S$, this reads

$$
H^i(X,\mathcal F)^{\wedge}_I
\xrightarrow{\sim}
\varprojlim_nH^i(X_n,\mathcal F_n).
$$

No flatness of $f$ or $\mathcal F$ over $S$ is required. Properness, coherence, and noetherianity are the essential hypotheses.

### 7.3 Proof by Artin--Rees and pro-systems

The proof has one algebraic mechanism used twice. The Artin--Rees lemma says that if $N\subseteq M$ are finite modules over a noetherian ring, then for some $c$ and all $n\geq c$,

$$
I^nM\cap N=I^{n-c}(I^cM\cap N).
$$

Consequently the $I$-adic topology induced on $N$ agrees with its own $I$-adic topology, and completion is exact on finite modules.

We need its cohomological form. A projective system $(M_n)$ is **pro-zero** if for every $n$ some later transition $M_m\to M_n$ is zero.

**Artin--Rees cohomology lemma.** Let $X$ be proper over a noetherian ring $A$, let $I\subseteq A$, and let $\mathcal F$ be coherent. For every $i$, the two filtrations on $H^i(X,\mathcal F)$,

$$
I^nH^i(X,\mathcal F)
\quad\text{and}\quad
\operatorname{im}\bigl(H^i(X,I^n\mathcal F)\to H^i(X,\mathcal F)\bigr),
$$

are cofinal. Moreover the kernels and cokernels created by replacing $I^n\mathcal F$ with the image of $I^n\otimes\mathcal F\to\mathcal F$ form pro-zero systems.

**Proof.** In the projective case, resolve $\mathcal F$ through more steps than the cohomological dimension by finite sums of twists. Apply the finite Čech complexes of those twists. At every kernel and image in the resulting bounded diagram, ordinary Artin--Rees says that intersection with $I^n$ differs from the intrinsic $I$-adic filtration by a bounded shift. Induction through the finitely many rows and columns proves cofinality and makes every error system pro-zero. No flatness is used: the error caused by tensoring a syzygy is retained as a kernel system, and Artin--Rees is exactly what makes it pro-zero.

For a general proper $X$, use the projective reduction of Section 2.4. The projective term satisfies the assertion. The kernel, cokernel, and positive higher direct images are supported on a proper closed subset, where noetherian induction applies. The Leray sequence for the modification and the two long exact sequences transfer cofinality and pro-vanishing to $\mathcal F$. $\square$

Apply the lemma to

$$
0\longrightarrow I^{n+1}\mathcal F
\longrightarrow\mathcal F
\longrightarrow\mathcal F_n\longrightarrow0.
$$

The long exact sequence shows that $H^i(X_n,\mathcal F_n)$ differs from the quotient of $H^i(X,\mathcal F)$ by the image of $H^i(X,I^{n+1}\mathcal F)$ only by the kernel of

$$
H^{i+1}(X,I^{n+1}\mathcal F)
\longrightarrow H^{i+1}(X,\mathcal F).
$$

The Artin--Rees cohomology lemma makes the latter kernels pro-zero and identifies the inverse limit of the former quotients with the $I$-adic completion of $H^i(X,\mathcal F)$. All transition systems involved are Mittag--Leffler: modulo any fixed power their images stabilize inside a finite module. Taking inverse limits is therefore exact here and gives

$$
H^i(X,\mathcal F)^\wedge_I
\xrightarrow{\sim}
\varprojlim_nH^i(X_n,\mathcal F_n).
$$

The construction localizes on the base, so the affine isomorphisms sheafify to the stated theorem. $\square$

The proof explains why formal functions is not simply repeated base change. Fixed-level errors can survive, but Artin--Rees makes their filtrations cofinal, so completion forgets the bounded displacement.

### 7.4 Consequences and limitations

If $A$ is complete for $I$ and $X$ is proper over $A$, then

$$
H^i(X,\mathcal F)
\simeq\varprojlim_nH^i(X_n,\mathcal F_n),
$$

because proper finiteness makes $H^i(X,\mathcal F)$ a finite, hence complete, $A$-module. Thus a coherent cohomology class is determined by its compatible restrictions to all infinitesimal neighborhoods.

This does not say every compatible family of coherent sheaves $\mathcal F_n$ comes from a coherent sheaf on $X$. That is an existence theorem for coherent objects on a completed proper space and belongs to a stronger algebraization theory. Formal functions compares cohomology of a sheaf already given on $X$.

Properness remains essential. For an open family, sections can have unbounded poles toward the omitted boundary, and the inverse limit of infinitesimal sections can be larger than the completion of global sections.

## 8. Completion and coherent passages

### 8.1 Ordinary and derived completion

For a complex $K$ of $A$-modules, the completion appropriate to exact constructions is

$$
R\widehat K=R\varprojlim_n(K\otimes_A^LA/I^{n+1}).
$$

There is a Milnor exact sequence

$$
0\to R^1\varprojlim_nH^{i-1}(K\otimes_A^LA/I^{n+1})
\to H^i(R\widehat K)
\to\varprojlim_nH^i(K\otimes_A^LA/I^{n+1})\to0.
$$

When $K$ is bounded with finite cohomology over a noetherian ring, Artin--Rees makes the relevant towers Mittag--Leffler and annihilates the first derived limit. Ordinary completion is exact on those cohomology modules. Hence

$$
H^i(R\widehat K)\simeq H^i(K)^{\wedge}_I.
$$

This is the derived-to-coherent passage behind formal functions. It is valid because finiteness removes both possible defects: Tor is organized inside derived tensor, and inverse-limit failure is removed by Mittag--Leffler.

Without finite generation the conclusion can fail. A tower may have images that shrink forever, producing a nonzero $R^1\varprojlim$, and an infinitely generated module need not be separated or complete for its $I$-adic topology.

### 8.2 Completed base change

Suppose $A\to B$ is a homomorphism of noetherian rings, $B$ is complete for $IB$, and $X$ is proper over $A$. Assume that $\mathcal F$ is $A$-flat, or more generally that the coherent complex under consideration has finite Tor amplitude over $A$, and that its derived base-change morphism is an isomorphism. Then completion and formal functions yield

$$
R\Gamma(X,\mathcal F)\otimes_A^LB
\simeq
R\varprojlim_nR\Gamma
\bigl(X_{B/I^{n+1}B},\mathcal F_{B/I^{n+1}B}\bigr).
$$

Here $\mathcal F_{B/I^{n+1}B}$ means derived pullback in the general complex case and ordinary pullback in the $A$-flat sheaf case. The left side is already derived $IB$-complete because it is a bounded complex with finite $B$-cohomology. If in addition the neighboring cohomology modules satisfy the local-freeness criterion, taking degree $i$ gives the ordinary formula

$$
H^i(X,\mathcal F)\otimes_AB
\simeq H^i(X_B,\mathcal F_B).
$$

The first statement is robust; the second discards Tor and therefore needs the extra condition. This distinction is particularly important when $B$ has residue characteristic dividing torsion in $H^{i+1}$.

### 8.3 Lifting sections through thickenings

Let $A'\twoheadrightarrow A$ have square-zero kernel $J$, and let $X'$ be a proper flat lift of $X$ with a coherent $A'$-flat sheaf $\mathcal F'$. The exact sequence

$$
0\to J\otimes_A\mathcal F\to\mathcal F'\to\mathcal F\to0
$$

gives

$$
H^0(X',\mathcal F')\to H^0(X,\mathcal F)
\xrightarrow{\delta}H^1(X,J\otimes_A\mathcal F).
$$

A section lifts exactly when its obstruction $\delta(s)$ vanishes; if it lifts, the set of lifts is a torsor under $H^0(X,J\otimes_A\mathcal F)$. Iterating through $A/I^{n+1}$ makes the role of $H^1$ concrete. If all these obstructions vanish and compatible sections exist, formal functions produces a section of the completed cohomology module. When $A$ is complete and cohomology finite, that is an actual global section of $\mathcal F$.

For line bundles the analogous obstruction lies one degree higher: infinitesimal automorphisms are $H^0(X,J\otimes\mathcal O_X)$, deformations form a torsor under $H^1(X,J\otimes\mathcal O_X)$, and obstructions lie in $H^2(X,J\otimes\mathcal O_X)$. When the base is affine and the relevant cohomology is locally free, these become $H^i(X,\mathcal O_X)\otimes J$. On a curve $H^2=0$, which is the cohomological reason its Picard functor is smooth.

### 8.4 What is not yet algebraization

Completion remembers every infinitesimal neighborhood, but an object over all neighborhoods need not automatically come from the algebraic family without an existence theorem. Nor does an isomorphism of completions imply an isomorphism on an unspecified open neighborhood unless finite presentation and an effectivity argument are supplied.

The safe conclusions here are these: cohomology of a given coherent sheaf completes correctly; compatible sections algebraize because they belong to a finite complete module; and morphisms between already-given coherent sheaves can often be recovered from completed Hom modules under properness. Constructing schemes or sheaves from purely completed data requires the separate proper existence theory developed later.

## 9. Duality interfaces in relative dimension one

### 9.1 Trace and the relative dualizing line

Let $f:C\to S$ be smooth, proper, and finitely presented of relative dimension one. The sheaf

$$
\omega_{C/S}=\Omega^1_{C/S}
$$

is invertible. Fiberwise residues define a trace

$$
\operatorname{Tr}_f:R^1f_*\omega_{C/S}\longrightarrow\mathcal O_S.
$$

We first justify the relative projection used in its construction. After shrinking around a point of $S$, choose a finite separable divisor on the smooth geometric fiber. Its points lift after an étale base change to disjoint sections; the sum of their conjugates descends to a relative effective Cartier divisor $D$. A line bundle of positive degree on every proper curve fiber is relatively ample: its high powers separate length-two subschemes by the vanishing argument of Book 8. Hence $C$ is projective locally on $S$, and a general pair of sections of a high power of $\mathcal O(D)$ gives a finite map to $\mathbf P^1_S$.

Choose such a map. On the affine line, a meromorphic differential has residues at the finitely many poles; the coefficient of $t^{-1}dt$ is unchanged by a change of local parameter. The sum of residues, including the point at infinity, is zero. Čech representatives on the standard two-open cover therefore define a functional on $H^1(\omega)$. Compatibility of residue with finite trace makes the functional independent of the chosen projection. These local traces agree under base change and glue over $S$.

The residue assertions used here can be proved algebraically. For a parameter $t$ in a regular one-dimensional local ring, define

$$
\operatorname{res}\left(\sum_{n\gg-\infty}a_nt^n\,dt\right)=a_{-1}.
$$

If $u$ is another parameter, formal differentiation and comparison of Laurent coefficients show that the value is unchanged. For a finite extension of function fields, grouping the conjugate Laurent expansions proves $\operatorname{res}(\operatorname{Tr}\eta)=\sum\operatorname{res}(\eta)$. On $\mathbf P^1$, the Laurent expansion at infinity proves that the sum of residues is zero. A finite projection therefore transfers this identity to $C$. Independence of the projection follows because both resulting functionals agree after passing to a common finite refinement and applying transitivity of field trace.

On every geometrically connected fiber, the trace is an isomorphism

$$
H^1(C_s,\omega_{C_s})\simeq\kappa(s).
$$

One proves this first for $\mathbf P^1$ by the Laurent-monomial calculation and then for a finite map to $\mathbf P^1$ using the trace pairing. Since the curve is already smooth, no normalization defect remains. Base change in top degree is automatically an isomorphism for a relative curve. The fiberwise trace isomorphisms and Nakayama's lemma therefore upgrade to

$$
R^1f_*\omega_{C/S}\simeq\mathcal O_S.
$$

### 9.2 Perfect pairings for smooth proper curves

Multiplication followed by trace gives, for a vector bundle $\mathcal E$ on $C$,

$$
R^if_*\mathcal E\otimes
R^{1-i}f_*(\mathcal E^\vee\otimes\omega_{C/S})
\longrightarrow\mathcal O_S.
$$

**Relative duality for curves.** If the indicated higher direct images are locally free and commute with base change—as they do on the open where the adjacent base-change conditions of Section 5.2 hold—the pairing is perfect. Equivalently,

$$
(R^if_*\mathcal E)^\vee
\simeq R^{1-i}f_*(\mathcal E^\vee\otimes\omega_{C/S}),
\qquad i=0,1.
$$

**Proof.** We first prove perfectness over a field. Choose a finite map $\pi:C\to\mathbf P^1$ as in Section 9.1. It is finite flat because its source is Cohen--Macaulay of pure dimension one and its target is regular of dimension one. There is a local trace isomorphism

$$
\pi_*\omega_C
\xrightarrow{\sim}
\mathcal Hom_{\mathbf P^1}(\pi_*\mathcal O_C,\omega_{\mathbf P^1}).
$$

At a pair of discrete valuation rings it sends a differential $\eta$ to the functional $b\mapsto\operatorname{Tr}(b\eta)$. The inverse different consists exactly of those meromorphic differentials whose residues against every integral $b$ are integral; the parameter calculation of Section 9.1 proves both injectivity and surjectivity. Tensoring with a vector bundle $\mathcal E$ gives

$$
\pi_*(\mathcal E^\vee\otimes\omega_C)
\simeq (\pi_*\mathcal E)^\vee\otimes\omega_{\mathbf P^1}.
$$

It remains to check duality on $\mathbf P^1$. Use its standard two-affine cover. The Čech complex of a vector bundle $\mathcal V$ has the form

$$
\Gamma(U_0,\mathcal V)\oplus\Gamma(U_\infty,\mathcal V)
\longrightarrow\Gamma(U_0\cap U_\infty,\mathcal V).
$$

Pair it with the reversed Čech complex of $\mathcal V^\vee\otimes\omega_{\mathbf P^1}$ by taking the coefficient of $t^{-1}dt$. Boundaries annihilate cocycles by the residue theorem. After trivializing on the two charts, Gaussian elimination on the Laurent transition matrix splits both complexes into rank-one monomial complexes. For a monomial $t^n$, the surviving positive and negative Laurent coefficients pair one-for-one. Hence the induced pairing on cohomology is perfect. Finite direct image is exact, so this perfect pairing on $\pi_*\mathcal E$ is exactly the residue pairing on $C$. Thus

$$
H^1(C,\mathcal E)^\vee
\simeq H^0(C,\mathcal E^\vee\otimes\omega).
$$

Applying this to $\mathcal E^\vee\otimes\omega$ and using the canonical biduality of a vector bundle gives the degree-zero pairing as well. This proves fiberwise perfectness without importing a general duality theorem.

The residue construction commutes with extension of the ground field and with arbitrary base change in the relative family. Under the hypotheses of the theorem both sides of the displayed relative map are vector bundles and their fibers are the groups just paired. The map is therefore an isomorphism on every geometric fiber. Its kernel and cokernel are finite modules with zero residue fibers, hence vanish by Nakayama. $\square$

Taking $\mathcal E=\mathcal O_C$ gives

$$
f_*\omega_{C/S}\simeq(R^1f_*\mathcal O_C)^\vee.
$$

This is the precise duality interface used below. It requires no general duality statement in higher relative dimension.

### 9.3 Base change and the Hodge bundle

Assume the fibers of $C/S$ are geometrically connected of genus $g$. Then $f_*\mathcal O_C=\mathcal O_S$, $R^1f_*\mathcal O_C$ is locally free of rank $g$, and

$$
\mathbb E_C=f_*\omega_{C/S}
$$

is locally free of rank $g$. It commutes with every base change. We call $\mathbb E_C$ the **Hodge bundle** of the curve.

The assertion follows from Section 5.5 and relative duality. Notice the order of reasoning. Fiberwise dimension $g$ gives local constancy; base change in top degree starts the downward criterion; only then may one treat $f_*\omega$ as a vector bundle. Writing a determinant before proving local freeness would conceal the main issue.

For genus one with a section, $\omega_{C/S}$ is pulled back from $\mathbb E_C$ by translation, and $\mathbb E_C$ is a line bundle. A nowhere-vanishing invariant differential is therefore a trivialization of the Hodge line, not merely a differential chosen separately on each fiber.

### 9.4 Nodal and Gorenstein curves

If $f:C\to S$ is proper, flat, finitely presented, and Gorenstein of pure relative dimension one, there is an invertible relative dualizing sheaf $\omega_{C/S}$ even when fibers are nodal. At a node with local equation $xy=a$, a dualizing differential can be written

$$
\frac{dx}{x}=-\frac{dy}{y}.
$$

On the normalization of a nodal fiber, sections are meromorphic differentials with at most simple poles at the two branches and residues summing to zero. This residue condition makes the trace and the perfect pairings extend across the node.

The proof reduces to the smooth normalization and the exact sequence comparing functions on the curve with functions on its normalization. The cokernel is supported at the nodes. Dualizing that finite-length sequence turns the difference of values into the sum-of-residues condition. Fiberwise perfectness and coherent base change then give the relative pairing. If the family is not Gorenstein, the dualizing object need not be a line bundle; treating it as one would make the Hodge formulas false.

## 10. Proper curves and Picard representability

### 10.1 The relative Picard functor

Let $f:C\to S$ be proper, flat, and finitely presented with geometrically integral fibers, and suppose a section $e:S\to C$ is fixed. For an $S$-scheme $T$, begin with

$$
\operatorname{Pic}(C_T)/\operatorname{Pic}(T).
$$

Its associated fppf sheaf is denoted $\operatorname{Pic}_{C/S}$. The section gives a concrete equivalent description. A line bundle $\mathcal L$ on $C_T$ has the canonical relative representative

$$
\mathcal L\otimes f_T^*(e_T^*\mathcal L)^{-1},
$$

rigidified along $e_T$. Conversely, forgetting the rigidification gives a class modulo $\operatorname{Pic}(T)$. Because $f_{T*}\mathcal O_{C_T}=\mathcal O_T$, an automorphism of a rigidified line bundle is multiplication by a unit whose value at $e_T$ is one, hence is the identity. Faithfully flat descent of invertible modules is effective: on affine covers the descended module is the equalizer of the two pullbacks, and faithful flatness proves that this equalizer pulls back to the original module. Thus rigidified line bundles form an fppf sheaf of sets and identify with $\operatorname{Pic}_{C/S}$.

Degree is locally constant in flat families. Thus

$$
\operatorname{Pic}_{C/S}=\coprod_{d\in\mathbf Z}
\operatorname{Pic}^d_{C/S}.
$$

The central problem is to show that these sheaves are schemes of finite presentation, not infinite-dimensional collections of line bundles.

### 10.2 Divisors provide finite-dimensional charts

Assume now that $C/S$ is smooth and projective of genus $g$, with geometrically connected fibers. The relative symmetric power $C^{(d)}$ represents effective relative divisors of degree $d$. Sending a divisor $D$ to $\mathcal O_C(D)$ defines the Abel transformation

$$
a_d:C^{(d)}\longrightarrow\operatorname{Pic}^d_{C/S}.
$$

This notation does not assume the target is already represented: it is a natural transformation from a represented functor.

If $d\geq2g-1$, then for every degree-$d$ line bundle $L$ on a fiber,

$$
H^1(C_s,L)=0.
$$

Indeed, relative duality identifies its dual with $H^0(C_s,L^{-1}\otimes\omega)$, whose degree $2g-2-d$ is negative. A nonzero section would define an effective divisor of negative degree, impossible. It remains to calculate the Euler characteristic. Tensoring by the line bundle of one point changes Euler characteristic by one, as follows from

$$
0\to L(-x)\to L\to L|_x\to0.
$$

A nonzero rational section of $L$ writes it as $\mathcal O(D)$ for a Cartier divisor $D=\sum_x n_x[x]$. Applying the displayed exact sequence successively, with the reversed sequence for negative $n_x$, gives

$$
\chi(L)=\deg L+\chi(\mathcal O_C)=d+1-g,
$$

because a closed point contributes its residue-field degree. Since $H^1(C_s,L)=0$, this proves $h^0(L)=d+1-g$ without importing a stronger curve theorem.

In a family, semicontinuity and base change show that $p_*\mathcal L$ is locally free of that rank for any locally given universal degree-$d$ line bundle $\mathcal L$ on $C_T$. Its projective bundle of nonzero sections up to scalar parametrizes effective divisors whose associated line bundle is $\mathcal L$. Thus the fibers of $a_d$ are projective spaces of dimension $d-g$ and vary as projective bundles.

This is the decisive boundedness statement. Every degree-$d$ line bundle with $d\geq2g-1$ has a section, hence comes from a divisor; and the ambiguity in the divisor is a finite-rank projective bundle controlled by coherent base change.

### 10.3 The Picard scheme of a smooth proper curve

**Picard representability theorem for curves.** Let $S$ be locally noetherian and let $C\to S$ be smooth, projective, and finitely presented with geometrically connected fibers of genus $g$ and a section. Then the rigidified relative Picard sheaf is represented by a separated $S$-scheme locally of finite presentation. Each $\operatorname{Pic}^d_{C/S}$ is smooth and proper over $S$, and formation of the Picard scheme commutes with arbitrary base change.

**Proof.** Choose $n\geq2g-1-d$. Tensoring by $\mathcal O(ne)$ identifies degree $d$ with degree $m=d+n\geq2g-1$, so it suffices to construct the component in degree $m$. Book 8 proves that $Q=C^{(m)}$ represents effective relative divisors and carries a universal divisor $\Delta$. Write $p:C\times_SQ\to Q$. Section 10.2 and cohomology and base change give

$$
\mathcal E=p_*\mathcal O(\Delta),
\qquad \operatorname{rank}\mathcal E=m+1-g,
\qquad R^1p_*\mathcal O(\Delta)=0.
$$

For a divisor $D$, the complete linear system of divisors $E$ with $\mathcal O(E)\simeq\mathcal O(D)$ is the projective space of lines in $H^0(C,\mathcal O(D))$. With the quotient convention this is $\mathbf P_Q(\mathcal E^\vee)$. The universal line in $\mathcal E$ evaluates to a section of $\mathcal O(\Delta)$; its zero divisor defines a second map to $Q$. Thus

$$
R=\mathbf P_Q(\mathcal E^\vee)
\rightrightarrows Q
$$

represents the relation “the two divisors define the same rigidified line-bundle class.” A section with a prescribed zero divisor is unique up to one scalar, so $R\to Q\times_SQ$ is a monomorphism. It is proper, hence a closed immersion. The relation is therefore a closed equivalence relation, and either projection is a projective-space bundle of relative dimension $m-g$.

We record the quotient argument rather than assuming it. After an fppf base change, choose $m-g$ disjoint sections $x_1,\ldots,x_{m-g}$ of the curve. On the open locus where the evaluation map

$$
\mathcal E\longrightarrow
\bigoplus_{j=1}^{m-g}\mathcal O(\Delta)|_{x_j}
$$

is surjective, its kernel is a line bundle. Its unique line of sections selects one divisor in each complete linear system. These loci cover $Q$: on a geometric fiber, successively choose points away from the base locus so that each evaluation lowers the dimension of sections by one. The selected slices are schemes, and on overlaps the closed relation gives a unique transition isomorphism. Their cocycle identity follows from transitivity of linear equivalence. Affine-locally, effective faithfully flat descent is the equalizer construction for the coordinate algebras, so the slices descend and glue to a scheme $P^m$. By construction,

$$
\operatorname{Hom}_S(T,P^m)
\simeq Q(T)/R(T)
$$

after fppf sheafification. The universal divisor then identifies this quotient with rigidified degree-$m$ line bundles. Hence $P^m$ represents $\operatorname{Pic}^m_{C/S}$. The diagonal of $P^m$ pulls back to the closed relation $R$, so it is closed and $P^m$ is separated. The Abel map $Q\to P^m$ is fppf-locally a projective-space bundle, in particular proper and surjective. Properness descends after this faithfully flat cover, so $P^m$ is proper over $S$. Translation by $\mathcal O((d-m)e)$ constructs every other degree component.

All ingredients—symmetric powers, the universal divisor, the vector bundle $\mathcal E$, evaluation, and the descent slices—commute with arbitrary base change. Thus the representing scheme does as well.

Smoothness can be checked infinitesimally. It is enough to work fppf-locally with $T_0$ affine. For a square-zero extension $T_0\subset T$ with ideal $J$, the obstruction to lifting a line bundle lies in

$$
H^2(C_{T_0},J\otimes\mathcal O_{C_{T_0}})=0.
$$

Thus lifts exist locally; rigidified automorphisms vanish, and the difference between two lifts lies in $H^1(C_{T_0},J\otimes\mathcal O)$. This is the infinitesimal lifting criterion for smoothness. Its relative tangent space has rank $g$, so every component is smooth of relative dimension $g$. $\square$

The construction uses the selected Hilbert spaces of effective divisors and the coherent base-change theorem. It does not require a general parameter space for all quotients.

### 10.4 Tangent spaces, smoothness, and the Jacobian

Apply the square-zero calculation to $T=\operatorname{Spec}(k[\epsilon]/(\epsilon^2))$. A line bundle trivial modulo $\epsilon$ is glued by functions $1+\epsilon a_{ij}$. The cocycle condition says $(a_{ij})$ is a Čech $1$-cocycle; changing trivializations changes it by a coboundary. Hence

$$
T_0\operatorname{Pic}_{C_s/\kappa(s)}
\simeq H^1(C_s,\mathcal O_{C_s}).
$$

In families, the tangent bundle along the identity is $R^1f_*\mathcal O_C$, locally free of rank $g$. Its dual is the Hodge bundle $f_*\omega_{C/S}$.

The identity component

$$
\operatorname{Pic}^0_{C/S}
$$

is a smooth proper group scheme of relative dimension $g$, the Jacobian of $C/S$. The group law comes from tensor product of rigidified line bundles, inversion from dualization, and the identity from $\mathcal O_C$. Their compatibility with base change is functorial. The construction of canonical polarizations and detailed divisor theory belongs to the later study of Jacobians; the representability, smoothness, tangent space, and Hodge cotangent space are already consequences of the present cohomology.

## 11. Abelian schemes and their coherent cohomology

### 11.1 Invariant differentials

Let $p:A\to S$ be an abelian scheme of relative dimension $g$. In this book this means a projective, smooth, finitely presented commutative group scheme with geometrically connected fibers; projectivity, rather than only fiberwise properness, is part of the convention. Let $e:S\to A$ be its identity. Translation by a section $a\in A(T)$ identifies the cotangent spaces along $e_T$ and $a$. These identifications glue to an isomorphism

$$
p^*\omega_A\xrightarrow{\sim}\Omega^1_{A/S},
\qquad \omega_A=e^*\Omega^1_{A/S}.
$$

To see this, pull a differential back along multiplication $A\times_SA\to A$, then restrict one factor to the identity. The resulting invariant differential agrees with the original at $e$; translating shows equality everywhere. Since $\Omega^1_{A/S}$ is locally free of rank $g$, so is $\omega_A$. Its determinant

$$
\lambda_A=\det\omega_A
$$

is the Hodge line bundle. Both $\omega_A$ and $\lambda_A$ commute with arbitrary base change because relative differentials do for smooth morphisms and the identity section base-changes.

The relative canonical line is

$$
\omega_{A/S}^{\mathrm{top}}
=\bigwedge^g\Omega^1_{A/S}
\simeq p^*\lambda_A.
$$

It is not generally trivial on the total family: it is pulled back from the Hodge line on the base. Fiberwise it is trivial because the base line becomes one-dimensional.

### 11.2 The dual abelian scheme

For an $S$-scheme $T$, consider line bundles $\mathcal L$ on $A_T$ rigidified along the identity and algebraically equivalent to zero on every geometric fiber. Tensor product defines a group functor.

**Dual representability theorem.** If $A/S$ is an abelian scheme, this functor is represented by an abelian scheme $A^\vee/S$ of relative dimension $g$. It commutes with arbitrary base change and carries a universal rigidified line bundle

$$
\mathcal P\quad\text{on}\quad A\times_SA^\vee,
$$

the Poincaré bundle.

**Proof.** We first supply the group-theoretic ingredient used in the Hilbert construction. By the projectivity in the definition, locally on $S$ there is a relatively ample line bundle $L_0$. Rigidify it by tensoring with $p^*(e^*L_0)^{-1}$ and replace it by $L=L_0\otimes[-1]^*L_0$. The resulting $L$ is relatively ample, symmetric, and rigidified.

**Cube lemma.** If $L$ is a rigidified line bundle on an abelian scheme $A/S$, then on $A^3$ the alternating tensor product

$$
m_{123}^*L\otimes m_{12}^*L^{-1}\otimes m_{13}^*L^{-1}
\otimes m_{23}^*L^{-1}\otimes
\operatorname{pr}_1^*L\otimes\operatorname{pr}_2^*L\otimes\operatorname{pr}_3^*L
$$

is canonically trivial. To prove this, rigidify the displayed bundle on the three coordinate planes, where cancellation makes it trivial. A morphism from a proper connected fiber to the affine scheme of trivializations is constant: its coordinate functions are global functions and hence come from the base. Applying this rigidity observation successively in the three variables extends the coordinate-plane trivializations to all of $A^3$. Uniqueness along the identity makes the extensions agree. This proves the cube identity and, by fixing one variable, the theorem of the square

$$
t_{a+b}^*L\otimes L
\simeq t_a^*L\otimes t_b^*L.
$$

Now choose a relatively ample symmetric $L$. For an algebraically trivial rigidified $M$, the cube identity shows that $L^n\otimes M$ has the same fiber Hilbert polynomial as $L^n$ and that this polynomial is unchanged by translation. For $n$ large, higher cohomology vanishes and the bundle is generated by sections, uniformly on the base. Effective divisors in all $L^n\otimes M$ therefore lie in the one projective Hilbert scheme supplied by Book 8.

Pairs of these divisors defining the same rigidified line bundle form the projective bundle of their complete linear systems, exactly as in Section 10.3. Evaluation at finitely many relative points gives local slices; the equalizer construction for faithfully flat descent glues the slices. Hence the fppf sheaf of rigidified line bundles with this Hilbert polynomial is represented by a separated scheme locally of finite presentation. A rigidified line bundle $M$ on an abelian variety is algebraically equivalent to zero exactly when every $t_a^*M\otimes M^{-1}$ is trivial. Apply this test to the universal line bundle on $A\times A\times P$: triviality is the closed relation constructed from complete linear systems, and finite presentation makes it enough to impose the resulting universal coefficient equations. The cube identity shows that this locus is stable under tensor product and inversion. It therefore constructs a separated group scheme $P^0/S$ and a universal rigidified bundle on $A\times_SP^0$.

The remaining claims are checked without using structure-sheaf cohomology. The ample bundle defines

$$
\phi_L:A\longrightarrow P^0,
\qquad a\longmapsto t_a^*L\otimes L^{-1}.
$$

The theorem of the square makes this a homomorphism. Its kernel is finite: if a positive-dimensional subgroup fixed $L$, the restriction of $L$ to an orbit of that subgroup would be translation-invariant and hence numerically trivial, contradicting ampleness. On each geometric fiber, intersection with $g$ general translates of a divisor in a high power of $L$ shows that the finite kernel has positive length and that the image has dimension $g$. The local-slice construction shows that every algebraically trivial class lies in this image after a finite extension. Thus $\phi_L$ is finite and surjective on geometric fibers. Properness makes it finite globally, and translation identifies all local flatness defects; since its source and target have the same fiber dimension and its fiber length is locally constant, the local flatness criterion makes it finite locally free. Smoothness and properness descend along this faithfully flat map from $A$ to $P^0$. Therefore $P^0$ is an abelian scheme of relative dimension $g$; set $A^\vee=P^0$.

Every step is functorial under base change. The initial ample bundle was only auxiliary: two choices represent the same fppf functor and hence give a unique isomorphism. The universal rigidified line bundle is the Poincaré bundle. $\square$

The tangent space follows directly from the square-zero gluing calculation:

$$
\operatorname{Lie}(A^\vee/S)=R^1p_*\mathcal O_A,
\qquad
R^1p_*\mathcal O_A\simeq\omega_{A^\vee}^\vee.
$$

This calculation also proves that $R^1p_*\mathcal O_A$ is finite locally free of rank $g$ and commutes with arbitrary base change, because $A^\vee/S$ is smooth and its Lie algebra does.

### 11.3 The exterior algebra theorem

The structure-sheaf cohomology of an abelian scheme is controlled by degree one.

**Exterior algebra theorem.** For an abelian scheme $p:A\to S$ of relative dimension $g$,

$$
R^ip_*\mathcal O_A
\simeq\bigwedge^iR^1p_*\mathcal O_A,
\qquad 0\leq i\leq g,
$$

and $R^ip_*\mathcal O_A=0$ for $i>g$. Every displayed sheaf is finite locally free, its rank is $\binom gi$, and its formation commutes with arbitrary base change.

**Proof.** It is enough first to work over an algebraically closed field $k$. Let $q:A\times A^\vee\to A^\vee$ and let $\mathcal P$ be the Poincaré bundle. We use two elementary consequences of the cube lemma.

First, if $M\in A^\vee(k)$ is nontrivial, then $H^i(A,M)=0$ for every $i$. Indeed, the theta group of $M$ consists of pairs $(a,\alpha)$ with $\alpha:t_a^*M\simeq M$. It is a central extension of $A$ by $\mathbf G_m$. A nonzero cohomology class would give a projective representation of $A$ on a finite-dimensional cohomology space. A morphism from the proper connected scheme $A$ to the affine group $\operatorname{PGL}$ is constant, so the projective representation is trivial. The central action then supplies a splitting of the theta extension, and restricting that splitting along the identity says that $M$ has a nowhere-vanishing global section. A degree-zero bundle with such a section is trivial, a contradiction.

Second, formal functions identifies the completion of $Rq_*\mathcal P$ at the identity with a Koszul complex. To see the differential, let $\mathfrak m$ be the ideal of the identity in the smooth $g$-fold $A^\vee$. The restriction of $\mathcal P$ to the first infinitesimal neighborhood is its universal deformation class

$$
\mathrm{id}\in
H^1(A,\mathcal O_A)\otimes_k\mathfrak m/\mathfrak m^2.
$$

The tangent calculation above identifies the two factors as dual $g$-dimensional spaces. On successive powers $\mathfrak m^n/\mathfrak m^{n+1}$, the cube identity says that the connecting map is exterior multiplication by this universal class. Induction on $n$ therefore identifies the completed complex with the Koszul complex of a regular system of parameters of $\widehat{\mathcal O}_{A^\vee,0}$, shifted by $-g$. The acyclicity away from the identity proved in the preceding paragraph shows that there is no additional summand. Thus

$$
Rq_*\mathcal P\simeq e_*\mathcal N[-g]
$$

for a one-dimensional $k$-space $\mathcal N$. Derived pullback to the identity is the Koszul self-intersection, whose cohomology is the exterior algebra on the conormal space. Proper base change identifies that derived fiber with $R\Gamma(A,\mathcal O_A)$. Consequently cup product gives

$$
\bigwedge^iH^1(A,\mathcal O_A)
\xrightarrow{\sim}H^i(A,\mathcal O_A),
$$

and the dimensions are $\binom gi$.

Return to $S$. Cup product defines maps

$$
\bigwedge^iR^1p_*\mathcal O_A\longrightarrow R^ip_*\mathcal O_A.
$$

After tensoring with a residue field and then applying the base-change map, this is the exterior-algebra isomorphism just proved over the geometric fiber. It follows at once that every residue-field base-change map $\beta_s^i$ is surjective. The exact criterion of Section 5.2 now gives arbitrary base change in every degree and, using the adjacent surjectivity, finite local freeness. The relative cup-product map is an isomorphism on every geometric fiber, so its kernel and cokernel vanish by Nakayama. $\square$

The group law is essential. A general smooth proper $g$-fold does not have structure-sheaf cohomology generated in degree one, nor binomial Hodge numbers.

The top exterior power gives

$$
R^gp_*\mathcal O_A
\simeq\det(R^1p_*\mathcal O_A)
\simeq\lambda_{A^\vee}^\vee.
$$

Exterior multiplication consequently gives perfect pairings

$$
R^ip_*\mathcal O_A\otimes
R^{g-i}p_*\mathcal O_A\longrightarrow\lambda_{A^\vee}^\vee.
$$

### 11.4 Polarizations and base change

A line bundle $L$ on $A$ defines

$$
\phi_L:A\longrightarrow A^\vee,\qquad
a\longmapsto t_a^*L\otimes L^{-1}.
$$

The theorem of the square proves that $\phi_L$ is a homomorphism: expanding the expression at $a+b$ cancels the cross terms. If $L$ is relatively ample, $\phi_L$ is finite and surjective on every geometric fiber, hence finite locally free after the usual constant-degree condition. It is a polarization.

Here the constant-degree condition is automatic on each connected component of $S$. The kernel is proper and has zero-dimensional fibers, hence is finite. Translation identifies its local rings over a fiber, while the intersection number of $L$ is locally constant in the flat family and gives the fiber length. The local flatness criterion therefore makes the kernel finite locally free, and the quotient map $A\to A/\ker\phi_L=A^\vee$ is finite locally free.

Every part of the construction commutes with base change. In particular, the kernel, degree, and induced map on Hodge bundles specialize correctly. The cotangent map at the identity is

$$
\omega_{A^\vee}\longrightarrow\omega_A.
$$

For a principal polarization it is an isomorphism. This self-duality will later identify the two halves of the Hodge data in symplectic moduli problems; here it is simply a morphism of finite locally free sheaves justified by coherent base change.

## 12. Hodge bundles in low-dimensional PEL families

### 12.1 What is assumed and what is proved

A PEL family in this chapter means an abelian scheme $A\to T$ of relative dimension $g\leq2$, together with an action

$$
\iota:\mathcal O\longrightarrow\operatorname{End}_T(A)
$$

of a fixed finite free order, a polarization compatible with a chosen involution on $\mathcal O$, and any finite level structure already defined over $T$. We do not construct a parameter space for these data. Given such a family, we prove the coherent statements that are stable under changing $T$: local freeness and decomposition of Hodge bundles, closed rank conditions, finite modules of sections on a proper parameter space, and exact coefficient-change criteria.

This boundary is important. Cohomology can show that a condition on an existing universal family is closed or that its sections are finite. It cannot by itself supply the universal family, compactification, or level structure.

### 12.2 Endomorphisms and decompositions

The action on $A$ differentiates to an action of $\mathcal O$ on

$$
\omega_A=e^*\Omega^1_{A/T}
$$

and hence on $\lambda_A=\det\omega_A$. Suppose a commutative suborder $\mathcal C\subseteq\mathcal O$—usually the center or a prescribed maximal commutative subalgebra—becomes split étale on $T$, so that

$$
\mathcal C\otimes_{\mathbf Z}\mathcal O_T
\simeq\prod_{\tau} \mathcal O_T
$$

through orthogonal idempotents $e_\tau$. Then

$$
\omega_A=\bigoplus_\tau\omega_\tau,
\qquad \omega_\tau=e_\tau\omega_A.
$$

Each summand is finite locally free because the image of an idempotent on a vector bundle is a direct summand. Its rank is locally constant. The determinant condition prescribing ranks $r_\tau$ is therefore open and closed.

In dimension one this gives the familiar Hodge line. In dimension two, the possibilities include one rank-two bundle, two Hodge lines, or conjugate rank-one pieces tied together by the polarization. If a principal polarization exchanges the relevant idempotents under the involution, the cotangent isomorphism $\omega_{A^\vee}\simeq\omega_A$, together with $R^1p_*\mathcal O_A\simeq\omega_{A^\vee}^\vee$, identifies the corresponding Hodge and Lie summands. These statements use only idempotent decomposition and the cotangent map of Section 11.4; no classification of the parameter problem is needed.

### 12.3 Determinants, ranks, and bad primes

At a prime where $\mathcal C$ is not étale over the base, the idempotents may not exist. One must not write a direct sum indexed by embeddings. The integral replacement fixes, as part of the PEL datum, a polynomial law $P_a(T)$ for every $a\in\mathcal O$; on the split generic locus it has the form

$$
P_a(T)=\prod_\tau(T-\tau(a))^{r_\tau}.
$$

The determinant condition is

$$
\det(T-\iota(a)\mid\omega_A)=P_a(T)
\qquad\text{for every }a\in\mathcal O.
$$

It is nevertheless a finite closed condition. Choose a $\mathbf Z$-basis $a_1,\ldots,a_r$ of the finite free order, insert the universal element $a_{\mathrm{univ}}=\sum X_ja_j$, and compare coefficients of the two polynomials in $T,X_1,\ldots,X_r$. There are finitely many coefficient equations, and their vanishing is equivalent to the identity after every specialization of the $X_j$. On the locus where $\mathcal C$ is split étale, the restriction of the determinant condition to $\mathcal C$ is equivalent to the rank decomposition above.

This explains a typical special-fiber phenomenon. Two eigenspaces distinct in characteristic zero can coalesce modulo a ramified prime. The total Hodge bundle remains locally free of rank $g$, but the individual characteristic-zero summands need not extend as vector bundles. Determinant equations survive because they avoid choosing idempotents.

For the low-dimensional families considered here, these rank and determinant equations are the coherent conditions we use. Even in dimension two, one must not infer that they define a flat parameter space at a ramified prime: a particular ramified unitary problem can require an additional incidence or wedge condition. Such a condition is again expressed as vanishing of a map between finite exterior powers of the Hodge bundle, hence is closed and commutes with base change. Determining which extra condition gives the correct flat parameter space is separate local geometry, not a consequence of coherent cohomology.

### 12.4 Compactifications and boundary behavior

Suppose a low-dimensional PEL parameter scheme $M$ and an abelian scheme $A/M$ are already given. Then $\lambda_A$ is a line bundle and

$$
H^0(M,\lambda_A^k)
$$

is finite over the base whenever $M$ is proper and noetherian. If $M$ is not proper, this finiteness need not hold.

Often one has a proper compactification $\bar M$ with boundary divisor $D$ and an extension $\bar\lambda$ of the Hodge line. The present theory applies once these objects are given and coherent. It proves finiteness of $H^i(\bar M,\bar\lambda^k(-D))$, semicontinuity in a flat family, and base change under the adjacent-degree criteria. It does not prove that $\bar M$, $D$, or $\bar\lambda$ exists. That geometric construction is a separate input.

If $\bar M$ is a curve or surface, coherent cohomology vanishes above degree one or two respectively. This small amplitude makes reduction questions tractable: on a curve, only $H^1$ can obstruct base change of global sections; on a surface, both $H^1$ and $H^2$ enter, and constancy of Euler characteristic alone cannot distinguish them.

## 13. Integral modular forms as coherent sections

### 13.1 The geometric definition

Let $R$ be a noetherian ring and let $q:Y\to\operatorname{Spec}R$ be a proper flat finitely presented curve that is already known to carry the relevant compactified modular interpretation. Assume its universal generalized elliptic family supplies an invertible Hodge sheaf $\omega$ on $Y$. For $k\geq0$, define

$$
M_k(Y/R)=H^0(Y,\omega^k).
$$

An element is an integral modular form of weight $k$ for this given modular problem. The transformation law is built into the line bundle: trivializing $\omega$ by an invariant differential turns a section into a function, and rescaling the differential by $u$ rescales that function by $u^{-k}$ under the quotient convention.

This definition is geometric and integral. It requires neither a complex variable nor division by the level. It also makes the foundational boundary exact: the present book studies sections once $Y$ and $\omega$ exist; it does not assert the representability or compactification of a modular problem.

### 13.2 Finiteness and change of coefficients

Proper finiteness immediately gives:

**Integral finiteness theorem.** The $R$-module $M_k(Y/R)$ is finite. If $R\to R'$ is flat, then

$$
M_k(Y/R)\otimes_RR'\xrightarrow{\sim}
M_k(Y_{R'}/R')
$$

provided $\omega$ pulls back to the Hodge sheaf of the changed family.

For a nonflat $R'$, ordinary cohomology need not commute with extension of scalars. Because $Y/R$ is a curve, a finite complex in degrees zero and one governs $\omega^k$. When $R'=R/I$ and the quotient has Tor dimension at most one, the exact sequence is

$$
0\to M_k(Y/R)\otimes_RR/I
\to M_k(Y_{R/I}/(R/I))
\to\operatorname{Tor}_1^R
\bigl(H^1(Y,\omega^k),R/I\bigr)\to0.
$$

Thus reduction creates extra modular forms exactly from torsion in $H^1(Y,\omega^k)$. If $R$ is a discrete valuation ring with uniformizer $\pi$, the last term is the $\pi$-torsion of $H^1(Y,\omega^k)$.

For $k\gg0$, ampleness of $\omega$—when it is known for the given compactification—implies $H^1(Y,\omega^k)=0$. Then $M_k$ is locally free and commutes with every coefficient change. If $\omega$ is not ample, eventual vanishing cannot be inferred merely from its name as a Hodge bundle.

### 13.3 Cusp forms and the boundary

Let $D\subset Y$ be a finite flat effective Cartier divisor marking the cusps. Define

$$
S_k(Y/R)=H^0(Y,\omega^k(-D)).
$$

The exact sequence

$$
0\to\omega^k(-D)\to\omega^k\to\omega^k|_D\to0
$$

shows that a modular form is cuspidal exactly when its restriction to every cusp vanishes scheme-theoretically. The quotient is finite locally free over $R$ when $D/R$ is finite locally free. Its connecting map gives

$$
0\to S_k(Y/R)\to M_k(Y/R)\to
H^0(D,\omega^k|_D)\to H^1(Y,\omega^k(-D)).
$$

Consequently surjectivity of evaluation at the cusps is controlled by the last $H^1$. This remains meaningful over nonreduced bases: vanishing on the underlying cusp points is weaker than vanishing on the Cartier divisor.

If $\omega^k(-D)$ is sufficiently positive, its $H^1$ vanishes, cusp evaluation is onto, and both modular and cusp forms commute with arbitrary base change. The proof is relative Serre vanishing followed by the exact base-change theorem.

### 13.4 The exact base-change test

Let $s\in\operatorname{Spec}R$. The reduction map

$$
M_k(Y/R)\otimes\kappa(s)\longrightarrow
H^0(Y_s,\omega_s^k)
$$

is surjective if and only if the outgoing differential in degree zero of a local minimal cohomology complex vanishes. When it is surjective, it is an isomorphism after every base change near $s$, and $M_k(Y/R)$ is finite locally free there; for degree zero there is no preceding base-change condition. If the quotient map $R\to\kappa(s)$ has Tor dimension at most one, the universal-coefficient sequence identifies this surjectivity exactly with the vanishing of

$$
\operatorname{Tor}_1^R(H^1(Y,\omega^k),\kappa(s)).
$$

Over a discrete valuation ring, the statement is particularly transparent:

$$
M_k(Y/R)\otimes_RR/\pi
\xrightarrow{\sim}M_k(Y_{R/\pi}/(R/\pi))
$$

if and only if $H^1(Y,\omega^k)$ has no $\pi$-torsion. The same criterion with $\omega^k(-D)$ governs cusp forms. This is the exact integral content of “forms reduce correctly”; a dimension comparison over the fraction field and residue field is only a consequence.

## 14. Representability consequences and their boundary

### 14.1 A coherent representability package

The arguments above repeatedly use one pattern. Let $f:X\to S$ be projective, flat, and finitely presented, with $S$ locally noetherian, and let $\mathcal F$ be coherent and $S$-flat. On an open where $R^1f_*\mathcal F=0$, the sheaf $f_*\mathcal F$ is finite locally free and commutes with arbitrary base change. Therefore the functor

$$
T\longmapsto H^0(X_T,\mathcal F_T)
$$

is represented by the affine bundle

$$
\mathbf V((f_*\mathcal F)^\vee)
=\operatorname{Spec}_S\operatorname{Sym}((f_*\mathcal F)^\vee).
$$

Indeed, a map $T\to\mathbf V(\mathcal E^\vee)$ is a section of $\mathcal E_T$, and base change identifies this with a section of $\mathcal F_T$. Under the quotient convention of Book 8, nowhere-zero sections up to scaling are line subbundles of $\mathcal E_T$ and are represented by $\mathbf P_S(\mathcal E^\vee)$. Vanishing along a fixed finite flat subscheme is the zero locus of the restriction map between the associated affine bundles; when its cokernel is flat, its kernel is itself a vector subbundle.

This elementary representability result is the local engine behind Abel maps, divisors in a fixed line bundle, Hodge tensors, and spaces of forms. It requires vanishing or the exact base-change criterion; a merely coherent pushforward need not represent fiberwise sections correctly.

### 14.2 Curves, abelian schemes, and PEL data

For a smooth proper curve with a section, high-degree divisors form a symmetric power and their linear systems are projective bundles. Their quotient represents the Picard scheme. Degree-one cohomology gives its tangent bundle, and vanishing of degree two makes it smooth.

For an abelian scheme, high ample divisors again give a bounded Hilbert construction. The theorem of the cube cuts out algebraically trivial rigidified classes, giving the dual abelian scheme. Its tangent and cotangent bundles are respectively $R^1p_*\mathcal O_A$ and $\omega_{A^\vee}$.

For a given low-dimensional PEL family, idempotent rank conditions are open and closed on the unramified locus, while characteristic-polynomial conditions are closed integrally. A prescribed Hodge tensor is the zero locus or fixed locus of a map between finite locally free sheaves. A choice of a Hodge section is represented by an affine bundle, and a line in a rank-two Hodge bundle by a projective bundle. These are genuine representability consequences. They do not amount to construction of the entire PEL parameter space, which also requires group objects, level structures, descent, and compactification.

### 14.3 Failures when hypotheses are weakened

The following boundary cases summarize why the hypotheses have been repeated.

- If $f$ is not proper, $f_*\mathcal F$ can be infinitely generated and formal functions can fail.

- If $\mathcal F$ is not coherent, properness does not force finite cohomology.

- If $\mathcal F$ is not flat over the base, ordinary fibers omit Tor and semicontinuity in the stated form can fail.

- If fiber dimensions jump, higher direct images need not be vector bundles; the Poincaré bundle on an elliptic curve gives a basic example.

- If an order ramifies on the base, characteristic-zero Hodge eigenspaces may merge and must be replaced by determinant equations.

- If a compactified modular or PEL family is not already constructed, coherent finiteness does not construct it.

- If a dualizing sheaf is not invertible, determinant formulas requiring a dualizing line are invalid.

Each failure has the same moral: a fiberwise slogan loses extension, nilpotent, or boundary information. Finite complexes and coherent sheaves preserve it.

## 15. Synthesis

### 15.1 The chain of implications

The theory can be read as one chain:

$$
\begin{array}{c}
\text{properness and coherence}\\
\Downarrow\\
\text{finite higher direct images}\\
\Downarrow\quad\text{with flatness}\\
\text{finite complexes controlling fibers}\\
\Downarrow\\
\text{semicontinuity and exact base-change criteria}\\
\Downarrow\\
\text{local freeness, flattening, and uniform linear systems}\\
\Downarrow\\
\text{Picard charts, Hodge bundles, and finite spaces of forms}.
\end{array}
$$

In a different direction, noetherian finiteness plus Artin--Rees gives

$$
\text{proper cohomology}
\Longrightarrow
\text{formal functions}
\Longrightarrow
\text{control by all infinitesimal neighborhoods}.
$$

The derived language supplies the maps and remembers Tor and inverse-limit terms. The coherent language supplies finite modules, vector bundles, rank loci, and parameter spaces. Passing from the first to the second is justified only after boundedness, finite generation, and the adjacent-degree tests have been checked.

### 15.2 A theorem checklist for later use

Every scheme separated and of finite type over a noetherian affine base admits, by Chow's lemma of Section 2.4, a projective surjection from a scheme quasi-projective over that base which is an isomorphism over a dense open; when the scheme is proper, the source is projective over the base. For a proper morphism of locally noetherian schemes and a coherent sheaf, all higher direct images are coherent. For a proper finitely presented family and a base-flat coherent sheaf, a bounded finite locally free complex exists locally on the base and governs arbitrary coefficient modules. Fiber cohomology dimensions are upper semicontinuous, and Euler characteristic is locally constant.

At a point, surjectivity of the degree-$i$ base-change map persists nearby. Under that surjectivity, $R^if_*\mathcal F$ is locally free exactly when base change is also surjective in degree $i-1$. When both adjacent conditions hold, degree-$i$ cohomology commutes with arbitrary base change. Flat base change needs no local-freeness conclusion.

For a coherent ideal on a noetherian base, the completion of $R^if_*\mathcal F$ is the inverse limit of cohomology on infinitesimal thickenings. If the base is complete, finite cohomology is recovered from that limit. This is a statement about a sheaf already present on the proper family, not an unrestricted existence theorem for completed objects.

For smooth proper geometrically connected curves, $R^1f_*\mathcal O$ and $f_*\omega$ are dual vector bundles. When the family is projective and has a section, its rigidified Picard scheme is smooth, proper in each degree, and compatible with arbitrary base change. For abelian schemes, structure-sheaf cohomology is the exterior algebra on degree one, the Hodge bundle is finite locally free, and algebraically trivial rigidified line bundles form the dual abelian scheme.

Given a proper low-dimensional PEL or modular family, Hodge bundles, their integral determinant conditions, modular forms, and cusp forms are coherent constructions. Their modules of sections are finite. Reduction of forms is exact precisely when the neighboring coherent cohomology contributes no Tor.

### 15.3 Conclusion

Coherent cohomology in a proper family is finite linear algebra carrying geometric memory. The matrices in a finite complex remember how fiber classes appear and disappear. Their minors draw the jumping loci. Their neighboring differentials decide whether cohomology is a vector bundle. Their reductions record torsion, and their completions gather every infinitesimal neighborhood into one finite module.

That linear algebra is powerful because its hypotheses are geometric. Properness closes the boundary, coherence bounds the data, flatness makes fibers honest tensor products, finite presentation makes rank conditions visible, and noetherianity makes completion exact. Relative duality then turns degree-one cohomology into Hodge cotangent data. On curves it yields Picard schemes; on abelian schemes it yields the dual family and exterior cohomology; on a given PEL or modular family it yields integral Hodge bundles and finite modules of forms.

The resulting toolkit is deliberately exact about its frontier. It proves the cohomological and representability consequences available from proper projective geometry and derived comparison. It does not assume later constructions of modular or PEL parameter spaces, nor does it turn completed data into algebraic objects without an existence theorem. Within that frontier, finiteness, semicontinuity, base change, formal functions, duality, and Hodge theory form one coherent mechanism.
