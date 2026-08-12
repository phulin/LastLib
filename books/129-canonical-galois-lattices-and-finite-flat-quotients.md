# Galois Lattices and Finite-Flat Closures in Abelian Tate Modules

## Contents

1. [The integral question and its honest scope](#1-the-integral-question-and-its-honest-scope)
   - [From a rational constituent to a torsion tower](#11-from-a-rational-constituent-to-a-torsion-tower)
   - [The local setting and the finite-flat normalization](#12-the-local-setting-and-the-finite-flat-normalization)
   - [Existence, homothety, and canonicality](#13-existence-homothety-and-canonicality)
2. [Saturated lattices in a fixed Tate module](#2-saturated-lattices-in-a-fixed-tate-module)
   - [Scaling and intersection](#21-scaling-and-intersection)
   - [The saturated-intersection theorem](#22-the-saturated-intersection-theorem)
   - [Stable lattices and residual irreducibility](#23-stable-lattices-and-residual-irreducibility)
3. [Finite torsion inside an abelian scheme](#3-finite-torsion-inside-an-abelian-scheme)
   - [Good reduction supplies the ambient groups](#31-good-reduction-supplies-the-ambient-groups)
   - [Putting each coefficient quotient into geometric torsion](#32-putting-each-coefficient-quotient-into-geometric-torsion)
   - [Finite-flat closure, rank, and ambient uniqueness](#33-finite-flat-closure-rank-and-ambient-uniqueness)
4. [Why the levels form one exact tower](#4-why-the-levels-form-one-exact-tower)
   - [The gap between levelwise closure and exactness](#41-the-gap-between-levelwise-closure-and-exactness)
   - [The Raynaud rigidity range](#42-the-raynaud-rigidity-range)
   - [Exact multiplication sequences](#43-exact-multiplication-sequences)
   - [Transitivity and recovery of the lattice](#44-transitivity-and-recovery-of-the-lattice)
5. [The finite-flat closure-tower theorem](#5-the-finite-flat-closure-tower-theorem)
   - [Complete statement](#51-complete-statement)
   - [Proof of the theorem](#52-proof-of-the-theorem)
   - [Localizations of number fields](#53-localizations-of-number-fields)
6. [Cartier duality, determinants, and polarizations](#6-cartier-duality-determinants-and-polarizations)
   - [The dual tower and its coefficient action](#61-the-dual-tower-and-its-coefficient-action)
   - [Determinants are generic data carried by the lattice](#62-determinants-are-generic-data-carried-by-the-lattice)
   - [Polarizations and the two separate unit tests](#63-polarizations-and-the-two-separate-unit-tests)
7. [Ground-field and coefficient change](#7-ground-field-and-coefficient-change)
   - [Flat change of the valuation ring](#71-flat-change-of-the-valuation-ring)
   - [Extension of the coefficient DVR](#72-extension-of-the-coefficient-dvr)
   - [The different and duality after coefficient extension](#73-the-different-and-duality-after-coefficient-extension)
8. [How a curve packet supplies the rational plane](#8-how-a-curve-packet-supplies-the-rational-plane)
   - [A nonzero oldvector gives an embedding](#81-a-nonzero-oldvector-gives-an-embedding)
   - [Passing from cohomology to the finite-flat normalization](#82-passing-from-cohomology-to-the-finite-flat-normalization)
   - [What saturation proves and what it does not](#83-what-saturation-proves-and-what-it-does-not)
9. [The unramified Fontaine--Laffaille realization](#9-the-unramified-fontaine--laffaille-realization)
   - [The same tower in filtered form](#91-the-same-tower-in-filtered-form)
   - [Changing a stable lattice by commensurability](#92-changing-a-stable-lattice-by-commensurability)
   - [The prime-two and ramified boundaries](#93-the-prime-two-and-ramified-boundaries)
10. [Exact handoffs to the later arithmetic books](#10-exact-handoffs-to-the-later-arithmetic-books)
    - [Compatible systems and potential modularity](#101-compatible-systems-and-potential-modularity)
    - [Changing the coefficient prime and the fixed-three argument](#102-changing-the-coefficient-prime-and-the-fixed-three-argument)
11. [Hostile audit and conclusion](#11-hostile-audit-and-conclusion)
    - [Dependency and hypothesis audit](#111-dependency-and-hypothesis-audit)
    - [Failure tests](#112-failure-tests)
    - [Conclusion](#113-conclusion)

## 1. The integral question and its honest scope

### 1.1 From a rational constituent to a torsion tower

A two-dimensional $p$-adic representation obtained from the first cohomology of a curve is initially a rational object. Arithmetic applications need more. They need one named stable lattice $T$, all of its quotients $T/\varpi^nT$, finite locally free group schemes realizing those quotients at places above $p$, coefficient actions on the group schemes, and exact reduction maps joining all levels. A proof at level one does not supply the higher tower, and a collection of unrelated finite-flat models does not supply exact transition maps.

There are two distinct operations in the construction. The first is linear: intersect a rational Galois-stable plane with a fixed ambient Tate lattice and saturate. The second is geometric: view each finite quotient as a subgroup of the generic torsion of an abelian scheme and take its schematic closure. Over a discrete valuation ring, closure is finite flat because saturation of the defining Hopf ideal removes vertical torsion.

That levelwise argument is not yet the whole theorem. If $\mathcal G_{n+1}$ and $\mathcal G_n$ are constructed in different ambient torsion groups, the generic reduction map

$$
T/\varpi^{n+1}T\longrightarrow T/\varpi^nT
$$

need not extend to a faithfully flat integral map merely because both endpoints are finite flat. Generic fiber is faithful on finite-flat groups over a DVR, but it is not generally full. The exact tower therefore requires a rigidity theorem. The proved range used here is Raynaud's range

$$
e(R)=v_R(p)<p-1. \tag{1.1}
$$

This includes every absolutely unramified base at an odd prime. In that range generic fiber is fully faithful on finite flat commutative groups of $p$-power order. It turns the quotient of one closed level by the closure of its generic kernel into the already constructed lower level, and this is the decisive all-level argument.

The result is deliberately an existence theorem relative to a fixed geometric carrier. It does not construct a rational projector, an integral Morita splitting, or a lattice independent of arbitrary PEL presentations. Those stronger claims are neither needed for the Fermat spine nor supplied by the curve-extraction theorems.

### 1.2 The local setting and the finite-flat normalization

Fix a prime $p$. Let $R$ be a mixed-characteristic DVR with fraction field $K$, perfect residue field $k$ of characteristic $p$, and absolute ramification index $e=v_R(p)$. We first suppose that $R$ is henselian. Section 5.3 explains how to work over a nonhenselian localization by passing faithfully flatly to its henselization.

Let $\mathcal O$ be the ring of integers of a finite extension $L/\mathbf Q_p$, let $\varpi$ be a uniformizer, and let $\kappa=\mathcal O/\varpi$ have cardinality $q$. Let $\mathcal A/R$ be an abelian scheme and put $A=\mathcal A_K$. An action by a coefficient order on $\mathcal A$, after completion at a chosen coefficient place, is assumed to give a continuous $\mathcal O$-action on the Tate module used below. We impose the concrete freeness hypothesis

$$
M=T_pB
\quad\text{is finite free over }\mathcal O, \tag{1.2}
$$

where $B$ is one of the following two abelian varieties with good reduction:

- $B=A$, for the covariant Tate-module normalization;
- $B=A^\vee$, for the Cartier-twisted dual normalization

  $$
  T_pA^\vee\simeq\operatorname{Hom}_{\mathbf Z_p}(T_pA,\mathbf Z_p)(1). \tag{1.3}
  $$

Replacing $A$ or $A^\vee$ by a finite power is allowed and is often necessary. In particular, if a constituent first lies in $T_pA\otimes_{\mathbf Z_p}\mathcal O$, choose a $\mathbf Z_p$-basis of $\mathcal O$ and realize that lattice as the Tate module of $A^{[L:\mathbf Q_p]}$ with the regular coefficient action. This is a choice of carrier, not a canonical identification with the Tate module of $A$ itself.

The completed action in (1.2) can be obtained from an honest integral order action: modulo every $p^r$, an element of the completion is represented by an element of the order, and the resulting action on torsion is independent of the representative. Nothing requires a rational idempotent to act integrally.

Write $M_L=M\otimes_{\mathcal O}L$. The input rational representation is a $G_K$-stable $L$-plane

$$
W\hookrightarrow M_L. \tag{1.4}
$$

It is essential that (1.4) already use a finite-flat normalization. Untwisted cohomology of a curve is generally the negative Tate twist of a covariant Jacobian Tate module. The valid geometric conversion is

$$
H^1_{\mathrm{et}}(C_{\overline K},L)(1)
\hookrightarrow V_pJ_C, \tag{1.5}
$$

or equivalently a Cartier-twisted dual realization. No assertion in this book says that finite flatness survives an arbitrary negative Tate twist.

### 1.3 Existence, homothety, and canonicality

Three conclusions that are often conflated must remain separate.

**Existence** means that at least one stable rank-two $\mathcal O$-lattice in $W$ has been constructed, and that its finite quotients have compatible finite-flat models.

**Homothety** means that two stable lattices become equal after multiplication by an element of $L^\times$. Absolute irreducibility of a residual representation can force homothety. Homothety still leaves the power of $\varpi$ undetermined.

**Canonicality** would mean that the rational representation alone selects a distinguished lattice, or that arbitrary geometric presentations give the same embedded lattice. Neither follows. The intersection $M\cap W$ is distinguished only relative to the fixed embedding (1.4) and the fixed ambient lattice $M$. The schematic closure at level $n$ is unique only inside its fixed ambient torsion group. Raynaud full faithfulness gives unique isomorphisms of *marked finite-flat models* in the range (1.1), but the marking includes the already chosen finite Galois module $T/\varpi^nT$.

This hierarchy is the organizing discipline of the book. The construction proves existence unconditionally at each level and proves one exact compatible tower under (1.1). It proves homothety when residual absolute irreducibility is supplied. It never promotes those statements to independence of an arbitrary curve vector, an arbitrary isogeny, or an arbitrary PEL realization.

## 2. Saturated lattices in a fixed Tate module

### 2.1 Scaling and intersection

Let $T_0$ be any full $\mathcal O$-lattice in the abstract plane $W$. Because (1.4) is rational, there is $c\in L^\times$ such that

$$
cT_0\subset M. \tag{2.1}
$$

Scaling is only a way to put a chosen set of generators into the ambient lattice. It does not select a final lattice: multiplying the embedding by a nonzero scalar does not change its image subspace in $M_L$. The intrinsic operation relative to $M$ and $W$ is

$$
T=M\cap W. \tag{2.2}
$$

The intersection contains the scaled lattice in (2.1), so it has full rank in $W$. More importantly, it is saturated in $M$. This is the property that later makes every quotient $T/\varpi^nT$ inject into the appropriate ambient quotient.

### 2.2 The saturated-intersection theorem

**Proposition 2.1 (saturated intersection).** Let $\mathcal O$ be a DVR, let $M$ be a finite free $\mathcal O$-module, and let $W\subset M_L$ be an $L$-subspace. Then $T=M\cap W$ has the following properties.

1. $T$ is a free $\mathcal O$-lattice in $W$.
2. $T$ is saturated in $M$, so $M/T$ is torsion-free.
3. For every $n\geq1$,

   $$
   T\cap\varpi^nM=\varpi^nT, \tag{2.3}
   $$

   and hence $T/\varpi^nT\to M/\varpi^nM$ is injective.
4. Every group or algebra preserving both $M$ and $W$ preserves $T$.
5. For a flat extension of coefficient DVRs $\mathcal O\to\mathcal O'$, with fraction field $L'$, one has

   $$
   T\otimes_{\mathcal O}\mathcal O'
   =(M\otimes_{\mathcal O}\mathcal O')
   \cap(W\otimes_LL'). \tag{2.4}
   $$

**Proof strategy.** The quotient $M/T$ embeds in the vector-space quotient $M_L/W$. That proves saturation. All other claims follow from this one-dimensional torsion-free calculation.

The composite $M\to M_L\to M_L/W$ has kernel $M\cap W=T$. Thus

$$
M/T\hookrightarrow M_L/W. \tag{2.5}
$$

The target is an $L$-vector space, so $M/T$ has no $\mathcal O$-torsion. Over a DVR, a finite torsion-free module is free. The same is true of $T$. Clearing denominators in an $L$-basis of $W$ shows that $T$ spans $W$, proving the first two assertions.

If $x\in T\cap\varpi^nM$, write $x=\varpi^ny$ with $y\in M$. Since $x\in W$ and $W$ is an $L$-space, $y\in W$. Hence $y\in M\cap W=T$, proving (2.3). Stability is immediate: an operator preserving the two sets preserves their intersection.

Finally tensor the saturated exact sequence

$$
0\longrightarrow T\longrightarrow M\longrightarrow M/T\longrightarrow0 \tag{2.6}
$$

with the flat module $\mathcal O'$. The quotient remains torsion-free, and its generic kernel is $W\otimes_LL'$. The characterization of a saturated lattice as the contraction of its generic span gives (2.4). $\square$

The proposition gives an abstract $\mathcal O$-module complement because $M/T$ is free, but such a complement is not unique and need not be Galois stable, coefficient stable, orthogonal, or geometric. No equivariant direct-summand claim is hidden in saturation.

### 2.3 Stable lattices and residual irreducibility

The lattice $T$ in (2.2) is $G_K$-stable because $M$ and $W$ are stable. Its construction does not require residual irreducibility. Irreducibility becomes relevant only when one compares $T$ with another stable lattice.

**Proposition 2.2 (homothety criterion).** Let $V$ be a two-dimensional $L$-representation of a group $\Gamma$. Suppose $T_1$ is a stable lattice and $T_1/\varpi T_1$ is absolutely irreducible over $\kappa$. Then every stable lattice $T_2\subset V$ is homothetic to $T_1$. Their residual representations are isomorphic.

**Proof.** Scale $T_2$ so that

$$
T_2\subset T_1,
\qquad
T_2\not\subset\varpi T_1. \tag{2.7}
$$

The image of $T_2$ in $T_1/\varpi T_1$ is a nonzero $\Gamma$-stable subspace. Absolute irreducibility makes it the whole residual space. Therefore

$$
T_1=T_2+\varpi T_1.
$$

Nakayama's lemma gives $T_1=T_2$. Undoing the scaling proves homothety. The equality after scaling also identifies the reductions. $\square$

Absolute irreducibility is the stable hypothesis under coefficient extension. A representation which is irreducible over $\kappa$ but not absolutely irreducible may split after enlarging the residue field. Conversely, absolute irreducibility remains absolute after a finite residue-field extension. If the residual representation is reducible, stable lattices can encode different nonsplit extensions and need not be homothetic. Their semisimplifications agree, but that weaker fact neither selects a lattice nor identifies finite-level extension classes.

Even under Proposition 2.2, a curve packet with a multidimensional oldspace can be embedded into cohomology by different nonproportional oldvectors. Pulling the resulting intersection lattices back to the same abstract $W$ makes them homothetic when the residual hypothesis holds; it does not make the embedded subspaces or the power of $\varpi$ canonical.

## 3. Finite torsion inside an abelian scheme

### 3.1 Good reduction supplies the ambient groups

For every integer $r\geq1$, multiplication by $p^r$ on the abelian scheme $\mathcal B/R$ is a finite locally free isogeny. Its kernel

$$
\mathcal B[p^r] \tag{3.1}
$$

is therefore a finite locally free commutative group scheme of rank $p^{2r\dim B}$. Formation of (3.1) commutes with arbitrary base change. Since $K$ has characteristic zero, the generic fiber is finite etale and its geometric points are the ordinary Galois module $B[p^r](\overline K)$.

The covariant Tate module and the full $p$-power torsion are related by a canonical exact sequence

$$
0\longrightarrow M\longrightarrow M\otimes_{\mathbf Z_p}\mathbf Q_p
\longrightarrow B[p^\infty](\overline K)\longrightarrow0. \tag{3.2}
$$

Concretely, the class of $p^{-r}x$, for a compatible Tate vector $x$, maps to its $r$th torsion component. The $G_K$-action and every completed coefficient action commute with this identification.

Good reduction is used here in its exact geometric sense: it supplies the finite-flat ambient groups (3.1). It is not being used to claim that $p$-adic torsion is unramified. At the residue characteristic, even $\mu_p$ is ramified on generic points while remaining finite flat.

### 3.2 Putting each coefficient quotient into geometric torsion

For the saturated lattice $T=M\cap W$, define

$$
U_n=\varpi^{-n}T/T. \tag{3.3}
$$

Because $\varpi^{-n}T\subset W$ and $M\cap W=T$, the natural map

$$
U_n\longrightarrow M_L/M \tag{3.4}
$$

is injective. Multiplication by $\varpi^n$ identifies $U_n$ with the coefficient quotient:

$$
T/\varpi^nT\xrightarrow{\sim}U_n,
\qquad
t\bmod\varpi^nT\longmapsto\varpi^{-n}t\bmod T. \tag{3.5}
$$

Thus $U_n$ is a $G_K$-stable subgroup of $B[p^\infty](\overline K)$, free of rank two over $\mathcal O/\varpi^n$, and

$$
|U_n|=|\mathcal O/\varpi^n|^2=q^{2n}. \tag{3.6}
$$

Choose $r(n)$ such that $p^{r(n)}\in(\varpi^n)$. Then $p^{r(n)}U_n=0$, so $U_n$ determines a closed finite etale subgroup

$$
U_{n,K}\hookrightarrow B[p^{r(n)}]. \tag{3.7}
$$

No endomorphism $[\varpi]$ of the abelian scheme is required to make (3.7). The completed coefficient action is used on the generic Tate module, while an ordinary integer power $p^{r(n)}$ supplies the finite geometric ambient group.

The choice of $r(n)$ is harmless. If $s\geq r(n)$, then $\mathcal B[p^{r(n)}]$ is a closed subgroup of $\mathcal B[p^s]$. The closure of $U_{n,K}$ in $\mathcal B[p^s]$ is killed by $p^{r(n)}$: multiplication by $p^{r(n)}$ and the zero map agree on its generic fiber, hence agree integrally because its coordinate algebra is torsion-free. The closure therefore lies in $\mathcal B[p^{r(n)}]$ and agrees with the closure taken there.

### 3.3 Finite-flat closure, rank, and ambient uniqueness

Let $\mathcal G_n$ be the schematic closure of (3.7) in $\mathcal B[p^{r(n)}]$. The closure theorem over a DVR gives the first major conclusion.

**Proposition 3.1 (levelwise finite-flat closure).** For every $n\geq1$, $\mathcal G_n$ is a finite locally free closed commutative subgroup of $\mathcal B[p^{r(n)}]$. Its generic fiber is $U_{n,K}$, its rank is $q^{2n}$, and it is the unique finite-flat closed subgroup of this fixed ambient torsion group with that generic fiber. Formation of $\mathcal G_n$ commutes with flat extensions of DVRs.

**Proof strategy.** Contract the generic Hopf ideal to the integral coordinate algebra. The contracted quotient injects into its generic fiber and is therefore torsion-free; over a DVR it is free. Only after this flatness step do the Hopf identities descend.

Write $\mathcal B[p^{r(n)}]=\operatorname{Spec}C$ and let $I_K\subset C_K$ be the Hopf ideal of $U_{n,K}$. Put

$$
I=C\cap I_K,
\qquad
\mathcal G_n=\operatorname{Spec}(C/I). \tag{3.8}
$$

The map $C/I\to C_K/I_K$ is injective, so $C/I$ is a finite torsion-free $R$-module and hence finite free. The quotient sequence splits as an $R$-module sequence. Consequently the kernel of

$$
C\otimes_RC\longrightarrow(C/I)\otimes_R(C/I)
$$

is $I\otimes C+C\otimes I$. The coproduct of an element of $I$ maps to zero after inverting the uniformizer; torsion-freeness of the target makes it zero already over $R$. The counit and antipode are treated in the same way. Thus $I$ is a Hopf ideal and $\mathcal G_n$ is a finite-flat subgroup.

Its rank equals the dimension of its generic coordinate algebra, which is the order (3.6). If another finite-flat closed subgroup in the same ambient group has generic ideal $I_K$, its integral ideal is saturated and therefore equals $C\cap I_K=I$. This proves ambient uniqueness. Flat base change preserves the saturated exact sequence and hence the contracted ideal. $\square$

Proposition 3.1 is valid without (1.1). It proves existence and correct rank at every single level. It does not yet prove that the lower-level group chosen by closure is the represented quotient of a higher level.

## 4. Why the levels form one exact tower

### 4.1 The gap between levelwise closure and exactness

The generic modules satisfy, for every $m,n\geq1$, an exact sequence

$$
0\longrightarrow U_m
\longrightarrow U_{m+n}
\xrightarrow{\,\varpi^m\,}U_n
\longrightarrow0. \tag{4.1}
$$

Here the first arrow is the inclusion

$$
\varpi^{-m}T/T\subset\varpi^{-(m+n)}T/T,
$$

and the last arrow multiplies a torsion class by $\varpi^m$. Its kernel is exactly $\varpi^{-m}T/T$.

Close $U_m$ inside $\mathcal G_{m+n}$ and call the result $\mathcal H_{m,n}$. Schematic closure makes $\mathcal H_{m,n}$ finite flat, and the represented quotient gives an exact sequence

$$
0\longrightarrow\mathcal H_{m,n}
\longrightarrow\mathcal G_{m+n}
\longrightarrow\mathcal Q_{m,n}
\longrightarrow0. \tag{4.2}
$$

The generic fiber of $\mathcal Q_{m,n}$ is $U_n$. The desired conclusion is $\mathcal Q_{m,n}\simeq\mathcal G_n$. This does not follow from rank and generic fiber alone. Outside a rigidity range, two nonisomorphic finite-flat groups can have isomorphic generic fibers, and a generically invertible map can fail to be an integral isomorphism. The raw kernel of an integral morphism can also acquire a nonflat vertical layer.

Thus the safe proof has two stages: closure and represented quotient produce the exact sequence (4.2); a separate uniqueness theorem identifies its marked quotient with the independently closed lower level.

### 4.2 The Raynaud rigidity range

Assume now that $R$ is henselian, $k$ is perfect, and $e<p-1$. Raynaud full faithfulness says that for finite flat commutative $p$-power-order groups $\mathcal H$ and $\mathcal H'$ the map

$$
\operatorname{Hom}_R(\mathcal H,\mathcal H')
\xrightarrow{\sim}
\operatorname{Hom}_K(\mathcal H_K,\mathcal H'_K) \tag{4.3}
$$

is bijective. In particular, two marked models of the same finite generic group are uniquely isomorphic: extend the generic marking and its inverse, then use faithfulness to prove that the two composites are identities.

The same argument extends a finite coefficient action. If a finite ring $\Lambda$ acts on the generic fiber, every scalar extends by (4.3), and all ring identities hold integrally because they hold generically. This observation will put the full $\mathcal O/\varpi^n$-action on the particular closures $\mathcal G_n$, not merely on some replacement models.

The inequality is sharp for the theory being used. At $e\geq p-1$, distinct Oort--Tate models can have the same marked generic group. At $p=2$, the inequality would be $e<1$, impossible for a mixed-characteristic DVR. These facts explain why levelwise closure outside (1.1) cannot be silently upgraded to the theorem below.

### 4.3 Exact multiplication sequences

**Proposition 4.1 (all-level exactness).** Under the hypotheses of Section 4.2, there are unique isomorphisms of marked models

$$
\mathcal H_{m,n}\simeq\mathcal G_m,
\qquad
\mathcal Q_{m,n}\simeq\mathcal G_n, \tag{4.4}
$$

and hence a finite-flat exact sequence

$$
0\longrightarrow\mathcal G_m
\longrightarrow\mathcal G_{m+n}
\xrightarrow{\,\varpi^m\,}\mathcal G_n
\longrightarrow0 \tag{4.5}
$$

whose generic fiber is (4.1).

**Proof.** Both $\mathcal H_{m,n}$ and $\mathcal G_m$ are finite-flat models of the marked generic group $U_m$. Raynaud full faithfulness extends the generic identity in both directions, and faithfulness makes the extensions inverse. This gives the first isomorphism in (4.4).

The quotient $\mathcal Q_{m,n}$ is finite flat by the represented quotient theorem, and its generic fiber is the quotient $U_{m+n}/U_m$. Multiplication by $\varpi^m$ identifies that generic quotient with $U_n$. Thus $\mathcal Q_{m,n}$ and $\mathcal G_n$ are marked models of the same generic group. The same full-faithfulness argument gives the second isomorphism.

Every coefficient scalar on $\mathcal G_{m+n}$ preserves $\mathcal H_{m,n}$: it preserves the generic subgroup $U_m$, so its restriction carries the unique closure of $U_m$ into itself. The action therefore descends to $\mathcal Q_{m,n}$. The two isomorphisms in (4.4) intertwine coefficient scalars because their generic fibers do, and generic-fiber faithfulness makes the intertwining squares commute integrally. Transporting (4.2) through (4.4) now gives the coefficient-linear sequence (4.5). Because (4.2) is a represented quotient sequence, the last arrow in (4.5) is faithfully flat and its scheme-theoretic kernel is $\mathcal G_m$. This is fppf exactness, not merely exactness on generic points. $\square$

For $m=1$, (4.5) is the principal transition sequence

$$
0\longrightarrow\mathcal G_1
\longrightarrow\mathcal G_{n+1}
\xrightarrow{\,\varpi\,}\mathcal G_n
\longrightarrow0. \tag{4.6}
$$

For arbitrary $m$, it proves exactly the multiplication devissage later arithmetic arguments use.

### 4.4 Transitivity and recovery of the lattice

Let

$$
r_{m+n,n}:\mathcal G_{m+n}\longrightarrow\mathcal G_n \tag{4.7}
$$

be the last map of (4.5). If $a,b,c\geq1$, the two composites

$$
\mathcal G_{a+b+c}\longrightarrow\mathcal G_c
$$

obtained by reducing in one step or in two steps have the same generic fiber, multiplication by $\varpi^{a+b}$. Generic-fiber faithfulness therefore makes them equal. The transition maps are transitive.

The coefficient action is equally compatible. The generic $\mathcal O/\varpi^n$-action on $U_n$ extends uniquely to

$$
\mathcal O/\varpi^n
\longrightarrow\operatorname{End}_R(\mathcal G_n). \tag{4.8}
$$

The transition $r_{n+1,n}$ intertwines the quotient map $\mathcal O/\varpi^{n+1}\to\mathcal O/\varpi^n$ because it does so generically. The action of $\varpi^n$ on $\mathcal G_n$ is zero: it is zero on the generic fiber, and faithfulness extends that identity.

Taking geometric generic points and using (3.5) gives

$$
\varprojlim_n\mathcal G_n(\overline K)
\simeq\varprojlim_nT/\varpi^nT
\simeq T. \tag{4.9}
$$

The last isomorphism uses completeness and finite freeness of $T$. Formula (4.9) recovers the chosen lattice from the marked tower. It does not say that the inverse limit of the schemes is an abelian scheme or that the rational representation selects $T$ without the marking.

## 5. The finite-flat closure-tower theorem

### 5.1 Complete statement

**Theorem 5.1 (Galois lattice and finite-flat closure tower).** Let $R$ be a henselian mixed-characteristic $(0,p)$ DVR with perfect residue field, fraction field $K$, and $e=v_R(p)<p-1$. Let $\mathcal A/R$ be an abelian scheme with an integral coefficient-order action on the relevant $p$-power torsion. Choose either the covariant Tate-module normalization $B=A$, the Cartier-twisted dual normalization $B=A^\vee$, or a finite power of either as in Section 1.2, and suppose

$$
M=T_pB
$$

is finite free over a coefficient DVR $\mathcal O$ with fraction field $L$ and uniformizer $\varpi$. Let $W\subset M_L$ be a $G_K$-stable two-dimensional $L$-subspace. Then the following assertions hold.

1. After scaling any initial lattice into $M$, the saturated intersection

   $$
   T=M\cap W
   $$

   is a $G_K$-stable free rank-two $\mathcal O$-lattice in $W$.
2. For every $n\geq1$, $T/\varpi^nT$ embeds, through (3.5), as a $G_K$-stable generic subgroup $U_n$ of some $B[p^{r(n)}]$. Its schematic closure $\mathcal G_n$ in $\mathcal B[p^{r(n)}]$ is independent of the sufficiently large integer $r(n)$.
3. The group $\mathcal G_n$ is finite locally free of rank

   $$
   |\mathcal G_n|=|\mathcal O/\varpi^n|^2=q^{2n},
   $$

   has generic fiber $T/\varpi^nT$, and carries a unique compatible $\mathcal O/\varpi^n$-action extending the generic coefficient action.
4. For all $m,n\geq1$, the generic multiplication sequence extends to a coefficient-linear fppf-exact sequence

   $$
   0\longrightarrow\mathcal G_m
   \longrightarrow\mathcal G_{m+n}
   \xrightarrow{\,\varpi^m\,}\mathcal G_n
   \longrightarrow0. \tag{5.1}
   $$

   These maps are transitive. Consequently the $\mathcal G_n$ form one compatible all-level tower and their generic inverse limit is $T$.
5. For a flat extension of DVRs $R\to R'$, base change of this tower is the closure tower of the restricted generic modules in $\mathcal B_{R'}$. Exactness, ranks, coefficient actions, and transition maps are preserved. This remains true even if the ramification index of $R'$ no longer satisfies (1.1), because the already constructed exact sequence is merely being base-changed.
6. Cartier duality gives an exact compatible dual tower whose generic modules are the Tate-twisted contragredients. Determinants reduce from $T$ to every level. A polarization supplies a perfect self-duality on this tower only under the coefficient-adjoint compatibility of Section 6.3 and its two separate unit conditions: the $p$-primary degree defect must vanish on the ambient Tate module, and the restricted lattice pairing must be unimodular. Calling this self-duality an alternating polarization also requires the self-adjoint finite-level normalization stated there.

If (1.1) is omitted, assertions 1--3 remain true except that the coefficient action on the particular closure must come from the ambient order action or another integral extension argument. Levelwise finite flatness and ambient uniqueness remain valid, but assertion 4 is not asserted from closure alone.

### 5.2 Proof of the theorem

Proposition 2.1 proves assertion 1, including freeness, rank, saturation, and Galois stability. Section 3.2 embeds every quotient into finite geometric torsion, and the independence argument following (3.7) removes the auxiliary exponent $r(n)$. Proposition 3.1 proves finite local freeness, generic-fiber recovery, rank, flat base change, and uniqueness inside the chosen ambient torsion object.

Under $e<p-1$, Raynaud full faithfulness extends the generic coefficient endomorphisms and their ring identities, giving (4.8). Proposition 4.1 proves (5.1) by first closing the generic kernel in the already constructed middle group, then taking the represented quotient, and only then identifying the marked quotient with $\mathcal G_n$. Section 4.4 proves transitivity and (4.9). These arguments prove assertions 2--4 without treating a raw scheme-theoretic image or kernel as automatically flat.

Flat base change for saturated closure identifies $\mathcal G_n\times_RR'$ with the closure constructed after restriction to $K'$. A represented finite-flat quotient and its torsor identity commute with arbitrary base change, so (5.1) remains exact. This proves assertion 5. Cartier duality, determinants, and polarizations are proved in Chapter 6, completing assertion 6. $\square$

The proof is all-level: (5.1) holds for every pair $(m,n)$, not merely for adjacent levels, and its construction is compatible under every further reduction.

The full Tate module of an elliptic scheme is the basic calculation. Take $\mathcal O=\mathbf Z_p$, $B=E$, and $W=V_pE$. Then $T=T_pE$, the subgroup $U_n=p^{-n}T/T$ is $E[p^n](\overline K)$, and its closure is the already existing group $\mathcal E[p^n]$. Sequence (5.1) becomes

$$
0\longrightarrow\mathcal E[p^m]
\longrightarrow\mathcal E[p^{m+n}]
\xrightarrow{\,p^m\,}\mathcal E[p^n]
\longrightarrow0. \tag{5.2}
$$

Here exactness comes directly from the abelian scheme and even survives at $p=2$. The low-ramification theorem is needed for the general saturated subplane, where the lower closure must be identified with a quotient of the higher one. A special carrier can therefore prove more than the general closure argument, but it cannot justify that stronger conclusion for every rational subspace.

### 5.3 Localizations of number fields

Let $R=\mathcal O_{F,v}$ be the localization of a number field at a finite place $v\mid p$. It is a DVR with finite, hence perfect, residue field, but it need not be henselian. The closures $\mathcal G_n$ are nevertheless defined over $R$ by the contracted Hopf ideals of Proposition 3.1.

Pass to the henselization $R^h$. It is faithfully flat over $R$, has the same residue field and the same absolute ramification index, and closure commutes with this base change. If $e<p-1$, Chapter 4 constructs the transition maps after henselization. Their two pullbacks to $R^h\otimes_RR^h$ agree on the generic fiber and therefore agree integrally by faithfulness. Faithfully flat descent gives the maps over $R$. Alternatively, close the graph of the generic transition over $R$; after base change to $R^h$ its first projection is an isomorphism, so faithful flatness makes it an isomorphism already over $R$.

Exactness of (5.1) can also be checked after the faithfully flat extension $R\to R^h$. Thus Theorem 5.1 applies verbatim to number-field localizations satisfying $e<p-1$. Completion gives the same conclusion and does not change the constructed groups after base change.

## 6. Cartier duality, determinants, and polarizations

### 6.1 The dual tower and its coefficient action

Cartier duality is contravariant, exact on finite-flat exact sequences, and compatible with arbitrary base change. Therefore (5.1) dualizes to

$$
0\longrightarrow\mathcal G_n^D
\longrightarrow\mathcal G_{m+n}^D
\longrightarrow\mathcal G_m^D
\longrightarrow0. \tag{6.1}
$$

If $N$ is a finite generic module killed by a power of $p$, the geometric points of its Cartier dual are

$$
N^*(1)=\operatorname{Hom}\bigl(N,\mu_{p^\infty}(\overline K)\bigr), \tag{6.2}
$$

with Galois action

$$
(\sigma f)(x)=\sigma f(\sigma^{-1}x). \tag{6.3}
$$

Thus $\mathcal G_n^D$ models $(T/\varpi^nT)^*(1)$. The twist in (6.2) is forced by the action on roots of unity. Replacing (6.2) by an untwisted ordinary dual gives the wrong Galois action.

The coefficient action on the dual is contragredient:

$$
(a\cdot f)(x)=f(ax). \tag{6.4}
$$

If an involution $a\mapsto a^\dagger$ is built into a polarization datum, one may rewrite (6.4) as an $\mathcal O$-linear action using $a^\dagger$ on the second variable. Without such an involution, one should retain the precomposition formula rather than silently identify the two coefficient actions.

Cartier duality also describes closure. If $U_n$ is closed inside ambient torsion, its annihilator in the Cartier dual ambient group is the closure of the generic annihilator. The dual of $\mathcal G_n$ is the corresponding quotient of the ambient dual torsion. A subgroup therefore becomes a quotient under duality; it need not be another subgroup selected by the same rational projector.

### 6.2 Determinants are generic data carried by the lattice

The determinant of the rank-two representation is

$$
\delta=\det_LW:G_K\longrightarrow L^\times. \tag{6.5}
$$

Since $T$ is stable, every matrix of $G_K$ on $T$ lies in $\operatorname{GL}_2(\mathcal O)$. Hence $\delta$ takes values in $\mathcal O^\times$, acts on the rank-one lattice $\bigwedge^2_{\mathcal O}T$, and reduces at every level:

$$
\det_{\mathcal O/\varpi^n}(T/\varpi^nT)
=\delta\bmod\varpi^n. \tag{6.6}
$$

Scaling $T$ or replacing it by another stable lattice does not change the rational character $\delta$. No self-duality is needed for (6.6). This is why the determinant identity supplied rationally by curve extraction survives even when an integral pairing becomes degenerate modulo $\varpi$.

One must not infer from (6.6) that an exterior-power group scheme has automatically been constructed. Finite-flat commutative groups do not possess an unrestricted tensor calculus that realizes every generic exterior power. The determinant in (6.6) is a statement about the marked generic coefficient module. When a geometric Weil pairing supplies an integral morphism, it can realize the corresponding determinant character; absent that pairing, finite flatness of a determinant group requires its own construction.

If a rank-one $\mathcal O$-lattice $\mathcal L(\psi)$ and a perfect alternating $\mathcal O$-bilinear pairing

$$
b:T\times T\longrightarrow\mathcal L(\psi) \tag{6.7}
$$

are supplied, then $t_1\wedge t_2\mapsto b(t_1,t_2)$ identifies $\det T$ with $\mathcal L(\psi)$ and forces $\delta=\psi$. In rank two this implication has no square-root ambiguity. The word *perfect* in (6.7) is an integral unit condition, not merely rational nondegeneracy.

### 6.3 Polarizations and the two separate unit tests

Let $\lambda:\mathcal B\to\mathcal B^\vee$ be a polarization. It gives Weil pairings on every ambient torsion group,

$$
e_{p^r}^{\lambda}:\mathcal B[p^r]\times\mathcal B[p^r]
\longrightarrow\mu_{p^r}. \tag{6.8}
$$

They are alternating, commute with base change, and obey the adjoint relation

$$
e_{p^r}^{\lambda}(ax,y)
=e_{p^r}^{\lambda}(x,a^\dagger y) \tag{6.9}
$$

whenever the coefficient order is stable under the Rosati involution. Restricting (6.8) to the closed subgroup $\mathcal G_n$ gives an integral alternating pairing and hence a map $\mathcal G_n\to\mathcal G_n^D$. This statement is only levelwise and uses the declared embedding in $\mathcal B[p^{r(n)}]$; the map can be degenerate. A compatible perfect tower requires a separate coefficient-normalized construction from one Rosati-balanced Tate pairing. Without such a construction, this book retains the Cartier dual tower but does not identify it with a polarized self-dual tower.

There is a normalization trap in that last passage. The restriction of $e_{p^{r(n)}}^\lambda$ is always an integral pairing, but for a ramified coefficient ring it need not be the perfect pairing appropriate to the $\varpi^n$-quotient. Indeed $p^{r(n)}$ and $\varpi^n$ can have different valuation, and the resulting extra scalar can be a nonunit. Thus perfectness of the coefficient tower will not be inferred from the raw ambient restriction.

There are two independent tests for perfectness.

First, the ambient polarization must be prime to $p$. More exactly, $\lambda$ induces an isomorphism on the full $p$-adic Tate lattice if and only if its $p$-primary isogeny defect vanishes; a sufficient and standard condition is

$$
p\nmid\deg\lambda. \tag{6.10}
$$

Under (6.10), $\lambda[p^r]$ is an isomorphism for every $r$, so the ambient pairing (6.8) is perfect. A principal polarization satisfies (6.10) for every $p$. If $p\mid\deg\lambda$, the ambient adjoint can have nontrivial $p$-primary kernel or cokernel, and no perfectness conclusion is available without a separate calculation.

Second, even a perfect ambient pairing need not restrict perfectly to a saturated sublattice. Let

$$
b_T^\sharp:T\longrightarrow
\operatorname{Hom}_{\mathbf Z_p}(T,\mathbf Z_p)(1) \tag{6.11}
$$

be the adjoint of the restricted Tate pairing, with the appropriate Rosati coefficient action. The restricted tower is perfectly self-dual exactly when the relevant coefficient-balanced form is unimodular, equivalently when $b_T^\sharp$ identifies $T$ with its declared dual lattice. In an $\mathcal O$-valued rank-two presentation this says that the Gram determinant is a unit of $\mathcal O$.

Here is the exact finite-level normalization. Use the rational extension of the Tate pairing to identify the rational plane with its twisted dual, and for a lattice $L_0$ in that plane write

$$
L_0^\#=\{x:b(L_0,x)\subset\mathbf Z_p(1)\}.
$$

If $b_T^\sharp$ is an isomorphism, then $T^\#=T$. The Rosati adjoint relation gives

$$
(\varpi^nT)^\#=(\varpi^\dagger)^{-n}T, \tag{6.12}
$$

and hence a canonical perfect generic pairing

$$
T/\varpi^nT\ \times\
(\varpi^\dagger)^{-n}T/T
\longrightarrow \mathbf Q_p/\mathbf Z_p(1),
\qquad
(t,y)\longmapsto b(t,y)\bmod\mathbf Z_p(1). \tag{6.13}
$$

An involution of the local coefficient DVR preserves its maximal ideal, so $(\varpi^\dagger)=(\varpi)$. Consequently the second module in (6.13) is the same fractional-ideal realization $\varpi^{-n}T/T=U_n$ used in Chapter 3, with the contragredient coefficient action. Formula (6.13), rather than an unscaled restriction of $e_{p^{r(n)}}^\lambda$, is the coefficient-normalized perfect duality. Its adjoint is a generic isomorphism $U_n\to U_n^*(1)$. Raynaud full faithfulness extends that adjoint uniquely to $\mathcal G_n\to\mathcal G_n^D$, and the extension is an isomorphism because its inverse extends as well. The generic identities relating (6.13) at different levels then make the integral dualities compatible with (5.1) and (6.1) by generic-fiber faithfulness.

Perfect self-duality and alternation are not identical normalization statements. If $\varpi^\dagger=\varpi$, then (6.13), after (3.5), is alternating in the present odd-prime range: skew-symmetry and self-adjointness first give twice the diagonal value equal to zero, and multiplication by $2$ is invertible on the group. More generally one must choose a compatible self-adjoint trivialization of the Rosati-stable fractional ideals, or directly verify that the resulting generic pairing is alternating; multiplying a perfect adjoint by an arbitrary coefficient unit can destroy that identity. Raynaud faithfulness preserves alternation once it holds generically. Thus a Rosati-stable ideal alone gives the perfect contragredient self-duality, not an unqualified alternating polarization under every choice of uniformizer.

When $\varpi=p$ and $r(n)=n$, this normalized pairing is the usual restriction of $e_{p^n}^\lambda$. For ramified coefficient extensions it generally is not; the inverse-different issue in Section 7.3 is the same discrepancy viewed under coefficient duality. Thus the phrase “Gram determinant is a unit” is valid only after the coefficient-valued target and its trace-dual normalization have been fixed.

A useful sufficient condition is an orthogonal integral decomposition

$$
M=T\oplus T^\perp \tag{6.14}
$$

with (6.10). The ambient adjoint is then block diagonal and invertible, so its restriction to $T$ is invertible. Without (6.14), a primitive sublattice of a unimodular lattice can have nonunit discriminant. Thus prime-to-$p$ degree of the polarization does not by itself prove a perfect residual pairing on a packet lattice.

For a concrete test, let $M$ have symplectic basis $e_1,f_1,e_2,f_2$ over $\mathbf Z_p$ and let $T$ be spanned by $e_1$ and $pf_1+e_2$. The minor on the coordinates $e_1,e_2$ is a unit, so $T$ is primitive in $M$, but its restricted pairing has matrix

$$
\begin{pmatrix}0&p\\-p&0\end{pmatrix}. \tag{6.15}
$$

Its discriminant is not a unit. This example separates saturation from self-duality even inside a principally polarized ambient lattice.

Under both unit tests and the Rosati-stable coefficient normalization, the generic adjoint (6.13) is an isomorphism at every level. Raynaud's isomorphism lemma then makes its integral extension $\mathcal G_n\to\mathcal G_n^D$ an isomorphism, so the duality is schematically perfect even on connected special fibers. It is a perfect alternating polarization when the additional self-adjoint normalization in the preceding paragraph holds. If a curve construction supplies only a rational perfect pairing, its return-map, projector, level, and lattice discriminants must all be units before either conclusion can be used.

## 7. Ground-field and coefficient change

### 7.1 Flat change of the valuation ring

Let $R\to R'$ be a local injection of DVRs, with fraction fields $K\to K'$. Such an extension is flat. The saturated Hopf ideal defining $\mathcal G_n$ remains saturated after tensoring, so

$$
\mathcal G_n\times_RR'
$$

is the closure of the restricted $G_{K'}$-module $U_n$ in the base-changed ambient torsion. Ranks and coefficient actions are unchanged, while Galois action is restricted from $G_K$ to $G_{K'}$.

The exact sequence (5.1) base-changes to an exact sequence because represented quotient torsors commute with arbitrary base change. Therefore a ramified extension $R'/R$ cannot destroy a tower already constructed over $R$. It can, however, cross the Raynaud boundary and permit new upstairs models not descended from $R$. The theorem does not identify every model over $R'$ with the base change of the closure model.

Descent is a different direction. An upstairs group descends only with compatible integral descent data satisfying the cocycle condition. Descent of the generic representation alone does not descend the Hopf lattice. Below the Raynaud boundary, a generic descent datum on an already existing model extends uniquely and can then be descended faithfully flatly; existence of the upstairs model is still an input.

### 7.2 Extension of the coefficient DVR

Let $\mathcal O\to\mathcal O'$ be a finite extension of coefficient DVRs, with fraction fields $L\to L'$, uniformizer $\varpi'$, and residue field $\kappa'$. Put

$$
T'=T\otimes_{\mathcal O}\mathcal O',
\qquad
W'=W\otimes_LL'. \tag{7.1}
$$

Then $T'$ is free of rank two over $\mathcal O'$ and is $G_K$-stable. If the ambient Tate module is also scalar-extended, Proposition 2.1 gives the saturated-intersection identity (2.4). This is a coefficient operation, not a change of the local ground field.

The finite module $T'/\varpi'^nT'$ need not embed in the torsion of the same abelian variety: as a $\mathbf Z_p$-module its rank has grown. Its finite-flat model is instead constructed from products, closures, and represented quotients. Choose $a$ such that $\varpi^a$ acts as zero on $\mathcal O'/\varpi'^n$. Then

$$
T'/\varpi'^nT'
\simeq
(\mathcal O'/\varpi'^n)
\otimes_{\mathcal O/\varpi^a}(T/\varpi^aT). \tag{7.2}
$$

Here is the coefficient construction in full. Put $\Lambda=\mathcal O/\varpi^a$ and $\Lambda'=\mathcal O'/\varpi'^n$, choose a surjection $q:P=\Lambda^d\twoheadrightarrow\Lambda'$, and tensor it with $T/\varpi^aT$. If $N$ is the kernel of

$$
P\otimes_\Lambda(T/\varpi^aT)
\longrightarrow
\Lambda'\otimes_\Lambda(T/\varpi^aT), \tag{7.2a}
$$

close $N$ in the finite-flat model $\mathcal G_a^d$ and take the represented quotient $\mathcal Q$. Its generic module is (7.2). For $b\in\Lambda'$, projectivity of $P$ lifts the map $bq:P\to\Lambda'$ to a $\Lambda$-linear endomorphism $\widetilde b:P\to P$. It preserves $\ker q$, hence its matrix of $\Lambda$-scalars preserves $N$ and its schematic closure. It therefore descends to $\mathcal Q$. Two lifts differ by a map into $\ker q$ and induce the same generic endomorphism of the quotient, so generic-fiber faithfulness makes the integral endomorphisms equal. The unit, sum, and product identities also hold generically and hence integrally. Thus $\mathcal Q$ carries a genuine $\Lambda'$-action; call it $\mathcal G'_n$. Its rank is

$$
|\mathcal G'_n|=|\mathcal O'/\varpi'^n|^2. \tag{7.3}
$$

In the Raynaud range, $\mathcal G'_n$ is unique as a marked model. The generic reductions $T'/\varpi'^{m+n}\to T'/\varpi'^n$ extend uniquely, and the proof of Proposition 4.1 gives exact sequences

$$
0\longrightarrow\mathcal G'_m
\longrightarrow\mathcal G'_{m+n}
\longrightarrow\mathcal G'_n
\longrightarrow0. \tag{7.4}
$$

Thus finite coefficient extension preserves the all-level conclusion. The construction does not assert a basis-independent embedding of $T'$ into the original $T_pB$, and it does not assert independence of arbitrary geometric carriers.

Residual absolute irreducibility behaves well: if $T/\varpi T$ is absolutely irreducible, its scalar extension to $\kappa'$ is absolutely irreducible. Mere irreducibility over $\kappa$ is insufficient. Conversely, a residual representation that becomes reducible over $\kappa'$ was not absolutely irreducible to begin with.

### 7.3 The different and duality after coefficient extension

Coefficient extension and Cartier duality do not commute through a naive identification of coefficient lattices when $\mathcal O'/\mathcal O$ is ramified. The trace dual is

$$
(\mathcal O')^\vee
=\operatorname{Hom}_{\mathcal O}(\mathcal O',\mathcal O)
\simeq\mathfrak D_{\mathcal O'/\mathcal O}^{-1}, \tag{7.5}
$$

where $\mathfrak D$ is the different. Consequently the $\mathcal O$-linear dual of $T\otimes\mathcal O'$ naturally contains the inverse different. Choosing a generator identifies it with $\mathcal O'$, but that choice is noncanonical and changes by a unit.

If $\mathcal O'/\mathcal O$ is unramified, the different is the unit ideal and the trace pairing is perfect. Then the usual tensor description of a perfect coefficient pairing is valid without a valuation defect. If the extension is ramified, a rational self-duality can acquire an integral different factor. Finite-flatness of the scalar-extended modules still follows from Section 7.2, but a claimed self-dual lattice or unit discriminant must include the inverse different explicitly.

This is another instance of the main distinction: coefficient extension preserves existence, while perfect integral duality needs a separate unit calculation.

## 8. How a curve packet supplies the rational plane

### 8.1 A nonzero oldvector gives an embedding

Books 125--126 prove the rational curve-extraction statement in the form needed here. After choosing a coefficient field which splits the relevant simple finite Hecke algebra, a packet block of first cohomology has a factorization

$$
H^1_{\mathrm{et}}(C_{\overline F},L)[\Pi]
\simeq P_\Pi\otimes_LW_\Pi, \tag{8.1}
$$

where $P_\Pi$ is the finite automorphic level or oldvector factor and $W_\Pi$ is the two-dimensional Galois multiplicity space. Galois acts on $W_\Pi$ and trivially on the displayed finite factor because its action commutes with the split Hecke algebra.

The $W_\Pi$ in (8.1) is the actual, possibly nonsemisimple multiplicity representation occurring in cohomology. If one later replaces it by a globally defined semisimplification, the geometric embedding below transfers only after a proved Galois isomorphism or a theorem that the raw representation is already semisimple. Equality of almost all Frobenius polynomials does not embed an abstract semisimplification into this fixed cohomology group and does not transport its lattice.

Choose any nonzero vector $s\in P_\Pi$. Then

$$
i_s:W_\Pi\longrightarrow P_\Pi\otimes_LW_\Pi,
\qquad
w\longmapsto s\otimes w \tag{8.2}
$$

is injective and $G_F$-equivariant. This is the promised rational embedding of the rank-two multiplicity space once the packet occurs in $H^1$.

The choice of $s$ is not canonical. If $\dim P_\Pi>1$, two nonproportional oldvectors give different embedded planes. The intrinsic rational construction of Books 125--126 is the Hom multiplicity space $W_\Pi$, determined up to coefficient extension and isomorphism; (8.2) is merely a convenient way to put a copy of it into one geometric carrier. No integral Morita equivalence is needed for existence.

### 8.2 Passing from cohomology to the finite-flat normalization

Let $J_C$ be the product of the Jacobians of the connected components of the proper smooth curve. With covariant Tate modules, the Kummer comparison is

$$
T_pJ_C\simeq H^1_{\mathrm{et}}(C_{\overline F},\mathbf Z_p)(1). \tag{8.3}
$$

Therefore (8.2) gives a rational embedding

$$
W_\Pi(1)\hookrightarrow
V_pJ_C\otimes_{\mathbf Q_p}L. \tag{8.4}
$$

The coefficient extension in (8.4) is real: unless $L=\mathbf Q_p$, its target is not literally $V_pJ_C$. Choose a $\mathbf Z_p$-basis of $\mathcal O$ and identify $T_pJ_C\otimes\mathcal O$, as a $\mathbf Z_p$-lattice with its regular $\mathcal O$-action, with the Tate module of the finite power $J_C^{[L:\mathbf Q_p]}$. Then (8.4) becomes an embedding into an actual good-reduction abelian Tate module of the form (1.4). The basis and finite-power presentation are not canonical. Equivalently, one may use the Poincare identification with a Cartier-twisted dual Tate module.

The representation $W_\Pi$ in untwisted cohomology and the finite-flat representation $W_\Pi(1)$ are different normalizations. Their determinants differ by the square of the cyclotomic character. One must transport the determinant formula accordingly. Writing $W_\Pi$ itself as a subgroup of $T_pJ_C$ would erase the twist in (8.3) and is not permitted.

Good reduction is also a real hypothesis. A rational curve constituent at a place where the chosen Jacobian has only semistable reduction is not covered by the abelian-scheme closure theorem. Crystallinity or the expected Hodge--Tate weights alone do not create the missing finite-flat ambient torsion groups.

### 8.3 What saturation proves and what it does not

Apply Proposition 2.1 to the image of (8.4):

$$
T_s=M\cap i_s(W_\Pi(1)). \tag{8.5}
$$

This is a stable saturated rank-two lattice. Theorem 5.1 then gives its all-level finite-flat tower in the Raynaud range. This proves the existence needed downstream.

The construction of the lattice does not require a formula for $\det W_\Pi$. When a determinant formula is used, it is exactly the polarized packet conclusion of Books 125--126: the basic quaternionic group, or a connected central modification with the stated essential-self-duality character on its actual abelian quotient and the required component normalization. Outside that range, (6.5)--(6.6) still apply to the actual determinant character, but this book does not manufacture the automorphic formula from two-dimensionality or adjoint duality.

The construction deliberately avoids the false stronger argument. A rational central idempotent cutting out the packet can have a nonunit denominator. The full packet block can have dimension $2\dim P_\Pi$, and rational Morita evaluation need not be an integral isomorphism for a nonmaximal order. None of those facts prevents choosing $s\ne0$ and intersecting the rational plane (8.2) with the ambient Tate lattice. Conversely, saturation does not repair the projector denominator or prove that an integral Hom module is a canonical direct factor.

There is one further handoff to check. Book 126 distinguishes the raw multiplicity representation from its abstract semisimplification. The warning after (8.1) is correct: semisimplification does not put a new plane inside the same Jacobian Tate module. It nevertheless preserves the *existence* of an all-level finite-flat lattice below the Raynaud boundary, by a subquotient construction rather than by a new geometric embedding.

**Proposition 8.1 (finite-flat tower after semisimplification).** Assume the hypotheses of Theorem 5.1, and let $T\subset V$ be its chosen rank-two lattice with tower $\{\mathcal G_n\}$. Then the semisimplification $V^{\mathrm{ss}}$ contains a stable lattice $T^{\mathrm{ss}}$ whose quotients admit one coefficient-linear compatible exact finite-flat tower. This construction asserts neither an embedding of $V^{\mathrm{ss}}$ into the original abelian Tate module nor a canonical lattice in $V^{\mathrm{ss}}$.

**Proof.** If $V$ is irreducible, then $V^{\mathrm{ss}}=V$ and there is nothing to prove. Otherwise choose a stable $L$-line $V_1\subset V$ and put

$$
T_1=T\cap V_1,
\qquad
T_2=T/T_1. \tag{8.6}
$$

Saturation makes $T_1$ and $T_2$ free rank-one $\mathcal O$-lattices and gives, for every $n$,

$$
0\longrightarrow T_1/\varpi^nT_1
\longrightarrow T/\varpi^nT
\longrightarrow T_2/\varpi^nT_2
\longrightarrow0. \tag{8.7}
$$

Close the first generic term inside $\mathcal G_n$ and denote the closure by $\mathcal H_n$; let $\mathcal Q_n=\mathcal G_n/\mathcal H_n$ be the represented quotient. Schematic closure and the quotient theorem make both groups finite flat with their inherited coefficient actions, and their marked generic modules are the two endpoints of (8.7).

For the generic reduction sequences of the $T_1$-quotients, close the generic kernel in $\mathcal H_{m+n}$ and take the represented quotient. Raynaud full faithfulness identifies that quotient with $\mathcal H_n$ and the kernel with $\mathcal H_m$, exactly as in Proposition 4.1. The same argument applied to the marked models $\mathcal Q_n$ gives an exact compatible tower for $T_2$. Generic-fiber faithfulness makes all transition maps transitive and coefficient linear. Therefore

$$
T^{\mathrm{ss}}=T_1\oplus T_2\subset V_1\oplus V/V_1=V^{\mathrm{ss}} \tag{8.8}
$$

has the product tower $\{\mathcal H_n\times\mathcal Q_n\}$. Products preserve the exact level sequences, so this is the required compatible tower. $\square$

In particular, the semisimple representation used by an immediate arithmetic consumer receives a finite-flat tower without being declared a geometric subspace. If a residual lattice is absolutely irreducible, then $V$ itself is irreducible and this extra construction is unnecessary; the original saturated lattice and its tower already belong to the semisimple representation.

The exact conclusions are therefore:

- the rational multiplicity space $W_\Pi$ exists intrinsically up to coefficient extension and isomorphism;
- a nonzero $s\in P_\Pi$ gives a noncanonical rational geometric embedding;
- saturation relative to that embedding gives a stable rank-two lattice;
- semisimplification preserves existence of some all-level finite-flat lattice by Proposition 8.1, but does not preserve the original geometric embedding or select a lattice;
- residual absolute irreducibility can make the pulled-back homothety class independent of the stable lattice, but not independent of the embedding as an embedded subspace;
- no arbitrary PEL-presentation independence, integral Morita splitting, canonical projector, or preferred scale is asserted.

## 9. The unramified Fontaine--Laffaille realization

### 9.1 The same tower in filtered form

Suppose $R=W(k)$ for a perfect field $k$ of characteristic $p>2$. Then $e=1<p-1$, so Theorem 5.1 applies. Books 53--54 give a second description of the resulting tower: finite-flat $p$-power groups over $W(k)$ correspond to divided filtered modules of weights $[0,1]$, and a compatible system of all finite quotients corresponds to a finite free strongly divisible lattice.

Applied to the tower $\{\mathcal G_n\}$, that equivalence produces one strongly divisible object whose Galois realization is $T$. Exactness (5.1) becomes strict exactness at every filtered level. Cartier duality, coefficient actions, perfect pairings when supplied, and unramified ground-field base change are preserved. Since every nonzero open ideal of the DVR $\mathcal O$ is $(\varpi^n)$, Theorem 5.1 already covers every open coefficient quotient; the filtered description proves that these quotients belong to one compatible admissible system.

The logical direction matters. Geometry and closure first construct the finite-flat groups. Fontaine--Laffaille theory classifies and transports the resulting integral system. A rational crystalline representation with weights $\{0,1\}$ does not by itself select a strongly divisible lattice, and rational Hodge labels do not make every arbitrary stable lattice finite flat without an additional argument.

### 9.2 Changing a stable lattice by commensurability

In the unramified odd-prime range, one all-level finite-flat lattice implies the same *existence property* for every commensurable stable lattice, though the models and residual extensions can change.

**Proposition 9.1 (commensurability transfer).** Let $T$ have an all-level finite-flat tower over $W(k)$, with $p>2$, and let $T'$ be another $G_K$-stable $\mathcal O$-lattice in the same rational representation. Then every $T'/\varpi^nT'$ is finite flat with its coefficient action, and the quotients admit one compatible exact tower.

**Proof.** Choose $c\geq0$ such that

$$
\varpi^cT\subset T'\subset\varpi^{-c}T. \tag{9.1}
$$

For fixed $n$, the finite module

$$
H=\varpi^{-c}T/\varpi^{n+c}T
\simeq T/\varpi^{n+2c}T \tag{9.2}
$$

has a coefficient-linear finite-flat model. The images

$$
B=\varpi^nT'/\varpi^{n+c}T
\subset
C=T'/\varpi^{n+c}T
\subset H \tag{9.3}
$$

are stable, and $C/B\simeq T'/\varpi^nT'$. Close $C$ in the model of $H$, close $B$ inside that closure, and take the represented quotient. This constructs a finite-flat model of $T'/\varpi^nT'$ with its coefficient action.

Raynaud full faithfulness identifies any two marked models at these levels and extends the generic reduction maps. Closing their generic kernels and taking represented quotients proves exactness exactly as in Proposition 4.1. Equivalently, the stable-lattice equivalence of Book 54 reconstructs one strongly divisible lattice from the compatible marked finite levels. $\square$

Proposition 9.1 is an existence and compatibility statement. It does not say $T'=T$, that their reductions are isomorphic when reducible, or that their strongly divisible lattices coincide. Under the absolute residual irreducibility hypothesis of Proposition 2.2, the lattices are homothetic; without it, the integral extension direction can change.

### 9.3 The prime-two and ramified boundaries

At $p=2$, neither the inequality $e<p-1$ nor the Fontaine--Laffaille interval $[0,1]\subset[0,p-2]$ is available. Good reduction still gives ambient groups, and Proposition 3.1 still gives a finite-flat closure at every level. What is missing from the cited theory is the identification of independently closed quotients needed for (5.1). No dyadic all-level theorem is asserted here.

For a ramified base with $e\geq p-1$, the same distinction applies. Schematic closure remains finite flat and unique inside the fixed ambient torsion group, but generic models need not be abstractly unique and generic morphisms need not extend. A Breuil--Kisin or another ramified integral theory could supply a different exact theorem, but it is not among the inputs used in this book and is not invoked.

Finally, twisting a representation changes its Galois action without supplying a geometric model. Cartier duality proves stability under the *Tate-twisted dual* $N\mapsto N^*(1)$ because it is an operation on finite-flat group schemes. It does not prove stability under $N\mapsto N(-1)$ or any other arbitrary negative twist. This boundary is part of the theorem, not a missing convenience.

## 10. Exact handoffs to the later arithmetic books

### 10.1 Compatible systems and potential modularity

Book 168 constructs rational compatible systems and saturated cohomological packet lattices but explicitly stops before coefficient-prime finite flatness. The present theorem fills that gap only when a member has the geometric bridge (1.4), good reduction, and the low-ramification hypothesis. It supplies a chosen placewise lattice and tower; it does not synchronize lattices across distinct coefficient primes or make the rational compatible system integrally canonical.

Book 177 may use the following output at an unramified coefficient-prime place of odd residue characteristic:

$$
\left(T/\varpi^nT,\ \mathcal G_n,\
0\to\mathcal G_m\to\mathcal G_{m+n}\to\mathcal G_n\to0\right)_{m,n\geq1}, \tag{10.1}
$$

together with the coefficient action, declared polarization pairing when the degree and discriminant tests and the coefficient-adjoint normalization pass, and coefficient extension from Section 7.2. If potential modularity identifies two rational representations and their common residual member is absolutely irreducible, Proposition 2.2 makes transported stable lattices homothetic. If the residual member is reducible, equality of rational representations or good Frobenius polynomials identifies at most residual semisimplifications and does not identify extension classes.

Book 179 may record (10.1) for the distinguished geometric member of a compatible family. It may transport the rational determinant and restrict the tower after ground-field base change. It may not infer the same tower for a new coefficient prime from weak or strong compatibility alone. At each moving coefficient prime there must be a new geometric or integral comparison input.

### 10.2 Changing the coefficient prime and the fixed-three argument

Book 186 deliberately returns only a rational member at the place above three and asks a later integral theorem to choose a named stable lattice. The present theorem can provide that lattice when Book 186's rational member is embedded, after the correct twist or Cartier dual, in the Tate module of a good-reduction abelian scheme over $\mathbf Z_3$ or an unramified extension. Since

$$
e(\mathbf Z_3)=1<2, \tag{10.2}
$$

the full tower theorem applies. Any special line at the dyadic place must then be intersected with this same named lattice; changing the lattice can change its residual thickness.

Book 187 has two valid routes at three. A geometric bridge as above gives $T$ and every $\mathcal G_n$ directly. A strongly divisible Fontaine--Laffaille lattice gives one local all-level lattice, after which Proposition 9.1 transfers finite-flat existence to any chosen commensurable global stable lattice and Raynaud rigidity supplies one compatible tower. Neither route says that rational crystallinity canonically selected the global lattice.

For a finite coefficient extension used in Book 187, Section 7.2 supplies the extended tower and Section 7.3 records the possible different in duality. For residual image language, absolute irreducibility must be checked after residue-field extension. These are exactly the hypotheses needed to pass from existence of a rational three-adic member to a named coefficient-linear all-level finite-flat system.

## 11. Hostile audit and conclusion

### 11.1 Dependency and hypothesis audit

The proof uses earlier books only in their established ranges.

| Source | Imported result | Use here | Strengthening not made |
|---|---|---|---|
| Book 35 | torsion of an abelian scheme, isogenies, quotients, polarizations, and base change | ambient groups and degree conditions | good reduction does not make $p$-torsion unramified |
| Books 26--28 | finite locally free algebra, Hopf ideals, closure over a DVR, and represented quotients | levelwise closure and exact quotient sequences | raw kernels and images are not declared flat |
| Book 34 | Cartier exactness, annihilators, Weil pairing, and Tate-twisted duality | dual tower and polarization maps | ordinary duals and negative twists are not substituted |
| Book 42 | marked finite-flat representations, subquotients, and coefficient extension | coefficient actions and finite coefficient change | existence is not uniqueness of a chosen model |
| Book 45 | covariant Tate modules, torsion limits, and the cyclotomic pairing | normalization and determinant checks | elliptic rank-two conclusions are not imposed on arbitrary abelian factors |
| Book 52 | Raynaud full faithfulness for $e<p-1$ | identification of quotient levels and transition maps | no rigidity is claimed at or above the boundary |
| Books 53--54 | unramified weights $[0,1]$, stable-lattice equivalence, duality, and compatible quotients | filtered description and the fixed-three route | rational crystallinity does not select a lattice |
| Books 125--126 | rational packet factorization and the rank-two Galois multiplicity space | the embedding (8.2) and determinant input | no integral Morita factor or canonical oldvector is imported |

Books 168, 177, 179, and 186--187 appear only in Chapter 10 to state what they may receive. They are not proof dependencies.

Every hypothesis of Theorem 5.1 has a visible role. The DVR makes a finite torsion-free coordinate algebra flat. Good reduction supplies ambient finite-flat torsion. Saturation makes the quotient inject into geometric torsion. Perfect residue field, henselianity, and $e<p-1$ invoke Raynaud full faithfulness. Rank two over $\mathcal O$ gives $q^{2n}$ and the determinant line. Prime-to-$p$ polarization degree makes the ambient pairing perfect, while a separate unit discriminant makes its restriction perfect; Rosati-stable ideals and a self-adjoint normalization determine whether that perfect self-duality is also the declared alternating polarization.

### 11.2 Failure tests

**Attack: schematic closure at every level automatically gives an exact tower.** It does not. The proof closes the generic kernel in the middle level, takes the represented quotient, and invokes Raynaud rigidity to identify that quotient with the independently constructed lower level.

**Attack: equal rank and equal generic fiber identify two finite-flat groups.** They do not outside a uniqueness theorem. Oort--Tate models at the ramification boundary are the obstruction. The proof uses full faithfulness, not a rank count.

**Attack: the coefficient action on generic points automatically acts on a chosen closure.** Generic fullness fails in general. In Theorem 5.1 the action extends by Raynaud full faithfulness; an honest ambient order action is a separate sufficient source outside that range.

**Attack: a rational packet projector gives the desired integral rank-two summand.** A nonunit projector denominator or a nonmaximal Hecke order can obstruct integral splitting. The construction chooses a nonzero finite automorphic vector rationally and saturates its image. It proves existence, not a canonical summand.

**Attack: principal polarization of the ambient Jacobian makes every saturated packet lattice self-dual.** A primitive sublattice of a unimodular lattice can have nonunit discriminant. Ambient degree and restricted discriminant are separate unit tests, and ramified coefficient levels still require the coefficient-adjoint normalization of Section 6.3.

**Attack: determinant reduction needs a perfect residual pairing.** It does not. Stable integral matrices already prove (6.6). Perfect pairing is stronger and needs the unit tests of Section 6.3.

**Attack: coefficient extension is just another embedding into the same abelian Tate module.** Its underlying $\mathbf Z_p$-rank can grow. Section 7.2 uses products, closure, and quotient; Section 7.3 retains the inverse different in duality.

**Attack: residual irreducibility over the displayed finite field is enough after coefficient extension.** Only absolute irreducibility has that permanence. Mere irreducibility can disappear after extending the residue field.

**Attack: untwisted curve cohomology is already a finite-flat Tate lattice.** Formula (8.3) shows the required twist. The geometric operations allowed here are passage to the covariant Tate module and Cartier-twisted duality, never an arbitrary negative Tate twist.

**Attack: the prime-two case is covered because every single closure is finite flat.** Levelwise flatness survives, but Raynaud rigidity and the Fontaine--Laffaille range do not. This book makes no dyadic all-level assertion from those inputs.

### 11.3 Conclusion

The integral package is now exact. A rational Galois-stable plane in a fixed coefficient-linear abelian Tate module meets the ambient lattice in a saturated stable rank-two lattice. Each quotient embeds in finite geometric torsion, and schematic closure produces a coefficient-sized finite-flat group of rank $q^{2n}$. In the low-ramification range, closing the generic kernel inside each higher level, taking the represented quotient, and applying Raynaud full faithfulness proves the exact sequences

$$
0\longrightarrow\mathcal G_m
\longrightarrow\mathcal G_{m+n}
\longrightarrow\mathcal G_n
\longrightarrow0
$$

for every $m,n$. The transitions are transitive, their generic fibers are the reductions of one lattice, and their inverse limit recovers that lattice.

Cartier duality reverses the tower with the required Tate twist. Determinants reduce without a self-duality hypothesis. Polarizations give perfect integral pairings only after both the ambient degree and restricted discriminant have passed their unit tests. Flat ground-field change preserves the constructed tower; coefficient change is realized by products, closures, and quotients and carries a different factor in duality when ramified.

For curve cohomology, a nonzero vector in the finite automorphic factor embeds the two-dimensional raw Galois multiplicity space rationally. The vector is a choice. Saturation then proves existence, and finite-flat subquotients give a separate tower on its abstract semisimplification without pretending that the semisimplification is the same geometric subspace. Residual absolute irreducibility can prove homothety, and none of these arguments proves canonicality. This is precisely the reusable finite-flat spine required later: one named lattice, every coefficient quotient, exact compatible transitions, coefficient actions, duality, determinant, polarization qualifications, and base change, with no unsupported integral Morita splitting or independence of arbitrary presentations.
