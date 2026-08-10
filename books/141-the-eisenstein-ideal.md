# The Eisenstein Ideal

## Contents

1. [The boundary eigensystem and the arithmetic problem](#1-the-boundary-eigensystem-and-the-arithmetic-problem)
   - [Why an Eisenstein ideal appears](#11-why-an-eisenstein-ideal-appears)
   - [Standing notation and the five trivial levels](#12-standing-notation-and-the-five-trivial-levels)
   - [The theorem package](#13-the-theorem-package)
   - [The dependency order](#14-the-dependency-order)
2. [Four integral Hecke realizations](#2-four-integral-hecke-realizations)
   - [The actual cusp lattice and its perfect coefficient pairing](#21-the-actual-cusp-lattice-and-its-perfect-coefficient-pairing)
   - [Anemic, full, relative, and augmented algebras](#22-anemic-full-relative-and-augmented-algebras)
   - [Why relative equals augmented](#23-why-relative-equals-augmented)
   - [The semistable correspondence theorem](#24-the-semistable-correspondence-theorem)
   - [The three special-fiber actions of $U_p$](#25-the-three-special-fiber-actions-of-u_p)
3. [The two-cusp integral Eisenstein bound](#3-the-two-cusp-integral-eisenstein-bound)
   - [The coefficient-one Eisenstein form](#31-the-coefficient-one-eisenstein-form)
   - [The Deligne--Rapoport--Katz theorem](#32-the-deligne--rapoport--katz-theorem)
   - [Why the theorem needs the stack and both cusps](#33-why-the-theorem-needs-the-stack-and-both-cusps)
   - [The independent upper bound](#34-the-independent-upper-bound)
   - [The cuspidal lower bound and exact index](#35-the-cuspidal-lower-bound-and-exact-index)
4. [The augmented crossing and its numerical meaning](#4-the-augmented-crossing-and-its-numerical-meaning)
   - [The integral fiber product](#41-the-integral-fiber-product)
   - [Saturated branches at an Eisenstein prime](#42-saturated-branches-at-an-eisenstein-prime)
   - [The conclusion supplied by the numerical criterion](#43-the-conclusion-supplied-by-the-numerical-criterion)
   - [Why no complete-intersection shortcut is available](#44-why-no-complete-intersection-shortcut-is-available)
5. [Cuspidal, Shimura, and component groups](#5-cuspidal-shimura-and-component-groups)
   - [Three cyclic objects with the same order](#51-three-cyclic-objects-with-the-same-order)
   - [The quadratic Shimura-character theorem](#52-the-quadratic-shimura-character-theorem)
   - [The exact cusp--Shimura intersection](#53-the-exact-cusp--shimura-intersection)
   - [Monodromy and the variance ledger](#54-monodromy-and-the-variance-ledger)
6. [Odd Eisenstein multiplicity one](#6-odd-eisenstein-multiplicity-one)
   - [The maximal ideal and the claimed finite group scheme](#61-the-maximal-ideal-and-the-claimed-finite-group-scheme)
   - [The Mazur--Raynaud infrastructure theorem](#62-the-mazur--raynaud-infrastructure-theorem)
   - [The two Selmer orientations](#63-the-two-selmer-orientations)
   - [The cyclotomic class-group input, including $\ell=3$](#64-the-cyclotomic-class-group-input-including-ell3)
   - [Admissible-group-scheme devissage](#65-admissible-group-scheme-devissage)
7. [Tate modules, duality, and the character lattice](#7-tate-modules-duality-and-the-character-lattice)
   - [From multiplicity one to two generators](#71-from-multiplicity-one-to-two-generators)
   - [Tate-module freeness](#72-tate-module-freeness)
   - [Gorenstein self-duality](#73-gorenstein-self-duality)
   - [Character-lattice freeness](#74-character-lattice-freeness)
   - [Why this chapter has no $2$-adic analogue](#75-why-this-chapter-has-no-2-adic-analogue)
8. [Rational torsion](#8-rational-torsion)
   - [The odd rational Eisenstein-support theorem](#81-the-odd-rational-eisenstein-support-theorem)
   - [The prime-level two-primary fixed-line theorem](#82-the-prime-level-two-primary-fixed-line-theorem)
   - [Rational points of exact prime order](#83-rational-points-of-exact-prime-order)
   - [The specialization and divisibility argument](#84-the-specialization-and-divisibility-argument)
   - [The exact torsion theorem and its Hecke action](#85-the-exact-torsion-theorem-and-its-hecke-action)
9. [The absolute winding quotient](#9-the-absolute-winding-quotient)
   - [From a relative path to a rational absolute class](#91-from-a-relative-path-to-a-rational-absolute-class)
   - [Construction and newform support](#92-construction-and-newform-support)
   - [The Kolyvagin--Logachev rank-zero theorem](#93-the-kolyvagin--logachev-rank-zero-theorem)
   - [Finiteness of rational points](#94-finiteness-of-rational-points)
10. [Integral cotangents and formal immersion](#10-integral-cotangents-and-formal-immersion)
    - [The winding-quotient cotangent theorem](#101-the-winding-quotient-cotangent-theorem)
    - [Producing the formal immersion](#102-producing-the-formal-immersion)
    - [Odd good-prime cusp-disk rigidity](#103-odd-good-prime-cusp-disk-rigidity)
    - [Why the Jacobian torsion theorem does not settle the quotient at $2$](#104-why-the-jacobian-torsion-theorem-does-not-settle-the-quotient-at-2)
11. [Four diagnostic prime levels](#11-four-diagnostic-prime-levels)
    - [Levels $11$, $17$, and $19$](#111-levels-11-17-and-19)
    - [Level $37$](#112-level-37)
    - [What the diagnostics verify](#113-what-the-diagnostics-verify)
12. [The exported theorem ledger](#12-the-exported-theorem-ledger)
    - [The prime-level Eisenstein package](#121-the-prime-level-eisenstein-package)
    - [The infrastructure ledger](#122-the-infrastructure-ledger)
    - [The dependency audit](#123-the-dependency-audit)
    - [The exact interface with Book 148](#124-the-exact-interface-with-book-148)
    - [Conclusion](#125-conclusion)

## 1. The boundary eigensystem and the arithmetic problem

### 1.1 Why an Eisenstein ideal appears

The two rational cusps of a prime-level modular curve form the smallest possible boundary. A Hecke correspondence away from the level has $q+1$ incoming branches at each cusp, while the incoming correspondence at the level preserves the oriented cusp difference. The boundary therefore carries the one-dimensional system

$$
T_q\longmapsto q+1,\qquad U_p\longmapsto1.
$$

Holomorphic cusp forms have no boundary values. The Eisenstein problem asks how closely an integral cuspidal eigensystem can approach this boundary system. The answer is not merely a congruence of Fourier coefficients. The same modulus governs a rational cusp class, a multiplicative finite subgroup, the component group at the bad prime, and the residual constant--cyclotomic representation in the Jacobian.

Those manifestations must nevertheless be kept separate. A free boundary class in relative homology is not the torsion cusp class in the Jacobian. A character of the torus is not a component. A constant group scheme is not a multiplicative one, even when their geometric point sets have the same size. Much of this book is devoted to constructing the maps among these objects and proving that the common integer which appears is forced independently in each realization.

The ultimate purpose is geometric. Book 148 will send a rational point of $X_0(p)$ to a finite quotient of $J_0(p)$ and use reduction at a cusp. The present book supplies the exact torsion, the finite winding quotient, and the formal-immersion statement required for that argument. It deliberately stops before classifying prime degrees of rational isogenies.

### 1.2 Standing notation and the five trivial levels

Let $p$ be prime. For the main argument assume $p\ge5$ and put

$$
X=X_0(p),\qquad J=J_0(p),\qquad
c=[0]-[\infty],\qquad
n=\frac{p-1}{\gcd(p-1,12)}.
$$

The incoming convention for correspondences is the convention of Books 122 and 140. In particular, if a correspondence is displayed as

$$
X\xleftarrow{\beta}Y\xrightarrow{\alpha}X,
$$

its covariant action on divisors, the Jacobian, and homology is $\alpha_*\beta^*$. All Tate modules are covariant. Arithmetic Frobenius acts on them, and the Tate twist is retained in every duality statement.

Throughout, $q$ denotes a prime distinct from $p$ when it indexes a Hecke generator, while $m$ denotes an arbitrary positive integer.

The levels

$$
p=2,3,5,7,13
$$

are handled separately. Book 139 proves that $X_0(p)$ has genus zero at precisely these prime levels, and Book 140 gives

$$
J_0(p)=0,\qquad n=1.
$$

The faithful cuspidal Hecke algebra is then the zero ring, and

$$
\mathbb T/I=0=\mathbf Z/1\mathbf Z,\qquad
C=\Sigma=\Phi_p=0,\qquad
J(\mathbf Q)_{\mathrm{tors}}=0.
$$

There is no nonzero winding quotient in genus zero. Every later assertion about a nonzero winding quotient is therefore made only for the positive-genus prime levels, namely $p=11$ or $p\ge17$. The statements about $p=2,3$ do not rely on extending the $p\ge5$ integral-stack arguments into wild level characteristic.

### 1.3 The theorem package

The central result can now be stated without concealing its qualifications.

**Prime-level Eisenstein theorem.** Let $p\ge5$ be prime. Let $\mathbb T$ be the faithful full integral Hecke algebra acting on the actual integral lattice $S_2(\Gamma_0(p),\mathbf Z)$, with incoming $U_p$, and define

$$
I=(T_q-q-1:q\ne p)+(U_p-1).
$$

Then

$$
\boxed{\mathbb T/I\simeq\mathbf Z/n\mathbf Z.}
$$

Moreover,

$$
C=\langle c\rangle\simeq\mathbf Z/n\mathbf Z,\qquad
\Sigma\simeq\mu_n,\qquad
\Phi_p\simeq\mathbf Z/n\mathbf Z,
$$

specialization induces an isomorphism $C\xrightarrow{\sim}\Phi_p$, and

$$
C\cap\Sigma=C[\gcd(n,2)].
$$

For every odd prime $\ell\mid n$, with $\mathfrak m=(\ell,I)$,

$$
J[\mathfrak m]\simeq\mathbf Z/\ell\mathbf Z\oplus\mu_\ell.
$$

After that multiplicity-one statement is established, it implies in order

$$
T_\ell J_{\mathfrak m}\simeq\mathbb T_{\mathfrak m}^{2},\qquad
\mathbb T_{\mathfrak m}^{\vee}\simeq\mathbb T_{\mathfrak m},\qquad
X_{p,\mathfrak m}\simeq\mathbb T_{\mathfrak m}.
$$

No corresponding multiplicity-one assertion is made at $2$. Instead a separate integral fixed-line theorem supplies the two-primary rational torsion. For every prime level,

$$
\boxed{J_0(p)(\mathbf Q)_{\mathrm{tors}}=C.}
$$

If $X_0(p)$ has positive genus, the absolute winding class defines a nonzero optimal quotient $J^{\mathrm w}$ supported on precisely the newform factors with $L(f,1)\ne0$, and

$$
J^{\mathrm w}(\mathbf Q)
$$

is finite. A Hecke translate of $X_0(p)\to J^{\mathrm w}$ is a formal immersion at either cusp in every good residue characteristic. The clean rational-point consequence used here is at an odd good prime. No quotient-level assertion about the kernel of specialization at $2$ is inferred from the torsion theorem for $J$.

### 1.4 The dependency order

The order of proof prevents the main conclusions from certifying their own hypotheses. First, integral modular geometry gives an upper bound for the Eisenstein quotient; the known cusp of order $n$ gives the independent lower bound. Only after those two bounds meet do we identify the augmented algebra as a fiber product.

Second, the quadratic Shimura-character theorem identifies the possible common order-two point of $C$ and $\Sigma$. Character theory then excludes every larger intersection. Third, the odd multiplicity-one theorem is taken as deep classical infrastructure in the same explicit sense that Book 67 takes Raynaud and Fontaine--Laffaille theory as infrastructure. From multiplicity one we prove Tate-module freeness by Nakayama and generic rank, then Gorenstein self-duality, then character-lattice freeness. None of these arrows is reversed.

Fourth, rational points of prime order are determined using the odd support theorem and the separate two-primary fixed-line theorem. The isomorphism $C\simeq\Phi_p$ then lifts the result through all prime powers. Only after rational torsion has been identified with $C$ do we conclude that the Eisenstein ideal annihilates all rational torsion.

Finally, winding is constructed in absolute homology. The passage from nonzero central $L$-values to finite Mordell--Weil groups uses the full Kolyvagin--Logachev theorem. Formal immersion is then an integral cotangent statement for the optimal quotient. This last step does not assume that rational torsion on a quotient lifts to rational torsion on the Jacobian.

## 2. Four integral Hecke realizations

### 2.1 The actual cusp lattice and its perfect coefficient pairing

An exact index requires a fixed integral lattice. Let $\mathscr X_0(p)$ be the unrigidified compactified modular stack over $\mathbf Z$, and let $\omega_{\mathrm{dual}}$ denote its relative dualizing sheaf. Set

$$
S_2(\mathbf Z)
=H^0(\mathscr X_0(p),\omega_{\mathrm{dual}})
=S_2(\Gamma_0(p),\mathbf Q)\cap\mathbf Z[[q]].
$$

The last equality is the integral $q$-expansion and base-change theorem: the Tate expansion embeds the dualizing lattice as a saturated lattice, with integrality compatible with expansion at every cusp and every stack chart. It is not a definition obtained by taking a naive coarse curve and declaring one $q$-expansion integral. At $2$ and $3$ the unrigidified stack retains the stabilizer conditions needed for saturation.

For $m\ge1$, write $T_m$ for the usual integral operator, with

$$
T_{p^ru}=U_p^rT_u,\qquad (u,p)=1.
$$

The fundamental coefficient identity is

$$
a_1(T_mf)=a_m(f). \tag{2.1}
$$

It turns the first coefficient into a universal normalization functional.

**Perfect Hecke--expansion theorem.** On the actual integral cusp lattice, the pairing

$$
\mathbb T\times S_2(\mathbf Z)\longrightarrow\mathbf Z,\qquad
(t,f)\longmapsto a_1(tf) \tag{2.2}
$$

is perfect. Thus

$$
S_2(\mathbf Z)\simeq\operatorname{Hom}_{\mathbf Z}(\mathbb T,\mathbf Z). \tag{2.3}
$$

The hypotheses in this statement matter. The algebra is the faithful image on the displayed lattice, it contains the incoming $U_p$, and integrality is tested on the stack lattice. Injectivity follows from (2.1) and the $q$-expansion principle. Surjectivity is the integral saturation assertion: the coefficient functionals generated by the $T_m$ form the full dual lattice, rather than a finite-index sublattice. Its proof uses integral $q$-expansion and base change on the compactification, including the wild charts at $2$ and $3$.

This theorem is established infrastructure. Its construction-level content is nevertheless transparent: Hecke correspondences manufacture every coefficient from $a_1$, while saturation says that a rational cusp form whose every coefficient functional is integral was already an integral dualizing differential. We shall use (2.2) to turn additive characters of a Hecke quotient into rational cusp forms.

### 2.2 Anemic, full, relative, and augmented algebras

Different realizations remember different parts of the boundary. Let

$$
\mathcal H=\mathbf Z[T_q\ (q\ne p),U_p]
$$

be the abstract commutative algebra mapping to the geometric correspondences. Define the Eisenstein augmentation

$$
\epsilon:\mathcal H\longrightarrow\mathbf Z,\qquad
\epsilon(T_q)=q+1,\qquad \epsilon(U_p)=1. \tag{2.4}
$$

The **anemic cuspidal algebra** is

$$
\mathbb T^{\mathrm{an}}
=\operatorname{im}\left(
\mathbf Z[T_q:q\ne p]\to
\operatorname{End}_{\mathbf Z}S_2(\mathbf Z)
\right). \tag{2.5}
$$

The **full cuspidal algebra** is

$$
\mathbb T
=\operatorname{im}\left(
\mathcal H\to\operatorname{End}_{\mathbf Z}S_2(\mathbf Z)
\right). \tag{2.6}
$$

It is faithful by definition and agrees with the image on $J$ and on absolute homology. This is an equality of image algebras, not an assertion that the abstract algebra is faithful on every realization.

Put

$$
H=H_1(X(\mathbf C),\mathbf Z),\qquad
H^{\mathrm{rel}}=H_1(X(\mathbf C),\{0,\infty\};\mathbf Z).
$$

The **relative algebra** is

$$
\mathbb T^{\mathrm{rel}}
=\operatorname{im}\left(
\mathcal H\to\operatorname{End}_{\mathbf Z}H^{\mathrm{rel}}
\right). \tag{2.7}
$$

The **augmented algebra** is

$$
\mathbb T^{\mathrm{aug}}
=\operatorname{im}\left(
\mathcal H\longrightarrow\mathbb T\times\mathbf Z,
\ t\longmapsto(t,\epsilon(t))
\right). \tag{2.8}
$$

The free group $\operatorname{Div}^0\{0,\infty\}$ and the finite group $C\subset J$ must not be identified. The former is the quotient of relative homology; the latter is its Abel--Jacobi image. This distinction is the reason the relative Eisenstein quotient is infinite while the cuspidal Eisenstein quotient is finite.

### 2.3 Why relative equals augmented

The relative algebra might appear to contain an off-diagonal action invisible on absolute homology and on the boundary. Mixed Hodge theory rules out exactly that possibility.

The exact homology sequence is

$$
0\longrightarrow H
\longrightarrow H^{\mathrm{rel}}
\xrightarrow{\partial}
\operatorname{Div}^0\{0,\infty\}
\longrightarrow0. \tag{2.9}
$$

All three groups are torsion free. Over $\mathbf Q$, (2.9) is an exact sequence of mixed Hodge structures. The absolute homology has pure weight $-1$, while the reduced boundary group has weight $0$.

The action on the subobject and quotient gives a homomorphism

$$
\mathbb T^{\mathrm{rel}}\longrightarrow\mathbb T^{\mathrm{aug}}. \tag{2.10}
$$

Suppose an abstract Hecke operator acts trivially on $H$ and on the boundary quotient. Its action on $H^{\mathrm{rel}}_{\mathbf Q}$ then factors as a morphism

$$
\operatorname{Div}^0\{0,\infty\}_{\mathbf Q}
\longrightarrow H_{\mathbf Q}. \tag{2.11}
$$

Hecke correspondences act by morphisms of mixed Hodge structures. Strictness for the weight filtration makes (2.11) zero, because there is no nonzero morphism from a pure weight-$0$ object to a pure weight-$-1$ object. Hence the original operator is zero on $H^{\mathrm{rel}}_{\mathbf Q}$. Torsion-freeness of $H^{\mathrm{rel}}$ makes it zero integrally.

The map (2.10) is therefore injective. It is surjective because both sides are the images of the same abstract generators with the same two recorded actions. Consequently

$$
\boxed{\mathbb T^{\mathrm{rel}}\simeq\mathbb T^{\mathrm{aug}}.} \tag{2.12}
$$

This proof uses neither a splitting of (2.9) over $\mathbf Z$ nor division by the degree of a trace. It is precisely the weight separation, followed by integral torsion-freeness, that removes the possible off-diagonal operator.

### 2.4 The semistable correspondence theorem

The operator at the level controls signs, components, and the missing Hecke relation in the torsion argument. Its integral construction cannot be replaced by a picture of one node.

**Semistable $U_p$ correspondence theorem.** Let $p\ge5$. Add a neat prime-to-$p$ auxiliary level so that the modular problem is represented by a scheme, form the Deligne--Rapoport compactification, and let $\mathcal Y$ be the normalization of the compactified $p^2$-correspondence parametrizing chains of cyclic subgroup schemes of orders $p$ and $p^2$. The two forgetful maps

$$
\mathcal X\xleftarrow{\beta}\mathcal Y\xrightarrow{\alpha}\mathcal X
$$

are used with their scheme-theoretic multiplicities. Then:

1. the incoming action on divisors, the Jacobian, and covariant homology is $U_p=\alpha_*\beta^*$;
2. its action adjoint on relative dualizing differentials is $\beta_*\alpha^*$, and at the Tate cusp it is the Fourier operator

   $$
   \sum_{m\ge0}a_mq^m\longmapsto\sum_{m\ge0}a_{pm}q^m;
   $$

3. the identity $U_p=-w_p$ holds integrally on the prime-level cusp space and on the corresponding Jacobian and absolute-homology realizations;
4. on the boundary and on the Néron component group, $U_p$ acts as $1$;
5. if

   $$
   X_p=\operatorname{Div}^0(S_p)
   $$

   is the geometric character lattice of the torus at $p$, and

   $$
   \sigma[s]=[s^{(p)}]
   $$

   is the $p$-power Frobenius permutation of supersingular classes, then the incoming action on $X_p$ is $U_p=\sigma$.

The proof architecture explains every clause. The auxiliary neat level removes stabilizers while the correspondence is normalized; it is removed only after pullback, trace, and multiplicities have been checked. Grothendieck duality for finite maps of the normalized correspondence identifies the differential action with pullback followed by trace on the relative dualizing sheaf. No ordinary-differential calculation at a node is substituted for this dualizing operation.

On the generic fiber, prime level is entirely new in weight two because $S_2(\mathrm{SL}_2(\mathbf Z))=0$. The two degeneracy maps from level one therefore make the usual newspace relation reduce to

$$
U_p=-w_p.
$$

Both sides preserve the saturated integral cusp lattice, so the rational identity is integral. On the special fiber, the normalized $p^2$ correspondence has several subgroup-chain strata. Following both maps through those strata gives the boundary and component action $1$. Book 140 gives $w_p=-\sigma$ on the oriented character lattice; combining this with $U_p=-w_p$ gives $U_p=\sigma$ with the correct variance.

This is established semistable infrastructure. A single local nodal chart describes only one lifted crossing of the $X_0(p)$ model; it neither describes the global $p^2$ correspondence nor justifies an integral descent by dividing a trace degree.

### 2.5 The three special-fiber actions of $U_p$

It is useful to display why the apparently different formulas are compatible. The cusp and component group record a difference of the two principal components. The Frobenius permutation does not change that difference, so the action induced by $\sigma$ on the cyclic discriminant group is $1$. On the full character lattice, however, supersingular classes need not be individually fixed over $\mathbf F_p$, and the permutation must remain visible.

Thus the variance ledger is

$$
\begin{array}{c|c|c}
\text{realization}&U_p&w_p\\ \hline
S_2(\mathbf Z),\ J,\ H&-w_p&w_p\\
\operatorname{Div}^0\{0,\infty\}&1&-1\\
\Phi_p&1&-1\\
X_p&\sigma&-\sigma.
\end{array} \tag{2.13}
$$

The first row is an operator identity, not a scalar assertion: different newforms can have different signs. The final row is an identity on the character lattice, not on its dual unless the monodromy pairing is used to transport it. This table will later prevent a rational fixed point from being analyzed with the wrong $U_p$ action.

## 3. The two-cusp integral Eisenstein bound

### 3.1 The coefficient-one Eisenstein form

The boundary eigensystem has a canonical characteristic-zero differential. Start with

$$
E_2(q)=1-24\sum_{m\ge1}\sigma_1(m)q^m
$$

and define

$$
E_p=\frac{pE_2(q^p)-E_2(q)}{24}. \tag{3.1}
$$

The nonmodular transformation term of $E_2$ cancels in this combination. Hence $E_p$ is a rational weight-two modular form of level $p$. Expanding gives

$$
E_p=\frac{p-1}{24}+\sum_{m\ge1}b_mq^m,\qquad
b_m=\sum_{\substack{d\mid m\\p\nmid d}}d. \tag{3.2}
$$

Indeed the coefficient of $q^m$ is $\sigma_1(m)$ when $p\nmid m$, while for $m=pr$ it is $\sigma_1(pr)-p\sigma_1(r)$, which removes exactly the divisors divisible by $p$. The same calculation at every $p$-adic valuation of $m$ gives (3.2).

The Atkin--Lehner and level-operator formulas are

$$
w_pE_p=-E_p,\qquad U_pE_p=E_p. \tag{3.3}
$$

For the first, use the transformation of the logarithmic derivative of

$$
\frac{\Delta(pz)}{\Delta(z)};
$$

$w_p$ exchanges its zero and pole divisors and reverses the logarithmic differential. For the second, (3.2) gives $b_{pm}=b_m$, including repeated powers of $p$, and the constant term is unchanged by the Fourier $U_p$ operator. Thus $E_p$ is the coefficient-one logarithmic Eisenstein eigenform for (2.4).

The constant $(p-1)/24$ is not the final congruence modulus. The exact prime exponents of $n$ are

$$
\begin{array}{c|c}
\ell&e_\ell=v_\ell(n)\\ \hline
2&\max(v_2(p-1)-2,0)\\
3&\max(v_3(p-1)-1,0)\\
\ell\ge5&v_\ell(p-1).
\end{array} \tag{3.4}
$$

At $2$, the constant term alone is short by one power. The missing step is a divided congruence visible only after both cusps and the wild stack geometry are retained.

### 3.2 The Deligne--Rapoport--Katz theorem

We now state the deep integral theorem which supplies the upper bound. Its strength is maximality through every prime power, including the wild primes $2$ and $3$.

**Two-cusp integral Eisenstein theorem.** Let $p\ge5$ be prime and let $b_m$ be as in (3.2). Suppose

$$
x\in\mathbf Q/\mathbf Z,\qquad
g\in S_2(\Gamma_0(p),\mathbf Q)
$$

satisfy

$$
a_m(g)-xb_m\in\mathbf Z
\qquad\text{for every }m\ge1, \tag{3.5}
$$

where a rational representative of $x$ may be used because the condition is taken modulo $\mathbf Z$. Then

$$
nx=0\quad\text{in }\mathbf Q/\mathbf Z. \tag{3.6}
$$

Prime by prime, if $x$ has $\ell$-power order, that order is at most $\ell^{e_\ell}$ with $e_\ell$ given by (3.4). The assertion includes $\ell=3$ and every higher power of $2$ or $3$ permitted by the table.

The theorem is an established Deligne--Rapoport--Katz input. It is not a consequence of the order of the cuspidal divisor, and its proof does not use the desired Hecke index. It is the independent integral obstruction against a cusp form being too congruent to $E_p$.

### 3.3 Why the theorem needs the stack and both cusps

The construction behind the theorem explains both the denominator $12$ and the exceptional behavior at $2$. One works first on the unrigidified compactified modular stack. The Hodge bundle $\omega$ exists there because the universal generalized elliptic curve exists there. The generic automorphism $[-1]$ acts as $-1$ on $\omega$, so $\omega$ itself does not descend after rigidification by $\{\pm1\}$; only $\omega^2$ does. Weight-two forms must therefore be followed through the descent of $\omega^2$, not through a fictitious descent of $\omega$.

If $D_{\mathrm{cusp}}$ denotes the cusp divisor, Kodaira--Spencer identifies $\omega^2$ with the logarithmic dualizing sheaf $\omega_{\mathrm{dual}}(D_{\mathrm{cusp}})$, while cusp forms are sections of $\omega^2(-D_{\mathrm{cusp}})\simeq\omega_{\mathrm{dual}}$. At nodal fibers $\omega_{\mathrm{dual}}$ is the relative dualizing sheaf, not the sheaf of ordinary Kähler differentials. Replacing it by ordinary differentials at a node loses the residue and base-change exactness which control the integral lattice.

There are two cusp expansions. The global residue theorem makes their residues opposite in characteristic zero, while integral base change and saturation require both completed cusp discs. A one-cusp calculation sees $(p-1)/24$ but cannot decide whether an equal-value Hasse direction is compatible with the opposite boundary value at the other cusp.

Away from $2$ and $3$, the $q$-expansion principle and Katz's filtration theorem show that a putative congruence is bounded by $v_\ell(p-1)$. A missing coefficient at the characteristic prime would put the reduction in the kernel of Katz's $\Theta$ operator. Filtration rules then force a Frobenius pullback and a Hasse factor of incompatible weight.

At $3$, the weight-two Hasse invariant has expansion $1$, but its equal values at the two cusps do not match the opposite Eisenstein residues. Exactly one factor of $3$ is removed. At $2$, the square of the weight-one Hasse invariant has weight two, and equal and opposite residues coincide modulo $2$. It contributes exactly one extra divided-congruence step beyond the raw constant term. The next lift is obstructed on the integral stack, so the exponent is $v_2(p-1)-2$, not $v_2(p-1)-3$ and not $v_2(p-1)-1$.

The proof uses the unrigidified stack, its stabilizer representations, integral divided congruences, and Katz filtration through all powers. It does not model the wild points by diagonal $\mu_2$ or $\mu_3$ quotient charts; such diagonal charts do not describe the non-linearly reductive integral stabilizers and would give an unjustified saturation calculation.

### 3.4 The independent upper bound

Let

$$
Q=\mathbb T/I.
$$

Every abstract generator becomes an integer in $Q$, so the additive group of $Q$ is generated by $1$. In particular, an additive character $\varphi:Q\to\mathbf Q/\mathbf Z$ is determined by

$$
x=\varphi(1).
$$

The perfect pairing (2.2) represents $\varphi$ by a class

$$
g+S_2(\mathbf Z)\in
S_2(\Gamma_0(p),\mathbf Q)/S_2(\mathbf Z), \tag{3.7}
$$

with

$$
\varphi(t)=a_1(tg)\pmod{\mathbf Z}.
$$

Taking $t=1$ gives $a_1(g)\equiv x$. In $Q$, the Hecke relations and $U_p=1$ give

$$
T_m=b_m
$$

for every $m\ge1$. This follows first for primes, then for prime powers from the Hecke recurrence, multiplicatively for coprime indices, and at powers of $p$ from $U_p=1$. Consequently

$$
a_m(g)-xb_m\in\mathbf Z
$$

for every $m$. The two-cusp integral theorem gives $nx=0$.

Thus every character of $Q$ takes values in the subgroup killed by $n$. The finite-rank algebra $\mathbb T$ makes $Q$ a finitely generated cyclic abelian group. An infinite cyclic $Q$ would admit a character sending $1$ to an element of order greater than $n$, a contradiction. If $Q\simeq\mathbf Z/d\mathbf Z$, its character sending $1$ to $1/d$ shows that $d\mid n$. Therefore

$$
\#Q\le n. \tag{3.8}
$$

No fact about the order of $c$ entered this argument. The upper bound belongs entirely to the perfect coefficient pairing and the two-cusp integral theorem.

### 3.5 The cuspidal lower bound and exact index

Book 140 proves independently that $c$ has exact order $n$. It also proves, with the incoming convention,

$$
T_qc=(q+1)c\quad(q\ne p),\qquad
U_pc=c. \tag{3.9}
$$

Hence $I$ annihilates $C=\langle c\rangle$, and restriction gives a surjective ring map

$$
\mathbb T/I\longrightarrow\operatorname{End}(C)\simeq\mathbf Z/n\mathbf Z. \tag{3.10}
$$

It is surjective because integral scalars already act by every residue class. Therefore

$$
n\le\#Q. \tag{3.11}
$$

Combining (3.8) and (3.11) proves

$$
\boxed{\mathbb T/I\simeq\mathbf Z/n\mathbf Z.} \tag{3.12}
$$

The two inequalities have different sources. The cusp gives only the lower bound; the integral two-cusp theorem gives only the upper bound. Their independence is the central logical safeguard in the index calculation.

## 4. The augmented crossing and its numerical meaning

### 4.1 The integral fiber product

The augmented algebra remembers the characteristic-zero boundary branch together with all cuspidal branches. Once (3.12) is known, its integral gluing becomes explicit.

There is a natural inclusion

$$
\mathbb T^{\mathrm{aug}}\hookrightarrow\mathbb T\times\mathbf Z.
$$

Every element $(t,a)$ in its image satisfies

$$
t\equiv a\pmod I,
$$

so it lies in the fiber product

$$
\mathbb T\times_{\mathbf Z/n\mathbf Z}\mathbf Z. \tag{4.1}
$$

Conversely, suppose $(t,a)$ satisfies this congruence. Then $t-a\in I$. By definition, every element of $I$ is the cuspidal image of an element of $\ker\epsilon\subset\mathcal H$. Adding the scalar $a$ produces an abstract operator whose two images are exactly $(t,a)$. Hence

$$
\boxed{
\mathbb T^{\mathrm{aug}}
\simeq\mathbb T\times_{\mathbf Z/n\mathbf Z}\mathbf Z.} \tag{4.2}
$$

Together with (2.12), this also computes the relative Hecke algebra. The relative Eisenstein quotient is $\mathbf Z$, not $\mathbf Z/n\mathbf Z$, because the boundary branch itself survives there.

### 4.2 Saturated branches at an Eisenstein prime

Fix a prime $\ell\mid n$, put

$$
a=v_\ell(n),\qquad
R=(\mathbb T\otimes\mathbf Z_\ell)_{\mathfrak m}
=\mathbb T_{\mathfrak m},\qquad
\mathfrak m=(\ell,I),
$$

where the last notation denotes the complete local factor, and complete the augmented algebra at the maximal ideal determined by $\mathfrak m$ and the boundary augmentation. Formula (4.2) gives

$$
A=R\times_{\mathbf Z_\ell/\ell^a\mathbf Z_\ell}\mathbf Z_\ell. \tag{4.3}
$$

After inverting $\ell$, the congruence condition disappears:

$$
A_{\mathbf Q_\ell}=R_{\mathbf Q_\ell}\times\mathbf Q_\ell.
$$

The saturated cuspidal and Eisenstein branch lattices are intersections with these two rational factors. They are

$$
L_{\mathrm c}=I_{\mathfrak m}\times0,\qquad
L_{\mathrm E}=0\times\ell^a\mathbf Z_\ell. \tag{4.4}
$$

Indeed an integral point supported only on the cuspidal factor must have zero common residue, hence lies in $I_{\mathfrak m}$; an integral point supported only on the boundary factor must be divisible by $\ell^a$. Therefore

$$
A/(L_{\mathrm c}+L_{\mathrm E})
\simeq\mathbf Z_\ell/\ell^a\mathbf Z_\ell. \tag{4.5}
$$

This is the branch congruence module. Formula (4.4) is a saturation statement inside the rational product, not an arbitrary choice of two embedded submodules.

### 4.3 The conclusion supplied by the numerical criterion

Let $\lambda:A\to\mathbf Z_\ell$ be projection to the boundary factor. Its augmentation ideal is

$$
I_A=I_{\mathfrak m}\times0,
$$

and consequently

$$
I_A/I_A^2\simeq I_{\mathfrak m}/I_{\mathfrak m}^2. \tag{4.6}
$$

The quotient $R/I_{\mathfrak m}\simeq\mathbf Z_\ell/\ell^a\mathbf Z_\ell$ vanishes after inverting $\ell$, so $I_{\mathfrak m}R_{\mathbf Q_\ell}=R_{\mathbf Q_\ell}$. Since $R$ is $\mathbf Z_\ell$-torsion free, $\operatorname{Ann}_R(I_{\mathfrak m})=0$. It follows directly from the fiber product that

$$
\operatorname{Ann}_A(I_A)
=0\times\ell^a\mathbf Z_\ell,
\qquad
\lambda(\operatorname{Ann}_A(I_A))
=\ell^a\mathbf Z_\ell.
$$

Thus Book 71's congruence module is exactly the cyclic module in (4.5). The algebra $A$ is finite flat over $\mathbf Z_\ell$, and its generic fiber

$$
A_{\mathbf Q_\ell}
=R_{\mathbf Q_\ell}\times\mathbf Q_\ell
$$

has the boundary as an isolated field factor; the hypotheses of the fundamental numerical inequality are therefore satisfied. That inequality says that relative cotangent length dominates congruence length. Applying it gives exactly

$$
\boxed{
\operatorname{length}_{\mathbf Z_\ell}
(I_{\mathfrak m}/I_{\mathfrak m}^2)\ge a.} \tag{4.7}
$$

This is the full conclusion available from the index theorem alone. Equality would require an independent upper bound for the cotangent module. No such upper bound is supplied merely by knowing $\mathbb T/I$.

### 4.4 Why no complete-intersection shortcut is available

The projection $A\to R$ kills the boundary lattice

$$
0\times\ell^a\mathbf Z_\ell.
$$

Every element of this kernel annihilates $I_{\mathfrak m}\times0$. It is therefore a zero divisor whenever the cuspidal factor is nonzero. A theorem about quotients by regular sequences cannot be applied to this projection.

Even if an independent argument proved that the augmented crossing $A$ were a complete intersection, neither complete-intersection structure nor Gorenstein duality could be passed to $R$ through this zero-divisor quotient. The odd Gorenstein theorem for $R$ will instead be proved from multiplicity one and the polarized Tate module. Keeping these arguments separate is essential: branch gluing measures the Eisenstein congruence, while Gorensteinness is a self-duality property of the cuspidal local algebra.

## 5. Cuspidal, Shimura, and component groups

### 5.1 Three cyclic objects with the same order

The exact index has three geometric companions, already constructed in Book 140. We recall their independent origins because the later intersection and torsion proofs use their maps, not only their orders.

The eta quotient and its full multiplier calculation give

$$
C=\langle c\rangle\simeq\mathbf Z/n\mathbf Z. \tag{5.1}
$$

The multiplier, including the rational descent character, proves exactness; a divisor computation alone would prove only an upper bound.

Let

$$
\pi:X_1(p)\longrightarrow X_0(p)
$$

be the compactified forgetful map. The Shimura subgroup is the scheme-theoretic kernel of pullback on Jacobians. Picard descent through the deck group

$$
\Delta=(\mathbf Z/p\mathbf Z)^\times/\{\pm1\}
$$

and its cusp and elliptic inertia gives

$$
\Sigma\simeq\mu_n. \tag{5.2}
$$

This is an isomorphism of group schemes. It does not say that $\Sigma(\mathbf Q)$ has $n$ points.

At $p$, Book 140 identifies the toric character lattice and its monodromy pairing as

$$
X_p=\operatorname{Div}^0(S_p),\qquad
\langle x,y\rangle=\sum_{s\in S_p}w_sx_sy_s,\qquad
w_s=\frac{\#\operatorname{Aut}(E_s)}2. \tag{5.3}
$$

The exact sequence

$$
0\longrightarrow X_p
\longrightarrow X_p^\vee
\longrightarrow\Phi_p
\longrightarrow0 \tag{5.4}
$$

and the supersingular mass formula give

$$
\Phi_p\simeq\mathbf Z/n\mathbf Z. \tag{5.5}
$$

The two cusp sections meet the two principal components, so $c$ maps to the vertex-difference generator. Hence specialization is an isomorphism

$$
\boxed{C\xrightarrow{\sim}\Phi_p.} \tag{5.6}
$$

The explicit component calculation, not equality of cardinalities, proves that this map is an isomorphism.

### 5.2 The quadratic Shimura-character theorem

Constant and multiplicative group schemes can meet at order two, because the mod-$2$ cyclotomic character is trivial. Identifying the actual common point is a deep descent calculation.

The valuation formula (3.4) shows

$$
n\text{ is even}
\quad\Longleftrightarrow\quad
v_2(p-1)\ge3
\quad\Longleftrightarrow\quad
p\equiv1\pmod8. \tag{5.7}
$$

Under this condition the Legendre character

$$
\chi_p:\Delta\longrightarrow\{\pm1\},\qquad
\chi_p(a)=\left(\frac ap\right) \tag{5.8}
$$

is well defined.

**Quadratic Shimura-character theorem.** Assume $p\equiv1\pmod8$. Picard descent of the $\chi_p$-linearized trivial line on $X_1(p)$ defines a point

$$
\sigma_{\chi_p}\in\Sigma[2](\mathbf Q).
$$

Under the embedding $\Sigma\subset J$ and with $c=[0]-[\infty]$,

$$
\boxed{\sigma_{\chi_p}=\frac n2c.} \tag{5.9}
$$

The theorem is established quadratic descent infrastructure. Its construction uses the compactified cover, Picard descent, and the theta groups supplied by the canonical polarization. The boundary computation is carried out with the full family of Siegel functions. Their exact cusp orders are

$$
\operatorname{ord}_{b/p}g_{(a/p,0)}
=\frac p2B_2\left(\left\langle\frac{ab}{p}\right\rangle\right), \tag{5.10}
$$

and the generalized-Bernoulli pairing obtained by summing (5.10) against $\chi_p(a)$ computes the theta character at every cusp orbit. The multiplier at infinity, the width-$p$ parameter at zero, the elliptic inertia, and the rational descent character are all retained. The result singles out $(n/2)c$ and proves (5.9).

This proof architecture matters. A function transforming through a nontrivial deck character cannot at the same time be used as an invariant rational function downstairs with the same divisor. The theorem does not use such an impossible deck-eigen invariant-divisor identity. The descended object is a line bundle with linearization, and its comparison with the cusp class occurs through Picard descent and theta groups.

### 5.3 The exact cusp--Shimura intersection

We can now prove the intersection completely. Let $G=C\cap\Sigma$ as a finite subgroup scheme over $\mathbf Q$.

If an odd prime $\ell$ divides $\#G$, then $G$ contains a subgroup scheme of order $\ell$. As a subgroup of the constant group $C$, its geometric points carry the trivial Galois character. As a subgroup of $\Sigma\simeq\mu_n$, they carry the mod-$\ell$ cyclotomic character. These two characters are distinct over $\mathbf Q$ for odd $\ell$. Hence $G$ has no odd-order part.

Suppose the $2$-primary part of $G$ has order at least $4$. It then contains a cyclic subgroup of order $4$. The constant action on that subgroup is trivial, while the action on $\mu_4$ is cyclotomic and is nontrivial under complex conjugation. This is again impossible. Thus $G$ has order at most two.

If $n$ is odd, $C[2]=0$, so $G=0$. If $n$ is even, the quadratic theorem gives

$$
\frac n2c=\sigma_{\chi_p}\in C\cap\Sigma,
$$

and this is the unique nonzero point of $C[2]$. Therefore

$$
\boxed{C\cap\Sigma=C[\gcd(n,2)].} \tag{5.11}
$$

The argument also explains why a character comparison alone was insufficient: it excludes odd and higher $2$-power intersections, but the mod-$2$ characters coincide. The quadratic theorem supplies the missing existence and identifies the point.

### 5.4 Monodromy and the variance ledger

The groups $C$, $\Sigma$, and $\Phi_p$ are connected by specialization and polarization, but they are not interchangeable. The monodromy sequence (5.4) compares the character lattice with components. The principal polarization compares the multiplicative Shimura line with a constant quotient. Formula (5.6) compares the rational cusp with the component generator.

The Hecke actions are

$$
T_q=q+1\quad(q\ne p),\qquad
U_p=1
$$

on $C$ and $\Phi_p$. On $X_p$, the actions are the Brandt correspondence $B_q$ and $\sigma$, respectively. The monodromy map is Hecke equivariant because $B_q$ is self-adjoint for (5.3), while $\sigma$ preserves the automorphism weights and the degree-zero condition.

The precise comparison to be used at an odd Eisenstein prime is

$$
0\longrightarrow X_{p,\ell}^\vee(1)
\longrightarrow T_\ell J
\longrightarrow X_{p,\ell}
\longrightarrow0, \tag{5.12}
$$

together with (5.4) tensored with $\mathbf Z_\ell$. Here $X_{p,\ell}=X_p\otimes\mathbf Z_\ell$, and the left term means $\operatorname{Hom}(X_p,\mathbf Z_\ell)(1)$. Relative homology does not enter either sequence.

## 6. Odd Eisenstein multiplicity one

### 6.1 The maximal ideal and the claimed finite group scheme

Let $\ell$ be an odd prime dividing $n$. Then $\ell<p$, and

$$
\mathfrak m=(\ell,I)
$$

is a maximal ideal of $\mathbb T$ with residue field $\mathbf F_\ell$. The known finite subgroups supply two lines:

$$
C[\ell]\simeq\mathbf Z/\ell\mathbf Z,\qquad
\Sigma[\ell]\simeq\mu_\ell. \tag{6.1}
$$

They are disjoint by (5.11). The difficult assertion is that there are no additional copies or extensions hidden in $J[\mathfrak m]$. A trace calculation determines only the semisimplification; it cannot prove this multiplicity statement.

### 6.2 The Mazur--Raynaud infrastructure theorem

We state the deep theorem in the exact range used here.

**Mazur--Raynaud odd Eisenstein multiplicity-one theorem.** Let $p\ge5$ be prime, let

$$
n=\frac{p-1}{\gcd(p-1,12)},\qquad
\ell\mid n
$$

with $\ell$ odd, and let $\mathfrak m=(\ell,I)$ in the faithful full cuspidal Hecke algebra. Then the finite group scheme over $\mathbf Q$ cut out by $\mathfrak m$ is

$$
\boxed{
J[\mathfrak m]
=C[\ell]\oplus\Sigma[\ell]
\simeq\mathbf Z/\ell\mathbf Z\oplus\mu_\ell.} \tag{6.2}
$$

The isomorphism is compatible with the Weil pairing, the Hecke action, finite-flat closure over $\mathbf Z_\ell$, Raynaud uniformization at $p$, and the constant and multiplicative identifications in (6.1). The theorem includes $\ell=3$. It makes no assertion at $2$.

The proof is established Mazur--Raynaud infrastructure. Its real machinery has four layers. First, the purely toric reduction of $J$ at $p$ gives Raynaud's uniformization (5.12) and identifies its inertia boundary with the monodromy map. Second, because $\ell\ne p$, $J$ has good reduction at $\ell$; the closure of every $\ell$-primary subquotient is finite flat over $\mathbf Z_\ell$. Book 67's odd, unramified, low-weight Raynaud--Fontaine--Laffaille classification gives exactness, unique extension of morphisms, Cartier duality, and the allowed connected--étale extensions. This includes $\ell=3$ because the weight interval $[0,1]$ has length $1\le\ell-2$.

Third, the two possible extension orientations define two distinct global Selmer groups. Their exact calculation is recorded next. Fourth, Mazur's category of admissible group schemes organizes successive constant and multiplicative subquotients. A devissage argument turns every hypothetical extra Jordan--Hölder copy into a new Selmer class. Since the two Selmer calculations leave only the single monodromy class already realized by $J$, no extra copy survives.

This theorem is not being rederived from a few elementary group-scheme observations. Raynaud uniformization, finite-flat classification, the cyclotomic class-group theorem, and admissible-group-scheme devissage are substantive integral results. The consequences in Chapter 7, however, will be proved from (6.2) without using Gorensteinness in advance.

### 6.3 The two Selmer orientations

The Selmer calculation explains why there can be one monodromy extension but no reverse extension. It also fixes the local conditions rather than inferring them from a dimension count.

For the plus orientation, use the coefficient module $\mathbf F_\ell(1)$. Away from $p\ell$ impose the unramified condition. At $\ell$, impose the finite-flat Kummer subgroup

$$
\mathbf Z_\ell^\times/\mathbf Z_\ell^{\times\ell}
\subset
\mathbf Q_\ell^\times/\mathbf Q_\ell^{\times\ell}.
$$

At $p$, allow the one-dimensional valuation direction generated by $p$. These local conditions define $\mathcal L_+$. Global Kummer theory then gives

$$
\boxed{
H^1_{\mathcal L_+}(\mathbf Q,\mathbf F_\ell(1))
=\mathbf F_\ell[p].} \tag{6.3}
$$

Indeed unramifiedness away from $p\ell$ makes all other valuations divisible by $\ell$, finite flatness at $\ell$ removes the $\ell$-valuation, and the odd real condition contributes nothing. The class of $p$ is nonzero because its $p$-adic valuation is one.

For the reverse orientation, use $\mathbf F_\ell(-1)$. Again impose unramifiedness away from $p\ell$ and the finite-flat condition at $\ell$, but impose zero monodromy at $p$, equivalently the unramified subgroup there. These conditions define $\mathcal L_-$. The classical calculation is

$$
\boxed{
H^1_{\mathcal L_-}(\mathbf Q,\mathbf F_\ell(-1))=0.} \tag{6.4}
$$

The two groups in (6.3) and (6.4) are not dual copies of one calculation. Their coefficient twists, their connected--étale orientations at $\ell$, and their monodromy conditions at $p$ differ. Book 31's local duality explains their orthogonality, while Books 32 and 33 assemble the stated local permissions into honest global Selmer structures.

### 6.4 The cyclotomic class-group input, including $\ell=3$

The reverse vanishing is where global class groups enter. Put

$$
K=\mathbf Q(\zeta_\ell),\qquad
\Delta=\operatorname{Gal}(K/\mathbf Q),\qquad
\omega:\Delta\to\mathbf F_\ell^\times.
$$

Restriction identifies a reverse extension with an $\ell$-extension of $K$ in the $\omega^{-1}$ eigenspace. The local conditions in $\mathcal L_-$ make this extension unramified at every finite place, including the primes over $p$ and $\ell$. The unit contribution is removed by the finite-flat local condition and the character. Hence there is an injection

$$
H^1_{\mathcal L_-}(\mathbf Q,\mathbf F_\ell(-1))
\hookrightarrow
\operatorname{Cl}(K)[\ell]^{\omega^{-1}}. \tag{6.5}
$$

The required cyclotomic theorem is

$$
\operatorname{Cl}(\mathbf Q(\zeta_\ell))[\ell]^{\omega^{-1}}=0
\qquad(\ell\ge5). \tag{6.6}
$$

Its proof uses the integral Stickelberger ideal on the $\omega^{-1}$ branch, or equivalently the nonvanishing modulo $\ell$ of the generalized Bernoulli value controlling that branch. Integrality of Stickelberger elements, annihilation of ideal classes by Gauss-sum resolvents, and passage to the idempotent component are all essential. A formal relation obtained by translating a prime above $p$ would be zero when $p\equiv1\pmod\ell$ and supplies no proof.

For $\ell=3$, one argues separately. The cyclotomic field is

$$
\mathbf Q(\zeta_3)=\mathbf Q(\sqrt{-3}),
$$

whose ring of integers is Euclidean for its norm and hence has trivial class group. The root-of-unity Kummer class is not an allowed reverse extension: the finite-flat local condition at $3$ removes it. Thus (6.4) holds at $3$ as well. Notice that $3\mid n$ forces $p\equiv1\pmod9$, which is also the exact wild congruence condition from (3.4).

### 6.5 Admissible-group-scheme devissage

The final infrastructure layer turns the two cohomology calculations into multiplicity one. An admissible object is an $\ell$-primary finite group scheme over $\mathbf Z[1/p]$ whose generic fiber is a Hecke-stable subquotient of $J[\ell^r]$, whose closure at $\ell$ is finite flat of weights $0$ and $1$, and whose local representation at $p$ has the Raynaud monodromy permitted by (5.12). The category is closed under the saturated subobjects, quotients, Cartier duals, and extensions used in the argument.

Eichler--Shimura away from $p\ell$ and Chebotarev show that the only simple constituents in the Eisenstein block are $\mathbf Z/\ell$ and $\mu_\ell$. Raynaud monodromy orders them at $p$, while the finite-flat classification orders them at $\ell$. Choose a shortest admissible filtration containing the known constant and multiplicative lines. An additional adjacent pair would determine either a plus extension independent of $[p]$ or a reverse extension. The quotient of (6.3) by its known monodromy line is zero, and (6.4) is zero. Cartier duality handles the filtration in the opposite direction. Induction on the length leaves exactly the two known factors.

The devissage is where extension classes become a statement about the whole group scheme. It does not assume that every generic extension is finite flat, and it does not infer a subgroup from a semisimplified trace. These are precisely the tasks supplied by Book 67's exact finite-flat category and Mazur's admissibility theorem.

## 7. Tate modules, duality, and the character lattice

### 7.1 From multiplicity one to two generators

We now prove the algebraic consequences of (6.2) in the direction required for a noncircular argument. Put

$$
R=\mathbb T_{\mathfrak m},\qquad
M=(T_\ell J)_{\mathfrak m}.
$$

The principal polarization gives a perfect Weil pairing on the localized Tate module. Every $T_q$ is self-adjoint and $U_p=-w_p$ is self-adjoint, so the pairing is $R$-balanced. Modulo $\ell$, the orthogonal complement of $\mathfrak m J[\ell]$ is $J[\mathfrak m]$. Consequently

$$
(M/\mathfrak mM)^\vee(1)
\simeq J[\mathfrak m](\overline{\mathbf Q}). \tag{7.1}
$$

By (6.2), the right side has dimension two over $\mathbf F_\ell$. Thus

$$
\dim_{\mathbf F_\ell}M/\mathfrak mM=2. \tag{7.2}
$$

This conclusion uses the polarization and multiplicity one. It does not use a self-duality of the ring $R$.

### 7.2 Tate-module freeness

Nakayama's lemma applied to (7.2) gives a surjection

$$
R^2\twoheadrightarrow M. \tag{7.3}
$$

The generic fiber of $R$ is a product of the coefficient fields of the characteristic-zero newform branches passing through $\mathfrak m$. On each such branch, the covariant Tate module of the associated modular factor has dimension two over that coefficient field. Therefore the source and target of (7.3) have the same $\mathbf Z_\ell$-rank.

The kernel of (7.3) has generic rank zero. Since $R$ is a finite torsion-free $\mathbf Z_\ell$-algebra, $R^2$ is $\mathbf Z_\ell$-torsion free; a rank-zero submodule must be zero. Hence

$$
\boxed{T_\ell J_{\mathfrak m}\simeq R^2.} \tag{7.4}
$$

The proof has exactly two inputs beyond finite algebra: residual multiplicity one supplies two generators, and characteristic-zero multiplicity supplies the generic rank. Faithfulness alone would supply neither.

### 7.3 Gorenstein self-duality

The Tate-module result now turns the polarized self-duality of $M$ into a ring-theoretic duality. Let

$$
R^\vee=\operatorname{Hom}_{\mathbf Z_\ell}(R,\mathbf Z_\ell).
$$

The Weil pairing identifies $M$ with its $\mathbf Z_\ell$-dual as an $R$-module, apart from the Galois Tate twist, which does not change the $R$-module structure. Using (7.4) gives

$$
(R^\vee)^2\simeq R^2. \tag{7.5}
$$

Let $\mu_R(N)$ denote the minimum number of generators of a finite $R$-module. Reducing (7.5) modulo the maximal ideal gives

$$
2\mu_R(R^\vee)=2,
$$

so $R^\vee$ is cyclic. Choose a generator to obtain a surjection

$$
R\twoheadrightarrow R^\vee. \tag{7.6}
$$

Both sides have the same $\mathbf Z_\ell$-rank. The kernel is therefore a rank-zero submodule of the torsion-free module $R$, hence zero. Thus

$$
\boxed{R^\vee\simeq R.} \tag{7.7}
$$

The local Hecke algebra is Gorenstein. This deduction came after Tate-module freeness. It was not imported from the augmented crossing and was not used to prove multiplicity one.

### 7.4 Character-lattice freeness

Localize the Raynaud sequence (5.12) at $\mathfrak m$:

$$
0\longrightarrow X_{p,\mathfrak m}^\vee(1)
\longrightarrow M
\longrightarrow X_{p,\mathfrak m}
\longrightarrow0. \tag{7.8}
$$

The finite-level filtration supplied by (6.2) identifies its multiplicative subline with $\Sigma[\ell]$ and its constant quotient with $C[\ell]$. Hence

$$
\dim_{\mathbf F_\ell}
X_{p,\mathfrak m}/\mathfrak mX_{p,\mathfrak m}=1. \tag{7.9}
$$

The Gorenstein isomorphism (7.7) ensures that localization and the required $\mathbf Z_\ell$-dual lattice are identified without replacing the character lattice by an unsaturated dual. Nakayama now gives a surjection

$$
R\twoheadrightarrow X_{p,\mathfrak m}. \tag{7.10}
$$

On every characteristic-zero branch the toric character module is one-dimensional over the coefficient field. Thus (7.10) has generic rank one on both sides. By definition, $X_{p,\mathfrak m}$ is the $\mathfrak m$-primary direct factor of the finite free lattice $X_p\otimes\mathbf Z_\ell$; it is therefore $\mathbf Z_\ell$-torsion free. The kernel is again zero, proving

$$
\boxed{X_{p,\mathfrak m}\simeq R.} \tag{7.11}
$$

The logical sequence is now explicit:

$$
J[\mathfrak m]\text{ multiplicity one}
\Longrightarrow T_\ell J_{\mathfrak m}\simeq R^2
\Longrightarrow R^\vee\simeq R
\Longrightarrow X_{p,\mathfrak m}\simeq R. \tag{7.12}
$$

No arrow points backward.

### 7.5 Why this chapter has no $2$-adic analogue

At $2$, the constant and cyclotomic characters coincide, $\mu_2(\mathbf Q)$ is nontrivial, and the quadratic point (5.9) lies simultaneously in the known constant and multiplicative subgroups. The residual group scheme need not split into two distinguishable character lines. In addition, Book 67's low-ramification theorem assumes $\ell>2$: the weight interval $[0,1]$ is not inside a strict Fontaine--Laffaille full-faithfulness range at $2$, and trace-zero splittings also fail.

We therefore make no assertion that $J[\mathfrak m_2]$ has dimension two, that $T_2J_{\mathfrak m_2}$ is free of rank two over a local Hecke algebra, or that the local algebra is Gorenstein. The two-primary rational fixed line is supplied by a different theorem, stated in the next chapter.

## 8. Rational torsion

### 8.1 The odd rational Eisenstein-support theorem

Multiplicity one can classify rational torsion only after a rational point has been placed in the correct Hecke block. Density-one Frobenius relations do not by themselves recover the operator at the coefficient prime or the operator at the level.

**Odd rational Eisenstein-support theorem.** Let $p\ge5$ be prime, let $\ell$ be odd, and let

$$
0\ne P\in J_0(p)(\mathbf Q)[\ell].
$$

Then $\ell\mid n$ and

$$
\mathfrak mP=0,\qquad \mathfrak m=(\ell,I). \tag{8.1}
$$

Equivalently, every nonzero rational simple subquotient of odd order is supported at the full Eisenstein maximal ideal, including $U_p-1$.

This is established rational-support infrastructure. Its proof has three distinct stages. At a good prime $q\nmid p\ell$, Eichler--Shimura gives

$$
F_q^2-T_qF_q+q=0
$$

on $J[\ell]$. Since $P$ is rational, $F_qP=P$, so

$$
(T_q-q-1)P=0. \tag{8.2}
$$

The integral missing-coefficient theorem then recovers $T_\ell-\ell-1$. Its proof uses the perfect $q$-expansion pairing, Hecke recurrences, Katz's $\Theta$ operator, and the two-cusp filtration theorem through the relevant powers. At $\ell=3$, the weight-two Hasse direction is excluded by its two cusp values. This is not a formal application of Chebotarev.

Finally, the actual semistable correspondence theorem analyzes $U_p$ on the torus and components. A rational specialization is fixed by arithmetic Frobenius; with $U_p=\sigma$ on characters and $U_p=1$ on components, the full point is placed on the $U_p=1$ branch. The possible case $\ell=p$ is eliminated during this comparison, and the exact index then forces $\ell\mid n$. No good-prime polynomial is asserted at $p$.

At $\ell=2$, the good-prime argument omits $T_2$, and Katz filtration has the Hasse-square direction described in Chapter 3. The theorem is intentionally odd. The $T_2$ issue is part of the separate two-primary theorem below.

### 8.2 The prime-level two-primary fixed-line theorem

The rational $2$-torsion calculation is deep integral geometry, not the $\ell=2$ specialization of odd multiplicity one.

**Prime-level two-primary fixed-line theorem.** Let $p\ge5$ be prime. Then

$$
J_0(p)(\mathbf Q)[2]=0
\qquad\text{if }p\not\equiv1\pmod8, \tag{8.3}
$$

while

$$
\boxed{
J_0(p)(\mathbf Q)[2]
=C[2]=\Sigma[2]}
\qquad\text{if }p\equiv1\pmod8. \tag{8.4}
$$

In the second case the common nonzero point is $\sigma_{\chi_p}=(n/2)c$.

This is established two-primary infrastructure. Its proof begins with the finite-flat closure of a rational fixed line in the good Néron model over $\mathbf Z_2$. It then uses the mod-$2$ Deligne--Rapoport Picard geometry, the Cartier operator on dualizing differentials, and both cusp expansions to classify possible constant finite-flat lines. The missing operator $T_2$ is recovered inside that geometry rather than inserted by a density argument. The semistable $p^2$ correspondence supplies the genuine $U_p$ condition. Finally, quadratic Picard descent and the theta-group calculation of Chapter 5 identify the surviving line with the Legendre line.

The proof works with connected--étale closures over $\mathbf Z_2$ and the actual Cartier geometry of the modular stack. It is not an application of Book 67: Raynaud's odd low-ramification full faithfulness and the Fontaine--Laffaille interval used there do not apply at $2$. Nor is the result a claim that the whole local Hecke block has multiplicity one.

### 8.3 Rational points of exact prime order

Let $\ell$ be odd. If $J(\mathbf Q)[\ell]$ is nonzero, the support theorem gives $\ell\mid n$ and places it in $J[\mathfrak m]$. By (6.2),

$$
J[\mathfrak m]
=C[\ell]\oplus\Sigma[\ell].
$$

The rational points of the multiplicative summand vanish for odd $\ell$:

$$
\mu_\ell(\mathbf Q)=1.
$$

Hence

$$
J(\mathbf Q)[\ell]=C[\ell]. \tag{8.5}
$$

If $\ell\nmid n$, the support theorem says that both sides are zero. At $2$, equations (8.3)--(8.4) give the same conclusion. Thus for every prime $\ell$,

$$
\boxed{J(\mathbf Q)[\ell]=C[\ell].} \tag{8.6}
$$

At this point we know only points killed by $\ell$. A separate divisibility argument is needed for higher powers; a splitting of the $\ell$-divisible group has not been proved and will not be assumed.

### 8.4 The specialization and divisibility argument

Fix a prime $\ell$ and write

$$
A=J(\mathbf Q)[\ell^\infty],\qquad
B=C[\ell^\infty].
$$

Mordell--Weil finite generation makes $A/B$ finite. Suppose it is nonzero. Choose a class of order $\ell$ and represent it by $P\in A$. Then

$$
b=\ell P\in B. \tag{8.7}
$$

If $b\in\ell B$, choose $c_1\in B$ with $\ell c_1=b$. Then

$$
P-c_1\in A[\ell]=B[\ell]
$$

by (8.6), so $P\in B$, contrary to the choice of its class.

It remains to consider $b\notin\ell B$. Specialize at $p$ and pass to components. The isomorphism (5.6) identifies $B$ with the $\ell$-primary part of the cyclic group $\Phi_p$. Therefore

$$
\operatorname{sp}_p(b)\notin\ell\Phi_p. \tag{8.8}
$$

But (8.7) gives

$$
\ell\operatorname{sp}_p(P)=\operatorname{sp}_p(b), \tag{8.9}
$$

which is impossible because the right side is not divisible by $\ell$ in $\Phi_p$. Both alternatives are contradictory. Hence $A=B$.

This argument works uniformly at odd primes and at $2$. Its exact inputs are the order-$\ell$ fixed-line equality and the isomorphism $C\simeq\Phi_p$. It does not assume that specialization is injective on all bad-reduction torsion.

### 8.5 The exact torsion theorem and its Hecke action

Applying the preceding argument at every prime gives

$$
\boxed{
J_0(p)(\mathbf Q)_{\mathrm{tors}}
=C
\simeq\mathbf Z/n\mathbf Z.} \tag{8.10}
$$

Only now do we conclude that rational torsion is Eisenstein. Book 140's explicit Hecke calculation on the generator $c$ gives

$$
T_qP=(q+1)P\quad(q\ne p),\qquad
U_pP=P \tag{8.11}
$$

for every rational torsion point $P$. Thus

$$
I\,J(\mathbf Q)_{\mathrm{tors}}=0. \tag{8.12}
$$

The direction is important. We did not first assume that arbitrary rational torsion was killed by $I$ and then use the index theorem to classify it. Prime-order support, odd multiplicity one, the independent two-primary theorem, and component divisibility proved the torsion theorem; the global Eisenstein action follows afterward because the resulting group is the known cusp group.

For $p=2,3,5,7,13$, equation (8.10) is the genus-zero statement $0=0$. Thus the formula holds at every prime level.

## 9. The absolute winding quotient

### 9.1 From a relative path to a rational absolute class

The path from $0$ to $\infty$ is relative, but the quotient of a Jacobian must be cut out in absolute homology. The bridge is period duality.

Fix the path $\lambda$ from $0$ to $i\infty$ and normalize a cusp form $f$ by the differential $2\pi i f(z)\,dz$. Integration defines

$$
\Lambda(f)=2\pi i\int_0^{i\infty}f(z)\,dz=-L(f,1). \tag{9.1}
$$

**Absolute winding comparison theorem.** Poincaré duality for $X(\mathbf C)$ gives a unique plus-class

$$
e\in H_1(X(\mathbf C),\mathbf R)^+
$$

whose period functional is $\Lambda$. This class is rational and satisfies

$$
ne\in H_1(X(\mathbf C),\mathbf Z). \tag{9.2}
$$

For every normalized weight-two newform $f$ of level $p$, with the period normalization fixed above,

$$
\boxed{\langle e,f\rangle=-L(f,1).} \tag{9.3}
$$

The theorem is established absolute-period infrastructure. Its construction begins with the relative path but applies the Poincaré dual of its integration functional. Abel--Jacobi identifies the class of that functional modulo absolute periods with the cusp difference. Since $nc=0$, multiplication by $n$ puts the functional in the integral absolute period lattice, proving (9.2). It does not assert that the relative chain $n\lambda$ has zero boundary.

At positive genus $c\ne0$, so $e\ne0$. If $e$ vanished, every holomorphic differential would integrate to zero along $\lambda$, and Abel--Jacobi would send $c$ to zero.

### 9.2 Construction and newform support

Let

$$
I_{\mathrm w}=\operatorname{Ann}_{\mathbb T}(e).
$$

Over $\mathbf Q$, the Hecke algebra is semisimple and prime level has no old cusp forms. Let

$$
K_{\mathrm w}=I_{\mathrm w}J
$$

be the connected abelian subvariety generated by the images of the endomorphisms in $I_{\mathrm w}$; rationally it is the product of the newform factors on which $e$ has zero projection. Define the optimal quotient

$$
\pi_{\mathrm w}:J\twoheadrightarrow
J^{\mathrm w}=J/K_{\mathrm w}. \tag{9.4}
$$

The kernel is connected by construction. Equivalently, intersect the zero-winding rational homology subspace with the integral homology lattice; that intersection is primitive, and its complex subtorus is $K_{\mathrm w}$. This formulation fixes the integral quotient rather than only its isogeny class.

Equation (9.3) gives the exact support:

$$
J^{\mathrm w}_{\mathbf Q}
\sim
\prod_{L(f,1)\ne0}A_f, \tag{9.5}
$$

with one factor for each Galois orbit of newforms. Since $e\ne0$, this product and the optimal quotient are nonzero at every positive-genus prime level.

### 9.3 The Kolyvagin--Logachev rank-zero theorem

Analytic nonvanishing does not become Mordell--Weil finiteness by a formal comparison. The required arithmetic theorem is the following.

**Kolyvagin--Logachev modular rank-zero theorem.** Let $f$ be a normalized weight-two newform on $\Gamma_0(p)$, let $K_f$ be its coefficient field, and let $A_f$ be the optimal modular abelian variety attached to its Galois orbit. Suppose, for one fixed embedding $K_f\hookrightarrow\mathbf C$,

$$
L(f,1)\ne0.
$$

Then every Galois-conjugate central value is nonzero, the Mordell--Weil rank of $A_f$ is zero, and the relevant Tate--Shafarevich group is finite. In particular,

$$
\boxed{A_f(\mathbf Q)\text{ is finite}.} \tag{9.6}
$$

The statement is compatible with Galois conjugacy of $f$, optimal quotients, isogenies, and coefficient-field decompositions. It is the exact rank-zero input needed for (9.5).

Its proof architecture passes through imaginary quadratic fields. One chooses a field satisfying the Heegner hypothesis and uses a nonvanishing theorem for quadratic twists so that the base-change $L$-function has the required simple-zero behavior. The Gross--Zagier formula identifies the derivative with the Néron--Tate height of a Heegner point. Norm-compatible Heegner points over ring class fields form the Euler system. Kolyvagin's derivative classes and local reciprocity relations then bound the relevant Selmer groups and the Tate--Shafarevich group. Comparing the plus and minus eigenspaces for the quadratic extension forces the original $\mathbf Q$-factor to have rank zero; Mordell--Weil finite generation then makes its rational points finite.

Each stage is essential: twist nonvanishing supplies a usable auxiliary field, Gross--Zagier supplies a nonzero initial class, the Heegner norm relations supply the Euler system, and Kolyvagin descent turns it into a Selmer bound. No abbreviated modular-unit construction replaces that machinery here.

### 9.4 Finiteness of rational points

Every simple factor in (9.5) has finite rational points by (9.6). A finite product of them has finite rational points, and this property is preserved under isogeny. Therefore

$$
\boxed{J^{\mathrm w}(\mathbf Q)\text{ is finite}.} \tag{9.7}
$$

The conclusion concerns the actual optimal quotient (9.4), not merely a rational Hecke subspace. It does not identify its rational torsion as the image of $C$, nor does it claim that every rational torsion point of $J^{\mathrm w}$ lifts to a rational point of $J$. Those stronger assertions would require a separate descent calculation through the connected kernel.

## 10. Integral cotangents and formal immersion

### 10.1 The winding-quotient cotangent theorem

Formal immersion is an integral first-order property. A rational isogeny class of quotients is not enough; one must know the actual Néron cotangent lattice.

**Integral winding-quotient cotangent theorem.** Let $\pi_{\mathrm w}:J\twoheadrightarrow J^{\mathrm w}$ be the optimal quotient (9.4). For every prime $r\ne p$, let $\mathcal J$ and $\mathcal J^{\mathrm w}$ be the Néron models over $\mathbf Z_r$, with identity sections $e_{\mathcal J}$ and $e_{\mathcal J^{\mathrm w}}$. Define

$$
\Omega_{\mathrm w}
=\operatorname{im}\left(
e_{\mathcal J^{\mathrm w}}^*\Omega^1_{\mathcal J^{\mathrm w}/\mathbf Z_r}
\xrightarrow{\ \pi_{\mathrm w}^*\ }
e_{\mathcal J}^*\Omega^1_{\mathcal J/\mathbf Z_r}
\right).
$$

Pullback identifies $\Omega_{\mathrm w}$ with a primitive Hecke-stable sublattice of the integral dualizing cusp forms

$$
S_2(\Gamma_0(p),\mathbf Z_r).
$$

Its rational span is the sum of the newform spaces with $L(f,1)\ne0$. For every $m\ge1$ and $f\in\Omega_{\mathrm w}$,

$$
a_1(T_mf)=a_m(f). \tag{10.1}
$$

If $0\ne\bar f\in\Omega_{\mathrm w}/r\Omega_{\mathrm w}$, some $m$ satisfies

$$
a_m(\bar f)\ne0. \tag{10.2}
$$

The assertions remain valid at $r=2,3$ when the lattice is interpreted on the compactified modular stack and then pulled back from the Néron model.

This is established integral cotangent infrastructure. The connected optimal kernel determines the rational quotient and a primitive quotient of integral singular homology, but that fact alone does not prove saturation of a Néron cotangent lattice at primes dividing a congruence degree. The integral comparison takes the schematic closure of the optimal kernel in the Néron model, compares invariant differentials with relative dualizing forms on the regular modular stack by Grothendieck duality, and uses the perfect Hecke--$q$-expansion pairing plus base change to prove that the pullback lattice is saturated. Hecke stability and the coefficient identity then give (10.1), while the full $q$-expansion principle gives (10.2).

At $2$ and $3$, the proof includes the wild correction: the Hodge bundle is retained on the unrigidified stack, $\omega^2$ is descended with its stabilizer character, and Katz filtration controls forms whose visible coefficients vanish. A naive coarse cotangent lattice could fail to be primitive and would not justify reduction of (10.1).

### 10.2 Producing the formal immersion

Use $\infty$ as base cusp and define

$$
h:X\xrightarrow{\iota_\infty}J
\xrightarrow{\pi_{\mathrm w}}J^{\mathrm w}. \tag{10.3}
$$

Fix a residue characteristic $r\ne p$. Choose a primitive $f\in\Omega_{\mathrm w}$ whose reduction is nonzero. By (10.2), choose $m$ with $a_m(f)$ a unit modulo $r$. The pullback of $f$ by the Hecke translate

$$
h_m=T_m\circ h \tag{10.4}
$$

has expansion

$$
h_m^*f=(T_mf)(q)\frac{dq}{q}
=\bigl(a_1(T_mf)+O(q)\bigr)dq.
$$

Thus its image in the cotangent line at $\infty$ is

$$
a_1(T_mf)\,dq=a_m(f)\,dq. \tag{10.5}
$$

This is nonzero modulo $r$. Since the cotangent space of the curve at the cusp is one-dimensional, the map on cotangents is surjective. Therefore

$$
\boxed{h_m\text{ is a formal immersion at }\infty.} \tag{10.6}
$$

Applying $w_p$ gives the same statement at $0$. The Hecke translate may depend on $r$; no single coefficient is claimed to be a unit in every characteristic.

### 10.3 Odd good-prime cusp-disk rigidity

The formal immersion becomes a rational-point statement after a specialization kernel has been killed. Let $r$ be an odd prime with

$$
r\ne p.
$$

Then $X$, $J$, and $J^{\mathrm w}$ have good reduction at $r$. Suppose

$$
x\in X(\mathbf Q)
$$

reduces to the same point as $\infty$ modulo $r$. The difference

$$
D=h(x)-h(\infty)=h(x)
$$

lies in the finite group $J^{\mathrm w}(\mathbf Q)$ and reduces to zero. At an odd good prime, rational torsion specializes injectively: the prime-to-$r$ part is étale, and the formal group over the unramified field $\mathbf Q_r$ has no rational $r$-power torsion. Hence $D=0$.

It follows that

$$
h_m(x)=h_m(\infty).
$$

Formal immersion at the common reduction point forces the two $\mathbf Z_r$-sections to agree. Therefore

$$
\boxed{
x\equiv\infty\pmod r, r\text{ odd}, r\ne p
\quad\Longrightarrow\quad x=\infty.} \tag{10.7}
$$

The same holds with $0$ in place of $\infty$. This odd good-prime cusp-disk rigidity is the clean interface exported to Book 148.

### 10.4 Why the Jacobian torsion theorem does not settle the quotient at $2$

At $2$, good reduction alone does not give the same torsion-injectivity statement for a rational formal group. More importantly, (8.10) says nothing by itself about the specialization kernel on $J^{\mathrm w}(\mathbf Q)_{\mathrm{tors}}$.

Let

$$
0\longrightarrow K_{\mathrm w}
\longrightarrow J
\longrightarrow J^{\mathrm w}
\longrightarrow0
$$

be the optimal quotient sequence. Rational points yield a connecting map

$$
J^{\mathrm w}(\mathbf Q)
\longrightarrow H^1(\mathbf Q,K_{\mathrm w}). \tag{10.8}
$$

A rational torsion point on the quotient can have a nonzero image in this cohomology set and need not lift to a rational torsion point of $J$. Consequently

$$
J(\mathbf Q)_{\mathrm{tors}}=C
$$

does not determine either $J^{\mathrm w}(\mathbf Q)_{\mathrm{tors}}$ or its kernel of reduction at $2$.

This book supplies no quotient-level $2$-kernel theorem. Book 148 may use (10.7) at an odd good specialization prime. If it wishes to use a $2$-adic cusp disk, it must first prove separately, for this exact optimal quotient, that the relevant rational torsion specialization kernel is zero or identify it completely. The Jacobian torsion theorem cannot be substituted for that missing quotient statement.

## 11. Four diagnostic prime levels

### 11.1 Levels $11$, $17$, and $19$

The first three positive-genus prime levels are elliptic curves, so every scalar can be checked on the unique normalized newform. The data are

$$
\begin{array}{c|c|c|c|c|c}
p&n&T_2&U_p&\Phi_p&C\cap\Sigma\\ \hline
11&5&-2&1&\mathbf Z/5&0\\
17&4&-1&1&\mathbf Z/4&C[2]\\
19&3&0&1&\mathbf Z/3&0.
\end{array} \tag{11.1}
$$

The Eisenstein scalar at $2$ is $3$, so the differences are

$$
-5,\qquad-4,\qquad-3. \tag{11.2}
$$

They recover the exact congruence moduli. The $U_p$ values agree with the boundary branch, the component orders equal $n$, and the intersection is nonzero only at $17\equiv1\pmod8$.

With the period normalization of (9.1), the winding values are

$$
\frac{L(f_{11},1)}{\Omega_{11}^+}=\frac15,\qquad
\frac{L(f_{17},1)}{\Omega_{17}^+}=\frac14,\qquad
\frac{L(f_{19},1)}{\Omega_{19}^+}=\frac13. \tag{11.3}
$$

Thus the winding quotient is the whole elliptic Jacobian in each case. The Kolyvagin--Logachev theorem makes its rational points finite, consistently with the torsion orders $5$, $4$, and $3$.

### 11.2 Level $37$

At level $37$,

$$
n=3,\qquad
\Phi_{37}\simeq\mathbf Z/3,\qquad
C\cap\Sigma=0. \tag{11.4}
$$

There are two rational newform factors. Their verified pairs of scalar data are

$$
(T_2,U_{37})=(-2,-1),\qquad
(T_2,U_{37})=(0,1). \tag{11.5}
$$

Only the second factor supports the full Eisenstein ideal: on the first, the level sign is wrong, while on the second

$$
T_2-3=-3,\qquad U_{37}-1=0. \tag{11.6}
$$

The first factor has vanishing central value and positive rank. The second has

$$
\frac{L(f,1)}{\Omega^+}=\frac13
$$

and is the winding factor. Consequently

$$
J_0(37)^{\mathrm w}
$$

is the optimal rank-zero elliptic quotient, not the whole genus-two Jacobian. The cusp and component generator project to this factor.

### 11.3 What the diagnostics verify

These levels test four independent mechanisms. Level $11$ tests an ordinary odd Eisenstein congruence. Level $17$ tests the extra $2$-adic divided-congruence step and the quadratic point $C[2]=\Sigma[2]$. Level $19$ tests the wild factor at $3$, including the fact that $\ell=3$ remains in odd multiplicity one. Level $37$ tests the distinction among the full Eisenstein support, the winding support, and a positive-rank factor.

No general matrix is inferred from these examples. The displayed data are scalar eigenvalues on one-dimensional newform factors, cyclic component orders, the proven intersection, and the support of the absolute winding class. Their purpose is diagnostic: each would expose a wrong denominator, a reversed $U_p$ variance, or a false claim that the winding quotient is always the whole Jacobian.

## 12. The exported theorem ledger

### 12.1 The prime-level Eisenstein package

For convenient use in the next book, the conclusions are collected in one place. Let $p$ be prime and $n=(p-1)/\gcd(p-1,12)$.

1. For $p=2,3,5,7,13$, $J_0(p)=0$ and every finite statement below is trivial with $n=1$.
2. The faithful full cuspidal algebra with incoming $U_p$ satisfies

   $$
   \mathbb T/I\simeq\mathbf Z/n\mathbf Z.
   $$

3. The four Hecke algebras are the image algebras (2.5)--(2.8),

   $$
   \mathbb T^{\mathrm{rel}}\simeq\mathbb T^{\mathrm{aug}},\qquad
   \mathbb T^{\mathrm{aug}}\simeq
   \mathbb T\times_{\mathbf Z/n\mathbf Z}\mathbf Z.
   $$

4. On cusp and Jacobian realizations $U_p=-w_p$; on the boundary and $\Phi_p$, $U_p=1$; on $X_p$, $U_p=\sigma$.
5. The finite objects and their intersection are

   $$
   C\simeq\mathbf Z/n,\qquad
   \Sigma\simeq\mu_n,\qquad
   \Phi_p\simeq\mathbf Z/n,\qquad
   C\xrightarrow{\sim}\Phi_p,\qquad
   C\cap\Sigma=C[\gcd(n,2)].
   $$

6. For every odd $\ell\mid n$,

   $$
   J[\mathfrak m]\simeq\mathbf Z/\ell\oplus\mu_\ell,\qquad
   T_\ell J_{\mathfrak m}\simeq\mathbb T_{\mathfrak m}^2,\qquad
   \mathbb T_{\mathfrak m}^\vee\simeq\mathbb T_{\mathfrak m},\qquad
   X_{p,\mathfrak m}\simeq\mathbb T_{\mathfrak m}.
   $$

   There is no analogous assertion at $2$.
7. Rational torsion is exactly cuspidal:

   $$
   J_0(p)(\mathbf Q)_{\mathrm{tors}}=C.
   $$

8. At positive genus the nonzero optimal winding quotient is supported exactly on the newform factors with $L(f,1)\ne0$, and its rational points are finite.
9. In every good residue characteristic, a Hecke translate of $X_0(p)\to J^{\mathrm w}$ is a formal immersion at either cusp. If a rational point lies in the same cusp disk at an odd good prime, it is that cusp.

### 12.2 The infrastructure ledger

The deep inputs used in the proof have exact roles.

| Infrastructure | Exact output used here | Construction and proof machinery |
|---|---|---|
| Two-cusp Deligne--Rapoport--Katz theorem | (3.5) implies $nx=0$, with the exponent table (3.4) | unrigidified compactified stack, Hodge bundle, descent of $\omega^2$, relative dualizing sheaf, two cusp expansions, base change, saturation, Katz filtration, and wild divided congruences |
| Perfect Hecke--expansion theorem | $\mathbb T^\vee=S_2(\mathbf Z)$ through $a_1(tf)$ | integral dualizing-form lattice and the full $q$-expansion principle |
| Semistable $U_p$ theorem | $U_p=-w_p$, $1$, and $\sigma$ on the three stated realizations | neat auxiliary level, normalized $p^2$ correspondence, pullback and trace on dualizing sheaves, newness, monodromy, and descent without dividing a degree |
| Quadratic Shimura-character theorem | $\sigma_{\chi_p}=(n/2)c$ | Picard descent, theta groups, Siegel functions, generalized-Bernoulli boundary pairing, and rational multiplier control |
| Mazur--Raynaud odd multiplicity one | $J[\mathfrak m]=\mathbf Z/\ell\oplus\mu_\ell$ | Raynaud uniformization, Book 67 finite-flat classification, the two Selmer orientations, cyclotomic class groups, and admissible-group-scheme devissage |
| Odd rational support theorem | every rational order-$\ell$ point lies at $(\ell,I)$ | Eichler--Shimura, integral missing coefficients, Katz filtration, and the actual semistable $U_p$ action |
| Two-primary fixed-line theorem | (8.3)--(8.4) | finite-flat closure over $\mathbf Z_2$, mod-$2$ Deligne--Rapoport Picard and Cartier geometry, $T_2$, semistable $U_p$, and quadratic descent |
| Absolute winding comparison | rational $e$, integral $ne$, and $\langle e,f\rangle=-L(f,1)$ | Abel--Jacobi periods and Poincaré duality |
| Kolyvagin--Logachev theorem | $L(f,1)\ne0$ implies $A_f(\mathbf Q)$ finite | imaginary quadratic fields, nonvanishing twists, Gross--Zagier, Heegner Euler systems, and Kolyvagin descent |
| Integral cotangent theorem | primitive Néron cotangent lattice, (10.1), and formal immersion | optimal quotients, Néron models, dualizing forms, $q$-expansion, and wild corrections at $2$ and $3$ |

These inputs are stated rather than compressed into counterfeit elementary proofs. Every consequence peculiar to the Eisenstein ideal—index, fiber product, intersection, local freeness, Gorensteinness, higher torsion, winding support, and formal immersion—was proved after the relevant input was fixed.

### 12.3 The dependency audit

The formal dependency graph has direct arrows from Books 91 and 140. Book 91 supplies faithful image algebras, localization, Hecke duality, and the congruence-versus-cotangent discipline; Book 140 supplies the prime-level cusp, Shimura subgroup, component group, monodromy lattice, and incoming variance. The proof architectures expose their earlier foundations rather than silently strengthening them: Book 51 for covariant Tate modules, Books 29--33 for continuous and local--global Galois cohomology, Book 67 for odd finite-flat closure and classification, Book 71 for the numerical inequality, Book 122 for correspondence adjoints, and Books 139--140 for integral modular geometry. No conclusion from Book 148 or any later book enters.

The index theorem does not use rational torsion. Its upper bound is the two-cusp theorem, and its lower bound is only the already known cusp class. The augmented fiber product is derived after the index theorem. Book 71 then gives only the inequality (4.7); no equality of cotangent and congruence lengths is asserted without another theorem.

The cusp--Shimura intersection uses the quadratic theorem for existence and Galois characters for exclusion. It does not identify a deck-eigen function with an invariant downstairs divisor. The odd multiplicity theorem is prior to Tate freeness. Tate freeness is prior to Gorenstein duality. Gorenstein duality is prior to the final saturated character-lattice identification.

The odd support theorem and the two-primary fixed-line theorem precede the prime-order torsion calculation. Prime-order torsion and $C\simeq\Phi_p$ precede the higher-power argument. Only after all of that is $I$ declared to annihilate rational torsion.

The winding quotient is cut out by an absolute Poincaré-dual class. Its finite rational points come from Kolyvagin--Logachev, not from the Jacobian torsion theorem. The formal-immersion argument uses the actual optimal quotient cotangent lattice. Its rational-point consequence is stated at an odd good prime, where quotient torsion specializes injectively.

### 12.4 The exact interface with Book 148

Book 148 may use the following implication without adding an Eisenstein hypothesis. Let $p$ be a positive-genus prime level, let $r$ be an odd prime with $r\ne p$, and let $x\in X_0(p)(\mathbf Q)$. If the integral moduli argument of Book 139 shows that $x$ reduces to $0$ or $\infty$ modulo $r$, then the winding quotient and formal immersion give

$$
x=0\quad\text{or}\quad x=\infty
$$

with the same chosen cusp. The required inputs are exactly the finiteness of $J^{\mathrm w}(\mathbf Q)$, odd good-reduction torsion injectivity on that quotient, and the cotangent theorem.

If the only available cusp disk has residue characteristic $2$, Book 148 must prove a quotient-level specialization-kernel theorem before making the same deduction. It may not infer that theorem from

$$
J_0(p)(\mathbf Q)_{\mathrm{tors}}=C.
$$

The final classification of prime degrees, the treatment of noncuspidal reductions, and the exceptional prime list remain in Book 148.

### 12.5 Conclusion

The Eisenstein ideal measures the integral contact between a free boundary eigensystem and the cuspidal Hecke algebra. At prime level that contact has exact order

$$
\operatorname{num}\left(\frac{p-1}{12}\right),
$$

but no single calculation explains all of its appearances. The two-cusp modular-stack theorem bounds congruences from above. The eta multiplier supplies a cusp of the same exact order. Picard descent produces the multiplicative Shimura subgroup, monodromy produces the component group, and quadratic descent identifies their sole possible common point.

At odd Eisenstein primes, Raynaud uniformization and finite-flat Selmer theory prove genuine multiplicity one. Only then do Nakayama, generic multiplicity, polarization, and the character lattice yield the free Tate module and Gorenstein local algebra. Rational torsion requires one more separation: odd support comes from Eichler--Shimura plus missing coefficients and the real $U_p$ correspondence, while the prime $2$ comes from its own integral fixed-line theorem. Components then lift the order-$\ell$ result through every higher power.

Absolute winding selects a different structure: the factors with nonzero central $L$-value. Kolyvagin--Logachev makes their rational points finite, and the primitive Néron cotangent lattice turns a nonzero Fourier coefficient into a formal immersion. At an odd good prime, a rational point in a cusp disk is therefore the cusp itself. This is the exact algebraic engine passed to the rational-isogeny argument, with its $2$-primary quotient boundary stated rather than hidden.
