# Cuspidal Divisors and Specialization on Modular Jacobians

## Contents

1. [The arithmetic carried by two cusps](#1-the-arithmetic-carried-by-two-cusps)
   - [The question and its three answers](#11-the-question-and-its-three-answers)
   - [Prime-level conventions](#12-prime-level-conventions)
   - [The exact integer](#13-the-exact-integer)
   - [The logical architecture](#14-the-logical-architecture)
2. [The cuspidal divisor and a modular unit](#2-the-cuspidal-divisor-and-a-modular-unit)
   - [Why a function is the first tool](#21-why-a-function-is-the-first-tool)
   - [The minimal eta exponent](#22-the-minimal-eta-exponent)
   - [The divisor calculation](#23-the-divisor-calculation)
   - [What the modular unit proves](#24-what-the-modular-unit-proves)
3. [The level-prime special fiber](#3-the-level-prime-special-fiber)
   - [Two components and supersingular crossings](#31-two-components-and-supersingular-crossings)
   - [Effective automorphisms and edge lengths](#32-effective-automorphisms-and-edge-lengths)
   - [The supersingular mass formula](#33-the-supersingular-mass-formula)
   - [The two exceptional elliptic points](#34-the-two-exceptional-elliptic-points)
4. [The weighted graph calculation](#4-the-weighted-graph-calculation)
   - [The theta graph and its cycle lattice](#41-the-theta-graph-and-its-cycle-lattice)
   - [Order of the discriminant group](#42-order-of-the-discriminant-group)
   - [Cyclicity and the endpoint class](#43-cyclicity-and-the-endpoint-class)
   - [The exact component pairing](#44-the-exact-component-pairing)
5. [Specialization of the cuspidal class](#5-specialization-of-the-cuspidal-class)
   - [Where the two cusps reduce](#51-where-the-two-cusps-reduce)
   - [The specialization formula](#52-the-specialization-formula)
   - [Exact order of the cuspidal divisor](#53-exact-order-of-the-cuspidal-divisor)
   - [Cuspidal and component groups identified](#54-cuspidal-and-component-groups-identified)
6. [Hecke operators on the cuspidal line](#6-hecke-operators-on-the-cuspidal-line)
   - [Good-prime correspondences at the boundary](#61-good-prime-correspondences-at-the-boundary)
   - [Fricke and the level operator](#62-fricke-and-the-level-operator)
   - [The Eisenstein annihilator](#63-the-eisenstein-annihilator)
   - [Hecke equivariance of specialization](#64-hecke-equivariance-of-specialization)
7. [The Eisenstein quotient realized geometrically](#7-the-eisenstein-quotient-realized-geometrically)
   - [The algebraic index recalled](#71-the-algebraic-index-recalled)
   - [The cuspidal module](#72-the-cuspidal-module)
   - [The component module](#73-the-component-module)
   - [Prime-by-prime localization](#74-prime-by-prime-localization)
8. [Monodromy behind the calculation](#8-monodromy-behind-the-calculation)
   - [Characters, cocharacters, and the weighted form](#81-characters-cocharacters-and-the-weighted-form)
   - [The cusp class as a discriminant functional](#82-the-cusp-class-as-a-discriminant-functional)
   - [Hecke adjunction](#83-hecke-adjunction)
   - [What changes under base extension](#84-what-changes-under-base-extension)
9. [The auxiliary multiplicative subgroup](#9-the-auxiliary-multiplicative-subgroup)
   - [Why a second Eisenstein object appears](#91-why-a-second-eisenstein-object-appears)
   - [A descent lemma for a cyclic cover](#92-a-descent-lemma-for-a-cyclic-cover)
   - [The prime-level Shimura kernel](#93-the-prime-level-shimura-kernel)
   - [Its Hecke action and the precise boundary](#94-its-hecke-action-and-the-precise-boundary)
10. [Exceptional levels and exact examples](#10-exceptional-levels-and-exact-examples)
    - [Levels two and three](#101-levels-two-and-three)
    - [The trivial cases five, seven, and thirteen](#102-the-trivial-cases-five-seven-and-thirteen)
    - [Levels eleven, seventeen, and nineteen](#103-levels-eleven-seventeen-and-nineteen)
    - [Levels thirty-seven and seventy-three](#104-levels-thirty-seven-and-seventy-three)
11. [Failure modes and hypothesis ledger](#11-failure-modes-and-hypothesis-ledger)
    - [Stack, stable coarse model, and regular resolution](#111-stack-stable-coarse-model-and-regular-resolution)
    - [Orders, rational points, and subgroup schemes](#112-orders-rational-points-and-subgroup-schemes)
    - [The primes two, three, and the level prime](#113-the-primes-two-three-and-the-level-prime)
    - [Results deliberately not proved](#114-results-deliberately-not-proved)
12. [The prime-level specialization theorem](#12-the-prime-level-specialization-theorem)
    - [The complete statement](#121-the-complete-statement)
    - [Dependency closure](#122-dependency-closure)
    - [Conclusion](#123-conclusion)

## 1. The arithmetic carried by two cusps

### 1.1 The question and its three answers

The compact modular curve $X_0(p)$ has only two cusps. Their difference therefore looks like the smallest possible divisor one could put on a modular curve. Nevertheless, that difference simultaneously detects a modular unit, a bad-reduction component, and the Eisenstein quotient of the Hecke algebra. The purpose of this book is to prove that these are not three numerical coincidences. They are three realizations of one cyclic integral object.

Write the two cusps as $0$ and $\infty$, and put

$$
c=[0]-[\infty]\in J_0(p)(\mathbf Q),
$$

where $J_0(p)=\operatorname{Pic}^0(X_0(p))$. The first question is the exact order of $c$. A modular unit gives a principal multiple of $c$, hence an upper bound. An upper bound is not enough: a smaller multiple might be principal for a less visible reason.

The second question supplies the lower bound. At the level prime, $X_0(p)$ degenerates into two principal components. The cusp $0$ lies on one and $\infty$ on the other. Their difference therefore specializes to the difference of the two component vertices. The denominator of the monodromy pairing on that vertex difference proves its exact order.

The third question asks how Hecke operators act. Away from $p$, a degree-$\ell+1$ correspondence preserves each cusp type, so $T_\ell$ acts by $1+\ell$. The level operator acts by $1$. Thus the same ideal that cuts out the Eisenstein coefficient system annihilates the cuspidal class and its component specialization. The exact index theorem from Book 142 then identifies all three cyclic modules.

This route is deliberately integral. A rational eigenspace cannot see the order of a divisor, the denominator of a component pairing, or the difference between a primitive lattice vector and a multiple of one.

### 1.2 Prime-level conventions

Let $p$ be a prime. For the geometric calculation we first assume $p\geq5$; the levels $2$ and $3$ are handled directly in Chapter 10. The curve $X_0(p)$ is the smooth proper coarse curve over $\mathbf Q$ attached to cyclic subgroups of order $p$. Its two cusps are rational. We use the sign

$$
c=[0]-[\infty]. \tag{1.1}
$$

Changing the sign changes no order statement but reverses displayed specialization generators, so the choice will remain fixed.

Let $\mathbb T$ be the faithful Hecke algebra acting on $J_0(p)$, equivalently on its regular differentials. It is generated by $T_\ell$ for primes $\ell\ne p$ and by the level operator $U_p$. The Eisenstein ideal is

$$
I=(T_\ell-(1+\ell):\ell\ne p)+(U_p-1). \tag{1.2}
$$

Let $\mathcal J/\mathbf Z_p$ be the Néron model of $J_0(p)_{\mathbf Q_p}$ and let

$$
\Phi_p=\mathcal J_{\mathbf F_p}/\mathcal J^0_{\mathbf F_p} \tag{1.3}
$$

be its finite étale component group. When a geometric calculation is intended, we write $\Phi_p(\overline{\mathbf F}_p)$. In the present prime-level calculation every component and the final generator descend to $\mathbf F_p$, but the distinction is retained until descent has been proved.

The specialization homomorphism is

$$
\operatorname{sp}_p:J_0(p)(\mathbf Q_p)
\longrightarrow\Phi_p(\mathbf F_p). \tag{1.4}
$$

It is induced by extending a rational point to a section of the Néron model and reducing that section. Every Hecke endomorphism extends uniquely to $\mathcal J$, so (1.4) is Hecke equivariant.

### 1.3 The exact integer

The integer governing every answer is

$$
n_p=\operatorname{num}\left(\frac{p-1}{12}\right)
=\frac{p-1}{\gcd(p-1,12)}. \tag{1.5}
$$

Put also

$$
d_p=\gcd(p-1,12),
\qquad e_p=\frac{12}{d_p}. \tag{1.6}
$$

Then

$$
\frac{12}{p-1}=\frac{e_p}{n_p} \tag{1.7}
$$

is in lowest terms. This reduced fraction will reappear as the self-pairing of the specialized cusp class. Its denominator immediately gives the order $n_p$.

For every prime $r$,

$$
v_r(n_p)=\max\{0,v_r(p-1)-v_r(12)\}. \tag{1.8}
$$

Thus a factor $4$ is removed at $2$, a factor $3$ at $3$, and no factor is removed at primes at least $5$. These exceptional losses are geometric: they arise from the elliptic automorphisms of the level-one components.

### 1.4 The logical architecture

The proof has two independent halves that meet only after each is exact:

$$
\begin{array}{ccccc}
\text{eta quotient}&\Longrightarrow&n_pc=0
& &\text{upper bound},\\
\text{weighted special fiber}&\Longrightarrow&
\operatorname{ord}(\operatorname{sp}_p(c))=n_p
& &\text{lower bound}.
\end{array}
$$

Since a homomorphism cannot increase order, the second line forces $\operatorname{ord}(c)\geq n_p$, while the first forces $\operatorname{ord}(c)\leq n_p$. Equality follows. Only then do we use the Hecke action and the already established isomorphism $\mathbb T/I\simeq\mathbf Z/n_p\mathbf Z$.

This order prevents circularity. The Eisenstein index is not used to prove the component order. The cusp order is not used to prove the Eisenstein index. The component calculation uses the weighted monodromy theorem of Books 12, 39, and 121, together with a mass calculation proved here.

## 2. The cuspidal divisor and a modular unit

### 2.1 Why a function is the first tool

A divisor class vanishes precisely when its divisor is principal. Because a modular unit has zeros and poles only at cusps, it is the natural device for producing a relation between $0$ and $\infty$. The difficulty is not finding some relation: powers of the discriminant do that immediately. The difficulty is choosing the smallest exponent that descends with trivial character to the coarse curve.

Recall

$$
\eta(z)=q^{1/24}\prod_{m\geq1}(1-q^m),
\qquad q=e^{2\pi iz}.
$$

The eta function has no zero in the upper half-plane. Hence any weight-zero eta quotient, once its multiplier is trivial, is a modular unit.

### 2.2 The minimal eta exponent

Set

$$
k_p=\frac{24}{d_p}. \tag{2.1}
$$

This is the smallest positive even integer $k$ for which $24\mid k(p-1)$. The two requirements must be kept separate. If

$$
g_p=\gcd(p-1,24),
$$

then divisibility alone says $24/g_p\mid k$, while removal of the quadratic eta character requires $2\mid k$. Hence the least admissible exponent is

$$
\operatorname{lcm}\left(2,\frac{24}{g_p}\right).
$$

This equals $24/d_p$. To check the only nontrivial primary part, write $a=v_2(p-1)\geq1$. The combined conditions require

$$
v_2(k)\geq\max\{1,3-a\}
=3-\min\{a,2\}
=v_2(24/d_p).
$$

At $3$ both expressions have valuation $1-\min\{v_3(p-1),1\}$, and no other prime occurs. This also explains, for example, why divisibility at $p=17$ permits $k=3$ but trivial character first occurs at $k=6$.

Define

$$
u_p(z)=\left(\frac{\eta(pz)}{\eta(z)}\right)^{k_p}. \tag{2.2}
$$

**Proposition 2.1.** The function $u_p$ is a rational modular unit on $X_0(p)$.

**Proof strategy.** The eta transformation law has a $24$th-root multiplier and a square-root weight factor. The congruence $24\mid k_p(p-1)$ removes the multiplier on the parabolic generators of $\Gamma_0(p)$, while evenness of $k_p$ removes the residual quadratic character. The quotient has weight zero.

**Proof.** For

$$
\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\operatorname{SL}_2(\mathbf Z),
$$

the eta transformation law has the form

$$
\eta(\gamma z)=\varepsilon(\gamma)(cz+d)^{1/2}\eta(z),
\qquad \varepsilon(\gamma)^{24}=1.
$$

We use the transformation law in its specialized eta-quotient form. For exponents $r_1,r_p$ with $r_1+r_p=0$, the product

$$
f(z)=\eta(z)^{r_1}\eta(pz)^{r_p}
$$

has weight zero. Applying the displayed transformation law to a matrix of $\Gamma_0(p)$ and to the conjugate matrix governing $pz$ shows that its root-of-unity multiplier is trivial provided

$$
r_1+pr_p\equiv0\pmod{24},
\qquad
pr_1+r_p\equiv0\pmod{24}.
$$

The two congruences are the transformations at the two cusps; after they hold, the only remaining multiplier is the quadratic character associated with

$$
p^{r_p}.
$$

This specialized criterion follows directly by collecting the two powers of $cz+d$, which cancel because the weight is zero, and then collecting the two Dedekind multipliers modulo $24$. It is important that both cusp congruences and the residual character are retained.

For $r_1=-k_p$ and $r_p=k_p$, both congruences reduce to

$$
k_p(p-1)\equiv0\pmod{24}.
$$

Moreover $k_p$ is even, so $p^{k_p}$ is a rational square and the quadratic character is trivial. Thus (2.2) is invariant under $\Gamma_0(p)$. Its expansion

$$
u_p(q)=q^{n_p}
\prod_{m\geq1}\left(\frac{1-q^{pm}}{1-q^m}\right)^{k_p}
$$

has rational coefficients, so the invariant function descends to the rational coarse curve.

Eta has no zero on the upper half-plane, so $u_p$ has neither zero nor pole there. Its only possible zeros and poles are at the two cusps. Therefore it is a rational modular unit on the compact coarse curve. $\square$

The minimality in (2.1) is a statement about this eta construction, not yet a proof that no other function yields a smaller cuspidal relation. That missing assertion will come from specialization.

### 2.3 The divisor calculation

At $\infty$, the parameter $q$ has width one and

$$
\frac{\eta(pz)}{\eta(z)}
=q^{(p-1)/24}\prod_{m\geq1}
\frac{1-q^{pm}}{1-q^m}.
$$

The infinite product is a unit in $\mathbf Z[[q]]$. Hence

$$
\operatorname{ord}_{\infty}(u_p)
=\frac{k_p(p-1)}{24}
=\frac{p-1}{d_p}=n_p. \tag{2.3}
$$

The Fricke involution $w_p:z\mapsto-1/(pz)$ exchanges the two cusps. Applying the eta transformation law shows that $u_p\circ w_p$ is a nonzero constant times $u_p^{-1}$. Therefore the order at $0$ is $-n_p$. Since there are no other zeros or poles,

$$
\operatorname{div}(u_p)=n_p([\infty]-[0])=-n_pc. \tag{2.4}
$$

Changing $u_p$ by its inverse would reverse the displayed sign and nothing else.

### 2.4 What the modular unit proves

Equation (2.4) gives

$$
n_pc=0\quad\text{in }J_0(p)(\mathbf Q). \tag{2.5}
$$

Thus the subgroup generated by degree-zero cusp divisors is finite and cyclic of order dividing $n_p$. Because $X_0(p)$ has exactly two geometric cusps and both are rational, there is no larger geometric cuspidal divisor group hidden after base change:

$$
C_p^{\mathrm{cusp}}=\langle c\rangle. \tag{2.6}
$$

One should resist concluding that its order is already known. A principal divisor $mc$ for some proper divisor $m\mid n_p$ need not be an eta quotient. The exactness proof must detect all rational functions, not just the one family we have written. Specialization does exactly that without classifying modular units.

## 3. The level-prime special fiber

### 3.1 Two components and supersingular crossings

The component group of a Jacobian is calculated from a regular curve model, or equivalently from the weighted graph of a stable semistable model. At the prime occurring in the level, the Deligne--Rapoport description makes this graph explicit.

Over $\overline{\mathbf F}_p$, the special fiber has two normalized principal components, denoted $Y_F$ and $Y_V$. Each is the level-one modular curve, hence a projective line. They correspond to the Frobenius and Verschiebung possibilities for a cyclic subgroup of rank $p$. They meet precisely at the supersingular elliptic curves.

On a rigidified fine chart, each meeting is an ordinary node with completed equation

$$
xy=p. \tag{3.1}
$$

Thus the fine geometric dual graph has two vertices and one unit edge for every rigidified supersingular point. Passing to the coarse curve identifies points under their effective automorphisms. The incidence graph remains a two-terminal graph, but an exceptional stabilizer changes the length of its edge.

Both cusps lie in the smooth locus. With our labels, $0$ meets $Y_F$ and $\infty$ meets $Y_V$. Interchanging the labels would reverse every endpoint divisor below but would not alter the graph or its pairing.

### 3.2 Effective automorphisms and edge lengths

Every elliptic curve has the central automorphism $[-1]$, which acts trivially on the unrigidified coarse moduli coordinate. After dividing by this generic stabilizer, a supersingular point has effective automorphism order

$$
e(E)=
\begin{cases}
2,&j(E)=1728,\\
3,&j(E)=0,\\
1,&\text{otherwise}.
\end{cases} \tag{3.2}
$$

For $p\geq5$ these orders are prime to $p$, so the quotient is tame. If a cyclic group of effective order $e$ acts on the fine node by opposite characters on $x$ and $y$, the invariant coarse equation has thickness $e$:

$$
XY=p^e. \tag{3.3}
$$

This is the tame invariant-node calculation recalled in Book 121. Resolving (3.3) replaces the coarse edge by a chain of $e$ unit edges. Consequently the weighted stable graph has one edge of length $e(E)$ for each coarse supersingular class $E$.

It is useful to see why thickness, rather than multiplicity, changes. Work after adjoining the $e$th roots of unity and choose the action

$$
\zeta(x,y)=(\zeta x,\zeta^{-1}y)
$$

on the chart $xy=p$. The invariant monomials of smallest positive degree on the two branches are $X=x^e$ and $Y=y^e$. They satisfy

$$
XY=(xy)^e=p^e.
$$

Mixed invariant monomials are powers of $xy=p$ times powers of $X$ or $Y$, so they add no further generator to the completed invariant ring. Thus the completed coarse ring is

$$
\mathbf Z_p^{\mathrm{nr}}[[X,Y]]/(XY-p^e).
$$

Its special fiber is still reduced: it is $XY=0$. The exponent $e$ measures singularity of the total space and metric length of the node, not multiplicity of either principal component.

The minimal regular resolution can be read from the same equation. It inserts $e-1$ rational curves between the strict transforms of the two branches. The intersection graph is a path of $e$ unit edges. A cycle that uses the coarse edge uses every segment with the same coefficient, so its squared length becomes $e$ times that coefficient squared. This directly verifies that the coarse weight in (3.2) is the coefficient in the monodromy pairing.

There is at most one edge of length $2$ and at most one of length $3$. All remaining edges have length $1$. This small observation will force cyclicity of the discriminant group; arbitrary weighted theta graphs need not have cyclic discriminant.

### 3.3 The supersingular mass formula

The graph order depends not on the number of supersingular classes alone but on their stabilizer-weighted mass. We now prove the exact formula needed later.

**Proposition 3.1 (mass formula).** For $p\geq5$,

$$
\sum_{E\ \mathrm{supersingular}}
\frac1{e(E)}=\frac{p-1}{12}. \tag{3.4}
$$

The sum is over coarse supersingular classes over $\overline{\mathbf F}_p$, and $e(E)$ is the effective order (3.2).

**Proof strategy.** The Hasse invariant is a section of the $(p-1)$st power of the Hodge line. Its zeros are exactly the supersingular points and are simple. The degree of the Hodge line on the rigidified level-one moduli stack is $1/12$. Stack degree counts a coarse point with weight the reciprocal of its effective stabilizer.

**Proof.** Let $\lambda$ be the Hodge line on the compactified level-one moduli stack with the generic central involution rigidified. The discriminant is a section of $\lambda^{12}$ with a simple zero at the cusp and no zero on the smooth locus. Hence

$$
\deg(\lambda)=\frac1{12}. \tag{3.5}
$$

The Hasse invariant $A_p$ is a section of $\lambda^{p-1}$. On the Tate curve its expansion is $1$, so it does not vanish at the cusp. It vanishes precisely when Verschiebung kills the invariant differential, which is precisely the supersingular condition. The deformation space of a supersingular elliptic curve is one-dimensional and the Hasse invariant is a local parameter up to a unit, so each zero has multiplicity one.

Taking degrees of the zero divisor gives

$$
\deg\operatorname{div}(A_p)
=(p-1)\deg\lambda=\frac{p-1}{12}. \tag{3.6}
$$

On the stack, the degree of a geometric point with effective stabilizer of order $e(E)$ is $1/e(E)$. Summing the simple zeros proves (3.4). $\square$

The simplicity assertion can also be checked deformation-theoretically. The completed deformation ring of a supersingular elliptic curve is $W(\overline{\mathbf F}_p)[[t]]$. The connected--étale boundary in the universal $p$-divisible group is cut out to first order by one parameter, and the Hasse invariant measures that parameter. Hence its image in $(t)/(t^2)$ is nonzero. This rules out an unnoticed multiplicity in (3.6).

There is an elementary consistency check. Write $a$ for the number of nonexceptional supersingular classes, and let $\epsilon_2,\epsilon_3\in\{0,1\}$ record whether $j=1728,0$ are supersingular. Then (3.4) reads

$$
a+\frac{\epsilon_2}{2}+\frac{\epsilon_3}{3}
=\frac{p-1}{12}. \tag{3.7}
$$

The congruence criteria of the next section make the right side have exactly the same fractional part as the two exceptional terms. Thus $a$ is an integer, as it must be. This check catches the common factor-of-two error caused by forgetting whether the generic central involution has been rigidified.

The convention is important. If one keeps the generic central involution rather than rigidifying it, every weight is halved and $\deg\lambda=1/24$. Both conventions give the same geometry when used consistently. The coarse edge thickness uses the effective order after the generic involution has been removed, so (3.4) is the convenient form here.

### 3.4 The two exceptional elliptic points

To turn the mass into an integer determinant, we must know exactly when the edges of lengths $2$ and $3$ occur.

**Proposition 3.2.** For $p\geq5$:

1. the class $j=1728$ is supersingular exactly when $p\equiv3\pmod4$;
2. the class $j=0$ is supersingular exactly when $p\equiv2\pmod3$.

**Proof.** In odd characteristic, an elliptic curve $y^2=f(x)$ is ordinary precisely when the coefficient of $x^{p-1}$ in $f(x)^{(p-1)/2}$ is nonzero.

For $j=1728$ take $f=x^3-x=x(x^2-1)$. A term of degree $p-1$ occurs in

$$
x^{(p-1)/2}(x^2-1)^{(p-1)/2}
$$

exactly when $(p-1)/2$ is even, that is, when $p\equiv1\pmod4$. Its binomial coefficient is then nonzero modulo $p$ because all indices lie strictly between $0$ and $p$. Hence the curve is ordinary in that case and supersingular when $p\equiv3\pmod4$.

For $j=0$ take $f=x^3-1$. A term of degree $p-1$ occurs exactly when $p-1$ is divisible by $3$. Again the relevant binomial coefficient is nonzero modulo $p$. Thus the curve is ordinary for $p\equiv1\pmod3$ and supersingular for $p\equiv2\pmod3$. $\square$

Let

$$
E_p^{\mathrm{exc}}=\prod_{E\ \mathrm{supersingular}}e(E). \tag{3.8}
$$

Only exceptional factors affect this product. Proposition 3.2 gives the four cases

$$
\begin{array}{c|c|c}
p\bmod12&\text{exceptional lengths}&E_p^{\mathrm{exc}}\\ \hline
1&\text{none}&1\\
5&3&3\\
7&2&2\\
11&2,3&6.
\end{array} \tag{3.9}
$$

Comparing with $d_p=\gcd(p-1,12)$ yields

$$
E_p^{\mathrm{exc}}=\frac{12}{d_p}=e_p. \tag{3.10}
$$

This identity is the exact place where the denominator $12$ enters the component calculation.

## 4. The weighted graph calculation

### 4.1 The theta graph and its cycle lattice

Let $S$ be the set of coarse supersingular classes and write $e_s=e(E_s)$. The weighted dual graph $G_p$ has vertices $v_F,v_V$ and an edge from $v_F$ to $v_V$ of length $e_s$ for every $s\in S$. Orient all edges from $v_F$ to $v_V$.

The cycle lattice is

$$
X=H_1(G_p,\mathbf Z)
=\left\{(a_s)_{s\in S}\in\mathbf Z^S:
\sum_sa_s=0\right\}. \tag{4.1}
$$

Its monodromy pairing is

$$
q(a,b)=\sum_{s\in S}e_sa_sb_s. \tag{4.2}
$$

Books 12, 39, and 121 identify the geometric component group with the discriminant group

$$
\Phi_p(\overline{\mathbf F}_p)
\simeq X^\vee/qX. \tag{4.3}
$$

This formula already includes the exceptional chains that appear in a regular resolution. Applying an unweighted two-vertex Laplacian directly to the stable coarse graph would discard their lengths and give a false result.

### 4.2 Order of the discriminant group

For edge lengths $e_1,\ldots,e_r$, the weighted spanning-tree formula gives

$$
\#(X^\vee/qX)
=\sum_{i=1}^r\prod_{j\ne i}e_j
=\left(\prod_{j=1}^re_j\right)
\left(\sum_{i=1}^r\frac1{e_i}\right). \tag{4.4}
$$

For completeness, choose the basis $f_i=e_i-e_r$, $1\leq i<r$. The Gram matrix is

$$
Q=\operatorname{diag}(e_1,\ldots,e_{r-1})
+e_r\mathbf1\mathbf1^t. \tag{4.5}
$$

The matrix determinant lemma gives

$$
\det Q=\left(\prod_{i<r}e_i\right)
\left(1+e_r\sum_{i<r}\frac1{e_i}\right),
$$

which is (4.4). When $r=1$, $X=0$ and the empty determinant is $1$; formula (4.4) also gives $1$.

Using (3.4) and (3.10),

$$
\#\Phi_p(\overline{\mathbf F}_p)
=E_p^{\mathrm{exc}}\frac{p-1}{12}
=\frac{12}{d_p}\frac{p-1}{12}
=n_p. \tag{4.6}
$$

Thus the component order is already exact, including its $2$- and $3$-primary parts. Notice that no Eisenstein-index result entered the computation.

### 4.3 Cyclicity and the endpoint class

An order formula alone does not prove cyclicity. We need more: the endpoint divisor

$$
\delta=v_F-v_V \tag{4.7}
$$

must generate.

Resolve every length-$e_i$ edge into a path of $e_i$ unit edges. To determine the order of $\delta$ in the graph Jacobian, solve the vertical-correction equation electrically. Give the two endpoints a potential difference $t$. The current along the $i$th path is $t/e_i$. Kirchhoff's law says that the total current leaving $v_F$ is

$$
m=t\sum_i\frac1{e_i}. \tag{4.8}
$$

The divisor $m\delta$ is an integral Laplacian precisely when every vertex potential can be chosen integral. Along the $i$th path, this requires $t/e_i\in\mathbf Z$ for every $i$, so the least positive possible $t$ is

$$
L=\operatorname{lcm}(e_1,\ldots,e_r). \tag{4.9}
$$

Consequently

$$
\operatorname{ord}(\delta)=L\sum_i\frac1{e_i}. \tag{4.10}
$$

Here all $e_i$ equal $1$, except for at most one $2$ and at most one $3$. They are therefore pairwise coprime after the unit factors are ignored, and

$$
L=\prod_ie_i=E_p^{\mathrm{exc}}. \tag{4.11}
$$

Equations (3.4), (3.10), and (4.10) give

$$
\operatorname{ord}(\delta)=n_p. \tag{4.12}
$$

Since the whole component group has order $n_p$, the endpoint class generates and

$$
\Phi_p(\overline{\mathbf F}_p)
\simeq\mathbf Z/n_p\mathbf Z. \tag{4.13}
$$

This argument also explains why the analogous assertion fails for arbitrary theta graphs. If the path lengths share a common factor, the least common multiple is smaller than their product, the endpoint class has smaller order than the discriminant group, and the latter can be noncyclic.

For readers who prefer an entirely integral matrix argument, the same conclusion follows from Smith normal form. In the basis $f_i=e_i-e_r$, the Gram matrix is (4.5). If there is a unit edge, choose it as the $r$th edge. Subtracting one row from another and then the corresponding columns produces an identity block of size $r-2$; the last invariant factor is the determinant (4.4). Hence the cokernel is cyclic. If there is no unit edge, the only possibilities in the modular calculation are one edge, giving the trivial group, or the two exceptional edges of coprime lengths $2$ and $3$, giving the one-by-one matrix $[5]$. Thus every case is cyclic.

To identify the endpoint class in this presentation, subdivide the paths and delete the vertex $v_V$ from the ordinary Laplacian. The coordinate vector of $\delta$ is the first basis vector at $v_F$. Its order in the cokernel is the least $m$ for which the linear system

$$
\Delta u=m\delta
$$

has an integral solution. Restricting $u$ to a path forces an arithmetic progression, so the drop along the $i$th path is divisible by $e_i$. This recovers exactly the least-common-multiple condition (4.9), now without electrical terminology.

### 4.4 The exact component pairing

The monodromy discriminant group carries a perfect symmetric pairing with values in $\mathbf Q/\mathbf Z$. In the vertex-potential description, the self-pairing of $\delta$ is the effective resistance between the endpoints. Parallel paths of lengths $e_i$ have total conductance $\sum_i1/e_i$, hence resistance

$$
R_p=\left(\sum_i\frac1{e_i}\right)^{-1}
=\frac{12}{p-1}. \tag{4.14}
$$

Therefore

$$
\langle\delta,\delta\rangle_{\Phi}
=\frac{12}{p-1}\pmod{\mathbf Z}
=\frac{e_p}{n_p}\pmod{\mathbf Z}. \tag{4.15}
$$

The last fraction is reduced by (1.6), so its denominator is $n_p$. Perfectness then gives another proof that $\delta$ has exact order $n_p$. Depending on whether the component pairing is defined using the negative intersection matrix or the positive monodromy form, every value in (4.15) may acquire a common minus sign. The order and all adjunction statements are unchanged; throughout this book we use the positive monodromy convention of Book 12.

Let us spell out the discriminant-pairing construction in this example. If $d,d'$ are integral degree-zero vertex divisors, solve

$$
\Delta u=d
$$

over $\mathbf Q$, with $u$ normalized by $u(v_V)=0$. Define

$$
(d,d')=u^td'\pmod{\mathbf Z}.
$$

Adding an integral Laplacian to $d$ changes $u$ by an integral potential, so the value changes by an integer. The same holds in the second variable by symmetry of $\Delta$. If the class of $d$ pairs trivially with every $d'$, then $u$ takes integral values modulo constants; hence $d=\Delta u$ is an integral Laplacian and its component class is zero. This proves nondegeneracy directly.

For $d=d'=\delta$, the normalized solution is constant-slope along every path. If the endpoint potential is $R$, its current on the $i$th path is $R/e_i$. Total current one imposes

$$
R\sum_i\frac1{e_i}=1,
$$

which gives (4.14). This computation simultaneously proves the pairing formula and the endpoint-order formula: the order of a class in a finite group with perfect $\mathbf Q/\mathbf Z$ pairing is the least positive integer clearing all its pairing denominators.

## 5. Specialization of the cuspidal class

### 5.1 Where the two cusps reduce

The graph calculation becomes arithmetic only after a divisor class is placed in it. The two cusps are particularly clean because their closures are disjoint sections through the smooth locus of the Deligne--Rapoport model.

The Tate-curve description distinguishes the sections. At $\infty$, the cyclic subgroup is the multiplicative subgroup in the standard degeneration; at $0$, Fricke duality gives the complementary cusp type. On the special fiber these meet opposite principal components. With the labels fixed in Section 3.1,

$$
\overline{0}\cap\mathscr X_{\mathbf F_p}\subset Y_F,
\qquad
\overline{\infty}\cap\mathscr X_{\mathbf F_p}\subset Y_V. \tag{5.1}
$$

Neither section passes through a supersingular node or an exceptional resolution chain. Thus no residue-degree or intersection-multiplicity correction is hidden in (5.1).

### 5.2 The specialization formula

Book 12 proves that if a degree-zero horizontal divisor $D$ meets the smooth loci of components $Y_v$, its component class is the vertex multidegree

$$
\operatorname{sp}([D])=
[(\overline D\cdot Y_v)_v]. \tag{5.2}
$$

The same formula is identified with the Néron component map in Book 39 and with the integral Albanese specialization on modular curves in Book 121.

Apply (5.2) to $D=0-\infty$. Equations (5.1) give

$$
\operatorname{sp}_p(c)=v_F-v_V=\delta. \tag{5.3}
$$

On a regular resolution, the vector has coefficient $1$ on the two strict transforms and coefficient $0$ on every exceptional component. Its class is nevertheless sensitive to the lengths of the intervening chains because vertical equivalence uses the full intersection matrix. This is exactly what the weighted calculation in Chapter 4 encoded.

One can verify independence from the chosen divisor representative directly. Suppose $D$ is replaced by $D+\operatorname{div}(f)$ on the generic curve. On the regular surface,

$$
\operatorname{div}_{\mathscr X}(f)
=\overline{\operatorname{div}(f)}+\sum_Za_ZZ,
$$

where $Z$ runs through the irreducible components of the special fiber. Intersecting this principal divisor with every component gives zero. Therefore the change in horizontal intersection vector is the negative of the intersection-matrix image of $(a_Z)_Z$. It vanishes in the component cokernel. This is the precise reason (5.2) descends from divisors to the Jacobian.

For the cusp divisor, no moving lemma is necessary: both horizontal sections already meet the smooth locus. If one works first on the thick stable model, its principal components need not be Cartier at an exceptional node. Passing to the regular resolution makes every $Z$ in the displayed divisor decomposition Cartier. Contracting the exceptional chains afterward recovers the same class through the weighted pairing. Thus (5.3) is independent of whether one calculates on the fine chart, stable coarse model, or regular coarse resolution, provided the integral metric is retained.

### 5.3 Exact order of the cuspidal divisor

We can now close the upper--lower-bound argument.

**Theorem 5.1 (exact cuspidal order).** For every prime $p$,

$$
\operatorname{ord}([0]-[\infty])
=n_p=\operatorname{num}\left(\frac{p-1}{12}\right). \tag{5.4}
$$

**Proof.** Suppose first that $p\geq5$. The modular-unit divisor (2.4) proves that the order of $c$ divides $n_p$. The specialization homomorphism sends $c$ to $\delta$ by (5.3), and $\delta$ has order $n_p$ by (4.12). Since the order of the image of an element divides the order of the element,

$$
n_p=\operatorname{ord}(\delta)
\mid\operatorname{ord}(c)\mid n_p.
$$

All three integers are equal.

For $p=2,3$, the curve $X_0(p)$ has genus zero, so its Jacobian and its degree-zero Picard group are zero. Formula (1.5) gives $n_2=n_3=1$. Thus (5.4) holds at the exceptional levels as well. $\square$

This proof establishes more than the existence of torsion. It rules out every smaller principal multiple of the cusp difference, without requiring a classification of all modular units.

### 5.4 Cuspidal and component groups identified

Let

$$
C_p=\langle c\rangle\subseteq J_0(p)(\mathbf Q). \tag{5.5}
$$

Both $C_p$ and $\Phi_p(\overline{\mathbf F}_p)$ are cyclic of order $n_p$, and specialization sends the displayed generator of the first to the displayed generator of the second. Hence:

**Corollary 5.2.** For $p\geq5$, specialization induces an isomorphism

$$
\boxed{
C_p\xrightarrow{\ \sim\ }
\Phi_p(\overline{\mathbf F}_p),
\qquad c\longmapsto\delta.} \tag{5.6}
$$

Both generators are defined over the prime field. Therefore Frobenius fixes $\delta$, the finite étale component group is constant, and (5.6) descends to

$$
C_p\xrightarrow{\sim}\Phi_p(\mathbf F_p). \tag{5.7}
$$

The statement concerns the cuspidal subgroup, not all rational torsion of $J_0(p)$. Proving that every rational torsion point is cuspidal is a substantially stronger theorem and is not a consequence of (5.6).

## 6. Hecke operators on the cuspidal line

### 6.1 Good-prime correspondences at the boundary

The cuspidal subgroup becomes an Eisenstein module because Hecke correspondences have a simple boundary behavior. This simplicity must be proved with multiplicity: set-theoretically seeing one cusp is not enough to recover the degree $\ell+1$.

Let $\ell\ne p$ be prime. The correspondence defining $T_\ell$ classifies a cyclic subgroup of order $\ell$ and has degree $\ell+1$ over either generic leg. On a Tate curve at either cusp type, its $\ell+1$ cyclic subgroups consist of the multiplicative subgroup and the $\ell$ complementary subgroups. After taking the quotient and contracting the generalized elliptic curve, every branch returns to the same cusp type. The multiplicative branch and the complementary branches contribute with their scheme-theoretic degrees, whose sum is $\ell+1$.

Thus, on cusp divisors,

$$
T_\ell[0]=(\ell+1)[0],
\qquad
T_\ell[\infty]=(\ell+1)[\infty]. \tag{6.1}
$$

Subtracting gives

$$
\boxed{T_\ell c=(1+\ell)c\qquad(\ell\ne p).} \tag{6.2}
$$

This agrees with the variance fixed in Book 121: $T_\ell$ is quotient-pushforward after source-pullback. Using the transpose convention would give the same scalar on the cusp line, but keeping the variance fixed is essential for later adjunction.

Here is a local count that makes the multiplicities visible. Over the Tate parameter $q$, the cyclic subgroups of order $\ell$ are

$$
\mu_\ell
\quad\text{and}\quad
\langle\zeta_\ell^a q^{1/\ell}\rangle,
\qquad a=0,\ldots,\ell-1.
$$

The first quotient has Tate parameter $q^\ell$ and the other $\ell$ quotients have parameter $q^{1/\ell}$ after the appropriate base change. In the compactified target they all meet the same cusp. The first branch has ramification index $\ell$ in one degeneracy direction while the remaining branches are permuted transitively in the other; push--pull records their total degree $\ell+1$. At the cusp $0$, apply Fricke to exchange the source and quotient descriptions. This yields the second formula in (6.1) with exactly the same degree.

The argument also handles composite indices prime to $p$. If $m$ is prime to $p$, the Hecke recurrence gives

$$
T_mc=\sigma_1(m)c.
$$

For coprime indices this follows by multiplicativity, and for powers of a prime it follows from

$$
T_{\ell^{a+1}}=T_\ell T_{\ell^a}-\ell T_{\ell^{a-1}}
$$

together with the identical recurrence for $\sigma_1(\ell^a)$. Thus the whole away-from-$p$ Eisenstein character, not merely its prime generators, is visible on the cusp line.

### 6.2 Fricke and the level operator

The Fricke involution exchanges the two cusps, so

$$
w_pc=[\infty]-[0]=-c. \tag{6.3}
$$

At prime level the weight-two cusp space is entirely new because the level-one cusp space is zero. The standard two-degeneracy calculation therefore gives

$$
U_p=-w_p \tag{6.4}
$$

on regular differentials. This relation was established with the same normalization in Book 142. It also holds as an equality of endomorphisms of $J_0(p)$. Indeed, in characteristic zero a homomorphism of abelian varieties whose pullback on invariant differentials is zero has zero-dimensional image and is therefore zero.

Combining (6.3) and (6.4),

$$
\boxed{U_pc=c.} \tag{6.5}
$$

The distinction between $U_p$ and the good-prime operator $T_p$ is indispensable. There is no assertion here that $T_p$ acts by $1+p$ at a prime already in the level.

### 6.3 The Eisenstein annihilator

Equations (6.2) and (6.5) show immediately that

$$
IC_p=0. \tag{6.6}
$$

More explicitly, the action character on the generator is

$$
T_\ell\longmapsto1+\ell,
\qquad U_p\longmapsto1,
\qquad w_p\longmapsto-1
\quad\text{in }\mathbf Z/n_p\mathbf Z. \tag{6.7}
$$

This proves an annihilation statement, not yet that $I$ is the full annihilator. The full statement will follow only after comparing orders with the exact Eisenstein quotient.

### 6.4 Hecke equivariance of specialization

Every Hecke endomorphism of $J_0(p)$ extends uniquely to its Néron model. It preserves the open identity subgroup and therefore induces an endomorphism of $\Phi_p$. For $t\in\mathbb T$ and $x\in J_0(p)(\mathbf Q_p)$,

$$
\operatorname{sp}_p(tx)=t\operatorname{sp}_p(x). \tag{6.8}
$$

Applying (6.8) to $c$ and using that $\delta$ generates gives

$$
T_\ell\delta=(1+\ell)\delta,
\qquad U_p\delta=\delta,
\qquad w_p\delta=-\delta. \tag{6.9}
$$

Thus $I\Phi_p=0$. This calculation also verifies the sign obtained directly from the graph: Fricke exchanges the two vertices and hence negates their difference.

## 7. The Eisenstein quotient realized geometrically

### 7.1 The algebraic index recalled

Book 142 constructs the weight-two prime-level Eisenstein series, proves its exact integral congruence modulus, and establishes

$$
\mathbb T/I\simeq\mathbf Z/n_p\mathbf Z. \tag{7.1}
$$

The algebra is the faithful acting algebra generated by $T_\ell$ for $\ell\ne p$ and $U_p$; the ideal is exactly (1.2). The theorem includes the extra two-primary congruence that a constant-term-only argument misses.

The role of (7.1) here is comparison, not proof of the geometric order. Chapters 2--5 established both the cusp and component orders independently.

### 7.2 The cuspidal module

The action map

$$
\mathbb T\longrightarrow C_p,
\qquad t\longmapsto t(c) \tag{7.2}
$$

is a homomorphism of additive groups and factors through $\mathbb T/I$ by (6.6). It is surjective because the class of $1$ maps to the generator $c$. Both source and target have order $n_p$. Hence:

**Theorem 7.1.** The map (7.2) induces an isomorphism of $\mathbb T$-modules

$$
\boxed{\mathbb T/I\xrightarrow{\sim}C_p,
\qquad 1\longmapsto c.} \tag{7.3}
$$

In particular,

$$
\operatorname{Ann}_{\mathbb T}(C_p)=I. \tag{7.4}
$$

The equality of annihilators follows because the action of $\mathbb T/I$ on its element $1$ is faithful. This is stronger than the eigenvalue formulas alone.

### 7.3 The component module

Compose (7.3) with specialization (5.6). We obtain

$$
\boxed{
\mathbb T/I\xrightarrow{\sim}C_p
\xrightarrow{\sim}\Phi_p(\mathbf F_p),
\qquad1\longmapsto c\longmapsto\delta.} \tag{7.5}
$$

Therefore

$$
\operatorname{Ann}_{\mathbb T}(\Phi_p)=I. \tag{7.6}
$$

Equation (7.5) is the precise form of “cuspidal specialization is Eisenstein.” It includes the group order, a canonical generator once the cusp sign is fixed, the Hecke action, and descent to the ground residue field.

### 7.4 Prime-by-prime localization

Let $r$ be a prime. Taking $r$-primary parts in (7.5) gives

$$
C_p[r^\infty]
\simeq\Phi_p[r^\infty]
\simeq\mathbf Z/r^{v_r(n_p)}\mathbf Z. \tag{7.7}
$$

It is nonzero precisely when $r\mid n_p$. Since $n_p\mid p-1$, one always has $r\ne p$. Thus all cuspidal torsion used here is prime to the residue characteristic at the level prime, and the injectivity of reduction on unramified prime-to-$p$ torsion from Book 39 is compatible with the explicit isomorphism.

At an Eisenstein maximal ideal $\mathfrak m_r=(r,I)$,

$$
(\mathbb T/I)_{\mathfrak m_r}
\simeq\mathbf Z_r/r^{v_r(n_p)}\mathbf Z_r \tag{7.8}
$$

acts faithfully on the corresponding local cusp and component groups. No multiplicity-one or Gorenstein assertion is needed for this cyclic module statement.

The valuation formula makes the exceptional primes transparent. For $r\geq5$,

$$
\#C_p[r^\infty]=r^{v_r(p-1)}.
$$

At $r=3$, one factor of $3$ is removed when present, and at $r=2$, two factors of $2$ are removed:

$$
\#C_p[3^\infty]
=3^{\max(0,v_3(p-1)-1)},
\qquad
\#C_p[2^\infty]
=2^{\max(0,v_2(p-1)-2)}. \tag{7.9}
$$

The graph proof sees these losses through the exceptional paths. The Eisenstein-congruence proof of Book 142 sees the same losses through elliptic stabilizers in the integral differential lattice. The agreement is a comparison of two separately established integral phenomena, not a transfer of a valuation count from one side to the other.

## 8. Monodromy behind the calculation

### 8.1 Characters, cocharacters, and the weighted form

The finite component group is the cokernel of a map between two free lattices, not an isolated finite group. Keeping that map explains both the pairing and the functorial Hecke action.

Let $T$ be the torus in the identity component of the special Néron fiber. Since the two normalized components have genus zero, the connected special fiber is purely toric:

$$
\mathcal J^0_{\overline{\mathbf F}_p}=T,
\qquad X^*(T)=X=H_1(G_p,\mathbf Z). \tag{8.1}
$$

The principal polarization gives the monodromy injection

$$
q:X\hookrightarrow X^\vee,
\qquad q(a)(b)=\sum_se_sa_sb_s, \tag{8.2}
$$

and the exact sequence

$$
0\longrightarrow X\xrightarrow{q}X^\vee
\longrightarrow\Phi_p(\overline{\mathbf F}_p)
\longrightarrow0. \tag{8.3}
$$

The toric rank is $|S|-1$. It is generally much larger than the number of generators of the component group, which is one. A cyclic cokernel does not imply a rank-one torus.

Because both normalized components are projective lines, their Jacobians vanish. The normalization genus formula gives

$$
g(X_0(p))=b_1(G_p)=|S|-1. \tag{8.4}
$$

This provides an independent dimension check on (8.1). Each additional supersingular crossing beyond the first creates one graph cycle, hence one toric dimension. Edge thickness changes the integral monodromy form but not the rank, so exceptional automorphisms affect the component order without changing the genus.

### 8.2 The cusp class as a discriminant functional

The endpoint divisor $\delta$ can be represented in the dual cycle lattice by the current functional that sums the flow leaving $v_F$. Solving the potential equation with unit total current gives potential difference

$$
R_p=\frac{12}{p-1}. \tag{8.5}
$$

Evaluation of this rational potential on the endpoint divisor is the discriminant self-pairing (4.15). Because the numerator and denominator in $e_p/n_p$ are coprime, this functional is primitive in $X^\vee/qX$.

This is the integral heart of the specialization proof. Merely knowing that the graph pairing has determinant $n_p$ would show only the group order. The primitive functional identifies the actual cusp specialization as a generator.

### 8.3 Hecke adjunction

Let $t\in\mathbb T$ be represented by a resolved correspondence and $t^t$ by its transpose. Book 121 proves that their maps on graph cycles are adjoint:

$$
q(t_Xa,b)=q(a,t_X^tb). \tag{8.6}
$$

Dualizing and passing to the cokernel gives

$$
\langle tx,y\rangle_\Phi
=\langle x,t^ty\rangle_\Phi. \tag{8.7}
$$

On the one-dimensional cyclic discriminant module generated by $\delta$, both sides can be checked from (6.9). For the standard prime-to-$p$ Hecke operators, transpose equals the operator under the canonical polarization, so multiplication by $1+\ell$ is self-adjoint. Fricke is an involution and multiplication by $-1$ is self-adjoint.

The monodromy formulation remains valuable even though the component module is cyclic: it controls how the same correspondence acts on the higher-rank torus and on tame inertia, data that the quotient alone forgets.

### 8.4 What changes under base extension

Under an unramified extension of $\mathbf Q_p$, the geometric graph and its edge lengths do not change. The finite étale component group base-changes, and in this case its generator was already rational, so the group of rational components remains cyclic of order $n_p$.

Under a ramified extension of index $a$, every node thickness is multiplied by $a$. The cycle lattice remains $X$ while the monodromy map becomes $aq$. Book 12 gives

$$
0\longrightarrow X/aX
\longrightarrow\Phi_{p,a}
\longrightarrow\Phi_p
\longrightarrow0. \tag{8.8}
$$

Its order is $a^{\operatorname{rank}X}n_p$. The surjection in (8.8) is the contraction map coming from the inclusions

$$
aqX\subset qX\subset X^\vee.
$$

It must not be confused with the map on components induced by canonical Néron base change. In the lattice presentations, that map is the injection

$$
i_a:X^\vee/qX\longrightarrow X^\vee/aqX,
\qquad [x]\longmapsto[ax]. \tag{8.9}
$$

Indeed, if $ax\in aqX$, then $x\in qX$, so $i_a$ is injective; its cokernel is $X^\vee/aX^\vee$. Specialization commutes with canonical Néron base change. Consequently the original cusp class specializes after extension to $i_a(\delta)$, and contraction sends this class to $a\delta$, not to $\delta$:

$$
\Phi_{p,a}\longrightarrow\Phi_p,
\qquad i_a(\delta)\longmapsto a\delta. \tag{8.10}
$$

The base-changed cusp class need not generate the enlarged component group. Thus (5.6) is a statement over the unramified level-prime base, not a claim stable under arbitrary ramification.

## 9. The auxiliary multiplicative subgroup

### 9.1 Why a second Eisenstein object appears

The cuspidal subgroup is constant: its generator is rational. Prime-level geometry also produces a subgroup of multiplicative type, often called the Shimura subgroup. Later Eisenstein quotients use the existence, order, and Hecke character of this second subgroup. They do not require a complete theorem about how it intersects the cuspidal subgroup.

We develop exactly that limited package. Let

$$
\pi:X_1(p)\longrightarrow X_0(p) \tag{9.1}
$$

be the map that forgets a generator of the cyclic subgroup. On the generic curve its deck group is

$$
\Delta=(\mathbf Z/p\mathbf Z)^\times/\{\pm1\}, \tag{9.2}
$$

a cyclic group of order $(p-1)/2$. Define

$$
\Sigma_p=\ker\bigl(\pi^*:J_0(p)\longrightarrow J_1(p)\bigr). \tag{9.3}
$$

The kernel is finite because pullback followed by norm is multiplication by $\deg\pi$.

### 9.2 A descent lemma for a cyclic cover

The following elementary lemma isolates the only descent calculation needed.

**Lemma 9.1.** Let $f:Y\to X$ be a finite generically Galois cover of smooth proper geometrically connected curves over a characteristic-zero field, with finite abelian deck group $D$. Let $H\subseteq D$ be generated by the inertia groups of geometric ramification points. Then the geometric kernel of

$$
f^*:J_X\longrightarrow J_Y
$$

is the diagonalizable group whose character group is $D/H$.

**Proof strategy.** A line bundle in the kernel becomes trivial upstairs. A choice of trivialization turns descent into a character of the deck group. At a ramification point the stabilizer must act trivially on the fiber of a bundle pulled back from the coarse quotient, so the character kills inertia. Conversely, a character killing inertia descends the trivial bundle.

**Proof.** Let $L\in\operatorname{Pic}^0(X_{\bar K})$ and choose an isomorphism $f^*L\simeq\mathcal O_Y$. For $d\in D$, compare the chosen trivialization with its pullback under $d$. Since every invertible regular function on the proper connected curve $Y$ is constant, the comparison is multiplication by a scalar $\chi(d)$. The cocycle condition makes $\chi:D\to\bar K^\times$ a character.

If $y$ lies over a ramification point and $d$ fixes $y$, the natural action on the fiber of a pullback line bundle is trivial. Hence $\chi(d)=1$. Thus $\chi$ kills every inertia group and factors through $D/H$.

Conversely, give the trivial line bundle on $Y$ the $D$-linearization defined by a character of $D/H$. We explain why the condition on inertia is exactly what makes descent through a ramification point effective. In completed local coordinates one has a tame quotient

$$
\bar K[[u]]\subset\bar K[[t]],
\qquad u=t^e,
$$

with inertia acting by $t\mapsto\zeta t$. If inertia acts trivially on the chosen basis of the trivial line, that basis is invariant and descends to a free rank-one module over $\bar K[[u]]$; pulling it back recovers the original basis. If the fiber character is nontrivial, every invariant local section acquires a positive power of $t$, and the pullback of the invariant module fails to generate at the ramification point. Thus precisely the characters trivial on inertia give descent data for a line bundle on the coarse quotient. Away from ramification the cover is a torsor and ordinary finite étale descent applies. These local descents agree on the punctured neighborhoods, so finite flat descent produces a line bundle $L_\chi$ on $X$ whose pullback is trivial.

Tensor product corresponds to multiplication of characters. Changing the upstairs trivialization changes all comparisons by the same scalar and hence changes no character. The constructions are inverse, so

$$
\ker(f^*)(\bar K)=\operatorname{Hom}(D/H,\bar K^\times). \tag{9.4}
$$

Finally, $f_*f^*=[\deg f]$ on $J_X$, so the kernel is contained in $J_X[\deg f]$ and is finite. In characteristic zero it is finite étale. The construction is Galois equivariant: Galois acts on a character through its values in roots of unity. Hence the geometric-point identification, with its Galois action, identifies the kernel group scheme with the diagonalizable group having character group $D/H$. $\square$

The lemma does not say that every kernel of pullback is constant. Its Galois action is the cyclotomic action on character values, which is the hallmark of multiplicative type.

### 9.3 The prime-level Shimura kernel

For the cover (9.1), the only nontrivial generic inertia comes from elliptic points. An order-two inertia subgroup occurs exactly when $p\equiv1\pmod4$, because then the order-four automorphism has eigenlines on $E[p]$. An order-three inertia subgroup occurs exactly when $p\equiv1\pmod3$, because then the order-six automorphism has eigenlines. The cusp stabilizers contribute no additional subgroup after the central sign has been divided out.

We justify each clause. At a nonelliptic point, the only automorphisms are the central signs already removed in (9.2), so the deck action is free. At a $j=1728$ point, choose an automorphism $i$ of order four. Modulo the central sign its effective order is two. A cyclic subgroup $C\subset E[p]$ is fixed by $i$ precisely when its line in the two-dimensional $\mathbf F_p$-space $E[p]$ is an eigenspace. The polynomial of $i$ is $X^2+1$, so such an eigenline exists precisely when $-1$ is a square modulo $p$, equivalently $p\equiv1\pmod4$.

At a $j=0$ point, use an automorphism whose effective order is three. Its polynomial on $E[p]$ splits precisely when a primitive cube root of unity lies in $\mathbf F_p$, equivalently $p\equiv1\pmod3$. A fixed eigenline then has inertia of order three. These inertia subgroups lie in the cyclic deck group $\Delta$, so if both occur they generate the unique subgroup of order six.

At a cusp, the Tate description gives the same width for $\Gamma_1(p)$ and $\Gamma_0(p)$ after a generator above the fixed cusp type has been chosen. The deck transformations permute the cusps above it rather than fixing a branch parameter nontrivially. Thus the compactified cover has no new deck inertia at the cusps. This is why (9.5) contains only the elliptic factors.

Since $\Delta$ is cyclic, the subgroup $H$ generated by these inertia groups has order

$$
\#H=
\begin{cases}
6,&p\equiv1\pmod{12},\\
2,&p\equiv5\pmod{12},\\
3,&p\equiv7\pmod{12},\\
1,&p\equiv11\pmod{12}.
\end{cases} \tag{9.5}
$$

Equivalently,

$$
\#H=\frac{d_p}{2}. \tag{9.6}
$$

Therefore

$$
\#(\Delta/H)
=\frac{(p-1)/2}{d_p/2}=n_p. \tag{9.7}
$$

Lemma 9.1 proves:

**Theorem 9.2.** For $p\geq5$, $\Sigma_p$ is a diagonalizable cyclic group scheme of order $n_p$. More canonically,

$$
\Sigma_p=D(\Delta/H), \tag{9.8}
$$

and after choosing a generator of the cyclic group $\Delta/H$ one obtains a noncanonical isomorphism

$$
\Sigma_p\simeq\mu_{n_p}. \tag{9.9}
$$

The word “noncanonical” matters: replacing a generator by its $a$th power changes (9.9) by the automorphism $\zeta\mapsto\zeta^a$.

### 9.4 Its Hecke action and the precise boundary

Prime-to-$p$ Hecke correspondences lift equivariantly through the generator cover (9.1). The two maps in the lifted correspondence commute with $\Delta$: an $\ell$-isogeny transports the chosen generator of the $p$-subgroup, and multiplication of that generator by $a\in\Delta$ commutes with transport because $\ell\ne p$. Start with the trivial line upstairs carrying descent character $\chi$. Pullback retains $\chi$ on every branch. Norm tensors the fibers over the $\ell+1$ branches, so its descent character is $\chi^{\ell+1}$. Under the additive group law of the kernel, this is multiplication by $1+\ell$. Hence

$$
T_\ell|_{\Sigma_p}=[1+\ell]\qquad(\ell\ne p). \tag{9.10}
$$

Fricke conjugates a diamond deck transformation to its inverse. It therefore sends a descent character $\chi$ to $\chi^{-1}$ and acts as $[-1]$ on $\Sigma_p$. Using $U_p=-w_p$ gives

$$
U_p|_{\Sigma_p}=[1]. \tag{9.11}
$$

Thus

$$
I\Sigma_p=0. \tag{9.12}
$$

This is the auxiliary multiplicative subgroup package used later: multiplicative type, cyclic order $n_p$, and Eisenstein Hecke action. We make no assertion here about the scheme-theoretic intersection $C_p\cap\Sigma_p$, the image of $\Sigma_p$ in the level-prime component group, or a classification of every multiplicative-type subgroup of $J_0(p)$. Those require additional finite-flat and intersection arguments and are deliberately outside the present scope.

## 10. Exceptional levels and exact examples

### 10.1 Levels two and three

The tame quotient-node argument assumed $p\geq5$ because effective stabilizers of orders $2$ and $3$ must be invertible in the residue field. At levels $2$ and $3$, one must not write a coarse equation $XY=p^e$ by tame invariant theory.

No wild calculation is needed for the theorem, however. Both $X_0(2)$ and $X_0(3)$ have genus zero. Hence

$$
J_0(2)=J_0(3)=0,
\qquad C_2=C_3=0,
\qquad\Phi_2=\Phi_3=0. \tag{10.1}
$$

Also $n_2=n_3=1$, so every cyclic order statement is correct. The acting cusp-form Hecke algebra is the zero ring, and the quotient $\mathbb T/I$ is correspondingly trivial.

### 10.2 The trivial cases five, seven, and thirteen

At $p=5$, the only supersingular class is $j=0$, of edge length $3$. A graph with two vertices joined by one path is a tree, so its Jacobian is trivial. The effective resistance is $3$, an integer, and $n_5=1$.

At $p=7$, the only supersingular class is $j=1728$, of edge length $2$. Again the graph is a tree and $n_7=1$.

At $p=13$, there is one ordinary supersingular class, giving one unit edge. Again $n_{13}=1$. These examples are useful because the special fiber is reducible and nodal while the Jacobian component group is trivial. Reducibility alone does not create a graph cycle.

### 10.3 Levels eleven, seventeen, and nineteen

For $p=11$, both exceptional classes are supersingular. The graph has two paths of lengths $2$ and $3$. Its cycle lattice has rank one and Gram matrix $[5]$, so

$$
C_{11}\simeq\Phi_{11}\simeq\mathbf Z/5\mathbf Z,
\qquad
\langle\delta,\delta\rangle=\frac65\equiv\frac15. \tag{10.2}
$$

For $p=17$, the supersingular paths have lengths $1$ and $3$. The Gram matrix is $[4]$:

$$
C_{17}\simeq\Phi_{17}\simeq\mathbf Z/4\mathbf Z,
\qquad
\langle\delta,\delta\rangle=\frac34. \tag{10.3}
$$

This is the geometric appearance of the two-primary correction. A constant-term numerator would suggest only $2$, but the weighted component and cusp orders are $4$.

For $p=19$, the paths have lengths $1$ and $2$. Thus

$$
C_{19}\simeq\Phi_{19}\simeq\mathbf Z/3\mathbf Z,
\qquad
\langle\delta,\delta\rangle=\frac23. \tag{10.4}
$$

In each case the denominator of the reduced resistance is the exact group order.

### 10.4 Levels thirty-seven and seventy-three

At $p=37$, neither exceptional class is supersingular and the mass is $3$. Thus there are three unit paths. The cycle lattice is $A_2$ with Gram matrix

$$
\begin{pmatrix}2&1\\1&2\end{pmatrix},
$$

whose Smith form is $\operatorname{diag}(1,3)$. Hence

$$
C_{37}\simeq\Phi_{37}\simeq\mathbf Z/3\mathbf Z. \tag{10.5}
$$

At $p=73$, the mass is $6$ and again all paths have unit length. The graph has six parallel edges, its cycle lattice is $A_5$, and its discriminant is cyclic of order $6$:

$$
C_{73}\simeq\Phi_{73}\simeq\mathbf Z/6\mathbf Z. \tag{10.6}
$$

The $2$- and $3$-primary pieces are both nonzero and are simultaneously generated by the specialization of $c$. The example shows that the global cyclic group can have more than one Eisenstein maximal ideal.

## 11. Failure modes and hypothesis ledger

### 11.1 Stack, stable coarse model, and regular resolution

Three related models occurred in the proof, and their roles cannot be interchanged without adjustment.

On a rigidified fine chart, every supersingular crossing is a unit node. On the stable coarse model, an effective stabilizer of order $e$ compresses that chart to a node of thickness $e$. On a regular coarse resolution, that node becomes a chain of $e$ unit edges. The weighted cycle pairing on the stable graph equals the unit pairing on the resolved graph.

The mass formula is a stack-degree calculation. The component group is a coarse Jacobian calculation. Effective stabilizer weights are the bridge between them. Counting coarse supersingular points without weights loses the denominator $12$; using stack weights as though they were edge lengths reverses them and is equally wrong.

### 11.2 Orders, rational points, and subgroup schemes

The geometric component group, its rational points, and a finite subgroup scheme of the generic Jacobian are different objects. In this particular calculation the component generator $\delta$ is rational, so the geometric cyclic group descends as a constant group. That conclusion was proved from the cusp sections; it was not inferred merely from the order.

The cuspidal subgroup $C_p$ is constant because its generator lies in $J_0(p)(\mathbf Q)$. The auxiliary group $\Sigma_p$ is of multiplicative type and has cyclotomic geometric points. Even though both have order $n_p$ and the same scalar Hecke eigenvalues, they are not thereby the same subgroup scheme. Equality of orders and annihilators never proves equality or determines intersection.

### 11.3 The primes two, three, and the level prime

There are two distinct exceptional-prime issues.

First, $2$ and $3$ divide automorphism orders. At residue characteristic at least $5$, these automorphisms are tame but still change edge lengths and the exact primary parts of the group. At residue characteristics $2$ and $3$, the invariant-node calculation is wild and was not used; genus zero settled those levels directly.

Second, $p$ is the level prime. The operator there is $U_p$, the modular curve has semistable bad reduction, and the good-prime Eichler--Shimura formula is not substituted for a $U_p$ calculation. Since $n_p\mid p-1$, the cuspidal group has no $p$-primary part. This fact makes prime-to-$p$ specialization available but does not turn the bad fiber into good reduction.

### 11.4 Results deliberately not proved

The following stronger statements are not consequences of the present calculation and are not asserted:

- that all of $J_0(p)(\mathbf Q)_{\mathrm{tors}}$ is cuspidal;
- a complete multiplicity-one theorem at every Eisenstein maximal ideal;
- the full scheme-theoretic intersection of the cuspidal and Shimura subgroups;
- a classification of every finite flat subgroup of an Eisenstein quotient;
- a direct-sum decomposition of torsion into constant and multiplicative parts; or
- invariance of the cusp--component isomorphism under ramified base change.

The selected Eisenstein quotient needs the cyclic cusp module, its exact specialization, and the limited multiplicative subgroup facts of Chapter 9. The omitted statements require the admissible group-scheme and descent theory developed later.

## 12. The prime-level specialization theorem

### 12.1 The complete statement

We now collect the results in a form that can be used without reconstructing the proof.

**Theorem 12.1 (cuspidal divisor, component, and Eisenstein package).** Let $p$ be prime, set

$$
n_p=\operatorname{num}\left(\frac{p-1}{12}\right),
$$

let $c=[0]-[\infty]\in J_0(p)(\mathbf Q)$, and let $I$ be the ideal (1.2) in the faithful prime-level Hecke algebra.

1. The geometric cuspidal divisor group is generated by $c$ and

   $$
   C_p=\langle c\rangle\simeq\mathbf Z/n_p\mathbf Z.
   $$

2. For $p\geq5$, the stable coarse special fiber at $p$ has two principal components and one path of length

   $$
   e(E)\in\{1,2,3\}
   $$

   for each supersingular class, with exceptional lengths $2$ at $j=1728$ and $3$ at $j=0$ when those classes are supersingular.

3. For $p\geq5$, the weighted mass and exceptional product are

   $$
   \sum_E\frac1{e(E)}=\frac{p-1}{12},
   \qquad
   \prod_Ee(E)=\frac{12}{\gcd(p-1,12)}.
   $$

4. For $p\geq5$, the geometric component group is cyclic of order $n_p$. If $\delta$ is the difference of the two principal component vertices, then

   $$
   \Phi_p(\overline{\mathbf F}_p)=\langle\delta\rangle,
   \qquad
   \langle\delta,\delta\rangle_\Phi
   =\frac{12}{p-1}\pmod{\mathbf Z}.
   $$

5. For $p\geq5$, the cusps reduce to opposite principal components and

   $$
   \operatorname{sp}_p(c)=\delta.
   $$

   Consequently specialization is an isomorphism

   $$
   C_p\xrightarrow{\sim}\Phi_p(\mathbf F_p).
   $$

6. The Hecke action is

   $$
   T_\ell c=(1+\ell)c\quad(\ell\ne p),
   \qquad U_pc=c,
   \qquad w_pc=-c,
   $$

   For $p\geq5$, the identical formulas hold for $\delta$.

7. There are canonical $\mathbb T$-module isomorphisms

   $$
   \mathbb T/I\xrightarrow{\sim}C_p
   \xrightarrow{\sim}\Phi_p(\mathbf F_p).
   $$

   For $p\geq5$, fixing the sign of $c$ fixes these isomorphisms by

   $$
   1\longmapsto c\longmapsto\delta.
   $$

8. For $p\geq5$, the auxiliary Shimura kernel

   $$
   \Sigma_p=\ker(J_0(p)\to J_1(p))
   $$

   is diagonalizable cyclic of order $n_p$, is noncanonically isomorphic to $\mu_{n_p}$, and is annihilated by $I$.

9. For $p=2,3$, the Jacobian, cusp group, and component group are trivial and $n_p=1$, so all assertions concerning them remain valid without a tame coarse-node calculation.

**Proof.** The modular unit of Chapter 2 gives the upper bound for item 1. Chapters 3 and 4 prove items 2--4 from the Deligne--Rapoport fiber, Hasse mass, exceptional-point calculation, and weighted graph theorem. Chapter 5 proves the specialization formula, the lower bound, and item 5. Chapter 6 proves item 6. The exact Eisenstein index from Book 142 and the order comparison give item 7 in Chapter 7. Lemma 9.1 and the elliptic inertia calculation prove item 8. Chapter 10 proves item 9. $\square$

### 12.2 Dependency closure

Every imported ingredient has a precise role.

Book 12 supplies the weighted cycle lattice, its monodromy pairing, the discriminant presentation of the component group, specialization of horizontal divisors, subdivision invariance, and adjunction for correspondences. Its hypotheses apply after passing from the tame stable coarse model to a regular semistable resolution.

Book 39 identifies the separated Picard quotient with the Néron model, identifies the graph discriminant with the Néron component group, proves functorial extension of endomorphisms, and supplies the component specialization map. It also distinguishes the canonical ramified base-change injection from the contraction surjection in (8.8)--(8.10). Here the base is the henselian localization of $\mathbf Z_p$, the generic object is an abelian variety, and the curve model is regular after resolution.

Book 121 supplies the modular-Jacobian variance, the two-branch Deligne--Rapoport geometry, the coarse-node thickness rule, the integral Hecke action on the Néron model, Hecke equivariance of specialization, and monodromy adjunction. We use its level-prime statements only for a prime occurring once in cyclic level and retain all exceptional lengths.

Book 142 supplies the eta normalization check, the relation $U_p=-w_p$ at prime level, the definition of the acting Hecke algebra and Eisenstein ideal, and the exact index

$$
\mathbb T/I\simeq\mathbf Z/n_p\mathbf Z.
$$

It explicitly did not use cuspidal divisors or component groups, so importing its index here creates no circularity. The mass formula, the exceptional supersingularity criteria, cyclicity of the weighted discriminant, exact cusp order, and the limited multiplicative subgroup calculation were all proved in the present book.

### 12.3 Conclusion

The difference of the two prime-level cusps is a remarkably efficient integral probe. Its modular-unit multiple records the smallest eta exponent that descends with trivial character. Its specialization records the potential difference between the two components of the bad fiber. Its Hecke orbit records the Eisenstein character.

The geometry explains the denominator exactly. Supersingular points contribute conductances $1/e(E)$, and their mass is $(p-1)/12$. The exceptional automorphisms contribute the complementary product $12/\gcd(p-1,12)$. Their product is the integer

$$
n_p=\frac{p-1}{\gcd(p-1,12)}.
$$

The effective resistance is the reduced fraction $12/(p-1)$, whose denominator proves that the endpoint difference is primitive. That primitive endpoint is precisely the specialization of $[0]-[\infty]$.

Consequently the analytic, geometric, and algebraic objects coincide as Hecke modules:

$$
\boxed{
\mathbb T/I
\simeq
\langle[0]-[\infty]\rangle
\simeq
\Phi_p(\mathbf F_p)
\simeq
\mathbf Z/n_p\mathbf Z.}
$$

Alongside them lies a diagonalizable cyclic subgroup of the same order and Eisenstein character. Its existence supplies the multiplicative constituent needed in later quotient arguments, while its intersection with the constant cuspidal line remains a separate finite-flat question. This separation of proved structure from later descent is what makes the prime-level specialization package both exact and reusable.
