# Jacobians of Modular Curves

## Contents

1. [From a modular curve to its Jacobian](#1-from-a-modular-curve-to-its-jacobian)
2. [Hecke correspondences and variance](#2-hecke-correspondences-and-variance)
3. [Polarization, transpose, and duality](#3-polarization-transpose-and-duality)
4. [The prime-level cuspidal subgroup](#4-the-prime-level-cuspidal-subgroup)
5. [The Shimura kernel](#5-the-shimura-kernel)
6. [Néron models and specialization](#6-néron-models-and-specialization)
7. [Semistable reduction at the level prime](#7-semistable-reduction-at-the-level-prime)
8. [Component maps and the Albanese map](#8-component-maps-and-the-albanese-map)
9. [Hecke-stable subvarieties and quotients](#9-hecke-stable-subvarieties-and-quotients)
10. [The winding quotient and its Eisenstein boundary](#10-the-winding-quotient-and-its-eisenstein-boundary)
11. [Reduction and rational torsion](#11-reduction-and-rational-torsion)
12. [Finite subgroup schemes and Hecke modules](#12-finite-subgroup-schemes-and-hecke-modules)
13. [Rational points on the modular curve](#13-rational-points-on-the-modular-curve)
14. [The prime-level Jacobian package](#14-the-prime-level-jacobian-package)

## 1. From a modular curve to its Jacobian

Fix an integer $N\geq 1$, and let $X=X_0(N)_{\mathbf Q}$ be the smooth proper coarse modular curve. Its Jacobian

$$
J_0(N)=\operatorname{Pic}^0_{X/\mathbf Q}
$$

is an abelian variety of dimension $g(X)$. A point of $X$ describes an elliptic curve with a cyclic subgroup, but $X$ has no natural addition law. The Jacobian supplies one: divisors can be added, correspondences act linearly, and points may be compared after reduction.

There are two logically different reasons for making this passage. The first is geometric. A correspondence does not ordinarily send one point to one point; it sends a point to a divisor with multiplicities. Degree-zero divisor classes are therefore the natural target on which pullback and norm become homomorphisms. The second is arithmetic. A proper curve has a reduction map, but equality of two reductions is only a local coincidence. Their difference in a Jacobian lies in a group, where torsion, divisibility, component maps, and finite quotients can measure that coincidence.

The passage is not lossless. A quotient of the Jacobian can identify distinct points, and a genus-zero curve has zero Jacobian. The point is not to replace the curve by an abelian variety, but to extract exactly the additive information to which Hecke and Néron methods apply.

The two standard cusps $0$ and $\infty$ are rational. Choosing $\infty$ as base point gives the Albanese, or pointed Abel--Jacobi, map

$$
\iota_\infty:X\longrightarrow J_0(N),
\qquad x\longmapsto [x]-[\infty]. \tag{1.1}
$$

For a field extension $K/\mathbf Q$ and $x\in X(K)$, the right side means the degree-zero class of the corresponding $K$-rational divisor. The construction also works for a closed point by taking its divisor and subtracting the same degree at the base cusp.

Over an algebraic closure one may write

$$
J_0(N)(\overline{\mathbf Q})
=\operatorname{Div}^0(X_{\overline{\mathbf Q}})
/\operatorname{Prin}(X_{\overline{\mathbf Q}}). \tag{1.2}
$$

Over a nonclosed field a rational Picard class need not have a rational divisor representative: the obstruction lies in the Brauer group. Formula (1.1) avoids that issue because both $x$ and $\infty$ are actual rational divisors. Likewise, a closed point $z$ of degree $d$ gives the unambiguous class $[z]-d[\infty]$. None of these divisor-class constructions requires the coarse modular point to lift to a modular object over its residue field.

The Abel map is universal among pointed maps from $X$ to abelian varieties. If $A$ is an abelian variety and $f:X\to A$ satisfies $f(\infty)=0$, there is a unique homomorphism $\widetilde f:J_0(N)\to A$ with $f=\widetilde f\circ\iota_\infty$. Consequently every quotient $q:J_0(N)\twoheadrightarrow A$ produces a modular map

$$
X\xrightarrow{\iota_\infty}J_0(N)\xrightarrow{q}A. \tag{1.3}
$$

Here is the mechanism behind universality. Extend a pointed morphism $f:X\to A$ additively to effective divisors of sufficiently large degree. Two effective divisors in one complete linear system are joined by a projective space, and every morphism from a projective space to an abelian variety is constant. The additive map therefore descends to the appropriate Picard component. Translating that component to $\operatorname{Pic}^0$ gives a morphism $J_0(N)\to A$; the theorem of the square makes it a homomorphism. Since the Abel image generates the Jacobian, the factorization is unique.

Changing the base cusp changes only a translation. Put

$$
c_N=[0]-[\infty]\in J_0(N)(\mathbf Q).
$$

Then

$$
\iota_0(x)=[x]-[0]=\iota_\infty(x)-c_N. \tag{1.4}
$$

The homomorphism induced on Jacobians is independent of the base point; the map from the curve is not. This distinction matters after passage to a quotient, because the translating point $q(c_N)$ need not vanish.

If $X$ has genus zero, its Jacobian is zero and (1.1) carries no information. If $X$ has genus one, choosing $\infty$ identifies $X$ with its Jacobian. In higher genus, the Abel map is a closed immersion. Indeed, equality $\iota_\infty(x)=\iota_\infty(y)$ would make $x-y$ principal. A nonconstant function with that divisor has degree one and forces $X\simeq\mathbf P^1$. The differential is injective because the canonical system of a positive-genus smooth curve has no base point; otherwise Riemann--Roch again produces a degree-one function. Properness then upgrades the injective immersion to a closed immersion.

These cases should not be blurred. Geometric injectivity of $X\to J$ does not imply injectivity after a Hecke quotient, and it does not say that reduction on rational points is injective. Those are precisely the two arithmetic questions for which the later constructions are needed.

## 2. Hecke correspondences and variance

Let $q\nmid N$ be prime. The auxiliary modular curve classifying a cyclic $N$-subgroup together with a cyclic $q$-subgroup has two degeneracy maps

$$
X_0(Nq)\mathrel{\substack{\xrightarrow{\ \alpha\ }\\[-2mm]
\xrightarrow[\ \beta\ ]{}}}X_0(N). \tag{2.1}
$$

The map $\alpha$ forgets the $q$-subgroup; the map $\beta$ divides by it and transports the $N$-subgroup. We use the source-to-quotient convention

$$
T_q=\beta_*\alpha^*. \tag{2.2}
$$

Thus a point is pulled back to all cyclic $q$-subgroups and each lift is then sent to the quotient elliptic curve. Formula (2.2) acts on divisors, respects principal divisors, preserves degree, and therefore induces an endomorphism of $J_0(N)$.

The assertion about principal divisors is a norm calculation, not a set-theoretic count. If $g$ is a rational function on $X_0(N)$, then

$$
\beta_*\alpha^*\operatorname{div}(g)
=\operatorname{div}\!\left(
N_{K(X_0(Nq))/K(X_0(N))}(\alpha^*g)
\right). \tag{2.3}
$$

Ramification indices enter pullback and residue degrees enter the norm, so (2.3) retains the multiplicity of every branch. For a geometric point $x$ away from ramification one obtains the transparent divisor formula

$$
T_q([x]-[b])
=\sum_{z\in\alpha^{-1}(x)}[\beta(z)]
-\sum_{z\in\alpha^{-1}(b)}[\beta(z)]. \tag{2.4}
$$

This is the precise Hecke compatibility of the pointed Albanese map. It should not be shortened to $T_q\iota_b(x)=\sum\iota_b(\beta z)$ unless the second sum has first been evaluated: the base cusp contributes a genuine correction divisor.

The same symbol on different realizations is justified by functoriality, but its variance must remain visible. For a finite map $f:Y\to X$:

- pullback of divisor classes gives $f^*:J_X\to J_Y$;
- norm gives $f_*:J_Y\to J_X$;
- the covariant Tate module follows homomorphisms in the same direction;
- pullback on differentials and ordinary cohomology is contravariant.

Accordingly (2.2) acts covariantly on $T_\ell J_0(N)$. Under the standard comparison with curve cohomology, a dual or Tate twist appears according to the chosen cohomological convention. Writing the maps before simplifying prevents an accidental reversal of $T_q$.

At a prime dividing the level, the analogous source-to-quotient correspondence defines $U_q$. The reverse correspondence will be denoted $V_q$ when both are needed. They must not be identified before a level-specific relation has been proved.

An automorphism of the level structure gives a diamond operator $\langle a\rangle$. On $X_0(N)$ diamonds are trivial, but retaining them for a moment records the adjoint formulas correctly. The Atkin--Lehner involution $w_N$ sends a cyclic isogeny to its dual. It is an involution on the coarse curve and hence on the Jacobian.

At a good prime $q\nmid N\ell$, the integral correspondence and the two Tate quotient types give the Eichler--Shimura relation on the covariant Tate module:

$$
F_q^2-T_qF_q+q\langle q\rangle=0, \tag{2.5}
$$

where $F_q$ is arithmetic Frobenius. The convention agrees with the Frobenius endomorphism of the special abelian variety under good-reduction comparison. For $X_0(N)$ the diamond is $1$.

The relation is first an identity on the good special fiber:

$$
T_q=F_q+\langle q\rangle V_q,
\qquad F_qV_q=V_qF_q=[q]. \tag{2.6}
$$

Multiplication by $F_q$ gives (2.5). This derivation explains both the sign and the constant term, and it shows why the polynomial remains an integral annihilating polynomial on every stable finite torsion quotient. It does not by itself say that a selected module has rank two or that the polynomial is its characteristic polynomial. The hypotheses are essential: (2.5) is a good-reduction relation, and it is not a substitute for the geometry at a prime dividing $N$.

## 3. Polarization, transpose, and duality

The theta divisor gives the Jacobian its canonical principal polarization

$$
\lambda:J_0(N)\xrightarrow{\sim}J_0(N)^\vee. \tag{3.1}
$$

For an endomorphism $u$ of the Jacobian, its Rosati adjoint is

$$
u^\dagger=\lambda^{-1}u^\vee\lambda. \tag{3.2}
$$

If a correspondence is written as $\beta_*\alpha^*$, its transpose is $\alpha_*\beta^*$. Compatibility of the Picard and Albanese constructions with the theta polarization gives

$$
(\beta_*\alpha^*)^\dagger=\alpha_*\beta^*. \tag{3.3}
$$

For $q\nmid N$, the transpose correspondence is identified with the original one after the standard dual-isogeny involution. On $J_0(N)$ this yields

$$
T_q^\dagger=T_q. \tag{3.4}
$$

More generally diamonds satisfy

$$
\langle a\rangle^\dagger=\langle a\rangle^{-1}, \tag{3.5}
$$

and an Atkin--Lehner involution is self-adjoint. At a level prime, (3.3), rather than a guessed scalar formula, says that $U_q^\dagger=V_q$.

These identities control both pairings and quotients. On $\ell^r$-torsion over a field of characteristic different from $\ell$, the polarization Weil pairing satisfies

$$
e_{\ell^r}(ux,y)=e_{\ell^r}(x,u^\dagger y). \tag{3.6}
$$

If $B\subset J_0(N)$ is an abelian subvariety, define

$$
B^\perp=\ker\bigl(J_0(N)\xrightarrow{\lambda}J_0(N)^\vee
\longrightarrow B^\vee\bigr)^0. \tag{3.7}
$$

Then $B^\perp$ is complementary to $B$ up to isogeny, while $B\cap B^\perp$ is finite. If $B$ is stable under an algebra of endomorphisms, $B^\perp$ is stable under the adjoint algebra. Thus a Hecke-stable quotient and its dual subvariety involve the same ideal only when that ideal is Rosati stable.

To see the stability assertion, let $uB\subseteq B$. The composite $J\xrightarrow{u}J\xrightarrow{\lambda}J^\vee\to B^\vee$ is, after adjunction, the composite defining $B^\perp$ followed by $u|_B^\vee$. It therefore vanishes on $u^\dagger B^\perp$. Taking identity components gives $u^\dagger B^\perp\subseteq B^\perp$. This short calculation is why transpose conventions cannot be suppressed when passing from a quotient to its dual subvariety.

There are three integral objects here and they need not coincide. The quotient by a connected Hecke-stable subvariety is an abelian variety; the intersection of kernels of an ideal can have a finite component group; and the orthogonal complement is defined by the polarization. They agree only after the hypotheses needed for the corresponding ideal and saturation statements have been checked.

## 4. The prime-level cuspidal subgroup

From now on let $p$ be prime, put

$$
X=X_0(p),\qquad J=J_0(p),\qquad c=[0]-[\infty]. \tag{4.1}
$$

There are exactly two cusps and both are rational, so the rational cuspidal subgroup is simply

$$
C(p)=\langle c\rangle\subset J(\mathbf Q). \tag{4.2}
$$

This statement defines the subgroup; it does not yet determine its order. The first task is to prove torsion without appealing to a later Eisenstein-index theorem or to a component-group cardinality.

The discriminant supplies a useful first relation. The weight-twelve form has expansion

$$
\Delta(\tau)=q\prod_{n\geq1}(1-q^n)^{24}.
$$

The quotient

$$
u_p(\tau)=\frac{\Delta(p\tau)}{\Delta(\tau)} \tag{4.3}
$$

has weight zero. If $\gamma=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\in\Gamma_0(p)$, then $c/p$ is integral and the transformation law for $\Delta$, applied to

$$
\begin{pmatrix}a&bp\\c/p&d\end{pmatrix}\in\operatorname{SL}_2(\mathbf Z),
$$

shows that the factors of $(c\tau+d)^{12}$ cancel. Hence $u_p$ is a rational function on $X_0(p)$. It has no zero or pole away from the cusps, and its $q$-expansion at $\infty$ begins $q^{p-1}$. The involution $w_p$ exchanges the cusps and gives

$$
u_p(w_p\tau)=p^{-12}u_p(\tau)^{-1}.
$$

Therefore

$$
\operatorname{div}(u_p)=(p-1)([\infty]-[0]), \tag{4.4}
$$

so

$$
(p-1)c=0. \tag{4.5}
$$

The factor $p-1$ is not sharp. The eta multiplier removes exactly the part that the discriminant quotient misses. Put

$$
d_p=\gcd(p-1,12),
\qquad
n_p=\frac{p-1}{d_p}
=\operatorname{num}\!\left(\frac{p-1}{12}\right), \tag{4.6}
$$

and, for $p\geq5$, set

$$
k_p=\frac{24}{d_p}. \tag{4.7}
$$

This is the least positive even integer $k$ for which $24$ divides $k(p-1)$. Indeed, if $g=\gcd(24,p-1)$, the divisibility alone requires $24/g\mid k$, so the least even choice is

$$
\operatorname{lcm}\!\left(2,\frac{24}{g}\right).
$$

Because $p-1$ is even, its $3$-adic contribution to this least common multiple is $3/\gcd(3,p-1)$, and its $2$-adic contribution is $2^{3-\min(v_2(p-1),2)}$. These are exactly the primary factors of $24/\gcd(p-1,12)$, proving (4.7) and its minimality.

Recall Dedekind's eta function

$$
\eta(\tau)=q^{1/24}\prod_{m\geq1}(1-q^m).
$$

Consider the weight-zero eta quotient

$$
v_p(\tau)
=\left(\frac{\eta(p\tau)}{\eta(\tau)}\right)^{k_p}. \tag{4.8}
$$

We verify its descent rather than infer it from its expansion. For an eta product $\eta(\tau)^{r_1}\eta(p\tau)^{r_p}$ of total weight zero, the eta transformation law leaves two cusp-multiplier congruences

$$
r_1+pr_p\equiv0\pmod {24},
\qquad
pr_1+r_p\equiv0\pmod {24}, \tag{4.9}
$$

and a residual quadratic character attached to $p^{r_p}$. This criterion follows by applying

$$
\eta\!\left(\frac{a\tau+b}{c\tau+d}\right)
=\varepsilon(a,b,c,d)(c\tau+d)^{1/2}\eta(\tau),
\qquad \varepsilon^{24}=1,
$$

both to $\tau$ and to $p\tau$. The half-weight factors cancel because $r_1+r_p=0$. Collecting the two Dedekind multipliers gives (4.9); after those congruences hold, the multiplier on a matrix with lower-right entry $d_\gamma$ is the Kronecker character

$$
d_\gamma\longmapsto
\left(\frac{p^{r_p}}{d_\gamma}\right).
$$

This specialized eta-quotient criterion follows from the two transformations $\eta(\tau+1)=e^{\pi i/12}\eta(\tau)$ and $\eta(-1/\tau)=(-i\tau)^{1/2}\eta(\tau)$, which generate the displayed Dedekind multiplier formula. For $(r_1,r_p)=(-k_p,k_p)$, both congruences say $24\mid k_p(p-1)$, while $k_p$ even makes $p^{k_p}$ a rational square and hence makes the Kronecker character trivial. Thus (4.8) is invariant under $\Gamma_0(p)$ and defines an algebraic meromorphic function on $X_0(p)_{\mathbf C}$.

Its expansion has rational coefficients. To apply the holomorphic q-expansion principle without concealing the pole, choose $M$ large enough that multiplication by the pullback of $\Delta^M$ clears the poles of both $v_p$ and $1$ at every cusp. The two sections

$$
\Delta^Mv_p,\qquad \Delta^M
$$

then lie in rationally defined powers of the Hodge line, and their quotient is $v_p$. For every $\sigma\in\operatorname{Aut}(\mathbf C/\mathbf Q)$, the sections $\sigma(\Delta^Mv_p)$ and $\Delta^Mv_p$ have the same expansion at the rational cusp $\infty$. Their difference is a holomorphic section with zero expansion, so q-expansion injectivity makes it zero. Since $\Delta^M$ is rational, $\sigma(v_p)=v_p$. Hence $v_p$ lies in the rational function field of the coarse curve; rationality has not been inferred merely from one formal series.

At $\infty$ one has

$$
v_p(q)=q^{k_p(p-1)/24}
\prod_{m\geq1}
\left(\frac{1-q^{pm}}{1-q^m}\right)^{k_p}
=q^{n_p}(1+O(q)). \tag{4.10}
$$

Eta has no zero on the upper half-plane. The Fricke involution exchanges the two eta factors up to a nonzero constant, so $v_p\circ w_p$ is a constant times $v_p^{-1}$. There are only two cusps. Consequently

$$
\operatorname{div}(v_p)
=n_p([\infty]-[0]),
\qquad
n_pc=0. \tag{4.11}
$$

For $p=2,3$, the coarse curves have genus zero and the same conclusion holds because $n_p=1$ and $J_0(p)=0$. Thus for every prime $p$ the cuspidal group is finite cyclic of order dividing $n_p$.

This is the sharp modular-unit upper bound, but it is still only an upper bound. Minimality of the exponent among eta quotients does not prove minimality among all rational functions. Proving that $c$ has exact order $n_p$ requires a lower bound, obtained from an exact weighted component calculation. That exact order and the resulting identification with the component group belong to the later cuspidal-specialization development; neither will be assumed in this book.

The first levels make the distinction concrete:

|  $p$ | $n_p$ | conclusion proved here              |
| ---: | ----: | ----------------------------------- |
|  $5$ |   $1$ | $c=0$                               |
|  $7$ |   $1$ | $c=0$                               |
| $11$ |   $5$ | $\operatorname{ord}(c)$ divides $5$ |
| $13$ |   $1$ | $c=0$                               |
| $17$ |   $4$ | $\operatorname{ord}(c)$ divides $4$ |
| $19$ |   $3$ | $\operatorname{ord}(c)$ divides $3$ |

For the rows with $n_p>1$, the table intentionally does not replace “divides” by “equals.” That replacement is exactly the lower-bound theorem deferred above.

The Hecke action on $C(p)$ can be computed without knowing its order. At a standard cusp, the $q+1$ cyclic subgroups in the source-to-quotient correspondence have two Tate types. Keeping their multiplicities and subtracting the two cusp images gives

$$
T_qc=(q+1)c\qquad(q\ne p). \tag{4.12}
$$

More explicitly, over the Tate chart the $q+1$ subgroup directions are $\mu_q$ and the $q$ groups generated after adjoining $q^{1/q}$ by $\zeta_q^a q^{1/q}$. Quotienting by the first replaces the Tate parameter by its $q$th power; quotienting by the others replaces it by a chosen $q$th root. After compactification every branch returns to the same cusp type. Pullback ramification and norm degree make the total coefficient $q+1$ at both $0$ and $\infty$, proving (4.12) with the variance of (2.2).

The level operator needs a separate argument. On weight-two cusp forms at prime level, the trace to level one is

$$
\operatorname{Tr}_{\Gamma_0(p)}^{\operatorname{SL}_2(\mathbf Z)}(f)
=f+U_pw_pf. \tag{4.13}
$$

Here is the normalization check. For a positive-determinant matrix put

$$
(f|_2\gamma)(z)=\det(\gamma)(cz+d)^{-2}f(\gamma z).
$$

Represent the nonidentity cosets of $\Gamma_0(p)$ in
$\operatorname{SL}_2(\mathbf Z)$ by

$$
\gamma_j=\begin{pmatrix}0&-1\\1&j\end{pmatrix}
\qquad(0\leq j<p),
$$

and set

$$
W_p=\begin{pmatrix}0&-1\\p&0\end{pmatrix},
\qquad
A_j=\begin{pmatrix}1&j\\0&p\end{pmatrix}.
$$

The identity $W_pA_j=p\gamma_j$ and the trivial action of scalar matrices give

$$
\sum_{j=0}^{p-1}f|_2\gamma_j
=\sum_{j=0}^{p-1}(f|_2W_p)|_2A_j
=U_pw_pf.
$$

Indeed, the determinant factor in $|_2A_j$ is $p^{-1}$, so the last sum has $q$-expansion $\sum_na_{pn}q^n$, which is the normalized $U_p$. Adding the identity coset proves (4.13). Since $S_2(\operatorname{SL}_2(\mathbf Z))=0$, it gives $U_p=-w_p$ on regular differentials. An endomorphism of a characteristic-zero abelian variety that pulls every invariant differential back to zero has zero-dimensional connected image and is therefore zero. Hence the same equality holds in $\operatorname{End}(J)$.

The involution exchanges the cusps, so $w_pc=-c$, and therefore

$$
U_pc=c, \tag{4.14}
$$

with

$$
w_pc=-c. \tag{4.15}
$$

Let $\mathbb T$ be the image of the commutative Hecke algebra in $\operatorname{End}(J)$. The boundary relations generate the prime-level Eisenstein ideal

$$
I_{\mathrm{Eis}}=(T_q-(q+1):q\ne p,\ U_p-1)\subset\mathbb T. \tag{4.16}
$$

Equations (4.12) and (4.14) say $I_{\mathrm{Eis}}C(p)=0$. They do not determine $\mathbb T/I_{\mathrm{Eis}}$, nor do they identify the order of $C(p)$ with the index of the ideal. Even if one separately knew that both objects were killed by $n_p$, that common annihilator would not identify them. The exact congruence modulus requires the integral two-cusp weight-two calculation, including separate $2$- and $3$-primary corrections; that calculation begins only in the Eisenstein-series books.

There is nevertheless an existence statement strong enough to make the later quotient construction nonvacuous. Suppose $J\ne0$. Then $X$ has positive genus, so Chapter 1 makes the Abel map injective. The two cusps are distinct, hence $c\ne0$. Let $m_c>1$ be its order and choose a prime $\ell\mid m_c$. The action on the cyclic group $\langle c\rangle$ gives a ring homomorphism

$$
\mathbb T\longrightarrow\operatorname{End}(\langle c\rangle)
\simeq\mathbf Z/m_c\mathbf Z, \tag{4.17}
$$

and (4.12), (4.14) identify its values on the Hecke generators with the Eisenstein character. Reduction modulo $\ell$ is surjective because integers act as scalars. Its kernel is therefore a maximal ideal

$$
\mathfrak m_c\supseteq(\ell,I_{\mathrm{Eis}}). \tag{4.18}
$$

Since $m_c\mid n_p$, one has $\ell\mid n_p$ and in particular $\ell\ne p$. Thus at least one actual Eisenstein maximal ideal exists whenever the prime-level Jacobian is nonzero. What has not been proved is that every prime dividing $n_p$ occurs, that $m_c=n_p$, or that the local congruence depth is $v_\ell(n_p)$. Those are exactly the strengthenings excluded above.

## 5. The Shimura kernel

Let

$$
\pi:X_1(p)\longrightarrow X_0(p)
$$

forget the chosen generator of the cyclic subgroup. On smooth proper curves it induces pullback and norm

$$
\pi^*:J_0(p)\longrightarrow J_1(p),
\qquad
\pi_*:J_1(p)\longrightarrow J_0(p). \tag{5.1}
$$

Their composite is multiplication by the degree $d$ of $\pi$:

$$
\pi_*\pi^*=[d]. \tag{5.2}
$$

The **Shimura kernel** is the scheme-theoretic kernel

$$
\Sigma(p)=\ker(\pi^*:J_0(p)\to J_1(p)). \tag{5.3}
$$

Equation (5.2) shows that it is a finite subgroup scheme killed by $d$. This is stronger and more useful than a statement only about geometric points.

Indeed, the kernel is a closed subgroup of the proper variety $J_0(p)$, and its identity component would be an abelian subvariety killed by $[d]$. Multiplication by $d$ is an isogeny on every positive-dimensional abelian variety, so that identity component is zero. In characteristic zero the remaining finite group scheme is étale, though its character description below is more naturally expressed as a group of multiplicative type.

There is also a descent description. Away from the ramification points, the cover has deck group

$$
D=(\mathbf Z/p\mathbf Z)^\times/\{\pm1\}.
$$

A degree-zero line bundle $L$ whose pullback is trivial acquires descent data on the trivial bundle upstairs. Choose a trivialization $\varphi:\pi^*L\simeq\mathcal O$. For $g\in D$, the ratio between $g^*\varphi$ and $\varphi$ is a global unit on the proper connected curve $X_1(p)$ and hence a scalar. The cocycle rule makes these scalars a character of $D$. Changing $\varphi$ changes no character, and the trivial character descends the chosen trivialization, forcing $L$ itself to be trivial. This proves injectivity.

At a ramification point, its inertia subgroup fixes a point upstairs. Descent of the trivialized fiber forces the corresponding character to be trivial on that inertia group. Thus one obtains, more precisely, an injection

$$
\Sigma(p)\hookrightarrow \operatorname{Diag}(D/H), \tag{5.4}
$$

where $H$ is generated by the inertia groups and $\operatorname{Diag}(M)$ denotes the diagonalizable group with character group $M$. The character construction is a homomorphism on geometric points and commutes with the Galois action. Over a characteristic-zero field, finite group schemes are finite étale, and the fiber functor identifies finite étale group schemes with finite continuous Galois modules. The Galois-equivariant injection just constructed therefore comes from a unique scheme-theoretic monomorphism (5.4). Dually, $\Sigma(p)^\vee$ is a quotient of the constant group $D/H$. Thus $\Sigma(p)$ is of multiplicative type. This argument deliberately gives no assertion that every allowed character occurs; proving equality and calculating the exact order require an additional divisor-descent calculation.

The away-from-$p$ Hecke correspondences lift through $X_1(p)$ and commute with $\pi$. Hence $\Sigma(p)$ is stable under every $T_q$ with $q\ne p$. We do not promote this to a scalar formula for $U_p$, or even to full-Hecke stability, without calculating the level correspondence on the descent characters. Cartier duality reverses arrows and changes an action to its adjoint under the principal polarization. In particular, comparing $\Sigma(p)$ with the constant cuspidal subgroup requires both the Rosati formula and an order calculation; it is not licensed by the vague slogan that the two groups are dual.

The two boundary objects therefore have complementary forms:

$$
C(p)\text{ is generated by a rational point},
\qquad
\Sigma(p)\text{ is of multiplicative type}. \tag{5.5}
$$

Their exact orders, their possible intersection, and the precise Eisenstein character on every constituent are not consequences of the structural construction alone.

The contrast in (5.5) is scheme-theoretic. If $c$ has order $m$, then $1\mapsto c$ embeds the constant group $(\mathbf Z/m\mathbf Z)_{\mathbf Q}$ in $J$. A multiplicative-type group can have the same geometric order while carrying the Cartier-dual Galois character. Equality of orders, even if later established, neither identifies the groups nor determines their intersection inside $J$.

## 6. Néron models and specialization

Let $K$ be a discretely valued field with ring of integers $R$ and residue field $k$. For an abelian variety $A/K$, its Néron model $\mathcal A/R$ is the smooth separated group scheme characterized by the extension property

$$
\operatorname{Hom}_K(Y_K,A)
\simeq\operatorname{Hom}_R(Y,\mathcal A)
$$

for every smooth $R$-scheme $Y$. In particular, every $K$-endomorphism of $A$ extends uniquely to $\mathcal A$. Thus the Hecke action on a modular Jacobian extends without choosing equations for the special fiber.

Uniqueness carries more structure than individual maps. If two generic endomorphisms satisfy a polynomial relation, their extensions satisfy it because both sides are extensions of the same generic homomorphism. Products, dual maps, and a principal polarization extend as well. The established good-level modular-Jacobian theory gives an abelian scheme over $\mathbf Z[1/p]$ with generic fiber $J_0(p)$, and uniqueness identifies it with the Néron model there. Thus $J_0(p)$ has good reduction away from $p$, while the fiber at $p$ is the sole level-prime component calculation in this book. At residue characteristics $2$ and $3$, this is a statement about the Jacobian obtained from the verified stack or rigidified charts and their descent; it is not a claim that every naive unrigidified coarse modular surface is smooth.

The canonical polarization extends to an isomorphism of Néron models. Consequently transpose correspondences remain adjoint on identity components, toric character lattices, and component pairings. This does not mean that the Néron model is proper at $p$; it means that duality survives in the smooth separated model that replaces properness.

Write $\mathcal A_k^0$ for the identity component and

$$
\Phi_A=\mathcal A_k/\mathcal A_k^0 \tag{6.1}
$$

for the finite étale component group. A point $P\in A(K)=\mathcal A(R)$ has a reduction in $\mathcal A_k(k)$ and a component class

$$
\operatorname{sp}_v(P)\in\Phi_A(k). \tag{6.2}
$$

The component map is a homomorphism and is equivariant for every extended endomorphism. It records only the component of a section; a point specializing to the identity component need not be zero.

Over a henselian DVR with finite residue field, smoothness and Hensel lifting make $\mathcal A(R)\to\mathcal A_k(k)$ surjective, and Lang's theorem makes $\mathcal A_k(k)\to\Phi_A(k)$ surjective. Hence

$$
0\longrightarrow\mathcal A^0(R)
\longrightarrow A(K)
\longrightarrow\Phi_A(k)
\longrightarrow0. \tag{6.3}
$$

Over a more general residue field the last arrow need not be onto, so later quotient arguments use the actual image. Even in (6.3), the kernel is the group of sections meeting the identity component, not the formal kernel of reduction to the identity point.

If $X/R$ is a regular semistable model of a smooth curve and $J$ its Jacobian, the identity component of the Néron model is the separated quotient of the relative degree-zero Picard functor. Vertical divisors account for the failure of the naive Picard functor to be separated. The component group is computed from the intersection matrix, or equivalently from the weighted dual graph.

Finite subgroup schemes require a separate caution. If $A$ has good reduction, then $\mathcal A$ is an abelian scheme and $\mathcal A[m]$ is finite flat over $R$. When $m$ is invertible in $R$, it is finite étale; the closure of a generic finite étale subgroup inside this finite ambient group is then finite étale, and specialization preserves its geometric order. When the residue characteristic divides $m$, the ambient torsion remains finite flat but can have connected or multiplicative parts, so geometric points alone can lose information.

At bad reduction the first sentence is false without an extra hypothesis. Even for $m$ invertible, $\mathcal A[m]$ is in general only quasi-finite étale and need not be finite: torsion can escape through the missing boundary of the nonproper Néron model. A schematic closure in $\mathcal A$ must therefore be proved finite and flat in the particular ambient model before one uses its rank or connected--étale sequence. A subgroup may also meet several components. Component specialization and schematic closure answer different questions, and neither construction repairs a failure of finiteness in the other.

At a good prime, $\mathcal A$ is an abelian scheme and $\Phi_A=0$. At a semistable prime there is an exact sequence

$$
0\longrightarrow T\longrightarrow\mathcal A_k^0
\longrightarrow B\longrightarrow0, \tag{6.4}
$$

with $T$ a torus and $B$ an abelian variety. The character lattice of $T$ and its monodromy pairing determine the component group. This is the form needed at the level prime.

Functoriality is exact only at the level of morphisms. A homomorphism $A\to A'$ extends and induces $\Phi_A\to\Phi_{A'}$, but applying component groups to an exact sequence of generic abelian varieties need not produce an exact sequence. Kernels can acquire components and component classes can disappear in a quotient. Later component arguments will therefore use the actual induced map, never an assumed surjection.

## 7. Semistable reduction at the level prime

Assume now $p\geq5$, and make the geometric calculation after strict henselization so that the nodes and their branches are split. Three models must be distinguished. On a rigidified fine chart, the level-$p$ fiber has two normalized components, corresponding to the multiplicative and étale order-$p$ subgroup types, and the completed equation at a supersingular crossing is $xy=p$. The stable coarse model still has the same two principal components, but an effective stabilizer of order $e$ changes the completed equation, after absorbing a unit, to

$$
XY=p^e. \tag{7.1}
$$

For $e>1$ this total space is not regular. Its minimal regular resolution inserts a chain of $e-1$ rational curves, replacing the thick edge by a path of $e$ unit edges. It is this resolved model that is regular semistable. Thus the convenient weighted two-vertex graph belongs to the stable coarse model, while the ordinary subdivided graph belongs to the regular model. They give the same cycle lattice and pairing. Calling the thick model regular would erase exactly the exceptional correction at $j=0$ and $1728$.

Let $S_p$ be the set of geometric supersingular classes and put

$$
X_p=\operatorname{Div}^0(S_p)
=\left\{\sum_{s\in S_p}a_s[s]:\sum_sa_s=0\right\}. \tag{7.2}
$$

Why is this the correct lattice? Orient every weighted edge from the multiplicative component to the étale component. A graph $1$-cycle assigns an integer $a_s$ to each edge, and the boundary at either vertex is $\sum_sa_s$. The cycle condition is therefore exactly the degree-zero condition in (7.2). Subdivision of a length-$e$ edge forces the same coefficient on all $e$ segments, so it changes neither the lattice nor its rank.

The normalization of each principal component is the level-one coarse modular curve, hence $\mathbf P^1$. The normalized components contribute no abelian Jacobian. The generalized-Jacobian exact sequence therefore identifies (7.2) with the character lattice of the entire geometric identity component of the Néron model of $J_0(p)$. In particular, the reduction is purely toric:

$$
\mathcal J_{\overline{\mathbf F}_p}^0\simeq\operatorname{Hom}(X_p,\mathbf G_m). \tag{7.3}
$$

For a supersingular elliptic curve represented by $s$, define

$$
e_s=\#\operatorname{Aut}(E_s)/2.
$$

For $p\geq5$, the possible values are $1,2,3$: the generic value is $1$, while $j=1728$ and $j=0$ can contribute $2$ and $3$. On the resolved graph a coefficient $a_s$ occurs on each of the $e_s$ unit segments, so its contribution to intersection length is $e_sa_sb_s$. The monodromy pairing is therefore

$$
\left\langle\sum_sa_s[s],\sum_sb_s[s]\right\rangle
=\sum_se_sa_sb_s. \tag{7.4}
$$

It induces an injection

$$
X_p\longrightarrow X_p^\vee,
\qquad a\longmapsto\langle a,-\rangle, \tag{7.5}
$$

and the geometric component group is

$$
\Phi_p(\overline{\mathbf F}_p)
\simeq\operatorname{coker}(X_p\to X_p^\vee). \tag{7.6}
$$

Equations (7.1)--(7.6) give the geometric lattice presentation needed in this book. They specify the group by an explicit integral lattice map and are sufficient for functorial component computations. Determining a closed formula for its order, proving cyclicity in every case, identifying a distinguished generator, and recording its full residue-field descent require the exact weighted discriminant calculation; those facts will not be silently imported here.

The same lattice controls inertia, not only components. Fix $\ell\ne p$. Because the normalized principal components have zero Jacobian, the canonical monodromy filtration on $T_\ell J$ has graded pieces

$$
\operatorname{gr}_{-2}T_\ell J
\simeq X_p^\vee\otimes\mathbf Z_\ell(1),
\qquad
\operatorname{gr}_{-1}T_\ell J=0,
\qquad
\operatorname{gr}_{0}T_\ell J
\simeq X_p\otimes\mathbf Z_\ell. \tag{7.7}
$$

The monodromy operator

$$
N:T_\ell J\longrightarrow T_\ell J(-1) \tag{7.8}
$$

kills the lower filtration step, satisfies $N^2=0$, and induces between the outer graded pieces the completed lattice map (7.5). If $t_\ell:I_p\to\mathbf Z_\ell(1)$ is the tame character, then

$$
\sigma(v)=v+t_\ell(\sigma)N(v) \tag{7.9}
$$

for inertia $\sigma$. Thus the component group is the integral cokernel of the same map that measures tame inertia. In particular, knowing only $\Phi_p$ would lose the pairing and would not recover monodromy.

An elementary model illustrates both the calculation and the boundary. If there are $r$ unit edges, then $X_p$ is the root lattice

$$
A_{r-1}=\{(a_1,\ldots,a_r):\sum a_i=0\}
$$

with its ordinary dot product, and its discriminant group is $\mathbf Z/r\mathbf Z$. With edge lengths $e_1,\ldots,e_r$, a basis $[s_i]-[s_r]$ has Gram matrix

$$
G_{ij}=e_i\delta_{ij}+e_r. \tag{7.10}
$$

Thus

$$
\#\Phi_p(\overline{\mathbf F}_p)
=\det G
=\left(\prod_{i=1}^re_i\right)
\left(\sum_{i=1}^r\frac1{e_i}\right). \tag{7.11}
$$

Formula (7.11) is exact once the supersingular list and weights are known. This book does not evaluate the weighted mass in closed form or compute the Smith normal form in all congruence classes. In particular, (7.11) is not being used to infer the exact order of the cusp class.

Away-from-$p$ Hecke correspondences extend through a resolved closure and act on the supersingular module. Their action on $X_p$ preserves (7.4) up to the adjoint relation dictated by polarization, so it descends to (7.6), preserves (7.7), and commutes with $N$. The Atkin--Lehner involution exchanges the two principal components. A scalar formula on the component group must be proved from this graph action; it cannot be inferred merely from the scalar action on one known cusp class. No graph formula for the level correspondence is being smuggled into this statement; its generic endomorphism still extends to the Néron model by Chapter 6.

## 8. Component maps and the Albanese map

Let $\mathcal X/\mathbf Z_p$ be the regular semistable model and let $v_\infty$ be the component met by the cusp $\infty$. A section $x\in X(\mathbf Q_p)$ meets the smooth locus of one component after passing to the regular model. The divisor $[x]-[\infty]$ has multidegree equal to the difference of the two component vertices. Its class in the graph Jacobian is exactly the component of the Albanese image:

$$
\operatorname{sp}_p(\iota_\infty(x))
=[v(x)-v_\infty]\in\Phi_p. \tag{8.1}
$$

Here the bracket means the class obtained from the intersection lattice, not a formal subtraction in the free vertex group. Formula (8.1) follows by extending the horizontal divisor to the regular model, taking its multidegree on the irreducible components, and then passing from the relative Picard functor to its separated quotient.

Write the irreducible components of the special fiber as $Y_i$ and let $M=((Y_i\cdot Y_j))$ be their intersection matrix. If the horizontal closures of $x$ and $\infty$ meet $Y_a$ and $Y_b$, their intersection vector is

$$
d_i=(\overline x-\overline\infty)\cdot Y_i
=\delta_{i,a}-\delta_{i,b}. \tag{8.2}
$$

The component group is the degree-zero vertex lattice modulo $M\mathbf Z^{\{Y_i\}}$, with the usual adjustment for total-fiber multiplicities. If a divisor representative is changed by $\operatorname{div}(g)$ on the generic curve, then on the regular surface

$$
\operatorname{div}_{\mathcal X}(g)
=\overline{\operatorname{div}_X(g)}+\sum_i a_iY_i. \tag{8.3}
$$

Intersecting this principal divisor with every $Y_j$ shows that the horizontal multidegree changes by $-M(a_i)$. It therefore has the same class in the component cokernel. This proves both well-definedness and (8.1), rather than merely describing what the formula should be.

If a section meets a thick coarse crossing, passing to the regular resolution locates it on one of the inserted components according to the valuations of the two local parameters. Formula (8.2) is then applied on the subdivided graph. Contracting back to the weighted graph gives the same class because subdivision preserves the graph Jacobian and monodromy pairing.

The cusp $0$ meets the other principal component. If $\delta_p$ denotes the resulting endpoint-difference class, then

$$
\operatorname{sp}_p(c)=\delta_p. \tag{8.4}
$$

This is an identification of a particular class, not a proof that $\delta_p$ generates $\Phi_p$ or has any prescribed order. Indeed, (4.11) only implies $n_p\delta_p=0$, which is compatible with many possible component groups.

The formula is Hecke equivariant. If $t\in\mathbb T$, then

$$
\operatorname{sp}_p(t\iota_\infty(x))
=t\operatorname{sp}_p(\iota_\infty(x)). \tag{8.5}
$$

For a quotient $q:J\twoheadrightarrow A$, the Néron mapping property extends $q$ to the Néron models and gives a component map

$$
\Phi_J\longrightarrow\Phi_A. \tag{8.6}
$$

This map need not be surjective and its kernel is not determined solely by the connected kernel of $q$ on the generic fiber. Component-group functoriality is not exact in arbitrary short exact sequences of abelian varieties.

At a good prime $r\ne p$, there is no component group. If $x$ and $y$ have the same reduction on a smooth proper model, then

$$
\iota_y(x)=[x]-[y]
$$

reduces to the origin in the abelian scheme. The conclusion is only that the class lies in the formal kernel. For torsion of order prime to $r$, that kernel contains no nonzero such torsion; for $r$-primary torsion, an additional local argument is required.

These observations separate three pieces of information that are often conflated:

1. the component met by a point of the curve;
2. the reduction of its Jacobian class inside the identity component;
3. the image of that class in a chosen quotient.

Only the first is read directly from the dual graph. The other two use the Picard and Néron functoriality.

## 9. Hecke-stable subvarieties and quotients

Let $J$ be an abelian variety with an action of a commutative ring $\mathbb T$ that is finite as a $\mathbf Z$-module. If $u:J^r\to J$ is a homomorphism, the image of $u$ is connected, proper, and smooth; hence it is an abelian subvariety. This elementary fact constructs the images of Hecke ideals without an appeal to rational eigenspace decompositions.

For an ideal $I=(t_1,\ldots,t_r)\subset\mathbb T$, define

$$
IJ=\operatorname{im}\left(J^r\longrightarrow J,
(x_i)\longmapsto\sum_it_ix_i\right). \tag{9.1}
$$

The result is independent of the chosen generators and is Hecke stable. The connected quotient

$$
J_I=J/IJ \tag{9.2}
$$

is an abelian variety, and the action descends through $\mathbb T/I$. Its faithful coefficient ring is the image of $\mathbb T/I$ in $\operatorname{End}(J_I)$; that map need not be injective.

The notation

$$
J[I]=\bigcap_{t\in I}\ker(t:J\to J) \tag{9.3}
$$

means something different. It is the scheme annihilated by $I$, possibly with a positive-dimensional identity component and a finite component group. The image $IJ$ records what the ideal generates; $J[I]$ records what it kills.

There is a decisive warning when $I$ has finite additive index in $\mathbb T$. Then $I$ contains a nonzero integer $m$. Since multiplication by $m$ is surjective on an abelian variety,

$$
mJ=J\subset IJ,
$$

and therefore

$$
J_I=0. \tag{9.4}
$$

Thus quotienting an abelian variety by the image of the classical finite-index Eisenstein ideal cannot produce a positive-dimensional Eisenstein quotient. A nonzero quotient must be selected by a characteristic-zero factor, an annihilator ideal that contains no nonzero integer, or equivalent rational idempotent data.

The simplest example is already decisive. For $I=(m)\subset\mathbf Z$ acting on a positive-dimensional abelian variety, $IJ=mJ=J$, so $J_I=0$, whereas

$$
J[I]=J[m]
$$

is a nontrivial finite group scheme of rank $m^{2\dim J}$. Thus “quotient by the ideal” and “torsion killed by the ideal” point in opposite directions. The same distinction remains at an Eisenstein ideal even when both constructions carry the same residue eigensystem.

Dualizing (9.2) and using the principal polarization identifies $J_I^\vee$ with the connected subvariety

$$
J[I^\dagger]^0\subset J. \tag{9.5}
$$

For a Rosati-stable ideal the symbols on the two sides agree, but quotient and subvariety remain dual constructions rather than the same embedded object.

For every prime $\ell$, the exact sequence of abelian varieties gives an exact sequence of covariant Tate modules

$$
0\longrightarrow T_\ell(IJ)
\longrightarrow T_\ell J
\longrightarrow T_\ell J_I
\longrightarrow0. \tag{9.6}
$$

Surjectivity on the right can be checked at every finite level. Given $a\in J_I[\ell^n](\overline{\mathbf Q})$, lift it to $x\in J(\overline{\mathbf Q})$. Then $\ell^nx$ lies in $IJ$. Multiplication by $\ell^n$ is surjective on the abelian subvariety $IJ$, so choose $b\in IJ$ with $\ell^nb=\ell^nx$. The point $x-b$ is an $\ell^n$-torsion lift of $a$. Passing to inverse limits proves (9.6) without assuming a splitting.

After tensoring with $\mathbf Q_\ell$, the image of the first map is exactly the vector-space span of the images of the elements of $I$, and therefore

$$
V_\ell J_I\simeq
V_\ell J/I(V_\ell J). \tag{9.7}
$$

Integrally, the quotient by $I(T_\ell J)$ can differ from (9.6) by a finite saturation defect. Likewise, localization at a maximal ideal retains an entire local Hecke packet, not merely the vectors killed by that maximal ideal. Freeness over $\mathbf Z_\ell$ is automatic; freeness of a specified rank over a local Hecke algebra is a separate multiplicity assertion.

Concretely, two full lattices in one rational eigenspace can differ by an $\ell$-power index. They define the same $V_\ell$ but different reductions modulo $\ell$, so one can contain a residual line that the other does not. A rational idempotent detects the common vector space and is blind to this index. Only a connected-kernel exact sequence, or an independently proved saturation theorem, identifies the integral selected lattice.

An arbitrary quotient $q:J\twoheadrightarrow A$ can be made **optimal** by replacing its kernel with its identity component. Equivalently, if a rational idempotent $e\in\operatorname{End}^0(J)$ selects an isogeny factor, choose $m$ with $me$ integral and put

$$
B=\operatorname{im}(m(1-e)),\qquad A_e=J/B. \tag{9.8}
$$

Then $B$ is independent of $m$, $A_e$ has connected kernel, and $V_\ell A_e=eV_\ell J$. Optimality fixes the integral representative of the rational factor and prevents an unnoticed postcomposition by an isogeny.

Independence from the denominator is elementary but important. If both $m(1-e)$ and $m'(1-e)$ are integral, their images have the same rational tangent space. After replacing $m,m'$ by a common multiple, each image is the image of a nonzero multiplication map on the same abelian subvariety, hence is that whole subvariety. Rational support alone does not name a completed local factor. Once a maximal ideal is specified, however, the distinction between the two projectors can already be stated exactly.

Return to the prime-level acting algebra $\mathbb T$. Its generators are commuting Rosati-self-adjoint operators: the away-level operators are self-adjoint by (3.4), and the trace calculation following (4.13) gives $U_p=-w_p$. Every element of the resulting commutative rational algebra is therefore self-adjoint. A nilpotent self-adjoint operator for a positive Hodge metric is zero. Hence $\mathbb T\otimes\mathbf Q$ is reduced and therefore is a product of number fields,

$$
\mathbb T\otimes\mathbf Q=\prod_iK_i. \tag{9.9}
$$

Let $\mathfrak m\subset\mathbb T$ be a maximal ideal of residue characteristic $\ell$. The finite $\mathbf Z_\ell$-algebra

$$
\mathbb T_\ell=\mathbb T\otimes\mathbf Z_\ell
\simeq\prod_{\mathfrak n\mid\ell}\widehat{\mathbb T}_{\mathfrak n}. \tag{9.10}
$$

is a product of complete local factors. Here is the integral algebra behind the decomposition. Modulo a sufficiently high power of $\ell$, powers of the distinct maximal ideals are pairwise comaximal, so the Chinese remainder theorem splits the finite quotient into its local factors. The transition maps have nilpotent kernels. Coordinate idempotents lift uniquely through such a kernel: if $x^2-x$ lies in the kernel, the usual correction by the unit $2x-1$ raises the nilpotence order of the error. Passing to the inverse limit gives (9.10), because the finite $\mathbf Z_\ell$-module $\mathbb T_\ell$ is $\ell$-adically complete.

Let $e_{\mathfrak m}\in\mathbb T_\ell$ be $1$ on the $\mathfrak m$-factor and $0$ on the others. This is a **completed idempotent**. The integral Hecke action extends continuously to $\mathbb T_\ell$, so $e_{\mathfrak m}$ acts on $T_\ell J$, but it need not be an algebraic endomorphism of $J$ over $\mathbf Q$.

For each factor $K_i$, let $\mathcal O_i$ be the image of $\mathbb T$ in $K_i$. Retain $K_i$ if some maximal ideal of $\mathcal O_i$ contracts to $\mathfrak m$, and let

$$
E_{\mathfrak m}\in\mathbb T\otimes\mathbf Q \tag{9.11}
$$

be the sum of the corresponding field idempotents. This is the **rational-support idempotent**. It retains a whole characteristic-zero factor, including every companion prime above $\ell$, whereas $e_{\mathfrak m}$ retains only one completed branch. Thus no equality $E_{\mathfrak m}=e_{\mathfrak m}$ is asserted; the exact compatibility is

$$
e_{\mathfrak m}E_{\mathfrak m}=e_{\mathfrak m}
\quad\text{in }\mathbb T\otimes\mathbf Q_\ell. \tag{9.12}
$$

Using (9.8), the rational projector constructs an optimal quotient

$$
A_{\mathfrak m}
=J/\operatorname{im}\bigl(a(1-E_{\mathfrak m})\bigr) \tag{9.13}
$$

for any denominator $a$ making $aE_{\mathfrak m}$ integral. The connected-kernel Tate sequence is exact. Its kernel has rational Tate space $(1-E_{\mathfrak m})V_\ell J$, which the completed idempotent kills. Since its integral Tate module is torsion free, applying $e_{\mathfrak m}$ gives the integral comparison

$$
e_{\mathfrak m}T_\ell J
\xrightarrow{\ \sim\ }
e_{\mathfrak m}T_\ell A_{\mathfrak m}. \tag{9.14}
$$

This does not yet produce the finite-flat completed tower used in Eisenstein descent. If $\mathfrak m$ contains $I_{\mathrm{Eis}}$, then (9.13) is the rational Eisenstein-support quotient attached to $\mathfrak m$. Equations (4.17)--(4.18) produce at least one such nonzero quotient whenever $J\ne0$. This book has not proved that $(\ell,I_{\mathrm{Eis}})$ is proper for every $\ell\mid n_p$, calculated its local depth, or compared (9.14) with images on every finite-flat torsion level. Those are precisely the later congruence and completed-tower inputs. In particular, the eta-quotient annihilator is used only together with the proved nonzero cuspidal class, not by itself, to obtain existence.

## 10. The winding quotient and its Eisenstein boundary

The boundary path from $0$ to $\infty$ is a relative homology class. Integration against holomorphic differentials defines a unique **winding element**

$$
e_{\mathrm w}\in H_1(X_0(p)(\mathbf C),\mathbf R) \tag{10.1}
$$

by

$$
\int_{e_{\mathrm w}}\omega
=-\int_0^{i\infty}\omega
\qquad
(\omega\in H^0(X_0(p)_{\mathbf C},\Omega^1)). \tag{10.2}
$$

The right side converges because a holomorphic differential on the compact curve corresponds to a weight-two cusp form. The perfect real period pairing proves existence and uniqueness. Its rationality is a further arithmetic statement, proved next from the cuspidal relation rather than assumed from the analytic definition.

In fact the eta-quotient relation proves the stronger rationality that the abbreviated construction would miss. Let $\delta$ be the relative path from $0$ to $\infty$. Its Abel--Jacobi period class is $[\infty]-[0]=-c$. Since $n_pc=0$ by (4.11), Abel's theorem gives an absolute integral cycle $\gamma\in H_1(X(\mathbf C),\mathbf Z)$ such that

$$
\int_\gamma\omega
=n_p\int_\delta\omega
\qquad\text{for every holomorphic }\omega. \tag{10.3}
$$

Comparing (10.2) and (10.3), and using perfection of the real period pairing, yields

$$
n_pe_{\mathrm w}=-\gamma,
\qquad
e_{\mathrm w}\in H_1(X(\mathbf C),\mathbf Q). \tag{10.4}
$$

Thus the winding element is a rational absolute homology class whose denominator divides the proved modular-unit bound. No exact cuspidal order was used.

Let

$$
I_{\mathrm w}=\{t\in\mathbb T:t e_{\mathrm w}=0\}. \tag{10.5}
$$

Because the Hecke operators commute, this is an ideal. It is saturated as an additive subgroup: if $nt e_{\mathrm w}=0$ for a nonzero integer $n$, then $te_{\mathrm w}=0$ in the real vector space. In particular, when $e_{\mathrm w}\ne0$, the ideal contains no nonzero integer.

The **winding quotient** is

$$
J_{\mathrm w}=J_0(p)/I_{\mathrm w}J_0(p). \tag{10.6}
$$

Chapter 9 proves that this is an abelian variety with connected kernel. If $e_{\mathrm w}=0$, the definition gives the zero quotient. When $e_{\mathrm w}\ne0$, it is nonzero. Indeed, use the field decomposition (9.9). On a factor where the component of $e_{\mathrm w}$ is nonzero, its annihilator is zero. Formula (9.7) therefore retains that factor in $J_{\mathrm w}$.

The rational support is read from the map

$$
\mathbb T\otimes\mathbf Q\longrightarrow
H_1(X(\mathbf C),\mathbf R),
\qquad t\longmapsto te_{\mathrm w}, \tag{10.7}
$$

whose kernel is $I_{\mathrm w}\otimes\mathbf Q$. On any simultaneous Hecke-factor decomposition, the surviving factors are precisely those on which the winding period is nonzero. The construction of (10.6), however, needs no choice of such a decomposition.

There is a familiar analytic reading of the same support. If

$$
\omega_f=2\pi i f(z)\,dz
$$

is the differential attached to a normalized weight-two eigenform, then

$$
-\int_0^{i\infty}\omega_f=L(f,1). \tag{10.8}
$$

The endpoint and summation convention in this formula can be checked directly. For $\varepsilon>0$, uniform convergence on $\operatorname{Im}z\geq\varepsilon$ gives

$$
-\int_{i\varepsilon}^{i\infty}\omega_f
=\sum_{n\geq1}\frac{a_n}{n}e^{-2\pi n\varepsilon}. \tag{10.8a}
$$

The cusp expansion after the Fricke change $z\mapsto-1/(pz)$ shows exponential decay as $z$ approaches $0$ vertically, so the integral has a limit as $\varepsilon\to0^+$. For completeness, put $g=f|_2W_p$ and $y_0=p^{-1/2}$. The slash normalization gives

$$
g(it)=-\frac{1}{pt^2}f\!\left(\frac{i}{pt}\right).
$$

Consequently the Mellin integral, initially compared with the Fourier series in a right half-plane, can be split as

$$
\int_0^\infty f(iy)y^{s-1}\,dy
=\int_{y_0}^\infty f(iy)y^{s-1}\,dy
-p^{1-s}\int_{y_0}^\infty g(it)t^{1-s}\,dt. \tag{10.8b}
$$

Both integrals on the right are entire functions of $s$ because $f$ and $g$ decay exponentially at infinity. For real part of $s$ sufficiently large, termwise integration at the cusp $\infty$ gives

$$
\int_0^\infty f(iy)y^{s-1}\,dy
=(2\pi)^{-s}\Gamma(s)\sum_{n\geq1}a_nn^{-s}.
$$

Equation (10.8b) therefore continues the Dirichlet series to $s=1$. Since $\Gamma(1)=1$, evaluating there shows that its value is the Abel limit in (10.8a), proving (10.8) without formally integrating at a boundary where the Fourier series is not uniformly convergent. Consequently the $f$-factor survives precisely when its winding period, equivalently this central value, is nonzero. Equation (10.8) identifies the factors; it does not convert analytic nonvanishing into a theorem about rational Mordell--Weil rank.

The boundary of the construction is Eisenstein in a limited and precise sense. In the relative homology sequence

$$
H_1(X,\mathbf Z)\longrightarrow H_1(X,\{0,\infty\};\mathbf Z)
\xrightarrow{\partial}\operatorname{Div}^0\{0,\infty\}
\longrightarrow0, \tag{10.9}
$$

the modular path has boundary $[\infty]-[0]$. The divisor-level calculation behind (4.12) shows that every $T_q-(q+1)$ with $q\ne p$ kills this free boundary class, so its action sends the path into absolute homology. Equation (4.14), by contrast, is an equality in the Jacobian; by itself it does not calculate $U_p$ on the free boundary module. Thus the boundary origin explains the away-level Eisenstein relations, while the level relation has only been proved on the cuspidal class. This deliberately falls short of proving that $I_{\mathrm w}=I_{\mathrm{Eis}}$, or that the two ideals have the same index or support. The terminology therefore remains **winding quotient**: it is not the rational Eisenstein-support quotient (9.13), and it is not the completed local Eisenstein factor used in the later finite-flat theory.

The associated modular map is

$$
f_{\mathrm w}:X_0(p)\longrightarrow J_{\mathrm w},
\qquad
x\longmapsto q_{\mathrm w}([x]-[\infty]). \tag{10.10}
$$

Changing the base point to $0$ translates it by $-q_{\mathrm w}(c)$. Its differential is the quotient of the weight-two differential space selected by the support map (10.7). Its Tate module is governed by the exact sequence (9.6), not by a naive quotient of the integral lattice.

The construction alone makes no assertion that $J_{\mathrm w}(\mathbf Q)$ is finite, that every rational point is torsion, or that a particular Eisenstein maximal ideal occurs. Proving finiteness from (10.8) would require an analytic-rank-zero theorem not present among the prerequisites. The later finite-flat development instead specializes (9.13) at an actual Eisenstein maximal ideal and obtains finiteness by descent. Keeping both boundaries explicit prevents the existence of a quotient from being mistaken for a Mordell--Weil theorem and prevents the winding quotient from being identified with a rational or completed Eisenstein factor.

## 11. Reduction and rational torsion

Let $A/\mathbf Q$ be a quotient of $J_0(p)$ with good reduction at a prime $r$. The reduction map fits into

$$
0\longrightarrow A_1(\mathbf Q_r)
\longrightarrow A(\mathbf Q_r)
\longrightarrow\widetilde A(\mathbf F_r), \tag{11.1}
$$

where $A_1$ is the formal kernel. For $m$ prime to $r$, multiplication by $m$ is an automorphism of the formal group. Hence reduction is injective on prime-to-$r$ torsion:

$$
A(\mathbf Q)[m]\hookrightarrow\widetilde A(\mathbf F_r)
\qquad((m,r)=1). \tag{11.2}
$$

For $r>2$ over the unramified field $\mathbf Q_r$, the formal logarithm also rules out nonzero torsion in the formal kernel, so all rational torsion injects. The more robust statement is (11.2), which remains valid without that strengthening.

Using two good primes of different residue characteristics bounds every primary part. If $r,s>2$ are good, then

$$
\#A(\mathbf Q)_{\mathrm{tors}}
\mid\gcd\bigl(\#\widetilde A(\mathbf F_r),
\#\widetilde A(\mathbf F_s)\bigr). \tag{11.3}
$$

Point counts are obtained from Frobenius:

$$
\#\widetilde A(\mathbf F_r)
=\det(1-F_r\mid V_\ell A),
\qquad\ell\ne r. \tag{11.4}
$$

For a Hecke quotient, (2.5) constrains this determinant. An explicit numerical count still requires the dimensions, eigenvalues, and multiplicities of the selected factor; they do not follow from the abstract quotient construction.

At the level prime $p$, reduction has two layers:

$$
A(\mathbf Q_p)\longrightarrow\mathcal A_{\mathbf F_p}(\mathbf F_p)
\longrightarrow\Phi_A(\mathbf F_p). \tag{11.5}
$$

The second arrow detects a component defect. A point with nonzero component class cannot be the identity, but a point with zero component class may remain nonzero in the torus. For the Albanese image, (8.1) computes the first obstruction from the component of the reduced modular point. Passing to a quotient applies (8.6), which may kill that obstruction.

The cuspidal point illustrates all three layers. It is torsion by (4.11), its component at $p$ is the endpoint class $\delta_p$ by (8.4), and its image in a quotient may have smaller order or vanish. None of these observations determines its exact order in $J(\mathbf Q)$.

## 12. Finite subgroup schemes and Hecke modules

For an ideal $I\subset\mathbb T$ and an integer $m\geq1$, the scheme

$$
J[I,m]=J[I]\cap J[m] \tag{12.1}
$$

is a finite commutative group scheme carrying compatible Hecke and Galois actions. Retaining the scheme structure distinguishes constant, multiplicative, and connected constituents that may have identical orders.

If $P\in J(\mathbf Q)$ has order $m$, the morphism

$$
(\mathbf Z/m\mathbf Z)_{\mathbf Q}\longrightarrow J,
\qquad1\longmapsto P \tag{12.2}
$$

is a closed immersion onto a constant cyclic subgroup scheme. If an ideal $I$ kills $P$, this subgroup lies in $J[I,m]$. Its Cartier dual is of multiplicative type. Conversely, a multiplicative subgroup can have very few rational geometric generators; rational points do not recover its scheme structure.

Write $\mathcal C(p)$ for the constant cyclic subgroup scheme that is the image of (12.2) with $P=c$ and $m=\operatorname{ord}(c)$; it is trivial when $c=0$. The prime-level boundary then gives two natural subgroup schemes:

$$
\mathcal C(p)\subset J[n_p],
\qquad
\Sigma(p)\subset J[d], \tag{12.3}
$$

with the first constant and the second of multiplicative type. The first is stable under the full prime-level Hecke algebra; the second has been proved stable under the away-from-$p$ operators. The displayed ambient torsion bounds are all that has been proved here; replacing them by exact orders or a full level-prime action would strengthen the result.

Torsion points are not the only honest bridge to finite coefficients. Let $A$ be any Hecke-stable quotient of $J$ and let $m\geq2$. The multiplication sequence gives the Kummer injection

$$
\kappa_m:A(\mathbf Q)/mA(\mathbf Q)
\hookrightarrow H^1(\mathbf Q,A[m]). \tag{12.4}
$$

If $P\in A(\mathbf Q)$ and $Q\in A(\overline{\mathbf Q})$ satisfies $mQ=P$, then $\kappa_m(P)$ is represented by

$$
\sigma\longmapsto\sigma Q-Q\in A[m]. \tag{12.5}
$$

Changing $Q$ changes the cocycle by a coboundary, while a trivial cocycle makes a translate of $Q$ rational and hence makes $P$ divisible by $m$. This proves injectivity directly. Hecke endomorphisms commute with multiplication, so

$$
\kappa_m(tP)=t\kappa_m(P). \tag{12.6}
$$

Weak Mordell--Weil says $A(\mathbf Q)/mA(\mathbf Q)$ is finite. Consequently every rational point, whether torsion or not, generates a finite Hecke module

$$
M_m(P)=\mathbb T\cdot(P\bmod mA(\mathbf Q)) \tag{12.7}
$$

whose Kummer realization has coefficients in the finite group scheme $A[m]$. This is the unconditional finite-module interface promised by the catalog. If an ideal $I$ kills $M_m(P)$, the exact conclusion is $IP\subseteq mA(\mathbf Q)$, not $IP=0$.

For $m$ invertible at a good prime $r$, the finite subgroup schemes occurring above extend inside the finite étale group $\mathcal A[m]$ of the abelian scheme, and their geometric Hecke modules specialize faithfully. This assertion concerns subgroup schemes of torsion; a Kummer class instead extends as a torsor when its local point is integral. At $r\mid m$, the special fiber of a finite flat closure has the connected--étale sequence

$$
0\longrightarrow G^0\longrightarrow G
\longrightarrow G^{\mathrm{et}}\longrightarrow0, \tag{12.8}
$$

and that sequence must be retained. Cartier duality exchanges the connected multiplicative part with an étale quotient. Counting geometric points sees $G^{\mathrm{et}}$ but can miss $G^0$.

At a good prime $r\nmid m$, the local image of (12.4) is unramified: the finite étale group $A[m]$ and its torsors extend over $\mathbf Z_r$, and Lang's theorem identifies integral Kummer classes with the unramified subgroup. At $r\mid m$, “unramified” is generally too small because connected finite-flat classes can occur.

At the semistable prime one can form a schematic closure in the Néron model, but Section 6 warns that it need not be finite. If finiteness and flatness have been established for a particular closure, its intersection with the identity component may lie in the torus and its component image is a quotient group. There is no automatic exact sequence obtained by applying “component group” to a short exact sequence of generic-fiber group schemes.

The same caution applies to Hecke modules. The rational representation

$$
V_\ell A
$$

of a quotient is a direct summand in the isogeny category, whereas $T_\ell A$ is an integral lattice that can be glued to its complement along finite torsion. A residual eigensystem in $A[\ell]$ is therefore not, by itself, evidence that the whole Tate module is free of rank two over a local Hecke algebra.

## 13. Rational points on the modular curve

A noncuspidal rational point $x\in X_0(p)(\mathbf Q)$ is first a rational point of the coarse curve. It comes from a rational cyclic subgroup scheme of rank $p$, equivalently a rational cyclic $p$-isogeny, exactly when its moduli gerbe is neutral. Neutrality is automatic away from the exceptional values $j=0,1728$ in characteristic zero, and it is automatic in the direction used for an actual elliptic curve with a given Galois-stable line, because the pair is constructed before its coarse point. At the exceptional fibers an arbitrary coarse point requires a stabilizer or descent check.

Even after neutrality, the subgroup need not have a rational generator. Passing from $X_0(p)$ to $X_1(p)$ asks for that additional generator and hence for triviality of the kernel character. The three notions—coarse point, rational cyclic subgroup, and rational generator—will not be identified.

Send $x$ to

$$
P_x=\iota_\infty(x)=[x]-[\infty]\in J(\mathbf Q) \tag{13.1}
$$

or to its winding image

$$
P_{x,\mathrm w}=q_{\mathrm w}(P_x)\in J_{\mathrm w}(\mathbf Q). \tag{13.2}
$$

The construction relates a modular point to the previous structures as follows:

$$
\begin{array}{c}
x\in X_0(p)(\mathbf Q)\\
\downarrow\ \iota_\infty\\
P_x\in J(\mathbf Q)\\
\swarrow\qquad\searrow\\
\text{reduction and components}\qquad
\text{Hecke quotients and finite Kummer modules}.
\end{array} \tag{13.3}
$$

The vertical arrow is unconditional: it uses only the rational divisor $x-\infty$, not a modular lift of $x$. From $P_x$ there are then three different finite interfaces.

First, for every $m\ge2$ its class modulo $mJ(\mathbf Q)$ lies in the finite Hecke module $M_m(P_x)$ of (12.7), and its Kummer cocycle has coefficients in $J[m]$. The same statement holds after passage to $J_{\mathrm w}$ or any other Hecke quotient. This needs no torsion or rank-zero hypothesis.

Second, at a good prime $r$, reduction gives a point of the finite group $\widetilde J(\mathbf F_r)$. The subgroup generated by its Hecke orbit is a finite Hecke module in the special fiber. This reduction module records only a local image; an annihilator found there need not annihilate $P_x$ globally.

Third, if an independent argument proves that an image of $P_x$ is torsion, its actual cyclic closure is a constant finite subgroup scheme over $\mathbf Q$. This is stronger than either of the first two interfaces and must not be inferred from them.

At a good prime, equality of reductions of $x$ and $\infty$ puts $P_x$ in the formal kernel. If $P_x$ is known independently to be prime-to-residue torsion, (11.2) forces it to vanish. At the level prime, the component met by $x$ gives $\operatorname{sp}_p(P_x)$ through (8.1). In the winding quotient one then applies the induced component map (8.6).

If a Hecke ideal kills $P_{x,\mathrm w}$ and the point has finite order $m$, its cyclic closure is a constant subgroup of

$$
J_{\mathrm w}[I,m]. \tag{13.4}
$$

This is the strongest form of the bridge from rational modular points to finite subgroup schemes. Both hypotheses in the preceding sentence matter. Construction of $J_{\mathrm w}$ does not prove that $P_{x,\mathrm w}$ is torsion, and a relation in a reduction group does not automatically lift to a global Hecke annihilator. Without those hypotheses, the unconditional statement is instead the finite Kummer module (12.4)--(12.7).

Low genus must be handled separately. If $g(X_0(p))=0$, then $J=0$ and every $P_x$ vanishes, even though the curve may have many rational points. If $g=1$, the base cusp identifies $X$ with $J$, so information about $P_x$ is information about $x$ itself. In genus at least two, the Abel image is a proper curve in $J$ and quotient maps can identify distinct points. A formal-immersion or Mordell--Weil argument requires extra hypotheses beyond the present structural package.

## 14. The prime-level Jacobian package

We can now state exactly what has been constructed and proved.

**Theorem 14.1.** Let $p\geq5$ be prime. Put $X=X_0(p)$, $J=J_0(p)$, and $c=[0]-[\infty]$. Then:

1. The pointed Albanese map $x\mapsto[x]-[\infty]$ is compatible with Hecke correspondences through the divisor formula (2.4), with quotient maps, and with Néron specialization. Changing the base cusp translates it by $c$.

2. With the source-to-quotient convention, $T_q=\beta_*\alpha^*$ for $q\ne p$. The canonical polarization makes $T_q$ self-adjoint, sends diamonds to their inverses, and identifies the adjoint of a level operator with the transpose correspondence.

3. The cuspidal subgroup $C(p)=\langle c\rangle$ is finite. More precisely,

   $$
   n_pc=0,
   \qquad n_p=\frac{p-1}{\gcd(p-1,12)},
   $$

   and $T_qc=(q+1)c$, $U_pc=c$, and $w_pc=-c$.

4. The Shimura kernel $\Sigma(p)=\ker(J_0(p)\to J_1(p))$ is a finite subgroup scheme of multiplicative type, killed by the degree of the forgetful map and stable under every away-from-$p$ Hecke operator. No full level-prime action or exact order is included.

5. At $p$, the geometric identity component of the Néron model is a torus with character lattice $X_p=\operatorname{Div}^0(S_p)$. Its monodromy pairing is

   $$
   \langle a,b\rangle=\sum_{s\in S_p}e_sa_sb_s,
   $$

   and the geometric component group is the cokernel of $X_p\to X_p^\vee$. For $\ell\ne p$, the outer graded pieces of the monodromy filtration are $X_p^\vee\otimes\mathbf Z_\ell(1)$ and $X_p\otimes\mathbf Z_\ell$, and the monodromy operator between them is the completed pairing map.

6. The component of $[x]-[\infty]$ is the weighted graph class of the difference between the components met by $x$ and $\infty$. In particular, $c$ specializes to the endpoint-difference class.

7. Every Hecke ideal $I$ defines the connected quotient $J/IJ$ and the finite annihilator schemes $J[I,m]$. If $I$ contains a nonzero integer, the connected quotient is zero. Rational and integral Tate-module quotients differ by a possible saturation defect. A maximal ideal $\mathfrak m$ of residue characteristic $\ell$ has separately defined completed and rational-support idempotents $e_{\mathfrak m}$ and $E_{\mathfrak m}$; the latter defines the optimal quotient $A_{\mathfrak m}$, and the connected-kernel sequence gives $e_{\mathfrak m}T_\ell J\simeq e_{\mathfrak m}T_\ell A_{\mathfrak m}$. If $J\ne0$, the nonzero cuspidal class produces at least one Eisenstein maximal ideal $\mathfrak m_c$ and hence a nonzero rational Eisenstein-support quotient $A_{\mathfrak m_c}$. No assertion for every $\ell\mid n_p$ and no finite-flat completed tower are included.

8. The winding element is rational and satisfies $n_pe_{\mathrm w}\in H_1(X(\mathbf C),\mathbf Z)$. Its annihilator $I_{\mathrm w}$ defines an optimal winding quotient

   $$
   J_{\mathrm w}=J/I_{\mathrm w}J
   $$

   and a modular map $X\to J_{\mathrm w}$. The quotient carries the induced Hecke action and has the Néron, component, duality, and Tate-module structures described above.

9. For every Hecke quotient $A$ and every $m\ge2$, weak Mordell--Weil makes $A(\mathbf Q)/mA(\mathbf Q)$ a finite Hecke module, and Kummer theory injects it into $H^1(\mathbf Q,A[m])$. A rational torsion image gives the stronger object of a constant cyclic finite subgroup scheme. Good reduction injects its prime-to-residue part, while level-prime reduction maps it to the weighted component group.

**Proof.** The Picard and Albanese statements are proved in Chapter 1. Chapters 2 and 3 establish the correspondence convention and adjoints. The eta quotient proves the cuspidal annihilator in Chapter 4, while the Tate-cusp and trace calculations prove its Hecke character; Abel injectivity then supplies the nonzero class that produces $\mathfrak m_c$. Pullback, norm, and descent prove the limited Shimura assertions in Chapter 5. Chapters 6--8 apply the Néron mapping property, the semistable Picard description, the weighted dual graph, and the monodromy filtration. Chapter 9 constructs connected Hecke quotients, proves the finite-index warning, and separates rational support from completed local selection. Chapter 10 proves rationality of the winding element and constructs its distinct winding quotient. Chapters 11--13 give reduction, Kummer, and finite-group-scheme interfaces. No assertion in the list uses an exact cuspidal order, an exact Eisenstein index, a selected completed finite-flat tower, or a Mordell--Weil finiteness theorem. $\square$

The dependency closure is exact. Betti--de Rham comparison supplies the integral period lattice, Abel's period criterion, and rational correspondence action used by the winding element. Relative Picard theory supplies the Abel map, Albanese property, theta polarization, pullback, norm, and transpose. The theory of abelian schemes supplies finite multiplication kernels, duality, Weil pairings, and quotient formation. Néron theory supplies extension, component maps, the separated Picard quotient, and the weighted graph discriminant. Weak Mordell--Weil supplies only the finiteness of $A(\mathbf Q)/mA(\mathbf Q)$ and its Kummer realization, not finite generation or rank zero. Integral modular forms supply the discriminant, cusp expansions, and normalized away-level Hecke operators. The modular-Jacobian correspondence theory supplies integral variance, Eichler--Shimura, cotangent compatibility, and the bad-fiber monodromy lattice. The preceding modular-curve book supplies the compactification, two cusp types, level-prime model, and the exact coarse-point neutrality caveat. These are precisely Books 25, 35, 38, 40, 47, 113--114, and 130 in the dependency row.

The forward boundary is equally exact:

| Later book | New result not used here                                                                                                            |
| ---------- | ----------------------------------------------------------------------------------------------------------------------------------- |
| 169        | Synthesis of the selected prime-level Eisenstein package                                                                            |
| 132        | Exact congruence modulus and $\mathbb T/I_{\mathrm{Eis}}\simeq\mathbf Z/n_p\mathbf Z$                                               |
| 133        | Exact order of $c$, cyclic component group, generator specialization, and the limited exact Shimura calculation                     |
| 134        | Admissible constant--multiplicative finite-flat filtrations and their extension theory                                              |
| 147        | Selection at every Eisenstein prime, scheme-level comparison at each torsion power, and the exact finite-flat tower                 |
| 148        | Eisenstein descent and finiteness of the selected quotient's rational points                                                        |
| 149        | Primitive cotangent lattices, oriented formal immersion, and cusp-disk rigidity                                                     |
| 151        | Prime-isogeny and prime-torsion classification, exceptional genus-two calculations, and semistable full-two residual irreducibility |

Thus the lattice presentation (7.6) has not been replaced by a closed order formula; the annihilator (4.11) has not been promoted to the exact order of $c$; $I_{\mathrm{Eis}}$ has not been assigned an index; a completed idempotent has not been promoted to a finite-flat tower; the winding quotient has not been identified with either Eisenstein projector; and its rational points have not been claimed finite. Those are not missing proofs inside Theorem 14.1. They are the stated inputs and conclusions of the later books.

The direct downstream contract is narrower than that forward list. Book 169 uses the pointed Albanese map, the connected optimal-quotient construction, the prime-level Néron and monodromy geometry, the $U_p=-w_p$ convention, and the distinction among rational points, finite subgroup schemes, and components. Books 132--134 and 147--149 do not depend on Book 131; they prove the specialist chain independently and Book 169 assembles it. The current residual-irreducibility volume uses the specialist formal-immersion and explicit-sieve chain directly; no deleted synthesis volume is treated as a source. Consequently no exact index, exact subgroup order, completed finite-flat tower, finiteness theorem, formal immersion, prime-isogeny classification, or Fermat conclusion flows from Theorem 14.1 alone.

The two quotient branches constructed in this volume fit into the common chain

$$
X_0(p)
\xrightarrow{\ \iota_\infty\ }
J_0(p)
\longrightarrow
\begin{cases}
A_{\mathfrak m_c},&\text{rational Eisenstein support when }J\ne0,\\
J_{\mathrm w},&\text{winding-period support},
\end{cases}
\longrightarrow
\begin{cases}
\text{finite Kummer--Hecke modules and torsion subgroup schemes},\\
\text{good-prime reduction},\\
\text{level-prime component classes}.
\end{cases} \tag{14.1}
$$

This is the Jacobian framework required for arithmetic arguments with rational points: it is functorial, convention-conscious, integral where integrality has been proved, and explicit about every conclusion that still needs an exact boundary or descent calculation.
