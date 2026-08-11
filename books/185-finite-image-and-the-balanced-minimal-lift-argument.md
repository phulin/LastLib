# Finite Image and the Balanced Minimal-Lift Argument

## Contents

1. [The last step from balance to a lift](#1-the-last-step-from-balance-to-a-lift)
   - [What balance gives and what it does not give](#11-what-balance-gives-and-what-it-does-not-give)
   - [The finite scalar fibre as the missing bridge](#12-the-finite-scalar-fibre-as-the-missing-bridge)
   - [The theorem and its precise scope](#13-the-theorem-and-its-precise-scope)
   - [Logical order of the proof](#14-logical-order-of-the-proof)
2. [The hardly-ramified deformation problem](#2-the-hardly-ramified-deformation-problem)
   - [Coefficients and residual representation](#21-coefficients-and-residual-representation)
   - [The condition at two](#22-the-condition-at-two)
   - [The finite-flat condition at the coefficient prime](#23-the-finite-flat-condition-at-the-coefficient-prime)
   - [The global functor and universal representation](#24-the-global-functor-and-universal-representation)
   - [Coefficient extension](#25-coefficient-extension)
   - [Finite flatness rules out the cyclotomic-dihedral branch](#26-finite-flatness-rules-out-the-cyclotomic-dihedral-branch)
3. [Supported balance and the relation bound](#3-supported-balance-and-the-relation-bound)
   - [The tangent and dual Selmer structures](#31-the-tangent-and-dual-selmer-structures)
   - [Why the local corrections cancel](#32-why-the-local-corrections-cancel)
   - [Supported obstructions](#33-supported-obstructions)
   - [Relations inject into supported degree two](#34-relations-inject-into-supported-degree-two)
   - [The balanced presentation](#35-the-balanced-presentation)
4. [The automorphic finiteness witness](#4-the-automorphic-finiteness-witness)
   - [Why residual potential modularity is not enough](#41-why-residual-potential-modularity-is-not-enough)
   - [Choosing the totally real field](#42-choosing-the-totally-real-field)
   - [Preservation of the local problem](#43-preservation-of-the-local-problem)
   - [Image and adequacy after restriction](#44-image-and-adequacy-after-restriction)
   - [The restricted modularity-lifting ring](#45-the-restricted-modularity-lifting-ring)
5. [Finite image on the scalar fibre](#5-finite-image-on-the-scalar-fibre)
   - [Restriction of the universal scalar-fibre representation](#51-restriction-of-the-universal-scalar-fibre-representation)
   - [Factorization through a finite ring](#52-factorization-through-a-finite-ring)
   - [From the subgroup image to the full image](#53-from-the-subgroup-image-to-the-full-image)
   - [What has and has not been proved](#54-what-has-and-has-not-been-proved)
6. [Trace descent and scalar-fibre factorization](#6-trace-descent-and-scalar-fibre-factorization)
   - [The closed trace ring](#61-the-closed-trace-ring)
   - [Why the trace ring is finite](#62-why-the-trace-ring-is-finite)
   - [Carayol descent](#63-carayol-descent)
   - [Universality forces equality with the trace ring](#64-universality-forces-equality-with-the-trace-ring)
   - [The scalar-fibre finiteness theorem](#65-the-scalar-fibre-finiteness-theorem)
7. [Topological Nakayama and finiteness over the coefficient ring](#7-topological-nakayama-and-finiteness-over-the-coefficient-ring)
   - [A complete-module Nakayama lemma](#71-a-complete-module-nakayama-lemma)
   - [Application to the universal ring](#72-application-to-the-universal-ring)
   - [Why ordinary Nakayama is not enough by itself](#73-why-ordinary-nakayama-is-not-enough-by-itself)
8. [Balanced finite algebras are flat complete intersections](#8-balanced-finite-algebras-are-flat-complete-intersections)
   - [The dimension lower bound](#81-the-dimension-lower-bound)
   - [The uniformizer cannot be nilpotent](#82-the-uniformizer-cannot-be-nilpotent)
   - [Injectivity of the coefficient map](#83-injectivity-of-the-coefficient-map)
   - [The balanced finite criterion](#84-the-balanced-finite-criterion)
   - [Consequences for the universal ring](#85-consequences-for-the-universal-ring)
9. [Horizontal minimal primes and normalization](#9-horizontal-minimal-primes-and-normalization)
   - [Choosing a horizontal component](#91-choosing-a-horizontal-component)
   - [The domain quotient](#92-the-domain-quotient)
   - [Finiteness of normalization](#93-finiteness-of-normalization)
   - [A coefficient DVR and a characteristic-zero point](#94-a-coefficient-dvr-and-a-characteristic-zero-point)
10. [The extracted hardly-ramified lift](#10-the-extracted-hardly-ramified-lift)
   - [Construction of the representation](#101-construction-of-the-representation)
   - [Reduction and determinant](#102-reduction-and-determinant)
   - [Ramification and the condition at two](#103-ramification-and-the-condition-at-two)
   - [Finite flatness at the coefficient prime](#104-finite-flatness-at-the-coefficient-prime)
   - [The final existence theorem](#105-the-final-existence-theorem)
11. [Failure diagnostics and forbidden shortcuts](#11-failure-diagnostics-and-forbidden-shortcuts)
   - [Potential modularity is not automorphy of the universal family](#111-potential-modularity-is-not-automorphy-of-the-universal-family)
   - [Balance alone does not imply finiteness](#112-balance-alone-does-not-imply-finiteness)
   - [Finite image alone does not make matrix entries finite](#113-finite-image-alone-does-not-make-matrix-entries-finite)
   - [Faithfulness is not assumed](#114-faithfulness-is-not-assumed)
   - [Normalization does not precede the horizontal component](#115-normalization-does-not-precede-the-horizontal-component)
12. [Exceptional primes and the dihedral boundary](#12-exceptional-primes-and-the-dihedral-boundary)
   - [Characteristics two and three](#121-characteristics-two-and-three)
   - [Characteristic five](#122-characteristic-five)
   - [Why cyclotomic failure cannot occur](#123-why-cyclotomic-failure-cannot-occur)
   - [Why character lifting does not provide an alternative](#124-why-character-lifting-does-not-provide-an-alternative)
13. [Dependency, hypothesis, and normalization audit](#13-dependency-hypothesis-and-normalization-audit)
   - [Direct prerequisite ledger](#131-direct-prerequisite-ledger)
   - [Hypothesis matching](#132-hypothesis-matching)
   - [Circularity audit](#133-circularity-audit)
   - [Normalization and notation audit](#134-normalization-and-notation-audit)
14. [Conclusion](#14-conclusion)

## 1. The last step from balance to a lift

### 1.1 What balance gives and what it does not give

Let $\ell\geq 7$, let $\mathcal O$ be the ring of integers in a finite extension of $\mathbf Q_\ell$, let $\varpi$ be a uniformizer, and let $k$ be the finite residue field. The hardly-ramified deformation problem begins with an absolutely irreducible representation

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k)
$$

of determinant $\bar\chi_\ell$, unramified outside $\{2,\ell\}$, having one rigid tame-quadratic type at $2$ and a coefficient-linear finite-flat model at $\ell$. Books 182--184 construct its universal fixed-determinant deformation ring and prove that it admits a presentation

$$
R_{\mathrm{hr}}
\simeq
\mathcal O[[X_1,\ldots,X_t]]/(f_1,\ldots,f_r)
\qquad\text{with}\qquad r\leq t.
\tag{1.1}
$$

This is the balanced presentation. It is already a strong theorem. The $t$ variables are not guessed from a global Euler characteristic: they form the actual tangent space of the represented deformation problem. The $r$ relations are not bounded by an ambient cohomology group through a dimension slogan: their dual injects into the supported obstruction group after all local correction torsors have been included.

Yet (1.1) does not itself produce a characteristic-zero point. The example

$$
k[[X]]
$$

is balanced when regarded as a quotient of $\mathcal O[[X]]$ by the single relation $\varpi$, but it has no characteristic-zero point. At the opposite extreme, the power-series ring $\mathcal O[[X]]$ is balanced and has many characteristic-zero points, but it is not finite over $\mathcal O$. Balance controls dimension; it does not decide whether the universal ring is vertical, finite, flat, reduced, or faithful on an automorphic module.

The task of this book is to add exactly the missing input and no more. We shall prove that the special fibre

$$
R_{\mathrm{hr}}/\varpi R_{\mathrm{hr}}
$$

is finite over $k$. Topological Nakayama will then make $R_{\mathrm{hr}}$ finite over $\mathcal O$. The balanced relation bound will rule out a vertical ring and force flat complete-intersection structure. A horizontal minimal prime and its normalization will finally give a coefficient discrete valuation ring and a characteristic-zero hardly-ramified representation.

### 1.2 The finite scalar fibre as the missing bridge

Write

$$
A=R_{\mathrm{hr}}/\varpi R_{\mathrm{hr}}
$$

and let

$$
\rho_A:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(A)
\tag{1.2}
$$

be the universal representation after scalar reduction. There are two logically separate claims.

First, the image of (1.2) is finite. This is proved by restricting to a finite totally real field $F$ on which the residual representation is modular and on which the restricted deformation problem lies in the exact finite-flat modularity-lifting range. The restricted representation then factors through the special fibre of a finite Hecke algebra. Because $G_F$ has finite index in $G_{\mathbf Q}$, finiteness of the restricted image implies finiteness of the full image.

Second, finite image must be converted into finiteness of the coefficient ring $A$. Matrix entries need not be generated by traces in an arbitrary reducible family, and a finite subgroup can contain unipotent matrices whose entries involve apparently free nilpotent parameters. Absolute irreducibility of the residual representation is decisive here. Carayol descent conjugates (1.2) into its closed trace ring. The universal property then shows that the inclusion of the trace ring into $A$ has a retraction whose composite is the identity on $A$. Hence the trace ring is all of $A$.

This is the spine of the argument:

$$
\begin{array}{c}
\text{residual modularity over }F
\\ \Downarrow
\\
\rho_A|_{G_F}\text{ factors through a finite ring}
\\ \Downarrow
\\
\rho_A(G_{\mathbf Q})\text{ is finite}
\\ \Downarrow\ \text{Carayol descent and universality}
\\
A\text{ is a finite }k\text{-algebra}
\\ \Downarrow\ \text{topological Nakayama}
\\
R_{\mathrm{hr}}\text{ is finite over }\mathcal O
\\ \Downarrow\ \text{balance}
\\
R_{\mathrm{hr}}\text{ is finite flat and a complete intersection}
\\ \Downarrow\ \text{minimal prime and normalization}
\\
\text{a characteristic-zero hardly-ramified lift.}
\end{array}
\tag{1.3}
$$

Each downward arrow has its own hypotheses. None may be replaced by the conclusion of a later arrow.

### 1.3 The theorem and its precise scope

We isolate the extra hypothesis not contained in the local and Selmer calculations.

**Definition 1.1 (modularity-admissible hardly-ramified datum).** A residual representation $\bar\rho$ satisfying the six hardly-ramified hypotheses is called **modularity-admissible** if the following further conditions hold.

1. The residual datum, with its pairings and integral local models, belongs to the lifting-admissible two-prime range of the residual potential-modularity theorem of Book 170.
2. In the field-control theorem of Book 170, the places $2$ and $\ell$ are required to split completely and the output field is required to be disjoint from the joint residual and cyclotomic image field.
3. Over the resulting totally real field $F$, the fixed-determinant deformation problem obtained by restricting the hardly-ramified local conditions is an exact instance of the finite-flat fixed-type modularity-lifting theorem exported by Book 166: the residual automorphic localization, coefficient-prime conditions, named prime-to-$\ell$ types, integral type lattices, local--global compatibility, auxiliary-level exactness, support, reducedness, and trace-generation hypotheses all match.

The cyclotomic absolute irreducibility required by Books 170 and 166 is not an extra clause: Theorem 2.2 below proves it from the six hardly-ramified hypotheses. Clause 3 is intentionally exact. It does not say merely that some automorphic representation congruent to $\bar\rho|_{G_F}$ exists. It says that the universal restricted deformation ring through which $\rho_A|_{G_F}$ factors is identified with a finite flat faithful Hecke order.

**Theorem 1.2 (balanced hardly-ramified lift).** Let $\bar\rho$ be a modularity-admissible hardly-ramified datum. Then, after a finite extension $k'/k$, there exist a finite extension $E'/\operatorname{Frac}(\mathcal O)$ with ring of integers $\mathcal O'$, residue field $k'$, and a continuous representation

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\mathcal O')
\tag{1.4}
$$

such that:

1. $\rho\bmod\mathfrak m_{\mathcal O'}\simeq\bar\rho\otimes_k k'$;
2. $\det\rho=\chi_\ell$;
3. $\rho$ is unramified outside $\{2,\ell\}$;
4. at $2$, wild inertia is trivial and tame inertia has characteristic polynomial $T^2+T+1$, so the Artin conductor exponent is two; and
5. at $\ell$, every quotient of the selected lattice is coefficient-linearly finite flat of weight $\{0,1\}$.

Moreover $R_{\mathrm{hr}}$ is finite free over $\mathcal O$ and is a relative complete intersection. The representation (1.4) is obtained from a horizontal minimal prime of $R_{\mathrm{hr}}$ and the normalization of its domain quotient.

The residue extension is harmless and sometimes unavoidable: normalization of a horizontal component can have residue field strictly larger than $k$. The theorem lifts the prescribed residual representation after extension of scalars, not merely its semisimplification.

### 1.4 Logical order of the proof

The proof is organized to prevent four circles.

We do not use a characteristic-zero lift to prove residual potential modularity. Book 170 supplies residual modularity from a separate two-prime construction.

We do not use finiteness of $R_{\mathrm{hr}}$ to prove finiteness of its special fibre. The special fibre is controlled first by the restricted modularity-lifting ring.

We do not use flatness to invoke topological Nakayama. Finiteness over $\mathcal O$ is obtained before flatness. Flatness is deduced later from finiteness, balance, and injectivity of $\mathcal O\to R_{\mathrm{hr}}$.

We do not choose a characteristic-zero point before proving that a horizontal component exists. The component is forced by the dimension bound; normalization is performed only afterward.

## 2. The hardly-ramified deformation problem

### 2.1 Coefficients and residual representation

Fix a finite extension $E/\mathbf Q_\ell$ with ring of integers $\mathcal O$, uniformizer $\varpi$, and finite residue field $k$. Assume $\ell\geq7$. Let

$$
\bar\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(k)
\tag{2.1}
$$

be continuous and satisfy:

$$
\det\bar\rho=\bar\chi_\ell,
\qquad
\bar\rho\text{ is absolutely irreducible and odd},
\tag{2.2}
$$

and suppose that it is unramified outside $\{2,\ell\}$. Absolute irreducibility gives

$$
\operatorname{End}_{k[G_{\mathbf Q}]}(k^2)=k,
\tag{2.3}
$$

so strict-equivalence classes form a represented unframed global deformation problem. No analogous scalar-centralizer assertion is made locally at $\ell$; the local restriction may be a split sum of distinct characters.

Put

$$
S=\{2,\ell,\infty\},
\qquad
M=\operatorname{ad}^0\bar\rho,
\qquad
M'=M(1).
\tag{2.4}
$$

The trace pairing identifies $M^*(1)$ with $M'$ because $2$ is invertible in $k$.

### 2.2 The condition at two

Choose a tame inertia generator $\tau$ and arithmetic Frobenius $\phi$ at $2$, normalized by

$$
\phi\tau\phi^{-1}=\tau^2.
\tag{2.5}
$$

The residual restriction has trivial wild inertia and satisfies

$$
\bar\rho(\tau)^2+\bar\rho(\tau)+I=0.
\tag{2.6}
$$

The hardly-ramified condition imposes the same two equations on every lift:

$$
\rho(P_2)=1,
\qquad
\rho(\tau)^2+\rho(\tau)+I=0.
\tag{2.7}
$$

Because $T^2+T+1$ is separable for $\ell\ne3$, tame inertia has two distinct primitive cubic eigencharacters after scalar extension. Frobenius interchanges them. The unframed fixed-determinant local deformation ring is $\mathcal O$, its tangent space is zero, and its framed ring is a power-series ring in three frame variables.

The adjoint calculation is equally important. The trace-zero inertia invariants form a line on which arithmetic Frobenius acts by $-1$. After a Tate twist Frobenius acts by $-2$, which is not $1$ for $\ell\geq7$. Thus

$$
H^0(\mathbf Q_2,M)=H^1(\mathbf Q_2,M)
=H^0(\mathbf Q_2,M')=H^1(\mathbf Q_2,M')=0.
\tag{2.8}
$$

Local duality also gives $H^2(\mathbf Q_2,M)=0$. Every characteristic-zero representation satisfying (2.7) has Artin conductor exponent two. This is a fixed tame-quadratic type, not a Steinberg condition and not an inequality on conductors.

### 2.3 The finite-flat condition at the coefficient prime

At $\ell$, the residual representation is the generic fibre of a coefficient-linear finite locally free group scheme of rank $|k|^2$ over $\mathbf Z_\ell$. A lift over an Artinian $\mathcal O$-algebra is admitted only when it has compatible coefficient-linear finite-flat models on all Artinian quotients, with determinant $\chi_\ell$ and Hodge weights $\{0,1\}$.

Let

$$
h_\ell
=\dim_k\operatorname{End}_{k[G_{\mathbf Q_\ell}]}(k^2).
\tag{2.9}
$$

The finite-flat tangent space $L_\ell$ satisfies

$$
\dim_kL_\ell=h_\ell,
\qquad
\dim_kH^0(\mathbf Q_\ell,M)=h_\ell-1.
\tag{2.10}
$$

The framed local ring is formally smooth of relative dimension four. If $h_\ell=1$, the unframed local ring is $\mathcal O[[Z]]$. If the local representation splits as two distinct characters, then $h_\ell=2$ and a coarse unframed local universal ring is not inferred. The global problem remains represented because its global centralizer is scalar and the framed local condition is available.

The finite-flat local condition lifts through every small extension. This is intrinsic liftability inside the finite-flat category. It does not assert

$$
H^2(\mathbf Q_\ell,M)=0.
$$

That ambient group may be nonzero.

### 2.4 The global functor and universal representation

For a complete Noetherian local $\mathcal O$-algebra $B$ with residue field $k$, a hardly-ramified deformation is a strict-equivalence class of continuous lifts

$$
\rho_B:G_{\mathbf Q,S}\longrightarrow\operatorname{GL}_2(B)
$$

with determinant $\chi_\ell$, satisfying (2.7) at $2$ and the coefficient-linear finite-flat condition at $\ell$. The source group already imposes unramifiedness outside $\{2,\ell\}$.

This functor is represented by a complete Noetherian local ring $R_{\mathrm{hr}}$ with universal strict-equivalence class

$$
\rho^{\mathrm{univ}}:
G_{\mathbf Q,S}\longrightarrow
\operatorname{GL}_2(R_{\mathrm{hr}}).
\tag{2.11}
$$

The representing property has a consequence that will later be crucial. Two local homomorphisms

$$
f_1,f_2:R_{\mathrm{hr}}\longrightarrow B
$$

are equal if the corresponding $B$-valued deformations are strictly equivalent. This is stronger than equality of traces, but it rests on the scalar residual centralizer (2.3).

### 2.5 Coefficient extension

Let $\mathcal O'/\mathcal O$ be a finite extension with residue extension $k'/k$. The tame equations at $2$ commute with scalar extension. The coefficient-linear finite-flat condition at $\ell$ also commutes with the finite coefficient extensions in its established range. Consequently the global problem for $\bar\rho\otimes_k k'$ is obtained by the corresponding completed base change.

This fact has two uses. The potential-modularity and modularity-lifting constructions may enlarge coefficients to contain type values and Hecke eigenvalues. Later, normalization of a horizontal component may enlarge the residue field. Neither operation changes the ground field $\mathbf Q$, the primes $2$ and $\ell$, or the meaning of the local conditions.

### 2.6 Finite flatness rules out the cyclotomic-dihedral branch

The image theorem of Book 162 leaves one apparent exception to cyclotomic absolute irreducibility. The local condition at $\ell$ removes it. Because this point is needed before potential modularity is invoked, we prove the removal here rather than leaving it among the later diagnostics.

We first isolate the local calculation.

**Proposition 2.1 (the ramified-quadratic induction obstruction).** Let $\ell\geq7$, let $k$ be a finite field of characteristic $\ell$, and let

$$
\bar r:G_{\mathbf Q_\ell}\longrightarrow\operatorname{GL}_2(k)
\tag{2.12}
$$

be coefficient-linearly finite flat over $\mathbf Z_\ell$, of weights $\{0,1\}$ and determinant $\bar\chi_\ell$. Even after a finite extension of $k$, the representation $\bar r$ cannot have the form

$$
\operatorname{Ind}_{G_L}^{G_{\mathbf Q_\ell}}\bar\theta
\tag{2.13}
$$

for a ramified quadratic extension $L/\mathbf Q_\ell$ and a character $\bar\theta:G_L\to\overline k^\times$.

**Proof.** There are two independent descriptions of projective tame inertia.

The integral low-weight classification recalled in Book 182 attaches to $\bar r$ a rank-two divided filtered module with one Hodge line. Extend the residue coefficients so that its simple factors are defined. The generic-fibre calculation has exactly two possibilities. If the filtered Frobenius module has a stable line, the line and quotient have weights zero and one; up to unramified characters, their tame inertial characters are

$$
1,\qquad \omega,
\tag{2.14}
$$

where $\omega=\bar\chi_\ell|_{I_\ell}$. If it has no stable line, its two weights form one Frobenius orbit of length two. With $\omega_2$ a fundamental character of niveau two, the two tame characters are, again up to unramified factors,

$$
\omega_2,\qquad \omega_2^\ell.
\tag{2.15}
$$

Here is the short filtered-module verification. In the reducible case, strictness puts the unique Hodge line on exactly one rank-one factor. The weight-zero and weight-one atomic calculations give $1$ and $\omega$. In the irreducible case, divided Frobenius exchanges the two scalar lines. Reading the two successive weights around that orbit gives the exponents $1$ and $\ell$ modulo $\ell^2-1$. Exactness and scalar extension show that extensions do not alter the semisimplified tame characters. This is the low-weight inertial calculation obtained from the integral classification, not from rational Hodge--Tate labels.

Consequently the ratio of the two semisimplified tame characters has order

$$
\ell-1\quad\text{in (2.14)},
\qquad
\ell+1\quad\text{in (2.15)}.
\tag{2.16}
$$

Now suppose (2.13) held. The continuous image of $\bar\theta$ is finite, and every finite subgroup of $\overline k^\times$ has order prime to $\ell$; hence $\bar\theta$ kills wild inertia. Let $\tau$ be a tame inertia generator. Since $L/\mathbf Q_\ell$ is ramified quadratic, $\tau$ lies outside $G_L$ and $\tau^2$ lies in $G_L$. In the induced basis, $\bar r(\tau)$ is antidiagonal and its square is scalar. Its two eigenvalues therefore have ratio $-1$. Equivalently, the ratio of the two semisimplified tame characters is the ramified quadratic character and has order two.

For $\ell\geq7$, neither $\ell-1$ nor $\ell+1$ is two. This contradicts (2.16). The argument is unchanged by finite extension of $k$, since both the finite-flat model and the tame character ratios commute with coefficient extension. $\square$

The proposition eliminates precisely the quadratic field arising in the cyclotomic dichotomy.

**Theorem 2.2 (automatic cyclotomic absolute irreducibility).** Every residual representation satisfying the six hardly-ramified hypotheses of Book 182 has

$$
\bar\rho|_{G_{\mathbf Q(\zeta_\ell)}}
\quad\text{absolutely irreducible}.
\tag{2.17}
$$

**Proof.** Suppose the restriction were reducible. The cyclotomic Clifford theorem of Book 162 would give, after a finite coefficient extension,

$$
\bar\rho\simeq
\operatorname{Ind}_{G_K}^{G_{\mathbf Q}}\bar\theta,
\tag{2.18}
$$

where $K$ is the unique quadratic subfield of $\mathbf Q(\zeta_\ell)$. Its discriminant is

$$
\ell^*=(-1)^{(\ell-1)/2}\ell,
$$

so its unique completion at $\ell$ is a ramified quadratic extension of $\mathbf Q_\ell$. There is one double coset in the local Mackey decomposition, and restriction of (2.18) gives

$$
\bar\rho|_{G_{\mathbf Q_\ell}}
\simeq
\operatorname{Ind}_{G_{K_\ell}}^{G_{\mathbf Q_\ell}}
(\bar\theta|_{G_{K_\ell}}).
\tag{2.19}
$$

The left side is coefficient-linearly finite flat with determinant $\bar\chi_\ell$ by the hardly-ramified hypotheses. Proposition 2.1 forbids (2.19). Thus the reducible alternative in Book 162 cannot occur. $\square$

This is stronger than adequacy of the full residual image. It proves irreducibility on the cyclotomic subgroup itself, which is the exact image hypothesis used by Books 170 and 166. No characteristic-zero lift and no automorphy theorem has entered the proof.

## 3. Supported balance and the relation bound

### 3.1 The tangent and dual Selmer structures

The tangent structure on $M$ is

$$
L_2=0,
\qquad
L_\ell=H^1_{\mathrm{fl}}(\mathbf Q_\ell,M),
\qquad
L_\infty=0.
\tag{3.1}
$$

At every other finite place the implicit condition is unramified. The global tangent space is

$$
H^1_{\mathrm{hr}}(\mathbf Q,M)
=\ker\!\left(
H^1(G_{\mathbf Q,S},M)
\longrightarrow
\frac{H^1(\mathbf Q_2,M)}{L_2}
\oplus
\frac{H^1(\mathbf Q_\ell,M)}{L_\ell}
\right).
\tag{3.2}
$$

Let $L_v^\perp\subset H^1(\mathbf Q_v,M')$ be the exact local Tate orthogonal. The dual Selmer group is

$$
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')
=\ker\!\left(
H^1(G_{\mathbf Q,S},M')
\longrightarrow
\bigoplus_{v\in S}
\frac{H^1(\mathbf Q_v,M')}{L_v^\perp}
\right),
\tag{3.3}
$$

with the positive convention at the real place. The orthogonal is part of the definition. It is not replaced by a subspace having the expected dimension.

The supported mapping fibre retains the global cochain and its local nullhomotopies. Its first cohomology is (3.2), and supported duality gives

$$
H^2_{\mathrm{hr}}(\mathbf Q,M)
\simeq
H^1_{\mathrm{hr}^\perp}(\mathbf Q,M')^*.
\tag{3.4}
$$

### 3.2 Why the local corrections cancel

The Greenberg--Wiles correction at a place $v$ is

$$
c_v=\dim_kL_v-\dim_kH^0(\mathbf Q_v,M).
\tag{3.5}
$$

At $2$, both terms vanish by (2.8), so $c_2=0$. At $\ell$, equation (2.10) gives $c_\ell=1$. At infinity, oddness fixes the deformation class, while the trace-zero centralizer of complex conjugation has dimension one. Hence $c_\infty=-1$.

Global absolute irreducibility gives $H^0(\mathbf Q,M)=0$. A global class in $H^0(\mathbf Q,M')$ restricts to a class in $H^0(\mathbf Q_2,M')$, which is zero by (2.8); hence

$$
H^0(\mathbf Q,M')=0.
\tag{3.6}
$$

The global invariant terms vanish, and

$$
c_2+c_\ell+c_\infty=0+1-1=0.
\tag{3.7}
$$

Therefore

$$
\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M)
=
\dim_kH^1_{\mathrm{hr}^\perp}(\mathbf Q,M').
\tag{3.8}
$$

Combining (3.4) and (3.8) gives the supported balance

$$
\dim_kH^2_{\mathrm{hr}}(\mathbf Q,M)
=
\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M).
\tag{3.9}
$$

The calculation remains valid when the local restriction at $\ell$ splits as two distinct characters: both dimensions in (2.10) rise by one, so their difference remains one.

### 3.3 Supported obstructions

Consider a small extension of Artinian coefficient rings

$$
0\longrightarrow I\longrightarrow B'\longrightarrow B\longrightarrow0,
\qquad \mathfrak m_{B'}I=0.
\tag{3.10}
$$

Choose set-theoretic determinant-compatible lifts of the matrices of a $B$-valued deformation. Their failure to multiply defines a normalized factor-set cocycle with values in $M\otimes_k I$. At $2$ and $\ell$, local liftability supplies admissible local lifts. Comparing the global matrix lifts with those local lifts gives local $1$-cochains whose coboundaries are the restricted factor sets. The global cocycle together with these local nullhomotopies defines a supported class

$$
\operatorname{ob}(\rho_B,B')
\in H^2_{\mathrm{hr}}(\mathbf Q,M)\otimes_k I.
\tag{3.11}
$$

The class is independent of every choice. It vanishes if and only if the global deformation lifts with all local conditions preserved. The reverse implication uses the Poitou--Tate correction functional: local admissible lifts form torsors under the $L_v$, their mismatch pairs with dual Selmer classes, and global reciprocity says that a mismatch is globally correctable precisely when every such pairing vanishes.

Thus supported degree two is not merely a convenient upper bound. It is a complete obstruction receptacle for this deformation problem.

### 3.4 Relations inject into supported degree two

Choose a minimal presentation

$$
P=\mathcal O[[X_1,\ldots,X_t]]
\twoheadrightarrow R_{\mathrm{hr}},
\qquad J=\ker(P\to R_{\mathrm{hr}}),
\tag{3.12}
$$

where

$$
t=\dim_kH^1_{\mathrm{hr}}(\mathbf Q,M).
\tag{3.13}
$$

Let $\mathfrak n=(\varpi,X_1,\ldots,X_t)$ and put

$$
\operatorname{Rel}=J/\mathfrak nJ.
\tag{3.14}
$$

A functional $\lambda\in\operatorname{Rel}^*$ defines a small quotient of $P$ in which exactly the relation direction measured by $\lambda$ is retained. Pull the universal representation to that quotient and form its supported obstruction class. This gives a linear map

$$
\operatorname{Rel}^*
\longrightarrow H^2_{\mathrm{hr}}(\mathbf Q,M).
\tag{3.15}
$$

The map is injective. Indeed, if the supported class of a nonzero relation functional vanished, completeness of (3.11) would lift the universal deformation across the corresponding small extension. Universality would then give a section of the quotient that kills the chosen nonzero conormal functional, contradicting minimality of the relation direction.

Here is the small-extension argument in detail. Choose $\lambda\ne0$ in $\operatorname{Rel}^*$ and let

$$
J_\lambda=\ker\!\left(
J\longrightarrow J/\mathfrak nJ
\xrightarrow{\lambda}k
\right).
$$

Put $P_\lambda=P/J_\lambda$. The image $I_\lambda$ of $J$ in $P_\lambda$ is one-dimensional over $k$, is killed by the maximal ideal, and has square zero. Thus

$$
0\longrightarrow I_\lambda
\longrightarrow P_\lambda
\longrightarrow R_{\mathrm{hr}}
\longrightarrow0
\tag{3.15a}
$$

is a small extension in the pro-Artinian sense after reduction at any finite precision. Pull the universal representation over $R_{\mathrm{hr}}$ across (3.15a). Its obstruction is precisely the image of $\lambda$ under (3.15), because changing the lift of a matrix coefficient changes the factor set by a supported coboundary and changing the generator of $I_\lambda$ scales both constructions by the same scalar.

Suppose this class were zero. At each finite precision the complete obstruction criterion would give a locally admissible lift to the corresponding quotient of $P_\lambda$. The lifts are torsors under finite tangent groups. Surjective transition maps and compactness let us choose a compatible inverse system, producing a deformation over $P_\lambda$. Universality gives a map

$$
s:R_{\mathrm{hr}}\longrightarrow P_\lambda
$$

whose composite with $P_\lambda\to R_{\mathrm{hr}}$ is the identity. On cotangent spaces, the quotient and section split the conormal sequence. But the class of $I_\lambda$ is, by construction, the nonzero functional $\lambda$ on the minimal conormal space. A split would make that conormal direction zero. This contradiction proves injectivity.

This proof also explains why an arbitrary obstruction space does not bound minimal relations. One needs a functorial obstruction class whose vanishing is equivalent to an actual lift preserving every local condition. The supported class has this completeness because the local nullhomotopies and the Poitou--Tate correction functional were built into it.

The variance matters. It is the dual relation space that injects into supported degree two:

$$
\operatorname{Rel}^*\hookrightarrow H^2_{\mathrm{hr}}.
\tag{3.16}
$$

Equivalently, after supported duality, the dual Selmer group surjects onto $\operatorname{Rel}$.

### 3.5 The balanced presentation

Let

$$
r=\dim_k\operatorname{Rel}.
$$

Equations (3.9) and (3.16) give

$$
r\leq\dim_kH^2_{\mathrm{hr}}
=\dim_kH^1_{\mathrm{hr}}=t.
\tag{3.17}
$$

Lifting a basis of $\operatorname{Rel}$ to $J$ and applying topological Nakayama to the finite $P$-module $J$ shows that these $r$ lifts generate $J$. Hence

$$
R_{\mathrm{hr}}
\simeq
\mathcal O[[X_1,\ldots,X_t]]/(f_1,\ldots,f_r),
\qquad r\leq t.
\tag{3.18}
$$

The elementary height inequality yields

$$
\dim R_{\mathrm{hr}}
\geq 1+t-r\geq1.
\tag{3.19}
$$

This lower bound will later rule out a vertical finite ring. At this stage no finiteness or flatness has been proved.

## 4. The automorphic finiteness witness

### 4.1 Why residual potential modularity is not enough

Residual potential modularity produces a finite totally real field $F$ and a parallel-weight-two cuspidal automorphic representation whose residual representation is $\bar\rho|_{G_F}$ after scalar extension. This establishes residual automorphy. It does not say that the $A$-valued representation $\rho_A|_{G_F}$ is automorphic, and it does not imply that the universal restricted deformation ring is finite.

To obtain a finite ring through which $\rho_A|_{G_F}$ factors, one needs an exact modularity-lifting theorem for the restricted deformation problem. Its local conditions must be represented, its residual automorphic form must occur in the correct localization, the image hypotheses must hold, and the integral patching theorem must identify the restricted universal deformation ring with a faithful Hecke order finite over $\mathcal O$.

This is why Definition 1.1 contains both Books 170 and 166. The first supplies the residual automorphic field and its control. The second supplies finiteness of the ring governing all deformations on the selected local tuple.

### 4.2 Choosing the totally real field

Apply the field-control form of residual potential modularity with the finite split set containing $2$ and $\ell$. Put into the avoidance field:

- the fixed field of $\ker\bar\rho$;
- the finite cyclotomic field needed to preserve the joint action on $M(1)$;
- the component and self-twist fields used by the modularity-lifting datum; and
- every finite auxiliary field whose intersection could shrink the residual image.

The resulting field $F$ is finite and totally real, and

$$
F\otimes_{\mathbf Q}\mathbf Q_2
\simeq\mathbf Q_2^{[F:\mathbf Q]},
\qquad
F\otimes_{\mathbf Q}\mathbf Q_\ell
\simeq\mathbf Q_\ell^{[F:\mathbf Q]}.
\tag{4.1}
$$

It is linearly disjoint from the chosen finite Galois avoidance field. The theorem does not need $F/\mathbf Q$ to be Galois or solvable. Its only group-theoretic use below is that $G_F$ is an open subgroup of finite index in $G_{\mathbf Q}$.

### 4.3 Preservation of the local problem

At every $w\mid2$, complete splitting identifies $F_w$ with $\mathbf Q_2$. Hence the equations (2.7), their rigid tangent calculation, and the tame-quadratic type are literally unchanged.

At every $w\mid\ell$, complete splitting identifies $F_w$ with $\mathbf Q_\ell$. Thus the coefficient-linear finite-flat category, determinant, Hodge range, and possible local centralizer are unchanged. No theorem about finite flatness over a ramified extension is required.

At a finite place $w\nmid2\ell$, the restriction of an unramified representation of $G_{\mathbf Q_p}$ to $G_{F_w}$ is unramified. Ramification of the number-field extension itself does not create inertia in the restricted representation: local inertia maps into the original inertia group, on which the representation is trivial.

Consequently every hardly-ramified deformation over $\mathbf Q$ restricts to the fixed-determinant deformation problem $\mathcal D_F$ having:

$$
\begin{array}{c|c}
w\mid2&\text{the same named tame-quadratic type},\\
w\mid\ell&\text{the same coefficient-linear finite-flat condition},\\
w\nmid2\ell&\text{unramified}.
\end{array}
\tag{4.2}
$$

The automorphic finiteness witness requires this exact tuple, not a tuple having merely equal conductor exponents.

### 4.4 Image and adequacy after restriction

Let $L/\mathbf Q$ be the finite Galois extension fixed by $\ker\bar\rho$. Since $F\cap L=\mathbf Q$, restriction gives

$$
\bar\rho(G_F)=\bar\rho(G_{\mathbf Q}).
\tag{4.3}
$$

Indeed, $\operatorname{Gal}(FL/F)\to\operatorname{Gal}(L/\mathbf Q)$ is an isomorphism, and $G_F$ surjects onto the left side. The same argument applied to the joint residual-cyclotomic representation preserves the relevant adjoint-twist invariants.

Theorem 2.2 proves that $\bar\rho|_{G_{\mathbf Q(\zeta_\ell)}}$ is absolutely irreducible. Since $\ell\geq7$, Book 162 therefore supplies adequacy. Equality of the matrix image after restriction preserves adequacy verbatim. Exceptional projective images $A_4$, $S_4$, and $A_5$ cause no additional exception in this range when their order is prime to $\ell$; the defining-characteristic large-image cases are adequate as well.

The vanishing

$$
H^0(F,\operatorname{ad}^0\bar\rho(1))=0
\tag{4.4}
$$

can also be seen locally: restriction to a place above $2$ injects global invariants into the zero group in (2.8). Thus the adjoint invariant required by the modularity-lifting ledger is checked without assuming it from adequacy.

### 4.5 The restricted modularity-lifting ring

Let $R_F$ be the universal fixed-determinant ring for the exact local tuple $\mathcal D_F$. By modularity-admissibility, residual potential modularity places $\bar\rho|_{G_F}$ in the correct non-Eisenstein parallel-weight-two localization, and the finite-flat fixed-type modularity-lifting theorem gives

$$
R_F\xrightarrow{\sim}\mathbb T_F,
\tag{4.5}
$$

where $\mathbb T_F$ is a faithful Hecke order finite flat over $\mathcal O$. In particular,

$$
R_F/\varpi R_F
\quad\text{is a finite-dimensional }k\text{-algebra}.
\tag{4.6}
$$

The patching theorem behind (4.5) keeps the coefficient-prime finite-flat quotients, the named tame types, the primary and companion type lattices, auxiliary diamond actions, determinant lines, and acting-image augmentation. Its role here is precisely (4.6). We do not reproduce its patching construction, and we do not use its conclusion for a local tuple different from (4.2).

It is useful to see why the conclusion is ring-theoretic rather than pointwise. At Taylor--Wiles level $Q_N$, the automorphic carrier is finite free over the diamond group algebra and carries a faithful image algebra $\mathbb T_{F,Q_N}$. The corresponding deformation ring $R_{F,Q_N}$ acts through a surjection

$$
R_{F,Q_N}\twoheadrightarrow\mathbb T_{F,Q_N}.
\tag{4.7}
$$

Finite marked quotients retain the local type actions, pairings, determinant, and both augmentation ideals. Passing to a compatible inverse system produces a patched deformation source, a patched deformation ring, and a patched Hecke image. The patched automorphic complex collapses to a finite free module over the regular auxiliary base. Component support and reducedness make the selected deformation source act faithfully. Thus the patched analogue of (4.7) is an isomorphism. Exact auxiliary augmentation descends the equality to finite level, giving (4.5).

Two consequences are essential for the present argument. First, the equality concerns the universal ring for the selected local tuple, so every coefficient algebra point of that ring factors through the Hecke order. Second, the Hecke order is finite over $\mathcal O$ because it is an image in the endomorphisms of a finite $\mathcal O$-module. Neither conclusion would follow from knowing only that every characteristic-zero irreducible component contains some automorphic point. A nilpotent kernel could survive pointwise tests, and a positive-dimensional formal direction could contain infinitely many automorphic points.

The exact augmentation hypotheses also prevent a different gap. If one patched cohomology after discarding the type complex, specialization could create

$$
\operatorname{Tor}_1
$$

and enlarge the acting kernel. The amplitude-collapse theorem proves flatness over the auxiliary and type parameters before augmentation. Hence the Hecke algebra in (4.5) is the faithful specialized image, not merely a quotient of an image constructed before specialization.

## 5. Finite image on the scalar fibre

### 5.1 Restriction of the universal scalar-fibre representation

Set

$$
A=R_{\mathrm{hr}}/\varpi R_{\mathrm{hr}}
$$

and reduce (2.11):

$$
\rho_A:G_{\mathbf Q,S}\longrightarrow\operatorname{GL}_2(A).
\tag{5.1}
$$

By Section 4.3, its restriction to $G_F$ belongs to $\mathcal D_F(A)$. The universal property of $R_F$ therefore gives a local homomorphism

$$
\alpha:R_F\longrightarrow A
\tag{5.2}
$$

such that the pushforward of the universal $R_F$-valued representation is strictly equivalent to $\rho_A|_{G_F}$. Since $A$ has characteristic $\ell$, the map factors through

$$
\bar\alpha:R_F/\varpi R_F\longrightarrow A.
\tag{5.3}
$$

No finiteness of $A$ has been used.

### 5.2 Factorization through a finite ring

Let

$$
B=\operatorname{im}(\bar\alpha)\subset A.
\tag{5.4}
$$

By (4.6), $B$ is a finite-dimensional $k$-algebra, hence a finite set. After a strict change of basis, the restricted representation takes values in

$$
\operatorname{GL}_2(B).
\tag{5.5}
$$

Therefore

$$
\rho_A(G_F)
$$

is finite. Notice the direction of the reasoning. The representation factors through a finite coefficient ring because the restricted universal deformation ring is finite. We have not argued that an arbitrary characteristic-$\ell$ lift of a modular residual representation is automorphic.

### 5.3 From the subgroup image to the full image

We use a general lemma.

**Lemma 5.1.** Let $G$ be a group, let $H\subset G$ have finite index, and let $r:G\to\Gamma$ be a homomorphism. If $r(H)$ is finite, then $r(G)$ is finite.

**Proof.** Choose right-coset representatives $g_1,\ldots,g_d$ for $H\backslash G$. Every $g\in G$ has the form $hg_i$, so

$$
r(G)\subseteq\bigcup_{i=1}^d r(H)r(g_i).
$$

The right side is a finite union of finite sets. $\square$

Apply the lemma with $G=G_{\mathbf Q}$ and $H=G_F$. Since $F/\mathbf Q$ is finite, $G_F$ is open of finite index. We obtain

$$
\boxed{\rho_A(G_{\mathbf Q})\text{ is finite}.}
\tag{5.6}
$$

Normality of $F/\mathbf Q$ is unnecessary.

### 5.4 What has and has not been proved

Equation (5.6) is a statement about the image group. It does not yet say that $A$ is finite-dimensional. A finite group can act through matrices over a large characteristic-$\ell$ ring, especially through unipotent elements of $\ell$-power order. For example, if $N^2=0$, then

$$
(I+xN)^\ell=I
$$

in characteristic $\ell$, even when $x$ lies in a large ring. Thus finite image cannot be converted into coefficient finiteness by inspecting orders of matrices.

The residual absolute irreducibility and the universal property are needed to eliminate these hidden coefficient directions. This is the purpose of trace descent.

## 6. Trace descent and scalar-fibre factorization

### 6.1 The closed trace ring

Let

$$
T\subseteq A
$$

be the closed $k$-subalgebra topologically generated by the traces

$$
\operatorname{tr}\rho_A(g),\qquad g\in G_{\mathbf Q}.
\tag{6.1}
$$

The determinant of $\rho_A$ is the reduction of the cyclotomic character, so

$$
\det\rho_A(g)\in k^\times.
\tag{6.2}
$$

The ring $T$ is a complete local pseudocompact $k$-algebra with residue field $k$. At this point it is merely a closed subring of $A$.

### 6.2 Why the trace ring is finite

Let $H=\rho_A(G_{\mathbf Q})$, which is finite by (5.6). For $2\times2$ invertible matrices one has

$$
\operatorname{tr}(X)\operatorname{tr}(Y)
=\operatorname{tr}(XY)+\det(Y)\operatorname{tr}(XY^{-1}).
\tag{6.3}
$$

To verify (6.3), use the Cayley--Hamilton identity

$$
Y+\det(Y)Y^{-1}=\operatorname{tr}(Y)I
$$

and multiply by $X$ before taking traces.

Let $V$ be the $k$-linear span in $A$ of

$$
\{\operatorname{tr}(h):h\in H\}.
$$

The set is finite, so $V$ is finite-dimensional. Equations (6.2) and (6.3) show that $V$ is closed under multiplication; it contains $1$ because $2$ is invertible and $\operatorname{tr}(I)=2$. Hence $V$ is a finite-dimensional $k$-subalgebra. It contains every trace and is contained in the trace algebra, so

$$
T=V.
\tag{6.4}
$$

In particular, $T$ is finite-dimensional over $k$ and is already closed.

### 6.3 Carayol descent

The ring $A$ is a complete Noetherian local $k$-algebra, hence a countable inverse limit of Artinian local rings. The group $G_{\mathbf Q,S}$ is compact, the representation $\rho_A$ is continuous, and its residual representation is absolutely irreducible. The hypotheses of Carayol descent therefore apply.

There exists

$$
u\in1+M_2(\mathfrak m_A)
$$

such that

$$
u\rho_Au^{-1}:
G_{\mathbf Q,S}\longrightarrow\operatorname{GL}_2(T).
\tag{6.5}
$$

No flatness of $A$ is required. The conjugator is strict, so (6.5) represents the same $A$-valued deformation after applying the inclusion

$$
i:T\hookrightarrow A.
\tag{6.6}
$$

The theorem descends matrix entries, not only characteristic polynomials. Absolute irreducibility is essential: without it, extension classes can vary while all traces remain fixed.

We recall the mechanism of the descent theorem because it clarifies every hypothesis. Choose elements $g_1,\ldots,g_4$ of the group whose residual matrices form a $k$-basis of $M_2(k)$. Such elements exist by the density theorem for an absolutely irreducible finite-dimensional representation. After replacing the list if necessary, the trace Gram matrix

$$
\mathcal G=
\bigl(\operatorname{tr}(\rho_A(g_i)\rho_A(g_j))\bigr)_{i,j}
\tag{6.5a}
$$

has determinant a unit: modulo the maximal ideal it is the nondegenerate trace pairing on $M_2(k)$. Every matrix $\rho_A(g)$ can therefore be expanded uniquely as

$$
\rho_A(g)=\sum_{i=1}^4 c_i(g)\rho_A(g_i),
\tag{6.5b}
$$

and Cramer's rule expresses each $c_i(g)$ using traces of products and the inverse of $\det\mathcal G$. Since traces of products are traces of group elements, all $c_i(g)$ lie in the closed trace ring $T$.

Let $\mathscr A_T$ be the $T$-span of the four matrices $\rho_A(g_i)$ inside $M_2(A)$. Equation (6.5b) shows that it contains the image of the group. Multiplication of basis matrices again has structure constants computed from trace pairings, so $\mathscr A_T$ is a rank-four $T$-algebra. Its reduction is $M_2(k)$, and the reduced trace pairing is perfect. Consequently $\mathscr A_T$ is an Azumaya algebra of degree two over the complete local ring $T$.

An Azumaya algebra over a complete local ring whose residue algebra is split is itself split. One proof lifts matrix units. Lift the two diagonal residual idempotents successively using Hensel's lemma for $X^2-X$; lift generators of the two off-diagonal rank-one bimodules; their products are units in the diagonal corners and can be rescaled to satisfy the matrix-unit relations. Completeness turns the compatible finite-level lifts into exact matrix units. Hence

$$
\mathscr A_T\simeq M_2(T).
\tag{6.5c}
$$

There are now two embeddings of the split algebra $\mathscr A_T$ into $M_2(A)$: the given one and the standard one supplied by (6.5c). The local Skolem--Noether theorem says they are conjugate. Reducing the conjugator modulo the maximal ideal gives a scalar because the residual representation has scalar centralizer. Multiplying by the inverse of that scalar and correcting successively through the nilpotent quotients makes the conjugator congruent to $1$. Passing to the inverse limit gives

$$
u\in1+M_2(\mathfrak m_A)
$$

and the descent (6.5).

This argument also shows why the closed topology matters. The conjugators and matrix units are first constructed modulo every open ideal. Completeness produces their limit, while separatedness makes the limiting identities exact. It also shows why no flatness is used: invertibility of the trace Gram determinant and Henselian lifting take place entirely in the local topology.

### 6.4 Universality forces equality with the trace ring

The $T$-valued deformation (6.5) gives, by universality of $R_{\mathrm{hr}}$, a local map

$$
f:R_{\mathrm{hr}}\longrightarrow T.
\tag{6.7}
$$

Because $T$ has characteristic $\ell$, this factors through a map

$$
\bar f:A\longrightarrow T.
\tag{6.8}
$$

Let $q:R_{\mathrm{hr}}\twoheadrightarrow A$ be scalar reduction. The two maps

$$
q,qquad i\circ f:R_{\mathrm{hr}}\longrightarrow A
$$

give strictly equivalent $A$-valued deformations: the first gives $\rho_A$, and the second gives its strict conjugate (6.5) followed by inclusion. Representability therefore implies

$$
i\circ f=q.
\tag{6.9}
$$

Factoring through $A$ yields

$$
i\circ\bar f=\operatorname{id}_A.
\tag{6.10}
$$

But $i$ is the inclusion of $T$ into $A$. Equation (6.10) says that every $a\in A$ equals the image of an element of $T$. Thus

$$
A=T.
\tag{6.11}
$$

This is the scalar-fibre factorization. Carayol descent supplies a ring of definition; universality proves that the universal coefficient ring has no elements outside it.

### 6.5 The scalar-fibre finiteness theorem

Combining (6.4) and (6.11) gives the central theorem.

**Theorem 6.1 (finite universal scalar fibre).** For a modularity-admissible hardly-ramified datum,

$$
\boxed{R_{\mathrm{hr}}/\varpi R_{\mathrm{hr}}
\text{ is a finite-dimensional }k\text{-algebra}.}
\tag{6.12}
$$

**Proof.** Restriction to the controlled totally real field and the finite restricted modularity-lifting ring give finite image by Chapter 5. The trace identity makes the closed trace ring finite-dimensional. Carayol descent makes the representation trace-ring-valued after strict conjugacy. The universal property gives the retraction (6.10), hence equality (6.11). $\square$

The theorem proves neither that the special fibre is reduced nor that it is a field. Nilpotents and several components can remain. Only its finite length is needed next.

## 7. Topological Nakayama and finiteness over the coefficient ring

### 7.1 A complete-module Nakayama lemma

We use the following form of topological Nakayama.

**Lemma 7.1.** Let $M$ be a separated and complete $\mathcal O$-module for the $\varpi$-adic topology. Suppose $M/\varpi M$ is finite-dimensional over $k$ and $M$ is a pseudocompact quotient of a finite product of complete Noetherian local modules. Then $M$ is finitely generated over $\mathcal O$.

**Proof.** Choose $m_1,\ldots,m_d\in M$ lifting a $k$-basis of $M/\varpi M$, and let

$$
\psi:\mathcal O^d\longrightarrow M
$$

send the standard basis to the $m_i$. Its image is compact and therefore closed. Modulo $\varpi$, the map is surjective, so

$$
M=\operatorname{im}\psi+\varpi M.
\tag{7.1}
$$

Iterating gives

$$
M=\operatorname{im}\psi+\varpi^nM
\qquad(n\geq1).
$$

For $m\in M$, choose $x_n\in\mathcal O^d$ with $m-\psi(x_n)\in\varpi^nM$. Successively modify $x_n$ so that $x_{n+1}\equiv x_n\pmod{\varpi^n}$. Completeness of $\mathcal O^d$ gives a limit $x$, continuity gives $m-\psi(x)\in\bigcap_n\varpi^nM=0$, and separatedness finishes the proof. $\square$

The compactness clause is automatic for the complete Noetherian local rings used here. It ensures that the finite span has closed image; without closedness, density modulo every finite quotient would not imply equality.

There is a useful quotient formulation. Let $N$ be the closed $\mathcal O$-submodule generated by the chosen lifts $m_i$. Surjectivity modulo $\varpi$ gives $M/N=\varpi(M/N)$. Because $M/N$ remains complete and separated, iteration gives

$$
M/N=\varpi^n(M/N)
$$

for every $n$. An element of $M/N$ therefore lies in every $\varpi^n(M/N)$ and is zero. Thus $M=N$. This is the topological replacement for applying the ordinary finite-module Nakayama lemma to $M/N$ before its finiteness is known.

### 7.2 Application to the universal ring

Apply Lemma 7.1 to $M=R_{\mathrm{hr}}$, regarded as an $\mathcal O$-module. Completeness and separatedness are part of the definition of the representing ring. Theorem 6.1 gives finite-dimensional reduction. Therefore

$$
\boxed{R_{\mathrm{hr}}\text{ is finite over }\mathcal O.}
\tag{7.2}
$$

This is the first finiteness statement about the original universal ring over $\mathbf Q$. It was not imported from the modularity-lifting theorem over $F$; only the finite scalar fibre was imported back through restriction and trace descent.

### 7.3 Why ordinary Nakayama is not enough by itself

The usual finite-module Nakayama lemma assumes in advance that the module is finitely generated. Here finite generation is the conclusion. The topological form uses completeness and closed image to pass from a finite set of residual generators to actual generators.

Nor may one argue that $R_{\mathrm{hr}}$ is generated as an $\mathcal O$-algebra by finitely many elements and hence is finite as a module. The power-series ring $\mathcal O[[X]]$ is topologically generated by one algebra element but has infinite $\mathcal O$-rank. The finite-dimensional special fibre is the additional input that turns topological algebra generation into module finiteness.

## 8. Balanced finite algebras are flat complete intersections

### 8.1 The dimension lower bound

Recall the presentation

$$
R_{\mathrm{hr}}
\simeq P/(f_1,\ldots,f_r),
\qquad
P=\mathcal O[[X_1,\ldots,X_t]],
\qquad r\leq t.
\tag{8.1}
$$

The regular local ring $P$ has dimension $1+t$. Krull's height theorem gives

$$
\operatorname{ht}(f_1,\ldots,f_r)\leq r,
$$

so

$$
\dim R_{\mathrm{hr}}
\geq1+t-r\geq1.
\tag{8.2}
$$

This is the only place where the inequality $r\leq t$ is needed to prove existence of a horizontal direction. It says nothing about which prime is horizontal until finiteness over $\mathcal O$ is also known.

### 8.2 The uniformizer cannot be nilpotent

Suppose $\varpi$ were nilpotent in $R_{\mathrm{hr}}$. Since the ring is finite over $\mathcal O$, it would be killed by some power $\varpi^n$ and would have finite length as an $\mathcal O$-module. A finite-length ring is Artinian and has Krull dimension zero, contradicting (8.2). Hence

$$
\varpi\text{ is not nilpotent in }R_{\mathrm{hr}}.
\tag{8.3}
$$

This conclusion is weaker than saying that $\varpi$ is a nonzerodivisor. The latter will follow from the balanced finite criterion.

### 8.3 Injectivity of the coefficient map

The kernel of the local homomorphism

$$
\mathcal O\longrightarrow R_{\mathrm{hr}}
\tag{8.4}
$$

is an ideal of the discrete valuation ring $\mathcal O$. If it is nonzero, it contains a power of $\varpi$, making $\varpi$ nilpotent in the target. Equation (8.3) therefore gives

$$
\mathcal O\hookrightarrow R_{\mathrm{hr}}.
\tag{8.5}
$$

Thus faithfulness of the coefficient action has been proved. It is not borrowed from a Hecke module and not assumed before finiteness.

### 8.4 The balanced finite criterion

We prove the commutative-algebra result in the form needed here.

**Proposition 8.1 (balanced finite criterion).** Let $\mathcal O$ be a complete discrete valuation ring and

$$
R=\mathcal O[[X_1,\ldots,X_g]]/(f_1,\ldots,f_s)
$$

be a nonzero complete local ring. Suppose $R$ is finite over $\mathcal O$, the structural map $\mathcal O\to R$ is injective, and $s\leq g$. Then $s=g$, the $f_i$ form a regular sequence, and $R$ is finite free over $\mathcal O$.

**Proof.** Since $R$ is finite and integral over the image of $\mathcal O$, every prime of $R$ contracts to a prime of $\mathcal O$, and

$$
\dim R=\dim\mathcal O=1.
\tag{8.6}
$$

The source $P=\mathcal O[[X_1,\ldots,X_g]]$ is regular local of dimension $g+1$. Hence the kernel $I=(f_1,\ldots,f_s)$ has height

$$
\operatorname{ht}I=(g+1)-1=g.
\tag{8.7}
$$

Krull's height theorem gives $g\leq s$, while the hypothesis gives $s\leq g$. Thus $s=g$.

A regular local ring is Cohen--Macaulay. An ideal of height $g$ generated by $g$ elements is generated by a regular sequence. Therefore $R=P/I$ is Cohen--Macaulay of dimension one. The injection $\mathcal O\hookrightarrow R$ makes $\varpi$ a parameter: because $R$ is finite over $\mathcal O$, the quotient $R/\varpi R$ has dimension zero. In a one-dimensional Cohen--Macaulay local ring every parameter is a nonzerodivisor. Hence multiplication by $\varpi$ on $R$ is injective.

Thus $R$ is torsion-free as an $\mathcal O$-module. It is already finite over the DVR, so it is finite free. $\square$

The proposition does not begin with faithfulness of an $R$-action on a patched module. Its injectivity hypothesis is the coefficient injectivity proved in Section 8.3.

### 8.5 Consequences for the universal ring

Apply Proposition 8.1 to (8.1), using (7.2), (8.5), and $r\leq t$. We conclude

$$
r=t,
\tag{8.8}
$$

the minimal relations form a regular sequence, and

$$
\boxed{R_{\mathrm{hr}}
\text{ is finite free over }\mathcal O
\text{ and a relative complete intersection}.}
\tag{8.9}
$$

In particular, $\varpi$ is a nonzerodivisor. Notice that equality $r=t$ is a conclusion of finiteness plus balance. It was not obtained from the equality of tangent and obstruction dimensions alone.

Finite flatness of the universal ring still does not itself choose a characteristic-zero field-valued point. The ring may have several components and nilpotents. We now isolate a domain component.

## 9. Horizontal minimal primes and normalization

### 9.1 Choosing a horizontal component

Because $R_{\mathrm{hr}}$ is finite flat over $\mathcal O$, $\varpi$ lies in no associated prime. Every minimal prime is associated in the Cohen--Macaulay ring $R_{\mathrm{hr}}$, so no minimal prime contains $\varpi$.

One can also see horizontality by contraction. The finite map $\mathcal O\to R_{\mathrm{hr}}$ is integral. The contraction of a minimal prime of $R_{\mathrm{hr}}$ is a minimal prime of $\mathcal O$, hence is $(0)$. Thus, for every minimal prime $\mathfrak p$,

$$
\mathfrak p\cap\mathcal O=(0).
\tag{9.1}
$$

Choose one minimal prime $\mathfrak p$.

### 9.2 The domain quotient

Put

$$
C=R_{\mathrm{hr}}/\mathfrak p.
\tag{9.2}
$$

Then $C$ is a complete local domain, finite over $\mathcal O$. Equation (9.1) makes it torsion-free over $\mathcal O$, hence finite free. Its fraction field

$$
L=\operatorname{Frac}(C)
$$

is a finite extension of $E=\operatorname{Frac}(\mathcal O)$. The composite

$$
R_{\mathrm{hr}}\twoheadrightarrow C\hookrightarrow L
\tag{9.3}
$$

already gives a characteristic-zero representation over a field. To obtain an integral lattice with a discrete valuation coefficient ring and controlled reduction, we pass to normalization.

### 9.3 Finiteness of normalization

Let $\widetilde C$ be the integral closure of $C$ in $L$. Since $C$ is finite over the complete discrete valuation ring $\mathcal O$, it is an excellent one-dimensional Noetherian domain. Its normalization is therefore finite:

$$
\widetilde C\text{ is a finite }C\text{-module}.
\tag{9.4}
$$

There is also a direct order-theoretic interpretation. The ring $C$ is an $\mathcal O$-order in the finite extension $L/E$. The integral closure of $\mathcal O$ in $L$ is finite over $\mathcal O$, and every element integral over $C$ is integral over $\mathcal O$. Hence $\widetilde C$ lies inside that finite $\mathcal O$-module and is itself finite.

The normalization can be semilocal. Choose a maximal ideal $\mathfrak n$ of $\widetilde C$ above the maximal ideal of $C$ and set

$$
\mathcal O'=\widetilde C_{\mathfrak n}.
\tag{9.5}
$$

We justify the order-theoretic finiteness more explicitly. Since $C$ is finite and torsion-free over $\mathcal O$, multiplication embeds $C$ into the $E$-vector space $L$ and makes $L$ finite-dimensional over $E$. Let $\mathcal O_L$ be the integral closure of $\mathcal O$ in $L$. The trace pairing on the separable field extension $L/E$ identifies the complementary module

$$
C^\vee=
\{x\in L:\operatorname{Tr}_{L/E}(xC)\subseteq\mathcal O\}
$$

as a finite $\mathcal O$-module containing every $C$-integral element after multiplication by one fixed discriminant denominator. Hence $\mathcal O_L$ is contained in a finite fractional $\mathcal O$-lattice. Being an $\mathcal O$-submodule of a finite free module over a Noetherian ring, it is finite. Since an element integral over $C$ is integral over $\mathcal O$, $\widetilde C\subseteq\mathcal O_L$ and is finite as well.

The separability used here is automatic: $E$ has characteristic zero. Thus no inseparable normalization phenomenon is hidden in the argument.

### 9.4 A coefficient DVR and a characteristic-zero point

The ring $\mathcal O'$ is a one-dimensional Noetherian normal local domain. Therefore it is a discrete valuation ring. It is finite over $\mathcal O$, its fraction field is $L$, and its residue field $k'$ is a finite extension of $k$.

The composite

$$
x:R_{\mathrm{hr}}longrightarrow C
\longrightarrow\widetilde C
\longrightarrow\mathcal O'
\tag{9.6}
$$

is local. Reducing it modulo the maximal ideal of $\mathcal O'$ gives the original residue map followed by $k\hookrightarrow k'$. Thus (9.6) is an integral characteristic-zero point lying over the prescribed residual point.

No claim that $R_{\mathrm{hr}}$ is reduced was needed. Passing to a minimal-prime quotient removes nilpotents on one horizontal component, and normalization then supplies a regular integral coefficient ring.

## 10. The extracted hardly-ramified lift

### 10.1 Construction of the representation

Push the universal representation (2.11) forward along (9.6):

$$
\rho_x=x\circ\rho^{\mathrm{univ}}:
G_{\mathbf Q,S}\longrightarrow\operatorname{GL}_2(\mathcal O').
\tag{10.1}
$$

Continuity follows because $x$ is continuous between finite complete local $\mathcal O$-algebras. The representation is genuinely integral; it is not obtained merely by semisimplifying a field-valued representation and then choosing an arbitrary lattice.

### 10.2 Reduction and determinant

Since $x$ is local and induces $k\hookrightarrow k'$ on residue fields,

$$
\rho_x\bmod\mathfrak m_{\mathcal O'}
\simeq\bar\rho\otimes_k k'.
\tag{10.2}
$$

The universal determinant is $\chi_\ell$, so

$$
\det\rho_x=\chi_\ell.
\tag{10.3}
$$

This equality is integral and holds on all of $G_{\mathbf Q}$, not only at unramified Frobenius elements.

### 10.3 Ramification and the condition at two

The universal representation factors through $G_{\mathbf Q,S}$, so $\rho_x$ is unramified outside $\{2,\ell\}$.

At $2$, the universal matrices satisfy

$$
\rho^{\mathrm{univ}}(P_2)=1,
\qquad
\rho^{\mathrm{univ}}(\tau)^2+\rho^{\mathrm{univ}}(\tau)+I=0.
$$

These polynomial identities survive every coefficient map, including (9.6). Thus $\rho_x$ has trivial wild inertia and the fixed tame-quadratic order-three inertia. The local classification of Book 182 gives the unramified-quadratic induced Weil form and Artin conductor exponent two.

No nonzero-monodromy assertion is inserted: this local type is finite tame dihedral, not special. Conversely, it would be too weak to say only that the conductor is at most two; the exact inertia polynomial is retained.

### 10.4 Finite flatness at the coefficient prime

The coefficient-prime local condition is represented as a closed condition stable under base change. The universal restriction at $\ell$ has compatible finite-flat models on every Artinian quotient. Pushing forward along

$$
R_{\mathrm{hr}}\longrightarrow\mathcal O'/\mathfrak m_{\mathcal O'}^n
$$

therefore gives a coefficient-linear finite locally free group scheme realizing

$$
\rho_x|_{G_{\mathbf Q_\ell}}\bmod\mathfrak m_{\mathcal O'}^n
$$

for every $n\geq1$. These models are compatible as $n$ varies. Hence the selected lattice is finite flat of weight $\{0,1\}$ in the integral sense.

This conclusion does not come from flatness of the global ring $R_{\mathrm{hr}}$ over $\mathcal O$. Global coefficient flatness and local finite flatness of a Galois representation are different notions. The former was proved in Chapter 8; the latter is inherited from the represented local deformation condition.

### 10.5 The final existence theorem

**Theorem 10.1 (characteristic-zero hardly-ramified lift).** Let $\ell\geq7$ and let $\bar\rho$ be a modularity-admissible hardly-ramified residual representation. Then the representation $\rho_x$ of (10.1) satisfies every conclusion of Theorem 1.2.

**Proof.** Chapters 4--6 prove that the special fibre of $R_{\mathrm{hr}}$ is finite. Chapter 7 proves that $R_{\mathrm{hr}}$ is finite over $\mathcal O$. Supported balance and the relation injection give the presentation (8.1); Chapters 8 and 9 produce the local homomorphism (9.6) into a finite coefficient DVR. Sections 10.1--10.4 verify reduction, determinant, ramification, the exact type at $2$, and coefficient-linear finite flatness at $\ell$. $\square$

The construction proves existence, not uniqueness. Different horizontal minimal primes can give nonisomorphic lifts. The universal ring records all of them and their congruences.

## 11. Failure diagnostics and forbidden shortcuts

### 11.1 Potential modularity is not automorphy of the universal family

Suppose $\bar\rho|_{G_F}$ is the reduction of an automorphic representation. This fact supplies a residual Hecke maximal ideal. It does not force a deformation

$$
G_F\to\operatorname{GL}_2(A)
$$

to factor through a finite Hecke algebra. The factorization requires an $R=T$ theorem for the exact determinant and local components containing that deformation.

In the proof above, the decisive statement is (4.5), not the bare residual automorphy statement. Omitting the integral type, local--global compatibility, support, or acting-order hypotheses would break (5.2)--(5.4).

### 11.2 Balance alone does not imply finiteness

The ring

$$
\mathcal O[[X]]
$$

has one tangent variable and no relation, so it satisfies the inequality $r\leq t$, but it is not finite over $\mathcal O$. The ring

$$
\mathcal O[[X]]/(\varpi)
$$

has one variable and one relation and is balanced, but it is vertical and has no characteristic-zero point.

The first example shows why scalar-fibre finiteness is needed. The second shows why the dimension lower bound must be combined with finiteness to prove that $\varpi$ is not nilpotent. Neither defect is repaired by calling the presentation balanced.

### 11.3 Finite image alone does not make matrix entries finite

In characteristic $\ell$, take a square-zero matrix $N$ and an arbitrary element $x$ of a large complete local ring. The matrix $I+xN$ has order dividing $\ell$. Thus a finite cyclic image can be written using a coefficient parameter that does not visibly lie in a finite subring.

For an absolutely irreducible residual family, Carayol descent removes this apparent freedom: after strict conjugacy all entries lie in the trace ring. Universality then proves that the coefficient parameter was not genuinely universal. Without residual absolute irreducibility, the trace ring can miss extension parameters and Chapter 6 fails.

### 11.4 Faithfulness is not assumed

There are two possible faithfulness statements in nearby arguments. A patched automorphic module can be faithful over a deformation source, and the coefficient ring $\mathcal O$ can act faithfully on $R_{\mathrm{hr}}$. Neither is assumed here for the global ring over $\mathbf Q$.

The modularity-lifting theorem over $F$ proves the faithful Hecke comparison needed to make $R_F$ finite. For $R_{\mathrm{hr}}$, injectivity of $\mathcal O\to R_{\mathrm{hr}}$ is proved only in Section 8.3, after scalar-fibre finiteness, topological Nakayama, and the dimension lower bound. Assuming it earlier would conceal the possibility of a vertical universal ring.

### 11.5 Normalization does not precede the horizontal component

Normalizing a ring annihilated by a power of $\varpi$ cannot create characteristic zero. Nor is normalization of a nonreduced ring defined by simply placing all its elements in one fraction field. The correct order is:

$$
R_{\mathrm{hr}}
\longrightarrow R_{\mathrm{hr}}/\mathfrak p
\longrightarrow\widetilde{R_{\mathrm{hr}}/\mathfrak p}
\longrightarrow\mathcal O'.
$$

The minimal prime $\mathfrak p$ is known to be horizontal before the domain quotient is formed. Only that domain has a fraction field in which normalization is taken.

## 12. Exceptional primes and the dihedral boundary

### 12.1 Characteristics two and three

At $\ell=2$, scalars do not split from trace-zero endomorphisms, determinant correction cannot divide by two, signs coincide, and real complete cohomology is no longer acyclic in the required way. The local deformation, supported duality, and relation-obstruction arguments all change.

At $\ell=3$, the polynomial

$$
T^2+T+1
$$

is inseparable. The tame order-three algebra is not etale, the two inertia characters coalesce, and the Frobenius eigenvalue $-2$ on the twisted adjoint invariant becomes $1$. The rigid local calculation (2.8) and the supported balance therefore fail in their stated form.

These are structural exclusions, not notational inconveniences.

### 12.2 Characteristic five

The local equalities at $2$ remain favorable in characteristic five: $2$ is invertible and $-2\ne1$. Nevertheless the unified hardly-ramified local package and the modularity-lifting package used here are stated for $\ell\geq7$.

There is also a genuine image boundary. In characteristic five, an icosahedral residual image can fail the adequacy conclusion needed by the Taylor--Wiles argument. Absolute irreducibility does not repair that failure. A characteristic-five version of Theorem 10.1 would require a separately verified local, image, and patching theorem.

### 12.3 Why cyclotomic failure cannot occur

Book 162 proves the sharp dichotomy. If $\bar\rho$ is absolutely irreducible but

$$
\bar\rho|_{G_{\mathbf Q(\zeta_\ell)}}
$$

is reducible, then $\bar\rho$ is induced from a character of the quadratic subfield

$$
K\subset\mathbf Q(\zeta_\ell).
\tag{12.1}
$$

At first sight this cyclotomic-dihedral alternative appears to be a genuine boundary. Theorem 2.2 shows that it is not a branch of the hardly-ramified problem at all. The field $K$ is ramified quadratic at $\ell$, so localizing the induction produces ramified-quadratic projective tame inertia of order two. Integral finite flatness of weights $\{0,1\}$ permits only the two tame ratios in (2.16), of orders $\ell-1$ and $\ell+1$. The contradiction occurs already in the residual local representation.

The condition at $2$ neither causes nor repairs this contradiction. If $2$ splits in $K$, local restriction of the global induction is a sum and cannot have the irreducible tame-quadratic type. If $2$ is inert, the completion is the unramified quadratic field and an order-three inducing character can indeed give the required local type. That compatibility at $2$ does not affect the ramified completion at $\ell$.

Thus the cyclotomic irreducibility used in Chapter 4 is a theorem from the six local and global residual hypotheses, not an added modularity assumption. Passing to the disjoint totally real field preserves it, and Books 170 and 166 may test their cyclotomic image hypotheses in the ordinary way.

### 12.4 Why character lifting does not provide an alternative

It is useful to examine the proposed character construction, because it identifies why a superficially natural repair would have been false even before Theorem 2.2 made it unnecessary.

Suppose hypothetically that (12.1) and a character $\bar\theta$ had survived the local test. Pointwise Teichmüller lifting would give a finite-order character

$$
\widetilde\theta:G_K\longrightarrow\mathcal O_1^\times
$$

after a finite unramified coefficient extension. It would preserve the exact prime-to-$\ell$ inertia at $2$, and the standard induced lattice would reduce to $\operatorname{Ind}\bar\theta$, not merely to its semisimplification. But

$$
\det\operatorname{Ind}_{G_K}^{G_{\mathbf Q}}\widetilde\theta
=\eta_{K/\mathbf Q}(\widetilde\theta\circ\operatorname{Ver})
\tag{12.2}
$$

has finite image. It cannot equal the cyclotomic character, which has infinite pro-$\ell$ image. This is the first failure of the finite-image lift. Taking a formal square root of the quotient of the two determinants does not solve it: such a half-cyclotomic character has nonintegral labeled weight and is not finite flat. A Teichmüller lift controls reduction and finite inertial type; it does not choose a Hodge type.

The weight-two alternative also fails locally. If $K$ is imaginary and the ray-unit and determinant compatibilities can be solved, Books 6 and 95 can construct an algebraic Hecke character $\psi$ of infinity type $(1,0)$ and Book 95 gives the cuspidal automorphic induction $\operatorname{AI}_{K/\mathbf Q}(\psi)$. If $K$ is real, that CM weight-two theorem is unavailable and the nonparallel rank-one infinity type is already incompatible with the positive-rank unit relations. In either signature the completion $K_\ell/\mathbf Q_\ell$ in (12.1) is ramified quadratic.

Let $\chi$ be any characteristic-zero local character of $G_{K_\ell}$ and put

$$
V=\operatorname{Ind}_{G_{K_\ell}}^{G_{\mathbf Q_\ell}}\chi.
$$

The induced model itself gives

$$
D_{\mathrm{cris},\mathbf Q_\ell}(V)
\simeq D_{\mathrm{cris},K_\ell}(\chi)
\tag{12.3}
$$

as vector spaces over the maximal unramified subfield of $K_\ell$. Because $K_\ell/\mathbf Q_\ell$ is totally ramified, that subfield is $\mathbf Q_\ell$. The right side has dimension at most one, whereas $V$ has dimension two. Hence $V$ is not crystalline, whatever the conductor or infinity type of $\chi$.

Indeed, realize the induction as functions on $G_{\mathbf Q_\ell}$ with the usual $G_{K_\ell}$-equivariance. After tensoring with the crystalline period ring, evaluation at the identity identifies the $G_{\mathbf Q_\ell}$-invariants with the $G_{K_\ell}$-invariants of the inducing line. This proves (12.3) directly and keeps track of the common maximal unramified coefficient field.

Compatible finite-flat quotients of weights $\{0,1\}$ would give a strongly divisible lattice and therefore a crystalline generic representation. Equation (12.3) proves that no induced characteristic-zero representation from this ramified quadratic field can satisfy the coefficient-prime condition. Automorphically the same failure appears as a ramified dihedral local parameter at $\ell$, with the discriminant contribution in the conductor formula. It is not a point of the finite-flat coefficient-prime deformation ring.

This obstruction is invariant under coefficient extension and coefficient descent. Enlarging a field of values can split eigencharacters and provide an integral induced lattice, but it neither changes the ramification index of $K_\ell/\mathbf Q_\ell$ nor increases the crystalline-period dimension in (12.3).

The prior theorems have exactly the expected boundaries. Books 5 and 6 globalize compatible rank-one characters but do not turn ramified induction into a finite-flat representation. Book 95 proves automorphic induction and its determinant and conductor formulas, not coefficient-prime level lowering. Book 174 obtains a finite-flat dihedral seed by requiring the coefficient prime to split in the CM field; here it is ramified. Books 166 and 170 require cyclotomic irreducibility rather than treating this bad-dihedral image. No allowed theorem supplies the proposed induced finite-flat source, because such a source cannot exist.

The scalar-fibre argument therefore needs no second factorization. Theorem 2.2 places every actual hardly-ramified residual datum in the cyclotomically irreducible image branch. For every datum satisfying the remaining realization and exact-patching clauses of Definition 1.1, Chapters 4--6 give the strict trace-ring factorization (6.10), and Chapters 7--10 finish the balanced lift without circular $R=T$ reasoning.

## 13. Dependency, hypothesis, and normalization audit

### 13.1 Direct prerequisite ledger

| Book | Result used | Hypotheses retained | Exact role |
|---|---|---|---|
| 62, *Coefficient Rings and Deformation Categories* | pseudocompact trace rings, closed images, topological Nakayama, strict universality conventions | complete separated local rings, finite residual quotients, closed finite spans | Chapters 6 and 7 |
| 63, *Carayol Descent and Strict Conjugacy* | descent of an absolutely residually irreducible family to its closed trace ring | compact group, pro-Artinian local coefficient ring, scalar residual centralizer | Section 6.3 |
| 69, *Balanced Commutative Algebra* | height bound, balanced finite criterion, torsion-free equals flat over a DVR, finite normalization of orders | finite local algebra, injective coefficient map, no more relations than variables | Chapters 8 and 9 |
| 162, *Finite Subgroups, Dickson Classification, and Adequacy* | adequacy for cyclotomically irreducible rank-two images at $\ell\geq7$; classification of cyclotomic failure | absolute irreducibility, exact cyclotomic restriction, small-prime boundary | Theorem 2.2 and Sections 4.4 and 12.3 |
| 166, *One-Prime Nonminimal Patching and $R=T$* | finite-flat fixed-type $R=T$, faithful finite Hecke order, exact augmentation and coefficient extension | exact clean local tuple, residual automorphy, cyclotomic irreducibility supplied by Theorem 2.2, integral patching and support ledger | Equation (4.5) and scalar-fibre factorization after restriction |
| 170, *Potential Modularity of Two-Dimensional Representations* | residual potential modularity and field control | lifting-admissible two-prime datum, complete splitting, disjointness, exact coefficient and local models | construction of $F$ and residual automorphic localization |
| 182, *Local Conditions for Hardly-Ramified Minimal Deformations* | represented universal ring; integral low-weight classification; exact conditions, tangents, liftability, coefficient extension | six hardly-ramified hypotheses, $\ell\geq7$, actual coefficient-linear finite-flat model | Chapter 2 and inheritance in Chapter 10 |
| 183, *Supported Galois Cohomology and Selmer Calculations* | mapping fibre, supported duality, local ledger, zero Greenberg--Wiles correction | exact local tangent spaces and positive real convention | Sections 3.1--3.2 |
| 184, *Relation Obstructions and Poitou--Tate Corrections* | complete supported obstruction, correction torsors, relation injection | locally liftable conditions, exact orthogonals, global reciprocity | Sections 3.3--3.5 |

No theorem from a later book is used. In particular, no potential automorphy theorem for the characteristic-zero lift constructed here is assumed.

### 13.2 Hypothesis matching

The local condition at $2$ is a fixed prime-to-$\ell$ tame type. In the modularity-lifting application it must appear as that named type, with its integral lattice and local--global compatibility. It is not substituted for the selected Steinberg family appearing in a different one-prime theorem.

At places above $\ell$, complete splitting makes the local field exactly $\mathbf Q_\ell$. This matches the unramified low-weight finite-flat theorem. The possible split local residual representation is retained through framed local deformation theory; no local absolute irreducibility is added.

The potential-modularity theorem is used only for residual modularity and field control. The automorphy of an arbitrary deformation is supplied only by the matching $R=T$ theorem over $F$.

The adequacy theorem is invoked only after Theorem 2.2 proves cyclotomic absolute irreducibility from the finite-flat local condition. The adjoint-twist invariant is checked separately at the place above $2$.

Carayol descent is invoked only after global residual absolute irreducibility is known. The coefficient ring $A$ is complete Noetherian local and hence pro-Artinian; no flatness or reducedness is inserted.

The balanced finite criterion is invoked only after three independent facts are established: $R_{\mathrm{hr}}$ is finite over $\mathcal O$, $\mathcal O\to R_{\mathrm{hr}}$ is injective, and $r\leq t$.

### 13.3 Circularity audit

The proof order is:

1. local theory represents $R_{\mathrm{hr}}$;
2. the local low-weight calculation eliminates ramified quadratic induction and proves cyclotomic absolute irreducibility;
3. supported duality and relation obstructions prove $r\leq t$;
4. residual potential modularity chooses $F$ without using a characteristic-zero lift of $\bar\rho$;
5. modularity lifting over $F$ makes the restricted universal special-fibre representation factor through a finite ring;
6. finite index gives finite full image;
7. Carayol descent and universality prove that the special fibre itself is finite;
8. topological Nakayama proves finiteness over $\mathcal O$;
9. balance rules out a vertical ring and proves flat complete-intersection structure;
10. a minimal prime and normalization give the characteristic-zero lift.

No step assumes potential automorphy of the lift, finite image of the universal family, faithfulness of $R_{\mathrm{hr}}$, finiteness of $R_{\mathrm{hr}}$, or flatness of $R_{\mathrm{hr}}$ before that conclusion has been proved.

### 13.4 Normalization and notation audit

The local relation at $2$ uses arithmetic Frobenius and the exponent $2$ in (2.5). The determinant is the covariant cyclotomic character $\chi_\ell$. The fixed tame inertia polynomial is $T^2+T+1$ and gives conductor exponent two.

The symbol $A$ always denotes the scalar fibre $R_{\mathrm{hr}}/\varpi$. The symbol $B$ denotes the finite image of the restricted modularity-lifting ring in $A$. The symbol $T$ denotes the closed trace ring. These rings are not identified until the corresponding proofs: $B$ need not equal $A$, while $T=A$ follows only from Carayol descent and universality.

The finite flatness of $R_{\mathrm{hr}}$ over $\mathcal O$ is a commutative-algebra conclusion. The finite flatness of $\rho_x$ at $\ell$ is a local integral Galois condition. Their identical adjective does not make either imply the other.

The normalization is taken after quotienting by a horizontal minimal prime. The residue field may enlarge from $k$ to $k'$, and the final residual identification is stated after scalar extension.

## 14. Conclusion

The hardly-ramified deformation problem has one permitted tame type at $2$, one integral finite-flat condition at $\ell$, and no ramification elsewhere. Its local deformation theory is smooth in the relevant constrained sense, but its global deformation ring can still have relations. Supported cohomology records exactly those global obstructions together with their local nullhomotopies. Rigidity at $2$, the one normalized finite-flat direction at $\ell$, and oddness at infinity make the tangent and supported obstruction dimensions equal. The factor-set construction then injects the dual relation module into supported degree two and gives a presentation with no more relations than variables.

Balance is only half of the lift argument. The other half is the finite scalar fibre. Residual potential modularity supplies a totally real field split at $2$ and $\ell$ and disjoint from the residual image fields. On the exact restricted local tuple, modularity lifting identifies the restricted universal deformation ring with a finite Hecke order. The universal scalar-fibre representation therefore has finite image on $G_F$, and hence on $G_{\mathbf Q}$.

Finite image is converted into coefficient finiteness without assuming faithfulness or reducedness. The rank-two trace identity makes the trace algebra finite-dimensional. Carayol descent conjugates the family into that trace algebra. The universal property forces the scalar fibre to equal its trace ring. Topological Nakayama then makes the full universal ring finite over $\mathcal O$.

Only at this point does balance become a flatness theorem. The dimension lower bound prevents the uniformizer from being nilpotent, so the coefficient map is injective. The balanced finite criterion forces equality of generators and relations, a regular sequence, and finite freeness over $\mathcal O$. Every minimal component is horizontal. Quotienting by one minimal prime and normalizing produces a finite coefficient discrete valuation ring and a local characteristic-zero point.

Specializing the universal representation at that point gives

$$
\rho:G_{\mathbf Q}\longrightarrow\operatorname{GL}_2(\mathcal O')
$$

with cyclotomic determinant, exact tame-quadratic conductor-two type at $2$, compatible coefficient-linear finite-flat quotients at $\ell$, and no other ramification. Its reduction is the prescribed residual representation after a finite scalar extension.

The construction is complete for modularity-admissible data. Cyclotomic absolute irreducibility is not an extra part of that admissibility: a cyclotomic-dihedral residual representation would localize at $\ell$ to ramified quadratic induction, whose projective tame inertia is incompatible with the integral weight-$\{0,1\}$ classification. Finite-order Teichmüller induction has the wrong determinant, while algebraic weight-two induction from the ramified quadratic completion is not crystalline. Thus there is no omitted dihedral source and no unproved factorization for such a source. Subject only to the explicit two-prime realization and exact-patching clauses in Definition 1.1, every step from supported balance to the characteristic-zero hardly-ramified lift is closed by the preceding argument.
