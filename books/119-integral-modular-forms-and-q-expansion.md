# Integral Modular Forms and q-Expansion

## Contents

1. [From functions of a variable to sections on a moduli curve](#1-from-functions-of-a-variable-to-sections-on-a-moduli-curve)
   - [The three problems an integral definition must solve](#11-the-three-problems-an-integral-definition-must-solve)
   - [The compactified modular setting](#12-the-compactified-modular-setting)
   - [Conventions on weights, cusps, and coefficients](#13-conventions-on-weights-cusps-and-coefficients)
   - [The logical boundary of the book](#14-the-logical-boundary-of-the-book)
2. [The Hodge line](#2-the-hodge-line)
   - [Invariant differentials and changes of frame](#21-invariant-differentials-and-changes-of-frame)
   - [Extension over generalized elliptic curves](#22-extension-over-generalized-elliptic-curves)
   - [The geometric and rule-valued definitions](#23-the-geometric-and-rule-valued-definitions)
   - [Stabilizers and the necessity of the stack](#24-stabilizers-and-the-necessity-of-the-stack)
3. [Modules of integral modular forms](#3-modules-of-integral-modular-forms)
   - [Global sections and descent from a fine cover](#31-global-sections-and-descent-from-a-fine-cover)
   - [Finiteness and flat change of coefficients](#32-finiteness-and-flat-change-of-coefficients)
   - [Arbitrary base change and its obstruction](#33-arbitrary-base-change-and-its-obstruction)
   - [Products, grading, and vanishing in negative weight](#34-products-grading-and-vanishing-in-negative-weight)
4. [Tate frames and expansion maps](#4-tate-frames-and-expansion-maps)
   - [A framed cusp](#41-a-framed-cusp)
   - [Expansion in a root parameter](#42-expansion-in-a-root-parameter)
   - [Change of cusp frame](#43-change-of-cusp-frame)
   - [Expansions at nonrational and stacky cusps](#44-expansions-at-nonrational-and-stacky-cusps)
5. [The q-expansion principles](#5-the-q-expansion-principles)
   - [Why boundary series can determine a global section](#51-why-boundary-series-can-determine-a-global-section)
   - [Injectivity on a connected component](#52-injectivity-on-a-connected-component)
   - [Divisibility and descent of coefficients](#53-divisibility-and-descent-of-coefficients)
   - [The integral q-expansion lattice](#54-the-integral-q-expansion-lattice)
6. [The discriminant and concrete forms](#6-the-discriminant-and-concrete-forms)
   - [The discriminant as a Hodge section](#61-the-discriminant-as-a-hodge-section)
   - [Cusp width and the weighted discriminant divisor](#62-cusp-width-and-the-weighted-discriminant-divisor)
   - [The forms c4 and c6](#63-the-forms-c4-and-c6)
   - [Examples and normalization checks](#64-examples-and-normalization-checks)
7. [Cusp forms and boundary values](#7-cusp-forms-and-boundary-values)
   - [Vanishing on the reduced boundary](#71-vanishing-on-the-reduced-boundary)
   - [Constant terms at every cusp](#72-constant-terms-at-every-cusp)
   - [The boundary exact sequence](#73-the-boundary-exact-sequence)
   - [Saturation of the cusp-form lattice](#74-saturation-of-the-cusp-form-lattice)
8. [Kodaira--Spencer and dualizing forms](#8-kodaira--spencer-and-dualizing-forms)
   - [Why weight two is differential](#81-why-weight-two-is-differential)
   - [The logarithmic Kodaira--Spencer isomorphism](#82-the-logarithmic-kodaira--spencer-isomorphism)
   - [Weight-two cusp forms and regular dualizing differentials](#83-weight-two-cusp-forms-and-regular-dualizing-differentials)
   - [Residues and constant terms](#84-residues-and-constant-terms)
9. [Cohomology, base change, and integral lattices](#9-cohomology-base-change-and-integral-lattices)
   - [Duality calculations for powers of the Hodge line](#91-duality-calculations-for-powers-of-the-hodge-line)
   - [Stable base change in weights at least two](#92-stable-base-change-in-weights-at-least-two)
   - [Lattices over Dedekind domains](#93-lattices-over-dedekind-domains)
   - [Low weights and torsion warnings](#94-low-weights-and-torsion-warnings)
10. [Diamond operators and change of level](#10-diamond-operators-and-change-of-level)
    - [Changing a chosen generator](#101-changing-a-chosen-generator)
    - [Action on forms and expansions](#102-action-on-forms-and-expansions)
    - [Characters and nebentypus](#103-characters-and-nebentypus)
    - [Pullback and trace along a finite change of level](#104-pullback-and-trace-along-a-finite-change-of-level)
11. [Hecke correspondences away from the level](#11-hecke-correspondences-away-from-the-level)
    - [The moduli correspondence](#111-the-moduli-correspondence)
    - [Differentials through the universal isogeny](#112-differentials-through-the-universal-isogeny)
    - [The normalized Hecke operator](#113-the-normalized-hecke-operator)
    - [Preservation of cusp forms and integral lattices](#114-preservation-of-cusp-forms-and-integral-lattices)
12. [Hecke operators on q-expansions](#12-hecke-operators-on-q-expansions)
    - [The subgroups of a Tate curve](#121-the-subgroups-of-a-tate-curve)
    - [The prime-index formula](#122-the-prime-index-formula)
    - [Composite indices and Hecke relations](#123-composite-indices-and-hecke-relations)
    - [An integral extension without bad-level geometry](#124-an-integral-extension-without-bad-level-geometry)
13. [Sturm bounds as finite jet separation](#13-sturm-bounds-as-finite-jet-separation)
    - [The geometric bound](#131-the-geometric-bound)
    - [Degree of the Hodge line](#132-degree-of-the-hodge-line)
    - [Classical numerical bounds](#133-classical-numerical-bounds)
    - [Congruences and finite certification](#134-congruences-and-finite-certification)
14. [The integral q-expansion package](#14-the-integral-q-expansion-package)
    - [A dependency-closed theorem summary](#141-a-dependency-closed-theorem-summary)
    - [Hypotheses that cannot be suppressed](#142-hypotheses-that-cannot-be-suppressed)
    - [Conclusion](#143-conclusion)

## 1. From functions of a variable to sections on a moduli curve

### 1.1 The three problems an integral definition must solve

Over the complex numbers a modular form is first encountered as a holomorphic function on the upper half-plane satisfying a transformation law. That description is excellent for analysis, but it hides three arithmetic questions. What is a modular form over a ring in which no complex variable exists? What does it mean to reduce a form modulo a prime? Why should a power series at a cusp remember a global object?

The answer to the first question is that the transformation law is the gluing rule of a line bundle. An elliptic curve has a one-dimensional space of invariant differentials. Choosing a differential is choosing a frame; rescaling the frame produces precisely the weight factor. A modular form of weight $k$ is therefore a section of the $k$th power of the **Hodge line** on the moduli stack.

The answer to the second question requires properness. On the affine moduli curve, sections can acquire arbitrary poles at missing cusps. Book 117 constructed the compactified modular stack and its Cartier boundary. Extending the Hodge line over generalized elliptic curves makes integral forms into global sections on a proper relative curve. Proper coherent cohomology then gives finite modules and exact criteria for changing coefficients.

The answer to the third question uses the Tate curve. At a framed cusp, its invariant differential $du/u$ trivializes the Hodge line and its deformation parameter turns a section into a formal power series. A power series is local data, so it cannot determine a global section for purely formal reasons. It does so because every connected modular component meets the boundary and a section of a line bundle that vanishes on a nonempty formal neighborhood vanishes on a dense open and hence everywhere. The q-expansion principle is thus a theorem about proper curves, not a convention about series.

This book develops these answers as one continuous theory. Its endpoint is a finite method: sufficiently many initial coefficients determine a form and certify congruences. The bridge from infinitely long expansions to a finite test is divisor degree.

### 1.2 The compactified modular setting

Fix one of the level types

$$
\Gamma(N),\qquad \Gamma_1(N),\qquad \Gamma_0(N),
$$

with the ample Drinfeld meaning of Book 116. Let $B=B_\Gamma$ be the good-level base of Book 117: for point or cyclic level this is $\operatorname{Spec}\mathbf Z[1/N]$, and for symplectic full level it also includes the chosen cyclotomic coefficient ring. Write

$$
p:\mathcal X=\overline{\mathcal M}(\Gamma)\longrightarrow B
$$

for the proper compactified modular stack, $\mathcal Y=\mathcal M(\Gamma)$ for its smooth-elliptic open, and

$$
D=\mathcal X\setminus\mathcal Y
$$

for the reduced effective Cartier cusp divisor. The universal generalized elliptic curve on the stack is denoted

$$
\pi:\mathcal E\longrightarrow\mathcal X,
$$

with identity section $e$. All universal language belongs on $\mathcal X$. A universal curve need not descend to the coarse modular curve because its stabilizers can act nontrivially.

The results below also apply componentwise to a compactified modular stack obtained by a finite change of level, provided the following package holds:

- $\mathcal X$ is proper and flat of relative dimension one;
- every geometric connected component is reduced and meets $D$;
- the boundary is a relative effective Cartier divisor finite over the base;
- framed completed cusp charts are power-series discs carrying Tate generalized elliptic curves;
- the level order and every cusp width are invertible on the base.

Book 117 proves this package over $B_\Gamma$. Its fine covers are local on the arithmetic base: after a faithfully flat disjoint-union base change, one may choose projective fine curves $Y\to\mathcal X$ with finite change-of-level groups. Sections on $\mathcal X$ are equivariant sections on these curves, and the assertions below are checked there and descended. We never assume the existence of one auxiliary level that is invertible over all of $B_\Gamma$.

### 1.3 Conventions on weights, cusps, and coefficients

The Hodge line will be denoted by $\lambda$ rather than $\omega$, reserving $\omega_{\mathcal X/B}$ for the relative dualizing line of the modular curve. For an integer $k$, put

$$
M_k(\Gamma;R)=H^0(\mathcal X_R,\lambda_R^{\otimes k}),
\qquad \mathcal X_R=\mathcal X\times_B\operatorname{Spec}R,
$$

for a noetherian $B$-algebra $R$. Tensor powers with $k<0$ mean powers of the dual line. A **cusp form** is a section

$$
S_k(\Gamma;R)=H^0(\mathcal X_R,\lambda_R^{\otimes k}(-D_R)).
$$

The divisor $D$ is reduced. It must not be confused with the divisor of the discriminant. If a cusp has width $w$, the unlevelled Tate parameter is $q=t^w$, so the pulled-back discriminant vanishes to order $w$ in the local parameter $t$. We shall call

$$
W=\sum_c w_cD_c
$$

the **weighted cusp divisor**. The identity $\operatorname{div}(\Delta)=W$ is compatible with the definition of cusp forms, but $W$ and $D$ serve different purposes.

A phrase such as “at every cusp” includes every geometric cusp on every geometric connected component. Over a nonclosed coefficient field, a cusp may have a finite residue algebra and a nontrivial stabilizer. Expansions are first taken after a finite faithfully flat framing that chooses the Tate parameter and invariant differential; descent invariance is then imposed. This convention prevents a hidden rational-cusp assumption.

### 1.4 The logical boundary of the book

The integral Drinfeld moduli functors make sense at primes dividing the level, but Book 117 deliberately constructs its normal proper compactification only over the good-level base. This book uses exactly that construction. It does not assume regularity, semistable equations, or normalization at a removed level prime.

Hecke correspondences of auxiliary degree $m$ are first constructed where $m$ is invertible, because there Book 117 applies to the enlarged level. In positive weight, their q-expansion formulas preserve the lattice over the characteristic-zero Dedekind coefficient rings used below; the q-expansion principle then gives an integral operator without asserting an integral compactified correspondence in characteristic dividing $m$. This distinction will be explicit in Chapters 11 and 12.

The ordinary background used below consists of invariant differentials on elliptic curves, the elementary deformation theory of a smooth elliptic curve, and traces for finite locally free morphisms. Divisor degree, relative duality, cohomology and base change, generalized elliptic curves, Tate charts, compactified stacks, and coarse-space warnings are all supplied by Books 9, 15, 116, and 117 and are recalled when used.

## 2. The Hodge line

The weight of a modular form is invisible until an invariant differential is rescaled. This chapter isolates the line whose frames are invariant differentials, proves that it survives the polygonal boundary, and translates between global sections and Katz's rule-valued formulation.

### 2.1 Invariant differentials and changes of frame

Let $E\to S$ be an elliptic curve with identity $e$. Translation identifies every relative cotangent space with the cotangent space at the identity. More precisely, evaluation at the identity induces an isomorphism

$$
\pi^*e^*\Omega^1_{E/S}\xrightarrow{\sim}\Omega^1_{E/S}.
$$

The line

$$
\lambda_E=e^*\Omega^1_{E/S}
$$

is the line of invariant differentials. A frame $\eta$ of $\lambda_E$ pulls back to a nowhere-vanishing invariant differential on $E$. If $\eta'=u\eta$ for a unit $u$, then

$$
\eta^{\otimes k}=u^{-k}(\eta')^{\otimes k}. \tag{2.1}
$$

Thus a section $f$ of $\lambda_E^{\otimes k}$, written $f=F(E,\eta)\eta^{\otimes k}$, obeys

$$
F(E,u\eta)=u^{-k}F(E,\eta). \tag{2.2}
$$

The exponent and sign in (2.2) are forced by tensor algebra. Some analytic conventions put the inverse scaling into the chosen differential and therefore display the opposite-looking law. Throughout this book (2.2) fixes the normalization.

Formation of $\lambda_E$ commutes with arbitrary base change: smooth relative differentials do, and so does pullback by the identity. An isomorphism $\varphi:E\to E'$ induces

$$
\varphi^*:e'^*\Omega^1_{E'/S}\xrightarrow{\sim}e^*\Omega^1_{E/S}.
$$

Consequently the assignment $E\mapsto\lambda_E$ descends to a line bundle on the elliptic moduli stack.

### 2.2 Extension over generalized elliptic curves

For a generalized elliptic curve $E/S$, the identity still lies in the smooth locus. Define

$$
\lambda_E=e^*\Omega^1_{E^{\mathrm{sm}}/S}. \tag{2.3}
$$

This remains a line bundle and commutes with base change. The definition is not merely formal: it agrees with the dualizing differential of the complete genus-one curve.

**Proposition 2.1.** Let $\pi:E\to S$ be a generalized elliptic curve. There is a canonical isomorphism

$$
\pi_*\omega_{E/S}\xrightarrow{\sim}\lambda_E, \tag{2.4}
$$

where $\omega_{E/S}$ is the relative dualizing line. It is compatible with arbitrary base change and with translation.

**Proof.** Book 116 proves that generalized elliptic fibers are Gorenstein genus-one curves. Book 9 then makes $\omega_{E/S}$ invertible and base-change compatible, while relative duality makes $\pi_*\omega_{E/S}$ a line bundle. Restriction of a dualizing differential to the smooth locus and evaluation at $e$ gives the map (2.4).

It suffices to check it on geometric fibers. On a smooth elliptic curve, every regular differential is translation invariant and evaluation at the identity is an isomorphism between one-dimensional spaces. On a split $n$-gon, normalize into projective lines with coordinates $z_i$. A dualizing section is a tuple of meromorphic differentials with simple poles at the two branches of each node and opposite residues. The forms $dz_i/z_i$ glue around the cycle and span the global dualizing differentials. Their restriction to the identity component evaluates to the invariant toric differential $dz/z$. Hence the fiber map is nonzero between one-dimensional spaces and is an isomorphism. Base change and Nakayama's lemma give the relative result. Translation preserves $dz/z$ and hence the isomorphism. $\square$

This proposition explains why the Hodge line has no singular correction at a cusp. Ordinary differentials on the nodal curve are not locally free, but the invariant differential belongs to the dualizing line and has opposite residues on the two normalization branches.

### 2.3 The geometric and rule-valued definitions

The universal generalized elliptic curve on $\mathcal X$ gives the Hodge line

$$
\lambda=e^*\Omega^1_{\mathcal E^{\mathrm{sm}}/\mathcal X}.
$$

By definition, a geometric modular form of weight $k$ over $R$ is a section of $\lambda_R^{\otimes k}$. Katz's formulation describes the same object as a rule.

**Theorem 2.2.** Giving $f\in M_k(\Gamma;R)$ is equivalent to giving, for every $R$-algebra $A$ and every smooth elliptic curve with $\Gamma$-level $(E,\alpha)/A$ equipped with a frame $\eta$ of $\lambda_E$, an element

$$
F(E,\alpha,\eta)\in A
$$

such that:

1. $F$ is invariant under isomorphisms;
2. $F$ commutes with extension of $A$;
3. $F(E,\alpha,u\eta)=u^{-k}F(E,\alpha,\eta)$;
4. the rule extends regularly to every generalized elliptic family with ample level.

**Proof.** A section pulls back along the classifying map $\operatorname{Spec}A\to\mathcal X$. The frame $\eta$ identifies the pulled-back line with $A$, producing $F$. Functoriality of pullback gives the first two properties, (2.1) gives the third, and regularity on $\mathcal X$ gives the fourth.

Conversely, choose a faithfully flat atlas $U\to\mathcal X$ on which $\lambda$ is trivial. Evaluating the rule on the universal object and the chosen frame gives a function on $U$. Isomorphism invariance gives equality of its two pullbacks to $U\times_{\mathcal X}U$, with the weight factor exactly compensating for the change between the two frames. Faithfully flat descent therefore glues the local functions to a section of $\lambda^k$. The regular-extension clause ensures that the section lies on the compactification, not merely on the elliptic open. The constructions are inverse. $\square$

The fourth clause is essential. Without it, multiplying by an arbitrary negative power of the discriminant would give a rule on smooth elliptic curves with an uncontrolled cusp pole.

### 2.4 Stabilizers and the necessity of the stack

At a geometric object $(E,\alpha)$, an automorphism $g$ acts on the one-dimensional fiber $\lambda_{(E,\alpha)}$. A section on the stack must take a value fixed under this character. This produces genuine restrictions.

For the unlevelled stack, inversion acts on an invariant differential by

$$
[-1]^*\eta=-\eta.
$$

Hence it acts on $\lambda^k$ by $(-1)^k$. If multiplication by $2$ is injective on the coefficient module--in particular over a field of characteristic different from two--an odd-weight section on the unlevelled stack must vanish at every point with only generic inversion inertia; density then makes it zero. This is the geometric source of the absence of ordinary odd-weight level-one forms. In characteristic two the character becomes trivial, so a special-fiber section can exist without lifting; Chapter 9 will identify the accompanying base-change issue.

The same calculation gives the descent criterion to a coarse curve. If $\lambda^k$ were pulled back from a line on the coarse curve, every stabilizer would act trivially on its fiber. Conversely, on a tame quotient chart, Book 117 proves that trivial stabilizer characters suffice for descent. Thus modular forms are naturally stack sections even when a divisible power of the Hodge line happens to descend.

This distinction also protects the universal meaning of q-expansion. A framed cusp lives on a finite cover with a chosen parameter and differential. The stabilizer changes those frames. The expansion of a stack section is not an arbitrary series on the cover; it is an equivariant series whose transformation law records the weight.

## 3. Modules of integral modular forms

The geometric definition would have little arithmetic force if its section modules were uncontrolled. Properness makes them finite; descent makes them intrinsic; coherent base change explains exactly when reduction creates new forms.

### 3.1 Global sections and descent from a fine cover

Work on an arithmetic-base open admitting a projective fine cover $r:Y\to\mathcal X$ as in Book 117, with finite change-of-level group $G$, so that $\mathcal X\simeq[Y/G]$. The pullback $\lambda_Y=r^*\lambda$ is a genuine line bundle on a projective relative curve. Descent gives

$$
M_k(\Gamma;R)
=H^0(Y_R,\lambda_{Y,R}^k)^G. \tag{3.1}
$$

The equality is an equalizer, not an averaging formula. It remains valid when $|G|$ is not invertible. This matters at exceptional characteristics, where division by $|G|$ would be illegal.

Independence of the fine cover follows from the stack definition, but it is also visible directly. Two fine covers admit the common normalized refinement constructed in Book 117. Pulling an equivariant section to the refinement and imposing both descent data recovers the same section on the quotient stack.

Equation (3.1) lets every finiteness or base-change assertion be checked using the coherent theory of Book 15 on the proper scheme $Y$. The local conclusions agree on common refinements and descend along the faithfully flat cover of the arithmetic base, so they are global statements about $\mathcal X$. Equation (3.1) also shows why replacing the stack by its coarse curve can give the wrong module: the Hodge line on $Y$ may have a nontrivial stabilizer character and therefore no line-bundle descent to the coarse quotient.

### 3.2 Finiteness and flat change of coefficients

**Theorem 3.1.** For every integer $k$ and every noetherian $B$-algebra $R$, the module $M_k(\Gamma;R)$ is finite over $R$. If $R\to R'$ is flat, the natural map

$$
M_k(\Gamma;R)\otimes_RR'
\xrightarrow{\sim}M_k(\Gamma;R') \tag{3.2}
$$

is an isomorphism.

**Proof.** Proper finiteness from Book 15 makes $H^0(Y_R,\lambda_Y^k)$ a finite $R$-module. Its invariant submodule is the kernel of the finite collection of maps $g-1$, hence is finite because $R$ is noetherian. This proves finiteness.

For flat $R'$, coherent flat base change gives

$$
H^0(Y_R,\lambda_Y^k)\otimes_RR'
\simeq H^0(Y_{R'},\lambda_Y^k).
$$

Invariants are an equalizer, and flat tensor product preserves kernels. Taking $G$-invariants therefore commutes with the extension. Combining this with (3.1) proves (3.2). $\square$

Flatness in (3.2) includes localization and extension to a fraction field. It does not include reduction modulo a prime. Reduction is precisely where torsion in neighboring cohomology can create new sections.

### 3.3 Arbitrary base change and its obstruction

Let $L=\lambda_Y^k$. For a quotient $R\to R/I$ of Tor dimension at most one, the two-term curve complex of Book 15 gives

$$
0\longrightarrow H^0(Y,L)\otimes_RR/I
\longrightarrow H^0(Y_{R/I},L_{R/I})
\longrightarrow\operatorname{Tor}_1^R(H^1(Y,L),R/I)
\longrightarrow0. \tag{3.3}
$$

When invariants are exact, for example when $G$ is linearly reductive over $R$, taking invariants gives the corresponding exact obstruction sequence for modular forms. Without exact invariants there is a second possible obstruction, measured by the failure of invariants to commute with the quotient.

Thus the slogan “reduce the coefficients of a modular form” has two meanings:

- an existing integral form always has a reduction;
- not every form in the special fiber need lift.

The second assertion holds exactly when the relevant Tor and invariant obstructions vanish. In Chapters 8 and 9, duality will prove vanishing or local freeness in weights at least two under the standard good-level hypotheses. Weight one is genuinely more delicate.

For a DVR $R$ with uniformizer $\varpi$, (3.3) says that extra special-fiber sections are contributed by the $\varpi$-torsion in $H^1(Y,L)$. This is a structural statement, not a dimension-counting accident.

### 3.4 Products, grading, and vanishing in negative weight

Tensor product gives

$$
M_k(\Gamma;R)\times M_\ell(\Gamma;R)
\longrightarrow M_{k+\ell}(\Gamma;R).
$$

Hence

$$
M_*(\Gamma;R)=\bigoplus_{k\geq0}M_k(\Gamma;R)
$$

is a graded $R$-algebra. Its multiplication is compatible with every expansion map because multiplication of sections becomes multiplication of their coefficient series in a common Hodge frame.

Negative weights usually vanish, but positivity must be proved. The discriminant of Chapter 6 will show that a positive tensor power of $\lambda$ is the line of an effective boundary divisor meeting every connected component. On a proper curve this makes $\lambda$ positive on every component. A nonzero section of $\lambda^{-m}$ for $m>0$ would define an effective divisor of negative degree on some integral component, which is impossible. Therefore

$$
M_{-m}(\Gamma;K)=0\qquad(m>0) \tag{3.4}
$$

over every field $K$ on the good-level base. If the coefficient ring is reduced and flat over the base, fiberwise vanishing plus Nakayama gives the same result over the ring.

One should not infer (3.4) on an arbitrary nonflat nonreduced base solely from geometric points: a nilpotent section can vanish on every reduced fiber. The safe statement uses either coherent base change or the positivity argument on the actual relative curve.

## 4. Tate frames and expansion maps

A q-expansion is a section expressed in a very special local frame. The parameter and frame carry level labels, so both must be tracked before any coefficient principle can be correct.

### 4.1 A framed cusp

Let $c$ be a geometric cusp of $\mathcal X$. After a finite faithfully flat coefficient extension and the finite framing described in Books 116 and 117, the completed neighborhood of $c$ is

$$
\widehat{\mathcal U}_c=\operatorname{Spf}A_c[[t_c]]. \tag{4.1}
$$

The pulled-back universal generalized elliptic curve is a Tate model with unlevelled period

$$
q=t_c^{w_c}, \tag{4.2}
$$

where $w_c$ is the cusp width. Its multiplicative uniformizing coordinate $u$ supplies the invariant differential

$$
\eta_{\mathrm{Tate}}=\frac{du}{u}. \tag{4.3}
$$

Thus (4.3) trivializes $\lambda$ on the formal chart. A framed cusp means the combined choice of the coefficient extension, level labels, component orientation, parameter $t_c$, and Tate differential.

The parameter $t_c$ cuts out the reduced boundary. The unlevelled discriminant is $q$ times a unit and therefore has order $w_c$ in $t_c$. Since $w_c$ divides a level order inverted on $B$, it is a unit on the good-level base. This invertibility will be decisive for logarithmic Kodaira--Spencer.

### 4.2 Expansion in a root parameter

Let $f\in M_k(\Gamma;R)$. Pull it to the framed completion. There is a unique series

$$
f=F_c(t_c)\eta_{\mathrm{Tate}}^{\otimes k},
\qquad F_c(t_c)=\sum_{n\geq0}a_n(c,f)t_c^n \tag{4.4}
$$

with coefficients in $R\otimes_BA_c$. Define

$$
\operatorname{qexp}_c(f)=F_c(t_c). \tag{4.5}
$$

Although the notation says q-expansion, the honest uniformizer is $t_c=q^{1/w_c}$. Writing fractional powers of $q$ is shorthand for (4.4), not the choice of a branch in a field.

Regularity on the compactification is exactly the absence of negative powers of $t_c$. A weakly holomorphic rule on the elliptic open would instead give a Laurent series with a finite principal part. A cusp form will be characterized by $a_0(c,f)=0$ at every cusp.

Products satisfy

$$
\operatorname{qexp}_c(fg)
=\operatorname{qexp}_c(f)\operatorname{qexp}_c(g). \tag{4.6}
$$

Base change applies coefficientwise. These simple compatibilities are why formal expansions can detect algebraic operations after injectivity is proved.

### 4.3 Change of cusp frame

Suppose another frame uses $t'_c=v t_c+O(t_c^2)$ with $v\in A_c^\times$ and

$$
\eta'_{\mathrm{Tate}}=u\eta_{\mathrm{Tate}},
\qquad u\in A_c[[t_c]]^\times.
$$

If $f=F(t_c)\eta^k=F'(t'_c)(\eta')^k$, then

$$
F'(t'_c)=u^{-k}F(t_c(t'_c)). \tag{4.7}
$$

Thus the whole series depends on the frame, but the following data do not:

- whether the series is zero;
- whether its constant term is zero;
- its order of vanishing in the reduced boundary parameter;
- whether all coefficients lie in a subring stable under the frame change.

For the finite cusp framings used here, $u$ and the coefficients of the coordinate change are integral units. Consequently q-integrality is intrinsic after imposing all Galois and stabilizer compatibilities.

A root-of-unity change $t_c\mapsto\zeta t_c$ is especially common. It sends $a_n$ to $\zeta^{-n}a_n$, with the additional factor from the Hodge frame if that frame changes. The invariant series on an unframed stack chart is the subspace satisfying this combined character law.

### 4.4 Expansions at nonrational and stacky cusps

Let the completed stack chart be $[\operatorname{Spf}A_c[[t_c]]/H_c]$, where $H_c$ is the finite frame stabilizer. The group acts on the parameter, the coefficient algebra, and the Tate differential. If

$$
h(t_c)=\zeta_h t_c+O(t_c^2),
\qquad h^*\eta_{\mathrm{Tate}}=\chi_\lambda(h)\eta_{\mathrm{Tate}},
$$

then a weight-$k$ expansion satisfies

$$
h(F_c)=\chi_\lambda(h)^{-k}F_c. \tag{4.8}
$$

Equation (4.8) is the descent condition. The q-expansion at the stacky cusp is the equivariant series, not merely its coefficients after forgetting $H_c$.

If the cusp is defined over a finite residue algebra $A_0/R$, Galois conjugation permutes its framed expansions. A form over $R$ yields a compatible orbit. Conversely, compatible series at one representative of each orbit descend only after the global q-expansion principle has produced a section; local compatibility alone does not guarantee global existence.

The use of every cusp avoids two failures. A disconnected full-level modular curve can have components not meeting a chosen cusp, and a nonrational cusp can split after scalar extension. Taking the product over all geometric cusp orbits is stable under both phenomena.

## 5. The q-expansion principles

The expansion map is visibly compatible with algebra, but its injectivity is global. This chapter proves three increasingly arithmetic forms: vanishing, divisibility, and recognition of the integral lattice inside the generic space of forms.

### 5.1 Why boundary series can determine a global section

Let $X$ be a reduced proper curve over a field, $L$ a line bundle, and $c$ a smooth point. If a section $s\in H^0(X,L)$ has zero image in the completed stalk $\widehat L_c$, then $s=0$ near $c$. Indeed, after trivializing $L$, this says that a local function maps to zero in the completion of the noetherian local ring $\mathcal O_{X,c}$. The Krull intersection theorem makes

$$
\mathcal O_{X,c}\longrightarrow\widehat{\mathcal O}_{X,c}
$$

injective. Hence the germ is zero and the section vanishes on a nonempty open neighborhood.

If $X$ is integral, a section of a line bundle that vanishes on a nonempty open is zero: after trivializing at the generic point, it is a rational function equal to zero in the function field. If $X$ is merely reduced, the same conclusion holds provided the open meets every irreducible component. This is why expansions must be taken at enough cusps.

For a relative modular curve, one uses schematic density rather than only pointwise fibers. On a flat finitely presented family with geometrically reduced fibers, an open meeting every geometric irreducible component contains every associated point and is schematically dense. The cusp charts guarantee that every geometric connected component contains a cusp. If a component is smooth, it is integral; on a reduced reducible fine model, one chooses a cusp on every irreducible component or uses all cusps. Stack descent does not change the conclusion because a section is zero if its pullback to a faithfully flat atlas is zero.

### 5.2 Injectivity on a connected component

**Theorem 5.1 (q-expansion principle).** Let $R$ be a noetherian $B$-algebra and assume that $\mathcal X_R$ is flat with reduced geometric fibers. Choose the finite cusp framings so that their images meet every geometric irreducible component. Then

$$
\operatorname{qexp}:M_k(\Gamma;R)
\longrightarrow\prod_c(R\otimes_BA_c)[[t_c]] \tag{5.1}
$$

is injective. Over a field, one cusp on each integral connected component suffices.

**Proof.** Pull a section $f$ with zero expansions to a fine cover $Y_R$. At a selected cusp, trivialize the line. Its coefficient function maps to zero in the $t_c$-adic completion. Since $t_c$ is a non-zero-divisor in the noetherian local cusp ring, Krull intersection makes the completion map injective. Thus $f$ vanishes on an open neighborhood of every selected cusp.

The union of these neighborhoods meets every irreducible component of every geometric fiber. It is schematically dense. Indeed, for a flat finitely presented morphism, an associated point of the total space lies over an associated point of the base and is an associated point of that fiber; geometric reducedness says that the latter points are precisely the generic points of the fiber components. All of them lie in the union. A section of a line bundle vanishing on a schematically dense open is zero. Faithful descent gives $f=0$ on $\mathcal X_R$. $\square$

The theorem also has a one-cusp field form: on an integral modular curve over a field, the expansion at any one cusp is injective. The all-cusp form is safer over arithmetic bases because it survives splitting of components and cusp fields.

The same proof applies to sections of $\lambda^k(-D)$ and to any line bundle. What is special about modular forms is not the injectivity mechanism but the canonical Tate frames that turn completed sections into named power series.

### 5.3 Divisibility and descent of coefficients

Let $R$ be a domain and $a\in R$ a non-zero-divisor. If every coefficient of every cusp expansion of $f\in M_k(\Gamma;R)$ lies in $aR$, then the reduction of $f$ on $\mathcal X_{R/aR}$ has zero expansions. Theorem 5.1 makes that reduction zero. The exact sequence

$$
0\longrightarrow\lambda^k\xrightarrow{a}\lambda^k
\longrightarrow\lambda^k|_{R/aR}\longrightarrow0
$$

therefore shows that $f=ag$ for a unique $g\in M_k(\Gamma;R)$. We obtain:

**Corollary 5.2 (divisibility principle).** Under the hypotheses of Theorem 5.1, for every non-zero-divisor $a\in R$,

$$
\operatorname{qexp}_c(f)\in a(R\otimes A_c)[[t_c]]
\text{ for all }c
\quad\Longleftrightarrow\quad
f\in aM_k(\Gamma;R). \tag{5.2}
$$

The implication from right to left is immediate; the proof above gives the converse. Uniqueness uses $R$-flatness of the line bundle and of the modular curve.

For a general ideal $I$, the same assertion holds when $I$ is locally free of rank one, or whenever the natural map

$$
I\otimes_RM_k(\Gamma;R)
\longrightarrow H^0(\mathcal X_R,I\lambda^k) \tag{5.3}
$$

is an isomorphism. It is unsafe without such a hypothesis: kernels of reduction on global sections can be larger than $IM_k$ when cohomology has Tor. Over a Dedekind domain every nonzero ideal is invertible, so (5.3) holds.

There is also a descent version. Let $R\subset R'$ be a faithfully flat extension and suppose a form $f'\in M_k(\Gamma;R')$ has cusp expansions whose coefficients lie in $R$ and satisfy the descent symmetries. The two pullbacks of $f'$ to $R'\otimes_RR'$ have identical expansions and hence are equal by Theorem 5.1. Faithfully flat descent produces a unique form over $R$. Thus coefficient descent is a consequence of q-injectivity plus ordinary descent.

### 5.4 The integral q-expansion lattice

Let $R$ be a DVR with fraction field $K$, and assume the standard good-level model over $R$. Flat base change embeds

$$
M_k(\Gamma;R)\hookrightarrow M_k(\Gamma;K). \tag{5.4}
$$

The left side is a finite torsion-free module and therefore a lattice in the right side once it spans. Flat base change gives the spanning equality.

**Theorem 5.3 (integral q-expansion criterion).** A generic form $f\in M_k(\Gamma;K)$ belongs to $M_k(\Gamma;R)$ if and only if, at every cusp, its framed expansion has coefficients integral over $R$.

**Proof.** Necessity follows by restricting an integral section. For sufficiency, choose the smallest integer $r\geq0$ such that $\varpi^rf\in M_k(\Gamma;R)$; such an $r$ exists because the integral module is a full lattice. If $r>0$, the assumed integrality of the expansion of $f$ implies that every coefficient of $\varpi^rf$ is divisible by $\varpi$. Corollary 5.2 gives $\varpi^rf=\varpi g$ with $g$ integral. Then $\varpi^{r-1}f=g$, contradicting minimality. Thus $r=0$. $\square$

Over a Dedekind domain, apply the theorem at every height-one localization. Since a finite torsion-free module is the intersection of its height-one localizations inside its generic fiber,

$$
M_k(\Gamma;R)
=\{f\in M_k(\Gamma;K):
\operatorname{qexp}_c(f)\text{ is integral at every height-one prime and cusp}\}. \tag{5.5}
$$

All cusps are essential in (5.5) when the modular curve has several components. One expansion cannot see a component it does not meet.

## 6. The discriminant and concrete forms

The discriminant is simultaneously a modular form, an equation of the boundary, and a degree-measuring device. Its order is the first place where reduced cusps and cusp widths must be separated carefully.

### 6.1 The discriminant as a Hodge section

For a Weierstrass equation

$$
y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,
$$

the invariant differential is

$$
\eta=\frac{dx}{2y+a_1x+a_3}.
$$

A change of variables

$$
x=u^2x'+r,
\qquad y=u^3y'+su^2x'+t
$$

sends $\eta$ to $u^{-1}\eta'$ and the discriminant to $u^{12}\Delta'$. Therefore

$$
\Delta(E,u\eta)=u^{-12}\Delta(E,\eta),
$$

in the convention of (2.2). The discriminant defines a section

$$
\Delta\in M_{12}(1;\mathbf Z) \tag{6.1}
$$

on the unlevelled stack and, by pullback, on every level stack.

The Weierstrass discriminant is a unit exactly when the cubic is smooth. On a generalized elliptic boundary chart its Tate expansion is

$$
\Delta(q)=q\prod_{n\geq1}(1-q^n)^{24}. \tag{6.2}
$$

The infinite product belongs to $\mathbf Z[[q]]$ and has constant term one. Hence $\Delta$ has neither zeros nor poles on the elliptic open and vanishes precisely at the cusp.

Equation (6.2) also fixes the normalization. Replacing $\Delta$ by a nonzero scalar would retain its weight and divisor but change its first coefficient. We always normalize the coefficient of $q$ to be one.

### 6.2 Cusp width and the weighted discriminant divisor

At a framed cusp $c$ of width $w_c$, substitute $q=t_c^{w_c}$ into (6.2):

$$
\Delta=t_c^{w_c}
\prod_{n\geq1}(1-t_c^{nw_c})^{24}. \tag{6.3}
$$

The product is a unit. Thus

$$
\operatorname{ord}_{D_c}(\Delta)=w_c. \tag{6.4}
$$

**Proposition 6.1.** On $\mathcal X$ there is a canonical isomorphism

$$
\lambda^{12}\simeq\mathcal O_{\mathcal X}(W),
\qquad W=\sum_cw_cD_c, \tag{6.5}
$$

under which the canonical section of the right side corresponds to $\Delta$.

**Proof.** A nonzero section of a line bundle determines an effective Cartier divisor wherever its local equation is a non-zero-divisor. The stack is normal, $\Delta$ is nonzero on every component, and (6.3) gives the local equation $t_c^{w_c}$ times a unit. It has no other zeros. Hence its Cartier divisor is $W$, and the divisor--line correspondence of Book 9 gives (6.5). $\square$

The reduced boundary line $\mathcal O(D)$ agrees with $\lambda^{12}$ only when every width is one. Confusing $D$ and $W$ gives incorrect degrees and an incorrect definition of first-order cuspidality.

Because every connected component meets the cusp, $W$ has positive degree on every geometric component. Proposition 6.1 therefore proves the positivity of $\lambda$ used in Section 3.4.

### 6.3 The forms c4 and c6

The standard Weierstrass invariants $c_4$ and $c_6$ transform with exponents $4$ and $6$. Hence they define

$$
c_4\in M_4(1;\mathbf Z),
\qquad c_6\in M_6(1;\mathbf Z). \tag{6.6}
$$

Their algebraic identity is

$$
c_4^3-c_6^2=1728\Delta. \tag{6.7}
$$

All three terms have weight $12$, so the equation is globally well-typed. It can be checked on a universal Weierstrass equation, where it is the defining relation among the standard invariants.

On the Tate curve, direct substitution into the integral Tate equation gives

$$
c_4=1+240\sum_{n\geq1}\sigma_3(n)q^n, \tag{6.8}
$$

$$
c_6=-1+504\sum_{n\geq1}\sigma_5(n)q^n. \tag{6.9}
$$

The sign in (6.9) is fixed by the standard invariant formula: at the nodal Tate equation $y^2+xy=x^3$ one has $b_2=1$, $b_4=b_6=0$, and therefore $c_6=-b_2^3=-1$. Identity (6.7) then checks the squares and the normalized first term $\Delta=q+O(q^2)$. These expansions show that $c_4$ and $c_6$ do not vanish at the cusp, whereas $\Delta$ is cuspidal.

We do not need a presentation of the entire graded ring of level-one forms. The forms (6.6) are included because they calibrate weight, integrality, and discriminant normalization without relying on complex analysis.

### 6.4 Examples and normalization checks

First, $\Delta^m$ is a cusp form of weight $12m$ and vanishes to order $mw_c$ at a width-$w_c$ cusp. It lies in $S_{12m}$ because $mw_c\geq1$, but it usually vanishes much more strongly than cuspidality requires.

Second, $c_4\Delta$ has weight $16$ and first level-one terms

$$
c_4\Delta=q+216q^2+O(q^3).
$$

The product rule (4.6) computes the coefficient and shows directly that it is cuspidal.

Third, (6.7) explains why division by $1728$ is delicate over $\mathbf Z$. The numerator is divisible by $1728$ as an integral modular form, not merely coefficientwise over $\mathbf Q$. One may prove the divisibility from the universal invariant identity; alternatively, the q-expansion divisibility principle upgrades coefficientwise divisibility at all cusps to global divisibility.

Finally, at a component-type prime cusp of Book 116, $q=t^p$. Formula (6.3) gives $\Delta=t^p$ times a unit. The reduced boundary is still $t=0$. Thus the discriminant order remembers the $p$ passages around the polygon, while a cusp form need only contain one factor of $t$.

## 7. Cusp forms and boundary values

Cuspidality is often introduced as “zero constant term.” Geometrically it means vanishing on the reduced Cartier boundary. The equivalence is local, while the structure of the quotient is global cohomology.

### 7.1 Vanishing on the reduced boundary

The ideal of $D$ is $\mathcal O_{\mathcal X}(-D)$. Thus

$$
S_k(\Gamma;R)
=H^0(\mathcal X_R,\lambda^k(-D)). \tag{7.1}
$$

This definition is scheme-theoretic. If the base is nonreduced, vanishing at the underlying cusp points is not enough; the restriction to the Cartier divisor must be zero.

Why use the reduced boundary rather than the discriminant divisor? A regular parameter at the level cusp is $t$, and a function is zero on the boundary exactly when divisible by $t$. The discriminant is divisible by $t^w$. Requiring divisibility by $\Delta$ would impose order at least $w$ and would exclude legitimate cusp forms whenever $w>1$.

The definition commutes with every base change for which $D$ remains an effective Cartier divisor, as it does on the good-level stack. It is also multiplicative:

$$
M_k\cdot S_\ell\subseteq S_{k+\ell},
\qquad S_k\cdot S_\ell\subseteq H^0(\lambda^{k+\ell}(-2D)).
$$

Thus $S_*\subset M_*$ is a homogeneous ideal.

### 7.2 Constant terms at every cusp

On a framed cusp chart, $D$ has equation $t_c$. From (4.4),

$$
f\in S_k
\quad\Longleftrightarrow\quad
F_c(t_c)\in t_cA_c[[t_c]]
\quad\Longleftrightarrow\quad a_0(c,f)=0. \tag{7.2}
$$

The criterion is invariant under change of frame because an invertible coordinate change preserves the ideal $(t_c)$ and the Hodge scaling is a unit.

**Proposition 7.1.** A modular form is cuspidal if and only if its constant term vanishes at every geometric cusp.

**Proof.** If the section vanishes on $D$, every completed restriction is divisible by its local equation. Conversely, if all constant terms vanish, the restriction of the section to the finite divisor $D$ becomes zero after the faithfully flat cusp framings. Descent makes the restriction zero globally, so the section lies in the kernel of $\lambda^k\to\lambda^k|_D$, namely $\lambda^k(-D)$. $\square$

One cusp is not enough when components or cusp orbits are missing. At level one there is a single cusp, so the familiar one-series criterion is recovered.

### 7.3 The boundary exact sequence

Tensor the Cartier sequence of $D$ by $\lambda^k$:

$$
0\longrightarrow\lambda^k(-D)
\longrightarrow\lambda^k
\longrightarrow\lambda^k|_D
\longrightarrow0. \tag{7.3}
$$

Taking cohomology gives

$$
0\longrightarrow S_k
\longrightarrow M_k
\xrightarrow{\operatorname{ct}}
H^0(D,\lambda^k|_D)
\xrightarrow{\delta}
H^1(\mathcal X,\lambda^k(-D)). \tag{7.4}
$$

The map $\operatorname{ct}$ is the simultaneous constant-term map. It retains residue fields and stabilizer characters; replacing its target by one copy of the base per visible cusp is correct only after a splitting frame.

Surjectivity of constant-term evaluation is not formal. The obstruction is exactly the last $H^1$. On a fine modular curve, or on a quotient with linearly reductive stabilizers, Chapter 9 proves that it vanishes for $k>2$. For $k=2$ the corresponding duality module has rank one on each geometrically connected component, and the single relation among constant terms is the residue theorem. On a wild quotient, taking invariants can impose further restrictions. This exceptional behavior is geometrically meaningful rather than a defect of the definition.

### 7.4 Saturation of the cusp-form lattice

Let $R$ be a domain with fraction field $K$. Inside $M_k(\Gamma;K)$ one has

$$
S_k(\Gamma;R)
=M_k(\Gamma;R)\cap S_k(\Gamma;K). \tag{7.5}
$$

**Proof.** Only the reverse inclusion needs proof. Let $f$ be integral as a modular form and generically cuspidal. Its restriction to $D_R$ is a section of the line bundle $\lambda^k|_D$. It becomes zero over $K$. Since $D_R$ is finite flat over $R$, its section module is finite locally free after a cusp splitting and therefore torsion-free. The restriction was torsion and must be zero. Hence $f$ lies in $S_k(R)$. $\square$

Thus the quotient $M_k/S_k$ is torsion-free over a Dedekind coefficient ring. Equivalently, $S_k$ is a saturated sublattice of $M_k$. Combining (7.5) with Theorem 5.3 gives the q-expansion description

$$
S_k(\Gamma;R)=
\{f\in M_k(\Gamma;K):
\text{all cusp expansions are integral and all constant terms vanish}\}. \tag{7.6}
$$

This is the cusp-form lattice used in integral Hecke theory. It is defined by the compactified geometry, yet can be recognized entirely from generic forms and their expansions.

## 8. Kodaira--Spencer and dualizing forms

Weight two is special because deformation of an elliptic curve is dual to the square of its invariant differentials. At the cusp the deformation is logarithmic. Removing its logarithmic pole turns weight-two cusp forms into ordinary dualizing differentials.

### 8.1 Why weight two is differential

Let $E$ be an elliptic curve over a ring $A$, and let $A'\twoheadrightarrow A$ have square-zero kernel $I$. First regard $E$ as a pointed genus-one curve. Infinitesimal automorphisms fixing the identity are sections of $T_{E/A}(-e)$. The exact sequence

$$
0\to T_{E/A}(-e)\to T_{E/A}\to e_*e^*T_{E/A}\to0
$$

induces an isomorphism on $H^1$, because translation identifies global vector fields with their values at the identity, so $H^0(T_{E/A})\to e^*T_{E/A}$ is an isomorphism. A pointed genus-one curve has a unique compatible elliptic group law; consequently the deformation groupoid of the pointed curve is the deformation groupoid of the elliptic curve.

Choose affine opens of $E$ on which a putative lift is trivial. Two local lifts differ on an overlap by an infinitesimal automorphism, hence, after the preceding $H^1$ identification, by a section of $T_{E/A}\otimes_A I$. The cocycle condition on triple overlaps says that the differences form a class in

$$
H^1(E,T_{E/A})\otimes_A I. \tag{8.1}
$$

Here the displayed tensor description follows from projection formula and cohomology and base change for the trivial line on a genus-one curve. Changing the local identifications adds a coboundary. Conversely, gluing by any such cocycle gives a deformation, and a Cech calculation on triple overlaps proves associativity of the gluing. Thus (8.1) is the torsor of first-order deformations. Obstructions would lie in $H^2(E,T_{E/A})$, which is zero because $E$ is a curve.

Translation canonically identifies

$$
T_{E/A}\simeq\lambda_E^{-1}\otimes_A\mathcal O_E.
$$

Serre duality and the canonical trivialization $\Omega^1_{E/A}\simeq\lambda_E\otimes_A\mathcal O_E$ give

$$
H^1(E,T_{E/A})
\simeq\lambda_E^{-1}\otimes_AH^1(E,\mathcal O_E)
\simeq\lambda_E^{-2}. \tag{8.2}
$$

The universal deformation class on a smooth atlas of the elliptic moduli stack $\mathcal M$ therefore gives a canonical morphism from the dual line

$$
\operatorname{KS}_{\mathcal M}:\lambda^2
\longrightarrow\Omega^1_{\mathcal M/B}. \tag{8.3}
$$

At a geometric point, its transpose is exactly the isomorphism (8.2), so (8.3) is an isomorphism. For a family classified by $h:S\to\mathcal M$, pullback followed by the cotangent map gives the usual family Kodaira--Spencer morphism

$$
\lambda_E^2\simeq h^*\lambda^2
\longrightarrow h^*\Omega^1_{\mathcal M/B}
\longrightarrow\Omega^1_{S/B};
$$

this last map need not be an isomorphism for a non-universal family. The Cech construction is functorial in isomorphisms and base change, which makes the atlas maps glue.

Level of order invertible on the base is finite étale deformation data: finite étale schemes lift uniquely across nilpotent thickenings. Once the elliptic curve lifts, so do its chosen level sections or subgroup. The deformation torsor is therefore unchanged, explaining why the same Hodge square is the cotangent line for every good-level modular curve.

### 8.2 The logarithmic Kodaira--Spencer isomorphism

At a cusp, the ordinary cotangent line is generated by $dt$. Inside the logarithmic cotangent line one has $dt=t(dt/t)$, so its image on the boundary is zero, whereas elliptic deformation retains the nonzero logarithmic direction $dt/t$. Let

$$
\Omega^1_{\mathcal X/B}(\log D)=\Omega^1_{\mathcal X/B}(D)
$$

on the smooth relative stack curve. Locally it is generated by $dt/t$.

**Theorem 8.1 (logarithmic Kodaira--Spencer).** Over the good-level base there is a canonical isomorphism

$$
\operatorname{KS}:\lambda^2
\xrightarrow{\sim}\Omega^1_{\mathcal X/B}(\log D). \tag{8.4}
$$

**Proof strategy.** On the elliptic open, use the deformation calculation of Section 8.1. At a cusp, compute in a Tate frame and prove that the extension is a unit multiple of the logarithmic parameter.

**Proof.** The deformation interpretation makes (8.3) an isomorphism on $\mathcal Y$. It is functorial under isomorphisms and level changes, so it descends from a fine chart to the stack.

On a Tate curve with period $q$, use the invariant frame $\eta=du/u$. The universal extension class of the multiplicative quotient varies with $q$, and differentiating it gives

$$
\operatorname{KS}(\eta^{\otimes2})=\frac{dq}{q} \tag{8.5}
$$

as the sign normalization. To verify it, vary the period to $q(1+\epsilon a)$. The old and new multiplicative uniformizations are locally identical, but their gluing across one period differs by

$$
u\longmapsto(1+\epsilon a)u.
$$

The resulting deformation cocycle is $a\,u\partial_u$. Under the two identifications in (8.2), $u\partial_u$ is dual to $du/u$, so this cocycle pairs with $(du/u)^2$ to $a$. Since the cotangent functional $dq/q$ also takes the value $a$ on $q\mapsto q(1+\epsilon a)$, formula (8.5) follows.

At a width-$w$ level cusp, $q=t^w$, so

$$
\frac{dq}{q}=w\frac{dt}{t}. \tag{8.5a}
$$

The integer $w$ is invertible on the good-level base. Hence (8.5) extends as an isomorphism from the Hodge square to the logarithmic cotangent line. Both sides are line bundles; the local extensions agree with the already canonical map on the dense elliptic open, so density makes them glue uniquely. $\square$

If $w$ were not invertible, the coefficient in (8.5a) could vanish in the special fiber. This is one precise reason the theorem is not being asserted at a removed level prime without further integral-model analysis.

### 8.3 Weight-two cusp forms and regular dualizing differentials

For a smooth relative curve with Cartier divisor $D$,

$$
\Omega^1_{\mathcal X/B}(\log D)(-D)
=\Omega^1_{\mathcal X/B}.
$$

On the stack, or after passage to a fine cover, the ordinary cotangent line is the relative dualizing line. Twisting (8.4) by $-D$ gives

$$
\lambda^2(-D)\xrightarrow{\sim}\omega_{\mathcal X/B}. \tag{8.6}
$$

**Corollary 8.2.** There is a canonical identification

$$
S_2(\Gamma;R)
\xrightarrow{\sim}H^0(\mathcal X_R,\omega_{\mathcal X_R/R}). \tag{8.7}
$$

Thus weight-two cusp forms are regular dualizing differentials on the compactified modular curve.

In a cusp frame, if

$$
f=\left(\sum_{n\geq0}a_nt^n\right)\eta^2,
$$

then (8.4) sends it to

$$
\left(\sum_{n\geq0}a_nt^n\right)w\frac{dt}{t}. \tag{8.8}
$$

This differential is regular exactly when $a_0=0$. Writing $a_0=0$ turns (8.8) into

$$
w\left(a_1+a_2t+a_3t^2+\cdots\right)dt.
$$

The coefficient shift explains the analytic phrase $f(q)dq/q$: a cuspidal q-series produces a regular differential.

### 8.4 Residues and constant terms

Without the cusp condition, (8.4) identifies weight-two modular forms with logarithmic differentials. Formula (8.8) gives

$$
\operatorname{res}_c(\operatorname{KS}(f))=w_c a_0(c,f), \tag{8.9}
$$

in the coefficient algebra of the framed cusp. For a nonrational cusp orbit, descent places this element in the corresponding finite boundary algebra. The width factor is required because $dq/q=w_cdt/t$.

Book 9's global residue theorem, applied after a finite cusp splitting and then descended, gives the relation

$$
\sum_c\operatorname{Tr}_{A(c)/R}
\bigl(w_c a_0(c,f)\bigr)=0. \tag{8.10}
$$

Here $A(c)$ is the finite residue algebra of the descended cusp orbit after imposing its framing symmetries. The symbol $\operatorname{Tr}_{A(c)/R}$ is its finite-algebra trace; over a field it is the usual residue-field trace, with all geometric cusps counted after splitting. Equivalently, one may verify (8.10) on a fine cusp-splitting cover, where it is the ordinary sum of residues, and descend the resulting zero.

Suppose now that the modular problem is fine, or that its stabilizers are linearly reductive over the coefficient ring. On a geometrically connected component, (8.10) is then the only relation. Indeed, the residue exact sequence

$$
0\to\omega_{\mathcal X}
\to\omega_{\mathcal X}(D)
\xrightarrow{\operatorname{res}}\mathcal O_D
\to H^1(\mathcal X,\omega_{\mathcal X})\to0
$$

ends in a one-dimensional space, and the last map is the sum of residues. Since $\omega_{\mathcal X}(D)\simeq\lambda^2$, we obtain

$$
M_2/S_2\simeq
\ker\left(H^0(D,\mathcal O_D)
\xrightarrow{\sum\operatorname{Tr}(w_c\cdot)}R\right), \tag{8.11}
$$

with the Hodge frames understood in identifying the fibers with $\mathcal O_D$.

For a fine curve this is the ordinary relative residue sequence. For a linearly reductive quotient it remains exact after taking invariants. Without either hypothesis, every actual form still satisfies (8.10), but taking invariants need not preserve surjectivity, so further constant-term restrictions can occur. Under the stated hypothesis, (8.11) explains why arbitrary prescribed weight-two constant terms do not occur. For weights greater than two, the obstruction group vanishes and the boundary values become independent under the same fine or linearly reductive hypothesis.

## 9. Cohomology, base change, and integral lattices

The dualizing identity (8.6) turns all remaining cohomology into powers of the Hodge line. Positivity then proves vanishing, base change, and the lattice properties needed for congruences.

### 9.1 Duality calculations for powers of the Hodge line

Let $X$ be a geometric connected fine modular curve, or a geometric fiber of a modular stack with linearly reductive stabilizers. By (8.6),

$$
\omega_X\simeq\lambda^2(-D). \tag{9.1}
$$

Serre duality from Book 9 gives

$$
H^1(X,\lambda^k)^\vee
\simeq H^0(X,\lambda^{-k}\otimes\omega_X)
=H^0(X,\lambda^{2-k}(-D)), \tag{9.2}
$$

and

$$
H^1(X,\lambda^k(-D))^\vee
\simeq H^0(X,\lambda^{2-k}). \tag{9.3}
$$

The positivity supplied by $\lambda^{12}\simeq\mathcal O(W)$ has the following consequences:

$$
H^1(X,\lambda^k)=0\quad(k\geq2), \tag{9.4}
$$

because for $k=2$ the dual space is $H^0(\mathcal O(-D))=0$, and for $k>2$ it has negative Hodge degree. Likewise,

$$
H^1(X,\lambda^k(-D))=0\quad(k>2), \tag{9.5}
$$

while for $k=2$ its dual is $H^0(X,\mathcal O_X)$, one-dimensional on a geometrically connected component.

These proofs remain correct on a linearly reductive stack fiber after pulling to a fine cover and taking invariants, because invariants are exact. Every vanishing statement is made componentwise. On a wild quotient stack, higher group cohomology can survive even when the curve cohomology upstairs vanishes, so (9.4)--(9.5) are not asserted there.

### 9.2 Stable base change in weights at least two

**Theorem 9.1.** Assume $p:\mathcal X\to\operatorname{Spec}R$ is a good-level compactified modular curve with geometrically reduced connected fibers and constant cusp data. Assume in addition either that the moduli problem is fine or that the stabilizers are linearly reductive over $R$. Then:

1. for $k\geq2$, $M_k(\Gamma;R)$ is finite locally free and commutes with arbitrary base change;
2. for $k>2$, $S_k(\Gamma;R)$ is finite locally free and commutes with arbitrary base change;
3. $S_2(\Gamma;R)\simeq p_*\omega_{\mathcal X/R}$ is finite locally free and commutes with arbitrary base change.

**Proof.** On a fine cover, (9.4) gives fiberwise $H^1=0$ for $\lambda^k$, so Book 15's cohomology-and-base-change theorem gives local freeness and arbitrary base change of $H^0$. The same argument with (9.5) handles cusp forms of weight greater than two. If a quotient presentation is needed, linear reductivity makes invariants exact and compatible with arbitrary scalar extension, so these conclusions descend to the stack.

For weight two cusp forms, (8.7) and relative duality identify

$$
p_*\omega_{\mathcal X/R}\simeq(R^1p_*\mathcal O_{\mathcal X})^\vee.
$$

The right side is locally free and base-change compatible for a proper flat family of geometrically connected curves of constant genus. Descent from the fine cover preserves the assertion under the stated fine or linearly reductive hypothesis. $\square$

Without that extra hypothesis, all three modules remain finite and commute with flat coefficient change by Theorem 3.1, but arbitrary nonflat base change can fail because invariants need not be exact. Vanishing of curve cohomology does not erase wild stabilizer cohomology.

For $k>2$, (7.4) is therefore short exact:

$$
0\longrightarrow S_k
\longrightarrow M_k
\longrightarrow H^0(D,\lambda^k|_D)
\longrightarrow0. \tag{9.6}
$$

For $k=2$, it is replaced by the residue relation (8.11).

### 9.3 Lattices over Dedekind domains

Let $R$ be a Dedekind domain with fraction field $K$. Proper finiteness makes $M_k(R)$ and $S_k(R)$ finite. They are torsion-free: multiplication by a nonzero $a\in R$ is injective on the line bundle, hence on its global sections. A finite torsion-free module over a Dedekind domain is projective. Flat base change gives

$$
M_k(R)\otimes_RK\simeq M_k(K),
\qquad
S_k(R)\otimes_RK\simeq S_k(K). \tag{9.7}
$$

Thus both are full projective lattices in their generic spaces.

The cusp lattice is saturated by (7.5). The modular lattice is characterized by q-integrality by (5.5). Combining them gives a practical intrinsic description:

$$
S_k(R)=
\bigcap_{\mathfrak p\subset R,\,\operatorname{ht}\mathfrak p=1}
\{f\in S_k(K):
\operatorname{qexp}_c(f)\in R_{\mathfrak p}[[t_c]]
\text{ for every }c\}. \tag{9.8}
$$

Hecke and diamond operators will preserve this lattice because their coefficient formulas are integral and preserve zero constant terms.

### 9.4 Low weights and torsion warnings

For weight one, duality gives

$$
H^1(X,\lambda)^\vee\simeq H^0(X,\lambda(-D))=S_1(X), \tag{9.9}
$$

so the obstruction to base change of $M_1$ is governed by weight-one cusp forms. Its dimension can vary in characteristic, and torsion in integral cohomology can create forms after reduction. No blanket arbitrary-base-change statement is valid.

For weight zero,

$$
H^1(X,\mathcal O_X)^\vee\simeq S_2(X). \tag{9.10}
$$

On a connected proper reduced curve, $M_0=R$ under the usual cohomological flatness hypothesis, but $H^1$ records the genus and is far from zero.

Stabilizers create an independent low-characteristic warning. An odd-weight section may be forced to vanish in characteristic different from two by inversion, while the character becomes trivial in characteristic two. A special-fiber odd-weight form can therefore fail to lift even when the underlying curve varies smoothly. This is consistent with (3.3): the failure lies in cohomology and invariants, not in the definition of weight.

These warnings delimit, rather than weaken, Theorem 9.1. Weights at least two are stable because duality and positivity kill the exact obstruction; low weights retain arithmetic information that cannot be discarded.

## 10. Diamond operators and change of level

Level structures introduce finite symmetries before any isogeny correspondence is considered. Diamond operators record those symmetries on forms, and finite change-of-level maps supply the pullback and trace operations from which Hecke theory is built.

### 10.1 Changing a chosen generator

On the $\Gamma_1(N)$ stack, every $a\in(\mathbf Z/N\mathbf Z)^\times$ defines

$$
\delta_a:\mathcal X_1(N)\longrightarrow\mathcal X_1(N),
\qquad(E,P)\longmapsto(E,aP). \tag{10.1}
$$

The Drinfeld divisor generated by $aP$ equals the divisor generated by $P$, because multiplication by $a$ permutes the indices modulo $N$. It remains ample, so the map extends across the compactification without changing the underlying generalized elliptic curve. Its inverse is $\delta_{a^{-1}}$.

Define the diamond operator by pullback:

$$
\langle a\rangle f=\delta_a^*f. \tag{10.2}
$$

Our convention gives

$$
\langle a\rangle\langle b\rangle=\langle ab\rangle. \tag{10.3}
$$

Some sources define the operator using $\delta_{a^{-1}}^*$ so that a chosen right action becomes a left action. Formula (10.2) removes that ambiguity for every later q-expansion formula.

On full level, a matrix in the group preserving the chosen Weil-pairing normalization changes the basis $(P,Q)$ and acts in the same way. On $\Gamma_0(N)$ the generator has already been forgotten, so the unit action is invisible on the object $(E,C)$; diamond eigenspaces are naturally studied on the point-level cover before passing to cyclic level.

### 10.2 Action on forms and expansions

The automorphism $\delta_a$ leaves the elliptic curve and its invariant differential unchanged, so it acts trivially on the local Hodge frame. It generally permutes the cusps. If $c$ is a framed cusp and $\delta_a(c)$ carries the transported frame, then

$$
\operatorname{qexp}_c(\langle a\rangle f)
=\operatorname{qexp}_{\delta_a(c)}(f). \tag{10.4}
$$

If one replaces the transported frame by a fixed standard frame at $\delta_a(c)$, (4.7) inserts the corresponding root-of-unity and Hodge factors. Formula (10.4) is the intrinsic statement.

Diamond operators preserve $M_k(R)$, $S_k(R)$, and their integral lattices. Preservation of cusp forms follows either because $\delta_a^{-1}D=D$ or because (10.4) permutes zero constant terms. The operators commute with change of coefficients.

At a cusp fixed by the diamond action as an unframed point, the operator can still act nontrivially on the root parameter. If $t\mapsto\zeta t$, then a series $\sum a_nt^n$ is transformed to $\sum a_n\zeta^nt^n$, up to the Hodge character. Thus diamond eigenspaces impose congruence conditions on the allowed exponents at that cusp.

### 10.3 Characters and nebentypus

Let $R$ contain the values of a character

$$
\chi:(\mathbf Z/N\mathbf Z)^\times\longrightarrow R^\times.
$$

The nebentypus submodule in our convention is

$$
M_k(\Gamma_1(N),\chi;R)
=\{f:\langle a\rangle f=\chi(a)f\text{ for all }a\}. \tag{10.5}
$$

The same definition gives $S_k(\chi;R)$. If the order of the character group is invertible in $R$, the idempotent

$$
e_\chi=\frac1{\varphi(N)}
\sum_a\chi(a)^{-1}\langle a\rangle \tag{10.6}
$$

projects onto this summand. Without that invertibility, (10.5) remains the correct kernel intersection, but it need not be a direct summand. We shall never use (10.6) integrally without its denominator hypothesis.

Inversion gives a parity constraint. The automorphism $[-1]$ sends $P$ to $-P$, so it is the diamond operator $\langle-1\rangle$ on point level, while its pullback on the Hodge frame contributes $(-1)^k$. A nonzero eigensection must therefore satisfy

$$
\chi(-1)=(-1)^k \tag{10.7}
$$

over a coefficient ring in which the two signs are distinct. This is the geometric parity condition for nebentypus.

### 10.4 Pullback and trace along a finite change of level

Let

$$
r:\mathcal X(\Gamma')\longrightarrow\mathcal X(\Gamma)
$$

be a finite flat change-of-level map over a base on which the additional level order is invertible. The underlying generalized elliptic curve is unchanged after the canonical contraction prescribed by the retained level, and on the smooth locus the Hodge lines identify. Thus there is a pullback

$$
r^*:M_k(\Gamma;R)\longrightarrow M_k(\Gamma';R). \tag{10.8}
$$

Projection formula and the trace $r_*\mathcal O\to\mathcal O$ give

$$
\operatorname{Tr}_r:M_k(\Gamma';R)
\longrightarrow M_k(\Gamma;R). \tag{10.9}
$$

Locally, if $r$ is finite free with basis $b_i$, the trace is the matrix trace of multiplication. Hence

$$
\operatorname{Tr}_r(r^*f)=\deg(r)f. \tag{10.10}
$$

Both maps preserve cusp forms when the reduced boundary pulls back to the reduced boundary. More generally, trace preserves vanishing along $D$ because a section vanishing on the source boundary has zero restriction on every point above the target boundary; the trace of that restriction is zero.

Pullback and trace are integral. Division by the degree is a separate normalization and is permitted only after a divisibility theorem or after inverting the degree. Hecke operators provide the central example.

## 11. Hecke correspondences away from the level

A Hecke operator is not an endomorphism of elliptic curves. It is a sum over isogenies, organized by a finite correspondence. The Hodge line tells us how to transport weight through each isogeny, and trace performs the sum.

### 11.1 The moduli correspondence

Let $\ell$ be a prime not dividing $N$. Work first over $B[1/\ell]$. Let $\mathcal X(\Gamma;\ell)$ classify a $\Gamma$-object together with a cyclic subgroup

$$
C\subset E[\ell]
$$

of rank $\ell$. Because $\ell$ is invertible, $C$ is finite étale locally cyclic, and the compactified moduli construction of Book 117 applies to the enlarged level. There are finite maps

$$
\begin{array}{ccc}
&\mathcal X(\Gamma;\ell)&\\
\pi_1\swarrow&&\searrow\pi_2\\
\mathcal X(\Gamma)&&\mathcal X(\Gamma),
\end{array} \tag{11.1}
$$

where

$$
\pi_1(E,\alpha,C)=(E,\alpha),
$$

and $\pi_2$ sends the object to the quotient $E/C$ with the transported $\Gamma$-level. Since $(\ell,N)=1$, the image of the $N$-level remains a full structure of the same type. Quotient and contraction extend $\pi_2$ across the boundary by Books 116 and 117.

On a smooth geometric fiber, $E[\ell]\simeq(\mathbf Z/\ell\mathbf Z)^2$ has $\ell+1$ cyclic subgroups. Hence $\pi_1$ is finite étale of degree $\ell+1$ on the elliptic locus. At cusps its ramification is governed by the two Tate quotient types, but it remains finite on the good-level compactification.

It is also finite locally free. This may be checked before arbitrary scalar extension, on a fine chart over the regular Dedekind good-level base. Both total spaces are smooth relative curves and hence regular of dimension two. For a target local ring $A$ and a source local ring $B$ above it, finiteness and equality of dimensions make $B$ a maximal Cohen--Macaulay $A$-module. The regular local ring $A$ has finite global dimension; the depth formula therefore makes $B$ projective, hence free because $A$ is local. The rank is the constant generic degree $\ell+1$. Finite local freeness persists under every later base change, so the trace below is the ordinary finite-locally-free trace.

### 11.2 Differentials through the universal isogeny

On the correspondence there is a universal isogeny

$$
\varphi:\pi_1^*\mathcal E\longrightarrow\pi_2^*\mathcal E. \tag{11.2}
$$

Pullback of invariant differentials gives

$$
\varphi^*:\pi_2^*\lambda\longrightarrow\pi_1^*\lambda. \tag{11.3}
$$

Over $B[1/\ell]$ the isogeny is étale on smooth elliptic fibers, so (11.3) is an isomorphism there. On the compactification it is a morphism of lines whose Tate formula records any factor of $\ell$.

For weight $k$, tensoring gives

$$
(\varphi^*)^k:\pi_2^*\lambda^k\longrightarrow\pi_1^*\lambda^k. \tag{11.4}
$$

Thus a form $f$ pulls back along $\pi_2$, is transported to the source Hodge frame by the isogeny, and becomes a section of $\pi_1^*\lambda^k$. Trace along $\pi_1$ can then return it to the original modular curve.

The direction of (11.3) is essential. Transporting a differential from $E/C$ back to $E$ uses pullback. Reversing it would change the powers of $\ell$ in the q-expansion formula.

### 11.3 The normalized Hecke operator

Define over $R[1/\ell]$

$$
T_\ell f=\frac{1}{\ell}
\operatorname{Tr}_{\pi_1}
\left((\varphi^*)^k\pi_2^*f\right). \tag{11.5}
$$

The factor is $1/\ell$, not $1/(\ell+1)$. It is chosen so that the coefficient of $q^n$ coming from the $\ell$ nonmultiplicative subgroups is one. Chapter 12 will derive the formula and prove that the apparent denominator cancels on the integral q-expansion lattice.

The construction is functorial under coefficient extension and commutes with diamond operators. The latter follows because changing the $N$-level generator commutes with taking an $\ell$-subgroup and quotienting, as $\ell$ is prime to $N$.

On weight two cusp forms, use (8.7). Formula (11.5) becomes the usual normalized pull--push operation on regular differentials. Regularity at the boundary follows from the cusp-preservation statement below, not from pretending that the boundary is absent.

### 11.4 Preservation of cusp forms and integral lattices

The correspondence maps boundary to boundary. If $f$ vanishes along the target boundary, then $\pi_2^*f$ vanishes along its inverse image. Transport by the isogeny changes only the Hodge factor, and trace along $\pi_1$ has zero restriction at every target cusp. Thus

$$
T_\ell(S_k)\subseteq S_k \tag{11.6}
$$

where (11.5) is defined.

For the characteristic-zero Dedekind coefficient rings $R$ considered in Section 12.4, (11.5) initially lies in $M_k(R[1/\ell])$. In positive weight, Chapter 12 shows that every cusp expansion has coefficients in $R$. The integral q-expansion criterion then puts the result in $M_k(R)$. In this way the operator is extended integrally without using a compactified auxiliary-$\ell$ correspondence in residue characteristic $\ell$.

This argument also proves uniqueness in that setting. Two integral endomorphisms agreeing after inverting $\ell$ agree because the Dedekind lattice $M_k(R)$ is torsion-free. Thus the q-expansion formula does not merely suggest an integral operator; it determines one.

## 12. Hecke operators on q-expansions

The coefficient formula is a local calculation on the Tate curve. It also explains the normalization, the diamond factor, the Hecke relations, and the integrality that is not obvious from the trace definition.

### 12.1 The subgroups of a Tate curve

Work over a ring containing the required $\ell$th roots and a formal root $q^{1/\ell}$. The cyclic order-$\ell$ subgroups of $E_q$ fall into $\ell+1$ directions:

1. the multiplicative subgroup $\mu_\ell$;
2. for $j\in\mathbf Z/\ell\mathbf Z$, the subgroup generated by the class of $\zeta_\ell^j q^{1/\ell}$.

For the first subgroup, Book 116 gives

$$
E_q/\mu_\ell\simeq E_{q^\ell}, \tag{12.1}
$$

and the quotient map is induced by $u\mapsto u^\ell$. Therefore

$$
\varphi^*\left(\frac{du'}{u'}\right)
=\ell\frac{du}{u}. \tag{12.2}
$$

For the subgroup generated by $\zeta_\ell^jq^{1/\ell}$, enlarging the period lattice gives

$$
E_q/C_j\simeq E_{\zeta_\ell^jq^{1/\ell}}, \tag{12.3}
$$

and the isogeny is induced by the identity on $\mathbf G_m$. It therefore pulls $du'/u'$ back to $du/u$.

For $\Gamma_1(N)$, the multiplicative quotient sends the chosen $N$-point to its $\ell$th multiple in the standard Tate identification. With convention (10.2), this contributes the diamond operator $\langle\ell\rangle$. For level one the diamond factor is absent.

### 12.2 The prime-index formula

Write at the chosen cusp

$$
f(q)=\sum_{n\geq0}a_n(f)q^n.
$$

The multiplicative subgroup contributes, before the normalization $1/\ell$,

$$
\ell^k(\langle\ell\rangle f)(q^\ell). \tag{12.4}
$$

The other subgroups contribute

$$
\sum_{j=0}^{\ell-1}
f(\zeta_\ell^jq^{1/\ell}). \tag{12.5}
$$

Expand and use

$$
\sum_{j=0}^{\ell-1}\zeta_\ell^{jn}
=\begin{cases}
\ell,&\ell\mid n,\\
0,&\ell\nmid n.
\end{cases} \tag{12.6}
$$

Then (12.5) equals

$$
\ell\sum_{m\geq0}a_{\ell m}(f)q^m. \tag{12.7}
$$

Dividing the sum of (12.4) and (12.7) by $\ell$ proves:

**Theorem 12.1 (Hecke q-expansion formula).** With the diamond convention (10.2),

$$
a_n(T_\ell f)
=a_{\ell n}(f)
+\ell^{k-1}a_{n/\ell}(\langle\ell\rangle f), \tag{12.8}
$$

where $a_{n/\ell}=0$ if $\ell\nmid n$. Equivalently,

$$
(T_\ell f)(q)
=\sum_{n\geq0}a_{\ell n}(f)q^n
+\ell^{k-1}(\langle\ell\rangle f)(q^\ell). \tag{12.9}
$$

On a $\chi$-eigenspace, the second term is $\chi(\ell)\ell^{k-1}a_{n/\ell}(f)$.

At a general framed cusp, write its period as $q=t^w$. Because $w$ divides the original level order and $(\ell,N)=1$, one has $(\ell,w)=1$. The multiplicative subgroup sends the transported root parameter to a unit times $t^\ell$; the other $\ell$ subgroups use the $\ell$ choices of a root parameter, and summing them gives the same root-of-unity cancellation as (12.6). After choosing compatible transported frames, (12.8) is therefore the coefficient formula in the genuine parameter $t$, with the cusp label and diamond action transported along the correspondence. A different standard framing inserts only the unit changes of (4.7). In particular the operator may permute cusps, but at every cusp its coefficients remain integral and its constant term remains zero when the original constant terms are zero.

### 12.3 Composite indices and Hecke relations

For $m$ prime to $N$, the degree-$m$ correspondence can be organized by finite locally free cyclic subgroup schemes of rank $m$. Its normalized operator is characterized by the coefficient formula

$$
a_n(T_mf)
=\sum_{d\mid(m,n)}d^{k-1}
a_{mn/d^2}(\langle d\rangle f), \tag{12.10}
$$

with the evident interpretation that $\langle d\rangle$ depends only on $d\bmod N$. For level one it is omitted.

We prove the formula and relations by prime powers and coprime products. In a chain consisting of a cyclic $\ell$-isogeny followed by a cyclic $\ell^r$-isogeny, let $H$ be the inverse image of the second kernel in the original elliptic curve. If $H$ is cyclic of order $\ell^{r+1}$, its order-$\ell$ subgroup is unique, so the chain is counted by the cyclic $\ell^{r+1}$-correspondence. Otherwise $H$ contains the full kernel $E[\ell]$; quotienting it by $E[\ell]$ leaves a cyclic subgroup of order $\ell^{r-1}$. This is the exceptional family of chains. On it the composite isogeny factors through $[\ell]$, which multiplies invariant differentials by $\ell$. Repeating the root-of-unity trace calculation of (12.4)--(12.7) on this exceptional family shows that the normalized pull--trace is $\ell^{k-1}\langle\ell\rangle$ times the remaining $\ell^{r-1}$-correspondence. Sorting the two disjoint families therefore gives

$$
T_\ell T_{\ell^r}
=T_{\ell^{r+1}}
+\ell^{k-1}\langle\ell\rangle T_{\ell^{r-1}}. \tag{12.11}
$$

For coprime $m,n$, a cyclic subgroup of order $mn$ is uniquely the direct sum of its order-$m$ and order-$n$ parts. Hence

$$
T_mT_n=T_{mn}\qquad((m,n)=1). \tag{12.12}
$$

Starting with $T_1=1$, relations (12.11)--(12.12) determine the operators and induction gives (12.10). One can verify the induction coefficientwise: divisors of $(mn,r)$ split uniquely into their coprime parts, while the two terms in (12.11) separate divisors according to whether they contain the last factor of $\ell$. Q-expansion injectivity upgrades the coefficient identities to identities of global operators.

The geometric chain count also explains why the scalar is $\ell^{k-1}\langle\ell\rangle$: the exceptional composite is multiplication by $\ell$ on invariant differentials, contributing $\ell^k$, while the normalized trace removes one factor of $\ell$.

### 12.4 An integral extension without bad-level geometry

Let $R$ be a characteristic-zero Dedekind $B$-algebra, flat over the corresponding localization of $\mathbf Z$, and do not invert $\ell$. Define $T_\ell$ on the generic fiber by the correspondence over $R[1/\ell]$. Formula (12.8) shows that every cusp expansion of $T_\ell f$ is integral whenever the expansions of $f$ are integral: both terms have coefficients in $R$, and $\ell^{k-1}$ is integral for $k\geq1$.

Theorem 5.3 therefore gives

$$
T_\ell f\in M_k(\Gamma;R) \tag{12.13}
$$

for $k\geq1$. If $f$ is cuspidal, both terms of (12.9) have zero constant term at every transported cusp, so $T_\ell f\in S_k(R)$. The same reasoning applies to $T_m$ using (12.10).

For weight zero the factor $\ell^{-1}$ is not integral in (12.8); the usual normalized Hecke operator on functions requires separate interpretation. Our integral operator statement is therefore made for positive weights. This is a real edge case, not a notational inconvenience.

No geometry in characteristic $\ell$ has been assumed. We used the good auxiliary-level correspondence after inverting $\ell$, proved an integral coefficient formula, and recognized the original integral lattice by q-expansion. This is exactly the conclusion supported by the dependency graph.

## 13. Sturm bounds as finite jet separation

The q-expansion principle asks whether an entire series is zero. A Sturm bound replaces that infinite question by a finite one. Geometrically, too many initial zero coefficients force a section to have more zeros than the degree of its line bundle permits.

### 13.1 The geometric bound

Let $f:X\to S$ be a proper flat family of geometrically reduced curves, let $L$ be a line bundle, and let

$$
Z=\sum_ci_cc
$$

be an effective Cartier divisor supported on disjoint sections through the smooth locus. The restriction map

$$
H^0(X,L)\longrightarrow H^0(Z,L|_Z) \tag{13.1}
$$

records the jets of orders $0$ through $i_c-1$ at $c$.

**Theorem 13.1 (finite-jet criterion).** If

$$
\deg(L_s|_C)-\deg(Z_s|_C)<0 \tag{13.2}
$$

for every irreducible component $C$ of every geometric fiber, then (13.1) is injective and remains injective after arbitrary base change.

**Proof.** Its kernel is $H^0(X,L(-Z))$. On every geometric irreducible component, (13.2) gives negative degree. A section on a reduced curve restricts to a section on each normalization component. Negative degree forces every restriction to vanish, so the original section is zero.

Apply Book 15's exact base-change criterion in degree zero to $L(-Z)$. At every geometric point the target of the base-change map is zero, so the map is vacuously surjective. It follows locally that $f_*L(-Z)$ commutes with arbitrary base change and is locally free of fiber rank zero; hence it is zero. The same degree inequality survives every base change, proving the universal assertion. $\square$

For an integral curve over a field, one point $c$ and an integer $i>\deg L$ suffice. A nonzero section has an effective zero divisor of degree $\deg L$; vanishing to order $i$ is impossible. The relative proof is stronger because it also rules out nilpotent sections invisible on reduced point sets.

Applied to $L=\lambda^k$, the restriction to $i_cc$ is exactly the first $i_c$ coefficients of the $t_c$-expansion after choosing the Tate frame.

### 13.2 Degree of the Hodge line

Fix a geometric connected component $X$. Degrees must retain inertia. Choose a finite representable fine cover $r:Y\to X$. It is finite locally free after restricting to the component: both curves are smooth and the same Cohen--Macaulay argument used for $\pi_1$ in Section 11.1 applies. For a line bundle $L$ on $X$, define

$$
\deg_XL=\frac{\deg_Y(r^*L)}{\deg(r)}.
$$

For a geometric cusp component $D_c$, define $\deg_XD_c$ by the same pullback rule, including ramification multiplicity. A common fine refinement shows that both definitions are independent of $r$. On a fine modular curve they are ordinary degrees; on a stack they can be rational. In particular, on the unlevelled stack the generic involution gives

$$
\deg\lambda=\frac1{24},
\qquad \deg D_\infty=\frac12.
$$

This example is the factor-of-two test that an unnormalized stack calculation must pass.

The discriminant identity gives the exact degree formula

$$
12\deg_X\lambda
=\deg_XW
=\sum_cw_c\deg_XD_c. \tag{13.3}
$$

For a chosen cusp $c$, define its **cusp-normalized modular index** by

$$
\mu_{X,c}
=\frac{12\deg_X\lambda}{\deg_XD_c}. \tag{13.4}
$$

This ratio is unchanged on a fine framed cover provided the denominator is the degree of the full pulled-back cusp orbit $r^*D_c$, not the degree of one arbitrarily chosen lift. The degree of the cover, the stabilizer order, and the ramification of the local parameter then occur in both numerator and denominator and cancel. At the standard infinity cusp, $\mu_{X,c}$ is the usual index $[\operatorname{SL}_2(\mathbf Z):\Gamma]$ when $-I\in\Gamma$, and it is the index of the image of $\Gamma$ in $\operatorname{PSL}_2(\mathbf Z)$ when $-I\notin\Gamma$. Using the larger $\operatorname{SL}_2$ index in the latter case gives a valid but sometimes nonsharp bound.

Kodaira--Spencer gives a second check. Taking degrees in

$$
\lambda^2\simeq\omega_X(D)
$$

yields

$$
2\deg\lambda=2g(X)-2+\deg D \tag{13.5}
$$

on a fine smooth curve. Combining (13.3) and (13.5) is the familiar genus--cusp--index relation. The rational-degree version retains the elliptic stabilizer corrections on the stack.

### 13.3 Classical numerical bounds

Let $k\geq0$, let $K$ be a field on the good-level base, and let $X$ be an integral component. Choose a cusp $c$ with genuine root parameter $t$. If

$$
f(t)=\sum_{n\geq0}a_nt^n
$$

is nonzero of weight $k$, its zero divisor contains $\operatorname{ord}_c(f)D_c$. Consequently

$$
\operatorname{ord}_c(f)\deg_XD_c
\leq k\deg_X\lambda,
\qquad
\operatorname{ord}_c(f)\leq\frac{k\mu_{X,c}}{12}. \tag{13.6}
$$

Consequently, with

$$
B_{X,c}(k)=\left\lfloor\frac{k\mu_{X,c}}{12}\right\rfloor, \tag{13.7}
$$

the vanishing

$$
a_0=a_1=\cdots=a_{B_{X,c}(k)}=0 \tag{13.8}
$$

forces $f=0$. Indeed, (13.8) gives an order whose contribution to the zero-divisor degree is strictly greater than $k\deg_X\lambda$.

If the chosen series is written in the unlevelled parameter $q=t^w$, only exponents compatible with the cusp frame occur, and order must be converted to $t$-order. The clean bound is always (13.7) in the genuine uniformizer. At the standard infinity cusp of $\Gamma_0(N)$, the width is one, so (13.7) is the usual q-coefficient bound.

For a disconnected modular curve, impose (13.8) at one cusp on each connected component. Alternatively, choose jets of lengths $i_c$ at all cusps such that

$$
\sum_c i_c\deg_XD_c>k\deg_X\lambda
$$

on each component. This form is invariant under Galois permutation of cusps.

The bound is intentionally stated with a floor and coefficients through that index. Saying only “check up to $k\mu/12$” is ambiguous when the number is integral: one must force order strictly greater than the degree.

### 13.4 Congruences and finite certification

Let $k\geq0$, let $R$ be a noetherian coefficient ring, and let $I\subset R$ be an ideal. Choose a finite cusp jet divisor $Z$ satisfying (13.2) for $L=\lambda^k$ on every geometric fiber of $R/I$. On a stack this condition is checked after a finite fine framing; the resulting jet conditions are then imposed equivariantly. Theorem 13.1 gives an injection

$$
M_k(\Gamma;R/I)
\hookrightarrow H^0(Z_{R/I},\lambda^k|_Z). \tag{13.9}
$$

Therefore, for $f,g\in M_k(\Gamma;R)$,

$$
f\equiv g\pmod{I}
$$

if and only if their finitely many selected cusp coefficients are congruent modulo $I$ in the corresponding framed coefficient algebras. Here $f\equiv g\pmod I$ means that their images in $M_k(\Gamma;R/I)$ agree. It means $f-g\in I M_k(\Gamma;R)$ as well whenever the base-change map identifies the latter quotient with its image, for example under Theorem 9.1; without such a hypothesis, that stronger module-theoretic wording is not automatic. No reducedness of $R/I$ is needed: injectivity was proved for the whole relative scheme, not only its geometric points.

At one cusp of an integral component, one may take the first

$$
1+B_{X,c}(k)
$$

coefficients. For all-cusp certification, choose nonnegative integers $i_c$ with

$$
\sum_c i_c\deg_XD_c>k\deg_X\lambda
$$

on each component and compare coefficients of orders $0$ through $i_c-1$.

The same criterion applies to cusp forms. Their constant terms are already zero, but they still live in $\lambda^k$ and the safest universal bound remains (13.7). A sharper cusp-space bound can be obtained from $\lambda^k(-D)$ by subtracting the forced boundary degree, provided the chosen jets and every component are tracked separately.

Since Hecke and diamond operators are determined by their q-expansions, (13.9) also gives finite certification of operator identities and eigenvalue congruences. One proves the coefficient identity through the Sturm cutoff; the geometric injection proves the global identity.

## 14. The integral q-expansion package

The theory can now be used as a closed sequence: moduli geometry produces a Hodge line, Tate charts produce series, proper curves make the series faithful, duality controls lattices, correspondences act on them, and degree makes the tests finite.

### 14.1 A dependency-closed theorem summary

Under the good-level hypotheses of Section 1.2, the following statements have been proved.

1. The universal generalized elliptic curve has a base-change-compatible Hodge line

   $$
   \lambda=e^*\Omega^1_{\mathcal E^{\mathrm{sm}}/\mathcal X}
   \simeq\pi_*\omega_{\mathcal E/\mathcal X}.
   $$

2. Integral modular forms and cusp forms are

   $$
   M_k=H^0(\mathcal X,\lambda^k),
   \qquad S_k=H^0(\mathcal X,\lambda^k(-D)).
   $$

   They are finite modules; flat coefficient change always commutes with their formation.

3. A framed width-$w$ cusp has $q=t^w$ and Hodge frame $du/u$. Expansion in $t$ is equivariant under changes of frame and stabilizers.

4. Expansions at cusps meeting every component determine a modular form. Over a DVR or Dedekind domain, a generic form is integral exactly when all its framed cusp expansions are integral. It is cuspidal exactly when all constant terms vanish.

5. The discriminant is a normalized weight-$12$ form with

   $$
   \operatorname{div}(\Delta)=W=\sum_cw_cD_c,
   \qquad\lambda^{12}\simeq\mathcal O(W).
   $$

6. Logarithmic Kodaira--Spencer and its cuspidal twist give

   $$
   \lambda^2\simeq\Omega^1_{\mathcal X/B}(\log D),
   \qquad\lambda^2(-D)\simeq\omega_{\mathcal X/B}.
   $$

   Hence weight-two cusp forms are regular dualizing differentials, and weight-two constant terms are residues divided by cusp widths.

7. In weights at least two, positivity and duality give the stable base-change results of Theorem 9.1 on fine or linearly reductive stacks; flat base change holds without that extra assumption. Over a Dedekind domain, modular and cusp forms are projective lattices, and the cusp lattice is saturated.

8. Diamond operators act by changing a level generator. Away-level Hecke operators are normalized pull--trace operators. Their q-expansion is

   $$
   a_n(T_\ell f)=a_{\ell n}(f)
   +\ell^{k-1}a_{n/\ell}(\langle\ell\rangle f),
   $$

   and this formula extends them integrally in positive weight while preserving cusp lattices.

9. A section is determined by any finite set of cusp jets whose total imposed vanishing exceeds the Hodge degree on every component. At a cusp $c$ of an integral component, coefficients through

   $$
   \left\lfloor k\mu_{X,c}/12\right\rfloor,
   \qquad
   \mu_{X,c}=\frac{12\deg_X\lambda}{\deg_XD_c},
   $$

   suffice in the genuine cusp uniformizer. This ratio, rather than either stack degree alone, incorporates generic and cuspidal inertia correctly.

The imported results are exactly those verified in the direct prerequisites. Book 9 supplies Cartier divisors, residues, dualizing sheaves, degree, Serre duality, and the finite-jet degree argument. Book 15 supplies proper finiteness, exact base-change criteria, formal completion, and Hodge pushforwards. Book 116 supplies invariant differentials on polygons, Tate frames, cusp parameters, contractions, and quotient isogenies. Book 117 supplies the proper compactified stacks, fine covers, coarse-space cautions, cusp Cartier divisors, and finite degeneracy maps. Every additional result central here—q-injectivity, integral lattice recognition, logarithmic Kodaira--Spencer in this setting, Hecke coefficient formulas, and Sturm certification—was proved in the present book. Arbitrary nonflat base change on a stack is asserted only in the fine or linearly reductive cases; flat base change remains valid generally.

### 14.2 Hypotheses that cannot be suppressed

The following failures mark the exact scope of the package.

- If a cusp is omitted on a disconnected component, its expansion cannot detect a form supported on that component.

- If cusp width is ignored, the discriminant divisor, logarithmic differential, Hecke normalization, and Sturm order can all be off by a factor.

- If the reduced boundary $D$ is replaced by the weighted divisor $W$, the definition of cusp form becomes too strong at a wide cusp.

- If properness is removed, global sections need not be finite and a form can have uncontrolled poles at the missing boundary.

- If flatness or the adjacent cohomology criterion is removed, reduction can create modular forms through Tor.

- If stabilizers are discarded by passing prematurely to a coarse curve, the Hodge line or universal elliptic curve may fail to descend.

- If the level or cusp width is not invertible, $dq/q=w\,dt/t$ need not generate the logarithmic cotangent line. The good-level Kodaira--Spencer proof then does not establish the desired integral isomorphism.

- If one divides a trace without proving divisibility, the proposed Hecke operator need not preserve an integral lattice. Here integrality was proved from the q-formula and the integral q-expansion criterion.

- If a Sturm test imposes vanishing equal to, rather than strictly greater than, the line-bundle degree, a nonzero section with exactly that zero divisor is not excluded.

These are hypothesis boundaries rather than missing parts of the stated theory. Geometry at primes dividing the level, regular special-fiber components, and their intersection theory require a different local model and are not used here.

### 14.3 Conclusion

An integral modular form is a global section whose weight records how invariant differentials are framed. The generalized elliptic boundary makes that section proper, the Tate curve gives it a power series, and the stack retains the stabilizer characters that a coarse curve would forget. The resulting definition works over rings because every ingredient—Hodge line, Cartier cusp, dualizing differential, and formal parameter—commutes with the permitted base changes.

The q-expansion principle is the point where local and global geometry meet. A zero formal series kills a section near a cusp; a cusp on every component makes that neighborhood globally decisive. Over a valuation ring, the same argument detects divisibility and therefore identifies the integral lattice inside the generic space of forms. Cuspidality becomes first-order vanishing on the reduced boundary, while the discriminant remembers the larger cusp-width multiplicity.

Kodaira--Spencer explains the exceptional role of weight two. The square of the Hodge line is the logarithmic cotangent line, and removing the cusp pole gives the dualizing line. Constant terms become residues, cusp forms become regular differentials, and relative duality controls base change and saturation. Hecke correspondences then transport Hodge frames through isogenies; their Tate calculation gives the integral coefficient formula and preserves the cusp lattice.

Finally, divisor degree turns infinite expansions into finite evidence. A nonzero section cannot vanish beyond the degree of its line. The Hodge degree is measured by the weighted discriminant divisor, producing the Sturm cutoff. Thus the complete chain is

$$
\text{invariant differential}
\longrightarrow\text{Hodge section}
\longrightarrow\text{cusp expansion}
\longrightarrow\text{integral lattice}
\longrightarrow\text{Hecke action}
\longrightarrow\text{finite certification}.
$$

This is the integral modular-form package required for later modular Jacobians and Hecke correspondences: complete at every cusp, exact about coefficients and duality, and finite enough to certify global identities from a bounded list of terms.
