# Quaternion Algebras over Number Fields

## Contents

1. [Why quaternion algebras](#1-why-quaternion-algebras)
   - [The degree-two central simple problem](#11-the-degree-two-central-simple-problem)
   - [Presentations and their multiplication](#12-presentations-and-their-multiplication)
   - [Why every degree-two algebra has a presentation](#13-why-every-degree-two-algebra-has-a-presentation)
   - [Changing parameters without changing the algebra](#14-changing-parameters-without-changing-the-algebra)
   - [Inner symmetries and conjugacy of quadratic subalgebras](#15-inner-symmetries-and-conjugacy-of-quadratic-subalgebras)
2. [Conjugation, trace, norm, and the norm form](#2-conjugation-trace-norm-and-the-norm-form)
   - [The intrinsic replacement for eigenvalues](#21-the-intrinsic-replacement-for-eigenvalues)
   - [The reduced characteristic polynomial](#22-the-reduced-characteristic-polynomial)
   - [Invertibility and the quadratic norm form](#23-invertibility-and-the-quadratic-norm-form)
   - [Polarization and pure quaternions](#24-polarization-and-pure-quaternions)
   - [Worked trace and norm calculations](#25-worked-trace-and-norm-calculations)
   - [The trace pairing and the pure three-space](#26-the-trace-pairing-and-the-pure-three-space)
3. [The split and division models](#3-the-split-and-division-models)
   - [Matrices as a quaternion algebra](#31-matrices-as-a-quaternion-algebra)
   - [Hamilton's algebra](#32-hamiltons-algebra)
   - [Zero divisors and division](#33-zero-divisors-and-division)
   - [Idempotents and minimal left ideals](#34-idempotents-and-minimal-left-ideals)
4. [Equivalent tests for splitting](#4-equivalent-tests-for-splitting)
   - [One dichotomy, many witnesses](#41-one-dichotomy-many-witnesses)
   - [The splitting theorem](#42-the-splitting-theorem)
   - [Scalar extension and splitting fields](#43-scalar-extension-and-splitting-fields)
   - [Quadratic subfields](#44-quadratic-subfields)
   - [The splitting conic](#45-the-splitting-conic)
5. [Quadratic norms and cyclic algebras](#5-quadratic-norms-and-cyclic-algebras)
   - [Why a norm equation controls splitting](#51-why-a-norm-equation-controls-splitting)
   - [The cyclic description](#52-the-cyclic-description)
   - [The norm criterion](#53-the-norm-criterion)
   - [Worked norm equations](#54-worked-norm-equations)
   - [What the parameter class remembers](#55-what-the-parameter-class-remembers)
6. [Brauer classes and algebraic operations](#6-brauer-classes-and-algebraic-operations)
   - [Matrix factors and the Brauer group](#61-matrix-factors-and-the-brauer-group)
   - [Opposites and exponent two](#62-opposites-and-exponent-two)
   - [Tensor identities](#63-tensor-identities)
   - [Extension of scalars](#64-extension-of-scalars)
   - [Restriction, corestriction, exponent, and index](#65-restriction-corestriction-exponent-and-index)
7. [Hilbert symbols over local fields](#7-hilbert-symbols-over-local-fields)
   - [A binary sign for a local splitting problem](#71-a-binary-sign-for-a-local-splitting-problem)
   - [Square classes, symmetry, and bilinearity](#72-square-classes-symmetry-and-bilinearity)
   - [The archimedean fields](#73-the-archimedean-fields)
   - [Odd residue characteristic](#74-odd-residue-characteristic)
   - [Dyadic fields and the rational dyadic formula](#75-dyadic-fields-and-the-rational-dyadic-formula)
   - [A local calculation laboratory](#76-a-local-calculation-laboratory)
   - [Nondegeneracy and the geometry of square classes](#77-nondegeneracy-and-the-geometry-of-square-classes)
8. [Local classification and local invariants](#8-local-classification-and-local-invariants)
   - [Why there is only one division algebra](#81-why-there-is-only-one-division-algebra)
   - [The invariant normalization](#82-the-invariant-normalization)
   - [A concrete division algebra](#83-a-concrete-division-algebra)
   - [Local quadratic embeddings](#84-local-quadratic-embeddings)
   - [Local splitting extensions and norm groups](#85-local-splitting-extensions-and-norm-groups)
9. [Global ramification and reciprocity](#9-global-ramification-and-reciprocity)
   - [Seeing a global algebra place by place](#91-seeing-a-global-algebra-place-by-place)
   - [The ramification set](#92-the-ramification-set)
   - [Finiteness and the infinite places](#93-finiteness-and-the-infinite-places)
   - [Hilbert reciprocity and parity](#94-hilbert-reciprocity-and-parity)
   - [Reciprocity as a global norm statement](#95-reciprocity-as-a-global-norm-statement)
   - [Global reduced norms and positivity](#96-global-reduced-norms-and-positivity)
10. [The local--global classification](#10-the-local--global-classification)
    - [The classification theorem](#101-the-classification-theorem)
    - [Why uniqueness is global](#102-why-uniqueness-is-global)
    - [Why every even set occurs](#103-why-every-even-set-occurs)
    - [Presentations versus algebras](#104-presentations-versus-algebras)
    - [Producing a presentation from local data](#105-producing-a-presentation-from-local-data)
    - [Exact control of the archimedean signature](#106-exact-control-of-the-archimedean-signature)
11. [Base change and quadratic embeddings](#11-base-change-and-quadratic-embeddings)
    - [The local degree formula](#111-the-local-degree-formula)
    - [Ramification after extension](#112-ramification-after-extension)
    - [The quadratic embedding criterion](#113-the-quadratic-embedding-criterion)
    - [Constructing useful quadratic subfields](#114-constructing-useful-quadratic-subfields)
    - [Conjugacy and the classification of embeddings](#115-conjugacy-and-the-classification-of-embeddings)
    - [Why every ramified place must be checked](#116-why-every-ramified-place-must-be-checked)
12. [Totally definite algebras](#12-totally-definite-algebras)
    - [Compactness at infinity begins with ramification](#121-compactness-at-infinity-begins-with-ramification)
    - [The exact parity condition](#122-the-exact-parity-condition)
    - [Construction with prescribed finite ramification](#123-construction-with-prescribed-finite-ramification)
    - [The algebra required later](#124-the-algebra-required-later)
    - [Definite, indefinite, and mixed signature](#125-definite-indefinite-and-mixed-signature)
13. [Explicit algebras over the rationals](#13-explicit-algebras-over-the-rationals)
    - [Four basic ramification patterns](#131-four-basic-ramification-patterns)
    - [Computing a ramification set](#132-computing-a-ramification-set)
    - [Behavior under selected base changes](#133-behavior-under-selected-base-changes)
14. [The reusable local--global dictionary](#14-the-reusable-local--global-dictionary)
    - [Equivalent languages](#141-equivalent-languages)
    - [A decision procedure](#142-a-decision-procedure)
    - [Conclusion](#143-conclusion)

## 1. Why quaternion algebras

### 1.1 The degree-two central simple problem

A matrix algebra is the most familiar noncommutative algebra over a field. Yet a field can possess algebras which become matrix algebras only after its scalars are enlarged. Quaternion algebras are the first place where this descent phenomenon is visible without being buried under high-dimensional structure. They have dimension four, their multiplication can be written on one line, and nevertheless their behavior records subtle information from every completion of a number field.

Throughout this book, $F$ is a field of characteristic different from $2$ unless explicitly stated otherwise. The principal cases are number fields and their completions, all of characteristic zero. An $F$-algebra $B$ is **central simple** if its center is exactly $F$ and it has no nonzero proper two-sided ideals. Its **degree** is the positive integer $n$ such that

$$
\dim_F B=n^2.
$$

Thus a four-dimensional central simple algebra has degree two. We call such an algebra a **quaternion algebra over $F$**. This definition is intrinsic: an algebra, not a chosen list of generators, is the object. A presentation will give coordinates, but the same algebra generally has many presentations.

The general structure theorem for central simple algebras says that $B\cong M_r(D)$ for a central division algebra $D$, uniquely determined up to isomorphism. In degree two there are only two possibilities:

$$
B\cong M_2(F),
\qquad\text{or}\qquad
B\text{ is a four-dimensional division algebra.}
$$

This sharp dichotomy is why so many later conditions become equivalent. A single zero divisor, an isotropic norm vector, or a nontrivial idempotent is enough to rule out the division case and force the matrix case.

### 1.2 Presentations and their multiplication

To calculate, we want generators that isolate two quadratic directions. For $a,b\in F^\times$, define

$$
(a,b)_F=F\langle i,j\rangle/(i^2-a,\ j^2-b,\ ij+ji).
$$

Put $k=ij$. Every element has a unique expression

$$
x=x_0+x_1i+x_2j+x_3k,
\qquad x_r\in F.
$$

The multiplication table follows from the three defining relations:

$$
i^2=a,\qquad j^2=b,\qquad ij=k,\qquad ji=-k,
$$

$$
k^2=-ab,\qquad ik=aj,\qquad ki=-aj,
\qquad jk=-bi,\qquad kj=bi.
$$

These relations prove directly that the displayed four vectors span. Linear independence can be checked after adjoining square roots of $a$ and $b$, where an explicit matrix representation is available. They also show that an element commuting with both $i$ and $j$ is scalar, so the center is $F$. Simplicity follows after the same scalar extension, or directly by using commutators to isolate the four coordinates. Hence $(a,b)_F$ is a quaternion algebra.

The hypotheses $a,b\ne0$ matter. If one allowed $a=0$, the generator $i$ would be a nonzero nilpotent and the resulting algebra would not be central simple. Characteristic $2$ also changes the correct form of a presentation: the relation $ij=-ji$ then becomes commutativity. Since all arithmetic fields in this book have characteristic zero, the classical presentation is exactly the right one here.

### 1.3 Why every degree-two algebra has a presentation

The notation $(a,b)_F$ would be much less useful if it described only specially constructed examples. The decisive fact is that it describes every quaternion algebra when $\operatorname{char}F\ne2$.

**Theorem 1.1 (presentation theorem).** Every four-dimensional central simple $F$-algebra is isomorphic to $(a,b)_F$ for some $a,b\in F^\times$.

**Proof strategy.** First find a quadratic étale subalgebra and choose a generator of trace zero inside it. Then find a second element that implements the nontrivial automorphism of that subalgebra. The two elements necessarily anticommute.

**Proof.** Let $B$ be a quaternion algebra. The separable-element theorem for central simple algebras supplies a quadratic separable étale subalgebra $E\subset B$; the hypothesis $\operatorname{char}F\ne2$ excludes an inseparable degree-two obstruction. Choose a generator $i\in E$ of trace zero for the quadratic étale trace. Its two conjugates are $i$ and $-i$, so

$$
i^2=a\in F^\times.
$$

The scalar is nonzero because the chosen subalgebra is étale. Thus $E=F[i]$ is either a quadratic field or the split quadratic algebra $F\times F$.

The nontrivial $F$-automorphism $\sigma$ of $E$ sends $i$ to $-i$. The conjugacy theorem for embeddings of a separable commutative subalgebra in a central simple algebra supplies $j\in B^\times$ such that

$$
jxj^{-1}=\sigma(x)\qquad(x\in E).
$$

Consequently $ji=-ij$. The four elements $1,i,j,ij$ are independent. If $E$ is a field, a relation $x+yj=0$ with $x,y\in E$ and $y\ne0$ would put $j=-y^{-1}x$ in $E$, where conjugation by $j$ could not induce $\sigma$. If $E\cong F\times F$, let $e$ and $1-e$ be its primitive idempotents. The relation $je=(1-e)j$ places $ej$ and $(1-e)j$ in the two off-diagonal Peirce components, while $E$ occupies the diagonal components; invertibility of $j$ makes both off-diagonal vectors nonzero. Thus $E\oplus Ej$ has dimension four in either case and equals $B$.

Now $j^2$ centralizes $E$ because $\sigma^2=1$, and it plainly centralizes $j$. Since $E$ and $j$ generate $B$, centrality of $B$ gives $j^2=b\in F^\times$. The basis $1,i,j,ij$ and its relations give $B\cong(a,b)_F$. $\square$

This proof also explains the shape of the presentation. One generator records a quadratic subalgebra; the other records its Galois involution. Anticommutation is not an arbitrary flourish but the equation expressing that involution.

### 1.4 Changing parameters without changing the algebra

Coordinates are useful only if we know which changes are harmless. Replacing $i$ by $ri$ and $j$ by $sj$, with $r,s\in F^\times$, gives

$$
(a,b)_F\cong(ar^2,bs^2)_F.
$$

Interchanging $i$ and $j$ gives

$$
(a,b)_F\cong(b,a)_F,
$$

and replacing $j$ by $ij$ gives

$$
(a,b)_F\cong(a,-ab)_F.
$$

Thus the parameters live naturally in square classes, but square classes alone do not classify presentations: different pairs of square classes can still define the same algebra.

There is a more flexible change. Let $E=F(\sqrt a)$ when $a$ is nonsquare, and write $N=N_{E/F}$. If $u\in E^\times$, replacing the cyclic generator $j$ by $uj$ changes its square to $N(u)b$. Hence

$$
(a,b)_F\cong(a,bN(u))_F.
$$

The same formula remains valid when $E=F\times F$, with its exchange involution and product norm. This is the first indication that splitting will be governed by quadratic norm groups.

One warning will remain in force. The symbol $(a,b)_F$ denotes a presented algebra; a letter such as $B$ denotes an algebra independent of presentation. Statements about ramification, discriminant, or definiteness belong to $B$. We may compute them from a chosen presentation, but they do not depend on that choice.

### 1.5 Inner symmetries and conjugacy of quadratic subalgebras

A presentation chooses a quadratic direction, but the algebra itself usually contains many of them. To compare calculations made from different choices, one needs to know how much freedom an algebra automorphism has. The answer is unusually rigid: every symmetry fixing the center is produced by conjugation inside the algebra.

**Theorem 1.2 (innerness and conjugacy).** Let $B$ be a quaternion algebra over an infinite field $F$ of characteristic different from $2$.

1. Every $F$-algebra automorphism of $B$ has the form $x\mapsto uxu^{-1}$ for some $u\in B^\times$.
2. If $E$ and $E'$ are isomorphic quadratic étale $F$-subalgebras of $B$, then some $u\in B^\times$ satisfies $uEu^{-1}=E'$.
3. If two embeddings $\iota_1,\iota_2:E\hookrightarrow B$ of a quadratic étale algebra have the same source, then $\iota_2(x)=u\iota_1(x)u^{-1}$ for all $x\in E$ and some $u\in B^\times$.

**Proof strategy.** After extending scalars to a field that splits $B$, the assertions become the familiar conjugacy of faithful two-dimensional representations. The relation obtained there is a finite system of linear equations over $F$. Its solution space is already defined over $F$, and invertibility is the nonvanishing of a determinant polynomial. Descent then produces an invertible solution over $F$.

**Proof.** We prove the third statement, from which the second follows by composing one embedding with an isomorphism $E\cong E'$. Consider the $F$-linear subspace

$$
V=\{u\in B:u\iota_1(x)=\iota_2(x)u\text{ for every }x\in E\}.
$$

It suffices to impose the relation for one generator of $E$, so $V$ is the kernel of an $F$-linear map. Extend scalars to a separable closure $F^s$. The algebra $B_{F^s}$ is $M_2(F^s)$, while $E_{F^s}\cong F^s\times F^s$. Both embeddings decompose the two-dimensional column space into two distinct one-dimensional eigenspaces. A linear isomorphism carrying the ordered pair of eigenspaces for $\iota_1$ to that for $\iota_2$ is an invertible element of $V\otimes_FF^s$.

Choose an $F$-basis $v_1,\ldots,v_r$ of $V$. The reduced norm of $t_1v_1+\cdots+t_rv_r$ is a quadratic polynomial in the $t_i$. The invertible point over $F^s$ shows that this polynomial is not identically zero. Because $F$ is infinite, some $(c_1,\ldots,c_r)\in F^r$ makes it nonzero. Then

$$
u=c_1v_1+\cdots+c_rv_r
$$

lies in $V^\times$ and intertwines the embeddings. This proves the third and second statements.

For the first, let $\varphi$ be an $F$-automorphism of $B$. Choose a quadratic étale subalgebra $E\subset B$. By the third statement, after composing $\varphi$ with an inner automorphism we may suppose that it fixes $E$ pointwise. Write $B=E\oplus Ej$ with $jx=\sigma(x)j$. An automorphism fixing $E$ must send $j$ to $cj$ for some $c\in E^\times$, because $Ej$ is exactly the subspace on which right multiplication twists by $\sigma$. Preservation of $j^2$ gives $N_{E/F}(c)=1$. Hilbert's theorem 90 supplies $d\in E^\times$ with $c=d/\sigma(d)$. Conjugation by $d$ fixes $E$ and sends $j$ to $(d/\sigma(d))j=cj$. Thus the adjusted automorphism is also inner, and so is $\varphi$. $\square$

The infinitude hypothesis enters only in the nonvanishing argument. The conclusion also holds over finite fields, but that extension is not needed here. Every field considered from Chapter 7 onward is infinite.

This theorem explains why changing a maximal quadratic subfield is a coordinate change rather than new structure. It also gives a useful warning: the conjugating element is determined only up to multiplication by the centralizer of $E$, which is $E^\times$. A presentation is therefore plentiful but never canonical.

## 2. Conjugation, trace, norm, and the norm form

### 2.1 The intrinsic replacement for eigenvalues

Matrices carry trace, determinant, and characteristic polynomial. A quaternion algebra may not act on a two-dimensional vector space over its ground field, so those familiar definitions are not immediately available. The remedy is to define them after passing to a splitting field and then descend. In degree two the result has an especially concrete form.

For

$$
x=x_0+x_1i+x_2j+x_3k\in(a,b)_F,
$$

define the **canonical conjugate**

$$
\bar x=x_0-x_1i-x_2j-x_3k.
$$

This is an involution of the first kind: it fixes $F$, satisfies $\bar{\bar x}=x$, and reverses multiplication,

$$
\overline{xy}=\bar y\,\bar x.
$$

The reversal is essential because conjugation is an anti-automorphism, not an automorphism. Checking it on $i$ and $j$ is enough.

Define the **reduced trace** and **reduced norm** by

$$
\operatorname{Trd}(x)=x+\bar x,
\qquad
\operatorname{Nrd}(x)=x\bar x=\bar x x.
$$

Both values lie in $F$. In coordinates,

$$
\operatorname{Trd}(x)=2x_0
$$

and

$$
\operatorname{Nrd}(x)
=x_0^2-a x_1^2-b x_2^2+ab x_3^2.
$$

The adjective “reduced” distinguishes these degree-two invariants from the trace and determinant of left multiplication on the four-dimensional vector space $B$. Those larger invariants satisfy

$$
\operatorname{Tr}_F(L_x)=2\operatorname{Trd}(x),
\qquad
\det_F(L_x)=\operatorname{Nrd}(x)^2.
$$

### 2.2 The reduced characteristic polynomial

Every quaternion satisfies a quadratic equation over the center:

$$
x^2-\operatorname{Trd}(x)x+\operatorname{Nrd}(x)=0.
$$

Indeed, $\bar x=\operatorname{Trd}(x)-x$, and multiplication by $x$ gives the identity. We call

$$
P_x(T)=T^2-\operatorname{Trd}(x)T+\operatorname{Nrd}(x)
$$

the **reduced characteristic polynomial**. After any splitting $B\otimes_F L\cong M_2(L)$, it becomes the ordinary characteristic polynomial of the corresponding matrix. This proves that reduced trace, reduced norm, and canonical conjugation are intrinsic and independent of the presentation used to calculate them.

For a scalar $c\in F$, the reduced characteristic polynomial is $(T-c)^2$, so $\operatorname{Trd}(c)=2c$ and $\operatorname{Nrd}(c)=c^2$. For a pure quaternion $y$, meaning $\operatorname{Trd}(y)=0$, one has

$$
y^2=-\operatorname{Nrd}(y).
$$

Thus pure quaternions are precisely the quadratic directions that appeared in the presentation theorem.

Reduced norm is multiplicative:

$$
\operatorname{Nrd}(xy)
=xy\overline{xy}
=xy\bar y\bar x
=x\operatorname{Nrd}(y)\bar x
=\operatorname{Nrd}(x)\operatorname{Nrd}(y).
$$

Reduced trace is linear but not multiplicative. It is cyclic in the useful sense

$$
\operatorname{Trd}(xy)=\operatorname{Trd}(yx),
$$

as follows either by coordinates or after splitting into matrices.

### 2.3 Invertibility and the quadratic norm form

The norm was designed to detect inverses. If $\operatorname{Nrd}(x)\ne0$, then

$$
x^{-1}=\frac{\bar x}{\operatorname{Nrd}(x)}.
$$

Conversely, a multiplicative norm cannot vanish on an invertible element. Hence

$$
x\in B^\times
\quad\Longleftrightarrow\quad
\operatorname{Nrd}(x)\ne0.
$$

The coordinate formula exhibits the reduced norm as the four-dimensional quadratic form

$$
n_B=\langle1,-a,-b,ab\rangle
=\langle1,-a\rangle\otimes\langle1,-b\rangle.
$$

This is a two-fold Pfister form. Its special shape explains an unusually strong alternative: it is either anisotropic or hyperbolic. For the immediate splitting theory we need only the simpler observation that a nonzero isotropic vector is exactly a nonzero noninvertible quaternion.

For example, in $(1,b)_F$ the vector $1+i$ is nonzero and has norm $1-1=0$. By contrast, in $(-1,-1)_{\mathbf R}$ the norm is

$$
x_0^2+x_1^2+x_2^2+x_3^2,
$$

which vanishes only at zero. The first algebra must split; the second must be division. A single quadratic form has exposed the entire algebraic dichotomy.

### 2.4 Polarization and pure quaternions

The polar form of the norm is

$$
\langle x,y\rangle
=\operatorname{Nrd}(x+y)-\operatorname{Nrd}(x)-\operatorname{Nrd}(y)
=\operatorname{Trd}(x\bar y).
$$

Because $2$ is invertible, this bilinear form recovers the norm. The scalar line $F\cdot1$ is orthogonal to the three-dimensional pure subspace

$$
B^0=\ker(\operatorname{Trd}).
$$

On $B^0$ the quadratic form is

$$
-a x_1^2-b x_2^2+ab x_3^2.
$$

This geometry is useful when searching for alternative presentations. A pure element $u$ with $u^2=a'$ supplies a new first generator; an orthogonal pure element $v$ anticommutes with it, because for pure $u,v$ one has

$$
uv+vu=-\langle u,v\rangle.
$$

Thus orthogonal pairs in the pure norm space are exactly anticommuting pairs of generators. Coordinate changes in the algebra and orthogonal changes in its norm form are two views of the same operation.

### 2.5 Worked trace and norm calculations

The coordinate rules are short enough that one should be able to use them without expanding every product from scratch. Let

$$
x=x_0+x_1i+x_2j+x_3k,
\qquad
y=y_0+y_1i+y_2j+y_3k.
$$

The scalar part of $xy$ is

$$
x_0y_0+a x_1y_1+b x_2y_2-abx_3y_3,
$$

so

$$
\operatorname{Trd}(xy)
=2(x_0y_0+a x_1y_1+b x_2y_2-abx_3y_3).
$$

This symmetric expression makes $\operatorname{Trd}(xy)=\operatorname{Trd}(yx)$ visible even though $xy$ and $yx$ usually differ. The commutator of the basic generators is

$$
[i,j]=ij-ji=2k,
$$

and its norm is

$$
\operatorname{Nrd}(2k)=4ab.
$$

The sign is worth checking: $k^2=-ab$, while a pure quaternion has norm minus its square.

Take $B=(2,3)_{\mathbf Q}$ and

$$
x=1+i+j.
$$

Then

$$
\operatorname{Trd}(x)=2,
\qquad
\operatorname{Nrd}(x)=1-2-3=-4,
$$

so

$$
x^{-1}=-\frac14(1-i-j).
$$

Multiplication verifies this directly. The negative rational norm is no obstacle to invertibility; only vanishing matters. At the real place an indefinite norm form naturally takes both signs.

For another example, let $u=i+j$ in $(a,b)_F$. It is pure and

$$
u^2=a+b,
\qquad
\operatorname{Nrd}(u)=-(a+b).
$$

If $a+b\ne0$, then $F[u]$ is the quadratic étale algebra determined by the square class of $a+b$. Thus the same quaternion presentation may exhibit many quadratic subalgebras besides $F(i)$ and $F(j)$. If $a+b=0$, then $u$ is nilpotent; this can occur only in the split algebra, as the splitting theorem predicts.

Reduced trace and norm also control powers. From

$$
x^2=\operatorname{Trd}(x)x-\operatorname{Nrd}(x)
$$

every polynomial in $x$ reduces to a linear expression in $1$ and $x$. If $t=\operatorname{Trd}(x)$ and $n=\operatorname{Nrd}(x)$, then

$$
x^3=(t^2-n)x-tn.
$$

This is the quaternionic analogue of the Cayley--Hamilton recurrence for a $2\times2$ matrix. It is often preferable to repeated noncommutative multiplication because all coefficients remain central.

### 2.6 The trace pairing and the pure three-space

The norm determines invertibility, while the trace pairing detects the full four-dimensional linear structure. Define

$$
T_B(x,y)=\operatorname{Trd}(xy).
$$

It is symmetric because reduced trace is cyclic. In the basis $1,i,j,k$ of $(a,b)_F$, its Gram matrix is diagonal:

$$
\operatorname{diag}(2,2a,2b,-2ab).
$$

Its determinant is $-16a^2b^2$, which is nonzero. Thus $T_B$ is nondegenerate. This gives a quick intrinsic proof that the orthogonal complement of the scalar line is exactly $B^0=\ker(\operatorname{Trd})$: for $y\in B$,

$$
T_B(1,y)=\operatorname{Trd}(y).
$$

The multiplication of pure quaternions can be separated into a scalar part and a pure part. For $u,v\in B^0$, put

$$
u\times v=\frac{uv-vu}{2}.
$$

Then

$$
uv=-\frac12\langle u,v\rangle+u\times v,
$$

where $\langle u,v\rangle=\operatorname{Trd}(u\bar v)$ is the polar form of the reduced norm. The first summand measures the failure of $u$ and $v$ to be orthogonal; the second measures the failure to commute. In particular,

$$
uv=-vu
\quad\Longleftrightarrow\quad
\langle u,v\rangle=0,
$$

If nonzero pure elements $u$ and $v$ commute, then their cross product vanishes. The centralizer of $u$ is the quadratic algebra $F[u]$, whose pure part is one-dimensional; hence $u$ and $v$ lie on the same pure line.

These formulas recover the multiplication from the geometry of $B^0$ together with an orientation of its alternating product. For the standard generators,

$$
i\times j=k,\qquad j\times k=-bi,\qquad k\times i=-aj.
$$

The signs encode the same parameters that occur in the norm form. This is the three-dimensional shadow of quaternion multiplication: scalar products govern anticommutators, cross products govern commutators.

There is a useful separability consequence. If $x\notin F$, then the subalgebra $F[x]$ has dimension two. It is quadratic étale unless the reduced characteristic polynomial is a repeated linear factor. In characteristic different from $2$, the latter occurs precisely when the trace-zero part of $x$ is a nonzero nilpotent. That can happen in the split algebra but never in a division algebra. Thus every nonscalar element of a quaternion division algebra generates a separable quadratic field, while a split algebra also contains nonsemisimple elements. The matrix

$$
\begin{pmatrix}0&1\\0&0\end{pmatrix}
$$

is the basic counterexample: it is nonscalar, has repeated reduced characteristic polynomial $T^2$, and generates the nonreduced algebra $F[\varepsilon]/(\varepsilon^2)$ rather than a quadratic étale algebra.

## 3. The split and division models

### 3.1 Matrices as a quaternion algebra

The split quaternion algebra is $M_2(F)$. A useful presentation is $(1,b)_F$ for any $b\in F^\times$. Send

$$
i\longmapsto
\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad
j\longmapsto
\begin{pmatrix}0&b\\1&0\end{pmatrix}.
$$

The two matrices square to $1$ and $b$, respectively, and anticommute. Together with their product they form a basis of $M_2(F)$, proving

$$
(1,b)_F\cong M_2(F).
$$

Under this isomorphism canonical conjugation becomes the adjugate involution

$$
\begin{pmatrix}r&s\\t&u\end{pmatrix}
\longmapsto
\begin{pmatrix}u&-s\\-t&r\end{pmatrix},
$$

and reduced trace and norm become ordinary trace and determinant.

This example also gives concrete zero divisors. The matrices

$$
e=\begin{pmatrix}1&0\\0&0\end{pmatrix},
\qquad
1-e=\begin{pmatrix}0&0\\0&1\end{pmatrix}
$$

are nonzero and satisfy $e(1-e)=0$. The nilpotent matrix

$$
n=\begin{pmatrix}0&1\\0&0\end{pmatrix}
$$

has $n^2=0$. Thus “has a zero divisor,” “has a nilpotent,” and “has an idempotent” give visibly different witnesses to the same split condition.

### 3.2 Hamilton's algebra

Over $\mathbf R$, the presentation

$$
\mathbf H=(-1,-1)_{\mathbf R}
$$

is Hamilton's quaternion algebra. Its norm is a sum of four squares and is positive on every nonzero element. The inverse formula therefore makes every nonzero quaternion invertible. Hence $\mathbf H$ is a division algebra.

The contrast with matrices is not merely that multiplication is noncommutative in one and not the other: both are noncommutative. The distinction is the existence of singular nonzero elements. In $M_2(\mathbf R)$, rank-one matrices are singular. In $\mathbf H$, positive definiteness of the norm forbids them.

Over $\mathbf C$, the same presentation splits. Indeed, $-1$ is a square, so

$$
(-1,-1)_{\mathbf C}\cong(1,-1)_{\mathbf C}\cong M_2(\mathbf C).
$$

This is the first example of a division algebra destroyed by scalar extension.

### 3.3 Zero divisors and division

For an arbitrary finite-dimensional algebra, the absence of zero divisors need not be easy to compare with simplicity. For a central simple algebra of degree two, the structure theorem makes the comparison exact.

If $B$ is division, it plainly has no nonzero zero divisors. If $B$ is not division, write $B\cong M_r(D)$. Degree two forces $r=2$ and $D=F$, so $B\cong M_2(F)$ and has the explicit zero divisors above. Therefore a quaternion algebra is either split or division, with no third case.

The norm gives a computational refinement:

$$
B\text{ is division}
\quad\Longleftrightarrow\quad
n_B\text{ is anisotropic}.
$$

One should not weaken “anisotropic” to a statement about some convenient coordinate plane. A form may have no zero involving only $x_0,x_1$ and still be isotropic in all four variables. For instance $(2,3)_{\mathbf Q}$ does not split merely because neither $2$ nor $3$ is a rational square; its splitting must be tested by the full norm form or by local symbols.

### 3.4 Idempotents and minimal left ideals

An idempotent $e^2=e$ decomposes a module into image and kernel. A division algebra has only the idempotents $0$ and $1$, because $e(e-1)=0$. In $M_2(F)$, every rank-one projection is a nontrivial idempotent.

Conversely, a nontrivial idempotent in a four-dimensional central simple algebra produces the proper nonzero left ideal $Be$. Its $F$-dimension is two. Left multiplication on $Be$ gives a homomorphism

$$
B\longrightarrow\operatorname{End}_F(Be)\cong M_2(F).
$$

Its kernel is a two-sided ideal and hence zero; equal dimensions make it an isomorphism. This argument is more than another splitting test. It explains where the two-dimensional vector space underlying a matrix realization comes from: it is a minimal left ideal cut out by an idempotent.

## 4. Equivalent tests for splitting

### 4.1 One dichotomy, many witnesses

Different problems naturally reveal different pieces of a quaternion algebra. A calculation may produce a norm-zero vector, a representation may produce an idempotent, and a field extension may produce matrices. It is essential to know that these witnesses all answer the same question.

We say that $B$ **splits over $F$** if $B\cong M_2(F)$. If $L/F$ is an extension, we say that $L$ splits $B$ if

$$
B_L=B\otimes_F L\cong M_2(L).
$$

Splitting belongs to the algebra and the base field, not to a presentation.

### 4.2 The splitting theorem

**Theorem 4.1 (equivalent splitting criteria).** Let $B$ be a quaternion algebra over a field $F$ of characteristic different from $2$. The following are equivalent:

1. $B\cong M_2(F)$.
2. $B$ is not a division algebra.
3. $B$ has a nonzero zero divisor.
4. $B$ has a nonzero element of reduced norm zero.
5. The norm form $n_B$ is isotropic.
6. $B$ has an idempotent other than $0$ and $1$.
7. $B$ has a two-dimensional left ideal.

**Proof strategy.** Most implications are immediate from the inverse formula. The only constructive step is to turn a singular element into a minimal left ideal, and central simplicity then identifies its action with all $2\times2$ matrices.

**Proof.** The degree-two structure dichotomy gives (1)$\Leftrightarrow$(2). A finite-dimensional algebra fails to be division precisely when left or right multiplication by some nonzero element is noninjective, giving (2)$\Leftrightarrow$(3). The inverse formula gives (3)$\Leftrightarrow$(4), and (4)$\Leftrightarrow$(5) is the definition of isotropy.

We saw that (6) produces the two-dimensional left ideal $Be$, hence (6)$\Rightarrow$(7). A two-dimensional left ideal $I$ gives a faithful action $B\to\operatorname{End}_F(I)$ and therefore (7)$\Rightarrow$(1). Finally, in the matrix algebra a rank-one projection supplies (6). $\square$

The theorem makes a useful counterpoint clear. A nonzero norm-zero element need not itself be idempotent: the nilpotent matrix in Section 3.1 is not. It is the existence of some singular element that forces a matrix realization, within which an idempotent can then be chosen.

### 4.3 Scalar extension and splitting fields

Every quaternion algebra splits over a finite separable extension. From a presentation, adjoining $\sqrt a$ is enough:

$$
(a,b)_F\otimes_FF(\sqrt a)\cong M_2(F(\sqrt a)).
$$

If $a$ was already a square, the algebra was split before extension. Thus every nonsplit quaternion algebra has a quadratic splitting field. More intrinsically, any maximal commutative subfield $E\subset B$ has degree two, and $B\otimes_FE\cong M_2(E)$.

The converse needs its degree hypothesis. If a quadratic field $E/F$ splits a quaternion algebra $B$, then $E$ embeds in $B$. One way to see this is to view the split algebra $B_E$ as endomorphisms of a two-dimensional $E$-space and descend a minimal left ideal; equivalently, use the embedding theorem for separable extensions of degree equal to the degree of a central simple algebra. We will exploit this equivalence locally and globally.

A finite separable extension of odd degree cannot split a quaternion division algebra. In Brauer-group language its class has order two and restriction followed by corestriction multiplies it by the odd degree. If restriction were zero, the original class would be zero. The local invariant formula later gives the sharper place-by-place version. Over the characteristic-zero arithmetic fields used below, every finite extension is separable.

### 4.4 Quadratic subfields

Let $B$ be division. Every nonscalar $x\in B$ has irreducible reduced characteristic polynomial of degree two: if it split over $F$, the equation

$$
(x-r)(x-s)=0
$$

would contradict division unless $x$ were scalar. Hence $F[x]$ is a quadratic field. Conversely every quadratic subfield is maximal commutative, because its dimension already equals the degree of $B$.

In the split algebra the situation is different but parallel. Every quadratic field $E/F$ embeds in $M_2(F)$ through its regular action on the two-dimensional $F$-space $E$. The split quadratic algebra $F\times F$ embeds as diagonal matrices. Thus “quadratic subalgebra” must sometimes mean a quadratic **étale** algebra, while “quadratic subfield” excludes the split case. Keeping that distinction prevents false claims at places where a global quadratic field splits.

### 4.5 The splitting conic

There is a projective-geometric way to package the same obstruction. To the presentation $(a,b)_F$ attach the smooth conic

$$
C_{a,b}:X^2-aY^2-bZ^2=0
$$

in $\mathbf P^2_F$. Then

$$
C_{a,b}(F)\ne\varnothing
\quad\Longleftrightarrow\quad
(a,b)_F\text{ splits}.
$$

If $(X:Y:Z)$ is a point with $Z\ne0$, division by $Z^2$ expresses $b$ as the norm of $(X+Y\sqrt a)/Z$. If $Z=0$, then $a$ is a square unless $X=Y=0$, which is not a projective point; a square first parameter already splits the algebra. Conversely, a norm expression $b=r^2-as^2$ gives the point $(r:s:1)$.

This conic is the variety of right ideals of reduced dimension one, often called the Severi--Brauer conic of $B$. In a split algebra such an ideal has ordinary $F$-dimension two and corresponds to a line in the underlying two-dimensional module. A rational point chooses such an ideal over $F$ and therefore chooses a matrix realization. The absence of a rational point is not a failure of the conic to exist: over any splitting field it becomes $\mathbf P^1$. The conic records precisely the descent obstruction from projective lines over a splitting field to a projective line over $F$.

For example, the real conic

$$
X^2+Y^2+Z^2=0
$$

has no real point and belongs to Hamilton's algebra. The conic

$$
X^2-2Y^2-7Z^2=0
$$

has the rational point $(3:1:1)$ and belongs to the split algebra $(2,7)_{\mathbf Q}$. These are the same computations as before, but projectivization removes irrelevant scalar multiples of a norm-zero quaternion.

Over a number field, the Hasse principle for conics says that $C(F)$ has a point exactly when $C(F_v)$ has a point for every place $v$. For these particular conics, that theorem is exactly the local--global splitting principle for quaternion algebras. The geometry and the Brauer invariant sequence express the same reciprocity obstruction.

## 5. Quadratic norms and cyclic algebras

### 5.1 Why a norm equation controls splitting

A presentation $(a,b)_F$ singles out the quadratic étale algebra

$$
E=F[t]/(t^2-a).
$$

Its nontrivial involution is $\sigma(t)=-t$. The remaining generator $j$ does two jobs: it implements $\sigma$ by conjugation and its square records $b$. Altering $j$ by an element of $E^\times$ changes $b$ by a norm. It is therefore natural that the class of $b$ in $F^\times/N_{E/F}(E^\times)$ measures whether the twisting can be removed.

When $a$ is nonsquare, $E=F(\sqrt a)$ and

$$
N_{E/F}(r+s\sqrt a)=r^2-a s^2.
$$

When $a$ is a square, $E\cong F\times F$ and its norm is $(x,y)\mapsto xy$, hence surjective. This split étale case is not an exception to the criterion; it is precisely the case in which the criterion is automatic.

### 5.2 The cyclic description

As a vector space,

$$
(a,b)_F=E\oplus Ej,
$$

with multiplication determined by

$$
j^2=b,
\qquad
jx=\sigma(x)j\quad(x\in E).
$$

This is the degree-two cyclic algebra $(E/F,\sigma,b)$. If $u\in E^\times$ and $j'=uj$, then

$$
(j')^2=u\sigma(u)j^2=N_{E/F}(u)b.
$$

This calculation proves directly that norm-equivalent parameters give isomorphic algebras. It also shows why the generator convention matters for cyclic algebras of higher degree. In degree two, however, $\sigma=\sigma^{-1}$, so no arithmetic-versus-geometric ambiguity changes the sign-valued Hilbert symbol.

### 5.3 The norm criterion

**Theorem 5.1 (quadratic norm criterion).** Let $F$ have characteristic different from $2$, let $a,b\in F^\times$, and put $E=F[t]/(t^2-a)$. Then

$$
(a,b)_F\text{ splits}
\quad\Longleftrightarrow\quad
b\in N_{E/F}(E^\times).
$$

If $a$ is nonsquare, this says exactly that $b=r^2-a s^2$ for some $r,s\in F$, not both zero.

**Proof strategy.** A norm expression gives an isotropic norm vector immediately. Conversely, an arbitrary isotropic vector is rearranged into a norm equation; the only exceptional coordinate pattern already forces $a$ to be a square.

**Proof.** If $b=r^2-a s^2$, then the quaternion

$$
x=r+si+j
$$

has norm $r^2-a s^2-b=0$ and is nonzero. The splitting theorem applies.

Conversely, suppose

$$
x_0^2-a x_1^2-bx_2^2+abx_3^2=0
$$

for a nonzero vector. If $x_2^2-a x_3^2\ne0$, then

$$
b=\frac{x_0^2-a x_1^2}{x_2^2-a x_3^2}
=N_{E/F}\left(\frac{x_0+x_1\sqrt a}{x_2+x_3\sqrt a}\right).
$$

If the denominator is zero, then $x_2^2=a x_3^2$. Unless $x_2=x_3=0$, this makes $a$ a square, and the étale norm is surjective. If $x_2=x_3=0$, isotropy gives $x_0^2=a x_1^2$ and again $a$ is a square because the vector is nonzero. $\square$

Equivalently, a quadratic extension $E=F(\sqrt a)$ splits $(a,b)_F$ automatically, while the element $b$ decides whether it was already split over $F$.

### 5.4 Worked norm equations

Consider $(2,7)_{\mathbf Q}$. Since

$$
7=3^2-2\cdot1^2=N_{\mathbf Q(\sqrt2)/\mathbf Q}(3+\sqrt2),
$$

the algebra splits. The element $3+i+j$ is a visible nonzero element of norm zero.

By contrast, $(-1,-1)_{\mathbf R}$ asks whether $-1$ is a norm from $\mathbf C/\mathbf R$. Those norms are the positive real numbers, so it is not; Hamilton's algebra is division.

The criterion is exact but not always computationally global. To decide whether $b$ is a norm from a quadratic number field, one may test all completions and use the cyclic Hasse norm theorem. In the quaternion setting this becomes the statement that the algebra splits globally exactly when it splits everywhere locally. The local symbols developed below turn those infinitely many apparent tests into finitely many calculations.

### 5.5 What the parameter class remembers

Fix a quadratic étale algebra $E/F$ with involution $\sigma$. Cyclic algebra theory gives a bijection

$$
F^\times/N_{E/F}(E^\times)
\longrightarrow
\ker\bigl(\operatorname{Br}(F)\to\operatorname{Br}(E)\bigr),
$$

$$
b\longmapsto[(E/F,\sigma,b)].
$$

For a quadratic field, every class on the right is represented by a quaternion algebra split by $E$. Thus, once the embedded quadratic field has been fixed, the coset of $b$ is exactly the remaining information in the Brauer class.

This assertion contains both directions of the parameter-change discussion. Multiplying $b$ by a norm visibly changes the generator and preserves the algebra. Conversely, if two cyclic presentations with the same embedded $E$ define the same Brauer class, their quotient parameter is a norm. That converse is not a consequence of merely comparing the four coefficients; it is the content of the relative Brauer-group classification.

The embedded copy of $E$ still matters. An abstract isomorphism

$$
(E/F,\sigma,b)\cong(E/F,\sigma,c)
$$

need not carry the displayed copy of $E$ to itself. Conjugacy of maximal étale subalgebras lets one adjust an isomorphism by an inner automorphism, after which the norm-coset comparison applies. This explains why the norm criterion classifies both the cyclic construction and the underlying quaternion algebra without making the chosen generators canonical.

For $E=F\times F$, the norm map is surjective and the relative Brauer group is zero. A cyclic algebra built from a split quadratic étale algebra is always a matrix algebra. For a genuine quadratic field, the quotient can be nontrivial. Over a nonarchimedean local field it has order two; over a number field it may be much larger as an abstract quotient, but its elements are controlled by local norm conditions, and the cyclic Hasse norm theorem detects the trivial coset.

There is also a useful elementwise recognition principle. If $x\in B\setminus F$ has nonsquare reduced discriminant

$$
\Delta(x)=\operatorname{Trd}(x)^2-4\operatorname{Nrd}(x),
$$

then $F[x]=F(\sqrt{\Delta(x)})$ is a quadratic subfield. Replacing $x$ by its trace-zero part

$$
x_0=x-\frac12\operatorname{Trd}(x)
$$

gives $x_0^2=\Delta(x)/4$. A second pure quaternion orthogonal to $x_0$ supplies the cyclic generator. Thus reduced trace and norm not only test invertibility; they recover the quadratic field from a single element and lead back to a presentation.

## 6. Brauer classes and algebraic operations

### 6.1 Matrix factors and the Brauer group

Tensor products of quaternion algebras have dimension sixteen and are usually not quaternion algebras. To record their essential division content without carrying matrix sizes, one uses the Brauer group. Two central simple $F$-algebras are **Brauer equivalent** if their underlying central division algebras are isomorphic, or equivalently if

$$
M_r(A)\cong M_s(C)
$$

for some positive integers $r,s$. Tensor product induces addition in $\operatorname{Br}(F)$, the split matrix algebras represent zero, and the inverse of $[A]$ is $[A^{\mathrm{op}}]$.

For quaternion algebras, equality of nonzero Brauer classes is especially strong. Two quaternion division algebras with the same class are isomorphic because each is already the division representative of that class. If one is split, equality forces both to split. Thus two quaternion algebras with equal Brauer class are isomorphic, even though the tensor-product calculation establishing equality may pass through a degree-four algebra.

This language separates two ideas that should not be confused. An isomorphism $B\cong C$ preserves the full algebra. A Brauer equivalence forgets matrix factors. The distinction disappears only when both algebras under comparison have degree two.

### 6.2 Opposites and exponent two

Canonical conjugation gives an $F$-algebra isomorphism

$$
B\xrightarrow{\sim}B^{\mathrm{op}},
\qquad x\longmapsto\bar x,
$$

because it reverses multiplication. Consequently

$$
[B]=[B^{\mathrm{op}}]=-[B]
$$

and therefore

$$
2[B]=0.
$$

Every quaternion class has exponent dividing two. The split class has exponent one; a division quaternion class has exponent exactly two.

One can see the same fact from a presentation. The tensor square of $(a,b)_F$ has trivial Brauer class by the bilinear identities below, since $b^2$ is a square. It follows that any finite separable field extension of odd degree preserves nonsplitting: restriction followed by corestriction multiplies $[B]$ by that odd degree, which acts as the identity on a nonzero element of order two.

### 6.3 Tensor identities

The two basic identities in the Brauer group are

$$
[(a,b)_F]+[(a,c)_F]=[(a,bc)_F]
$$

and

$$
[(a,b)_F]+[(c,b)_F]=[(ac,b)_F].
$$

They express bilinearity in the two square-class variables. For the first, regard both algebras as cyclic algebras for $F(\sqrt a)/F$. Tensoring adds their cyclic parameters multiplicatively; a matrix factor accounts for the doubled degree. The second follows from the first using symmetry $(a,b)\cong(b,a)$.

Some useful consequences are

$$
[(a,1)_F]=0,
\qquad
[(a,-a)_F]=0,
\qquad
[(a,b)_F]=[(a,bc^2)_F].
$$

The middle identity is also a norm calculation, since $-a=N_{F(\sqrt a)/F}(\sqrt a)$. Combining it with bilinearity gives familiar parameter transformations such as

$$
[(a,b)_F]=[(a,-ab)_F].
$$

Because both sides are quaternion algebras, these Brauer equalities are algebra isomorphisms. By contrast, the displayed sum identities themselves do **not** assert that a sixteen-dimensional tensor product is four-dimensional; they assert that it is a matrix algebra over the quaternion algebra on the right.

### 6.4 Extension of scalars

For an extension $L/F$, scalar extension sends

$$
(a,b)_F\longmapsto(a,b)_L
$$

and induces a restriction homomorphism

$$
\operatorname{Br}(F)\longrightarrow\operatorname{Br}(L).
$$

Reduced trace and norm commute with scalar extension. The norm form simply acquires coefficients in $L$, so it may become isotropic even when it was anisotropic over $F$.

If $F$ is a number field and $v$ a place, the completion $F_v$ is such an extension. We write

$$
B_v=B\otimes_FF_v.
$$

At this stage $B_v$ could in principle be split or division independently at many places. Local classification and global reciprocity will show exactly which patterns occur and why only finitely many places can be division.

### 6.5 Restriction, corestriction, exponent, and index

Scalar extension is only one direction of functoriality. For a finite separable extension $L/F$, there is also a transfer

$$
\operatorname{Cor}_{L/F}:\operatorname{Br}(L)\longrightarrow\operatorname{Br}(F).
$$

The two operations satisfy

$$
\operatorname{Cor}_{L/F}\bigl(\operatorname{Res}_{L/F}(\alpha)\bigr)
=[L:F]\alpha.
$$

This identity is the conceptual reason that odd-degree extensions cannot destroy a nonzero quaternion class. If $\alpha$ has order two and its restriction is zero, then

$$
0=\operatorname{Cor}(0)=[L:F]\alpha.
$$

For odd $[L:F]$, multiplication by the degree acts as the identity on a group of exponent two, so $\alpha=0$.

Two numerical invariants of a Brauer class must be distinguished. Its **exponent** is its order in the Brauer group. Its **index** is the degree of the central division algebra representing it. The exponent divides the index and they have the same prime divisors. For a quaternion division algebra both are two. A class of exponent two can nevertheless have index four or larger over a general field; it need not be represented by a quaternion algebra. This is why the number-field index theorem is used explicitly in the global existence proof: local invariants in $\{0,1/2\}$ force global index at most two there, a conclusion unavailable over arbitrary fields.

For local fields the invariant map makes the functorial laws numerical. If $L/F$ is finite and $\alpha\in\operatorname{Br}(F)$, then

$$
\operatorname{inv}_L(\operatorname{Res}_{L/F}\alpha)
=[L:F]\operatorname{inv}_F(\alpha).
$$

If $\beta\in\operatorname{Br}(L)$, then

$$
\operatorname{inv}_F(\operatorname{Cor}_{L/F}\beta)
=\operatorname{inv}_L(\beta).
$$

Applying the second formula to a restriction recovers the first compatibility with transfer. Over number fields, corestriction sums these local contributions over all places above a fixed place. More precisely, for $w\mid v$,

$$
\operatorname{inv}_v\bigl((\operatorname{Cor}_{L/F}\beta)_v\bigr)
=\sum_{w\mid v}\operatorname{inv}_w(\beta_w).
$$

These formulas prevent a common normalization error. Restriction multiplies an invariant by a local degree; corestriction does not multiply each local invariant but adds the invariants over the branches. The global sum remains unchanged because summing first over $w$ or first over $v$ gives the same finite sum.

## 7. Hilbert symbols over local fields

### 7.1 A binary sign for a local splitting problem

Let $K$ be a local field of characteristic different from $2$: in this book, $K$ is $\mathbf R$, $\mathbf C$, or a finite extension of $\mathbf Q_p$. For $a,b\in K^\times$, define the **Hilbert symbol**

$$
(a,b)_K=
\begin{cases}
+1,&(a,b)_K\text{ as an algebra is split},\\
-1,&(a,b)_K\text{ as an algebra is division}.
\end{cases}
$$

The same typography is traditionally used for the algebra and for the sign. Context distinguishes them: $(a,b)_K$ after “the algebra” means the four-dimensional algebra, while an equality $(a,b)_K=\pm1$ means the symbol. When ambiguity would distract, we write $B=(a,b)_K$ for the algebra.

The norm criterion gives the fundamental interpretation

$$
(a,b)_K=+1
\quad\Longleftrightarrow\quad
b\in N_{K(\sqrt a)/K}(K(\sqrt a)^\times),
$$

with the quadratic étale algebra understood when $a$ is a square. Thus the Hilbert symbol is the quadratic norm-residue symbol.

### 7.2 Square classes, symmetry, and bilinearity

The Hilbert symbol depends only on the images of $a$ and $b$ in

$$
K^\times/K^{\times 2}.
$$

It is symmetric and bimultiplicative:

$$
(a,b)_K=(b,a)_K,
$$

$$
(aa',b)_K=(a,b)_K(a',b)_K,
\qquad
(a,bb')_K=(a,b)_K(a,b')_K.
$$

Symmetry comes from interchanging the generators. Bilinearity comes from the tensor identities in the Brauer group, together with the fact that the local two-torsion Brauer group has only the split and quaternion-division classes. In particular,

$$
(a,-a)_K=1,
\qquad
(a,1-a)_K=1\quad(a\ne1).
$$

The second identity is the norm calculation

$$
1-a=N_{K(\sqrt a)/K}(1+\sqrt a).
$$

These relations are often more efficient than a direct formula. They also show why signs alone still retain group structure: multiplication of signs is addition of two-torsion Brauer invariants.

For nonsquare $a$, the map $b\mapsto(a,b)_K$ is the unique nontrivial character of the index-two norm quotient

$$
K^\times/N_{K(\sqrt a)/K}(K(\sqrt a)^\times).
$$

It is not the assertion that every nontrivial square class gives a different character without qualification; local nondegeneracy of the Hilbert pairing is the theorem that supplies that stronger statement.

### 7.3 The archimedean fields

Over $\mathbf C$, every nonzero element is a square, so every quaternion algebra splits:

$$
(a,b)_{\mathbf C}=+1.
$$

There is no complex ramification.

Over $\mathbf R$, square classes are represented by $1$ and $-1$. The norm group from $\mathbf C/\mathbf R$ is $\mathbf R_{>0}$. Therefore

$$
(a,b)_{\mathbf R}=-1
\quad\Longleftrightarrow\quad
a<0\text{ and }b<0.
$$

The unique division algebra is Hamilton's $\mathbf H$. If either parameter is positive, one parameter is a square after using symmetry, and the algebra is $M_2(\mathbf R)$.

This classification is sensitive only to signs, but both signs are necessary. For example $(-1,2)_{\mathbf R}$ splits even though its first parameter defines $\mathbf C$; the second parameter is the positive norm $N_{\mathbf C/\mathbf R}(\sqrt2)$.

### 7.4 Odd residue characteristic

Let $K$ be nonarchimedean with odd residue cardinality $q$. Choose a uniformizer $\pi$. Write

$$
a=\pi^\alpha u,
\qquad
b=\pi^\beta v,
$$

where $u,v\in\mathcal O_K^\times$ and only the parities of $\alpha,\beta$ matter. Let $\kappa=\mathcal O_K/\mathfrak m_K$ and let

$$
\left(\frac{\bar u}{\kappa}\right)\in\{\pm1\}
$$

denote the quadratic character of the residue field, with value $1$ on nonzero squares and $-1$ on nonsquares. Then

$$
(a,b)_K
=(-1)^{\alpha\beta(q-1)/2}
\left(\frac{\bar u}{\kappa}\right)^\beta
\left(\frac{\bar v}{\kappa}\right)^\alpha.
$$

The formula is best understood through three generators. Two units give symbol $1$: an unramified or split quadratic extension has surjective norm on units. A nonsquare unit $u$ and a uniformizer satisfy $(u,\pi)_K=-1$, because norms from the unramified quadratic extension have even valuation. Finally $(\pi,\pi)_K=(\pi,-1)_K$, using $(\pi,-\pi)=1$, and the residue character of $-1$ gives the first sign. Bilinearity then gives the formula.

As a worked example, over $\mathbf Q_3$,

$$
(2,3)_3=\left(\frac23\right)=-1.
$$

Over $\mathbf Q_5$,

$$
(2,3)_5=1
$$

because both valuations are zero. This does not say that $2$ or $3$ is a square in $\mathbf Q_5$; it says that the quaternion algebra determined by the pair is split.

### 7.5 Dyadic fields and the rational dyadic formula

Residue characteristic two is genuinely different. The residue field has odd-order multiplicative group, so its quadratic character cannot encode the larger group $K^\times/K^{\times 2}$. Any formula obtained by blindly substituting $q=2$ into the odd-residue formula is false.

The robust statement over every dyadic local field remains the norm test:

$$
(a,b)_K=1
\quad\Longleftrightarrow\quad
b\text{ is a norm from }K(\sqrt a).
$$

One computes that norm group using the valuation and the deeper unit filtration. The answer depends on the ramification index of $K/\mathbf Q_2$ and cannot be compressed into one residue-Legendre-symbol formula valid for all dyadic fields.

For $K=\mathbf Q_2$ there is a convenient explicit formula. Write

$$
a=2^\alpha u,
\qquad
b=2^\beta v,
$$

with $u,v$ odd and $\alpha,\beta\in\mathbf Z$. Then

$$
(a,b)_2=(-1)^E,
$$

where, modulo $2$,

$$
E=
\frac{u-1}{2}\frac{v-1}{2}
+\alpha\frac{v^2-1}{8}
+\beta\frac{u^2-1}{8}.
$$

All three displayed fractions are integers. The formula follows from a small square-class calculation rather than from the odd-residue formula. The group $\mathbf Q_2^\times/\mathbf Q_2^{\times2}$ is generated by the classes of $-1$, $2$, and $5$: the valuation gives the factor $2$, while an odd unit is a square precisely when it is congruent to $1$ modulo $8$. On these generators the norm criterion gives

$$
(-1,-1)_2=-1,
\qquad
(-1,2)_2=(-1,5)_2=1,
$$

$$
(2,2)_2=(5,5)_2=1,
\qquad
(2,5)_2=-1.
$$

For the positive entries one may use the explicit norms $2=1^2+1^2$, $5=1^2+2^2$, $2=2^2-2\cdot1^2$, and $4-5=-1$ together with $N_{\mathbf Q_2(\sqrt5)/\mathbf Q_2}(\sqrt5)=-5$ and multiplicativity. For $(2,5)_2$, valuation first forces any solution of $x^2-2y^2=5$ to have $x,y\in\mathbf Z_2$ and $x$ odd; reduction modulo $8$ then gives only $1$ or $7$, never $5$. Valuation likewise makes any solution of $x^2+y^2=-1$ integral with at least one of $x,y$ odd, and reduction modulo $4$ is impossible. Symmetry and bilinearity now determine the full table, and expanding $a=2^\alpha u$ and $b=2^\beta v$ gives the stated exponent $E$.

For instance,

$$
(2,3)_2=(-1)^{(3^2-1)/8}=-1,
$$

whereas

$$
(-1,-3)_2=+1.
$$

The first calculation will combine with the place $3$ to produce an indefinite rational quaternion algebra ramified at exactly $2$ and $3$. The second allows $(-1,-3)_{\mathbf Q}$ to ramify at $3$ and infinity but not at $2$.

### 7.6 A local calculation laboratory

The formula at odd residue characteristic becomes more memorable when organized by the quadratic extension $K(\sqrt a)$. Let $u$ be a unit of nonsquare residue and let $\pi$ be a uniformizer.

If $a=u$, the extension is unramified quadratic. Its norm group consists exactly of elements of even valuation:

$$
N_{K(\sqrt u)/K}(K(\sqrt u)^\times)
=\{x\in K^\times:v(x)\equiv0\pmod2\}.
$$

The norm on units is surjective. Accordingly,

$$
(u,b)_K=(-1)^{v(b)}.
$$

This gives the standard division presentation $(u,\pi)_K$.

If $a=\pi$, the extension is ramified quadratic. A unit $v$ is a norm precisely when its residue is a square; valuations impose no parity restriction because the norm of a uniformizer upstairs has valuation one. Thus

$$
(\pi,v)_K=\left(\frac{\bar v}{\kappa}\right),
$$

while

$$
(\pi,\pi)_K=\left(\frac{-1}{\kappa}\right).
$$

The last equality follows from replacing the second parameter $\pi$ by $-1$, since $-\pi$ is a norm from $K(\sqrt\pi)$.

These statements yield the entire table on the four square classes

$$
1,\quad u,\quad \pi,\quad u\pi.
$$

For example, if $q\equiv1\pmod4$, then $-1$ is a residue square and $(\pi,\pi)_K=1$; if $q\equiv3\pmod4$, it equals $-1$. In either case $(u,\pi)_K=-1$. The pairing is nondegenerate: for every nonsquare $a$, some $b$ has $(a,b)_K=-1$. Equivalently, the norm group of each quadratic field has index two.

Over $\mathbf Q_5$, take $u=2$. Then $(2,5)_5=-1$, so $(2,5)_{\mathbf Q_5}$ is the unique division algebra. Since $5\equiv1\pmod4$,

$$
(5,5)_5=1.
$$

Over $\mathbf Q_3$, take $u=-1$. Then $(-1,3)_3=-1$ and $(3,3)_3=-1$, the latter because $-1$ is not a square modulo $3$. Bilinearity gives

$$
(-3,3)_3=(-1,3)_3(3,3)_3=1.
$$

These calculations also warn against a common shortcut: the fact that both $a$ and $b$ are nonsquares does not determine the symbol. The relative position of their square classes under the Hilbert pairing is what matters.

At $2$, the eight square classes of $\mathbf Q_2^\times$ may be represented by

$$
\{1,3,5,7,2,6,10,14\}.
$$

The dyadic formula determines the full pairing table from these representatives. Some useful entries are

$$
(-1,-1)_2=-1,
\qquad
(2,3)_2=-1,
\qquad
(2,5)_2=-1,
\qquad
(2,7)_2=1.
$$

The last two follow from $(v^2-1)/8$ for $v=5,7$. The larger square-class group is exactly why “unit versus uniformizer” no longer gives a complete dyadic classification.

### 7.7 Nondegeneracy and the geometry of square classes

Bilinearity says that the symbol is a pairing; nondegeneracy says that it loses no square-class information. This matters whenever local conditions are prescribed, because it guarantees a parameter capable of detecting each nonsquare class.

**Theorem 7.1 (local nondegeneracy).** Let $K$ be $\mathbf R$ or a nonarchimedean local field of characteristic different from $2$. The pairing

$$
K^\times/K^{\times2}\times K^\times/K^{\times2}
\longrightarrow\{\pm1\},
\qquad(a,b)\longmapsto(a,b)_K
$$

is symmetric, bilinear, and nondegenerate. Equivalently, if $(a,b)_K=1$ for every $b\in K^\times$, then $a$ is a square.

**Proof strategy.** For a nonsquare $a$, the quadratic field $E=K(\sqrt a)$ has a norm subgroup of index two. Choosing any element outside that subgroup gives a nontrivial symbol.

**Proof.** Symmetry and bilinearity were established in Section 7.2. Suppose that $a$ is nonsquare. Then $E/K$ is quadratic. Local reciprocity, or the local norm-index theorem in its quadratic form, gives

$$
[K^\times:N_{E/K}(E^\times)]=[E:K]=2.
$$

Thus some $b\in K^\times$ is not a norm. The norm criterion yields $(a,b)_K=-1$. Hence the left radical is trivial; symmetry makes the right radical trivial as well. Over $\mathbf R$, the same argument is the elementary identity $N_{\mathbf C/\mathbf R}(\mathbf C^\times)=\mathbf R_{>0}$. $\square$

For a fixed nonsquare $a$, the orthogonal hyperplane

$$
a^\perp=\{b\in K^\times/K^{\times2}:(a,b)_K=1\}
$$

is exactly the image of the norm group from $K(\sqrt a)$. Over a nonarchimedean field of odd residue characteristic, the square-class space has dimension two over $\mathbf F_2$, so every nonzero class has an orthogonal line. Over $\mathbf Q_2$ it has dimension three, and each nonzero class has an orthogonal plane. This linear-algebra picture explains both the compact odd-prime table and the richer dyadic one.

The pairing need not be alternating. Since $(a,-a)_K=1$, bilinearity gives

$$
(a,a)_K=(a,-1)_K.
$$

Thus $(a,a)_K$ can be $-1$ when $-1$ is not orthogonal to $a$. For example,

$$
(-1,-1)_{\mathbf R}=-1,
\qquad
(-1,-1)_2=-1.
$$

Calling the pairing symplectic would therefore be wrong unless $-1$ is a square in $K$. When $-1$ is a square, the pairing is alternating and the square-class space has even dimension.

There is also a direct algebraic consequence. Given a nonsquare $a$, exactly half of the square classes $b$ yield the division algebra and half yield the split algebra. The statement is literal because the square-class group of a nonarchimedean local field of characteristic zero is finite. It does not mean half of the elements of $K^\times$ in a measure-theoretic sense; each square class is an open coset, and their measures depend on normalization.

## 8. Local classification and local invariants

### 8.1 Why there is only one division algebra

Let $K$ be a nonarchimedean local field. General local Brauer theory gives a canonical invariant isomorphism

$$
\operatorname{inv}_K:\operatorname{Br}(K)\xrightarrow{\sim}\mathbf Q/\mathbf Z.
$$

A quaternion class has exponent dividing two, so its invariant is either $0$ or $1/2$. Invariant zero means split. There is exactly one nonzero possibility, and its division representative has index two and dimension four. Consequently:

**Theorem 8.1 (local quaternion classification).** Over a nonarchimedean local field $K$, every quaternion algebra is either $M_2(K)$ or the unique quaternion division algebra over $K$.

This is more than a count based on the Hilbert symbol. Here is the Brauer-theoretic mechanism. Let $K_2/K$ be the unramified quadratic extension and let $\varphi$ denote arithmetic Frobenius. For a uniformizer $\pi$, the cyclic algebra

$$
(K_2/K,\varphi,\pi)
$$

has invariant $1/2$. Indeed, norms from $K_2$ have even valuation, so $\pi$ is not a norm and the algebra is nonsplit. Local cyclic theory identifies every class killed by $K_2$ with a parameter in $K^\times/N_{K_2/K}(K_2^\times)$, a group of order two. General local invariant theory says every degree-two class is killed by the unramified quadratic extension. Thus there is precisely one nonzero quaternion class.

This proof works in residue characteristic two as well. No odd-residue formula was used; the valuation of norms from an unramified quadratic extension still detects the nontrivial class.

### 8.2 The invariant normalization

For a quaternion algebra $B/K$, our convention is

$$
\operatorname{inv}_K(B)=
\begin{cases}
0,&B\cong M_2(K),\\
\frac12,&B\text{ is division}.
\end{cases}
$$

It is related to the sign symbol by

$$
(a,b)_K=(-1)^{2\operatorname{inv}_K((a,b)_K)}.
$$

Thus addition of invariants corresponds to multiplication of signs.

The normalization agrees with arithmetic reciprocity: if $K_2/K$ is unramified quadratic, $\varphi$ is arithmetic Frobenius, and $\pi$ is a uniformizer, then

$$
\operatorname{inv}_K(K_2/K,\varphi,\pi)=\frac12.
$$

For degree two, replacing arithmetic Frobenius by geometric Frobenius does not change the generator, since $\varphi^{-1}=\varphi$. This happy accident should not be generalized to cyclic algebras of larger degree. The Brauer invariant itself is canonical; only a cyclic presentation used to calculate it has a generator convention.

The normalization is functorial in the precise form needed below. If $L/K$ is a finite extension of nonarchimedean local fields and $A$ is a central simple $K$-algebra, then

$$
\operatorname{inv}_L(A\otimes_KL)
=[L:K]\operatorname{inv}_K(A)
\qquad\text{in }\mathbf Q/\mathbf Z.
$$

For an unramified cyclic presentation this follows by comparing Frobenius and the valuation of its parameter; the general statement follows because unramified cyclic classes generate the local Brauer group. In particular, restriction to an even-degree extension kills the invariant $1/2$, whereas restriction to an odd-degree extension preserves it. This establishes the base-change rule before its first use in the embedding and splitting arguments.

At the archimedean places we use the compatible conventions

$$
\operatorname{Br}(\mathbf C)=0,
\qquad
\operatorname{Br}(\mathbf R)=\{0,\tfrac12\},
$$

with $\mathbf H$ having invariant $1/2$.

### 8.3 A concrete division algebra

Choose $d\in K^\times$ such that $K(\sqrt d)/K$ is the unramified quadratic extension. Then

$$
D=(d,\pi)_K
$$

is the unique quaternion division algebra. The norm criterion makes the reason transparent: $\pi$ has odd valuation, whereas every norm from an unramified quadratic extension has even valuation.

When the residue characteristic is odd, $d$ may be chosen to be a unit with nonsquare residue. In residue characteristic two, “nonsquare residue” is not the right instruction, since every element of the finite residue field has a unique square root. One instead chooses a unit or other element defining the unramified quadratic extension via its correct unramified polynomial. The presentation $(d,\pi)$ still exists because the characteristic of $K$ is zero, but the method of finding $d$ is different.

Every other nonsplit presentation $(a,b)_K$ defines an algebra isomorphic to $D$, even when neither parameter visibly describes the unramified quadratic extension. The Hilbert symbol determines the algebra, not a privileged pair of generators.

### 8.4 Local quadratic embeddings

Let $E/K$ be a quadratic étale algebra. If $B=M_2(K)$, then every $E$ embeds: a field acts on itself by left multiplication, and $K\times K$ embeds diagonally. If $B=D$ is division, the split algebra $K\times K$ cannot embed because it contains a nontrivial idempotent, while every quadratic **field** extension embeds.

For the last assertion, scalar extension multiplies the invariant by the degree:

$$
\operatorname{inv}_E(D\otimes_KE)=2\cdot\frac12=0.
$$

Thus $E$ splits $D$, and the degree-two embedding theorem gives $E\hookrightarrow D$. We obtain the compact local rule:

$$
E\hookrightarrow B
\quad\Longleftrightarrow\quad
E\text{ is a field whenever }B\text{ is division}.
$$

This rule is the local input for the global quadratic embedding criterion.

### 8.5 Local splitting extensions and norm groups

The invariant formula describes every finite local splitting extension at once. If $D/K$ is the quaternion division algebra and $L/K$ is finite, then

$$
D\otimes_KL\text{ splits}
\quad\Longleftrightarrow\quad
[L:K]\text{ is even}.
$$

Indeed, restriction sends $1/2$ to $[L:K]/2$ in $\mathbf Q/\mathbf Z$. Thus an odd extension preserves the unique division class, while an even extension kills it. For arbitrary quaternion $B$, a split algebra remains split under every extension.

The assertion is about a field extension. If $L=K\times K$ is the split quadratic étale algebra, then

$$
D\otimes_KL\cong D\times D,
$$

not a matrix algebra over a field. This distinction is exactly what appears when a global quadratic field splits at a place.

For a fixed quadratic field $E/K$, the norm criterion and local norm-index theorem identify

$$
K^\times/N_{E/K}(E^\times)\cong\{\pm1\}.
$$

The nontrivial coset consists of the parameters $b$ for which $(E/K,\sigma,b)$ is the division algebra. Consequently all nonnorm parameters produce isomorphic quaternion algebras; however different displayed parameters may conceal the fact that their quotient is a norm.

There are three standard local shapes for $E/K$.

- If $E\cong K\times K$, every element is a norm and every associated algebra splits.
- If $E/K$ is unramified quadratic, the norm group consists of elements of even valuation.
- If the residue characteristic is odd and $E/K$ is ramified quadratic, norm valuations are unrestricted, while the residue of a norm unit must be a square; principal-unit surjectivity makes that condition sufficient.

At dyadic places the third description needs refinement: norms on deeper unit layers depend on the quadratic extension. The index remains two, but the correct subgroup may distinguish congruence classes modulo $4$, $8$, or deeper powers in ramified base fields.

The local invariant also identifies the reduced norm group of the division algebra itself. In fact

$$
\operatorname{Nrd}(D^\times)=K^\times.
$$

This surjectivity should not be confused with norms from a quadratic subfield, which have index two. One route to surjectivity uses an unramified quadratic maximal subfield to obtain every even valuation and a ramified quadratic maximal subfield to obtain odd valuations; the unit norm images together fill the units. More generally, reduced norms from central division algebras over nonarchimedean local fields are surjective. The quaternion Hilbert symbol measures a quadratic **field** norm obstruction, not an obstruction to reduced norms from $D$.

## 9. Global ramification and reciprocity

### 9.1 Seeing a global algebra place by place

Let $F$ now be a number field and $B$ a quaternion algebra over $F$. For every place $v$, set

$$
B_v=B\otimes_FF_v.
$$

Local classification says that $B_v$ is split or division. We say that $B$ **ramifies at $v$** in the division case and **splits at $v$** in the matrix case. Write

$$
\operatorname{Ram}(B)=\{v:B_v\text{ is division}\}.
$$

If $B=(a,b)_F$, then

$$
v\in\operatorname{Ram}(B)
\quad\Longleftrightarrow\quad
(a,b)_{F_v}=-1
\quad\Longleftrightarrow\quad
\operatorname{inv}_v(B_v)=\frac12.
$$

The definition does not depend on the presentation. Indeed, it is stated directly in terms of the completed algebra.

### 9.2 The ramification set

The ramification set is the most economical global label for a quaternion algebra. It includes finite and real places. Complex places never occur. To separate the finite part, write

$$
\operatorname{Ram}_f(B)=\{v<\infty:v\in\operatorname{Ram}(B)\},
$$

and define the **reduced discriminant of the algebra** by

$$
\mathfrak d(B)=\prod_{v\in\operatorname{Ram}_f(B)}\mathfrak p_v.
$$

This is a squarefree ideal. It records only finite ramification; the ramified real places must be stated separately. In this book the notation belongs solely to the algebra $B$. Discriminants of orders, maximal and Eichler orders, integral ideals in $B$, and their local exponents require additional integral structure and are reserved for the next book.

Two algebras can have the same finite discriminant and differ at infinity if the number field has several real places. Thus $\mathfrak d(B)$ alone is not a complete invariant unless the archimedean behavior has separately been fixed.

### 9.3 Finiteness and the infinite places

Only finitely many places ramify. To see this from a presentation $B=(a,b)_F$, exclude the finite places dividing $2$, $a$, or $b$, with fractional valuations interpreted by clearing denominators. At every remaining place, $a$ and $b$ are units and the residue characteristic is odd; the local formula gives symbol $+1$. There are only finitely many excluded finite places and finitely many archimedean places.

At a complex place, $B_v\cong M_2(\mathbf C)$ automatically. At a real place corresponding to an embedding $\tau:F\hookrightarrow\mathbf R$, the algebra ramifies exactly when

$$
\tau(a)<0\quad\text{and}\quad\tau(b)<0.
$$

This criterion depends on the chosen presentation only in appearance: any other presentation yields the same split or Hamilton algebra after applying $\tau$.

The finite exceptional set in the preceding argument is usually larger than the actual ramification set. A prime dividing $2ab$ is merely a candidate and may still split. Local calculation, followed by the global parity check, finds the exact set.

### 9.4 Hilbert reciprocity and parity

The local symbols of one global pair cannot be prescribed independently.

**Theorem 9.1 (Hilbert reciprocity).** For $a,b\in F^\times$,

$$
\prod_v(a,b)_{F_v}=1.
$$

Equivalently,

$$
\sum_v\operatorname{inv}_v((a,b)_{F_v})=0
\qquad\text{in }\mathbf Q/\mathbf Z.
$$

Both expressions are finite because almost every local symbol is $+1$. The invariant form is the degree-two part of the global Brauer invariant sequence

$$
0\longrightarrow\operatorname{Br}(F)
\longrightarrow\bigoplus_v\operatorname{Br}(F_v)
\xrightarrow{\sum\operatorname{inv}_v}\mathbf Q/\mathbf Z
\longrightarrow0.
$$

Every ramified quaternion place contributes $1/2$. Therefore

$$
|\operatorname{Ram}(B)|\equiv0\pmod2.
$$

The parity counts finite and real places together. Complex places contribute nothing. Omitting real places gives false conclusions: Hamilton's algebra over $\mathbf Q$ ramifies at $2$ and at infinity, not at a lone finite prime.

Reciprocity is also a powerful error detector. Once all but one candidate local symbols have been computed, the final one is forced. This does not replace the dyadic theory, but it often avoids a second delicate dyadic calculation.

### 9.5 Reciprocity as a global norm statement

Fix $a\in F^\times$ and let $E=F(\sqrt a)$ be a quadratic field. For each place $v$, the character

$$
b\longmapsto(a,b)_{F_v}
$$

detects whether $b$ is a norm from the quadratic étale algebra $E\otimes_FF_v$. Hilbert reciprocity says that a global element $b$ is a local nonnorm at an even number of places:

$$
\prod_v(a,b)_{F_v}=1.
$$

The cyclic Hasse norm theorem supplies the converse at the trivial pattern:

$$
b\in N_{E/F}(E^\times)
\quad\Longleftrightarrow\quad
b\in N_{E_v/F_v}(E_v^\times)\text{ for every }v.
$$

Here $E_v=E\otimes_FF_v$; at a split place its norm is simply multiplication $F_v^\times\times F_v^\times\to F_v^\times$ and is surjective. At a real place where $E_v=\mathbf C$, the local norm condition is positivity.

The implications line up as follows:

$$
\begin{array}{ccccc}
b\text{ global norm}
&\Longleftrightarrow&(a,b)_F\text{ split}
&\Longleftrightarrow&\operatorname{Ram}((a,b)_F)=\varnothing,\\
&&\Updownarrow&&\\
&& (a,b)_{F_v}=1\text{ for every }v.&&
\end{array}
$$

The lower-to-upper implication uses global Brauer injectivity, or equivalently the Hasse norm theorem for the cyclic quadratic extension. The product formula alone is weaker: it says the number of failures is even, not that there are no failures.

Over $\mathbf Q$, quadratic reciprocity can be recovered by comparing the local factors of $(p,q)$ for distinct odd primes $p$ and $q$. Only $2,p,q,$ and infinity can contribute. The real symbol is $1$, and

$$
(p,q)_p=\left(\frac qp\right),
\qquad
(p,q)_q=\left(\frac pq\right),
$$

while

$$
(p,q)_2=(-1)^{\frac{p-1}{2}\frac{q-1}{2}}.
$$

The product formula yields

$$
\left(\frac pq\right)\left(\frac qp\right)
=(-1)^{\frac{p-1}{2}\frac{q-1}{2}}.
$$

Thus classical quadratic reciprocity is the rational shadow of Hilbert reciprocity. The places $2$ and infinity are not corrections added after the fact; they are indispensable local factors in the global relation.

### 9.6 Global reduced norms and positivity

Quadratic subfield norms have index two locally, but reduced norms from the whole quaternion algebra behave differently. At finite places they are surjective even in the division case. The only global obstruction comes from Hamiltonian real places.

**Theorem 9.2 (reduced norm theorem for quaternion algebras).** Let $B$ be a quaternion algebra over a number field $F$. Then

$$
\operatorname{Nrd}(B^\times)
=\{c\in F^\times:\tau(c)>0
\text{ for every real }\tau\in\operatorname{Ram}(B)\}.
$$

In particular, if $B$ is split at every real place, its reduced norm map is surjective.

**Proof strategy.** Necessity is the positivity of the Hamilton norm. For sufficiency, view $\operatorname{Nrd}(x)=c$ as a quadratic-form representation problem, solve it at every completion, and apply the local--global theorem for quadratic forms. Anisotropy of the quaternion norm rules out a solution at infinity in the homogenizing coordinate.

**Proof.** If $c=\operatorname{Nrd}(x)$ and $v$ is a ramified real place, then $B_v\cong\mathbf H$ and its reduced norm is the positive-definite sum of four squares. Hence $c$ is positive at $v$.

Conversely, suppose $c$ has the stated signs. If $B$ is globally split, identify it with $M_2(F)$; then

$$
\begin{pmatrix}c&0\\0&1\end{pmatrix}
$$

has determinant $c$, so assume that $B$ is division. Let $n_B$ be its reduced norm form and consider the five-dimensional quadratic form

$$
q_c=n_B\perp\langle-c\rangle.
$$

We show that $q_c$ is isotropic over every completion $F_v$. At a finite place, if $B_v$ is split, determinants represent every nonzero element. If $B_v$ is division, the local reduced norm map is surjective by Section 8.5. At a complex place every quaternion algebra is split. At a real split place determinants are again surjective. At a real ramified place, the Hamilton norm represents precisely the positive numbers, and the hypothesis gives $c>0$. Thus in every case there is $x_v\in B_v^\times$ with $n_B(x_v)=c$, so $(x_v,1)$ is an isotropic vector for $q_c$.

The local--global theorem for quadratic forms now makes $q_c$ isotropic over $F$. Choose a nonzero pair $(x,t)\in B\oplus F$ with

$$
n_B(x)=ct^2.
$$

If $t=0$, then $n_B(x)=0$. Since $B$ is division, its norm form is anisotropic, forcing $x=0$, contrary to the choice of a nonzero pair. Hence $t\ne0$, and

$$
\operatorname{Nrd}(x/t)=c.
$$

The element $x/t$ is invertible because its norm is nonzero. This proves sufficiency. $\square$

The theorem separates two norm phenomena that are easy to conflate. For a quadratic field $E\subset B$, the field norm subgroup $N_{E/F}(E^\times)$ can have many local index-two conditions. Allowing all of $B^\times$ removes every finite-place condition; only positivity at ramified real places survives.

For a totally definite algebra over a totally real field, the reduced norm image is exactly the group of totally positive elements. For an indefinite quaternion algebra over $\mathbf Q$, the reduced norm is all of $\mathbf Q^\times$, even if the algebra is division at finite primes. This is another sharp distinction between global division and definiteness.

## 10. The local--global classification

### 10.1 The classification theorem

Ramification is not merely an invariant; it is a complete invariant with one exact constraint.

**Theorem 10.1 (local--global classification).** Let $F$ be a number field.

1. Two quaternion algebras over $F$ are isomorphic if and only if they ramify at the same places.
2. The ramification set of a quaternion algebra is a finite even set of noncomplex places.
3. Conversely, every finite even set $S$ of finite or real places of $F$ occurs as the ramification set of a quaternion algebra, unique up to $F$-algebra isomorphism.

The theorem converts a noncommutative algebra into finite combinatorial data. It is the main construction principle used later: specify local division behavior where it is needed, check parity, and obtain one global algebra with no further ambiguity.

### 10.2 Why uniqueness is global

Suppose $B$ and $C$ have the same ramification set. At every place their invariants agree: both are $0$ off the set and $1/2$ on it. Hence the Brauer class

$$
[B]-[C]
$$

has zero localization at every place. Injectivity of the global Brauer map forces $[B]=[C]$. Since both have degree two, equality of Brauer classes implies $B\cong C$.

This proof clarifies why checking many local presentations independently is enough. One does not need to glue local generator choices. Local invariants glue at the level of the Brauer class, and degree two then recovers the algebra itself.

It also proves the Hasse splitting principle for quaternion algebras:

$$
B\cong M_2(F)
\quad\Longleftrightarrow\quad
B_v\cong M_2(F_v)\text{ for every }v.
$$

Combining this with the norm criterion recovers the Hasse norm theorem for the particular quadratic norm equation attached to a presentation.

### 10.3 Why every even set occurs

Let $S$ be a finite even set of noncomplex places. Assign local classes

$$
\alpha_v=
\begin{cases}
\frac12,&v\in S,\\
0,&v\notin S.
\end{cases}
$$

Their sum is $|S|/2=0$ in $\mathbf Q/\mathbf Z$. Exactness of the global Brauer invariant sequence produces a class $\alpha\in\operatorname{Br}(F)$ with precisely these local invariants.

It remains important to explain why $\alpha$ is represented by a quaternion algebra, not merely by some larger central simple algebra. The local indices of $\alpha$ are $1$ and $2$, so the global index theorem says that the index of $\alpha$ is their least common multiple, at most $2$. If $S$ is empty, $\alpha=0$ and $M_2(F)$ represents it. If $S$ is nonempty, its division representative has degree two and is therefore a quaternion division algebra. This gives existence.

The parity condition is exactly sufficient, not just necessary. In particular, one may prescribe a real place and a finite place together, two finite places, or any larger even collection. A singleton can never occur.

### 10.4 Presentations versus algebras

The classification theorem constructs an isomorphism class. It does not canonically choose $a$ and $b$. A presentation can be obtained by the presentation theorem, and in concrete situations weak approximation can be used to choose parameters with convenient local square classes. Different successful choices need not resemble one another.

It is therefore useful to write

$$
B_S
$$

for the unique quaternion algebra ramified exactly at an even set $S$. This notation specifies an algebra up to isomorphism, not a presentation. When $S=\varnothing$, $B_S=M_2(F)$. When $S\ne\varnothing$, $B_S$ is division globally, since it remains division at every place in $S$.

Calling $\mathfrak d(B)$ “the product of the finite ramified primes” is safe. Calling a chosen product of parameters the discriminant is not: $ab$ changes under harmless transformations and is not an invariant of the algebra.

### 10.5 Producing a presentation from local data

The existence proof via the Brauer sequence may appear to leave presentations inaccessible. In fact it gives a clean route to one, although not a canonical one.

Let $S$ be the desired finite even ramification set and let $B_S$ be the class constructed in Section 10.3. Use weak approximation to choose $a\in F^\times$ such that

$$
E=F(\sqrt a)
$$

is a field at every place in $S$. At a real place in $S$, choose $a<0$; at a finite place in $S$, choose any nonsquare local class. If necessary, impose nonsquareness at one auxiliary place so that $E$ is globally a field.

The field $E$ splits $B_S$. Indeed, at every $v\in S$ its unique local degree is two, which kills the invariant $1/2$, and outside $S$ there is no invariant to kill. Hence the class of $B_S$ lies in the relative Brauer group

$$
\operatorname{Br}(E/F)
=\ker(\operatorname{Br}(F)\to\operatorname{Br}(E)).
$$

Since $E/F$ is cyclic quadratic, relative cyclic algebra theory gives some $b\in F^\times$ with

$$
B_S\cong(E/F,\sigma,b)\cong(a,b)_F.
$$

The local requirements on $b$ are transparent: $b$ must be a nonnorm from $E_v/F_v$ exactly at $v\in S$, and a norm at every other place. Global existence of the Brauer class guarantees that these local norm cosets are compatible. Changing $b$ by a global norm changes the cyclic generator but not the algebra.

This construction explains both the power and the limitation of local prescriptions. One may freely prescribe the division sign at an even set of places. After a quadratic splitting field has been chosen, the corresponding local norm signs determine a global cyclic class. But one may not prescribe an odd number of nonnorm signs: Hilbert reciprocity is the obstruction.

### 10.6 Exact control of the archimedean signature

The global classification is often used with the finite places fixed and the real behavior left implicit. That is unsafe: real ramification participates in the same parity law and can change compactness, embeddings, and positivity. The following form makes every archimedean choice explicit.

Let $F$ have $r_1$ real places and $r_2$ complex places. Choose a subset $S_\infty$ of the real places and a finite set $S_f$ of finite places. Complex places are excluded because no quaternion algebra can ramify there.

**Theorem 10.2 (signature prescription).** There exists a quaternion algebra $B/F$ satisfying

$$
B_v\cong
\begin{cases}
\mathbf H,&v\in S_\infty,\\
M_2(\mathbf R),&v\text{ real and }v\notin S_\infty,\\
M_2(\mathbf C),&v\text{ complex},
\end{cases}
$$

and ramified at exactly the finite places in $S_f$ if and only if

$$
|S_\infty|+|S_f|\equiv0\pmod2.
$$

When it exists, it is unique up to $F$-algebra isomorphism.

**Proof strategy.** Translate the desired behavior into local invariants and use exactness of the global invariant sequence. Degree two then converts the resulting class back into a quaternion algebra.

**Proof.** Necessity follows from reciprocity: each prescribed ramified place contributes $1/2$, so the invariant sum vanishes only when the total number is even. Conversely, assume the parity condition and define a finite family of local invariants by assigning $1/2$ at $S_\infty\cup S_f$ and $0$ elsewhere. The sum is zero. Exactness produces a global Brauer class with precisely these localizations. As in Section 10.3, its global index is the least common multiple of its local indices, hence at most two. The zero class is represented by $M_2(F)$; a nonzero class has a division representative of degree two. In either case there is a quaternion algebra with the required local forms. Equality of all local invariants and global injectivity prove uniqueness. $\square$

Several consequences are worth recording separately.

First, if $F$ has no real places, the archimedean behavior is forced: every infinite completion is complex and split. A quaternion algebra over such a field is determined by an even set of finite places. It is division globally exactly when that set is nonempty.

Second, if $F$ has real places, one may alter the real signature only while respecting total parity with the finite ramification. With $S_f$ fixed, the number of ramified real places has prescribed parity but their identities remain freely selectable. Two choices of the same cardinality can yield nonisomorphic algebras because ramification remembers the actual embeddings, not merely their number.

Third, a quaternion algebra is globally division if and only if its ramification set is nonempty. Indeed, any ramified completion rules out a global matrix algebra, while an empty ramification set gives the split algebra by injectivity. This condition is weaker than definiteness. An algebra ramified at two finite places and split at every real place is division but indefinite.

Fourth, if $B=(a,b)_F$ is a chosen presentation, the real set is

$$
S_\infty(B)=\{\tau:F\hookrightarrow\mathbf R:\tau(a)<0\text{ and }\tau(b)<0\}.
$$

Weak approximation allows one to control the signs of $a$ at all real embeddings independently, and likewise for $b$. Yet prescribing the sign intersections alone does not control the finite Hilbert symbols; the global class theorem is what guarantees simultaneous compatibility.

This theorem is the exact archimedean version of global existence and uniqueness. “Ramified at infinity” is never a single condition over a general number field: it is a subset of the real places, and every complex place is automatically absent.

## 11. Base change and quadratic embeddings

### 11.1 The local degree formula

Let $L/F$ be a finite extension of number fields. A place $v$ of $F$ may have several places $w$ of $L$ above it, and the scalar extension $B_L=B\otimes_FL$ must be examined at each one. Completion and scalar extension commute:

$$
(B_L)_w\cong B_v\otimes_{F_v}L_w.
$$

The local Brauer invariant satisfies the exact formula

$$
\operatorname{inv}_w((B_L)_w)
=[L_w:F_v]\operatorname{inv}_v(B_v)
\qquad\text{in }\mathbf Q/\mathbf Z.
$$

This formula fixes the normalization completely. It uses the local degree at the individual place $w$, not the global degree $[L:F]$ and not the number of places above $v$. For quaternion algebras it becomes a parity rule:

$$
w\in\operatorname{Ram}(B_L)
\quad\Longleftrightarrow\quad
v\in\operatorname{Ram}(B)
\text{ and }[L_w:F_v]\text{ is odd}.
$$

Indeed, multiplying $1/2$ by an even degree gives $0$, while multiplying it by an odd degree leaves $1/2$. A place where $B$ was split can never become ramified under extension.

### 11.2 Ramification after extension

Several consequences deserve to be separated.

First, an even-degree local extension splits the unique local division quaternion algebra. In particular every quadratic field extension of a local field splits it. A split quadratic algebra does not: base change to $K\times K$ merely produces two copies of the original algebra.

Second, a global extension $L/F$ splits $B$ exactly when every place above every ramified place has even local degree:

$$
B_L\cong M_2(L)
\quad\Longleftrightarrow\quad
[L_w:F_v]\text{ is even for all }v\in\operatorname{Ram}(B),\ w\mid v.
$$

At a ramified real place, an extension place has local degree two precisely when it is complex and degree one when it remains real. Thus complexifying a ramified real place removes that ramification; a real place above it preserves it.

Third, odd-degree global extensions preserve some ramification and therefore cannot split a division quaternion algebra. Indeed, if every local degree above a fixed ramified $v$ were even, then

$$
[L:F]=\sum_{w\mid v}[L_w:F_v]
$$

would be even. For odd global degree, at least one summand is odd.

The ramification set after base change may contain more places even though no new base place ramifies: one ramified $v$ can split into several $w$ of odd degree. The total number remains even by global reciprocity. This parity is also visible from the local degree sum.

### 11.3 The quadratic embedding criterion

Let $E/F$ be a quadratic field and $B/F$ a quaternion algebra. At each place $v$,

$$
E\otimes_FF_v
$$

is either a quadratic field extension of $F_v$ or the split algebra $F_v\times F_v$. We say that $v$ splits in $E$ in the latter case.

**Theorem 11.1 (quadratic embedding criterion).** There is an $F$-embedding $E\hookrightarrow B$ if and only if no place in $\operatorname{Ram}(B)$ splits in $E$.

Equivalently,

$$
E\hookrightarrow B
\quad\Longleftrightarrow\quad
E\otimes_FF_v\text{ is a field for every }v\in\operatorname{Ram}(B).
$$

**Proof strategy.** A quadratic field embeds in a degree-two central simple algebra precisely when it splits that algebra. The base-change invariant formula translates global splitting by $E$ into the stated local condition.

**Proof.** If $E\hookrightarrow B$, then $E$ is a maximal commutative subfield and $B_E\cong M_2(E)$. At a ramified $v$, the local algebra $E\otimes_F F_v$ cannot be split: otherwise $B_v$ would embed a nontrivial idempotent through $F_v\times F_v$, contradicting division.

Conversely, assume no ramified place splits in $E$. At a place $w$ of $E$ above a ramified $v$, the local degree is two, so

$$
\operatorname{inv}_w(B_E)=2\cdot\frac12=0.
$$

Above an unramified place the invariant was already zero. Hence $B_E$ splits at every place of $E$, and global injectivity gives $B_E\cong M_2(E)$. The degree-two embedding theorem now supplies $E\hookrightarrow B$. $\square$

At a real ramified place, the condition says that $E$ must become complex. Thus every quadratic subfield of a totally definite algebra is totally imaginary. At a finite ramified place, the condition allows either a ramified or unramified quadratic local field, but forbids two copies of the base field.

### 11.4 Constructing useful quadratic subfields

The criterion is practical because only finitely many places impose conditions. Given $B$ with ramification set $S$, choose at every finite $v\in S$ a nonsquare class $d_v\in F_v^\times/F_v^{\times 2}$ and at every real $v\in S$ require $d_v<0$. Weak approximation chooses $d\in F^\times$ lying in these prescribed open square classes. Then

$$
E=F(\sqrt d)
$$

is a field at every place of $S$ and therefore embeds in $B$.

One must also ensure that $d$ is not a global square. Any prescribed nonsquare local class already ensures this. If $S$ is empty, add an auxiliary place at which $d$ is required to be nonsquare. This produces a quadratic field embedded in the split algebra as well.

This construction has two related uses. It recognizes a given algebra by finding a maximal subfield, and it helps construct a presentation. Once $E=F(\sqrt a)$ is embedded, choose an element $j$ implementing its nontrivial automorphism; then $j^2=b\in F^\times$ and $B\cong(a,b)_F$. The parameter $b$ is determined only modulo $N_{E/F}(E^\times)$, exactly as the cyclic norm criterion predicts.

The local condition cannot be weakened to “every ramified finite prime is nonsplit” while ignoring infinity. If $B$ ramifies at a real place and $E$ is real there, then $E\otimes_F\mathbf R\cong\mathbf R\times\mathbf R$ and no embedding can exist, regardless of the finite behavior.

### 11.5 Conjugacy and the classification of embeddings

Existence is only the first embedding question. Once a quadratic field occurs, one also wants to know whether different occurrences carry extra information. They do not at the level of the ambient algebra.

**Corollary 11.2 (conjugacy of quadratic embeddings).** Let $E/F$ be a quadratic field and let $B/F$ be a quaternion algebra. If $\iota_1,\iota_2:E\hookrightarrow B$ are $F$-embeddings, then there is $u\in B^\times$ such that

$$
\iota_2(x)=u\iota_1(x)u^{-1}
\qquad(x\in E).
$$

**Proof.** This is Theorem 1.2 applied to the two images of $E$. Number fields are infinite and have characteristic zero, so all its hypotheses hold. $\square$

Thus the criterion of Theorem 11.1 classifies quadratic subfields up to inner conjugacy by one condition: nonsplitting at every ramified place. It does not distinguish integral embeddings into particular orders; those involve additional local data and belong to the next stage of the subject.

An embedded field can be recognized from one element. Suppose $x\in B\setminus F$ and set

$$
t=\operatorname{Trd}(x),
\qquad n=\operatorname{Nrd}(x),
\qquad \Delta=t^2-4n.
$$

Then $x$ satisfies $X^2-tX+n$. If $\Delta$ is nonsquare, this polynomial is irreducible and

$$
F[x]\cong F(\sqrt\Delta).
$$

Conversely, for an embedding $E=F(\sqrt d)\hookrightarrow B$, the image of $\sqrt d$ is pure, squares to $d$, and has reduced norm $-d$. Hence the embedding criterion can be restated:

> There exists a pure quaternion $y\in B$ with $y^2=d$ if and only if no ramified place of $B$ splits in $F(\sqrt d)$.

This is a representation statement for the ternary quadratic form on $B^0$, because $y^2=-\operatorname{Nrd}(y)$. It links field embeddings to values of the pure norm form without introducing new hypotheses.

### 11.6 Why every ramified place must be checked

The criterion is a conjunction, not a parity test. It is not enough for the number of ramified places that split in $E$ to be even. A single split ramified place leaves two degree-one extensions of the invariant $1/2$, and both remain nonzero. For example, let $B/\mathbf Q$ ramify at $2$ and $3$. A quadratic field in which both primes split still fails to embed, even though the number of offending base places is two.

Nor may “split” be replaced by “unramified.” At a finite ramified place of $B$, either an unramified quadratic field or a ramified quadratic field splits the local division algebra, because both have local degree two. The forbidden local algebra is only $F_v\times F_v$. Thus the behavior of the prime in the quadratic field, not the ramification of the quadratic extension, is decisive.

At infinity, the terminology becomes especially transparent. If $v$ is real, then

$$
E\otimes_FF_v\cong
\begin{cases}
\mathbf C,&d<0\text{ under }v,\\
\mathbf R\times\mathbf R,&d>0\text{ under }v.
\end{cases}
$$

The first is a field of local degree two and kills a Hamiltonian invariant; the second has two degree-one branches and preserves it twice. Consequently, if $B$ is totally definite over a totally real field, every quadratic subfield is totally imaginary. The converse is not automatic: a totally imaginary quadratic field embeds only if it is also nonsplit at every finite ramified place.

Finally, the criterion applies to the split algebra with no local restrictions. Every quadratic field embeds in $M_2(F)$ through the regular representation. This endpoint is a useful consistency check: a proposed embedding theorem that imposes conditions at unramified places would incorrectly exclude quadratic fields from the matrix algebra.

## 12. Totally definite algebras

### 12.1 Compactness at infinity begins with ramification

Assume that $F$ is totally real of degree $d$. A quaternion algebra $B/F$ is **totally definite** if it ramifies at every real place. Equivalently,

$$
B\otimes_{F,\tau}\mathbf R\cong\mathbf H
$$

for every real embedding $\tau:F\hookrightarrow\mathbf R$.

Why is this the useful condition? At a real split place,

$$
B_v^\times/F_v^\times\cong\operatorname{PGL}_2(\mathbf R)
$$

is noncompact. At a ramified real place,

$$
\mathbf H^\times/\mathbf R^\times
$$

is compact: every class can be scaled to reduced norm one, and the norm-one Hamilton quaternions form the three-sphere. Thus total definiteness is the algebraic source of compactness at infinity that later turns automorphic quotients into finite, essentially combinatorial objects.

Definiteness says nothing by itself about finite ramification. That part is independently prescribed, subject to one parity constraint.

### 12.2 The exact parity condition

Let $S_f$ be the desired finite ramification set. Total definiteness requires

$$
\operatorname{Ram}(B)=\{v\mid\infty\}\cup S_f,
$$

where all $d$ archimedean places are real. The local--global classification gives the exact existence condition

$$
d+|S_f|\equiv0\pmod2.
$$

Thus:

- if $d$ is even, $S_f$ must have even cardinality, and it may be empty;
- if $d$ is odd, $S_f$ must have odd cardinality, so at least one finite place must ramify.

This is a cardinality statement about places, not about the degree or norm of the ideal $\prod_{v\in S_f}\mathfrak p_v$. Repeated prime powers never occur in $\mathfrak d(B)$ and would not repair a parity failure.

Over $\mathbf Q$, there is one real place. Hence a totally definite rational quaternion algebra must ramify at an odd number of finite primes. In particular there is no rational quaternion algebra ramified only at infinity. Hamilton's rational algebra has the smallest possible pattern, $\{2,\infty\}$.

### 12.3 Construction with prescribed finite ramification

**Theorem 12.1 (definite construction).** Let $F$ be totally real of degree $d$, and let $S_f$ be a finite set of finite places satisfying

$$
|S_f|\equiv d\pmod2.
$$

There is a unique quaternion algebra, up to $F$-isomorphism, ramified at every real place and exactly at the finite places in $S_f$.

**Proof.** The set consisting of the $d$ real places and $S_f$ has even cardinality. The local--global classification supplies a unique algebra with that ramification set. Its real localizations are all Hamiltonian, so it is totally definite. $\square$

Although short, the proof is a genuine existence argument: the global Brauer sequence is doing the gluing. No choice of globally compatible parameters is being assumed. If explicit generators are needed, choose a totally imaginary quadratic extension $E/F$ that is also a field at every $v\in S_f$. It embeds in the constructed $B$. Writing $E=F(\sqrt a)$ and choosing a cyclic generator produces $B\cong(a,b)_F$ for a suitable $b$.

There is also a useful flexibility statement. Given any finite set $T$ of finite places at which one wants $B$ split, choose $S_f$ disjoint from $T$ with the required parity. If $d$ is odd, one auxiliary finite ramified place outside $T$ suffices; if $d$ is even, none is needed unless other requirements prescribe finite ramification. The infinitude of finite places guarantees room for these choices.

### 12.4 The algebra required later

For later automorphic constructions, the input should be stated without integral embellishment:

> Let $F$ be totally real and let $S_f$ be a finite set of finite places with $|S_f|\equiv[F:\mathbf Q]\pmod2$. Denote by $D/F$ the unique quaternion algebra ramified at every real place and precisely at $S_f$ among finite places.

From this statement alone one can safely infer:

- $D$ is a division algebra, because it is division at every real completion;
- $D_v^\times/F_v^\times$ is compact for every archimedean $v$;
- $D_v\cong M_2(F_v)$ for every finite $v\notin S_f$;
- $D_v$ is the unique local quaternion division algebra for $v\in S_f$;
- the reduced discriminant of the algebra is $\mathfrak d(D)=\prod_{v\in S_f}\mathfrak p_v$.

No maximal order, Eichler level, ideal class, or compact open subgroup has yet been chosen. Those are extra integral and adelic data. Keeping them separate is what allows the same algebra $D$ to support many later levels.

### 12.5 Definite, indefinite, and mixed signature

Over $\mathbf Q$ the terminology is binary: a quaternion algebra is definite when it ramifies at the unique real place and indefinite when it splits there. Over a totally real field with several embeddings, an algebra can have mixed signature, ramified at some real places and split at others. It is useful to state exactly which conclusions survive.

At a real ramified place, the norm-one group is the compact three-sphere

$$
\{x\in\mathbf H:\operatorname{Nrd}(x)=1\}.
$$

At a real split place it is $\operatorname{SL}_2(\mathbf R)$, which is noncompact. Hence the product of the archimedean norm-one groups is compact if and only if the algebra is ramified at every real place. One split real factor makes the product noncompact.

If $F$ has a complex place, its local factor is $\operatorname{SL}_2(\mathbf C)$ and is noncompact. Therefore a number field admits an algebra compact modulo center at all archimedean places only when it is totally real and the algebra is totally definite. Complex places cannot be repaired by ramification because there is no quaternion division algebra over $\mathbf C$.

The center quotient gives the same criterion. At a Hamiltonian place,

$$
\mathbf H^\times/\mathbf R^\times
$$

is compact. At a real split place one gets $\operatorname{PGL}_2(\mathbf R)$, and at a complex place one gets $\operatorname{PGL}_2(\mathbf C)$; both are noncompact. Thus the phrase “definite at infinity” contains two exact hypotheses: the base field is totally real, and every real localization is Hamiltonian.

The quadratic embedding criterion has a parallel signature consequence. A quadratic subfield of a totally definite algebra must be totally imaginary. For mixed signature, it must be complex at each ramified real place but may be real or complex at each split real place. Weak approximation can impose these signs independently, simultaneously with nonsplitting conditions at the finitely many ramified finite places.

Finally, reduced norms reflect the same trichotomy. At a ramified real place they are positive; at a split real or complex place they are unrestricted. Theorem 9.2 therefore says that the global reduced norm image is cut out by positivity at exactly the ramified real places. Total definiteness is the extreme case in which positivity is required at every real embedding.

## 13. Explicit algebras over the rationals

### 13.1 Four basic ramification patterns

The rational field offers one real place and one completion $\mathbf Q_p$ for every prime $p$. A rational quaternion algebra is therefore classified by a finite even subset of

$$
\{2,3,5,7,\ldots,\infty\}.
$$

Four patterns form a useful library.

**The split algebra.** The algebra $M_2(\mathbf Q)$ has

$$
\operatorname{Ram}(M_2(\mathbf Q))=\varnothing,
\qquad
\mathfrak d(M_2(\mathbf Q))=(1).
$$

It may be presented as $(1,b)_{\mathbf Q}$ for any nonzero $b$.

**Hamilton's rational algebra.** Let

$$
B=(-1,-1)_{\mathbf Q}.
$$

At infinity both parameters are negative, so $B$ ramifies. At every odd prime $p$, the odd-residue formula shows that the symbol is $+1$ unless a valuation is odd; here both parameters are units, so it is $+1$. Reciprocity then forces ramification at $2$. Hence

$$
\operatorname{Ram}(B)=\{2,\infty\},
\qquad
\mathfrak d(B)=(2).
$$

**A definite algebra of odd prime discriminant.** If $p\equiv3\pmod4$, then

$$
B=(-1,-p)_{\mathbf Q}
$$

ramifies exactly at $p$ and infinity. At $p$,

$$
(-1,-p)_p=\left(\frac{-1}{p}\right)=-1.
$$

At infinity both parameters are negative. Every other odd prime is immediately split, and the dyadic formula gives $+1$ because $-p\equiv1\pmod4$. Thus

$$
\operatorname{Ram}(B)=\{p,\infty\},
\qquad
\mathfrak d(B)=(p).
$$

For $p=3$, this is $(-1,-3)_{\mathbf Q}$.

**An indefinite division algebra.** Let

$$
B=(2,3)_{\mathbf Q}.
$$

At infinity it splits because both parameters are positive. At $3$,

$$
(2,3)_3=\left(\frac23\right)=-1,
$$

and the rational dyadic formula gives $(2,3)_2=-1$. At every other finite prime both parameters are units and the residue characteristic is odd, so the symbol is $+1$. Hence

$$
\operatorname{Ram}(B)=\{2,3\},
\qquad
\mathfrak d(B)=(6).
$$

It is division over $\mathbf Q$ because it is division at $2$ and $3$, but it is **indefinite** because it splits over $\mathbf R$. Global division and total definiteness are different properties.

Finally, classification produces an algebra $B_{\{2,3,5,7\}}$ ramified at exactly those four finite primes and split at infinity. The notation is more informative than an arbitrary presentation. Its existence also illustrates that no sign at infinity is forced merely by having many finite ramified places; only total parity matters.

### 13.2 Computing a ramification set

For a presented rational algebra $B=(a,b)_{\mathbf Q}$, the following finite computation is reliable.

1. Replace $a$ and $b$ by square-class representatives, often squarefree integers.
2. List $\infty$, $2$, and the odd primes dividing $ab$. Every other place splits.
3. At infinity, test whether both parameters are negative.
4. At odd candidate primes, apply the valuation-unit formula.
5. At $2$, use the dyadic formula or the norm criterion.
6. Check that the number of negative symbols is even.

Consider $B=(-1,-3)_{\mathbf Q}$. The candidates are $2,3,\infty$. The real symbol is $-1$. At $3$, write $a=-1$ as a unit and $b=3(-1)$; the odd formula gives

$$
(-1,-3)_3=\left(\frac{-1}{3}\right)=-1.
$$

At $2$, both parameters are odd. The exponent in the dyadic formula is

$$
\frac{-2}{2}\frac{-4}{2}=2\equiv0\pmod2,
$$

so the symbol is $+1$. This yields $\{3,\infty\}$ and passes the parity check.

Now consider $(2,7)_{\mathbf Q}$. A direct global norm computation in Section 5.4 already proved it split. Locally the same conclusion says every symbol is $+1$. At $7$, $(2/7)=+1$; at $2$, the dyadic exponent is $(7^2-1)/8=6$, also even; infinity is split. This agreement illustrates how the norm, symbol, and ramification languages reinforce one another.

The parity check detects but does not locate a mistake. If a computation produces the singleton $\{3\}$, some omitted place—usually $2$ or infinity—must also ramify, or the $3$-adic calculation is wrong.

### 13.3 Behavior under selected base changes

Let $B=(-1,-1)_{\mathbf Q}$, ramified at $2$ and infinity. Over $\mathbf Q(i)$, the real place becomes complex and disappears. The unique place above $2$ has local degree two, so its invariant is

$$
2\cdot\frac12=0.
$$

Thus

$$
B\otimes_{\mathbf Q}\mathbf Q(i)\cong M_2(\mathbf Q(i)).
$$

This is also immediate from the presentation because $-1$ becomes a square.

Now let $L/\mathbf Q$ be a real quadratic field. The real ramification of $B$ persists at both real places of $L$. At the prime $2$ there are two possibilities relevant to invariants. If $2$ is inert or ramified in $L$, the single local degree is two and finite ramification disappears. If $2$ splits, there are two places of local degree one and both remain ramified. Thus

$$
\operatorname{Ram}(B_L)=
\begin{cases}
\{\text{the two real places}\},&2\text{ is nonsplit in }L,\\
\{\text{the two real places and the two places above }2\},&2\text{ splits in }L.
\end{cases}
$$

Both sets have even cardinality, as they must.

For the indefinite algebra $(2,3)_{\mathbf Q}$, any quadratic field in which neither $2$ nor $3$ splits embeds in the algebra and splits it after scalar extension. If either prime splits, the algebra remains ramified at the degree-one places above that prime and the field does not embed. This gives a concrete instance of Theorem 11.1.

## 14. The reusable local--global dictionary

### 14.1 Equivalent languages

The theory is most useful when one can move without hesitation among its different descriptions. Let $B=(a,b)_F$ be a quaternion algebra over a number field. The central correspondences are:

| Question | Algebraic answer | Quadratic-form answer | Local answer |
|---|---|---|---|
| Is $B$ split over $F$? | $B\cong M_2(F)$ | $n_B$ is isotropic | $B_v$ splits for every $v$ |
| Is a nonzero $x$ invertible? | $x\in B^\times$ | $\operatorname{Nrd}(x)\ne0$ | the same after every scalar extension |
| Does $(a,b)_F$ split? | its Brauer class is zero | $\langle1,-a,-b,ab\rangle$ is isotropic | $(a,b)_{F_v}=+1$ for every $v$ |
| Is $b$ the relevant norm? | $(E/F,\sigma,b)$ is split | $b=r^2-as^2$ when $E=F(\sqrt a)$ | $b\in N(E_v^\times)$ for every $v$ |
| Does $E/F$ embed in $B$? | $E$ is a maximal subfield | $E$ splits $B$ | no ramified place of $B$ splits in $E$ |
| What determines $B$? | its Brauer class of order at most two | the isometry class of its reduced norm form | the finite even set $\operatorname{Ram}(B)$ |

At a local place the sign and invariant carry the same bit of information:

$$
(a,b)_{F_v}=+1\leftrightarrow\operatorname{inv}_v(B)=0,
\qquad
(a,b)_{F_v}=-1\leftrightarrow\operatorname{inv}_v(B)=\frac12.
$$

Globally those bits satisfy one relation:

$$
\prod_v(a,b)_{F_v}=1
\quad\Longleftrightarrow\quad
\sum_v\operatorname{inv}_v(B)=0
\quad\Longleftrightarrow\quad
|\operatorname{Ram}(B)|\text{ is even}.
$$

The first expression is tailored to explicit Hilbert-symbol calculations, the second to Brauer functoriality, and the third to classification.

### 14.2 A decision procedure

Suppose a later argument asks for a quaternion algebra over a number field with specified behavior. The theory reduces the problem to a stable sequence of decisions.

If the algebra is given by parameters, first determine the finite candidate places from $2ab$ and the real candidates from signs. Compute odd local symbols with the residue formula, treat dyadic places by their actual norm groups or a field-specific formula, and use reciprocity as a consistency check. The negative places are $\operatorname{Ram}(B)$, and their finite product is $\mathfrak d(B)$.

If the algebra is to be constructed, prescribe a finite set of noncomplex places and count it. An even set gives one and only one algebra. An odd set is impossible until one more finite or real place is added. For a totally definite algebra over a totally real field, all real places are already prescribed, so the finite set must have cardinality congruent to $[F:\mathbf Q]$ modulo two.

If a scalar extension $L/F$ is introduced, do not recompute presentations unless convenient. For every $w\mid v$, multiply the old invariant by $[L_w:F_v]$. A ramified place survives exactly at the extensions of odd local degree.

If a quadratic field $E/F$ is to embed, inspect only the ramified places. It embeds exactly when each of those places stays a field in $E$, including the requirement that every ramified real place becomes complex. When it embeds, it is maximal and splits $B$.

These procedures require no integral order. The algebra, its reduced norm, its localizations, and its ramification set are the complete input at this stage.

### 14.3 Conclusion

Quaternion algebras occupy a rare point where noncommutative algebra, quadratic forms, local norm theory, and global reciprocity describe exactly the same object. A presentation $(a,b)_F$ gives four coordinates and an explicit multiplication law. Canonical conjugation compresses that law into reduced trace and reduced norm. The norm form turns division into anisotropy and splitting into the existence of a visible singular vector. A quadratic subfield turns the presentation into a cyclic algebra, so splitting becomes a norm equation.

Completion then strips the question to one bit at each place: split with invariant $0$, or division with invariant $1/2$. At odd finite places that bit has a residue formula; at dyadic places it must respect the deeper unit structure; over $\mathbf R$ it is the sign obstruction, and over $\mathbf C$ it vanishes. Global reciprocity says that the bits sum to zero. The resulting even ramification set both classifies the algebra and provides the exact existence theorem needed to build it.

The final construction principle is therefore precise. Over a totally real field, choose the finite ramification required by the arithmetic application, add every real place, and check parity. There is then one totally definite quaternion algebra with exactly that behavior. Its later integral structures may vary, but the ambient algebra—its norm, its local division factors, its quadratic subfields, and its behavior under base change—is already determined.
