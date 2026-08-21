# Tate--Sen Theory and $\mathbf C_\ell$ Period Foundations

> **PLACEHOLDER — NOT A MANUSCRIPT.**
> This file is an outline. No result below is proved anywhere in this repository, and nothing
> in this file may be cited by another volume as an available result. It exists so that the
> dependency graph names the volume that is missing, rather than leaving the gap implicit.
> When the volume is written, this file is replaced by the manuscript.

## Why this volume exists

Two manuscripts reach for a quantitative Tate--Sen theory that no volume in the collection
supplies.

Book 6, §11.5 formerly proved a rank-one Hodge--Tate algebraicity theorem — that a continuous
one-dimensional Hodge--Tate character of a local Galois group is locally algebraic — on the
strength of an asserted finite Ax--Sen estimate together with compatible contracting homotopies
on continuous bar cochains in degrees one and two. The homotopies were never constructed and
their valuation bounds were never verified, and the whole of the subsequent argument —
$H^1$ vanishing over the completed algebraic closure, semilinear descent, decompletion, the Sen
operator — rested on exactly that omission. That passage has been excised; Book 6 now proves
local algebraicity and builds the $\ell$-adic avatar from it, and defers the converse here.

Book 47 needs the same foundation and says so: item one of its missing-work list asks for a
$\mathbf C_p$ and Tate--Sen package, including the rank-one case, before its Hodge--Tate
inheritance results can be unconditional.

## Scope

**In scope.** The $\mathbf C_\ell$ and Tate--Sen foundation, through the rank-one Hodge--Tate
algebraicity theorem and the functoriality that Book 47 consumes.

**Out of scope, and to remain so.** The good-reduction $p$-divisible-group Hodge--Tate exact
sequence; the coefficient-prime Raynaud one-motive realization and semistable descent; any
general smooth-proper comparison theorem. Those are items two through four of Book 47's list
and are separate later volumes. A volume that quietly absorbed them would repeat the failure
this one is being written to repair.

## Prerequisites

Books 1, 2, 3, 5, 24. From Book 1 and Book 2, complete discretely valued fields, extension of
valuations, and the structure of finite extensions; from Book 3, the lower and upper ramification
filtrations, Herbrand functions, and the different, which are what make the Ax--Sen constant
uniform; from Book 5, Lubin--Tate formal modules and their towers; from Book 24, continuous
cohomology of profinite groups, its cochain description, and inflation--restriction.

## Chapter outline

**1. The completed algebraic closure.** Extension of the valuation to $\overline L$; the
completion $\mathbf C_\ell$; its algebraic closedness; the continuous action of $G_L$ and the
identification of the invariants of a closed subgroup. Establish at the outset which statements
are about $\overline L$ and which survive completion, since the whole subject is the passage
between them.

**2. The finite Ax--Sen estimate.** For a finite Galois $M/L$, a subgroup $J$, and $x \in M$,
produce $y \in M^J$ with $v_\ell(x-y)$ bounded below by $\min_\sigma v_\ell(\sigma x - x)$ minus
a constant depending only on $\ell$. Prove it by separating the unramified quotient with an
integral normal basis, the tame quotient with its Reynolds operator, and clustering the remaining
conjugates by lower ramification breaks; the geometric series over nested clusters supplies the
uniform constant $\ell/(\ell-1)^2$. Prove the additive cocycle form as well: a one-cocycle
$J \to M$ is a coboundary up to the same uniform valuation loss. Give the examples showing the
constant cannot be removed and the clustering cannot be replaced by an arbitrary composition
series.

**3. Contracting homotopies on continuous cochains.** This is the chapter Book 6 asserted and did
not write, and it is the technical heart of the volume. Construct explicitly the operators
$h^1_J$ and $h^2_J$ on normalized additive bar cochains, verify $dh + hd = 1 - P$ in degrees one
and two as identities rather than as expansions gestured at, prove the valuation loss of each is
bounded by the Ax--Sen constant, and prove that refining the coset decomposition changes the
homotopies by an explicit prism, so that corrections may be chosen compatibly as the finite
Galois field and its quotient grow. Nothing later in the volume is available without the
compatibility statement, so it is proved here in full and used by name.

**4. Almost-vanishing of continuous cohomology.** Normalized trace operators on the tower;
computation of $H^i(H, \mathbf C_\ell)$ for $H$ the kernel of the tower; in particular
$H^1(H, \mathbf C_\ell) = 0$. Both the Lubin--Tate and cyclotomic towers should be treated, with
the dependence on the choice of tower made explicit rather than suppressed.

**5. Decompletion and semilinear descent.** Descent of $\mathbf C_\ell$-semilinear
representations of $G_L$ to finite-level modules over the tower; the equivalence of categories
and the precise sense in which it is an equivalence; what fails without the compatibility proved
in Chapter 3.

**6. The Sen operator.** Construction from the descended module; independence of choices;
functoriality in the representation; the criteria for semisimplicity and for integrality of the
eigenvalues. Worked rank-one and rank-two examples, including one where the operator is nilpotent
and nonzero.

**7. Tate twists and Hodge--Tate representations.** Computation of $H^i(G_L, \mathbf C_\ell(i))$;
the Hodge--Tate condition and its equivalence with semisimplicity and integrality of the Sen
operator; the Hodge--Tate decomposition. Then the theorem Book 6 defers: **a continuous
one-dimensional Hodge--Tate character of $G_L$ is locally algebraic**, with the labeled exponents
matching the Sen eigenvalues under arithmetic local reciprocity.

**8. Functoriality and the reusable interface.** Behavior under subobjects, quotients, tensor
products, duals, coefficient extension, and restriction to open subgroups — precisely the
closure properties Book 47's Proposition 9.1 invokes. Close with an explicit statement of what
this volume makes available to later volumes and, equally explicitly, what it does not.

## Downstream consumers to update when this volume is written

- **Book 6, §11.5** — the deferral note there is replaced by a forward citation, or the
  Hodge--Tate direction is restored as a cited consequence. Book 6 precedes this volume in the
  chronology, so it must not use the theorem in a proof; a roadmap pointer is the most it may do.
- **Book 47, §9.5** — item one of the missing-work list is discharged; Proposition 9.1's
  dependence on a semisimple integral Sen operator becomes a citation. Items two through four
  remain open, so $(\mathrm{HT}_{\mathrm{curve}})$ itself stays an assumption.
- **`BOOK_DEPENDENCIES.md`** — add 24a to Book 47's prerequisite row, which is deliberately not
  done while this file is a placeholder.
