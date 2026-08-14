import Mathlib.Algebra.BigOperators.Fin
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section01TheAbsoluteAndRelativeSettings

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry BigOperators Matrix

universe u v

/-!
Shared interfaces for Chapter 13.

The pinned Mathlib tree supplies schemes, scheme-theoretic fibers, regular local
rings, algebraic cycles, and the matrix/combinatorial operations used below.  It
does not package the intersection product of Cartier divisors on a regular
arithmetic surface.  The structures in this file keep that missing earlier-book
interface explicit; the section files state the fiber identities that follow
from it.
-/

/-! ### Arithmetic surfaces and their fiber components -/

def chapter13RegularScheme (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

abbrev chapter13PureDimensionOne (X : Scheme.{u}) : Prop :=
  LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Chapter01PureDimensionOne X

/- The relative-curve condition is recorded on every scheme-theoretic fiber;
the regularity condition is imposed on the total space, as required for the
Cartier/Weil dictionary used by the chapter. -/
structure Chapter13ArithmeticSurface
    (R : Type u) [CommRing R] [IsDomain R] [IsDedekindDomain R] where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of R)
  proper : IsProper structureMap
  flat : Flat structureMap
  finitePresentation : LocallyOfFinitePresentation structureMap
  regular : chapter13RegularScheme carrier
  fiberPureDimensionOne :
    ∀ s : Spec (CommRingCat.of R),
      chapter13PureDimensionOne (structureMap.fiber s)

namespace Chapter13ArithmeticSurface

instance (A : Chapter13ArithmeticSurface R) : IsProper A.structureMap := A.proper

instance (A : Chapter13ArithmeticSurface R) : Flat A.structureMap := A.flat

instance (A : Chapter13ArithmeticSurface R) :
    LocallyOfFinitePresentation A.structureMap := A.finitePresentation

end Chapter13ArithmeticSurface

abbrev chapter13SchemeTheoreticFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (A : Chapter13ArithmeticSurface R)
    (s : Spec (CommRingCat.of R)) : Scheme.{u} :=
  A.structureMap.fiber s

/- LOCAL_DEPENDENCY_GUESS: Earlier chapters expose divisor cycles and local
equations separately, but the pinned checkout has no bundled Cartier-divisor
type for a regular surface.  This small wrapper is the weakest interface needed
to distinguish the Cartier divisors used in the displayed pairings. -/
structure Chapter13CartierDivisor
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (A : Chapter13ArithmeticSurface R) where
  cycle : AlgebraicCycle A.carrier ℤ

@[ext]
theorem chapter13CartierDivisor_ext
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {D E : Chapter13CartierDivisor A}
    (h : D.cycle = E.cycle) : D = E := by
  cases D
  cases E
  cases h
  rfl

/- A prime component carries its canonical closed integral support as well as
the cycle used by the intersection interface.  The bundled type is the
book-facing bridge from the scheme support to the canonical cycle API. -/
structure Chapter13PrimeDivisor
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (A : Chapter13ArithmeticSurface R)
    extends Chapter13CartierDivisor A where
  support : Scheme.{u}
  inclusion : support ⟶ A.carrier
  closed : IsClosedImmersion inclusion
  integral : IsIntegral support
  proper : IsProper (inclusion ≫ A.structureMap)

def chapter13FiniteFlatOverNeighborhood
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    (P : Chapter13PrimeDivisor A)
    (s : Spec (CommRingCat.of R)) : Prop :=
  ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
    IsFinite ((P.inclusion ≫ A.structureMap) ∣_ U) ∧
      Flat ((P.inclusion ≫ A.structureMap) ∣_ U)

/-! A component of a scheme-theoretic fiber.  The factorization through the
fiber and the finite-type curve condition make the geometric meaning of the
index `Γᵢ` available without pretending that Mathlib already has a global
intersection theory for these components. -/
structure Chapter13FiberComponent
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (A : Chapter13ArithmeticSurface R)
    (s : Spec (CommRingCat.of R))
    extends Chapter13CartierDivisor A where
  support : Scheme.{u}
  inclusion : support ⟶ A.carrier
  fiberInclusion : support ⟶ A.structureMap.fiber s
  factor_through_fiber : fiberInclusion ≫ A.structureMap.fiberι s = inclusion
  closed : IsClosedImmersion fiberInclusion
  integral : IsIntegral support
  proper : IsProper
    (fiberInclusion ≫ A.structureMap.fiberToSpecResidueField s)
  curve : chapter13PureDimensionOne support

/- The support of a fiber is allowed to be indexed by an arbitrary finite
indexing choice.  The positive multiplicities and the cycle decomposition are
the exact data behind `F = ∑ mᵢ Γᵢ`. -/
structure Chapter13SpecialFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (A : Chapter13ArithmeticSurface R)
    (s : Spec (CommRingCat.of R)) where
  r : ℕ
  component : Fin r → Chapter13FiberComponent A s
  multiplicity : Fin r → ℕ
  multiplicity_pos : ∀ i, 0 < multiplicity i
  fiber : Chapter13CartierDivisor A
  fiber_cycle_decomposition :
    fiber.cycle =
      ∑ i, (multiplicity i : ℤ) • (component i).cycle

@[simp]
theorem chapter13SpecialFiber.multiplicity_ne_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (F : Chapter13SpecialFiber A s) (i : Fin F.r) :
    F.multiplicity i ≠ 0 := by
  exact Nat.ne_of_gt (F.multiplicity_pos i)

/-! ### The missing intersection-product interface -/

/- LOCAL_DEPENDENCY_GUESS: This is the book-facing form of the earlier local
intersection and Cartier divisor calculus.  Additivity and symmetry are kept
as fields so later formulas can be transported to matrices without depending
on a particular implementation of cycles. -/
structure Chapter13SpecialFiberIntersectionData
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    extends Chapter13SpecialFiber A s where
  intersection : AlgebraicCycle A.carrier ℤ → AlgebraicCycle A.carrier ℤ → ℤ
  intersection_add_left :
    ∀ x y z, intersection (x + y) z = intersection x z + intersection y z
  intersection_add_right :
    ∀ x y z, intersection x (y + z) = intersection x y + intersection x z
  intersection_smul_left :
    ∀ (n : ℤ) x y, intersection (n • x) y = n * intersection x y
  intersection_smul_right :
    ∀ (n : ℤ) x y, intersection x (n • y) = n * intersection x y
  symmetric : ∀ x y, intersection x y = intersection y x
  principal_fiber_restriction :
    ∀ i, intersection fiber.cycle (component i).cycle = 0
  off_diagonal_nonnegative :
    ∀ i j, i ≠ j → 0 ≤ intersection (component i).cycle (component j).cycle
  components_meet : Fin r → Fin r → Prop
  off_diagonal_positive_iff_meet :
    ∀ i j, i ≠ j →
      (0 < intersection (component i).cycle (component j).cycle ↔
        components_meet i j)

def chapter13ComponentIntersection
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i j : Fin T.r) : ℤ :=
  T.intersection (T.component i).cycle (T.component j).cycle

def chapter13FiberIntersectionWithComponent
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) : ℤ :=
  T.intersection T.fiber.cycle (T.component i).cycle

def chapter13IntersectionMatrix
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Matrix (Fin T.r) (Fin T.r) ℤ :=
  fun i j => chapter13ComponentIntersection T i j

@[simp]
theorem chapter13IntersectionMatrix_apply
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i j : Fin T.r) :
    chapter13IntersectionMatrix T i j = chapter13ComponentIntersection T i j :=
  rfl

def chapter13FiberMultiplicityVector
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Fin T.r → ℤ :=
  fun i => T.multiplicity i

@[simp]
theorem chapter13FiberMultiplicityVector_apply
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (i : Fin T.r) :
    chapter13FiberMultiplicityVector T i = T.multiplicity i :=
  rfl

def chapter13FiberRelation
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) : Prop :=
  ∀ i, ∑ j, (T.multiplicity j : ℤ) * chapter13ComponentIntersection T j i = 0

def chapter13MatrixKernel
    {α : Type u} [Semiring α] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) α) (v : Fin n → α) : Prop :=
  ∀ i, ∑ j, M i j * v j = 0

def chapter13RationalIntersectionMatrix
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Matrix (Fin T.r) (Fin T.r) ℚ :=
  fun i j => chapter13ComponentIntersection T i j

def chapter13RationalMultiplicityVector
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Fin T.r → ℚ :=
  fun i => T.multiplicity i

def chapter13RationalMatrixLinearMap {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) :
    (Fin n → ℚ) →ₗ[ℚ] (Fin n → ℚ) where
  toFun x := M *ᵥ x
  map_add' x y := Matrix.mulVec_add M x y
  map_smul' c x := Matrix.mulVec_smul M c x

def chapter13RationalMatrixKernel
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Set (Fin T.r → ℚ) :=
  {x | chapter13MatrixKernel (chapter13RationalIntersectionMatrix T) x}

def chapter13MultiplicityLine
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Set (Fin T.r → ℚ) :=
  {x | ∃ q : ℚ, x = q • chapter13RationalMultiplicityVector T}

def chapter13WeightedPotential
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) (i : Fin T.r) : ℚ :=
  a i / (T.multiplicity i : ℚ)

def chapter13VerticalSelfIntersection
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) : ℚ :=
  ∑ i, ∑ j, a i * a j * (chapter13ComponentIntersection T i j : ℚ)

def chapter13WeightedLaplacianEnergy
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (a : Fin T.r → ℚ) : ℚ :=
  ∑ i, ∑ j ∈ Finset.Ioi i,
    (T.multiplicity i : ℚ) * (T.multiplicity j : ℚ) *
      (chapter13ComponentIntersection T i j : ℚ) *
        (chapter13WeightedPotential T a i - chapter13WeightedPotential T a j) ^ 2

def chapter13MultiplicitySubmodule
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Submodule ℚ (Fin T.r → ℚ) :=
  Submodule.span ℚ {chapter13RationalMultiplicityVector T}

abbrev Chapter13VerticalCoefficientQuotient
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :=
  Submodule.Quotient (chapter13MultiplicitySubmodule T)

/-! ### Generic-fiber degree and the local-length proof interface -/

/- The actual generic fiber and finite-flat rank constructions live in the
earlier surface/divisor chapters.  This record keeps their outputs canonical
at the Chapter 13 boundary and exposes the exact local assertions used in the
proof of (13.3). -/
structure Chapter13GenericDegreeData
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) where
  degreeOnGenericFiber : Chapter13CartierDivisor A → ℤ
  fiberLength : Chapter13PrimeDivisor A → ℕ
  finiteFlatRank : Chapter13PrimeDivisor A → ℕ
  isVerticalPrime : Chapter13PrimeDivisor A → Prop
  isHorizontalPrime : Chapter13PrimeDivisor A → Prop
  vertical_prime_intersection_zero :
    ∀ P, isVerticalPrime P →
      T.intersection P.cycle T.fiber.cycle = 0
  horizontal_prime_is_finite_flat :
    ∀ P, isHorizontalPrime P → chapter13FiniteFlatOverNeighborhood P s
  horizontal_fiber_length_eq_rank :
    ∀ P, isHorizontalPrime P → fiberLength P = finiteFlatRank P
  horizontal_local_length_formula :
    ∀ P, isHorizontalPrime P →
      T.intersection P.cycle T.fiber.cycle = fiberLength P
  horizontal_degree_eq_rank :
    ∀ P, isHorizontalPrime P →
      degreeOnGenericFiber P.toChapter13CartierDivisor = finiteFlatRank P
  isHorizontalSection : Chapter13PrimeDivisor A → Prop
  horizontal_section_degree_one :
    ∀ P, isHorizontalSection P → degreeOnGenericFiber P.toChapter13CartierDivisor = 1

def chapter13DegreeZeroOnGenericFiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    {T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)}
    (G : Chapter13GenericDegreeData T)
    (D : Chapter13CartierDivisor A) : Prop :=
  G.degreeOnGenericFiber D = 0

/-! ### Graph language and warning interfaces -/

def chapter13Adjacency
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) :
    Fin T.r → Fin T.r → Prop :=
  fun i j => i ≠ j ∧ T.components_meet i j

def chapter13GraphConnected
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s)) : Prop :=
  ∀ i j : Fin T.r,
    Relation.ReflTransGen (chapter13Adjacency T) i j

def chapter13NoBoundaryEdges
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (C : Set (Fin T.r)) : Prop :=
  ∀ i ∈ C, ∀ j ∉ C, chapter13ComponentIntersection T i j = 0

def chapter13ComponentIndicator
    {R : Type u} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (C : Set (Fin T.r)) : Fin T.r → ℤ :=
  fun i => if i ∈ C then T.multiplicity i else 0

end

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13
