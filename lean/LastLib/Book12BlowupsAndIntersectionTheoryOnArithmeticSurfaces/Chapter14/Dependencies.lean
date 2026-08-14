import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic
import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13.Section03NegativityAndTheExactKernel

/-!
# Book 12, Chapter 14: shared interfaces

The preceding chapters expose scheme-level fibre and intersection data.  The
records below are the smallest numerical interfaces needed by this chapter.
The finite-dimensional assertions about a special fibre are kept as fields of
the component-matrix record so that the correction and pairing constructions
use only the displayed matrix operations.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14

open AlgebraicGeometry CategoryTheory
open LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter13

/-! ## Component vectors and matrices -/

abbrev Chapter14IntegralVector (r : ℕ) := Fin r → ℤ

abbrev Chapter14RationalVector (r : ℕ) := Fin r → ℚ

def chapter14DotProduct {ι R : Type*} [Fintype ι] [Mul R] [AddCommMonoid R]
    (v w : ι → R) : R :=
  ∑ i, v i * w i

def chapter14MatrixVec {ι R : Type*} [Fintype ι] [Mul R] [AddCommMonoid R]
    (M : Matrix ι ι R) (v : ι → R) : ι → R :=
  fun i => ∑ j, M i j * v j

def chapter14MatrixPairing {ι R : Type*} [Fintype ι] [Mul R] [AddCommMonoid R]
    (M : Matrix ι ι R) (v w : ι → R) : R :=
  ∑ i, v i * chapter14MatrixVec M w i

/- LOCAL_DEPENDENCY_GUESS: Chapters 13.1--13.3 are expected to provide the
component matrix, its fibre relation, and the negative-semidefinite/kernel
theorems.  This record is only a book-facing interface for those results. -/
structure Chapter14FiberMatrix (r : ℕ) where
  nonempty : 0 < r
  multiplicity : Chapter14IntegralVector r
  multiplicity_pos : ∀ i, 0 < multiplicity i
  matrix : Matrix (Fin r) (Fin r) ℤ
  symmetric : ∀ i j, matrix i j = matrix j i
  fiber_relation :
    ∀ i, ∑ j, matrix i j * multiplicity j = 0
  rational_kernel :
    ∀ v : Chapter14RationalVector r,
      chapter14MatrixVec
          (fun i j => (matrix i j : ℚ)) v = 0 ↔
        ∃ c : ℚ, v = c • (fun i => (multiplicity i : ℚ))
  negative_semidefinite :
    ∀ v : Chapter14RationalVector r,
      chapter14MatrixPairing
          (fun i j => (matrix i j : ℚ)) v v ≤ 0
  connected : Prop

/-!
The matrix record is a numerical view of the preceding special-fiber API.
This constructor keeps the Chapter 13 component cycles, multiplicities, kernel
theorem, and connected-fiber certificate as the source of the Chapter 14
fields instead of asking a caller to repeat those facts independently.
-/
def chapter14FiberMatrixOfChapter13
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hr : 0 < T.r)
    (C : Chapter13ConnectedFibersCertificate T) :
    Chapter14FiberMatrix T.r :=
  { nonempty := hr
    multiplicity := chapter13FiberMultiplicityVector T
    multiplicity_pos := by
      intro i
      sorry
    matrix := chapter13IntersectionMatrix T
    symmetric := by
      intro i j
      sorry
    fiber_relation := by
      intro i
      sorry
    rational_kernel := by
      intro v
      sorry
    negative_semidefinite := by
      intro v
      sorry
    connected := chapter13GraphConnected T }

def chapter14FiberRationalMatrix {r : ℕ}
    (F : Chapter14FiberMatrix r) : Matrix (Fin r) (Fin r) ℚ :=
  fun i j => (F.matrix i j : ℚ)

def chapter14FiberMultiplicityRat {r : ℕ} (F : Chapter14FiberMatrix r) :
    Chapter14RationalVector r :=
  fun i => (F.multiplicity i : ℚ)

theorem chapter14_fiber_rational_matrix_symmetric
    {r : ℕ} (F : Chapter14FiberMatrix r) (i j : Fin r) :
    chapter14FiberRationalMatrix F i j =
      chapter14FiberRationalMatrix F j i := by
  sorry

theorem chapter14_fiber_multiplicity_is_rational_kernel
    {r : ℕ} (F : Chapter14FiberMatrix r) :
    chapter14MatrixVec (chapter14FiberRationalMatrix F)
        (chapter14FiberMultiplicityRat F) = 0 := by
  sorry

def chapter14IntegralCompatibility {r : ℕ} (F : Chapter14FiberMatrix r)
    (d : Chapter14IntegralVector r) : Prop :=
  chapter14DotProduct F.multiplicity d = 0

def chapter14RationalCompatibility {r : ℕ} (F : Chapter14FiberMatrix r)
    (d : Chapter14RationalVector r) : Prop :=
  chapter14DotProduct (chapter14FiberMultiplicityRat F) d = 0

/-! ## Horizontal and vertical divisor vocabulary -/

/- LOCAL_DEPENDENCY_GUESS: the preceding divisor/intersection chapters are
expected to identify horizontal divisors with their component-intersection
vectors and generic degree.  The record deliberately exposes only the data
used by the balancing equations. -/
structure Chapter14HorizontalDivisor {r : ℕ} (F : Chapter14FiberMatrix r) where
  componentIntersections : Chapter14IntegralVector r
  genericDegree : ℤ
  genericDegree_zero : genericDegree = 0
  compatibility :
    chapter14IntegralCompatibility F componentIntersections

/-!
The horizontal-divisor vocabulary is likewise obtained from the Chapter 13
intersection and generic-degree interfaces.  In particular, the degree-zero
hypothesis supplies `genericDegree_zero`, while the divisor/fiber formula
supplies the component compatibility field.
-/
def chapter14HorizontalDivisorOfChapter13
    {R : Type u} [CommRing R] [IsDedekindDomain R]
    {A : Chapter13ArithmeticSurface R}
    {s : Spec (CommRingCat.of R)}
    (T : Chapter13SpecialFiberIntersectionData (A := A) (s := s))
    (hr : 0 < T.r)
    (C : Chapter13ConnectedFibersCertificate T)
    (G : Chapter13GenericDegreeData T)
    (D : Chapter13CartierDivisor A)
    (hD : chapter13DegreeZeroOnGenericFiber G D) :
    Chapter14HorizontalDivisor (chapter14FiberMatrixOfChapter13 T hr C) :=
  { componentIntersections := fun i =>
      T.intersection D.cycle (T.component i).cycle
    genericDegree := G.degreeOnGenericFiber D
    genericDegree_zero := by
      exact hD
    compatibility := by
      sorry }

abbrev Chapter14RationalVerticalDivisor {r : ℕ} (_F : Chapter14FiberMatrix r) :=
  Chapter14RationalVector r

def chapter14VerticalDivisorCoefficients {r : ℕ}
    {F : Chapter14FiberMatrix r}
    (v : Chapter14RationalVerticalDivisor F) : Chapter14RationalVector r :=
  v

def chapter14RationallyEquivalentModuloFiber {r : ℕ}
    (F : Chapter14FiberMatrix r)
    (v w : Chapter14RationalVerticalDivisor F) : Prop :=
  ∃ c : ℚ, v = w + c • chapter14FiberMultiplicityRat F

theorem chapter14_rationally_equivalent_modulo_fiber_refl
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (v : Chapter14RationalVerticalDivisor F) :
    chapter14RationallyEquivalentModuloFiber F v v := by
  exact ⟨0, by simp⟩

theorem chapter14_rationally_equivalent_modulo_fiber_symm
    {r : ℕ} {F : Chapter14FiberMatrix r}
    {v w : Chapter14RationalVerticalDivisor F}
    (h : chapter14RationallyEquivalentModuloFiber F v w) :
    chapter14RationallyEquivalentModuloFiber F w v := by
  sorry

theorem chapter14_rationally_equivalent_modulo_fiber_trans
    {r : ℕ} {F : Chapter14FiberMatrix r}
    {u v w : Chapter14RationalVerticalDivisor F}
    (huv : chapter14RationallyEquivalentModuloFiber F u v)
    (hvw : chapter14RationallyEquivalentModuloFiber F v w) :
    chapter14RationallyEquivalentModuloFiber F u w := by
  sorry

def chapter14Balanced {r : ℕ} (F : Chapter14FiberMatrix r)
    (d : Chapter14RationalVector r)
    (v : Chapter14RationalVerticalDivisor F) : Prop :=
  chapter14MatrixVec (chapter14FiberRationalMatrix F) v = -d

def chapter14CorrectedComponentVector {r : ℕ}
    (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F)
    (v : Chapter14RationalVerticalDivisor F) : Chapter14RationalVector r :=
  fun i => (D.componentIntersections i : ℚ) +
    chapter14MatrixVec (chapter14FiberRationalMatrix F) v i

theorem chapter14_balanced_iff_corrected_component_vector_eq_zero
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F)
    (v : Chapter14RationalVerticalDivisor F) :
    chapter14Balanced F
      (fun i => (D.componentIntersections i : ℚ)) v ↔
      chapter14CorrectedComponentVector F D v = 0 := by
  sorry

def chapter14VerticalIntersection {r : ℕ} (F : Chapter14FiberMatrix r)
    (v w : Chapter14RationalVerticalDivisor F) : ℚ :=
  chapter14MatrixPairing (chapter14FiberRationalMatrix F) v w

theorem chapter14_vertical_intersection_symmetric
    {r : ℕ} (F : Chapter14FiberMatrix r)
    (v w : Chapter14RationalVerticalDivisor F) :
    chapter14VerticalIntersection F v w =
      chapter14VerticalIntersection F w v := by
  sorry

def chapter14VerticalAgainstHorizontal {r : ℕ}
    (v : Chapter14RationalVector r)
    (d : Chapter14IntegralVector r) : ℚ :=
  chapter14DotProduct v (fun i => (d i : ℚ))

def chapter14FiberAgainstHorizontal {r : ℕ} (F : Chapter14FiberMatrix r)
    (D : Chapter14HorizontalDivisor F) : ℚ :=
  chapter14VerticalAgainstHorizontal
    (chapter14FiberMultiplicityRat F) D.componentIntersections

theorem chapter14_horizontal_degree_zero_component_compatibility
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F) :
    chapter14IntegralCompatibility F D.componentIntersections := by
  exact D.compatibility

theorem chapter14_fiber_against_horizontal_eq_zero
    {r : ℕ} {F : Chapter14FiberMatrix r}
    (D : Chapter14HorizontalDivisor F) :
    chapter14FiberAgainstHorizontal F D = 0 := by
  sorry

/-! ## Local intersections -/

/- LOCAL_DEPENDENCY_GUESS: the earlier local-intersection chapter supplies a
raw value for proper generic pairs and symmetry.  Requiring a separate
`genericDisjoint` predicate prevents the API from silently assigning a raw
self-intersection when the generic supports meet. -/
structure Chapter14LocalIntersectionData {r : ℕ}
    (F : Chapter14FiberMatrix r) where
  genericDisjoint : Chapter14HorizontalDivisor F →
    Chapter14HorizontalDivisor F → Prop
  rawIntersection : ∀ (D G : Chapter14HorizontalDivisor F),
    genericDisjoint D G → ℤ
  raw_symmetric : ∀ (D G : Chapter14HorizontalDivisor F) hDG hGD,
    rawIntersection D G hDG = rawIntersection G D hGD

/-! ## Surface and finite-flat interfaces used in §14.4 -/

/- LOCAL_DEPENDENCY_GUESS: the preceding regular-model chapters are expected
to supply the canonical scheme-theoretic surface predicates.  This small
record retains the exact hypotheses named in the source without importing a
later chapter or inventing a competing scheme API. -/
structure Chapter14ArithmeticSurfaceData (X : Type u) (S : Type v) where
  structureMap : X → S
  base_is_dedekind : Prop
  base_is_dedekind_evidence : base_is_dedekind
  regular : Prop
  regular_evidence : regular
  proper : Prop
  proper_evidence : proper
  flat : Prop
  flat_evidence : flat
  generic_fiber_smooth_geometrically_connected : Prop
  generic_fiber_smooth_geometrically_connected_evidence :
    generic_fiber_smooth_geometrically_connected

structure Chapter14FiniteFlatSurfaceMap
    {Y X : Type u} {S : Type v}
    (Ydata : Chapter14ArithmeticSurfaceData Y S)
    (Xdata : Chapter14ArithmeticSurfaceData X S)
    (f : Y → X) where
  finite : Prop
  finite_evidence : finite
  flat : Prop
  flat_evidence : flat
  over_base : ∀ y, Xdata.structureMap (f y) = Ydata.structureMap y
  generic_degree : ℕ
  generic_degree_pos : 0 < generic_degree

/-!
`pushforward` has rows indexed by downstairs components and columns by
upstairs components.  Its transpose is consequently the component-vector
map on pullback.  The matrix intertwining identity is the component form of
the projection formula.
-/
structure Chapter14ComponentCorrespondence
    {r t : ℕ} (down : Chapter14FiberMatrix r)
    (up : Chapter14FiberMatrix t) where
  pushforward : Matrix (Fin r) (Fin t) ℤ
  imageComponent : Fin t → Fin r
  residueDegree : Fin t → ℕ
  residueDegree_pos : ∀ j, 0 < residueDegree j
  pushforward_eq_residue_degree :
    ∀ i j, pushforward i j =
      if i = imageComponent j then (residueDegree j : ℤ) else 0
  pushforward_nonnegative : ∀ i j, 0 ≤ pushforward i j
  matrix_intertwining :
    ∀ v : Chapter14RationalVector r,
      chapter14MatrixVec (chapter14FiberRationalMatrix up)
          (fun j => ∑ i, (pushforward i j : ℚ) * v i) =
        (fun j => ∑ i, (pushforward i j : ℚ) *
          chapter14MatrixVec (chapter14FiberRationalMatrix down) v i)

def chapter14TransposeComponentVector
    {r t : ℕ} {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    (C : Chapter14ComponentCorrespondence down up)
    (d : Chapter14RationalVector r) : Chapter14RationalVector t :=
  fun j => ∑ i, (C.pushforward i j : ℚ) * d i

def chapter14PushforwardComponentVector
    {r t : ℕ} {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    (C : Chapter14ComponentCorrespondence down up)
    (c : Chapter14RationalVector t) : Chapter14RationalVector r :=
  fun i => ∑ j, (C.pushforward i j : ℚ) * c j

theorem chapter14_transpose_component_vector_apply
    {r t : ℕ} {down : Chapter14FiberMatrix r}
    {up : Chapter14FiberMatrix t}
    (C : Chapter14ComponentCorrespondence down up)
    (d : Chapter14RationalVector r) (j : Fin t) :
    chapter14TransposeComponentVector C d j =
      ∑ i, (C.pushforward i j : ℚ) * d i := by
  rfl

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter14
