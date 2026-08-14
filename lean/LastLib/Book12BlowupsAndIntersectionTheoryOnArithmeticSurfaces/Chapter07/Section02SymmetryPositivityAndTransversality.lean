import Mathlib.RingTheory.MvPolynomial.Homogeneous

import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07

universe u

/- LOCAL_DEPENDENCY_GUESS: the associated-graded/tangent-cone implementation is not present in
the earlier books, so this chapter-facing class records the initial homogeneous forms needed by
the blowup argument without identifying them with a later geometric model. -/
class Chapter07InitialFormData (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] where
  initialForm : Chapter07LocalEffectiveCartierCurve A →
    MvPolynomial (Fin 2) (IsLocalRing.ResidueField A)
  initialForm_isHomogeneous :
    ∀ C, MvPolynomial.IsHomogeneous (initialForm C) (Chapter07CurveMultiplicity C)
  initialForm_ne_zero : ∀ C, initialForm C ≠ 0

def Chapter07InitialForm {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Chapter07InitialFormData A] (C : Chapter07LocalEffectiveCartierCurve A) :
    MvPolynomial (Fin 2) (IsLocalRing.ResidueField A) :=
  Chapter07InitialFormData.initialForm C

/-- A tangent direction on the exceptional projective line. -/
def Chapter07TangentDirection (A : Type u) [CommRing A] [IsLocalRing A] :=
  Projectivization (IsLocalRing.ResidueField A)
    (Fin 2 → IsLocalRing.ResidueField A)

/-- Vanishing of an initial form at a projective tangent direction. -/
def Chapter07InitialFormVanishesAt {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A]
    [Chapter07InitialFormData A] (C : Chapter07LocalEffectiveCartierCurve A)
    (p : Chapter07TangentDirection A) : Prop :=
  (Chapter07InitialForm C).eval (Projectivization.rep p) = 0

/-- The tangent cones have a common point on the exceptional projective line. -/
def Chapter07SharesTangentDirection {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A]
    [Chapter07InitialFormData A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : Prop :=
  ∃ p : Chapter07TangentDirection A,
    Chapter07InitialFormVanishesAt C p ∧ Chapter07InitialFormVanishesAt D p

def Chapter07NoCommonTangentDirection {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A]
    [Chapter07InitialFormData A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : Prop :=
  ¬ Chapter07SharesTangentDirection C D

/- LOCAL_DEPENDENCY_GUESS: the blowup calculation which identifies the residual
contact above the first exceptional divisor is not exposed by the preceding
local-algebra API.  This package records exactly that bridge; the initial-form
class alone is deliberately not allowed to determine an unrelated intersection
number. -/
structure Chapter07TangentConeContactData
    (A : Type u) [CommRing A] [IsLocalRing A]
    [IsRegularLocalRing A] [IsNoetherianRing A] [Chapter07InitialFormData A]
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hCD : Chapter07ProperIntersectionAt C D) where
  residualContact : ℕ
  separation :
    Chapter07LocalIntersectionNumber C D =
      Chapter07CurveMultiplicity C * Chapter07CurveMultiplicity D + residualContact
  residual_zero_of_no_common_tangent :
    Chapter07NoCommonTangentDirection C D → residualContact = 0
  residual_positive_of_common_tangent :
    Chapter07SharesTangentDirection C D → 0 < residualContact

/-- For effective curves, positivity is exactly incidence at the closed point. -/
theorem chapter07_local_intersection_number_pos_iff
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hCD : Chapter07ProperIntersectionAt C D) :
    0 < Chapter07LocalIntersectionNumber C D ↔
      Chapter07PassesThrough C ∧ Chapter07PassesThrough D := by
  sorry

/-- Formula (7.2): the first exceptional contribution gives the multiplicity product lower bound. -/
theorem chapter07_local_intersection_number_ge_multiplicity_mul
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    [Chapter07InitialFormData A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07PassesThrough C) (hD : Chapter07PassesThrough D)
    (hCD : Chapter07ProperIntersectionAt C D)
    (T : Chapter07TangentConeContactData A C D hCD) :
    Chapter07CurveMultiplicity C * Chapter07CurveMultiplicity D ≤
      Chapter07LocalIntersectionNumber C D := by
  sorry

/-- If the initial forms have no common exceptional direction, no residual contact remains. -/
theorem chapter07_local_intersection_number_eq_multiplicity_mul_of_no_common_tangent_direction
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    [Chapter07InitialFormData A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07PassesThrough C) (hD : Chapter07PassesThrough D)
    (hCD : Chapter07ProperIntersectionAt C D)
    (T : Chapter07TangentConeContactData A C D hCD)
    (hT : Chapter07NoCommonTangentDirection C D) :
    Chapter07LocalIntersectionNumber C D =
      Chapter07CurveMultiplicity C * Chapter07CurveMultiplicity D := by
  sorry

/-- Smoothness of a Cartier curve at the point, expressed by the regular-surface multiplicity
criterion. -/
def Chapter07SmoothAt {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (C : Chapter07LocalEffectiveCartierCurve A) : Prop :=
  Chapter07CurveMultiplicity C = 1

def Chapter07DistinctTangentLines {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A]
    [Chapter07InitialFormData A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : Prop :=
  Chapter07NoCommonTangentDirection C D

/-- For two smooth curves, distinct tangent lines are equivalent to transverse intersection. -/
theorem chapter07_smooth_curves_intersection_eq_one_iff_distinct_tangent_lines
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    [Chapter07InitialFormData A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07SmoothAt C) (hD : Chapter07SmoothAt D)
    (hCpass : Chapter07PassesThrough C) (hDpass : Chapter07PassesThrough D)
    (hCD : Chapter07ProperIntersectionAt C D)
    (T : Chapter07TangentConeContactData A C D hCD) :
    Chapter07LocalIntersectionNumber C D = 1 ↔
      Chapter07DistinctTangentLines C D := by
  sorry

/-- A transverse pair of smooth equations is a regular system of parameters and has residue-field
quotient. -/
theorem chapter07_transverse_smooth_pair_is_regular_parameters
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    [Chapter07InitialFormData A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07SmoothAt C) (hD : Chapter07SmoothAt D)
    (hCpass : Chapter07PassesThrough C) (hDpass : Chapter07PassesThrough D)
    (hT : Chapter07DistinctTangentLines C D)
    (hCD : Chapter07ProperIntersectionAt C D)
    (T : Chapter07TangentConeContactData A C D hCD) :
    RingTheory.Sequence.IsRegular A [C.equation, D.equation] ∧
      Nonempty (A ⧸ Chapter07IntersectionIdeal C D ≃+* IsLocalRing.ResidueField A) := by
  sorry

/-- Tangency of two smooth curves forces local length at least two. -/
theorem chapter07_smooth_tangency_length_at_least_two
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    [Chapter07InitialFormData A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07SmoothAt C) (hD : Chapter07SmoothAt D)
    (hCpass : Chapter07PassesThrough C) (hDpass : Chapter07PassesThrough D)
    (hCD : Chapter07ProperIntersectionAt C D)
    (hT : Chapter07SharesTangentDirection C D)
    (T : Chapter07TangentConeContactData A C D hCD) :
    2 ≤ Chapter07LocalIntersectionNumber C D := by
  sorry

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
