import Mathlib.RingTheory.LocalRing.ResidueField.Basic

import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07

noncomputable section

universe u v

/-- The bivariate formal power-series ring used for the local examples. -/
abbrev Chapter07BivariatePowerSeries (k : Type u) := MvPowerSeries (Fin 2) k

def chapter07_u (k : Type u) [Field k] : Chapter07BivariatePowerSeries k :=
  MvPowerSeries.X 0

def chapter07_v (k : Type u) [Field k] : Chapter07BivariatePowerSeries k :=
  MvPowerSeries.X 1

/-- A power-series equation viewed as a local effective Cartier curve. -/
def chapter07_powerSeriesCurve {k : Type u} [Field k]
    (f : Chapter07BivariatePowerSeries k) :
    f ∈ nonZeroDivisors (Chapter07BivariatePowerSeries k) →
    Chapter07LocalEffectiveCartierCurve (Chapter07BivariatePowerSeries k) :=
  fun hf =>
    { equation := f
      equation_is_regular := hf }

def chapter07_powerSeries_v_zero (k : Type u) [Field k] :
    Chapter07LocalEffectiveCartierCurve (Chapter07BivariatePowerSeries k) :=
  chapter07_powerSeriesCurve (chapter07_v k) (by sorry)

def chapter07_powerSeries_v_sub_u_pow (k : Type u) [Field k] (r : ℕ) :
    Chapter07LocalEffectiveCartierCurve (Chapter07BivariatePowerSeries k) :=
  chapter07_powerSeriesCurve (chapter07_v k - chapter07_u k ^ r) (by sorry)

def chapter07_powerSeries_u_zero (k : Type u) [Field k] :
    Chapter07LocalEffectiveCartierCurve (Chapter07BivariatePowerSeries k) :=
  chapter07_powerSeriesCurve (chapter07_u k) (by sorry)

def chapter07_powerSeries_cusp (k : Type u) [Field k] :
    Chapter07LocalEffectiveCartierCurve (Chapter07BivariatePowerSeries k) :=
  chapter07_powerSeriesCurve (chapter07_v k ^ 2 - chapter07_u k ^ 3) (by sorry)

/-- The contact-order computation in `k[[u,v]]`. -/
theorem chapter07_powerSeries_contact_order (k : Type u) [Field k] (r : ℕ) :
    Chapter07LocalIntersectionMultiplicity
        (chapter07_powerSeries_v_zero k)
        (chapter07_powerSeries_v_sub_u_pow k r) = (r : ℕ∞) := by
  sorry

/-- The quotient in the contact-order example is the one-variable quotient `k[[u]]/(u^r)`. -/
theorem chapter07_powerSeries_contact_quotient
    (k : Type u) [Field k] (r : ℕ) :
    Nonempty
      ((Chapter07BivariatePowerSeries k ⧸
          Chapter07IntersectionIdeal (chapter07_powerSeries_v_zero k)
            (chapter07_powerSeries_v_sub_u_pow k r)) ≃ₐ[k]
        (PowerSeries k ⧸ Ideal.span ({PowerSeries.X ^ r} : Set (PowerSeries k)))) := by
  sorry

/-- The coordinate axes meet with multiplicity one. -/
theorem chapter07_powerSeries_axes_intersection_one (k : Type u) [Field k] :
    Chapter07LocalIntersectionMultiplicity
        (chapter07_powerSeries_u_zero k) (chapter07_powerSeries_v_zero k) = 1 := by
  sorry

/-- The tangent line to the cusp sees order three. -/
theorem chapter07_powerSeries_cusp_tangent_line (k : Type u) [Field k] :
    Chapter07LocalIntersectionMultiplicity
        (chapter07_powerSeries_v_zero k) (chapter07_powerSeries_cusp k) = 3 := by
  sorry

/-- A transverse line meets the same cusp with order two. -/
theorem chapter07_powerSeries_cusp_transverse_line (k : Type u) [Field k] :
    Chapter07LocalIntersectionMultiplicity
        (chapter07_powerSeries_u_zero k) (chapter07_powerSeries_cusp k) = 2 := by
  sorry

theorem chapter07_powerSeries_cusp_tangent_quotient (k : Type u) [Field k] :
    Nonempty
      ((Chapter07BivariatePowerSeries k ⧸
          Chapter07IntersectionIdeal (chapter07_powerSeries_v_zero k)
            (chapter07_powerSeries_cusp k)) ≃ₐ[k]
        (PowerSeries k ⧸ Ideal.span ({PowerSeries.X ^ 3} : Set (PowerSeries k)))) := by
  sorry

theorem chapter07_powerSeries_cusp_transverse_quotient (k : Type u) [Field k] :
    Nonempty
      ((Chapter07BivariatePowerSeries k ⧸
          Chapter07IntersectionIdeal (chapter07_powerSeries_u_zero k)
            (chapter07_powerSeries_cusp k)) ≃ₐ[k]
        (PowerSeries k ⧸ Ideal.span ({PowerSeries.X ^ 2} : Set (PowerSeries k)))) := by
  sorry

/-- The residue-field degree multiplying a local contribution over a base field. -/
noncomputable def Chapter07ResidueExtensionDegree
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] : ℕ :=
  Module.finrank K L

noncomputable def Chapter07BaseFieldWeightedContribution
    (n : ℕ) (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] : ℕ :=
  n * Chapter07ResidueExtensionDegree K L

/-- Formula (7.3), written with Mathlib's finite-dimensional degree. -/
theorem chapter07_base_field_weighted_local_contribution
    (n : ℕ) (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Chapter07BaseFieldWeightedContribution n K L =
      n * Module.finrank K L := by
  rfl

def Chapter07IntegralCurve {A : Type u} [CommRing A]
    (C : Chapter07LocalEffectiveCartierCurve A) : Prop :=
  IsDomain (Chapter07CurveRing C)

/- The second equation is restricted to the first curve before a branch order is
computed.  A branch of the normalization therefore has source `A/(f)`, not
the ambient surface ring `A`. -/
def Chapter07RestrictedEquation
    {A : Type u} [CommRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) : Chapter07CurveRing C :=
  Ideal.Quotient.mk (Ideal.span ({C.equation} : Set A)) D.equation

def Chapter07CurveRingMap
    {A : Type u} [CommRing A]
    (C : Chapter07LocalEffectiveCartierCurve A) :
    A →+* Chapter07CurveRing C :=
  Ideal.Quotient.mk (Ideal.span ({C.equation} : Set A))

/- LOCAL_DEPENDENCY_GUESS: the normalization chapters should replace this
finite-algebra package by their canonical normalization and point-over-x API. -/
/-- A finite normalization of the local curve ring. -/
structure Chapter07FiniteNormalization
    {A : Type u} [CommRing A]
    (C : Chapter07LocalEffectiveCartierCurve A) where
  integral : Chapter07IntegralCurve C
  normalization : Type v
  commRingNormalization : CommRing normalization
  algebraNormalization :
    letI : CommRing normalization := commRingNormalization
    Algebra (Chapter07CurveRing C) normalization
  finite :
    letI : CommRing normalization := commRingNormalization
    letI : Algebra (Chapter07CurveRing C) normalization := algebraNormalization
    Module.Finite (Chapter07CurveRing C) normalization
  domain :
    letI : CommRing normalization := commRingNormalization
    IsDomain normalization
  injective :
    letI : CommRing normalization := commRingNormalization
    letI : Algebra (Chapter07CurveRing C) normalization := algebraNormalization
    Function.Injective (algebraMap (Chapter07CurveRing C) normalization)
  integrallyClosed :
    letI : CommRing normalization := commRingNormalization
    IsIntegrallyClosed normalization

noncomputable def Chapter07FiniteNormalizationMap
    {A : Type u} [CommRing A]
    {C : Chapter07LocalEffectiveCartierCurve A}
    (N : Chapter07FiniteNormalization.{u, v} C) :
    letI : CommRing N.normalization := N.commRingNormalization
    Chapter07CurveRing C →+* N.normalization := by
  letI : CommRing N.normalization := N.commRingNormalization
  letI : Algebra (Chapter07CurveRing C) N.normalization := N.algebraNormalization
  exact algebraMap _ _

/-- A branch of a finite normalization, with its DVR order and residue extension exposed. -/
structure Chapter07NormalizationBranch
    {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Type u} [CommRing A]
    (baseMap : R →+* A) (g : A) where
  valuationRing : Type v
  commRingValuationRing : CommRing valuationRing
  map :
    letI : CommRing valuationRing := commRingValuationRing
    A →+* valuationRing
  restrictedEquation :
    letI : CommRing valuationRing := commRingValuationRing
    valuationRing
  restriction_eq_map :
    letI : CommRing valuationRing := commRingValuationRing
    restrictedEquation = map g
  domain :
    letI : CommRing valuationRing := commRingValuationRing
    IsDomain valuationRing
  dvr :
    letI : CommRing valuationRing := commRingValuationRing
    letI : IsDomain valuationRing := domain
    IsDiscreteValuationRing valuationRing
  order : ℕ
  order_eq_addVal :
    letI : CommRing valuationRing := commRingValuationRing
    letI : IsDomain valuationRing := domain
    letI : IsDiscreteValuationRing valuationRing := dvr
    order = (IsDiscreteValuationRing.addVal valuationRing restrictedEquation).toNat
  map_from_base_local :
    letI : CommRing valuationRing := commRingValuationRing
    letI : IsDomain valuationRing := domain
    letI : IsDiscreteValuationRing valuationRing := dvr
    IsLocalHom (map.comp baseMap)
  residueField_finite :
    letI : CommRing valuationRing := commRingValuationRing
    letI : IsDomain valuationRing := domain
    letI : IsDiscreteValuationRing valuationRing := dvr
    letI : IsLocalHom (map.comp baseMap) := map_from_base_local
    letI : Algebra (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField valuationRing) :=
      RingHom.toAlgebra (IsLocalRing.ResidueField.map (map.comp baseMap))
    FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField valuationRing)

noncomputable def Chapter07NormalizationBranch.residueDegree
    {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Type u} [CommRing A] {baseMap : R →+* A} {g : A}
    (B : Chapter07NormalizationBranch.{u, v} baseMap g) : ℕ := by
  letI : CommRing B.valuationRing := B.commRingValuationRing
  letI : IsDomain B.valuationRing := B.domain
  letI : IsDiscreteValuationRing B.valuationRing := B.dvr
  letI : IsLocalHom (B.map.comp baseMap) := B.map_from_base_local
  letI : Algebra (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField B.valuationRing) :=
    RingHom.toAlgebra (IsLocalRing.ResidueField.map (B.map.comp baseMap))
  letI : FiniteDimensional (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField B.valuationRing) := B.residueField_finite
  exact Module.finrank (IsLocalRing.ResidueField R)
    (IsLocalRing.ResidueField B.valuationRing)

theorem Chapter07NormalizationBranch.residueDegree_pos
    {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Type u} [CommRing A] {baseMap : R →+* A} {g : A}
    (B : Chapter07NormalizationBranch.{u, v} baseMap g) :
    0 < B.residueDegree := by
  sorry

def Chapter07BranchLiesOverClosedPoint
    {A : Type u} [CommRing A] [IsLocalRing A]
    (C : Chapter07LocalEffectiveCartierCurve A)
    {g : Chapter07CurveRing C}
    (B : Chapter07NormalizationBranch.{u, v} (Chapter07CurveRingMap C) g) : Prop := by
  letI : CommRing B.valuationRing := B.commRingValuationRing
  letI : IsDomain B.valuationRing := B.domain
  letI : IsDiscreteValuationRing B.valuationRing := B.dvr
  exact ∀ a ∈ IsLocalRing.maximalIdeal A,
    B.map (Chapter07CurveRingMap C a) ∈
      IsLocalRing.maximalIdeal B.valuationRing

def Chapter07BranchFactorsThroughNormalization
    {A : Type u} [CommRing A] [IsLocalRing A]
    (C : Chapter07LocalEffectiveCartierCurve A)
    (N : Chapter07FiniteNormalization.{u, v} C)
    {g : Chapter07CurveRing C}
    (B : Chapter07NormalizationBranch.{u, v} (Chapter07CurveRingMap C) g) : Prop := by
  exact ∃ φ :
      letI : CommRing N.normalization := N.commRingNormalization
      letI : CommRing B.valuationRing := B.commRingValuationRing
      N.normalization →+* B.valuationRing,
    letI : CommRing N.normalization := N.commRingNormalization
    letI : CommRing B.valuationRing := B.commRingValuationRing
    B.map = φ.comp (Chapter07FiniteNormalizationMap N)

/-- The finite set of branches above the chosen point in a finite normalization. -/
structure Chapter07NormalizationBranchFamily
    {A : Type u} [CommRing A] [IsLocalRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) where
  normalization : Chapter07FiniteNormalization.{u, v} C
  branches : Type v
  finiteBranches : Fintype branches
  branch : branches →
    Chapter07NormalizationBranch.{u, v} (Chapter07CurveRingMap C)
      (Chapter07RestrictedEquation C D)
  abovePoint : branches → Prop
  abovePoint_specification :
    ∀ q, abovePoint q ↔ Chapter07BranchLiesOverClosedPoint C (branch q)
  branch_over_normalization :
    ∀ q, Chapter07BranchFactorsThroughNormalization C normalization (branch q)
  branch_injective : Function.Injective branch
  exhaustive_abovePoint :
    ∀ B : Chapter07NormalizationBranch.{u, v} (Chapter07CurveRingMap C)
      (Chapter07RestrictedEquation C D),
      Chapter07BranchFactorsThroughNormalization C normalization B →
      Chapter07BranchLiesOverClosedPoint C B →
      ∃ q, abovePoint q ∧ B = branch q

noncomputable def Chapter07NormalizationBranchContribution
    {A : Type u} [CommRing A] [IsLocalRing A]
    {C D : Chapter07LocalEffectiveCartierCurve A}
    (F : Chapter07NormalizationBranchFamily C D) : ℕ := by
  classical
  letI := F.finiteBranches
  exact ∑ q : F.branches,
    if F.abovePoint q then (F.branch q).order * (F.branch q).residueDegree else 0

/-- One-branch interpretation of local intersection multiplicity under finite normalization. -/
theorem chapter07_local_intersection_eq_normalization_branch_sum
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    (C D : Chapter07LocalEffectiveCartierCurve A)
    (hC : Chapter07IntegralCurve C)
    (hCD : Chapter07ProperIntersectionAt C D)
    (F : Chapter07NormalizationBranchFamily C D) :
    Chapter07LocalIntersectionNumber C D =
      Chapter07NormalizationBranchContribution F := by
  sorry

end
end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
