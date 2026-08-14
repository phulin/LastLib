import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07

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

/- LOCAL_DEPENDENCY_GUESS: the normalization chapters should replace this
finite-algebra package by their canonical normalization and point-over-x API. -/
/-- A finite normalization of the local curve ring. -/
structure Chapter07FiniteNormalization
    {A : Type u} [CommRing A]
    (C : Chapter07LocalEffectiveCartierCurve A) where
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

/-- A branch of a finite normalization, with its DVR order and residue degree exposed. -/
structure Chapter07NormalizationBranch {A : Type u} [CommRing A] (g : A) where
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
  dvr :
    letI : CommRing valuationRing := commRingValuationRing
    IsDiscreteValuationRing valuationRing
  order : ℕ
  order_eq_addVal :
    letI : CommRing valuationRing := commRingValuationRing
    order = (IsDiscreteValuationRing.addVal valuationRing restrictedEquation).toNat
  residueDegree : ℕ

/-- The finite set of branches above the chosen point in a finite normalization. -/
structure Chapter07NormalizationBranchFamily
    {A : Type u} [CommRing A] [IsLocalRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) where
  normalization : Chapter07FiniteNormalization C
  branches : Type v
  finiteBranches : Fintype branches
  abovePoint : branches → Prop
  branch : ∀ q, Chapter07NormalizationBranch D.equation
  branch_factors_through_curve :
    ∀ q, (branch q).map C.equation = 0

noncomputable def Chapter07NormalizationBranchContribution
    {A : Type u} [CommRing A] [IsLocalRing A]
    {C D : Chapter07LocalEffectiveCartierCurve A}
    (F : Chapter07NormalizationBranchFamily C D) : ℕ := by
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

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
