import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Section02ThetaKernelsAndDualLattices

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open MeasureTheory NumberField
open scoped BigOperators ComplexConjugate NumberField nonZeroDivisors

/-! ### 4.3. Continuation and functional equation -/

noncomputable def chapter04ThetaMellinTail
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04FractionalIdeal K) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (1 : ℝ),
    ((chapter04ThetaAverage K D a t - 1 : ℝ) : ℂ) *
      chapter04MellinKernel s t ∂volume

noncomputable def chapter04ZeroVectorCorrection (s : ℂ) : ℂ :=
  1 / (s - 1) - 1 / s

theorem chapter04_zero_vector_correction_integral
    {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Set.Ioo (0 : ℝ) 1,
      ((t⁻¹ - 1 : ℝ) : ℂ) * chapter04MellinKernel s t ∂volume) =
      chapter04ZeroVectorCorrection s := by
  sorry

theorem chapter04_theta_mellin_split_at_one
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0)
    {s : ℂ} (hs : 1 < s.re) :
    chapter04ThetaMellinIntegral K D a s =
      chapter04ThetaMellinTail K D a s +
        chapter04ThetaMellinTail K D (chapter04DualFractionalIdeal K a) (1 - s) +
          chapter04ZeroVectorCorrection s := by
  sorry

theorem chapter04_theta_mellin_tail_entire
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0) :
    AnalyticOnNhd ℂ (chapter04ThetaMellinTail K D a) Set.univ := by
  sorry

theorem chapter04_theta_mellin_dual_tail_entire
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    {a : Chapter04FractionalIdeal K} (ha : a ≠ 0) :
    AnalyticOnNhd ℂ
      (chapter04ThetaMellinTail K D (chapter04DualFractionalIdeal K a)) Set.univ := by
  exact chapter04_theta_mellin_tail_entire K D
    (chapter04_dual_fractional_ideal_ne_zero K ha)

/-- The meromorphic continuation supplied by the split theta integral. -/
noncomputable def chapter04CompletedPartialZetaForIdeal
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04NonzeroFractionalIdeal K) (s : ℂ) : ℂ :=
  (chapter04MellinConstant K : ℂ)⁻¹ *
    (chapter04ThetaMellinTail K D (a : Chapter04FractionalIdeal K) s +
      chapter04ThetaMellinTail K D
        (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K)) (1 - s) +
        chapter04ZeroVectorCorrection s)

theorem chapter04_completed_partial_zeta_for_ideal_meromorphic
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04NonzeroFractionalIdeal K) :
    Meromorphic (chapter04CompletedPartialZetaForIdeal K D a) := by
  sorry

theorem chapter04_completed_partial_zeta_for_ideal_simple_poles
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04NonzeroFractionalIdeal K) :
    meromorphicOrderAt (chapter04CompletedPartialZetaForIdeal K D a) 0 = (-1 : ℤ) ∧
      meromorphicOrderAt (chapter04CompletedPartialZetaForIdeal K D a) 1 = (-1 : ℤ) ∧
        ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
          0 ≤ meromorphicOrderAt (chapter04CompletedPartialZetaForIdeal K D a) s := by
  sorry

theorem chapter04_completed_partial_zeta_for_ideal_duality
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04NonzeroFractionalIdeal K) (s : ℂ) :
    chapter04CompletedPartialZetaForIdeal K D a s =
      chapter04CompletedPartialZetaForIdeal K D
        (chapter04DualNonzeroFractionalIdeal K a) (1 - s) := by
  sorry

theorem chapter04_completed_partial_zeta_for_ideal_eq_euler_half_plane
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04NonzeroFractionalIdeal K)
    {s : ℂ} (hs : 1 < s.re) :
    chapter04CompletedPartialZetaForIdeal K D a s =
      (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
        chapter04ArchimedeanFactor K s *
          chapter04PartialZeta K (chapter04InverseIdealClass K a) s := by
  sorry

theorem chapter04_fractional_ideal_class_surjective
    (K : Type*) [Field K] [NumberField K] :
    ∀ C : ClassGroup (𝓞 K),
      ∃ a : Chapter04NonzeroFractionalIdeal K, ClassGroup.mk K a = C := by
  sorry

noncomputable def chapter04FractionalIdealRepresentative
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) : Chapter04NonzeroFractionalIdeal K :=
  Classical.choose (chapter04_fractional_ideal_class_surjective K C)

theorem chapter04_fractional_ideal_representative_class
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (chapter04FractionalIdealRepresentative K C) = C := by
  exact Classical.choose_spec (chapter04_fractional_ideal_class_surjective K C)

/- The duality on ideal representatives induces a permutation of the finite
   class group; it is not generally the plain inverse map because the
   different can contribute a nonprincipal ideal class. -/
noncomputable def chapter04DualPartialZetaClass
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) : ClassGroup (𝓞 K) :=
  (ClassGroup.mk K
    (chapter04DualNonzeroFractionalIdeal K
      (chapter04FractionalIdealRepresentative K C⁻¹)))⁻¹

theorem chapter04_dual_partial_zeta_class_involutive
    (K : Type*) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) :
    chapter04DualPartialZetaClass K (chapter04DualPartialZetaClass K C) = C := by
  sorry

/-- A class-indexed continuation, choosing an ideal in the inverse class so
    that the theta orbit formula has the source's class label. -/
noncomputable def chapter04CompletedPartialZetaContinuation
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  chapter04CompletedPartialZetaForIdeal K D
    (chapter04FractionalIdealRepresentative K C⁻¹) s

theorem chapter04_completed_partial_zeta_continuation_eq_partial_factor
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (C : ClassGroup (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    chapter04CompletedPartialZetaContinuation K D C s =
      (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
        chapter04ArchimedeanFactor K s * chapter04PartialZeta K C s := by
  sorry

theorem chapter04_completed_partial_zeta_continuation_independent_of_representative
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (C : ClassGroup (𝓞 K)) (s : ℂ)
    (a b : Chapter04NonzeroFractionalIdeal K)
    (ha : ClassGroup.mk K a = C⁻¹) (hb : ClassGroup.mk K b = C⁻¹) :
    chapter04CompletedPartialZetaForIdeal K D a s =
      chapter04CompletedPartialZetaForIdeal K D b s := by
  sorry

theorem chapter04_completed_partial_zeta_duality
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (C : ClassGroup (𝓞 K)) (s : ℂ) :
    chapter04CompletedPartialZetaContinuation K D C s =
      chapter04CompletedPartialZetaContinuation K D
        (chapter04DualPartialZetaClass K C) (1 - s) := by
  sorry

noncomputable def chapter04SumCompletedPartialZeta
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) (s : ℂ) : ℂ :=
  ∑' C : ClassGroup (𝓞 K), chapter04CompletedPartialZetaContinuation K D C s

theorem chapter04_sum_completed_partial_zeta_eq_completed_dedekind_zeta
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) (s : ℂ) :
    chapter04SumCompletedPartialZeta K D s =
      chapter04CompletedDedekindZeta K s := by
  sorry

theorem chapter04_completed_dedekind_zeta_meromorphic
    (K : Type*) [Field K] [NumberField K] :
    Meromorphic (chapter04CompletedDedekindZeta K) := by
  sorry

theorem chapter04_completed_dedekind_zeta_functional_equation
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04CompletedDedekindZeta K s =
      chapter04CompletedDedekindZeta K (1 - s) := by
  sorry

theorem chapter04_completed_dedekind_zeta_simple_poles
    (K : Type*) [Field K] [NumberField K] :
    meromorphicOrderAt (chapter04CompletedDedekindZeta K) 0 = (-1 : ℤ) ∧
      meromorphicOrderAt (chapter04CompletedDedekindZeta K) 1 = (-1 : ℤ) ∧
        ∀ s : ℂ, s ≠ 0 → s ≠ 1 →
          0 ≤ meromorphicOrderAt (chapter04CompletedDedekindZeta K) s := by
  sorry

/-! The rational model. -/

theorem chapter04_rational_class_group_trivial :
    ∀ C : ClassGroup (𝓞 ℚ), C = 1 := by
  sorry

theorem chapter04_rational_unit_log_space_zero
    (x : chapter04UnitLogHyperplane ℚ) : x = 0 := by
  sorry

noncomputable def chapter04RationalTheta (u : ℝ) : ℝ :=
  ∑' m : ℤ, Real.exp (-Real.pi * u * (m : ℝ) ^ 2)

theorem chapter04_rational_theta_poisson
    {u : ℝ} (hu : 0 < u) :
    chapter04RationalTheta u =
      u⁻¹ ^ (1 / 2 : ℝ) * chapter04RationalTheta u⁻¹ := by
  sorry

noncomputable def chapter04RationalThetaMellin (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    ∫ u in Set.Ioi (0 : ℝ),
      ((chapter04RationalTheta u - 1 : ℝ) : ℂ) *
        ((u : ℂ) ^ (s / 2) / (u : ℂ)) ∂volume

theorem chapter04_rational_theta_mellin_eq_completed_riemann_zeta
    {s : ℂ} (hs : 1 < s.re) :
    chapter04RationalThetaMellin s =
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s := by
  sorry

theorem chapter04_rational_theta_mellin_functional_equation
    (s : ℂ) :
    chapter04RationalThetaMellin s = chapter04RationalThetaMellin (1 - s) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
