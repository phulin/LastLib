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
  (chapter04MellinConstant K D : ℂ)⁻¹ *
    (chapter04ThetaMellinTail K D (a : Chapter04FractionalIdeal K) s +
      chapter04ThetaMellinTail K D
        (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K)) (1 - s) +
        chapter04ZeroVectorCorrection s)

theorem chapter04_completed_partial_zeta_for_ideal_meromorphic
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04NonzeroFractionalIdeal K) :
    Meromorphic (chapter04CompletedPartialZetaForIdeal K D a) := by
  have htail₁ : Meromorphic (chapter04ThetaMellinTail K D
      (a : Chapter04FractionalIdeal K)) :=
    meromorphicOn_univ.mp
      (chapter04_theta_mellin_tail_entire K D (Units.ne_zero a)).meromorphicOn
  have htail₂base : Meromorphic (chapter04ThetaMellinTail K D
      (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K))) :=
    meromorphicOn_univ.mp
      (chapter04_theta_mellin_tail_entire K D
        (chapter04_dual_fractional_ideal_ne_zero K (Units.ne_zero a))).meromorphicOn
  have htail₂ : Meromorphic (fun s : ℂ =>
      chapter04ThetaMellinTail K D
        (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K)) (1 - s)) := by
    intro s
    simpa [Function.comp_def] using
      (htail₂base (1 - s)).comp_analyticAt (by fun_prop)
  have hden₁ : Meromorphic (fun s : ℂ => s - 1) := by
    intro s
    fun_prop
  have hden₀ : Meromorphic (fun s : ℂ => s) := by
    intro s
    fun_prop
  have hcorr : Meromorphic (fun s : ℂ =>
      (1 : ℂ) / (s - 1) - 1 / s) := by
    intro s
    fun_prop
  have hsum : Meromorphic (fun s : ℂ =>
      chapter04ThetaMellinTail K D (a : Chapter04FractionalIdeal K) s +
        chapter04ThetaMellinTail K D
          (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K)) (1 - s) +
        ((1 : ℂ) / (s - 1) - 1 / s)) :=
    (htail₁.add htail₂).add hcorr
  let : NormedAddCommGroup ℂ := Complex.instNormedAddCommGroup
  let : NormedSpace ℂ ℂ :=
    (CommCStarAlgebra.toNonUnitalCommCStarAlgebra ℂ).toNonUnitalCStarAlgebra.toNormedSpace
  intro s
  unfold chapter04CompletedPartialZetaForIdeal chapter04ZeroVectorCorrection
  convert (hsum s).const_smul ((chapter04MellinConstant K D : ℂ)⁻¹) using 1
  ext z
  simp [smul_eq_mul]

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
  unfold chapter04CompletedPartialZetaForIdeal
  rw [chapter04_dual_nonzero_fractional_ideal_coe,
    chapter04_dual_dual_fractional_ideal K (Units.ne_zero a)]
  congr 1
  simp [chapter04ZeroVectorCorrection]
  by_cases hs0 : s = 0
  · simp [hs0, add_comm]
  by_cases hs1 : s = 1
  · simp [hs1, add_comm]
  field_simp [hs0, hs1]
  ring

theorem chapter04_completed_partial_zeta_for_ideal_eq_euler_half_plane
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K)
    (a : Chapter04NonzeroFractionalIdeal K)
    {s : ℂ} (hs : 1 < s.re) :
    chapter04CompletedPartialZetaForIdeal K D a s =
      (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
        chapter04ArchimedeanFactor K s *
          chapter04PartialZeta K (chapter04InverseIdealClass K a) s := by
  unfold chapter04CompletedPartialZetaForIdeal
  rw [← chapter04_theta_mellin_split_at_one K D
      (a := (a : Chapter04FractionalIdeal K)) (Units.ne_zero a) hs,
    chapter04_theta_mellin_eq_completed_partial_zeta K D a hs]
  field_simp [chapter04_mellin_constant_ne_zero K D]

theorem chapter04_fractional_ideal_class_surjective
    (K : Type*) [Field K] [NumberField K] :
    ∀ C : ClassGroup (𝓞 K),
      ∃ a : Chapter04NonzeroFractionalIdeal K, ClassGroup.mk K a = C := by
  intro C
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C
  refine ⟨FractionalIdeal.mk0 K J, ?_⟩
  rw [ClassGroup.mk_mk0]
  exact hJ

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
  have hdual_map : ∀ (x y : Chapter04NonzeroFractionalIdeal K),
      ClassGroup.mk K x = ClassGroup.mk K y →
        ClassGroup.mk K (chapter04DualNonzeroFractionalIdeal K x) =
        ClassGroup.mk K (chapter04DualNonzeroFractionalIdeal K y) := by
    intro x y hxy
    have hxi :
        ClassGroup.mk K
            (Units.mk0 ((x : Chapter04FractionalIdeal K)⁻¹)
              (inv_ne_zero (Units.ne_zero x))) =
          (ClassGroup.mk K x)⁻¹ := by
      rw [← map_inv]
      congr 1
      ext
      simp
    have hyi :
        ClassGroup.mk K
            (Units.mk0 ((y : Chapter04FractionalIdeal K)⁻¹)
              (inv_ne_zero (Units.ne_zero y))) =
          (ClassGroup.mk K y)⁻¹ := by
      rw [← map_inv]
      congr 1
      ext
      simp
    simp [chapter04DualNonzeroFractionalIdeal, chapter04DualFractionalIdeal,
      chapter04DifferentFractionalIdeal, hxi, hyi, hxy]
  have hC := chapter04_fractional_ideal_representative_class K (C⁻¹)
  have hFC := chapter04_fractional_ideal_representative_class K
    ((chapter04DualPartialZetaClass K C)⁻¹)
  have hdual := hdual_map
    (chapter04FractionalIdealRepresentative K (chapter04DualPartialZetaClass K C)⁻¹)
    (chapter04DualNonzeroFractionalIdeal K
      (chapter04FractionalIdealRepresentative K C⁻¹)) hFC
  have hdd :
      ClassGroup.mk K
          (chapter04DualNonzeroFractionalIdeal K
            (chapter04DualNonzeroFractionalIdeal K
              (chapter04FractionalIdealRepresentative K C⁻¹))) =
        ClassGroup.mk K (chapter04FractionalIdealRepresentative K C⁻¹) := by
    congr 1
    apply Units.ext
    exact chapter04_dual_dual_fractional_ideal K
      (Units.ne_zero (chapter04FractionalIdealRepresentative K C⁻¹))
  calc
    chapter04DualPartialZetaClass K (chapter04DualPartialZetaClass K C) =
        (ClassGroup.mk K
          (chapter04DualNonzeroFractionalIdeal K
            (chapter04FractionalIdealRepresentative K
              (chapter04DualPartialZetaClass K C)⁻¹)))⁻¹ := rfl
    _ = (ClassGroup.mk K
          (chapter04DualNonzeroFractionalIdeal K
            (chapter04DualNonzeroFractionalIdeal K
              (chapter04FractionalIdealRepresentative K C⁻¹))))⁻¹ := by
      rw [hdual]
    _ = (ClassGroup.mk K
          (chapter04FractionalIdealRepresentative K C⁻¹))⁻¹ := by
      rw [hdd]
    _ = C := by rw [hC]; simp

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
  simpa [chapter04CompletedPartialZetaContinuation, chapter04InverseIdealClass,
    chapter04_fractional_ideal_representative_class] using
    (chapter04_completed_partial_zeta_for_ideal_eq_euler_half_plane K D
      (chapter04FractionalIdealRepresentative K C⁻¹) hs)

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
  have hdual_class :
      ClassGroup.mk K
          (chapter04DualNonzeroFractionalIdeal K
            (chapter04FractionalIdealRepresentative K C⁻¹)) =
        (chapter04DualPartialZetaClass K C)⁻¹ := by
    simp [chapter04DualPartialZetaClass]
  have hrep_class :=
    chapter04_fractional_ideal_representative_class K
      ((chapter04DualPartialZetaClass K C)⁻¹)
  calc
    chapter04CompletedPartialZetaContinuation K D C s =
        chapter04CompletedPartialZetaForIdeal K D
          (chapter04FractionalIdealRepresentative K C⁻¹) s := rfl
    _ = chapter04CompletedPartialZetaForIdeal K D
          (chapter04DualNonzeroFractionalIdeal K
            (chapter04FractionalIdealRepresentative K C⁻¹)) (1 - s) :=
      chapter04_completed_partial_zeta_for_ideal_duality K D
        (chapter04FractionalIdealRepresentative K C⁻¹) s
    _ = chapter04CompletedPartialZetaForIdeal K D
          (chapter04FractionalIdealRepresentative K
            (chapter04DualPartialZetaClass K C)⁻¹) (1 - s) :=
      chapter04_completed_partial_zeta_continuation_independent_of_representative
        K D (chapter04DualPartialZetaClass K C) (1 - s)
        (chapter04DualNonzeroFractionalIdeal K
          (chapter04FractionalIdealRepresentative K C⁻¹))
        (chapter04FractionalIdealRepresentative K
          (chapter04DualPartialZetaClass K C)⁻¹)
        hdual_class hrep_class
    _ = chapter04CompletedPartialZetaContinuation K D
          (chapter04DualPartialZetaClass K C) (1 - s) := rfl

noncomputable def chapter04SumCompletedPartialZeta
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter04UnitFundamentalDomain K) (s : ℂ) : ℂ :=
  ∑' C : ClassGroup (𝓞 K), chapter04CompletedPartialZetaContinuation K D C s

noncomputable def chapter04ChosenUnitFundamentalDomain
    (K : Type*) [Field K] [NumberField K] : Chapter04UnitFundamentalDomain K :=
  Classical.choice (chapter04_exists_unit_fundamental_domain K)

/- The global completion is the continuation obtained from one fixed
   normalized unit fundamental domain.  The representative-independence
   theorem below concerns the ideal representative inside each class; domain
   independence would require an additional Haar-measure comparison theorem. -/
noncomputable def chapter04CompletedDedekindZeta
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  chapter04SumCompletedPartialZeta K
    (chapter04ChosenUnitFundamentalDomain K) s

theorem chapter04_sum_completed_partial_zeta_eq_completed_dedekind_zeta
    (K : Type*) [Field K] [NumberField K]
    (s : ℂ) :
    chapter04SumCompletedPartialZeta K
        (chapter04ChosenUnitFundamentalDomain K) s =
      chapter04CompletedDedekindZeta K s := by
  rfl

theorem chapter04_completed_dedekind_zeta_agrees_on_euler_half_plane
    (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    chapter04CompletedDedekindZeta K s =
      chapter04EulerCompletedDedekindZeta K s := by
  sorry

theorem chapter04_completed_dedekind_zeta_meromorphic
    (K : Type*) [Field K] [NumberField K] :
    Meromorphic (chapter04CompletedDedekindZeta K) := by
  unfold chapter04CompletedDedekindZeta chapter04SumCompletedPartialZeta
  have hsum : Meromorphic (∑ C ∈ Finset.univ,
      chapter04CompletedPartialZetaContinuation K
        (chapter04ChosenUnitFundamentalDomain K) C) := by
    apply Meromorphic.sum
    intro C hC
    change Meromorphic (chapter04CompletedPartialZetaForIdeal K
      (chapter04ChosenUnitFundamentalDomain K)
      (chapter04FractionalIdealRepresentative K C⁻¹))
    exact chapter04_completed_partial_zeta_for_ideal_meromorphic K
      (chapter04ChosenUnitFundamentalDomain K)
      (chapter04FractionalIdealRepresentative K C⁻¹)
  convert hsum using 1
  funext s
  rw [Finset.sum_apply]
  change (∑' C : ClassGroup (𝓞 K),
      chapter04CompletedPartialZetaContinuation K
        (chapter04ChosenUnitFundamentalDomain K) C s) =
    ∑ C ∈ Finset.univ,
      chapter04CompletedPartialZetaContinuation K
        (chapter04ChosenUnitFundamentalDomain K) C s
  exact tsum_eq_sum (s := Finset.univ) (fun C hC => by simp at hC)

theorem chapter04_completed_dedekind_zeta_functional_equation
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04CompletedDedekindZeta K s =
      chapter04CompletedDedekindZeta K (1 - s) := by
  unfold chapter04CompletedDedekindZeta chapter04SumCompletedPartialZeta
  rw [tsum_eq_sum (s := Finset.univ) (fun C hC => by simp at hC),
    tsum_eq_sum (s := Finset.univ) (fun C hC => by simp at hC)]
  have hInv : Function.Involutive (chapter04DualPartialZetaClass K) :=
    fun C => chapter04_dual_partial_zeta_class_involutive K C
  refine Fintype.sum_bijective (chapter04DualPartialZetaClass K) hInv.bijective _ _ ?_
  intro C
  exact chapter04_completed_partial_zeta_duality K
    (chapter04ChosenUnitFundamentalDomain K) C s

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
  intro C
  have hcard : Fintype.card (ClassGroup (𝓞 ℚ)) = 1 := by
    exact Rat.classNumber_eq
  obtain ⟨C₀, hC₀⟩ := Fintype.card_eq_one_iff.mp hcard
  exact (hC₀ C).trans (hC₀ 1).symm

theorem chapter04_rational_unit_log_space_zero
    (x : chapter04UnitLogHyperplane ℚ) : x = 0 := by
  apply Subtype.ext
  funext v
  have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
  subst v
  have hx := x.property
  change (∑ v : InfinitePlace ℚ, (v.mult : ℝ) * x.1 v) = 0 at hx
  rw [Fintype.sum_unique] at hx
  have hdefault : (default : InfinitePlace ℚ) = Rat.infinitePlace :=
    Subsingleton.elim _ _
  rw [hdefault] at hx
  norm_num at hx
  simpa using hx

noncomputable def chapter04RationalTheta (u : ℝ) : ℝ :=
  ∑' m : ℤ, Real.exp (-Real.pi * u * (m : ℝ) ^ 2)

theorem chapter04_rational_theta_poisson
    {u : ℝ} (hu : 0 < u) :
    chapter04RationalTheta u =
      u⁻¹ ^ (1 / 2 : ℝ) * chapter04RationalTheta u⁻¹ := by
  rw [chapter04RationalTheta, chapter04RationalTheta]
  rw [Real.inv_rpow hu.le]
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (Real.tsum_exp_neg_mul_int_sq hu)

/- The raw Mellin integral is only defined by convergence in the Euler
   half-plane.  It is kept separate from the meromorphic continuation used
   by the functional equation below. -/
noncomputable def chapter04RationalThetaMellinIntegral (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    ∫ u in Set.Ioi (0 : ℝ),
      ((chapter04RationalTheta u - 1 : ℝ) : ℂ) *
        ((u : ℂ) ^ (s / 2) / (u : ℂ)) ∂volume

noncomputable def chapter04RationalThetaMellinTail (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    ∫ u in Set.Ioi (1 : ℝ),
      ((chapter04RationalTheta u - 1 : ℝ) : ℂ) *
        ((u : ℂ) ^ (s / 2) / (u : ℂ)) ∂volume

/- Splitting the raw integral at one and applying theta inversion defines the
   entire continuation. -/
noncomputable def chapter04RationalThetaMellin (s : ℂ) : ℂ :=
  chapter04RationalThetaMellinTail s +
    chapter04RationalThetaMellinTail (1 - s) +
      chapter04ZeroVectorCorrection s

theorem chapter04_rational_theta_mellin_continuation_eq_integral
    {s : ℂ} (hs : 1 < s.re) :
    chapter04RationalThetaMellin s = chapter04RationalThetaMellinIntegral s := by
  sorry

theorem chapter04_rational_theta_mellin_integral_eq_completed_riemann_zeta
    {s : ℂ} (hs : 1 < s.re) :
    chapter04RationalThetaMellinIntegral s =
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s := by
  sorry

theorem chapter04_rational_theta_mellin_eq_completed_riemann_zeta
    {s : ℂ} (hs : 1 < s.re) :
    chapter04RationalThetaMellin s =
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s := by
  rw [chapter04_rational_theta_mellin_continuation_eq_integral hs,
    chapter04_rational_theta_mellin_integral_eq_completed_riemann_zeta hs]

theorem chapter04_rational_theta_mellin_functional_equation
    (s : ℂ) :
    chapter04RationalThetaMellin s = chapter04RationalThetaMellin (1 - s) := by
  simp [chapter04RationalThetaMellin, chapter04ZeroVectorCorrection]
  rw [show s - 1 = -(1 - s) by ring, inv_neg]
  ring

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
