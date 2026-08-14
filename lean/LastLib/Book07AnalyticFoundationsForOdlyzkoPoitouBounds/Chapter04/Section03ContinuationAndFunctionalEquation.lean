import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Section02ThetaKernelsAndDualLattices
import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03.Section01IdealsAndAbsoluteConvergence
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.Meromorphic.Complex

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03
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
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hsm2 : -1 < (s - 2).re := by
    norm_num [Complex.sub_re]
    linarith
  have hsm1 : -1 < (s - 1).re := by
    norm_num [Complex.sub_re]
    linarith
  unfold chapter04ZeroVectorCorrection chapter04MellinKernel
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hcongr :
      (∫ t : ℝ in 0..1,
        ((t⁻¹ - 1 : ℝ) : ℂ) *
          (if 0 < t then (t : ℂ) ^ s / (t : ℂ) else 0)) =
      ∫ t : ℝ in 0..1, ((t : ℂ) ^ (s - 2) - (t : ℂ) ^ (s - 1)) := by
    apply intervalIntegral.integral_congr_ae
    refine (volume.ae_ne (0 : ℝ)).mono ?_
    intro t ht0 ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [if_pos ht.1, Complex.ofReal_sub, Complex.ofReal_inv]
    have hpow1 : (t : ℂ) ^ s / (t : ℂ) = (t : ℂ) ^ (s - 1) := by
      calc
        (t : ℂ) ^ s / (t : ℂ) = (t : ℂ) ^ s / (t : ℂ) ^ (1 : ℂ) := by
          rw [Complex.cpow_one]
        _ = (t : ℂ) ^ (s - 1) := by
          exact (Complex.cpow_sub s 1
            (Complex.ofReal_ne_zero.mpr ht.1.ne')).symm
    have hpow2 : (t : ℂ) ^ (s - 2) =
        (t : ℂ) ^ (s - 1) / (t : ℂ) := by
      calc
        (t : ℂ) ^ (s - 2) = (t : ℂ) ^ ((s - 1) - 1) := by
          apply congrArg (fun z : ℂ => (t : ℂ) ^ z)
          ring
        _ = (t : ℂ) ^ (s - 1) / (t : ℂ) ^ (1 : ℂ) :=
          Complex.cpow_sub (s - 1) 1
            (Complex.ofReal_ne_zero.mpr ht.1.ne')
        _ = (t : ℂ) ^ (s - 1) / (t : ℂ) := by rw [Complex.cpow_one]
    rw [hpow1, hpow2]
    field_simp
    ac_rfl
  rw [hcongr,
    intervalIntegral.integral_sub
      (intervalIntegral.intervalIntegrable_cpow' hsm2)
      (intervalIntegral.intervalIntegrable_cpow' hsm1),
    integral_cpow (Or.inl hsm2), integral_cpow (Or.inl hsm1)]
  have hsm1ne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have he1 : s - 2 + 1 = s - 1 := by ring
  have he2 : s - 1 + 1 = s := sub_add_cancel s 1
  rw [he1, he2]
  simp [Complex.zero_cpow hsm1ne, Complex.zero_cpow hs0]

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
  let f₁ : ℂ → ℂ :=
    chapter04ThetaMellinTail K D (a : Chapter04FractionalIdeal K)
  let f₂ : ℂ → ℂ := fun s ↦
    chapter04ThetaMellinTail K D
      (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K)) (1 - s)
  let f₃ : ℂ → ℂ := fun s ↦ (1 : ℂ) / (s - 1) - 1 / s
  have hf₁ (s : ℂ) : AnalyticAt ℂ f₁ s := by
    exact chapter04_theta_mellin_tail_entire K D (Units.ne_zero a) s
      (Set.mem_univ _)
  have hf₂ (s : ℂ) : AnalyticAt ℂ f₂ s := by
    simpa [f₂, Function.comp_def] using (chapter04_theta_mellin_tail_entire K D
      (chapter04_dual_fractional_ideal_ne_zero K (Units.ne_zero a)) (1 - s)
      (Set.mem_univ _)).comp (by fun_prop)
  have hf₃ (s : ℂ) : MeromorphicAt f₃ s := by
    fun_prop
  have hfscale (s : ℂ) : AnalyticAt ℂ (fun _ : ℂ =>
      (chapter04MellinConstant K D : ℂ)⁻¹) s := by
    fun_prop
  have hfscale_ne (s : ℂ) :
      (fun _ : ℂ => (chapter04MellinConstant K D : ℂ)⁻¹) s ≠ 0 := by
    simp [chapter04_mellin_constant_ne_zero K D]
  have hcorr_zero : meromorphicOrderAt f₃ 0 = (-1 : ℤ) := by
    have h₁ : meromorphicOrderAt (fun s : ℂ => (1 : ℂ) / (s - 1)) 0 = 0 := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun s : ℂ => s - 1)) 0 = 0
      rw [meromorphicOrderAt_div
        (by fun_prop : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) 0)
        (by fun_prop : MeromorphicAt (fun s : ℂ => s - 1) 0)]
      have hsub : meromorphicOrderAt (fun s : ℂ => s - 1) 0 = 0 := by
        have hsuban : AnalyticAt ℂ (fun s : ℂ => s - 1) 0 := by fun_prop
        rw [hsuban.meromorphicOrderAt_eq]
        simp [hsuban.analyticOrderAt_eq_zero.2 (by norm_num)]
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hsub]
      norm_num
    have h₂ : meromorphicOrderAt (fun s : ℂ => (1 : ℂ) / s) 0 = (-1 : ℤ) := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun s : ℂ => s)) 0 = (-1 : ℤ)
      rw [meromorphicOrderAt_div
        (by fun_prop : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) 0)
        (by fun_prop : MeromorphicAt (fun s : ℂ => s) 0)]
      have hid : meromorphicOrderAt (fun s : ℂ => s) 0 = 1 := by
        change meromorphicOrderAt id 0 = 1
        exact meromorphicOrderAt_id
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hid]
      norm_num
    have h₂neg : meromorphicOrderAt (fun s : ℂ => -(1 / s)) 0 = (-1 : ℤ) := by
      have hneg :=
        (meromorphicOrderAt_neg (f := fun s : ℂ => 1 / s) (x := 0)).symm.trans h₂
      change meromorphicOrderAt (fun s : ℂ => -(1 / s)) 0 = (-1 : ℤ) at hneg
      exact hneg
    change meromorphicOrderAt
      ((fun s : ℂ => (1 : ℂ) / (s - 1)) +
        (fun s : ℂ => -(1 / s))) 0 = (-1 : ℤ)
    rw [meromorphicOrderAt_add_of_ne (by fun_prop) (by fun_prop)]
    · rw [h₁, h₂neg]
      apply min_eq_right
      exact WithTop.coe_le_coe.mpr (by norm_num)
    · rw [h₁, h₂neg]
      norm_num
  have hcorr_one : meromorphicOrderAt f₃ 1 = (-1 : ℤ) := by
    have h₁ : meromorphicOrderAt (fun s : ℂ => (1 : ℂ) / (s - 1)) 1 = (-1 : ℤ) := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun s : ℂ => s - 1)) 1 = (-1 : ℤ)
      rw [meromorphicOrderAt_div
        (by fun_prop : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) 1)
        (by fun_prop : MeromorphicAt (fun s : ℂ => s - 1) 1)]
      have hsub : meromorphicOrderAt (fun s : ℂ => s - 1) 1 = 1 := by
        have hsuban : AnalyticAt ℂ (fun s : ℂ => s - 1) 1 := by fun_prop
        rw [hsuban.meromorphicOrderAt_eq]
        simp
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hsub]
      norm_num
    have h₂ : meromorphicOrderAt (fun s : ℂ => (1 : ℂ) / s) 1 = 0 := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun s : ℂ => s)) 1 = 0
      rw [meromorphicOrderAt_div
        (by fun_prop : MeromorphicAt (fun _ : ℂ => (1 : ℂ)) 1)
        (by fun_prop : MeromorphicAt (fun s : ℂ => s) 1)]
      have hid : meromorphicOrderAt (fun s : ℂ => s) 1 = 0 := by
        have hidan : AnalyticAt ℂ (fun s : ℂ => s) 1 := by fun_prop
        rw [hidan.meromorphicOrderAt_eq]
        simp [hidan.analyticOrderAt_eq_zero.2 (by norm_num)]
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hid]
      norm_num
    have h₂neg : meromorphicOrderAt (fun s : ℂ => -(1 / s)) 1 = 0 := by
      have hneg :=
        (meromorphicOrderAt_neg (f := fun s : ℂ => 1 / s) (x := 1)).symm.trans h₂
      change meromorphicOrderAt (fun s : ℂ => -(1 / s)) 1 = 0 at hneg
      exact hneg
    change meromorphicOrderAt
      ((fun s : ℂ => (1 : ℂ) / (s - 1)) +
        (fun s : ℂ => -(1 / s))) 1 = (-1 : ℤ)
    rw [meromorphicOrderAt_add_of_ne (by fun_prop) (by fun_prop)]
    · rw [h₁, h₂neg]
      apply min_eq_left
      exact WithTop.coe_le_coe.mpr (by norm_num)
    · rw [h₁, h₂neg]
      norm_num
  have htail_order (s : ℂ) :
      0 ≤ meromorphicOrderAt (f₁ + f₂) s := by
    have hsum := meromorphicOrderAt_add (hf₁ s).meromorphicAt (hf₂ s).meromorphicAt
    exact le_trans (by
      exact le_min (hf₁ s).meromorphicOrderAt_nonneg
        (hf₂ s).meromorphicOrderAt_nonneg) hsum
  have htotal_order (s : ℂ) (hcorr_nonneg : 0 ≤ meromorphicOrderAt f₃ s) :
      0 ≤ meromorphicOrderAt (f₁ + f₂ + f₃) s := by
    have hsum' : MeromorphicAt (f₁ + f₂) s :=
      (hf₁ s).meromorphicAt.add (hf₂ s).meromorphicAt
    have htotal := meromorphicOrderAt_add hsum' (hf₃ s)
    exact le_trans (le_min (htail_order s) hcorr_nonneg) htotal
  have horder (s : ℂ) :
      meromorphicOrderAt (chapter04CompletedPartialZetaForIdeal K D a) s =
        meromorphicOrderAt (f₁ + f₂ + f₃) s := by
    unfold chapter04CompletedPartialZetaForIdeal
    apply meromorphicOrderAt_mul_of_ne_zero (hfscale s) (hfscale_ne s)
  constructor
  · rw [horder, meromorphicOrderAt_add_eq_right_of_lt
      ((hf₁ 0).meromorphicAt.add (hf₂ 0).meromorphicAt)]
    · exact hcorr_zero
    · rw [hcorr_zero]
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (htail_order 0)
  constructor
  · rw [horder, meromorphicOrderAt_add_eq_right_of_lt
      ((hf₁ 1).meromorphicAt.add (hf₂ 1).meromorphicAt)]
    · exact hcorr_one
    · rw [hcorr_one]
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num)) (htail_order 1)
  · intro s hs0 hs1
    rw [horder]
    have hcorr_nonneg : 0 ≤ meromorphicOrderAt f₃ s := by
      have hden₁ : AnalyticAt ℂ (fun z : ℂ => z - 1) s := by fun_prop
      have hden₀ : AnalyticAt ℂ (fun z : ℂ => z) s := by fun_prop
      have h₃an : AnalyticAt ℂ f₃ s := by
        exact (analyticAt_const.div hden₁ (sub_ne_zero.mpr hs1)).sub
          (analyticAt_const.div hden₀ hs0)
      exact h₃an.meromorphicOrderAt_nonneg
    exact htotal_order s hcorr_nonneg

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
  have htail_a (z : ℂ) :
      AnalyticAt ℂ
        (chapter04ThetaMellinTail K D (a : Chapter04FractionalIdeal K)) z :=
    chapter04_theta_mellin_tail_entire K D (Units.ne_zero a) z
      (Set.mem_univ _)
  have htail_b (z : ℂ) :
      AnalyticAt ℂ
        (chapter04ThetaMellinTail K D (b : Chapter04FractionalIdeal K)) z :=
    chapter04_theta_mellin_tail_entire K D (Units.ne_zero b) z
      (Set.mem_univ _)
  have htail_da (z : ℂ) :
      AnalyticAt ℂ
        (fun w : ℂ =>
          chapter04ThetaMellinTail K D
            (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K))
            (1 - w)) z := by
    simpa [Function.comp_def] using
      (chapter04_theta_mellin_tail_entire K D
        (chapter04_dual_fractional_ideal_ne_zero K (Units.ne_zero a))
        (1 - z) (Set.mem_univ _)).comp (by fun_prop)
  have htail_db (z : ℂ) :
      AnalyticAt ℂ
        (fun w : ℂ =>
          chapter04ThetaMellinTail K D
            (chapter04DualFractionalIdeal K (b : Chapter04FractionalIdeal K))
            (1 - w)) z := by
    simpa [Function.comp_def] using
      (chapter04_theta_mellin_tail_entire K D
        (chapter04_dual_fractional_ideal_ne_zero K (Units.ne_zero b))
        (1 - z) (Set.mem_univ _)).comp (by fun_prop)
  have hdiff : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        chapter04CompletedPartialZetaForIdeal K D a z -
          chapter04CompletedPartialZetaForIdeal K D b z) Set.univ := by
    intro z hz
    have hsum_a := (htail_a z).add (htail_da z)
    have hsum_b := (htail_b z).add (htail_db z)
    have hfun :
        (fun w : ℂ =>
          chapter04CompletedPartialZetaForIdeal K D a w -
            chapter04CompletedPartialZetaForIdeal K D b w) =
        (fun w : ℂ =>
          (chapter04MellinConstant K D : ℂ)⁻¹ *
            ((chapter04ThetaMellinTail K D (a : Chapter04FractionalIdeal K) w +
                chapter04ThetaMellinTail K D
                  (chapter04DualFractionalIdeal K (a : Chapter04FractionalIdeal K))
                  (1 - w)) -
              (chapter04ThetaMellinTail K D (b : Chapter04FractionalIdeal K) w +
                chapter04ThetaMellinTail K D
                  (chapter04DualFractionalIdeal K (b : Chapter04FractionalIdeal K))
                  (1 - w)))) := by
      funext w
      unfold chapter04CompletedPartialZetaForIdeal chapter04ZeroVectorCorrection
      ring
    rw [hfun]
    convert ((hsum_a.sub hsum_b).const_smul
        (c := (chapter04MellinConstant K D : ℂ)⁻¹)) using 1
    ext w
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  have hclass :
      chapter04InverseIdealClass K a = chapter04InverseIdealClass K b := by
    simp [chapter04InverseIdealClass, ha, hb]
  have hfg :
      Filter.EventuallyEq (nhds (2 : ℂ))
        (fun z : ℂ =>
          chapter04CompletedPartialZetaForIdeal K D a z -
            chapter04CompletedPartialZetaForIdeal K D b z)
        (fun _ : ℂ => 0) := by
    have hnh : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hnh] with z hz
    have hea := chapter04_completed_partial_zeta_for_ideal_eq_euler_half_plane
      K D a hz
    have heb := chapter04_completed_partial_zeta_for_ideal_eq_euler_half_plane
      K D b hz
    have heq :
        chapter04CompletedPartialZetaForIdeal K D a z =
          chapter04CompletedPartialZetaForIdeal K D b z := by
      rw [hea, heb, hclass]
    rw [heq]
    simp
  have hglobal := hdiff.eq_of_eventuallyEq analyticOnNhd_const hfg
  have hzero := congrFun hglobal s
  exact sub_eq_zero.mp hzero

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

/-- The uncompleted Dedekind zeta continuation obtained from the completed
    function.  Chapter 3's `chapter03DedekindZeta` is the Euler-half-plane
    Dirichlet series, so it cannot serve as the global meromorphic function
    appearing in the functional equation. -/
noncomputable def chapter04DedekindZetaContinuation
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  chapter04CompletedDedekindZeta K s /
    ((chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
      chapter04ArchimedeanFactor K s)

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
  classical
  have hs' : s ∈ chapter03EulerHalfPlane := hs
  have hnorm : Summable (fun I : Chapter03IntegralIdeal K =>
      ‖chapter03IdealTerm s I‖) :=
    chapter03_ideal_series_absolutely_summable K hs'
  have hfiber (C : ClassGroup (𝓞 K)) :
      Summable (fun I : Chapter03IntegralIdeal K =>
        if ClassGroup.mk0 I = C then chapter03IdealTerm s I else 0) := by
    apply Summable.of_norm_bounded hnorm
    intro I
    split_ifs <;> simp [norm_nonneg]
  have hpartition :
      (∑ C : ClassGroup (𝓞 K), chapter04PartialZeta K C s) =
        chapter03IdealSeries K s := by
    unfold chapter04PartialZeta chapter03IdealSeries
    calc
      (∑ C : ClassGroup (𝓞 K),
          ∑' I : Chapter03IntegralIdeal K,
            if ClassGroup.mk0 I = C then chapter03IdealTerm s I else 0) =
          ∑' I : Chapter03IntegralIdeal K,
            ∑ C : ClassGroup (𝓞 K),
              if ClassGroup.mk0 I = C then chapter03IdealTerm s I else 0 := by
            symm
            rw [Summable.tsum_finsetSum (fun C hC => hfiber C)]
      _ = ∑' I : Chapter03IntegralIdeal K, chapter03IdealTerm s I := by
        apply tsum_congr
        intro I
        simp
  unfold chapter04CompletedDedekindZeta chapter04SumCompletedPartialZeta
  rw [tsum_fintype]
  simp_rw [chapter04_completed_partial_zeta_continuation_eq_partial_factor K
    (chapter04ChosenUnitFundamentalDomain K) _ hs]
  rw [← Finset.mul_sum, hpartition]
  unfold chapter04EulerCompletedDedekindZeta
  rw [← chapter03_ideal_series_eq_dedekind_zeta K hs']

theorem chapter04_dedekind_zeta_continuation_agrees_on_euler_half_plane
    (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    chapter04DedekindZetaContinuation K s = chapter03DedekindZeta K s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hsre : 0 < s.re := lt_trans zero_lt_one hs
  have hs2re : 0 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  have hdisc : (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (chapter04_absolute_discriminant_pos K)))
  have hreal : chapter04GammaReal s ≠ 0 := by
    unfold chapter04GammaReal
    exact mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
      (Complex.Gamma_ne_zero_of_re_pos hs2re)
  have hcomplex : chapter04GammaComplex s ≠ 0 := by
    unfold chapter04GammaComplex
    exact mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))))
      (Complex.Gamma_ne_zero_of_re_pos hsre)
  have harch : chapter04ArchimedeanFactor K s ≠ 0 := by
    unfold chapter04ArchimedeanFactor
    exact mul_ne_zero (pow_ne_zero _ hreal) (pow_ne_zero _ hcomplex)
  have hden : (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
      chapter04ArchimedeanFactor K s ≠ 0 :=
    mul_ne_zero hdisc harch
  unfold chapter04DedekindZetaContinuation
  rw [chapter04_completed_dedekind_zeta_agrees_on_euler_half_plane K hs]
  unfold chapter04EulerCompletedDedekindZeta
  apply (div_eq_iff hden).2
  ring

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

/- The Euler expression is a meromorphic factorization of the global
   continuation.  The punctured-neighborhood formulation avoids identifying
   the assigned values at poles with values of a meromorphic germ. -/
theorem chapter04_completed_dedekind_zeta_global_factorization
    (K : Type*) [Field K] [NumberField K] :
    Meromorphic (chapter04CompletedDedekindZeta K) ∧
      Meromorphic (chapter04DedekindZetaContinuation K) ∧
        Meromorphic (chapter04ArchimedeanFactor K) ∧
          ∀ s : ℂ,
            Filter.EventuallyEq (nhdsWithin s ({s} : Set ℂ)ᶜ)
              (chapter04CompletedDedekindZeta K)
              (fun z : ℂ =>
                (chapter04AbsoluteDiscriminant K : ℂ) ^ (z / 2) *
                  chapter04ArchimedeanFactor K z *
                    chapter04DedekindZetaContinuation K z) := by
  have harch : Meromorphic (chapter04ArchimedeanFactor K) := by
    intro s
    unfold chapter04ArchimedeanFactor
    apply MeromorphicAt.mul
    · apply MeromorphicAt.pow
      unfold chapter04GammaReal
      apply MeromorphicAt.mul
      · exact (((differentiable_id.neg.div_const (2 : ℂ)).const_cpow
          (c := (Real.pi : ℂ))
          (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).analyticAt s).meromorphicAt
      · simpa [Function.comp_def] using
          (MeromorphicAt.comp_analyticAt (x := s)
            (f := Complex.Gamma) (g := fun z : ℂ => z / 2)
            (Meromorphic.Gamma (s / 2))
            ((differentiable_id.div_const (2 : ℂ)).analyticAt s))
    · apply MeromorphicAt.pow
      unfold chapter04GammaComplex
      apply MeromorphicAt.mul
      · exact (((differentiable_id.neg.const_cpow
          (c := (2 : ℂ) * (Real.pi : ℂ))
          (Or.inl (mul_ne_zero (by norm_num)
            (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))).analyticAt s).meromorphicAt)
      · exact Meromorphic.Gamma s
  have hdisc : Meromorphic (fun s : ℂ =>
      (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2)) := by
    intro s
    exact (((differentiable_id.div_const (2 : ℂ)).const_cpow
      (c := (chapter04AbsoluteDiscriminant K : ℂ))
      (Or.inl (Complex.ofReal_ne_zero.mpr
        (ne_of_gt (chapter04_absolute_discriminant_pos K))))).analyticAt s).meromorphicAt
  let q : ℂ → ℂ := fun s =>
    (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2) *
      chapter04ArchimedeanFactor K s
  have hq : Meromorphic q := by
    intro s
    dsimp [q]
    exact (hdisc s).mul (harch s)
  have hq2 : q (2 : ℂ) ≠ 0 := by
    dsimp [q]
    unfold chapter04ArchimedeanFactor chapter04GammaReal chapter04GammaComplex
    norm_num [Complex.cpow_eq_zero_iff]
    exact (chapter04_absolute_discriminant_pos K).ne'
  have hrealDiff : DifferentiableAt ℂ chapter04GammaReal (2 : ℂ) := by
    unfold chapter04GammaReal
    apply DifferentiableAt.mul
    · exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    · have hcomp : DifferentiableAt ℂ
          (fun z : ℂ => Complex.Gamma (z / 2)) (2 : ℂ) := by
        apply DifferentiableAt.fun_comp'
        · exact Complex.differentiableAt_Gamma (2 / 2 : ℂ) (by
            intro m hm
            have hm' := congrArg Complex.re hm
            norm_num at hm'
            have hmnonneg : 0 ≤ (m : ℝ) := by positivity
            linarith)
        · exact (differentiable_id.div_const (2 : ℂ)) (2 : ℂ)
      exact hcomp
  have hcomplexDiff : DifferentiableAt ℂ chapter04GammaComplex (2 : ℂ) := by
    unfold chapter04GammaComplex
    apply DifferentiableAt.mul
    · exact (differentiableAt_id.neg).const_cpow
        (Or.inl (mul_ne_zero (by norm_num)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
    · exact Complex.differentiableAt_Gamma 2 (by
        intro m hm
        have hm' := congrArg Complex.re hm
        norm_num at hm'
        have hmnonneg : 0 ≤ (m : ℝ) := by positivity
        linarith)
  have harchDiff : DifferentiableAt ℂ (chapter04ArchimedeanFactor K) (2 : ℂ) := by
    unfold chapter04ArchimedeanFactor
    exact (hrealDiff.pow _).mul (hcomplexDiff.pow _)
  have hdiscDiff : DifferentiableAt ℂ (fun s : ℂ =>
      (chapter04AbsoluteDiscriminant K : ℂ) ^ (s / 2)) (2 : ℂ) := by
    exact (differentiableAt_id.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr
        (ne_of_gt (chapter04_absolute_discriminant_pos K))))
  have hqcont : ContinuousAt q (2 : ℂ) := by
    dsimp [q]
    exact hdiscDiff.continuousAt.mul harchDiff.continuousAt
  have hq2order : meromorphicOrderAt q (2 : ℂ) ≠ ⊤ := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hq (2 : ℂ))).2
    exact (hqcont.eventually_ne hq2).filter_mono nhdsWithin_le_nhds
  have hqorder (s : ℂ) : meromorphicOrderAt q s ≠ ⊤ := by
    apply MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (meromorphicOn_univ.mpr hq) isPreconnected_univ
        (Set.mem_univ _) (Set.mem_univ _)
      hq2order
  have hqevent (s : ℂ) : ∀ᶠ z : ℂ in nhdsWithin s ({s} : Set ℂ)ᶜ, q z ≠ 0 := by
    exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hq s)).1 (hqorder s)
  have hcompleted : Meromorphic (chapter04CompletedDedekindZeta K) :=
    chapter04_completed_dedekind_zeta_meromorphic K
  have hcontinuation : Meromorphic (chapter04DedekindZetaContinuation K) := by
    intro s
    unfold chapter04DedekindZetaContinuation
    exact (hcompleted s).div (hq s)
  refine ⟨hcompleted, hcontinuation, harch, ?_⟩
  intro s
  filter_upwards [hqevent s] with z hz
  unfold q at hz
  unfold chapter04DedekindZetaContinuation
  have hdisc_z : (chapter04AbsoluteDiscriminant K : ℂ) ^ (z / 2) ≠ 0 :=
    (mul_ne_zero_iff.mp hz).1
  have harch_z : chapter04ArchimedeanFactor K z ≠ 0 :=
    (mul_ne_zero_iff.mp hz).2
  field_simp [hdisc_z, harch_z]

theorem chapter04_dedekind_zeta_zero_of_archimedean_pole
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs0 : s ≠ 0)
    (hspole : meromorphicOrderAt (chapter04ArchimedeanFactor K) s < 0) :
    chapter04DedekindZetaContinuation K s = 0 := by
  have harch_zero : chapter04ArchimedeanFactor K s = 0 := by
    by_contra harch_ne
    have hreal_an : AnalyticAt ℂ
        (fun z : ℂ => chapter04GammaReal z ^ chapter04RealPlaces K) s := by
      by_cases hr : chapter04RealPlaces K = 0
      · simpa [hr] using
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) s)
      · have hreal_ne : chapter04GammaReal s ≠ 0 := by
          intro hz
          apply harch_ne
          simp [chapter04ArchimedeanFactor, hz, hr]
        have hgamma_ne : Complex.Gamma (s / 2) ≠ 0 := by
          intro hz
          apply hreal_ne
          unfold chapter04GammaReal
          rw [hz, mul_zero]
        have hgamma_cond : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
          intro m hm
          by_cases hm0 : m = 0
          · subst m
            have hsdiv : s / 2 ≠ 0 := by
              intro h
              apply hs0
              field_simp at h
              simpa using h
            apply hsdiv
            simpa using hm
          · apply hgamma_ne
            rw [hm, Complex.Gamma_neg_nat_eq_zero]
        have hgamma_mer : MeromorphicAt
            (fun z : ℂ => Complex.Gamma (z / 2)) s := by
          simpa [Function.comp_def] using
            (MeromorphicAt.comp_analyticAt (x := s)
              (f := Complex.Gamma) (g := fun z : ℂ => z / 2)
              (Meromorphic.Gamma (s / 2))
              ((differentiable_id.div_const (2 : ℂ)).analyticAt s))
        have hgamma_diff : DifferentiableAt ℂ
            (fun z : ℂ => Complex.Gamma (z / 2)) s := by
          apply DifferentiableAt.fun_comp'
          · exact Complex.differentiableAt_Gamma (s / 2) hgamma_cond
          · exact (differentiable_id.div_const (2 : ℂ)) s
        have hpow_an : AnalyticAt ℂ
            (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
          (((differentiable_id.neg.div_const (2 : ℂ)).const_cpow
            (c := (Real.pi : ℂ))
            (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).analyticAt s)
        have hreal_mer : MeromorphicAt chapter04GammaReal s := by
          unfold chapter04GammaReal
          apply MeromorphicAt.mul
          · exact hpow_an.meromorphicAt
          · exact hgamma_mer
        have hreal_diff : DifferentiableAt ℂ chapter04GammaReal s := by
          unfold chapter04GammaReal
          apply DifferentiableAt.mul
          · exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
              (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          · exact hgamma_diff
        exact (hreal_mer.pow _).analyticAt (hreal_diff.pow _).continuousAt
    have hcomplex_an : AnalyticAt ℂ
        (fun z : ℂ => chapter04GammaComplex z ^ chapter04ComplexPlaces K) s := by
      by_cases hc : chapter04ComplexPlaces K = 0
      · simpa [hc] using
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) s)
      · have hcomplex_ne : chapter04GammaComplex s ≠ 0 := by
          intro hz
          apply harch_ne
          simp [chapter04ArchimedeanFactor, hz, hc]
        have hgamma_ne : Complex.Gamma s ≠ 0 := by
          intro hz
          apply hcomplex_ne
          unfold chapter04GammaComplex
          rw [hz, mul_zero]
        have hgamma_cond : ∀ m : ℕ, s ≠ -(m : ℂ) := by
          intro m hm
          apply hgamma_ne
          rw [hm, Complex.Gamma_neg_nat_eq_zero]
        have hgamma_mer : MeromorphicAt Complex.Gamma s := Meromorphic.Gamma s
        have hgamma_diff : DifferentiableAt ℂ Complex.Gamma s :=
          Complex.differentiableAt_Gamma s hgamma_cond
        have hpow_an : AnalyticAt ℂ
            (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ)) ^ (-z)) s :=
          (((differentiable_id.neg).const_cpow
            (c := (2 : ℂ) * (Real.pi : ℂ))
            (Or.inl (mul_ne_zero (by norm_num)
              (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))).analyticAt s)
        have hcomplex_mer : MeromorphicAt chapter04GammaComplex s := by
          unfold chapter04GammaComplex
          apply MeromorphicAt.mul
          · exact hpow_an.meromorphicAt
          · exact hgamma_mer
        have hcomplex_diff : DifferentiableAt ℂ chapter04GammaComplex s := by
          unfold chapter04GammaComplex
          apply DifferentiableAt.mul
          · exact ((differentiable_id.neg).const_cpow
              (c := (2 : ℂ) * (Real.pi : ℂ))
              (Or.inl (mul_ne_zero (by norm_num)
                (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))) s
          · exact hgamma_diff
        exact (hcomplex_mer.pow _).analyticAt (hcomplex_diff.pow _).continuousAt
    have harch_mer : MeromorphicAt (chapter04ArchimedeanFactor K) s := by
      unfold chapter04ArchimedeanFactor
      apply MeromorphicAt.mul
      · exact hreal_an.meromorphicAt
      · exact hcomplex_an.meromorphicAt
    have harch_cont : ContinuousAt (chapter04ArchimedeanFactor K) s := by
      unfold chapter04ArchimedeanFactor
      exact hreal_an.continuousAt.mul hcomplex_an.continuousAt
    have harch_an : AnalyticAt ℂ (chapter04ArchimedeanFactor K) s := by
      exact harch_mer.analyticAt harch_cont
    have horder : meromorphicOrderAt (chapter04ArchimedeanFactor K) s = 0 := by
      rw [harch_an.meromorphicOrderAt_eq,
        harch_an.analyticOrderAt_eq_zero.2 harch_ne]
      simp
    rw [horder] at hspole
    norm_num at hspole
  unfold chapter04DedekindZetaContinuation
  rw [harch_zero, mul_zero, div_zero]

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
  classical
  let D := chapter04ChosenUnitFundamentalDomain K
  let scale : ℂ := (chapter04MellinConstant K D : ℂ)⁻¹
  let q : ℂ → ℂ := chapter04ZeroVectorCorrection
  let p : ClassGroup (𝓞 K) → ℂ → ℂ := fun C z =>
    chapter04ThetaMellinTail K D
        (chapter04FractionalIdealRepresentative K C⁻¹) z +
      chapter04ThetaMellinTail K D
        (chapter04DualFractionalIdeal K
          (chapter04FractionalIdealRepresentative K C⁻¹ :
            Chapter04FractionalIdeal K)) (1 - z)
  let f : ClassGroup (𝓞 K) → ℂ → ℂ := fun C z =>
    chapter04CompletedPartialZetaContinuation K D C z
  have hscale : scale ≠ 0 := by
    simp [scale, chapter04_mellin_constant_ne_zero K D]
  have hdecomp (C : ClassGroup (𝓞 K)) :
      f C = fun z => scale * (p C z + q z) := by
    funext z
    simp [f, p, q, scale, D, chapter04CompletedPartialZetaContinuation,
      chapter04CompletedPartialZetaForIdeal]
  have hp (C : ClassGroup (𝓞 K)) (z : ℂ) :
      AnalyticAt ℂ (p C) z := by
    apply (chapter04_theta_mellin_tail_entire K D
      (Units.ne_zero (chapter04FractionalIdealRepresentative K C⁻¹)) z
      (Set.mem_univ _)).add
    simpa [p, Function.comp_def] using
      ((chapter04_theta_mellin_tail_entire K D
        (chapter04_dual_fractional_ideal_ne_zero K
          (Units.ne_zero (chapter04FractionalIdealRepresentative K C⁻¹)))
        (1 - z) (Set.mem_univ _)).comp (by fun_prop))
  have hfirst (z : ℂ) :
      AnalyticAt ℂ (fun w : ℂ =>
        ∑ C : ClassGroup (𝓞 K), scale * p C w) z := by
    have hsum : AnalyticAt ℂ
        (∑ C : ClassGroup (𝓞 K), fun w : ℂ => scale * p C w) z := by
      apply Finset.analyticAt_sum Finset.univ
      intro C hC
      exact analyticAt_const.mul (hp C z)
    have hfun :
        (∑ C : ClassGroup (𝓞 K), fun w : ℂ => scale * p C w) =
          (fun w : ℂ => ∑ C : ClassGroup (𝓞 K), scale * p C w) := by
      funext w
      rw [Finset.sum_apply]
    rw [← hfun]
    exact hsum
  have hq_zero : meromorphicOrderAt q 0 = (-1 : ℤ) := by
    unfold q chapter04ZeroVectorCorrection
    change meromorphicOrderAt
      ((fun z : ℂ => (1 : ℂ) / (z - 1)) +
        (fun z : ℂ => -(1 / z))) 0 = (-1 : ℤ)
    have h₁ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / (z - 1)) 0 = 0 := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z - 1)) 0 = 0
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z - 1) 0)]
      have hsub : meromorphicOrderAt (fun z : ℂ => z - 1) 0 = 0 := by
        have hsuban : AnalyticAt ℂ (fun z : ℂ => z - 1) 0 := by fun_prop
        rw [hsuban.meromorphicOrderAt_eq]
        simp [hsuban.analyticOrderAt_eq_zero.2 (by norm_num)]
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hsub]
      norm_num
    have h₂ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / z) 0 = (-1 : ℤ) := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z)) 0 = (-1 : ℤ)
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z) 0)]
      have hid : meromorphicOrderAt (fun z : ℂ => z) 0 = 1 := by
        change meromorphicOrderAt id 0 = 1
        exact meromorphicOrderAt_id
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hid]
      norm_num
    have h₂neg : meromorphicOrderAt (fun z : ℂ => -(1 / z)) 0 = (-1 : ℤ) := by
      have hneg :=
        (meromorphicOrderAt_neg (f := fun z : ℂ => 1 / z) (x := 0)).symm.trans h₂
      change meromorphicOrderAt (fun z : ℂ => -(1 / z)) 0 = (-1 : ℤ) at hneg
      exact hneg
    rw [meromorphicOrderAt_add_of_ne (by fun_prop) (by fun_prop)]
    · rw [h₁, h₂neg]
      apply min_eq_right
      exact WithTop.coe_le_coe.mpr (by norm_num)
    · rw [h₁, h₂neg]
      norm_num
  have hq_one : meromorphicOrderAt q 1 = (-1 : ℤ) := by
    unfold q chapter04ZeroVectorCorrection
    change meromorphicOrderAt
      ((fun z : ℂ => (1 : ℂ) / (z - 1)) +
        (fun z : ℂ => -(1 / z))) 1 = (-1 : ℤ)
    have h₁ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / (z - 1)) 1 = (-1 : ℤ) := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z - 1)) 1 = (-1 : ℤ)
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z - 1) 1)]
      have hsub : meromorphicOrderAt (fun z : ℂ => z - 1) 1 = 1 := by
        have hsuban : AnalyticAt ℂ (fun z : ℂ => z - 1) 1 := by fun_prop
        rw [hsuban.meromorphicOrderAt_eq]
        simp
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hsub]
      norm_num
    have h₂ : meromorphicOrderAt (fun z : ℂ => (1 : ℂ) / z) 1 = 0 := by
      change meromorphicOrderAt
        ((fun _ : ℂ => (1 : ℂ)) / (fun z : ℂ => z)) 1 = 0
      rw [meromorphicOrderAt_div (by fun_prop)
        (by fun_prop : MeromorphicAt (fun z : ℂ => z) 1)]
      have hid : meromorphicOrderAt (fun z : ℂ => z) 1 = 0 := by
        have hidan : AnalyticAt ℂ (fun z : ℂ => z) 1 := by fun_prop
        rw [hidan.meromorphicOrderAt_eq]
        simp [hidan.analyticOrderAt_eq_zero.2 (by norm_num)]
      rw [meromorphicOrderAt_const, if_neg (by norm_num), hid]
      norm_num
    have h₂neg : meromorphicOrderAt (fun z : ℂ => -(1 / z)) 1 = 0 := by
      have hneg :=
        (meromorphicOrderAt_neg (f := fun z : ℂ => 1 / z) (x := 1)).symm.trans h₂
      change meromorphicOrderAt (fun z : ℂ => -(1 / z)) 1 = 0 at hneg
      exact hneg
    rw [meromorphicOrderAt_add_of_ne (by fun_prop) (by fun_prop)]
    · rw [h₁, h₂neg]
      apply min_eq_left
      exact WithTop.coe_le_coe.mpr (by norm_num)
    · rw [h₁, h₂neg]
      norm_num
  let c : ℂ := (Fintype.card (ClassGroup (𝓞 K)) : ℂ) * scale
  have hc : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ClassGroup (𝓞 K)) ≠ 0)
    · exact hscale
  have hsecond (z : ℂ) :
      MeromorphicAt (fun w : ℂ => c * q w) z := by
    change MeromorphicAt
      (fun w : ℂ => c * ((1 : ℂ) / (w - 1) - 1 / w)) z
    fun_prop
  have hsecond_order_zero :
      meromorphicOrderAt (fun w : ℂ => c * q w) 0 = (-1 : ℤ) := by
    change meromorphicOrderAt ((fun _ : ℂ => c) * q) 0 = (-1 : ℤ)
    rw [meromorphicOrderAt_mul_of_ne_zero (by fun_prop) hc, hq_zero]
  have hsecond_order_one :
      meromorphicOrderAt (fun w : ℂ => c * q w) 1 = (-1 : ℤ) := by
    change meromorphicOrderAt ((fun _ : ℂ => c) * q) 1 = (-1 : ℤ)
    rw [meromorphicOrderAt_mul_of_ne_zero (by fun_prop) hc, hq_one]
  have hdecomp_sum (z : ℂ) :
      chapter04CompletedDedekindZeta K z =
        (∑ C : ClassGroup (𝓞 K), scale * p C z) + c * q z := by
    unfold chapter04CompletedDedekindZeta chapter04SumCompletedPartialZeta
    rw [tsum_fintype]
    change (∑ C : ClassGroup (𝓞 K), f C z) = _
    simp_rw [hdecomp]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_mul]
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [c, mul_assoc]
  have hdecomp_fun :
      chapter04CompletedDedekindZeta K =
        (fun z => (∑ C : ClassGroup (𝓞 K), scale * p C z) + c * q z) := by
    funext z
    exact hdecomp_sum z
  constructor
  · rw [hdecomp_fun]
    change meromorphicOrderAt
      ((fun w : ℂ => ∑ C : ClassGroup (𝓞 K), scale * p C w) +
        (fun w : ℂ => c * q w)) 0 = (-1 : ℤ)
    rw [meromorphicOrderAt_add_eq_right_of_lt
      (hfirst 0).meromorphicAt]
    · exact hsecond_order_zero
    · rw [hsecond_order_zero]
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num))
        (hfirst 0).meromorphicOrderAt_nonneg
  constructor
  · rw [hdecomp_fun]
    change meromorphicOrderAt
      ((fun w : ℂ => ∑ C : ClassGroup (𝓞 K), scale * p C w) +
        (fun w : ℂ => c * q w)) 1 = (-1 : ℤ)
    rw [meromorphicOrderAt_add_eq_right_of_lt
      (hfirst 1).meromorphicAt]
    · exact hsecond_order_one
    · rw [hsecond_order_one]
      exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (by norm_num))
        (hfirst 1).meromorphicOrderAt_nonneg
  · intro z hz0 hz1
    rw [hdecomp_fun]
    change meromorphicOrderAt
      ((fun w : ℂ => ∑ C : ClassGroup (𝓞 K), scale * p C w) +
        (fun w : ℂ => c * q w)) z ≥ 0
    have hqz : AnalyticAt ℂ q z := by
      unfold q chapter04ZeroVectorCorrection
      have hden₁ : AnalyticAt ℂ (fun w : ℂ => w - 1) z := by fun_prop
      have hden₀ : AnalyticAt ℂ (fun w : ℂ => w) z := by fun_prop
      exact (analyticAt_const.div hden₁ (sub_ne_zero.mpr hz1)).sub
        (analyticAt_const.div hden₀ hz0)
    have hsecond_an : AnalyticAt ℂ (fun w : ℂ => c * q w) z :=
      analyticAt_const.mul hqz
    have hadd := meromorphicOrderAt_add
      (hfirst z).meromorphicAt hsecond_an.meromorphicAt
    exact le_trans (le_min (hfirst z).meromorphicOrderAt_nonneg
      hsecond_an.meromorphicOrderAt_nonneg) hadd

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
  have htail (r : ℂ) :
      (1 / 2 : ℂ) *
          ∫ u in Set.Ioi (1 : ℝ),
            ((chapter04RationalTheta u - 1 : ℝ) : ℂ) *
              ((u : ℂ) ^ r / (u : ℂ)) ∂volume =
        (1 / 2 : ℂ) *
          mellin
            ((Set.Ioi (1 : ℝ)).indicator
              (fun u : ℝ => ((chapter04RationalTheta u - 1 : ℝ) : ℂ))) r := by
    unfold mellin
    rw [← integral_const_mul]
    have hrestrict :
        (∫ u in Set.Ioi (0 : ℝ),
          (u : ℂ) ^ (r - 1) •
            (Set.Ioi (1 : ℝ)).indicator
              (fun v : ℝ => ((chapter04RationalTheta v - 1 : ℝ) : ℂ)) u) =
          ∫ u in Set.Ioi (1 : ℝ),
            (u : ℂ) ^ (r - 1) •
              ((chapter04RationalTheta u - 1 : ℝ) : ℂ) := by
      calc
        (∫ u in Set.Ioi (0 : ℝ),
            (u : ℂ) ^ (r - 1) •
              (Set.Ioi (1 : ℝ)).indicator
                (fun v : ℝ => ((chapter04RationalTheta v - 1 : ℝ) : ℂ)) u) =
            ∫ u in Set.Ioi (1 : ℝ),
              (u : ℂ) ^ (r - 1) •
                (Set.Ioi (1 : ℝ)).indicator
                  (fun v : ℝ => ((chapter04RationalTheta v - 1 : ℝ) : ℂ)) u := by
              apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
              · exact measurableSet_Ioi
              · intro u hu
                change 1 < u at hu
                exact lt_trans zero_lt_one hu
              · intro u hu
                rcases hu with ⟨hu0, hu1⟩
                simp [Set.indicator_of_notMem hu1]
        _ = ∫ u in Set.Ioi (1 : ℝ),
              (u : ℂ) ^ (r - 1) •
                ((chapter04RationalTheta u - 1 : ℝ) : ℂ) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro u hu
              simp [Set.indicator_of_mem, hu]
    rw [hrestrict, integral_const_mul]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change 1 < u at hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    have hpow :
        (u : ℂ) ^ (r - 1) =
          (u : ℂ) ^ r / (u : ℂ) := by
      rw [Complex.cpow_sub r 1 (Complex.ofReal_ne_zero.mpr hu0.ne'),
        Complex.cpow_one]
    dsimp
    rw [hpow]
    ring
  let G : ℝ → ℂ :=
    (Set.Ioi (1 : ℝ)).indicator
      (fun u : ℝ => ((chapter04RationalTheta u - 1 : ℝ) : ℂ))
  have hcomp' {r : ℂ} :
      mellin (fun t : ℝ => G (t ^ (-1 : ℝ))) (r - 1 / 2) =
        mellin G (1 / 2 - r) := by
    simpa [one_div, div_eq_mul_inv, Function.comp_def] using
      (mellin_comp_rpow G (r - 1 / 2) (-1))
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  have hPsymm : P.symm = P := by
    simp [P, HurwitzZeta.hurwitzEvenFEPair_zero_symm]
  have hPfg : P.f = P.g := by
    funext t
    simp [P, HurwitzZeta.hurwitzEvenFEPair, Function.comp_def,
      HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  have hP0 : P.f₀ = 1 := by simp [P, HurwitzZeta.hurwitzEvenFEPair]
  have hPg0 : P.g₀ = 1 := by simp [P, HurwitzZeta.hurwitzEvenFEPair]
  have htheta (u : ℝ) (hu : 0 < u) :
      chapter04RationalTheta u = HurwitzZeta.cosKernel 0 u := by
    have hsum := HurwitzZeta.hasSum_int_cosKernel 0 hu
    have hsum' :
        HasSum
          (fun n : ℤ => (Real.exp (-Real.pi * (n : ℝ) ^ 2 * u) : ℂ))
          (HurwitzZeta.cosKernel 0 u : ℂ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsum
    have hsumR :
        HasSum (fun n : ℤ => Real.exp (-Real.pi * (n : ℝ) ^ 2 * u))
          (HurwitzZeta.cosKernel 0 u) := by
      exact (Complex.hasSum_ofReal).mp hsum'
    unfold chapter04RationalTheta
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsumR.tsum_eq
  let GP : ℝ → ℂ :=
    (Set.Ioi (1 : ℝ)).indicator (fun u : ℝ => P.g u - P.g₀)
  have hG : G = GP := by
    funext u
    by_cases hu : 1 < u
    · have hu0 : 0 < u := lt_trans zero_lt_one hu
      have hu' : u ∈ Set.Ioi (1 : ℝ) := hu
      simp only [G, GP]
      rw [Set.indicator_of_mem hu', Set.indicator_of_mem hu']
      rw [htheta u hu0]
      simp [P, HurwitzZeta.hurwitzEvenFEPair, Function.comp_def]
    · have hu' : u ∉ Set.Ioi (1 : ℝ) := hu
      simp [G, GP, hu']
  have htailP (r : ℂ) :
      (1 / 2 : ℂ) *
          ∫ u in Set.Ioi (1 : ℝ),
            ((chapter04RationalTheta u - 1 : ℝ) : ℂ) *
              ((u : ℂ) ^ r / (u : ℂ)) ∂volume =
        (1 / 2 : ℂ) * mellin GP r := by
    calc
      _ = (1 / 2 : ℂ) * mellin G r := htail r
      _ = (1 / 2 : ℂ) * mellin GP r := by rw [hG]
  let H : ℝ → ℂ := fun t =>
    (t : ℂ) ^ (-(1 / 2 : ℂ)) • GP (t ^ (-1 : ℝ))
  have hmodif : P.f_modif = GP + H := by
    funext t
    by_cases ht : 0 < t
    · rcases lt_trichotomy 1 t with hlt | heq | hgt
      · have hinv : t⁻¹ < 1 := (inv_lt_one₀ ht).2 hlt
        have htIoi : t ∈ Set.Ioi (1 : ℝ) := hlt
        have htIoo : t ∉ Set.Ioo (0 : ℝ) 1 := by
          intro h
          exact (not_lt_of_ge hlt.le) h.2
        have hinvIoi : t⁻¹ ∉ Set.Ioi (1 : ℝ) := by
          intro h
          exact (not_lt_of_ge hinv.le) h
        simp only [WeakFEPair.f_modif, Pi.add_apply, H, GP]
        rw [Real.rpow_neg_one]
        simp only [Set.indicator_of_mem htIoi, Set.indicator_of_notMem htIoo,
          Set.indicator_of_notMem hinvIoi]
        simp [P, HurwitzZeta.hurwitzEvenFEPair, Function.comp_def,
          HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
      · subst t
        simp [WeakFEPair.f_modif, H, GP, P,
          HurwitzZeta.hurwitzEvenFEPair, Function.comp_def]
      · have hinv : 1 < t⁻¹ := (one_lt_inv₀ ht).2 hgt
        have htIoi : t ∉ Set.Ioi (1 : ℝ) := by
          intro h
          exact (not_lt_of_ge hgt.le) h
        have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht, hgt⟩
        have hinvIoi : t⁻¹ ∈ Set.Ioi (1 : ℝ) := hinv
        simp only [WeakFEPair.f_modif, Pi.add_apply, H, GP]
        rw [Real.rpow_neg_one]
        simp only [Set.indicator_of_notMem htIoi, Set.indicator_of_mem htIoo,
          Set.indicator_of_mem hinvIoi]
        simp [P, HurwitzZeta.hurwitzEvenFEPair, Function.comp_def,
          HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
        have hfe := HurwitzZeta.evenKernel_functional_equation 0 t
        have hpowC :
            (t : ℂ) ^ (-2⁻¹ : ℂ) = (t ^ (-(1 / 2 : ℝ)) : ℝ) := by
          have hexp : (-2⁻¹ : ℂ) = (-(1 / 2 : ℝ) : ℂ) := by norm_num
          rw [hexp]
          simpa [Complex.ofReal_neg] using
            (Complex.ofReal_cpow ht.le (-(1 / 2 : ℝ))).symm
        have hpowR : t ^ (-2⁻¹ : ℝ) = t ^ (-(1 / 2 : ℝ)) := by
          norm_num
        have hfe' :
            HurwitzZeta.cosKernel 0 t =
              t ^ (-(1 / 2 : ℝ)) * HurwitzZeta.cosKernel 0 t⁻¹ := by
          have heq : HurwitzZeta.evenKernel 0 t =
              HurwitzZeta.cosKernel 0 t :=
            congrFun HurwitzZeta.evenKernel_eq_cosKernel_of_zero t
          have hfe0 := hfe
          rw [heq] at hfe0
          simpa [one_div, Real.rpow_neg ht.le] using hfe0
        rw [hpowC, hpowR, hfe', Complex.ofReal_mul]
        ring
    · by_cases hzero : t = 0
      · subst t
        simp [WeakFEPair.f_modif, H, GP, P,
          HurwitzZeta.hurwitzEvenFEPair, Function.comp_def]
      · have hneg : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) hzero
        have htIoi : t ∉ Set.Ioi (1 : ℝ) := by
          intro h
          exact (not_lt_of_ge (le_trans hneg.le (by norm_num))) h
        have htIoo : t ∉ Set.Ioo (0 : ℝ) 1 := by
          intro h
          exact (not_lt_of_ge (le_of_not_gt ht)) h.1
        have hinv : t⁻¹ < 0 := inv_lt_zero'.2 hneg
        have hinvIoi : t⁻¹ ∉ Set.Ioi (1 : ℝ) := by
          intro h
          exact (not_lt_of_ge (le_trans hinv.le (by norm_num))) h
        simp only [WeakFEPair.f_modif, Pi.add_apply, H, GP]
        rw [Real.rpow_neg_one]
        simp only [Set.indicator_of_notMem htIoi, Set.indicator_of_notMem htIoo,
          Set.indicator_of_notMem hinvIoi]
        simp
  have hPconv (r : ℂ) : MellinConvergent P.f_modif r := by
    let Q := P.isStrongFEPair_toStrongFEPair
    obtain ⟨a, ha⟩ := exists_gt r.re
    obtain ⟨b, hb⟩ := exists_lt r.re
    apply mellinConvergent_of_isBigO_rpow P.hf_modif_int
    · simpa [Q, WeakFEPair.toStrongFEPair] using Q.hf_top (-a)
    · exact ha
    · simpa [Q, WeakFEPair.toStrongFEPair] using Q.hf_zero (-b)
    · exact hb
  have hGPint (r : ℂ) :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (r - 1) • GP t) (Set.Ioi (0 : ℝ)) := by
    have hI :
        IntegrableOn
          ((Set.Ioi (1 : ℝ)).indicator
            (fun t : ℝ => (t : ℂ) ^ (r - 1) • P.f_modif t))
          (Set.Ioi (0 : ℝ)) :=
      (hPconv r).indicator (measurableSet_Ioi : MeasurableSet (Set.Ioi (1 : ℝ)))
    apply hI.congr_fun ?_ measurableSet_Ioi
    intro t ht
    by_cases h1 : 1 < t
    · have htpos : 0 < t := ht
      have htIoi : t ∈ Set.Ioi (1 : ℝ) := h1
      have hinv : t⁻¹ < 1 := (inv_lt_one₀ htpos).2 h1
      have hinvIoi : t⁻¹ ∉ Set.Ioi (1 : ℝ) := by
        intro h
        exact (not_lt_of_ge hinv.le) h
      simp only [Set.indicator_of_mem htIoi]
      have hHzero : H t = 0 := by
        simp only [H]
        rw [Real.rpow_neg_one]
        simp [GP, Set.indicator_of_notMem hinvIoi]
      rw [hmodif]
      simp [hHzero]
    · have htIoi : t ∉ Set.Ioi (1 : ℝ) := h1
      have hGPzero : GP t = 0 := by simp [GP, htIoi]
      simp [Set.indicator_of_notMem htIoi, hGPzero]
  have hHint (r : ℂ) :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (r - 1) • H t) (Set.Ioi (0 : ℝ)) := by
    have hI :
        IntegrableOn
          ((Set.Ioo (0 : ℝ) 1).indicator
            (fun t : ℝ => (t : ℂ) ^ (r - 1) • P.f_modif t))
          (Set.Ioi (0 : ℝ)) :=
      (hPconv r).indicator (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))
    apply hI.congr_fun ?_ measurableSet_Ioi
    intro t ht
    by_cases hsmall : t ∈ Set.Ioo (0 : ℝ) 1
    · have hinvIoi : t⁻¹ ∈ Set.Ioi (1 : ℝ) := by
        exact (one_lt_inv₀ hsmall.1).2 hsmall.2
      have htIoi : t ∉ Set.Ioi (1 : ℝ) := by
        intro h
        exact (not_lt_of_ge hsmall.2.le) h
      simp only [Set.indicator_of_mem hsmall]
      have hGPzero : GP t = 0 := by simp [GP, htIoi]
      rw [hmodif]
      simp only [Pi.add_apply]
      rw [hGPzero]
      simp
    · have hinvIoi : t⁻¹ ∉ Set.Ioi (1 : ℝ) := by
        intro h
        exact hsmall ⟨ht, (one_lt_inv₀ ht).1 h⟩
      have hHzero : H t = 0 := by
        simp only [H]
        rw [Real.rpow_neg_one]
        simp [GP, Set.indicator_of_notMem hinvIoi]
      simp [Set.indicator_of_notMem hsmall, hHzero]
  have hsplit (r : ℂ) :
      mellin P.f_modif r = mellin GP r + mellin H r := by
    unfold mellin
    rw [← integral_add (hGPint r) (hHint r)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    rw [hmodif]
    simp only [Pi.add_apply, smul_add]
  have hH (r : ℂ) :
      mellin H r = mellin G (1 / 2 - r) := by
    calc
      mellin H r =
          mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) •
            GP (t ^ (-1 : ℝ))) r := by rfl
      _ = mellin (fun t : ℝ => GP (t ^ (-1 : ℝ))) (r - 1 / 2) := by
        simpa [sub_eq_add_neg] using
          (mellin_cpow_smul (fun t : ℝ => GP (t ^ (-1 : ℝ))) r
            (-(1 / 2 : ℂ)))
      _ = mellin (fun t : ℝ => G (t ^ (-1 : ℝ))) (r - 1 / 2) := by
        rw [hG]
      _ = mellin G (1 / 2 - r) := hcomp'
  have hGPraw_top {t : ℝ} (ht : 1 < t) :
      GP t = ((chapter04RationalTheta t - 1 : ℝ) : ℂ) := by
    rw [← hG]
    simp [G, ht]
  have hmodif_top {t : ℝ} (ht : 1 < t) :
      P.f_modif t = GP t := by
    have htpos : 0 < t := lt_trans zero_lt_one ht
    have hinv : t⁻¹ < 1 := (inv_lt_one₀ htpos).2 ht
    have hinvIoi : t⁻¹ ∉ Set.Ioi (1 : ℝ) := by
      intro h
      exact (not_lt_of_ge hinv.le) h
    have hHzero : H t = 0 := by
      simp only [H]
      rw [Real.rpow_neg_one]
      simp [GP, Set.indicator_of_notMem hinvIoi]
    rw [hmodif]
    simp [hHzero]
  have hmodif_small {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
      P.f_modif t = H t := by
    have htIoi : t ∉ Set.Ioi (1 : ℝ) := by
      intro h
      exact (not_lt_of_ge ht1.le) h
    have hGPzero : GP t = 0 := by simp [GP, htIoi]
    rw [hmodif]
    simp [hGPzero]
  have hsmall_exp : -1 < ((s / 2 : ℂ) - 3 / 2).re := by
    norm_num [Complex.div_re, Complex.sub_re]
    linarith
  have hsmall_exp2 : -1 < ((s / 2 : ℂ) - 1).re := by
    norm_num [Complex.div_re, Complex.sub_re]
    linarith
  have hcorr :
      (1 / 2 : ℂ) *
          ∫ t in Set.Ioo (0 : ℝ) 1,
            ((t ^ (-(1 / 2 : ℝ)) - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume =
        chapter04ZeroVectorCorrection s := by
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      norm_num at hs
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hs
      norm_num at hs
    have hexp1 : -1 < ((s / 2 : ℂ) - 3 / 2).re := by
      norm_num [Complex.div_re, Complex.sub_re]
      linarith
    have hexp2 : -1 < ((s / 2 : ℂ) - 1).re := by
      norm_num [Complex.div_re, Complex.sub_re]
      linarith
    unfold chapter04ZeroVectorCorrection
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    have hcongr :
        (∫ t : ℝ in 0..1,
          ((t ^ (-(1 / 2 : ℝ)) - 1 : ℝ) : ℂ) *
            ((t : ℂ) ^ (s / 2) / (t : ℂ))) =
        ∫ t : ℝ in 0..1,
          ((t : ℂ) ^ (s / 2 - 3 / 2) - (t : ℂ) ^ (s / 2 - 1)) := by
      apply intervalIntegral.integral_congr_ae
      refine (volume.ae_ne (0 : ℝ)).mono ?_
      intro t ht0 ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have htpos : 0 < t := ht.1
      have hroot :
          ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
            (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
        simpa [Complex.ofReal_neg] using
          (Complex.ofReal_cpow htpos.le (-(1 / 2 : ℝ)))
      have hquot :
          (t : ℂ) ^ (s / 2) / (t : ℂ) =
            (t : ℂ) ^ (s / 2 - 1) := by
        calc
          (t : ℂ) ^ (s / 2) / (t : ℂ) =
              (t : ℂ) ^ (s / 2) / (t : ℂ) ^ (1 : ℂ) := by
                rw [Complex.cpow_one]
          _ = (t : ℂ) ^ (s / 2 - 1) :=
            (Complex.cpow_sub (s / 2) 1
              (Complex.ofReal_ne_zero.mpr htpos.ne')).symm
      rw [Complex.ofReal_sub, hroot, hquot]
      rw [sub_mul]
      simp only [Complex.ofReal_one, one_mul]
      rw [← Complex.cpow_add _ _
        (Complex.ofReal_ne_zero.mpr htpos.ne')]
      congr 1
      · congr 1
        ring
    rw [hcongr,
      intervalIntegral.integral_sub
        (intervalIntegral.intervalIntegrable_cpow' hexp1)
        (intervalIntegral.intervalIntegrable_cpow' hexp2),
      integral_cpow (Or.inl hexp1),
      integral_cpow (Or.inl hexp2)]
    have hden1 : s / 2 - 3 / 2 + 1 ≠ 0 := by
      intro h
      apply hs1
      linear_combination 2 * h
    have hden2 : s / 2 - 1 + 1 ≠ 0 := by
      intro h
      apply hs0
      linear_combination 2 * h
    have hsdiv2 : s / 2 ≠ 0 := div_ne_zero hs0 (by norm_num)
    simp [Complex.zero_cpow hden1, Complex.zero_cpow hsdiv2]
    field_simp [hden1, hden2, hs0, hs1]
    have hden3 : s - 3 + 2 ≠ 0 := by
      intro h
      apply hs1
      linear_combination h
    field_simp [hden3]
    ring
  have htail_pointwise {t : ℝ} (ht : 1 < t) :
      (t : ℂ) ^ (s / 2 - 1) • P.f_modif t =
        ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
          ((t : ℂ) ^ (s / 2) / (t : ℂ)) := by
    have hfm := hmodif_top ht
    have hraw := hGPraw_top ht
    have hpow :
        (t : ℂ) ^ (s / 2 - 1) =
          (t : ℂ) ^ (s / 2) / (t : ℂ) := by
      rw [Complex.cpow_sub (s / 2) 1
        (Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one ht).ne'),
        Complex.cpow_one]
    rw [hfm, hraw, hpow]
    simp only [smul_eq_mul]
    ring
  have htail_int :
      IntegrableOn
        (fun t : ℝ =>
          ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
            ((t : ℂ) ^ (s / 2) / (t : ℂ)))
        (Set.Ioi (1 : ℝ)) := by
    have hI :
        IntegrableOn
          (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • P.f_modif t)
          (Set.Ioi (1 : ℝ)) := by
      apply (hPconv (s / 2)).mono_set
      intro t ht
      change 1 < t at ht
      exact lt_trans zero_lt_one ht
    apply hI.congr_fun ?_ measurableSet_Ioi
    intro t ht
    change 1 < t at ht
    have hfm := hmodif_top ht
    have hraw := hGPraw_top ht
    have hpow :
        (t : ℂ) ^ (s / 2 - 1) =
          (t : ℂ) ^ (s / 2) / (t : ℂ) := by
        rw [Complex.cpow_sub (s / 2) 1
        (Complex.ofReal_ne_zero.mpr (lt_trans zero_lt_one ht).ne'),
        Complex.cpow_one]
    change (t : ℂ) ^ (s / 2 - 1) • P.f_modif t =
      ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
        ((t : ℂ) ^ (s / 2) / (t : ℂ))
    rw [hfm, hraw, hpow]
    simp only [smul_eq_mul]
    ring
  have hsmall_pointwise {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
      (t : ℂ) ^ (s / 2 - 1) • P.f_modif t +
          ((t : ℂ) ^ (s / 2 - 3 / 2) -
            (t : ℂ) ^ (s / 2 - 1)) =
        ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
          ((t : ℂ) ^ (s / 2) / (t : ℂ)) := by
    have hfm :
        P.f_modif t =
          (chapter04RationalTheta t : ℂ) -
            (t ^ (-(1 / 2 : ℝ)) : ℝ) := by
      have htIoi : t ∉ Set.Ioi (1 : ℝ) := by
        intro h
        exact (not_lt_of_ge ht1.le) h
      have htIoo : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
      simp only [WeakFEPair.f_modif, Pi.add_apply,
        Set.indicator_of_notMem htIoi, Set.indicator_of_mem htIoo]
      simp [P, HurwitzZeta.hurwitzEvenFEPair,
        Function.comp_def, HurwitzZeta.evenKernel_eq_cosKernel_of_zero,
        htheta t ht0, smul_eq_mul]
    have hroot :
        ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
          (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
      simpa [Complex.ofReal_neg] using
        (Complex.ofReal_cpow ht0.le (-(1 / 2 : ℝ)))
    have hpow1 :
        (t : ℂ) ^ (s / 2 - 1) =
          (t : ℂ) ^ (s / 2) / (t : ℂ) := by
      rw [Complex.cpow_sub (s / 2) 1
        (Complex.ofReal_ne_zero.mpr ht0.ne'), Complex.cpow_one]
    have hpow2 :
        (t : ℂ) ^ (s / 2 - 3 / 2) =
          (t : ℂ) ^ (-(1 / 2 : ℂ)) * (t : ℂ) ^ (s / 2 - 1) := by
      calc
        (t : ℂ) ^ (s / 2 - 3 / 2) =
            (t : ℂ) ^ (-(1 / 2 : ℂ) + (s / 2 - 1)) := by
              congr 1
              ring
        _ = (t : ℂ) ^ (-(1 / 2 : ℂ)) *
            (t : ℂ) ^ (s / 2 - 1) := by
              rw [Complex.cpow_add _ _
                (Complex.ofReal_ne_zero.mpr ht0.ne')]
    rw [hfm, hroot, hpow2, hpow1]
    simp only [smul_eq_mul]
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hFsmall :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • P.f_modif t)
        (Set.Ioo (0 : ℝ) 1) := by
    apply (hPconv (s / 2)).mono_set
    intro t ht
    exact ht.1
  have hCsmall1 :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s / 2 - 3 / 2))
        (Set.Ioo (0 : ℝ) 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_cpow' hsmall_exp) |>.mono_set
    intro t ht
    exact ⟨ht.1, ht.2.le⟩
  have hCsmall2 :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1))
        (Set.Ioo (0 : ℝ) 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_cpow' hsmall_exp2) |>.mono_set
    intro t ht
    exact ⟨ht.1, ht.2.le⟩
  have hCsmall :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s / 2 - 3 / 2) -
          (t : ℂ) ^ (s / 2 - 1))
        (Set.Ioo (0 : ℝ) 1) := hCsmall1.sub hCsmall2
  have hsmall_int :
      IntegrableOn
        (fun t : ℝ =>
          ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
            ((t : ℂ) ^ (s / 2) / (t : ℂ)))
        (Set.Ioo (0 : ℝ) 1) := by
    apply (hFsmall.add hCsmall).congr_fun ?_ measurableSet_Ioo
    intro t ht
    exact hsmall_pointwise ht.1 ht.2
  have hsmall_integral :
      (∫ t in Set.Ioo (0 : ℝ) 1,
        ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
          ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume) =
        (∫ t in Set.Ioo (0 : ℝ) 1,
          (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume) +
          ∫ t in Set.Ioo (0 : ℝ) 1,
            ((t : ℂ) ^ (s / 2 - 3 / 2) -
              (t : ℂ) ^ (s / 2 - 1)) ∂volume := by
    rw [← integral_add hFsmall hCsmall]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    exact (hsmall_pointwise ht.1 ht.2).symm
  have hcorr_integral :
      (∫ t in Set.Ioo (0 : ℝ) 1,
        (t : ℂ) ^ (s / 2 - 3 / 2) - (t : ℂ) ^ (s / 2 - 1) ∂volume) =
        ∫ t in Set.Ioo (0 : ℝ) 1,
          ((t ^ (-(1 / 2 : ℝ)) - 1 : ℝ) : ℂ) *
            ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    have ht0 : 0 < t := ht.1
    have hroot :
        ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) =
          (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
      simpa [Complex.ofReal_neg] using
        (Complex.ofReal_cpow ht0.le (-(1 / 2 : ℝ)))
    have hquot :
        (t : ℂ) ^ (s / 2) / (t : ℂ) =
          (t : ℂ) ^ (s / 2 - 1) := by
      rw [Complex.cpow_sub (s / 2) 1
        (Complex.ofReal_ne_zero.mpr ht0.ne'), Complex.cpow_one]
    have hpow :
        (t : ℂ) ^ (s / 2 - 3 / 2) =
          (t : ℂ) ^ (-(1 / 2 : ℂ)) *
            (t : ℂ) ^ (s / 2 - 1) := by
      rw [← Complex.cpow_add _ _
        (Complex.ofReal_ne_zero.mpr ht0.ne')]
      congr 1
      ring
    dsimp
    rw [hpow, Complex.ofReal_sub, hroot, hquot, Complex.ofReal_one]
    ring
  have hFsmallIoc :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • P.f_modif t)
        (Set.Ioc (0 : ℝ) 1) := by
    apply (hPconv (s / 2)).mono_set
    intro t ht
    exact ht.1
  have hFtail :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s / 2 - 1) • P.f_modif t)
        (Set.Ioi (1 : ℝ)) := by
    apply (hPconv (s / 2)).mono_set
    intro t ht
    change 1 < t at ht
    exact lt_trans zero_lt_one ht
  have hFsplit :
      mellin P.f_modif (s / 2) =
        (∫ t in Set.Ioc (0 : ℝ) 1,
          (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume) +
          ∫ t in Set.Ioi (1 : ℝ),
            (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume := by
    unfold mellin
    rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    rw [setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      hFsmallIoc hFtail]
  have htail_f_integral :
      (∫ t in Set.Ioi (1 : ℝ),
        (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume) =
        ∫ t in Set.Ioi (1 : ℝ),
          ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
            ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change 1 < t at ht
    exact htail_pointwise ht
  have hFsplit' :
      mellin P.f_modif (s / 2) =
        (∫ t in Set.Ioo (0 : ℝ) 1,
          (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume) +
          ∫ t in Set.Ioi (1 : ℝ),
            ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := by
    calc
      mellin P.f_modif (s / 2) =
          (∫ t in Set.Ioc (0 : ℝ) 1,
            (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume) +
            ∫ t in Set.Ioi (1 : ℝ),
              (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume := hFsplit
      _ =
          (∫ t in Set.Ioo (0 : ℝ) 1,
            (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume) +
            ∫ t in Set.Ioi (1 : ℝ),
              ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
                ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := by
        rw [integral_Ioc_eq_integral_Ioo, htail_f_integral]
  let U : Set ℝ := Set.Ioo (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)
  have hraw_set : (Set.Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume] U := by
    apply ae_eq_set.2
    constructor
    · refine measure_mono_null ?_ (by simp : volume ({1} : Set ℝ) = 0)
      intro t ht
      change t = 1
      have htU : t ∉ Set.Ioo (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
        simpa [U] using ht.2
      rcases lt_trichotomy 1 t with hlt | heq | hgt
      · exact (htU (Or.inr hlt)).elim
      · exact heq.symm
      · exact (htU (Or.inl ⟨ht.1, hgt⟩)).elim
    · refine measure_mono_null ?_ (by simp : volume ({1} : Set ℝ) = 0)
      intro t ht
      have htU : t ∈ Set.Ioo (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
        simpa [U] using ht.1
      exact (by
        rcases htU with ht' | ht'
        · exact (ht.2 ht'.1).elim
        · exact (ht.2 (show 0 < t from lt_trans zero_lt_one ht')).elim)
  have hraw_split :
      (∫ t in Set.Ioi (0 : ℝ),
        ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
          ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume) =
        (∫ t in Set.Ioo (0 : ℝ) 1,
          ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
            ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume) +
          ∫ t in Set.Ioi (1 : ℝ),
            ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := by
    have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
      refine Set.disjoint_left.2 ?_
      intro t ht0 ht1
      exact (not_lt_of_ge ht0.2.le) ht1
    rw [setIntegral_congr_set hraw_set]
    rw [setIntegral_union hdisj measurableSet_Ioi hsmall_int htail_int]
  have hmodif_mellin :
      mellin P.f_modif (s / 2) =
        mellin GP (s / 2) + mellin GP ((1 - s) / 2) := by
    calc
      mellin P.f_modif (s / 2) =
          mellin GP (s / 2) + mellin H (s / 2) := hsplit (s / 2)
      _ = mellin GP (s / 2) + mellin G (1 / 2 - s / 2) := by
        rw [hH]
      _ = mellin GP (s / 2) + mellin GP ((1 - s) / 2) := by
        rw [hG]
        congr 1
        ring_nf
  have htail_sum :
      (1 / 2 : ℂ) *
          ∫ t in Set.Ioi (1 : ℝ),
            ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume +
        (1 / 2 : ℂ) *
          ∫ t in Set.Ioi (1 : ℝ),
            ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ ((1 - s) / 2) / (t : ℂ)) ∂volume =
        (1 / 2 : ℂ) * mellin P.f_modif (s / 2) := by
    calc
      _ = (1 / 2 : ℂ) * mellin GP (s / 2) +
          (1 / 2 : ℂ) * mellin GP ((1 - s) / 2) := by
        rw [htailP (s / 2), htailP ((1 - s) / 2)]
      _ = (1 / 2 : ℂ) *
          (mellin GP (s / 2) + mellin GP ((1 - s) / 2)) := by
        ring
      _ = (1 / 2 : ℂ) * mellin P.f_modif (s / 2) := by
        rw [hmodif_mellin]
  have hraw_eq :
      (∫ t in Set.Ioi (0 : ℝ),
        ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
          ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume) =
        mellin P.f_modif (s / 2) +
          ∫ t in Set.Ioo (0 : ℝ) 1,
            ((t ^ (-(1 / 2 : ℝ)) - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := by
    calc
      (∫ t in Set.Ioi (0 : ℝ),
          ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
            ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume) =
          (∫ t in Set.Ioo (0 : ℝ) 1,
            ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume) +
            ∫ t in Set.Ioi (1 : ℝ),
              ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
                ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := hraw_split
      _ =
          ((∫ t in Set.Ioo (0 : ℝ) 1,
              (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume) +
            ∫ t in Set.Ioo (0 : ℝ) 1,
              ((t : ℂ) ^ (s / 2 - 3 / 2) -
                (t : ℂ) ^ (s / 2 - 1)) ∂volume) +
            ∫ t in Set.Ioi (1 : ℝ),
              ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
                ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := by
        rw [hsmall_integral]
      _ =
          ((∫ t in Set.Ioo (0 : ℝ) 1,
              (t : ℂ) ^ (s / 2 - 1) • P.f_modif t ∂volume) +
            ∫ t in Set.Ioi (1 : ℝ),
              ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
                ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume) +
            ∫ t in Set.Ioo (0 : ℝ) 1,
              ((t : ℂ) ^ (s / 2 - 3 / 2) -
                (t : ℂ) ^ (s / 2 - 1)) ∂volume := by
        ring
      _ = mellin P.f_modif (s / 2) +
            ∫ t in Set.Ioo (0 : ℝ) 1,
              ((t : ℂ) ^ (s / 2 - 3 / 2) -
                (t : ℂ) ^ (s / 2 - 1)) ∂volume := by
        rw [← hFsplit']
      _ = mellin P.f_modif (s / 2) +
            ∫ t in Set.Ioo (0 : ℝ) 1,
              ((t ^ (-(1 / 2 : ℝ)) - 1 : ℝ) : ℂ) *
                ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := by
        rw [hcorr_integral]
  have hmain :
      (1 / 2 : ℂ) *
          ∫ t in Set.Ioi (0 : ℝ),
            ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume =
        (1 / 2 : ℂ) * mellin P.f_modif (s / 2) +
          chapter04ZeroVectorCorrection s := by
    calc
      (1 / 2 : ℂ) *
          ∫ t in Set.Ioi (0 : ℝ),
            ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume =
          (1 / 2 : ℂ) *
            (mellin P.f_modif (s / 2) +
              ∫ t in Set.Ioo (0 : ℝ) 1,
                ((t ^ (-(1 / 2 : ℝ)) - 1 : ℝ) : ℂ) *
                  ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume) := by
        rw [hraw_eq]
      _ = (1 / 2 : ℂ) * mellin P.f_modif (s / 2) +
          (1 / 2 : ℂ) *
            ∫ t in Set.Ioo (0 : ℝ) 1,
              ((t ^ (-(1 / 2 : ℝ)) - 1 : ℝ) : ℂ) *
                ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := by
        ring
      _ = (1 / 2 : ℂ) * mellin P.f_modif (s / 2) +
          chapter04ZeroVectorCorrection s := by
        rw [hcorr]
  calc
    chapter04RationalThetaMellin s =
        (1 / 2 : ℂ) *
            ∫ t in Set.Ioi (1 : ℝ),
              ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
                ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume +
          (1 / 2 : ℂ) *
            ∫ t in Set.Ioi (1 : ℝ),
              ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
                ((t : ℂ) ^ ((1 - s) / 2) / (t : ℂ)) ∂volume +
          chapter04ZeroVectorCorrection s := by
      rfl
    _ = (1 / 2 : ℂ) * mellin P.f_modif (s / 2) +
          chapter04ZeroVectorCorrection s := by
      rw [htail_sum]
    _ = (1 / 2 : ℂ) *
          ∫ t in Set.Ioi (0 : ℝ),
            ((chapter04RationalTheta t - 1 : ℝ) : ℂ) *
              ((t : ℂ) ^ (s / 2) / (t : ℂ)) ∂volume := hmain.symm
    _ = chapter04RationalThetaMellinIntegral s := by
      rfl

theorem chapter04_rational_theta_mellin_integral_eq_completed_riemann_zeta
    {s : ℂ} (hs : 1 < s.re) :
    chapter04RationalThetaMellinIntegral s =
      (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s := by
  have htheta (u : ℝ) (hu : 0 < u) :
      chapter04RationalTheta u = HurwitzZeta.cosKernel 0 u := by
    have hsum := HurwitzZeta.hasSum_int_cosKernel 0 hu
    have hsum' :
        HasSum
          (fun n : ℤ => (Real.exp (-Real.pi * (n : ℝ) ^ 2 * u) : ℂ))
          (HurwitzZeta.cosKernel 0 u : ℂ) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsum
    have hsumR :
        HasSum (fun n : ℤ => Real.exp (-Real.pi * (n : ℝ) ^ 2 * u))
          (HurwitzZeta.cosKernel 0 u) := by
      exact (Complex.hasSum_ofReal).mp hsum'
    unfold chapter04RationalTheta
    simpa [mul_comm, mul_left_comm, mul_assoc] using hsumR.tsum_eq
  have hraw :
      chapter04RationalThetaMellinIntegral s =
        mellin
          (fun t : ℝ => ((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ) / 2)
          (s / 2) := by
    unfold chapter04RationalThetaMellinIntegral mellin
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hpow :
        (t : ℂ) ^ (s / 2 - 1) =
          (t : ℂ) ^ (s / 2) / (t : ℂ) := by
      rw [Complex.cpow_sub (s / 2) 1
        (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
    dsimp
    rw [htheta t ht, hpow]
    simp
    ring
  have hcos :
      HurwitzZeta.completedCosZeta 0 s =
        mellin
          (fun t : ℝ => ((HurwitzZeta.cosKernel 0 t - 1 : ℝ) : ℂ) / 2)
          (s / 2) := by
    rw [mellin_div_const, HurwitzZeta.completedCosZeta]
    congr 1
    simpa [HurwitzZeta.hurwitzEvenFEPair, WeakFEPair.symm,
      Function.comp_def] using
      (((HurwitzZeta.hurwitzEvenFEPair 0).symm.hasMellin (by
        simp [HurwitzZeta.hurwitzEvenFEPair, WeakFEPair.symm,
          Complex.div_ofNat_re]
        linarith)).2.symm)
  calc
    chapter04RationalThetaMellinIntegral s =
        HurwitzZeta.completedCosZeta 0 s := hraw.trans hcos.symm
    _ = completedRiemannZeta s := HurwitzZeta.completedCosZeta_zero s
    _ = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s := by
      rw [completedZeta_eq_tsum_of_one_lt_re hs,
        zeta_eq_tsum_one_div_nat_cpow hs]

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
