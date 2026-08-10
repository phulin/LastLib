import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01

noncomputable section

open scoped TensorProduct WithZero

/-! # Book 2, Chapter 1, Section 1.1

The declarations in this file fix the local-field notation used throughout the
chapter.  Valuation equivalence is kept separate from the normalized additive
valuation scale: the former describes the place and the latter records the
ramification factor.
-/

universe u

/-! ### The four structures attached to one valued field -/

/-- The valuation ring attached to a chosen valuation. -/
abbrev chapter01ValuationRing {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : Type _ :=
  v.valuationSubring

/-- The maximal ideal of the chosen valuation ring. -/
abbrev chapter01MaximalIdeal {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    Ideal (chapter01ValuationRing v) :=
  IsLocalRing.maximalIdeal (chapter01ValuationRing v)

/-- The residue field of the chosen valuation ring. -/
abbrev chapter01ResidueField {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : Type _ :=
  IsLocalRing.ResidueField (chapter01ValuationRing v)

/-- Completeness and rank-one discreteness for a normalized multiplicative valuation. -/
def chapter01CompleteDiscreteValuation (K : Type*) [Field K]
    (v : Valuation K ℤᵐ⁰) : Prop :=
  Valuation.IsRankOneDiscrete v ∧
    IsAdicComplete (chapter01MaximalIdeal v) (chapter01ValuationRing v)

/-- A uniformizer in the valuation ring, expressed by its maximal-ideal equation. -/
def chapter01IsUniformizer {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (π : chapter01ValuationRing v) : Prop :=
  π ≠ 0 ∧ chapter01MaximalIdeal v = Ideal.span ({π} : Set (chapter01ValuationRing v))

/-- A discrete valuation ring has a generator for its maximal ideal. -/
theorem chapter01_complete_discrete_has_uniformizer
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    [Valuation.IsRankOneDiscrete v] :
    ∃ π : chapter01ValuationRing v, chapter01IsUniformizer v π := by
  obtain ⟨π, hπ⟩ :=
    Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial v
  refine ⟨π, ?_⟩
  exact ⟨by
    intro h
    apply hπ.ne_zero
    exact congrArg (fun y : chapter01ValuationRing v => (y : K)) h,
    hπ.is_generator⟩

/-! ### Normalized additive scales and compatible valuation rings -/

/-- The normalized additive restriction formula with its positive integer factor. -/
def chapter01ValuationRestrictionScale
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) : Prop :=
  0 < e ∧ ∀ x : K, x ≠ 0 →
    vL (algebraMap K L x) = e • vK x

/-- The multiplicative formulation of “the two valuations extend the same place”. -/
def chapter01SamePlace
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) : Prop :=
  vK.IsEquiv (vL.comap (algebraMap K L))

/-- For normalized discrete additive valuations, restriction changes only by a scale. -/
theorem chapter01_normalized_restriction_scale_exists
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvK : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hvL : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hext : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
    ∃ e : ℕ, chapter01ValuationRestrictionScale vK vL e := by
  rcases hvK with ⟨π, hπ0, hπ, hvK_values⟩
  have hvLπ_top : (AddValuation.comap (algebraMap K L) vL) π ≠
      (⊤ : WithTop ℤ) :=
    (AddValuation.ne_top_iff _).2 hπ0
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hvLπ_top
  have hm' : (AddValuation.comap (algebraMap K L) vL) π = (m : WithTop ℤ) :=
    hm.symm
  have hle :=
    Valuation.IsEquiv.le_iff_le hext (x := π) (y := 1)
  change vK 1 ≤ vK π ↔
    (AddValuation.comap (algebraMap K L) vL) 1 ≤
      (AddValuation.comap (algebraMap K L) vL) π at hle
  have hm_nonneg : 0 ≤ m := by
    have hzero_le :
        (AddValuation.comap (algebraMap K L) vL) 1 ≤
          (AddValuation.comap (algebraMap K L) vL) π := by
      apply hle.mp
      simpa [hπ]
    simpa [hm'] using hzero_le
  have hm_ne_zero : m ≠ 0 := by
    intro hmzero
    have hval_eq : vK π = vK 1 := by
      apply (AddValuation.IsEquiv.val_eq hext).mpr
      rw [hm', hmzero]
      simp
    simpa [hπ] using hval_eq
  have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg (Ne.symm hm_ne_zero)
  obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le hm_nonneg
  subst m
  refine ⟨q, by exact_mod_cast hm_pos, ?_⟩
  have hnat_smul_comm : ∀ a b : ℕ,
      a • (b : WithTop ℤ) = b • (a : WithTop ℤ) := by
    intro a b
    have ha : (a : WithTop ℤ) = ((a : ℤ) : WithTop ℤ) := by simp
    have hb : (b : WithTop ℤ) = ((b : ℤ) : WithTop ℤ) := by simp
    rw [ha, hb, ← WithTop.coe_nsmul (b : ℤ) a,
      ← WithTop.coe_nsmul (a : ℤ) b]
    congr 1
    exact mul_comm _ _
  intro x hx
  obtain ⟨n, hn⟩ := hvK_values x hx
  cases n with
  | ofNat k =>
      have hvalue : vK x = vK (π ^ k) := by
        rw [hn]
        simp [hπ]
      have hvalue' :
          (AddValuation.comap (algebraMap K L) vL) x =
            (AddValuation.comap (algebraMap K L) vL) (π ^ k) :=
        (AddValuation.IsEquiv.val_eq hext).mp hvalue
      calc
        vL (algebraMap K L x) =
            (AddValuation.comap (algebraMap K L) vL) x := rfl
        _ = (AddValuation.comap (algebraMap K L) vL) (π ^ k) := hvalue'
        _ = q • vK x := by
          simp [AddValuation.map_pow, hm', hn]
          exact hnat_smul_comm k q
  | negSucc k =>
      have hvalue : vK x = vK ((π ^ (k + 1))⁻¹) := by
        rw [hn]
        simp [hπ, Int.negSucc_eq]
      have hvalue' :
          (AddValuation.comap (algebraMap K L) vL) x =
            (AddValuation.comap (algebraMap K L) vL) ((π ^ (k + 1))⁻¹) :=
        (AddValuation.IsEquiv.val_eq hext).mp hvalue
      calc
        vL (algebraMap K L x) =
            (AddValuation.comap (algebraMap K L) vL) x := rfl
        _ = (AddValuation.comap (algebraMap K L) vL) ((π ^ (k + 1))⁻¹) := hvalue'
        _ = q • vK x := by
          simp [AddValuation.map_pow, AddValuation.map_inv, hm', hn,
            Int.negSucc_eq]
          rw [succ_nsmul, hnat_smul_comm k q, add_comm]
          simpa [WithTop.LinearOrderedAddCommGroup.coe_neg] using
            (add_comm (-(q • (k : WithTop ℤ))) (-(q : WithTop ℤ)))

/-! ### The finite extension is still local -/

/-- In a finite complete extension, the upper valuation ring is complete, finite, and a DVR. -/
theorem chapter01_finite_extension_remains_local
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring ∧
      IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring ∧
      IsDiscreteValuationRing vL.valuationSubring := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring vK vL hcomplete

/-- The upper valuation ring is the integral closure of the lower one. -/
theorem chapter01_extension_valuation_ring_is_integral_closure
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    (vL.valuationSubring : Set L) =
      {x : L | IsIntegral vK.valuationSubring x} := by
  have hfinite := chapter01_finite_extension_remains_local vK vL hcomplete
  letI : Module.Finite vK.valuationSubring vL.valuationSubring := hfinite.1
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_unit_ball_is_integral_closure
    vK vL

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
