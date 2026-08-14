import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section06TheValuationRingInAFiniteCompleteExtension

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02

noncomputable section

open Ideal IsLocalRing
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12
open scoped BigOperators WithZero

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ## Book 2, Chapter 2, §2.3

`chapterRamificationIndex` and `chapterResidueDegree` are the Book 1
Chapter 12 wrappers around Mathlib's `Ideal.ramificationIdx` and
`Ideal.inertiaDeg`.  Under the complete DVR hypotheses these are the
ideal-theoretic realizations of the value-group index and residue-field
dimension in the source.
-/

/-- The normalized restriction formula in Mathlib's multiplicative notation. -/
def chapter2NormalizedValuationRestriction
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰) (e : ℕ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = vK x ^ e

/-- A valuation to `ℤᵐ⁰` is normalized when it is surjective onto its target. -/
def chapter2SurjectiveIntegerValuation
    {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰) : Prop :=
  Function.Surjective v

/-- The residue-field extension attached to two extending valuation rings. -/
def chapter2ResidueFieldExtension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] : Prop :=
    Module.Finite (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

private theorem chapter2_maximal_ideal_extension_is_power_aux
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    (IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring) =
      (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e := by
  let : FaithfulSMul vK.valuationSubring vL.valuationSubring :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Valuation.HasExtension.algebraMap_injective (vK := vK) (vA := vL))
  let A := vK.valuationSubring
  let B := vL.valuationSubring
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  let J : Ideal B := mA.map (algebraMap A B)
  have hJ0 : J ≠ ⊥ := by
    exact Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field A)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal mB) J hJ0
  have hlen :
      (Module.length (Localization.AtPrime mB)
        (Localization.AtPrime mB ⧸
          mA.map (algebraMap A (Localization.AtPrime mB)))).toNat = n := by
    have hmaploc :
        mA.map (algebraMap A (Localization.AtPrime mB)) =
          J.map (algebraMap B (Localization.AtPrime mB)) := by
      rw [Ideal.map_map]
      congr 1
    let : IsDiscreteValuationRing (Localization.AtPrime mB) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
        (IsDiscreteValuationRing.not_a_field B) (Localization.AtPrime mB)
    rw [hmaploc, hn, Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  have hen : e = n := by
    calc
      e = chapterRamificationIndex A B mB := he.symm
      _ = (Module.length (Localization.AtPrime mB)
          (Localization.AtPrime mB ⧸
            mA.map (algebraMap A (Localization.AtPrime mB)))).toNat := by
        unfold chapterRamificationIndex
        exact Ideal.ramificationIdx_eq mA mB
      _ = n := hlen
  change J = mB ^ e
  rw [hn, ← hen]

/-- In the normalized convention, restriction scales by the ramification index.

`Valuation.HasExtension` fixes only the valuation ring, so the surjectivity
hypotheses are needed to fix the integer-valued normalization as well. -/
theorem valuation_restriction_is_power_of_ramification_index
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (hK : chapter2SurjectiveIntegerValuation vK)
    (hL : chapter2SurjectiveIntegerValuation vL)
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    ∀ x : K, vL (algebraMap K L x) = vK x ^ e := by
  obtain ⟨πK, hπK⟩ :=
    Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial vK
  obtain ⟨πL, hπL⟩ :=
    Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial vL
  have hmap := chapter2_maximal_ideal_extension_is_power_aux vK vL e he
  have hspan :
      Ideal.span ({(πL : vL.valuationSubring) ^ e} :
          Set vL.valuationSubring) =
        Ideal.span ({algebraMap vK.valuationSubring vL.valuationSubring πK} :
          Set vL.valuationSubring) := by
    calc
      Ideal.span ({(πL : vL.valuationSubring) ^ e} :
          Set vL.valuationSubring) =
          (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e := by
            rw [hπL.is_generator, Ideal.span_singleton_pow]
      _ = (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring) := hmap.symm
      _ = Ideal.span ({algebraMap vK.valuationSubring vL.valuationSubring πK} :
          Set vL.valuationSubring) := by
            rw [hπK.is_generator, Ideal.map_span]
            simp
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hfac :
      algebraMap vK.valuationSubring vL.valuationSubring πK =
        (u : vL.valuationSubring) * (πL : vL.valuationSubring) ^ e := by
    simpa [mul_comm] using hu.symm
  have huval : vL (u : L) = 1 := by
    have huval' : vL.valuationSubring.valuation (u : L) = 1 :=
      (ValuationSubring.valuation_eq_one_iff vL.valuationSubring
        (u : vL.valuationSubring)).mp u.isUnit
    exact ((Valuation.isEquiv_valuation_valuationSubring vL).eq_one_iff_eq_one).mpr huval'
  have hfac' :
      algebraMap K L (πK : K) = (u : L) * (πL : L) ^ e := by
    have h := congrArg (fun z : vL.valuationSubring => (z : L)) hfac
    simpa [Valuation.HasExtension.coe_algebraMap_valuationSubring_eq] using h
  have hπmap : vL (algebraMap K L (πK : K)) =
      (vK (πK : K)) ^ e := by
    have hπLval : vL (πL : L) = WithZero.exp (-1 : ℤ) := by
      calc
        vL (πL : L) = (Valuation.IsRankOneDiscrete.generator vL : ℤᵐ⁰) := hπL.val
        _ = WithZero.exp (-1 : ℤ) := by
          rw [Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective hL]
          rfl
    have hπKval : vK (πK : K) = WithZero.exp (-1 : ℤ) := by
      calc
        vK (πK : K) = (Valuation.IsRankOneDiscrete.generator vK : ℤᵐ⁰) := hπK.val
        _ = WithZero.exp (-1 : ℤ) := by
          rw [Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective hK]
          rfl
    calc
      vL (algebraMap K L (πK : K)) = vL ((u : L) * (πL : L) ^ e) := by rw [hfac']
      _ = vL (u : L) * vL (πL : L) ^ e := by rw [map_mul, map_pow]
      _ = vL (πL : L) ^ e := by rw [huval, one_mul]
      _ = (WithZero.exp (-1 : ℤ)) ^ e := by rw [hπLval]
      _ = (vK (πK : K)) ^ e := by rw [hπKval]
  have hpower : ∀ x : K, x ≠ 0 → ∃ n : ℤ, vK x = (vK (πK : K)) ^ n := by
    intro x hx
    have hxv : vK x ≠ 0 := by simpa using hx
    have hxg : Units.mk0 (vK x) hxv ∈
        MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass vK) := by
      exact MonoidWithZeroHom.mem_valueGroup _ ⟨x, rfl⟩
    rw [hπK.zpowers_eq_valueGroup] at hxg
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxg
    refine ⟨n, ?_⟩
    have hn' := congrArg (fun z : ℤᵐ⁰ˣ => (z : ℤᵐ⁰)) hn
    simpa using hn'.symm
  have hepos : 0 < e := by
    rw [← he]
    unfold chapterRamificationIndex
    exact Ideal.ramificationIdx_pos
      (IsLocalRing.maximalIdeal vL.valuationSubring)
      vK.valuationSubring
  intro x
  obtain rfl | hx := eq_or_ne x 0
  · simp [Nat.ne_of_gt hepos]
  obtain ⟨n, hn⟩ := hpower x hx
  calc
    vL (algebraMap K L x) =
        vL (algebraMap K L ((πK : K) ^ n)) := by
      apply (Valuation.HasExtension.val_map_eq_iff vK vL x ((πK : K) ^ n)).mpr
      simpa only [map_zpow₀] using hn
    _ = (vL (algebraMap K L (πK : K))) ^ n := by
      rw [map_zpow₀, map_zpow₀]
    _ = ((vK (πK : K)) ^ e) ^ n := by rw [hπmap]
    _ = (vK x) ^ e := by
      have hpowcomm :
          (vK (πK : K) ^ e) ^ n = (vK (πK : K) ^ n) ^ e := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      exact hpowcomm.trans (congrArg (fun z : ℤᵐ⁰ => z ^ e) hn).symm

/-- The restriction formula with surjective integer-valued normalizations. -/
theorem normalized_valuation_restriction_has_ramification_factor
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (hK : chapter2SurjectiveIntegerValuation vK)
    (hL : chapter2SurjectiveIntegerValuation vL)
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    chapter2NormalizedValuationRestriction vK vL e := by
  exact valuation_restriction_is_power_of_ramification_index vK vL hK hL e he

/-- Uniformizers give the principal-ideal factorization `π_K = u π_L^e`. -/
theorem uniformizer_factorization
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e)
    (πK : vK.valuationSubring) (πL : vL.valuationSubring)
    (hπK : vK.IsUniformizer πK) (hπL : vL.IsUniformizer πL) :
    ∃ u : vL.valuationSubringˣ,
      algebraMap vK.valuationSubring vL.valuationSubring πK =
      (u : vL.valuationSubring) * (πL : vL.valuationSubring) ^ e := by
  let : FaithfulSMul vK.valuationSubring vL.valuationSubring :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Valuation.HasExtension.algebraMap_injective (vK := vK) (vA := vL))
  let A := vK.valuationSubring
  let B := vL.valuationSubring
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  let J : Ideal B := mA.map (algebraMap A B)
  have hJ0 : J ≠ ⊥ := by
    exact Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field A)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal mB) J hJ0
  have hlen :
      (Module.length (Localization.AtPrime mB)
        (Localization.AtPrime mB ⧸
          mA.map (algebraMap A (Localization.AtPrime mB)))).toNat = n := by
    have hmaploc :
      mA.map (algebraMap A (Localization.AtPrime mB)) =
          J.map (algebraMap B (Localization.AtPrime mB)) := by
      rw [Ideal.map_map]
      congr 1

    let : IsDiscreteValuationRing (Localization.AtPrime mB) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
        (IsDiscreteValuationRing.not_a_field B) (Localization.AtPrime mB)
    rw [hmaploc, hn, Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  have hen : e = n := by
    calc
      e = chapterRamificationIndex A B mB := he.symm
      _ = (Module.length (Localization.AtPrime mB)
          (Localization.AtPrime mB ⧸
            mA.map (algebraMap A (Localization.AtPrime mB)))).toNat := by
        unfold chapterRamificationIndex
        exact Ideal.ramificationIdx_eq mA mB
      _ = n := hlen
  have hmap : mA.map (algebraMap A B) = mB ^ e := by
    change J = mB ^ e
    rw [hn, ← hen]
  have hspan :
      Ideal.span ({(πL : vL.valuationSubring) ^ e} :
          Set vL.valuationSubring) =
        Ideal.span ({algebraMap vK.valuationSubring vL.valuationSubring πK} :
          Set vL.valuationSubring) := by
    calc
      Ideal.span ({(πL : vL.valuationSubring) ^ e} :
          Set vL.valuationSubring) =
          (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e := by
            rw [hπL.is_generator, Ideal.span_singleton_pow]
      _ = (IsLocalRing.maximalIdeal vK.valuationSubring).map
          (algebraMap vK.valuationSubring vL.valuationSubring) := hmap.symm
      _ = Ideal.span ({algebraMap vK.valuationSubring vL.valuationSubring πK} :
          Set vL.valuationSubring) := by
            rw [hπK.is_generator, Ideal.map_span]
            simp
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

/-- The extension of the base maximal ideal is the `e`th power upstairs. -/
theorem maximal_ideal_extension_is_power
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring]
    (e : ℕ)
    (he : chapterRamificationIndex vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring) = e) :
    (IsLocalRing.maximalIdeal vK.valuationSubring).map
        (algebraMap vK.valuationSubring vL.valuationSubring) =
      (IsLocalRing.maximalIdeal vL.valuationSubring) ^ e := by
  let : FaithfulSMul vK.valuationSubring vL.valuationSubring :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (Valuation.HasExtension.algebraMap_injective (vK := vK) (vA := vL))
  let A := vK.valuationSubring
  let B := vL.valuationSubring
  let mA := IsLocalRing.maximalIdeal A
  let mB := IsLocalRing.maximalIdeal B
  let J : Ideal B := mA.map (algebraMap A B)
  have hJ0 : J ≠ ⊥ := by
    exact Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field A)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal mB) J hJ0
  have hlen :
      (Module.length (Localization.AtPrime mB)
        (Localization.AtPrime mB ⧸
          mA.map (algebraMap A (Localization.AtPrime mB)))).toNat = n := by
    have hmaploc :
      mA.map (algebraMap A (Localization.AtPrime mB)) =
          J.map (algebraMap B (Localization.AtPrime mB)) := by
      rw [Ideal.map_map]
      congr 1

    let : IsDiscreteValuationRing (Localization.AtPrime mB) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
        (IsDiscreteValuationRing.not_a_field B) (Localization.AtPrime mB)
    rw [hmaploc, hn, Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  have hen : e = n := by
    calc
      e = chapterRamificationIndex A B mB := he.symm
      _ = (Module.length (Localization.AtPrime mB)
          (Localization.AtPrime mB ⧸
            mA.map (algebraMap A (Localization.AtPrime mB)))).toNat := by
        unfold chapterRamificationIndex
        exact Ideal.ramificationIdx_eq mA mB
      _ = n := hlen
  change J = mB ^ e
  rw [hn, ← hen]

/-- The residue degree is the finite-dimensional degree of `l/k`. -/
theorem residue_degree_is_residue_field_finrank
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring] :
    chapterResidueDegree vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) =
      Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) := by
  unfold chapterResidueDegree
  exact Ideal.inertiaDeg_eq_of_isMaximal
    (IsLocalRing.maximalIdeal vK.valuationSubring)
    (IsLocalRing.maximalIdeal vL.valuationSubring)

/-- The residue-degree formula has no separability hypothesis. -/
theorem residue_degree_formula_without_separability
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [FiniteDimensional K L]
    [Module.Finite vK.valuationSubring vL.valuationSubring] :
    chapterResidueDegree vK.valuationSubring vL.valuationSubring
        (IsLocalRing.maximalIdeal vL.valuationSubring) =
      Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) := by
  exact residue_degree_is_residue_field_finrank vK vL

/-- A residue degree is not replaced by a count of embeddings without separability. -/
def chapter2ResidueDegreeUsesVectorSpaceDimension
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] (f : ℕ) : Prop :=
  f = Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
    (IsLocalRing.ResidueField vL.valuationSubring)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02
