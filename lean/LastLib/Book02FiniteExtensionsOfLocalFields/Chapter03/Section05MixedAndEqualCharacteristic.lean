import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.LaurentSeries

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Polynomial
open scoped WithZero

open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

/-! ## 3.5. Mixed and equal characteristic -/

/-! The bridge below is local because the normalized additive valuation used in
this section takes values in `WithTop ℤ`, whereas Mathlib's extension theorems
expect the associated multiplicative valuation to carry its rank-one-discrete
instance explicitly. -/
private theorem chapter03_rank_one_discrete_of_add_valuation
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hdiscrete :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v) :
    Valuation.IsRankOneDiscrete v.toValuation := by
  let vk : Valuation K (Multiplicative (WithTop ℤ)ᵒᵈ) := v
  obtain ⟨π, hπ0, hπ, hv⟩ := hdiscrete
  have hone : ∀ z : ℕ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
    intro z
    induction z with
    | zero => simp
    | succ z ih =>
        rw [succ_nsmul, Nat.cast_succ, ih]
  have hnegcast : ∀ z : ℕ,
      (Int.negSucc z : WithTop ℤ) = -((z + 1 : ℕ) : WithTop ℤ) := by
    intro z
    simp [Int.negSucc_eq]
  have hpow : ∀ z : ℤ, v (π ^ z) = (z : WithTop ℤ) := by
    intro z
    cases z with
    | ofNat z =>
        change v (π ^ (z : ℤ)) = (z : WithTop ℤ)
        rw [zpow_natCast, v.map_pow, hπ, hone]
    | negSucc z =>
        rw [zpow_negSucc, v.map_inv, v.map_pow, hπ]
        rw [hnegcast z, hone]
  have hvg : MonoidWithZeroHom.valueGroup (.ofClass vk) = ⊤ := by
    apply top_unique
    intro u _hu
    have hu0 :
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
      intro htop
      apply Units.ne_zero u
      change Multiplicative.ofAdd (OrderDual.toDual
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
        Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
      congr 1
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hu0
    apply MonoidWithZeroHom.mem_valueGroup
    refine ⟨π ^ n, ?_⟩
    change Multiplicative.ofAdd (OrderDual.toDual (v (π ^ n))) =
      (u : Multiplicative (WithTop ℤ)ᵒᵈ)
    rw [hpow n]
    exact congrArg (fun z : WithTop ℤ =>
      Multiplicative.ofAdd (OrderDual.toDual z)) hn
  let γ : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ :=
    Units.mk0 (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)))
      (by
        intro h
        have htop : (1 : WithTop ℤ) = ⊤ := congrArg (fun z =>
          OrderDual.ofDual (Multiplicative.toAdd z)) h
        exact (WithTop.coe_lt_top 1).ne htop)
  have honeD : ∀ z : ℕ,
      z • (OrderDual.toDual (1 : WithTop ℤ)) =
        OrderDual.toDual (z : WithTop ℤ) := by
    intro z
    exact congrArg OrderDual.toDual (hone z)
  have hγpow : ∀ n : ℤ,
      (γ ^ n : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ).val =
        Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ)) := by
    intro n
    cases n with
    | ofNat n =>
        simp [γ, zpow_natCast]
        change Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^ n =
          Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ))
        rw [← ofAdd_nsmul n (OrderDual.toDual (1 : WithTop ℤ))]
        congr 1
        exact honeD n
    | negSucc n =>
        simp [γ, zpow_negSucc]
        change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
            (n + 1))⁻¹ =
          Multiplicative.ofAdd (OrderDual.toDual
            (Int.negSucc n : WithTop ℤ))
        rw [hnegcast n]
        change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
            (n + 1))⁻¹ =
          Multiplicative.ofAdd
            (-(OrderDual.toDual ((n + 1 : ℕ) : WithTop ℤ)))
        rw [ofAdd_neg]
        rw [← ofAdd_nsmul (n + 1) (OrderDual.toDual (1 : WithTop ℤ))]
        congr 1
        exact honeD (n + 1)
  have hcyc : IsCyclic ((Multiplicative (WithTop ℤ)ᵒᵈ)ˣ) := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    refine ⟨γ, ?_⟩
    apply top_unique
    intro u _hu
    have hu0 :
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
      intro htop
      apply Units.ne_zero u
      change Multiplicative.ofAdd (OrderDual.toDual
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
        Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
      congr 1
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hu0
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    apply Units.ext
    rw [hγpow]
    exact congrArg (fun z : WithTop ℤ =>
      Multiplicative.ofAdd (OrderDual.toDual z)) hn
  let : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass vk)) := by
    rw [hvg]
    exact (Subgroup.topEquiv.isCyclic :
      IsCyclic (⊤ : Subgroup ((Multiplicative (WithTop ℤ)ᵒᵈ)ˣ)) ↔
        IsCyclic ((Multiplicative (WithTop ℤ)ᵒᵈ)ˣ)).mpr hcyc
  let : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass vk)) := by
    rw [hvg]
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    refine ⟨γ, Subgroup.mem_top γ, ?_⟩
    intro hγ
    have hval := congrArg Units.val hγ
    simp [γ] at hval
  exact Valuation.IsRankOneDiscrete.mk' vk

private theorem chapter03_discrete_of_rank_one_add_valuation
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K) (hπ0 : π ≠ 0)
    (hπ : v π = 1) [Valuation.IsRankOneDiscrete v.toValuation] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v := by
  refine ⟨π, hπ0, hπ, ?_⟩
  intro x hx
  have hxv : v.toValuation x ≠ 0 := by
    exact (Valuation.ne_zero_iff v.toValuation).mpr hx
  have hfinite : v x ≠ ⊤ := by
    intro htop
    apply Units.ne_zero (Units.mk0 (v.toValuation x) hxv)
    change Multiplicative.ofAdd (OrderDual.toDual (v x)) =
      Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
    rw [htop]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
  exact ⟨n, hn.symm⟩

private theorem chapter03_additive_value_group_eq_top
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (hdiscrete :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v) :
    MonoidWithZeroHom.valueGroup (.ofClass v.toValuation) = ⊤ := by
  obtain ⟨π, hπ0, hπ, hv⟩ := hdiscrete
  have hone : ∀ z : ℕ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
    intro z
    induction z with
    | zero => simp
    | succ z ih =>
        rw [succ_nsmul, Nat.cast_succ, ih]
  have hnegcast : ∀ z : ℕ,
      (Int.negSucc z : WithTop ℤ) = -((z + 1 : ℕ) : WithTop ℤ) := by
    intro z
    simp [Int.negSucc_eq]
  have hpow : ∀ z : ℤ, v (π ^ z) = (z : WithTop ℤ) := by
    intro z
    cases z with
    | ofNat z =>
        change v (π ^ (z : ℤ)) = (z : WithTop ℤ)
        rw [zpow_natCast, v.map_pow, hπ, hone]
    | negSucc z =>
        rw [zpow_negSucc, v.map_inv, v.map_pow, hπ]
        rw [hnegcast z, hone]
  apply top_unique
  intro u _hu
  have hu0 :
      (OrderDual.ofDual (Multiplicative.toAdd
        (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
    intro htop
    apply Units.ne_zero u
    change Multiplicative.ofAdd (OrderDual.toDual
      (OrderDual.ofDual (Multiplicative.toAdd
        (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
      Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
    congr 1
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hu0
  apply MonoidWithZeroHom.mem_valueGroup
  refine ⟨π ^ n, ?_⟩
  change Multiplicative.ofAdd (OrderDual.toDual (v (π ^ n))) =
    (u : Multiplicative (WithTop ℤ)ᵒᵈ)
  rw [hpow n]
  exact congrArg (fun z : WithTop ℤ =>
    Multiplicative.ofAdd (OrderDual.toDual z)) hn

private theorem chapter03_additive_value_one_is_uniformizer
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K)
    (_hπ0 : π ≠ 0) (hπ : v π = 1)
    (hdiscrete :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation v)
    [Valuation.IsRankOneDiscrete v.toValuation] :
    v.toValuation.IsUniformizer
      (⟨π, (Valuation.mem_valuationSubring_iff v.toValuation π).mpr (by
        change Multiplicative.ofAdd (OrderDual.toDual (v π)) ≤ 1
        rw [hπ]
        change (0 : WithTop ℤ) ≤ 1
        norm_num)⟩ : v.toValuation.valuationSubring) := by
  have hvg := chapter03_additive_value_group_eq_top v hdiscrete
  let γ : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ :=
    Units.mk0 (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)))
      (by
        intro h
        have htop : (1 : WithTop ℤ) = ⊤ := congrArg (fun z =>
          OrderDual.ofDual (Multiplicative.toAdd z)) h
        exact (WithTop.coe_lt_top 1).ne htop)
  have hγ_lt : γ < 1 := by
    change Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) < 1
    change (0 : WithTop ℤ) < 1
    norm_num
  have hone : ∀ z : ℕ, z • (1 : WithTop ℤ) = (z : WithTop ℤ) := by
    intro z
    induction z with
    | zero => simp
    | succ z ih =>
        rw [succ_nsmul, Nat.cast_succ, ih]
  have hnegcast : ∀ z : ℕ,
      (Int.negSucc z : WithTop ℤ) = -((z + 1 : ℕ) : WithTop ℤ) := by
    intro z
    simp [Int.negSucc_eq]
  have hγpow : ∀ n : ℤ,
      (γ ^ n : (Multiplicative (WithTop ℤ)ᵒᵈ)ˣ).val =
        Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ)) := by
    intro n
    cases n with
    | ofNat n =>
        simp [γ, zpow_natCast]
        change Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^ n =
          Multiplicative.ofAdd (OrderDual.toDual (n : WithTop ℤ))
        rw [← ofAdd_nsmul n (OrderDual.toDual (1 : WithTop ℤ))]
        congr 1
        exact congrArg OrderDual.toDual (hone n)
    | negSucc n =>
        simp [γ, zpow_negSucc]
        change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
            (n + 1))⁻¹ =
          Multiplicative.ofAdd (OrderDual.toDual (Int.negSucc n : WithTop ℤ))
        rw [hnegcast n]
        change (Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) ^
            (n + 1))⁻¹ =
          Multiplicative.ofAdd
            (-(OrderDual.toDual ((n + 1 : ℕ) : WithTop ℤ)))
        rw [ofAdd_neg]
        rw [← ofAdd_nsmul (n + 1) (OrderDual.toDual (1 : WithTop ℤ))]
        congr 1
        exact congrArg OrderDual.toDual (hone (n + 1))
  have hγ_zpowers : Subgroup.zpowers γ =
      (⊤ : Subgroup ((Multiplicative (WithTop ℤ)ᵒᵈ)ˣ)) := by
    apply top_unique
    intro u _hu
    have hu0 :
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)) : WithTop ℤ) ≠ ⊤ := by
      intro htop
      apply Units.ne_zero u
      change Multiplicative.ofAdd (OrderDual.toDual
        (OrderDual.ofDual (Multiplicative.toAdd
          (u : Multiplicative (WithTop ℤ)ᵒᵈ)))) =
        Multiplicative.ofAdd (OrderDual.toDual (⊤ : WithTop ℤ))
      congr 1
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hu0
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨n, ?_⟩
    apply Units.ext
    rw [hγpow]
    exact congrArg (fun z : WithTop ℤ =>
      Multiplicative.ofAdd (OrderDual.toDual z)) hn
  have hγ_zpowers_v :
      Subgroup.zpowers γ =
        MonoidWithZeroHom.valueGroup (.ofClass v.toValuation) := by
    rw [hvg]
    exact hγ_zpowers
  have hgen :
      γ =
        LinearOrderedCommGroup.Subgroup.genLTOne
          (MonoidWithZeroHom.valueGroup (.ofClass v.toValuation)) := by
    exact LinearOrderedCommGroup.Subgroup.genLTOne_unique
      (MonoidWithZeroHom.valueGroup (.ofClass v.toValuation)) hγ_lt hγ_zpowers_v
  rw [Valuation.IsUniformizer.iff]
  change Multiplicative.ofAdd (OrderDual.toDual (v π)) = _
  rw [hπ]
  calc
    Multiplicative.ofAdd (OrderDual.toDual (1 : WithTop ℤ)) =
        γ := by rfl
    _ = LinearOrderedCommGroup.Subgroup.genLTOne
          (MonoidWithZeroHom.valueGroup (.ofClass v.toValuation)) :=
      congrArg Units.val hgen
    _ = Valuation.IsRankOneDiscrete.generator v.toValuation :=
      by
        exact congrArg Units.val
          (Valuation.IsRankOneDiscrete.valueGroup_genLTOne_eq_generator
            v.toValuation)

/-- The normalized mixed-characteristic profile over `ℚ_[p]`. -/
def chapter03MixedCharacteristicProfile
    (p : ℕ) (K : Type*) [Fact p.Prime] [Field K] [Algebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
    (vK : AddValuation K (WithTop ℤ)) (e f : ℕ) : Prop :=
  Module.finrank (ℚ_[p]) K = e * f ∧
    vK (algebraMap (ℚ_[p]) K (p : ℚ_[p])) = (e : WithTop ℤ)

@[simp] theorem chapter03MixedCharacteristicProfile_iff
    (p : ℕ) (K : Type*) [Fact p.Prime] [Field K] [Algebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
    (vK : AddValuation K (WithTop ℤ)) (e f : ℕ) :
    chapter03MixedCharacteristicProfile p K vK e f ↔
      Module.finrank (ℚ_[p]) K = e * f ∧
        vK (algebraMap (ℚ_[p]) K (p : ℚ_[p])) = (e : WithTop ℤ) := Iff.rfl

/-- In mixed characteristic, the degree and the normalized value of `p` are
the ramification and residue factors. -/
theorem chapter03_mixed_characteristic_degree_and_prime_value
    (p : ℕ) (K : Type*) [Fact p.Prime] [Field K] [Algebra (ℚ_[p]) K]
    [FiniteDimensional (ℚ_[p]) K]
    (vK : AddValuation K (WithTop ℤ))
    [(AddValuation.toValuation (Padic.addValuation (p := p))).HasExtension
      (AddValuation.toValuation vK)]
    [Valuation.IsRankOneDiscrete (AddValuation.toValuation vK)]
    (e f : ℕ)
    (he : chapterRamificationIndex
      (AddValuation.toValuation (Padic.addValuation (p := p))).valuationSubring
      (AddValuation.toValuation vK).valuationSubring
      (IsLocalRing.maximalIdeal (AddValuation.toValuation vK).valuationSubring) = e)
    (hf : chapterResidueDegree
      (AddValuation.toValuation (Padic.addValuation (p := p))).valuationSubring
      (AddValuation.toValuation vK).valuationSubring
      (IsLocalRing.maximalIdeal (AddValuation.toValuation vK).valuationSubring) = f)
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (Padic.addValuation (p := p)).valuationSubring)
      (Padic.addValuation (p := p)).valuationSubring)
    (hrestriction :
      ∀ x : ℚ_[p],
        vK (algebraMap (ℚ_[p]) K x) =
          e • Padic.addValuation x) :
    chapter03MixedCharacteristicProfile p K vK e f := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have hdiscrete :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation
        (Padic.addValuation (p := p)) := by
    refine ⟨(p : ℚ_[p]), hp0, ?_, ?_⟩
    · rw [Padic.addValuation.apply hp0, Padic.valuation_p]
      simp
    · intro x hx
      refine ⟨x.valuation, ?_⟩
      exact Padic.addValuation.apply hx
  have hbase : Valuation.IsRankOneDiscrete
      (AddValuation.toValuation (Padic.addValuation (p := p))) :=
    chapter03_rank_one_discrete_of_add_valuation
      (Padic.addValuation (p := p)) hdiscrete
  unfold chapter03MixedCharacteristicProfile
  constructor
  · have hfund :=
      @LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
        (ℚ_[p]) K (Multiplicative (WithTop ℤ)ᵒᵈ) _ _ _ _
        (AddValuation.toValuation (Padic.addValuation (p := p)))
        (AddValuation.toValuation vK) inferInstance hbase inferInstance inferInstance hcomplete
    simpa only [he, hf] using hfund
  · have hp := hrestriction (p : ℚ_[p])
    rw [Padic.addValuation.apply hp0, Padic.valuation_p] at hp
    simpa using hp

/-- A finite field is perfect. -/
theorem chapter03_finite_residue_field_is_perfect
    (k : Type*) [Field k] [Fintype k] :
    PerfectField k := by
  infer_instance

/-- Every finite extension of a finite field is separable. -/
theorem chapter03_finite_residue_extensions_are_separable
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Fintype k] :
    Algebra.IsSeparable k l := by
  infer_instance

/-- The Laurent-series model for equal characteristic. -/
abbrev chapter03EqualCharacteristicModel (k : Type*) [Field k] :=
  LaurentSeries k

/-- A coefficient field is an injective residue-section compatible with the
chosen fraction field. -/
def chapter03HasCoefficientField
    (A k K : Type*) [CommRing A] [IsLocalRing A]
    [Field k] [Field K] [Algebra A K] [Algebra k K] : Prop :=
  ∃ s : k →+* A, Function.Injective s ∧
    ∃ e : A ⧸ IsLocalRing.maximalIdeal A ≃+* k,
      ((e.toRingHom.comp
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).comp s =
        RingHom.id k) ∧
      (∀ a : k, algebraMap k K a = algebraMap A K (s a))

/-- The distinguished parameter in the Laurent-series model. -/
def chapter03EqualCharacteristicUniformizer
    (k : Type*) [Field k] : LaurentSeries k :=
  ((PowerSeries.X : PowerSeries k) : LaurentSeries k)

theorem chapter03_equal_characteristic_model_is_complete
    (k : Type*) [Field k] :
    CompleteSpace (chapter03EqualCharacteristicModel k) := by
  infer_instance

/-- The residue-case purely inseparable polynomial `X^p-a`. -/
def chapter03PurelyInseparableResiduePolynomial
    (k : Type*) [Ring k] (p : ℕ) (a : k) : k[X] :=
  ((X : k[X]) ^ p - (C a : k[X]) : k[X])

/-- The uniformizer-case purely inseparable polynomial `X^p-t`. -/
def chapter03PurelyInseparableUniformizerPolynomial
    (k : Type*) [Field k] (p : ℕ) :
    (LaurentSeries k)[X] :=
  X ^ p - C (chapter03EqualCharacteristicUniformizer k)

/-- A lift of residue coefficients into the chosen valuation ring. -/
structure Chapter03ResidueLift
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (vK : AddValuation K (WithTop ℤ)) where
  lift : k →+* vK.toValuation.valuationSubring
  residueEquiv :
    IsLocalRing.ResidueField vK.toValuation.valuationSubring ≃+* k
  section_compatibility :
    (residueEquiv.toRingHom.comp
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring))).comp lift =
      RingHom.id k
  algebra_compatibility :
    ∀ a : k, algebraMap k K a = (lift a : K)

/-- A purely inseparable residue root has `e=1` and `f=p`. -/
-- The general interface records the coefficient lift explicitly; in the
-- Laurent-series model this is supplied by the constant coefficient field.
theorem chapter03_purely_inseparable_residue_root_has_e_one
    (k K L : Type*) [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (p : ℕ) [ExpChar k p] (a : k) (α : L)
    (ha : ¬ ∃ b : k, b ^ p = a)
    (hroot :
      aeval α (chapter03PurelyInseparableResiduePolynomial k p a) = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    [FiniteDimensional K L] (hdegree : Module.finrank K L = p)
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (residueLift : Chapter03ResidueLift k K vK)
    (hnot_power_K : ¬ ∃ b : K, b ^ p = algebraMap k K a)
    [IsPurelyInseparable K L]
    [Valuation.HasExtension vK.toValuation vL.toValuation]
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring)
    (hrestriction :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01ValuationRestrictionScale
        vK vL 1) :
    ∃ data : Chapter03FiniteLocalExtensionData K L _
      vK.toValuation vL.toValuation,
      data.e = 1 ∧ data.f = p := by
  sorry

/-- A root of `X^p-t` is purely inseparable and totally ramified. -/
-- The `hvalue` hypothesis records the source's normalization `v(t)=1`.
theorem chapter03_purely_inseparable_uniformizer_root_has_e_p
    (k L : Type*) [Field k] [Field L]
    [Algebra (LaurentSeries k) L] [FiniteDimensional (LaurentSeries k) L]
    [IsPurelyInseparable (LaurentSeries k) L]
    (p : ℕ) [ExpChar k p] (α : L)
    (hroot :
      aeval α (chapter03PurelyInseparableUniformizerPolynomial k p) = 0)
    (hgen : Algebra.adjoin (LaurentSeries k) ({α} : Set L) = ⊤)
    (hdegree : Module.finrank (LaurentSeries k) L = p)
    (vK : AddValuation (LaurentSeries k) (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvalue : vK (chapter03EqualCharacteristicUniformizer k) = 1)
    [Valuation.HasExtension vK.toValuation vL.toValuation]
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring)
    (hrestriction :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01ValuationRestrictionScale
        vK vL p) :
    ∃ data : Chapter03FiniteLocalExtensionData (LaurentSeries k) L _
      vK.toValuation vL.toValuation,
      data.e = p ∧ data.f = 1 := by
  have hp_pos : 0 < p := by
    rw [← hdegree]
    exact Module.finrank_pos
  have ht0 : chapter03EqualCharacteristicUniformizer k ≠ 0 := by
    intro ht'
    have hv := hvalue
    rw [ht', vK.map_zero] at hv
    exact (WithTop.coe_lt_top (1 : ℤ)).ne hv.symm
  have hroot' :
      α ^ p - algebraMap (LaurentSeries k) L
        (chapter03EqualCharacteristicUniformizer k) = 0 := by
    simpa [chapter03PurelyInseparableUniformizerPolynomial,
      Polynomial.aeval_def] using hroot
  have hparameter :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10PowerParameterRelation
        (chapter03EqualCharacteristicUniformizer k) α p := by
    unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10PowerParameterRelation
    exact (sub_eq_zero.mp hroot').symm
  have hα0 : α ≠ 0 := by
    intro hα
    subst α
    have hmapt0 :
        (algebraMap (LaurentSeries k) L)
          (chapter03EqualCharacteristicUniformizer k) ≠ 0 :=
      (map_ne_zero_iff (algebraMap (LaurentSeries k) L)
        (FaithfulSMul.algebraMap_injective (LaurentSeries k) L)).2 ht0
    apply hmapt0
    simpa [hp_pos.ne'] using hroot'
  have hαtop : vL α ≠ ⊤ :=
    (AddValuation.ne_top_iff vL).mpr hα0
  have hpowval : vL (α ^ p) = (p : WithTop ℤ) := by
    rw [← hparameter]
    rw [hrestriction.2 _ ht0, hvalue]
    simp
  have hsmul : p • vL α = (p : WithTop ℤ) := by
    simpa only [vL.map_pow] using hpowval
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hαtop
  have hsmul' : p • (z : WithTop ℤ) = (p : WithTop ℤ) := by
    rw [← hz] at hsmul
    exact hsmul
  rw [← WithTop.coe_nsmul] at hsmul'
  have hz' : (p : ℤ) * z = p := by
    exact_mod_cast hsmul'
  have hp_int : (0 : ℤ) < p := by
    exact_mod_cast hp_pos
  have hz1 : z = 1 := by
    nlinarith [hz']
  have hαvalue : vL α = 1 := by
    calc
      vL α = (z : WithTop ℤ) := hz.symm
      _ = 1 := by rw [hz1]; norm_num
  have htA_mem :
      chapter03EqualCharacteristicUniformizer k ∈
        vK.toValuation.valuationSubring := by
    apply (Valuation.mem_valuationSubring_iff vK.toValuation _).mpr
    change Multiplicative.ofAdd
        (OrderDual.toDual (vK (chapter03EqualCharacteristicUniformizer k))) ≤ 1
    rw [hvalue]
    change (0 : WithTop ℤ) ≤ 1
    norm_num
  let tA : vK.toValuation.valuationSubring :=
    ⟨chapter03EqualCharacteristicUniformizer k, htA_mem⟩
  have hmem_pos (x : vK.toValuation.valuationSubring)
      (hx : x ∈ IsLocalRing.maximalIdeal vK.toValuation.valuationSubring) :
      (0 : WithTop ℤ) < vK (x : LaurentSeries k) := by
    have hxlt :=
      (Valuation.mem_maximalIdeal_iff
        (K := LaurentSeries k) vK.toValuation).mp hx
    change Multiplicative.ofAdd
        (OrderDual.toDual (vK (x : LaurentSeries k))) <
          Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) at hxlt
    rw [Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual] at hxlt
    exact hxlt
  have hspan :
      Ideal.span ({tA} : Set vK.toValuation.valuationSubring) =
        IsLocalRing.maximalIdeal vK.toValuation.valuationSubring := by
    apply le_antisymm
    · apply Ideal.span_le.2
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      change tA ∈ IsLocalRing.maximalIdeal vK.toValuation.valuationSubring
      rw [Valuation.mem_maximalIdeal_iff]
      change Multiplicative.ofAdd
          (OrderDual.toDual (vK (chapter03EqualCharacteristicUniformizer k))) <
          Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ))
      rw [Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual]
      rw [hvalue]
      norm_num
    · intro x hx
      by_cases hx0 : (x : LaurentSeries k) = 0
      · have hxzero : x = 0 := Subtype.ext hx0
        subst x
        exact Ideal.zero_mem _
      · have hxpos := hmem_pos x hx
        have hxtop : vK (x : LaurentSeries k) ≠ ⊤ :=
          (AddValuation.ne_top_iff vK).mpr hx0
        obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hxtop
        have hzpos : (0 : ℤ) < z := by
          rw [← hz] at hxpos
          exact_mod_cast hxpos
        have hzge : (1 : ℤ) ≤ z := by omega
        have hquot :
            (0 : WithTop ℤ) ≤
              vK ((x : LaurentSeries k) /
                chapter03EqualCharacteristicUniformizer k) := by
          rw [vK.map_div, ← hz, hvalue]
          change (0 : WithTop ℤ) ≤ (↑(z - 1) : WithTop ℤ)
          exact_mod_cast (sub_nonneg.mpr hzge)
        have hy_mem :
            (x : LaurentSeries k) /
                chapter03EqualCharacteristicUniformizer k ∈
              vK.toValuation.valuationSubring := by
          apply (Valuation.mem_valuationSubring_iff vK.toValuation _).mpr
          change Multiplicative.ofAdd
              (OrderDual.toDual
                (vK ((x : LaurentSeries k) /
                  chapter03EqualCharacteristicUniformizer k))) ≤ 1
          change (0 : WithTop ℤ) ≤
            vK ((x : LaurentSeries k) /
              chapter03EqualCharacteristicUniformizer k)
          exact hquot
        let y : vK.toValuation.valuationSubring :=
          ⟨(x : LaurentSeries k) /
              chapter03EqualCharacteristicUniformizer k, hy_mem⟩
        apply Ideal.mem_span_singleton.mpr
        refine ⟨y, ?_⟩
        apply Subtype.ext
        dsimp [y, tA]
        field_simp [ht0]
  let fA :
      (vK.toValuation.valuationSubring)[X] :=
    (Polynomial.X : (vK.toValuation.valuationSubring)[X]) ^ p -
      Polynomial.C tA
  have hfA :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt tA fA := by
    unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt
    refine ⟨?_, ?_, ?_, ?_, hspan⟩
    · simpa [fA] using
        (Polynomial.monic_X_pow_sub_C tA hp_pos.ne')
    · simp [fA, hp_pos]
    · intro i hi
      have hi' : i < p := by
        simpa [fA, Polynomial.natDegree_X_pow_sub_C] using hi
      by_cases hi0 : i = 0
      · subst i
        simp [fA, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          hp_pos.ne', eq_comm]
      · simp [fA, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
          Polynomial.coeff_C, Nat.ne_of_lt hi', hi0]
    · have htA0 : tA ≠ 0 := by
        intro hzero
        have hbot :
            IsLocalRing.maximalIdeal vK.toValuation.valuationSubring =
              (⊥ : Ideal vK.toValuation.valuationSubring) := by
          rw [← hspan, hzero]
          simp
        exact IsDiscreteValuationRing.not_a_field _ hbot
      have hirr : Irreducible tA :=
        IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
          tA htA0 hspan.symm
      intro hmem
      have hmem' : -tA ∈
          Ideal.span ({tA ^ 2} :
            Set vK.toValuation.valuationSubring) := by
        simpa [fA, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_sub,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
          hp_pos.ne'] using hmem
      have hdiv : tA ^ 2 ∣ -tA :=
        (Ideal.mem_span_singleton.mp hmem')
      rcases hdiv with ⟨c, hc⟩
      have hcancel : -1 = tA * c := by
        apply (mul_left_cancel₀ htA0)
        simpa [pow_two, mul_assoc] using hc
      have hunit : IsUnit tA := by
        apply isUnit_of_dvd_one
        refine ⟨-c, ?_⟩
        simpa [mul_neg] using congrArg Neg.neg hcancel
      exact hirr.not_isUnit hunit
  have hmap_tA :
      algebraMap vK.toValuation.valuationSubring L tA =
        algebraMap (LaurentSeries k) L
          (chapter03EqualCharacteristicUniformizer k) := by
    rw [IsScalarTower.algebraMap_apply vK.toValuation.valuationSubring
      (LaurentSeries k) L]
    rfl
  have hrootA : aeval α fA = 0 := by
    simpa [fA, Polynomial.aeval_def, hmap_tA] using hroot'
  have hdegreeA : fA.natDegree = p := by
    simp [fA]
  have hbase :
      (vK.toValuation.valuationSubring : Set (LaurentSeries k)) =
        Set.range (algebraMap vK.toValuation.valuationSubring
          (LaurentSeries k)) := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact a.property
  let _ : IsFractionRing vK.toValuation.valuationSubring
      (LaurentSeries k) :=
    (Valuation.valuationSubring.integers vK.toValuation).isFractionRing
  have hbaseIntegers :
      vK.toValuation.Integers vK.toValuation.valuationSubring := by
    refine
      { hom_inj := IsFractionRing.injective
            vK.toValuation.valuationSubring (LaurentSeries k)
        map_le_one := ?_
        exists_of_le_one := ?_ }
    · intro a
      exact (Valuation.mem_valuationSubring_iff vK.toValuation
        (a : LaurentSeries k)).mp a.property
    · intro x hx
      have hx' : x ∈ vK.toValuation.valuationSubring :=
        (Valuation.mem_valuationSubring_iff vK.toValuation x).mpr hx
      exact ⟨⟨x, hx'⟩, rfl⟩
  have hstruct :=
    finite_complete_extension_valuation_ring
      vK.toValuation vL.toValuation hcomplete
  have hupper :
      (vL.toValuation.valuationSubring : Set L) =
        (integralClosure vK.toValuation.valuationSubring L : Set L) :=
    hstruct.2.2.2.2
  have hend :=
    eisenstein_root_is_uniformizer_and_totally_ramified
      (A := vK.toValuation.valuationSubring)
      (K := LaurentSeries k) (L := L)
      (Γ := Multiplicative (WithTop ℤ)ᵒᵈ)
      vK.toValuation vL.toValuation tA fA α hfA hrootA hdegreeA hgen
      hbaseIntegers hbase hupper
  rcases hend with ⟨_huniform, he, hf, _hequiv, hfin⟩
  refine ⟨
    { e := p
      f := 1
      e_eq := he
      f_eq := hf
      degree_eq := ?_ }, rfl, rfl⟩
  simpa using hfin

/-- A nontrivial finite purely inseparable extension is neither separable nor
Galois. -/
theorem chapter03_purely_inseparable_extension_is_not_separable
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hdegree : Module.finrank K L ≠ 1) :
    ¬ Algebra.IsSeparable K L ∧ ¬ IsGalois K L := by
  constructor
  · intro hseparable
    have hbij : Function.Bijective (algebraMap K L) :=
      @IsPurelyInseparable.bijective_algebraMap_of_isSeparable K L
        _ _ _ _ _ _ _ hseparable
    apply hdegree
    exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr hbij
  · intro hgalois
    have hseparable : Algebra.IsSeparable K L := (isGalois_iff.mp hgalois).1
    have hbij : Function.Bijective (algebraMap K L) :=
      @IsPurelyInseparable.bijective_algebraMap_of_isSeparable K L
        _ _ _ _ _ _ _ hseparable
    apply hdegree
    exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr hbij

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
