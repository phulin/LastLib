import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section01TheLocalExtensionProblem

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01

noncomputable section

universe u

open scoped Polynomial TensorProduct WithZero

/-! # Book 2, Chapter 1, Section 1.2

This file records Theorem 1.1, the henselian-versus-complete distinction, and
the concrete Gaussian example at the prime `5`.
-/

/-! ### Existence, uniqueness, and branches -/

/-- The valuation-theoretic extension theorem, in valuation-subring form. -/
theorem chapter01_algebraic_extension_exists
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) :
    ∃ W : ValuationSubring L,
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ContractsTo
        vK.valuationSubring.toSubring W.toSubring := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_algebraic_valuation_extension_exists vK

/-- Adic completeness of the valuation ring implies henselianity of the field. -/
theorem chapter01_complete_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    HenselianLocalRing vK.valuationSubring := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.complete_valued_field_is_henselian vK hcomplete

/-- Henselianity, rather than completeness, is enough for uniqueness of an algebraic extension. -/
theorem chapter01_henselian_discrete_field_unique_extension
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    [HenselianLocalRing vK.valuationSubring] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L := by
  have hiff :=
    List.TFAE.out
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.henselian_uniqueness_criterion vK) 0 1
  have hall :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueExtensionToEveryAlgebraicField vK :=
    hiff.mp inferInstance
  exact hall L

/-- Theorem 1.1, in the heterogeneous value-group interface. -/
theorem chapter01_theorem_1_1
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L := by
  letI : HenselianLocalRing vK.valuationSubring :=
    chapter01_complete_field_is_henselian vK hcomplete
  exact chapter01_henselian_discrete_field_unique_extension vK

/-- A heterogeneous extension is discrete when its own value group is discrete. -/
def chapter01DiscreteHeterogeneousExtension
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    (W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension vK L) : Prop :=
  letI : LinearOrderedCommGroupWithZero W.valueGroup := W.orderedValueGroup
  Valuation.IsRankOneDiscrete W.valuation

/-- Finite algebraic extensions of a discrete field have discrete extension values. -/
theorem chapter01_finite_extension_value_group_is_discrete
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [FiniteDimensional K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    ∀ W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.HeterogeneousValuationExtension vK L,
      chapter01DiscreteHeterogeneousExtension vK W := by
  sorry

/-- The value-group quotient in a finite extension is finite. -/
theorem chapter01_finite_value_group_quotient_is_finite
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    (hext : chapter01SamePlace vK vL)
    (hΓ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK ≤
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL) :
    Finite
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL ⧸
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vK).subgroupOf
          (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ValueGroup vL)) := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_value_group_quotient_finite
    vK vL hext hΓ

/-- A discrete value group has a canonical ordered integer model. -/
theorem chapter01_discrete_value_group_can_be_normalized
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [Valuation.IsRankOneDiscrete v] :
    Nonempty
      (MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass v) ≃*o ℤᵐ⁰) := by
  exact ⟨Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v⟩

/-- The finite normalization is local over a henselian valuation ring. -/
theorem chapter01_henselian_integral_closure_is_local
    {A K L : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [HenselianLocalRing A]
    (hfinite : Module.Finite A (integralClosure A L)) :
    IsLocalRing (integralClosure A L) := by
  letI : Module.Finite A (integralClosure A L) := hfinite
  obtain ⟨data⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.henselian_finite_algebra_is_local_product
      A (integralClosure A L)
  letI : ∀ i, CommRing (data.factor i) := data.factor_ring
  letI : ∀ i, IsLocalRing (data.factor i) := data.factor_local
  obtain ⟨e⟩ := data.equivalence
  have hindex_nonempty : Nonempty data.index := by
    classical
    by_contra h
    letI : IsEmpty data.index := ⟨fun i => h ⟨i⟩⟩
    have h01 : e (0 : integralClosure A L) = e 1 := Subsingleton.elim _ _
    exact zero_ne_one (e.injective h01)
  have hindex_subsingleton : Subsingleton data.index := by
    classical
    constructor
    intro i j
    by_contra hij
    let p : ∀ k, data.factor k := fun k => if k = i then 1 else 0
    let q : ∀ k, data.factor k := fun k => if k = j then 1 else 0
    have hp : p ≠ 0 := by
      intro hp
      have hpi := congrFun hp i
      simpa [p] using hpi
    have hq : q ≠ 0 := by
      intro hq
      have hqj := congrFun hq j
      simpa [q] using hqj
    have hpq : p * q = 0 := by
      funext k
      by_cases hki : k = i
      · by_cases hkj : k = j
        · exact False.elim (hij (hki.symm.trans hkj))
        · have hkj' : ¬i = j := by
            simpa [hki] using hkj
          simp [p, q, hki, hkj']
      · simp [p, q, hki]
    let a : integralClosure A L := e.symm p
    let b : integralClosure A L := e.symm q
    have ha : a ≠ 0 := by
      intro ha
      apply hp
      have := congrArg e ha
      simpa [a] using this
    have hb : b ≠ 0 := by
      intro hb
      apply hq
      have := congrArg e hb
      simpa [b] using this
    have hab : a * b = 0 := by
      apply e.injective
      simp [a, b, hpq]
    exact (mul_eq_zero.mp hab).elim ha hb
  letI : Subsingleton data.index := hindex_subsingleton
  let ⟨i₀⟩ := hindex_nonempty
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  have hchoice :=
    IsLocalRing.isUnit_or_isUnit_one_sub_self ((e a) i₀)
  rcases hchoice with hunit | hunit
  · left
    have hprod : IsUnit (e a) := by
      apply (Pi.isUnit_iff).2
      intro i
      have hi : i = i₀ := Subsingleton.elim _ _
      rw [hi]
      exact hunit
    simpa using hprod.map e.symm
  · right
    have hprod : IsUnit (e (1 - a)) := by
      apply (Pi.isUnit_iff).2
      intro i
      have hi : i = i₀ := Subsingleton.elim _ _
      rw [hi]
      have heval : e (1 - a) i₀ = 1 - e a i₀ := by
        simp
      rw [heval]
      exact hunit
    simpa using hprod.map e.symm

/-- Maximal ideals above the base maximal ideal are the finite-extension branches. -/
theorem chapter01_henselian_branch_is_unique
    {A K L : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L]
    [IsScalarTower A K L] [HenselianLocalRing A]
    (hfinite : Module.Finite A (integralClosure A L)) :
    ∃! P : Ideal (integralClosure A L),
      P.IsMaximal ∧ P.LiesOver (IsLocalRing.maximalIdeal A) := by
  letI : IsLocalRing (integralClosure A L) :=
    chapter01_henselian_integral_closure_is_local (A := A) (K := K) (L := L) hfinite
  letI : FaithfulSMul A (integralClosure A L) :=
    (faithfulSMul_iff_algebraMap_injective A (integralClosure A L)).mpr
      (by
        intro x y hxy
        apply IsFractionRing.injective A K
        apply FaithfulSMul.algebraMap_injective K L
        simpa only [← IsScalarTower.algebraMap_apply A K L,
          IsScalarTower.algebraMap_apply A (integralClosure A L) L] using
          congrArg (algebraMap (integralClosure A L) L) hxy)
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral
      (R := A) (S := integralClosure A L) (IsLocalRing.maximalIdeal A)
  refine ⟨P, ⟨hPmax, hPover⟩, ?_⟩
  intro Q hQ
  exact (IsLocalRing.eq_maximalIdeal hQ.1).trans
    (IsLocalRing.eq_maximalIdeal hPmax).symm

/-! ### The nonhenselian `5`-adic Gaussian example -/

/-- Irreducibility supplies the field instance for Book 1's Gaussian presentation. -/
theorem chapter01_gaussian_polynomial_irreducible :
    Irreducible
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hnat :
        (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ).natDegree = 2 := by
      simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial] using
        (Polynomial.natDegree_X_pow_add_C (R := ℚ) (n := 2) (r := (1 : ℚ)))
    rw [hnat]
    norm_num
  · intro x hx
    have hx' : x ^ 2 + 1 = 0 := by
      simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
        Polynomial.IsRoot] using hx
    nlinarith [sq_nonneg x]

noncomputable instance chapter01GaussianPolynomialIrreducible :
    Fact (Irreducible
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℚ)) :=
  ⟨chapter01_gaussian_polynomial_irreducible⟩

/-- The normalized `5`-adic valuation on the rational field. -/
abbrev chapter01FiveAdicValuation [Fact (Nat.Prime 5)] : Valuation ℚ ℤᵐ⁰ :=
  Rat.padicValuation 5

/-- Two inequivalent extension places, retaining Book 1's heterogeneous groups. -/
def chapter01TwoInequivalentValuationExtensions
    {K L ΓK : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero ΓK] (vK : Valuation K ΓK) : Prop :=
  ∃ w₁ w₂ :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Chapter09ValuationExtension (L := L) vK,
    ¬ LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.Chapter09ValuationExtensionEquivalent
      (L := L) vK w₁ w₂

/-- `X² + 1` has two distinct roots modulo `5`. -/
theorem chapter01_gaussian_mod_five_has_two_distinct_roots
    [Fact (Nat.Prime 5)] :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11SimpleResidueRoots (ZMod 5)
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial (ZMod 5)) := by
  simpa using
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_gaussian_odd_prime_one_mod_four_has_two_roots
      5 (by decide) (by decide))

/-- The two residue roots lift to two distinct linear factors over `ℚ₅`. -/
theorem chapter01_gaussian_polynomial_splits_over_five_adics
    [Fact (Nat.Prime 5)] :
    ∃ a b : ℚ_[5], a ≠ b ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial (ℚ_[5]) =
        (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) := by
  have hderiv :
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).derivative.aeval
          (2 : ℤ_[5]) = (4 : ℤ_[5]) := by
    simp [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      Polynomial.aeval_def]
  have hval :
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).aeval
          (2 : ℤ_[5]) = (5 : ℤ_[5]) := by
    norm_num [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      Polynomial.aeval_def]
  have hnorm :
      ‖(LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).aeval
          (2 : ℤ_[5])‖ <
        ‖(LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ).derivative.aeval
          (2 : ℤ_[5])‖ ^ 2 := by
    rw [hval, hderiv]
    have hfour : ‖(4 : ℤ_[5])‖ = 1 := by
      exact (PadicInt.norm_intCast_eq_one_iff).2 (by norm_num)
    change ‖(5 : ℤ_[5])‖ < ‖(4 : ℤ_[5])‖ ^ 2
    rw [hfour]
    simpa using
      (PadicInt.norm_intCast_lt_one_iff (p := 5) (z := (5 : ℤ))).2 (by norm_num)
  obtain ⟨z, hz, _, _, _⟩ :=
    hensels_lemma (p := 5)
      (F := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial ℤ)
      (a := (2 : ℤ_[5])) hnorm
  let u : ℚ_[5] := z
  have hu : u ^ 2 = -1 := by
    have hz' := congrArg (fun x : ℤ_[5] => (x : ℚ_[5])) hz
    have hz'' : u ^ 2 + 1 = 0 := by
      simpa [u,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
        Polynomial.aeval_def] using hz'
    exact eq_neg_of_add_eq_zero_left hz''
  have hu0 : u ≠ 0 := by
    intro hu0
    rw [hu0] at hu
    norm_num at hu
  let g : ℚ_[5][X] := Polynomial.X - Polynomial.C u
  let h : ℚ_[5][X] := Polynomial.X - Polynomial.C (-u)
  have hfactor :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial
          (ℚ_[5]) = g * h := by
    have hcalc : (Polynomial.X : ℚ_[5][X]) ^ 2 + 1 =
        (Polynomial.X - Polynomial.C u) * (Polynomial.X + Polynomial.C u) := by
      have hcu : (Polynomial.C u : ℚ_[5][X]) ^ 2 = -(1 : ℚ_[5][X]) := by
        rw [← Polynomial.C_pow, hu]
        simp
      calc
        Polynomial.X ^ 2 + 1 = Polynomial.X ^ 2 - (Polynomial.C u) ^ 2 := by
          rw [hcu]
          ring
        _ = (Polynomial.X - Polynomial.C u) * (Polynomial.X + Polynomial.C u) := by
          rw [sq_sub_sq]
          ring
    simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianPolynomial,
      g, h] using hcalc
  have hcop_elem : IsCoprime g h := by
    have h2u0 : (2 : ℚ_[5]) * u ≠ 0 := mul_ne_zero (by norm_num) hu0
    have hC2 : (Polynomial.C (2 : ℚ_[5]) : ℚ_[5][X]) = 2 := by
      change Polynomial.C ((2 : ℕ) : ℚ_[5]) = ((2 : ℕ) : ℚ_[5][X])
      exact Polynomial.C_eq_natCast 2
    refine ⟨-Polynomial.C ((2 * u)⁻¹), Polynomial.C ((2 * u)⁻¹), ?_⟩
    calc
      -Polynomial.C ((2 * u)⁻¹) * g + Polynomial.C ((2 * u)⁻¹) * h =
          Polynomial.C ((2 * u)⁻¹) * Polynomial.C (2 * u) := by
            simp [g, h, sub_eq_add_neg, map_neg]
            ring_nf
            rw [hC2]
      _ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h2u0]
        simp
  refine ⟨u, -u, ?_, ?_⟩
  · intro h
    have htwo : (2 : ℚ_[5]) * u = 0 := by
      calc
        (2 : ℚ_[5]) * u = u + u := by rw [two_mul]
        _ = u + (-u) := congrArg (fun z => u + z) h
        _ = 0 := add_neg_cancel u
    rcases mul_eq_zero.mp htwo with h2 | hu'
    · norm_num at h2
    · exact hu0 hu'
  · simpa [g, h] using hfactor

/-- The rational `5`-adic field is nonhenselian. -/
theorem chapter01_rationals_five_adic_are_not_henselian
    [Fact (Nat.Prime 5)] :
    ¬ HenselianLocalRing
      (chapter01FiveAdicValuation.valuationSubring) := by
  intro hH
  letI : HenselianLocalRing chapter01FiveAdicValuation.valuationSubring := hH
  let f : chapter01FiveAdicValuation.valuationSubring[X] := Polynomial.X ^ 2 + 1
  have hf : f.Monic := by
    simpa [f] using
      (Polynomial.monic_X_pow_add_C (R := chapter01FiveAdicValuation.valuationSubring)
        (1 : chapter01FiveAdicValuation.valuationSubring) (n := 2) (by norm_num))
  have h2 : (2 : ℚ) ∈ chapter01FiveAdicValuation.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]
    exact (Rat.padicValuation_le_one_iff).2 (by norm_num)
  let a₀ : chapter01FiveAdicValuation.valuationSubring := ⟨2, h2⟩
  have hf_a₀ : f.eval a₀ ∈ IsLocalRing.maximalIdeal
      chapter01FiveAdicValuation.valuationSubring := by
    rw [Valuation.mem_maximalIdeal_iff]
    have hval : ((f.eval a₀ : chapter01FiveAdicValuation.valuationSubring) : ℚ) = 5 := by
      norm_num [f, a₀]
    rw [hval]
    change Rat.padicValuation 5 (5 : ℚ) < 1
    have hfive : (5 : ℚ) = ((5 : ℕ) : ℚ) := by norm_num
    rw [hfive, Rat.padicValuation_self, WithZero.exp_neg]
    exact inv_lt_one_of_one_lt₀ (by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num)
  have h4 : (4 : ℚ) ∈ chapter01FiveAdicValuation.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]
    exact (Rat.padicValuation_le_one_iff).2 (by norm_num)
  have h4inv : ((4 : ℚ)⁻¹) ∈ chapter01FiveAdicValuation.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]
    exact (Rat.padicValuation_le_one_iff).2 (by norm_num)
  have hunit4 : IsUnit
      (⟨4, h4⟩ : chapter01FiveAdicValuation.valuationSubring) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨⟨(4 : ℚ)⁻¹, h4inv⟩, ?_⟩
    exact Subtype.ext (by norm_num)
  have hderiv : f.derivative.eval a₀ =
      (⟨4, h4⟩ : chapter01FiveAdicValuation.valuationSubring) := by
    apply Subtype.ext
    simp [f, a₀] <;> norm_num
  obtain ⟨a, ha, _⟩ := HenselianLocalRing.is_henselian f hf a₀ hf_a₀ (by
    rw [hderiv]
    exact hunit4)
  have ha' : (a : ℚ) ^ 2 + 1 = 0 := by
    change f.eval a = 0 at ha
    have ha'' := congrArg (fun z : chapter01FiveAdicValuation.valuationSubring => (z : ℚ)) ha
    simpa [f] using ha''
  nlinarith [sq_nonneg (a : ℚ)]

/-- `ℚ(i)` has two inequivalent extensions of the rational `5`-adic place. -/
theorem chapter01_gaussian_has_two_five_adic_extensions
    [Fact (Nat.Prime 5)] :
    chapter01TwoInequivalentValuationExtensions
      (L := LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField)
      (Rat.padicValuation 5) := by
  sorry

/-- Completion at `5` separates the Gaussian tensor product into two local factors. -/
theorem chapter01_gaussian_completed_tensor_product_at_five
    [Fact (Nat.Prime 5)] :
    Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField ⊗[ℚ] ℚ_[5] ≃+*
        ℚ_[5] × ℚ_[5]) := by
  simpa [LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11TensorSplit] using
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_gaussian_completed_tensor_at_five

/-- Each factor in the completed split tensor product is a local field. -/
theorem chapter01_gaussian_completed_factors_are_fields
    [Fact (Nat.Prime 5)] :
    Nonempty
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField ⊗[ℚ] ℚ_[5] ≃+*
        ℚ_[5] × ℚ_[5]) ∧
      IsField ℚ_[5] := by
  exact ⟨chapter01_gaussian_completed_tensor_product_at_five, Field.toIsField _⟩

/-- The split completed tensor product is not itself a field. -/
theorem chapter01_gaussian_completed_tensor_product_not_field
    [Fact (Nat.Prime 5)] :
    ¬ IsField
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11GaussianField ⊗[ℚ] ℚ_[5]) := by
  intro hfield
  obtain ⟨e⟩ := chapter01_gaussian_completed_tensor_product_at_five
  have hprod : IsField (ℚ_[5] × ℚ_[5]) :=
    MulEquiv.isField hfield e.symm.toMulEquiv
  have hleft : ((1, 0) : ℚ_[5] × ℚ_[5]) ≠ 0 := by
    intro h
    have := congrArg Prod.fst h
    simp at this
  obtain ⟨b, hb⟩ := hprod.mul_inv_cancel hleft
  have hsecond := congrArg Prod.snd hb
  simp at hsecond

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
