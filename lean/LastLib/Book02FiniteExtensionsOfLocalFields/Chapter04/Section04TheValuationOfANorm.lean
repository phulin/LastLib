import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.Section07NormsAndIdeals
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section06TheValuationRingInAFiniteCompleteExtension

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators Polynomial WithTop

/-! ## 4.4. The valuation of a norm -/

/-
The norm expression for an extending real absolute value.  This is the
canonical `Real.rpow` form of the formula from Book 1 §1.4.
-/
noncomputable def chapter04NormInducedAbsoluteValue
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (abvK : AbsoluteValue K ℝ) (x : L) : ℝ :=
  Real.rpow (abvK (Algebra.norm K x))
    (1 / (Module.finrank K L : ℝ))

/- Theorem 4.1: normalized valuations of a norm (§4.4).  The restriction
relation is recorded with its ramification factor, rather than as literal
equality of normalized valuations. -/
/- This declaration is stated for a generic pair of chosen discrete
valuations, so it records the unique-branch and degree data explicitly.  In
the book's complete discretely valued setting, uniqueness follows from
henselianity and `[L : K] = e * f` follows from finite freeness of the
extension valuation ring. -/
theorem chapter04_norm_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {vK : AddValuation K (WithTop ℤ)}
    {vL : AddValuation L (WithTop ℤ)} (e f : ℕ)
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hext : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hrestrict : ∀ y : K,
      vL (algebraMap K L y) = (e : WithTop ℤ) * vK y)
    (hf : f = LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
      vK vL hext)
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) → vL.IsEquiv w)
    (hdegree : Module.finrank K L = e * f) (x : L) (hx : x ≠ 0) :
    vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_single_branch_norm_valuation_formula
    K L e f hext hrestrict hf hunique hdegree x hx

/- A cross-multiplied form of `v_L(x)/e = v_K(Nx)/[L:K]` (§4.4). -/
theorem chapter04_norm_valuation_cross_multiplication
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {vK : AddValuation K (WithTop ℤ)}
    {vL : AddValuation L (WithTop ℤ)} (e f : ℕ)
    (hformula : ∀ x : L, x ≠ 0 →
      vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x)
    (hdegree : Module.finrank K L = e * f) (x : L) (hx : x ≠ 0) :
    (e : WithTop ℤ) * vK (Algebra.norm K x) =
      (Module.finrank K L : WithTop ℤ) * vL x := by
  calc
    (e : WithTop ℤ) * vK (Algebra.norm K x) =
        (e : WithTop ℤ) * ((f : WithTop ℤ) * vL x) := by
      rw [hformula x hx]
    _ = ((e * f : ℕ) : WithTop ℤ) * vL x := by
      change (↑(e : ℤ) : WithTop ℤ) *
          (↑(f : ℤ) * vL x) =
        (↑((e : ℤ) * (f : ℤ)) : WithTop ℤ) * vL x
      rw [← mul_assoc, WithTop.coe_mul]
    _ = (Module.finrank K L : WithTop ℤ) * vL x := by
      rw [hdegree]

/- The length computation behind Theorem 4.1 (§4.4). -/
theorem chapter04_principal_quotient_length
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B]
    [IsDiscreteValuationRing B]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal A)] (x : B) (r f : ℕ)
    (_hx0 : x ≠ 0)
    (hx : LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11LocalLengthValue B P x = r)
    (hf : P.inertiaDeg A = f) :
    (Module.length A
      (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) x})).toNat = r * f := by
  let S := Localization.AtPrime P
  let M := S ⧸ Ideal.span {algebraMap B S x}
  let _ := Localization.AtPrime.algebraOfLiesOver
    (IsLocalRing.maximalIdeal A) P
  let _ : IsLocalHom (algebraMap A S) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A S)).out 4 0).mp
    change (IsLocalRing.maximalIdeal S).under A = IsLocalRing.maximalIdeal A
    rw [← Ideal.under_under (B := B), Localization.AtPrime.under_maximalIdeal]
    exact (P.over_def (IsLocalRing.maximalIdeal A)).symm
  have hres : Module.length (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField S) = f := by
    let e : (B ⧸ P) ≃+* (IsLocalRing.ResidueField S) :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal P S
    let eA : (A ⧸ IsLocalRing.maximalIdeal A) ≃+*
        (IsLocalRing.ResidueField A) := RingEquiv.refl _
    let _ : Module.Finite (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) := inferInstance
    let _ : Module.Finite (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) := by
      apply Module.Finite.of_equiv_equiv eA e
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun a => rfl)
    have hfin : Module.finrank (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ P) =
        Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) := by
      apply Algebra.finrank_eq_of_equiv_equiv eA e
      apply RingHom.ext
      intro a
      exact Quotient.inductionOn' a (fun a => rfl)
    rw [Module.length_eq_finrank, hfin.symm,
      (Ideal.inertiaDeg_eq_of_isMaximal
        (IsLocalRing.maximalIdeal A) P).symm, hf]
  have hlength : Module.length A M =
      Module.length S M * Module.length (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField S) :=
    IsLocalRing.length_restrictScalars A S M
  calc
    (Module.length A M).toNat =
        (Module.length S M * Module.length (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField S)).toNat := by rw [hlength]
    _ = (Module.length S M).toNat *
        (Module.length (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField S)).toNat := by simp
    _ = r * f := by
      rw [show (Module.length S M).toNat = r by
        simpa [M, S,
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11LocalLengthValue] using hx,
        hres]
      simp

/- The valuation formula determines the norm-induced absolute value (§4.4). -/
theorem chapter04_norm_absolute_value_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (abvK : AbsoluteValue K ℝ)
    (abvL : AbsoluteValue L ℝ)
    (_hext : ∀ y : K, abvL (algebraMap K L y) = abvK y)
    (hpower : ∀ x : L,
      abvL x ^ Module.finrank K L = abvK (Algebra.norm K x)) :
    ∀ x : L, abvL x =
      chapter04NormInducedAbsoluteValue K L abvK x := by
  intro x
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  calc
    abvL x = (abvL x ^ Module.finrank K L) ^
        ((Module.finrank K L : ℝ)⁻¹) := by
      symm
      exact Real.pow_rpow_inv_natCast (abvL.nonneg x) hn
    _ = (abvK (Algebra.norm K x)) ^
        ((Module.finrank K L : ℝ)⁻¹) := by rw [hpower x]
    _ = chapter04NormInducedAbsoluteValue K L abvK x := by
      simp [chapter04NormInducedAbsoluteValue, one_div]

/- In the totally ramified case, a uniformizer has norm of value one (§4.4). -/
theorem chapter04_totally_ramified_uniformizer_norm_value
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {vK : AddValuation K (WithTop ℤ)}
    {vL : AddValuation L (WithTop ℤ)} (f : ℕ)
    (hformula : ∀ x : L, x ≠ 0 →
      vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x)
    (hf : f = 1) (πL : L) (hπL : πL ≠ 0)
    (hval : vL πL = 1) :
    vK (Algebra.norm K πL) = 1 := by
  rw [hformula πL hπL, hf, hval]
  simp

/- The unit-times-uniformizer form of the totally ramified example (§4.4). -/
theorem chapter04_totally_ramified_uniformizer_norm_is_unit_times_uniformizer
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {vK : AddValuation K (WithTop ℤ)}
    {vL : AddValuation L (WithTop ℤ)} (f : ℕ)
    (hformula : ∀ x : L, x ≠ 0 →
      vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x)
    (hf : f = 1) (πK : K) (πL : L)
    (hπK : vK πK = 1) (hπL : vL πL = 1) :
    ∃ u : K, vK u = 0 ∧
      Algebra.norm K πL = u * πK := by
  have hπK0 : πK ≠ 0 := by
    intro hzero
    subst πK
    simp at hπK
  have hπL0 : πL ≠ 0 := by
    intro hzero
    subst πL
    simp at hπL
  have hnorm := chapter04_totally_ramified_uniformizer_norm_value
    K L f hformula hf πL hπL0 hπL
  refine ⟨Algebra.norm K πL / πK, ?_, ?_⟩
  · rw [AddValuation.map_div, hnorm, hπK]
    norm_num
  · field_simp [hπK0]

/- In the unramified case, the common uniformizer has norm of value `f` (§4.4). -/
theorem chapter04_unramified_common_uniformizer_norm_value
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {vK : AddValuation K (WithTop ℤ)}
    {vL : AddValuation L (WithTop ℤ)} (f : ℕ)
    (hformula : ∀ x : L, x ≠ 0 →
      vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x)
    (πK : K) (hπK : πK ≠ 0) (hcommon : vL (algebraMap K L πK) = 1) :
    vK (Algebra.norm K (algebraMap K L πK)) = (f : WithTop ℤ) := by
  have hmap : algebraMap K L πK ≠ 0 := by
    intro h
    apply hπK
    exact (FaithfulSMul.algebraMap_injective K L) (by simpa using h)
  rw [hformula (algebraMap K L πK) hmap, hcommon]
  simp

/- A common uniformizer in an unramified extension has norm a unit times its
`f`th power (§4.4). -/
theorem chapter04_unramified_common_uniformizer_norm_is_unit_times_power
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (f : ℕ) (πK : K) (hdegree : Module.finrank K L = f)
    (_hπK : πK ≠ 0) :
    ∃ u : Kˣ,
      Algebra.norm K (algebraMap K L πK) = (u : K) * πK ^ f := by
  refine ⟨1, ?_⟩
  simp [hdegree]

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
