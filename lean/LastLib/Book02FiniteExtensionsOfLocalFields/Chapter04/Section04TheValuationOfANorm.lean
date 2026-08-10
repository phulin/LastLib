import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section03Transitivity

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
theorem chapter04_norm_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {vK : AddValuation K (WithTop ℤ)}
    {vL : AddValuation L (WithTop ℤ)} (e f : ℕ)
    (hext : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (hrestrict : ∀ y : K,
      vL (algebraMap K L y) = (e : WithTop ℤ) * vK y)
    (hf : f = LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
      vK vL hext) (x : L) (hx : x ≠ 0) :
    vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x := by
  sorry

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
  sorry

/- The length computation behind Theorem 4.1 (§4.4). -/
theorem chapter04_principal_quotient_length
    (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsLocalRing A] [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (P : Ideal B) [P.IsPrime] [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal A)] (x : B) (r f : ℕ)
    (hx : LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11LocalLengthValue B P x = r)
    (hf : P.inertiaDeg A = f) :
    (Module.length A
      (Localization.AtPrime P ⧸
        Ideal.span {algebraMap B (Localization.AtPrime P) x})).toNat = r * f := by
  sorry

/- The valuation formula determines the norm-induced absolute value (§4.4). -/
theorem chapter04_norm_absolute_value_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (abvK : AbsoluteValue K ℝ)
    (abvL : AbsoluteValue L ℝ)
    (hext : ∀ y : K, abvL (algebraMap K L y) = abvK y)
    (hpower : ∀ x : L,
      abvL x ^ Module.finrank K L = abvK (Algebra.norm K x)) :
    ∀ x : L, abvL x =
      chapter04NormInducedAbsoluteValue K L abvK x := by
  sorry

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
  sorry

/- In the unramified case, the common uniformizer has norm of value `f` (§4.4). -/
theorem chapter04_unramified_common_uniformizer_norm_value
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {vK : AddValuation K (WithTop ℤ)}
    {vL : AddValuation L (WithTop ℤ)} (f : ℕ)
    (hformula : ∀ x : L, x ≠ 0 →
      vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x)
    (πK : K) (hπK : πK ≠ 0) (hcommon : vL (algebraMap K L πK) = 1) :
    vK (Algebra.norm K (algebraMap K L πK)) = (f : WithTop ℤ) := by
  sorry

/- A common uniformizer in an unramified extension has norm a unit times its
`f`th power (§4.4). -/
theorem chapter04_unramified_common_uniformizer_norm_is_unit_times_power
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (f : ℕ) (πK : K) (hdegree : Module.finrank K L = f)
    (hπK : πK ≠ 0) :
    ∃ u : Kˣ,
      Algebra.norm K (algebraMap K L πK) = (u : K) * πK ^ f := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
