import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section07MinimalPolynomialsAndMultiplicities

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open Ideal IsLocalRing
open scoped BigOperators Polynomial nonZeroDivisors

/-! ## 4.8. Norms of ideals and determinants -/

/- The fractional ideal represented by the integer power `m^n`. -/
noncomputable def chapter04FractionalIdealPower
    (R K : Type*) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (m : Ideal R) (n : ℤ) :
    FractionalIdeal R⁰ K :=
  if h : 0 ≤ n then
    ((m ^ n.toNat : Ideal R) : FractionalIdeal R⁰ K)
  else
    (((m ^ (-n).toNat : Ideal R) : FractionalIdeal R⁰ K)⁻¹)

/- The ideal norm of a DVR power, as used in §4.8. -/
noncomputable def chapter04IdealNormPower
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (mK : Ideal A) (f : ℕ) (n : ℤ) : FractionalIdeal A⁰ K :=
  chapter04FractionalIdealPower A K mK ((f : ℤ) * n)

/- Every nonzero fractional ideal of a DVR is a unique maximal-ideal power
with an integer exponent (§4.8). -/
theorem chapter04_nonzero_fractional_ideal_is_maximal_power
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    ∃! n : ℤ,
      I = chapter04FractionalIdealPower A K (IsLocalRing.maximalIdeal A) n := by
  sorry

/- Exponents add under the ideal norm (§4.8). -/
theorem chapter04_ideal_norm_power_is_multiplicative
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (mK : Ideal A) (f : ℕ) (n₁ n₂ : ℤ) :
    chapter04IdealNormPower A K mK f (n₁ + n₂) =
      chapter04IdealNormPower A K mK f n₁ *
        chapter04IdealNormPower A K mK f n₂ := by
  sorry

/- A relative ideal norm is defined on a power decomposition of a fractional
ideal; the decomposition theorem above supplies this input in a DVR. -/
noncomputable def chapter04IdealNorm
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Field K] [Field L] [Algebra A K] [Algebra B L]
    [IsFractionRing A K] [IsFractionRing B L]
    (mA : Ideal A) (mB : Ideal B) (f : ℕ)
    (I : FractionalIdeal B⁰ L)
    (hI : ∃ n : ℤ,
      I = chapter04FractionalIdealPower B L mB n) :
    FractionalIdeal A⁰ K :=
  chapter04IdealNormPower A K mA f (Classical.choose hI)

/- Principal ideals have principal norm given by the field norm (§4.8). -/
theorem chapter04_ideal_norm_of_principal
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    (mA : Ideal A) (mB : Ideal B) (f : ℕ) (x : B)
    (hI : ∃ n : ℤ,
      FractionalIdeal.spanSingleton B⁰ (algebraMap B L x) =
        chapter04FractionalIdealPower B L mB n) :
    chapter04IdealNorm A B K L mA mB f
        (FractionalIdeal.spanSingleton B⁰ (algebraMap B L x)) hI =
      FractionalIdeal.spanSingleton A⁰
        (Algebra.norm K (algebraMap B L x)) := by
  sorry

/- The norm of the first branch power is `m_K^f` (§4.8). -/
theorem chapter04_ideal_norm_of_one_power
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (mK : Ideal A) (f : ℕ) :
    chapter04IdealNormPower A K mK f 1 =
      chapter04FractionalIdealPower A K mK (f : ℤ) := by
  sorry

/- The ideal norm of a maximal-ideal power is the residue-degree power
formula (§4.8). -/
theorem chapter04_ideal_norm_of_maximal_power
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [Field K] [Field L] [Algebra A K] [Algebra B L]
    [IsFractionRing A K] [IsFractionRing B L]
    (mA : Ideal A) (mB : Ideal B) (f : ℕ) (n : ℤ)
    (I : FractionalIdeal B⁰ L)
    (hI : I = chapter04FractionalIdealPower B L mB n) :
    chapter04IdealNorm A B K L mA mB f I ⟨n, hI⟩ =
      chapter04FractionalIdealPower A K mA ((f : ℤ) * n) := by
  sorry

/- Extending the base maximal ideal gives the degree power (§4.8).  The
decomposition hypothesis makes the extension ideal and its ramification
exponent explicit. -/
theorem chapter04_norm_of_extended_maximal_ideal
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [IsDedekindDomain B]
    [Field K] [Field L] [Algebra A B] [Algebra A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L]
    [IsScalarTower A K L] [IsFractionRing A K] [IsFractionRing B L]
    [FiniteDimensional K L] [Module.Finite A B] [Module.Free A B]
    [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (mA : Ideal A) (mB : Ideal B) (e f : ℕ)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B)
    (hdecomp :
      ((Ideal.map (algebraMap A B) mA : Ideal B) : FractionalIdeal B⁰ L) =
        chapter04FractionalIdealPower B L mB (e : ℤ))
    (hdegree : Module.finrank K L = e * f) :
    chapter04IdealNorm A B K L mA mB f
        ((Ideal.map (algebraMap A B) mA : Ideal B) : FractionalIdeal B⁰ L)
        ⟨e, hdecomp⟩ =
      chapter04FractionalIdealPower A K mA (Module.finrank K L : ℤ) := by
  sorry

/- The determinant of multiplication by a base element is the expected
power (§4.8). -/
theorem chapter04_norm_of_base_element_is_degree_power
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (πK : K) :
    Algebra.norm K (algebraMap K L πK) = πK ^ Module.finrank K L := by
  sorry

/- The residue quotient has the cardinality of the residue field (§4.8). -/
theorem chapter04_residue_quotient_cardinality
    (B l : Type*) [CommRing B] [Field l] (m : Ideal B)
    [m.IsMaximal] (red : B →+* l)
    (hred : chapter04ResidueMap B l m red)
    [Fintype (B ⧸ m)] [Fintype l]
    (hequiv : Nonempty ((B ⧸ m) ≃+* l)) :
    Fintype.card (B ⧸ m) = Fintype.card l := by
  sorry

/- For a finite residue field, the `f`th maximal-ideal power has index
`|k|^f`, the numerical shadow used in §4.8. -/
theorem chapter04_dvr_power_quotient_cardinality
    (A k : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field k]
    (m : Ideal A) [m.IsMaximal] [Fintype k]
    [Fintype (A ⧸ m ^ 1)] (f : ℕ) [Fintype (A ⧸ m ^ f)]
    (hmax : m = IsLocalRing.maximalIdeal A) :
    Fintype.card (A ⧸ m ^ f) = Fintype.card k ^ f := by
  sorry

/- The residue degree, not the ramification index, controls the norm of an
individual maximal-ideal power (§4.8). -/
theorem chapter04_residue_degree_quotient_cardinality
    (A B k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [Field k] [Field l]
    (mA : Ideal A) (mB : Ideal B) (f : ℕ)
    [Fintype k] [Fintype l] [Fintype (A ⧸ mA)] [Fintype (A ⧸ mA ^ f)]
    [Fintype (B ⧸ mB)]
    (hA : Fintype.card (A ⧸ mA) = Fintype.card k)
    (hB : Fintype.card (B ⧸ mB) = Fintype.card l)
    (hf : Fintype.card l = Fintype.card k ^ f) :
    Fintype.card (B ⧸ mB) = Fintype.card k ^ f := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
