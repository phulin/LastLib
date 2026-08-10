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
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπK : algebraMap A K π ≠ 0 := by
    simpa using hπ.ne_zero
  have hpow (n : ℤ) :
      chapter04FractionalIdealPower A K (IsLocalRing.maximalIdeal A) n =
        FractionalIdeal.spanSingleton A⁰ ((algebraMap A K π) ^ n) := by
    by_cases hn : 0 ≤ n
    · rw [chapter04FractionalIdealPower, dif_pos hn,
        hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
        FractionalIdeal.coeIdeal_span_singleton]
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn
      simp [hk]
    · rw [chapter04FractionalIdealPower, dif_neg hn,
        hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
        FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.spanSingleton_inv]
      have hnneg : 0 ≤ -n := by omega
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hnneg
      have hn' : n = -(k : ℤ) := by omega
      simp [hn']
  let g : K := Submodule.IsPrincipal.generator (I : Submodule A K)
  have hg : g ≠ 0 := by
    intro hg
    apply hI
    have hg' : Submodule.IsPrincipal.generator (I : Submodule A K) = 0 := by
      simpa [g] using hg
    rw [FractionalIdeal.eq_spanSingleton_of_principal I, hg',
      FractionalIdeal.spanSingleton_zero]
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hg
  have hgen : I = FractionalIdeal.spanSingleton A⁰
      ((algebraMap A K π) ^ n) := by
    have hgen0 : I = FractionalIdeal.spanSingleton A⁰ g := by
      simpa [g] using FractionalIdeal.eq_spanSingleton_of_principal I
    calc
      I = FractionalIdeal.spanSingleton A⁰ g := hgen0
      _ = FractionalIdeal.spanSingleton A⁰
          (u • (algebraMap A K π) ^ n) := by rw [hu]
      _ = FractionalIdeal.spanSingleton A⁰
          ((algebraMap A K π) ^ n) := by
        apply (FractionalIdeal.spanSingleton_eq_spanSingleton).2
        exact ⟨u⁻¹, by simp [smul_smul]⟩
  refine ⟨n, (hgen.trans (hpow n).symm), ?_⟩
  intro m hm
  have hpow' : FractionalIdeal.spanSingleton A⁰
        ((algebraMap A K π) ^ n) =
      FractionalIdeal.spanSingleton A⁰ ((algebraMap A K π) ^ m) := by
    simpa [hpow] using hgen.symm.trans hm
  obtain ⟨u', hu'⟩ :=
    (FractionalIdeal.spanSingleton_eq_spanSingleton).1 hpow'
  let v : IsDedekindDomain.HeightOneSpectrum A :=
    { asIdeal := IsLocalRing.maximalIdeal A
      isPrime := (IsLocalRing.maximalIdeal.isMaximal A).isPrime
      ne_bot := by
        rw [hπ.maximalIdeal_eq]
        exact fun h => hπ.ne_zero (Ideal.span_singleton_eq_bot.mp h) }
  let w : Valuation K (WithZero (Multiplicative ℤ)) := v.valuation K
  have hwπ : w (algebraMap A K π) = WithZero.exp (-1 : ℤ) := by
    dsimp [w]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      v.intValuation_singleton hπ.ne_zero hπ.maximalIdeal_eq]
    rfl
  have hnm : n = m := by
    have huval : w (algebraMap A K (u' : A)) = 1 := by
      dsimp [w]
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        v.intValuation_eq_one_iff.mpr]
      exact (IsLocalRing.notMem_maximalIdeal).2 u'.isUnit
    have hval := congrArg (fun z : K => w z) hu'
    have hpowval : (WithZero.exp (-1 : ℤ)) ^ n =
        (WithZero.exp (-1 : ℤ)) ^ m := by
      simpa [Units.smul_def, Algebra.smul_def, huval, hwπ, map_zpow] using hval
    have hnmz : (-(n : ℤ)) = -(m : ℤ) := by
      apply WithZero.exp_injective
      simpa [← WithZero.exp_zsmul] using hpowval
    exact neg_injective hnmz
  exact hnm.symm

/- Exponents add under the ideal norm (§4.8). -/
theorem chapter04_ideal_norm_power_is_multiplicative
    (A K : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (mK : Ideal A) (hmK : mK = IsLocalRing.maximalIdeal A)
    (f : ℕ) (n₁ n₂ : ℤ) :
    chapter04IdealNormPower A K mK f (n₁ + n₂) =
    chapter04IdealNormPower A K mK f n₁ *
        chapter04IdealNormPower A K mK f n₂ := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπK : algebraMap A K π ≠ 0 := by
    simpa using hπ.ne_zero
  have hpow (n : ℤ) :
      chapter04FractionalIdealPower A K (IsLocalRing.maximalIdeal A) n =
        FractionalIdeal.spanSingleton A⁰ ((algebraMap A K π) ^ n) := by
    by_cases hn : 0 ≤ n
    · rw [chapter04FractionalIdealPower, dif_pos hn,
        hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
        FractionalIdeal.coeIdeal_span_singleton]
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hn
      simp [hk]
    · rw [chapter04FractionalIdealPower, dif_neg hn,
        hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
        FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.spanSingleton_inv]
      have hnneg : 0 ≤ -n := by omega
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hnneg
      have hn' : n = -(k : ℤ) := by omega
      simp [hn']
  rw [hmK, chapter04IdealNormPower, chapter04IdealNormPower,
    chapter04IdealNormPower, hpow, hpow, hpow]
  rw [FractionalIdeal.spanSingleton_mul_spanSingleton, ← zpow_add₀ hπK]
  congr 1
  ring

/- A relative ideal norm is defined on a power decomposition of a fractional
ideal; the decomposition theorem above supplies this input in a DVR. -/
noncomputable def chapter04IdealNorm
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Algebra A K] [Algebra B L]
    [IsFractionRing A K] [IsFractionRing B L]
    (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B) (f : ℕ)
    (I : FractionalIdeal B⁰ L)
    (hI : ∃ n : ℤ,
      I = chapter04FractionalIdealPower B L mB n) :
    FractionalIdeal A⁰ K :=
  chapter04IdealNormPower A K mA f (Classical.choose hI)

/- Principal ideals have principal norm given by the field norm (§4.8). -/
theorem chapter04_ideal_norm_of_principal
    (A B K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B]
    [IsDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
    [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L]
    [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.Finite A B]
    [Module.Free A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]
    (x : B) :
    ((Ideal.relNorm A (Ideal.span ({x} : Set B)) : Ideal A) :
      FractionalIdeal A⁰ K) =
      FractionalIdeal.spanSingleton A⁰
        (Algebra.norm K (algebraMap B L x)) := by
  rw [Ideal.relNorm_singleton, FractionalIdeal.coeIdeal_span_singleton]
  rw [Algebra.algebraMap_intNorm (A := A) (B := B) (K := K) (L := L) x]

/- The norm of the first branch power is `m_K^f` (§4.8). -/
theorem chapter04_ideal_norm_of_one_power
    (A K : Type*) [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (mK : Ideal A) (f : ℕ) :
    chapter04IdealNormPower A K mK f 1 =
      chapter04FractionalIdealPower A K mK (f : ℤ) := by
  simp [chapter04IdealNormPower]

/- The ideal norm of a maximal-ideal power is the residue-degree power
formula (§4.8). -/
theorem chapter04_ideal_norm_of_maximal_power
    (A B K L : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Algebra A K] [Algebra B L]
    [IsFractionRing A K] [IsFractionRing B L]
    (mA : Ideal A) (mB : Ideal B)
    (hmA : mA = IsLocalRing.maximalIdeal A)
    (hmB : mB = IsLocalRing.maximalIdeal B) (f : ℕ) (n : ℤ)
    (I : FractionalIdeal B⁰ L)
    (hI : I = chapter04FractionalIdealPower B L mB n) :
    chapter04IdealNorm A B K L mA mB hmA hmB f I ⟨n, hI⟩ =
      chapter04FractionalIdealPower A K mA ((f : ℤ) * n) := by
  subst mB
  have hmB0 : IsLocalRing.maximalIdeal B ≠ (⊥ : Ideal B) := by
    exact IsDiscreteValuationRing.not_a_field B
  have hpow_nezero (q : ℤ) :
      chapter04FractionalIdealPower B L (IsLocalRing.maximalIdeal B) q ≠ 0 := by
    by_cases hq : 0 ≤ q
    · rw [chapter04FractionalIdealPower, dif_pos hq]
      exact FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ hmB0)
    · rw [chapter04FractionalIdealPower, dif_neg hq]
      exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ hmB0))
  have huniq := chapter04_nonzero_fractional_ideal_is_maximal_power B L I
    (by
      rw [hI]
      exact hpow_nezero n)
  let hI' : ∃ q : ℤ,
      I = chapter04FractionalIdealPower B L (IsLocalRing.maximalIdeal B) q :=
    ⟨n, hI⟩
  have hchoose : Classical.choose hI' = n := by
    exact huniq.unique (Classical.choose_spec hI') hI
  unfold chapter04IdealNorm
  rw [hchoose]
  rfl

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
    chapter04IdealNorm A B K L mA mB hmA hmB f
        ((Ideal.map (algebraMap A B) mA : Ideal B) : FractionalIdeal B⁰ L)
        ⟨e, hdecomp⟩ =
      chapter04FractionalIdealPower A K mA (Module.finrank K L : ℤ) := by
  subst mB
  have hmB0 : IsLocalRing.maximalIdeal B ≠ (⊥ : Ideal B) := by
    exact IsDiscreteValuationRing.not_a_field B
  have hpow_nezero (q : ℤ) :
      chapter04FractionalIdealPower B L (IsLocalRing.maximalIdeal B) q ≠ 0 := by
    by_cases hq : 0 ≤ q
    · rw [chapter04FractionalIdealPower, dif_pos hq]
      exact FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ hmB0)
    · rw [chapter04FractionalIdealPower, dif_neg hq]
      exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ hmB0))
  have huniq := chapter04_nonzero_fractional_ideal_is_maximal_power B L
    ((Ideal.map (algebraMap A B) mA : Ideal B) : FractionalIdeal B⁰ L)
    (by rw [hdecomp]; exact hpow_nezero e)
  let hdecomp' : ∃ q : ℤ,
      ((Ideal.map (algebraMap A B) mA : Ideal B) : FractionalIdeal B⁰ L) =
        chapter04FractionalIdealPower B L (IsLocalRing.maximalIdeal B) q :=
    ⟨e, hdecomp⟩
  have hchoose : Classical.choose hdecomp' = e := by
    exact huniq.unique (Classical.choose_spec hdecomp') hdecomp
  unfold chapter04IdealNorm
  rw [hchoose, chapter04IdealNormPower, ← Nat.cast_mul, hdegree, Nat.mul_comm]

/- The determinant of multiplication by a base element is the expected
power (§4.8). -/
theorem chapter04_norm_of_base_element_is_degree_power
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (πK : K) :
    Algebra.norm K (algebraMap K L πK) = πK ^ Module.finrank K L := by
  simpa using (Algebra.norm_algebraMap (R := K) (S := L) πK)

/- The residue quotient has the cardinality of the residue field (§4.8). -/
theorem chapter04_residue_quotient_cardinality
    (B l : Type*) [CommRing B] [Field l] (m : Ideal B)
    [m.IsMaximal] (red : B →+* l)
    (hred : chapter04ResidueMap B l m red)
    [Fintype (B ⧸ m)] [Fintype l] :
    Fintype.card (B ⧸ m) = Fintype.card l := by
  have hker : RingHom.ker red = m := by
    ext x
    rw [RingHom.mem_ker]
    exact hred.2 x
  let e : (B ⧸ m) ≃+* l :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hred.1)
  exact Fintype.card_congr e

/- For a finite residue field, the `f`th maximal-ideal power has index
`|k|^f`, the numerical shadow used in §4.8. -/
theorem chapter04_dvr_power_quotient_cardinality
    (A k : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field k]
    (m : Ideal A) [m.IsMaximal] [Fintype k]
    (f : ℕ) [Fintype (A ⧸ m ^ f)]
    (hmax : m = IsLocalRing.maximalIdeal A)
    (hequiv : Nonempty ((A ⧸ m) ≃+* k)) :
    Fintype.card (A ⧸ m ^ f) = Fintype.card k ^ f := by
  have hm0 : m ≠ (⊥ : Ideal A) := by
    rw [hmax]
    exact IsDiscreteValuationRing.not_a_field A
  letI : Fintype (A ⧸ m) := Fintype.ofEquiv k hequiv.some.toEquiv.symm
  calc
    Fintype.card (A ⧸ m ^ f) = Submodule.cardQuot (m ^ f) := by
      rw [Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    _ = Submodule.cardQuot m ^ f := cardQuot_pow_of_prime hm0
    _ = Fintype.card (A ⧸ m) ^ f := by
      rw [Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    _ = Fintype.card k ^ f := by
      rw [Fintype.card_congr hequiv.some.toEquiv]

/- The residue degree, not the ramification index, controls the norm of an
individual maximal-ideal power (§4.8). -/
theorem chapter04_residue_degree_quotient_cardinality
    (A B k l : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Field k] [Field l]
    [Algebra k l] [FiniteDimensional k l] (f : ℕ)
    [Fintype k] [Fintype l]
    [Fintype (A ⧸ IsLocalRing.maximalIdeal A)]
    [Fintype (B ⧸ IsLocalRing.maximalIdeal B)]
    (hA : Nonempty
      ((A ⧸ IsLocalRing.maximalIdeal A) ≃+* k))
    (hB : Nonempty
      ((B ⧸ IsLocalRing.maximalIdeal B) ≃+* l))
    (hf : f = Module.finrank k l) :
    Fintype.card (B ⧸ IsLocalRing.maximalIdeal B) =
      Fintype.card k ^ f := by
  calc
    Fintype.card (B ⧸ IsLocalRing.maximalIdeal B) = Fintype.card l :=
      Fintype.card_congr hB.some.toEquiv
    _ = Fintype.card k ^ Module.finrank k l := by
      rw [← Module.card_eq_pow_finrank]
    _ = Fintype.card k ^ f := by rw [hf]

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
