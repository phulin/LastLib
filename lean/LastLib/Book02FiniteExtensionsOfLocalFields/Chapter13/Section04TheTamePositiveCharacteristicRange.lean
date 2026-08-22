import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13.Section03FinitenessInCharacteristicZero
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section04ImperfectResidueFields
import Mathlib.RingTheory.LaurentSeries

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13

noncomputable section

universe uK uL uGamma

open Polynomial

/-! ## 13.4. The tame positive-characteristic range -/

def chapter13ResidueCharacteristicExponent (k : Type*) [Ring k] : ℕ :=
  ringExpChar k

/-- The derivative has the expected nonzero leading term when the degree is
prime to the field characteristic. -/
theorem chapter13_prime_to_characteristic_derivative_has_expected_degree
    {E : Type*} [Field E] {p e : ℕ} [Fact p.Prime] [CharP E p]
    (g : E[X]) (hmonic : g.Monic) (hdegree : g.natDegree = e)
    (he : 0 < e) (he_p : Nat.Coprime e p) :
    (g.derivative).natDegree = e - 1 ∧
      g.derivative.leadingCoeff = (e : E) := by
  have he_cast : (e : E) ≠ 0 := by
    intro hezero
    have hdiv : p ∣ e := (CharP.cast_eq_zero_iff E p e).mp hezero
    exact (Nat.Prime.ne_one (Fact.out : Nat.Prime p)
      (he_p.symm.eq_one_of_dvd hdiv))
  have hcast : ((e - 1 : ℕ) : E) + 1 = (e : E) := by
    rw [Nat.cast_sub he]
    push_cast
    ring
  have hlead : g.coeff e = 1 := by
    rw [← hdegree]
    exact hmonic.coeff_natDegree
  have hdegree_le : (g.derivative).natDegree ≤ e - 1 := by
    simpa [hdegree] using Polynomial.natDegree_derivative_le g
  have hcoeff : (g.derivative).coeff (e - 1) ≠ 0 := by
    rw [Polynomial.coeff_derivative]
    rw [show e - 1 + 1 = e by omega, hlead, hcast]
    simpa using he_cast
  have hderivative_degree : (g.derivative).natDegree = e - 1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdegree_le hcoeff
  constructor
  · exact hderivative_degree
  · rw [Polynomial.leadingCoeff, hderivative_degree,
      Polynomial.coeff_derivative]
    rw [show e - 1 + 1 = e by omega, hlead, hcast]
    simp

/-- An irreducible monic degree-`e` polynomial over a field of characteristic
`p` is separable when `p` does not divide `e`.  Irreducibility is essential:
a repeated-factor polynomial can have prime-to-`p` total degree. -/
theorem chapter13_prime_to_characteristic_monic_polynomial_is_separable
    {E : Type*} [Field E] {p e : ℕ} [Fact p.Prime] [CharP E p]
    (g : E[X]) (hirreducible : Irreducible g) (hmonic : g.Monic)
    (hdegree : g.natDegree = e)
    (he : 0 < e) (he_p : Nat.Coprime e p) :
    g.Separable := by
  apply (Polynomial.separable_iff_derivative_ne_zero hirreducible).2
  have hderivative := chapter13_prime_to_characteristic_derivative_has_expected_degree
    g hmonic hdegree he he_p
  have he_cast : (e : E) ≠ 0 := by
    intro hezero
    have hdiv : p ∣ e := (CharP.cast_eq_zero_iff E p e).mp hezero
    exact (Nat.Prime.ne_one (Fact.out : Nat.Prime p)
      (he_p.symm.eq_one_of_dvd hdiv))
  apply Polynomial.leadingCoeff_ne_zero.mp
  rw [hderivative.2]
  exact he_cast

/-- In characteristic zero, every irreducible monic positive-degree
polynomial is separable. -/
theorem chapter13_characteristic_zero_monic_polynomial_is_separable
    {E : Type*} [Field E] [CharZero E]
    (g : E[X]) (hirreducible : Irreducible g) (he : 0 < g.natDegree)
    (hmonic : g.Monic) :
    g.Separable := by
  have _he : 0 < g.natDegree := he
  have _hmonic : g.Monic := hmonic
  exact hirreducible.separable

theorem chapter13_characteristic_zero_irreducible_polynomial_is_separable
    {E : Type*} [Field E] [CharZero E]
    (g : E[X]) (hirreducible : Irreducible g) :
    g.Separable := by
  exact hirreducible.separable

/-- The prime-to-residue-characteristic condition is the exact tame
condition used in the coefficient argument. -/
theorem chapter13_eisenstein_degree_prime_to_residue_characteristic_is_separable
    {A E : Type*} [CommRing A] [Field E]
    [Algebra A E] {p e : ℕ} [Fact p.Prime] [CharP E p]
    (g : A[X])
    (hirreducible : Irreducible (g.map (algebraMap A E)))
    (hmonic : (g.map (algebraMap A E)).Monic)
    (hdegree : (g.map (algebraMap A E)).natDegree = e)
    (he : 0 < e) (he_p : Nat.Coprime e p) :
    (g.map (algebraMap A E)).Separable := by
  exact chapter13_prime_to_characteristic_monic_polynomial_is_separable
    _ hirreducible hmonic hdegree he he_p

/-- Unramified extensions are tame because their ramification index is one. -/
theorem chapter13_unramified_ramification_index_is_tame
    (k : Type*) [Field k] :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09Tame k 1 := by
  exact Nat.coprime_one_left _

/-- A tame Eisenstein coefficient family therefore satisfies the separability
hypothesis required by the Krasner local-constancy interface. -/
theorem chapter13_tame_eisenstein_family_is_separable
    {A E : Type*} [CommRing A] [Field E]
    [Algebra A E] {p e : ℕ} [Fact p.Prime] [CharP E p]
    (_m : Ideal A) (g : A[X])
    (_hEisenstein : g.IsEisensteinAt _m)
    (hirreducible : Irreducible (g.map (algebraMap A E)))
    (hmonic : (g.map (algebraMap A E)).Monic)
    (hdegree : (g.map (algebraMap A E)).natDegree = e)
    (he : 0 < e) (he_p : Nat.Coprime e p) :
    (g.map (algebraMap A E)).Separable := by
  exact chapter13_eisenstein_degree_prime_to_residue_characteristic_is_separable
    g hirreducible hmonic hdegree he he_p

/-- The tame proof has the same compact-family shape as the characteristic
zero proof; only the separability bridge changes. -/
theorem chapter13_tame_finiteness_reduces_to_compact_separable_families
    {P C : Type*} [TopologicalSpace P]
    (φ : P → C) (hcompact : IsCompact (Set.univ : Set P))
    (hlocally_constant : chapter13LocallyConstant φ) :
    Set.Finite (Set.range φ) := by
  exact chapter13_compact_locally_constant_range_finite φ hcompact
    hlocally_constant

/-! The fixed-degree corollary is stated at the valuation level, where the
ramification index divides the defectless degree product. -/
theorem chapter13_prime_to_p_degree_extension_is_tame
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (p d : ℕ) [Fact p.Prime]
    (hdegree : Module.finrank K L = d) (hd : Nat.Coprime d p) :
    chapter13TameExtension vK vL := by
  let e :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring)
  let f :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring)
  have hformula : d = e * f := by
    have hformula' :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
        vK vL hcomplete
    change Module.finrank K L = e * f at hformula'
    exact hdegree.symm.trans hformula'
  have hdiv : e ∣ d := by
    rw [hformula]
    exact dvd_mul_right e f
  have hecop : Nat.Coprime e p := Nat.Coprime.of_dvd_left hdiv hd
  change Nat.Coprime e (ringExpChar
    (IsLocalRing.ResidueField vK.valuationSubring))
  exact hecop

private theorem chapter13_lifted_tame_witness
    {K : Type uK} {L : Type uL}
    [Field K] [Field L] [Algebra K L]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    [Valuation.IsRankOneDiscrete vK] [FiniteDimensional K L]
    (x : L) (hx : x ≠ 0) (hxl : vL x < 1)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (p d : ℕ) [Fact p.Prime]
    (hchar : ringExpChar (IsLocalRing.ResidueField vK.valuationSubring) = p)
    (hdegree : Module.finrank K L = d) (hd : Nat.Coprime d p) :
    Nonempty (Chapter13ValuationExtensionWitness vK (L := L)) := by
  let : LinearOrderedCommMonoidWithZero
      (ULift.{uL} (WithZero (Multiplicative ℤ))) := by
    apply Function.Injective.linearOrderedCommMonoidWithZero ULift.down ULift.down_injective
    all_goals (intros; rfl)
  let : CommGroupWithZero (ULift.{uL} (WithZero (Multiplicative ℤ))) := by
    apply Function.Injective.commGroupWithZero ULift.down ULift.down_injective
    all_goals (intros; rfl)
  let : LinearOrderedCommGroupWithZero
      (ULift.{uL} (WithZero (Multiplicative ℤ))) :=
    { __ := (inferInstance : LinearOrderedCommMonoidWithZero
        (ULift.{uL} (WithZero (Multiplicative ℤ))))
      __ := (inferInstance : CommGroupWithZero
        (ULift.{uL} (WithZero (Multiplicative ℤ)))) }
  let f : (WithZero (Multiplicative ℤ)) →*₀
      ULift.{uL} (WithZero (Multiplicative ℤ)) :=
    { toFun := ULift.up
      map_one' := rfl
      map_zero' := rfl
      map_mul' := by intros; rfl }
  let vL' : Valuation L (ULift.{uL} (WithZero (Multiplicative ℤ))) :=
    vL.map f (by intro a b hab; exact hab)
  have hx' : vL' x < 1 := by
    change ULift.up (vL x) < ULift.up 1
    exact hxl
  have hx0' : vL' x ≠ 0 := by
    intro hzero
    exact ((Valuation.ne_zero_iff vL').2 hx) hzero
  let u : (MonoidWithZeroHom.ofClass vL').valueGroup :=
    ⟨Units.mk0 (vL' x) hx0', by
      apply MonoidWithZeroHom.mem_valueGroup
      exact ⟨x, rfl⟩⟩
  have hu_ne : u ≠ 1 := by
    intro hu
    apply (ne_of_lt hx')
    have hu' := congrArg Subtype.val hu
    have hu'' := congrArg Units.val hu'
    simpa [u] using hu''
  have hnot : ¬ Subsingleton ((MonoidWithZeroHom.ofClass vL').valueGroup) := by
    intro hs
    apply hu_ne
    exact hs.elim u 1
  let e : (WithZero (Multiplicative ℤ))ˣ →*
      (ULift.{uL} (WithZero (Multiplicative ℤ)))ˣ :=
    Units.map {
      toFun := ULift.up
      map_one' := rfl
      map_mul' := by intros; rfl }
  let : IsCyclic ((ULift.{uL} (WithZero (Multiplicative ℤ)))ˣ) := by
    apply isCyclic_of_surjective e
    intro y
    refine ⟨Units.map {
      toFun := ULift.down
      map_one' := rfl
      map_mul' := by intros; rfl } y, ?_⟩
    apply Units.ext
    rfl
  let : IsCyclic ((MonoidWithZeroHom.ofClass vL').valueGroup) := by
    infer_instance
  let : Nontrivial ((MonoidWithZeroHom.ofClass vL').valueGroup) :=
    not_subsingleton_iff_nontrivial.mp hnot
  let hdisc : Valuation.IsRankOneDiscrete vL' :=
    Valuation.IsRankOneDiscrete.mk' vL'
  let : IsCyclic ((MonoidWithZeroHom.ofClass vL).valueGroup) := by
    infer_instance
  let u₀ : (MonoidWithZeroHom.ofClass vL).valueGroup :=
    ⟨Units.mk0 (vL x) ((Valuation.ne_zero_iff vL).2 hx), by
      apply MonoidWithZeroHom.mem_valueGroup
      exact ⟨x, rfl⟩⟩
  have hu₀_ne : u₀ ≠ 1 := by
    intro hu₀
    apply (ne_of_lt hxl)
    have hu₀' := congrArg Subtype.val hu₀
    have hu₀'' := congrArg Units.val hu₀'
    simpa [u₀] using hu₀''
  let : Nontrivial ((MonoidWithZeroHom.ofClass vL).valueGroup) :=
    not_subsingleton_iff_nontrivial.mp (by
      intro hs
      exact hu₀_ne (hs.elim u₀ 1))
  let : Valuation.IsRankOneDiscrete vL :=
    Valuation.IsRankOneDiscrete.mk' vL
  let : vK.HasExtension vL := ⟨hext⟩
  let e₀ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring)
  let f₀ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterResidueDegree
      vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring)
  have hformula : d = e₀ * f₀ := by
    have hformula' :=
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
        vK vL hcomplete
    change Module.finrank K L = e₀ * f₀ at hformula'
    exact hdegree.symm.trans hformula'
  have hdiv : e₀ ∣ d := by
    rw [hformula]
    exact dvd_mul_right e₀ f₀
  have hecop : Nat.Coprime e₀ p := Nat.Coprime.of_dvd_left hdiv hd
  have htame : chapter13TameExtension vK vL := by
    unfold chapter13TameExtension
    change Nat.Coprime e₀ (ringExpChar
      (IsLocalRing.ResidueField vK.valuationSubring))
    rw [hchar]
    exact hecop
  have hext' : vK.IsEquiv (vL'.comap (algebraMap K L)) := by
    apply Valuation.isEquiv_of_val_le_one
    intro y
    change vK y ≤ 1 ↔ vL' (algebraMap K L y) ≤ 1
    change vK y ≤ 1 ↔
      (ULift.up (vL (algebraMap K L y)) :
        ULift.{uL} (WithZero (Multiplicative ℤ))) ≤
        (ULift.up (1 : WithZero (Multiplicative ℤ)) :
          ULift.{uL} (WithZero (Multiplicative ℤ)))
    change vK y ≤ 1 ↔ vL (algebraMap K L y) ≤ 1
    simpa [Valuation.comap_apply] using hext y 1
  let : vK.HasExtension vL' := ⟨hext'⟩
  let : Valuation.IsRankOneDiscrete vL' := hdisc
  have hsub : vL'.valuationSubring = vL.valuationSubring := by
    ext z
    change vL' z ≤ 1 ↔ vL z ≤ 1
    change
      (ULift.up (vL z) : ULift.{uL} (WithZero (Multiplicative ℤ))) ≤
          (ULift.up (1 : WithZero (Multiplicative ℤ)) :
            ULift.{uL} (WithZero (Multiplicative ℤ))) ↔
        vL z ≤ 1
    exact Iff.rfl
  have htame' : chapter13TameExtension vK vL' := by
    cases hsub
    exact htame
  refine ⟨{
    valueGroup := ULift.{uL} (WithZero (Multiplicative ℤ))
    valuation := vL'
    tame := htame' }⟩

/-- Fixed-degree tame finiteness in equal characteristic.  The conclusion is
stated on the canonical `K`-isomorphism-class set from the dependency layer. -/
theorem chapter13_laurent_series_prime_to_p_degree_finiteness
    (k : Type*) [Field k] [Fintype k]
    (p d : ℕ) [Fact p.Prime] [CharP k p]
    (hd : Nat.Coprime d p) :
    Set.Finite (chapter13DegreeClasses (K := LaurentSeries k) d) := by
  let vK : Valuation (LaurentSeries k) (WithZero (Multiplicative ℤ)) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesValuation k
  have hvKdiscrete : Valuation.IsRankOneDiscrete vK := by
    dsimp [vK]
    change Valuation.IsRankOneDiscrete
      ((PowerSeries.idealX k).valuation (LaurentSeries k))
    infer_instance
  let : Valuation.IsRankOneDiscrete vK := hvKdiscrete
  have hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring := by
    exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09_laurent_series_valuation_ring_complete k
  let : Finite (IsLocalRing.ResidueField vK.valuationSubring) := by
    dsimp [vK]
    exact Finite.of_equiv k
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesResidueRingEquiv k).toEquiv
  have hreschar : CharP (IsLocalRing.ResidueField vK.valuationSubring) p := by
    exact charP_of_injective_ringHom
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10LaurentSeriesResidueRingEquiv k).toRingHom.injective p
  have hchar : ringExpChar (IsLocalRing.ResidueField vK.valuationSubring) = p := by
    let : CharP (IsLocalRing.ResidueField vK.valuationSubring) p := hreschar
    exact ringExpChar.eq _ p
  have htame := chapter13_theorem_13_2_bounded_tame_finiteness vK hcomplete d
  apply htame.subset
  intro c hc
  rcases hc with ⟨E, hclass, hdegree⟩
  refine ⟨E, hclass, hdegree.le, ?_⟩
  let : Field E.carrier := E.field_carrier
  let : Algebra (LaurentSeries k) E.carrier := E.algebra
  let : FiniteDimensional (LaurentSeries k) E.carrier := E.finite_dimensional
  have hKinj : Function.Injective
      (algebraMap (LaurentSeries k) E.carrier) := by
    exact FaithfulSMul.algebraMap_injective _ _
  let A := vK.valuationSubring
  let B := integralClosure A E.carrier
  have hAinj : Function.Injective (algebraMap A (LaurentSeries k)) := by
    intro a b hab
    apply Subtype.ext
    simpa only [ValuationSubring.algebraMap_apply] using hab
  let hcdvr : LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11IsCompleteDVR A :=
    { isAdicComplete := hcomplete }
  let : Algebra.IsIntegral A B :=
    IsIntegralClosure.isIntegral_algebra A E.carrier
  have hABinj : Function.Injective (algebraMap A B) := by
    intro a b hab
    apply hAinj
    apply hKinj
    calc
      algebraMap A E.carrier a =
          algebraMap B E.carrier (algebraMap A B a) :=
        (IsScalarTower.algebraMap_apply A B E.carrier a).symm
      _ = algebraMap B E.carrier (algebraMap A B b) :=
        congrArg (algebraMap B E.carrier) hab
      _ = algebraMap A E.carrier b :=
        IsScalarTower.algebraMap_apply A B E.carrier b
  let : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).2
      hABinj
  have hfinite : Module.Finite A B := by
    change Module.Finite A (integralClosure A E.carrier)
    exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_complete_dvr_valuation_ring_is_finite A
        (LaurentSeries k) E.carrier hcdvr
  let : IsDedekindDomain B := by
    exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_finite_normalization_is_dedekind A
        (LaurentSeries k) E.carrier B hfinite
  obtain ⟨W : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousValuationExtension E.carrier vK⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_valuation_extension_exists_as_heterogeneous
      (K := LaurentSeries k) (L := E.carrier)
      (Γ₀ := WithZero (Multiplicative ℤ)) vK
  let hA := Valuation.valuationSubring.integers vK
  let P := LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_extension_center (A := A) (B := B)
      (K := LaurentSeries k) (L := E.carrier) vK hA W
  have hPabove := LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_extension_center_is_prime_above
      (A := A) (B := B) (K := LaurentSeries k) (L := E.carrier) vK hA W
  let : P.IsPrime := hPabove.1
  have hPmax : P.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) (S := B) P
    rw [hPabove.2]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hPover : P.LiesOver (IsLocalRing.maximalIdeal A) := ⟨hPabove.2.symm⟩
  have hP0 : P ≠ (⊥ : Ideal B) := by
    let : P.LiesOver (IsLocalRing.maximalIdeal A) := hPover
    exact Ideal.ne_bot_of_liesOver_of_ne_bot
      (IsDiscreteValuationRing.not_a_field A) P
  let : P.IsMaximal := hPmax
  let : IsDiscreteValuationRing
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11BranchLocalization B P) :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_branch_localization_is_dvr B P hP0
  have hbranch : LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11Branch A B (IsLocalRing.maximalIdeal A) P := by
    refine ⟨hPabove.1, hPmax, ?_⟩
    exact hPover
  let ιA : A →+* vK.valuationSubring := RingHom.id A
  have hιA : ∀ a : A, (ιA a : LaurentSeries k) =
      algebraMap A (LaurentSeries k) a := by
    intro a
    rfl
  have hcenter : LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11ValuationCenter A (LaurentSeries k)
        (IsLocalRing.maximalIdeal A) vK ιA := by
    change IsLocalRing.maximalIdeal A =
      (IsLocalRing.maximalIdeal A).comap (RingHom.id A)
    apply le_antisymm <;> intro a ha
    · exact ha
    · exact ha
  obtain ⟨vL, ι, hext, hcenterL, hι⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11_branch_labels_valuation_extensions A B
        (LaurentSeries k) E.carrier hAinj hKinj
        (IsLocalRing.maximalIdeal A) rfl P hbranch hfinite vK ιA hιA hcenter
  have hPmem : ∃ b : B, b ∈ P ∧ b ≠ 0 := by
    by_contra h
    apply hP0
    apply le_antisymm
    · intro b hb
      rw [Ideal.mem_bot]
      by_contra hb0
      exact h ⟨b, hb, hb0⟩
    · exact bot_le
  rcases hPmem with ⟨b, hbP, hb0⟩
  have hmax : ι b ∈ IsLocalRing.maximalIdeal vL.valuationSubring := by
    change b ∈ (IsLocalRing.maximalIdeal vL.valuationSubring).comap ι
    rw [← hcenterL]
    exact hbP
  have hlt : vL (ι b : E.carrier) < 1 := by
    rw [← Valuation.mem_maximalIdeal_iff]
    exact hmax
  have hιb0 : (ι b : E.carrier) ≠ 0 := by
    intro hz
    apply hb0
    apply IsIntegralClosure.algebraMap_injective B A E.carrier
    calc
      algebraMap B E.carrier b = (ι b : E.carrier) := (hι b).symm
      _ = 0 := hz
      _ = algebraMap B E.carrier 0 := by simp
  change Module.finrank (LaurentSeries k) E.carrier = d at hdegree
  apply chapter13_lifted_tame_witness vK vL (ι b : E.carrier) hιb0 hlt hext
    hcomplete p d hchar hdegree hd

/-- The numerical scope of the tame corollary: the prime-to-`p` hypothesis is
what permits the preceding separability argument. -/
def chapter13TameDegreeScope (p d : ℕ) : Prop :=
  Nat.Coprime d p

theorem chapter13_tame_degree_scope_iff
    (p d : ℕ) :
    chapter13TameDegreeScope p d ↔ Nat.Coprime d p :=
  Iff.rfl

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13
