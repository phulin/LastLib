import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section08ExplicitTameNormEquations
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section10RootsOfUnityInsideTheUnitFiltration
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section05ResidueFieldShadows
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15.Section01TheStructuralDictionary
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace LastLib.Book05LocalClassFieldTheory.Chapter10

noncomputable section

/-! ## 10.2. Totally tamely ramified cyclic extensions -/

/- LOCAL_DEPENDENCY_GUESS: Eisenstein irreducibility and the normalized
   valuation extension supplied by the preceding local-field chapters turn
   the radical presentation into the stated cyclic, totally ramified field. -/
theorem chapter10_tame_radical_extension_is_cyclic_totally_ramified
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e) :
    Module.finrank K L = e ∧
      IsGalois K L ∧
      IsCyclic (Gal(L / K)) ∧
      Chapter10TotallyRamifiedValuedExtension
        D.valuation T.extensionValuation e := by
  sorry

/- Principal units are norms, while the residue of a unit norm is constrained
   to the `e`th-power subgroup. -/
theorem chapter10_tame_principal_units_are_norms
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e) :
    Chapter10FieldUnitFiltration D.valuation 1 ≤
      chapter10NormSubgroup K L := by
  sorry

theorem chapter10_tame_unit_norm_has_power_residue
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e)
    (x : Chapter10RingUnitGroup T.extensionValuation)
    (y : Chapter10RingUnitGroup D.valuation)
    (hnorm :
      chapter10RingUnitInField D.valuation y =
        chapter10NormHom K L
          (chapter10RingUnitInField T.extensionValuation x)) :
    chapter10ResidueUnitIsPower D.valuation e y := by
  classical
  let A := Chapter10ValuationRing D.valuation
  let B := Chapter10ValuationRing T.extensionValuation
  letI : Valuation.HasExtension D.valuation.toValuation T.extensionValuation.toValuation :=
    ⟨T.valuation_extension⟩
  letI : IsDiscreteValuationRing A := D.valuationRing_dvr
  letI : IsDiscreteValuationRing B := T.extension_dvr
  letI : Algebra A B :=
    Valuation.HasExtension.instAlgebra_valuationSubring
      D.valuation.toValuation T.extensionValuation.toValuation
  letI : Algebra A K := Algebra.ofSubsemiring A
  letI : Algebra B L := Algebra.ofSubsemiring B
  letI : Algebra A L := Algebra.ofSubsemiring A
  have hAL_apply (a : A) : algebraMap A L a = algebraMap K L (a : K) := by
    rfl
  have hAL_applyB (a : A) :
      algebraMap A L a = algebraMap B L (algebraMap A B a) := by
    rw [hAL_apply]
    calc
      algebraMap K L (a : K) = ((algebraMap A B a : B) : L) :=
        (Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
          D.valuation.toValuation T.extensionValuation.toValuation a).symm
      _ = algebraMap B L (algebraMap A B a) := by rfl
  let _ : IsScalarTower A K L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap A L a = algebraMap K L (algebraMap A K a)
    rw [hAL_apply]
    rfl
  let _ : IsScalarTower A B L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap A L a = algebraMap B L (algebraMap A B a)
    exact hAL_applyB a
  let _ : IsFractionRing A K :=
    (Valuation.valuationSubring.integers D.valuation.toValuation).isFractionRing
  let _ : IsFractionRing B L :=
    (Valuation.valuationSubring.integers T.extensionValuation.toValuation).isFractionRing
  let _ : Valuation.IsRankOneDiscrete D.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      D.valuation D.complete.1
  let _ : Valuation.IsRankOneDiscrete T.extensionValuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      T.extensionValuation T.extension_complete.1
  have hff :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15.complete_extension_has_finite_free_integral_closure
      D.valuation.toValuation T.extensionValuation.toValuation D.complete.2
  rcases hff with ⟨hclosure, hfiniteB, hfreeB, _⟩
  let _ : Module.Finite A B := hfiniteB
  let _ : Module.Free A B := hfreeB
  let _ : IsDedekindDomain B := by infer_instance
  let _ : IsIntegrallyClosed A := by infer_instance
  let _ : Algebra.IsIntegral A B := by infer_instance
  let _ : Module.IsTorsionFree A B := by infer_instance
  let C := integralClosure A L
  let f : B →ₗ[A] C :=
    { toFun := fun b =>
        ⟨(b : L), by
          change (b : L) ∈ (integralClosure A L : Set L)
          rw [hclosure]
          exact b.property⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a b
        apply Subtype.ext
        rfl }
  have hf_surj : Function.Surjective f := by
    intro c
    have hc' : (c : L) ∈ (integralClosure A L : Set L) := by
      exact c.property
    have hc : (c : L) ∈ (B : Set L) := by
      rw [← hclosure]
      exact hc'
    let b : B := ⟨(c : L), hc⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    rfl
  have hfinite : Module.Finite A C := Module.Finite.of_surjective f hf_surj
  obtain ⟨πL, _hπL0, hπL, _⟩ := T.extension_complete.1
  have htotal : Chapter10TotallyRamifiedValuedExtension
      D.valuation T.extensionValuation e :=
    (chapter10_tame_radical_extension_is_cyclic_totally_ramified D e T).2.2.2
  have hscale := htotal.2.1
  have hscale' : ∀ z : K, z ≠ 0 →
      T.extensionValuation (algebraMap K L z) = e • D.valuation z := by
    have hdisc :
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation
          D.valuation := D.complete.1
    rcases hdisc with ⟨_π, _hπ0, _hπ, hvalues⟩
    intro z hz
    obtain ⟨n, hn⟩ := hvalues z hz
    rw [hn]
    have hs := hscale z
    rw [hn] at hs
    have hprod : (e : WithTop ℤ) * (n : WithTop ℤ) =
        e • (n : WithTop ℤ) := by
      calc
        (e : WithTop ℤ) * (n : WithTop ℤ) =
            (((e : ℤ) * n : ℤ) : WithTop ℤ) := by norm_cast
        _ = ((e • n : ℤ) : WithTop ℤ) := by
          congr 1
        _ = e • (n : WithTop ℤ) := by
          simp only [WithTop.coe_nsmul]
    exact hs.trans hprod
  have hmap :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_uniformizer_maximal_ideal_map
      D.complete.2 hfinite D.valuation T.extensionValuation
      D.complete.1 T.extension_complete.1 T.valuation_extension
      (by
        intro x
        constructor
        · intro hx
          obtain ⟨a, ha⟩ :=
            (IsIntegrallyClosed.isIntegral_iff (R := A)).mp hx
          exact ha ▸ a.property
        · intro hx
          apply (IsIntegrallyClosed.isIntegral_iff (R := A)).mpr
          exact ⟨⟨x, hx⟩, rfl⟩)
      (by
        intro x
        constructor
        · intro hx
          have hx' : x ∈ (integralClosure A L : Set L) := by
            exact hx
          rw [hclosure] at hx'
          exact hx'
        · intro hx
          have hx' : x ∈ (B : Set L) := hx
          rw [← hclosure] at hx'
          exact hx')
      e hscale'
      (by
        intro a
        exact Valuation.HasExtension.coe_algebraMap_valuationSubring_eq
          D.valuation.toValuation T.extensionValuation.toValuation a)
      πL hπL
  have hram' :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      A B (IsLocalRing.maximalIdeal B) = e := by
    let mA : Ideal A := IsLocalRing.maximalIdeal A
    let mB : Ideal B := IsLocalRing.maximalIdeal B
    let J : Ideal B := mA.map (algebraMap A B)
    have hJpow : J = (IsLocalRing.maximalIdeal B) ^ e := hmap
    have hmBpow : (IsLocalRing.maximalIdeal B) ^ e ≠ (⊥ : Ideal B) := by
      intro hzero
      apply IsDiscreteValuationRing.not_a_field B
      exact (Ideal.pow_eq_bot (Nat.ne_of_gt T.positive)).mp hzero
    have hJ0 : J ≠ ⊥ := by
      rw [hJpow]
      exact hmBpow
    obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
      (IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal B)) J hJ0
    have hlen :
        (Module.length (Localization.AtPrime mB)
          (Localization.AtPrime mB ⧸
            mA.map (algebraMap A (Localization.AtPrime mB)))).toNat = n := by
      have hmaploc :
          mA.map (algebraMap A (Localization.AtPrime mB)) =
            J.map (algebraMap B (Localization.AtPrime mB)) := by
        rw [Ideal.map_map]
        congr 1
      let _ : IsDiscreteValuationRing
          (Localization.AtPrime mB) :=
        IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B
          (IsDiscreteValuationRing.not_a_field B)
            (Localization.AtPrime mB)
      rw [hmaploc, hn, Ideal.map_pow,
        Localization.AtPrime.map_eq_maximalIdeal,
        IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
      rfl
    have hramn :
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
            A B (IsLocalRing.maximalIdeal B) = n := by
      calc
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
            A B (IsLocalRing.maximalIdeal B) =
            (Module.length (Localization.AtPrime mB)
              (Localization.AtPrime mB ⧸
                mA.map (algebraMap A (Localization.AtPrime mB)))).toNat := by
          unfold LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
          exact Ideal.ramificationIdx_eq mA mB
        _ = n := hlen
    have hpows : (IsLocalRing.maximalIdeal B) ^ n =
        (IsLocalRing.maximalIdeal B) ^ e := hn.symm.trans hJpow
    have hen : n = e := by
      have hpowval := congrArg
        (IsDiscreteValuationRing.idealOrderIsoENat B) hpows
      have hleft :
          (IsDiscreteValuationRing.idealOrderIsoENat B)
              ((IsLocalRing.maximalIdeal B) ^ n) = (n : ENatᵒᵈ) := by
        rw [← IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe B n]
        exact (IsDiscreteValuationRing.idealOrderIsoENat B).apply_symm_apply _
      have hright :
          (IsDiscreteValuationRing.idealOrderIsoENat B)
              ((IsLocalRing.maximalIdeal B) ^ e) = (e : ENatᵒᵈ) := by
        rw [← IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe B e]
        exact (IsDiscreteValuationRing.idealOrderIsoENat B).apply_symm_apply _
      have hpowval' : (n : ENatᵒᵈ) = (e : ENatᵒᵈ) := by
        calc
          (n : ENatᵒᵈ) =
              (IsDiscreteValuationRing.idealOrderIsoENat B)
                ((IsLocalRing.maximalIdeal B) ^ n) := hleft.symm
          _ = (IsDiscreteValuationRing.idealOrderIsoENat B)
                ((IsLocalRing.maximalIdeal B) ^ e) := hpowval
          _ = (e : ENatᵒᵈ) := hright
      change (n : WithTop ℕ) = (e : WithTop ℕ) at hpowval'
      exact WithTop.coe_injective hpowval'
    exact hramn.trans hen
  have hram : e = (IsLocalRing.maximalIdeal B).ramificationIdx A := hram'.symm
  let k := Chapter10ResidueField D.valuation
  obtain ⟨ι⟩ := htotal.2.2.2 T.valuation_extension
  let redA : A →+* k := IsLocalRing.residue A
  let redB : B →+* k := ι.toRingHom.comp (IsLocalRing.residue B)
  have hredA :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04ResidueMap
        A k (IsLocalRing.maximalIdeal A) redA := by
    refine ⟨?_, ?_⟩
    · exact IsLocalRing.residue_surjective
    · intro a
      exact IsLocalRing.residue_eq_zero_iff a
  have hredB :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04ResidueMap
        B k (IsLocalRing.maximalIdeal B) redB := by
    refine ⟨?_, ?_⟩
    · intro z
      obtain ⟨z', hz'⟩ := ι.surjective z
      obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective z'
      refine ⟨b, ?_⟩
      change ι (IsLocalRing.residue B b) = z
      rw [hb]
      exact hz'
    · intro b
      change ι (IsLocalRing.residue B b) = 0 ↔ b ∈ IsLocalRing.maximalIdeal B
      constructor
      · intro h
        apply (IsLocalRing.residue_eq_zero_iff b).mp
        apply ι.injective
        simpa using h
      · intro h
        have hb0 : IsLocalRing.residue B b = 0 :=
          (IsLocalRing.residue_eq_zero_iff b).mpr h
        simp [hb0]
  have hcompat : ∀ a : A,
      redB (algebraMap A B a) = algebraMap k k (redA a) := by
    intro a
    change ι (IsLocalRing.residue B (algebraMap A B a)) =
      algebraMap k k (IsLocalRing.residue A a)
    rw [← Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap
      D.valuation.toValuation T.extensionValuation.toValuation a]
    rw [ι.commutes]
  have htrace :
      algebraMap A K (Algebra.intTrace A B (x : B)) =
        Algebra.trace K L (algebraMap B L (x : B)) := by
    exact Algebra.algebraMap_intTrace (A := A) (B := B) (K := K) (L := L) (x : B)
  have hnorm' :
      algebraMap A K (y : A) = Algebra.norm K (algebraMap B L (x : B)) := by
    simpa [chapter10RingUnitInField, chapter10NormHom] using congrArg Units.val hnorm
  have hresnorm :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_residue_trace_and_norm
      A B K L k k redA redB hredA hredB hcompat e
      (Algebra.intTrace A B (x : B)) (y : A) (x : B) x htrace hnorm' hram
  have hpow : redA (y : A) = redB (x : B) ^ e :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_totally_ramified_residue_norm_of_unit
      k e (redA (y : A)) (redB (x : B)) hresnorm.2
  change chapter10UnitReduction D.valuation y ∈
    chapter10PowerSubgroup (G := (Chapter10ResidueField D.valuation)ˣ) e
  rw [chapter10_mem_powerSubgroup_iff]
  refine ⟨Units.map redB x, ?_⟩
  apply Units.ext
  change redB (x : B) ^ e = redA (y : A)
  exact hpow.symm

/- The norm of the chosen radical is the constant-term formula. -/
theorem chapter10_norm_of_tame_radical_root
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e) :
    Algebra.norm K T.root =
      (-1 : K) ^ (e + 1) * (T.unitFactor : K) * (D.uniformizer : K) := by
  have hdegree : Module.finrank K L = e :=
    (chapter10_tame_radical_extension_is_cyclic_totally_ramified D e T).1
  have hxint : IsIntegral K T.root := IsIntegral.of_finite K T.root
  have hgenIF : IntermediateField.adjoin K ({T.root} : Set L) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra
      (F := K) (S := ({T.root} : Set L)) T.generates
  have hfinrank :
      Module.finrank (IntermediateField.adjoin K ({T.root} : Set L)) L = 1 := by
    rw [hgenIF]
    simp
  have hdegpoly : (minpoly K T.root).natDegree = e := by
    calc
      (minpoly K T.root).natDegree =
          Module.finrank K (IntermediateField.adjoin K ({T.root} : Set L)) :=
        (IntermediateField.adjoin.finrank hxint).symm
      _ = Module.finrank K L := by
        have htower :=
          Module.finrank_mul_finrank K
            (IntermediateField.adjoin K ({T.root} : Set L)) L
        rw [hfinrank, mul_one] at htower
        exact htower
      _ = e := hdegree
  have hrootpoly :
      Polynomial.aeval T.root
        (Polynomial.X ^ e -
          Polynomial.C ((T.unitFactor : K) * (D.uniformizer : K))) = 0 := by
    rw [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_C, sub_eq_zero]
    exact T.root_equation
  have hminpoly :
      minpoly K T.root =
        Polynomial.X ^ e -
          Polynomial.C ((T.unitFactor : K) * (D.uniformizer : K)) := by
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hxint)
      (Polynomial.monic_X_pow_sub_C _ (Nat.ne_of_gt T.positive))
      (minpoly.dvd K T.root hrootpoly)
      (by rw [Polynomial.natDegree_X_pow_sub_C, hdegpoly])).symm
  rw [mul_assoc]
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_kummer_uniformizer_norm
      K L ((T.unitFactor : K) * (D.uniformizer : K)) T.root e hminpoly T.generates hdegree

theorem chapter10_norm_of_tame_radical_root_unit_value
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e) :
      (chapter10NormOfRootUnit T : K) =
      (-1 : K) ^ (e + 1) * (T.unitFactor : K) * (D.uniformizer : K) := by
  change Algebra.norm K T.root = _
  exact chapter10_norm_of_tame_radical_root D e T

/- A multiplicative Teichmüller section turns the residue power condition into
   an actual subgroup of `Kˣ`. -/
theorem chapter10_tame_norm_subgroup_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e)
    [Fintype (Chapter10ResidueField D.valuation)]
    (s : (Chapter10ResidueField D.valuation)ˣ →*
      Chapter10RingUnitGroup D.valuation)
    (hsred : ∀ a, chapter10UnitReduction D.valuation (s a) = a)
    (hsteich : ∀ a,
      (s a) ^ (Fintype.card (Chapter10ResidueField D.valuation) - 1) = 1) :
    chapter10NormSubgroup K L =
      Subgroup.zpowers (chapter10NormOfRootUnit T) ⊔
        (chapter10TeichmullerPowerSubgroup D.valuation e s ⊔
          Chapter10FieldUnitFiltration D.valuation 1) := by
  sorry

/- The roots-of-unity hypothesis forces the tame degree to divide the order
   of the residue-field unit group. -/
theorem chapter10_tame_degree_dvd_residue_unit_order
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e)
    [Fintype (Chapter10ResidueField D.valuation)] :
    e ∣ Fintype.card (Chapter10ResidueField D.valuation) - 1 := by
  classical
  have heK : (e : K) ≠ 0 := by
    by_cases hchar : CharZero K
    · exact_mod_cast (Nat.ne_of_gt T.positive)
    · obtain ⟨q, hq⟩ := CharP.exists K
      have hq0 : q ≠ 0 := by
        intro hq0
        apply hchar
        letI : CharP K 0 := hq0 ▸ hq
        exact CharP.charP_to_charZero K
      have hqprime : q.Prime :=
        (CharP.char_is_prime_or_zero K q).resolve_right hq0
      let A := Chapter10ValuationRing D.valuation
      letI : CharP K q := hq
      letI : CharP A q :=
        A.subtype.charP (ValuationSubring.subtype_injective A) q
      letI : CharP (Chapter10ResidueField D.valuation)
          D.residueCharacteristic := D.residueCharacteristic_charP
      have hpdiv : D.residueCharacteristic ∣ q := by
        exact CharP.dvd_of_ringHom (IsLocalRing.residue A) q
          D.residueCharacteristic
      have hpq : D.residueCharacteristic = q :=
        (Nat.prime_dvd_prime_iff_eq D.residueCharacteristic_prime hqprime).mp hpdiv
      intro he0
      have hdiv : q ∣ e := by
        rw [← CharP.cast_eq_zero_iff K q e]
        exact he0
      exact (Nat.Prime.coprime_iff_not_dvd hqprime).mp
        (by rw [← hpq]; exact T.tame.symm) hdiv
  letI : NeZero (e : K) := ⟨heK⟩
  obtain ⟨ζ, hζ⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) e
  obtain ⟨z, hz⟩ := T.roots_of_unity_in_base ζ hζ.pow_eq_one
  have hzprim : IsPrimitiveRoot z e := by
    apply IsPrimitiveRoot.of_map_of_injective (f := algebraMap K (AlgebraicClosure K))
      ?_ (algebraMap K (AlgebraicClosure K)).injective
    rw [hz]
    exact hζ
  obtain ⟨u, hu⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_field_root_of_unity_is_ring_unit
      (Chapter10ValuationRing D.valuation) e T.positive z hzprim.pow_eq_one
  let A := Chapter10ValuationRing D.valuation
  let f : Aˣ →* Kˣ := Units.map A.subtype.toMonoidHom
  have hmap_injective : Function.Injective f :=
    Units.map_injective (ValuationSubring.subtype_injective A)
  let zunit : Kˣ := (hzprim.isUnit (Nat.ne_of_gt T.positive)).unit
  have hzunitprim : IsPrimitiveRoot zunit e :=
    hzprim.isUnit_unit (Nat.ne_of_gt T.positive)
  have hzunit_value : (zunit : K) = z := by
    exact (hzprim.isUnit (Nat.ne_of_gt T.positive)).unit_spec
  have hmap : f u = zunit := by
    apply Units.ext
    exact hu.trans hzunit_value.symm
  have huprim : IsPrimitiveRoot u e := by
    apply IsPrimitiveRoot.of_map_of_injective (f := f) ?_ hmap_injective
    rw [hmap]
    exact hzunitprim
  have hu_power : u ^ e = 1 := by
    apply hmap_injective
    rw [map_pow]
    apply Units.ext
    change ((f u : Kˣ) : K) ^ e = 1
    rw [hu]
    exact hzprim.pow_eq_one
  let H : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10RootOfUnitySubgroup
      A e := ⟨u, hu_power⟩
  let red : Aˣ →* (Chapter10ResidueField D.valuation)ˣ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitReduction A
  letI : Fact (Nat.Prime D.residueCharacteristic) :=
    ⟨D.residueCharacteristic_prime⟩
  letI : CharP (Chapter10ResidueField D.valuation)
      D.residueCharacteristic := D.residueCharacteristic_charP
  have hredprim : IsPrimitiveRoot (red (H : Aˣ)) e := by
    refine ⟨?_, ?_⟩
    · rw [← map_pow]
      exact congrArg red H.property
    · intro n hn
      let V : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10RootOfUnitySubgroup
          (Chapter10ValuationRing D.valuation) e :=
        ⟨(H : Chapter10RingUnitGroup D.valuation) ^ n, by
          calc
            ((H : Aˣ) ^ n) ^ e = ((H : Aˣ) ^ e) ^ n := by
              rw [← pow_mul, Nat.mul_comm, pow_mul]
            _ = 1 := by rw [H.property, one_pow]⟩
      have hVred : red (V : Aˣ) = 1 := by
        change red ((H : Aˣ) ^ n) = 1
        rw [map_pow, hn]
      have hV : V = 1 :=
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_prime_to_residue_characteristic_roots_reduce_injectively
          (Chapter10ValuationRing D.valuation) e D.residueCharacteristic T.tame
          hVred
      have hUn : (H : Aˣ) ^ n = 1 :=
        by
          have hVval := congrArg Subtype.val hV
          change (H : Aˣ) ^ n = 1 at hVval
          exact hVval
      exact huprim.dvd_of_pow_eq_one n (by
        change u ^ n = 1 at hUn
        exact hUn)
  have horder : orderOf (red (H : Aˣ)) ∣
      Fintype.card ((Chapter10ResidueField D.valuation)ˣ) := orderOf_dvd_card
  have hcardunits : Fintype.card ((Chapter10ResidueField D.valuation)ˣ) =
      Fintype.card (Chapter10ResidueField D.valuation) - 1 :=
    Fintype.card_units (α := Chapter10ResidueField D.valuation)
  rw [← hredprim.eq_orderOf, hcardunits] at horder
  exact horder

theorem chapter10_tame_norm_quotient_card
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e)
    [Fintype (Chapter10ResidueField D.valuation)] :
    Nat.card (Chapter10NormQuotient K L) = e := by
  sorry

/- The field-norm generator retains the unit factor from the radical
   equation; valuation one alone does not determine this subgroup generator. -/
theorem chapter10_tame_norm_generator_has_unit_factor
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e) :
    (chapter10NormOfRootUnit T : K) /
        (D.uniformizer : K) =
      (-1 : K) ^ (e + 1) * (T.unitFactor : K) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter10
