import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section06QuadraticLaboratory
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section04MultiplicationPowersAndResidueCharacteristic

namespace LastLib.Book05LocalClassFieldTheory.Chapter10

noncomputable section

/-! ## 10.3. The three quadratic extensions for odd residue characteristic -/

def chapter10QuadraticUnramifiedNormSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K) : Subgroup Kˣ :=
  chapter10ValueUnitSubgroup D D.uniformizer 2 0

def chapter10QuadraticSqrtPiNormSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (s : (Chapter10ResidueField D.valuation)ˣ →*
      Chapter10RingUnitGroup D.valuation) : Subgroup Kˣ :=
  Subgroup.zpowers
      (chapter10NegOneUnit K * D.uniformizer) ⊔
    (chapter10TeichmullerPowerSubgroup D.valuation 2 s ⊔
      Chapter10FieldUnitFiltration D.valuation 1)

def chapter10QuadraticSqrtUnitPiNormSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (s : (Chapter10ResidueField D.valuation)ˣ →*
      Chapter10RingUnitGroup D.valuation)
    (u : Chapter10RingUnitGroup D.valuation) : Subgroup Kˣ :=
  Subgroup.zpowers
      (chapter10NegOneUnit K * chapter10RingUnitInField D.valuation u *
        D.uniformizer) ⊔
    (chapter10TeichmullerPowerSubgroup D.valuation 2 s ⊔
      Chapter10FieldUnitFiltration D.valuation 1)

def chapter10QuadraticResidueNonsquare
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (u : Chapter10RingUnitGroup D.valuation) : Prop :=
  ¬chapter10ResidueUnitIsPower D.valuation 2 u

theorem chapter10_quadratic_nonsquare_unit_exists
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (hodd : D.residueCharacteristic ≠ 2) :
    ∃ u : Chapter10RingUnitGroup D.valuation,
      chapter10QuadraticResidueNonsquare D u := by
  let k := Chapter10ResidueField D.valuation
  let A := Chapter10ValuationRing D.valuation
  let _ : CharP k D.residueCharacteristic := D.residueCharacteristic_charP
  have hodd_card : Fintype.card k % 2 = 1 := by
    obtain ⟨n, _hp, hcard⟩ := FiniteField.card k D.residueCharacteristic
    have hpodd : Odd D.residueCharacteristic :=
      D.residueCharacteristic_prime.eq_two_or_odd'.resolve_left hodd
    rw [hcard]
    exact Nat.odd_iff.mp (hpodd.pow)
  let _ : Fintype
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquareClassGroup k) :=
    Fintype.ofFinite _
  have hsquare_card : Fintype.card
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquareClassGroup k) = 2 :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03_finite_odd_field_has_two_square_classes
      k hodd_card
  have hsquare_ne_top :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquaresSubgroup k ≠ ⊤ := by
    intro htop
    have hcard_one : Fintype.card
        (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquareClassGroup k) = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨1, ?_⟩
      intro y
      refine QuotientGroup.induction_on y ?_
      intro z
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [htop]
      trivial
    omega
  obtain ⟨a, ha⟩ : ∃ a : kˣ, a ∉
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquaresSubgroup k := by
    by_contra h
    apply hsquare_ne_top
    apply (Subgroup.eq_top_iff' _).2
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨u, hu⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_reduction_surjective A a
  refine ⟨u, ?_⟩
  intro hpower
  apply ha
  have hpow : chapter10UnitReduction D.valuation u ∈
      chapter10PowerSubgroup (G := kˣ) 2 := hpower
  rw [show chapter10PowerSubgroup (G := kˣ) 2 =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquaresSubgroup k by
    apply le_antisymm
    · rintro _ ⟨b, rfl⟩
      change b ^ 2 ∈
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquaresSubgroup k
      exact Subgroup.subset_closure ⟨b, rfl⟩
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨b, rfl⟩
      exact ⟨b, rfl⟩] at hpow
  have hu' : chapter10UnitReduction D.valuation u = a := hu
  rw [hu'] at hpow
  exact hpow

/- The square map on principal units is an isomorphism when the residue
   characteristic is odd. -/
theorem chapter10_square_map_on_principal_units_isomorphism
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (hodd : D.residueCharacteristic ≠ 2) :
    ∃ e : Chapter10UnitFiltration D.valuation 1 ≃*
        Chapter10UnitFiltration D.valuation 1,
      ∀ u, e u = u ^ 2 := by
  let A := Chapter10ValuationRing D.valuation
  let k := Chapter10ResidueField D.valuation
  let _ : CharP k D.residueCharacteristic := D.residueCharacteristic_charP
  have h2res : (2 : k) ≠ 0 := by
    intro hzero
    have hdiv : D.residueCharacteristic ∣ 2 :=
      (CharP.cast_eq_zero_iff k D.residueCharacteristic 2).mp hzero
    have hle : D.residueCharacteristic ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hdiv
    exact hodd (Nat.le_antisymm hle D.residueCharacteristic_prime.two_le)
  have h2unit : IsUnit (2 : A) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (2 : A)).mp
    intro hzero
    apply h2res
    exact hzero
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_principal_unit_power_isomorphism
      A 2 h2unit D.complete.2 D.valuationRing_dvr

/- The valuation coordinate and the residue square-class coordinate give the
   two-factor decomposition of the square-class group. -/
theorem chapter10_square_class_group_decomposition
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (hodd : D.residueCharacteristic ≠ 2) :
    Nonempty
      ((Kˣ ⧸ chapter10PowerSubgroup (G := Kˣ) 2) ≃*
        (Multiplicative (ZMod 2) ×
        ((Chapter10ResidueField D.valuation)ˣ ⧸
            chapter10PowerSubgroup
              (G := (Chapter10ResidueField D.valuation)ˣ) 2))) := by
  classical
  let k := Chapter10ResidueField D.valuation
  let A := Chapter10ValuationRing D.valuation
  let _ : CharP k D.residueCharacteristic := D.residueCharacteristic_charP
  have h2res : (2 : k) ≠ 0 := by
    intro hzero
    have hdiv : D.residueCharacteristic ∣ 2 :=
      (CharP.cast_eq_zero_iff k D.residueCharacteristic 2).mp hzero
    have hle : D.residueCharacteristic ≤ 2 :=
      Nat.le_of_dvd (by norm_num) hdiv
    exact hodd (Nat.le_antisymm hle D.residueCharacteristic_prime.two_le)
  have h2unit : IsUnit (2 : A) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (2 : A)).mp
    intro hzero
    apply h2res
    exact hzero
  let _ : Algebra A K := A.subtype.toAlgebra
  let _ : IsFractionRing A K :=
    (Valuation.valuationSubring.integers D.valuation.toValuation).isFractionRing
  have hprincipal :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03PrincipalUnitSquareCondition
        A (IsLocalRing.maximalIdeal A) := by
    exact
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03_complete_odd_dvr_principal_units_are_squares
        A D.complete.2 h2unit
  obtain ⟨e⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03_principal_units_supply_square_class_decomposition
      A K k ⟨RingEquiv.refl _⟩ hprincipal
  have hpowK :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquaresSubgroup K =
        chapter10PowerSubgroup (G := Kˣ) 2 := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro _ ⟨b, rfl⟩
      exact Subgroup.subset_closure ⟨b, rfl⟩
  have hpowk :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquaresSubgroup k =
        chapter10PowerSubgroup (G := kˣ) 2 := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro _ ⟨b, rfl⟩
      exact Subgroup.subset_closure ⟨b, rfl⟩
  let eK :=
    QuotientGroup.quotientMulEquivOfEq hpowK
  let ek :=
    QuotientGroup.quotientMulEquivOfEq hpowk
  refine ⟨eK.symm.trans (e.trans
    (MulEquiv.prodCongr (MulEquiv.refl _) ek))⟩

/- For an odd finite residue field, its multiplicative square-class quotient
   is the remaining one-dimensional factor in the displayed decomposition. -/
theorem chapter10_residue_square_class_group_equiv_zmod_two
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (hodd : D.residueCharacteristic ≠ 2) :
    Nonempty
      (((Chapter10ResidueField D.valuation)ˣ ⧸
          chapter10PowerSubgroup
            (G := (Chapter10ResidueField D.valuation)ˣ) 2) ≃*
        Multiplicative (ZMod 2)) := by
  classical
  let k := Chapter10ResidueField D.valuation
  let _ : CharP k D.residueCharacteristic := D.residueCharacteristic_charP
  obtain ⟨n, _hp, hcard⟩ := FiniteField.card k D.residueCharacteristic
  have hpodd : Odd D.residueCharacteristic :=
    D.residueCharacteristic_prime.eq_two_or_odd'.resolve_left hodd
  have hodd_card : Fintype.card k % 2 = 1 := by
    rw [hcard]
    exact Nat.odd_iff.mp (hpodd.pow)
  let _ : Fintype
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquareClassGroup k) :=
    Fintype.ofFinite _
  have hsquare_card : Fintype.card
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquareClassGroup k) = 2 :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03_finite_odd_field_has_two_square_classes
      k hodd_card
  have hpow :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquaresSubgroup k =
        chapter10PowerSubgroup (G := kˣ) 2 := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨b, rfl⟩
      exact ⟨b, rfl⟩
    · rintro _ ⟨b, rfl⟩
      exact Subgroup.subset_closure ⟨b, rfl⟩
  have hcardq : Nat.card
      (kˣ ⧸ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquaresSubgroup k) = 2 := by
    calc
      Nat.card (kˣ ⧸
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquaresSubgroup k) =
          Fintype.card
            (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.chapter03SquareClassGroup k) :=
        Nat.card_eq_fintype_card
      _ = 2 := hsquare_card
  have hcardq' : Nat.card (kˣ ⧸ chapter10PowerSubgroup (G := kˣ) 2) = 2 := by
    have eqv := QuotientGroup.quotientMulEquivOfEq hpow
    exact (Nat.card_congr eqv.toEquiv).symm.trans hcardq
  have hcardz : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    simp
  exact ⟨mulEquivOfPrimeCardEq hcardq' hcardz⟩

theorem chapter10_square_class_group_is_two_dimensional
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (hodd : D.residueCharacteristic ≠ 2) :
    Nonempty
      ((Kˣ ⧸ chapter10PowerSubgroup (G := Kˣ) 2) ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  obtain ⟨e⟩ := chapter10_square_class_group_decomposition D hodd
  obtain ⟨f⟩ := chapter10_residue_square_class_group_equiv_zmod_two D hodd
  exact ⟨e.trans (MulEquiv.prodCongr (MulEquiv.refl _) f)⟩

theorem chapter10_unramified_quadratic_norm_subgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K)
    (u : Chapter10RingUnitGroup D.valuation) (α : L)
    (hroot : α ^ 2 = algebraMap K L
      ((chapter10RingUnitInField D.valuation u : Kˣ) : K))
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = 2)
    (hnonsquare : chapter10QuadraticResidueNonsquare D u)
    (hodd : D.residueCharacteristic ≠ 2) :
    chapter10NormSubgroup K L =
      chapter10QuadraticUnramifiedNormSubgroup D := by
  sorry

theorem chapter10_sqrt_pi_norm_subgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (s : (Chapter10ResidueField D.valuation)ˣ →*
      Chapter10RingUnitGroup D.valuation)
    (hsred : ∀ a, chapter10UnitReduction D.valuation (s a) = a)
    (hsteich : ∀ a,
      (s a) ^ (Fintype.card (Chapter10ResidueField D.valuation) - 1) = 1)
    (α : L)
    (hroot : α ^ 2 = algebraMap K L (D.uniformizer : K))
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = 2)
    (hodd : D.residueCharacteristic ≠ 2) :
    chapter10NormSubgroup K L =
      chapter10QuadraticSqrtPiNormSubgroup D s := by
  sorry

theorem chapter10_sqrt_unit_pi_norm_subgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (s : (Chapter10ResidueField D.valuation)ˣ →*
      Chapter10RingUnitGroup D.valuation)
    (hsred : ∀ a, chapter10UnitReduction D.valuation (s a) = a)
    (hsteich : ∀ a,
      (s a) ^ (Fintype.card (Chapter10ResidueField D.valuation) - 1) = 1)
    (u : Chapter10RingUnitGroup D.valuation) (α : L)
    (hroot : α ^ 2 = algebraMap K L
      ((chapter10RingUnitInField D.valuation u : Kˣ) : K) *
        algebraMap K L (D.uniformizer : K))
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = 2)
    (hnonsquare : chapter10QuadraticResidueNonsquare D u)
    (hodd : D.residueCharacteristic ≠ 2) :
    chapter10NormSubgroup K L =
      chapter10QuadraticSqrtUnitPiNormSubgroup D s u := by
  sorry

theorem chapter10_three_quadratic_norm_subgroups_distinct
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (s : (Chapter10ResidueField D.valuation)ˣ →*
      Chapter10RingUnitGroup D.valuation)
    [Fintype (Chapter10ResidueField D.valuation)]
    (hsred : ∀ a, chapter10UnitReduction D.valuation (s a) = a)
    (hsteich : ∀ a,
      (s a) ^ (Fintype.card (Chapter10ResidueField D.valuation) - 1) = 1)
    (u : Chapter10RingUnitGroup D.valuation)
    (hnonsquare : chapter10QuadraticResidueNonsquare D u)
    (hodd : D.residueCharacteristic ≠ 2) :
    Nat.card
          (Kˣ ⧸ chapter10QuadraticUnramifiedNormSubgroup D) = 2 ∧
      Nat.card
          (Kˣ ⧸ chapter10QuadraticSqrtPiNormSubgroup D s) = 2 ∧
      Nat.card
          (Kˣ ⧸ chapter10QuadraticSqrtUnitPiNormSubgroup D s u) = 2 ∧
      chapter10QuadraticUnramifiedNormSubgroup D ≠
        chapter10QuadraticSqrtPiNormSubgroup D s ∧
      chapter10QuadraticUnramifiedNormSubgroup D ≠
        chapter10QuadraticSqrtUnitPiNormSubgroup D s u ∧
      chapter10QuadraticSqrtPiNormSubgroup D s ≠
        chapter10QuadraticSqrtUnitPiNormSubgroup D s u ∧
      (chapter10QuadraticUnramifiedNormSubgroup D ⊓
          chapter10QuadraticSqrtPiNormSubgroup D s) ⊓
          chapter10QuadraticSqrtUnitPiNormSubgroup D s u =
      chapter10PowerSubgroup (G := Kˣ) 2 := by
  sorry

/- The common compositum of the three quadratic levels has the intersection
   norm subgroup, namely the square subgroup.  The three norm equalities are
   explicit hypotheses so this bridge can be reused with any chosen radical
   presentations of the fields. -/
theorem chapter10_three_quadratic_compositum_has_square_norm_subgroup
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsAbelianGalois K Ω]
    (D : Chapter10LocalFieldProfile K)
    (s : (Chapter10ResidueField D.valuation)ˣ →*
      Chapter10RingUnitGroup D.valuation)
    (u : Chapter10RingUnitGroup D.valuation)
    (L₀ L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₀] [FiniteDimensional K L₁]
    [FiniteDimensional K L₂]
    [FiniteDimensional K (↥(L₀ ⊔ L₁ ⊔ L₂))]
    (h₀ : chapter10NormSubgroup K L₀ =
      chapter10QuadraticUnramifiedNormSubgroup D)
    (h₁ : chapter10NormSubgroup K L₁ =
      chapter10QuadraticSqrtPiNormSubgroup D s)
    (h₂ : chapter10NormSubgroup K L₂ =
      chapter10QuadraticSqrtUnitPiNormSubgroup D s u) :
    chapter10NormSubgroup K (↥(L₀ ⊔ L₁ ⊔ L₂)) =
      chapter10PowerSubgroup (G := Kˣ) 2 := by
  sorry

/- Wild unit square classes are not visible in the residue field at `p = 2`.
   This is the precise obstruction behind the failure of the three-field
   classification. -/
abbrev Chapter10PrincipalUnitSquareClassGroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K) : Type _ :=
  (Chapter10UnitFiltration D.valuation 1) ⧸
    chapter10PowerSubgroup
      (G := Chapter10UnitFiltration D.valuation 1) 2

theorem chapter10_residue_characteristic_two_has_extra_principal_square_classes
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (hchar : D.residueCharacteristic = 2) :
    Nontrivial (Chapter10PrincipalUnitSquareClassGroup D) := by
  classical
  let A := Chapter10ValuationRing D.valuation
  let k := Chapter10ResidueField D.valuation
  let _ : Algebra A K := A.subtype.toAlgebra
  let _ : IsFractionRing A K :=
    (Valuation.valuationSubring.integers D.valuation.toValuation).isFractionRing
  let _ : CharP k 2 := by
    rw [← hchar]
    exact D.residueCharacteristic_charP
  let U := Chapter10UnitFiltration D.valuation 1
  let H := chapter10PowerSubgroup (G := U) 2
  by_contra hnontrivial
  have hquot_subsingleton : Subsingleton (U ⧸ H) :=
    not_nontrivial_iff_subsingleton.mp hnontrivial
  let _ : Subsingleton (U ⧸ H) := hquot_subsingleton
  have hsq_surj : ∀ x : U, ∃ y : U, y ^ 2 = x := by
    intro x
    have hq : (QuotientGroup.mk' H x) = 1 := Subsingleton.elim _ _
    have hxH : x ∈ H := (QuotientGroup.eq_one_iff _).mp hq
    exact (chapter10_mem_powerSubgroup_iff 2 x).mp hxH
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπmem : π ∈ IsLocalRing.maximalIdeal A := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hπ_not_m2 : π ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
    intro hπ2
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hπ2
    obtain ⟨c, hc⟩ := hπ2
    have hmul : (1 : A) = π * c := by
      apply (mul_left_cancel₀ hπ.ne_zero)
      calc
        π * 1 = π := mul_one π
        _ = π ^ 2 * c := hc
        _ = π * (π * c) := by ring
    have hunit : IsUnit π := isUnit_iff_dvd_one.mpr ⟨c, hmul⟩
    exact hπ.not_isUnit hunit
  have hneg_nonunit : -π ∈ nonunits A := by
    rw [← IsLocalRing.mem_maximalIdeal]
    exact (IsLocalRing.maximalIdeal A).neg_mem hπmem
  have hunit_one_add : IsUnit (1 + π) := by
    have ht := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-π) hneg_nonunit
    simpa [sub_neg_eq_add] using ht
  let u : Aˣ := hunit_one_add.unit
  have huval : (u : A) = 1 + π := IsUnit.unit_spec hunit_one_add
  have huprincipal : (u : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
    simpa [huval] using hπmem
  let x : U := ⟨u, by
    change (u : A) - 1 ∈ (IsLocalRing.maximalIdeal A) ^ 1
    simpa [pow_one] using huprincipal⟩
  obtain ⟨y, hy⟩ := hsq_surj x
  have hsq : (y.1 : A) ^ 2 = (u : A) := by
    have h := congrArg (fun z : U => (z.1 : A)) hy
    simpa [x] using h
  let a : A := (y.1 : A) - 1
  have hyprincipal_pow : (y.1 : A) - 1 ∈
      (IsLocalRing.maximalIdeal A) ^ 1 := by
    exact y.2
  have hyprincipal : (y.1 : A) - 1 ∈ IsLocalRing.maximalIdeal A := by
    simpa [pow_one] using hyprincipal_pow
  have ha : a ∈ IsLocalRing.maximalIdeal A := by
    change (y.1 : A) - 1 ∈ IsLocalRing.maximalIdeal A
    exact hyprincipal
  have hya : (y.1 : A) = 1 + a := by
    simp [a]
  have hrel : π = (2 : A) * a + a ^ 2 := by
    calc
      π = (y.1 : A) ^ 2 - 1 := by rw [hsq, huval]; ring
      _ = (1 + a) ^ 2 - 1 := by rw [hya]
      _ = (2 : A) * a + a ^ 2 := by ring
  have h2 : (2 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change (2 : k) = 0
    exact CharP.cast_eq_zero k 2
  have h2a : (2 : A) * a ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul h2 ha
  have haa : a ^ 2 ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
    simpa [pow_two] using Ideal.mul_mem_mul ha ha
  have hπ2 : π ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
    rw [hrel]
    exact (IsLocalRing.maximalIdeal A) ^ 2 |>.add_mem h2a haa
  exact hπ_not_m2 hπ2

theorem chapter10_residue_characteristic_two_three_quadratic_classification_fails
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (hchar : D.residueCharacteristic = 2) :
    Nat.card (Kˣ ⧸ chapter10PowerSubgroup (G := Kˣ) 2) ≠ 4 := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter10
