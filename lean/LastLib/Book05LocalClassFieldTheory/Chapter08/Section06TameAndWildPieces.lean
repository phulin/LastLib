import LastLib.Book05LocalClassFieldTheory.Chapter08.Section04UnitAndRamificationTheorem
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section04MultiplicationPowersAndResidueCharacteristic

namespace LastLib.Book05LocalClassFieldTheory.Chapter08

noncomputable section

open scoped IsMulCommutative Pointwise

local instance chapter08_section06_isMulCommutative_of_commGroup
    {G : Type*} [CommGroup G] : IsMulCommutative G :=
  IsMulCommutative.of_comm (fun _ _ => mul_comm _ _)

/-! ## 8.6. Tame and wild pieces -/

abbrev chapter08ResidueUnitQuotient
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  Chapter08RingUnitGroup v ⧸ Chapter08RingUnitFiltration v 1

theorem chapter08_residue_unit_quotient_equiv_residue_units
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Nonempty
      (chapter08ResidueUnitQuotient v ≃*
        (Chapter08ResidueField v)ˣ) := by
  exact LastLib.Book05LocalClassFieldTheory.Chapter02.chapter02_unit_filtration_first_quotient v

theorem chapter08_residue_unit_quotient_is_cyclic
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [Finite (Chapter08ResidueField v)] :
    IsCyclic (chapter08ResidueUnitQuotient v) := by
  exact (chapter08_residue_unit_quotient_equiv_residue_units v).some.isCyclic.mpr
    (by infer_instance)

theorem chapter08_residue_unit_quotient_card
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [Finite (Chapter08ResidueField v)] :
    Nat.card (chapter08ResidueUnitQuotient v) =
      Nat.card (Chapter08ResidueField v) - 1 := by
  rcases chapter08_residue_unit_quotient_equiv_residue_units v with ⟨e⟩
  calc
    Nat.card (chapter08ResidueUnitQuotient v) =
        Nat.card ((Chapter08ResidueField v)ˣ) := Nat.card_congr e.toEquiv
    _ = Nat.card (Chapter08ResidueField v) - 1 := Nat.card_units _

theorem chapter08_residue_unit_quotient_prime_to_residue_characteristic
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    [Finite (Chapter08ResidueField v)] :
    Nat.Coprime
      (Nat.card (chapter08ResidueUnitQuotient v))
      (chapter08ResidueCharacteristic v) := by
  let _ := Fintype.ofFinite (Chapter08ResidueField v)
  obtain ⟨n, hp, hcard⟩ :=
    FiniteField.card (Chapter08ResidueField v) (chapter08ResidueCharacteristic v)
  rw [chapter08_residue_unit_quotient_card v,
    Nat.card_eq_fintype_card, hcard]
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro h
  have hpow : chapter08ResidueCharacteristic v ∣
      chapter08ResidueCharacteristic v ^ (n : ℕ) :=
    dvd_pow_self _ n.ne_zero
  have hone : chapter08ResidueCharacteristic v ∣ 1 := by
    have hd := Nat.dvd_sub hpow h
    rw [tsub_tsub_cancel_of_le (Nat.one_le_pow _ _ hp.pos)] at hd
    exact hd
  exact hp.not_dvd_one hone

abbrev chapter08TameInertiaQuotient
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L) : Type _ :=
  (chapter08UnitFiltration X.base.valuation 0).map
      (chapter08FiniteReciprocityMap D) ⧸
    ((chapter08UnitFiltration X.base.valuation 1).map
        (chapter08FiniteReciprocityMap D)).subgroupOf
      ((chapter08UnitFiltration X.base.valuation 0).map
        (chapter08FiniteReciprocityMap D))

theorem chapter08_residue_units_identify_with_tame_abelian_inertia
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F) :
    Nonempty
      (chapter08ResidueUnitQuotient X.base.valuation ≃*
        chapter08TameInertiaQuotient X D) := by
  sorry

def chapter08WildAbelianInertia
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L) : Subgroup (Gal(L / K)) :=
  (chapter08UnitFiltration X.base.valuation 1).map
    (chapter08FiniteReciprocityMap D)

theorem chapter08_principal_units_are_wild_abelian_inertia
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F) :
    chapter08WildAbelianInertia X D = chapter08UpperGroup F 1 := by
  change (chapter08UnitFiltration X.base.valuation 1).map
      (chapter08FiniteReciprocityMap D) = chapter08UpperGroup F 1
  simpa only [Nat.cast_one] using
    (chapter08_unit_and_upper_ramification X D F P 1)

theorem chapter08_higher_principal_units_are_higher_abelian_ramification
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (D : Chapter08FiniteReciprocityData K L)
    (F : Chapter08RamificationFiltration (Gal(L / K)))
    (P : Chapter08UnitRamificationInput X F) (n : ℕ) :
    (chapter08UnitFiltration X.base.valuation n).map
        (chapter08FiniteReciprocityMap D) =
      chapter08UpperGroup F n := by
  exact chapter08_unit_and_upper_ramification X D F P n

private theorem chapter08_finite_index_quotient_is_p_power
    {G : Type*} [CommGroup G] (p : ℕ)
    (H : Subgroup G) (hH : H.FiniteIndex)
    (hpow : ∀ q : ℕ, Nat.Prime q → q ≠ p →
      Function.Surjective (fun x : G => x ^ q)) :
    ∃ n : ℕ, Nat.card (G ⧸ H) = p ^ n := by
  classical
  let _ : H.FiniteIndex := hH
  have hprime_not_dvd (q : ℕ) (hq : Nat.Prime q) (hqp : q ≠ p) :
      ¬q ∣ Nat.card (G ⧸ H) := by
    intro hqcard
    let _ : Fact (Nat.Prime q) := ⟨hq⟩
    have hsurj : Function.Surjective (fun x : G ⧸ H => x ^ q) := by
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H z
      obtain ⟨y, hy⟩ := hpow q hq hqp x
      refine ⟨QuotientGroup.mk' H y, ?_⟩
      change QuotientGroup.mk' H (y ^ q) = QuotientGroup.mk' H x
      exact congrArg (QuotientGroup.mk' H) hy
    have hinj : Function.Injective (fun x : G ⧸ H => x ^ q) :=
      (Finite.injective_iff_surjective).2 hsurj
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hqcard
    have hxeq : x = 1 := by
      apply hinj
      change x ^ q = (1 : G ⧸ H) ^ q
      rw [← hx, pow_orderOf_eq_one]
      simp
    exact hq.ne_one (by simpa [hxeq] using hx.symm)
  let c := Nat.card (G ⧸ H)
  have hc : c ≠ 0 := by
    exact (Nat.card_ne_zero).2 ⟨⟨1⟩, inferInstance⟩
  let k := c.factorization p
  have hk : c.factorization = Finsupp.single p k := by
    ext q
    by_cases hqp' : q = p
    · subst q
      simp [k]
    · simp only [Finsupp.single_apply, if_neg (Ne.symm hqp')]
      by_cases hq : Nat.Prime q
      · exact (Nat.factorization_eq_zero_iff c q).2
          (Or.inr (Or.inl (hprime_not_dvd q hq hqp')))
      · exact (Nat.factorization_eq_zero_iff c q).2 (Or.inl hq)
  refine ⟨k, ?_⟩
  exact Nat.eq_pow_of_factorization_eq_single hc hk

theorem chapter08_ring_principal_units_are_pro_p
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K) :
    chapter08ProPGroup (Chapter08RingUnitFiltration D.valuation 1)
      (chapter08ResidueCharacteristic D.valuation) := by
  intro H hH
  let _ : Finite (Chapter08ResidueField D.valuation) := D.localField.2
  let _ : Fintype (Chapter08ResidueField D.valuation) := Fintype.ofFinite _
  let _ : Valuation.IsRankOneDiscrete D.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      D.valuation D.localField.1.1
  let _ : Nontrivial
      (MonoidWithZeroHom.valueGroup (.ofClass D.valuation.toValuation)) :=
    ⟨⟨Valuation.IsRankOneDiscrete.generator' D.valuation.toValuation, 1,
      ne_of_lt (Valuation.IsRankOneDiscrete.generator'_lt_one
        D.valuation.toValuation)⟩⟩
  have hDVR : IsDiscreteValuationRing D.valuation.toValuation.valuationSubring := by
    infer_instance
  have hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal D.valuation.toValuation.valuationSubring)
      D.valuation.toValuation.valuationSubring :=
    D.localField.1.2
  have hp : Nat.Prime (chapter08ResidueCharacteristic D.valuation) :=
    CharP.prime_ringChar _
  apply chapter08_finite_index_quotient_is_p_power
    (chapter08ResidueCharacteristic D.valuation) H hH
  intro q hq hqp
  have hqunit :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10IntegerIsUnit
        D.valuation.toValuation.valuationSubring q := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit
      (q : D.valuation.toValuation.valuationSubring)).mp
    intro hzero
    have hcast : (q : Chapter08ResidueField D.valuation) = 0 := by
      simpa using hzero
    have hdiv : chapter08ResidueCharacteristic D.valuation ∣ q :=
      (CharP.cast_eq_zero_iff (Chapter08ResidueField D.valuation)
        (chapter08ResidueCharacteristic D.valuation) q).mp hcast
    rcases (Nat.dvd_prime hq).mp hdiv with hpone | hpeq
    · exact hp.ne_one hpone
    · exact hqp hpeq.symm
  obtain ⟨e, he⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_principal_unit_power_isomorphism
      D.valuation.toValuation.valuationSubring q hqunit hcomplete hDVR
  intro u
  obtain ⟨v, hv⟩ := e.surjective u
  refine ⟨v, ?_⟩
  exact (he v).symm.trans hv

theorem chapter08_field_principal_units_are_pro_p
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K) :
    chapter08ProPGroup (chapter08UnitFiltration D.valuation 1)
      (chapter08ResidueCharacteristic D.valuation) := by
  intro H hH
  let _ : Finite (Chapter08ResidueField D.valuation) := D.localField.2
  let _ : Fintype (Chapter08ResidueField D.valuation) := Fintype.ofFinite _
  let _ : Valuation.IsRankOneDiscrete D.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      D.valuation D.localField.1.1
  let _ : Nontrivial
      (MonoidWithZeroHom.valueGroup (.ofClass D.valuation.toValuation)) :=
    ⟨⟨Valuation.IsRankOneDiscrete.generator' D.valuation.toValuation, 1,
      ne_of_lt (Valuation.IsRankOneDiscrete.generator'_lt_one
        D.valuation.toValuation)⟩⟩
  have hDVR : IsDiscreteValuationRing D.valuation.toValuation.valuationSubring := by
    infer_instance
  have hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal D.valuation.toValuation.valuationSubring)
      D.valuation.toValuation.valuationSubring :=
    D.localField.1.2
  have hp : Nat.Prime (chapter08ResidueCharacteristic D.valuation) :=
    CharP.prime_ringChar _
  apply chapter08_finite_index_quotient_is_p_power
    (chapter08ResidueCharacteristic D.valuation) H hH
  intro q hq hqp
  have hqunit :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10IntegerIsUnit
        D.valuation.toValuation.valuationSubring q := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit
      (q : D.valuation.toValuation.valuationSubring)).mp
    intro hzero
    have hcast : (q : Chapter08ResidueField D.valuation) = 0 := by
      simpa using hzero
    have hdiv : chapter08ResidueCharacteristic D.valuation ∣ q :=
      (CharP.cast_eq_zero_iff (Chapter08ResidueField D.valuation)
        (chapter08ResidueCharacteristic D.valuation) q).mp hcast
    rcases (Nat.dvd_prime hq).mp hdiv with hpone | hpeq
    · exact hp.ne_one hpone
    · exact hqp hpeq.symm
  obtain ⟨e, he⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_principal_unit_power_isomorphism
      D.valuation.toValuation.valuationSubring q hqunit hcomplete hDVR
  intro u
  rcases u.property with ⟨r, hr, hru⟩
  let r' : Chapter08RingUnitFiltration D.valuation 1 := ⟨r, hr⟩
  obtain ⟨s, hs⟩ := e.surjective r'
  let v : chapter08UnitFiltration D.valuation 1 :=
    ⟨chapter08RingUnitInclusion D.valuation (s : Chapter08RingUnitGroup D.valuation),
      ⟨s, s.property, rfl⟩⟩
  refine ⟨v, ?_⟩
  apply Subtype.ext
  change (chapter08RingUnitInclusion D.valuation
      (s : Chapter08RingUnitGroup D.valuation)) ^ q = (u : Kˣ)
  rw [← map_pow]
  have hspow : s ^ q = r' := (he s).symm.trans hs
  have hspow' := congrArg
    (fun z : Chapter08RingUnitFiltration D.valuation 1 =>
      chapter08RingUnitInclusion D.valuation (z : Chapter08RingUnitGroup D.valuation)) hspow
  exact hspow'.trans hru

private theorem chapter08_coordinate_unit_decomposition
    {K : Type*} [Field K] (D : Chapter08LocalFieldData K) :
    ∃ e : Kˣ ≃*
        (Multiplicative ℤ × Chapter08RingUnitGroup D.valuation),
      (∀ x : Kˣ,
        (e x).1 = D.coordinate.valuation x) ∧
      (∀ u : Chapter08RingUnitGroup D.valuation,
        e (chapter08RingUnitInclusion D.valuation u) = (1, u)) := by
  classical
  let n : Kˣ → ℤ := fun x => Multiplicative.toAdd (D.coordinate.valuation x)
  have hval_zpow (m : ℤ) :
      D.coordinate.valuation (D.uniformizer ^ m) = Multiplicative.ofAdd m := by
    rw [map_zpow, D.uniformizer_coordinate]
    rw [← ofAdd_zsmul]
    simp
  have hker_unit (u : Chapter08RingUnitGroup D.valuation) :
      D.coordinate.valuation (chapter08RingUnitInclusion D.valuation u) = 1 :=
    (D.coordinate.exact.2.1 _).mpr ⟨u, rfl⟩
  have hfactor (x : Kˣ) :
      ∃ u : Chapter08RingUnitGroup D.valuation,
        x = D.uniformizer ^ n x * chapter08RingUnitInclusion D.valuation u := by
    let q : Kˣ := x * (D.uniformizer ^ n x)⁻¹
    have hqval : D.coordinate.valuation q = 1 := by
      dsimp [q]
      rw [map_mul, map_inv, hval_zpow, ofAdd_toAdd]
      exact mul_inv_cancel _
    have hqker : q ∈ D.coordinate.valuation.ker :=
      MonoidHom.mem_ker.mpr hqval
    have hqrange : q ∈ (chapter08RingUnitInclusion D.valuation).range := by
      change q ∈
        (LastLib.Book05LocalClassFieldTheory.Chapter02.chapter02UnitInclusion
          D.valuation).range
      rw [← (MonoidHom.mulExact_iff.mp D.coordinate.exact.2.1)]
      exact hqker
    obtain ⟨u, hu⟩ := hqrange
    refine ⟨u, ?_⟩
    calc
      x = q * D.uniformizer ^ n x := by dsimp [q]; group
      _ = chapter08RingUnitInclusion D.valuation u * D.uniformizer ^ n x := by
        rw [hu]
      _ = D.uniformizer ^ n x * chapter08RingUnitInclusion D.valuation u := by
        ac_rfl
  choose u hfactor using hfactor
  have hunique (x : Kˣ) (m : ℤ) (w : Chapter08RingUnitGroup D.valuation)
      (h : x = D.uniformizer ^ m * chapter08RingUnitInclusion D.valuation w) :
      m = n x ∧ w = u x := by
    have hcoord_m : D.coordinate.valuation x =
        D.coordinate.valuation (D.uniformizer ^ m) := by
      calc
        D.coordinate.valuation x =
            D.coordinate.valuation
              (D.uniformizer ^ m * chapter08RingUnitInclusion D.valuation w) :=
          congrArg D.coordinate.valuation h
        _ = D.coordinate.valuation (D.uniformizer ^ m) := by
          rw [map_mul, hker_unit, mul_one]
    have hcoord_n : D.coordinate.valuation x =
        D.coordinate.valuation (D.uniformizer ^ n x) := by
      calc
        D.coordinate.valuation x =
            D.coordinate.valuation
              (D.uniformizer ^ n x * chapter08RingUnitInclusion D.valuation (u x)) :=
          congrArg D.coordinate.valuation (hfactor x)
        _ = D.coordinate.valuation (D.uniformizer ^ n x) := by
          rw [map_mul, hker_unit, mul_one]
    have hmnval : D.coordinate.valuation (D.uniformizer ^ m) =
        D.coordinate.valuation (D.uniformizer ^ n x) :=
      hcoord_m.symm.trans hcoord_n
    have hmnval' : Multiplicative.ofAdd m =
        Multiplicative.ofAdd (n x) :=
      (hval_zpow m).symm.trans (hmnval.trans (hval_zpow (n x)))
    have hmn : m = n x := Multiplicative.ofAdd.injective hmnval'
    have hunit : chapter08RingUnitInclusion D.valuation w =
        chapter08RingUnitInclusion D.valuation (u x) := by
      apply mul_left_cancel (a := D.uniformizer ^ n x)
      rw [hmn] at h
      exact h.symm.trans (hfactor x)
    exact ⟨hmn,
      LastLib.Book05LocalClassFieldTheory.Chapter02.chapter02_valuation_sequence_is_injective_on_units
        D.valuation hunit⟩
  let f : Kˣ →* (Multiplicative ℤ × Chapter08RingUnitGroup D.valuation) :=
    { toFun := fun x => (Multiplicative.ofAdd (n x), u x)
      map_one' := by
        have h := hunique 1 0 1 (by simp)
        apply Prod.ext
        · change n 1 = 0
          exact h.1.symm
        · exact h.2.symm
      map_mul' := by
        intro x y
        have hxy : x * y =
            D.uniformizer ^ (n x + n y) *
              chapter08RingUnitInclusion D.valuation (u x * u y) := by
          calc
            x * y =
                (D.uniformizer ^ n x * chapter08RingUnitInclusion D.valuation (u x)) *
                  (D.uniformizer ^ n y * chapter08RingUnitInclusion D.valuation (u y)) := by
              exact congrArg₂ (· * ·) (hfactor x) (hfactor y)
            _ = (D.uniformizer ^ n x * D.uniformizer ^ n y) *
                (chapter08RingUnitInclusion D.valuation (u x) *
                  chapter08RingUnitInclusion D.valuation (u y)) := by ac_rfl
            _ = D.uniformizer ^ (n x + n y) *
                chapter08RingUnitInclusion D.valuation (u x * u y) := by
              rw [← zpow_add, map_mul]
        have h := hunique (x * y) (n x + n y) (u x * u y) hxy
        apply Prod.ext
        · change n (x * y) = n x + n y
          exact h.1.symm
        · exact h.2.symm }
  let g : (Multiplicative ℤ × Chapter08RingUnitGroup D.valuation) →* Kˣ :=
    { toFun := fun z =>
        D.uniformizer ^ (Multiplicative.toAdd z.1) *
          chapter08RingUnitInclusion D.valuation z.2
      map_one' := by simp
      map_mul' := by
        intro z w
        change D.uniformizer ^
            (Multiplicative.toAdd z.1 + Multiplicative.toAdd w.1) *
            chapter08RingUnitInclusion D.valuation (z.2 * w.2) =
          (D.uniformizer ^ Multiplicative.toAdd z.1 *
            chapter08RingUnitInclusion D.valuation z.2) *
            (D.uniformizer ^ Multiplicative.toAdd w.1 *
              chapter08RingUnitInclusion D.valuation w.2)
        rw [zpow_add, map_mul]
        ac_rfl }
  have hfg : ∀ x : Kˣ, g (f x) = x := by
    intro x
    change D.uniformizer ^ n x *
        chapter08RingUnitInclusion D.valuation (u x) = x
    exact (hfactor x).symm
  have hgf : ∀ z : Multiplicative ℤ × Chapter08RingUnitGroup D.valuation,
      f (g z) = z := by
    intro z
    have hz : g z = D.uniformizer ^ (Multiplicative.toAdd z.1) *
        chapter08RingUnitInclusion D.valuation z.2 := by
      rfl
    have h := hunique (g z) (Multiplicative.toAdd z.1) z.2 hz
    apply Prod.ext
    · change n (g z) = Multiplicative.toAdd z.1
      exact h.1.symm
    · exact h.2.symm
  let e : Kˣ ≃* (Multiplicative ℤ × Chapter08RingUnitGroup D.valuation) :=
    { toFun := fun x => f x
      invFun := fun z => g z
      left_inv := hfg
      right_inv := hgf
      map_mul' := by
        intro x y
        exact f.map_mul x y }
  refine ⟨e, ?_, ?_⟩
  · intro x
    rfl
  · intro u₀
    have h := hunique (chapter08RingUnitInclusion D.valuation u₀) 0 u₀ (by simp)
    apply Prod.ext
    · change n (chapter08RingUnitInclusion D.valuation u₀) = 0
      exact h.1.symm
    · exact h.2.symm

private theorem chapter08_unit_coordinate_split
    {K : Type*} [Field K] (D : Chapter08LocalFieldData K) :
    ∃ e : (D.valuation.toValuation.valuationSubring)ˣ ≃*
        ((Chapter08ResidueField D.valuation)ˣ ×
          Chapter08RingUnitFiltration D.valuation 1),
      ∀ u : Chapter08RingUnitFiltration D.valuation 1,
        (e (u : (D.valuation.toValuation.valuationSubring)ˣ)).1 = 1 := by
  classical
  let _ : Finite (Chapter08ResidueField D.valuation) := D.localField.2
  let _ : Fintype (Chapter08ResidueField D.valuation) := Fintype.ofFinite _
  let _ : Valuation.IsRankOneDiscrete D.valuation.toValuation :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      D.valuation D.localField.1.1
  let _ : Nontrivial
      (MonoidWithZeroHom.valueGroup (.ofClass D.valuation.toValuation)) :=
    ⟨⟨Valuation.IsRankOneDiscrete.generator' D.valuation.toValuation, 1,
      ne_of_lt (Valuation.IsRankOneDiscrete.generator'_lt_one
        D.valuation.toValuation)⟩⟩
  have hDVR : IsDiscreteValuationRing D.valuation.toValuation.valuationSubring := by
    infer_instance
  have hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal D.valuation.toValuation.valuationSubring)
      D.valuation.toValuation.valuationSubring :=
    D.localField.1.2
  obtain ⟨s, hs, _hsunique⟩ :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_teichmuller_section_exists_unique
      D.valuation.toValuation.valuationSubring hcomplete hDVR
  rcases hs with ⟨hsred, _hspow, _hsuniq⟩
  let red :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitReduction
      D.valuation.toValuation.valuationSubring
  have w_mem (u : (D.valuation.toValuation.valuationSubring)ˣ) :
      (s (red u))⁻¹ * u ∈
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
          D.valuation.toValuation.valuationSubring 1 := by
    rw [← LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_reduction_kernel
      D.valuation.toValuation.valuationSubring]
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hsred]
    exact inv_mul_cancel _
  let w : (D.valuation.toValuation.valuationSubring)ˣ →*
      Chapter08RingUnitFiltration D.valuation 1 :=
    { toFun := fun u => ⟨(s (red u))⁻¹ * u, w_mem u⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        change (s (red (u * v)))⁻¹ * (u * v) =
          ((s (red u))⁻¹ * u) * ((s (red v))⁻¹ * v)
        rw [map_mul, map_mul, mul_inv_rev]
        ac_rfl }
  let e : (D.valuation.toValuation.valuationSubring)ˣ ≃*
      ((Chapter08ResidueField D.valuation)ˣ ×
        Chapter08RingUnitFiltration D.valuation 1) :=
    { toFun := fun u => (red u, w u)
      invFun := fun x => s x.1 * (x.2 : (D.valuation.toValuation.valuationSubring)ˣ)
      left_inv := by
        intro u
        change s (red u) * ((s (red u))⁻¹ * u) = u
        simp
      right_inv := by
        intro x
        have hx2ker :
            (x.2 : (D.valuation.toValuation.valuationSubring)ˣ) ∈ red.ker := by
          change (x.2 : (D.valuation.toValuation.valuationSubring)ˣ) ∈
            (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitReduction
              D.valuation.toValuation.valuationSubring).ker
          rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_reduction_kernel
            D.valuation.toValuation.valuationSubring]
          exact x.2.property
        have hx2red : red (x.2 : (D.valuation.toValuation.valuationSubring)ˣ) = 1 :=
          MonoidHom.mem_ker.mp hx2ker
        have hprodred :
            red (s x.1 * (x.2 : (D.valuation.toValuation.valuationSubring)ˣ)) = x.1 := by
          rw [map_mul, hsred, hx2red, mul_one]
        apply Prod.ext
        · exact hprodred
        · change w (s x.1 * (x.2 : (D.valuation.toValuation.valuationSubring)ˣ)) = x.2
          apply Subtype.ext
          change (s (red (s x.1 *
            (x.2 : (D.valuation.toValuation.valuationSubring)ˣ))))⁻¹ *
              (s x.1 * (x.2 : (D.valuation.toValuation.valuationSubring)ˣ)) =
            (x.2 : (D.valuation.toValuation.valuationSubring)ˣ)
          rw [hprodred]
          simp
      map_mul' := by
        intro u v
        apply Prod.ext
        · exact red.map_mul u v
        · exact w.map_mul u v }
  refine ⟨e, ?_⟩
  intro u
  have hker : (u : (D.valuation.toValuation.valuationSubring)ˣ) ∈ red.ker := by
    change (u : (D.valuation.toValuation.valuationSubring)ˣ) ∈
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitReduction
        D.valuation.toValuation.valuationSubring).ker
    rw [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10_unit_reduction_kernel
      D.valuation.toValuation.valuationSubring]
    exact u.property
  exact MonoidHom.mem_ker.mp hker

theorem chapter08_principal_unit_finite_quotients_have_p_power_order
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K)
    (H : Subgroup (chapter08UnitFiltration D.valuation 1))
    (hH : H.FiniteIndex) :
    ∃ n : ℕ,
      Nat.card ((chapter08UnitFiltration D.valuation 1) ⧸ H) =
        (chapter08ResidueCharacteristic D.valuation) ^ n := by
  exact chapter08_field_principal_units_are_pro_p D H hH

/- The Teichmüller and uniformizer choices are represented by a nonempty
   coordinate type; the final factor is the only one carrying positive unit
   depth. -/
structure Chapter08TameWildCoordinate
    {K : Type*} [Field K] (D : Chapter08LocalFieldData K) where
  decomposition : Kˣ ≃* Chapter08TameWildProduct D
  higher_unit_in_wild_factor : ∀ n : ℕ, 1 ≤ n → ∀ x : Kˣ,
    x ∈ chapter08UnitFiltration D.valuation n →
      ∃ w : Chapter08RingUnitFiltration D.valuation 1,
        decomposition x = (1, (1, w))

theorem chapter08_tame_wild_multiplicative_decomposition
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K) :
    Nonempty (Chapter08TameWildCoordinate D) := by
  obtain ⟨eVal, _heValCoord, heValUnit⟩ :=
    chapter08_coordinate_unit_decomposition D
  obtain ⟨eUnit, heUnitPrincipal⟩ := chapter08_unit_coordinate_split D
  let e : Kˣ ≃* Chapter08TameWildProduct D :=
    eVal.trans (MulEquiv.prodCongr (MulEquiv.refl _) eUnit)
  refine ⟨{ decomposition := e, higher_unit_in_wild_factor := ?_ }⟩
  intro n hn x hx
  rcases hx with ⟨u, hu, hux⟩
  change chapter08RingUnitInclusion D.valuation u = x at hux
  have hu1 : u ∈ Chapter08RingUnitFiltration D.valuation 1 := by
    change ((u : (D.valuation.toValuation.valuationSubring)ˣ) :
      D.valuation.toValuation.valuationSubring) - 1 ∈
      (IsLocalRing.maximalIdeal D.valuation.toValuation.valuationSubring) ^ 1
    change ((u : (D.valuation.toValuation.valuationSubring)ˣ) :
      D.valuation.toValuation.valuationSubring) - 1 ∈
      (IsLocalRing.maximalIdeal D.valuation.toValuation.valuationSubring) ^ n at hu
    exact (Ideal.pow_le_pow_right hn) hu
  let u1 : Chapter08RingUnitFiltration D.valuation 1 := ⟨u, hu1⟩
  refine ⟨(eUnit (u1 : (D.valuation.toValuation.valuationSubring)ˣ)).2, ?_⟩
  change (MulEquiv.prodCongr (MulEquiv.refl _) eUnit) (eVal x) =
    (1, (1, (eUnit (u1 : (D.valuation.toValuation.valuationSubring)ˣ)).2))
  rw [← hux, heValUnit]
  change (1, eUnit (u1 : (D.valuation.toValuation.valuationSubring)ˣ)) = _
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact heUnitPrincipal u1
    · rfl

theorem chapter08_tame_wild_decomposition_has_unramified_coordinate
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K)
    (C : Chapter08TameWildCoordinate D) (x : Kˣ) :
    (C.decomposition x).1 =
      Multiplicative.toAdd (D.coordinate.valuation x) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter08
