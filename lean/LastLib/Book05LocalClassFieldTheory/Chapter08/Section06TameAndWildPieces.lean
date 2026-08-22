import LastLib.Book05LocalClassFieldTheory.Chapter08.Section04UnitAndRamificationTheorem

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

theorem chapter08_ring_principal_units_are_pro_p
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K) :
    chapter08ProPGroup (Chapter08RingUnitFiltration D.valuation 1)
      (chapter08ResidueCharacteristic D.valuation) := by
  sorry

theorem chapter08_field_principal_units_are_pro_p
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K) :
    chapter08ProPGroup (chapter08UnitFiltration D.valuation 1)
      (chapter08ResidueCharacteristic D.valuation) := by
  sorry

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
  sorry

theorem chapter08_tame_wild_decomposition_has_unramified_coordinate
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K)
    (C : Chapter08TameWildCoordinate D) (x : Kˣ) :
    (C.decomposition x).1 =
      Multiplicative.toAdd (D.coordinate.valuation x) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter08
