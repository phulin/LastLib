import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies

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
  sorry

/- The norm of the chosen radical is the constant-term formula. -/
theorem chapter10_norm_of_tame_radical_root
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e) :
    Algebra.norm K T.root =
      (-1 : K) ^ (e + 1) * (T.unitFactor : K) * (D.uniformizer : K) := by
  sorry

theorem chapter10_norm_of_tame_radical_root_unit_value
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter10LocalFieldProfile K) (e : ℕ)
    (T : Chapter10TameRadicalData D L e) :
    (chapter10NormOfRootUnit T : K) =
      (-1 : K) ^ (e + 1) * (T.unitFactor : K) * (D.uniformizer : K) := by
  sorry

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
  sorry

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
