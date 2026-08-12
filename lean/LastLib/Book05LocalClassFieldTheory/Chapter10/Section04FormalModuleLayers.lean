import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter10

noncomputable section

/-! ## 10.4. Formal-module layers -/

noncomputable def chapter10TorsionNormSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) : Subgroup Kˣ := by
  letI : FiniteDimensional K (T.torsionField n) := T.finite n
  exact chapter10NormSubgroup K (T.torsionField n)

abbrev Chapter10TorsionNormQuotient
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) : Type _ :=
  Kˣ ⧸ chapter10TorsionNormSubgroup D T n

def chapter10TorsionValueUnitSubgroup
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (n : ℕ) : Subgroup Kˣ :=
  chapter10ValueUnitSubgroup D D.uniformizer 1 n

/- LOCAL_DEPENDENCY_GUESS: this is the finite-level norm calculation attached
   to the formal-module torsion field. -/
theorem chapter10_formal_torsion_norm_group
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n) :
    chapter10TorsionNormSubgroup D T n =
      chapter10TorsionValueUnitSubgroup D n := by
  sorry

theorem chapter10_formal_torsion_norm_quotient_equiv
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      ((Chapter10TorsionNormQuotient D T n) ≃*
        Chapter10UnitQuotient D.valuation n) := by
  sorry

theorem chapter10_formal_torsion_precision_unit_equiv
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)]
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      (Chapter10UnitQuotient D.valuation n ≃*
        (Chapter10PrecisionQuotient D.valuation n)ˣ) := by
  sorry

theorem chapter10_formal_torsion_extension_degree
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [Fintype (Chapter10ResidueField D.valuation)] :
    Module.finrank K (T.torsionField n) =
      (Fintype.card (Chapter10ResidueField D.valuation) - 1) *
        Fintype.card (Chapter10ResidueField D.valuation) ^ (n - 1) := by
  sorry

theorem chapter10_formal_torsion_norm_quotient_card
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [Fintype (Chapter10ResidueField D.valuation)] :
    Nat.card (Chapter10TorsionNormQuotient D T n) =
      (Fintype.card (Chapter10ResidueField D.valuation) - 1) *
        Fintype.card (Chapter10ResidueField D.valuation) ^ (n - 1) := by
  sorry

/- At level one the formal torsion field contains every finite tame abelian
   totally ramified subextension whose degree divides `q - 1`. -/
theorem chapter10_formal_level_one_captures_tame_abelian_inertia
    {K M : Type*} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω)
    (vM : AddValuation M (WithTop ℤ))
    (hM : Chapter10TotallyRamifiedValuedExtension D.valuation vM 1)
    (hgal : IsGalois K M)
    (habelian : ∀ σ τ : Gal(M / K), σ * τ = τ * σ)
    [Fintype (Chapter10ResidueField D.valuation)]
    (hdegree : Module.finrank K M ∣
      Fintype.card (Chapter10ResidueField D.valuation) - 1) :
    Nonempty (M →ₐ[K] T.torsionField 1) := by
  sorry

/- Each positive unit layer is an additive residue-field layer. -/
theorem chapter10_formal_unit_layer_is_additive_residue_field
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ))
    (n : ℕ) (hn : 0 < n) :
    Nonempty
      (Chapter10UnitFiltration v n ⧸
      (Chapter10UnitFiltration v (n + 1)).subgroupOf
            (Chapter10UnitFiltration v n) ≃*
        Multiplicative (Chapter10ResidueField v)) := by
  sorry

theorem chapter10_formal_unit_layer_card
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    [Fintype (Chapter10ResidueField D.valuation)] (n : ℕ) (hn : 0 < n) :
    Nat.card
        (Chapter10UnitFiltration D.valuation n ⧸
          (Chapter10UnitFiltration D.valuation (n + 1)).subgroupOf
            (Chapter10UnitFiltration D.valuation n)) =
      Fintype.card (Chapter10ResidueField D.valuation) := by
  sorry

theorem chapter10_formal_torsion_layers_are_totally_ramified
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [Fintype (Chapter10ResidueField D.valuation)] :
    ∃ vL : AddValuation (T.torsionField n) (WithTop ℤ),
      Chapter10TotallyRamifiedValuedExtension
        D.valuation vL
        ((Fintype.card (Chapter10ResidueField D.valuation) - 1) *
          Fintype.card (Chapter10ResidueField D.valuation) ^ (n - 1)) := by
  sorry

/- Proposition 10.1: arithmetic reciprocity acts by the inverse formal-unit
   label, with the inverse reduced in the finite quotient `Oˣ/Uⁿ`. -/
theorem chapter10_artin_action_on_formal_torsion
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [FiniteDimensional K (T.torsionField n)]
    (A : Chapter10FiniteArtinMap K (T.torsionField n))
    (u : Chapter10RingUnitGroup D.valuation) :
    A.reciprocity (chapter10RingUnitInField D.valuation u)
        (T.primitivePoint n) =
      T.formalAction n
        (QuotientGroup.mk'
          (Chapter10UnitFiltration D.valuation n) u⁻¹)
        (T.primitivePoint n) := by
  sorry

theorem chapter10_artin_and_torsion_labelings_differ_by_inversion
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [FiniteDimensional K (T.torsionField n)]
    (A : Chapter10FiniteArtinMap K (T.torsionField n)) :
    ∀ u : Chapter10RingUnitGroup D.valuation,
      A.reciprocity (chapter10RingUnitInField D.valuation u) =
        T.torsionLabel n
          (QuotientGroup.mk'
            (Chapter10UnitFiltration D.valuation n) u⁻¹) := by
  sorry

theorem chapter10_artin_of_uniformizer_on_formal_torsion
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    {Ω : Type*} [Field Ω] [Algebra K Ω]
    (T : Chapter10FormalTorsionSystem D Ω) (n : ℕ) (hn : 1 ≤ n)
    [FiniteDimensional K (T.torsionField n)]
    (A : Chapter10FiniteArtinMap K (T.torsionField n)) :
    A.reciprocity D.uniformizer = 1 := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter10
