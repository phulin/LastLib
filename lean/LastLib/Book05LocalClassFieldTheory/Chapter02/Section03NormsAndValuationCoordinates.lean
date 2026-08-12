import LastLib.Book05LocalClassFieldTheory.Chapter02.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter02

noncomputable section

open Function Ideal IsLocalRing
open Filter Topology
open scoped BigOperators Pointwise Topology WithTop

/-! ## 2.3. Norms and valuation coordinates -/

theorem chapter02_mem_norm_subgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (u : Kˣ) :
    u ∈ chapter02NormSubgroup K L ↔
      ∃ x : Lˣ, chapter02NormHom K L x = u := by
  sorry

theorem chapter02_mem_unit_norm_subgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (u : Chapter02UnitGroup vK) :
    u ∈ chapter02UnitNormSubgroup K L vK vL ↔
      ∃ x : Chapter02UnitGroup vL,
        (u : K) = Algebra.norm K (x : L) := by
  sorry

theorem chapter02_norm_unit_map_range_eq_unit_norm_subgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02NormUnitMapData K L vK vL) :
    Subgroup.map d.map ⊤ = chapter02UnitNormSubgroup K L vK vL := by
  sorry

theorem chapter02_norm_unit_field_image_le_norm_subgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02NormUnitMapData K L vK vL) :
    chapter02NormUnitFieldImage K L vK vL d ≤
      chapter02NormSubgroup K L := by
  sorry

theorem chapter02_norm_principal_unit_field_image_le_norm_unit_field_image
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02NormUnitMapData K L vK vL) :
    chapter02NormPrincipalUnitFieldImage K L vK vL d ≤
      chapter02NormUnitFieldImage K L vK vL d := by
  sorry

theorem chapter02_norm_hom_preserves_one
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    chapter02NormHom K L 1 = 1 := by
  simp [chapter02NormHom]

theorem chapter02_norm_hom_preserves_mul
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x y : Lˣ) :
    chapter02NormHom K L (x * y) =
      chapter02NormHom K L x * chapter02NormHom K L y := by
  exact (chapter02NormHom K L).map_mul x y

/- LOCAL_DEPENDENCY_GUESS: the earlier normalized valuation API supplies the
   restriction of the field norm to valuation-ring units. -/
theorem chapter02_norm_unit_map_data_exists
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (f : ℕ)
    (hformula : chapter02NormValuationFormula K L vK vL f)
    (hcompleteK : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing vK))
      (Chapter02ValuationRing vK))
    (hcompleteL : IsAdicComplete
      (IsLocalRing.maximalIdeal (Chapter02ValuationRing vL))
      (Chapter02ValuationRing vL))
    (hDVRK : IsDiscreteValuationRing (Chapter02ValuationRing vK))
    (hDVRL : IsDiscreteValuationRing (Chapter02ValuationRing vL)) :
    Nonempty (Chapter02NormUnitMapData K L vK vL) := by
  sorry

theorem chapter02_norm_valuation_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (f : ℕ)
    (hformula : chapter02NormValuationFormula K L vK vL f) :
    ∀ x : L, x ≠ 0 →
      vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x := by
  exact hformula

theorem chapter02_norm_valuation_image
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (f : ℕ)
    (hformula : chapter02NormValuationFormula K L vK vL f)
    (πL : Lˣ) (hπL : vL (πL : L) = (1 : WithTop ℤ)) :
    chapter02NormValuationImage K L vK vL =
      Set.range (fun z : ℤ => (f : WithTop ℤ) * z) := by
  sorry

theorem chapter02_norm_valuation_image_eq_multiples
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (f : ℕ)
    (hformula : chapter02NormValuationFormula K L vK vL f)
    (πL : Lˣ) (hπL : vL (πL : L) = (1 : WithTop ℤ)) :
    ∀ z : WithTop ℤ,
      z ∈ chapter02NormValuationImage K L vK vL ↔
        ∃ n : ℤ, z = (f : WithTop ℤ) * n := by
  sorry

/- The intersection hypothesis is the exact kernel bridge needed to split a
   norm quotient into its valuation and unit coordinates. -/
theorem chapter02_norm_index_decomposition
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (f : ℕ)
    (hformula : chapter02NormValuationFormula K L vK vL f)
    (πL : Lˣ) (hπL : vL (πL : L) = (1 : WithTop ℤ))
    (hintersection :
      (chapter02NormSubgroup K L).comap (chapter02UnitInclusion vK) =
        chapter02UnitNormSubgroup K L vK vL)
    [Finite (Kˣ ⧸ chapter02NormSubgroup K L)]
    [Finite (Chapter02UnitGroup vK ⧸ chapter02UnitNormSubgroup K L vK vL)] :
    Nat.card (Kˣ ⧸ chapter02NormSubgroup K L) =
      f * Nat.card
        (Chapter02UnitGroup vK ⧸ chapter02UnitNormSubgroup K L vK vL) := by
  sorry

structure Chapter02UnramifiedNormData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) where
  degree : ℕ
  degree_pos : 0 < degree
  degree_eq : Module.finrank K L = degree
  πK : Kˣ
  πL : Lˣ
  πK_uniformizer : vK (πK : K) = (1 : WithTop ℤ)
  πL_uniformizer : vL (πL : L) = (1 : WithTop ℤ)
  valuation_extension :
    vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)
  residue_degree_eq : degree =
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
      vK vL valuation_extension
  common_uniformizer :
    (πL : L) = algebraMap K L (πK : K)
  norm_formula : chapter02NormValuationFormula K L vK vL degree
  units_are_norms :
    chapter02FieldUnitFiltration vK 0 ≤
      (chapter02NormSubgroup K L)
  uniformizer_norm : ∃ u : chapter02FieldUnitFiltration vK 0,
    chapter02NormHom K L πL = πK ^ degree * (u : Kˣ)

theorem chapter02_unramified_norm_group
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02UnramifiedNormData K L vK vL) :
    chapter02NormSubgroup K L =
      chapter02ValueUnitSubgroup vK d.πK d.degree 0 := by
  sorry

theorem chapter02_unramified_norm_index
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02UnramifiedNormData K L vK vL)
    (hcard : Nat.card
        (Kˣ ⧸ chapter02ValueUnitSubgroup vK d.πK d.degree 0) = d.degree) :
    Nat.card (Kˣ ⧸ chapter02NormSubgroup K L) = d.degree := by
  sorry

theorem chapter02_unramified_norm_quotient_generated_by_uniformizer
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02UnramifiedNormData K L vK vL) :
    ∀ x : Kˣ, ∃ z : ℤ,
      QuotientGroup.mk' (chapter02NormSubgroup K L) x =
        (QuotientGroup.mk' (chapter02NormSubgroup K L) d.πK) ^ z := by
  sorry

theorem chapter02_totally_ramified_norm_valuation_unrestricted
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (f : ℕ)
    (hf : f = 1)
    (hformula : chapter02NormValuationFormula K L vK vL f)
    (πL : Lˣ) (hπL : vL (πL : L) = (1 : WithTop ℤ)) :
    chapter02NormValuationImage K L vK vL =
      Set.range (fun z : ℤ => (z : WithTop ℤ)) := by
  sorry

theorem chapter02_totally_ramified_obstruction_is_unit
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (f : ℕ)
    (hf : f = 1)
    (hformula : chapter02NormValuationFormula K L vK vL f)
    (πL : Lˣ) (hπL : vL (πL : L) = (1 : WithTop ℤ)) :
    ∀ x : Kˣ, ∃ y : Kˣ, y ∈ chapter02NormSubgroup K L ∧
      ∃ u : chapter02FieldUnitFiltration vK 0,
        x = y * (u : Kˣ) := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter02
