import LastLib.Book05LocalClassFieldTheory.Chapter06.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter06

noncomputable section

open scoped BigOperators

/-!
### 6.1. Why a separate existence construction is necessary
-/

/-- The explicit finite-precision subgroups occurring in the source. -/
def chapter06PrecisionFamily
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) :
    Set (Subgroup Kˣ) :=
  {H | ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ H = chapter06PrecisionSubgroup D m n}

/- SOURCE_WARNING (§6.2, after the independence discussion): the precision
   and torsion coordinates retain the chosen uniformizer.  The intrinsic
   object is the resulting family of extensions, not a canonical equality of
   coordinate presentations attached to two different uniformizers. -/

theorem chapter06_mem_precisionFamily_iff
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (H : Subgroup Kˣ) :
    H ∈ chapter06PrecisionFamily D ↔
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ H = chapter06PrecisionSubgroup D m n :=
  Iff.rfl

/-- The valuation and unit directions commute in the multiplicative group. -/
theorem chapter06_precisionSubgroup_is_product
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) (x : Kˣ) :
    x ∈ chapter06PrecisionSubgroup D m n ↔
      ∃ z : ℤ, ∃ u : Kˣ,
        u ∈ Chapter06UnitFiltration D n ∧
          x = (chapter06UniformizerUnit D) ^ (m * z) * u := by
  exact chapter06_mem_precisionSubgroup_iff D m n x

/- The finite-index statement is the precise form of the “cofinal family”
claim; the finite residue field is used through the cardinality of the unit
layers. -/
theorem chapter06_precisionSubgroup_finite_index
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Finite (Kˣ ⧸ chapter06PrecisionSubgroup D m n) := by
  sorry

theorem chapter06_precisionSubgroup_index
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Nat.card (Kˣ ⧸ chapter06PrecisionSubgroup D m n) =
      m * (chapter06ResidueCardinality D - 1) *
        chapter06ResidueCardinality D ^ (n - 1) := by
  sorry

/-- Every open finite-index subgroup contains a displayed precision subgroup.
This is the local-field form of Proposition 2.1 used by the chapter. -/
theorem chapter06_open_finite_index_contains_precision
    {K : Type*} [Field K]
    (D : Chapter06LocalFieldData K)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D)
    (H : Subgroup Kˣ) (hopen : IsOpen (H : Set Kˣ))
    (hfinite : H.FiniteIndex) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      chapter06PrecisionSubgroup D m n ≤ H := by
  sorry

theorem chapter06_precision_cofinality
    {K : Type*} [Field K]
    (D : Chapter06LocalFieldData K)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (htop : Chapter06UnitFiltrationNeighborhoodBasis D) :
    Chapter06PrecisionCofinality D htop := by
  intro H hopen hfinite
  exact chapter06_open_finite_index_contains_precision D htop H hopen hfinite

/-- The norm subgroup of a totally ramified level will be the unit precision
subgroup; this declaration keeps the two pieces separate until Section 5. -/
def chapter06RamifiedPrecisionSubgroup
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (n : ℕ) :
    Subgroup Kˣ :=
  Chapter06UnitFiltration D n

theorem chapter06_precision_family_realizes_valuation_and_unit_parts
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) :
    chapter06PrecisionSubgroup D m n =
      Subgroup.zpowers ((chapter06UniformizerUnit D) ^ m) ⊔
        chapter06RamifiedPrecisionSubgroup D n := by
  rfl

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
