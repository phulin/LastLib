import LastLib.Book05LocalClassFieldTheory.Chapter10.Dependencies

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
  sorry

/- The square map on principal units is an isomorphism when the residue
   characteristic is odd. -/
theorem chapter10_square_map_on_principal_units_isomorphism
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (hodd : D.residueCharacteristic ≠ 2) :
    ∃ e : Chapter10UnitFiltration D.valuation 1 ≃*
        Chapter10UnitFiltration D.valuation 1,
      ∀ u, e u = u ^ 2 := by
  sorry

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
  sorry

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
  sorry

theorem chapter10_residue_characteristic_two_three_quadratic_classification_fails
    {K : Type*} [Field K] (D : Chapter10LocalFieldProfile K)
    (hchar : D.residueCharacteristic = 2) :
    Nat.card (Kˣ ⧸ chapter10PowerSubgroup (G := Kˣ) 2) ≠ 4 := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter10
