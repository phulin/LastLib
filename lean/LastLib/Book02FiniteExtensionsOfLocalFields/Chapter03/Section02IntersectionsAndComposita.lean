import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import Mathlib.FieldTheory.LinearDisjoint

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open scoped BigOperators TensorProduct

/-! ## 3.2. Intersections and composita -/

/-- The compositum and intersection inside a fixed overfield. -/
abbrev chapter03Compositum
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω) : IntermediateField K Ω :=
  L₁ ⊔ L₂

abbrev chapter03Intersection
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω) : IntermediateField K Ω :=
  L₁ ⊓ L₂

/-- The compositum/intersection degree identity when one extension is Galois. -/
theorem chapter03_compositum_intersection_degree_of_galois
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsGalois K L₁] :
    Module.finrank K (chapter03Compositum L₁ L₂) *
        Module.finrank K (chapter03Intersection L₁ L₂) =
      Module.finrank K L₁ * Module.finrank K L₂ := by
  sorry

/-- Without a Galois hypothesis, the degree identity becomes an inequality. -/
theorem chapter03_compositum_intersection_degree_inequality
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] :
    Module.finrank K (chapter03Compositum L₁ L₂) *
        Module.finrank K (chapter03Intersection L₁ L₂) ≤
      Module.finrank K L₁ * Module.finrank K L₂ := by
  sorry

/- The numerical profiles below are deliberately parameters: the preceding
chapter supplies the canonical ramification and residue functions, while this
section records the closure and tower interfaces used by the intersection
argument. -/
def chapter03UnramifiedNumerical
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (e : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (L B : IntermediateField K Ω) : Prop :=
  e L B = 1

def chapter03TotallyRamifiedNumerical
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (L B : IntermediateField K Ω) : Prop :=
  f L B = 1

@[simp] theorem chapter03UnramifiedNumerical_iff
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (e : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (L B : IntermediateField K Ω) :
    chapter03UnramifiedNumerical e L B ↔ e L B = 1 := Iff.rfl

@[simp] theorem chapter03TotallyRamifiedNumerical_iff
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (L B : IntermediateField K Ω) :
    chapter03TotallyRamifiedNumerical f L B ↔ f L B = 1 := Iff.rfl

/-- An unramified and a totally ramified extension have trivial intersection
once their tower profiles and degree formula are supplied. -/
theorem chapter03_unramified_totally_ramified_intersection
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (Lᵤ Lₜ : IntermediateField K Ω)
    (e f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (hLᵤ : chapter03UnramifiedNumerical e Lᵤ ⊥)
    (hLₜ : chapter03TotallyRamifiedNumerical f Lₜ ⊥)
    (htowerᵤ : ∀ F : IntermediateField K Ω, F ≤ Lᵤ →
      e Lᵤ ⊥ = e Lᵤ F * e F ⊥)
    (htowerₜ : ∀ F : IntermediateField K Ω, F ≤ Lₜ →
      f Lₜ ⊥ = f Lₜ F * f F ⊥)
    (hdegree : ∀ F : IntermediateField K Ω,
      Module.finrank K F = e F ⊥ * f F ⊥)
    [FiniteDimensional K Lᵤ] [FiniteDimensional K Lₜ] :
    Lᵤ ⊓ Lₜ = ⊥ := by
  sorry

/-- Intermediate fields inherit the unramified profile. -/
theorem chapter03_intermediate_of_unramified_is_unramified
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω)
    (e : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (hL : chapter03UnramifiedNumerical e L ⊥)
    (F : IntermediateField K Ω) (hF : F ≤ L) :
    0 < e L F → e L ⊥ = e L F * e F ⊥ →
    chapter03UnramifiedNumerical e F ⊥ := by
  sorry

/-- Intermediate fields inherit the totally ramified profile. -/
theorem chapter03_intermediate_of_totally_ramified_is_totally_ramified
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω)
    (f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (hL : chapter03TotallyRamifiedNumerical f L ⊥)
    (F : IntermediateField K Ω) (hF : F ≤ L) :
    0 < f L F → f L ⊥ = f L F * f F ⊥ →
    chapter03TotallyRamifiedNumerical f F ⊥ := by
  sorry

/-- The common `e=f=1` profile identifies an intermediate field with the base. -/
theorem chapter03_intermediate_e_one_f_one_is_base
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (F : IntermediateField K Ω)
    (e f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (he : e F ⊥ = 1) (hf : f F ⊥ = 1)
    (hdegree : Module.finrank K F = e F ⊥ * f F ⊥) :
    F = ⊥ := by
  sorry

/-- A Galois extension with trivial intersection is linearly disjoint. -/
theorem chapter03_unramified_galois_extensions_are_linearly_disjoint
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsGalois K L₁] (hinter : L₁ ⊓ L₂ = ⊥) :
    L₁.LinearDisjoint L₂ := by
  sorry

/-- The degree formula for a compositum, isolated as a reusable proposition. -/
def chapter03CompositumDegreeFormula
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω) : Prop :=
  Module.finrank K (chapter03Compositum L₁ L₂) =
    Module.finrank K L₁ * Module.finrank K L₂

theorem chapter03CompositumDegreeFormula_iff
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω) :
    chapter03CompositumDegreeFormula L₁ L₂ ↔
      Module.finrank K (chapter03Compositum L₁ L₂) =
        Module.finrank K L₁ * Module.finrank K L₂ := Iff.rfl

theorem chapter03_compositum_degree_of_linearly_disjoint
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (hld : L₁.LinearDisjoint L₂) :
    chapter03CompositumDegreeFormula L₁ L₂ := by
  sorry

/-- The self-base-change algebra; it need not be a field. -/
abbrev chapter03SelfScalarExtension
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] : Type _ :=
  L ⊗[K] L

def chapter03SelfScalarExtensionSplits
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] (n : ℕ) : Prop :=
  Nonempty (chapter03SelfScalarExtension K L ≃+* (Fin n → L))

/-- A finite Galois self-base-change splits into copies of `L`. -/
theorem chapter03_galois_self_scalar_extension_splits
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∃ n : ℕ, n = Module.finrank K L ∧
      chapter03SelfScalarExtensionSplits K L n := by
  sorry

def chapter03SelfBaseChangeRamificationIndex
    {L F Γ : Type*} [Field L] [Field F] [Algebra L F]
    [LinearOrderedCommGroupWithZero Γ]
    (vL : Valuation L Γ) (vF : Valuation F Γ)
    [vL.HasExtension vF] : ℕ :=
  chapter03RamificationIndex vL vF

/-- Each field factor of the separable self-base change is unramified over
the new base. -/
theorem chapter03_self_scalar_extension_factors_have_e_one
    {K L F Γ : Type*} [Field K] [Field L] [Field F]
    [LinearOrderedCommGroupWithZero Γ]
    [Algebra K L] [Algebra L F] [FiniteDimensional K L]
    [FiniteDimensional L F] [IsGalois K L]
    (vL : Valuation L Γ) (vF : Valuation F Γ)
    [vL.HasExtension vF] [Valuation.IsRankOneDiscrete vL]
    [Valuation.IsRankOneDiscrete vF]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vL.valuationSubring) vL.valuationSubring)
    (hfactor :
      letI : Algebra L (chapter03SelfScalarExtension K L) :=
        Algebra.TensorProduct.rightAlgebra
      Nonempty (chapter03SelfScalarExtension K L ≃ₐ[L] F)) :
    chapter03SelfBaseChangeRamificationIndex vL vF = 1 := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
