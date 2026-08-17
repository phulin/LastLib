import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.Galois.NormalBasis

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open scoped BigOperators TensorProduct

open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

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
  let A' : IntermediateField (↥(L₁ ⊓ L₂)) Ω :=
    IntermediateField.extendScalars (F := L₁ ⊓ L₂) (E := L₁) inf_le_left
  let B' : IntermediateField (↥(L₁ ⊓ L₂)) Ω :=
    IntermediateField.extendScalars (F := L₁ ⊓ L₂) (E := L₂) inf_le_right
  let S' : IntermediateField (↥(L₁ ⊓ L₂)) Ω :=
    IntermediateField.extendScalars (F := L₁ ⊓ L₂) (E := L₁ ⊔ L₂)
      (le_sup_of_le_left (inf_le_left : L₁ ⊓ L₂ ≤ L₁))
  let _ : IsGalois K (↥A') := by
    change IsGalois K L₁
    infer_instance
  let _ : FiniteDimensional K (↥A') := by
    change FiniteDimensional K L₁
    infer_instance
  let _ : FiniteDimensional K (↥B') := by
    change FiniteDimensional K L₂
    infer_instance
  let _ : IsGalois (↥(L₁ ⊓ L₂)) (↥A') :=
    IsGalois.tower_top_of_isGalois K (↥(L₁ ⊓ L₂)) (↥A')
  let _ : FiniteDimensional (↥(L₁ ⊓ L₂)) (↥A') :=
    Module.Finite.of_restrictScalars_finite K (↥(L₁ ⊓ L₂)) (↥A')
  let _ : FiniteDimensional (↥(L₁ ⊓ L₂)) (↥B') :=
    Module.Finite.of_restrictScalars_finite K (↥(L₁ ⊓ L₂)) (↥B')
  have hld : A'.LinearDisjoint B' :=
    IntermediateField.LinearDisjoint.of_inf_eq_bot (by
      change
        (IntermediateField.extendScalars (F := L₁ ⊓ L₂) (E := L₁) inf_le_left ⊓
            IntermediateField.extendScalars (F := L₁ ⊓ L₂) (E := L₂) inf_le_right) =
          (⊥ : IntermediateField (↥(L₁ ⊓ L₂)) Ω)
      rw [IntermediateField.extendScalars_inf,
        IntermediateField.extendScalars_self])
  have hsup : A' ⊔ B' = S' := by
    exact IntermediateField.extendScalars_sup
      (inf_le_left : L₁ ⊓ L₂ ≤ L₁) (inf_le_right : L₁ ⊓ L₂ ≤ L₂)
  have hdegree : Module.finrank (↥(L₁ ⊓ L₂)) (↥S') =
      Module.finrank (↥(L₁ ⊓ L₂)) (↥A') *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥B') := by
    rw [← hsup]
    exact hld.finrank_sup
  have hS : Module.finrank K (↥(L₁ ⊔ L₂)) =
      Module.finrank K (↥(L₁ ⊓ L₂)) *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥S') := by
    exact (Module.finrank_mul_finrank' (↥S')).symm
  have h₁ : Module.finrank K L₁ =
      Module.finrank K (↥(L₁ ⊓ L₂)) *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥A') := by
    exact (Module.finrank_mul_finrank' (↥A')).symm
  have h₂ : Module.finrank K L₂ =
      Module.finrank K (↥(L₁ ⊓ L₂)) *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥B') := by
    exact (Module.finrank_mul_finrank' (↥B')).symm
  rw [hS, h₁, h₂, hdegree]
  ac_rfl

/-- Without a Galois hypothesis, the degree identity becomes an inequality. -/
theorem chapter03_compositum_intersection_degree_inequality
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] :
    Module.finrank K (chapter03Compositum L₁ L₂) *
        Module.finrank K (chapter03Intersection L₁ L₂) ≤
      Module.finrank K L₁ * Module.finrank K L₂ := by
  let A' : IntermediateField (↥(L₁ ⊓ L₂)) Ω :=
    IntermediateField.extendScalars (F := L₁ ⊓ L₂) (E := L₁) inf_le_left
  let B' : IntermediateField (↥(L₁ ⊓ L₂)) Ω :=
    IntermediateField.extendScalars (F := L₁ ⊓ L₂) (E := L₂) inf_le_right
  let S' : IntermediateField (↥(L₁ ⊓ L₂)) Ω :=
    IntermediateField.extendScalars (F := L₁ ⊓ L₂) (E := L₁ ⊔ L₂)
      (le_sup_of_le_left (inf_le_left : L₁ ⊓ L₂ ≤ L₁))
  let _ : FiniteDimensional K (↥A') := by
    change FiniteDimensional K L₁
    infer_instance
  let _ : FiniteDimensional K (↥B') := by
    change FiniteDimensional K L₂
    infer_instance
  let _ : FiniteDimensional (↥(L₁ ⊓ L₂)) (↥A') :=
    Module.Finite.of_restrictScalars_finite K (↥(L₁ ⊓ L₂)) (↥A')
  let _ : FiniteDimensional (↥(L₁ ⊓ L₂)) (↥B') :=
    Module.Finite.of_restrictScalars_finite K (↥(L₁ ⊓ L₂)) (↥B')
  have hsup : A' ⊔ B' = S' := by
    exact IntermediateField.extendScalars_sup
      (inf_le_left : L₁ ⊓ L₂ ≤ L₁) (inf_le_right : L₁ ⊓ L₂ ≤ L₂)
  have hineq : Module.finrank (↥(L₁ ⊓ L₂)) (↥S') ≤
      Module.finrank (↥(L₁ ⊓ L₂)) (↥A') *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥B') := by
    rw [← hsup]
    exact IntermediateField.finrank_sup_le A' B'
  have hS : Module.finrank K (↥(L₁ ⊔ L₂)) =
      Module.finrank K (↥(L₁ ⊓ L₂)) *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥S') := by
    exact (Module.finrank_mul_finrank' (↥S')).symm
  have h₁ : Module.finrank K L₁ =
      Module.finrank K (↥(L₁ ⊓ L₂)) *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥A') := by
    exact (Module.finrank_mul_finrank' (↥A')).symm
  have h₂ : Module.finrank K L₂ =
      Module.finrank K (↥(L₁ ⊓ L₂)) *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥B') := by
    exact (Module.finrank_mul_finrank' (↥B')).symm
  rw [hS, h₁, h₂]
  calc
    (Module.finrank K (↥(L₁ ⊓ L₂)) *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥S')) *
        Module.finrank K (↥(L₁ ⊓ L₂)) ≤
      Module.finrank K (↥(L₁ ⊓ L₂)) *
        (Module.finrank (↥(L₁ ⊓ L₂)) (↥S') *
          Module.finrank K (↥(L₁ ⊓ L₂))) := by rw [Nat.mul_assoc]
    _ ≤ Module.finrank K (↥(L₁ ⊓ L₂)) *
        ((Module.finrank (↥(L₁ ⊓ L₂)) (↥A') *
          Module.finrank (↥(L₁ ⊓ L₂)) (↥B')) *
          Module.finrank K (↥(L₁ ⊓ L₂))) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hineq)
    _ = (Module.finrank K (↥(L₁ ⊓ L₂)) *
        Module.finrank (↥(L₁ ⊓ L₂)) (↥A')) *
        (Module.finrank K (↥(L₁ ⊓ L₂)) *
          Module.finrank (↥(L₁ ⊓ L₂)) (↥B')) := by
      ac_rfl

/- The intermediate-field lattice has no canonical valuation-ring data of its
   own, so the numerical arguments below are paired with an explicit residue
   separability predicate.  This records the full unramified condition while
   leaving the field-theoretic tower input explicit. -/
def chapter03UnramifiedNumerical
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (e : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (residueSeparable : IntermediateField K Ω → IntermediateField K Ω → Prop)
    (L B : IntermediateField K Ω) : Prop :=
  e L B = 1 ∧ residueSeparable L B

def chapter03TotallyRamifiedNumerical
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (L B : IntermediateField K Ω) : Prop :=
  f L B = 1

@[simp] theorem chapter03UnramifiedNumerical_iff
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (e : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (residueSeparable : IntermediateField K Ω → IntermediateField K Ω → Prop)
    (L B : IntermediateField K Ω) :
    chapter03UnramifiedNumerical e residueSeparable L B ↔
      e L B = 1 ∧ residueSeparable L B := Iff.rfl

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
    (residueSeparable : IntermediateField K Ω → IntermediateField K Ω → Prop)
    (hLᵤ : chapter03UnramifiedNumerical e residueSeparable Lᵤ ⊥)
    (hLₜ : chapter03TotallyRamifiedNumerical f Lₜ ⊥)
    (htowerᵤ : ∀ F : IntermediateField K Ω, F ≤ Lᵤ →
      e Lᵤ ⊥ = e Lᵤ F * e F ⊥)
    (htowerₜ : ∀ F : IntermediateField K Ω, F ≤ Lₜ →
      f Lₜ ⊥ = f Lₜ F * f F ⊥)
    (hpositiveᵤ : ∀ F : IntermediateField K Ω, F ≤ Lᵤ → 0 < e Lᵤ F)
    (hpositiveₜ : ∀ F : IntermediateField K Ω, F ≤ Lₜ → 0 < f Lₜ F)
    (hdegree : ∀ F : IntermediateField K Ω,
      Module.finrank K F = e F ⊥ * f F ⊥)
    [FiniteDimensional K Lᵤ] [FiniteDimensional K Lₜ]
    [FiniteDimensional K (↥(Lᵤ ⊓ Lₜ))] :
    Lᵤ ⊓ Lₜ = ⊥ := by
  have hFᵤ : Lᵤ ⊓ Lₜ ≤ Lᵤ := inf_le_left
  have hFₜ : Lᵤ ⊓ Lₜ ≤ Lₜ := inf_le_right
  have heprod : e Lᵤ (Lᵤ ⊓ Lₜ) * e (Lᵤ ⊓ Lₜ) ⊥ = 1 := by
    calc
      e Lᵤ (Lᵤ ⊓ Lₜ) * e (Lᵤ ⊓ Lₜ) ⊥ = e Lᵤ ⊥ :=
        (htowerᵤ (Lᵤ ⊓ Lₜ) hFᵤ).symm
      _ = 1 := hLᵤ.1
  have hfprod : f Lₜ (Lᵤ ⊓ Lₜ) * f (Lᵤ ⊓ Lₜ) ⊥ = 1 := by
    calc
      f Lₜ (Lᵤ ⊓ Lₜ) * f (Lᵤ ⊓ Lₜ) ⊥ = f Lₜ ⊥ :=
        (htowerₜ (Lᵤ ⊓ Lₜ) hFₜ).symm
      _ = 1 := hLₜ
  have heF : e (Lᵤ ⊓ Lₜ) ⊥ = 1 := by
    have hleft : e Lᵤ (Lᵤ ⊓ Lₜ) = 1 :=
      Nat.eq_one_of_mul_eq_one_right heprod
    apply Nat.eq_of_mul_eq_mul_left (hpositiveᵤ (Lᵤ ⊓ Lₜ) hFᵤ)
    simpa [hleft] using heprod
  have hfF : f (Lᵤ ⊓ Lₜ) ⊥ = 1 := by
    have hleft : f Lₜ (Lᵤ ⊓ Lₜ) = 1 :=
      Nat.eq_one_of_mul_eq_one_right hfprod
    apply Nat.eq_of_mul_eq_mul_left (hpositiveₜ (Lᵤ ⊓ Lₜ) hFₜ)
    simpa [hleft] using hfprod
  apply IntermediateField.finrank_eq_one_iff.mp
  rw [hdegree (Lᵤ ⊓ Lₜ), heF, hfF]

/-- Intermediate fields inherit the unramified profile. -/
theorem chapter03_intermediate_of_unramified_is_unramified
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω)
    (e : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (residueSeparable : IntermediateField K Ω → IntermediateField K Ω → Prop)
    (hL : chapter03UnramifiedNumerical e residueSeparable L ⊥)
    (F : IntermediateField K Ω) (hF : F ≤ L) :
    (hresidue : residueSeparable L ⊥ → residueSeparable F ⊥) →
    0 < e L F → e L ⊥ = e L F * e F ⊥ →
    chapter03UnramifiedNumerical e residueSeparable F ⊥ := by
  have _ := hF
  intro hresidue hpositive htower
  refine ⟨?_, hresidue hL.2⟩
  have hprod : e L F * e F ⊥ = 1 := by
    calc
      e L F * e F ⊥ = e L ⊥ := htower.symm
      _ = 1 := hL.1
  have hleft : e L F = 1 := Nat.eq_one_of_mul_eq_one_right hprod
  apply Nat.eq_of_mul_eq_mul_left hpositive
  simpa [hleft] using hprod

/-- Intermediate fields inherit the totally ramified profile. -/
theorem chapter03_intermediate_of_totally_ramified_is_totally_ramified
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω)
    (f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    (hL : chapter03TotallyRamifiedNumerical f L ⊥)
    (F : IntermediateField K Ω) (hF : F ≤ L) :
    0 < f L F → f L ⊥ = f L F * f F ⊥ →
    chapter03TotallyRamifiedNumerical f F ⊥ := by
  have _ := hF
  intro hpositive htower
  have hprod : f L F * f F ⊥ = 1 := by
    calc
      f L F * f F ⊥ = f L ⊥ := htower.symm
      _ = 1 := hL
  have hleft : f L F = 1 := Nat.eq_one_of_mul_eq_one_right hprod
  apply Nat.eq_of_mul_eq_mul_left hpositive
  simpa [hleft] using hprod

/-- The common `e=f=1` profile identifies an intermediate field with the base. -/
theorem chapter03_intermediate_e_one_f_one_is_base
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (F : IntermediateField K Ω)
    (e f : IntermediateField K Ω → IntermediateField K Ω → ℕ)
    [FiniteDimensional K F]
    (he : e F ⊥ = 1) (hf : f F ⊥ = 1)
    (hdegree : Module.finrank K F = e F ⊥ * f F ⊥) :
    F = ⊥ := by
  apply IntermediateField.finrank_eq_one_iff.mp
  rw [hdegree, he, hf]

/-- A Galois extension with trivial intersection is linearly disjoint. -/
theorem chapter03_galois_extensions_are_linearly_disjoint_of_trivial_intersection
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsGalois K L₁] (hinter : L₁ ⊓ L₂ = ⊥) :
    L₁.LinearDisjoint L₂ := by
  exact IntermediateField.LinearDisjoint.of_inf_eq_bot hinter

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
  exact hld.finrank_sup

/-- The self-base-change algebra; it need not be a field. -/
abbrev chapter03SelfScalarExtension
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] : Type _ :=
  L ⊗[K] L

def chapter03SelfScalarExtensionSplits
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] (n : ℕ) : Prop :=
  letI : Algebra L (chapter03SelfScalarExtension K L) :=
    Algebra.TensorProduct.rightAlgebra
  Nonempty (chapter03SelfScalarExtension K L ≃ₐ[L] (Fin n → L))

/-- A field factor of the self-base-change algebra, viewed over the right
`L`-scalar structure.  A surjective `L`-algebra map records a quotient factor
without incorrectly identifying the whole product with one field. -/
def chapter03SelfScalarExtensionFieldFactor
    (K L F : Type*) [CommRing K] [CommRing L] [Field F]
    [Algebra K L] [Algebra L F] : Prop :=
  letI : Algebra L (chapter03SelfScalarExtension K L) :=
    Algebra.TensorProduct.rightAlgebra
  ∃ φ : chapter03SelfScalarExtension K L →ₐ[L] F, Function.Surjective φ

/-- A finite Galois self-base-change splits into copies of `L`. -/
theorem chapter03_galois_self_scalar_extension_splits
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∃ n : ℕ, n = Module.finrank K L ∧
      chapter03SelfScalarExtensionSplits K L n := by
  sorry

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
    (hfactor : chapter03SelfScalarExtensionFieldFactor K L F) :
    chapterRamificationIndex vL.valuationSubring vF.valuationSubring
      (IsLocalRing.maximalIdeal vF.valuationSubring) = 1 := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
