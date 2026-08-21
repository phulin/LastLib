import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.RingTheory.TensorProduct.Maps

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
  classical
  let G := Gal(L / K)
  let q : L →ₗ[K] (G → L) :=
    LinearMap.pi (fun σ : G => σ.toAlgHom.toLinearMap)
  have hli : LinearIndependent L (fun σ : G => fun x : L => σ x) := by
    have hli' : LinearIndependent L (fun σ : G => σ.toAlgHom.toLinearMap) :=
      (linearIndependent_algHom_toLinearMap K L L).comp
        (fun σ : G => σ.toAlgHom) (algEquivEquivAlgHom K L).injective
    have hker : LinearMap.ker (LinearMap.ltoFun K L L L) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro f g h
      ext x
      exact congr_fun h x
    simpa [Function.comp_def] using hli'.map' (LinearMap.ltoFun K L L L) hker
  have hqrange : (LinearMap.range q : Set (G → L)) = Set.range q := by
    ext y
    simp [LinearMap.mem_range]
  have hsurj : Function.Surjective (q.liftBaseChange L) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange]
    rw [hqrange]
    change Submodule.span L (Set.range (fun x : L => fun σ : G => σ x)) = ⊤
    exact
      (span_flip_eq_top_iff_linearIndependent
        (f := fun σ : G => fun x : L => σ x)).2 hli
  have hdim : Module.finrank L (L ⊗[K] L) = Module.finrank L (G → L) := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul,
      Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card,
      IsGalois.card_aut_eq_finrank]
  have hbij : Function.Bijective (q.liftBaseChange L) := by
    refine ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
  let eLin : (L ⊗[K] L) ≃ₗ[L] (G → L) :=
    LinearEquiv.ofBijective (q.liftBaseChange L) hbij
  have hmul : ∀ (a₁ a₂ b₁ b₂ : L),
      eLin ((a₁ * a₂) ⊗ₜ[K] (b₁ * b₂)) =
        eLin (a₁ ⊗ₜ[K] b₁) * eLin (a₂ ⊗ₜ[K] b₂) := by
    intro a₁ a₂ b₁ b₂
    ext σ
    simp [eLin, q, mul_assoc, mul_comm, mul_left_comm]
  have hone : eLin ((1 : L) ⊗ₜ[K] (1 : L)) = 1 := by
    ext σ
    simp [eLin, q]
  let eAlg : @AlgEquiv L (L ⊗[K] L) (G → L)
      _ _ _ Algebra.TensorProduct.leftAlgebra _ :=
    Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct eLin hmul hone
  refine ⟨Fintype.card G, ?_, ?_⟩
  · rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  · let eFin : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
    let ePi : (G → L) ≃ₐ[L] (Fin (Fintype.card G) → L) :=
      AlgEquiv.piCongrLeft' L (fun _ : G => L) eFin
    let eComm0 :=
      @AlgEquiv.symm L (L ⊗[K] L) (L ⊗[K] L) _ _ _
        Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra
        (Algebra.TensorProduct.commRight K L L)
    let eComm : @AlgEquiv L (L ⊗[K] L) (L ⊗[K] L)
        _ _ _ Algebra.TensorProduct.rightAlgebra Algebra.TensorProduct.leftAlgebra :=
      eComm0
    let eMiddle := eAlg.trans ePi
    let eFinal0 :=
      @AlgEquiv.trans L (L ⊗[K] L) (L ⊗[K] L) (Fin (Fintype.card G) → L) _ _ _ _
        Algebra.TensorProduct.rightAlgebra Algebra.TensorProduct.leftAlgebra _ eComm eMiddle
    let eFinal :
        @AlgEquiv L (L ⊗[K] L) (Fin (Fintype.card G) → L)
          _ _ _ Algebra.TensorProduct.rightAlgebra _ :=
      eFinal0
    unfold chapter03SelfScalarExtensionSplits
    exact ⟨eFinal⟩

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
  classical
  let _ : Algebra L (L ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  change ∃ φ : L ⊗[K] L →ₐ[L] F, Function.Surjective φ at hfactor
  rcases hfactor with ⟨φ, hφ⟩
  obtain ⟨n, hn, hsplit⟩ := chapter03_galois_self_scalar_extension_splits K L
  change Nonempty (L ⊗[K] L ≃ₐ[L] (Fin n → L)) at hsplit
  rcases hsplit with ⟨e⟩
  let ψ : (Fin n → L) →ₐ[L] F := φ.comp e.symm
  have hψ : Function.Surjective ψ := hφ.comp e.symm.surjective
  have hAlgMap : Function.Surjective (algebraMap L F) := by
    have hsum_one :
        ∑ i : Fin n, Pi.single i (1 : L) = (1 : Fin n → L) := by
      exact Finset.univ_sum_single 1
    have hex : ∃ i : Fin n, ψ (Pi.single i (1 : L)) ≠ 0 := by
      by_contra h
      have hall : ∀ i : Fin n, ψ (Pi.single i (1 : L)) = 0 := by
        intro i
        by_contra hi
        exact h ⟨i, hi⟩
      have hsum := congrArg ψ hsum_one
      have hzero : ∑ i : Fin n, ψ (Pi.single i (1 : L)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        exact hall i
      have : (0 : F) = 1 := by
        simp [map_sum, hzero] at hsum
      exact zero_ne_one this
    obtain ⟨i, hi⟩ := hex
    have hid : IsIdempotentElem (ψ (Pi.single i (1 : L))) := by
      rw [isIdempotentElem_iff]
      calc
        ψ (Pi.single i (1 : L)) * ψ (Pi.single i (1 : L)) =
            ψ (Pi.single i (1 : L) * Pi.single i (1 : L)) :=
          (map_mul ψ _ _).symm
        _ = ψ (Pi.single i (1 : L)) := by simp [← Pi.single_mul]
    have hei : ψ (Pi.single i (1 : L)) = 1 := by
      rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hid) with hz | hone
      · exact (hi hz).elim
      · exact hone
    intro x
    obtain ⟨y, rfl⟩ := hψ x
    have hy : y = ∑ j : Fin n, Pi.single j (y j) := by
      symm
      rw [Finset.univ_sum_single]
    refine ⟨y i, ?_⟩
    have hterm : ∀ j : Fin n, ψ (Pi.single j (y j)) =
        if j = i then algebraMap L F (y i) else 0 := by
      intro j
      by_cases hji : j = i
      · subst j
        have hsingle :
            Pi.single i (y i) = (fun _ : Fin n => y i) * Pi.single i (1 : L) := by
          ext k
          by_cases hki : k = i <;> simp [hki]
        rw [hsingle, map_mul, hei]
        simp [Pi.algebraMap_def, ← ψ.commutes]
      · have hsingle :
            Pi.single j (y j) = (fun _ : Fin n => y j) * Pi.single j (1 : L) := by
          ext k
          by_cases hkj : k = j <;> simp [hkj]
        rw [hsingle, map_mul]
        have hconst : ψ (fun _ : Fin n => y j) = algebraMap L F (y j) := by
          simpa [Pi.algebraMap_def] using ψ.commutes (y j)
        have horth :
            ψ (Pi.single j (1 : L)) * ψ (Pi.single i (1 : L)) = 0 := by
          rw [← map_mul]
          have hprodzero :
              Pi.single (M := fun _ : Fin n => L) j (1 : L) *
                  Pi.single (M := fun _ : Fin n => L) i (1 : L) = 0 := by
            ext k
            by_cases hkj : k = j <;> by_cases hki : k = i <;>
              simp [hkj, hki, hji]
          rw [hprodzero, map_zero]
        have hzero : ψ (Pi.single j (1 : L)) = 0 := by
          simpa [hei] using horth
        rw [hconst, hzero, mul_zero]
        simp [hji]
    have hsum_y :
        ψ y = ∑ j : Fin n, ψ (Pi.single j (y j)) := by
      calc
        ψ y = ψ (∑ j : Fin n, Pi.single j (y j)) := congrArg ψ hy
        _ = ∑ j : Fin n, ψ (Pi.single j (y j)) := by simp
    have hsum_i :
        (∑ j : Fin n, ψ (Pi.single j (y j))) = ψ (Pi.single i (y i)) := by
      rw [Finset.sum_eq_single i]
      · intro j hj hne
        exact (hterm j).trans (by simp [hne])
      · intro hi'
        exact (hi' (Finset.mem_univ i)).elim
    have hsingle_i : algebraMap L F (y i) = ψ (Pi.single i (y i)) := by
      simpa using (hterm i).symm
    exact hsingle_i.trans (hsum_i.symm.trans hsum_y.symm)
  have hfin : Module.finrank L F = 1 := by
    apply finrank_eq_one (1 : F) one_ne_zero
    intro w
    obtain ⟨c, hc⟩ := hAlgMap w
    refine ⟨c, ?_⟩
    simpa [Algebra.smul_def] using hc
  have hdegree :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.complete_extension_defectless_without_separability
      vL vF hcomplete
  have hprod :
      1 = chapterRamificationIndex vL.valuationSubring vF.valuationSubring
          (IsLocalRing.maximalIdeal vF.valuationSubring) *
        chapterResidueDegree vL.valuationSubring vF.valuationSubring
          (IsLocalRing.maximalIdeal vF.valuationSubring) := by
    simpa [hfin] using hdegree
  apply Nat.dvd_one.mp
  refine ⟨chapterResidueDegree vL.valuationSubring vF.valuationSubring
    (IsLocalRing.maximalIdeal vF.valuationSubring), hprod⟩

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
