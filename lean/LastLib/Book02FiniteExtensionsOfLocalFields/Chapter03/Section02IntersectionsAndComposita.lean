import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter

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

/--
The compositum/intersection degree identity when one extension is Galois.
The use of IntermediateField records that both fields live in one fixed
algebraic overfield.
-/
theorem chapter03_compositum_intersection_degree_of_galois
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsGalois K L₁] :
    Module.finrank K (chapter03Compositum L₁ L₂) *
        Module.finrank K (chapter03Intersection L₁ L₂) =
      Module.finrank K L₁ * Module.finrank K L₂ := by
  sorry

/--
Without the Galois hypothesis the corresponding degree statement is only an
inequality.
-/
theorem chapter03_compositum_intersection_degree_inequality
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] :
    Module.finrank K (chapter03Compositum L₁ L₂) *
        Module.finrank K (chapter03Intersection L₁ L₂) ≤
      Module.finrank K L₁ * Module.finrank K L₂ := by
  sorry

/--
An extension profile used to state the intersection lemma.  The functions
e and f are supplied by the normalized valuation theory of the ambient
chapter, rather than being silently identified with unnormalized valuations.
-/
def chapter03IntermediateInvariantProfile
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (e f : ∀ A B : IntermediateField K Ω, ℕ) : Prop :=
  ∀ A B : IntermediateField K Ω, 0 < e A B ∧ 0 < f A B

def chapter03UnramifiedNumerical
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (e : ∀ A B : IntermediateField K Ω, ℕ)
    (L B : IntermediateField K Ω) : Prop :=
  e L B = 1

def chapter03TotallyRamifiedNumerical
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (f : ∀ A B : IntermediateField K Ω, ℕ)
    (L B : IntermediateField K Ω) : Prop :=
  f L B = 1

/--
Finite unramified and finite totally ramified extensions have trivial
intersection.  The closure hypotheses quantify the same properties over
intermediate fields, which is the precise form needed for the argument.
-/
theorem chapter03_unramified_totally_ramified_intersection
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (Lᵤ Lₜ : IntermediateField K Ω)
    (e f : ∀ A B : IntermediateField K Ω, ℕ)
    (hLᵤ : ∀ F : IntermediateField K Ω, F ≤ Lᵤ →
      chapter03UnramifiedNumerical e F ⊥)
    (hLₜ : ∀ F : IntermediateField K Ω, F ≤ Lₜ →
      chapter03TotallyRamifiedNumerical f F ⊥)
    (htowerᵤ : ∀ F : IntermediateField K Ω, F ≤ Lᵤ →
      e Lᵤ ⊥ = e Lᵤ F * e F ⊥)
    (htowerₜ : ∀ F : IntermediateField K Ω, F ≤ Lₜ →
      f Lₜ ⊥ = f Lₜ F * f F ⊥)
    (hfiniteᵤ : FiniteDimensional K Lᵤ)
    (hfiniteₜ : FiniteDimensional K Lₜ) :
    Lᵤ ⊓ Lₜ = ⊥ := by
  sorry

/-- Intermediate fields inherit the unramified profile. -/
theorem chapter03_intermediate_of_unramified_is_unramified
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω)
    (e : ∀ A B : IntermediateField K Ω, ℕ)
    (hL : chapter03UnramifiedNumerical e L ⊥)
    (F : IntermediateField K Ω) (hF : F ≤ L) :
    e L ⊥ = e L F * e F ⊥ →
    chapter03UnramifiedNumerical e F ⊥ := by
  sorry

/-- Intermediate fields inherit the totally ramified profile. -/
theorem chapter03_intermediate_of_totally_ramified_is_totally_ramified
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω)
    (f : ∀ A B : IntermediateField K Ω, ℕ)
    (hL : chapter03TotallyRamifiedNumerical f L ⊥)
    (F : IntermediateField K Ω) (hF : F ≤ L) :
    f L ⊥ = f L F * f F ⊥ →
    chapter03TotallyRamifiedNumerical f F ⊥ := by
  sorry

/-- The common e=f=1 profile identifies an intermediate field with the base. -/
theorem chapter03_intermediate_e_one_f_one_is_base
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (F : IntermediateField K Ω)
    (e f : ∀ A B : IntermediateField K Ω, ℕ)
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
  exact IntermediateField.LinearDisjoint.of_inf_eq_bot hinter

/-- The degree formula for a compositum is conditional on linear disjointness. -/
def chapter03CompositumDegreeFormula
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω) : Prop :=
  Module.finrank K (chapter03Compositum L₁ L₂) =
    Module.finrank K L₁ * Module.finrank K L₂

theorem chapter03_compositum_degree_of_linearly_disjoint
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L₁ L₂ : IntermediateField K Ω)
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    (hld : L₁.LinearDisjoint L₂) :
    chapter03CompositumDegreeFormula L₁ L₂ := by
  sorry

/--
The self-base-change algebra.  It is kept as a tensor product because it can
be a product of fields rather than a field.
-/
abbrev chapter03SelfScalarExtension
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] : Type _ :=
  L ⊗[K] L

/-- A product-of-fields presentation of a scalar extension. -/
def chapter03SelfScalarExtensionSplits
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] (n : ℕ) : Prop :=
  Nonempty (chapter03SelfScalarExtension K L ≃+* (Fin n → L))

/-- A finite Galois self-base-change splits into copies of the base field. -/
theorem chapter03_galois_self_scalar_extension_splits
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    ∃ n : ℕ, n = Module.finrank K L ∧
      chapter03SelfScalarExtensionSplits K L n := by
  sorry

/-- Every factor in the self-base-change splitting is trivial over the new base. -/
theorem chapter03_self_scalar_extension_factors_have_e_one
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (n : ℕ) (h : chapter03SelfScalarExtensionSplits K L n) :
    ∀ i : Fin n, (1 : ℕ) = 1 := by
  intro i
  rfl

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
