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
  let I : IntermediateField K Ω := L₁ ⊓ L₂
  let A : IntermediateField (↥I) Ω :=
    IntermediateField.extendScalars (inf_le_left : I ≤ L₁)
  let B : IntermediateField (↥I) Ω :=
    IntermediateField.extendScalars (inf_le_right : I ≤ L₂)
  let C : IntermediateField (↥I) Ω :=
    IntermediateField.extendScalars
      (le_sup_of_le_left (inf_le_left : I ≤ L₁) : I ≤ L₁ ⊔ L₂)
  have hsup : A ⊔ B = C := by
    dsimp [A, B, C]
    exact IntermediateField.extendScalars_sup (inf_le_left : I ≤ L₁)
      (inf_le_right : I ≤ L₂)
  have hrel :
      IntermediateField.relfinrank I (L₁ ⊔ L₂) ≤
        IntermediateField.relfinrank I L₁ * IntermediateField.relfinrank I L₂ := by
    have h := IntermediateField.finrank_sup_le A B
    rw [hsup] at h
    calc
      IntermediateField.relfinrank I (L₁ ⊔ L₂) = Module.finrank (↥I) C := by
        simpa [C] using
          (IntermediateField.relfinrank_eq_finrank_of_le
            (A := I) (B := L₁ ⊔ L₂)
            (le_sup_of_le_left (inf_le_left : I ≤ L₁)))
      _ ≤ Module.finrank (↥I) A * Module.finrank (↥I) B := h
      _ = IntermediateField.relfinrank I L₁ *
          IntermediateField.relfinrank I L₂ := by
        rw [← IntermediateField.relfinrank_eq_finrank_of_le
          (A := I) (B := L₁) (inf_le_left : I ≤ L₁),
          ← IntermediateField.relfinrank_eq_finrank_of_le
            (A := I) (B := L₂) (inf_le_right : I ≤ L₂)]
        rfl
  have hI :
      Module.finrank K I * Module.finrank K I *
          IntermediateField.relfinrank I (L₁ ⊔ L₂) ≤
        Module.finrank K I * Module.finrank K I *
          (IntermediateField.relfinrank I L₁ *
            IntermediateField.relfinrank I L₂) :=
    Nat.mul_le_mul_left (Module.finrank K I * Module.finrank K I) hrel
  have hC :
      Module.finrank K I * IntermediateField.relfinrank I (L₁ ⊔ L₂) =
        Module.finrank K (L₁ ⊔ L₂) :=
    IntermediateField.finrank_bot_mul_relfinrank
      (A := I) (B := L₁ ⊔ L₂)
      (le_sup_of_le_left (inf_le_left : I ≤ L₁))
  have hL₁ :
      Module.finrank K I * IntermediateField.relfinrank I L₁ =
        Module.finrank K L₁ :=
    IntermediateField.finrank_bot_mul_relfinrank
      (A := I) (B := L₁) (inf_le_left : I ≤ L₁)
  have hL₂ :
      Module.finrank K I * IntermediateField.relfinrank I L₂ =
        Module.finrank K L₂ :=
    IntermediateField.finrank_bot_mul_relfinrank
      (A := I) (B := L₂) (inf_le_right : I ≤ L₂)
  change Module.finrank K (L₁ ⊔ L₂) * Module.finrank K I ≤
    Module.finrank K L₁ * Module.finrank K L₂
  calc
    Module.finrank K (L₁ ⊔ L₂) * Module.finrank K I =
        Module.finrank K I * Module.finrank K I *
          IntermediateField.relfinrank I (L₁ ⊔ L₂) := by
      rw [← hC]
      ac_rfl
    _ ≤ Module.finrank K I * Module.finrank K I *
          (IntermediateField.relfinrank I L₁ *
            IntermediateField.relfinrank I L₂) := hI
    _ = (Module.finrank K I * IntermediateField.relfinrank I L₁) *
          (Module.finrank K I * IntermediateField.relfinrank I L₂) := by
      ac_rfl
    _ = Module.finrank K L₁ * Module.finrank K L₂ := by
      rw [hL₁, hL₂]

/- The numerical predicates below are used only after the functions `e` and
`f` have been tied to actual local invariants by the hypotheses of the
intersection theorem. -/

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

/--
Finite unramified and finite totally ramified extensions have trivial
intersection.  The closure hypotheses quantify the same properties over
intermediate fields, which is the precise form needed for the argument.
-/
theorem chapter03_unramified_totally_ramified_intersection
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (Lᵤ Lₜ : IntermediateField K Ω)
    (e f : ∀ A B : IntermediateField K Ω, ℕ)
    (hLᵤ : chapter03UnramifiedNumerical e Lᵤ ⊥)
    (hLₜ : chapter03TotallyRamifiedNumerical f Lₜ ⊥)
    (hpos_e : ∀ A B : IntermediateField K Ω, A ≤ B → 0 < e A B)
    (hpos_f : ∀ A B : IntermediateField K Ω, A ≤ B → 0 < f A B)
    (htowerᵤ : ∀ F : IntermediateField K Ω, F ≤ Lᵤ →
      e Lᵤ ⊥ = e Lᵤ F * e F ⊥)
    (htowerₜ : ∀ F : IntermediateField K Ω, F ≤ Lₜ →
      f Lₜ ⊥ = f Lₜ F * f F ⊥)
    (hdegree : ∀ F : IntermediateField K Ω,
      Module.finrank K F = e F ⊥ * f F ⊥)
    [FiniteDimensional K Lᵤ] [FiniteDimensional K Lₜ] :
    Lᵤ ⊓ Lₜ = ⊥ := by
  change e Lᵤ ⊥ = 1 at hLᵤ
  change f Lₜ ⊥ = 1 at hLₜ
  have heprod :
      e Lᵤ (Lᵤ ⊓ Lₜ) * e (Lᵤ ⊓ Lₜ) ⊥ = 1 := by
    rw [← htowerᵤ (Lᵤ ⊓ Lₜ) inf_le_left, hLᵤ]
  have hfprod :
      f Lₜ (Lᵤ ⊓ Lₜ) * f (Lᵤ ⊓ Lₜ) ⊥ = 1 := by
    rw [← htowerₜ (Lᵤ ⊓ Lₜ) inf_le_right, hLₜ]
  have he : e (Lᵤ ⊓ Lₜ) ⊥ = 1 :=
    Nat.eq_one_of_mul_eq_one_right heprod
  have hf : f (Lᵤ ⊓ Lₜ) ⊥ = 1 :=
    Nat.eq_one_of_mul_eq_one_right hfprod
  have hfin : Module.finrank K (Lᵤ ⊓ Lₜ) = 1 := by
    simpa [he, hf] using hdegree (Lᵤ ⊓ Lₜ)
  exact IntermediateField.finrank_eq_one_iff.mp hfin

/-- Intermediate fields inherit the unramified profile. -/
theorem chapter03_intermediate_of_unramified_is_unramified
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω)
    (e : ∀ A B : IntermediateField K Ω, ℕ)
    (hL : chapter03UnramifiedNumerical e L ⊥)
    (F : IntermediateField K Ω) (hF : F ≤ L) :
    0 < e L F →
    e L ⊥ = e L F * e F ⊥ →
    chapter03UnramifiedNumerical e F ⊥ := by
  intro _ htower
  change e F ⊥ = 1
  change e L ⊥ = 1 at hL
  have hprod : e L F * e F ⊥ = 1 := by
    rw [← htower, hL]
  exact Nat.eq_one_of_mul_eq_one_right hprod

/-- Intermediate fields inherit the totally ramified profile. -/
theorem chapter03_intermediate_of_totally_ramified_is_totally_ramified
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω)
    (f : ∀ A B : IntermediateField K Ω, ℕ)
    (hL : chapter03TotallyRamifiedNumerical f L ⊥)
    (F : IntermediateField K Ω) (hF : F ≤ L) :
    0 < f L F →
    f L ⊥ = f L F * f F ⊥ →
    chapter03TotallyRamifiedNumerical f F ⊥ := by
  intro _ htower
  change f F ⊥ = 1
  change f L ⊥ = 1 at hL
  have hprod : f L F * f F ⊥ = 1 := by
    rw [← htower, hL]
  exact Nat.eq_one_of_mul_eq_one_right hprod

/-- The common e=f=1 profile identifies an intermediate field with the base. -/
theorem chapter03_intermediate_e_one_f_one_is_base
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (F : IntermediateField K Ω)
    (e f : ∀ A B : IntermediateField K Ω, ℕ)
    (he : e F ⊥ = 1) (hf : f F ⊥ = 1)
    (hdegree : Module.finrank K F = e F ⊥ * f F ⊥) :
    F = ⊥ := by
  apply IntermediateField.finrank_eq_one_iff.mp
  simpa [he, hf] using hdegree

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
  change Module.finrank K (L₁ ⊔ L₂) = Module.finrank K L₁ * Module.finrank K L₂
  exact hld.finrank_sup

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

def chapter03SelfBaseChangeRamificationIndex
    {L F Γ : Type*} [Field L] [Field F] [Algebra L F]
    [LinearOrderedCommGroupWithZero Γ]
    (vL : Valuation L Γ) (vF : Valuation F Γ)
    [vL.HasExtension vF] : ℕ :=
  chapter03RamificationIndex vL vF

/- Every factor in the self-base-change splitting has ramification index one
over the new base field. -/
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
    (hfactor : Nonempty
      (chapter03SelfScalarExtension K L ≃ₐ[L] F)) :
    chapter03SelfBaseChangeRamificationIndex vL vF = 1 := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
