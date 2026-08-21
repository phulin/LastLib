import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14.Dependencies

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14

noncomputable section

open scoped BigOperators NumberField TensorProduct
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

universe u v w

/-! ## 14.1. A prime and its completed branches -/

structure Chapter14PrimeAboveEnumeration
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) where
  index : Type w
  finite_index : Fintype index
  prime : index → Chapter14PrimeAbove F E p
  exhaustive : ∀ P : Chapter14PrimeAbove F E p, ∃ i, prime i = P
  injective : Function.Injective prime

theorem chapter14_prime_above_enumeration_exists
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) :
    Nonempty (Chapter14PrimeAboveEnumeration E p) := by
  let _ : Fintype (Chapter14PrimeAbove F E p) :=
    Set.Finite.fintype (Algebra.QuasiFinite.finite_primesOver p.asIdeal)
  let e : Chapter14PrimeAbove F E p ≃
      Fin (Fintype.card (Chapter14PrimeAbove F E p)) :=
    Fintype.equivFin _
  let H : Chapter14PrimeAboveEnumeration E p :=
    { index := ULift (Fin (Fintype.card (Chapter14PrimeAbove F E p)))
      finite_index := inferInstance
      prime := fun i => e.symm i.down
      exhaustive := by
        intro P
        refine ⟨⟨e P⟩, ?_⟩
        simp [e]
      injective := e.symm.injective.comp ULift.down_injective }
  exact ⟨H⟩

def Chapter14CompletedScalarExtension
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) [Algebra F (chapter14BaseCompletion F p)] : Prop :=
  Nonempty
    (E ⊗[F] chapter14BaseCompletion F p ≃+*
      (∀ P : Chapter14PrimeAbove F E p,
        chapter14BranchCompletion F E p P))

def chapter14SelectedBranchProjection
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p)
    [Algebra F (chapter14BaseCompletion F p)]
    (hproduct : Chapter14CompletedScalarExtension E p) :
    E ⊗[F] chapter14BaseCompletion F p →+*
      chapter14BranchCompletion F E p P :=
  let e := Classical.choice hproduct
  (Pi.evalRingHom (fun Q : Chapter14PrimeAbove F E p =>
    chapter14BranchCompletion F E p Q) P).comp e.toRingHom

theorem chapter14_each_completed_branch_is_a_finite_local_extension
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F)
    [Algebra F (chapter14BaseCompletion F p)]
    [∀ P : Chapter14PrimeAbove F E p,
      Algebra (chapter14BaseCompletion F p)
        (chapter14BranchCompletion F E p P)] :
    ∀ P : Chapter14PrimeAbove F E p,
      FiniteDimensional (chapter14BaseCompletion F p)
        (chapter14BranchCompletion F E p P) := by
  sorry

theorem chapter14_selected_branch_projection_surjective
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p)
    [Algebra F (chapter14BaseCompletion F p)]
    (hproduct : Chapter14CompletedScalarExtension E p) :
    Function.Surjective (chapter14SelectedBranchProjection E p P hproduct) := by
  let e := Classical.choice hproduct
  exact
    (Pi.evalRingHom (fun Q : Chapter14PrimeAbove F E p =>
      chapter14BranchCompletion F E p Q) P).surjective.comp e.surjective

/- The product decomposition over the completed localization is the earlier
   Dedekind-domain product theorem, transported to the prime-above subtype. -/
theorem chapter14_completed_scalar_extension_decomposition
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F)
    [Algebra F (chapter14BaseCompletion F p)]
    [Module.Finite (𝓞 F) (𝓞 E)] [Module.Free (𝓞 F) (𝓞 E)]
    (H : Chapter14PrimeAboveEnumeration E p) :
    Chapter14CompletedScalarExtension E p := by
  sorry

/- The finite degree of an individual completed branch is `e f`.  Its
   completed valuations and the two global/local invariant identifications
   are explicit because the branch model is a fraction field of an adic
   completion, whereas Mathlib's finite-place completion uses a uniform-space
   completion. -/
theorem chapter14_completed_branch_degree
    {F : Type u} (E : Type v) {Γ : Type w} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p)
    [IsDomain (branchCompletion (𝓞 E) P.1)]
    [Algebra F (chapter14BaseCompletion F p)]
    [Algebra (chapter14BaseCompletion F p)
      (chapter14BranchCompletion F E p P)]
    [FiniteDimensional (chapter14BaseCompletion F p)
      (chapter14BranchCompletion F E p P)]
    [LinearOrderedCommGroupWithZero Γ]
    (vBase : Valuation (chapter14BaseCompletion F p) Γ)
    (vBranch : Valuation (chapter14BranchCompletion F E p P) Γ)
    [vBase.HasExtension vBranch]
    [Valuation.IsRankOneDiscrete vBase]
    [Valuation.IsRankOneDiscrete vBranch]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vBase.valuationSubring)
      vBase.valuationSubring)
    (H : CompleteExtensionGlobalInvariantIdentification
        (K := chapter14BaseCompletion F p)
        (L := chapter14BranchCompletion F E p P)
        (R := 𝓞 F) (S := 𝓞 E) P.1 vBase vBranch)
    (e f : ℕ)
    (he : chapter14RamificationIndex E p P = e)
    (hf : chapter14ResidueDegree E p P = f) :
    Module.finrank (chapter14BaseCompletion F p)
        (chapter14BranchCompletion F E p P) = e * f := by
  have hglobal :=
    complete_extension_defectless_of_global_invariant_identification
      P.1 vBase vBranch hcomplete H
  change P.1.ramificationIdx (𝓞 F) = e at he
  change P.1.inertiaDeg (𝓞 F) = f at hf
  simpa only [he, hf] using hglobal

theorem chapter14_sum_of_completed_branch_degrees
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F)
    [Module.Finite (𝓞 F) (𝓞 E)] [Module.Flat (𝓞 F) (𝓞 E)]
    [Fintype (p.asIdeal.primesOver (𝓞 E))] :
    Module.finrank F E =
      ∑ P : Chapter14PrimeAbove F E p,
        chapter14RamificationIndex E p P * chapter14ResidueDegree E p P := by
  calc
    Module.finrank F E = Module.finrank (𝓞 F) (𝓞 E) := by
      exact IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E
    _ = ∑ Q : p.asIdeal.primesOver (𝓞 E),
        Q.1.ramificationIdx (𝓞 F) * Q.1.inertiaDeg (𝓞 F) :=
      (Ideal.sum_ramification_inertia_eq_finrank p.asIdeal (𝓞 E)).symm
    _ = ∑ P : Chapter14PrimeAbove F E p,
        chapter14RamificationIndex E p P * chapter14ResidueDegree E p P := by
      rfl

/- The action on prime ideals is Mathlib's canonical Galois action. -/
def chapter14PrimeAction
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) (σ : Gal(E / F))
    (P : Chapter14PrimeAbove F E p) : Chapter14PrimeAbove F E p :=
  σ • P

def chapter14DecompositionGroup
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p) :
    Subgroup (Gal(E / F)) := by
  classical
  refine
    { carrier := {σ | chapter14PrimeAction E p σ P = P}
      one_mem' := by
        change chapter14PrimeAction E p 1 P = P
        simp [chapter14PrimeAction]
      mul_mem' := by
        intro σ τ hσ hτ
        change σ • P = P at hσ
        change τ • P = P at hτ
        change chapter14PrimeAction E p (σ * τ) P = P
        change (σ * τ) • P = P
        rw [mul_smul, hτ, hσ]
      inv_mem' := by
        intro σ hσ
        change σ • P = P at hσ
        change chapter14PrimeAction E p σ⁻¹ P = P
        change σ⁻¹ • P = P
        calc
          σ⁻¹ • P = σ⁻¹ • (σ • P) := by rw [hσ]
          _ = P := inv_smul_smul σ P }

theorem chapter14_mem_decomposition_group_iff
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p)
    (σ : Gal(E / F)) :
    σ ∈ chapter14DecompositionGroup E p P ↔
      chapter14PrimeAction E p σ P = P := by
  rfl

theorem chapter14_galois_factors_are_transitive
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (p : Chapter14Prime F) :
    ∀ P Q : Chapter14PrimeAbove F E p,
      ∃ σ : Gal(E / F), chapter14PrimeAction E p σ P = Q := by
  intro P Q
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_comap_galRestrict_eq (𝓞 F) F E (𝓞 E) Q.2 P.2
  have hmap :
      Ideal.map (galRestrict (𝓞 F) F E (𝓞 E) σ) P.1 = Q.1 := by
    rw [← hσ]
    exact Ideal.map_comap_of_surjective _
      (galRestrict (𝓞 F) F E (𝓞 E) σ).surjective _
  refine ⟨σ, ?_⟩
  change σ • P = Q
  apply Subtype.ext
  rw [Ideal.coe_smul_primesOver_eq_map_galRestrict]
  exact hmap

/- The global decomposition group becomes the local Galois group after the
   selected completion is supplied with its induced algebra and action. -/
theorem chapter14_decomposition_group_is_completed_branch_galois_group
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p)
    [Algebra F (chapter14BaseCompletion F p)]
    [Algebra (chapter14BaseCompletion F p)
      (chapter14BranchCompletion F E p P)]
    [FiniteDimensional (chapter14BaseCompletion F p)
      (chapter14BranchCompletion F E p P)]
    [MulSemiringAction (chapter14DecompositionGroup E p P)
      (chapter14BranchCompletion F E p P)]
    (hD : IsGaloisGroup (chapter14DecompositionGroup E p P)
      (chapter14BaseCompletion F p)
      (chapter14BranchCompletion F E p P)) :
    Nonempty
      (chapter14DecompositionGroup E p P ≃*
        Gal(chapter14BranchCompletion F E p P /
          chapter14BaseCompletion F p)) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14
