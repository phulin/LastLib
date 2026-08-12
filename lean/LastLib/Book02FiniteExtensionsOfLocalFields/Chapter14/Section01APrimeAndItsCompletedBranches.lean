import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14.Dependencies

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter14

noncomputable section

open scoped BigOperators NumberField TensorProduct

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
  sorry

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
  sorry

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

/- The finite degree of an individual completed branch is `e f`.  The
   equalities identifying the canonical global ideal invariants with the
   normalized local invariants are kept as hypotheses so this declaration can
   be reused before a dedicated number-field completion bridge is added. -/
theorem chapter14_completed_branch_degree
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F) (P : Chapter14PrimeAbove F E p)
    [Algebra F (chapter14BaseCompletion F p)]
    [Algebra (chapter14BaseCompletion F p)
      (chapter14BranchCompletion F E p P)]
    [FiniteDimensional (chapter14BaseCompletion F p)
      (chapter14BranchCompletion F E p P)]
    (e f : ℕ)
    (he : chapter14RamificationIndex E p P = e)
    (hf : chapter14ResidueDegree E p P = f) :
    Module.finrank (chapter14BaseCompletion F p)
        (chapter14BranchCompletion F E p P) = e * f := by
  sorry

/- DEPENDENCY_GUESS: The preceding chapters expose the `e f` formula for a
   valuation extension and the canonical ideal invariants separately, but do
   not yet expose their identification for this prime-above subtype. -/

theorem chapter14_sum_of_completed_branch_degrees
    {F : Type u} (E : Type v) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    (p : Chapter14Prime F)
    [Module.Finite (𝓞 F) (𝓞 E)] [Module.Flat (𝓞 F) (𝓞 E)]
    [Fintype (p.asIdeal.primesOver (𝓞 E))] :
    Module.finrank F E =
      ∑ P : Chapter14PrimeAbove F E p,
        chapter14RamificationIndex E p P * chapter14ResidueDegree E p P := by
  sorry

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
      one_mem' := by sorry
      mul_mem' := by sorry
      inv_mem' := by sorry }

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
  sorry

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
