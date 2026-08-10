import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section01FromEmbeddingsToLocalSymmetries

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators Pointwise

/-! ## 5.2. Why a decomposition group is needed -/

/-- The Galois action on valuations, with the inverse convention from the book. -/
def chapter05ValuationAction
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (σ : Gal(E / F)) (w : Valuation E Γ) : Valuation E Γ :=
  w.comap σ.symm.toRingEquiv.toRingHom

/-- Pointwise form of the valuation action. -/
theorem chapter05ValuationAction_apply
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (σ : Gal(E / F)) (w : Valuation E Γ) (x : E) :
    chapter05ValuationAction σ w x = w (σ.symm x) := by
  rfl

/-- Valuations on `E` lying above the chosen valuation on `F`, up to equivalence. -/
def chapter05ValuationsAbove
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) : Set (Valuation E Γ) :=
  {w | v.IsEquiv (w.comap (algebraMap F E))}

/-- Mathlib's decomposition group, retained under a chapter-facing name. -/
abbrev chapter05DecompositionGroup
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) : Subgroup (Gal(E / F)) :=
  ValuationSubring.decompositionSubgroup F A

/-- The ideal-stabilizer condition used for the integral-closure formulation. -/
def chapter05BranchIdealStabilized
    {B : Type*} [CommRing B] (P : Ideal B) (τ : B ≃+* B) : Prop :=
  Ideal.map τ.toRingHom P = P

/-- Membership in the decomposition group is stabilization of the valuation ring. -/
theorem decomposition_group_membership_iff_valuation_ring_stable
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : Gal(E / F)) :
    σ ∈ chapter05DecompositionGroup F A ↔ σ • A = A := by
  rfl

/-- A decomposition-group automorphism preserves the maximal ideal. -/
theorem decomposition_group_preserves_maximal_ideal
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) :
    ∀ x : A,
      x ∈ IsLocalRing.maximalIdeal A ↔ σ • x ∈ IsLocalRing.maximalIdeal A := by
  sorry

/-- The same action preserves every power of the maximal ideal. -/
theorem decomposition_group_preserves_maximal_ideal_powers
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) (n : ℕ) :
    ∀ x : A,
      x ∈ (IsLocalRing.maximalIdeal A) ^ n ↔
        σ • x ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  sorry

/-- A decomposition-group element preserves the corresponding valuation up to equivalence. -/
theorem decomposition_group_stabilizes_the_valuation
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation E Γ) (σ : Gal(E / F))
    (hσ : σ ∈ chapter05DecompositionGroup F w.valuationSubring) :
    (chapter05ValuationAction σ w).IsEquiv w := by
  sorry

/-- The Galois group acts transitively on the valuations above a base valuation. -/
theorem galois_group_transitive_on_valuations_above
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) :
    ∀ ⦃w₁ w₂ : Valuation E Γ⦄,
      w₁ ∈ chapter05ValuationsAbove v → w₂ ∈ chapter05ValuationsAbove v →
        ∃ σ : Gal(E / F), chapter05ValuationAction σ w₁ = w₂ := by
  sorry

/-- The number of branches is the cardinality of the valuation set above `v`. -/
def chapter05BranchCount
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) : ℕ :=
  Nat.card {w : Valuation E Γ // w ∈ chapter05ValuationsAbove v}

/-- Orbit--stabilizer identifies the branch count with the decomposition index. -/
theorem branch_count_eq_decomposition_index
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w ∈ chapter05ValuationsAbove v)
    (htrans :
      ∀ ⦃w₁ w₂ : Valuation E Γ⦄,
        w₁ ∈ chapter05ValuationsAbove v → w₂ ∈ chapter05ValuationsAbove v →
          ∃ σ : Gal(E / F), chapter05ValuationAction σ w₁ = w₂) :
    chapter05BranchCount (E := E) v =
      (chapter05DecompositionGroup F w.valuationSubring).index := by
  sorry

/-- A completion of a valued field, using Mathlib's valuation completion. -/
abbrev chapter05ValuationCompletion
    {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) : Type _ :=
  v.Completion

/--
 The global decomposition group becomes the Galois group of the selected
 completed branch.  The algebra and Galois instances on the completions make
 the intended local-field structure explicit.
 -/
theorem decomposition_group_is_completion_galois_group
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w ∈ chapter05ValuationsAbove v)
    [Algebra (v.Completion) (w.Completion)]
    [FiniteDimensional (v.Completion) (w.Completion)]
    [IsGalois (v.Completion) (w.Completion)] :
    Nonempty
      (chapter05DecompositionGroup F w.valuationSubring ≃*
        Gal(w.Completion / v.Completion)) := by
  sorry

/-- Over a complete base, the unique branch makes the decomposition group all of `G`. -/
theorem complete_base_decomposition_group_eq_galois_group
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional K L] [IsGalois K L]
    (v : Valuation K Γ) (w : Valuation L Γ)
    (hext : v.IsEquiv (w.comap (algebraMap K L)))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring)
      v.valuationSubring)
    (hunique : chapter05UniqueNormalizedValuationExtension v w) :
    chapter05DecompositionGroup K w.valuationSubring = ⊤ := by
  sorry

/-- A convenient pointwise version of the preceding local conclusion. -/
theorem complete_base_every_galois_automorphism_preserves_the_branch
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional K L] [IsGalois K L]
    (v : Valuation K Γ) (w : Valuation L Γ)
    (hext : v.IsEquiv (w.comap (algebraMap K L)))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring)
      v.valuationSubring)
    (hunique : chapter05UniqueNormalizedValuationExtension v w) :
    ∀ σ : Gal(L / K), σ ∈ chapter05DecompositionGroup K w.valuationSubring := by
  intro σ
  rw [complete_base_decomposition_group_eq_galois_group v w hext hcomplete hunique]
  exact Subgroup.mem_top σ

/-- Stabilization of the valuation-center ideal under a compatible symmetry. -/
theorem decomposition_stabilizes_the_integral_closure_branch
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    {B : Type*} [CommRing B] [Algebra B L]
    (w : Valuation L Γ) (P : Ideal B) (ι : B →+* L)
    (τ : B ≃+* B) (σ : L ≃+* L)
    (hcenter : ∀ x : B, x ∈ P ↔ w (ι x) < 1)
    (hcompat : ∀ x : B, ι (τ x) = σ (ι x))
    (hσ : chapter05ValuationPreserving w σ) :
    chapter05BranchIdealStabilized P τ := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
