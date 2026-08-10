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

/-
Valuation subrings on `E` lying above the chosen valuation ring on `F`.
Mathlib identifies equivalent valuations with the same valuation subring, so
these are the actual branches counted by the decomposition group.
-/
def chapter05ValuationsAbove
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) : Set (ValuationSubring E) :=
  {A | A.comap (algebraMap F E) = v.valuationSubring}

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
  intro x
  let f : RingAut A := MulSemiringAction.toRingAut _ _ σ
  change x ∈ IsLocalRing.maximalIdeal A ↔ f x ∈ IsLocalRing.maximalIdeal A
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal]
  exact (not_congr (isUnit_map_iff f x)).symm

/-- The same action preserves every power of the maximal ideal. -/
theorem decomposition_group_preserves_maximal_ideal_powers
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) (n : ℕ) :
    ∀ x : A,
      x ∈ (IsLocalRing.maximalIdeal A) ^ n ↔
        σ • x ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  intro x
  let f : RingAut A := MulSemiringAction.toRingAut _ _ σ
  change x ∈ (IsLocalRing.maximalIdeal A) ^ n ↔
    f x ∈ (IsLocalRing.maximalIdeal A) ^ n
  have hmap : Ideal.map f
        ((IsLocalRing.maximalIdeal A) ^ n) =
      (IsLocalRing.maximalIdeal A) ^ n := by
    rw [Ideal.map_pow]
    exact congrArg
      (fun I : Ideal A => I ^ n) (IsLocalRing.map_ringEquiv_maximalIdeal f)
  constructor
  · intro hx
    have hx' : f x ∈ Ideal.map f
        ((IsLocalRing.maximalIdeal A) ^ n) := Ideal.mem_map_of_mem f hx
    rw [hmap] at hx'
    exact hx'
  · intro hx
    have hx' : f x ∈ Ideal.map f
        ((IsLocalRing.maximalIdeal A) ^ n) := by
      rw [hmap]
      exact hx
    exact (Ideal.apply_mem_of_equiv_iff (f := f)
      (I := (IsLocalRing.maximalIdeal A) ^ n) (x := x)).mp hx'

/-- A decomposition-group element preserves the corresponding valuation up to equivalence. -/
theorem decomposition_group_stabilizes_the_valuation
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation E Γ) (σ : Gal(E / F))
    (hσ : σ ∈ chapter05DecompositionGroup F w.valuationSubring) :
    (chapter05ValuationAction σ w).IsEquiv w := by
  rw [Valuation.isEquiv_iff_valuationSubring]
  have hval : (chapter05ValuationAction σ w).valuationSubring =
      (σ : Gal(E / F)) • w.valuationSubring := by
    ext x
    change w (σ.symm x) ≤ 1 ↔ x ∈ (σ : Gal(E / F)) • w.valuationSubring
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [hval]
  exact decomposition_group_membership_iff_valuation_ring_stable
    w.valuationSubring σ |>.mp hσ

/-- The Galois group acts transitively on the branches above a base valuation. -/
theorem galois_group_transitive_on_valuations_above
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) :
    ∀ ⦃A₁ A₂ : ValuationSubring E⦄,
      A₁ ∈ chapter05ValuationsAbove v → A₂ ∈ chapter05ValuationsAbove v →
        ∃ σ : Gal(E / F), σ • A₁ = A₂ := by
  sorry

/-- The number of branches is the cardinality of the branch set above `v`. -/
def chapter05BranchCount
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) : ℕ :=
  Nat.card {A : ValuationSubring E // A ∈ chapter05ValuationsAbove v}

/-- Orbit--stabilizer identifies the branch count with the decomposition index. -/
theorem branch_count_eq_decomposition_index
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (A : ValuationSubring E)
    (hA : A ∈ chapter05ValuationsAbove v)
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite)
    (htrans :
      ∀ ⦃A₁ A₂ : ValuationSubring E⦄,
        A₁ ∈ chapter05ValuationsAbove v → A₂ ∈ chapter05ValuationsAbove v →
          ∃ σ : Gal(E / F), σ • A₁ = A₂) :
    chapter05BranchCount (E := E) v =
      (chapter05DecompositionGroup F A).index := by
  have hstable : ∀ (σ : Gal(E / F)) (B : ValuationSubring E),
      B ∈ chapter05ValuationsAbove v →
        σ • B ∈ chapter05ValuationsAbove v := by
    intro σ B hB
    ext x
    rw [ValuationSubring.mem_comap]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change (σ⁻¹ : Gal(E / F)) (algebraMap F E x) ∈ B ↔
      x ∈ v.valuationSubring
    rw [(σ⁻¹ : Gal(E / F)).commutes x]
    change x ∈ B.comap (algebraMap F E) ↔ x ∈ v.valuationSubring
    rw [hB]
  have horbit : MulAction.orbit (Gal(E / F)) A =
      chapter05ValuationsAbove v := by
    ext B
    constructor
    · rintro ⟨σ, rfl⟩
      exact hstable σ A hA
    · intro hB
      exact htrans hA hB
  calc
    chapter05BranchCount (E := E) v =
        (chapter05ValuationsAbove v).ncard :=
      Nat.card_coe_set_eq _
    _ = (MulAction.orbit (Gal(E / F)) A).ncard := by rw [horbit]
    _ = (MulAction.stabilizer (Gal(E / F)) A).index :=
      (MulAction.index_stabilizer (Gal(E / F)) A).symm
    _ = (chapter05DecompositionGroup F A).index := rfl

/-- A completion of a valued field, using Mathlib's valuation completion. -/
abbrev chapter05ValuationCompletion
    {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation F Γ) : Type _ :=
  v.Completion

/--
 The global decomposition group becomes the Galois group of the selected
 completed branch.  The `IsGaloisGroup` hypothesis is the explicit interface
 for the induced completed action; it is not implied by an unrelated
 `IsGalois` instance on the completed fields.
 -/
theorem decomposition_group_is_completion_galois_group
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) (w : Valuation E Γ)
    (hw : w.valuationSubring ∈ chapter05ValuationsAbove v)
    [Algebra (v.Completion) (w.Completion)]
    [FiniteDimensional (v.Completion) (w.Completion)]
    [MulSemiringAction (chapter05DecompositionGroup F w.valuationSubring)
      (w.Completion)]
    [Finite (chapter05DecompositionGroup F w.valuationSubring)]
    (hD : IsGaloisGroup (chapter05DecompositionGroup F w.valuationSubring)
      (v.Completion) (w.Completion)) :
    Nonempty
      (chapter05DecompositionGroup F w.valuationSubring ≃*
        Gal(w.Completion / v.Completion)) := by
  letI := hD
  exact ⟨IsGaloisGroup.mulEquivAlgEquiv
    (chapter05DecompositionGroup F w.valuationSubring)
    (v.Completion) (w.Completion)⟩

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
  rw [eq_top_iff]
  intro σ
  intro _
  apply (decomposition_group_membership_iff_valuation_ring_stable
    w.valuationSubring σ).mpr
  have hcomap :
      (chapter05ValuationAction σ w).comap (algebraMap K L) =
        w.comap (algebraMap K L) := by
    ext x
    change w (σ.symm (algebraMap K L x)) = w (algebraMap K L x)
    rw [σ.symm.commutes x]
  have hunique' : chapter05ValuationAction σ w = w :=
    hunique _ (by rw [hcomap]; exact hext)
  have hval : (chapter05ValuationAction σ w).valuationSubring =
      (σ : Gal(L / K)) • w.valuationSubring := by
    ext x
    change w (σ.symm x) ≤ 1 ↔ x ∈ (σ : Gal(L / K)) • w.valuationSubring
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [← hval, hunique']

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
  unfold chapter05BranchIdealStabilized
  ext x
  have hmem : x ∈ Ideal.map τ.toRingHom P ↔
      ∃ y, y ∈ P ∧ τ.toRingHom y = x := by
    exact Ideal.mem_map_iff_of_surjective τ.toRingHom τ.surjective
  rw [hmem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (hcenter (τ y)).mpr
    rw [hcompat y, hσ]
    exact (hcenter y).mp hy
  · intro hx
    refine ⟨τ.symm x, ?_, by simp⟩
    apply (hcenter (τ.symm x)).mpr
    have hcompat' := hcompat (τ.symm x)
    have hval : w (ι x) = w (ι (τ.symm x)) := by
      calc
        w (ι x) = w (σ (ι (τ.symm x))) := by
          rw [← hcompat']
          simp
        _ = w (ι (τ.symm x)) := hσ _
    exact hval ▸ (hcenter x).mp hx

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
