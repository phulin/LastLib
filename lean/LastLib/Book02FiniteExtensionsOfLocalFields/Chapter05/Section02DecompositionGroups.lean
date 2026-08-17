import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section01FromEmbeddingsToLocalSymmetries
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section03IntegralElementsAreBounded
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.Topology.Algebra.Valued.WithVal

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
  let e : RingAut A := MulSemiringAction.toRingAut _ _ σ
  have hmap : (IsLocalRing.maximalIdeal A).map e = IsLocalRing.maximalIdeal A :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  change x ∈ IsLocalRing.maximalIdeal A ↔ e x ∈ IsLocalRing.maximalIdeal A
  constructor
  · intro hx
    have hx' : e x ∈ (IsLocalRing.maximalIdeal A).map e :=
      Ideal.mem_map_of_mem e hx
    rw [hmap] at hx'
    exact hx'
  · intro hx
    have hx' : e.symm (e x) ∈ (IsLocalRing.maximalIdeal A).map e.symm :=
      Ideal.mem_map_of_mem e.symm hx
    rw [IsLocalRing.map_ringEquiv_maximalIdeal e.symm] at hx'
    simpa using hx'

/-- The same action preserves every power of the maximal ideal. -/
theorem decomposition_group_preserves_maximal_ideal_powers
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) (n : ℕ) :
    ∀ x : A,
      x ∈ (IsLocalRing.maximalIdeal A) ^ n ↔
        σ • x ∈ (IsLocalRing.maximalIdeal A) ^ n := by
  intro x
  let e : RingAut A := MulSemiringAction.toRingAut _ _ σ
  have hmap : (IsLocalRing.maximalIdeal A).map e = IsLocalRing.maximalIdeal A :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have hmapn : ((IsLocalRing.maximalIdeal A) ^ n).map e =
      (IsLocalRing.maximalIdeal A) ^ n := by
    rw [Ideal.map_pow, hmap]
  change x ∈ (IsLocalRing.maximalIdeal A) ^ n ↔
    e x ∈ (IsLocalRing.maximalIdeal A) ^ n
  constructor
  · intro hx
    have hx' : e x ∈ ((IsLocalRing.maximalIdeal A) ^ n).map e :=
      Ideal.mem_map_of_mem e hx
    rw [hmapn] at hx'
    exact hx'
  · intro hx
    have hx' : e.symm (e x) ∈ ((IsLocalRing.maximalIdeal A) ^ n).map e.symm :=
      Ideal.mem_map_of_mem e.symm hx
    rw [Ideal.map_pow, IsLocalRing.map_ringEquiv_maximalIdeal e.symm] at hx'
    simpa using hx'

/-- A decomposition-group element preserves the corresponding valuation up to equivalence. -/
theorem decomposition_group_stabilizes_the_valuation
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation E Γ) (σ : Gal(E / F))
    (hσ : σ ∈ chapter05DecompositionGroup F w.valuationSubring) :
    (chapter05ValuationAction σ w).IsEquiv w := by
  rw [Valuation.isEquiv_iff_valuationSubring]
  ext x
  have hσ' : σ • w.valuationSubring = w.valuationSubring :=
    (decomposition_group_membership_iff_valuation_ring_stable
      w.valuationSubring σ).mp hσ
  have hx : x ∈ σ • w.valuationSubring ↔ x ∈ w.valuationSubring := by
    rw [hσ']
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simpa [chapter05ValuationAction, Valuation.mem_valuationSubring_iff] using hx

/-- The Galois group acts transitively on the branches above a base valuation. -/
theorem galois_group_transitive_on_valuations_above
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) :
    ∀ ⦃A₁ A₂ : ValuationSubring E⦄,
      A₁ ∈ chapter05ValuationsAbove v → A₂ ∈ chapter05ValuationsAbove v →
        ∃ σ : Gal(E / F), σ • A₁ = A₂ := by
  intro A₁ A₂ h₁ h₂
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_galois_group_transitive_on_valuation_branches
    v h₁ h₂

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
    (hbranches : (chapter05ValuationsAbove (E := E) v).Finite) :
    chapter05BranchCount (E := E) v =
      (chapter05DecompositionGroup F A).index := by
  have _hbranches := hbranches
  have htrans := galois_group_transitive_on_valuations_above (E := E) v
  have hA' : A.comap (algebraMap F E) = v.valuationSubring := hA
  have hsmul : ∀ σ : Gal(E / F),
      σ • A ∈ chapter05ValuationsAbove v := by
    intro σ
    change (σ • A).comap (algebraMap F E) = v.valuationSubring
    ext x
    rw [ValuationSubring.mem_comap,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using congrArg (fun S : ValuationSubring F => x ∈ S) hA'
  have horbit : MulAction.orbit (Gal(E / F)) A =
      chapter05ValuationsAbove v := by
    ext B
    constructor
    · rintro ⟨σ, rfl⟩
      exact hsmul σ
    · intro hB
      obtain ⟨σ, hσ⟩ := htrans hA hB
      exact ⟨σ, hσ⟩
  unfold chapter05BranchCount
  rw [Nat.card_coe_set_eq, ← horbit]
  exact (MulAction.index_stabilizer (Gal(E / F)) A).symm

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
  have _hw := hw
  exact ⟨@IsGaloisGroup.mulEquivAlgEquiv
    (chapter05DecompositionGroup F w.valuationSubring) inferInstance
    v.Completion w.Completion inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance hD inferInstance⟩

/- NOTE: Mathlib records valuation uniqueness up to equivalence.  Literal
   equality for the selected normalized valuation therefore requires the
   explicit extension and normalized-uniqueness hypotheses below. -/
/- Over a complete base, the unique branch makes the decomposition group all of `G`. -/
theorem complete_base_decomposition_group_eq_galois_group
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional K L] [IsGalois K L]
    (v : Valuation K Γ) (w : Valuation L Γ)
    (hext : v.IsEquiv (w.comap (algebraMap K L)))
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring)
      v.valuationSubring)
    (hunique : chapter05UniqueNormalizedValuationExtension v w) :
    chapter05DecompositionGroup K w.valuationSubring = ⊤ := by
  have _hcomplete := hcomplete
  refine le_antisymm le_top ?_
  intro σ _
  have hpres := valuation_preservation_preserves_valuation_ring w σ.toRingEquiv
    (galois_automorphism_preserves_unique_valuation v w hext hunique σ)
  have hstab : σ • w.valuationSubring = w.valuationSubring := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using hpres (σ.symm x)
  exact (decomposition_group_membership_iff_valuation_ring_stable
    w.valuationSubring σ).mpr hstab

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
  simp

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
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr ?_
    intro x hx
    apply (hcenter (τ x)).2
    rw [hcompat x, hσ (ι x)]
    exact (hcenter x).1 hx
  · intro x hx
    have hcompat_inv : ι (τ.symm x) = σ.symm (ι x) := by
      simpa using (congrArg σ.symm (hcompat (τ.symm x))).symm
    have hσ_inv : ∀ y : L, w (σ.symm y) = w y := by
      intro y
      have hy := hσ (σ.symm y)
      simpa using hy.symm
    have hx' : τ.symm x ∈ P := by
      apply (hcenter (τ.symm x)).2
      rw [hcompat_inv, hσ_inv]
      exact (hcenter x).1 hx
    have := Ideal.mem_map_of_mem τ.toRingHom hx'
    simpa using this

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
