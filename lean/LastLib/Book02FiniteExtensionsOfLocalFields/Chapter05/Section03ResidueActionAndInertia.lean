import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section02DecompositionGroups

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.3. The residue action and inertia -/

/-- The residue field attached to a valuation subring. -/
abbrev chapter05ResidueField {E : Type*} [Field E] (A : ValuationSubring E) : Type _ :=
  IsLocalRing.ResidueField A

/-- The action of the decomposition group on the valuation ring. -/
noncomputable def chapter05ValuationRingAction
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05DecompositionGroup F A →* RingAut A :=
  MulSemiringAction.toRingAut _ _

/-- The induced action on the residue field. -/
noncomputable def chapter05ResidueAction
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05DecompositionGroup F A →* RingAut (IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut _ _

/-- Mathlib's inertia subgroup, exposed at the chapter namespace. -/
abbrev chapter05InertiaGroup
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    Subgroup (chapter05DecompositionGroup F A) :=
  ValuationSubring.inertiaSubgroup F A

/-- The inertia subgroup embedded in the ambient Galois group. -/
def chapter05InertiaGroupInG
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) : Subgroup (Gal(E / F)) :=
  (chapter05InertiaGroup F A).map (Subgroup.subtype _)

/-- Automorphisms of a residue extension that fix the base residue field. -/
def chapter05ResidueAutomorphismsOver
    (k l : Type*) [CommRing k] [CommRing l] [Algebra k l] :
    Subgroup (RingAut l) := by
  classical
  refine
    { carrier := {φ | ∀ x : k, φ (algebraMap k l x) = algebraMap k l x}
      one_mem' := ?_
      mul_mem' := ?_
      inv_mem' := ?_ }
  · intro φ ψ hφ hψ x
    change φ (ψ (algebraMap k l x)) = algebraMap k l x
    rw [hψ x, hφ x]
  · intro x
    rfl
  · intro φ hφ x
    apply φ.injective
    simpa using (hφ x).symm

/-- The residue automorphism target agrees with the Galois group in the finite Galois case. -/
theorem residue_automorphisms_over_base_is_galois_group
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Normal k l]
    (hseparable : Algebra.IsSeparable k l) :
    Nonempty
      (chapter05ResidueAutomorphismsOver k l ≃* Gal(l / k)) := by
  let ρ : chapter05ResidueAutomorphismsOver k l →* Gal(l / k) :=
    { toFun := fun φ => AlgEquiv.ofRingEquiv (f := φ.1) (φ.2)
      map_one' := by
        ext x
        rfl
      map_mul' := by
        intro φ ψ
        ext x
        rfl }
  refine ⟨MulEquiv.ofBijective ρ ?_⟩
  constructor
  · intro φ ψ h
    apply Subtype.ext
    ext x
    exact congrArg (fun σ : Gal(l / k) => σ x) h
  · intro σ
    refine ⟨⟨σ.toRingEquiv, fun x => σ.commutes x⟩, ?_⟩
    rfl

/-- Restriction of a residue action to automorphisms over the base. -/
def chapter05ResidueActionOverBase
    (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (k : Type*) [CommRing k]
    [Algebra k (IsLocalRing.ResidueField A)]
    (hbase : ∀ σ : chapter05DecompositionGroup F A, ∀ x : k,
      chapter05ResidueAction F A σ (algebraMap k (IsLocalRing.ResidueField A) x) =
        algebraMap k (IsLocalRing.ResidueField A) x) :
    chapter05DecompositionGroup F A →*
      chapter05ResidueAutomorphismsOver k (IsLocalRing.ResidueField A) :=
  (chapter05ResidueAction F A).codRestrict _ (fun σ => hbase σ)

/-- The Mathlib inertia subgroup is exactly the kernel of residue reduction. -/
theorem inertia_group_is_residue_action_kernel
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) :
    chapter05InertiaGroup F A = MonoidHom.ker (chapter05ResidueAction F A) := by
  rfl

/-- Kernel membership is invisibility on every residue class. -/
theorem inertia_mem_iff_residue_fixed
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) :
    σ ∈ chapter05InertiaGroup F A ↔
      ∀ x : IsLocalRing.ResidueField A,
        chapter05ResidueAction F A σ x = x := by
  rw [inertia_group_is_residue_action_kernel]
  change chapter05ResidueAction F A σ = 1 ↔ _
  constructor
  · intro h x
    exact congrArg (fun f : RingAut (IsLocalRing.ResidueField A) => f x) h
  · intro h
    ext x
    exact h x

/-- Reduction commutes with the residue action. -/
theorem residue_action_commutes_with_reduction
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A : ValuationSubring E) (σ : chapter05DecompositionGroup F A) (x : A) :
    IsLocalRing.residue A (σ • x) =
      chapter05ResidueAction F A σ (IsLocalRing.residue A x) := by
  rfl

/-- The first congruence condition is the elementary description of inertia. -/
theorem inertia_iff_positive_valuation_displacement
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    (w : AddValuation L (WithTop ℤ))
    (σ : chapter05DecompositionGroup F w.toValuation.valuationSubring) :
    σ ∈ chapter05InertiaGroup F w.toValuation.valuationSubring ↔
      ∀ x : w.toValuation.valuationSubring,
        w ((σ : Gal(L / F)) (x : L) - (x : L)) > 0 := by
  rw [inertia_mem_iff_residue_fixed]
  constructor
  · intro h x
    have hz : IsLocalRing.residue w.toValuation.valuationSubring
        (σ • x - x) = 0 := by
      rw [map_sub, residue_action_commutes_with_reduction]
      rw [h]
      exact sub_self _
    have hm : (σ • x - x) ∈
        IsLocalRing.maximalIdeal w.toValuation.valuationSubring :=
      (IsLocalRing.residue_eq_zero_iff _).mp hz
    have hv := (Valuation.mem_maximalIdeal_iff
      (v := w.toValuation)).mp hm
    change 0 < w ((σ : Gal(L / F)) (x : L) - (x : L)) at hv
    exact hv
  · intro h x
    rcases IsLocalRing.residue_surjective x with ⟨y, rfl⟩
    rw [← residue_action_commutes_with_reduction]
    apply sub_eq_zero.mp
    have hm : (σ • y - y) ∈
        IsLocalRing.maximalIdeal w.toValuation.valuationSubring := by
      have hv := h y
      apply (Valuation.mem_maximalIdeal_iff
        (v := w.toValuation)).mpr
      change 0 < w ((σ : Gal(L / F)) (y : L) - (y : L))
      exact hv
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hm

/-- The exactness assertion for a residue action whose kernel is inertia. -/
theorem residue_action_exact_sequence
    {D Q : Type*} [Group D] [Group Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ) :
    Function.MulExact (Subgroup.subtype (MonoidHom.ker ρ)) ρ ∧
      Function.Surjective ρ := by
  constructor
  · rw [MonoidHom.mulExact_iff]
    exact (Subgroup.range_subtype (MonoidHom.ker ρ)).symm
  · exact hρ

/--
 In the complete local Galois situation, separability of the residue
 extension is the hypothesis used by Hensel lifting to make the residue action
 surjective.
 -/
theorem residue_action_surjective_when_residue_separable
    {F E Γ : Type*} [Field F] [Field E] [Algebra F E]
    [LinearOrderedCommGroupWithZero Γ] [FiniteDimensional F E] [IsGalois F E]
    (v : Valuation F Γ) [Valuation.IsRankOneDiscrete v]
    (w : Valuation E Γ)
    (hext : v.IsEquiv (w.comap (algebraMap F E)))
    (hcomplete :
      IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring)
        v.valuationSubring)
    (hunique : chapter05UniqueNormalizedValuationExtension v w)
    [Algebra (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)]
    [Normal (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)]
    (hbase : ∀ σ : chapter05DecompositionGroup F w.valuationSubring, ∀ x :
      IsLocalRing.ResidueField v.valuationSubring,
      chapter05ResidueAction F w.valuationSubring σ
          (algebraMap (IsLocalRing.ResidueField v.valuationSubring)
            (IsLocalRing.ResidueField w.valuationSubring) x) =
        algebraMap (IsLocalRing.ResidueField v.valuationSubring)
          (IsLocalRing.ResidueField w.valuationSubring) x)
    (hseparable : Algebra.IsSeparable (IsLocalRing.ResidueField v.valuationSubring)
      (IsLocalRing.ResidueField w.valuationSubring)) :
    Function.Surjective
      (chapter05ResidueActionOverBase F w.valuationSubring
        (IsLocalRing.ResidueField v.valuationSubring) hbase) := by
  sorry

/-- Finite exact residue sequences account for the group order as `|I| · |Q|`. -/
theorem residue_exact_sequence_cardinality
    {D Q : Type*} [Group D] [Group Q] [Finite D] [Finite Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ) :
    Nat.card D = Nat.card (MonoidHom.ker ρ) * Nat.card Q := by
  calc
    Nat.card D = Nat.card (MonoidHom.ker ρ) *
        (MonoidHom.ker ρ).index :=
      (MonoidHom.ker ρ).card_mul_index.symm
    _ = Nat.card (MonoidHom.ker ρ) * Nat.card (D ⧸ MonoidHom.ker ρ) := by
      rw [Subgroup.index_eq_card]
    _ = Nat.card (MonoidHom.ker ρ) * Nat.card Q := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv]

/-- The residue quotient cannot recover the full residue degree in an inseparable case. -/
theorem inseparable_residue_automorphism_group_is_strictly_smaller
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (hinsep : ¬Algebra.IsSeparable k l) :
    Nat.card (Gal(l / k)) < Module.finrank k l := by
  have hle : Nat.card (Gal(l / k)) ≤ Module.finrank k l := by
    rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  have hne : Nat.card (Gal(l / k)) ≠ Module.finrank k l := by
    intro h
    letI : IsGalois k l := IsGalois.of_card_aut_eq_finrank k l h
    exact hinsep (inferInstance : Algebra.IsSeparable k l)
  exact lt_of_le_of_ne hle hne

/-- Perfect residue fields make every finite residue extension separable. -/
theorem perfect_residue_field_has_separable_finite_extensions
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [PerfectField k] :
    Algebra.IsSeparable k l := by
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- A finite residue field is perfect, so it has no inseparability obstruction. -/
theorem finite_residue_field_is_perfect
    (k : Type*) [Field k] [Finite k] : PerfectField k := by
  infer_instance

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05
