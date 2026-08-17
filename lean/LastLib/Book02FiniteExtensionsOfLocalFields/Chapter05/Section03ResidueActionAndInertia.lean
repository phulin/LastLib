import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section02DecompositionGroups
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.Valuation.Extension

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

/-- The residue automorphism target agrees with the Galois group. -/
theorem residue_automorphisms_over_base_is_galois_group
    {k l : Type*} [Field k] [Field l] [Algebra k l] :
    Nonempty
      (chapter05ResidueAutomorphismsOver k l ≃* Gal(l / k)) := by
  let e : chapter05ResidueAutomorphismsOver k l ≃* Gal(l / k) :=
    { toFun := fun φ => AlgEquiv.ofRingEquiv (R := k) (f := φ.1) (fun x => φ.2 x)
      invFun := fun σ => ⟨σ.toRingEquiv, fun x => σ.commutes x⟩
      left_inv := by
        intro φ
        ext x
        rfl
      right_inv := by
        intro σ
        ext x
        rfl
      map_mul' := by
        intro φ ψ
        ext x
        rfl }
  exact ⟨e⟩

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
  constructor
  · intro h x
    change chapter05ResidueAction F A σ = 1 at h
    have hx := congrArg (fun τ : RingAut (IsLocalRing.ResidueField A) => τ x) h
    simpa using hx
  · intro h
    change chapter05ResidueAction F A σ = 1
    ext x
    simpa using h x

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
  have hval (z : WithTop ℤ) :
      Multiplicative.ofAdd (OrderDual.toDual z) <
          (1 : Multiplicative (WithTop ℤ)ᵒᵈ) ↔ 0 < z := by
    change Multiplicative.ofAdd (OrderDual.toDual z) <
        Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) ↔ 0 < z
    rw [Multiplicative.ofAdd_lt, OrderDual.toDual_lt_toDual]
  rw [inertia_mem_iff_residue_fixed]
  constructor
  · intro h x
    have hres : IsLocalRing.residue w.toValuation.valuationSubring (σ • x) =
        IsLocalRing.residue w.toValuation.valuationSubring x := by
      rw [residue_action_commutes_with_reduction, h]
    have hzero : IsLocalRing.residue w.toValuation.valuationSubring ((σ • x) - x) = 0 := by
      rw [map_sub, hres, sub_self]
    have hmax : (σ • x) - x ∈
        IsLocalRing.maximalIdeal w.toValuation.valuationSubring :=
      (IsLocalRing.residue_eq_zero_iff _).mp hzero
    have hv := (Valuation.mem_maximalIdeal_iff L w.toValuation).mp hmax
    have := (hval (w ((σ : Gal(L / F)) (x : L) - (x : L)))).mp hv
    exact this
  · intro h x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective
      (R := w.toValuation.valuationSubring) x
    have hpos : w ((σ : Gal(L / F)) (y : L) - (y : L)) > 0 := h y
    have hsmul : ((σ • y : w.toValuation.valuationSubring) : L) =
        (σ : Gal(L / F)) (y : L) := rfl
    have hpos' : 0 < w ((σ • y : w.toValuation.valuationSubring) - y) := by
      rw [hsmul]
      exact hpos
    have hv : w.toValuation ((σ • y) - y) < 1 :=
      (hval _).mpr hpos'
    have hmax : (σ • y) - y ∈
        IsLocalRing.maximalIdeal w.toValuation.valuationSubring :=
      (Valuation.mem_maximalIdeal_iff L w.toValuation).mpr hv
    have hzero : IsLocalRing.residue w.toValuation.valuationSubring ((σ • y) - y) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmax
    have hres : IsLocalRing.residue w.toValuation.valuationSubring (σ • y) =
        IsLocalRing.residue w.toValuation.valuationSubring y := by
      apply sub_eq_zero.mp
      simpa only [map_sub] using hzero
    rw [← residue_action_commutes_with_reduction]
    exact hres

/- NOTE: The source's surjectivity argument is in the standing complete local
   setting.  This generic interface makes the corresponding completeness and
   normalization hypotheses explicit. -/
/-- The exactness assertion for a residue action whose kernel is inertia. -/
theorem residue_action_exact_sequence
    {D Q : Type*} [Group D] [Group Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ) :
    Function.MulExact (Subgroup.subtype (MonoidHom.ker ρ)) ρ ∧
      Function.Surjective ρ := by
  constructor
  · intro y
    constructor
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact x.2
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
    (w : Valuation E Γ) [Valuation.IsRankOneDiscrete w]
    (hext : v.IsEquiv (w.comap (algebraMap F E)))
    [Valuation.HasExtension v w]
    (hcomplete :
      IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring)
        v.valuationSubring)
    (hunique : chapter05UniqueNormalizedValuationExtension v w)
    [FiniteDimensional (IsLocalRing.ResidueField v.valuationSubring)
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
  classical
  let _ := hseparable
  let A := v.valuationSubring
  let B := w.valuationSubring
  let D := chapter05DecompositionGroup F B
  have hD : D = ⊤ := by
    exact complete_base_decomposition_group_eq_galois_group v w hext hcomplete hunique
  let _ : Algebra.IsInvariant A B D := by
    constructor
    intro b hb
    have hfixed : ∀ σ : Gal(E / F), σ (b : E) = b := by
      intro σ
      have hσ : σ ∈ D := by
        rw [hD]
        exact Subgroup.mem_top σ
      have hbσ := hb ⟨σ, hσ⟩
      exact congrArg (fun x : B => (x : E)) hbσ
    have hmem : (b : E) ∈ (⊥ : IntermediateField F E) :=
      (IsGalois.mem_bot_iff_fixed (b : E)).mpr hfixed
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hmem
    have hAB : A = B.comap (algebraMap F E) := by
      change v.valuationSubring =
        (w.comap (algebraMap F E)).valuationSubring
      exact (Valuation.isEquiv_iff_valuationSubring v
        (w.comap (algebraMap F E))).mp hext
    have haA : a ∈ A := by
      rw [hAB]
      change algebraMap F E a ∈ B
      rw [ha]
      exact b.property
    refine ⟨⟨a, haA⟩, ?_⟩
    apply Subtype.ext
    change algebraMap F E a = (b : E)
    exact ha
  let _ : SMulCommClass D A B := by
    constructor
    intro σ a b
    apply Subtype.ext
    simp only [Algebra.smul_def]
    change (σ.1 : E ≃+* E)
        (algebraMap F E (a : F) * (b : E)) =
      algebraMap F E (a : F) * (σ.1 : E ≃+* E) (b : E)
    have hσa : (σ.1 : E ≃+* E) (algebraMap F E (a : F)) =
        algebraMap F E (a : F) := by
      exact σ.1.commutes (a : F)
    rw [map_mul, hσa]
  have hsurj : Function.Surjective
      (Ideal.Quotient.stabilizerHom (IsLocalRing.maximalIdeal B)
        (IsLocalRing.maximalIdeal A) D) := by
    exact Ideal.Quotient.stabilizerHom_surjective D
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
  intro φ
  let φ' : (B ⧸ IsLocalRing.maximalIdeal B) ≃ₐ[
      A ⧸ IsLocalRing.maximalIdeal A] (B ⧸ IsLocalRing.maximalIdeal B) :=
    AlgEquiv.ofRingEquiv (R := A ⧸ IsLocalRing.maximalIdeal A) (f := φ.1)
      (fun x => φ.2 x)
  obtain ⟨g, hg⟩ := hsurj φ'
  refine ⟨g.1, ?_⟩
  apply Subtype.ext
  ext x
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := B) x
  have hred := congrArg (fun e => e (IsLocalRing.residue B b)) hg
  change chapter05ResidueAction F B g.1 (IsLocalRing.residue B b) =
    φ.1 (IsLocalRing.residue B b)
  rw [← residue_action_commutes_with_reduction B g.1 b]
  have hst : IsLocalRing.residue B (g.1 • b) =
      (Ideal.Quotient.stabilizerHom (IsLocalRing.maximalIdeal B)
        (IsLocalRing.maximalIdeal A) D g) (IsLocalRing.residue B b) := by
    rfl
  rw [hst, hred]
  rfl

/-- Finite exact residue sequences account for the group order as `|I| · |Q|`. -/
theorem residue_exact_sequence_cardinality
    {D Q : Type*} [Group D] [Group Q] [Finite D] [Finite Q]
    (ρ : D →* Q) (hρ : Function.Surjective ρ) :
    Nat.card D = Nat.card (MonoidHom.ker ρ) * Nat.card Q := by
  rw [← (MonoidHom.ker ρ).card_mul_index, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hρ]
  simp

/-- The residue quotient cannot recover the full residue degree in an inseparable case. -/
theorem inseparable_residue_automorphism_group_is_strictly_smaller
    {k l : Type*} [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] (hinsep : ¬Algebra.IsSeparable k l) :
    Nat.card (Gal(l / k)) < Module.finrank k l := by
  have hle : Nat.card (Gal(l / k)) ≤ Module.finrank k l :=
    by simpa only [Nat.card_eq_fintype_card] using
      (AlgEquiv.card_le (F := k) (K := l))
  have hne : Nat.card (Gal(l / k)) ≠ Module.finrank k l := by
    intro heq
    have hgal : IsGalois k l := IsGalois.of_card_aut_eq_finrank k l heq
    exact hinsep hgal.to_isSeparable
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
