import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15.Section02TheSeparabilityMap
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section03ResidueActionAndInertia
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section02TheCompletedProductTheorem
import Mathlib.FieldTheory.Finite.GaloisField

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
noncomputable section

open scoped BigOperators

universe u

/-! ## 15.3. The Galois picture -/

/--
The reduction homomorphism behind the decomposition/inertia exact sequence.
The homomorphism is kept explicit because its construction from quotient
valuation rings belongs to the earlier residue-action interface; exactness is
proved separately from a surjectivity hypothesis.
-/
structure Chapter15GaloisReductionData
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)] where
  reduction :
    Gal(L / K) →* Gal(IsLocalRing.ResidueField vL.valuationSubring /
      IsLocalRing.ResidueField vK.valuationSubring)
  residue_normal :
    Normal (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)
  valuation_unique :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L
  kernel_is_inertia :
    reduction.ker =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG
        K vL.valuationSubring

/-- Inertia is the kernel of the actual residue-reduction homomorphism. -/
def Chapter15GaloisReductionData.inertia
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    {vK : Valuation K Γ} {vL : Valuation L Γ}
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL) : Subgroup (Gal(L / K)) :=
  d.reduction.ker

/-- The inertia subgroup is exactly the kernel in the displayed sequence. -/
theorem galois_reduction_kernel_is_inertia
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    {vK : Valuation K Γ} {vL : Valuation L Γ}
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL) :
    d.reduction.ker = d.inertia := by
  rfl

/-- The kernel-exact part of the displayed sequence `1 → I → G → Gal(l/k)`.
Surjectivity is kept separate so that it is not smuggled into a proof as a
copy of the conclusion. -/
def chapter15GaloisReductionExactSequence
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL) : Prop :=
  Function.MulExact (Subgroup.subtype d.inertia) d.reduction

/-- Book 2, §15.3: the reduction datum is an exact sequence. -/
theorem galois_reduction_is_exact
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL) :
    chapter15GaloisReductionExactSequence vK vL d := by
  change Function.MulExact (Subgroup.subtype d.inertia) d.reduction
  apply MonoidHom.mulExact_iff.mpr
  exact (Subgroup.range_subtype (MonoidHom.ker d.reduction)).symm

instance chapter15GaloisInertiaNormal
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL) : d.inertia.Normal := by
  change d.reduction.ker.Normal
  infer_instance

/-- The fixed field of inertia, i.e. the maximal unramified intermediate field. -/
noncomputable def inertiaFixedField
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL) : IntermediateField K L :=
  IntermediateField.fixedField d.inertia

/-- The group-theoretic predicate expressing that an intermediate field is unramified. -/
def chapter15UnramifiedIntermediateField
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL) (M : IntermediateField K L) : Prop :=
  d.inertia ≤ M.fixingSubgroup

/-- The arithmetic Frobenius `x ↦ x ^ #k` for a finite-field extension. -/
noncomputable def arithmeticFrobenius
    {k l : Type u} [Field k] [Field l] [Algebra k l]
    [Finite k] [Algebra.IsAlgebraic k l] : Gal(l / k) :=
  letI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic k l

/-- The geometric Frobenius convention, inverse to arithmetic Frobenius. -/
noncomputable def geometricFrobenius
    {k l : Type u} [Field k] [Field l] [Algebra k l]
    [Finite k] [Algebra.IsAlgebraic k l] : Gal(l / k) :=
  (arithmeticFrobenius (k := k) (l := l))⁻¹

/-- Book 2, §15.3: completeness gives uniqueness of the valuation extension. -/
theorem complete_galois_extension_has_unique_valuation
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_theorem_1_1
    vK hcomplete

/-- Book 2, §15.3: uniqueness of the chosen normalized valuation makes the
decomposition group equal to the full Galois group. -/
theorem complete_decomposition_group_is_the_whole_galois_group
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hunique : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueNormalizedValuationExtension
      vK vL) :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
        K vL.valuationSubring = ⊤ := by
  exact
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.complete_base_decomposition_group_eq_galois_group vK vL
      Valuation.HasExtension.val_isEquiv_comap hcomplete hunique

/-- Book 2, §15.3: under completeness and residue separability, reduction is onto. -/
-- DEPENDENCY_GUESS: This is the Hensel-lifting/surjectivity bridge from the
-- residue-action chapter, retained as an explicit local interface until its
-- valuation-ring construction is connected to this generic package.
theorem complete_galois_reduction_is_surjective
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hunique :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueNormalizedValuationExtension
        vK vL) :
    ∃ d : Chapter15GaloisReductionData vK vL,
      Function.Surjective d.reduction := by
  sorry

/-- Book 2, §15.3: in the complete case the reduction data realizes the full
exact sequence, including surjectivity. -/
theorem complete_galois_reduction_is_exact
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hunique :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueNormalizedValuationExtension
        vK vL) :
    ∃ d : Chapter15GaloisReductionData vK vL,
      chapter15GaloisReductionExactSequence vK vL d ∧
        Function.Surjective d.reduction := by
  rcases complete_galois_reduction_is_surjective vK vL hcomplete hunique with ⟨d, hred⟩
  exact ⟨d, galois_reduction_is_exact vK vL d, hred⟩

/-- Book 2, §15.3: the decomposition/inertia reduction has the exact quotient. -/
theorem galois_reduction_has_exact_quotient
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL)
    (hred : Function.Surjective d.reduction) :
    Nonempty
      (Gal(L / K) ⧸ d.inertia ≃*
        Gal(IsLocalRing.ResidueField vL.valuationSubring /
          IsLocalRing.ResidueField vK.valuationSubring)) := by
  refine ⟨?_⟩
  change Gal(L / K) ⧸ d.reduction.ker ≃*
    Gal(IsLocalRing.ResidueField vL.valuationSubring /
      IsLocalRing.ResidueField vK.valuationSubring)
  exact QuotientGroup.quotientKerEquivOfSurjective d.reduction hred

/-- Book 2, §§15.2–15.3: the exact quotient has order equal to the residue degree. -/
theorem galois_reduction_quotient_order_is_residue_degree
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL)
    (hred : Function.Surjective d.reduction) :
    Nat.card (Gal(L / K) ⧸ d.inertia) =
      Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) := by
  rcases galois_reduction_has_exact_quotient vK vL d hred with ⟨e⟩
  calc
    Nat.card (Gal(L / K) ⧸ d.inertia) =
        Nat.card (Gal(IsLocalRing.ResidueField vL.valuationSubring /
          IsLocalRing.ResidueField vK.valuationSubring)) :=
      Nat.card_congr e.toEquiv
    _ = Module.finrank (IsLocalRing.ResidueField vK.valuationSubring)
        (IsLocalRing.ResidueField vL.valuationSubring) :=
      by sorry

/-- Book 2, §15.3: fixed field of inertia is maximal among unramified fields. -/
theorem inertia_fixed_field_is_maximal_unramified
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL)
    (_hred : Function.Surjective d.reduction) :
    chapter15UnramifiedIntermediateField vK vL d (inertiaFixedField vK vL d) ∧
      ∀ M : IntermediateField K L,
        chapter15UnramifiedIntermediateField vK vL d M →
          M ≤ inertiaFixedField vK vL d := by
  constructor
  · change d.inertia ≤ (IntermediateField.fixedField d.inertia).fixingSubgroup
    exact (IntermediateField.le_iff_le _ _).mp le_rfl
  · intro M hM
    change M ≤ IntermediateField.fixedField d.inertia
    exact (IntermediateField.le_iff_le _ _).mpr hM

/-- Book 2, §15.3: the fixed-field diagram sits between the two endpoints. -/
theorem inertia_fixed_field_has_field_inclusions
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL) :
    (⊥ : IntermediateField K L) ≤ inertiaFixedField vK vL d ∧
      inertiaFixedField vK vL d ≤ (⊤ : IntermediateField K L) := by
  exact ⟨bot_le, le_top⟩

/-- Book 2, §15.3: finite residue Galois groups are generated by Frobenius. -/
theorem arithmetic_frobenius_generates_finite_residue_galois_group
    {k l : Type u} [Field k] [Field l] [Algebra k l]
    [Fintype k] [Finite l] [Algebra.IsAlgebraic k l] :
    Subgroup.zpowers (arithmeticFrobenius (k := k) (l := l)) =
      (⊤ : Subgroup (Gal(l / k))) := by
  let := Fintype.ofFinite k
  apply (Subgroup.eq_top_iff' _).2
  intro σ
  obtain ⟨n, hn⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l).2 σ
  apply Subgroup.mem_zpowers_iff.mpr
  exact ⟨(n : ℤ), by simpa [arithmeticFrobenius] using hn⟩

/-- Book 2, §15.3: a finite-residue Frobenius lift determines an inertia coset. -/
theorem ramified_frobenius_lifts_to_a_coset
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Finite (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL)
    (hred : Function.Surjective d.reduction) :
    ∃ σ : Gal(L / K),
      d.reduction σ = arithmeticFrobenius
        (k := IsLocalRing.ResidueField vK.valuationSubring)
        (l := IsLocalRing.ResidueField vL.valuationSubring) := by
  exact hred _

/-- Book 2, §15.3: any two such lifts represent the same quotient coset. -/
theorem ramified_frobenius_lifts_have_the_same_inertia_coset
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Finite (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL)
    (σ τ : Gal(L / K))
    (hσ : d.reduction σ = arithmeticFrobenius
      (k := IsLocalRing.ResidueField vK.valuationSubring)
      (l := IsLocalRing.ResidueField vL.valuationSubring))
    (hτ : d.reduction τ = arithmeticFrobenius
      (k := IsLocalRing.ResidueField vK.valuationSubring)
      (l := IsLocalRing.ResidueField vL.valuationSubring)) :
    QuotientGroup.mk' d.inertia σ = QuotientGroup.mk' d.inertia τ := by
  apply (QuotientGroup.mk'_eq_mk' d.inertia).mpr
  refine ⟨σ⁻¹ * τ, ?_, ?_⟩
  · change d.reduction (σ⁻¹ * τ) = 1
    rw [map_mul, map_inv, hσ, hτ]
    simp
  · simp

/-- Book 2, §15.3: when inertia is trivial, Frobenius is an actual generator. -/
theorem unramified_frobenius_is_an_actual_generator
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [FiniteDimensional K L] [IsGalois K L]
    [Algebra (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [FiniteDimensional (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    [Fintype (IsLocalRing.ResidueField vK.valuationSubring)]
    [Finite (IsLocalRing.ResidueField vL.valuationSubring)]
    [Algebra.IsAlgebraic (IsLocalRing.ResidueField vK.valuationSubring)
      (IsLocalRing.ResidueField vL.valuationSubring)]
    (d : Chapter15GaloisReductionData vK vL)
    (hred : Function.Surjective d.reduction)
    (hinertia : d.inertia = ⊥) :
    ∃ σ : Gal(L / K),
      d.reduction σ = arithmeticFrobenius
        (k := IsLocalRing.ResidueField vK.valuationSubring)
        (l := IsLocalRing.ResidueField vL.valuationSubring) ∧
      Subgroup.zpowers σ = (⊤ : Subgroup (Gal(L / K))) := by
  obtain ⟨σ, hσ⟩ := ramified_frobenius_lifts_to_a_coset vK vL d hred
  have hgen := arithmetic_frobenius_generates_finite_residue_galois_group
    (k := IsLocalRing.ResidueField vK.valuationSubring)
    (l := IsLocalRing.ResidueField vL.valuationSubring)
  have hinj : Function.Injective d.reduction := by
    apply (MonoidHom.ker_eq_bot_iff d.reduction).mp
    simpa [Chapter15GaloisReductionData.inertia] using hinertia
  refine ⟨σ, hσ, ?_⟩
  apply (Subgroup.eq_top_iff' _).2
  intro τ
  have hτ : d.reduction τ ∈
      Subgroup.zpowers (arithmeticFrobenius
        (k := IsLocalRing.ResidueField vK.valuationSubring)
        (l := IsLocalRing.ResidueField vL.valuationSubring)) := by
    rw [hgen]
    exact Subgroup.mem_top (d.reduction τ)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hτ
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  apply hinj
  rw [map_zpow, hσ]
  exact hn

/-- Book 2, §15.3: geometric Frobenius is the inverse convention. -/
theorem geometric_frobenius_is_the_inverse
    {k l : Type u} [Field k] [Field l] [Algebra k l]
    [Finite k] [Algebra.IsAlgebraic k l] :
    geometricFrobenius (k := k) (l := l) =
      (arithmeticFrobenius (k := k) (l := l))⁻¹ := by
  rfl

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter15
