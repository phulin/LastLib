import LastLib.Book01ValuationsDVRsAndCompletions.Chapter09
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01

noncomputable section

open scoped TensorProduct WithZero

/-! # Book 2, Chapter 1, Section 1.1

The declarations in this file fix the local-field notation used throughout the
chapter.  Valuation equivalence is kept separate from the normalized additive
valuation scale: the former describes the place and the latter records the
ramification factor.
-/

universe u

/-! ### The four structures attached to one valued field -/

/-- The valuation ring attached to a chosen valuation. -/
abbrev chapter01ValuationRing {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : Type _ :=
  v.valuationSubring

/-- The maximal ideal of the chosen valuation ring. -/
abbrev chapter01MaximalIdeal {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    Ideal (chapter01ValuationRing v) :=
  IsLocalRing.maximalIdeal (chapter01ValuationRing v)

/-- The residue field of the chosen valuation ring. -/
abbrev chapter01ResidueField {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) : Type _ :=
  IsLocalRing.ResidueField (chapter01ValuationRing v)

/-- Completeness and rank-one discreteness for a normalized multiplicative valuation. -/
def chapter01CompleteDiscreteValuation (K : Type*) [Field K]
    (v : Valuation K ℤᵐ⁰) : Prop :=
  Valuation.IsRankOneDiscrete v ∧
    IsAdicComplete (chapter01MaximalIdeal v) (chapter01ValuationRing v)

/-- A uniformizer in the valuation ring, expressed by its maximal-ideal equation. -/
def chapter01IsUniformizer {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (π : chapter01ValuationRing v) : Prop :=
  π ≠ 0 ∧ chapter01MaximalIdeal v = Ideal.span ({π} : Set (chapter01ValuationRing v))

/-- A discrete valuation ring has a generator for its maximal ideal. -/
theorem chapter01_complete_discrete_has_uniformizer
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    [Valuation.IsRankOneDiscrete v] :
    ∃ π : chapter01ValuationRing v, chapter01IsUniformizer v π := by
  obtain ⟨π, hπ⟩ :=
    Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial v
  refine ⟨π, ?_⟩
  exact ⟨by
    intro h
    apply hπ.ne_zero
    exact congrArg (fun y : chapter01ValuationRing v => (y : K)) h,
    hπ.is_generator⟩

/-! ### The uniqueness bridge exported by the leaf interface -/

/-- Adic completeness of the valuation ring implies henselianity of the field. -/
theorem chapter01_complete_field_is_henselian
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    HenselianLocalRing vK.valuationSubring := by
  exact LastLib.Book01ValuationsDVRsAndCompletions.Chapter09.complete_separated_local_ring_is_henselian
    hcomplete

/-- Henselianity, rather than completeness, is enough for uniqueness of an algebraic extension. -/
theorem chapter01_henselian_discrete_field_unique_extension
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    (hH : HenselianLocalRing vK.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L := by
  have hiff :=
    List.TFAE.out
      (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.henselian_uniqueness_criterion vK) 0 1
  have hall :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueExtensionToEveryAlgebraicField vK :=
    hiff.mp hH
  exact hall L

/-- Theorem 1.1, in the heterogeneous value-group interface. -/
theorem chapter01_theorem_1_1
    {K L Γ : Type u} [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) [Valuation.IsRankOneDiscrete vK]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.hasUniqueValuationExtension vK L := by
  exact chapter01_henselian_discrete_field_unique_extension vK
    (chapter01_complete_field_is_henselian vK hcomplete)

/-! ### Normalized additive scales and compatible valuation rings -/

/-- The normalized additive restriction formula with its positive integer factor. -/
def chapter01ValuationRestrictionScale
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ) : Prop :=
  0 < e ∧ ∀ x : K, x ≠ 0 →
    vL (algebraMap K L x) = e • vK x

theorem chapter01_restriction_scale_pos
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ)
    (hscale : chapter01ValuationRestrictionScale vK vL e) :
    0 < e := hscale.1

theorem chapter01_restriction_scale_apply
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ)
    (hscale : chapter01ValuationRestrictionScale vK vL e)
    {x : K} (hx : x ≠ 0) :
    vL (algebraMap K L x) = e • vK x := hscale.2 x hx

/-- The multiplicative formulation of “the two valuations extend the same place”. -/
def chapter01SamePlace
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) : Prop :=
  vK.IsEquiv (vL.comap (algebraMap K L))

/-- An exact positive additive restriction scale determines the same place. -/
theorem chapter01_restriction_scale_is_same_place
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (e : ℕ)
    (hscale : chapter01ValuationRestrictionScale vK vL e) :
    chapter01SamePlace vK.toValuation vL.toValuation := by
  sorry

/-- Equivalent valuations have the same valuation subring after restriction. -/
theorem chapter01_same_place_iff_valuation_subring_eq
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ) :
    chapter01SamePlace vK vL ↔
      vK.valuationSubring =
        (vL.comap (algebraMap K L)).valuationSubring := by
  exact Valuation.isEquiv_iff_valuationSubring
    (v₁ := vK) (v₂ := vL.comap (algebraMap K L))

/-- Same-place valuations have the same integral elements on the base field. -/
theorem chapter01_same_place_mem_valuation_subring_iff
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    (h : chapter01SamePlace vK vL) (x : K) :
    x ∈ vK.valuationSubring ↔
      algebraMap K L x ∈ vL.valuationSubring := by
  change vK x ≤ 1 ↔ vL (algebraMap K L x) ≤ 1
  exact (show vK.IsEquiv (vL.comap (algebraMap K L)) from h).le_one_iff_le_one

/-- Equivalent valuations induce uniformly equivalent valuation topologies. -/
theorem chapter01_same_place_uniform_equiv
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    (h : chapter01SamePlace vK vL) :
    Nonempty
      (WithVal vK ≃ᵤ WithVal (vL.comap (algebraMap K L))) := by
  exact ⟨(show vK.IsEquiv (vL.comap (algebraMap K L)) from h).uniformEquiv⟩

/-- For normalized discrete additive valuations, restriction changes only by a scale. -/
theorem chapter01_normalized_restriction_scale_exists
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hvK : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (_hvL : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hext : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
    ∃ e : ℕ, chapter01ValuationRestrictionScale vK vL e := by
  obtain ⟨e, he, hscale⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_normalized_restriction_formula
      vK vL hvK _hvL hext
  exact ⟨e, he, hscale⟩

/-! ### The finite extension is still local -/

/-- In a finite complete extension, the upper valuation ring is complete, finite, and a DVR. -/
theorem chapter01_finite_extension_remains_local
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    Module.Finite vK.valuationSubring vL.valuationSubring ∧
      Module.Free vK.valuationSubring vL.valuationSubring ∧
      IsAdicComplete (IsLocalRing.maximalIdeal vL.valuationSubring)
        vL.valuationSubring ∧
      IsDiscreteValuationRing vL.valuationSubring := by
  have h :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring
      vK vL hcomplete
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- The upper valuation ring is the integral closure of the lower one. -/
theorem chapter01_extension_valuation_ring_is_integral_closure
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal vK.valuationSubring)
      vK.valuationSubring) :
    (vL.valuationSubring : Set L) =
      {x : L | IsIntegral vK.valuationSubring x} := by
  exact (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.finite_complete_extension_valuation_ring
    vK vL hcomplete).2.2.2.2

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01
