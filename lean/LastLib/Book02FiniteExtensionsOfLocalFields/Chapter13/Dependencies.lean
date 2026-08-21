import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter02.Section03RamificationIndexAndResidueDegree
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.Section06TameBoundary
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13

noncomputable section

open Polynomial
open scoped BigOperators Pointwise Topology WithZero

universe u uK uL uGamma

/-! Shared interfaces for Chapter 13.  These are deliberately small bridges
between the valuation-ring APIs of Chapters 2, 7, 8, and 9 and the
classification statements in this chapter. -/

abbrev chapter13ValuationRing
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : Type _ :=
  v.valuationSubring

abbrev chapter13ResidueField
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : Type _ :=
  IsLocalRing.ResidueField v.valuationSubring

def chapter13CompleteDiscreteValuedField
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : Prop :=
  Valuation.IsRankOneDiscrete v ∧
    IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring)
      v.valuationSubring ∧
    Finite (IsLocalRing.ResidueField v.valuationSubring)

def chapter13FiniteResidueField
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) : Prop :=
  Finite (IsLocalRing.ResidueField v.valuationSubring)

/-! A concrete quotient of finite extension presentations records precisely
the `K`-isomorphism classes used by the two finiteness theorems. -/

structure Chapter13FiniteExtensionModel (K : Type u) [Field K] where
  carrier : Type u
  field_carrier : Field carrier
  algebra : Algebra K carrier
  finite_dimensional : FiniteDimensional K carrier

noncomputable def chapter13FiniteExtensionDegree
    {K : Type u} [Field K]
    (E : Chapter13FiniteExtensionModel K) : ℕ :=
  letI : Field E.carrier := E.field_carrier
  letI : Algebra K E.carrier := E.algebra
  letI : FiniteDimensional K E.carrier := E.finite_dimensional
  Module.finrank K E.carrier

def chapter13FiniteExtensionIso
    {K : Type u} [Field K]
    (E F : Chapter13FiniteExtensionModel K) : Prop :=
  letI : Field E.carrier := E.field_carrier
  letI : Algebra K E.carrier := E.algebra
  letI : FiniteDimensional K E.carrier := E.finite_dimensional
  letI : Field F.carrier := F.field_carrier
  letI : Algebra K F.carrier := F.algebra
  letI : FiniteDimensional K F.carrier := F.finite_dimensional
  Nonempty (E.carrier ≃ₐ[K] F.carrier)

def chapter13FiniteExtensionSetoid
    {K : Type u} [Field K] : Setoid (Chapter13FiniteExtensionModel K) where
  r := chapter13FiniteExtensionIso
  iseqv := by
    constructor
    · intro E
      let : Field E.carrier := E.field_carrier
      let : Algebra K E.carrier := E.algebra
      let : FiniteDimensional K E.carrier := E.finite_dimensional
      exact ⟨(AlgEquiv.refl : E.carrier ≃ₐ[K] E.carrier)⟩
    · intro E F h
      let : Field E.carrier := E.field_carrier
      let : Algebra K E.carrier := E.algebra
      let : FiniteDimensional K E.carrier := E.finite_dimensional
      let : Field F.carrier := F.field_carrier
      let : Algebra K F.carrier := F.algebra
      let : FiniteDimensional K F.carrier := F.finite_dimensional
      rcases h with ⟨e⟩
      exact ⟨e.symm⟩
    · intro E F G hEF hFG
      let : Field E.carrier := E.field_carrier
      let : Algebra K E.carrier := E.algebra
      let : FiniteDimensional K E.carrier := E.finite_dimensional
      let : Field F.carrier := F.field_carrier
      let : Algebra K F.carrier := F.algebra
      let : FiniteDimensional K F.carrier := F.finite_dimensional
      let : Field G.carrier := G.field_carrier
      let : Algebra K G.carrier := G.algebra
      let : FiniteDimensional K G.carrier := G.finite_dimensional
      rcases hEF with ⟨e⟩
      rcases hFG with ⟨f⟩
      exact ⟨e.trans f⟩

abbrev Chapter13FiniteExtensionClass (K : Type u) [Field K] : Type _ :=
  Quotient (chapter13FiniteExtensionSetoid (K := K))

def chapter13FiniteExtensionClassOf
    {K : Type u} [Field K]
    (E : Chapter13FiniteExtensionModel K) : Chapter13FiniteExtensionClass K :=
  Quotient.mk _ E

def chapter13BoundedDegreeClasses
    {K : Type u} [Field K] (N : ℕ) : Set (Chapter13FiniteExtensionClass K) :=
  {c | ∃ E : Chapter13FiniteExtensionModel K,
      chapter13FiniteExtensionClassOf E = c ∧
        chapter13FiniteExtensionDegree E ≤ N}

def chapter13DegreeClasses
    {K : Type u} [Field K] (d : ℕ) : Set (Chapter13FiniteExtensionClass K) :=
  {c | ∃ E : Chapter13FiniteExtensionModel K,
      chapter13FiniteExtensionClassOf E = c ∧
        chapter13FiniteExtensionDegree E = d}

def chapter13BoundedDegreeFiniteness
    {K : Type u} [Field K] (N : ℕ) : Prop :=
  Set.Finite (chapter13BoundedDegreeClasses (K := K) N)

theorem chapter13_mem_bounded_degree_classes_iff
    {K : Type u} [Field K] (N : ℕ)
    (c : Chapter13FiniteExtensionClass K) :
    c ∈ chapter13BoundedDegreeClasses N ↔
      ∃ E : Chapter13FiniteExtensionModel K,
        chapter13FiniteExtensionClassOf E = c ∧
          chapter13FiniteExtensionDegree E ≤ N :=
  Iff.rfl

theorem chapter13_mem_degree_classes_iff
    {K : Type u} [Field K] (d : ℕ)
    (c : Chapter13FiniteExtensionClass K) :
    c ∈ chapter13DegreeClasses d ↔
      ∃ E : Chapter13FiniteExtensionModel K,
        chapter13FiniteExtensionClassOf E = c ∧
          chapter13FiniteExtensionDegree E = d :=
  Iff.rfl

/-! The tame predicate uses the canonical ramification index and the
exponential characteristic of the residue field. -/

def chapter13TameExtension
    {K L ΓK ΓL : Type*} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (vK : Valuation K ΓK) (vL : Valuation L ΓL)
    [vK.HasExtension vL]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    [FiniteDimensional K L] : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09Tame
    (IsLocalRing.ResidueField vK.valuationSubring)
    (LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.chapterRamificationIndex
      vK.valuationSubring vL.valuationSubring
      (IsLocalRing.maximalIdeal vL.valuationSubring))

structure Chapter13ValuationExtensionWitness
  {K : Type uK} {L : Type uL} {ΓK : Type uGamma} [Field K] [Field L]
    [Algebra K L] [LinearOrderedCommGroupWithZero ΓK]
    (vK : Valuation K ΓK) [Valuation.IsRankOneDiscrete vK] where
  valueGroup : Type uL
  [valueGroupOrder : LinearOrderedCommGroupWithZero valueGroup]
  valuation : Valuation L valueGroup
  [extension : vK.HasExtension valuation]
  [discrete : Valuation.IsRankOneDiscrete valuation]
  [finite_extension : FiniteDimensional K L]
  tame : chapter13TameExtension vK valuation

def chapter13ModelHasTameWitness
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    [Valuation.IsRankOneDiscrete vK]
    (E : Chapter13FiniteExtensionModel K) : Prop :=
  letI : Field E.carrier := E.field_carrier
  letI : Algebra K E.carrier := E.algebra
  letI : FiniteDimensional K E.carrier := E.finite_dimensional
  Nonempty (Chapter13ValuationExtensionWitness vK (L := E.carrier))

def chapter13TameBoundedDegreeClasses
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    [Valuation.IsRankOneDiscrete vK] (N : ℕ) :
    Set (Chapter13FiniteExtensionClass K) :=
  {c | ∃ E : Chapter13FiniteExtensionModel K,
      chapter13FiniteExtensionClassOf E = c ∧
        chapter13FiniteExtensionDegree E ≤ N ∧
        chapter13ModelHasTameWitness vK E}

def chapter13TameBoundedDegreeFiniteness
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ)
    [Valuation.IsRankOneDiscrete vK] (N : ℕ) : Prop :=
  Set.Finite (chapter13TameBoundedDegreeClasses vK N)

/-! The local constancy bridge used in the compactness argument. -/

def chapter13LocallyConstant
    {P C : Type*} [TopologicalSpace P] (φ : P → C) : Prop :=
  ∀ x : P, ∃ U : Set P,
    IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, φ y = φ x

theorem chapter13_compact_locally_constant_range_finite
    {P C : Type*} [TopologicalSpace P]
    (φ : P → C) (hcompact : IsCompact (Set.univ : Set P))
    (hlocally_constant : chapter13LocallyConstant φ) :
    Set.Finite (Set.range φ) := by
  sorry

/-! Root fields are kept as actual intermediate fields, so the Krasner
interface compares book-facing generated fields by canonical `AlgEquiv`s. -/

noncomputable def chapter13RootField
    (E Ω : Type*) [Field E] [Field Ω] [Algebra E Ω]
    (α : Ω) : IntermediateField E Ω :=
  IntermediateField.adjoin E ({α} : Set Ω)

def chapter13RootFieldsEIsomorphic
    (E Ω : Type*) [Field E] [Field Ω] [Algebra E Ω]
    (α β : Ω) : Prop :=
  Nonempty (chapter13RootField E Ω α ≃ₐ[E] chapter13RootField E Ω β)

noncomputable def chapter13RootFieldExtensionModel
    (E Ω : Type u) [Field E] [Field Ω] [Algebra E Ω]
    (α : Ω) [FiniteDimensional E (chapter13RootField E Ω α)] :
    Chapter13FiniteExtensionModel E where
  carrier := chapter13RootField E Ω α
  field_carrier := inferInstance
  algebra := inferInstance
  finite_dimensional := inferInstance

noncomputable def chapter13RootFieldExtensionClass
    (E Ω : Type u) [Field E] [Field Ω] [Algebra E Ω]
    (α : Ω) [FiniteDimensional E (chapter13RootField E Ω α)] :
    Chapter13FiniteExtensionClass E :=
  chapter13FiniteExtensionClassOf (chapter13RootFieldExtensionModel E Ω α)

theorem chapter13_root_field_isomorphic_classes_equal
    (E Ω : Type u) [Field E] [Field Ω] [Algebra E Ω]
    (α β : Ω)
    [FiniteDimensional E (chapter13RootField E Ω α)]
    [FiniteDimensional E (chapter13RootField E Ω β)]
    (hiso : chapter13RootFieldsEIsomorphic E Ω α β) :
    chapter13RootFieldExtensionClass E Ω α =
      chapter13RootFieldExtensionClass E Ω β := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13
