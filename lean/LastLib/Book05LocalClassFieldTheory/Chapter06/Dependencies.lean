import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Topology.Algebra.Group.Basic
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section03TheUnramifiedCase
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section04TheTotallyRamifiedCase
import LastLib.Book05LocalClassFieldTheory.Chapter02.Dependencies
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section06FiniteReciprocity

namespace LastLib.Book05LocalClassFieldTheory.Chapter06

noncomputable section

open scoped BigOperators

/-!
Shared interfaces for Chapter 6.

The source fixes one complete discretely valued field with finite residue field.
The valuation-ring and unit-filtration objects below are the canonical Book 2
objects; the records only package the choices which are genuinely made in the
chapter, namely a normalized uniformizer and an ambient separable/algebraic
closure for finite subextensions.
-/

universe u v

/-- The local-field data fixed throughout the chapter. -/
structure Chapter06LocalFieldData (K : Type*) [Field K] where
  valuation : AddValuation K (WithTop ℤ)
  complete :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01CompleteAdditiveValuation
      valuation
  [residue_finite : Finite
    (IsLocalRing.ResidueField valuation.toValuation.valuationSubring)]
  uniformizer : valuation.toValuation.valuationSubring
  uniformizer_spec :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01IsUniformizer
      valuation.toValuation uniformizer

/-- The valuation ring and residue field attached to `D`. -/
abbrev Chapter06ValuationRing {K : Type*} [Field K]
    (D : Chapter06LocalFieldData K) : ValuationSubring K :=
  D.valuation.toValuation.valuationSubring

abbrev Chapter06ResidueField {K : Type*} [Field K]
    (D : Chapter06LocalFieldData K) : Type _ :=
  IsLocalRing.ResidueField (Chapter06ValuationRing D)

/-- The canonical field-unit filtration imported from Book 2, Chapter 2. -/
abbrev Chapter06UnitFiltration {K : Type*} [Field K]
    (D : Chapter06LocalFieldData K) (n : ℕ) : Subgroup Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter02.chapter02FieldUnitFiltration
    D.valuation n

noncomputable def chapter06ValuationRingUnitSubgroup
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) : Subgroup Kˣ :=
  (⊤ : Subgroup (Chapter06ValuationRing D)ˣ).map
    (Units.map (Chapter06ValuationRing D).subtype.toMonoidHom)

theorem chapter06_unit_filtration_zero_eq_valuationRingUnits
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) :
    Chapter06UnitFiltration D 0 = chapter06ValuationRingUnitSubgroup D := by
  sorry

def Chapter06UnitFiltrationNeighborhoodBasis
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    [TopologicalSpace Kˣ] : Prop :=
  LastLib.Book05LocalClassFieldTheory.Chapter02.Chapter02FieldUnitFiltrationNeighborhoodBasis
    D.valuation

theorem chapter06_uniformizer_ne_zero
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) :
    (D.uniformizer : K) ≠ 0 := by
  intro h
  apply D.uniformizer_spec.1
  exact Subtype.ext h

/-- The chosen uniformizer viewed as a unit of the field. -/
noncomputable def chapter06UniformizerUnit
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) : Kˣ :=
  Units.mk0 (D.uniformizer : K) (chapter06_uniformizer_ne_zero D)

@[simp]
theorem chapter06UniformizerUnit_coe
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) :
    (chapter06UniformizerUnit D : K) = D.uniformizer := rfl

/-- The residue cardinality denoted by `q` in the source. -/
noncomputable def chapter06ResidueCardinality
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) : ℕ :=
  Nat.card (Chapter06ResidueField D)

theorem chapter06_residue_cardinality_pos
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) :
    0 < chapter06ResidueCardinality D := by
  sorry

/-- Positive indices used for the precision family. -/
abbrev Chapter06PositiveNat := {n : ℕ // 0 < n}

/-- The subgroup `π^(mℤ) U^n` used in the existence construction. -/
def chapter06PrecisionSubgroup
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) : Subgroup Kˣ :=
  Subgroup.zpowers ((chapter06UniformizerUnit D) ^ m) ⊔
    Chapter06UnitFiltration D n

theorem chapter06_mem_precisionSubgroup_iff
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (m n : ℕ) (x : Kˣ) :
    x ∈ chapter06PrecisionSubgroup D m n ↔
      ∃ z : ℤ, ∃ u : Kˣ,
        u ∈ Chapter06UnitFiltration D n ∧
          x = (chapter06UniformizerUnit D) ^ (m * z) * u := by
  sorry

/-- The precision subgroups are a neighborhood basis at the identity. -/
def Chapter06PrecisionCofinality
    {K : Type*} [Field K]
    (D : Chapter06LocalFieldData K)
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    (_htop : Chapter06UnitFiltrationNeighborhoodBasis D) : Prop :=
  ∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex →
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ chapter06PrecisionSubgroup D m n ≤ H

/-- The multiplicative norm subgroup, in the units presentation used by Book 5. -/
abbrev chapter06NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K L

theorem chapter06_mem_normSubgroup_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Kˣ) :
    x ∈ chapter06NormSubgroup K L ↔
      ∃ y : Lˣ,
        LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormMap K L y = x := by
  exact LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_mem_normSubgroup_iff K L x

/-- A finite abelian extension, kept as a local typeclass for norm-index APIs. -/
class Chapter06FiniteAbelianExtension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] : Prop where
  galois_commutative : ∀ σ τ : Gal(L / K), σ * τ = τ * σ

instance chapter06FiniteAbelianExtension.commGroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Chapter06FiniteAbelianExtension K L] : CommGroup (Gal(L / K)) :=
  { (inferInstance : Group (Gal(L / K))) with
    mul_comm := Chapter06FiniteAbelianExtension.galois_commutative }

/-- A finite Artin map with exactly the kernel and surjectivity interfaces used
by the fixed-field construction. -/
structure Chapter06FiniteArtinMap
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L] where
  reciprocity : Kˣ →* Gal(L / K)
  kernel_eq_norm : reciprocity.ker = chapter06NormSubgroup K L
  surjective : Function.Surjective reciprocity

theorem chapter06_finite_artin_map_kernel
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) :
    A.reciprocity.ker = chapter06NormSubgroup K L :=
  A.kernel_eq_norm

theorem chapter06_finite_artin_map_surjective
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    [Chapter06FiniteAbelianExtension K L]
    (A : Chapter06FiniteArtinMap K L) :
    Function.Surjective A.reciprocity :=
  A.surjective

/-- A finite abelian subextension inside a chosen ambient abelian closure. -/
structure Chapter06FiniteAbelianSubextension
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb] where
  field : IntermediateField K KAb
  [finite : FiniteDimensional K field]
  [galois : IsGalois K field]
  [galois_group_finite : Fintype (Gal(field / K))]
  abelian : ∀ σ τ : Gal(field / K), σ * τ = τ * σ

instance chapter06FiniteAbelianSubextension.isAbelian
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (L : Chapter06FiniteAbelianSubextension K KAb) :
    @Chapter06FiniteAbelianExtension K L.field
      (inferInstance : Field K) (IntermediateField.toField L.field)
      (IntermediateField.algebra' L.field) L.finite L.galois := by
  sorry

noncomputable def Chapter06FiniteAbelianSubextension.normSubgroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (L : Chapter06FiniteAbelianSubextension K KAb) : Subgroup Kˣ := by
  letI : FiniteDimensional K L.field := L.finite
  exact chapter06NormSubgroup K L.field

noncomputable def Chapter06FiniteAbelianSubextension.degree
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (L : Chapter06FiniteAbelianSubextension K KAb) : ℕ := by
  letI : FiniteDimensional K L.field := L.finite
  exact Module.finrank K L.field

@[simp]
theorem chapter06FiniteAbelianSubextension_normSubgroup_coe
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    (L : Chapter06FiniteAbelianSubextension K KAb) :
    L.normSubgroup =
      @chapter06NormSubgroup K L.field _ _ _ L.finite := by
  rfl

/-- Maximality of the selected model of `K^ab`. -/
def Chapter06IsMaximalAbelianExtension
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb] : Prop :=
  ∀ (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [Chapter06FiniteAbelianExtension K L],
    Nonempty (L →ₐ[K] KAb)

/-- A valued finite extension used when stating convergence and ramification
properties.  The valuation is kept explicit because Mathlib does not yet
bundle the normalized local-field valuation and its residue degree. -/
structure Chapter06ValuedFiniteExtension
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K)
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] where
  valuation : AddValuation L (WithTop ℤ)
  complete :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01CompleteAdditiveValuation
      valuation
  extension :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationExtension
      D.valuation valuation

def Chapter06UnramifiedValuedExtension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (D : Chapter06LocalFieldData K)
    (V : Chapter06ValuedFiniteExtension D L) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
    D.valuation V.valuation

/-- A chosen finite unramified level of degree `m`. -/
structure Chapter06UnramifiedExtension
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ) where
  carrier : Type*
  [carrier_field : Field carrier]
  [carrier_algebra : Algebra K carrier]
  [carrier_finite : FiniteDimensional K carrier]
  [carrier_galois : IsGalois K carrier]
  [carrier_fintype : Fintype (Gal(carrier / K))]
  valued : Chapter06ValuedFiniteExtension D carrier
  degree_eq : Module.finrank K carrier = m
  unramified : Chapter06UnramifiedValuedExtension D valued

instance Chapter06UnramifiedExtension.finiteAbelian
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (E : Chapter06UnramifiedExtension D m) :
    @Chapter06FiniteAbelianExtension K E.carrier
      (inferInstance : Field K) E.carrier_field E.carrier_algebra
        E.carrier_finite E.carrier_galois := by
  sorry

noncomputable def chapter06UnramifiedNormSubgroup
    {K : Type*} [Field K] (D : Chapter06LocalFieldData K) (m : ℕ)
    (E : Chapter06UnramifiedExtension D m) : Subgroup Kˣ := by
  letI : Field E.carrier := E.carrier_field
  letI : Algebra K E.carrier := E.carrier_algebra
  letI : FiniteDimensional K E.carrier := E.carrier_finite
  exact chapter06NormSubgroup K E.carrier

/-- A compositum package records the embeddings and the fact that the chosen
field is generated by them. -/
structure Chapter06CompositumData
    (K L₁ L₂ E : Type*) [Field K] [Field L₁] [Field L₂] [Field E]
    [Algebra K L₁] [Algebra K L₂] [Algebra K E]
    [Algebra L₁ E] [Algebra L₂ E]
    [IsScalarTower K L₁ E] [IsScalarTower K L₂ E]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [FiniteDimensional K E] where
  left_inclusion : L₁ →ₐ[K] E
  right_inclusion : L₂ →ₐ[K] E
  left_is_compositum :
    IntermediateField.adjoin K
      (Set.range (left_inclusion : L₁ → E) ∪ Set.range (right_inclusion : L₂ → E)) =
      ⊤

end

end LastLib.Book05LocalClassFieldTheory.Chapter06
