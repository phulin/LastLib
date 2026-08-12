import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section08NormsAndDeterminants
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.Section01FromEmbeddingsToLocalSymmetries
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section07ExplicitUnramifiedNormEquations
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter03

noncomputable section

open scoped BigOperators TensorProduct

/-! ## Shared interfaces for Chapter 3

The preceding local-field chapters provide the valuation and norm interfaces used below.
The definitions in this file keep the cyclic-extension data explicit: in particular, a chosen
generator is part of the data whenever a formula depends on it.
-/

/-- The book's phrase `G = ⟨σ⟩`, written using the canonical Galois group. -/
def chapter03CyclicGeneratorCondition
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) : Prop :=
  ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ

/-- A finite cyclic extension together with its degree and a chosen generator. -/
def chapter03CyclicExtension
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K)) : Prop :=
  Module.finrank K L = n ∧ chapter03CyclicGeneratorCondition K L σ

theorem chapter03_cyclic_extension_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K)) :
    chapter03CyclicExtension K L n σ ↔
      Module.finrank K L = n ∧ ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ := Iff.rfl

theorem chapter03_cyclic_extension_degree
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    Module.finrank K L = n :=
  hcyc.1

theorem chapter03_cyclic_extension_generator
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ :=
  hcyc.2

theorem chapter03_exists_cyclic_generator
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)] :
    ∃ σ : Gal(L/K), ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ := by
  sorry

theorem chapter03_cyclic_generator_exists_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (∃ σ : Gal(L/K), chapter03CyclicGeneratorCondition K L σ) ↔
      IsCyclic Gal(L/K) := by
  sorry

theorem chapter03_cyclic_extension_iff_degree_and_isCyclic
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) :
    (∃ σ : Gal(L/K), chapter03CyclicExtension K L n σ) ↔
      Module.finrank K L = n ∧ IsCyclic Gal(L/K) := by
  sorry

/-- The difference operator `D = σ - 1` in the integral group ring. -/
def chapter03GroupRingDifference {G : Type*} [Group G] (σ : G) : MonoidAlgebra ℤ G :=
  MonoidAlgebra.single σ 1 - MonoidAlgebra.single 1 1

/-- The cyclic norm operator `N_G = 1 + σ + ⋯ + σ^(n-1)`. -/
def chapter03GroupRingNorm {G : Type*} [Group G] (σ : G) (n : ℕ) : MonoidAlgebra ℤ G :=
  ∑ i ∈ Finset.range n, MonoidAlgebra.single (σ ^ i) 1

theorem chapter03_group_ring_difference_mul_norm_eq_zero
    {G : Type*} [Group G] (σ : G) (n : ℕ) (hσ : σ ^ n = 1) :
    chapter03GroupRingDifference σ * chapter03GroupRingNorm σ n = 0 := by
  sorry

theorem chapter03_group_ring_norm_mul_difference_eq_zero
    {G : Type*} [Group G] (σ : G) (n : ℕ) (hσ : σ ^ n = 1) :
    chapter03GroupRingNorm σ n * chapter03GroupRingDifference σ = 0 := by
  sorry

theorem chapter03_group_ring_operators_compose_zero
    {G : Type*} [Group G] (σ : G) (n : ℕ) (hσ : σ ^ n = 1) :
    chapter03GroupRingDifference σ * chapter03GroupRingNorm σ n = 0 ∧
      chapter03GroupRingNorm σ n * chapter03GroupRingDifference σ = 0 := by
  exact ⟨chapter03_group_ring_difference_mul_norm_eq_zero σ n hσ,
    chapter03_group_ring_norm_mul_difference_eq_zero σ n hσ⟩

/-- The multiplicative action of `D` on `Lˣ`, namely `y ↦ σ(y) / y`. -/
def chapter03DifferenceUnit
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (y : Lˣ) : Lˣ :=
  Units.map σ.toRingEquiv.toMonoidHom y / y

/-- The field norm on units, viewed as the multiplicative action of `N_G`. -/
def chapter03NormUnit
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K (S := L))

theorem chapter03_difference_unit_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (y : Lˣ) :
    (chapter03DifferenceUnit K L σ y : L) = σ (y : L) / (y : L) := by
  simp [chapter03DifferenceUnit]

theorem chapter03_norm_unit_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : Lˣ) :
    (chapter03NormUnit K L x : K) = Algebra.norm K (x : L) := by
  rfl

/-- The subgroup `N_{L/K}(Lˣ)` in the base multiplicative group. -/
abbrev chapter03NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormSubgroup K L

/-- The multiplicative norm quotient used for the cyclic Tate and Brauer formulas. -/
abbrev chapter03NormQuotient
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Type _ :=
  Kˣ ⧸ chapter03NormSubgroup K L

/-- The norm image in the base field, with the nonzero source represented by units. -/
def chapter03NormImage
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Set K :=
  {a | ∃ x : Lˣ, (chapter03NormUnit K L x : K) = a}

theorem chapter03_mem_norm_subgroup_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (u : Kˣ) :
    u ∈ chapter03NormSubgroup K L ↔
      ∃ x : Lˣ, chapter03NormUnit K L x = u := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_mem_norm_subgroup_iff
    K L u

theorem chapter03_norm_image_mem_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : K) :
    a ∈ chapter03NormImage K L ↔
      ∃ x : Lˣ, (chapter03NormUnit K L x : K) = a := Iff.rfl

/- The unit-group presentation is equivalent to the field-level norm equation with its nonzero
   source made explicit. -/
theorem chapter03_field_norm_image_mem_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (a : K) :
    a ∈ chapter03NormImage K L ↔
      ∃ x : L, x ≠ 0 ∧ Algebra.norm K x = a := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter03
