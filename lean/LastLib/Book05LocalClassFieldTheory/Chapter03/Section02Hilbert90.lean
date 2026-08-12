import LastLib.Book05LocalClassFieldTheory.Chapter03.Core
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

namespace LastLib.Book05LocalClassFieldTheory.Chapter03

noncomputable section

open scoped BigOperators

/-! ## 3.2. Hilbert's Theorem 90 with proof -/

/-- The twisted partial product `x_i = x σ(x) ⋯ σ^(i-1)(x)`. -/
def chapter03Hilbert90PartialProduct
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (i : ℕ) : Lˣ :=
  ∏ j ∈ Finset.range i,
    Units.map ((σ ^ j).toRingEquiv.toMonoidHom) x

theorem chapter03_hilbert90_partial_product_zero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) :
    chapter03Hilbert90PartialProduct K L σ x 0 = 1 := by
  simp [chapter03Hilbert90PartialProduct]

theorem chapter03_hilbert90_partial_product_succ
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (i : ℕ) :
    chapter03Hilbert90PartialProduct K L σ x (i + 1) =
      chapter03Hilbert90PartialProduct K L σ x i *
        Units.map ((σ ^ i).toRingEquiv.toMonoidHom) x := by
  sorry

/-- The twisted averaging operator `a ↦ ∑ x_i σ^i(a)`. -/
def chapter03Hilbert90Averaging
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (n : ℕ) (a : L) : L :=
  ∑ i ∈ Finset.range n,
    (chapter03Hilbert90PartialProduct K L σ x i : L) * (σ ^ i) a

theorem chapter03_hilbert90_averaging_zero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (n : ℕ) :
    chapter03Hilbert90Averaging K L σ x n 0 =
      ∑ i ∈ Finset.range n, (chapter03Hilbert90PartialProduct K L σ x i : L) * 0 := by
  simp [chapter03Hilbert90Averaging]

theorem chapter03_hilbert90_partial_product_coe
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (σ : Gal(L/K)) (x : Lˣ) (i : ℕ) :
    (chapter03Hilbert90PartialProduct K L σ x i : L) =
      ∏ j ∈ Finset.range i, (σ ^ j) (x : L) := by
  sorry

theorem chapter03_hilbert90_partial_product_norm_wrap
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) (x : Lˣ)
    (hx : chapter03NormUnit K L x = 1) :
    chapter03Hilbert90PartialProduct K L σ x n = 1 := by
  sorry

/-- Dedekind independence supplies a nonzero value of the averaging operator. -/
theorem chapter03_hilbert90_averaging_exists_nonzero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) (x : Lˣ)
    (hx : chapter03NormUnit K L x = 1) :
    ∃ a : L, chapter03Hilbert90Averaging K L σ x n a ≠ 0 := by
  sorry

/-- The index shift in the Hilbert 90 averaging argument. -/
theorem chapter03_hilbert90_averaging_shift
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) (x : Lˣ)
    (hx : chapter03NormUnit K L x = 1) (a : L)
    (ha : chapter03Hilbert90Averaging K L σ x n a ≠ 0) :
    (x : L) * σ (chapter03Hilbert90Averaging K L σ x n a) =
      chapter03Hilbert90Averaging K L σ x n a := by
  sorry

/-- Hilbert 90 in the book's unit-valued convention. -/
theorem chapter03_hilbert90
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) (x : Lˣ) :
    chapter03NormUnit K L x = 1 ↔
      ∃ y : Lˣ, x = chapter03DifferenceUnit K L σ y := by
  sorry

/-- The kernel/image form of Hilbert 90, matching the displayed set equality. -/
theorem chapter03_hilbert90_kernel_eq_difference_range
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (σ : Gal(L/K))
    (hcyc : chapter03CyclicExtension K L n σ) :
    {x : Lˣ | chapter03NormUnit K L x = 1} =
      Set.range (chapter03DifferenceUnit K L σ) := by
  ext x
  constructor
  · intro hx
    rcases (chapter03_hilbert90 K L n σ hcyc x).mp hx with ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩
    exact (chapter03_hilbert90 K L n σ hcyc x).mpr ⟨y, hy.symm⟩

/- This is deliberately a separate predicate: Hilbert 90 identifies the norm kernel, whereas norm
   surjectivity concerns the image and is an additional local-field calculation. -/
def chapter03NormSurjectivity
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Prop :=
  ∀ u : Kˣ, ∃ x : Lˣ, chapter03NormUnit K L x = u

/-- Mathlib's canonical generator-oriented formulation, with the opposite quotient convention. -/
theorem chapter03_hilbert90_via_mathlib
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)] (σ : Gal(L/K))
    (hσ : ∀ τ : Gal(L/K), τ ∈ Subgroup.zpowers σ)
    {x : L} (hx : Algebra.norm K x = 1) :
    ∃ y : Lˣ, y / σ y = x := by
  sorry

/-- The group-cohomological vanishing supplied by Mathlib's Hilbert 90 API. -/
abbrev chapter03Hilbert90H1
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :=
  groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)

instance chapter03_hilbert90_h1_unique
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Unique (chapter03Hilbert90H1 K L) := by
  infer_instance

theorem chapter03_hilbert90_h1_subsingleton
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Subsingleton (chapter03Hilbert90H1 K L) := by
  infer_instance

end

end LastLib.Book05LocalClassFieldTheory.Chapter03
