import LastLib.Book04AdelesAndIdeles.Chapter05.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter04.Section03NeighborhoodsAsLocalSpecifications

namespace LastLib.Book04AdelesAndIdeles.Chapter05

open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04

noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

/-! ## 5.5. Weak approximation at arbitrary places -/

def chapter05SelectedFinitePlaces
    (K : Type*) [Field K] [NumberField K]
  (T : Finset (Chapter04Place K)) : Finset (Chapter04FinitePlace K) := by
  classical
  exact T.toLeft

def chapter05SelectedArchimedeanPlaces
    (K : Type*) [Field K] [NumberField K]
  (T : Finset (Chapter04Place K)) : Finset (Chapter04InfinitePlace K) := by
  classical
  exact T.toRight

def chapter05FiniteCorrectionSet
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K))
    (m : ∀ _v : S, ℤ) : Set K :=
  chapter05FiniteDiagonal K ⁻¹'
    chapter04FinitePrecisionNeighborhood K S m

theorem chapter05_finite_correction_set_is_fractional_ideal
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (m : ∀ v : S, ℤ) :
    ∃ I : FractionalIdeal (𝓞 K)⁰ K,
      I ≠ 0 ∧ chapter05FiniteCorrectionSet K S m = (I : Set K) := by
  sorry

/-! An auxiliary rational prime is characterized canonically by vanishing
finite-place order at each selected prime. -/

def chapter05AuxiliaryPrimeAvoids
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (ell : ℕ) : Prop :=
  Nat.Prime ell ∧
    ∀ v : S,
      LastLib.Book04AdelesAndIdeles.Chapter01.chapter01Order v.1
        (ell : K) = 0

theorem chapter05_exists_auxiliary_prime
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) :
    ∃ ell : ℕ, chapter05AuxiliaryPrimeAvoids K S ell := by
  sorry

def chapter05ScaledCorrectionSet
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (m : ∀ _v : S, ℤ)
    (ell s : ℕ) : Set K :=
  {c |
    ∃ d : K, d ∈ chapter05FiniteCorrectionSet K S m ∧
      c = ((ell : K)⁻¹) ^ s * d}

theorem chapter05_scaled_correction_preserves_finite_precision
    (K : Type*) [Field K] [NumberField K]
    (S : Finset (Chapter04FinitePlace K)) (m : ∀ v : S, ℤ)
    (ell s : ℕ) (hℓ : chapter05AuxiliaryPrimeAvoids K S ell)
    {c : K} (hc : c ∈ chapter05ScaledCorrectionSet K S m ell s) :
    ∀ v : S,
      chapter05FiniteDiagonal K c v.1 ∈
        LastLib.Book04AdelesAndIdeles.Chapter01.chapter01LocalNeighborhood
          v.1 (m v) := by
  sorry

/-! The correction lattice is now the canonical mixed-space image of a
fractional ideal; its mesh statement is the scaled-lattice statement from the
source proof. -/

theorem chapter05_correction_lattice_mesh
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) (ell : ℕ) (hℓ : 1 < ell)
    (x : chapter01MinkowskiSpace K)
    (U : Set (chapter01MinkowskiSpace K)) (hU : U ∈ 𝓝 x) :
    ∀ᶠ s : ℕ in Filter.atTop,
      ∃ c : K,
        c ∈ chapter05ScaledFractionalIdeal K I ell s ∧
          chapter01MinkowskiEmbedding K c ∈ U := by
  sorry

theorem chapter05_place_system_lattice_mesh
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) (ell : ℕ) (hℓ : 1 < ell) :
    chapter05MinkowskiLatticeMesh K I ell := by
  sorry

/-!
**Theorem 5.3 (weak approximation).** For every finite list of distinct
canonical places, the diagonal map has dense image in the selected local
product.
-/
theorem chapter05_theorem_5_3_weak_approximation
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    chapter05WeakApproximationStatement K T := by
  sorry

theorem chapter05_theorem_5_3_weak_approximation_dense
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    DenseRange (chapter05DiagonalAtPlaces K T) := by
  sorry

theorem chapter05_weak_approximation_iff_dense_selected_diagonal
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    chapter05WeakApproximationStatement K T ↔
      DenseRange (chapter05DiagonalAtPlaces K T) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter05
