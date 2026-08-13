import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Separation.Hausdorff
import LastLib.Book04AdelesAndIdeles.Chapter04.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter05

noncomputable section

open Filter Set
open NumberField IsDedekindDomain
open scoped BigOperators Pointwise Topology RestrictedProduct

universe u v w

/-!
Shared canonical interfaces for Chapter 5.

The carriers in this chapter are the pinned number-field and adelic carriers
from Chapters 1--4.  In particular, finite places are height-one primes of
`𝓞 K`, the Minkowski space is Mathlib's mixed space, and the finite and full
adele rings are the canonical restricted product and product carriers.
-/

abbrev Chapter05RingOfIntegers (K : Type*) [Field K] [NumberField K] :=
  𝓞 K

abbrev Chapter05FinitePlace (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04FinitePlace K

abbrev Chapter05InfinitePlace (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04InfinitePlace K

abbrev Chapter05Place (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04Place K

abbrev Chapter05FiniteLocalField
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter05FinitePlace K) : Type _ :=
  LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04FiniteLocalField K v

abbrev Chapter05FiniteLocalIntegerRing
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter05FinitePlace K) : Type _ :=
  LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04FiniteLocalIntegerRing K v

abbrev Chapter05LocalField
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter05Place K) : Type _ :=
  LastLib.Book04AdelesAndIdeles.Chapter04.chapter04LocalField K v

abbrev Chapter05LocalIntegralSubring
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter05Place K) : Subring (Chapter05LocalField K v) :=
  LastLib.Book04AdelesAndIdeles.Chapter04.chapter04LocalIntegralSubring K v

def chapter05LocalEmbedding
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter05Place K) : K →+* Chapter05LocalField K v :=
  match v with
  | Sum.inl w => NumberField.FinitePlace.embedding w
  | Sum.inr w => algebraMap K w.Completion

abbrev Chapter05FiniteAdeleRing (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04FiniteAdeleRing K

abbrev Chapter05InfiniteAdeleRing (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04InfiniteAdeleRing K

abbrev Chapter05AdeleRing (K : Type*) [Field K] [NumberField K] :=
  LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04AdeleRing K

abbrev Chapter05MinkowskiSpace (K : Type*) [Field K] [NumberField K] :=
  NumberField.mixedEmbedding.mixedSpace K

abbrev Chapter05IntegerLattice (K : Type*) [Field K] [NumberField K] :=
  NumberField.mixedEmbedding.integerLattice K

abbrev Chapter05FractionalIdealGroup (K : Type*) [Field K] [NumberField K] :=
  (FractionalIdeal (𝓞 K)⁰ K)ˣ

def chapter05FiniteDiagonal (K : Type*) [Field K] [NumberField K] :
    K →+* Chapter05FiniteAdeleRing K :=
  IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K

def chapter05InfiniteDiagonal (K : Type*) [Field K] [NumberField K] :
    K →+* Chapter05InfiniteAdeleRing K :=
  algebraMap K (Chapter05InfiniteAdeleRing K)

def chapter05Diagonal (K : Type*) [Field K] [NumberField K] :
    K →+* Chapter05AdeleRing K :=
  algebraMap K (Chapter05AdeleRing K)

def chapter05MinkowskiEmbedding (K : Type*) [Field K] [NumberField K] :
    K →+* Chapter05MinkowskiSpace K :=
  NumberField.mixedEmbedding K

abbrev chapter05FiniteIntegralAdeleSubring
    (K : Type*) [Field K] [NumberField K] :
    Subring (Chapter05FiniteAdeleRing K) :=
  LastLib.Book04AdelesAndIdeles.Chapter04.Chapter04FiniteIntegralAdeleSubring K

def chapter05InfinitePlaces (K : Type*) [Field K] [NumberField K] :
    Set (Chapter05Place K) :=
  Set.range Sum.inr

/-! The full adele carrier uses the product of infinite completions, whereas
the Minkowski lattice uses the mixed real/complex space.  The map below is
Mathlib's canonical ring equivalence between these two carriers. -/

def chapter05FullZeroNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (Uinf : Set (Chapter05MinkowskiSpace K)) : Set (Chapter05AdeleRing K) :=
  ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm '' Uinf) ×ˢ
    (chapter05FiniteIntegralAdeleSubring K : Set (Chapter05FiniteAdeleRing K))

def chapter05FiniteZeroNeighborhood
    (K : Type*) [Field K] [NumberField K] : Set (Chapter05FiniteAdeleRing K) :=
  chapter05FiniteIntegralAdeleSubring K

def chapter05FinsetSubtypeCoe
    {X : Type u} {s : Set X} (S : Finset {x // x ∈ s}) : Set X :=
  {x | ∃ hx : x ∈ s, (⟨x, hx⟩ : {x // x ∈ s}) ∈ S}

/-! The canonical Minkowski image of a nonzero fractional ideal is the
    correction lattice used in the weak-approximation argument. -/

abbrev chapter05MinkowskiCorrectionLattice
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter05FractionalIdealGroup K) :
    Submodule ℤ (Chapter05MinkowskiSpace K) :=
  NumberField.mixedEmbedding.idealLattice K I

theorem chapter05_minkowski_correction_lattice_mem_iff
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter05FractionalIdealGroup K)
    {x : Chapter05MinkowskiSpace K} :
    x ∈ chapter05MinkowskiCorrectionLattice K I ↔
      ∃ a : K, a ∈ (I : Set K) ∧ NumberField.mixedEmbedding K a = x := by
  sorry

theorem chapter05_minkowski_correction_lattice_is_discrete_and_full
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter05FractionalIdealGroup K) :
    DiscreteTopology (chapter05MinkowskiCorrectionLattice K I) ∧
      IsZLattice ℝ (chapter05MinkowskiCorrectionLattice K I) := by
  sorry

theorem chapter05_minkowski_correction_lattice_has_fundamental_domain
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter05FractionalIdealGroup K) :
    MeasureTheory.IsAddFundamentalDomain
      (chapter05MinkowskiCorrectionLattice K I)
      (ZSpan.fundamentalDomain
        (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I)) := by
  sorry

def chapter05ScaledFractionalIdeal
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter05FractionalIdealGroup K) (ell s : ℕ) : Set K :=
  {c | ∃ d : K, d ∈ (I : Set K) ∧
    c = ((ell : K)⁻¹) ^ s * d}

def chapter05MinkowskiLatticeMesh (K : Type*) [Field K] [NumberField K]
    (I : Chapter05FractionalIdealGroup K) (ell : ℕ) : Prop :=
  1 < ell →
    ∀ (x : Chapter05MinkowskiSpace K) (U : Set (Chapter05MinkowskiSpace K)),
      U ∈ 𝓝 x →
        ∃ s : ℕ, ∃ c : K,
          c ∈ chapter05ScaledFractionalIdeal K I ell s ∧
            NumberField.mixedEmbedding K c ∈ U

theorem chapter05_minkowski_correction_lattice_mesh
    (K : Type*) [Field K] [NumberField K]
    (I : Chapter05FractionalIdealGroup K) (ell : ℕ) (hℓ : 1 < ell) :
    chapter05MinkowskiLatticeMesh K I ell := by
  sorry

def chapter05NondiscreteAtZero
    {G : Type u} [Zero G] [TopologicalSpace G] : Prop :=
  ({0} : Set G) ∉ 𝓝 (0 : G)

/-! Canonical local-product interfaces used by Sections 5.5--5.6. -/

abbrev Chapter05AdeleAwayFrom
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05Place K)) :=
  Πʳ v : {v // v ∉ S},
    [Chapter05LocalField K v.1, Chapter05LocalIntegralSubring K v.1]_[Filter.cofinite]

def chapter05AwayDiagonal
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05Place K))
    (hS : chapter05InfinitePlaces K ⊆ S) :
  K → Chapter05AdeleAwayFrom K S := fun a =>
  ⟨fun v => chapter05LocalEmbedding K v.1 a, by
    sorry⟩

@[simp]
theorem chapter05_awayDiagonal_coordinate
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05Place K))
    (hS : chapter05InfinitePlaces K ⊆ S) (a : K)
    (v : {v // v ∉ S}) :
    (chapter05AwayDiagonal K S hS a) v =
      chapter05LocalEmbedding K v.1 a := by
  sorry

def chapter05FiniteToAwayProjection
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05Place K))
    (hfinite : ∀ v, v ∉ S → ∃ w : Chapter05FinitePlace K,
      v = Sum.inl w)
    (x : Chapter05FiniteAdeleRing K) : Chapter05AdeleAwayFrom K S :=
  ⟨fun v => match h : v.1 with
    | Sum.inl w => x w
    | Sum.inr _ => 0, by
      sorry⟩

def chapter05AwayBasicNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05Place K))
    (x : Chapter05AdeleAwayFrom K S)
    (T : Finset {v // v ∉ S})
    (W : ∀ v : T, Set (Chapter05LocalField K v.1)) :
    Set (Chapter05AdeleAwayFrom K S) :=
  {y |
    (∀ v : T, y v - x v ∈ W v) ∧
      (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
        y v - x v ∈ (Chapter05LocalIntegralSubring K v.1 :
          Set (Chapter05LocalField K v.1)))}

@[simp]
theorem chapter05_mem_awayBasicNeighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05Place K))
    (x y : Chapter05AdeleAwayFrom K S)
    (T : Finset {v // v ∉ S})
    (W : ∀ v : T, Set (Chapter05LocalField K v.1)) :
    y ∈ chapter05AwayBasicNeighborhood K S x T W ↔
      ((∀ v : T, y v - x v ∈ W v) ∧
        (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
          y v - x v ∈ (Chapter05LocalIntegralSubring K v.1 :
            Set (Chapter05LocalField K v.1)))) := by
  sorry

def chapter05RestrictedProductBasis
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05Place K)) : Prop :=
  ∀ (x : Chapter05AdeleAwayFrom K S)
    (U : Set (Chapter05AdeleAwayFrom K S)), U ∈ 𝓝 x →
      ∃ (T : Finset {v // v ∉ S})
        (W : ∀ v : T, Set (Chapter05LocalField K v.1)),
        (∀ v : T, W v ∈ 𝓝 (0 : Chapter05LocalField K v.1)) ∧
          chapter05AwayBasicNeighborhood K S x T W ⊆ U

def chapter05WeakApproximationStatement
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter05Place K)) : Prop :=
  ∀ (x : ∀ v : T, Chapter05LocalField K v.1)
    (W : ∀ v : T, Set (Chapter05LocalField K v.1)),
    (∀ v : T, W v ∈ 𝓝 (x v)) →
      ∃ a : K, ∀ v : T,
        chapter05LocalEmbedding K v.1 a ∈ W v

def chapter05DiagonalAtPlaces
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter05Place K)) :
    K → (∀ v : T, Chapter05LocalField K v.1) :=
  fun a v => chapter05LocalEmbedding K v.1 a

def chapter05StrongApproximationAwayFrom
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter05Place K)) : Prop :=
  ∀ (T : Finset {v // v ∉ S})
    (x : ∀ v : T, Chapter05LocalField K v.1)
    (W : ∀ v : T, Set (Chapter05LocalField K v.1)),
    (∀ v : T, W v ∈ 𝓝 (0 : Chapter05LocalField K v.1)) →
      ∃ a : K,
        (∀ v : T,
          chapter05LocalEmbedding K v.1 a - x v ∈ W v) ∧
        (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
          chapter05LocalEmbedding K v.1 a ∈
            (Chapter05LocalIntegralSubring K v.1 :
              Set (Chapter05LocalField K v.1)))

end

end LastLib.Book04AdelesAndIdeles.Chapter05
