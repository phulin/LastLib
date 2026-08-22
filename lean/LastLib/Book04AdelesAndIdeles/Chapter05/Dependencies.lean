import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Normed.Group.Constructions
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
open LastLib.Book04AdelesAndIdeles.Chapter01
open LastLib.Book04AdelesAndIdeles.Chapter04
open scoped BigOperators Pointwise Topology RestrictedProduct nonZeroDivisors

universe u v w

/-!
Shared canonical interfaces for Chapter 5.

The carriers in this chapter are the pinned number-field and adelic carriers
from Chapters 1--4.  In particular, finite places are height-one primes of
`𝓞 K`, the Minkowski space is Mathlib's mixed space, and the finite and full
adele rings are the canonical restricted product and product carriers.
-/

def chapter05RingOfIntegersSet
    (K : Type*) [Field K] [NumberField K] : Set K :=
  Set.range (algebraMap (𝓞 K) K)

/-! These names are retained as compatibility interfaces for later Book 4
chapters; Chapter 5 itself uses the canonical Chapter 4 carriers directly. -/

abbrev Chapter05Place (K : Type*) [Field K] [NumberField K] :=
  Chapter04Place K

abbrev Chapter05LocalField
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter05Place K) : Type _ :=
  chapter04LocalField K v

abbrev Chapter05AdeleRing (K : Type*) [Field K] [NumberField K] :=
  Chapter04AdeleRing K

def chapter05LocalEmbedding
    (K : Type*) [Field K] [NumberField K]
    (v : Chapter04Place K) : K →+* chapter04LocalField K v :=
  match v with
  | Sum.inl w => NumberField.FinitePlace.embedding w
  | Sum.inr w => algebraMap K w.Completion

noncomputable instance chapter05InfiniteAdeleRingT2Space
    (K : Type*) [Field K] [NumberField K] :
    T2Space (Chapter04InfiniteAdeleRing K) := by
  change T2Space (∀ v : Chapter04InfinitePlace K, v.Completion)
  exact Pi.t2Space

noncomputable instance chapter05FiniteAdeleRingT2Space
    (K : Type*) [Field K] [NumberField K] :
    T2Space (Chapter04FiniteAdeleRing K) := by
  change T2Space
    (Πʳ v : Chapter04FinitePlace K,
      [Chapter04FiniteLocalField K v, chapter04FiniteLocalIntegerSet K v]_[Filter.cofinite])
  exact RestrictedProduct.instT2Space

noncomputable instance chapter05AdeleRingT2Space
    (K : Type*) [Field K] [NumberField K] :
    T2Space (Chapter04AdeleRing K) := by
  change T2Space (Chapter04InfiniteAdeleRing K × Chapter04FiniteAdeleRing K)
  exact Prod.t2Space

open scoped Classical in
noncomputable instance chapter05MinkowskiSpaceNormedAddCommGroup
    (K : Type*) [Field K] [NumberField K] :
    NormedAddCommGroup (chapter01MinkowskiSpace K) :=
  Prod.normedAddCommGroup

def chapter05FiniteDiagonal (K : Type*) [Field K] [NumberField K] :
    K →+* Chapter04FiniteAdeleRing K :=
  IsDedekindDomain.FiniteAdeleRing.algebraMap (𝓞 K) K

def chapter05InfiniteDiagonal (K : Type*) [Field K] [NumberField K] :
    K →+* Chapter04InfiniteAdeleRing K :=
  algebraMap K (Chapter04InfiniteAdeleRing K)

def chapter05Diagonal (K : Type*) [Field K] [NumberField K] :
    K →+* Chapter04AdeleRing K :=
  algebraMap K (Chapter04AdeleRing K)

def chapter05InfinitePlaces (K : Type*) [Field K] [NumberField K] :
    Set (Chapter04Place K) :=
  Set.range Sum.inr

/-! The full adele carrier uses the product of infinite completions, whereas
the Minkowski lattice uses the mixed real/complex space.  The map below is
Mathlib's canonical ring equivalence between these two carriers. -/

def chapter05FullZeroNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (Uinf : Set (chapter01MinkowskiSpace K)) : Set (Chapter04AdeleRing K) :=
  ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm '' Uinf) ×ˢ
    (Chapter04FiniteIntegralAdeleSubring K : Set (Chapter04FiniteAdeleRing K))

def chapter05FiniteZeroNeighborhood
    (K : Type*) [Field K] [NumberField K] : Set (Chapter04FiniteAdeleRing K) :=
  Chapter04FiniteIntegralAdeleSubring K

def chapter05FinsetSubtypeCoe
    {X : Type u} {s : Set X} (S : Finset {x // x ∈ s}) : Set X :=
  {x | ∃ hx : x ∈ s, (⟨x, hx⟩ : {x // x ∈ s}) ∈ S}

/-! The canonical Minkowski image of a nonzero fractional ideal is the
    correction lattice used in the weak-approximation argument. -/

theorem chapter05_minkowski_correction_lattice_mem_iff
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K)
    {x : chapter01MinkowskiSpace K} :
    x ∈ chapter01IdealLattice K I ↔
      ∃ a : K, a ∈ (I : Set K) ∧ NumberField.mixedEmbedding K a = x := by
  exact NumberField.mixedEmbedding.mem_idealLattice K I

theorem chapter05_minkowski_correction_lattice_is_discrete_and_full
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) :
    DiscreteTopology (chapter01IdealLattice K I) ∧
      IsZLattice ℝ (E := chapter01MinkowskiSpace K)
        (chapter01IdealLattice K I) := by
  exact ⟨inferInstance, inferInstance⟩

open scoped Classical in
theorem chapter05_minkowski_correction_lattice_has_fundamental_domain
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) :
    MeasureTheory.IsAddFundamentalDomain
      (chapter01IdealLattice K I)
      (ZSpan.fundamentalDomain
        (NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I)) := by
  exact NumberField.mixedEmbedding.fundamentalDomain_idealLattice K I

def chapter05ScaledFractionalIdeal
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) (ell s : ℕ) : Set K :=
  {c | ∃ d : K, d ∈ (I : Set K) ∧
    c = ((ell : K)⁻¹) ^ s * d}

def chapter05MinkowskiLatticeMesh (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) (ell : ℕ) : Prop :=
  1 < ell →
    ∀ (x : chapter01MinkowskiSpace K) (U : Set (chapter01MinkowskiSpace K)),
      U ∈ 𝓝 x →
        ∀ᶠ s : ℕ in atTop,
          ∃ c : K,
            c ∈ chapter05ScaledFractionalIdeal K I ell s ∧
              chapter01MinkowskiEmbedding K c ∈ U

theorem chapter05_minkowski_correction_lattice_mesh
    (K : Type*) [Field K] [NumberField K]
    (I : chapter01FractionalIdealGroup K) (ell : ℕ) (hℓ : 1 < ell) :
    chapter05MinkowskiLatticeMesh K I ell := by
  intro _ x U hU
  rcases Metric.mem_nhds_iff.1 hU with ⟨ε, hε, hεU⟩
  have hpos : (0 : ℝ) < ell := by
    exact_mod_cast Nat.zero_lt_of_lt hℓ
  let b := NumberField.mixedEmbedding.fractionalIdealLatticeBasis K I
  have hspan : Submodule.span ℤ (Set.range b) = chapter01IdealLattice K I := by
    dsimp [b]
    exact NumberField.mixedEmbedding.span_idealLatticeBasis K I
  rcases (isBounded_iff_forall_norm_le.1 (ZSpan.fundamentalDomain_isBounded b)) with ⟨C, hC⟩
  have hinv_lt : (ell : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one₀ hpos]
    exact_mod_cast hℓ
  have hscale : Tendsto (fun s : ℕ => ((ell : ℝ)⁻¹) ^ s * C) atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hpos.le) hinv_lt).mul_const C
  have hsmall : ∀ᶠ s : ℕ in atTop, ((ell : ℝ)⁻¹) ^ s * C < ε :=
    hscale.eventually (Iio_mem_nhds hε)
  have hscalar (s : ℕ) (d : K) :
      chapter01MinkowskiEmbedding K (((ell : K)⁻¹) ^ s * d) =
        ((ell : ℝ)⁻¹) ^ s • chapter01MinkowskiEmbedding K d := by
    rw [map_mul, map_pow]
    apply Prod.ext
    · funext w
      simp [Algebra.smul_def]
    · funext w
      simp [Algebra.smul_def]
  filter_upwards [hsmall] with s hs
  let q : ℝ := ((ell : ℝ)⁻¹) ^ s
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  obtain ⟨z, hz, _⟩ :=
    ZSpan.exist_unique_vadd_mem_fundamentalDomain b (-q⁻¹ • x)
  have hz' : (z : chapter01MinkowskiSpace K) + (-q⁻¹) • x ∈
      ZSpan.fundamentalDomain b := by
    simpa [Submodule.vadd_def, vadd_eq_add] using hz
  have hzmem : (z : chapter01MinkowskiSpace K) ∈ chapter01IdealLattice K I := by
    rw [← hspan]
    exact z.property
  obtain ⟨d, hdI, hdz⟩ := (chapter05_minkowski_correction_lattice_mem_iff K I).mp hzmem
  refine ⟨((ell : K)⁻¹) ^ s * d, ⟨d, hdI, rfl⟩, ?_⟩
  have hdiff : q • (z : chapter01MinkowskiSpace K) - x =
      q • ((z : chapter01MinkowskiSpace K) + (-q⁻¹) • x) := by
    rw [sub_eq_add_neg, smul_add, smul_smul]
    simp [hqpos.ne']
  have hclose : ‖q • (z : chapter01MinkowskiSpace K) - x‖ < ε := by
    calc
      ‖q • (z : chapter01MinkowskiSpace K) - x‖ =
          ‖q • ((z : chapter01MinkowskiSpace K) + (-q⁻¹) • x)‖ := by rw [hdiff]
      _ = |q| * ‖(z : chapter01MinkowskiSpace K) + (-q⁻¹) • x‖ := norm_smul q _
      _ = q * ‖(z : chapter01MinkowskiSpace K) + (-q⁻¹) • x‖ := by
        rw [abs_of_pos hqpos]
      _ ≤ q * C := mul_le_mul_of_nonneg_left (hC _ hz') hqpos.le
      _ < ε := by simpa [q] using hs
  rw [hscalar, hdz]
  apply hεU
  simpa [Metric.mem_ball, dist_eq_norm, q, inv_pow] using hclose

def chapter05NondiscreteAtZero
    {G : Type u} [Zero G] [TopologicalSpace G] : Prop :=
  ({0} : Set G) ∉ 𝓝 (0 : G)

/-! Canonical local-product interfaces used by Sections 5.5--5.6. -/

abbrev Chapter05AdeleAwayFrom
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) :=
  Πʳ v : {v // v ∉ S},
    [chapter04LocalField K v.1, chapter04LocalIntegralSubring K v.1]_[Filter.cofinite]

def chapter05AwayDiagonal
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hS : chapter05InfinitePlaces K ⊆ S) :
  K → Chapter05AdeleAwayFrom K S := fun a =>
  ⟨fun v => chapter05LocalEmbedding K v.1 a, by
    classical
    have hfinite : ∀ v : {v // v ∉ S}, ∃ w : Chapter04FinitePlace K,
        v.1 = Sum.inl w := by
      rintro ⟨v, hv⟩
      rcases v with w | w
      · exact ⟨w, rfl⟩
      · exfalso
        apply hv
        exact hS ⟨w, rfl⟩
    let f : {v // v ∉ S} → Chapter04FinitePlace K :=
      fun v => (hfinite v).choose
    have hf_spec : ∀ v : {v // v ∉ S}, v.1 = Sum.inl (f v) := by
      intro v
      exact (hfinite v).choose_spec
    have hf : Function.Injective f := by
      intro v₁ v₂ h
      apply Subtype.ext
      rw [hf_spec v₁, hf_spec v₂, h]
    have hfinite_integral : ∀ᶠ w : Chapter04FinitePlace K in Filter.cofinite,
        chapter05LocalEmbedding K (Sum.inl w) a ∈
          chapter04LocalIntegralSet K (Sum.inl w) := by
      change ∀ᶠ w : Chapter04FinitePlace K in Filter.cofinite,
        (↑a : Chapter04FiniteLocalField K w) ∈
          chapter04FiniteLocalIntegerSet K w
      exact chapter04_finiteAdele_mem_iff_eventually_integral K
        (chapter05FiniteDiagonal K a)
    have hpull : ∀ᶠ v : {v // v ∉ S} in Filter.cofinite,
        chapter05LocalEmbedding K v.1 a ∈
          chapter04LocalIntegralSet K v.1 := by
      have h' := hf.tendsto_cofinite hfinite_integral
      filter_upwards [h'] with v hv
      change chapter05LocalEmbedding K (Sum.inl (f v)) a ∈
        chapter04LocalIntegralSet K (Sum.inl (f v)) at hv
      rw [hf_spec v]
      exact hv
    exact hpull⟩

@[simp]
theorem chapter05_awayDiagonal_coordinate
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hS : chapter05InfinitePlaces K ⊆ S) (a : K)
    (v : {v // v ∉ S}) :
    (chapter05AwayDiagonal K S hS a) v =
      chapter05LocalEmbedding K v.1 a := by
  rfl

def chapter05FiniteCoordinate
    (K : Type*) [Field K] [NumberField K]
    (x : Chapter04FiniteAdeleRing K) (v : Chapter04Place K) :
    chapter04LocalField K v :=
  match v with
  | Sum.inl w => x w
  | Sum.inr _ => 0

def chapter05FiniteToAwayProjection
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (hfinite : ∀ v, v ∉ S → ∃ w : Chapter04FinitePlace K,
      v = Sum.inl w)
    (x : Chapter04FiniteAdeleRing K) : Chapter05AdeleAwayFrom K S :=
  ⟨fun v => chapter05FiniteCoordinate K x v.1, by
      classical
      have hfinite' : ∀ v : {v // v ∉ S}, ∃ w : Chapter04FinitePlace K,
          v.1 = Sum.inl w := by
        intro v
        exact hfinite v.1 v.2
      let f : {v // v ∉ S} → Chapter04FinitePlace K :=
        fun v => (hfinite' v).choose
      have hf_spec : ∀ v : {v // v ∉ S}, v.1 = Sum.inl (f v) := by
        intro v
        exact (hfinite' v).choose_spec
      have hf : Function.Injective f := by
        intro v₁ v₂ h
        apply Subtype.ext
        rw [hf_spec v₁, hf_spec v₂, h]
      have hx : ∀ᶠ w : Chapter04FinitePlace K in Filter.cofinite,
          x w ∈ chapter04FiniteLocalIntegerSet K w :=
        chapter04_finiteAdele_mem_iff_eventually_integral K x
      have hpull : ∀ᶠ v : {v // v ∉ S} in Filter.cofinite,
          x (f v) ∈ chapter04FiniteLocalIntegerSet K (f v) :=
        hf.tendsto_cofinite hx
      filter_upwards [hpull] with v hv
      rcases v with ⟨v, hvS⟩
      rcases v with w | w
      · have hfw : f ⟨Sum.inl w, hvS⟩ = w := by
          apply Sum.inl.inj
          exact (hf_spec ⟨Sum.inl w, hvS⟩).symm
        change x w ∈ chapter04FiniteLocalIntegerSet K w
        rw [hfw] at hv
        exact hv
      · simp [chapter05FiniteCoordinate, chapter04LocalIntegralSubring]⟩

def chapter05AwayBasicNeighborhood
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (x : Chapter05AdeleAwayFrom K S)
    (T : Finset {v // v ∉ S})
    (W : ∀ v : T, Set (chapter04LocalField K v.1)) :
    Set (Chapter05AdeleAwayFrom K S) :=
  {y |
    (∀ v : T, y v - x v ∈ W v) ∧
      (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
        y v - x v ∈ (chapter04LocalIntegralSubring K v.1 :
          Set (chapter04LocalField K v.1)))}

@[simp]
theorem chapter05_mem_awayBasicNeighborhood_iff
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K))
    (x y : Chapter05AdeleAwayFrom K S)
    (T : Finset {v // v ∉ S})
    (W : ∀ v : T, Set (chapter04LocalField K v.1)) :
    y ∈ chapter05AwayBasicNeighborhood K S x T W ↔
      ((∀ v : T, y v - x v ∈ W v) ∧
        (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
          y v - x v ∈ (chapter04LocalIntegralSubring K v.1 :
            Set (chapter04LocalField K v.1)))) := by
  rfl

def chapter05RestrictedProductBasis
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) : Prop :=
  ∀ (x : Chapter05AdeleAwayFrom K S)
    (U : Set (Chapter05AdeleAwayFrom K S)), U ∈ 𝓝 x →
      ∃ (T : Finset {v // v ∉ S})
        (W : ∀ v : T, Set (chapter04LocalField K v.1)),
        (∀ v : T, W v ∈ 𝓝 (0 : chapter04LocalField K v.1)) ∧
          chapter05AwayBasicNeighborhood K S x T W ⊆ U

def chapter05WeakApproximationStatement
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) : Prop :=
  ∀ (x : ∀ v : T, chapter04LocalField K v.1)
    (W : ∀ v : T, Set (chapter04LocalField K v.1)),
    (∀ v : T, W v ∈ 𝓝 (x v)) →
      ∃ a : K, ∀ v : T,
        chapter05LocalEmbedding K v.1 a ∈ W v

def chapter05DiagonalAtPlaces
    (K : Type*) [Field K] [NumberField K]
    (T : Finset (Chapter04Place K)) :
    K → (∀ v : T, chapter04LocalField K v.1) :=
  fun a v => chapter05LocalEmbedding K v.1 a

def chapter05StrongApproximationAwayFrom
    (K : Type*) [Field K] [NumberField K]
    (S : Set (Chapter04Place K)) : Prop :=
  ∀ (T : Finset {v // v ∉ S})
    (x : ∀ v : T, chapter04LocalField K v.1)
    (W : ∀ v : T, Set (chapter04LocalField K v.1)),
    (∀ v : T, W v ∈ 𝓝 (0 : chapter04LocalField K v.1)) →
      ∃ a : K,
        (∀ v : T,
          chapter05LocalEmbedding K v.1 a - x v ∈ W v) ∧
        (∀ v : {v // v ∉ S}, v ∉ (T : Set {v // v ∉ S}) →
          chapter05LocalEmbedding K v.1 a ∈
            (chapter04LocalIntegralSubring K v.1 :
              Set (chapter04LocalField K v.1)))

end

end LastLib.Book04AdelesAndIdeles.Chapter05
