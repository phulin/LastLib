import Mathlib.Topology.Defs.Induced
import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter11

open NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-! ## 11.5 Open compact subgroups -/

def chapter11FiniteRayUnitSubgroup (m : RayModulus K) :
    Subgroup (Chapter11FiniteIdeleGroup K) where
  carrier := {x |
    ∀ v, chapter11FiniteIdeleComponent K v x ∈
      chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)}
  one_mem' := by
    sorry
  mul_mem' := by
    intro x y hx hy
    sorry
  inv_mem' := by
    intro x hx
    sorry

theorem chapter11_finite_ray_unit_subgroup_mem_iff (m : RayModulus K)
    (x : Chapter11FiniteIdeleGroup K) :
    x ∈ chapter11FiniteRayUnitSubgroup m ↔
      ∀ v, chapter11FiniteIdeleComponent K v x ∈
        chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) := by
  rfl

theorem chapter11_finite_ray_unit_subgroup_is_compact_open (m : RayModulus K) :
    IsCompact (chapter11FiniteRayUnitSubgroup m : Set (Chapter11FiniteIdeleGroup K)) ∧
      IsOpen (chapter11FiniteRayUnitSubgroup m : Set (Chapter11FiniteIdeleGroup K)) := by
  sorry

theorem chapter11_finite_ray_unit_subgroups_are_cofinal_among_compact_open_subgroups
    (H : Subgroup (Chapter11FiniteIdeleGroup K))
    (hcompact : IsCompact (H : Set (Chapter11FiniteIdeleGroup K)))
    (hopen : IsOpen (H : Set (Chapter11FiniteIdeleGroup K))) :
    ∃ m : RayModulus K,
      m.infinitePart = ∅ ∧ chapter11FiniteRayUnitSubgroup m ≤ H := by
  sorry

theorem chapter11_compact_open_finite_subgroup_is_eventually_integral
    (H : Subgroup (Chapter11FiniteIdeleGroup K))
    (hcompact : IsCompact (H : Set (Chapter11FiniteIdeleGroup K)))
    (hopen : IsOpen (H : Set (Chapter11FiniteIdeleGroup K))) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      ∀ x ∈ H, ∀ v, v ∉ S →
        chapter11FiniteIdeleComponent K v x ∈
        chapter11FiniteLocalUnitGroup K v 0 := by
  sorry

theorem chapter11_additive_compact_open_subgroup_is_eventually_an_ideal_lattice
    (H : AddSubgroup (Chapter11FiniteAdeleRing K))
    (hcompact : IsCompact (H : Set (Chapter11FiniteAdeleRing K)))
    (hopen : IsOpen (H : Set (Chapter11FiniteAdeleRing K))) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
      ∀ x ∈ H, ∀ v, v ∉ S →
        ∃ z : v.adicCompletionIntegers K,
          (z : v.adicCompletion K) = x v ∧
            z ∈ chapter11AdditiveLocalDepth
              (A := v.adicCompletionIntegers K) 0 := by
  sorry

theorem chapter11_one_plus_translation_has_multiplicative_defect
    {A : Type*} [CommRing A] (x y : A) :
    (1 + x) * (1 + y) - 1 - (x + y) = x * y := by
  sorry

theorem chapter11_local_multiplicative_layer_is_additive_layer
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsPrincipalIdealRing A] {n : ℕ} (hn : 0 < n) :
    Nonempty
      (chapter11MultiplicativeLocalLayer (A := A) n ≃*
        Multiplicative (chapter11AdditiveLocalLayer (A := A) n)) := by
  sorry

abbrev Chapter11ArchimedeanMaximalCompact (K : Type*) [Field K] [NumberField K] :=
  (({v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal v} → SignTypeˣ) ×
    ({v : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsComplex v} → Circle))

theorem chapter11_archimedean_maximal_compact_factor_is_compact
    (K : Type*) [Field K] [NumberField K] :
    CompactSpace (Chapter11ArchimedeanMaximalCompact K) := by
  sorry

structure Chapter11MagnitudeDirection {G : Type*} [TopologicalSpace G] where
  toFun : ℝ → G
  closedEmbedding : Topology.IsClosedEmbedding toFun

def chapter11ContainsMagnitudeDirection {G : Type*} [Group G] [TopologicalSpace G]
    (H : Subgroup G) : Prop :=
  Nonempty (Chapter11MagnitudeDirection (G := H))

theorem chapter11_compact_subgroup_cannot_contain_magnitude_direction
    {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G)
    (hcompact : IsCompact (H : Set G))
    (hdirection : chapter11ContainsMagnitudeDirection H) : False := by
  sorry

end
