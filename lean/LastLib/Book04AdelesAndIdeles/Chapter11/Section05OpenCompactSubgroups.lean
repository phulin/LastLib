import Mathlib.Topology.Defs.Induced
import Mathlib.Topology.Algebra.OpenSubgroup
import LastLib.Book04AdelesAndIdeles.Chapter09.Section03CompactnessOfNormOneClassGroup
import LastLib.Book04AdelesAndIdeles.Chapter08.Section81
import LastLib.Book04AdelesAndIdeles.Chapter11.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter11.Section02LocalCongruenceGroups

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
    intro v
    simpa only [map_one] using
      (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).one_mem
  mul_mem' := by
    intro x y hx hy v
    simpa only [map_mul] using
      (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).mul_mem
        (hx v) (hy v)
  inv_mem' := by
    intro x hx v
    simpa only [map_inv] using
      (chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)).inv_mem (hx v)

theorem chapter11_finite_ray_unit_subgroup_mem_iff (m : RayModulus K)
    (x : Chapter11FiniteIdeleGroup K) :
    x ∈ chapter11FiniteRayUnitSubgroup m ↔
      ∀ v, chapter11FiniteIdeleComponent K v x ∈
        chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) := by
  rfl

theorem chapter11_finite_ray_unit_subgroup_is_compact_open (m : RayModulus K) :
    IsCompact (chapter11FiniteRayUnitSubgroup m : Set (Chapter11FiniteIdeleGroup K)) ∧
      IsOpen (chapter11FiniteRayUnitSubgroup m : Set (Chapter11FiniteIdeleGroup K)) := by
  classical
  let e := LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K
  let lift : Chapter11FiniteIdeleGroup K → Chapter11IdeleGroup K :=
    fun x => e.symm (1, x)
  let tprod : TopologicalSpace
      ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ ×
        Chapter11FiniteIdeleGroup K) :=
    @instTopologicalSpaceProd
      ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ)
      (Chapter11FiniteIdeleGroup K) inferInstance
      (chapter11FiniteIdeleGraphTopology K)
  have hlift : Continuous lift := by
    change @Continuous
      (Chapter11FiniteIdeleGroup K)
      (Chapter11IdeleGroup K)
      (chapter11FiniteIdeleGraphTopology K)
      (TopologicalSpace.induced
        (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09IdeleProductEquiv K :
          Chapter11IdeleGroup K →
            ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ ×
              Chapter11FiniteIdeleGroup K))
        tprod)
      lift
    rw [continuous_induced_rng]
    have hprod : @Continuous (Chapter11FiniteIdeleGroup K)
        ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ ×
          Chapter11FiniteIdeleGroup K)
        (chapter11FiniteIdeleGraphTopology K) tprod
        (fun x => ((1 :
          (LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K)ˣ), x)) := by
      exact continuous_const.prodMk continuous_id
    have heq : (fun x => e (lift x)) = (fun x => (1, x)) := by
      funext x
      exact e.apply_symm_apply _
    change Continuous (fun x => e (lift x))
    rw [heq]
    exact hprod
  have hopen : IsOpen (chapter11FiniteRayUnitSubgroup m :
      Set (Chapter11FiniteIdeleGroup K)) := by
    have hpre : IsOpen (lift ⁻¹'
        (chapter11RayUnitSubgroup m : Set (Chapter11IdeleGroup K))) :=
      (chapter11_ray_unit_subgroup_is_open m).preimage hlift
    have heq : lift ⁻¹' (chapter11RayUnitSubgroup m : Set (Chapter11IdeleGroup K)) =
        (chapter11FiniteRayUnitSubgroup m : Set (Chapter11FiniteIdeleGroup K)) := by
      ext x
      change
        ((∀ v, chapter11IdeleFiniteComponent K v (lift x) ∈
            chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)) ∧
          (∀ v (hv : v ∈ m.infinitePart),
            chapter11RealSignComponent K v (m.infinitePart_isReal v hv) (lift x) = 1)) ↔
          ∀ v, chapter11FiniteIdeleComponent K v x ∈
            chapter11FiniteLocalUnitGroup K v (m.finiteExponent v)
      constructor
      · intro hx v
        have hcomp : chapter11IdeleFiniteComponent K v (lift x) =
            chapter11FiniteIdeleComponent K v x := by
          apply Units.ext
          have hdecomp : e (lift x) = (1, x) := e.apply_symm_apply _
          exact congrArg (fun z => ((z.2 : Chapter11FiniteAdeleRing K) v)) hdecomp
        rw [← hcomp]
        exact hx.1 v
      · intro hx
        refine ⟨?_, ?_⟩
        · intro v
          have hcomp : chapter11IdeleFiniteComponent K v (lift x) =
              chapter11FiniteIdeleComponent K v x := by
            apply Units.ext
            have hdecomp : e (lift x) = (1, x) := e.apply_symm_apply _
            exact congrArg (fun z => ((z.2 : Chapter11FiniteAdeleRing K) v)) hdecomp
          rw [hcomp]
          exact hx v
        · intro v hv
          have hdecomp : e (lift x) = (1, x) := e.apply_symm_apply _
          have hinf : ((lift x : Chapter11AdeleRing K).1 v) = 1 := by
            change ((e (lift x)).1 :
              LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v = 1
            exact congrArg (fun z => ((z.1 :
              LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09InfiniteAdele K) v)) hdecomp
          apply Units.ext
          change SignType.sign
            (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
              (m.infinitePart_isReal v hv) ((lift x : Chapter11AdeleRing K).1 v)) = 1
          rw [hinf]
          simp
    rw [heq] at hpre
    exact hpre
  have hfull : IsCompact (chapter11FiniteRayUnitSubgroup (RayModulus.trivial (K := K)) :
      Set (Chapter11FiniteIdeleGroup K)) := by
    have htop : chapter11FiniteIdeleGraphTopology K =
        (Units.instTopologicalSpaceUnits : TopologicalSpace (Chapter11FiniteIdeleGroup K)) := by
      simpa [chapter11FiniteIdeleGraphTopology,
        LastLib.Book04AdelesAndIdeles.Chapter08.chapter08FiniteIdeleGraphTopology] using
        (LastLib.Book04AdelesAndIdeles.Chapter07.chapter07_finiteIdele_restrictedProduct_topology
          (𝓞 K) K).symm
    change @IsCompact (Chapter11FiniteIdeleGroup K)
      (chapter11FiniteIdeleGraphTopology K) _
    rw [htop]
    have hsub : @IsCompact
        (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteUnitIdeles K)
        (@instTopologicalSpaceSubtype
          ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09FiniteAdele K)ˣ)
          (fun x => x ∈
            LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteUnitIdeles K)
          Units.instTopologicalSpaceUnits)
        (Set.univ : Set (
          LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteUnitIdeles K)) :=
      LastLib.Book04AdelesAndIdeles.Chapter09.chapter09_finite_unit_ideles_compact K
    have himage :=
      (@Subtype.isCompact_iff
        ((LastLib.Book04AdelesAndIdeles.Chapter09.Chapter09FiniteAdele K)ˣ)
        Units.instTopologicalSpaceUnits
        (fun x => x ∈ LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteUnitIdeles K)
        (Set.univ : Set (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteUnitIdeles K))).mp hsub
    have himage_eq :
        Subtype.val '' (Set.univ :
          Set (LastLib.Book04AdelesAndIdeles.Chapter09.chapter09FiniteUnitIdeles K)) =
          (chapter11FiniteRayUnitSubgroup (RayModulus.trivial (K := K)) :
            Set (Chapter11FiniteIdeleGroup K)) := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        change ∀ v, chapter11FiniteIdeleComponent K v y ∈
          chapter11FiniteLocalUnitGroup K v 0
        intro v
        rw [chapter11FiniteLocalUnitGroup_zero K v]
        have hv := (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one
          y.1).1 y.2 v
        change Valued.v ((chapter11FiniteIdeleComponent K v y.1 :
          v.adicCompletion K) : v.adicCompletion K) = 1 at hv
        exact (Valuation.mem_unitGroup_iff (v.adicCompletion K) (Valued.v) _).2 hv
      · intro hx
        change ∀ v, chapter11FiniteIdeleComponent K v x ∈
          chapter11FiniteLocalUnitGroup K v 0 at hx
        refine ⟨⟨x, ?_⟩, Set.mem_univ _, rfl⟩
        apply (LastLib.Book04AdelesAndIdeles.Chapter08.chapter08_finite_integral_unit_iff_local_valued_eq_one
          x).2
        intro v
        have hv := hx v
        rw [chapter11FiniteLocalUnitGroup_zero K v] at hv
        have hv' :=
          (Valuation.mem_unitGroup_iff (v.adicCompletion K) (Valued.v) _).1 hv
        change Valued.v ((chapter11FiniteIdeleComponent K v x :
          v.adicCompletion K) : v.adicCompletion K) = 1
        exact hv'
    rw [← himage_eq]
    exact himage
  have hclosed : IsClosed (chapter11FiniteRayUnitSubgroup m :
      Set (Chapter11FiniteIdeleGroup K)) :=
    Subgroup.isClosed_of_isOpen _ hopen
  have hle : chapter11FiniteRayUnitSubgroup m ≤
      chapter11FiniteRayUnitSubgroup (RayModulus.trivial (K := K)) := by
    intro x hx
    change ∀ v, chapter11FiniteIdeleComponent K v x ∈
      chapter11FiniteLocalUnitGroup K v 0
    intro v
    apply (show chapter11FiniteLocalUnitGroup K v (m.finiteExponent v) ≤
        chapter11FiniteLocalUnitGroup K v 0 from ?_) (hx v)
    intro z hz
    rcases hz with ⟨u, hu, hzu⟩
    exact ⟨u, chapter11LocalUnitFiltration_antitone (Nat.zero_le _) hu, hzu⟩
  have hcompact : IsCompact (chapter11FiniteRayUnitSubgroup m :
      Set (Chapter11FiniteIdeleGroup K)) := by
    rw [show (chapter11FiniteRayUnitSubgroup m : Set (Chapter11FiniteIdeleGroup K)) =
        (chapter11FiniteRayUnitSubgroup (RayModulus.trivial (K := K)) :
          Set (Chapter11FiniteIdeleGroup K)) ∩
          (chapter11FiniteRayUnitSubgroup m : Set (Chapter11FiniteIdeleGroup K)) by
      ext x
      constructor
      · intro hx
        exact ⟨hle hx, hx⟩
      · rintro ⟨_, hx⟩
        exact hx]
    exact hfull.inter_right hclosed
  exact ⟨hcompact, hopen⟩

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
        x v ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  sorry

theorem chapter11_one_plus_translation_has_multiplicative_defect
    {A : Type*} [CommRing A] (x y : A) :
    (1 + x) * (1 + y) - 1 - (x + y) = x * y := by
  ring

theorem chapter11_local_multiplicative_layer_is_additive_layer
    {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ} (hn : 0 < n) :
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
  infer_instance

structure Chapter11MagnitudeDirection {G : Type*} [Group G] [TopologicalSpace G] where
  toFun : ℝ → G
  map_zero' : toFun 0 = 1
  map_add' : ∀ x y, toFun (x + y) = toFun x * toFun y
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
