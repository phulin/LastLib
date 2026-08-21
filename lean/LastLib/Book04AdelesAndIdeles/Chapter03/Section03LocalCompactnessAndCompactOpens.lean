import LastLib.Book04AdelesAndIdeles.Chapter03.Section02TheRestrictedProductTopology
import Mathlib.Topology.Algebra.Group.Pointwise

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter
open scoped BigOperators Pointwise Topology

noncomputable section

/-! ### 3.3 Local compactness and compact opens -/

universe u v

section RestrictedProductLocalCompactness

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

/-- The hypotheses used by the local-compactness proposition. -/
structure Chapter03LocallyCompactRestrictedProductHypotheses
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i)) : Prop where
  local_locally_compact : ∀ i, LocallyCompactSpace (G i)
  distinguished_compact : ∀ i, IsCompact (H i : Set (G i))
  distinguished_open : ∀ i, IsOpen (H i : Set (G i))

theorem chapter03_distinguishedTail_is_compact
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsCompact (H i : Set (G i))) :
    IsCompact (chapter03DistinguishedTail H) := by
  classical
  let T := Chapter03Stage H (∅ : Set I)
  let e : T → ∀ i, G i :=
    fun x => ((x : T).1 : ∀ i, G i)
  let j : T → Chapter03RestrictedProduct H := fun x => x.1
  have heimage : e '' (Set.univ : Set T) =
      Set.pi Set.univ (fun i => (H i : Set (G i))) := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      intro i hi
      exact x.2 i (by simp)
    · intro hy
      have hyH : ∀ i, y i ∈ H i := fun i => hy i (by simp)
      let z : Chapter03RestrictedProduct H :=
        ⟨y, (chapter03_restrictedProduct_mem_iff H y).2
          (Filter.Eventually.of_forall hyH)⟩
      have hz : z ∈ chapter03StageSubgroup H (∅ : Set I) := by
        intro i hi
        exact hyH i
      let x : T := ⟨z, hz⟩
      exact ⟨x, Set.mem_univ x, rfl⟩
  have hcompactProd :
      @IsCompact T (chapter03StageProductTopology H (∅ : Set I))
        (Set.univ : Set T) := by
    let _ : TopologicalSpace T := chapter03StageProductTopology H (∅ : Set I)
    have heprod : Topology.IsEmbedding e := by
      refine { eq_induced := ?_, injective := ?_ }
      · change chapter03StageProductTopology H (∅ : Set I) =
          TopologicalSpace.induced e inferInstance
        rfl
      · intro x y hxy
        apply Subtype.ext
        apply chapter03_restrictedProduct_ext H
        intro i
        exact congrFun hxy i
    rw [heprod.isCompact_iff, heimage]
    exact isCompact_univ_pi hH
  have htop :
      chapter03StageProductTopology H (∅ : Set I) ≤
        chapter03StageSubtypeTopology H (∅ : Set I) := by
    change chapter03StageProductTopology H (∅ : Set I) ≤
      TopologicalSpace.induced j (chapter03RestrictedProductTopology H)
    rw [← continuous_iff_le_induced]
    rw [continuous_generateFrom_iff]
    rintro _ ⟨U, hU, rfl⟩
    have hE : {i | U i ≠ (H i : Set (G i))}.Finite := by
      exact Filter.eventually_cofinite.mp hU.2
    let E : Set I := {i | U i ≠ (H i : Set (G i))}
    let V : ∀ i, Set (G i) := fun i =>
      if i ∈ E then U i else Set.univ
    have hVopen : IsOpen (Set.pi Set.univ V) := by
      rw [show Set.pi Set.univ V = Set.pi E V by
        ext x
        constructor
        · intro hx i hi
          exact hx i (by simp)
        · intro hx i hi
          by_cases hiE : i ∈ E
          · exact hx i hiE
          · change x i ∈ (if i ∈ E then U i else Set.univ)
            rw [if_neg hiE]
            exact Set.mem_univ _]
      apply isOpen_set_pi (by simpa [E] using hE)
      intro i hi
      by_cases hiE : i ∈ E
      · change IsOpen (if i ∈ E then U i else Set.univ)
        rw [if_pos hiE]
        exact hU.1 i
      · change IsOpen (if i ∈ E then U i else Set.univ)
        rw [if_neg hiE]
        exact isOpen_univ
    have hset :
        j ⁻¹' chapter03BasicProductSet H U =
          e ⁻¹' Set.pi Set.univ V := by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_preimage, Set.mem_pi, mem_univ, true_implies]
        intro i
        by_cases hiE : i ∈ E
        · change e x i ∈ (if i ∈ E then U i else Set.univ)
          rw [if_pos hiE]
          simpa [e] using hx i
        · change e x i ∈ (if i ∈ E then U i else Set.univ)
          rw [if_neg hiE]
          exact Set.mem_univ _
      · intro hx
        change ∀ i, ((x : T).1 : ∀ i, G i) i ∈ U i
        intro i
        by_cases hiE : i ∈ E
        ·
          simpa [e, V, hiE] using hx i (by simp)
        · have hiU : U i = (H i : Set (G i)) := by
            by_contra hne
            exact hiE (by simpa [E] using hne)
          have hxi : ((x : T).1 : ∀ i, G i) i ∈ H i := by
            exact x.2 i (by simp)
          simpa [hiU] using hxi
    rw [hset]
    exact isOpen_induced hVopen
  have hcompactSub :
    @IsCompact T (chapter03StageSubtypeTopology H (∅ : Set I))
        (Set.univ : Set T) := by
    refine (isCompact_iff_ultrafilter_le_nhds).2 ?_
    intro F hFle
    obtain ⟨x, hx, hxF⟩ :=
      (@isCompact_iff_ultrafilter_le_nhds T
        (chapter03StageProductTopology H (∅ : Set I))
        (Set.univ : Set T)).mp hcompactProd F hFle
    exact ⟨x, hx, hxF.trans (nhds_mono htop)⟩
  have hj : @Topology.IsEmbedding T (Chapter03RestrictedProduct H)
      (chapter03StageSubtypeTopology H (∅ : Set I))
      (chapter03RestrictedProductTopology H) j := by
    refine { eq_induced := ?_, injective := ?_ }
    · rfl
    · intro x y hxy
      exact Subtype.ext hxy
  have hjimage : j '' (Set.univ : Set T) = chapter03DistinguishedTail H := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      apply (chapter03_distinguishedTail_mem_iff H _).2
      intro i
      exact y.2 i (by simp)
    · intro hx
      have hxH := (chapter03_distinguishedTail_mem_iff H x).1 hx
      have hxS : x ∈ chapter03StageSubgroup H (∅ : Set I) := by
        intro i hi
        exact hxH i
      let y : T := ⟨x, hxS⟩
      exact ⟨y, Set.mem_univ y, rfl⟩
  have himagecompact : IsCompact (j '' (Set.univ : Set T)) :=
    (Topology.IsEmbedding.isCompact_iff hj (s := (Set.univ : Set T))).1 hcompactSub
  rw [hjimage] at himagecompact
  exact himagecompact

theorem chapter03_distinguishedTail_is_open
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    IsOpen (chapter03DistinguishedTail H) := by
  exact chapter03_stage_isOpen H Set.finite_empty hH

theorem chapter03_distinguishedTail_is_compact_open
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i))) :
    IsCompact (chapter03DistinguishedTail H) ∧
      IsOpen (chapter03DistinguishedTail H) := by
  exact ⟨chapter03_distinguishedTail_is_compact H hcompact,
    chapter03_distinguishedTail_is_open H hopen⟩

private theorem chapter03_compact_subset_basicProduct
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i)))
    (U : ∀ i, Set (G i))
    (hU : chapter03BasicProductCondition H U)
    (x : Chapter03RestrictedProduct H)
    (hx : x ∈ chapter03BasicProductSet H U) :
    ∃ K : Set (Chapter03RestrictedProduct H),
      IsCompact K ∧ K ∈ 𝓝 x ∧ K ⊆ chapter03BasicProductSet H U := by
  classical
  let E : Set I := {i | U i ≠ (H i : Set (G i))}
  have hE : E.Finite := by
    exact Filter.eventually_cofinite.mp hU.2
  have hKdata : ∀ i, ∃ K : Set (G i),
      (i ∈ E → IsCompact K ∧ K ∈ 𝓝 ((x : ∀ i, G i) i) ∧ K ⊆ U i) ∧
        (i ∉ E → K = (H i : Set (G i))) := by
    intro i
    by_cases hi : i ∈ E
    · obtain ⟨K, hKnhds, hKsub, hKcompact⟩ :=
        (hlocal i).local_compact_nhds ((x : ∀ i, G i) i) (U i)
          ((hU.1 i).mem_nhds (hx i))
      exact ⟨K, fun _ => ⟨hKcompact, hKnhds, hKsub⟩, fun h => (h hi).elim⟩
    · refine ⟨(H i : Set (G i)), ?_, fun _ => rfl⟩
      exact fun hiE => (hi hiE).elim
  choose K hKdata using hKdata
  have hKcompact : ∀ i, IsCompact (K i) := by
    intro i
    by_cases hi : i ∈ E
    · exact (hKdata i).1 hi |>.1
    · rw [(hKdata i).2 hi]
      exact hcompact i
  have hKtail : ∀ i, i ∉ E → K i = (H i : Set (G i)) := fun i => (hKdata i).2
  have hKsubset : ∀ i, i ∈ E → K i ⊆ U i := by
    intro i hi
    exact (hKdata i).1 hi |>.2.2
  have hKnhds : ∀ i, i ∈ E → K i ∈ 𝓝 ((x : ∀ i, G i) i) := by
    intro i hi
    exact (hKdata i).1 hi |>.2.1
  have hVdata : ∀ i, ∃ V : Set (G i),
      IsOpen V ∧ ((x : ∀ i, G i) i ∈ V) ∧ V ⊆ K i ∧
        (i ∉ E → V = (H i : Set (G i))) := by
    intro i
    by_cases hi : i ∈ E
    · rcases mem_nhds_iff.mp (hKnhds i hi) with ⟨V, hVK, hVopen, hxV⟩
      exact ⟨V, hVopen, hxV, hVK, fun h => (h hi).elim⟩
    · refine ⟨(H i : Set (G i)), ?_, ?_, ?_, fun _ => rfl⟩
      · have hUeq : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hi (by simpa [E] using hne)
        simpa [hUeq] using hU.1 i
      · have hUeq : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hi (by simpa [E] using hne)
        have hxiH : ((x : ∀ i, G i) i) ∈ H i := by
          simpa [hUeq] using hx i
        exact hxiH
      · rw [hKtail i hi]
  choose V hVopen hxV hVK hVtail using hVdata
  have hVcond : chapter03BasicProductCondition H V := by
    constructor
    · exact hVopen
    · filter_upwards [hE.compl_mem_cofinite] with i hi
      exact hVtail i (by simpa [E] using hi)
  have hBopen : IsOpen (chapter03BasicProductSet H V) :=
    chapter03_basicProductSet_isOpen H V hVcond
  have hxB : x ∈ chapter03BasicProductSet H V := by
    intro i
    exact hxV i
  let T := Chapter03Stage H E
  let e : T → ∀ i, G i :=
    fun y => ((y : T).1 : ∀ i, G i)
  let Q : Set T := e ⁻¹' Set.pi Set.univ K
  have heimage : e '' Q = Set.pi Set.univ K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hyH : ∀ᶠ i in Filter.cofinite, y i ∈ H i := by
        filter_upwards [hE.compl_mem_cofinite] with i hi
        have hiE : i ∉ E := by simpa [E] using hi
        have hyK : y i ∈ K i := hy i (by simp)
        simpa [hKtail i hiE] using hyK
      let z : Chapter03RestrictedProduct H := ⟨y, hyH⟩
      have hzE : z ∈ chapter03StageSubgroup H E := by
        intro i hi
        have hyK : y i ∈ K i := hy i (by simp)
        change y i ∈ H i
        simpa [hKtail i hi] using hyK
      let t : T := ⟨z, hzE⟩
      exact ⟨t, hy, rfl⟩
  have hQcompact : @IsCompact T (chapter03StageProductTopology H E) Q := by
    let _ : TopologicalSpace T := chapter03StageProductTopology H E
    have hemb : Topology.IsEmbedding e := by
      refine { eq_induced := rfl, injective := ?_ }
      intro y z h
      apply Subtype.ext
      apply chapter03_restrictedProduct_ext H
      intro i
      exact congrFun h i
    rw [hemb.isCompact_iff, heimage]
    exact isCompact_univ_pi hKcompact
  have hQcompact' : @IsCompact T (chapter03StageSubtypeTopology H E) Q := by
    rw [chapter03_stage_subtype_topology_eq_product_topology H hE hopen]
    exact hQcompact
  let j : T → Chapter03RestrictedProduct H := fun y => y.1
  have hj : @Topology.IsEmbedding T (Chapter03RestrictedProduct H)
      (chapter03StageSubtypeTopology H E)
      (chapter03RestrictedProductTopology H) j := by
    refine { eq_induced := rfl, injective := ?_ }
    intro y z h
    exact Subtype.ext h
  let K' : Set (Chapter03RestrictedProduct H) := j '' Q
  have hK'compact : IsCompact K' := by
    exact (hj.isCompact_iff (s := Q)).1 hQcompact'
  have hBsub : chapter03BasicProductSet H V ⊆ K' := by
    intro y hy
    have hyE : y ∈ chapter03StageSubgroup H E := by
      intro i hi
      simpa [hVtail i hi] using hy i
    let z : T := ⟨y, hyE⟩
    have hzQ : z ∈ Q := by
      intro i _
      simpa [e, z] using hVK i (hy i)
    exact ⟨z, hzQ, rfl⟩
  have hKsubset' : K' ⊆ chapter03BasicProductSet H U := by
    rintro y ⟨z, hzQ, rfl⟩
    intro i
    by_cases hi : i ∈ E
    · exact hKsubset i hi (by simpa [e] using hzQ i (by simp))
    · have hzH : ((z : T).1 : ∀ i, G i) i ∈ H i := z.2 i hi
      have hUeq : U i = (H i : Set (G i)) := by
        by_contra hne
        exact hi (by simpa [E] using hne)
      simpa [j, hUeq] using hzH
  refine ⟨K', hK'compact, ?_, hKsubset'⟩
  exact mem_of_superset (hBopen.mem_nhds hxB) hBsub

/-- Compact neighborhoods in finitely many exceptional factors give compact
neighborhoods everywhere in the restricted product. -/
theorem chapter03_restrictedProduct_has_compact_neighborhood
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i)))
    (x : Chapter03RestrictedProduct H) :
    ∃ K : Set (Chapter03RestrictedProduct H),
      IsCompact K ∧ K ∈ 𝓝 x := by
  classical
  let E : Set I := chapter03ExceptionalSet H (x : ∀ i, G i)
  have hE : E.Finite := by
    exact (chapter03_restrictedProduct_mem_iff_exceptional_finite H
      (x : ∀ i, G i)).1 x.property
  have hKdata : ∀ i, ∃ K : Set (G i),
      (i ∈ E → IsCompact K ∧ K ∈ 𝓝 ((x : ∀ i, G i) i)) ∧
        (i ∉ E → K = (H i : Set (G i))) := by
    intro i
    by_cases hi : i ∈ E
    · obtain ⟨K, hKnhds, hKsub, hKcompact⟩ :=
        (hlocal i).local_compact_nhds ((x : ∀ i, G i) i) Set.univ
          univ_mem
      exact ⟨K, fun _ => ⟨hKcompact, hKnhds⟩, fun h => (h hi).elim⟩
    · refine ⟨(H i : Set (G i)), ?_, fun _ => rfl⟩
      intro _
      refine ⟨hcompact i, ?_⟩
      have hxiH : ((x : ∀ i, G i) i) ∈ H i := by
        by_contra hne
        apply hi
        simpa [E, chapter03ExceptionalSet] using hne
      exact (hopen i).mem_nhds hxiH
  choose K hKdata using hKdata
  have hKcompact : ∀ i, IsCompact (K i) := by
    intro i
    by_cases hi : i ∈ E
    · exact (hKdata i).1 hi |>.1
    · rw [(hKdata i).2 hi]
      exact hcompact i
  have hKtail : ∀ i, i ∉ E → K i = (H i : Set (G i)) := fun i => (hKdata i).2
  have hKnhds : ∀ i, i ∈ E → K i ∈ 𝓝 ((x : ∀ i, G i) i) := by
    intro i hi
    exact (hKdata i).1 hi |>.2
  have hUdata : ∀ i, ∃ U : Set (G i),
      IsOpen U ∧ ((x : ∀ i, G i) i ∈ U) ∧ U ⊆ K i ∧
        (i ∉ E → U = (H i : Set (G i))) := by
    intro i
    by_cases hi : i ∈ E
    · rcases mem_nhds_iff.mp (hKnhds i hi) with ⟨U, hUK, hUopen, hxU⟩
      exact ⟨U, hUopen, hxU, hUK, fun h => (h hi).elim⟩
    · refine ⟨(H i : Set (G i)), hopen i, ?_, ?_, fun _ => rfl⟩
      · have hxiH : ((x : ∀ i, G i) i) ∈ H i := by
          by_contra hne
          apply hi
          simpa [E, chapter03ExceptionalSet] using hne
        exact hxiH
      · rw [hKtail i hi]
  choose U hUopen hxU hUK hUtail using hUdata
  have hUcond : chapter03BasicProductCondition H U := by
    constructor
    · exact hUopen
    · filter_upwards [hE.compl_mem_cofinite] with i hi
      exact hUtail i (by simpa [E] using hi)
  have hBopen : IsOpen (chapter03BasicProductSet H U) :=
    chapter03_basicProductSet_isOpen H U hUcond
  have hxB : x ∈ chapter03BasicProductSet H U := by
    intro i
    exact hxU i
  let T := Chapter03Stage H E
  let e : T → ∀ i, G i :=
    fun y => ((y : T).1 : ∀ i, G i)
  let Q : Set T := e ⁻¹' Set.pi Set.univ K
  have heimage : e '' Q = Set.pi Set.univ K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hyH : ∀ᶠ i in Filter.cofinite, y i ∈ H i := by
        filter_upwards [hE.compl_mem_cofinite] with i hi
        have hiE : i ∉ E := by simpa [E] using hi
        have hyK : y i ∈ K i := hy i (by simp)
        simpa [hKtail i hiE] using hyK
      let z : Chapter03RestrictedProduct H := ⟨y, hyH⟩
      have hzE : z ∈ chapter03StageSubgroup H E := by
        intro i hi
        have hyK : y i ∈ K i := hy i (by simp)
        change y i ∈ H i
        simpa [hKtail i hi] using hyK
      let t : T := ⟨z, hzE⟩
      exact ⟨t, hy, rfl⟩
  have hQcompact : @IsCompact T (chapter03StageProductTopology H E) Q := by
    let _ : TopologicalSpace T := chapter03StageProductTopology H E
    have hemb : Topology.IsEmbedding e := by
      refine { eq_induced := rfl, injective := ?_ }
      intro y z h
      apply Subtype.ext
      apply chapter03_restrictedProduct_ext H
      intro i
      exact congrFun h i
    rw [hemb.isCompact_iff, heimage]
    exact isCompact_univ_pi hKcompact
  have hQcompact' : @IsCompact T (chapter03StageSubtypeTopology H E) Q := by
    rw [chapter03_stage_subtype_topology_eq_product_topology H hE hopen]
    exact hQcompact
  let j : T → Chapter03RestrictedProduct H := fun y => y.1
  have hj : @Topology.IsEmbedding T (Chapter03RestrictedProduct H)
      (chapter03StageSubtypeTopology H E)
      (chapter03RestrictedProductTopology H) j := by
    refine { eq_induced := rfl, injective := ?_ }
    intro y z h
    exact Subtype.ext h
  let K' : Set (Chapter03RestrictedProduct H) := j '' Q
  have hK'compact : IsCompact K' := by
    exact (hj.isCompact_iff (s := Q)).1 hQcompact'
  have hBsub : chapter03BasicProductSet H U ⊆ K' := by
    intro y hy
    have hyE : y ∈ chapter03StageSubgroup H E := by
      intro i hi
      have hiU : U i = (H i : Set (G i)) := hUtail i hi
      simpa [hiU] using hy i
    let z : T := ⟨y, hyE⟩
    have hzQ : z ∈ Q := by
      intro i _
      simpa [e, z] using hUK i (hy i)
    exact ⟨z, hzQ, rfl⟩
  refine ⟨K', hK'compact, ?_⟩
  exact mem_of_superset (hBopen.mem_nhds hxB) hBsub

theorem chapter03_restrictedProduct_locallyCompact
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i))) :
    LocallyCompactSpace (Chapter03RestrictedProduct H) := by
  refine ⟨?_⟩
  intro x n hn
  change n ∈ @nhds _ (chapter03RestrictedProductTopology H) x at hn
  rw [TopologicalSpace.nhds_generateFrom] at hn
  rcases (Filter.mem_biInf_principal.mp hn) with ⟨T, hTfin, hTgen, hTsub⟩
  have hSx : (chapter03ExceptionalSet H (x : ∀ i, G i)).Finite := by
    exact (chapter03_restrictedProduct_mem_iff_exceptional_finite H
      (x : ∀ i, G i)).1 x.property
  rcases chapter03_stage_is_basicProduct H hSx hopen with ⟨U₀, hU₀, hU₀eq⟩
  let b₀ : Set (Chapter03RestrictedProduct H) := chapter03BasicProductSet H U₀
  have hb₀ : b₀ ∈ chapter03BasicOpenSets H := ⟨U₀, hU₀, rfl⟩
  have hxb₀ : x ∈ b₀ := by
    change x ∈ chapter03BasicProductSet H U₀
    rw [hU₀eq]
    exact (chapter03_stage_mem_iff_exceptional_subset H _ x).2 Set.Subset.rfl
  let T' : Set (Set (Chapter03RestrictedProduct H)) := insert b₀ T
  have hT'fin : T'.Finite := hTfin.insert b₀
  have hT'gen : ∀ t ∈ T', t ∈ {s | x ∈ s ∧ s ∈ chapter03BasicOpenSets H} := by
    intro t ht
    simp only [T', mem_insert_iff] at ht
    rcases ht with rfl | ht
    · exact ⟨hxb₀, hb₀⟩
    · exact hTgen t ht
  have hT'sub : (⋂ t ∈ T', t) ⊆ n := by
    intro y hy
    apply hTsub
    simp only [mem_iInter] at hy ⊢
    intro t ht
    exact hy t (by simp [T', ht])
  have hbasic : ∀ t ∈ T', ∃ U : ∀ i, Set (G i),
      chapter03BasicProductCondition H U ∧
        chapter03BasicProductSet H U = t := by
    intro t ht
    rcases (hT'gen t ht).2 with ⟨U, hU, rfl⟩
    exact ⟨U, hU, rfl⟩
  let _ : Fintype T' := hT'fin.fintype
  choose U hU hUt using (fun t : T' => hbasic t t.property)
  let W : ∀ i, Set (G i) := fun i => ⋂ t : T', U t i
  have hW : chapter03BasicProductCondition H W := by
    constructor
    · intro i
      exact isOpen_iInter_of_finite (fun t => (hU t).1 i)
    · have he : ∀ᶠ i in Filter.cofinite, ∀ t : T', U t i = (H i : Set (G i)) :=
        (Filter.eventually_all).2 fun t => (hU t).2
      filter_upwards [he] with i hi
      ext y
      simp only [W, mem_iInter]
      let t₀ : T' := ⟨b₀, by simp [T']⟩
      constructor
      · intro hy
        rw [← hi t₀]
        exact hy t₀
      · intro hy t
        rw [hi t]
        exact hy
  have hxW : x ∈ chapter03BasicProductSet H W := by
    intro i
    simp only [W, mem_iInter]
    intro t
    have hxt : x ∈ (t : Set (Chapter03RestrictedProduct H)) :=
      (hT'gen t t.property).1
    have hxt' : x ∈ chapter03BasicProductSet H (U t) := by
      rw [hUt t]
      exact hxt
    exact hxt' i
  have hWs : chapter03BasicProductSet H W ⊆ n := by
    intro y hy
    apply hT'sub
    simp only [mem_iInter]
    intro t ht
    have hy' : y ∈ chapter03BasicProductSet H (U ⟨t, ht⟩) := by
      intro i
      have hyW : ((y : ∀ i, G i) i) ∈ W i :=
        (chapter03_mem_basicProductSet_iff H W y).1 hy i
      exact (mem_iInter.1 hyW) ⟨t, ht⟩
    simpa only [hUt ⟨t, ht⟩] using hy'
  obtain ⟨K, hKcompact, hKnhds, hKW⟩ :=
    chapter03_compact_subset_basicProduct H hlocal hcompact hopen W hW x hxW
  exact ⟨K, hKnhds, hKW.trans hWs, hKcompact⟩

private def chapter03AdditiveStageSubgroup
    {G : I → Type v} [∀ i, AddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i)) (S : Set I) :
    AddSubgroup (Chapter03AdditiveRestrictedProduct H) where
  carrier := {x | ∀ i, i ∉ S → (x : ∀ i, G i) i ∈ H i}
  zero_mem' := by
    intro i hi
    exact (H i).zero_mem
  add_mem' := by
    intro x y hx hy i hi
    exact (H i).add_mem (hx i hi) (hy i hi)
  neg_mem' := by
    intro x hx i hi
    exact (H i).neg_mem (hx i hi)

private abbrev chapter03AdditiveStage
    {G : I → Type v} [∀ i, AddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i)) (S : Set I) :=
  chapter03AdditiveStageSubgroup H S

@[instance_reducible]
private def chapter03AdditiveStageProductTopology
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i)) (S : Set I) :
    TopologicalSpace (chapter03AdditiveStage H S) :=
  TopologicalSpace.induced
    (fun x : chapter03AdditiveStage H S =>
      ((x : chapter03AdditiveStage H S).1 : ∀ i, G i)) inferInstance

@[instance_reducible]
private def chapter03AdditiveStageSubtypeTopology
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i)) (S : Set I) :
    TopologicalSpace (chapter03AdditiveStage H S) :=
  TopologicalSpace.induced
    (fun x : chapter03AdditiveStage H S =>
      (x : Chapter03AdditiveRestrictedProduct H))
    inferInstance

private theorem chapter03_additive_stage_subtype_topology_eq_product_topology
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i)) {S : Set I} (hS : S.Finite)
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    chapter03AdditiveStageSubtypeTopology H S =
      chapter03AdditiveStageProductTopology H S := by
  classical
  change TopologicalSpace.induced
      (fun x : chapter03AdditiveStage H S =>
        (x : Chapter03AdditiveRestrictedProduct H))
      (chapter03AdditiveRestrictedProductTopology H) =
    TopologicalSpace.induced
      (fun x : chapter03AdditiveStage H S =>
        ((x : chapter03AdditiveStage H S).1 : ∀ i, G i)) inferInstance
  apply le_antisymm
  · rw [← continuous_iff_le_induced]
    apply continuous_pi
    intro i
    rw [continuous_def]
    intro U hU
    let W : ∀ j, Set (G j) := fun j =>
      if hji : j = i then hji ▸ U
      else if j ∈ S then Set.univ else (H j : Set (G j))
    have hW : chapter03AdditiveBasicProductCondition H W := by
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          simpa [W] using hU
        · by_cases hjS : j ∈ S
          · simp [W, hji, hjS]
          · simpa [W, hji, hjS] using hH j
      · filter_upwards [hS.compl_mem_cofinite, eventually_cofinite_ne i] with j hjS hji
        have hjS' : j ∉ S := by simpa using hjS
        simp [W, hjS', hji]
    have hset :
        (fun x : chapter03AdditiveStage H S =>
            ((x : chapter03AdditiveStage H S).1 : ∀ i, G i) i) ⁻¹' U =
          (fun x : chapter03AdditiveStage H S =>
            (x : Chapter03AdditiveRestrictedProduct H)) ⁻¹'
            chapter03AdditiveBasicProductSet H W := by
      ext x
      constructor
      · intro hx
        change ∀ j, ((x : chapter03AdditiveStage H S).1 : ∀ i, G i) j ∈ W j
        intro j
        by_cases hji : j = i
        · subst j
          simpa [W] using hx
        · by_cases hjS : j ∈ S
          · simp [W, hji, hjS]
          · simpa [W, hji, hjS] using x.2 j hjS
      · intro hx
        change ((x : chapter03AdditiveStage H S).1 : ∀ i, G i) i ∈ U
        have hxi := hx i
        simpa [W] using hxi
    rw [hset]
    exact isOpen_induced (chapter03_additive_basicProductSet_isOpen H W hW)
  · rw [← continuous_iff_le_induced]
    rw [continuous_generateFrom_iff]
    rintro _ ⟨U, hU, rfl⟩
    have hE : {i | U i ≠ (H i : Set (G i))}.Finite := by
      exact Filter.eventually_cofinite.mp hU.2
    let K : Set I := S ∪ {i | U i ≠ (H i : Set (G i))}
    have hK : K.Finite := hS.union hE
    let V : ∀ i, Set (G i) := fun i => if i ∈ K then U i else Set.univ
    have hV : IsOpen (Set.pi Set.univ V) := by
      rw [show Set.pi Set.univ V = Set.pi K V by
        ext x
        constructor
        · intro hx i hi
          exact hx i (by simp)
        · intro hx i hi
          by_cases hiK : i ∈ K
          · exact hx i hiK
          · simp [V, hiK]]
      apply isOpen_set_pi hK
      intro i hi
      by_cases hiK : i ∈ K
      · simpa [V, hiK] using hU.1 i
      · simp [V, hiK]
    have hset :
        (fun x : chapter03AdditiveStage H S =>
            (x : Chapter03AdditiveRestrictedProduct H)) ⁻¹'
            chapter03AdditiveBasicProductSet H U =
          (fun x : chapter03AdditiveStage H S =>
            ((x : chapter03AdditiveStage H S).1 : ∀ i, G i)) ⁻¹'
            Set.pi Set.univ V := by
      ext x
      constructor
      · intro hx
        simp only [Set.mem_preimage, Set.mem_pi, mem_univ, true_implies]
        intro i
        by_cases hiK : i ∈ K
        · simpa [V, hiK] using hx i
        · simp [V, hiK]
      · intro hx
        change ∀ i, ((x : chapter03AdditiveStage H S).1 : ∀ i, G i) i ∈ U i
        intro i
        by_cases hiK : i ∈ K
        · simpa [V, hiK] using hx i
        · have hiS : i ∉ S := by
            intro hiS
            exact hiK (Or.inl hiS)
          have hiE : U i = (H i : Set (G i)) := by
            by_contra hne
            exact hiK (Or.inr hne)
          simpa [hiE] using x.2 i hiS
    rw [hset]
    exact isOpen_induced hV

private theorem chapter03_additive_compact_subset_basicProduct
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i)))
    (U : ∀ i, Set (G i))
    (hU : chapter03AdditiveBasicProductCondition H U)
    (x : Chapter03AdditiveRestrictedProduct H)
    (hx : x ∈ chapter03AdditiveBasicProductSet H U) :
    ∃ K : Set (Chapter03AdditiveRestrictedProduct H),
      IsCompact K ∧ K ∈ 𝓝 x ∧
        K ⊆ chapter03AdditiveBasicProductSet H U := by
  classical
  let E : Set I := {i | U i ≠ (H i : Set (G i))}
  have hE : E.Finite := by
    exact Filter.eventually_cofinite.mp hU.2
  have hKdata : ∀ i, ∃ K : Set (G i),
      (i ∈ E → IsCompact K ∧ K ∈ 𝓝 ((x : ∀ i, G i) i) ∧ K ⊆ U i) ∧
        (i ∉ E → K = (H i : Set (G i))) := by
    intro i
    by_cases hi : i ∈ E
    · obtain ⟨K, hKnhds, hKsub, hKcompact⟩ :=
        (hlocal i).local_compact_nhds ((x : ∀ i, G i) i) (U i)
          ((hU.1 i).mem_nhds (hx i))
      exact ⟨K, fun _ => ⟨hKcompact, hKnhds, hKsub⟩, fun h => (h hi).elim⟩
    · refine ⟨(H i : Set (G i)), ?_, fun _ => rfl⟩
      exact fun hiE => (hi hiE).elim
  choose K hKdata using hKdata
  have hKcompact : ∀ i, IsCompact (K i) := by
    intro i
    by_cases hi : i ∈ E
    · exact (hKdata i).1 hi |>.1
    · rw [(hKdata i).2 hi]
      exact hcompact i
  have hKtail : ∀ i, i ∉ E → K i = (H i : Set (G i)) := fun i => (hKdata i).2
  have hKsubset : ∀ i, i ∈ E → K i ⊆ U i := by
    intro i hi
    exact (hKdata i).1 hi |>.2.2
  have hKnhds : ∀ i, i ∈ E → K i ∈ 𝓝 ((x : ∀ i, G i) i) := by
    intro i hi
    exact (hKdata i).1 hi |>.2.1
  have hVdata : ∀ i, ∃ V : Set (G i),
      IsOpen V ∧ ((x : ∀ i, G i) i ∈ V) ∧ V ⊆ K i ∧
        (i ∉ E → V = (H i : Set (G i))) := by
    intro i
    by_cases hi : i ∈ E
    · rcases mem_nhds_iff.mp (hKnhds i hi) with ⟨V, hVK, hVopen, hxV⟩
      exact ⟨V, hVopen, hxV, hVK, fun h => (h hi).elim⟩
    · refine ⟨(H i : Set (G i)), hopen i, ?_, ?_, fun _ => rfl⟩
      · have hUeq : U i = (H i : Set (G i)) := by
          by_contra hne
          exact hi (by simpa [E] using hne)
        have hxiH : ((x : ∀ i, G i) i) ∈ H i := by
          simpa [hUeq] using hx i
        exact hxiH
      · rw [hKtail i hi]
  choose V hVopen hxV hVK hVtail using hVdata
  have hVcond : chapter03AdditiveBasicProductCondition H V := by
    constructor
    · exact hVopen
    · filter_upwards [hE.compl_mem_cofinite] with i hi
      exact hVtail i (by simpa [E] using hi)
  have hBopen : IsOpen (chapter03AdditiveBasicProductSet H V) :=
    chapter03_additive_basicProductSet_isOpen H V hVcond
  have hxB : x ∈ chapter03AdditiveBasicProductSet H V := by
    intro i
    exact hxV i
  let T := chapter03AdditiveStage H E
  let e : T → ∀ i, G i :=
    fun y => ((y : T).1 : ∀ i, G i)
  let Q : Set T := e ⁻¹' Set.pi Set.univ K
  have heimage : e '' Q = Set.pi Set.univ K := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      have hyH : ∀ᶠ i in Filter.cofinite, y i ∈ H i := by
        filter_upwards [hE.compl_mem_cofinite] with i hi
        have hiE : i ∉ E := by simpa [E] using hi
        have hyK : y i ∈ K i := hy i (by simp)
        simpa [hKtail i hiE] using hyK
      let z : Chapter03AdditiveRestrictedProduct H := ⟨y, hyH⟩
      have hzE : z ∈ chapter03AdditiveStageSubgroup H E := by
        intro i hi
        have hyK : y i ∈ K i := hy i (by simp)
        change y i ∈ H i
        simpa [hKtail i hi] using hyK
      let t : T := ⟨z, hzE⟩
      exact ⟨t, hy, rfl⟩
  have hQcompact : @IsCompact T (chapter03AdditiveStageProductTopology H E) Q := by
    let _ : TopologicalSpace T := chapter03AdditiveStageProductTopology H E
    have hemb : Topology.IsEmbedding e := by
      refine { eq_induced := rfl, injective := ?_ }
      intro y z h
      apply Subtype.ext
      apply chapter03_additiveRestrictedProduct_ext H
      intro i
      exact congrFun h i
    rw [hemb.isCompact_iff, heimage]
    exact isCompact_univ_pi hKcompact
  have hQcompact' : @IsCompact T (chapter03AdditiveStageSubtypeTopology H E) Q := by
    rw [chapter03_additive_stage_subtype_topology_eq_product_topology H hE hopen]
    exact hQcompact
  let j : T → Chapter03AdditiveRestrictedProduct H := fun y => y.1
  have hj : @Topology.IsEmbedding T (Chapter03AdditiveRestrictedProduct H)
      (chapter03AdditiveStageSubtypeTopology H E)
      (chapter03AdditiveRestrictedProductTopology H) j := by
    refine { eq_induced := rfl, injective := ?_ }
    intro y z h
    exact Subtype.ext h
  let K' : Set (Chapter03AdditiveRestrictedProduct H) := j '' Q
  have hK'compact : IsCompact K' := by
    exact (hj.isCompact_iff (s := Q)).1 hQcompact'
  have hBsub : chapter03AdditiveBasicProductSet H V ⊆ K' := by
    intro y hy
    have hyE : y ∈ chapter03AdditiveStageSubgroup H E := by
      intro i hi
      simpa [hVtail i hi] using hy i
    let z : T := ⟨y, hyE⟩
    have hzQ : z ∈ Q := by
      intro i _
      simpa [e, z] using hVK i (hy i)
    exact ⟨z, hzQ, rfl⟩
  have hKsubset' : K' ⊆ chapter03AdditiveBasicProductSet H U := by
    rintro y ⟨z, hzQ, rfl⟩
    intro i
    by_cases hi : i ∈ E
    · exact hKsubset i hi (by simpa [e] using hzQ i (by simp))
    · have hzH : ((z : T).1 : ∀ i, G i) i ∈ H i := z.2 i hi
      have hUeq : U i = (H i : Set (G i)) := by
        by_contra hne
        exact hi (by simpa [E] using hne)
      simpa [j, hUeq] using hzH
  refine ⟨K', hK'compact, ?_, hKsubset'⟩
  exact mem_of_superset (hBopen.mem_nhds hxB) hBsub

theorem chapter03_additive_distinguishedTail_is_compact_open
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i))) :
    IsCompact (chapter03AdditiveDistinguishedTail H) ∧
      IsOpen (chapter03AdditiveDistinguishedTail H) := by
  classical
  let U : ∀ i, Set (G i) := fun i => (H i : Set (G i))
  have hU : chapter03AdditiveBasicProductCondition H U := by
    constructor
    · exact hopen
    · exact Filter.Eventually.of_forall (fun i => rfl)
  have hUset : chapter03AdditiveBasicProductSet H U =
      chapter03AdditiveDistinguishedTail H := by
    ext x
    rfl
  have hopenTail : IsOpen (chapter03AdditiveDistinguishedTail H) := by
    rw [← hUset]
    exact chapter03_additive_basicProductSet_isOpen H U hU
  let T := chapter03AdditiveStage H (∅ : Set I)
  let e : T → ∀ i, G i :=
    fun x => ((x : T).1 : ∀ i, G i)
  let j : T → Chapter03AdditiveRestrictedProduct H := fun x => x.1
  have heimage : e '' (Set.univ : Set T) =
      Set.pi Set.univ (fun i => (H i : Set (G i))) := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      intro i hi
      exact x.2 i (by simp)
    · intro hy
      have hyH : ∀ᶠ i in Filter.cofinite, y i ∈ H i :=
        Filter.Eventually.of_forall (fun i => hy i (by simp))
      let z : Chapter03AdditiveRestrictedProduct H := ⟨y, hyH⟩
      have hz : z ∈ chapter03AdditiveStageSubgroup H (∅ : Set I) := by
        intro i hi
        simpa [z] using hy i (by simp)
      let x : T := ⟨z, hz⟩
      exact ⟨x, Set.mem_univ x, rfl⟩
  have hcompactProd :
      @IsCompact T (chapter03AdditiveStageProductTopology H (∅ : Set I))
        (Set.univ : Set T) := by
    let _ : TopologicalSpace T :=
      chapter03AdditiveStageProductTopology H (∅ : Set I)
    have hemb : Topology.IsEmbedding e := by
      refine { eq_induced := rfl, injective := ?_ }
      intro x y hxy
      apply Subtype.ext
      apply chapter03_additiveRestrictedProduct_ext H
      intro i
      exact congrFun hxy i
    rw [hemb.isCompact_iff, heimage]
    exact isCompact_univ_pi hcompact
  have hcompactSub :
      @IsCompact T (chapter03AdditiveStageSubtypeTopology H (∅ : Set I))
        (Set.univ : Set T) := by
    rw [chapter03_additive_stage_subtype_topology_eq_product_topology H
      Set.finite_empty hopen]
    exact hcompactProd
  have hj : @Topology.IsEmbedding T
      (Chapter03AdditiveRestrictedProduct H)
      (chapter03AdditiveStageSubtypeTopology H (∅ : Set I))
      (chapter03AdditiveRestrictedProductTopology H) j := by
    refine { eq_induced := rfl, injective := ?_ }
    intro x y hxy
    exact Subtype.ext hxy
  have hjimage : j '' (Set.univ : Set T) =
      chapter03AdditiveDistinguishedTail H := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      intro i
      exact y.2 i (by simp)
    · intro hx
      have hxS : x ∈ chapter03AdditiveStageSubgroup H (∅ : Set I) := by
        intro i hi
        exact hx i
      let y : T := ⟨x, hxS⟩
      exact ⟨y, Set.mem_univ y, rfl⟩
  have himagecompact : IsCompact (j '' (Set.univ : Set T)) :=
    (hj.isCompact_iff (s := (Set.univ : Set T))).1 hcompactSub
  rw [hjimage] at himagecompact
  exact ⟨himagecompact, hopenTail⟩

theorem chapter03_additive_restrictedProduct_locallyCompact
    {G : I → Type v} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hopen : ∀ i, IsOpen (H i : Set (G i))) :
    LocallyCompactSpace (Chapter03AdditiveRestrictedProduct H) := by
  classical
  refine ⟨?_⟩
  intro x n hn
  change n ∈ @nhds _ (chapter03AdditiveRestrictedProductTopology H) x at hn
  rw [TopologicalSpace.nhds_generateFrom] at hn
  rcases (Filter.mem_biInf_principal.mp hn) with ⟨T, hTfin, hTgen, hTsub⟩
  let Sx : Set I := {i | ((x : ∀ i, G i) i) ∉ H i}
  have hSx : Sx.Finite := by
    exact Filter.eventually_cofinite.mp x.property
  let U₀ : ∀ i, Set (G i) := fun i =>
    if i ∈ Sx then Set.univ else (H i : Set (G i))
  have hU₀ : chapter03AdditiveBasicProductCondition H U₀ := by
    constructor
    · intro i
      by_cases hi : i ∈ Sx
      · simp [U₀, hi]
      · simpa [U₀, hi] using hopen i
    · filter_upwards [hSx.compl_mem_cofinite] with i hi
      have hi' : i ∉ Sx := by simpa using hi
      simp [U₀, hi']
  have hU₀eq : chapter03AdditiveBasicProductSet H U₀ =
      (chapter03AdditiveStageSubgroup H Sx :
        Set (Chapter03AdditiveRestrictedProduct H)) := by
    ext y
    change (∀ i, ((y : ∀ i, G i) i) ∈ U₀ i) ↔
      ∀ i, i ∉ Sx → ((y : ∀ i, G i) i) ∈ H i
    constructor
    · intro hy i hi
      simpa [U₀, hi] using hy i
    · intro hy i
      by_cases hi : i ∈ Sx
      · simp [U₀, hi]
      · simpa [U₀, hi] using hy i hi
  let b₀ : Set (Chapter03AdditiveRestrictedProduct H) :=
    chapter03AdditiveBasicProductSet H U₀
  have hb₀ : b₀ ∈ chapter03AdditiveBasicOpenSets H := ⟨U₀, hU₀, rfl⟩
  have hxb₀ : x ∈ b₀ := by
    change x ∈ chapter03AdditiveBasicProductSet H U₀
    rw [hU₀eq]
    intro i hi
    exact not_not.mp (by
      intro hne
      exact hi (by simpa [Sx] using hne))
  let T' : Set (Set (Chapter03AdditiveRestrictedProduct H)) := insert b₀ T
  have hT'fin : T'.Finite := hTfin.insert b₀
  have hT'gen : ∀ t ∈ T', t ∈
      {s | x ∈ s ∧ s ∈ chapter03AdditiveBasicOpenSets H} := by
    intro t ht
    simp only [T', mem_insert_iff] at ht
    rcases ht with rfl | ht
    · exact ⟨hxb₀, hb₀⟩
    · exact hTgen t ht
  have hT'sub : (⋂ t ∈ T', t) ⊆ n := by
    intro y hy
    apply hTsub
    simp only [mem_iInter] at hy ⊢
    intro t ht
    exact hy t (by simp [T', ht])
  have hbasic : ∀ t ∈ T', ∃ U : ∀ i, Set (G i),
      chapter03AdditiveBasicProductCondition H U ∧
        chapter03AdditiveBasicProductSet H U = t := by
    intro t ht
    rcases (hT'gen t ht).2 with ⟨U, hU, rfl⟩
    exact ⟨U, hU, rfl⟩
  let _ : Fintype T' := hT'fin.fintype
  choose U hU hUt using (fun t : T' => hbasic t t.property)
  let W : ∀ i, Set (G i) := fun i => ⋂ t : T', U t i
  have hW : chapter03AdditiveBasicProductCondition H W := by
    constructor
    · intro i
      exact isOpen_iInter_of_finite (fun t => (hU t).1 i)
    · have he : ∀ᶠ i in Filter.cofinite, ∀ t : T', U t i = (H i : Set (G i)) :=
        (Filter.eventually_all).2 fun t => (hU t).2
      filter_upwards [he] with i hi
      ext y
      simp only [W, mem_iInter]
      let t₀ : T' := ⟨b₀, by simp [T']⟩
      constructor
      · intro hy
        rw [← hi t₀]
        exact hy t₀
      · intro hy t
        rw [hi t]
        exact hy
  have hxW : x ∈ chapter03AdditiveBasicProductSet H W := by
    intro i
    simp only [W, mem_iInter]
    intro t
    have hxt : x ∈ (t : Set (Chapter03AdditiveRestrictedProduct H)) :=
      (hT'gen t t.property).1
    have hxt' : x ∈ chapter03AdditiveBasicProductSet H (U t) := by
      rw [hUt t]
      exact hxt
    exact hxt' i
  have hWs : chapter03AdditiveBasicProductSet H W ⊆ n := by
    intro y hy
    apply hT'sub
    simp only [mem_iInter]
    intro t ht
    have hy' : y ∈ chapter03AdditiveBasicProductSet H (U ⟨t, ht⟩) := by
      intro i
      have hyW : ((y : ∀ i, G i) i) ∈ W i :=
        (chapter03_mem_additiveBasicProductSet_iff H W y).1 hy i
      exact (mem_iInter.1 hyW) ⟨t, ht⟩
    simpa only [hUt ⟨t, ht⟩] using hy'
  obtain ⟨K, hKcompact, hKnhds, hKW⟩ :=
    chapter03_additive_compact_subset_basicProduct H hlocal hcompact hopen W hW x hxW
  exact ⟨K, hKnhds, hKW.trans hWs, hKcompact⟩

/-- Infinitely many noncompact coordinates obstruct local compactness of the
unrestricted product. -/
def chapter03InfinitelyManyNoncompactFactors
    [∀ i, TopologicalSpace (G i)] : Prop :=
  {i | ¬ IsCompact (Set.univ : Set (G i))}.Infinite

theorem chapter03_unrestrictedProduct_not_locallyCompact
    [∀ i, TopologicalSpace (G i)]
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hhausdorff : ∀ i, T2Space (G i))
    (hinfinite : chapter03InfinitelyManyNoncompactFactors (G := G)) :
    ¬ LocallyCompactSpace (∀ i, G i) := by
  classical
  intro hfull
  let _ : LocallyCompactSpace (∀ i, G i) := hfull
  obtain ⟨K, hKcompact, hKnhds⟩ := exists_compact_mem_nhds (1 : ∀ i, G i)
  rw [nhds_pi, Filter.mem_pi'] at hKnhds
  rcases hKnhds with ⟨S, V, hV, hSK⟩
  have hcompact_of_not_mem : ∀ i, i ∉ S → IsCompact (Set.univ : Set (G i)) := by
    intro i hiS
    let _ : LocallyCompactSpace (G i) := hlocal i
    let _ : T2Space (G i) := hhausdorff i
    have himage : (fun x : (∀ j, G j) => x i) '' K = (Set.univ : Set (G i)) := by
      apply Set.eq_univ_of_forall
      intro g
      let y : ∀ j, G j := Function.update (fun _ => 1) i g
      have hyS : y ∈ Set.pi (↑S : Set I) V := by
        intro j hj
        have hji : j ≠ i := by
          intro hji
          subst j
          exact hiS hj
        have hVj : V j ∈ 𝓝 (1 : G j) := hV j
        have honeV : (1 : G j) ∈ V j := mem_of_mem_nhds hVj
        simpa [y, hji] using honeV
      have hyK : y ∈ K := hSK hyS
      exact ⟨y, hyK, by simp [y]⟩
    have hcompactImage : IsCompact ((fun x : (∀ j, G j) => x i) '' K) :=
      hKcompact.image (continuous_apply i)
    rwa [himage] at hcompactImage
  change {i | ¬ IsCompact (Set.univ : Set (G i))}.Infinite at hinfinite
  have hnoncompact_subset :
      {i | ¬ IsCompact (Set.univ : Set (G i))} ⊆ (S : Set I) := by
    intro i hi
    by_contra hiS
    exact hi (hcompact_of_not_mem i hiS)
  have hnoncompact_finite : {i | ¬ IsCompact (Set.univ : Set (G i))}.Finite :=
    S.finite_toSet.subset hnoncompact_subset
  exact hinfinite hnoncompact_finite

section DirectSumWarning

variable {A : Type v} [∀ i, AddGroup (G i)]

/-- The finite-support additive subgroup, used here as the direct-sum model. -/
def chapter03FiniteSupportAddSubgroup : AddSubgroup (∀ i, G i) where
  carrier := {x | {i | x i ≠ 0}.Finite}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    refine (hx.union hy).subset ?_
    intro i hi
    by_cases hxi : x i ≠ 0
    · exact Or.inl hxi
    by_cases hyi : y i ≠ 0
    · exact Or.inr hyi
    · exfalso
      apply hi
      have hxi_zero : x i = 0 := not_ne_iff.mp hxi
      have hyi_zero : y i = 0 := not_ne_iff.mp hyi
      simp [hxi_zero, hyi_zero]
  neg_mem' := by
    intro x hx
    simpa using hx

abbrev Chapter03DirectSum := chapter03FiniteSupportAddSubgroup (G := G)

omit [(i : I) → Group (G i)] in
theorem chapter03_directSum_contains_additive_identity :
    chapter03AdditiveZeroFamily ∈ Chapter03DirectSum (G := G) := by
  exact (chapter03FiniteSupportAddSubgroup (G := G)).zero_mem

omit [(i : I) → Group (G i)] in
theorem chapter03_directSum_mem_iff_finite_support (x : ∀ i, G i) :
    x ∈ Chapter03DirectSum (G := G) ↔ {i | x i ≠ 0}.Finite :=
  Iff.rfl

omit [(i : I) → Group (G i)] in
theorem chapter03_directSum_excludes_infinite_support
    (x : ∀ i, G i) (hinfinite : {i | x i ≠ 0}.Infinite) :
    x ∉ Chapter03DirectSum (G := G) := by
  exact fun hx => hinfinite
    ((chapter03_directSum_mem_iff_finite_support x).mp hx)

/-!
The direct-sum comparison is additive: its zero family is the additive
identity and is finitely supported, whereas a diagonal family with infinitely
many nonzero coordinates is excluded.  In particular, the all-ones family is
excluded from the additive direct sum of nontrivial rings, so that additive
direct sum is not unital as a subring of the product.
-/
omit [(i : I) → Group (G i)] in
theorem chapter03_directSum_diagonal_family_excluded_when_support_infinite
    (diagonal : A → ∀ i, G i) (a : A)
    (hinfinite : {i | diagonal a i ≠ 0}.Infinite) :
    diagonal a ∉ Chapter03DirectSum (G := G) := by
  exact chapter03_directSum_excludes_infinite_support _ hinfinite

end DirectSumWarning

end RestrictedProductLocalCompactness

end
end LastLib.Book04AdelesAndIdeles.Chapter03
