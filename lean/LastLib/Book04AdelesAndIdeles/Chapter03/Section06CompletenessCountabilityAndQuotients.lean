import LastLib.Book04AdelesAndIdeles.Chapter03.Section05RestrictedProductsAsIncreasingUnions
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Set.FiniteExhaustion
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Order.Filter.CountablyGenerated
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.UniformSpace.Cauchy

namespace LastLib.Book04AdelesAndIdeles.Chapter03

open Set Filter Function TopologicalSpace
open scoped BigOperators Pointwise Topology Uniformity

noncomputable section

/-! ### 3.6 Completeness, countability, and quotients -/

universe u v

section Countability

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

theorem chapter03_restrictedProduct_metrizable
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (H : ∀ i, Subgroup (G i))
    [Countable I]
    (hmetric : ∀ i, MetrizableSpace (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    MetrizableSpace (Chapter03RestrictedProduct H) := by
  classical
  let _ : ∀ i, MetrizableSpace (G i) := hmetric
  let _ : ∀ i, FirstCountableTopology (G i) := by infer_instance
  choose B hB using fun i => Filter.exists_antitone_basis (𝓝 (1 : G i))
  let K : Set.FiniteExhaustion (Set.univ : Set I) :=
    Set.Countable.finiteExhaustion Set.countable_univ
  let E : Chapter03StageExhaustion I :=
    { stage := K
      finite := fun n => K.finite n
      mono := fun m n hmn => K.mono hmn
      exhaustive := by
        intro i
        have hi : i ∈ ⋃ n, K n := by
          rw [K.iUnion_eq]
          exact Set.mem_univ i
        rcases Set.mem_iUnion.1 hi with ⟨n, hn⟩
        exact ⟨n, hn⟩ }
  have hOdata : ∀ i n, ∃ O : Set (G i), IsOpen O ∧
      (1 : G i) ∈ O ∧ O ⊆ B i n := by
    intro i n
    rcases mem_nhds_iff.mp ((hB i).mem n) with ⟨O, hOB, hOopen, hOone⟩
    exact ⟨O, hOopen, hOone, hOB⟩
  choose O hOopen hOone hOB using hOdata
  let Q : ℕ → ℕ → Set (Chapter03RestrictedProduct H) := fun m n =>
    chapter03BasicProductSet H (fun i =>
      if i ∈ E.stage m then B i n else (H i : Set (G i)))
  have hQmem : ∀ m n, Q m n ∈ 𝓝 (1 : Chapter03RestrictedProduct H) := by
    intro m n
    let W : ∀ i, Set (G i) := fun i =>
      if i ∈ E.stage m then O i n else (H i : Set (G i))
    have hWcond : chapter03BasicProductCondition H W := by
      constructor
      · intro i
        by_cases hi : i ∈ E.stage m
        · simpa [W, hi] using hOopen i n
        · simpa [W, hi] using hH i
      · filter_upwards [(E.finite m).compl_mem_cofinite] with i hi
        have hi' : i ∉ E.stage m := by simpa using hi
        simp [W, hi']
    have hWopen : IsOpen (chapter03BasicProductSet H W) :=
      chapter03_basicProductSet_isOpen_of_condition H W hWcond
    have hWone : (1 : Chapter03RestrictedProduct H) ∈
        chapter03BasicProductSet H W := by
      change ∀ i, (1 : G i) ∈ W i
      intro i
      by_cases hi : i ∈ E.stage m
      · simpa [W, hi] using hOone i n
      · simp [W, hi]
    have hWsub : chapter03BasicProductSet H W ⊆ Q m n := by
      intro x hx
      change ∀ i, ((x : ∀ i, G i) i) ∈ W i at hx
      change ∀ i, ((x : ∀ i, G i) i) ∈
        (if i ∈ E.stage m then B i n else (H i : Set (G i)))
      intro i
      by_cases hi : i ∈ E.stage m
      · simpa [hi] using hOB i n (by simpa [W, hi] using hx i)
      · simpa [W, hi] using hx i
    exact mem_of_superset (hWopen.mem_nhds hWone) hWsub
  have hnhds : 𝓝 (1 : Chapter03RestrictedProduct H) =
      ⨅ m : ℕ, ⨅ n : ℕ, 𝓟 (Q m n) := by
    change @nhds (Chapter03RestrictedProduct H)
      (chapter03RestrictedProductTopology H) 1 = _
    rw [TopologicalSpace.nhds_generateFrom]
    apply le_antisymm
    · refine le_iInf fun m => le_iInf fun n => ?_
      apply le_principal_iff.2
      have hQmem' := hQmem m n
      rw [TopologicalSpace.nhds_generateFrom] at hQmem'
      exact hQmem'
    · refine le_iInf fun s => le_iInf fun hs => ?_
      change 1 ∈ s ∧ s ∈ chapter03BasicOpenSets H at hs
      rcases hs with ⟨hsone, ⟨U, hU, rfl⟩⟩
      have hUfinite : {i | U i ≠ (H i : Set (G i))}.Finite := by
        simpa only [Filter.eventually_cofinite, not_not] using hU.2
      have hUeq : ∀ i, i ∉ {i | U i ≠ (H i : Set (G i))} →
          U i = (H i : Set (G i)) := by
        intro i hi
        by_contra hne
        exact hi (by simpa using hne)
      let m : ℕ := hUfinite.toFinset.sup (fun i => (E.exhaustive i).choose)
      have hUstage : {i | U i ≠ (H i : Set (G i))} ⊆ E.stage m := by
        intro i hi
        exact E.mono (Finset.le_sup (hUfinite.mem_toFinset.mpr hi))
          (E.exhaustive i).choose_spec
      have hNdata : ∀ i, ∃ n, B i n ⊆ U i := by
        intro i
        apply (hB i).mem_iff.mp
        exact (hU.1 i).mem_nhds (hsone i)
      choose N hN using hNdata
      let n : ℕ := (E.finite m).toFinset.sup (fun i => N i)
      have hQsub : Q m n ⊆ chapter03BasicProductSet H U := by
        intro x hx
        change ∀ i, ((x : ∀ i, G i) i) ∈
          (if i ∈ E.stage m then B i n else (H i : Set (G i))) at hx
        change ∀ i, ((x : ∀ i, G i) i) ∈ U i
        intro i
        by_cases hi : i ∈ E.stage m
        · have hiF : i ∈ (E.finite m).toFinset :=
            (E.finite m).mem_toFinset.mpr hi
          have hNi : N i ≤ n := by
            exact Finset.le_sup (s := (E.finite m).toFinset)
              (f := fun j => N j) hiF
          exact hN i ((hB i).antitone hNi (by simpa [hi] using hx i))
        · have hiF : i ∉ {i | U i ≠ (H i : Set (G i))} := by
            intro hiF
            exact hi (hUstage hiF)
          simpa [hUeq i hiF, hi] using hx i
      exact le_trans
        (iInf_le_of_le m (iInf_le_of_le n (le_refl _)))
        (principal_mono.2 hQsub)
  have hnhdsCG : (𝓝 (1 : Chapter03RestrictedProduct H)).IsCountablyGenerated := by
    rw [hnhds]
    infer_instance
  let _ : IsTopologicalGroup (Chapter03RestrictedProduct H) :=
    chapter03_restrictedProduct_is_topologicalGroup H hH
  have hsep : ∀ x : Chapter03RestrictedProduct H, x ≠ 1 →
      ∃ U ∈ 𝓝 (1 : Chapter03RestrictedProduct H), x ∉ U := by
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, ((x : ∀ i, G i) i) ≠ 1 := by
      by_contra hxi
      apply hx
      apply chapter03_restrictedProduct_ext H
      intro i
      have hxi' : ((x : ∀ i, G i) i) = 1 := by
        by_contra hne
        exact hxi ⟨i, hne⟩
      simpa using hxi'
    rcases t2_separation_nhds hi with ⟨u, v, hu, hv, huv⟩
    rcases mem_nhds_iff.mp hv with ⟨w, hwv, hwopen, hwone⟩
    let V : ∀ j, Set (G j) := fun j =>
      if hji : j = i then hji ▸ w else (H j : Set (G j))
    have hVcond : chapter03BasicProductCondition H V := by
      constructor
      · intro j
        by_cases hji : j = i
        · subst j
          simpa [V] using hwopen
        · simpa [V, hji] using hH j
      · filter_upwards [eventually_cofinite_ne i] with j hji
        simp [V, hji]
    have honeV : (1 : Chapter03RestrictedProduct H) ∈
        chapter03BasicProductSet H V := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [V] using hwone
      · simp [V, hji]
    have hxnot : x ∉ chapter03BasicProductSet H V := by
      intro hxV
      have hxiw : ((x : ∀ i, G i) i) ∈ w := by
        simpa [V] using hxV i
      exact Set.disjoint_left.1 huv (mem_of_mem_nhds hu) (hwv hxiw)
    refine ⟨chapter03BasicProductSet H V, ?_, hxnot⟩
    exact (chapter03_basicProductSet_isOpen_of_condition H V hVcond).mem_nhds honeV
  let _ : T2Space (Chapter03RestrictedProduct H) :=
    IsTopologicalGroup.t2Space_of_one_sep hsep
  let u : UniformSpace (Chapter03RestrictedProduct H) :=
    IsTopologicalGroup.rightUniformSpace (Chapter03RestrictedProduct H)
  let _ : UniformSpace (Chapter03RestrictedProduct H) := u
  let _ : IsCountablyGenerated (𝓝 (1 : Chapter03RestrictedProduct H)) := hnhdsCG
  have huniform : (𝓤 (Chapter03RestrictedProduct H)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_one']
    infer_instance
  let _ : IsCountablyGenerated (𝓤 (Chapter03RestrictedProduct H)) := huniform
  infer_instance

theorem chapter03_restrictedProduct_secondCountable
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [Countable I]
    (hsecond : ∀ i, SecondCountableTopology (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    SecondCountableTopology (Chapter03RestrictedProduct H) := by
  classical
  let _ : ∀ i, SecondCountableTopology (G i) := hsecond
  let K : Set.FiniteExhaustion (Set.univ : Set I) :=
    Set.Countable.finiteExhaustion Set.countable_univ
  let E : Chapter03StageExhaustion I :=
    { stage := K
      finite := fun n => K.finite n
      mono := fun m n hmn => K.mono hmn
      exhaustive := by
        intro i
        have hi : i ∈ ⋃ n, K n := by
          rw [K.iUnion_eq]
          exact Set.mem_univ i
        rcases Set.mem_iUnion.1 hi with ⟨n, hn⟩
        exact ⟨n, hn⟩ }
  let U : ℕ → Set (Chapter03RestrictedProduct H) := fun n =>
    (chapter03StageSubgroup H (E.stage n) : Set (Chapter03RestrictedProduct H))
  have hUopen : ∀ n, IsOpen (U n) := by
    intro n
    exact chapter03_stage_isOpen H (E.finite n) hH
  have hUsecond : ∀ n, SecondCountableTopology (U n) := by
    intro n
    change @SecondCountableTopology (Chapter03Stage H (E.stage n))
      (chapter03StageSubtypeTopology H (E.stage n))
    rw [chapter03_stage_subtype_topology_eq_product_topology H (E.finite n) hH]
    exact TopologicalSpace.secondCountableTopology_induced
      (Chapter03Stage H (E.stage n)) (∀ i, G i)
      (fun x => ((x : Chapter03Stage H (E.stage n)).1 : ∀ i, G i))
  let _ : ∀ n, SecondCountableTopology (U n) := hUsecond
  apply TopologicalSpace.secondCountableTopology_of_countable_cover hUopen
  simpa [U] using
    (chapter03_restrictedProduct_eq_iUnion_exhaustion H E).symm

theorem chapter03_restrictedProduct_sigmaCompact_of_local_data
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [Countable I]
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hsecond : ∀ i, SecondCountableTopology (G i))
    (hHcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hHopen : ∀ i, IsOpen (H i : Set (G i))) :
    SigmaCompactSpace (Chapter03RestrictedProduct H) := by
  classical
  let _ : ∀ i, LocallyCompactSpace (G i) := hlocal
  let _ : ∀ i, SecondCountableTopology (G i) := hsecond
  let K : Set.FiniteExhaustion (Set.univ : Set I) :=
    Set.Countable.finiteExhaustion Set.countable_univ
  let E : Chapter03StageExhaustion I :=
    { stage := K
      finite := fun n => K.finite n
      mono := fun m n hmn => K.mono hmn
      exhaustive := by
        intro i
        have hi : i ∈ ⋃ n, K n := by
          rw [K.iUnion_eq]
          exact Set.mem_univ i
        rcases Set.mem_iUnion.1 hi with ⟨n, hn⟩
        exact ⟨n, hn⟩ }
  let U : ℕ → Set (Chapter03RestrictedProduct H) := fun n =>
    (chapter03StageSubgroup H (E.stage n) : Set (Chapter03RestrictedProduct H))
  have hUsigma : ∀ n, IsSigmaCompact (U n) := by
    intro n
    let S : Set I := E.stage n
    let W : ℕ → ∀ i, Set (G i) := fun m i =>
      if i ∈ S then compactCovering (G i) m else (H i : Set (G i))
    have hWcompact : ∀ m i, IsCompact (W m i) := by
      intro m i
      by_cases hi : i ∈ S
      · simpa [W, hi] using isCompact_compactCovering (G i) m
      · simpa [W, hi] using hHcompact i
    let T := Chapter03Stage H S
    let e : T → ∀ i, G i := fun x => ((x : T).1 : ∀ i, G i)
    have he : @Topology.IsEmbedding T (∀ i, G i)
        (chapter03StageProductTopology H S) inferInstance e := by
      let _ : TopologicalSpace T := chapter03StageProductTopology H S
      refine { eq_induced := rfl, injective := ?_ }
      intro x y hxy
      apply Subtype.ext
      apply chapter03_restrictedProduct_ext H
      intro i
      exact congrFun hxy i
    let L : ℕ → Set T := fun m => e ⁻¹' Set.pi Set.univ (W m)
    have hLcompact : ∀ m, @IsCompact T
        (chapter03StageSubtypeTopology H S) (L m) := by
      intro m
      rw [chapter03_stage_subtype_topology_eq_product_topology H
        (E.finite n) hHopen]
      let _ : TopologicalSpace T := chapter03StageProductTopology H S
      have heimage : e '' L m = Set.pi Set.univ (W m) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact hx
        · intro hy
          have hyH : ∀ᶠ i in Filter.cofinite, y i ∈ H i := by
            filter_upwards [(E.finite n).compl_mem_cofinite] with i hi
            have hiS : i ∉ S := by simpa [S] using hi
            have hyW : y i ∈ W m i := hy i (by simp)
            simpa [W, hiS] using hyW
          let z : Chapter03RestrictedProduct H := ⟨y, hyH⟩
          have hzS : z ∈ chapter03StageSubgroup H S := by
            intro i hiS
            have hyW : y i ∈ W m i := hy i (by simp)
            simpa [W, hiS] using hyW
          let x : T := ⟨z, hzS⟩
          exact ⟨x, hy, rfl⟩
      rw [he.isCompact_iff, heimage]
      exact isCompact_univ_pi (fun i => hWcompact m i)
    have hLcover : ⋃ m, L m = (Set.univ : Set T) := by
      apply Set.eq_univ_of_forall
      intro x
      let F : Finset I := (E.finite n).toFinset
      let m : ℕ := F.sup (fun i =>
        (exists_mem_compactCovering ((e x) i)).choose)
      have hxm : x ∈ L m := by
        change e x ∈ Set.pi Set.univ (W m)
        simp only [Set.mem_pi, mem_univ, true_implies]
        intro i
        by_cases hiS : i ∈ S
        · have hiF : i ∈ F := (E.finite n).mem_toFinset.mpr hiS
          have hiCover : (e x) i ∈ compactCovering (G i)
              (exists_mem_compactCovering ((e x) i)).choose :=
            (exists_mem_compactCovering ((e x) i)).choose_spec
          have hle : (exists_mem_compactCovering ((e x) i)).choose ≤
              F.sup (fun j => (exists_mem_compactCovering ((e x) j)).choose) := by
            exact Finset.le_sup (s := F)
              (f := fun j => (exists_mem_compactCovering ((e x) j)).choose) hiF
          have hle' : (exists_mem_compactCovering ((e x) i)).choose ≤ m := by
            simpa [m] using hle
          have hiCover' := (compactCovering_subset (G i) hle') hiCover
          simpa [W, S, hiS] using hiCover'
        · have hxH : (e x) i ∈ H i := x.2 i hiS
          simpa [W, S, hiS] using hxH
      exact Set.mem_iUnion.2 ⟨m, hxm⟩
    have hstage : @IsSigmaCompact T (chapter03StageSubtypeTopology H S)
        (Set.univ : Set T) := ⟨L, hLcompact, hLcover⟩
    simpa [U, T, S] using
      ((Subtype.isSigmaCompact_iff (s := (Set.univ : Set T))).mp hstage)
  have hSigma : IsSigmaCompact (⋃ n, U n) :=
    isSigmaCompact_iUnion U hUsigma
  have hcover : ⋃ n, U n = (Set.univ : Set (Chapter03RestrictedProduct H)) := by
    simpa [U] using (chapter03_restrictedProduct_eq_iUnion_exhaustion H E).symm
  exact isSigmaCompact_univ_iff.mp (hcover ▸ hSigma)

theorem chapter03_restrictedProduct_secondCountable_sigmaCompact
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [Countable I]
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hsecond : ∀ i, SecondCountableTopology (G i))
    (hHcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hHopen : ∀ i, IsOpen (H i : Set (G i))) :
    SecondCountableTopology (Chapter03RestrictedProduct H) ∧
      SigmaCompactSpace (Chapter03RestrictedProduct H) := by
  exact ⟨chapter03_restrictedProduct_secondCountable H hsecond hHopen,
    chapter03_restrictedProduct_sigmaCompact_of_local_data H hlocal hsecond
      hHcompact hHopen⟩

section AdditiveCountability

variable {I : Type u} {G : I → Type v} [∀ i, AddGroup (G i)]

theorem chapter03_additiveRestrictedProduct_metrizable
    [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [Countable I]
    (hmetric : ∀ i, MetrizableSpace (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    MetrizableSpace (Chapter03AdditiveRestrictedProduct H) := by
  exact chapter03_restrictedProduct_metrizable
    (fun i => AddSubgroup.toSubgroup (H i)) hmetric hH

theorem chapter03_additiveRestrictedProduct_secondCountable
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [Countable I]
    (hsecond : ∀ i, SecondCountableTopology (G i))
    (hH : ∀ i, IsOpen (H i : Set (G i))) :
    SecondCountableTopology (Chapter03AdditiveRestrictedProduct H) := by
  exact chapter03_restrictedProduct_secondCountable
    (fun i => AddSubgroup.toSubgroup (H i)) hsecond hH

theorem chapter03_additiveRestrictedProduct_sigmaCompact_of_local_data
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [Countable I]
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hsecond : ∀ i, SecondCountableTopology (G i))
    (hHcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hHopen : ∀ i, IsOpen (H i : Set (G i))) :
    SigmaCompactSpace (Chapter03AdditiveRestrictedProduct H) := by
  exact chapter03_restrictedProduct_sigmaCompact_of_local_data
    (fun i => AddSubgroup.toSubgroup (H i)) hlocal hsecond hHcompact hHopen

theorem chapter03_additiveRestrictedProduct_secondCountable_sigmaCompact
    [∀ i, TopologicalSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [Countable I]
    (hlocal : ∀ i, LocallyCompactSpace (G i))
    (hsecond : ∀ i, SecondCountableTopology (G i))
    (hHcompact : ∀ i, IsCompact (H i : Set (G i)))
    (hHopen : ∀ i, IsOpen (H i : Set (G i))) :
    SecondCountableTopology (Chapter03AdditiveRestrictedProduct H) ∧
      SigmaCompactSpace (Chapter03AdditiveRestrictedProduct H) := by
  exact ⟨chapter03_restrictedProduct_secondCountable
      (fun i => AddSubgroup.toSubgroup (H i)) hsecond hHopen,
    chapter03_restrictedProduct_sigmaCompact_of_local_data
      (fun i => AddSubgroup.toSubgroup (H i)) hlocal hsecond hHcompact hHopen⟩

end AdditiveCountability

theorem chapter03_secondCountable_closure_has_convergent_sequence
    {X : Type v} [TopologicalSpace X] [SecondCountableTopology X]
    (s : Set X) {x : X} (hx : x ∈ closure s) :
    ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 x) := by
  exact mem_closure_iff_seq_limit.mp hx

end Countability

section Completeness

variable {I : Type u} {G : I → Type v} [∀ i, Group (G i)]

/-- The tail part of the Cauchy condition in a restricted product. -/
def chapter03CauchyTailCondition
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i)) (u : ℕ → Chapter03RestrictedProduct H) : Prop :=
  ∃ S : Set I, S.Finite ∧
    ∀ᶠ n in Filter.atTop, ∀ m : ℕ, n ≤ m →
      ∀ i, i ∉ S →
        ((((u n : ∀ i, G i) i)⁻¹) * ((u m : ∀ i, G i) i)) ∈ H i

/-- A natural uniformity is recorded by the coordinatewise Cauchy and tail
characterization used in the proof of completeness. -/
def chapter03NaturalCauchySequenceCharacterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)] : Prop :=
  ∀ u : ℕ → Chapter03RestrictedProduct H,
    CauchySeq u ↔
      (∀ i, CauchySeq (fun n => ((u n : ∀ i, G i) i))) ∧
        chapter03CauchyTailCondition H u

/-- The filter-level tail condition used for Cauchy nets. -/
def chapter03CauchyFilterTailCondition
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    (l : Filter (Chapter03RestrictedProduct H)) : Prop :=
    ∃ S : Set I, S.Finite ∧
    ∀ᶠ p in l ×ˢ l, ∀ i, i ∉ S →
      (((((p.1 : Chapter03RestrictedProduct H) : ∀ i, G i) i)⁻¹) *
        (((p.2 : Chapter03RestrictedProduct H) : ∀ i, G i) i)) ∈ H i

def chapter03NaturalCauchyFilterCharacterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)] : Prop :=
  ∀ l : Filter (Chapter03RestrictedProduct H),
    Cauchy l ↔
      (∀ i, Cauchy (l.map (fun x : Chapter03RestrictedProduct H =>
        ((x : ∀ i, G i) i)))) ∧
        chapter03CauchyFilterTailCondition H l

/-- The convergence characterization needed in addition to the Cauchy
characterization when proving completeness for a chosen restricted-product
uniformity. -/
def chapter03NaturalConvergenceFilterCharacterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)] : Prop :=
  ∀ l : Filter (Chapter03RestrictedProduct H),
    ∀ x : Chapter03RestrictedProduct H,
      Tendsto (fun y : Chapter03RestrictedProduct H => y) l
        (@nhds _
          (UniformSpace.toTopologicalSpace
            (α := Chapter03RestrictedProduct H)) x) ↔
          (∀ i, Tendsto (fun y : Chapter03RestrictedProduct H =>
          ((y : ∀ i, G i) i)) l
            (𝓝 (((x : ∀ i, G i) i)))) ∧
          ∃ S : Set I, S.Finite ∧
            ∀ᶠ y : Chapter03RestrictedProduct H in l, ∀ i, i ∉ S →
              ((y : ∀ i, G i) i) ∈ H i

/-- The natural-uniformity interface needed by the completeness theorem.

This class deliberately records the two structural characterizations rather
than choosing a competing uniformity on the restricted product. -/
class Chapter03NaturalRestrictedProductUniformity
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)] : Prop where
  sequence_characterization : chapter03NaturalCauchySequenceCharacterization H
  cauchy_characterization : chapter03NaturalCauchyFilterCharacterization H
  convergence_characterization : chapter03NaturalConvergenceFilterCharacterization H
  topology_compatibility :
    UniformSpace.toTopologicalSpace (α := Chapter03RestrictedProduct H) =
      chapter03RestrictedProductTopology H

theorem chapter03_cauchy_sequence_has_eventually_integral_tail
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)]
    (hchar : chapter03NaturalCauchySequenceCharacterization H)
    (u : ℕ → Chapter03RestrictedProduct H) (hu : CauchySeq u) :
    chapter03CauchyTailCondition H u := by
  exact ((hchar u).mp hu).2

theorem chapter03_cauchy_filter_has_eventually_integral_tail
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)]
    (hchar : chapter03NaturalCauchyFilterCharacterization H)
    (l : Filter (Chapter03RestrictedProduct H)) (hl : Cauchy l) :
    chapter03CauchyFilterTailCondition H l := by
  exact ((hchar l).mp hl).2

theorem chapter03_restrictedProduct_complete_of_natural_characterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)]
    (hlocal : ∀ i, CompleteSpace (G i))
    (hclosed : ∀ i, IsClosed (H i : Set (G i)))
    (hchar : chapter03NaturalCauchyFilterCharacterization H)
    (hconv : chapter03NaturalConvergenceFilterCharacterization H) :
    CompleteSpace (Chapter03RestrictedProduct H) := by
  classical
  let _ : ∀ i, CompleteSpace (G i) := hlocal
  refine ⟨?_⟩
  intro l hl
  rcases ((hchar l).mp hl) with ⟨hcoord, htail⟩
  choose x hxcoord using fun i => CompleteSpace.complete (hcoord i)
  have hcoordTendsto : ∀ i, Tendsto
      (fun y : Chapter03RestrictedProduct H => ((y : ∀ i, G i) i)) l (𝓝 (x i)) :=
    fun i => hxcoord i
  let _ : NeBot l := hl.1
  rcases htail with ⟨S, hS, htail⟩
  rcases Filter.mem_prod_iff.mp htail with ⟨s, hs, t, ht, hst⟩
  obtain ⟨a, ha⟩ := Filter.nonempty_of_mem hs
  have hT : (chapter03ExceptionalSet H (a : ∀ i, G i)).Finite :=
    (chapter03_restrictedProduct_mem_iff_exceptional_finite H
      (a : ∀ i, G i)).1 a.property
  let R : Set I := S ∪ chapter03ExceptionalSet H (a : ∀ i, G i)
  have hR : R.Finite := hS.union hT
  have hRtail : ∀ᶠ y : Chapter03RestrictedProduct H in l, ∀ i, i ∉ R →
      ((y : ∀ i, G i) i) ∈ H i := by
    filter_upwards [ht] with y hy
    intro i hiR
    have hiR' : i ∉ S ∪ chapter03ExceptionalSet H (a : ∀ i, G i) := by
      simpa [R] using hiR
    have hiS : i ∉ S := by
      intro hi
      exact hiR' (Or.inl hi)
    have hiT : i ∉ chapter03ExceptionalSet H (a : ∀ i, G i) := by
      intro hi
      exact hiR' (Or.inr hi)
    have haH : ((a : ∀ i, G i) i) ∈ H i := by
      by_contra hne
      apply hiT
      simpa [chapter03ExceptionalSet] using hne
    have hrel :
        ((((a : Chapter03RestrictedProduct H) : ∀ i, G i) i)⁻¹) *
            (((y : Chapter03RestrictedProduct H) : ∀ i, G i) i) ∈ H i := by
      have hpair : (a, y) ∈ s ×ˢ t := ⟨ha, hy⟩
      exact hst hpair i hiS
    have hmul := (H i).mul_mem haH hrel
    simpa [mul_assoc] using hmul
  have hxHtail : ∀ i, i ∉ R → x i ∈ H i := by
    intro i hiR
    apply (hclosed i).mem_of_tendsto (hcoordTendsto i)
    exact hRtail.mono fun y hy => hy i hiR
  have hxmem : ∀ᶠ i in Filter.cofinite, x i ∈ H i := by
    filter_upwards [hR.compl_mem_cofinite] with i hiR
    exact hxHtail i hiR
  let z : Chapter03RestrictedProduct H := ⟨x, hxmem⟩
  have hzconv : Tendsto (fun y : Chapter03RestrictedProduct H => y) l
      (@nhds _
        (UniformSpace.toTopologicalSpace
          (α := Chapter03RestrictedProduct H)) z) := by
    apply (hconv l z).2
    refine ⟨hcoordTendsto, ?_⟩
    exact ⟨R, hR, hRtail⟩
  exact ⟨z, Filter.tendsto_id'.mp (by
    convert hzconv using 1 ; rfl)⟩

theorem chapter03_restrictedProduct_complete_of_complete_local_closed_natural
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, Subgroup (G i))
    [UniformSpace (Chapter03RestrictedProduct H)]
    [Chapter03NaturalRestrictedProductUniformity H]
    (hlocal : ∀ i, CompleteSpace (G i))
    (hclosed : ∀ i, IsClosed (H i : Set (G i))) :
    CompleteSpace (Chapter03RestrictedProduct H) := by
  exact chapter03_restrictedProduct_complete_of_natural_characterization H hlocal hclosed
    (Chapter03NaturalRestrictedProductUniformity.cauchy_characterization (H := H))
    (Chapter03NaturalRestrictedProductUniformity.convergence_characterization (H := H))

section AdditiveCompleteness

variable {I : Type u} {G : I → Type v} [∀ i, AddGroup (G i)]

/-! The same Cauchy and convergence interfaces are needed for additive
restricted products.  They are stated separately because Lean's additive and
multiplicative group hierarchies are distinct. -/

def chapter03AdditiveCauchyTailCondition
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (u : ℕ → Chapter03AdditiveRestrictedProduct H) : Prop :=
  ∃ S : Set I, S.Finite ∧
    ∀ᶠ n in Filter.atTop, ∀ m : ℕ, n ≤ m →
      ∀ i, i ∉ S →
        -(((u n : ∀ i, G i) i)) + ((u m : ∀ i, G i) i) ∈ H i

def chapter03AdditiveNaturalCauchySequenceCharacterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [UniformSpace (Chapter03AdditiveRestrictedProduct H)] : Prop :=
  ∀ u : ℕ → Chapter03AdditiveRestrictedProduct H,
    CauchySeq u ↔
      (∀ i, CauchySeq (fun n => ((u n : ∀ i, G i) i))) ∧
        chapter03AdditiveCauchyTailCondition H u

def chapter03AdditiveCauchyFilterTailCondition
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    (l : Filter (Chapter03AdditiveRestrictedProduct H)) : Prop :=
  ∃ S : Set I, S.Finite ∧
    ∀ᶠ p in l ×ˢ l, ∀ i, i ∉ S →
      -((((p.1 : Chapter03AdditiveRestrictedProduct H) : ∀ i, G i) i)) +
        (((p.2 : Chapter03AdditiveRestrictedProduct H) : ∀ i, G i) i) ∈ H i

def chapter03AdditiveNaturalCauchyFilterCharacterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [UniformSpace (Chapter03AdditiveRestrictedProduct H)] : Prop :=
  ∀ l : Filter (Chapter03AdditiveRestrictedProduct H),
    Cauchy l ↔
      (∀ i, Cauchy (l.map (fun x : Chapter03AdditiveRestrictedProduct H =>
        ((x : ∀ i, G i) i)))) ∧
        chapter03AdditiveCauchyFilterTailCondition H l

def chapter03AdditiveNaturalConvergenceFilterCharacterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [UniformSpace (Chapter03AdditiveRestrictedProduct H)] : Prop :=
  ∀ l : Filter (Chapter03AdditiveRestrictedProduct H),
    ∀ x : Chapter03AdditiveRestrictedProduct H,
      Tendsto (fun y : Chapter03AdditiveRestrictedProduct H => y) l
        (@nhds _
          (UniformSpace.toTopologicalSpace
            (α := Chapter03AdditiveRestrictedProduct H)) x) ↔
          (∀ i, Tendsto (fun y : Chapter03AdditiveRestrictedProduct H =>
          ((y : ∀ i, G i) i)) l
            (𝓝 (((x : ∀ i, G i) i)))) ∧
          ∃ S : Set I, S.Finite ∧
            ∀ᶠ y : Chapter03AdditiveRestrictedProduct H in l, ∀ i, i ∉ S →
              ((y : ∀ i, G i) i) ∈ H i

class Chapter03NaturalAdditiveRestrictedProductUniformity
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [UniformSpace (Chapter03AdditiveRestrictedProduct H)] : Prop where
  sequence_characterization :
    chapter03AdditiveNaturalCauchySequenceCharacterization H
  cauchy_characterization :
    chapter03AdditiveNaturalCauchyFilterCharacterization H
  convergence_characterization :
    chapter03AdditiveNaturalConvergenceFilterCharacterization H
  topology_compatibility :
    UniformSpace.toTopologicalSpace (α := Chapter03AdditiveRestrictedProduct H) =
      chapter03AdditiveRestrictedProductTopology H

theorem chapter03_additive_cauchy_sequence_has_eventually_integral_tail
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [UniformSpace (Chapter03AdditiveRestrictedProduct H)]
    (hchar : chapter03AdditiveNaturalCauchySequenceCharacterization H)
    (u : ℕ → Chapter03AdditiveRestrictedProduct H) (hu : CauchySeq u) :
    chapter03AdditiveCauchyTailCondition H u := by
  exact ((hchar u).mp hu).2

theorem chapter03_additive_cauchy_filter_has_eventually_integral_tail
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [UniformSpace (Chapter03AdditiveRestrictedProduct H)]
    (hchar : chapter03AdditiveNaturalCauchyFilterCharacterization H)
    (l : Filter (Chapter03AdditiveRestrictedProduct H)) (hl : Cauchy l) :
    chapter03AdditiveCauchyFilterTailCondition H l := by
  exact ((hchar l).mp hl).2

theorem chapter03_additiveRestrictedProduct_complete_of_natural_characterization
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [UniformSpace (Chapter03AdditiveRestrictedProduct H)]
    (hlocal : ∀ i, CompleteSpace (G i))
    (hclosed : ∀ i, IsClosed (H i : Set (G i)))
    (hchar : chapter03AdditiveNaturalCauchyFilterCharacterization H)
    (hconv : chapter03AdditiveNaturalConvergenceFilterCharacterization H) :
    CompleteSpace (Chapter03AdditiveRestrictedProduct H) := by
  classical
  let _ : ∀ i, CompleteSpace (G i) := hlocal
  refine ⟨?_⟩
  intro l hl
  rcases ((hchar l).mp hl) with ⟨hcoord, htail⟩
  choose x hxcoord using fun i => CompleteSpace.complete (hcoord i)
  have hcoordTendsto : ∀ i, Tendsto
      (fun y : Chapter03AdditiveRestrictedProduct H => ((y : ∀ i, G i) i)) l (𝓝 (x i)) :=
    fun i => hxcoord i
  let _ : NeBot l := hl.1
  rcases htail with ⟨S, hS, htail⟩
  rcases Filter.mem_prod_iff.mp htail with ⟨s, hs, t, ht, hst⟩
  obtain ⟨a, ha⟩ := Filter.nonempty_of_mem hs
  have hT : {i | ((a : ∀ i, G i) i) ∉ H i}.Finite :=
    Filter.eventually_cofinite.mp a.property
  let R : Set I := S ∪ {i | ((a : ∀ i, G i) i) ∉ H i}
  have hR : R.Finite := hS.union hT
  have hRtail : ∀ᶠ y : Chapter03AdditiveRestrictedProduct H in l, ∀ i, i ∉ R →
      ((y : ∀ i, G i) i) ∈ H i := by
    filter_upwards [ht] with y hy
    intro i hiR
    have hiR' : i ∉ S ∪ {i | ((a : ∀ i, G i) i) ∉ H i} := by
      simpa [R] using hiR
    have hiS : i ∉ S := by
      intro hi
      exact hiR' (Or.inl hi)
    have hiT : i ∉ {i | ((a : ∀ i, G i) i) ∉ H i} := by
      intro hi
      exact hiR' (Or.inr hi)
    have haH : ((a : ∀ i, G i) i) ∈ H i := by
      by_contra hne
      apply hiT
      exact hne
    have hrel :
        -(((a : Chapter03AdditiveRestrictedProduct H) : ∀ i, G i) i) +
            (((y : Chapter03AdditiveRestrictedProduct H) : ∀ i, G i) i) ∈ H i := by
      have hpair : (a, y) ∈ s ×ˢ t := ⟨ha, hy⟩
      exact hst hpair i hiS
    have hadd := (H i).add_mem haH hrel
    simpa [add_assoc] using hadd
  have hxHtail : ∀ i, i ∉ R → x i ∈ H i := by
    intro i hiR
    apply (hclosed i).mem_of_tendsto (hcoordTendsto i)
    exact hRtail.mono fun y hy => hy i hiR
  have hxmem : ∀ᶠ i in Filter.cofinite, x i ∈ H i := by
    filter_upwards [hR.compl_mem_cofinite] with i hiR
    exact hxHtail i hiR
  let z : Chapter03AdditiveRestrictedProduct H := ⟨x, hxmem⟩
  have hzconv : Tendsto (fun y : Chapter03AdditiveRestrictedProduct H => y) l
      (@nhds _
        (UniformSpace.toTopologicalSpace
          (α := Chapter03AdditiveRestrictedProduct H)) z) := by
    apply (hconv l z).2
    refine ⟨hcoordTendsto, ?_⟩
    exact ⟨R, hR, hRtail⟩
  exact ⟨z, Filter.tendsto_id'.mp (by
    convert hzconv using 1 ; rfl)⟩

theorem chapter03_additiveRestrictedProduct_complete_of_complete_local_closed_natural
    [∀ i, UniformSpace (G i)]
    (H : ∀ i, AddSubgroup (G i))
    [UniformSpace (Chapter03AdditiveRestrictedProduct H)]
    [Chapter03NaturalAdditiveRestrictedProductUniformity H]
    (hlocal : ∀ i, CompleteSpace (G i))
    (hclosed : ∀ i, IsClosed (H i : Set (G i))) :
    CompleteSpace (Chapter03AdditiveRestrictedProduct H) := by
  exact chapter03_additiveRestrictedProduct_complete_of_natural_characterization H hlocal hclosed
    (Chapter03NaturalAdditiveRestrictedProductUniformity.cauchy_characterization (H := H))
    (Chapter03NaturalAdditiveRestrictedProductUniformity.convergence_characterization (H := H))

end AdditiveCompleteness

/-!
The source's completeness assertion is conditional on complete local uniform
spaces and closed distinguished subgroups.  Since this chapter does not yet
choose a canonical uniform-space construction for the restricted product, the
theorem above exposes the corresponding Cauchy and convergence
characterizations as explicit interfaces.
-/

end Completeness

section ClosedSubgroupsAndQuotients

variable {G : Type v} [Group G] [TopologicalSpace G]

theorem chapter03_closed_subgroup_is_locallyCompact
    [LocallyCompactSpace G] [T2Space G]
    (H : Subgroup G) (hclosed : IsClosed (H : Set G)) :
    LocallyCompactSpace H := by
  exact hclosed.locallyCompactSpace

theorem chapter03_closed_subgroup_is_secondCountable
    [SecondCountableTopology G]
    (H : Subgroup G) :
    SecondCountableTopology H := by
  exact TopologicalSpace.secondCountableTopology_induced (H : Set G) G (↑)

theorem chapter03_closed_normal_quotient_is_locallyCompact_hausdorff
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (N : Subgroup G) [N.Normal]
    (hclosed : IsClosed (N : Set G)) :
    LocallyCompactSpace (G ⧸ N) ∧ T2Space (G ⧸ N) := by
  let _ : IsClosed (N : Set G) := hclosed
  exact ⟨inferInstance, inferInstance⟩

/-- Closedness of a diagonal range is the interface needed before forming the
locally compact Hausdorff quotient by diagonal global points. -/
def chapter03DiagonalRangeClosed {A : Type*} [Monoid A]
    (ι : A →* G) : Prop :=
  IsClosed (Set.range ι)

theorem chapter03_closed_diagonal_quotient_is_locallyCompact_hausdorff
    {A : Type*} [Group A]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    (ι : A →* G) (N : Subgroup G) [N.Normal]
    (hι : chapter03DiagonalRangeClosed ι)
    (hrange : Set.range ι = (N : Set G)) :
    LocallyCompactSpace (G ⧸ N) ∧ T2Space (G ⧸ N) := by
  apply chapter03_closed_normal_quotient_is_locallyCompact_hausdorff N
  rw [← hrange]
  exact hι

end ClosedSubgroupsAndQuotients

section AdditiveClosedSubgroupsAndQuotients

variable {G : Type v} [AddCommGroup G] [TopologicalSpace G]

theorem chapter03_closed_addSubgroup_is_locallyCompact
    [LocallyCompactSpace G] [T2Space G]
    (H : AddSubgroup G) (hclosed : IsClosed (H : Set G)) :
    LocallyCompactSpace H := by
  exact hclosed.locallyCompactSpace

theorem chapter03_closed_normal_addQuotient_is_locallyCompact_hausdorff
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G]
    (N : AddSubgroup G) (hclosed : IsClosed (N : Set G)) :
    LocallyCompactSpace (G ⧸ N) ∧ T2Space (G ⧸ N) := by
  let _ : IsClosed (N : Set G) := hclosed
  exact ⟨inferInstance, inferInstance⟩

/-- The additive version of the closed-diagonal quotient interface. -/
def chapter03AdditiveDiagonalRangeClosed {A : Type*} [AddZeroClass A]
    (ι : A →+ G) : Prop :=
  IsClosed (Set.range ι)

theorem chapter03_closed_additive_diagonal_quotient_is_locallyCompact_hausdorff
    {A : Type*} [AddCommGroup A]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G]
    (ι : A →+ G) (N : AddSubgroup G)
    (hι : chapter03AdditiveDiagonalRangeClosed ι)
    (hrange : Set.range ι = (N : Set G)) :
    LocallyCompactSpace (G ⧸ N) ∧ T2Space (G ⧸ N) := by
  apply chapter03_closed_normal_addQuotient_is_locallyCompact_hausdorff N
  rw [← hrange]
  exact hι

end AdditiveClosedSubgroupsAndQuotients

end
end LastLib.Book04AdelesAndIdeles.Chapter03
