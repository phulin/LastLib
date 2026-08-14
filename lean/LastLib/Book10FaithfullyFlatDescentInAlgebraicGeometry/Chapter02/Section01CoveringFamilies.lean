import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Dependencies

/-!
## 2.1 Covering families

This file records the family-level fpqc and fppf interfaces.  The finite reduction is indexed by a
natural number rather than a finite set of family members, because the source allows several
quasi-compact opens in the same member of a family.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v

/-- A set-indexed family of morphisms into a fixed scheme. -/
structure SchemeFamily (S : Scheme.{u}) (I : Type v) where
  obj : I → Scheme.{u}
  map : ∀ i, obj i ⟶ S

def SchemeFamily.presieve {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Presieve S :=
  Presieve.ofArrows F.obj F.map

/-- A finite amount of a family lying over a quasi-compact open of the base. -/
structure FiniteFamilyReduction {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) (U : S.Opens) where
  cardinality : ℕ
  member : Fin cardinality → I
  sourceOpen : ∀ j, (F.obj (member j)).Opens
  quasiCompact : ∀ j, IsCompact (sourceOpen j : Set (F.obj (member j)))
  covers : (U : Set S) =
    ⋃ j : Fin cardinality,
      F.map (member j) '' (sourceOpen j : Set (F.obj (member j)))

/-- The book's family-level definition of an fpqc cover. -/
structure FpqcCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Prop where
  flat : ∀ i, Flat (F.map i)
  finite_reduction : ∀ (U : S.Opens), IsCompact (U : Set S) →
    Nonempty (FiniteFamilyReduction F U)

/-- The image condition used for family-level joint surjectivity. -/
def JointlySurjective {S : Scheme.{u}} {I : Type v} (F : SchemeFamily S I) : Prop :=
  ∀ s : S, ∃ i, ∃ x : F.obj i, F.map i x = s

theorem jointlySurjective_iff_iUnion_range_eq_univ
    {S : Scheme.{u}} {I : Type v} (F : SchemeFamily S I) :
    JointlySurjective F ↔
      (⋃ i, Set.range (F.map i)) = (Set.univ : Set S) := by
  constructor
  · intro h
    ext s
    constructor
    · intro _
      exact Set.mem_univ s
    · intro _
      obtain ⟨i, x, hx⟩ := h s
      exact Set.mem_iUnion.2 ⟨i, ⟨x, hx⟩⟩
  · intro h s
    have hs : s ∈ ⋃ i, Set.range (F.map i) := by
      rw [h]
      exact Set.mem_univ s
    rcases Set.mem_iUnion.1 hs with ⟨i, hi⟩
    rcases hi with ⟨x, hx⟩
    exact ⟨i, x, hx⟩

/-- A family of flat morphisms locally of finite presentation which is jointly surjective. -/
structure FppfCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Prop where
  jointly_surjective : JointlySurjective F
  flat : ∀ i, Flat (F.map i)
  locally_of_finite_presentation : ∀ i, LocallyOfFinitePresentation (F.map i)

/-- A family of open immersions covering its target. -/
def IsZariskiCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Prop :=
  (∀ i, IsOpenImmersion (F.map i)) ∧ JointlySurjective F

/-- A jointly surjective family of étale morphisms. -/
def IsEtaleCoveringFamily {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) : Prop :=
  JointlySurjective F ∧ ∀ i, Etale (F.map i)

theorem fppf_member_image_isOpen
    {S T : Scheme.{u}} {p : T ⟶ S} (hflat : Flat p)
    (hfp : LocallyOfFinitePresentation p) (V : T.Opens) :
    IsOpen (p '' (V : Set T)) := by
  have : Flat p := hflat
  have : LocallyOfFinitePresentation p := hfp
  exact Scheme.Hom.isOpenMap p (V : Set T) V.isOpen

theorem fpqcCoveringFamily_iff_affine_reductions
    {S : Scheme.{u}} {I : Type v} (F : SchemeFamily S I) :
    FpqcCoveringFamily F ↔
      (∀ i, Flat (F.map i)) ∧
        (∀ (U : S.Opens), IsAffineOpen U →
          Nonempty (FiniteFamilyReduction F U)) := by
  constructor
  · intro hF
    refine ⟨hF.flat, ?_⟩
    intro U hU
    exact hF.finite_reduction U hU.isCompact
  · rintro ⟨hflat, hred⟩
    refine ⟨hflat, ?_⟩
    intro U hU
    obtain ⟨s, hs, hUeq⟩ :=
      isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
    let J := {i : S.affineOpens // i ∈ s}
    let : Fintype J := hs.fintype
    let R : ∀ i : J, FiniteFamilyReduction F (i.1 : S.Opens) :=
      fun i => (hred (i.1 : S.Opens) i.1.2).some
    let K := Σ i : J, Fin (R i).cardinality
    let : Fintype K := Fintype.ofFinite K
    let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
    refine ⟨Fintype.card K,
      (fun j => (R (e.symm j).1).member (e.symm j).2),
      (fun j => (R (e.symm j).1).sourceOpen (e.symm j).2),
      (fun j => (R (e.symm j).1).quasiCompact (e.symm j).2), ?_⟩
    ext x
    constructor
    · intro hx
      have hxU : x ∈ (⨆ i ∈ s, (i : S.Opens)) := by
        rw [← hUeq]
        exact hx
      rcases TopologicalSpace.Opens.mem_iSup.mp hxU with ⟨i, hxU⟩
      rcases TopologicalSpace.Opens.mem_iSup.mp hxU with ⟨hi, hxi⟩
      have hxi' : x ∈ ⋃ k : Fin (R ⟨i, hi⟩).cardinality,
          F.map ((R ⟨i, hi⟩).member k) ''
            ((R ⟨i, hi⟩).sourceOpen k :
              Set (F.obj ((R ⟨i, hi⟩).member k))) := by
        rw [← (R ⟨i, hi⟩).covers]
        exact hxi
      rcases Set.mem_iUnion.1 hxi' with ⟨k, hk⟩
      refine Set.mem_iUnion.2 ⟨e ⟨⟨i, hi⟩, k⟩, ?_⟩
      rw [e.symm_apply_apply]
      exact hk
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
      let q := e.symm j
      have hxi : x ∈ ((q.1 : S.Opens) : Set S) := by
        rw [(R q.1).covers]
        exact Set.mem_iUnion.2 ⟨q.2, hj⟩
      have hxU : x ∈ (⨆ i ∈ s, (i : S.Opens)) := by
        apply TopologicalSpace.Opens.mem_iSup.mpr
        refine ⟨q.1.1, ?_⟩
        apply TopologicalSpace.Opens.mem_iSup.mpr
        exact ⟨q.1.2, hxi⟩
      exact hUeq.symm ▸ hxU

theorem FpqcCoveringFamily.jointly_surjective
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : FpqcCoveringFamily F) : JointlySurjective F := by
  intro s
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (a := s) (Set.mem_univ s) isOpen_univ
  obtain ⟨R⟩ := hF.finite_reduction U hU.isCompact
  have hs : s ∈ (U : Set S) := hsU
  rw [R.covers] at hs
  rcases Set.mem_iUnion.1 hs with ⟨j, hj⟩
  rcases hj with ⟨x, _, hxp⟩
  exact ⟨R.member j, x, hxp⟩

private theorem finiteReduction_of_flat_lfp_jointlySurjective
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hflat : ∀ i, Flat (F.map i))
    (hfp : ∀ i, LocallyOfFinitePresentation (F.map i))
    (hjoint : JointlySurjective F) :
    ∀ (U : S.Opens), IsAffineOpen U →
      Nonempty (FiniteFamilyReduction F U) := by
  intro U hU
  let L := Σ i : I,
    {V : (F.obj i).affineOpens //
      (V : Set (F.obj i)) ⊆ (F.map i) ⁻¹' (U : Set S)}
  let c : L → Set S := fun q ↦
    F.map q.1 '' (q.2.1 : Set (F.obj q.1))
  have hc : ∀ q : L, IsOpen (c q) := by
    intro q
    exact fppf_member_image_isOpen (hflat q.1) (hfp q.1)
      (q.2.1 : (F.obj q.1).Opens)
  have hcov : (U : Set S) ⊆ ⋃ q, c q := by
    intro x hx
    obtain ⟨i, y, hy⟩ := hjoint x
    have hyU : y ∈ (F.map i) ⁻¹ᵁ U := by
      change F.map i y ∈ (U : Set S)
      rw [hy]
      exact hx
    obtain ⟨W, hW, hyW, hWsub⟩ :=
      exists_isAffineOpen_mem_and_subset (U := (F.map i) ⁻¹ᵁ U) hyU
    let V : (F.obj i).affineOpens := ⟨W, hW⟩
    have hVsub : (V : Set (F.obj i)) ⊆ (F.map i) ⁻¹' (U : Set S) := by
      simpa [V] using hWsub
    let q : L := ⟨i, ⟨V, hVsub⟩⟩
    refine Set.mem_iUnion.2 ⟨q, ?_⟩
    simpa [c, q] using (show x ∈ F.map i '' (V : Set (F.obj i)) from ⟨y, hyW, hy⟩)
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover c hc hcov
  let K := {q : L // q ∈ (t : Set L)}
  let : Finite K := t.finite_toSet.to_subtype
  let : Fintype K := Fintype.ofFinite K
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  refine ⟨Fintype.card K,
    (fun j ↦ (e j).1.1),
    (fun j ↦ (e j).1.2.1),
    (fun j ↦ (e j).1.2.1.property.isCompact), ?_⟩
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 (ht hx) with ⟨q, hq⟩
    rcases Set.mem_iUnion.1 hq with ⟨hqt, hqx⟩
    refine Set.mem_iUnion.2 ⟨e.symm ⟨q, hqt⟩, ?_⟩
    rw [e.apply_symm_apply]
    exact hqx
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
    let q := e j
    rcases hj with ⟨y, hyV, hy⟩
    have hyU := q.1.2.2 hyV
    change F.map q.1.1 y ∈ (U : Set S) at hyU
    rw [hy] at hyU
    exact hyU

theorem fppfCoveringFamily_is_fpqc
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : FppfCoveringFamily F) : FpqcCoveringFamily F := by
  refine (fpqcCoveringFamily_iff_affine_reductions F).2 ?_
  exact ⟨hF.flat, finiteReduction_of_flat_lfp_jointlySurjective
    hF.flat hF.locally_of_finite_presentation hF.jointly_surjective⟩

theorem zariskiCoveringFamily_is_fpqc
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsZariskiCoveringFamily F) : FpqcCoveringFamily F := by
  refine (fpqcCoveringFamily_iff_affine_reductions F).2 ?_
  refine ⟨?_, ?_⟩
  · intro i
    have : IsOpenImmersion (F.map i) := hF.1 i
    infer_instance
  · apply finiteReduction_of_flat_lfp_jointlySurjective
    · intro i
      have : IsOpenImmersion (F.map i) := hF.1 i
      infer_instance
    · intro i
      have : IsOpenImmersion (F.map i) := hF.1 i
      infer_instance
    · exact hF.2

theorem zariskiCoveringFamily_is_etale
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsZariskiCoveringFamily F) :
    IsEtaleCoveringFamily F := by
  refine ⟨hF.2, ?_⟩
  intro i
  have : IsOpenImmersion (F.map i) := hF.1 i
  infer_instance

theorem zariskiCoveringFamily_is_fppf
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsZariskiCoveringFamily F) : FppfCoveringFamily F := by
  refine ⟨hF.2, ?_, ?_⟩
  · intro i
    have : IsOpenImmersion (F.map i) := hF.1 i
    infer_instance
  · intro i
    have : IsOpenImmersion (F.map i) := hF.1 i
    infer_instance

theorem etaleCoveringFamily_is_fppf
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsEtaleCoveringFamily F) : FppfCoveringFamily F := by
  refine ⟨hF.1, ?_, ?_⟩
  · intro i
    have : Etale (F.map i) := hF.2 i
    infer_instance
  · intro i
    have : Etale (F.map i) := hF.2 i
    infer_instance

theorem etaleCoveringFamily_is_fpqc
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hF : IsEtaleCoveringFamily F) : FpqcCoveringFamily F := by
  exact fppfCoveringFamily_is_fpqc (etaleCoveringFamily_is_fppf hF)

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02
