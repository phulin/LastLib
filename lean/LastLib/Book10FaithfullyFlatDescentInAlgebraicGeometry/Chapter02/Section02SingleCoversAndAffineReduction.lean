import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section01CoveringFamilies

/-!
## 2.2 Single covers and affine reduction

The singleton-family predicate is kept distinct from quasi-compactness of the whole source.  This
is the distinction needed for an infinite disjoint union of redundant copies of the target.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry TensorProduct

universe u v

/-- A faithfully flat, quasi-compact, surjective morphism in the book's fpqc terminology. -/
def IsFpqcMorphism {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  Flat p ∧ QuasiCompact p ∧ Surjective p

/-- The singleton family associated to one scheme morphism. -/
def singletonFamily {S T : Scheme.{u}} (p : T ⟶ S) : SchemeFamily S Unit where
  obj := fun _ ↦ T
  map := fun _ ↦ p

/-- The family-level fpqc condition for a singleton. -/
def IsFpqcSingletonFamily {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  FpqcCoveringFamily (singletonFamily p)

/-- The finite-reduction condition for one morphism, with the source open exposed explicitly. -/
def SingletonFiniteReductionCondition {S T : Scheme.{u}} (p : T ⟶ S) : Prop :=
  ∀ (U : S.Opens), IsCompact (U : Set S) →
    ∃ V : T.Opens, IsCompact (V : Set T) ∧
      (U : Set S) = p '' (V : Set T)

theorem singletonFamily_iff_flat_and_finite_reduction
    {S T : Scheme.{u}} (p : T ⟶ S) :
    IsFpqcSingletonFamily p ↔ Flat p ∧ SingletonFiniteReductionCondition p := by
  constructor
  · intro hp
    change FpqcCoveringFamily
      ({ obj := (fun _ : Unit ↦ T), map := (fun _ : Unit ↦ p) } : SchemeFamily S Unit) at hp
    refine ⟨hp.flat (), ?_⟩
    intro U hU
    obtain ⟨R⟩ := hp.finite_reduction U hU
    let sourceOpen : ∀ j : Fin R.cardinality, T.Opens := fun j ↦ by
      exact R.sourceOpen j
    have hsource (j : Fin R.cardinality) : sourceOpen j = R.sourceOpen j := by
      dsimp [sourceOpen]
    let V : T.Opens := ⨆ j, sourceOpen j
    have hcompact : IsCompact (⋃ j : Fin R.cardinality,
        (sourceOpen j : Set T)) := by
      apply isCompact_iUnion
      intro j
      exact R.quasiCompact j
    have hVeq : (V : Set T) = ⋃ j : Fin R.cardinality,
        (sourceOpen j : Set T) := by
      simp [V, TopologicalSpace.Opens.coe_iSup]
    refine ⟨V, ?_, ?_⟩
    · simpa [V, TopologicalSpace.Opens.coe_iSup] using
        hcompact
    · calc
        (U : Set S) = ⋃ j : Fin R.cardinality,
            p '' (sourceOpen j : Set T) := by
              rw [R.covers]
        _ = p '' (V : Set T) := by rw [hVeq, Set.image_iUnion]
  · rintro ⟨hflat, hcondition⟩
    refine ⟨?_, ?_⟩
    · intro i
      simpa [singletonFamily] using hflat
    · intro U hU
      obtain ⟨V, hV, hVU⟩ := hcondition U hU
      refine ⟨⟨1, (fun _ ↦ ()), (fun _ ↦ V), (fun _ ↦ hV), ?_⟩⟩
      change (U : Set S) = ⋃ _ : Fin 1, p '' (V : Set T)
      rw [hVU]
      ext x
      constructor
      · intro hx
        exact Set.mem_iUnion.2 ⟨0, hx⟩
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
        exact hj

theorem fpqcMorphism_is_singletonFamily
    {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : IsFpqcMorphism p) : IsFpqcSingletonFamily p := by
  apply (singletonFamily_iff_flat_and_finite_reduction p).2
  refine ⟨hp.1, ?_⟩
  intro U hU
  let : QuasiCompact p := hp.2.1
  let : Surjective p := hp.2.2
  refine ⟨p ⁻¹ᵁ U, p.isCompact_preimage hU, ?_⟩
  simpa only [Scheme.Hom.coe_preimage] using (‹Surjective p›.surj.image_preimage U).symm

theorem singletonFamily_is_flat_and_surjective
    {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : IsFpqcSingletonFamily p) : Flat p ∧ Surjective p := by
  change FpqcCoveringFamily
    ({ obj := (fun _ : Unit ↦ T), map := (fun _ : Unit ↦ p) } : SchemeFamily S Unit) at hp
  refine ⟨hp.flat (), ⟨?_⟩⟩
  intro s
  obtain ⟨_, ⟨U, hU, rfl⟩, hsU, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (a := s) (Set.mem_univ s) isOpen_univ
  obtain ⟨R⟩ := hp.finite_reduction U hU.isCompact
  have hs : s ∈ (U : Set S) := hsU
  rw [R.covers] at hs
  rcases Set.mem_iUnion.1 hs with ⟨j, hj⟩
  rcases hj with ⟨x, _, hxp⟩
  exact ⟨x, hxp⟩

theorem singletonFamily_is_fpqcMorphism_of_quasiCompact
    {S T : Scheme.{u}} {p : T ⟶ S}
    (hp : IsFpqcSingletonFamily p) (hqc : QuasiCompact p) :
    IsFpqcMorphism p := by
  rcases singletonFamily_is_flat_and_surjective hp with ⟨hflat, hsurj⟩
  exact ⟨hflat, hqc, hsurj⟩

theorem isFpqcMorphism_iff_singletonFamily_of_quasiCompact
    {S T : Scheme.{u}} (p : T ⟶ S) (hqc : QuasiCompact p) :
    IsFpqcMorphism p ↔ IsFpqcSingletonFamily p := by
  constructor
  · intro hp
    exact fpqcMorphism_is_singletonFamily hp
  · intro hp
    exact singletonFamily_is_fpqcMorphism_of_quasiCompact hp hqc

/-- A quasi-compact open part of a singleton source, together with a finite affine refinement. -/
structure AffineSingletonRefinement {S T : Scheme.{u}} (p : T ⟶ S) where
  sourceOpen : T.Opens
  sourceOpen_quasiCompact : IsCompact (sourceOpen : Set T)
  sourceOpen_surjective : p '' (sourceOpen : Set T) = (Set.univ : Set S)
  cardinality : ℕ
  affineOpen : Fin cardinality → T.Opens
  affine : ∀ j, IsAffineOpen (affineOpen j)
  refines : ∀ j, affineOpen j ≤ sourceOpen
  covers : (sourceOpen : Set T) = ⋃ j : Fin cardinality, (affineOpen j : Set T)

theorem exists_affine_singleton_refinement
    {S T : Scheme.{u}} {p : T ⟶ S}
    (hS : IsAffine S) (hp : IsFpqcSingletonFamily p) :
    Nonempty (AffineSingletonRefinement p) := by
  let : IsAffine S := hS
  change FpqcCoveringFamily
    ({ obj := (fun _ : Unit ↦ T), map := (fun _ : Unit ↦ p) } : SchemeFamily S Unit) at hp
  obtain ⟨R⟩ := hp.finite_reduction (⊤ : S.Opens) isCompact_univ
  let affineSets : ∀ j : Fin R.cardinality, Set T.affineOpens := fun j ↦
    (isCompact_iff_finite_and_eq_biUnion_affineOpens.mp (R.quasiCompact j)).choose
  have affineSets_finite : ∀ j : Fin R.cardinality, (affineSets j).Finite := by
    intro j
    exact (isCompact_iff_finite_and_eq_biUnion_affineOpens.mp (R.quasiCompact j)).choose_spec.1
  have affineSets_covers : ∀ j : Fin R.cardinality,
      R.sourceOpen j = ⨆ (V : T.affineOpens) (_ : V ∈ affineSets j), (V : T.Opens) := by
    intro j
    exact (isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (R.quasiCompact j)).choose_spec.2
  let J := Σ j : Fin R.cardinality, {V : T.affineOpens // V ∈ affineSets j}
  let : ∀ j : Fin R.cardinality,
      Finite {V : T.affineOpens // V ∈ affineSets j} := fun j ↦
    (affineSets_finite j).to_subtype
  let : Finite J := inferInstance
  let : Fintype J := Fintype.ofFinite J
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let affineOpen : Fin (Fintype.card J) → T.Opens := fun k ↦
    ((e k).2.1 : T.Opens)
  let sourceOpen : T.Opens := ⨆ k, affineOpen k
  have hsource : (sourceOpen : Set T) = ⋃ k, (affineOpen k : Set T) := by
    simp [sourceOpen, TopologicalSpace.Opens.coe_iSup]
  refine ⟨⟨sourceOpen, ?_, ?_, Fintype.card J, affineOpen, ?_, ?_, ?_⟩⟩
  · rw [hsource]
    apply isCompact_iUnion
    intro k
    exact (e k).2.1.2.isCompact
  · ext x
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      have hx : x ∈ ⋃ j : Fin R.cardinality,
          p '' (R.sourceOpen j : Set T) := by
        rw [← R.covers]
        exact Set.mem_univ x
      rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
      rcases hj with ⟨y, hy, hpy⟩
      rw [affineSets_covers j] at hy
      have hy' : y ∈ ⋃ (V : T.affineOpens) (_ : V ∈ affineSets j),
          (V : Set T) := by
        simpa only [TopologicalSpace.Opens.coe_iSup] using hy
      rcases Set.mem_iUnion.1 hy' with ⟨V, hy⟩
      rcases Set.mem_iUnion.1 hy with ⟨hV, hyV⟩
      let q : J := ⟨j, ⟨V, hV⟩⟩
      refine ⟨y, ?_, hpy⟩
      rw [hsource]
      refine Set.mem_iUnion.2 ⟨e.symm q, ?_⟩
      change y ∈ ((e (e.symm q)).2.1 : Set T)
      rw [e.apply_symm_apply]
      exact hyV
  · intro k
    exact (e k).2.1.2
  · intro k
    exact le_iSup affineOpen k
  · rw [hsource]

/-- A finite family reduction in which every selected source open is affine. -/
structure AffineFiniteFamilyReduction {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) (U : S.Opens) where
  cardinality : ℕ
  member : Fin cardinality → I
  sourceOpen : ∀ j, (F.obj (member j)).Opens
  affine : ∀ j, IsAffineOpen (sourceOpen j)
  quasiCompact : ∀ j, IsCompact (sourceOpen j : Set (F.obj (member j)))
  covers : (U : Set S) =
    ⋃ j : Fin cardinality,
      F.map (member j) '' (sourceOpen j : Set (F.obj (member j)))

theorem finiteFamilyReduction_affine_refinement
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    {U : S.Opens} (hU : IsCompact (U : Set S))
    (hF : FpqcCoveringFamily F) :
    Nonempty (AffineFiniteFamilyReduction F U) := by
  obtain ⟨R⟩ := hF.finite_reduction U hU
  let affineSets : ∀ j : Fin R.cardinality,
      Set (F.obj (R.member j)).affineOpens := fun j ↦
    (isCompact_iff_finite_and_eq_biUnion_affineOpens.mp (R.quasiCompact j)).choose
  have affineSets_finite : ∀ j : Fin R.cardinality,
      (affineSets j).Finite := by
    intro j
    exact (isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (R.quasiCompact j)).choose_spec.1
  have affineSets_covers : ∀ j : Fin R.cardinality,
      R.sourceOpen j = ⨆ (V : (F.obj (R.member j)).affineOpens)
        (_ : V ∈ affineSets j), (V : (F.obj (R.member j)).Opens) := by
    intro j
    exact (isCompact_iff_finite_and_eq_biUnion_affineOpens.mp
      (R.quasiCompact j)).choose_spec.2
  let J := Σ j : Fin R.cardinality,
    {V : (F.obj (R.member j)).affineOpens // V ∈ affineSets j}
  let : ∀ j : Fin R.cardinality,
      Finite {V : (F.obj (R.member j)).affineOpens // V ∈ affineSets j} := fun j ↦
    (affineSets_finite j).to_subtype
  let : Finite J := inferInstance
  let : Fintype J := Fintype.ofFinite J
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨⟨Fintype.card J,
    (fun k ↦ R.member (e k).1),
    (fun k ↦ ((e k).2.1 : (F.obj (R.member (e k).1)).Opens)),
    (fun k ↦ (e k).2.1.2),
    (fun k ↦ (e k).2.1.2.isCompact), ?_⟩⟩
  ext x
  constructor
  · intro hx
    rw [R.covers] at hx
    rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
    rcases hj with ⟨y, hy, hmap⟩
    let W : (F.obj (R.member j)).Opens :=
      ⨆ (V : (F.obj (R.member j)).affineOpens) (_ : V ∈ affineSets j),
        (V : (F.obj (R.member j)).Opens)
    have hW : (R.sourceOpen j : Set (F.obj (R.member j))) = (W : Set _) := by
      exact congrArg (fun V : (F.obj (R.member j)).Opens =>
        (V : Set (F.obj (R.member j))))
        (affineSets_covers j)
    have hy' : y ∈ ⋃ (V : (F.obj (R.member j)).affineOpens)
        (_ : V ∈ affineSets j), (V : Set (F.obj (R.member j))) := by
      have hy'' : y ∈ (W : Set (F.obj (R.member j))) := by
        rw [← hW]
        exact hy
      simpa [W, TopologicalSpace.Opens.coe_iSup] using hy''
    rcases Set.mem_iUnion.1 hy' with ⟨V, hyV⟩
    rcases Set.mem_iUnion.1 hyV with ⟨hV, hyV⟩
    let q : J := ⟨j, ⟨V, hV⟩⟩
    refine Set.mem_iUnion.2 ⟨e.symm q, ?_⟩
    rw [e.apply_symm_apply]
    refine ⟨y, ?_, hmap⟩
    exact hyV
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨k, hk⟩
    rcases hk with ⟨y, hy, hmap⟩
    let q := e k
    have hyR : y ∈ (R.sourceOpen q.1 : Set (F.obj (R.member q.1))) := by
      rw [affineSets_covers q.1]
      have hy' : y ∈ ⋃ (V : (F.obj (R.member q.1)).affineOpens)
          (_ : V ∈ affineSets q.1), (V : Set (F.obj (R.member q.1))) :=
        Set.mem_iUnion.2 ⟨q.2.1, Set.mem_iUnion.2 ⟨q.2.2, hy⟩⟩
      simpa only [TopologicalSpace.Opens.coe_iSup] using hy'
    rw [R.covers]
    refine Set.mem_iUnion.2 ⟨q.1, ?_⟩
    exact ⟨y, hyR, hmap⟩

/-- The finite affine ring diagram obtained over an affine base. -/
structure AffineRingReduction (A : CommRingCat.{u}) where
  cardinality : ℕ
  B : Fin cardinality → CommRingCat.{u}
  map : ∀ j, A ⟶ B j
  flat : ∀ j, RingHom.Flat (map j).hom
  spectra_cover :
    (⋃ j : Fin cardinality,
      Set.range (PrimeSpectrum.comap (map j).hom)) =
      (Set.univ : Set (PrimeSpectrum A))

/-- The geometric and algebraic records retained by affine reduction. -/
structure AffineFamilyRingReduction {S : Scheme.{u}} {I : Type v}
    (F : SchemeFamily S I) (U : S.Opens) where
  geometric : AffineFiniteFamilyReduction F U
  A : CommRingCat.{u}
  targetIso : S ≅ Spec A
  B : Fin geometric.cardinality → CommRingCat.{u}
  map : ∀ j, A ⟶ B j
  sourceMap : ∀ j, Spec (B j) ⟶ S
  sourceMap_eq : ∀ j,
    sourceMap j ≫ targetIso.hom = Spec.map (map j)
  sourceMap_range : ∀ j,
    Set.range (sourceMap j) =
      F.map (geometric.member j) ''
        (geometric.sourceOpen j : Set (F.obj (geometric.member j)))
  flat : ∀ j, RingHom.Flat (map j).hom
  spectra_cover :
    (⋃ j : Fin geometric.cardinality,
      Set.range (PrimeSpectrum.comap (map j).hom)) =
      (Set.univ : Set (PrimeSpectrum A))

noncomputable def AffineFamilyRingReduction.toRingReduction
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I} {U : S.Opens}
    (R : AffineFamilyRingReduction F U) : AffineRingReduction R.A where
  cardinality := R.geometric.cardinality
  B := R.B
  map := R.map
  flat := R.flat
  spectra_cover := R.spectra_cover

private theorem specMap_appTop_ΓSpecIso_eq
    {S : Scheme} {R : CommRingCat} [IsAffine S] (f : Spec R ⟶ S) :
    f ≫ S.isoSpec.hom =
      Spec.map (f.appTop ≫ (Scheme.ΓSpecIso R).hom) := by
  rw [← Scheme.isoSpec_hom_naturality f, Scheme.isoSpec_Spec_hom]
  rw [AlgebraicGeometry.Spec.map_comp]

theorem exists_affine_family_ring_reduction
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hS : IsAffine S) (hF : FpqcCoveringFamily F) :
    Nonempty (AffineFamilyRingReduction F (⊤ : S.Opens)) := by
  let : IsAffine S := hS
  obtain ⟨G⟩ := finiteFamilyReduction_affine_refinement
    (U := (⊤ : S.Opens)) isCompact_univ hF
  let A : CommRingCat := Γ(S, ⊤)
  let targetIso : S ≅ Spec A := S.isoSpec
  let B : Fin G.cardinality → CommRingCat := fun j ↦
    Γ(F.obj (G.member j), G.sourceOpen j)
  let sourceMap : ∀ j, Spec (B j) ⟶ S := fun j ↦
    (G.affine j).fromSpec ≫ F.map (G.member j)
  let map : ∀ j, A ⟶ B j := fun j ↦
    (sourceMap j).appTop ≫ (Scheme.ΓSpecIso (B j)).hom
  refine ⟨⟨G, A, targetIso, B, map, sourceMap, ?_, ?_, ?_, ?_⟩⟩
  · intro j
    change sourceMap j ≫ S.isoSpec.hom =
      Spec.map ((sourceMap j).appTop ≫ (Scheme.ΓSpecIso (B j)).hom)
    exact specMap_appTop_ΓSpecIso_eq (sourceMap j)
  · intro j
    ext s
    constructor
    · rintro ⟨z, hz⟩
      have hz' : (G.affine j).fromSpec z ∈
          (G.sourceOpen j : Set (F.obj (G.member j))) := by
        have hz'' : (G.affine j).fromSpec z ∈ Set.range (G.affine j).fromSpec :=
          ⟨z, rfl⟩
        rw [(G.affine j).range_fromSpec] at hz''
        exact hz''
      refine ⟨(G.affine j).fromSpec z, hz', ?_⟩
      simpa [sourceMap] using hz
    · rintro ⟨x, hx, hxs⟩
      have hx' : x ∈ Set.range (G.affine j).fromSpec := by
        rw [(G.affine j).range_fromSpec]
        exact hx
      rcases hx' with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      simpa [sourceMap, hz] using hxs
  · intro j
    let : Flat (F.map (G.member j)) := hF.flat (G.member j)
    let : Flat (sourceMap j) := by
      dsimp [sourceMap]
      infer_instance
    have : RingHom.Flat (sourceMap j).appTop.hom :=
      (sourceMap j).flat_appTop
    change RingHom.Flat
      ((Scheme.ΓSpecIso (B j)).hom.hom.comp (sourceMap j).appTop.hom)
    exact RingHom.Flat.comp (sourceMap j).flat_appTop
      (RingHom.Flat.of_bijective
        (ConcreteCategory.bijective_of_isIso (C := CommRingCat)
          (Scheme.ΓSpecIso (B j)).hom))
  · ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      let s : S := targetIso.inv z
      have hs : s ∈ ((⊤ : S.Opens) : Set S) := Set.mem_univ s
      rw [G.covers] at hs
      rcases Set.mem_iUnion.1 hs with ⟨j, hj⟩
      rcases hj with ⟨x, hx, hxs⟩
      have hx' : x ∈ Set.range (G.affine j).fromSpec := by
        rw [(G.affine j).range_fromSpec]
        exact hx
      rcases hx' with ⟨y, hy⟩
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      refine ⟨y, ?_⟩
      have hys : sourceMap j y = s := by
        change F.map (G.member j) ((G.affine j).fromSpec y) = s
        rw [hy]
        exact hxs
      have heq := congrArg (fun f : Spec (B j) ⟶ Spec A => f y)
        (show sourceMap j ≫ targetIso.hom = Spec.map (map j) from by
          change sourceMap j ≫ S.isoSpec.hom =
            Spec.map ((sourceMap j).appTop ≫ (Scheme.ΓSpecIso (B j)).hom)
          exact specMap_appTop_ΓSpecIso_eq (sourceMap j))
      change PrimeSpectrum.comap (map j).hom y = z
      change targetIso.hom (sourceMap j y) =
        PrimeSpectrum.comap (map j).hom y at heq
      rw [hys] at heq
      have hz : targetIso.hom s = z := by
        dsimp [s]
        have hz' := congrArg (fun f : Spec A ⟶ Spec A => f z)
          targetIso.inv_hom_id
        change targetIso.hom (targetIso.inv z) = z at hz'
        exact hz'
      rw [← hz]
      exact heq.symm

noncomputable def AffineRingReduction.productRingHom
    {A : CommRingCat.{u}} (R : AffineRingReduction A) :
    (A : Type u) →+* (∀ j, (R.B j : Type u)) :=
  RingHom.pi (fun j ↦ (R.map j).hom)

/-- The finite product of the selected modules, identified with their finite direct sum. -/
noncomputable def AffineRingReduction.productDirectSumLinearEquiv
    {A : CommRingCat.{u}} (R : AffineRingReduction A) :
    letI : ∀ j, Algebra (A : Type u) (R.B j : Type u) :=
      fun j ↦ (R.map j).hom.toAlgebra
    (∀ j, (R.B j : Type u)) ≃ₗ[(A : Type u)]
      DirectSum (Fin R.cardinality) (fun j ↦ (R.B j : Type u)) := by
  letI : ∀ j, Algebra (A : Type u) (R.B j : Type u) :=
    fun j ↦ (R.map j).hom.toAlgebra
  exact
    (DirectSum.linearEquivFunOnFintype (A : Type u) (Fin R.cardinality)
      (fun j ↦ (R.B j : Type u))).symm

@[simp]
theorem AffineRingReduction.productRingHom_apply
    {A : CommRingCat.{u}} (R : AffineRingReduction A)
    (a : A) (j : Fin R.cardinality) :
    R.productRingHom a j = R.map j a := by
  rfl

theorem AffineRingReduction.productRingHom_flat
    {A : CommRingCat.{u}} (R : AffineRingReduction A) :
    RingHom.Flat R.productRingHom := by
  let : ∀ j, Algebra (A : Type u) (R.B j : Type u) :=
    fun j ↦ (R.map j).hom.toAlgebra
  let : ∀ j, Module.Flat (A : Type u) (R.B j : Type u) :=
    fun j ↦ R.flat j
  change Module.Flat (A : Type u) (∀ j, (R.B j : Type u))
  apply Module.Flat.of_linearEquiv R.productDirectSumLinearEquiv

theorem AffineRingReduction.productRingHom_faithfullyFlat
    {A : CommRingCat.{u}} (R : AffineRingReduction A) :
    RingHom.FaithfullyFlat R.productRingHom := by
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  refine ⟨R.productRingHom_flat, ?_⟩
  intro p
  have hp : p ∈ ⋃ j : Fin R.cardinality,
      Set.range (PrimeSpectrum.comap (R.map j).hom) := by
    rw [R.spectra_cover]
    exact Set.mem_univ p
  rcases Set.mem_iUnion.1 hp with ⟨j, hj⟩
  rcases hj with ⟨q, hq⟩
  refine ⟨PrimeSpectrum.sigmaToPi (fun j ↦ (R.B j : Type u)) ⟨j, q⟩, ?_⟩
  rw [PrimeSpectrum.sigmaToPi_apply, ← PrimeSpectrum.comap_comp_apply]
  have heq : (Pi.evalRingHom (fun j ↦ (R.B j : Type u)) j).comp
      R.productRingHom = (R.map j).hom := by
    ext a
    rfl
  rw [heq, hq]

/-- The pairwise overlap ring retained for descent calculations. -/
noncomputable def AffineRingReduction.pairwiseOverlap
    {A : CommRingCat.{u}} (R : AffineRingReduction A)
    (i j : Fin R.cardinality) : Type u := by
  letI : Algebra (A : Type u) (R.B i : Type u) := (R.map i).hom.toAlgebra
  letI : Algebra (A : Type u) (R.B j : Type u) := (R.map j).hom.toAlgebra
  exact (R.B i : Type u) ⊗[(A : Type u)] (R.B j : Type u)

/-- The triple overlap ring retained for cocycle calculations. -/
noncomputable def AffineRingReduction.tripleOverlap
    {A : CommRingCat.{u}} (R : AffineRingReduction A)
    (i j k : Fin R.cardinality) : Type u := by
  letI : Algebra (A : Type u) (R.B i : Type u) := (R.map i).hom.toAlgebra
  letI : Algebra (A : Type u) (R.B j : Type u) := (R.map j).hom.toAlgebra
  letI : Algebra (A : Type u) (R.B k : Type u) := (R.map k).hom.toAlgebra
  exact
    ((R.B i : Type u) ⊗[(A : Type u)] (R.B j : Type u)) ⊗[(A : Type u)]
      (R.B k : Type u)

theorem affine_family_product_is_faithfullyFlat
    {S : Scheme.{u}} {I : Type v} {F : SchemeFamily S I}
    (hS : IsAffine S) (hF : FpqcCoveringFamily F) :
    ∃ (R : AffineFamilyRingReduction F (⊤ : S.Opens)),
      RingHom.FaithfullyFlat R.toRingReduction.productRingHom := by
  obtain ⟨R⟩ := exists_affine_family_ring_reduction hS hF
  exact ⟨R,
    AffineRingReduction.productRingHom_faithfullyFlat R.toRingReduction⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02
