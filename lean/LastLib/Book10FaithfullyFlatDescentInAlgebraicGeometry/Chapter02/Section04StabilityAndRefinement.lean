import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section01CoveringFamilies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02.Section02SingleCoversAndAffineReduction

/-!
## 2.4 Stability and refinement

Base change and composition are expressed at the family level.  A refinement is represented as a
second fpqc/fppf family over each member of a coarse family; its composite is the refined cover of
the original base.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v w v' u'

variable {S S' : Scheme.{u}} {I : Type v}

noncomputable def SchemeFamily.baseChange
    (F : SchemeFamily S I) (g : S' ⟶ S) : SchemeFamily S' I where
  obj := fun i ↦ pullback (F.map i) g
  map := fun i ↦ pullback.snd (F.map i) g

@[reassoc]
theorem SchemeFamily.baseChange_projection
    (F : SchemeFamily S I) (g : S' ⟶ S) (i : I) :
    pullback.fst (F.map i) g ≫ F.map i =
      (F.baseChange g).map i ≫ g := by
  change pullback.fst (F.map i) g ≫ F.map i =
    pullback.snd (F.map i) g ≫ g
  exact pullback.condition

theorem flat_family_baseChange
    (F : SchemeFamily S I) (g : S' ⟶ S)
    (hF : ∀ i, Flat (F.map i)) :
    ∀ i, Flat ((F.baseChange g).map i) := by
  intro i
  let : Flat (F.map i) := hF i
  change Flat (pullback.snd (F.map i) g)
  infer_instance

theorem locallyOfFinitePresentation_family_baseChange
    (F : SchemeFamily S I) (g : S' ⟶ S)
    (hF : ∀ i, LocallyOfFinitePresentation (F.map i)) :
    ∀ i, LocallyOfFinitePresentation ((F.baseChange g).map i) := by
  intro i
  let : LocallyOfFinitePresentation (F.map i) := hF i
  change LocallyOfFinitePresentation (pullback.snd (F.map i) g)
  infer_instance

theorem jointlySurjective_family_baseChange
    (F : SchemeFamily S I) (g : S' ⟶ S)
    (hjoint : JointlySurjective F) :
    JointlySurjective (F.baseChange g) := by
  intro s'
  obtain ⟨i, x, hx⟩ := hjoint (g s')
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x s' hx
  exact ⟨i, z, hz₂⟩

theorem jointlySurjective_family_baseChange_of_flat
    (F : SchemeFamily S I) (g : S' ⟶ S)
    (_hflat : ∀ i, Flat (F.map i)) (hjoint : JointlySurjective F) :
    JointlySurjective (F.baseChange g) := by
  exact jointlySurjective_family_baseChange F g hjoint

theorem fpqcCoveringFamily_baseChange
    {F : SchemeFamily S I} (g : S' ⟶ S)
    (hF : FpqcCoveringFamily F) :
    FpqcCoveringFamily (F.baseChange g) := by
  refine (fpqcCoveringFamily_iff_affine_reductions (F.baseChange g)).2 ?_
  refine ⟨flat_family_baseChange F g hF.flat, ?_⟩
  intro U hU
  have hlocal : ∀ x : U, ∃ (V : S.Opens) (W : S'.Opens),
      IsAffineOpen V ∧ IsAffineOpen W ∧ g (x : S') ∈ V ∧
        (x : S') ∈ W ∧ W ≤ U ⊓ g ⁻¹ᵁ V := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (g (x : S'))) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      S'.isBasis_affineOpens.exists_subset_of_mem_open
        (a := (x : S'))
          (show (x : S') ∈ (U ⊓ g ⁻¹ᵁ V : S'.Opens) from ⟨x.property, hxV⟩)
          (U ⊓ g ⁻¹ᵁ V).isOpen
    exact ⟨V, W, hV, hW, hxV, hxW, hWU⟩
  choose V W hV hW hxV hxW hWU using hlocal
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover
    (fun x : U => (W x : Set S')) (fun x => (W x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxW ⟨x, hx⟩⟩)
  let J := {x : U // x ∈ t}
  let : Fintype J := Fintype.ofFinite J
  let R : ∀ j : J, AffineFiniteFamilyReduction F (V j.1) :=
    fun j => (finiteFamilyReduction_affine_refinement (hV j.1).isCompact hF).some
  let K := Σ j : J, Fin (R j).cardinality
  let : Fintype K := Fintype.ofFinite K
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let sourceOpen : ∀ q : K,
      ((F.baseChange g).obj ((R q.1).member q.2)).Opens := fun q ↦
    (pullback.fst (F.map ((R q.1).member q.2)) g ⁻¹ᵁ (R q.1).sourceOpen q.2 ⊓
      pullback.snd (F.map ((R q.1).member q.2)) g ⁻¹ᵁ (W q.1) :
        (pullback (F.map ((R q.1).member q.2)) g).Opens)
  refine ⟨Fintype.card K,
    (fun l ↦ (R (e.symm l).1).member (e.symm l).2),
    (fun l ↦ sourceOpen (e.symm l)), ?_, ?_⟩
  · intro l
    let q := e.symm l
    dsimp [sourceOpen]
    apply IsAffineOpen.isCompact_pullback_inf ((R q.1).affine q.2)
      ((hW q.1).isCompact) (hV q.1)
    · intro y hy
      change F.map ((R q.1).member q.2) y ∈ (V q.1 : Set S)
      rw [(R q.1).covers]
      exact Set.mem_iUnion.2 ⟨q.2, ⟨y, hy, rfl⟩⟩
    · exact (hWU q.1).trans inf_le_right
  · ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 (ht hx) with ⟨x₀, hx₀⟩
      rcases Set.mem_iUnion.1 hx₀ with ⟨hx₀t, hxW₀⟩
      let j : J := ⟨x₀, hx₀t⟩
      have hxWj : x ∈ W j.1 := hxW₀
      have hxVj : g x ∈ V j.1 := by
        exact (hWU j.1).trans inf_le_right hxWj
      have hxR : g x ∈ ⋃ k : Fin (R j).cardinality,
          F.map ((R j).member k) '' ((R j).sourceOpen k : Set _) := by
        rw [← (R j).covers]
        exact hxVj
      rcases Set.mem_iUnion.1 hxR with ⟨k, hk⟩
      rcases hk with ⟨y, hy, hmap⟩
      obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback y x hmap
      refine Set.mem_iUnion.2 ⟨e ⟨j, k⟩, ?_⟩
      rw [e.symm_apply_apply]
      refine ⟨z, ?_, ?_⟩
      · change z ∈
          pullback.fst (F.map ((R j).member k)) g ⁻¹ᵁ (R j).sourceOpen k ⊓
            pullback.snd (F.map ((R j).member k)) g ⁻¹ᵁ (W j)
        constructor
        · change pullback.fst (F.map ((R j).member k)) g z ∈ (R j).sourceOpen k
          rw [hz₁]
          exact hy
        · change pullback.snd (F.map ((R j).member k)) g z ∈ W j
          rw [hz₂]
          exact hxWj
      · exact hz₂
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨l, hl⟩
      let q := e.symm l
      rcases hl with ⟨z, hz, hzx⟩
      have hzW : pullback.snd (F.map ((R q.1).member q.2)) g z ∈ W q.1 := by
        change z ∈
          pullback.fst (F.map ((R q.1).member q.2)) g ⁻¹ᵁ (R q.1).sourceOpen q.2 ⊓
            pullback.snd (F.map ((R q.1).member q.2)) g ⁻¹ᵁ (W q.1) at hz
        exact hz.2
      change pullback.snd (F.map ((R q.1).member q.2)) g z = x at hzx
      rw [← hzx]
      exact (hWU q.1 hzW).1

theorem fppfCoveringFamily_baseChange
    {F : SchemeFamily S I} (g : S' ⟶ S)
    (hF : FppfCoveringFamily F) :
    FppfCoveringFamily (F.baseChange g) := by
  refine ⟨jointlySurjective_family_baseChange F g hF.jointly_surjective,
    flat_family_baseChange F g hF.flat,
    locallyOfFinitePresentation_family_baseChange F g
      hF.locally_of_finite_presentation⟩

/-- A second-stage family covering each member of a coarse family. -/
structure FamilyTower (F : SchemeFamily S I) (J : I → Type w) where
  inner : ∀ i, SchemeFamily (F.obj i) (J i)

noncomputable def FamilyTower.composite
    {F : SchemeFamily S I} {J : I → Type w}
    (G : FamilyTower F J) : SchemeFamily S (Σ i, J i) where
  obj := fun ij ↦ (G.inner ij.1).obj ij.2
  map := fun ij ↦ (G.inner ij.1).map ij.2 ≫ F.map ij.1

@[simp]
theorem FamilyTower.composite_map
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (ij : Σ i, J i) :
    (G.composite.map ij) = (G.inner ij.1).map ij.2 ≫ F.map ij.1 := by
  rfl

private theorem FamilyTower.composite_obj
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (ij : Σ i, J i) :
    G.composite.obj ij = (G.inner ij.1).obj ij.2 := by
  rfl

private noncomputable def FamilyTower.explicitDescentData
    {P : Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat.{v', u'}}
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (D : P.DescentData G.composite.map) :
    P.DescentData
      (fun ij : Σ i, J i => (G.inner ij.1).map ij.2 ≫ F.map ij.1) := by
  change P.DescentData G.composite.map
  exact D

private noncomputable def FamilyTower.compositePullFunctor
    {P : Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat.{v', u'}}
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J) :
    P.DescentData F.map ⥤ P.DescentData G.composite.map :=
  (Pseudofunctor.DescentData.pullFunctor P
    (p := 𝟙 S) (f := F.map)
    (X' := fun ij : Σ i, J i => (G.inner ij.1).obj ij.2)
    (f' := fun ij => (G.inner ij.1).map ij.2 ≫ F.map ij.1)
    (α := fun ij => ij.1)
    (p' := fun ij => (G.inner ij.1).map ij.2)
    (fun ij => by simp))

private theorem FamilyTower.inner_sieve_eq_baseChange_id
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J) (i : I) :
    Sieve.ofArrows (G.inner i).obj (G.inner i).map =
      Sieve.ofArrows ((G.inner i).baseChange (𝟙 (F.obj i))).obj
        ((G.inner i).baseChange (𝟙 (F.obj i))).map := by
  apply le_antisymm
  · intro X f hf
    rw [Sieve.mem_ofArrows_iff] at hf ⊢
    rcases hf with ⟨j, a, rfl⟩
    refine ⟨j, pullback.lift a (a ≫ (G.inner i).map j), ?_⟩
    change a ≫ (G.inner i).map j =
      pullback.lift a (a ≫ (G.inner i).map j) ≫
        pullback.snd ((G.inner i).map j) (𝟙 (F.obj i))
    rw [pullback.lift_snd]
  · intro X f hf
    rw [Sieve.mem_ofArrows_iff] at hf ⊢
    rcases hf with ⟨j, a, rfl⟩
    dsimp [SchemeFamily.baseChange] at a
    refine ⟨j, a ≫ pullback.fst ((G.inner i).map j) (𝟙 (F.obj i)), ?_⟩
    change a ≫ pullback.snd ((G.inner i).map j) (𝟙 (F.obj i)) =
      (a ≫ pullback.fst ((G.inner i).map j) (𝟙 (F.obj i))) ≫
        (G.inner i).map j
    rw [Category.assoc, pullback.condition]
    simp

private theorem FamilyTower.inner_descentData_isEquivalence
    {P : Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat.{v', u'}}
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J) (i : I)
    (hinner : ∀ (X : Scheme.{u}) (g : X ⟶ F.obj i),
      (P.toDescentData ((G.inner i).baseChange g).map).IsEquivalence) :
    (P.toDescentData (G.inner i).map).IsEquivalence := by
  exact (Pseudofunctor.DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
    P (G.inner i).map ((G.inner i).baseChange (𝟙 (F.obj i))).map
    (G.inner_sieve_eq_baseChange_id i)).2 (hinner _ (𝟙 (F.obj i)))

private noncomputable def FamilyTower.restrictedDescentData
    {P : Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat.{v', u'}}
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (D : P.DescentData G.composite.map) (i : I) :
    P.DescentData (G.inner i).map where
  obj j := D.obj ⟨i, j⟩
  hom Y q j₁ j₂ f₁ f₂ hf₁ hf₂ :=
    D.hom (q ≫ F.map i) (i₁ := ⟨i, j₁⟩) (i₂ := ⟨i, j₂⟩) f₁ f₂
      (by
        change f₁ ≫ (G.inner i).map j₁ ≫ F.map i = q ≫ F.map i
        simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map i) hf₁)
      (by
        change f₂ ≫ (G.inner i).map j₂ ≫ F.map i = q ≫ F.map i
        simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map i) hf₂)
  pullHom_hom Y' Y g q q' hq j₁ j₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    exact D.pullHom_hom (i₁ := ⟨i, j₁⟩) (i₂ := ⟨i, j₂⟩) g
      (q ≫ F.map i) (q' ≫ F.map i)
      (by simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map i) hq)
      f₁ f₂
      (by
        change f₁ ≫ (G.inner i).map j₁ ≫ F.map i = q ≫ F.map i
        simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map i) hf₁)
      (by
        change f₂ ≫ (G.inner i).map j₂ ≫ F.map i = q ≫ F.map i
        simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map i) hf₂)
      gf₁ gf₂ hgf₁ hgf₂
  hom_self Y q j g hg := by
    exact D.hom_self (i := ⟨i, j⟩) (q ≫ F.map i) g (by
      change g ≫ (G.inner i).map j ≫ F.map i = q ≫ F.map i
      simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map i) hg)
  hom_comp Y q j₁ j₂ j₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    exact D.hom_comp (i₁ := ⟨i, j₁⟩) (i₂ := ⟨i, j₂⟩) (i₃ := ⟨i, j₃⟩)
      (q ≫ F.map i) f₁ f₂ f₃
      (by
        change f₁ ≫ (G.inner i).map j₁ ≫ F.map i = q ≫ F.map i
        simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map i) hf₁)
      (by
        change f₂ ≫ (G.inner i).map j₂ ≫ F.map i = q ≫ F.map i
        simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map i) hf₂)
      (by
        change f₃ ≫ (G.inner i).map j₃ ≫ F.map i = q ≫ F.map i
        simpa only [Category.assoc] using congrArg (fun k => k ≫ F.map i) hf₃)

private noncomputable def FamilyTower.restrictedBaseChange
    {P : Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat.{v', u'}}
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (D : P.DescentData G.composite.map) (i : I) {X : Scheme.{u}}
    (g : X ⟶ F.obj i) :
    P.DescentData ((G.inner i).baseChange g).map :=
  (Pseudofunctor.DescentData.pullFunctor P
    (p := g) (f := (G.inner i).map)
    (X' := fun j => ((G.inner i).baseChange g).obj j)
    (f' := ((G.inner i).baseChange g).map)
    (α := fun j => j)
    (p' := fun j => pullback.fst ((G.inner i).map j) g)
    (fun j => by
      change pullback.fst ((G.inner i).map j) g ≫ (G.inner i).map j =
        pullback.snd ((G.inner i).map j) g ≫ g
      exact pullback.condition)
    ).obj (G.restrictedDescentData D i)

private noncomputable def FamilyTower.restrictedBaseChangeIso
    {P : Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat.{v', u'}}
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (D : P.DescentData G.composite.map) (i : I) {X : Scheme.{u}}
    (g : X ⟶ F.obj i) (M : P.obj (.mk (Opposite.op (F.obj i))))
    (α : (P.toDescentData (G.inner i).map).obj M ≅
      G.restrictedDescentData D i) :
    (P.toDescentData ((G.inner i).baseChange g).map).obj
        ((P.map g.op.toLoc).toFunctor.obj M) ≅
      G.restrictedBaseChange D i g := by
  let e := Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso P
    (f := (G.inner i).map) (f' := ((G.inner i).baseChange g).map)
    (p := g) (α := fun j => j)
    (p' := fun j => pullback.fst ((G.inner i).map j) g)
    (fun j => by
      change pullback.fst ((G.inner i).map j) g ≫ (G.inner i).map j =
        pullback.snd ((G.inner i).map j) g ≫ g
      exact pullback.condition)
  exact (e.app M).symm ≪≫
    (Functor.mapIso
      (Pseudofunctor.DescentData.pullFunctor P
        (p := g) (f := (G.inner i).map)
        (X' := fun j => ((G.inner i).baseChange g).obj j)
        (f' := ((G.inner i).baseChange g).map)
        (α := fun j => j)
        (p' := fun j => pullback.fst ((G.inner i).map j) g)
        (fun j => by
          change pullback.fst ((G.inner i).map j) g ≫ (G.inner i).map j =
            pullback.snd ((G.inner i).map j) g ≫ g
          exact pullback.condition)) α)

set_option maxHeartbeats 10000000 in
private noncomputable def FamilyTower.crossHom
    {P : Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat.{v', u'}}
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (D : P.DescentData G.composite.map) (i k : I) (j : J i)
    {X : Scheme.{u}} (a : X ⟶ (G.inner i).obj j) (g : X ⟶ F.obj k)
    (ha : a ≫ (G.inner i).map j ≫ F.map i = g ≫ F.map k)
    (M : ∀ i, P.obj (.mk (Opposite.op (F.obj i))))
    (α : ∀ i, (P.toDescentData (G.inner i).map).obj (M i) ≅
      G.restrictedDescentData D i)
    (hK : (P.toDescentData ((G.inner k).baseChange g).map).IsEquivalence) :
    (P.map (a ≫ (G.inner i).map j).op.toLoc).toFunctor.obj (M i) ⟶
      (P.map g.op.toLoc).toFunctor.obj (M k) := by
  let D' : P.DescentData
      (fun ij : Σ i, J i => (G.inner ij.1).map ij.2 ≫ F.map ij.1) :=
    G.explicitDescentData D
  let K := P.toDescentData (fun l ↦ pullback.snd ((G.inner k).map l) g)
  let source :=
    (P.map (((G.inner i).map j).op.toLoc ≫ a.op.toLoc)).toFunctor.obj (M i)
  let target := (P.map g.op.toLoc).toFunctor.obj (M k)
  let : K.IsEquivalence := hK
  let R :=
    (Pseudofunctor.DescentData.pullFunctor P
      (p := g) (f := (G.inner k).map)
      (X' := fun l ↦ pullback ((G.inner k).map l) g)
      (f' := fun l ↦ pullback.snd ((G.inner k).map l) g)
      (α := fun l ↦ l)
      (p' := fun l ↦ pullback.fst ((G.inner k).map l) g)
      (fun l ↦ by
        change pullback.fst ((G.inner k).map l) g ≫ (G.inner k).map l =
          pullback.snd ((G.inner k).map l) g ≫ g
        exact pullback.condition)).obj (G.restrictedDescentData D k)
  let e := G.restrictedBaseChangeIso D k g (M k) (α k)
  let alphaHom : ∀ (i : I) (j : J i),
      (P.map ((G.inner i).map j).op.toLoc).toFunctor.obj (M i) ⟶
        (G.restrictedDescentData D i).obj j := fun i j ↦ by
    exact (α i).hom.hom j
  let gammaHom : ∀ l,
      (P.map (pullback.snd ((G.inner k).map l) g).op.toLoc).toFunctor.obj
          ((P.map (((G.inner i).map j).op.toLoc ≫ a.op.toLoc)).toFunctor.obj (M i)) ⟶
        (P.map (pullback.fst ((G.inner k).map l) g).op.toLoc).toFunctor.obj
          ((G.restrictedDescentData D k).obj l) := fun l ↦ by
    let f₁ := pullback.fst ((G.inner k).map l) g
    let f₂ := pullback.snd ((G.inner k).map l) g
    let c := f₂ ≫ a ≫ (G.inner i).map j
    let d := f₂ ≫ a
    have hsource :
        d ≫ (G.inner i).map j ≫ F.map i =
          f₂ ≫ g ≫ F.map k := by
      simpa [d, Category.assoc] using congrArg (fun h => f₂ ≫ h) ha
    have htarget :
        f₁ ≫ (G.inner k).map l ≫ F.map k =
          f₂ ≫ g ≫ F.map k := by
      change
        (pullback.fst ((G.inner k).map l) g ≫ (G.inner k).map l) ≫ F.map k =
          (pullback.snd ((G.inner k).map l) g ≫ g) ≫ F.map k
      rw [pullback.condition]
    exact
      (P.mapComp' (a ≫ (G.inner i).map j).op.toLoc f₂.op.toLoc
        (f₂ ≫ a ≫ (G.inner i).map j).op.toLoc
        (by simpa only [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app
        (M i) ≫
      (P.mapComp' ((G.inner i).map j).op.toLoc (a.op.toLoc ≫ f₂.op.toLoc)
          (f₂ ≫ a ≫ (G.inner i).map j).op.toLoc
          (by simpa only [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc])).hom.toNatTrans.app
        (M i) ≫
        (P.map d.op.toLoc).toFunctor.map (alphaHom i j) ≫
        D'.hom (f₂ ≫ g ≫ F.map k) (i₁ := ⟨i, j⟩) (i₂ := ⟨k, l⟩)
          d f₁ hsource htarget
  let gamma : K.obj source ⟶ R :=
    set_option backward.isDefEq.respectTransparency.types false in
    set_option backward.isDefEq.respectTransparency false in by
    refine { hom := gammaHom, comm := ?_ }
    intro Y q l₁ l₂ f₁ f₂ hf₁ hf₂
    let r₁ : pullback ((G.inner k).map l₁) g ⟶ (G.inner k).obj l₁ :=
      pullback.fst ((G.inner k).map l₁) g
    let r₂ : pullback ((G.inner k).map l₂) g ⟶ (G.inner k).obj l₂ :=
      pullback.fst ((G.inner k).map l₂) g
    dsimp [R, K, source, Pseudofunctor.toDescentData,
      Pseudofunctor.DescentData.ofObj, FamilyTower.restrictedBaseChange,
      Pseudofunctor.DescentData.pullFunctor,
      Pseudofunctor.DescentData.pullFunctorObj]
    rw [Pseudofunctor.DescentData.pullFunctorObjHom_eq _ _ _ _ _
      (q ≫ g) (f₁ ≫ r₁) (f₂ ≫ r₂)]
    rw [Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom_assoc
      (gammaHom l₁) f₁ q (f₁ ≫ r₁) hf₁ (by simp [r₁]),
      Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (gammaHom l₂) f₂ q (f₂ ≫ r₂) hf₂ (by simp [r₂])]
    simp only [Category.assoc]
    dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
    dsimp [gammaHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (D'.hom (pullback.snd ((G.inner k).map l₁) g ≫ g ≫ F.map k)
        (i₁ := ⟨i, j⟩) (i₂ := ⟨k, l₁⟩)
        (pullback.snd ((G.inner k).map l₁) g ≫ a) r₁
        (by
          change
            (pullback.snd ((G.inner k).map l₁) g ≫ a) ≫
                (G.inner i).map j ≫ F.map i =
              (pullback.snd ((G.inner k).map l₁) g ≫ g) ≫ F.map k
          simpa [Category.assoc] using
            congrArg (fun h => pullback.snd ((G.inner k).map l₁) g ≫ h) ha)
        (by
          simpa only [r₁, Category.assoc] using
            congrArg (fun h => h ≫ F.map k)
              (pullback.condition :
                pullback.fst ((G.inner k).map l₁) g ≫ (G.inner k).map l₁ =
                  pullback.snd ((G.inner k).map l₁) g ≫ g))
        )
      f₁ (f₁ ≫ (pullback.snd ((G.inner k).map l₁) g ≫ a)) (f₁ ≫ r₁)
      rfl rfl,
      Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
      (D'.hom (pullback.snd ((G.inner k).map l₂) g ≫ g ≫ F.map k)
        (i₁ := ⟨i, j⟩) (i₂ := ⟨k, l₂⟩)
        (pullback.snd ((G.inner k).map l₂) g ≫ a) r₂
        (by
          change
            (pullback.snd ((G.inner k).map l₂) g ≫ a) ≫
                (G.inner i).map j ≫ F.map i =
              (pullback.snd ((G.inner k).map l₂) g ≫ g) ≫ F.map k
          simpa [Category.assoc] using
            congrArg (fun h => pullback.snd ((G.inner k).map l₂) g ≫ h) ha)
        (by
          simpa only [r₂, Category.assoc] using
            congrArg (fun h => h ≫ F.map k)
              (pullback.condition :
                pullback.fst ((G.inner k).map l₂) g ≫ (G.inner k).map l₂ =
                  pullback.snd ((G.inner k).map l₂) g ≫ g))
        )
      f₂ (f₂ ≫ (pullback.snd ((G.inner k).map l₂) g ≫ a)) (f₂ ≫ r₂)
      rfl rfl]
    dsimp [r₁, r₂]
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
      Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
    rw [D'.pullHom_hom (i₁ := ⟨i, j⟩) (i₂ := ⟨k, l₁⟩) f₁
      (pullback.snd ((G.inner k).map l₁) g ≫ g ≫ F.map k)
      (q ≫ g ≫ F.map k)
      (by
        simpa only [Category.assoc] using
          congrArg (fun h => h ≫ g ≫ F.map k) hf₁)
      (pullback.snd ((G.inner k).map l₁) g ≫ a) r₁
      (by
        change
          (pullback.snd ((G.inner k).map l₁) g ≫ a) ≫
              (G.inner i).map j ≫ F.map i =
            (pullback.snd ((G.inner k).map l₁) g ≫ g) ≫ F.map k
        simpa [Category.assoc] using
          congrArg (fun h => pullback.snd ((G.inner k).map l₁) g ≫ h) ha)
      (by
        simpa only [r₁, Category.assoc] using
          congrArg (fun h => h ≫ F.map k)
            (pullback.condition :
              pullback.fst ((G.inner k).map l₁) g ≫ (G.inner k).map l₁ =
                pullback.snd ((G.inner k).map l₁) g ≫ g))
      (f₁ ≫ (pullback.snd ((G.inner k).map l₁) g ≫ a)) (f₁ ≫ r₁)
      rfl rfl,
      D'.pullHom_hom (i₁ := ⟨i, j⟩) (i₂ := ⟨k, l₂⟩) f₂
      (pullback.snd ((G.inner k).map l₂) g ≫ g ≫ F.map k)
      (q ≫ g ≫ F.map k)
      (by
        simpa only [Category.assoc] using
          congrArg (fun h => h ≫ g ≫ F.map k) hf₂)
      (pullback.snd ((G.inner k).map l₂) g ≫ a) r₂
      (by
        change
          (pullback.snd ((G.inner k).map l₂) g ≫ a) ≫
              (G.inner i).map j ≫ F.map i =
            (pullback.snd ((G.inner k).map l₂) g ≫ g) ≫ F.map k
        simpa [Category.assoc] using
          congrArg (fun h => pullback.snd ((G.inner k).map l₂) g ≫ h) ha)
      (by
        simpa only [r₂, Category.assoc] using
          congrArg (fun h => h ≫ F.map k)
            (pullback.condition :
              pullback.fst ((G.inner k).map l₂) g ≫ (G.inner k).map l₂ =
                pullback.snd ((G.inner k).map l₂) g ≫ g))
      (f₂ ≫ (pullback.snd ((G.inner k).map l₂) g ≫ a)) (f₂ ≫ r₂)
      rfl rfl]
    simp only [r₁, r₂]
    have hcomp := D'.hom_comp (i₁ := ⟨i, j⟩) (i₂ := ⟨k, l₁⟩) (i₃ := ⟨k, l₂⟩)
      (q ≫ g ≫ F.map k)
      (f₁ ≫ pullback.snd ((G.inner k).map l₁) g ≫ a)
      (f₁ ≫ pullback.fst ((G.inner k).map l₁) g)
      (f₂ ≫ pullback.fst ((G.inner k).map l₂) g)
      (by
        change
          (f₁ ≫ pullback.snd ((G.inner k).map l₁) g ≫ a) ≫
              (G.inner i).map j ≫ F.map i =
            q ≫ g ≫ F.map k
        calc
          (f₁ ≫ pullback.snd ((G.inner k).map l₁) g ≫ a) ≫
                (G.inner i).map j ≫ F.map i =
              f₁ ≫ pullback.snd ((G.inner k).map l₁) g ≫
                (a ≫ (G.inner i).map j ≫ F.map i) := by
                simp [Category.assoc]
          _ = f₁ ≫ pullback.snd ((G.inner k).map l₁) g ≫
                (g ≫ F.map k) := by rw [ha]
          _ = q ≫ g ≫ F.map k := by
            simpa only [Category.assoc] using
              congrArg (fun h => h ≫ g ≫ F.map k) hf₁)
      (by
        change
          (f₁ ≫ pullback.fst ((G.inner k).map l₁) g) ≫
              (G.inner k).map l₁ ≫ F.map k =
            q ≫ g ≫ F.map k
        calc
          (f₁ ≫ pullback.fst ((G.inner k).map l₁) g) ≫
                (G.inner k).map l₁ ≫ F.map k =
              f₁ ≫
                (pullback.fst ((G.inner k).map l₁) g ≫
                  (G.inner k).map l₁) ≫ F.map k := by
                simp [Category.assoc]
          _ = f₁ ≫
                (pullback.snd ((G.inner k).map l₁) g ≫ g) ≫ F.map k := by
                rw [pullback.condition]
          _ = q ≫ g ≫ F.map k := by
            simpa only [Category.assoc] using
              congrArg (fun h => h ≫ g ≫ F.map k) hf₁)
      (by
        change
          (f₂ ≫ pullback.fst ((G.inner k).map l₂) g) ≫
              (G.inner k).map l₂ ≫ F.map k =
            q ≫ g ≫ F.map k
        calc
          (f₂ ≫ pullback.fst ((G.inner k).map l₂) g) ≫
                (G.inner k).map l₂ ≫ F.map k =
              f₂ ≫
                (pullback.fst ((G.inner k).map l₂) g ≫
                  (G.inner k).map l₂) ≫ F.map k := by
                simp [Category.assoc]
          _ = f₂ ≫
                (pullback.snd ((G.inner k).map l₂) g ≫ g) ≫ F.map k := by
                rw [pullback.condition]
          _ = q ≫ g ≫ F.map k := by
            simpa only [Category.assoc] using
              congrArg (fun h => h ≫ g ≫ F.map k) hf₂)
    have hrestricted₁ :
        (f₁ ≫ r₁) ≫ (G.inner k).map l₁ = q ≫ g := by
      calc
        (f₁ ≫ r₁) ≫ (G.inner k).map l₁ =
            f₁ ≫ (r₁ ≫ (G.inner k).map l₁) := by simp [Category.assoc]
        _ = f₁ ≫ (pullback.snd ((G.inner k).map l₁) g ≫ g) := by
          dsimp [r₁]
          rw [pullback.condition]
        _ = q ≫ g := by
          simpa only [Category.assoc] using congrArg (fun h => h ≫ g) hf₁
    have hrestricted₂ :
        (f₂ ≫ r₂) ≫ (G.inner k).map l₂ = q ≫ g := by
      calc
        (f₂ ≫ r₂) ≫ (G.inner k).map l₂ =
            f₂ ≫ (r₂ ≫ (G.inner k).map l₂) := by simp [Category.assoc]
        _ = f₂ ≫ (pullback.snd ((G.inner k).map l₂) g ≫ g) := by
          dsimp [r₂]
          rw [pullback.condition]
        _ = q ≫ g := by
          simpa only [Category.assoc] using congrArg (fun h => h ≫ g) hf₂
    have hrestricted₁' :
        (f₁ ≫ r₁) ≫ ((G.inner k).map l₁ ≫ F.map k) =
          (q ≫ g) ≫ F.map k := by
      calc
        (f₁ ≫ r₁) ≫ ((G.inner k).map l₁ ≫ F.map k) =
            ((f₁ ≫ r₁) ≫ (G.inner k).map l₁) ≫ F.map k :=
          (Category.assoc _ _ _).symm
        _ = (q ≫ g) ≫ F.map k := congrArg (fun h => h ≫ F.map k) hrestricted₁
    have hrestricted₂' :
        (f₂ ≫ r₂) ≫ ((G.inner k).map l₂ ≫ F.map k) =
          (q ≫ g) ≫ F.map k := by
      calc
        (f₂ ≫ r₂) ≫ ((G.inner k).map l₂ ≫ F.map k) =
            ((f₂ ≫ r₂) ≫ (G.inner k).map l₂) ≫ F.map k :=
          (Category.assoc _ _ _).symm
        _ = (q ≫ g) ≫ F.map k := congrArg (fun h => h ≫ F.map k) hrestricted₂
    have hrestricted :
        (G.restrictedDescentData D k).hom (q ≫ g) (f₁ ≫ r₁) (f₂ ≫ r₂)
            hrestricted₁ hrestricted₂ =
          D'.hom ((q ≫ g) ≫ F.map k) (i₁ := ⟨k, l₁⟩) (i₂ := ⟨k, l₂⟩)
            (f₁ ≫ r₁) (f₂ ≫ r₂)
            hrestricted₁' hrestricted₂' := by
      rfl
    rw [hrestricted]
  apply K.preimage
  exact gamma ≫ e.inv

/- If every base change of every second-stage descent functor is an equivalence, refining a family
   does not change the effectiveness question for the outer family.  The base-change clause is
   needed to descend the comparison morphisms on the outer overlaps. -/
theorem familyTower_descentData_effectivity_invariant_under_refinement
    {P : Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat.{v', u'}}
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (hinner : ∀ (i : I) (X : Scheme.{u}) (g : X ⟶ F.obj i),
      (P.toDescentData ((G.inner i).baseChange g).map).IsEquivalence) :
      (P.toDescentData F.map).IsEquivalence ↔
      (P.toDescentData G.composite.map).IsEquivalence := by
  let H := G.compositePullFunctor (P := P)
  have hHfaithful : H.Faithful := by
    constructor
    intro D₁ D₂ φ ψ hφψ
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    let : (P.toDescentData (G.inner i).map).IsEquivalence :=
      G.inner_descentData_isEquivalence i (fun X g => hinner i X g)
    apply (P.toDescentData (G.inner i).map).map_injective
    apply Pseudofunctor.DescentData.hom_ext
    intro j
    have h := congrArg (fun θ => θ.hom ⟨i, j⟩) hφψ
    change (P.map ((G.inner i).map j).op.toLoc).toFunctor.map (φ.hom i) =
      (P.map ((G.inner i).map j).op.toLoc).toFunctor.map (ψ.hom i)
    exact h
  let e : (P.toDescentData F.map) ⋙ H ≅ P.toDescentData G.composite.map :=
    Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso P
      (f := F.map) (f' := G.composite.map) (p := 𝟙 S)
      (α := fun ij : Σ i, J i => ij.1)
      (p' := fun ij : Σ i, J i => (G.inner ij.1).map ij.2)
      (fun ij => by
        simp [FamilyTower.composite]) ≪≫
      Functor.isoWhiskerRight (Cat.Hom.toNatIso (P.mapId _)) _ ≪≫
      Functor.leftUnitor _
  have htarget_of_hH : H.IsEquivalence →
      ((P.toDescentData F.map).IsEquivalence ↔
      (P.toDescentData G.composite.map).IsEquivalence) := by
    intro hH
    let : H.IsEquivalence := hH
    constructor
    · intro hF
      let : (P.toDescentData F.map).IsEquivalence := hF
      exact Functor.isEquivalence_of_iso e
    · intro hG
      let : (P.toDescentData G.composite.map).IsEquivalence := hG
      have hcomp : (P.toDescentData F.map ⋙ H).IsEquivalence :=
        Functor.isEquivalence_of_iso e.symm
      exact Functor.isEquivalence_of_comp_right (P.toDescentData F.map) H
  exact htarget_of_hH (by
    let : H.Faithful := hHfaithful
    refine { faithful := hHfaithful, full := ?_, essSurj := ?_ }
    · constructor
      intro D₁ D₂ φ
      sorry
    · sorry)

theorem fpqcFamilyTower_composite
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (hF : FpqcCoveringFamily F)
    (hG : ∀ i, FpqcCoveringFamily (G.inner i)) :
    FpqcCoveringFamily G.composite := by
  refine ⟨?_, ?_⟩
  · intro ij
    let : Flat ((G.inner ij.1).map ij.2) := (hG ij.1).flat ij.2
    let : Flat (F.map ij.1) := hF.flat ij.1
    change Flat ((G.inner ij.1).map ij.2 ≫ F.map ij.1)
    infer_instance
  · intro U hU
    obtain ⟨R⟩ := hF.finite_reduction U hU
    let Q : ∀ j : Fin R.cardinality,
        FiniteFamilyReduction (G.inner (R.member j)) (R.sourceOpen j) :=
      fun j => (hG (R.member j)).finite_reduction (R.sourceOpen j)
        (R.quasiCompact j) |>.some
    let K := Σ j : Fin R.cardinality, Fin (Q j).cardinality
    let : Fintype K := Fintype.ofFinite K
    let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
    refine ⟨Fintype.card K,
      (fun l ↦ ⟨R.member (e.symm l).1,
        (Q (e.symm l).1).member (e.symm l).2⟩),
      (fun l ↦ (Q (e.symm l).1).sourceOpen (e.symm l).2),
      (fun l ↦ (Q (e.symm l).1).quasiCompact (e.symm l).2), ?_⟩
    ext x
    constructor
    · intro hx
      rw [R.covers] at hx
      rcases Set.mem_iUnion.1 hx with ⟨j, hj⟩
      rcases hj with ⟨y, hy, hxy⟩
      have hy' : y ∈ ⋃ k : Fin (Q j).cardinality,
          (G.inner (R.member j)).map ((Q j).member k) ''
            ((Q j).sourceOpen k : Set ((G.inner (R.member j)).obj ((Q j).member k))) := by
        rw [← (Q j).covers]
        exact hy
      rcases Set.mem_iUnion.1 hy' with ⟨k, hk⟩
      refine Set.mem_iUnion.2 ⟨e ⟨j, k⟩, ?_⟩
      rw [e.symm_apply_apply]
      rcases hk with ⟨z, hz, hzy⟩
      refine ⟨z, hz, ?_⟩
      change F.map (R.member j) ((G.inner (R.member j)).map ((Q j).member k) z) = x
      rw [hzy, hxy]
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨l, hl⟩
      let q := e.symm l
      rcases hl with ⟨z, hz, hzx⟩
      have hy : (G.inner (R.member q.1)).map ((Q q.1).member q.2) z ∈
          (R.sourceOpen q.1 : Set (F.obj (R.member q.1))) := by
        rw [(Q q.1).covers]
        exact Set.mem_iUnion.2 ⟨q.2, ⟨z, hz, rfl⟩⟩
      have hxy : x ∈ (U : Set S) := by
        rw [R.covers]
        exact Set.mem_iUnion.2 ⟨q.1, ⟨_, hy, hzx⟩⟩
      exact hxy

theorem fppfFamilyTower_composite
    {F : SchemeFamily S I} {J : I → Type w} (G : FamilyTower F J)
    (hF : FppfCoveringFamily F)
    (hG : ∀ i, FppfCoveringFamily (G.inner i)) :
    FppfCoveringFamily G.composite := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨i, y, hy⟩ := hF.jointly_surjective s
    obtain ⟨j, z, hz⟩ := (hG i).jointly_surjective y
    refine ⟨⟨i, j⟩, z, ?_⟩
    change F.map i ((G.inner i).map j z) = s
    rw [hz, hy]
  · intro ij
    let : Flat ((G.inner ij.1).map ij.2) := (hG ij.1).flat ij.2
    let : Flat (F.map ij.1) := hF.flat ij.1
    change Flat ((G.inner ij.1).map ij.2 ≫ F.map ij.1)
    infer_instance
  · intro ij
    let : LocallyOfFinitePresentation ((G.inner ij.1).map ij.2) :=
      (hG ij.1).locally_of_finite_presentation ij.2
    let : LocallyOfFinitePresentation (F.map ij.1) :=
      hF.locally_of_finite_presentation ij.1
    change LocallyOfFinitePresentation ((G.inner ij.1).map ij.2 ≫ F.map ij.1)
    infer_instance

/-- A refinement records a local family over every member of a coarse family. -/
structure FamilyRefinement (F : SchemeFamily S I) (J : I → Type w) where
  family : FamilyTower F J
  fpqc : ∀ i, FpqcCoveringFamily (family.inner i)

def FamilyRefinement.refinedFamily
    {F : SchemeFamily S I} {J : I → Type w}
    (R : FamilyRefinement F J) : SchemeFamily S (Σ i, J i) :=
  R.family.composite

theorem familyRefinement_is_fpqc
    {F : SchemeFamily S I} {J : I → Type w}
    (hF : FpqcCoveringFamily F) (R : FamilyRefinement F J) :
    FpqcCoveringFamily R.refinedFamily := by
  exact fpqcFamilyTower_composite R.family hF R.fpqc

/-- The fppf analogue of a refinement. -/
structure FppfFamilyRefinement (F : SchemeFamily S I) (J : I → Type w) where
  family : FamilyTower F J
  fppf : ∀ i, FppfCoveringFamily (family.inner i)

def FppfFamilyRefinement.refinedFamily
    {F : SchemeFamily S I} {J : I → Type w}
    (R : FppfFamilyRefinement F J) : SchemeFamily S (Σ i, J i) :=
  R.family.composite

theorem fppfFamilyRefinement_is_fppf
    {F : SchemeFamily S I} {J : I → Type w}
    (hF : FppfCoveringFamily F) (R : FppfFamilyRefinement F J) :
    FppfCoveringFamily R.refinedFamily := by
  exact fppfFamilyTower_composite R.family hF R.fppf

/-- Canonical descent data only depends on the sieve generated by a covering family. -/
theorem descentData_effectivity_invariant_under_same_sieve
    {C : Type u} [Category.{v} C]
    (P : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι ι' : Type w} {S : C} {X : ι → C} {X' : ι' → C}
    (f : ∀ i, X i ⟶ S) (f' : ∀ j, X' j ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    (P.toDescentData f).IsEquivalence ↔
      (P.toDescentData f').IsEquivalence := by
  exact Pseudofunctor.DescentData.isEquivalence_toDescentData_iff_of_sieve_eq P f f' h

theorem schemeFamily_descentData_effectivity_invariant_under_same_sieve
    {S : Scheme.{u}} (P : Pseudofunctor (LocallyDiscrete Schemeᵒᵖ) Cat.{v', u'})
    {I J : Type w} (F : SchemeFamily S I) (G : SchemeFamily S J)
    (h : Sieve.ofArrows F.obj F.map = Sieve.ofArrows G.obj G.map) :
    (P.toDescentData F.map).IsEquivalence ↔
      (P.toDescentData G.map).IsEquivalence := by
  exact Pseudofunctor.DescentData.isEquivalence_toDescentData_iff_of_sieve_eq
    P F.map G.map h

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter02
