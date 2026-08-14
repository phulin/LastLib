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
  sorry

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
