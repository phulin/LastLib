import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04.Section02ObjectsIsomorphismsAndCocycles

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v v' u'

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04

noncomputable section

/-! ## 4.3 Morphisms and full faithfulness -/

/-- Morphisms between singleton descent data, using Mathlib's canonical category. -/
abbrev Chapter04DescentMorphism
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D D' : Chapter04SingleDescentData F p} :=
  D ⟶ D'

/-- The map on the object over `T` underlying a descent morphism. -/
def chapter04DescentMorphismMap
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D D' : Chapter04SingleDescentData F p}
    (φ : Chapter04DescentMorphism F (D := D) (D' := D')) :
    chapter04DescentObject F D ⟶ chapter04DescentObject F D' :=
  φ.hom PUnit.unit

theorem chapter04DescentMorphism_compatibility
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D D' : Chapter04SingleDescentData F p}
    (φ : Chapter04DescentMorphism F (D := D) (D' := D')) :
    (Chapter04PullbackFunctor F (chapter04P1 p)).map (chapter04DescentMorphismMap F φ) ≫
        (chapter04DescentIsomorphism F D').hom =
      (chapter04DescentIsomorphism F D).hom ≫
        (Chapter04PullbackFunctor F (chapter04P2 p)).map (chapter04DescentMorphismMap F φ) := by
  exact φ.comm (chapter04P1 p ≫ p) (chapter04P1 p) (chapter04P2 p) rfl
    (pullback.condition (f := p) (g := p)).symm

@[ext]
theorem chapter04DescentMorphism_ext
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D D' : Chapter04SingleDescentData F p}
    {φ ψ : Chapter04DescentMorphism F (D := D) (D' := D')}
    (h : chapter04DescentMorphismMap F φ = chapter04DescentMorphismMap F ψ) :
    φ = ψ := by
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  have hi : i = PUnit.unit := Subsingleton.elim _ _
  subst i
  exact h

@[simp]
theorem chapter04DescentMorphism_map_id
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S} (D : Chapter04SingleDescentData F p) :
    chapter04DescentMorphismMap F (𝟙 D) = 𝟙 (chapter04DescentObject F D) := by
  rfl

@[simp]
theorem chapter04DescentMorphism_map_comp
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} {p : T ⟶ S}
    {D₁ D₂ D₃ : Chapter04SingleDescentData F p}
    (φ : D₁ ⟶ D₂) (ψ : D₂ ⟶ D₃) :
    chapter04DescentMorphismMap F (φ ≫ ψ) =
      chapter04DescentMorphismMap F φ ≫ chapter04DescentMorphismMap F ψ := by
  rfl

/-- The compatibility condition induced on a downstairs morphism by the canonical data. -/
def Chapter04CompatibleHom
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (E E' : Chapter04FiberObject F S) (u : E ⟶ E') : Prop :=
  (Chapter04PullbackFunctor F (chapter04P1 p)).map
      ((Chapter04PullbackFunctor F p).map u) ≫
      (chapter04DescentIsomorphism F (chapter04CanonicalDescentDatum F p E')).hom =
    (chapter04DescentIsomorphism F (chapter04CanonicalDescentDatum F p E)).hom ≫
      (Chapter04PullbackFunctor F (chapter04P2 p)).map
        ((Chapter04PullbackFunctor F p).map u)

/-- Downstairs morphisms satisfying the induced compatibility condition. -/
def Chapter04CompatibleHomSet
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (E E' : Chapter04FiberObject F S) :=
  {u : E ⟶ E' // Chapter04CompatibleHom F p E E' u}

/-- The equalizer condition on a map over `T` for the canonical data. -/
def Chapter04CompatibleUpstairsHom
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (E E' : Chapter04FiberObject F S)
    (u : (Chapter04PullbackFunctor F p).obj E ⟶
      (Chapter04PullbackFunctor F p).obj E') : Prop :=
  (Chapter04PullbackFunctor F (chapter04P1 p)).map u ≫
        (chapter04DescentIsomorphism F (chapter04CanonicalDescentDatum F p E')).hom =
    (chapter04DescentIsomorphism F (chapter04CanonicalDescentDatum F p E)).hom ≫
      (Chapter04PullbackFunctor F (chapter04P2 p)).map u

def Chapter04CompatibleUpstairsHomSet
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (E E' : Chapter04FiberObject F S) :=
  {u : (Chapter04PullbackFunctor F p).obj E ⟶
      (Chapter04PullbackFunctor F p).obj E' //
    Chapter04CompatibleUpstairsHom F p E E' u}

/-- Full faithfulness identifies downstairs maps with compatible upstairs maps. -/
def chapter04CanonicalHomEquiv
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (hF : Chapter04DescentIsFullyFaithful F p)
    (E E' : Chapter04FiberObject F S) :
    (E ⟶ E') ≃ Chapter04CompatibleUpstairsHomSet F p E E' := by
  let π : ∀ _ : PUnit.{1}, Over.mk p ⟶ Over.mk (𝟙 S) :=
    fun _ => Over.homMk p
  let x (u : (Chapter04PullbackFunctor F p).obj E ⟶
      (Chapter04PullbackFunctor F p).obj E') :
      ∀ _ : PUnit.{1}, (F.presheafHom E E').obj (Opposite.op (Over.mk p)) :=
    fun _ => u
  have hcompatible
      (u : (Chapter04PullbackFunctor F p).obj E ⟶
        (Chapter04PullbackFunctor F p).obj E') :
      Chapter04CompatibleUpstairsHom F p E E' u →
        Presieve.Arrows.Compatible (F.presheafHom E E')
          π (x u) := by
    intro hu i j Z gi gj hgi
    cases i
    cases j
    have hbase : gi.left ≫ p = gj.left ≫ p := by
      simpa [π] using congrArg (fun k => k.left) hgi
    let g : Z.left ⟶ chapter04PairProduct p :=
      pullback.lift gi.left gj.left hbase
    have hg₁ : g ≫ chapter04P1 p = gi.left := by
      exact pullback.lift_fst _ _ hbase
    have hg₂ : g ≫ chapter04P2 p = gj.left := by
      exact pullback.lift_snd _ _ hbase
    let u' :
        chapter04DescentObject F (chapter04CanonicalDescentDatum F p E) ⟶
          chapter04DescentObject F (chapter04CanonicalDescentDatum F p E') := u
    have hu' :
        (Chapter04PullbackFunctor F (chapter04P1 p)).map u' ≫
            (chapter04DescentIsomorphism F
              (chapter04CanonicalDescentDatum F p E')).hom =
            (chapter04DescentIsomorphism F
              (chapter04CanonicalDescentDatum F p E)).hom ≫
          (Chapter04PullbackFunctor F (chapter04P2 p)).map u' := by
      exact hu
    have hcomp₁ :
        (chapter04P1 p).op.toLoc ≫ g.op.toLoc = (g ≫ chapter04P1 p).op.toLoc := by
      cat_disch
    have hcomp₂ :
        (chapter04P2 p).op.toLoc ≫ g.op.toLoc = (g ≫ chapter04P2 p).op.toLoc := by
      cat_disch
    have hhu := congrArg ((F.map g.op.toLoc).toFunctor.map) hu'
    dsimp [Pseudofunctor.presheafHom, x] at ⊢
    rw [Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom _ g
          (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) rfl rfl,
      Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom _ g
          (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) rfl rfl] at hhu
    dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom] at hhu
    simp only [cancel_epi] at hhu
    simp only [← Category.assoc, cancel_mono] at hhu
    rw [Functor.map_comp, Functor.map_comp] at hhu
    rw [← F.mapComp'_naturality_1 (chapter04P1 p).op.toLoc g.op.toLoc
          (g ≫ chapter04P1 p).op.toLoc hcomp₁ u',
      Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
        (chapter04DescentIsomorphism F
          (chapter04CanonicalDescentDatum F p E')).hom g
          (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) rfl rfl,
      Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom
        (chapter04DescentIsomorphism F
          (chapter04CanonicalDescentDatum F p E)).hom g
          (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) rfl rfl,
      ← F.mapComp'_naturality_1 (chapter04P2 p).op.toLoc g.op.toLoc
          (g ≫ chapter04P2 p).op.toLoc hcomp₂ u'] at hhu
    simp only [Category.assoc,
      Cat.Hom.hom_inv_id_toNatTrans_app_assoc] at hhu
    have hgiBase : (g ≫ chapter04P1 p) ≫ p = Z.hom := by
      simpa [hg₁, Category.assoc] using (Over.w gi)
    have hgjBase : (g ≫ chapter04P2 p) ≫ p = Z.hom := by
      simpa [hg₂, Category.assoc] using (Over.w gj)
    have hpull' :
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (chapter04DescentIsomorphism F
              (chapter04CanonicalDescentDatum F p E')).hom
            g (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) rfl rfl =
          (chapter04CanonicalDescentDatum F p E').hom Z.hom
            (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) := by
      simpa [chapter04DescentIsomorphism, chapter04DescentObject] using
        (chapter04CanonicalDescentDatum F p E').pullHom_hom
          g (chapter04P1 p ≫ p) Z.hom hgiBase
          (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          (chapter04P1 p) (chapter04P2 p) rfl (chapter04P1_base p).symm
          (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) rfl rfl
    have hpull :
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom
            (chapter04DescentIsomorphism F
              (chapter04CanonicalDescentDatum F p E)).hom
            g (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) rfl rfl =
          (chapter04CanonicalDescentDatum F p E).hom Z.hom
            (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) := by
      simpa [chapter04DescentIsomorphism, chapter04DescentObject] using
        (chapter04CanonicalDescentDatum F p E).pullHom_hom
          g (chapter04P1 p ≫ p) Z.hom hgiBase
          (i₁ := PUnit.unit) (i₂ := PUnit.unit)
          (chapter04P1 p) (chapter04P2 p) rfl (chapter04P1_base p).symm
          (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) rfl rfl
    rw [hpull', hpull] at hhu
    simp only [cancel_epi] at hhu
    have hcore :
        (F.map (g ≫ chapter04P1 p).op.toLoc).toFunctor.map u' ≫
            (chapter04CanonicalDescentDatum F p E').hom Z.hom
              (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) =
          (chapter04CanonicalDescentDatum F p E).hom Z.hom
          (g ≫ chapter04P1 p) (g ≫ chapter04P2 p) ≫
          (F.map (g ≫ chapter04P2 p).op.toLoc).toFunctor.map u' := by
      let b :=
        (F.mapComp' (chapter04P2 p).op.toLoc g.op.toLoc
          (g ≫ chapter04P2 p).op.toLoc rfl).hom.toNatTrans.app
          (chapter04DescentObject F
            (chapter04CanonicalDescentDatum F p E'))
      apply (cancel_mono b).1
      have hb :
          (F.mapComp' (chapter04P2 p).op.toLoc g.op.toLoc
            (g ≫ chapter04P2 p).op.toLoc hcomp₂).hom.toNatTrans.app
              (chapter04DescentObject F
                (chapter04CanonicalDescentDatum F p E')) = b := by
        dsimp [b]
      rw [hb] at hhu
      exact (Category.assoc _ _ _).trans
        (hhu.trans (Category.assoc _ _ _).symm)
    let c₁ :=
      (F.mapComp' p.op.toLoc (g ≫ chapter04P1 p).op.toLoc Z.hom.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgiBase])).hom.toNatTrans.app E
    let c₂ :=
      (F.mapComp' p.op.toLoc (g ≫ chapter04P2 p).op.toLoc Z.hom.op.toLoc
        (by rw [← Quiver.Hom.comp_toLoc, ← op_comp, hgjBase])).inv.toNatTrans.app E'
    have hmul := congrArg (fun k => c₁ ≫ k ≫ c₂) hcore
    have hgiOp :
        (chapter04P1 p).op.toLoc ≫ g.op.toLoc = gi.left.op.toLoc := by
      rw [hcomp₁]
      exact congrArg (fun k => k.op.toLoc) hg₁
    have hgjOp :
        (chapter04P2 p).op.toLoc ≫ g.op.toLoc = gj.left.op.toLoc := by
      rw [hcomp₂]
      exact congrArg (fun k => k.op.toLoc) hg₂
    simp only [← hg₁, ← hg₂]
    simpa [c₁, c₂, Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      chapter04DescentIsomorphism, chapter04DescentObject,
      chapter04CanonicalDescentDatum, chapter04DescentComparison,
      Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
      hgiOp, hgjOp, Category.assoc] using hmul
  let hFF : (chapter04DescentComparison F p).FullyFaithful := hF.some
  let e :=
    Pseudofunctor.DescentData.subtypeCompatibleHomEquiv (F := F)
      (f := fun _ : PUnit.{1} => p) (M := E) (N := E')
  refine
    { toFun := fun u =>
        let φ := (chapter04DescentComparison F p).map u
        ⟨chapter04DescentMorphismMap F φ, by
          simpa [Chapter04CompatibleUpstairsHom, chapter04DescentComparison,
            chapter04CanonicalDescentDatum, chapter04DescentObject,
            chapter04DescentMorphismMap,
            Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
            using chapter04DescentMorphism_compatibility F φ⟩
      invFun := fun v =>
        let w : Subtype (Presieve.Arrows.Compatible (F.presheafHom E E')
            (X := fun _ : PUnit.{1} => Over.mk p)
            (B := Over.mk (𝟙 S)) (fun _ => Over.homMk p)) :=
          ⟨x v.1, by simpa [π] using hcompatible v.1 v.2⟩
        hFF.preimage (e w)
      left_inv := by
        intro u
        dsimp
        apply hFF.map_injective
        apply hFF.map_preimage
      right_inv := by
        intro v
        apply Subtype.ext
        dsimp [chapter04DescentMorphismMap]
        let w : Subtype (Presieve.Arrows.Compatible (F.presheafHom E E')
            (X := fun _ : PUnit.{1} => Over.mk p)
            (B := Over.mk (𝟙 S)) (fun _ => Over.homMk p)) :=
          ⟨x v.1, by simpa [π] using hcompatible v.1 v.2⟩
        have hmap :
            (chapter04DescentComparison F p).map (hFF.preimage (e w)) = e w := by
          apply hFF.map_preimage
        change
          ((chapter04DescentComparison F p).map
              (hFF.preimage (e w))).hom PUnit.unit = v.1
        rw [hmap]
        rfl }

theorem chapter04CanonicalMorphism_is_compatible
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Cat.{v', u'}))
    {S T : Scheme.{u}} (p : T ⟶ S)
    (E E' : Chapter04FiberObject F S) (u : E ⟶ E') :
    Chapter04CompatibleHom F p E E' u := by
  exact chapter04DescentMorphism_compatibility F
    ((chapter04DescentComparison F p).map u)

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter04
