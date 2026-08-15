import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12.Dependencies
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Section03TableOfDescendingProperties

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped MonObj

universe u

/-!
### 12.1 Group laws descend

The descent datum records the underlying scheme gluing and its cocycle.  The theorem below adds the
group-object structure by descending the three structure maps and checking their equations after
the fpqc cover.
-/

theorem chapter12_group_laws_descend
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12GroupSchemeDescentDatum p) :
      ∃ G : Chapter12GroupScheme S,
      ∃ e : Chapter12GroupScheme.baseChange p G ≅ D.upstairs,
        chapter12GroupSchemeDescentComparisonCompatible D G e := by
  sorry

private theorem chapter12_commutativity_descends_aux
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hcomm : IsCommMonObj G_T.X) :
    IsCommMonObj G.X := by
  let : IsCommMonObj (Chapter12GroupScheme.baseChange p G).X := by
    refine { mul_comm := ?_ }
    apply (cancel_mono e.hom.hom.hom).1
    simp only [Category.assoc, IsMonHom.mul_hom]
    rw [← BraidedCategory.braiding_naturality_assoc e.hom.hom.hom e.hom.hom.hom]
    rw [hcomm.mul_comm]
  refine { mul_comm := ?_ }
  apply Over.OverMorphism.ext
  change (β_ G.X G.X).hom.left ≫ μ[G.X].left = μ[G.X].left
  let : Flat p := hp.1
  let : Surjective p := hp.2
  let : Epi (pullback.fst (G.X ⊗ G.X).hom p) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (pullback.fst (G.X ⊗ G.X).hom p)).1 ?_
  let c := CartesianMonoidalCategory.prodComparisonIso (Over.pullback p) G.X G.X
  have hh := congrArg (fun k => c.hom.left ≫ k.left)
    (IsCommMonObj.mul_comm (Chapter12GroupScheme.baseChange p G).X)
  change c.hom.left ≫
      (β_ ((Over.pullback p).obj G.X) ((Over.pullback p).obj G.X)).hom.left ≫
        (Functor.LaxMonoidal.μ (Over.pullback p) G.X G.X ≫
          (Over.pullback p).map μ[G.X]).left =
    c.hom.left ≫
      (Functor.LaxMonoidal.μ (Over.pullback p) G.X G.X ≫
        (Over.pullback p).map μ[G.X]).left at hh
  rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory] at hh
  have hbraid :
      c.hom ≫ (β_ ((Over.pullback p).obj G.X) ((Over.pullback p).obj G.X)).hom ≫ c.inv =
        (Over.pullback p).map (β_ G.X G.X).hom := by
    simpa only [c, Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory,
      Functor.Monoidal.μ_of_cartesianMonoidalCategory,
      CartesianMonoidalCategory.prodComparisonIso_hom, Category.assoc] using
      (Functor.map_braiding (Over.pullback p) G.X G.X).symm
  have hbraid_left := congrArg Over.Hom.left hbraid
  simp only [Over.comp_left, ← Category.assoc] at hbraid_left
  simp only [Over.comp_left, ← Category.assoc] at hh
  change c.hom.left ≫
      (β_ ((Over.pullback p).obj G.X) ((Over.pullback p).obj G.X)).hom.left ≫
        c.inv.left ≫ Over.Hom.left ((Over.pullback p).map μ[G.X]) =
    c.hom.left ≫ c.inv.left ≫ Over.Hom.left ((Over.pullback p).map μ[G.X]) at hh
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc] at hh
  rw [hbraid_left] at hh
  have hh' := congrArg (fun k => k ≫ pullback.fst G.X.hom p) hh
  simpa [Over.pullback, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc] using hh'

private theorem chapter12_commutative_group_comparison_underlying
    {S T U : Scheme.{u}} (p : T ⟶ S) (G : Chapter12GroupScheme S)
    [IsCommMonObj G.X] (q₁ q₂ : U ⟶ T) (h : q₁ ≫ p = q₂ ≫ p) :
      Over.Hom.left
        (chapter12CommutativeGroupSchemeBaseChangeComparison p { X := G.X } q₁ q₂ h).hom.hom.hom.hom =
      Over.Hom.left (chapter12GroupSchemeBaseChangeComparison p G q₁ q₂ h).hom.hom.hom := by
  have hc₁ :
      (CommGrp.forget₂Grp (Over U)).mapIso
          ((Functor.mapCommGrpCompIso (F := Over.pullback p)
            (G := Over.pullback q₁)).app { X := G.X }) =
        (Functor.mapGrpCompIso (F := Over.pullback p)
          (G := Over.pullback q₁)).app G := by
    apply Iso.ext
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    rfl
  have hc₂ :
      (CommGrp.forget₂Grp (Over U)).mapIso
          ((Functor.mapCommGrpCompIso (F := Over.pullback p)
            (G := Over.pullback q₂)).app { X := G.X }) =
        (Functor.mapGrpCompIso (F := Over.pullback p)
          (G := Over.pullback q₂)).app G := by
    apply Iso.ext
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    rfl
  have hn₁ :
      (CommGrp.forget₂Grp (Over U)).mapIso
          ((Functor.mapCommGrpNatIso (Over.pullbackComp q₁ p)).app { X := G.X }) =
        (Functor.mapGrpNatIso (Over.pullbackComp q₁ p)).app G := by
    apply Iso.ext
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    rfl
  have hn₂ :
      (CommGrp.forget₂Grp (Over U)).mapIso
          ((Functor.mapCommGrpNatIso (Over.pullbackComp q₂ p)).app { X := G.X }) =
        (Functor.mapGrpNatIso (Over.pullbackComp q₂ p)).app G := by
    apply Iso.ext
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    rfl
  have hci₁ :
      (CommGrp.forget₂Grp (Over U)).mapIso
          (chapter12CommutativeGroupSchemeBaseChangeCompIso p q₁ { X := G.X }) =
        chapter12GroupSchemeBaseChangeCompIso p q₁ G := by
    change
      (CommGrp.forget₂Grp (Over U)).mapIso
          (((Functor.mapCommGrpCompIso (F := Over.pullback p)
              (G := Over.pullback q₁)).app { X := G.X }).symm ≪≫
            ((Functor.mapCommGrpNatIso (Over.pullbackComp q₁ p)).app
              { X := G.X }).symm) =
        ((Functor.mapGrpCompIso (F := Over.pullback p)
            (G := Over.pullback q₁)).app G).symm ≪≫
          ((Functor.mapGrpNatIso (Over.pullbackComp q₁ p)).app G).symm
    rw [Functor.mapIso_trans, Functor.mapIso_symm, Functor.mapIso_symm, hc₁, hn₁]
    rfl
  have hci₂ :
      (CommGrp.forget₂Grp (Over U)).mapIso
          (chapter12CommutativeGroupSchemeBaseChangeCompIso p q₂ { X := G.X }) =
        chapter12GroupSchemeBaseChangeCompIso p q₂ G := by
    change
      (CommGrp.forget₂Grp (Over U)).mapIso
          (((Functor.mapCommGrpCompIso (F := Over.pullback p)
              (G := Over.pullback q₂)).app { X := G.X }).symm ≪≫
            ((Functor.mapCommGrpNatIso (Over.pullbackComp q₂ p)).app
              { X := G.X }).symm) =
        ((Functor.mapGrpCompIso (F := Over.pullback p)
            (G := Over.pullback q₂)).app G).symm ≪≫
          ((Functor.mapGrpNatIso (Over.pullbackComp q₂ p)).app G).symm
    rw [Functor.mapIso_trans, Functor.mapIso_symm, Functor.mapIso_symm, hc₂, hn₂]
    rfl
  have hforget :
      (CommGrp.forget₂Grp (Over U)).mapIso
          (chapter12CommutativeGroupSchemeBaseChangeComparison p { X := G.X } q₁ q₂ h) =
        chapter12GroupSchemeBaseChangeComparison p G q₁ q₂ h := by
    simp only [chapter12CommutativeGroupSchemeBaseChangeComparison,
      chapter12GroupSchemeBaseChangeComparison]
    rw [Functor.mapIso_trans]
    rw [hci₁]
    rw [Functor.mapIso_trans, eqToIso_map, Functor.mapIso_symm, hci₂]
    rfl
  change Over.Hom.left
      (((CommGrp.forget₂Grp (Over U)).map
        (chapter12CommutativeGroupSchemeBaseChangeComparison p { X := G.X } q₁ q₂ h).hom).hom.hom) =
    Over.Hom.left (chapter12GroupSchemeBaseChangeComparison p G q₁ q₂ h).hom.hom.hom
  rw [← hforget]
  rfl

private def chapter12_commutative_descentDatum_to_group
    {S T : Scheme.{u}} {p : T ⟶ S}
    (D : Chapter12CommutativeGroupSchemeDescentDatum p) :
    Chapter12GroupSchemeDescentDatum p :=
  { upstairs := D.upstairs.toGrp
    compare := fun {U} q₁ q₂ h =>
      (CommGrp.forget₂Grp (Over U)).mapIso (D.compare q₁ q₂ h)
    compare_self := by
      intro U q h
      rw [D.compare_self q h]
      rfl
    compare_comp := by
      intro U q₁ q₂ q₃ h₁₂ h₂₃ h₁₃
      change
        (CommGrp.forget₂Grp (Over U)).map (D.compare q₁ q₂ h₁₂).hom ≫
            (CommGrp.forget₂Grp (Over U)).map (D.compare q₂ q₃ h₂₃).hom =
          (CommGrp.forget₂Grp (Over U)).map (D.compare q₁ q₃ h₁₃).hom
      rw [← Functor.map_comp]
      exact congrArg (fun k => (CommGrp.forget₂Grp (Over U)).map k)
        (D.compare_comp q₁ q₂ q₃ h₁₂ h₂₃ h₁₃)
    compare_pull := by
      intro U V r q₁ q₂ h h'
      apply Grp.hom_ext
      apply Over.OverMorphism.ext
      have hh := congrArg (fun k => (CommGrp.forget₂Grp (Over V)).map k)
        (D.compare_pull r q₁ q₂ h h')
      have hh' := congrArg (fun k => k.hom.hom.left) hh
      simp [Chapter12GroupScheme.baseChangeIso,
        Chapter12CommutativeGroupScheme.baseChangeIso,
        Chapter12GroupScheme.baseChange,
        Chapter12CommutativeGroupScheme.baseChange,
        Functor.mapGrp, Functor.mapCommGrp, CommGrp.forget₂Grp] at hh' ⊢
      exact hh' }

private theorem chapter12_commutative_group_comparison_compatible
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12CommutativeGroupSchemeDescentDatum p)
    (G : Chapter12GroupScheme S)
    (e : Chapter12GroupScheme.baseChange p G ≅ D.upstairs.toGrp)
    (he : chapter12GroupSchemeDescentComparisonCompatible
      (chapter12_commutative_descentDatum_to_group D) G e) :
    ∃ G' : Chapter12CommutativeGroupScheme S,
      ∃ e' : Chapter12CommutativeGroupScheme.baseChange p G' ≅ D.upstairs,
        chapter12CommutativeGroupSchemeDescentComparisonCompatible D G' e' := by
  let comm : IsCommMonObj G.X :=
    chapter12_commutativity_descends_aux p ⟨hp.2.1, hp.2.2⟩ G D.upstairs.toGrp e D.upstairs.comm
  let G' : Chapter12CommutativeGroupScheme S := { X := G.X, comm := comm }
  let e' : Chapter12CommutativeGroupScheme.baseChange p G' ≅ D.upstairs :=
    InducedCategory.isoMk e
  refine ⟨G', e', ?_⟩
  intro U q₁ q₂ h
  apply CommGrp.hom_ext
  apply Over.OverMorphism.ext
  have hh := congrArg (fun k => k.hom.hom.left) (he q₁ q₂ h)
  simp only [CommGrp.comp_hom, Grp.comp_hom_hom, Over.comp_left]
  rw [@chapter12_commutative_group_comparison_underlying S T U p G comm q₁ q₂ h]
  exact hh

theorem chapter12_commutative_group_laws_descend
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12CommutativeGroupSchemeDescentDatum p) :
    ∃ G : Chapter12CommutativeGroupScheme S,
      ∃ e : Chapter12CommutativeGroupScheme.baseChange p G ≅ D.upstairs,
        chapter12CommutativeGroupSchemeDescentComparisonCompatible D G e := by
  let D' : Chapter12GroupSchemeDescentDatum p :=
    chapter12_commutative_descentDatum_to_group D
  obtain ⟨G, e, he⟩ := chapter12_group_laws_descend p hp D'
  exact chapter12_commutative_group_comparison_compatible p hp D G e he

/-- Equality of homomorphisms can be detected after a faithfully flat base change. -/
theorem chapter12_group_hom_ext_of_faithfullyFlat
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    {G H : Chapter12GroupScheme S} (f g : G ⟶ H)
    (h : Chapter12GroupScheme.baseChangeHom p f =
      Chapter12GroupScheme.baseChangeHom p g) :
    f = g := by
  apply Chapter12GroupScheme.hom_ext
  change f.hom.hom.left = g.hom.hom.left
  let : Flat p := hp.1
  let : Surjective p := hp.2
  let : Epi (pullback.fst G.X.hom p) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (pullback.fst G.X.hom p)).1 ?_
  have h' := (congrArg (fun k => k.hom.hom.left ≫ pullback.fst H.X.hom p) h)
  simpa [Chapter12GroupScheme.baseChangeHom, Chapter12GroupScheme.baseChange,
    Functor.mapGrp, Functor.mapMon, Over.pullback, pullback.lift_fst,
    Category.assoc] using h'

/-- Equality of commutative-group homomorphisms is detected after a faithfully flat base change. -/
theorem chapter12_commutative_group_hom_ext_of_faithfullyFlat
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    {G H : Chapter12CommutativeGroupScheme S} (f g : G ⟶ H)
    (h : Chapter12CommutativeGroupScheme.baseChangeHom p f =
      Chapter12CommutativeGroupScheme.baseChangeHom p g) :
    f = g := by
  apply Chapter12CommutativeGroupScheme.hom_ext
  change f.hom.hom.hom.left = g.hom.hom.hom.left
  let : Flat p := hp.1
  let : Surjective p := hp.2
  let : Epi (pullback.fst G.X.hom p) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (pullback.fst G.X.hom p)).1 ?_
  have hh := (congrArg (fun k => k.hom.hom.hom.left ≫ pullback.fst H.X.hom p) h)
  simpa [Chapter12CommutativeGroupScheme.baseChangeHom,
    Chapter12CommutativeGroupScheme.baseChange, Functor.mapCommGrp,
    Functor.mapGrp, Functor.mapMon, Over.pullback, pullback.lift_fst,
    Category.assoc] using hh

/-!
The commutativity equation is the equality of multiplication with its pullback along the
symmetry.  It is kept as an instance-shaped proposition so later affine and finite commutative
group-object APIs can consume it directly.
-/

theorem chapter12_commutativity_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hcomm : IsCommMonObj G_T.X) :
    IsCommMonObj G.X := by
  let : IsCommMonObj (Chapter12GroupScheme.baseChange p G).X := by
    refine { mul_comm := ?_ }
    apply (cancel_mono e.hom.hom.hom).1
    simp only [Category.assoc, IsMonHom.mul_hom]
    rw [← BraidedCategory.braiding_naturality_assoc e.hom.hom.hom e.hom.hom.hom]
    rw [hcomm.mul_comm]
  refine { mul_comm := ?_ }
  apply Over.OverMorphism.ext
  change (β_ G.X G.X).hom.left ≫ μ[G.X].left = μ[G.X].left
  let : Flat p := hp.1
  let : Surjective p := hp.2
  let : Epi (pullback.fst (G.X ⊗ G.X).hom p) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  refine (cancel_epi (pullback.fst (G.X ⊗ G.X).hom p)).1 ?_
  let c := CartesianMonoidalCategory.prodComparisonIso (Over.pullback p) G.X G.X
  have hh := congrArg (fun k => c.hom.left ≫ k.left)
    (IsCommMonObj.mul_comm (Chapter12GroupScheme.baseChange p G).X)
  change c.hom.left ≫
      (β_ ((Over.pullback p).obj G.X) ((Over.pullback p).obj G.X)).hom.left ≫
        (Functor.LaxMonoidal.μ (Over.pullback p) G.X G.X ≫
          (Over.pullback p).map μ[G.X]).left =
    c.hom.left ≫
      (Functor.LaxMonoidal.μ (Over.pullback p) G.X G.X ≫
        (Over.pullback p).map μ[G.X]).left at hh
  rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory] at hh
  have hbraid :
      c.hom ≫ (β_ ((Over.pullback p).obj G.X) ((Over.pullback p).obj G.X)).hom ≫ c.inv =
        (Over.pullback p).map (β_ G.X G.X).hom := by
    simpa only [c, Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory,
      Functor.Monoidal.μ_of_cartesianMonoidalCategory,
      CartesianMonoidalCategory.prodComparisonIso_hom, Category.assoc] using
      (Functor.map_braiding (Over.pullback p) G.X G.X).symm
  have hbraid_left := congrArg Over.Hom.left hbraid
  simp only [Over.comp_left, ← Category.assoc] at hbraid_left
  simp only [Over.comp_left, ← Category.assoc] at hh
  change c.hom.left ≫
      (β_ ((Over.pullback p).obj G.X) ((Over.pullback p).obj G.X)).hom.left ≫
        c.inv.left ≫ Over.Hom.left ((Over.pullback p).map μ[G.X]) =
    c.hom.left ≫ c.inv.left ≫ Over.Hom.left ((Over.pullback p).map μ[G.X]) at hh
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc] at hh
  rw [hbraid_left] at hh
  have hh' := congrArg (fun k => k ≫ pullback.fst G.X.hom p) hh
  simpa [Over.pullback, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc] using hh'

theorem chapter12_finite_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hfinite : Chapter12Finite G_T.X.hom) :
    Chapter12Finite G.X.hom := by
  have hbase : Chapter12Finite (Chapter12GroupScheme.baseChange p G).X.hom := by
    rw [← e.hom.hom.hom.w]
    let : Chapter12Finite G_T.X.hom := hfinite
    let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
      dsimp [Chapter12GroupScheme.homScheme]
      let : IsIso e.hom.hom := by
        change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
        infer_instance
      let : IsIso e.hom.hom.hom := by
        change IsIso ((Mon.forget (Over T)).map e.hom.hom)
        infer_instance
      change IsIso ((Over.forget T).map e.hom.hom.hom)
      infer_instance
    infer_instance
  exact (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_finite_fpqc_local_on_base
    (f := G.X.hom) (p := p) ⟨hp.2.2, hp.2.1, hp.1⟩).2 hbase

theorem chapter12_flat_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FaithfullyFlat p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hflat : Chapter12Flat G_T.X.hom) :
    Chapter12Flat G.X.hom := by
  sorry

theorem chapter12_locallyOfFinitePresentation_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hlfp : Chapter12LocallyOfFinitePresentation G_T.X.hom) :
    Chapter12LocallyOfFinitePresentation G.X.hom := by
  have hbase : Chapter12LocallyOfFinitePresentation
      (Chapter12GroupScheme.baseChange p G).X.hom := by
    rw [← e.hom.hom.hom.w]
    let : Chapter12LocallyOfFinitePresentation G_T.X.hom := hlfp
    let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
      dsimp [Chapter12GroupScheme.homScheme]
      let : IsIso e.hom.hom := by
        change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
        infer_instance
      let : IsIso e.hom.hom.hom := by
        change IsIso ((Mon.forget (Over T)).map e.hom.hom)
        infer_instance
      change IsIso ((Over.forget T).map e.hom.hom.hom)
      infer_instance
    infer_instance
  exact (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_locallyOfFinitePresentation_fpqc_local_on_base
    (f := G.X.hom) (p := p) ⟨hp.2.2, hp.2.1, hp.1⟩).2 hbase

theorem chapter12_finitePresentation_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hfp : Chapter12FinitePresentation G_T.X.hom) :
    Chapter12FinitePresentation G.X.hom := by
  have hbase : Chapter12FinitePresentation
      (Chapter12GroupScheme.baseChange p G).X.hom := by
    constructor
    · rw [← e.hom.hom.hom.w]
      let : LocallyOfFinitePresentation G_T.X.hom := hfp.1
      let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
        dsimp [Chapter12GroupScheme.homScheme]
        let : IsIso e.hom.hom := by
          change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
          infer_instance
        let : IsIso e.hom.hom.hom := by
          change IsIso ((Mon.forget (Over T)).map e.hom.hom)
          infer_instance
        change IsIso ((Over.forget T).map e.hom.hom.hom)
        infer_instance
      infer_instance
    · rw [← e.hom.hom.hom.w]
      let : QuasiCompact G_T.X.hom := hfp.2
      let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
        dsimp [Chapter12GroupScheme.homScheme]
        let : IsIso e.hom.hom := by
          change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
          infer_instance
        let : IsIso e.hom.hom.hom := by
          change IsIso ((Mon.forget (Over T)).map e.hom.hom)
          infer_instance
        change IsIso ((Over.forget T).map e.hom.hom.hom)
        infer_instance
      infer_instance
  exact (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_finitePresentation_fpqc_local_on_base
    (f := G.X.hom) (p := p) ⟨hp.2.2, hp.2.1, hp.1⟩).2 hbase

theorem chapter12_finiteLocallyFree_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T)
    (hfinite : Chapter12FiniteLocallyFree G_T.X.hom) :
    Chapter12FiniteLocallyFree G.X.hom := by
  have hbase : Chapter12FiniteLocallyFree
      (Chapter12GroupScheme.baseChange p G).X.hom := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← e.hom.hom.hom.w]
      let : IsFinite G_T.X.hom := hfinite.1
      let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
        dsimp [Chapter12GroupScheme.homScheme]
        let : IsIso e.hom.hom := by
          change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
          infer_instance
        let : IsIso e.hom.hom.hom := by
          change IsIso ((Mon.forget (Over T)).map e.hom.hom)
          infer_instance
        change IsIso ((Over.forget T).map e.hom.hom.hom)
        infer_instance
      infer_instance
    · rw [← e.hom.hom.hom.w]
      let : Flat G_T.X.hom := hfinite.2.1
      let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
        dsimp [Chapter12GroupScheme.homScheme]
        let : IsIso e.hom.hom := by
          change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
          infer_instance
        let : IsIso e.hom.hom.hom := by
          change IsIso ((Mon.forget (Over T)).map e.hom.hom)
          infer_instance
        change IsIso ((Over.forget T).map e.hom.hom.hom)
        infer_instance
      infer_instance
    · rw [← e.hom.hom.hom.w]
      let : LocallyOfFinitePresentation G_T.X.hom := hfinite.2.2
      let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
        dsimp [Chapter12GroupScheme.homScheme]
        let : IsIso e.hom.hom := by
          change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
          infer_instance
        let : IsIso e.hom.hom.hom := by
          change IsIso ((Mon.forget (Over T)).map e.hom.hom)
          infer_instance
        change IsIso ((Over.forget T).map e.hom.hom.hom)
        infer_instance
      infer_instance
  exact ⟨chapter12_finite_descends p hp G G_T e hfinite.1,
    chapter12_flat_descends p ⟨hp.2.1, hp.2.2⟩ G G_T e hfinite.2.1,
    chapter12_locallyOfFinitePresentation_descends p hp G G_T e hfinite.2.2⟩

theorem chapter12_finiteLocallyFree_rank_descends
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (G : Chapter12GroupScheme S) (G_T : Chapter12GroupScheme T)
    (e : Chapter12GroupScheme.baseChange p G ≅ G_T) (n : ℕ)
    (hrank : Chapter12FiniteLocallyFreeOfRank G_T.X.hom n) :
    Chapter12FiniteLocallyFreeOfRank G.X.hom n := by
  have hbaseFinite : Chapter12FiniteLocallyFree
      (Chapter12GroupScheme.baseChange p G).X.hom := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← e.hom.hom.hom.w]
      let : IsFinite G_T.X.hom := hrank.1.1
      let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
        dsimp [Chapter12GroupScheme.homScheme]
        let : IsIso e.hom.hom := by
          change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
          infer_instance
        let : IsIso e.hom.hom.hom := by
          change IsIso ((Mon.forget (Over T)).map e.hom.hom)
          infer_instance
        change IsIso ((Over.forget T).map e.hom.hom.hom)
        infer_instance
      infer_instance
    · rw [← e.hom.hom.hom.w]
      let : Flat G_T.X.hom := hrank.1.2.1
      let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
        dsimp [Chapter12GroupScheme.homScheme]
        let : IsIso e.hom.hom := by
          change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
          infer_instance
        let : IsIso e.hom.hom.hom := by
          change IsIso ((Mon.forget (Over T)).map e.hom.hom)
          infer_instance
        change IsIso ((Over.forget T).map e.hom.hom.hom)
        infer_instance
      infer_instance
    · rw [← e.hom.hom.hom.w]
      let : LocallyOfFinitePresentation G_T.X.hom := hrank.1.2.2
      let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
        dsimp [Chapter12GroupScheme.homScheme]
        let : IsIso e.hom.hom := by
          change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
          infer_instance
        let : IsIso e.hom.hom.hom := by
          change IsIso ((Mon.forget (Over T)).map e.hom.hom)
          infer_instance
        change IsIso ((Over.forget T).map e.hom.hom.hom)
        infer_instance
      infer_instance
  have hbase : Chapter12FiniteLocallyFreeOfRank
      (Chapter12GroupScheme.baseChange p G).X.hom n := by
    refine ⟨hbaseFinite, ?_⟩
    intro y
    let : IsFinite G_T.X.hom := hrank.1.1
    let : Flat G_T.X.hom := hrank.1.2.1
    let : IsIso (Chapter12GroupScheme.homScheme e.hom) := by
      dsimp [Chapter12GroupScheme.homScheme]
      let : IsIso e.hom.hom := by
        change IsIso ((Grp.forget₂Mon (Over T)).map e.hom)
        infer_instance
      let : IsIso e.hom.hom.hom := by
        change IsIso ((Mon.forget (Over T)).map e.hom.hom)
        infer_instance
      change IsIso ((Over.forget T).map e.hom.hom.hom)
      infer_instance
    rw [← e.hom.hom.hom.w, Scheme.Hom.finrank_comp_left_of_isIso]
    exact hrank.2 y
  have hbase10 :
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10FiniteLocallyFreeOfRank
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10BaseChangeMorphism
        G.X.hom p) n :=
    ⟨hbaseFinite.1, hbaseFinite.2.1, hbaseFinite.2.2, hbase.2⟩
  have hresult := (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10_finiteLocallyFreeOfRank_fpqc_local_on_base n
    (f := G.X.hom) (p := p) ⟨hp.2.2, hp.2.1, hp.1⟩).2 hbase10
  exact ⟨⟨hresult.1, hresult.2.1, hresult.2.2.1⟩, hresult.2.2.2⟩

/-! The finite-flat and finite-locally-free group-object categories inherit effectivity. -/

theorem chapter12_finiteFlat_group_objects_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12GroupSchemeDescentDatum p)
    (hfiniteFlat : Chapter12FiniteFlat D.upstairs.X.hom) :
    ∃ G : Chapter12FiniteFlatGroupScheme S,
      ∃ e : Chapter12GroupScheme.baseChange p G.group ≅ D.upstairs,
        chapter12GroupSchemeDescentComparisonCompatible D G.group e := by
  obtain ⟨G, e, he⟩ := chapter12_group_laws_descend p hp D
  refine ⟨{ group := G, finiteFlat := ?_ }, e, he⟩
  exact ⟨chapter12_finite_descends p hp G D.upstairs e hfiniteFlat.1,
    chapter12_flat_descends p ⟨hp.2.1, hp.2.2⟩ G D.upstairs e hfiniteFlat.2⟩

theorem chapter12_finiteLocallyFree_group_objects_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12GroupSchemeDescentDatum p)
    (hfiniteLocallyFree : Chapter12FiniteLocallyFree D.upstairs.X.hom) :
    ∃ G : Chapter12FiniteLocallyFreeGroupScheme S,
      ∃ e : Chapter12GroupScheme.baseChange p G.group ≅ D.upstairs,
        chapter12GroupSchemeDescentComparisonCompatible D G.group e := by
  obtain ⟨G, e, he⟩ := chapter12_group_laws_descend p hp D
  refine ⟨{ group := G, finiteLocallyFree := ?_ }, e, he⟩
  exact ⟨chapter12_finite_descends p hp G D.upstairs e hfiniteLocallyFree.1,
    chapter12_flat_descends p ⟨hp.2.1, hp.2.2⟩ G D.upstairs e hfiniteLocallyFree.2.1,
    chapter12_locallyOfFinitePresentation_descends p hp G D.upstairs e
      hfiniteLocallyFree.2.2⟩

theorem chapter12_finiteLocallyFree_commutative_group_objects_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12CommutativeGroupSchemeDescentDatum p)
    (hfiniteLocallyFree : Chapter12FiniteLocallyFree D.upstairs.X.hom) :
    ∃ G : Chapter12FiniteLocallyFreeCommutativeGroupScheme S,
      ∃ e : Chapter12CommutativeGroupScheme.baseChange p G.group ≅ D.upstairs,
        chapter12CommutativeGroupSchemeDescentComparisonCompatible D G.group e := by
  obtain ⟨G, e, he⟩ := chapter12_commutative_group_laws_descend p hp D
  let G' : Chapter12GroupScheme S := G.toGrp
  let e' : Chapter12GroupScheme.baseChange p G' ≅ D.upstairs.toGrp :=
    (CommGrp.forget₂Grp (Over T)).mapIso e
  refine ⟨{ group := G, finiteLocallyFree := ?_ }, e, he⟩
  exact ⟨chapter12_finite_descends p hp G' D.upstairs.toGrp e' hfiniteLocallyFree.1,
    chapter12_flat_descends p ⟨hp.2.1, hp.2.2⟩ G' D.upstairs.toGrp e'
      hfiniteLocallyFree.2.1,
    chapter12_locallyOfFinitePresentation_descends p hp G' D.upstairs.toGrp e'
      hfiniteLocallyFree.2.2⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12
