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

theorem chapter12_commutative_group_laws_descend
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12CommutativeGroupSchemeDescentDatum p) :
    ∃ G : Chapter12CommutativeGroupScheme S,
      ∃ e : Chapter12CommutativeGroupScheme.baseChange p G ≅ D.upstairs,
        chapter12CommutativeGroupSchemeDescentComparisonCompatible D G e := by
  sorry

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
  have h' := congrArg (fun k => k.hom.hom.left ≫ pullback.fst H.X.hom p) h
  simpa [Chapter12GroupScheme.baseChangeHom, Chapter12GroupScheme.baseChange,
    Functor.mapGrp, Functor.mapMon, Over.pullback, pullback.lift_fst,
    Category.assoc] using h'

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
  sorry

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
  sorry

theorem chapter12_finiteLocallyFree_group_objects_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12GroupSchemeDescentDatum p)
    (hfiniteLocallyFree : Chapter12FiniteLocallyFree D.upstairs.X.hom) :
    ∃ G : Chapter12FiniteLocallyFreeGroupScheme S,
      ∃ e : Chapter12GroupScheme.baseChange p G.group ≅ D.upstairs,
        chapter12GroupSchemeDescentComparisonCompatible D G.group e := by
  sorry

theorem chapter12_finiteLocallyFree_commutative_group_objects_effective_fpqc_descent
    {S T : Scheme.{u}} (p : T ⟶ S) (hp : Chapter12FpqcCover p)
    (D : Chapter12CommutativeGroupSchemeDescentDatum p)
    (hfiniteLocallyFree : Chapter12FiniteLocallyFree D.upstairs.X.hom) :
    ∃ G : Chapter12FiniteLocallyFreeCommutativeGroupScheme S,
      ∃ e : Chapter12CommutativeGroupScheme.baseChange p G.group ≅ D.upstairs,
        chapter12CommutativeGroupSchemeDescentComparisonCompatible D G.group e := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter12
