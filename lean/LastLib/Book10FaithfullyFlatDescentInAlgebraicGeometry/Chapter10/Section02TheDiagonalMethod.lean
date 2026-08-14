import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Dependencies
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
## 10.2 The diagonal method

This file records the diagonal characterizations and the descent bridges for closed immersions,
open immersions, and isomorphisms.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/-- The diagonal of a scheme morphism. -/
abbrev chapter10Diagonal {X S : Scheme.{u}} (f : X ⟶ S) :
    X ⟶ pullback f f :=
  pullback.diagonal f

/-- Separatedness is the closed-immersion condition on the diagonal. -/
theorem chapter10_separated_iff_diagonal_closedImmersion {X S : Scheme.{u}} (f : X ⟶ S) :
    IsSeparated f ↔ IsClosedImmersion (chapter10Diagonal f) := by
  simpa [chapter10Diagonal] using (isSeparated_iff f)

/-- Quasi-separatedness is exactly quasi-compactness of the diagonal. -/
theorem chapter10_quasiSeparated_iff_diagonal_quasiCompact {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiSeparated f ↔ QuasiCompact (chapter10Diagonal f) := by
  simpa [chapter10Diagonal] using (quasiSeparated_iff f)

/-- The source's unramified condition is locally finite type plus open diagonal. -/
theorem chapter10_unramified_iff_diagonal_openImmersion {X S : Scheme.{u}} (f : X ⟶ S) :
    chapter10Unramified f ↔
      LocallyOfFiniteType f ∧ IsOpenImmersion (chapter10Diagonal f) := by
  rfl

/-- Comparison with Mathlib's formally-unramified condition. -/
theorem chapter10_unramified_iff_formallyUnramified {X S : Scheme.{u}} (f : X ⟶ S) :
    chapter10Unramified f ↔ LocallyOfFiniteType f ∧ FormallyUnramified f := by
  constructor
  · rintro ⟨hfin, hdiag⟩
    let : LocallyOfFiniteType f := hfin
    let : IsOpenImmersion (chapter10Diagonal f) := hdiag
    exact ⟨hfin, inferInstance⟩
  · rintro ⟨hfin, hformal⟩
    let : LocallyOfFiniteType f := hfin
    let : FormallyUnramified f := hformal
    exact ⟨hfin, inferInstance⟩

/-- A morphism is a monomorphism exactly when its diagonal is an isomorphism. -/
theorem chapter10_monomorphism_iff_diagonal_isIso {X S : Scheme.{u}} (f : X ⟶ S) :
    Mono f ↔ IsIso (chapter10Diagonal f) := by
  exact (pullback.isIso_diagonal_iff f).symm

/-- The canonical map from the diagonal object after base change to the original diagonal object.
It is the pullback comparison induced by the two projections to `X` and by `p : T ⟶ S`. -/
def chapter10DiagonalBaseChangeTargetMap {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) :
    pullback (chapter10BaseChangeMorphism f p) (chapter10BaseChangeMorphism f p) ⟶
      pullback f f :=
  pullback.map (chapter10BaseChangeMorphism f p) (chapter10BaseChangeMorphism f p) f f
    (chapter10BaseChangeToSource f p) (chapter10BaseChangeToSource f p) p
    (chapter10BaseChange_condition f p).symm (chapter10BaseChange_condition f p).symm

/-- Diagonals commute with arbitrary base change, up to the canonical pullback comparison. -/
theorem chapter10_diagonal_commutes_with_baseChange {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) :
    Nonempty (Arrow.mk (chapter10Diagonal (chapter10BaseChangeMorphism f p)) ≅
      Arrow.mk (pullback.snd (chapter10Diagonal f)
        (chapter10DiagonalBaseChangeTargetMap f p))) := by
  let q := chapter10BaseChangeMorphism f p
  let r := chapter10BaseChangeToSource f p
  let m := chapter10DiagonalBaseChangeTargetMap f p
  have hm_fst : m ≫ pullback.fst f f = pullback.fst q q ≫ r := by
    simp [m, q, r, chapter10DiagonalBaseChangeTargetMap,
      chapter10BaseChangeToSource, chapter10BaseChangeMorphism, pullback.map]
    rw [pullback.lift_fst]
  have hm_snd : m ≫ pullback.snd f f = pullback.snd q q ≫ r := by
    simp [m, q, r, chapter10DiagonalBaseChangeTargetMap,
      chapter10BaseChangeToSource, chapter10BaseChangeMorphism, pullback.map]
    rw [pullback.lift_snd]
  have hcompat : r ≫ chapter10Diagonal f = chapter10Diagonal q ≫ m := by
    apply pullback.hom_ext
    · simp only [Category.assoc, chapter10Diagonal, pullback.diagonal_fst, hm_fst]
      simp
    · simp only [Category.assoc, chapter10Diagonal, pullback.diagonal_snd, hm_snd]
      simp
  let eHom : pullback f p ⟶ pullback (chapter10Diagonal f) m :=
    pullback.lift r (chapter10Diagonal q) hcompat
  let eInv : pullback (chapter10Diagonal f) m ⟶ pullback f p :=
    pullback.snd (chapter10Diagonal f) m ≫ pullback.fst q q
  have heHom_fst : eHom ≫ pullback.fst (chapter10Diagonal f) m = r := by
    simp [eHom]
    rw [pullback.lift_fst]
  have heHom_snd : eHom ≫ pullback.snd (chapter10Diagonal f) m =
      chapter10Diagonal q := by
    simp [eHom]
    rw [pullback.lift_snd]
  have heInv_fst : eInv ≫ r =
      pullback.fst (chapter10Diagonal f) m := by
    calc
      eInv ≫ r =
          pullback.snd (chapter10Diagonal f) m ≫
            (pullback.fst q q ≫ r) := by simp [eInv, Category.assoc]
      _ = pullback.snd (chapter10Diagonal f) m ≫
          (m ≫ pullback.fst f f) := by rw [hm_fst]
      _ = (pullback.snd (chapter10Diagonal f) m ≫ m) ≫
          pullback.fst f f := by simp only [Category.assoc]
      _ = (pullback.fst (chapter10Diagonal f) m ≫ chapter10Diagonal f) ≫
          pullback.fst f f := by rw [← pullback.condition]
      _ = pullback.fst (chapter10Diagonal f) m := by
        rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have heInv_snd : eInv ≫ pullback.snd f p =
      pullback.snd (chapter10Diagonal f) m ≫ pullback.fst q q ≫
        pullback.snd f p := by
    simp [eInv, Category.assoc]
  have hpair : pullback.snd (chapter10Diagonal f) m ≫ pullback.fst q q =
      pullback.snd (chapter10Diagonal f) m ≫ pullback.snd q q := by
    apply pullback.hom_ext
    · calc
        pullback.snd (chapter10Diagonal f) m ≫ pullback.fst q q ≫ r =
            pullback.fst (chapter10Diagonal f) m := by
              simpa [eInv, Category.assoc] using heInv_fst
        _ = pullback.snd (chapter10Diagonal f) m ≫
            pullback.snd q q ≫ r := by
              calc
                pullback.fst (chapter10Diagonal f) m =
                    pullback.snd (chapter10Diagonal f) m ≫ m ≫
                      pullback.snd f f := by
                        calc
                          pullback.fst (chapter10Diagonal f) m =
                              (pullback.fst (chapter10Diagonal f) m ≫
                                chapter10Diagonal f) ≫ pullback.snd f f := by
                                  rw [Category.assoc, pullback.diagonal_snd,
                                    Category.comp_id]
                          _ = (pullback.snd (chapter10Diagonal f) m ≫ m) ≫
                              pullback.snd f f := by rw [pullback.condition]
                          _ = pullback.snd (chapter10Diagonal f) m ≫ m ≫
                              pullback.snd f f := by simp only [Category.assoc]
                _ = pullback.snd (chapter10Diagonal f) m ≫
                    pullback.snd q q ≫ r := by rw [hm_snd]
    · change
        (pullback.snd (chapter10Diagonal f) m ≫ pullback.fst q q) ≫ q =
          (pullback.snd (chapter10Diagonal f) m ≫ pullback.snd q q) ≫ q
      rw [Category.assoc, pullback.condition, Category.assoc]
  have heInv_hom_snd : eInv ≫ chapter10Diagonal q =
      pullback.snd (chapter10Diagonal f) m := by
    apply pullback.hom_ext
    · simp [eInv, Category.assoc]
    · simpa [eInv, Category.assoc] using hpair
  let e : pullback f p ≅ pullback (chapter10Diagonal f) m :=
    { hom := eHom
      inv := eInv
      hom_inv_id := by
        apply pullback.hom_ext
        · change eHom ≫ (eInv ≫ r) = r
          rw [heInv_fst, heHom_fst]
        · calc
            eHom ≫ eInv ≫ pullback.snd f p =
                eHom ≫
                  (pullback.snd (chapter10Diagonal f) m ≫ pullback.fst q q ≫
                    pullback.snd f p) := by rw [heInv_snd]
            _ = (eHom ≫ pullback.snd (chapter10Diagonal f) m) ≫
                pullback.fst q q ≫ pullback.snd f p := by
                  simp only [Category.assoc]
            _ = chapter10Diagonal q ≫ pullback.fst q q ≫
                pullback.snd f p := by rw [heHom_snd]
            _ = pullback.snd f p := by
              rw [← Category.assoc, pullback.diagonal_fst, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, heHom_fst, heInv_fst]
          simp
        · rw [Category.assoc, heHom_snd, heInv_hom_snd]
          simp }
  exact ⟨Arrow.isoMk e (Iso.refl _) heHom_snd⟩

/-- Any diagonal property stable under base change remains stable for the base-changed morphism. -/
theorem chapter10_diagonal_property_baseChange
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso] [P.IsStableUnderBaseChange]
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hf : P (chapter10Diagonal f)) : P (chapter10Diagonal (chapter10BaseChangeMorphism f p)) := by
  obtain ⟨e⟩ := chapter10_diagonal_commutes_with_baseChange f p
  apply (MorphismProperty.arrow_mk_iso_iff P e).2
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := P)
    (IsPullback.of_hasPullback (chapter10Diagonal f)
      (chapter10DiagonalBaseChangeTargetMap f p)) hf

private theorem chapter10_diagonal_baseChange_fpqcCover {X S T : Scheme.{u}}
    (f : X ⟶ S) (p : T ⟶ S) (hp : Chapter10FpqcCover p) :
    Chapter10FpqcCover (chapter10DiagonalBaseChangeTargetMap f p) := by
  have hcond :
      chapter10DiagonalBaseChangeTargetMap f p ≫ pullback.fst f f ≫ f =
        pullback.fst (chapter10BaseChangeMorphism f p)
            (chapter10BaseChangeMorphism f p) ≫
          chapter10BaseChangeMorphism f p ≫ p := by
    simp [chapter10DiagonalBaseChangeTargetMap, chapter10BaseChangeMorphism,
      chapter10BaseChangeToSource, pullback.map]
    rw [pullback.lift_snd_assoc]
    calc
      _ = pullback.snd (chapter10BaseChangeMorphism f p)
          (chapter10BaseChangeMorphism f p) ≫
            chapter10BaseChangeMorphism f p ≫ p := by
        simpa only [Category.assoc, chapter10BaseChangeToSource,
          chapter10BaseChangeMorphism] using
          congrArg
            (fun k =>
              pullback.snd (chapter10BaseChangeMorphism f p)
                  (chapter10BaseChangeMorphism f p) ≫ k)
            (chapter10BaseChange_condition f p)
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ p)
            (pullback.condition
              (f := chapter10BaseChangeMorphism f p)
              (g := chapter10BaseChangeMorphism f p)).symm
  let q := chapter10BaseChangeMorphism f p
  let r := chapter10BaseChangeToSource f p
  let m := chapter10DiagonalBaseChangeTargetMap f p
  let g : pullback f f ⟶ S := pullback.fst f f ≫ f
  have hm_fst : m ≫ pullback.fst f f = pullback.fst q q ≫ r := by
    simp [m, q, r, chapter10DiagonalBaseChangeTargetMap,
      chapter10BaseChangeToSource, chapter10BaseChangeMorphism, pullback.map]
    rw [pullback.lift_fst]
  have hm_snd : m ≫ pullback.snd f f = pullback.snd q q ≫ r := by
    simp [m, q, r, chapter10DiagonalBaseChangeTargetMap,
      chapter10BaseChangeToSource, chapter10BaseChangeMorphism, pullback.map]
    rw [pullback.lift_snd]
  have hcond' : m ≫ g = (pullback.fst q q ≫ q) ≫ p := by
    simpa only [g, q, m, Category.assoc] using hcond
  let eHom : pullback q q ⟶ pullback g p :=
    pullback.lift m (pullback.fst q q ≫ q) hcond'
  let u₁ : pullback g p ⟶ pullback f p :=
    pullback.lift
      (pullback.fst g p ≫ pullback.fst f f)
      (pullback.snd g p) (by
        simpa [g, Category.assoc] using
          (pullback.condition :
            pullback.fst g p ≫ g = pullback.snd g p ≫ p))
  let u₂ : pullback g p ⟶ pullback f p :=
    pullback.lift
      (pullback.fst g p ≫ pullback.snd f f)
      (pullback.snd g p) (by
        calc
          (pullback.fst g p ≫ pullback.snd f f) ≫ f =
              pullback.fst g p ≫ (pullback.fst f f ≫ f) := by
                simpa only [Category.assoc] using
                  congrArg (fun k => pullback.fst g p ≫ k)
                    (pullback.condition :
                      pullback.fst f f ≫ f = pullback.snd f f ≫ f).symm
          _ = pullback.fst g p ≫ g := rfl
          _ = pullback.snd g p ≫ p := pullback.condition)
  let eInv : pullback g p ⟶ pullback q q :=
    pullback.lift u₁ u₂ (by
      change u₁ ≫ pullback.snd f p = u₂ ≫ pullback.snd f p
      dsimp [u₁, u₂]
      rw [pullback.lift_snd, pullback.lift_snd])
  have heHom_fst : eHom ≫ pullback.fst g p = m := by
    dsimp [eHom]
    rw [pullback.lift_fst]
  have heHom_snd : eHom ≫ pullback.snd g p = pullback.fst q q ≫ q := by
    dsimp [eHom]
    rw [pullback.lift_snd]
  have hu₁_fst : u₁ ≫ pullback.fst f p =
      pullback.fst g p ≫ pullback.fst f f := by
    dsimp [u₁]
    rw [pullback.lift_fst]
  have hu₁_snd : u₁ ≫ pullback.snd f p = pullback.snd g p := by
    dsimp [u₁]
    rw [pullback.lift_snd]
  have hu₂_fst : u₂ ≫ pullback.fst f p =
      pullback.fst g p ≫ pullback.snd f f := by
    dsimp [u₂]
    rw [pullback.lift_fst]
  have hu₂_snd : u₂ ≫ pullback.snd f p = pullback.snd g p := by
    dsimp [u₂]
    rw [pullback.lift_snd]
  have heInv_fst : eInv ≫ pullback.fst q q = u₁ := by
    dsimp [eInv]
    rw [pullback.lift_fst]
  have heInv_snd : eInv ≫ pullback.snd q q = u₂ := by
    dsimp [eInv]
    rw [pullback.lift_snd]
  have hu₁_r : u₁ ≫ r = pullback.fst g p ≫ pullback.fst f f := by
    simpa [r] using hu₁_fst
  have hu₂_r : u₂ ≫ r = pullback.fst g p ≫ pullback.snd f f := by
    simpa [r] using hu₂_fst
  have hu₁_q : u₁ ≫ q = pullback.snd g p := by
    simpa [q] using hu₁_snd
  have hqpair : pullback.fst q q ≫ q = pullback.snd q q ≫ q :=
    pullback.condition
  let e : pullback q q ≅ pullback g p :=
    { hom := eHom
      inv := eInv
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, heInv_fst]
          apply pullback.hom_ext
          · simp only [Category.id_comp]
            rw [Category.assoc, hu₁_fst, ← Category.assoc, heHom_fst, hm_fst]
          · simp only [Category.id_comp]
            rw [Category.assoc, hu₁_snd, heHom_snd]
        · rw [Category.assoc, heInv_snd]
          apply pullback.hom_ext
          · simp only [Category.id_comp]
            rw [Category.assoc, hu₂_fst, ← Category.assoc, heHom_fst, hm_snd]
          · simp only [Category.id_comp]
            rw [Category.assoc, hu₂_snd, heHom_snd, hqpair]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, heHom_fst]
          apply pullback.hom_ext
          · simp only [Category.id_comp]
            rw [Category.assoc, hm_fst, ← Category.assoc, heInv_fst, hu₁_r]
          · simp only [Category.id_comp]
            rw [Category.assoc, hm_snd, ← Category.assoc, heInv_snd, hu₂_r]
        · simp only [Category.id_comp]
          rw [Category.assoc, heHom_snd, ← Category.assoc, heInv_fst, hu₁_q] }
  have hmcover : Chapter10FpqcCover m := by
    have : IsIso e.hom := e.isIso_hom
    have : Surjective (pullback.fst g p) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Surjective) (IsPullback.of_hasPullback g p).flip hp.surjective
    have : Flat (pullback.fst g p) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Flat) (IsPullback.of_hasPullback g p).flip hp.flat
    have : QuasiCompact (pullback.fst g p) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @QuasiCompact) (IsPullback.of_hasPullback g p).flip hp.quasiCompact
    rw [← heHom_fst]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  simpa [m] using hmcover

/-- Separatedness descends from an fpqc base change through the closed diagonal. -/
theorem chapter10_separated_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : IsSeparated (chapter10BaseChangeMorphism f p)) :
    IsSeparated f := by
  let q := chapter10BaseChangeMorphism f p
  let m := chapter10DiagonalBaseChangeTargetMap f p
  have hdiagBase : IsClosedImmersion (chapter10Diagonal q) :=
    (chapter10_separated_iff_diagonal_closedImmersion q).1 hf
  have hUCq : UniversallyClosed (chapter10Diagonal q) := by
    have : IsClosedImmersion (chapter10Diagonal q) := hdiagBase
    infer_instance
  have hLFTq : LocallyOfFiniteType (chapter10Diagonal q) := by
    have : IsClosedImmersion (chapter10Diagonal q) := hdiagBase
    infer_instance
  obtain ⟨eDiag⟩ := chapter10_diagonal_commutes_with_baseChange f p
  have hUCpull : UniversallyClosed (pullback.snd (chapter10Diagonal f) m) := by
    have : MorphismProperty.RespectsIso (@UniversallyClosed) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff (P := @UniversallyClosed) eDiag).1 hUCq
  have hLFTpull : LocallyOfFiniteType (pullback.snd (chapter10Diagonal f) m) := by
    have : MorphismProperty.RespectsIso (@LocallyOfFiniteType) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff (P := @LocallyOfFiniteType) eDiag).1 hLFTq
  have hmcover : Chapter10FpqcCover m := by
    simpa [m] using chapter10_diagonal_baseChange_fpqcCover f p hp
  have hUC : UniversallyClosed (chapter10Diagonal f) := by
    have hdesc : MorphismProperty.DescendsAlong
        (@UniversallyClosed : MorphismProperty _) chapter10FpqcMorphismProperty := by
      infer_instance
    exact hdesc.of_isPullback (IsPullback.of_hasPullback (chapter10Diagonal f) m).flip
      ⟨⟨hmcover.surjective, hmcover.flat⟩, hmcover.quasiCompact⟩ hUCpull
  have hLFT : LocallyOfFiniteType (chapter10Diagonal f) := by
    have hdesc : MorphismProperty.DescendsAlong
        (@LocallyOfFiniteType : MorphismProperty _) chapter10FpqcMorphismProperty := by
      infer_instance
    exact hdesc.of_isPullback (IsPullback.of_hasPullback (chapter10Diagonal f) m).flip
      ⟨⟨hmcover.surjective, hmcover.flat⟩, hmcover.quasiCompact⟩ hLFTpull
  have hproper : IsProper (chapter10Diagonal f) := by
    refine (isProper_iff (chapter10Diagonal f)).2 ⟨?_, hUC, hLFT⟩
    infer_instance
  apply (chapter10_separated_iff_diagonal_closedImmersion f).2
  exact (IsClosedImmersion.iff_isProper_and_mono (chapter10Diagonal f)).2
    ⟨hproper, inferInstance⟩

/-- Quasi-separatedness descends from an fpqc base change through the quasi-compact diagonal. -/
theorem chapter10_quasiSeparated_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : QuasiSeparated (chapter10BaseChangeMorphism f p)) :
    QuasiSeparated f := by
  have hcond :
      chapter10DiagonalBaseChangeTargetMap f p ≫ pullback.fst f f ≫ f =
        pullback.fst (chapter10BaseChangeMorphism f p)
            (chapter10BaseChangeMorphism f p) ≫
          chapter10BaseChangeMorphism f p ≫ p := by
    simp [chapter10DiagonalBaseChangeTargetMap, chapter10BaseChangeMorphism,
      chapter10BaseChangeToSource, pullback.map]
    rw [pullback.lift_snd_assoc]
    calc
      _ = pullback.snd (chapter10BaseChangeMorphism f p)
          (chapter10BaseChangeMorphism f p) ≫
            chapter10BaseChangeMorphism f p ≫ p := by
        simpa only [Category.assoc, chapter10BaseChangeToSource,
          chapter10BaseChangeMorphism] using
          congrArg
            (fun k =>
              pullback.snd (chapter10BaseChangeMorphism f p)
                  (chapter10BaseChangeMorphism f p) ≫ k)
            (chapter10BaseChange_condition f p)
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ p)
            (pullback.condition
              (f := chapter10BaseChangeMorphism f p)
              (g := chapter10BaseChangeMorphism f p)).symm
  let q := chapter10BaseChangeMorphism f p
  let r := chapter10BaseChangeToSource f p
  let m := chapter10DiagonalBaseChangeTargetMap f p
  let g : pullback f f ⟶ S := pullback.fst f f ≫ f
  have hm_fst : m ≫ pullback.fst f f = pullback.fst q q ≫ r := by
    simp [m, q, r, chapter10DiagonalBaseChangeTargetMap,
      chapter10BaseChangeToSource, chapter10BaseChangeMorphism, pullback.map]
    rw [pullback.lift_fst]
  have hm_snd : m ≫ pullback.snd f f = pullback.snd q q ≫ r := by
    simp [m, q, r, chapter10DiagonalBaseChangeTargetMap,
      chapter10BaseChangeToSource, chapter10BaseChangeMorphism, pullback.map]
    rw [pullback.lift_snd]
  have hcond' : m ≫ g = (pullback.fst q q ≫ q) ≫ p := by
    simpa only [g, q, m, Category.assoc] using hcond
  let eHom : pullback q q ⟶ pullback g p :=
    pullback.lift m (pullback.fst q q ≫ q) hcond'
  let u₁ : pullback g p ⟶ pullback f p :=
    pullback.lift
      (pullback.fst g p ≫ pullback.fst f f)
      (pullback.snd g p) (by
        simpa [g, Category.assoc] using
          (pullback.condition :
            pullback.fst g p ≫ g = pullback.snd g p ≫ p))
  let u₂ : pullback g p ⟶ pullback f p :=
    pullback.lift
      (pullback.fst g p ≫ pullback.snd f f)
      (pullback.snd g p) (by
        calc
          (pullback.fst g p ≫ pullback.snd f f) ≫ f =
              pullback.fst g p ≫ (pullback.fst f f ≫ f) := by
                simpa only [Category.assoc] using
                  congrArg (fun k => pullback.fst g p ≫ k)
                    (pullback.condition :
                      pullback.fst f f ≫ f = pullback.snd f f ≫ f).symm
          _ = pullback.fst g p ≫ g := rfl
          _ = pullback.snd g p ≫ p := pullback.condition)
  let eInv : pullback g p ⟶ pullback q q :=
    pullback.lift u₁ u₂ (by
      change u₁ ≫ pullback.snd f p = u₂ ≫ pullback.snd f p
      dsimp [u₁, u₂]
      rw [pullback.lift_snd, pullback.lift_snd])
  have heHom_fst : eHom ≫ pullback.fst g p = m := by
    dsimp [eHom]
    rw [pullback.lift_fst]
  have heHom_snd : eHom ≫ pullback.snd g p = pullback.fst q q ≫ q := by
    dsimp [eHom]
    rw [pullback.lift_snd]
  have hu₁_fst : u₁ ≫ pullback.fst f p =
      pullback.fst g p ≫ pullback.fst f f := by
    dsimp [u₁]
    rw [pullback.lift_fst]
  have hu₁_snd : u₁ ≫ pullback.snd f p = pullback.snd g p := by
    dsimp [u₁]
    rw [pullback.lift_snd]
  have hu₂_fst : u₂ ≫ pullback.fst f p =
      pullback.fst g p ≫ pullback.snd f f := by
    dsimp [u₂]
    rw [pullback.lift_fst]
  have hu₂_snd : u₂ ≫ pullback.snd f p = pullback.snd g p := by
    dsimp [u₂]
    rw [pullback.lift_snd]
  have heInv_fst : eInv ≫ pullback.fst q q = u₁ := by
    dsimp [eInv]
    rw [pullback.lift_fst]
  have heInv_snd : eInv ≫ pullback.snd q q = u₂ := by
    dsimp [eInv]
    rw [pullback.lift_snd]
  have hu₁_r : u₁ ≫ r = pullback.fst g p ≫ pullback.fst f f := by
    simpa [r] using hu₁_fst
  have hu₂_r : u₂ ≫ r = pullback.fst g p ≫ pullback.snd f f := by
    simpa [r] using hu₂_fst
  have hu₁_q : u₁ ≫ q = pullback.snd g p := by
    simpa [q] using hu₁_snd
  have hqpair : pullback.fst q q ≫ q = pullback.snd q q ≫ q :=
    pullback.condition
  let e : pullback q q ≅ pullback g p :=
    { hom := eHom
      inv := eInv
      hom_inv_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, heInv_fst]
          apply pullback.hom_ext
          · simp only [Category.id_comp]
            rw [Category.assoc, hu₁_fst, ← Category.assoc, heHom_fst, hm_fst]
          · simp only [Category.id_comp]
            rw [Category.assoc, hu₁_snd, heHom_snd]
        · rw [Category.assoc, heInv_snd]
          apply pullback.hom_ext
          · simp only [Category.id_comp]
            rw [Category.assoc, hu₂_fst, ← Category.assoc, heHom_fst, hm_snd]
          · simp only [Category.id_comp]
            rw [Category.assoc, hu₂_snd, heHom_snd, hqpair]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [Category.assoc, heHom_fst]
          apply pullback.hom_ext
          · simp only [Category.id_comp]
            rw [Category.assoc, hm_fst, ← Category.assoc, heInv_fst, hu₁_r]
          · simp only [Category.id_comp]
            rw [Category.assoc, hm_snd, ← Category.assoc, heInv_snd, hu₂_r]
        · simp only [Category.id_comp]
          rw [Category.assoc, heHom_snd, ← Category.assoc, heInv_fst, hu₁_q] }
  have hmcover : Chapter10FpqcCover m := by
    have : IsIso e.hom := e.isIso_hom
    have : Surjective (pullback.fst g p) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Surjective) (IsPullback.of_hasPullback g p).flip hp.surjective
    have : Flat (pullback.fst g p) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Flat) (IsPullback.of_hasPullback g p).flip hp.flat
    have : QuasiCompact (pullback.fst g p) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @QuasiCompact) (IsPullback.of_hasPullback g p).flip hp.quasiCompact
    rw [← heHom_fst]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨eDiag⟩ := chapter10_diagonal_commutes_with_baseChange f p
  have hdiagbase : QuasiCompact (pullback.snd (chapter10Diagonal f) m) := by
    have : MorphismProperty.RespectsIso (@QuasiCompact) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hdiagq : QuasiCompact (chapter10Diagonal q) :=
      (chapter10_quasiSeparated_iff_diagonal_quasiCompact q).1 hf
    exact (MorphismProperty.arrow_mk_iso_iff (P := @QuasiCompact) eDiag).1 hdiagq
  apply (chapter10_quasiSeparated_iff_diagonal_quasiCompact f).2
  exact chapter10_quasiCompact_descends (chapter10Diagonal f) m hmcover hdiagbase

/-- Monomorphisms descend from an fpqc base change through the diagonal isomorphism. -/
theorem chapter10_monomorphism_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : Mono (chapter10BaseChangeMorphism f p)) :
    Mono f := by
  let : Surjective p := hp.surjective
  let : Flat p := hp.flat
  let : QuasiCompact p := hp.quasiCompact
  let : Mono (chapter10BaseChangeMorphism f p) := hf
  constructor
  intro Z g h gh
  let g' : Over.mk (g ≫ f) ⟶ Over.mk f := Over.homMk g
  let h' : Over.mk (g ≫ f) ⟶ Over.mk f := Over.homMk h
  have gh' : g' = h' := by
    apply (Over.pullback p).map_injective
    apply Over.OverMorphism.ext
    apply (cancel_mono (chapter10BaseChangeMorphism f p)).1
    simp [g', h', chapter10BaseChangeMorphism]
    rw [pullback.lift_snd, pullback.lift_snd]
  have gh'' := congrArg Over.Hom.left gh'
  simpa [g', h'] using gh''

/-- Smooth morphisms carry the local finite-presentation hypothesis used by the fiber criterion. -/
theorem chapter10_smooth_has_local_finite_presentation {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Smooth f) : LocallyOfFinitePresentation f := by
  let : Smooth f := hf
  infer_instance

/-- Étale morphisms carry the local finite-presentation hypothesis. -/
theorem chapter10_etale_has_local_finite_presentation {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : Etale f) : LocallyOfFinitePresentation f := by
  let : Etale f := hf
  infer_instance

/-- A closed immersion descends from its fpqc pullback. -/
theorem chapter10_closedImmersion_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : IsClosedImmersion (chapter10BaseChangeMorphism f p)) :
    IsClosedImmersion f := by
  let q := chapter10BaseChangeMorphism f p
  have hbase := (IsClosedImmersion.iff_isProper_and_mono q).1 hf
  have hproperBase := (isProper_iff q).1 hbase.1
  have hproper : IsProper f := by
    have hUC : UniversallyClosed f := by
      have hdesc : MorphismProperty.DescendsAlong
          (@UniversallyClosed : MorphismProperty _) chapter10FpqcMorphismProperty := by
        infer_instance
      exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
        ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hproperBase.2.1
    have hLFT : LocallyOfFiniteType f := by
      have hdesc : MorphismProperty.DescendsAlong
          (@LocallyOfFiniteType : MorphismProperty _) chapter10FpqcMorphismProperty := by
        infer_instance
      exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
        ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hproperBase.2.2
    refine (isProper_iff f).2 ⟨chapter10_separated_descends f p hp hproperBase.1, hUC, hLFT⟩
  exact (IsClosedImmersion.iff_isProper_and_mono f).2
    ⟨hproper, chapter10_monomorphism_descends f p hp hbase.2⟩

/-- An isomorphism descends from its fpqc pullback. -/
theorem chapter10_isomorphism_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : IsIso (chapter10BaseChangeMorphism f p)) : IsIso f := by
  have hdesc : MorphismProperty.DescendsAlong
      (MorphismProperty.isomorphisms Scheme.{u})
        chapter10FpqcMorphismProperty := inferInstance
  change (MorphismProperty.isomorphisms Scheme.{u}) f
  exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
    ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

/-- A flat, locally finitely presented monomorphism is an open immersion. -/
theorem chapter10_openImmersion_of_flat_of_local_finite_presentation_of_mono
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) (hmono : Mono f) :
    IsOpenImmersion f := by
  let : Flat f := hflat
  let : LocallyOfFinitePresentation f := hfp
  let : Mono f := hmono
  exact IsOpenImmersion.of_flat_of_mono f

/-- Open immersions descend from compatible fpqc-local open data. -/
theorem chapter10_openImmersion_descends {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : IsOpenImmersion (chapter10BaseChangeMorphism f p)) :
    IsOpenImmersion f := by
  have hdesc : MorphismProperty.DescendsAlong
      (@IsOpenImmersion : MorphismProperty Scheme.{u})
        chapter10FpqcMorphismProperty := inferInstance
  exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
    ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

/-- The image argument for the open-immersion descent theorem: flat locally finitely presented maps
are open, so a descended monomorphism identifies its source with an open image. -/
theorem chapter10_openImmersion_image_argument {X S : Scheme.{u}} (f : X ⟶ S)
    (hflat : Flat f) (hfp : LocallyOfFinitePresentation f) (hmono : Mono f) :
    IsOpen (Set.range f.base) ∧ IsOpenImmersion f := by
  have hopen : IsOpenImmersion f :=
    chapter10_openImmersion_of_flat_of_local_finite_presentation_of_mono f hflat hfp hmono
  let : IsOpenImmersion f := hopen
  exact ⟨by simpa using IsOpenImmersion.isOpen_range f, hopen⟩

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
