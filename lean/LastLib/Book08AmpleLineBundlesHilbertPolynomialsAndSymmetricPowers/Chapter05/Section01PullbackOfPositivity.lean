import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.Dependencies

/-!
# 5.1 Pullback of positivity

The declarations in this section deliberately have no flatness hypotheses: arbitrary scheme
base change preserves the explicit embedding and affine-chart tests used by positivity.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05

noncomputable section

theorem veryAmple_baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : LineBundle X)
    (hL : IsVeryAmple f L) :
    IsVeryAmple (baseChangeToBase f g) (baseChangeLineBundle f g L) := by
  rcases hL with ⟨w⟩
  let map : pullback f g ⟶ pullback w.projectiveBundle.projection g :=
    pullback.map f g w.projectiveBundle.projection g w.map (𝟙 T) (𝟙 S)
      (by simp [w.over]) (by simp)
  let hcomp : map ≫ pullback.fst w.projectiveBundle.projection g =
      pullback.fst f g ≫ w.map := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _
  have hmap_snd : map ≫ pullback.snd w.projectiveBundle.projection g =
      pullback.snd f g := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    simpa using (pullback.lift_snd _ _ _)
  have hmap : IsImmersion map := by
    have hpb : IsPullback (pullback.fst f g) map w.map
        (pullback.fst w.projectiveBundle.projection g) :=
      IsPullback.mk' hcomp.symm
        (by
          intro Z a b h₁ h₂
          apply pullback.hom_ext
          · exact h₁
          · have hh := congrArg
              (fun k => k ≫ pullback.snd w.projectiveBundle.projection g) h₂
            simpa only [Category.assoc, hmap_snd] using hh)
        (by
          intro Z a b hab
          have hc : a ≫ f =
              (b ≫ pullback.snd w.projectiveBundle.projection g) ≫ g := by
            calc
              a ≫ f = a ≫ (w.map ≫ w.projectiveBundle.projection) := by rw [w.over]
              _ = (a ≫ w.map) ≫ w.projectiveBundle.projection := by simp [Category.assoc]
              _ = (b ≫ pullback.fst w.projectiveBundle.projection g) ≫
                  w.projectiveBundle.projection := by rw [hab]
              _ = b ≫ (pullback.snd w.projectiveBundle.projection g ≫ g) := by
                simp [Category.assoc, pullback.condition]
              _ = (b ≫ pullback.snd w.projectiveBundle.projection g) ≫ g := by
                simp [Category.assoc]
          refine ⟨pullback.lift a (b ≫ pullback.snd w.projectiveBundle.projection g) hc,
            pullback.lift_fst _ _ _, ?_⟩
          apply pullback.hom_ext
          · rw [Category.assoc, hcomp, pullback.lift_fst_assoc, hab]
          · rw [Category.assoc, hmap_snd, pullback.lift_snd])
    exact MorphismProperty.of_isPullback hpb w.immersion
  let eSource :
      (Scheme.Modules.pullback (pullback.fst f g)).obj L.sheaf ≅
        (Scheme.Modules.pullback (pullback.fst f g)).obj
          ((Scheme.Modules.pullback w.map).obj w.projectiveBundle.tautological) :=
    (Scheme.Modules.pullback (pullback.fst f g)).mapIso w.pullback_iso
  let eSourceComp :=
    Chapter04.chapter04PullbackCompositionIso (pullback.fst f g) w.map
      w.projectiveBundle.tautological
  let eTargetComp :=
    Chapter04.chapter04PullbackCompositionIso map
      (pullback.fst w.projectiveBundle.projection g)
      w.projectiveBundle.tautological
  let eComparison := Scheme.Modules.pullbackCongr hcomp.symm
  refine ⟨{ projectiveBundle := RelativeProjectiveBundleData.baseChange
              w.projectiveBundle g
            map := map
            immersion := hmap
            over := by
              change map ≫ pullback.snd w.projectiveBundle.projection g =
                pullback.snd f g
              exact hmap_snd
            pullback_iso :=
              eSource ≪≫
                (eSourceComp.symm ≪≫
                  (eComparison.app w.projectiveBundle.tautological) ≪≫
                  eTargetComp) }⟩

theorem ample_baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (L : LineBundle X)
    (hL : IsAmple f L) :
    IsAmple (baseChangeToBase f g) (baseChangeLineBundle f g L) := by sorry

private theorem chapter05_baseChange_map_isPullback
    {X S T Y : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (p : Y ⟶ S)
    (m : X ⟶ Y) (hm : m ≫ p = f) :
    IsPullback (pullback.fst f g)
      (pullback.map f g p g m (𝟙 T) (𝟙 S) (by simp [hm]) (by simp))
      m (pullback.fst p g) := by
  let map : pullback f g ⟶ pullback p g :=
    pullback.map f g p g m (𝟙 T) (𝟙 S) (by simp [hm]) (by simp)
  have hcomp : map ≫ pullback.fst p g = pullback.fst f g ≫ m := by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
    exact pullback.lift_fst _ _ _
  have hmap_snd : map ≫ pullback.snd p g = pullback.snd f g := by
    change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
    simpa using (pullback.lift_snd _ _ _)
  have hpb : IsPullback (pullback.fst f g) map m (pullback.fst p g) :=
    IsPullback.mk' hcomp.symm
      (by
        intro Z a b h₁ h₂
        apply pullback.hom_ext
        · exact h₁
        · have hh := congrArg (fun k => k ≫ pullback.snd p g) h₂
          simpa only [Category.assoc, hmap_snd] using hh)
      (by
        intro Z a b hab
        have hc : a ≫ f = (b ≫ pullback.snd p g) ≫ g := by
          calc
            a ≫ f = a ≫ (m ≫ p) := by rw [hm]
            _ = (a ≫ m) ≫ p := by simp [Category.assoc]
            _ = (b ≫ pullback.fst p g) ≫ p := by rw [hab]
            _ = b ≫ (pullback.snd p g ≫ g) := by
              simp [Category.assoc, pullback.condition]
            _ = (b ≫ pullback.snd p g) ≫ g := by simp [Category.assoc]
        refine ⟨pullback.lift a (b ≫ pullback.snd p g) hc,
          pullback.lift_fst _ _ _, ?_⟩
        apply pullback.hom_ext
        · rw [Category.assoc, hcomp, pullback.lift_fst_assoc, hab]
        · rw [Category.assoc, hmap_snd, pullback.lift_snd])
  simpa [map]

theorem quasiProjective_baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsQuasiProjectiveMorphism f) :
    IsQuasiProjectiveMorphism (baseChangeToBase f g) := by
  rcases hf with ⟨w⟩
  let map : pullback f g ⟶ pullback w.projectiveBundle.projection g :=
    pullback.map f g w.projectiveBundle.projection g w.embedding (𝟙 T) (𝟙 S)
      (by simp [w.over]) (by simp)
  have hmap : IsImmersion map := by
    exact MorphismProperty.of_isPullback
      (chapter05_baseChange_map_isPullback f g w.projectiveBundle.projection
        w.embedding w.over) w.immersion
  refine ⟨{ projectiveBundle := RelativeProjectiveBundleData.baseChange
              w.projectiveBundle g
            embedding := map
            over := ?_
            immersion := hmap }⟩
  change map ≫ pullback.snd w.projectiveBundle.projection g = pullback.snd f g
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  simpa using (pullback.lift_snd _ _ _)

theorem projective_baseChange {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsProjectiveMorphism f) :
    IsProjectiveMorphism (baseChangeToBase f g) := by
  rcases hf with ⟨w⟩
  let map : pullback f g ⟶ pullback w.projectiveBundle.projection g :=
    pullback.map f g w.projectiveBundle.projection g w.map (𝟙 T) (𝟙 S)
      (by simp [w.over]) (by simp)
  have hmap : IsClosedImmersion map := by
    exact MorphismProperty.of_isPullback
      (chapter05_baseChange_map_isPullback f g w.projectiveBundle.projection
        w.map w.over) w.closedImmersion
  refine ⟨{ projectiveBundle := RelativeProjectiveBundleData.baseChange
              w.projectiveBundle g
            map := map
            closedImmersion := hmap
            over := ?_ }⟩
  change map ≫ pullback.snd w.projectiveBundle.projection g = pullback.snd f g
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = _
  simpa using (pullback.lift_snd _ _ _)

theorem veryAmple_restrict {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (L : LineBundle X)
    (hL : IsVeryAmple f L) :
    IsVeryAmple (f ∣_ U) (L.pullback (f ⁻¹ᵁ U).ι) := by
  rcases veryAmple_baseChange f U.ι L hL with ⟨w⟩
  let e := pullbackRestrictIsoRestrict f U
  let wmap : pullback f U.ι ⟶ w.projectiveBundle.space := w.map
  have hwmap : IsImmersion wmap := w.immersion
  have hwover : wmap ≫ w.projectiveBundle.projection = pullback.snd f U.ι := w.over
  have he : IsImmersion e.inv := by
    let _ : IsClosedImmersion e.inv := by infer_instance
    infer_instance
  let map : (f ⁻¹ᵁ U).toScheme ⟶ w.projectiveBundle.space := e.inv ≫ wmap
  have hmap : IsImmersion map := by
    let _ : IsImmersion e.inv := he
    let _ : IsImmersion wmap := hwmap
    dsimp [map]
    infer_instance
  refine ⟨{ projectiveBundle := w.projectiveBundle
            map := map
            immersion := hmap
            over := ?_
            pullback_iso := ?_ }⟩
  · change e.inv ≫ wmap ≫ w.projectiveBundle.projection = f ∣_ U
    rw [hwover]
    calc
      e.inv ≫ pullback.snd f U.ι = e.inv ≫ (e.hom ≫ f ∣_ U) := by
        rw [pullbackRestrictIsoRestrict_hom_morphismRestrict]
      _ = f ∣_ U := by simp
  · let eSource :
        (L.pullback (f ⁻¹ᵁ U).ι).sheaf ≅
          ((baseChangeLineBundle f U.ι L).pullback e.inv).sheaf := by
      let eLine := Classical.choice (lineBundle_pullback_comp L e.inv (pullback.fst f U.ι))
      simpa [baseChangeLineBundle, baseChange, baseChangeToSource, e] using eLine.symm
    exact eSource ≪≫
      ((Scheme.Modules.pullback e.inv).mapIso w.pullback_iso ≪≫
        (Chapter04.chapter04PullbackCompositionIso e.inv wmap
          w.projectiveBundle.tautological).symm)

theorem ample_restrict {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (L : LineBundle X)
    (hL : IsAmple f L) :
    IsAmple (f ∣_ U) (L.pullback (f ⁻¹ᵁ U).ι) := by sorry

theorem fiber_projective_of_projective {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (hf : IsProjectiveMorphism f) :
    IsProjectiveMorphism (f.fiberToSpecResidueField s) := by
  simpa [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber,
    baseChangeToBase, baseChange] using
    (projective_baseChange f (S.fromSpecResidueField s) hf)

theorem fiber_veryAmple_of_veryAmple {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (L : LineBundle X) (hL : IsVeryAmple f L) :
    IsVeryAmple (f.fiberToSpecResidueField s) (L.pullback (f.fiberι s)) := by
  change IsVeryAmple (baseChangeToBase f (S.fromSpecResidueField s))
    (baseChangeLineBundle f (S.fromSpecResidueField s) L)
  exact veryAmple_baseChange f (S.fromSpecResidueField s) L hL

theorem fiber_ample_of_ample {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (L : LineBundle X)
    (hL : IsAmple f L) :
    IsAmple (f.fiberToSpecResidueField s) (L.pullback (f.fiberι s)) := by sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05
