import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Section02TheDiagonalMethod
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter07.Section03AffineDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
## 10.3 A table of descending properties

The table is exposed as individual declarations so downstream chapters can use the weakest
hypotheses for a particular morphism property.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

private theorem chapter10_fpqc_local_of_descendsAlong_aux
    (P : MorphismProperty Scheme.{u})
    (hP : chapter10StableUnderBaseChange P)
    (hdesc : P.DescendsAlong chapter10FpqcMorphismProperty) :
    chapter10FpqcLocalOnBase P := by
  intro X S T f p hp
  constructor
  · intro hf
    exact hP f p hf
  · intro hf
    exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
      ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

theorem chapter10_affine_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsAffineHom) := by
  apply chapter10_fpqc_local_of_descendsAlong_aux
  · intro X S T f p hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsAffineHom) (IsPullback.of_hasPullback f p) hf
  · infer_instance

theorem chapter10_quasiCompact_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@QuasiCompact) := by
  intro X S T f p hp
  constructor
  · intro hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @QuasiCompact) (IsPullback.of_hasPullback f p) hf
  · intro hf
    exact chapter10_quasiCompact_descends f p hp hf

theorem chapter10_quasiSeparated_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@QuasiSeparated) := by
  intro X S T f p hp
  constructor
  · intro hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @QuasiSeparated) (IsPullback.of_hasPullback f p) hf
  · intro hf
    exact chapter10_quasiSeparated_descends f p hp hf

theorem chapter10_separated_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsSeparated) := by
  intro X S T f p hp
  constructor
  · intro hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsSeparated) (IsPullback.of_hasPullback f p) hf
  · intro hf
    exact chapter10_separated_descends f p hp hf

theorem chapter10_locallyOfFiniteType_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@LocallyOfFiniteType) := by
  apply chapter10_fpqc_local_of_descendsAlong_aux
  · intro X S T f p hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback f p) hf
  · infer_instance

theorem chapter10_finiteType_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@chapter10FiniteType) := by
  intro X S T f p hp
  change (LocallyOfFiniteType f ∧ QuasiCompact f) ↔
    (LocallyOfFiniteType (chapter10BaseChangeMorphism f p) ∧
      QuasiCompact (chapter10BaseChangeMorphism f p))
  constructor
  · rintro ⟨hfin, hqc⟩
    refine ⟨?_, ?_⟩
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback f p) hfin
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @QuasiCompact) (IsPullback.of_hasPullback f p) hqc
  · rintro ⟨hfin, hqc⟩
    have hfin' := (chapter10_locallyOfFiniteType_fpqc_local_on_base f p hp).2 hfin
    exact ⟨hfin',
      chapter10_quasiCompact_descends f p hp hqc⟩

theorem chapter10_locallyOfFinitePresentation_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@LocallyOfFinitePresentation) := by
  apply chapter10_fpqc_local_of_descendsAlong_aux
  · intro X S T f p hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @LocallyOfFinitePresentation) (IsPullback.of_hasPullback f p) hf
  · infer_instance

theorem chapter10_finitePresentation_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@chapter10FinitePresentation) := by
  intro X S T f p hp
  change (LocallyOfFinitePresentation f ∧ QuasiCompact f) ↔
    (LocallyOfFinitePresentation (chapter10BaseChangeMorphism f p) ∧
      QuasiCompact (chapter10BaseChangeMorphism f p))
  constructor
  · rintro ⟨hfin, hqc⟩
    refine ⟨?_, ?_⟩
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @LocallyOfFinitePresentation) (IsPullback.of_hasPullback f p) hfin
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @QuasiCompact) (IsPullback.of_hasPullback f p) hqc
  · rintro ⟨hfin, hqc⟩
    have hfin' := (chapter10_locallyOfFinitePresentation_fpqc_local_on_base f p hp).2 hfin
    exact ⟨hfin',
      chapter10_quasiCompact_descends f p hp hqc⟩

private theorem chapter10_ringHomFlat_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  apply RingHom.CodescendsAlong.mk RingHom.FaithfullyFlat RingHom.Flat.respectsIso
  introv h H
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  rw [RingHom.flat_algebraMap_iff] at H ⊢
  exact Module.Flat.of_flat_tensorProduct (R := R) (M := T) S

theorem chapter10_flat_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@Flat) := by
  intro X S T f p hp
  constructor
  · intro hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Flat) (IsPullback.of_hasPullback f p) hf
  · intro hf
    have hdesc := HasRingHomProperty.descendsAlong_flat
      (P := @Flat) chapter10_ringHomFlat_codescendsAlong_faithfullyFlat
    exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
      ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ hf

private theorem chapter10_finite_descends_aux {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p)
    (hf : IsFinite (chapter10BaseChangeMorphism f p)) : IsFinite f := by
  have : IsFinite (chapter10BaseChangeMorphism f p) := hf
  have hLFT : LocallyOfFiniteType f := by
    exact (chapter10_locallyOfFiniteType_fpqc_local_on_base f p hp).2 inferInstance
  have hUC : UniversallyClosed f := by
    have hdesc : MorphismProperty.DescendsAlong
        (@UniversallyClosed : MorphismProperty _) chapter10FpqcMorphismProperty := by
      infer_instance
    exact hdesc.of_isPullback (IsPullback.of_hasPullback f p).flip
      ⟨⟨hp.surjective, hp.flat⟩, hp.quasiCompact⟩ inferInstance
  have hproper : IsProper f := by
    exact (isProper_iff f).2
      ⟨chapter10_separated_descends f p hp inferInstance, hUC, hLFT⟩
  have hLQF : LocallyQuasiFinite f := by
    have : LocallyOfFiniteType f := hLFT
    apply LocallyQuasiFinite.of_finite_preimage_singleton f
    intro s
    obtain ⟨t, ht⟩ := hp.surjective.surj s
    have hfiniteT :
        ((chapter10BaseChangeMorphism f p) ⁻¹' ({t} : Set T)).Finite :=
      Scheme.Hom.finite_preimage_singleton (chapter10BaseChangeMorphism f p) t
    apply Set.Finite.subset (hfiniteT.image (chapter10BaseChangeToSource f p))
    intro x hx
    have hxs : f x = s := by simpa using hx
    obtain ⟨z, hz₁, hz₂⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f) (g := p) x t (by
        rw [hxs, ht])
    exact ⟨z, hz₂, hz₁⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

theorem chapter10_finiteLocallyFreeOfRank_fpqc_local_on_base (r : ℕ) :
    chapter10FpqcLocalOnBase (fun {_X _S} f => chapter10FiniteLocallyFreeOfRank f r) := by
  intro X S T f p hp
  constructor
  · rintro ⟨hfinite, hflat, hlfp, hrank⟩
    have : IsFinite f := hfinite
    have : Flat f := hflat
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsFinite) (IsPullback.of_hasPullback f p) hfinite
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @Flat) (IsPullback.of_hasPullback f p) hflat
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @LocallyOfFinitePresentation) (IsPullback.of_hasPullback f p) hlfp
    · intro t
      rw [Scheme.Hom.finrank_pullback_snd f p t, hrank (p t)]
  · rintro ⟨hfinite, hflat, hlfp, hrank⟩
    refine ⟨chapter10_finite_descends_aux f p hp hfinite,
      (chapter10_flat_fpqc_local_on_base f p hp).2 hflat,
      (chapter10_locallyOfFinitePresentation_fpqc_local_on_base f p hp).2 hlfp, ?_⟩
    have : IsFinite f := chapter10_finite_descends_aux f p hp hfinite
    have : Flat f := (chapter10_flat_fpqc_local_on_base f p hp).2 hflat
    intro s
    obtain ⟨t, ht⟩ := hp.surjective.surj s
    rw [← ht, ← Scheme.Hom.finrank_pullback_snd f p t]
    exact hrank t

theorem chapter10_finite_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsFinite) := by
  intro X S T f p hp
  constructor
  · intro hf
    have : IsFinite f := hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsFinite) (IsPullback.of_hasPullback f p) hf
  · intro hf
    have : IsFinite (chapter10BaseChangeMorphism f p) := hf
    exact chapter10_finite_descends_aux f p hp hf

theorem chapter10_monomorphism_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (MorphismProperty.monomorphisms Scheme.{u}) := by
  intro X S T f p hp
  change Mono f ↔ Mono (chapter10BaseChangeMorphism f p)
  constructor
  · intro hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := MorphismProperty.monomorphisms Scheme.{u})
      (IsPullback.of_hasPullback f p) hf
  · exact chapter10_monomorphism_descends f p hp

theorem chapter10_openImmersion_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsOpenImmersion) := by
  apply chapter10_fpqc_local_of_descendsAlong_aux
  · intro X S T f p hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion) (IsPullback.of_hasPullback f p) hf
  · infer_instance

theorem chapter10_closedImmersion_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsClosedImmersion) := by
  intro X S T f p hp
  constructor
  · intro hf
    have h := (IsClosedImmersion.iff_isProper_and_mono f).1 hf
    apply (IsClosedImmersion.iff_isProper_and_mono
      (chapter10BaseChangeMorphism f p)).2
    refine ⟨?_, ?_⟩
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsProper) (IsPullback.of_hasPullback f p) h.1
    · exact (IsPullback.of_hasPullback f p).mono_snd_of_mono h.2
  · intro hf
    have h := (IsClosedImmersion.iff_isProper_and_mono
      (chapter10BaseChangeMorphism f p)).1 hf
    have hproper := (isProper_iff (chapter10BaseChangeMorphism f p)).1 h.1
    apply (IsClosedImmersion.iff_isProper_and_mono f).2
    refine ⟨?_, (chapter10_monomorphism_fpqc_local_on_base f p hp).2 h.2⟩
    refine (isProper_iff f).2 ?_
    refine ⟨chapter10_separated_descends f p hp hproper.1, ?_, ?_⟩
    · have hdesc : MorphismProperty.DescendsAlong
          (@UniversallyClosed : MorphismProperty _) chapter10FpqcMorphismProperty := by
        infer_instance
      exact (chapter10_fpqc_local_of_descendsAlong_aux
        (@UniversallyClosed) (by
          intro X S T f p hf
          exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
            (P := @UniversallyClosed) (IsPullback.of_hasPullback f p) hf)
        hdesc f p hp).2 hproper.2.1
    · exact (chapter10_locallyOfFiniteType_fpqc_local_on_base f p hp).2 hproper.2.2

theorem chapter10_locallyClosedImmersion_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsImmersion) := by
  apply chapter10_fpqc_local_of_descendsAlong_aux
  · intro X S T f p hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsImmersion) (IsPullback.of_hasPullback f p) hf
  · infer_instance

theorem chapter10_proper_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@IsProper) := by
  intro X S T f p hp
  constructor
  · intro hf
    have h := (isProper_iff f).1 hf
    refine (isProper_iff (chapter10BaseChangeMorphism f p)).2 ?_
    refine ⟨?_, ?_, ?_⟩
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @IsSeparated) (IsPullback.of_hasPullback f p) h.1
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @UniversallyClosed) (IsPullback.of_hasPullback f p) h.2.1
    · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @LocallyOfFiniteType) (IsPullback.of_hasPullback f p) h.2.2
  · intro hf
    have h := (isProper_iff (chapter10BaseChangeMorphism f p)).1 hf
    refine (isProper_iff f).2 ?_
    refine ⟨chapter10_separated_descends f p hp h.1, ?_, ?_⟩
    · have hdesc : MorphismProperty.DescendsAlong
          (@UniversallyClosed : MorphismProperty _) chapter10FpqcMorphismProperty := by
        infer_instance
      exact (chapter10_fpqc_local_of_descendsAlong_aux
        (@UniversallyClosed) (by
          intro X S T f p hf
          exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
            (P := @UniversallyClosed) (IsPullback.of_hasPullback f p) hf)
        hdesc f p hp).2 h.2.1
    · exact (chapter10_locallyOfFiniteType_fpqc_local_on_base f p hp).2 h.2.2

theorem chapter10_smooth_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@Smooth) := by
  apply chapter10_fpqc_local_of_descendsAlong_aux
  · intro X S T f p hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Smooth) (IsPullback.of_hasPullback f p) hf
  · infer_instance

theorem chapter10_etale_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@Etale) := by
  apply chapter10_fpqc_local_of_descendsAlong_aux
  · intro X S T f p hf
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale) (IsPullback.of_hasPullback f p) hf
  · infer_instance

theorem chapter10_unramified_fpqc_local_on_base :
    chapter10FpqcLocalOnBase (@chapter10Unramified) := by
  intro X S T f p hp
  constructor
  · intro hf
    obtain ⟨hfin, hformal⟩ :=
      (chapter10_unramified_iff_formallyUnramified f).1 hf
    have hfin' :=
      (chapter10_locallyOfFiniteType_fpqc_local_on_base f p hp).1 hfin
    have hformal' := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @FormallyUnramified) (IsPullback.of_hasPullback f p) hformal
    exact (chapter10_unramified_iff_formallyUnramified
      (chapter10BaseChangeMorphism f p)).2 ⟨hfin', hformal'⟩
  · intro hf
    obtain ⟨hfin, hformal⟩ :=
      (chapter10_unramified_iff_formallyUnramified
        (chapter10BaseChangeMorphism f p)).1 hf
    have hfin' :=
      (chapter10_locallyOfFiniteType_fpqc_local_on_base f p hp).2 hfin
    have hdesc : MorphismProperty.DescendsAlong
        (@FormallyUnramified : MorphismProperty _) chapter10FpqcMorphismProperty := by
      infer_instance
    have hformal' := (chapter10_fpqc_local_of_descendsAlong_aux
      (@FormallyUnramified) (by
        intro X S T f p hf
        exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
          (P := @FormallyUnramified) (IsPullback.of_hasPullback f p) hf)
      hdesc f p hp).2 hformal
    exact (chapter10_unramified_iff_formallyUnramified f).2 ⟨hfin', hformal'⟩

/-- The general bridge from a canonical Mathlib descent instance to the source-facing iff. -/
theorem chapter10_fpqc_local_of_descendsAlong
    (P : MorphismProperty Scheme.{u})
    (hP : chapter10StableUnderBaseChange P)
    (hdesc : P.DescendsAlong chapter10FpqcMorphismProperty) :
    chapter10FpqcLocalOnBase P := by
  exact chapter10_fpqc_local_of_descendsAlong_aux P hP hdesc

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
