import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14.Section01IntrinsicAffineEnvelopes

/-!
# Book 10, Chapter 14, §14.2: descending quasi-affine schemes

The base-change comparison is recorded at both the sheaf-of-functions level
and the affine-envelope level.  The fpqc descent statement then applies the
Mathlib descent interface for open immersions.
-/

noncomputable section

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

/-! ## Base change of the canonical map -/

theorem chapter14_relative_global_functions_base_change_exists
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] :
    Nonempty (Chapter14RelativeGlobalFunctionsBaseChangeData f g) := by
  sorry

noncomputable def chapter14_relative_global_functions_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] :
    (Scheme.Modules.pullback g).obj (chapter14RelativeGlobalFunctions f) ≅
      chapter14RelativeGlobalFunctions (chapter14BaseChangeToBase f g) :=
  (Classical.choice
    (chapter14_relative_global_functions_base_change_exists f g)).comparison

noncomputable def chapter14RelativeGlobalFunctionsBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] :
    (Scheme.Modules.pullback g).obj (chapter14RelativeGlobalFunctions f) ≅
      chapter14RelativeGlobalFunctions (chapter14BaseChangeToBase f g) :=
  chapter14_relative_global_functions_base_change f g

theorem chapter14_relative_global_functions_base_change_is_quasicoherent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g] :
    (chapter14RelativeGlobalFunctions (chapter14BaseChangeToBase f g)).IsQuasicoherent := by
  have hqcStable : MorphismProperty.IsStableUnderBaseChange
      (@QuasiCompact : MorphismProperty Scheme.{u}) := inferInstance
  have hqcAlong : MorphismProperty.IsStableUnderBaseChangeAlong
      (@QuasiCompact : MorphismProperty Scheme.{u}) g :=
    { of_isPullback := fun pb h => hqcStable.of_isPullback pb h }
  have hqsStable : MorphismProperty.IsStableUnderBaseChange
      (@QuasiSeparated : MorphismProperty Scheme.{u}) := inferInstance
  have hqsAlong : MorphismProperty.IsStableUnderBaseChangeAlong
      (@QuasiSeparated : MorphismProperty Scheme.{u}) g :=
    { of_isPullback := fun pb h => hqsStable.of_isPullback pb h }
  have hqc : QuasiCompact (pullback.snd f g) :=
    hqcAlong.of_isPullback (IsPullback.of_hasPullback f g) inferInstance
  have hqs : QuasiSeparated (pullback.snd f g) :=
    hqsAlong.of_isPullback (IsPullback.of_hasPullback f g) inferInstance
  exact @chapter14_relative_global_functions_is_quasicoherent _ _
    (pullback.snd f g) hqc hqs

@[simp]
theorem chapter14AffineEnvelopeEvaluationBaseChange_fst
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14AffineEnvelopeEvaluationBaseChange f g ≫
        pullback.fst (chapter14AffineEnvelopeMap f) g =
      chapter14BaseChangeToSource f g ≫ chapter14AffineEnvelopeEvaluation f := by
  exact pullback.lift_fst _ _ _

@[simp]
theorem chapter14AffineEnvelopeEvaluationBaseChange_snd
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14AffineEnvelopeEvaluationBaseChange f g ≫
        pullback.snd (chapter14AffineEnvelopeMap f) g =
      chapter14BaseChangeToBase f g := by
  exact pullback.lift_snd _ _ _

/-! ## The affine-envelope base-change comparison -/

theorem chapter14_affine_envelope_base_change_exists
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    Nonempty (Chapter14AffineEnvelopeBaseChangeData f g) := by
  sorry

noncomputable def chapter14AffineEnvelopeBaseChange
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    Chapter14AffineEnvelopeBaseChangeData f g :=
  Classical.choice (chapter14_affine_envelope_base_change_exists f g)

def chapter14AffineEnvelopeBaseChangeIso
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    pullback (chapter14AffineEnvelopeMap f) g ≅
      (chapter14AffineEnvelope (chapter14BaseChangeToBase f g)).envelope :=
  (chapter14AffineEnvelopeBaseChange f g).comparison

theorem chapter14_affine_envelope_base_change_over_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    (chapter14AffineEnvelopeBaseChangeIso f g).hom ≫
        chapter14AffineEnvelopeMap (chapter14BaseChangeToBase f g) =
      pullback.snd (chapter14AffineEnvelopeMap f) g := by
  exact (chapter14AffineEnvelopeBaseChange f g).comparison_over_base

theorem chapter14_affine_envelope_base_change_evaluation
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [Flat g]
    [QuasiCompact (chapter14BaseChangeToBase f g)]
    [QuasiSeparated (chapter14BaseChangeToBase f g)] :
    chapter14AffineEnvelopeEvaluationBaseChange f g ≫
        (chapter14AffineEnvelopeBaseChangeIso f g).hom =
      chapter14AffineEnvelopeEvaluation (chapter14BaseChangeToBase f g) := by
  exact (chapter14AffineEnvelopeBaseChange f g).comparison_evaluation

/-! ## Stability and fpqc descent -/

theorem chapter14_quasiAffine_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hX : chapter14QuasiAffine f) :
    chapter14QuasiAffine (chapter14BaseChangeToBase f g) := by
  rcases hX with ⟨hX⟩
  let e := pullback.map f g hX.ambientMap g hX.embedding (𝟙 _) (𝟙 _)
    (by simpa using hX.overBase.symm) (by simp)
  have he : IsOpenImmersion e := by
    dsimp [e]
    exact @Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ f g
      hX.ambientMap g hX.embedding (𝟙 _) (𝟙 _) _ _
      hX.embeddingOpen inferInstance inferInstance
  have hAffine : IsAffineHom (pullback.snd hX.ambientMap g) := by
    let stable : MorphismProperty.IsStableUnderBaseChange @IsAffineHom :=
      AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
    let along : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) g :=
      { of_isPullback := fun pb h => stable.of_isPullback pb h }
    exact along.of_isPullback (IsPullback.of_hasPullback _ _) hX.ambientAffine
  refine chapter14_quasiAffine_mk (chapter14BaseChangeToBase f g)
    (pullback.snd hX.ambientMap g)
    hAffine e he ?_
  dsimp [e]
  exact pullback.lift_snd _ _ _

theorem chapter14_quasiAffine_of_fpqc_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g)
    (hXT : chapter14QuasiAffine (chapter14BaseChangeToBase f g)) :
    chapter14QuasiAffine f := by
  let e := chapter14AffineEnvelopeEvaluation f
  let p := chapter14AffineEnvelopeMap f
  let he : e ≫ p = f := chapter14_affine_envelope_evaluation_over_base f
  have hqcBase : QuasiCompact (pullback.snd f g) := by
    have hstable : MorphismProperty.IsStableUnderBaseChange
        (@QuasiCompact : MorphismProperty Scheme.{u}) := inferInstance
    have halong : MorphismProperty.IsStableUnderBaseChangeAlong
        (@QuasiCompact : MorphismProperty Scheme.{u}) g :=
      { of_isPullback := fun pb h => hstable.of_isPullback pb h }
    exact halong.of_isPullback (IsPullback.of_hasPullback f g) inferInstance
  have hqsBase : QuasiSeparated (pullback.snd f g) := by
    have hstable : MorphismProperty.IsStableUnderBaseChange
        (@QuasiSeparated : MorphismProperty Scheme.{u}) := inferInstance
    have halong : MorphismProperty.IsStableUnderBaseChangeAlong
        (@QuasiSeparated : MorphismProperty Scheme.{u}) g :=
      { of_isPullback := fun pb h => hstable.of_isPullback pb h }
    exact halong.of_isPullback (IsPullback.of_hasPullback f g) inferInstance
  let : Flat g := hg.flat
  let : QuasiCompact (chapter14BaseChangeToBase f g) := hqcBase
  let : QuasiSeparated (chapter14BaseChangeToBase f g) := hqsBase
  let c := @chapter14AffineEnvelopeBaseChange _ _ _ f g inferInstance
    inferInstance hg.flat hqcBase hqsBase
  let a := chapter14AffineEnvelopeEvaluationBaseChange f g
  have ha_fst : a ≫ pullback.fst p g =
      chapter14BaseChangeToSource f g ≫ e := by
    exact chapter14AffineEnvelopeEvaluationBaseChange_fst f g
  have ha_snd : a ≫ pullback.snd p g =
      chapter14BaseChangeToBase f g := by
    exact chapter14AffineEnvelopeEvaluationBaseChange_snd f g
  have hOpenT :
      IsOpenImmersion (chapter14AffineEnvelopeEvaluation
        (chapter14BaseChangeToBase f g)) :=
    @chapter14_affine_envelope_evaluation_is_open_of_quasiAffine _ _
      (chapter14BaseChangeToBase f g) hqcBase hqsBase hXT
  have hOpenA : IsOpenImmersion a := by
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (P := @IsOpenImmersion) a c.comparison.hom]
    rw [c.comparison_evaluation]
    exact hOpenT
  have hPullback : IsPullback a
      (chapter14BaseChangeToSource f g) (pullback.fst p g) e := by
    apply IsPullback.mk'
    · exact chapter14AffineEnvelopeEvaluationBaseChange_fst f g
    · intro Z φ ψ hφ hψ
      apply pullback.hom_ext
      · exact hψ
      · have hφ' := congrArg (fun k => k ≫ pullback.snd p g) hφ
        rw [Category.assoc, Category.assoc] at hφ'
        rw [ha_snd] at hφ'
        simpa only [chapter14BaseChangeToBase, chapter14BaseChange] using hφ'
    · intro Z α β hαβ
      have hcond : β ≫ f = (α ≫ pullback.snd p g) ≫ g := by
        calc
          β ≫ f = β ≫ (e ≫ p) := by rw [he]
          _ = (β ≫ e) ≫ p := by simp only [Category.assoc]
          _ = (α ≫ pullback.fst p g) ≫ p := by rw [← hαβ]
          _ = α ≫ (pullback.fst p g ≫ p) := by simp only [Category.assoc]
          _ = α ≫ (pullback.snd p g ≫ g) := by rw [pullback.condition]
          _ = (α ≫ pullback.snd p g) ≫ g := by simp only [Category.assoc]
      let l : Z ⟶ chapter14BaseChange f g :=
        pullback.lift β (α ≫ pullback.snd p g) hcond
      have hl_fst : l ≫ chapter14BaseChangeToSource f g = β := by
        dsimp [l, chapter14BaseChangeToSource, chapter14BaseChange]
        exact pullback.lift_fst _ _ _
      have hl_snd : l ≫ chapter14BaseChangeToBase f g =
          α ≫ pullback.snd p g := by
        dsimp [l, chapter14BaseChangeToBase, chapter14BaseChange]
        exact pullback.lift_snd _ _ _
      refine ⟨l, ?_, ?_⟩
      · apply pullback.hom_ext
        · calc
            (l ≫ a) ≫ pullback.fst p g =
                l ≫ (a ≫ pullback.fst p g) := Category.assoc _ _ _
            _ = l ≫ (chapter14BaseChangeToSource f g ≫ e) := by rw [ha_fst]
            _ = (l ≫ chapter14BaseChangeToSource f g) ≫ e :=
              (Category.assoc _ _ _).symm
            _ = β ≫ e := by rw [hl_fst]
            _ = α ≫ pullback.fst p g := hαβ.symm
        · calc
            (l ≫ a) ≫ pullback.snd p g =
                l ≫ (a ≫ pullback.snd p g) := Category.assoc _ _ _
            _ = l ≫ chapter14BaseChangeToBase f g := by rw [ha_snd]
            _ = α ≫ pullback.snd p g := hl_snd
      · exact pullback.lift_fst _ _ _
  have hsurjE : Surjective (pullback.fst p g) := by
    have hstable : MorphismProperty.IsStableUnderBaseChange
        (@Surjective : MorphismProperty Scheme.{u}) := inferInstance
    have halong : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Surjective : MorphismProperty Scheme.{u}) p :=
      { of_isPullback := fun pb h => hstable.of_isPullback pb h }
    exact halong.of_isPullback (IsPullback.of_hasPullback p g).flip hg.surjective
  have hflatE : Flat (pullback.fst p g) := by
    have hstable : MorphismProperty.IsStableUnderBaseChange
        (@Flat : MorphismProperty Scheme.{u}) := inferInstance
    have halong : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Flat : MorphismProperty Scheme.{u}) p :=
      { of_isPullback := fun pb h => hstable.of_isPullback pb h }
    exact halong.of_isPullback (IsPullback.of_hasPullback p g).flip hg.flat
  have hqcE : QuasiCompact (pullback.fst p g) := by
    have hstable : MorphismProperty.IsStableUnderBaseChange
        (@QuasiCompact : MorphismProperty Scheme.{u}) := inferInstance
    have halong : MorphismProperty.IsStableUnderBaseChangeAlong
        (@QuasiCompact : MorphismProperty Scheme.{u}) p :=
      { of_isPullback := fun pb h => hstable.of_isPullback pb h }
    exact halong.of_isPullback (IsPullback.of_hasPullback p g).flip hg.quasiCompact
  have hDesc : MorphismProperty.DescendsAlong
      (@IsOpenImmersion : MorphismProperty Scheme.{u})
      ((@Surjective : MorphismProperty (Scheme.{u})) ⊓
        (@Flat : MorphismProperty (Scheme.{u})) ⊓
        (@QuasiCompact : MorphismProperty (Scheme.{u}))) := inferInstance
  have hg' : (Surjective (pullback.fst p g) ∧
      Flat (pullback.fst p g)) ∧ QuasiCompact (pullback.fst p g) :=
    ⟨⟨hsurjE, hflatE⟩, hqcE⟩
  have hOpen : IsOpenImmersion e :=
    hDesc.of_isPullback hPullback hg' hOpenA
  exact chapter14_quasiAffine_of_affine_envelope_evaluation_is_open f hOpen

theorem chapter14_quasiAffine_iff_fpqc_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g) :
    chapter14QuasiAffine f ↔
      chapter14QuasiAffine (chapter14BaseChangeToBase f g) := by
  constructor
  · exact chapter14_quasiAffine_base_change f g
  · exact chapter14_quasiAffine_of_fpqc_base_change f g hg

theorem chapter14_quasi_affine_descent_theorem
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g)
    (hXT : chapter14QuasiAffine (chapter14BaseChangeToBase f g)) :
    chapter14QuasiAffine f := by
  exact chapter14_quasiAffine_of_fpqc_base_change f g hg hXT

theorem chapter14_quasi_affineness_is_fpqc_local
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g) :
    chapter14QuasiAffine f ↔
      chapter14QuasiAffine (chapter14BaseChangeToBase f g) := by
  exact chapter14_quasiAffine_iff_fpqc_base_change f g hg

/-! ## The locally quasi-affine boundary variant -/

def chapter14LocallyQuasiAffine {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsCompact (U : Set X) ∧
    chapter14QuasiAffine (U.ι ≫ f)

theorem chapter14_quasiAffine_implies_locallyQuasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hX : chapter14QuasiAffine f) :
    chapter14LocallyQuasiAffine f := by
  rcases hX with ⟨hX⟩
  intro x
  obtain ⟨i, hi⟩ := hX.ambient.affineCover.exists_eq (hX.embedding x)
  let A : hX.ambient.Opens := (hX.ambient.affineCover.f i).opensRange
  have hA : IsAffineOpen A := by
    exact isAffineOpen_opensRange (hX.ambient.affineCover.f i)
  have hxA : hX.embedding x ∈ A := hi
  let V : hX.ambient.Opens :=
    ⟨Set.range hX.embedding, hX.embeddingOpen.base_open.isOpen_range⟩
  obtain ⟨r, hrRange, hxr⟩ :=
    hA.exists_basicOpen_le (V := V)
      ⟨hX.embedding x, ⟨x, rfl⟩⟩ hxA
  let W : hX.ambient.Opens := hX.ambient.basicOpen r
  have hW : IsAffineOpen W := by
    exact hA.basicOpen r
  let U : X.Opens := hX.embedding ⁻¹ᵁ W
  have hxU : x ∈ U := by
    change hX.embedding x ∈ W
    exact hxr
  have hemb := hX.embeddingOpen.base_open
  have hUcompact : IsCompact (U : Set X) := by
    dsimp [U]
    exact hemb.isInducing.isCompact_preimage' hW.isCompact (by
      intro y hy
      change ∃ z : X, hX.embedding z = y
      exact hrRange hy)
  have hcomp : IsOpenImmersion (U.ι ≫ hX.embedding) := by
    exact @IsOpenImmersion.comp _ _ _ U.ι hX.embedding inferInstance
      hX.embeddingOpen
  refine ⟨U, hxU, hUcompact, ?_⟩
  exact chapter14_quasiAffine_mk (U.ι ≫ f) hX.ambientMap
    hX.ambientAffine (U.ι ≫ hX.embedding) hcomp (by
      rw [Category.assoc, hX.overBase])

private theorem chapter14_quasiAffine_exists_compact_open_subset
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hX : chapter14QuasiAffine f) (x : X) (O : X.Opens) (hxO : x ∈ O) :
    ∃ V : X.Opens, x ∈ V ∧ V ≤ O ∧ IsCompact (V : Set X) ∧
      chapter14QuasiAffine (V.ι ≫ f) := by
  rcases hX with ⟨hX⟩
  obtain ⟨i, hi⟩ := hX.ambient.affineCover.exists_eq (hX.embedding x)
  let A : hX.ambient.Opens := (hX.ambient.affineCover.f i).opensRange
  have hA : IsAffineOpen A := by
    exact isAffineOpen_opensRange (hX.ambient.affineCover.f i)
  have hxA : hX.embedding x ∈ A := hi
  let imageO : hX.ambient.Opens :=
    ⟨hX.embedding '' (O : Set X),
      hX.embeddingOpen.base_open.isOpenMap _ O.isOpen⟩
  let range : hX.ambient.Opens :=
    ⟨Set.range hX.embedding, hX.embeddingOpen.base_open.isOpen_range⟩
  let target : hX.ambient.Opens := range ⊓ imageO
  have hxTarget : hX.embedding x ∈ target := by
    exact ⟨⟨x, rfl⟩, ⟨x, hxO, rfl⟩⟩
  obtain ⟨r, hrTarget, hxr⟩ :=
    hA.exists_basicOpen_le (V := target)
      ⟨hX.embedding x, hxTarget⟩ hxA
  let W : hX.ambient.Opens := hX.ambient.basicOpen r
  have hW : IsAffineOpen W := by
    exact hA.basicOpen r
  let V : X.Opens := hX.embedding ⁻¹ᵁ W
  have hxV : x ∈ V := by
    change hX.embedding x ∈ W
    exact hxr
  have hVO : V ≤ O := by
    intro y hy
    change hX.embedding y ∈ W at hy
    have hyImage : hX.embedding y ∈ imageO := (hrTarget hy).2
    obtain ⟨z, hzO, hzeq⟩ := hyImage
    have hzy : z = y := hX.embeddingOpen.base_open.injective hzeq
    simpa [hzy] using hzO
  have hemb := hX.embeddingOpen.base_open
  have hVcompact : IsCompact (V : Set X) := by
    dsimp [V]
    exact hemb.isInducing.isCompact_preimage' hW.isCompact (by
      intro y hy
      exact (hrTarget hy).1)
  have hcomp : IsOpenImmersion (V.ι ≫ hX.embedding) := by
    exact @IsOpenImmersion.comp _ _ _ V.ι hX.embedding inferInstance
      hX.embeddingOpen
  refine ⟨V, hxV, hVO, hVcompact, ?_⟩
  exact chapter14_quasiAffine_mk (V.ι ≫ f) hX.ambientMap
    hX.ambientAffine (V.ι ≫ hX.embedding) hcomp (by
      rw [Category.assoc, hX.overBase])

theorem chapter14_locallyQuasiAffine_restrict
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hX : chapter14LocallyQuasiAffine f) (U : S.Opens) :
    chapter14LocallyQuasiAffine (chapter14RestrictionToOpenMap f U) := by
  intro x
  change (pullback f U.ι :) at x
  let k := pullback.fst f U.ι
  let pU : pullback f U.ι ⟶ U.toScheme := pullback.snd f U.ι
  have hx0U : k x ∈ f ⁻¹ᵁ U := by
    change f (k x) ∈ U
    have hc := congrArg (fun h : pullback f U.ι ⟶ S => h x)
      (pullback.condition :
        pullback.fst f U.ι ≫ f = pullback.snd f U.ι ≫ U.ι)
    have hc' : f (k x) = (pullback.snd f U.ι x).1 := by
      calc
        f (k x) = (pullback.fst f U.ι ≫ f) x := by
          change f ((pullback.fst f U.ι) x) = _
          exact (Scheme.Hom.comp_apply (pullback.fst f U.ι) f x).symm
        _ = (pullback.snd f U.ι ≫ U.ι) x := hc
        _ = (pullback.snd f U.ι x).1 := by
          calc
            (pullback.snd f U.ι ≫ U.ι) x = U.ι (pullback.snd f U.ι x) :=
              Scheme.Hom.comp_apply (pullback.snd f U.ι) U.ι x
            _ = (pullback.snd f U.ι x).1 := by rfl
    rw [hc']
    exact (pullback.snd f U.ι x).property
  rcases hX (k x) with ⟨U₀, hxU₀, hU₀compact, hU₀qa⟩
  let z : U₀.toScheme := ⟨k x, hxU₀⟩
  let O₀ : U₀.toScheme.Opens := U₀.ι ⁻¹ᵁ (f ⁻¹ᵁ U)
  have hzO₀ : z ∈ O₀ := by
    change f (k x) ∈ U
    exact hx0U
  obtain ⟨V₀, hzV₀, hV₀sub, hV₀compact, hV₀qa⟩ :=
    chapter14_quasiAffine_exists_compact_open_subset (U₀.ι ≫ f) hU₀qa z O₀ hzO₀
  let jV : V₀.toScheme ⟶ X := V₀.ι ≫ U₀.ι
  have hjV : IsOpenImmersion jV := by
    dsimp [jV]
    infer_instance
  let : IsOpenImmersion jV := hjV
  let V : X.Opens := jV.opensRange
  have hxV : k x ∈ V := by
    apply (Scheme.Hom.mem_opensRange).2
    refine ⟨⟨z, hzV₀⟩, ?_⟩
    rfl
  have hVsub : V ≤ f ⁻¹ᵁ U := by
    intro y hy
    obtain ⟨w, hwy⟩ := (Scheme.Hom.mem_opensRange).1 hy
    have hwO₀ := hV₀sub w.property
    have hwO₀' : f (U₀.ι (V₀.ι w)) ∈ U := by
      change f (U₀.ι (V₀.ι w)) ∈ U at hwO₀
      exact hwO₀
    change f y ∈ U
    rw [← hwy]
    simpa [jV] using hwO₀'
  let : CompactSpace V₀.toScheme := isCompact_iff_compactSpace.mp hV₀compact
  have hVcompact : IsCompact (V : Set X) := by
    convert isCompact_range jV.continuous
    simp [V]
  have hVqa : chapter14QuasiAffine (V.ι ≫ f) := by
    rcases hV₀qa with ⟨hQ⟩
    let i := jV.isoOpensRange
    refine chapter14_quasiAffine_mk (V.ι ≫ f)
      hQ.ambientMap hQ.ambientAffine (i.inv ≫ hQ.embedding) ?_ ?_
    · exact @IsOpenImmersion.comp _ _ _ i.inv hQ.embedding inferInstance
        hQ.embeddingOpen
    · rw [Category.assoc, hQ.overBase]
      simpa only [i, V, jV, Category.assoc] using
        congrArg (fun h => h ≫ f) (Scheme.Hom.isoOpensRange_inv_comp jV)
  let q : pullback (V.ι ≫ f) U.ι ⟶ pullback f U.ι :=
    pullback.map (V.ι ≫ f) U.ι f U.ι V.ι (𝟙 _) (𝟙 _)
      (by simp) (by simp)
  have hq : IsOpenImmersion q := by
    dsimp [q]
    exact @Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _
      (V.ι ≫ f) U.ι f U.ι V.ι (𝟙 _) (𝟙 _) _ _
      inferInstance inferInstance inferInstance
  let : IsOpenImmersion q := hq
  have hQqa : chapter14QuasiAffine
      (pullback.snd (V.ι ≫ f) U.ι) := by
    exact chapter14_quasiAffine_base_change (V.ι ≫ f) U.ι hVqa
  have hxq : x ∈ Set.range q := by
    change x ∈ Set.range (pullback.map (V.ι ≫ f) U.ι f U.ι V.ι
      (𝟙 _) (𝟙 _) _ _)
    rw [Scheme.Pullback.range_map]
    constructor
    · exact ⟨⟨k x, hxV⟩, rfl⟩
    · exact ⟨pullback.snd f U.ι x, by simp⟩
  let W : (pullback f U.ι).Opens := q.opensRange
  have hxW : x ∈ W := by
    exact (Scheme.Hom.mem_opensRange).2 hxq
  have hW_eq : W = k ⁻¹ᵁ V := by
    ext y
    change y ∈ Set.range q ↔ k y ∈ V
    rw [Scheme.Pullback.range_map]
    constructor
    · rintro ⟨⟨z, hz⟩, _⟩
      rw [← hz]
      exact z.property
    · intro hy
      refine ⟨⟨⟨k y, hy⟩, rfl⟩, ?_⟩
      exact ⟨pullback.snd f U.ι y, rfl⟩
  have hkOpen : IsOpenImmersion k := by infer_instance
  have hk := Scheme.Hom.isOpenEmbedding k (H := hkOpen)
  have hVrange : (V : Set X) ⊆ Set.range k := by
    intro y hy
    rw [Scheme.Pullback.range_fst]
    change f y ∈ Set.range U.ι
    exact ⟨⟨f y, hVsub hy⟩, rfl⟩
  have hWcompact : IsCompact (W : Set (pullback f U.ι :)) := by
    rw [hW_eq]
    change IsCompact (k ⁻¹' (V : Set X))
    exact hk.isInducing.isCompact_preimage' hVcompact hVrange
  have hqbase : q ≫ pU = pullback.snd (V.ι ≫ f) U.ι := by
    dsimp [q, pU, chapter14RestrictionToOpenMap]
    simp only [pullback.lift_snd, Category.comp_id]
  have hWqa : chapter14QuasiAffine (W.ι ≫ pU) := by
    rcases hQqa with ⟨hQ⟩
    let i := q.isoOpensRange
    refine chapter14_quasiAffine_mk (W.ι ≫ pU)
      hQ.ambientMap hQ.ambientAffine (i.inv ≫ hQ.embedding) ?_ ?_
    · exact @IsOpenImmersion.comp _ _ _ i.inv hQ.embedding inferInstance
        hQ.embeddingOpen
    · rw [Category.assoc, hQ.overBase, ← hqbase, ← Category.assoc,
        Scheme.Hom.isoOpensRange_inv_comp]
  exact ⟨W, hxW, hWcompact, by
    simpa [chapter14RestrictionToOpen, chapter14RestrictionToOpenMap, pU] using hWqa⟩

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
