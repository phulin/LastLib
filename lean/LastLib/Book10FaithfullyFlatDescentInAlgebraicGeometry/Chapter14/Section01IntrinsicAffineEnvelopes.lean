import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14.Dependencies

/-!
# Book 10, Chapter 14, §14.1: intrinsic affine envelopes

The declarations below separate the canonical envelope map from the
quasi-affineness assertion.  The latter is the theorem that makes the
envelope useful for descent.
-/

noncomputable section

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

/-! ## Finite principal opens on affine schemes -/

structure Chapter14FinitePrincipalOpenCover (Y : Scheme.{u}) where
  affine : IsAffine Y
  carrierOpen : Y.Opens
  sections : Finset Γ(Y, ⊤)
  covers : ∀ x : Y, x ∈ carrierOpen ↔ ∃ g ∈ sections, x ∈ Y.basicOpen g

theorem chapter14_finite_principal_open_cover_of_compact_open
    (Y : Scheme.{u}) [IsAffine Y] (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) :
    ∃ s : Finset Γ(Y, ⊤), ∀ x : Y, x ∈ V ↔ ∃ g ∈ s, x ∈ Y.basicOpen g := by
  obtain ⟨s, hs, hV'⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen (X := Y)).mp
      ⟨hV, V.isOpen⟩
  let t : Finset Γ(Y, ⊤) := hs.toFinset
  refine ⟨t, ?_⟩
  intro x
  constructor
  · intro hx
    change x ∈ (V : Set Y) at hx
    rw [hV'] at hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨g, hg, hxg⟩ := hx
    exact ⟨g, by simpa [t] using hg, hxg⟩
  · rintro ⟨g, hg, hxg⟩
    change x ∈ (V : Set Y)
    rw [hV']
    simp only [Set.mem_iUnion]
    exact ⟨g, by simpa [t] using hg, hxg⟩

theorem chapter14_principal_open_is_affine_of_affine
    (Y : Scheme.{u}) (U : Y.Opens) (hU : IsAffineOpen U)
    (g : Γ(Y, U)) :
    IsAffineOpen (Y.basicOpen g) := by
  exact hU.basicOpen g

theorem chapter14_finite_principal_open_cover_is_affine
    (Y : Scheme.{u}) [IsAffine Y] (V : Y.Opens)
    (hV : IsCompact (V : Set Y)) :
    ∃ C : Chapter14FinitePrincipalOpenCover Y,
      C.carrierOpen = V ∧
        ∀ x : Y, x ∈ V ↔ ∃ g ∈ C.sections, x ∈ Y.basicOpen g := by
  obtain ⟨s, hs⟩ := chapter14_finite_principal_open_cover_of_compact_open Y V hV
  refine ⟨{
      affine := inferInstance
      carrierOpen := V
      sections := s
      covers := hs
    }, rfl, hs⟩

/-! ## The envelope map -/

theorem chapter14_affine_envelope_evaluation_is_open_of_quasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f) :
    IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) := by
  rcases hX with ⟨hX⟩
  let U : S.affineCover.I₀ → S.Opens := fun i => (S.affineCover.f i).opensRange
  have hU : TopologicalSpace.IsOpenCover U := by
    simpa [U] using S.affineCover.isOpenCover_opensRange
  let 𝒰 : S.OpenCover := S.openCoverOfIsOpenCover U hU
  let 𝒱 : X.OpenCover := 𝒰.pullback₁ f
  have hAbs (i : 𝒰.I₀) :
      IsOpenImmersion
        (chapter14AbsoluteAffineEnvelopeEvaluation (pullback f (U i).ι)) := by
    have hUi : IsAffineOpen (U i) := by
      dsimp [U]
      exact @isAffineOpen_opensRange _ _ (by
        change IsAffine (Spec _)
        infer_instance) (S.affineCover.f i) (S.affineCover.map_prop i)
    let a := chapter14EvaluationBaseChange f hX.ambientMap hX.embedding
      (U i).ι hX.overBase
    have ha : IsOpenImmersion a := by
      let a' := pullback.map f (U i).ι hX.ambientMap (U i).ι
        hX.embedding (𝟙 _) (𝟙 _) (by simpa using hX.overBase.symm) (by simp)
      have ha' : IsOpenImmersion a' := by
        dsimp [a']
        exact @Scheme.pullback_map_isOpenImmersion _ _ _ _ _ _ f (U i).ι
          hX.ambientMap (U i).ι hX.embedding (𝟙 _) (𝟙 _) _ _
          hX.embeddingOpen inferInstance inferInstance
      have haa : a = a' := by
        dsimp [a, a']
        apply pullback.hom_ext <;>
          simp [pullback.map, chapter14EvaluationBaseChange]
      rw [haa]
      exact ha'
    have hQ : Scheme.IsQuasiAffine (pullback f (U i).ι) := by
      let : IsAffine (U i).toScheme := hUi
      let : IsAffineHom hX.ambientMap := hX.ambientAffine
      let : IsOpenImmersion hX.embedding := hX.embeddingOpen
      let : IsAffine (pullback hX.ambientMap (U i).ι) := inferInstance
      let : IsOpenImmersion a := ha
      exact Scheme.IsQuasiAffine.of_isImmersion a
    exact (chapter14_absolute_quasiAffine_iff_affine_envelope_open
      (pullback f (U i).ι)).mp hQ
  have hlocal (i : 𝒰.I₀) :
      IsOpenImmersion
        (𝒱.f i ≫ chapter14AffineEnvelopeEvaluation f) := by
    have hUi : IsAffineOpen (U i) := by
      dsimp [U]
      exact @isAffineOpen_opensRange _ _ (by
        change IsAffine (Spec _)
        infer_instance) (S.affineCover.f i) (S.affineCover.map_prop i)
    obtain ⟨c⟩ := (chapter14AffineEnvelope f).localChart (U i) hUi
    have hbase :
        IsOpenImmersion (chapter14EvaluationBaseChange f
          (chapter14AffineEnvelopeMap f) (chapter14AffineEnvelopeEvaluation f)
          (U i).ι (chapter14_affine_envelope_evaluation_over_base f)) := by
      rw [← MorphismProperty.cancel_right_of_respectsIso
        (P := @IsOpenImmersion) _ c.comparison.hom]
      rw [c.comparison_evaluation]
      exact hAbs i
    have hcomp : IsOpenImmersion (chapter14EvaluationBaseChange f
        (chapter14AffineEnvelopeMap f) (chapter14AffineEnvelopeEvaluation f)
        (U i).ι (chapter14_affine_envelope_evaluation_over_base f) ≫
        pullback.fst (chapter14AffineEnvelopeMap f) (U i).ι) := by
      exact @IsOpenImmersion.comp _ _ _
        (chapter14EvaluationBaseChange f
          (chapter14AffineEnvelopeMap f) (chapter14AffineEnvelopeEvaluation f)
          (U i).ι (chapter14_affine_envelope_evaluation_over_base f))
        (pullback.fst (chapter14AffineEnvelopeMap f) (U i).ι)
        hbase inferInstance
    dsimp only [𝒱, 𝒰, Scheme.openCoverOfIsOpenCover,
      Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f]
    change IsOpenImmersion (pullback.fst f (U i).ι ≫
      chapter14AffineEnvelopeEvaluation f)
    have heq : chapter14EvaluationBaseChange f
        (chapter14AffineEnvelopeMap f) (chapter14AffineEnvelopeEvaluation f)
        (U i).ι (chapter14_affine_envelope_evaluation_over_base f) ≫
        pullback.fst (chapter14AffineEnvelopeMap f) (U i).ι =
        pullback.fst f (U i).ι ≫ chapter14AffineEnvelopeEvaluation f := by
      rw [chapter14EvaluationBaseChange, pullback.lift_fst]
    rw [heq] at hcomp
    exact hcomp
  have hinj : Function.Injective (chapter14AffineEnvelopeEvaluation f) := by
    intro x y hxy
    have hfy : f x = f y := by
      have heq : chapter14AffineEnvelopeEvaluation f ≫
          chapter14AffineEnvelopeMap f = f :=
        chapter14_affine_envelope_evaluation_over_base f
      calc
        f x = (chapter14AffineEnvelopeEvaluation f ≫
            chapter14AffineEnvelopeMap f) x := by
          exact congrArg (fun g : X ⟶ S ↦ g x) heq.symm
        _ = (chapter14AffineEnvelopeEvaluation f ≫
            chapter14AffineEnvelopeMap f) y := by
          change chapter14AffineEnvelopeMap f (chapter14AffineEnvelopeEvaluation f x) =
            chapter14AffineEnvelopeMap f (chapter14AffineEnvelopeEvaluation f y)
          rw [hxy]
        _ = f y := by
          exact congrArg (fun g : X ⟶ S ↦ g y) heq
    let i : 𝒰.I₀ := 𝒰.idx (f x)
    obtain ⟨z, hz⟩ := 𝒰.covers (f x)
    have hzx : f x = 𝒰.f i z := hz.symm
    have hzy : f y = 𝒰.f i z := hfy.symm.trans hzx
    obtain ⟨x' : 𝒱.X i, hx₁⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance x z hzx
    obtain ⟨y' : 𝒱.X i, hy₁⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance y z hzy
    change 𝒱.f i x' = x at hx₁
    change 𝒱.f i y' = y at hy₁
    have hxy' : x' = y' := by
      apply (Scheme.Hom.isOpenEmbedding (𝒱.f i ≫
        chapter14AffineEnvelopeEvaluation f) (H := hlocal i)).injective
      change chapter14AffineEnvelopeEvaluation f (𝒱.f i x') =
        chapter14AffineEnvelopeEvaluation f (𝒱.f i y')
      rw [hx₁, hy₁, hxy]
    calc
      x = 𝒱.f i x' := hx₁.symm
      _ = 𝒱.f i y' := by rw [hxy']
      _ = y := hy₁
  exact IsOpenImmersion.of_openCover_source (chapter14AffineEnvelopeEvaluation f)
    𝒱 hinj hlocal

theorem chapter14_affine_envelope_evaluation_is_quasiCompact_of_quasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f) :
    QuasiCompact (chapter14AffineEnvelopeEvaluation f) := by
  let e := chapter14AffineEnvelopeEvaluation f
  let p := chapter14AffineEnvelopeMap f
  let : IsAffineHom p := chapter14_affine_envelope_is_affine f
  let : QuasiCompact (e ≫ p) := by
    rw [show e ≫ p = f from chapter14_affine_envelope_evaluation_over_base f]
    infer_instance
  exact (fun (_ : IsOpenImmersion e) => QuasiCompact.of_comp e p)
    (chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f hX)

theorem chapter14_quasiAffine_of_affine_envelope_evaluation_is_open
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hOpen : IsOpenImmersion (chapter14AffineEnvelopeEvaluation f)) :
    chapter14QuasiAffine f := by
  exact chapter14_quasiAffine_mk f (chapter14AffineEnvelopeMap f)
    (chapter14_affine_envelope_is_affine f)
    (chapter14AffineEnvelopeEvaluation f) hOpen
    (chapter14_affine_envelope_evaluation_over_base f)

theorem chapter14_quasiAffine_iff_affine_envelope_evaluation_is_open
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14QuasiAffine f ↔
      IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) := by
  constructor
  · exact chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f
  · exact chapter14_quasiAffine_of_affine_envelope_evaluation_is_open f

theorem chapter14_affine_envelope_evaluation_is_quasiCompact_open_of_quasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine f) :
    IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) ∧
      QuasiCompact (chapter14AffineEnvelopeEvaluation f) := by
  exact ⟨chapter14_affine_envelope_evaluation_is_open_of_quasiAffine f hX,
    chapter14_affine_envelope_evaluation_is_quasiCompact_of_quasiAffine f hX⟩

theorem chapter14_quasiAffine_iff_quasiCompact_open_affine_envelope_evaluation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14QuasiAffine f ↔
      IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) ∧
        QuasiCompact (chapter14AffineEnvelopeEvaluation f) := by
  constructor
  · exact chapter14_affine_envelope_evaluation_is_quasiCompact_open_of_quasiAffine f
  · intro h
    exact chapter14_quasiAffine_of_affine_envelope_evaluation_is_open f h.1

/-! ## Restriction, membership, and normalization bridges -/

theorem chapter14_affine_envelope_preimage_basicOpen
    {X Y : Scheme.{u}} (j : X ⟶ Y) (g : Γ(Y, ⊤)) :
    j ⁻¹ᵁ Y.basicOpen g = X.basicOpen (j.appTop g) := by
  exact Scheme.preimage_basicOpen_top j g

theorem chapter14_affine_envelope_preimage_basicOpen_mem_iff
    {X Y : Scheme.{u}} (j : X ⟶ Y) (g : Γ(Y, ⊤)) (x : X) :
    x ∈ j ⁻¹ᵁ Y.basicOpen g ↔ x ∈ X.basicOpen (j.appTop g) := by
  rw [chapter14_affine_envelope_preimage_basicOpen]

theorem chapter14_affine_envelope_basicOpen_restriction
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) :
    X.basicOpen g ≤ U ∧ IsAffineOpen (X.basicOpen g) := by
  exact ⟨Scheme.basicOpen_le _ _, hU.basicOpen g⟩

theorem chapter14_affine_envelope_evaluation_over_base_appTop
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    (chapter14AffineEnvelopeMap f).appTop ≫
        (chapter14AffineEnvelopeEvaluation f).appTop = f.appTop := by
  rw [← Scheme.Hom.comp_appTop, chapter14_affine_envelope_evaluation_over_base]

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
