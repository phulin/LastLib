import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14.Section02DescendingQuasiAffineSchemes

/-!
# Book 10, Chapter 14, §14.4: the precise reusable criterion

The criterion is stated using only affine opens of the base and finite sets
of relative global functions.  The three formulations from the source are
then exposed by separate equivalences and a combined theorem.
-/

noncomputable section

universe u

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

/-! ## Relative principal-open covers -/

def chapter14RelativePrincipalOpenCover
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) : Prop :=
  ∃ s : Finset (chapter14RelativeFunctionsOnOpen f U),
    (∀ g ∈ s,
      IsAffineOpen ((chapter14RestrictionToOpen f U).basicOpen g)) ∧
      ∀ x : chapter14RestrictionToOpen f U, ∃ g ∈ s,
        x ∈ (chapter14RestrictionToOpen f U).basicOpen g

theorem chapter14_relativePrincipalOpenCover_mk
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (s : Finset (chapter14RelativeFunctionsOnOpen f U))
    (hAffine : ∀ g ∈ s,
      IsAffineOpen ((chapter14RestrictionToOpen f U).basicOpen g))
    (hCover : ∀ x : chapter14RestrictionToOpen f U, ∃ g ∈ s,
      x ∈ (chapter14RestrictionToOpen f U).basicOpen g) :
    chapter14RelativePrincipalOpenCover f U := by
  exact ⟨s, hAffine, hCover⟩

theorem chapter14_relativePrincipalOpenCover_elim
    {X S : Scheme.{u}} {f : X ⟶ S} {U : S.Opens}
    (h : chapter14RelativePrincipalOpenCover f U) :
    ∃ s : Finset (chapter14RelativeFunctionsOnOpen f U),
      (∀ g ∈ s,
        IsAffineOpen ((chapter14RestrictionToOpen f U).basicOpen g)) ∧
        ∀ x : chapter14RestrictionToOpen f U, ∃ g ∈ s,
          x ∈ (chapter14RestrictionToOpen f U).basicOpen g := by
  exact h

theorem chapter14_relativePrincipalOpenCover_mem
    {X S : Scheme.{u}} {f : X ⟶ S} {U : S.Opens}
    (h : chapter14RelativePrincipalOpenCover f U)
    (x : chapter14RestrictionToOpen f U) :
    ∃ g : chapter14RelativeFunctionsOnOpen f U,
      x ∈ (chapter14RestrictionToOpen f U).basicOpen g := by
  rcases h with ⟨s, _, hs⟩
  rcases hs x with ⟨g, hg, hx⟩
  exact ⟨g, hx⟩

def chapter14PreciseQuasiAffineCriterion {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U → chapter14RelativePrincipalOpenCover f U

theorem chapter14_preciseCriterion_restricts_to_affine_open
    {X S : Scheme.{u}} {f : X ⟶ S}
    (h : chapter14PreciseQuasiAffineCriterion f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    chapter14RelativePrincipalOpenCover f U :=
  h U hU

/-! ## Local affine coordinate and localization bridges -/

theorem chapter14_relative_principal_open_is_localization
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (g : chapter14RelativeFunctionsOnOpen f U)
    [CompactSpace (chapter14RestrictionToOpen f U)]
    [QuasiSeparatedSpace (chapter14RestrictionToOpen f U)] :
    IsLocalization.Away g
      Γ(chapter14RestrictionToOpen f U,
        (chapter14RestrictionToOpen f U).basicOpen g) := by
  exact isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ g

theorem chapter14_relative_principal_open_le_top
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (g : chapter14RelativeFunctionsOnOpen f U) :
    (chapter14RestrictionToOpen f U).basicOpen g ≤ ⊤ := by
  exact le_top

theorem chapter14_relative_principal_open_mul
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (g h : chapter14RelativeFunctionsOnOpen f U) :
    (chapter14RestrictionToOpen f U).basicOpen (g * h) =
      (chapter14RestrictionToOpen f U).basicOpen g ⊓
        (chapter14RestrictionToOpen f U).basicOpen h := by
  exact Scheme.basicOpen_mul _ _ _

theorem chapter14_relative_principal_open_one
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) :
    (chapter14RestrictionToOpen f U).basicOpen (1 : chapter14RelativeFunctionsOnOpen f U) =
      ⊤ := by
  exact Scheme.basicOpen_one _

theorem chapter14_relative_principal_open_zero
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) :
    (chapter14RestrictionToOpen f U).basicOpen (0 : chapter14RelativeFunctionsOnOpen f U) =
      ⊥ := by
  exact Scheme.basicOpen_zero _ _

/-! ## The three equivalent formulations -/

private theorem chapter14_absolute_quasiAffine_of_relative_quasiAffine
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) (hU : IsAffineOpen U)
    [QuasiCompact f] [QuasiSeparated f]
    (hX : chapter14QuasiAffine (chapter14BaseChangeToBase f U.ι)) :
    Scheme.IsQuasiAffine (chapter14BaseChange f U.ι) := by sorry

theorem chapter14_quasiAffine_iff_preciseCriterion
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14QuasiAffine f ↔ chapter14PreciseQuasiAffineCriterion f := by
  classical
  constructor
  · intro hX U hU
    have hYrel : chapter14QuasiAffine (chapter14BaseChangeToBase f U.ι) :=
      chapter14_quasiAffine_base_change f U.ι hX
    have hYabs : Scheme.IsQuasiAffine (chapter14BaseChange f U.ι) :=
      chapter14_absolute_quasiAffine_of_relative_quasiAffine f U hU hYrel
    let : Scheme.IsQuasiAffine (chapter14BaseChange f U.ι) := hYabs
    let I := {r : Γ(chapter14BaseChange f U.ι, ⊤) //
      IsAffineOpen ((chapter14BaseChange f U.ι).basicOpen r)}
    let V : I → Set (chapter14BaseChange f U.ι) :=
      fun r ↦ (chapter14BaseChange f U.ι).basicOpen r.1
    have hVopen (r : I) : IsOpen (V r) := by
      exact ((chapter14BaseChange f U.ι).basicOpen r.1).isOpen
    have hVcover : (Set.univ : Set (chapter14BaseChange f U.ι)) ⊆
        ⋃ r : I, V r := by
      intro x hx
      obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, _⟩ :=
        (Scheme.IsQuasiAffine.isBasis_basicOpen
          (chapter14BaseChange f U.ι)).exists_subset_of_mem_open
            (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨r, hr⟩, hxr⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVopen hVcover
    let s : Finset Γ(chapter14BaseChange f U.ι, ⊤) := t.image Subtype.val
    refine ⟨s, ?_, ?_⟩
    · intro g hg
      dsimp [s] at hg
      obtain ⟨r, hrt, rfl⟩ := Finset.mem_image.mp hg
      exact r.property
    · intro x
      have hxcover := ht (Set.mem_univ x)
      obtain ⟨r, hxr⟩ := Set.mem_iUnion.mp hxcover
      obtain ⟨hrt, hxr⟩ := Set.mem_iUnion.mp hxr
      refine ⟨r.1, Finset.mem_image.mpr ⟨r, hrt, rfl⟩, hxr⟩
  · intro hC
    let U : S.affineCover.I₀ → S.Opens := fun i =>
      (S.affineCover.f i).opensRange
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
      let : IsAffine (U i).toScheme := hUi
      let : CompactSpace (U i).toScheme := isCompact_iff_compactSpace.mp hUi.isCompact
      obtain ⟨s, hsAffine, hsCover⟩ := hC (U i) hUi
      have hQ : Scheme.IsQuasiAffine (pullback f (U i).ι) := by
        refine Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen _ ?_
        intro x
        obtain ⟨g, hg, hxg⟩ := hsCover x
        exact ⟨g, hsAffine g hg, hxg⟩
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
            change chapter14AffineEnvelopeMap f
              (chapter14AffineEnvelopeEvaluation f x) =
              chapter14AffineEnvelopeMap f
                (chapter14AffineEnvelopeEvaluation f y)
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
    exact chapter14_quasiAffine_of_affine_envelope_evaluation_is_open f
      (IsOpenImmersion.of_openCover_source
        (chapter14AffineEnvelopeEvaluation f) 𝒱 hinj hlocal)

theorem chapter14_affine_envelope_open_iff_preciseCriterion
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) ↔
      chapter14PreciseQuasiAffineCriterion f := by
  rw [← chapter14_quasiAffine_iff_affine_envelope_evaluation_is_open f,
    chapter14_quasiAffine_iff_preciseCriterion]

theorem chapter14_quasiCompact_open_affine_envelope_iff_preciseCriterion
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    (IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) ∧
        QuasiCompact (chapter14AffineEnvelopeEvaluation f)) ↔
      chapter14PreciseQuasiAffineCriterion f := by
  constructor
  · intro h
    exact (chapter14_quasiAffine_iff_preciseCriterion f).mp
      ((chapter14_quasiAffine_iff_quasiCompact_open_affine_envelope_evaluation f).mpr h)
  · intro h
    exact (chapter14_quasiAffine_iff_quasiCompact_open_affine_envelope_evaluation f).mp
      ((chapter14_quasiAffine_iff_preciseCriterion f).mpr h)

theorem chapter14_quasiAffine_envelope_criterion
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    (chapter14QuasiAffine f ↔
        IsOpenImmersion (chapter14AffineEnvelopeEvaluation f)) ∧
      (IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) ↔
        chapter14PreciseQuasiAffineCriterion f) := by
  exact ⟨chapter14_quasiAffine_iff_affine_envelope_evaluation_is_open f,
    chapter14_affine_envelope_open_iff_preciseCriterion f⟩

theorem chapter14_preciseCriterion_stable_under_fpqc_base_change
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (hg : chapter14Fpqc g) :
    chapter14PreciseQuasiAffineCriterion f ↔
      chapter14PreciseQuasiAffineCriterion (chapter14BaseChangeToBase f g) := by sorry

/-! ## Restriction and map compatibility -/

theorem chapter14_restriction_to_open_over_base
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) :
    chapter14RestrictionToOpenMap f U ≫ U.ι =
      chapter14BaseChangeToSource f U.ι ≫ f := by
  exact pullback.condition.symm

theorem chapter14_relative_function_basicOpen_membership_iff
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens)
    (g : chapter14RelativeFunctionsOnOpen f U)
    (x : chapter14RestrictionToOpen f U) :
    x ∈ (chapter14RestrictionToOpen f U).basicOpen g ↔
      IsUnit ((chapter14RestrictionToOpen f U).presheaf.germ ⊤ x trivial g) := by
  exact chapter14_mem_principalOpen_iff g x

theorem chapter14_relative_principal_cover_iff_finite_affine_basic_opens
    {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Opens) :
    chapter14RelativePrincipalOpenCover f U ↔
      ∃ s : Finset (chapter14RelativeFunctionsOnOpen f U),
        (∀ g ∈ s,
          IsAffineOpen ((chapter14RestrictionToOpen f U).basicOpen g)) ∧
          (⨆ g ∈ s,
            (chapter14RestrictionToOpen f U).basicOpen g) = ⊤ := by
  constructor
  · rintro ⟨s, hsAffine, hsCover⟩
    refine ⟨s, hsAffine, ?_⟩
    apply top_unique
    intro x hx
    obtain ⟨g, hg, hxg⟩ := hsCover x
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨g, TopologicalSpace.Opens.mem_iSup.mpr ⟨hg, hxg⟩⟩
  · rintro ⟨s, hsAffine, hsTop⟩
    refine ⟨s, hsAffine, ?_⟩
    intro x
    have hxTop : x ∈ (⊤ : (chapter14RestrictionToOpen f U).Opens) := by
      trivial
    rw [← hsTop] at hxTop
    obtain ⟨g, hxg⟩ := TopologicalSpace.Opens.mem_iSup.mp hxTop
    obtain ⟨hg, hxg⟩ := TopologicalSpace.Opens.mem_iSup.mp hxg
    exact ⟨g, hg, hxg⟩

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
