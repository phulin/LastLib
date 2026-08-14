import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14.Section03FinitePresentationAndOpenness

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
    ∃ g, x ∈ (chapter14RestrictionToOpen f U).basicOpen g := by
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
    (h : IsAffineOpen ((chapter14RestrictionToOpen f U).basicOpen g)) :
    IsLocalization.Away g
      Γ(chapter14RestrictionToOpen f U,
        (chapter14RestrictionToOpen f U).basicOpen g) := by
  exact h.isLocalization_basicOpen g

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
  exact Scheme.basicOpen_zero _

/-! ## The three equivalent formulations -/

theorem chapter14_quasiAffine_iff_preciseCriterion
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    chapter14QuasiAffine f ↔ chapter14PreciseQuasiAffineCriterion f := by
  sorry

theorem chapter14_affine_envelope_open_iff_preciseCriterion
    {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] :
    IsOpenImmersion (chapter14AffineEnvelopeEvaluation f) ↔
      chapter14PreciseQuasiAffineCriterion f := by
  rw [← chapter14_quasiAffine_iff_affine_envelope_evaluation_is_open f,
    chapter14_quasiAffine_iff_preciseCriterion]

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
      chapter14PreciseQuasiAffineCriterion (chapter14BaseChangeToBase f g) := by
  sorry

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
  sorry

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter14
