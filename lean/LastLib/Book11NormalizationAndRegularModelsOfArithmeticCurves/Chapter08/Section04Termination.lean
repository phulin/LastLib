import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08.Section03ADecreasingLocalInvariant

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter01
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter04
open LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
open scoped AlgebraicGeometry BigOperators

universe u v

/-! ## 8.4. Termination -/

def chapter08LexLe (a b : ℕ × ℕ × ℕ) : Prop :=
  a = b ∨ chapter08LexLess a b

def Chapter08ZeroDimensionalClosedSubset
    {X : Scheme.{u}} (Z : Set X) : Prop :=
  topologicalKrullDim Z = 0

structure Chapter08StageProfile (X : Scheme.{u}) where
  singularLocus : Set X
  singularLocus_eq : singularLocus = chapter08SingularLocus X
  singular_closed : IsClosed singularLocus
  singular_zero_dimensional :
    Chapter08ZeroDimensionalClosedSubset singularLocus
  singular_finite : singularLocus.Finite
  pointInvariant : X → ℕ × ℕ × ℕ
  pointInvariant_maximal : ∃ m : ℕ × ℕ × ℕ,
    (∀ x : X, x ∈ singularLocus → chapter08LexLe (pointInvariant x) m) ∧
      (∃ x : X, x ∈ singularLocus ∧ pointInvariant x = m)

structure Chapter08ResolutionStage where
  carrier : Scheme.{u}
  normal : Chapter08NormalNoetherianSurface carrier
  profile : Chapter08StageProfile carrier

structure Chapter08PreparedNormalSurface (X0 : Scheme.{u}) : Type (u + 1) where
  normal : Chapter08NormalNoetherianSurface X0
  excellent : Chapter01ExcellentScheme X0
  quasiCompact : IsCompact (Set.univ : Set X0)
  singularLocus : Set X0
  singularLocus_eq : singularLocus = chapter08SingularLocus X0
  singular_closed : IsClosed singularLocus
  singular_codimension_two : Chapter08CodimensionAtLeastTwo singularLocus
  singular_finite_on_quasiCompact_open :
    ∀ V : X0.Opens, IsCompact (V : Set X0) →
      (singularLocus ∩ (V : Set X0)).Finite

structure Chapter08ResolutionStep
    (S T : Chapter08ResolutionStage) where
  map : T.carrier ⟶ S.carrier
  modification : Chapter08ResolutionModification map
  centers : Set S.carrier
  centers_finite : centers.Finite
  centers_above_maximal :
    ∃ m : ℕ × ℕ × ℕ,
      (∀ x : S.carrier, x ∈ centers → S.profile.pointInvariant x = m) ∧
        (∀ x : S.carrier, x ∈ S.profile.singularLocus →
          chapter08LexLe (S.profile.pointInvariant x) m) ∧
        (∀ x : S.carrier, x ∈ S.profile.singularLocus →
          S.profile.pointInvariant x = m → x ∈ centers)
  isIso_off_centers :
    ∀ U : S.carrier.Opens,
      (∀ x : S.carrier, x ∈ U → x ∉ centers) →
        IsIso (map ∣_ U)
  target_singular_points_decrease :
    ∀ y : T.carrier, y ∈ T.profile.singularLocus →
      ∃ x : S.carrier, x ∈ centers ∧
        chapter08LexLess (T.profile.pointInvariant y)
          (S.profile.pointInvariant x)

theorem chapter08_resolutionStep_is_projective
    {S T : Chapter08ResolutionStage} (step : Chapter08ResolutionStep S T) :
    Chapter07IsProjectiveMorphism step.map := by
  exact chapter08_resolutionModification_is_projective step.modification

theorem chapter08_resolutionStep_is_proper
    {S T : Chapter08ResolutionStage} (step : Chapter08ResolutionStep S T) :
    IsProper step.map := by
  exact chapter08_resolutionModification_is_proper step.modification

structure Chapter08ResolutionSequence (X0 : Scheme.{u}) : Type (u + 1) where
  carrier : ℕ → Scheme.{u}
  initial : carrier 0 = X0
  regularOpen : X0.Opens
  normal : ∀ n, Chapter08NormalNoetherianSurface (carrier n)
  singularLocus : ∀ n, Set (carrier n)
  singularLocus_eq : ∀ n, singularLocus n = chapter08SingularLocus (carrier n)
  singular_closed : ∀ n, IsClosed (singularLocus n)
  singular_finite : ∀ n, (singularLocus n).Finite
  pointInvariant : ∀ n, carrier n → ℕ × ℕ × ℕ
  map : ∀ n, carrier (n + 1) ⟶ carrier n
  regularOpenAt : ∀ n, (carrier n).Opens
  regularOpenAt_initial : Prop
  regularOpenAt_step_eq : ∀ n,
    regularOpenAt (n + 1) = (map n) ⁻¹ᵁ regularOpenAt n
  regularOpen_preserved : ∀ n, IsIso ((map n) ∣_ regularOpenAt n)
  modification : ∀ n, Chapter08ResolutionModification (map n)
  centers : ∀ n, Set (carrier n)
  centers_finite : ∀ n, (centers n).Finite
  centers_are_maximal : ∀ n, ∃ m : ℕ × ℕ × ℕ,
    (∀ x : carrier n, x ∈ centers n → pointInvariant n x = m) ∧
      (∀ x : carrier n, x ∈ singularLocus n →
        chapter08LexLe (pointInvariant n x) m)
  target_decrease : ∀ n, ∀ y : carrier (n + 1),
    y ∈ singularLocus (n + 1) →
      ∃ x : carrier n, x ∈ centers n ∧
        chapter08LexLess (pointInvariant (n + 1) y) (pointInvariant n x)

def Chapter08ResolutionSequenceAtStage
    {X0 : Scheme.{u}} (S : Chapter08ResolutionSequence X0) (n : ℕ) :
    Chapter08ResolutionStage where
  carrier := S.carrier n
  normal := S.normal n
  profile :=
    { singularLocus := S.singularLocus n
      singularLocus_eq := S.singularLocus_eq n
      singular_closed := S.singular_closed n
      singular_zero_dimensional := by sorry
      singular_finite := S.singular_finite n
      pointInvariant := S.pointInvariant n
      pointInvariant_maximal := by sorry }

theorem chapter08_resolutionSequence_stage_projective
    {X0 : Scheme.{u}} (S : Chapter08ResolutionSequence X0) (n : ℕ) :
    Chapter07IsProjectiveMorphism (S.map n) := by
  exact chapter08_resolutionModification_is_projective (S.modification n)

theorem chapter08_resolutionSequence_stage_proper
    {X0 : Scheme.{u}} (S : Chapter08ResolutionSequence X0) (n : ℕ) :
    IsProper (S.map n) := by
  exact chapter08_resolutionModification_is_proper (S.modification n)

theorem chapter08_no_infinite_strictly_decreasing_invariant
    (a : ℕ → ℕ × ℕ × ℕ)
    (hdecrease : ∀ n : ℕ, chapter08LexLess (a (n + 1)) (a n)) :
    False := by
  sorry

theorem chapter08_stage_singular_locus_finite
    (S : Chapter08ResolutionStage) : S.profile.singularLocus.Finite :=
  S.profile.singular_finite

theorem chapter08_stage_has_a_maximal_invariant
    (S : Chapter08ResolutionStage) :
    ∃ m : ℕ × ℕ × ℕ,
      (∀ x : S.carrier, x ∈ S.profile.singularLocus →
        chapter08LexLe (S.profile.pointInvariant x) m) ∧
        ∃ x : S.carrier, x ∈ S.profile.singularLocus ∧
          S.profile.pointInvariant x = m := by
  exact S.profile.pointInvariant_maximal

theorem chapter08_resolution_stage_clears_maximal_invariant
    (S : Chapter08ResolutionStage)
    (hnotregular : ¬ Chapter04RegularScheme S.carrier) :
    Nonempty (Σ T : Chapter08ResolutionStage, Chapter08ResolutionStep S T) := by
  sorry

theorem chapter08_resolution_stage_preserves_regular_open
    {S T : Chapter08ResolutionStage} (step : Chapter08ResolutionStep S T)
    (U : S.carrier.Opens) (_hU : ∀ x : S.carrier, x ∈ U →
      IsRegularLocalRing (S.carrier.presheaf.stalk x))
    (hUcenters : ∀ x : S.carrier, x ∈ U → x ∉ step.centers) :
    IsIso (step.map ∣_ U) := by
  exact step.isIso_off_centers U hUcenters

theorem chapter08_resolution_termination
    (X0 : Scheme.{u}) (hX0 : Chapter08PreparedNormalSurface X0) :
    Nonempty (Chapter08ResolutionSequence X0) ∧
      ∃ S : Chapter08ResolutionSequence X0, ∃ N : ℕ,
        Chapter04RegularScheme (S.carrier N) := by
  sorry

theorem chapter08_resolution_termination_relative_to_regular_open
    (X0 : Scheme.{u}) (hX0 : Chapter08PreparedNormalSurface X0)
    (U : X0.Opens)
    (hU : ∀ x : X0, x ∈ U →
      IsRegularLocalRing (X0.presheaf.stalk x)) :
    ∃ S : Chapter08ResolutionSequence X0, S.regularOpen = U ∧
      ∃ N : ℕ, Chapter04RegularScheme (S.carrier N) := by
  sorry

def chapter08SequenceCompositeMap
    {X0 : Scheme.{u}} (S : Chapter08ResolutionSequence X0) :
    ∀ N : ℕ, S.carrier N ⟶ S.carrier 0
  | 0 => 𝟙 _
  | n + 1 => S.map n ≫ chapter08SequenceCompositeMap S n

def Chapter08SequenceCompositeProjective
    {X0 : Scheme.{u}} (S : Chapter08ResolutionSequence X0) (N : ℕ) : Prop :=
  Chapter07IsProjectiveMorphism (chapter08SequenceCompositeMap S N)

theorem chapter08_projectivity_of_terminated_composite
    {X0 : Scheme.{u}} (S : Chapter08ResolutionSequence X0) (N : ℕ) :
    Chapter08SequenceCompositeProjective S N := by
  sorry

theorem chapter08_resolution_termination_gives_resolution_data
    (X0 : Scheme.{u}) (hX0 : Chapter08PreparedNormalSurface X0)
    (U : X0.Opens)
    (hU : ∀ x : X0, x ∈ U →
      IsRegularLocalRing (X0.presheaf.stalk x)) :
    Nonempty (Chapter08ResolutionData X0 U) := by
  sorry

/-! The proof's global finiteness input is explicit: a noetherian quasi-compact surface cannot
produce infinitely many distinct zero-dimensional singular points at one stage. -/

theorem chapter08_zero_dimensional_closed_finite_on_quasiCompact
    {X : Scheme.{u}} (Z : Set X)
    (hnoetherian : IsNoetherian X) (hclosed : IsClosed Z)
    (hzero : Chapter08ZeroDimensionalClosedSubset Z)
    (hqc : IsCompact (Set.univ : Set X)) : Z.Finite := by
  sorry

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter08
