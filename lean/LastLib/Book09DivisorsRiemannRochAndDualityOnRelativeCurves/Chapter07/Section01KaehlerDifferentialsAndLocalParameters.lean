import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/-!
## 7.1 Kähler differentials and local parameters

The universal affine construction and the conormal sequence live in
`Dependencies.lean`; this section adds the curve-facing names and the
relative-dimension-one bridges.
-/

theorem chapter07_smooth_relative_differential_data_exists
    {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] :
    Nonempty (Chapter07SmoothRelativeDifferentialData f) := by
  sorry

noncomputable def chapter07SmoothRelativeDifferentialData
    {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] : Chapter07SmoothRelativeDifferentialData f :=
  Classical.choice (chapter07_smooth_relative_differential_data_exists f)

noncomputable def chapter07RelativeDifferentialLineBundle
    {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] : Chapter07LineBundle X :=
  let D := chapter07SmoothRelativeDifferentialData f
  { module := D.relativeDifferentials.relativeDifferentials
    isInvertible := D.isLineBundle }

theorem chapter07_smooth_curve_differentials_are_quasicoherent
    {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] :
    (chapter07RelativeDifferentialLineBundle f).module.IsQuasicoherent := by
  sorry

theorem chapter07_smooth_curve_differentials_are_a_line_bundle
    {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] :
    Chapter07IsLineBundle (chapter07RelativeDifferentialLineBundle f).module := by
  exact (chapter07RelativeDifferentialLineBundle f).isInvertible

theorem chapter07_standard_smooth_differentials_have_relative_rank_one
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [Nontrivial A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R A] :
    Module.rank A Ω[A⁄R] = 1 := by
  exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1

theorem chapter07_affine_differentials_are_generated_by_d
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    Submodule.span A (Set.range (KaehlerDifferential.D R A)) = ⊤ := by
  exact KaehlerDifferential.span_range_derivation R A

theorem chapter07_conormal_sequence_has_zero_composite
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (h : Function.Surjective (algebraMap A B)) :
    (KaehlerDifferential.mapBaseChange R A B) ∘
        (KaehlerDifferential.kerCotangentToTensor R A B) = 0 := by
  funext x
  exact (chapter07_affine_conormal_sequence_exact R A B h).apply_apply_eq_zero x

theorem chapter07_smooth_curve_local_parameter_transition
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (P : Chapter07LocalParameterChangeData R A) :
    ∃ jacobian : A,
      KaehlerDifferential.D R A P.u =
        jacobian • KaehlerDifferential.D R A P.t ∧
      IsUnit jacobian := by
  sorry

theorem chapter07_local_parameter_differential_is_a_basis
    (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
    (P : Chapter07LocalParameterChangeData R A) :
    ∃ e : Module.Basis (Fin 1) A Ω[A⁄R],
      e 0 = KaehlerDifferential.D R A P.t := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter07
