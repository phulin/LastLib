import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06.Section01TheCorrectRelativeNotion

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open RelativeScheme

universe u

/-! ## 6.2. Smooth curves turn points into divisors -/

abbrev Chapter06SmoothRelativeCurve {S : Scheme.{u}}
    (C : RelativeScheme S) : Prop :=
  SmoothOfRelativeDimension 1 C.structuralMap

instance chapter11SmoothQuasiProjectiveCurve_to_chapter06SmoothRelativeCurve
    {S : Scheme.{u}} {C : RelativeScheme S}
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter06SmoothRelativeCurve C :=
  Chapter11SmoothQuasiProjectiveCurve.smooth (C := C)

theorem chapter06_smooth_curve_finite_flat_family_is_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    ∃ D : Chapter06RelativeEffectiveDivisor C T d,
      D.divisor.ideal = Z.ideal := by
  sorry

noncomputable def chapter06FiniteFlatFamilyToRelativeDivisor
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    Chapter06RelativeEffectiveDivisor C T d :=
  Classical.choose (chapter06_smooth_curve_finite_flat_family_is_cartier C T d Z)

theorem chapter06FiniteFlatFamilyToRelativeDivisor_ideal
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    (chapter06FiniteFlatFamilyToRelativeDivisor C T d Z).divisor.ideal = Z.ideal :=
  Classical.choose_spec (chapter06_smooth_curve_finite_flat_family_is_cartier C T d Z)

def chapter06RelativeDivisorToFiniteFlatFamily
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06FiniteFlatClosedFamily C T d :=
  { ideal := D.divisor.ideal
    finite_flat_rank := D.finite_flat_rank }

theorem chapter06RelativeDivisorToFiniteFlatFamily_ideal
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    (chapter06RelativeDivisorToFiniteFlatFamily C T d D).ideal = D.divisor.ideal :=
  rfl

theorem chapter06_relative_divisor_to_family_is_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    chapter06IsEffectiveCartierFamily
      (chapter06RelativeDivisorToFiniteFlatFamily C T d D) := by
  exact D.divisor.isEffectiveCartier

noncomputable def chapter06_length_d_family_divisor_equiv
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C] :
    Chapter06FiniteFlatClosedFamily C T d ≃
      Chapter06RelativeEffectiveDivisor C T d where
  toFun := chapter06FiniteFlatFamilyToRelativeDivisor C T d
  invFun := chapter06RelativeDivisorToFiniteFlatFamily C T d
  left_inv := by
    intro Z
    apply chapter06FiniteFlatClosedFamily_ext
    exact chapter06FiniteFlatFamilyToRelativeDivisor_ideal C T d Z
  right_inv := by
    intro D
    apply chapter06_relative_effective_divisor_ext
    exact (chapter06FiniteFlatFamilyToRelativeDivisor_ideal C T d
      (chapter06RelativeDivisorToFiniteFlatFamily C T d D)).trans
      (chapter06RelativeDivisorToFiniteFlatFamily_ideal C T d D)

theorem chapter06_smooth_curve_length_and_divisor_functors_agree
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C] :
    Nonempty (Chapter06FiniteFlatClosedFamily C T d ≃
      Chapter06RelativeEffectiveDivisor C T d) :=
  ⟨chapter06_length_d_family_divisor_equiv C T d⟩

theorem chapter06_smooth_curve_length_family_is_effective_cartier
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    [Chapter06SmoothRelativeCurve C]
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    ∃ D : Chapter06RelativeEffectiveDivisor C T d,
      D.divisor.ideal = Z.ideal ∧
        chapter06IsEffectiveCartierFamily Z := by
  rcases chapter06_smooth_curve_finite_flat_family_is_cartier C T d Z with ⟨D, hD⟩
  refine ⟨D, hD, ?_⟩
  simpa [chapter06IsEffectiveCartierFamily, hD] using D.divisor.isEffectiveCartier

/-!
The node model is written with the affine coordinate ring used by Book 8;
its localization/completion is the usual local ring `k[[x,y]]/(xy)`.  The
profile records both the finite-flat length-one quotient and failure of local
principality of its ideal.
-/

abbrev Chapter06NodeRing (k : Type u) [Field k] := chapter10NodeRing k

abbrev Chapter06NodeIdeal (k : Type u) [Field k] := chapter10NodeIdeal k

abbrev Chapter06NodePointLengthOneProfile (k : Type u) [Field k] :=
  Chapter10NodePointLengthOneProfile k

theorem chapter06_node_point_has_length_one
    (k : Type u) [Field k] :
    Chapter06NodePointLengthOneProfile k :=
  chapter10_node_point_has_length_one k

theorem chapter06_node_point_ideal_is_not_principal
    (k : Type u) [Field k] :
    ¬ ∃ a : Chapter06NodeRing k,
      Chapter06NodeIdeal k = Ideal.span ({a} : Set (Chapter06NodeRing k)) :=
  chapter10_node_ideal_is_not_principal k

theorem chapter06_node_point_is_length_one_but_not_cartier
    (k : Type u) [Field k] :
    Chapter06NodePointLengthOneProfile k ∧
      ¬ ∃ a : Chapter06NodeRing k,
        Chapter06NodeIdeal k = Ideal.span ({a} : Set (Chapter06NodeRing k)) :=
  ⟨chapter06_node_point_has_length_one k,
    chapter06_node_point_ideal_is_not_principal k⟩

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
