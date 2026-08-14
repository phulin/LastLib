import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05.Dependencies
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05.Section02EulerCharacteristicAndDegree

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open scoped BigOperators

noncomputable section

/-! §5.4. Horizontal divisors. -/

abbrev Chapter05RelativeEffectiveCartierDivisor {C T : Scheme}
    (c : C ⟶ T) (d : ℕ) :=
  Chapter10RelativeEffectiveCartierDivisor c d

theorem chapter05_relative_divisor_projection_is_finite_locally_free
    {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter05RelativeEffectiveCartierDivisor c d) :
    Chapter05FiniteLocallyFreeProfile
      (chapter10RelativeDivisorProjection D) d :=
  D.finiteLocallyFree

theorem chapter05_relative_divisor_fiber_length
    {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter05RelativeEffectiveCartierDivisor c d) (t : T) :
    Chapter10FiberLength (chapter10RelativeDivisorProjection D) t = d :=
  chapter10_relativeDivisor_degree D t

theorem chapter05_relative_divisor_degree_on_projective_flat_family
    (F : Chapter05ProjectiveFlatRelativeCurve)
    [Chapter05FiberEulerCharacteristicTheory F]
    [Chapter05RelativeCohomologyBaseChangeTheory F]
    [Chapter10IdealDualAPI F.X]
    [Chapter10SectionVanishingIdealAPI F.X]
    {d : ℕ} (D : Chapter05RelativeEffectiveCartierDivisor F.f d) (s : F.S)
    [Chapter10IdealDualAPI (F.f.fiber s)]
    [Chapter10SectionVanishingIdealAPI (F.f.fiber s)] :
    chapter05FiberDegree F (chapter10OofD D.divisor) s = (d : ℤ) := by
  sorry

structure Chapter05RelativeDivisorFiberBaseChangeData
    {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter05RelativeEffectiveCartierDivisor c d) (t : T)
    [Chapter10IdealDualAPI C]
    [Chapter10IdealDualAPI (c.fiber t)]
    [Chapter10SectionVanishingIdealAPI (c.fiber t)] where
  fiberDivisor : Chapter05EffectiveCartierDivisor (c.fiber t)
  fiberIdeal_eq :
    fiberDivisor.ideal = D.divisor.ideal.comap (c.fiberι t)
  exactSequence :
    Nonempty (Chapter05EffectiveCartierTwistedExactSequence fiberDivisor)
  finiteLocallyFree :
    Chapter05FiniteLocallyFreeProfile
      (fiberDivisor.ideal.subschemeι ≫ c.fiberToSpecResidueField t) d
  lineBundle_base_change :
    Nonempty (Chapter05LineBundleIso
      (chapter09PullbackLineBundle (c.fiberι t) (chapter10OofD D.divisor))
      (chapter10OofD fiberDivisor))

theorem chapter05_relative_divisor_restricts_to_a_cartier_fiber
    {C T : Scheme} {c : C ⟶ T} [Flat c] {d : ℕ}
    (D : Chapter05RelativeEffectiveCartierDivisor c d) (t : T) :
    Nonempty (Chapter05EffectiveCartierDivisor (c.fiber t)) := by
  sorry

theorem chapter05_relative_divisor_has_fiber_base_change_data
    {C T : Scheme} {c : C ⟶ T} [Flat c] {d : ℕ}
    (D : Chapter05RelativeEffectiveCartierDivisor c d) (t : T)
    [Chapter10IdealDualAPI C]
    [Chapter10IdealDualAPI (c.fiber t)]
    [Chapter10SectionVanishingIdealAPI (c.fiber t)] :
    Nonempty (Chapter05RelativeDivisorFiberBaseChangeData D t) := by
  sorry

theorem chapter05_cartier_exact_sequence_is_compatible_with_fiber_base_change
    {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter05RelativeEffectiveCartierDivisor c d) (t : T)
    [Chapter10IdealDualAPI C]
    [Chapter10IdealDualAPI (c.fiber t)]
    [Chapter10SectionVanishingIdealAPI (c.fiber t)]
    (H : Chapter05RelativeDivisorFiberBaseChangeData D t) :
    Nonempty (Chapter05EffectiveCartierTwistedExactSequence H.fiberDivisor) :=
  H.exactSequence

theorem chapter05_zero_dimensional_twist_preserves_finrank
    {k : Type u} [Field k] (M N : ModuleCat k) (e : M ≅ N) :
    Module.finrank k M = Module.finrank k N := by
  sorry

/-! The intersection number with a fiber is the length of the finite flat
scheme-theoretic intersection `D ×_X X_s`, represented by the relative
divisor projection. -/

noncomputable def chapter05HorizontalIntersectionNumber
    {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter05RelativeEffectiveCartierDivisor c d) (t : T) : ℤ :=
  (Chapter10FiberLength (chapter10RelativeDivisorProjection D) t : ℤ)

theorem chapter05_horizontal_intersection_number_formula
    {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter05RelativeEffectiveCartierDivisor c d) (t : T) :
    chapter05HorizontalIntersectionNumber D t =
      (Chapter10FiberLength (chapter10RelativeDivisorProjection D) t : ℤ) :=
  rfl

theorem chapter05_horizontal_intersection_number_eq_rank
    {C T : Scheme} {c : C ⟶ T} {d : ℕ}
    (D : Chapter05RelativeEffectiveCartierDivisor c d) (t : T) :
    chapter05HorizontalIntersectionNumber D t = (d : ℤ) := by
  sorry

structure Chapter05RegularSurfaceOverRegularCurve where
  base : Scheme
  total : Scheme
  map : total ⟶ base
  flat : Flat map
  locallyOfFinitePresentation : LocallyOfFinitePresentation map
  relativeCurve : Chapter09RelativeCurve map
  baseLocallyNoetherian : IsLocallyNoetherian base
  totalLocallyNoetherian : IsLocallyNoetherian total
  base_regular_stalk : ∀ s : base,
    IsRegularLocalRing (base.presheaf.stalk s)
  base_dimension_one : ∀ s : base,
    ringKrullDim (base.presheaf.stalk s) = 1
  total_regular_stalk : ∀ x : total,
    IsRegularLocalRing (total.presheaf.stalk x)
  total_dimension_two : ∀ x : total,
    ringKrullDim (total.presheaf.stalk x) = 2

theorem chapter05_surface_fiber_intersection_is_horizontal_length
    (R : Chapter05RegularSurfaceOverRegularCurve)
    {d : ℕ} (D : Chapter05RelativeEffectiveCartierDivisor R.map d)
    (s : R.base) :
    chapter05HorizontalIntersectionNumber D s =
      (Chapter10FiberLength (chapter10RelativeDivisorProjection D) s : ℤ) :=
  rfl

/-! Proper intersections are sums of local lengths weighted by residue
degrees.  The `regular_sequence` field in each point packages the expected
regular-sequence hypothesis for `(f_D,f_s)`. -/

theorem chapter05_proper_intersection_number_formula
    {X S : Scheme} {f : X ⟶ S}
    {D : Chapter05EffectiveCartierDivisor X} {s : S}
    (I : Chapter05ProperIntersectionData f D s) :
    chapter05IntersectionNumber I =
      Finset.sum I.points.attach (fun x =>
        (chapter05LocalIntersectionMultiplicity
          (I.point_data x.1 x.2) : ℤ) *
          (f.residueDegree (I.point_data x.1 x.2).point : ℤ)) :=
  rfl

theorem chapter05_proper_intersection_requires_finite_support
    {X S : Scheme} (f : X ⟶ S)
    (D : Chapter05EffectiveCartierDivisor X) (s : S)
    (hvertical : chapter05ContainsFiber f D s)
    (hfiber_not_finite : ¬ (Set.Finite (f ⁻¹' ({s} : Set S)))) :
    ¬ Nonempty (Chapter05ProperIntersectionData f D s) := by
  exact chapter05_vertical_divisor_has_no_proper_intersection
    f D s hvertical hfiber_not_finite

/-! Self-intersection and component-pairing numbers are intentionally a later
surface-theory interface; the horizontal fiber intersection above is the only
pairing fixed in this chapter. -/

class Chapter05SurfaceIntersectionPairingTheory
    (X : Scheme) where
  selfIntersection : Chapter05EffectiveCartierDivisor X → ℤ
  componentPairing :
    Chapter05EffectiveCartierDivisor X → Chapter05EffectiveCartierDivisor X → ℤ

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05
