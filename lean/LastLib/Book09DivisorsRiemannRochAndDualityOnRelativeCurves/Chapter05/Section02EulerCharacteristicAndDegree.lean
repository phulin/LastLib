import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

noncomputable section

/-! §5.2. Euler characteristic and degree. -/

noncomputable def chapter05CartierTwistedQuotientModule {X : Scheme}
    (D : Chapter05EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] : X.Modules :=
  chapter04Tensor (chapter10OofD D).module (chapter10CartierQuotientModule D)

/-! This is the displayed exact sequence
`0 → O_X → O_X(D) → O_D(D) → 0`.  Its quotient is the canonical tensor of
the pushforward structure sheaf of `D` with `O_X(D)`. -/

structure Chapter05EffectiveCartierTwistedExactSequence {X : Scheme}
    (D : Chapter05EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] [Chapter10SectionVanishingIdealAPI X] where
  quotient :
    (chapter10OofD D).module ⟶ chapter05CartierTwistedQuotientModule D
  comp_zero :
    chapter10OofD_section D ≫ quotient = 0
  mono_inclusion : Mono (chapter10OofD_section D)
  epi_quotient : Epi quotient
  exact :
    (ShortComplex.mk (chapter10OofD_section D) quotient comp_zero).Exact

theorem chapter05_effective_cartier_exact_sequence
    {X : Scheme} (D : Chapter05EffectiveCartierDivisor X)
    [Chapter10IdealDualAPI X] [Chapter10SectionVanishingIdealAPI X] :
    Nonempty (Chapter05EffectiveCartierTwistedExactSequence D) := by
  sorry

theorem chapter05_effective_cartier_minus_sequence
    {X : Scheme} (D : Chapter05EffectiveCartierDivisor X) :
    Nonempty (Chapter05CartierExactSequence D) :=
  chapter10_cartier_exact_sequence_exists D

/-! Zero-dimensional cohomology is isolated as an explicit interface because
the pinned tree has no coherent-cohomology object. -/

class Chapter05ZeroDimensionalCohomologyTheory
    {k : Type u} [Field k] {Z : Scheme}
    (q : Z ⟶ Spec (.of k))
    [Chapter05EulerCharacteristicTheory Z] where
  finiteOverField :
    ∃ d, Chapter05FiniteLocallyFreeProfile q d
  cohomology : ℕ → Z.Modules → ModuleCat k
  h1_vanishes : ∀ M : Z.Modules, IsZero (cohomology 1 M)
  euler_eq_h0_finrank :
    ∀ M : Z.Modules,
      chapter05EulerCharacteristic M = (Module.finrank k (cohomology 0 M) : ℤ)

/-! The finite quotient in the Cartier exact sequence is a sheaf on the
ambient curve, so its Euler-characteristic/length bridge is indexed by the
ambient structure morphism rather than by a zero-dimensional cohomology
theory for the whole curve. -/

class Chapter05FiniteCartierQuotientEulerTheory
    {k : Type u} [Field k] {X : Scheme}
    (q : X ⟶ Spec (.of k))
    [Chapter05EulerCharacteristicTheory X] where
  finite_flat_cartier_quotient_euler :
    ∀ [Chapter10IdealDualAPI X]
      (D : Chapter05EffectiveCartierDivisor X) (d : ℕ),
      Chapter05FiniteLocallyFreeProfile (D.ideal.subschemeι ≫ q) d →
        chapter05EulerCharacteristic (chapter05CartierTwistedQuotientModule D) =
          (d : ℤ)

theorem chapter05_zero_dimensional_h1_vanishes
    {k : Type u} [Field k] {Z : Scheme}
    (q : Z ⟶ Spec (.of k))
    [Chapter05EulerCharacteristicTheory Z]
    [Chapter05ZeroDimensionalCohomologyTheory q]
    (M : Z.Modules) :
    IsZero (Chapter05ZeroDimensionalCohomologyTheory.cohomology q 1 M) :=
  Chapter05ZeroDimensionalCohomologyTheory.h1_vanishes M

theorem chapter05_zero_dimensional_euler_eq_h0_finrank
    {k : Type u} [Field k] {Z : Scheme}
    (q : Z ⟶ Spec (.of k))
    [Chapter05EulerCharacteristicTheory Z]
    [Chapter05ZeroDimensionalCohomologyTheory q]
    (M : Z.Modules) :
      chapter05EulerCharacteristic M =
      (Module.finrank k
        (Chapter05ZeroDimensionalCohomologyTheory.cohomology q 0 M) : ℤ) :=
  Chapter05ZeroDimensionalCohomologyTheory.euler_eq_h0_finrank M

theorem chapter05_dvr_point_quotient_length
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (n : ℕ) :
    Module.length A
        (A ⧸ ((IsLocalRing.maximalIdeal A) ^ n : Ideal A)) = (n : ℕ∞) := by
  sorry

theorem chapter05_zero_dimensional_twist_preserves_length
    {R : Type u} [CommRing R] {M N : Type v}
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) :
    Module.length R M = Module.length R N := by
  sorry

/-! The local calculation behind `n[x]` is recorded in the DVR form used by
the regular local ring at a closed point. -/

structure Chapter05PointDivisorLengthProfile
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] where
  multiplicity : ℕ
  quotientLength : ℕ∞
    := Module.length A
      (A ⧸ ((IsLocalRing.maximalIdeal A) ^ multiplicity : Ideal A))
  quotientLength_eq_multiplicity : quotientLength = (multiplicity : ℕ∞)

theorem chapter05_point_divisor_length_profile
    {A : Type u} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (n : ℕ) :
    Nonempty (Chapter05PointDivisorLengthProfile (A := A)) := by
  refine ⟨{ multiplicity := n
            quotientLength := Module.length A
              (A ⧸ ((IsLocalRing.maximalIdeal A) ^ n : Ideal A))
            quotientLength_eq_multiplicity := ?_ }⟩
  exact chapter05_dvr_point_quotient_length n

theorem chapter05_effective_divisor_line_bundle_degree_eq_length
    {k : Type u} [Field k] {X : Scheme}
    (q : X ⟶ Spec (.of k))
    [Chapter05EulerCharacteristicTheory X]
    [IsProper q]
    [Chapter05FiniteCartierQuotientEulerTheory q]
    [Chapter10IdealDualAPI X]
    [Chapter10SectionVanishingIdealAPI X]
    (D : Chapter05EffectiveCartierDivisor X) (d : ℕ)
    (hD : Chapter05FiniteLocallyFreeProfile
      (D.ideal.subschemeι ≫ q) d) :
    chapter05LineBundleDegree (chapter10OofD D) = (d : ℤ) := by
  sorry

structure Chapter05EffectiveCartierDivisorDegreeData
    {k : Type u} [Field k] {X : Scheme}
    (q : X ⟶ Spec (.of k))
    (D : Chapter05EffectiveCartierDivisor X) (d : ℕ) where
  associatedDivisor : Chapter05Divisor X
  associated_support : (associatedDivisor.coeff.support : Set X) = D.ideal.support
  degree_eq_length : chapter05Degree q associatedDivisor = (d : ℤ)

theorem chapter05_effective_divisor_euler_difference_eq_degree
    {k : Type u} [Field k] {X : Scheme}
    (q : X ⟶ Spec (.of k))
    [Chapter05EulerCharacteristicTheory X]
    [IsProper q]
    [Chapter05FiniteCartierQuotientEulerTheory q]
    [Chapter10IdealDualAPI X]
    [Chapter10SectionVanishingIdealAPI X]
    (D : Chapter05EffectiveCartierDivisor X) (d : ℕ)
    (hD : Chapter05FiniteLocallyFreeProfile
      (D.ideal.subschemeι ≫ q) d)
    (P : Chapter05EffectiveCartierDivisorDegreeData q D d) :
    chapter05LineBundleDegree (chapter10OofD D) =
      chapter05Degree q P.associatedDivisor := by
  sorry

/-! Every line bundle is represented by a difference of effective divisors on
a proper Cohen--Macaulay curve.  The two effective pieces are packaged using
the earlier Cartier/Picard interfaces. -/

structure Chapter05EffectiveDivisorDifferencePresentation
    {X : Scheme} (L : Chapter05LineBundle X)
    [Chapter10IdealDualAPI X] [Chapter10PicardOperations X] where
  positive : Chapter05EffectiveCartierDivisor X
  negative : Chapter05EffectiveCartierDivisor X
  representedBy :
    Nonempty (Chapter05LineBundleIso L
      (chapter10PicardTensor (chapter10OofD positive)
        (Chapter10PicardOperations.dual (chapter10OofD negative))))

class Chapter05EffectiveDivisorDifferenceTheory (X : Scheme)
    [Chapter10IdealDualAPI X] [Chapter10PicardOperations X] where
  every_line_bundle_has_effective_difference :
    ∀ L : Chapter05LineBundle X,
      Nonempty (Chapter05EffectiveDivisorDifferencePresentation L)

theorem chapter05_line_bundle_has_effective_difference
    {X : Scheme} [Chapter10IdealDualAPI X] [Chapter10PicardOperations X]
    [Chapter05EffectiveDivisorDifferenceTheory X]
    (L : Chapter05LineBundle X) :
    Nonempty (Chapter05EffectiveDivisorDifferencePresentation L) :=
  Chapter05EffectiveDivisorDifferenceTheory.every_line_bundle_has_effective_difference L

theorem chapter05_line_bundle_degree_tensor_add
    {k : Type u} [Field k]
    (C : Chapter05ProperRegularIntegralCurve k)
    [Chapter05EulerCharacteristicTheory C.carrier]
    [Chapter09LineBundleTensorTheory C.carrier]
    (L M : Chapter05LineBundle C.carrier) :
    chapter05LineBundleDegree (chapter09Tensor L M) =
      chapter05LineBundleDegree L + chapter05LineBundleDegree M := by
  sorry

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter05
