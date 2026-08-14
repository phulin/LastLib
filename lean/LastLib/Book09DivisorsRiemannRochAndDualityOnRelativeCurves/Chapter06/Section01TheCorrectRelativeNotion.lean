import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open RelativeScheme
open scoped BigOperators Polynomial

universe u

/-! ## 6.1. The correct relative notion -/

theorem chapter06_relative_effective_divisor_is_cartier_and_finite_flat
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    D.divisor.isEffectiveCartier ∧
      Chapter06FiniteFlatRank (chapter06RelativeDivisorProjection D) d := by
  exact ⟨D.divisor.isEffectiveCartier, D.finite_flat_rank⟩

theorem chapter06_relative_effective_divisor_inclusion_is_closed_immersion
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    IsClosedImmersion D.divisor.inclusion := by
  infer_instance

theorem chapter06_finite_flat_closed_family_inclusion_is_closed_immersion
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    IsClosedImmersion Z.ideal.subschemeι := by
  infer_instance

theorem chapter06_relative_effective_divisor_ext
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D E : Chapter06RelativeEffectiveDivisor C T d)
    (h : D.divisor.ideal = E.divisor.ideal) : D = E := by
  cases D with
  | mk D hD =>
    cases E with
    | mk E hE =>
      cases h
      rfl

noncomputable def chapter06RelativeDivisorBaseChangeAmbientMap
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T) :
    Chapter06RelativeDivisorAmbient C U ⟶ Chapter06RelativeDivisorAmbient C T := by
  simpa only [u.comm] using
    (chapter10BaseChangeMap C.structuralMap T.structuralMap u.hom)

noncomputable def chapter06RelativeEffectiveDivisorBaseChange
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06RelativeEffectiveDivisor C U d := by
  refine
    { divisor :=
        { ideal := D.divisor.ideal.comap
            (chapter06RelativeDivisorBaseChangeAmbientMap C T U u)
          isEffectiveCartier := by sorry }
      finite_flat_rank := by sorry }

def Chapter06RelativeDivisorBaseChangeRelation
    {S : Scheme.{u}} {C T U : RelativeScheme S} {d : ℕ}
    (u : U ⟶ T) (D : Chapter06RelativeEffectiveDivisor C T d)
    (E : Chapter06RelativeEffectiveDivisor C U d) : Prop :=
  Chapter11DivisorPullbackRelation
    (chapter06RelativeDivisorBaseChangeAmbientMap C T U u)
    D.divisor E.divisor

theorem chapter06_relative_effective_divisor_base_change_is_cartier
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    (chapter06RelativeEffectiveDivisorBaseChange C T U u d D).divisor.isEffectiveCartier := by
  exact (chapter06RelativeEffectiveDivisorBaseChange C T U u d D).divisor.isEffectiveCartier

theorem chapter06_relative_effective_divisor_base_change_is_finite_flat
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06FiniteFlatRank
      (chapter06RelativeDivisorProjection
        (chapter06RelativeEffectiveDivisorBaseChange C T U u d D)) d := by
  exact (chapter06RelativeEffectiveDivisorBaseChange C T U u d D).finite_flat_rank

theorem chapter06_relative_effective_divisor_base_change_has_same_rank
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) (t : U.carrier) :
    Scheme.Hom.finrank
        (chapter06RelativeDivisorProjection
          (chapter06RelativeEffectiveDivisorBaseChange C T U u d D)) t = d := by
  exact chapter06_relativeEffectiveDivisor_rank
    (chapter06RelativeEffectiveDivisorBaseChange C T U u d D) t

theorem chapter06_relative_effective_divisor_base_change_is_pullback
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06RelativeDivisorBaseChangeRelation u D
      (chapter06RelativeEffectiveDivisorBaseChange C T U u d D) := by
  sorry

theorem chapter06_relative_effective_divisor_base_change_id
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    chapter06RelativeEffectiveDivisorBaseChange C T T (𝟙 T) d D = D := by
  sorry

theorem chapter06_relative_effective_divisor_base_change_comp
    {S : Scheme.{u}} (C T U V : RelativeScheme S)
    (u : U ⟶ T) (v : V ⟶ U) (d : ℕ)
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    chapter06RelativeEffectiveDivisorBaseChange C U V v d
        (chapter06RelativeEffectiveDivisorBaseChange C T U u d D) =
      chapter06RelativeEffectiveDivisorBaseChange C T V (u ≫ v) d D := by
  sorry

noncomputable def chapter06FiniteFlatClosedFamilyBaseChange
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ) (Z : Chapter06FiniteFlatClosedFamily C T d) :
    Chapter06FiniteFlatClosedFamily C U d := by
  refine
    { ideal := Z.ideal.comap (chapter06RelativeDivisorBaseChangeAmbientMap C T U u)
      finite_flat_rank := by sorry }

theorem chapter06FiniteFlatClosedFamilyBaseChange_ideal
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ) (Z : Chapter06FiniteFlatClosedFamily C T d) :
    (chapter06FiniteFlatClosedFamilyBaseChange C T U u d Z).ideal =
      Z.ideal.comap (chapter06RelativeDivisorBaseChangeAmbientMap C T U u) :=
  rfl

theorem chapter06_finiteFlatClosedFamily_base_change_has_same_rank
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ) (Z : Chapter06FiniteFlatClosedFamily C T d) (t : U.carrier) :
    Scheme.Hom.finrank
        (chapter06FiniteFlatClosedFamilyProjection
          (chapter06FiniteFlatClosedFamilyBaseChange C T U u d Z)) t = d := by
  exact (chapter06FiniteFlatClosedFamilyBaseChange C T U u d Z).finite_flat_rank.2.2.2 t

theorem chapter06_finiteFlatClosedFamily_base_change_is_effectiveCartier
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ) (Z : Chapter06FiniteFlatClosedFamily C T d)
    (hZ : chapter06IsEffectiveCartierFamily Z) :
    chapter06IsEffectiveCartierFamily
      (chapter06FiniteFlatClosedFamilyBaseChange C T U u d Z) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS (6.1): the preceding Book 8 interfaces expose the
Cartier line-bundle construction as a profile rather than a canonical named
`𝓞(D)` constructor.  The profile below is the minimal bridge needed to state
the associated line bundle, its canonical section, and its vanishing scheme. -/

theorem chapter06_associated_line_bundle_exists
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Nonempty (Chapter06AssociatedLineBundleProfile D) := by
  sorry

noncomputable def chapter06AssociatedLineBundleProfile
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06AssociatedLineBundleProfile D :=
  Classical.choice (chapter06_associated_line_bundle_exists D)

abbrev chapter06AssociatedLineBundle
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06LineBundle (Chapter06RelativeDivisorAmbient C T) :=
  (chapter06AssociatedLineBundleProfile D).lineBundle

abbrev chapter06AssociatedLineBundleCanonicalSection
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06LineBundleSection (chapter06AssociatedLineBundle D) :=
  (chapter06AssociatedLineBundleProfile D).canonicalSection

theorem chapter06_associated_line_bundle_canonical_section_vanishes_on_divisor
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    (chapter06AssociatedLineBundleProfile D).vanishingIdeal = D.divisor.ideal :=
  (chapter06AssociatedLineBundleProfile D).canonicalSection_vanishingIdeal

theorem chapter06_associated_line_bundle_has_fiberwise_degree
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) (t : T.carrier) :
    Scheme.Hom.finrank (chapter06RelativeDivisorProjection D) t = d :=
  (chapter06AssociatedLineBundleProfile D).fiberwise_degree t

/-!
The following is the affine model of the warning `tx = 0` over `Spec k[t]`.
The fiber profile records the one-point fibers away from `t = 0` and the full
affine-line fiber at `t = 0`; the non-flatness theorem is the obstruction to
using this family as a relative effective divisor.
-/

abbrev chapter06TxZeroBaseRing (k : Type u) [CommRing k] := Polynomial k

abbrev chapter06TxZeroAmbientRing (k : Type u) [CommRing k] :=
  Polynomial (Polynomial k)

def chapter06TxZeroStructureMap (k : Type u) [CommRing k] :
    chapter06TxZeroBaseRing k →+* chapter06TxZeroAmbientRing k :=
  Polynomial.C

def chapter06TxZeroIdeal (k : Type u) [CommRing k] :
    Ideal (chapter06TxZeroAmbientRing k) :=
  Ideal.span ({
    Polynomial.C (Polynomial.X : Polynomial k) *
      (Polynomial.X : Polynomial (Polynomial k))
  } : Set (Polynomial (Polynomial k)))

abbrev chapter06TxZeroTotalRing (k : Type u) [CommRing k] :=
  chapter06TxZeroAmbientRing k ⧸ chapter06TxZeroIdeal k

def chapter06TxZeroQuotientMap (k : Type u) [CommRing k] :
    CommRingCat.of (chapter06TxZeroBaseRing k) ⟶
      CommRingCat.of (chapter06TxZeroTotalRing k) :=
  CommRingCat.ofHom
    ((Ideal.Quotient.mk (chapter06TxZeroIdeal k)).comp
      (chapter06TxZeroStructureMap k))

def chapter06TxZeroBaseScheme (k : Type u) [CommRing k] : Scheme :=
  Spec (.of (chapter06TxZeroBaseRing k))

def chapter06TxZeroTotalScheme (k : Type u) [CommRing k] : Scheme :=
  Spec (.of (chapter06TxZeroTotalRing k))

def chapter06TxZeroFamilyMap (k : Type u) [CommRing k] :
    chapter06TxZeroTotalScheme k ⟶ chapter06TxZeroBaseScheme k :=
  Scheme.Spec.map (chapter06TxZeroQuotientMap k).op

abbrev chapter06TxZeroFiberRing (k : Type u) [Field k] (a : k) :=
  Polynomial k ⧸
    Ideal.span ({Polynomial.C a * (Polynomial.X : Polynomial k)} : Set (Polynomial k))

def chapter06TxZeroFiberIsOnePoint (k : Type u) [Field k] (a : k) : Prop :=
  Nonempty (chapter06TxZeroFiberRing k a ≃ₐ[k] k)

def chapter06TxZeroFiberIsAffineLine (k : Type u) [Field k] : Prop :=
  Nonempty (chapter06TxZeroFiberRing k 0 ≃ₐ[k] Polynomial k)

structure Chapter06TxZeroFiberProfile (k : Type u) [Field k] where
  generic_is_one_point : ∀ a : k, a ≠ 0 → chapter06TxZeroFiberIsOnePoint k a
  special_is_affine_line : chapter06TxZeroFiberIsAffineLine k

theorem chapter06_tx_zero_fiber_profile (k : Type u) [Field k] :
    Nonempty (Chapter06TxZeroFiberProfile k) := by
  sorry

theorem chapter06_tx_zero_family_not_flat (k : Type u) [Field k] :
    ¬ Module.Flat (chapter06TxZeroBaseRing k) (chapter06TxZeroTotalRing k) := by
  sorry

theorem chapter06_tx_zero_family_not_finite_flat_of_constant_rank
    (k : Type u) [Field k] :
    ¬ ∃ d : ℕ, Chapter06FiniteFlatRank (chapter06TxZeroFamilyMap k) d := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
