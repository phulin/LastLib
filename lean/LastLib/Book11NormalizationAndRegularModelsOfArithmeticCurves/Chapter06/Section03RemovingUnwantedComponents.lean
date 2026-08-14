import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u v

/-! ### 6.3 Removing unwanted components -/

theorem chapter06_saturation_quotient_comp_generic_map
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    (chapter06SaturationGenericMap R A).comp
        (chapter06SaturationQuotientMap R A) =
      chapter06GenericFiberRingMap R A := by
  ext a
  exact RingHom.kerLift_mk _ a

theorem chapter06_saturation_generic_map_injective
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Function.Injective (chapter06SaturationGenericMap R A) := by
  exact RingHom.kerLift_injective _

theorem chapter06_saturation_iff_generic_zero
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] (a : A) :
    a ∈ chapter06SaturationIdeal R A ↔
      chapter06GenericFiberRingMap R A a = 0 :=
  Iff.rfl

theorem chapter06_saturated_affine_ring_has_no_generic_zero
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] (a : chapter06SaturatedAffineRing R A) :
    chapter06SaturationGenericMap R A a = 0 ↔ a = 0 := by
  constructor
  · intro h
    apply chapter06_saturation_generic_map_injective R A
    simpa using h
  · intro h
    simpa [h]

theorem chapter06_saturated_affine_ring_is_torsion_free
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Module.IsTorsionFree R (chapter06SaturatedAffineRing R A) := by
  sorry

theorem chapter06_saturated_affine_ring_is_flat
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Module.Flat R (chapter06SaturatedAffineRing R A) := by
  letI : Module.IsTorsionFree R (chapter06SaturatedAffineRing R A) :=
    chapter06_saturated_affine_ring_is_torsion_free R A
  infer_instance

theorem chapter06_dvr_saturation_is_power_torsion
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (a : A) :
    a ∈ chapter06SaturationIdeal R A ↔ chapter06PowerTorsion R A π a := by
  sorry

theorem chapter06_saturation_removes_generic_zero_sections
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Function.Injective (chapter06SaturationGenericMap R A) :=
  chapter06_saturation_generic_map_injective R A

/- A vertical component is one whose pullback to the generic point is empty.
This definition is only used to make the warning in the source precise; the
actual cleanup operation is the kernel quotient above. -/
def chapter06VerticalComponent
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    {X : Scheme.{u}} (f : X ⟶ Chapter06BaseScheme R) : Prop :=
  ∃ Z : Scheme.{u}, ∃ i : Z ⟶ X,
    IsClosedImmersion i ∧
      ¬ Nonempty (pullback (i ≫ f) (chapter06GenericBaseMap R))

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06
