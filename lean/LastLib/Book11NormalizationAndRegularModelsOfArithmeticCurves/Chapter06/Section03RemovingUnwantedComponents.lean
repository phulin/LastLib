import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u v

/-! ### 6.3 Removing unwanted components -/

theorem chapter06_saturation_quotient_comp_generic_map
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    (chapter06SaturationGenericMap R A).comp
        (chapter06SaturationQuotientMap R A) =
      chapter06GenericFiberRingMap R A := by
  ext a
  change RingHom.kerLift (chapter06GenericFiberRingMap R A)
      (Ideal.Quotient.mk _ a) = _
  exact RingHom.kerLift_mk (chapter06GenericFiberRingMap R A) a

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
  · rintro rfl
    simp

theorem chapter06_saturated_affine_ring_is_torsion_free
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Module.IsTorsionFree R (chapter06SaturatedAffineRing R A) := by
  let := Algebra.TensorProduct.rightAlgebra (R := R) (A := A)
    (B := FractionRing R)
  have hK : Module.IsTorsionFree (FractionRing R)
      (chapter06GenericFiberRing R A) := by infer_instance
  have hgeneric : Module.IsTorsionFree R
      (chapter06GenericFiberRing R A) :=
    hK.comap (algebraMap R (FractionRing R)) (by
      intro r hr
      apply IsRegular.of_ne_zero
      intro h
      apply IsRegular.ne_zero hr
      exact (IsFractionRing.injective R (FractionRing R)) (by simpa using h)) (by
      intro r x
      exact IsScalarTower.algebraMap_smul (A := FractionRing R) r x)
  exact @Function.Injective.moduleIsTorsionFree R
    (chapter06SaturatedAffineRing R A)
    (chapter06GenericFiberRing R A)
    _ _ _ _ _ hgeneric
    (chapter06SaturationGenericMap R A)
    (chapter06_saturation_generic_map_injective R A) (by
      intro r x
      have hscalar :
          (chapter06SaturationGenericMap R A).comp
              (algebraMap R (chapter06SaturatedAffineRing R A)) =
            algebraMap R (chapter06GenericFiberRing R A) := by
        ext r
        change chapter06SaturationGenericMap R A
            (chapter06SaturationQuotientMap R A (algebraMap R A r)) =
          algebraMap R (chapter06GenericFiberRing R A) r
        calc
          _ = (chapter06SaturationGenericMap R A).comp
              (chapter06SaturationQuotientMap R A) (algebraMap R A r) := by rfl
          _ = chapter06GenericFiberRingMap R A (algebraMap R A r) := by
            rw [chapter06_saturation_quotient_comp_generic_map R A]
          _ = algebraMap R (chapter06GenericFiberRing R A) r := by
            change Algebra.TensorProduct.includeLeft (algebraMap R A r) =
              algebraMap R (chapter06GenericFiberRing R A) r
            rw [IsScalarTower.algebraMap_apply R (FractionRing R)
              (chapter06GenericFiberRing R A) r]
            exact congrArg (fun f : R →+* chapter06GenericFiberRing R A => f r)
              Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      have hs := congrArg (fun f : R →+* chapter06GenericFiberRing R A => f r) hscalar
      have hs' : chapter06SaturationGenericMap R A
          (algebraMap R (chapter06SaturatedAffineRing R A) r) =
            algebraMap R (chapter06GenericFiberRing R A) r := by
        simpa only [RingHom.coe_comp, Function.comp_apply] using hs
      rw [Algebra.smul_def, map_mul, hs']
      exact (Algebra.smul_def r
        (chapter06SaturationGenericMap R A x)).symm)

theorem chapter06_saturated_affine_ring_is_flat
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Module.Flat R (chapter06SaturatedAffineRing R A) := by
  let : Module.IsTorsionFree R
      (chapter06SaturatedAffineRing R A) :=
    chapter06_saturated_affine_ring_is_torsion_free R A
  exact (inferInstance : Module.Flat R
    (chapter06SaturatedAffineRing R A))

theorem chapter06_dvr_saturation_is_power_torsion
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] [IsDiscreteValuationRing R]
    (π : R) (hπ : Irreducible π) (a : A) :
    a ∈ chapter06SaturationIdeal R A ↔ chapter06PowerTorsion R A π a := by
  have hpowloc : IsLocalization (Submonoid.powers π) (FractionRing R) := by
    refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
    · rintro ⟨n, hn⟩
      rcases (Submonoid.mem_powers_iff n π).mp hn with ⟨k, rfl⟩
      exact Ne.isUnit (by
        rw [map_pow]
        exact pow_ne_zero _ (by simpa using hπ.ne_zero))
    · intro z
      obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective R z
      obtain ⟨n, u, hu⟩ :=
        IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
          (x := y) (by simpa using hy) hπ
      let d : Submonoid.powers π := ⟨π ^ n, ⟨n, rfl⟩⟩
      refine ⟨(x * (↑(u⁻¹) : R), d), ?_⟩
      change z * algebraMap R (FractionRing R) (π ^ n) =
        algebraMap R (FractionRing R) (x * (↑(u⁻¹) : R))
      rw [← hxy, hu, map_mul, map_mul]
      simp only [map_pow]
      have hπK : algebraMap R (FractionRing R) π ≠ 0 := by
        simpa using hπ.ne_zero
      field_simp
      simp
    · intro x y hxy
      refine ⟨⟨1, by simp⟩, ?_⟩
      have hxy' : x = y := IsFractionRing.injective R (FractionRing R) hxy
      simp [hxy']
  let : IsLocalization (Submonoid.powers π) (FractionRing R) := hpowloc
  let : Algebra (A ⊗[R] R) (A ⊗[R] FractionRing R) :=
    (Algebra.TensorProduct.map (AlgHom.id R A)
      (IsScalarTower.toAlgHom R R (FractionRing R))).toAlgebra
  have : IsScalarTower A (A ⊗[R] R) (A ⊗[R] FractionRing R) :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := A ⊗[R] R)
      (A := A ⊗[R] FractionRing R) (by
        intro x
        simp [RingHom.algebraMap_toAlgebra])
  have hloc :
      IsLocalization
        ((Submonoid.powers π).map
          (Algebra.TensorProduct.includeRight (R := R) (A := A)))
        (A ⊗[R] FractionRing R) :=
    IsLocalization.tensorProduct_tensorProduct_right R A
      (Submonoid.powers π) (FractionRing R)
      (by
        ext x
        simpa [RingHom.coe_comp, Function.comp_apply,
          RingHom.algebraMap_toAlgebra] using
          (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R)
            (A := A) (B := FractionRing R) x).symm)
  have hgeneric (x : A) :
      algebraMap (A ⊗[R] R) (A ⊗[R] FractionRing R)
          ((Algebra.TensorProduct.rid R A A).symm x) =
        chapter06GenericFiberRingMap R A x := by
    change algebraMap (A ⊗[R] R) (A ⊗[R] FractionRing R)
          ((Algebra.TensorProduct.rid R A A).symm x) =
        Algebra.TensorProduct.includeLeft x
    simp [RingHom.algebraMap_toAlgebra]
  let : IsLocalization
      ((Submonoid.powers π).map
        (Algebra.TensorProduct.includeRight (R := R) (A := A)))
      (A ⊗[R] FractionRing R) := hloc
  have hzero :
      chapter06GenericFiberRingMap R A a = 0 ↔
        ∃ m : (Submonoid.powers π).map
            (Algebra.TensorProduct.includeRight (R := R) (A := A)),
          (m : A ⊗[R] R) *
              (Algebra.TensorProduct.rid R A A).symm a = 0 := by
    rw [← hgeneric a]
    exact IsLocalization.map_eq_zero_iff _ _ _
  rw [chapter06_saturation_iff_generic_zero, hzero]
  constructor
  · rintro ⟨m, hm⟩
    rcases m with ⟨m, hm_mem⟩
    obtain ⟨p, hp, hpm⟩ := hm_mem
    obtain ⟨n, hpn⟩ := (Submonoid.mem_powers_iff p π).mp hp
    refine ⟨n, ?_⟩
    change m * (Algebra.TensorProduct.rid R A A).symm a = 0 at hm
    rw [← hpm, ← hpn] at hm
    have hm' := congrArg (Algebra.TensorProduct.rid R A A) hm
    simpa [Algebra.smul_def] using hm'
  · rintro ⟨n, hn⟩
    refine ⟨⟨Algebra.TensorProduct.includeRight (π ^ n),
      ⟨π ^ n, ⟨n, rfl⟩, rfl⟩⟩, ?_⟩
    apply (Algebra.TensorProduct.rid R A A).injective
    simpa [Algebra.smul_def] using hn

theorem chapter06_saturation_removes_generic_zero_sections
    (R A : Type u) [CommRing R] [IsDedekindDomain R]
    [CommRing A] [Algebra R A] :
    Function.Injective (chapter06SaturationGenericMap R A) :=
  chapter06_saturation_generic_map_injective R A

/- A vertical closed subscheme is one whose pullback to the generic point is
empty.  The closed subscheme is an explicit argument, so the predicate classifies
the chosen immersion rather than merely asserting that some vertical subscheme
exists.  It deliberately does not claim irreducibility or maximality; the actual
cleanup operation is the kernel quotient above. -/
def chapter06VerticalClosedSubscheme
    (R : Type u) [CommRing R] [IsDedekindDomain R]
    {X Z : Scheme.{u}} (f : X ⟶ Chapter06BaseScheme R) (i : Z ⟶ X) : Prop :=
  Nonempty Z ∧ IsClosedImmersion i ∧
    ¬ Nonempty (pullback (C := Scheme) (i ≫ f) (chapter06GenericBaseMap R))

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter06
