import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

/-! ### 11.1 The theorem and its meaning -/

/-- The dimension of the space of sections of the line bundle associated to a
divisor. -/
noncomputable def chapter11Ell {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    (D : Chapter11Divisor C.carrier) : ℕ :=
  chapter11CohomologyFinrank (f := C.structureMap) D.lineBundle.module 0

/-- The Euler-characteristic form of Riemann--Roch. -/
def Chapter11RiemannRochEulerForm {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    (L : Chapter11LineBundle C.carrier) : Prop :=
  chapter11EulerCharacteristicOfLineBundle C L =
    chapter11Degree L + 1 - (C.genus : ℤ)

/-- The divisor form of Riemann--Roch, with the canonical divisor chosen. -/
def Chapter11RiemannRochDivisorForm {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (K : Chapter11CanonicalDivisor C)
    (D : Chapter11Divisor C.carrier) : Prop :=
  (chapter11Ell C D : ℤ) -
      (chapter11Ell C (chapter11DivisorSub K.divisor D) : ℤ) =
    D.degree + 1 - (C.genus : ℤ)

/-- Riemann--Roch in Euler-characteristic form (11.1). -/
theorem chapter11_riemann_roch_euler_characteristic
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11DivisorRepresentationTheory C]
    [Chapter11EffectiveDecompositionTheory C]
    [Chapter11EffectiveCartierTwistSequenceTheory C]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C]
    (L : Chapter11LineBundle C.carrier) :
    chapter11EulerCharacteristicOfLineBundle C L =
      chapter11Degree L + 1 - (C.genus : ℤ) := by
  sorry

/-- The `h⁰-h¹` spelling of the Euler characteristic. -/
theorem chapter11_euler_characteristic_eq_h0_sub_h1
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) :
    chapter11EulerCharacteristicOfLineBundle C L =
      (chapter11H0Finrank C L : ℤ) - chapter11H1Finrank C L := by
  rfl

/-- The speciality correction term is the dimension of `H¹`. -/
noncomputable def chapter11Speciality {k : Type u} [Field k]
    (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) : ℕ :=
  chapter11H1Finrank C L

theorem chapter11_euler_characteristic_eq_h0_sub_speciality
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) :
    chapter11EulerCharacteristicOfLineBundle C L =
      (chapter11H0Finrank C L : ℤ) - chapter11Speciality C L := by
  rfl

/-- Serre duality converts the first cohomology dimension into the dimension
of the dual-twisted global-section space.  The duality class is supplied by
the later duality chapter through the local dependency interface. -/
theorem chapter11_serre_duality_h1_finrank
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11SerreDualityTheory C] (L : Chapter11LineBundle C.carrier) :
    chapter11H1Finrank C L =
      chapter11H0Finrank C
        (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
          (chapter11Dual L)) := by
  sorry

/-- With a chosen canonical divisor, the divisor and Euler forms are
equivalent after the duality identification of `H¹` with `ℓ(K-D)`. -/
theorem chapter11_riemann_roch_forms_iff
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11DegreeTheory C.carrier]
    [Chapter11CohomologyIsomorphismTheory C.carrier C.structureMap]
    [Chapter11SerreDualityTheory C] (K : Chapter11CanonicalDivisor C)
    (D : Chapter11Divisor C.carrier) :
    Chapter11RiemannRochEulerForm C D.lineBundle ↔
      Chapter11RiemannRochDivisorForm C K D := by
  sorry

/-- Riemann--Roch in divisor notation (11.2). -/
theorem chapter11_riemann_roch_divisor
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11DegreeTheory C.carrier]
    [Chapter11DivisorRepresentationTheory C]
    [Chapter11EffectiveDecompositionTheory C]
    [Chapter11EffectiveCartierTwistSequenceTheory C]
    [Chapter11CohomologyIsomorphismTheory C.carrier C.structureMap]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C]
    [Chapter11SerreDualityTheory C] (K : Chapter11CanonicalDivisor C)
    (D : Chapter11Divisor C.carrier) :
    (chapter11Ell C D : ℤ) -
        (chapter11Ell C (chapter11DivisorSub K.divisor D) : ℤ) =
      D.degree + 1 - (C.genus : ℤ) := by
  sorry

/-- The duality correction vanishes in the nonspecial range. -/
theorem chapter11_h1_vanishes_of_degree_gt_two_genus_sub_two
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11DegreeTheory C.carrier]
    [Chapter11SerreDualityTheory C]
    (L : Chapter11LineBundle C.carrier)
    (hcanonicalDegree :
      chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) =
        2 * (C.genus : ℤ) - 2)
    (hnegative : ∀ M : Chapter11LineBundle C.carrier,
      chapter11Degree M < 0 → chapter11H0Finrank C M = 0)
    (hdegree : 2 * (C.genus : ℤ) - 2 < chapter11Degree L) :
    chapter11H1Finrank C L = 0 := by
  sorry

/-- In degree greater than `2g-2`, the naive section count is exact. -/
theorem chapter11_h0_eq_degree_plus_one_sub_genus_of_high_degree
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11DegreeTheory C.carrier]
    [Chapter11DivisorRepresentationTheory C]
    [Chapter11EffectiveDecompositionTheory C]
    [Chapter11EffectiveCartierTwistSequenceTheory C]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C]
    [Chapter11SerreDualityTheory C]
    (L : Chapter11LineBundle C.carrier)
    (hcanonicalDegree :
      chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) =
        2 * (C.genus : ℤ) - 2)
    (hnegative : ∀ M : Chapter11LineBundle C.carrier,
      chapter11Degree M < 0 → chapter11H0Finrank C M = 0)
    (hdegree : 2 * (C.genus : ℤ) - 2 < chapter11Degree L) :
    (chapter11H0Finrank C L : ℤ) = chapter11Degree L + 1 - (C.genus : ℤ) := by
  sorry

/-- The Euler-characteristic form remains valid for a proper Gorenstein curve.
The cohomology and degree interfaces are taken over its structural map. -/
theorem chapter11_riemann_roch_euler_characteristic_gorenstein
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11GorensteinDegreeTheory C]
    [Chapter11GorensteinEulerCharacteristicTheory C]
    (L : Chapter11LineBundle C.carrier) :
    chapter11EulerCharacteristic (f := C.structureMap) L.module =
      chapter11Degree L + 1 - (C.arithmeticGenus : ℤ) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
