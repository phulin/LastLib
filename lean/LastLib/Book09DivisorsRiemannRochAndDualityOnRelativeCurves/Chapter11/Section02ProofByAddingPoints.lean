import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-! ### 11.2 Proof by adding points -/

/-- Additivity of Euler characteristic for the Cartier sequence
`0 → 𝒪_X → 𝒪_X(D) → 𝒪_D(D) → 0`. -/
theorem chapter11_effective_cartier_euler_difference
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    (D : Chapter11EffectiveCartierDivisor C) :
    chapter11EulerCharacteristicOfLineBundle C D.divisor.lineBundle -
        chapter11EulerCharacteristic (f := C.structureMap)
          (chapter11StructureSheafLineBundle C.carrier).module =
      chapter11EulerCharacteristic (f := C.structureMap) D.cartier.quotient := by
  sorry

/-- The quotient in the Cartier sequence is a finite-length sheaf, so its
Euler characteristic is its field dimension and hence the degree of `D`. -/
theorem chapter11_effective_cartier_quotient_euler_eq_degree
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (D : Chapter11EffectiveCartierDivisor C) :
    chapter11EulerCharacteristic (f := C.structureMap) D.cartier.quotient =
      (D.divisor.degree : ℤ) := by
  sorry

/-- The effective point calculation. -/
theorem chapter11_effective_cartier_euler_characteristic_difference
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    (D : Chapter11EffectiveCartierDivisor C) :
    chapter11EulerCharacteristicOfLineBundle C D.divisor.lineBundle -
        chapter11EulerCharacteristic (f := C.structureMap)
          (chapter11StructureSheafLineBundle C.carrier).module =
      (D.divisor.degree : ℤ) := by
  sorry

/-- Every divisor on the smooth proper curve has a disjoint effective
decomposition. -/
theorem chapter11_divisor_has_effective_decomposition
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11EffectiveDecompositionTheory C]
    (D : Chapter11Divisor C.carrier) :
    Nonempty (Chapter11EffectiveDecomposition C D) :=
  Chapter11EffectiveDecompositionTheory.every_divisor_has_effective_decomposition D

/-- Euler characteristic is additive after subtracting the negative effective
part. -/
theorem chapter11_euler_characteristic_of_divisor_decomposition
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11EffectiveCartierTwistSequenceTheory C]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    (D : Chapter11Divisor C.carrier)
    (hD : Chapter11EffectiveDecomposition C D) :
    chapter11EulerCharacteristicOfLineBundle C D.lineBundle =
      D.degree +
        chapter11EulerCharacteristic (f := C.structureMap)
          (chapter11StructureSheafLineBundle C.carrier).module := by
  sorry

/-- The structure sheaf has Euler characteristic `1-g`. -/
theorem chapter11_euler_characteristic_structure_sheaf
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C] :
    chapter11EulerCharacteristic (f := C.structureMap)
        (chapter11StructureSheafLineBundle C.carrier).module =
      1 - (C.genus : ℤ) := by
  sorry

/-- The general divisor calculation, in the form used to finish the proof of
the Euler-characteristic theorem. -/
theorem chapter11_euler_characteristic_of_divisor
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11EffectiveDecompositionTheory C]
    [Chapter11EffectiveCartierTwistSequenceTheory C]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    [Chapter11ConnectedGlobalSections C]
    (D : Chapter11Divisor C.carrier) :
    chapter11EulerCharacteristicOfLineBundle C D.lineBundle =
      D.degree + 1 - (C.genus : ℤ) := by
  sorry

theorem chapter11_smooth_curve_every_line_bundle_has_divisor_representation
    {k : Type u} [Field k] (C : Chapter11CurveOverField k)
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11DivisorRepresentationTheory C]
    (L : Chapter11LineBundle C.carrier) :
    Chapter11LineBundleDivisorRepresentation C L :=
  Chapter11DivisorRepresentationTheory.every_line_bundle_has_divisor_representation L

/-- Degree defined by the Euler characteristic, the definition available for
the singular Gorenstein proof. -/
noncomputable def chapter11EulerDefinedDegree
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [Chapter11CohomologyTheory X f]
    (L : Chapter11LineBundle X) : ℤ :=
  chapter11EulerCharacteristic (f := f) L.module -
    chapter11EulerCharacteristic (f := f)
      (chapter11StructureSheafLineBundle X).module

theorem chapter11_euler_defined_degree_reconstructs_euler_characteristic
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    [Chapter11CohomologyTheory X f]
    (L : Chapter11LineBundle X) :
    chapter11EulerCharacteristic (f := f) L.module =
    chapter11EulerDefinedDegree f L +
        chapter11EulerCharacteristic (f := f)
          (chapter11StructureSheafLineBundle X).module := by
  simp [chapter11EulerDefinedDegree, sub_add_cancel]

/-- In a Gorenstein curve, the Euler-defined degree gives the same numerical
Riemann--Roch identity once `χ(𝒪_C)=1-g` is supplied. -/
theorem chapter11_gorenstein_euler_defined_degree_rr
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier)
    (hchi : chapter11EulerCharacteristic (f := C.structureMap)
        (chapter11StructureSheafLineBundle C.carrier).module =
      1 - (C.arithmeticGenus : ℤ)) :
    chapter11EulerCharacteristic (f := C.structureMap) L.module =
      chapter11EulerDefinedDegree C.structureMap L +
        1 - (C.arithmeticGenus : ℤ) := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
