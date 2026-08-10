import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section02FrobeniusInAnUnramifiedExtension

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

noncomputable section

open scoped BigOperators

/-! ## 6.3. Compatibility in towers -/

/- Arithmetic Frobenius acts by `q`-power on every residue extension in a tower. -/
theorem chapter06_arithmetic_frobenius_tower_power_actions
    (k m l : Type*) [Field k] [Fintype k] [Field m] [Fintype m]
    [Field l] [Finite l] [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower k m l] [Algebra.IsAlgebraic k l]
    [Algebra.IsAlgebraic m l] (d : ℕ)
    (hdegree : Module.finrank k m = d) (x : l) :
    chapter06ArithmeticFrobeniusRingEquiv k l x = x ^ Fintype.card k ∧
      chapter06ArithmeticFrobeniusRingEquiv m l x =
        x ^ (Fintype.card k ^ d) := by
  sorry

/- Relative arithmetic Frobenius is the `d`th power of absolute arithmetic Frobenius. -/
theorem chapter06_arithmetic_frobenius_tower_power_relation
    (k m l : Type*) [Field k] [Fintype k] [Field m] [Fintype m]
    [Field l] [Finite l] [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower k m l] [Algebra.IsAlgebraic k l]
    [Algebra.IsAlgebraic m l] (d : ℕ)
    (hdegree : Module.finrank k m = d) :
    chapter06ArithmeticFrobeniusRingEquiv m l =
      (chapter06ArithmeticFrobeniusRingEquiv k l) ^ d := by
  sorry

/- The same tower relation holds for geometric Frobenius after inversion. -/
theorem chapter06_geometric_frobenius_tower_power_relation
    (k m l : Type*) [Field k] [Fintype k] [Field m] [Fintype m]
    [Field l] [Finite l] [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower k m l] [Algebra.IsAlgebraic k l]
    [Algebra.IsAlgebraic m l] (d : ℕ)
    (hdegree : Module.finrank k m = d) :
    chapter06GeometricFrobeniusRingEquiv m l =
      (chapter06GeometricFrobeniusRingEquiv k l) ^ d := by
  sorry

/- Inversion preserves the tower power relation for the geometric convention. -/
theorem chapter06_geometric_tower_relation_is_inverse_of_arithmetic
    (k m l : Type*) [Field k] [Fintype k] [Field m] [Fintype m]
    [Field l] [Finite l] [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower k m l] [Algebra.IsAlgebraic k l]
    [Algebra.IsAlgebraic m l] (d : ℕ)
    (hdegree : Module.finrank k m = d) :
    chapter06GeometricFrobeniusRingEquiv m l =
      (chapter06ArithmeticFrobeniusRingEquiv m l)⁻¹ ∧
        chapter06GeometricFrobeniusRingEquiv k l =
          (chapter06ArithmeticFrobeniusRingEquiv k l)⁻¹ := by
  constructor <;> rfl

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
