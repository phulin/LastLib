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
  have hcard : Fintype.card m = Fintype.card k ^ d := by
    rw [Module.card_eq_pow_finrank (K := k) (V := m), hdegree]
  constructor
  · simpa [chapter06ArithmeticFrobeniusRingEquiv] using
      chapter06_arithmetic_frobenius_apply k l x
  · simpa [chapter06ArithmeticFrobeniusRingEquiv, hcard] using
      chapter06_arithmetic_frobenius_apply m l x

/- Relative arithmetic Frobenius is the `d`th power of absolute arithmetic Frobenius. -/
theorem chapter06_arithmetic_frobenius_tower_power_relation
    (k m l : Type*) [Field k] [Fintype k] [Field m] [Fintype m]
    [Field l] [Finite l] [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower k m l] [Algebra.IsAlgebraic k l]
    [Algebra.IsAlgebraic m l] (d : ℕ)
    (hdegree : Module.finrank k m = d) :
    chapter06ArithmeticFrobeniusRingEquiv m l =
      (chapter06ArithmeticFrobeniusRingEquiv k l) ^ d := by
  apply RingEquiv.ext
  intro x
  have hcard : Fintype.card m = Fintype.card k ^ d := by
    rw [Module.card_eq_pow_finrank (K := k) (V := m), hdegree]
  have hpow : ∀ n : ℕ,
      (chapter06ArithmeticFrobeniusRingEquiv k l ^ n) x =
        x ^ (Fintype.card k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', RingAut.mul_apply, ih, map_pow]
        change chapter06ArithmeticFrobenius k l x ^
          (Fintype.card k ^ n) = _
        rw [chapter06_arithmetic_frobenius_apply, ← pow_mul,
          Nat.pow_succ', Nat.mul_comm]
  calc
    chapter06ArithmeticFrobeniusRingEquiv m l x = x ^ Fintype.card m := by
      simpa [chapter06ArithmeticFrobeniusRingEquiv] using
        chapter06_arithmetic_frobenius_apply m l x
    _ = x ^ (Fintype.card k ^ d) := by rw [hcard]
    _ = (chapter06ArithmeticFrobeniusRingEquiv k l ^ d) x :=
      (hpow d).symm

/- The same tower relation holds for geometric Frobenius after inversion. -/
theorem chapter06_geometric_frobenius_tower_power_relation
    (k m l : Type*) [Field k] [Fintype k] [Field m] [Fintype m]
    [Field l] [Finite l] [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower k m l] [Algebra.IsAlgebraic k l]
    [Algebra.IsAlgebraic m l] (d : ℕ)
    (hdegree : Module.finrank k m = d) :
    chapter06GeometricFrobeniusRingEquiv m l =
      (chapter06GeometricFrobeniusRingEquiv k l) ^ d := by
  change (chapter06ArithmeticFrobeniusRingEquiv m l)⁻¹ =
    (chapter06ArithmeticFrobeniusRingEquiv k l)⁻¹ ^ d
  rw [chapter06_arithmetic_frobenius_tower_power_relation k m l d hdegree,
    inv_pow]

/- Inversion preserves the tower power relation for the geometric convention. -/
theorem chapter06_geometric_tower_relation_is_inverse_of_arithmetic
    (k m l : Type*) [Field k] [Fintype k] [Field m] [Fintype m]
    [Field l] [Finite l] [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower k m l] [Algebra.IsAlgebraic k l]
    [Algebra.IsAlgebraic m l] :
    chapter06GeometricFrobeniusRingEquiv m l =
      (chapter06ArithmeticFrobeniusRingEquiv m l)⁻¹ ∧
        chapter06GeometricFrobeniusRingEquiv k l =
          (chapter06ArithmeticFrobeniusRingEquiv k l)⁻¹ := by
  constructor <;> rfl

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
