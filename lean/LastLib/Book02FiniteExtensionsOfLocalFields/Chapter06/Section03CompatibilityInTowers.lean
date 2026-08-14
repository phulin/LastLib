import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section01WhyFrobeniusIsCanonical

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
  constructor
  · change chapter06ArithmeticFrobenius k l x = _
    exact chapter06_arithmetic_frobenius_apply k l x
  · change chapter06ArithmeticFrobenius m l x = _
    rw [chapter06_arithmetic_frobenius_apply]
    have hcard : Fintype.card m = Fintype.card k ^ d := by
      calc
        Fintype.card m = Fintype.card k ^ Module.finrank k m :=
          Module.card_eq_pow_finrank (K := k) (V := m)
        _ = Fintype.card k ^ d := by rw [hdegree]
    rw [hcard]

/- Relative arithmetic Frobenius is the `d`th power of absolute arithmetic Frobenius. -/
theorem chapter06_arithmetic_frobenius_tower_power_relation
    (k m l : Type*) [Field k] [Fintype k] [Field m] [Fintype m]
    [Field l] [Finite l] [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower k m l] [Algebra.IsAlgebraic k l]
    [Algebra.IsAlgebraic m l] (d : ℕ)
    (hdegree : Module.finrank k m = d) :
    chapter06ArithmeticFrobeniusRingEquiv m l =
      (chapter06ArithmeticFrobeniusRingEquiv k l) ^ d := by
  ext x
  have h := chapter06_arithmetic_frobenius_tower_power_actions k m l d hdegree x
  rw [h.2]
  have hpow : ∀ n : ℕ,
      (chapter06ArithmeticFrobeniusRingEquiv k l ^ n) x =
        x ^ (Fintype.card k ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        change (chapter06ArithmeticFrobeniusRingEquiv k l ^ n)
          ((chapter06ArithmeticFrobenius k l) x) = _
        rw [chapter06_arithmetic_frobenius_apply k l x, map_pow, ih]
        rw [← pow_mul]
        simp [pow_succ, Nat.mul_comm]
  exact (hpow d).symm

/- The same tower relation holds for geometric Frobenius after inversion. -/
theorem chapter06_geometric_frobenius_tower_power_relation
    (k m l : Type*) [Field k] [Fintype k] [Field m] [Fintype m]
    [Field l] [Finite l] [Algebra k m] [Algebra m l] [Algebra k l]
    [IsScalarTower k m l] [Algebra.IsAlgebraic k l]
    [Algebra.IsAlgebraic m l] (d : ℕ)
    (hdegree : Module.finrank k m = d) :
    chapter06GeometricFrobeniusRingEquiv m l =
      (chapter06GeometricFrobeniusRingEquiv k l) ^ d := by
  have h := chapter06_arithmetic_frobenius_tower_power_relation k m l d hdegree
  change (chapter06ArithmeticFrobenius m l).toRingEquiv =
    ((chapter06ArithmeticFrobenius k l).toRingEquiv) ^ d at h
  have h' := congrArg (fun e : l ≃+* l => e⁻¹) h
  change (chapter06ArithmeticFrobenius m l).toRingEquiv⁻¹ =
    (((chapter06ArithmeticFrobenius k l).toRingEquiv) ^ d)⁻¹ at h'
  rw [← inv_pow] at h'
  change (chapter06ArithmeticFrobenius m l).toRingEquiv⁻¹ =
    ((chapter06ArithmeticFrobenius k l).toRingEquiv⁻¹) ^ d
  exact h'

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
