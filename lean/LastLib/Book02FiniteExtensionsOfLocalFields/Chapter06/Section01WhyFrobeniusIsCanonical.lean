import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Galois.Basic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

noncomputable section

open Set
open scoped BigOperators Polynomial

/-! ## 6.1. Why Frobenius is canonical -/

/-
The finite-field Frobenius used below is Mathlib's canonical algebraic
Frobenius.  The hypotheses deliberately retain the finite-field structure and
do not assume characteristic zero.
-/

/- The arithmetic Frobenius of a finite algebraic field extension. -/
noncomputable def chapter06ArithmeticFrobenius
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : Gal(l/k) :=
  FiniteField.frobeniusAlgEquivOfAlgebraic k l

/- The geometric Frobenius, namely the inverse of arithmetic Frobenius. -/
noncomputable def chapter06GeometricFrobenius
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : Gal(l/k) :=
  (chapter06ArithmeticFrobenius k l)⁻¹

/- The underlying ring automorphism of arithmetic Frobenius. -/
noncomputable def chapter06ArithmeticFrobeniusRingEquiv
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : l ≃+* l :=
  (chapter06ArithmeticFrobenius k l).toRingEquiv

/- The underlying ring automorphism of geometric Frobenius. -/
noncomputable def chapter06GeometricFrobeniusRingEquiv
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : l ≃+* l :=
  (chapter06GeometricFrobenius k l).toRingEquiv

/- The fixed-point set of arithmetic Frobenius. -/
def chapter06FrobeniusFixedPoints
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] : Set l :=
  {x | chapter06ArithmeticFrobenius k l x = x}

/- Arithmetic Frobenius is the power map `x ↦ x^q`. -/
theorem chapter06_arithmetic_frobenius_apply
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] (x : l) :
    chapter06ArithmeticFrobenius k l x = x ^ Fintype.card k := by
  simpa [chapter06ArithmeticFrobenius] using
    congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic k l) x

/- Arithmetic Frobenius fixes the base field pointwise. -/
theorem chapter06_arithmetic_frobenius_fixes_base
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] (a : k) :
    chapter06ArithmeticFrobenius k l (algebraMap k l a) = algebraMap k l a := by
  exact (chapter06ArithmeticFrobenius k l).commutes a

/- For `l = 𝔽_(q^f)`, the fixed field of Frobenius is the copy of `𝔽_q`. -/
theorem chapter06_frobenius_fixed_points_eq_base_image
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] :
    chapter06FrobeniusFixedPoints k l = Set.range (algebraMap k l) := by
  ext x
  change chapter06ArithmeticFrobenius k l x = x ↔
    x ∈ Set.range (algebraMap k l)
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed (F := k) (E := l) x).2
    intro σ
    obtain ⟨i, hi⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l).2 σ
    change chapter06ArithmeticFrobenius k l ^ i.1 = σ at hi
    have hpow : ∀ n : ℕ,
        (chapter06ArithmeticFrobenius k l ^ n) x = x := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ', AlgEquiv.mul_apply, ih, hx]
    rw [← hi, hpow]
  · rintro ⟨a, rfl⟩
    exact chapter06_arithmetic_frobenius_fixes_base k l a

/- The arithmetic Frobenius has order equal to the finite-field degree. -/
theorem chapter06_arithmetic_frobenius_order
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] (f : ℕ)
    (hdegree : Module.finrank k l = f) :
    orderOf (chapter06ArithmeticFrobenius k l) = f := by
  simpa [chapter06ArithmeticFrobenius, hdegree] using
    (FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k l)

/- Every automorphism of `𝔽_(q^f)/𝔽_q` is an integral power of arithmetic Frobenius. -/
theorem chapter06_arithmetic_frobenius_generates
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] (σ : Gal(l/k)) :
    ∃ n : ℤ, (chapter06ArithmeticFrobenius k l) ^ n = σ := by
  obtain ⟨i, hi⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k l).2 σ
  refine ⟨i.1, ?_⟩
  simpa [chapter06ArithmeticFrobenius] using hi

/- Geometric Frobenius is the inverse convention. -/
theorem chapter06_geometric_frobenius_is_inverse
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] :
    chapter06GeometricFrobenius k l = (chapter06ArithmeticFrobenius k l)⁻¹ := by
  simp [chapter06GeometricFrobenius]

/- The explicit geometric-Frobenius formula on `𝔽_(q^f)`. -/
theorem chapter06_geometric_frobenius_apply
    (k l : Type*) [Field k] [Fintype k] [Field l] [Finite l]
    [Algebra k l] [Algebra.IsAlgebraic k l] (f : ℕ)
    (hdegree : Module.finrank k l = f) (hf : 0 < f) (x : l) :
    chapter06GeometricFrobenius k l x =
      x ^ (Fintype.card k ^ (f - 1)) := by
  let F : Gal(l / k) := chapter06ArithmeticFrobenius k l
  have hFpow : F ^ f = 1 := by
    rw [← chapter06_arithmetic_frobenius_order k l f hdegree]
    exact pow_orderOf_eq_one F
  have hmul : F ^ (f - 1) * F = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hf), hFpow]
  have hinv : F⁻¹ = F ^ (f - 1) := inv_eq_of_mul_eq_one_left hmul
  change F⁻¹ x = _
  rw [hinv]
  simp [F, chapter06ArithmeticFrobenius, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
