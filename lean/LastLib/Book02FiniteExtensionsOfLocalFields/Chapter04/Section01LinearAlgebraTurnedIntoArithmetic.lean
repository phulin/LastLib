import Mathlib
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter11
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04

noncomputable section

open scoped BigOperators Polynomial

/-! ## 4.1. Linear algebra turned into arithmetic -/

/-
The multiplication operator in §4.1.  The canonical Mathlib operator
`Algebra.lmul` is used rather than introducing a second multiplication map.
-/
theorem chapter04_multiplication_is_linear
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x y : L) :
    (Algebra.lmul K L x) y = x * y := by
  rfl

/- The trace is the linear-algebra trace of multiplication (§4.1). -/
theorem chapter04_trace_is_trace_of_multiplication
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.trace K L x = LinearMap.trace K L (Algebra.lmul K L x) := by
  rfl

/- The norm is the determinant of multiplication (§4.1). -/
theorem chapter04_norm_is_determinant_of_multiplication
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.norm K x = LinearMap.det (Algebra.lmul K L x) := by
  rfl

/- Additivity of trace for every finite field extension (§4.1). -/
theorem chapter04_trace_add
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x y : L) :
    Algebra.trace K L (x + y) = Algebra.trace K L x + Algebra.trace K L y := by
  exact (Algebra.trace K L).map_add x y

/- Multiplicativity of norm for every finite field extension (§4.1). -/
theorem chapter04_norm_mul
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x y : L) :
    Algebra.norm K (x * y) = Algebra.norm K x * Algebra.norm K y := by
  exact (Algebra.norm K).map_mul x y

/- The norm detects zero in a finite extension of fields (§4.1). -/
theorem chapter04_norm_eq_zero_iff
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (x : L) :
    Algebra.norm K x = 0 ↔ x = 0 := by
  exact Algebra.norm_eq_zero_iff

/-
In a separable extension, trace is the sum over all embeddings into a normal
overfield (§4.1).  The extra `L`-algebra structure on `Ω` records that `Ω`
contains the chosen copy of `L`; the formula itself uses the canonical
`K`-algebra embedding type.
-/
theorem chapter04_trace_eq_sum_embeddings
    (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [Normal K Ω] (x : L) :
    algebraMap K Ω (Algebra.trace K L x) =
      ∑ σ : L →ₐ[K] Ω, σ x := by
  let C := AlgebraicClosure Ω
  have hsplit : ∀ y : L,
      ((minpoly K y).map (algebraMap K Ω)).Splits := by
    intro y
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom K L Ω)
      (IsScalarTower.toAlgHom K L Ω).injective]
    exact Normal.splits (inferInstance : Normal K Ω) (algebraMap L Ω y)
  let e : (L →ₐ[K] Ω) ≃ (L →ₐ[K] C) :=
    Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits C Ω hsplit
  apply (IsScalarTower.toAlgHom K Ω C).injective
  rw [map_sum]
  change algebraMap Ω C (algebraMap K Ω (Algebra.trace K L x)) =
    ∑ σ : L →ₐ[K] Ω, algebraMap Ω C (σ x)
  rw [← IsScalarTower.algebraMap_apply K Ω C]
  rw [trace_eq_sum_embeddings C (x := x)]
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply C Ω hsplit σ x]

/- The corresponding product-over-embeddings formula for norm (§4.1). -/
theorem chapter04_norm_eq_prod_embeddings
    (K L Ω : Type*) [Field K] [Field L] [Field Ω] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] [Algebra K Ω]
    [Algebra L Ω] [IsScalarTower K L Ω] [Normal K Ω] (x : L) :
    algebraMap K Ω (Algebra.norm K x) =
      ∏ σ : L →ₐ[K] Ω, σ x := by
  let C := AlgebraicClosure Ω
  have hsplit : ∀ y : L,
      ((minpoly K y).map (algebraMap K Ω)).Splits := by
    intro y
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom K L Ω)
      (IsScalarTower.toAlgHom K L Ω).injective]
    exact Normal.splits (inferInstance : Normal K Ω) (algebraMap L Ω y)
  let e : (L →ₐ[K] Ω) ≃ (L →ₐ[K] C) :=
    Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits C Ω hsplit
  apply (IsScalarTower.toAlgHom K Ω C).injective
  rw [map_prod]
  change algebraMap Ω C (algebraMap K Ω (Algebra.norm K x)) =
    ∏ σ : L →ₐ[K] Ω, algebraMap Ω C (σ x)
  rw [← IsScalarTower.algebraMap_apply K Ω C]
  rw [Algebra.norm_eq_prod_embeddings K C x]
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro σ hσ
  rw [Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply C Ω hsplit σ x]

/-
The trace vanishes on a nontrivial finite purely inseparable extension
(§4.1).  The degree hypothesis excludes the trivial extension.
-/
theorem chapter04_purely_inseparable_trace_eq_zero
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    (hdegree : 1 < Module.finrank K L) :
    ∀ x : L, Algebra.trace K L x = 0 := by
  have hnot : ¬Algebra.IsSeparable K L := by
    intro hsep
    letI : Algebra.IsSeparable K L := hsep
    have hfin : Field.finSepDegree K L = Module.finrank K L :=
      Field.finSepDegree_eq_finrank_of_isSeparable K L
    have hone := IsPurelyInseparable.finSepDegree_eq_one K L
    have hdegree' := hdegree
    rw [← hfin, hone] at hdegree'
    omega
  intro x
  exact congrArg (fun f : L →ₗ[K] K => f x)
    (Algebra.trace_eq_zero_of_not_isSeparable hnot)

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04
