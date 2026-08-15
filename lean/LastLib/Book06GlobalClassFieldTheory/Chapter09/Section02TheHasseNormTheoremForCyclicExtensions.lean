import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section03FourKindsOfNormAssertion
import LastLib.Book06GlobalClassFieldTheory.Chapter09.Section01TheKnotBetweenLocalAndGlobalNorms

namespace LastLib.Book06GlobalClassFieldTheory.Chapter09

noncomputable section

universe uK uL uV uKV uAV

/-!
At a split place the local algebra is a finite product.  The product norm is
recorded by an equivalence of multiplicative monoids together with the factor
norm; this keeps the construction independent of a particular completion
implementation.
-/
structure Chapter09SplitPlaceNormData
    (V : Type uV) (K_v : V → Type uKV) (A_v : V → Type uAV)
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)] where
  splitPlace : V → Prop
  factorCount : V → ℕ
  factorCount_pos : ∀ v, splitPlace v → 0 < factorCount v
  factor : ∀ v, Fin (factorCount v) → Type (max uKV uAV)
  [factorMonoid : ∀ v i, Monoid (factor v i)]
  productEquiv : ∀ v, splitPlace v →
    (A_v v) ≃* (∀ i, factor v i)
  factorNorm : ∀ v, (∀ i, factor v i)ˣ →* (K_v v)ˣ
  localNorm : ∀ v, (A_v v)ˣ →* (K_v v)ˣ
  localNorm_eq_product : ∀ v (h : splitPlace v),
    localNorm v =
      (factorNorm v).comp (Units.map (productEquiv v h).toMonoidHom)

attribute [instance] Chapter09SplitPlaceNormData.factorMonoid

theorem chapter09_split_place_local_norm_is_product
    {V : Type*} {K_v A_v : V → Type*}
    [∀ v, Monoid (K_v v)] [∀ v, Monoid (A_v v)]
    (P : Chapter09SplitPlaceNormData V K_v A_v)
    (v : V) (h : P.splitPlace v) :
    P.localNorm v =
      (P.factorNorm v).comp (Units.map (P.productEquiv v h).toMonoidHom) :=
  P.localNorm_eq_product v h

/-!
Mathlib currently supplies the category of central simple algebras but not the
cyclic-algebra construction or the number-field Brauer invariant sequence.  We
retain the split predicate as a book-facing definition, while the actual Hasse
norm theorem below is stated through the canonical element/local-norm interface
from Chapter 1.  In particular, no arbitrary local predicate or arbitrary CSA
construction is allowed to masquerade as the cyclic-algebra theorem.
-/
def chapter09CsaIsSplit {K : Type uK} [Field K] (A : CSA.{uK, uK} K) : Prop :=
  ∃ n : ℕ, n ≠ 0 ∧ Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K)

/-!
Chapter 1 exposes the canonical local tensor algebra and the unconditional
cyclic Hasse-norm principle.  The theorem below is therefore the element-level
statement used by this chapter; it does not quantify over guessed local fields,
split predicates, or a guessed cyclic-algebra construction.
-/
abbrev chapter09CanonicalLocalScalarExtensionAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K) :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.LocalScalarExtensionAt K L v

def chapter09CanonicalLocalElementNormAt
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K)
    (y : chapter09CanonicalLocalScalarExtensionAt K L v) :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace.completion v :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.localElementNormAt K L v y

def chapter09CanonicalEverywhereLocalElementNorm
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (a : K) : Prop :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalElementNorm K L a

theorem chapter09_canonical_local_scalar_extension_is_product
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    ∀ v : LastLib.Book06GlobalClassFieldTheory.Chapter01.BookPlace K,
      LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalProductAlgebra K L v :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.local_tensor_product_product_decomposition

theorem chapter09_hasse_norm_principle_unconditional
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L / K))] :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.HasseNormPrinciple K L :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.cyclic_extensions_satisfy_hasse_norm_principle

theorem chapter09_hasse_norm_theorem_unconditional
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L / K))] {a : K} (ha : a ≠ 0) :
    LastLib.Book06GlobalClassFieldTheory.Chapter01.IsElementNorm K L a ↔
      LastLib.Book06GlobalClassFieldTheory.Chapter01.IsLocalElementNorm K L a := by
  constructor
  · exact LastLib.Book06GlobalClassFieldTheory.Chapter01.elementNorm_implies_local_elementNorm ha
  · intro hlocal
    exact chapter09_hasse_norm_principle_unconditional ha hlocal

/-!
This is the element-level, canonical local/global form of the displayed
Hasse norm theorem.  The unit-group formulation above remains available for
clients that already supply an explicit cyclic-algebra realization.
-/
theorem chapter09_hasse_norm_theorem_unconditional_units
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (Gal(L / K))] (a : Kˣ) :
    a ∈ chapter09FieldNormSubgroup K L ↔
      chapter09CanonicalEverywhereLocalElementNorm K L (a : K) := by
  constructor
  · rintro ⟨y, hy⟩
    have ha : (a : K) ≠ 0 := Units.ne_zero a
    have hnorm : LastLib.Book06GlobalClassFieldTheory.Chapter01.IsElementNorm
        K L (a : K) := by
      refine ⟨(y : L), Units.ne_zero y, ?_⟩
      have h := congrArg Units.val hy
      simpa using h
    exact LastLib.Book06GlobalClassFieldTheory.Chapter01.elementNorm_implies_local_elementNorm
      ha hnorm
  · intro hlocal
    have ha : (a : K) ≠ 0 := Units.ne_zero a
    have hnorm : LastLib.Book06GlobalClassFieldTheory.Chapter01.IsElementNorm
        K L (a : K) :=
      (chapter09_hasse_norm_theorem_unconditional (a := (a : K)) ha).mpr hlocal
    rcases hnorm with ⟨y, hy, hnorm⟩
    refine ⟨Units.mk0 y hy, ?_⟩
    apply Units.ext
    change Algebra.norm K y = (a : K)
    exact hnorm

def chapter09PositiveRealUnit (a : ℝˣ) : Prop :=
  0 < (a : ℝ)

/-!
At the real place of a complex quadratic extension, the local norm subgroup is
the positive reals.  This is recorded separately because it is the only
archimedean sign condition needed in the cyclic theorem.
-/
theorem chapter09_real_quadratic_norm_iff (a : ℝˣ) :
    a ∈ chapter09FieldNormSubgroup ℝ ℂ ↔ chapter09PositiveRealUnit a := by
  have norm_eq_normSq : ∀ z : ℂ, Algebra.norm ℝ z = Complex.normSq z := by
    intro z
    rw [Algebra.norm_apply]
    simp [Algebra.lmul, Complex.normSq]
    rw [← LinearMap.det_toMatrix Complex.basisOneI]
    rw [Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, Complex.basisOneI]
  constructor
  · rintro ⟨z, hz⟩
    have hnorm : Algebra.norm ℝ (z : ℂ) = (a : ℝ) := by
      simpa using congrArg Units.val hz
    have hnormSq : Complex.normSq (z : ℂ) = (a : ℝ) := by
      exact (norm_eq_normSq (z : ℂ)).symm.trans hnorm
    have hne : Complex.normSq (z : ℂ) ≠ 0 := by
      rw [hnormSq]
      exact Units.ne_zero a
    change 0 < (a : ℝ)
    rw [← hnormSq]
    exact (lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hne))
  · intro ha
    change 0 < (a : ℝ) at ha
    have hsqrt : (Real.sqrt (a : ℝ)) ^ 2 = (a : ℝ) := by
      exact Real.sq_sqrt (le_of_lt ha)
    have hsqrt0 : Real.sqrt (a : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 ha)
    refine ⟨Units.mk0 (Real.sqrt (a : ℝ) : ℂ) ?_, ?_⟩
    · exact_mod_cast hsqrt0
    · apply Units.ext
      change Algebra.norm ℝ (Real.sqrt (a : ℝ) : ℂ) = (a : ℝ)
      rw [norm_eq_normSq, Complex.normSq_ofReal]
      simpa [pow_two] using hsqrt

theorem chapter09_real_quadratic_norm_is_positive (a : ℂˣ) :
    chapter09PositiveRealUnit (chapter09FieldNormUnitHom ℝ ℂ a) := by
  exact (chapter09_real_quadratic_norm_iff
    (chapter09FieldNormUnitHom ℝ ℂ a)).mp ⟨a, rfl⟩

end

end LastLib.Book06GlobalClassFieldTheory.Chapter09
