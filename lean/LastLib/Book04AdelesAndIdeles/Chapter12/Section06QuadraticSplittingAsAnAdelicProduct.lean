import LastLib.Book04AdelesAndIdeles.Chapter12.Core
import Mathlib.NumberTheory.NumberField.Discriminant.Different

namespace LastLib.Book04AdelesAndIdeles.Chapter12

noncomputable section

open Set NumberField
open NumberField.InfinitePlace
open scoped BigOperators TensorProduct

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! # Book 4, Chapter 12, §12.6: Quadratic splitting as an adelic product -/

structure Chapter12QuadraticFieldData
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K] where
  d : ℤ
  squarefree : chapter12SquarefreeInteger d
  d_not_square : ¬∃ a : ℤ, a ^ 2 = d
  theta : K
  generator : chapter12QuadraticGenerator d theta

def chapter12QuadraticResidueSquare (d : ℤ) (p : Nat.Primes) : Prop :=
  ∃ a : ZMod p.1, a ^ 2 = (d : ZMod p.1)

def chapter12QuadraticResidueRootSet (d : ℤ) (p : Nat.Primes) : Set (ZMod p.1) :=
  {a | a ^ 2 = (d : ZMod p.1)}

theorem chapter12_quadratic_odd_prime_has_roots_or_no_roots
    (d : ℤ) (p : Nat.Primes) (hpodd : p.1 ≠ 2)
    (hpd : ¬((p.1 : ℤ) ∣ d)) :
    Set.ncard (chapter12QuadraticResidueRootSet d p) = 2 ∨
      chapter12QuadraticResidueRootSet d p = ∅ := by
  sorry

theorem chapter12_quadratic_square_residue_has_two_roots
    (d : ℤ) (p : Nat.Primes) (hpodd : p.1 ≠ 2)
    (hpd : ¬((p.1 : ℤ) ∣ d))
    (hsquare : chapter12QuadraticResidueSquare d p) :
    Set.ncard (chapter12QuadraticResidueRootSet d p) = 2 := by
  sorry

theorem chapter12_quadratic_nonsquare_residue_has_no_root
    (d : ℤ) (p : Nat.Primes)
    (hnonsquare : ¬chapter12QuadraticResidueSquare d p) :
    chapter12QuadraticResidueRootSet d p = ∅ := by
  sorry

/-! ## Hensel lifting and the two local tensor shapes -/

theorem chapter12_quadratic_split_at_odd_prime
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K)
    (p : Nat.Primes) (hpodd : p.1 ≠ 2)
    (hpd : ¬((p.1 : ℤ) ∣ Q.d))
    (hsquare : chapter12QuadraticResidueSquare Q.d p) :
    chapter12TensorSplitShape K ℚ_[p] := by
  sorry

structure Chapter12UnramifiedQuadraticLocalExtension
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.Unramified F E] where
  degree_two : Module.finrank F E = 2

/- The local factor must be tied to the scalar-extension tensor product.  An
   arbitrary unramified quadratic field with the same base is not enough to
   identify the completion of the global quadratic field. -/
structure Chapter12QuadraticUnramifiedLocalFactorData
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    (p : Nat.Primes) where
  E : Type*
  [fieldE : Field E]
  [algebraE : Algebra ℚ_[p] E]
  [finiteDimensionalE : FiniteDimensional ℚ_[p] E]
  [unramifiedE : Algebra.Unramified ℚ_[p] E]
  local_extension : Chapter12UnramifiedQuadraticLocalExtension ℚ_[p] E
  tensor_shape : chapter12TensorFieldShape K ℚ_[p] E

theorem chapter12_quadratic_nonsquare_at_odd_prime_is_unramified_field
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K)
    (p : Nat.Primes) (hpodd : p.1 ≠ 2)
    (hpd : ¬((p.1 : ℤ) ∣ Q.d))
    (hnonsquare : ¬chapter12QuadraticResidueSquare Q.d p) :
    Nonempty (Chapter12QuadraticUnramifiedLocalFactorData K p) := by
  sorry

theorem chapter12_quadratic_odd_prime_residue_dichotomy
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K) (p : Nat.Primes)
    (hpodd : p.1 ≠ 2) (hpd : ¬((p.1 : ℤ) ∣ Q.d)) :
    Set.ncard (chapter12QuadraticResidueRootSet Q.d p) = 2 ∨
      chapter12QuadraticResidueRootSet Q.d p = ∅ := by
  exact chapter12_quadratic_odd_prime_has_roots_or_no_roots Q.d p hpodd hpd

/-! ## Ramification, the dyadic place, and integral tensors -/

theorem chapter12_quadratic_discriminant_support_iff
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K) (p : ℕ) :
    chapter12QuadraticDiscriminantSupport Q.d p ↔
      p ∣ (chapter12QuadraticDiscriminant Q.d).natAbs := by
  rfl

/- The book's discriminant-support assertion is a ramification statement, not
   merely the unfolding of the support predicate. -/
theorem chapter12_quadratic_discriminant_support_iff_not_isUnramifiedIn
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K) (p : Nat.Primes) :
    chapter12QuadraticDiscriminantSupport Q.d p.1 ↔
      ¬Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p.1 : ℤ)}) := by
  sorry

def chapter12QuadraticTwoAdicBehavior (d : ℤ) :
    Chapter12QuadraticLocalBehavior := by
  classical
  exact if chapter12QuadraticDiscriminantSupport d 2 then .ramified
    else if ∃ a : ZMod 8, a ^ 2 = (d : ZMod 8) then .split else .inert

theorem chapter12_quadratic_two_adic_trichotomy
    (d : ℤ) :
    (chapter12QuadraticTwoAdicBehavior d = .ramified ∧
        chapter12QuadraticDiscriminantSupport d 2) ∨
      (chapter12QuadraticTwoAdicBehavior d = .split ∧
        ¬chapter12QuadraticDiscriminantSupport d 2 ∧
        ∃ a : ZMod 8, a ^ 2 = (d : ZMod 8)) ∨
      (chapter12QuadraticTwoAdicBehavior d = .inert ∧
        ¬chapter12QuadraticDiscriminantSupport d 2 ∧
        ¬∃ a : ZMod 8, a ^ 2 = (d : ZMod 8)) := by
  sorry

/-! ## The global adelic scalar-extension identity -/

abbrev chapter12QuadraticAdelicScalarExtension
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] :=
  K ⊗[ℚ] chapter12RationalAdeleRing

theorem chapter12_quadratic_adelic_scalar_extension
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] :
    Nonempty (chapter12AdeleRing (𝓞 K) K ≃+*
      chapter12QuadraticAdelicScalarExtension (K := K)) := by
  sorry

/- The integral base factor at a rational prime, written using the canonical
   height-one-spectrum/p-adic interface. -/
abbrev chapter12QuadraticIntegralBaseAt (p : Nat.Primes) :=
  let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
  v.adicCompletionIntegers ℚ

theorem chapter12_quadratic_integral_base_is_padic_integer
    (p : Nat.Primes) :
    Nonempty (ℤ_[p] ≃A[ℤ] chapter12QuadraticIntegralBaseAt p) := by
  sorry

/- The integral factor is packaged together with its ring structure and its
   identification with the tensor product.  This avoids treating an
   unrelated family of unramified quadratic rings as the scalar extension. -/
structure Chapter12QuadraticIntegralUnramifiedFactorData
    (A B : Type*) [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B] where
  E : Type*
  [commRingE : CommRing E]
  [isDomainE : IsDomain E]
  [algebraBE : Algebra B E]
  [algebraZE : Algebra ℤ E]
  [unramifiedE : Algebra.Unramified B E]
  degree_two : Module.finrank B E = 2
  basis : Nonempty (Module.Basis (Fin 2) B E)
  tensor_shape : chapter12IntegralTensorQuadraticFieldShape A B E

theorem chapter12_quadratic_integral_tensor_products_are_split_or_unramified_almost_everywhere
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K)
    : ∃ S : Finset Nat.Primes, ∀ p : Nat.Primes, p ∉ S →
      chapter12IntegralTensorSplitShape (𝓞 K) (chapter12QuadraticIntegralBaseAt p) ∨
        Nonempty (Chapter12QuadraticIntegralUnramifiedFactorData
          (𝓞 K) (chapter12QuadraticIntegralBaseAt p)) := by
  sorry

/-! ## Infinity and the normalized product formula -/

theorem chapter12_quadratic_positive_discriminant_signature
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K) (hd : 0 < Q.d) :
    NumberField.InfinitePlace.nrRealPlaces K = 2 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = 0 := by
  sorry

theorem chapter12_quadratic_negative_discriminant_signature
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K) (hd : Q.d < 0) :
    NumberField.InfinitePlace.nrRealPlaces K = 0 ∧
      NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  sorry

theorem chapter12_complex_place_has_degree_two_normalization
    {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K) (hv : IsComplex v) :
    v.mult = 2 :=
  hv.mult_eq_two

theorem chapter12_quadratic_product_formula_is_sign_uniform
    {K : Type*} [Field K] [NumberField K]
    (x : K) :
    ‖algebraMap K (chapter12InfiniteAdeleRing K) x‖ =
      |Algebra.norm ℚ x| :=
  chapter12_infinite_adele_product_formula x

end
end LastLib.Book04AdelesAndIdeles.Chapter12
