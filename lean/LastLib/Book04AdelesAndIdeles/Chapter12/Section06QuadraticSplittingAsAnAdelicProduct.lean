import LastLib.Book04AdelesAndIdeles.Chapter12.Core

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
    (d : ℤ) (p : Nat.Primes) :
    chapter12QuadraticResidueSquare d p ∨
      ¬chapter12QuadraticResidueSquare d p := by
  exact Classical.em (chapter12QuadraticResidueSquare d p)

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

theorem chapter12_quadratic_nonsquare_at_odd_prime_is_unramified_field
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K)
    (p : Nat.Primes) (hpodd : p.1 ≠ 2)
    (hpd : ¬((p.1 : ℤ) ∣ Q.d))
    {E : Type*} [Field E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] [Algebra.Unramified ℚ_[p] E]
    (U : Chapter12UnramifiedQuadraticLocalExtension ℚ_[p] E)
    (hnonsquare : ¬chapter12QuadraticResidueSquare Q.d p) :
    chapter12TensorFieldShape K ℚ_[p] E := by
  sorry

theorem chapter12_quadratic_odd_prime_residue_dichotomy
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K) (p : Nat.Primes)
    (_hpodd : p.1 ≠ 2) (_hpd : ¬((p.1 : ℤ) ∣ Q.d)) :
    chapter12QuadraticResidueSquare Q.d p ∨
      ¬chapter12QuadraticResidueSquare Q.d p := by
  exact chapter12_quadratic_odd_prime_has_roots_or_no_roots Q.d p

/-! ## Ramification, the dyadic place, and integral tensors -/

theorem chapter12_quadratic_discriminant_support_iff
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K) (p : ℕ) :
    chapter12QuadraticDiscriminantSupport Q.d p ↔
      p ∣ (chapter12QuadraticDiscriminant Q.d).natAbs := by
  rfl

def chapter12QuadraticTwoAdicBehavior (d : ℤ) :
    Chapter12QuadraticLocalBehavior := by
  classical
  exact if chapter12QuadraticDiscriminantSupport d 2 then .ramified
    else if ∃ a : ZMod 8, a ^ 2 = (d : ZMod 8) then .split else .inert

theorem chapter12_quadratic_two_adic_trichotomy
    (d : ℤ) :
    chapter12QuadraticTwoAdicBehavior d = .split ∨
      chapter12QuadraticTwoAdicBehavior d = .inert ∨
      chapter12QuadraticTwoAdicBehavior d = .ramified := by
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

/- LOCAL_DEPENDENCY_GUESS: `E` below is the canonical integral local factor
   for `K` at each rational prime; the stable earlier chapter API does not yet
   expose its chosen carrier or the finite bad-place theorem. -/
theorem chapter12_quadratic_integral_tensor_products_are_split_or_unramified_almost_everywhere
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (Q : Chapter12QuadraticFieldData K)
    (E : Nat.Primes → Type*)
    [∀ p, CommRing (E p)]
    [∀ p, Algebra (chapter12QuadraticIntegralBaseAt p) (E p)]
    [∀ p, Algebra ℤ (E p)] :
    ∃ S : Finset Nat.Primes, ∀ p : Nat.Primes, p ∉ S →
      chapter12IntegralTensorSplitShape (𝓞 K) (chapter12QuadraticIntegralBaseAt p) ∨
        chapter12IntegralTensorQuadraticFieldShape (𝓞 K)
          (chapter12QuadraticIntegralBaseAt p) (E p) := by
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
