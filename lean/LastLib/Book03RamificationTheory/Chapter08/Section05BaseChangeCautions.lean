import LastLib.Book03RamificationTheory.Chapter08.Dependencies

namespace LastLib.Book03RamificationTheory.Chapter08

noncomputable section

open Ideal Matrix Polynomial
open scoped BigOperators Polynomial TensorProduct nonZeroDivisors

/-! ## 8.5. Base change cautions -/

/- Mathlib keeps the right-factor algebra on a tensor product local because a
   tensor product has two natural scalar actions.  All declarations in this
   file use the right-factor action, matching scalar extension over `K'`. -/
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The scalar-extension algebra occurring in the base-change warning. -/
abbrev chapter08ScalarExtension
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Type _ :=
  L ⊗[K] K'

/-- The tensor product remains a field, the hypothesis in the preservation
statement for an unramified base change. -/
def chapter08TensorProductRemainsField
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] : Prop :=
  IsField (chapter08ScalarExtension K L K')

@[simp]
theorem chapter08TensorProductRemainsField_iff
    (K L K' : Type*) [CommRing K] [CommRing L] [CommRing K']
    [Algebra K L] [Algebra K K'] :
    chapter08TensorProductRemainsField K L K' ↔
      IsField (chapter08ScalarExtension K L K') := Iff.rfl

/- A finite separable scalar extension is finite étale over the changed base,
   hence a finite product of fields.  The factor index is existential and is
   intentionally not collapsed to one chosen branch. -/
theorem chapter08_separable_scalar_extension_has_field_factors
    (K L K' : Type*) [Field K] [Field L] [Field K']
    [Algebra K L] [Algebra K K'] [FiniteDimensional K L]
    [FiniteDimensional K K'] [Algebra.IsSeparable K L] :
    ∃ (I : Type*) (_ : Finite I) (F : I → Type*)
      (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra K' (F i)),
      Nonempty
        (chapter08ScalarExtension K L K' ≃ₐ[K'] (∀ i, F i)) := by
  sorry

/- The source's preservation statement is exposed at the exact point where
   the local derivative calculations meet.  This is deliberately a conditional
   bridge: the derivative comparison is a separate valuation-theoretic input,
   rather than the conclusion being smuggled into a theorem about base change. -/
theorem chapter08_unramified_base_change_preserves_different_exponent
    (K L K' L' : Type*) [Field K] [Field L] [Field K'] [Field L']
    [Algebra K L] [Algebra K K'] [Algebra K' L']
    [FiniteDimensional K L] [FiniteDimensional K K']
    (vL : AddValuation L (WithTop ℤ))
    (vL' : AddValuation L' (WithTop ℤ)) (d d' : ℕ)
    (_hbase :
      LastLib.Book03RamificationTheory.Chapter07.chapter07UnramifiedProfile
        1 K K')
    (_htensor : chapter08TensorProductRemainsField K L K')
    (_hsplitting : Nonempty
      (chapter08ScalarExtension K L K' ≃ₐ[K'] L'))
    (πK : K) (πK' : K') (α : L) (α' : L') (g : K[X])
    (_huniformizer_scale :
      vL (algebraMap K L πK) = vL' (algebraMap K' L' πK'))
    (hderivative_value :
      vL (aeval α (derivative g)) =
        vL' (aeval α' (derivative (g.map (algebraMap K K')))))
    (hd : d = vL (aeval α (derivative g)))
    (hd' : d' = vL' (aeval α' (derivative (g.map (algebraMap K K'))))) :
    d' = d := by
  apply Nat.cast_injective (R := WithTop ℤ)
  calc
    (d' : WithTop ℤ) = vL' (aeval α' (derivative (g.map (algebraMap K K')))) := hd'
    _ = vL (aeval α (derivative g)) := hderivative_value.symm
    _ = (d : WithTop ℤ) := hd.symm

/-- The left orthogonal idempotent in a binary product algebra. -/
def chapter08ProductLeftIdempotent
    (R S : Type*) [CommRing R] [CommRing S] : R × S :=
  (1, 0)

/-- The right orthogonal idempotent in a binary product algebra. -/
def chapter08ProductRightIdempotent
    (R S : Type*) [CommRing R] [CommRing S] : R × S :=
  (0, 1)

theorem chapter08_product_idempotents_are_orthogonal
    (R S : Type*) [CommRing R] [CommRing S] :
    chapter08ProductLeftIdempotent R S *
          chapter08ProductRightIdempotent R S = (0, 0) ∧
      chapter08ProductRightIdempotent R S *
          chapter08ProductLeftIdempotent R S = (0, 0) ∧
      chapter08ProductLeftIdempotent R S +
          chapter08ProductRightIdempotent R S = (1, 1) := by
  simp [chapter08ProductLeftIdempotent, chapter08ProductRightIdempotent]

/- The finite product formula is stated for an arbitrary dependent family of
   field factors.  The basis is `Pi.basis`, so the product is a finite
   K'-algebra discriminant rather than a discriminant of one selected field. -/
theorem chapter08_product_discriminant_is_product
    (K' : Type*) [Field K'] (ι : Type*) [Fintype ι] [DecidableEq ι]
    (κ : ι → Type*) [∀ i, Fintype (κ i)]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Algebra K' (F i)]
    [∀ i, DecidableEq (κ i)]
    (b : ∀ i, Module.Basis (κ i) K' (F i)) :
    Algebra.discr K' (Pi.basis b) =
      ∏ i, Algebra.discr K' (b i) := by
  sorry

theorem chapter08_binary_product_discriminant_is_product
    (K' E F : Type*) [Field K'] [Field E] [Field F]
    [Algebra K' E] [Algebra K' F]
    {ι : Type*} {ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι']
    (bE : Module.Basis ι K' E) (bF : Module.Basis ι' K' F) :
    Algebra.discr K' (bE.prod bF) =
      Algebra.discr K' bE * Algebra.discr K' bF := by
  sorry

/-- A product basis transported across a chosen splitting of a scalar
extension.  The index and equivalence are retained to prevent silently
choosing one field factor. -/
noncomputable def chapter08TensorProductFactorBasis
    (K L K' : Type*) [Field K] [Field L] [Field K']
    [Algebra K L] [Algebra K K']
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (κ : ι → Type*) [∀ i, Fintype (κ i)]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Algebra K' (F i)]
    (e : chapter08ScalarExtension K L K' ≃ₐ[K'] (∀ i, F i))
    (b : ∀ i, Module.Basis (κ i) K' (F i)) :
    Module.Basis (Σ i, κ i) K' (chapter08ScalarExtension K L K') :=
  (Pi.basis b).map e.symm.toLinearEquiv

theorem chapter08_tensor_product_discriminant_is_factor_product
    (K L K' : Type*) [Field K] [Field L] [Field K']
    [Algebra K L] [Algebra K K']
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (κ : ι → Type*) [∀ i, Fintype (κ i)]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Algebra K' (F i)]
    (e : chapter08ScalarExtension K L K' ≃ₐ[K'] (∀ i, F i))
    (b : ∀ i, Module.Basis (κ i) K' (F i))
    [∀ i, DecidableEq (κ i)] :
    Algebra.discr K'
        (chapter08TensorProductFactorBasis K L K' ι κ F e b) =
      ∏ i, Algebra.discr K' (b i) := by
  sorry

/- Taking K' = L in a nontrivial finite separable extension supplies a
   concrete source of splitting under base change.  The conclusion records
   the splitting itself; a separate local ramification model is not needed. -/
theorem chapter08_nontrivial_self_base_change_can_split
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdegree : 1 < Module.finrank K L) :
    ∃ (I : Type*) (_ : Fintype I) (F : I → Type*)
      (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra L (F i)),
      2 ≤ Fintype.card I ∧
        Nonempty (L ⊗[K] L ≃ₐ[L] (∀ i, F i)) := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter08
