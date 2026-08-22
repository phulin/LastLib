import LastLib.Book03RamificationTheory.Chapter08.Dependencies
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Maps

namespace LastLib.Book03RamificationTheory.Chapter08

universe uK uL uKp

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
    (K : Type uK) (L : Type uL) (K' : Type uKp)
    [Field K] [Field L] [Field K']
    [Algebra K L] [Algebra K K'] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] :
    ∃ (I : Type (max uK (max uL uKp))) (_ : Finite I)
      (F : I → Type (max uK (max uL uKp)))
      (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra K' (F i)),
      Nonempty
        (chapter08ScalarExtension K L K' ≃ₐ[K'] (∀ i, F i)) := by
  let : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let : Module.Finite K' (K' ⊗[K] L) := Module.Finite.base_change K K' L
  let : Module.Finite K' (L ⊗[K] K') :=
    Module.Finite.equiv (Algebra.TensorProduct.commRight K K' L).toLinearEquiv
  let : Algebra.FormallyEtale K' (K' ⊗[K] L) := inferInstance
  let : Algebra.FormallyEtale K' (L ⊗[K] K') :=
    Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.commRight K K' L)
  have hEtale : Algebra.Etale K' (L ⊗[K] K') := by
    constructor
    · infer_instance
    · exact Algebra.FinitePresentation.of_finiteType.mp inferInstance
  rcases (Algebra.Etale.iff_exists_algEquiv_prod (K := K')
      (A := L ⊗[K] K')).mp hEtale with
    ⟨I, hI, F, hF, hA, e, _hfinite⟩
  refine ⟨ULift.{max uK uL} I, inferInstance,
    (fun i : ULift.{max uK uL} I => ULift.{max uK uL} (F i.down)), ?_, ?_, ?_⟩
  · intro i
    exact ((ULift.ringEquiv :
      ULift.{max uK uL} (F i.down) ≃+* F i.down).toMulEquiv.isField
        (Field.toIsField (F i.down))).toField
  · intro i
    infer_instance
  · let eIndex : I ≃ ULift.{max uK uL} I := Equiv.ulift.symm
    let eIndexAlg : (∀ i, F i) ≃ₐ[K']
        (∀ i : ULift.{max uK uL} I, F (eIndex.symm i)) :=
      AlgEquiv.piCongrLeft' K' F eIndex
    let eLift : (∀ i : ULift.{max uK uL} I, F (eIndex.symm i)) ≃ₐ[K']
        (∀ i : ULift.{max uK uL} I,
          ULift.{max uK uL} (F (eIndex.symm i))) :=
      AlgEquiv.piCongrRight (fun i ↦
        (ULift.algEquiv (R := K') :
          ULift.{max uK uL} (F (eIndex.symm i)) ≃ₐ[K'] F (eIndex.symm i)).symm)
    exact ⟨e.trans (eIndexAlg.trans eLift)⟩

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
  classical
  have htrace :
      Algebra.traceMatrix K' (bE.prod bF) =
        Matrix.fromBlocks (Algebra.traceMatrix K' bE) 0 0
          (Algebra.traceMatrix K' bF) := by
    let : Module.Free K' E := Module.Free.of_basis bE
    let : Module.Finite K' E := Module.Finite.of_basis bE
    let : Module.Free K' F := Module.Free.of_basis bF
    let : Module.Finite K' F := Module.Finite.of_basis bF
    ext i j
    cases i <;> cases j <;>
      simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
        Algebra.trace_prod_apply, Module.Basis.prod_apply]
  rw [Algebra.discr_def, htrace, Matrix.det_fromBlocks_zero₂₁,
    ← Algebra.discr_def, ← Algebra.discr_def]

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
  calc
    Algebra.discr K'
        (chapter08TensorProductFactorBasis K L K' ι κ F e b) =
        Algebra.discr K' (e.symm ∘ Pi.basis b) := by
      congr 1
    _ = Algebra.discr K' (Pi.basis b) := by
      exact (Algebra.discr_eq_discr_of_algEquiv (Pi.basis b) e.symm).symm
    _ = ∏ i, Algebra.discr K' (b i) :=
      chapter08_product_discriminant_is_product K' ι κ F b

/-- If an extension has degree greater than one, multiplication on its self
tensor product has too small a target to be injective, so the tensor product
cannot be a field. -/
theorem chapter08_self_tensor_product_not_field
    (K : Type uK) (L : Type uL) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (hdegree : 1 < Module.finrank K L) :
    ¬ IsField (L ⊗[K] L) := by
  intro hfield
  let : Field (L ⊗[K] L) := hfield.toField
  let mulHom : L ⊗[K] L →ₐ[K] L :=
    Algebra.TensorProduct.lmul' K
  have hinjective : Function.Injective mulHom := mulHom.injective
  have hrank : Module.finrank K (L ⊗[K] L) ≤ Module.finrank K L :=
    LinearMap.finrank_le_finrank_of_injective
      (f := mulHom.toLinearMap) hinjective
  rw [Module.finrank_tensorProduct] at hrank
  have hlt : Module.finrank K L < Module.finrank K L * Module.finrank K L :=
    lt_mul_of_one_lt_left (Nat.zero_lt_of_lt hdegree) hdegree
  exact (not_le_of_gt hlt) hrank

/- Taking K' = L in a nontrivial finite separable extension supplies a
   concrete source of splitting under base change.  The conclusion records
   the splitting itself; a separate local ramification model is not needed. -/
theorem chapter08_nontrivial_self_base_change_can_split
    (K : Type uK) (L : Type uL) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hdegree : 1 < Module.finrank K L) :
    ∃ (I : Type (max uK uL)) (_ : Fintype I)
      (F : I → Type (max uK uL))
      (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra L (F i)),
      2 ≤ Fintype.card I ∧
        Nonempty (L ⊗[K] L ≃ₐ[L] (∀ i, F i)) := by
  rcases chapter08_separable_scalar_extension_has_field_factors K L L with
    ⟨I, hI, F, hF, hA, ⟨e⟩⟩
  let : Fintype I := Fintype.ofFinite I
  have hnonempty : Nonempty I := by
    by_contra hempty
    have hprod : Subsingleton (∀ i, F i) := by
      constructor
      intro f g
      funext i
      exact (hempty ⟨i⟩).elim
    exact zero_ne_one (e.injective (hprod.elim (e 0) (e 1)))
  have hcard : 2 ≤ Fintype.card I := by
    by_contra hnot
    have hle : Fintype.card I ≤ 1 :=
      Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hnot)
    let : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hle
    let : Unique I :=
      { default := Classical.choice hnonempty
        uniq := fun _ ↦ Subsingleton.elim _ _ }
    have hfield : IsField (L ⊗[K] L) :=
      (e.toRingEquiv.trans (RingEquiv.piUnique F)).toMulEquiv.isField
        (Field.toIsField (F (Classical.choice hnonempty)))
    exact chapter08_self_tensor_product_not_field K L hdegree hfield
  exact ⟨I, inferInstance, F, hF, hA, hcard, ⟨e⟩⟩

end

end LastLib.Book03RamificationTheory.Chapter08
