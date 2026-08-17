import LastLib.Book01ValuationsDVRsAndCompletions.Chapter05.Section01SuccessivePrecision
import Mathlib.Algebra.Module.PID
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Extension
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter05

open IsLocalRing
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped BigOperators DirectSum nonZeroDivisors WithZero

noncomputable section

/-!
# Chapter 5: The valuation filtration

This file is a statement-generation pass for Chapter 5 of *Valuations, DVRs, and
Completions*.  The declarations are deliberately self-contained: the DVR and
local-ring notions used below are Mathlib notions, while the few constructions
which are not exposed by Mathlib are recorded as chapter-local interfaces.
-/

/-! # Book 1, Chapter 5, Section 5.2: Leading Terms and Digits
-/

section LeadingTermsAndDigits

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (π : A) (hπ : Irreducible π)

/--
The external associated-graded object is the direct sum of the successive
quotients.  Mathlib does not provide the associated-graded ring construction
for this filtration, so the polynomial ring below is retained as the concrete
ring model used by the initial-form declarations.
-/
abbrev chapterAssociatedGradedObject : Type _ :=
  ⨁ n : ℕ, chapterGradedPiece A n

/- The concrete polynomial model for the associated graded ring. -/
abbrev chapterAssociatedGradedRing : Type _ :=
  Polynomial (IsLocalRing.ResidueField A)

noncomputable instance chapterAssociatedGradedRing.module :
    Module A (chapterAssociatedGradedRing (A := A)) := by
  let f : A →+* chapterAssociatedGradedRing (A := A) :=
    (Polynomial.C : IsLocalRing.ResidueField A →+*
      Polynomial (IsLocalRing.ResidueField A)).comp (IsLocalRing.residue A)
  exact Module.compHom (chapterAssociatedGradedRing (A := A)) f

/-- The chosen inclusion of a graded piece into the polynomial realization. -/
def chapterGradedInclusion (n : ℕ) :
    chapterGradedPiece A n →ₗ[A] chapterAssociatedGradedRing (A := A) := by
  classical
  let f : A →ₗ[A] chapterAssociatedGradedRing (A := A) :=
    { toFun := fun a => Polynomial.C (IsLocalRing.residue A a) * Polynomial.X ^ n
      map_add' := by
        intro a b
        simp only [map_add, add_mul]
      map_smul' := by
        intro a b
        simp only [smul_eq_mul, map_mul, RingHom.toModule_smul,
          RingHom.comp_apply, RingHom.id_apply]
        ring }
  have hf : (IsLocalRing.maximalIdeal A : Submodule A A) ≤ f.ker := by
    intro a ha
    change Polynomial.C (IsLocalRing.residue A a) * Polynomial.X ^ n = 0
    have hz : IsLocalRing.residue A a = 0 :=
      (IsLocalRing.residue_eq_zero_iff a).2 ha
    rw [hz]
    simp
  exact (Submodule.liftQ (IsLocalRing.maximalIdeal A : Submodule A A) f hf).comp
    (chapterLayerMultiplicationEquiv (A := A) π hπ n).symm.toLinearMap

/-- The class of `π` in `𝔪/𝔪^2`. -/
def chapterUniformizerLayerClass (π : A) (hπ : Irreducible π) :
    chapterGradedPiece A 1 := by
  exact chapterLayerRepresentative (A := A) π hπ 1 1

/-- The initial form of the uniformizer in the polynomial realization. -/
def chapterInitialFormUniformizer (π : A) (_hπ : Irreducible π) :
    chapterAssociatedGradedRing (A := A) := by
  exact Polynomial.X

/-- The finite valuation degree of an element, with `0` assigned to the zero element. -/
def chapterInitialDegree (x : A) : ℕ :=
  (IsDiscreteValuationRing.addVal A x).toNat

/-- The polynomial-model initial form of an element in its first nonzero graded piece. -/
noncomputable def chapterInitialForm (π : A) (hπ : Irreducible π) (x : A) :
    chapterAssociatedGradedRing (A := A) := by
  classical
  exact if hx : x = 0 then 0 else
    let hfac := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
    let n := Classical.choose hfac
    let u := Classical.choose (Classical.choose_spec hfac)
    Polynomial.C (IsLocalRing.residue A (u : A)) * Polynomial.X ^ n

theorem chapterInitialForm_eq_factorization {x : A} (hx : x ≠ 0)
    {n : ℕ} (u : Aˣ) (hu : x = (u : A) * π ^ n) :
    chapterInitialForm (A := A) π hπ x =
      Polynomial.C (IsLocalRing.residue A (u : A)) * Polynomial.X ^ n := by
  classical
  let hfac := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  let n₀ := Classical.choose hfac
  let u₀ := Classical.choose (Classical.choose_spec hfac)
  have hu₀ : x = (u₀ : A) * π ^ n₀ :=
    Classical.choose_spec (Classical.choose_spec hfac)
  have hn : n₀ = n := by
    apply ENat.natCast_inj.mp
    calc
      (n₀ : ℕ∞) = IsDiscreteValuationRing.addVal A x := by
        rw [hu₀, IsDiscreteValuationRing.addVal_def' u₀ hπ n₀]
      _ = (n : ℕ∞) := by
        rw [hu, IsDiscreteValuationRing.addVal_def' u hπ n]
  have huu : (u₀ : A) = (u : A) := by
    apply mul_right_cancel₀ (pow_ne_zero n hπ.ne_zero)
    calc
      (u₀ : A) * π ^ n = (u₀ : A) * π ^ n₀ := by rw [hn]
      _ = x := hu₀.symm
      _ = (u : A) * π ^ n := hu
  unfold chapterInitialForm
  rw [dif_neg hx]
  change Polynomial.C (IsLocalRing.residue A (u₀ : A)) * Polynomial.X ^ n₀ =
    Polynomial.C (IsLocalRing.residue A (u : A)) * Polynomial.X ^ n
  rw [hn, huu]

/- Book §5.2, the underlying graded-vector-space identification
   `gr_𝔪(A) ≅ k[T]`.

The direct sum is the external associated-graded object; the componentwise
condition records the chosen polynomial realization and sends the class of
the uniformizer to `T`.  The ring-level strengthening is recorded by
`chapter_associated_graded_ring_model_exists` below.
-/
theorem chapter_associated_graded_equiv_polynomial :
    ∃ e : chapterAssociatedGradedObject (A := A) ≃ₗ[IsLocalRing.ResidueField A]
        chapterAssociatedGradedRing (A := A),
      (∀ (n : ℕ) (x : chapterGradedPiece A n),
        e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n x) =
          chapterGradedInclusion (A := A) π hπ n x) ∧
      e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) 1
          (chapterUniformizerLayerClass (A := A) π hπ)) =
        chapterInitialFormUniformizer (A := A) π hπ := by
  classical
  let E : (n : ℕ) → chapterGradedPiece A n ≃ₗ[IsLocalRing.ResidueField A]
      IsLocalRing.ResidueField A := fun n =>
    (LinearEquiv.ofBijective
      (chapterLayerResidueLinearMap (A := A) π hπ n) (by
        change Function.Bijective
          (chapterLayerMultiplicationMap (A := A) π hπ n)
        exact chapterLayerMultiplicationMap_bijective (A := A) π hπ n)).symm
  let e₀ := DirectSum.congrLinearEquiv E
  let ePoly :
      (⨁ n : ℕ, IsLocalRing.ResidueField A) ≃ₗ[IsLocalRing.ResidueField A]
        chapterAssociatedGradedRing (A := A) :=
    (finsuppLEquivDirectSum (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField A) ℕ).symm.trans
      ((PolynomialModule.coeffLinearEquiv (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField A)).symm.trans
        (PolynomialModule.equivPolynomial (R := IsLocalRing.ResidueField A)
          (S := IsLocalRing.ResidueField A)))
  let e := e₀.trans ePoly
  have hE (n : ℕ) (a : A) :
      E n (chapterLayerRepresentative (A := A) π hπ n a) =
        IsLocalRing.residue A a := by
    have hf : Function.Bijective
        (chapterLayerResidueLinearMap (A := A) π hπ n) := by
      change Function.Bijective
        (chapterLayerMultiplicationMap (A := A) π hπ n)
      exact chapterLayerMultiplicationMap_bijective (A := A) π hπ n
    dsimp [E]
    apply (LinearEquiv.ofBijective
      (chapterLayerResidueLinearMap (A := A) π hπ n) hf).injective
    rw [(LinearEquiv.ofBijective
      (chapterLayerResidueLinearMap (A := A) π hπ n) hf).apply_symm_apply]
    symm
    change chapterLayerMultiplicationMap (A := A) π hπ n
        (Ideal.Quotient.mk _ a) =
      chapterLayerRepresentative (A := A) π hπ n a
    exact chapterLayerMultiplicationMap_apply (A := A) π hπ n a
  have hA (n : ℕ) (a : A) :
      (chapterLayerMultiplicationEquiv (A := A) π hπ n).symm
          (chapterLayerRepresentative (A := A) π hπ n a) =
        Ideal.Quotient.mk _ a := by
    apply (chapterLayerMultiplicationEquiv (A := A) π hπ n).injective
    rw [(chapterLayerMultiplicationEquiv (A := A) π hπ n).apply_symm_apply]
    symm
    change chapterLayerMultiplicationMap (A := A) π hπ n
        (Ideal.Quotient.mk _ a) =
      chapterLayerRepresentative (A := A) π hπ n a
    exact chapterLayerMultiplicationMap_apply (A := A) π hπ n a
  have hIncl (n : ℕ) (a : A) :
      chapterGradedInclusion (A := A) π hπ n
          (chapterLayerRepresentative (A := A) π hπ n a) =
        Polynomial.C (IsLocalRing.residue A a) * Polynomial.X ^ n := by
    have hA' :
        (↑((chapterLayerMultiplicationEquiv (A := A) π hπ n).symm
          (chapterLayerRepresentative (A := A) π hπ n a)) :
          A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A)) =
        Submodule.Quotient.mk a := by
      exact congrArg (fun z : A ⧸ (IsLocalRing.maximalIdeal A : Ideal A) =>
        (z : A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A))) (hA n a)
    simp only [chapterGradedInclusion, LinearMap.comp_apply]
    change (Submodule.liftQ _ _ _)
      (↑((chapterLayerMultiplicationEquiv (A := A) π hπ n).symm
        (chapterLayerRepresentative (A := A) π hπ n a)) :
        A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A)) = _
    rw [hA']
    rfl
  have hrep (n : ℕ) (x : chapterGradedPiece A n) :
      ∃ a : A, x = chapterLayerRepresentative (A := A) π hπ n a := by
    obtain ⟨z, rfl⟩ :=
      Submodule.Quotient.mk_surjective (chapterGradedPieceDenominator A n) x
    have hz : (z : A) ∈ Ideal.span {π ^ n} := by
      rw [← chapter_maximalIdeal_pow_eq_uniformizer_span A π hπ n]
      exact z.property
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
    refine ⟨a, ?_⟩
    apply (Submodule.Quotient.eq (chapterGradedPieceDenominator A n)).2
    change (z : A) - a * π ^ n ∈
      (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)
    rw [ha]
    have hz : π ^ n * a - a * π ^ n = 0 := by ring
    rw [hz]
    exact Ideal.zero_mem _
  have he₀ (n : ℕ) (x : chapterGradedPiece A n) :
      e₀ (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n x) =
        DirectSum.of (fun _ : ℕ => IsLocalRing.ResidueField A) n (E n x) := by
    simp [e₀, DirectSum.congrLinearEquiv, DirectSum.congrAddEquiv]
  have hePoly (n : ℕ) (c : IsLocalRing.ResidueField A) :
      ePoly (DirectSum.of (fun _ : ℕ => IsLocalRing.ResidueField A) n c) =
        Polynomial.monomial n c := by
    change PolynomialModule.equivPolynomial (R := IsLocalRing.ResidueField A)
      (S := IsLocalRing.ResidueField A)
      ((PolynomialModule.coeffLinearEquiv (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A)).symm
      ((finsuppLEquivDirectSum (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A) ℕ).symm
        (DirectSum.of (fun _ : ℕ => IsLocalRing.ResidueField A) n c))) = _
    change PolynomialModule.equivPolynomial (R := IsLocalRing.ResidueField A)
      (S := IsLocalRing.ResidueField A)
      ((PolynomialModule.coeffLinearEquiv (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A)).symm
      ((finsuppLEquivDirectSum (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField A) ℕ).symm
        (DirectSum.lof (IsLocalRing.ResidueField A) ℕ
          (fun _ : ℕ => IsLocalRing.ResidueField A) n c))) = _
    rw [finsuppLEquivDirectSum_symm_lof]
    rfl
  have hcomponent : ∀ (n : ℕ) (x : chapterGradedPiece A n),
      e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n x) =
        chapterGradedInclusion (A := A) π hπ n x := by
    intro n x
    obtain ⟨a, ha⟩ := hrep n x
    rw [ha]
    change ePoly (e₀ (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n
      (chapterLayerRepresentative (A := A) π hπ n a))) = _
    rw [he₀, hePoly, hE, hIncl]
    exact (Polynomial.C_mul_X_pow_eq_monomial).symm
  refine ⟨e, hcomponent, ?_⟩
  calc
    e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) 1
        (chapterUniformizerLayerClass (A := A) π hπ)) =
        chapterGradedInclusion (A := A) π hπ 1
          (chapterUniformizerLayerClass (A := A) π hπ) :=
      hcomponent 1 (chapterUniformizerLayerClass (A := A) π hπ)
    _ = Polynomial.C (IsLocalRing.residue A 1) * Polynomial.X ^ 1 := by
      exact hIncl 1 1
    _ = chapterInitialFormUniformizer (A := A) π hπ := by
      simp [chapterInitialFormUniformizer]

/-- Book §5.2: multiplication of successive quotient classes gives the graded product. -/
def chapterGradedPieceMultiplication (i j : ℕ) :
    chapterGradedPiece A i →ₗ[A]
      chapterGradedPiece A j →ₗ[A] chapterGradedPiece A (i + j) := by
  classical
  let eᵢ := chapterLayerMultiplicationEquiv (A := A) π hπ i
  let eⱼ := chapterLayerMultiplicationEquiv (A := A) π hπ j
  let eᵢⱼ := chapterLayerMultiplicationEquiv (A := A) π hπ (i + j)
  let μ : (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) →ₗ[A]
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) →ₗ[A]
      (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A)) :=
    LinearMap.mul A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))
  exact
    { toFun := fun x =>
        { toFun := fun y => eᵢⱼ (μ (eᵢ.symm x) (eⱼ.symm y))
          map_add' := by
            intro y z
            rw [eⱼ.symm.map_add, (μ (eᵢ.symm x)).map_add, eᵢⱼ.map_add]
          map_smul' := by
            intro c y
            change eᵢⱼ ((μ (eᵢ.symm x)) (eⱼ.symm (c • y))) =
              (RingHom.id A) c • eᵢⱼ ((μ (eᵢ.symm x)) (eⱼ.symm y))
            rw [eⱼ.symm.map_smul, (μ (eᵢ.symm x)).map_smul,
              eᵢⱼ.map_smul]
            rfl }
      map_add' := by
        intro x y
        apply LinearMap.ext
        intro z
        change eᵢⱼ ((μ (eᵢ.symm (x + y))) (eⱼ.symm z)) =
          eᵢⱼ ((μ (eᵢ.symm x)) (eⱼ.symm z)) +
            eᵢⱼ ((μ (eᵢ.symm y)) (eⱼ.symm z))
        have hμ := congrArg (fun f => f (eⱼ.symm z))
          (μ.map_add (eᵢ.symm x) (eᵢ.symm y))
        rw [eᵢ.symm.map_add, ← eᵢⱼ.map_add, hμ]
        simp only [LinearMap.add_apply]
      map_smul' := by
        intro c x
        apply LinearMap.ext
        intro y
        change eᵢⱼ ((μ (eᵢ.symm (c • x))) (eⱼ.symm y)) =
          (RingHom.id A) c • eᵢⱼ ((μ (eᵢ.symm x)) (eⱼ.symm y))
        have hμ := congrArg (fun f => f (eⱼ.symm y))
          (μ.map_smul c (eᵢ.symm x))
        rw [eᵢ.symm.map_smul, ← eᵢⱼ.map_smul, hμ]
        rfl }

/-- Book §5.2: the graded product sends uniformizer-layer representatives to
the representative of the product. -/
theorem chapterGradedPieceMultiplication_apply (i j : ℕ) (a b : A) :
    chapterGradedPieceMultiplication (A := A) π hπ i j
        (chapterLayerRepresentative (A := A) π hπ i a)
        (chapterLayerRepresentative (A := A) π hπ j b) =
      chapterLayerRepresentative (A := A) π hπ (i + j) (a * b) := by
  classical
  have hi :
      (chapterLayerMultiplicationEquiv (A := A) π hπ i).symm
          (chapterLayerRepresentative (A := A) π hπ i a) =
        Ideal.Quotient.mk _ a := by
    apply (chapterLayerMultiplicationEquiv (A := A) π hπ i).injective
    rw [(chapterLayerMultiplicationEquiv (A := A) π hπ i).apply_symm_apply]
    symm
    change chapterLayerMultiplicationMap (A := A) π hπ i
        (Ideal.Quotient.mk _ a) =
      chapterLayerRepresentative (A := A) π hπ i a
    exact chapterLayerMultiplicationMap_apply (A := A) π hπ i a
  have hj :
      (chapterLayerMultiplicationEquiv (A := A) π hπ j).symm
          (chapterLayerRepresentative (A := A) π hπ j b) =
        Ideal.Quotient.mk _ b := by
    apply (chapterLayerMultiplicationEquiv (A := A) π hπ j).injective
    rw [(chapterLayerMultiplicationEquiv (A := A) π hπ j).apply_symm_apply]
    symm
    change chapterLayerMultiplicationMap (A := A) π hπ j
        (Ideal.Quotient.mk _ b) =
      chapterLayerRepresentative (A := A) π hπ j b
    exact chapterLayerMultiplicationMap_apply (A := A) π hπ j b
  change (chapterLayerMultiplicationEquiv (A := A) π hπ (i + j))
      (LinearMap.mul A (A ⧸ (IsLocalRing.maximalIdeal A : Ideal A))
        ((chapterLayerMultiplicationEquiv (A := A) π hπ i).symm
          (chapterLayerRepresentative (A := A) π hπ i a))
        ((chapterLayerMultiplicationEquiv (A := A) π hπ j).symm
          (chapterLayerRepresentative (A := A) π hπ j b))) =
    chapterLayerRepresentative (A := A) π hπ (i + j) (a * b)
  rw [hi, hj]
  change (chapterLayerMultiplicationEquiv (A := A) π hπ (i + j))
      (Ideal.Quotient.mk _ (a * b)) =
    chapterLayerRepresentative (A := A) π hπ (i + j) (a * b)
  change chapterLayerMultiplicationMap (A := A) π hπ (i + j)
      (Ideal.Quotient.mk _ (a * b)) = _
  exact chapterLayerMultiplicationMap_apply (A := A) π hπ (i + j) (a * b)

/- The componentwise multiplication is compatible with the polynomial model.
   This is the ring-level bridge needed when the external direct sum is
   assembled into the associated graded ring. -/
theorem chapter_associated_graded_component_product_compatibility
    (i j : ℕ) (a b : A) :
    chapterGradedInclusion (A := A) π hπ (i + j)
        (chapterGradedPieceMultiplication (A := A) π hπ i j
          (chapterLayerRepresentative (A := A) π hπ i a)
          (chapterLayerRepresentative (A := A) π hπ j b)) =
      chapterGradedInclusion (A := A) π hπ i
        (chapterLayerRepresentative (A := A) π hπ i a) *
      chapterGradedInclusion (A := A) π hπ j
        (chapterLayerRepresentative (A := A) π hπ j b) := by
  rw [chapterGradedPieceMultiplication_apply (A := A) π hπ i j a b]
  have hIncl (n : ℕ) (c : A) :
      chapterGradedInclusion (A := A) π hπ n
          (chapterLayerRepresentative (A := A) π hπ n c) =
        Polynomial.C (IsLocalRing.residue A c) * Polynomial.X ^ n := by
    have hA :
        (↑((chapterLayerMultiplicationEquiv (A := A) π hπ n).symm
            (chapterLayerRepresentative (A := A) π hπ n c)) :
            A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A)) =
          Submodule.Quotient.mk c := by
      apply congrArg (fun z : A ⧸ (IsLocalRing.maximalIdeal A : Ideal A) =>
        (z : A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A)))
      apply (chapterLayerMultiplicationEquiv (A := A) π hπ n).injective
      rw [(chapterLayerMultiplicationEquiv (A := A) π hπ n).apply_symm_apply]
      symm
      exact chapterLayerMultiplicationMap_apply (A := A) π hπ n c
    simp only [chapterGradedInclusion, LinearMap.comp_apply]
    change (Submodule.liftQ _ _ _)
      (↑((chapterLayerMultiplicationEquiv (A := A) π hπ n).symm
        (chapterLayerRepresentative (A := A) π hπ n c)) :
        A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A)) = _
    rw [hA]
    rfl
  rw [hIncl, hIncl, hIncl]
  rw [map_mul, pow_add]
  rw [Polynomial.C_mul]
  rw [← pow_add]
  ring

/- A ring-level associated-graded model carrying the component and product
   identifications.  The ring structure on the external direct sum is part of
   this book-facing interface because the canonical direct-sum API supplies
   only its additive and module structure. -/
structure ChapterAssociatedGradedRingModel where
  [commRing : CommRing (chapterAssociatedGradedObject (A := A))]
  ringEquiv : chapterAssociatedGradedObject (A := A) ≃+*
    chapterAssociatedGradedRing (A := A)
  component : ∀ (n : ℕ) (x : chapterGradedPiece A n),
    ringEquiv (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n x) =
      chapterGradedInclusion (A := A) π hπ n x
  product : ∀ (i j : ℕ) (x : chapterGradedPiece A i)
      (y : chapterGradedPiece A j),
    ringEquiv (DirectSum.of (fun n : ℕ => chapterGradedPiece A n) (i + j)
      (chapterGradedPieceMultiplication (A := A) π hπ i j x y)) =
      ringEquiv (DirectSum.of (fun n : ℕ => chapterGradedPiece A n) i x) *
        ringEquiv (DirectSum.of (fun n : ℕ => chapterGradedPiece A n) j y)
  uniformizer :
    ringEquiv (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) 1
      (chapterUniformizerLayerClass (A := A) π hπ)) =
      chapterInitialFormUniformizer (A := A) π hπ

/- The associated graded object admits the ring structure asserted in §5.2. -/
theorem chapter_associated_graded_ring_model_exists :
    Nonempty (ChapterAssociatedGradedRingModel (A := A) π hπ) := by
  classical
  obtain ⟨e, hecomponent, heuniformizer⟩ :=
    chapter_associated_graded_equiv_polynomial (A := A) (π := π) (hπ := hπ)
  let mulO : chapterAssociatedGradedObject (A := A) →
      chapterAssociatedGradedObject (A := A) →
        chapterAssociatedGradedObject (A := A) :=
    fun x y => e.symm (e x * e y)
  let oneO : chapterAssociatedGradedObject (A := A) := e.symm 1
  let powO : chapterAssociatedGradedObject (A := A) → ℕ →
      chapterAssociatedGradedObject (A := A) := fun x n => e.symm ((e x) ^ n)
  let natCastO : ℕ → chapterAssociatedGradedObject (A := A) := fun n => e.symm n
  let intCastO : ℤ → chapterAssociatedGradedObject (A := A) := fun n => e.symm n
  let : Mul (chapterAssociatedGradedObject (A := A)) := ⟨mulO⟩
  let : One (chapterAssociatedGradedObject (A := A)) := ⟨oneO⟩
  let : Pow (chapterAssociatedGradedObject (A := A)) ℕ := ⟨powO⟩
  let : NatCast (chapterAssociatedGradedObject (A := A)) := ⟨natCastO⟩
  let : IntCast (chapterAssociatedGradedObject (A := A)) := ⟨intCastO⟩
  let : CommRing (chapterAssociatedGradedObject (A := A)) :=
    e.injective.commRing e e.map_zero
      (by change e (e.symm 1) = 1; rw [e.apply_symm_apply])
      (by intro x y; exact e.map_add x y)
      (by intro x y; change e (e.symm (e x * e y)) = e x * e y; rw [e.apply_symm_apply])
      (by intro x; exact e.map_neg x)
      (by intro x y; exact e.map_sub x y)
      (by
        intro n x
        simpa only [Nat.cast_smul_eq_nsmul] using
          e.map_smul (n : IsLocalRing.ResidueField A) x)
      (by
        intro n x
        rw [← Int.cast_smul_eq_zsmul (IsLocalRing.ResidueField A) n x]
        rw [← Int.cast_smul_eq_zsmul (IsLocalRing.ResidueField A) n (e x)]
        exact e.map_smul (n : IsLocalRing.ResidueField A) x)
      (by intro x n; change e (e.symm ((e x) ^ n)) = (e x) ^ n; rw [e.apply_symm_apply])
      (by intro n; change e (e.symm n) = n; rw [e.apply_symm_apply])
      (by intro n; change e (e.symm n) = n; rw [e.apply_symm_apply])
  let f : chapterAssociatedGradedObject (A := A) →+*
      chapterAssociatedGradedRing (A := A) :=
    { toFun := e
      map_zero' := e.map_zero
      map_one' := by change e (e.symm 1) = 1; rw [e.apply_symm_apply]
      map_add' := e.map_add
      map_mul' := by
        intro x y
        change e (e.symm (e x * e y)) = e x * e y
        rw [e.apply_symm_apply] }
  let er : chapterAssociatedGradedObject (A := A) ≃+*
      chapterAssociatedGradedRing (A := A) :=
    RingEquiv.ofBijective f e.bijective
  have hrep (n : ℕ) (x : chapterGradedPiece A n) :
      ∃ a : A, x = chapterLayerRepresentative (A := A) π hπ n a := by
    obtain ⟨z, rfl⟩ :=
      Submodule.Quotient.mk_surjective (chapterGradedPieceDenominator A n) x
    have hz : (z : A) ∈ Ideal.span {π ^ n} := by
      rw [← chapter_maximalIdeal_pow_eq_uniformizer_span A π hπ n]
      exact z.property
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hz
    refine ⟨a, ?_⟩
    apply (Submodule.Quotient.eq (chapterGradedPieceDenominator A n)).2
    change (z : A) - a * π ^ n ∈
      (IsLocalRing.maximalIdeal A ^ (n + 1) : Ideal A)
    rw [ha]
    have hz : π ^ n * a - a * π ^ n = 0 := by ring
    rw [hz]
    exact Ideal.zero_mem _
  refine ⟨{ ringEquiv := er, component := ?_, product := ?_, uniformizer := ?_ }⟩
  · intro n x
    change e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) n x) =
      chapterGradedInclusion (A := A) π hπ n x
    exact hecomponent n x
  · intro i j x y
    obtain ⟨a, rfl⟩ := hrep i x
    obtain ⟨b, rfl⟩ := hrep j y
    change e (DirectSum.of (fun n : ℕ => chapterGradedPiece A n) (i + j)
        (chapterGradedPieceMultiplication (A := A) π hπ i j
          (chapterLayerRepresentative (A := A) π hπ i a)
          (chapterLayerRepresentative (A := A) π hπ j b))) =
      e (DirectSum.of (fun n : ℕ => chapterGradedPiece A n) i
          (chapterLayerRepresentative (A := A) π hπ i a)) *
        e (DirectSum.of (fun n : ℕ => chapterGradedPiece A n) j
          (chapterLayerRepresentative (A := A) π hπ j b))
    rw [hecomponent, hecomponent, hecomponent]
    exact chapter_associated_graded_component_product_compatibility
      (A := A) π hπ i j a b
  · change e (DirectSum.of (fun i : ℕ => chapterGradedPiece A i) 1
        (chapterUniformizerLayerClass (A := A) π hπ)) =
      chapterInitialFormUniformizer (A := A) π hπ
    exact heuniformizer

/-- Book §5.2: initial forms multiply. -/
theorem chapter_initial_form_mul {x y : A} (hx : x ≠ 0) (hy : y ≠ 0) :
    chapterInitialForm (A := A) π hπ (x * y) =
      chapterInitialForm (A := A) π hπ x * chapterInitialForm (A := A) π hπ y := by
  classical
  obtain ⟨nx, ux, hux⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  obtain ⟨ny, uy, huy⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  have hxy : x * y = ((ux * uy : Aˣ) : A) * π ^ (nx + ny) := by
    rw [hux, huy, pow_add]
    simp [mul_assoc, mul_left_comm]
  rw [chapterInitialForm_eq_factorization (A := A) π hπ (mul_ne_zero hx hy)
      (ux * uy) hxy,
    chapterInitialForm_eq_factorization (A := A) π hπ hx ux hux,
    chapterInitialForm_eq_factorization (A := A) π hπ hy uy huy]
  simp [map_mul, pow_add, mul_assoc]
  ring

/-- Book §5.2: equal-degree initial forms can cancel, producing a strict valuation increase. -/
theorem chapter_initial_form_cancellation_strict_valuation
    {x y : A} (hx : x ≠ 0) (hy : y ≠ 0)
    (hdegree : IsDiscreteValuationRing.addVal A x =
      IsDiscreteValuationRing.addVal A y)
    (hcancel : chapterInitialForm (A := A) π hπ x +
        chapterInitialForm (A := A) π hπ y = 0) :
    IsDiscreteValuationRing.addVal A x <
      IsDiscreteValuationRing.addVal A (x + y) := by
  classical
  obtain ⟨nx, ux, hux⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  obtain ⟨ny, uy, huy⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hπ
  have hnx : nx = ny := by
    apply ENat.natCast_inj.mp
    calc
      (nx : ℕ∞) = IsDiscreteValuationRing.addVal A x := by
        rw [hux, IsDiscreteValuationRing.addVal_def' ux hπ nx]
      _ = IsDiscreteValuationRing.addVal A y := hdegree
      _ = (ny : ℕ∞) := by
        rw [huy, IsDiscreteValuationRing.addVal_def' uy hπ ny]
  have hcancel' :
      Polynomial.C (IsLocalRing.residue A (ux : A)) * Polynomial.X ^ nx +
        Polynomial.C (IsLocalRing.residue A (uy : A)) * Polynomial.X ^ nx = 0 := by
    simpa [chapterInitialForm_eq_factorization (A := A) π hπ hx ux hux,
      chapterInitialForm_eq_factorization (A := A) π hπ hy uy huy, hnx]
      using hcancel
  have hcoeff := congrArg (fun p : Polynomial (IsLocalRing.ResidueField A) => p.coeff nx)
    hcancel'
  have hres : IsLocalRing.residue A ((ux : A) + (uy : A)) = 0 := by
    simpa [map_add] using hcoeff
  have hmem : (ux : A) + (uy : A) ∈ IsLocalRing.maximalIdeal A :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (by
    rw [← hπ.maximalIdeal_eq]
    exact hmem)
  have hsum : x + y = c * π ^ (nx + 1) := by
    calc
      x + y = ((ux : A) + (uy : A)) * π ^ ny := by
        rw [hux, huy, hnx]
        ring
      _ = (c * π) * π ^ ny := by rw [hc]
      _ = c * π ^ (nx + 1) := by
        calc
          (c * π) * π ^ ny = c * (π * π ^ ny) := by ring
          _ = c * π ^ (ny + 1) := by rw [pow_succ']
          _ = c * π ^ (nx + 1) := by rw [hnx]
  have hdvd : π ^ (nx + 1) ∣ x + y := by
    refine ⟨c, ?_⟩
    simpa [mul_comm] using hsum
  have hle : (nx + 1 : ℕ∞) ≤ IsDiscreteValuationRing.addVal A (x + y) := by
    have hle' := (IsDiscreteValuationRing.addVal_le_iff_dvd).2 hdvd
    rw [hπ.addVal_pow] at hle'
    exact hle'
  have hxval : IsDiscreteValuationRing.addVal A x = nx :=
    IsDiscreteValuationRing.addVal_def x ux hπ nx hux
  rw [hxval]
  exact lt_of_lt_of_le (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self nx)) hle

/-- Book §5.2: relative to the original `π`-coordinate, replacing the
uniformizer by `uπ` rescales the degree-one generator by `ū`. -/
theorem chapter_initial_form_uniformizer_change
    (u : Aˣ) :
    chapterInitialForm (A := A) π hπ ((u : A) * π) =
      Polynomial.C (IsLocalRing.residue A (u : A)) *
        chapterInitialFormUniformizer (A := A) π hπ := by
  rw [chapterInitialForm_eq_factorization (A := A) π hπ
    (n := 1) (mul_ne_zero (Units.ne_zero u) hπ.ne_zero) u (by simp)]
  simp [chapterInitialFormUniformizer]

/-- A set of residue representatives, including `0`. -/
def chapterIsResidueRepresentativeSet (S : Set A) : Prop :=
  (0 : A) ∈ S ∧
    Function.Bijective (fun s : S => IsLocalRing.residue A (s : A))

/-- Book §5.2: residue representative sets exist. -/
theorem chapter_exists_residue_representative_set :
    ∃ S : Set A, chapterIsResidueRepresentativeSet A S := by
  classical
  let f := IsLocalRing.residue A
  let s : IsLocalRing.ResidueField A → A := fun r =>
    if r = 0 then 0 else Classical.choose (IsLocalRing.residue_surjective (R := A) r)
  have hs : ∀ r, f (s r) = r := by
    intro r
    by_cases hr : r = 0
    · simp [s, f, hr]
    · simpa [s, f, hr] using
        (Classical.choose_spec (IsLocalRing.residue_surjective (R := A) r))
  let S : Set A := Set.range s
  refine ⟨S, ⟨?_, ?_⟩⟩
  · exact ⟨0, by simp [s]⟩
  · constructor
    · intro x y hxy
      rcases x.property with ⟨r, hr⟩
      rcases y.property with ⟨t, ht⟩
      apply Subtype.ext
      have hres : f (s r) = f (s t) := by simpa [hr, ht] using hxy
      have hrt : r = t := by
        calc
          r = f (s r) := (hs r).symm
          _ = f (s t) := hres
          _ = t := hs t
      exact hr.symm.trans ((congrArg s hrt).trans ht)
    · intro r
      exact ⟨⟨s r, ⟨r, rfl⟩⟩, hs r⟩

/-- The finite digit polynomial attached to a list of representatives. -/
def chapterDigitExpansion (S : Set A) (n : ℕ) (digits : Fin n → S) : A :=
  ∑ i : Fin n, (digits i : A) * π ^ (i : ℕ)

/-- The class of a finite digit expansion modulo `π^n`. -/
def chapterDigitExpansionClass (S : Set A) (n : ℕ) (digits : Fin n → S) :
    A ⧸ (Ideal.span {π ^ n} : Ideal A) :=
  Ideal.Quotient.mk _ (chapterDigitExpansion (A := A) π S n digits)

/-- The representative chosen for the first residue digit of `x`. -/
noncomputable def chapterChosenResidueDigit
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (x : A) : S :=
  Classical.choose (hS.2.surjective (IsLocalRing.residue A x))

/-- Book §5.2: the chosen first digit has the same residue as `x`. -/
theorem chapterChosenResidueDigit_spec
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (x : A) :
    IsLocalRing.residue A (chapterChosenResidueDigit A S hS x : A) =
      IsLocalRing.residue A x := by
  exact Classical.choose_spec (hS.2.surjective (IsLocalRing.residue A x))

include π hπ in
/-- The quotient obtained after subtracting the first digit and dividing by `π`. -/
noncomputable def chapterDigitQuotient
    (π : A) (hπ : Irreducible π)
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (x : A) : A := by
  classical
  exact Classical.choose (show ∃ y : A,
      x - (chapterChosenResidueDigit A S hS x : A) = π * y from by
    have hz : IsLocalRing.residue A
        (x - (chapterChosenResidueDigit A S hS x : A)) = 0 := by
      rw [map_sub, chapterChosenResidueDigit_spec A S hS x]
      exact sub_self _
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp hz
    rw [hπ.maximalIdeal_eq] at hm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨y, by simpa [mul_comm] using hy.symm⟩)

/-- Book §5.2: one step of the digit extraction algorithm. -/
theorem chapter_digit_extraction_step
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (x : A) :
    x - (chapterChosenResidueDigit A S hS x : A) =
      π * chapterDigitQuotient (A := A) (π := π) (hπ := hπ) S hS x := by
  unfold chapterDigitQuotient
  exact Classical.choose_spec (show ∃ y : A,
      x - (chapterChosenResidueDigit A S hS x : A) = π * y from by
    have hz : IsLocalRing.residue A
        (x - (chapterChosenResidueDigit A S hS x : A)) = 0 := by
      rw [map_sub, chapterChosenResidueDigit_spec A S hS x]
      exact sub_self _
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp hz
    rw [hπ.maximalIdeal_eq] at hm
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨y, by simpa [mul_comm] using hy.symm⟩)

include hπ in
/-- Book §5.2, displayed digit expansion: existence and uniqueness modulo `π^n`. -/
theorem chapter_unique_digit_expansion
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S) (n : ℕ) :
    ∀ x : A ⧸ (Ideal.span {π ^ n} : Ideal A),
      ∃! digits : Fin n → S,
        chapterDigitExpansionClass (A := A) π S n digits = x := by
  classical
  have hcons : ∀ (k : ℕ) (d : S) (tail : Fin k → S),
      chapterDigitExpansion (A := A) π S (k + 1) (Fin.cons d tail) =
        (d : A) + π * chapterDigitExpansion (A := A) π S k tail := by
    intro k d tail
    simp [chapterDigitExpansion, Fin.sum_univ_succ, pow_succ',
      Fin.cons, mul_comm, mul_left_comm]
    rw [Finset.mul_sum]
  have hrepr : ∀ (k : ℕ) (digits : Fin (k + 1) → S),
      Fin.cons (digits 0) (fun i => digits i.succ) = digits := by
    intro k digits
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  have hcancel_mem : ∀ (k : ℕ) {z : A},
      π * z ∈ (Ideal.span {π ^ (k + 1)} : Ideal A) →
        z ∈ (Ideal.span {π ^ k} : Ideal A) := by
    intro k z hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz
    refine Ideal.mem_span_singleton'.2 ⟨c, ?_⟩
    apply mul_left_cancel₀ hπ.ne_zero
    calc
      π * (c * π ^ k) = c * π ^ (k + 1) := by
        rw [pow_succ']
        ring
      _ = π * z := hc
  have hpow_mem_max : ∀ (k : ℕ),
      (Ideal.span {π ^ (k + 1)} : Ideal A) ≤ IsLocalRing.maximalIdeal A := by
    intro k z hz
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hz
    rw [hπ.maximalIdeal_eq]
    rw [← hc]
    apply Ideal.mul_mem_left _ c
    rw [pow_succ']
    simpa [mul_comm] using
      (Ideal.mul_mem_left _ (π ^ k) (Ideal.mem_span_singleton_self π))
  induction n with
  | zero =>
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨(fun i => Fin.elim0 i), ?_, ?_⟩
      · change Ideal.Quotient.mk (Ideal.span {π ^ 0}) 0 =
          Ideal.Quotient.mk (Ideal.span {π ^ 0}) a
        rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        rw [pow_zero, Ideal.span_singleton_one]
        simp
      · intro digits hdigits
        funext i
        exact Fin.elim0 i
  | succ k ih =>
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      let d : S := chapterChosenResidueDigit A S hS a
      let y : A := chapterDigitQuotient (A := A) π hπ S hS a
      obtain ⟨tail, htail, htail_unique⟩ :=
        ih (Ideal.Quotient.mk (Ideal.span {π ^ k}) y)
      have hexists :
          chapterDigitExpansionClass (A := A) π S (k + 1) (Fin.cons d tail) =
            Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)}) a := by
        change Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)})
              (chapterDigitExpansion (A := A) π S (k + 1) (Fin.cons d tail)) =
            Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)}) a
        rw [hcons]
        rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        have htail_mem :
            chapterDigitExpansion (A := A) π S k tail - y ∈
              (Ideal.span {π ^ k} : Ideal A) := by
          apply (Ideal.Quotient.eq_zero_iff_mem).mp
          change Ideal.Quotient.mk (Ideal.span {π ^ k})
              (chapterDigitExpansion (A := A) π S k tail - y) = 0
          rw [map_sub]
          exact sub_eq_zero.mpr htail
        have hstep := chapter_digit_extraction_step
          (A := A) (π := π) (hπ := hπ) S hS a
        have hrewrite :
            (d : A) + π * chapterDigitExpansion
                (A := A) π S k tail - a =
              π * (chapterDigitExpansion (A := A) π S k tail - y) := by
          change (chapterChosenResidueDigit A S hS a : A) +
              π * chapterDigitExpansion (A := A) π S k tail - a =
            π * (chapterDigitExpansion (A := A) π S k tail -
              chapterDigitQuotient (A := A) π hπ S hS a)
          calc
            (chapterChosenResidueDigit A S hS a : A) +
                π * chapterDigitExpansion (A := A) π S k tail - a =
              -(a - (chapterChosenResidueDigit A S hS a : A)) +
                π * chapterDigitExpansion (A := A) π S k tail := by ring
            _ = -(π * chapterDigitQuotient (A := A) π hπ S hS a) +
                π * chapterDigitExpansion (A := A) π S k tail := by
              rw [hstep]
            _ = π * (chapterDigitExpansion (A := A) π S k tail -
                chapterDigitQuotient (A := A) π hπ S hS a) := by ring
        have hm : chapterDigitExpansion (A := A) π S k tail - y ∈
            (Ideal.span {π ^ k} : Ideal A) := by
          exact htail_mem
        have hmemterm :
            π * (chapterDigitExpansion (A := A) π S k tail - y) ∈
              (Ideal.span {π ^ (k + 1)} : Ideal A) := by
          rw [show π ^ (k + 1) = π * π ^ k by
            rw [pow_succ']]
          rw [← Ideal.span_singleton_mul_span_singleton]
          exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self π) hm
        exact hrewrite ▸ hmemterm
      refine ⟨Fin.cons d tail, hexists, ?_⟩
      · intro digits₁ h₁
        let digits₂ : Fin (k + 1) → S := Fin.cons d tail
        have h₂ :
            chapterDigitExpansionClass (A := A) π S (k + 1) digits₂ =
              Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)}) a := by
          simpa [digits₂] using hexists
        have heq : chapterDigitExpansionClass (A := A) π S (k + 1) digits₁ =
            chapterDigitExpansionClass (A := A) π S (k + 1) digits₂ :=
          h₁.trans h₂.symm
        have hmem :
            chapterDigitExpansion (A := A) π S (k + 1) digits₁ -
              chapterDigitExpansion (A := A) π S (k + 1) digits₂ ∈
                (Ideal.span {π ^ (k + 1)} : Ideal A) := by
          apply (Ideal.Quotient.eq_zero_iff_mem).mp
          change Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)})
              (chapterDigitExpansion (A := A) π S (k + 1) digits₁ -
                chapterDigitExpansion (A := A) π S (k + 1) digits₂) = 0
          rw [map_sub]
          exact sub_eq_zero.mpr heq
        let tail₁ : Fin k → S := fun i => digits₁ i.succ
        let tail₂ : Fin k → S := fun i => digits₂ i.succ
        have hmem' := hmem
        rw [← hrepr (k := k) digits₁, ← hrepr (k := k) digits₂] at hmem'
        have hfirst : digits₁ 0 = digits₂ 0 := by
          have hdm : ((digits₁ 0 : S) : A) - (digits₂ 0 : S) ∈
              IsLocalRing.maximalIdeal A := by
            have hraw :
                chapterDigitExpansion (A := A) π S (k + 1)
                    (Fin.cons (digits₁ 0) tail₁) -
                    chapterDigitExpansion (A := A) π S (k + 1)
                      (Fin.cons (digits₂ 0) tail₂) -
                  π * (chapterDigitExpansion (A := A) π S k tail₁ -
                    chapterDigitExpansion (A := A) π S k tail₂) ∈
                IsLocalRing.maximalIdeal A := by
              apply Ideal.sub_mem (IsLocalRing.maximalIdeal A)
              · exact hpow_mem_max k hmem'
              · rw [hπ.maximalIdeal_eq]
                simpa [mul_comm] using
                  (Ideal.mul_mem_left (Ideal.span {π})
                    (chapterDigitExpansion (A := A) π S k tail₁ -
                      chapterDigitExpansion (A := A) π S k tail₂)
                    (Ideal.mem_span_singleton_self π))
            simpa [hcons, tail₁, tail₂, sub_eq_add_neg,
              add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_assoc,
              mul_comm, mul_left_comm] using hraw
          apply hS.2.1
          apply sub_eq_zero.mp
          rw [← map_sub]
          apply (IsLocalRing.residue_eq_zero_iff _).2
          exact hdm
        have htail_mem :
            chapterDigitExpansion (A := A) π S k tail₁ -
              chapterDigitExpansion (A := A) π S k tail₂ ∈
                (Ideal.span {π ^ k} : Ideal A) := by
          apply hcancel_mem k
          simpa [hcons, tail₁, tail₂, hfirst, sub_eq_add_neg,
            add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_assoc,
            mul_comm, mul_left_comm] using hmem'
        have htail_eq : chapterDigitExpansionClass (A := A) π S k tail₁ =
            chapterDigitExpansionClass (A := A) π S k tail₂ := by
          apply sub_eq_zero.mp
          change Ideal.Quotient.mk (Ideal.span {π ^ k})
              (chapterDigitExpansion (A := A) π S k tail₁ -
                chapterDigitExpansion (A := A) π S k tail₂) = 0
          exact (Ideal.Quotient.eq_zero_iff_mem).2 htail_mem
        have htail_fun : tail₁ = tail₂ := by
          apply (ih (chapterDigitExpansionClass (A := A) π S k tail₁)).unique
          · rfl
          · exact htail_eq.symm
        calc
          digits₁ = Fin.cons (digits₁ 0) tail₁ :=
            (hrepr (k := k) digits₁).symm
          _ = Fin.cons (digits₂ 0) tail₂ := by rw [hfirst, htail_fun]
          _ = digits₂ := hrepr (k := k) digits₂
          _ = Fin.cons d tail := by rfl

/-- The `n`th prefix of an infinite digit string. -/
def chapterInfiniteDigitPrefix (S : Set A) (digits : ℕ → S) (n : ℕ) : A :=
  Finset.sum (Finset.range n) (fun i => (digits i : A) * π ^ i)

include hπ in
/-- Book §5.2: in an adically complete ring, every infinite digit string converges. -/
theorem chapter_infinite_digit_expansion_exists
    (S : Set A) (_hS : chapterIsResidueRepresentativeSet A S)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (digits : ℕ → S) :
    ∃ x : A, ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n ∈
        IsLocalRing.maximalIdeal A ^ n := by
  classical
  let t : ℕ → A := fun i => (digits i : A) * π ^ i
  let f : ℕ → A := fun n => ∑ i ∈ Finset.range n, t i
  have hfdiff : ∀ {m n : ℕ}, m ≤ n →
      f n - f m ∈ (IsLocalRing.maximalIdeal A) ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
        have hstep : f (n + 1) - f m = (f n - f m) + t n := by
          calc
            f (n + 1) - f m = (f n + t n) - f m := by
              simp [f, t, Finset.sum_range_succ]
            _ = (f n - f m) + t n := by ring
        rw [hstep]
        apply Ideal.add_mem
        · exact ih
        · have hpow : π ^ n ∈ (IsLocalRing.maximalIdeal A) ^ m := by
            exact (Ideal.pow_le_pow_right hmn) (by
              rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
              exact Ideal.mem_span_singleton_self _)
          exact Ideal.mul_mem_left _ (digits n : A) hpow
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((IsLocalRing.maximalIdeal A) ^ m •
        (⊤ : Submodule A A))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    simpa [sub_eq_add_neg, add_comm] using
      (neg_mem (hfdiff hmn))
  obtain ⟨x, hx⟩ := IsPrecomplete.prec
    (I := IsLocalRing.maximalIdeal A) (M := A)
    (IsAdicComplete.toIsPrecomplete (I := IsLocalRing.maximalIdeal A) (M := A))
    (f := f) hcauchy
  refine ⟨x, ?_⟩
  intro n
  have hn : f n - x ∈ (IsLocalRing.maximalIdeal A) ^ n := by
    simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hx n
  simpa [f, t, chapterInfiniteDigitPrefix, sub_eq_add_neg, add_comm] using
    (neg_mem hn)

include hπ in
/-- Book §5.2: Hausdorffness makes the infinite digit expansion unique. -/
theorem chapter_infinite_digit_expansion_unique
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (digits : ℕ → S) :
    ∃! x : A, ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n ∈
        IsLocalRing.maximalIdeal A ^ n := by
  classical
  obtain ⟨x, hx⟩ := chapter_infinite_digit_expansion_exists
    (A := A) (π := π) (hπ := hπ) S hS digits
  refine ⟨x, hx, ?_⟩
  intro y hy
  symm
  apply (IsHausdorff.eq_iff_smodEq
    (I := IsLocalRing.maximalIdeal A) (x := x) (y := y)).2
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  have hxy :
      (x - chapterInfiniteDigitPrefix (A := A) π S digits n) -
          (y - chapterInfiniteDigitPrefix (A := A) π S digits n) ∈
        (IsLocalRing.maximalIdeal A) ^ n :=
    Ideal.sub_mem _ (hx n) (hy n)
  convert hxy using 1; ring

include hπ in
/-- Book §5.2: in an adically complete DVR, every element has a unique
infinite digit expansion. -/
theorem chapter_complete_element_unique_infinite_digit_expansion
    (S : Set A) (hS : chapterIsResidueRepresentativeSet A S)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (x : A) :
    ∃! digits : ℕ → S, ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n ∈
        IsLocalRing.maximalIdeal A ^ n := by
  classical
  let q : ℕ → A := Nat.rec x (fun _ y =>
    chapterDigitQuotient (A := A) π hπ S hS y)
  let digits : ℕ → S := fun n =>
    chapterChosenResidueDigit A S hS (q n)
  have hq (n : ℕ) : q (n + 1) =
      chapterDigitQuotient (A := A) π hπ S hS (q n) := by
    rfl
  have hprefix : ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n =
        π ^ n * q n := by
    intro n
    induction n with
    | zero => simp [chapterInfiniteDigitPrefix, q]
    | succ n ih =>
      have hstep := chapter_digit_extraction_step
        (A := A) (π := π) (hπ := hπ) S hS (q n)
      have hstep' : q n - (digits n : A) = π * q (n + 1) := by
        simpa [digits, hq n] using hstep
      calc
        x - chapterInfiniteDigitPrefix (A := A) π S digits (n + 1) =
            (x - chapterInfiniteDigitPrefix (A := A) π S digits n) -
              (digits n : A) * π ^ n := by
                simp [chapterInfiniteDigitPrefix, Finset.sum_range_succ]
                ring
        _ = π ^ n * q n - (digits n : A) * π ^ n := by rw [ih]
        _ = π ^ n * (q n - (digits n : A)) := by ring
        _ = π ^ n * (π * q (n + 1)) := by rw [hstep']
        _ = π ^ (n + 1) * q (n + 1) := by
          rw [pow_succ']
          ring
  have hex : ∀ n : ℕ,
      x - chapterInfiniteDigitPrefix (A := A) π S digits n ∈
        IsLocalRing.maximalIdeal A ^ n := by
    intro n
    rw [hprefix n, hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
    simpa [mul_comm] using
      (Ideal.mul_mem_left (Ideal.span {π ^ n}) (q n)
        (Ideal.mem_span_singleton_self (π ^ n)))
  refine ⟨digits, hex, ?_⟩
  intro digits' hdigits'
  funext n
  apply Subtype.ext
  have hprefix_eq (d : ℕ → S) (m : ℕ) :
      chapterDigitExpansion (A := A) π S m (fun i => d i) =
        chapterInfiniteDigitPrefix (A := A) π S d m := by
    rw [chapterDigitExpansion, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hfinite : (fun i : Fin (n + 1) => digits' i) =
      (fun i : Fin (n + 1) => digits i) := by
    have hmem :
        chapterDigitExpansion (A := A) π S (n + 1) (fun i => digits' i) -
          chapterDigitExpansion (A := A) π S (n + 1) (fun i => digits i) ∈
          Ideal.span {π ^ (n + 1)} := by
      have hsub := Ideal.sub_mem (IsLocalRing.maximalIdeal A ^ (n + 1))
        (hex (n + 1)) (hdigits' (n + 1))
      have hsub' :
          chapterInfiniteDigitPrefix (A := A) π S digits' (n + 1) -
              chapterInfiniteDigitPrefix (A := A) π S digits (n + 1) ∈
            IsLocalRing.maximalIdeal A ^ (n + 1) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsub
      rw [hprefix_eq digits' (n + 1), hprefix_eq digits (n + 1)]
      simpa [hπ.maximalIdeal_eq, Ideal.span_singleton_pow] using hsub'
    have hclass :
        chapterDigitExpansionClass (A := A) π S (n + 1) (fun i => digits' i) =
          chapterDigitExpansionClass (A := A) π S (n + 1) (fun i => digits i) := by
      apply sub_eq_zero.mp
      change Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})
          (chapterDigitExpansion (A := A) π S (n + 1) (fun i => digits' i) -
            chapterDigitExpansion (A := A) π S (n + 1) (fun i => digits i)) = 0
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hmem
    exact (chapter_unique_digit_expansion
      (A := A) (π := π) (hπ := hπ) S hS (n + 1)
      (chapterDigitExpansionClass (A := A) π S (n + 1) (fun i => digits' i))).unique
      rfl hclass.symm
  simpa using congrArg Subtype.val (congrFun hfinite ⟨n, Nat.lt_succ_self n⟩)

/-- The localization `ℤ_(p)` used in the base-`p` example. -/
abbrev chapterZLocalizedAtPrime (p : ℕ) [Fact p.Prime] :=
  Localization.AtPrime
    (Ideal.span ({(p : ℤ)} : Set ℤ))

/-- The finite prefix represented by the first `n` digits of a base-`p` string. -/
def chapterBasePDigitPrefix (p : ℕ) (digits : ℕ → Fin p) (n : ℕ) : ℤ :=
  Finset.sum (Finset.range n) (fun i => ((digits i : ℕ) : ℤ) * (p : ℤ) ^ i)

/-- Congruence meaning that a localized integer represents a base-`p` digit string. -/
def chapterBasePStringRepresents (p : ℕ) [Fact p.Prime] (digits : ℕ → Fin p)
    (x : chapterZLocalizedAtPrime p) : Prop :=
  ∀ n : ℕ,
    x - algebraMap ℤ (chapterZLocalizedAtPrime p) (chapterBasePDigitPrefix p digits n) ∈
      Ideal.span {algebraMap ℤ (chapterZLocalizedAtPrime p) ((p : ℤ) ^ n)}

/-- Book §5.2, base-`p` example: not every infinite string represents an element of `ℤ_(p)`. -/
theorem chapter_not_every_infinite_base_p_string_represents_a_localized_integer
    (p : ℕ) [Fact p.Prime] :
    ∃ digits : ℕ → Fin p,
      ¬ ∃ x : chapterZLocalizedAtPrime p, chapterBasePStringRepresents p digits x := by
  classical
  let P : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
  have hPprime : P.IsPrime := by
    dsimp [P]
    exact Ideal.isPrime_span_singleton_of_prime
      (Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p))
  have hprefix_succ (digits : ℕ → Fin p) (n : ℕ) :
      chapterBasePDigitPrefix p digits (n + 1) =
        chapterBasePDigitPrefix p digits n +
          ((digits n : ℕ) : ℤ) * (p : ℤ) ^ n := by
    simp [chapterBasePDigitPrefix, Finset.sum_range_succ]
  have hmod : ∀ (x : chapterZLocalizedAtPrime p)
      (digits₁ digits₂ : ℕ → Fin p),
      chapterBasePStringRepresents p digits₁ x →
      chapterBasePStringRepresents p digits₂ x →
      ∀ n : ℕ,
        chapterBasePDigitPrefix p digits₁ n ≡
          chapterBasePDigitPrefix p digits₂ n [ZMOD (p : ℤ) ^ n] := by
    intro x digits₁ digits₂ hx₁ hx₂ n
    have hmem :
        algebraMap ℤ (chapterZLocalizedAtPrime p)
            (chapterBasePDigitPrefix p digits₂ n -
              chapterBasePDigitPrefix p digits₁ n) ∈
          Ideal.span {algebraMap ℤ (chapterZLocalizedAtPrime p) ((p : ℤ) ^ n)} := by
      have hsub := Ideal.sub_mem
        (Ideal.span {algebraMap ℤ (chapterZLocalizedAtPrime p) ((p : ℤ) ^ n)})
        (hx₁ n) (hx₂ n)
      simpa [map_sub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsub
    have hmap :
        algebraMap ℤ (chapterZLocalizedAtPrime p)
            (chapterBasePDigitPrefix p digits₂ n -
              chapterBasePDigitPrefix p digits₁ n) ∈
          Ideal.map (algebraMap ℤ (chapterZLocalizedAtPrime p))
            (Ideal.span {((p : ℤ) ^ n)}) := by
      simpa [Ideal.map_span] using hmem
    obtain ⟨m, hm, hmprod⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        (M := P.primeCompl) (S := chapterZLocalizedAtPrime p)
        (Ideal.span {((p : ℤ) ^ n)})
        (chapterBasePDigitPrefix p digits₂ n -
          chapterBasePDigitPrefix p digits₁ n)).mp hmap
    change m ∉ P at hm
    have hmprod' : m *
          (chapterBasePDigitPrefix p digits₂ n -
            chapterBasePDigitPrefix p digits₁ n) ∈ P ^ n := by
      rw [show P ^ n = Ideal.span {((p : ℤ) ^ n)} by
        change (Ideal.span ({(p : ℤ)} : Set ℤ)) ^ n =
          Ideal.span {((p : ℤ) ^ n)}
        exact Ideal.span_singleton_pow (p : ℤ) n]
      exact hmprod
    have hdiff :
        chapterBasePDigitPrefix p digits₂ n -
            chapterBasePDigitPrefix p digits₁ n ∈ P ^ n :=
      (Ideal.IsPrime.mul_mem_pow P (hI := hPprime) hmprod').resolve_left hm
    have hdiv :
        ((p : ℤ) ^ n) ∣
          chapterBasePDigitPrefix p digits₂ n -
            chapterBasePDigitPrefix p digits₁ n := by
      apply Ideal.mem_span_singleton.mp
      simpa [P, Ideal.span_singleton_pow] using hdiff
    rw [Int.modEq_iff_dvd]
    exact hdiv
  have hunique : ∀ (x : chapterZLocalizedAtPrime p)
      (digits₁ digits₂ : ℕ → Fin p),
      chapterBasePStringRepresents p digits₁ x →
      chapterBasePStringRepresents p digits₂ x → digits₁ = digits₂ := by
    intro x digits₁ digits₂ hx₁ hx₂
    funext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        have hprefix :
            chapterBasePDigitPrefix p digits₁ n =
              chapterBasePDigitPrefix p digits₂ n := by
          unfold chapterBasePDigitPrefix
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k (Finset.mem_range.mp hk)]
        have hmul := hmod x digits₁ digits₂ hx₁ hx₂ (n + 1)
        rw [hprefix_succ digits₁ n, hprefix_succ digits₂ n, hprefix] at hmul
        have hmul' := Int.ModEq.add_left_cancel'
          (chapterBasePDigitPrefix p digits₂ n) hmul
        have hdigit :
            ((digits₁ n : ℕ) : ℤ) ≡ ((digits₂ n : ℕ) : ℤ)
              [ZMOD (p : ℤ)] := by
          apply Int.ModEq.mul_right_cancel'
            (c := (p : ℤ) ^ n) (m := (p : ℤ))
            (pow_ne_zero n
              (Int.ofNat_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero))
          simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using hmul'
        have hmodnat :
            (digits₁ n : ℕ) % p = (digits₂ n : ℕ) % p := by
          have hmodint :
              ((digits₁ n : ℕ) : ℤ) % (p : ℤ) =
                ((digits₂ n : ℕ) : ℤ) % (p : ℤ) := by
            simpa [Int.ModEq] using hdigit
          rw [← Int.natCast_mod, ← Int.natCast_mod] at hmodint
          exact_mod_cast hmodint
        have hval : (digits₁ n : ℕ) = (digits₂ n : ℕ) := by
          simpa [Nat.mod_eq_of_lt (digits₁ n).isLt,
            Nat.mod_eq_of_lt (digits₂ n).isLt] using hmodnat
        exact Fin.ext hval
  have hnotcount : ¬ Countable (ℕ → Fin p) := by
    intro hcount
    obtain ⟨f, hf⟩ := @exists_surjective_nat (ℕ → Fin p) inferInstance hcount
    let zero : Fin p := ⟨0, (Fact.out : Nat.Prime p).pos⟩
    let one : Fin p := ⟨1, (Fact.out : Nat.Prime p).one_lt⟩
    have hone : one ≠ zero := by
      intro h
      have hv := congrArg Fin.val h
      norm_num at hv
    let diagonal : ℕ → Fin p := fun n => if f n n = zero then one else zero
    have hdiag : ∀ n, diagonal n ≠ f n n := by
      intro n
      by_cases h : f n n = zero
      · simp only [diagonal, h]
        exact hone
      · simp only [diagonal, h]
        exact Ne.symm h
    obtain ⟨n, hn⟩ := hf diagonal
    exact hdiag n (congrFun hn n).symm
  by_contra h
  have hall : ∀ digits : ℕ → Fin p,
      ∃ x : chapterZLocalizedAtPrime p,
        chapterBasePStringRepresents p digits x := by
    intro digits
    by_contra hd
    exact h ⟨digits, hd⟩
  let representative : (ℕ → Fin p) → chapterZLocalizedAtPrime p :=
    fun digits => Classical.choose (hall digits)
  have hrepresentative : ∀ digits : ℕ → Fin p,
      chapterBasePStringRepresents p digits (representative digits) := by
    intro digits
    dsimp [representative]
    exact Classical.choose_spec (hall digits)
  have hinjective : Function.Injective representative := by
    intro digits₁ digits₂ heq
    apply hunique (representative digits₁) digits₁ digits₂
    · exact hrepresentative digits₁
    · simpa [heq] using hrepresentative digits₂
  have hsurjective : Function.Surjective
      (fun z : ℤ × P.primeCompl =>
        IsLocalization.mk' (chapterZLocalizedAtPrime p) z.1 z.2) :=
    IsLocalization.mk'_surjective P.primeCompl
  exact hnotcount
    (@Function.Injective.countable (ℕ → Fin p) (chapterZLocalizedAtPrime p)
      hsurjective.countable representative hinjective)

/-- The cardinality of the residue field. -/
def chapterResidueCardinality : ℕ := Nat.card (IsLocalRing.ResidueField A)

include hπ in
/-- Book §5.2: if `|k| = q`, then `|A/(π^n)| = q^n`. -/
theorem chapter_quotient_cardinality_pow
    [Finite (IsLocalRing.ResidueField A)] (n : ℕ) :
    Nat.card (A ⧸ (Ideal.span {π ^ n} : Ideal A)) =
      chapterResidueCardinality A ^ n := by
  classical
  rw [← chapter_maximalIdeal_pow_eq_uniformizer_span A π hπ n,
    ← Submodule.cardQuot_apply]
  calc
    Submodule.cardQuot (IsLocalRing.maximalIdeal A ^ n) =
        Submodule.cardQuot (IsLocalRing.maximalIdeal A) ^ n :=
      cardQuot_pow_of_prime
        (P := IsLocalRing.maximalIdeal A)
        (by
          rw [hπ.maximalIdeal_eq]
          exact fun h => hπ.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    _ = Nat.card (IsLocalRing.ResidueField A) ^ n := by
      rw [Submodule.cardQuot_apply]
      rfl

/-- The image of the uniformizer in the truncated quotient. -/
def chapterQuotientUniformizer (n : ℕ) :
    A ⧸ (Ideal.span {π ^ n} : Ideal A) :=
  Ideal.Quotient.mk _ π

include hπ in
/-- Book §5.2: the truncated quotient is Artinian local. -/
-- The truncation index is explicitly positive, as is conventional for
-- quotients called truncated DVRs.
theorem chapter_quotient_is_artinian_local (n : ℕ) (hn : 0 < n) :
    IsArtinianRing (A ⧸ (Ideal.span {π ^ n} : Ideal A)) ∧
      IsLocalRing (A ⧸ (Ideal.span {π ^ n} : Ideal A)) := by
  classical
  let I : Ideal A := Ideal.span {π ^ n}
  let Q := A ⧸ I
  have hunit : ¬ IsUnit (π ^ n) := by
    intro h
    have hn0 : n = 0 :=
      (isUnit_pow_iff_of_not_isUnit hπ.not_isUnit).mp h
    exact (Nat.ne_of_gt hn) hn0
  have hItop : I ≠ ⊤ := by
    exact Ideal.span_singleton_ne_top hunit
  have hQnontrivial : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hItop
  have hQlocal : IsLocalRing Q :=
    letI : Nontrivial Q := hQnontrivial
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hnil :
      IsNilpotent (@IsLocalRing.maximalIdeal Q _ hQlocal) :=
    letI : Nontrivial Q := hQnontrivial
    letI : IsLocalRing Q := hQlocal
    by
      refine ⟨n, ?_⟩
      rw [← IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, ← Ideal.map_pow,
        hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
      apply (Ideal.map_eq_bot_iff_le_ker _).2
      rw [Ideal.mk_ker]
  have hArt : IsArtinianRing Q :=
    letI : Nontrivial Q := hQnontrivial
    letI : IsLocalRing Q := hQlocal
    (isArtinianRing_iff_isNilpotent_maximalIdeal Q).2 hnil
  exact ⟨by simpa [I, Q] using hArt, by simpa [I, Q] using hQlocal⟩

include hπ in
/-- Book §5.2: all ideals of the truncated quotient are powers of `π̄`. -/
theorem chapter_quotient_ideals_are_uniformizer_powers (n : ℕ) :
    ∀ I : Ideal (A ⧸ (Ideal.span {π ^ n} : Ideal A)),
      ∃ i : Fin (n + 1),
        I = Ideal.span {(chapterQuotientUniformizer (A := A) π n) ^ (i : ℕ)} := by
  classical
  intro I
  let I₀ : Ideal A := Ideal.span {π ^ n}
  let q : A →+* (A ⧸ I₀) := Ideal.Quotient.mk I₀
  let J : Ideal A := I.comap q
  have hI₀J : I₀ ≤ J := by
    intro x hx
    change q x ∈ I
    have hqx : q x = 0 := (Ideal.Quotient.eq_zero_iff_mem).2 hx
    rw [hqx]
    exact I.zero_mem
  have hJne : J ≠ ⊥ := by
    intro hJ
    have hmem : π ^ n ∈ J := by
      apply hI₀J
      exact Ideal.mem_span_singleton_self _
    rw [hJ] at hmem
    have hzero : π ^ n = 0 := by
      exact (Submodule.mem_bot A).1 hmem
    exact (pow_ne_zero n hπ.ne_zero) hzero
  obtain ⟨i, hi⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJne hπ
  have hdiv : π ^ i ∣ π ^ n := by
    apply Ideal.mem_span_singleton.mp
    rw [← hi]
    exact hI₀J (Ideal.mem_span_singleton_self _)
  have hin : i ≤ n := by
    have hval := (IsDiscreteValuationRing.addVal_le_iff_dvd).2 hdiv
    rw [hπ.addVal_pow, hπ.addVal_pow] at hval
    exact ENat.natCast_le_natCast.mp hval
  refine ⟨⟨i, Nat.lt_succ_of_le hin⟩, ?_⟩
  change I = Ideal.span {(q π) ^ i}
  calc
    I = Ideal.map q (I.comap q) :=
      (Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective I).symm
    _ = Ideal.map q J := rfl
    _ = Ideal.map q (Ideal.span {π ^ i}) := by rw [hi]
    _ = Ideal.span {q (π ^ i)} := by rw [Ideal.map_span]; simp
    _ = Ideal.span {(q π) ^ i} := by rw [map_pow]

omit [IsDiscreteValuationRing A] in
include hπ in
/-- Book §5.2: `π̄` has nilpotence index exactly `n` for `n > 0`. -/
theorem chapter_quotient_uniformizer_nilpotence_index
    (n : ℕ) (hn : 0 < n) :
    (chapterQuotientUniformizer (A := A) π n) ^ n = 0 ∧
      (chapterQuotientUniformizer (A := A) π n) ^ (n - 1) ≠ 0 := by
  classical
  constructor
  · change (Ideal.Quotient.mk (Ideal.span {π ^ n}) π) ^ n = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  · intro hzero
    have hzero' :
        Ideal.Quotient.mk (Ideal.span {π ^ n}) (π ^ (n - 1)) = 0 := by
      simpa [chapterQuotientUniformizer, map_pow] using hzero
    have hmem : π ^ (n - 1) ∈ Ideal.span {π ^ n} :=
      (Ideal.Quotient.eq_zero_iff_mem).mp hzero'
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    have hunit : IsUnit π := by
      have hpow : π ^ (n - 1) = c * π ^ n := hc.symm
      have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn.ne')
      have hpow' : π ^ (n - 1) = (c * π) * π ^ (n - 1) := by
        calc
          π ^ (n - 1) = c * π ^ n := hpow
          _ = c * (π * π ^ (n - 1)) := by
            rw [← pow_succ', hn']
          _ = (c * π) * π ^ (n - 1) := by ring
      have hone : (c * π) = 1 := by
        apply mul_right_cancel₀ (pow_ne_zero (n - 1) hπ.ne_zero)
        simpa [one_mul] using hpow'.symm
      exact IsUnit.of_mul_eq_one c (by simpa [mul_comm] using hone)
    exact hπ.not_isUnit hunit

end LeadingTermsAndDigits

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter05
