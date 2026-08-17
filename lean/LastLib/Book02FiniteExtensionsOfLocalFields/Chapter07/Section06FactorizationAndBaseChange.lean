import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Maps
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section05ExamplesBothCharacteristics

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Function
open Polynomial
open scoped BigOperators TensorProduct WithZero
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

noncomputable section

universe uFactor

-- The tensor product has a canonical right-factor algebra structure, but
-- Mathlib keeps it local to avoid ambiguity with the left-factor action.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! # Book 2, Chapter 7, §7.6: unramified factorization and base change -/

/-- A finite family of distinct monic irreducible residue factors. -/
structure Chapter07SeparableResidueFactorization
    (k : Type*) [Field k] (r : ℕ) where
  polynomial : k[X]
  factors : Fin r → k[X]
  monic : ∀ i, (factors i).Monic
  irreducible : ∀ i, Irreducible (factors i)
  separable : ∀ i, (factors i).Separable
  distinct : Pairwise (fun i j => factors i ≠ factors j)
  product : polynomial = ∏ i, factors i

/-- A chosen coefficient lift of a residue factorization. -/
structure Chapter07LiftedFactorization
    (A k : Type*) [CommRing A] [Field k] (res : A →+* k)
    (r : ℕ) (F : Chapter07SeparableResidueFactorization k r) (g : A[X]) where
  factors : Fin r → A[X]
  monic : ∀ i, (factors i).Monic
  pairwise_coprime : Pairwise (fun i j =>
    IsCoprime (Ideal.span ({factors i} : Set A[X]))
      (Ideal.span ({factors j} : Set A[X])))
  reductions : ∀ i, (factors i).map res =
    F.factors i
  product : g = ∏ i, factors i
  reduced_product : g.map res = ∏ i, F.factors i

/-- Coprime residue factors lift uniquely to coprime monic factors over a
henselian local ring. -/
theorem chapter07_separable_factorization_lifts_uniquely
    {A k : Type*} [CommRing A] [Field k] [HenselianLocalRing A]
    (res : A →+* k) (r : ℕ) (F : Chapter07SeparableResidueFactorization k r)
    (g : A[X]) (hgmonic : g.Monic)
    (hgred : g.map res = ∏ i, F.factors i)
    (hres_surjective : Function.Surjective res)
    (hres_kernel : RingHom.ker res = IsLocalRing.maximalIdeal A) :
    ∃ G : Chapter07LiftedFactorization A k res r F g,
      ∀ H : Chapter07LiftedFactorization A k res r F g,
        H.factors = G.factors := by
  sorry

/-- The quotient of a separable product splits as the product of its field
factors. -/
theorem chapter07_separable_quotient_is_product
    {K : Type*} [Field K] (g : K[X]) {r : ℕ} (gᵢ : Fin r → K[X])
    (hproduct : g = ∏ i, gᵢ i)
    (hirreducible : ∀ i, Irreducible (gᵢ i))
    (hpairwise : Pairwise (fun i j => IsCoprime (Ideal.span ({gᵢ i} : Set K[X]))
      (Ideal.span ({gᵢ j} : Set K[X])))) :
    Nonempty (AdjoinRoot g ≃+* (∀ i, AdjoinRoot (gᵢ i))) ∧
      ∀ i, IsField (AdjoinRoot (gᵢ i)) := by
  classical
  have hcop : Pairwise (IsCoprime on
      fun i : Fin r => Ideal.span ({gᵢ i} : Set K[X])) := by
    intro i j hij
    exact hpairwise hij
  have hideal :
      (Ideal.span ({g} : Set K[X])) =
        ⨅ i : Fin r, Ideal.span ({gᵢ i} : Set K[X]) := by
    calc
      Ideal.span ({g} : Set K[X]) =
          Ideal.span ({∏ i : Fin r, gᵢ i} : Set K[X]) := by rw [hproduct]
      _ = ∏ i : Fin r, Ideal.span ({gᵢ i} : Set K[X]) := by
        symm
        simpa using
          (Ideal.prod_span_singleton (Finset.univ : Finset (Fin r)) gᵢ)
      _ = ⨅ i : Fin r, Ideal.span ({gᵢ i} : Set K[X]) := by
        simpa using
          (Ideal.prod_eq_iInf_of_pairwise_isCoprime
            (s := (Finset.univ : Finset (Fin r)))
            (J := fun i : Fin r => Ideal.span ({gᵢ i} : Set K[X]))
            (by
              intro i hi j hj hij
              exact hcop hij))
  let e : AdjoinRoot g ≃+* (∀ i, AdjoinRoot (gᵢ i)) :=
    (Ideal.quotEquivOfEq hideal).trans
      (Ideal.quotientInfRingEquivPiQuotient
        (fun i : Fin r => Ideal.span ({gᵢ i} : Set K[X])) hcop)
  refine ⟨⟨e⟩, ?_⟩
  intro i
  let _ : Fact (Irreducible (gᵢ i)) := ⟨hirreducible i⟩
  exact Field.toIsField _

/-- The local-field data attached to one lifted factor.  The factor index is
kept in the type so that a later proof can identify the residue polynomial,
residue degree, and unramified profile without choosing a ring homomorphism
by classical choice. -/
structure Chapter07SeparableFactorResidueField
    (A K k l L : Type*) [CommRing A] [Field K] [Field k] [Field l] [Field L]
    [Algebra A K] [Algebra K L] [Algebra k l]
    [FiniteDimensional K L] [FiniteDimensional k l]
    {r : ℕ} (res : A →+* k)
    (F : Chapter07SeparableResidueFactorization k r)
    (g : A[X]) (G : Chapter07LiftedFactorization A k res r F g)
    (i : Fin r) [Algebra A L] [IsScalarTower A K L] where
  profile : Chapter07FiniteLocalExtensionData K L k l
  unramified : Chapter07UnramifiedExtension profile
  residue_degree : profile.residueDegree = (F.factors i).natDegree
  residue_separable : Chapter07ResidueExtensionIsSeparable k l
  integralModel : Subalgebra A L
  integralModel_finite : Module.Finite A integralModel
  residueMap : integralModel →+* l
  residueMap_surjective : Function.Surjective residueMap
  residueIdeal : Ideal integralModel
  residueMap_kernel : RingHom.ker residueMap = residueIdeal
  integralModel_fractionRing : IsFractionRing integralModel L
  integralModel_etale : Algebra.Etale A integralModel
  /-- The displayed local field is the field factor represented by the
  selected lifted residue factor, rather than an unrelated field with the
  same numerical profile. -/
  factor_quotient_equiv : Nonempty
    (L ≃ₐ[K]
      Chapter07LiftedPolynomialQuotient K
        (chapter07LiftedPolynomial (G.factors i)))
  residueMap_compatible :
    residueMap.comp (algebraMap A integralModel) =
      (algebraMap k l).comp res

/-- A chosen residue-field shadow of an intermediate unramified extension. -/
structure Chapter07IntermediateResidueShadow
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    where
  residue : IntermediateField k κ
  [residueFinite : FiniteDimensional k residue]
  profile : Chapter07FiniteLocalExtensionData K E k residue
  actual :
    Chapter07ActualUnramifiedIntermediateData K Ω k κ E residue profile

/- A residue shadow is defined only on the witnessed unramified carriers.  A
global lattice map on all intermediate fields would incorrectly assign residue
fields to ramified or otherwise unvalued intermediate extensions. -/
structure Chapter07ResidueShadowFunctoriality
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ] where
  classification :
    Chapter07CanonicalUnramifiedClassification K Ω k κ

/-- The residue-field equalities for composita and intersections, with the
chosen reduction equivalence on witnessed unramified carriers made explicit. -/
theorem chapter07_unramified_residue_compositum_and_intersection
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E F : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ)
    (R : Chapter07ResidueShadowFunctoriality K Ω k κ) :
    (∃ G : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
      G.1 = chapter07CanonicalUnramifiedCompositum E F ∧
        (R.classification.reduction G).1 =
          chapter07CanonicalResidueCompositum
            (R.classification.reduction E) (R.classification.reduction F)) ∧
      (∃ G : Chapter07CanonicalFiniteUnramifiedIntermediate K Ω k κ,
        G.1 = chapter07CanonicalUnramifiedIntersection E F ∧
          (R.classification.reduction G).1 =
              chapter07CanonicalResidueIntersection
                (R.classification.reduction E) (R.classification.reduction F)) := by
  exact ⟨R.classification.compositum_preserved E F,
    R.classification.intersection_preserved E F⟩

/-- The residue tensor product is finite étale over the changed residue field,
hence a finite product of separable fields. -/
theorem chapter07_residue_tensor_product_is_separable_product
    {k k' l : Type*} [Field k] [Field k'] [Field l]
    [Algebra k k'] [Algebra k l] [FiniteDimensional k l]
    [Algebra.IsSeparable k l] :
    Chapter07FiniteEtaleExtension k' (l ⊗[k] k') := by
  sorry

/-- A finite product of unramified factors after scalar extension. -/
structure Chapter07UnramifiedScalarExtensionProduct
    (K K' L k k' l : Type*) [Field K] [Field K'] [Field L]
    [Field k] [Field k'] [Field l] [Algebra K K'] [Algebra K L]
    [Algebra k k'] [Algebra k l] (r : ℕ)
    (vK' : Valuation K' ℤᵐ⁰)
    (baseResidueIdentification : Chapter10ResidueField vK' ≃+* k')
    [FiniteDimensional K K'] [FiniteDimensional K L]
    [FiniteDimensional k l] where
  factor : Fin r → Type uFactor
  [factorField : ∀ i, Field (factor i)]
  [factorAlgebra : ∀ i, Algebra K' (factor i)]
  [factorFinite : ∀ i, FiniteDimensional K' (factor i)]
  residue : Fin r → Type uFactor
  [residueField : ∀ i, Field (residue i)]
  [residueAlgebra : ∀ i, Algebra k' (residue i)]
  [residueFinite : ∀ i, FiniteDimensional k' (residue i)]
  profile : ∀ i,
    Chapter07FiniteLocalExtensionData K' (factor i) k' (residue i)
  unramified : ∀ i, Chapter07UnramifiedExtension (profile i)
  factorValuation : ∀ i, Valuation (factor i) ℤᵐ⁰
  factorValuation_extension : ∀ i,
    vK'.IsEquiv
      ((factorValuation i).comap (algebraMap K' (factor i)))
  factorResidueIdentification : ∀ i,
    Chapter10ResidueField (factorValuation i) ≃+* (residue i)
  factorResidueMap : ∀ i,
    Chapter10ResidueField vK' →+*
      Chapter10ResidueField (factorValuation i)
  factorResidueMap_compatible : ∀ i,
    (factorResidueIdentification i).toRingHom.comp (factorResidueMap i) =
      (algebraMap k' (residue i)).comp baseResidueIdentification.toRingHom
  factorExtensionData : ∀ i,
    Chapter10HeterogeneousExtensionData vK' (factorValuation i)
      (factorValuation_extension i)
  factorProfile_ramificationIndex : ∀ i,
    (profile i).ramificationIndex = (factorExtensionData i).ramificationIndex
  factorProfile_residueDegree : ∀ i,
    (profile i).residueDegree = (factorExtensionData i).residueDegree
  productEquiv : Nonempty
    (L ⊗[K] K' ≃ₐ[K'] (∀ i, factor i))

/-- Hensel lifting of the residue idempotents gives the product decomposition
of an unramified scalar extension. -/
theorem chapter07_unramified_scalar_extension_is_product
    {K K' L k k' l : Type*} [Field K] [Field K'] [Field L]
    [Field k] [Field k'] [Field l] [Algebra K K'] [Algebra K L]
    [Algebra k k'] [Algebra k l] [FiniteDimensional K K']
    [FiniteDimensional K L] [FiniteDimensional k l]
    [Algebra.IsSeparable k l]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hE : Chapter07UnramifiedExtension E)
    (hLseparable : Algebra.IsSeparable K L)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (baseResidueIdentification : Chapter10ResidueField vK ≃+* k)
    (extensionResidueIdentification : Chapter10ResidueField vL ≃+* l)
    (residueMap : Chapter10ResidueField vK →+* Chapter10ResidueField vL)
    (residueMap_compatible :
      extensionResidueIdentification.toRingHom.comp residueMap =
        (algebraMap k l).comp baseResidueIdentification.toRingHom)
    (vK' : Valuation K' ℤᵐ⁰) [Valuation.IsRankOneDiscrete vK']
    (baseChangeValuation : vK.IsEquiv (vK'.comap (algebraMap K K')))
    (baseChangeComplete :
      IsAdicComplete (IsLocalRing.maximalIdeal vK'.valuationSubring)
        vK'.valuationSubring)
    (baseChangeResidueIdentification : Chapter10ResidueField vK' ≃+* k')
    (d : Chapter10HeterogeneousExtensionData vK vL hext)
    (hprofile : E.ramificationIndex = d.ramificationIndex ∧
      E.residueDegree = d.residueDegree) :
    ∃ r : ℕ, Nonempty
      (Chapter07UnramifiedScalarExtensionProduct K K' L k k' l r vK'
        baseChangeResidueIdentification) := by
  sorry

theorem chapter07_galois_over_intersection_linearly_disjoint
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (K₁ K₂ : IntermediateField K Ω)
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    [IsGalois (↥(K₁ ⊓ K₂))
      (↥(IntermediateField.extendScalars
        (F := K₁ ⊓ K₂) (E := K₁) inf_le_left))] :
    (IntermediateField.extendScalars
      (F := K₁ ⊓ K₂) (E := K₁) inf_le_left).LinearDisjoint
      (IntermediateField.extendScalars
        (F := K₁ ⊓ K₂) (E := K₂) inf_le_right) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
