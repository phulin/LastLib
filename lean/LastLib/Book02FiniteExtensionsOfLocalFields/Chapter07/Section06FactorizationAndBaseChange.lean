import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section05ExamplesBothCharacteristics

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open scoped BigOperators TensorProduct

noncomputable section

-- The tensor product has a canonical right-factor algebra structure, but
-- Mathlib keeps it local to avoid ambiguity with the left-factor action.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! # Book 2, Chapter 7, §7.6: unramified factorization and base change -/

/-- The compositum and intersection operations in a fixed common field. -/
def chapter07IntermediateCompositum
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (K₁ K₂ : IntermediateField K Ω) : IntermediateField K Ω :=
  K₁ ⊔ K₂

def chapter07IntermediateIntersection
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (K₁ K₂ : IntermediateField K Ω) : IntermediateField K Ω :=
  K₁ ⊓ K₂

/-- Tensor-product injectivity is the standard field-theoretic meaning of
linear disjointness over the intersection field. -/
def Chapter07LinearlyDisjointOver
    (K₀ K₁ K₂ Ω : Type*) [Field K₀] [Field K₁] [Field K₂] [Field Ω]
    [Algebra K₀ K₁] [Algebra K₀ K₂] [Algebra K₁ Ω] [Algebra K₂ Ω]
    [Algebra K₀ Ω] [IsScalarTower K₀ K₁ Ω] [IsScalarTower K₀ K₂ Ω] : Prop :=
  Function.Injective
    (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom K₀ K₁ Ω)
      (IsScalarTower.toAlgHom K₀ K₂ Ω)
      (fun _ _ => Commute.all _ _))

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
    (hmonic : ∀ i, (gᵢ i).Monic)
    (hirreducible : ∀ i, Irreducible (gᵢ i))
    (hpairwise : Pairwise (fun i j => IsCoprime (Ideal.span ({gᵢ i} : Set K[X]))
      (Ideal.span ({gᵢ j} : Set K[X])))) :
    Nonempty (AdjoinRoot g ≃+* (∀ i, AdjoinRoot (gᵢ i))) ∧
      ∀ i, IsField (AdjoinRoot (gᵢ i)) := by
  sorry

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
    (i : Fin r) where
  profile : Chapter07FiniteLocalExtensionData K L k l
  unramified : Chapter07UnramifiedExtension profile
  residue_degree : profile.residueDegree = (F.factors i).natDegree
  residue_separable : Chapter07ResidueExtensionIsSeparable k l

/-- A chosen residue-field shadow of an intermediate unramified extension. -/
structure Chapter07IntermediateResidueShadow
    (K Ω k κ : Type*) [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (E : IntermediateField K Ω) [FiniteDimensional K E]
    where
  residue : IntermediateField k κ
  [residueFinite : FiniteDimensional k residue]
  profile : Chapter07FiniteLocalExtensionData K E k residue
  unramified : Chapter07UnramifiedExtension profile

/-- The residue-field equalities for composita and intersections, with the
chosen residue shadows made explicit. -/
theorem chapter07_unramified_residue_compositum_and_intersection
    {K Ω k κ : Type*} [Field K] [Field Ω] [Field k] [Field κ]
    [Algebra K Ω] [Algebra k κ]
    (K₁ K₂ : IntermediateField K Ω)
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    [FiniteDimensional K (K₁ ⊔ K₂)] [FiniteDimensional K (K₁ ⊓ K₂)]
    (S₁ : Chapter07IntermediateResidueShadow K Ω k κ K₁)
    (S₂ : Chapter07IntermediateResidueShadow K Ω k κ K₂)
    (S₁₂ : Chapter07IntermediateResidueShadow K Ω k κ (K₁ ⊔ K₂))
    (S₀ : Chapter07IntermediateResidueShadow K Ω k κ (K₁ ⊓ K₂)) :
    S₁₂.residue = S₁.residue ⊔ S₂.residue ∧
      S₀.residue = S₁.residue ⊓ S₂.residue := by
  sorry

/-- The residue tensor product is finite étale over the changed residue field,
hence a finite product of separable fields. -/
theorem chapter07_residue_tensor_product_is_separable_product
    {k k' l : Type*} [Field k] [Field k'] [Field l]
    [Algebra k k'] [Algebra k l] [FiniteDimensional k l]
    [Algebra.IsSeparable k l] :
    Algebra.Etale k' (l ⊗[k] k') := by
  sorry

/-- A finite product of unramified factors after scalar extension. -/
structure Chapter07UnramifiedScalarExtensionProduct
    (K K' L k k' l : Type*) [Field K] [Field K'] [Field L]
    [Field k] [Field k'] [Field l] [Algebra K K'] [Algebra K L]
    [Algebra k k'] [Algebra k l] (r : ℕ)
    [FiniteDimensional K K'] [FiniteDimensional K L]
    [FiniteDimensional k l] where
  factor : Fin r → Type*
  [factorField : ∀ i, Field (factor i)]
  [factorAlgebra : ∀ i, Algebra K' (factor i)]
  [factorFinite : ∀ i, FiniteDimensional K' (factor i)]
  residue : Fin r → Type*
  [residueField : ∀ i, Field (residue i)]
  [residueAlgebra : ∀ i, Algebra k' (residue i)]
  [residueFinite : ∀ i, FiniteDimensional k' (residue i)]
  profile : ∀ i,
    Chapter07FiniteLocalExtensionData K' (factor i) k' (residue i)
  unramified : ∀ i, Chapter07UnramifiedExtension (profile i)
  productEquiv : Nonempty
    (L ⊗[K] K' ≃+* (∀ i, factor i))

/-- Hensel lifting of the residue idempotents gives the product decomposition
of an unramified scalar extension. -/
theorem chapter07_unramified_scalar_extension_is_product
    {K K' L k k' l : Type*} [Field K] [Field K'] [Field L]
    [Field k] [Field k'] [Field l] [Algebra K K'] [Algebra K L]
    [Algebra k k'] [Algebra k l] [FiniteDimensional K K']
    [FiniteDimensional K L] [FiniteDimensional k l]
    [Algebra.IsSeparable k l]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hE : Chapter07UnramifiedExtension E) :
    ∃ r : ℕ, Nonempty
      (Chapter07UnramifiedScalarExtensionProduct K K' L k k' l r) := by
  sorry

-- SOURCE_ISSUE: The source's unconditional linear-disjointness sentence is
-- false for arbitrary finite separable residue extensions.  The minimal
-- correction here assumes finite Galois residue extensions, which is the
-- situation in the finite-field tower of §7.4.
theorem chapter07_finite_galois_residue_extensions_linearly_disjoint
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (K₁ K₂ : IntermediateField K Ω)
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    [IsGalois K K₁] [IsGalois K K₂] :
      Chapter07LinearlyDisjointOver
        (↥(K₁ ⊓ K₂))
        (↥(IntermediateField.extendScalars
          (F := K₁ ⊓ K₂) (E := K₁) inf_le_left))
        (↥(IntermediateField.extendScalars
          (F := K₁ ⊓ K₂) (E := K₂) inf_le_right)) Ω := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
