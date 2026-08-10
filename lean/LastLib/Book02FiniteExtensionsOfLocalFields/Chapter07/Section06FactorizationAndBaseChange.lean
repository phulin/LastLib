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
  have hcop : ∀ i j : Fin r, i ≠ j → IsCoprime (gᵢ i) (gᵢ j) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp (hpairwise hij)
  let f : Fin r → Ideal K[X] := fun i => Ideal.span ({gᵢ i} : Set K[X])
  have hpair : Pairwise (fun i j => IsCoprime (f i) (f j)) := by
    intro i j hij
    exact hpairwise hij
  have hspan : Ideal.span ({g} : Set K[X]) = ⨅ i, f i := by
    rw [hproduct]
    exact (Ideal.iInf_span_singleton hcop).symm
  constructor
  · refine ⟨(Ideal.quotEquivOfEq hspan).trans
      (Ideal.quotientInfRingEquivPiQuotient f hpair)⟩
  · intro i
    letI : Fact (Irreducible (gᵢ i)) := ⟨hirreducible i⟩
    letI : Field (AdjoinRoot (gᵢ i)) := inferInstance
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
    (i : Fin r) where
  profile : Chapter07FiniteLocalExtensionData K L k l
  unramified : Chapter07UnramifiedExtension profile
  residue_degree : profile.residueDegree = (F.factors i).natDegree
  residue_separable : Chapter07ResidueExtensionIsSeparable k l

/-- The residue tensor product is finite étale over the changed residue field,
hence a finite product of separable fields. -/
theorem chapter07_residue_tensor_product_is_separable_product
    {k k' l : Type*} [Field k] [Field k'] [Field l]
    [Algebra k k'] [Algebra k l] [FiniteDimensional k l]
    [Algebra.IsSeparable k l] :
    Algebra.Etale k' (l ⊗[k] k') := by
  letI : Algebra.FormallyEtale k l :=
    Algebra.FormallyEtale.of_isSeparable k l
  letI : Algebra.FinitePresentation k l :=
    Algebra.FinitePresentation.of_finiteType.mp
      (inferInstance : Algebra.FiniteType k l)
  letI : Algebra.Etale k l := ⟨inferInstance, inferInstance⟩
  let e : l ⊗[k] k' ≃ₐ[k'] k' ⊗[k] l :=
    .ofRingEquiv (f := Algebra.TensorProduct.comm k l k') (by
      intro x
      simp [RingHom.algebraMap_toAlgebra])
  exact Algebra.Etale.of_equiv e.symm

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
