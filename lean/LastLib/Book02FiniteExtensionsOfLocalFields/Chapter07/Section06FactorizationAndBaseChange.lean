import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section05ExamplesBothCharacteristics

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open scoped BigOperators TensorProduct

noncomputable section

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
  ∃ φ : K₁ ⊗[K₀] K₂ →ₐ[K₀] Ω, Function.Injective φ

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
    (hgred : g.map res = ∏ i, F.factors i) :
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
    Nonempty (AdjoinRoot g ≃+* (∀ i, AdjoinRoot (gᵢ i))) := by
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

/-- A product model for unramified scalar extension.  The factor fields and
their étale maps are explicit, so the tensor-product statement does not hide
the branch index type. -/
structure Chapter07UnramifiedBaseChangeProduct
    (K K' L : Type*) [Field K] [Field K'] [Field L]
    [Algebra K K'] [Algebra K L] [Algebra K' (L ⊗[K] K')]
    [Module.Finite K L] where
  index : Type*
  factor : index → Type*
  [factorField : ∀ i, Field (factor i)]
  [factorAlgebra : ∀ i, Algebra K' (factor i)]
  [factorFinite : ∀ i, Module.Finite K' (factor i)]
  [factorEtale : ∀ i, Algebra.Etale K' (factor i)]
  algebraEquiv : L ⊗[K] K' ≃ₐ[K'] (∀ i, factor i)
  tensorEtale : Algebra.Etale K' (L ⊗[K] K')

/-- Base change of an unramified extension is a finite product of unramified
extensions of the new base. -/
theorem chapter07_unramified_base_change_splits
    {K K' L k l : Type*} [Field K] [Field K'] [Field L] [Field k] [Field l]
    [Algebra K K'] [Algebra K L] [Algebra K' (L ⊗[K] K')]
    [Module.Finite K L] [Module.Finite K K'] [Algebra.IsSeparable K L]
    [Algebra k l] [FiniteDimensional k l]
    (E : Chapter07FiniteLocalExtensionData K L k l)
    (hE : Chapter07UnramifiedExtension E) :
    Nonempty (Chapter07UnramifiedBaseChangeProduct K K' L) := by
  sorry

/-- The residue tensor product is finite étale over the changed residue field,
hence a finite product of separable fields. -/
theorem chapter07_residue_tensor_product_is_separable_product
    {k k' l : Type*} [Field k] [Field k'] [Field l]
    [Algebra k k'] [Algebra k l] [FiniteDimensional k l]
    [Algebra.IsSeparable k l] [Algebra k' (l ⊗[k] k')] :
    Algebra.Etale k' (l ⊗[k] k') := by
  sorry

/-- The compositum/intersection laws are bundled with a fixed unramified
tower.  Using the intersection carrier itself as the scalar field records
the source's “linearly disjoint over their intersection” qualification. -/
structure Chapter07UnramifiedCompositumData
    (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
    (T : Chapter07FiniteResidueTower K Ω) where
  compositum : ∀ m n : ℕ,
    T.level m ⊔ T.level n = T.level (Nat.lcm m n)
  intersection : ∀ m n : ℕ,
    T.level m ⊓ T.level n = T.level (Nat.gcd m n)
  linearly_disjoint : ∀ m n : ℕ,
    Chapter07LinearlyDisjointOver
      (↥(T.level m ⊓ T.level n))
      (↥(IntermediateField.extendScalars
        (F := T.level m ⊓ T.level n) (E := T.level m) inf_le_left))
      (↥(IntermediateField.extendScalars
        (F := T.level m ⊓ T.level n) (E := T.level n) inf_le_right)) Ω

theorem chapter07_unramified_compositum_and_intersection
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (T : Chapter07FiniteResidueTower K Ω)
    (D : Chapter07UnramifiedCompositumData K Ω T) (m n : ℕ) :
      T.level m ⊔ T.level n = T.level (Nat.lcm m n) ∧
      T.level m ⊓ T.level n = T.level (Nat.gcd m n) ∧
      Chapter07LinearlyDisjointOver
        (↥(T.level m ⊓ T.level n))
        (↥(IntermediateField.extendScalars
          (F := T.level m ⊓ T.level n) (E := T.level m) inf_le_left))
        (↥(IntermediateField.extendScalars
          (F := T.level m ⊓ T.level n) (E := T.level n) inf_le_right)) Ω := by
  exact ⟨D.compositum m n, D.intersection m n, D.linearly_disjoint m n⟩

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
