import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section06QuadraticLaboratory

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Filter Topology
open scoped BigOperators

/-! ## 3.7. Continuity of embeddings -/

/-- Exact extension of a valuation along a field algebra. -/
def chapter03ValuationExtendsExactly
    {K L Γ : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L]
    (vK : Valuation K Γ) (vL : Valuation L Γ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = vK x

/-- Uniqueness of the normalized valuation extension in a fixed value group. -/
def chapter03UniqueNormalizedValuationExtension
    {K L Γ : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L]
    (vK : Valuation K Γ) (vL : Valuation L Γ) : Prop :=
  chapter03ValuationExtendsExactly vK vL ∧
    ∀ w : Valuation L Γ,
      chapter03ValuationExtendsExactly vK w → w = vL

/--
Valuation data for the pullback of an ambient valuation along an algebraic
embedding.  The pullback is a valuation on L, and the compatibility field is
the equation used to identify it with the unique normalized extension.
-/
structure Chapter03ValuedEmbeddingData
    {K L Ω Γ : Type*} [Field K] [Field L] [Field Ω]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L] [Algebra K Ω]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (vΩ : Valuation Ω Γ)
    (σ : L →ₐ[K] Ω) where
  injective : Function.Injective σ
  pullback : Valuation L Γ
  pullback_extends : chapter03ValuationExtendsExactly vK pullback
  ambient_compatibility : ∀ x : L, vΩ (σ x) = pullback x

/-- An embedding into a uniquely valued algebraic extension preserves values. -/
theorem chapter03_embedding_preserves_normalized_valuation
    {K L Ω Γ : Type*} [Field K] [Field L] [Field Ω]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L] [Algebra K Ω]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (vΩ : Valuation Ω Γ)
    (σ : L →ₐ[K] Ω)
    (hunique : chapter03UniqueNormalizedValuationExtension vK vL)
    (D : Chapter03ValuedEmbeddingData vK vL vΩ σ) :
    ∀ x : L, vΩ (σ x) = vL x := by
  intro x
  rw [D.ambient_compatibility]
  rw [hunique.2 D.pullback D.pullback_extends]

/-- Norm equality is the metric form of continuity for a valued embedding. -/
def chapter03IsometricEmbedding
    {L Ω : Type*} [Norm L] [Norm Ω] (σ : L → Ω) : Prop :=
  ∀ x : L, ‖σ x‖ = ‖x‖

theorem chapter03_algebraic_embedding_is_isometric_and_continuous
    {K L Ω : Type*} [NormedField K] [NormedField L] [NormedField Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
    (σ : L →ₐ[K] Ω)
    (hnorm : chapter03IsometricEmbedding σ) :
    Isometry σ ∧ Continuous σ := by
  sorry

/-- Galois automorphisms are continuous for the extending local absolute value. -/
theorem chapter03_galois_action_is_continuous
    {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (hnorm : ∀ x : L, ‖σ x‖ = ‖x‖) :
    Continuous σ := by
  sorry

/-- Trace and norm are continuous finite algebraic operations. -/
theorem chapter03_trace_and_norm_are_continuous
    {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    [FiniteDimensional K L] :
    Continuous (fun x : L => Algebra.trace K L x) ∧
      Continuous (fun x : L => Algebra.norm K x) := by
  sorry

/-- Finite sums and products commute with limits in a topological semiring. -/
theorem chapter03_finite_sums_and_products_commute_with_limits
    {X ι : Type*} [TopologicalSpace X] [CommSemiring X]
    [IsTopologicalSemiring X]
    [Fintype ι] (f : ι → ℕ → X) (x : ι → X)
    (hlim : ∀ i, Tendsto (f i) atTop (𝓝 (x i))) :
    Tendsto (fun n => ∑ i, f i n) atTop (𝓝 (∑ i, x i)) ∧
      Tendsto (fun n => ∏ i, f i n) atTop (𝓝 (∏ i, x i)) := by
  sorry

/-- The same limit statement applies to a finite family of embeddings. -/
theorem chapter03_finite_embedding_products_preserve_limits
    {X ι : Type*} [TopologicalSpace X] [CommSemiring X]
    [IsTopologicalSemiring X]
    [Fintype ι] (f : ι → ℕ → X) (x : ι → X)
    (hlim : ∀ i, Tendsto (f i) atTop (𝓝 (x i))) :
    Tendsto (fun n => ∏ i, f i n) atTop (𝓝 (∏ i, x i)) := by
  exact (chapter03_finite_sums_and_products_commute_with_limits f x hlim).2

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
