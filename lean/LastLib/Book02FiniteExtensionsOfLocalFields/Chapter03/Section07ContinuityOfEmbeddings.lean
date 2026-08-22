import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section04AbsoluteValueNormalizations

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Filter Topology
open scoped BigOperators

/-! ## 3.7. Continuity of embeddings -/

/-- Literal extension of a valuation along a field algebra. -/
def chapter03ValuationExtendsExactly
    {K L Γ : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L]
    (vK : Valuation K Γ) (vL : Valuation L Γ) : Prop :=
  ∀ x : K, vL (algebraMap K L x) = vK x

/-- Uniqueness of a normalized valuation extension in a fixed value group. -/
def chapter03UniqueNormalizedValuationExtension
    {K L Γ : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L]
    (vK : Valuation K Γ) (vL : Valuation L Γ) : Prop :=
  chapter03ValuationExtendsExactly vK vL ∧
    ∀ w : Valuation L Γ,
      chapter03ValuationExtendsExactly vK w → w = vL

@[simp] theorem chapter03ValuationExtendsExactly_iff
    {K L Γ : Type*} [Field K] [Field L]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L]
    (vK : Valuation K Γ) (vL : Valuation L Γ) :
    chapter03ValuationExtendsExactly vK vL ↔
      ∀ x : K, vL (algebraMap K L x) = vK x := Iff.rfl

/-- Data expressing that an ambient valuation pulls back to the unique one on
the embedded field. -/
structure Chapter03ValuedEmbeddingData
    {K L Ω Γ : Type*} [Field K] [Field L] [Field Ω]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L] [Algebra K Ω]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (vΩ : Valuation Ω Γ)
    (σ : L →ₐ[K] Ω) where
  pullback : Valuation L Γ
  pullback_extends : chapter03ValuationExtendsExactly vK pullback
  ambient_compatibility : ∀ x : L, vΩ (σ x) = pullback x

theorem chapter03_embedding_preserves_normalized_valuation
    {K L Ω Γ : Type*} [Field K] [Field L] [Field Ω]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L] [Algebra K Ω]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (vΩ : Valuation Ω Γ)
    (σ : L →ₐ[K] Ω)
    (hunique : chapter03UniqueNormalizedValuationExtension vK vL)
    (D : Chapter03ValuedEmbeddingData vK vL vΩ σ) :
    ∀ x : L, vΩ (σ x) = vL x := by
  intro x
  rw [D.ambient_compatibility x, hunique.2 D.pullback D.pullback_extends]

/-- An ambient valuation extending the base valuation automatically pulls back
to the unique normalized valuation on an embedded finite extension. -/
theorem chapter03_embedding_preserves_normalized_valuation_of_base_extension
    {K L Ω Γ : Type*} [Field K] [Field L] [Field Ω]
    [LinearOrderedCommGroupWithZero Γ] [Algebra K L] [Algebra K Ω]
    (vK : Valuation K Γ) (vL : Valuation L Γ) (vΩ : Valuation Ω Γ)
    (σ : L →ₐ[K] Ω)
    (hunique : chapter03UniqueNormalizedValuationExtension vK vL)
    (hΩ : chapter03ValuationExtendsExactly vK vΩ) :
    ∀ x : L, vΩ (σ x) = vL x := by
  let w := vΩ.comap σ.toRingHom
  have hw : chapter03ValuationExtendsExactly vK w := by
    intro x
    simpa [w, chapter03ValuationExtendsExactly] using hΩ x
  have hw_eq : w = vL := hunique.2 w hw
  intro x
  simpa [w] using congrArg (fun z : Valuation L Γ => z x) hw_eq

/-- The value of a normalized additive valuation after dividing by its scale. -/
def chapter03NormalizedValuationValue
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (e : ℕ) (_he : 0 < e) : K → ℝ :=
  by
    classical
    exact fun x => if x = 0 then 0 else
      (((v x).untopD 0 : ℤ) : ℝ) / (e : ℝ)

/-- The scale-independent normalized valuation formula along an embedding. -/
theorem chapter03_embedding_preserves_normalized_valuation_ratio
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω]
    (vL : AddValuation L (WithTop ℤ))
    (vΩ : AddValuation Ω (WithTop ℤ))
    (eΩL eLK eΩK : ℕ)
    (heΩL : 0 < eΩL) (heLK : 0 < eLK)
    (heΩK : eΩK = eΩL * eLK)
    (σ : L →ₐ[K] Ω)
    (hscale : ∀ x : L, x ≠ 0 → vΩ (σ x) = eΩL • vL x) :
    ∀ x : L,
      chapter03NormalizedValuationValue vΩ eΩK (by
        rw [heΩK]
        exact Nat.mul_pos heΩL heLK) (σ x) =
        chapter03NormalizedValuationValue vL eLK heLK x := by
  intro x
  by_cases hx : x = 0
  · simp [chapter03NormalizedValuationValue, hx]
  · have hσ : σ x ≠ 0 := (map_ne_zero_iff σ σ.injective).2 hx
    simp only [chapter03NormalizedValuationValue, if_neg hσ, if_neg hx]
    have hvL : vL x ≠ ⊤ := (vL.ne_top_iff).2 hx
    obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp hvL
    have hv := hscale x hx
    rw [← hz] at hv
    have hnsmul : ∀ n : ℕ, n • (z : WithTop ℤ) = (n * z : ℤ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [succ_nsmul, ih]
          norm_cast
          simp only [Nat.cast_add, Nat.cast_one]
          ring
    have hv' : vΩ (σ x) = (eΩL * z : ℤ) := by
      simpa [hnsmul] using hv
    rw [hv']
    rw [← hz]
    simp only [WithTop.untopD_coe, Int.cast_mul]
    rw [heΩK]
    field_simp
    norm_num [Nat.cast_mul]
    ring

/-- The equivalent absolute-value restriction statement. -/
theorem chapter03_embedding_preserves_base_compatible_absolute_value
    {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω]
    (c : ℝ) (hc : 0 < c ∧ c < 1)
    (vL : AddValuation L (WithTop ℤ))
    (vΩ : AddValuation Ω (WithTop ℤ)) (e : ℕ) (he : 0 < e)
    (σ : L →ₐ[K] Ω)
    (hscale : ∀ x : L, x ≠ 0 → vΩ (σ x) = e • vL x) :
    letI : Algebra L Ω := σ.toRingHom.toAlgebra
    ∀ x : L,
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01RelativeAbsoluteValue
          (K := L) (L := Ω) c vΩ e (σ x) =
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01BaseAbsoluteValue c vL x := by
  exact @LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01_relative_absolute_value_restricts
    L Ω _ _ (σ.toRingHom.toAlgebra) c hc vL vΩ e ⟨he, hscale⟩

/-- Norm equality is the metric form of an isometric embedding. -/
def chapter03IsometricEmbedding
    {L Ω : Type*} [Norm L] [Norm Ω] (σ : L → Ω) : Prop :=
  ∀ x : L, ‖σ x‖ = ‖x‖

/- A finite-dimensional normed-algebra embedding over a complete nontrivial
   base is continuous.  Isometry is provided by the valuation-normalization
   results above once the norms are the corresponding local norms. -/
theorem chapter03_algebraic_embedding_is_continuous
    {K L Ω : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedField L] [NormedField Ω]
    [NormedAlgebra K L] [NormedAlgebra K Ω] [FiniteDimensional K L]
    (σ : L →ₐ[K] Ω) :
    Continuous σ := by
  sorry

/-- Galois automorphisms are continuous for the extending local absolute value. -/
theorem chapter03_galois_action_is_continuous
    {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (hnorm : ∀ x : L, ‖σ x‖ = ‖x‖) :
    Continuous σ := by
  exact (AddMonoidHomClass.isometry_of_norm σ hnorm).continuous

/-- Trace and norm are continuous finite algebraic operations over a complete
nontrivially normed base. -/
theorem chapter03_trace_and_norm_are_continuous
    {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [NormedField L] [NormedAlgebra K L]
    [FiniteDimensional K L] :
    Continuous (fun x : L => Algebra.trace K L x) ∧
      Continuous (fun x : L => Algebra.norm K x) := by
  sorry

/-- Finite sums and products commute with limits in a topological semiring. -/
theorem chapter03_finite_sums_and_products_commute_with_limits
    {X ι : Type*} [TopologicalSpace X] [CommSemiring X]
    [IsTopologicalSemiring X] [Fintype ι]
    (f : ι → ℕ → X) (x : ι → X)
    (hlim : ∀ i, Tendsto (f i) atTop (𝓝 (x i))) :
    Tendsto (fun n => ∑ i, f i n) atTop (𝓝 (∑ i, x i)) ∧
      Tendsto (fun n => ∏ i, f i n) atTop (𝓝 (∏ i, x i)) := by
  refine ⟨?_, ?_⟩
  · simpa using (tendsto_finsetSum (Finset.univ : Finset ι) (fun i _ => hlim i))
  · simpa using (tendsto_finsetProd (Finset.univ : Finset ι) (fun i _ => hlim i))

/-- The product half of the preceding finite-limit interface. -/
theorem chapter03_finite_embedding_products_preserve_limits
    {X ι : Type*} [TopologicalSpace X] [CommSemiring X]
    [IsTopologicalSemiring X] [Fintype ι]
    (f : ι → ℕ → X) (x : ι → X)
    (hlim : ∀ i, Tendsto (f i) atTop (𝓝 (x i))) :
    Tendsto (fun n => ∏ i, f i n) atTop (𝓝 (∏ i, x i)) := by
  exact (chapter03_finite_sums_and_products_commute_with_limits f x hlim).2

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
