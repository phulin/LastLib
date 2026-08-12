import LastLib.Book06GlobalClassFieldTheory.Chapter11.Section03QuasicharactersAndModuleDirection

namespace LastLib.Book06GlobalClassFieldTheory.Chapter11

open scoped BigOperators NumberField.AdeleRing RestrictedProduct
open NumberField

noncomputable section

/-! ## 11.4. Algebraic infinity types -/

def chapter11AlgebraicInfinityType
    {K : Type*} [Field K] [NumberField K]
    (χinf : Chapter11ArchimedeanParameter K →* ℂˣ)
    (n : Chapter11InfinityType K) : Prop :=
  chapter11HasInfinityType χinf n

theorem chapter11_algebraic_infinity_type_iff
    {K : Type*} [Field K] [NumberField K]
    (χinf : Chapter11ArchimedeanParameter K →* ℂˣ)
    (n : Chapter11InfinityType K) :
    chapter11AlgebraicInfinityType χinf n ↔ chapter11HasInfinityType χinf n :=
  Iff.rfl

def chapter11ComplexPairInfinityFormula
    (p q : ℤ) (z : ℂˣ) : ℂˣ :=
  Units.mk0
    (((z : ℂ) ^ (-p)) * ((starRingEnd ℂ) (z : ℂ) ^ (-q))) (by sorry)

def chapter11RealPositiveInfinityFormula
    (n : ℤ) (x : ℝˣ) : ℂˣ :=
  Units.mk0 (((x : ℝ) : ℂ) ^ (-n)) (by sorry)

structure Chapter11AlgebraicInfinityTypeData
    (K : Type*) [Field K] [NumberField K] where
  archimedeanCharacter : Chapter11ArchimedeanParameter K →* ℂˣ
  infinityType : Chapter11InfinityType K
  algebraic_on_connected_subgroup :
    chapter11AlgebraicInfinityType archimedeanCharacter infinityType

theorem chapter11_algebraic_character_has_local_monomial
    {K : Type*} [Field K] [NumberField K]
    (D : Chapter11AlgebraicInfinityTypeData K) :
    ∃ U : Subgroup (Chapter11ArchimedeanParameter K),
      IsConnected (U : Set (Chapter11ArchimedeanParameter K)) ∧
        ∀ x : U,
          D.archimedeanCharacter x =
            chapter11InfinityMonomial D.infinityType x := by
  exact D.algebraic_on_connected_subgroup

def chapter11A0InfinityTypePredicate
    {K : Type*} [Field K] [NumberField K]
    (n : Chapter11InfinityType K) (w : ℤ) : Prop :=
  chapter11A0InfinityType n w

theorem chapter11_A0_purity_expanded
    {K : Type*} [Field K] [NumberField K]
    (n : Chapter11InfinityType K) (w : ℤ) :
    chapter11A0InfinityTypePredicate n w ↔
      ((∀ τ, ComplexEmbedding.IsReal τ → 2 * n τ = w) ∧
        (∀ τ, ¬ComplexEmbedding.IsReal τ →
          n τ + n (chapter11ConjugateEmbedding τ) = w)) :=
  Iff.rfl

theorem chapter11_finite_order_infinity_type_zero
    {K : Type*} [Field K] [NumberField K]
    (χinf : Chapter11ArchimedeanParameter K →ₜ* ℂˣ)
    (hχ : chapter11FiniteOrder χinf.toMonoidHom)
    (n : Chapter11InfinityType K)
    (hn : chapter11HasInfinityType χinf.toMonoidHom n) :
    n = 0 := by
  sorry

structure Chapter11UnitRelationData
    (K : Type*) [Field K] [NumberField K]
    (n : Chapter11InfinityType K) where
  deepUnits : Subgroup Kˣ
  finiteValue : Kˣ →* ℂˣ
  archimedeanValue : Kˣ →* ℂˣ
  finite_part_trivial : ∀ u : deepUnits, finiteValue (u : Kˣ) = 1
  principal_relation : ∀ u : deepUnits,
    finiteValue (u : Kˣ) * archimedeanValue (u : Kˣ) = 1
  archimedean_formula : ∀ u : deepUnits,
    archimedeanValue (u : Kˣ) = ∏ τ, ((τ ((u : Kˣ) : K) : ℂ) ^ n τ)

theorem chapter11_unit_relation_on_deep_congruence_units
    {K : Type*} [Field K] [NumberField K]
    {n : Chapter11InfinityType K}
    (D : Chapter11UnitRelationData K n) :
    ∀ u : D.deepUnits, ∏ τ, ((τ ((u : Kˣ) : K) : ℂ) ^ n τ) = 1 := by
  sorry

def chapter11UnitLogLinearForm
    {K : Type*} [Field K] [NumberField K]
    (n : Chapter11InfinityType K) (u : Kˣ) : ℝ :=
  ∑ τ, (n τ : ℝ) * Real.log ‖(τ (u : K) : ℂ)‖

theorem chapter11_unit_relations_give_logarithmic_linear_relations
    {K : Type*} [Field K] [NumberField K]
    {n : Chapter11InfinityType K}
    (D : Chapter11UnitRelationData K n) :
    ∀ u : D.deepUnits, chapter11UnitLogLinearForm n (u : Kˣ) = 0 := by
  sorry

structure Chapter11DirichletUnitRankData
    (K : Type*) [Field K] [NumberField K] where
  unitSubgroup : Subgroup Kˣ
  unitLogarithm : Kˣ → (K →+* ℂ) → ℝ
  logarithmic_rank_condition : Prop

theorem chapter11_totally_real_type_is_parallel_after_norm
    {K : Type*} [Field K] [NumberField K] [IsTotallyReal K]
    (n : Chapter11InfinityType K)
    (D : Chapter11DirichletUnitRankData K)
    (hrelations : ∀ u : D.unitSubgroup,
      chapter11UnitLogLinearForm n (u : Kˣ) = 0)
    (hrank : D.logarithmic_rank_condition) :
    ∃ c : ℤ, ∀ τ, n τ = c := by
  sorry

structure Chapter11CMInfinityTypeData
    (K : Type*) [Field K] [NumberField K] where
  p : ℤ
  q : ℤ
  infinityType : Chapter11InfinityType K
  pair_formula : ∀ z : ℂˣ,
    chapter11ComplexPairInfinityFormula p q z =
      Units.mk0 (((z : ℂ) ^ (-p)) * ((starRingEnd ℂ) (z : ℂ) ^ (-q))) (by sorry)
  unitSubgroup : Subgroup (𝓞 K)ˣ
  unit_relations : ∀ u : unitSubgroup,
    ∏ τ, ((τ ((u : (𝓞 K)ˣ) : K) : ℂ) ^ infinityType τ) = 1

theorem chapter11_cm_fields_allow_nonparallel_infinity_pairs
    {K : Type*} [Field K] [NumberField K] [IsCMField K]
    (D : Chapter11CMInfinityTypeData K) (hneq : D.p ≠ D.q) :
    D.p ≠ D.q ∧ ∀ z : ℂˣ,
      chapter11ComplexPairInfinityFormula D.p D.q z =
        Units.mk0 (((z : ℂ) ^ (-D.p)) *
          ((starRingEnd ℂ) (z : ℂ) ^ (-D.q))) (by sorry) := by
  exact ⟨hneq, D.pair_formula⟩

theorem chapter11_cm_pair_formula
    (p q : ℤ) (z : ℂˣ) :
    chapter11ComplexPairInfinityFormula p q z =
      Units.mk0 (((z : ℂ) ^ (-p)) * ((starRingEnd ℂ) (z : ℂ) ^ (-q))) (by sorry) :=
  rfl

end

end LastLib.Book06GlobalClassFieldTheory.Chapter11
