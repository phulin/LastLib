import LastLib.Book06GlobalClassFieldTheory.Chapter04.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

universe u v

open scoped BigOperators

/-! ## 4.5. Restriction, corestriction, and invariant normalizations -/

/-! The local invariant formulas below are stated against the small dependency interface in
`Dependencies`.  The canonical local Brauer maps from Book 5 should instantiate that interface;
the formulas are deliberately not expressed by choosing a completion or a branch. -/

/-- The normalized invariant of an unramified cyclic algebra of degree `d`. -/
structure Chapter04UnramifiedCyclicInvariantData where
  degree : ℕ
  positive_degree : 0 < degree
  invariant : chapter04QModZ
  normalized : invariant = chapter04QModZOfRat ((1 : ℚ) / degree)

theorem chapter04_unramified_cyclic_invariant_normalization
    (A : Chapter04UnramifiedCyclicInvariantData) :
    A.invariant = chapter04QModZOfRat ((1 : ℚ) / A.degree) := by
  exact A.normalized

/-- Restriction multiplies a local Brauer invariant by the extension degree (4.4). -/
theorem chapter04_local_invariant_restriction_formula
    {B₀ B₁ : Type*} [AddCommGroup B₀] [AddCommGroup B₁]
    (D : Chapter04LocalBrauerMapData B₀ B₁) (α : B₀) :
    D.inv₁ (D.res α) = D.degree • D.inv₀ α := by
  sorry

/-- Corestriction preserves the normalized local invariant (4.5). -/
theorem chapter04_local_invariant_corestriction_formula
    {B₀ B₁ : Type*} [AddCommGroup B₀] [AddCommGroup B₁]
    (D : Chapter04LocalBrauerMapData B₀ B₁) (β : B₁) :
    D.inv₀ (D.cor β) = D.inv₁ β := by
  sorry

/-- The local projection formula, before applying the invariant. -/
theorem chapter04_local_corestriction_restriction_formula
    {B₀ B₁ : Type*} [AddCommGroup B₀] [AddCommGroup B₁]
    (D : Chapter04LocalBrauerMapData B₀ B₁) (α : B₀) :
    D.cor (D.res α) = D.degree • α := by
  sorry

/-- Restriction and corestriction are transitive in a tower of local fields. -/
structure Chapter04LocalBrauerTowerData
    (B₀ B₁ B₂ : Type*)
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂] where
  first : Chapter04LocalBrauerMapData B₀ B₁
  second : Chapter04LocalBrauerMapData B₁ B₂
  composite : Chapter04LocalBrauerMapData B₀ B₂
  restriction_transitive : ∀ x : B₀,
    composite.res x = second.res (first.res x)
  corestriction_transitive : ∀ z : B₂,
    composite.cor z = first.cor (second.cor z)

theorem chapter04_local_restriction_is_transitive
    {B₀ B₁ B₂ : Type*}
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    (T : Chapter04LocalBrauerTowerData B₀ B₁ B₂) (x : B₀) :
    T.composite.res x = T.second.res (T.first.res x) := by
  exact T.restriction_transitive x

theorem chapter04_local_corestriction_is_transitive
    {B₀ B₁ B₂ : Type*}
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    (T : Chapter04LocalBrauerTowerData B₀ B₁ B₂) (z : B₂) :
    T.composite.cor z = T.first.cor (T.second.cor z) := by
  exact T.corestriction_transitive z

/-! ### Products of completions -/

/-- Brauer restriction/corestriction and invariant maps for a finite étale product. -/
structure Chapter04FiniteEtaleBrauerData (I : Type u) [Fintype I] where
  base : Type u
  [baseGroup : AddCommGroup base]
  branch : I → Type u
  [branchGroup : ∀ i, AddCommGroup (branch i)]
  degree : I → ℕ
  res : ∀ i, base →+ branch i
  cor : ∀ i, branch i →+ base
  invBase : base →+ chapter04QModZ
  invBranch : ∀ i, branch i →+ chapter04QModZ

attribute [instance] Chapter04FiniteEtaleBrauerData.baseGroup
  Chapter04FiniteEtaleBrauerData.branchGroup

/-- The finite étale corestriction sum formula (4.6). -/
theorem chapter04_finite_etale_corestriction_sum_formula
    {I : Type*} [Fintype I]
    (D : Chapter04FiniteEtaleBrauerData I) (β : ∀ i, D.branch i) :
    D.invBase (∑ i, D.cor i (β i)) = ∑ i, D.invBranch i (β i) := by
  sorry

/-- The finite étale restriction sum formula (4.7). -/
theorem chapter04_finite_etale_restriction_sum_formula
    {I : Type*} [Fintype I]
    (D : Chapter04FiniteEtaleBrauerData I) (α : D.base) :
    (∑ i, D.invBranch i (D.res i α)) =
      (∑ i, D.degree i) • D.invBase α := by
  sorry

/-- The degree sum for the completions of a finite global extension. -/
structure Chapter04CompletionBranchDegrees (I : Type*) [Fintype I] where
  branchDegree : I → ℕ
  totalDegree : ℕ
  degree_sum : ∑ i, branchDegree i = totalDegree

theorem chapter04_completion_branch_degree_sum
    {I : Type*} [Fintype I] (D : Chapter04CompletionBranchDegrees I) :
    ∑ i, D.branchDegree i = D.totalDegree := by
  exact D.degree_sum

/-! ### The global invariant row -/

/- The direct sum in the next theorem is literally `DFinsupp`, so finite support is part of the
type rather than an informal side condition.  Since `Chapter04Place` is a finite-place sum with an
infinite-place summand, real and complex terms are included by construction. -/
theorem chapter04_global_invariant_sequence
    {F : Type u} [Field F] [NumberField F]
    (D : Chapter04BrauerContext.{u, v} F)
    (hlocal : Chapter04LocalBrauerBehavior D) :
    chapter04BrauerInvariantExact D := by
  sorry

end

end LastLib.Book06GlobalClassFieldTheory.Chapter04
