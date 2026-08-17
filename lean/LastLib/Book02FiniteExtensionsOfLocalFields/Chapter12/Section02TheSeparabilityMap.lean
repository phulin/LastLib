import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12.Section01TheStructuralDictionary
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12

noncomputable section

open Polynomial

/-! ## 12.2. The Krasner radius -/

/-- The distances from `α` to its distinct `K`-conjugates in the chosen
normed overfield.  The integrality guard prevents the unconstrained
`IsConjRoot` relation from treating two non-integral elements as conjugate.
The empty set represents an element with no distinct conjugate, so its
infimum is `⊤` in `ENNReal`. -/
def chapter12KrasnerDistanceSet
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α : L) : Set ENNReal :=
  {r | IsIntegral K α ∧ ∃ α' : L, IsConjRoot K α α' ∧ α ≠ α' ∧
      r = ENNReal.ofReal ‖α' - α‖}

/-- The Krasner radius, with `⊤` for an element of the base field. -/
noncomputable def chapter12KrasnerRadius
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α : L) : ENNReal :=
  sInf (chapter12KrasnerDistanceSet (K := K) α)

/-- The strict proximity condition in Krasner's lemma. -/
def chapter12KrasnerProximity
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α β : L) : Prop :=
  ∀ α' : L, IsConjRoot K α α' → α ≠ α' →
    ‖β - α‖ < ‖α' - α‖

/-- There are no distinct conjugates of a base element. -/
theorem chapter12_krasner_radius_for_base_element
    {K L : Type*} [Field K] [NormedField L] [Algebra K L] (a : K) :
    chapter12KrasnerRadius (K := K) (algebraMap K L a) = ⊤ := by
  sorry

/-- Separability and splitting make the finite conjugate separation positive. -/
theorem chapter12_krasner_radius_pos
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α : L) (hseparable : IsSeparable K α)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits) :
  0 < chapter12KrasnerRadius (K := K) α := by
  sorry

/-- Splitting the minimal polynomial makes the integral conjugate-distance
set finite. -/
theorem chapter12_krasner_distance_set_finite
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α : L) (hα : IsIntegral K α)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits) :
    Set.Finite (chapter12KrasnerDistanceSet (K := K) α) := by
  sorry

/- The unique extension of the absolute value makes conjugation an
isometry.  The hypothesis is written explicitly here because Mathlib's
`IsKrasner` interface records the field-containment conclusion, not this
separate invariance statement. -/
theorem chapter12_krasner_radius_conjugate_invariant
    {K L : Type*} [Field K] [NormedField L] [Algebra K L] [Normal K L]
    {α α' : L} (hα : IsIntegral K α) (hconj : IsConjRoot K α α')
    (hisometry : ∀ σ : L ≃ₐ[K] L, ∀ x : L, ‖σ x‖ = ‖x‖) :
    chapter12KrasnerRadius (K := K) α =
      chapter12KrasnerRadius (K := K) α' := by
  sorry

/- In the nontrivial separable case the infimum is the minimum over the
finite distinct-conjugate set. -/
theorem chapter12_krasner_radius_is_attained
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α : L) (hfinite : Set.Finite (chapter12KrasnerDistanceSet (K := K) α))
    (hnonempty : (chapter12KrasnerDistanceSet (K := K) α).Nonempty) :
    ∃ α' : L, IsConjRoot K α α' ∧ α ≠ α' ∧
      chapter12KrasnerRadius (K := K) α = ENNReal.ofReal ‖α' - α‖ := by
  sorry

/-- For the finite conjugate set, strict proximity is equivalent to the
radius test in the source definition. -/
theorem chapter12_krasner_proximity_iff_radius
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α β : L) (hα : IsIntegral K α)
    (hfinite : Set.Finite (chapter12KrasnerDistanceSet (K := K) α)) :
    chapter12KrasnerProximity (K := K) α β ↔
      ENNReal.ofReal ‖β - α‖ < chapter12KrasnerRadius (K := K) α := by
  sorry

/-- Replacing the norm by any positive real power does not change the
strict proximity condition. -/
theorem chapter12_krasner_proximity_invariant_under_positive_power
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α β : L) (q : ℝ) (hq : 0 < q) :
    chapter12KrasnerProximity (K := K) α β ↔
      ∀ α' : L, IsConjRoot K α α' → α ≠ α' →
        Real.rpow ‖β - α‖ q < Real.rpow ‖α' - α‖ q := by
  sorry

/-- The boundary point supplied by a distinct conjugate is one of the
distances whose minimum defines the radius. -/
theorem chapter12_conjugate_lies_on_krasner_boundary
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    {α β : L} (hα : IsIntegral K α) (hconj : IsConjRoot K α β) (hne : α ≠ β) :
    ENNReal.ofReal ‖β - α‖ ∈ chapter12KrasnerDistanceSet (K := K) α := by
  exact ⟨hα, β, hconj, hne, rfl⟩

/- In the quadratic case the other root is the unique distinct conjugate,
so its distance is exactly the radius. -/
theorem chapter12_quadratic_conjugate_has_boundary_radius
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (f : K[X]) (α β : L)
    (hf_monic : f.Monic) (hf_degree : f.natDegree = 2)
    (hf_irreducible : Irreducible f) (hf_separable : f.Separable)
    (hsplits : (f.map (algebraMap K L)).Splits)
    (hαroot : aeval α f = 0) (hβroot : aeval β f = 0)
    (hne : α ≠ β)
    (hroots : ∀ z : L, aeval z f = 0 → z = α ∨ z = β) :
    ENNReal.ofReal ‖β - α‖ = chapter12KrasnerRadius (K := K) α := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
