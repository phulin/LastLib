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
  simp [chapter12KrasnerRadius, chapter12KrasnerDistanceSet]

private theorem chapter12_krasner_distance_set_finite_aux
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α : L) (hα : IsIntegral K α)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits) :
    Set.Finite (chapter12KrasnerDistanceSet (K := K) α) := by
  have _ := hsplits
  let g : L → ENNReal := fun α' => ENNReal.ofReal ‖α' - α‖
  have hrootset : Set.Finite ((minpoly K α).rootSet L) :=
    Polynomial.rootSet_finite (minpoly K α) L
  have hsubset : chapter12KrasnerDistanceSet (K := K) α ⊆
      g '' (minpoly K α).rootSet L := by
    rintro r ⟨_, α', hconj, _, hr⟩
    refine ⟨α', (isConjRoot_iff_mem_minpoly_rootSet hα).mp hconj, ?_⟩
    exact hr.symm
  exact (hrootset.image g).subset hsubset

/-- Separability and splitting make the finite conjugate separation positive. -/
theorem chapter12_krasner_radius_pos
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α : L) (hseparable : IsSeparable K α)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits) :
  0 < chapter12KrasnerRadius (K := K) α := by
  have hα : IsIntegral K α := hseparable.isIntegral
  have hfinite : Set.Finite (chapter12KrasnerDistanceSet (K := K) α) :=
    chapter12_krasner_distance_set_finite_aux α hα hsplits
  by_cases hnonempty : (chapter12KrasnerDistanceSet (K := K) α).Nonempty
  · rcases hnonempty.csInf_mem hfinite with ⟨_, α', hconj, hne, hvalue⟩
    rw [chapter12KrasnerRadius, hvalue]
    exact ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))
  · have hempty : chapter12KrasnerDistanceSet (K := K) α = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    simp [chapter12KrasnerRadius, hempty]

/-- Splitting the minimal polynomial makes the integral conjugate-distance
set finite. -/
theorem chapter12_krasner_distance_set_finite
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α : L) (hα : IsIntegral K α)
    (hsplits : ((minpoly K α).map (algebraMap K L)).Splits) :
    Set.Finite (chapter12KrasnerDistanceSet (K := K) α) := by
  exact chapter12_krasner_distance_set_finite_aux α hα hsplits

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
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  have hα' : IsIntegral K α' := IsConjRoot.isIntegral hα hconj
  have hσinv : σ.symm α = α' := by
    rw [← hσ]
    simp
  have hset : chapter12KrasnerDistanceSet (K := K) α' =
      chapter12KrasnerDistanceSet (K := K) α := by
    ext r
    constructor
    · rintro ⟨_, γ, hγ, hne, hr⟩
      refine ⟨hα, σ γ, ?_, ?_, ?_⟩
      · have hmap : IsConjRoot K (σ α') (σ γ) :=
          (isConjRoot_algHom_iff σ.toAlgHom).mpr hγ
        simpa [hσ] using hmap
      · intro heq
        apply hne
        apply σ.injective
        calc
          σ α' = α := hσ
          _ = σ γ := heq
      · rw [hr]
        exact congrArg ENNReal.ofReal <| by
          simpa [map_sub, hσ] using (hisometry σ (γ - α')).symm
    · rintro ⟨_, γ, hγ, hne, hr⟩
      refine ⟨hα', σ.symm γ, ?_, ?_, ?_⟩
      · have hmap : IsConjRoot K (σ.symm α) (σ.symm γ) :=
          (isConjRoot_algHom_iff σ.symm.toAlgHom).mpr hγ
        simpa [hσinv] using hmap
      · intro heq
        apply hne
        calc
          α = σ α' := hσ.symm
          _ = σ (σ.symm γ) := congrArg σ heq
          _ = γ := by simp
      · rw [hr]
        exact congrArg ENNReal.ofReal <| by
          simpa [map_sub, hσinv] using (hisometry σ.symm (γ - α)).symm
  change sInf (chapter12KrasnerDistanceSet (K := K) α) =
    sInf (chapter12KrasnerDistanceSet (K := K) α')
  rw [hset]

/- In the nontrivial separable case the infimum is the minimum over the
finite distinct-conjugate set. -/
theorem chapter12_krasner_radius_is_attained
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α : L) (hfinite : Set.Finite (chapter12KrasnerDistanceSet (K := K) α))
    (hnonempty : (chapter12KrasnerDistanceSet (K := K) α).Nonempty) :
    ∃ α' : L, IsConjRoot K α α' ∧ α ≠ α' ∧
      chapter12KrasnerRadius (K := K) α = ENNReal.ofReal ‖α' - α‖ := by
  rcases hnonempty.csInf_mem hfinite with ⟨_, α', hconj, hne, hvalue⟩
  refine ⟨α', hconj, hne, ?_⟩
  simpa [chapter12KrasnerRadius] using hvalue

/-- For the finite conjugate set, strict proximity is equivalent to the
radius test in the source definition. -/
theorem chapter12_krasner_proximity_iff_radius
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α β : L) (hα : IsIntegral K α)
    (hfinite : Set.Finite (chapter12KrasnerDistanceSet (K := K) α)) :
    chapter12KrasnerProximity (K := K) α β ↔
      ENNReal.ofReal ‖β - α‖ < chapter12KrasnerRadius (K := K) α := by
  simp only [chapter12KrasnerProximity]
  change (∀ α' : L, IsConjRoot K α α' → α ≠ α' →
      ‖β - α‖ < ‖α' - α‖) ↔
    ENNReal.ofReal ‖β - α‖ <
      sInf (chapter12KrasnerDistanceSet (K := K) α)
  by_cases hnonempty : (chapter12KrasnerDistanceSet (K := K) α).Nonempty
  · rw [hfinite.lt_csInf_iff hnonempty]
    constructor
    · intro h r hr
      rcases hr with ⟨_, α', hconj, hne, hr⟩
      rw [hr]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)
        |>.mpr (h α' hconj hne)
    · intro h α' hconj hne
      have hr : ENNReal.ofReal ‖β - α‖ <
          ENNReal.ofReal ‖α' - α‖ :=
        h _ ⟨hα, α', hconj, hne, rfl⟩
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)
        |>.mp hr
  · have hempty : chapter12KrasnerDistanceSet (K := K) α = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hnonempty
    constructor
    · intro _
      simp [hempty]
    · intro _ α' hconj hne
      have hmem : ENNReal.ofReal ‖α' - α‖ ∈
          chapter12KrasnerDistanceSet (K := K) α :=
        ⟨hα, α', hconj, hne, rfl⟩
      simp [hempty] at hmem

/-- Replacing the norm by any positive real power does not change the
strict proximity condition. -/
theorem chapter12_krasner_proximity_invariant_under_positive_power
    {K L : Type*} [Field K] [NormedField L] [Algebra K L]
    (α β : L) (q : ℝ) (hq : 0 < q) :
    chapter12KrasnerProximity (K := K) α β ↔
      ∀ α' : L, IsConjRoot K α α' → α ≠ α' →
        Real.rpow ‖β - α‖ q < Real.rpow ‖α' - α‖ q := by
  simp only [chapter12KrasnerProximity]
  constructor
  · intro h α' hconj hne
    exact Real.rpow_lt_rpow (norm_nonneg _) (h α' hconj hne) hq
  · intro h α' hconj hne
    exact (Real.rpow_lt_rpow_iff (norm_nonneg (β - α))
      (norm_nonneg (α' - α)) hq).mp (h α' hconj hne)

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
  have _ := hf_degree
  have _ := hf_separable
  have _ := hsplits
  have hα : IsIntegral K α := ⟨f, hf_monic, hαroot⟩
  have hmin : f = minpoly K α :=
    minpoly.eq_of_irreducible_of_monic hf_irreducible hαroot hf_monic
  have hconjβ : IsConjRoot K α β := by
    apply (isConjRoot_iff_aeval_eq_zero hα).mpr
    rw [← hmin]
    exact hβroot
  have hdistance : chapter12KrasnerDistanceSet (K := K) α =
      {ENNReal.ofReal ‖β - α‖} := by
    ext r
    constructor
    · rintro ⟨_, γ, hγ, hγne, hr⟩
      have hγroot : aeval γ f = 0 := by
        rw [hmin]
        exact IsConjRoot.aeval_eq_zero hγ
      rcases hroots γ hγroot with hγα | hγβ
      · exact (hγne hγα.symm).elim
      · subst γ
        exact Set.mem_singleton_iff.mpr hr
    · intro hr
      have hr' : r = ENNReal.ofReal ‖β - α‖ :=
        Set.mem_singleton_iff.mp hr
      subst r
      exact ⟨hα, β, hconjβ, hne, rfl⟩
  rw [chapter12KrasnerRadius, hdistance]
  simp

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter12
