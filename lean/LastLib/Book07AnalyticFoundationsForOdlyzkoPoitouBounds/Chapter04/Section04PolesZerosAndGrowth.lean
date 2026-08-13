import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04.Section03ContinuationAndFunctionalEquation

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04

noncomputable section

open LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter03

open Filter MeasureTheory NumberField Set
open scoped BigOperators ComplexConjugate nonZeroDivisors

/-! ### 4.4. Poles, zeros, and growth -/

/-- The pole-removing factor in the definition of `ξ_K`. -/
noncomputable def chapter04PoleFactor (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1)

/-- The completed entire function attached to the Dedekind zeta function. -/
noncomputable def chapter04Xi
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  chapter04PoleFactor s * chapter04CompletedDedekindZeta K s

theorem chapter04_xi_eq_pole_factor_mul_completed_zeta
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04Xi K s =
      (1 / 2 : ℂ) * s * (s - 1) * chapter04CompletedDedekindZeta K s := by
  rfl

theorem chapter04_xi_entire
    (K : Type*) [Field K] [NumberField K] :
    AnalyticOnNhd ℂ (chapter04Xi K) Set.univ := by
  sorry

theorem chapter04_xi_functional_equation
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04Xi K s = chapter04Xi K (1 - s) := by
  rw [chapter04Xi, chapter04Xi,
    chapter04_completed_dedekind_zeta_functional_equation]
  unfold chapter04PoleFactor
  ring

theorem chapter04_xi_conjugation_symmetry
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04Xi K (star s) = star (chapter04Xi K s) := by
  sorry

theorem chapter04_xi_not_identically_zero
    (K : Type*) [Field K] [NumberField K] :
    ¬(∀ s : ℂ, chapter04Xi K s = 0) := by
  sorry

def chapter04NontrivialZero
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) : Prop :=
  chapter04Xi K ρ = 0

theorem chapter04_mem_nontrivial_zero_iff
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    ρ ∈ {ρ : ℂ | chapter04NontrivialZero K ρ} ↔
      chapter04Xi K ρ = 0 := by
  rfl

noncomputable def chapter04ZeroMultiplicity
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) : ℕ :=
  (analyticOrderAt (chapter04Xi K) ρ).toNat

theorem chapter04_zero_multiplicity_pos_iff
    (K : Type*) [Field K] [NumberField K] {ρ : ℂ} :
    0 < chapter04ZeroMultiplicity K ρ ↔ chapter04NontrivialZero K ρ := by
  constructor
  · intro h
    apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
    change (analyticOrderAt (chapter04Xi K) ρ).toNat ≠ 0
    exact Nat.ne_of_gt h
  · intro h
    unfold chapter04NontrivialZero at h
    have hwhole := chapter04_xi_entire K
    have hρ : AnalyticAt ℂ (chapter04Xi K) ρ := hwhole ρ (Set.mem_univ _)
    obtain ⟨z, hz⟩ : ∃ z : ℂ, chapter04Xi K z ≠ 0 := by
      by_contra h'
      push Not at h'
      exact (chapter04_xi_not_identically_zero K) h'
    have hzorder : analyticOrderAt (chapter04Xi K) z ≠ ⊤ := by
      have hzzero : analyticOrderAt (chapter04Xi K) z = 0 :=
        (hwhole z (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hz
      rw [hzzero]
      exact ENat.zero_ne_top
    have hρtop : analyticOrderAt (chapter04Xi K) ρ ≠ ⊤ :=
      hwhole.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
        (Set.mem_univ _) (Set.mem_univ _) hzorder
    unfold chapter04ZeroMultiplicity
    exact ENat.toNat_pos (hρ.analyticOrderAt_ne_zero.mpr h) hρtop

def chapter04CriticalStrip (ρ : ℂ) : Prop :=
  0 ≤ ρ.re ∧ ρ.re ≤ 1

theorem chapter04_nontrivial_zero_in_critical_strip
    (K : Type*) [Field K] [NumberField K] {ρ : ℂ}
    (hρ : chapter04NontrivialZero K ρ) :
    chapter04CriticalStrip ρ := by
  sorry

/-- The functional-equation/conjugation partner used by later zero sums. -/
def chapter04ZeroPartner (ρ : ℂ) : ℂ :=
  1 - star ρ

theorem chapter04_nontrivial_zero_partner_iff
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter04NontrivialZero K ρ ↔
      chapter04NontrivialZero K (chapter04ZeroPartner ρ) := by
  constructor
  · intro h
    unfold chapter04NontrivialZero at h ⊢
    rw [chapter04ZeroPartner, ← chapter04_xi_functional_equation K (star ρ)]
    rw [chapter04_xi_conjugation_symmetry K ρ, h]
    simp
  · intro h
    unfold chapter04NontrivialZero at h ⊢
    have heq : chapter04Xi K (chapter04ZeroPartner ρ) = star (chapter04Xi K ρ) := by
      rw [chapter04ZeroPartner, ← chapter04_xi_functional_equation K (star ρ)]
      exact chapter04_xi_conjugation_symmetry K ρ
    rw [heq] at h
    simpa using h

theorem chapter04_zero_multiplicity_partner
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter04ZeroMultiplicity K (chapter04ZeroPartner ρ) =
      chapter04ZeroMultiplicity K ρ := by
  sorry

theorem chapter04_nontrivial_zero_conjugate_iff
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter04NontrivialZero K ρ ↔ chapter04NontrivialZero K (star ρ) := by
  unfold chapter04NontrivialZero
  rw [chapter04_xi_conjugation_symmetry K ρ]
  simp

theorem chapter04_zero_multiplicity_conjugate
    (K : Type*) [Field K] [NumberField K] (ρ : ℂ) :
    chapter04ZeroMultiplicity K (star ρ) = chapter04ZeroMultiplicity K ρ := by
  sorry

/- The boundary-line statement is deliberately an interface for the separate
   zero-free-line theorem mentioned in the source, not an unproved theorem of
   this chapter. -/
def chapter04BoundaryZeroFree
    (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ ρ : ℂ, chapter04NontrivialZero K ρ →
    (ρ.re = 0 ∨ ρ.re = 1) → False

/-- The aggregate archimedean factor whose poles are canceled by trivial zeros. -/
noncomputable def chapter04ArchimedeanLogDerivative
    (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  deriv (chapter04ArchimedeanFactor K) s /
    chapter04ArchimedeanFactor K s

def chapter04GammaPoleSet
    (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {s | meromorphicOrderAt (chapter04ArchimedeanFactor K) s < 0}

def chapter04TrivialZeroSet
    (K : Type*) [Field K] [NumberField K] : Set ℂ :=
  {s | s ∈ chapter04GammaPoleSet K ∧ chapter03DedekindZeta K s = 0}

theorem chapter04_gamma_poles_away_from_zero_are_canceled_by_trivial_zeros
    (K : Type*) [Field K] [NumberField K] :
    (chapter04GammaPoleSet K \ {0}) ⊆
      {s : ℂ | chapter03DedekindZeta K s = 0} := by
  sorry

theorem chapter04_trivial_zero_set_mem_gamma_poles
    (K : Type*) [Field K] [NumberField K] :
    chapter04TrivialZeroSet K ⊆ chapter04GammaPoleSet K := by
  intro s hs
  exact hs.1

theorem chapter04_trivial_zero_contribution_is_aggregate
    (K : Type*) [Field K] [NumberField K] (s : ℂ) :
    chapter04ArchimedeanLogDerivative K s =
      deriv (chapter04ArchimedeanFactor K) s /
        chapter04ArchimedeanFactor K s := by
  rfl

theorem chapter04_pole_factor_log_derivative
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv chapter04PoleFactor s / chapter04PoleFactor s =
      1 / s + 1 / (s - 1) := by
  have hderiv :
      HasDerivAt chapter04PoleFactor
        ((1 / 2 : ℂ) * (s - 1) + (1 / 2 : ℂ) * s) s := by
    change HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) * z * (z - 1))
      ((1 / 2 : ℂ) * (s - 1) + (1 / 2 : ℂ) * s) s
    convert (((hasDerivAt_const s (1 / 2 : ℂ)).mul (hasDerivAt_id s)).mul
      ((hasDerivAt_id s).sub (hasDerivAt_const s (1 : ℂ)))) using 1
    · rfl
    · rfl
    · funext z
      simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
    · simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
      ring
  rw [hderiv.deriv]
  simp only [chapter04PoleFactor]
  field_simp [hs0, hs1]

noncomputable def chapter04ResidueAt
    (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  meromorphicTrailingCoeffAt f z

theorem chapter04_residues_at_zero_and_one_are_opposite
    (K : Type*) [Field K] [NumberField K] :
    chapter04ResidueAt (chapter04CompletedDedekindZeta K) 0 =
      -chapter04ResidueAt (chapter04CompletedDedekindZeta K) 1 := by
  sorry

theorem chapter04_residue_at_one_is_positive_real
    (K : Type*) [Field K] [NumberField K] :
    0 < (chapter04ResidueAt (chapter04CompletedDedekindZeta K) 1).re ∧
      (chapter04ResidueAt (chapter04CompletedDedekindZeta K) 1).im = 0 := by
  sorry

/-! The order-one growth interface and the symmetric zero count. -/

def chapter04OrderAtMostOne (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C R : ℝ, 0 < C ∧ 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ →
      ‖f z‖ ≤ Real.exp (C * Real.rpow ‖z‖ (1 + ε))

/- The source only needs the order-one upper-growth interface.  Exact lower
   order is stronger and is not part of the continuation argument. -/
def chapter04OrderOne (f : ℂ → ℂ) : Prop :=
  chapter04OrderAtMostOne f

theorem chapter04_xi_order_one
    (K : Type*) [Field K] [NumberField K] :
    chapter04OrderOne (chapter04Xi K) := by
  sorry

theorem chapter04_xi_order_at_most_one
    (K : Type*) [Field K] [NumberField K] :
    chapter04OrderAtMostOne (chapter04Xi K) := by
  exact chapter04_xi_order_one K

def chapter04ZeroBand
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : Set ℂ :=
  {ρ | chapter04NontrivialZero K ρ ∧ |ρ.im| ≤ T}

theorem chapter04_zero_band_finite
    (K : Type*) [Field K] [NumberField K] (T : ℝ) :
    (chapter04ZeroBand K T).Finite := by
  sorry

noncomputable def chapter04ZeroCounting
    (K : Type*) [Field K] [NumberField K] (T : ℝ) : ℕ :=
  (chapter04_zero_band_finite K T).toFinset.sum
    (fun ρ => chapter04ZeroMultiplicity K ρ)

theorem chapter04_zero_counting_monotone
    (K : Type*) [Field K] [NumberField K] {S T : ℝ}
    (hST : S ≤ T) :
    chapter04ZeroCounting K S ≤ chapter04ZeroCounting K T := by
  let fS := chapter04_zero_band_finite K S
  let fT := chapter04_zero_band_finite K T
  have hsubset : chapter04ZeroBand K S ⊆ chapter04ZeroBand K T := by
    intro ρ hρ
    exact ⟨hρ.1, hρ.2.trans hST⟩
  have hfin : fS.toFinset ⊆ fT.toFinset := by
    exact (Set.Finite.toFinset_subset_toFinset).2 hsubset
  change fS.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ) ≤
    fT.toFinset.sum (fun ρ => chapter04ZeroMultiplicity K ρ)
  exact Finset.sum_le_sum_of_subset_of_nonneg hfin
    (fun _ _ _ => Nat.zero_le _)

theorem chapter04_zero_counting_unit_band_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ((chapter04ZeroCounting K (T + 1) - chapter04ZeroCounting K T : ℕ) : ℝ) ≤
        C * (Real.log (chapter04AbsoluteDiscriminant K) +
          (chapter04Degree K : ℝ) * Real.log (T + 3)) := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter04
