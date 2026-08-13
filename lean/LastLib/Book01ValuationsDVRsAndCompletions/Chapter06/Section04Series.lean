import LastLib.Book01ValuationsDVRsAndCompletions.Chapter06.Section03CauchySequences
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter06

open Set Filter Function
open scoped BigOperators Pointwise Topology WithZero NNReal Valued PowerSeries

noncomputable section

/-! # Book 1, Chapter 6, Section 6.4: Series
-/

/-! ### 6.4 Series -/

section Series

variable {K : Type*} [Field K]

/-- The `n`th partial sum of a series indexed from zero. -/
def chapter06PartialSums (a : ℕ → K) (n : ℕ) : K :=
  Finset.sum (Finset.range n) (fun i => a i)

/-- A series has sum `s` in the valuation metric. -/
def chapter06SeriesConverges
    (v : AbsoluteValue K ℝ) (a : ℕ → K) (s : K) : Prop :=
  chapter06ConvergesTo v (chapter06PartialSums a) s

/-- Existential form of convergence of a series. -/
def chapter06SeriesHasSum (v : AbsoluteValue K ℝ) (a : ℕ → K) : Prop :=
  ∃ s : K, chapter06SeriesConverges v a s

/-- Finite tails of a nonarchimedean series are bounded by their largest term. -/
theorem chapter06_series_tail_bound
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : ℕ → K} {n m : ℕ} (_hnm : n < m)
    (hs : (Finset.Ico n m).Nonempty) :
    v (Finset.sum (Finset.Ico n m) (fun i => a i)) ≤
      (Finset.Ico n m).sup' hs (fun i => v (a i)) := by
  exact IsNonarchimedean.apply_sum_le_sup hv hs

/-- The difference of two partial sums is the corresponding finite tail sum. -/
theorem chapter06_partial_sum_difference_eq_tail
    (a : ℕ → K) {n m : ℕ} (hnm : n ≤ m) :
    chapter06PartialSums a m - chapter06PartialSums a n =
      Finset.sum (Finset.Ico n m) (fun i => a i) := by
  simp only [chapter06PartialSums]
  simpa using (Finset.sum_Ico_eq_sub (fun i => a i) hnm).symm

/-- Convergence of a series forces its terms to tend to zero. -/
theorem chapter06_series_convergence_implies_terms_tend_to_zero
    (v : AbsoluteValue K ℝ) {a : ℕ → K} {s : K}
    (h : chapter06SeriesConverges v a s) : chapter06TendsToZero v a := by
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, ?_⟩
  intro n hn
  have hn1 : N ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hterm : chapter06PartialSums a (n + 1) - chapter06PartialSums a n = a n := by
    rw [chapter06_partial_sum_difference_eq_tail a (Nat.le_succ n)]
    simp
  have h1 : v (chapter06PartialSums a (n + 1) - s) < ε / 2 := by
    simpa [chapter06Distance] using hN (n + 1) hn1
  have h2 : v (chapter06PartialSums a n - s) < ε / 2 := by
    simpa [chapter06Distance] using hN n hn
  calc
    v (a n) = v (chapter06PartialSums a (n + 1) - chapter06PartialSums a n) := by
      rw [hterm]
    _ ≤ v (chapter06PartialSums a (n + 1) - s) +
          v (s - chapter06PartialSums a n) :=
      v.sub_le (chapter06PartialSums a (n + 1)) s (chapter06PartialSums a n)
    _ = v (chapter06PartialSums a (n + 1) - s) +
          v (chapter06PartialSums a n - s) := by
      congr 1
      exact v.map_sub s (chapter06PartialSums a n)
    _ < ε := by linarith

/-- In a complete nonarchimedean field, a series converges exactly when its terms vanish. -/
theorem chapter06_series_converges_iff_terms_tend_to_zero
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v) (a : ℕ → K) :
    chapter06SeriesHasSum v a ↔ chapter06TendsToZero v a := by
  constructor
  · rintro ⟨s, hs⟩
    exact chapter06_series_convergence_implies_terms_tend_to_zero v hs
  · intro hzero
    have hpc : chapter06CauchySeq v (chapter06PartialSums a) := by
      intro ε hε
      obtain ⟨N, hN⟩ := hzero ε hε
      refine ⟨N, ?_⟩
      intro m n hm hn
      by_cases hmn : m < n
      · have htail := chapter06_partial_sum_difference_eq_tail a hmn.le
        have hbound := chapter06_series_tail_bound (a := a) v hv hmn
          ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩⟩
        have hsmall :
              (Finset.Ico m n).sup'
              ⟨m, Finset.mem_Ico.mpr ⟨le_rfl, hmn⟩⟩ (fun i => v (a i)) < ε := by
          apply (Finset.sup'_lt_iff _).2
          intro i hi
          exact hN i (hm.trans (Finset.mem_Ico.mp hi).1)
        have hdiff : v (chapter06PartialSums a n - chapter06PartialSums a m) < ε := by
          rw [htail]
          exact hbound.trans_lt hsmall
        simpa [chapter06Distance, v.map_sub] using hdiff
      · by_cases hnm : n < m
        · have htail := chapter06_partial_sum_difference_eq_tail a hnm.le
          have hbound := chapter06_series_tail_bound (a := a) v hv hnm
            ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, hnm⟩⟩
          have hsmall :
                (Finset.Ico n m).sup'
                ⟨n, Finset.mem_Ico.mpr ⟨le_rfl, hnm⟩⟩ (fun i => v (a i)) < ε := by
            apply (Finset.sup'_lt_iff _).2
            intro i hi
            exact hN i (hn.trans (Finset.mem_Ico.mp hi).1)
          have hdiff : v (chapter06PartialSums a m - chapter06PartialSums a n) < ε := by
            rw [htail]
            exact hbound.trans_lt hsmall
          exact hdiff
        · have heq : m = n := by omega
          subst n
          simpa [chapter06Distance] using hε
    obtain ⟨s, hs⟩ := hcomplete (chapter06PartialSums a) hpc
    exact ⟨s, hs⟩

/-- The geometric series converges to `(1-x)⁻¹` when `|x| < 1`. -/
theorem chapter06_geometric_series
    (v : AbsoluteValue K ℝ) (_hv : IsNonarchimedean v)
    (_hcomplete : chapter06CompleteValuedSpace v) {x : K} (hx : v x < 1) :
    chapter06SeriesConverges v (fun n => x ^ n) (1 - x)⁻¹ := by
  have hne : 1 - x ≠ 0 := by
    intro h
    have hx1 : x = 1 := (sub_eq_zero.mp h).symm
    subst x
    simp at hx
  have hzero : chapter06TendsToZero v (fun n => x ^ n) := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hx
    refine ⟨N, ?_⟩
    intro n hn
    change v (x ^ n) < ε
    rw [map_pow]
    exact (pow_le_pow_of_le_one (v.nonneg x) hx.le hn).trans_lt hN
  have hgeom : ∀ n : ℕ,
      chapter06PartialSums (fun i => x ^ i) n * (1 - x) = 1 - x ^ n := by
    intro n
    induction n with
    | zero => simp [chapter06PartialSums]
    | succ n ih =>
        have hpartial :
            chapter06PartialSums (fun i => x ^ i) (n + 1) =
              chapter06PartialSums (fun i => x ^ i) n + x ^ n := by
          unfold chapter06PartialSums
          rw [Finset.sum_range_succ]
        rw [hpartial]
        rw [add_mul, ih]
        ring
  have hinvpos : 0 < v ((1 - x)⁻¹) := v.pos (inv_ne_zero hne)
  intro ε hε
  obtain ⟨N, hN⟩ := hzero (ε / v ((1 - x)⁻¹))
    (div_pos hε hinvpos)
  refine ⟨N, ?_⟩
  intro n hn
  have hsum :
      chapter06PartialSums (fun i => x ^ i) n - (1 - x)⁻¹ =
        -x ^ n * (1 - x)⁻¹ := by
    calc
      chapter06PartialSums (fun i => x ^ i) n - (1 - x)⁻¹ =
          (chapter06PartialSums (fun i => x ^ i) n * (1 - x) - 1) *
            (1 - x)⁻¹ := by
              field_simp [hne]
      _ = (1 - x ^ n - 1) * (1 - x)⁻¹ := by rw [hgeom n]
      _ = -x ^ n * (1 - x)⁻¹ := by ring
  change v (chapter06PartialSums (fun i => x ^ i) n - (1 - x)⁻¹) < ε
  rw [hsum, v.map_mul, v.map_neg]
  exact (lt_div_iff₀ hinvpos).1 (hN n hn)

/-- The principal-unit set of a local ring. -/
def chapter06PrincipalUnitSet (A : Type*) [CommRing A] [IsLocalRing A] : Set A :=
  {x | ∃ y ∈ (IsLocalRing.maximalIdeal A : Set A), x = 1 + y}

/-- `1 + 𝔪` lies in the unit group. -/
theorem chapter06_principal_units_are_units
    {A : Type*} [CommRing A] [IsLocalRing A] :
    chapter06PrincipalUnitSet A ⊆ Set.range (Units.val : Aˣ → A) := by
  rintro x ⟨y, hy, rfl⟩
  have hnot : (1 + y : A) ∉ IsLocalRing.maximalIdeal A := by
    intro hmem
    have hone : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
      have hsub := (IsLocalRing.maximalIdeal A).sub_mem hmem hy
      rw [add_sub_cancel_right] at hsub
      exact hsub
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((IsLocalRing.maximalIdeal A).eq_top_iff_one.mpr hone)
  have hu : IsUnit (1 + y : A) := IsLocalRing.notMem_maximalIdeal.mp hnot
  rcases hu with ⟨u, hu⟩
  exact ⟨u, hu⟩

/-- The geometric identity accompanies the algebraic principal-unit assertion. -/
theorem chapter06_geometric_inverse_identity
    (v : AbsoluteValue K ℝ) {x : K} (hx : v x < 1) :
    (1 - x) * (1 - x)⁻¹ = 1 := by
  have hne : 1 - x ≠ 0 := by
    intro h
    have hx1 : x = 1 := (sub_eq_zero.mp h).symm
    subst x
    simp at hx
  exact mul_inv_cancel₀ hne

/-- A permutation of the natural numbers used to reorder a series. -/
def chapter06SeriesPermutation (σ : ℕ → ℕ) : Prop :=
  Function.Bijective σ

private theorem chapter06_comp_tendsToZero_of_finite_threshold
    {ι : Type*} (v : AbsoluteValue K ℝ) (a : ι → K)
    (hfinite : ∀ ε : ℝ, 0 < ε → ({i : ι | ε ≤ v (a i)} : Set ι).Finite)
    {σ : ℕ → ι} (hσ : Function.Injective σ) :
    chapter06TendsToZero v (a ∘ σ) := by
  intro ε hε
  have hbad := hfinite ε hε
  have hev : ∀ᶠ n : ℕ in (atTop : Filter ℕ), v (a (σ n)) < ε := by
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [hσ.tendsto_cofinite.eventually hbad.compl_mem_cofinite] with n hn
    change ¬ ε ≤ v (a (σ n)) at hn
    exact lt_of_not_ge hn
  exact eventually_atTop.1 hev

private theorem chapter06_reindexed_series_converges
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {a : ℕ → K} (hzero : chapter06TendsToZero v a)
    {σ : ℕ → ℕ} (hσ : Function.Bijective σ) {s : K}
    (hs : chapter06SeriesConverges v a s) :
    chapter06SeriesConverges v (a ∘ σ) s := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  obtain ⟨M₀, hM₀⟩ := hs δ hδ
  obtain ⟨N₀, hN₀⟩ := hzero δ hδ
  let g : ℕ → ℕ := fun k => Classical.choose (hσ.2 k)
  have hg : ∀ k : ℕ, σ (g k) = k := fun k => Classical.choose_spec (hσ.2 k)
  let P : Finset ℕ := (Finset.range N₀).image g
  obtain ⟨N, hNP⟩ := Finset.exists_nat_subset_range P
  refine ⟨N, ?_⟩
  intro n hn
  let t : Finset ℕ := (Finset.range n).image σ
  have hlow : Finset.range N₀ ⊆ t := by
    intro k hk
    have hkg : g k ∈ P := by
      dsimp [P]
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hgN : g k ∈ Finset.range N := hNP hkg
    have hgn : g k ∈ Finset.range n :=
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hgN) hn)
    dsimp [t]
    exact Finset.mem_image.mpr ⟨g k, hgn, hg k⟩
  obtain ⟨M₁, hM₁⟩ := Finset.exists_nat_subset_range t
  let M := max M₀ M₁
  have hMt : t ⊆ Finset.range M :=
    hM₁.trans (Finset.range_mono (le_max_right _ _))
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hsumσ : chapter06PartialSums (a ∘ σ) n = Finset.sum t a := by
    dsimp [chapter06PartialSums, t]
    simpa [Function.comp_def] using
      (Finset.sum_image (s := Finset.range n) (f := a) (g := σ)
        hσ.1.injOn).symm
  have hdiff_eq :
      chapter06PartialSums a M - chapter06PartialSums (a ∘ σ) n =
        Finset.sum (Finset.range M \ t) a := by
    rw [hsumσ]
    unfold chapter06PartialSums
    rw [← Finset.sum_sdiff hMt]
    ring
  have htail : v (Finset.sum (Finset.range M \ t) a) < δ := by
    by_cases hne : (Finset.range M \ t).Nonempty
    · apply lt_of_le_of_lt (IsNonarchimedean.apply_sum_le_sup hv hne)
      apply (Finset.sup'_lt_iff _).2
      intro i hi
      have hiN₀ : N₀ ≤ i := by
        apply Nat.le_of_not_gt
        intro hi'
        exact (Finset.mem_sdiff.mp hi).2 (hlow (Finset.mem_range.mpr hi'))
      exact hN₀ i hiN₀
    · have hempty : Finset.range M \ t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [hempty, δ, hδ]
  have hclose : v (chapter06PartialSums (a ∘ σ) n - chapter06PartialSums a M) < δ := by
    simpa only [v.map_sub] using (show v (chapter06PartialSums a M -
      chapter06PartialSums (a ∘ σ) n) < δ from by simpa [hdiff_eq] using htail)
  have hlimit : v (chapter06PartialSums a M - s) < δ := by
    simpa [chapter06Distance] using hM₀ M hM₀M
  change v (chapter06PartialSums (a ∘ σ) n - s) < ε
  calc
    v (chapter06PartialSums (a ∘ σ) n - s) ≤
        v (chapter06PartialSums (a ∘ σ) n - chapter06PartialSums a M) +
          v (chapter06PartialSums a M - s) :=
      v.sub_le _ _ _
    _ < ε := by
      dsimp [δ] at hclose hlimit ⊢
      linarith

/-- Reordering a nonarchimedean series with vanishing terms preserves its sum. -/
theorem chapter06_series_reordering_invariant
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (_hcomplete : chapter06CompleteValuedSpace v) {a : ℕ → K}
    (hzero : chapter06TendsToZero v a) {σ : ℕ → ℕ}
    (hσ : chapter06SeriesPermutation σ) {s : K}
    (hs : chapter06SeriesConverges v a s) :
    chapter06SeriesConverges v (a ∘ σ) s := by
  change Function.Bijective σ at hσ
  exact chapter06_reindexed_series_converges v hv hzero hσ hs

/-- Threshold-finiteness of a doubly indexed family. -/
def chapter06DoubleSeriesThresholdFinite
    (v : AbsoluteValue K ℝ) (a : ℕ × ℕ → K) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ({p : ℕ × ℕ | ε ≤ v (a p)} : Set (ℕ × ℕ)).Finite

/-- Rearrangements of a threshold-finite double series have the same sum. -/
theorem chapter06_double_series_rearrangement
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v)
    {a : ℕ × ℕ → K} (hfinite : chapter06DoubleSeriesThresholdFinite v a)
    {e₁ e₂ : ℕ ≃ ℕ × ℕ} {s₁ s₂ : K}
    (h₁ : chapter06SeriesConverges v (a ∘ e₁) s₁)
    (h₂ : chapter06SeriesConverges v (a ∘ e₂) s₂) :
    s₁ = s₂ := by
  have hzero₁ : chapter06TendsToZero v (a ∘ e₁) := by
    apply chapter06_comp_tendsToZero_of_finite_threshold v a (σ := e₁)
    · exact fun ε hε => hfinite ε hε
    · exact e₁.injective
  let σe : ℕ ≃ ℕ := e₂.trans e₁.symm
  have hσ : chapter06SeriesPermutation σe := σe.bijective
  have hrel : (a ∘ e₁) ∘ σe = a ∘ e₂ := by
    funext n
    simp [σe, Function.comp_def]
  have hconv := chapter06_series_reordering_invariant v hv hcomplete hzero₁ hσ h₁
  have hconv' : chapter06SeriesConverges v (a ∘ e₂) s₁ := by
    simpa [hrel] using hconv
  exact chapter06_limit_unique v hconv' h₂

/-- A threshold-finite double series admits a common sum along every enumeration. -/
theorem chapter06_double_series_has_rearrangement_invariant_sum
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v)
    {a : ℕ × ℕ → K} (hfinite : chapter06DoubleSeriesThresholdFinite v a) :
    ∃ s : K, ∀ e : ℕ ≃ ℕ × ℕ,
      chapter06SeriesConverges v (a ∘ e) s := by
  let e₀ : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  have hzero₀ : chapter06TendsToZero v (a ∘ e₀) := by
    apply chapter06_comp_tendsToZero_of_finite_threshold v a (σ := e₀)
    · exact fun ε hε => hfinite ε hε
    · exact e₀.injective
  obtain ⟨s, hs⟩ :=
    (chapter06_series_converges_iff_terms_tend_to_zero v hv hcomplete (a ∘ e₀)).2 hzero₀
  refine ⟨s, ?_⟩
  intro e
  let σe : ℕ ≃ ℕ := e.trans e₀.symm
  have hσ : chapter06SeriesPermutation σe := σe.bijective
  have hrel : (a ∘ e₀) ∘ σe = a ∘ e := by
    funext n
    simp [σe, Function.comp_def]
  have hconv := chapter06_series_reordering_invariant v hv hcomplete hzero₀ hσ hs
  simpa [hrel] using hconv

/-- The geometric identity in Laurent series `k((t))`. -/
theorem chapter06_laurentSeries_geometric_example
    {k : Type*} [Field k]
    (v : AbsoluteValue (LaurentSeries k) ℝ)
    (hv : IsNonarchimedean v)
    (hcomplete : chapter06CompleteValuedSpace v)
    (hX : v ((PowerSeries.X : PowerSeries k) : LaurentSeries k) < 1) :
    chapter06SeriesConverges v
      (fun n => (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ n))
      (1 - ((PowerSeries.X : PowerSeries k) : LaurentSeries k))⁻¹ := by
  exact chapter06_geometric_series v hv hcomplete hX

/-- The same geometric formula applies in `ℚ_p` for `|x|ₚ < 1`. -/
theorem chapter06_padic_geometric_example
    {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x‖ < 1) :
    chapter06SeriesConverges (NormedField.toAbsoluteValue ℚ_[p])
      (fun n => x ^ n) (1 - x)⁻¹ := by
  have hne : 1 - x ≠ 0 := by
    intro h
    have hx1 : x = 1 := (sub_eq_zero.mp h).symm
    subst x
    norm_num at hx
  have hzero : chapter06TendsToZero (NormedField.toAbsoluteValue ℚ_[p])
      (fun n => x ^ n) := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hx
    refine ⟨N, ?_⟩
    intro n hn
    change ‖x ^ n‖ < ε
    rw [norm_pow]
    exact (pow_le_pow_of_le_one (norm_nonneg x) hx.le hn).trans_lt hN
  have hgeom : ∀ n : ℕ,
      chapter06PartialSums (fun i => x ^ i) n * (1 - x) = 1 - x ^ n := by
    intro n
    induction n with
    | zero => simp [chapter06PartialSums]
    | succ n ih =>
        have hpartial :
            chapter06PartialSums (fun i => x ^ i) (n + 1) =
              chapter06PartialSums (fun i => x ^ i) n + x ^ n := by
          unfold chapter06PartialSums
          rw [Finset.sum_range_succ]
        rw [hpartial]
        rw [add_mul, ih]
        ring
  have hinvpos : 0 < ‖(1 - x)⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero hne)
  intro ε hε
  obtain ⟨N, hN⟩ := hzero (ε / ‖(1 - x)⁻¹‖)
    (div_pos hε hinvpos)
  refine ⟨N, ?_⟩
  intro n hn
  have hsum :
      chapter06PartialSums (fun i => x ^ i) n - (1 - x)⁻¹ =
        -x ^ n * (1 - x)⁻¹ := by
    calc
      chapter06PartialSums (fun i => x ^ i) n - (1 - x)⁻¹ =
          (chapter06PartialSums (fun i => x ^ i) n * (1 - x) - 1) *
            (1 - x)⁻¹ := by
              field_simp [hne]
      _ = (1 - x ^ n - 1) * (1 - x)⁻¹ := by rw [hgeom n]
      _ = -x ^ n * (1 - x)⁻¹ := by ring
  change ‖chapter06PartialSums (fun i => x ^ i) n - (1 - x)⁻¹‖ < ε
  rw [hsum, norm_mul, norm_neg]
  exact (lt_div_iff₀ hinvpos).1 (hN n hn)

/-- The geometric expression `1+p⁻¹+p⁻²+⋯` cannot converge p-adically. -/
theorem chapter06_padic_growing_geometric_series_diverges
    {p : ℕ} [Fact p.Prime] :
    ¬ chapter06SeriesHasSum (NormedField.toAbsoluteValue ℚ_[p])
      (fun n => (p : ℚ_[p]) ^ (-(n : ℤ))) := by
  intro h
  obtain ⟨s, hs⟩ := h
  have hzero := chapter06_series_convergence_implies_terms_tend_to_zero
    (NormedField.toAbsoluteValue ℚ_[p]) hs
  obtain ⟨N, hN⟩ := hzero 1 zero_lt_one
  have hp : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hterm := hN N le_rfl
  have hnorm : ‖(p : ℚ_[p]) ^ (-(N : ℤ))‖ = (p : ℝ) ^ N := by
    simp
  change ‖(p : ℚ_[p]) ^ (-(N : ℤ))‖ < 1 at hterm
  rw [hnorm] at hterm
  exact (not_lt_of_ge (one_le_pow₀ (le_of_lt hp))) hterm

end Series

end

end LastLib.Book01ValuationsDVRsAndCompletions.Chapter06
