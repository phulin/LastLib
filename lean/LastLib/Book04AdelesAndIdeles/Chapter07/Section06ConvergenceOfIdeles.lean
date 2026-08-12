import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies
import LastLib.Book04AdelesAndIdeles.Chapter07.Section01WhyNonzeroAdelesNotEnough

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct

/-! # 7.6 Convergence of ideles -/

/-- The finite-place tail condition appearing in the convergence criterion for restricted
products of multiplicative local groups. -/
def chapter07RestrictedIdeleTailCondition
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, Group (G i)] (B : (i : ι) → Subgroup (G i))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) : Prop :=
  ∃ S : Set ι, S.Finite ∧
    ∀ᶠ n in l, ∀ i ∉ S, f n i * (x i)⁻¹ ∈ B i

/-- The additive analogue of the restricted-product tail condition. -/
def chapter07RestrictedAdditiveTailCondition
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, AddGroup (G i)] (B : (i : ι) → AddSubgroup (G i))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) : Prop :=
  ∃ S : Set ι, S.Finite ∧
    ∀ᶠ n in l, ∀ i ∉ S, f n i - x i ∈ B i

theorem chapter07_restrictedProduct_tendsto_iff
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (B : (i : ι) → Subgroup (G i))
    (hB : ∀ i, IsOpen (B i : Set (G i)))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ i, Tendsto (fun n => f n i) l (𝓝 (x i))) ∧
        chapter07RestrictedIdeleTailCondition G B f x l := by
  sorry

theorem chapter07_restrictedProduct_tendsto_iff_eventually_integral_quotient
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)]
    (B : (i : ι) → Subgroup (G i))
    (hB : ∀ i, IsOpen (B i : Set (G i)))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ i, Tendsto (fun n => f n i) l (𝓝 (x i))) ∧
        ∃ S : Set ι, S.Finite ∧
          ∀ᶠ n in l, ∀ i ∉ S, f n i * (x i)⁻¹ ∈ B i :=
  chapter07_restrictedProduct_tendsto_iff G B hB f x l

theorem chapter07_restrictedProduct_additive_tendsto_iff
    {ι δ : Type*} (G : ι → Type*)
    [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalAddGroup (G i)]
    (B : (i : ι) → AddSubgroup (G i))
    (hB : ∀ i, IsOpen (B i : Set (G i)))
    (f : δ → Πʳ i, [(G i), (B i : Set (G i))])
    (x : Πʳ i, [(G i), (B i : Set (G i))]) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ i, Tendsto (fun n => f n i) l (𝓝 (x i))) ∧
        chapter07RestrictedAdditiveTailCondition G B f x l := by
  sorry

theorem chapter07_idele_tendsto_iff
    {δ : Type*} (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : δ → chapter07IdeleGroup R K)
    (x : chapter07IdeleGroup R K) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n).1.1 v) l (𝓝 (x.1.1 v))) ∧
        (∀ v : chapter07FinitePlace R,
          Tendsto (fun n => (f n).1.2 v) l (𝓝 (x.1.2 v))) ∧
        ∃ S : Set (chapter07FinitePlace R), S.Finite ∧
          ∀ᶠ n in l, ∀ v ∉ S,
            Valued.v ((f n).1.2 v * (x.1.2 v)⁻¹) = 1 := by
  sorry

theorem chapter07_idele_sequence_tendsto_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : ℕ → chapter07IdeleGroup R K) (x : chapter07IdeleGroup R K) :
    Tendsto f atTop (𝓝 x) ↔
      (∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n).1.1 v) atTop (𝓝 (x.1.1 v))) ∧
        (∀ v : chapter07FinitePlace R,
          Tendsto (fun n => (f n).1.2 v) atTop (𝓝 (x.1.2 v))) ∧
        ∃ S : Set (chapter07FinitePlace R), S.Finite ∧
          ∀ᶠ n in atTop, ∀ v ∉ S,
            Valued.v ((f n).1.2 v * (x.1.2 v)⁻¹) = 1 := by
  sorry

theorem chapter07_additive_adele_tendsto_iff
    {δ : Type*} (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : δ → chapter07AdeleRing R K)
    (x : chapter07AdeleRing R K) (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      (∀ v : NumberField.InfinitePlace K,
        Tendsto (fun n => (f n).1 v) l (𝓝 (x.1 v))) ∧
        (∀ v : chapter07FinitePlace R,
          Tendsto (fun n => (f n).2 v) l (𝓝 (x.2 v))) ∧
        ∃ S : Set (chapter07FinitePlace R), S.Finite ∧
          ∀ᶠ n in l, ∀ v ∉ S,
            (f n).2 v - (x.2 v) ∈ chapter07LocalIntegerRing R K v := by
  sorry

theorem chapter07_moving_prime_idele_does_not_tendsto_one :
    ¬ Tendsto chapter07MovingPrimeIdele cofinite
      (𝓝 (1 : chapter07IdeleGroup ℤ ℚ)) := by
  sorry

theorem chapter07_moving_prime_is_additively_convergent_but_not_idelically :
    Tendsto chapter07MovingPrimeAdele cofinite
        (𝓝 (1 : chapter07AdeleRing ℤ ℚ)) ∧
      ¬ Tendsto chapter07MovingPrimeIdele cofinite
        (𝓝 (1 : chapter07IdeleGroup ℤ ℚ)) := by
  exact ⟨chapter07_moving_prime_adele_tendsto_one,
    chapter07_moving_prime_idele_does_not_tendsto_one⟩

theorem chapter07_idele_graph_tendsto_iff
    {δ : Type*} (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (f : δ → chapter07IdeleGroup R K) (x : chapter07IdeleGroup R K)
    (l : Filter δ) :
    Tendsto f l (𝓝 x) ↔
      Tendsto (fun n => chapter07IdeleGraph R K (f n)) l
        (𝓝 (chapter07IdeleGraph R K x)) := by
  sorry

theorem chapter07_idele_inversion_is_continuous
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Continuous (fun x : chapter07IdeleGroup R K => x⁻¹) := by
  sorry

/-- The underlying set of ideles is exactly the set of units of the adele ring. -/
theorem chapter07_idele_underlying_set_iff_adele_is_unit
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    (x : chapter07AdeleRing R K) :
    IsUnit x ↔ ∃ u : chapter07IdeleGroup R K, (u : chapter07AdeleRing R K) = x := by
  sorry

theorem chapter07_idele_underlying_set_eq_adele_units
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Set.range (fun u : chapter07IdeleGroup R K =>
      (u : chapter07AdeleRing R K)) = {x | IsUnit x} := by
  sorry

theorem chapter07_idele_inversion_is_continuous_from_graph_topology
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] :
    Continuous (fun x : chapter07IdeleGroup R K => x⁻¹) :=
  chapter07_idele_inversion_is_continuous R K

end

end LastLib.Book04AdelesAndIdeles.Chapter07
