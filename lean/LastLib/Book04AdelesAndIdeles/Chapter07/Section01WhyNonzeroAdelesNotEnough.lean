import LastLib.Book04AdelesAndIdeles.Chapter07.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter07

noncomputable section

open Set Filter Topology
open scoped BigOperators DirectSum RestrictedProduct

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-! # 7.1 Why nonzero adeles are not enough -/

/-- A book-facing criterion for a unit of the adele ring.  The finite condition is the
restricted-product integrality condition, while the first conjunct records nonvanishing at the
infinite places. -/
theorem chapter07_adele_unit_iff
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (x : chapter07AdeleRing R K) :
    IsUnit x ↔
      (∀ v : NumberField.InfinitePlace K, x.1 v ≠ 0) ∧
        ∀ᶠ v : chapter07FinitePlace R in cofinite, Valued.v (x.2 v) = 1 := by
  sorry

theorem chapter07_adele_unit_iff_local_units_at_almost_all_finite_places
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (x : chapter07AdeleRing R K) :
    IsUnit x ↔
      (∀ v : NumberField.InfinitePlace K, x.1 v ≠ 0) ∧
        ∀ᶠ v : chapter07FinitePlace R in cofinite,
          Valued.v (x.2 v) = 1 := by
  sorry

theorem chapter07_nonzero_adele_need_not_be_an_idele
    [NumberField ℚ] :
    ∃ x : chapter07AdeleRing ℤ ℚ,
      (∀ v : NumberField.InfinitePlace ℚ, x.1 v ≠ 0) ∧
        (∀ v : chapter07FinitePlace ℤ, x.2 v ≠ 0) ∧ ¬ IsUnit x := by
  sorry

/-- The finite adele which is equal to a chosen rational prime at one finite place and to one
everywhere else.  This is the moving-prime family used to test the inherited topology. -/
noncomputable def chapter07MovingPrimeAdele (p : Nat.Primes) :
    chapter07AdeleRing ℤ ℚ :=
  by
    classical
    exact
      ⟨(1 : NumberField.InfiniteAdeleRing ℚ),
        RestrictedProduct.mk
          (fun v : chapter07FinitePlace ℤ =>
            if h : v = (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p then
              h.symm ▸
                Padic.adicCompletionEquiv ℤ p
                  (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ))
            else 1)
          (by sorry)⟩

theorem chapter07_moving_prime_adele_component_at_prime (p : Nat.Primes) :
    (chapter07MovingPrimeAdele p).2
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) =
      Padic.adicCompletionEquiv ℤ p
        (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ)) := by
  sorry

theorem chapter07_moving_prime_adele_component_away_from_prime
    (p : Nat.Primes) (v : chapter07FinitePlace ℤ)
    (hv : v ≠ (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) :
    (chapter07MovingPrimeAdele p).2 v = 1 := by
  sorry

theorem chapter07_moving_prime_adele_is_unit (p : Nat.Primes) :
    IsUnit (chapter07MovingPrimeAdele p) := by
  sorry

/-- The moving-prime family viewed as ideles, using the canonical unit constructor. -/
noncomputable def chapter07MovingPrimeIdele (p : Nat.Primes) :
    chapter07IdeleGroup ℤ ℚ :=
  (chapter07_moving_prime_adele_is_unit p).unit

@[simp]
theorem chapter07MovingPrimeIdele_val (p : Nat.Primes) :
    (chapter07MovingPrimeIdele p : chapter07AdeleRing ℤ ℚ) =
      chapter07MovingPrimeAdele p := by
  sorry

theorem chapter07_moving_prime_adele_tendsto_one :
    Tendsto chapter07MovingPrimeAdele cofinite
      (𝓝 (1 : chapter07AdeleRing ℤ ℚ)) := by
  sorry

/-- The moving-prime family converges to one for the additive topology pulled back to the units. -/
def chapter07NaiveIdeleTendsto
    {ι : Type*} (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (f : ι → chapter07IdeleGroup R K)
    (l : Filter ι) (x : chapter07IdeleGroup R K) : Prop :=
  Tendsto f l (@nhds (chapter07IdeleGroup R K)
    (chapter07NaiveIdeleTopology R K) x)

theorem chapter07_moving_prime_naive_tendsto_one :
    chapter07NaiveIdeleTendsto ℤ ℚ chapter07MovingPrimeIdele cofinite 1 := by
  sorry

theorem chapter07_moving_prime_inverse_component_at_prime (p : Nat.Primes) :
    ((chapter07MovingPrimeIdele p)⁻¹ : chapter07IdeleGroup ℤ ℚ).1.2
        ((Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p) =
      Padic.adicCompletionEquiv ℤ p
        (algebraMap ℚ (ℚ_[p]) (p.1 : ℚ))⁻¹ := by
  sorry

/-- Inversion is not continuous for the naive subspace topology. -/
theorem chapter07_naive_idele_inversion_not_continuous :
    ¬ @Continuous (chapter07IdeleGroup ℤ ℚ) (chapter07IdeleGroup ℤ ℚ)
      (chapter07NaiveIdeleTopology ℤ ℚ) (chapter07NaiveIdeleTopology ℤ ℚ)
      (fun x => x⁻¹) := by
  sorry

theorem chapter07_naive_idele_topology_is_not_a_topological_group :
    ¬ @ContinuousMul (chapter07IdeleGroup ℤ ℚ)
      (chapter07NaiveIdeleTopology ℤ ℚ)
      (inferInstance : Mul (chapter07IdeleGroup ℤ ℚ)) := by
  sorry

end

end LastLib.Book04AdelesAndIdeles.Chapter07
