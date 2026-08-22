import LastLib.Book03RamificationTheory.Chapter05.Section05ATwoBreakTower
import Mathlib.FieldTheory.Fixed
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Valuation.Discrete.RankOne

namespace LastLib.Book03RamificationTheory.Chapter05

noncomputable section

open scoped BigOperators

/-! ## 5.6. Hasse--Arf and the limits of integrality -/

/-- Perfectness of the residue field attached to a normalized additive valuation. -/
def chapter05PerfectResidueField
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) : Prop :=
  PerfectField (IsLocalRing.ResidueField v.toValuation.valuationSubring)

/-- Every upper break of a profile is integral. -/
def chapter05AllUpperBreaksIntegral
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Prop :=
  ∀ v : ℝ, chapter05UpperBreak D v → chapter05UpperBreakIsInteger v

/- Chapter 4 uses a separate integer-profile interface, while this chapter
   needs its real, left-continuous extension together with the local valuation
   hypotheses used by Hasse--Arf.  This structure is therefore a local bridge,
   and its canonical field points directly to the Book 2 congruence groups. -/
structure Chapter05LocalGaloisUpperData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))] where
  vK : AddValuation K (WithTop ℤ)
  vL : AddValuation L (WithTop ℤ)
  vK_rank_one_discrete : Valuation.IsRankOneDiscrete vK.toValuation
  vL_rank_one_discrete : Valuation.IsRankOneDiscrete vL.toValuation
  restriction :
    vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)
  base_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal vK.toValuation.valuationSubring)
      vK.toValuation.valuationSubring
  extension_complete :
    IsAdicComplete (IsLocalRing.maximalIdeal vL.toValuation.valuationSubring)
      vL.toValuation.valuationSubring
  /- Valuation extensions are unique up to valuation equivalence.  Requiring
     literal equality of every equivalent `WithTop ℤ`-valued valuation would
     impose an extra normalization not supplied by the local-field
     hypotheses. -/
  unique_valuation_extension :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05UniqueValuationExtension
      vK.toValuation vL.toValuation
  decomposition_top :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05DecompositionGroup
      K vL.toValuation.valuationSubring = ⊤
  profile : Chapter05RamificationFiltration (Gal(L / K))
  lower_canonical :
    ∀ n : ℕ,
      profile.lowerGroup (n : ℝ) =
        chapter05RamificationGroupInG (F := K)
          vL.toValuation.valuationSubring (n + 1)

namespace Chapter05LocalGaloisUpperData

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]

theorem lower_canonical_at
    (D : Chapter05LocalGaloisUpperData K L) (n : ℕ) :
    D.profile.lowerGroup (n : ℝ) =
      chapter05RamificationGroupInG (F := K)
        D.vL.toValuation.valuationSubring (n + 1) := by
  exact D.lower_canonical n

end Chapter05LocalGaloisUpperData

/-
 The manuscript's proof of Hasse--Arf requires the local Sen congruence for
 the fixed ideals of all iterates of one automorphism.  That local-intersection
 theorem is not proved in Books 1--3.  This class records exactly the
 ramification-number consequence used by the unfinished proof route.  It is
 auxiliary proof-support theorem; the source-facing Hasse--Arf statements
 below retain the manuscript's hypotheses and do not make this route an
 extra mathematical assumption.

 If `σ` generates a cyclic wild group of order `p ^ s`, the conclusion is
 `p ^ r ∣ i(σ^(p^r)) - i(σ^(p^(r-1)))`, equivalently the congruence for the
 corresponding ramification numbers after subtracting one from both terms.
-/
theorem chapter05_local_sen_ramification_number_congruence
    : ∀ {K L : Type*} [Field K] [Field L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
      (D : Chapter05LocalGaloisUpperData K L)
      (p r s : ℕ)
      (_hchar : CharP
        (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring) p)
      (_hp : p.Prime) (_hr : 0 < r) (_hrs : r < s)
      (σ : Gal(L / K))
      (_hwild : σ ∈ D.profile.lowerGroup 1)
      (_horder : orderOf σ = p ^ s),
      ((p : ℤ) ^ r) ∣
        (D.profile.displacement (σ ^ (p ^ r)) : ℤ) -
          (D.profile.displacement (σ ^ (p ^ (r - 1))) : ℤ) := by
  sorry

/-!
  The preceding consequence is the special prime-power step used by the
  unfinished arithmetic route.  This interface records the full
  source-facing cyclic congruence as well: the ramification number depends
  only on the p-adic order of the exponent, and exponents congruent modulo
  p^a give ramification numbers congruent modulo p^(a+1).  Integer exponents
  retain the source's formulation for arbitrary k₁ and k₂.
-/
def chapter05SenRamificationNumber
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L) (σ : Gal(L / K)) (k : ℤ) : ℕ :=
  D.profile.displacement (σ ^ k)

structure Chapter05SenCyclicCongruenceData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (σ : Gal(L / K)) where
  p : ℕ
  wild_exponent : ℕ
  p_prime : Nat.Prime p
  wild_exponent_pos : 0 < wild_exponent
  residue_characteristic : CharP
    (IsLocalRing.ResidueField D.vL.toValuation.valuationSubring) p
  sigma_order : orderOf σ = p ^ wild_exponent
  sigma_generates : ∀ τ : Gal(L / K), ∃ k : ℤ, τ = σ ^ k
  wild : σ ∈ D.profile.lowerGroup 1
  c_depends_only_on_padic_order :
    ∀ {k₁ k₂ : ℤ},
      ¬((p ^ wild_exponent : ℕ) : ℤ) ∣ k₁ →
      ¬((p ^ wild_exponent : ℕ) : ℤ) ∣ k₂ →
      padicValInt p k₁ = padicValInt p k₂ →
      chapter05SenRamificationNumber D σ k₁ =
        chapter05SenRamificationNumber D σ k₂
  c_congruent_of_exponent_congruent :
    ∀ {a : ℕ} {k₁ k₂ : ℤ},
      a < wild_exponent →
      ¬((p ^ wild_exponent : ℕ) : ℤ) ∣ k₁ →
      ¬((p ^ wild_exponent : ℕ) : ℤ) ∣ k₂ →
      ((p : ℤ) ^ a) ∣ k₁ - k₂ →
      Int.ModEq (p ^ (a + 1))
        (chapter05SenRamificationNumber D σ k₁ : ℤ)
        (chapter05SenRamificationNumber D σ k₂ : ℤ)

theorem chapter05_sen_cyclic_congruence_depends_only_on_padic_order
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    {D : Chapter05LocalGaloisUpperData K L}
    {σ : Gal(L / K)}
    (S : Chapter05SenCyclicCongruenceData D σ)
    {k₁ k₂ : ℤ}
    (hk₁ : ¬((S.p ^ S.wild_exponent : ℕ) : ℤ) ∣ k₁)
    (hk₂ : ¬((S.p ^ S.wild_exponent : ℕ) : ℤ) ∣ k₂)
    (hval : padicValInt S.p k₁ = padicValInt S.p k₂) :
    chapter05SenRamificationNumber D σ k₁ =
      chapter05SenRamificationNumber D σ k₂ := by
  exact S.c_depends_only_on_padic_order hk₁ hk₂ hval

theorem chapter05_sen_cyclic_congruence_modulus
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    {D : Chapter05LocalGaloisUpperData K L}
    {σ : Gal(L / K)}
    (S : Chapter05SenCyclicCongruenceData D σ)
    {a : ℕ} {k₁ k₂ : ℤ}
    (ha : a < S.wild_exponent)
    (hk₁ : ¬((S.p ^ S.wild_exponent : ℕ) : ℤ) ∣ k₁)
    (hk₂ : ¬((S.p ^ S.wild_exponent : ℕ) : ℤ) ∣ k₂)
    (hcongruent : ((S.p : ℤ) ^ a) ∣ k₁ - k₂) :
    Int.ModEq (S.p ^ (a + 1))
      (chapter05SenRamificationNumber D σ k₁ : ℤ)
      (chapter05SenRamificationNumber D σ k₂ : ℤ) := by
  exact S.c_congruent_of_exponent_congruent ha hk₁ hk₂ hcongruent

/-- The normalized lower-group sum in the cyclic Hasse--Arf lemma. -/
def chapter05CyclicHasseArfSum
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (b : ℕ) : ℚ :=
  (Finset.sum (Finset.Icc 1 b)
      (fun i => (Nat.card (D.lowerGroup (i : ℝ)) : ℚ))) /
    (Nat.card (D.lowerGroup 0) : ℚ)

/-!
  The cyclic proof in the source has three arithmetic inputs.  They are kept
  separate from the final integrality statement: the fixed-point input gives
  divisibility, the ramification-number input turns that divisibility into
  congruences, and the lower-layer input performs the final finite sum.

  The first record is the kernel-facing part of the periodic fixed-point
  argument.  `primitive_period_count` is the Moebius-inverted fixed-point
  multiplicity.  The specialized prime-power identity is the only part of
  the inversion used by the ramification-number congruence below.
-/
structure Chapter05CyclicFixedPointMultiplicityData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (σ : Gal(L / K)) where
  automorphism_order : ℕ
  automorphism_order_pos : 0 < automorphism_order
  automorphism_period : σ ^ automorphism_order = 1
  automorphism_order_minimal :
    ∀ {n : ℕ}, σ ^ n = 1 → automorphism_order ∣ n
  /- `fixed_point_length n` is the length of the fixed-point scheme of
     `σ ^ n`; `primitive_period_count` is its Moebius inversion.  Keeping
     these as lengths, rather than as arbitrary signed numbers, matches the
     periodic-point argument and leaves the divisibility conclusion to the
     theorem below. -/
  fixed_point_length : ℕ → ℕ
  fixed_point_length_nontrivial :
    ∀ {n : ℕ}, σ ^ n ≠ 1 → 0 < fixed_point_length n
  primitive_period_count : ℕ → ℕ
  primitive_period_count_eq_periodic_orbits :
    ∃ periodic_orbit_count : ℕ → ℕ,
      (∀ n : ℕ,
        primitive_period_count n = periodic_orbit_count n) ∧
      (∀ {n : ℕ}, 0 < n → n ∣ periodic_orbit_count n)
  prime_power_mobius_identity :
    ∀ {p r : ℕ}, Nat.Prime p → 0 < r →
      primitive_period_count (p ^ r) =
        fixed_point_length (p ^ r) - fixed_point_length (p ^ (r - 1))

theorem chapter05_cyclic_fixed_point_multiplicity_divisibility
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    {D : Chapter05LocalGaloisUpperData K L}
    {σ : Gal(L / K)}
    (P : Chapter05CyclicFixedPointMultiplicityData D σ)
    {n : ℕ} (hn : 0 < n) :
    n ∣ P.primitive_period_count n := by
  rcases P.primitive_period_count_eq_periodic_orbits with
    ⟨periodic_orbit_count, hcount, hdiv⟩
  rw [hcount]
  exact hdiv hn

/-!
  A ramification-number datum records the value of the fixed-point
  multiplicity at the prime powers of the wild order.  The congruence theorem
  below is deliberately stated before any lower-group sum: it cannot assume
  Hasse--Arf or the integrality of that sum.
-/
structure Chapter05CyclicRamificationNumberData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    {D : Chapter05LocalGaloisUpperData K L}
    {σ : Gal(L / K)}
    (P : Chapter05CyclicFixedPointMultiplicityData D σ) where
  p : ℕ
  tame_factor : ℕ
  p_prime : Nat.Prime p
  tame_factor_coprime_p : Nat.Coprime tame_factor p
  wild_exponent : ℕ
  q : ℕ → ℕ
  q_prime_power :
    ∀ {r : ℕ}, r < wild_exponent →
      q r + 1 = P.fixed_point_length (p ^ r)
  q_monotone :
    ∀ {r : ℕ}, 0 < r → r < wild_exponent → q (r - 1) ≤ q r

theorem chapter05_cyclic_ramification_number_congruence
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    {D : Chapter05LocalGaloisUpperData K L}
    {σ : Gal(L / K)}
    (P : Chapter05CyclicFixedPointMultiplicityData D σ)
    (Q : Chapter05CyclicRamificationNumberData P)
    {r : ℕ} (hr : 0 < r) (hr_last : r < Q.wild_exponent) :
    Q.p ^ r ∣ Q.q r - Q.q (r - 1) := by
  have hr_prev : r - 1 < Q.wild_exponent := by
    exact lt_of_le_of_lt (Nat.sub_le r 1) hr_last
  have hdiv :
      Q.p ^ r ∣ P.primitive_period_count (Q.p ^ r) :=
    chapter05_cyclic_fixed_point_multiplicity_divisibility P
      (by exact pow_pos Q.p_prime.pos r)
  rw [P.prime_power_mobius_identity Q.p_prime hr] at hdiv
  rw [← Q.q_prime_power hr_last, ← Q.q_prime_power hr_prev] at hdiv
  simpa [Nat.add_sub_add_right] using hdiv

/-!
  The following record is the finite lower-layer calculation after the
  congruence has been established.  `tame_factor` is the prime-to-`p` factor
  of inertia.  `qPrevious` makes the initial layer explicit (`qPrevious 0 =
  0`) and avoids an informal negative index in the Lean statement.
-/
structure Chapter05CyclicLowerLayerShape
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (b : ℕ) where
  tame_factor : ℕ
  tame_factor_pos : 0 < tame_factor
  p : ℕ
  p_prime : Nat.Prime p
  wild_exponent : ℕ
  wild_exponent_pos : 0 < wild_exponent
  q : ℕ → ℕ
  qPrevious : ℕ → ℕ
  qPrevious_zero : qPrevious 0 = 0
  qPrevious_succ : ∀ r : ℕ, qPrevious (r + 1) = q r
  zeroth_cardinality :
    Nat.card (D.lowerGroup 0) = tame_factor * p ^ wild_exponent
  last_break : q (wild_exponent - 1) = b
  layer_order :
    ∀ {r i : ℕ}, r < wild_exponent → qPrevious r < i → i ≤ q r →
      Nat.card (D.lowerGroup (i : ℝ)) = p ^ (wild_exponent - r)
  layer_breaks_strict :
    ∀ {r : ℕ}, r < wild_exponent → qPrevious r < q r
  tame_divides_first_break : tame_factor ∣ q 0

/- The divisibility of the later jumps is the output of the
   ramification-number congruence, not part of the filtration shape. -/
structure Chapter05CyclicLowerLayerDecomposition
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) (b : ℕ)
    extends Chapter05CyclicLowerLayerShape D b where
  tame_wild_jump_divisibility :
    ∀ {r : ℕ}, 0 < r → r < wild_exponent →
      tame_factor * p ^ r ∣ q r - q (r - 1)

/-!
  This is the complete local arithmetic interface used by the cyclic proof.
  The fixed-point and ramification-number records are tied to the lower-layer
  shape by the displayed parameter equalities.  The tame-factor relation is an
  explicit field of this interface; weighted jump divisibility is produced by
  the decomposition theorem below, and final integrality is not an input field.
-/
structure Chapter05CyclicLocalArithmeticInterface
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (σ : Gal(L / K)) (b : ℕ) where
  cyclic_group : IsCyclic (Gal(L / K))
  /- A generator of the full cyclic inertia group.  The wild generator is its
     `tame_factor`-th power, as in the source's decomposition
     `|C| = tame_factor * p ^ wild_exponent`. -/
  cyclic_generator : Gal(L / K)
  fixed_point : Chapter05CyclicFixedPointMultiplicityData D σ
  ramification_number :
    Chapter05CyclicRamificationNumberData fixed_point
  layer_shape :
    Chapter05CyclicLowerLayerShape D.profile b
  cyclic_generator_zpowers : Subgroup.zpowers cyclic_generator = ⊤
  wild_generator_eq :
    cyclic_generator ^ layer_shape.tame_factor = σ
  wild_generator_mem_lower_one : σ ∈ D.profile.lowerGroup 1
  p_eq : layer_shape.p = ramification_number.p
  wild_exponent_eq :
    layer_shape.wild_exponent = ramification_number.wild_exponent
  automorphism_order_eq :
    fixed_point.automorphism_order =
      ramification_number.p ^ ramification_number.wild_exponent
  q_eq : ∀ r : ℕ,
    layer_shape.q r = ramification_number.q r
  tame_factor_eq :
    layer_shape.tame_factor = ramification_number.tame_factor
  /- Comparing the tame character on the leading term of
     `σ ^ (p ^ r)` with commutation by `cyclic_generator` gives
     `ζ ^ (q r) = 1`.  Since `ζ` has exact order `tame_factor`, this is
     precisely the reusable prime-to-`p` divisibility consequence. -/
  tame_character_divisibility :
    ∀ {r : ℕ}, r < layer_shape.wild_exponent →
      layer_shape.tame_factor ∣ layer_shape.q r

/-- The tame character forces every positive ramification number of a cyclic
inertia group to be divisible by the order of its tame quotient. -/
theorem chapter05_cyclic_tame_character_divisibility
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    {D : Chapter05LocalGaloisUpperData K L}
    {σ : Gal(L / K)} {b r : ℕ}
    (A : Chapter05CyclicLocalArithmeticInterface D σ b)
    (hr : r < A.layer_shape.wild_exponent) :
    A.layer_shape.tame_factor ∣ A.layer_shape.q r := by
  exact A.tame_character_divisibility hr

theorem chapter05_cyclic_local_arithmetic_lower_layer_decomposition
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    {σ : Gal(L / K)} {b : ℕ}
    (A : Chapter05CyclicLocalArithmeticInterface D σ b) :
    Nonempty (Chapter05CyclicLowerLayerDecomposition D.profile b) := by
  refine ⟨{ A.layer_shape with tame_wild_jump_divisibility := ?_ }⟩
  intro r hr hr_last
  have hr_prev : r - 1 < A.layer_shape.wild_exponent :=
    lt_of_le_of_lt (Nat.sub_le r 1) hr_last
  have htame_r : A.layer_shape.tame_factor ∣ A.layer_shape.q r :=
    chapter05_cyclic_tame_character_divisibility A hr_last
  have htame_prev :
      A.layer_shape.tame_factor ∣ A.layer_shape.q (r - 1) :=
    chapter05_cyclic_tame_character_divisibility A hr_prev
  have htame :
      A.layer_shape.tame_factor ∣
        A.layer_shape.q r - A.layer_shape.q (r - 1) :=
    Nat.dvd_sub htame_r htame_prev
  have hp :
      A.layer_shape.p ^ r ∣
        A.layer_shape.q r - A.layer_shape.q (r - 1) := by
    rw [A.p_eq, A.q_eq, A.q_eq]
    apply chapter05_cyclic_ramification_number_congruence
      A.fixed_point A.ramification_number hr
    rwa [← A.wild_exponent_eq]
  have hcoprime :
      Nat.Coprime A.layer_shape.tame_factor (A.layer_shape.p ^ r) := by
    rw [A.p_eq, A.tame_factor_eq]
    exact A.ramification_number.tame_factor_coprime_p.pow_right r
  exact hcoprime.mul_dvd_of_dvd_of_dvd htame hp

theorem chapter05_cyclic_lower_layer_sum_decomposition
    {G : Type*} [Group G] [Finite G]
    {D : Chapter05RamificationFiltration G} {b : ℕ}
    (A : Chapter05CyclicLowerLayerDecomposition D b) :
    chapter05CyclicHasseArfSum D b =
      (A.q 0 : ℚ) / A.tame_factor +
        ∑ r ∈ Finset.Icc 1 (A.wild_exponent - 1),
          ((A.q r - A.q (r - 1) : ℕ) : ℚ) /
            ((A.tame_factor * A.p ^ r : ℕ) : ℚ) := by
  have hfirst :
      (∑ i ∈ Finset.Icc 1 (A.q 0),
        Nat.card (D.lowerGroup (i : ℝ))) =
        A.q 0 * A.p ^ A.wild_exponent := by
    rw [Finset.sum_const_nat (m := A.p ^ A.wild_exponent)]
    · simp
    · intro i hi
      have hi' := Finset.mem_Icc.mp hi
      exact A.layer_order (r := 0) (i := i)
        A.wild_exponent_pos
        (by simpa [A.qPrevious_zero] using (show 0 < i by omega))
        hi'.2
  have hsum_interval (l u c : ℕ) (hlu : l ≤ u)
      (hconst : ∀ i ∈ Finset.Icc (l + 1) u,
        Nat.card (D.lowerGroup (i : ℝ)) = c) :
      (∑ i ∈ Finset.Icc (l + 1) u,
        Nat.card (D.lowerGroup (i : ℝ))) = (u - l) * c := by
    rw [Finset.sum_const_nat (m := c)]
    · have hcard : u + 1 - (l + 1) = u - l := by omega
      rw [Nat.card_Icc, hcard]
    · exact hconst
  have hq_succ {r : ℕ} (hr : r + 1 < A.wild_exponent) :
      A.q r < A.q (r + 1) := by
    have h := A.layer_breaks_strict (r := r + 1) hr
    rw [A.qPrevious_succ r] at h
    exact h
  have hprefix : ∀ r : ℕ, r < A.wild_exponent →
      (∑ i ∈ Finset.Icc 1 (A.q r),
        Nat.card (D.lowerGroup (i : ℝ))) =
        A.q 0 * A.p ^ A.wild_exponent +
          ∑ k ∈ Finset.Icc 1 r,
            (A.q k - A.q (k - 1)) *
              A.p ^ (A.wild_exponent - k) := by
    intro r
    induction r with
    | zero =>
        intro hr
        simpa using hfirst
    | succ r ihr =>
        intro hr
        have hr_lt : r < A.wild_exponent := by omega
        have ih := ihr hr_lt
        have hq : A.q r < A.q (r + 1) := hq_succ hr
        have hnew :
            (∑ i ∈ Finset.Icc (A.q r + 1) (A.q (r + 1)),
              Nat.card (D.lowerGroup (i : ℝ))) =
              (A.q (r + 1) - A.q r) *
                A.p ^ (A.wild_exponent - (r + 1)) := by
          apply hsum_interval (A.q r) (A.q (r + 1))
            (A.p ^ (A.wild_exponent - (r + 1))) hq.le
          intro i hi
          have hi' := Finset.mem_Icc.mp hi
          apply A.layer_order (r := r + 1) (i := i) hr
          · rw [A.qPrevious_succ r]
            omega
          · exact hi'.2
        have hset :
            Finset.Icc 1 (A.q (r + 1)) =
              Finset.Icc 1 (A.q r) ∪
                Finset.Icc (A.q r + 1) (A.q (r + 1)) := by
          ext i
          simp only [Finset.mem_Icc, Finset.mem_union]
          omega
        have hdisj :
            Disjoint (Finset.Icc 1 (A.q r))
              (Finset.Icc (A.q r + 1) (A.q (r + 1))) := by
          rw [Finset.disjoint_left]
          intro i hi₁ hi₂
          have hi₁' := Finset.mem_Icc.mp hi₁
          have hi₂' := Finset.mem_Icc.mp hi₂
          omega
        rw [hset, Finset.sum_union hdisj, ih, hnew]
        have hks :
            Finset.Icc 1 (r + 1) =
              insert (r + 1) (Finset.Icc 1 r) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnotmem : r + 1 ∉ Finset.Icc 1 r := by
          simp [Finset.mem_Icc]
        rw [hks, Finset.sum_insert hnotmem]
        simp
        ac_rfl
  have hexp : A.wild_exponent - 1 < A.wild_exponent := by
    exact Nat.sub_lt A.wild_exponent_pos Nat.zero_lt_one
  have hlast := hprefix (A.wild_exponent - 1) hexp
  have htame : (A.tame_factor : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt A.tame_factor_pos)
  have hp : (A.p : ℚ) ≠ 0 := by
    exact_mod_cast A.p_prime.ne_zero
  have hsum_bound :
      (∑ i ∈ Finset.Icc 1 b,
        (Nat.card (D.lowerGroup (i : ℝ)) : ℚ)) =
      ∑ i ∈ Finset.Icc 1 (A.q (A.wild_exponent - 1)),
        (Nat.card (D.lowerGroup (i : ℝ)) : ℚ) := by
    simp only [A.last_break]
  have hlastq :
      (∑ i ∈ Finset.Icc 1 (A.q (A.wild_exponent - 1)),
        (Nat.card (D.lowerGroup (i : ℝ)) : ℚ)) =
      ((A.q 0 * A.p ^ A.wild_exponent : ℕ) : ℚ) +
        ∑ k ∈ Finset.Icc 1 (A.wild_exponent - 1),
          (((A.q k - A.q (k - 1)) *
            A.p ^ (A.wild_exponent - k) : ℕ) : ℚ) := by
    have hcast := congrArg (fun n : ℕ => (n : ℚ)) hlast
    simpa only [Nat.cast_add, Nat.cast_sum] using hcast
  unfold chapter05CyclicHasseArfSum
  rw [hsum_bound, hlastq, A.zeroth_cardinality]
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [add_div, Finset.sum_div]
  have hzero :
      (A.q 0 : ℚ) * (A.p : ℚ) ^ A.wild_exponent /
          ((A.tame_factor : ℚ) * (A.p : ℚ) ^ A.wild_exponent) =
        (A.q 0 : ℚ) / A.tame_factor := by
    field_simp [htame, hp]
  rw [hzero]
  have hsum_terms :
      (∑ r ∈ Finset.Icc 1 (A.wild_exponent - 1),
        ((A.q r - A.q (r - 1) : ℕ) : ℚ) *
            (A.p : ℚ) ^ (A.wild_exponent - r) /
              ((A.tame_factor : ℚ) * (A.p : ℚ) ^ A.wild_exponent)) =
      ∑ r ∈ Finset.Icc 1 (A.wild_exponent - 1),
        ((A.q r - A.q (r - 1) : ℕ) : ℚ) /
          ((A.tame_factor : ℚ) * (A.p : ℚ) ^ r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    have hpow :
        (A.p : ℚ) ^ (A.wild_exponent - r) * (A.p : ℚ) ^ r =
          (A.p : ℚ) ^ A.wild_exponent := by
      rw [← pow_add, Nat.sub_add_cancel (by omega : r ≤ A.wild_exponent)]
    field_simp [htame, hp]
    rw [mul_assoc, hpow]
  exact congrArg
    (fun x : ℚ => (A.q 0 : ℚ) / A.tame_factor + x) hsum_terms

theorem chapter05_cyclic_lower_layer_sum_integral
    {G : Type*} [Group G] [Finite G]
    {D : Chapter05RamificationFiltration G} {b : ℕ}
    (A : Chapter05CyclicLowerLayerDecomposition D b) :
    ∃ z : ℤ, (z : ℚ) = chapter05CyclicHasseArfSum D b := by
  classical
  let c0 : ℕ := Classical.choose A.tame_divides_first_break
  have hc0 : A.q 0 = A.tame_factor * c0 := by
    exact Classical.choose_spec A.tame_divides_first_break
  let c : ℕ → ℕ := fun r =>
    if hr : 0 < r ∧ r < A.wild_exponent then
      Classical.choose (A.tame_wild_jump_divisibility hr.1 hr.2)
    else 0
  have hc {r : ℕ} (hr : 0 < r) (hrlt : r < A.wild_exponent) :
      A.q r - A.q (r - 1) =
        A.tame_factor * A.p ^ r * c r := by
    dsimp [c]
    rw [dif_pos ⟨hr, hrlt⟩]
    exact Classical.choose_spec (A.tame_wild_jump_divisibility hr hrlt)
  have htame : (A.tame_factor : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt A.tame_factor_pos)
  have hp : (A.p : ℚ) ≠ 0 := by
    exact_mod_cast A.p_prime.ne_zero
  have hzero :
      (A.q 0 : ℚ) / A.tame_factor = (c0 : ℚ) := by
    rw [hc0]
    simp only [Nat.cast_mul]
    field_simp [htame]
  have hterm {r : ℕ} (hr : r ∈ Finset.Icc 1 (A.wild_exponent - 1)) :
      ((A.q r - A.q (r - 1) : ℕ) : ℚ) /
          ((A.tame_factor * A.p ^ r : ℕ) : ℚ) = (c r : ℚ) := by
    have hr' := Finset.mem_Icc.mp hr
    have hcr := hc hr'.1 (by omega : r < A.wild_exponent)
    rw [hcr]
    simp only [Nat.cast_mul, Nat.cast_pow]
    field_simp [htame, hp]
  let z : ℤ := (c0 : ℤ) + ∑ r ∈ Finset.Icc 1 (A.wild_exponent - 1), (c r : ℤ)
  refine ⟨z, ?_⟩
  rw [chapter05_cyclic_lower_layer_sum_decomposition A]
  simp only [z, Int.cast_add, Int.cast_sum]
  norm_num
  have hsum :
      (∑ r ∈ Finset.Icc 1 (A.wild_exponent - 1), (c r : ℚ)) =
        ∑ r ∈ Finset.Icc 1 (A.wild_exponent - 1),
          ((A.q r - A.q (r - 1) : ℕ) : ℚ) /
            ((A.tame_factor * A.p ^ r : ℕ) : ℚ) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact (hterm hr).symm
  rw [hzero, hsum]
  simp only [Nat.cast_mul, Nat.cast_pow]

theorem chapter05_cyclic_local_arithmetic_integrality
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    {σ : Gal(L / K)} {b : ℕ}
    (A : Chapter05CyclicLocalArithmeticInterface D σ b) :
    ∃ z : ℤ, (z : ℚ) = chapter05CyclicHasseArfSum D.profile b := by
  rcases chapter05_cyclic_local_arithmetic_lower_layer_decomposition D A with
    ⟨A'⟩
  exact chapter05_cyclic_lower_layer_sum_integral A'

/-- The canonical fixed field cut out by a character kernel. -/
abbrev chapter05CharacterKernelFixedField
    {K L C : Type*} [Field K] [Field L] [Algebra K L] [Group C]
    (χ : Gal(L / K) →* C) : IntermediateField K L :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField
    (MonoidHom.ker χ)

/-!
 A character-kernel package records the field-level quotient needed by the
 cyclic Hasse--Arf argument.  The transfer field is the source of the
 normalized fixed-field valuation and canonical quotient profile; the local
 quotient record supplies the exact interface expected by the cyclic lemma.
-/
structure Chapter05CharacterKernelHasseArfData
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    [FiniteDimensional K (chapter05CharacterKernelFixedField χ)]
    [IsGalois K (chapter05CharacterKernelFixedField χ)]
    [Finite (Gal(chapter05CharacterKernelFixedField χ / K))]
    [FiniteDimensional (chapter05CharacterKernelFixedField χ) L]
    [IsGalois (chapter05CharacterKernelFixedField χ) L]
    [Finite (Gal(L / chapter05CharacterKernelFixedField χ))] where
  character_surjective : Function.Surjective χ
  character_cyclic : IsCyclic C
  local_data : Chapter05LocalGaloisUpperData K L
  transfer :
    Chapter05FixedFieldSubextensionTransfer (MonoidHom.ker χ) local_data.profile
  /- The abstract quotient setup is the structural input for applying the
     quotient theorem to the character kernel.  It records a local-field
     realization and a profile transport, rather than assuming the upper
     compatibility that the quotient theorem is meant to prove. -/
  quotient_setup :
    Chapter05QuotientRamificationSetup (Gal(L / K)) (MonoidHom.ker χ)
  quotient_setup_upstairs_eq : quotient_setup.upstairs = local_data.profile
  quotient_local :
    Chapter05LocalGaloisUpperData K (chapter05CharacterKernelFixedField χ)
  /- The cyclic quotient may still have an unramified stage.  Its inertia
     fixed field is a second fixed-field transfer, distinct from `transfer`,
     which concerns the original χ-kernel extension. -/
  quotient_inertia_transfer :
    Chapter05FixedFieldSubextensionTransfer
      (quotient_local.profile.lowerGroup 0)
      quotient_local.profile
  /- The top valuation in the inertia transfer is the valuation used by
     `quotient_local`.  This is the valuation-subring compatibility needed
     to reuse the canonical quotient profile at the transfer's top field. -/
  quotient_inertia_top_valuation_eq :
    quotient_local.vL = quotient_inertia_transfer.vL
  /- Both transfer records describe extensions over the same base field `K`.
     This equality transports residue-field hypotheses to the base valuation
     expected by the canonical inertia bridge. -/
  quotient_inertia_base_valuation_eq :
    quotient_local.vK = quotient_inertia_transfer.vK
  /- The base of the totally ramified inertia stage is the transfer's `vM`,
     not the original valuation on `K`; its residue perfectness is therefore
     recorded at that exact stage. -/
  quotient_inertia_base_residue_perfect :
    PerfectField
      (IsLocalRing.ResidueField
        quotient_inertia_transfer.vM.toValuation.valuationSubring)
  quotient_galois_equiv :
    (Gal(L / K) ⧸ MonoidHom.ker χ) ≃*
      Gal(chapter05CharacterKernelFixedField χ / K)
  quotient_profile_transport :
    ∀ u : ℝ,
      quotient_local.profile.lowerGroup u =
        (quotient_setup.downstairs.lowerGroup u).map
          quotient_galois_equiv.toMonoidHom
  quotient_profile_eq : quotient_local.profile = transfer.quotient_profile
  quotient_base_valuation_eq : quotient_local.vK = transfer.vK
  quotient_extension_valuation_eq : quotient_local.vL = transfer.vM
  quotient_cyclic :
    IsCyclic (Gal(chapter05CharacterKernelFixedField χ / K))
  base_residue_perfect :
      PerfectField
      (IsLocalRing.ResidueField local_data.vK.toValuation.valuationSubring)
  quotient_residue_perfect :
    PerfectField
      (IsLocalRing.ResidueField quotient_local.vK.toValuation.valuationSubring)

theorem chapter05_character_kernel_quotient_profile_canonical_at_inertia_top
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ) (n : ℕ) :
    R.quotient_local.profile.lowerGroup (n : ℝ) =
      chapter05RamificationGroupInG (F := K)
        R.quotient_inertia_transfer.vL.toValuation.valuationSubring (n + 1) := by
  rw [← R.quotient_inertia_top_valuation_eq]
  exact R.quotient_local.lower_canonical n

theorem chapter05_character_kernel_inertia_base_residue_is_perfect
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ) :
    PerfectField
      (IsLocalRing.ResidueField
    R.quotient_inertia_transfer.vM.toValuation.valuationSubring) := by
  exact R.quotient_inertia_base_residue_perfect

theorem chapter05_character_kernel_inertia_base_residue_over_base_is_perfect
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ) :
    PerfectField
      (IsLocalRing.ResidueField
        R.quotient_inertia_transfer.vK.toValuation.valuationSubring) := by
  rw [← R.quotient_inertia_base_valuation_eq]
  exact R.quotient_residue_perfect

theorem chapter05_character_kernel_inertia_is_cyclic
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ) :
    IsCyclic (R.quotient_local.profile.lowerGroup 0) := by
  exact @Subgroup.isCyclic
    (Gal(chapter05CharacterKernelFixedField χ / K)) _ R.quotient_cyclic
    (R.quotient_local.profile.lowerGroup 0)

/-!
  A positive break is detected on a cyclic character quotient by taking a
  character nontrivial on the corresponding graded layer.  This package is
  deliberately a data interface: its source profile is retained, while the
  selected quotient is required to have the selected break as its maximal
  positive break.  The inertia bridge then supplies the last lower break used
  by the cyclic arithmetic interface.
-/
structure Chapter05AbelianBreakDetectionConstructionData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05RamificationFiltration (Gal(L / K))) (v : ℝ) where
  C : Type*
  [group_C : Group C]
  [finite_C : Finite C]
  reduced_character : Gal(L / K) →* C
  reduced_package :
    @Chapter05CharacterKernelHasseArfData K L C
      _ _ _ _ _ _ group_C finite_C reduced_character _ _ _ _ _ _
  source_profile_eq : reduced_package.local_data.profile = D
  selected_break :
    chapter05UpperBreak reduced_package.quotient_local.profile v
  maximal_positive_break :
    ∀ r : ℝ, 0 < r →
      chapter05UpperBreak reduced_package.quotient_local.profile r → r ≤ v
  reduced_inertia_cyclic :
    IsCyclic (reduced_package.quotient_local.profile.lowerGroup 0)
  inertia_bridge :
    ∃ b : ℕ,
      Chapter05FixedFieldInertiaBridge
        (reduced_package.quotient_local.profile.lowerGroup 0)
        reduced_package.quotient_local.profile
        reduced_package.quotient_inertia_transfer v b

structure Chapter05AbelianBreakDetectionData
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05RamificationFiltration (Gal(L / K))) (v : ℝ) where
  C : Type*
  [group_C : Group C]
  [finite_C : Finite C]
  reduced_character : Gal(L / K) →* C
  reduced_package :
    @Chapter05CharacterKernelHasseArfData K L C
      _ _ _ _ _ _ group_C finite_C reduced_character _ _ _ _ _ _
  source_profile_eq : reduced_package.local_data.profile = D
  source_break : chapter05UpperBreak D v
  selected_break :
    chapter05UpperBreak reduced_package.quotient_local.profile v
  maximal_positive_break :
    ∀ r : ℝ, 0 < r →
      chapter05UpperBreak reduced_package.quotient_local.profile r → r ≤ v
  reduced_inertia_cyclic :
    IsCyclic (reduced_package.quotient_local.profile.lowerGroup 0)
  inertia_bridge :
    ∃ b : ℕ,
      Chapter05FixedFieldInertiaBridge
        (reduced_package.quotient_local.profile.lowerGroup 0)
        reduced_package.quotient_local.profile
        reduced_package.quotient_inertia_transfer v b

universe u

theorem chapter05_abelian_break_detection_data_of_construction
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    {D : Chapter05RamificationFiltration (Gal(L / K))} {v : ℝ}
    (B : Chapter05AbelianBreakDetectionConstructionData.{_, _, u} D v)
    (hbreak : chapter05UpperBreak D v) :
    Nonempty (Chapter05AbelianBreakDetectionData.{_, _, u} D v) := by
  exact ⟨{ B with source_break := hbreak }⟩

theorem chapter05_abelian_break_detection_construction
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    {v : ℝ} (hv : 0 < v)
    (hbreak : chapter05UpperBreak D.profile v) :
    Nonempty (Chapter05AbelianBreakDetectionConstructionData D.profile v) := by
  sorry

theorem chapter05_abelian_break_detection
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    {v : ℝ} (hv : 0 < v)
    (hbreak : chapter05UpperBreak D.profile v) :
    Nonempty (Chapter05AbelianBreakDetectionData D.profile v) := by
  rcases chapter05_abelian_break_detection_construction D habelian hv hbreak with
    ⟨B⟩
  exact chapter05_abelian_break_detection_data_of_construction B hbreak

theorem chapter05_character_kernel_positive_break_reduction
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {v : ℝ} (hv : 0 < v)
    (hbreak : chapter05UpperBreak R.quotient_local.profile v) :
    Nonempty
      (Chapter05AbelianBreakDetectionData R.quotient_local.profile v) := by
  have habelian :
      ∀ σ τ : Gal(chapter05CharacterKernelFixedField χ / K),
        σ * τ = τ * σ := by
    intro σ τ
    exact (@IsCyclic.isMulCommutative
      (Gal(chapter05CharacterKernelFixedField χ / K)) _ R.quotient_cyclic).is_comm.comm
      σ τ
  exact @chapter05_abelian_break_detection _ _ _ _ _ _ _ _
    R.quotient_local habelian R.quotient_residue_perfect v hv hbreak

/-!
 The cyclic quotient `quotient_local` can still have an unramified stage.
 This bridge records the missing passage to the inertia fixed field: its
 transfer is a genuine fixed-field transfer, its upper breaks are transported
 at positive depth, and its lower profile is the totally ramified cyclic one
 to which the cyclic lemma applies.  It is only a maximal-positive-break
 bridge; an arbitrary positive break requires a separate graded-layer or
 character-kernel reduction.  The construction is kept separate from the
 character-kernel package so that a quotient theorem cannot silently be
 replaced by a false equality of lower indices.
-/
theorem chapter05_character_kernel_positive_break_inertia_bridge
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {v : ℝ} (hv : 0 < v)
    (hbreak : chapter05UpperBreak R.quotient_local.profile v)
    (hmax : ∀ r : ℝ, 0 < r →
      chapter05UpperBreak R.quotient_local.profile r → r ≤ v) :
    ∃ b : ℕ,
      Chapter05FixedFieldInertiaBridge
        (R.quotient_local.profile.lowerGroup 0)
        R.quotient_local.profile R.quotient_inertia_transfer v b := by
  exact chapter05_fixed_field_inertia_bridge_of_canonical_profile
    (R.quotient_local.profile.lowerGroup 0)
    R.quotient_local.profile R.quotient_inertia_transfer
    (fun n => chapter05_character_kernel_quotient_profile_canonical_at_inertia_top χ R n)
    rfl (chapter05_character_kernel_inertia_is_cyclic χ R)
    (chapter05_character_kernel_inertia_base_residue_over_base_is_perfect χ R)
    hv hbreak hmax

private theorem chapter05_nat_card_map_group_equiv
    {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (K : Subgroup G) (e : G ≃* G') :
    Nat.card (K.map e.toMonoidHom) = Nat.card K := by
  classical
  let f : K → K.map e.toMonoidHom := fun x =>
    ⟨e x, ⟨x, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val hxy
    · intro y
      rcases y.property with ⟨x, hx, hxy⟩
      refine ⟨⟨x, hx⟩, ?_⟩
      apply Subtype.ext
      exact hxy
  exact Nat.card_congr (Equiv.ofBijective f hf).symm

private theorem chapter05_upper_group_transport_of_profile
    {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (D : Chapter05RamificationFiltration G)
    (E : Chapter05RamificationFiltration G')
    (e : G ≃* G')
    (hprofile : ∀ u : ℝ,
      E.lowerGroup u = (D.lowerGroup u).map e.toMonoidHom)
    (hD : Function.Bijective (chapter05HerbrandFunction D))
    (hE : Function.Bijective (chapter05HerbrandFunction E))
    {v : ℝ} (hv : (-1 : ℝ) ≤ v) :
    chapter05UpperRamificationGroup E v =
      (chapter05UpperRamificationGroup D v).map e.toMonoidHom := by
  have hcard (u : ℝ) :
      Nat.card (E.lowerGroup u) = Nat.card (D.lowerGroup u) := by
    rw [hprofile u]
    exact chapter05_nat_card_map_group_equiv _ e
  have hslope (u : ℝ) :
      chapter05HerbrandSlope E u = chapter05HerbrandSlope D u := by
    by_cases hu : u ≤ 0
    · simp [chapter05HerbrandSlope, hu]
    · rw [chapter05HerbrandSlope, if_neg hu,
        chapter05HerbrandSlope, if_neg hu, hcard u, hcard 0]
  have hfunction (u : ℝ) :
      chapter05HerbrandFunction E u = chapter05HerbrandFunction D u := by
    by_cases hu : u ≤ 0
    · simp [chapter05HerbrandFunction, hu]
    · rw [chapter05HerbrandFunction, if_neg hu,
        chapter05HerbrandFunction, if_neg hu]
      rw [show (fun t : ℝ => chapter05HerbrandSlope E t) =
          (fun t : ℝ => chapter05HerbrandSlope D t) by
        funext t
        exact hslope t]
  have hinverse (u : ℝ) :
      chapter05HerbrandInverse E u = chapter05HerbrandInverse D u := by
    apply hD.1
    calc
      chapter05HerbrandFunction D
          (chapter05HerbrandInverse E u) =
          chapter05HerbrandFunction E
            (chapter05HerbrandInverse E u) :=
        (hfunction _).symm
      _ = u := chapter05_herbrand_inverse_spec E hE u
      _ = chapter05HerbrandFunction D
          (chapter05HerbrandInverse D u) :=
        (chapter05_herbrand_inverse_spec D hD u).symm
  rw [chapter05_upper_group_eq_lower_at_inverse E hv,
    chapter05_upper_group_eq_lower_at_inverse D hv,
    hinverse]
  exact hprofile _

/- The source's cyclic lemma is exposed separately so the abelian theorem can
   reduce to cyclic quotients without hiding the integrality input in its
   conclusion. -/
theorem chapter05_cyclic_local_arithmetic_interface_of_last_break
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (hcyclic : IsCyclic (Gal(L / K)))
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    {b : ℕ}
    (hb_pos : 0 < b)
    (hlast : ∀ n : ℕ, b < n →
      D.profile.lowerGroup (n : ℝ) = ⊥)
    (hbreak : b = 0 ∨
      D.profile.lowerGroup (b : ℝ) ≠
        D.profile.lowerGroup (b + 1 : ℕ))
    (htotally_ramified : D.profile.lowerGroup 0 = ⊤) :
    ∃ σ : Gal(L / K),
      Nonempty (Chapter05CyclicLocalArithmeticInterface D σ b) := by
  sorry

theorem chapter05_cyclic_hasse_arf_lemma
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (hcyclic : IsCyclic (Gal(L / K)))
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    {b : ℕ}
    (hlast : ∀ n : ℕ, b < n →
      D.profile.lowerGroup (n : ℝ) = ⊥)
    (hbreak : b = 0 ∨
      D.profile.lowerGroup (b : ℝ) ≠
        D.profile.lowerGroup (b + 1 : ℕ))
    (htotally_ramified : D.profile.lowerGroup 0 = ⊤) :
    ∃ z : ℤ, (z : ℚ) = chapter05CyclicHasseArfSum D.profile b := by
  by_cases hb : b = 0
  · refine ⟨0, ?_⟩
    simp [chapter05CyclicHasseArfSum, hb]
  · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
    rcases chapter05_cyclic_local_arithmetic_interface_of_last_break
        D hcyclic hb_pos hlast hbreak htotally_ramified with ⟨σ, ⟨A⟩⟩
    exact chapter05_cyclic_local_arithmetic_integrality D A

/- The inertia stage is naturally presented by a fixed-field transfer rather
   than by the original quotient local data.  This version keeps its base
   valuation and canonical subextension profile visible. -/
theorem chapter05_cyclic_hasse_arf_lemma_of_fixed_field_transfer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    {H : Subgroup (Gal(L / K))} [H.Normal]
    [FiniteDimensional K
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H)]
    [IsGalois K
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H)]
    [Finite
      (Gal(
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H / K))]
    [FiniteDimensional
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H) L]
    [IsGalois
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H) L]
    [Finite
      (Gal(
        L /
          LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H))]
    (D : Chapter05RamificationFiltration (Gal(L / K)))
    (T : Chapter05FixedFieldSubextensionTransfer H D)
    (hcyclic : IsCyclic (Gal(
      L /
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H)))
    (hperfect : PerfectField
      (IsLocalRing.ResidueField T.vM.toValuation.valuationSubring))
    {b : ℕ}
    (hlast : ∀ n : ℕ, b < n →
      T.subextension_profile.lowerGroup (n : ℝ) = ⊥)
    (hbreak : b = 0 ∨
      T.subextension_profile.lowerGroup (b : ℝ) ≠
        T.subextension_profile.lowerGroup (b + 1 : ℕ))
    (htotally_ramified : T.subextension_profile.lowerGroup 0 = ⊤) :
    ∃ z : ℤ, (z : ℚ) =
      chapter05CyclicHasseArfSum T.subextension_profile b := by
  let M :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05FixedField H
  let D' : Chapter05LocalGaloisUpperData M L :=
    { vK := T.vM
      vL := T.vL
      vK_rank_one_discrete := T.vM_rank_one_discrete
      vL_rank_one_discrete := T.vL_rank_one_discrete
      restriction := T.vM_restriction_to_L
      base_complete := T.fixed_field_complete
      extension_complete := T.extension_complete
      unique_valuation_extension := T.unique_normalized_ML
      decomposition_top := T.decomposition_top_ML
      profile := T.subextension_profile
      lower_canonical := T.subextension_lower_canonical }
  exact @chapter05_cyclic_hasse_arf_lemma _ _ _ _ _ _ _ _
    D' hcyclic hperfect b hlast hbreak htotally_ramified

/-- The fixed-field transfer supplies the local quotient input for the cyclic
 Hasse--Arf lemma on a character-kernel quotient. -/
theorem chapter05_character_kernel_cyclic_hasse_arf
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {b : ℕ}
    (hlast : ∀ n : ℕ, b < n →
      R.quotient_local.profile.lowerGroup (n : ℝ) = ⊥)
    (hbreak : b = 0 ∨
      R.quotient_local.profile.lowerGroup (b : ℝ) ≠
        R.quotient_local.profile.lowerGroup (b + 1 : ℕ))
    (htotally_ramified : R.quotient_local.profile.lowerGroup 0 = ⊤) :
    ∃ z : ℤ,
      (z : ℚ) = chapter05CyclicHasseArfSum R.quotient_local.profile b := by
  exact @chapter05_cyclic_hasse_arf_lemma _ _ _ _ _ _ _ _
    R.quotient_local R.quotient_cyclic R.quotient_residue_perfect
    b hlast hbreak htotally_ramified

theorem chapter05_character_kernel_inertia_cyclic_hasse_arf
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {v : ℝ} {bn : ℕ}
    (B : Chapter05FixedFieldInertiaBridge
      (R.quotient_local.profile.lowerGroup 0)
      R.quotient_local.profile R.quotient_inertia_transfer v bn) :
    ∃ z : ℤ,
      (z : ℚ) =
        chapter05CyclicHasseArfSum
          R.quotient_inertia_transfer.subextension_profile bn := by
  exact chapter05_cyclic_hasse_arf_lemma_of_fixed_field_transfer
    R.quotient_local.profile R.quotient_inertia_transfer
    B.cyclic_subextension R.quotient_inertia_base_residue_perfect
    B.subextension_last_lower
    B.subextension_lower_break B.subextension_totally_ramified

private theorem chapter05_herbrand_nat_value_eq_cyclic_hasse_arf_sum
    {G : Type*} [Group G] [Finite G]
    (T : Chapter05RamificationFiltration G) (b : ℕ) :
    (chapter05CyclicHasseArfSum T b : ℝ) =
      chapter05HerbrandFunction T (b : ℝ) := by
  rw [chapter05_herbrand_function_interval_formula T b le_rfl
    (by exact_mod_cast Nat.le_succ b)]
  simp [chapter05CyclicHasseArfSum]

private theorem chapter05_integer_of_cyclic_inertia_value
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {v : ℝ} {bn : ℕ}
    (B : Chapter05FixedFieldInertiaBridge
      (R.quotient_local.profile.lowerGroup 0)
      R.quotient_local.profile R.quotient_inertia_transfer v bn)
    {z : ℤ}
    (hz : (z : ℚ) =
      chapter05CyclicHasseArfSum
        R.quotient_inertia_transfer.subextension_profile bn) :
    chapter05UpperBreakIsInteger v := by
  refine ⟨z, ?_⟩
  have hz' :
      (z : ℝ) =
        (chapter05CyclicHasseArfSum
          R.quotient_inertia_transfer.subextension_profile bn : ℝ) := by
    exact_mod_cast hz
  calc
    (z : ℝ) =
        (chapter05CyclicHasseArfSum
          R.quotient_inertia_transfer.subextension_profile bn : ℝ) := hz'
    _ = chapter05HerbrandFunction
          R.quotient_inertia_transfer.subextension_profile (bn : ℝ) :=
      chapter05_herbrand_nat_value_eq_cyclic_hasse_arf_sum
        R.quotient_inertia_transfer.subextension_profile bn
    _ = v := B.upper_value

theorem chapter05_character_kernel_upper_break_integer
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {v : ℝ}
    (hv : chapter05UpperBreak R.quotient_local.profile v) :
    chapter05UpperBreakIsInteger v := by
  by_cases hvpos : 0 < v
  · rcases chapter05_character_kernel_positive_break_reduction.{_, _, _, 0}
        χ R hvpos hv with ⟨B⟩
    rcases B.inertia_bridge with ⟨bn, Bn⟩
    rcases @chapter05_character_kernel_inertia_cyclic_hasse_arf
        _ _ B.C
        inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
        B.group_C B.finite_C
        B.reduced_character B.reduced_package v bn Bn with ⟨z, hz⟩
    exact @chapter05_integer_of_cyclic_inertia_value
      _ _ B.C
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      B.group_C B.finite_C
      B.reduced_character B.reduced_package v bn Bn z hz
  · classical
    rcases (chapter05_upper_break_iff_herbrand_image_of_lower_break
        R.quotient_local.profile
        (chapter05_herbrand_bijective_of_filtration
          R.quotient_local.profile)).mp hv with
      hneg | ⟨m, _, hFm⟩
    · refine ⟨(-1 : ℤ), ?_⟩
      norm_num
      exact hneg.1.symm
    · have hmono : StrictMonoOn
          (chapter05HerbrandFunction R.quotient_local.profile)
          (Set.Ici (-1 : ℝ)) :=
        (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
          R.quotient_local.profile).2.1
      have hm_mem : (m : ℝ) ∈ Set.Ici (-1 : ℝ) := by
        change (-1 : ℝ) ≤ (m : ℝ)
        have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
        linarith
      have hzero_mem : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
      have hmono' := hmono.monotoneOn hzero_mem hm_mem
        (by exact_mod_cast Nat.zero_le m)
      rw [chapter05_herbrand_function_zero
        R.quotient_local.profile] at hmono'
      have hvzero : v = 0 := by linarith [hmono', hFm]
      refine ⟨(0 : ℤ), ?_⟩
      norm_num [hvzero]

/-!
 The actual order-`p²` specialization.  The surviving subgroup in the
 two-break tower and the character kernel need not be the same line in the
 elementary abelian quotient; the latter is required only to miss the former,
 so its cyclic quotient still detects the second upper break.
-/
theorem chapter05_character_kernel_detects_two_break_second_upper
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))] [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {H : Subgroup (Gal(L / K))} [H.Normal]
    (T : Chapter05TwoBreakTowerData (Gal(L / K)) H)
    (hprofile : R.local_data.profile = T.twoBreak.profile)
    (hsubgroup_not_le_kernel : ¬H ≤ MonoidHom.ker χ) :
    chapter05UpperBreak R.quotient_local.profile
      (chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b) := by
  classical
  let q := chapter05QuotientMap (MonoidHom.ker χ)
  let c : ℝ :=
    chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b
  have hcomp :
      (T.twoBreak.a : ℝ) < c ∧ c < (T.twoBreak.b : ℝ) := by
    simpa [c] using chapter05_two_break_upper_label_is_strictly_compressed
      T.twoBreak.p T.twoBreak.a T.twoBreak.b T.twoBreak.p_prime
        T.twoBreak.a_lt_b
  have hformula (x : ℝ) :
      chapter05HerbrandFunction T.twoBreak.profile x =
        chapter05TwoBreakHerbrand T.twoBreak.p T.twoBreak.a T.twoBreak.b x := by
    exact chapter05_two_break_herbrand_formula H T.twoBreak x
  have hF_le_a {x : ℝ} (hx : x ≤ (T.twoBreak.a : ℝ)) :
      chapter05HerbrandFunction T.twoBreak.profile x = x := by
    rw [hformula]
    by_cases hx0 : x ≤ 0
    · simp [chapter05TwoBreakHerbrand, hx0]
    · simp [chapter05TwoBreakHerbrand, hx0, hx]
  have hF_mid {x : ℝ} (hxa : (T.twoBreak.a : ℝ) < x)
      (hxb : x ≤ (T.twoBreak.b : ℝ)) :
      chapter05HerbrandFunction T.twoBreak.profile x =
        (T.twoBreak.a : ℝ) +
          (x - (T.twoBreak.a : ℝ)) / (T.twoBreak.p : ℝ) := by
    rw [hformula]
    have hx0 : ¬x ≤ 0 := by
      have ha_pos : (0 : ℝ) < (T.twoBreak.a : ℝ) := by
        exact_mod_cast T.twoBreak.a_pos
      linarith
    simp [chapter05TwoBreakHerbrand, hx0, not_le.mpr hxa, hxb]
  have hF_gt {x : ℝ} (hxb : (T.twoBreak.b : ℝ) < x) :
      chapter05HerbrandFunction T.twoBreak.profile x =
        (T.twoBreak.a : ℝ) +
          ((T.twoBreak.b - T.twoBreak.a : ℕ) : ℝ) /
            (T.twoBreak.p : ℝ) +
          (x - (T.twoBreak.b : ℝ)) / (T.twoBreak.p : ℝ) ^ 2 := by
    rw [hformula]
    have hab : (T.twoBreak.a : ℝ) ≤ (T.twoBreak.b : ℝ) := by
      exact_mod_cast T.twoBreak.a_lt_b.le
    have hxa : ¬x ≤ (T.twoBreak.a : ℝ) := by linarith
    have hb_pos : (0 : ℝ) < (T.twoBreak.b : ℝ) := by
      exact lt_of_lt_of_le (by exact_mod_cast T.twoBreak.a_pos) hab
    have hx0 : ¬x ≤ 0 := by linarith
    simp [chapter05TwoBreakHerbrand, hx0, hxa, hxb]
  have hFb :
      chapter05HerbrandFunction T.twoBreak.profile (T.twoBreak.b : ℝ) = c := by
    have h := hF_mid (x := (T.twoBreak.b : ℝ))
      (by exact_mod_cast T.twoBreak.a_lt_b) le_rfl
    have hcast : ((T.twoBreak.b - T.twoBreak.a : ℕ) : ℝ) =
        (T.twoBreak.b : ℝ) - (T.twoBreak.a : ℝ) := by
      exact_mod_cast Nat.cast_sub T.twoBreak.a_lt_b.le
    simpa [c, chapter05TwoBreakSecondUpper, hcast] using h
  have hF_gt_c {x : ℝ} (hxb : (T.twoBreak.b : ℝ) < x) :
      c < chapter05HerbrandFunction T.twoBreak.profile x := by
    rw [hF_gt hxb]
    simp only [c, chapter05TwoBreakSecondUpper]
    have hp0 : (0 : ℝ) < (T.twoBreak.p : ℝ) := by
      exact_mod_cast T.twoBreak.p_prime.pos
    have hpos : 0 < (x - (T.twoBreak.b : ℝ)) /
        (T.twoBreak.p : ℝ) ^ 2 := by
      exact div_pos (sub_pos.mpr hxb) (sq_pos_of_pos hp0)
    linarith
  have hmono : StrictMonoOn
      (chapter05HerbrandFunction T.twoBreak.profile)
      (Set.Ici (-1 : ℝ)) :=
    (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
      T.twoBreak.profile).2.1
  have htop_bij :
      Function.Bijective (chapter05HerbrandFunction T.twoBreak.profile) :=
    chapter05_herbrand_bijective_of_filtration T.twoBreak.profile
  have hinv_domain {x : ℝ} (hx : (-1 : ℝ) ≤ x) :
      (-1 : ℝ) ≤ chapter05HerbrandInverse T.twoBreak.profile x := by
    by_contra hnot
    have hlt : chapter05HerbrandInverse T.twoBreak.profile x < (-1 : ℝ) :=
      lt_of_not_ge hnot
    have hidentity :=
      chapter05_herbrand_function_of_nonpositive T.twoBreak.profile (by linarith)
    have hspec := chapter05_herbrand_inverse_spec
      T.twoBreak.profile htop_bij x
    have hxeq : chapter05HerbrandInverse T.twoBreak.profile x = x :=
      hidentity.symm.trans hspec
    linarith
  have htop_upper_c :
      chapter05UpperRamificationGroup T.twoBreak.profile c = H := by
    have hc_dom : (-1 : ℝ) ≤ c := by linarith [hcomp.1]
    have hspec := chapter05_herbrand_inverse_spec
      T.twoBreak.profile htop_bij c
    have hψ_dom := hinv_domain hc_dom
    have hψ_gt_a : (T.twoBreak.a : ℝ) <
        chapter05HerbrandInverse T.twoBreak.profile c := by
      by_contra hnot
      have hψ_le := le_of_not_gt hnot
      have hfx := hF_le_a hψ_le
      linarith [hcomp.1]
    have hψ_le_b : chapter05HerbrandInverse T.twoBreak.profile c ≤
        (T.twoBreak.b : ℝ) := by
      by_contra hnot
      have hψ_gt := lt_of_not_ge hnot
      have hgtc := hF_gt_c hψ_gt
      linarith
    rw [chapter05UpperRamificationGroup, if_pos hc_dom,
      T.twoBreak.lower_second_layer _ hψ_gt_a hψ_le_b]
  have htop_upper_gt {w : ℝ} (hw : c < w) :
      chapter05UpperRamificationGroup T.twoBreak.profile w = ⊥ := by
    have hw_dom : (-1 : ℝ) ≤ w := by linarith [hcomp.1]
    have hspec := chapter05_herbrand_inverse_spec
      T.twoBreak.profile htop_bij w
    have hψ_dom := hinv_domain hw_dom
    have hF_le_b {x : ℝ} (hx : (-1 : ℝ) ≤ x)
        (hxb : x ≤ (T.twoBreak.b : ℝ)) :
        chapter05HerbrandFunction T.twoBreak.profile x ≤ c := by
      have hb_dom : (-1 : ℝ) ≤ (T.twoBreak.b : ℝ) := by
        have hb_nonneg : (0 : ℝ) ≤ (T.twoBreak.b : ℝ) := by
          exact_mod_cast T.twoBreak.a_pos.le.trans T.twoBreak.a_lt_b.le
        linarith
      have hle := hmono.monotoneOn hx hb_dom hxb
      rw [hFb] at hle
      exact hle
    have hψ_gt_b : (T.twoBreak.b : ℝ) <
        chapter05HerbrandInverse T.twoBreak.profile w := by
      by_contra hnot
      have hψ_le := le_of_not_gt hnot
      have hle := hF_le_b hψ_dom hψ_le
      linarith
    rw [chapter05UpperRamificationGroup, if_pos hw_dom,
      T.twoBreak.lower_after_second_layer _ hψ_gt_b]
  let : Fintype (Gal(L / K)) := AlgEquiv.fintype K L
  let Q := R.quotient_setup
  have hQ_profile : Q.upstairs = R.local_data.profile := by
    exact R.quotient_setup_upstairs_eq
  have hup_R :
      Function.Bijective
        (chapter05HerbrandFunction Q.upstairs) := by
    exact chapter05_herbrand_bijective_of_filtration Q.upstairs
  have hdown_R :
      Function.Bijective
        (chapter05HerbrandFunction Q.downstairs) := by
    exact chapter05_herbrand_bijective_of_filtration Q.downstairs
  have hquotient_upper {w : ℝ} (hw : (-1 : ℝ) ≤ w) :
    chapter05UpperRamificationGroup Q.downstairs w =
        (chapter05UpperRamificationGroup R.local_data.profile w).map q := by
    simpa [chapter05UpperQuotientImage, q, hQ_profile] using
      (chapter05_herbrand_quotient_theorem (MonoidHom.ker χ)
        Q hw)
  have hdown_upper_c :
      chapter05UpperRamificationGroup Q.downstairs c =
        H.map q := by
    have htop_upper_c_R :
        chapter05UpperRamificationGroup R.local_data.profile c = H := by
      rw [hprofile]
      exact htop_upper_c
    rw [hquotient_upper (by linarith [hcomp.1]), htop_upper_c_R]
  have hdown_upper_gt {w : ℝ} (hw : c < w) :
      chapter05UpperRamificationGroup Q.downstairs w = ⊥ := by
    have htop_upper_gt_R :
        chapter05UpperRamificationGroup R.local_data.profile w = ⊥ := by
      rw [hprofile]
      exact htop_upper_gt hw
    rw [hquotient_upper (by linarith [hcomp.1]), htop_upper_gt_R]
    simp
  have hdown_right :
      chapter05UpperRightLimit Q.downstairs c = ⊥ := by
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K' hK'
      rcases hK' with ⟨w, hw, rfl⟩
      exact le_of_eq (hdown_upper_gt hw)
    · exact bot_le
  have hnotker : ∃ h : Gal(L / K), h ∈ H ∧ h ∉ MonoidHom.ker χ := by
    by_contra hnone
    apply hsubgroup_not_le_kernel
    intro h hh
    by_contra hhk
    apply hnone
    exact ⟨h, hh, hhk⟩
  have hqker_eq : MonoidHom.ker q = MonoidHom.ker χ := by
    dsimp [q]
    exact Chapter05QuotientRamificationSetup.quotient_map_kernel _
  have hmapH_ne_bot : H.map q ≠ (⊥ : Subgroup _ ) := by
    intro hbot
    rcases hnotker with ⟨h, hh, hhk⟩
    have hmem : q h ∈ H.map q := ⟨h, hh, rfl⟩
    rw [hbot] at hmem
    have hqone : q h = 1 := by simpa using hmem
    apply hhk
    have hkerq : h ∈ MonoidHom.ker q := MonoidHom.mem_ker.mpr hqone
    rw [hqker_eq] at hkerq
    exact hkerq
  have hdown_break : chapter05UpperBreak
      R.quotient_setup.downstairs c := by
    rw [chapter05UpperBreak]
    refine ⟨by linarith [hcomp.1], ?_⟩
    have hc_ne : c ≠ (-1 : ℝ) := by linarith [hcomp.1]
    rw [if_neg hc_ne, hdown_upper_c, hdown_right]
    exact hmapH_ne_bot
  have hquotient_profile_bij :
      Function.Bijective
        (chapter05HerbrandFunction R.quotient_local.profile) := by
    exact chapter05_herbrand_bijective_of_filtration R.quotient_local.profile
  have htransport_c := chapter05_upper_group_transport_of_profile
    R.quotient_setup.downstairs R.quotient_local.profile
      R.quotient_galois_equiv R.quotient_profile_transport hdown_R
        hquotient_profile_bij (by linarith [hcomp.1] : (-1 : ℝ) ≤ c)
  have htransport_gt {w : ℝ} (hw : c < w) :
      chapter05UpperRamificationGroup R.quotient_local.profile w = ⊥ := by
    have hw_dom : (-1 : ℝ) ≤ w := by linarith [hcomp.1]
    rw [chapter05_upper_group_transport_of_profile
      R.quotient_setup.downstairs R.quotient_local.profile
        R.quotient_galois_equiv R.quotient_profile_transport hdown_R
          hquotient_profile_bij hw_dom, hdown_upper_gt hw]
    simp
  have hupper_c_ne_bot :
      chapter05UpperRamificationGroup R.quotient_local.profile c ≠ ⊥ := by
    intro hzero
    have hmapzero :
        (chapter05UpperRamificationGroup Q.downstairs c).map
            R.quotient_galois_equiv.toMonoidHom = ⊥ := by
      rw [← htransport_c, hzero]
    rw [hdown_upper_c] at hmapzero
    rcases hnotker with ⟨h, hh, hhk⟩
    have hmem :
        R.quotient_galois_equiv (q h) ∈
          (H.map q).map R.quotient_galois_equiv.toMonoidHom := by
      exact ⟨q h, ⟨h, hh, rfl⟩, rfl⟩
    rw [hmapzero] at hmem
    have heq : R.quotient_galois_equiv (q h) = 1 := by simpa using hmem
    apply hhk
    have hqone : q h = 1 := by
      apply R.quotient_galois_equiv.injective
      simpa using heq
    have hkerq : h ∈ MonoidHom.ker q := MonoidHom.mem_ker.mpr hqone
    rw [hqker_eq] at hkerq
    exact hkerq
  have hright :
      chapter05UpperRightLimit R.quotient_local.profile c = ⊥ := by
    rw [chapter05UpperRightLimit, chapter05RightLimit]
    apply le_antisymm
    · apply sSup_le
      intro K' hK'
      rcases hK' with ⟨w, hw, rfl⟩
      exact le_of_eq (htransport_gt hw)
    · exact bot_le
  rw [chapter05UpperBreak]
  refine ⟨by linarith [hcomp.1], ?_⟩
  have hc_ne : c ≠ (-1 : ℝ) := by linarith [hcomp.1]
  rw [if_neg hc_ne, hright]
  exact hupper_c_ne_bot

theorem chapter05_perfect_residue_p_squared_two_break_second_upper_integral
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))] [Group C] [Finite C]
    (χ : Gal(L / K) →* C)
    (R : Chapter05CharacterKernelHasseArfData χ)
    {H : Subgroup (Gal(L / K))} [H.Normal]
    (T : Chapter05TwoBreakTowerData (Gal(L / K)) H)
    (hprofile : R.local_data.profile = T.twoBreak.profile)
    (hsubgroup_not_le_kernel : ¬H ≤ MonoidHom.ker χ) :
    chapter05UpperBreakIsInteger
        (chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b) ∧
      T.twoBreak.p ∣ T.twoBreak.b - T.twoBreak.a := by
  have hbreak := chapter05_character_kernel_detects_two_break_second_upper
    χ R T hprofile hsubgroup_not_le_kernel
  have hintegral := chapter05_character_kernel_upper_break_integer χ R hbreak
  refine ⟨hintegral, ?_⟩
  exact chapter05_two_break_integral_second_label_implies_dvd
    T.twoBreak.p T.twoBreak.a T.twoBreak.b T.twoBreak.p_prime.pos
    T.twoBreak.a_lt_b hintegral

/-- The Hasse--Arf theorem in the local field interface of this chapter,
conditional on the explicit local Dold congruence input. -/
theorem chapter05_hasse_arf
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    :
    chapter05AllUpperBreaksIntegral D.profile := by
  intro v hv
  by_cases hvpos : 0 < v
  · have hB :
        Nonempty (Chapter05AbelianBreakDetectionData.{_, _, 0} D.profile v) := by
      exact chapter05_abelian_break_detection D habelian hvpos hv
    rcases hB with ⟨B⟩
    exact @chapter05_character_kernel_upper_break_integer
      _ _ B.C
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      B.group_C B.finite_C
      B.reduced_character B.reduced_package v B.selected_break
  · classical
    rcases (chapter05_upper_break_iff_herbrand_image_of_lower_break
        D.profile
        (chapter05_herbrand_bijective_of_filtration D.profile)).mp hv with
      hneg | ⟨m, _, hFm⟩
    · refine ⟨(-1 : ℤ), ?_⟩
      norm_num
      exact hneg.1.symm
    · have hmono : StrictMonoOn
          (chapter05HerbrandFunction D.profile)
          (Set.Ici (-1 : ℝ)) :=
        (chapter05_herbrand_function_is_continuous_increasing_piecewise_linear
          D.profile).2.1
      have hm_mem : (m : ℝ) ∈ Set.Ici (-1 : ℝ) := by
        change (-1 : ℝ) ≤ (m : ℝ)
        have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := by positivity
        linarith
      have hzero_mem : (0 : ℝ) ∈ Set.Ici (-1 : ℝ) := by norm_num
      have hmono' := hmono.monotoneOn hzero_mem hm_mem
        (by exact_mod_cast Nat.zero_le m)
      rw [chapter05_herbrand_function_zero D.profile] at hmono'
      have hvzero : v = 0 := by linarith [hmono', hFm]
      refine ⟨(0 : ℤ), ?_⟩
      norm_num [hvzero]

theorem chapter05_hasse_arf_upper_break_integer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    (habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    {v : ℝ} (hv : chapter05UpperBreak D.profile v) :
    chapter05UpperBreakIsInteger v := by
  exact chapter05_hasse_arf D habelian v hv

/- The two-break discussion in the source specializes Hasse--Arf directly:
   for an actual order-`p^2` local Galois group, the second upper label is an
   upper break of the local profile, hence it is integral and the arithmetic
   characterization from Section 5.5 gives `p ∣ b - a`. -/
theorem chapter05_perfect_residue_p_squared_two_break_second_upper_integral_direct
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    [Fintype (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    {H : Subgroup (Gal(L / K))} [H.Normal]
    (T : Chapter05TwoBreakTowerData (Gal(L / K)) H)
    (hprofile : D.profile = T.twoBreak.profile) :
    chapter05UpperBreakIsInteger
        (chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b) ∧
      T.twoBreak.p ∣ T.twoBreak.b - T.twoBreak.a := by
  have habelian : ∀ σ τ : Gal(L / K), σ * τ = τ * σ := by
    exact (chapter05_two_break_group_is_commutative H T.twoBreak).is_comm.comm
  have hbreaks := chapter05_two_break_upper_breaks H T.twoBreak
    (chapter05_herbrand_bijective_of_filtration T.twoBreak.profile)
  have hsecond : chapter05UpperBreak D.profile
      (chapter05TwoBreakSecondUpper T.twoBreak.p T.twoBreak.a T.twoBreak.b) := by
    rw [hprofile]
    exact hbreaks.2.1
  have hintegral := (chapter05_hasse_arf D habelian) _ hsecond
  refine ⟨hintegral, ?_⟩
  exact chapter05_two_break_integral_second_label_implies_dvd
    T.twoBreak.p T.twoBreak.a T.twoBreak.b T.twoBreak.p_prime.pos
    T.twoBreak.a_lt_b hintegral

/-- The boundary predicate for a fractional upper break in the nonabelian case. -/
def chapter05HasFractionalUpperBreak
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G) : Prop :=
  ∃ v : ℝ, chapter05UpperBreak D v ∧ ¬chapter05UpperBreakIsInteger v

/-
 The theorem above has exactly the classical hypotheses: no finiteness of the
 residue field is present, while perfection of the residue field and
 commutativity of the finite Galois group are explicit.  The predicate
 `chapter05HasFractionalUpperBreak` is intentionally not ruled out for a
 nonabelian profile; this is the limit of the integrality statement.
-/
theorem chapter05_hasse_arf_does_not_assert_nonabelian_integrality
    {G : Type*} [Group G] [Finite G]
    (D : Chapter05RamificationFiltration G)
    (hfrac : chapter05HasFractionalUpperBreak D) :
    ¬chapter05AllUpperBreaksIntegral D := by
  intro hAll
  rcases hfrac with ⟨v, hv, hnot⟩
  exact hnot (hAll v hv)

/- In the actual local-Galois interface, Hasse--Arf gives the sharper
   contrapositive: a fractional upper break rules out an abelian Galois group
   under the same perfect-residue hypotheses. -/
theorem chapter05_fractional_upper_break_forces_nonabelian
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Finite (Gal(L / K))]
    (D : Chapter05LocalGaloisUpperData K L)
    [PerfectField (IsLocalRing.ResidueField D.vK.toValuation.valuationSubring)]
    (hfrac : chapter05HasFractionalUpperBreak D.profile) :
    ¬ (∀ σ τ : Gal(L / K), σ * τ = τ * σ) := by
  intro habelian
  rcases hfrac with ⟨v, hv, hnot⟩
  exact hnot ((chapter05_hasse_arf D habelian) v hv)

end
end LastLib.Book03RamificationTheory.Chapter05
