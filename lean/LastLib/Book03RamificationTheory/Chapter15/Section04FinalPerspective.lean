import LastLib.Book03RamificationTheory.Chapter15.Section03ConsequencesForTwoDimensionalArithmetic
import LastLib.Book03RamificationTheory.Chapter09.Section05UpperNumberedFormAndADiscriminantBound

namespace LastLib.Book03RamificationTheory.Chapter15

noncomputable section

open scoped BigOperators

/-! ## 15.5--15.7. Global discriminants, Fontaine estimates, and checks -/

/- The global ledger reuses the earlier branch-count normalization.  Its
   explicit `branches`, `e`, `f`, and `d` fields are what make the local ratio
   visible before any root-discriminant estimate is applied. -/
abbrev Chapter15GlobalDiscriminantLedger :=
  LastLib.Book03RamificationTheory.Chapter09.Chapter09GlobalDiscriminantLedger

theorem chapter15_global_discriminant_ratio_is_local_ratio
    (C : Chapter15GlobalDiscriminantLedger) :
    (C.discriminantExponent : ℚ) / (C.relativeDegree : ℚ) =
      (C.d : ℚ) / (C.e : ℚ) := by
  sorry

def chapter15AuxiliaryRootDiscriminantFactor
    (primeNorm : ℝ) (lastUpperBreak : ℝ) (globalDegree : ℕ) : ℝ :=
  Real.rpow primeNorm ((1 + lastUpperBreak) / (globalDegree : ℝ))

structure Chapter15FontaineCutoffData where
  residuePrime : ℕ
  residuePrime_prime : Nat.Prime residuePrime
  exponent : ℕ
  baseRamificationIndex : ℕ
  cutoff : ℝ
  cutoff_bound :
    cutoff ≤ (baseRamificationIndex : ℝ) *
        ((exponent : ℝ) + ((residuePrime : ℝ) - 1)⁻¹) - 1

theorem chapter15_fontaine_local_different_bound
    (D : Chapter15FontaineCutoffData) (e d : ℕ) (he : 0 < e)
    (hidentity : (d : ℝ) / (e : ℝ) =
      1 - (e : ℝ)⁻¹ + D.cutoff) :
    (d : ℝ) ≤ (e : ℝ) * (D.baseRamificationIndex : ℝ) *
        ((D.exponent : ℝ) + ((D.residuePrime : ℝ) - 1)⁻¹) - 1 ∧
      (d : ℝ) / (e : ℝ) <
        (D.baseRamificationIndex : ℝ) *
          ((D.exponent : ℝ) + ((D.residuePrime : ℝ) - 1)⁻¹) := by
  sorry

structure Chapter15GlobalRootDiscriminantLedger
    (ι : Type*) [Fintype ι] where
  baseRootDiscriminant : ℝ
  extensionRootDiscriminant : ℝ
  residuePrime : ℕ
  residuePrime_prime : Nat.Prime residuePrime
  exponent : ℕ
  localWeight : ι → ℝ
  localExponent : ι → ℝ
  globalRootExponent : ℝ
  baseRootDiscriminant_pos : 0 < baseRootDiscriminant
  weight_nonneg : ∀ v, 0 ≤ localWeight v
  weight_sum_pos : 0 < ∑ v, localWeight v
  globalRootExponent_eq :
    globalRootExponent =
      (∑ v, localWeight v * localExponent v) /
        ∑ v, localWeight v
  root_discriminant_formula :
    extensionRootDiscriminant =
      baseRootDiscriminant *
        Real.rpow (residuePrime : ℝ) globalRootExponent

theorem chapter15_global_root_discriminant_bound
    {ι : Type*} [Fintype ι]
    (D : Chapter15GlobalRootDiscriminantLedger ι)
    (hlocal : ∀ v, D.localExponent v <
      (D.exponent : ℝ) + ((D.residuePrime : ℝ) - 1)⁻¹) :
    D.extensionRootDiscriminant <
      D.baseRootDiscriminant *
        Real.rpow (D.residuePrime : ℝ)
          ((D.exponent : ℝ) + ((D.residuePrime : ℝ) - 1)⁻¹) := by
  sorry

/- The numerical table is part of the chapter's normalization checks, not a
   claim that any of the displayed universal ceilings is attained. -/
noncomputable def chapter15UniversalLevelOneCeiling (ell : ℕ) : ℝ :=
  Real.rpow (ell : ℝ) ((ell : ℝ) / ((ell : ℝ) - 1))

theorem chapter15_level_two_root_discriminant_check :
    chapter15UniversalLevelOneCeiling 2 = 4 := by
  sorry

theorem chapter15_level_three_root_discriminant_check :
    chapter15UniversalLevelOneCeiling 3 = Real.rpow 3 (3 / 2 : ℝ) := by
  sorry

theorem chapter15_level_five_root_discriminant_check :
    chapter15UniversalLevelOneCeiling 5 = Real.rpow 5 (5 / 4 : ℝ) := by
  sorry

theorem chapter15_quadratic_two_root_discriminant_ratio_check :
    (3 : ℚ) / 2 = 3 / 2 := by
  sorry

/-! The following valuation and trace-dual declarations are retained as the
    Chapter 16 compatibility layer. -/

/-- A bound on the last nontrivial upper-numbered group. -/
def chapter15LastUpperBreakBound
    {G : Type*} [Group G]
    (U : ℝ → Subgroup G) (b : ℝ) : Prop :=
  ∀ r : ℝ, b < r → U r = ⊥

/-- The action of an upper-numbered subgroup is trivial on a representation. -/
def chapter15UpperGroupActsTrivially
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (U : ℝ → Subgroup G) (ρ : Representation k G V) (r : ℝ) : Prop :=
  ∀ g : U r, ρ g = 1

/-- For a faithful action, triviality of the image detects a trivial upper group. -/
theorem chapter15_upper_group_trivial_iff_faithful_action
    {k G V : Type*} [Semiring k] [Group G] [AddCommGroup V] [Module k V]
    (U : ℝ → Subgroup G) (ρ : Representation k G V) (r : ℝ)
    (hfaithful : Function.Injective ρ) :
    U r = ⊥ ↔ chapter15UpperGroupActsTrivially U ρ r := by
  sorry

/-- A separate bound on the order of the finite Galois group. -/
def chapter15GroupOrderBound
    {G : Type*} [Group G] [Finite G] (N : ℕ) : Prop :=
  Nat.card G ≤ N

/-- The numerical form in which a local ramification estimate is consumed. -/
def chapter15DiscriminantExponentBound (δ B : ℕ) : Prop :=
  δ ≤ B

structure Chapter15UpperBreakGroupOrderData
    (G : Type*) [Group G] [Finite G] where
  upper : ℝ → Subgroup G
  lastBreak : ℝ
  lastBreak_nonneg : 0 ≤ lastBreak
  upper_trivial_after : ∀ {r : ℝ}, lastBreak < r → upper r = ⊥
  groupOrderLimit : ℕ
  group_order_bound : Nat.card G ≤ groupOrderLimit

def chapter15UpperDifferentIntegrand
    {G : Type*} [Group G] [Finite G]
    (U : ℝ → Subgroup G) (r : ℝ) : ℝ :=
  (Nat.card (U r) : ℝ) - 1

theorem chapter15_upper_different_integrand_le_group_order
    {G : Type*} [Group G] [Finite G]
    (D : Chapter15UpperBreakGroupOrderData G) (r : ℝ) :
    chapter15UpperDifferentIntegrand D.upper r ≤
      (D.groupOrderLimit : ℝ) - 1 := by
  sorry

/--
The trace-dual lattice whose inverse defines the different.  This is kept as
an explicit interface because the different ideal itself lives downstairs in
the integral model, while the trace form lives in the fraction fields.
-/
noncomputable def chapter15TraceDualLattice
    (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra A B] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L] : Submodule B L :=
  Submodule.traceDual A K (1 : Submodule B L)

/-- Pointwise trace characterization of the trace-dual lattice. -/
theorem chapter15_mem_trace_dual_iff
    (A K B L : Type*) [CommRing A] [Field K] [CommRing B] [Field L]
    [Algebra A K] [Algebra A B] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (x : L) :
    x ∈ chapter15TraceDualLattice A K B L ↔
      ∀ y : B,
        Algebra.trace K L (x * algebraMap B L y) ∈ Set.range (algebraMap A K) := by
  sorry

/--
The source-level separation between field discriminants and Weierstrass
discriminants is represented by their different codomains: an ideal downstairs
versus a coefficient of a chosen model.
-/
theorem chapter15_field_and_model_discriminants_have_distinct_interfaces
    (A R : Type*) [Semiring A] :
    Chapter15FieldDiscriminant A = Ideal A ∧
      Chapter15WeierstrassDiscriminant R = R := by
  exact ⟨rfl, rfl⟩

end

end LastLib.Book03RamificationTheory.Chapter15
