import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13.Section03FinitenessInCharacteristicZero
import Mathlib.RingTheory.LaurentSeries

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13

noncomputable section

open Polynomial

/-! ## 13.4. The tame positive-characteristic range -/

def chapter13ResidueCharacteristicExponent (k : Type*) [Ring k] : ℕ :=
  ringExpChar k

/-- The derivative has the expected nonzero leading term when the degree is
prime to the field characteristic. -/
theorem chapter13_prime_to_characteristic_derivative_has_expected_degree
    {E : Type*} [Field E] {p e : ℕ} [Fact p.Prime] [CharP E p]
    (g : E[X]) (hmonic : g.Monic) (hdegree : g.natDegree = e)
    (he : 0 < e) (he_p : Nat.Coprime e p) :
    (g.derivative).natDegree = e - 1 ∧
      g.derivative.leadingCoeff = (e : E) := by
  sorry

/-- An irreducible monic degree-`e` polynomial over a field of characteristic
`p` is separable when `p` does not divide `e`.  Irreducibility is essential:
a repeated-factor polynomial can have prime-to-`p` total degree. -/
theorem chapter13_prime_to_characteristic_monic_polynomial_is_separable
    {E : Type*} [Field E] {p e : ℕ} [Fact p.Prime] [CharP E p]
    (g : E[X]) (hirreducible : Irreducible g) (hmonic : g.Monic)
    (hdegree : g.natDegree = e)
    (he : 0 < e) (he_p : Nat.Coprime e p) :
    g.Separable := by
  sorry

/-- In characteristic zero, every irreducible monic positive-degree
polynomial is separable. -/
theorem chapter13_characteristic_zero_monic_polynomial_is_separable
    {E : Type*} [Field E] [CharZero E]
    (g : E[X]) (hirreducible : Irreducible g) (he : 0 < g.natDegree)
    (hmonic : g.Monic) :
    g.Separable := by
  sorry

theorem chapter13_characteristic_zero_irreducible_polynomial_is_separable
    {E : Type*} [Field E] [CharZero E]
    (g : E[X]) (hirreducible : Irreducible g) :
    g.Separable := by
  sorry

/-- The prime-to-residue-characteristic condition is the exact tame
condition used in the coefficient argument. -/
theorem chapter13_eisenstein_degree_prime_to_residue_characteristic_is_separable
    {A E : Type*} [CommRing A] [Field E]
    [Algebra A E] {p e : ℕ} [Fact p.Prime] [CharP E p]
    (g : A[X])
    (hirreducible : Irreducible (g.map (algebraMap A E)))
    (hmonic : (g.map (algebraMap A E)).Monic)
    (hdegree : (g.map (algebraMap A E)).natDegree = e)
    (he : 0 < e) (he_p : Nat.Coprime e p) :
    (g.map (algebraMap A E)).Separable := by
  exact chapter13_prime_to_characteristic_monic_polynomial_is_separable
    _ hirreducible hmonic hdegree he he_p

/-- Unramified extensions are tame because their ramification index is one. -/
theorem chapter13_unramified_ramification_index_is_tame
    (k : Type*) [Field k] :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter09.chapter09Tame k 1 := by
  exact Nat.coprime_one_left _

/-- A tame Eisenstein coefficient family therefore satisfies the separability
hypothesis required by the Krasner local-constancy interface. -/
theorem chapter13_tame_eisenstein_family_is_separable
    {A E : Type*} [CommRing A] [Field E]
    [Algebra A E] {p e : ℕ} [Fact p.Prime] [CharP E p]
    (_m : Ideal A) (g : A[X])
    (_hEisenstein : g.IsEisensteinAt _m)
    (hirreducible : Irreducible (g.map (algebraMap A E)))
    (hmonic : (g.map (algebraMap A E)).Monic)
    (hdegree : (g.map (algebraMap A E)).natDegree = e)
    (he : 0 < e) (he_p : Nat.Coprime e p) :
    (g.map (algebraMap A E)).Separable := by
  exact chapter13_eisenstein_degree_prime_to_residue_characteristic_is_separable
    g hirreducible hmonic hdegree he he_p

/-- The tame proof has the same compact-family shape as the characteristic
zero proof; only the separability bridge changes. -/
theorem chapter13_tame_finiteness_reduces_to_compact_separable_families
    {P C : Type*} [TopologicalSpace P]
    (φ : P → C) (hcompact : IsCompact (Set.univ : Set P))
    (hlocally_constant : chapter13LocallyConstant φ) :
    Set.Finite (Set.range φ) := by
  exact chapter13_compact_locally_constant_range_finite φ hcompact
    hlocally_constant

/-! The fixed-degree corollary is stated at the valuation level, where the
ramification index divides the defectless degree product. -/
theorem chapter13_prime_to_p_degree_extension_is_tame
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ]
    (vK : Valuation K Γ) (vL : Valuation L Γ)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL] [FiniteDimensional K L]
    [PerfectField (IsLocalRing.ResidueField vK.valuationSubring)]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (p d : ℕ) [Fact p.Prime]
    (hchar : ringExpChar (IsLocalRing.ResidueField vK.valuationSubring) = p)
    (hdegree : Module.finrank K L = d) (hd : Nat.Coprime d p) :
    chapter13TameExtension vK vL := by
  sorry

/-- Fixed-degree tame finiteness in equal characteristic.  The conclusion is
stated on the canonical `K`-isomorphism-class set from the dependency layer. -/
theorem chapter13_laurent_series_prime_to_p_degree_finiteness
    (k : Type*) [Field k] [Fintype k]
    (p d : ℕ) [Fact p.Prime] [CharP k p]
    (hd : Nat.Coprime d p) :
    Set.Finite (chapter13DegreeClasses (K := LaurentSeries k) d) := by
  sorry

/-- The numerical scope of the tame corollary: the prime-to-`p` hypothesis is
what permits the preceding separability argument. -/
def chapter13TameDegreeScope (p d : ℕ) : Prop :=
  Nat.Coprime d p

theorem chapter13_tame_degree_scope_iff
    (p d : ℕ) :
    chapter13TameDegreeScope p d ↔ Nat.Coprime d p :=
  Iff.rfl

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter13
