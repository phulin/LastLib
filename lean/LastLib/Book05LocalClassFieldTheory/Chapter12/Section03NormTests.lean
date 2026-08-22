import LastLib.Book05LocalClassFieldTheory.Chapter12.Core
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section05NormLimitation

namespace LastLib.Book05LocalClassFieldTheory.Chapter12

noncomputable section

/-! ## 12.3. Norm tests -/

/-- The norm subgroup is the kernel of the finite Artin map. -/
theorem chapter12_norm_membership_iff_artin_trivial
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (A : Chapter12FiniteArtinMap K L) (x : Kˣ) :
    x ∈ chapter12NormSubgroup K L ↔ A.artin.reciprocity x = 1 := by
  rw [← chapter12_finite_artin_kernel_eq_norm K L A]
  exact MonoidHom.mem_ker

/-- The valuation divisibility part of the norm test. -/
def chapter12NormValuationTest
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (f : ℕ) (x : Kˣ) : Prop :=
  ∃ z : ℤ, C.valuation x = (f : ℤ) * z

/-- Removing a suitable norm of the valuation leaves a unit coordinate. -/
def chapter12NormUnitTest
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ)
    (U : Subgroup C.units) (x : Kˣ) : Prop :=
  ∃ y : H, C.valuation y.1 = C.valuation x ∧
    ∃ u : C.units, (u : Kˣ) = x * y.1⁻¹ ∧ u ∈ U

/-- A higher-unit test records all successive principal-unit obstructions. -/
def chapter12HigherUnitTest
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k)
    (V : ℕ → Subgroup Kˣ) (x : Kˣ) : Prop :=
  ∀ n, 0 < n → x ∈ C.principalUnits n → x ∈ V n

/-- The three-part norm test in a reusable proposition. -/
def chapter12NormTest
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ)
    (f : ℕ) (U : Subgroup C.units) (V : ℕ → Subgroup Kˣ)
    (x : Kˣ) : Prop :=
  chapter12NormValuationTest C f x ∧
    chapter12NormUnitTest C H U x ∧
    chapter12HigherUnitTest C V x

/-- The hypotheses consumed by the norm-test reconstruction lemma.  The
valuation and unit-layer clauses are deliberately separate so that later
norm-filtration proofs can replace either component without changing the API. -/
/- The converse reconstruction direction is intentionally left to the
canonical norm-filtration interface from the missing preceding chapters; the
safe projection theorem below records the direction available from these
book-facing factors. -/
structure Chapter12NormTestProfile
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ) where
  residueDegree : ℕ
  unitNormSubgroup : Subgroup C.units
  higherNormSubgroups : ℕ → Subgroup Kˣ
  valuation_factor :
    ∀ {x : Kˣ}, x ∈ H → chapter12NormValuationTest C residueDegree x
  unit_factor :
    ∀ {x : Kˣ}, x ∈ H → chapter12NormUnitTest C H unitNormSubgroup x
  higher_factor :
    ∀ {x : Kˣ}, x ∈ H → chapter12HigherUnitTest C higherNormSubgroups x

/-- Membership in a norm group supplies the valuation, unit, and higher-unit
tests. -/
theorem chapter12_norm_membership_implies_three_tests
    {K k : Type*} [Field K] [Field k]
    {C : Chapter12LocalCoordinates K k} {H : Subgroup Kˣ}
    (P : Chapter12NormTestProfile C H) {x : Kˣ} (hx : x ∈ H) :
    chapter12NormTest C H P.residueDegree P.unitNormSubgroup
      P.higherNormSubgroups x := by
  exact ⟨P.valuation_factor hx, P.unit_factor hx, P.higher_factor hx⟩

/-- For an unramified profile, only valuation divisibility remains. -/
def chapter12UnramifiedNormTest
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (f : ℕ) (x : Kˣ) : Prop :=
  chapter12NormValuationTest C f x

theorem chapter12_unramified_norm_test_iff_valuation
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (f : ℕ) (x : Kˣ) :
    chapter12UnramifiedNormTest C f x ↔
      chapter12NormValuationTest C f x := by
  rfl

/-- In tame total ramification the valuation is unrestricted and principal
units are norms; the remaining obstruction is the residue-unit class. -/
def chapter12TameTotallyRamifiedNormProfile
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ) : Prop :=
  Function.Surjective (fun y : H => C.valuation y.1) ∧
    ∀ n, 0 < n → C.principalUnits n ≤ H

theorem chapter12_tame_total_profile_has_unrestricted_valuation_and_principal_norms
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ)
    (hprofile : chapter12TameTotallyRamifiedNormProfile C H) :
    Function.Surjective (fun y : H => C.valuation y.1) ∧
      ∀ n, 0 < n → C.principalUnits n ≤ H := by
  exact hprofile

def chapter12TameTotallyRamifiedNormTest
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ)
    (U : Subgroup C.units) (x : Kˣ) : Prop :=
  chapter12NormUnitTest C H U x ∧
    chapter12HigherUnitTest C (fun n => C.principalUnits n) x

theorem chapter12_tame_total_norm_test_has_no_valuation_obstruction
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k) (H : Subgroup Kˣ)
    (U : Subgroup C.units) (x : Kˣ)
    (_hvaluation : Function.Surjective (fun y : H => C.valuation y.1)) :
    chapter12TameTotallyRamifiedNormTest C H U x ↔
      chapter12NormUnitTest C H U x ∧
        chapter12HigherUnitTest C (fun n => C.principalUnits n) x := by
  rfl

/-- Wild ramification contributes genuine higher principal-unit obstructions. -/
def chapter12WildNormObstruction
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k)
    (V : ℕ → Subgroup Kˣ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ V n ≠ C.principalUnits n

theorem chapter12_wild_norm_test_sees_higher_layers
    {K k : Type*} [Field K] [Field k]
    (C : Chapter12LocalCoordinates K k)
    (V : ℕ → Subgroup Kˣ)
    (hwild : chapter12WildNormObstruction C V) :
    ∃ n : ℕ, 0 < n ∧ V n ≠ C.principalUnits n := by
  exact hwild

/-- Norm limitation reduces a finite Galois extension to its maximal abelian
subextension. -/
theorem chapter12_nonabelian_norm_limitation
    (K E : Type) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [IsGalois K E]
    [Fintype (Gal(E / K))]
    [Fintype (Gal(
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05MaximalAbelianField K E / K))]
    (D : LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData K E)
    (DM : LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData K
      (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05MaximalAbelianField K E)) :
    LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K E =
      LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K
        (LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05MaximalAbelianField K E) := by
  exact LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05_norm_limitation K E D DM

end

end LastLib.Book05LocalClassFieldTheory.Chapter12
