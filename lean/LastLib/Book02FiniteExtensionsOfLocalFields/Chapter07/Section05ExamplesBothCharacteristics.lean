import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section04FiniteResidueFields

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07

open Set
open Polynomial
open LastLib.Book01ValuationsDVRsAndCompletions.Chapter10

noncomputable section

/-! # Book 2, Chapter 7, §7.5: examples in both characteristics -/

/-- A purely inseparable residue extension in characteristic `p`, written
without imposing a perfectness typeclass on the base field. -/
def Chapter07PurelyInseparableResidueExtension
    (k k' : Type*) [Field k] [Field k'] [Algebra k k'] (p : ℕ)
    [ExpChar k p] : Prop :=
  ∀ x : k', ∃ n : ℕ, ∃ y : k,
    x ^ (p ^ n) = algebraMap k k' y

/-- An element witnessing that a characteristic-`p` field is imperfect. -/
def Chapter07ImperfectElement
    (k : Type*) [Field k] (p : ℕ) [ExpChar k p] (a : k) : Prop :=
  a ∉ Set.range (fun x : k => x ^ p)

/-- Over `Q_p`, an irreducible separable residue polynomial produces the
unramified profile with its degree spent entirely in the residue field. -/
theorem chapter07_padic_irreducible_residue_lift
    {p : ℕ} [Fact p.Prime]
    (res : ℤ_[p] →+* ZMod p) (P : ℤ_[p][X]) (f : ℕ)
    (hred : Chapter10IrreducibleSeparableReduction res P f)
    {L : Type*} [Field L] [Algebra ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L]
    (α : L)
    (hroot : eval₂ (algebraMap ℚ_[p] L) α (P.map (algebraMap ℤ_[p] ℚ_[p])) = 0)
    (hgen : Algebra.adjoin ℚ_[p] ({α} : Set L) = ⊤)
    (hdegree : Module.finrank ℚ_[p] L = f) :
    ∃ q : Chapter10FiniteExtensionProfile,
      q.degree = f ∧ q.ramificationIndex = 1 ∧ q.residueDegree = f ∧
        Chapter10Unramified q := by
  letI : Algebra ℤ_[p] L :=
    Algebra.compHom L (algebraMap ℤ_[p] ℚ_[p])
  exact chapter10_unramified_lift_profile res P f hred α
    (by
      change eval₂ ((algebraMap ℚ_[p] L).comp (algebraMap ℤ_[p] ℚ_[p])) α P = 0
      rw [← eval₂_map]
      exact hroot) hgen hdegree

/-- The base prime `p` keeps normalized value one in the unramified `p`-adic
extension. -/
theorem chapter07_padic_prime_is_a_uniformizer
    {p : ℕ} [Fact p.Prime] :
    Padic.valuation (p : ℚ_[p]) = 1 := by
  exact chapter10_padic_uniformizer_value

/-- In the equal-characteristic model, extending the coefficient field leaves
the parameter `t` unchanged and gives `e = 1`, `f = [k' : k]`. -/
theorem chapter07_equal_characteristic_constant_field_extension
    {k k' : Type*} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] :
    ∃ p : Chapter10FiniteExtensionProfile,
      p.degree = Module.finrank k k' ∧ p.ramificationIndex = 1 ∧
        p.residueDegree = Module.finrank k k' ∧ Chapter10Unramified p := by
  exact chapter10_constant_field_extension_profile (Module.finrank k k') rfl

/-- The Laurent-series realization uses `k'((t))/k((t))`; the common
uniformizer is the Laurent-series parameter. -/
theorem chapter07_laurent_series_parameter_is_common
    (k : Type*) [Field k] (n : ℕ) :
    Chapter10LaurentSeriesValuation k
        (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ n) =
      WithZero.exp (-(n : ℤ)) := by
  exact chapter10_laurent_series_parameter_value n

/-- The precise `e = 1`, residue-degree-`p`, inseparable conclusion is exposed
as a profile theorem; the polynomial realization supplies the hypotheses in a
later proof pass. -/
theorem chapter07_purely_inseparable_residue_profile
    {K L k k' : Type*} [Field K] [Field L] [Field k] [Field k']
    [Algebra K L] [Algebra k k']
    [FiniteDimensional K L] [FiniteDimensional k k']
    (p : ℕ) (E : Chapter07FiniteLocalExtensionData K L k k')
    (he : E.ramificationIndex = 1)
    (hf : E.residueDegree = p)
    (hinsep : ¬Chapter07ResidueExtensionIsSeparable k k') :
    Chapter07FiercelyRamifiedExtension E ∧
      ¬Chapter07UnramifiedExtension E ∧ E.residueDegree = p := by
  constructor
  · exact ⟨he, hinsep⟩
  constructor
  · exact chapter07_fierce_is_not_unramified E ⟨he, hinsep⟩
  · exact hf

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
