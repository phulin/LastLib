import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07.Section04FiniteResidueFields
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Section07ConcreteFiniteExtensions

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
  0 < p ∧ ∀ x : k', ∃ n : ℕ, ∃ y : k,
    x ^ (p ^ n) = algebraMap k k' y

/-- An element witnessing that a characteristic-`p` field is imperfect. -/
def Chapter07ImperfectElement
    (k : Type*) [Field k] (p : ℕ) [ExpChar k p] (a : k) : Prop :=
  0 < p ∧ a ∉ Set.range (fun x : k => x ^ p)

/-- Over `Q_p`, an irreducible separable residue polynomial produces the
unramified profile with its degree spent entirely in the residue field. -/
theorem chapter07_padic_irreducible_residue_lift
    {p : ℕ} [Fact p.Prime]
    (res : ℤ_[p] →+* ZMod p) (P : ℤ_[p][X]) (f : ℕ)
    (hred : Chapter10IrreducibleSeparableReduction res P f)
    {L : Type*} [Field L] [Algebra ℤ_[p] L] [Algebra ℚ_[p] L]
    [IsScalarTower ℤ_[p] ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L]
    (α : L)
    (hroot : eval₂ (algebraMap ℤ_[p] L) α P = 0)
    (hgen : Algebra.adjoin ℚ_[p] ({α} : Set L) = ⊤)
    (hdegree : Module.finrank ℚ_[p] L = f)
    (vL : AddValuation L (WithTop ℤ))
    (hvL : Chapter10DiscreteAddValuation vL)
    (hext : (Padic.addValuation (p := p)).IsEquiv
      (vL.comap (algebraMap ℚ_[p] L)))
    (hA : (Padic.addValuation (p := p)).Integers (ℤ_[p]))
    (hres : ∃ e : IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p,
      e.toRingHom.comp (IsLocalRing.residue ℤ_[p]) = res) :
    ∃ d : Chapter10HeterogeneousExtensionData
        (Padic.addValuation (p := p)) vL hext,
      ∃ q : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d q ∧
          q.degree = f ∧ q.ramificationIndex = 1 ∧ q.residueDegree = f ∧
          Chapter10Unramified q ∧
          Chapter10UnramifiedBranch
            (Padic.addValuation (p := p)) vL hext d := by
  sorry

/-- The base prime `p` keeps normalized value one in the unramified `p`-adic
extension. -/
theorem chapter07_padic_prime_is_a_uniformizer
    {p : ℕ} [Fact p.Prime] :
    Padic.valuation (p : ℚ_[p]) = 1 := by
  sorry

/-- In the equal-characteristic model, extending the coefficient field leaves
the parameter `t` unchanged and gives `e = 1`, `f = [k' : k]`. -/
theorem chapter07_equal_characteristic_constant_field_extension
    {k k' : Type*} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k']
    [Algebra (LaurentSeries k) (LaurentSeries k')]
    [FiniteDimensional (LaurentSeries k) (LaurentSeries k')]
    [IsScalarTower k (LaurentSeries k) (LaurentSeries k')]
    (hparameter :
      algebraMap (LaurentSeries k) (LaurentSeries k')
          (((PowerSeries.X : PowerSeries k) : LaurentSeries k)) =
        ((PowerSeries.X : PowerSeries k') : LaurentSeries k'))
    (hseparable : Algebra.IsSeparable k k')
    (h : (Chapter10LaurentSeriesValuation k).IsEquiv
      ((Chapter10LaurentSeriesValuation k').comap
        (algebraMap (LaurentSeries k) (LaurentSeries k')))) :
    ∃ d : Chapter10HeterogeneousExtensionData
        (Chapter10LaurentSeriesValuation k)
        (Chapter10LaurentSeriesValuation k') h,
      ∃ p : Chapter10FiniteExtensionProfile,
        Chapter10ProfileRealizedByData d p ∧
          p.degree = Module.finrank k k' ∧ p.ramificationIndex = 1 ∧
          p.residueDegree = Module.finrank k k' ∧ Chapter10Unramified p ∧
          Chapter10UnramifiedBranch
            (Chapter10LaurentSeriesValuation k)
            (Chapter10LaurentSeriesValuation k') h d := by
  sorry

/-- The Laurent-series realization uses `k'((t))/k((t))`; the common
uniformizer is the Laurent-series parameter. -/
theorem chapter07_laurent_series_parameter_is_common
    (k : Type*) [Field k] (n : ℕ) :
    Chapter10LaurentSeriesValuation k
        (((PowerSeries.X : PowerSeries k) : LaurentSeries k) ^ n) =
      WithZero.exp (-(n : ℤ)) := by
  sorry

/-- The precise `e = 1`, residue-degree-`p`, inseparable conclusion is exposed
as a profile theorem; the polynomial realization supplies the hypotheses in a
later proof pass. -/
theorem chapter07_purely_inseparable_residue_profile
    {K L k k' : Type*} [Field K] [Field L] [Field k] [Field k']
    [Algebra K L] [Algebra k k']
    [FiniteDimensional K L] [FiniteDimensional k k']
    (p : ℕ) [ExpChar k p]
    (E : Chapter07FiniteLocalExtensionData K L k k')
    (he : E.ramificationIndex = 1)
    (hf : E.residueDegree = p)
    (hinsep : Chapter07PurelyInseparableResidueExtension k k' p)
    (hinsep_nontrivial : ¬Chapter07ResidueExtensionIsSeparable k k')
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hext : vK.IsEquiv (vL.comap (algebraMap K L)))
    (d : Chapter10HeterogeneousExtensionData vK vL hext)
    (hactual : d.ramificationIndex = E.ramificationIndex ∧
      d.residueDegree = E.residueDegree) :
      Chapter10ProfileRealizedByData d
        { degree := Module.finrank K L
          ramificationIndex := E.ramificationIndex
          residueDegree := E.residueDegree } ∧
      Chapter07FiercelyRamifiedExtension E ∧
      ¬Chapter07UnramifiedExtension E := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter07
