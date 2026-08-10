import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section05MonogenicityAndResidueGenerators

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial

/-! # 8.6. Recognition through a chosen element -/

/-- The reduction-side hypotheses used to recognize an unramified extension
from a chosen polynomial. -/
def chapter08IrreducibleSeparableReduction
    {A k : Type*} [CommRing A] [Field k] [Algebra A k]
    (fbar : k[X]) (f : A[X]) : Prop :=
  fbar.Monic ∧ f.Monic ∧ Irreducible fbar ∧ fbar.Separable ∧
    f.map (algebraMap A k) = fbar

/-- Book §8.6: irreducible separable reduction of the same degree recognizes
an unramified branch. -/
theorem chapter08_irreducible_separable_reduction_recognizes_unramified
    {A K L k : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L] [Field k]
    [Algebra A k]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (fbar : k[X]) (f : A[X]) (θ : L)
    (hred : chapter08IrreducibleSeparableReduction fbar f)
    (hroot : aeval θ f = 0)
    (hgen : Algebra.adjoin K ({θ} : Set L) = ⊤)
    (hdegree : Module.finrank K L = f.natDegree)
    (hsamedegree : fbar.natDegree = f.natDegree) :
    ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
      q.degree = Module.finrank K L ∧ q.ramificationIndex = 1 ∧
        q.residueDegree = Module.finrank K L ∧
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified q := by
  sorry

/-- Book §8.6: an Eisenstein polynomial recognizes the totally ramified
endpoint through the chosen element. -/
theorem chapter08_eisenstein_reduction_recognizes_total_ramification
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (π : A) (f : A[X]) (θ : L)
    (hf : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval θ f = 0)
    (hgen : Algebra.adjoin K ({θ} : Set L) = ⊤)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = f.natDegree • vK x)
    (hπ : vK (algebraMap A K π) = 1) :
    ∃ e fdeg : ℕ,
      e = f.natDegree ∧ fdeg = 1 ∧
        Module.finrank K L = f.natDegree ∧
        chapter08TotallyRamified vK vL hval := by
  sorry

/-- The chosen integral order attached to a polynomial generator. -/
def chapter08ChosenIntegralOrder
    (A L : Type*) [CommRing A] [Field L] [Algebra A L]
    (θ : L) : Subalgebra A L :=
  Algebra.adjoin A ({θ} : Set L)

/-- Book §8.6: repeated factors in a reduced polynomial provide evidence but
do not by themselves compute the intrinsic ramification index. -/
theorem chapter08_repeated_reduction_requires_integral_closure_check
    {A : Type*} [CommRing A] (f : A[X])
    (hrepeated : ∃ g : A[X], g ≠ 0 ∧ g * g ∣ f) :
    ∃ g q : A[X], g ≠ 0 ∧ f = g * g * q := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
