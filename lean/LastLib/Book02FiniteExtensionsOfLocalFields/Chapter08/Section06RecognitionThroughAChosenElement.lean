import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section05MonogenicityAndResidueGenerators
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section02EisensteinCoefficientsAndValueBalance

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
    [HenselianLocalRing A]
    (fbar : k[X]) (f : A[X]) (θ : L)
    (_hred : chapter08IrreducibleSeparableReduction fbar f)
    (_hroot : aeval θ f = 0)
    (_hgen : Algebra.adjoin K ({θ} : Set L) = ⊤)
    (_hdegree : Module.finrank K L = f.natDegree)
    (_hsamedegree : fbar.natDegree = f.natDegree)
    (_hresidue : ∃ e : IsLocalRing.ResidueField A ≃+* k,
      ∀ a : A, algebraMap A k a = e (IsLocalRing.residue A a))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hdiscreteK :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vK)
    (hdiscreteL :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vL)
    (hA : vK.Integers A)
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL)) :
    ∃ d : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10HeterogeneousExtensionData
        vK vL hval,
      ∃ q : LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10FiniteExtensionProfile,
        LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10ProfileRealizedByData d q ∧
          q.degree = Module.finrank K L ∧ q.ramificationIndex = 1 ∧
          q.residueDegree = Module.finrank K L ∧
          LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10Unramified q ∧
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10UnramifiedBranch
            vK vL hval d := by
  have hdiscreteK' := hdiscreteK
  have hdiscreteL' := hdiscreteL
  clear hdiscreteK' hdiscreteL'
  rcases _hred with ⟨hbarMonic, hMonic, hIrred, hSep, hmap⟩
  have hred :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10IrreducibleSeparableReduction
        (algebraMap A k) f f.natDegree := by
    dsimp [LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10IrreducibleSeparableReduction]
    refine ⟨hMonic, ?_, ?_, ?_, ?_⟩
    · rw [hmap]
      exact hbarMonic
    · rw [hmap]
      exact _hsamedegree
    · rw [hmap]
      exact hIrred
    · rw [hmap]
      exact hSep
  have hres : ∃ e : IsLocalRing.ResidueField A ≃+* k,
      e.toRingHom.comp (IsLocalRing.residue A) = algebraMap A k := by
    rcases _hresidue with ⟨e, he⟩
    refine ⟨e, ?_⟩
    ext a
    exact (he a).symm
  have hroot : Polynomial.eval₂ (algebraMap A L) θ f = 0 := by
    simpa [Polynomial.aeval_def] using _hroot
  obtain ⟨d, q, hd, hirr, hqdeg, hqram, hqres, hqunram, hbranch, hsep⟩ :=
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.chapter10_unramified_lift_profile
      (algebraMap A k) f f.natDegree hred hres θ hroot _hgen _hdegree
      vK vL hA hval
  exact ⟨d, q, hd, hqdeg.trans _hdegree.symm, hqram, hqres.trans _hdegree.symm,
    hqunram, hbranch⟩

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
    (hvalue_ideal : ∀ a : A,
      a ∈ IsLocalRing.maximalIdeal A ↔
        0 < vK (algebraMap A K a))
    (hvalue_square : ∀ a : A,
      a ∈ IsLocalRing.maximalIdeal A ∧
        a ∉ (IsLocalRing.maximalIdeal A) ^ 2 ↔
        vK (algebraMap A K a) = 1)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = f.natDegree • vK x)
    (hπ : vK (algebraMap A K π) = 1) :
    Module.finrank K L = f.natDegree ∧
      chapter08TotallyRamified vK vL hval := by
  have h := chapter08_eisenstein_extension
    vK vL hval π f θ hf hroot hgen hvalue_ideal hvalue_square hscale hπ
  exact ⟨h.2.1, h.2.2.1⟩

/-- The chosen integral order attached to a polynomial generator. -/
def chapter08ChosenIntegralOrder
    (A L : Type*) [CommRing A] [Field L] [Algebra A L]
    (θ : L) : Subalgebra A L :=
  Algebra.adjoin A ({θ} : Set L)

/-! Reduction of a polynomial is only an order-level test until the following
normalization equality has been supplied. -/

/-- Book §8.6: the chosen order is the full integral closure, the extra datum
needed to turn polynomial recognition into an intrinsic statement about `B`. -/
def chapter08ChosenOrderMatchesNormalization
    (A L : Type*) [CommRing A] [Field L] [Algebra A L]
    (θ : L) : Prop :=
  (integralClosure A L : Set L) =
    (chapter08ChosenIntegralOrder A L θ : Set L)

/-- The chosen-order formulation is equivalent to the integral-generator
formulation used in §8.5. -/
theorem chapter08_integral_generator_for_iff_chosen_order_matches_normalization
    (A L : Type*) [CommRing A] [Field L] [Algebra A L]
    (θ : L) :
    chapter08IntegralGeneratorFor A L θ ↔
      IsIntegral A θ ∧ chapter08ChosenOrderMatchesNormalization A L θ := by
  rfl

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
