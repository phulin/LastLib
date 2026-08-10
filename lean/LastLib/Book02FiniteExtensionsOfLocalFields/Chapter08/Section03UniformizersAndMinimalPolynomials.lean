import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.Section02EisensteinCoefficientsAndValueBalance

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08

noncomputable section

open Polynomial
open scoped WithTop

/-! # 8.3. Every totally ramified extension comes from a uniformizer -/

/-- Book §8.3: a normalized value-one element generates the field in a finite
totally ramified extension once the base is a complete DVR. -/
theorem chapter08_uniformizer_generates_the_field
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfinite : Module.Finite A (integralClosure A L))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (htotal : chapter08TotallyRamified vK vL hval)
    (πL : L) (hπL : vL πL = 1) :
    Algebra.adjoin K ({πL} : Set L) = ⊤ := by
  sorry

/-- The coefficient-level form of the uniformizer theorem: the minimal
polynomial of a uniformizer is Eisenstein over the base DVR. -/
theorem chapter08_uniformizer_minpoly_is_eisenstein
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfinite : Module.Finite A (integralClosure A L))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (htotal : chapter08TotallyRamified vK vL hval)
    (πK : A) (hπK : vK (algebraMap A K πK) = 1)
    (πL : L) (hπL : vL πL = 1)
    (g : A[X])
    (hminpoly : g.map (algebraMap A K) = minpoly K πL) :
    LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt πK g ∧
      g.natDegree = Module.finrank K L := by
  sorry

/-- Book §8.3, Theorem 8.2: every uniformizer of a finite totally ramified
local extension generates both the field and its integral closure, and its
minimal polynomial is Eisenstein of the field degree. -/
theorem chapter08_uniformizer_theorem
    {A K L : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfinite : Module.Finite A (integralClosure A L))
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (htotal : chapter08TotallyRamified vK vL hval)
    (πK : A) (hπK : vK (algebraMap A K πK) = 1)
    (πL : L) (hπL : vL πL = 1) :
    ∃ g : A[X],
      g.Monic ∧
      g.map (algebraMap A K) = minpoly K πL ∧
      g.natDegree = Module.finrank K L ∧
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt πK g ∧
      Algebra.adjoin K ({πL} : Set L) = ⊤ ∧
      (integralClosure A L : Set L) =
        (Algebra.adjoin A ({πL} : Set L) : Set L) ∧
      vL πL = 1 := by
  sorry

/-- The norm of a uniformizer in a finite totally ramified extension has
valuation one in the base field (Book 2, Section 8.3). -/
theorem chapter08_uniformizer_norm_has_value_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (hval : vK.IsEquiv (AddValuation.comap (algebraMap K L) vL))
    (e : ℕ) (he : 0 < e)
    (hedegree : e = Module.finrank K L)
    (hscale : ∀ x : K, x ≠ 0 →
      vL (algebraMap K L x) = e • vK x)
    (htotal : chapter08TotallyRamified vK vL hval)
    (varpi : L) (hvarpi : vL varpi = 1) :
    vK (Algebra.norm K varpi) = 1 := by
  sorry

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08
