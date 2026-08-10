import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section04TheTotallyRamifiedCase

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open scoped BigOperators

/-! ## 11.5. Norms in towers -/

/- A supplied two-stage factorization records the unramified first stage and
   totally ramified second stage without assuming that a general local-field
   factorization is canonical. -/
def chapter11UnramifiedThenTotallyRamifiedFactorization
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    (vK : AddValuation K (WithTop ℤ)) (vM : AddValuation M (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (eKM eML : ℕ) : Prop :=
  chapter11UnramifiedValuedExtension vK vM ∧
    chapter11ValuationExtension vM vL ∧
    chapter11ValuationScaling vM vL eML ∧
    chapter11TotallyRamifiedResidueAgreement vM vL ∧
    chapter11ValuationScaling vK vM eKM

/- Norms are transitive on every filtration layer. -/
theorem chapter11_norms_transitive_on_unit_filtration
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) :
    chapter11NormImage K L vL n =
      Algebra.norm K '' chapter11NormImage M L vL n := by
  sorry

/- The residue norm and trace are the two maps handled by the unramified
   stage of a two-stage calculation. -/
theorem chapter11_two_stage_residue_norm_trace_interface
    (K M L : Type*) [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (vK : AddValuation K (WithTop ℤ)) (vM : AddValuation M (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (eKM eML : ℕ)
    (hfactor : chapter11UnramifiedThenTotallyRamifiedFactorization
      K M L vK vM vL eKM eML) (n : ℕ) :
    chapter11NormImage K L vL n =
      Algebra.norm K '' chapter11NormImage M L vL n := by
  exact chapter11_norms_transitive_on_unit_filtration K M L vL n

/- Finite residue fields make both residue maps surjective, independently of
   the deeper ramified unit calculation. -/
theorem chapter11_finite_residue_norm_and_trace_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Finite l] [FiniteDimensional k l] :
    Function.Surjective (Algebra.norm k (S := l)) ∧
      Function.Surjective (Algebra.trace k l) := by
  constructor
  · exact FiniteField.norm_surjective k l
  · exact Algebra.trace_surjective k l

/- Under the finite-residue and completeness hypotheses, failure of principal
   unit norm-surjectivity rules out unramifiedness; the remaining obstruction
   is therefore ramified. -/
theorem chapter11_deep_norm_failure_is_ramified
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (hfail : ¬Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1)) :
    ¬chapter11UnramifiedValuedExtension vK vL := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
