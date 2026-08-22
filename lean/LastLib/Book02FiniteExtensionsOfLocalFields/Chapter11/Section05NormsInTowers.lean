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
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) :
    chapter11NormImage K L vL n =
      Algebra.norm K '' chapter11NormImage M L vL n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Algebra.norm M y, ⟨y, hy, rfl⟩, ?_⟩
    exact Algebra.norm_norm (R := K) (S := M) (a := y)
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨y, hy, ?_⟩
    exact (Algebra.norm_norm (R := K) (S := M) (a := y)).symm

/- Finite residue fields make both residue maps surjective, independently of
   the deeper ramified unit calculation. -/
theorem chapter11_finite_residue_norm_and_trace_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Finite l] [FiniteDimensional k l] :
    Function.Surjective (Algebra.norm k (S := l)) ∧
      Function.Surjective (Algebra.trace k l) := by
  exact ⟨chapter11_finite_residue_norm_surjective k l,
    chapter11_unramified_residue_trace_surjective k l⟩

/- Under the finite-residue and completeness hypotheses, failure of principal
   unit norm-surjectivity rules out unramifiedness; the remaining obstruction
   is therefore ramified. -/
theorem chapter11_deep_norm_failure_is_ramified
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Finite (chapter11ResidueField vK)]
    [Finite (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hdegree : Module.finrank K L =
      Module.finrank (chapter11ResidueField vK) (chapter11ResidueField vL))
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL))
    (hfail : ¬Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1)) :
    ¬chapter11UnramifiedValuedExtension vK vL := by
  have hunused := And.intro hcompleteK hcompleteL
  clear hunused
  intro hunram
  apply hfail
  exact proposition_11_1_unramified_principal_unit_norm_surjective K L vK vL
    hunram hdegree hred

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
