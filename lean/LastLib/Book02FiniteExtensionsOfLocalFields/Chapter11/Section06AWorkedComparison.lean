import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section05NormsInTowers
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section04TheValuationOfANorm

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

/-! ## 11.6. A worked comparison -/

/- The symbol `q` in the finite-residue comparison is the cardinality of the
   residue field, not an implicit characteristic-zero assumption. -/
def chapter11ResidueFieldCardinality (k : Type*) [Fintype k] : ℕ :=
  Fintype.card k

/- In the unramified case the norm valuation is multiplication by the residue
   degree. -/
theorem chapter11_unramified_comparison_norm_valuation
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (f : ℕ) (hunram : chapter11UnramifiedValuedExtension vK vL)
    [Valuation.IsRankOneDiscrete vK.toValuation]
    [Valuation.IsRankOneDiscrete vL.toValuation]
    (hunique : ∀ w : AddValuation L (WithTop ℤ),
      vK.IsEquiv (AddValuation.comap (algebraMap K L) w) → vL.IsEquiv w)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1) (x : L) :
    vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x := by
  sorry

/- All base units are norms in the finite-residue unramified comparison. -/
theorem chapter11_unramified_comparison_units_are_norms
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    [Finite (chapter11ResidueField vK)]
    [Finite (chapter11ResidueField vL)]
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hdegree : Module.finrank K L =
      Module.finrank (chapter11ResidueField vK) (chapter11ResidueField vL))
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL))
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L
      (chapter11ResidueField vK) (chapter11ResidueField vL) vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL) 1 N) :
    Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 0) (chapter11UnitFiltration vK 0) := by
  sorry

/- A base uniformizer cannot be a norm when the unramified degree is greater
   than one, because its valuation is not divisible by that degree. -/
theorem chapter11_unramified_comparison_uniformizer_not_a_norm
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (f : ℕ) (hf : 1 < f)
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    (hnorm : chapter11NormValuationFormula K L vK vL f)
    (hdegree : Module.finrank K L = f)
    (hfres : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hunram.1) (πK : K)
    (hπ : vK πK = (1 : WithTop ℤ)) :
    ¬∃ x : L, Algebra.norm K x = πK := by
  rintro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro hx0
    have hπ0 : πK = 0 := by
      rw [← hx]
      simp [hx0]
    rw [hπ0] at hπ
    norm_num at hπ
  have hval : (1 : WithTop ℤ) = (f : WithTop ℤ) * vL x := by
    calc
      1 = vK πK := hπ.symm
      _ = vK (Algebra.norm K x) := by rw [hx]
      _ = _ := hnorm x hx0
  obtain ⟨z, hz⟩ := WithTop.ne_top_iff_exists.mp (vL.ne_top_iff.mpr hx0)
  have hzval : (1 : WithTop ℤ) = (f : WithTop ℤ) * (z : WithTop ℤ) := by
    simpa [hz] using hval
  have hzint : (1 : ℤ) = (f : ℤ) * z := by
    exact_mod_cast hzval
  have hfd : (f : ℤ) ∣ (1 : ℤ) := ⟨z, hzint⟩
  have hfdn : f ∣ 1 := Int.natCast_dvd_natCast.mp hfd
  have hf_one : f = 1 := Nat.dvd_one.mp hfdn
  omega

/- In the totally tamely ramified comparison, the first positive unit layer is
   surjective; the same lifting argument is iterated for deeper layers. -/
theorem chapter11_tame_total_comparison_principal_units_are_norms
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (he : 0 < e) (htame : chapter11TameAtResidueCharacteristic e p)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL) :
    Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1) := by
  exact proposition_11_2_tame_totally_ramified_principal_unit_norm_surjective K L k vK vL ρK ρL e p he
    htame hext hscale hres hdegree hred hcompleteK hcompleteL

/- The elementary residue-unit obstruction for the tame total extension is
   exactly the `e`th-power condition, of order `gcd(e,q-1)` over `F_q`. -/
theorem chapter11_tame_total_comparison_residue_obstruction
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (he : 0 < e) (htame : chapter11TameAtResidueCharacteristic e p)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k k vK vL ρK ρL e N)
    (hprincipal :
      Set.SurjOn (Algebra.norm K (S := L))
        (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1)) :
    chapter11NormImage K L vL 0 =
      chapter11ResidueConditionSet vK ρK
        (chapter11ResidueUnitPowerImage k e) := by
  exact proposition_11_2_tame_totally_ramified_all_unit_norm_image K L k vK vL ρK ρL e p he
    htame hext hscale hres hdegree hred hcompleteK hcompleteL N hnormunit hnormred hprincipal

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
