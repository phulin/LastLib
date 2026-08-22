import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section03TheUnramifiedCase
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section04MultiplicationPowersAndResidueCharacteristic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open Ideal IsLocalRing

/-! ## 11.4. The totally ramified case -/

/- Total ramification is recorded by the canonical residue-degree-one
   invariant attached to the chosen valuation branch; the field-degree
   equality is kept as a separate hypothesis where it is needed. -/
def chapter11TotallyRamifiedResidueAgreement
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ)) : Prop :=
  chapter11ValuationExtension vK vL ∧
    ∀ hext : chapter11ValuationExtension vK vL,
      letI : Valuation.HasExtension vK.toValuation vL.toValuation := ⟨hext⟩
      Nonempty
        (chapter11ResidueField vL ≃ₐ[chapter11ResidueField vK]
          chapter11ResidueField vK)

def chapter11TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  Nat.Coprime e p

def chapter11WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  ¬chapter11TameAtResidueCharacteristic e p

theorem chapter11_wild_at_residue_characteristic_iff_prime_dvd
    (e p : ℕ) [Fact (Nat.Prime p)] :
    chapter11WildAtResidueCharacteristic e p ↔ p ∣ e := by
  unfold chapter11WildAtResidueCharacteristic chapter11TameAtResidueCharacteristic
  constructor
  · intro h
    by_contra hdiv
    exact h ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hdiv).symm
  · intro hdiv hc
    exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hc.symm) hdiv

/- The residue formula for trace in a totally ramified extension. -/
theorem chapter11_totally_ramified_trace_residue_formula
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ) (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (T : chapter11ValuationRing vL →+ chapter11ValuationRing vK)
    (htrace : chapter11TraceLiftCompatibility K L vK vL T)
    (htracered : chapter11TraceResidueScalarCompatibility K L k vK vL ρK ρL e T)
    (x : chapter11ValuationRing vL) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.trace K L (x : L) ∧
        ρK y = (e : k) * ρL x := by
  have hunused := And.intro hext (And.intro hscale (And.intro hres
    (And.intro hdegree (And.intro hred (And.intro hcompleteK hcompleteL)))))
  clear hunused
  exact ⟨T x, htrace x, htracered x⟩

/- The residue formula for norm on a totally ramified residue unit. -/
theorem chapter11_totally_ramified_norm_residue_formula
    (K L k : Type*) [Field K] [Field L] [Field k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ) (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL)
    (N : (chapter11ValuationRing vL)ˣ →* (chapter11ValuationRing vK)ˣ)
    (hnormunit : chapter11NormUnitLiftCompatibility K L vK vL N)
    (hnormred : chapter11NormResidueCompatibility K L k k vK vL ρK ρL e N)
    (u : chapter11ValuationRing vL) (hu : IsUnit u) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.norm K (u : L) ∧ ρK y = (ρL u) ^ e := by
  have hunused := And.intro hext (And.intro hscale (And.intro hres
    (And.intro hdegree (And.intro hred (And.intro hcompleteK hcompleteL)))))
  clear hunused
  have hnormvalue :
      ((N hu.unit : chapter11ValuationRing vK) : K) = Algebra.norm K (u : L) := by
    rw [hnormunit, hu.unit_spec]
  have hresvalue :
      ρK (N hu.unit : chapter11ValuationRing vK) = (ρL u) ^ e := by
    rw [hnormred, hu.unit_spec]
    simp
  exact ⟨(N hu.unit : chapter11ValuationRing vK), hnormvalue, hresvalue⟩

/- With normalized valuations and residue degree one, the norm of an
   extension uniformizer has base valuation one. -/
-- SOURCE_ISSUE: The source suppresses the norm-valuation compatibility of the
-- chosen branch.  The explicit hypothesis below is the minimal interface
-- needed until the canonical defectless norm theorem is available here.
theorem chapter11_totally_ramified_norm_of_uniformizer
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (πL : L) (hπ : chapter11IsUniformizer vL πL)
    (hnorm : chapter11NormValuationFormula K L vK vL 1) :
    vK (Algebra.norm K πL) = (1 : WithTop ℤ) := by
  rw [hnorm πL hπ.1, hπ.2.1]
  simp

/- Tameness makes multiplication by `e` invertible on the residue field. -/
theorem chapter11_tame_residue_scalar_is_nonzero
    (k : Type*) [Field k] (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (htame : chapter11TameAtResidueCharacteristic e p) :
    (e : k) ≠ 0 := by
  intro he
  have hdiv : p ∣ e := (CharP.cast_eq_zero_iff k p e).mp he
  exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp htame.symm) hdiv

theorem chapter11_wild_residue_scalar_is_zero
    (k : Type*) [Field k] (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hwild : chapter11WildAtResidueCharacteristic e p) :
    (e : k) = 0 := by
  sorry

/- A power profile keeps track of the higher unit information which is not
   determined by `e` and the residue degree in the wild case. -/
def chapter11HigherUnitNormProfile
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vL : AddValuation L (WithTop ℤ)) : ℕ → Set K :=
  fun n => chapter11NormImage K L vL n

/- Proposition 11.2: tame total ramification gives surjectivity on principal
   units. -/
theorem proposition_11_2_tame_totally_ramified_principal_unit_norm_surjective
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
  sorry

/- Residue characteristic zero has characteristic exponent one, so every
   positive ramification degree is tame and the same principal-unit argument
   applies without a positive-characteristic `Fact` or `CharP` instance. -/
theorem proposition_11_2_char_zero_totally_ramified_principal_unit_norm_surjective
    (K L k : Type*) [Field K] [Field L] [Field k] [CharZero k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hred : chapter11ResidueReductionCompatible vK vL ρK ρL)
    (hcompleteK : chapter11ValuationComplete vK)
    (hcompleteL : chapter11ValuationComplete vL) :
    Set.SurjOn (Algebra.norm K (S := L))
      (chapter11UnitFiltration vL 1) (chapter11UnitFiltration vK 1) := by
  sorry

/- The image on all units is the inverse image of the `e`th-power subgroup
   in the common residue field. -/
theorem proposition_11_2_tame_totally_ramified_all_unit_norm_image
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
  sorry

/- The same all-unit image description in residue characteristic zero. -/
theorem proposition_11_2_char_zero_totally_ramified_all_unit_norm_image
    (K L k : Type*) [Field K] [Field L] [Field k] [CharZero k]
    [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (ρK : chapter11ValuationRing vK →+* k)
    (ρL : chapter11ValuationRing vL →+* k)
    (e : ℕ) (he : 0 < e)
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
  sorry

/- The elementary residue obstruction has the finite-field index shown in the
   source. -/
def chapter11PowerMap (k : Type*) [Field k] (e : ℕ) : kˣ →* kˣ where
  toFun u := u ^ e
  map_one' := by simp
  map_mul' := by intro u v; simp [mul_pow]

def chapter11PowerSubgroup (k : Type*) [Field k] (e : ℕ) : Subgroup kˣ :=
  Subgroup.map (chapter11PowerMap k e) ⊤

theorem chapter11_mem_power_subgroup_iff
    (k : Type*) [Field k] (e : ℕ) (u : kˣ) :
    u ∈ chapter11PowerSubgroup k e ↔ ∃ z : kˣ, z ^ e = u := by
  sorry

theorem chapter11_tame_residue_power_quotient_index
    (k : Type*) [Field k] [Fintype k] (e : ℕ) :
    Nat.card (kˣ ⧸ chapter11PowerSubgroup k e) =
      Nat.gcd e (Fintype.card k - 1) := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
