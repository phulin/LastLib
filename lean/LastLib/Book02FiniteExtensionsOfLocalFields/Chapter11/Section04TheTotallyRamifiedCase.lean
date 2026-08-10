import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section03TheUnramifiedCase

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

open Ideal IsLocalRing

/-! ## 11.4. The totally ramified case -/

/- Total ramification is recorded by the exact valuation scaling and an
   explicit agreement of residue fields; the field-degree equality is kept as
   a separate hypothesis where it is needed. -/
def chapter11TotallyRamifiedResidueAgreement
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ)) : Prop :=
  Nonempty (chapter11ResidueField vL ≃+* chapter11ResidueField vK)

def chapter11TameAtResidueCharacteristic (e p : ℕ) : Prop :=
  Nat.Coprime e p

def chapter11WildAtResidueCharacteristic (e p : ℕ) : Prop :=
  ¬chapter11TameAtResidueCharacteristic e p

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
    (x : chapter11ValuationRing vL) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.trace K L (x : L) ∧
        ρK y = (e : k) * ρL x := by
  sorry

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
    (u : chapter11ValuationRing vL) (hu : IsUnit u) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.norm K (u : L) ∧ ρK y = (ρL u) ^ e := by
  sorry

/- With normalized valuations and residue degree one, the norm of an
   extension uniformizer has base valuation one. -/
-- STATEMENT_NEEDS_UPDATE: The hypotheses record one chosen valuation branch and
-- the residue degree, but they do not supply uniqueness of the normalized
-- extension or a norm-valuation formula.  Add that uniqueness/norm
-- compatibility (or the corresponding complete defectless hypotheses) before
-- asserting the valuation of the norm of `πL`.
theorem chapter11_totally_ramified_norm_of_uniformizer
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (e : ℕ) (he : 0 < e)
    (hext : chapter11ValuationExtension vK vL)
    (hscale : chapter11ValuationScaling vK vL e)
    (hres : chapter11TotallyRamifiedResidueAgreement vK vL)
    (hdegree : Module.finrank K L = e)
    (hfres :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vK vL hext = 1)
    (πL : L) (hπ : chapter11IsUniformizer vL πL) :
    vK (Algebra.norm K πL) = (1 : WithTop ℤ) := by
  sorry

/- Tameness makes multiplication by `e` invertible on the residue field. -/
theorem chapter11_tame_residue_scalar_is_nonzero
    (k : Type*) [Field k] (e p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (htame : chapter11TameAtResidueCharacteristic e p) :
    (e : k) ≠ 0 := by
  intro hezero
  have hpdiv : p ∣ e := (CharP.cast_eq_zero_iff k p e).mp hezero
  exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp htame.symm) hpdiv

/- A power profile keeps track of the higher unit information which is not
   determined by `e` and the residue degree in the wild case. -/
def chapter11HigherUnitNormProfile
    (K L : Type*) [Field K] [Field L] [Algebra K L]
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

theorem chapter11_tame_residue_power_quotient_index
    (k : Type*) [Field k] [Fintype k] (e : ℕ) :
    Nat.card (kˣ ⧸ chapter11PowerSubgroup k e) =
      Nat.gcd e (Fintype.card k - 1) := by
  classical
  have hmap : chapter11PowerMap k e = (powMonoidHom e : kˣ →* kˣ) := by
    ext u
    rfl
  change Nat.card (kˣ ⧸ Subgroup.map (chapter11PowerMap k e) ⊤) = _
  rw [← (chapter11PowerMap k e).range_eq_map,
    ← (chapter11PowerMap k e).range.index_eq_card, hmap]
  simpa [Nat.card_units, Nat.card_eq_fintype_card, Nat.gcd_comm] using
    (IsCyclic.index_powMonoidHom_range (G := kˣ) e)

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
