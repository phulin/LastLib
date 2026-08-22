import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section08ExplicitTameNormEquations
import Mathlib.Algebra.Field.ULift

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11

noncomputable section

/-! ## 11.9. Trace versus norm on the first layer

The first residue layer has an additive map for trace and a multiplicative
power map for norm.  The two maps are recorded separately so that tame
invertibility of the scalar `e` is not confused with surjectivity of the
`e`th-power map.
-/

/- Multiplication by the ramification degree on the additive residue field. -/
def chapter11TameFirstLayerAdditiveMap
    (k : Type*) [Field k] (e : ℕ) : k →+ k where
  toFun x := (e : k) * x
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

/- The multiplicative first-layer map is the power homomorphism from §11.4. -/
abbrev chapter11TameFirstLayerMultiplicativeMap
    (k : Type*) [Field k] (e : ℕ) : kˣ →* kˣ :=
  chapter11PowerMap k e

/- The simultaneous residue condition whose automatic validity requires finite
   residue fields. -/
def chapter11ResidueNormTraceSurjectivity
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] : Prop :=
  Function.Surjective (Algebra.trace k l) ∧
    Function.Surjective (Algebra.norm k (S := l))

/- The totally ramified trace formula on the first layer. -/
theorem chapter11_tame_total_first_layer_trace_formula
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

/- The totally ramified norm formula on residue units. -/
theorem chapter11_tame_total_first_layer_norm_formula
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

/- In the unramified case the reductions of trace and norm are the residue
   trace and residue norm, respectively. -/
theorem chapter11_unramified_first_layer_trace_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (hdegree : Module.finrank K L =
      Module.finrank (chapter11ResidueField vK) (chapter11ResidueField vL))
    (hred : chapter11ResidueReductionCompatible vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL))
    (T : chapter11ValuationRing vL →+ chapter11ValuationRing vK)
    (htrace : chapter11TraceLiftCompatibility K L vK vL T)
    (htracered : chapter11TraceResidueCompatibility K L
      (chapter11ResidueField vK) (chapter11ResidueField vL) vK vL
      (chapter11ResidueMap vK) (chapter11ResidueMap vL) 1 T)
    (x : chapter11ValuationRing vL) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.trace K L (x : L) ∧
        chapter11ResidueMap vK y =
          Algebra.trace (chapter11ResidueField vK) (chapter11ResidueField vL)
            (chapter11ResidueMap vL x) := by
  have hunused := And.intro hunram (And.intro hdegree hred)
  clear hunused
  exact ⟨T x, htrace x, by simpa using htracered x⟩

theorem chapter11_unramified_first_layer_norm_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
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
      (chapter11ResidueMap vK) (chapter11ResidueMap vL) 1 N)
    (u : chapter11ValuationRing vL) (hu : IsUnit u) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.norm K (u : L) ∧
        chapter11ResidueMap vK y =
          Algebra.norm (chapter11ResidueField vK)
            (chapter11ResidueMap vL u) := by
  have hunused := And.intro hunram (And.intro hdegree hred)
  clear hunused
  have hnormvalue :
      ((N hu.unit : chapter11ValuationRing vK) : K) = Algebra.norm K (u : L) := by
    rw [hnormunit, hu.unit_spec]
  have hresvalue :
      chapter11ResidueMap vK (N hu.unit : chapter11ValuationRing vK) =
        Algebra.norm (chapter11ResidueField vK)
          (chapter11ResidueMap vL u) := by
    have h := hnormred hu.unit
    simpa only [hu.unit_spec, pow_one] using h
  exact ⟨(N hu.unit : chapter11ValuationRing vK), hnormvalue, hresvalue⟩

/- Over finite fields, trace is surjective as a nonzero linear map and norm is
   surjective as the exponent map on a cyclic multiplicative group. -/
theorem chapter11_finite_residue_trace_norm_simultaneously_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Finite l] [FiniteDimensional k l] :
    chapter11ResidueNormTraceSurjectivity k l := by
  rcases chapter11_finite_residue_norm_and_trace_surjective k l with
    ⟨hnorm, htrace⟩
  exact ⟨htrace, hnorm⟩

/- Tame invertibility makes the additive first-layer map onto even when the
   multiplicative power map is not. -/
theorem chapter11_tame_first_layer_additive_multiplicative_asymmetry
    (k : Type*) [Field k] (e : ℕ) (he : (e : k) ≠ 0)
    (hpower : ¬Function.Surjective (chapter11TameFirstLayerMultiplicativeMap k e)) :
    Function.Surjective (chapter11TameFirstLayerAdditiveMap k e) ∧
      ¬Function.Surjective (chapter11TameFirstLayerMultiplicativeMap k e) := by
  have hadd : Function.Surjective (chapter11TameFirstLayerAdditiveMap k e) := by
    intro x
    exact ⟨(e : k)⁻¹ * x, by
      simp [chapter11TameFirstLayerAdditiveMap, he]⟩
  exact ⟨hadd, hpower⟩

/- Unramifiedness alone does not force residue norm surjectivity over arbitrary
   residue fields; finiteness (or another explicit residue hypothesis) is an
   independent input to the simultaneous first-layer lifting argument. -/
theorem chapter11_residue_norm_surjectivity_not_formal_for_arbitrary_fields :
    ¬ (∀ (k l : Type*) [Field k] [Field l] [Algebra k l]
      [FiniteDimensional k l] [Algebra.IsSeparable k l],
      Function.Surjective (Algebra.norm k (S := l))) := by
  intro h
  let k := ULift ℝ
  let l := ULift ℂ
  let : Algebra k ℂ := by
    dsimp [k]
    exact ULift.algebra' ℝ ℂ
  let : Algebra k l := by
    dsimp [k, l]
    exact ULift.algebra
  let b : Module.Basis (Fin 2) k ℂ :=
    Complex.basisOneI.mapCoeffs (ULift.ringEquiv.symm) (by
      intro c x
      rfl)
  let : FiniteDimensional k ℂ := b.finiteDimensional_of_finite
  let : FiniteDimensional k l :=
    (ULift.moduleEquiv (R := k) (M := ℂ)).symm.finiteDimensional
  let : CharZero k := ⟨by
    intro m n hmn
    apply (Nat.cast_injective : Function.Injective (Nat.cast : ℕ → ℝ))
    exact congr_arg ULift.down hmn⟩
  let : Algebra.IsIntegral k l :=
    ⟨fun x => IsIntegral.of_finite k x⟩
  let : Algebra.IsSeparable k l :=
    Algebra.IsSeparable.of_integral (F := k) (K := l)
  have hs := h k l
  obtain ⟨z, hz⟩ := hs (-1 : k)
  have he :
      RingHom.comp (algebraMap ℝ ℂ)
          (ULift.ringEquiv (R := ℝ) : k →+* ℝ) =
        RingHom.comp (ULift.ringEquiv (R := ℂ) : l →+* ℂ)
          (algebraMap k l) := by
    ext x
    rfl
  have hnorm := Algebra.norm_eq_of_equiv_equiv
    (ULift.ringEquiv (R := ℝ) : k ≃+* ℝ)
    (ULift.ringEquiv (R := ℂ) : l ≃+* ℂ) he z
  have hneg :
      (ULift.ringEquiv (R := ℝ)).symm
          (Algebra.norm ℝ ((ULift.ringEquiv (R := ℂ)) z)) = (-1 : k) :=
    hnorm.symm.trans hz
  have hnorm_complex :
      Algebra.norm ℝ ((ULift.ringEquiv (R := ℂ)) z) = (-1 : ℝ) := by
    simpa using congr_arg (ULift.ringEquiv (R := ℝ)) hneg
  rw [Algebra.norm_complex_apply] at hnorm_complex
  linarith [Complex.normSq_nonneg ((ULift.ringEquiv (R := ℂ)) z)]

/- The higher-unit profile remains the data needed after a first-layer
   calculation; the source deliberately makes no claim that `e` and `f` alone
   determine it in wild ramification. -/
def chapter11FirstLayerLiftingData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ)) : Prop :=
  ∀ n : ℕ, Set.SurjOn (Algebra.norm K (S := L))
    (chapter11UnitFiltration vL (n + 1))
    (chapter11UnitFiltration vK (n + 1))

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
