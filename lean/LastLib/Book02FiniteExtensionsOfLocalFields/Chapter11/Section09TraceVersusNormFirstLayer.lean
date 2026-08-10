import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section08ExplicitTameNormEquations

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
    (k l : Type*) [Field k] [Field l] [Algebra k l] : Prop :=
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
    (x : chapter11ValuationRing vL) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.trace K L (x : L) ∧
        ρK y = (e : k) * ρL x := by
  exact chapter11_totally_ramified_trace_residue_formula
    K L k vK vL ρK ρL e hext hscale hres x

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
    (u : chapter11ValuationRing vL) (hu : IsUnit u) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.norm K (u : L) ∧ ρK y = (ρL u) ^ e := by
  exact chapter11_totally_ramified_norm_residue_formula
    K L k vK vL ρK ρL e hext hscale hres u hu

/- In the unramified case the reductions of trace and norm are the residue
   trace and residue norm, respectively. -/
theorem chapter11_unramified_first_layer_trace_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (x : chapter11ValuationRing vL) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.trace K L (x : L) ∧
        chapter11ResidueMap vK y =
          Algebra.trace (chapter11ResidueField vK) (chapter11ResidueField vL)
            (chapter11ResidueMap vL x) := by
  sorry

theorem chapter11_unramified_first_layer_norm_formula
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ))
    (hunram : chapter11UnramifiedValuedExtension vK vL)
    [Algebra (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [FiniteDimensional (chapter11ResidueField vK) (chapter11ResidueField vL)]
    [Algebra.IsSeparable (chapter11ResidueField vK) (chapter11ResidueField vL)]
    (u : chapter11ValuationRing vL) (hu : IsUnit u) :
    ∃ y : chapter11ValuationRing vK,
      (y : K) = Algebra.norm K (u : L) ∧
        chapter11ResidueMap vK y =
          Algebra.norm (chapter11ResidueField vK)
            (chapter11ResidueMap vL u) := by
  sorry

/- Over finite fields, trace is surjective as a nonzero linear map and norm is
   surjective as the exponent map on a cyclic multiplicative group. -/
theorem chapter11_finite_residue_trace_norm_simultaneously_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Finite l] [FiniteDimensional k l] :
    chapter11ResidueNormTraceSurjectivity k l := by
  exact chapter11_finite_residue_norm_and_trace_surjective k l |>.symm

/- Tame invertibility makes the additive first-layer map onto even when the
   multiplicative power map is not. -/
theorem chapter11_tame_first_layer_additive_multiplicative_asymmetry
    (k : Type*) [Field k] (e : ℕ) (he : (e : k) ≠ 0)
    (hpower : ¬Function.Surjective (chapter11TameFirstLayerMultiplicativeMap k e)) :
    Function.Surjective (chapter11TameFirstLayerAdditiveMap k e) ∧
      ¬Function.Surjective (chapter11TameFirstLayerMultiplicativeMap k e) := by
  sorry

/- Unramifiedness alone does not force residue norm surjectivity over arbitrary
   residue fields; finiteness (or another explicit residue hypothesis) is an
   independent input to the simultaneous first-layer lifting argument. -/
theorem chapter11_residue_norm_surjectivity_not_formal_for_arbitrary_fields :
    ¬ (∀ (k l : Type*) [Field k] [Field l] [Algebra k l]
      [FiniteDimensional k l] [Algebra.IsSeparable k l],
      Function.Surjective (Algebra.norm k (S := l))) := by
  sorry

/- The higher-unit profile remains the data needed after a first-layer
   calculation; the source deliberately makes no claim that `e` and `f` alone
   determine it in wild ramification. -/
def chapter11FirstLayerLiftingData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    (vK : AddValuation K (WithTop ℤ)) (vL : AddValuation L (WithTop ℤ)) : Prop :=
  ∀ n : ℕ, Set.SurjOn (Algebra.norm K (S := L))
    (chapter11UnitFiltration vL (n + 1))
    (chapter11UnitFiltration vK (n + 1))

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11
