import LastLib.Book04AdelesAndIdeles.Chapter10.Dependencies

namespace LastLib.Book04AdelesAndIdeles.Chapter10

noncomputable section

open scoped BigOperators

/-! ## 10.1. The local norm as a multiplicative determinant -/

/-- Multiplication by `y` as an `F`-linear endomorphism of `E`. -/
def chapter10MultiplicationLinearMap
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (y : E) : E →ₗ[F] E :=
  Algebra.lmul F E y

@[simp]
theorem chapter10MultiplicationLinearMap_apply
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (y z : E) :
    chapter10MultiplicationLinearMap F E y z = y * z := by
  rfl

/-- The determinant definition of the local field norm. -/
theorem chapter10_local_norm_is_multiplicative_determinant
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (y : E) :
    chapter10LocalNorm F E y =
      LinearMap.det (chapter10MultiplicationLinearMap F E y) := by
  rfl

theorem chapter10_local_norm_mul
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (y z : E) :
    chapter10LocalNorm F E (y * z) =
      chapter10LocalNorm F E y * chapter10LocalNorm F E z := by
  exact (chapter10LocalNorm F E).map_mul y z

theorem chapter10_local_norm_one
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] :
    chapter10LocalNorm F E 1 = 1 := by
  exact (chapter10LocalNorm F E).map_one

theorem chapter10_local_norm_eq_zero_iff
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (y : E) :
    chapter10LocalNorm F E y = 0 ↔ y = 0 := by
  exact Algebra.norm_eq_zero_iff

theorem chapter10_local_norm_transitive
    (F M E : Type*) [Field F] [Field M] [Field E]
    [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E]
    [FiniteDimensional F M] [FiniteDimensional M E] [FiniteDimensional F E]
    (y : E) :
    chapter10LocalNorm F E y =
      chapter10LocalNorm F M (chapter10LocalNorm M E y) := by
  sorry

/- The valuation-side interface used below is the normalized branch formula
from the preceding local-field chapters. -/
def chapter10UnramifiedLocalExtension
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ)) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedValuedExtension
    vF vE

def chapter10NormalizedUniformizer {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) (π : F) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11IsUniformizer v π

theorem chapter10_normalized_uniformizer_ne_zero
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ)) (π : F)
    (hπ : chapter10NormalizedUniformizer v π) : π ≠ 0 :=
  hπ.1

theorem chapter10_normalized_uniformizer_value
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ)) (π : F)
    (hπ : chapter10NormalizedUniformizer v π) : v π = (1 : WithTop ℤ) :=
  hπ.2.1

theorem chapter10_local_norm_maps_integers
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (f : ℕ) (hformula : chapter10NormValuationFormula F E vF vE f) :
    Set.MapsTo (chapter10LocalNorm F E)
      (chapter10LocalIntegerSet vE) (chapter10LocalIntegerSet vF) := by
  sorry

theorem chapter10_local_norm_maps_units
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (f : ℕ) (hformula : chapter10NormValuationFormula F E vF vE f) :
    Set.MapsTo (chapter10LocalNorm F E)
      (chapter10LocalUnitSet vE) (chapter10LocalUnitSet vF) := by
  sorry

theorem chapter10_local_norm_valuation_formula
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {vF : AddValuation F (WithTop ℤ)}
    {vE : AddValuation E (WithTop ℤ)} (e f : ℕ)
    [Valuation.IsRankOneDiscrete vF.toValuation]
    [Valuation.IsRankOneDiscrete vE.toValuation]
    (hext : vF.IsEquiv (AddValuation.comap (algebraMap F E) vE))
    (hrestrict : ∀ y : F,
      vE (algebraMap F E y) = (e : WithTop ℤ) * vF y)
    (hf : f =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vF vE hext)
    (hunique : ∀ w : AddValuation E (WithTop ℤ),
      vF.IsEquiv (AddValuation.comap (algebraMap F E) w) → vE.IsEquiv w)
    (hdegree : Module.finrank F E = e * f) :
    chapter10NormValuationFormula F E vF vE f := by
  sorry

theorem chapter10_unramified_norm_valuation
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (d : ℕ) (hunram : chapter10UnramifiedLocalExtension vF vE)
    (hdegree : Module.finrank F E = d)
    (hunique : ∀ w : AddValuation E (WithTop ℤ),
      vF.IsEquiv (AddValuation.comap (algebraMap F E) w) → vE.IsEquiv w)
    (hfres : d =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vF vE hunram.1) :
    chapter10NormValuationFormula F E vF vE d := by
  sorry

theorem chapter10_unramified_uniformizer_norm
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (d : ℕ) (_hunram : chapter10UnramifiedLocalExtension vF vE)
    (πF : F) (_hπF : chapter10NormalizedUniformizer vF πF)
    (hdegree : Module.finrank F E = d) :
    chapter10LocalNorm F E (algebraMap F E πF) = πF ^ d := by
  sorry

/-- The target `π_F^{dℤ} O_Fˣ` in the unramified norm lemma. -/
def chapter10UnramifiedNormTarget {F : Type*} [Field F]
    (vF : AddValuation F (WithTop ℤ)) (πF : F) (d : ℕ)
    (_hπF : chapter10NormalizedUniformizer vF πF) : Set F :=
  {x | ∃ z : ℤ, ∃ u : F,
    u ∈ chapter10LocalUnitSet vF ∧
      x = πF ^ ((d : ℤ) * z) * u}

theorem chapter10_mem_unramified_norm_target_iff
    {F : Type*} [Field F] (vF : AddValuation F (WithTop ℤ))
    (πF : F) (d : ℕ) (hπF : chapter10NormalizedUniformizer vF πF) (x : F) :
    x ∈ chapter10UnramifiedNormTarget vF πF d hπF ↔
      ∃ z : ℤ, ∃ u : F,
        u ∈ chapter10LocalUnitSet vF ∧
          x = πF ^ ((d : ℤ) * z) * u := Iff.rfl

/-! The finite-residue proof interfaces used in Lemma 10.1. -/

abbrev chapter10ResidueField {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) : Type _ :=
  IsLocalRing.ResidueField (chapter10ValuationRing v)

def chapter10ResidueMap {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) :
    chapter10ValuationRing v →+* chapter10ResidueField v :=
  IsLocalRing.residue (chapter10ValuationRing v)

def chapter10ValuationCongruence {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) (n : ℕ) (x y : F) : Prop :=
  v (x - y) ≥ (n : WithTop ℤ)

theorem chapter10_mem_valuation_congruence_iff
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (n : ℕ) (x y : F) :
    chapter10ValuationCongruence v n x y ↔
      v (x - y) ≥ (n : WithTop ℤ) := Iff.rfl

theorem chapter10_finite_residue_norm_is_exponent_map
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Finite l] [FiniteDimensional k l] (x : l) :
    algebraMap k l (Algebra.norm k x) =
      x ^ ((Nat.card l - 1) / (Nat.card k - 1)) := by
  sorry

theorem chapter10_finite_residue_norm_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Finite l] [FiniteDimensional k l] :
    Function.Surjective (Algebra.norm k (S := l)) := by
  sorry

theorem chapter10_finite_residue_trace_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Algebra.IsSeparable k l] :
    Function.Surjective (Algebra.trace k l) := by
  sorry

theorem chapter10_unramified_norm_first_layer_congruence
    (F E k l : Type*) [Field F] [Field E] [Field k] [Field l]
    [Algebra F E] [Algebra k l] [FiniteDimensional F E]
    [FiniteDimensional k l] [Algebra.IsSeparable k l]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (hunram : chapter10UnramifiedLocalExtension vF vE)
    (ρF : chapter10ValuationRing vF →+* k)
    (ρE : chapter10ValuationRing vE →+* l)
    (hred :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueReductionCompatible
        vF vE ρF ρE)
    (hdegree : Module.finrank F E = Module.finrank k l)
    (hnorm : chapter10NormValuationFormula F E vF vE (Module.finrank k l))
    (n : ℕ) (hn : 1 ≤ n) (a : chapter10ValuationRing vE)
    (πF : F) (πE : E)
    (hπF : chapter10NormalizedUniformizer vF πF)
    (hπE : chapter10NormalizedUniformizer vE πE)
    (hπ : πE = algebraMap F E πF)
    (T : chapter10ValuationRing vE →+ chapter10ValuationRing vF)
    (htrace :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11TraceLiftCompatibility
        F E vF vE T)
    (htracered :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11TraceResidueCompatibility
        F E k l vF vE ρF ρE 1 T) :
    ∃ c : chapter10ValuationRing vF,
      ρF c = Algebra.trace k l (ρE a) ∧
        chapter10ValuationCongruence vF (n + 1)
          (chapter10LocalNorm F E (1 + (a : E) * πE ^ n))
          (1 + (c : F) * πF ^ n) := by
  sorry

theorem lemma_10_1_norms_in_an_unramified_extension
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (d : ℕ) (hunram : chapter10UnramifiedLocalExtension vF vE)
    (hdegree : Module.finrank F E = d)
    (πF : F) (hπF : chapter10NormalizedUniformizer vF πF)
    (hnorm : chapter10NormValuationFormula F E vF vE d)
    (hfres : d =
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter11.chapter11AdditiveResidueDegree
        vF vE hunram.1)
    [Finite (chapter10ResidueField vF)]
    [Algebra (chapter10ResidueField vF) (chapter10ResidueField vE)]
    [FiniteDimensional (chapter10ResidueField vF) (chapter10ResidueField vE)]
    [Algebra.IsSeparable (chapter10ResidueField vF) (chapter10ResidueField vE)]
    (hred :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueReductionCompatible
        vF vE (chapter10ResidueMap vF) (chapter10ResidueMap vE))
    (N : (chapter10ValuationRing vE)ˣ →* (chapter10ValuationRing vF)ˣ)
    (hnormunit :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormUnitLiftCompatibility
        F E vF vE N)
    (hnormred :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormResidueCompatibility
        F E (chapter10ResidueField vF) (chapter10ResidueField vE) vF vE
          (chapter10ResidueMap vF) (chapter10ResidueMap vE) 1 N) :
    chapter10ValuationUnitNormImage F E vE = chapter10LocalUnitSet vF ∧
      chapter10LocalNormImage F E = chapter10UnramifiedNormTarget vF πF d hπF := by
  sorry

/-! The norm is continuous; the local-field topology supplies the topology on
the source and target, while finite-dimensionality supplies continuity of the
determinant polynomial. -/
theorem chapter10_local_norm_continuous
    (F E : Type*) [NontriviallyNormedField F] [CompleteSpace F] [NormedField E]
    [NormedAlgebra F E]
    [FiniteDimensional F E] :
    Continuous (chapter10LocalNorm F E) := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter10
