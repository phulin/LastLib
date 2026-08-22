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
  exact (Algebra.norm_norm (R := F) (S := M) (A := E) (a := y)).symm

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
  intro y hy
  unfold chapter10LocalIntegerSet at hy ⊢
  apply (Valuation.mem_valuationSubring_iff vF.toValuation _).2
  have hyval : 0 ≤ vE y := by
    have hyval' := (Valuation.mem_valuationSubring_iff vE.toValuation y).mp hy
    change Multiplicative.ofAdd (OrderDual.toDual (vE y)) ≤
      Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ)) at hyval'
    rw [Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual] at hyval'
    exact hyval'
  by_cases hy0 : y = 0
  · subst y
    have hnormzero : chapter10LocalNorm F E (0 : E) = 0 := by
      change Algebra.norm F (0 : E) = 0
      exact Algebra.norm_zero
    rw [hnormzero]
    change Multiplicative.ofAdd (OrderDual.toDual (vF 0)) ≤
      Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ))
    rw [AddValuation.map_zero]
    exact zero_le_one
  · change Multiplicative.ofAdd
      (OrderDual.toDual (vF (chapter10LocalNorm F E y))) ≤
      Multiplicative.ofAdd (OrderDual.toDual (0 : WithTop ℤ))
    rw [hformula y hy0, Multiplicative.ofAdd_le, OrderDual.toDual_le_toDual]
    cases hv : vE y with
    | top =>
      cases f with
      | zero => simp
      | succ n =>
        rw [WithTop.mul_top]
        · exact le_top
        · exact ne_of_gt (by positivity)
    | coe z =>
      rw [hv] at hyval
      have hz : (0 : ℤ) ≤ z := by exact_mod_cast hyval
      have hprod : (0 : ℤ) ≤ (f : ℤ) * z :=
        mul_nonneg (by exact_mod_cast Nat.zero_le f) hz
      change (0 : WithTop ℤ) ≤ ((f : ℤ) : WithTop ℤ) * (z : WithTop ℤ)
      rw [← WithTop.coe_mul]
      exact_mod_cast hprod

theorem chapter10_local_norm_maps_units
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (f : ℕ) (hformula : chapter10NormValuationFormula F E vF vE f) :
    Set.MapsTo (chapter10LocalNorm F E)
      (chapter10LocalUnitSet vE) (chapter10LocalUnitSet vF) := by
  intro y hy
  apply (chapter10_mem_local_unit_set_iff vF _).2
  have hy0 : y ≠ 0 := by
    intro hy0
    subst y
    have hval : vE (0 : E) = 0 :=
      (chapter10_mem_local_unit_set_iff vE (0 : E)).mp hy
    simp at hval
  rw [hformula y hy0, (chapter10_mem_local_unit_set_iff vE y).mp hy, mul_zero]

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
  intro y hy
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_norm_valuation_formula
    F E e f hext hrestrict hf hunique hdegree y hy

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
  have hdiscF :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vF :=
    hunram.2.2.1.1
  have hdiscE :
      LastLib.Book01ValuationsDVRsAndCompletions.Chapter10.Chapter10DiscreteAddValuation vE :=
    hunram.2.2.2.1.1
  let hrankF :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      vF hdiscF
  let hrankE :=
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter08.chapter08_rank_one_discrete_of_add_valuation
      vE hdiscE
  let _ : Valuation.IsRankOneDiscrete vF.toValuation := hrankF
  let _ : Valuation.IsRankOneDiscrete vE.toValuation := hrankE
  intro y hy
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.chapter04_norm_valuation_formula
    F E 1 d hunram.1
      (show ∀ z : F, vE (algebraMap F E z) =
        (1 : WithTop ℤ) * vF z from hunram.2.1)
      hfres hunique (by simpa using hdegree) y hy

theorem chapter10_unramified_uniformizer_norm
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (d : ℕ) (_hunram : chapter10UnramifiedLocalExtension vF vE)
    (πF : F) (_hπF : chapter10NormalizedUniformizer vF πF)
    (hdegree : Module.finrank F E = d) :
    chapter10LocalNorm F E (algebraMap F E πF) = πF ^ d := by
  change Algebra.norm F (algebraMap F E πF) = πF ^ d
  rw [Algebra.norm_algebraMap, hdegree]

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
  exact FiniteField.algebraMap_norm_eq_pow

theorem chapter10_finite_residue_norm_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [Finite l] [FiniteDimensional k l] :
    Function.Surjective (Algebra.norm k (S := l)) := by
  exact FiniteField.norm_surjective k l

theorem chapter10_finite_residue_trace_surjective
    (k l : Type*) [Field k] [Field l] [Algebra k l]
    [FiniteDimensional k l] [Algebra.IsSeparable k l] :
    Function.Surjective (Algebra.trace k l) := by
  exact Algebra.trace_surjective k l

theorem chapter10_unramified_norm_first_layer_congruence
    (F E k l : Type*) [Field F] [Field E] [Field k] [Field l]
    [Algebra F E] [Algebra k l] [FiniteDimensional F E]
    [FiniteDimensional k l] [Algebra.IsSeparable k l]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (hunram : chapter10UnramifiedLocalExtension vF vE)
    (ρF : chapter10ValuationRing vF →+* k)
    (ρE : chapter10ValuationRing vE →+* l)
    (_hred :
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ResidueReductionCompatible
        vF vE ρF ρE)
    (_hdegree : Module.finrank F E = Module.finrank k l)
    (hnorm : chapter10NormValuationFormula F E vF vE (Module.finrank k l))
    (n : ℕ) (hn : 1 ≤ n) (a : chapter10ValuationRing vE)
    (πF : F) (πE : E)
    (_hπF : chapter10NormalizedUniformizer vF πF)
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
  rcases hπE with ⟨_, _, ⟨pE, hpE, hpEgen⟩⟩
  let mE := IsLocalRing.maximalIdeal (chapter10ValuationRing vE)
  have hpEmem : pE ∈ mE := by
    change pE ∈ IsLocalRing.maximalIdeal (chapter10ValuationRing vE)
    rw [hpEgen.2]
    exact Ideal.subset_span (by simp)
  have hxa : (a : E) * πE ^ n ∈
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValuationIdealPowerSet
        vE n := by
    apply
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_mem_valuation_ideal_power_set_iff
        vE n _).2
    refine ⟨a * pE ^ n, ?_, ?_⟩
    · exact Ideal.mul_mem_left _ a (Ideal.pow_mem_pow hpEmem n)
    · rw [← hpE]
      simp
  have hremval :
      vF (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormRemainder
        F E ((a : E) * πE ^ n)) ≥
        (2 : WithTop ℤ) * (n : WithTop ℤ) := by
    simpa [LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11CeilDiv] using
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_norm_remainder_has_depth
        F E vF vE 1 (Module.finrank k l) (by simp)
          hunram.1 hunram.2.1 hnorm hunram.2.2.1 hunram.2.2.2.1 n hn
          ((a : E) * πE ^ n) hxa)
  have h2n : ((n + 1 : ℕ) : WithTop ℤ) ≤
      (2 : WithTop ℤ) * (n : WithTop ℤ) := by
    have h2n_nat : n + 1 ≤ 2 * n := by omega
    have h2n_top : ((n + 1 : ℕ) : WithTop ℤ) ≤
        ((2 * n : ℕ) : WithTop ℤ) := by exact_mod_cast h2n_nat
    calc
      ((n + 1 : ℕ) : WithTop ℤ) ≤ ((2 * n : ℕ) : WithTop ℤ) := h2n_top
      _ = (2 : WithTop ℤ) * (n : WithTop ℤ) := by norm_cast
  have hremval' :
      vF (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormRemainder
        F E ((a : E) * πE ^ n)) ≥ ((n + 1 : ℕ) : WithTop ℤ) :=
    h2n.trans hremval
  let c : chapter10ValuationRing vF := T a
  have hcres : ρF c = Algebra.trace k l (ρE a) := by
    simpa [c] using htracered a
  refine ⟨c, hcres, ?_⟩
  have htrace_a : (c : F) = Algebra.trace F E (a : E) := by
    exact htrace a
  have htrace_x : Algebra.trace F E ((a : E) * πE ^ n) =
      (c : F) * πF ^ n := by
    calc
      Algebra.trace F E ((a : E) * πE ^ n) =
          Algebra.trace F E (algebraMap F E (πF ^ n) * (a : E)) := by
            rw [hπ, map_pow]
            ring_nf
      _ = Algebra.trace F E ((πF ^ n) • (a : E)) := by
            rw [Algebra.smul_def]
      _ = (πF ^ n) • Algebra.trace F E (a : E) := by
            exact (Algebra.trace F E).map_smul _ _
      _ = (c : F) * πF ^ n := by
            rw [htrace_a]
            simp [smul_eq_mul, mul_comm]
  have hnorm_exp : Algebra.norm F (1 + (a : E) * πE ^ n) =
      1 + (c : F) * πF ^ n +
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormRemainder
          F E ((a : E) * πE ^ n) := by
    calc
      Algebra.norm F (1 + (a : E) * πE ^ n) =
          1 + Algebra.trace F E ((a : E) * πE ^ n) +
            LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormRemainder
              F E ((a : E) * πE ^ n) :=
        LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_norm_one_add_linearizes_to_trace
          F E ((a : E) * πE ^ n)
      _ = 1 + (c : F) * πF ^ n +
            LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11NormRemainder
              F E ((a : E) * πE ^ n) := by
        rw [htrace_x]
  change vF (Algebra.norm F (1 + (a : E) * πE ^ n) -
      (1 + (c : F) * πF ^ n)) ≥ ((n + 1 : ℕ) : WithTop ℤ)
  rw [hnorm_exp]
  convert hremval' using 1
  ring_nf

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
  have hfull0 :
      {x : F | ∃ y : E, y ≠ 0 ∧ x = Algebra.norm F y} =
        chapter10UnramifiedNormTarget vF πF d hπF := by
    simpa [chapter10LocalNormImage, chapter10UnramifiedNormTarget,
      chapter10LocalNorm, chapter10LocalUnitSet,
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11ValueUnitProductSet,
      LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnitFiltration] using
      (LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_unramified_full_norm_image
        F E vF vE πF d hunram hπF hnorm hdegree hfres hred N hnormunit hnormred)
  have hfull : chapter10LocalNormImage F E =
      chapter10UnramifiedNormTarget vF πF d hπF := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Set.ext_iff.mp hfull0 _).1 ⟨y, hy, rfl⟩
    · intro hx
      rcases (Set.ext_iff.mp hfull0 _).2 hx with ⟨y, hy, hxy⟩
      exact ⟨y, hy, hxy.symm⟩
  refine ⟨?_, hfull⟩
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    apply (chapter10_mem_local_unit_set_iff vF x).2
    have hy0 : y ≠ 0 := by
      intro hy0
      subst y
      have hyval := (chapter10_mem_local_unit_set_iff vE (0 : E)).1 hy
      simp at hyval
    rw [← hxy, hnorm y hy0]
    simp [(chapter10_mem_local_unit_set_iff vE y).1 hy]
  · intro hx
    have hxfull : x ∈ chapter10LocalNormImage F E := by
      rw [hfull]
      exact ⟨0, x, hx, by simp⟩
    rcases hxfull with ⟨y, hy0, hxy⟩
    refine ⟨y, ?_, hxy⟩
    apply (chapter10_mem_local_unit_set_iff vE y).2
    have hxval := (chapter10_mem_local_unit_set_iff vF x).1 hx
    have hdpos : 0 < d := by
      rw [← hdegree]
      exact Module.finrank_pos
    have hdmul : (d : WithTop ℤ) * vE y = 0 := by
      calc
        (d : WithTop ℤ) * vE y = vF (chapter10LocalNorm F E y) :=
          (hnorm y hy0).symm
        _ = vF x := by rw [hxy]
        _ = 0 := hxval
    exact (mul_eq_zero.mp hdmul).resolve_left (by exact_mod_cast (Nat.ne_of_gt hdpos))

/-! The norm is continuous; the local-field topology supplies the topology on
the source and target, while finite-dimensionality supplies continuity of the
determinant polynomial. -/
theorem chapter10_local_norm_continuous
    (F E : Type*) [NontriviallyNormedField F] [CompleteSpace F] [NormedField E]
    [NormedAlgebra F E]
    [FiniteDimensional F E] :
    Continuous (chapter10LocalNorm F E) := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_norm_continuous F E

end
end LastLib.Book04AdelesAndIdeles.Chapter10
