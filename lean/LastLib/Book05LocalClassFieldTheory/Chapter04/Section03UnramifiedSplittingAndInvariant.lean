import LastLib.Book05LocalClassFieldTheory.Chapter04.Section02ValuationsOnDivisionAlgebras
import LastLib.Book05LocalClassFieldTheory.Chapter03.Section04CyclicAlgebras
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section05NormsInTowers
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter04

noncomputable section

open scoped BigOperators TensorProduct
open LastLib.Book05LocalClassFieldTheory.Chapter03
open LastLib.Book05LocalClassFieldTheory.Chapter02

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-! ## 4.3. Unramified splitting and the invariant -/

structure Chapter04ScalarExtensionAction
    (K D E : Type*) [Field K] [Ring D] [Field E]
    [Algebra K D] [Algebra K E] [Module E D] [FiniteDimensional E D]
    (embedding : E →ₐ[K] D) where
  action : D ⊗[K] E →ₐ[E] Module.End E D
  module_smul_eq : ∀ b : E, ∀ x : D, b • x = x * embedding b
  action_on_tmul : ∀ a : D, ∀ b : E, ∀ x : D,
    action (TensorProduct.tmul K a b) x = a * x * embedding b
  action_isomorphism : Nonempty
    (D ⊗[K] E ≃ₐ[E] Module.End E D)

theorem chapter04_scalar_extension_action_exists
    {K D E : Type*} [Field K] [Ring D] [Field E]
    [Algebra K D] [Algebra K E] [Module E D] [FiniteDimensional E D]
    (φ : E →ₐ[K] D) (hsmul : ∀ b : E, ∀ x : D, b • x = x * φ b) (d : ℕ)
    (hdimension : Module.finrank E D = d) :
    Nonempty (Chapter04ScalarExtensionAction K D E φ) := by
  sorry

theorem chapter04_division_algebra_splits_over_unramified_maximal_subfield
    {K D E : Type*} [Field K] [Ring D] [Field E]
    [Algebra K D] [Algebra K E] [Module E D] [FiniteDimensional E D]
    (φ : E →ₐ[K] D) (d : ℕ)
    (hdimension : Module.finrank E D = d)
    (A : Chapter04ScalarExtensionAction K D E φ) :
    Nonempty (D ⊗[K] E ≃ₐ[E] Matrix (Fin d) (Fin d) E) := by
  sorry

theorem chapter04_division_algebra_is_split_by_unramified_extension
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K)
    (D : Chapter04DivisionAlgebraData K)
    (E : Chapter04UnramifiedMaximalSubfieldSpec K P D) :
    chapter04UnramifiedMaximalSubfieldSplits P D E := by
  exact E.split_over_unramified_field

theorem chapter04_unramified_extension_is_cyclic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) :
    chapter03CyclicExtension K L U.degree U.arithmeticFrobenius := by
  sorry

noncomputable def chapter04UnramifiedCyclicAlgebraPresentation
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter03CyclicAlgebra K L U.degree U.arithmeticFrobenius
      (U.uniformizer ^ r) :=
  chapter03CyclicAlgebraChoice K L U.degree U.arithmeticFrobenius
    (U.uniformizer ^ r) (chapter04_unramified_extension_is_cyclic U)

def chapter04UnramifiedCyclicAlgebraSplits
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) : Prop :=
  chapter03CyclicAlgebraSplitsOverBase K L U.degree U.arithmeticFrobenius
    (U.uniformizer ^ r)
    (chapter04UnramifiedCyclicAlgebraPresentation U r)

def chapter04UnramifiedCyclicBrauerClass
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04BrauerGroup K :=
  chapter03CyclicAlgebraBrauerClass K L U.degree U.arithmeticFrobenius
    (U.uniformizer ^ r) (chapter04UnramifiedCyclicAlgebraPresentation U r)

def chapter04CyclicTermValue
    {L : Type*} [Field L] (vL : L → WithTop ℚ) (r : ℤ) (d : ℕ)
    (i : Fin d) (x : L) : WithTop ℚ :=
  vL x +
    (((r : ℚ) * ((i : ℕ) : ℚ) / (d : ℚ)) : WithTop ℚ)

def chapter04CyclicValuationFormula
    {L A : Type*} [Field L] [Ring A]
    (embed : L → A) (vL : L → WithTop ℚ) (r : ℤ) (d : ℕ)
    (basis : Fin d → A) (w : A → WithTop ℚ) : Prop :=
  ∀ x, x ≠ 0 →
    ∃ c : Fin d → L,
      x = ∑ i, embed (c i) * basis i ∧
        ∃ i : Fin d,
          w x = chapter04CyclicTermValue vL r d i (c i) ∧
            ∀ j : Fin d,
              w x ≤ chapter04CyclicTermValue vL r d j (c j)

def chapter04UnramifiedInvariantFraction
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04RationalResidue :=
  chapter04RationalResidueFraction r U.degree

theorem chapter04_unramified_cyclic_parameter_period
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04UnramifiedCyclicBrauerClass U (r + U.degree) =
      chapter04UnramifiedCyclicBrauerClass U r := by
  sorry

theorem chapter04_unramified_cyclic_parameter_modulo_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r s : ℤ)
    (hmod : r ≡ s [ZMOD U.degree]) :
    chapter04UnramifiedCyclicBrauerClass U r =
      chapter04UnramifiedCyclicBrauerClass U s := by
  sorry

theorem chapter04_unramified_invariant_fraction_periodic
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04UnramifiedInvariantFraction U (r + U.degree) =
      chapter04UnramifiedInvariantFraction U r := by
  sorry

theorem chapter04_unramified_fraction_denominator_change
    (r : ℤ) (d m : ℕ) (hm : 0 < m) (hd : 0 < d) :
    chapter04RationalResidueFraction r d =
      chapter04RationalResidueFraction (m * r) (m * d) := by
  sorry

/- A denominator change is a tower calculation.  Merely having two
  unramified extensions of the required dimensions does not identify their
  crossed products, so the intermediate-field and Frobenius compatibilities
  are recorded explicitly here. -/
structure Chapter04UnramifiedTowerData
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    (U : Chapter04UnramifiedExtensionData K L)
    (U' : Chapter04UnramifiedExtensionData K M) (m : ℕ) where
  positive : 0 < m
  degree_factor : U'.degree = m * U.degree
  uniformizer_eq : U'.uniformizer = U.uniformizer
  frobenius_restricts : ∀ x : L,
    U'.arithmeticFrobenius ^ m (algebraMap L M x) =
      algebraMap L M (U.arithmeticFrobenius x)

theorem chapter04_unramified_cyclic_brauer_denominator_change
    {K L M : Type*} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    (U : Chapter04UnramifiedExtensionData K L)
    (U' : Chapter04UnramifiedExtensionData K M)
    (m : ℕ) (T : Chapter04UnramifiedTowerData U U' m) (r : ℤ) :
    chapter04UnramifiedCyclicBrauerClass U r =
      chapter04UnramifiedCyclicBrauerClass U' (m * r) := by
  sorry

theorem chapter04_rational_residue_multiplication_is_surjective
    (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun q : chapter04RationalResidue => n • q) := by
  sorry

theorem chapter04_unramified_norm_of_base_uniformizer
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) :
    ∃ u : Kˣ,
      Units.map (Algebra.norm K (S := L))
          (Units.map (algebraMap K L).toMonoidHom U.uniformizer) =
        U.uniformizer ^ U.degree * u := by
  sorry

def chapter04CoprimeParameter (r : ℤ) (d : ℕ) : Prop :=
  Nat.Coprime r.natAbs d

theorem chapter04_unramified_cyclic_split_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04UnramifiedCyclicAlgebraSplits U r ↔
      U.degree ∣ r.natAbs := by
  sorry

theorem chapter04_unramified_cyclic_is_division_of_coprime_parameter
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ)
    (hcoprime : chapter04CoprimeParameter r U.degree) :
    ∃ w : (chapter04UnramifiedCyclicAlgebraPresentation U r).carrier → WithTop ℚ,
      w 0 = ⊤ ∧ w 1 = 0 ∧
      (∀ x y, x ≠ 0 → y ≠ 0 → w (x * y) = w x + w y) ∧
      (∀ x, x ≠ 0 → w x ≠ ⊤) ∧
      (∀ x y, x * y = 0 → x = 0 ∨ y = 0) := by
  sorry

theorem chapter04_unramified_cyclic_minimum_valuation_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ)
    (vL : AddValuation L (WithTop ℚ))
    (hπ : vL (algebraMap K L (U.uniformizer : K)) = (1 : WithTop ℚ))
    (hcoprime : chapter04CoprimeParameter r U.degree)
    (C : chapter03CyclicAlgebra K L U.degree U.arithmeticFrobenius
      (U.uniformizer ^ r)) :
    ∃ w : C.carrier → WithTop ℚ,
      chapter04CyclicValuationFormula
        (C.algebraL.algebraMap : L → C.carrier) vL r U.degree
        (fun i => C.symbol ^ (i : ℕ)) w ∧
      (∀ x y, x ≠ 0 → y ≠ 0 → w (x * y) = w x + w y) ∧
      (∀ x, x ≠ 0 → w x ≠ ⊤) ∧
      (∀ x y, x * y = 0 → x = 0 ∨ y = 0) := by
  sorry

theorem chapter04_finite_csa_without_zero_divisors_is_division
    {K : Type*} [Field K] (A : chapter04CentralSimpleAlgebra K)
    (hnozero : ∀ x y : A, x * y = 0 → x = 0 ∨ y = 0) :
    ∃ D : Chapter04DivisionAlgebraData K,
      Nonempty (A ≃ₐ[K] D.carrier) := by
  sorry

def chapter04ReducedCyclicDegree (r : ℤ) (d : ℕ) : ℕ :=
  d / Nat.gcd r.natAbs d

theorem chapter04_unramified_cyclic_underlying_division_degree
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    chapter04ReducedCyclicDegree r U.degree =
      U.degree / Nat.gcd r.natAbs U.degree := by
  rfl

theorem chapter04_unramified_cyclic_reduced_division_representative
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) (r : ℤ) :
    ∃ D : Chapter04DivisionAlgebraData K,
      D.degree = chapter04ReducedCyclicDegree r U.degree ∧
      chapter04BrauerEquivalent D.carrier
        (chapter04UnramifiedCyclicAlgebraPresentation U r).carrier := by
  sorry

structure Chapter04UnramifiedInvariantNormalization
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K)
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L) where
  uniformizer_value :
    I.invariant (chapter04UnramifiedCyclicBrauerClass U 1) =
      chapter04RationalResidueOneOver U.degree
  zero_parameter :
    chapter04UnramifiedCyclicBrauerClass U 0 = I.brauerLaw.one
  tensor_parameter_add : ∀ r s : ℤ,
    I.brauerLaw.tensor
        (chapter04UnramifiedCyclicBrauerClass U r)
        (chapter04UnramifiedCyclicBrauerClass U s) =
      chapter04UnramifiedCyclicBrauerClass U (r + s)
  opposite_parameter_neg : ∀ r : ℤ,
    I.brauerLaw.opposite (chapter04UnramifiedCyclicBrauerClass U r) =
      chapter04UnramifiedCyclicBrauerClass U (-r)

theorem chapter04_unramified_cyclic_invariant_fraction
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K)
    {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (U : Chapter04UnramifiedExtensionData K L)
    (N : Chapter04UnramifiedInvariantNormalization I U) (r : ℤ) :
    I.invariant (chapter04UnramifiedCyclicBrauerClass U r) =
      chapter04RationalResidueFraction r U.degree := by
  sorry

theorem chapter04_local_invariant_data_exists
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K) :
    Nonempty {I : Chapter04LocalInvariantData K // I.localField = P} := by
  sorry

theorem chapter04_theorem_4_1_local_invariant
    {K : Type*} [Field K] (P : Chapter04LocalFieldProfile K) :
    Nonempty {I : Chapter04LocalInvariantData K // I.localField = P} := by
  exact chapter04_local_invariant_data_exists P

theorem chapter04_local_invariant_is_an_isomorphism
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K) :
    Function.Injective I.invariant ∧ Function.Surjective I.invariant := by
  exact ⟨I.invariant_injective, I.invariant_surjective⟩

noncomputable def chapter04LocalInvariantEquiv
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K) :
    chapter04BrauerGroup K ≃ chapter04RationalResidue :=
  Equiv.ofBijective I.invariant
    ⟨I.invariant_injective, I.invariant_surjective⟩

theorem chapter04LocalInvariantEquiv_apply
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K)
    (a : chapter04BrauerGroup K) :
    chapter04LocalInvariantEquiv I a = I.invariant a := by
  rfl

def chapter04BrauerNatPower
    {K : Type*} [Field K] (B : Chapter04BrauerGroupLaw K)
    (a : chapter04BrauerGroup K) : ℕ → chapter04BrauerGroup K
  | 0 => B.one
  | n + 1 => B.tensor (chapter04BrauerNatPower B a n) a

theorem chapter04_invariant_of_brauer_nat_power
    {K : Type*} [Field K] (I : Chapter04LocalInvariantData K)
    (a : chapter04BrauerGroup K) (n : ℕ) :
    I.invariant (chapter04BrauerNatPower I.brauerLaw a n) =
      n • I.invariant a := by
  sorry

theorem chapter04_local_invariant_restriction_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = n • I_K.invariant α := by
  sorry

/- The invariant theorem also covers finite extensions with a purely
   inseparable part; separability is therefore not part of the final
   restriction statement. -/
theorem chapter04_local_invariant_restriction_formula_finite_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = n • I_K.invariant α := by
  sorry

theorem chapter04_restriction_unramified_stage_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (U : Chapter04UnramifiedExtensionData K L)
    (hdegree : Module.finrank K L = U.degree)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = U.degree • I_K.invariant α := by
  sorry

structure Chapter04TotallyRamifiedStageData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] where
  valuationK : AddValuation K (WithTop ℤ)
  valuationL : AddValuation L (WithTop ℤ)
  localK : Chapter02LocalField valuationK
  localL : Chapter02LocalField valuationL
  degree : ℕ
  degree_pos : 0 < degree
  degree_eq : Module.finrank K L = degree
  residue_agreement :
    LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11TotallyRamifiedResidueAgreement
      valuationK valuationL
  uniformizerK : K
  uniformizerL : L
  unit_factor : Lˣ
  uniformizerK_spec : chapter02IsUniformizer valuationK uniformizerK
  uniformizerL_spec : chapter02IsUniformizer valuationL uniformizerL
  uniformizer_factor :
    algebraMap K L uniformizerK = (unit_factor : L) * uniformizerL ^ degree

theorem chapter04_restriction_totally_ramified_stage_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (T : Chapter04TotallyRamifiedStageData K L)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = T.degree • I_K.invariant α := by
  sorry

/- The stage formula takes an explicit factorization witness; the source's
  purely inseparable case is handled separately in the invariant theorem. -/
theorem chapter04_restriction_finite_extension_stage_formula
    {K M L : Type*} [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vM : AddValuation M (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (eKM eML : ℕ)
    (hstage : LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnramifiedThenTotallyRamifiedFactorization
      K M L vK vM vL eKM eML)
    (I_K : Chapter04LocalInvariantData K)
    (I_M : Chapter04LocalInvariantData M)
    (I_L : Chapter04LocalInvariantData L)
    (R_KM : Chapter04BrauerRestrictionData K M)
    (R_ML : Chapter04BrauerRestrictionData M L)
    (R : Chapter04BrauerRestrictionData K L)
    (hdegreeKM : Module.finrank K M = eKM)
    (hdegreeML : Module.finrank M L = eML)
    (hrestriction_trans : R.restriction = R_ML.restriction ∘ R_KM.restriction)
    (α : chapter04BrauerGroup K) :
    I_L.invariant (R.restriction α) = (eKM * eML) • I_K.invariant α := by
  sorry

theorem chapter04_local_invariant_corestriction_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (C : Chapter04BrauerCorestrictionData K L)
    (β : chapter04BrauerGroup L) :
    I_K.invariant (C.corestriction β) = I_L.invariant β := by
  sorry

theorem chapter04_restriction_is_surjective_on_brauer_groups
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n) :
    Function.Surjective R.restriction := by
  sorry

theorem chapter04_corestriction_restriction_degree_formula
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (I_K : Chapter04LocalInvariantData K)
    (I_L : Chapter04LocalInvariantData L)
    (R : Chapter04BrauerRestrictionData K L)
    (C : Chapter04BrauerCorestrictionData K L)
    (n : ℕ) (hdegree : Module.finrank K L = n)
    (α : chapter04BrauerGroup K) :
    C.corestriction (R.restriction α) =
      chapter04BrauerNatPower I_K.brauerLaw α n := by
  sorry

end

end LastLib.Book05LocalClassFieldTheory.Chapter04
