import Mathlib

namespace ValuationsBook.Chapter07

open Filter Set Function MonoidWithZeroHom
open scoped BigOperators Topology PowerSeries LaurentSeries RatFunc WithZero Multiplicative

noncomputable section

/-!
  Chapter 7 develops completion from the metric point of view and compares it with
  valuation rings and ideal-adic completion. Proofs are deferred to a later pass.
-/

/-! ### 7.1. Finite approximations and digit strings -/

/-- The infinite base-p digit strings used to describe compatible approximations. -/
def chapter07DigitString (p : ℕ) : Type _ :=
  ℕ → Fin p

/-- The finite truncation of a p-adic digit string. -/
def chapter07DigitTruncation (p n : ℕ) (a : chapter07DigitString p) : ℕ :=
  ∑ i ∈ Finset.range n, (a i).val * p ^ i

/-! The localization at p and the finite rings ZMod powers. -/

abbrev chapter07LocalizedIntegers (p : ℕ) [Fact p.Prime] : Type _ :=
  Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))

abbrev chapter07FinitePAdicApproximation (p n : ℕ) : Type _ :=
  ZMod (p ^ n)

-- Section 7.1: every finite base-p approximation is represented by digits.
theorem chapter07_digits_surject_onto_finite_approximations
    (p n : ℕ) [Fact p.Prime] :
    Function.Surjective
      (fun a : chapter07DigitString p =>
        (chapter07DigitTruncation p n a : chapter07FinitePAdicApproximation p n)) := by
  sorry

-- Section 7.1: localization at (p) realizes every finite p-adic approximation.
theorem chapter07_localized_integers_realize_finite_approximations
    (p n : ℕ) [Fact p.Prime] :
    ∃ φ : chapter07LocalizedIntegers p →+*
        chapter07FinitePAdicApproximation p n,
      Function.Surjective φ := by
  sorry

/-! ### 7.1. Completion data and uniqueness -/

/-- A complete valued-field completion package, with its dense field embedding. -/
structure Chapter07CompletionData
    (K F Γ₀ : Type*) [Field K] [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Valued F Γ₀] where
  embedding : K →+* F
  complete : CompleteSpace F
  hausdorff : T0Space F
  injective : Function.Injective embedding
  isometric : ∀ x : K,
    Valued.v (R := F) (embedding x) = Valued.v (R := K) x
  dense : DenseRange embedding

/-- The property that a field equivalence is isometric and commutes with the embeddings. -/
def chapter07IsometricFieldEquiv
    {K F G Γ₀ : Type*} [Field K] [Field F] [Field G]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Valued F Γ₀] [Valued G Γ₀]
    (A : Chapter07CompletionData K F Γ₀) (B : Chapter07CompletionData K G Γ₀)
    (e : F ≃+* G) : Prop :=
  (∀ y : F, Valued.v (R := G) (e y) = Valued.v (R := F) y) ∧
    ∀ x : K, e (A.embedding x) = B.embedding x

-- Section 7.1: a completion is unique up to a unique isometric field isomorphism.
theorem chapter07_completion_unique_up_to_unique_isometric_field_equiv
    {K F G Γ₀ : Type*} [Field K] [Field F] [Field G]
    [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [Valued F Γ₀] [Valued G Γ₀]
    (A : Chapter07CompletionData K F Γ₀) (B : Chapter07CompletionData K G Γ₀) :
    ∃! e : F ≃+* G, chapter07IsometricFieldEquiv A B e := by
  sorry

-- The standard Mathlib completion package for a valued field.
noncomputable def chapter07StandardValuedCompletionData
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    Chapter07CompletionData K (UniformSpace.Completion K) Γ₀ where
  embedding := UniformSpace.Completion.coeRingHom
  complete := inferInstance
  hausdorff := inferInstance
  injective := by
    exact UniformSpace.Completion.coe_injective K
  isometric := by
    intro x
    exact Valued.extensionValuation_apply_coe x
  dense := UniformSpace.Completion.denseRange_coe

/-! ### 7.1. The Cauchy-sequence construction -/

/-- Cauchy sequences in a uniform space, packaged as a subtype. -/
abbrev chapter07CauchySequence (K : Type*) [UniformSpace K] : Type _ :=
  {u : ℕ → K // CauchySeq u}

/-- Equivalence of Cauchy sequences: their difference tends to zero. -/
def chapter07CauchyEquivalent
    (K : Type*) [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (u v : chapter07CauchySequence K) : Prop :=
  Tendsto (fun n => u.1 n - v.1 n) (atTop : Filter ℕ) (𝓝 0)

/-- The setoid used for the Cauchy-sequence model of completion. -/
def chapter07CauchySetoid
    (K : Type*) [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] :
    Setoid (chapter07CauchySequence K) where
  r := chapter07CauchyEquivalent K
  iseqv := by
    sorry

/-- The quotient of Cauchy sequences by sequences tending to zero. -/
abbrev chapter07CauchyCompletion
    (K : Type*) [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] : Type _ :=
  Quotient (chapter07CauchySetoid K)

-- The class of a Cauchy sequence in the quotient model.
def chapter07CauchyClass
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (u : chapter07CauchySequence K) : chapter07CauchyCompletion K :=
  Quotient.mk (chapter07CauchySetoid K) u

-- Termwise addition of Cauchy sequences.
def chapter07CauchySequenceAdd
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (u v : chapter07CauchySequence K) : chapter07CauchySequence K :=
  ⟨fun n => u.1 n + v.1 n, by
    sorry⟩

-- Termwise multiplication of Cauchy sequences.
def chapter07CauchySequenceMul
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (u v : chapter07CauchySequence K) : chapter07CauchySequence K :=
  ⟨fun n => u.1 n * v.1 n, by
    sorry⟩

-- Constant Cauchy sequences embed the original field in the quotient model.
def chapter07CauchyConstant
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (x : K) : chapter07CauchySequence K :=
  ⟨fun _ => x, by
    sorry⟩

-- The constant-sequence map into the Cauchy quotient.
def chapter07CauchyConstantEmbedding
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] :
    K → chapter07CauchyCompletion K :=
  fun x => chapter07CauchyClass (chapter07CauchyConstant x)

-- Termwise addition descends to equivalence classes.
def chapter07CauchyCompletionAdd
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (x y : chapter07CauchyCompletion K) : chapter07CauchyCompletion K :=
  Quotient.liftOn₂ x y
    (fun u v => chapter07CauchyClass (chapter07CauchySequenceAdd u v))
    (by
      intro u₁ v₁ u₂ v₂ hu hv
      sorry)

-- Termwise multiplication descends to equivalence classes.
def chapter07CauchyCompletionMul
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (x y : chapter07CauchyCompletion K) : chapter07CauchyCompletion K :=
  Quotient.liftOn₂ x y
    (fun u v => chapter07CauchyClass (chapter07CauchySequenceMul u v))
    (by
      intro u₁ v₁ u₂ v₂ hu hv
      sorry)

-- The quotient zero and one represented by constant sequences.
def chapter07CauchyCompletionZero
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] :
    chapter07CauchyCompletion K :=
  chapter07CauchyConstantEmbedding 0

def chapter07CauchyCompletionOne
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K] :
    chapter07CauchyCompletion K :=
  chapter07CauchyConstantEmbedding 1

-- Section 7.1: termwise addition is independent of representatives.
theorem chapter07_cauchy_add_respects_equivalence
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K]
    (u₁ u₂ v₁ v₂ : chapter07CauchySequence K)
    (hu : chapter07CauchyEquivalent K u₁ u₂)
    (hv : chapter07CauchyEquivalent K v₁ v₂) :
    chapter07CauchyEquivalent K
      (chapter07CauchySequenceAdd u₁ v₁)
      (chapter07CauchySequenceAdd u₂ v₂) := by
  sorry

-- Section 7.1: termwise multiplication is independent of representatives.
theorem chapter07_cauchy_mul_respects_equivalence
    {K : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (u₁ u₂ v₁ v₂ : chapter07CauchySequence K)
    (hu : chapter07CauchyEquivalent K u₁ u₂)
    (hv : chapter07CauchyEquivalent K v₁ v₂) :
    chapter07CauchyEquivalent K
      (chapter07CauchySequenceMul u₁ v₁)
      (chapter07CauchySequenceMul u₂ v₂) := by
  sorry

-- The constant-sequence map is injective.
theorem chapter07_cauchy_constant_embedding_injective
    {K : Type*} [AddGroup K] [UniformSpace K] [IsUniformAddGroup K] [T0Space K] :
    Function.Injective (@chapter07CauchyConstantEmbedding K _ _ _) := by
  sorry

/- A discrete nonarchimedean absolute value compatible with the given uniformity. -/
class Chapter07NonarchimedeanStationarity
    (K : Type*) [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) : Prop where
  nonarchimedean : ∀ x y : K, abv (x + y) ≤ max (abv x) (abv y)
  discrete : ∃ q : ℝ, 0 < q ∧ q < 1 ∧
    ∀ {x : K}, x ≠ 0 → ∃ z : ℤ, abv x = q ^ z
  compatible : Continuous (abv : K → ℝ)
  uniformSpace_eq : (inferInstance : UniformSpace K) = abv.uniformSpace
-- A representative formula for the extended absolute value.
def chapter07CauchyAbsoluteValue
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ)
    [Chapter07NonarchimedeanStationarity K abv] :
    chapter07CauchyCompletion K → ℝ := by
  refine Quotient.lift
    (fun u : chapter07CauchySequence K =>
      limUnder (atTop : Filter ℕ) (fun n => abv (u.1 n))) ?_
  intro u v huv
  sorry

-- Section 7.1: the extension has the displayed representative formula.
theorem chapter07_cauchy_absolute_value_formula
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K) :
    chapter07CauchyAbsoluteValue abv (chapter07CauchyClass u) =
      limUnder (atTop : Filter ℕ) (fun n => abv (u.1 n)) := by
  sorry

-- If a representative tends to zero, its extended absolute value is zero.
theorem chapter07_cauchy_absolute_value_limit_zero
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) (u : chapter07CauchySequence K)
    (hu : Tendsto u.1 (atTop : Filter ℕ) (𝓝 0))
    (habv : Continuous (abv : K → ℝ)) :
    Tendsto (fun n => abv (u.1 n)) (atTop : Filter ℕ) (𝓝 0) := by
  sorry

-- The absolute value of a zero-limit representative is zero in the quotient.
theorem chapter07_cauchy_absolute_value_of_zero_limit
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K)
    (hu : Tendsto u.1 (atTop : Filter ℕ) (𝓝 0))
    (habv : Continuous (abv : K → ℝ)) :
    chapter07CauchyAbsoluteValue abv (chapter07CauchyClass u) = 0 := by
  sorry

-- A nonzero norm sequence that is eventually constant.
def chapter07EventuallyConstantAbsoluteValue
    {K : Type*} [Field K] [UniformSpace K]
    (abv : AbsoluteValue K ℝ) (u : chapter07CauchySequence K) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in (atTop : Filter ℕ), abv (u.1 n) = c


-- Section 7.1: a nonzero Cauchy class has eventually constant positive absolute value.
theorem chapter07_nonzero_cauchy_absolute_value_eventually_constant
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ)
    [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K)
    (hu : ¬ Tendsto u.1 (atTop : Filter ℕ) (𝓝 0)) :
    chapter07EventuallyConstantAbsoluteValue abv u := by
  sorry

-- The extended absolute value is independent of the representative.
theorem chapter07_cauchy_absolute_value_representative_independent
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u v : chapter07CauchySequence K)
    (h : chapter07CauchyEquivalent K u v) :
    chapter07CauchyAbsoluteValue abv (chapter07CauchyClass u) =
      chapter07CauchyAbsoluteValue abv (chapter07CauchyClass v) := by
  sorry

/- The quotient model carries the uniformity transported from Mathlib's canonical completion. -/
structure Chapter07CauchyCompletionModel
    (K : Type*) [Field K] [UniformSpace K] [IsUniformAddGroup K] where
  uniformSpace : UniformSpace (chapter07CauchyCompletion K)
  complete : @CompleteSpace (chapter07CauchyCompletion K) uniformSpace
  equivalent : chapter07CauchyCompletion K ≃ UniformSpace.Completion K
  uniform_to_completion :
    @UniformContinuous (chapter07CauchyCompletion K) (UniformSpace.Completion K)
      uniformSpace inferInstance equivalent
  uniform_from_completion :
    @UniformContinuous (UniformSpace.Completion K) (chapter07CauchyCompletion K)
      inferInstance uniformSpace equivalent.symm

-- Section 7.1: a diagonal argument makes the Cauchy quotient complete.
theorem chapter07_cauchy_quotient_complete
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] :
    Nonempty (Chapter07CauchyCompletionModel K) := by
  sorry

-- The diagonal representative assertion used to prove completeness.
theorem chapter07_cauchy_diagonal_representative
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    (x : chapter07CauchyCompletion K) :
    ∃ u : chapter07CauchySequence K,
      x = chapter07CauchyClass u := by
  sorry

/-! ### 7.2. Extending inverses and valuations -/

-- The inverse-difference formula displayed in Section 7.2.
theorem chapter07_inverse_difference_absolute_value
    {K : Type*} [Field K] (abv : AbsoluteValue K ℝ)
    (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    abv (x⁻¹ - y⁻¹) =
      abv (x - y) / (abv x * abv y) := by
  sorry

-- A quantitative form of being bounded away from zero.
def chapter07CauchyBoundedAwayFromZero
    {K : Type*} [Field K] [UniformSpace K]
    (abv : AbsoluteValue K ℝ) (u : chapter07CauchySequence K) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in (atTop : Filter ℕ), c ≤ abv (u.1 n)

-- The termwise inverse sequence after discarding finitely many terms.
def chapter07CauchySequenceInverse
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K)
    (hu : chapter07CauchyBoundedAwayFromZero abv u) :
    chapter07CauchySequence K :=
  ⟨fun n => (u.1 n)⁻¹, by
    sorry⟩

-- Section 7.2: the inverse of a nonzero Cauchy class is represented by inverse terms.
theorem chapter07_inverse_sequence_is_cauchy
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (u : chapter07CauchySequence K)
    (hu : chapter07CauchyBoundedAwayFromZero abv u) :
    CauchySeq (fun n => (u.1 n)⁻¹) := by
  sorry

-- Inversion descends to the Cauchy quotient.
def chapter07CauchyCompletionInverse
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (x : chapter07CauchyCompletion K) : chapter07CauchyCompletion K := by
  sorry

-- The inverse class is a two-sided inverse.
theorem chapter07_cauchy_completion_nonzero_has_inverse
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv]
    (x : chapter07CauchyCompletion K) (hx : x ≠ chapter07CauchyCompletionZero) :
    ∃ y : chapter07CauchyCompletion K,
      chapter07CauchyCompletionMul x y = chapter07CauchyCompletionOne ∧
        chapter07CauchyCompletionMul y x = chapter07CauchyCompletionOne := by
  sorry

-- Section 7.2: the Cauchy completion of a valued field is a field.
theorem chapter07_valued_cauchy_completion_is_a_field
    {K : Type*} [Field K] [UniformSpace K] [IsUniformAddGroup K] [IsTopologicalRing K]
    (abv : AbsoluteValue K ℝ) [Chapter07NonarchimedeanStationarity K abv] :
    ∀ x : chapter07CauchyCompletion K,
      x ≠ chapter07CauchyCompletionZero →
        ∃ y : chapter07CauchyCompletion K,
          chapter07CauchyCompletionMul x y = chapter07CauchyCompletionOne ∧
            chapter07CauchyCompletionMul y x = chapter07CauchyCompletionOne := by
  sorry

-- The valuation on the standard completion, obtained by extending the original valuation.
noncomputable def chapter07CompletionValuation
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    Valuation (UniformSpace.Completion K) Γ₀ :=
  Valued.extensionValuation

-- Section 7.2: the extended valuation agrees with the original on the dense subfield.
theorem chapter07_completion_valuation_apply_coe
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : K) :
    chapter07CompletionValuation K Γ₀ (x : UniformSpace.Completion K) =
      Valued.v x := by
  sorry

-- The value groups of a valued field and its completion are canonically equivalent.
noncomputable def chapter07CompletionValueGroupEquiv
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    ValueGroup₀ (.ofClass (Valued.v (R := K))) ≃*
      ValueGroup₀ (.ofClass (chapter07CompletionValuation K Γ₀)) :=
  Valued.valueGroup₀_equiv_extensionValuation

-- Discrete valuations have eventually constant values on nonzero Cauchy sequences.
theorem chapter07_discrete_valuation_values_eventually_constant
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (u : chapter07CauchySequence K)
    (hu : ¬ Tendsto u.1 (atTop : Filter ℕ) (𝓝 0)) :
    ∃ c : Γ₀, c ≠ 0 ∧ ∀ᶠ n in (atTop : Filter ℕ), Valued.v (u.1 n) = c := by
  sorry

-- A discrete value group is indexed by the integers, including zero.
noncomputable def chapter07DiscreteValueGroupEquiv
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) [v.IsRankOneDiscrete] :
    ValueGroup₀ (.ofClass v) ≃*o ℤᵐ⁰ :=
  Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt v

/- Order-theoretic approximation of a completed value by values from the dense field. -/
def Chapter07ValueApproximatedByOriginalValues
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) : Prop :=
  ∀ γ : Γ₀, γ < chapter07CompletionValuation K Γ₀ x →
    ∃ r : K, γ < Valued.v r

-- Nonzero values in the completed field are limits of values from the original field.
theorem chapter07_completion_nonzero_value_is_approximated
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) (hx : x ≠ 0) :
    Chapter07ValueApproximatedByOriginalValues x := by
  sorry

/- Order closure of the original value set at a completed nonzero value. -/
def Chapter07ValueInOrderClosureOfOriginalValues
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) : Prop :=
  ∀ γ₁ γ₂ : Γ₀,
    γ₁ < chapter07CompletionValuation K Γ₀ x →
      chapter07CompletionValuation K Γ₀ x < γ₂ →
        ∃ r : K, γ₁ < Valued.v r ∧ Valued.v r < γ₂

-- Nonzero completed values lie in the order closure of original values.
theorem chapter07_completion_nonzero_value_is_in_order_closure
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K) (hx : x ≠ 0) :
    Chapter07ValueInOrderClosureOfOriginalValues x := by
  sorry

/-! ### 7.3. The universal property -/

-- The canonical extension map from a uniform space to a complete target.
noncomputable def chapter07UniversalCompletionExtension
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F]
    (f : K → F) (hf : UniformContinuous f) : UniformSpace.Completion K → F :=
  UniformSpace.Completion.extension f

-- The extension agrees with the original map on the dense copy of K.
theorem chapter07_universal_extension_coe
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F]
    (f : K → F) (hf : UniformContinuous f) (x : K) :
    chapter07UniversalCompletionExtension f hf (x : UniformSpace.Completion K) = f x := by
  sorry

-- Theorem 7.1: every uniformly continuous map extends uniquely to the completion.
theorem chapter07_completion_universal_property
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F]
    (f : K → F) (hf : UniformContinuous f) :
    ∃ g : UniformSpace.Completion K → F,
      UniformContinuous g ∧
        (∀ x : K, g (x : UniformSpace.Completion K) = f x) ∧
          ∀ g' : UniformSpace.Completion K → F, Continuous g' →
            (∀ x : K, g' (x : UniformSpace.Completion K) = f x) → g' = g := by
  sorry

-- The value of the extension can be computed from any approximating sequence.
theorem chapter07_universal_extension_as_limit
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F] [Nonempty F]
    (f : K → F) (hf : UniformContinuous f)
    (x : UniformSpace.Completion K) (u : ℕ → K)
    (hu : Tendsto (fun n => (u n : UniformSpace.Completion K)) (atTop : Filter ℕ) (𝓝 x)) :
    chapter07UniversalCompletionExtension f hf x =
      limUnder (atTop : Filter ℕ) (fun n => f (u n)) := by
  sorry

-- The dense-approximation construction is independent of the chosen approximating sequence.
theorem chapter07_universal_extension_approximation_independent
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F] [Nonempty F]
    (f : K → F) (hf : UniformContinuous f) (x : UniformSpace.Completion K)
    (u v : ℕ → K)
    (hu : Tendsto (fun n => (u n : UniformSpace.Completion K)) (atTop : Filter ℕ) (𝓝 x))
    (hv : Tendsto (fun n => (v n : UniformSpace.Completion K)) (atTop : Filter ℕ) (𝓝 x)) :
    limUnder (atTop : Filter ℕ) (fun n => f (u n)) =
      limUnder (atTop : Filter ℕ) (fun n => f (v n)) := by
  sorry

-- The completion extension of a continuous ring homomorphism.
noncomputable def chapter07UniversalCompletionRingHom
    {K F : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K] [Ring F] [UniformSpace F] [IsUniformAddGroup F]
    [IsTopologicalRing F] [CompleteSpace F] [T0Space F]
    (f : K →+* F) (hf : Continuous f) :
    UniformSpace.Completion K →+* F :=
  UniformSpace.Completion.extensionHom f hf

-- The ring-hom extension agrees with the original ring homomorphism.
theorem chapter07_universal_extension_ringHom_coe
    {K F : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K] [Ring F] [UniformSpace F] [IsUniformAddGroup F]
    [IsTopologicalRing F] [CompleteSpace F] [T0Space F]
    (f : K →+* F) (hf : Continuous f) (x : K) :
    chapter07UniversalCompletionRingHom f hf (x : UniformSpace.Completion K) = f x := by
  sorry

-- Compatibility of a field hom with a chosen valuation.
def chapter07ValuationCompatibleRingHom
    {K F Γ₀ : Type*} [Ring K] [Ring F] [LinearOrderedCommMonoidWithZero Γ₀]
    (vK : Valuation K Γ₀) (vF : Valuation F Γ₀) (f : K →+* F) : Prop :=
  ∀ x : K, vF (f x) = vK x

-- Theorem 7.1, valued form: compatible field homomorphisms extend compatibly.
theorem chapter07_completion_extension_preserves_valuation
    {K F Γ₀ : Type*} [Field K] [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Valued F Γ₀]
    [CompleteSpace F] [T0Space F]
    (f : K →+* F) (hf : Continuous f)
    (hcompat : chapter07ValuationCompatibleRingHom (Valued.v (R := K)) (Valued.v (R := F)) f) :
    ∀ x : UniformSpace.Completion K,
      Valued.v (R := F) (chapter07UniversalCompletionRingHom f hf x) =
        chapter07CompletionValuation K Γ₀ x := by
  sorry

/-! ### 7.4. Completion of a valuation ring -/

abbrev chapter07ValuationRing
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] : Type _ :=
  Valued.integer K

@[instance_reducible]
noncomputable def chapter07CompletedValuationRing
    (K Γ₀ : Type*) [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] : ValuationSubring (UniformSpace.Completion K) :=
  (chapter07CompletionValuation K Γ₀).valuationSubring

-- The unit-ball characterization of the completed valuation ring.
theorem chapter07_completed_valuation_ring_carrier
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    (chapter07CompletedValuationRing K Γ₀ : Set (UniformSpace.Completion K)) =
      {x | chapter07CompletionValuation K Γ₀ x ≤ 1} := by
  sorry

-- The completed unit ball is closed.
theorem chapter07_completed_valuation_ring_is_closed
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    IsClosed (chapter07CompletedValuationRing K Γ₀ :
      Set (UniformSpace.Completion K)) := by
  sorry

-- The inclusion from the original valuation ring into the completion.
def chapter07ValuationRingCompletionEmbedding
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    chapter07ValuationRing K Γ₀ → UniformSpace.Completion K :=
  fun a => ((a : K) : UniformSpace.Completion K)

-- Section 7.4: one inclusion in the closure characterization.
theorem chapter07_valuation_ring_closure_subset
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    closure (Set.range (@chapter07ValuationRingCompletionEmbedding K Γ₀ _ _ _)) ⊆
      (chapter07CompletedValuationRing K Γ₀ :
        Set (UniformSpace.Completion K)) := by
  sorry

-- Section 7.4: every point of the completed unit ball is approximated by integral elements.
theorem chapter07_completed_unit_ball_is_approximated_by_integral_elements
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] (x : UniformSpace.Completion K)
    (hx : chapter07CompletionValuation K Γ₀ x ≤ 1) :
    x ∈ closure (Set.range (@chapter07ValuationRingCompletionEmbedding K Γ₀ _ _ _)) := by
  sorry

-- The closure of the valuation ring is exactly the completed valuation ring.
theorem chapter07_valuation_ring_closure_eq_completed_valuation_ring
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] :
    closure (Set.range (@chapter07ValuationRingCompletionEmbedding K Γ₀ _ _ _)) =
      (chapter07CompletedValuationRing K Γ₀ :
        Set (UniformSpace.Completion K)) := by
  sorry

-- A uniformizer in the original valuation ring, bundled by Mathlib.
def chapter07CompletedUniformizer
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (π : (Valued.v (R := K)).Uniformizer) :
    chapter07CompletedValuationRing K Γ₀ :=
  ⟨(((π : Valued.integer K) : K) : UniformSpace.Completion K), by
    sorry⟩

-- The completed uniformizer has the same value as the original uniformizer.
theorem chapter07_completed_uniformizer_preserves_value
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (π : (Valued.v (R := K)).Uniformizer) :
    chapter07CompletionValuation K Γ₀
        (chapter07CompletedUniformizer π) =
      Valued.v (π.val : K) := by
  sorry

-- The completion has the same discrete value group.
theorem chapter07_completed_dvr_value_group_is_integer
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete] :
    Nonempty
      (ValueGroup₀ (.ofClass (chapter07CompletionValuation K Γ₀)) ≃*o ℤᵐ⁰) := by
  sorry

-- The completed valuation ring is a DVR.
theorem chapter07_completed_valuation_ring_is_dvr
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete] :
    IsDiscreteValuationRing (chapter07CompletedValuationRing K Γ₀) ∧
      IsAdicComplete
        (IsLocalRing.maximalIdeal (chapter07CompletedValuationRing K Γ₀))
        (chapter07CompletedValuationRing K Γ₀) := by
  sorry

-- A uniformizer generates the maximal ideal in any DVR.
theorem chapter07_dvr_uniformizer_generates_maximal_ideal
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) :
    Ideal.span ({π} : Set A) = IsLocalRing.maximalIdeal A := by
  sorry

-- Finite-level quotients of the original and completed valuation rings.
theorem chapter07_dvr_finite_level_quotient_equivalence
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (π : (Valued.v (R := K)).Uniformizer) (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      ((chapter07ValuationRing K Γ₀) ⧸
          Ideal.span ({(π.val : chapter07ValuationRing K Γ₀) ^ n} : Set
            (chapter07ValuationRing K Γ₀)) ≃+*
        (chapter07CompletedValuationRing K Γ₀) ⧸
          Ideal.span ({(chapter07CompletedUniformizer π) ^ n} : Set
            (chapter07CompletedValuationRing K Γ₀))) := by
  sorry

-- The residue fields are canonically identified at level n = 1.
theorem chapter07_dvr_residue_field_equivalence
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete]
    (π : (Valued.v (R := K)).Uniformizer) :
    Nonempty
      ((chapter07ValuationRing K Γ₀) ⧸
          Ideal.span ({(π.val : chapter07ValuationRing K Γ₀)} : Set
            (chapter07ValuationRing K Γ₀)) ≃+*
        (chapter07CompletedValuationRing K Γ₀) ⧸
          Ideal.span ({chapter07CompletedUniformizer π} : Set
            (chapter07CompletedValuationRing K Γ₀))) := by
  sorry

-- The completed field is the fraction field of the completed DVR.
theorem chapter07_completed_field_is_fraction_field
    {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [hdiscrete : (Valued.v (R := K)).IsRankOneDiscrete] :
    Nonempty
      (FractionRing (chapter07CompletedValuationRing K Γ₀) ≃+*
        UniformSpace.Completion K) := by
  sorry

/-! ### 7.5. Separated ideal-adic completion -/

abbrev chapter07AdicCompletion
    (R : Type*) [CommRing R] (I : Ideal R) : Type _ :=
  AdicCompletion I R

-- The canonical map from a ring to its ideal-adic completion.
def chapter07AdicCompletionMap
    {R : Type*} [CommRing R] (I : Ideal R) :
    R →+* chapter07AdicCompletion R I :=
  algebraMap R (chapter07AdicCompletion R I)

-- The inverse-limit compatibility condition in AdicCompletion.
theorem chapter07_adic_completion_compatible_family
    {R : Type*} [CommRing R] (I : Ideal R)
    (x : chapter07AdicCompletion R I) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      AdicCompletion.transitionMap I R hmn (x.val n) = x.val m := by
  sorry

-- The kernel of the natural map is the intersection of all powers of the ideal.
theorem chapter07_adic_completion_kernel
    {R : Type*} [CommRing R] (I : Ideal R) :
    RingHom.ker (chapter07AdicCompletionMap I) = ⨅ n : ℕ, I ^ n := by
  sorry

-- The algebraic completion map is injective exactly in the separated case.
theorem chapter07_adic_completion_injective_iff_separated
    {R : Type*} [CommRing R] (I : Ideal R) :
    Function.Injective (chapter07AdicCompletionMap I) ↔ IsHausdorff I R := by
  sorry

-- A witness in every power of I disappears in the adic completion.
theorem chapter07_adic_nonseparated_witness_in_kernel
    {R : Type*} [CommRing R] (I : Ideal R) (x : R)
    (hx : ∀ n : ℕ, x ∈ I ^ n) :
    chapter07AdicCompletionMap I x = 0 := by
  sorry

-- A nonzero intersection witness makes the completion map noninjective.
theorem chapter07_adic_nonseparated_map_not_injective
    {R : Type*} [CommRing R] (I : Ideal R)
    (h : ∃ x : R, x ≠ 0 ∧ ∀ n : ℕ, x ∈ I ^ n) :
    ¬ Function.Injective (chapter07AdicCompletionMap I) := by
  sorry

-- Noetherian local domains are separated for every ideal contained in the maximal ideal.
theorem chapter07_noetherian_local_domain_is_adically_separated
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsLocalRing R] (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R) :
    IsHausdorff I R := by
  sorry

-- The canonical uniformity pulled back from the DVR valuation on its fraction field.
noncomputable def chapter07DvrUniformSpace
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    UniformSpace A :=
  UniformSpace.comap (algebraMap A (FractionRing A))
    ((Valued.mk' ((IsDiscreteValuationRing.maximalIdeal A).valuation (FractionRing A))).toUniformSpace)

-- The standard DVR statement comparing metric and ideal-adic completion.
theorem chapter07_dvr_metric_completion_agrees_with_adic_completion
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    : ∃ e : @UniformSpace.Completion A (chapter07DvrUniformSpace A) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal A) A,
      ∀ a : A,
        e ((a : A) : @UniformSpace.Completion A (chapter07DvrUniformSpace A)) =
        chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) a := by
  sorry

-- The finite filtration is unchanged by completion in the DVR case.
theorem chapter07_dvr_adic_completion_preserves_finite_filtration
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (hπ : Irreducible π) :
    ∀ n : ℕ, 1 ≤ n →
      Nonempty
        (A ⧸ Ideal.span ({π ^ n} : Set A) ≃+*
          AdicCompletion (IsLocalRing.maximalIdeal A) A ⧸ Ideal.span
            ({chapter07AdicCompletionMap (IsLocalRing.maximalIdeal A) (π ^ n)} : Set
              (AdicCompletion (IsLocalRing.maximalIdeal A) A))) := by
  sorry

/-! ### 7.6. Examples: p-adic completions -/

abbrev chapter07PAdicField (p : ℕ) [Fact p.Prime] : Type _ :=
  ℚ_[p]

abbrev chapter07PAdicIntegerRing (p : ℕ) [Fact p.Prime] : Type _ :=
  ℤ_[p]

-- The absolute value underlying the p-adic uniformity on ℚ.
def chapter07PAdicAbsoluteValue (p : ℕ) [Fact p.Prime] : AbsoluteValue ℚ ℚ :=
  IsAbsoluteValue.toAbsoluteValue (padicNorm p)

-- The uniform structure used for the p-adic completion of ℚ.
abbrev chapter07PAdicUniformSpace (p : ℕ) [Fact p.Prime] : UniformSpace ℚ :=
  (chapter07PAdicAbsoluteValue p).uniformSpace

-- Section 7.6: the rationals are incomplete for the p-adic uniformity.
theorem chapter07_rationals_are_padic_incomplete
    (p : ℕ) [Fact p.Prime] :
    ¬ @CompleteSpace ℚ (chapter07PAdicUniformSpace p) := by
  sorry

-- The p-adic field is complete.
theorem chapter07_padic_field_is_complete
    (p : ℕ) [Fact p.Prime] :
    CompleteSpace (chapter07PAdicField p) := by
  sorry

-- The rationals are dense in the p-adic field.
theorem chapter07_rationals_are_dense_in_padic_field
    (p : ℕ) [Fact p.Prime] :
    DenseRange ((↑) : ℚ → chapter07PAdicField p) := by
  sorry

-- The completion of ℚ for the p-adic absolute value is ℚ_[p].
theorem chapter07_padic_field_is_the_padic_completion
    (p : ℕ) [Fact p.Prime] :
    Nonempty
      (@UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p) ≃ᵤ
        chapter07PAdicField p) := by
  sorry

-- The p-adic integers form the complete valuation ring inside ℚ_[p].
theorem chapter07_padic_integer_ring_is_complete
    (p : ℕ) [Fact p.Prime] :
    CompleteSpace (chapter07PAdicIntegerRing p) := by
  sorry

-- The localization at (p) carries its canonical map into the fraction field ℚ.
noncomputable def chapter07LocalizedIntegersToRationals
    (p : ℕ) [Fact p.Prime] :
    chapter07LocalizedIntegers p →+* ℚ := by
  sorry

abbrev chapter07LocalizedIntegersPAdicUniformSpace (p : ℕ) [Fact p.Prime] :
    UniformSpace (chapter07LocalizedIntegers p) :=
  UniformSpace.comap (chapter07LocalizedIntegersToRationals p)
    (chapter07PAdicUniformSpace p)

-- The canonical p-adic uniformity on the localization is pulled back from ℚ.
theorem chapter07_localized_integers_padic_completion
    (p : ℕ) [Fact p.Prime] :
    Nonempty
      (@UniformSpace.Completion (chapter07LocalizedIntegers p)
        (chapter07LocalizedIntegersPAdicUniformSpace p) ≃ᵤ
          chapter07PAdicIntegerRing p) := by
  sorry

-- The p-adic truncation sequence attached to an infinite digit string.
def chapter07PAdicDigitLimit
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) :
    chapter07PAdicIntegerRing p :=
  PadicInt.ofIntSeq (p := p)
    (fun n => (chapter07DigitTruncation p n a : ℤ))
    (by
      sorry)

-- Rational truncations converge to the digit-string limit in the p-adic integers.
theorem chapter07_padic_digit_truncations_converge
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) :
    Tendsto
      (fun n => ((chapter07DigitTruncation p n a : ℕ) :
        chapter07PAdicField p))
      (atTop : Filter ℕ)
      (𝓝 ((chapter07PAdicDigitLimit p a : chapter07PAdicIntegerRing p) :
        chapter07PAdicField p)) := by
  sorry

-- A digit string is rationally represented if its p-adic limit comes from ℚ.
def chapter07DigitStringRationallyRepresented
    (p : ℕ) [Fact p.Prime] (a : chapter07DigitString p) : Prop :=
  ∃ q : ℚ,
    (q : chapter07PAdicField p) =
      (chapter07PAdicDigitLimit p a : chapter07PAdicField p)

-- There are infinitely many compatible infinite digit strings with no rational representative.
theorem chapter07_infinitely_many_nonrational_padic_digit_strings
    (p : ℕ) [Fact p.Prime] :
    Set.Infinite
      {a : chapter07DigitString p |
        ¬ chapter07DigitStringRationallyRepresented p a} := by
  sorry

/-! ### 7.6. Examples: Laurent and power series -/

abbrev chapter07RationalFunctionField (k : Type*) [Field k] : Type _ :=
  RatFunc k

abbrev chapter07LaurentSeriesField (k : Type*) [Field k] : Type _ :=
  LaurentSeries k

abbrev chapter07PowerSeriesRing (k : Type*) [Field k] : Type _ :=
  PowerSeries k

-- The X-adic completion of the rational-function field in the Laurent-series API.
abbrev chapter07RationalFunctionAdicCompletion (k : Type*) [Field k] : Type _ :=
  LaurentSeries.RatFuncAdicCompl k

-- The actual local polynomial ring k[t]_(t), before completion.
local instance chapter07PolynomialXPrime (k : Type*) [Field k] :
    (Ideal.span ({Polynomial.X} : Set (Polynomial k))).IsPrime :=
  (Ideal.span_singleton_prime Polynomial.X_ne_zero).2 Polynomial.prime_X

abbrev chapter07PolynomialLocalRing (k : Type*) [Field k] : Type _ :=
  Localization.AtPrime
    (Ideal.span ({Polynomial.X} : Set (Polynomial k)))

-- The completed local ring, using its canonical maximal-ideal adic completion.
abbrev chapter07PolynomialLocalCompletion (k : Type*) [Field k] : Type _ :=
  AdicCompletion (IsLocalRing.maximalIdeal (chapter07PolynomialLocalRing k))
    (chapter07PolynomialLocalRing k)

-- Laurent series are complete for the X-adic valuation.
theorem chapter07_laurent_series_are_complete
    (k : Type*) [Field k] :
    CompleteSpace (chapter07LaurentSeriesField k) := by
  sorry

-- Rational functions are dense in Laurent series.
theorem chapter07_rational_functions_are_dense_in_laurent_series
    (k : Type*) [Field k] :
    DenseRange
      ((↑) : chapter07RationalFunctionField k →
        chapter07LaurentSeriesField k) := by
  sorry

-- The rational-function completion is identified with the Laurent-series field.
def chapter07RationalFunctionAdicToLaurentSeries
    (k : Type*) [Field k] :
    chapter07RationalFunctionAdicCompletion k ≃+*
      chapter07LaurentSeriesField k :=
  LaurentSeries.ratfuncAdicComplRingEquiv k

-- Section 7.6: completion of k(t) for the t-adic valuation gives k((t)).
theorem chapter07_rational_function_completion_is_laurent_series
    (k : Type*) [Field k] :
    Nonempty
      (chapter07RationalFunctionAdicCompletion k ≃+*
        chapter07LaurentSeriesField k) := by
  sorry

-- The completed local valuation ring is identified with k[[t]].
def chapter07PowerSeriesToPolynomialLocalCompletion
    (k : Type*) [Field k] :
    Prop :=
  ∃ e : chapter07PowerSeriesRing k ≃+* chapter07PolynomialLocalCompletion k,

    ∀ p : Polynomial k,
      e (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (IsLocalRing.maximalIdeal (chapter07PolynomialLocalRing k))
          (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k) p)
-- The same local identification as an algebra equivalence.
def chapter07PowerSeriesAlgebraToPolynomialLocalCompletion
    (k : Type*) [Field k] :
    Prop :=
  ∃ e : chapter07PowerSeriesRing k ≃ₐ[k] chapter07PolynomialLocalCompletion k,
    ∀ p : Polynomial k,
      e (p : chapter07PowerSeriesRing k) =
        chapter07AdicCompletionMap (IsLocalRing.maximalIdeal (chapter07PolynomialLocalRing k))
          (algebraMap (Polynomial k) (chapter07PolynomialLocalRing k) p)

-- Section 7.6: completion of k[t]_(t) gives k[[t]].
theorem chapter07_polynomial_local_completion_is_power_series
    (k : Type*) [Field k] :
    chapter07PowerSeriesToPolynomialLocalCompletion k ∧
      chapter07PowerSeriesAlgebraToPolynomialLocalCompletion k := by
  sorry

-- Truncation of a power series to a polynomial, viewed again as a power series.
def chapter07PowerSeriesTruncation
    {k : Type*} [Field k] (n : ℕ) (f : chapter07PowerSeriesRing k) :
    chapter07PowerSeriesRing k :=
  (PowerSeries.trunc n f : chapter07PowerSeriesRing k)

-- Power-series truncations stabilize each coefficient, the canonical X-adic statement.
theorem chapter07_power_series_truncations_converge
    {k : Type*} [Field k] (f : chapter07PowerSeriesRing k) :
    ∀ d : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      PowerSeries.coeff d (chapter07PowerSeriesTruncation n f) = PowerSeries.coeff d f := by
  sorry

-- A Cauchy Laurent-series filter has an eventually fixed coefficient at each degree.
theorem chapter07_laurent_cauchy_coefficients_eventually_stabilize
    (k : Type*) [Field k] {ℱ : Filter (chapter07LaurentSeriesField k)}
    (hℱ : Cauchy ℱ) (D : ℤ) :
    ∀ᶠ f in ℱ, ∀ d : ℤ, d < D →
      LaurentSeries.Cauchy.coeff hℱ d = f.coeff d := by
  sorry

-- The coefficient sequence attached to a Laurent Cauchy filter has a uniform lower bound.
theorem chapter07_laurent_cauchy_limit_has_uniform_lower_bound
    (k : Type*) [Field k] {ℱ : Filter (chapter07LaurentSeriesField k)}
    (hℱ : Cauchy ℱ) :
    ∃ N : ℤ, ∀ d : ℤ, d < N →
      (LaurentSeries.Cauchy.limit hℱ).coeff d = 0 := by
  sorry

-- The Laurent-series Cauchy limit is the coefficientwise limit constructed from stabilization.
theorem chapter07_laurent_cauchy_limit_is_a_laurent_series
    (k : Type*) [Field k] {ℱ : Filter (chapter07LaurentSeriesField k)}
    (hℱ : Cauchy ℱ) :
    ∀ d : ℤ,
      (LaurentSeries.Cauchy.limit hℱ).coeff d =
        LaurentSeries.Cauchy.coeff hℱ d := by
  sorry

-- Rational truncations approximate every Laurent series in the valuation topology.
theorem chapter07_laurent_series_have_rational_approximations
    (k : Type*) [Field k] (f : chapter07LaurentSeriesField k) :
    f ∈ closure
      (Set.range ((↑) : chapter07RationalFunctionField k →
        chapter07LaurentSeriesField k)) := by
  sorry

/-! ### 7.6. The chosen valuation controls the completion -/

-- Completion as a construction parameterized by the chosen uniformity.
def chapter07CompletionForUniformity
    (K : Type*) (u : UniformSpace K) : Type _ :=
  @UniformSpace.Completion K u

-- The completion construction remembers the chosen uniformity.
theorem chapter07_completion_is_parameterized_by_uniformity
    (K : Type*) (u : UniformSpace K) :
    chapter07CompletionForUniformity K u = @UniformSpace.Completion K u := by
  sorry

abbrev chapter07ArchimedeanRationalCompletion : Type _ :=
  ℝ

-- The usual completion of ℚ is the real field.
theorem chapter07_rationals_have_real_completion :
    Nonempty (UniformSpace.Completion ℚ ≃ᵤ
      chapter07ArchimedeanRationalCompletion) := by
  sorry

-- The same abstract field ℚ has the distinct p-adic completion with p-adic uniformity.
theorem chapter07_rationals_have_padic_completion
    (p : ℕ) [Fact p.Prime] :
    Nonempty
      (@UniformSpace.Completion ℚ (chapter07PAdicUniformSpace p) ≃ᵤ
        chapter07PAdicField p) := by
  sorry

-- Completion magnifies one chosen notion of nearness and does not canonically retain
-- completions for other uniformities.
theorem chapter07_completion_is_local_to_the_chosen_valuation
    (K : Type*) (u : UniformSpace K) :
    DenseRange (@UniformSpace.Completion.coe' K u) ∧
      @CompleteSpace (@UniformSpace.Completion K u)
        (@UniformSpace.Completion.uniformSpace K u) := by
  sorry

end
end ValuationsBook.Chapter07
