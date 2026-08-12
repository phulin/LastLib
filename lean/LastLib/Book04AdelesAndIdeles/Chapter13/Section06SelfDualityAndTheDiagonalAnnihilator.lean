import Mathlib.Topology.Order
import Mathlib.Algebra.Group.TransferInstance
import LastLib.Book04AdelesAndIdeles.Chapter13.Section05TheStandardAdditiveCharacter

open scoped NumberField NumberField.AdeleRing RestrictedProduct

namespace LastLib.Book04AdelesAndIdeles.Chapter13

noncomputable section

instance chapter13WithDiscreteTopologyCommGroup
    (G : Type*) [CommGroup G] :
    CommGroup (WithDiscreteTopology G) :=
  (WithTopology.equiv G (⊥ : TopologicalSpace G)).commGroup

instance chapter13WithDiscreteTopologyAddCommGroup
    (G : Type*) [AddCommGroup G] :
    AddCommGroup (WithDiscreteTopology G) :=
  (WithTopology.equiv G (⊥ : TopologicalSpace G)).addCommGroup

/-!
## 13.6 Self-duality and the diagonal annihilator
-/

def chapter13RightMultiplicationAddMonoidHom
    {A : Type*} [NonUnitalNonAssocRing A] (y : A) : A →+ A :=
  { toFun := fun x => x * y
    map_zero' := by sorry
    map_add' := by sorry }

def chapter13ContinuousAddCharToDual
    {A : Type*} [NonUnitalNonAssocRing A] [TopologicalSpace A]
    (ψ : AddChar A Circle) (hψ : Continuous ψ) : Chapter13AdditiveDual A :=
  Additive.ofMul
    { toMonoidHom := ψ.toMonoidHom
      continuous_toFun := hψ }

def chapter13PairingCharacter
    {A : Type*} [NonUnitalNonAssocRing A] [TopologicalSpace A]
    (ψ : AddChar A Circle) (hψ : Continuous ψ) (y : A) :
    Chapter13AdditiveDual A :=
  chapter13ContinuousAddCharToDual
    (ψ.compAddMonoidHom (chapter13RightMultiplicationAddMonoidHom y))
    (by sorry)

theorem chapter13PairingCharacter_apply
    {A : Type*} [NonUnitalNonAssocRing A] [TopologicalSpace A]
    (ψ : AddChar A Circle) (hψ : Continuous ψ) (y x : A) :
    chapter13PairingCharacter ψ hψ y x = ψ (x * y) :=
  rfl

def chapter13RealAdditiveCharacterAt (y : ℝ) : Chapter13AdditiveDual ℝ :=
  chapter13PairingCharacter Real.fourierChar Real.continuous_fourierChar y

theorem chapter13_real_additive_character_at_apply (x y : ℝ) :
    chapter13RealAdditiveCharacterAt y x = Real.fourierChar (x * y) :=
  rfl

theorem chapter13_real_continuous_additive_character_classification
    (χ : Chapter13AdditiveDual ℝ) :
    ∃! y : ℝ, χ = chapter13RealAdditiveCharacterAt y := by
  sorry

def chapter13ComplexPairingAddMonoidHom (y : ℂ) : ℂ →+ ℝ :=
  { toFun := fun x => chapter13ComplexTracePairing x y
    map_zero' := by sorry
    map_add' := by sorry }

def chapter13ComplexPairingAddChar (y : ℂ) : AddChar ℂ Circle :=
  Real.fourierChar.compAddMonoidHom (chapter13ComplexPairingAddMonoidHom y)

def chapter13ComplexAdditiveCharacterAt (y : ℂ) : Chapter13AdditiveDual ℂ :=
  chapter13ContinuousAddCharToDual (chapter13ComplexPairingAddChar y) (by sorry)

theorem chapter13_complex_additive_character_at_apply (x y : ℂ) :
    chapter13ComplexAdditiveCharacterAt y x =
      Circle.exp (2 * Real.pi * chapter13ComplexTracePairing x y) := by
  sorry

theorem chapter13_complex_continuous_additive_character_classification
    (χ : Chapter13AdditiveDual ℂ) :
    ∃! y : ℂ, χ = chapter13ComplexAdditiveCharacterAt y := by
  sorry

/- DEPENDENCY_GUESS: instantiate the local-field completeness and inverse-limit argument from the
earlier completion chapters for the concrete trace pairing; the data structure deliberately stores
only the pairing and its elementary nondegeneracy properties. -/

theorem chapter13_local_additive_character_classification_from_data
    {F : Type*} [Field F] [TopologicalSpace F]
    (D : Chapter13LocalSelfDualityData F)
    (χ : AddChar F Circle) (hχ : Continuous χ) :
    ∃! y : F, ∀ x, χ x = D.pairing x y := by
  sorry

theorem chapter13_local_self_duality_from_data
    {F : Type*} [Field F] [TopologicalSpace F]
    (D : Chapter13LocalSelfDualityData F) :
    Nonempty (F ≃ₜ+ Chapter13AdditiveDual F) := by
  sorry

def chapter13FinitePairingIsPerfect
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (pair : A → B → Circle) : Prop :=
  (∀ a, (∀ b, pair a b = 1) → a = 0) ∧
    (∀ b, (∀ a, pair a b = 1) → b = 0)

theorem chapter13_finite_trace_pairing_perfect_from_nondegeneracy
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B]
    (q r m : ℕ) (pair : A → B → Circle)
    (_hcardA : Fintype.card A = q ^ (r + m))
    (_hcardB : Fintype.card B = q ^ (r + m))
    (hleft : ∀ a, (∀ b, pair a b = 1) → a = 0)
    (hright : ∀ b, (∀ a, pair a b = 1) → b = 0) :
    chapter13FinitePairingIsPerfect pair := by
  exact ⟨hleft, hright⟩

/-!
The preceding finite interface is the book's local statement for
`π⁻ʳ O / πᵐ O` paired with `π⁻ᵐ D⁻¹ / πʳ D⁻¹`; the later fixup pass can instantiate `A` and `B`
with the canonical valuation-ring quotients from Chapters 05--08.
-/

def chapter13DiagonalAdditiveSubgroup
    (K : Type*) [Field K] [NumberField K] : AddSubgroup (Chapter13Adele K) :=
  NumberField.AdeleRing.principalSubgroup (R := 𝓞 K) (K := K)

abbrev Chapter13AdditiveAdelicQuotient (K : Type*) [Field K] [NumberField K] :=
  Chapter13Adele K ⧸ chapter13DiagonalAdditiveSubgroup K

def chapter13AdelicDualMap
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    Chapter13Adele K →ₜ+ Chapter13AdditiveDual (Chapter13Adele K) :=
  { toAddMonoidHom :=
      { toFun := fun y =>
          chapter13PairingCharacter
            (chapter13StandardAdditiveCharacter K D)
            (chapter13StandardAdditiveCharacter_continuous K D) y
        map_zero' := by sorry
        map_add' := by sorry }
    continuous_toFun := by sorry }

theorem chapter13_adelic_dual_map_apply
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) (x y : Chapter13Adele K) :
    chapter13AdelicDualMap K D y x =
      chapter13StandardAdditiveCharacter K D (x * y) :=
  rfl

structure Chapter13AdelicLocalParameterData
    (K : Type*) [Field K] [NumberField K] where
  parameter :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), v.adicCompletion K
  inverseDifferent :
    ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K)
  integral_tail : ∀ᶠ v in Filter.cofinite, parameter v ∈ inverseDifferent v

theorem chapter13_global_character_parameters_are_adeles
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (χ : Chapter13AdditiveDual (Chapter13Adele K)) :
    ∃ y : Chapter13Adele K,
      χ = chapter13AdelicDualMap K D y := by
  sorry

theorem chapter13_global_character_has_local_trace_dual_tail
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (χ : Chapter13AdditiveDual (Chapter13Adele K)) :
    ∃ y : Chapter13Adele K,
      χ = chapter13AdelicDualMap K D y ∧
        ∃ P : Chapter13AdelicLocalParameterData K,
          (∀ v, P.parameter v = y.2 v) := by
  sorry

theorem chapter13_global_character_parameter_unique
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    {y z : Chapter13Adele K}
    (h : chapter13AdelicDualMap K D y = chapter13AdelicDualMap K D z) :
    y = z := by
  sorry

theorem chapter13_adelic_self_duality
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    Nonempty
      (Chapter13Adele K ≃ₜ+ Chapter13AdditiveDual (Chapter13Adele K)) := by
  sorry

theorem chapter13_adelic_dual_map_is_topological_equivalence
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    ∃ e : Chapter13Adele K ≃ₜ+ Chapter13AdditiveDual (Chapter13Adele K),
      ∀ y, e y = chapter13AdelicDualMap K D y := by
  sorry

def chapter13DiagonalAnnihilator
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) : AddSubgroup (Chapter13Adele K) :=
  chapter13AdditiveAnnihilator
    (chapter13StandardAdditiveCharacter K D) (chapter13DiagonalAdditiveSubgroup K)

theorem chapter13_diagonal_annihilator_forward
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    chapter13DiagonalAdditiveSubgroup K ≤ chapter13DiagonalAnnihilator K D := by
  sorry

theorem chapter13_diagonal_annihilator_reverse_by_approximation
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    chapter13DiagonalAnnihilator K D ≤ chapter13DiagonalAdditiveSubgroup K := by
  sorry

theorem chapter13_diagonal_annihilator_eq_diagonal
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    chapter13DiagonalAnnihilator K D = chapter13DiagonalAdditiveSubgroup K := by
  apply le_antisymm
  · exact chapter13_diagonal_annihilator_reverse_by_approximation K D
  · exact chapter13_diagonal_annihilator_forward K D

theorem chapter13_adelic_quotient_is_compact
    (K : Type*) [Field K] [NumberField K] :
    IsCompact (Set.univ : Set (Chapter13AdditiveAdelicQuotient K)) := by
  sorry

def chapter13DescendAdditiveCharacterToAdelicQuotient
    (K : Type*) [Field K] [NumberField K]
    (ψ : AddChar (Chapter13Adele K) Circle)
    (hψ : ∀ x : chapter13DiagonalAdditiveSubgroup K, ψ x = 1) :
    AddChar (Chapter13AdditiveAdelicQuotient K) Circle :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (chapter13DiagonalAdditiveSubgroup K)
      ψ.toAddMonoidHom (by
        intro x hx
        change ψ x = 1
        exact hψ ⟨x, hx⟩))

theorem chapter13DescendAdditiveCharacterToAdelicQuotient_apply
    (K : Type*) [Field K] [NumberField K]
    (ψ : AddChar (Chapter13Adele K) Circle)
    (hψ : ∀ x : chapter13DiagonalAdditiveSubgroup K, ψ x = 1)
    (x : Chapter13Adele K) :
    chapter13DescendAdditiveCharacterToAdelicQuotient K ψ hψ (x : Chapter13AdditiveAdelicQuotient K) =
      ψ x :=
  rfl

theorem chapter13_additive_quotient_character_iff_trivial_on_diagonal
    (K : Type*) [Field K] [NumberField K]
    (χ : AddChar (Chapter13Adele K) Circle) (hχ : Continuous χ) :
    (∃ ψ : AddChar (Chapter13AdditiveAdelicQuotient K) Circle,
      Continuous ψ ∧
        ∀ x : Chapter13Adele K,
          ψ (x : Chapter13AdditiveAdelicQuotient K) = χ x) ↔
      ∀ x : chapter13DiagonalAdditiveSubgroup K, χ x = 1 := by
  sorry

theorem chapter13_quotient_dual_is_the_diagonal_field
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    Nonempty
      (Chapter13AdditiveDual (Chapter13AdditiveAdelicQuotient K) ≃ₜ+
        WithDiscreteTopology K) := by
  sorry

theorem chapter13_quotient_character_is_trivial_on_diagonal
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K)
    (χ : Chapter13AdditiveDual (Chapter13Adele K))
    (hχ : ∀ x : chapter13DiagonalAdditiveSubgroup K,
      (Additive.toMul χ) (Multiplicative.ofAdd (x : Chapter13Adele K)) = 1) :
    ∃ ψ : Chapter13AdditiveDual (Chapter13AdditiveAdelicQuotient K),
      ∀ x : Chapter13Adele K,
        ψ (x : Chapter13AdditiveAdelicQuotient K) = χ x := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter13
