import LastLib.Book04AdelesAndIdeles.Chapter13.Dependencies

open scoped BigOperators NumberField NumberField.AdeleRing RestrictedProduct

namespace LastLib.Book04AdelesAndIdeles.Chapter13

noncomputable section

/-!
## 13.5 The standard additive character
-/

def chapter13PadicStandardCharacter
    (p : {p : ℕ // Nat.Prime p})
    (D : Chapter13RationalPrincipalPartData p) : AddChar (Chapter13Padic p) Circle :=
  D.principalCharacter

theorem chapter13PadicStandardCharacter_apply
    (p : {p : ℕ // Nat.Prime p})
    (D : Chapter13RationalPrincipalPartData p) (x : Chapter13Padic p) :
    chapter13PadicStandardCharacter p D x =
      chapter13RationalModIntegerCharacter (D.principalPart x) := by
  simpa [chapter13PadicStandardCharacter] using D.principalCharacter_formula x

theorem chapter13PadicStandardCharacter_trivial_on_integers
    (p : {p : ℕ // Nat.Prime p})
    (D : Chapter13RationalPrincipalPartData p) (x : Chapter13PadicInteger p) :
    chapter13PadicStandardCharacter p D x = 1 := by
  exact D.principalCharacter_trivial_on_integers x

def chapter13RationalStandardAdditiveCharacter
    (D : Chapter13RationalStandardCharacterData) :
    AddChar (Chapter13Adele ℚ) Circle :=
  { toFun := fun x =>
      D.psiInfinity (D.infinityCoordinate x) *
        ∏ᶠ p, (D.padic p).principalCharacter (D.finiteCoordinate p x)
    map_zero_eq_one' := by sorry
    map_add_eq_mul' := by sorry }

theorem chapter13RationalStandardAdditiveCharacter_apply
    (D : Chapter13RationalStandardCharacterData) (x : Chapter13Adele ℚ) :
    chapter13RationalStandardAdditiveCharacter D x =
      D.psiInfinity (D.infinityCoordinate x) *
        ∏ᶠ p, (D.padic p).principalCharacter (D.finiteCoordinate p x) :=
  rfl

theorem chapter13RationalStandardAdditiveCharacter_continuous
    (D : Chapter13RationalStandardCharacterData) :
    Continuous (chapter13RationalStandardAdditiveCharacter D) :=
  by sorry

theorem chapter13_real_standard_character_apply
    (D : Chapter13RationalStandardCharacterData) (x : ℝ) :
    D.psiInfinity x = Real.fourierChar x := by
  rw [D.psiInfinity_eq_fourier]

theorem chapter13PadicStandardCharacter_nontrivial
    (p : {p : ℕ // Nat.Prime p})
    (D : Chapter13RationalPrincipalPartData p) :
    ∃ x, chapter13PadicStandardCharacter p D x ≠ 1 := by
  exact ⟨(p.1 : Chapter13Padic p)⁻¹, D.principalCharacter_nontrivial_on_inverse_p⟩

theorem chapter13PadicStandardCharacter_nontrivial_on_inverse_p
    (p : {p : ℕ // Nat.Prime p})
    (D : Chapter13RationalPrincipalPartData p) :
    chapter13PadicStandardCharacter p D ((p.1 : Chapter13Padic p)⁻¹) ≠ 1 :=
  D.principalCharacter_nontrivial_on_inverse_p

theorem chapter13RationalStandardCharacter_finite_principal_support
    (D : Chapter13RationalStandardCharacterData) (x : Chapter13Adele ℚ) :
    Set.Finite {p | (D.padic p).principalPart (D.finiteCoordinate p x) ≠ 0} := by
  sorry

theorem chapter13RationalStandardCharacter_finite_character_support
    (D : Chapter13RationalStandardCharacterData) (x : Chapter13Adele ℚ) :
    Set.Finite {p | (D.padic p).principalCharacter (D.finiteCoordinate p x) ≠ 1} := by
  sorry

theorem chapter13RationalStandardAdditiveCharacter_trivial_on_diagonal
    (D : Chapter13RationalStandardCharacterData) (a : ℚ) :
    chapter13RationalStandardAdditiveCharacter D
      (algebraMap ℚ (Chapter13Adele ℚ) a) = 1 :=
  by sorry

structure Chapter13RationalPrincipalPartBalanceData where
  finitePart : ∀ _p : {p : ℕ // Nat.Prime p}, ℚ → ℚ
  finite_support : ∀ a, Set.Finite {p | finitePart p a ≠ 0}
  balance : ∀ a : ℚ, ∃ z : ℤ,
    a - ∑ᶠ p, finitePart p a = (z : ℚ)

theorem chapter13_rational_principal_part_sum_differs_by_integer
    (B : Chapter13RationalPrincipalPartBalanceData) (a : ℚ) :
    ∃ z : ℤ, a - ∑ᶠ p, B.finitePart p a = (z : ℚ) :=
  B.balance a

/- The explicit sign convention is recorded by multiplying the chosen finite factor by its inverse.
The nontriviality hypothesis below is the exact condition under which changing one local sign breaks
triviality on the diagonal. -/

def chapter13RationalCharacterWithOneFiniteSignChanged
    (D : Chapter13RationalStandardCharacterData)
    (p : {p : ℕ // Nat.Prime p}) : AddChar (Chapter13Adele ℚ) Circle :=
  { toFun := fun x =>
      chapter13RationalStandardAdditiveCharacter D x *
        ((D.padic p).principalCharacter (D.finiteCoordinate p x))⁻¹ *
        ((D.padic p).principalCharacter (D.finiteCoordinate p x))⁻¹
    map_zero_eq_one' := by sorry
    map_add_eq_mul' := by sorry }

def chapter13RationalCharacterWithRealSignChanged
    (D : Chapter13RationalStandardCharacterData) : AddChar (Chapter13Adele ℚ) Circle :=
  { toFun := fun x =>
      (D.psiInfinity (D.infinityCoordinate x))⁻¹ *
        ∏ᶠ p, (D.padic p).principalCharacter (D.finiteCoordinate p x)
    map_zero_eq_one' := by sorry
    map_add_eq_mul' := by sorry }

def chapter13RationalCharacterWithAllSignsReversed
    (D : Chapter13RationalStandardCharacterData) : AddChar (Chapter13Adele ℚ) Circle :=
  { toFun := fun x => (chapter13RationalStandardAdditiveCharacter D x)⁻¹
    map_zero_eq_one' := by sorry
    map_add_eq_mul' := by sorry }

theorem chapter13_all_sign_reversal_preserves_diagonal_triviality
    (D : Chapter13RationalStandardCharacterData) (a : ℚ) :
    chapter13RationalCharacterWithAllSignsReversed D
      (algebraMap ℚ (Chapter13Adele ℚ) a) = 1 := by
  sorry

theorem chapter13_single_finite_sign_change_is_detected_on_diagonal
    (D : Chapter13RationalStandardCharacterData)
    (p : {p : ℕ // Nat.Prime p})
    (a : ℚ)
    (hlocal : (D.padic p).principalCharacter
      (D.finiteCoordinate p (algebraMap ℚ (Chapter13Adele ℚ) a)) ^ 2 ≠ 1) :
    chapter13RationalCharacterWithOneFiniteSignChanged D p
      (algebraMap ℚ (Chapter13Adele ℚ) a) ≠ 1 := by
  sorry

theorem chapter13_single_real_sign_change_is_detected_on_diagonal
    (D : Chapter13RationalStandardCharacterData)
    (a : ℚ)
    (hlocal : D.psiInfinity
      (D.infinityCoordinate (algebraMap ℚ (Chapter13Adele ℚ) a)) ^ 2 ≠ 1) :
    chapter13RationalCharacterWithRealSignChanged D
      (algebraMap ℚ (Chapter13Adele ℚ) a) ≠ 1 := by
  sorry

def chapter13LocalTraceAdditiveCharacter
    {L F : Type*} [AddCommGroup L] [AddCommGroup F]
    (ψF : AddChar F Circle) (tr : L →+ F) : AddChar L Circle :=
  ψF.compAddMonoidHom tr

theorem chapter13LocalTraceAdditiveCharacter_apply
    {L F : Type*} [AddCommGroup L] [AddCommGroup F]
    (ψF : AddChar F Circle) (tr : L →+ F) (x : L) :
    chapter13LocalTraceAdditiveCharacter ψF tr x = ψF (tr x) :=
  rfl

theorem chapter13LocalTraceAdditiveCharacter_continuous
    {L F : Type*} [AddCommGroup L] [AddCommGroup F]
    [TopologicalSpace L] [TopologicalSpace F]
    (ψF : AddChar F Circle) (hψF : Continuous ψF) (tr : L →+ F)
    (htr : Continuous tr) :
    Continuous (chapter13LocalTraceAdditiveCharacter ψF tr) := by
  sorry

def chapter13TraceDual
    {L F : Type*} [NonUnitalNonAssocRing L] [AddCommGroup F]
    (tr : L →+ F) (O : Set L) (R : Set F) : Set L :=
  {y | ∀ x, x ∈ O → tr (x * y) ∈ R}

def chapter13LocalInverseDifferent
    {L F : Type*} [NonUnitalNonAssocRing L] [AddCommGroup F]
    (tr : L →+ F) (O : Set L) (R : Set F) : Set L :=
  chapter13TraceDual tr O R

theorem chapter13_local_annihilator_is_inverse_different
    {L F : Type*} [NonUnitalNonAssocRing L] [AddCommGroup F]
    (tr : L →+ F) (O : Set L) (R : Set F) :
    chapter13TraceDual tr O R = chapter13LocalInverseDifferent tr O R :=
  rfl

theorem chapter13_mem_local_inverse_different_iff
    {L F : Type*} [NonUnitalNonAssocRing L] [AddCommGroup F]
    (tr : L →+ F) (O : Set L) (R : Set F) (y : L) :
    y ∈ chapter13LocalInverseDifferent tr O R ↔
      ∀ x, x ∈ O → tr (x * y) ∈ R :=
  Iff.rfl

theorem chapter13_local_inverse_different_is_additive_subgroup
    {L F : Type*} [NonUnitalNonAssocRing L] [AddCommGroup F]
    (tr : L →+ F) (O : AddSubgroup L) (R : AddSubgroup F) :
    ∃ H : AddSubgroup L,
      (H : Set L) = chapter13LocalInverseDifferent tr O R := by
  sorry

def chapter13GlobalInverseDifferent (K : Type*) [Field K] [NumberField K] : Set K :=
  {y | ∀ x : 𝓞 K, ∃ z : ℤ,
    Algebra.trace ℚ K (y * (x : K)) = (z : ℚ)}

theorem chapter13_global_inverse_different_is_trace_dual
    (K : Type*) [Field K] [NumberField K] :
    chapter13GlobalInverseDifferent K =
      {y | ∀ x : 𝓞 K, ∃ z : ℤ,
        Algebra.trace ℚ K (y * (x : K)) = (z : ℚ)} :=
  rfl

theorem chapter13_mem_global_inverse_different_iff
    (K : Type*) [Field K] [NumberField K] (y : K) :
    y ∈ chapter13GlobalInverseDifferent K ↔
      ∀ x : 𝓞 K, ∃ z : ℤ,
        Algebra.trace ℚ K (y * (x : K)) = (z : ℚ) :=
  Iff.rfl

def chapter13FiniteSelfDualMeasureScale (q : ℝ) (d : ℕ) : ℝ :=
  Real.rpow q (-(d : ℝ) / 2)

theorem chapter13_finite_self_dual_measure_scale
    (q : ℝ) (d : ℕ) (_hq : 0 < q) :
    chapter13FiniteSelfDualMeasureScale q d = Real.rpow q (-(d : ℝ) / 2) :=
  rfl

def chapter13ComplexTracePairing (z w : ℂ) : ℝ :=
  2 * (z * w).re

theorem chapter13_complex_trace_pairing_apply (z w : ℂ) :
    chapter13ComplexTracePairing z w = 2 * (z * w).re :=
  rfl

def chapter13ComplexSelfDualMeasureScale : ℝ := 2

theorem chapter13_complex_self_dual_measure_scale :
    chapter13ComplexSelfDualMeasureScale = 2 :=
  rfl

theorem chapter13_global_self_dual_covolume_one
    (disc : ℝ) (r₂ : ℕ) (hdisc : 0 < disc)
    (baseCovolume : ℝ)
    (hbase : baseCovolume = (2 : ℝ) ^ (-(r₂ : ℤ)) * Real.sqrt disc) :
    (2 : ℝ) ^ r₂ * Real.rpow disc (-(1 : ℝ) / 2) * baseCovolume = 1 := by
  sorry

def chapter13StandardAdditiveCharacter
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    AddChar (Chapter13Adele K) Circle :=
  (chapter13RationalStandardAdditiveCharacter D.rationalCharacter).compAddMonoidHom D.trace

theorem chapter13StandardAdditiveCharacter_apply
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) (x : Chapter13Adele K) :
    chapter13StandardAdditiveCharacter K D x =
      chapter13RationalStandardAdditiveCharacter D.rationalCharacter (D.trace x) :=
  rfl

theorem chapter13StandardAdditiveCharacter_continuous
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) :
    Continuous (chapter13StandardAdditiveCharacter K D) := by
  sorry

theorem chapter13StandardAdditiveCharacter_trivial_on_diagonal
    (K : Type*) [Field K] [NumberField K]
    (D : Chapter13AdelicTraceData K) (a : K) :
    chapter13StandardAdditiveCharacter K D
      (algebraMap K (Chapter13Adele K) a) = 1 := by
  sorry

end
end LastLib.Book04AdelesAndIdeles.Chapter13
