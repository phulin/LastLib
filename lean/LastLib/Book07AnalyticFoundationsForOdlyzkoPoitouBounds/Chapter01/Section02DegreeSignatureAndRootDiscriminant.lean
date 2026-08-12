import LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01.Section01TheProblemAndTheScale

namespace LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01

noncomputable section

open NumberField

/-! ## 1.2. Degree, signature, and root discriminant -/

noncomputable def chapter01RealPlaces
    (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrRealPlaces K

noncomputable def chapter01ComplexPlaces
    (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.InfinitePlace.nrComplexPlaces K

theorem chapter01_signature_identity
    (K : Type*) [Field K] [NumberField K] :
    chapter01Degree K = chapter01RealPlaces K + 2 * chapter01ComplexPlaces K := by
  exact (NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K).symm

theorem chapter01_realPlaces_le_degree
    (K : Type*) [Field K] [NumberField K] :
    chapter01RealPlaces K ≤ chapter01Degree K := by
  obtain ⟨r₂, h⟩ := show ∃ r₂ : ℕ,
      chapter01Degree K = chapter01RealPlaces K + 2 * r₂ from
    ⟨chapter01ComplexPlaces K, chapter01_signature_identity K⟩
  omega

theorem chapter01_signed_discriminant_sign
    (K : Type*) [Field K] [NumberField K] :
    (NumberField.discr K).sign = (-1 : ℤ) ^ chapter01ComplexPlaces K := by
  exact NumberField.sign_discr K

theorem chapter01AbsoluteDiscriminant_eq_natAbs
    (K : Type*) [Field K] [NumberField K] :
    chapter01AbsoluteDiscriminant K = (NumberField.discr K).natAbs := by
  sorry

theorem chapter01AbsoluteDiscriminant_eq_absolute_different_norm
    (K : Type*) [Field K] [NumberField K] :
    chapter01AbsoluteDiscriminant K =
      (Ideal.absNorm
        (differentIdeal ℤ (NumberField.RingOfIntegers K)) : ℝ) := by
  sorry

theorem chapter01AbsoluteDiscriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter01AbsoluteDiscriminant K := by
  sorry

def chapter01ValidSignature (n r₁ : ℕ) : Prop :=
  ∃ r₂ : ℕ, n = r₁ + 2 * r₂

theorem chapter01_signature_is_valid
    (K : Type*) [Field K] [NumberField K] :
    chapter01ValidSignature (chapter01Degree K) (chapter01RealPlaces K) := by
  exact ⟨chapter01ComplexPlaces K, chapter01_signature_identity K⟩

theorem chapter01ValidSignature_real_le_degree
    {n r₁ : ℕ} (h : chapter01ValidSignature n r₁) : r₁ ≤ n := by
  obtain ⟨r₂, rfl⟩ := h
  omega

/- The real proportion records exactly the signature statistic used by the
   analytic bounds. -/
noncomputable def chapter01RealProportion
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  (chapter01RealPlaces K : ℝ) / chapter01Degree K

theorem chapter01RealProportion_nonneg
    (K : Type*) [Field K] [NumberField K] :
    0 ≤ chapter01RealProportion K := by
  sorry

theorem chapter01RealProportion_le_one
    (K : Type*) [Field K] [NumberField K] :
    chapter01RealProportion K ≤ 1 := by
  sorry

def chapter01TotallyReal
    (K : Type*) [Field K] [NumberField K] : Prop :=
  chapter01RealPlaces K = chapter01Degree K

def chapter01TotallyComplex
    (K : Type*) [Field K] [NumberField K] : Prop :=
  chapter01RealPlaces K = 0

def chapter01UnrestrictedSignature
    (K : Type*) [Field K] [NumberField K] : Prop :=
  chapter01TotallyComplex K

theorem chapter01RealProportion_eq_zero_iff
    (K : Type*) [Field K] [NumberField K] :
    chapter01RealProportion K = 0 ↔ chapter01TotallyComplex K := by
  sorry

theorem chapter01RealProportion_eq_zero_iff_unrestricted
    (K : Type*) [Field K] [NumberField K] :
    chapter01RealProportion K = 0 ↔ chapter01UnrestrictedSignature K := by
  sorry

theorem chapter01RealProportion_eq_one_iff
    (K : Type*) [Field K] [NumberField K] :
    chapter01RealProportion K = 1 ↔ chapter01TotallyReal K := by
  sorry

theorem chapter01_rootDiscriminant_uses_absolute_discriminant
    (K : Type*) [Field K] [NumberField K] :
    chapter01RootDiscriminant K =
      chapter01AbsoluteDiscriminant K ^ (chapter01Degree K : ℝ)⁻¹ :=
  rfl

/- The completed zeta package later in the book receives the same absolute
   discriminant parameter, rather than the signed integer discriminant. -/
def chapter01CompletedZetaDiscriminantParameter
    (K : Type*) [Field K] [NumberField K] : ℝ :=
  chapter01AbsoluteDiscriminant K

@[simp]
theorem chapter01CompletedZetaDiscriminantParameter_def
    (K : Type*) [Field K] [NumberField K] :
    chapter01CompletedZetaDiscriminantParameter K =
      chapter01AbsoluteDiscriminant K :=
  rfl

/- A signature summary intentionally contains no involution or Galois datum:
   the analytic input in this chapter is the pair `(r₁,r₂)` and its degree
   identity. -/
structure Chapter01SignatureSummary where
  degree : ℕ
  realPlaces : ℕ
  complexPlaces : ℕ
  degree_eq : degree = realPlaces + 2 * complexPlaces

def chapter01SignatureSummary
    (K : Type*) [Field K] [NumberField K] : Chapter01SignatureSummary where
  degree := chapter01Degree K
  realPlaces := chapter01RealPlaces K
  complexPlaces := chapter01ComplexPlaces K
  degree_eq := chapter01_signature_identity K

@[ext]
theorem Chapter01SignatureSummary.ext
    {S T : Chapter01SignatureSummary}
    (hdegree : S.degree = T.degree)
    (hreal : S.realPlaces = T.realPlaces)
    (hcomplex : S.complexPlaces = T.complexPlaces) :
    S = T := by
  cases S
  cases T
  simp_all

/- The relative different and its absolute norm are the canonical realization
   of the book's `𝔡_{L/K}` and `N_{K/ℚ}(𝔡_{L/K})`. -/
noncomputable def chapter01RelativeDifferentIdeal
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] : Ideal (NumberField.RingOfIntegers L) :=
  differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)

noncomputable def chapter01RelativeDifferentNorm
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] : ℕ :=
  Ideal.absNorm (chapter01RelativeDifferentIdeal K L)

theorem chapter01RelativeDifferentNorm_pos
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] :
    0 < chapter01RelativeDifferentNorm K L := by
  sorry

/- `L/K` is unramified at every finite prime of the base ring.  Quantifying
   over maximal base ideals keeps the finite-place convention explicit while
   using Mathlib's canonical `IsUnramifiedIn` predicate. -/
def chapter01UnramifiedAtFinitePrimes
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] : Prop :=
  ∀ (p : Ideal (NumberField.RingOfIntegers K)), p.IsMaximal →
    Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) p

theorem chapter01_unramifiedAtFinitePrimes_iff_relativeDifferentNorm_eq_one
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] :
    chapter01UnramifiedAtFinitePrimes K L ↔
      chapter01RelativeDifferentNorm K L = 1 := by
  sorry

/- Discriminant transitivity in the source order.  The displayed identity is
   stated over `ℝ`, while the canonical Mathlib theorem is the corresponding
   `natAbs` identity. -/
theorem chapter01_absoluteDiscriminant_transitivity
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] :
    chapter01AbsoluteDiscriminant L =
      chapter01AbsoluteDiscriminant K ^ Module.finrank K L *
        (chapter01RelativeDifferentNorm K L : ℝ) := by
  sorry

theorem chapter01_absoluteDiscriminant_transitivity_of_unramified
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (h : chapter01UnramifiedAtFinitePrimes K L) :
    chapter01AbsoluteDiscriminant L =
      chapter01AbsoluteDiscriminant K ^ Module.finrank K L := by
  sorry

theorem chapter01_rootDiscriminant_transitivity
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] :
    chapter01RootDiscriminant L =
      chapter01RootDiscriminant K *
        (chapter01RelativeDifferentNorm K L : ℝ) ^
          (chapter01Degree L : ℝ)⁻¹ := by
  sorry

theorem chapter01_rootDiscriminant_mono
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] :
    chapter01RootDiscriminant K ≤ chapter01RootDiscriminant L := by
  sorry

theorem chapter01_rootDiscriminant_eq_iff_unramified
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] :
    chapter01RootDiscriminant L = chapter01RootDiscriminant K ↔
      chapter01UnramifiedAtFinitePrimes K L := by
  sorry

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01
