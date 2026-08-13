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
  simp [chapter01AbsoluteDiscriminant, Nat.cast_natAbs, Int.cast_abs]

theorem chapter01AbsoluteDiscriminant_eq_absolute_different_norm
    (K : Type*) [Field K] [NumberField K] :
    chapter01AbsoluteDiscriminant K =
      (Ideal.absNorm
        (differentIdeal ℤ (NumberField.RingOfIntegers K)) : ℝ) := by
  have h := NumberField.absNorm_differentIdeal K (NumberField.RingOfIntegers K)
  have h' := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [chapter01AbsoluteDiscriminant, Nat.cast_natAbs, Int.cast_abs] using h'.symm

theorem chapter01AbsoluteDiscriminant_pos
    (K : Type*) [Field K] [NumberField K] :
    0 < chapter01AbsoluteDiscriminant K := by
  rw [chapter01AbsoluteDiscriminant_eq_natAbs]
  exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)

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
  exact div_nonneg (by positivity) (by positivity)

theorem chapter01RealProportion_le_one
    (K : Type*) [Field K] [NumberField K] :
    chapter01RealProportion K ≤ 1 := by
  have hdegree : 0 < (chapter01Degree K : ℝ) := by
    exact_mod_cast chapter01Degree_pos K
  rw [chapter01RealProportion, div_le_iff₀ hdegree]
  norm_num
  exact_mod_cast chapter01_realPlaces_le_degree K

def chapter01TotallyReal
    (K : Type*) [Field K] [NumberField K] : Prop :=
  chapter01RealPlaces K = chapter01Degree K

def chapter01TotallyComplex
    (K : Type*) [Field K] [NumberField K] : Prop :=
  chapter01RealPlaces K = 0

/- “Unrestricted signature” refers to the lower-bound parameter `α₀ = 0`,
   not to the field property `r₁ = 0`. -/
def chapter01UnrestrictedSignature (α₀ : ℝ) : Prop :=
  α₀ = 0

theorem chapter01RealProportion_eq_zero_iff
    (K : Type*) [Field K] [NumberField K] :
    chapter01RealProportion K = 0 ↔ chapter01TotallyComplex K := by
  have hdegree : 0 < (chapter01Degree K : ℝ) := by
    exact_mod_cast chapter01Degree_pos K
  constructor
  · intro h
    change (chapter01RealPlaces K : ℝ) / (chapter01Degree K : ℝ) = 0 at h
    have hz : (chapter01RealPlaces K : ℝ) = 0 :=
      (div_eq_zero_iff.mp h).resolve_right hdegree.ne'
    exact_mod_cast hz
  · intro h
    change chapter01RealPlaces K = 0 at h
    change (chapter01RealPlaces K : ℝ) / (chapter01Degree K : ℝ) = 0
    rw [h, Nat.cast_zero, zero_div]

theorem chapter01_unrestrictedSignature_zero :
    chapter01UnrestrictedSignature (0 : ℝ) := by
  rfl

theorem chapter01RealProportion_eq_one_iff
    (K : Type*) [Field K] [NumberField K] :
    chapter01RealProportion K = 1 ↔ chapter01TotallyReal K := by
  have hdegree : (chapter01Degree K : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (chapter01Degree_pos K))
  constructor
  · intro h
    change (chapter01RealPlaces K : ℝ) / (chapter01Degree K : ℝ) = 1 at h
    have h' := (div_eq_one_iff_eq hdegree).mp h
    exact_mod_cast h'
  · intro h
    change (chapter01RealPlaces K : ℝ) / (chapter01Degree K : ℝ) = 1
    apply (div_eq_one_iff_eq hdegree).mpr
    exact_mod_cast h

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

/- The relative discriminant ideal is the relative norm of the different.  This
   is the canonical realization of the book's `𝔡_{L/K} ⊆ 𝓞_K`; its absolute
   norm is the book's `N_{K/ℚ}(𝔡_{L/K})`. -/
noncomputable def chapter01RelativeDiscriminantIdeal
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] :
    Ideal (NumberField.RingOfIntegers K) :=
  Ideal.relNorm (NumberField.RingOfIntegers K)
    (differentIdeal (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L))

/- Keep the earlier book-facing name available, but give it the source's
   base-ring type rather than the different ideal's ambient ring. -/
noncomputable abbrev chapter01RelativeDifferentIdeal
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] :
    Ideal (NumberField.RingOfIntegers K) :=
  chapter01RelativeDiscriminantIdeal K L

noncomputable def chapter01RelativeDifferentNorm
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] : ℕ :=
  Ideal.absNorm (chapter01RelativeDiscriminantIdeal K L)

theorem chapter01RelativeDifferentNorm_pos
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] :
    0 < chapter01RelativeDifferentNorm K L := by
  change 0 < Ideal.absNorm (Ideal.relNorm (NumberField.RingOfIntegers K)
    (differentIdeal (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)))
  apply Nat.pos_of_ne_zero
  intro h
  apply differentIdeal_ne_bot
    (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers L)
  exact Ideal.relNorm_eq_bot_iff.mp (Ideal.absNorm_eq_zero_iff.mp h)

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
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] :
    chapter01UnramifiedAtFinitePrimes K L ↔
      chapter01RelativeDifferentNorm K L = 1 := by
  let A := NumberField.RingOfIntegers K
  let B := NumberField.RingOfIntegers L
  let D : Ideal B := differentIdeal A B
  constructor
  · intro h
    have hD : D = ⊤ := by
      by_contra hD
      obtain ⟨P, hP, hPD⟩ := Ideal.exists_le_maximal D hD
      have hPmax : P.IsMaximal := hP
      have hPprime : P.IsPrime := hP.isPrime
      have hPprime' : P.IsPrime := hPprime
      have hpm : (P.under A).IsMaximal := inferInstance
      have hunr : Algebra.IsUnramifiedIn B (P.under A) := h (P.under A) hpm
      have hAt : Algebra.IsUnramifiedAt A P := hunr P inferInstance inferInstance
      exact (not_dvd_differentIdeal_iff (A := A) (B := B)).mpr hAt
        (Ideal.dvd_iff_le.mpr hPD)
    change Ideal.absNorm (Ideal.relNorm A D) = 1
    rw [hD, Ideal.relNorm_top, Ideal.absNorm_top]
  · intro h
    have hDnorm : Ideal.absNorm D = 1 := by
      rw [← Ideal.absNorm_relNorm A B D]
      simpa [chapter01RelativeDifferentNorm, chapter01RelativeDiscriminantIdeal, A, B, D]
        using h
    have hD : D = ⊤ := Ideal.absNorm_eq_one_iff.mp hDnorm
    intro p hp P hP hPover
    have hPprime : P.IsPrime := hP
    have hnot : ¬ P ∣ D := by
      intro hdiv
      have htop : (⊤ : Ideal B) ≤ P := by
        rw [hD] at hdiv
        exact Ideal.le_of_dvd hdiv
      exact hP.ne_top (top_unique htop)
    exact (not_dvd_differentIdeal_iff (A := A) (B := B)).mp hnot

/- Discriminant transitivity in the source order.  The displayed identity is
   stated over `ℝ`, while the canonical Mathlib theorem is the corresponding
   `natAbs` identity. -/
theorem chapter01_absoluteDiscriminant_transitivity
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] [IsScalarTower ℚ K L] :
    chapter01AbsoluteDiscriminant L =
      chapter01AbsoluteDiscriminant K ^ Module.finrank K L *
        (chapter01RelativeDifferentNorm K L : ℝ) := by
  have h := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    K (NumberField.RingOfIntegers K) L (NumberField.RingOfIntegers L)
  have h' := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [chapter01AbsoluteDiscriminant, chapter01RelativeDifferentNorm,
    chapter01RelativeDiscriminantIdeal, Nat.cast_natAbs, Int.cast_abs,
    Nat.cast_mul, Nat.cast_pow, mul_comm,
    Ideal.absNorm_relNorm (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] using h'

theorem chapter01_absoluteDiscriminant_transitivity_of_unramified
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] [IsScalarTower ℚ K L]
    (h : chapter01UnramifiedAtFinitePrimes K L) :
    chapter01AbsoluteDiscriminant L =
      chapter01AbsoluteDiscriminant K ^ Module.finrank K L := by
  have hnorm :=
    (chapter01_unramifiedAtFinitePrimes_iff_relativeDifferentNorm_eq_one K L).mp h
  simpa [hnorm] using (chapter01_absoluteDiscriminant_transitivity K L)

theorem chapter01_rootDiscriminant_transitivity
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] [IsScalarTower ℚ K L] :
    chapter01RootDiscriminant L =
      chapter01RootDiscriminant K *
        (chapter01RelativeDifferentNorm K L : ℝ) ^
          (chapter01Degree L : ℝ)⁻¹ := by
  have hdegree : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ K L
  have hdegree' : (Module.finrank ℚ K : ℝ) * (Module.finrank K L : ℝ) =
      (Module.finrank ℚ L : ℝ) := by
    exact_mod_cast hdegree
  have hpower : (Module.finrank K L : ℝ) * (Module.finrank ℚ L : ℝ)⁻¹ =
      (Module.finrank ℚ K : ℝ)⁻¹ := by
    rw [← hdegree']
    have hm : (Module.finrank K L : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (show 0 < Module.finrank K L from Module.finrank_pos))
    have hK : (Module.finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (chapter01Degree_pos K))
    field_simp [hm, hK]
  rw [chapter01RootDiscriminant_def, chapter01RootDiscriminant_def,
    chapter01_absoluteDiscriminant_transitivity K L]
  rw [← Real.rpow_natCast]
  have hA : 0 ≤ chapter01AbsoluteDiscriminant K ^ (Module.finrank K L : ℝ) :=
    (Real.rpow_pos_of_pos (chapter01AbsoluteDiscriminant_pos K) _).le
  have hR : 0 ≤ (chapter01RelativeDifferentNorm K L : ℝ) := by
    exact_mod_cast (Nat.zero_le (chapter01RelativeDifferentNorm K L))
  rw [Real.mul_rpow hA hR]
  rw [← Real.rpow_mul (chapter01AbsoluteDiscriminant_pos K).le]
  have hpower' : (Module.finrank K L : ℝ) * (chapter01Degree L : ℝ)⁻¹ =
      (chapter01Degree K : ℝ)⁻¹ := by
    simpa [chapter01Degree] using hpower
  rw [hpower']

theorem chapter01_rootDiscriminant_mono
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] [IsScalarTower ℚ K L] :
    chapter01RootDiscriminant K ≤ chapter01RootDiscriminant L := by
  rw [chapter01_rootDiscriminant_transitivity K L]
  have hroot : 0 ≤ chapter01RootDiscriminant K :=
    (show 0 < chapter01RootDiscriminant K by
      rw [chapter01RootDiscriminant_def]
      exact Real.rpow_pos_of_pos (chapter01AbsoluteDiscriminant_pos K) _).le
  have hnorm : (1 : ℝ) ≤ (chapter01RelativeDifferentNorm K L : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (chapter01RelativeDifferentNorm_pos K L))
  have hfactor : (1 : ℝ) ≤
      (chapter01RelativeDifferentNorm K L : ℝ) ^ (chapter01Degree L : ℝ)⁻¹ :=
    Real.one_le_rpow hnorm (by positivity)
  simpa using (mul_le_mul_of_nonneg_left hfactor hroot)

theorem chapter01_rootDiscriminant_eq_iff_unramified
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L]
    [Module.Finite (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)] [IsScalarTower ℚ K L] :
    chapter01RootDiscriminant L = chapter01RootDiscriminant K ↔
      chapter01UnramifiedAtFinitePrimes K L := by
  constructor
  · intro heq
    apply (chapter01_unramifiedAtFinitePrimes_iff_relativeDifferentNorm_eq_one K L).mpr
    have htrans := chapter01_rootDiscriminant_transitivity K L
    have hroot : 0 < chapter01RootDiscriminant K := by
      rw [chapter01RootDiscriminant_def]
      exact Real.rpow_pos_of_pos (chapter01AbsoluteDiscriminant_pos K) _
    have hfactor :
        chapter01RootDiscriminant K *
            (chapter01RelativeDifferentNorm K L : ℝ) ^
              (chapter01Degree L : ℝ)⁻¹ =
          chapter01RootDiscriminant K * 1 := by
      calc
        chapter01RootDiscriminant K *
            (chapter01RelativeDifferentNorm K L : ℝ) ^
              (chapter01Degree L : ℝ)⁻¹ = chapter01RootDiscriminant L := htrans.symm
        _ = chapter01RootDiscriminant K := heq
        _ = chapter01RootDiscriminant K * 1 := (mul_one _).symm
    have hpow :
        (chapter01RelativeDifferentNorm K L : ℝ) ^
            (chapter01Degree L : ℝ)⁻¹ = 1 :=
      mul_left_cancel₀ hroot.ne' hfactor
    have hq : (chapter01RelativeDifferentNorm K L : ℝ) = 1 := by
      have hdegreeL : 0 < (chapter01Degree L : ℝ) := by
        exact_mod_cast chapter01Degree_pos L
      have hexp : (chapter01Degree L : ℝ)⁻¹ ≠ 0 :=
        inv_ne_zero hdegreeL.ne'
      apply (Real.rpow_left_inj
        (x := (chapter01RelativeDifferentNorm K L : ℝ)) (y := 1)
        (z := (chapter01Degree L : ℝ)⁻¹)
        (by positivity) (by positivity) hexp).mp
      simpa using hpow
    exact_mod_cast hq
  · intro h
    have hnorm :=
      (chapter01_unramifiedAtFinitePrimes_iff_relativeDifferentNorm_eq_one K L).mp h
    rw [chapter01_rootDiscriminant_transitivity K L, hnorm]
    simp

end

end LastLib.Book07AnalyticFoundationsForOdlyzkoPoitouBounds.Chapter01
