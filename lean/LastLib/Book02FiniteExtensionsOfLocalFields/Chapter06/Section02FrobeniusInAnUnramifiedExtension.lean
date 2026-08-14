import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06.Section01WhyFrobeniusIsCanonical

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06

noncomputable section

open Set

/-! ## 6.2. Frobenius in an unramified extension -/

/-
The reduction map on Galois groups is represented by a multiplicative
equivalence.  This keeps the local-ring construction of the reduction map
outside the statement interface while retaining exactly the identification
used by the chapter.
-/

/- Reduction data identifying the two finite Galois groups in an unramified extension. -/
structure Chapter06UnramifiedGaloisReduction
    (K L k l : Type*) [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l] where
  /- The canonical reduction identification `Gal(L/K) ≃ Gal(l/k)`. -/
  reduction : Gal(L/K) ≃* Gal(l/k)

/- The arithmetic Frobenius element upstairs, transported through reduction. -/
noncomputable def chapter06UnramifiedArithmeticFrobenius
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) : Gal(L/K) :=
  D.reduction.symm (chapter06ArithmeticFrobenius k l)

/- The geometric Frobenius element upstairs. -/
noncomputable def chapter06UnramifiedGeometricFrobenius
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) : Gal(L/K) :=
  (chapter06UnramifiedArithmeticFrobenius D)⁻¹

/-
SOURCE_ISSUE: The source writes the reduction map on automorphisms and on the
valuation ring without naming either map.  This interface makes those maps
explicit.  The residue-surjectivity field is the exact local hypothesis needed
to turn equality of residue actions into uniqueness of the lifted automorphism.
-/

/- A reduction action on an integral model of an unramified extension. -/
structure Chapter06UnramifiedResidueAction
    (K L k l B : Type*) [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [CommRing B] [Algebra K L] [Algebra k l]
    [Algebra B L] [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) where
  /- Reduction of the chosen integral model to the residue field. -/
  residue : B →+* l
  /- The induced action of `Gal(L/K)` on the integral model. -/
  action : Gal(L/K) →* (B ≃+* B)
  /- The model action is the restriction of the field automorphism. -/
  action_on_field : ∀ (σ : Gal(L/K)) (x : B),
    algebraMap B L (action σ x) = σ (algebraMap B L x)
  /- Every residue class has an integral representative. -/
  residue_surjective : Function.Surjective residue
  /- Reduction intertwines the two Galois actions. -/
  reduction_commutes : ∀ (σ : Gal(L/K)) (x : B),
    residue (action σ x) = D.reduction σ (residue x)

/- The integral-model action of the lifted arithmetic Frobenius. -/
noncomputable def chapter06UnramifiedArithmeticFrobeniusOnModel
    {K L k l B : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [CommRing B] [Algebra K L] [Algebra k l]
    [Algebra B L] [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    {D : Chapter06UnramifiedGaloisReduction K L k l}
    (R : Chapter06UnramifiedResidueAction K L k l B D) : B ≃+* B :=
  R.action (chapter06UnramifiedArithmeticFrobenius D)

/- The field action corresponding to the model action. -/
theorem chapter06_unramified_arithmetic_frobenius_action_on_field
    {K L k l B : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [CommRing B] [Algebra K L] [Algebra k l]
    [Algebra B L] [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    {D : Chapter06UnramifiedGaloisReduction K L k l}
    (R : Chapter06UnramifiedResidueAction K L k l B D) (x : B) :
    algebraMap B L (chapter06UnramifiedArithmeticFrobeniusOnModel R x) =
      chapter06UnramifiedArithmeticFrobenius D (algebraMap B L x) := by
  exact R.action_on_field (chapter06UnramifiedArithmeticFrobenius D) x

/- The residue formula for the lifted arithmetic Frobenius. -/
theorem chapter06_unramified_arithmetic_frobenius_residue_formula
    {K L k l B : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [CommRing B] [Algebra K L] [Algebra k l]
    [Algebra B L] [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    {D : Chapter06UnramifiedGaloisReduction K L k l}
    (R : Chapter06UnramifiedResidueAction K L k l B D) (x : B) :
    R.residue (chapter06UnramifiedArithmeticFrobeniusOnModel R x) =
      (R.residue x) ^ Fintype.card k := by
  change R.residue (R.action (chapter06UnramifiedArithmeticFrobenius D) x) = _
  rw [R.reduction_commutes]
  simp [chapter06UnramifiedArithmeticFrobenius,
    chapter06_arithmetic_frobenius_apply]

/- The residue congruence characterizes the lifted arithmetic Frobenius. -/
theorem chapter06_unramified_arithmetic_frobenius_residue_unique
    {K L k l B : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [CommRing B] [Algebra K L] [Algebra k l]
    [Algebra B L] [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    {D : Chapter06UnramifiedGaloisReduction K L k l}
    (R : Chapter06UnramifiedResidueAction K L k l B D) :
    ∃! σ : Gal(L/K), ∀ x : B,
      R.residue (R.action σ x) = (R.residue x) ^ Fintype.card k := by
  let σ₀ := chapter06UnramifiedArithmeticFrobenius D
  refine ⟨σ₀, ?_, ?_⟩
  · intro x
    exact chapter06_unramified_arithmetic_frobenius_residue_formula R x
  · intro σ hσ
    apply D.reduction.injective
    have hσ₀ : D.reduction σ₀ = chapter06ArithmeticFrobenius k l := by
      simp [σ₀, chapter06UnramifiedArithmeticFrobenius]
    have hσ₀' : ∀ x : B, R.residue (R.action σ₀ x) =
        D.reduction σ₀ (R.residue x) := R.reduction_commutes σ₀
    ext y
    obtain ⟨x, hx⟩ := R.residue_surjective y
    have hσx := hσ x
    have hσ₀x := (show ∀ z : B, R.residue (R.action σ₀ z) =
        (R.residue z) ^ Fintype.card k from by
          intro z
          exact chapter06_unramified_arithmetic_frobenius_residue_formula R z) x
    rw [R.reduction_commutes σ x] at hσx
    rw [hσ₀' x] at hσ₀x
    rw [hx] at hσx hσ₀x
    rw [hσx, hσ₀x]

/- The reduction identification itself, recorded as a chapter-facing theorem. -/
theorem chapter06_unramified_reduction_identifies_galois_groups
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [Algebra k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) :
    Nonempty (Gal(L/K) ≃* Gal(l/k)) := by
  exact ⟨D.reduction⟩

/- The upstairs arithmetic Frobenius is the unique lift of residue Frobenius. -/
theorem chapter06_unramified_arithmetic_frobenius_unique
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) :
    ∃! σ : Gal(L/K), D.reduction σ = chapter06ArithmeticFrobenius k l := by
  refine ⟨chapter06UnramifiedArithmeticFrobenius D, ?_, ?_⟩
  · simp [chapter06UnramifiedArithmeticFrobenius]
  · intro σ hσ
    apply D.reduction.injective
    rw [hσ]
    simp [chapter06UnramifiedArithmeticFrobenius]

/- The arithmetic Frobenius upstairs generates the unramified Galois group. -/
theorem chapter06_unramified_arithmetic_frobenius_generates
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) (σ : Gal(L/K)) :
    ∃ n : ℤ, (chapter06UnramifiedArithmeticFrobenius D) ^ n = σ := by
  obtain ⟨n, hn⟩ := chapter06_arithmetic_frobenius_generates k l
      (D.reduction σ)
  refine ⟨n, ?_⟩
  apply D.reduction.injective
  simpa [chapter06UnramifiedArithmeticFrobenius] using hn

/- Geometric Frobenius upstairs is the inverse of arithmetic Frobenius. -/
theorem chapter06_unramified_geometric_frobenius_is_inverse
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) :
    chapter06UnramifiedGeometricFrobenius D =
      (chapter06UnramifiedArithmeticFrobenius D)⁻¹ := by
  rfl

/-
For the ramified case the inertia subgroup is kept explicit.  The quotient
equivalence is the precise data supplied by the valuation-theoretic
decomposition-group construction; a quotient element, rather than a chosen
automorphism upstairs, is the canonical Frobenius object.
-/

/- A quotient-level residue Galois identification for a ramified extension. -/
structure Chapter06RamifiedGaloisReduction
    (G H : Type*) [Group G] [Group H] (I : Subgroup G) [I.Normal] where
  /- `G/I ≃ Gal(l/k)`; in applications `I` is the inertia subgroup. -/
  quotientEquiv : (G ⧸ I) ≃* H

/- The arithmetic Frobenius coset in a ramified Galois group. -/
def chapter06ArithmeticFrobeniusCoset
    {G H : Type*} [Group G] [Group H] (I : Subgroup G) [I.Normal]
    (D : Chapter06RamifiedGaloisReduction G H I) (φ : H) : Set G :=
  {g | D.quotientEquiv (QuotientGroup.mk' I g) = φ}

/- The residue Frobenius has a nonempty coset of lifts. -/
theorem chapter06_arithmetic_frobenius_coset_nonempty
    {G H : Type*} [Group G] [Group H] (I : Subgroup G) [I.Normal]
    (D : Chapter06RamifiedGaloisReduction G H I) (φ : H) :
    (chapter06ArithmeticFrobeniusCoset I D φ).Nonempty := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective I (D.quotientEquiv.symm φ)
  refine ⟨g, ?_⟩
  change D.quotientEquiv (QuotientGroup.mk' I g) = φ
  rw [hg]
  exact D.quotientEquiv.apply_symm_apply φ

/- Two lifts of the same residue automorphism differ by an inertia element. -/
theorem chapter06_frobenius_lifts_differ_by_inertia
    {G H : Type*} [Group G] [Group H] (I : Subgroup G) [I.Normal]
    (D : Chapter06RamifiedGaloisReduction G H I) (φ : H)
    {g h : G} (hg : g ∈ chapter06ArithmeticFrobeniusCoset I D φ)
    (hh : h ∈ chapter06ArithmeticFrobeniusCoset I D φ) :
    ∃ i : I, h = g * i := by
  change D.quotientEquiv (QuotientGroup.mk' I g) = φ at hg
  change D.quotientEquiv (QuotientGroup.mk' I h) = φ at hh
  have hquot : QuotientGroup.mk' I g = QuotientGroup.mk' I h :=
    D.quotientEquiv.injective (hg.trans hh.symm)
  obtain ⟨i, hi, hgi⟩ := (QuotientGroup.mk'_eq_mk' I).mp hquot
  exact ⟨⟨i, hi⟩, hgi.symm⟩

/- If inertia is nontrivial, the Frobenius coset has no unique lift. -/
theorem chapter06_ramified_frobenius_has_no_distinguished_lift
    {G H : Type*} [Group G] [Group H] (I : Subgroup G) [I.Normal]
    (D : Chapter06RamifiedGaloisReduction G H I) (φ : H)
    (hI : ∃ i : I, (i : G) ≠ 1) :
    ¬ ∃! g : G, g ∈ chapter06ArithmeticFrobeniusCoset I D φ := by
  rintro ⟨g, hg, huniq⟩
  obtain ⟨i, hi⟩ := hI
  have hgi : g * (i : G) ∈ chapter06ArithmeticFrobeniusCoset I D φ := by
    change D.quotientEquiv (QuotientGroup.mk' I (g * (i : G))) = φ
    rw [map_mul]
    have hmk : QuotientGroup.mk' I (i : G) = 1 :=
      (QuotientGroup.eq_one_iff _).2 i.property
    rw [hmk, mul_one]
    exact hg
  have hneq : g * (i : G) ≠ g := by
    intro h
    apply hi
    calc
      (i : G) = g⁻¹ * (g * (i : G)) := by simp
      _ = g⁻¹ * g := by rw [h]
      _ = 1 := by simp
  exact hneq (huniq (g * (i : G)) hgi)

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
