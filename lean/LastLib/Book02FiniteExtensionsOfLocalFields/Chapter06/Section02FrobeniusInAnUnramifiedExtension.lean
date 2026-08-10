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
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
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

/- The reduction identification itself, recorded as a chapter-facing theorem. -/
theorem chapter06_unramified_reduction_identifies_galois_groups
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
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
    simpa [chapter06UnramifiedArithmeticFrobenius] using hσ

/- The arithmetic Frobenius upstairs generates the unramified Galois group. -/
theorem chapter06_unramified_arithmetic_frobenius_generates
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Fintype k] [Finite l] [Algebra K L] [Algebra k l]
    [Algebra.IsAlgebraic k l] [FiniteDimensional K L]
    [FiniteDimensional k l] [IsGalois K L] [IsGalois k l]
    (D : Chapter06UnramifiedGaloisReduction K L k l) (σ : Gal(L/K)) :
    ∃ n : ℤ, (chapter06UnramifiedArithmeticFrobenius D) ^ n = σ := by
  obtain ⟨n, hn⟩ :=
    chapter06_arithmetic_frobenius_generates k l (D.reduction σ)
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
  rw [hg, D.quotientEquiv.apply_symm_apply]

/- Two lifts of the same residue automorphism differ by an inertia element. -/
theorem chapter06_frobenius_lifts_differ_by_inertia
    {G H : Type*} [Group G] [Group H] (I : Subgroup G) [I.Normal]
    (D : Chapter06RamifiedGaloisReduction G H I) (φ : H)
    {g h : G} (hg : g ∈ chapter06ArithmeticFrobeniusCoset I D φ)
    (hh : h ∈ chapter06ArithmeticFrobeniusCoset I D φ) :
    ∃ i : I, h = g * i := by
  change D.quotientEquiv (QuotientGroup.mk' I g) = φ at hg
  change D.quotientEquiv (QuotientGroup.mk' I h) = φ at hh
  have hq : QuotientGroup.mk' I g = QuotientGroup.mk' I h := by
    apply D.quotientEquiv.injective
    rw [hg, hh]
  obtain ⟨i, hi, hih⟩ := (QuotientGroup.mk'_eq_mk' I).mp hq
  refine ⟨⟨i, hi⟩, ?_⟩
  exact hih.symm

/- If inertia is nontrivial, the Frobenius coset has no unique lift. -/
theorem chapter06_ramified_frobenius_has_no_distinguished_lift
    {G H : Type*} [Group G] [Group H] (I : Subgroup G) [I.Normal]
    (D : Chapter06RamifiedGaloisReduction G H I) (φ : H)
    (hI : ∃ i : I, (i : G) ≠ 1) :
    ¬ ∃! g : G, g ∈ chapter06ArithmeticFrobeniusCoset I D φ := by
  rintro ⟨g, hg, hunique⟩
  change D.quotientEquiv (QuotientGroup.mk' I g) = φ at hg
  obtain ⟨i, hi⟩ := hI
  have hqi : QuotientGroup.mk' I (i : G) = 1 := by
    simpa only [QuotientGroup.mk'_apply] using
      (QuotientGroup.eq_one_iff (i : G)).2 i.property
  have hgi : g * (i : G) ∈ chapter06ArithmeticFrobeniusCoset I D φ := by
    change D.quotientEquiv (QuotientGroup.mk' I (g * (i : G))) = φ
    rw [map_mul, hqi, mul_one, hg]
  have heq := hunique (g * (i : G)) hgi
  apply hi
  apply (mul_left_cancel (a := g))
  simpa using heq

end

end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter06
