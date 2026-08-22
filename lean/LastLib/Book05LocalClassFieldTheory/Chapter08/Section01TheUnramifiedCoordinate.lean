import LastLib.Book05LocalClassFieldTheory.Chapter08.Dependencies

namespace LastLib.Book05LocalClassFieldTheory.Chapter08

noncomputable section

open scoped Pointwise WithTop

/-! ## 8.1. The unramified coordinate -/

/- The chosen maximal-unramified quotient is the Chapter 7 quotient whose
   profinite coordinate is normalized arithmetically. -/
theorem chapter08_maximal_unramified_galois_group_hatZ
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I) :
    Nonempty (U.G ≃ₜ* Chapter08ProfiniteIntegers) := by
  exact ⟨U.completionEquiv⟩

theorem chapter08_arithmetic_frobenius_has_coordinate_one
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I) :
    U.completionEquiv (chapter08ArithmeticFrobenius S U) =
      chapter08IntegerToProfiniteCompletion 1 := by
  change U.completionEquiv
      (U.completionEquiv.symm (chapter08IntegerToProfiniteCompletion 1)) =
    chapter08IntegerToProfiniteCompletion 1
  exact U.completionEquiv.apply_symm_apply (chapter08IntegerToProfiniteCompletion 1)

/- The displayed square is represented as equality of the two homomorphisms
   from `Kˣ` to the profinite integer coordinate. -/
theorem chapter08_unramified_coordinate_commutes_with_valuation
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (hvaluation : U.valuation = D.coordinate.valuation) :
    chapter08UnramifiedCoordinate S U =
      chapter08IntegerToProfiniteCompletionHom.comp D.coordinate.valuation := by
  ext x
  rw [chapter08_unramified_coordinate_formula S U x, hvaluation]
  rfl

theorem chapter08_reciprocity_restricts_to_frobenius_power
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (hvaluation : U.valuation = D.coordinate.valuation)
    (x : Kˣ) :
    chapter08RestrictionToUnramified S U x =
      (chapter08ArithmeticFrobenius S U) ^
        Multiplicative.toAdd (D.coordinate.valuation x) := by
  apply U.completionEquiv.injective
  change chapter08UnramifiedCoordinate S U x =
    U.completionEquiv
      ((chapter08ArithmeticFrobenius S U) ^
        Multiplicative.toAdd (D.coordinate.valuation x))
  rw [chapter08_unramified_coordinate_formula S U x]
  rw [map_zpow U.completionEquiv,
    chapter08_arithmetic_frobenius_has_coordinate_one S U]
  rw [hvaluation]
  change chapter08IntegerToProfiniteCompletionHom
      (Multiplicative.ofAdd (Multiplicative.toAdd (D.coordinate.valuation x))) =
    chapter08IntegerToProfiniteCompletionHom (Multiplicative.ofAdd 1) ^
      Multiplicative.toAdd (D.coordinate.valuation x)
  rw [← map_zpow chapter08IntegerToProfiniteCompletionHom]
  congr 1
  change Multiplicative.ofAdd (Multiplicative.toAdd (D.coordinate.valuation x)) =
    Multiplicative.ofAdd
      (Multiplicative.toAdd (D.coordinate.valuation x) • (1 : ℤ))
  simp

theorem chapter08_units_act_trivially_on_maximal_unramified
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (hvaluation : U.valuation = D.coordinate.valuation)
    {x : Kˣ} (hx : x ∈ chapter08Units D.valuation) :
    chapter08RestrictionToUnramified S U x = 1 := by
  rw [chapter08_reciprocity_restricts_to_frobenius_power D S U hvaluation x]
  have hvaluation_x : D.coordinate.valuation x = 1 :=
    (D.mem_units_iff x).mp hx
  rw [hvaluation_x]
  simp

theorem chapter08_uniformizer_acts_as_arithmetic_frobenius
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (hvaluation : U.valuation = D.coordinate.valuation) :
    chapter08RestrictionToUnramified S U D.uniformizer =
      chapter08ArithmeticFrobenius S U := by
  rw [chapter08_reciprocity_restricts_to_frobenius_power D S U hvaluation]
  rw [D.valuation_uniformizer]
  simp

theorem chapter08_unramified_action_unchanged_by_unit_multiple
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (hvaluation : U.valuation = D.coordinate.valuation)
    (u : Kˣ) (hu : u ∈ chapter08Units D.valuation) :
    chapter08RestrictionToUnramified S U (u * D.uniformizer) =
      chapter08RestrictionToUnramified S U D.uniformizer := by
  rw [chapter08_reciprocity_restricts_to_frobenius_power D S U hvaluation]
  rw [map_mul, (D.mem_units_iff u).mp hu, D.valuation_uniformizer]
  simp
  exact (chapter08_uniformizer_acts_as_arithmetic_frobenius D S U hvaluation).symm

/- The finite unramified norm criterion.  The branch data expose the degree
   `f` as the residue degree; no separate unit condition is present. -/
theorem chapter08_unramified_norm_iff_valuation_divisible
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (hX : chapter08FiniteUnramified X) (x : Kˣ) :
    x ∈ chapter08NormSubgroup K L ↔
      (X.residueDegree : ℤ) ∣ Multiplicative.toAdd
        (X.base.coordinate.valuation x) := by
  sorry

theorem chapter08_unramified_units_are_norms
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (hX : chapter08FiniteUnramified X) :
    chapter08Units X.base.valuation ≤ chapter08NormSubgroup K L := by
  intro x hx
  apply (chapter08_unramified_norm_iff_valuation_divisible X hX x).2
  rw [X.base.mem_units_iff x] at hx
  rw [hx]
  simp

def chapter08ValuationDivisibilitySubgroup
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K) (m : ℕ) : Subgroup Kˣ :=
  (Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ))).comap D.coordinate.valuation

theorem chapter08_mem_valuation_divisibility_subgroup_iff
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K) (m : ℕ) (x : Kˣ) :
    x ∈ chapter08ValuationDivisibilitySubgroup D m ↔
      (m : ℤ) ∣ Multiplicative.toAdd (D.coordinate.valuation x) := by
  change D.coordinate.valuation x ∈
      Subgroup.zpowers (Multiplicative.ofAdd (m : ℤ)) ↔ _
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hz' := congrArg Multiplicative.toAdd hz
    simpa [mul_comm] using hz'.symm
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← ofAdd_toAdd (D.coordinate.valuation x), hz]
    have hmz : (m : ℤ) * z = z • (m : ℤ) := by
      simpa [smul_eq_mul] using (mul_comm (m : ℤ) z)
    rw [hmz, ofAdd_zsmul]

theorem chapter08_unramified_norm_subgroup_is_valuation_preimage
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L)
    (hX : chapter08FiniteUnramified X) :
    chapter08NormSubgroup K L =
      chapter08ValuationDivisibilitySubgroup X.base X.residueDegree := by
  ext x
  exact (chapter08_unramified_norm_iff_valuation_divisible X hX x).trans
    (chapter08_mem_valuation_divisibility_subgroup_iff
      X.base X.residueDegree x).symm

/- A formal-module tower is kept as a construction interface.  The norm field
   is an earlier construction fact; the action-on-labels identity is the
   comparison with the torsion labeling used in the source. -/
structure Chapter08LubinTateTower
    {K : Type*} [Field K] (D : Chapter08LocalFieldData K) where
  level : ℕ → Type*
  [fieldLevel : ∀ n, Field (level n)]
  [algebraLevel : ∀ n, Algebra K (level n)]
  [finiteLevel : ∀ n, FiniteDimensional K (level n)]
  [galoisLevel : ∀ n, IsGalois K (level n)]
  [abelianLevel : ∀ n, CommGroup (Gal(level n / K))]
  omega : ∀ n, level n
  artin : ∀ n, Kˣ →* Gal(level n / K)
  formalAction : ∀ n, Kˣ → level n → level n
  artin_kernel_norm : ∀ n,
    (artin n).ker = chapter08NormSubgroup K (level n)
  uniformizer_is_norm : ∀ n,
    D.uniformizer ∈ chapter08NormSubgroup K (level n)

def chapter08LubinTateCoordinate
    {K : Type*} [Field K] {D : Chapter08LocalFieldData K}
    (T : Chapter08LubinTateTower D) (n : ℕ) (x : Kˣ) : T.level n :=
  (T.artin n x) (T.omega n)

theorem chapter08_lubin_tate_uniformizer_reciprocity
    {K : Type*} [Field K] [TopologicalSpace Kˣ]
    (D : Chapter08LocalFieldData K)
    (T : Chapter08LubinTateTower D) (n : ℕ) :
    T.artin n D.uniformizer = 1 := by
  rw [← MonoidHom.mem_ker, T.artin_kernel_norm n]
  exact T.uniformizer_is_norm n

theorem chapter08_lubin_tate_unit_action_on_division_point
    {K : Type*} [Field K]
    (D : Chapter08LocalFieldData K)
    (T : Chapter08LubinTateTower D) (n : ℕ) (u : Kˣ) :
    chapter08LubinTateCoordinate T n u =
      T.formalAction n u⁻¹ (T.omega n) := by
  sorry

def chapter08TwoCoordinateValue
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    {D : Chapter08LocalFieldData K}
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (T : Chapter08LubinTateTower D) (n : ℕ) (x : Kˣ) : U.G × T.level n :=
  (chapter08RestrictionToUnramified S U x, chapter08LubinTateCoordinate T n x)

def chapter08TwoCoordinateAutomorphism
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    {D : Chapter08LocalFieldData K}
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (T : Chapter08LubinTateTower D) (n : ℕ) (x : Kˣ) :=
  (chapter08RestrictionToUnramified S U x, T.artin n x)

theorem chapter08_two_coordinate_artin_formula
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (T : Chapter08LubinTateTower D) (n : ℕ)
    (hvaluation : U.valuation = D.coordinate.valuation)
    (r : ℤ) (u : Kˣ) :
    chapter08TwoCoordinateValue S U T n (D.uniformizer ^ r * u) =
      ((chapter08ArithmeticFrobenius S U) ^ r,
        T.formalAction n u⁻¹ (T.omega n)) := by
  sorry

theorem chapter08_two_coordinate_automorphism_formula
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (D : Chapter08LocalFieldData K)
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (T : Chapter08LubinTateTower D) (n : ℕ)
    (hvaluation : U.valuation = D.coordinate.valuation)
    (r : ℤ) (u : Kˣ) :
    chapter08TwoCoordinateAutomorphism S U T n (D.uniformizer ^ r * u) =
      ((chapter08ArithmeticFrobenius S U) ^ r, T.artin n u) ∧
      T.artin n u (T.omega n) = T.formalAction n u⁻¹ (T.omega n) := by
  sorry

/- Any two chosen coordinate formulas which realize the same reciprocity value
   induce the same finite automorphism.  This is the formal content of the
   source's choice-independence warning. -/
theorem chapter08_product_coordinates_induce_choice_independent_automorphism
    {G A : Type*} [Group G] [Group A]
    (rec : G → A) (c₁ c₂ : G → A)
    (h₁ : ∀ x, c₁ x = rec x) (h₂ : ∀ x, c₂ x = rec x) (x : G) :
    c₁ x = c₂ x := by
  exact (h₁ x).trans (h₂ x).symm

end

end LastLib.Book05LocalClassFieldTheory.Chapter08
