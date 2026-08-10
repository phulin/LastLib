import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section05MixedAndEqualCharacteristic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Polynomial
open scoped TensorProduct WithZero

/-! ## 3.6. Quadratic laboratory -/

/-- The quadratic polynomial T²-a. -/
def chapter03QuadraticPolynomial
    {K : Type*} [CommRing K] (a : K) : K[X] :=
  ((X : K[X]) ^ 2 - (C a : K[X]) : K[X])

/-- The canonical root algebra attached to T²-a. -/
noncomputable abbrev chapter03QuadraticRootAlgebra
    (K : Type*) [CommRing K] (a : K) : Type _ :=
  AdjoinRoot (chapter03QuadraticPolynomial a)

/-- Reduction of a polynomial along a chosen residue map. -/
def chapter03QuadraticReductionCondition
    (A k : Type*) [CommRing A] [CommRing k]
    (f : A[X]) (fbar : k[X]) : Prop :=
  ∃ ρ : A →+* k, Function.Surjective ρ ∧ f.map ρ = fbar ∧
    Irreducible fbar ∧ fbar.Separable

/-- The unit/nonsquare hypothesis in the quadratic laboratory. -/
def chapter03UnitNonsquare
    (A : Type*) [CommRing A] (u : Aˣ) : Prop :=
  ¬ ∃ x : A, x ^ 2 = (u : A)

/-- The residue field is finite of odd cardinality. -/
def chapter03FiniteOddResidueField
    (k : Type*) [Field k] [Fintype k] : Prop :=
  Fintype.card k % 2 = 1

/--
An irreducible separable reduction of T²-u gives the unramified quadratic
profile.
-/
-- STATEMENT_NEEDS_UPDATE: hred uses an arbitrary surjective ring map ρ : A →+* k and is not tied to the residue map induced by vK, so the reduction data cannot determine the intrinsic e/f of vK and vL; identify k with the vK residue field and require ρ to be the compatible residue map (with the corresponding integral-generation condition).
theorem chapter03_unit_quadratic_is_unramified
    (A k K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] [Field K] [Field L]
    [Fintype k]
    [Algebra A k] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L]
    [IsFractionRing A K]
    [FiniteDimensional K L] (u : Aˣ)
    (hodd : chapter03FiniteOddResidueField k)
    (hunit : IsUnit (u : A))
    (hnonsquare : chapter03UnitNonsquare A u)
    (hred :
      chapter03QuadraticReductionCondition A k
        (chapter03QuadraticPolynomial (u : A))
        (chapter03QuadraticPolynomial (algebraMap A k (u : A))))
    (α : L)
    (hroot : aeval α (chapter03QuadraticPolynomial (algebraMap A L (u : A))) = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = 2)
    (hseparable : Algebra.IsSeparable K L)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hvaluationRing : (vK.valuationSubring : Set K) =
      Set.range (algebraMap A K)) :
    ∃ data : Chapter03FiniteLocalExtensionData K L ℤᵐ⁰ vK vL,
      data.e = 1 ∧ data.f = 2 := by
  sorry

/-- Quadratic separable extensions are represented by square-root algebras. -/
theorem chapter03_quadratic_extension_is_a_square_root
    (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hdegree : Module.finrank K L = 2)
    [Algebra.IsSeparable K L] (hchar : ¬ CharP K 2) :
    ∃ a : K, Nonempty
      (L ≃ₐ[K] chapter03QuadraticRootAlgebra K a) := by
  sorry

/--
An Eisenstein quadratic is totally ramified.  This single interface applies
to both T²-π and T²-uπ.
-/
theorem chapter03_eisenstein_quadratic_is_totally_ramified
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsFractionRing A K]
    [IsScalarTower A K L]
    [FiniteDimensional K L] (π : A) (f : A[X]) (α : L)
    (hE : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = 2)
    (hdegree_poly : f.natDegree = 2)
    (vK : Valuation K ℤᵐ⁰) (vL : Valuation L ℤᵐ⁰)
    [vK.HasExtension vL] [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vL]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hvaluationRing : (vK.valuationSubring : Set K) =
      Set.range (algebraMap A K)) :
    ∃ data : Chapter03FiniteLocalExtensionData K L ℤᵐ⁰ vK vL,
      data.e = 2 ∧ data.f = 1 := by
  sorry

/-- The two ramified quadratic examples in the local laboratory. -/
theorem chapter03_uniformizer_and_unit_uniformizer_are_totally_ramified
    (A K Lπ Lᵤπ : Type*) [CommRing A] [IsDomain A]
    [Field K] [Field Lπ] [Field Lᵤπ]
    [Algebra A K] [Algebra K Lπ] [Algebra K Lᵤπ]
    [Algebra A Lπ] [Algebra A Lᵤπ]
    [IsDiscreteValuationRing A] [IsFractionRing A K]
    [IsScalarTower A K Lπ] [IsScalarTower A K Lᵤπ]
    [FiniteDimensional K Lπ] [FiniteDimensional K Lᵤπ]
    (π : A) (u : Aˣ) (απ : Lπ) (αᵤπ : Lᵤπ)
    (hπ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π
      (chapter03QuadraticPolynomial π))
    (hᵤπ : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π
      (chapter03QuadraticPolynomial ((u : A) * π)))
    (hrootπ :
      aeval απ (chapter03QuadraticPolynomial π) = 0)
    (hrootᵤπ :
      aeval αᵤπ (chapter03QuadraticPolynomial ((u : A) * π)) = 0)
    (hgenπ : Algebra.adjoin K ({απ} : Set Lπ) = ⊤)
    (hgenᵤπ : Algebra.adjoin K ({αᵤπ} : Set Lᵤπ) = ⊤)
    (hdegreeπ : Module.finrank K Lπ = 2)
    (hdegreeᵤπ : Module.finrank K Lᵤπ = 2)
    (hdegreeπ_poly : (chapter03QuadraticPolynomial π).natDegree = 2)
    (hdegreeᵤπ_poly :
      (chapter03QuadraticPolynomial ((u : A) * π)).natDegree = 2)
    (vK : Valuation K ℤᵐ⁰) (vLπ : Valuation Lπ ℤᵐ⁰)
    (vLᵤπ : Valuation Lᵤπ ℤᵐ⁰)
    [vK.HasExtension vLπ] [vK.HasExtension vLᵤπ]
    [Valuation.IsRankOneDiscrete vK]
    [Valuation.IsRankOneDiscrete vLπ]
    [Valuation.IsRankOneDiscrete vLᵤπ]
    (hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal vK.valuationSubring) vK.valuationSubring)
    (hvaluationRing : (vK.valuationSubring : Set K) =
      Set.range (algebraMap A K)) :
    (∃ data : Chapter03FiniteLocalExtensionData K Lπ ℤᵐ⁰ vK vLπ,
      data.e = 2 ∧ data.f = 1) ∧
      (∃ data : Chapter03FiniteLocalExtensionData K Lᵤπ ℤᵐ⁰ vK vLᵤπ,
        data.e = 2 ∧ data.f = 1) := by
  sorry

/-- The square subgroup and square-class group of a field. -/
def chapter03SquaresSubgroup (K : Type*) [Field K] : Subgroup Kˣ :=
  Subgroup.closure (Set.range (fun x : Kˣ => x ^ 2))

abbrev chapter03SquareClassGroup (K : Type*) [Field K] :=
  Kˣ ⧸ chapter03SquaresSubgroup K

/-- Every principal unit is a square in the local ring. -/
def chapter03PrincipalUnitSquareCondition
    (A : Type*) [CommRing A] (m : Ideal A) : Prop :=
  ∀ x : A, (∃ y : A, x = 1 + y ∧ y ∈ m) →
    ∃ z : A, z ^ 2 = x

/-- Over a finite odd field there are exactly two square classes. -/
theorem chapter03_finite_odd_field_has_two_square_classes
    (k : Type*) [Field k] [Fintype k]
    [Fintype (chapter03SquareClassGroup k)]
    (hodd : chapter03FiniteOddResidueField k) :
    Fintype.card (chapter03SquareClassGroup k) = 2 := by
  classical
  change Fintype.card k % 2 = 1 at hodd
  let sq : kˣ →* kˣ := powMonoidHom 2
  have hsq : chapter03SquaresSubgroup k = sq.range := by
    apply le_antisymm
    · apply Subgroup.closure_le.2
      rintro _ ⟨x, rfl⟩
      exact ⟨x, by simp [sq, powMonoidHom_apply]⟩
    · rintro _ ⟨x, rfl⟩
      exact Subgroup.subset_closure ⟨x, rfl⟩
  have hdiv : 2 ∣ Nat.card kˣ := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
    omega
  have hindex : (chapter03SquaresSubgroup k).index = 2 := by
    rw [hsq]
    change sq.range.index = 2
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right hdiv]
  simpa [Subgroup.index, Nat.card_eq_fintype_card] using hindex

/--
The principal-unit input to the local square-class calculation is recorded as
an explicit multiplicative-group decomposition.
-/
def chapter03LocalSquareClassDecomposition
    (K k : Type*) [Field K] [Field k] : Prop :=
  Nonempty
    (chapter03SquareClassGroup K ≃*
      Multiplicative (ZMod 2) × chapter03SquareClassGroup k)

/--
The principal-unit square condition and the residue quotient produce the
local square-class decomposition used in Proposition 10.1.
-/
theorem chapter03_principal_units_supply_square_class_decomposition
    (A K k : Type*) [CommRing A] [Field K] [Field k]
    [IsDomain A] [IsLocalRing A] [IsDiscreteValuationRing A]
    [Algebra A K] [IsFractionRing A K]
    (hresidue :
      Nonempty (A ⧸ IsLocalRing.maximalIdeal A ≃+* k))
    (hprincipal :
      chapter03PrincipalUnitSquareCondition A (IsLocalRing.maximalIdeal A)) :
    chapter03LocalSquareClassDecomposition K k := by
  sorry

/-- The four square classes in the odd-residue local case. -/
theorem chapter03_odd_residue_local_square_classes
    (K k : Type*) [Field K] [Field k] [Fintype k]
    [Fintype (chapter03SquareClassGroup K)]
    (hodd : chapter03FiniteOddResidueField k)
    (hprincipal : chapter03LocalSquareClassDecomposition K k) :
    Fintype.card (chapter03SquareClassGroup K) = 4 := by
  rcases hprincipal with ⟨e⟩
  have hk : Fintype.card (chapter03SquareClassGroup k) = 2 :=
    chapter03_finite_odd_field_has_two_square_classes k hodd
  simpa [Fintype.card_prod, Fintype.card_multiplicative, ZMod.card, hk] using
    Fintype.card_congr e.toEquiv

/-- Nontrivial square classes index the three nontrivial quadratic examples. -/
def chapter03NontrivialSquareClass (K : Type*) [Field K] :=
  {a : chapter03SquareClassGroup K // a ≠ 1}

theorem chapter03_three_nontrivial_quadratic_square_classes
    (K : Type*) [Field K] [Fintype (chapter03SquareClassGroup K)]
    [Fintype (chapter03NontrivialSquareClass K)]
    (hcard : Fintype.card (chapter03SquareClassGroup K) = 4) :
    Fintype.card (chapter03NontrivialSquareClass K) = 3 := by
  classical
  have hcard' :
      Fintype.card (chapter03NontrivialSquareClass K) =
        Fintype.card (chapter03SquareClassGroup K) - 1 := by
    simpa [chapter03NontrivialSquareClass] using
      (Fintype.card_subtype_compl
        (α := chapter03SquareClassGroup K) (fun a => a = 1))
  omega

/-- The quadratic self-base-change algebra. -/
abbrev chapter03QuadraticSelfBaseChange
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] :=
  L ⊗[K] L

/- After adjoining the unramified square root, the two ramified quadratic
classes become isomorphic over the new base.  The square relation is stated
directly in the scalar extension, so the conclusion cannot be supplied by
unrelated profile data.
-/
theorem chapter03_ramified_quadratics_become_isomorphic_after_unramified_base_change
    (K Kᵤ : Type*) [Field K] [Field Kᵤ] [Algebra K Kᵤ]
    (u π : K) (hu : IsUnit u) (hπ : π ≠ 0)
    (s : Kᵤ) (hsquare : s ^ 2 = algebraMap K Kᵤ u) :
    Nonempty
      ((chapter03QuadraticRootAlgebra K π ⊗[K] Kᵤ) ≃+*
        (chapter03QuadraticRootAlgebra K (u * π) ⊗[K] Kᵤ)) := by
  sorry

/- The converse stage statement is recorded at the level of the numerical
invariants: an unramified quadratic stage followed by a totally ramified
quadratic stage has total degree four and retains both e- and f-growth. -/
theorem chapter03_unramified_then_totally_ramified_stages
    (e₁ f₁ e₂ f₂ e f d : ℕ)
    (hunramified : e₁ = 1 ∧ f₁ = 2)
    (htotallyramified : e₂ = 2 ∧ f₂ = 1)
    (he_tower : e = e₂ * e₁)
    (hf_tower : f = f₂ * f₁)
    (hdegree : d = e * f) :
    e = 2 ∧ f = 2 ∧ d = 4 := by
  rcases hunramified with ⟨he₁, hf₁⟩
  rcases htotallyramified with ⟨he₂, hf₂⟩
  have he : e = 2 := by simpa [he₁, he₂] using he_tower
  have hf : f = 2 := by simpa [hf₁, hf₂] using hf_tower
  exact ⟨he, hf, by simpa [he, hf] using hdegree⟩

/- Principal-unit squaring is the step that fails in residue characteristic 2. -/
def chapter03PrincipalUnit
    (A : Type*) [CommRing A] (m : Ideal A) : Type _ :=
  {u : Aˣ // (u : A) - 1 ∈ m}

def chapter03PrincipalUnitSquaringMap
    (A : Type*) [CommRing A] (m : Ideal A) :
    chapter03PrincipalUnit A m → chapter03PrincipalUnit A m := by
  intro u
  refine ⟨u.1 ^ 2, ?_⟩
  change ((u.1 : A) ^ 2 - 1) ∈ m
  have hfactor : (u.1 : A) ^ 2 - 1 =
      (u.1 : A) * ((u.1 : A) - 1) + ((u.1 : A) - 1) := by ring
  rw [hfactor]
  exact m.add_mem (m.mul_mem_left _ u.2) u.2

def chapter03PrincipalUnitSquaringBijective
    (A : Type*) [CommRing A] (m : Ideal A) : Prop :=
  Function.Bijective (chapter03PrincipalUnitSquaringMap A m)

/- The source warns that residue characteristic two requires a separate
filtration argument.  The local DVR and completeness hypotheses are explicit
on this diagnostic interface. -/
theorem chapter03_residue_characteristic_two_needs_a_different_square_class_count
    (A K k : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Field k] [Algebra A K]
    [IsDiscreteValuationRing A] [IsFractionRing A K]
    [Fintype k] [CharP k 2]
    [Fintype (chapter03SquareClassGroup K)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfraction : Nonempty (FractionRing A ≃+* K))
    (hresidue :
      Nonempty (A ⧸ IsLocalRing.maximalIdeal A ≃+* k))
    (hnot :
      ¬ chapter03PrincipalUnitSquaringBijective A
        (IsLocalRing.maximalIdeal A)) :
    4 < Fintype.card (chapter03SquareClassGroup K) := by
  sorry

theorem chapter03_dyadic_square_classes_do_not_have_the_odd_count
    (K k : Type*) [Field K] [Field k] [Fintype k] [CharP k 2]
    [Fintype (chapter03SquareClassGroup K)]
    (hcard : 4 < Fintype.card (chapter03SquareClassGroup K)) :
    ¬ chapter03LocalSquareClassDecomposition K k := by
  intro hdecomp
  rcases hdecomp with ⟨e⟩
  have hsq : chapter03SquaresSubgroup k = ⊤ := by
    apply top_unique
    intro u hu
    rcases FiniteField.isSquare_of_char_two (ringChar.eq k 2) (u : k) with ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro ha0
      apply Units.ne_zero u
      rw [ha, ha0, zero_mul]
    let au : kˣ := Units.mk0 a ha0
    have hau : au ^ 2 = u := by
      apply Units.ext
      change (a : k) ^ 2 = (u : k)
      simpa [au, pow_two] using ha.symm
    exact Subgroup.subset_closure
      (show au ^ 2 ∈ Set.range (fun x : kˣ => x ^ 2) from ⟨au, rfl⟩)
  have hindex : (chapter03SquaresSubgroup k).index = 1 := by
    rw [hsq]
    exact Subgroup.index_top
  have hcardk : Fintype.card (chapter03SquareClassGroup k) = 1 := by
    simpa [Subgroup.index, Nat.card_eq_fintype_card] using hindex
  have hcardtwo : Fintype.card (chapter03SquareClassGroup K) = 2 := by
    simpa [Fintype.card_prod, Fintype.card_multiplicative, hcardk, ZMod.card] using
      Fintype.card_congr e.toEquiv
  omega

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
