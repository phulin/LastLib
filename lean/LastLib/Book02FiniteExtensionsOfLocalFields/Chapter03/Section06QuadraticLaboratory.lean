import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section01WhyTowerFormulasMatter
import LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.Section07UnramifiedAndTotallyRamifiedEndpoints

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Polynomial
open scoped TensorProduct WithZero

/-! ## 3.6. A quadratic laboratory -/

/-- The quadratic polynomial `T^2-a`. -/
def chapter03QuadraticPolynomial
    {K : Type*} [CommRing K] (a : K) : K[X] :=
  ((X : K[X]) ^ 2 - (C a : K[X]) : K[X])

@[simp] theorem chapter03QuadraticPolynomial_eval
    {K : Type*} [CommRing K] (a x : K) :
    (chapter03QuadraticPolynomial a).eval x = x ^ 2 - a := by
  simp [chapter03QuadraticPolynomial]

/-- The canonical root algebra attached to `T^2-a`. -/
noncomputable abbrev chapter03QuadraticRootAlgebra
    (K : Type*) [CommRing K] (a : K) : Type _ :=
  AdjoinRoot (chapter03QuadraticPolynomial a)

/-- Compatibility of a chosen residue map with the quotient residue map. -/
def chapter03CompatibleResidueMap
    (A k : Type*) [CommRing A] [IsLocalRing A] [CommRing k]
    (ρ : A →+* k) : Prop :=
  ∃ e : A ⧸ IsLocalRing.maximalIdeal A ≃+* k,
    e.toRingHom.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)) = ρ

/-- The precise reduction hypotheses for a quadratic polynomial. -/
def chapter03QuadraticReductionCondition
    (A k : Type*) [CommRing A] [CommRing k]
    (ρ : A →+* k) (f : A[X]) (fbar : k[X]) : Prop :=
  Function.Surjective ρ ∧ f.map ρ = fbar ∧
    Irreducible fbar ∧ fbar.Separable

/-- A unit whose residue class is not a square. -/
def chapter03ResidueUnitNonsquare
    (A k : Type*) [CommRing A] [Field k]
    (ρ : A →+* k) (u : Aˣ) : Prop :=
  ¬ ∃ x : k, x ^ 2 = ρ (u : A)

/-- A finite residue field of odd cardinality. -/
def chapter03FiniteOddResidueField
    (k : Type*) [Field k] [Fintype k] : Prop :=
  Fintype.card k % 2 = 1

theorem chapter03FiniteOddResidueField_iff
    (k : Type*) [Field k] [Fintype k] :
    chapter03FiniteOddResidueField k ↔ Fintype.card k % 2 = 1 := Iff.rfl

/-- An irreducible separable reduction of `T^2-u` gives an unramified
quadratic extension. -/
theorem chapter03_unit_quadratic_is_unramified
    (A k K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] [Field K] [Field L] [Fintype k]
    [Algebra A k] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsFractionRing A K] [IsScalarTower A K L]
    [FiniteDimensional K L] (u : Aˣ)
    (hodd : chapter03FiniteOddResidueField k)
    (hnonsquare : chapter03ResidueUnitNonsquare A k (algebraMap A k) u)
    (hred :
      chapter03QuadraticReductionCondition A k
        (algebraMap A k)
        (chapter03QuadraticPolynomial (u : A))
        (chapter03QuadraticPolynomial (algebraMap A k (u : A))))
    (hresidue : chapter03CompatibleResidueMap A k (algebraMap A k))
    (α : L)
    (hroot : aeval α
      (chapter03QuadraticPolynomial (algebraMap A L (u : A))) = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = 2)
    [Algebra.IsSeparable K L]
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

/-- A separable quadratic extension is represented by a square-root algebra. -/
theorem chapter03_quadratic_extension_is_a_square_root
    (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hdegree : Module.finrank K L = 2)
    [Algebra.IsSeparable K L] (hchar : ¬ CharP K 2) :
    ∃ a : K, Nonempty
      (L ≃ₐ[K] chapter03QuadraticRootAlgebra K a) := by
  sorry

/-- An Eisenstein quadratic is totally ramified. -/
theorem chapter03_eisenstein_quadratic_is_totally_ramified
    (A K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsFractionRing A K] [IsScalarTower A K L]
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

/-- The two standard ramified quadratic examples. -/
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
    (hrootπ : aeval απ (chapter03QuadraticPolynomial π) = 0)
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

/-- Every principal unit is a square in the odd-residue complete DVR case. -/
def chapter03PrincipalUnitSquareCondition
    (A : Type*) [CommRing A] (m : Ideal A) : Prop :=
  ∀ x : A, (∃ y : A, x = 1 + y ∧ y ∈ m) →
    ∃ z : A, z ^ 2 = x

theorem chapter03_complete_odd_dvr_principal_units_are_squares
    (A : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (h2 : IsUnit (2 : A)) :
    chapter03PrincipalUnitSquareCondition A (IsLocalRing.maximalIdeal A) := by
  sorry

/-- An odd finite field has exactly two square classes. -/
theorem chapter03_finite_odd_field_has_two_square_classes
    (k : Type*) [Field k] [Fintype k]
    [Fintype (chapter03SquareClassGroup k)]
    (hodd : chapter03FiniteOddResidueField k) :
    Fintype.card (chapter03SquareClassGroup k) = 2 := by
  sorry

/-- The local square-class decomposition supplied by principal units and the
residue quotient. -/
def chapter03LocalSquareClassDecomposition
    (K k : Type*) [Field K] [Field k] : Prop :=
    Nonempty
    (chapter03SquareClassGroup K ≃*
      Multiplicative (ZMod 2) × chapter03SquareClassGroup k)

theorem chapter03_principal_units_supply_square_class_decomposition
    (A K k : Type*) [CommRing A] [Field K] [Field k]
    [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A K] [IsFractionRing A K]
    (hresidue : Nonempty (A ⧸ IsLocalRing.maximalIdeal A ≃+* k))
    (hprincipal :
      chapter03PrincipalUnitSquareCondition A (IsLocalRing.maximalIdeal A)) :
    chapter03LocalSquareClassDecomposition K k := by
  sorry

theorem chapter03_odd_residue_local_square_classes
    (K k : Type*) [Field K] [Field k] [Fintype k]
    [Fintype (chapter03SquareClassGroup K)]
    (hodd : chapter03FiniteOddResidueField k)
    (hprincipal : chapter03LocalSquareClassDecomposition K k) :
    Fintype.card (chapter03SquareClassGroup K) = 4 := by
  sorry

def chapter03NontrivialSquareClass (K : Type*) [Field K] :=
  {a : chapter03SquareClassGroup K // a ≠ 1}

theorem chapter03_three_nontrivial_quadratic_square_classes
    (K : Type*) [Field K] [Fintype (chapter03SquareClassGroup K)]
    [Fintype (chapter03NontrivialSquareClass K)]
    (hcard : Fintype.card (chapter03SquareClassGroup K) = 4) :
    Fintype.card (chapter03NontrivialSquareClass K) = 3 := by
  sorry

/-- The quadratic self-base-change algebra. -/
abbrev chapter03QuadraticSelfBaseChange
    (K L : Type*) [CommRing K] [CommRing L] [Algebra K L] :=
  L ⊗[K] L

/-- The two ramified quadratic classes become isomorphic after the unramified
square class becomes a square in the new base. -/
theorem chapter03_ramified_quadratics_become_isomorphic_after_unramified_base_change
    (K Kᵤ : Type*) [Field K] [Field Kᵤ] [Algebra K Kᵤ]
    (u π : K) (hu : IsUnit u) (hπ : π ≠ 0)
    (s : Kᵤ) (hsquare : s ^ 2 = algebraMap K Kᵤ u) :
    Nonempty
      ((chapter03QuadraticRootAlgebra K π ⊗[K] Kᵤ) ≃ₐ[Kᵤ]
        (chapter03QuadraticRootAlgebra K (u * π) ⊗[K] Kᵤ)) := by
  sorry

/- The tower bookkeeping for the unramified and totally ramified quadratic
stages is recorded independently of a chosen common overfield. -/
theorem chapter03_unramified_then_totally_ramified_stages
    (e₁ f₁ e₂ f₂ e f d : ℕ)
    (hunramified : e₁ = 1 ∧ f₁ = 2)
    (htotallyramified : e₂ = 2 ∧ f₂ = 1)
    (he_tower : e = e₂ * e₁)
    (hf_tower : f = f₂ * f₁)
    (hdegree : d = e * f) :
    e = 2 ∧ f = 2 ∧ d = 4 := by
  sorry

/-- Principal units in a local ring. -/
def chapter03PrincipalUnit
    (A : Type*) [CommRing A] (m : Ideal A) : Type _ :=
  {u : Aˣ // (u : A) - 1 ∈ m}

/-- Squaring preserves the principal-unit subgroup. -/
def chapter03PrincipalUnitSquaringMap
    (A : Type*) [CommRing A] (m : Ideal A) :
    chapter03PrincipalUnit A m → chapter03PrincipalUnit A m := by
  intro u
  refine ⟨u.1 ^ 2, ?_⟩
  change ((u.1 : A) ^ 2 - 1) ∈ m
  have hfactor : (u.1 : A) ^ 2 - 1 =
      (u.1 : A) * ((u.1 : A) - 1) + ((u.1 : A) - 1) := by
    ring
  rw [hfactor]
  exact m.add_mem (m.mul_mem_left _ u.2) u.2

def chapter03PrincipalUnitSquaringBijective
    (A : Type*) [CommRing A] (m : Ideal A) : Prop :=
  Function.Bijective (chapter03PrincipalUnitSquaringMap A m)

/-- The dyadic case does not have the odd-residue square-class count. -/
-- The qualitative source warning is represented by a conditional cardinality
-- theorem, so its local-DVR hypotheses are explicit here.
theorem chapter03_residue_characteristic_two_needs_a_different_square_class_count
    (A K k : Type*) [CommRing A] [IsDomain A]
    [Field K] [Field k] [Algebra A K]
    [IsDiscreteValuationRing A] [IsFractionRing A K]
    [Fintype k] [CharP k 2]
    [Fintype (chapter03SquareClassGroup K)]
    (hcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hfraction : Nonempty (FractionRing A ≃+* K))
    (hresidue : Nonempty
      (A ⧸ IsLocalRing.maximalIdeal A ≃+* k))
    (hnot : ¬ chapter03PrincipalUnitSquaringBijective A
      (IsLocalRing.maximalIdeal A)) :
    4 < Fintype.card (chapter03SquareClassGroup K) := by
  sorry

theorem chapter03_dyadic_square_classes_do_not_have_the_odd_count
    (K k : Type*) [Field K] [Field k] [Fintype k] [CharP k 2]
    [Fintype (chapter03SquareClassGroup K)]
    (hcard : 4 < Fintype.card (chapter03SquareClassGroup K)) :
    ¬ chapter03LocalSquareClassDecomposition K k := by
  sorry

end
end LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03
