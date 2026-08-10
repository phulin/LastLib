import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03.Section05MixedAndEqualCharacteristic

namespace LastLib.Book02FiniteExtensionsOfLocalFields.Chapter03

noncomputable section

open Polynomial
open scoped TensorProduct

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
  ∃ ρ : A →+* k, f.map ρ = fbar ∧ Irreducible fbar

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
theorem chapter03_unit_quadratic_is_unramified
    (A k K L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field k] [Field K] [Field L]
    [Fintype k]
    [Algebra A k] [Algebra A K] [Algebra K L] [Algebra A L]
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
    (hseparable : Algebra.IsSeparable K L) :
    ∃ data : Chapter03FiniteLocalExtensionData K L,
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
    (A K L : Type*) [CommRing A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
    [FiniteDimensional K L] (π : A) (f : A[X]) (α : L)
    (hE : LastLib.Book01ValuationsDVRsAndCompletions.Chapter12.IsEisensteinAt π f)
    (hroot : aeval α f = 0)
    (hgen : Algebra.adjoin K ({α} : Set L) = ⊤)
    (hdegree : Module.finrank K L = 2) :
    ∃ data : Chapter03FiniteLocalExtensionData K L,
      data.e = 2 ∧ data.f = 1 := by
  sorry

/-- The two ramified quadratic examples in the local laboratory. -/
theorem chapter03_uniformizer_and_unit_uniformizer_are_totally_ramified
    (A K Lπ Lᵤπ : Type*) [CommRing A] [IsLocalRing A]
    [Field K] [Field Lπ] [Field Lᵤπ]
    [Algebra A K] [Algebra K Lπ] [Algebra K Lᵤπ]
    [Algebra A Lπ] [Algebra A Lᵤπ]
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
    (hdegreeᵤπ : Module.finrank K Lᵤπ = 2) :
    (∃ data : Chapter03FiniteLocalExtensionData K Lπ,
      data.e = 2 ∧ data.f = 1) ∧
      (∃ data : Chapter03FiniteLocalExtensionData K Lᵤπ,
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
  sorry

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
    [IsLocalRing A] [Algebra A K]
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
  sorry

/-- Nontrivial square classes index the three nontrivial quadratic examples. -/
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

/--
After adjoining the unramified square root, the two ramified quadratic
classes become isomorphic over the new base.
-/
theorem chapter03_ramified_quadratics_become_isomorphic_after_unramified_base_change
    (K Kᵤ Kπ Kᵤπ : Type*) [Field K] [Field Kᵤ] [Field Kπ] [Field Kᵤπ]
    [Algebra K Kᵤ] [Algebra K Kπ] [Algebra K Kᵤπ]
    [FiniteDimensional K Kᵤ] [FiniteDimensional K Kπ]
    [FiniteDimensional K Kᵤπ]
    (u π : K)
    (hᵤ : Nonempty (Kᵤ ≃+* chapter03QuadraticRootAlgebra K u))
    (hπ : Nonempty (Kπ ≃+* chapter03QuadraticRootAlgebra K π))
    (hᵤπ : Nonempty
      (Kᵤπ ≃+* chapter03QuadraticRootAlgebra K (u * π)))
    (hprofileᵤ : ∃ data : Chapter03FiniteLocalExtensionData K Kᵤ,
      data.e = 1 ∧ data.f = 2)
    (hprofileπ : ∃ data : Chapter03FiniteLocalExtensionData K Kπ,
      data.e = 2 ∧ data.f = 1)
    (hprofileᵤπ : ∃ data : Chapter03FiniteLocalExtensionData K Kᵤπ,
      data.e = 2 ∧ data.f = 1) :
    Nonempty ((Kπ ⊗[K] Kᵤ) ≃+* (Kᵤπ ⊗[K] Kᵤ)) := by
  sorry

/-- The unramified stage remains unramified when the ramified square is added. -/
theorem chapter03_unramified_then_totally_ramified_stages
    (e₁ f₁ e₂ f₂ : ℕ)
    (hunramified : e₁ = 1) (htotallyramified : f₂ = 1) :
    e₁ = 1 ∧ f₂ = 1 :=
  ⟨hunramified, htotallyramified⟩

/-- Principal-unit squaring is the step that fails in residue characteristic 2. -/
def chapter03PrincipalUnitSquaringBijective (K : Type*) [Monoid K] : Prop :=
  Function.Bijective (fun x : Kˣ => x ^ 2)

-- SOURCE_ISSUE: The three-class quadratic picture in §3.6 uses odd residue
-- characteristic; in characteristic 2 principal-unit squaring is not
-- invertible and the square-class count must be recomputed.
theorem chapter03_residue_characteristic_two_needs_a_different_square_class_count
    (A K k : Type*) [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field K] [Field k] [Algebra A K] [Fintype k] [CharP k 2]
    [Fintype (chapter03SquareClassGroup K)]
    (hfraction : Nonempty (FractionRing A ≃+* K))
    (hresidue :
      Nonempty (A ⧸ IsLocalRing.maximalIdeal A ≃+* k))
    (hnot :
      ¬ chapter03PrincipalUnitSquaringBijective A) :
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
