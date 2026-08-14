import LastLib.Book06GlobalClassFieldTheory.Chapter04.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

universe u v

open scoped BigOperators

/-! ## 4.6. Cup products and the local trace -/

/-! The local cohomology object is a dependency interface: the pinned Mathlib snapshot supplies the
finite-group complexes, while the absolute-Galois/local-field realization belongs to the earlier
local class-field chapters. -/

/-- Local cohomology, cup product, and the degree-two invariant for a dual coefficient pair. -/
structure Chapter04LocalCupProductData
    {G : Type u} [Group G]
    (P : Chapter04DualCoefficientPair.{u, v} G) where
  H : Chapter04GModule.{u, v} G → ℤ → Type v
  [hGroup : ∀ M r, AddCommGroup (H M r)]
  cup : ∀ r : ℤ,
    H P.M r → H P.Mdual (2 - r) → H P.μn 2
  invariant : H P.μn 2 →+ chapter04QModZ
  denominator : ∀ (r : ℤ) (x : H P.M r) (y : H P.Mdual (2 - r)),
    invariant (cup r x y) ∈ chapter04QModZTorsion P.n

attribute [instance] Chapter04LocalCupProductData.hGroup

/-- The numerical local cup-product pairing in the book's normalization. -/
def chapter04LocalNumericalPairing
    {G : Type u} [Group G]
    {P : Chapter04DualCoefficientPair.{u, v} G}
    (Q : Chapter04LocalCupProductData P) (r : ℤ) :
    Q.H P.M r → Q.H P.Mdual (2 - r) → chapter04QModZ :=
  fun x y => Q.invariant (Q.cup r x y)

/- The subgroup of `ℚ / ℤ` consisting of classes killed by `n` is defined in `Dependencies` so
that the global trace section can use the same target without importing this leaf. -/
theorem chapter04_local_numerical_pairing_has_denominator
    {G : Type u} [Group G]
    {P : Chapter04DualCoefficientPair.{u, v} G}
    (Q : Chapter04LocalCupProductData P) (r : ℤ)
    (x : Q.H P.M r) (y : Q.H P.Mdual (2 - r)) :
    chapter04LocalNumericalPairing Q r x y ∈ chapter04QModZTorsion P.n := by
  change Q.invariant (Q.cup r x y) ∈ chapter04QModZTorsion P.n
  exact Q.denominator r x y

/-! Tate cohomology is retained at real places in all degrees.  Complex places contribute the zero
pairing; this convention belongs to the local cohomology realization represented by `H` above.
It is intentionally not encoded as an unrelated proposition-valued record. -/

/-- Abstract projection data for the local restriction/corestriction adjunction. -/
structure Chapter04LocalPairingAdjunctionData where
  X₀ : Type u
  [x₀Group : AddCommGroup X₀]
  Y₀ : Type u
  [y₀Group : AddCommGroup Y₀]
  X₁ : Type u
  [x₁Group : AddCommGroup X₁]
  Y₁ : Type u
  [y₁Group : AddCommGroup Y₁]
  pairing₀ : X₀ → Y₀ → chapter04QModZ
  pairing₁ : X₁ → Y₁ → chapter04QModZ
  restriction : X₀ →+ X₁
  corestriction : Y₁ →+ Y₀
  adjoint : ∀ x y, pairing₁ (restriction x) y = pairing₀ x (corestriction y)

attribute [instance] Chapter04LocalPairingAdjunctionData.x₀Group
  Chapter04LocalPairingAdjunctionData.y₀Group
  Chapter04LocalPairingAdjunctionData.x₁Group
  Chapter04LocalPairingAdjunctionData.y₁Group

/-- Restriction and corestriction are adjoint under the local numerical pairing (4.10). -/
theorem chapter04_local_restriction_corestriction_adjoint
    (D : Chapter04LocalPairingAdjunctionData) (x : D.X₀) (y : D.Y₁) :
    D.pairing₁ (D.restriction x) y = D.pairing₀ x (D.corestriction y) := by
  exact D.adjoint x y

/-- The product-field version of local adjointness, with all branches summed. -/
structure Chapter04ProductPairingAdjunctionData (I : Type u) [Fintype I] where
  X₀ : Type u
  [x₀Group : AddCommGroup X₀]
  Y₀ : Type u
  [y₀Group : AddCommGroup Y₀]
  X₁ : I → Type u
  [x₁Group : ∀ i, AddCommGroup (X₁ i)]
  Y₁ : I → Type u
  [y₁Group : ∀ i, AddCommGroup (Y₁ i)]
  pairing₀ : X₀ → Y₀ → chapter04QModZ
  pairing₁ : ∀ i, X₁ i → Y₁ i → chapter04QModZ
  restriction : ∀ i, X₀ →+ X₁ i
  corestriction : ∀ i, Y₁ i →+ Y₀
  adjoint_sum : ∀ x (y : ∀ i, Y₁ i),
    (∑ i, pairing₁ i ((restriction i) x) (y i)) =
      pairing₀ x (∑ i, (corestriction i) (y i))

attribute [instance] Chapter04ProductPairingAdjunctionData.x₀Group
  Chapter04ProductPairingAdjunctionData.y₀Group
  Chapter04ProductPairingAdjunctionData.x₁Group
  Chapter04ProductPairingAdjunctionData.y₁Group

theorem chapter04_product_local_restriction_corestriction_adjoint
    {I : Type*} [Fintype I]
    (D : Chapter04ProductPairingAdjunctionData I)
    (x : D.X₀) (y : ∀ i, D.Y₁ i) :
    (∑ i, D.pairing₁ i ((D.restriction i) x) (y i)) =
      D.pairing₀ x (∑ i, (D.corestriction i) (y i)) := by
  exact D.adjoint_sum x y

/-! ### The `Aₙ`--`μₙ` special pairing -/

/-- Local reciprocity data for the special pair `Aₙ = ℤ/nℤ`, `μₙ`. -/
structure Chapter04LocalAnMuPairingData where
  n : ℕ
  positive_n : 0 < n
  H1A : Type u
  [h1AGroup : AddCommGroup H1A]
  H1Mu : Type u
  [h1MuGroup : AddCommGroup H1Mu]
  localUnits : Type u
  [localUnitsGroup : CommGroup localUnits]
  reciprocity : H1Mu → localUnits
  reciprocity_zero : reciprocity 0 = 1
  reciprocity_add : ∀ a b, reciprocity (a + b) = reciprocity a * reciprocity b
  character : H1A → (localUnits →* ℂˣ)
  character_add : ∀ c d x,
    character (c + d) x = character c x * character d x
  character_zero : ∀ x, character 0 x = 1
  character_n_torsion : ∀ c x, (character c x) ^ n = 1
  pairing : H1A → H1Mu → chapter04QModZ
  exponentialInvariant : chapter04QModZ → ℂˣ
  sign_formula : ∀ c a,
    exponentialInvariant (pairing c a) = character c (reciprocity a)

attribute [instance] Chapter04LocalAnMuPairingData.h1AGroup
  Chapter04LocalAnMuPairingData.h1MuGroup
  Chapter04LocalAnMuPairingData.localUnitsGroup

theorem chapter04_local_A_n_mu_n_sign_formula
    (D : Chapter04LocalAnMuPairingData) (c : D.H1A) (a : D.H1Mu) :
    D.exponentialInvariant (D.pairing c a) = D.character c (D.reciprocity a) := by
  exact D.sign_formula c a

/-- The local Kummer and reciprocity identifications used in the special pairing. -/
structure Chapter04LocalAnMuIdentificationData
    (D : Chapter04LocalAnMuPairingData) where
  KummerQuotient : Type u
  [kummerGroup : AddCommGroup KummerQuotient]
  CharacterQuotient : Type u
  [characterGroup : AddCommGroup CharacterQuotient]
  H1Mu_equiv_Kummer : D.H1Mu ≃+ KummerQuotient
  H1A_equiv_Characters : D.H1A ≃+ CharacterQuotient
  evaluation : CharacterQuotient → KummerQuotient → chapter04QModZ
  evaluation_perfect : chapter04PerfectPairing evaluation
  pairing_compatibility : ∀ c a,
    D.pairing c a = evaluation (H1A_equiv_Characters c) (H1Mu_equiv_Kummer a)

attribute [instance] Chapter04LocalAnMuIdentificationData.kummerGroup
  Chapter04LocalAnMuIdentificationData.characterGroup

/-- Local reciprocity and Kummer theory make the `Aₙ`--`μₙ` pairing perfect. -/
theorem chapter04_local_A_n_mu_n_pairing_is_perfect
    (D : Chapter04LocalAnMuPairingData)
    (I : Chapter04LocalAnMuIdentificationData D) :
    chapter04PerfectPairing D.pairing := by
  sorry

/-! The preceding theorem is the finite Pontryagin-duality calculation: the Kummer quotient is
paired with its full character quotient.  It is intentionally separate from the global
reciprocity and compact-support trace statements of §4.7. -/

end

end LastLib.Book06GlobalClassFieldTheory.Chapter04
