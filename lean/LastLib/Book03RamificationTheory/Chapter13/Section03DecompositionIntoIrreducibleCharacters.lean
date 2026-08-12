import LastLib.Book03RamificationTheory.Chapter13.Section02TheRegularRepresentation

namespace LastLib.Book03RamificationTheory.Chapter13

noncomputable section

open LastLib.Book03RamificationTheory.Chapter11
open LastLib.Book03RamificationTheory.Chapter12
open scoped BigOperators DirectSum

/-! ## 13.3. Decomposition into irreducible characters -/

/- LOCAL_DEPENDENCY_GUESS: this finite family is the book-facing replacement
for Mathlib's currently categorical simple-object indexing.  The regular
equivalence is the semisimple decomposition supplied by Maschke over `ℂ`. -/
structure Chapter13ComplexIrreducibleFamily
    (G : Type*) [Group G] [Fintype G] where
  index : Type
  [index_fintype : Fintype index]
  representation : index → FDRep ℂ G
  irreducible : ∀ i, Representation.IsIrreducible (representation i).ρ
  pairwise_nonisomorphic :
    ∀ ⦃i j : index⦄, i ≠ j →
      ¬ Nonempty (Representation.Equiv (representation i).ρ (representation j).ρ)

attribute [instance] Chapter13ComplexIrreducibleFamily.index_fintype

def chapter13MultiplicityIndex
    {G : Type*} [Group G] [Fintype G]
    (F : Chapter13ComplexIrreducibleFamily G) : Type :=
  Σ i : F.index, Fin (Module.finrank ℂ (F.representation i).V)

noncomputable def chapter13RepeatedIrreducibleRepresentation
    {G : Type*} [Group G] [Fintype G]
    (F : Chapter13ComplexIrreducibleFamily G) :
    Representation ℂ G
      (⨁ j : (chapter13MultiplicityIndex F), (F.representation j.1).V) :=
  Representation.directSum
    (fun j : chapter13MultiplicityIndex F => (F.representation j.1).ρ)

structure Chapter13RegularIrreducibleDecomposition
    (G : Type*) [Group G] [Fintype G] where
  family : Chapter13ComplexIrreducibleFamily G
  regular_equiv :
    Nonempty
      (Representation.Equiv (chapter13RegularRepresentation ℂ G)
        (chapter13RepeatedIrreducibleRepresentation family))

theorem chapter13_regular_representation_has_irreducible_decomposition
    {G : Type*} [Group G] [Fintype G] :
    Nonempty (Chapter13RegularIrreducibleDecomposition G) := by
  sorry

def chapter13IrreducibleCharacter
    {G : Type*} [Group G] [Fintype G]
    (F : Chapter13ComplexIrreducibleFamily G) (i : F.index) : G → ℂ :=
  (F.representation i).character

theorem chapter13_regular_character_decomposition
    {G : Type*} [Group G] [Fintype G]
    (R : Chapter13RegularIrreducibleDecomposition G) :
    (chapter13RegularRepresentation ℂ G).character =
      fun g =>
        ∑ i : R.family.index,
          (Module.finrank ℂ (R.family.representation i).V : ℂ) *
            chapter13IrreducibleCharacter R.family i g := by
  sorry

/- Additivity of the conductor transfers the character decomposition to the
weighted conductor identity. -/
theorem chapter13_regular_conductor_decomposition
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G)
    (R : Chapter13RegularIrreducibleDecomposition G) :
    chapter11ArtinConductor D (chapter13RegularRepresentation ℂ G) =
      ∑ i : R.family.index,
        (Module.finrank ℂ (R.family.representation i).V : ℚ) *
          chapter13CharacterConductor D (R.family.representation i) := by
  sorry

theorem chapter13_conductor_discriminant_irreducible_sum
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G)
    (Δ : Chapter13LocalDiscriminantData D)
    (hres : D.residue_separable)
    (R : Chapter13RegularIrreducibleDecomposition G) :
    (Δ.discriminantExponent : ℚ) =
      ∑ i : R.family.index,
        (Module.finrank ℂ (R.family.representation i).V : ℚ) *
          chapter13CharacterConductor D (R.family.representation i) := by
  sorry

def Chapter13OneDimensionalIrreducibleFamily
    {G : Type*} [Group G] [Fintype G]
    (R : Chapter13RegularIrreducibleDecomposition G) : Prop :=
  ∀ i : R.family.index,
    Module.finrank ℂ (R.family.representation i).V = 1

theorem chapter13_abelian_irreducibles_are_one_dimensional
    {G : Type*} [CommGroup G] [Fintype G]
    (R : Chapter13RegularIrreducibleDecomposition G) :
    Chapter13OneDimensionalIrreducibleFamily R := by
  sorry

theorem chapter13_abelian_conductor_discriminant_sum
    {G : Type*} [CommGroup G] [Fintype G]
    (D : Chapter11RamificationData G)
    (Δ : Chapter13LocalDiscriminantData D)
    (hres : D.residue_separable)
    (R : Chapter13RegularIrreducibleDecomposition G)
    (hone : Chapter13OneDimensionalIrreducibleFamily R) :
    (Δ.discriminantExponent : ℚ) =
      ∑ i : R.family.index,
        chapter13CharacterConductor D (R.family.representation i) := by
  sorry

/- The ideal statement is kept separate from the exponent statement.  The
natural-number witnesses `a` are the integral conductor exponents of the
characters, as supplied by Artin integrality. -/
theorem chapter13_abelian_conductor_ideal_identity
    {A G : Type*} [CommRing A] [CommGroup G] [Fintype G]
    (m : Ideal A)
    (D : Chapter11RamificationData G)
    (Δ : Chapter13LocalDiscriminantData D)
    (hres : D.residue_separable)
    (R : Chapter13RegularIrreducibleDecomposition G)
    (hone : Chapter13OneDimensionalIrreducibleFamily R)
    (a : R.family.index → ℕ)
    (ha : ∀ i,
      (a i : ℚ) = chapter13CharacterConductor D (R.family.representation i)) :
    chapter13DiscriminantIdeal m Δ.discriminantExponent =
      ∏ i : R.family.index, chapter13ConductorIdeal m (a i) := by
  sorry

theorem chapter13_trivial_character_contributes_unit_ideal
    {A : Type*} [CommRing A]
    (m : Ideal A) :
    chapter13ConductorIdeal m 0 = ⊤ := by
  exact chapter13_trivial_conductor_ideal_eq_unit m

end

end LastLib.Book03RamificationTheory.Chapter13
