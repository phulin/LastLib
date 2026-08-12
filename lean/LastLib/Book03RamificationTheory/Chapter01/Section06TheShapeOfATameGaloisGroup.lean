import LastLib.Book03RamificationTheory.Chapter01.Section05TheMaximalTameStage

namespace LastLib.Book03RamificationTheory.Chapter01

noncomputable section

open scoped BigOperators WithZero

/-! ## 1.6. The shape of a tame Galois group -/

/-- A tame finite residue field gives the displayed Frobenius/tame-inertia
presentation, with the order relation left explicit. -/
theorem chapter01_tame_group_presentation_exists
    {K L k l : Type*} [Field K] [Field L] [Field k] [Field l]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Finite (chapter01GaloisGroup K L)]
    [Algebra k l] [FiniteDimensional k l] [Fintype k] [Finite l]
    [Algebra.IsAlgebraic k l]
    (I : Subgroup (chapter01GaloisGroup K L)) [I.Normal]
    (q e f : ℕ) (hq : Fintype.card k = q)
    (hf : Module.finrank k l = f)
    (hI : Nat.card I = e)
    (hresidue_separable : Algebra.IsSeparable k l)
    (htame : Nat.Coprime e (chapter01CharacteristicExponent k)) :
    Nonempty (Chapter01FiniteTameGroupPresentation
      (chapter01GaloisGroup K L) I q e f) := by
  sorry

/-- In the arithmetic convention, conjugation acts on a tame generator by the
`q`th power. -/
theorem chapter01_arithmetic_frobenius_conjugation
    {G : Type*} [Group G] [Finite G]
    {I : Subgroup G} [I.Normal] (q e f : ℕ)
    (D : Chapter01FiniteTameGroupPresentation G I q e f) :
    D.frobenius * D.tameGenerator * D.frobenius⁻¹ =
      D.tameGenerator ^ q := D.conjugation

/-- Geometric Frobenius reverses the conjugation convention. -/
theorem chapter01_geometric_frobenius_conjugation
    {G : Type*} [Group G] [Finite G]
    {I : Subgroup G} [I.Normal] (q e f : ℕ)
    (D : Chapter01FiniteTameGroupPresentation G I q e f) :
    ∃ r : ℕ,
      D.frobenius⁻¹ * D.tameGenerator * D.frobenius =
        D.tameGenerator ^ r := by
  sorry

/-- The tame filtration has only the ambient, tame-inertia, and trivial levels. -/
def chapter01TameRamificationGroup
    {G : Type*} [Group G] (I : Subgroup G) (i : ℤ) : Subgroup G :=
  if i < 0 then ⊤ else if i = 0 then I else ⊥

@[simp] theorem chapter01_tame_ramification_group_neg_one
    {G : Type*} [Group G] (I : Subgroup G) :
    chapter01TameRamificationGroup I (-1) = ⊤ := by
  simp [chapter01TameRamificationGroup]

@[simp] theorem chapter01_tame_ramification_group_zero
    {G : Type*} [Group G] (I : Subgroup G) :
    chapter01TameRamificationGroup I 0 = I := by
  simp [chapter01TameRamificationGroup]

@[simp] theorem chapter01_tame_ramification_group_one
    {G : Type*} [Group G] (I : Subgroup G) :
    chapter01TameRamificationGroup I 1 = ⊥ := by
  simp [chapter01TameRamificationGroup]

/-- Data expressing that conjugation carries the tame character through the
natural residue action. -/
-- LOCAL_DEPENDENCY_GUESS: a valuation-level naturality theorem should
-- construct this package from the inertia character and residue action; the
-- compatibility is kept as data until that earlier interface is available.
structure Chapter01TameCharacterConjugationData
    {G I l : Type*} [Group G] [Group I] [Field l]
    (I' : Subgroup G) [I'.Normal] where
  tameCharacter : I →* lˣ
  inclusion : I →* G
  residueAction : G →* RingAut l
  inclusion_injective : Function.Injective inclusion
  stable : ∀ g : G, ∀ i : I,
    g * inclusion i * g⁻¹ ∈ I'
  conjugateCharacter : I' →* lˣ
  compatibility : ∀ g : G, ∀ i : I,
    conjugateCharacter ⟨g * inclusion i * g⁻¹, stable g i⟩ =
      Units.map (residueAction g).toRingHom.toMonoidHom (tameCharacter i)

/-- The conjugation-compatibility eliminator. -/
theorem chapter01_tame_character_conjugation_compatibility
    {G I l : Type*} [Group G] [Group I] [Field l]
    (I' : Subgroup G) [I'.Normal]
    (D : Chapter01TameCharacterConjugationData (G := G) (I := I) (l := l) I') :
    ∀ g : G, ∀ i : I,
      D.conjugateCharacter ⟨g * D.inclusion i * g⁻¹, D.stable g i⟩ =
        Units.map (D.residueAction g).toRingHom.toMonoidHom (D.tameCharacter i) :=
  D.compatibility

end

end LastLib.Book03RamificationTheory.Chapter01
