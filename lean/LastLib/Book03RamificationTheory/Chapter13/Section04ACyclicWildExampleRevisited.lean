import LastLib.Book03RamificationTheory.Chapter13.Section02TheRegularRepresentation
import LastLib.Book03RamificationTheory.Chapter11.Section04FixedSpaceCalculations

namespace LastLib.Book03RamificationTheory.Chapter13

noncomputable section

open LastLib.Book03RamificationTheory.Chapter11
open LastLib.Book03RamificationTheory.Chapter12
open scoped BigOperators

/-! ## 13.4. A cyclic wild example revisited -/

/- The break condition `p ∤ m` is recorded in addition to the reusable
one-break ramification profile from Chapter 11. -/
structure Chapter13ArtinSchreierBreakExample
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) where
  wild : Chapter11WildCyclicBreakData G D
  p_not_dvd_m : ¬ wild.p ∣ wild.m

theorem chapter13_artin_schreier_break_positive
    {G : Type*} [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (A : Chapter13ArtinSchreierBreakExample D) :
    0 < A.wild.m :=
  A.wild.m_pos

theorem chapter13_cyclic_wild_nontrivial_character_conductor
    {E G : Type*} [Field E] [CharZero E] [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D)
    (χ : G →* Eˣ)
    (hχ : Chapter11NontrivialMultiplicativeCharacter χ) :
    chapter13ArtinConductor D (chapter11OneDimensionalRepresentation χ) =
      (W.m + 1 : ℚ) := by
  sorry

def chapter13CyclicWildConductorSum
    {G : Type*} [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D)
    (C : Chapter11AllNontrivialCharacters G D W) : ℚ :=
  ∑ j : Fin (W.p - 1),
    chapter13CharacterConductor D
      (FDRep.of (chapter11OneDimensionalRepresentation (C.characters j)))

theorem chapter13_cyclic_wild_sum_of_nontrivial_conductors
    {G : Type*} [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D)
    (C : Chapter11AllNontrivialCharacters G D W) :
    chapter13CyclicWildConductorSum W C =
      ((W.p - 1 : ℕ) : ℚ) * (W.m + 1 : ℚ) := by
  sorry

theorem chapter13_cyclic_wild_sum_eq_discriminant_exponent
    {G : Type*} [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D)
    (C : Chapter11AllNontrivialCharacters G D W)
    (Δ : Chapter13LocalDiscriminantData D)
    (hres : D.residue_separable)
    (hf : D.f = 1)
    (hdifferent : Δ.differentExponent = (W.p - 1) * (W.m + 1)) :
    chapter13CyclicWildConductorSum W C =
      (Δ.discriminantExponent : ℚ) := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: the preceding different chapter should supply the
derivative valuation and prove `hderivative`; this declaration keeps that
calculation as an explicit bridge instead of identifying a derivative model
with the abstract different by definition.

A direct comparison theorem records the four computations mentioned in the
source: a derivative value, Hilbert's sum, the character sum, and the regular
representation. -/
theorem chapter13_cyclic_wild_four_computations_agree
    {G : Type*} [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (W : Chapter11WildCyclicBreakData G D)
    (C : Chapter11AllNontrivialCharacters G D W)
    (Δ : Chapter13LocalDiscriminantData D)
    (dDerivative : ℕ)
    (hderivative : dDerivative = Δ.differentExponent)
    (hdifferent : Δ.differentExponent = (W.p - 1) * (W.m + 1))
    (hres : D.residue_separable)
    (hf : D.f = 1) :
    (dDerivative : ℚ) = chapter13CyclicWildConductorSum W C ∧
      (dDerivative : ℚ) =
        chapter11ArtinConductor D (chapter13RegularRepresentation ℚ G) := by
  sorry

/- The tame cyclic laboratory uses a complete list of the `e - 1` nontrivial
characters, so that its sum can be compared directly with the tame
discriminant exponent. -/
structure Chapter13TameCyclicData
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) where
  e : ℕ
  cyclic : IsCyclic G
  group_card_eq : Fintype.card G = e
  residue_degree_eq_one : D.f = 1
  inertia_eq_top : D.inertia = ⊤
  lower_one_eq_bot : D.lower 1 = ⊥
  characters : Fin (e - 1) → G →* ℂˣ
  pairwise_ne : Function.Injective characters
  nontrivial : ∀ j, Chapter11NontrivialMultiplicativeCharacter (characters j)
  complete :
    ∀ χ : G →* ℂˣ,
      Chapter11NontrivialMultiplicativeCharacter χ →
        ∃ j, characters j = χ

def chapter13TameCyclicConductorSum
    {G : Type*} [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (T : Chapter13TameCyclicData D) : ℚ :=
  ∑ j : Fin (T.e - 1),
    chapter13CharacterConductor D
      (FDRep.of (chapter11OneDimensionalRepresentation (T.characters j)))

theorem chapter13_tame_cyclic_nontrivial_character_conductor
    {G : Type*} [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (T : Chapter13TameCyclicData D)
    (hres : D.residue_separable) (j : Fin (T.e - 1)) :
    chapter13CharacterConductor D
      (FDRep.of (chapter11OneDimensionalRepresentation (T.characters j))) = 1 := by
  sorry

theorem chapter13_tame_cyclic_sum_of_nontrivial_conductors
    {G : Type*} [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (T : Chapter13TameCyclicData D)
    (hres : D.residue_separable) :
    chapter13TameCyclicConductorSum T = ((T.e - 1 : ℕ) : ℚ) := by
  sorry

theorem chapter13_tame_cyclic_sum_eq_discriminant_exponent
    {G : Type*} [Group G] [Fintype G]
    {D : Chapter11RamificationData G}
    (T : Chapter13TameCyclicData D)
    (Δ : Chapter13LocalDiscriminantData D)
    (hres : D.residue_separable)
    (hdifferent : Δ.differentExponent = T.e - 1) :
    chapter13TameCyclicConductorSum T =
      (Δ.discriminantExponent : ℚ) := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter13
