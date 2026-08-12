import LastLib.Book03RamificationTheory.Chapter13.Core

namespace LastLib.Book03RamificationTheory.Chapter13

noncomputable section

open LastLib.Book03RamificationTheory.Chapter11
open LastLib.Book03RamificationTheory.Chapter12
open scoped BigOperators

/-! ## 13.2. The regular representation -/

/-- The regular representation on the group algebra `E[G]`. -/
noncomputable def chapter13RegularRepresentation
    (E G : Type*) [Semiring E] [Group G] :
    Representation E G (MonoidAlgebra E G) :=
  Representation.ofMulAction E G G

@[simp] theorem chapter13RegularRepresentation_apply
    (E G : Type*) [Semiring E] [Group G] (g : G) :
    chapter13RegularRepresentation E G g = Representation.ofMulAction E G G g :=
  rfl

/- The invariant algebra elements are precisely the coefficient functions that
are constant on the relevant left-orbits. -/
theorem chapter13_regular_invariant_coeff_iff
    {E G : Type*} [Field E] [Group G] [Fintype G]
    (H : Subgroup G) (v : MonoidAlgebra E G) :
    v ∈ Representation.invariants
        ((chapter13RegularRepresentation E G).comp H.subtype) ↔
      ∀ h : H, ∀ x : G,
        v.coeff ((h : G)⁻¹ * x) = v.coeff x := by
  sorry

/- The dimension of the invariant space is the number of H-orbits on G.  For
the regular action those orbits all have cardinality `|H|`. -/
theorem chapter13_regular_invariant_finrank
    {E G : Type*} [Field E] [Group G] [Fintype G]
    (H : Subgroup G) :
    Module.finrank E
        (Representation.invariants
          ((chapter13RegularRepresentation E G).comp H.subtype)) =
      Fintype.card G / Fintype.card H := by
  sorry

theorem chapter13_regular_fixed_space_codimension
    {E G : Type*} [Field E] [Group G] [Fintype G]
    (D : Chapter11RamificationData G) (i : ℕ) :
    chapter11FixedSpaceCodimension D
        (chapter13RegularRepresentation E G) (D.lower i) =
      Fintype.card G - Fintype.card G / Fintype.card (D.lower i) := by
  sorry

/-- The displayed finite form of the regular-representation conductor sum. -/
def chapter13RegularConductorSum
    {G : Type*} [Group G] [Fintype G]
    (D : Chapter11RamificationData G) : ℚ :=
  Finset.sum (Finset.range D.bound) (fun i =>
    (Fintype.card (D.lower i) : ℚ) /
        (Fintype.card D.inertia : ℚ) *
      ((Fintype.card G : ℚ) -
        ((Fintype.card G / Fintype.card (D.lower i) : ℕ) : ℚ)))

theorem chapter13_regular_conductor_eq_fixed_space_sum
    {E G : Type*} [Field E] [Group G] [Fintype G]
    (D : Chapter11RamificationData G) :
    chapter11ArtinConductor D (chapter13RegularRepresentation E G) =
      chapter13RegularConductorSum D := by
  sorry

theorem chapter13_regular_conductor_eq_expanded_sum
    {E G : Type*} [Field E] [Group G] [Fintype G]
    (D : Chapter11RamificationData G) :
    chapter11ArtinConductor D (chapter13RegularRepresentation E G) =
      Finset.sum (Finset.range D.bound) (fun i =>
        (Fintype.card (D.lower i) : ℚ) /
        (Fintype.card D.inertia : ℚ) *
          ((Fintype.card G : ℚ) -
            ((Fintype.card G / Fintype.card (D.lower i) : ℕ) : ℚ))) := by
  sorry

/- Using `|G| = |G₀| f`, the regular fixed-space defects become the Hilbert
sum, with the residue-degree factor that norms the different downstairs. -/
theorem chapter13_regular_conductor_eq_residue_weighted_displacement_sum
    {E G : Type*} [Field E] [Group G] [Fintype G]
    (D : Chapter11RamificationData G)
    (hres : D.residue_separable) :
    chapter11ArtinConductor D (chapter13RegularRepresentation E G) =
      (D.f : ℚ) * (chapter13DifferentDisplacementSum D : ℚ) := by
  sorry

theorem chapter13_regular_conductor_eq_residue_degree_mul_different
    {E G : Type*} [Field E] [Group G] [Fintype G]
    (D : Chapter11RamificationData G)
    (Δ : Chapter13LocalDiscriminantData D)
    (hres : D.residue_separable) :
    chapter11ArtinConductor D (chapter13RegularRepresentation E G) =
      (D.f : ℚ) * (Δ.differentExponent : ℚ) := by
  sorry

/- The regular representation sees every element of G, so its conductor is
the local discriminant exponent. -/
theorem chapter13_regular_conductor_eq_discriminant_exponent
    {E G : Type*} [Field E] [Group G] [Fintype G]
    (D : Chapter11RamificationData G)
    (Δ : Chapter13LocalDiscriminantData D)
    (hres : D.residue_separable) :
    chapter11ArtinConductor D (chapter13RegularRepresentation E G) =
      (Δ.discriminantExponent : ℚ) := by
  sorry

end

end LastLib.Book03RamificationTheory.Chapter13
