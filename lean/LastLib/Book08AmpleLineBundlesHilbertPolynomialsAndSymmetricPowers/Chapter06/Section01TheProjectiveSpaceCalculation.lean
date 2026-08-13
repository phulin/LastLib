import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

/-! ### 6.1 The projective-space calculation -/

/-- Every finite intersection of the standard projective-space charts is affine. -/
theorem chapter06_projective_space_cech_intersection_is_affine
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r)
    (s : Finset (Fin (r + 1))) (hs : s.Nonempty) :
    IsAffineOpen (chapter06CechIntersection P s) := by
  simpa [chapter06CechIntersection] using P.standardOpen_intersection_isAffine s hs

/-- The standard opens cover projective space and hence form the Cech cover used below. -/
theorem chapter06_projective_space_standard_cech_cover
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r) :
    ⨆ i, P.standardOpen i = ⊤ := by
  exact P.standardOpen_cover

/-- Intermediate cohomology of all integral twists of projective space vanishes. -/
theorem chapter06_projective_space_intermediate_vanishing
    {A : Type u} [CommRing A] {r : ℕ}
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    (H : Chapter06ProjectiveSpaceCohomologyData C P)
    (n : ℤ) (i : ℕ)
    (hi : 0 < i) (hir : i < r) :
    chapter06CohomologyIsZero C
      (P.twisting.twist P.twisting.structureSheaf n) i := by
  exact H.intermediate_vanishing n i hi hir

/-- All positive-degree cohomology of a nonnegative twist vanishes. -/
theorem chapter06_projective_space_nonnegative_vanishing
    {A : Type u} [CommRing A] {r : ℕ}
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    (H : Chapter06ProjectiveSpaceCohomologyData C P)
    (n : ℕ) (i : ℕ)
    (hi : 0 < i) :
    chapter06CohomologyIsZero C
      (P.twisting.twist P.twisting.structureSheaf n) i := by
  exact H.nonnegative_vanishing n i hi

/-- The zeroth cohomology of `𝒪(n)` is the homogeneous degree-`n` polynomial piece. -/
theorem chapter06_projective_space_h0_iso_polynomial_piece
    {A : Type u} [CommRing A] {r : ℕ}
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    (H : Chapter06ProjectiveSpaceCohomologyData C P) (n : ℕ) :
    Nonempty (C.H (P.twisting.twist P.twisting.structureSheaf n) 0 ≅
        ModuleCat.of A (Chapter06PolynomialDegreePiece A r n)) := by
  exact H.h0_iso n

/-- The homogeneous degree-`n` polynomial piece is free with the monomial basis. -/
theorem chapter06_polynomial_degree_piece_is_free
    {A : Type u} [CommRing A] (r n : ℕ) :
    chapter06FreeModuleOfRank A
      (ModuleCat.of A (Chapter06PolynomialDegreePiece A r n))
      (Fintype.card (Chapter06MonomialIndex r n)) := by
  sorry

/-- The monomial basis has the expected cardinality. -/
theorem chapter06_monomial_index_card
    (r n : ℕ) :
    Fintype.card (Chapter06MonomialIndex r n) = Nat.choose (n + r) r := by
  sorry

/-- Consequently, `H⁰(𝒪(n))` is a free `A`-module of rank `binomial (n+r) r`. -/
theorem chapter06_projective_space_h0_is_free_of_choose_rank
    {A : Type u} [CommRing A] {r : ℕ}
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    (H : Chapter06ProjectiveSpaceCohomologyData C P) (n : ℕ) :
    chapter06FreeModuleOfRank A
      (C.H (P.twisting.twist P.twisting.structureSheaf n) 0)
      (Nat.choose (n + r) r) := by
  sorry

/-- The Laurent monomials with every coordinate exponent negative span top cohomology. -/
theorem chapter06_projective_space_top_cohomology_laurent_generators
    {A : Type u} [CommRing A] {r : ℕ}
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    (H : Chapter06ProjectiveSpaceCohomologyData C P) (hr : 0 < r) (n : ℤ) :
    ∃ g : chapter06NegativeLaurentMonomial r n →
        C.H (P.twisting.twist P.twisting.structureSheaf n) r,
      chapter06ModuleSpans A
        (C.H (P.twisting.twist P.twisting.structureSheaf n) r) g := by
  sorry

/-- In top degree these Laurent monomials are a basis, with the empty-index case covering the
vanishing range. -/
theorem chapter06_projective_space_top_cohomology_laurent_basis
    {A : Type u} [CommRing A] {r : ℕ}
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    (H : Chapter06ProjectiveSpaceCohomologyData C P) (hr : 0 < r) (n : ℤ) :
    Nonempty (C.H (P.twisting.twist P.twisting.structureSheaf n) r ≅
      ModuleCat.of A (chapter06NegativeLaurentMonomial r n →₀ A)) := by
  exact H.top_basis hr n

/-- Top cohomology vanishes in the twists at and above the boundary `n = -r`. -/
theorem chapter06_projective_space_top_cohomology_vanishing
    {A : Type u} [CommRing A] {r : ℕ}
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    (H : Chapter06ProjectiveSpaceCohomologyData C P) (hr : 0 < r) (n : ℤ)
    (hn : -(r : ℤ) ≤ n) :
    chapter06CohomologyIsZero C
      (P.twisting.twist P.twisting.structureSheaf n) r := by
  exact H.top_vanishing hr n hn

/-- The Euler characteristic of every twist over a field is the binomial polynomial. -/
theorem chapter06_projective_space_euler_characteristic
    {k : Type u} [Field k] {r : ℕ}
    (C : Chapter06CohomologyTheory k)
    (P : Chapter06ProjectiveSpaceData k r)
    (H : Chapter06ProjectiveSpaceEulerCharacteristicData C P) (n : ℤ) :
    chapter06ProjectiveEulerCharacteristic C P P.twisting.structureSheaf n =
      chapter06BinomialPolynomialEval r n := by
  exact H.euler_characteristic n

/- The canonical module-theoretic scalar extension used by the Cech calculation. -/
def chapter06ScalarExtendedModule
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (M : ModuleCat.{u} A) : ModuleCat.{u} B :=
  (ModuleCat.extendScalars φ).obj M

/- `DEPENDENCY_GUESS`: the canonical `P_B` must be the scalar base change of `P_A`, and the two
cohomology theories must be the corresponding scalar extensions.  The compatibility record keeps
that genuinely missing comparison data explicit instead of asserting it for unrelated theories. -/
structure Chapter06ProjectiveSpaceCohomologyScalarExtensionData
    {A B : Type u} [CommRing A] [CommRing B] {r : ℕ}
    (φ : A →+* B)
    (C_A : Chapter06CohomologyTheory A)
    (C_B : Chapter06CohomologyTheory B)
    (P_A : Chapter06ProjectiveSpaceData A r)
    (P_B : Chapter06ProjectiveSpaceData B r) where
  comparison : ∀ (n : ℤ) (i : ℕ),
    Nonempty (C_B.H (P_B.twisting.twist P_B.twisting.structureSheaf n) i ≅
      chapter06ScalarExtendedModule φ
        (C_A.H (P_A.twisting.twist P_A.twisting.structureSheaf n) i))

theorem chapter06_projective_space_cohomology_scalar_extension
    {A B : Type u} [CommRing A] [CommRing B] {r : ℕ}
    (φ : A →+* B)
    (C_A : Chapter06CohomologyTheory A)
    (C_B : Chapter06CohomologyTheory B)
    (P_A : Chapter06ProjectiveSpaceData A r)
    (P_B : Chapter06ProjectiveSpaceData B r)
    (hcompat : Chapter06ProjectiveSpaceCohomologyScalarExtensionData φ C_A C_B P_A P_B)
    (n : ℤ) (i : ℕ) :
    Nonempty (C_B.H (P_B.twisting.twist P_B.twisting.structureSheaf n) i ≅
        chapter06ScalarExtendedModule φ
          (C_A.H (P_A.twisting.twist P_A.twisting.structureSheaf n) i)) := by
  exact hcompat.comparison n i

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06
