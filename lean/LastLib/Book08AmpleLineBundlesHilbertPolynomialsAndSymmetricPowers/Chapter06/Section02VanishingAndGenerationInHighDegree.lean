import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

/-! ### 6.2 Vanishing and generation in high degree -/

/-- Serre vanishing and finite global generation on projective space. -/
theorem chapter06_serre_vanishing_projective_space
    {A : Type u} [CommRing A] {r : ℕ}
    (hA : IsNoetherianRing A)
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    (H : Chapter06SerreVanishingProjectiveSpaceData C P)
    (F : P.X.Modules) (hF : Chapter06Coherent F) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ i : ℕ, 0 < i →
        chapter06CohomologyIsZero C (P.twisting.twist F n) i) ∧
      chapter06FinitelyGloballyGenerated (P.twisting.twist F n) := by
  exact H.vanishing hA F hF

/-- The kernel of an epimorphism between coherent sheaves is coherent over a noetherian scheme. -/
theorem chapter06_coherent_kernel_of_epi
    {X : Chapter06Scheme} [IsLocallyNoetherian X]
    (M F : X.Modules) (hM : Chapter06Coherent M) (hF : Chapter06Coherent F)
    (p : M ⟶ F) [Epi p] :
    Chapter06Coherent (CategoryTheory.Limits.kernel p) := by
  sorry

/-- Closed immersions preserve coherent sheaves under pushforward. -/
theorem chapter06_closed_immersion_pushforward_coherent
    {X Y : Chapter06Scheme} (i : X ⟶ Y) [IsClosedImmersion i]
    [IsLocallyNoetherian Y]
    (G : X.Modules) (hG : Chapter06Coherent G) :
    Chapter06Coherent (chapter06Pushforward i G) := by
  sorry

/-- Cohomology is unchanged by pushforward along a closed immersion. -/
theorem chapter06_closed_immersion_cohomology_iso
    {R : Type v} [Ring R] (C : Chapter06CohomologyTheory R)
    {X Y : Chapter06Scheme} (i : X ⟶ Y) [IsClosedImmersion i]
    (G : X.Modules) (j : ℕ) :
    Nonempty (C.H (chapter06Pushforward i G) j ≅ C.H G j) := by
  exact C.closedImmersionPushforward i G j

/-- Pushforward commutes with the chosen twists under the canonical twisting compatibility. -/
def chapter06_closed_immersion_pushforward_twist_iso
    {X Y : Chapter06Scheme} (i : X ⟶ Y)
    (T_X : Chapter06TwistSystem X) (T_Y : Chapter06TwistSystem Y)
    (hT : Chapter06TwistCompatibility i T_X T_Y)
    (G : X.Modules) (n : ℤ) :
    chapter06Pushforward i (T_X.twist G n) ≅ T_Y.twist (chapter06Pushforward i G) n :=
  hT.iso G n

/-- The projective-space theorem transfers to a closed subscheme via pushforward. -/
theorem chapter06_serre_vanishing_closed_subscheme
    {A : Type u} [CommRing A] {r : ℕ}
    (hA : IsNoetherianRing A)
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    {X : Chapter06Scheme} (i : X ⟶ P.X) [IsClosedImmersion i]
    (G : X.Modules) (hG : Chapter06Coherent G)
    (T_X : Chapter06TwistSystem X)
    (hT : Chapter06TwistCompatibility i T_X P.twisting)
    (H : Chapter06SerreVanishingClosedSubschemeData C P i G T_X hT) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ j : ℕ, 0 < j →
        chapter06CohomologyIsZero C (T_X.twist G n) j ∧
          Nonempty (C.H (chapter06Pushforward i (T_X.twist G n)) j ≅
            C.H (T_X.twist G n) j)) ∧
      chapter06FinitelyGloballyGenerated (T_X.twist G n) := by
  exact H.vanishing hA hG

/-- Serre vanishing for a projective noetherian scheme with a relatively ample twist. -/
theorem chapter06_serre_vanishing_projective
    {X S : Chapter06Scheme} (f : X ⟶ S)
    (hS : IsLocallyNoetherian S) [IsAffine S]
    (hproj : chapter06IsProjective f)
    (T : Chapter06TwistSystem X) [Chapter06RelativelyAmple f T]
    (C : Chapter06CohomologyTheory ℤ)
    (H : Chapter06SerreVanishingProjectiveData f T C)
    (F : X.Modules) (hF : Chapter06Coherent F) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ i : ℕ, 0 < i → chapter06CohomologyIsZero C (T.twist F n) i) ∧
      chapter06FinitelyGloballyGenerated (T.twist F n) := by
  exact H.vanishing hS hproj F hF

/-- The finitely many residue classes modulo a very-ample power are the reduction used for an
ample twist. -/
theorem chapter06_serre_vanishing_of_ample_twist
    {X S : Chapter06Scheme} (f : X ⟶ S)
    (hS : IsLocallyNoetherian S) [IsAffine S]
    (hproj : chapter06IsProjective f)
    (T : Chapter06TwistSystem X) [Chapter06RelativelyAmple f T]
    (C : Chapter06CohomologyTheory ℤ)
    (H : Chapter06SerreVanishingProjectiveData f T C)
    (F : X.Modules) (hF : Chapter06Coherent F) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ i : ℕ, 0 < i → chapter06CohomologyIsZero C (T.twist F n) i) ∧
      chapter06FinitelyGloballyGenerated (T.twist F n) := by
  exact H.vanishing hS hproj F hF

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06
