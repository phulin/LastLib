import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/-! ### 6.3 Relative finiteness -/

/- SOURCE_ISSUE (6.3): the displayed statement “For n≫0, `R^if_*(F⊗L^n)=0`” introduces `L`
without declaring it or saying that it is `f`-ample.  The assertion is false for an arbitrary line
bundle.  The smallest correction is: “Let `L` be an `f`-ample line bundle.  Then for n≫0, ...”.
-/

/-- On an affine base open, all cohomology modules are finite and vanish above one bound. -/
theorem chapter06_relative_affine_cohomology_finite
    {X S : Chapter06Scheme} (f : X ⟶ S) (hproj : chapter06IsProjective f)
    [IsLocallyNoetherian S]
    (F : X.Modules) (hF : Chapter06Coherent F)
    (U : S.Opens) (hU : IsAffineOpen U)
    (C : Chapter06CohomologyTheory (chapter06AffineBaseRing S U)) :
    (∀ i : ℕ, Module.Finite (chapter06AffineBaseRing S U)
      (C.H (chapter06RestrictToOpen (f ⁻¹ᵁ U) F) i)) ∧
      ∃ N : ℕ, ∀ i : ℕ, N < i →
        chapter06CohomologyIsZero C
          (chapter06RestrictToOpen (f ⁻¹ᵁ U) F) i := by
  sorry

/-- Every higher direct image of a coherent sheaf is coherent. -/
theorem chapter06_relative_higher_direct_image_coherent
    (D : Chapter06DerivedPushforwardTheory)
    {X S : Chapter06Scheme} (f : X ⟶ S) (hproj : chapter06IsProjective f)
    [IsLocallyNoetherian S]
    (F : X.Modules) (hF : Chapter06Coherent F) :
    ∀ i : ℕ, Chapter06Coherent (D.derivedPushforward f F i) := by
  sorry

/-- Relative Serre vanishing for all higher direct images. -/
theorem chapter06_relative_serre_vanishing
    (D : Chapter06DerivedPushforwardTheory)
    {X S : Chapter06Scheme} (f : X ⟶ S) (hproj : chapter06IsProjective f)
    [IsLocallyNoetherian S]
    (T : Chapter06TwistSystem X) [Chapter06RelativelyAmple f T]
    (F : X.Modules) (hF : Chapter06Coherent F) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ i : ℕ, 0 < i →
        chapter06SheafIsZero (D.derivedPushforward f (T.twist F n) i) := by
  sorry

/-- Fiberwise base change after a high twist, locally on the base. -/
theorem chapter06_relative_flat_base_change_local
    (D : Chapter06DerivedPushforwardTheory)
    {X S : Chapter06Scheme} (f : X ⟶ S) (hproj : chapter06IsProjective f)
    [IsLocallyNoetherian S]
    (T : Chapter06TwistSystem X) [Chapter06RelativelyAmple f T]
    (C : Chapter06CohomologyTheory ℤ)
    (B : Chapter06FiberTheory f)
    (F : X.Modules) (hF : Chapter06Coherent F) [Chapter06FlatOver f F]
    (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter06LocallyFree
        (chapter06RestrictToOpen U (D.derivedPushforward f (T.twist F n) 0)) ∧
      ∀ s : U, Nonempty (chapter06SheafFiber B (s : S)
          (D.derivedPushforward f (T.twist F n) 0) ≅
          C.H (B.fiberTwist (s : S) F n) 0) := by
  sorry

/-- If the base is quasi-compact, the local high-degree bound can be chosen globally. -/
theorem chapter06_relative_flat_base_change_quasi_compact
    (D : Chapter06DerivedPushforwardTheory)
    {X S : Chapter06Scheme} (f : X ⟶ S) (hproj : chapter06IsProjective f)
    [IsLocallyNoetherian S] [CompactSpace S]
    (T : Chapter06TwistSystem X) [Chapter06RelativelyAmple f T]
    (C : Chapter06CohomologyTheory ℤ)
    (B : Chapter06FiberTheory f)
    (F : X.Modules) (hF : Chapter06Coherent F) [Chapter06FlatOver f F] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter06LocallyFree (D.derivedPushforward f (T.twist F n) 0) ∧
      (∀ s : S, Nonempty (chapter06SheafFiber B s
          (D.derivedPushforward f (T.twist F n) 0) ≅
          C.H (B.fiberTwist s F n) 0)) ∧
      chapter06DerivedPushforwardCommutesWithBaseChange D f (T.twist F n) := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06
