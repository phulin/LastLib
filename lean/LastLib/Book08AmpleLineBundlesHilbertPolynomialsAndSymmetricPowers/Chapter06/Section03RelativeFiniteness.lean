import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06.Dependencies

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/-! ### 6.3 Relative finiteness -/

/-- On an affine base open, all cohomology modules are finite and vanish above one bound. -/
theorem chapter06_relative_affine_cohomology_finite
    (D : Chapter06DerivedPushforwardTheory)
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
  exact D.affineCohomologyFinite f hproj inferInstance F hF U hU C

/-- Every higher direct image of a coherent sheaf is coherent. -/
theorem chapter06_relative_higher_direct_image_coherent
    (D : Chapter06DerivedPushforwardTheory)
    {X S : Chapter06Scheme} (f : X ⟶ S) (hproj : chapter06IsProjective f)
    [IsLocallyNoetherian S]
    (F : X.Modules) (hF : Chapter06Coherent F) :
    ∀ i : ℕ, Chapter06Coherent (D.derivedPushforward f F i) := by
  exact D.higherDirectImageCoherent f hproj inferInstance F hF

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
  exact D.relativeSerreVanishing f hproj inferInstance T inferInstance F hF

/-- Fiberwise base change after a high twist, locally on the base. -/
theorem chapter06_relative_flat_base_change_local
    (D : Chapter06DerivedPushforwardTheory)
    {X S : Chapter06Scheme} (f : X ⟶ S) (hproj : chapter06IsProjective f)
    [IsLocallyNoetherian S]
    (T : Chapter06TwistSystem X) [Chapter06RelativelyAmple f T]
    (B : Chapter06FiberTheory f)
    (hcompat : Chapter06DerivedFiberCompatibility D f B)
    (hbase : Chapter06RelativeFlatBaseChangeInterface D f)
    (F : X.Modules) (hF : Chapter06Coherent F) [Chapter06FlatOver f F]
    (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter06LocallyFree
        (chapter06RestrictToOpen U (D.derivedPushforward f (T.twist F n) 0)) ∧
      (∀ s : U, Nonempty (chapter06SheafFiber B (s : S)
          (D.derivedPushforward f (T.twist F n) 0) ≅
          chapter06FiberCohomology B (s : S)
            (chapter06FiberTwist f T (s : S) F n) 0)) ∧
      chapter06DerivedPushforwardCommutesWithBaseChange D f (T.twist F n) 0 := by
  obtain ⟨n₁, hn₁⟩ :=
    hbase.local_freeness hproj inferInstance T inferInstance F hF inferInstance U hU
  obtain ⟨n₂, hn₂⟩ :=
    hcompat.fiberCohomologyIso T inferInstance F hF inferInstance
  obtain ⟨n₃, hn₃⟩ :=
    hbase.local_base_change hproj inferInstance T inferInstance F hF inferInstance U hU
  refine ⟨max (max n₁ n₂) n₃, ?_⟩
  intro n hn
  have hmax₁₂ : max n₁ n₂ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn₁' : n₁ ≤ n := le_trans (Nat.le_max_left _ _) hmax₁₂
  have hn₂' : n₂ ≤ n := le_trans (Nat.le_max_right _ _) hmax₁₂
  have hn₃' : n₃ ≤ n := le_trans (Nat.le_max_right _ _) hn
  refine ⟨hn₁ n hn₁', ?_, hn₃ n hn₃'⟩
  intro s
  exact hn₂ n hn₂' (s : S)

/-- If the base is quasi-compact, the local high-degree bound can be chosen globally. -/
theorem chapter06_relative_flat_base_change_quasi_compact
    (D : Chapter06DerivedPushforwardTheory)
    {X S : Chapter06Scheme} (f : X ⟶ S) (hproj : chapter06IsProjective f)
    [IsLocallyNoetherian S] [QuasiCompact (𝟙 S)]
    (T : Chapter06TwistSystem X) [Chapter06RelativelyAmple f T]
    (B : Chapter06FiberTheory f)
    (hcompat : Chapter06DerivedFiberCompatibility D f B)
    (hbase : Chapter06RelativeFlatBaseChangeInterface D f)
    (F : X.Modules) (hF : Chapter06Coherent F) [Chapter06FlatOver f F] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter06LocallyFree (D.derivedPushforward f (T.twist F n) 0) ∧
      (∀ s : S, Nonempty (chapter06SheafFiber B s
          (D.derivedPushforward f (T.twist F n) 0) ≅
          chapter06FiberCohomology B s (chapter06FiberTwist f T s F n) 0)) ∧
      chapter06DerivedPushforwardCommutesWithBaseChange D f (T.twist F n) 0 := by
  obtain ⟨n₁, hn₁⟩ :=
    hbase.quasi_compact_freeness_and_base_change hproj inferInstance inferInstance
      T inferInstance F hF inferInstance
  obtain ⟨n₂, hn₂⟩ :=
    hcompat.fiberCohomologyIso T inferInstance F hF inferInstance
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn
  have hn₁' : n₁ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn₂' : n₂ ≤ n := le_trans (Nat.le_max_right _ _) hn
  obtain ⟨hlf, hbc⟩ := hn₁ n hn₁'
  refine ⟨hlf, ?_, hbc⟩
  intro s
  exact hn₂ n hn₂' s

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06
