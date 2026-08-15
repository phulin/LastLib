import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06.Dependencies
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.EpiMono

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
    (hC : Chapter06ProjectiveSpaceCechRealization C P)
    (hSerre : Chapter06ProjectiveSpaceSerreInterface hA C P hC)
    (F : P.X.Modules) (hF : Chapter06Coherent F) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ i : ℕ, 0 < i →
        chapter06CohomologyIsZero C (P.twisting.twist F n) i) ∧
      chapter06FinitelyGloballyGenerated (P.twisting.twist F n) := by
  simpa [chapter06SerreHighDegreeConclusion] using hSerre.for_coherent F hF

/-- The kernel of an epimorphism between coherent sheaves is coherent over a noetherian scheme. -/
theorem chapter06_coherent_kernel_of_epi
    {X : AlgebraicGeometry.Scheme.{u}} [IsLocallyNoetherian X]
    (M F : X.Modules) (hM : Chapter06Coherent M) (hF : Chapter06Coherent F)
    (p : M ⟶ F) [Epi p] (hClosure : Chapter06CoherentClosureInterface.{u}) :
    Chapter06Coherent (CategoryTheory.Limits.kernel p) := by
  exact hClosure.kernel_of_epi M F hM hF p

/-- Closed immersions preserve coherent sheaves under pushforward. -/
theorem chapter06_closed_immersion_pushforward_coherent
    {X Y : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    [IsLocallyNoetherian Y]
    (G : X.Modules) (hG : Chapter06Coherent G)
    (hClosure : Chapter06CoherentClosureInterface.{u}) :
    Chapter06Coherent (chapter06Pushforward i G) := by
  exact hClosure.closedImmersion_pushforward i G hG

/-- Cohomology is unchanged by pushforward along a closed immersion. -/
theorem chapter06_closed_immersion_cohomology_iso
    {R : Type v} [CommRing R] (C : Chapter06CohomologyTheory R)
    (hC : Chapter06CanonicalCohomologyRealization C)
    {X Y : Chapter06Scheme} (i : X ⟶ Y) [IsClosedImmersion i]
    (G : X.Modules) (j : ℕ) :
    Nonempty (C.H (chapter06Pushforward i G) j ≅ C.H G j) := by
  exact hC.cohomologyClosedImmersionIso i G j

/-- Pushforward commutes with the chosen twists under the canonical twisting compatibility. -/
def chapter06_closed_immersion_pushforward_twist_iso
    {X Y : Chapter06Scheme} (i : X ⟶ Y)
    (T_X : Chapter06TwistSystem X) (T_Y : Chapter06TwistSystem Y)
    (hT : Chapter06TwistCompatibility i T_X T_Y)
    (G : X.Modules) (n : ℤ) :
    chapter06Pushforward i (T_X.twist G n) ≅ T_Y.twist (chapter06Pushforward i G) n :=
  hT.iso G n

private theorem chapter06_finitely_globally_generated_of_closed_immersion_pushforward
    {X Y : Chapter06Scheme} (i : X ⟶ Y) [IsClosedImmersion i]
    (F : X.Modules)
    (hF : chapter06FinitelyGloballyGenerated (chapter06Pushforward i F)) :
    chapter06FinitelyGloballyGenerated F := by
  classical
  have hFinal : Functor.Final (TopologicalSpace.Opens.map i.base) := by
    apply Functor.final_of_exists_of_isFiltered
    · intro U
      obtain ⟨V, hV, hVU⟩ :=
        i.isClosedEmbedding.isInducing.isOpen_iff.mp U.2
      have hVU' :
          (TopologicalSpace.Opens.map i.base).obj ⟨V, hV⟩ = U := by
        ext x
        change x ∈ i.base ⁻¹' V ↔ x ∈ (U : Set X)
        rw [hVU]
      exact ⟨⟨V, hV⟩, ⟨eqToHom hVU'.symm⟩⟩
    · intro {d c} s s'
      have hss : s = s' := Subsingleton.elim _ _
      exact ⟨c, 𝟙 _, by simp [hss]⟩
  letI : Functor.Final (TopologicalSpace.Opens.map i.base) := hFinal
  have hFaithful : (Scheme.Modules.pushforward i).Faithful := by
    constructor
    intro M N f g h
    apply Scheme.Modules.hom_ext f g
    intro U
    obtain ⟨V, hV, hVU⟩ :=
      i.isClosedEmbedding.isInducing.isOpen_iff.mp U.2
    have hVU' : i ⁻¹ᵁ (⟨V, hV⟩ : Y.Opens) = U := by
      ext x
      change x ∈ i.base ⁻¹' V ↔ x ∈ (U : Set X)
      rw [hVU]
    have h' := congrArg (fun k => k.app (⟨V, hV⟩ : Y.Opens)) h
    simpa [hVU'] using h'
  letI : (Scheme.Modules.pushforward i).Faithful := hFaithful
  rcases hF with ⟨σ, hσ⟩
  let hsections : Function.Bijective
      (SheafOfModules.pushforwardSections i.toRingCatSheafHom (M := F)) :=
    SheafOfModules.bijective_pushforwardSections i.toRingCatSheafHom F
  let σs : σ.I → F.sections := fun k ↦
    Function.invFun (SheafOfModules.pushforwardSections i.toRingCatSheafHom (M := F))
      (σ.s k)
  have hσs (k : σ.I) :
      SheafOfModules.pushforwardSections i.toRingCatSheafHom (σs k) = σ.s k := by
    simpa [σs] using Function.rightInverse_invFun hsections.2 (σ.s k)
  let p : SheafOfModules.free (R := X.ringCatSheaf) σ.I ⟶ F :=
    F.freeHomEquiv.symm σs
  let qsections : σ.I →
      (chapter06Pushforward i (SheafOfModules.free (R := X.ringCatSheaf) σ.I)).sections :=
    fun k ↦ SheafOfModules.pushforwardSections i.toRingCatSheafHom
      (SheafOfModules.freeSection k)
  let q : SheafOfModules.free (R := Y.ringCatSheaf) σ.I ⟶
      chapter06Pushforward i (SheafOfModules.free (R := X.ringCatSheaf) σ.I) :=
    (SheafOfModules.freeHomEquiv _).symm qsections
  have hpushforwardSections_map {M N : X.Modules} (u : M ⟶ N) (s : M.sections) :
      SheafOfModules.sectionsMap ((Scheme.Modules.pushforward i).map u)
          (SheafOfModules.pushforwardSections i.toRingCatSheafHom s) =
        SheafOfModules.pushforwardSections i.toRingCatSheafHom
          (SheafOfModules.sectionsMap u s) := by
    ext U
    rfl
  have hfactor :
      (chapter06Pushforward i F).freeHomEquiv.symm σ.s =
        q ≫ (Scheme.Modules.pushforward i).map p := by
    dsimp [q]
    rw [SheafOfModules.freeHomEquiv_symm_comp]
    apply (chapter06Pushforward i F).freeHomEquiv.symm.injective
    funext k
    symm
    change SheafOfModules.sectionsMap ((Scheme.Modules.pushforward i).map p)
        (qsections k) = σ.s k
    dsimp [qsections]
    rw [hpushforwardSections_map]
    dsimp [p]
    rw [SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection]
    exact hσs k
  have hp : Epi p := by
    letI : Epi ((chapter06Pushforward i F).freeHomEquiv.symm σ.s) := σ.epi
    letI : Epi (q ≫ (Scheme.Modules.pushforward i).map p) := by
      rw [← hfactor]
      infer_instance
    letI : Epi ((Scheme.Modules.pushforward i).map p) :=
      epi_of_epi q ((Scheme.Modules.pushforward i).map p)
    exact (Scheme.Modules.pushforward i).epi_of_epi_map inferInstance
  exact ⟨{ I := σ.I, s := σs, epi := hp }, hσ⟩

/-- The projective-space theorem transfers to a closed subscheme via pushforward. -/
theorem chapter06_serre_vanishing_closed_subscheme
    {A : Type u} [CommRing A] {r : ℕ}
    (hA : IsNoetherianRing A)
    (C : Chapter06CohomologyTheory A)
    (P : Chapter06ProjectiveSpaceData A r)
    (hC : Chapter06ProjectiveSpaceCechRealization C P)
    {X : Chapter06Scheme} (i : X ⟶ P.X) [IsClosedImmersion i]
    (G : X.Modules) (hG : Chapter06Coherent G)
    (T_X : Chapter06TwistSystem X)
    (hT : Chapter06TwistCompatibility i T_X P.twisting)
    (hClosure : Chapter06CoherentClosureInterface.{u})
    (hSerre : Chapter06ProjectiveSpaceSerreInterface hA C P hC) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ j : ℕ, 0 < j →
        chapter06CohomologyIsZero C (T_X.twist G n) j ∧
          Nonempty (C.H (chapter06Pushforward i (T_X.twist G n)) j ≅
            C.H (T_X.twist G n) j)) ∧
      chapter06FinitelyGloballyGenerated (T_X.twist G n) := by
  obtain ⟨n₀, hn₀⟩ :=
    chapter06_serre_vanishing_projective_space hA C P hC hSerre
      (chapter06Pushforward i G)
      (chapter06_closed_immersion_pushforward_coherent i G hG hClosure)
  refine ⟨n₀, ?_⟩
  intro n hn
  rcases hn₀ n hn with ⟨hvanish, hgenerated⟩
  refine ⟨?_, ?_⟩
  · intro j hj
    refine ⟨?_, chapter06_closed_immersion_cohomology_iso C hC.canonical i
      (T_X.twist G n) j⟩
    obtain ⟨e⟩ := hC.canonical.mapIso (hT.iso (T_X.twist G n) n) j
    intro x
    have hx := hvanish j hj (e.hom x)
    have hx' : e.hom x = 0 := by simpa using hx
    calc
      x = e.inv (e.hom x) := by simp
      _ = e.inv 0 := by rw [hx']
      _ = 0 := by simp
  · obtain ⟨σ, hσ⟩ := hgenerated
    let e := hT.iso (T_X.twist G n) n
    let σ' := (SheafOfModules.GeneratingSections.equivOfIso e).symm σ
    have hσ' : chapter06FinitelyGloballyGenerated
        (chapter06Pushforward i (T_X.twist G n)) := by
      exact ⟨σ', hσ⟩
    exact chapter06_finitely_globally_generated_of_closed_immersion_pushforward
      i (T_X.twist G n) hσ'

/-- Serre vanishing for a projective noetherian scheme with a relatively ample twist. -/
theorem chapter06_serre_vanishing_projective
    {X S : Chapter06Scheme} (f : X ⟶ S)
    (_hS : IsLocallyNoetherian S) [IsAffine S]
    (hproj : chapter06IsProjective f)
    (T : Chapter06TwistSystem X) [Chapter06RelativelyAmple f T]
    (C : Chapter06CohomologyTheory ℤ)
    (_hC : Chapter06CanonicalCohomologyRealization C)
    (hSerre : Chapter06RelativeSerreInterface f T C _hC)
    (F : X.Modules) (hF : Chapter06Coherent F) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ i : ℕ, 0 < i → chapter06CohomologyIsZero C (T.twist F n) i) ∧
      chapter06FinitelyGloballyGenerated (T.twist F n) := by
  simpa [chapter06SerreHighDegreeConclusion] using
    hSerre.for_projective_ample _hS hproj inferInstance F hF

/-- The finitely many residue classes modulo a very-ample power are the reduction used for an
ample twist. -/
theorem chapter06_serre_vanishing_of_ample_twist
    {X S : Chapter06Scheme} (f : X ⟶ S)
    (_hS : IsLocallyNoetherian S) [IsAffine S]
    (hproj : chapter06IsProjective f)
    (T : Chapter06TwistSystem X) [Chapter06RelativelyAmple f T]
    (C : Chapter06CohomologyTheory ℤ)
    (_hC : Chapter06CanonicalCohomologyRealization C)
    (hSerre : Chapter06RelativeSerreInterface f T C _hC)
    (F : X.Modules) (hF : Chapter06Coherent F) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ i : ℕ, 0 < i → chapter06CohomologyIsZero C (T.twist F n) i) ∧
      chapter06FinitelyGloballyGenerated (T.twist F n) := by
  simpa [chapter06SerreHighDegreeConclusion] using
    hSerre.for_projective_ample _hS hproj inferInstance F hF

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06
