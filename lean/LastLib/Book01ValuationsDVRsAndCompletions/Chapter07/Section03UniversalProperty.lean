import LastLib.Book01ValuationsDVRsAndCompletions.Chapter07.Section02ExtendingInverses

namespace LastLib.Book01ValuationsDVRsAndCompletions.Chapter07

open Filter Set Function MonoidWithZeroHom
open scoped Topology

noncomputable section

/-!
  Chapter 7 develops completion from the metric point of view and compares it with
  valuation rings and ideal-adic completion. Proofs are deferred to a later pass.
-/

/-! # Book 1, Chapter 7, Section 7.3: Universal Property
-/

/-! ### 7.3. The universal property -/

-- The canonical extension map from a uniform space to a complete target.
noncomputable def chapter07UniversalCompletionExtension
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F]
    (f : K → F) (hf : UniformContinuous f) : UniformSpace.Completion K → F :=
  (fun _ : UniformContinuous f => UniformSpace.Completion.extension f) hf

-- The extension agrees with the original map on the dense copy of K.
theorem chapter07_universal_extension_coe
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F]
    (f : K → F) (hf : UniformContinuous f) (x : K) :
    chapter07UniversalCompletionExtension f hf (x : UniformSpace.Completion K) = f x := by
  simpa [chapter07UniversalCompletionExtension] using
    (UniformSpace.Completion.extension_coe hf x)

-- Theorem 7.1: every uniformly continuous map extends uniquely to the completion.
theorem chapter07_completion_universal_property
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F]
    (f : K → F) (hf : UniformContinuous f) :
    ∃ g : UniformSpace.Completion K → F,
      UniformContinuous g ∧
        (∀ x : K, g (x : UniformSpace.Completion K) = f x) ∧
          ∀ g' : UniformSpace.Completion K → F, Continuous g' →
            (∀ x : K, g' (x : UniformSpace.Completion K) = f x) → g' = g := by
  let g := chapter07UniversalCompletionExtension f hf
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa [g, chapter07UniversalCompletionExtension] using
      (UniformSpace.Completion.uniformContinuous_extension (f := f))
  · intro x
    exact chapter07_universal_extension_coe f hf x
  · intro g' hg' h'
    symm
    apply UniformSpace.Completion.ext
    · exact UniformSpace.Completion.continuous_extension
    · exact hg'
    · intro x
      exact (chapter07_universal_extension_coe f hf x).trans (h' x).symm

-- The value of the extension can be computed from any approximating sequence.
theorem chapter07_universal_extension_as_limit
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F] [Nonempty F]
    (f : K → F) (hf : UniformContinuous f)
    (x : UniformSpace.Completion K) (u : ℕ → K)
    (hu : Tendsto (fun n => (u n : UniformSpace.Completion K)) (atTop : Filter ℕ) (𝓝 x)) :
    chapter07UniversalCompletionExtension f hf x =
      limUnder (atTop : Filter ℕ) (fun n => f (u n)) := by
  have hlim : Tendsto (fun n => f (u n)) atTop
      (𝓝 (chapter07UniversalCompletionExtension f hf x)) := by
    have h := (UniformSpace.Completion.continuous_extension (f := f)).tendsto x |>.comp hu
    change Tendsto (fun n => f (u n)) atTop
      (𝓝 (UniformSpace.Completion.extension f x))
    exact h.congr' (Filter.Eventually.of_forall (fun n =>
      UniformSpace.Completion.extension_coe hf (u n)))
  exact hlim.limUnder_eq.symm

-- The dense-approximation construction is independent of the chosen approximating sequence.
theorem chapter07_universal_extension_approximation_independent
    {K F : Type*} [UniformSpace K] [UniformSpace F] [CompleteSpace F] [T0Space F] [Nonempty F]
    (f : K → F) (hf : UniformContinuous f) (x : UniformSpace.Completion K)
    (u v : ℕ → K)
    (hu : Tendsto (fun n => (u n : UniformSpace.Completion K)) (atTop : Filter ℕ) (𝓝 x))
    (hv : Tendsto (fun n => (v n : UniformSpace.Completion K)) (atTop : Filter ℕ) (𝓝 x)) :
    limUnder (atTop : Filter ℕ) (fun n => f (u n)) =
      limUnder (atTop : Filter ℕ) (fun n => f (v n)) := by
  have hU : Tendsto (fun n => f (u n)) atTop
      (𝓝 (chapter07UniversalCompletionExtension f hf x)) := by
    have h := (UniformSpace.Completion.continuous_extension (f := f)).tendsto x |>.comp hu
    change Tendsto (fun n => f (u n)) atTop
      (𝓝 (UniformSpace.Completion.extension f x))
    exact h.congr' (Filter.Eventually.of_forall (fun n =>
      UniformSpace.Completion.extension_coe hf (u n)))
  have hV : Tendsto (fun n => f (v n)) atTop
      (𝓝 (chapter07UniversalCompletionExtension f hf x)) := by
    have h := (UniformSpace.Completion.continuous_extension (f := f)).tendsto x |>.comp hv
    change Tendsto (fun n => f (v n)) atTop
      (𝓝 (UniformSpace.Completion.extension f x))
    exact h.congr' (Filter.Eventually.of_forall (fun n =>
      UniformSpace.Completion.extension_coe hf (v n)))
  exact hU.limUnder_eq.trans hV.limUnder_eq.symm

-- The completion extension of a continuous ring homomorphism.
noncomputable def chapter07UniversalCompletionRingHom
    {K F : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K] [Ring F] [UniformSpace F] [IsUniformAddGroup F]
    [IsTopologicalRing F] [CompleteSpace F] [T0Space F]
    (f : K →+* F) (hf : Continuous f) :
    UniformSpace.Completion K →+* F :=
  UniformSpace.Completion.extensionHom f hf

-- The ring-hom extension agrees with the original ring homomorphism.
theorem chapter07_universal_extension_ringHom_coe
    {K F : Type*} [Ring K] [UniformSpace K] [IsUniformAddGroup K]
    [IsTopologicalRing K] [Ring F] [UniformSpace F] [IsUniformAddGroup F]
    [IsTopologicalRing F] [CompleteSpace F] [T0Space F]
    (f : K →+* F) (hf : Continuous f) (x : K) :
    chapter07UniversalCompletionRingHom f hf (x : UniformSpace.Completion K) = f x := by
  exact UniformSpace.Completion.extensionHom_coe f hf x

-- Compatibility of a field hom with a chosen valuation.
def chapter07ValuationCompatibleRingHom
    {K F Γ₀ : Type*} [Ring K] [Ring F] [LinearOrderedCommMonoidWithZero Γ₀]
    (vK : Valuation K Γ₀) (vF : Valuation F Γ₀) (f : K →+* F) : Prop :=
  ∀ x : K, vF (f x) = vK x

-- Theorem 7.1, valued form: compatible field homomorphisms extend compatibly.
theorem chapter07_completion_extension_preserves_valuation
    {K F Γ₀ : Type*} [Field K] [Field F]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [Valued F Γ₀]
    [CompleteSpace F] [T0Space F]
    (f : K →+* F) (hf : Continuous f)
    (hcompat : chapter07ValuationCompatibleRingHom
      (Valued.v (R := K)) (Valued.v (R := F)) f) :
    ∀ x : UniformSpace.Completion K,
      Valued.v (R := F) (chapter07UniversalCompletionRingHom f hf x) =
        chapter07CompletionValuation K Γ₀ x := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp [chapter07UniversalCompletionRingHom, chapter07CompletionValuation]
  · let g := chapter07UniversalCompletionRingHom f hf
    have hgx : g x ≠ 0 := by
      intro hgx
      apply hx
      exact (RingHom.injective g) (by simpa using hgx)
    have hxc : chapter07CompletionValuation K Γ₀ x ≠ 0 :=
      (Valuation.ne_zero_iff (chapter07CompletionValuation K Γ₀)).2 hx
    have hvalC : {y : UniformSpace.Completion K |
        chapter07CompletionValuation K Γ₀ y = chapter07CompletionValuation K Γ₀ x} ∈ 𝓝 x :=
      Valued.locally_const hxc
    have hvalF : {y : F | Valued.v (R := F) y = Valued.v (R := F) (g x)} ∈ 𝓝 (g x) :=
      Valued.locally_const ((Valuation.ne_zero_iff (Valued.v (R := F))).2 hgx)
    have hgval : g ⁻¹' {y : F |
        Valued.v (R := F) y = Valued.v (R := F) (g x)} ∈ 𝓝 x :=
      (UniformSpace.Completion.continuous_extension (f := f)).continuousAt.preimage_mem_nhds hvalF
    obtain ⟨r, hrC, hrF⟩ := UniformSpace.Completion.denseRange_coe.mem_nhds
      (inter_mem hvalC hgval)
    calc
      Valued.v (R := F) (g x) = Valued.v (R := F) (g (r : UniformSpace.Completion K)) := hrF.symm
      _ = Valued.v (R := F) (f r) := by
        rw [chapter07_universal_extension_ringHom_coe]
      _ = Valued.v (R := K) r := hcompat r
      _ = chapter07CompletionValuation K Γ₀ (r : UniformSpace.Completion K) :=
        (chapter07_completion_valuation_apply_coe r).symm
      _ = chapter07CompletionValuation K Γ₀ x := hrC

end
end LastLib.Book01ValuationsDVRsAndCompletions.Chapter07
