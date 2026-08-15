import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Section03AffineOpenAmpleness

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

/-! ## 4.5. Tensor powers and operations -/

/-- Isomorphism of line bundles through their underlying module sheaves. -/
def chapter04LineBundleIsomorphic
    {X : Scheme.{u}} (L M : Chapter04LineBundle X) : Prop :=
  Nonempty (L.sheaf ≅ M.sheaf)

/-- Pullback commutes with the canonical tensor-power construction. -/
theorem chapter04_lineBundle_pullback_tensorPower
    {X Y : Scheme.{u}} (L : Chapter04LineBundle X) (g : Y ⟶ X) (n : ℕ) :
    chapter04LineBundleIsomorphic
      (chapter04PullbackLineBundle g (chapter04LineBundleTensorPower L n))
      (chapter04LineBundleTensorPower (chapter04PullbackLineBundle g L) n) := by
  sorry

/-- The pullback-composition comparison remains available on tensor powers. -/
theorem chapter04_lineBundle_pullback_tensorPower_comp
    {X Y Z : Scheme.{u}} (L : Chapter04LineBundle X)
    (g : Y ⟶ X) (h : Z ⟶ Y) (n : ℕ) :
    chapter04LineBundleIsomorphic
      (chapter04PullbackLineBundle (h ≫ g)
        (chapter04LineBundleTensorPower L n))
      (chapter04PullbackLineBundle h
        (chapter04PullbackLineBundle g (chapter04LineBundleTensorPower L n))) := by
  exact ⟨chapter04PullbackCompositionIso h g
    (chapter04LineBundleTensorPower L n).sheaf⟩

/-- The direct and iterated pullbacks of a tensor power are coherently
isomorphic after applying the tensor-power comparison at each stage. -/
theorem chapter04_lineBundle_pullback_tensorPower_coherent
    {X Y Z : Scheme.{u}} (L : Chapter04LineBundle X)
    (g : Y ⟶ X) (h : Z ⟶ Y) (n : ℕ) :
    chapter04LineBundleIsomorphic
      (chapter04PullbackLineBundle (h ≫ g)
        (chapter04LineBundleTensorPower L n))
      (chapter04LineBundleTensorPower
        (chapter04PullbackLineBundle h
          (chapter04PullbackLineBundle g L)) n) := by
  sorry

theorem chapter04_lineBundleIsomorphic_refl
    {X : Scheme.{u}} (L : Chapter04LineBundle X) :
    chapter04LineBundleIsomorphic L L := by
  exact ⟨Iso.refl L.sheaf⟩

theorem chapter04_lineBundleIsomorphic_symm
    {X : Scheme.{u}} {L M : Chapter04LineBundle X}
    (h : chapter04LineBundleIsomorphic L M) :
    chapter04LineBundleIsomorphic M L := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

theorem chapter04_lineBundleIsomorphic_trans
    {X : Scheme.{u}} {L M N : Chapter04LineBundle X}
    (hLM : chapter04LineBundleIsomorphic L M)
    (hMN : chapter04LineBundleIsomorphic M N) :
    chapter04LineBundleIsomorphic L N := by
  obtain ⟨e⟩ := hLM
  obtain ⟨g⟩ := hMN
  exact ⟨e ≪≫ g⟩

theorem chapter04_ample_iff_of_lineBundleIsomorphic
    {X S : Scheme.{u}} (f : X ⟶ S)
    {L M : Chapter04LineBundle X}
    (hLM : chapter04LineBundleIsomorphic L M) :
    chapter04Ample f L ↔ chapter04Ample f M := by
  have transport : ∀ (A B : Chapter04LineBundle X) (e : A.sheaf ≅ B.sheaf),
      chapter04Ample f A → chapter04Ample f B := by
    intro A B e hA
    let tensorIso {M₁ M₂ N₁ N₂ : X.Modules}
        (e₁ : M₁ ≅ M₂) (e₂ : N₁ ≅ N₂) :
        chapter04Tensor M₁ N₁ ≅ chapter04Tensor M₂ N₂ := by
      have e₁' : M₁.val ≅ M₂.val := by
        refine
          { hom := e₁.hom.val
            inv := e₁.inv.val
            hom_inv_id := ?_
            inv_hom_id := ?_ }
        · exact congrArg (fun q => q.val) e₁.hom_inv_id
        · exact congrArg (fun q => q.val) e₁.inv_hom_id
      have e₂' : N₁.val ≅ N₂.val := by
        refine
          { hom := e₂.hom.val
            inv := e₂.inv.val
            hom_inv_id := ?_
            inv_hom_id := ?_ }
        · exact congrArg (fun q => q.val) e₂.hom_inv_id
        · exact congrArg (fun q => q.val) e₂.inv_hom_id
      exact
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
          (CategoryTheory.MonoidalCategory.tensorIso
            (C := PresheafOfModules (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)) e₁' e₂')
    let powerIso : ∀ n : ℕ,
        chapter04TensorPower A.sheaf n ≅ chapter04TensorPower B.sheaf n := by
      intro n
      induction n with
      | zero =>
          exact Iso.refl _
      | succ n ih =>
          exact tensorIso ih e
    obtain ⟨w⟩ := hA
    refine ⟨{ I := w.I
              base_open := w.base_open
              base_open_affine := w.base_open_affine
              base_open_cover := w.base_open_cover
              J := w.J
              chart := fun i j =>
                let c := w.chart i j
                { n := c.n
                  positive := c.positive
                  power_iso := c.power_iso ≪≫ powerIso c.n
                  power := c.power
                  sectionData := c.sectionData
                  locus := c.locus
                  locus_spec := c.locus_spec
                  affine := c.affine }
              chart_cover := w.chart_cover }⟩
  obtain ⟨e⟩ := hLM
  exact ⟨transport L M e, transport M L e.symm⟩

/-- Positive tensor powers preserve relative ampleness. -/
theorem chapter04_ample_tensorPower
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X)
    (hL : chapter04Ample f L) (d : ℕ) (hd : 0 < d) :
    chapter04Ample f (chapter04LineBundleTensorPower L d) := by
  sorry

/-- Relative ampleness descends from a positive tensor power. -/
theorem chapter04_ample_of_ample_tensorPower
    {X S : Scheme.{u}} (f : X ⟶ S) (L : Chapter04LineBundle X)
    (d : ℕ) (hd : 0 < d)
    (hLd : chapter04Ample f (chapter04LineBundleTensorPower L d)) :
    chapter04Ample f L := by
  sorry

/- The source's bounded-twist assertion assumes quasi-compactness of both the
base and the morphism; those hypotheses are recorded explicitly here. -/
/-- Over a quasi-compact base, a fixed invertible twist does not affect ampleness in sufficiently high powers. -/
theorem chapter04_ample_eventually_tensor_twist
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiCompact f] [IsSeparated f]
    (L M : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter04Ample f
        (chapter04LineBundleTensor (chapter04LineBundleTensorPower L n) M) := by
  sorry

/-- Over a quasi-compact base, every sufficiently high power of an ample bundle is relatively very ample. -/
theorem chapter04_ample_eventually_veryAmple_power
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiCompact f]
    [LocallyOfFiniteType f] [QuasiSeparated f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      chapter04VeryAmple f (chapter04LineBundleTensorPower L n) := by
  sorry

/-- Over a quasi-compact base, an ample line bundle on a quasi-compact finite-type family has a very ample power. -/
theorem chapter04_ample_has_veryAmple_power
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiCompact f]
    [LocallyOfFiniteType f] [QuasiSeparated f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ d : ℕ, 0 < d ∧ chapter04VeryAmple f (chapter04LineBundleTensorPower L d) := by
  obtain ⟨n₀, hn₀⟩ := chapter04_ample_eventually_veryAmple_power f L hL
  let d := max n₀ 1
  refine ⟨d, ?_, hn₀ d ?_⟩
  · exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right n₀ 1)
  · exact Nat.le_max_left n₀ 1

/-- Over a quasi-compact base, if the family is proper, a sufficiently high ample power gives a closed projective embedding. -/
theorem chapter04_proper_ample_has_closed_projective_power
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [IsProper f] [QuasiCompact f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ d : ℕ, 0 < d ∧
      ∃ w : Chapter04VeryAmpleWitness f (chapter04LineBundleTensorPower L d),
        IsClosedImmersion w.map := by
  obtain ⟨d, hd, hV⟩ := chapter04_ample_has_veryAmple_power f L hL
  obtain ⟨w⟩ := hV
  refine ⟨d, hd, w, ?_⟩
  let : IsImmersion w.map := w.immersion
  have : IsProper (w.map ≫ w.projectiveBundle.projection) := by
    rw [w.over]
    infer_instance
  have : IsProper w.map := IsProper.of_comp w.map w.projectiveBundle.projection
  rw [IsClosedImmersion.iff_isProper_and_mono]
  exact ⟨inferInstance, inferInstance⟩

/-!
For a quasi-compact base, a proper family upgrades eventual very-ampleness to closed immersions,
so the exponent can be chosen uniformly rather than separately for one power.
-/
theorem chapter04_proper_ample_eventually_closed_projective_power
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [IsProper f] [QuasiCompact f]
    [QuasiSeparated f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ w : Chapter04VeryAmpleWitness f (chapter04LineBundleTensorPower L n),
        IsClosedImmersion w.map := by
  obtain ⟨n₀, hn₀⟩ := chapter04_ample_eventually_veryAmple_power f L hL
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨w⟩ := hn₀ n hn
  refine ⟨w, ?_⟩
  let : IsImmersion w.map := w.immersion
  have : IsProper (w.map ≫ w.projectiveBundle.projection) := by
    rw [w.over]
    infer_instance
  have : IsProper w.map := IsProper.of_comp w.map w.projectiveBundle.projection
  rw [IsClosedImmersion.iff_isProper_and_mono]
  exact ⟨inferInstance, inferInstance⟩

theorem chapter04_proper_ample_is_projective
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [IsProper f] [QuasiCompact f]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    chapter04Projective f := by
  obtain ⟨d, hd, w, hw⟩ :=
    chapter04_proper_ample_has_closed_projective_power f L hL
  exact ⟨{ projectiveBundle := w.projectiveBundle
           map := w.map
           closedImmersion := hw
           over := w.over }⟩

/-- Tensor products of ample line bundles are ample. -/
theorem chapter04_ample_tensor
    {X S : Scheme.{u}} (f : X ⟶ S)
    (L M : Chapter04LineBundle X)
    (hL : chapter04Ample f L) (hM : chapter04Ample f M) :
    chapter04Ample f (chapter04LineBundleTensor L M) := by
  sorry

/-- Pullback along a finite morphism preserves relative ampleness. -/
theorem chapter04_ample_pullback_of_finite
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X) [IsFinite g]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L) :
    chapter04Ample (g ≫ f) (chapter04PullbackLineBundle g L) := by
  sorry

/-- A constant pullback can become the trivial bundle on a proper non-affine fibre. -/
theorem chapter04_constant_pullback_can_destroy_ample
    {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of K)) (g : Y ⟶ X)
    [IsProper (g ≫ f)]
    (L : Chapter04LineBundle X) (hL : chapter04Ample f L)
    (hconstant : chapter04UnderlyingConstant g)
    (htrivial : chapter04LineBundleIsomorphic
      (chapter04PullbackLineBundle g L) (chapter04TrivialLineBundle Y))
    (hY : ¬ IsAffine Y) :
    ¬ chapter04Ample (g ≫ f) (chapter04PullbackLineBundle g L) := by
  intro hA
  have _hL := hL
  have _hconstant := hconstant
  have htriv : chapter04Ample (g ≫ f) (chapter04TrivialLineBundle Y) :=
    (chapter04_ample_iff_of_lineBundleIsomorphic (g ≫ f) htrivial).mp hA
  exact (chapter04_trivial_line_bundle_not_ample_of_proper_nonAffine Y (g ≫ f) hY) htriv

end
end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
