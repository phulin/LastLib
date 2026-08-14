import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Dependencies
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
## 10.1 Descent of maps

The declarations in this file expose the equalizer, saturated-open, section, and automorphism
forms of morphism descent.  The proofs are intentionally left for the later compilation pass.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v

private theorem chapter10_scheme_hom_descends_of_kernelPair
    {A B C K : Scheme.{u}} (q : A ⟶ B) (r s : K ⟶ A)
    (hker : IsPullback r s q q) [EffectiveEpi q] (u : A ⟶ C)
    (hu : r ≫ u = s ≫ u) : ∃! v : B ⟶ C, q ≫ v = u := by
  have hrel : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ A),
      g₁ ≫ q = g₂ ≫ q → g₁ ≫ u = g₂ ≫ u := by
    intro Z g₁ g₂ h
    let l := hker.lift g₁ g₂ h
    calc
      g₁ ≫ u = (l ≫ r) ≫ u := by rw [hker.lift_fst]
      _ = (l ≫ s) ≫ u := by
        simpa only [Category.assoc] using congrArg (fun k => l ≫ k) hu
      _ = g₂ ≫ u := by rw [hker.lift_snd]
  let v := EffectiveEpi.desc q u hrel
  refine ⟨v, EffectiveEpi.fac q u hrel, ?_⟩
  intro w hw
  apply (cancel_epi q).1
  rw [hw, EffectiveEpi.fac q u hrel]

private theorem chapter10_plain_pullbackComp_left_fst_fst
    {A X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : A ⟶ Z) :
    ((Over.pullbackComp f g).hom.app (Over.mk h)).left ≫
        pullback.fst (pullback.snd h g) f ≫ pullback.fst h g =
      pullback.fst h (f ≫ g) := by
  have hc := congrArg (fun k => k.left)
    (conjugateEquiv_counit (Over.mapPullbackAdj (f ≫ g))
      ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
      ((Over.mapComp f g).inv) (Over.mk h))
  simpa [Over.pullbackComp] using hc

private theorem chapter10_plain_pullbackComp_inv_fst_fst
    {A X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : A ⟶ Z) :
    ((Over.pullbackComp f g).inv.app (Over.mk h)).left ≫ pullback.fst h (f ≫ g) =
      pullback.fst (pullback.snd h g) f ≫ pullback.fst h g := by
  calc
    ((Over.pullbackComp f g).inv.app (Over.mk h)).left ≫ pullback.fst h (f ≫ g) =
        ((Over.pullbackComp f g).inv.app (Over.mk h)).left ≫
          (((Over.pullbackComp f g).hom.app (Over.mk h)).left ≫
            pullback.fst (pullback.snd h g) f ≫ pullback.fst h g) := by
              rw [chapter10_plain_pullbackComp_left_fst_fst f g h]
    _ = pullback.fst (pullback.snd h g) f ≫ pullback.fst h g := by
      have hi := congrArg (fun k =>
          k.left ≫ pullback.fst (pullback.snd h g) f ≫ pullback.fst h g)
        ((Over.pullbackComp f g).inv_hom_id_app (Over.mk h))
      change (((Over.pullbackComp f g).inv.app (Over.mk h)).left ≫
          ((Over.pullbackComp f g).hom.app (Over.mk h)).left ≫
            pullback.fst (pullback.snd h g) f ≫ pullback.fst h g) =
        (pullback.fst (pullback.snd h g) f ≫ pullback.fst h g) at hi
      exact hi

private theorem chapter10_plain_pullbackComp_hom_snd
    {A X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : A ⟶ Z) :
    ((Over.pullbackComp f g).hom.app (Over.mk h)).left ≫
        pullback.snd (pullback.snd h g) f = pullback.snd h (f ≫ g) := by
  exact Over.w ((Over.pullbackComp f g).hom.app (Over.mk h))

private theorem chapter10_plain_pullbackComp_inv_snd
    {A X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : A ⟶ Z) :
    ((Over.pullbackComp f g).inv.app (Over.mk h)).left ≫ pullback.snd h (f ≫ g) =
      pullback.snd (pullback.snd h g) f := by
  exact Over.w ((Over.pullbackComp f g).inv.app (Over.mk h))

private theorem chapter10_eqToIso_pullback_fst
    {A B S : Scheme.{u}} {f g : B ⟶ S} (hfg : f = g) (k : A ⟶ S) :
    (eqToIso (congrArg (fun q : B ⟶ S =>
        (Over.pullback q).obj (Over.mk k)) hfg)).hom.left ≫ pullback.fst k g =
      pullback.fst k f := by
  subst g
  simp

private theorem chapter10_eqToIso_pullback_snd
    {A B S : Scheme.{u}} {f g : B ⟶ S} (hfg : f = g) (k : A ⟶ S) :
    (eqToIso (congrArg (fun q : B ⟶ S =>
        (Over.pullback q).obj (Over.mk k)) hfg)).hom.left ≫ pullback.snd k g =
      pullback.snd k f := by
  subst g
  simp

private theorem chapter10_pullbackComp_comparison_fst
    {A D T S : Scheme.{u}} (f₁ f₂ : D ⟶ T) (p : T ⟶ S) (hfg : f₁ ≫ p = f₂ ≫ p)
    (h : A ⟶ S) :
    ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
        (eqToIso (congrArg (fun q : D ⟶ S =>
          (Over.pullback q).obj (Over.mk h)) hfg)).hom.left ≫
        ((Over.pullbackComp f₂ p).hom.app (Over.mk h)).left ≫
          pullback.fst (pullback.snd h p) f₂ ≫ pullback.fst h p =
      pullback.fst (pullback.snd h p) f₁ ≫ pullback.fst h p := by
  calc
    _ = ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
          (eqToIso (congrArg (fun q : D ⟶ S =>
            (Over.pullback q).obj (Over.mk h)) hfg)).hom.left ≫
          pullback.fst h (f₂ ≫ p) := by
            simpa only [Category.assoc] using congrArg
              (fun k => ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
                (eqToIso (congrArg (fun q : D ⟶ S =>
                  (Over.pullback q).obj (Over.mk h)) hfg)).hom.left ≫ k)
              (chapter10_plain_pullbackComp_left_fst_fst f₂ p h)
    _ = ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
          pullback.fst h (f₁ ≫ p) := by
            simpa only [Category.assoc] using congrArg
              (fun k => ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫ k)
              (chapter10_eqToIso_pullback_fst hfg h)
    _ = pullback.fst (pullback.snd h p) f₁ ≫ pullback.fst h p :=
      chapter10_plain_pullbackComp_inv_fst_fst f₁ p h

private theorem chapter10_pullbackComp_comparison_snd
    {A D T S : Scheme.{u}} (f₁ f₂ : D ⟶ T) (p : T ⟶ S) (hfg : f₁ ≫ p = f₂ ≫ p)
    (h : A ⟶ S) :
    ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
        (eqToIso (congrArg (fun q : D ⟶ S =>
          (Over.pullback q).obj (Over.mk h)) hfg)).hom.left ≫
        ((Over.pullbackComp f₂ p).hom.app (Over.mk h)).left ≫
          pullback.snd (pullback.snd h p) f₂ =
      pullback.snd (pullback.snd h p) f₁ := by
  calc
    _ = ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
          (eqToIso (congrArg (fun q : D ⟶ S =>
            (Over.pullback q).obj (Over.mk h)) hfg)).hom.left ≫
          pullback.snd h (f₂ ≫ p) := by
            simpa only [Category.assoc] using congrArg
              (fun k => ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
                (eqToIso (congrArg (fun q : D ⟶ S =>
                  (Over.pullback q).obj (Over.mk h)) hfg)).hom.left ≫ k)
              (chapter10_plain_pullbackComp_hom_snd f₂ p h)
    _ = ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫
          pullback.snd h (f₁ ≫ p) := by
            simpa only [Category.assoc] using congrArg
              (fun k => ((Over.pullbackComp f₁ p).inv.app (Over.mk h)).left ≫ k)
              (chapter10_eqToIso_pullback_snd hfg h)
    _ = pullback.snd (pullback.snd h p) f₁ :=
      chapter10_plain_pullbackComp_inv_snd f₁ p h

private theorem chapter10_descent_compatible_kernelPair
    {S T : Scheme.{u}} (p : T ⟶ S) (X Y : Chapter10SchemeOver S)
    (u : chapter10BaseChangeOver p X ⟶ chapter10BaseChangeOver p Y)
    (hu : chapter10DescentCompatible p u) :
    pullback.fst (pullback.fst X.toBase p) (pullback.fst X.toBase p) ≫ u.left ≫
        pullback.fst Y.toBase p =
      pullback.snd (pullback.fst X.toBase p) (pullback.fst X.toBase p) ≫ u.left ≫
        pullback.fst Y.toBase p := by sorry

/-- The Hom sequence over an fpqc cover is an equalizer. -/
noncomputable def chapter10_hom_equalizer {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S) :
    IsLimit (chapter10HomEqualizerFork p X Y) := by
  sorry

/-- A map on the cover descends exactly when its two pullbacks to the double overlap agree. -/
theorem chapter10_morphism_descends_iff {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    (u : chapter10BaseChangeOver p X ⟶ chapter10BaseChangeOver p Y) :
    (∃ f : chapter10OverHom X Y, chapter10BaseChangeOverHom p f = u) ↔
      chapter10DescentCompatible p u := by
  let e := chapter10HomEqualizerFork p X Y
  let he := chapter10_hom_equalizer p hp X Y
  constructor
  · rintro ⟨f, rfl⟩
    have hc := ConcreteCategory.congr_hom e.condition f
    dsimp [e, chapter10HomEqualizerFork] at hc
    change chapter10OverlapFirstHom p (chapter10BaseChangeOverHom p f) =
      chapter10OverlapSecondHomTransported p (chapter10BaseChangeOverHom p f) at hc
    exact hc
  · intro hu
    let l := Fork.IsLimit.lift' (W := PUnit.{u + 1}) he
      (↾fun _ : PUnit.{u + 1} => u) (by
      ext i
      exact congrArg Over.Hom.left hu)
    refine ⟨l.1 PUnit.unit, ?_⟩
    have hl := ConcreteCategory.congr_hom l.2 PUnit.unit
    exact hl

/-- The descended map is unique. -/
theorem chapter10_morphism_descends_unique {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    {f g : chapter10OverHom X Y}
    (hfg : chapter10BaseChangeOverHom p f = chapter10BaseChangeOverHom p g) :
    f = g := by
  let : Surjective p := hp.surjective
  let : Flat p := hp.flat
  let : QuasiCompact p := hp.quasiCompact
  apply (Over.pullback p).map_injective
  exact hfg

/-- The affine case is algebra descent with arrows reversed. -/
theorem chapter10_affine_morphism_descent {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    (_hS : IsAffine S) (_hX : IsAffine X.scheme) (_hY : IsAffine Y.scheme)
    (u : chapter10BaseChangeOver p X ⟶ chapter10BaseChangeOver p Y)
    (hu : chapter10DescentCompatible p u) :
    ∃! f : chapter10OverHom X Y, chapter10BaseChangeOverHom p f = u := by
  obtain ⟨f, hf⟩ := (chapter10_morphism_descends_iff p hp X Y u).2 hu
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact chapter10_morphism_descends_unique p hp X Y (by rw [hf, hg])

/-- If only the target is affine, maps can be checked on affine opens of the source. -/
theorem chapter10_affine_target_morphism_descent {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    (_hY : IsAffine Y.scheme)
    (u : chapter10BaseChangeOver p X ⟶ chapter10BaseChangeOver p Y)
    (hu : chapter10DescentCompatible p u) :
    ∃! f : chapter10OverHom X Y, chapter10BaseChangeOverHom p f = u := by
  obtain ⟨f, hf⟩ := (chapter10_morphism_descends_iff p hp X Y u).2 hu
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact chapter10_morphism_descends_unique p hp X Y (by rw [hf, hg])

/-- A surjective fpqc morphism is a quotient map on underlying spaces. -/
def chapter10QuotientMap {Z' Z : Scheme.{u}} (q : Z' ⟶ Z) : Prop :=
  Topology.IsQuotientMap q.base

theorem chapter10_fpqc_isQuotientMap {Z' Z : Scheme.{u}} (q : Z' ⟶ Z)
    (hq : Chapter10FpqcCover q) : chapter10QuotientMap q := by
  exact @Flat.isQuotientMap_of_surjective _ _ q hq.flat hq.quasiCompact hq.surjective

/-- Openness is detected by an fpqc quotient map. -/
theorem chapter10_open_iff_preimage_open {Z' Z : Scheme.{u}} (q : Z' ⟶ Z)
    (hq : Chapter10FpqcCover q) (U : Set Z) :
    IsOpen U ↔ IsOpen (q.base ⁻¹' U) := by
  exact (@Flat.isQuotientMap_of_surjective _ _ q hq.flat hq.quasiCompact hq.surjective).isOpen_preimage.symm

/-- An open of the cover is saturated when its two inverse images on the overlap agree. -/
def chapter10SaturatedOpen {Z' Z : Scheme.{u}} (q : Z' ⟶ Z) (U' : Z'.Opens) : Prop :=
  (pullback.fst q q ⁻¹ᵁ U') = (pullback.snd q q ⁻¹ᵁ U')

/-- Every saturated open upstairs descends to a unique open downstairs. -/
theorem chapter10_saturated_open_descends {Z' Z : Scheme.{u}} (q : Z' ⟶ Z)
    (hq : Chapter10FpqcCover q) (U' : Z'.Opens) (hU' : chapter10SaturatedOpen q U') :
    ∃! U : Z.Opens, q ⁻¹ᵁ U = U' := by
  let V : Set Z := q.base '' (U' : Set Z')
  have hUeq : (pullback.fst q q ⁻¹ᵁ U') = (pullback.snd q q ⁻¹ᵁ U') := hU'
  have hUmem : ∀ z, z ∈ (pullback.fst q q ⁻¹ᵁ U') ↔
      z ∈ (pullback.snd q q ⁻¹ᵁ U') := by
    intro z
    rw [hUeq]
  have hpre : q.base ⁻¹' V = (U' : Set Z') := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨z, hz₁, hz₂⟩ :=
        AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
          (f := q) (g := q) x y hxy.symm
      have hz₂' : z ∈ (pullback.snd q q ⁻¹ᵁ U') := by
        simpa [hz₂] using hy
      have hz₁' : z ∈ (pullback.fst q q ⁻¹ᵁ U') := (hUmem z).2 hz₂'
      simpa [hz₁] using hz₁'
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hV : IsOpen V := by
    apply (chapter10_open_iff_preimage_open q hq V).2
    simpa [hpre] using U'.2
  let U : Z.Opens := ⟨V, hV⟩
  refine ⟨U, ?_, ?_⟩
  · ext x
    change x ∈ q.base ⁻¹' V ↔ x ∈ (U' : Set Z')
    exact Set.ext_iff.mp hpre x
  · intro U₁ hU₁
    ext x
    constructor
    · intro hx
      obtain ⟨y, rfl⟩ := hq.surjective.surj x
      have hy : y ∈ (U' : Set Z') := by
        rw [← hU₁]
        exact hx
      exact ⟨y, hy, rfl⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hy' : y ∈ (q ⁻¹ᵁ U₁ : Set Z') := by
        rw [hU₁]
        exact hy
      simpa [hxy] using hy'

/-- General morphism descent, after descending the affine-open pieces of the target and gluing. -/
theorem chapter10_morphism_descent {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (X Y : Chapter10SchemeOver S)
    (u : chapter10BaseChangeOver p X ⟶ chapter10BaseChangeOver p Y)
    (hu : chapter10DescentCompatible p u) :
    ∃! f : chapter10OverHom X Y, chapter10BaseChangeOverHom p f = u := by
  obtain ⟨f, hf⟩ := (chapter10_morphism_descends_iff p hp X Y u).2 hu
  refine ⟨f, hf, ?_⟩
  intro g hg
  exact chapter10_morphism_descends_unique p hp X Y (by rw [hf, hg])

/-- A section of a morphism, bundled with its section identity. -/
structure Chapter10Section {X S : Scheme.{u}} (f : X ⟶ S) where
  hom : S ⟶ X
  isSection : hom ≫ f = 𝟙 S

/-- Pull a section back along a map to the base. -/
def chapter10PullbackSection {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (s : Chapter10Section f) : Chapter10Section (chapter10BaseChangeMorphism f p) where
  hom := pullback.lift (p ≫ s.hom) (𝟙 T) (by
    rw [Category.assoc, s.isSection, Category.comp_id, Category.id_comp])
  isSection := by
    exact pullback.lift_snd _ _ _

/-- The section-overlap condition can be tested after projecting the two pulled-back sections to
the original source `X`. -/
def chapter10SectionDescentCompatible {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (sT : Chapter10Section (chapter10BaseChangeMorphism f p)) : Prop :=
  chapter10DoubleOverlapFirst p ≫ sT.hom ≫ chapter10BaseChangeToSource f p =
    chapter10DoubleOverlapSecond p ≫ sT.hom ≫ chapter10BaseChangeToSource f p

/-- Sections form a sheaf for an fpqc cover. -/
theorem chapter10_section_descent {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (sT : Chapter10Section (chapter10BaseChangeMorphism f p))
    (hs : chapter10SectionDescentCompatible f p sT) :
    ∃! s : Chapter10Section f, (chapter10PullbackSection f p s).hom = sT.hom := by
  have : Surjective p := hp.surjective
  have : Flat p := hp.flat
  have : QuasiCompact p := hp.quasiCompact
  let r := chapter10BaseChangeToSource f p
  have hker : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ T),
      g₁ ≫ p = g₂ ≫ p → g₁ ≫ sT.hom ≫ r = g₂ ≫ sT.hom ≫ r := by
    intro Z g₁ g₂ h
    let l : Z ⟶ chapter10DoubleOverlap p := pullback.lift g₁ g₂ h
    have h' := congrArg (fun k => l ≫ k) hs
    change l ≫ pullback.fst p p ≫ sT.hom ≫ r =
      l ≫ pullback.snd p p ≫ sT.hom ≫ r at h'
    dsimp [l] at h'
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at h'
    exact h'
  let s : S ⟶ X := EffectiveEpi.desc p (sT.hom ≫ r) hker
  have hfac : p ≫ s = sT.hom ≫ r := EffectiveEpi.fac p (sT.hom ≫ r) hker
  have hsection_ext : ∀ {a b : Chapter10Section f}, a.hom = b.hom → a = b := by
    intro a b hab
    cases a with
    | mk ah ha =>
      cases b with
      | mk bh hb =>
        dsimp at hab ⊢
        cases hab
        rfl
  have hsection : s ≫ f = 𝟙 S := by
    apply (cancel_epi p).1
    calc
      p ≫ s ≫ f = (p ≫ s) ≫ f := by simp only [Category.assoc]
      _ = (sT.hom ≫ r) ≫ f := by rw [hfac]
      _ = sT.hom ≫ (r ≫ f) := by simp only [Category.assoc]
      _ = sT.hom ≫ (chapter10BaseChangeMorphism f p ≫ p) := by
        rw [chapter10BaseChange_condition f p]
      _ = (sT.hom ≫ chapter10BaseChangeMorphism f p) ≫ p := by
        simp only [Category.assoc]
      _ = 𝟙 T ≫ p := by rw [sT.isSection]
      _ = p ≫ 𝟙 S := by simp
  let sDown : Chapter10Section f := ⟨s, hsection⟩
  refine ⟨sDown, ?_, ?_⟩
  · apply pullback.hom_ext
    · dsimp [chapter10PullbackSection, sDown]
      rw [pullback.lift_fst]
      exact hfac
    · dsimp [chapter10PullbackSection, sDown]
      rw [pullback.lift_snd]
      exact sT.isSection.symm
  · intro s₁ hs₁
    have h₁ := congrArg (fun k => k ≫ r) hs₁
    have h₁' : p ≫ s₁.hom = sT.hom ≫ r := by
      dsimp [chapter10PullbackSection, r, chapter10BaseChangeToSource] at h₁
      rw [pullback.lift_fst] at h₁
      exact h₁
    have hDown : p ≫ sDown.hom = sT.hom ≫ r := by
      have hDown' : (chapter10PullbackSection f p sDown).hom = sT.hom := by
        apply pullback.hom_ext
        · dsimp [chapter10PullbackSection, sDown]
          rw [pullback.lift_fst]
          exact hfac
        · dsimp [chapter10PullbackSection, sDown]
          rw [pullback.lift_snd]
          exact sT.isSection.symm
      have hDown'' := congrArg (fun k => k ≫ r) hDown'
      dsimp [chapter10PullbackSection, sDown, r, chapter10BaseChangeToSource] at hDown''
      rw [pullback.lift_fst] at hDown''
      exact hDown''
    have hhom : s₁.hom = sDown.hom :=
      (cancel_epi p).1 (h₁'.trans hDown.symm)
    exact hsection_ext hhom

/-- The overlap criterion for sections is equivalent to existence and uniqueness downstairs. -/
theorem chapter10_section_descent_iff {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) (sT : Chapter10Section (chapter10BaseChangeMorphism f p)) :
    chapter10SectionDescentCompatible f p sT ↔
      ∃! s : Chapter10Section f, (chapter10PullbackSection f p s).hom = sT.hom := by
  constructor
  · intro hs
    exact chapter10_section_descent f p hp sT hs
  · intro h
    obtain ⟨s, hs', _⟩ := h
    change chapter10DoubleOverlapFirst p ≫ sT.hom ≫ chapter10BaseChangeToSource f p =
      chapter10DoubleOverlapSecond p ≫ sT.hom ≫ chapter10BaseChangeToSource f p
    rw [← hs']
    dsimp [chapter10PullbackSection, chapter10BaseChangeToSource,
      chapter10DoubleOverlapFirst, chapter10DoubleOverlapSecond]
    rw [pullback.lift_fst]
    rw [← Category.assoc, ← Category.assoc, chapter10DoubleOverlap_condition]

/-- Automorphisms over a base, expressed as isomorphisms in the over category. -/
abbrev Chapter10Automorphism {S : Scheme.{u}} (X : Chapter10SchemeOver S) :=
  chapter10OverObject X ≅ chapter10OverObject X

/-- Base change of an automorphism. -/
def chapter10PullbackAutomorphism {S T : Scheme.{u}} (p : T ⟶ S)
    {X : Chapter10SchemeOver S} (a : Chapter10Automorphism X) :
    chapter10BaseChangeOver p X ≅ chapter10BaseChangeOver p X :=
  (Over.pullback p).mapIso a

/-- Compatibility of an upstairs automorphism with the canonical comparison of the two overlap
pullbacks. -/
def chapter10AutomorphismDescentCompatible {S T : Scheme.{u}} (p : T ⟶ S)
    {X : Chapter10SchemeOver S}
    (aT : chapter10BaseChangeOver p X ≅ chapter10BaseChangeOver p X) : Prop :=
  chapter10OverlapFirstHom p (X := X) (Y := X) aT.hom ≫
      (chapter10DoubleOverlapComparison p X).hom =
    (chapter10DoubleOverlapComparison p X).hom ≫
      chapter10OverlapSecondHom p (X := X) (Y := X) aT.hom

/-- Compatibility is closed under taking inverses. -/
theorem chapter10_automorphism_inverse_compatible {S T : Scheme.{u}} (p : T ⟶ S)
    {X : Chapter10SchemeOver S}
    (aT : chapter10BaseChangeOver p X ≅ chapter10BaseChangeOver p X)
    (ha : chapter10AutomorphismDescentCompatible p aT) :
    chapter10AutomorphismDescentCompatible p aT.symm := by
  let aFirst := (Over.pullback (chapter10DoubleOverlapFirst p)).mapIso aT
  let aSecond := (Over.pullback (chapter10DoubleOverlapSecond p)).mapIso aT
  have ha' : aFirst.hom ≫ (chapter10DoubleOverlapComparison p X).hom =
      (chapter10DoubleOverlapComparison p X).hom ≫ aSecond.hom := by
    simpa [chapter10AutomorphismDescentCompatible, chapter10OverlapFirstHom,
      chapter10OverlapSecondHom, aFirst, aSecond] using ha
  have hi : aFirst.inv ≫ (chapter10DoubleOverlapComparison p X).hom =
      (chapter10DoubleOverlapComparison p X).hom ≫ aSecond.inv := by
    calc
      aFirst.inv ≫ (chapter10DoubleOverlapComparison p X).hom =
          aFirst.inv ≫ (aFirst.hom ≫ (chapter10DoubleOverlapComparison p X).hom ≫
            aSecond.inv) := by
              rw [← Category.assoc aFirst.hom (chapter10DoubleOverlapComparison p X).hom
                aSecond.inv]
              rw [ha']
              simp
      _ = (chapter10DoubleOverlapComparison p X).hom ≫ aSecond.inv := by
        simp
  simpa [chapter10AutomorphismDescentCompatible, chapter10OverlapFirstHom,
    chapter10OverlapSecondHom, aFirst, aSecond] using hi

/-- Compatible automorphisms descend, and their inverses descend at the same time. -/
theorem chapter10_automorphism_descent {S T : Scheme.{u}} (p : T ⟶ S)
    (hp : Chapter10FpqcCover p) {X : Chapter10SchemeOver S}
    (aT : chapter10BaseChangeOver p X ≅ chapter10BaseChangeOver p X)
    (ha : chapter10AutomorphismDescentCompatible p aT) :
    ∃! a : Chapter10Automorphism X, chapter10PullbackAutomorphism p a = aT := by
  have ha' : chapter10DescentCompatible p aT.hom := by
    unfold chapter10DescentCompatible
    have ha₁ : chapter10OverlapFirstHom p aT.hom ≫
        (chapter10DoubleOverlapComparison p X).hom =
        (chapter10DoubleOverlapComparison p X).hom ≫
          chapter10OverlapSecondHom p aT.hom := by
      simpa [chapter10AutomorphismDescentCompatible] using ha
    calc
      chapter10OverlapFirstHom p aT.hom =
          (chapter10OverlapFirstHom p aT.hom ≫
            (chapter10DoubleOverlapComparison p X).hom) ≫
            (chapter10DoubleOverlapComparison p X).inv := by simp
      _ = ((chapter10DoubleOverlapComparison p X).hom ≫
          chapter10OverlapSecondHom p aT.hom) ≫
            (chapter10DoubleOverlapComparison p X).inv := by rw [ha₁]
      _ = chapter10OverlapSecondHomTransported p aT.hom := by
        simp [chapter10OverlapSecondHomTransported, Category.assoc]
  obtain ⟨a₀, ha₀⟩ :=
    (chapter10_morphism_descends_iff p hp X X aT.hom).2 ha'
  have haInv : chapter10AutomorphismDescentCompatible p aT.symm :=
    chapter10_automorphism_inverse_compatible p aT ha
  have haInv' : chapter10DescentCompatible p aT.inv := by
    unfold chapter10DescentCompatible
    have haInv₁ : chapter10OverlapFirstHom p aT.inv ≫
        (chapter10DoubleOverlapComparison p X).hom =
        (chapter10DoubleOverlapComparison p X).hom ≫
          chapter10OverlapSecondHom p aT.inv := by
      simpa [chapter10AutomorphismDescentCompatible] using haInv
    calc
      chapter10OverlapFirstHom p aT.inv =
          (chapter10OverlapFirstHom p aT.inv ≫
            (chapter10DoubleOverlapComparison p X).hom) ≫
            (chapter10DoubleOverlapComparison p X).inv := by simp
      _ = ((chapter10DoubleOverlapComparison p X).hom ≫
          chapter10OverlapSecondHom p aT.inv) ≫
            (chapter10DoubleOverlapComparison p X).inv := by rw [haInv₁]
      _ = chapter10OverlapSecondHomTransported p aT.inv := by
        simp [chapter10OverlapSecondHomTransported, Category.assoc]
  obtain ⟨aInv₀, haInv₀⟩ :=
    (chapter10_morphism_descends_iff p hp X X aT.inv).2 haInv'
  have ha₀' : (Over.pullback p).map a₀ = aT.hom := ha₀
  have haInv₀' : (Over.pullback p).map aInv₀ = aT.inv := haInv₀
  let a : Chapter10Automorphism X :=
    { hom := a₀
      inv := aInv₀
      hom_inv_id := by
        apply chapter10_morphism_descends_unique p hp X X
        change (Over.pullback p).map (a₀ ≫ aInv₀) =
          (Over.pullback p).map (𝟙 (chapter10OverObject X))
        rw [Functor.map_comp, ha₀', haInv₀']
        simp
      inv_hom_id := by
        apply chapter10_morphism_descends_unique p hp X X
        change (Over.pullback p).map (aInv₀ ≫ a₀) =
          (Over.pullback p).map (𝟙 (chapter10OverObject X))
        rw [Functor.map_comp, haInv₀', ha₀']
        simp }
  refine ⟨a, ?_, ?_⟩
  · apply Iso.ext
    change (Over.pullback p).map a₀ = aT.hom
    exact ha₀
  · intro b hb
    apply Iso.ext
    apply chapter10_morphism_descends_unique p hp X X
    have hb' : chapter10BaseChangeOverHom p b.hom = aT.hom := by
      change (Over.pullback p).map b.hom = aT.hom
      exact congrArg Iso.hom hb
    rw [hb', ha₀]

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10
