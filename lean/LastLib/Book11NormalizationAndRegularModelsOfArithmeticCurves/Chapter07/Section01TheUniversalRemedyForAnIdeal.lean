import LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07.Dependencies

namespace LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open scoped AlgebraicGeometry

universe u v

/-! ## 7.1. The universal remedy for an ideal -/

/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib API exposes absolute `Proj` but not relative `Proj`
of a quasi-coherent graded algebra.  The record below keeps the relative-Proj presentation and
its universal property together until that API is available. -/
/- LOCAL_DEPENDENCY_GUESS: the pinned Mathlib API exposes absolute `Proj` but not the
relative structure map of the Rees `Proj`; the map is kept as a chapter-facing interface until
that API is available. -/
noncomputable def chapter07ReesProjMapOnAffine
    {X : Scheme.{u}} (U : X.affineOpens) (I : X.IdealSheafData) :
    chapter07ReesProj (Γ(X, U)) (I.ideal U) ⟶ U.1.toScheme := by
  let G := chapter07CanonicalReesGrading (Γ(X, U)) (I.ideal U)
  letI : CommRing (Chapter07ReesAlgebra (Γ(X, U)) (I.ideal U)) := inferInstance
  letI : GradedAlgebra G.component := G.graded
  exact AlgebraicGeometry.Proj.toSpecZero G.component ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap (Γ(X, U)) (G.component 0))) ≫ U.2.isoSpec.inv

structure Chapter07IdealModulePresentation
    {X : Scheme.{u}} (I : X.IdealSheafData) where
  module : X.Modules
  isInvertible : chapter04IsInvertible module
  /- LOCAL_DEPENDENCY_GUESS: pinned Mathlib has ideal-sheaf data but no coherent ideal
  subsheaf object in `X.Modules`; local module realizations retain the needed relation. -/
  realizesIdeal :
    ∀ U : X.affineOpens,
      Nonempty
        (I.ideal U ≃ₗ[Γ(X, U)]
          (Scheme.Modules.presheaf module).obj (Opposite.op U))

/- The line bundle is explicit so the tautological `O(1)` is not weakened to an
unspecified line bundle.  The relative-Proj API is carried by the blowup record. -/
structure Chapter07IdealLineBundleIso
    {X : Scheme.{u}} (I : X.IdealSheafData) (line : Chapter04LineBundle X) where
  idealModule : Chapter07IdealModulePresentation I
  iso : idealModule.module ≅ line.sheaf

structure Chapter07Blowup {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) where
  carrier : Scheme.{u}
  projection : carrier ⟶ X
  rees_presentation :
    ∀ U : X.affineOpens,
      Nonempty
        (Chapter07SchemeIsoOver
          (projection ∣_ U)
          (chapter07ReesProjMapOnAffine U I.ideal))
  quasiCompact : QuasiCompact projection
  quasiSeparated : QuasiSeparated projection
  projective : Chapter07IsProjectiveMorphism projection
  tautologicalIdeal : Chapter07CoherentIdeal carrier
  tautological_ideal_eq_pullback :
    tautologicalIdeal.ideal = I.ideal.comap projection
  tautological_isInvertible : Chapter07IsInvertibleIdeal tautologicalIdeal.ideal
  tautologicalLine : Chapter04LineBundle carrier
  tautologicalLine_iso :
    Nonempty (Chapter07IdealLineBundleIso tautologicalIdeal.ideal tautologicalLine)
  universal : ∀ {Y : Scheme.{u}} (g : Y ⟶ X),
    Chapter07IsInvertibleIdeal (I.ideal.comap g) →
      ∃! u : Y ⟶ carrier, u ≫ projection = g

def chapter07BlowupTautologicalIdeal
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    Chapter07CoherentIdeal B.carrier :=
  B.tautologicalIdeal

theorem chapter07_blowup_tautologicalIdeal_eq_pullback
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    B.tautologicalIdeal.ideal = I.ideal.comap B.projection :=
  B.tautological_ideal_eq_pullback

theorem chapter07_blowup_tautologicalIdeal_isInvertible
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    Chapter07IsInvertibleIdeal B.tautologicalIdeal.ideal :=
  B.tautological_isInvertible

/- The sign convention is intentionally carried by the name of the chosen twisting line. -/
def Chapter07OOne {X : Scheme.{u}} (I : X.IdealSheafData)
    (line : Chapter04LineBundle X) : Prop :=
  Nonempty (Chapter07IdealLineBundleIso I line)

theorem chapter07_blowup_tautological_ideal_is_O_one
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    Chapter07OOne B.tautologicalIdeal.ideal B.tautologicalLine :=
  B.tautologicalLine_iso

theorem chapter07_blowup_exists
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) : Nonempty (Chapter07Blowup I) := by
  sorry

noncomputable def chapter07Blowup
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X) : Chapter07Blowup I :=
  Classical.choice (chapter07_blowup_exists I)

abbrev chapter07BlowupScheme
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) : Scheme :=
  B.carrier

abbrev chapter07BlowupMap
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    B.carrier ⟶ X :=
  B.projection

theorem chapter07_blowup_universal_property
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (hI : Chapter07IsInvertibleIdeal (I.ideal.comap g)) :
    ∃! u : Y ⟶ B.carrier, u ≫ B.projection = g :=
  B.universal g hI

theorem chapter07_blowup_factor_exists
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (hI : Chapter07IsInvertibleIdeal (I.ideal.comap g)) :
    ∃ u : Y ⟶ B.carrier, u ≫ B.projection = g := by
  exact (chapter07_blowup_universal_property B g hI).exists

theorem chapter07_blowup_factor_unique
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    {Y : Scheme.{u}} (g : Y ⟶ X)
    (hI : Chapter07IsInvertibleIdeal (I.ideal.comap g))
    {u v : Y ⟶ B.carrier} (hu : u ≫ B.projection = g) (hv : v ≫ B.projection = g) :
    u = v := by
  exact (B.universal g hI).unique hu hv

theorem chapter07_blowup_projection_is_qc
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    QuasiCompact B.projection :=
  B.quasiCompact

theorem chapter07_blowup_projection_is_qs
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    QuasiSeparated B.projection :=
  B.quasiSeparated

theorem chapter07_blowup_unit_ideal_isIso
    (X : Scheme.{u}) :
    IsIso (chapter07Blowup (chapter07UnitCoherentIdeal X)).projection := by
  let hTop : Chapter07IsInvertibleIdeal (chapter07UnitCoherentIdeal X).ideal := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    refine ⟨⟨U, hU⟩, hxU, 1, ?_, isRegular_one⟩
    change (⊤ : Ideal Γ(X, U)) = Ideal.span {(1 : Γ(X, U))}
    simp
  let B := chapter07Blowup (chapter07UnitCoherentIdeal X)
  change IsIso B.projection
  obtain ⟨s, hs⟩ := chapter07_blowup_factor_exists B (𝟙 X) (by
    simpa using hTop)
  have hproj :
      Chapter07IsInvertibleIdeal ((chapter07UnitCoherentIdeal X).ideal.comap B.projection) := by
    rw [← B.tautological_ideal_eq_pullback]
    exact B.tautological_isInvertible
  refine ⟨⟨s, ?_, hs⟩⟩
  exact (B.universal B.projection hproj).unique (by simp [Category.assoc, hs]) (by simp)

theorem chapter07_blowup_invertible_ideal_isIso
    {X : Scheme.{u}} (I : Chapter07CoherentIdeal X)
    (hI : Chapter07IsInvertibleIdeal I.ideal) :
    IsIso (chapter07Blowup I).projection := by
  let B := chapter07Blowup I
  change IsIso B.projection
  obtain ⟨s, hs⟩ := chapter07_blowup_factor_exists B (𝟙 X) (by
    simpa using hI)
  have hproj : Chapter07IsInvertibleIdeal (I.ideal.comap B.projection) := by
    rw [← B.tautological_ideal_eq_pullback]
    exact B.tautological_isInvertible
  refine ⟨⟨s, ?_, hs⟩⟩
  exact (B.universal B.projection hproj).unique (by simp [Category.assoc, hs]) (by simp)

private theorem chapter07_isInvertibleIdeal_comap_support_compl
    {X : Scheme.{u}} (J : X.IdealSheafData) :
    Chapter07IsInvertibleIdeal (J.comap (Scheme.Opens.ι J.support.compl)) := by
  intro x
  let Y := Scheme.Opens.toScheme J.support.compl
  let K := J.comap (Scheme.Opens.ι J.support.compl)
  obtain ⟨_, ⟨V₀ : Y.Opens, hV₀, rfl⟩, hxV₀, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let V : Y.affineOpens := ⟨V₀, hV₀⟩
  have hxV : x ∈ V.1 := hxV₀
  have hxK : x ∉ K.support := by
    rw [show K = J.comap (Scheme.Opens.ι J.support.compl) from rfl,
      J.support_comap]
    exact x.2
  have hxzero : x ∉ Y.zeroLocus (U := V.1) (K.ideal V) := by
    intro hx
    apply hxK
    exact (K.mem_support_iff_of_mem hxV).2 hx
  have hex : ∃ a ∈ K.ideal V, x ∈ Y.basicOpen a := by
    by_contra h
    apply hxzero
    rw [Scheme.mem_zeroLocus_iff]
    intro a ha
    by_contra hax
    apply h
    exact ⟨a, ha, hax⟩
  obtain ⟨a, ha, hax⟩ := hex
  let W := Y.affineBasicOpen a
  have ha' :
      (Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op).hom a ∈ K.ideal W := by
    rw [← K.map_ideal_basicOpen V a]
    exact Ideal.mem_map_of_mem _ ha
  have haunit :
      IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le a)).op).hom a) := by
    exact Y.toRingedSpace.isUnit_res_basicOpen a
  have htop : K.ideal W = ⊤ := Ideal.eq_top_of_isUnit_mem _ ha' haunit
  exact ⟨W, hax, 1, by rw [htop]; simp, isRegular_one⟩

private theorem chapter07_ideal_comap_support_compl_eq_top
    {X : Scheme.{u}} (J : X.IdealSheafData) :
    J.comap (Scheme.Opens.ι J.support.compl) = ⊤ := by
  let K := J.comap (Scheme.Opens.ι J.support.compl)
  have hsupport : K.support = (⊥ : TopologicalSpace.Closeds (Scheme.Opens.toScheme
      J.support.compl)) := by
    rw [show K = J.comap (Scheme.Opens.ι J.support.compl) from rfl, J.support_comap]
    ext x
    simp
    change x.1 ∉ J.support
    exact x.2
  have hrad : K.radical = ⊤ := by
    rw [← K.vanishingIdeal_support, hsupport]
    exact Scheme.IdealSheafData.vanishingIdeal_bot
  apply Scheme.IdealSheafData.ext
  funext V
  have hV := congrArg
    (fun L : (Scheme.Opens.toScheme J.support.compl).IdealSheafData => L.ideal V) hrad
  exact Ideal.radical_eq_top.mp (by simpa using hV)

def chapter07BlowupRestriction
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    (U : X.Opens) : (B.projection ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
  B.projection ∣_ U

theorem chapter07_blowup_isIso_off_support
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I) :
    IsIso (chapter07BlowupRestriction B I.ideal.support.compl) := by
  let U : X.Opens := I.ideal.support.compl
  change IsIso (B.projection ∣_ U)
  have hU : Chapter07IsInvertibleIdeal (I.ideal.comap U.ι) := by
    dsimp [U]
    exact chapter07_isInvertibleIdeal_comap_support_compl I.ideal
  obtain ⟨s, hs⟩ := chapter07_blowup_factor_exists B U.ι hU
  let P : B.carrier.Opens := B.projection ⁻¹ᵁ U
  have hsRange : Set.range s ⊆ Set.range P.ι := by
    rintro _ ⟨y, rfl⟩
    refine ⟨⟨s y, ?_⟩, rfl⟩
    change B.projection (s y) ∈ U
    have hpoint := congrArg (fun q : U.toScheme ⟶ X => q y) hs
    have hpoint' : B.projection (s y) = U.ι y := by
      simpa [Scheme.Hom.comp_apply] using hpoint
    rw [hpoint']
    exact y.2
  let t : U.toScheme ⟶ P.toScheme := IsOpenImmersion.lift P.ι s hsRange
  have ht : t ≫ P.ι = s := by
    exact IsOpenImmersion.lift_fac P.ι s hsRange
  have hKtop : I.ideal.comap U.ι = ⊤ := by
    dsimp [U]
    exact chapter07_ideal_comap_support_compl_eq_top I.ideal
  have hPU : P.ι ≫ B.projection = (B.projection ∣_ U) ≫ U.ι := by
    dsimp [P]
    exact (morphismRestrict_ι B.projection U).symm
  have hg : Chapter07IsInvertibleIdeal
      (I.ideal.comap (P.ι ≫ B.projection)) := by
    rw [hPU, Scheme.IdealSheafData.comap_comp, hKtop,
      Scheme.IdealSheafData.comap_top]
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      (P.toScheme).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ y) isOpen_univ
    exact ⟨⟨V, hV⟩, hyV, 1, by simp, isRegular_one⟩
  have hfs : (B.projection ∣_ U) ≫ s = P.ι := by
    exact chapter07_blowup_factor_unique B (P.ι ≫ B.projection) hg
      (by simp [Category.assoc, hs, morphismRestrict_ι, P]) (by simp [P])
  have htf : t ≫ (B.projection ∣_ U) = 𝟙 _ := by
    apply (cancel_mono U.ι).1
    rw [Category.assoc, morphismRestrict_ι]
    change t ≫ P.ι ≫ B.projection = U.ι
    rw [← Category.assoc, ht, hs]
  have hft : (B.projection ∣_ U) ≫ t = 𝟙 _ := by
    apply (cancel_mono P.ι).1
    simp [Category.assoc, ht, hfs]
  exact ⟨⟨t, hft, htf⟩⟩

private theorem chapter07_blowup_isIso_on_open_of_le_support_compl
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    (U : X.Opens) (hU : U ≤ I.ideal.support.compl) :
    IsIso (B.projection ∣_ U) := by
  have hVtop : I.ideal.comap (Scheme.Opens.ι I.ideal.support.compl) = ⊤ :=
    chapter07_ideal_comap_support_compl_eq_top I.ideal
  have hUtop : I.ideal.comap U.ι = ⊤ := by
    have hfac : U.ι = (X.homOfLE hU) ≫ Scheme.Opens.ι I.ideal.support.compl := by
      exact (Scheme.homOfLE_ι X hU).symm
    rw [hfac, Scheme.IdealSheafData.comap_comp, hVtop,
      Scheme.IdealSheafData.comap_top]
  have hI : Chapter07IsInvertibleIdeal (I.ideal.comap U.ι) := by
    rw [hUtop]
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ y) isOpen_univ
    exact ⟨⟨V, hV⟩, hyV, 1, by simp, isRegular_one⟩
  obtain ⟨s, hs⟩ := chapter07_blowup_factor_exists B U.ι hI
  let P : B.carrier.Opens := B.projection ⁻¹ᵁ U
  have hsRange : Set.range s ⊆ Set.range P.ι := by
    rintro _ ⟨y, rfl⟩
    refine ⟨⟨s y, ?_⟩, rfl⟩
    change B.projection (s y) ∈ U
    have hpoint := congrArg (fun q : U.toScheme ⟶ X => q y) hs
    have hpoint' : B.projection (s y) = U.ι y := by
      simpa [Scheme.Hom.comp_apply] using hpoint
    rw [hpoint']
    exact y.2
  let t : U.toScheme ⟶ P.toScheme := IsOpenImmersion.lift P.ι s hsRange
  have ht : t ≫ P.ι = s := by
    exact IsOpenImmersion.lift_fac P.ι s hsRange
  have hPU : P.ι ≫ B.projection = (B.projection ∣_ U) ≫ U.ι := by
    dsimp [P]
    exact (morphismRestrict_ι B.projection U).symm
  have hg : Chapter07IsInvertibleIdeal
      (I.ideal.comap (P.ι ≫ B.projection)) := by
    rw [hPU, Scheme.IdealSheafData.comap_comp, hUtop,
      Scheme.IdealSheafData.comap_top]
    intro y
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      P.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ y) isOpen_univ
    exact ⟨⟨V, hV⟩, hyV, 1, by simp, isRegular_one⟩
  have hfs : (B.projection ∣_ U) ≫ s = P.ι := by
    exact chapter07_blowup_factor_unique B (P.ι ≫ B.projection) hg
      (by simp [Category.assoc, hs, morphismRestrict_ι, P]) (by simp [P])
  have htf : t ≫ (B.projection ∣_ U) = 𝟙 _ := by
    apply (cancel_mono U.ι).1
    rw [Category.assoc, morphismRestrict_ι]
    change t ≫ P.ι ≫ B.projection = U.ι
    rw [← Category.assoc, ht, hs]
  have hft : (B.projection ∣_ U) ≫ t = 𝟙 _ := by
    apply (cancel_mono P.ι).1
    simp [Category.assoc, ht, hfs]
  exact ⟨⟨t, hft, htf⟩⟩

noncomputable def chapter07FiniteCenterComplement
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X}
    (C : Chapter07FiniteClosedPointCenter I) : X.Opens := by
  refine ⟨(C.points : Set X)ᶜ, ?_⟩
  apply isOpen_compl_iff.mpr
  have h : (⋃ x ∈ C.points, ({x} : Set X)) = (C.points : Set X) := by
    ext x
    simp
  rw [← h]
  exact isClosed_biUnion_finset (fun x hx => C.points_closed x hx)

theorem chapter07_blowup_isIso_off_finite_closed_center
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    (C : Chapter07FiniteClosedPointCenter I) :
    IsIso (chapter07BlowupRestriction B (chapter07FiniteCenterComplement C)) := by
  apply chapter07_blowup_isIso_on_open_of_le_support_compl B
  intro x hx
  change x ∉ (C.points : Set X) at hx
  intro hxS
  obtain ⟨p, hp, hxp⟩ := C.support_subset x hxS
  apply hx
  simpa [hxp] using hp

theorem chapter07_blowup_isIso_over_finite_center_complement
    {X : Scheme.{u}} {I : Chapter07CoherentIdeal X} (B : Chapter07Blowup I)
    (C : Chapter07FiniteClosedPointCenter I) :
    IsIso (chapter07BlowupRestriction B (chapter07FiniteCenterComplement C)) := by
  exact chapter07_blowup_isIso_off_finite_closed_center B C

end

end LastLib.Book11NormalizationAndRegularModelsOfArithmeticCurves.Chapter07
