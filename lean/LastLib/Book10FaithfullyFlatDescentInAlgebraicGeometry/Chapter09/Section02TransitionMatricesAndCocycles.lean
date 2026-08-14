import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Dependencies
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section01ProjectiveBundles

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

/-! ## 9.2 Transition matrices and cocycles -/

/-- The affine rings and ring maps in a Čech diagram.  The maps `pair12`, `pair23`, and `pair13`
are the three pullbacks from the double overlap to the triple overlap. -/
structure Chapter09AffineCechNerve
    (R T D Q : Type u)
    [CommRing R] [CommRing T] [CommRing D] [CommRing Q] where
  base : R →+* T
  first : T →+* D
  second : T →+* D
  base_compatibility : first.comp base = second.comp base
  pair12 : D →+* Q
  pair23 : D →+* Q
  pair13 : D →+* Q
  pair12_first : pair12.comp first = pair13.comp first
  pair12_second : pair12.comp second = pair23.comp first
  pair23_second : pair23.comp second = pair13.comp second

/-- Base change of an invertible matrix along an overlap ring map. -/
noncomputable def chapter09MatrixBaseChange
    {D Q : Type u} [CommRing D] [CommRing Q]
    {r : ℕ} (f : D →+* Q) (g : Matrix.GeneralLinearGroup (Fin r) D) :
    Matrix.GeneralLinearGroup (Fin r) Q :=
  Matrix.GeneralLinearGroup.map f g

/-- The matrix form of the triple-overlap cocycle equation `g₂₃ g₁₂ = g₁₃`. -/
def chapter09MatrixCocycle
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin r) D) : Prop :=
  chapter09MatrixBaseChange N.pair23 g * chapter09MatrixBaseChange N.pair12 g =
    chapter09MatrixBaseChange N.pair13 g

/-- A transition matrix together with its triple-overlap cocycle proof. -/
structure Chapter09AffineTransitionCocycle
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ) where
  transition : Matrix.GeneralLinearGroup (Fin r) D
  cocycle : chapter09MatrixCocycle N r transition

/-! ### Affine module data and chosen frames

 The matrix presentation is obtained from an actual module descent datum after choosing frames on
 the two overlap pullbacks.  The module-level cocycle below is stated as an equality of the
 induced Q-linear maps on the free overlap module; the theorem following the datum translates it
 to the matrix equation used by the classification API. -/

noncomputable def chapter09AffineFrameTransitionLinearEquiv
    {D : Type u} [CommRing D] (r : ℕ)
    (firstModule secondModule : ModuleCat D)
    (firstTrivialization : ModuleCat.of D (Fin r → D) ≅ firstModule)
    (secondTrivialization : ModuleCat.of D (Fin r → D) ≅ secondModule)
    (overlapIso : firstModule ≅ secondModule) :
    (Fin r → D) ≃ₗ[D] Fin r → D :=
  (firstTrivialization ≪≫ overlapIso ≪≫ secondTrivialization.symm).toLinearEquiv

noncomputable def chapter09AffineFrameTransitionMatrix
    {D : Type u} [CommRing D] (r : ℕ)
    (firstModule secondModule : ModuleCat D)
    (firstTrivialization : ModuleCat.of D (Fin r → D) ≅ firstModule)
    (secondTrivialization : ModuleCat.of D (Fin r → D) ≅ secondModule)
    (overlapIso : firstModule ≅ secondModule) :
    Matrix.GeneralLinearGroup (Fin r) D :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin r) (R := D)).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv
      (chapter09AffineFrameTransitionLinearEquiv r firstModule secondModule
        firstTrivialization secondTrivialization overlapIso))

def chapter09AffineModuleCocycle
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (firstModule secondModule : ModuleCat D)
    (firstTrivialization : ModuleCat.of D (Fin r → D) ≅ firstModule)
    (secondTrivialization : ModuleCat.of D (Fin r → D) ≅ secondModule)
    (overlapIso : firstModule ≅ secondModule) : Prop :=
  ((Matrix.GeneralLinearGroup.toLin
      (chapter09MatrixBaseChange N.pair12
        (chapter09AffineFrameTransitionMatrix r firstModule secondModule
          firstTrivialization secondTrivialization overlapIso))).toLinearEquiv.toModuleIso).hom ≫
      ((Matrix.GeneralLinearGroup.toLin
        (chapter09MatrixBaseChange N.pair23
          (chapter09AffineFrameTransitionMatrix r firstModule secondModule
            firstTrivialization secondTrivialization overlapIso))).toLinearEquiv.toModuleIso).hom =
    ((Matrix.GeneralLinearGroup.toLin
      (chapter09MatrixBaseChange N.pair13
        (chapter09AffineFrameTransitionMatrix r firstModule secondModule
          firstTrivialization secondTrivialization overlapIso))).toLinearEquiv.toModuleIso).hom

/-- An affine rank-`r` module descent datum together with chosen frames on both overlap pullbacks.
The `firstBaseChange` and `secondBaseChange` fields retain the module-theoretic origin of the two
overlap modules; `moduleCocycle` is the Čech law before it is repackaged as a matrix equation. -/
structure Chapter09AffineModuleDescentDatum
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ) where
  upstairs : ModuleCat T
  upstairsTrivialization : upstairs ≅ ModuleCat.of T (Fin r → T)
  firstModule : ModuleCat D
  secondModule : ModuleCat D
  firstBaseChange : (ModuleCat.extendScalars N.first).obj upstairs ≅ firstModule
  secondBaseChange : (ModuleCat.extendScalars N.second).obj upstairs ≅ secondModule
  firstTrivialization : ModuleCat.of D (Fin r → D) ≅ firstModule
  secondTrivialization : ModuleCat.of D (Fin r → D) ≅ secondModule
  overlapIso : firstModule ≅ secondModule
  moduleCocycle :
    chapter09AffineModuleCocycle N r firstModule secondModule
      firstTrivialization secondTrivialization overlapIso

noncomputable def chapter09AffineTransitionMatrix
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    {N : Chapter09AffineCechNerve R T D Q} {r : ℕ}
    (Ddatum : Chapter09AffineModuleDescentDatum N r) :
    Matrix.GeneralLinearGroup (Fin r) D :=
  chapter09AffineFrameTransitionMatrix r Ddatum.firstModule Ddatum.secondModule
    Ddatum.firstTrivialization Ddatum.secondTrivialization Ddatum.overlapIso

theorem chapter09_affine_module_descent_matrix_cocycle
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    {N : Chapter09AffineCechNerve R T D Q} {r : ℕ}
    (Ddatum : Chapter09AffineModuleDescentDatum N r) :
    chapter09MatrixCocycle N r (chapter09AffineTransitionMatrix Ddatum) := by
  apply (Matrix.GeneralLinearGroup.toLin).injective
  rw [map_mul]
  apply Units.ext
  change
    (Matrix.GeneralLinearGroup.toLin
        (chapter09MatrixBaseChange N.pair23 (chapter09AffineTransitionMatrix Ddatum))).toLinearEquiv.toLinearMap.comp
      (Matrix.GeneralLinearGroup.toLin
        (chapter09MatrixBaseChange N.pair12 (chapter09AffineTransitionMatrix Ddatum))).toLinearEquiv.toLinearMap =
    (Matrix.GeneralLinearGroup.toLin
        (chapter09MatrixBaseChange N.pair13 (chapter09AffineTransitionMatrix Ddatum))).toLinearEquiv.toLinearMap
  have hc := congrArg
    (fun f : ModuleCat.of Q (Fin r → Q) ⟶ ModuleCat.of Q (Fin r → Q) => f.hom)
    Ddatum.moduleCocycle
  exact hc

noncomputable def chapter09AffineTransitionCocycleOfModuleDescentDatum
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    {N : Chapter09AffineCechNerve R T D Q} {r : ℕ}
    (Ddatum : Chapter09AffineModuleDescentDatum N r) :
    Chapter09AffineTransitionCocycle N r where
  transition := chapter09AffineTransitionMatrix Ddatum
  cocycle := chapter09_affine_module_descent_matrix_cocycle Ddatum

noncomputable def chapter09MatrixModuleIsoOfBaseChange
    {D Q : Type u} [CommRing D] [CommRing Q] (r : ℕ)
    (f : D →+* Q) (g : Matrix.GeneralLinearGroup (Fin r) D) :
    ModuleCat.of Q (Fin r → Q) ≅ ModuleCat.of Q (Fin r → Q) :=
  (Matrix.GeneralLinearGroup.toLin
      (chapter09MatrixBaseChange f g)).toLinearEquiv.toModuleIso

/- A change of basis on the trivial bundle acts by `h₂ g h₁⁻¹`. -/
noncomputable def chapter09GaugeTransform
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (h : Matrix.GeneralLinearGroup (Fin r) T)
    (g : Matrix.GeneralLinearGroup (Fin r) D) :
    Matrix.GeneralLinearGroup (Fin r) D :=
  chapter09MatrixBaseChange N.second h * g * (chapter09MatrixBaseChange N.first h)⁻¹

theorem chapter09_affine_module_descent_transition_gauge
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    {N : Chapter09AffineCechNerve R T D Q} {r : ℕ}
    (Ddatum : Chapter09AffineModuleDescentDatum N r)
    (h : Matrix.GeneralLinearGroup (Fin r) T)
    (firstTrivialization' : ModuleCat.of D (Fin r → D) ≅ Ddatum.firstModule)
    (secondTrivialization' : ModuleCat.of D (Fin r → D) ≅ Ddatum.secondModule)
    (h_first : firstTrivialization' =
      (chapter09MatrixModuleIsoOfBaseChange r N.first h).symm ≪≫
        Ddatum.firstTrivialization)
    (h_second : secondTrivialization' =
      (chapter09MatrixModuleIsoOfBaseChange r N.second h).symm ≪≫
        Ddatum.secondTrivialization) :
    chapter09AffineFrameTransitionMatrix r Ddatum.firstModule Ddatum.secondModule
        firstTrivialization' secondTrivialization' Ddatum.overlapIso =
      chapter09GaugeTransform N r h (chapter09AffineTransitionMatrix Ddatum) := by
  rw [h_first, h_second]
  apply (Matrix.GeneralLinearGroup.toLin).injective
  simp only [chapter09AffineFrameTransitionMatrix, chapter09AffineFrameTransitionLinearEquiv,
    chapter09MatrixModuleIsoOfBaseChange, chapter09GaugeTransform,
    chapter09AffineTransitionMatrix, MulEquiv.apply_symm_apply,
    map_mul, map_inv]
  apply Units.ext
  ext x
  rfl

def chapter09GaugeEquivalent
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (a b : Chapter09AffineTransitionCocycle N r) : Prop :=
  ∃ h : Matrix.GeneralLinearGroup (Fin r) T,
    b.transition = chapter09GaugeTransform N r h a.transition

theorem chapter09_gauge_transform_preserves_cocycle
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (a : Chapter09AffineTransitionCocycle N r)
    (h : Matrix.GeneralLinearGroup (Fin r) T) :
    chapter09MatrixCocycle N r (chapter09GaugeTransform N r h a.transition) := by
  simp only [chapter09MatrixCocycle, chapter09GaugeTransform, chapter09MatrixBaseChange,
    map_mul, map_inv]
  have h₂ :
      Matrix.GeneralLinearGroup.map N.pair23 (Matrix.GeneralLinearGroup.map N.second h) =
        Matrix.GeneralLinearGroup.map N.pair13 (Matrix.GeneralLinearGroup.map N.second h) := by
    change Matrix.GeneralLinearGroup.map (N.pair23.comp N.second) h =
      Matrix.GeneralLinearGroup.map (N.pair13.comp N.second) h
    rw [N.pair23_second]
  have h₁ :
      Matrix.GeneralLinearGroup.map N.pair12 (Matrix.GeneralLinearGroup.map N.first h) =
        Matrix.GeneralLinearGroup.map N.pair13 (Matrix.GeneralLinearGroup.map N.first h) := by
    change Matrix.GeneralLinearGroup.map (N.pair12.comp N.first) h =
      Matrix.GeneralLinearGroup.map (N.pair13.comp N.first) h
    rw [N.pair12_first]
  have h₁₂ :
      Matrix.GeneralLinearGroup.map N.pair12 (Matrix.GeneralLinearGroup.map N.second h) =
        Matrix.GeneralLinearGroup.map N.pair23 (Matrix.GeneralLinearGroup.map N.first h) := by
    change Matrix.GeneralLinearGroup.map (N.pair12.comp N.second) h =
      Matrix.GeneralLinearGroup.map (N.pair23.comp N.first) h
    rw [N.pair12_second]
  have h₁inv :
      (Matrix.GeneralLinearGroup.map N.pair12 (Matrix.GeneralLinearGroup.map N.first h))⁻¹ =
        (Matrix.GeneralLinearGroup.map N.pair13 (Matrix.GeneralLinearGroup.map N.first h))⁻¹ :=
    congrArg Inv.inv h₁
  have hc :
      Matrix.GeneralLinearGroup.map N.pair23 a.transition *
          Matrix.GeneralLinearGroup.map N.pair12 a.transition =
        Matrix.GeneralLinearGroup.map N.pair13 a.transition :=
    a.cocycle
  rw [h₂, h₁₂, h₁inv, ← hc]
  simp [mul_assoc]

instance chapter09AffineTransitionCocycleSetoid
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ) :
    Setoid (Chapter09AffineTransitionCocycle N r) where
  r := chapter09GaugeEquivalent N r
  iseqv := by
    constructor
    · intro a
      refine ⟨1, ?_⟩
      simp [chapter09GaugeTransform, chapter09MatrixBaseChange]
    · intro a b hab
      rcases hab with ⟨h, hh⟩
      refine ⟨h⁻¹, ?_⟩
      rw [hh]
      simp [chapter09GaugeTransform, chapter09MatrixBaseChange, map_inv, mul_assoc]
    · intro a b c hab₁ hab₂
      rcases hab₁ with ⟨h₁, hh₁⟩
      rcases hab₂ with ⟨h₂, hh₂⟩
      refine ⟨h₂ * h₁, ?_⟩
      rw [hh₂, hh₁]
      simp [chapter09GaugeTransform, chapter09MatrixBaseChange, map_mul, mul_assoc]

/-- Gauge-equivalence classes of affine transition cocycles. -/
abbrev Chapter09AffineCocycleClass
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ) :=
  Quotient (inferInstance : Setoid (Chapter09AffineTransitionCocycle N r))

def chapter09AffineCocycleClassMk
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (a : Chapter09AffineTransitionCocycle N r) :
    Chapter09AffineCocycleClass N r :=
  Quotient.mk _ a

theorem chapter09AffineCocycleClass_eq_iff
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (a b : Chapter09AffineTransitionCocycle N r) :
    chapter09AffineCocycleClassMk N r a = chapter09AffineCocycleClassMk N r b ↔
      chapter09GaugeEquivalent N r a b := by
  exact Quotient.eq

/- An isomorphism between chosen trivializations is represented by its change-of-basis matrix and
the resulting intertwining equation. -/
structure Chapter09TrivializedDescentDataIsomorphism
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (a b : Chapter09AffineTransitionCocycle N r) where
  gauge : Matrix.GeneralLinearGroup (Fin r) T
  intertwines : b.transition = chapter09GaugeTransform N r gauge a.transition

def chapter09TrivializedDescentDataIsomorphic
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (a b : Chapter09AffineTransitionCocycle N r) : Prop :=
  Nonempty (Chapter09TrivializedDescentDataIsomorphism N r a b)

theorem chapter09_trivialized_descent_isomorphic_iff_gauge
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (a b : Chapter09AffineTransitionCocycle N r) :
    chapter09TrivializedDescentDataIsomorphic N r a b ↔
      chapter09GaugeEquivalent N r a b := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i.gauge, i.intertwines⟩
  · rintro ⟨h, hh⟩
    exact ⟨⟨h, hh⟩⟩

/-! ### Rank one and multiplicative cocycles -/

def chapter09UnitCocycleCondition
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (u : Dˣ) : Prop :=
  Units.map N.pair23.toMonoidHom u * Units.map N.pair12.toMonoidHom u =
    Units.map N.pair13.toMonoidHom u

structure Chapter09AffineUnitCocycle
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) where
  transition : Dˣ
  cocycle : chapter09UnitCocycleCondition N transition

noncomputable def chapter09RankOneMatrixOfUnit
    {D : Type u} [CommRing D] (u : Dˣ) :
    Matrix.GeneralLinearGroup (Fin 1) D :=
  Matrix.GeneralLinearGroup.scalar (Fin 1) u

theorem chapter09_rank_one_matrix_cocycle_is_unit_cocycle
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q)
    (g : Matrix.GeneralLinearGroup (Fin 1) D)
    (hg : chapter09MatrixCocycle N 1 g) :
    chapter09UnitCocycleCondition N (Matrix.GeneralLinearGroup.det g) := by
  change chapter09MatrixBaseChange N.pair23 g * chapter09MatrixBaseChange N.pair12 g =
      chapter09MatrixBaseChange N.pair13 g at hg
  have h := congrArg (fun x : Matrix.GeneralLinearGroup (Fin 1) Q =>
    Matrix.GeneralLinearGroup.det x) hg
  change Units.map N.pair23.toMonoidHom (Matrix.GeneralLinearGroup.det g) *
      Units.map N.pair12.toMonoidHom (Matrix.GeneralLinearGroup.det g) =
        Units.map N.pair13.toMonoidHom (Matrix.GeneralLinearGroup.det g)
  simpa [chapter09MatrixBaseChange, Matrix.GeneralLinearGroup.map_det] using h

theorem chapter09_unit_cocycle_gives_rank_one_matrix_cocycle
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (u : Dˣ)
    (hu : chapter09UnitCocycleCondition N u) :
    chapter09MatrixCocycle N 1 (chapter09RankOneMatrixOfUnit u) := by
  change chapter09MatrixBaseChange N.pair23 (chapter09RankOneMatrixOfUnit u) *
      chapter09MatrixBaseChange N.pair12 (chapter09RankOneMatrixOfUnit u) =
        chapter09MatrixBaseChange N.pair13 (chapter09RankOneMatrixOfUnit u)
  simpa [chapter09MatrixBaseChange, chapter09RankOneMatrixOfUnit,
    Matrix.GeneralLinearGroup.map_scalar] using
    congrArg (Matrix.GeneralLinearGroup.scalar (Fin 1)) hu

noncomputable def chapter09UnitGaugeTransform
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (h : Tˣ) (u : Dˣ) : Dˣ :=
  Units.map N.second.toMonoidHom h * u * (Units.map N.first.toMonoidHom h)⁻¹

def chapter09UnitGaugeEquivalent
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q)
    (a b : Chapter09AffineUnitCocycle N) : Prop :=
  ∃ h : Tˣ, b.transition = chapter09UnitGaugeTransform N h a.transition

/-! ### The projective-line transition example -/

/- The pinned projective-spectrum API supplies the canonical projective line, tautological line
bundle, and standard affine cover.  The transition unit is extracted from the two selected chart
trivializations and is separately identified with the canonical degree-one coordinate. -/
def chapter09StructureRestriction
    {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) :
    Γ(X, U) →+* Γ(X, V) :=
  (X.sheaf.presheaf.map (homOfLE h).op).hom

def chapter09ProjectiveTransitionGaugeTrivial
    {X : Scheme.{u}} (U V : X.Opens) (g : (Γ(X, U ⊓ V))ˣ) : Prop :=
  ∃ hU : (Γ(X, U))ˣ, ∃ hV : (Γ(X, V))ˣ,
    g = Units.map
        (chapter09StructureRestriction
          (X := X) (U := V) (V := U ⊓ V) inf_le_right).toMonoidHom hV *
      (Units.map
        (chapter09StructureRestriction
          (X := X) (U := U) (V := U ⊓ V) inf_le_left).toMonoidHom hU)⁻¹

noncomputable def chapter09ProjectiveLineCoordinate
    (K : Type u) [Field K]
    (standardCover :
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02StandardAffineCover
        (AlgebraicGeometry.Spec (.of K))
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02ProjectiveSpaceIndex 1)
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceData
          (AlgebraicGeometry.Spec (.of K))
          (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02ProjectiveSpaceIndex 1))) :
    (Γ(LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04ProjectiveLine K,
      standardCover.chart (ULift.up (0 : Fin 2)) ⊓
        standardCover.chart (ULift.up (1 : Fin 2))))ˣ := by
  sorry

noncomputable def chapter09ProjectiveLineTransitionExtractor
    (K : Type u) [Field K]
    (standardLineBundle :
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04ProjectiveLine K))
    (standardCover :
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02StandardAffineCover
        (AlgebraicGeometry.Spec (.of K))
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02ProjectiveSpaceIndex 1)
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceData
          (AlgebraicGeometry.Spec (.of K))
          (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02ProjectiveSpaceIndex 1)))
    (trivial_on_zero_chart :
      (Scheme.Modules.pullback
        (standardCover.chart (ULift.up (0 : Fin 2))).ι).obj standardLineBundle.sheaf ≅
      SheafOfModules.unit
        (standardCover.chart (ULift.up (0 : Fin 2))).toScheme.ringCatSheaf)
    (trivial_on_infinity_chart :
      (Scheme.Modules.pullback
        (standardCover.chart (ULift.up (1 : Fin 2))).ι).obj standardLineBundle.sheaf ≅
      SheafOfModules.unit
        (standardCover.chart (ULift.up (1 : Fin 2))).toScheme.ringCatSheaf) :
    (Γ(LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04ProjectiveLine K,
      standardCover.chart (ULift.up (0 : Fin 2)) ⊓
        standardCover.chart (ULift.up (1 : Fin 2))))ˣ := by
  sorry

structure Chapter09ProjectiveLineDegreeOneTransitionData
    (K : Type u) [Field K] where
  standardLineBundle :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04LineBundle
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04ProjectiveLine K)
  isStandardDegreeOne :
    standardLineBundle =
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04ProjectiveLineTautologicalLineBundle K
  standardCover :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02StandardAffineCover
      (AlgebraicGeometry.Spec (.of K))
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02ProjectiveSpaceIndex 1)
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02ProjectiveSpaceData
        (AlgebraicGeometry.Spec (.of K))
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02ProjectiveSpaceIndex 1)
      )
  trivial_on_zero_chart :
    (Scheme.Modules.pullback
      (standardCover.chart (ULift.up (0 : Fin 2))).ι).obj standardLineBundle.sheaf ≅
      SheafOfModules.unit
        (standardCover.chart (ULift.up (0 : Fin 2))).toScheme.ringCatSheaf
  trivial_on_infinity_chart :
    (Scheme.Modules.pullback
      (standardCover.chart (ULift.up (1 : Fin 2))).ι).obj standardLineBundle.sheaf ≅
      SheafOfModules.unit
        (standardCover.chart (ULift.up (1 : Fin 2))).toScheme.ringCatSheaf
  transition :
    (Γ(LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04ProjectiveLine K,
      standardCover.chart (ULift.up (0 : Fin 2)) ⊓
        standardCover.chart (ULift.up (1 : Fin 2))))ˣ
  transition_extracted_from_trivializations :
    transition = chapter09ProjectiveLineTransitionExtractor K standardLineBundle standardCover
      trivial_on_zero_chart trivial_on_infinity_chart
  transition_is_coordinate :
    transition = chapter09ProjectiveLineCoordinate K standardCover
  nontrivial_cocycle :
    ¬ chapter09ProjectiveTransitionGaugeTrivial
      (standardCover.chart (ULift.up (0 : Fin 2)))
      (standardCover.chart (ULift.up (1 : Fin 2))) transition

def chapter09ProjectiveLineDegreeOneTransitionExample (K : Type u) [Field K] : Prop :=
  Nonempty (Chapter09ProjectiveLineDegreeOneTransitionData K)

theorem chapter09_projective_line_degree_one_transition_exists
    (K : Type u) [Field K] :
    chapter09ProjectiveLineDegreeOneTransitionExample K := by
  sorry

end
end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09
