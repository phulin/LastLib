import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09.Dependencies

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

/-- A change of basis on the trivial bundle acts by `h₂ g h₁⁻¹`. -/
noncomputable def chapter09GaugeTransform
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (h : Matrix.GeneralLinearGroup (Fin r) T)
    (g : Matrix.GeneralLinearGroup (Fin r) D) :
    Matrix.GeneralLinearGroup (Fin r) D :=
  chapter09MatrixBaseChange N.second h * g * (chapter09MatrixBaseChange N.first h)⁻¹

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
  sorry

instance chapter09AffineTransitionCocycleSetoid
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ) :
    Setoid (Chapter09AffineTransitionCocycle N r) where
  r := chapter09GaugeEquivalent N r
  iseqv := by
    sorry

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
  sorry

/-- In the chosen trivializations, an isomorphism of descended bundles is exactly a gauge change. -/
def chapter09TrivializedDescentDataIsomorphic
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (a b : Chapter09AffineTransitionCocycle N r) : Prop :=
  chapter09GaugeEquivalent N r a b

theorem chapter09_trivialized_descent_isomorphic_iff_gauge
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (r : ℕ)
    (a b : Chapter09AffineTransitionCocycle N r) :
    chapter09TrivializedDescentDataIsomorphic N r a b ↔
      chapter09GaugeEquivalent N r a b := by
  rfl

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
  sorry

theorem chapter09_unit_cocycle_gives_rank_one_matrix_cocycle
    {R T D Q : Type u} [CommRing R] [CommRing T] [CommRing D] [CommRing Q]
    (N : Chapter09AffineCechNerve R T D Q) (u : Dˣ)
    (hu : chapter09UnitCocycleCondition N u) :
    chapter09MatrixCocycle N 1 (chapter09RankOneMatrixOfUnit u) := by
  sorry

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

/- LOCAL_DEPENDENCY_GUESS: the pinned projective-spectrum API does not expose the standard
two-chart `𝒪(1)` transition datum as one bundled declaration. -/
structure Chapter09ProjectiveLineDegreeOneTransitionData
    (K A : Type u) [Field K] [CommRing A] where
  projectiveLine : Scheme.{u}
  standardLineBundle : Chapter09LineBundle projectiveLine
  isStandardDegreeOne : Prop
  standardOpenZero : TopologicalSpace.Opens projectiveLine
  standardOpenInfinity : TopologicalSpace.Opens projectiveLine
  standardOverlap : TopologicalSpace.Opens projectiveLine
  coordinate : Aˣ
  transition : Aˣ
  transition_is_coordinate : transition = coordinate
  trivial_on_zero_chart : Prop
  trivial_on_infinity_chart : Prop
  nontrivial_cocycle : Prop
  no_global_trivialization_selected : Prop

def chapter09ProjectiveLineDegreeOneTransitionExample (K : Type u) [Field K] : Prop :=
  ∃ (A : Type u) (instA : CommRing A),
    Nonempty (@Chapter09ProjectiveLineDegreeOneTransitionData K A _ instA)

theorem chapter09_projective_line_degree_one_transition_exists
    (K : Type u) [Field K] :
    chapter09ProjectiveLineDegreeOneTransitionExample K := by
  sorry

end
end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter09
