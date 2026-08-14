import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.MvPolynomial
import Mathlib.RingTheory.Polynomial.Quotient
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Section03DivisorsOnSmoothRelativeCurves
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section05SymmetricPowersAndBaseChange
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section01TheAbsoluteAndRelativeSettings

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
open RelativeScheme
open scoped BigOperators Polynomial

universe u v

/-!
Shared interfaces for Chapter 6.

The finite-flat and Cartier predicates are the canonical Book 8 predicates.
The records below only package the relative test-scheme notation needed by
the present chapter, so that the statements about Hilbert points and Cartier
points have the same domain and codomain.
-/

abbrev Chapter06ClosedSubscheme (X : Scheme) := X.IdealSheafData

abbrev Chapter06FiniteFlatRank {X Y : Scheme} (q : X ⟶ Y) (d : ℕ) : Prop :=
  Chapter11FiniteLocallyFreeOfRank q d

abbrev Chapter06FiniteFlatMorphism {X Y : Scheme} (q : X ⟶ Y) : Prop :=
  IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q

abbrev Chapter06RelativeEffectiveDivisor {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) :=
  RelativeEffectiveCartierDivisor C T d

abbrev Chapter06RelativeDivisorAmbient {S : Scheme.{u}}
    (C T : RelativeScheme S) : Scheme.{u} :=
  pullback C.structuralMap T.structuralMap

abbrev Chapter06RelativeDivisorSubscheme {S : Scheme.{u}}
    {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) : Scheme.{u} :=
  D.divisor.subscheme

abbrev Chapter06RelativeDivisorInclusion {S : Scheme.{u}}
    {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06RelativeDivisorSubscheme D ⟶ Chapter06RelativeDivisorAmbient C T :=
  D.divisor.inclusion

def chapter06RelativeDivisorProjection {S : Scheme.{u}}
    {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06RelativeDivisorSubscheme D ⟶ T.carrier :=
  D.divisor.inclusion ≫ pullback.snd C.structuralMap T.structuralMap

noncomputable def chapter06RelativeDivisorBaseChangeAmbientMap
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T) :
    Chapter06RelativeDivisorAmbient C U ⟶ Chapter06RelativeDivisorAmbient C T := by
  refine pullback.lift
    (pullback.fst C.structuralMap U.structuralMap)
    (pullback.snd C.structuralMap U.structuralMap ≫ u.hom) ?_
  simpa [Category.assoc, u.comm] using
    (pullback.condition (f := C.structuralMap) (g := U.structuralMap))

theorem chapter06_relative_divisor_base_change_ambient_map_comp
    {S : Scheme.{u}} (C T U V : RelativeScheme S)
    (u : U ⟶ T) (v : V ⟶ U) :
    chapter06RelativeDivisorBaseChangeAmbientMap C U V v ≫
        chapter06RelativeDivisorBaseChangeAmbientMap C T U u =
      chapter06RelativeDivisorBaseChangeAmbientMap C T V (v ≫ u) := by
  apply (IsPullback.of_hasPullback C.structuralMap T.structuralMap).hom_ext
  · simp only [Category.assoc, chapter06RelativeDivisorBaseChangeAmbientMap,
      pullback.lift_fst]
  · simp only [chapter06RelativeDivisorBaseChangeAmbientMap]
    rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    rw [pullback.lift_snd_assoc]
    rfl

theorem chapter06_relative_divisor_base_change_ambient_map_id
    {S : Scheme.{u}} (C T : RelativeScheme S) :
    chapter06RelativeDivisorBaseChangeAmbientMap C T T (𝟙 T) =
      𝟙 (Chapter06RelativeDivisorAmbient C T) := by
  apply (IsPullback.of_hasPullback C.structuralMap T.structuralMap).hom_ext
  · simp only [chapter06RelativeDivisorBaseChangeAmbientMap,
      pullback.lift_fst, Category.id_comp]
  · dsimp [chapter06RelativeDivisorBaseChangeAmbientMap]
    rw [pullback.lift_snd]
    change pullback.snd C.structuralMap T.structuralMap ≫ 𝟙 T.carrier = _
    simp

theorem chapter06_relativeEffectiveDivisor_rank
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) (t : T.carrier) :
    Scheme.Hom.finrank (chapter06RelativeDivisorProjection D) t = d := by
  exact D.finite_flat_rank.2.2.2 t

theorem chapter06_finiteFlatMorphism_rank_is_locally_constant
    {X Y : Scheme.{u}} {q : X ⟶ Y}
    (h : Chapter06FiniteFlatMorphism q) :
    IsLocallyConstant (Scheme.Hom.finrank q) := by
  exact @Scheme.Hom.isLocallyConstant_finrank _ _ q h.2.1 h.1 h.2.2

theorem chapter06_finiteFlatRank_is_locally_constant
    {X Y : Scheme.{u}} {q : X ⟶ Y} {d : ℕ}
    (h : Chapter06FiniteFlatRank q d) :
    IsLocallyConstant (Scheme.Hom.finrank q) := by
  exact chapter06_finiteFlatMorphism_rank_is_locally_constant
    ⟨h.1, h.2.1, h.2.2.1⟩

theorem chapter06_finiteFlatMorphism_rank_constant_on_connected_base
    {X Y : Scheme.{u}} {q : X ⟶ Y}
    (h : Chapter06FiniteFlatMorphism q)
    (hconnected : _root_.IsConnected (Set.univ : Set Y)) :
    ∀ y z : Y, Scheme.Hom.finrank q y = Scheme.Hom.finrank q z := by
  intro y z
  exact (chapter06_finiteFlatMorphism_rank_is_locally_constant h).apply_eq_of_isPreconnected
    hconnected.isPreconnected trivial trivial

/- The length family is deliberately recorded before Cartierness.  This is
the Hilbert-side object to which the smooth-curve theorem adds one equation. -/
structure Chapter06FiniteFlatClosedFamily {S : Scheme.{u}}
    (C T : RelativeScheme S) (d : ℕ) where
  ideal : (Chapter06RelativeDivisorAmbient C T).IdealSheafData
  finite_flat_rank :
    Chapter06FiniteFlatRank
      (ideal.subschemeι ≫ pullback.snd C.structuralMap T.structuralMap) d

/-!
The Chapter 10 smooth-curve theorem uses its own bundled profile.  The
Chapter 11 rank predicate is propositionally the same four-part package, so
these conversions keep the proof route through that canonical theorem
explicit rather than relying on a hidden coercion.
-/
def chapter06FiniteFlatClosedFamilyAsChapter10Family
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    Chapter10FamilyOfLength C.structuralMap T.structuralMap d :=
  ⟨Z.ideal,
    { finite := Z.finite_flat_rank.1
      flat := Z.finite_flat_rank.2.1
      locallyOfFinitePresentation := Z.finite_flat_rank.2.2.1
      rank := Z.finite_flat_rank.2.2.2 }⟩

def chapter06Chapter10FamilyAsFiniteFlatClosedFamily
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (Z : Chapter10FamilyOfLength C.structuralMap T.structuralMap d) :
    Chapter06FiniteFlatClosedFamily C T d :=
  { ideal := Z.1
    finite_flat_rank :=
      ⟨Z.2.finite, Z.2.flat, Z.2.locallyOfFinitePresentation, Z.2.rank⟩ }

@[simp]
theorem chapter06FiniteFlatClosedFamilyAsChapter10Family_ideal
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    (chapter06FiniteFlatClosedFamilyAsChapter10Family C T d Z).1 = Z.ideal :=
  rfl

@[simp]
theorem chapter06Chapter10FamilyAsFiniteFlatClosedFamily_ideal
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ)
    (Z : Chapter10FamilyOfLength C.structuralMap T.structuralMap d) :
    (chapter06Chapter10FamilyAsFiniteFlatClosedFamily C T d Z).ideal = Z.1 :=
  rfl

noncomputable def chapter06FiniteFlatClosedFamilyBaseChange
    {S : Scheme.{u}} (C T U : RelativeScheme S) (u : U ⟶ T)
    (d : ℕ) (Z : Chapter06FiniteFlatClosedFamily C T d) :
    Chapter06FiniteFlatClosedFamily C U d := by
  refine
    { ideal := Z.ideal.comap (chapter06RelativeDivisorBaseChangeAmbientMap C T U u)
      finite_flat_rank := by sorry }

abbrev Chapter06FiniteFlatClosedFamily.subscheme
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) : Scheme.{u} :=
  Z.ideal.subscheme

def chapter06FiniteFlatClosedFamilyProjection
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) :
    Z.subscheme ⟶ T.carrier :=
  Z.ideal.subschemeι ≫ pullback.snd C.structuralMap T.structuralMap

theorem chapter06_finiteFlatClosedFamily_rank
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) (t : T.carrier) :
    Scheme.Hom.finrank (chapter06FiniteFlatClosedFamilyProjection Z) t = d := by
  exact Z.finite_flat_rank.2.2.2 t

@[ext]
theorem chapter06FiniteFlatClosedFamily_ext
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z W : Chapter06FiniteFlatClosedFamily C T d)
    (h : Z.ideal = W.ideal) : Z = W := by
  cases Z
  cases W
  cases h
  rfl

def chapter06IsEffectiveCartierFamily
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (Z : Chapter06FiniteFlatClosedFamily C T d) : Prop :=
  Z.ideal.IsEffectiveCartier

/-!
The source uses "smooth projective relative curve".  Book 8's symmetric
power API consumes the canonical quasi-projective/smooth class; projectivity
is retained as an additional field rather than weakened in the Chapter 6
statement.
-/
class Chapter06SmoothProjectiveRelativeCurve {S : Scheme.{u}}
    (C : RelativeScheme S)
    extends Chapter11SmoothQuasiProjectiveCurve C where
  projective :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09ProjectiveMorphism
      C.structuralMap

instance chapter06SmoothProjectiveRelativeCurve_to_chapter10
    {S : Scheme.{u}} {C : RelativeScheme S}
    [Chapter06SmoothProjectiveRelativeCurve C] :
    Chapter10SmoothRelativeCurve C.structuralMap :=
  Chapter11SmoothQuasiProjectiveCurve.smooth (C := C)

/-!
The pinned Book 8 API exposes the Cartier line-bundle construction through
an explicit local interface.  Fiberwise degree is kept as a separate
line-bundle interface, while the conditional ideal-dual and section
interfaces remain the bridge to the earlier divisor/Picard chapters.
-/

abbrev Chapter06LineBundle (X : Scheme.{u}) := Chapter10LineBundle X

abbrev Chapter06LineBundleSection {X : Scheme.{u}}
    (L : Chapter06LineBundle X) := Chapter10LineBundleSection L

/-!
Book 8 has two effective-Cartier predicates: the Chapter 11 ideal-sheaf
predicate used by `RelativeEffectiveCartierDivisor`, and the Chapter 10
locally-regular-principal predicate consumed by the line-bundle interface.
This one-way bridge is the conversion needed by the associated-line-bundle
construction below.
-/
theorem chapter06_effective_cartier_is_locally_regular_principal
    {X : Scheme.{u}} (I : Chapter06ClosedSubscheme X)
    (hI : I.IsEffectiveCartier) : Chapter10LocallyRegularPrincipal I := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUtop⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let U' : X.affineOpens := ⟨U, hU⟩
  rcases hI U' ⟨x, hxU⟩ with ⟨V, f, hxV, hVU, hIdeal, hf⟩
  refine ⟨V, hxV, f, hIdeal, ?_⟩
  exact isRegular_iff_mem_nonZeroDivisors.mpr hf

def chapter06AsChapter10EffectiveCartierDivisor
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter10EffectiveCartierDivisor (Chapter06RelativeDivisorAmbient C T) :=
  { ideal := D.divisor.ideal
    locallyRegularPrincipal :=
      chapter06_effective_cartier_is_locally_regular_principal
        D.divisor.ideal D.divisor.isEffectiveCartier
    closed := by infer_instance }

class Chapter06LineBundleFiberwiseDegreeAPI {S : Scheme.{u}}
    (C T : RelativeScheme S) where
  degree :
    Chapter06LineBundle (Chapter06RelativeDivisorAmbient C T) →
      T.carrier → ℤ
  degree_respects_isomorphism :
    ∀ {L M : Chapter06LineBundle (Chapter06RelativeDivisorAmbient C T)}
      (_e : Nonempty (Chapter10LineBundleIso L M)) (t : T.carrier),
      degree L t = degree M t
  degree_of_associated_divisor :
    ∀ [Chapter10IdealDualAPI (Chapter06RelativeDivisorAmbient C T)]
      {d : ℕ} (D : Chapter06RelativeEffectiveDivisor C T d) (t : T.carrier),
      degree (chapter10OofD (chapter06AsChapter10EffectiveCartierDivisor D)) t =
        (d : ℤ)

theorem chapter06_line_bundle_degree_of_associated_divisor
    {S : Scheme.{u}} {C T : RelativeScheme S}
    [Chapter06LineBundleFiberwiseDegreeAPI C T]
    [Chapter10IdealDualAPI (Chapter06RelativeDivisorAmbient C T)]
    {d : ℕ} (D : Chapter06RelativeEffectiveDivisor C T d) (t : T.carrier) :
    Chapter06LineBundleFiberwiseDegreeAPI.degree
      (chapter10OofD (chapter06AsChapter10EffectiveCartierDivisor D)) t =
        (d : ℤ) :=
  Chapter06LineBundleFiberwiseDegreeAPI.degree_of_associated_divisor D t

def chapter06LineBundleFiberwiseDegree
    {S : Scheme.{u}} (C T : RelativeScheme S)
    [Chapter06LineBundleFiberwiseDegreeAPI C T]
    (L : Chapter06LineBundle (Chapter06RelativeDivisorAmbient C T))
    (t : T.carrier) : ℤ :=
  Chapter06LineBundleFiberwiseDegreeAPI.degree L t

def Chapter06LineBundleHasFiberwiseDegree
    {S : Scheme.{u}} (C T : RelativeScheme S)
    [Chapter06LineBundleFiberwiseDegreeAPI C T]
    (L : Chapter06LineBundle (Chapter06RelativeDivisorAmbient C T))
    (d : ℕ) : Prop :=
  ∀ t : T.carrier, chapter06LineBundleFiberwiseDegree C T L t = (d : ℤ)

abbrev chapter06AssociatedLineBundle
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    [Chapter10IdealDualAPI (Chapter06RelativeDivisorAmbient C T)]
    (D : Chapter06RelativeEffectiveDivisor C T d)
    :
    Chapter06LineBundle (Chapter06RelativeDivisorAmbient C T) :=
  chapter10OofD (chapter06AsChapter10EffectiveCartierDivisor D)

abbrev chapter06AssociatedLineBundleCanonicalSection
    {S : Scheme.{u}} {C T : RelativeScheme S} {d : ℕ}
    [Chapter10IdealDualAPI (Chapter06RelativeDivisorAmbient C T)]
    [Chapter10SectionVanishingIdealAPI (Chapter06RelativeDivisorAmbient C T)]
    (D : Chapter06RelativeEffectiveDivisor C T d) :
    Chapter06LineBundleSection (chapter06AssociatedLineBundle D) :=
  chapter10OofD_section (chapter06AsChapter10EffectiveCartierDivisor D)

/-!
The following two records describe the parameter-space language used in
§6.4 without choosing a second Hilbert-scheme implementation.  A Hilbert
space represents all finite-flat families; its Cartier locus is represented
by an open immersion and the displayed subtype.
-/

structure Chapter06LengthDHilbertSpaceData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ) where
  carrier : RelativeScheme S
  represents : ∀ T : RelativeScheme S,
    (T ⟶ carrier) ≃ Chapter06FiniteFlatClosedFamily C T d
  represents_natural : ∀ {T U : RelativeScheme S} (u : U ⟶ T)
    (f : T ⟶ carrier),
    chapter06FiniteFlatClosedFamilyBaseChange C T U u d (represents T f) =
      represents U (u ≫ f)

structure Chapter06CartierDivisorOpenLocusData {S : Scheme.{u}}
    (C : RelativeScheme S) (d : ℕ)
    (H : Chapter06LengthDHilbertSpaceData C d) where
  locus : RelativeScheme S
  inclusion : locus ⟶ H.carrier
  isOpen : IsOpenImmersion inclusion.hom
  represents : ∀ T : RelativeScheme S,
    (T ⟶ locus) ≃
      {Z : Chapter06FiniteFlatClosedFamily C T d //
        chapter06IsEffectiveCartierFamily Z}
  inclusion_compatibility : ∀ (T : RelativeScheme S) (f : T ⟶ locus),
    H.represents T (f ≫ inclusion) = (represents T f).1
  represents_natural : ∀ {T U : RelativeScheme S} (u : U ⟶ T)
    (f : T ⟶ locus),
    chapter06FiniteFlatClosedFamilyBaseChange C T U u d
        ((represents T f).1) =
      (represents U (u ≫ f)).1

/- The earlier standing-conventions chapter already supplies the genuine nodal
   relative-curve predicate, including properness, flatness, finite
   presentation, geometric purity, reduced fibers, and the ordinary-double-
   point condition.  Reuse it instead of storing unconstrained `Prop` labels. -/
abbrev Chapter06NodalRelativeCurveData {S : Scheme.{u}}
    (C : RelativeScheme S) :=
  Chapter01NodalRelativeCurve C.structuralMap

abbrev Chapter06NodalRelativeCurve {S : Scheme.{u}}
    (C : RelativeScheme S) : Prop :=
  Chapter06NodalRelativeCurveData C

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter06
