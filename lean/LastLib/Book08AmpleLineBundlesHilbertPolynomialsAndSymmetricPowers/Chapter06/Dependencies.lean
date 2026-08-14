import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Flat.Basic
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.Section01ProjectiveGeometryOverABase
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Section01ProjectiveBundles

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry BigOperators

universe u v

/-!
Shared interfaces for Chapter 6.

The pinned Mathlib snapshot supplies schemes, sheaves of modules, pushforward, affine-open
geometry, and internally graded `Proj`.  It does not yet expose the book-level derived global
sections, coherent cohomology, relative ampleness, or regularity packages.  The records below keep
those missing constructions explicit so that the section statements do not silently identify a
book notion with a merely similar Mathlib notion.  Chapters 1--5 are expected to provide the
canonical realizations of the projective-space and twisting records in the global fixup pass.
-/

abbrev Chapter06Scheme := AlgebraicGeometry.Scheme.{u}

abbrev Chapter06Sheaf (X : Chapter06Scheme) := X.Modules

abbrev chapter06AffineBaseRing (S : Chapter06Scheme) (U : S.Opens) := (Γ(S, U) : Type u)

/-- The rank-one locally free condition supplied by the projective-geometry chapter. -/
abbrev chapter06IsLineBundle {X : Chapter06Scheme} (L : X.Modules) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter01.Chapter01IsLineBundle L

/- `DEPENDENCY_GUESS`: the book's coherent-sheaf hypothesis is the standard finite-type,
quasi-coherent condition.  On locally Noetherian schemes it agrees with finite presentation, but
the weaker formulation is the one used by the source statements. -/
abbrev Chapter06Coherent {X : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04FiniteTypeQuasiCoherent F

theorem chapter06_coherent_iff_quasicoherent_and_finite_type
    {X : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) :
    Chapter06Coherent F ↔ F.IsQuasicoherent ∧ F.IsFiniteType :=
  Iff.rfl

/-- Global generation by a family of sections, in Mathlib's sheaf-of-modules interface. -/
def chapter06GloballyGenerated {X : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) : Prop :=
  Nonempty F.GeneratingSections

/-- Global generation by finitely many sections. -/
def chapter06FinitelyGloballyGenerated {X : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) : Prop :=
  ∃ σ : F.GeneratingSections, Finite σ.I

theorem chapter06_finitely_globally_generated_iff
    {X : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) :
    chapter06FinitelyGloballyGenerated F ↔
      ∃ σ : F.GeneratingSections, Finite σ.I :=
  Iff.rfl

theorem chapter06_finitely_globally_generated_implies_globally_generated
    {X : AlgebraicGeometry.Scheme.{u}} (F : X.Modules)
    (hF : chapter06FinitelyGloballyGenerated F) :
    chapter06GloballyGenerated F := by
  rcases hF with ⟨σ, _⟩
  exact ⟨σ⟩

/- `DEPENDENCY_GUESS`: the preceding chapters should replace this record by the canonical tensor
twist with a line bundle, including its unit, associativity, and pullback compatibilities.  The
structure sheaf is fixed here rather than supplied as unrelated data, since `𝒪_X` is part of the
meaning of a twist. -/
/- The preceding chapter already supplies the pinned presheaf-tensor/sheafification construction;
this name keeps the Chapter 6 statements independent of its namespace. -/
noncomputable def chapter06Tensor
    {X : Chapter06Scheme} (M N : X.Modules) : X.Modules :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04Tensor M N

structure Chapter06TwistSystem (X : Chapter06Scheme) where
  /-- Tensoring by the indicated integral twist. -/
  twist : X.Modules → ℤ → X.Modules
  /-- The twist is functorial in the sheaf. -/
  twist_map : ∀ {F G : X.Modules}, (F ⟶ G) → ∀ n : ℤ,
    twist F n ⟶ twist G n
  twist_map_id : ∀ (F : X.Modules) (n : ℤ),
    twist_map (𝟙 F) n = 𝟙 (twist F n)
  twist_map_comp : ∀ {F G H : X.Modules} (u : F ⟶ G) (v : G ⟶ H) (n : ℤ),
    twist_map (u ≫ v) n = twist_map u n ≫ twist_map v n
  /-- The degree-zero twist is canonically the original sheaf. -/
  twist_zero : ∀ F, Nonempty (twist F 0 ≅ F)
  /-- Twists add by tensoring with the corresponding power of the line bundle. -/
  twist_add : ∀ (F : X.Modules) (m n : ℤ),
    Nonempty (chapter06Tensor (twist F m)
      (twist (SheafOfModules.unit X.ringCatSheaf) n) ≅ twist F (m + n))
  /-- The degree-one twist is a line bundle. -/
  twist_one_isLineBundle :
    chapter06IsLineBundle (twist (SheafOfModules.unit X.ringCatSheaf) 1)
  /-- Tensoring by a twist preserves the coherent-sheaf class. -/
  twist_preserves_coherent :
    ∀ (F : X.Modules), Chapter06Coherent F → ∀ n : ℤ,
      Chapter06Coherent (twist F n)

noncomputable def Chapter06TwistSystem.structureSheaf
    (_T : Chapter06TwistSystem X) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

def chapter06Twist (T : Chapter06TwistSystem X) (F : X.Modules) (n : ℤ) : X.Modules :=
  T.twist F n

def chapter06TwistNat (T : Chapter06TwistSystem X) (F : X.Modules) (n : ℕ) : X.Modules :=
  T.twist F n

theorem chapter06_twist_nat_eq_twist_int
    (T : Chapter06TwistSystem X) (F : X.Modules) (n : ℕ) :
    chapter06TwistNat T F n = chapter06Twist T F n :=
  rfl

/- `DEPENDENCY_GUESS`: an additive-module valued model for the cohomology groups used in the
chapter.  The preceding chapters should supply derived global sections and their functoriality.

The coefficient ring is explicit: for projective space over `A` use `A`; for statements that only
need additive groups, use `ℤ`. -/
structure Chapter06CohomologyTheory (R : Type v) [Ring R] where
  H : ∀ {X : AlgebraicGeometry.Scheme.{u}}, X.Modules → ℕ → ModuleCat.{u} R
  /-- Cohomology is functorial in the coefficient sheaf. -/
  map : ∀ {X : AlgebraicGeometry.Scheme.{u}} {F G : X.Modules},
    (F ⟶ G) → ∀ i : ℕ, H F i ⟶ H G i
  map_id : ∀ {X : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (i : ℕ),
    map (𝟙 F) i = 𝟙 (H F i)
  map_comp : ∀ {X : AlgebraicGeometry.Scheme.{u}} {F G H' : X.Modules}
    (u : F ⟶ G) (v : G ⟶ H') (i : ℕ),
    map (u ≫ v) i = map u i ≫ map v i
  eulerCharacteristic : ∀ {X : AlgebraicGeometry.Scheme.{u}}, X.Modules → ℚ
  /-- Cohomology and Euler characteristic are invariant under an isomorphism of sheaves. -/
  mapIso : ∀ {X : AlgebraicGeometry.Scheme.{u}} {F G : X.Modules} (_e : F ≅ G) (i : ℕ),
    Nonempty (H F i ≅ H G i)
  eulerCharacteristic_congr : ∀ {X : AlgebraicGeometry.Scheme.{u}} {F G : X.Modules},
    (F ≅ G) → eulerCharacteristic F = eulerCharacteristic G
  /-- Cohomology is unchanged by pushforward along a closed immersion. -/
  closedImmersionIso :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
      (F : X.Modules) (j : ℕ),
      Nonempty (H ((Scheme.Modules.pushforward i).obj F) j ≅ H F j)

def chapter06Cohomology {R : Type v} [Ring R]
    (C : Chapter06CohomologyTheory R) {X : Chapter06Scheme} (F : X.Modules) (i : ℕ) :
    ModuleCat.{u} R :=
  C.H F i

def chapter06CohomologyIsZero {R : Type v} [Ring R]
    (C : Chapter06CohomologyTheory R) {X : Chapter06Scheme} (F : X.Modules) (i : ℕ) : Prop :=
  ∀ x : C.H F i, x = 0

theorem chapter06_cohomology_is_zero_iff_subsingleton {R : Type v} [Ring R]
    (C : Chapter06CohomologyTheory R) {X : Chapter06Scheme} (F : X.Modules) (i : ℕ) :
    chapter06CohomologyIsZero C F i ↔ Subsingleton (C.H F i) := by
  sorry

def chapter06EulerCharacteristic {R : Type v} [Ring R]
    (C : Chapter06CohomologyTheory R) {X : Chapter06Scheme} (F : X.Modules) : ℚ :=
  C.eulerCharacteristic F

/-- A standard projective space package over an arbitrary commutative ring.

`standardOpen_isAffine`, `standardOpen_cover`, and `standardOpen_intersection_isAffine` are the
chart-level data used by the Cech calculation.  The underlying relative projective bundle is the
canonical Chapter-2 package; only the missing twisting/cohomology compatibility remains abstract. -/
structure Chapter06ProjectiveSpaceData (A : Type u) [CommRing A] (r : ℕ) where
  /-- The canonical relative projective bundle over `Spec A` from Chapter 2. -/
  canonical :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02ProjectiveSpaceData
      (AlgebraicGeometry.Spec (CommRingCat.of A))
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02ProjectiveSpaceIndex r)
  twisting : Chapter06TwistSystem canonical.bundle.scheme
  /-- The chosen degree-one twist is the tautological line bundle of the canonical projective
  space. -/
  twisting_one_canonical :
    Nonempty (twisting.twist twisting.structureSheaf 1 ≅ canonical.bundle.twistingLineBundle.carrier)
  standardOpen : Fin (r + 1) → canonical.bundle.scheme.Opens
  standardOpen_isAffine : ∀ i, IsAffineOpen (standardOpen i)
  standardOpen_cover : ⨆ i, standardOpen i = ⊤
  /-- Nonempty finite intersections are the affine intersections used by Cech. -/
  standardOpen_intersection_isAffine : ∀ s : Finset (Fin (r + 1)), s.Nonempty →
    IsAffineOpen (s.inf standardOpen)
  /-- The chosen charts are the canonical coordinate charts, not an arbitrary affine cover. -/
  standardOpen_is_coordinate :
    ∀ i, (standardOpen i : Set canonical.bundle.scheme) =
      {x | LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.chapter02SectionGeneratesAt
        (canonical.coordinateSections (ULift.up i)) x}
  locallyNoetherian_of_noetherian_base :
    IsNoetherianRing A → IsLocallyNoetherian canonical.bundle.scheme

abbrev Chapter06ProjectiveSpaceData.X
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r) : Chapter06Scheme :=
  P.canonical.bundle.scheme

abbrev Chapter06ProjectiveSpaceData.toBase
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r) :
    P.X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A) :=
  P.canonical.bundle.projection

abbrev Chapter06ProjectiveSpace (A : Type u) [CommRing A] (r : ℕ) :=
  Chapter06ProjectiveSpaceData A r

theorem chapter06_projective_space_locally_noetherian
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r) (hA : IsNoetherianRing A) :
    IsLocallyNoetherian P.X :=
  P.locallyNoetherian_of_noetherian_base hA

def chapter06ProjectiveSpaceStructureSheaf
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r) : P.X.Modules :=
  P.twisting.structureSheaf

def chapter06ProjectiveSpaceTwist
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r) (F : P.X.Modules) (n : ℤ) : P.X.Modules :=
  P.twisting.twist F n

def chapter06ProjectiveSpaceTwistNat
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r) (F : P.X.Modules) (n : ℕ) : P.X.Modules :=
  P.twisting.twist F n

/-! ### Homogeneous polynomial pieces -/

def chapter06MonomialDegree (r n : ℕ) (e : Fin (r + 1) → Fin (n + 1)) : ℕ :=
  ∑ i, (e i : ℕ)

def Chapter06MonomialIndex (r n : ℕ) :=
  {e : Fin (r + 1) → Fin (n + 1) // chapter06MonomialDegree r n e = n}

noncomputable instance chapter06MonomialIndexFintype (r n : ℕ) :
    Fintype (Chapter06MonomialIndex r n) :=
  Fintype.subtype (Finset.univ.filter fun e => chapter06MonomialDegree r n e = n) (by sorry)

abbrev Chapter06PolynomialDegreePiece (A : Type u) (r n : ℕ) [AddCommMonoid A] :=
  Chapter06MonomialIndex r n →₀ A

def chapter06FreeModuleOfRank (R : Type u) [Ring R]
    (M : ModuleCat.{u} R) (q : ℕ) : Prop :=
  Nonempty (M ≅ ModuleCat.of R (Fin q →₀ R))

def chapter06ModuleSpans (R : Type u) [Ring R]
    (M : ModuleCat.{u} R) {ι : Type v} (g : ι → M) : Prop :=
  Submodule.span R (Set.range g) = ⊤

def chapter06NegativeLaurentMonomial (r : ℕ) (n : ℤ) : Type :=
  {e : Fin (r + 1) → ℤ // (∀ i, e i < 0) ∧ ∑ i, e i = n}

def chapter06ProjectiveCohomology {R : Type v} [Ring R]
    {A : Type u} [CommRing A] {r : ℕ}
    (C : Chapter06CohomologyTheory R)
    (P : Chapter06ProjectiveSpaceData A r) (F : P.X.Modules)
    (n : ℤ) (i : ℕ) : ModuleCat.{u} R :=
  C.H (P.twisting.twist F n) i

def chapter06ProjectiveEulerCharacteristic {R : Type v} [Ring R]
    {A : Type u} [CommRing A] {r : ℕ}
    (C : Chapter06CohomologyTheory R)
    (P : Chapter06ProjectiveSpaceData A r) (F : P.X.Modules) (n : ℤ) : ℚ :=
  C.eulerCharacteristic (P.twisting.twist F n)

def chapter06MRegular {R : Type v} [Ring R]
    {X : Chapter06Scheme}
    (C : Chapter06CohomologyTheory R)
    (T : Chapter06TwistSystem X) (F : X.Modules) (m : ℤ) : Prop :=
  ∀ i : ℕ, 0 < i →
    chapter06CohomologyIsZero C (T.twist F (m - i)) i

def chapter06HasHilbertPolynomial {R : Type v} [Ring R]
    {X : Chapter06Scheme}
    (C : Chapter06CohomologyTheory R)
    (T : Chapter06TwistSystem X) (F : X.Modules) (P : Polynomial ℚ) : Prop :=
  ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    C.eulerCharacteristic (T.twist F n) = P.eval (n : ℚ)

/- `DEPENDENCY_GUESS`: reuse the preceding coherent-ideal bundle until the sheaf-theoretic ideal
closure operation is available in the pinned API.  Its carrier is still tied to the structure
sheaf, rather than merely being an arbitrary subobject of an unrelated module. -/
def chapter06IdealSheaf {X : Chapter06Scheme} (F : X.Modules) : Prop :=
  ∃ I : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.Chapter04CoherentIdealSheaf X,
    I.carrier = F

def chapter06CechIntersection
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r) (s : Finset (Fin (r + 1))) : P.X.Opens :=
  s.inf P.standardOpen

theorem chapter06_projective_space_standard_open_cover
    {A : Type u} [CommRing A] {r : ℕ}
    (P : Chapter06ProjectiveSpaceData A r) :
    ⨆ i, P.standardOpen i = ⊤ :=
  P.standardOpen_cover

/-- A projective presentation of a morphism, used as the projectivity interface in 6.2--6.3.

The ambient object is deliberately a separate record: later fixup can replace this chart package
by the canonical projective bundle without changing the cohomological statements. -/
structure Chapter06ProjectiveSpaceOver (S : Chapter06Scheme) where
  /-- The finite locally free module whose relative Proj is the ambient projective bundle. -/
  module :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02QuasiCoherentModule S
  finiteLocallyFree :
    module.carrier.IsLocallyFree ∧ module.carrier.IsFiniteType
  canonical :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter02.Chapter02ProjectiveBundleData
      S module
  twisting : Chapter06TwistSystem canonical.scheme
  twisting_one_canonical :
    Nonempty (twisting.twist twisting.structureSheaf 1 ≅ canonical.twistingLineBundle.carrier)

abbrev Chapter06ProjectiveSpaceOver.X
    {S : Chapter06Scheme}
    (P : Chapter06ProjectiveSpaceOver S) : Chapter06Scheme :=
  P.canonical.scheme

abbrev Chapter06ProjectiveSpaceOver.toBase
    {S : Chapter06Scheme}
    (P : Chapter06ProjectiveSpaceOver S) : P.X ⟶ S :=
  P.canonical.projection

structure Chapter06ProjectivePresentation {X S : Chapter06Scheme} (f : X ⟶ S) where
  ambient : Chapter06ProjectiveSpaceOver S
  immersion : X ⟶ ambient.X
  closedImmersion : IsClosedImmersion immersion
  commutes : immersion ≫ ambient.toBase = f

def chapter06IsProjective {X S : Chapter06Scheme} (f : X ⟶ S) : Prop :=
  Nonempty (Chapter06ProjectivePresentation f)

theorem chapter06_is_projective_iff
    {X S : Chapter06Scheme} (f : X ⟶ S) :
    chapter06IsProjective f ↔ Nonempty (Chapter06ProjectivePresentation f) :=
  Iff.rfl

theorem chapter06_projective_presentation_locally_noetherian
    {X S : Chapter06Scheme} {f : X ⟶ S}
    (P : Chapter06ProjectivePresentation f) (hS : IsLocallyNoetherian S) :
    IsLocallyNoetherian X := by
  sorry

/-- The canonical sheaf pushforward already present in Mathlib. -/
def chapter06Pushforward {X Y : Chapter06Scheme} (f : X ⟶ Y) :
    X.Modules → Y.Modules :=
  (Scheme.Modules.pushforward f).obj

def chapter06PullbackSheaf {X Y : Chapter06Scheme} (f : X ⟶ Y) :
    Y.Modules → X.Modules :=
  (Scheme.Modules.pullback f).obj

def chapter06RestrictToOpen {X : Chapter06Scheme} (U : X.Opens) :
    X.Modules → U.toScheme.Modules :=
  (Scheme.Modules.pullback U.ι).obj

def chapter06CohomologyOnOpen {R : Type v} [Ring R]
    (C : Chapter06CohomologyTheory R) {X : Chapter06Scheme}
    (U : X.Opens) (F : X.Modules) (i : ℕ) : ModuleCat.{u} R :=
  C.H (chapter06RestrictToOpen U F) i

theorem chapter06_pushforward_apply {X Y : Chapter06Scheme} (f : X ⟶ Y)
    (F : X.Modules) :
    chapter06Pushforward f F = (Scheme.Modules.pushforward f).obj F :=
  rfl

structure Chapter06TwistCompatibility {X Y : Chapter06Scheme} (i : X ⟶ Y)
    (T_X : Chapter06TwistSystem X) (T_Y : Chapter06TwistSystem Y) where
  iso : ∀ (F : X.Modules) (n : ℤ),
    chapter06Pushforward i (T_X.twist F n) ≅ T_Y.twist (chapter06Pushforward i F) n

/-!
The following two records are intentionally data interfaces rather than aliases to arbitrary
`Prop`s.  Pinned Mathlib has the abelian sheaf category and ordinary pushforward, but not the
derived pushforward and base-change package required by the chapter. -/

/- `DEPENDENCY_GUESS`: a derived global-sections/pushforward construction is not in the pinned
Mathlib API, so the chapter temporarily receives it through this explicit theory. -/
structure Chapter06DerivedPushforwardTheory where
  derivedPushforward : ∀ {X Y : Chapter06Scheme} (_f : X ⟶ Y),
    X.Modules → ℕ → Y.Modules
  degreeZero : ∀ {X Y : Chapter06Scheme} (f : X ⟶ Y) (F : X.Modules),
    Nonempty (derivedPushforward f F 0 ≅ chapter06Pushforward f F)
  /-- The canonical pullback comparison morphism for derived direct images. -/
  baseChangeMap :
    ∀ {X S T : Chapter06Scheme} (f : X ⟶ S) (g : T ⟶ S)
      (F : X.Modules) (i : ℕ),
      (Scheme.Modules.pullback g).obj (derivedPushforward f F i) ⟶
        derivedPushforward (Limits.pullback.snd f g)
          ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F) i

def chapter06DerivedPushforward (D : Chapter06DerivedPushforwardTheory)
    {X Y : Chapter06Scheme} (f : X ⟶ Y) (F : X.Modules) (i : ℕ) : Y.Modules :=
  D.derivedPushforward f F i

theorem chapter06_derived_pushforward_degree_zero
    (D : Chapter06DerivedPushforwardTheory)
    {X Y : Chapter06Scheme} (f : X ⟶ Y) (F : X.Modules) :
    Nonempty (chapter06DerivedPushforward D f F 0 ≅ chapter06Pushforward f F) :=
  D.degreeZero f F

def chapter06BaseChangedSheaf {X S T : Chapter06Scheme}
    (f : X ⟶ S) (g : T ⟶ S) (F : X.Modules) :
    (Limits.pullback f g).Modules :=
  (Scheme.Modules.pullback (Limits.pullback.fst f g)).obj F

def chapter06PullbackDerivedPushforward (D : Chapter06DerivedPushforwardTheory)
    {X S T : Chapter06Scheme} (f : X ⟶ S) (g : T ⟶ S)
    (F : X.Modules) (i : ℕ) : T.Modules :=
  D.derivedPushforward (Limits.pullback.snd f g)
    (chapter06BaseChangedSheaf f g F) i

def chapter06DerivedPushforwardCommutesWithBaseChange
    (D : Chapter06DerivedPushforwardTheory)
    {X S : Chapter06Scheme} (f : X ⟶ S) (F : X.Modules) (i : ℕ) : Prop :=
  ∀ (T : Chapter06Scheme) (g : T ⟶ S),
    IsIso (D.baseChangeMap f g F i)

/- `DEPENDENCY_GUESS`: evaluation of a sheaf on the base at a residue-field point and the
residue-field cohomology theory still need the base-change layer from the preceding chapters. -/
structure Chapter06FiberTheory {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) where
  fiberOfSheaf : ∀ (s : S) (_G : S.Modules), ModuleCat.{u} (S.residueField s)
  fiberCohomologyTheory : ∀ s : S, Chapter06CohomologyTheory (S.residueField s)

def chapter06FiberSheaf {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (s : S) (F : X.Modules) : (f.fiber s).Modules :=
  (Scheme.Modules.pullback (f.fiberι s)).obj F

def chapter06FiberTwist {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (T : Chapter06TwistSystem X) (s : S)
    (F : X.Modules) (n : ℤ) : (f.fiber s).Modules :=
  (Scheme.Modules.pullback (f.fiberι s)).obj (T.twist F n)

def chapter06SheafFiber {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
    (B : Chapter06FiberTheory f) (s : S) (G : S.Modules) : ModuleCat.{u} (S.residueField s) :=
  B.fiberOfSheaf s G

def chapter06FiberCohomology {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
    (B : Chapter06FiberTheory f) (s : S) (G : (f.fiber s).Modules) (i : ℕ) :
    ModuleCat.{u} (S.residueField s) :=
  (B.fiberCohomologyTheory s).H G i

/-- A compact predicate for vanishing in all cohomological degrees above a bound. -/
def chapter06VanishingAbove {R : Type v} [Ring R]
    (C : Chapter06CohomologyTheory R) {X : Chapter06Scheme} (F : X.Modules) (N : ℕ) : Prop :=
  ∀ i : ℕ, N < i → chapter06CohomologyIsZero C F i

def chapter06LocallyFree {X : Chapter06Scheme} (F : X.Modules) : Prop :=
  F.IsLocallyFree ∧ F.IsFiniteType

def chapter06SheafIsZero {X : Chapter06Scheme} (F : X.Modules) : Prop :=
  Limits.IsZero F

def chapter06LocallyNoetherian (S : Chapter06Scheme) : Prop :=
  IsLocallyNoetherian S

def chapter06NoetherianRing (A : Type u) [CommRing A] : Prop :=
  IsNoetherianRing A

/-!
`DEPENDENCY_GUESS`: `Flat` for a sheaf over a scheme morphism is not packaged in the pinned sheaf
API.  The stalkwise class below is the intended bridge to the standard relative-flatness
definition; its field is kept explicit so later fixup can replace it by the canonical
local-flatness predicate and its induced base-stalk module structure.
-/
def chapter06StalkFlat {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
  (F : X.Modules) (x : X) : Prop :=
  letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) := by
    change Module (X.presheaf.stalk x)
      (↑(TopCat.Presheaf.stalk (C := Ab) F.val.presheaf x))
    exact PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  letI : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) (f.stalkMap x).hom
  Module.Flat (S.presheaf.stalk (f x)) (F.presheaf.stalk x)

class Chapter06FlatOver {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop where
  flatAtStalk : ∀ x : X, chapter06StalkFlat f F x

/- `DEPENDENCY_GUESS`: this is the smallest local bridge that records both a projective
presentation and a very-ample power of the chosen twist.  It should be replaced by the canonical
relative line-bundle/Proj interface when the preceding chapters are available. -/
class Chapter06RelativelyAmple {X S : Chapter06Scheme} (f : X ⟶ S)
    (T : Chapter06TwistSystem X) where
  projectivePresentation : Chapter06ProjectivePresentation f
  power : ℕ
  power_pos : 0 < power
  veryAmplePower :
    T.twist T.structureSheaf (power : ℤ) ≅
      chapter06PullbackSheaf projectivePresentation.immersion
        (projectivePresentation.ambient.twisting.twist
          projectivePresentation.ambient.twisting.structureSheaf 1)

/-- The integer-valued binomial polynomial used in the projective-space Euler characteristic. -/
def chapter06BinomialPolynomial (r : ℕ) : Polynomial ℚ :=
  (r.factorial : ℚ)⁻¹ •
    (∏ j ∈ Finset.range r, (Polynomial.X + Polynomial.C (j + 1 : ℚ)))

def chapter06BinomialPolynomialEval (r : ℕ) (n : ℤ) : ℚ :=
  (chapter06BinomialPolynomial r).eval (n : ℚ)

theorem chapter06_binomial_polynomial_eval_nat (r n : ℕ) :
    chapter06BinomialPolynomialEval r n = Nat.choose (n + r) r := by
  sorry

/- The Euler-characteristic calculation is stated separately because its coefficient ring is a
field in the source theorem. -/
end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter06
