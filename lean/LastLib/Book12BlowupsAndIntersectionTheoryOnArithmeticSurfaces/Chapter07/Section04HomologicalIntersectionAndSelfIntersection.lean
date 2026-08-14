import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length

import LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07.Dependencies

namespace LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07

open CategoryTheory

universe u v

/-!
This section records the homological formulation of local intersection
multiplicity.  The local Tor profile is kept explicit so that later chapters
can replace the profile by the canonical resolution APIs when those APIs are
available for the relevant module category.
-/

/-- The canonical Tor bifunctor in an abelian monoidal category with projective
resolutions. -/
abbrev Chapter07CanonicalTor
    (C : Type u) [Category C] [MonoidalCategory C] [Abelian C]
    [MonoidalPreadditive C] [HasProjectiveResolutions C] (j : ℕ) : C ⥤ C ⥤ C :=
  CategoryTheory.Tor C j

/-- A concrete presentation of the principal resolution used for a Cartier
equation.  The displayed maps are the usual multiplication and quotient maps. -/
structure Chapter07PrincipalIdealResolution (A : Type u) [CommRing A] (f : A) where
  multiply : A →ₗ[A] A
  quotient : A →ₗ[A] (A ⧸ Ideal.span ({f} : Set A))
  multiply_eq : multiply = LinearMap.mul A A f
  quotient_eq : quotient = Submodule.mkQ (Ideal.span ({f} : Set A))
  multiply_injective : Function.Injective multiply
  quotient_surjective : Function.Surjective quotient
  exact : Function.Exact multiply quotient

namespace Chapter07PrincipalIdealResolution

/-- Canonical construction of the principal resolution when `f` is regular. -/
def canonical {A : Type u} [CommRing A] {f : A}
    (hf : f ∈ nonZeroDivisors A) : Chapter07PrincipalIdealResolution A f :=
  { multiply := LinearMap.mul A A f
    quotient := Submodule.mkQ (Ideal.span ({f} : Set A))
    multiply_eq := rfl
    quotient_eq := rfl
    multiply_injective := by sorry
    quotient_surjective := by sorry
    exact := by sorry }

end Chapter07PrincipalIdealResolution

/-- The condition that multiplication by `f` is injective after quotienting by
the second Cartier equation `g`. -/
def Chapter07NonZeroDivisorModulo (A : Type u) [CommRing A] (f g : A) : Prop :=
  ∀ x : A ⧸ Ideal.span ({g} : Set A),
    Ideal.Quotient.mk (Ideal.span ({g} : Set A)) f * x = 0 → x = 0

/-- The first Tor term obtained from the principal resolution of `A/(f)`,
realized as the kernel of multiplication by `f` on `A/(g)`. -/
def Chapter07TorOneSubmodule (A : Type u) [CommRing A] (f g : A) :
    Submodule (A ⧸ Ideal.span ({g} : Set A)) (A ⧸ Ideal.span ({g} : Set A)) :=
  LinearMap.ker
    (LinearMap.mul (A ⧸ Ideal.span ({g} : Set A))
      (A ⧸ Ideal.span ({g} : Set A))
      (Ideal.Quotient.mk (Ideal.span ({g} : Set A)) f))

theorem chapter07_mem_tor_one_iff {A : Type u} [CommRing A] {f g : A}
    {x : A ⧸ Ideal.span ({g} : Set A)} :
    x ∈ Chapter07TorOneSubmodule A f g ↔
      Ideal.Quotient.mk (Ideal.span ({g} : Set A)) f * x = 0 := by
  rfl

/-- Vanishing of the first Tor term in the Cartier-curve calculation. -/
def Chapter07FirstTorVanishes (A : Type u) [CommRing A] (f g : A) : Prop :=
  Chapter07TorOneSubmodule A f g = ⊥

theorem chapter07_first_tor_vanishes_of_nonZeroDivisor_modulo
    {A : Type u} [CommRing A] {f g : A}
    (hfg : Chapter07NonZeroDivisorModulo A f g) :
    Chapter07FirstTorVanishes A f g := by
  sorry

/-- A finite local Tor-length profile.  On a regular surface the profile is
supported in degrees `0`, `1`, and `2`. -/
structure Chapter07LocalTorLengthProfile (A : Type u) [CommRing A] where
  torLength : ℕ → ℕ∞
  finite : ∀ j, torLength j ≠ ⊤
  vanishes_after_two : ∀ j, 2 < j → torLength j = 0

/-- The category of local module stalks over `A`. -/
abbrev Chapter07LocalModuleCategory (A : Type u) [CommRing A] := ModuleCat A

/-- The canonical Tor object for two local module stalks. -/
abbrev Chapter07CanonicalTorStalk
    {A : Type u} [CommRing A]
    [HasProjectiveResolutions (Chapter07LocalModuleCategory A)]
    (j : ℕ) (F G : Chapter07LocalModuleCategory A) :
    Chapter07LocalModuleCategory A :=
  ((Chapter07CanonicalTor (Chapter07LocalModuleCategory A) j).obj F).obj G

/-- The canonical extended-natural length of a local Tor stalk. -/
noncomputable def Chapter07CanonicalTorLength
    {A : Type u} [CommRing A]
    [HasProjectiveResolutions (Chapter07LocalModuleCategory A)]
    (j : ℕ) (F G : Chapter07LocalModuleCategory A) : ℕ∞ :=
  Module.length A (Chapter07CanonicalTorStalk j F G)

/-- Coherent local stalks together with the finite Tor-length profile used by
the Euler characteristic.  Over an affine local ring, `Module.Finite` is the
module-theoretic coherence condition. -/
structure Chapter07CoherentStalkPair
    (A : Type u) [CommRing A]
    [IsRegularLocalRing A]
    [HasProjectiveResolutions (Chapter07LocalModuleCategory A)] where
  surface : Chapter07IsTwoDimensionalRegularLocalRing A
  F : Chapter07LocalModuleCategory A
  G : Chapter07LocalModuleCategory A
  coherent_F : Module.Finite A F
  coherent_G : Module.Finite A G
  coherent_tor : ∀ j, Module.Finite A (Chapter07CanonicalTorStalk j F G)
  profile : Chapter07LocalTorLengthProfile A
  profile_eq_tor_length :
    ∀ j, profile.torLength j = Chapter07CanonicalTorLength j F G

namespace Chapter07LocalTorLengthProfile

instance instInhabited {A : Type u} [CommRing A] :
    Inhabited (Chapter07LocalTorLengthProfile A) where
  default :=
    { torLength := fun _ => 0
      finite := by intro j; simp
      vanishes_after_two := by intro j hj; rfl }

end Chapter07LocalTorLengthProfile

/-- The sign-corrected contribution of one finite-length Tor term. -/
def Chapter07AlternatingLengthTerm (j : ℕ) (n : ℕ∞) : ℤ :=
  if Even j then Int.ofNat n.toNat else -Int.ofNat n.toNat

/-- Euler characteristic of a local Tor profile.  The finite range is justified
by `vanishes_after_two`, and is the concrete form of the source's alternating
sum over all Tor degrees. -/
noncomputable def Chapter07LocalEulerCharacteristic
    {A : Type u} [CommRing A] (profile : Chapter07LocalTorLengthProfile A) : ℤ :=
  ∑ j in Finset.range 3,
    Chapter07AlternatingLengthTerm j (profile.torLength j)

theorem chapter07_euler_characteristic_is_finite_tor_sum
    {A : Type u} [CommRing A] (profile : Chapter07LocalTorLengthProfile A) :
    Chapter07LocalEulerCharacteristic profile =
      ∑ j in Finset.range 3,
        Chapter07AlternatingLengthTerm j (profile.torLength j) := by
  rfl

/-!
The following interface packages the two nonzero terms in the principal
resolution calculation.  It is intentionally independent of a particular
sheaf presentation, so later chapters can feed it local stalks of coherent
sheaves.
-/

structure Chapter07ProperCartierTorProfile
    (A : Type u) [CommRing A]
    [IsRegularLocalRing A]
    (C D : Chapter07LocalEffectiveCartierCurve A) where
  surface : Chapter07IsTwoDimensionalRegularLocalRing A
  proper : Chapter07ProperIntersectionAt C D
  profile : Chapter07LocalTorLengthProfile A
  tor_zero_length : profile.torLength 0 =
    Chapter07LocalIntersectionMultiplicity C D
  tor_one_zero : profile.torLength 1 = 0
  tor_two_zero : profile.torLength 2 = 0

theorem chapter07_euler_characteristic_of_proper_cartier_profile
    {A : Type u} [CommRing A]
    [IsRegularLocalRing A]
    {C D : Chapter07LocalEffectiveCartierCurve A}
    (data : Chapter07ProperCartierTorProfile A C D) :
    Chapter07LocalEulerCharacteristic data.profile =
      Int.ofNat (data.profile.torLength 0).toNat := by
  sorry

theorem chapter07_euler_characteristic_of_proper_cartier_pair
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    {C D : Chapter07LocalEffectiveCartierCurve A}
    (data : Chapter07ProperCartierTorProfile A C D) :
    Chapter07LocalEulerCharacteristic data.profile =
      Int.ofNat
        (Chapter07LocalIntersectionMultiplicity C D).toNat := by
  sorry

/-- A local intersection number presented through the Euler characteristic of
the Tor profile of two coherent stalks. -/
def Chapter07CoherentLocalIntersection
    {A : Type u} [CommRing A]
    [IsRegularLocalRing A]
    [HasProjectiveResolutions (Chapter07LocalModuleCategory A)]
    (data : Chapter07CoherentStalkPair A) : ℤ :=
  Chapter07LocalEulerCharacteristic data.profile

theorem chapter07_coherent_local_intersection_eq_euler
    {A : Type u} [CommRing A]
    [IsRegularLocalRing A]
    [HasProjectiveResolutions (Chapter07LocalModuleCategory A)]
    (data : Chapter07CoherentStalkPair A) :
    Chapter07CoherentLocalIntersection data =
      Chapter07LocalEulerCharacteristic data.profile := by
  rfl

/-- A common one-dimensional component makes the tensor product have
infinite local length, so the elementary finite-length formula is not the
appropriate invariant. -/
theorem chapter07_common_component_gives_infinite_length
    {A : Type u} [CommRing A] [IsRegularLocalRing A]
    (hA : Chapter07IsTwoDimensionalRegularLocalRing A)
    {C D : Chapter07LocalEffectiveCartierCurve A}
    (hcommon : ¬ Chapter07NoCommonCurveComponentAt C D) :
    Chapter07LocalIntersectionMultiplicity C D = ⊤ := by
  sorry

/-- A self-intersection is recorded through a normal-line-bundle degree or
through a rational-equivalence move, rather than by the improper tensor
product length. -/
/- LOCAL_DEPENDENCY_GUESS: the global divisor/normal-bundle chapters should
replace this small witness interface by their canonical self-intersection API. -/
inductive Chapter07SelfIntersectionMethod
  | normalLineBundle
  | rationalEquivalenceMove

structure Chapter07SelfIntersectionWitness (A : Type u) where
  method : Chapter07SelfIntersectionMethod
  value : ℤ

def Chapter07SelfIntersectionValue {A : Type u}
    (witness : Chapter07SelfIntersectionWitness A) : ℤ :=
  witness.value

theorem chapter07_self_intersection_value_is_recorded
    {A : Type u} (witness : Chapter07SelfIntersectionWitness A) :
    Chapter07SelfIntersectionValue witness = witness.value := by
  rfl

end LastLib.Book12BlowupsAndIntersectionTheoryOnArithmeticSurfaces.Chapter07
