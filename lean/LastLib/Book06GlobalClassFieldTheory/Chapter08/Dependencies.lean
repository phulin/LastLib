import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.RamificationInertia.HilbertTheory
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.Tactic.NormNum

namespace LastLib.Book06GlobalClassFieldTheory.Chapter08

noncomputable section

open scoped Classical
open scoped nonZeroDivisors

open scoped BigOperators
open NumberField

/-! ## Shared interfaces for §§8.1--8.5

The preceding global class-field chapters have not yet been assigned a Lean
implementation in this repository.  The structures below are deliberately
small interfaces for those missing declarations.  They retain the canonical
Mathlib types where they exist (number fields, integral ideals, Galois groups,
class groups, cyclotomic extensions, and Legendre symbols), while leaving only
the genuinely global idelic constructions abstract.
-/

universe u v w x y z

/-- A real infinite place, retaining the proof that the place is real. -/
abbrev Chapter08RealPlace (K : Type u) [Field K] :=
  {w : NumberField.InfinitePlace K // NumberField.InfinitePlace.IsReal w}

/-- The finite and infinite parts of a modulus. -/
structure Chapter08Modulus (K : Type u) [Field K] [NumberField K] where
  finitePart : Ideal (𝓞 K)
  infinitePart : Finset (Chapter08RealPlace K)

/-- Divisibility of the finite part together with inclusion of real places. -/
def chapter08ModulusDivides
    {K : Type u} [Field K] [NumberField K]
    (m₁ m₂ : Chapter08Modulus K) : Prop :=
  m₁.finitePart ∣ m₂.finitePart ∧
    ∀ w ∈ m₁.infinitePart, w ∈ m₂.infinitePart

@[refl] theorem chapter08_modulusDivides_refl
    {K : Type u} [Field K] [NumberField K]
    (m : Chapter08Modulus K) :
    chapter08ModulusDivides m m := by
  exact ⟨dvd_refl _, fun w hw => hw⟩

theorem chapter08_modulusDivides_trans
    {K : Type u} [Field K] [NumberField K]
    {m₁ m₂ m₃ : Chapter08Modulus K}
    (h₁₂ : chapter08ModulusDivides m₁ m₂)
    (h₂₃ : chapter08ModulusDivides m₂ m₃) :
    chapter08ModulusDivides m₁ m₃ := by
  exact ⟨dvd_trans h₁₂.1 h₂₃.1, fun w hw => h₂₃.2 w (h₁₂.2 w hw)⟩

/-- The ordinary (finite) trivial modulus. -/
def chapter08TrivialModulus
    (K : Type u) [Field K] [NumberField K] : Chapter08Modulus K where
  finitePart := ⊤
  infinitePart := ∅

/-- The ordinary ideal class group of a number field. -/
abbrev chapter08OrdinaryClassGroup
    (K : Type u) [Field K] [NumberField K] := ClassGroup (𝓞 K)

/-- The ordinary class number, through Mathlib's canonical definition. -/
noncomputable def chapter08ClassNumber
    (K : Type u) [Field K] [NumberField K] : ℕ :=
  NumberField.classNumber K

/-- The modulus containing every real place and no finite prime. -/
def chapter08NarrowModulus
    (K : Type u) [Field K] [NumberField K] : Chapter08Modulus K where
  finitePart := ⊤
  infinitePart := Finset.univ

/-- A finite prime is away from the finite part of a modulus. -/
def chapter08PrimeAwayFromModulus
    {K : Type u} [Field K] [NumberField K]
    (m : Chapter08Modulus K) (p : Ideal (𝓞 K)) : Prop :=
  p.IsPrime ∧ ¬p ∣ m.finitePart

/-- Positivity of an algebraic integer at a selected real place. -/
def chapter08PositiveAt
    {K : Type u} [Field K] [NumberField K]
    (w : Chapter08RealPlace K) (a : 𝓞 K) : Prop :=
  0 < (NumberField.InfinitePlace.embedding_of_isReal w.2)
    (algebraMap (𝓞 K) K a)

/-- The ideal-theoretic ray condition on a principal ideal. -/
def chapter08PrincipalRayCondition
    {K : Type u} [Field K] [NumberField K]
    (m : Chapter08Modulus K) (p : Ideal (𝓞 K)) (a : 𝓞 K) : Prop :=
  p = Ideal.span {a} ∧
    a - 1 ∈ m.finitePart ∧
    ∀ w ∈ m.infinitePart, chapter08PositiveAt w a

/-! The following presentation is the exact interface used by the ray-class
quotients.  `I` is the group of ideals prime to the finite modulus and `C` is
the idele class group. -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib has the ordinary ideal class group but not
the global ray-class/idele quotient used in this chapter.  This presentation
is the minimal reusable bridge: it exposes both quotient constructions and
the valuation representative of an ideal, without assuming any later class
field conclusion. -/
structure Chapter08RayClassPresentation
    (K : Type u) (I : Type v) (C : Type w) [Field K] [NumberField K]
    [CommGroup I] [CommGroup C] where
  modulus : Chapter08Modulus K
  principalSubgroup : Subgroup I
  unitsSubgroup : Subgroup C
  rayClassPresentation :
    (I ⧸ principalSubgroup) ≃* (C ⧸ unitsSubgroup)
  idealClass : Ideal (𝓞 K) → I
  idealClass_eq_one_iff :
    ∀ {p : Ideal (𝓞 K)}, chapter08PrimeAwayFromModulus modulus p →
      (QuotientGroup.mk' principalSubgroup (idealClass p) = 1 ↔
        ∃ a : 𝓞 K, chapter08PrincipalRayCondition modulus p a)

/-- The ray class group in the ideal presentation. -/
def chapter08RayClassGroup
    {K : Type u} {I : Type v} {C : Type w} [Field K] [NumberField K]
    [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C) : Type v :=
  I ⧸ R.principalSubgroup

instance chapter08RayClassGroupCommGroup
    {K : Type u} {I : Type v} {C : Type w} [Field K] [NumberField K]
    [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C) :
    CommGroup (chapter08RayClassGroup R) := by
  change CommGroup (I ⧸ R.principalSubgroup)
  infer_instance

/-- The quotient map from ideals to ray classes. -/
def chapter08RayClassQuotientMap
    {K : Type u} {I : Type v} {C : Type w} [Field K] [NumberField K]
    [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C) :
    I →* chapter08RayClassGroup R :=
  QuotientGroup.mk' R.principalSubgroup

/-- The ray class of an ideal in the chosen ideal presentation. -/
def chapter08RayClassOfIdeal
    {K : Type u} {I : Type v} {C : Type w} [Field K] [NumberField K]
    [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (p : Ideal (𝓞 K)) : chapter08RayClassGroup R :=
  chapter08RayClassQuotientMap R (R.idealClass p)

@[simp] theorem chapter08_rayClassOfIdeal_eq_quotient_mk
    {K : Type u} {I : Type v} {C : Type w} [Field K] [NumberField K]
    [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (p : Ideal (𝓞 K)) :
    chapter08RayClassOfIdeal R p =
      QuotientGroup.mk' R.principalSubgroup (R.idealClass p) := rfl

/-- A finite abelian extension together with its conductor modulus. -/
structure Chapter08AbelianExtensionData
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] where
  conductor : Chapter08Modulus K

def chapter08ConductorDivides
    {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (E : Chapter08AbelianExtensionData K L)
    (m : Chapter08Modulus K) : Prop :=
  chapter08ModulusDivides E.conductor m

/- LOCAL_DEPENDENCY_GUESS: global reciprocity supplies a surjective Artin map
on the idele class group.  The finite-prime representative and its arithmetic
Frobenius compatibility are kept as separate fields, so the ray factorization
below does not assume the desired splitting criterion. -/
structure Chapter08GlobalArtinData
    (K : Type u) (L : Type v) (I : Type w) (C : Type x) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L) where
  ideleArtin : C →* Gal(L / K)
  ideleArtin_surjective : Function.Surjective ideleArtin
  units_killed_of_conductor :
    chapter08ConductorDivides E R.modulus →
      R.unitsSubgroup ≤ ideleArtin.ker
  primeAway : Set (Ideal (𝓞 K))
  primeAway_spec :
    ∀ {p : Ideal (𝓞 K)}, p ∈ primeAway ↔
      chapter08PrimeAwayFromModulus R.modulus p
  ideleFiniteValuation : C → Ideal (𝓞 K)
  ideleTailIsOne : C → Prop
  ideleOfIdeal :
    ∀ {p : Ideal (𝓞 K)}, p ∈ primeAway → C
  ideleOfIdeal_finiteValuation :
    ∀ {p : Ideal (𝓞 K)} (hp : p ∈ primeAway),
      ideleFiniteValuation (ideleOfIdeal hp) = p
  ideleOfIdeal_tail_is_one :
    ∀ {p : Ideal (𝓞 K)} (hp : p ∈ primeAway),
      ideleTailIsOne (ideleOfIdeal hp)
  frobenius :
    ∀ {p : Ideal (𝓞 K)}, p ∈ primeAway → Gal(L / K)
  ideal_idele_compatibility :
    ∀ {p : Ideal (𝓞 K)} (hp : p ∈ primeAway),
      R.rayClassPresentation (chapter08RayClassOfIdeal R p) =
        QuotientGroup.mk' R.unitsSubgroup (ideleOfIdeal hp)
  arithmetic_frobenius_compatibility :
    ∀ {p : Ideal (𝓞 K)} (hp : p ∈ primeAway),
      ideleArtin (ideleOfIdeal hp) = frobenius hp

/-- The idele Artin map after killing the ray units. -/
def chapter08IdeleArtinFactor
    {K : Type u} {L : Type v} {I : Type w} {C : Type x} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus) :
    (C ⧸ R.unitsSubgroup) →* Gal(L / K) := by
  refine QuotientGroup.lift R.unitsSubgroup A.ideleArtin ?_
  intro c hc
  exact A.units_killed_of_conductor hcond hc

/-- The Artin map on the ideal group, obtained from the ray presentation. -/
def chapter08ArtinMap
    {K : Type u} {L : Type v} {I : Type w} {C : Type x} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus) :
    I →* Gal(L / K) :=
  (chapter08IdeleArtinFactor R E A hcond).comp
    (R.rayClassPresentation.toMonoidHom.comp
      (chapter08RayClassQuotientMap R))

/-- The Artin map factors through the ray class quotient. -/
def chapter08ArtinFactor
    {K : Type u} {L : Type v} {I : Type w} {C : Type x} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus) :
    chapter08RayClassGroup R →* Gal(L / K) :=
  (chapter08IdeleArtinFactor R E A hcond).comp
    R.rayClassPresentation.toMonoidHom

theorem chapter08_artin_map_surjective
    {K : Type u} {L : Type v} {I : Type w} {C : Type x} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus) :
    Function.Surjective (chapter08ArtinMap R E A hcond) := by
  sorry

theorem chapter08_artin_map_kernel_contains_principal
    {K : Type u} {L : Type v} {I : Type w} {C : Type x} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus) :
    R.principalSubgroup ≤ (chapter08ArtinMap R E A hcond).ker := by
  sorry

theorem chapter08_artin_factor_comp_quotientMap
    {K : Type u} {L : Type v} {I : Type w} {C : Type x} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus) :
    (chapter08ArtinFactor R E A hcond).comp (chapter08RayClassQuotientMap R) =
      chapter08ArtinMap R E A hcond := by
  rfl

theorem chapter08_artin_map_eq_arithmetic_frobenius
    {K : Type u} {L : Type v} {I : Type w} {C : Type x} [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C)
    (E : Chapter08AbelianExtensionData K L)
    (A : Chapter08GlobalArtinData K L I C R E)
    (hcond : chapter08ConductorDivides E R.modulus)
    {p : Ideal (𝓞 K)} (hp : p ∈ A.primeAway) :
    chapter08ArtinMap R E A hcond (R.idealClass p) = A.frobenius hp := by
  sorry

/-! ## Splitting and field-containment interfaces -/

/-- Complete splitting, expressed by `e=f=1` at every prime above `p`. -/
def chapter08SplitsCompletely
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)]
    (p : Ideal (𝓞 K)) [p.IsPrime] : Prop :=
  ∀ P : p.primesOver (𝓞 L),
    P.1.ramificationIdx (𝓞 K) = 1 ∧ P.1.inertiaDeg (𝓞 K) = 1

/-- Unramifiedness at every finite prime of the base. -/
def chapter08UnramifiedAtFinitePlaces
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)] : Prop :=
  ∀ p : Ideal (𝓞 K), p.IsPrime →
    Algebra.IsUnramifiedIn (𝓞 L) p

/-- Unramifiedness away from the finite part of a modulus. -/
def chapter08UnramifiedAwayFromFinitePart
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [Algebra (𝓞 K) (𝓞 L)]
    (m : Chapter08Modulus K) : Prop :=
  ∀ p : Ideal (𝓞 K), p.IsPrime → ¬p ∣ m.finitePart →
    Algebra.IsUnramifiedIn (𝓞 L) p

/-- Every real place of `K` remains real in `L`. -/
def chapter08RealPlacesStayReal
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop :=
  ∀ v : Chapter08RealPlace K,
    ∀ w ∈ NumberField.InfinitePlace.placesOver L v.1, w.IsReal

/-- Book-facing containment, represented by a `K`-algebra embedding. -/
def chapter08ExtensionContained
    (K : Type u) (L : Type v) (M : Type w) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] : Prop :=
  Nonempty (L →ₐ[K] M)

/- LOCAL_DEPENDENCY_GUESS: the subgroup-to-subextension part of global class
field theory is represented by the quotient Galois equivalence below.  It is
strictly weaker than the splitting criterion and is the natural input for the
subfield statement in §8.1. -/
structure Chapter08RaySubfieldData
    (K : Type u) (L : Type v) (I : Type w) (C : Type x) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C) where
  correspondingSubgroup : Subgroup (chapter08RayClassGroup R)
  quotientGaloisEquiv :
    (chapter08RayClassGroup R ⧸ correspondingSubgroup) ≃* Gal(L / K)

/- LOCAL_DEPENDENCY_GUESS: a ray class field is recorded by its finite
extension and the reciprocity equivalence; existence and maximality are
proved in the earlier global-existence chapter in the intended development. -/
structure Chapter08RayClassFieldData
    (K : Type u) [Field K] [NumberField K]
    {I : Type v} {C : Type w} [CommGroup I] [CommGroup C]
    (R : Chapter08RayClassPresentation K I C) where
  carrier : Type x
  [carrierField : Field carrier]
  [carrierAlgebra : Algebra K carrier]
  [carrierNumberField : NumberField carrier]
  [carrierFinite : FiniteDimensional K carrier]
  [carrierAbelianGalois : IsAbelianGalois K carrier]
  artinEquiv : chapter08RayClassGroup R ≃* Gal(carrier / K)
  maximal :
    ∀ (L : Type y) [Field L] [NumberField L] [Algebra K L]
      [Algebra (𝓞 K) (𝓞 L)] [FiniteDimensional K L] [IsAbelianGalois K L],
      (E : Chapter08AbelianExtensionData K L) →
      chapter08ConductorDivides E R.modulus →
      chapter08ExtensionContained K L carrier

/-! ## Hilbert and narrow Hilbert field interfaces -/

/- LOCAL_DEPENDENCY_GUESS: the existence theorem for the ordinary and narrow
Hilbert class fields is not in the pinned Mathlib tree.  These structures
package the canonical field, Galois, maximality, and class-group interfaces;
the section files only project or compare those fields. -/
structure Chapter08HilbertClassFieldData
    (K : Type u) [Field K] [NumberField K] where
  carrier : Type v
  [carrierField : Field carrier]
  [carrierAlgebra : Algebra K carrier]
  [carrierNumberField : NumberField carrier]
  [carrierFinite : FiniteDimensional K carrier]
  [carrierAbelianGalois : IsAbelianGalois K carrier]
  classGroupEquiv : ClassGroup (𝓞 K) ≃* Gal(carrier / K)
  unramifiedAtFinite : chapter08UnramifiedAtFinitePlaces K carrier
  realPlacesStayReal : chapter08RealPlacesStayReal K carrier
  maximal :
    ∀ (L : Type w) [Field L] [NumberField L] [Algebra K L]
      [Algebra (𝓞 K) (𝓞 L)] [FiniteDimensional K L] [IsAbelianGalois K L],
      chapter08UnramifiedAtFinitePlaces K L →
      chapter08RealPlacesStayReal K L →
      chapter08ExtensionContained K L carrier

abbrev chapter08HilbertClassField
    {K : Type u} [Field K] [NumberField K]
    (H : Chapter08HilbertClassFieldData K) : Type v :=
  H.carrier

abbrev Chapter08RealSignGroup
    (K : Type u) [Field K] :=
  Multiplicative (Chapter08RealPlace K → ZMod 2)

def chapter08RealQuadraticUnitSignPattern
    {K : Type u} [Field K] [NumberField K]
    (u : (𝓞 K)ˣ) (w : Chapter08RealPlace K) : ZMod 2 :=
  if 0 < (NumberField.InfinitePlace.embedding_of_isReal w.2)
      (algebraMap (𝓞 K) K (u : 𝓞 K)) then 0 else 1

def chapter08RealQuadraticSignMap
    (K : Type u) [Field K] [NumberField K] :
    (𝓞 K)ˣ → (Chapter08RealPlace K → ZMod 2) :=
  fun u w => chapter08RealQuadraticUnitSignPattern u w

def chapter08RealQuadraticSignMapSurjective
    (K : Type u) [Field K] [NumberField K] : Prop :=
  Function.Surjective (chapter08RealQuadraticSignMap K)

/- LOCAL_DEPENDENCY_GUESS: `Cl⁺(K)` is not a Mathlib declaration in the pinned
version.  The finite commutative carrier, the exact sign-kernel sequence, and
the forgetful map to `Cl(K)` are the natural interface for the
real-quadratic comparison. -/
structure Chapter08NarrowClassGroupData
    (K : Type u) [Field K] [NumberField K] where
  carrier : Type v
  [carrierCommGroup : CommGroup carrier]
  [carrierFintype : Fintype carrier]
  unitSign : (𝓞 K)ˣ →* Chapter08RealSignGroup K
  unitSign_spec :
    ∀ u, unitSign u = Multiplicative.ofAdd (chapter08RealQuadraticSignMap K u)
  forgetSigns : carrier →* ClassGroup (𝓞 K)
  forgetSigns_surjective : Function.Surjective forgetSigns
  kernelEquivSignQuotient :
    forgetSigns.ker ≃* (Chapter08RealSignGroup K ⧸ MonoidHom.range unitSign)

abbrev chapter08NarrowClassGroup
    {K : Type u} [Field K] [NumberField K]
    (N : Chapter08NarrowClassGroupData K) : Type v :=
  N.carrier

instance chapter08NarrowClassGroupCommGroup
    {K : Type u} [Field K] [NumberField K]
    (N : Chapter08NarrowClassGroupData K) :
    CommGroup (chapter08NarrowClassGroup N) := by
  change CommGroup N.carrier
  exact N.carrierCommGroup

/- LOCAL_DEPENDENCY_GUESS: this is the finite-unramified, possibly
complexifying analogue of `Chapter08HilbertClassFieldData`. -/
structure Chapter08NarrowHilbertClassFieldData
    (K : Type u) [Field K] [NumberField K]
    (N : Chapter08NarrowClassGroupData K) where
  carrier : Type v
  [carrierField : Field carrier]
  [carrierAlgebra : Algebra K carrier]
  [carrierNumberField : NumberField carrier]
  [carrierFinite : FiniteDimensional K carrier]
  [carrierAbelianGalois : IsAbelianGalois K carrier]
  narrowClassGroupEquiv : chapter08NarrowClassGroup N ≃* Gal(carrier / K)
  unramifiedAtFinite : chapter08UnramifiedAtFinitePlaces K carrier
  maximalFiniteUnramified :
    ∀ (L : Type w) [Field L] [NumberField L] [Algebra K L]
      [Algebra (𝓞 K) (𝓞 L)] [FiniteDimensional K L] [IsAbelianGalois K L],
      chapter08UnramifiedAtFinitePlaces K L →
      chapter08ExtensionContained K L carrier

abbrev chapter08NarrowHilbertClassField
    {K : Type u} [Field K] [NumberField K]
    {N : Chapter08NarrowClassGroupData K}
    (H : Chapter08NarrowHilbertClassFieldData K N) : Type v :=
  H.carrier

/- LOCAL_DEPENDENCY_GUESS: this packages the extra finite-unramified
quadratic extension which can occur when a real quadratic field has no unit of
norm `-1`. -/
structure Chapter08RealQuadraticExtraExtensionData
    (K : Type u) [Field K] [Algebra ℚ K] [NumberField K]
    [Algebra.IsQuadraticExtension ℚ K] where
  carrier : Type v
  [carrierField : Field carrier]
  [carrierAlgebra : Algebra K carrier]
  [carrierNumberField : NumberField carrier]
  [carrierFinite : FiniteDimensional K carrier]
  [carrierAbelianGalois : IsAbelianGalois K carrier]
  relativeDegree : Module.finrank K carrier = 2
  unramifiedAtFinite : chapter08UnramifiedAtFinitePlaces K carrier
  realPlacesComplexify :
    ¬chapter08RealPlacesStayReal K carrier

def chapter08NarrowClassNumber
    {K : Type u} [Field K] [NumberField K]
    (N : Chapter08NarrowClassGroupData K) : ℕ :=
  letI : Fintype N.carrier := N.carrierFintype
  Fintype.card N.carrier

/-- A unit of norm `-1`, the real-quadratic sign obstruction. -/
def chapter08HasUnitNormMinusOne
    (K : Type u) [Field K] [NumberField K] : Prop :=
  ∃ u : (𝓞 K)ˣ, Algebra.norm ℚ (u : K) = (-1 : ℚ)

/-! ## Concrete data used by the examples -/

/-- A number-field presentation of `ℚ(√-5)`. -/
structure Chapter08MinusFiveData
    (K : Type u) [Field K] [Algebra ℚ K] [NumberField K] where
  omega : 𝓞 K
  omega_square :
    (algebraMap (𝓞 K) K omega) ^ 2 = (-5 : K)
  discriminant : NumberField.discr K = (-20 : ℤ)

def chapter08MinusFivePrime
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K) : Ideal (𝓞 K) :=
  Ideal.span ({(2 : 𝓞 K), 1 + D.omega} : Set (𝓞 K))

def chapter08MinusFiveMinkowskiBound : ℝ :=
  (2 / Real.pi) * Real.sqrt 20

def chapter08MinusFiveNormEquationNoSolution : Prop :=
  ¬∃ a b : ℤ, a ^ 2 + 5 * b ^ 2 = 2

def chapter08QuadraticDiscriminants : Finset ℤ := {-4, 5, -20}

def chapter08DiscriminantProduct (d₁ d₂ d₃ : ℤ) : ℤ := d₁ * d₂ * d₃

/- LOCAL_DEPENDENCY_GUESS: the relative discriminant ideal and its norm are
left as explicit data because the full relative-discriminant API for an
arbitrary tower of number fields is not available through the earlier Book06
files. -/
structure Chapter08MinusFiveHilbertWitness
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    (D : Chapter08MinusFiveData K) where
  H : Type v
  [fieldH : Field H]
  [algebraKH : Algebra K H]
  [numberFieldH : NumberField H]
  [finiteKH : FiniteDimensional K H]
  [abelianGaloisKH : IsAbelianGalois K H]
  relativeDegree : Module.finrank K H = 2
  i : H
  sqrtFive : H
  i_square : i ^ 2 = (-1 : H)
  sqrtFive_square : sqrtFive ^ 2 = (5 : H)
  omega_image :
    algebraMap K H (algebraMap (𝓞 K) K D.omega) = i * sqrtFive
  relativeAdjoin : Algebra.adjoin K ({sqrtFive} : Set H) = ⊤
  absoluteAdjoin : Algebra.adjoin ℚ ({i, sqrtFive} : Set H) = ⊤
  quadraticDiscriminants :
    chapter08QuadraticDiscriminants = {-4, 5, -20}
  absoluteDiscriminant : NumberField.discr H = (400 : ℤ)
  relativeDiscriminant : Ideal (𝓞 K)
  relativeDiscriminantNorm : Ideal.absNorm relativeDiscriminant = 1

abbrev chapter08MinusFiveHilbertField
    {K : Type u} [Field K] [Algebra ℚ K] [NumberField K]
    {D : Chapter08MinusFiveData K}
    (W : Chapter08MinusFiveHilbertWitness D) : Type v :=
  W.H

/-! ## Rational ray and cyclotomic interfaces -/

def chapter08RationalRayModulus (m : ℕ) : Chapter08Modulus ℚ where
  finitePart := Ideal.span {(m : 𝓞 ℚ)}
  infinitePart := Finset.univ

def chapter08RationalRayModulusWithoutInfinity (m : ℕ) : Chapter08Modulus ℚ where
  finitePart := Ideal.span {(m : 𝓞 ℚ)}
  infinitePart := ∅

instance chapter08_rational_prime_ideal_isPrime
    (p : ℕ) [Fact p.Prime] :
    (Ideal.span {(p : 𝓞 ℚ)}).IsPrime := by
  apply Ideal.isPrime_span_singleton_of_prime
  apply (MulEquiv.prime_iff Rat.ringOfIntegersEquiv).mp
  simpa using (Nat.prime_iff_prime_int.1 (Fact.out : p.Prime))

def chapter08RationalRayGroup (m : ℕ) : Type := (ZMod m)ˣ

instance chapter08RationalRayGroupCommGroup (m : ℕ) :
    CommGroup (chapter08RationalRayGroup m) := by
  change CommGroup (ZMod m)ˣ
  infer_instance

def chapter08RationalRayGroupWithoutInfinity (m : ℕ) : Type :=
  (ZMod m)ˣ ⧸ Subgroup.closure ({(-1 : (ZMod m)ˣ)} : Set ((ZMod m)ˣ))

instance chapter08RationalRayGroupWithoutInfinityCommGroup (m : ℕ) :
    CommGroup (chapter08RationalRayGroupWithoutInfinity m) := by
  change CommGroup ((ZMod m)ˣ ⧸ Subgroup.closure
    ({(-1 : (ZMod m)ˣ)} : Set ((ZMod m)ˣ)))
  infer_instance

/-- Cyclotomic data retaining the chosen complex-conjugation automorphism. -/
structure Chapter08CyclotomicData
    (m : ℕ) (F : Type u) [Field F] [Algebra ℚ F]
    [NumberField F] [IsCyclotomicExtension {m} ℚ F] where
  complexConjugation : Gal(F / ℚ)

def chapter08CyclotomicRoot
    {m : ℕ} {F : Type u} [Field F] [Algebra ℚ F]
    [NumberField F] [IsCyclotomicExtension {m} ℚ F] [NeZero m]
    (_D : Chapter08CyclotomicData m F) : F :=
  IsCyclotomicExtension.zeta m ℚ F

def chapter08CyclotomicMaximalRealSubfield
    {m : ℕ} {F : Type u} [Field F] [Algebra ℚ F]
    [NumberField F] [IsCyclotomicExtension {m} ℚ F]
    (D : Chapter08CyclotomicData m F) : IntermediateField ℚ F :=
  IntermediateField.fixedField (Subgroup.closure {D.complexConjugation})

/- LOCAL_DEPENDENCY_GUESS: the local conductor calculation for cyclotomic
extensions is packaged as a profile, while the global ray-field maximality is
stated separately in the section file.  The local system records the actual
principal-unit subgroup and Artin map rather than replacing the calculation by
a bare proposition. -/
structure Chapter08LocalPrincipalUnitSystem
    (G : Type u) [Group G] where
  unitGroup : Type v
  [unitGroupCommGroup : CommGroup unitGroup]
  principalUnit : ℕ → Subgroup unitGroup
  localArtin : unitGroup →* G

structure Chapter08CyclotomicConductorProfile
    (m : ℕ) (F : Type u) [Field F] [Algebra ℚ F]
    [NumberField F] [IsCyclotomicExtension {m} ℚ F]
    (hm : 2 < m) where
  localPlace : Type v
  [localPlaceFintype : Fintype localPlace]
  primeIndex : localPlace → ℕ
  primeIndex_prime : ∀ v : localPlace, (primeIndex v).Prime
  principalUnitDepth : localPlace → ℕ
  principalUnitDepth_spec :
    ∀ v : localPlace, principalUnitDepth v = padicValNat (primeIndex v) m
  localSystem :
    ∀ _v : localPlace,
      Chapter08LocalPrincipalUnitSystem.{u, v} (Gal(F / ℚ))
  conductor : Chapter08Modulus ℚ
  writtenModulus : Chapter08Modulus ℚ

/- LOCAL_DEPENDENCY_GUESS: the conclusion of Kronecker--Weber is exposed as
a dependent package because Lean cannot quantify typeclass instances directly
inside an ordinary existential. -/
structure Chapter08CyclotomicContainmentData
    (L : Type u) [Field L] [Algebra ℚ L] where
  conductorIndex : ℕ
  carrier : Type v
  [carrierField : Field carrier]
  [carrierAlgebra : Algebra ℚ carrier]
  [carrierNumberField : NumberField carrier]
  [carrierCyclotomic :
    IsCyclotomicExtension {conductorIndex} ℚ carrier]
  embedding : L →ₐ[ℚ] carrier

/-! ## Quadratic Hilbert symbols and product formulas -/

abbrev Chapter08QuadraticSign := Multiplicative (ZMod 2)

/- LOCAL_DEPENDENCY_GUESS: the global/local Hilbert-symbol map is not a
pinned Mathlib declaration.  This finite-place product interface is exactly
what is needed for the final product-formula calculation. -/
structure Chapter08QuadraticHilbertProductData
    (K : Type u) [Field K] where
  place : Type v
  [placeFintype : Fintype place]
  hilbertSymbol : place → Kˣ → Kˣ → Chapter08QuadraticSign
  quadraticParameter : Kˣ
  hilbert_product_formula :
    ∀ a b : Kˣ, ∏ v, hilbertSymbol v a b = 1
  localCharacter : place → Kˣ →* Chapter08QuadraticSign
  localCharacter_eq_hilbertSymbol :
    ∀ v x, localCharacter v x = hilbertSymbol v x quadraticParameter
  globalCharacter : Kˣ →* Chapter08QuadraticSign
  global_eq_product :
    ∀ x : Kˣ, globalCharacter x = ∏ v, localCharacter v x

def chapter08LegendreSymbolAt
    (p : ℕ) [Fact p.Prime] (a : ℤ) : ℤ :=
  legendreSym p a

end
end LastLib.Book06GlobalClassFieldTheory.Chapter08
