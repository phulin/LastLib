import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section04TheValuationOfANorm
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Dependencies
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.Section03TheUnramifiedCase
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.NNReal.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Topology.Algebra.RestrictedProduct.Units

namespace LastLib.Book04AdelesAndIdeles.Chapter10

noncomputable section

open scoped BigOperators NNReal RestrictedProduct Topology

/-!
Shared interfaces for Chapter 10.

Mathlib has the canonical finite adèle ring of a Dedekind domain and the
canonical restricted product.  It does not package the book's global system
of completions for an arbitrary finite extension together with its maps over
places.  The small records below keep that missing bookkeeping explicit; the
local field norm itself is always `Algebra.norm`.
-/

/-! ### Local norms and valuation bookkeeping -/

/-- The valuation ring attached to an additive valuation. -/
abbrev chapter10ValuationRing {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) : Type _ :=
  v.toValuation.valuationSubring

/-- The underlying set of integral elements for a normalized additive valuation. -/
def chapter10LocalIntegerSet {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) : Set F :=
  (v.toValuation.valuationSubring : Set F)

/-- The units of the valuation ring, viewed in the ambient field. -/
def chapter10LocalUnitSet {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) : Set F :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11UnitSet v

theorem chapter10_mem_local_unit_set_iff
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ)) (x : F) :
    x ∈ chapter10LocalUnitSet v ↔ v x = 0 := by
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11_mem_unit_set_iff_valuation_zero v x

/-- The canonical principal-unit layer at depth `n`. -/
def chapter10LocalPrincipalUnitSet {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) (n : ℕ) : Set F :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11PrincipalUnitSet v n

theorem chapter10_mem_local_principal_unit_set_iff
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (n : ℕ) (x : F) :
    x ∈ chapter10LocalPrincipalUnitSet v n ↔
      x ∈ LastLib.Book02FiniteExtensionsOfLocalFields.Chapter11.chapter11PrincipalUnitSet v n :=
  Iff.rfl

/-- The field norm, viewed as the multiplicative monoid homomorphism used by
the local and global constructions. -/
def chapter10LocalNorm (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : E →* F :=
  Algebra.norm F (S := E)

/-- The induced map on unit groups. -/
def chapter10LocalNormUnitHom (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : Eˣ →* Fˣ :=
  Units.map (chapter10LocalNorm F E)

/-- The norm image of the nonzero elements of a finite field extension. -/
def chapter10LocalNormImage (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : Set F :=
  {x | ∃ y : E, y ≠ 0 ∧ chapter10LocalNorm F E y = x}

theorem chapter10_mem_local_norm_image_iff
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (x : F) :
    x ∈ chapter10LocalNormImage F E ↔
      ∃ y : E, y ≠ 0 ∧ chapter10LocalNorm F E y = x := Iff.rfl

/-- The norm image of the multiplicative group `Eˣ`; for a field this is
the full nonzero norm image, not merely the valuation-ring unit image. -/
def chapter10LocalNormUnitImage (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] : Set F :=
  Set.range (fun u : Eˣ => (chapter10LocalNormUnitHom F E u : F))

theorem chapter10_mem_local_norm_unit_image_iff
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] (x : F) :
    x ∈ chapter10LocalNormUnitImage F E ↔
      ∃ u : Eˣ, (chapter10LocalNormUnitHom F E u : F) = x := Iff.rfl

/-- The norm image of valuation-ring units, represented in the ambient field. -/
def chapter10ValuationUnitNormImage
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vE : AddValuation E (WithTop ℤ)) : Set F :=
  {x | ∃ y : E, y ∈ chapter10LocalUnitSet vE ∧
    chapter10LocalNorm F E y = x}

theorem chapter10_mem_valuation_unit_norm_image_iff
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vE : AddValuation E (WithTop ℤ)) (x : F) :
    x ∈ chapter10ValuationUnitNormImage F E vE ↔
      ∃ y : E, y ∈ chapter10LocalUnitSet vE ∧
        chapter10LocalNorm F E y = x := Iff.rfl

/-- The valuation-divisibility set occurring in the unramified norm group. -/
def chapter10ValuationDivisibleSet {F : Type*} [Field F]
    (v : AddValuation F (WithTop ℤ)) (d : ℕ) : Set F :=
  {x | ∃ z : ℤ, x ≠ 0 ∧ v x = ((d : ℤ) * z : ℤ)}

theorem chapter10_mem_valuation_divisible_set_iff
    {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (d : ℕ) (x : F) :
    x ∈ chapter10ValuationDivisibleSet v d ↔
      ∃ z : ℤ, x ≠ 0 ∧ v x = ((d : ℤ) * z : ℤ) := Iff.rfl

/-- A field norm formula at a chosen normalized branch. -/
def chapter10NormValuationFormula
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (f : ℕ) : Prop :=
  ∀ y : E, y ≠ 0 →
    vF (chapter10LocalNorm F E y) = (f : WithTop ℤ) * vE y

theorem chapter10_norm_valuation_formula_iff
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E]
    (vF : AddValuation F (WithTop ℤ)) (vE : AddValuation E (WithTop ℤ))
    (f : ℕ) :
    chapter10NormValuationFormula F E vF vE f ↔
      ∀ y : E, y ≠ 0 →
        vF (Algebra.norm F y) = (f : WithTop ℤ) * vE y := Iff.rfl

/-! ### Canonical finite adèles and abstract global place systems -/

/-- Mathlib's finite adèle ring, exposed under the book-facing name. -/
abbrev chapter10FiniteAdeles
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Type _ :=
  IsDedekindDomain.FiniteAdeleRing R K

/-- The unit group of Mathlib's finite adèle ring. -/
abbrev chapter10FiniteIdeles
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] : Type _ :=
  (chapter10FiniteAdeles R K)ˣ

/- LOCAL_DEPENDENCY_GUESS: Chapter 9 supplies the idele and module APIs for a
single number field, but not the extension-indexed completion data needed for
the source's family of places above each base place.  This record keeps that
additional bookkeeping explicit until such an extension interface exists. -/
/- A global extension datum records only the data needed to form the
restricted-product norm.  The local multiplicative groups may be unit groups
of completions, or any equivalent book-facing model. -/
structure Chapter10GlobalNormData
    (ιK ιL : Type*) (Kloc : ιK → Type*) (Lloc : ιL → Type*)
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)] where
  below : ιL → ιK
  finiteOver : ∀ v, Finite {w : ιL // below w = v}
  nonemptyOver : ∀ v, Nonempty {w : ιL // below w = v}
  unitK : ∀ v, Subgroup (Kloc v)
  unitL : ∀ w, Subgroup (Lloc w)
  localNorm : ∀ w, Lloc w →* Kloc (below w)
  mapsUnit : ∀ w, Set.MapsTo (localNorm w) (unitL w) (unitK (below w))

namespace Chapter10GlobalNormData

variable {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
  [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]

/-- The restricted product of the local multiplicative groups. -/
abbrev kIdeles (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) : Type _ :=
  Πʳ v, [Kloc v, d.unitK v]

abbrev lIdeles (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) : Type _ :=
  Πʳ w, [Lloc w, d.unitL w]

instance chapter10FiberFinite
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK) :
    Finite {w : ιL // d.below w = v} :=
  d.finiteOver v

noncomputable instance chapter10FiberFintype
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK) :
    Fintype {w : ιL // d.below w = v} := by
  letI : Finite {w : ιL // d.below w = v} := d.finiteOver v
  exact Fintype.ofFinite {w : ιL // d.below w = v}

/-- A local norm on a fiber, transported to the chosen base-place factor. -/
def chapter10LocalNormAt
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) (v : ιK)
    (w : {w : ιL // d.below w = v}) (y : Lloc (w : ιL)) : Kloc v :=
  cast (congrArg Kloc w.property) (d.localNorm (w : ιL) y)

end Chapter10GlobalNormData

open Chapter10GlobalNormData

/-! ### Adelic modules and scalar extension -/

/-- A global module is a multiplicative map whose local factorization is
recorded explicitly.  The `finprod` is legitimate because normalized local
modules are one on the distinguished unit subgroups. -/
structure Chapter10AdelicModuleData
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc) where
  localK : ∀ v, Kloc v →* ℝ≥0
  localL : ∀ w, Lloc w →* ℝ≥0
  moduleK : kIdeles d →* ℝ≥0
  moduleL : lIdeles d →* ℝ≥0
  localK_unit : ∀ v, ∀ u : d.unitK v, localK v u = 1
  localL_unit : ∀ w, ∀ u : d.unitL w, localL w u = 1
  moduleK_factorization : ∀ x, moduleK x = ∏ᶠ v, localK v (x v)
  moduleL_factorization : ∀ x, moduleL x = ∏ᶠ w, localL w (x w)

/-- The scalar-extension component map over a place. -/
def chapter10ScalarExtensionRaw
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (scalar : ∀ w, Kloc (d.below w) →* Lloc w)
    (x : kIdeles d) (w : ιL) : Lloc w :=
  scalar w (x (d.below w))

theorem chapter10ScalarExtensionRaw_eventually_unit
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (scalar : ∀ w, Kloc (d.below w) →* Lloc w)
    (hscalar : ∀ w, Set.MapsTo (scalar w) (d.unitK (d.below w)) (d.unitL w))
    (x : kIdeles d) :
    ∀ᶠ w in Filter.cofinite,
      chapter10ScalarExtensionRaw d scalar x w ∈ d.unitL w := by
  have hbelow : Filter.Tendsto d.below Filter.cofinite Filter.cofinite := by
    apply Filter.Tendsto.cofinite_of_finite_preimage_singleton
    intro v
    apply Set.finite_coe_iff.mpr
    have hEq : Set.Finite {w : ιL | d.below w = v} :=
      Set.finite_coe_iff.mp (d.finiteOver v)
    convert hEq using 1
    ext w
    simp
  filter_upwards [hbelow.eventually x.2] with w hw
  exact hscalar w hw

/-- Scalar extension of an idele, with the restricted-product proof supplied
by the finite-fibre argument. -/
def chapter10ScalarExtension
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (scalar : ∀ w, Kloc (d.below w) →* Lloc w)
    (_hscalar : ∀ w, Set.MapsTo (scalar w) (d.unitK (d.below w)) (d.unitL w)) :
    kIdeles d → lIdeles d := by
  intro x
  exact ⟨chapter10ScalarExtensionRaw d scalar x,
    chapter10ScalarExtensionRaw_eventually_unit d scalar _hscalar x⟩

/-- The scalar-extension homomorphism. -/
def chapter10ScalarExtensionHom
    {ιK ιL : Type*} {Kloc : ιK → Type*} {Lloc : ιL → Type*}
    [∀ v, CommGroup (Kloc v)] [∀ w, CommGroup (Lloc w)]
    (d : Chapter10GlobalNormData ιK ιL Kloc Lloc)
    (scalar : ∀ w, Kloc (d.below w) →* Lloc w)
    (hscalar : ∀ w, Set.MapsTo (scalar w) (d.unitK (d.below w)) (d.unitL w)) :
    kIdeles d →* lIdeles d where
  toFun := chapter10ScalarExtension d scalar hscalar
  map_one' := by
    exact (by ext w; simp [chapter10ScalarExtension, chapter10ScalarExtensionRaw])
  map_mul' := by
    exact (by
      intro x y
      ext w
      change (scalar w) (x (d.below w) * y (d.below w)) =
        (scalar w) (x (d.below w)) * (scalar w) (y (d.below w))
      exact (scalar w).map_mul _ _)

end
end LastLib.Book04AdelesAndIdeles.Chapter10
