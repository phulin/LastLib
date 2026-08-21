import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section01WhyUnitsNeedTheirOwnFiltration
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Section08CompletenessAndInverseLimitsOfUnits
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section04TheValuationOfANorm
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter04.Section05ResidueFieldShadows
import LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.Section04AbsoluteValueNormalizations

namespace LastLib.Book05LocalClassFieldTheory.Chapter02

noncomputable section

open Function Ideal IsLocalRing
open Filter Topology
open scoped BigOperators Pointwise Polynomial Topology WithTop

/-!
The chapter works with a complete discretely valued field with finite residue
field.  Earlier books keep the valuation-ring and principal-unit objects
canonical, so the Chapter 2 interfaces below use those objects rather than a
second presentation of a local field.
-/

abbrev Chapter02ValuationRing {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : ValuationSubring K :=
  v.toValuation.valuationSubring

abbrev Chapter02ResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  IsLocalRing.ResidueField (Chapter02ValuationRing v)

abbrev Chapter02UnitGroup {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  (Chapter02ValuationRing v)ˣ

abbrev Chapter02UnitFiltration {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Subgroup (Chapter02UnitGroup v) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10UnitFiltration
    (Chapter02ValuationRing v) n

def chapter02FieldUnitFiltration {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Subgroup Kˣ :=
  (Chapter02UnitFiltration v n).map
    (Units.map (Chapter02ValuationRing v).subtype.toMonoidHom)

def chapter02UnitInclusion {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Chapter02UnitGroup v →* Kˣ :=
  Units.map (Chapter02ValuationRing v).subtype.toMonoidHom

def chapter02ResidueMap {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) :
    Chapter02ValuationRing v →+* Chapter02ResidueField v :=
  IsLocalRing.residue (Chapter02ValuationRing v)

def Chapter02LocalField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter01.chapter01CompleteAdditiveValuation v ∧
    Finite (Chapter02ResidueField v)

def Chapter02UnitFiltrationNeighborhoodBasis {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) [TopologicalSpace (Chapter02UnitGroup v)] : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10UnitFiltrationNeighborhoodBasis
    (Chapter02UnitFiltration v)

def Chapter02FieldUnitFiltrationNeighborhoodBasis {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) [TopologicalSpace Kˣ] : Prop :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10UnitFiltrationNeighborhoodBasis
    (chapter02FieldUnitFiltration v)

def chapter02ValuationIdealPowerSet {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Set K :=
  {x | ∃ y : Chapter02ValuationRing v,
    y ∈ (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n ∧
      x = (y : K)}

def chapter02PrincipalUnitSet {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Set K :=
  {x | ∃ y : Chapter02ValuationRing v,
    y ∈ (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n ∧
      x = 1 + (y : K)}

def chapter02FieldUnitSet {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Set K :=
  {x | ∃ u : chapter02FieldUnitFiltration v n, x = ((u : Kˣ) : K)}

def chapter02UnitSet {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Set K :=
  chapter02FieldUnitSet v 0

abbrev Chapter02PrecisionQuotient {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Type _ :=
  Chapter02ValuationRing v ⧸
    (IsLocalRing.maximalIdeal (Chapter02ValuationRing v)) ^ n

def chapter02PrecisionUnitGroup {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Type _ :=
  (Chapter02PrecisionQuotient v (n + 1))ˣ

instance chapter02PrecisionUnitGroupGroup {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) :
    Group (chapter02PrecisionUnitGroup v n) := by
  change Group ((Chapter02PrecisionQuotient v (n + 1))ˣ)
  infer_instance

def chapter02PrecisionUnitTransition {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) :
    chapter02PrecisionUnitGroup v (n + 1) →*
      chapter02PrecisionUnitGroup v n := by
  change
    ((Chapter02PrecisionQuotient v (n + 2))ˣ) →*
      ((Chapter02PrecisionQuotient v (n + 1))ˣ)
  exact LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.chapter10PrecisionUnitTransition
    (Chapter02ValuationRing v) (n + 1)

abbrev Chapter02UnitInverseLimit {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter10.Chapter10AdicUnitInverseLimit
    (Chapter02ValuationRing v)

def chapter02UnitFiltrationMem {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) (u : Chapter02UnitGroup v) : Prop :=
  u ∈ Chapter02UnitFiltration v n

def chapter02IsUniformizer {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : K) : Prop :=
  π ≠ 0 ∧ v π = (1 : WithTop ℤ)

def chapter02IsUniformizerUnit {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : Kˣ) : Prop :=
  v (π : K) = (1 : WithTop ℤ)

/- Every nonzero element has an integral value in the chosen normalization.
   This is the value-group hypothesis used when a uniformizer is used to
   parameterize all valuation coordinates. -/
def Chapter02NormalizedValueGroup {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  ∀ x : K, x ≠ 0 → ∃ n : ℤ, v x = (n : WithTop ℤ)

/- The valuation map has an additive target.  `Multiplicative ℤ` records the
   same target as a group homomorphism out of the multiplicative field group. -/
def chapter02ValuationExactSequence {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ))
    (ν : Kˣ →* Multiplicative ℤ) : Prop :=
  Function.Injective (chapter02UnitInclusion v) ∧
    Function.MulExact (chapter02UnitInclusion v) ν ∧ Function.Surjective ν

def chapter02UniformizerSection {K : Type*} [Field K]
    (π : Kˣ) : Multiplicative ℤ →* Kˣ :=
  { toFun := fun z => π ^ (Multiplicative.toAdd z)
    map_one' := by sorry
    map_mul' := by sorry }

def chapter02ValueUnitSubgroup {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : Kˣ) (m n : ℕ) : Subgroup Kˣ :=
  Subgroup.zpowers (π ^ m) ⊔ chapter02FieldUnitFiltration v n

/- The value-unit subgroups form the neighborhood basis at the identity in
   the multiplicative topology.  The separate predicate prevents a basis for
   the compact unit subgroup from being mistaken for a basis of all of Kˣ. -/
def Chapter02ValueUnitNeighborhoodBasis {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : Kˣ) [TopologicalSpace Kˣ] : Prop :=
  (∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
    IsOpen (chapter02ValueUnitSubgroup v π m n : Set Kˣ)) ∧
    ∀ s ∈ 𝓝 (1 : Kˣ), ∃ m n : ℕ, 1 ≤ m ∧ 1 ≤ n ∧
      (chapter02ValueUnitSubgroup v π m n : Set Kˣ) ⊆ s

def chapter02ValueUnitProductSet {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (π : Kˣ) (m n : ℕ) : Set K :=
  {x | ∃ z : ℤ, ∃ u : K,
    u ∈ chapter02FieldUnitSet v n ∧
      x = ((π : Kˣ) : K) ^ ((m : ℤ) * z) * u}

def chapter02NormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K (S := L))

def chapter02NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  Subgroup.map (chapter02NormHom K L) ⊤

def chapter02UnitNormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) : Subgroup (Chapter02UnitGroup vK) where
  carrier := {u | ∃ x : Chapter02UnitGroup vL,
    (u : K) = Algebra.norm K (x : L)}
  one_mem' := by
    refine ⟨1, ?_⟩
    simp
  mul_mem' := by
    intro u w hu hw
    sorry
  inv_mem' := by
    intro u hu
    sorry

structure Chapter02NormUnitMapData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) where
  map : Chapter02UnitGroup vL →* Chapter02UnitGroup vK
  coe_norm : ∀ u,
    ((map u : Chapter02UnitGroup vK) : K) = Algebra.norm K (u : L)

def chapter02NormUnitFieldImage
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02NormUnitMapData K L vK vL) : Subgroup Kˣ :=
  ((⊤ : Subgroup (Chapter02UnitGroup vL)).map d.map).map
    (chapter02UnitInclusion vK)

def chapter02NormPrincipalUnitFieldImage
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (d : Chapter02NormUnitMapData K L vK vL) : Subgroup Kˣ :=
  ((Chapter02UnitFiltration vL 1).map d.map).map
    (chapter02UnitInclusion vK)

def chapter02NormValuationFormula
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (f : ℕ) : Prop :=
  ∀ x : L, x ≠ 0 →
    vK (Algebra.norm K x) = (f : WithTop ℤ) * vL x

def chapter02NormValuationImage
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ)) : Set (WithTop ℤ) :=
  {z | ∃ x : L, x ≠ 0 ∧ z = vK (Algebra.norm K x)}

def chapter02UnitNormImage
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ))
    (N : Chapter02UnitGroup vL →* Chapter02UnitGroup vK) :
    Set (Chapter02UnitGroup vK) :=
  Set.range N

def chapter02TraceImage
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) : Set K :=
  Algebra.trace K L '' chapter02ValuationIdealPowerSet vL n

def chapter02NormOneAddFunction
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (b : L) : K → K :=
  fun t => Algebra.norm K (1 + algebraMap K L t * b) - 1

def chapter02NormCorrectionStep
    {K : Type*} [Field K] (F : K → K) (s t : K) : K :=
  t + s - F t

def chapter02StrictValuationContraction
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (F : K → K) (c : ℕ) : Prop :=
  ∀ t t' : K,
    v t ≥ (c : WithTop ℤ) → v t' ≥ (c : WithTop ℤ) →
      v ((F t - t) - (F t' - t')) ≥ v (t - t') + 1

def chapter02CommutatorSubgroup (G : Type*) [Group G] : Subgroup G :=
  Subgroup.normalClosure {g : G | ∃ x y : G, g = x * y * x⁻¹ * y⁻¹}

abbrev Chapter02Abelianization (G : Type*) [Group G] : Type _ :=
  G ⧸ chapter02CommutatorSubgroup G

end

end LastLib.Book05LocalClassFieldTheory.Chapter02
