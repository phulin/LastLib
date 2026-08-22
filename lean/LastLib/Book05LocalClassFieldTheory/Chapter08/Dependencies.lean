import LastLib.Book05LocalClassFieldTheory.Chapter02.Section01SeparatingMagnitudeFromUnits
import LastLib.Book05LocalClassFieldTheory.Chapter05.Section06FiniteReciprocity
import LastLib.Book05LocalClassFieldTheory.Chapter07.Section06ReciprocityExistenceAndNorm
import LastLib.Book03RamificationTheory.Chapter05.Section02HerbrandsQuotientTheorem
import LastLib.Book03RamificationTheory.Chapter05.Section03TowerTransitivity
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Group.Basic

namespace LastLib.Book05LocalClassFieldTheory.Chapter08

noncomputable section

open Function
open scoped BigOperators Pointwise Topology WithTop
open LastLib.Book05LocalClassFieldTheory.Chapter02

/-!
Shared interfaces for Chapter 8.  The field-valued unit groups are the
canonical images of the valuation-ring unit groups from Book 2.  Finite
reciprocity and the inverse-limit reciprocity map are inherited from Chapters
5 and 7; the records below only add the local-field and ramification data
which the present chapter uses.
-/

abbrev Chapter08ValuationRing {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  Chapter02ValuationRing v

abbrev Chapter08ResidueField {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  Chapter02ResidueField v

abbrev Chapter08RingUnitGroup {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Type _ :=
  Chapter02UnitGroup v

abbrev Chapter08RingUnitFiltration {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Subgroup (Chapter08RingUnitGroup v) :=
  Chapter02UnitFiltration v n

/- The filtration used by reciprocity has carrier in `Kˣ`, while the ring
   filtration remains available for residue quotients and completeness. -/
def chapter08UnitFiltration {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Subgroup Kˣ :=
  chapter02FieldUnitFiltration v n

abbrev chapter08Units {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Subgroup Kˣ :=
  chapter08UnitFiltration v 0

abbrev chapter08PrincipalUnits {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) : Subgroup Kˣ :=
  chapter08UnitFiltration v n

def chapter08RingUnitInclusion {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : Chapter08RingUnitGroup v →* Kˣ :=
  chapter02UnitInclusion v

theorem chapter08_unit_filtration_descending
    {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (n : ℕ) :
    chapter08UnitFiltration v (n + 1) ≤ chapter08UnitFiltration v n := by
  change
    (Chapter02UnitFiltration v (n + 1)).map (chapter02UnitInclusion v) ≤
      (Chapter02UnitFiltration v n).map (chapter02UnitInclusion v)
  exact Subgroup.map_mono (chapter02_unit_filtration_descending v n)

def chapter08ValuationCoordinate {K : Type*} [Field K]
    {v : AddValuation K (WithTop ℤ)}
    (D : Chapter02ValuationCoordinateData v) : Kˣ →* Multiplicative ℤ :=
  D.valuation

/- The local field package records precisely the normalized valuation
   coordinate used by the unramified quotient.  The kernel field is a bridge
   from the canonical ring-unit image to the field-unit filtration. -/
structure Chapter08LocalFieldData (K : Type*) [Field K] where
  valuation : AddValuation K (WithTop ℤ)
  localField : Chapter02LocalField valuation
  coordinate : Chapter02ValuationCoordinateData valuation
  uniformizer : Kˣ
  uniformizer_coordinate :
    coordinate.valuation uniformizer = Multiplicative.ofAdd 1
  units_kernel : coordinate.valuation.ker = chapter08Units valuation

namespace Chapter08LocalFieldData

variable {K : Type*} [Field K]

@[simp] theorem valuation_uniformizer (D : Chapter08LocalFieldData K) :
    D.coordinate.valuation D.uniformizer = Multiplicative.ofAdd 1 :=
  D.uniformizer_coordinate

theorem mem_units_iff (D : Chapter08LocalFieldData K) (x : Kˣ) :
    x ∈ chapter08Units D.valuation ↔ D.coordinate.valuation x = 1 := by
  rw [← D.units_kernel]
  rfl

end Chapter08LocalFieldData

/- A finite local extension carries the valuation branch needed to read
   inertia and its residue quotient in the ambient Galois group. -/
structure Chapter08FiniteLocalExtensionData
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] where
  base : Chapter08LocalFieldData K
  valuation : AddValuation L (WithTop ℤ)
  localField : Chapter02LocalField valuation
  branch : ValuationSubring L
  branch_eq_valuation_ring :
    branch = valuation.toValuation.valuationSubring
  valuation_comap : ∀ x : K,
    valuation (algebraMap K L x) = base.valuation x
  branch_preserved : ∀ (σ : Gal(L / K)) (x : L), x ∈ branch ↔ σ x ∈ branch
  ramificationIndex : ℕ
  ramificationIndex_pos : 0 < ramificationIndex
  residueDegree : ℕ
  residueDegree_pos : 0 < residueDegree
  degree_eq_ef :
    Module.finrank K L = ramificationIndex * residueDegree

def chapter08FiniteInertia
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) : Subgroup (Gal(L / K)) :=
  LastLib.Book02FiniteExtensionsOfLocalFields.Chapter05.chapter05InertiaGroupInG
    K X.branch

def chapter08FiniteUnramified
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (X : Chapter08FiniteLocalExtensionData K L) : Prop :=
  X.ramificationIndex = 1 ∧ chapter08FiniteInertia X = ⊥

def chapter08NormHom
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormMap K L

def chapter08NormSubgroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05NormSubgroup K L

def chapter08NormUnitSubgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (_vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) : Subgroup Kˣ :=
  (chapter08UnitFiltration vL 0).map (chapter08NormHom K L)

theorem chapter08_norm_unit_subgroup_le_norm_subgroup
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) :
    chapter08NormUnitSubgroup vK vL ≤ chapter08NormSubgroup K L := by
  intro x hx
  rcases hx with ⟨y, _, rfl⟩
  exact ⟨y, ⟨by simp, rfl⟩⟩

def chapter08UnitNormProduct
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (vK : AddValuation K (WithTop ℤ))
    (vL : AddValuation L (WithTop ℤ)) (n : ℕ) : Subgroup Kˣ :=
  chapter08NormUnitSubgroup vK vL ⊔ chapter08UnitFiltration vK n

/- Chapter 5's class-formation record is currently universe-zero.  Keep this
   alias canonical and carry that restriction through the finite reciprocity
   declarations below rather than re-encoding its conclusions as input data. -/
abbrev Chapter08FiniteReciprocityData
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.Chapter05LocalClassFormationData K L

def chapter08FiniteReciprocityMap
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter08FiniteReciprocityData K L) : Kˣ →* Gal(L / K) :=
  LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05FiniteReciprocityMap D

theorem chapter08FiniteReciprocityMap_kernel
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter08FiniteReciprocityData K L) :
    (chapter08FiniteReciprocityMap D).ker = chapter08NormSubgroup K L := by
  simpa [chapter08FiniteReciprocityMap, chapter08NormSubgroup] using
    LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05FiniteReciprocityMap_kernel D

theorem chapter08FiniteReciprocityMap_surjective
    {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter08FiniteReciprocityData K L) :
    Function.Surjective (chapter08FiniteReciprocityMap D) := by
  simpa [chapter08FiniteReciprocityMap] using
    LastLib.Book05LocalClassFieldTheory.Chapter05.chapter05FiniteReciprocityMap_surjective D

abbrev Chapter08FiniteAbelianIndex
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :=
  LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07FiniteAbelianIndex K KAb

abbrev Chapter08FiniteArtinSystem
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb] :=
  LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07FiniteArtinSystem K KAb

def chapter08LocalReciprocity
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb) : Kˣ →* Gal(KAb / K) :=
  LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07LocalReciprocity S

abbrev Chapter08ArithmeticUnramifiedQuotient
    (K KAb : Type*) [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    (I : Subgroup (Gal(KAb / K))) :=
  LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07ArithmeticUnramifiedQuotient
    K KAb S I

def Chapter08ArithmeticUnramifiedQuotient.valuation
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    {S : Chapter08FiniteArtinSystem K KAb}
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I) :
    Kˣ →* Multiplicative ℤ :=
  U.localField.valuation_coordinate.valuation

instance chapter08ArithmeticUnramifiedQuotientGroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I) : Group U.G :=
  U.groupG

instance chapter08ArithmeticUnramifiedQuotientTopology
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I) : TopologicalSpace U.G :=
  U.topologyG

instance chapter08ArithmeticUnramifiedQuotientTopologicalGroup
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I) : IsTopologicalGroup U.G :=
  U.topologicalGroupG

abbrev Chapter08ProfiniteIntegers : Type _ :=
  LastLib.Book05LocalClassFieldTheory.Chapter07.Chapter07ProfiniteIntegers

noncomputable def chapter08IntegerToProfiniteCompletionHom :
    Multiplicative ℤ →* Chapter08ProfiniteIntegers :=
  LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07IntegerToProfiniteCompletionHom

noncomputable def chapter08IntegerToProfiniteCompletion
    (z : ℤ) : Chapter08ProfiniteIntegers :=
  LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07IntegerToProfiniteCompletion z

def chapter08UnramifiedCoordinate
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I) :
    Kˣ →* Chapter08ProfiniteIntegers :=
  letI : Group U.G := U.groupG
  U.completionEquiv.toMonoidHom.comp
    (U.quotient.comp (chapter08LocalReciprocity S))

def chapter08ArithmeticFrobenius
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I) : U.G :=
  letI : Group U.G := U.groupG
  letI : TopologicalSpace U.G := U.topologyG
  letI : IsTopologicalGroup U.G := U.topologicalGroupG
  U.completionEquiv.symm
    (chapter08IntegerToProfiniteCompletion 1)

def chapter08RestrictionToUnramified
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I) :
    Kˣ →* U.G :=
  letI : Group U.G := U.groupG
  U.quotient.comp (chapter08LocalReciprocity S)

theorem chapter08_unramified_coordinate_formula
    {K KAb : Type*} [Field K] [Field KAb] [Algebra K KAb]
    [TopologicalSpace Kˣ] [IsTopologicalGroup Kˣ]
    [IsAbelianGalois K KAb]
    (S : Chapter08FiniteArtinSystem K KAb)
    {I : Subgroup (Gal(KAb / K))}
    (U : Chapter08ArithmeticUnramifiedQuotient K KAb S I)
    (x : Kˣ) :
    chapter08UnramifiedCoordinate S U x =
      chapter08IntegerToProfiniteCompletion
        (Multiplicative.toAdd (U.valuation x)) := by
  let : Group U.G := U.groupG
  change
    U.completionEquiv
        (U.quotient
          (LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07LocalReciprocity
            S x)) =
      LastLib.Book05LocalClassFieldTheory.Chapter07.chapter07IntegerToProfiniteCompletion
        (Multiplicative.toAdd (U.valuation x))
  exact U.reciprocity_valuation x

/- The lower/upper filtration itself is imported from Book 3's canonical
   finite-filtration interface.  These aliases keep the Chapter 8 notation
   stable while retaining the quotient-compatible construction. -/
abbrev Chapter08RamificationFiltration (G : Type*) [Group G] [Finite G] :=
  LastLib.Book03RamificationTheory.Chapter05.Chapter05RamificationFiltration G

def chapter08LowerGroup
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) (t : ℝ) : Subgroup G :=
  F.lowerGroup t

def chapter08InertiaGroup
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) : Subgroup G :=
  chapter08LowerGroup F 0

def chapter08HerbrandFunction
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) (u : ℝ) : ℝ :=
  LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandFunction F u

def chapter08HerbrandInverse
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) (v : ℝ) : ℝ :=
  LastLib.Book03RamificationTheory.Chapter05.chapter05HerbrandInverse F v

def chapter08UpperGroup
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) (v : ℝ) : Subgroup G :=
  LastLib.Book03RamificationTheory.Chapter05.chapter05UpperRamificationGroup F v

def chapter08WildInertia
    {G : Type*} [Group G] [Finite G]
    (F : Chapter08RamificationFiltration G) : Subgroup G :=
  LastLib.Book03RamificationTheory.Chapter05.chapter05UpperZeroPlus F

/- The source's displacement definition is recorded independently of the
   subgroup-valued filtration.  The uniformizer formula is valid on a totally
   ramified branch; the all-integral-elements definition is the general one. -/
def chapter08UniformizerDisplacementIndex
    {L : Type*} [Field L]
    (vL : AddValuation L (WithTop ℤ)) (πL : L)
    (σ : L ≃+* L) : WithTop ℤ :=
  vL (σ πL - πL)

noncomputable def chapter08IntegralDisplacementIndex
    {L : Type*} [Field L]
    (vL : AddValuation L (WithTop ℤ))
    (σ : L ≃+* L) : WithTop ℤ :=
  sInf {r : WithTop ℤ |
    ∃ x : vL.toValuation.valuationSubring,
      r = vL (σ (x : L) - (x : L))}

def chapter08GaloisUniformizerDisplacementIndex
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (vL : AddValuation L (WithTop ℤ)) (πL : L)
    (σ : Gal(L / K)) : WithTop ℤ :=
  chapter08UniformizerDisplacementIndex vL πL σ.toRingEquiv

structure Chapter08LowerNumberingData
    (G : Type*) [Group G] [Finite G] where
  filtration : Chapter08RamificationFiltration G
  displacementIndex : G → WithTop ℤ
  displacement_one : displacementIndex 1 = ⊤
  lower_mem_iff : ∀ {σ : G}, σ ≠ 1 → ∀ n : ℕ,
    σ ∈ filtration.lowerGroup (n : ℝ) ↔
      (n : WithTop ℤ) + 1 ≤ displacementIndex σ

def chapter08IntegerLowerGroup
    {G : Type*} [Group G] [Finite G]
    (D : Chapter08LowerNumberingData G) (n : ℕ) : Subgroup G :=
  D.filtration.lowerGroup (n : ℝ)

def chapter08ConductorExists
    {K A : Type*} [Field K] [CommGroup A]
    (vK : AddValuation K (WithTop ℤ)) (χ : Kˣ →* A) : Prop :=
  ∃ n : ℕ, ∀ x ∈ chapter08UnitFiltration vK n, χ x = 1

def chapter08Conductor
    {K A : Type*} [Field K] [CommGroup A]
    (vK : AddValuation K (WithTop ℤ)) (χ : Kˣ →* A)
    (hχ : chapter08ConductorExists vK χ) : ℕ :=
  by
    classical
    exact Nat.find hχ

def chapter08FiniteOrderCharacter
    {K A : Type*} [Field K] [CommGroup A]
    (χ : Kˣ →* A) : Prop :=
  (Set.range χ).Finite

def chapter08GaloisConductorExists
    {G A : Type*} [Group G] [Finite G] [CommGroup A]
    (F : Chapter08RamificationFiltration G) (ρ : G →* A) : Prop :=
  ∃ n : ℕ, ∀ g ∈ chapter08UpperGroup F n, ρ g = 1

def chapter08GaloisConductor
    {G A : Type*} [Group G] [Finite G] [CommGroup A]
    (F : Chapter08RamificationFiltration G) (ρ : G →* A)
    (hρ : chapter08GaloisConductorExists F ρ) : ℕ :=
  by
    classical
    exact Nat.find hρ

def chapter08ResidueCharacteristic
    {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) : ℕ :=
  ringChar (Chapter08ResidueField v)

def chapter08ProPGroup (G : Type*) [Group G] (p : ℕ) : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex →
    ∃ n : ℕ, Nat.card (G ⧸ H) = p ^ n

abbrev Chapter08TameWildProduct
    {K : Type*} [Field K] (D : Chapter08LocalFieldData K) :=
  Multiplicative ℤ ×
    ((Chapter08ResidueField D.valuation)ˣ ×
      Chapter08RingUnitFiltration D.valuation 1)

end

end LastLib.Book05LocalClassFieldTheory.Chapter08
