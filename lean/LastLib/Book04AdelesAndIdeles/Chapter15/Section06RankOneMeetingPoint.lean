import LastLib.Book04AdelesAndIdeles.Chapter15.Section04DoubleQuotientsAndLattices
import LastLib.Book04AdelesAndIdeles.Chapter15.Section03CompactOpenLevel
import LastLib.Book04AdelesAndIdeles.Chapter11.Section04FinitenessOfRayClassGroups
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.Algebra.Group.Quotient

namespace LastLib.Book04AdelesAndIdeles.Chapter15

noncomputable section

open Set Filter NumberField MeasureTheory
open scoped RestrictedProduct

/-! ## 15.6. The rank-one meeting point -/

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-! ### The idele class group and the rank-one quotient -/

/-- `C_K = Kˣ \ 𝔸_Kˣ`, in the graph-topologized idele model. -/
abbrev Chapter15IdeleClassGroup :=
  Chapter15IdeleGroup R K ⧸
    (chapter15PrincipalIdele (R := R) (K := K)).range

/-- The quotient map from ideles to idele classes. -/
def chapter15IdeleClassMap :
    Chapter15IdeleGroup R K →* Chapter15IdeleClassGroup (R := R) (K := K) :=
  QuotientGroup.mk' (chapter15PrincipalIdele (R := R) (K := K)).range

theorem chapter15IdeleClassMap_kernel :
    (chapter15IdeleClassMap (R := R) (K := K)).ker =
      (chapter15PrincipalIdele (R := R) (K := K)).range := by sorry

theorem chapter15_idele_class_group_is_locally_compact
    (K : Type*) [Field K] [NumberField K] :
    LocallyCompactSpace (Chapter15IdeleClassGroup (R := 𝓞 K) (K := K)) := by
  sorry

/-- The rank-one automorphic quotient with no finite level. -/
abbrev Chapter15GL1NoLevelAutomorphicQuotient :=
  chapter15MatrixAutomorphicDoubleQuotient (R := R) (K := K) 1 (⊥ :
    Subgroup (Chapter15FiniteMatrixGroup 1 R K))

/- LOCAL_DEPENDENCY_GUESS: this is the canonical rank-one identification
between the matrix restricted product and the idele group; the quotient-level
equivalence is stated separately so that the graph topology is not confused
with the subspace topology on units of the adele ring. -/
def chapter15_rank_one_automorphic_quotient_formula
    (K : Type*) [Field K] [NumberField K] :
    Chapter15GL1NoLevelAutomorphicQuotient (R := 𝓞 K) (K := K) ≃ₜ
      Chapter15IdeleClassGroup (R := 𝓞 K) (K := K) := by
  sorry

/-! ### Hecke characters and one-dimensional automorphic representations -/

/-- A continuous character of the idele class group. -/
structure Chapter15HeckeCharacter where
  toMonoidHom : Chapter15IdeleClassGroup (R := R) (K := K) →* ℂˣ
  continuous_toMonoidHom : Continuous toMonoidHom

instance : CoeFun (Chapter15HeckeCharacter (R := R) (K := K))
    (fun _ => Chapter15IdeleClassGroup (R := R) (K := K) → ℂˣ) :=
  ⟨fun χ c => χ.toMonoidHom c⟩

/-- Finite order means that the character has finite exponent, not merely unitary values. -/
def chapter15FiniteOrderHeckeCharacter (χ : Chapter15HeckeCharacter (R := R) (K := K)) : Prop :=
  ∃ N : ℕ, 0 < N ∧ ∀ c, (χ.toMonoidHom c) ^ N = 1

/-- Unitary means that every complex value has absolute value one. -/
def chapter15UnitaryHeckeCharacter (χ : Chapter15HeckeCharacter (R := R) (K := K)) : Prop :=
  ∀ c, ‖(χ.toMonoidHom c : ℂ)‖ = 1

/-- The one-dimensional adelic representation model attached to a Hecke character. -/
abbrev Chapter15OneDimensionalAutomorphicRepresentation :=
  Chapter15HeckeCharacter (R := R) (K := K)

/-! ### Finite quotients, ray levels, and the finite-order boundary -/

/-- A finite continuous quotient of the idele class group. -/
structure Chapter15FiniteContinuousIdeleClassQuotient where
  quotient : Type*
  [quotientGroup : Group quotient]
  [quotient_topology : TopologicalSpace quotient]
  [quotient_discrete : DiscreteTopology quotient]
  finite : Finite quotient
  quotientMap : Chapter15IdeleClassGroup (R := R) (K := K) →* quotient
  surjective : Function.Surjective quotientMap
  continuous_quotientMap : Continuous quotientMap

/-- The finite-unit part of a ray level, with the standard tail outside its support. -/
def chapter15FiniteIdeleRayLevel
    (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) :
    Subgroup (Chapter15FiniteIdeleGroup R K) where
  carrier := {g | ∀ v : Chapter15FinitePlace R,
    g v ∈ chapter15PrincipalCongruenceLocalUnitLevel S m v}
  one_mem' := by
    intro v
    exact (chapter15PrincipalCongruenceLocalUnitLevel S m v).one_mem
  mul_mem' := by
    intro g h hg hh v
    exact (chapter15PrincipalCongruenceLocalUnitLevel S m v).mul_mem
      (hg v) (hh v)
  inv_mem' := by
    intro g hg v
    exact (chapter15PrincipalCongruenceLocalUnitLevel S m v).inv_mem (hg v)

theorem chapter15FiniteIdeleRayLevel_mem_iff
    (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ)
    (g : Chapter15FiniteIdeleGroup R K) :
    g ∈ chapter15FiniteIdeleRayLevel (R := R) (K := K) S m ↔
      ∀ v : Chapter15FinitePlace R,
        g v ∈ chapter15PrincipalCongruenceLocalUnitLevel S m v :=
  Iff.rfl

/-- A full ray level before quotienting by principal ideles. -/
def chapter15IdeleRayLevel
    (Ainf : Subgroup (Chapter15ArchimedeanIdeleGroup K))
    (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) :
    Subgroup (Chapter15IdeleGroup R K) :=
  Ainf.prod (chapter15FiniteIdeleRayLevel (R := R) (K := K) S m)

/-- The corresponding subgroup of the idele class group. -/
abbrev chapter15RayClassSubgroup
    (Ainf : Subgroup (Chapter15ArchimedeanIdeleGroup K))
    (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) :
    Subgroup (Chapter15IdeleClassGroup (R := R) (K := K)) :=
  Subgroup.map
    (chapter15IdeleClassMap (R := R) (K := K))
    (chapter15IdeleRayLevel (R := R) (K := K) Ainf S m)

instance chapter15RayClassSubgroup_normal
    (Ainf : Subgroup (Chapter15ArchimedeanIdeleGroup K))
    (S : Finset (Chapter15FinitePlace R))
    (m : Chapter15FinitePlace R → ℕ) :
    (chapter15RayClassSubgroup (R := R) (K := K) Ainf S m).Normal := by sorry

/- The canonical ray-modulus data are supplied by the preceding ray-class
chapter.  Keeping that type here prevents quotient finiteness from being
smuggled in as a field of the modulus itself. -/
structure Chapter15RayClassModulus (K : Type*) [Field K] [NumberField K] where
  underlying : LastLib.Book04AdelesAndIdeles.Chapter11.RayModulus K

/- The explicit finite-level constructions above remain useful as local
interfaces.  For the class-group quotient, however, use the canonical ray
unit subgroup transported across the underlying full-idele group equivalence. -/
/- The transport uses the same full adele-unit model as Chapter 11, so this
quotient is tied to the canonical ray class construction rather than to an
arbitrary open subgroup chosen with a finiteness proof. -/
def chapter15CanonicalIdeleRayLevel
    (K : Type*) [Field K] [NumberField K]
    (m : Chapter15RayClassModulus K) :
    Subgroup (Chapter15IdeleGroup (𝓞 K) K) :=
  (LastLib.Book04AdelesAndIdeles.Chapter11.chapter11RayUnitSubgroup m.underlying).comap
    (chapter15_idele_group_equiv_full_adele_units
      (R := 𝓞 K) (K := K)).toMonoidHom

def chapter15CanonicalRayClassSubgroup
    (K : Type*) [Field K] [NumberField K]
    (m : Chapter15RayClassModulus K) :
    Subgroup (Chapter15IdeleClassGroup (R := 𝓞 K) (K := K)) :=
  Subgroup.map (chapter15IdeleClassMap (R := 𝓞 K) (K := K))
    (chapter15CanonicalIdeleRayLevel K m)

instance chapter15CanonicalRayClassSubgroup_normal
    (K : Type*) [Field K] [NumberField K]
    (m : Chapter15RayClassModulus K) :
    (chapter15CanonicalRayClassSubgroup K m).Normal := by
  sorry

abbrev Chapter15RayClassQuotient
    (K : Type*) [Field K] [NumberField K]
    (m : Chapter15RayClassModulus K) :=
  Chapter15IdeleClassGroup (R := 𝓞 K) (K := K) ⧸
    chapter15CanonicalRayClassSubgroup K m

instance chapter15RayClassQuotient_finite
    (K : Type*) [Field K] [NumberField K]
    (m : Chapter15RayClassModulus K) :
    Finite (Chapter15RayClassQuotient K m) := by
  sorry

theorem chapter15_ray_class_subgroup_is_open
    {L : Type*} [Field L] [NumberField L]
    (m : Chapter15RayClassModulus L) :
    IsOpen (chapter15CanonicalRayClassSubgroup L m :
      Set (Chapter15IdeleClassGroup (R := 𝓞 L) (K := L))) := by
  sorry

theorem chapter15_ray_class_subgroups_are_cofinal
    {L : Type*} [Field L] [NumberField L]
    (H : Subgroup (Chapter15IdeleClassGroup (R := 𝓞 L) (K := L)))
    (hH : IsOpen (H : Set (Chapter15IdeleClassGroup (R := 𝓞 L) (K := L)))) :
      ∃ m : Chapter15RayClassModulus L,
      chapter15CanonicalRayClassSubgroup L m ≤ H := by
  sorry

theorem chapter15_finite_order_Hecke_character_has_finite_range
    (χ : Chapter15HeckeCharacter (R := R) (K := K))
    (hχ : chapter15FiniteOrderHeckeCharacter χ) :
    Finite (Set.range χ.toMonoidHom) := by
  sorry

theorem chapter15_finite_order_Hecke_character_factors_through_ray_class
    {L : Type*} [Field L] [NumberField L]
    (χ : Chapter15HeckeCharacter (R := 𝓞 L) (K := L))
    (hχ : chapter15FiniteOrderHeckeCharacter χ) :
      ∃ m : Chapter15RayClassModulus L,
      ∃ ψ : Chapter15RayClassQuotient L m →* ℂˣ,
        χ.toMonoidHom = ψ.comp (QuotientGroup.mk'
          (chapter15CanonicalRayClassSubgroup L m)) := by
  sorry

/- The finite-order condition is the part directly visible in finite abelian
reciprocity; a general unitary character need not satisfy it. -/
def chapter15FiniteAbelianReciprocityVisible
    (χ : Chapter15HeckeCharacter (R := R) (K := K)) : Prop :=
  chapter15FiniteOrderHeckeCharacter χ

/-! ### The archimedean warning -/

/-- Embed the archimedean idele component with finite component equal to one. -/
def chapter15ArchimedeanIdeleInclusion :
    Chapter15ArchimedeanIdeleGroup K →* Chapter15IdeleGroup R K where
  toFun x := (x, 1)
  map_one' := by
    sorry
  map_mul' x y := by
    sorry

/-- The archimedean component of a class-group character. -/
def chapter15ArchimedeanHeckeComponent
    (χ : Chapter15HeckeCharacter (R := R) (K := K)) :
    Chapter15ArchimedeanIdeleGroup K →* ℂˣ :=
  χ.toMonoidHom.comp
    ((chapter15IdeleClassMap (R := R) (K := K)).comp
      (chapter15ArchimedeanIdeleInclusion (R := R) (K := K)))

def chapter15ArchimedeanHeckeImage
    (χ : Chapter15HeckeCharacter (R := R) (K := K)) : Set ℂˣ :=
  Set.range (chapter15ArchimedeanHeckeComponent (R := R) (K := K) χ)

theorem chapter15_unitary_Hecke_characters_need_not_be_finite_order
    {L : Type*} [Field L] [NumberField L] :
    ∃ χ : Chapter15HeckeCharacter (R := 𝓞 L) (K := L),
      chapter15UnitaryHeckeCharacter χ ∧
        (chapter15ArchimedeanHeckeImage (R := 𝓞 L) (K := L) χ).Infinite := by
  sorry

theorem chapter15_infinite_archimedean_image_excludes_finite_order
    (χ : Chapter15HeckeCharacter (R := R) (K := K))
    (hχ : (chapter15ArchimedeanHeckeImage (R := R) (K := K) χ).Infinite) :
    ¬ chapter15FiniteOrderHeckeCharacter χ := by
  sorry

theorem chapter15_infinite_archimedean_image_excludes_finite_reciprocity
    (χ : Chapter15HeckeCharacter (R := R) (K := K))
    (hχ : (chapter15ArchimedeanHeckeImage (R := R) (K := K) χ).Infinite) :
    ¬ chapter15FiniteAbelianReciprocityVisible χ :=
  chapter15_infinite_archimedean_image_excludes_finite_order χ hχ

/-! ### Central characters, norms, and Haar measures -/

/-- A central character is a character of the center of the adelic matrix group. -/
abbrev Chapter15CentralCharacter (n : ℕ) :=
  Subgroup.center (Chapter15GLnAdeles n R K) →ₜ* ℂˣ

/-- A Haar measure record keeps the measure and its left-invariance witness together. -/
structure Chapter15HaarMeasureData (G : Type*) [Group G] [TopologicalSpace G]
    [MeasurableSpace G] where
  measure : Measure G
  isHaar : MeasureTheory.Measure.IsHaarMeasure measure

/- The remaining higher-dimensional Galois/automorphic correspondences and
irreducible decompositions are deliberately not asserted in this chapter. -/

end

end LastLib.Book04AdelesAndIdeles.Chapter15
