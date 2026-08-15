import LastLib.Book06GlobalClassFieldTheory.Chapter04.Dependencies
import LastLib.Book06GlobalClassFieldTheory.Chapter01.Section04ArchitectureOfTheProof

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

universe u v w z

open LastLib.Book05LocalClassFieldTheory.Chapter05
open scoped BigOperators

/-! ## 4.3. Construction of the fundamental class -/

/-- A finite `G`-set of places, together with the data used to enlarge it. -/
structure Chapter04PlaceSystem (G W V : Type*) [Group G] where
  action : G → W → W
  action_one : ∀ w, action 1 w = w
  action_mul : ∀ g h w, action (g * h) w = action g (action h w)
  below : W → V
  below_invariant : ∀ g w, below (action g w) = below w
  decomposition : W → Subgroup G
  decomposition_conjugate :
    ∀ (g : G) (w : W) (x : G),
      x ∈ decomposition (action g w) ↔ g⁻¹ * x * g ∈ decomposition w
  is_archimedean : W → Prop
  is_ramified : W → Prop
  represents_class_group_generator : W → Prop
  finite_archimedean_places : Set.Finite {w | is_archimedean w}
  finite_ramified_places : Set.Finite {w | is_ramified w}
  finite_class_group_generators :
    Set.Finite {w | represents_class_group_generator w}
  decomposition_groups_generate : (⨆ w : W, decomposition w) = ⊤

/-- The four source-order requirements on the chosen `S_L`: archimedean places, ramified places,
class-group generators, and decomposition groups generating `G`. -/
structure Chapter04LargePlaceSet
    (G W V : Type*) [Group G]
    (P : Chapter04PlaceSystem G W V) where
  S : Finset W
  stable : ∀ g w, w ∈ S → P.action g w ∈ S
  contains_archimedean : ∀ w, P.is_archimedean w → w ∈ S
  contains_ramified : ∀ w, P.is_ramified w → w ∈ S
  class_group_generated : ∀ w, P.represents_class_group_generator w → w ∈ S
  decomposition_groups_generate :
    (⨆ w : S, P.decomposition w) = ⊤

/-- The free divisor module `Y_S = ℤ[S_L]`. -/
abbrev chapter04YS {W : Type w} (S : Finset W) : Type w := S →₀ ℤ

/-- The augmentation of the free divisor module. -/
def chapter04YSAppendixAugmentation {W : Type*} (S : Finset W) :
    chapter04YS S →+ ℤ where
  toFun x := x.sum fun _ z => z
  map_zero' := by simp
  map_add' := by
    intro x y
    exact Finsupp.sum_add_index' (h := fun _ z => z)
      (fun _ => rfl) (fun _ _ _ => rfl)

/-- The degree-zero divisor lattice `X_S = ker(Y_S → ℤ)`. -/
def chapter04XS {W : Type*} (S : Finset W) : AddSubgroup (chapter04YS S) :=
  AddMonoidHom.ker (chapter04YSAppendixAugmentation S)

theorem chapter04_mem_XS_iff {W : Type*} (S : Finset W) (x : chapter04YS S) :
    x ∈ chapter04XS S ↔ x.sum (fun _ z => z) = 0 := by
  rfl

/-- The additive encoding of the valuation sequence outside `S_L`. -/
structure Chapter04SUnitValuationData
    {G : Type} {W : Type w} [Group G] [Fintype G]
  (S : Finset W) where
  units : Chapter04GModule.{0, 0} G
  multiplicative : Chapter04GModule.{0, w} G
  divisorsOutside : Chapter04GModule.{0, w} G
  unitsMap : units.V →+ multiplicative.V
  valuationMap : multiplicative.V →+ divisorsOutside.V
  unitsMap_equivariant : ∀ (g : G) (x : units.V),
    multiplicative.ρ g (unitsMap x) = unitsMap (units.ρ g x)
  valuationMap_equivariant : ∀ (g : G) (x : multiplicative.V),
    divisorsOutside.ρ g (valuationMap x) = valuationMap (multiplicative.ρ g x)
  unitsMap_injective : Function.Injective unitsMap
  valuation_exact : Function.Exact unitsMap valuationMap
  valuation_surjective : Function.Surjective valuationMap

theorem chapter04_S_unit_valuation_exact
    {G : Type} {W : Type w} [Group G] [Fintype G]
    {S : Finset W} (V : Chapter04SUnitValuationData (G := G) S) :
    Function.Injective V.unitsMap ∧
      Function.Exact V.unitsMap V.valuationMap ∧
      Function.Surjective V.valuationMap := by
  exact ⟨V.unitsMap_injective, V.valuation_exact, V.valuation_surjective⟩

/-! The field-indexed canonical package from the preceding global architecture.
The generic S-unit data below is allowed to use arbitrary place-system carriers,
but its resulting splice is only called global-fundamental after it is tied to
this actual idele-class coefficient package. -/
abbrev Chapter04CanonicalGlobalFundamentalClassData
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] :=
  LastLib.Book06GlobalClassFieldTheory.Chapter01.FiniteGaloisFundamentalClassData K L

/- The local fundamental classes are an input to the S-unit construction.  At
 this abstraction level their invariant values are the data exposed by the
 preceding Brauer interface; the normalization records the local degree. -/
structure Chapter04LocalFundamentalClassSystem
    {G : Type} {W : Type w} {V : Type z} [Group G] [Fintype G]
    (P : Chapter04PlaceSystem G W V) where
  value : W → chapter04QModZ
  normalization : ∀ w,
    value w = chapter04QModZOfRat ((1 : ℚ) / Nat.card (P.decomposition w))

/- A local realization records actual restricted degree-two classes for the
canonical coefficient representation.  The value-only record above remains a
useful source-order carrier, but it is not sufficient by itself to identify a
global idele-class fundamental class. -/
structure Chapter04CanonicalLocalFundamentalClassRealization
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter04CanonicalGlobalFundamentalClassData K L)
    {W : Type w} {V : Type z}
    (P : Chapter04PlaceSystem (Gal(L / K)) W V)
    (localClasses : Chapter04LocalFundamentalClassSystem P) where
  invariant : ∀ H : Subgroup (Gal(L / K)),
    chapter05GroupCohomology H
      (Rep.res H.subtype
        (LastLib.Book06GlobalClassFieldTheory.Chapter01.globalIdeleClassCoefficientRep
          D.ideleClassAction)) 2 →+ chapter04QModZ
  invariant_injective : ∀ H, Function.Injective (invariant H)
  invariant_range : ∀ H,
    (invariant H).range =
      AddSubgroup.zmultiples
        (chapter04QModZOfRat ((1 : ℚ) / Nat.card H))
  restriction_normalization : ∀ H,
    invariant H
        (chapter05RestrictTwoClass H D.fundamentalClass.value) =
      chapter04QModZOfRat ((1 : ℚ) / Nat.card H)
  local_value_compatibility : ∀ w,
    localClasses.value w =
      invariant (P.decomposition w)
        (chapter05RestrictTwoClass (P.decomposition w)
          D.fundamentalClass.value)

/-- The finite-level Tate sequence supplied by the local fundamental classes. -/
structure Chapter04CanonicalSUnitSequence
    {G : Type} {W : Type w} [Group G] [Fintype G]
    {V : Type z} (P : Chapter04PlaceSystem G W V)
    (S : Chapter04LargePlaceSet G W V P)
    (valuation : Chapter04SUnitValuationData (G := G) S.S)
    (localClasses : Chapter04LocalFundamentalClassSystem P) where
  lattice : Chapter04GModule.{0, 0} G
  sequence : Chapter04TwoExtension valuation.units lattice
  lattice_identification : lattice.V ≃+ chapter04XS S.S
  /-- The divisor lattice carries the induced `G`-action; this records that
  the additive identification really is an identification of endpoints in
  the equivariant S-unit sequence. -/
  xsAction : Representation ℤ G (chapter04XS S.S)
  lattice_identification_equivariant : ∀ (g : G) (x : lattice.V),
    lattice_identification (lattice.ρ g x) =
      xsAction g (lattice_identification x)
  localFundamentalClass : W → chapter04QModZ
  localFundamentalClass_supplied : localFundamentalClass = localClasses.value
  localFundamentalClass_normalization : ∀ w,
    localFundamentalClass w =
      chapter04QModZOfRat ((1 : ℚ) / Nat.card (P.decomposition w))

/-- The S-unit sequence can be built from local fundamental classes once the S-class group vanishes
and the selected decomposition groups generate the finite Galois group. -/
theorem chapter04_canonical_S_unit_sequence
    {G : Type} {W : Type w} {V : Type z} [Group G] [Fintype G]
    (P : Chapter04PlaceSystem G W V)
    (S : Chapter04LargePlaceSet G W V P)
    (valuation : Chapter04SUnitValuationData (G := G) S.S)
    (localClasses : Chapter04LocalFundamentalClassSystem P) :
    Nonempty (Chapter04CanonicalSUnitSequence P S valuation localClasses) := by
  sorry

/-- Enlarging the finite set until the S-class group vanishes and the decomposition groups generate
is possible without a prime-distribution theorem. -/
theorem chapter04_exists_large_place_set
    {G : Type} {W : Type w} {V : Type z} [Group G] [Fintype G]
    (P : Chapter04PlaceSystem G W V) :
    Nonempty (Chapter04LargePlaceSet G W V P) := by
  sorry

/- The global Tate extension obtained by splicing the S-unit sequence, the valuation sequence, and
the idele-class quotient.  Its coefficient and class are now the canonical
field-indexed ones, and the local values are required to be realized by
restricted local degree-two classes. -/
structure Chapter04GlobalFundamentalExtension
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter04CanonicalGlobalFundamentalClassData K L)
    {W : Type w} {V : Type z}
    (P : Chapter04PlaceSystem (Gal(L / K)) W V)
    (S : Chapter04LargePlaceSet (Gal(L / K)) W V P)
    (valuation : Chapter04SUnitValuationData (G := Gal(L / K)) S.S)
    {localClasses : Chapter04LocalFundamentalClassSystem P}
    (localSequence : Chapter04CanonicalSUnitSequence P S valuation localClasses) where
  localClassRealization :
    Chapter04CanonicalLocalFundamentalClassRealization D P localClasses
  splicedExtension :
    Chapter05TwoExtensionRepresentative (Gal(L / K))
      (LastLib.Book06GlobalClassFieldTheory.Chapter01.globalIdeleClassCoefficientRep
        D.ideleClassAction)
      D.fundamentalClass.value D.capProduct
  splicedExtension_is_canonical :
    splicedExtension.extension = D.twoExtensionRepresentative.extension
  suppliedLocalSequence : Chapter04CanonicalSUnitSequence P S valuation localClasses
  suppliedLocalSequence_eq : suppliedLocalSequence = localSequence

/-- The splicing construction produces the global fundamental extension. -/
theorem chapter04_splice_global_fundamental_extension
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter04CanonicalGlobalFundamentalClassData K L)
    {W : Type w} {V : Type z}
    (P : Chapter04PlaceSystem (Gal(L / K)) W V)
    (S : Chapter04LargePlaceSet (Gal(L / K)) W V P)
    (valuation : Chapter04SUnitValuationData (G := Gal(L / K)) S.S)
    {localClasses : Chapter04LocalFundamentalClassSystem P}
    (localRealization :
      Chapter04CanonicalLocalFundamentalClassRealization D P localClasses)
    (localSequence : Chapter04CanonicalSUnitSequence P S valuation localClasses) :
    Nonempty (Chapter04GlobalFundamentalExtension D P S valuation localSequence) := by
  sorry

/-- The splicing construction also supplies the normalized fundamental-class interface used by
the subgroup and cap-product statements. -/
theorem chapter04_splice_supplies_fundamental_class
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter04CanonicalGlobalFundamentalClassData K L)
    {W : Type w} {V : Type z}
    (P : Chapter04PlaceSystem (Gal(L / K)) W V)
    (S : Chapter04LargePlaceSet (Gal(L / K)) W V P)
    (valuation : Chapter04SUnitValuationData (G := Gal(L / K)) S.S)
    {localClasses : Chapter04LocalFundamentalClassSystem P}
    (localSequence : Chapter04CanonicalSUnitSequence P S valuation localClasses)
    (_globalExtension : Chapter04GlobalFundamentalExtension D P S valuation localSequence) :
    Nonempty
      (Chapter05FundamentalTwoClass (Gal(L / K))
        (LastLib.Book06GlobalClassFieldTheory.Chapter01.globalIdeleClassCoefficientRep
          D.ideleClassAction)) := by
  exact ⟨D.fundamentalClass⟩

theorem chapter04_canonical_global_fundamental_class_data_exists
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))] :
    Nonempty (Chapter04CanonicalGlobalFundamentalClassData K L) := by
  exact
    LastLib.Book06GlobalClassFieldTheory.Chapter01.finite_galois_fundamental_class_exists

/-! Any two auxiliary choices with the same canonical field-indexed package
produce the same extension class.  In particular this covers enlarging the
finite S-unit set. -/
theorem chapter04_global_fundamental_extension_choice_independent
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Fintype (Gal(L / K))]
    (D : Chapter04CanonicalGlobalFundamentalClassData K L)
    {W₁ : Type w} {V₁ : Type z}
    (P₁ : Chapter04PlaceSystem (Gal(L / K)) W₁ V₁)
    (S₁ : Chapter04LargePlaceSet (Gal(L / K)) W₁ V₁ P₁)
    (valuation₁ : Chapter04SUnitValuationData (G := Gal(L / K)) S₁.S)
    {localClasses₁ : Chapter04LocalFundamentalClassSystem P₁}
    (localSequence₁ : Chapter04CanonicalSUnitSequence P₁ S₁ valuation₁ localClasses₁)
    (E₁ : Chapter04GlobalFundamentalExtension D P₁ S₁ valuation₁ localSequence₁)
    {W₂ : Type w} {V₂ : Type z}
    (P₂ : Chapter04PlaceSystem (Gal(L / K)) W₂ V₂)
    (S₂ : Chapter04LargePlaceSet (Gal(L / K)) W₂ V₂ P₂)
    (valuation₂ : Chapter04SUnitValuationData (G := Gal(L / K)) S₂.S)
    {localClasses₂ : Chapter04LocalFundamentalClassSystem P₂}
    (localSequence₂ : Chapter04CanonicalSUnitSequence P₂ S₂ valuation₂ localClasses₂)
    (E₂ : Chapter04GlobalFundamentalExtension D P₂ S₂ valuation₂ localSequence₂) :
    E₁.splicedExtension.extension = E₂.splicedExtension.extension := by
  rw [E₁.splicedExtension_is_canonical, E₂.splicedExtension_is_canonical]

/-- Restriction of the canonical extension to a subgroup gives the corresponding intermediate
field normalization. -/
theorem chapter04_restricted_fundamental_class_has_intermediate_normalization
    {G : Type} [Group G] [Fintype G]
    (U : Chapter04FundamentalClass (G := G))
    (H : Subgroup G) :
    U.invariant H (chapter04RestrictTwoClass U.C H U.u) =
      chapter04QModZOfRat ((1 : ℚ) / Nat.card H) := by
  exact U.invariant_normalization H

end

end LastLib.Book06GlobalClassFieldTheory.Chapter04
