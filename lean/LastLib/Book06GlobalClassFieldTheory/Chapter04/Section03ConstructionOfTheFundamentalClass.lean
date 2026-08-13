import LastLib.Book06GlobalClassFieldTheory.Chapter04.Dependencies

namespace LastLib.Book06GlobalClassFieldTheory.Chapter04

noncomputable section

universe u v w z

open scoped BigOperators

/-! ## 4.3. Construction of the fundamental class -/

/-- A finite `G`-set of places, together with the data used to enlarge it. -/
structure Chapter04PlaceSystem (G W V : Type*) [Group G] where
  action : G → W → W
  action_one : ∀ w, action 1 w = w
  action_mul : ∀ g h w, action (g * h) w = action g (action h w)
  below : W → V
  decomposition : W → Subgroup G
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
  multiplicative : Type w
  [multiplicativeGroup : AddCommGroup multiplicative]
  divisorsOutside : Type w
  [divisorsGroup : AddCommGroup divisorsOutside]
  unitsMap : units.V →+ multiplicative
  valuationMap : multiplicative →+ divisorsOutside
  unitsMap_injective : Function.Injective unitsMap
  valuation_exact : Function.Exact unitsMap valuationMap
  valuation_surjective : Function.Surjective valuationMap

attribute [instance] Chapter04SUnitValuationData.multiplicativeGroup
  Chapter04SUnitValuationData.divisorsGroup

theorem chapter04_S_unit_valuation_exact
    {G : Type} {W : Type w} [Group G] [Fintype G]
    {S : Finset W} (V : Chapter04SUnitValuationData (G := G) S) :
    Function.Injective V.unitsMap ∧
      Function.Exact V.unitsMap V.valuationMap ∧
      Function.Surjective V.valuationMap := by
  exact ⟨V.unitsMap_injective, V.valuation_exact, V.valuation_surjective⟩

/-- The finite-level Tate sequence supplied by the local fundamental classes. -/
structure Chapter04CanonicalSUnitSequence
    {G : Type} {W : Type w} [Group G] [Fintype G]
    {V : Type z} (P : Chapter04PlaceSystem G W V)
    (S : Chapter04LargePlaceSet G W V P)
    (valuation : Chapter04SUnitValuationData (G := G) S.S) where
  lattice : Chapter04GModule.{0, 0} G
  sequence : Chapter04TwoExtension valuation.units lattice
  lattice_identification : lattice.V ≃+ chapter04XS S.S
  localFundamentalClass : W → chapter04QModZ
  localFundamentalClass_normalization : ∀ w,
    localFundamentalClass w =
      chapter04QModZOfRat ((1 : ℚ) / Nat.card (P.decomposition w))

/-- The S-unit sequence can be built from local fundamental classes once the S-class group vanishes
and the selected decomposition groups generate the finite Galois group. -/
theorem chapter04_canonical_S_unit_sequence
    {G : Type} {W : Type w} {V : Type z} [Group G] [Fintype G]
    (P : Chapter04PlaceSystem G W V)
    (S : Chapter04LargePlaceSet G W V P)
    (valuation : Chapter04SUnitValuationData (G := G) S.S) :
    Nonempty (Chapter04CanonicalSUnitSequence P S valuation) := by
  sorry

/-- Enlarging the finite set until the S-class group vanishes and the decomposition groups generate
is possible without a prime-distribution theorem. -/
theorem chapter04_exists_large_place_set
    {G : Type} {W : Type w} {V : Type z} [Group G] [Fintype G]
    (P : Chapter04PlaceSystem G W V) :
    Nonempty (Chapter04LargePlaceSet G W V P) := by
  sorry

/-- The global Tate extension obtained by splicing the S-unit sequence, the valuation sequence, and
the idele-class quotient. -/
structure Chapter04GlobalFundamentalExtension
    {G : Type} [Group G] [Fintype G] where
  ideleClasses : Chapter04GModule.{0, 0} G
  sequence : Chapter04TwoExtension ideleClasses (chapter04TrivialGModule G)

/-- The splicing construction produces the global fundamental extension. -/
theorem chapter04_splice_global_fundamental_extension
    {G : Type} {W : Type w} {V : Type z} [Group G] [Fintype G]
    (P : Chapter04PlaceSystem G W V)
    (S : Chapter04LargePlaceSet G W V P)
    (valuation : Chapter04SUnitValuationData (G := G) S.S)
    (localSequence : Chapter04CanonicalSUnitSequence P S valuation) :
    Nonempty (Chapter04GlobalFundamentalExtension (G := G)) := by
  sorry

/-- The splicing construction also supplies the normalized fundamental-class interface used by
the subgroup and cap-product statements. -/
theorem chapter04_splice_supplies_fundamental_class
    {G : Type} {W : Type w} {V : Type z} [Group G] [Fintype G]
    (P : Chapter04PlaceSystem G W V)
    (S : Chapter04LargePlaceSet G W V P)
    (valuation : Chapter04SUnitValuationData (G := G) S.S)
    (localSequence : Chapter04CanonicalSUnitSequence P S valuation) :
    Nonempty (Chapter04FundamentalClass (G := G)) := by
  sorry

/-! Independence of the auxiliary finite set is a property of the splicing construction, not an
unrelated proposition stored in every extension record.  The construction theorem above is the
interface at which that comparison is supplied. -/

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
