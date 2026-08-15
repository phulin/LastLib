import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section02SheafQuotientsAndOrbitFunctors

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeScheme
open scoped BigOperators

universe u v

/-!
### 11.3 Configuration spaces

The collision-free locus is represented by an open-subscheme interface.  Its
universal property is stated directly in terms of the ordered power, so the
definition remains useful before a particular presentation by equations is
chosen.
-/

structure ConfigurationSpace {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ) where
  carrier : RelativeScheme S
  inclusion : carrier ⟶ (relativePower X d).carrier
  isOpen : IsOpenImmersion inclusion.hom
  characterizes : ∀ (T : RelativeScheme S) (x : T ⟶ (relativePower X d).carrier),
    PairwiseDistinctTuple (fun i => x ≫ (relativePower X d).projection i) ↔
      ∃! y : T ⟶ carrier, y ≫ inclusion = x

theorem configurationSpace_exists {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] : Nonempty (ConfigurationSpace X d) := by
  sorry

noncomputable def configurationSpace {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] : ConfigurationSpace X d :=
  Classical.choice (configurationSpace_exists X d)

abbrev configurationInclusion {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    (configurationSpace X d).carrier ⟶ (relativePower X d).carrier :=
  (configurationSpace X d).inclusion

theorem configurationSpace_lift_unique {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] (T : RelativeScheme S)
    (x : T ⟶ (relativePower X d).carrier)
    (hx : PairwiseDistinctTuple (fun i => x ≫ (relativePower X d).projection i)) :
    ∃! y : T ⟶ (configurationSpace X d).carrier,
      y ≫ configurationInclusion X d = x := by
  exact ((configurationSpace X d).characterizes T x).mp hx

@[instance_reducible]
noncomputable def configurationSpace_quasiProjective {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Chapter11QuasiProjectiveOver (configurationSpace X d).carrier := by
  sorry

/-- The induced permutation action on the open configuration locus. -/
structure ConfigurationActionData {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] where
  action : RelativeAction (configurationSpace X d).carrier (Equiv.Perm (Fin d))
  compatible : ∀ σ : Equiv.Perm (Fin d),
    action.hom σ ≫ configurationInclusion X d =
      configurationInclusion X d ≫ (relativePower X d).permutation σ

theorem configurationAction_exists {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Nonempty (ConfigurationActionData X d) := by
  sorry

noncomputable def configurationActionData {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] : ConfigurationActionData X d :=
  Classical.choice (configurationAction_exists X d)

noncomputable def configurationAction {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    RelativeAction (configurationSpace X d).carrier (Equiv.Perm (Fin d)) :=
  (configurationActionData X d).action

theorem configurationAction_compatible {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    ∀ σ : Equiv.Perm (Fin d),
      (configurationAction X d).hom σ ≫ configurationInclusion X d =
        configurationInclusion X d ≫ (relativePower X d).permutation σ := by
  intro σ
  exact (configurationActionData X d).compatible σ

theorem configurationAction_isFree {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    (configurationAction X d).IsFree := by
  sorry

/- LOCAL_DEPENDENCY_GUESS: install the quasi-projectivity instance for the
   open configuration locus from the earlier relative embedding API. -/
noncomputable def unorderedConfigurationQuotient {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    RelativeFiniteGroupQuotient (configurationSpace X d).carrier
      (Equiv.Perm (Fin d)) (configurationAction X d) := by
  letI : Chapter11QuasiProjectiveOver (configurationSpace X d).carrier :=
    configurationSpace_quasiProjective X d
  exact finiteGroupQuotient (configurationAction X d)

abbrev unorderedConfigurationSpace {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] : RelativeScheme S :=
  (unorderedConfigurationQuotient X d).carrier

abbrev unorderedConfigurationMap {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    (configurationSpace X d).carrier ⟶ unorderedConfigurationSpace X d :=
  (unorderedConfigurationQuotient X d).quotientMap

/- The quotient of the collision-free locus maps canonically to the full
   symmetric power.  This bridge is the scheme-theoretic meaning of calling
   the quotient an open part of the symmetric power; the factorization below
   records the map before any pointwise identification is used. -/
noncomputable def unorderedConfigurationToSymmetricPower {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    unorderedConfigurationSpace X d ⟶ symmetricPower X d := by
  exact ((unorderedConfigurationQuotient X d).quotient.universal
    (configurationInclusion X d ≫ symmetricPowerMap X d) (by sorry)
    ).choose

theorem unorderedConfigurationToSymmetricPower_factorization {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    configurationInclusion X d ≫ symmetricPowerMap X d =
      unorderedConfigurationMap X d ≫ unorderedConfigurationToSymmetricPower X d := by
  sorry

theorem unorderedConfigurationToSymmetricPower_isOpen {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    IsOpenImmersion (unorderedConfigurationToSymmetricPower X d).hom := by
  sorry

theorem unorderedConfiguration_finite_etale {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    Chapter11FiniteEtaleOfDegree (unorderedConfigurationMap X d).hom (Nat.factorial d) := by
  sorry

theorem unorderedConfiguration_surjective {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Surjective (unorderedConfigurationMap X d).hom := by
  exact (unorderedConfigurationQuotient X d).surjective

/-- The splitting condition for a particular finite étale family. -/
abbrev Chapter11SubschemeSplitsAsDisjointSections {S : Scheme.{u}}
    {X T : RelativeScheme S} {d : ℕ} (Z : RelativeFiniteEtaleSubscheme X T d) : Prop :=
  Chapter11SplitsAsDisjointSections d Z

abbrev ConfigurationFamily {S : Scheme.{u}} (X T : RelativeScheme S) (d : ℕ) :=
  {Z : RelativeFiniteEtaleSubscheme X T d //
    Chapter11SubschemeSplitsAsDisjointSections Z}

/- Pullback on the family-valued classification functor. -/
noncomputable def ConfigurationFamily.pullback {S : Scheme.{u}}
    {X T U : RelativeScheme S} {d : ℕ} (u : U ⟶ T)
    (F : ConfigurationFamily X T d) : ConfigurationFamily X U d := by
  refine ⟨RelativeFiniteEtaleSubscheme.pullback F.1 u, ?_⟩
  sorry

structure Chapter11ConfigurationFamilyClassification {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] where
  equivalence : ∀ T : RelativeScheme S,
    (T ⟶ unorderedConfigurationSpace X d) ≃ ConfigurationFamily X T d
  natural :
    ∀ {T U : RelativeScheme S} (u : U ⟶ T)
      (f : T ⟶ unorderedConfigurationSpace X d),
      ConfigurationFamily.pullback u (equivalence T f) =
        equivalence U (u ≫ f)

noncomputable def unorderedConfiguration_classifies_split_finite_etale_families
    {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Chapter11ConfigurationFamilyClassification X d := by
  sorry

/- The identity point of the classification equivalence is the descended
   universal family.  Naming it makes the universal-family part of the
   configuration-space construction available independently of the chosen
   equivalence presentation. -/
noncomputable def unorderedConfigurationUniversalFamily
    {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    ConfigurationFamily X (unorderedConfigurationSpace X d) d :=
  (unorderedConfiguration_classifies_split_finite_etale_families X d).equivalence
    (unorderedConfigurationSpace X d) (𝟙 _)

theorem unorderedConfigurationUniversalFamily_pullback
    {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] {T : RelativeScheme S}
    (f : T ⟶ unorderedConfigurationSpace X d) :
    ConfigurationFamily.pullback f (unorderedConfigurationUniversalFamily X d) =
      (unorderedConfiguration_classifies_split_finite_etale_families X d).equivalence T f := by
  sorry

theorem configurationSpace_smooth {S : Scheme.{u}} (X : RelativeScheme S) (d r : ℕ)
    [Chapter11QuasiProjectiveOver X]
    (hX : SmoothOfRelativeDimension r X.structuralMap) :
    SmoothOfRelativeDimension (d * r)
      (configurationSpace X d).carrier.structuralMap := by
  sorry

theorem unorderedConfigurationSpace_smooth {S : Scheme.{u}} (X : RelativeScheme S) (d r : ℕ)
    [Chapter11QuasiProjectiveOver X]
    (hX : SmoothOfRelativeDimension r X.structuralMap) :
    SmoothOfRelativeDimension (d * r)
      (unorderedConfigurationSpace X d).structuralMap := by
  sorry

/- The pairwise diagonal is the equalizer of two coordinate projections.  Its
   regular-immersion statement is kept separate from the aggregate big
   diagonal, which is generally not a regular immersion at multiple
   collisions. -/
structure Chapter11PairwiseDiagonalData {S : Scheme.{u}} (X : RelativeScheme S)
    (d r : ℕ) (i j : Fin d) where
  carrier : RelativeScheme S
  inclusion : carrier ⟶ (relativePower X d).carrier
  regular : Chapter11RegularImmersion inclusion.hom r
  equal_coordinates :
    inclusion ≫ (relativePower X d).projection i =
      inclusion ≫ (relativePower X d).projection j
  characterizes : ∀ (T : RelativeScheme S) (x : T ⟶ (relativePower X d).carrier),
    x ≫ (relativePower X d).projection i =
        x ≫ (relativePower X d).projection j ↔
      ∃! y : T ⟶ carrier, y ≫ inclusion = x

theorem pairwiseDiagonal_exists {S : Scheme.{u}} (X : RelativeScheme S) (d r : ℕ)
    [Chapter11QuasiProjectiveOver X]
    (i j : Fin d) (hij : i ≠ j)
    (hX : SmoothOfRelativeDimension r X.structuralMap) :
    Nonempty (Chapter11PairwiseDiagonalData X d r i j) := by
  sorry

structure BigDiagonalData {S : Scheme.{u}} (X : RelativeScheme S) (d r : ℕ)
    [Chapter11QuasiProjectiveOver X] where
  carrier : RelativeScheme S
  inclusion : carrier ⟶ (relativePower X d).carrier
  closed : IsClosedImmersion inclusion.hom
  codimension : Chapter11FiberwiseHeightCodimension inclusion.hom r
  pairwiseDiagonals : ∀ (i j : Fin d), i ≠ j →
    Chapter11PairwiseDiagonalData X d r i j
  pairwise_factors_through_bigDiagonal :
    ∀ (i j : Fin d) (hij : i ≠ j),
      ∃ e : (pairwiseDiagonals i j hij).carrier ⟶ carrier,
        e ≫ inclusion = (pairwiseDiagonals i j hij).inclusion
  pairwise_union :
    Set.range inclusion.hom =
      (⋃ (i : Fin d), ⋃ (j : Fin d), ⋃ (hij : i ≠ j),
        Set.range ((pairwiseDiagonals i j hij).inclusion.hom))
  complement : ConfigurationSpace X d
  complement_eq :
    Set.range complement.inclusion.hom = Set.univ \ Set.range inclusion.hom

theorem bigDiagonal_exists {S : Scheme.{u}} (X : RelativeScheme S) (d r : ℕ)
    [Chapter11QuasiProjectiveOver X]
    (hd : 2 ≤ d) (hr : 0 < r)
    (hX : SmoothOfRelativeDimension r X.structuralMap) :
    Nonempty (BigDiagonalData X d r) := by
  sorry

theorem bigDiagonal_expected_codimension {S : Scheme.{u}} (X : RelativeScheme S)
    (d r : ℕ) [Chapter11QuasiProjectiveOver X]
    (hd : 2 ≤ d) (hr : 0 < r)
    (hX : SmoothOfRelativeDimension r X.structuralMap) :
    ∃ D : BigDiagonalData X d r,
      Chapter11FiberwiseHeightCodimension D.inclusion.hom r := by
  sorry

/- The source also records that passing to the finite permutation quotient does
   not change the codimension of the big diagonal.  The quotient construction
   itself is supplied by the symmetric-power package; this record keeps the
   resulting closed image and its codimension explicit. -/
structure QuotientBigDiagonalData {S : Scheme.{u}} (X : RelativeScheme S)
    (d r : ℕ) [Chapter11QuasiProjectiveOver X]
    (D : BigDiagonalData X d r) where
  carrier : RelativeScheme S
  inclusion : carrier ⟶ symmetricPower X d
  closed : IsClosedImmersion inclusion.hom
  codimension : Chapter11FiberwiseHeightCodimension inclusion.hom r
  factors_through_image :
    ∃ e : D.carrier ⟶ carrier,
      e ≫ inclusion = D.inclusion ≫ symmetricPowerMap X d
  image :
    Set.range inclusion.hom =
      Set.range (D.inclusion ≫ symmetricPowerMap X d).hom

theorem quotient_bigDiagonal_exists {S : Scheme.{u}} (X : RelativeScheme S)
    (d r : ℕ) [Chapter11QuasiProjectiveOver X]
    (hd : 2 ≤ d) (hr : 0 < r)
    (hX : SmoothOfRelativeDimension r X.structuralMap)
    (D : BigDiagonalData X d r) :
    Nonempty (QuotientBigDiagonalData X d r D) := by
  sorry

theorem curve_bigDiagonal_is_divisor_after_hypotheses {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (hd : 2 ≤ d)
    (hX : SmoothOfRelativeDimension 1 X.structuralMap) :
    ∃ D : BigDiagonalData X d 1,
        ∃ E : EffectiveCartierDivisor ((relativePower X d).carrier.carrier),
        (∃ e : E.subscheme ≅ D.carrier.carrier,
          e.hom ≫ D.inclusion.hom = E.inclusion) ∧
        (E.ideal.support : Set ((relativePower X d).carrier.carrier)) =
            Set.range D.inclusion.hom ∧
          Chapter11FiberwiseHeightCodimension D.inclusion.hom 1 := by
  sorry

/- The ordered family is the coproduct of the coordinate graphs. -/
noncomputable def configurationGraph {S : Scheme.{u}} {X : RelativeScheme S} (d : ℕ)
    (C : ConfigurationSpace X d) (i : Fin d) :
    C.carrier.carrier ⟶ pullback X.structuralMap C.carrier.structuralMap :=
  pullback.lift
    ((C.inclusion ≫ (relativePower X d).projection i).hom)
    (𝟙 C.carrier.carrier) (by sorry)

noncomputable def orderedConfigurationFamilyTotal {S : Scheme.{u}}
    {X : RelativeScheme S} (d : ℕ) (C : ConfigurationSpace X d) : Scheme.{u} :=
  ∐ fun _ : Fin d => C.carrier.carrier

noncomputable def orderedConfigurationFamilyToBase {S : Scheme.{u}}
    {X : RelativeScheme S} (d : ℕ) (C : ConfigurationSpace X d) :
    orderedConfigurationFamilyTotal d C ⟶ C.carrier.carrier :=
  Sigma.desc (fun _ : Fin d => 𝟙 C.carrier.carrier)

noncomputable def orderedConfigurationFamilyToX {S : Scheme.{u}}
    {X : RelativeScheme S} (d : ℕ) (C : ConfigurationSpace X d) :
    orderedConfigurationFamilyTotal d C ⟶
      pullback X.structuralMap C.carrier.structuralMap :=
  Sigma.desc (fun i => configurationGraph d C i)

structure OrderedConfigurationFamily {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    (C : ConfigurationSpace X d) where
  finite_etale : Chapter11FiniteEtaleOfDegree
    (orderedConfigurationFamilyToBase d C) d
  closed : IsClosedImmersion (orderedConfigurationFamilyToX d C)
  componentInclusion_open : ∀ i,
    IsOpenImmersion
      (Sigma.ι (fun _ : Fin d => C.carrier.carrier) i)
  component_inclusion_base : ∀ i,
    Sigma.ι (fun _ : Fin d => C.carrier.carrier) i ≫
        orderedConfigurationFamilyToBase d C = 𝟙 C.carrier.carrier
  component_disjoint : ∀ i j, i ≠ j →
    Disjoint
      (Scheme.Hom.opensRange
        (Sigma.ι (fun _ : Fin d => C.carrier.carrier) i)
        (H := componentInclusion_open i))
      (Scheme.Hom.opensRange
        (Sigma.ι (fun _ : Fin d => C.carrier.carrier) j)
        (H := componentInclusion_open j))
  /-- The coordinate graphs are disjoint in the ambient curve/product. -/
  graphs_disjoint : ∀ i j, i ≠ j →
    Disjoint
      (Set.range
        ((Sigma.ι (fun _ : Fin d => C.carrier.carrier) i) ≫
          orderedConfigurationFamilyToX d C))
      (Set.range
        ((Sigma.ι (fun _ : Fin d => C.carrier.carrier) j) ≫
          orderedConfigurationFamilyToX d C))

theorem ordered_configuration_family_exists {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    OrderedConfigurationFamily X d (configurationSpace X d) := by
  sorry

theorem ordered_configuration_family_graphs_disjoint {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (i j : Fin d) (hij : i ≠ j) :
    Disjoint
      (Set.range
        ((Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) i) ≫
          orderedConfigurationFamilyToX d (configurationSpace X d)))
      (Set.range
        ((Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) j) ≫
          orderedConfigurationFamilyToX d (configurationSpace X d))) := by
  exact (ordered_configuration_family_exists X d).graphs_disjoint i j hij

noncomputable def configurationAmbientPermutationMap {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (σ : Equiv.Perm (Fin d)) :
    pullback X.structuralMap (configurationSpace X d).carrier.structuralMap ⟶
      pullback X.structuralMap (configurationSpace X d).carrier.structuralMap :=
  pullback.lift
    (pullback.fst X.structuralMap (configurationSpace X d).carrier.structuralMap)
    ((pullback.snd X.structuralMap (configurationSpace X d).carrier.structuralMap) ≫
      ((configurationAction X d).hom σ).hom) (by sorry)

/- The comparison map on the ambient pullbacks induced by the quotient map. -/
noncomputable def configurationFamilyAmbientMap {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    pullback X.structuralMap (configurationSpace X d).carrier.structuralMap ⟶
      pullback X.structuralMap (unorderedConfigurationSpace X d).structuralMap :=
  pullback.lift
    (pullback.fst X.structuralMap (configurationSpace X d).carrier.structuralMap)
    (pullback.snd X.structuralMap (configurationSpace X d).carrier.structuralMap ≫
      (unorderedConfigurationMap X d).hom) (by sorry)

/- Equivariance of the ordered family is descent data, so it must include the
   group laws for the permutation action rather than unrelated isomorphisms
   indexed by individual permutations. -/
structure OrderedConfigurationFamilyEquivariance {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] where
  action : Equiv.Perm (Fin d) →
    (orderedConfigurationFamilyTotal d (configurationSpace X d) ⟶
      orderedConfigurationFamilyTotal d (configurationSpace X d))
  action_one : action 1 = 𝟙 _
  action_mul : ∀ σ τ, action (σ * τ) = action σ ≫ action τ
  action_isIso : ∀ σ, IsIso (action σ)
  over_base : ∀ σ,
    action σ ≫ orderedConfigurationFamilyToBase d (configurationSpace X d) =
      orderedConfigurationFamilyToBase d (configurationSpace X d) ≫
        ((configurationAction X d).hom σ).hom
  over_X : ∀ σ,
    action σ ≫ orderedConfigurationFamilyToX d (configurationSpace X d) =
      orderedConfigurationFamilyToX d (configurationSpace X d) ≫
        configurationAmbientPermutationMap X d σ
  component : ∀ σ : Equiv.Perm (Fin d), ∀ i : Fin d,
    (Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) i) ≫
        action σ =
      ((configurationAction X d).hom σ).hom ≫
        Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) (σ.symm i)

abbrev configurationFamilyPullback {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (family : RelativeFiniteEtaleSubscheme X (unorderedConfigurationSpace X d) d) :
    RelativeFiniteEtaleSubscheme X (configurationSpace X d).carrier d :=
  RelativeFiniteEtaleSubscheme.pullback family (unorderedConfigurationMap X d)

/- The pullback of a descended family carries the permutation action induced
   by the action on the configuration base.  Recording this action makes the
   comparison with the ordered family genuine descent data, rather than merely
   an isomorphism of the two underlying schemes. -/
structure ConfigurationFamilyPullbackAction {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (family : RelativeFiniteEtaleSubscheme X (unorderedConfigurationSpace X d) d) where
  hom : Equiv.Perm (Fin d) →
    ((configurationFamilyPullback X d family).carrier ⟶
      (configurationFamilyPullback X d family).carrier)
  one_hom : hom 1 = 𝟙 _
  mul_hom : ∀ σ τ, hom (σ * τ) = hom σ ≫ hom τ
  isIso : ∀ σ, IsIso (hom σ)
  over_base : ∀ σ,
    hom σ ≫ (configurationFamilyPullback X d family).mapToBase =
      (configurationFamilyPullback X d family).mapToBase ≫
        ((configurationAction X d).hom σ).hom
  over_X : ∀ σ,
    hom σ ≫ (configurationFamilyPullback X d family).mapToX =
      (configurationFamilyPullback X d family).mapToX ≫
        configurationAmbientPermutationMap X d σ

/- A descended family must identify its pullback along the quotient torsor with
   the explicit coproduct of the coordinate graphs. -/
structure ConfigurationFamilyDescent {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] where
  family : RelativeFiniteEtaleSubscheme X (unorderedConfigurationSpace X d) d
  family_is_universal :
    family = unorderedConfigurationUniversalFamily X d
  pullbackAction : ConfigurationFamilyPullbackAction X d family
  comparison :
    orderedConfigurationFamilyTotal d (configurationSpace X d) ⟶
      (configurationFamilyPullback X d family).carrier
  comparison_isIso : IsIso comparison
  ordered_equivariance : OrderedConfigurationFamilyEquivariance X d
  comparison_equivariant : ∀ σ : Equiv.Perm (Fin d),
    ordered_equivariance.action σ ≫ comparison =
      comparison ≫ pullbackAction.hom σ
  comparison_over_base :
    comparison ≫ (configurationFamilyPullback X d family).mapToBase =
      orderedConfigurationFamilyToBase d (configurationSpace X d)
  comparison_over_X :
    comparison ≫ (configurationFamilyPullback X d family).mapToX =
      orderedConfigurationFamilyToX d (configurationSpace X d)

theorem ordered_configuration_family_equivariant {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    Nonempty (OrderedConfigurationFamilyEquivariance X d) := by
  sorry

theorem configuration_family_descends {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Nonempty (ConfigurationFamilyDescent X d) := by
  sorry

/- The aggregate package is the interface consumed by later chapters.  Its
   fields package the open complement, permutation quotient, and classifying
   family constructed above, including the closed big diagonal. -/
theorem configuration_space_data_exists {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Nonempty (Chapter11ConfigurationSpaceData X d) := by
  sorry

noncomputable def configurationSpaceData {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] : Chapter11ConfigurationSpaceData X d :=
  Classical.choice (configuration_space_data_exists X d)

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
