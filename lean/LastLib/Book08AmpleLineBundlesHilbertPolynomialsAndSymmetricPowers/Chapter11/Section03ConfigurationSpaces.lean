import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section02SheafQuotientsAndOrbitFunctors

namespace LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeScheme

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

/- SOURCE_ISSUE: §11.3 says "its finite quotient has the same codimension"
   without specifying whether codimension is stalkwise, fiberwise, or a cycle
   codimension.  The aggregate big diagonal is generally not a regular
   immersion at multiple collisions, so the interface below records closedness
   and local ideal-height codimension; the pairwise regular-immersion claim is
   not silently promoted to a claim about the whole union. -/
structure BigDiagonalData {S : Scheme.{u}} (X : RelativeScheme S) (d r : ℕ)
    [Chapter11QuasiProjectiveOver X] where
  carrier : RelativeScheme S
  inclusion : carrier ⟶ (relativePower X d).carrier
  closed : IsClosedImmersion inclusion.hom
  codimension : Chapter11FiberwiseHeightCodimension inclusion.hom r
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

theorem curve_bigDiagonal_is_divisor_after_hypotheses {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (hd : 2 ≤ d)
    (hX : SmoothOfRelativeDimension 1 X.structuralMap) :
    ∃ D : BigDiagonalData X d 1,
        ∃ E : EffectiveCartierDivisor ((relativePower X d).carrier.carrier),
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

theorem ordered_configuration_family_exists {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    OrderedConfigurationFamily X d (configurationSpace X d) := by
  sorry

theorem ordered_configuration_family_graphs_disjoint {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (i j : Fin d) (hij : i ≠ j) :
    Disjoint (Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) i).opensRange
      (Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) j).opensRange := by
  exact disjoint_opensRange_sigmaι _ _ _ hij

noncomputable def configurationAmbientPermutationMap {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (σ : Equiv.Perm (Fin d)) :
    pullback X.structuralMap (configurationSpace X d).carrier.structuralMap ⟶
      pullback X.structuralMap (configurationSpace X d).carrier.structuralMap :=
  pullback.lift
    (pullback.fst X.structuralMap (configurationSpace X d).carrier.structuralMap)
    ((pullback.snd X.structuralMap (configurationSpace X d).carrier.structuralMap) ≫
      ((configurationAction X d).hom σ).hom) (by sorry)

theorem ordered_configuration_family_equivariant {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    ∀ σ : Equiv.Perm (Fin d),
      ∃ e : orderedConfigurationFamilyTotal d (configurationSpace X d) ⟶
        orderedConfigurationFamilyTotal d (configurationSpace X d),
        IsIso e ∧
          e ≫ orderedConfigurationFamilyToBase d (configurationSpace X d) =
            orderedConfigurationFamilyToBase d (configurationSpace X d) ≫
              ((configurationAction X d).hom σ).hom ∧
          e ≫ orderedConfigurationFamilyToX d (configurationSpace X d) =
            orderedConfigurationFamilyToX d (configurationSpace X d) ≫
              configurationAmbientPermutationMap X d σ ∧
            ∀ i : Fin d,
            (Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) i) ≫ e =
              ((configurationAction X d).hom σ).hom ≫
              Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) (σ.symm i) := by
  sorry

/- The comparison map on the ambient pullbacks induced by the quotient map. -/
noncomputable def configurationFamilyAmbientMap {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    pullback X.structuralMap (configurationSpace X d).carrier.structuralMap ⟶
      pullback X.structuralMap (unorderedConfigurationSpace X d).structuralMap :=
  pullback.lift
    (pullback.fst X.structuralMap (configurationSpace X d).carrier.structuralMap)
    (pullback.snd X.structuralMap (configurationSpace X d).carrier.structuralMap ≫
      (unorderedConfigurationMap X d).hom) (by sorry)

/- A descended family must identify its pullback along the quotient torsor with
   the explicit coproduct of the coordinate graphs. -/
structure ConfigurationFamilyDescent {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] where
  family : RelativeFiniteEtaleSubscheme X (unorderedConfigurationSpace X d) d
  comparison :
    orderedConfigurationFamilyTotal d (configurationSpace X d) ⟶ family.carrier
  comparison_isIso : IsIso comparison
  comparison_invariant :
    ∀ σ : Equiv.Perm (Fin d),
      ∃ e : orderedConfigurationFamilyTotal d (configurationSpace X d) ⟶
          orderedConfigurationFamilyTotal d (configurationSpace X d),
        IsIso e ∧
          (∀ i : Fin d,
            (Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) i) ≫ e =
              ((configurationAction X d).hom σ).hom ≫
                Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) (σ.symm i)) ∧
          e ≫ comparison = comparison
  comparison_over_base :
    comparison ≫ family.mapToBase =
      orderedConfigurationFamilyToBase d (configurationSpace X d) ≫
        (unorderedConfigurationMap X d).hom
  comparison_over_X :
    comparison ≫ family.mapToX =
      orderedConfigurationFamilyToX d (configurationSpace X d) ≫
        configurationFamilyAmbientMap X d

theorem configuration_family_descends {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Nonempty (ConfigurationFamilyDescent X d) := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
