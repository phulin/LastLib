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
theorem configurationAction_exists {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Nonempty (RelativeAction (configurationSpace X d).carrier (Equiv.Perm (Fin d))) := by
  sorry

noncomputable def configurationAction {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    RelativeAction (configurationSpace X d).carrier (Equiv.Perm (Fin d)) :=
  Classical.choice (configurationAction_exists X d)

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

theorem unorderedConfiguration_finite_etale_torsor {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    Chapter11FiniteEtaleOfDegree (unorderedConfigurationMap X d).hom (Nat.factorial d) ∧
      Etale (unorderedConfigurationMap X d).hom := by
  sorry

theorem unorderedConfiguration_surjective {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    Surjective (unorderedConfigurationMap X d).hom := by
  exact (unorderedConfigurationQuotient X d).surjective

/-- The splitting condition for a particular finite étale family. -/
def Chapter11SubschemeSplitsAsDisjointSections {S : Scheme.{u}}
    {X T : RelativeScheme S} {d : ℕ} (Z : RelativeFiniteEtaleSubscheme X T d) : Prop :=
  ∃ (U : Scheme.{u}) (u : U ⟶ T.carrier),
    Etale u ∧ Surjective u ∧
      ∃ (s : Fin d → (U ⟶ Z.carrier)),
        Pairwise (fun i j => s i ≠ s j) ∧
          ∀ i, s i ≫ Z.mapToBase = u

abbrev ConfigurationFamily {S : Scheme.{u}} (X T : RelativeScheme S) (d : ℕ) :=
  {Z : RelativeFiniteEtaleSubscheme X T d //
    Chapter11SubschemeSplitsAsDisjointSections Z}

theorem unorderedConfiguration_classifies_split_finite_etale_families
    {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    ∀ T : RelativeScheme S,
      Nonempty ((T ⟶ unorderedConfigurationSpace X d) ≃
        ConfigurationFamily X T d) := by
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

/- The big diagonal is recorded independently of the open complement so that
   codimension and divisor assertions can use whichever canonical codimension
   API is available later. -/
structure BigDiagonalData {S : Scheme.{u}} (X : RelativeScheme S) (d r : ℕ)
    [Chapter11QuasiProjectiveOver X] where
  carrier : RelativeScheme S
  inclusion : carrier ⟶ (relativePower X d).carrier
  isClosed : IsClosedImmersion inclusion.hom
  complement : ConfigurationSpace X d
  codimension : ℕ
  codimension_eq : codimension = r

theorem bigDiagonal_exists {S : Scheme.{u}} (X : RelativeScheme S) (d r : ℕ)
    [Chapter11QuasiProjectiveOver X]
    (hd : 2 ≤ d) (hr : 0 < r)
    (hX : SmoothOfRelativeDimension r X.structuralMap) :
    Nonempty (BigDiagonalData X d r) := by
  sorry

theorem bigDiagonal_expected_codimension {S : Scheme.{u}} (X : RelativeScheme S)
    (d r : ℕ) [Chapter11QuasiProjectiveOver X]
    (_hX : SmoothOfRelativeDimension r X.structuralMap)
    (D : BigDiagonalData X d r) : D.codimension = r :=
  D.codimension_eq

/- SOURCE_ISSUE: the source says "On a relative curve it is a divisor after
   suitable hypotheses" without specifying separation, smoothness, or the
   precise codimension/divisor convention.  This draft records the minimal
   smooth quasi-projective hypothesis available in this chapter interface and
   leaves the divisor witness to the fixup pass. -/
theorem curve_bigDiagonal_is_divisor_after_hypotheses {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (hd : 2 ≤ d)
    (hX : SmoothOfRelativeDimension 1 X.structuralMap) :
    ∃ D : BigDiagonalData X d 1, D.codimension = 1 := by
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
  total : Scheme.{u}
  toBase : total ⟶ C.carrier.carrier
  toX : total ⟶ pullback X.structuralMap C.carrier.structuralMap
  over_base : toX ≫ pullback.snd X.structuralMap C.carrier.structuralMap = toBase
  finite_etale : Chapter11FiniteEtaleOfDegree toBase d
  closed : IsClosedImmersion toX
  componentInclusion : Fin d → (C.carrier.carrier ⟶ total)
  componentInclusion_open : ∀ i, IsOpenImmersion (componentInclusion i)
  component_inclusion_base : ∀ i,
    componentInclusion i ≫ toBase = 𝟙 C.carrier.carrier
  component_disjoint : ∀ i j, i ≠ j →
    Disjoint
      (Scheme.Hom.opensRange (componentInclusion i) (H := componentInclusion_open i))
      (Scheme.Hom.opensRange (componentInclusion j) (H := componentInclusion_open j))

noncomputable def ordered_configuration_family_exists {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    OrderedConfigurationFamily X d (configurationSpace X d) := by
  sorry

theorem ordered_configuration_family_graphs_disjoint {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X]
    (i j : Fin d) (hij : i ≠ j) :
    Disjoint (Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) i).opensRange
      (Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) j).opensRange := by
  exact disjoint_opensRange_sigmaι _ _ _ hij

theorem ordered_configuration_family_equivariant {S : Scheme.{u}}
    (X : RelativeScheme S) (d : ℕ) [Chapter11QuasiProjectiveOver X] :
    ∀ σ : Equiv.Perm (Fin d),
      ∃ e : orderedConfigurationFamilyTotal d (configurationSpace X d) ⟶
        orderedConfigurationFamilyTotal d (configurationSpace X d),
        IsIso e ∧
          e ≫ orderedConfigurationFamilyToBase d (configurationSpace X d) =
            orderedConfigurationFamilyToBase d (configurationSpace X d) ∧
          ∀ i : Fin d,
            (Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) i) ≫ e =
              Sigma.ι (fun _ : Fin d => (configurationSpace X d).carrier.carrier) (σ i) := by
  sorry

theorem configuration_family_descends {S : Scheme.{u}} (X : RelativeScheme S) (d : ℕ)
    [Chapter11QuasiProjectiveOver X] :
    ∃ Z : RelativeFiniteEtaleSubscheme X (unorderedConfigurationSpace X d) d,
      Chapter11SubschemeSplitsAsDisjointSections Z := by
  sorry

end

end LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
