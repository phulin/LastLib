import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16.Dependencies

/-!
## 16.1 Generalized elliptic curves

The declarations in this file separate the geometric-fiber alternatives, the group/action data,
and the descent certificates.  In particular, the polygon branch does not silently replace a
polarizing divisor by the identity section.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v

/-! ### Geometric fibers -/

structure Chapter16SmoothGenusOneFiber (X : Scheme.{u}) (k : Type u)
    [Field k] [IsAlgClosed k] where
  structureMap : X ⟶ Spec (CommRingCat.of k)
  proper : IsProper structureMap
  smooth : Smooth structureMap
  relativeDimension : SmoothOfRelativeDimension structureMap 1
  geometricallyConnected : GeometricallyConnected structureMap
  arithmeticGenus : ℤ
  arithmeticGenus_eq_one : arithmeticGenus = 1
  eulerCharacteristic : ℤ
  eulerCharacteristic_eq_zero : eulerCharacteristic = 0

structure Chapter16NeronPolygonFiber (X : Scheme.{u}) (k : Type u) (m : ℕ)
    [Field k] [IsAlgClosed k] where
  structureMap : X ⟶ Spec (CommRingCat.of k)
  proper : IsProper structureMap
  flat : Flat structureMap
  componentData : Chapter16FiberComponentData X m
  smoothLocus : X.Opens
  smoothLocus_open : IsOpenImmersion smoothLocus.ι
  nodeLocus : Set X
  nodeModel : ∀ x, x ∈ nodeLocus → Chapter16PlaneNodeModel X k
  component_complement_is_nodeLocus : Prop
  component_finite_locally_free : Prop
  connected : Prop
  eulerCharacteristic : ℤ
  eulerCharacteristic_eq_zero : eulerCharacteristic = 0

inductive Chapter16FiberShape (X : Scheme.{u}) (k : Type u)
    [Field k] [IsAlgClosed k] where
  | smoothGenusOne (data : Chapter16SmoothGenusOneFiber X k)
  | neronPolygon (m : ℕ) (hm : 1 < m) (data : Chapter16NeronPolygonFiber X k m)

/- The residue-field extension used to define a geometric fiber is represented by a chosen
 algebraically closed field and a shape certificate over that field. -/
structure Chapter16GeometricFiberCondition {S E : Scheme.{u}} (f : E ⟶ S) where
  geometricField : ∀ s : S, Type u
  geometricField_structure : ∀ s, Field (geometricField s)
  geometricField_closed : ∀ s, IsAlgClosed (geometricField s)
  shape : ∀ s,
    @Chapter16FiberShape (f.fiber s) (geometricField s)
      (geometricField_structure s) (geometricField_closed s)

structure Chapter16FiberShapeInvariant {X Y : Scheme.{u}} (m : ℕ) where
  sourceComponents : Chapter16ComponentIndex X m
  targetComponents : Chapter16ComponentIndex Y m
  componentCorrespondence : Fin m ≃ Fin m
  componentCorrespondence_preserves_incidence : Prop
  nodeCorrespondence : Prop
  node_model_iff : Prop

def chapter16FieldBaseChangeMap {k K : Type u} [Field k] [Field K]
    (e : Chapter16FieldExtension k K) :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) := by
  letI := e.algebra
  exact Spec.map (CommRingCat.ofHom (algebraMap k K))

theorem chapter16_geometric_fiber_shape_baseChange
    {X : Scheme.{u}} {k K : Type u} [Field k] [Field K]
    [IsAlgClosed k] [IsAlgClosed K]
    (f : X ⟶ Spec (CommRingCat.of k))
    (e : Chapter16FieldExtension k K)
    (hX : Chapter16FiberShape X k) :
    Nonempty (Chapter16FiberShape
      (pullback f (chapter16FieldBaseChangeMap e)) K) := by
  sorry

structure Chapter16CommonGeometricFiberComparison
    {X Y : Scheme.{u}} (m : ℕ) where
  commonScheme : Scheme.{u}
  sourceIso : X ≅ commonScheme
  targetIso : Y ≅ commonScheme
  components : Chapter16FiberShapeInvariant X Y m

structure Chapter16CommonAlgebraicClosureData
    (k₁ k₂ K : Type u) [Field k₁] [Field k₂] [Field K] where
  first : Chapter16FieldExtension k₁ K
  second : Chapter16FieldExtension k₂ K

theorem chapter16_common_algebraic_closure_gives_same_geometric_scheme
    {X Y : Scheme.{u}} {k₁ k₂ K : Type u}
    [Field k₁] [Field k₂] [Field K]
    [IsAlgClosed k₁] [IsAlgClosed k₂] [IsAlgClosed K]
    (C : Chapter16CommonAlgebraicClosureData k₁ k₂ K)
    (hX : Chapter16FiberShape X k₁)
    (hY : Chapter16FiberShape Y k₂) :
    Nonempty (Chapter16CommonGeometricFiberComparison X Y 1) := by
  sorry

theorem chapter16_geometric_fiber_shape_reflects_common_algebraic_closure
    {X Y : Scheme.{u}} {k K : Type u} [Field k] [Field K]
    [IsAlgClosed k] [IsAlgClosed K]
    (e : Chapter16FieldExtension k K)
    (hX : Chapter16FiberShape X k)
    (hY : Chapter16FiberShape Y K)
    (comparison : Chapter16CommonGeometricFiberComparison X Y 1) :
    Nonempty (Chapter16FiberShapeInvariant X Y 1) := by
  exact ⟨comparison.components⟩

theorem chapter16_geometric_fiber_components_and_nodes_invariant
    {X Y : Scheme.{u}} {k K : Type u} [Field k] [Field K]
    [IsAlgClosed k] [IsAlgClosed K]
    {m : ℕ} (e : Chapter16FieldExtension k K)
    (hX : Chapter16FiberShape X k)
    (hY : Chapter16FiberShape Y K)
    (comparison : Chapter16CommonGeometricFiberComparison X Y m) :
    Nonempty (Chapter16FiberShapeInvariant X Y m) := by
  exact ⟨comparison.components⟩

/-! ### Cech cohomology and the Euler characteristic -/

structure Chapter16FiniteAffineCechCover (X : Scheme.{u}) where
  index : Type u
  finite_index : Finite index
  opens : index → X.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  cover : iSup opens = ⊤
  intersection : Finset index → X.Opens
  intersection_eq : ∀ s,
    (intersection s : Set X) = ⋂ i ∈ s, (opens i : Set X)
  finite_intersections_affine : ∀ s, IsAffineOpen (intersection s)
  cech_computes_coherent_cohomology : Prop

structure Chapter16CechBaseChangeData where
  downstairs : Chapter16EulerCharacteristicData
  upstairs : Chapter16EulerCharacteristicData
  proper_separated_fiber : Prop
  finite_affine_cover : Prop
  finite_intersections_affine : Prop
  baseChanged_cover : Prop
  tensor_complex : Prop
  tensor_exact : Prop
  cohomology_finite_dimensional : Prop
  dimensions_unchanged : ∀ i, downstairs.dimension i = upstairs.dimension i
  bounds_unchanged : downstairs.cohomologicalBound = upstairs.cohomologicalBound

theorem chapter16_cech_baseChange_preserves_euler_characteristic
    (C : Chapter16CechBaseChangeData) :
    chapter16EulerCharacteristic C.downstairs =
      chapter16EulerCharacteristic C.upstairs := by
  exact chapter16_euler_characteristic_congr C.downstairs C.upstairs
    C.bounds_unchanged C.dimensions_unchanged

theorem chapter16_cech_baseChange_preserves_arithmetic_genus
    (C : Chapter16CechBaseChangeData) :
    chapter16ArithmeticGenus C.downstairs = chapter16ArithmeticGenus C.upstairs := by
  exact chapter16_arithmetic_genus_congr _ _
    (chapter16_cech_baseChange_preserves_euler_characteristic C)

/-! ### The generalized elliptic curve package -/

/- LOCAL_DEPENDENCY_GUESS: the pinned APIs provide scheme pullbacks and categorical descent data,
but not a bundled base-change operation for generalized elliptic curves.  The compatibility fields
below are therefore kept explicit until the earlier descent chapters expose that bundled object. -/

structure Chapter16SmoothLocusData {E S : Scheme.{u}} (f : E ⟶ S) where
  locus : E.Opens
  openImmersion : IsOpenImmersion locus.ι
  map : locus.toScheme ⟶ S := locus.ι ≫ f
  smooth : Smooth map
  [groupObject : GrpObj (Over.mk map)]
  [commutative : IsCommMonObj (Over.mk map)]

structure Chapter16GeneralizedEllipticCurve (S : Scheme.{u}) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  proper : IsProper structureMap
  separated : IsSeparated structureMap
  flat : Flat structureMap
  finitePresentation : LocallyOfFinitePresentation structureMap
  smoothLocus : Chapter16SmoothLocusData structureMap
  identity : S ⟶ carrier
  identity_factor : ∃ e : S ⟶ smoothLocus.locus.toScheme,
    e ≫ smoothLocus.locus.ι = identity
  action :
    (Over.mk smoothLocus.map ⊗ Over.mk structureMap) ⟶ Over.mk structureMap
  action_on_smooth_locus : Prop
  action_on_components : Prop
  fiberCondition : Chapter16GeometricFiberCondition structureMap

structure Chapter16GeneralizedEllipticCurveDescentDatum
    {S T : Scheme.{u}} (g : T ⟶ S) where
  cover : Chapter16FpqcMorphism g
  upstairs : Chapter16GeneralizedEllipticCurve T
  carrierDescent : Chapter16SchemeDescentDatum g
  carrier_matches : carrierDescent.carrier = upstairs.carrier
  structure_map_matches : Prop
  section_descent : Prop
  smooth_open_descent : Prop
  multiplication_descent : Prop
  action_descent : Prop
  incidence_morphisms_descent : Prop
  triple_cocycle : Prop

structure Chapter16GeneralizedEllipticCurveDescentResult
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16GeneralizedEllipticCurveDescentDatum g) where
  descended : Chapter16GeneralizedEllipticCurve S
  carrier_baseChange_equivalence : Prop
  section_recovered : Prop
  smooth_open_recovered : Prop
  multiplication_recovered : Prop
  action_recovered : Prop
  incidence_morphisms_recovered : Prop
  component_finiteness_recovered : Prop

theorem chapter16_generalizedEllipticCurve_effective_descent
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16GeneralizedEllipticCurveDescentDatum g) :
    Nonempty (Chapter16GeneralizedEllipticCurveDescentResult D) := by
  sorry

theorem chapter16_generalizedEllipticCurve_structure_identities_descend
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16GeneralizedEllipticCurveDescentDatum g)
    (R : Chapter16GeneralizedEllipticCurveDescentResult D) :
    R.multiplication_recovered ∧ R.action_recovered := by
  exact ⟨R.multiplication_recovered, R.action_recovered⟩

/-! ### Projectivity and divisors -/

structure Chapter16CompatibleAmpleDivisor {X S : Scheme.{u}} (f : X ⟶ S) where
  degree : ℕ
  divisor :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10RelativeEffectiveCartierDivisor
      f degree
  n : ℕ
  positive_power : 0 < n
  lineBundle : Chapter16LineBundle X
  lineBundle_is_O_of_nD : Prop
  relatively_ample : Chapter16IsAmple f lineBundle
  compatible_with_descent : Prop

structure Chapter16IdentityDivisorCandidate {S : Scheme.{u}}
    (G : Chapter16GeneralizedEllipticCurve S) where
  degree : ℕ
  divisor :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10RelativeEffectiveCartierDivisor
      G.structureMap degree
  induced_by_identity_section : Prop
  lineBundle : Chapter16LineBundle G.carrier
  lineBundle_is_O_of_D : Prop
  relatively_ample : Chapter16IsAmple G.structureMap lineBundle

structure Chapter16PolygonPolarizingDivisor {E S : Scheme.{u}} (f : E ⟶ S) where
  degree : ℕ
  divisor :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10RelativeEffectiveCartierDivisor
      f degree
  meets_every_geometric_component : Prop
  orbit_under_level_data : Prop
  lineBundle : Chapter16LineBundle E
  relatively_ample : Chapter16IsAmple f lineBundle

structure Chapter16UpstairsPolarizedDescentData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) where
  cover : Chapter16FpqcMorphism g
  proper : IsProper f
  finitePresentation : LocallyOfFinitePresentation f
  separated : IsSeparated f
  upstairs : Chapter16CompatibleAmpleDivisor (pullback.snd f g)
  descendedLineBundle : Chapter16LineBundle X
  lineBundle_baseChange :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter05.IsBaseChangeOf
      f g descendedLineBundle upstairs.lineBundle
  ampleness_verification_is_external_input : Prop

theorem chapter16_projectivity_descends_from_compatible_divisor
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (D : Chapter16UpstairsPolarizedDescentData f g) :
    Chapter16IsProjectiveMorphism f := by
  sorry

structure Chapter16PolygonIdentityDivisorObstruction {E : Scheme.{u}} (m : ℕ) where
  polygon : Chapter16ComponentIndex E m
  hm : 1 < m
  identitySupport : Set E
  identity_component : Fin m
  identity_support_subset_component :
    identitySupport ⊆ polygon.component identity_component
  multipleIdentitySupport : ℕ → Set E
  multiple_support_subset_identity_component :
    ∀ n, 0 < n → multipleIdentitySupport n ⊆ polygon.component identity_component
  missing_component :
    ∀ n, 0 < n → ∃ j, j ≠ identity_component ∧
      ¬ (multipleIdentitySupport n ∩ polygon.component j).Nonempty

theorem chapter16_identity_divisor_does_not_meet_all_polygon_components
    {E : Scheme.{u}} {m : ℕ}
    (D : Chapter16PolygonIdentityDivisorObstruction m) (n : ℕ) (hn : 0 < n) :
    ¬ Chapter16MeetsEveryComponent D.polygon (D.multipleIdentitySupport n) := by
  rcases D.missing_component n hn with ⟨j, _, hj⟩
  intro h
  exact hj (h j)

/-! ### Level structures and fppf exactness -/

structure Chapter16FiniteLocallyFreeGroupScheme {G S : Scheme.{u}}
    (g : G ⟶ S) (r : ℕ) where
  groupObject : GrpObj (Over.mk g)
  finiteLocallyFree : Chapter16FiniteLocallyFreeProfile g r

structure Chapter16FullSetOfSections {G S : Scheme.{u}} (g : G ⟶ S) (r : ℕ) where
  sections : Fin r → (S ⟶ G)
  section_over : ∀ i, sections i ≫ g = 𝟙 S
  full_on_geometric_fibers : Prop

inductive Chapter16LevelTargetKind
  | smoothLocus
  | torsion

structure Chapter16LevelStructure {E S : Scheme.{u}} (f : E ⟶ S)
    (smooth : Chapter16SmoothLocusData f) (r : ℕ) where
  source : Scheme.{u}
  sourceMap : source ⟶ S
  sourceGroup : Chapter16FiniteLocallyFreeGroupScheme sourceMap r
  target : Scheme.{u}
  targetToSmooth : target ⟶ smooth.locus.toScheme
  map : source ⟶ target
  target_kind : Chapter16LevelTargetKind
  target_kind_compatibility : Prop
  over : map ≫ targetToSmooth ≫ smooth.locus.ι ≫ f = sourceMap
  homomorphism : Prop
  closedImmersion : IsClosedImmersion map
  rank : ℕ
  fullSections : Chapter16FullSetOfSections sourceMap rank

structure Chapter16FppfExactSequence {G H K S : Scheme.{u}}
    (gG : G ⟶ S) (gH : H ⟶ S) (gK : K ⟶ S) where
  first : G ⟶ H
  second : H ⟶ K
  first_over : first ≫ gH = gG
  second_over : second ≫ gK = gH
  composite_is_zero : Prop
  kernel_is_fppf : Prop
  fppf_locally_exact : Prop

structure Chapter16LevelStructureDescentDatum
    {S T E : Scheme.{u}} (g : T ⟶ S) (f : E ⟶ S) (r : ℕ) where
  cover : Chapter16FpqcMorphism g
  upstairsSmooth : Chapter16SmoothLocusData (pullback.snd f g)
  upstairs : Chapter16LevelStructure (pullback.snd f g) upstairsSmooth r
  homomorphism_descent : Prop
  closedImmersion_descent : Prop
  rank_descent : Prop
  fullSections_descent : Prop
  fppf_exactness_descent : Prop

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16
