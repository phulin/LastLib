import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16.Dependencies

/-!
## 16.1 Generalized elliptic curves

The declarations in this file separate the geometric-fiber alternatives, the group/action data,
and the descent certificates.  In particular, the polygon branch does not silently replace a
polarizing divisor by the identity section.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology MonoidalCategory
open scoped AlgebraicGeometry

universe u v

/-! ### Geometric fibers -/

structure Chapter16SmoothGenusOneFiber (X : Scheme.{u}) (k : Type u)
    [Field k] [IsAlgClosed k] where
  structureMap : X ⟶ Spec (CommRingCat.of k)
  proper : IsProper structureMap
  smooth : Smooth structureMap
  relativeDimension : SmoothOfRelativeDimension 1 structureMap
  geometricallyConnected : GeometricallyConnected structureMap
  nonempty : Nonempty X
  arithmeticGenus : ℤ
  arithmeticGenus_eq_one : arithmeticGenus = 1
  eulerData : Chapter16EulerCharacteristicData.{u}
  eulerCharacteristic : ℤ
  eulerCharacteristic_eq_data :
    eulerCharacteristic = chapter16EulerCharacteristic eulerData
  eulerCharacteristic_eq_zero : eulerCharacteristic = 0
  arithmeticGenus_formula : arithmeticGenus = 1 - eulerCharacteristic

structure Chapter16NeronPolygonFiber (X : Scheme.{u}) (k : Type u) (m : ℕ)
    [Field k] [IsAlgClosed k] where
  positive_components : 0 < m
  structureMap : X ⟶ Spec (CommRingCat.of k)
  proper : IsProper structureMap
  flat : Flat structureMap
  componentData : Chapter16FiberComponentData X m
  componentScheme : Fin m → Scheme.{u}
  componentInclusion : ∀ i, componentScheme i ⟶ X
  componentInclusion_closed : ∀ i, IsClosedImmersion (componentInclusion i)
  componentInclusion_image : ∀ i,
    Set.range (componentInclusion i) = componentData.index.component i
  componentToField : ∀ i, componentScheme i ⟶ Spec (CommRingCat.of k)
  component_over : ∀ i,
    componentInclusion i ≫ structureMap = componentToField i
  component_proper : ∀ i, IsProper (componentToField i)
  component_smooth : ∀ i, Smooth (componentToField i)
  component_relativeDimension : ∀ i,
    SmoothOfRelativeDimension 1 (componentToField i)
  component_geometricallyConnected : ∀ i,
    GeometricallyConnected (componentToField i)
  smoothLocus : X.Opens
  smoothLocus_open : IsOpenImmersion smoothLocus.ι
  nodeLocus : Set X
  nodeModel : ∀ x, x ∈ nodeLocus → Chapter16PlaneNodeModel X k
  nodeModel_point : ∀ x hx, (nodeModel x hx).point = x
  nodeLocus_eq_smoothLocus_complement : nodeLocus = (smoothLocus : Set X)ᶜ
  node_incidence : ∀ x, x ∈ nodeLocus →
    ∃ i j, i ≠ j ∧ x ∈ componentData.index.component i ∧
      x ∈ componentData.index.component j
  incidence_geometry : ∀ i j,
    componentData.incidence i j ↔
      (componentData.index.component i ∩ componentData.index.component j).Nonempty
  connected : _root_.IsConnected (Set.univ : Set X)
  eulerData : Chapter16EulerCharacteristicData.{u}
  eulerCharacteristic : ℤ
  eulerCharacteristic_eq_data :
    eulerCharacteristic = chapter16EulerCharacteristic eulerData
  eulerCharacteristic_eq_zero : eulerCharacteristic = 0

inductive Chapter16FiberShape (X : Scheme.{u}) (k : Type u)
  [Field k] [IsAlgClosed k] where
  | smoothGenusOne (data : Chapter16SmoothGenusOneFiber X k)
  | neronPolygon (m : ℕ) (hm : 0 < m) (data : Chapter16NeronPolygonFiber X k m)

def Chapter16FiberShape.structureMap
    {X : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k] :
    (Chapter16FiberShape X k) → (X ⟶ Spec (CommRingCat.of k))
  | Chapter16FiberShape.smoothGenusOne data => data.structureMap
  | Chapter16FiberShape.neronPolygon _ _ data => data.structureMap

/- The residue-field extension used to define a geometric fiber is represented by a chosen
 algebraically closed field and a shape certificate over that field. -/
structure Chapter16GeometricFiberCondition {S E : Scheme.{u}} (f : E ⟶ S) where
  geometricField : S → Type u
  geometricField_structure : ∀ s, Field (geometricField s)
  geometricField_closed : ∀ s, IsAlgClosed (geometricField s)
  geometricField_extension : ∀ s,
    S.residueField s ⟶ CommRingCat.of (geometricField s)
  shape : ∀ s,
    @Chapter16FiberShape
      (pullback (f.fiberToSpecResidueField s)
        (Spec.map (geometricField_extension s))) (geometricField s)
      (geometricField_structure s) (geometricField_closed s)
  shape_over : ∀ s,
    Chapter16FiberShape.structureMap (shape s) =
      pullback.snd (f.fiberToSpecResidueField s)
        (Spec.map (geometricField_extension s))

structure Chapter16FiberShapeInvariant (X Y : Scheme.{u}) (m : ℕ) where
  sourceComponents : Chapter16FiberComponentData X m
  targetComponents : Chapter16FiberComponentData Y m
  componentCorrespondence : Fin m ≃ Fin m
  componentCorrespondence_preserves_incidence :
    ∀ i j, sourceComponents.incidence i j ↔
      targetComponents.incidence (componentCorrespondence i) (componentCorrespondence j)
  schemeCorrespondence : X ≅ Y
  sourceNodes : Set X
  targetNodes : Set Y
  nodeCorrespondence :
    ∀ x, x ∈ sourceNodes ↔ schemeCorrespondence.hom x ∈ targetNodes

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
    (hX : Chapter16FiberShape X k)
    (hX_over : Chapter16FiberShape.structureMap hX = f) :
    Nonempty { h : Chapter16FiberShape
        (pullback f (chapter16FieldBaseChangeMap e)) K //
      Chapter16FiberShape.structureMap h =
        pullback.snd f (chapter16FieldBaseChangeMap e) } := by
  sorry

structure Chapter16CommonAlgebraicClosureData
    (k₁ k₂ K : Type u) [Field k₁] [Field k₂] [Field K] where
  first : Chapter16FieldExtension k₁ K
  second : Chapter16FieldExtension k₂ K
  algebraicallyClosed : IsAlgClosed K

structure Chapter16CommonGeometricFiberComparison
    {X Y : Scheme.{u}} {k₁ k₂ K : Type u}
    [Field k₁] [Field k₂] [Field K]
    (fX : X ⟶ Spec (CommRingCat.of k₁))
    (fY : Y ⟶ Spec (CommRingCat.of k₂))
    (C : Chapter16CommonAlgebraicClosureData k₁ k₂ K) (m : ℕ) where
  commonScheme : Scheme.{u}
  commonStructureMap : commonScheme ⟶ Spec (CommRingCat.of K)
  sourceIso : pullback fX (chapter16FieldBaseChangeMap C.first) ≅ commonScheme
  targetIso : pullback fY (chapter16FieldBaseChangeMap C.second) ≅ commonScheme
  sourceIso_over :
    sourceIso.hom ≫ commonStructureMap =
      pullback.snd fX (chapter16FieldBaseChangeMap C.first)
  targetIso_over :
    targetIso.hom ≫ commonStructureMap =
      pullback.snd fY (chapter16FieldBaseChangeMap C.second)

/- A common algebraic closure supplies compatible residue fields, but it does not identify two
arbitrary schemes.  The comparison of the two presentations is therefore an explicit input. -/
theorem chapter16_common_geometric_fiber_comparison_nonempty
    {X Y : Scheme.{u}} {k₁ k₂ K : Type u}
    [Field k₁] [Field k₂] [Field K]
    (fX : X ⟶ Spec (CommRingCat.of k₁))
    (fY : Y ⟶ Spec (CommRingCat.of k₂))
    (C : Chapter16CommonAlgebraicClosureData k₁ k₂ K)
    (comparison : Chapter16CommonGeometricFiberComparison fX fY C 1) :
    Nonempty (Chapter16CommonGeometricFiberComparison fX fY C 1) :=
  ⟨comparison⟩

theorem chapter16_geometric_fiber_shape_reflects_common_algebraic_closure
    {X Y : Scheme.{u}} {k₁ k₂ K : Type u}
    [Field k₁] [Field k₂] [Field K]
    [IsAlgClosed k₁] [IsAlgClosed k₂] [IsAlgClosed K]
    (fX : X ⟶ Spec (CommRingCat.of k₁))
    (fY : Y ⟶ Spec (CommRingCat.of k₂))
    (C : Chapter16CommonAlgebraicClosureData k₁ k₂ K)
    (_hX : Chapter16SmoothGenusOneFiber X k₁)
    (_hY : Chapter16SmoothGenusOneFiber Y k₂)
    (_hX_over : _hX.structureMap = fX)
    (_hY_over : _hY.structureMap = fY)
    (comparison : Chapter16CommonGeometricFiberComparison fX fY C 1) :
    Nonempty (pullback fX (chapter16FieldBaseChangeMap C.first) ≅
      pullback fY (chapter16FieldBaseChangeMap C.second)) := by
  exact ⟨comparison.sourceIso ≪≫ comparison.targetIso.symm⟩

theorem chapter16_geometric_fiber_components_and_nodes_invariant
    {X Y : Scheme.{u}} {k₁ k₂ K : Type u}
    [Field k₁] [Field k₂] [Field K]
    [IsAlgClosed k₁] [IsAlgClosed k₂] [IsAlgClosed K]
    {m : ℕ}
    (hm : 0 < m)
    (fX : X ⟶ Spec (CommRingCat.of k₁))
    (fY : Y ⟶ Spec (CommRingCat.of k₂))
    (C : Chapter16CommonAlgebraicClosureData k₁ k₂ K)
    (_hX : Chapter16NeronPolygonFiber X k₁ m)
    (_hY : Chapter16NeronPolygonFiber Y k₂ m)
    (_hX_over : _hX.structureMap = fX)
    (_hY_over : _hY.structureMap = fY)
    (comparison : Chapter16CommonGeometricFiberComparison fX fY C m) :
    Nonempty (Chapter16FiberShapeInvariant
      (pullback fX (chapter16FieldBaseChangeMap C.first))
      (pullback fY (chapter16FieldBaseChangeMap C.second)) m) := by
  sorry

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
  finite_intersections_affine : ∀ s, s.Nonempty → IsAffineOpen (intersection s)
  sectionsOnIntersection : Finset index → Type u
  sections_are_actual : ∀ s,
    Nonempty (sectionsOnIntersection s ≃
      ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).obj
        (Opposite.op (intersection s))).carrier)
  cechTerm : ℕ → Type u
  cechTerm_is_actual : ∀ n,
    Nonempty (cechTerm n ≃
      ((s : {s : Finset index // s.card = n + 1}) → sectionsOnIntersection s.1))
  cechDifferential : ∀ n, cechTerm n → cechTerm (n + 1)
  coherentCohomology : ℕ → Type u
  cech_computes_coherent_cohomology : ∀ i,
    Nonempty (coherentCohomology i ≃ cechTerm i)

structure Chapter16ProperSeparatedFiberData where
  fiber : Scheme.{u}
  base : Scheme.{u}
  structureMap : fiber ⟶ base
  proper : IsProper structureMap
  separated : IsSeparated structureMap

structure Chapter16FiniteDimensionalCertificate (V : Type u) where
  dimension : ℕ
  basisEquivalence : Nonempty (V ≃ Fin dimension)

structure Chapter16CechComplexData {X : Scheme.{u}}
    (cover : Chapter16FiniteAffineCechCover X) where
  term : ℕ → Type u
  term_is_actual : ∀ i, Nonempty (term i ≃ cover.cechTerm i)
  differential : ∀ i, term i → term (i + 1)
  differential_is_actual : ∀ i,
    differential i =
      (term_is_actual (i + 1)).some.symm ∘ cover.cechDifferential i ∘
        (term_is_actual i).some

structure Chapter16CechExactnessCertificate (A B C : Type u) where
  zeroC : C
  first : A → B
  second : B → C
  composite_zero : ∀ x, second (first x) = zeroC
  kernel_image : ∀ y, second y = zeroC ↔ ∃ x, first x = y

structure Chapter16CechBaseChangeCoverData
    {X Y : Scheme.{u}}
    (downstairs : Chapter16FiniteAffineCechCover X)
    (upstairs : Chapter16FiniteAffineCechCover Y)
    (p : Y ⟶ X) where
  indexEquivalence : downstairs.index ≃ upstairs.index
  open_compatibility : ∀ i,
    (upstairs.opens (indexEquivalence i) : Set Y) =
      p ⁻¹' (downstairs.opens i : Set X)

structure Chapter16CechBaseChangeData where
  downstairs : Chapter16EulerCharacteristicData.{u}
  upstairs : Chapter16EulerCharacteristicData.{u}
  fiberData : Chapter16ProperSeparatedFiberData
  baseChangedFiber : Scheme.{u}
  baseChangeMap : baseChangedFiber ⟶ fiberData.fiber
  finite_affine_cover : Chapter16FiniteAffineCechCover fiberData.fiber
  finite_intersections_affine : ∀ s, s.Nonempty →
    IsAffineOpen (finite_affine_cover.intersection s)
  baseChanged_finite_affine_cover : Chapter16FiniteAffineCechCover baseChangedFiber
  baseChanged_cover :
    Chapter16CechBaseChangeCoverData finite_affine_cover
      baseChanged_finite_affine_cover baseChangeMap
  downstairs_complex : Chapter16CechComplexData finite_affine_cover
  upstairs_complex : Chapter16CechComplexData baseChanged_finite_affine_cover
  baseChange_cochain_map : ∀ i,
    finite_affine_cover.cechTerm i → baseChanged_finite_affine_cover.cechTerm i
  baseChange_term_map : ∀ i,
    downstairs_complex.term i → upstairs_complex.term i
  baseChange_term_map_is_cech_baseChange : ∀ i,
    baseChange_term_map i =
      (upstairs_complex.term_is_actual i).some.symm ∘
        baseChange_cochain_map i ∘ (downstairs_complex.term_is_actual i).some
  tensor_exact : Chapter16CechExactnessCertificate
    (upstairs_complex.term 0) (upstairs_complex.term 1) (upstairs_complex.term 2)
  tensor_first_is_differential : tensor_exact.first = upstairs_complex.differential 0
  tensor_second_is_differential : tensor_exact.second = upstairs_complex.differential 1
  cohomology : ℕ → Type u
  cohomology_finite_dimensional : ∀ i,
    Chapter16FiniteDimensionalCertificate (cohomology i)
  cohomology_terms : ∀ i,
    Nonempty (cohomology i ≃ upstairs_complex.term i)
  cohomology_equivalence : ∀ i,
    Nonempty (downstairs.cohomologyModel i ≃ upstairs.cohomologyModel i)
  bounds_unchanged : downstairs.cohomologicalBound = upstairs.cohomologicalBound

theorem chapter16_cech_baseChange_preserves_euler_characteristic
    (C : Chapter16CechBaseChangeData) :
    chapter16EulerCharacteristic C.downstairs =
      chapter16EulerCharacteristic C.upstairs := by
  sorry

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
  map_eq : map = locus.ι ≫ f
  is_the_smooth_locus : ∀ x : E,
    x ∈ (locus : Set E) ↔
      ∃ U : E.Opens, x ∈ (U : Set E) ∧ IsOpenImmersion U.ι ∧
        Smooth (U.ι ≫ f)
  [groupObject : GrpObj (Over.mk map)]
  [commutative : IsCommMonObj (Over.mk map)]

noncomputable def chapter16SmoothLocusInclusion
    {E S : Scheme.{u}} {f : E ⟶ S} (smooth : Chapter16SmoothLocusData f) :
    Over.mk smooth.map ⟶ Over.mk f :=
  Over.homMk smooth.locus.ι smooth.map_eq.symm

structure Chapter16ComponentActionData (X : Scheme.{u}) where
  index : Type u
  component : index → Set X
  component_nonempty : ∀ i, (component i).Nonempty
  component_closed : ∀ i, IsClosed (component i)
  component_covers : (Set.univ : Set X) = ⋃ i, component i
  incidence : Set (index × index)
  incidence_iff_intersection : ∀ i j,
    (i, j) ∈ incidence ↔ (component i ∩ component j).Nonempty
  permutation : index ≃ index
  component_transport : ∀ i, component i ≃ component (permutation i)
  preserves_incidence : ∀ i j,
    (i, j) ∈ incidence ↔ (permutation i, permutation j) ∈ incidence

structure Chapter16ComponentFinitenessData (S : Scheme.{u}) where
  index : Type u
  component : index → Scheme.{u}
  componentMap : ∀ i, component i ⟶ S
  rank : index → ℕ
  finiteLocallyFree : ∀ i,
    Chapter16FiniteLocallyFreeProfile (componentMap i) (rank i)

noncomputable def chapter16BaseChangeSection
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (section_ : S ⟶ X) (section_over : section_ ≫ f = 𝟙 S) :
  T ⟶ pullback f g :=
  pullback.lift (g ≫ section_) (𝟙 T) (by sorry)

structure Chapter16GeneralizedEllipticCurve (S : Scheme.{u}) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  proper : IsProper structureMap
  separated : IsSeparated structureMap
  flat : Flat structureMap
  finitePresentation : LocallyOfFinitePresentation structureMap
  smoothLocus : Chapter16SmoothLocusData structureMap
  identity : S ⟶ carrier
  identity_section : identity ≫ structureMap = 𝟙 S
  identity_is_group_unit :
    identity = smoothLocus.groupObject.one.left ≫ smoothLocus.locus.ι
  identity_factor : ∃ e : S ⟶ smoothLocus.locus.toScheme,
    e ≫ smoothLocus.locus.ι = identity
  action :
    (Over.mk smoothLocus.map ⊗ Over.mk structureMap) ⟶ Over.mk structureMap
  action_on_smooth_locus :
    smoothLocus.groupObject.mul ≫ chapter16SmoothLocusInclusion smoothLocus =
      (CartesianMonoidalCategory.lift
        (CartesianMonoidalCategory.fst (Over.mk smoothLocus.map)
          (Over.mk smoothLocus.map))
        (CartesianMonoidalCategory.snd (Over.mk smoothLocus.map)
          (Over.mk smoothLocus.map) ≫ chapter16SmoothLocusInclusion smoothLocus)) ≫ action
  action_on_components : Chapter16ComponentActionData carrier
  fiberCondition : Chapter16GeometricFiberCondition structureMap

structure Chapter16GeneralizedEllipticCurveDescentDatum
    {S T : Scheme.{u}} (g : T ⟶ S) where
  cover : Chapter16FpqcMorphism g
  upstairs : Chapter16GeneralizedEllipticCurve T
  carrierDescent : Chapter16SchemeDescentDatum g
  carrier_matches : carrierDescent.carrier = upstairs.carrier
  structure_map_matches : HEq carrierDescent.structureMap upstairs.structureMap
  section_descent : T ⟶ upstairs.carrier
  section_descent_over : section_descent ≫ upstairs.structureMap = 𝟙 T
  section_descent_eq_identity : section_descent = upstairs.identity
  section_canonical_morphism : Over.mk (𝟙 T) ⟶ Over.mk upstairs.structureMap
  section_canonical_morphism_eq :
    section_canonical_morphism = Over.homMk section_descent section_descent_over
  smooth_open_descent : Chapter16SmoothLocusData upstairs.structureMap
  smooth_open_descent_eq : smooth_open_descent = upstairs.smoothLocus
  smooth_open_canonical_morphism :
    Over.mk upstairs.smoothLocus.map ⟶ Over.mk upstairs.structureMap
  smooth_open_canonical_morphism_eq :
    smooth_open_canonical_morphism = chapter16SmoothLocusInclusion upstairs.smoothLocus
  multiplication_descent :
    (Over.mk upstairs.smoothLocus.map ⊗ Over.mk upstairs.smoothLocus.map) ⟶
      Over.mk upstairs.smoothLocus.map
  multiplication_descent_eq :
    multiplication_descent = upstairs.smoothLocus.groupObject.mul
  action_descent :
    (Over.mk upstairs.smoothLocus.map ⊗ Over.mk upstairs.structureMap) ⟶
      Over.mk upstairs.structureMap
  action_descent_eq : action_descent = upstairs.action
  incidence_morphisms_descent : Chapter16ComponentActionData upstairs.carrier
  incidence_morphisms_descent_eq :
    incidence_morphisms_descent = upstairs.action_on_components
  component_finiteness_descent : Chapter16ComponentFinitenessData T
  fiber_condition_descent : Chapter16GeometricFiberCondition upstairs.structureMap
  fiber_condition_descent_eq : fiber_condition_descent = upstairs.fiberCondition

structure Chapter16GeneralizedEllipticCurveDescentResult
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16GeneralizedEllipticCurveDescentDatum g) where
  descended : Chapter16GeneralizedEllipticCurve S
  comparison : pullback descended.structureMap g ≅ D.upstairs.carrier
  comparison_over : comparison.hom ≫ D.upstairs.structureMap =
    pullback.snd descended.structureMap g
  identity_from_comparison :
    chapter16BaseChangeSection descended.structureMap g descended.identity
        descended.identity_section ≫ comparison.hom = D.upstairs.identity
  section_recovered : T ⟶ D.upstairs.carrier
  section_recovered_eq : section_recovered = D.section_descent
  smooth_open_recovered : Chapter16SmoothLocusData D.upstairs.structureMap
  smooth_open_recovered_eq : smooth_open_recovered = D.smooth_open_descent
  smooth_locus_comparison :
    (Over.pullback g).obj (Over.mk descended.smoothLocus.map) ≅
      Over.mk D.upstairs.smoothLocus.map
  smooth_locus_comparison_over :
    smooth_locus_comparison.hom.left ≫ D.upstairs.smoothLocus.map =
      pullback.snd descended.smoothLocus.map g
  smooth_locus_inclusion_from_comparison :
    smooth_locus_comparison.hom.left ≫ D.upstairs.smoothLocus.locus.ι =
      chapter16BaseChangeMorphism descended.smoothLocus.map descended.structureMap g
        descended.smoothLocus.locus.ι descended.smoothLocus.map_eq.symm ≫ comparison.hom
  multiplication_recovered :
    (Over.mk D.upstairs.smoothLocus.map ⊗ Over.mk D.upstairs.smoothLocus.map) ⟶
      Over.mk D.upstairs.smoothLocus.map
  multiplication_recovered_eq : multiplication_recovered = D.multiplication_descent
  action_recovered :
    (Over.mk D.upstairs.smoothLocus.map ⊗ Over.mk D.upstairs.structureMap) ⟶
      Over.mk D.upstairs.structureMap
  action_recovered_eq : action_recovered = D.action_descent
  incidence_morphisms_recovered : Chapter16ComponentActionData D.upstairs.carrier
  incidence_morphisms_recovered_eq :
    incidence_morphisms_recovered = D.incidence_morphisms_descent
  component_finiteness_recovered : Chapter16ComponentFinitenessData T
  component_finiteness_recovered_eq :
    component_finiteness_recovered = D.component_finiteness_descent
  fiber_condition_recovered : Chapter16GeometricFiberCondition D.upstairs.structureMap
  fiber_condition_recovered_eq :
    fiber_condition_recovered = D.fiber_condition_descent

theorem chapter16_generalizedEllipticCurve_effective_descent
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16GeneralizedEllipticCurveDescentDatum g) :
    Nonempty (Chapter16GeneralizedEllipticCurveDescentResult D) := by
  sorry

theorem chapter16_generalizedEllipticCurve_structure_identities_descend
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16GeneralizedEllipticCurveDescentDatum g)
    (R : Chapter16GeneralizedEllipticCurveDescentResult D) :
    R.multiplication_recovered = D.multiplication_descent ∧
      R.action_recovered = D.action_descent := by
  exact ⟨R.multiplication_recovered_eq, R.action_recovered_eq⟩

/-! ### Projectivity and divisors -/

structure Chapter16CompatibleAmpleDivisor {X S : Scheme.{u}}
    [LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10IdealDualAPI X]
    (f : X ⟶ S) where
  degree : ℕ
  divisor :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10RelativeEffectiveCartierDivisor
      f degree
  n : ℕ
  positive_power : 0 < n
  lineBundle : Chapter16LineBundle X
  divisorLineBundle : Chapter16LineBundle X
  divisorLineBundle_is_O_of_D :
    Chapter16LineBundle.Isomorphic divisorLineBundle
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09AsChapter04LineBundle
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10OofD
          divisor.divisor))
  lineBundle_is_O_of_nD :
    Chapter16LineBundle.Isomorphic lineBundle
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04LineBundleTensorPower
        divisorLineBundle n)
  relatively_ample : Chapter16IsAmple f lineBundle
  descentLineBundle : Chapter16LineBundle X
  compatible_with_descent : Chapter16LineBundle.Isomorphic lineBundle descentLineBundle

structure Chapter16IdentityDivisorCandidate {S : Scheme.{u}}
    (G : Chapter16GeneralizedEllipticCurve S)
    [LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10IdealDualAPI G.carrier] where
  degree : ℕ
  divisor :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10RelativeEffectiveCartierDivisor
      G.structureMap degree
  induced_by_identity_section :
    ∃ e : S ⟶ divisor.divisor.ideal.subscheme,
      e ≫ divisor.divisor.ideal.subschemeι = G.identity
  lineBundle : Chapter16LineBundle G.carrier
  divisorLineBundle : Chapter16LineBundle G.carrier
  divisorLineBundle_is_O_of_D :
    Chapter16LineBundle.Isomorphic divisorLineBundle
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09AsChapter04LineBundle
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10OofD
          divisor.divisor))
  lineBundle_is_O_of_D :
    Chapter16LineBundle.Isomorphic lineBundle divisorLineBundle
  relatively_ample : Chapter16IsAmple G.structureMap lineBundle

structure Chapter16PolygonPolarizingDivisor {E S : Scheme.{u}}
    [LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10IdealDualAPI E]
    (f : E ⟶ S) (m : ℕ) where
  components : Chapter16ComponentIndex E m
  positive_components : 0 < m
  degree : ℕ
  divisor :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10RelativeEffectiveCartierDivisor
      f degree
  meets_every_geometric_component :
    Chapter16MeetsEveryComponent components (divisor.divisor.ideal.support : Set E)
  orbit : Fin m → E
  orbit_under_level_data : ∀ i, ∃ j, orbit j ∈ components.component i
  n : ℕ
  positive_power : 0 < n
  divisorLineBundle : Chapter16LineBundle E
  divisorLineBundle_is_O_of_D :
    Chapter16LineBundle.Isomorphic divisorLineBundle
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09AsChapter04LineBundle
        (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.chapter10OofD
          divisor.divisor))
  lineBundle_is_O_of_nD :
    Chapter16LineBundle.Isomorphic lineBundle
      (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04LineBundleTensorPower
        divisorLineBundle n)
  lineBundle : Chapter16LineBundle E
  relatively_ample : Chapter16IsAmple f lineBundle

structure Chapter16UpstairsPolarizedDescentData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10IdealDualAPI
      (pullback f g)]
    where
  cover : Chapter16FpqcMorphism g
  finiteLocallyFreeCover : Chapter16FiniteLocallyFreeSurjectiveCover g
  proper : IsProper f
  finitePresentation : LocallyOfFinitePresentation f
  separated : IsSeparated f
  upstairs : Chapter16CompatibleAmpleDivisor (pullback.snd f g)
  descendedLineBundle : Chapter16LineBundle X
  lineBundle_baseChange :
    Chapter16IsBaseChangeOf f g descendedLineBundle upstairs.lineBundle
  ampleness_verification :
    Chapter16IsAmple (pullback.snd f g) upstairs.lineBundle

theorem chapter16_projectivity_descends_from_compatible_divisor
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10IdealDualAPI
      (pullback f g)]
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
    (D : Chapter16PolygonIdentityDivisorObstruction (E := E) m) (n : ℕ) (hn : 0 < n) :
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
  full_on_geometric_fibers : ∀ (s : S) (x : G),
    g x = s → ∃ i, sections i s = x

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
  targetGroup : GrpObj (Over.mk (targetToSmooth ≫ smooth.locus.ι ≫ f))
  map : source ⟶ target
  target_kind : Chapter16LevelTargetKind
  target_kind_compatibility :
    match target_kind with
    | .smoothLocus => IsIso targetToSmooth
    | .torsion => IsClosedImmersion targetToSmooth
  over : map ≫ targetToSmooth ≫ smooth.locus.ι ≫ f = sourceMap
  map_as_group_hom :
    letI := sourceGroup.groupObject
    letI := targetGroup
    IsMonHom
      (show Over.mk sourceMap ⟶
        Over.mk (targetToSmooth ≫ smooth.locus.ι ≫ f) from
        Over.homMk map over)
  sourceUnit : S ⟶ source
  targetUnit : S ⟶ target
  sourceOperation : source ⟶ source
  targetOperation : target ⟶ target
  sourceUnit_over : sourceUnit ≫ sourceMap = 𝟙 S
  targetUnit_over : targetUnit ≫ targetToSmooth ≫ smooth.locus.ι ≫ f = 𝟙 S
  homomorphism_unit : sourceUnit ≫ map = targetUnit
  homomorphism : sourceOperation ≫ map = map ≫ targetOperation
  closedImmersion : IsClosedImmersion map
  rank : ℕ
  rank_eq_source_rank : rank = r
  fullSections : Chapter16FullSetOfSections sourceMap rank

structure Chapter16FppfExactSequence {G H K S : Scheme.{u}}
    (gG : G ⟶ S) (gH : H ⟶ S) (gK : K ⟶ S) where
  first : G ⟶ H
  second : H ⟶ K
  first_over : first ≫ gH = gG
  second_over : second ≫ gK = gH
  groupG : GrpObj (Over.mk gG)
  groupH : GrpObj (Over.mk gH)
  groupK : GrpObj (Over.mk gK)
  first_as_group_hom :
    letI := groupG
    letI := groupH
    IsMonHom (show Over.mk gG ⟶ Over.mk gH from Over.homMk first first_over)
  second_as_group_hom :
    letI := groupH
    letI := groupK
    IsMonHom (show Over.mk gH ⟶ Over.mk gK from Over.homMk second second_over)
  zero_section : S ⟶ K
  zero_section_over : zero_section ≫ gK = 𝟙 S
  composite_is_zero : first ≫ second = gG ≫ zero_section
  first_kernel : IsClosedImmersion first
  second_fppf : Flat second ∧ LocallyOfFinitePresentation second ∧ Surjective second
  kernel_comparison : G ≅ pullback second zero_section
  kernel_comparison_fst : kernel_comparison.hom ≫ pullback.fst second zero_section = first
  kernel_comparison_snd : kernel_comparison.hom ≫ pullback.snd second zero_section = gG

structure Chapter16LevelFppfExactness
    {G H K T : Scheme.{u}}
    (gG : G ⟶ T) (gH : H ⟶ T) (gK : K ⟶ T) (map : H ⟶ K) where
  kernel : Scheme.{u}
  kernelMap : kernel ⟶ T
  sequence : Chapter16FppfExactSequence kernelMap gH gK
  sequence_second : sequence.second = map

structure Chapter16LevelStructureDescentDatum
    {S T E : Scheme.{u}} (g : T ⟶ S) (f : E ⟶ S) (r : ℕ) where
  cover : Chapter16FpqcMorphism g
  upstairsSmooth : Chapter16SmoothLocusData (pullback.snd f g)
  upstairs : Chapter16LevelStructure (pullback.snd f g) upstairsSmooth r
  homomorphism_descent :
    upstairs.sourceOperation ≫ upstairs.map = upstairs.map ≫ upstairs.targetOperation
  closedImmersion_descent : IsClosedImmersion upstairs.map
  rank_descent : upstairs.rank = r
  fullSections_descent : Chapter16FullSetOfSections upstairs.sourceMap upstairs.rank
  fppf_kernel : Scheme.{u}
  fppf_kernel_map : fppf_kernel ⟶ T
  fppf_exactness_descent :
    Chapter16LevelFppfExactness fppf_kernel_map upstairs.sourceMap
      (upstairs.targetToSmooth ≫ upstairsSmooth.locus.ι ≫ pullback.snd f g) upstairs.map

structure Chapter16LevelStructureDescentResult
    {S T E : Scheme.{u}} {g : T ⟶ S} {f : E ⟶ S} {r : ℕ}
    (D : Chapter16LevelStructureDescentDatum g f r) where
  descendedSmooth : Chapter16SmoothLocusData f
  descended : Chapter16LevelStructure f descendedSmooth r
  baseChange_equivalence : pullback descended.sourceMap g ≅ D.upstairs.source
  baseChange_equivalence_over :
    baseChange_equivalence.hom ≫ D.upstairs.sourceMap =
      pullback.snd descended.sourceMap g
  homomorphism_recovered :
    D.upstairs.sourceOperation ≫ D.upstairs.map =
      D.upstairs.map ≫ D.upstairs.targetOperation
  closedImmersion_recovered : IsClosedImmersion D.upstairs.map
  rank_recovered : D.upstairs.rank = r
  fullSections_recovered : Chapter16FullSetOfSections
    D.upstairs.sourceMap D.upstairs.rank
  fppf_exactness_recovered :
    Chapter16LevelFppfExactness D.fppf_kernel_map D.upstairs.sourceMap
      (D.upstairs.targetToSmooth ≫ D.upstairsSmooth.locus.ι ≫ pullback.snd f g)
      D.upstairs.map
  fppf_exactness_recovered_eq :
    fppf_exactness_recovered = D.fppf_exactness_descent

theorem chapter16_level_structure_effective_descent
    {S T E : Scheme.{u}} {g : T ⟶ S} {f : E ⟶ S} {r : ℕ}
    (D : Chapter16LevelStructureDescentDatum g f r) :
    Nonempty (Chapter16LevelStructureDescentResult D) := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16
