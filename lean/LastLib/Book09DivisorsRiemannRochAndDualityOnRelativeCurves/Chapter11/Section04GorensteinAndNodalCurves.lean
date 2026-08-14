import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Dependencies

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
open LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter10
open scoped BigOperators

universe u

/-! ### 11.4 Gorenstein and nodal curves -/

abbrev chapter11GorensteinH0Finrank {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) : ℕ :=
  chapter11CohomologyFinrank (f := C.structureMap) L.module 0

abbrev chapter11GorensteinH1Finrank {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) : ℕ :=
  chapter11CohomologyFinrank (f := C.structureMap) L.module 1

abbrev chapter11GorensteinEulerCharacteristic {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) : ℤ :=
  chapter11EulerCharacteristic (f := C.structureMap) L.module

/- LOCAL_DEPENDENCY_GUESS: the relative duality chapter supplies the following
field-valued form of duality for a Gorenstein curve.  The three maps retain
the specializations needed to calculate `χ(ω_C)` without importing Chapter 12.
-/
class Chapter11GorensteinSerreDualityTheory {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  h1_h0_dual_iso : ∀ L,
    Chapter11CohomologySpace C.carrier C.structureMap L.module 1 ≃ₗ[k]
      (Chapter11CohomologySpace C.carrier C.structureMap
        (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
          (chapter11Dual L)).module 0 →ₗ[k] k)
  h0_canonical_h1_structure_iso :
    Chapter11CohomologySpace C.carrier C.structureMap
        (chapter11CanonicalBundle (X := C.carrier)).module 0 ≃ₗ[k]
      (Chapter11CohomologySpace C.carrier C.structureMap
        (chapter11StructureSheafLineBundle C.carrier).module 1 →ₗ[k] k)
  h1_canonical_h0_structure_iso :
    Chapter11CohomologySpace C.carrier C.structureMap
        (chapter11CanonicalBundle (X := C.carrier)).module 1 ≃ₗ[k]
      (Chapter11CohomologySpace C.carrier C.structureMap
        (chapter11StructureSheafLineBundle C.carrier).module 0 →ₗ[k] k)

class Chapter11GorensteinConnectedGlobalSections {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  h0_structure_sheaf :
    chapter11GorensteinH0Finrank C
      (chapter11StructureSheafLineBundle C.carrier) = 1

/-- Riemann--Roch for every line bundle on a proper geometrically connected
Gorenstein curve of pure dimension one (11.5). -/
theorem chapter11_gorenstein_riemann_roch_euler_characteristic
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11GorensteinDegreeTheory C]
    [Chapter11GorensteinEulerCharacteristicTheory C]
    (L : Chapter11LineBundle C.carrier) :
    chapter11GorensteinEulerCharacteristic C L =
      chapter11Degree L + 1 - (C.arithmeticGenus : ℤ) := by
  sorry

/-- The duality form of Gorenstein Riemann--Roch (11.6). -/
theorem chapter11_gorenstein_riemann_roch_duality_form
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11GorensteinDegreeTheory C]
    [Chapter11GorensteinEulerCharacteristicTheory C]
    [Chapter11GorensteinSerreDualityTheory C]
    (L : Chapter11LineBundle C.carrier) :
    (chapter11GorensteinH0Finrank C L : ℤ) -
        chapter11GorensteinH0Finrank C
          (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
            (chapter11Dual L)) =
      chapter11Degree L + 1 - (C.arithmeticGenus : ℤ) := by
  sorry

/-- Duality exchanges the two cohomology groups of `ω_C` and `𝒪_C`, hence
`χ(ω_C) = -χ(𝒪_C)`. -/
theorem chapter11_gorenstein_canonical_euler_characteristic_is_negative
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11GorensteinSerreDualityTheory C] :
    chapter11GorensteinEulerCharacteristic C
        (chapter11CanonicalBundle (X := C.carrier)) =
      -chapter11GorensteinEulerCharacteristic C
        (chapter11StructureSheafLineBundle C.carrier) := by
  sorry

/-- The dualizing line bundle has degree `2g-2` on a proper Gorenstein curve. -/
theorem chapter11_gorenstein_degree_canonical_bundle
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11GorensteinDegreeTheory C]
    [Chapter11GorensteinEulerCharacteristicTheory C]
    [Chapter11GorensteinSerreDualityTheory C] :
    chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) =
      2 * (C.arithmeticGenus : ℤ) - 2 := by
  sorry

/-! ### Normalization of nodal curves -/

/-- The exact normalization sequence for the structure sheaf of a nodal
curve.  `nodeQuotient` is the direct sum of the one-dimensional node terms. -/
structure Chapter11NodalNormalizationData {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k) where
  nodal : chapter10IsNodal C.carrier
  reduced : IsReduced C.carrier
  normalization : Scheme.{u}
  normalizationMap : normalization ⟶ C.carrier
  normalization_is_finite : IsFinite normalizationMap
  normalization_is_normal : chapter10IsNormal normalization
  normalization_is_normalization :
    Nonempty (Chapter10NormalizationUniversalProperty normalizationMap)
  nodeQuotient : C.carrier.Modules
  inclusion :
    (chapter11StructureSheafLineBundle C.carrier).module ⟶
      (Scheme.Modules.pushforward normalizationMap).obj
        (chapter11StructureSheafLineBundle normalization).module
  quotientMap :
    (Scheme.Modules.pushforward normalizationMap).obj
        (chapter11StructureSheafLineBundle normalization).module ⟶ nodeQuotient
  inclusion_mono : Mono inclusion
  quotient_epi : Epi quotientMap
  comp_zero : inclusion ≫ quotientMap = 0
  exact : (ShortComplex.mk inclusion quotientMap comp_zero).Exact
  /-- The node profile is indexed by the actual closed nodes.  Its residue
  fields retain the degree contribution over the ground field, so the
  normalization quotient is not silently treated as a sum of copies of `k`.
  In the split rational case every degree is one and `nodeCount` is the
  ordinary number of nodes. -/
  nodeIndex : Type u
  [nodeIndexFinite : Fintype nodeIndex]
  nodePoint : nodeIndex → C.carrier
  nodePoint_is_node : ∀ q,
    chapter01OrdinaryDoublePointAt C.carrier (nodePoint q)
  nodePoint_pairwiseDistinct : Pairwise (fun q r : nodeIndex =>
    nodePoint q ≠ nodePoint r)
  nodePoint_exhaustive : ∀ x : C.carrier,
    chapter01OrdinaryDoublePointAt C.carrier x → ∃ q, nodePoint q = x
  nodeData : nodeIndex → Chapter10NonsplitNodeData k
  nodeCount : ℕ
  nodeCount_eq_residue_degree_sum :
    nodeCount = ∑ q, ((nodeData q).residue.degree)
  nodeQuotient_dimension : ℕ
  nodeQuotient_dimension_eq_count : nodeQuotient_dimension = nodeCount
  normalization_genus : ℕ
  componentCount : ℕ
  graphBetti : ℕ
  graph_betti_eq : graphBetti + componentCount = nodeCount + 1
  graph_contribution : C.arithmeticGenus = normalization_genus + graphBetti

attribute [instance] Chapter11NodalNormalizationData.nodeIndexFinite

theorem chapter11_nodal_normalization_sequence_exact
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    (N : Chapter11NodalNormalizationData C) :
    (ShortComplex.mk N.inclusion N.quotientMap N.comp_zero).Exact :=
  N.exact

theorem chapter11_nodal_normalization_euler_characteristic_difference
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    (N : Chapter11NodalNormalizationData C)
    (hnode : chapter11EulerCharacteristic (f := C.structureMap) N.nodeQuotient =
      (N.nodeCount : ℤ)) :
    chapter11EulerCharacteristic (f := C.structureMap)
        (chapter11StructureSheafLineBundle C.carrier).module -
        chapter11EulerCharacteristic (f := C.structureMap)
          ((Scheme.Modules.pushforward N.normalizationMap).obj
            (chapter11StructureSheafLineBundle N.normalization).module) =
      -(N.nodeCount : ℤ) := by
  sorry

/-- Tensoring the normalization sequence by a line bundle gives the sequence
whose Euler characteristics display the node correction. -/
structure Chapter11NodalTwistedNormalizationData {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier]
    [Chapter11DegreeTheory C.carrier]
    (N : Chapter11NodalNormalizationData C)
    (L : Chapter11LineBundle C.carrier) where
  normalizedLineBundle : Chapter11LineBundle N.normalization
  normalizedLineBundle_comparison :
    normalizedLineBundle.module ≅
      (Scheme.Modules.pullback N.normalizationMap).obj L.module
  twistedQuotient : C.carrier.Modules
  twistedInclusion : L.module ⟶
    (Scheme.Modules.pushforward N.normalizationMap).obj
      normalizedLineBundle.module
  twistedQuotientMap :
    (Scheme.Modules.pushforward N.normalizationMap).obj
      normalizedLineBundle.module ⟶
      twistedQuotient
  twistedInclusion_mono : Mono twistedInclusion
  twistedQuotient_epi : Epi twistedQuotientMap
  twistedQuotient_comparison :
    twistedQuotient ≅ chapter04Tensor L.module N.nodeQuotient
  twistedCompZero : twistedInclusion ≫ twistedQuotientMap = 0
  twistedExact :
    (ShortComplex.mk twistedInclusion twistedQuotientMap twistedCompZero).Exact
  nodeContribution :
    chapter11EulerCharacteristic (f := C.structureMap) twistedQuotient =
      (N.nodeCount : ℤ)
  normalized_euler_characteristic :
    chapter11EulerCharacteristic (f := C.structureMap)
        ((Scheme.Modules.pushforward N.normalizationMap).obj
          normalizedLineBundle.module) =
      chapter11Degree L + (N.componentCount : ℤ) - (N.normalization_genus : ℤ)

/-- Ordinary Riemann--Roch on normalized components plus the node terms gives
the global nodal formula. -/
theorem chapter11_nodal_curve_riemann_roch_from_normalization
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    [Chapter11EulerCharacteristicTheory C.carrier C.structureMap]
    (N : Chapter11NodalNormalizationData C)
    (L : Chapter11LineBundle C.carrier)
    (T : Chapter11NodalTwistedNormalizationData C N L) :
    chapter11GorensteinEulerCharacteristic C L =
      chapter11Degree L + 1 - (C.arithmeticGenus : ℤ) := by
  sorry

/-! ### Rosenlicht differentials and the nodal dual term -/

/-- A Rosenlicht differential datum records the orientation-free residue line
at every node.  The line is the Chapter 10 dual of the branch discrepancy
line, so no split ordering or scalar residue coordinate is chosen. -/
structure Chapter11RosenlichtDifferentialData {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    (N : Chapter11NodalNormalizationData C)
    [Chapter11DualizingSheafTheory C.carrier] where
  normalizationDifferentials : N.normalization.Modules
  residueTarget : C.carrier.Modules
  normalization_inclusion :
    (Scheme.Modules.pushforward N.normalizationMap).obj normalizationDifferentials ⟶
      (chapter11CanonicalBundle (X := C.carrier)).module
  residueMap :
    (chapter11CanonicalBundle (X := C.carrier)).module ⟶ residueTarget
  comp_zero : normalization_inclusion ≫ residueMap = 0
  inclusion_mono : Mono normalization_inclusion
  residue_epi : Epi residueMap
  exact : (ShortComplex.mk normalization_inclusion residueMap comp_zero).Exact
  residueLine : N.nodeIndex → Type u
  residueLine_is_dual : ∀ q,
    residueLine q =
      chapter10NonsplitResidueLine (N.nodeData q).branches

structure Chapter11NodalRosenlichtPairingData {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    (N : Chapter11NodalNormalizationData C)
    [Chapter11DualizingSheafTheory C.carrier]
    (R : Chapter11RosenlichtDifferentialData C N)
    [Chapter11PicardTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier) where
  leftPairing :
    Chapter11CohomologySpace C.carrier C.structureMap L.module 1 →ₗ[k]
      (Chapter11CohomologySpace C.carrier C.structureMap
        (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
          (chapter11Dual L)).module 0 →ₗ[k] k)
  leftPerfect : Function.Bijective leftPairing
  rightPairing :
    Chapter11CohomologySpace C.carrier C.structureMap
        (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
          (chapter11Dual L)).module 0 →ₗ[k]
      (Chapter11CohomologySpace C.carrier C.structureMap L.module 1 →ₗ[k] k)
  rightPerfect : Function.Bijective rightPairing
  compatibility : ∀ a b, leftPairing a b = rightPairing b a
  normalization_sequence :
    (ShortComplex.mk N.inclusion N.quotientMap N.comp_zero).Exact
  rosenlicht_sequence :
    (ShortComplex.mk R.normalization_inclusion R.residueMap R.comp_zero).Exact
  residue_line_source : ∀ q,
    R.residueLine q = chapter10NonsplitResidueLine (N.nodeData q).branches

def chapter11NodalRosenlichtLinearPerfectPairing
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    (N : Chapter11NodalNormalizationData C)
    [Chapter11DualizingSheafTheory C.carrier]
    (R : Chapter11RosenlichtDifferentialData C N)
    [Chapter11PicardTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (L : Chapter11LineBundle C.carrier)
    (P : Chapter11NodalRosenlichtPairingData C N R L) :
    LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter09.Chapter09LinearPerfectPairing
      k
      (Chapter11CohomologySpace C.carrier C.structureMap L.module 1)
      (Chapter11CohomologySpace C.carrier C.structureMap
        (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
          (chapter11Dual L)).module 0) :=
  { leftPairing := P.leftPairing
    leftPerfect := P.leftPerfect
    rightPairing := P.rightPairing
    rightPerfect := P.rightPerfect
    compatibility := P.compatibility }

class Chapter11NodalDualityTheory {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    (N : Chapter11NodalNormalizationData C)
    [Chapter11DualizingSheafTheory C.carrier]
    (R : Chapter11RosenlichtDifferentialData C N)
    [Chapter11PicardTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  /-- The perfect pairing is supplied together with the normalization exact
  sequence and the Rosenlicht residue-line identifications from which it is
  constructed. -/
  residue_line_pairing : ∀ L,
    Chapter11NodalRosenlichtPairingData C N R L

theorem chapter11_nodal_residue_lines_give_dual_term
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    (N : Chapter11NodalNormalizationData C)
    (R : Chapter11RosenlichtDifferentialData C N)
    [Chapter11NodalDualityTheory C N R]
    (L : Chapter11LineBundle C.carrier) :
    chapter11CohomologyFinrank (f := C.structureMap) L.module 1 =
    chapter11CohomologyFinrank (f := C.structureMap)
        (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
          (chapter11Dual L)).module 0 := by
  have _residue_line := R.residueLine
  have _residue_line_is_dual := R.residueLine_is_dual
  have _pairing_data :=
    Chapter11NodalDualityTheory.residue_line_pairing (C := C) (N := N) (R := R) L
  have _perfect_pairing :=
    chapter11NodalRosenlichtLinearPerfectPairing C N R L _pairing_data
  sorry

/-! ### The safe componentwise vanishing criterion -/

class Chapter11ComponentDegreeTheory {k : Type u} [Field k]
    (C : Chapter11ReducedConnectedCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  components : Type u
  componentDegree : Chapter11LineBundle C.carrier → components → ℤ
  nonzero_section_has_nonnegative_component :
    ∀ (L : Chapter11LineBundle C.carrier)
      (s : Chapter11CohomologySpace C.carrier C.structureMap L.module 0),
      s ≠ 0 → ∃ i, 0 ≤ componentDegree L i

def Chapter11ComponentwiseNegativeDegree {k : Type u} [Field k]
    (C : Chapter11ReducedConnectedCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11ComponentDegreeTheory C]
    (L : Chapter11LineBundle C.carrier) : Prop :=
  ∀ i : Chapter11ComponentDegreeTheory.components C,
    Chapter11ComponentDegreeTheory.componentDegree L i < 0

theorem chapter11_componentwise_negative_degree_forces_vanishing
    {k : Type u} [Field k]
    (C : Chapter11ReducedConnectedCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11ComponentDegreeTheory C]
    (L : Chapter11LineBundle C.carrier)
    (hnegative : Chapter11ComponentwiseNegativeDegree C L) :
    ∀ s : Chapter11CohomologySpace C.carrier C.structureMap L.module 0,
      s = 0 := by
  sorry

theorem chapter11_componentwise_negative_degree_h0_eq_zero
    {k : Type u} [Field k]
    (C : Chapter11ReducedConnectedCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11ComponentDegreeTheory C]
    (L : Chapter11LineBundle C.carrier)
    (hnegative : Chapter11ComponentwiseNegativeDegree C L) :
    chapter11CohomologyFinrank (f := C.structureMap) L.module 0 = 0 := by
  sorry

end

end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11
