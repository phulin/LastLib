import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11.Section03ConsequencesAndExamples

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter11

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

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
    [Chapter11GorensteinConnectedGlobalSections C]
    [Chapter11GorensteinSerreDualityTheory C] :
    chapter11Degree (chapter11CanonicalBundle (X := C.carrier)) =
      2 * (C.arithmeticGenus : ℤ) - 2 := by
  sorry

/-! ### Normalization of nodal curves -/

/-- The exact normalization sequence for the structure sheaf of a nodal
curve.  `nodeQuotient` is the direct sum of the one-dimensional node terms. -/
structure Chapter11NodalNormalizationData {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k) where
  nodal : Prop
  normalization : Scheme.{u}
  normalizationMap : normalization ⟶ C.carrier
  normalization_is_normal : Prop
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
  nodeCount : ℕ
  nodeQuotient_dimension : ℕ
  nodeQuotient_dimension_eq_count : nodeQuotient_dimension = nodeCount
  normalization_genus : ℕ
  componentCount : ℕ
  graphBetti : ℕ
  graph_betti_eq : graphBetti + componentCount = nodeCount + 1
  graph_contribution : C.arithmeticGenus = normalization_genus + graphBetti

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
    (N : Chapter11NodalNormalizationData C) :
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

/-- Ordinary Riemann--Roch on normalized components plus the node terms gives
the global nodal formula. -/
theorem chapter11_nodal_curve_riemann_roch_from_normalization
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11PicardTheory C.carrier] [Chapter11DegreeTheory C.carrier]
    (N : Chapter11NodalNormalizationData C)
    (L : Chapter11LineBundle C.carrier)
    (T : Chapter11NodalTwistedNormalizationData C N L) :
    chapter11GorensteinEulerCharacteristic C L =
      chapter11Degree L + 1 - (C.arithmeticGenus : ℤ) := by
  sorry

/-! ### Rosenlicht differentials and the nodal dual term -/

/-- A Rosenlicht differential datum stores the opposite-residue condition at
the two branches of every node. -/
structure Chapter11RosenlichtDifferentialData {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k) where
  branch : Type u
  node : Type u
  oppositeBranch : branch → branch
  isOpposite : Prop
  residue : branch → k
  oppositeResidues : ∀ b, residue (oppositeBranch b) = -residue b
  regularAwayFromNodes : Prop

class Chapter11NodalDualityTheory {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap] where
  duality_from_opposite_residues : Prop
  h1_h0_dual_iso : ∀ L,
    Chapter11CohomologySpace C.carrier C.structureMap L.module 1 ≃ₗ[k]
      (Chapter11CohomologySpace C.carrier C.structureMap
        (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
          (chapter11Dual L)).module 0 →ₗ[k] k)

theorem chapter11_nodal_opposite_residues_give_dual_term
    {k : Type u} [Field k]
    (C : Chapter11ProperGorensteinCurveOverField k)
    [Chapter11PicardTheory C.carrier]
    [Chapter11DualizingSheafTheory C.carrier]
    [Chapter11CohomologyTheory C.carrier C.structureMap]
    [Chapter11NodalDualityTheory C]
    (R : Chapter11RosenlichtDifferentialData C)
    (L : Chapter11LineBundle C.carrier) :
    chapter11CohomologyFinrank (f := C.structureMap) L.module 1 =
      chapter11CohomologyFinrank (f := C.structureMap)
        (chapter11Tensor (chapter11CanonicalBundle (X := C.carrier))
          (chapter11Dual L)).module 0 := by
  sorry

/-! ### The safe componentwise vanishing criterion -/

class Chapter11ComponentDegreeTheory {k : Type u} [Field k]
    (C : Chapter11ReducedConnectedCurveOverField k) where
  components : Type u
  componentDegree : Chapter11LineBundle C.carrier → components → ℤ

def Chapter11ComponentwiseNegativeDegree {k : Type u} [Field k]
    (C : Chapter11ReducedConnectedCurveOverField k)
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
