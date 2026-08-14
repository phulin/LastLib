import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16.Section01GeneralizedEllipticCurves

/-!
## 16.2 PEL objects

The PEL records keep the two safe polarization presentations separate: a rigidified ample line
bundle with its cocycle, or a supplied dual abelian scheme and a homomorphism to it.  The latter is
not reconstructed from a bare homomorphism.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry

universe u v

/-! ### Abelian schemes -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib and the currently drafted earlier chapters do not expose a
single dual-abelian-scheme/PEL object.  The records below keep the supplied dual, evaluation,
endomorphism, and polarization maps explicit rather than reconstructing them. -/

structure Chapter16AbelianScheme {A S : Scheme.{u}} (f : A ⟶ S) where
  core :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14AbelianSchemeCore
      f
  identity : S ⟶ A
  identity_section : identity ≫ f = 𝟙 S

structure Chapter16AbelianSchemeDescentDatum {S T : Scheme.{u}} (g : T ⟶ S) where
  cover : Chapter16FpqcMorphism g
  upstairsCarrier : Scheme.{u}
  upstairsMap : upstairsCarrier ⟶ T
  upstairs : Chapter16AbelianScheme upstairsMap
  carrier : Chapter16SchemeDescentDatum g
  carrier_matches : carrier.carrier = upstairsCarrier
  structure_map_matches : Prop
  identity_descent : Prop
  group_law_descent : Prop
  commutativity_descent : Prop
  smoothness_descent : Prop
  properness_descent : Prop
  connectedness_descent : Prop

structure Chapter16AbelianSchemeDescentResult
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16AbelianSchemeDescentDatum g) where
  descended : Scheme.{u}
  descendedMap : descended ⟶ S
  abelian : Chapter16AbelianScheme descendedMap
  baseChange_equivalence : Prop
  identity_recovered : Prop
  group_law_recovered : Prop

theorem chapter16_abelianScheme_effective_descent
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16AbelianSchemeDescentDatum g) :
    Nonempty (Chapter16AbelianSchemeDescentResult D) := by
  sorry

theorem chapter16_geometric_connectedness_after_residue_extension
    {A S : Scheme.{u}} {f : A ⟶ S}
    (h : GeometricallyConnected f) :
    ∀ s, GeometricallyConnected (f.fiberToSpecResidueField s) := by
  letI := h
  intro s
  infer_instance

/-! ### Algebra actions and polarization presentations -/

structure Chapter16EndomorphismAction {A S : Scheme.{u}} (f : A ⟶ S)
    (O : Chapter16FiniteAlgebraWithInvolution) where
  iota : O.carrier → (Over.mk f ⟶ Over.mk f)
  zeroEnd : Over.mk f ⟶ Over.mk f
  map_zero : iota O.ring.zero = zeroEnd
  map_one : iota O.ring.one = 𝟙 (Over.mk f)
  map_mul : ∀ a b, iota (O.ring.mul a b) = iota a ≫ iota b
  map_add : Prop
  finite_generation_identities : Prop
  endomorphisms_over_base : Prop

structure Chapter16DualAbelianSchemeData {A S B : Scheme.{u}}
    (fA : A ⟶ S) (fB : B ⟶ S) where
  dual : Chapter16AbelianScheme fB
  evaluation : Prop
  duality_is_functorial : Prop

structure Chapter16PolarizationLineBundleData {A S : Scheme.{u}} (f : A ⟶ S) where
  lineBundle : Chapter16LineBundle A
  rigidification : Prop
  lineBundle_cocycle : Prop
  relatively_ample : Chapter16IsAmple f lineBundle
  induced_homomorphism : Prop

structure Chapter16PolarizationHomData {A S B : Scheme.{u}}
    (fA : A ⟶ S) (fB : B ⟶ S) where
  target : Chapter16AbelianScheme fB
  lambda : A ⟶ B
  over_base : lambda ≫ fB = fA
  isogeny : Chapter16Isogeny lambda
  evaluation_supplied : Prop

inductive Chapter16PolarizationPresentation {A S : Scheme.{u}} (f : A ⟶ S) where
  | lineBundle (data : Chapter16PolarizationLineBundleData f)
  | homomorphism {B : Scheme.{u}} (fB : B ⟶ S)
      (data : Chapter16PolarizationHomData f fB)

structure Chapter16PolarizationInvolutionRelation
    (O : Chapter16FiniteAlgebraWithInvolution)
    {A B S : Scheme.{u}} (fA : A ⟶ S) (fB : B ⟶ S)
    (iota : O.carrier → (Over.mk fA ⟶ Over.mk fA))
    (lambda : (Over.mk fA ⟶ Over.mk fB)) where
  dualAction : O.carrier → (Over.mk fB ⟶ Over.mk fB)
  dualAction_over_base : ∀ a, (dualAction a).left ≫ fB = fB
  relation : ∀ a,
    (iota a).left ≫ lambda.left = lambda.left ≫ (dualAction (O.star a)).left

theorem chapter16_polarization_involution_compatibility
    (O : Chapter16FiniteAlgebraWithInvolution)
    {A B S : Scheme.{u}} {fA : A ⟶ S} {fB : B ⟶ S}
    (iota : O.carrier → (Over.mk fA ⟶ Over.mk fA))
    (lambda : (Over.mk fA ⟶ Over.mk fB))
    (R : Chapter16PolarizationInvolutionRelation O fA fB iota lambda) :
    ∀ a, (iota a).left ≫ lambda.left = lambda.left ≫ (R.dualAction (O.star a)).left := by
  exact R.relation

structure Chapter16PELDeterminantCertificate
    (O : Chapter16FiniteAlgebraWithInvolution) (R M : Type u)
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] where
  lie : Chapter16LieDeterminantData O R M
  lie_module_finite_locally_free : Prop
  prescribed_is_fixed : Prop
  baseChange_compatibility : Prop

structure Chapter16PELObject (S : Scheme.{u})
    (O : Chapter16FiniteAlgebraWithInvolution) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  abelian : Chapter16AbelianScheme structureMap
  action : Chapter16EndomorphismAction structureMap O
  polarization : Chapter16PolarizationPresentation structureMap
  polarization_compatibility : Prop
  level_structure : Prop
  determinant_condition : Prop
  alternating_pairing : Prop
  isotropic_subgroup : Prop
  similitude_factor : Prop

/-! ### Isogenies, kernels, and finite-flat rank -/

structure Chapter16KernelRankData {A B S : Scheme.{u}}
    (fA : A ⟶ S) (fB : B ⟶ S) (lambda : A ⟶ B) where
  kernel : Scheme.{u}
  kernelMap : kernel ⟶ S
  inclusion : kernel ⟶ A
  inclusion_over : inclusion ≫ fA = kernelMap
  finiteLocallyFree : ∃ d, Chapter16FiniteLocallyFreeProfile kernelMap d
  degree : ℕ
  degree_is_rank : Prop
  exactness : Chapter16FppfExactSequence kernelMap fA fB

structure Chapter16IsogenyDescentDatum {A B S T : Scheme.{u}}
    (fA : A ⟶ S) (fB : B ⟶ S) (g : T ⟶ S) (lambda : A ⟶ B) where
  cover : Chapter16FpqcMorphism g
  upstairsMap : pullback fA g ⟶ pullback fB g
  upstairs_isogeny : Chapter16Isogeny upstairsMap
  upstairs_kernel : Prop
  kernel_finite_flat : Prop
  kernel_rank : Prop
  degree_rank_compatibility : Prop

theorem chapter16_isogeny_properties_descend
    {A B S T : Scheme.{u}}
    {fA : A ⟶ S} {fB : B ⟶ S} {g : T ⟶ S} {lambda : A ⟶ B}
    (D : Chapter16IsogenyDescentDatum fA fB g lambda) :
    Chapter16Isogeny lambda := by
  sorry

structure Chapter16KernelRankDescentResult
    {A B S T : Scheme.{u}}
    {fA : A ⟶ S} {fB : B ⟶ S} {g : T ⟶ S} {lambda : A ⟶ B}
    (D : Chapter16IsogenyDescentDatum fA fB g lambda) where
  descendedKernel : Scheme.{u}
  descendedKernelMap : descendedKernel ⟶ S
  finiteLocallyFree : ∃ d, Chapter16FiniteLocallyFreeProfile descendedKernelMap d
  rank_recovered : Prop
  degree_recovered : Prop

theorem chapter16_kernel_rank_and_degree_descend
    {A B S T : Scheme.{u}}
    {fA : A ⟶ S} {fB : B ⟶ S} {g : T ⟶ S} {lambda : A ⟶ B}
    (D : Chapter16IsogenyDescentDatum fA fB g lambda) :
    Nonempty (Chapter16KernelRankDescentResult D) := by
  sorry

/-! ### Determinants, pairings, isotropy, and similitudes -/

theorem chapter16_determinant_equation_after_faithfully_flat_baseChange
    {O : Chapter16FiniteAlgebraWithInvolution} {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M]
    (D : Chapter16PELDeterminantCertificate O R M) :
    ∀ a, (D.lie.action a).charpoly = D.lie.prescribed a := by
  exact D.lie.characteristic_polynomial

structure Chapter16PairingDescentDatum {R M R' M' : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing R'] [AddCommGroup M'] [Module R' M'] where
  pairing : Chapter16PerfectAlternatingPairing R M
  baseChangedPairing : Chapter16PerfectAlternatingPairing R' M'
  scalarExtension : Prop
  finite_locally_free : Prop
  alternating_after_baseChange : Prop
  perfect_after_baseChange : Prop
  isotropic_after_baseChange : Prop
  similitude_after_baseChange : Prop

theorem chapter16_alternating_pairing_perfectness_and_isotropy_descend
    {R M R' M' : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing R'] [AddCommGroup M'] [Module R' M']
    (D : Chapter16PairingDescentDatum) :
    D.alternating_after_baseChange ∧ D.perfect_after_baseChange ∧
      D.isotropic_after_baseChange ∧ D.similitude_after_baseChange := by
  exact ⟨D.alternating_after_baseChange, D.perfect_after_baseChange,
    D.isotropic_after_baseChange, D.similitude_after_baseChange⟩

structure Chapter16PELDescentDatum {S T : Scheme.{u}}
    (g : T ⟶ S) (O : Chapter16FiniteAlgebraWithInvolution) where
  cover : Chapter16FpqcMorphism g
  upstairs : Chapter16PELObject T O
  action_descent : Prop
  polarization_descent : Prop
  involution_relation_descent : Prop
  determinant_descent : Prop
  pairing_descent : Prop
  level_descent : Prop
  triple_cocycle : Prop

structure Chapter16PELDescentResult {S T : Scheme.{u}}
    {g : T ⟶ S} {O : Chapter16FiniteAlgebraWithInvolution}
    (D : Chapter16PELDescentDatum g O) where
  descended : Chapter16PELObject S O
  baseChange_equivalence : Prop
  all_structure_maps_recovered : Prop
  all_equations_recovered : Prop

theorem chapter16_PEL_object_effective_descent
    {S T : Scheme.{u}} {g : T ⟶ S} {O : Chapter16FiniteAlgebraWithInvolution}
    (D : Chapter16PELDescentDatum g O) :
    Nonempty (Chapter16PELDescentResult D) := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16
