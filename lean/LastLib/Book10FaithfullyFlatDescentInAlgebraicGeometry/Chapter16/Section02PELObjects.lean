import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16.Section01GeneralizedEllipticCurves
import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.Dependencies

/-!
## 16.2 PEL objects

The PEL records keep the two safe polarization presentations separate: a rigidified ample line
bundle with its cocycle, or a supplied dual abelian scheme and a homomorphism to it.  The latter is
not reconstructed from a bare homomorphism.
-/

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open scoped AlgebraicGeometry TensorProduct

universe u v

/-! ### Abelian schemes -/

/- LOCAL_DEPENDENCY_GUESS: Mathlib and the currently drafted earlier chapters do not expose a
single dual-abelian-scheme/PEL object.  The records below keep the supplied dual, evaluation,
endomorphism, and polarization maps explicit rather than reconstructing them. -/

structure Chapter16GroupHomomorphismCertificate
    {A B S : Scheme.{u}} (fA : A ⟶ S) (fB : B ⟶ S) (lambda : A ⟶ B) where
  sourceGroup : GrpObj (Over.mk fA)
  targetGroup : GrpObj (Over.mk fB)
  lambda_over : lambda ≫ fB = fA
  hom : Over.mk fA ⟶ Over.mk fB
  hom_eq : hom = Over.homMk lambda lambda_over
  isMonHom :
    letI := sourceGroup
    letI := targetGroup
    IsMonHom hom

structure Chapter16LineBundleCocycleData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (L : Chapter16LineBundle X) where
  overlap : Scheme.{u} :=
    LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap g
  overlap_is_cech_nerve :
    overlap =
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlap g
  overlapComparison :
    (Over.pullback
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst g)).obj
        ((Over.pullback g).obj (Over.mk f)) ≅
      (Over.pullback
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond g)).obj
          ((Over.pullback g).obj (Over.mk f))
  overlapComparison_is_canonical :
    overlapComparison =
      LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapComparison
        g { scheme := X, toBase := f }
  left :
    (pullback (pullback.snd f g)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst g)).Modules
  rightOnSecond :
    (pullback (pullback.snd f g)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond g)).Modules
  left_is_pullback :
    left =
      (Scheme.Modules.pullback
        (pullback.fst (pullback.snd f g)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst g))).obj
        (chapter16BaseChangeLineBundle f g L).sheaf
  rightOnSecond_is_pullback :
    rightOnSecond =
      (Scheme.Modules.pullback
        (pullback.fst (pullback.snd f g)
          (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond g))).obj
        (chapter16BaseChangeLineBundle f g L).sheaf
  right :
    (pullback (pullback.snd f g)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst g)).Modules
  right_is_transport :
    right = (Scheme.Modules.pullback overlapComparison.hom.left).obj rightOnSecond
  transition : left ≅ right
  tripleOverlap : Scheme.{u} :=
    pullback
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond g)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst g)
  tripleOverlap_is_cech_nerve :
    tripleOverlap =
      pullback
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapSecond g)
        (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst g)
  tripleLeft :
    (pullback (pullback.snd f g)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst g)).Modules
  tripleMiddle :
    (pullback (pullback.snd f g)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst g)).Modules
  tripleRight :
    (pullback (pullback.snd f g)
      (LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter10.chapter10DoubleOverlapFirst g)).Modules
  transition12 : tripleLeft ≅ tripleMiddle
  transition23 : tripleMiddle ≅ tripleRight
  transition13 : tripleLeft ≅ tripleRight
  triple_cocycle : transition12.hom ≫ transition23.hom = transition13.hom

structure Chapter16DualEvaluationData
    {A B S : Scheme.{u}} (fA : A ⟶ S) (fB : B ⟶ S) where
  evaluationSpace : Scheme.{u} := pullback fA fB
  evaluationSpace_is_pullback : evaluationSpace = pullback fA fB
  toA : pullback fA fB ⟶ A
  toB : pullback fA fB ⟶ B
  value : pullback fA fB ⟶ S
  toA_is_pullback_fst : toA = pullback.fst fA fB
  toB_is_pullback_snd : toB = pullback.snd fA fB
  value_is_pullback_map : value = pullback.snd fA fB ≫ fB
  value_over_A : toA ≫ fA = value
  value_over_B : toB ≫ fB = value

structure Chapter16PELCompatibilityData
    (O : Chapter16FiniteAlgebraWithInvolution)
    {A S B : Scheme.{u}} (fA : A ⟶ S) (fB : B ⟶ S)
    (iota : O.carrier → (Over.mk fA ⟶ Over.mk fA)) where
  lambda : A ⟶ B
  lambda_over : lambda ≫ fB = fA
  dualAction : O.carrier → (B ⟶ B)
  dualAction_over : ∀ a, dualAction a ≫ fB = fB
  dualGroup : GrpObj (Over.mk fB)
  dualAction_is_group_hom : ∀ a,
    Chapter16GroupHomomorphismCertificate fB fB (dualAction a)
  relation : ∀ a,
    (iota a).left ≫ lambda = lambda ≫ dualAction (O.star a)

structure Chapter16AbelianScheme {A S : Scheme.{u}} (f : A ⟶ S) where
  core :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter14.Chapter14AbelianSchemeCore
      f
  identity : S ⟶ A
  identity_section : identity ≫ f = 𝟙 S
  identity_is_group_unit : identity = core.group.one.left

structure Chapter16AbelianSchemeDescentDatum {S T : Scheme.{u}} (g : T ⟶ S) where
  cover : Chapter16FpqcMorphism g
  upstairsCarrier : Scheme.{u}
  upstairsMap : upstairsCarrier ⟶ T
  upstairs : Chapter16AbelianScheme upstairsMap
  carrier : Chapter16SchemeDescentDatum g
  carrier_matches : carrier.carrier = upstairsCarrier
  structure_map_matches : HEq carrier.structureMap upstairsMap
  identity_descent : T ⟶ upstairsCarrier
  identity_descent_over : identity_descent ≫ upstairsMap = 𝟙 T
  group_law_descent : GrpObj (Over.mk upstairsMap)
  commutativity_descent : IsCommMonObj (Over.mk upstairsMap)
  smoothness_descent : Smooth upstairsMap
  properness_descent : IsProper upstairsMap
  connectedness_descent : GeometricallyConnected upstairsMap

structure Chapter16AbelianSchemeDescentResult
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16AbelianSchemeDescentDatum g) where
  descended : Scheme.{u}
  descendedMap : descended ⟶ S
  abelian : Chapter16AbelianScheme descendedMap
  comparison : pullback descendedMap g ≅ D.upstairsCarrier
  comparison_over : comparison.hom ≫ D.upstairsMap = pullback.snd descendedMap g
  identity_recovered : T ⟶ D.upstairsCarrier
  group_law_recovered : GrpObj (Over.mk D.upstairsMap)
  commutativity_recovered : IsCommMonObj (Over.mk D.upstairsMap)
  smoothness_recovered : Smooth D.upstairsMap
  properness_recovered : IsProper D.upstairsMap
  connectedness_recovered : GeometricallyConnected D.upstairsMap

theorem chapter16_abelianScheme_effective_descent
    {S T : Scheme.{u}} {g : T ⟶ S}
    (D : Chapter16AbelianSchemeDescentDatum g) :
    Nonempty (Chapter16AbelianSchemeDescentResult D) := by
  sorry

theorem chapter16_geometric_connectedness_after_residue_extension
    {A S : Scheme.{u}} {f : A ⟶ S}
    (h : GeometricallyConnected f) :
    ∀ s, GeometricallyConnected (f.fiberToSpecResidueField s) := by
  let := h
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
  addEnd : O.carrier → O.carrier → (Over.mk f ⟶ Over.mk f)
  map_add : ∀ a b, iota (a + b) = addEnd a b
  endomorphisms_over_base : ∀ a, (iota a).left ≫ f = f
  each_is_group_homomorphism : ∀ a,
    Chapter16GroupHomomorphismCertificate f f (iota a).left

structure Chapter16DualAbelianSchemeData {A S B : Scheme.{u}}
    (fA : A ⟶ S) (fB : B ⟶ S) where
  dual : Chapter16AbelianScheme fB
  evaluation : Chapter16DualEvaluationData fA fB
  duality_is_functorial : evaluation.toA ≫ fA = evaluation.toB ≫ fB

structure Chapter16PolarizationLineBundleData {A S : Scheme.{u}} (f : A ⟶ S) where
  lineBundle : Chapter16LineBundle A
  rigidifyingSection : S ⟶ A
  rigidifyingSection_over : rigidifyingSection ≫ f = 𝟙 S
  rigidificationBase : Chapter16LineBundle S
  rigidification : Chapter16LineBundle.Isomorphic rigidificationBase
    (LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04PullbackLineBundle
      rigidifyingSection lineBundle)
  lineBundle_cocycle : ∀ {T : Scheme.{u}} (g : T ⟶ S),
    Chapter16LineBundleCocycleData f g lineBundle
  relatively_ample : Chapter16IsAmple f lineBundle
  inducedMap : A ⟶ A
  inducedMap_over : inducedMap ≫ f = f
  induced_homomorphism : Chapter16GroupHomomorphismCertificate f f inducedMap

structure Chapter16PolarizationHomData {A S B : Scheme.{u}}
    (fA : A ⟶ S) (fB : B ⟶ S) where
  target : Chapter16AbelianScheme fB
  lambda : A ⟶ B
  over_base : lambda ≫ fB = fA
  homomorphism : Chapter16GroupHomomorphismCertificate fA fB lambda
  isogeny : Chapter16Isogeny lambda
  evaluation_supplied : Chapter16DualAbelianSchemeData fA fB

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
  lie_module_finite_locally_free :
    Module.Free R M ∧ Module.Finite R M
  fixedPrescribed : O.carrier → Polynomial R
  prescribed_is_fixed : lie.prescribed = fixedPrescribed
  baseChangedAction : O.carrier → Module.End R M
  baseChangedPrescribed : O.carrier → Polynomial R
  baseChange_action : ∀ a, baseChangedAction a = lie.action a
  baseChange_compatibility : ∀ a, baseChangedPrescribed a = fixedPrescribed a

structure Chapter16PELLinearData
    (O : Chapter16FiniteAlgebraWithInvolution) where
  R : Type u
  M : Type u
  [commRing : CommRing R]
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  [free : Module.Free R M]
  [finite : Module.Finite R M]
  determinant : Chapter16PELDeterminantCertificate O R M
  pairing : Chapter16PerfectAlternatingPairing R M
  isotropicSubmodule : Submodule R M
  isotropic : Chapter16Isotropic pairing isotropicSubmodule
  similitude : Chapter16SimilitudePairing R M

structure Chapter16PELObject (S : Scheme.{u})
    (O : Chapter16FiniteAlgebraWithInvolution) where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ S
  abelian : Chapter16AbelianScheme structureMap
  action : Chapter16EndomorphismAction structureMap O
  polarization : Chapter16PolarizationPresentation structureMap
  polarization_compatibility :
    Chapter16PELCompatibilityData O structureMap structureMap action.iota
  levelRank : ℕ
  levelSmooth : Chapter16SmoothLocusData structureMap
  level_structure : Chapter16LevelStructure structureMap levelSmooth levelRank
  linearData : Chapter16PELLinearData.{u, u} O

/-! ### Isogenies, kernels, and finite-flat rank -/

structure Chapter16KernelRankData {A B S : Scheme.{u}}
    (fA : A ⟶ S) (fB : B ⟶ S) (lambda : A ⟶ B) (zero : S ⟶ B) where
  zero_over : zero ≫ fB = 𝟙 S
  kernel : Scheme.{u}
  kernelMap : kernel ⟶ S
  inclusion : kernel ⟶ A
  inclusion_over : inclusion ≫ fA = kernelMap
  kernel_scheme_theoretic : kernel ≅ pullback lambda zero
  kernel_scheme_theoretic_inclusion :
    kernel_scheme_theoretic.hom ≫ pullback.fst lambda zero = inclusion
  kernel_scheme_theoretic_structure :
    kernel_scheme_theoretic.hom ≫ pullback.snd lambda zero = kernelMap
  degree : ℕ
  finiteLocallyFree : Chapter16FiniteLocallyFreeProfile kernelMap degree
  exactness : Chapter16FppfExactSequence kernelMap fA fB
  exactness_first : exactness.first = inclusion
  exactness_second : exactness.second = lambda

structure Chapter16IsogenyDescentDatum {A B S T : Scheme.{u}}
    (fA : A ⟶ S) (fB : B ⟶ S) (g : T ⟶ S) (lambda : A ⟶ B) where
  cover : Chapter16FpqcMorphism g
  lambda_over : lambda ≫ fB = fA
  zero : S ⟶ B
  zero_over : zero ≫ fB = 𝟙 S
  homomorphism : Chapter16GroupHomomorphismCertificate fA fB lambda
  upstairsMap : pullback fA g ⟶ pullback fB g
  upstairsMap_is_baseChange :
    upstairsMap = chapter16BaseChangeMorphism fA fB g lambda lambda_over
  upstairs_isogeny : Chapter16Isogeny upstairsMap
  upstairsZero : T ⟶ pullback fB g
  upstairsZero_over : upstairsZero ≫ pullback.snd fB g = 𝟙 T
  upstairsZero_is_baseChange :
    upstairsZero = chapter16BaseChangeSection fB g zero zero_over
  upstairsKernel :
    Chapter16KernelRankData (pullback.snd fA g) (pullback.snd fB g) upstairsMap upstairsZero
  kernelDescent : Chapter16SchemeDescentDatum g
  kernel_descent_matches : kernelDescent.carrier = upstairsKernel.kernel
  kernel_structure_map_matches : HEq kernelDescent.structureMap upstairsKernel.kernelMap
  degree : ℕ
  kernel_finite_flat :
    Chapter16FiniteLocallyFreeProfile upstairsKernel.kernelMap degree
  kernel_rank : ∀ x,
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10FiberLength
      upstairsKernel.kernelMap x = upstairsKernel.degree
  degree_rank_compatibility : degree = upstairsKernel.degree

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
  kernelData : Chapter16KernelRankData fA fB lambda D.zero
  kernel_comparison : pullback kernelData.kernelMap g ≅ D.upstairsKernel.kernel
  kernel_comparison_over : kernel_comparison.hom ≫ D.upstairsKernel.kernelMap =
    pullback.snd kernelData.kernelMap g
  kernel_comparison_inclusion :
    kernel_comparison.hom ≫ D.upstairsKernel.inclusion =
      chapter16BaseChangeMorphism kernelData.kernelMap fA g kernelData.inclusion
        kernelData.inclusion_over
  scheme_theoretic_kernel_comparison :
    pullback kernelData.kernelMap g ≅
      pullback D.upstairsMap D.upstairsZero
  scheme_theoretic_kernel_comparison_commutes :
    kernel_comparison.hom ≫ D.upstairsKernel.kernel_scheme_theoretic.hom =
      scheme_theoretic_kernel_comparison.hom
  exact_sequence_first_recovered :
    kernel_comparison.hom ≫ D.upstairsKernel.exactness.first =
      chapter16BaseChangeMorphism kernelData.kernelMap fA g
        kernelData.exactness.first kernelData.exactness.first_over
  exact_sequence_second_recovered :
    D.upstairsKernel.exactness.second =
      chapter16BaseChangeMorphism fA fB g kernelData.exactness.second
        kernelData.exactness.second_over
  exact_sequence_zero_recovered :
    D.upstairsKernel.exactness.zero_section =
      chapter16BaseChangeSection fB g D.zero D.zero_over
  upstairs_isogeny_map_recovered :
    D.upstairsMap = chapter16BaseChangeMorphism fA fB g lambda D.lambda_over
  rank_recovered : ∀ x,
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10.Chapter10FiberLength
      D.upstairsKernel.kernelMap x = D.upstairsKernel.degree
  degree_recovered : D.degree = D.upstairsKernel.degree

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
    [CommRing R'] [AddCommGroup M'] [Module R' M']
    [Algebra R R'] [Module R M'] [Module.FaithfullyFlat R R'] where
  pairing : M →ₗ[R] (M →ₗ[R] R)
  baseChangedPairing : M' →ₗ[R'] (M' →ₗ[R'] R')
  baseChangeIdentification : R' ⊗[R] M ≃ₗ[R'] M'
  scalarExtension : M →ₗ[R] M'
  scalarExtension_is_baseChange : ∀ x,
    scalarExtension x =
      baseChangeIdentification (TensorProduct.mk R R' M 1 x)
  scalarExtension_compatibility : ∀ x y,
    baseChangedPairing (scalarExtension x) (scalarExtension y) =
      algebraMap R R' (pairing x y)
  finite_locally_free :
    Module.Free R M ∧ Module.Finite R M ∧
      Module.Free R' M' ∧ Module.Finite R' M'
  baseChanged_perfect : Function.Bijective baseChangedPairing
  baseChanged_alternating : ∀ x, baseChangedPairing x x = 0
  isotropicSubmodule : Submodule R M
  baseChangedIsotropicSubmodule : Submodule R' M'
  baseChanged_isotropic : ∀ x ∈ baseChangedIsotropicSubmodule,
    ∀ y ∈ baseChangedIsotropicSubmodule, baseChangedPairing x y = 0
  baseChangedSimilitudePairing : Chapter16SimilitudePairing R' M'
  baseChanged_pairing_matches : baseChangedSimilitudePairing.pairing = baseChangedPairing
  referencePairing : M →ₗ[R] (M →ₗ[R] R)
  reference_pairing_baseChange : ∀ x y,
    baseChangedSimilitudePairing.referencePairing (scalarExtension x)
        (scalarExtension y) = algebraMap R R' (referencePairing x y)
  factor : R
  factor_baseChange : baseChangedSimilitudePairing.factor = algebraMap R R' factor
  baseChanged_similitude : ∀ x y,
    baseChangedPairing x y =
      baseChangedSimilitudePairing.factor *
        baseChangedSimilitudePairing.referencePairing x y

theorem chapter16_alternating_pairing_perfectness_and_isotropy_descend
    {R M R' M' : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing R'] [AddCommGroup M'] [Module R' M']
    [Algebra R R'] [Module R M'] [Module.FaithfullyFlat R R']
    (D : Chapter16PairingDescentDatum (R := R) (M := M) (R' := R') (M' := M')) :
    ∃ P : Chapter16PerfectAlternatingPairing R M,
      P.pairing = D.pairing ∧
        Chapter16Isotropic P D.isotropicSubmodule ∧
          ∃ Q : Chapter16SimilitudePairing R M,
            Q.pairing = D.pairing ∧
              (∀ x y, Q.pairing x y = Q.factor * Q.referencePairing x y) := by
  sorry

structure Chapter16PELDescentDatum {S T : Scheme.{u}}
    (g : T ⟶ S) (O : Chapter16FiniteAlgebraWithInvolution) where
  cover : Chapter16FpqcMorphism g
  upstairs : Chapter16PELObject T O
  carrier : Chapter16SchemeDescentDatum g
  carrier_matches : carrier.carrier = upstairs.carrier
  structure_map_matches : HEq carrier.structureMap upstairs.structureMap
  action_descent : Chapter16EndomorphismAction upstairs.structureMap O
  action_descent_matches : action_descent = upstairs.action
  polarization_descent : Chapter16PolarizationPresentation upstairs.structureMap
  polarization_descent_matches : polarization_descent = upstairs.polarization
  involution_relation_descent :
    Chapter16PELCompatibilityData O upstairs.structureMap upstairs.structureMap
      upstairs.action.iota
  determinant_descent : Chapter16PELLinearData.{u, u} O
  determinant_descent_matches : determinant_descent = upstairs.linearData
  pairing_descent : Chapter16PELLinearData.{u, u} O
  pairing_descent_matches : pairing_descent = upstairs.linearData
  level_descent :
    Chapter16LevelStructure upstairs.structureMap upstairs.levelSmooth upstairs.levelRank
  level_descent_matches : level_descent = upstairs.level_structure

structure Chapter16PELDescentResult {S T : Scheme.{u}}
    {g : T ⟶ S} {O : Chapter16FiniteAlgebraWithInvolution}
    (D : Chapter16PELDescentDatum g O) where
  descended : Chapter16PELObject S O
  comparison : pullback descended.structureMap g ≅ D.upstairs.carrier
  comparison_over : comparison.hom ≫ D.upstairs.structureMap =
    pullback.snd descended.structureMap g
  action_map_compatibility : ∀ a,
    comparison.hom ≫ (D.upstairs.action.iota a).left =
      chapter16BaseChangeMorphism descended.structureMap descended.structureMap g
        (descended.action.iota a).left
          (descended.action.endomorphisms_over_base a) ≫ comparison.hom
  linearData_recovered : Chapter16PELLinearData.{u, u} O
  linearData_recovered_is_descended : linearData_recovered = descended.linearData
  linearData_recovered_is_upstairs : linearData_recovered = D.upstairs.linearData
  all_structure_maps_recovered :
      Chapter16EndomorphismAction D.upstairs.structureMap O ×
      Chapter16PolarizationPresentation D.upstairs.structureMap ×
      Chapter16LevelStructure D.upstairs.structureMap D.upstairs.levelSmooth D.upstairs.levelRank
  all_structure_maps_match :
    all_structure_maps_recovered =
      (D.action_descent, D.polarization_descent, D.level_descent)
  all_equations_recovered :
    Chapter16PELCompatibilityData O D.upstairs.structureMap D.upstairs.structureMap
        D.upstairs.action.iota ×
      Chapter16PELLinearData.{u, u} O × Chapter16PELLinearData.{u, u} O
  all_equations_match :
    all_equations_recovered =
      (D.involution_relation_descent, D.determinant_descent, D.pairing_descent)

theorem chapter16_PEL_object_effective_descent
    {S T : Scheme.{u}} {g : T ⟶ S} {O : Chapter16FiniteAlgebraWithInvolution}
    (D : Chapter16PELDescentDatum g O) :
    Nonempty (Chapter16PELDescentResult D) := by
  sorry

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter16
