import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Separation.Connected
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08.Dependencies
import LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11.Section04UniversalDivisorOnASmoothCurve
import LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01.Section02DimensionOneAsAMeetingPoint

namespace LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter08
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter11
open scoped AlgebraicGeometry BigOperators TensorProduct

universe u v

/-! ### Standing conventions and hypotheses -/

def chapter01StructureSheaf {X : Scheme.{u}} : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

def chapter01StructureSheafCohomologyDimensionData
    {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier) : Prop :=
  ∃ hO : chapter04FiniteTypeQuasiCoherent
      (chapter01StructureSheaf : C.carrier.Modules),
    ∀ i,
      let R := D.realization chapter01StructureSheaf hO i
      letI := R.addCommGroup
      letI := R.module
      letI := R.finite
      FiniteDimensional k R.V

abbrev chapter01GlobalFunctions {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k) : Type u :=
  Γ(C.carrier, ⊤)

def chapter01GlobalFunctionsAlgebraMap {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k) : k →+* chapter01GlobalFunctions C :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.structureMap.appTop).hom

structure Chapter01GeometricallyConnectedReducedCurve
    (k : Type u) [Field k] (C : Chapter01ProperCurveOverField k) where
  geometricallyConnected : GeometricallyConnected C.structureMap
  geometricallyReduced : GeometricallyReduced C.structureMap

theorem chapter01_globalFunctions_eq_baseField
    {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k)
    (H : Chapter01GeometricallyConnectedReducedCurve k C) :
    ∃ e : chapter01GlobalFunctions C ≃+* k,
      ∀ r : k, e (chapter01GlobalFunctionsAlgebraMap C r) = r := by
  have : GeometricallyConnected C.structureMap := H.geometricallyConnected
  have : GeometricallyReduced C.structureMap := H.geometricallyReduced
  let : ConnectedSpace C.carrier :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := C.structureMap)
  let : IsReduced C.carrier :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian C.structureMap
  have hred : _root_.IsReduced (chapter01GlobalFunctions C) :=
    IsReduced.component_reduced (X := C.carrier) ⊤
  let _ : CompactSpace C.carrier :=
    compactSpace_of_universallyClosed C.structureMap
  let : MorphismProperty.RespectsIso @UniversallyClosed :=
    universallyClosed_respectsIso
  have huccomp : UniversallyClosed
      (C.carrier.toSpecΓ ≫ Spec.map C.structureMap.appTop) := by
    rw [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
    infer_instance
  have huc : UniversallyClosed C.carrier.toSpecΓ :=
    .of_comp_of_isSeparated _ (Spec.map C.structureMap.appTop)
  let _ : UniversallyClosed C.carrier.toSpecΓ := huc
  have hsurj : Surjective C.carrier.toSpecΓ := by infer_instance
  let : ConnectedSpace (Spec (CommRingCat.of (chapter01GlobalFunctions C))) :=
    hsurj.surj.connectedSpace C.carrier.toSpecΓ.continuous
  have hint : (chapter01GlobalFunctionsAlgebraMap C).IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed C.structureMap
  have hdim0 : Ring.KrullDimLE 0 (chapter01GlobalFunctions C) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    let : (I.comap (chapter01GlobalFunctionsAlgebraMap C)).IsPrime :=
      Ideal.comap_isPrime _ _
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap'
      (chapter01GlobalFunctionsAlgebraMap C) hint I
      (Ideal.IsPrime.isMaximal' inferInstance)
  let : IsLocallyNoetherian C.carrier := by
    exact LocallyOfFiniteType.isLocallyNoetherian C.structureMap
  let : IsNoetherian C.carrier := ⟨⟩
  have hnoethSpec : NoetherianSpace
      (Spec (CommRingCat.of (chapter01GlobalFunctions C))) :=
    TopologicalSpace.noetherianSpace_of_surjective C.carrier.toSpecΓ
      C.carrier.toSpecΓ.continuous hsurj.surj
  let : NoetherianSpace
      (PrimeSpectrum (chapter01GlobalFunctions C)) := by
    change NoetherianSpace (Spec (CommRingCat.of (chapter01GlobalFunctions C)))
    exact hnoethSpec
  let : Ring.KrullDimLE 0 (chapter01GlobalFunctions C) := hdim0
  have hcompSingleton :
      ∀ (Z : TopologicalSpace.IrreducibleCloseds
          (PrimeSpectrum (chapter01GlobalFunctions C)))
        (hZ : (Z : Set (PrimeSpectrum (chapter01GlobalFunctions C))) ∈
          irreducibleComponents (PrimeSpectrum (chapter01GlobalFunctions C))),
        (Z : Set (PrimeSpectrum (chapter01GlobalFunctions C))) =
          ({Z.isIrreducible'.genericPoint} : Set (PrimeSpectrum (chapter01GlobalFunctions C))) := by
    intro Z hZ
    have hzclosed : IsClosed
        ({Z.isIrreducible'.genericPoint} : Set (PrimeSpectrum (chapter01GlobalFunctions C))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal Z.isIrreducible'.genericPoint).mpr
        (Ideal.IsPrime.isMaximal' Z.isIrreducible'.genericPoint.2)
    have hzgen : IsGenericPoint Z.isIrreducible'.genericPoint (Z : Set _) :=
      Z.isIrreducible'.isGenericPoint_genericPoint
        (isClosed_of_mem_irreducibleComponents _ hZ)
    exact hzgen.symm.trans hzclosed.closure_eq
  have hspecfiniteSet :
      (Set.univ : Set (PrimeSpectrum (chapter01GlobalFunctions C))).Finite := by
    rw [← sUnion_irreducibleComponents]
    apply TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sUnion
    intro Z hZ
    let Z' : TopologicalSpace.IrreducibleCloseds
        (PrimeSpectrum (chapter01GlobalFunctions C)) :=
      ⟨Z, hZ.1, isClosed_of_mem_irreducibleComponents _ hZ⟩
    have hZeq : Z =
        ({Z'.isIrreducible'.genericPoint} : Set
          (PrimeSpectrum (chapter01GlobalFunctions C))) := by
      simpa [Z'] using hcompSingleton Z' hZ
    rw [hZeq]
    exact Set.finite_singleton _
  let : Finite (PrimeSpectrum (chapter01GlobalFunctions C)) :=
    Set.finite_univ_iff.mp hspecfiniteSet
  let : DiscreteTopology (PrimeSpectrum (chapter01GlobalFunctions C)) :=
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr
      ⟨inferInstance, hdim0⟩
  let : ConnectedSpace (PrimeSpectrum (chapter01GlobalFunctions C)) := by
    change ConnectedSpace (Spec (CommRingCat.of (chapter01GlobalFunctions C)))
    infer_instance
  have hsub : Subsingleton (PrimeSpectrum (chapter01GlobalFunctions C)) :=
    @PreconnectedSpace.trivial_of_discrete
      (PrimeSpectrum (chapter01GlobalFunctions C)) _ inferInstance inferInstance
  have hnonempty : Nonempty (PrimeSpectrum (chapter01GlobalFunctions C)) :=
    inferInstance
  let : Nontrivial (chapter01GlobalFunctions C) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp hnonempty
  have hfield : IsField (chapter01GlobalFunctions C) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp hsub
  let : Field (chapter01GlobalFunctions C) := hfield.toField
  have hfinite : (chapter01GlobalFunctionsAlgebraMap C).Finite := by
    have x : C.carrier := Nonempty.some inferInstance
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      C.carrier.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ x) isOpen_univ
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    apply RingHom.finite_of_algHom_finiteType_of_isJacobsonRing
      (A := Γ(C.carrier, U))
      (g := (C.carrier.presheaf.map (homOfLE le_top).op).hom)
    have hft := C.structureMap.finiteType_appLE (isAffineOpen_top _) hU (by simp)
    have hft' :=
      (RingHom.finiteType_respectsIso.cancel_left_isIso
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        (C.structureMap.appLE (⊤ : (Spec (CommRingCat.of k)).Opens) U (by simp))).2 hft
    have happ :
        C.structureMap.appTop ≫ C.carrier.presheaf.map (homOfLE le_top).op =
          C.structureMap.appLE (⊤ : (Spec (CommRingCat.of k)).Opens) U (by simp) := by
      rfl
    convert hft' using 1
    · change (inferInstance : CommRing k) = (CommRingCat.of k).commRing
      rfl
    · change
        ((C.carrier.presheaf.map (homOfLE le_top).op).hom).comp
          (((C.structureMap.appTop).hom).comp
            ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom) =
          ((C.structureMap.appLE (⊤ : (Spec (CommRingCat.of k)).Opens) U (by simp)).hom).comp
            ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom
      simpa [CommRingCat.hom_comp, RingHom.comp_assoc] using congrArg
        (fun t => t.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) happ
  let : Algebra k (chapter01GlobalFunctions C) :=
    (chapter01GlobalFunctionsAlgebraMap C).toAlgebra
  let g : Spec (CommRingCat.of (chapter01GlobalFunctions C)) ⟶
      Spec (CommRingCat.of k) :=
    Spec.map C.structureMap.appTop ≫
      Spec.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  let g0 : Spec (CommRingCat.of (chapter01GlobalFunctions C)) ⟶
      Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (chapter01GlobalFunctions C)))
  have hg0 : g0 = g := by
    dsimp [g0, g, chapter01GlobalFunctionsAlgebraMap]
    change Spec.map (CommRingCat.ofHom
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.structureMap.appTop).hom)) = _
    rw [CommRingCat.hom_comp, CommRingCat.ofHom_comp, Spec.map_comp]
    simp
  have hcomp : C.structureMap = C.carrier.toSpecΓ ≫ g := by
    dsimp [g]
    rw [← Scheme.toSpecΓ_naturality_assoc]
    simp
  have hcomp0 : C.structureMap = C.carrier.toSpecΓ ≫ g0 := by
    rw [hg0]
    exact hcomp
  let : _root_.IsReduced (chapter01GlobalFunctions C) := hred
  let : IsField (chapter01GlobalFunctions C) := hfield
  have hflatg0 : Flat g0 := by
    dsimp [g0]
    rw [Flat.SpecMap_iff]
    exact RingHom.Flat.of_isField (Field.toIsField k) _
  let : Flat g0 := hflatg0
  let : IsSchemeTheoreticallyDominant C.carrier.toSpecΓ :=
    IsSchemeTheoreticallyDominant.of_isDominant C.carrier.toSpecΓ
  let r : pullback g0 g0 ⟶ Spec (CommRingCat.of (chapter01GlobalFunctions C)) :=
    pullback.fst g0 g0
  let eP : pullback C.carrier.toSpecΓ r ≅ pullback C.structureMap g0 :=
    pullbackRightPullbackFstIso g0 g0 C.carrier.toSpecΓ ≪≫
      pullback.congrHom hcomp0.symm rfl
  let p : pullback C.carrier.toSpecΓ r ⟶ pullback g0 g0 :=
    pullback.snd C.carrier.toSpecΓ r
  let q : pullback C.structureMap g0 ⟶ pullback g0 g0 :=
    eP.inv ≫ p
  have hpstd : IsSchemeTheoreticallyDominant p := by infer_instance
  have hpuc : UniversallyClosed p := by infer_instance
  let : MorphismProperty.IsStableUnderComposition @IsSchemeTheoreticallyDominant :=
    ⟨fun _ _ _ _ => inferInstance⟩
  let : MorphismProperty.RespectsIso @IsSchemeTheoreticallyDominant :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f (_ : IsIso f) => inferInstance)
  have hqstd : IsSchemeTheoreticallyDominant q := by
    change IsSchemeTheoreticallyDominant (eP.inv ≫ p)
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsSchemeTheoreticallyDominant) eP.inv p).mpr hpstd
  have hquc : UniversallyClosed q := by
    change UniversallyClosed (eP.inv ≫ p)
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @UniversallyClosed) eP.inv p).mpr hpuc
  let : ConnectedSpace (pullback C.structureMap g0 : Scheme.{u}) :=
    by
      exact H.geometricallyConnected.geometrically_connectedSpace
        (K := chapter01GlobalFunctions C) g0
        (pullback.fst C.structureMap g0) (pullback.snd C.structureMap g0)
        (IsPullback.of_hasPullback C.structureMap g0)
  let : IsReduced (pullback C.structureMap g0 : Scheme.{u}) :=
    by
      exact H.geometricallyReduced.geometrically_isReduced
        (K := chapter01GlobalFunctions C) g0
        (pullback.fst C.structureMap g0) (pullback.snd C.structureMap g0)
        (IsPullback.of_hasPullback C.structureMap g0)
  let : IsSchemeTheoreticallyDominant q := hqstd
  let : UniversallyClosed q := hquc
  have hqsurj : Surjective q := by infer_instance
  have hQconn : ConnectedSpace (pullback g0 g0 : Scheme.{u}) :=
    hqsurj.surj.connectedSpace q.continuous
  have hQred : IsReduced (pullback g0 g0 : Scheme.{u}) :=
    IsSchemeTheoreticallyDominant.isReduced q
  let eQ : pullback g0 g0 ≅
      Spec (CommRingCat.of
        (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C)) :=
    pullbackSpecIso k (chapter01GlobalFunctions C) (chapter01GlobalFunctions C)
  let : ConnectedSpace
      (Spec (CommRingCat.of
        (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C))) := by
    exact eQ.hom.surjective.connectedSpace eQ.hom.continuous
  let : IsReduced
      (Spec (CommRingCat.of
        (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C))) := by
    let : IsReduced (pullback g0 g0 : Scheme.{u}) := hQred
    exact isReduced_of_isOpenImmersion eQ.inv
  have hTred : _root_.IsReduced
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) :=
    (affine_isReduced_iff
      (CommRingCat.of
        (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C))).mp inferInstance
  have hfiniteK : Module.Finite k (chapter01GlobalFunctions C) := by
    change Module.Finite k (chapter01GlobalFunctions C) at hfinite
    exact hfinite
  let : Module.Finite k (chapter01GlobalFunctions C) := hfiniteK
  let : Module.Finite k
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) :=
    Module.Finite.tensorProduct k (chapter01GlobalFunctions C)
      (chapter01GlobalFunctions C)
  let : IsArtinianRing
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) :=
    IsArtinianRing.of_finite k _
  have hdim0T : Ring.KrullDimLE 0
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) := by
    rw [Ring.krullDimLE_zero_iff]
    intro I hI
    let : I.IsPrime := hI
    infer_instance
  let : _root_.IsReduced
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) := hTred
  let : DiscreteTopology
      (PrimeSpectrum (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C)) :=
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr
      ⟨inferInstance, hdim0T⟩
  let : ConnectedSpace
      (PrimeSpectrum (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C)) := by
    change ConnectedSpace (Spec (CommRingCat.of
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C)))
    infer_instance
  have hsubT : Subsingleton
      (PrimeSpectrum (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C)) :=
    @PreconnectedSpace.trivial_of_discrete
      (PrimeSpectrum (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C)) _
      inferInstance inferInstance
  have hnonemptyT : Nonempty
      (PrimeSpectrum (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C)) :=
    inferInstance
  let : Nontrivial
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp hnonemptyT
  have hfieldT : IsField
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp hsubT
  let : Field
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) := hfieldT.toField
  let μ : (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) →ₐ[k]
      chapter01GlobalFunctions C := Algebra.TensorProduct.lmul' k
  have hμinj : Function.Injective μ :=
    RingHom.injective μ.toRingHom
  have hμsurj : Function.Surjective μ := by
    intro x
    exact ⟨1 ⊗ₜ[k] x, by simp [μ]⟩
  have hμbij : Function.Bijective μ := ⟨hμinj, hμsurj⟩
  let eμ : (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) ≃ₐ[k]
      chapter01GlobalFunctions C := AlgEquiv.ofBijective μ hμbij
  have hfinrank : Module.finrank k
      (chapter01GlobalFunctions C ⊗[k] chapter01GlobalFunctions C) =
      Module.finrank k (chapter01GlobalFunctions C) := eμ.toLinearEquiv.finrank_eq
  have hrank : Module.finrank k (chapter01GlobalFunctions C) *
      Module.finrank k (chapter01GlobalFunctions C) =
      Module.finrank k (chapter01GlobalFunctions C) := by
    simpa using hfinrank
  have hKrank : Module.finrank k (chapter01GlobalFunctions C) = 1 := by
    apply Nat.mul_left_cancel
      (show 0 < Module.finrank k (chapter01GlobalFunctions C) from Module.finrank_pos)
    simpa using hrank
  have hbij : Function.Bijective (algebraMap k (chapter01GlobalFunctions C)) :=
    Module.Free.bijective_algebraMap_of_finrank_eq_one hKrank
  let e : k ≃+* chapter01GlobalFunctions C :=
    RingEquiv.ofBijective (algebraMap k (chapter01GlobalFunctions C)) hbij
  refine ⟨e.symm, ?_⟩
  intro r
  change e.symm (algebraMap k (chapter01GlobalFunctions C) r) = r
  exact e.symm_apply_apply r

theorem chapter01_h0_structureSheaf_eq_one
    {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier)
    (hO : chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules))
    (H : Chapter01GeometricallyConnectedReducedCurve k C)
    (B : Chapter01DegreeZeroCohomologyGlobalSectionsBridge k C.structureMap D hO) :
    chapter01h0 D chapter01StructureSheaf hO = 1 := by
  classical
  rcases chapter01_globalFunctions_eq_baseField C H with ⟨e, he⟩
  let _ : AddCommGroup
      (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).V :=
    (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).addCommGroup
  let _ : Module k
      (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).V :=
    (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).module
  let _ : AddCommMonoid
      (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).V :=
    (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).addCommGroup.toAddCommMonoid
  let _ : Module k (chapter01GlobalFunctions C) :=
    Module.compHom _ (chapter01GlobalFunctionsAlgebraMap C)
  have halg : chapter01GlobalFunctionsAlgebraMap C = e.symm := by
    ext r
    apply e.injective
    simp [he]
  let E : k ≃ₗ[k] chapter01GlobalFunctions C :=
    { toFun := chapter01GlobalFunctionsAlgebraMap C
      invFun := e
      left_inv := by
        intro r
        exact he r
      right_inv := by
        intro w
        rw [halg]
        exact e.symm_apply_apply w
      map_add' := (chapter01GlobalFunctionsAlgebraMap C).map_add
      map_smul' := by
        intro a x
        change chapter01GlobalFunctionsAlgebraMap C (a * x) =
          chapter01GlobalFunctionsAlgebraMap C a *
            chapter01GlobalFunctionsAlgebraMap C x
        exact (chapter01GlobalFunctionsAlgebraMap C).map_mul a x }
  have hΓ : Module.finrank k (chapter01GlobalFunctions C) = 1 := by
    calc
      Module.finrank k (chapter01GlobalFunctions C) = Module.finrank k k :=
        E.finrank_eq.symm
      _ = 1 := by simp
  have hV : Module.finrank k
      (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).V =
      Module.finrank k (chapter01GlobalFunctions C) := by
    exact @LinearEquiv.finrank_eq k
      (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).V
      (chapter01GlobalFunctions C)
      (inferInstance : Semiring k)
      (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).addCommGroup.toAddCommMonoid
      (D.realization (chapter01StructureSheaf : C.carrier.Modules) hO 0).module
      (inferInstance : AddCommMonoid (chapter01GlobalFunctions C))
      (Module.compHom _ (chapter01GlobalFunctionsAlgebraMap C)) B.linearEquiv
  simpa [chapter01h0, chapter01Hi] using hV.trans hΓ

def chapter01ArithmeticGenus {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier)
    (hO : chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules)) : ℤ :=
  1 - chapter01Chi D chapter01StructureSheaf hO

def chapter01ArithmeticGenusAsH1 {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier)
    (hO : chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules)) : ℕ :=
  chapter01h1 D chapter01StructureSheaf hO

theorem chapter01_arithmeticGenus_eq_h1
    {k : Type u} [Field k] (C : Chapter01ProperCurveOverField k)
    (D : Chapter01CohomologyDimensions k C.carrier)
    (hO : chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules))
    (hH0 : chapter01h0 D chapter01StructureSheaf hO = 1) :
    chapter01ArithmeticGenus C D hO = chapter01ArithmeticGenusAsH1 C D hO := by
  simp [chapter01ArithmeticGenus, chapter01ArithmeticGenusAsH1, chapter01Chi,
    chapter01EulerCharacteristic, hH0]

/- No algebraic closure is built into the definition of a curve.  Residue-field
  degrees are part of the degree convention. -/
def chapter01ClosedPointDegree {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k) (x : C.carrier)
    (_hx : chapter01ClosedPoint C.carrier x) : ℕ := by
  letI : Algebra k (C.carrier.residueField x) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ C.structureMap.appTop ≫
      C.carrier.Γevaluation x).hom.toAlgebra
  exact Module.finrank k (C.carrier.residueField x)

def chapter01DegreeWithResidueFieldFactors {k : Type u} [Field k]
    (C : Chapter01ProperCurveOverField k) (E : Finset C.carrier)
    (hE : ∀ x, x ∈ E → chapter01ClosedPoint C.carrier x) : ℕ :=
  E.attach.sum (fun x => chapter01ClosedPointDegree C x.1 (hE x.1 x.2))

structure Chapter01NoetherianRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    : Prop extends Chapter01RelativeCurve f where
  baseLocallyNoetherian : IsLocallyNoetherian S

structure Chapter01ProjectiveRelativeCurve {X S : Scheme.{u}} (f : X ⟶ S)
    : Prop extends Chapter01NoetherianRelativeCurve f where
  projective : Chapter08IsProjective f

def chapter01RelativeFinitenessHypotheses {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter01RelativeCurve f ∧ IsLocallyNoetherian S

def chapter01ProjectiveRelativeHypothesis {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter08IsProjective f

/-! Book 8's numerical and Hilbert-polynomial APIs are the canonical inputs for the
  later relative statements.  The aliases below keep the dependency visible at the
  chapter boundary without re-defining those constructions. -/
abbrev Chapter01Book08NumericalPolynomial := Chapter08NumericalPolynomial
abbrev Chapter01Book08ProjectiveFamily := Chapter08ProjectiveFamily
abbrev Chapter01Book08RelativeScheme := RelativeScheme
abbrev Chapter01Book08RelativeEffectiveCartierDivisor
    {S : Scheme.{u}} (C T : RelativeScheme S) (d : ℕ) :=
  RelativeEffectiveCartierDivisor C T d

abbrev Chapter01Book08UniversalDivisorRepresentation
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :=
  Chapter11UniversalDivisorRepresentingData C d

structure Chapter01Book08ProjectiveInput {X S : Scheme.{u}} (f : X ⟶ S) where
  projective : Chapter08IsProjective f
  locallyNoetherian : IsLocallyNoetherian S

def chapter01Book08EulerConstancyInput {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter01Book08ProjectiveInput f

def chapter01Book08UniversalDivisorInput (S : Scheme.{u}) : Prop :=
  ∀ (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C],
    Chapter11FiniteLocallyFreeOfRank
      ((universalDivisor C d).inclusion ≫
        pullback.snd C.structuralMap (symmetricPower C d).structuralMap) d

noncomputable def chapter01Book08UniversalDivisor
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    EffectiveCartierDivisor (curveSymmetricAmbient C d) :=
  universalDivisor C d

noncomputable def chapter01Book08UniversalDivisorRepresentation
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter01Book08UniversalDivisorRepresentation C d :=
  universalDivisorRepresentingData C d

theorem chapter01_book08_universalDivisor_has_constant_length
    {S : Scheme.{u}} (C : RelativeScheme S) (d : ℕ)
    [Chapter11SmoothQuasiProjectiveCurve C] :
    Chapter11FiniteLocallyFreeOfRank
      ((universalDivisor C d).inclusion ≫
        pullback.snd C.structuralMap (symmetricPower C d).structuralMap) d := by
  exact universalDivisor_finiteLocallyFree C d

/-! The normalization and length conventions are named explicitly for use by the
  divisor and exact-sequence chapters. -/
structure Chapter01NormalizedValuation (R : Type u) [CommRing R] [IsLocalRing R]
    [IsDomain R] where
  valuation : FractionRing R → ℤ
  valuation_one : valuation 1 = 0
  valuation_mul : ∀ {a b}, a ≠ 0 → b ≠ 0 →
    valuation (a * b) = valuation a + valuation b
  valuation_nonnegative : ∀ {a : R}, a ≠ 0 →
    0 ≤ valuation (algebraMap R (FractionRing R) a)
  valuation_add : ∀ {a b : FractionRing R}, a ≠ 0 → b ≠ 0 → a + b ≠ 0 →
    min (valuation a) (valuation b) ≤ valuation (a + b)
  uniformizer_value : ∀ t, chapter01LocalParameter t →
    valuation (algebraMap R (FractionRing R) t) = 1

def chapter01ModuleLength {R M : Type u} [Ring R] [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R M

theorem chapter01_length_is_module_length {R M : Type u} [Ring R] [AddCommGroup M]
    [Module R M] : chapter01ModuleLength (R := R) (M := M) = Module.length R M := by
  rfl

theorem chapter01_normal_local_domain_isDVR
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain R] (hnormal : IsIntegrallyClosed R)
    (hdim : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  exact chapter01_normal_oneDimensional_local_isDVR hnormal hdim

theorem chapter01_regular_local_is_factorial
    {R : Type u} [CommRing R] [IsRegularLocalRing R] [IsDomain R] :
    UniqueFactorizationMonoid R := by
  exact chapter01_regular_local_ring_is_factorial

/-! A cohomology profile records exactly the finiteness and dimension-one vanishing
  used in the definition of ``h^i`` and ``χ``. -/
structure Chapter01ProperCurveFinitenessProfile
    (k : Type u) [Field k] (C : Chapter01ProperCurveOverField k) where
  dimensions : Chapter01CohomologyDimensions k C.carrier
  dimensions_structureMap : dimensions.structureMap = C.structureMap
  coherentStructureSheaf :
    chapter04FiniteTypeQuasiCoherent (chapter01StructureSheaf : C.carrier.Modules)
  vanishingAboveOne :
    ∀ (F : C.carrier.Modules), chapter04FiniteTypeQuasiCoherent F →
      chapter01CohomologyVanishesAboveOne F

theorem chapter01_proper_curve_coherent_cohomology_is_finite_dimensional
    {k : Type u} [Field k] {C : Chapter01ProperCurveOverField k}
    (H : Chapter01ProperCurveFinitenessProfile k C)
    (F : C.carrier.Modules) (hF : chapter04FiniteTypeQuasiCoherent F) (i : ℕ) :
    ∃ V : Type u, ∃ (_ : AddCommGroup V) (_ : Module k V),
      FiniteDimensional k V ∧
        Nonempty (V ≃+ chapter01CohomologyGroup F i) := by
  let R := H.dimensions.realization F hF i
  refine ⟨R.V, R.addCommGroup, R.module, ?_⟩
  constructor
  · exact R.finite
  · exact ⟨@LinearEquiv.toAddEquiv k k _ _ _ _ _ _ R.V
      (chapter01CohomologyGroup F i) R.addCommGroup.toAddCommMonoid
      (inferInstance : AddCommMonoid (chapter01CohomologyGroup F i)) R.module R.moduleG
      R.linearEquiv⟩

theorem chapter01_proper_curve_coherent_cohomology_vanishes_above_one
    {k : Type u} [Field k] {C : Chapter01ProperCurveOverField k}
    (H : Chapter01ProperCurveFinitenessProfile k C)
    (F : C.carrier.Modules) (hF : chapter04FiniteTypeQuasiCoherent F) :
    chapter01CohomologyVanishesAboveOne F := by
  exact H.vanishingAboveOne F hF

/-! The relative two-term presentation has two independent numerical behaviours:
  kernel and cokernel ranks may vary, while the index is locally constant under the
  projective/flat hypotheses supplied by the preceding book. -/
structure Chapter01RelativeCohomologyIndexProfile (S : Type u) [TopologicalSpace S] where
  h₀ : S → ℕ
  h₁ : S → ℕ
  χ : S → ℤ
  h₀_upperSemicontinuous : chapter01UpperSemicontinuous h₀
  h₁_upperSemicontinuous : chapter01UpperSemicontinuous h₁
  chi_formula : ∀ s, χ s = (h₀ s : ℤ) - h₁ s
  chiLocallyConstant : IsLocallyConstant χ

theorem chapter01_relative_euler_characteristic_is_locally_constant
    {S : Type u} [TopologicalSpace S] (P : Chapter01RelativeCohomologyIndexProfile S) :
    IsLocallyConstant P.χ := by
  exact P.chiLocallyConstant

/-! These are the exact theorem-level hypotheses used whenever properness is upgraded
  to projectivity in the relative arguments. -/
structure Chapter01RelativeRiemannRochHypotheses {X S : Scheme.{u}} (f : X ⟶ S) where
  relativeCurve : Chapter01RelativeCurve f
  baseLocallyNoetherian : IsLocallyNoetherian S
  projectiveWhenRequired : Chapter08IsProjective f

def chapter01RelativeStatementNeedsProjectivity {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Chapter08IsProjective f

end
end LastLib.Book09DivisorsRiemannRochAndDualityOnRelativeCurves.Chapter01
