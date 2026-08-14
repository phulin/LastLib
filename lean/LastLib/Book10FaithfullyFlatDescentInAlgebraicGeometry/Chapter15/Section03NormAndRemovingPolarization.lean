import LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15.Section02VeryAmplenessAndClosedImmersions

/-!
# 15.3 Removing a chosen polarization

The norm construction is used only after a finite locally free cover has been
specified.  The second half records the two compatible positive-data patterns
used later: an effective Cartier divisor and a rigidified polarized abelian
scheme.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09
open LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter10

universe u v

namespace LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15

noncomputable section

structure FiniteLocallyFreeNormSetup {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    where
  cover : FiniteLocallyFreeConstantRank g
  sourceProjection : FiniteLocallyFreeMorphism (baseChangeToSource f g)
  sourceProjection_surjective : Surjective (baseChangeToSource f g)
  finitePresentation : IsFinitePresentation f

noncomputable def finiteLocallyFreeNormSetupOf
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) (hf : IsFinitePresentation f) :
    FiniteLocallyFreeNormSetup f g :=
  { cover := G
    sourceProjection := baseChangeToSource_finiteLocallyFree f g G
    sourceProjection_surjective := baseChangeToSource_surjective f g G
    finitePresentation := hf }

theorem baseChange_projection_is_finite_locally_free
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) :
    FiniteLocallyFreeMorphism (baseChangeToSource f g) := by
  exact baseChangeToSource_finiteLocallyFree f g G

theorem baseChange_projection_is_surjective
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) :
    Surjective (baseChangeToSource f g) := by
  exact baseChangeToSource_surjective f g G

theorem norm_formula
    {Y X : Scheme.{u}} (q : Y ⟶ X) (hq : FiniteLocallyFreeMorphism q)
    (M : LineBundle Y) :
    normLineBundle q hq M =
      let C := normConstruction q hq
      letI : Chapter10PicardOperations X := C.picard
      letI : Chapter10DeterminantLineAPI q := C.determinant
      fromNormLineBundle
        (chapter10PicardTensor
          (chapter10DeterminantLine q (toNormLineBundle M))
          (Chapter10PicardOperations.dual
            (chapter10DeterminantLine q (toNormLineBundle
              (chapter15StructureLineBundle Y))))) := by
  exact normLineBundle_determinant_formula q hq M

theorem norm_is_multiplicative
    {Y X : Scheme.{u}} (q : Y ⟶ X) (hq : FiniteLocallyFreeMorphism q)
    (M N : LineBundle Y) :
    lineBundleIsomorphic
      (normLineBundle q hq (sourceTensorLineBundle (normConstruction q hq) M N))
      (targetTensorLineBundle (normConstruction q hq)
        (normLineBundle q hq M) (normLineBundle q hq N)) := by
  exact normLineBundle_tensor q hq M N

/- A finite morphism of the base is affine over affine opens, so the same
  affine nonvanishing criterion tests ampleness for the composite. -/
theorem ample_relative_to_finite_base
    {Y T S : Scheme.{u}} (h : Y ⟶ T) (g : T ⟶ S) (M : LineBundle Y)
    (hg : IsFinite g) (hM : IsAmple h M) : IsAmple (h ≫ g) M := by
  sorry

theorem baseChange_ample_over_finite_base
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hg : IsFinite g) (M : LineBundle (baseChange f g))
    (hM : IsAmple (baseChangeToBase f g) M) :
    IsAmple (baseChangeStructureMap f g) M := by
  exact ample_relative_to_finite_base (baseChangeToBase f g) g M hg hM

/-! The norm-ampleness lemma -/

theorem norm_ampleness
    {Y X S : Scheme.{u}} (q : Y ⟶ X) (f : X ⟶ S)
    (hq : FiniteLocallyFreeMorphism q) (hqsurj : Surjective q)
    (hY : IsFinitePresentation (q ≫ f)) (M : LineBundle Y)
    (hM : IsAmple (q ≫ f) M) :
    IsAmple f (normLineBundle q hq M) := by
  sorry

theorem norm_ampleness_of_ampleness_over_finite_cover
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) (hf : IsFinitePresentation f)
    (M : LineBundle (baseChange f g))
    (hM : IsAmple (baseChangeToBase f g) M) :
    IsAmple f (normLineBundle (baseChangeToSource f g)
      (baseChangeToSource_finiteLocallyFree f g G) M) := by
  apply norm_ampleness (baseChangeToSource f g) f
    (baseChangeToSource_finiteLocallyFree f g G)
    (baseChangeToSource_surjective f g G)
  · let : IsFinite (baseChangeToSource f g) :=
      (baseChangeToSource_finiteLocallyFree f g G).1
    let : Flat (baseChangeToSource f g) :=
      (baseChangeToSource_finiteLocallyFree f g G).2.1
    let : LocallyOfFinitePresentation (baseChangeToSource f g) :=
      (baseChangeToSource_finiteLocallyFree f g G).2.2
    let : QuasiCompact f := hf.1
    let : QuasiSeparated f := hf.2.1
    let : LocallyOfFinitePresentation f := hf.2.2
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · have hcomp : IsAmple (baseChangeToBase f g ≫ g) M :=
      baseChange_ample_over_finite_base f g G.profile.finite M hM
    have heq : baseChangeToSource f g ≫ f = baseChangeToBase f g ≫ g :=
      pullback.condition
    rw [← heq] at hcomp
    exact hcomp

theorem quasiProjectivity_finiteLocallyFree_descent_local
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) (hf : IsFinitePresentation f)
    (M : LineBundle (baseChange f g))
    (hM : IsAmple (baseChangeToBase f g) M) :
    HasLocalFiniteRankEmbedding f := by
  sorry

theorem quasiProjectivity_finiteLocallyFree_descent_global
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) (hf : IsFinitePresentation f)
    (hS : QuasiCompact (𝟙 S)) (M : LineBundle (baseChange f g))
    (hM : IsAmple (baseChangeToBase f g) M) :
    HasGlobalFiniteRankEmbedding f := by
  sorry

theorem projectivity_finiteLocallyFree_descent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) (hf : IsFinitePresentation f)
    (hproper : IsProper f) (hS : QuasiCompact (𝟙 S))
    (M : LineBundle (baseChange f g))
    (hM : IsAmple (baseChangeToBase f g) M) :
    IsProjectiveMorphism f := by
  sorry

theorem properness_finiteLocallyFree_descent
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g)
    (hproper : IsProper (baseChangeToBase f g)) : IsProper f := by
  let : IsFinite g := G.profile.finite
  exact proper_faithfullyFlat_descent f g
    ⟨G.profile.flat, G.surjective, inferInstance⟩ hproper

theorem projectivity_finiteLocallyFree_descent_of_upstairs_proper
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (G : FiniteLocallyFreeConstantRank g) (hf : IsFinitePresentation f)
    (hproper : IsProper (baseChangeToBase f g)) (hS : QuasiCompact (𝟙 S))
    (M : LineBundle (baseChange f g))
    (hM : IsAmple (baseChangeToBase f g) M) :
    IsProjectiveMorphism f := by
  sorry

/-! ### Marked effective Cartier divisors -/

structure MarkedDivisorDescentData
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [Chapter10IdealDualAPI (baseChange f g)] where
  divisor : Chapter10EffectiveCartierDivisor (baseChange f g)
  lineBundle : LineBundle (baseChange f g)
  lineBundle_is_OofD :
    lineBundle = fromNormLineBundle (chapter10OofD divisor)
  descent : FpqcLineBundleDescentDatum f g
  descent_carrier : descent.lineBundle = lineBundle
  positivePower : ∃ n : ℕ, 0 < n ∧
    IsAmple (baseChangeToBase f g) (lineBundle.tensorPower n)

theorem marked_divisor_OofD_has_descent_datum
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [Chapter10IdealDualAPI (baseChange f g)]
    (D : MarkedDivisorDescentData f g) :
    ∃ E : LineBundleDescentDatum (baseChangeToSource f g),
      E.carrier = fromNormLineBundle (chapter10OofD D.divisor) := by
  refine ⟨D.descent.descent, ?_⟩
  exact D.descent.carrier_eq.trans (D.descent_carrier.trans D.lineBundle_is_OofD)

theorem marked_divisor_fixed_power_descends
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (hf : IsFinitePresentation f) (hg : FpqcCoverData g)
    [Chapter10IdealDualAPI (baseChange f g)]
    (D : MarkedDivisorDescentData f g) :
    ∃ L : LineBundle X,
      Nonempty (LineBundleDescentRealization D.descent.descent L) ∧
        IsAmple f L := by
  obtain ⟨n, hn, hpower⟩ := D.positivePower
  have hline : IsAmple (baseChangeToBase f g) D.lineBundle := by
    change
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04Ample
        (baseChangeToBase f g) D.lineBundle
    exact
      LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter04.chapter04_ample_of_ample_tensorPower
        (baseChangeToBase f g) D.lineBundle n hn hpower
  obtain ⟨L, hreal⟩ := lineBundle_fpqc_effective_descent f g hg D.descent
  refine ⟨L, hreal, ?_⟩
  exact
    relative_ampleness_of_descended_lineBundle f g L D.lineBundle D.descent hreal
      (by
        rw [← D.descent_carrier, ← D.descent.carrier_eq]
        exact lineBundleIsomorphic_refl _) hf hg hline

def CartierDivisorMeetsComponent {X : Scheme.{u}}
    (D : Chapter10EffectiveCartierDivisor X) (C : Set X) : Prop :=
  ∃ x : X, x ∈ C ∧ x ∈ D.ideal.support

def CartierDivisorMeetsEveryGeometricComponent {X : Scheme.{u}}
    (D : Chapter10EffectiveCartierDivisor X) {ι : Type v}
    (component : ι → Set X) : Prop :=
  ∀ i, CartierDivisorMeetsComponent D (component i)

structure PolygonCurveComponentData {X : Scheme.{u}} (n : ℕ) where
  moreThanOne : 1 < n
  component : Fin n → Set X
  component_nonempty : ∀ i, (component i).Nonempty
  identityDivisor : Chapter10EffectiveCartierDivisor X
  identityComponent : Fin n
  identity_support_nonempty :
    (identityDivisor.ideal.support : Set X).Nonempty
  identity_support_in_identity_component :
    (identityDivisor.ideal.support : Set X) ⊆ component identityComponent
  identity_support_avoids_other_components :
    ∀ j, j ≠ identityComponent →
      Disjoint (identityDivisor.ideal.support : Set X) (component j)

theorem identity_divisor_does_not_meet_all_components_on_polygon
    {X : Scheme.{u}} {n : ℕ} (P : PolygonCurveComponentData (X := X) n) :
    ¬ CartierDivisorMeetsEveryGeometricComponent (ι := Fin n) P.identityDivisor P.component := by
  intro h
  let j : Fin n :=
    if hzero : P.identityComponent.val = 0 then
      ⟨1, P.moreThanOne⟩
    else
      ⟨0, lt_trans Nat.zero_lt_one P.moreThanOne⟩
  have hj : j ≠ P.identityComponent := by
    dsimp [j]
    split_ifs with hzero
    · intro hEq
      have hval : (1 : ℕ) = P.identityComponent.val := congrArg Fin.val hEq
      have : (1 : ℕ) = 0 := hval.trans hzero
      exact Nat.one_ne_zero this
    · intro hEq
      apply hzero
      exact (congrArg Fin.val hEq).symm
  obtain ⟨x, hxComponent, hxSupport⟩ := h j
  exact (Set.disjoint_left.1 (P.identity_support_avoids_other_components j hj))
    hxSupport hxComponent

/-! ### Rigidified polarized abelian schemes -/

def chapter15AsChapter09LineBundle {X : Scheme.{u}} (L : LineBundle X) :
    LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09LineBundle X :=
  { module := L.sheaf
    isInvertible := L.isInvertible }

def RigidifiedAbelianLineBundle {S : Scheme.{u}}
    (A : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09AbelianScheme S)
    (L : LineBundle A.carrier)
    [Chapter10PicardOperations A.carrier] : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09Rigidified A
    (chapter15AsChapter09LineBundle L)

def AbelianRelativePolarization {S : Scheme.{u}}
    (A : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09AbelianScheme S)
    (L : LineBundle A.carrier)
    [Chapter10PicardOperations A.carrier] : Prop :=
  LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.chapter09Polarization A
    (chapter15AsChapter09LineBundle L)

structure RigidifiedPolarizationDescentData
    {S T : Scheme.{u}}
    (A : LastLib.Book08AmpleLineBundlesHilbertPolynomialsAndSymmetricPowers.Chapter09.Chapter09AbelianScheme S)
    (g : T ⟶ S) [Chapter10PicardOperations A.carrier] where
  lineBundle : LineBundle A.carrier
  rigidified : RigidifiedAbelianLineBundle A lineBundle
  polarization : AbelianRelativePolarization A lineBundle
  descent : FpqcLineBundleDescentDatum A.structureMap g
  descent_carrier :
    descent.lineBundle =
      pullbackLineBundle (baseChangeToSource A.structureMap g) lineBundle

/- A rigidification controls the scalar ambiguity only after an overlap
  isomorphism has been chosen.  The uniqueness field is the reusable form of
  that normalization statement; it does not manufacture the overlap map. -/
structure RigidifiedOverlapNormalization {X : Scheme.{u}}
    (L M : LineBundle X) where
  overlap : LineBundleIso L M
  compatible : LineBundleIso L M → Prop
  scalar_uniqueness : ∀ e₁ e₂ : LineBundleIso L M,
    compatible e₁ → compatible e₂ → e₁.hom = e₂.hom

theorem rigidification_removes_scalar_ambiguity
    {X : Scheme.{u}} {L M : LineBundle X}
    (R : RigidifiedOverlapNormalization L M)
    {e₁ e₂ : LineBundleIso L M}
    (h₁ : R.compatible e₁) (h₂ : R.compatible e₂) :
    e₁.hom = e₂.hom := by
  exact R.scalar_uniqueness e₁ e₂ h₁ h₂

def RigidificationInsufficientForDescent {S : Scheme.{u}}
    (A : Chapter09AbelianScheme S) (L M : LineBundle A.carrier)
    [Chapter10PicardOperations A.carrier] : Prop :=
  RigidifiedAbelianLineBundle A L ∧ ¬ lineBundleIsomorphic L M

end

end LastLib.Book10FaithfullyFlatDescentInAlgebraicGeometry.Chapter15
